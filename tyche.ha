// Type Checker in Hare
// Very simple type checker
// 
// features [state]
// 	inference [in progress]
// 	validation [in progress]
//	generics [planned]
//
// phases
// 	AST tagging
// 		All AST nodes aer assigned a type.
// 		Type inference is performed here
// 		Failure to tag a node is an error.
// 	validation
// 		Checks if all the types hold to their promises.
// 
// details
// 	notation stuffs
// 		`=>` infer type (conlude: Assign)
// 		`<=` check type 
// 		`:` has type by definition
// 	current type rules
//		(I've not implemented any)
//	planned rules
//		- If we've already typed an identifier, we can infer that it
//		- hasn't changed
//		if  | Γ# x : A
//		then| Γ# x => A
//		
//		if  | Γ#

use fmt;

type ShouldDefer = !void;
type DoesNotApply = void;

fn check_typ(context: *TypContext, node: *Ast, typ: *Typ) (bool | ShouldDefer) = {
	match (node.typ) {
		case null =>
			return ShouldDefer;
		case let x : *Typ =>
			return x == typ;
	};
};

fn infer_typ(context: *TypContext, node: *Ast, typ: *Typ) bool = {
	match (node.typ) {	
		case null => {
			node.typ = typ;
			return true;
		};
		case let x : *Typ =>
			return x == typ;
	};
};

fn apply_rule_var(context: *TypContext, goal: *Ast)
(bool | ShouldDefer | DoesNotApply) = {
	fmt::println("executing rule: var")!;
	defer fmt::println("finishing rule: var")!;
	let inner : IdentId = if (goal.val is IdentN) {
		yield (goal.val as IdentN).id ;
	} else {
		return DoesNotApply;
	};
	fmt::println("\tgot var, looking up in context")!;
	let luv = lookup(context, inner);
	if (luv is null) {
		fmt::println("\tlookup failed")!;
		return ShouldDefer;
	} else {
		fmt::println("\tlookup succeeded, forcing infer")!;
		return infer_typ(context, goal, luv as *Typ);
	};
};

fn apply_rule_int(context: *TypContext, goal: *Ast)
(bool | ShouldDefer | DoesNotApply) = {
	fmt::println("executing rule: int")!;
	defer fmt::println("finishing rule: var")!;
	if (!(goal.val is IntLitN)) {
		return DoesNotApply;
	};
	fmt::println("\tgot int, forcing infer")!;
	fmt::println("\tlookup succeeded, forcing infer")!;
	return infer_typ(context, goal, &context.pool.buckets[0].1[0]);
};

fn apply_rule_app(context: *TypContext, goal: *Ast)
(bool | ShouldDefer | DoesNotApply) = {
	fmt::println("executing rule: app")!;
	defer fmt::println("finishing rule: app")!;
	if (!(goal.val is FuncCallN)) {
		return DoesNotApply;
	};
	fmt::println("\tgot func, checking deferral")!;
	let inner : FuncCallN = goal.val as FuncCallN;
	if (inner.targe.typ is null) {
		return ShouldDefer;
	};
	for (let i : size = 0; i < len(inner.args); i += 1) {	
		if (inner.args[i].typ is null) {
			return ShouldDefer;
		};
	};
	fmt::println("\tDeferrals checked, checking reciever and prototype")!;
	let proto = if (inner.targe.typ is *Typ) {
		let inner = inner.targe.typ as *Typ;
		// Can Only call functions
		if (!(inner.repr is FuncT)) {
			return false;
		};
		yield &(inner.repr as FuncT);
	} else {
		abort("Type unset during deferral check");
	};
	fmt::println("\tchecking function args")!;
	// wrong number of args
	if (len(proto.args) != len(inner.args)) {
		return false;
	};
	for (let i : size = 0; i < len(proto.args); i += 1) {
		// mismatch param args
		match (check_typ(context, inner.args[i], proto.args[i])) {
			case ShouldDefer => return ShouldDefer;
			case let ma : bool => if (!ma) {return false;};
		};
	};
	fmt::println("\tchecks passed, forcing inference")!;
	return infer_typ(context, goal, proto.rets);
	//return false;
};

export fn main() void = {
	fmt::println("typing shit boio")!;

	let pool = TypPool { buckets = [] };
	let context = TypContext { ident_map = [], pool = &pool, outer = null };
	defer drop_context(&context);
	defer drop_pool(&pool);

	// defining a type and defining an ident with that type
	fmt::println("Creating int type")!;
	let intT = Typ{name = "int", repr = PrimitiveT};
	let intT = register_typ(&pool, intT);
	fmt::print("created: ")!; print_typ(intT)!; fmt::print("\n")!;

	fmt::println("Creating float type")!;
	let floatT = Typ{name = "float", repr = PrimitiveT};
	let floatT = register_typ(&pool, floatT);
	fmt::print("created: ")!; print_typ(floatT)!; fmt::print("\n")!;

	fmt::println("Creating func type `fn (int) float` ")!;
	let funcT = Typ{name = void, repr = FuncT {
		rets = floatT,
		args = [intT, intT],
	}};
	let funcT = register_typ(&pool, funcT);
	fmt::print("created: ")!; print_typ(funcT)!; fmt::print("\n")!;

	// Binding to idents
	insert_context(&context, 0, intT)!;
	insert_context(&context, 1, funcT)!;
	
	let source_base = "@1(@0, 5)";

	let x : *Ast = {
		let arg1 = alloc(Ast{
			val = IdentN { id = 0 },
			typ = null,
			loc = SourceLoc {
				blob  = &source_base,
				start = 4,
				end   = 6,
			}
		});
		let arg2 = alloc(Ast{
			val = 5: IntLitN,
			typ = null,
			loc = SourceLoc {
				blob  = &source_base,
				start = 7,
				end   = 8,
			}
		});
		let func = alloc(Ast{
			val = IdentN { id = 1},
			typ = null,
			loc = SourceLoc {
				blob  = &source_base,
				start = 0,
				end   = 3,
			}
		});

		yield alloc(Ast{
			val = FuncCallN { targe = func, args = [arg1, arg2] },
			typ = null,
			loc = SourceLoc {
				blob  = &source_base,
				start = 0,
				end   = 9,
			}
		});
	};

	defer drop_ast(x);

	// converting the ast into some type checking goals
	let goals = goals_from_ast(x);

	// going through them and just kinda applying rules :)
	
	// imagine we've deferred type checking while initialising the
	// typechecker
	let deferred : bool = true;
	fmt::println("==================== TYPECHECKING")!;
	const rules : [_]*fn(*TypContext, *Ast) (bool|ShouldDefer|DoesNotApply)
		= [&apply_rule_var, &apply_rule_int, &apply_rule_app];
	for (deferred) {
		fmt::println("\t\t ==== scanning vars ====")!;
		deferred = false;
		for (let i : size = 0; i < len(goals); i += 1) {
			if (!(goals[i].typ is null)) continue;
			fmt::println("testing rule: var")!;
			let attempt = apply_rule_var(&context, goals[i]);
			match (attempt) {
				case let i : ShouldDefer => {
					fmt::println("\tdeferred")!;	
					deferred = true;
					continue;
				};
				case let i : DoesNotApply => {
					yield;
				};
				case let success : bool => if (!success) {
					fmt::println("TypeCheckFailed")!;
					return;
				};
			};
			fmt::println("testing rule: int")!;
			let attempt = apply_rule_int(&context, goals[i]);
			match (attempt) {
				case let i : ShouldDefer => {
					fmt::println("\tdeferred")!;	
					deferred = true;
					continue;
				};
				case let i : DoesNotApply => {
					yield;
				};
				case let success : bool => if (!success) {
					fmt::println("TypeCheckFailed")!;
					return;
				};
			};
			fmt::println("testing rule: app")!;
			let attempt = apply_rule_app(&context, goals[i]);
			match (attempt) {
				case let i : ShouldDefer => {
					fmt::println("\tdeferred")!;	
					deferred = true;
					continue;
				};
				case let i : DoesNotApply => {
					yield;
				};
				case let success : bool => if (!success) {
					fmt::println("TypeCheckFailed")!;
					return;
				};
			};
		};
	};
	fmt::println("==================== TYPECHECKING")!;
	fmt::println("Type Checked Successfully")!;
	fmt::println("Printing inferred types")!;
	for (let i : size = 0; i < len(goals); i += 1) {
		debug_ast(goals[i])!;
		fmt::print(": ")!;
		match (goals[i].typ) {
		case let typ : *Typ =>
			print_typ(typ)!;
		case null =>
			fmt::print("!!UNTYPED!!")!;
		};
		fmt::print("\n")!;
	};


};
