// Implementing a constraint solver based system
//  as shown in https://www.youtube.com/watch?v=-TJGhGa04F8&t=3215s

// Simpler than before, since we don't have TypeClasses (or traits)

use fmt;
use io;

type Scheme = (Type|TypeVar|TypeCons);
type Type = size;
type TypeVar = (size|void);
type TypeCons = struct {
	cons : ConsId,
	args: []size,
};
type ConsId = size;
type SchemeTable = []Scheme;

type Names = struct {
	types: []str,
	cons: []str,
};

fn show_scheme
(table: *SchemeTable, names: *Names, scheme: size)
(void|io::error) = {
	let schemei = deref(table, scheme);
	let scheme = table[schemei];
	return show_scheme_i(table, names, scheme);
};
fn show_scheme_i
(table: *SchemeTable, names: *Names, scheme: Scheme)
(void|io::error) = {
	match (scheme) {
		case let typ : Type =>
//			fmt::printf("T{}", typ : size)?;
			fmt::print(names.types[typ])?;
		case let var : TypeVar => show_var_i(table, var)?;
		case let con : TypeCons => {
//			fmt::printf("${}<", con.cons : size)?;
			fmt::printf("{}<", names.cons[con.cons])?;
			for (let i : size = 0; i < len(con.args); i += 1) {
				show_scheme(table, names, con.args[i])?;
				if (i + 1 < len(con.args)) {
					fmt::print(", ")?;
				};
			};
			fmt::print(">")?;
		};
	};
};

fn show_var_i(table: *SchemeTable, var: TypeVar) (void|io::error) = {
	match (var) {
		case void => fmt::print("<Unbound>")?;
		case let ind : size =>
			fmt::printf("<Bound:{}>", ind)?;
	};
	return;
};

type Goal = struct {
	source: (GoalEq|void),
	cons: (GoalEq|void),
};
type GoalEq = (size, size);

fn into_goal(goal: GoalEq) Goal = Goal { source = goal, cons = goal };

fn deref(table: *SchemeTable, ind: size) size = {
	let ind = ind;
	let got = table[ind];
	for (got is TypeVar; got = table[ind]) {
		let ref = got as TypeVar;
		if (ref is void) {return ind;};
		ind = ref as size;
	};
	return ind;
};

type Solver = struct {
	table: SchemeTable,
	remap_bag: []size,
	goals: []Goal,
	error_bag: []Goal,
};

fn bind(this: *Solver, a: size, b: size) void = {
	this.table[a] = b : TypeVar;
	append(this.remap_bag, a);
};

fn commit_binds(this: *Solver) void = {
	if (len(this.remap_bag) == 0) return;
	for (let i = len(this.remap_bag) - 1; i >= 0; i -= 1) {
		delete(this.remap_bag[i]);
	};
};

fn clear_binds(this: *Solver) void = {
	if (len(this.remap_bag) == 0) return;
	for (let i = len(this.remap_bag) - 1; i >= 0; i -= 1) {
		this.table[this.remap_bag[i]] = void : TypeVar;
		delete(this.remap_bag[i]);
	};
};

// This function makes a lot of assumptions:
// 	1) `dump` is a temporary goal pool
// 	2) the solver does the substitutions
// (using jotter-tables makes memory management assumptions true)
// (the ownership one is wrong, as we own our indexes)
fn unify
(this: *Solver, dump: *[]Goal, source: Goal, a: size, b: size )
bool = {
	let ai = deref(&this.table, a);
	let a = this.table[ai];
	let bi = deref(&this.table, b);
	let b = this.table[bi];
	if (a is TypeVar) {
		this.table[ai] = bi : TypeVar;
		return true;
	};
	if (b is TypeVar) {
		this.table[bi] = ai : TypeVar;
		return true;
	};
	if (a is Type && b is Type) {
		return a as Type == b as Type;
	};
	if (a is TypeCons && b is TypeCons) {
		return unify_typecons(this, dump, source, ai, bi);
	};
	return false;
};

fn unify_typecons
(this: *Solver, dump: *[]Goal, source: Goal, ai: size, bi: size)
bool = {
	let a = this.table[ai] as TypeCons; 
	let b = this.table[bi] as TypeCons;
	if (a.cons != b.cons) {
		return false;
	};
	if (len(a.args) != len(b.args)) {
		return false;
	};
	for (let i : size = 0; i < len(a.args); i += 1) {
		fmt::printfln("pushing goal to unify {} and {}",
			a.args[i], b.args[i])!;
		append(dump, Goal {
			source = source.source,
			cons = (a.args[i], b.args[i]) : GoalEq,
		});
	};
	return true;
};

export fn main() void = {
	fmt::println("Initialising shit first :)")!;

	const typ_int   : Type    = 0x00;
	const typ_float : Type    = 0x01;
	const con_vec   : ConsId  = 0x00;
	
	const names = Names {
		types = ["int", "float"],
		cons = ["vec"],
	};

	let solver = Solver { 
		table = [
			(void : TypeVar),			 // 0:T
			TypeCons { cons = con_vec, args = [0] }, // 1:$vec<T>
			(void : TypeVar),			 // 2:A
			TypeCons { cons = con_vec, args = [2] }, // 3:$vec<A>
			(void: TypeVar),			 // 4:C
			TypeCons { cons = con_vec, args = [4]},	 // 5:$vec<C>
			typ_int,				 // 6:Tint
			typ_float,				 // 7:Tfloat
		],
		remap_bag = [],
		goals = [],
		error_bag = [],
	};

	fmt::println("initialising solver")!;
	let goal = into_goal( ( 
		1, // TypeCons{ cons = con_vec, args = [typvar_T] },
		3, // TypeCons{ cons = con_vec, args = [typvar_A] }
	) : GoalEq);
	append(solver.goals, goal);

	let goal = into_goal( (
		2, // typvar_A,
		6, // typ_int,
	) : GoalEq);
	append(solver.goals, goal);
	let goal = into_goal( (
		1, // TypeCons{ cons = con_vec, args = [typvar_T] },
		5, // TypeCons{ cons = con_vec, args = [typvar_C] }
	) : GoalEq);
	append(solver.goals, goal);
	let goal = into_goal( (
		4, //typvar_C,
		7, //typ_float,
	) : GoalEq);
	append(solver.goals, goal);
	for (demo_step(&solver)) {yield;};

	if (len(solver.error_bag) > 0) {
		fmt::println("There are some errors")!;
		for (let i: size = 0; i < len(solver.error_bag); i += 1) {
			let goal = solver.error_bag[i].source as GoalEq;
			fmt::print("tried to assign value of type ")!;
			show_scheme(&solver.table, &names, goal.0)!;
			fmt::print(" to reciever of type ")!;
			show_scheme(&solver.table, &names, goal.1)!;
			fmt::println("")!;
		};
	} else {
		fmt::println("No errors accrued")!;
	};
};

fn demo_step(solver: *Solver) bool = {
	fmt::println("Running solve")!;
	show_goals(&solver.goals);
	fmt::println("")!;
	return !random_shit(solver);
};

// returns true if finished
fn random_shit(this: *Solver) bool = {
	if (len(this.goals) == 0) return true;

	let temp = alloc([] : []Goal, 8);
	defer free(temp);

	const suc = solve_goal(this, &temp, this.goals[0]);
	if (suc) {
		commit_binds(this);
		for (let i: size = 0; i < len(temp); i += 1) {
			append(this.goals, temp[i]);
		};
	} else {
		clear_binds(this);
		append(this.error_bag, this.goals[0]);
	};
	delete(this.goals[0]);
	return false;
};

fn solve_goal(this: *Solver, dump: *[]Goal, goal: Goal) bool = {
	fmt::println("selecting strategy")!;
	return match (goal.cons) {
		case GoalEq =>
			yield solve_eq(this, dump, goal, goal.cons as GoalEq);
		case void => yield true;
	};
};

fn solve_eq(this: *Solver, dump: *[]Goal, source: Goal, eq: GoalEq) bool = {
	fmt::printfln("unifying : {} & {}", eq.0, eq.1)!;
	return unify(this, dump, source, eq.0, eq.1);
};

fn show_goals(goals: *[]Goal) void = {
	for (let i: size = 0; i < len(goals); i += 1) {
		let goal = goals[i];
		match (goal.cons) {
			case void => fmt::print("<DEBUG>")!;
			case let eq : GoalEq =>
				fmt::printf("{} ~ {}", eq.0, eq.1)!;
		};
		if (i + 1 < len(goals)) {
			fmt::print(" + ")!;
		};
	};
};
