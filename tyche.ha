// Implementing a constraint solver based system
//  as shown in https://www.youtube.com/watch?v=-TJGhGa04F8&t=3215s

// Simpler than before, since we don't have TypeClasses (or traits)

use fmt;
use io;

type Scheme = (Type|TypeVar|TypeCons);
type Type = size;
type TypeVar = size;
type TypeCons = struct {
	cons : ConsId,
	args: []Scheme,
};
type ConsId = size;

fn show_scheme(scheme: Scheme) (void|io::error) = {
	match (scheme) {
		case let typ : Type =>
			fmt::printf("T{}", typ : size)?;
		case let var : TypeVar => 
			fmt::printf("@{}", var : size)?;
		case let con : TypeCons => {
			fmt::printf("${}<", con.cons : size)?;
			for (let i : size = 0; i < len(con.args); i += 1) {
				show_scheme(con.args[i])?;
				if (i + 1 < len(con.args)) {
					fmt::print(", ")?;
				};
			};
			fmt::print(">")?;
		};
	};
};

type Goal = GoalEq;

type GoalEq = (Scheme, Scheme);


type SubMap = [](TypeVar, Scheme);

fn deref_sub(map: *SubMap, var: TypeVar) Scheme = {
	let ret = var : Scheme;
	for (ret is TypeVar) {
		let got = deref_sub_single(map, ret as TypeVar);
		if (got is void) {
			break;
		};
		ret = got as Scheme;
	};
	return ret;
};

fn deref_sub_single(map: *SubMap, var: TypeVar) (Scheme|void) = {
	for (let i : size = 0; i < len(map); i += 1) {
		if (map[i].0 == var) {
			return map[i].1;
		};
	};
	return;
};

fn quick_deref(map: *SubMap, scheme: Scheme) Scheme = {
	return if (scheme is TypeVar) deref_sub(map, scheme as TypeVar)
	else scheme;
};

type Solver = struct {
	goals: []Goal,
	backburner: []Goal,
	error_bag: []Goal,
	subs: SubMap,
};

fn prep_pass(this: *Solver) void = {
	for (len(this.backburner) > 0) {
		append(this.goals, this.backburner[0]);
		delete(this.backburner[0]);
	};
};

// returns false when there's nothing left to do :)
fn solve_step(this: *Solver) bool = {
	for (let i : size = 0; i < len(this.goals); i += 1) {
		if (try_solve(this, &this.goals[i])) {
			fmt::println("goal satisfied, removing")!;
			delete(this.goals[i]);
			i -= 1;
		} else {
			fmt::println("goal failed, putting into error bag")!;
			let clone = this.goals[i];
			delete(this.goals[i]);
			append(this.error_bag, clone);
			return false;
		};
	};
	return len(this.goals) != 0;
};

fn try_solve(this: *Solver, goal: *Goal) bool = {
	let copy = *goal : GoalEq; // Will require updating :)
	let copy = (
		quick_deref(&this.subs, copy.0),
		quick_deref(&this.subs, copy.1));

	fmt::print("testing:: ")!;
	show_scheme(copy.0)!;
	fmt::print(" ~ ")!;
	show_scheme(copy.1)!;
	fmt::println(";")!;


	if (copy.0 is TypeVar || copy.1 is TypeVar) {
		let var = (if (copy.0 is TypeVar) copy.0 else copy.1) as TypeVar;
		let val = (if (copy.0 is TypeVar) copy.1 else copy.0);
		append(this.subs, (var, val));
		return true;
	};
	
	fmt::println("resorting to unification")!;
	// assume unify
	let dump = [] : []Goal;
	defer free(dump);
	let unif = unify_to_goals(this, &dump, copy.0, copy.1);
	fmt::printfln("\tunification success: {}", unif)!;
	if (!unif) return false;
	for (let i : size = 0; i < len(dump); i += 1) {
		append(this.goals, dump[i]);
	};
	return true;
};

// This function makes a lot of assumptions:
// 	1) `dump` isn't the actual goal pool
// 	2) variables are substituted by the solver
// 	3) `Scheme` is an immutable type (we do some dirty copying)
// 	4) This function doesn't own any of its arguments.
fn unify_to_goals(this: *Solver, dump: *[]Goal, a: Scheme, b: Scheme) bool = {
	let a = quick_deref(&this.subs, a);
	let b = quick_deref(&this.subs, b);
	if (a is TypeVar || b is TypeVar) {
		append(dump, (a, b) : GoalEq );
		return true;
	};
	if (a is Type && b is Type) {
		return a as Type == b as Type;
	};
	if (a is TypeCons && b is TypeCons) {
		return unify_typecons(
			this, dump,
			a as TypeCons, 
			b as TypeCons);
	};
	return false;
};

fn unify_typecons(this: *Solver, dump: *[]Goal, a: TypeCons, b: TypeCons) bool = {
	if (a.cons != b.cons) {
		return false;
	};
	if (len(a.args) != len(b.args)) {
		return false;
	};
	for (let i : size = 0; i < len(a.args); i += 1) {
		if (!unify_to_goals(this, dump, a.args[i], b.args[i])) {
			return false;
		};
	};
	return true;
};

export fn main() void = {
	fmt::println("Initialising shit first :)")!;
	let solver = Solver { 
		goals = [],
		subs = [],
		backburner = [],
		error_bag = [],
	};
	
	const typ_int   : Type    = 0x100;
	const typ_float : Type    = 0x101;
	const con_vec   : ConsId  = 0x201;
	const typvar_T  : TypeVar = 0;
	const typvar_A  : TypeVar = 1;
	const typvar_C  : TypeVar = 2;
	
	// We're testing using
	// 	`vec::push(&nums, 5);`
	// So
	// 	unify Vec<@0> with Vec<@1>
	// 	unify @1 with Int

	fmt::println("initialising solver")!;
	let goal = (
		TypeCons{ cons = con_vec, args = [typvar_T] },
		TypeCons{ cons = con_vec, args = [typvar_A] }
	) : GoalEq;
	append(solver.goals, goal);

	let goal = (
		typvar_A,
		typ_int,
	) : GoalEq;
	append(solver.goals, goal);
	let goal = (
		TypeCons{ cons = con_vec, args = [typvar_T] },
		TypeCons{ cons = con_vec, args = [typvar_C] }
	) : GoalEq;
	append(solver.goals, goal);
	let goal = (
		typvar_C,
		typ_float,
	) : GoalEq;
	append(solver.goals, goal);
	prep_pass(&solver);
	for (demo_step(&solver)) {yield;};

	if (len(solver.error_bag) > 0) {
		fmt::println("There are some errors")!;
	} else {
		fmt::println("No errors accrued")!;
	};
};

fn demo_step(solver: *Solver) bool = {
	let suc = solve_step(solver);
	fmt::printfln("stepping solver: {}", suc)!;
	fmt::println("printing states")!;
	for (let i : size = 0; i < len(solver.subs); i += 1) {
		let sub = solver.subs[i];
		fmt::printf("@{} -> ", sub.0 : size)!;
		show_scheme(sub.1)!;
		fmt::println("")!;
	};
	return suc;
};
