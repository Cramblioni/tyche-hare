use fmt;
use io;
// Ast is a reference type.
// These should only be owned by value during construction.

type Ast = struct {
	val: (IdentN|FuncCallN|IntLitN),
	typ: nullable *Typ,
	loc: SourceLoc,
};

type IdentId = size;
type IdentN = struct {
	id: IdentId,
};

type FuncCallN = struct {
	targe: *Ast,
	args: []*Ast,
};

type IntLitN = int;


// Leaves the reference invalid;
fn drop_ast(ast: *Ast) void = {
	if (ast.val is FuncCallN) {
		let inner = &(ast.val as FuncCallN);
		drop_ast(inner.targe);
		for (let i = 0: size; i < len(inner.args); i += 1) {
			drop_ast(inner.args[i]);
		};
		// free(inner.args);
	};
	free(ast);
};

fn goals_from_ast(ast: *Ast) []*Ast = {
	let res = [] : []*Ast;
	goals_from_ast_inplace(&res, ast);
	return res;
};
fn goals_from_ast_inplace(goals: *[]*Ast, ast: *Ast) void = {
	append(goals, ast);
	let inner : *FuncCallN = if (ast.val is FuncCallN) {
		yield &(ast.val as FuncCallN);
	} else {
		return;
	};
	
	goals_from_ast_inplace(goals, inner.targe);
	for (let i : size = 0; i < len(inner.args); i+= 1) {
        		goals_from_ast_inplace(goals, inner.args[i]);
	};
};

fn debug_ast(ast: *Ast) (void | io::error) = {
	match (ast.val) {
		case let ident : IdentN =>
			fmt::printf("@{}", ident.id: size)?;
		case let litint : IntLitN =>
			fmt::printf("{}", litint: size)?;
		case let func : FuncCallN => {
			debug_ast(func.targe)?;
			fmt::print("(")?;
			for (let i : size = 0; i < len(func.args); i += 1) {
				debug_ast(func.args[i])?;
				if (i + 1 < len(func.args)) {
					fmt::print(", ")?;
				};
			};
			fmt::print(")")?;
		};
	};
};

type SourceLoc = struct {
	blob: *str,
	start: size,
	end: size,
};
