use io;
use fmt;

// `Typ` should only ever be stored in the TypPool. The only exception to this
// 	is during construction of the Typ value.
export type Typ = struct {
	name:  (str|void),
	repr: (PrimitiveT|FuncT),
};

export type PrimitiveT = void;

export type FuncT = struct {
	rets: *Typ,
	args: []*Typ,
};

export fn print_typ(typ: *Typ) (void|io::error) = {
	if (typ.name is str) {
		fmt::print(typ.name)?;
		return;
	};
	match (typ.repr) {
	case let i : PrimitiveT =>
		fmt::print("<PRIM>")?;
	case let f : FuncT => {
		// print args
		fmt::print("(")?;
		for (let i : size = 0; i < len(f.args); i += 1) {
			print_typ(f.args[i])?;
			if (i + 1 < len(f.args)) {
				fmt::print(", ")?;
			};
		};
		fmt::print(")")?;
		// print sep
		fmt::print(" -> ")?;
		// print ret
		print_typ(f.rets)?;
	};
	};
	return;
};
