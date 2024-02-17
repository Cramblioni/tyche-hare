
// slightly more freeform. It does not own any of the useful information it is
// used to retrieve. It also forms a linked list of contexts, allowing for
// nesting and overriding. 
type TypContext = struct {
	ident_map: [](IdentId, nullable *Typ),
	pool: *TypPool,
	outer: nullable *TypContext,
};

fn drop_context(context: *TypContext) void = {
	free(context.ident_map);
	return;
};

fn lookup(context: *TypContext, ident: IdentId) nullable *Typ = {
	for (let i : IdentId = 0; i < len(&context.ident_map); i += 1) {
		if (ident != context.ident_map[i].0) {
			continue;
		};
		return context.ident_map[i].1;
	};
	match (context.outer) {
		case null =>
			return null;
		case let x : *TypContext =>
			return lookup(x, ident);
	};
};

type RedefinitionError = !void;

fn insert_context(context: *TypContext, ident: IdentId, typ: *Typ) 
(void | RedefinitionError) = {
	for (let i : size = 0; i < len(&context.ident_map); i += 1) {
		let slot = context.ident_map[i];
		if (slot.0 == ident) {
			return RedefinitionError;
		};
	};
	append(context.ident_map, (ident, typ));
	return;
};
fn remove_context(context: *TypContext, ident: IdentId) void = {
	for (let i : size = 0; i < len(&context.ident_map); i += 1) {
		let slot = context.ident_map[i];
		if (slot.0 == ident) {
			delete(context.ident_map[i]);
			break;
		};
	};
	return;
};
