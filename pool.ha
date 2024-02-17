use fmt;

def BUCKETSIZE : size = 32; 

// Dropping this drops all of the types in the type pool.
// only drop the type pool AFTER all references to it are dropped.
type TypPool = struct {
	buckets: [](size, *[BUCKETSIZE]Typ),
};

fn register_typ(pool: *TypPool, typ: Typ) *Typ = {
	let init = len(&pool.buckets);
	let ind = if (init == 0) {
		let buff : *[BUCKETSIZE]Typ
			= alloc([] : [BUCKETSIZE]Typ);
		append(pool.buckets, (0, buff));
		yield init;
	} else init - 1;
	if (pool.buckets[ind].0 >= BUCKETSIZE) {
		let buff : *[BUCKETSIZE]Typ
			= alloc([] : [BUCKETSIZE]Typ);
		append(pool.buckets, (0, buff));
		ind += 1;
	};
	let bucket = &pool.buckets[ind];
	let bind = bucket.0;
	bucket.0 += 1;
	bucket.1[bind] = typ;
	return &bucket.1[bind];
};

fn drop_pool(pool: *TypPool) void = {
	for (let i = 0: size; i < len(&pool.buckets); i += 1) {
		free(pool.buckets[i].1);
	};
	free(pool.buckets);
	return;
};
