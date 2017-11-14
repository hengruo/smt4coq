let names = [
    ("Ind(Coq.Init.Datatypes.nat,0)", "Int");
    ("Cst(Coq.Init.Nat.add)", "+");
    ("Cst(Coq.Init.Nat.sub)", "-");
    ("Cst(Coq.Init.Nat.mul)", "*");
    ("Cst(Coq.Init.Nat.div)", "/");
    ("Cst(Coq.Init.Nat.modulo)", "mod");
    ("Cst(Coq.Init.Nat.eqb)", "=");
    ("Cst(Coq.Init.Nat.leb)", "<=");
    ("Cst(Coq.Init.Nat.ltb)", "<");

    ("Ind(Coq.Init.Peano.le,0)", "<=");
    ("Ind(Coq.Init.Peano.lt,0)", "<");
    ("Ind(Coq.Init.Peano.ge,0)", "=>");
    ("Ind(Coq.Init.Peano.gt,0)", ">");

    ("Ind(Coq.Numbers.BinNums.Z,0)", "Int");
    ("Cst(Coq.ZArith.BinInt.Z.add)", "+");
    ("Cst(Coq.ZArith.BinInt.Z.sub)", "-");
    ("Cst(Coq.ZArith.BinInt.Z.mul)", "*");
    ("Cst(Coq.ZArith.BinInt.Z.div)", "/");
    ("Cst(Coq.ZArith.BinInt.Z.modulo)", "mod");
    ("Cst(Coq.ZArith.BinInt.Z.le)", "<=");
    ("Cst(Coq.ZArith.BinInt.Z.lt)", "<");
    ("Cst(Coq.ZArith.BinInt.Z.ge)", ">=");
    ("Cst(Coq.ZArith.BinInt.Z.gt)", ">");

    ("Ind(Coq.Init.Datatypes.bool,0)", "Bool");
    ("Constr(Coq.Init.Datatypes.bool,0,2)", "false");
    ("Constr(Coq.Init.Datatypes.bool,0,1)", "true");
    ("Cst(Coq.Init.Datatypes.andb)", "&&");
    ("Cst(Coq.Init.Datatypes.orb)", "or");
    ("Cst(Coq.Init.Datatypes.notb)", "not");
    ("Cst(Coq.Init.Datatypes.negb)", "not");
    ("Cst(Coq.Init.Datatypes.xorb)", "xor");

    ("Cst(Coq.Init.Logic.not)", "not");
    ("Cst(Coq.Init.Logic.or)", "or");
    ("Ind(Coq.Init.Logic.or,0)", "or");
    ("Ind(Coq.Init.Logic.and,0)", "&&");
    ("Ind(Coq.Init.Logic.eq,0)", "=");
    ("Ind(Coq.Init.Logic.False,0)", "false");

    ("Ind(compcert.lib.Integers.Int64.int,0)", "_ BitVec 64");
    ("Cst(compcert.lib.Integers.Int64.repr)", "(_ int2bv 64)");
    ("Cst(compcert.lib.Integers.Int64.unsigned)", "bv2int");
    ("Cst(compcert.lib.Integers.Int64.one)", "#x0000000000000001");
    ("Cst(compcert.lib.Integers.Int64.mone)", "#xffffffffffffffff");
    ("Cst(compcert.lib.Integers.Int64.zero)", "#x0000000000000000");
    ("Cst(compcert.lib.Integers.Int64.and)", "bvand");
    ("Cst(compcert.lib.Integers.Int64.or)", "bvor");
    ("Cst(compcert.lib.Integers.Int64.xor)", "bvxor");
    ("Cst(compcert.lib.Integers.Int64.not)", "bvnot");
    ("Cst(compcert.lib.Integers.Int64.shru)", "bvlshr");
    ("Cst(compcert.lib.Integers.Int64.shr)", "bvashr");
    ("Cst(compcert.lib.Integers.Int64.shl)", "bvshl");
    ("Cst(compcert.lib.Integers.Int64.neg)", "bvneg");
    ("Cst(compcert.lib.Integers.Int64.add)", "bvadd");
    ("Cst(compcert.lib.Integers.Int64.sub)", "bvsub");
    ("Cst(compcert.lib.Integers.Int64.mul)", "bvmul");
    ("Cst(compcert.lib.Integers.Int64.mods)", "bvsmod");
    ("Cst(compcert.lib.Integers.Int64.modu)", "bvurem");
    ("Cst(compcert.lib.Integers.Int64.divs)", "bvsdiv");
    ("Cst(compcert.lib.Integers.Int64.divu)", "bvudiv");
    ("Cst(compcert.lib.Integers.Int64.zwordsize)", "64");
    ("Cst(compcert.lib.Integers.Int64.ltu)", "bvult");
    ("Cst(compcert.lib.Integers.Int64.lt)", "bvslt");

    ("Ind(compcert.lib.Integers.Int.int,0)", "_ BitVec 32");
    ("Cst(compcert.lib.Integers.Int.repr)", "(_ int2bv 32)");
    ("Cst(compcert.lib.Integers.Int.unsigned)", "bv2int");
    ("Cst(compcert.lib.Integers.Int.one)", "#x00000001");
    ("Cst(compcert.lib.Integers.Int.mone)", "#xffffffff");
    ("Cst(compcert.lib.Integers.Int.zero)", "#x00000000");
    ("Cst(compcert.lib.Integers.Int.and)", "bvand");
    ("Cst(compcert.lib.Integers.Int.or)", "bvor");
    ("Cst(compcert.lib.Integers.Int.xor)", "bvxor");
    ("Cst(compcert.lib.Integers.Int.not)", "bvnot");
    ("Cst(compcert.lib.Integers.Int.shru)", "bvlshr");
    ("Cst(compcert.lib.Integers.Int.shr)", "bvashr");
    ("Cst(compcert.lib.Integers.Int.shl)", "bvshl");
    ("Cst(compcert.lib.Integers.Int.neg)", "bvneg");
    ("Cst(compcert.lib.Integers.Int.add)", "bvadd");
    ("Cst(compcert.lib.Integers.Int.sub)", "bvsub");
    ("Cst(compcert.lib.Integers.Int.mul)", "bvmul");
    ("Cst(compcert.lib.Integers.Int.mods)", "bvsmod");
    ("Cst(compcert.lib.Integers.Int.modu)", "bvurem");
    ("Cst(compcert.lib.Integers.Int.divs)", "bvsdiv");
    ("Cst(compcert.lib.Integers.Int.divu)", "bvudiv");
    ("Cst(compcert.lib.Integers.Int.zwordsize)", "32");
    ("Cst(compcert.lib.Integers.Int.ltu)", "bvult");
    ("Cst(compcert.lib.Integers.Int.lt)", "bvslt");
]

let rec list_to_map l =
  match l with
  | (a, b)::ls -> let t = (list_to_map ls) in Hashtbl.add t a b;t
  | [] -> Hashtbl.create 10

let name_map = list_to_map names
