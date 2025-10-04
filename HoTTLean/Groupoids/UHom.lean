def liftSeqObjs (i : Nat) (h : i < 4) : Universe Grpd.IsIsofibration.{4} :=
  match i with
  | 0 => U.{0,4}
  | 1 => U.{1,4}
  | 2 => U.{2,4}
  | 3 => U.{3,4}
  | (n+4) => by omega

-- TODO: rename UHom to Universe.Lift
def lift : UHom U.{v, max u (v+2)} U.{v+1, max u (v+2)} :=
    @UHom.ofTyIsoExt _ _ _ _ _ _
    { mapTy := U.liftTy.{v,max u (v+2)}
      mapTm := U.liftTm
      pb := IsPullback.liftTm_isPullback }
    asSmallClosedType
    isoExtAsSmallClosedType.{v,u}

def liftSeqHomSucc' (i : Nat) (h : i < 3) :
    UHom (liftSeqObjs i (by omega)) (liftSeqObjs (i + 1) (by omega)) :=
  match i with
  | 0 => lift.{0,4}
  | 1 => lift.{1,4}
  | 2 => lift.{2,4}
  | (n+3) => by omega

/--
  The groupoid natural model with three nested representable universes
  within the ambient natural model.
-/
def liftSeq : UHomSeq Grpd.IsIsofibration.{4} where
  length := 3
  objs := liftSeqObjs
  homSucc' := liftSeqHomSucc'
