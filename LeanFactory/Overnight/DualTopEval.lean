import Mathlib.Geometry.Convex.Cone.Dual


namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- A linear functional nonnegative on the whole module is zero. -/
theorem dual_top_eval :
    dual (Module.Dual.eval R G) (⊤ : PointedCone R G) =
      (⊥ : PointedCone R (Module.Dual R G)) :=
by
  apply dual_univ
  intro f g h
  ext x
  simpa [Module.Dual.eval, LinearMap.flip_apply] using congrArg (fun q => q x) h

end PointedCone
