import Mathlib.Geometry.Convex.Cone.Simplicial
import Mathlib.LinearAlgebra.Basis.Basic

namespace PointedCone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G H K G' H' : Type*}
variable [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- Transport finite independent cone generators through embeddings. -/
theorem IsSimplicial.map {C : PointedCone R G} (hC : C.IsSimplicial)
    (f : G →ₗ[R] H) (hf : Function.Injective f) : (C.map f).IsSimplicial :=
by
  obtain ⟨s, hs, hli, rfl⟩ := hC
  refine ⟨f '' s, hs.image f, hli.id_imageₛ ?_, ?_⟩
  · intro x hx y hy hxy
    exact hf hxy
  · change Submodule.span ({c : R // 0 ≤ c}) (f '' s) =
      Submodule.map (f : G →ₗ[({c : R // 0 ≤ c})] H)
        (Submodule.span ({c : R // 0 ≤ c}) s)
    exact (Submodule.map_span (f : G →ₗ[({c : R // 0 ≤ c})] H) s).symm

end PointedCone
