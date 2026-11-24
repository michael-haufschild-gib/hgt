import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundlePullback
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Compatible units glue by gluing their sections and inverses. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.Semi

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : X.Opens}

/-- Unit-valued sections on an open cover glue uniquely. -/
theorem existsUnique_glueUnits (V : ι → X.Opens) (hV : ∀ i, V i ≤ U)
    (hcov : U ≤ ⨆ i, V i) (a : ∀ i, Γ(X, V i)ˣ)
    (h : ∀ i j, res (inf_le_left : V i ⊓ V j ≤ V i) (a i) =
      res (inf_le_right : V i ⊓ V j ≤ V j) (a j)) :
    ∃! z : Γ(X, U)ˣ, ∀ i, res (hV i) z = a i := by
  let F := X.toLocallyRingedSpace.toSheafedSpace.sheaf
  have ha : TopCat.Presheaf.IsCompatible F.1 V (fun i => (a i : Γ(X, V i))) :=
    fun i j => congrArg Units.val (h i j)
  have hb : TopCat.Presheaf.IsCompatible F.1 V (fun i => (↑((a i)⁻¹) : Γ(X, V i))) := by
    intro i j
    have e := congrArg Inv.inv (h i j)
    rw [← map_inv, ← map_inv] at e
    exact congrArg Units.val e
  obtain ⟨s, hs, hs_unique⟩ := F.existsUnique_gluing' V U (fun i => homOfLE (hV i)) hcov _ ha
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' V U (fun i => homOfLE (hV i)) hcov _ hb
  have hst : s * t = 1 := by
    obtain ⟨z, -, hz⟩ := F.existsUnique_gluing' V U (fun i => homOfLE (hV i)) hcov
      (fun _ => 1) (fun i j => by rw [map_one, map_one])
    have hm : ∀ i, F.1.map (homOfLE (hV i)).op (s * t) = 1 := by
      intro i
      rw [map_mul, hs i, ht i]
      exact (a i).val_inv
    exact (hz (s * t) hm).trans (hz 1 (fun _ => map_one _)).symm
  refine ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, fun i => Units.ext (hs i), ?_⟩
  intro z hz
  apply Units.ext
  exact hs_unique z.val (fun i => congrArg Units.val (hz i))

/-- Sections of the unit sheaf are determined by their restrictions to a cover. -/
theorem units_ext_on_cover (V : ι → X.Opens) (hV : ∀ i, V i ≤ U)
    (hcov : U ≤ ⨆ i, V i) {a b : Γ(X, U)ˣ}
    (h : ∀ i, res (hV i) a = res (hV i) b) : a = b := by
  obtain ⟨c, -, hc⟩ := existsUnique_glueUnits V hV hcov (fun i => res (hV i) b)
    (fun i j => by rw [res_res, res_res])
  exact (hc a h).trans (hc b (fun _ => rfl)).symm

end ReciprocityTheory.ChartRestriction.G.Semi
