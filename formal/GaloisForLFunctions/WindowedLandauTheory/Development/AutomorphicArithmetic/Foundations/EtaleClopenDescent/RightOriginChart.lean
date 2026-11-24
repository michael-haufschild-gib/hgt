import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FixedOriginFibreValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphDiagonalWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedChartDenominators

/-! A right affine chart other than the origin chart cannot contain a
fixed point of the origin fibre. -/

noncomputable section

open GlobalTheory.PD GlobalTheory.SchemeCohomology

namespace GlobalTheory.WH

variable {k F E L : Type} [Field k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] L)

include h in
/-- If a joined evaluation has the local values of a fixed origin
point, its right chart indices are contained in the origin singleton. -/
theorem rightChart_subset_origin_of_fixed_localValues
    {I J : Finset (Fin (d + 1))} (e : RY x j₂ I J →ₐ[k] k)
    (f : OriginFibrePoint k L x)
    (hval : ∀ a b, Val (RY x j₂ I J) e a b ↔ Val (rB k L x {0}) f.1 a b)
    (hfix : IsFix (rB k L x {0}) f.1 j₂ (rB k E x {0})) : J ⊆ {0} := by
  let B := RY x j₂ I J
  let A := rB k E x {0}
  let C := rB k L x {0}
  intro j hj
  apply Finset.mem_singleton.mpr
  by_contra hn
  obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.mpr hn
  let s := j₂ (algebraMap F E (x l.succ / x 0))
  have hs : s ≠ 0 :=
    (map_ne_zero _).mpr ((map_ne_zero _).mpr (div_ne_zero (h.ne l.succ) (h.ne 0)))
  have ha : s⁻¹ ∈ B := by
    change (j₂ (algebraMap F E (x l.succ / x 0)))⁻¹ ∈ B
    rw [← map_inv₀, ← map_inv₀, inv_div]
    have hJ : (rB k E x J).map j₂ ≤ B := (rB_map_le_R2 j₂ (x := x) J).trans le_sup_right
    exact hJ ⟨algebraMap F E (x 0 / x l.succ), chartRatio_mem_rB hj 0, rfl⟩
  let x₀ : A := ⟨_, tco_mem k E x l⟩
  let y₀ : C := rBPullback x {0} x₀
  have hy : f.1 y₀ = 0 := by
    rw [show y₀ = ⟨_, tco_mem k L x l⟩ from rBPullback_originCoordinate x l]
    exact f.2 l
  have hv : Val C f.1 s 0 := by
    have hv := hfix (x₀ : E) x₀.property y₀.property
    change Val C f.1 s (f.1 y₀) at hv
    rwa [hy] at hv
  have hzero := (hval s 0).mpr hv
  have hprod := val_mul B e hzero (val_chartElement B e ⟨s⁻¹, ha⟩)
  rw [mul_inv_cancel₀ hs, zero_mul] at hprod
  have hone := val_chartElement B e (1 : B)
  rw [map_one, Subalgebra.coe_one] at hone
  exact one_ne_zero (val_value_unique B e hone hprod)

end GlobalTheory.WH
