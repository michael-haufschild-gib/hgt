import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-! # A norm bound for ordered positive square roots -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

private theorem squares_order_norm {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {d g : A} (hd : 0 ≤ d) (hg : 0 ≤ g) (hs : g^2 ≤ d^2) :
    0 ≤ d-g ∧ ‖d-g‖ ≤ ‖d‖ ∧ ‖d-g‖^2 ≤ ‖d^2-g^2‖ := by
  let r := Real.sqrt ‖d^2-g^2‖
  let R := algebraMap ℝ A r
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hR : 0 ≤ R := by
    change 0 ≤ algebraMap ℝ A r
    rw [Algebra.algebraMap_eq_smul_one]
    exact smul_nonneg hr zero_le_one
  have hfirst := CFC.sqrt_le_sqrt _ _ hs
  rw [CFC.sqrt_sq _ hg,CFC.sqrt_sq _ hd] at hfirst
  have hpos := sub_nonneg.mpr hfirst
  refine ⟨hpos,CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos (sub_le_self _ hg),?_⟩
  have hsq : R*R = algebraMap ℝ A ‖d^2-g^2‖ := by
    change algebraMap ℝ A r * algebraMap ℝ A r = _
    rw [← map_mul,Real.mul_self_sqrt (norm_nonneg _)]
  have hcross : 0 ≤ R*g := by
    change 0 ≤ algebraMap ℝ A r*g
    rw [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
    exact smul_nonneg hr hg
  have hc : g*R = R*g := (Algebra.commutes r g).symm
  have htop : d^2 ≤ (g+R)^2 := calc
    d^2 ≤ algebraMap ℝ A ‖d^2-g^2‖ + g^2 :=
      sub_le_iff_le_add.mp ((sub_nonneg.mpr hs).isSelfAdjoint.le_algebraMap_norm_self)
    _ ≤ (g+R)^2 := by
      rw [← hsq,pow_two g,pow_two (g+R),add_mul,mul_add,mul_add,hc]
      exact le_of_sub_nonneg (by
        have he : g*g+R*g+(R*g+R*R)-(R*R+g*g) = R*g+R*g := by abel
        rw [he]
        exact add_nonneg hcross hcross)
  have hlast := CFC.sqrt_le_sqrt _ _ htop
  rw [CFC.sqrt_sq _ hd,CFC.sqrt_sq _ (add_nonneg hg hR),add_comm g R] at hlast
  have hn := (CStarAlgebra.norm_le_iff_le_algebraMap (d-g) hr hpos).mpr (sub_le_iff_le_add.mpr hlast)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt (norm_nonneg _))

/-- An ordered square deficit bounds the error of its positive roots with constant one. -/
theorem positive_square_comparison {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {D G : H →L[ℂ] H} (hD : D.IsPositive) (hG : G.IsPositive)
    (hdiff : (D^2-G^2).IsPositive) :
    (D-G).IsPositive ∧ ‖D-G‖ ≤ ‖D‖ ∧ ‖D-G‖^2 ≤ ‖D^2-G^2‖ := by
  have h := squares_order_norm ((nonneg_iff_isPositive D).mpr hD)
    ((nonneg_iff_isPositive G).mpr hG) (sub_nonneg.mp ((nonneg_iff_isPositive _).mpr hdiff))
  exact ⟨(nonneg_iff_isPositive _).mp h.1,h.2⟩

#print axioms positive_square_comparison

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
