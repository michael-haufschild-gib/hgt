import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.Cutoff
import GaloisForLFunctions.HTGeometry.LidskiiPowerTrace
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.SpectralBasis

/-! # Cofinal even operator traces detect a hard occupation cutoff -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set ContinuousLinearMap _root_.RHTower

/-- Natural orders starting with the first ordinary trace of squared critical heat. -/
def ordinaryMomentOrder (m : ℕ) : GibbsExponent := ⟨(m+2:ℕ),Nat.cast_pos.mpr (by omega)⟩

/-- Every even operator trace from the fourth onward is the convergent moment of the physical spectrum. -/
theorem projected_even_trace (P : Projection) {r : ℕ} (dim : MissingDimension P r) (hc : Conserving (projected P)) (m : ℕ) :
    opTrace (projected P^(2*(m+2))) = ((∑' n, (physicalSpectrum P dim hc n).val^(m+2):ℝ):ℂ) := by
  let S := projected P^2
  have hhs : S.IsHilbertSchmidt := conserving_square_hs ⟨projected P,projected_positive P,hc⟩
  have hpos := projected_square_positive P
  have hfac : S^(m+2) = S ∘L (S ∘L S^m) := by
    change S^(m+2) = S*(S*S^m)
    rw [pow_succ',pow_succ']
  rw [pow_mul,show projected P^2 = S from rfl,opTrace_pow_eq_tsum_sgVal_pow hhs.isCompactOperator hpos.isSymmetric (by omega : 0<m+2)
    hhs (hhs.comp_right _) hfac,Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [← projected_square_sgVal P dim hc n,Complex.ofReal_pow]

theorem momentLoss_ordinary_eq_operator_deficit (P : Projection) {r : ℕ} (dim : MissingDimension P r)
    (hc : Conserving (projected P)) (m : ℕ) :
    momentLoss (ordinaryMomentOrder m) (physicalSpectrum P dim hc) =
      (riemannZeta ((m+2:ℕ):ℂ)).re - (opTrace (projected P^(2*(m+2)))).re := by
  have ho : 1 < (ordinaryMomentOrder m).val := by change (1:ℝ)<(m+2:ℕ); exact_mod_cast (show 1<m+2 by omega)
  rw [momentLoss_eq_trace_difference _ ho,projected_even_trace P dim hc m,Complex.ofReal_re]
  simp only [ordinaryMomentOrder,Complex.ofReal_natCast,Real.rpow_natCast]

/-- The entire family of ordinary even operator trace tests is equivalent to fixing the low energies exactly. -/
theorem even_operator_traces_cutoff (P : Projection) (dim : MissingDimension P 1) (hc : Conserving (projected P))
    {h : ℝ} (hh : 0 ≤ h) :
    (∀ m : ℕ, (riemannZeta ((m+2:ℕ):ℂ)).re - (opTrace (projected P^(2*(m+2)))).re ≤ h^(m+2)) ↔
      ∀ k, h < occupationWeight k → (physicalSpectrum P dim hc k).val = occupationWeight k := by
  let b := physicalSpectrum P dim hc
  have hcof (a : GibbsExponent) : ∃ q ∈ range ordinaryMomentOrder, a ≤ q := by
    refine ⟨ordinaryMomentOrder ⌈a.val⌉₊,⟨_,rfl⟩,?_⟩
    change a.val ≤ ((⌈a.val⌉₊+2:ℕ):ℝ)
    exact (Nat.le_ceil a.val).trans (Nat.cast_le.mpr (Nat.le_add_right _ 2))
  have he := cofinal_moment_ceilings_iff b hh (range ordinaryMomentOrder) hcof
  simp only [forall_mem_range] at he
  simpa only [b,momentLoss_ordinary_eq_operator_deficit,ordinaryMomentOrder,Real.rpow_natCast] using he

#print axioms projected_even_trace
#print axioms momentLoss_ordinary_eq_operator_deficit
#print axioms even_operator_traces_cutoff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
