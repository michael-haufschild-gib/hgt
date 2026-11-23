import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenbasis
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.PositiveRoot

/-! # Faithful positive Hilbert–Schmidt pairings

In the eigenbasis of a positive injective Hilbert–Schmidt operator, its
pairing with a positive observable is a sum of squared amplitudes with
strictly positive weights.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem positive_diagonal {C : H →L[ℂ] H} (hC : C.IsPositive) (x : H) :
    inner ℂ (C x) x = ((‖positiveRoot C x‖^2:ℝ):ℂ) := by
  let Z := positiveRoot C
  have h := adjoint_inner_left Z x (Z x)
  rw [show adjoint Z = Z from (positiveRoot_positive C).isSelfAdjoint.star_eq] at h
  change inner ℂ ((Z^2) x) x = _ at h
  rw [sq_positiveRoot hC] at h
  rw [h,Complex.ofReal_pow]
  exact inner_self_eq_norm_sq_to_K _

/-- A positive injective Hilbert–Schmidt operator detects every nonzero positive Hilbert–Schmidt operator. -/
theorem faithful_hs_pairing {B C : H →L[ℂ] H} (hB : B.IsPositive) (hBh : B.IsHilbertSchmidt)
    (hi : Function.Injective B) (hC : C.IsPositive) (hCh : C.IsHilbertSchmidt) :
    0 ≤ (hsInner C B).re ∧ ((hsInner C B).re = 0 ↔ C = 0) := by
  letI : Fact (IsCompactOperator B) := ⟨hBh.isCompactOperator⟩
  have hk (x : H) (hx : B x = 0) : x = 0 := hi (hx.trans (map_zero B).symm)
  let b := eigenHilbertBasis hB.isSymmetric hk
  have he (i : EigenIndex B) : B (b i) = i.1.val • b i := by
    change B (eigenHilbertBasis hB.isSymmetric hk i) = _ • eigenHilbertBasis hB.isSymmetric hk i
    rw [eigenHilbertBasis_apply,apply_eigenVec]
  have hp (i : EigenIndex B) : 0 < i.1.val.re := by
    have hn := hB.re_inner_nonneg_right (b i)
    change 0 ≤ (inner ℂ (b i) (B (b i))).re at hn
    rw [he,inner_smul_right,inner_self_eq_norm_sq_to_K,b.orthonormal.norm_eq_one] at hn
    simp only [RCLike.ofReal_one,one_pow,mul_one] at hn
    apply lt_of_le_of_ne hn
    intro hz
    exact i.1.property ((eigenValue_real hB.isSymmetric i).symm.trans
      (by rw [← hz,Complex.ofReal_zero]))
  have term (i : EigenIndex B) : (inner ℂ (C (b i)) (B (b i))).re =
      i.1.val.re*‖positiveRoot C (b i)‖^2 := by
    rw [he,inner_smul_right,positive_diagonal hC,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
  have hs := Complex.hasSum_re (hCh.summable_inner hBh b).hasSum
  rw [← hsInner_eq_tsum_basis hCh hBh b] at hs
  have mass : HasSum (fun i : EigenIndex B => i.1.val.re*‖positiveRoot C (b i)‖^2) (hsInner C B).re := by
    simpa only [term] using hs
  have hnn (i : EigenIndex B) : 0 ≤ i.1.val.re*‖positiveRoot C (b i)‖^2 := mul_nonneg (hp i).le (sq_nonneg _)
  refine ⟨mass.tsum_eq ▸ tsum_nonneg hnn,?_,?_⟩
  · intro hz
    have zero_root : positiveRoot C = 0 := by
      refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) ?_
      rintro _ ⟨i,rfl⟩
      have hle := mass.summable.le_tsum i (fun j _ => hnn j)
      rw [mass.tsum_eq,hz] at hle
      have hn := (mul_eq_zero.mp (le_antisymm hle (hnn i))).resolve_left (hp i).ne'
      change positiveRoot C (b i) = 0
      by_contra hne
      exact (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)) hn
    rw [← sq_positiveRoot hC,zero_root,zero_pow (by decide : 2 ≠ 0)]
  · rintro rfl
    simp [hsInner]

#print axioms faithful_hs_pairing

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
