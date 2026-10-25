import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PoissonPrincipalCyclesOnTheScalingSurface
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHalfDensityL1Completion
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiSpectralInclusion
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# Hilbert–Schmidt admission and centered source jets

Every genuine Meyer convolution is Hilbert–Schmidt by its actual resolvent
factorization. Its first column controls every lower Xi jet. The exact centered
jet flow is triangular; after lower jets vanish, its first surviving coordinate
is a character and the next is an affine shear.
-/

noncomputable section
open Complex RHTower ContinuousLinearMap
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The actual resolvent factorization admits every source to Hilbert–Schmidt class. -/
theorem meyerHilbertConvolution_isHilbertSchmidt (g : DeningerMeyerStrongLogTarget) :
    (deningerMeyerHilbertConvolution g).IsHilbertSchmidt := by
  rw [deningerMeyerHilbertConvolution_resolvent g]
  exact deningerMeyerHasseResolvent_isHilbertSchmidt.comp_right _

/-- Each actual lower Hasse jet is bounded by the admitted convolution norm. -/
theorem meyerHasseMoment_norm_le_hsNorm (g : DeningerMeyerStrongLogTarget)
    (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    ‖deningerMeyerHasseMoment g j.val (rho : ℂ)‖ ≤ hsNorm (deningerMeyerHilbertConvolution g) := by
  let q : DeningerArithmeticJetCoordinate := ⟨rho, j⟩
  let q0 : DeningerArithmeticJetCoordinate := ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  have he : deningerMeyerHasseMoment g j.val (rho : ℂ) =
      inner ℂ (xiDivisorHilbertBasis q)
        (deningerMeyerHilbertConvolution g (xiDivisorHilbertBasis q0)) := by
    rw [xiDivisorHilbertBasis_apply, xiDivisorHilbertBasis_apply,
      lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    exact (deningerMeyerHilbertConvolution_first_column g q).symm
  rw [he]
  calc
    _ ≤ ‖xiDivisorHilbertBasis q‖ *
        ‖deningerMeyerHilbertConvolution g (xiDivisorHilbertBasis q0)‖ := norm_inner_le_norm _ _
    _ ≤ ‖xiDivisorHilbertBasis q‖ *
        (‖deningerMeyerHilbertConvolution g‖ * ‖xiDivisorHilbertBasis q0‖) :=
      mul_le_mul_of_nonneg_left ((deningerMeyerHilbertConvolution g).le_opNorm _)
        (norm_nonneg _)
    _ = ‖deningerMeyerHilbertConvolution g‖ := by
      rw [xiDivisorHilbertBasis.orthonormal.1 q,
        xiDivisorHilbertBasis.orthonormal.1 q0, mul_one, one_mul]
    _ ≤ _ := opNorm_le_hsNorm (meyerHilbertConvolution_isHilbertSchmidt g)

/-- Raw jets have the same bound with their explicit factorial normalization. -/
theorem meyerRawJet_norm_le_factorial_mul_hsNorm (g : DeningerMeyerStrongLogTarget)
    (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    ‖deningerMeyerStrongLogMellinJetLM j.val (rho : ℂ) g‖ ≤
      (j.val.factorial : ℝ) * hsNorm (deningerMeyerHilbertConvolution g) := by
  have hf : (j.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
  have he : deningerMeyerStrongLogMellinJetLM j.val (rho : ℂ) g =
      (j.val.factorial : ℂ) * deningerMeyerHasseMoment g j.val (rho : ℂ) := by
    rw [deningerMeyerHasseMoment]
    field_simp [hf]
  rw [he, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (meyerHasseMoment_norm_le_hsNorm g rho j) (Nat.cast_nonneg _)

/-- Centering preserves the complete triangular jet law, including the nilpotent shear. -/
theorem meyerCenteredSource_jet_flow (c : ℝ) (g : DeningerMeyerStrongLogTarget)
    (k : ℕ) (s : ℂ) :
    deningerMeyerStrongLogMellinJetLM k s (deningerMeyerStrongLogCenteredFlow c g) =
      Complex.exp ((c : ℂ) * (s - 1 / 2)) *
        ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℂ) * (c : ℂ) ^ i * deningerMeyerStrongLogMellinJetLM (k - i) s g := by
  rw [deningerMeyerStrongLogCenteredFlow, LinearMap.smul_apply, map_smul,
    deningerMeyerStrongLogMellinJetLM_flow]
  simp only [smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : Complex.exp (-(c : ℂ) / 2) * Complex.exp ((c : ℂ) * s) =
      Complex.exp ((c : ℂ) * (s - 1 / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (Complex.exp (-(c : ℂ) / 2) * Complex.exp ((c : ℂ) * s)) *
        ((k.choose i : ℂ) * (c : ℂ) ^ i * deningerMeyerStrongLogMellinJetLM (k - i) s g) := by ring
    _ = _ := by rw [he]

/-- With lower jets zero, the first surviving raw jet has an exact character orbit. -/
theorem meyerCenteredSource_jet_of_lower_zero (c : ℝ) (g : DeningerMeyerStrongLogTarget)
    (k : ℕ) (s : ℂ)
    (hz : ∀ i < k, deningerMeyerStrongLogMellinJetLM i s g = 0) :
    deningerMeyerStrongLogMellinJetLM k s (deningerMeyerStrongLogCenteredFlow c g) =
      Complex.exp ((c : ℂ) * (s - 1 / 2)) * deningerMeyerStrongLogMellinJetLM k s g := by
  rw [meyerCenteredSource_jet_flow, Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul, Nat.sub_zero]
  · intro i hi hn
    have hik := Finset.mem_range.mp hi
    rw [hz (k - i) (by omega), mul_zero]
  · intro h0
    exact False.elim (h0 (Finset.mem_range.mpr (by omega)))

/-- The next jet of a first surviving coefficient has precisely one affine shear. -/
theorem meyerCenteredSource_next_jet_of_lower_zero (c : ℝ) (g : DeningerMeyerStrongLogTarget)
    (k : ℕ) (s : ℂ)
    (hz : ∀ i < k, deningerMeyerStrongLogMellinJetLM i s g = 0) :
    deningerMeyerStrongLogMellinJetLM (k + 1) s (deningerMeyerStrongLogCenteredFlow c g) =
      Complex.exp ((c : ℂ) * (s - 1 / 2)) *
        (deningerMeyerStrongLogMellinJetLM (k + 1) s g +
          ((k + 1 : ℕ) : ℂ) * (c : ℂ) * deningerMeyerStrongLogMellinJetLM k s g) := by
  rw [meyerCenteredSource_jet_flow, Finset.sum_range_succ']
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul,
      Nat.sub_zero, Nat.zero_add, Nat.choose_one_right, pow_one, Nat.add_sub_cancel]
    ring
  · intro i hi hn
    have hik := Finset.mem_range.mp hi
    rw [hz (k + 1 - (i + 1)) (by omega), mul_zero]
  · intro h0
    exact False.elim (h0 (Finset.mem_range.mpr (by omega)))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
