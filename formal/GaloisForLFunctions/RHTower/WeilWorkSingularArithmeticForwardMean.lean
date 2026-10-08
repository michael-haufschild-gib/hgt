import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardCoefficients
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseForwardSummatory
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The actual residue is the logarithmic first mean

The centered ordinary Dirichlet convergence already proved for the source
pays both coordinates of the logarithmic mean. No mean is postulated.
-/

open Complex Filter Topology
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem sum_Icc_one_eq_range {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ n ∈ Finset.range N, f (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- The two existing definitions use exactly the same truncated logarithm. -/
theorem forwardCoeff_eq_sourceCoeff (lam : ℕ → ℝ) :
    forwardCoeff lam = WeilWorkSettledPhase.sourceCoeff lam := by
  unfold forwardCoeff WeilWorkSettledPhase.sourceCoeff
  congr 1
  funext n
  simp only [logZetaCoeff, IntegerMassRigidity.lamLog]
  split_ifs <;> simp [Complex.ofReal_div]

/-- Ordinary harmonic convergence after centering at the literal pole residue. -/
theorem exists_centered_forward_harmonic_limit {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ L : ℂ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (forwardCoeff lam n - WeilWorkSettledPhase.sourceCompletion hW 1) / n)
        atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := WeilWorkSettledPhase.centered_forward_dirichletConvergesAt
    hW (s := 1) (by norm_num)
  refine ⟨L, hL.congr fun N => ?_⟩
  rw [sum_Icc_one_eq_range]
  simp [dirichletPartialSum, Complex.cpow_neg_one, forwardCoeff_eq_sourceCoeff,
    Nat.cast_add, Nat.cast_one, div_eq_mul_inv]

/-- The harmonic weight has leading coefficient one. -/
theorem tendsto_harmonic_weight_div_log :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n) / Real.log N)
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (Real.tendsto_harmonic_sub_log.div_atTop hlog).add_const 1
  simp only [zero_add] at ht
  refine ht.congr' ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with N hN
  rw [sum_Icc_one_eq_range]
  have hh : (harmonic N : ℝ) = ∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1) := by
    simp [harmonic, one_div]
  rw [hh]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

private theorem mean_of_centered {f : ℕ → ℝ} {B L : ℝ}
    (h : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (f n - B) / n)
      atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, f n / n) / Real.log N)
      atTop (𝓝 B) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (h.div_atTop hlog).add (tendsto_harmonic_weight_div_log.const_mul B)
  simp only [mul_one, zero_add] at ht
  apply ht.congr
  intro N
  simp only [sub_div, Finset.sum_sub_distrib]
  rw [← mul_div_assoc, Finset.mul_sum]
  simp only [mul_one_div]
  ring

/-- Both coordinates of the actual logarithmic first mean equal the residue. -/
theorem forwardCoeff_harmonic_mean {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (forwardCoeff lam n).re / n) /
      Real.log N) atTop (𝓝 (WeilWorkSettledPhase.sourceCompletion hW 1).re) ∧
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (forwardCoeff lam n).im / n) /
      Real.log N) atTop (𝓝 (WeilWorkSettledPhase.sourceCompletion hW 1).im) := by
  obtain ⟨L, hL⟩ := exists_centered_forward_harmonic_limit hW
  constructor
  · apply mean_of_centered (L := L.re)
    have ht := (Complex.continuous_re.tendsto L).comp hL
    simpa only [Function.comp_def, Complex.re_sum, ← Complex.ofReal_natCast,
      Complex.div_ofReal_re, Complex.sub_re] using ht
  · apply mean_of_centered (L := L.im)
    have ht := (Complex.continuous_im.tendsto L).comp hL
    simpa only [Function.comp_def, Complex.im_sum, ← Complex.ofReal_natCast,
      Complex.div_ofReal_im, Complex.sub_im] using ht

end RHTower.WeilSingularArithmetic
