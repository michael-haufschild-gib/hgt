import GaloisForLFunctions.RHTower.MobiusSquareResidueGcdBound
import GaloisForLFunctions.RHTower.CausalMobiusThetaHistoryLocalization

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace RHTower

noncomputable def logMobiusQuadraticResidueAction (N D : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 D, (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
    quadraticResiduePrefix N d

private theorem squareResidue_first_moment_eq (f : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Icc 1 N, f d * ((d : ℝ) - 1)) =
      (N : ℝ) * (∑ d ∈ Icc 1 N, f d) - ∑ k ∈ Icc 1 N, ∑ d ∈ Icc 1 k, f d := by
  have hsucc (n : ℕ) (g : ℕ → ℝ) :
      (∑ k ∈ Icc 1 (n + 1), g k) = (∑ k ∈ Icc 1 n, g k) + g (n + 1) := by
    have he : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext k
      simp only [mem_Icc, mem_insert]
      omega
    rw [he, sum_insert (by simp)]
    ring
  induction N with
  | zero => simp
  | succ N ih =>
    rw [hsucc, hsucc, hsucc, hsucc]
    push_cast
    linear_combination ih

theorem abs_logMobiusQuadraticResidueMean_le {S : ℝ}
    (hS : ∀ M : ℕ,
      |∑ d ∈ Icc 1 M, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d| ≤ S)
    (N : ℕ) :
    |(N : ℝ) / 2 * ∑ d ∈ Icc 1 N,
      (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d) * (1 - 1 / (d : ℝ))| ≤
      S * (N : ℝ) ^ 2 := by
  let f : ℕ → ℝ := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d
  have hW : |∑ d ∈ Icc 1 N, f d * ((d : ℝ) - 1)| ≤ 2 * (N : ℝ) * S := by
    rw [squareResidue_first_moment_eq, sub_eq_add_neg]
    calc
      _ ≤ |(N : ℝ) * (∑ d ∈ Icc 1 N, f d)| +
          |-(∑ k ∈ Icc 1 N, ∑ d ∈ Icc 1 k, f d)| := abs_add_le _ _
      _ = (N : ℝ) * |∑ d ∈ Icc 1 N, f d| +
          |∑ k ∈ Icc 1 N, ∑ d ∈ Icc 1 k, f d| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N), abs_neg]
      _ ≤ (N : ℝ) * S + ∑ k ∈ Icc 1 N, |∑ d ∈ Icc 1 k, f d| :=
        add_le_add (mul_le_mul_of_nonneg_left (hS N) (Nat.cast_nonneg N))
          (abs_sum_le_sum_abs _ _)
      _ ≤ (N : ℝ) * S + ∑ _k ∈ Icc 1 N, S :=
        add_le_add le_rfl (sum_le_sum fun k _ => hS k)
      _ = _ := by simp; ring
  have hw : (∑ d ∈ Icc 1 N,
      (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d) * (1 - 1 / (d : ℝ))) =
      ∑ d ∈ Icc 1 N, f d * ((d : ℝ) - 1) := by
    apply sum_congr rfl
    intro d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    dsimp [f]
    field_simp [ne_of_gt hdR]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N / 2), hw]
  calc
    _ ≤ (N : ℝ) / 2 * (2 * (N : ℝ) * S) := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = _ := by ring

theorem exists_abs_logMobiusQuadraticResidueAction_self_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |logMobiusQuadraticResidueAction N N| ≤ C * (N : ℝ) ^ 2 := by
  obtain ⟨S, hS0, hS⟩ := exists_abs_sum_moebius_log_div_le
  refine ⟨S + 16384, by positivity, ?_⟩
  intro N
  rw [logMobiusQuadraticResidueAction, logMobiusQuadraticResidueAction_eq_mean_add_centered]
  calc
    _ ≤ |(N : ℝ) / 2 * ∑ d ∈ Icc 1 N,
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d) * (1 - 1 / (d : ℝ))| +
        |logMobiusCenteredQuadraticResidueAction N N| := abs_add_le _ _
    _ ≤ S * (N : ℝ) ^ 2 + 16384 * (N : ℝ) ^ 2 :=
      add_le_add (abs_logMobiusQuadraticResidueMean_le hS N)
        (abs_logMobiusCenteredQuadraticResidueAction_self_le N)
    _ = _ := by ring

noncomputable def mobiusLargeModulusSquareResidueSource (N : ℕ) : ℝ :=
  logMobiusQuadraticResidueAction N (N ^ 2) - logMobiusQuadraticResidueAction N N -
    (1 + ∑ d ∈ Icc 1 (N ^ 2),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
      ∑ s ∈ range N, (s : ℝ) ^ 2

theorem mobiusLargeModulusSquareResidueSource_eq_sum_Ioc (N : ℕ) :
    mobiusLargeModulusSquareResidueSource N =
      (∑ d ∈ Ioc N (N ^ 2),
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
          quadraticResiduePrefix N d) -
      (1 + ∑ d ∈ Icc 1 (N ^ 2),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
        ∑ s ∈ range N, (s : ℝ) ^ 2 := by
  have hN : N ≤ N ^ 2 := by
    by_cases hn : N = 0
    · simp [hn]
    · have h1 : 1 ≤ N := by omega
      simpa [pow_two] using Nat.mul_le_mul_left N h1
  have he : Icc 1 N ∪ Ioc N (N ^ 2) = Icc 1 (N ^ 2) := by
    ext d
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 N) (Ioc N (N ^ 2)) := by
    apply Finset.disjoint_left.mpr
    intro d h1 h2
    have := mem_Icc.mp h1
    have := mem_Ioc.mp h2
    omega
  have hs : logMobiusQuadraticResidueAction N (N ^ 2) =
      logMobiusQuadraticResidueAction N N +
      ∑ d ∈ Ioc N (N ^ 2),
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
          quadraticResiduePrefix N d := by
    unfold logMobiusQuadraticResidueAction
    rw [← he, sum_union hd]
  unfold mobiusLargeModulusSquareResidueSource
  rw [hs]
  ring

theorem psiRemainder_squareSum_eq_small_add_large {N : ℕ} (hN : 1 ≤ N) :
    (∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) =
      logMobiusQuadraticResidueAction N N + mobiusLargeModulusSquareResidueSource N := by
  rw [psiRemainder_squareSum_eq_quadraticResidues hN]
  unfold mobiusLargeModulusSquareResidueSource logMobiusQuadraticResidueAction
  ring

theorem riemannHypothesis_iff_mobiusLargeModulusSquareResidueSource_boundedAbove :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      mobiusLargeModulusSquareResidueSource N ≤ B * (N : ℝ) ^ 2 := by
  rw [GaloisForLFunctions.RHTower.riemannHypothesis_iff_psiRemainder_squareSum_boundedAbove]
  obtain ⟨C, _, hC⟩ := exists_abs_logMobiusQuadraticResidueAction_self_le
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + C, ?_⟩
    intro N hN
    have hb := hB N hN
    have hc := (abs_le.mp (hC N)).1
    have he := psiRemainder_squareSum_eq_small_add_large (N := N) (by omega)
    nlinarith only [hb, hc, he]
  · rintro ⟨B, hB⟩
    refine ⟨B + C, ?_⟩
    intro N hN
    have hb := hB N hN
    have hc := (abs_le.mp (hC N)).2
    have he := psiRemainder_squareSum_eq_small_add_large (N := N) (by omega)
    nlinarith only [hb, hc, he]

/-- Residual source after retaining the explicit mean and removing a centered cutoff. -/
noncomputable def mobiusCenteredCutoffSquareResidueSource (N D : ℕ) : ℝ :=
  logMobiusQuadraticResidueAction N (N ^ 2) - logMobiusQuadraticResidueAction N D +
    (N : ℝ) / 2 * ∑ d ∈ Icc 1 D,
      (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d) * (1 - 1 / (d : ℝ)) -
    (1 + ∑ d ∈ Icc 1 (N ^ 2),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
      ∑ s ∈ range N, (s : ℝ) ^ 2

/-- For an actual interval cutoff, the residual consists of its tail, mean, and counterterm. -/
theorem mobiusCenteredCutoffSquareResidueSource_eq_sum_Ioc {N D : ℕ} (hD : D ≤ N ^ 2) :
    mobiusCenteredCutoffSquareResidueSource N D =
      (∑ d ∈ Ioc D (N ^ 2),
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
          quadraticResiduePrefix N d) +
      (N : ℝ) / 2 * ∑ d ∈ Icc 1 D,
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d) * (1 - 1 / (d : ℝ)) -
      (1 + ∑ d ∈ Icc 1 (N ^ 2),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
        ∑ s ∈ range N, (s : ℝ) ^ 2 := by
  have he : Icc 1 D ∪ Ioc D (N ^ 2) = Icc 1 (N ^ 2) := by
    ext d
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 D) (Ioc D (N ^ 2)) := by
    apply Finset.disjoint_left.mpr
    intro d h1 h2
    have := mem_Icc.mp h1
    have := mem_Ioc.mp h2
    omega
  have hs : logMobiusQuadraticResidueAction N (N ^ 2) =
      logMobiusQuadraticResidueAction N D +
      ∑ d ∈ Ioc D (N ^ 2),
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
          quadraticResiduePrefix N d := by
    unfold logMobiusQuadraticResidueAction
    rw [← he, sum_union hd]
  unfold mobiusCenteredCutoffSquareResidueSource
  rw [hs]
  ring

theorem psiRemainder_squareSum_eq_centered_add_cutoffSource
    {N : ℕ} (hN : 1 ≤ N) (D : ℕ) :
    (∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) =
      logMobiusCenteredQuadraticResidueAction N D +
        mobiusCenteredCutoffSquareResidueSource N D := by
  have hmean := logMobiusQuadraticResidueAction_eq_mean_add_centered N D
  change logMobiusQuadraticResidueAction N D = _ at hmean
  rw [psiRemainder_squareSum_eq_quadraticResidues hN]
  change logMobiusQuadraticResidueAction N (N ^ 2) - _ = _
  unfold mobiusCenteredCutoffSquareResidueSource
  rw [hmean]
  ring

/-- Superlinear centered cutoffs leave an exact one-sided RH criterion; their mean is retained. -/
theorem riemannHypothesis_iff_mobiusCenteredCutoffSquareResidueSource_boundedAbove
    {ε : ℝ} (hε : 0 < ε) (D : ℕ → ℕ)
    (hD : ∀ N : ℕ, 2 ≤ N → 1 ≤ D N)
    (hND : ∀ N : ℕ, 2 ≤ N → N ≤ D N)
    (hcritical : ∀ N : ℕ, 2 ≤ N → (D N : ℝ) ^ (3 / 2 + ε) ≤ (N : ℝ) ^ 2) :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      mobiusCenteredCutoffSquareResidueSource N (D N) ≤ B * (N : ℝ) ^ 2 := by
  rw [GaloisForLFunctions.RHTower.riemannHypothesis_iff_psiRemainder_squareSum_boundedAbove]
  have hc (N : ℕ) (hN : 2 ≤ N) :=
    abs_logMobiusCenteredQuadraticResidueAction_le_superlinear_aperture
      hε (hD N hN) (hND N hN) (hcritical N hN)
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + 4 * (1 + 4 / ε) ^ 4, ?_⟩
    intro N hN
    have hb := hB N hN
    have hl := (abs_le.mp (hc N hN)).1
    have he := psiRemainder_squareSum_eq_centered_add_cutoffSource (N := N) (by omega) (D N)
    nlinarith only [hb, hl, he]
  · rintro ⟨B, hB⟩
    refine ⟨B + 4 * (1 + 4 / ε) ^ 4, ?_⟩
    intro N hN
    have hb := hB N hN
    have hu := (abs_le.mp (hc N hN)).2
    have he := psiRemainder_squareSum_eq_centered_add_cutoffSource (N := N) (by omega) (D N)
    nlinarith only [hb, hu, he]

end RHTower
