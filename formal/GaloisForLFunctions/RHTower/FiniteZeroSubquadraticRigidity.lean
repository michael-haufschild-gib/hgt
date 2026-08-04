import GaloisForLFunctions.RHTower.Peeling
import GaloisForLFunctions.HTGeometry.EntireLogarithm

/-!
# Finite-zero subquadratic rigidity

An entire function of order strictly below two with only finitely many zeros is a finite divisor
polynomial times one exponential character.  This is the finite-divisor form of Hadamard rigidity,
proved here from the project's global peeling theorem and entire-logarithm theorem.

The proof includes the missing growth-transfer step.  Outside one ball every peeled linear factor
has norm at least one, so the zero-free cofactor inherits the original envelope.  On the ball,
compactness supplies one bound, absorbed into the same subquadratic envelope.  No Hadamard
factorization axiom or external entire-function classification is assumed.
-/

noncomputable section

open Complex Metric Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The finite divisor factor attached to a multiplicity function. -/
def finiteDivisorFactor (t : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) : ℂ :=
  ∏ w ∈ t, (z - w) ^ m w

/-- Outside the radius `1 + sum ‖w‖`, every finite divisor factor has norm at least one. -/
theorem one_le_norm_finiteDivisorFactor_of_far
    (t : Finset ℂ) (m : ℂ → ℕ) {z : ℂ}
    (hz : 1 + ∑ w ∈ t, ‖w‖ ≤ ‖z‖) :
    1 ≤ ‖finiteDivisorFactor t m z‖ := by
  classical
  rw [finiteDivisorFactor, norm_prod]
  apply Finset.one_le_prod
  intro w hw
  rw [norm_pow]
  apply one_le_pow₀
  have hwSum : ‖w‖ ≤ ∑ u ∈ t, ‖u‖ := by
    exact Finset.single_le_sum (fun u _ => norm_nonneg u) hw
  have hsub : 1 ≤ ‖z‖ - ‖w‖ := by linarith
  exact hsub.trans (norm_sub_norm_le z w)

/-- **Finite-zero subquadratic Hadamard rigidity.**

If an entire function has a subquadratic exponential envelope and a finite zero set, then it is
exactly a finite divisor factor times a nonzero constant and one exponential character. -/
theorem exists_finiteDivisorFactor_mul_exp_of_finite_zeroSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C a : ℝ} (ha0 : 0 ≤ a) (ha2 : a < 2) (hC : 0 ≤ C)
    (hgrow : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ a))
    (hfinite : {z : ℂ | f z = 0}.Finite) :
    ∃ (t : Finset ℂ) (m : ℂ → ℕ) (c B : ℂ), c ≠ 0 ∧
      (∀ z, f z = finiteDivisorFactor t m z * c * Complex.exp (B * z)) ∧
      (∀ z, f z = 0 ↔ z ∈ t) := by
  classical
  let t : Finset ℂ := hfinite.toFinset
  let S : ℝ := ∑ w ∈ t, ‖w‖
  let R : ℝ := 1 + S
  have hS0 : 0 ≤ S := by
    dsimp [S]
    positivity
  have hR0 : 0 ≤ R := by dsimp [R]; linarith
  have htZeros (z : ℂ) : z ∈ t ↔ f z = 0 := by
    simp only [t, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hzAnchorNotMem : ((R : ℝ) : ℂ) ∉ t := by
    intro hz
    have hzSum : ‖((R : ℝ) : ℂ)‖ ≤ S := by
      have := Finset.single_le_sum (fun w _ => norm_nonneg w) hz
      simpa only [S] using this
    have hnormR : ‖((R : ℝ) : ℂ)‖ = R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0]
    rw [hnormR] at hzSum
    dsimp [R] at hzSum
    linarith
  have hfAnchor : f ((R : ℝ) : ℂ) ≠ 0 := by
    intro hz
    exact hzAnchorNotMem ((htZeros _).mpr hz)
  have hfA : AnalyticOnNhd ℂ f Set.univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hord : ∀ w ∈ t, analyticOrderAt f w ≠ ⊤ := by
    intro w hw htop
    have hev : f =ᶠ[nhds w] 0 := analyticOrderAt_eq_top.mp htop
    have hall := hfA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ w) hev (Set.mem_univ ((R : ℝ) : ℂ))
    exact hfAnchor hall
  obtain ⟨m, h, hhA, hh0, hfactor⟩ :=
    exists_multi_peel isOpen_univ hfA t (fun _ _ => Set.mem_univ _)
      (fun z _ hz => (htZeros z).mpr hz) hord
  have hhDiff : Differentiable ℂ h := fun z => (hhA z (Set.mem_univ z)).differentiableAt
  have hbdd : BddAbove ((fun z : ℂ => ‖h z‖) '' Metric.closedBall 0 R) :=
    (isCompact_closedBall (0 : ℂ) R).bddAbove_image hhDiff.continuous.norm.continuousOn
  let K : ℝ := max 1 (sSup ((fun z : ℂ => ‖h z‖) '' Metric.closedBall 0 R))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hinside {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) : ‖h z‖ ≤ K := by
    exact (le_csSup hbdd (mem_image_of_mem (fun w : ℂ => ‖h w‖) hz)).trans
      (le_max_right _ _)
  have houtside {z : ℂ} (hz : z ∉ Metric.closedBall (0 : ℂ) R) :
      ‖h z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ a) := by
    have hzFar : R ≤ ‖z‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using le_of_lt
        (show R < ‖z‖ by
          simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz)
    have hP : 1 ≤ ‖finiteDivisorFactor t m z‖ := by
      apply one_le_norm_finiteDivisorFactor_of_far
      simpa only [R, S] using hzFar
    have hfactNorm : ‖f z‖ = ‖finiteDivisorFactor t m z‖ * ‖h z‖ := by
      rw [hfactor z (Set.mem_univ z), norm_mul]
      rfl
    have hhf : ‖h z‖ ≤ ‖f z‖ := by
      rw [hfactNorm]
      nlinarith [norm_nonneg (h z)]
    exact hhf.trans (hgrow z)
  let C' : ℝ := C + Real.log K
  have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hC'0 : 0 ≤ C' := by dsimp [C']; linarith
  have hhGrow : ∀ z, ‖h z‖ ≤ Real.exp (C' * (1 + ‖z‖) ^ a) := by
    intro z
    have hpow1 : 1 ≤ (1 + ‖z‖) ^ a :=
      Real.one_le_rpow (by linarith [norm_nonneg z]) ha0
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R
    · calc
        ‖h z‖ ≤ K := hinside hz
        _ = Real.exp (Real.log K) := (Real.exp_log hKpos).symm
        _ ≤ Real.exp (C' * (1 + ‖z‖) ^ a) := by
          rw [Real.exp_le_exp]
          dsimp [C']
          nlinarith [hC, hlogK0]
    · refine (houtside hz).trans ?_
      rw [Real.exp_le_exp]
      dsimp [C']
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  obtain ⟨B, hB⟩ := exists_linear_of_ne_zero_of_growth
    hhDiff (fun z => hh0 z (Set.mem_univ z)) ha0 ha2 hC'0 hhGrow
  refine ⟨t, m, h 0, B, hh0 0 (Set.mem_univ 0), ?_, ?_⟩
  · intro z
    rw [hfactor z (Set.mem_univ z), finiteDivisorFactor, hB z]
    ring
  · intro z
    exact (htZeros z).symm

/-- **Superlinear-ray infinitude law.**  A subquadratic entire function whose logarithmic norm
beats every linear slope on the positive real ray has infinitely many distinct zeros.

The earlier one-zero theorem follows from the same hypotheses.  The stronger conclusion uses the
finite-zero normal form above: a finite divisor contributes only polynomial growth and its
zero-free cofactor contributes only one exponential character, so their product cannot beat every
linear slope. -/
theorem zeroSet_infinite_of_subquadratic_superlinear_ray
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C a : ℝ} (ha0 : 0 ≤ a) (ha2 : a < 2) (hC : 0 ≤ C)
    (hgrow : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ a))
    (hsuper : ∀ A : ℝ, ∃ sigma : ℝ, 1 ≤ sigma ∧
      A * sigma < Real.log ‖f (sigma : ℂ)‖) :
    {z : ℂ | f z = 0}.Infinite := by
  classical
  intro hfinite
  obtain ⟨t, m, c, B, hc, hform, _⟩ :=
    exists_finiteDivisorFactor_mul_exp_of_finite_zeroSet
      hf ha0 ha2 hC hgrow hfinite
  let S : ℝ := ∑ w ∈ t, ‖w‖
  let M : ℕ := ∑ w ∈ t, m w
  let K : ℝ := ‖c‖ * (1 + S) ^ M
  have hS0 : 0 ≤ S := by
    dsimp [S]
    positivity
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (norm_pos_iff.mpr hc) (pow_pos (by linarith) M)
  let A : ℝ := (M : ℝ) + |B.re| + |Real.log K| + 1
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  obtain ⟨sigma, hsigma1, hsigmaSuper⟩ := hsuper A
  have hsigma0 : 0 ≤ sigma := zero_le_one.trans hsigma1
  have hnormPos : 0 < ‖f (sigma : ℂ)‖ := by
    by_contra hnot
    have hzero : ‖f (sigma : ℂ)‖ = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
    rw [hzero, Real.log_zero] at hsigmaSuper
    nlinarith
  have hrootBound (w : ℂ) (hw : w ∈ t) :
      ‖(sigma : ℂ) - w‖ ≤ sigma * (1 + S) := by
    have hwS : ‖w‖ ≤ S := by
      exact Finset.single_le_sum (fun u _ => norm_nonneg u) hw
    calc
      ‖(sigma : ℂ) - w‖ ≤ ‖(sigma : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ sigma + S := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsigma0]
        linarith
      _ ≤ sigma * (1 + S) := by nlinarith
  have hfactorBound :
      ‖finiteDivisorFactor t m (sigma : ℂ)‖ ≤
        (sigma * (1 + S)) ^ M := by
    rw [finiteDivisorFactor, norm_prod]
    calc
      ∏ w ∈ t, ‖((sigma : ℂ) - w) ^ m w‖ =
          ∏ w ∈ t, ‖(sigma : ℂ) - w‖ ^ m w := by
            apply Finset.prod_congr rfl
            intro w hw
            rw [norm_pow]
      _ ≤ ∏ w ∈ t, (sigma * (1 + S)) ^ m w := by
            apply Finset.prod_le_prod
            · intro w hw
              positivity
            · intro w hw
              exact pow_le_pow_left₀ (norm_nonneg _) (hrootBound w hw) _
      _ = (sigma * (1 + S)) ^ M := by
            exact Finset.prod_pow_eq_pow_sum t m (sigma * (1 + S))
  have hsigmaExp : sigma ≤ Real.exp sigma := by
    exact le_trans (by linarith) (Real.add_one_le_exp sigma)
  have hsigmaPow : sigma ^ M ≤ Real.exp ((M : ℝ) * sigma) := by
    calc
      sigma ^ M ≤ (Real.exp sigma) ^ M := pow_le_pow_left₀ hsigma0 hsigmaExp M
      _ = Real.exp ((M : ℝ) * sigma) := (Real.exp_nat_mul sigma M).symm
  have hformNorm :
      ‖f (sigma : ℂ)‖ =
        ‖finiteDivisorFactor t m (sigma : ℂ)‖ * ‖c‖ *
          Real.exp (B.re * sigma) := by
    rw [hform, norm_mul, norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  have hfactorExp :
      ‖finiteDivisorFactor t m (sigma : ℂ)‖ ≤
        Real.exp ((M : ℝ) * sigma) * (1 + S) ^ M := by
    calc
      ‖finiteDivisorFactor t m (sigma : ℂ)‖
          ≤ (sigma * (1 + S)) ^ M := hfactorBound
      _ = sigma ^ M * (1 + S) ^ M := by rw [mul_pow]
      _ ≤ Real.exp ((M : ℝ) * sigma) * (1 + S) ^ M := by
        exact mul_le_mul_of_nonneg_right hsigmaPow (pow_nonneg (by linarith) M)
  have hfK :
      ‖f (sigma : ℂ)‖ ≤ K * Real.exp (((M : ℝ) + B.re) * sigma) := by
    rw [hformNorm]
    calc
      ‖finiteDivisorFactor t m (sigma : ℂ)‖ * ‖c‖ * Real.exp (B.re * sigma)
          ≤ (Real.exp ((M : ℝ) * sigma) * (1 + S) ^ M) * ‖c‖ *
              Real.exp (B.re * sigma) := by
            gcongr
      _ = K * Real.exp (((M : ℝ) + B.re) * sigma) := by
            dsimp [K]
            rw [show ((M : ℝ) + B.re) * sigma =
              (M : ℝ) * sigma + B.re * sigma by ring, Real.exp_add]
            ring
  have hKexp : K ≤ Real.exp ((|Real.log K| + 1) * sigma) := by
    calc
      K = Real.exp (Real.log K) := (Real.exp_log hKpos).symm
      _ ≤ Real.exp ((|Real.log K| + 1) * sigma) := by
        rw [Real.exp_le_exp]
        have hlogle : Real.log K ≤ |Real.log K| := le_abs_self _
        nlinarith [abs_nonneg (Real.log K)]
  have hfUpper : ‖f (sigma : ℂ)‖ ≤ Real.exp (A * sigma) := by
    calc
      ‖f (sigma : ℂ)‖ ≤ K * Real.exp (((M : ℝ) + B.re) * sigma) := hfK
      _ ≤ Real.exp ((|Real.log K| + 1) * sigma) *
            Real.exp (((M : ℝ) + B.re) * sigma) := by
          exact mul_le_mul_of_nonneg_right hKexp (Real.exp_pos _).le
      _ = Real.exp (((M : ℝ) + B.re + |Real.log K| + 1) * sigma) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (A * sigma) := by
          rw [Real.exp_le_exp]
          dsimp [A]
          have hBre : B.re ≤ |B.re| := le_abs_self _
          nlinarith
  have hlower : Real.exp (A * sigma) < ‖f (sigma : ℂ)‖ :=
    (Real.lt_log_iff_exp_lt hnormPos).mp hsigmaSuper
  exact (not_lt_of_ge hfUpper) hlower

end RHTower
