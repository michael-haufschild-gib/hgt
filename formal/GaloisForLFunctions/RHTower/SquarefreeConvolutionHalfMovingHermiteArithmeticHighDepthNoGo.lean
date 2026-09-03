import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteHighDepthNoGo
import GaloisForLFunctions.HTGeometry.ExponentialSumDA

/-!
# Arithmetic mode tails sharpen the high Hermite-depth obstruction

The Cauchy remainder treats the dressed Dirichlet polynomial as an arbitrary entire function and
only excludes depths eventually above `N/2`.  Its arithmetic exponential-mode decomposition is
sharper.  At `s=1101/1100`, undoing the dress turns every Taylor remainder into a Poisson upper
tail with action

`((N : ℝ) - log n) * 501/1100`.

An exponential tilt at `t=1/75`, together with `exp(1/75) ≤ 75/74`, gives the common bound

`N * exp(-29N/2442000)`

whenever `K ≥ 37N/80`.  Hence every such schedule cancels the nonzero Euler source and violates
counterterm admissibility.  The canonical point-Hermite class is now confined between the
low-depth obstruction `K ≤ N/15` and this source-fidelity obstruction.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

def boundaryDressedModeFrequency (N n : ℕ) : ℂ :=
  (N : ℂ) - (Real.log n : ℂ)

def boundaryDressedModeCoefficient (N n : ℕ) : ℂ :=
  squarefreeConvolutionHalf n *
    Complex.exp (-(N : ℂ) * boundaryExteriorPoint)

theorem boundaryPositiveExponentialDress_eq_modeSum (N : ℕ) (s : ℂ) :
    boundaryPositiveExponentialDress N s =
      ∑ n ∈ Finset.range N,
        boundaryDressedModeCoefficient N n *
          Complex.exp (boundaryDressedModeFrequency N n * s) := by
  rw [boundaryPositiveExponentialDress, boundaryPositiveExponentialSeparator,
    squarefreeHalfDirichletPartialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [boundaryDressedModeCoefficient]
  · rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, ← Complex.cpow_neg]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hpow : ((n : ℂ) ^ (-(s : ℂ))) =
        Complex.exp (-((Real.log n : ℝ) : ℂ) * s) := by
      have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
      rw [Complex.cpow_def_of_ne_zero hne]
      congr 1
      rw [← Complex.natCast_log]
      ring
    rw [hpow, boundaryDressedModeCoefficient, boundaryDressedModeFrequency]
    calc
      Complex.exp ((N : ℂ) * (s - boundaryExteriorPoint)) *
          (squarefreeConvolutionHalf n *
            Complex.exp (-((Real.log n : ℝ) : ℂ) * s)) =
        squarefreeConvolutionHalf n *
          (Complex.exp ((N : ℂ) * (s - boundaryExteriorPoint)) *
            Complex.exp (-((Real.log n : ℝ) : ℂ) * s)) := by ring
      _ = squarefreeConvolutionHalf n *
          Complex.exp ((N : ℂ) * (s - boundaryExteriorPoint) -
            ((Real.log n : ℝ) : ℂ) * s) := by
        rw [← Complex.exp_add]
        congr 2
        ring
      _ = squarefreeConvolutionHalf n *
          Complex.exp (-(N : ℂ) * boundaryExteriorPoint +
            (((N : ℂ) - (Real.log n : ℂ)) * s)) := by
        congr 2
        ring
      _ = squarefreeConvolutionHalf n *
          Complex.exp (-(N : ℂ) * boundaryExteriorPoint) *
            Complex.exp (((N : ℂ) - (Real.log n : ℂ)) * s) := by
        rw [Complex.exp_add]
        ring

/-- Exponential tilting bound for the upper tail of the real exponential series. -/
theorem real_exp_neg_mul_tail_le_chernoff
    (M : ℕ) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    Real.exp (-x) *
        (Real.exp x - ∑ j ∈ Finset.range M, x ^ j / j.factorial) ≤
      Real.exp (-(t * (M : ℝ)) + x * (Real.exp t - 1)) := by
  let f : ℕ → ℝ := fun j => x ^ j / j.factorial
  let g : ℕ → ℝ := fun j => (x * Real.exp t) ^ j / j.factorial
  have hsf : Summable f := by
    simpa only [f] using Real.summable_pow_div_factorial x
  have hsg : Summable g := by
    simpa only [g] using Real.summable_pow_div_factorial (x * Real.exp t)
  have hsumf : (∑' j : ℕ, f j) = Real.exp x := by
    simpa only [f, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq
  have hsumg : (∑' j : ℕ, g j) = Real.exp (x * Real.exp t) := by
    simpa only [g, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (x * Real.exp t)).tsum_eq
  have htail :
      Real.exp x - ∑ j ∈ Finset.range M, x ^ j / j.factorial =
        ∑' k : ℕ, f (k + M) := by
    have hsplit := hsf.sum_add_tsum_nat_add M
    rw [← hsumf]
    simp only [f] at hsplit ⊢
    linarith
  have hscale (k : ℕ) :
      (1 : ℝ) ≤ Real.exp (-(t * (M : ℝ))) * (Real.exp t) ^ (k + M) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hk : (0 : ℝ) ≤ k := by positivity
    push_cast
    nlinarith
  have hterm (k : ℕ) :
      f (k + M) ≤ Real.exp (-(t * (M : ℝ))) * g (k + M) := by
    have hnonneg : 0 ≤ f (k + M) := by
      unfold f
      positivity
    calc
      f (k + M) = f (k + M) * 1 := by ring
      _ ≤ f (k + M) *
          (Real.exp (-(t * (M : ℝ))) * (Real.exp t) ^ (k + M)) :=
        mul_le_mul_of_nonneg_left (hscale k) hnonneg
      _ = Real.exp (-(t * (M : ℝ))) * g (k + M) := by
        unfold f g
        rw [mul_pow]
        ring
  have htailg : (∑' k : ℕ, g (k + M)) ≤ Real.exp (x * Real.exp t) := by
    have hsplit := hsg.sum_add_tsum_nat_add M
    rw [← hsumg]
    have hprefix : 0 ≤ ∑ j ∈ Finset.range M, g j := by
      exact Finset.sum_nonneg fun j _ => by
        unfold g
        positivity
    linarith
  rw [htail]
  calc
    Real.exp (-x) * (∑' k : ℕ, f (k + M)) ≤
        Real.exp (-x) *
          (∑' k : ℕ, Real.exp (-(t * (M : ℝ))) * g (k + M)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact ((summable_nat_add_iff M).2 hsf).tsum_le_tsum hterm
        (((summable_nat_add_iff M).2 hsg).mul_left _)
    _ = Real.exp (-x) *
        (Real.exp (-(t * (M : ℝ))) * (∑' k : ℕ, g (k + M))) := by
      rw [tsum_mul_left]
    _ ≤ Real.exp (-x) *
        (Real.exp (-(t * (M : ℝ))) * Real.exp (x * Real.exp t)) := by
      gcongr
    _ = Real.exp (-(t * (M : ℝ)) + x * (Real.exp t - 1)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem boundaryHermiteJetPolynomial_eq_modeTaylorSum (N K : ℕ) (s : ℂ) :
    boundaryHermiteJetPolynomial N K s =
      ∑ n ∈ Finset.range N,
        boundaryDressedModeCoefficient N n *
          Complex.exp
            (boundaryDressedModeFrequency N n * boundaryExteriorPoint) *
          (∑ j ∈ Finset.range (K + 1),
            (boundaryDressedModeFrequency N n *
                (s - boundaryExteriorPoint)) ^ j /
              (j.factorial : ℂ)) := by
  have hfun : boundaryPositiveExponentialDress N = fun z : ℂ =>
      ∑ n ∈ Finset.range N,
        boundaryDressedModeCoefficient N n *
          Complex.exp (boundaryDressedModeFrequency N n * z) := by
    funext z
    exact boundaryPositiveExponentialDress_eq_modeSum N z
  rw [boundaryHermiteJetPolynomial]
  simp_rw [hfun, GaloisForLFunctions.iteratedDeriv_finset_expSum]
  simp_rw [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow]
  ring

def boundaryDressedModeAction (N n : ℕ) : ℝ :=
  ((N : ℝ) - Real.log n) * (501 / 1100 : ℝ)

private theorem hermiteEulerCancellationPoint_sub_boundaryExteriorPoint :
    hermiteEulerCancellationPoint - boundaryExteriorPoint = (501 / 1100 : ℂ) := by
  norm_num [hermiteEulerCancellationPoint, boundaryExteriorPoint]

theorem boundaryDressedModeFrequency_mul_eulerGap (N n : ℕ) :
    boundaryDressedModeFrequency N n *
        (hermiteEulerCancellationPoint - boundaryExteriorPoint) =
      (boundaryDressedModeAction N n : ℂ) := by
  rw [hermiteEulerCancellationPoint_sub_boundaryExteriorPoint]
  simp only [boundaryDressedModeFrequency, boundaryDressedModeAction]
  push_cast
  ring

theorem boundarySeparator_mul_dressedMode_at_boundary_eq
    (N : ℕ) {n : ℕ} (hn : n ≠ 0) :
    boundaryExponentialSeparator N hermiteEulerCancellationPoint *
        (boundaryDressedModeCoefficient N n *
          Complex.exp
            (boundaryDressedModeFrequency N n * boundaryExteriorPoint)) =
      LSeries.term squarefreeConvolutionHalf hermiteEulerCancellationPoint n *
        Complex.exp (-(boundaryDressedModeAction N n : ℂ)) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : ((n : ℂ) ^ (-hermiteEulerCancellationPoint)) =
      Complex.exp
        (-((Real.log n : ℝ) : ℂ) * hermiteEulerCancellationPoint) := by
    have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_def_of_ne_zero hne]
    congr 1
    rw [← Complex.natCast_log]
    ring
  rw [hpow, boundaryExponentialSeparator, boundaryDressedModeCoefficient,
    boundaryDressedModeFrequency]
  calc
    Complex.exp ((N : ℂ) *
          (boundaryExteriorPoint - hermiteEulerCancellationPoint)) *
        (squarefreeConvolutionHalf n *
          Complex.exp (-(N : ℂ) * boundaryExteriorPoint) *
          Complex.exp (((N : ℂ) - (Real.log n : ℂ)) *
            boundaryExteriorPoint)) =
      squarefreeConvolutionHalf n *
        Complex.exp
          ((N : ℂ) * (boundaryExteriorPoint - hermiteEulerCancellationPoint) +
            (-(N : ℂ) * boundaryExteriorPoint +
              ((N : ℂ) - (Real.log n : ℂ)) * boundaryExteriorPoint)) := by
        rw [Complex.exp_add, Complex.exp_add]
        ring
    _ = squarefreeConvolutionHalf n *
        Complex.exp
          (-((Real.log n : ℝ) : ℂ) * hermiteEulerCancellationPoint +
            -(boundaryDressedModeAction N n : ℂ)) := by
      congr 2
      rw [boundaryDressedModeAction]
      push_cast
      norm_num [hermiteEulerCancellationPoint, boundaryExteriorPoint]
      ring
    _ = squarefreeConvolutionHalf n *
        Complex.exp (-((Real.log n : ℝ) : ℂ) *
          hermiteEulerCancellationPoint) *
        Complex.exp (-(boundaryDressedModeAction N n : ℂ)) := by
      rw [Complex.exp_add]
      ring

theorem boundaryHermiteJet_correctedSource_euler_eq_modeSum (N K : ℕ) :
    squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
        boundaryHermiteJetCounterterm N K hermiteEulerCancellationPoint =
      ∑ n ∈ Finset.range N,
        LSeries.term squarefreeConvolutionHalf hermiteEulerCancellationPoint n *
          ((1 : ℂ) - Complex.exp (-(boundaryDressedModeAction N n : ℂ)) *
            (∑ j ∈ Finset.range (K + 1),
              (boundaryDressedModeAction N n : ℂ) ^ j /
                (j.factorial : ℂ))) := by
  rw [boundaryHermiteJetCounterterm,
    boundaryHermiteJetPolynomial_eq_modeTaylorSum,
    squarefreeHalfDirichletPartialSum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hnrange
  by_cases hn0 : n = 0
  · subst n
    simp [LSeries.term_zero, boundaryDressedModeCoefficient]
  · rw [boundaryDressedModeFrequency_mul_eulerGap]
    rw [show -boundaryExponentialSeparator N hermiteEulerCancellationPoint *
          (boundaryDressedModeCoefficient N n *
            Complex.exp
              (boundaryDressedModeFrequency N n * boundaryExteriorPoint) *
            (∑ j ∈ Finset.range (K + 1),
              (boundaryDressedModeAction N n : ℂ) ^ j /
                (j.factorial : ℂ))) =
        -(boundaryExponentialSeparator N hermiteEulerCancellationPoint *
          (boundaryDressedModeCoefficient N n *
            Complex.exp
              (boundaryDressedModeFrequency N n * boundaryExteriorPoint))) *
          (∑ j ∈ Finset.range (K + 1),
            (boundaryDressedModeAction N n : ℂ) ^ j /
              (j.factorial : ℂ)) by ring,
      boundarySeparator_mul_dressedMode_at_boundary_eq N hn0]
    ring

def realPoissonUpperTail (M : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) *
    (Real.exp x - ∑ j ∈ Finset.range M, x ^ j / j.factorial)

theorem complex_poissonUpperTail_eq_ofReal (M : ℕ) (x : ℝ) :
    (1 : ℂ) - Complex.exp (-(x : ℂ)) *
        (∑ j ∈ Finset.range M, (x : ℂ) ^ j / (j.factorial : ℂ)) =
      (realPoissonUpperTail M x : ℂ) := by
  have hsum :
      (∑ j ∈ Finset.range M, (x : ℂ) ^ j / (j.factorial : ℂ)) =
        ((∑ j ∈ Finset.range M, x ^ j / (j.factorial : ℝ)) : ℂ) := by
    push_cast
    rfl
  rw [hsum, show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_exp]
  norm_cast
  unfold realPoissonUpperTail
  rw [show Real.exp (-x) *
      (Real.exp x - ∑ j ∈ Finset.range M, x ^ j / (j.factorial : ℝ)) =
        1 - Real.exp (-x) *
          (∑ j ∈ Finset.range M, x ^ j / (j.factorial : ℝ)) by
    rw [mul_sub, ← Real.exp_add, show -x + x = 0 by ring, Real.exp_zero]]

theorem realPoissonUpperTail_nonneg (M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ realPoissonUpperTail M x := by
  unfold realPoissonUpperTail
  apply mul_nonneg (Real.exp_pos _).le
  apply sub_nonneg.mpr
  have hs := Real.summable_pow_div_factorial x
  have hsum : (∑' j : ℕ, x ^ j / j.factorial) = Real.exp x := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq
  rw [← hsum]
  exact hs.sum_le_tsum (Finset.range M) (fun j _ => by positivity)

theorem realPoissonUpperTail_le_chernoff
    (M : ℕ) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    realPoissonUpperTail M x ≤
      Real.exp (-(t * (M : ℝ)) + x * (Real.exp t - 1)) := by
  exact real_exp_neg_mul_tail_le_chernoff M hx ht

theorem boundaryDressedModeAction_nonneg
    {N n : ℕ} (hn : n ∈ Finset.range N) :
    0 ≤ boundaryDressedModeAction N n := by
  have hlog : Real.log n ≤ (n : ℝ) :=
    Real.log_le_self (Nat.cast_nonneg n)
  have hnN : (n : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hn)
  unfold boundaryDressedModeAction
  nlinarith

theorem boundaryDressedModeAction_le
    {N n : ℕ} (_hn : n ∈ Finset.range N) :
    boundaryDressedModeAction N n ≤
      (501 / 1100 : ℝ) * (N : ℝ) := by
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  unfold boundaryDressedModeAction
  nlinarith

theorem norm_squarefreeHalf_term_hermiteEulerCancellationPoint_le_one (n : ℕ) :
    ‖LSeries.term squarefreeConvolutionHalf hermiteEulerCancellationPoint n‖ ≤ 1 := by
  by_cases hn0 : n = 0
  · subst n
    simp [LSeries.term_zero]
  · rw [LSeries.norm_term_eq, if_neg hn0]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have hre : 0 ≤ hermiteEulerCancellationPoint.re := by
      norm_num [hermiteEulerCancellationPoint]
    have hden : 1 ≤ (n : ℝ) ^ hermiteEulerCancellationPoint.re :=
      Real.one_le_rpow hn1 hre
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hden)).2
      ((norm_squarefreeConvolutionHalf_le_one n).trans hden)

theorem exp_one_div_seventyfive_le_seventyfive_div_seventyfour :
    Real.exp (1 / 75 : ℝ) ≤ 75 / 74 := by
  have h := real_exp_sub_sum_le_factorial_tail
    (1 / 75 : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h ⊢
  nlinarith [Real.exp_pos (1 / 75 : ℝ)]

theorem norm_boundaryHermiteJet_correctedSource_euler_le_chernoff
    (N K : ℕ) {t q : ℝ} (ht : 0 ≤ t) (_hq : 0 ≤ q)
    (hexpSub : Real.exp t - 1 ≤ q) :
    ‖squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
        boundaryHermiteJetCounterterm N K hermiteEulerCancellationPoint‖ ≤
      (N : ℝ) * Real.exp
        (-(t * ((K + 1 : ℕ) : ℝ)) +
          ((501 / 1100 : ℝ) * (N : ℝ)) * q) := by
  rw [boundaryHermiteJet_correctedSource_euler_eq_modeSum]
  calc
    ‖∑ n ∈ Finset.range N,
        LSeries.term squarefreeConvolutionHalf hermiteEulerCancellationPoint n *
          ((1 : ℂ) - Complex.exp (-(boundaryDressedModeAction N n : ℂ)) *
            (∑ j ∈ Finset.range (K + 1),
              (boundaryDressedModeAction N n : ℂ) ^ j /
                (j.factorial : ℂ)))‖ ≤
      ∑ n ∈ Finset.range N,
        ‖LSeries.term squarefreeConvolutionHalf hermiteEulerCancellationPoint n *
          ((1 : ℂ) - Complex.exp (-(boundaryDressedModeAction N n : ℂ)) *
            (∑ j ∈ Finset.range (K + 1),
              (boundaryDressedModeAction N n : ℂ) ^ j /
                (j.factorial : ℂ)))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N,
        Real.exp
          (-(t * ((K + 1 : ℕ) : ℝ)) +
            ((501 / 1100 : ℝ) * (N : ℝ)) * q) := by
      apply Finset.sum_le_sum
      intro n hn
      have hx0 := boundaryDressedModeAction_nonneg hn
      have hxN := boundaryDressedModeAction_le hn
      have htail := realPoissonUpperTail_le_chernoff
        (K + 1) hx0 ht
      have hexpSub0 : 0 ≤ Real.exp t - 1 := by
        have := Real.one_le_exp ht
        linarith
      have haction : boundaryDressedModeAction N n *
          (Real.exp t - 1) ≤
        ((501 / 1100 : ℝ) * (N : ℝ)) * q := by
        calc
          boundaryDressedModeAction N n *
              (Real.exp t - 1) ≤
            ((501 / 1100 : ℝ) * (N : ℝ)) *
              (Real.exp t - 1) :=
            mul_le_mul_of_nonneg_right hxN hexpSub0
          _ ≤ ((501 / 1100 : ℝ) * (N : ℝ)) * q :=
            mul_le_mul_of_nonneg_left hexpSub (by positivity)
      rw [norm_mul, complex_poissonUpperTail_eq_ofReal,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (realPoissonUpperTail_nonneg (K + 1) hx0)]
      calc
        ‖LSeries.term squarefreeConvolutionHalf hermiteEulerCancellationPoint n‖ *
            realPoissonUpperTail (K + 1) (boundaryDressedModeAction N n) ≤
          1 * realPoissonUpperTail (K + 1) (boundaryDressedModeAction N n) := by
            exact mul_le_mul_of_nonneg_right
              (norm_squarefreeHalf_term_hermiteEulerCancellationPoint_le_one n)
              (realPoissonUpperTail_nonneg (K + 1) hx0)
        _ ≤ Real.exp
            (-(t * ((K + 1 : ℕ) : ℝ)) +
              boundaryDressedModeAction N n *
                (Real.exp t - 1)) := by
          simpa only [one_mul] using htail
        _ ≤ Real.exp
            (-(t * ((K + 1 : ℕ) : ℝ)) +
              ((501 / 1100 : ℝ) * (N : ℝ)) * q) := by
          apply Real.exp_le_exp.mpr
          linarith
    _ = (N : ℝ) * Real.exp
        (-(t * ((K + 1 : ℕ) : ℝ)) +
          ((501 / 1100 : ℝ) * (N : ℝ)) * q) := by simp

theorem norm_boundaryHermiteJet_correctedSource_euler_le_of_thirtyseven_div_eighty
    (N K : ℕ) (hK : (37 / 80 : ℝ) * (N : ℝ) ≤ (K : ℝ)) :
    ‖squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
        boundaryHermiteJetCounterterm N K hermiteEulerCancellationPoint‖ ≤
      (N : ℝ) * Real.exp (-(29 / 2442000 : ℝ) * (N : ℝ)) := by
  have hexpSub : Real.exp (1 / 75 : ℝ) - 1 ≤ 1 / 74 := by
    linarith [exp_one_div_seventyfive_le_seventyfive_div_seventyfour]
  have hbase := norm_boundaryHermiteJet_correctedSource_euler_le_chernoff N K
    (show (0 : ℝ) ≤ 1 / 75 by norm_num)
    (show (0 : ℝ) ≤ 1 / 74 by norm_num) hexpSub
  apply hbase.trans
  gcongr
  have hsucc : (K : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by norm_num
  nlinarith

theorem tendsto_boundaryHermiteJet_correctedSource_euler_of_eventually_thirtyseven_div_eighty_le_depth
    {depth : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop,
      (37 / 80 : ℝ) * (N : ℝ) ≤ (depth N : ℝ)) :
    Tendsto (fun N => squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
        boundaryHermiteJetCounterterm N (depth N) hermiteEulerCancellationPoint)
      atTop (nhds 0) := by
  have hmajor : Tendsto
      (fun N : ℕ => (N : ℝ) *
        Real.exp (-(29 / 2442000 : ℝ) * (N : ℝ)))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1
      (29 / 2442000 : ℝ) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, Real.rpow_one, mul_assoc, mul_left_comm, mul_comm] using h
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hdepth] with N hN
  exact
    norm_boundaryHermiteJet_correctedSource_euler_le_of_thirtyseven_div_eighty
      N (depth N) hN

/-- Arithmetic mode decomposition lowers the source-fidelity obstruction from the Cauchy
threshold `1/2` to `37/80`. -/
theorem not_squarefreeHalfCountertermAdmissible_boundaryHermiteJetCounterterm_of_eventually_thirtyseven_div_eighty_le_depth
    {depth : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop,
      (37 / 80 : ℝ) * (N : ℝ) ≤ (depth N : ℝ)) :
    ¬ SquarefreeHalfCountertermAdmissible
      (fun N => boundaryHermiteJetCounterterm N (depth N)) := by
  intro hadm
  have hcounter : Tendsto
      (fun N => boundaryHermiteJetCounterterm N (depth N)
        hermiteEulerCancellationPoint) atTop (nhds 0) :=
    hadm.2.tendsto_at hermiteEulerCancellationPoint_mem_farHalf
  have hdirichlet : Tendsto
      (fun N => squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint)
      atTop (nhds (LSeries squarefreeConvolutionHalf hermiteEulerCancellationPoint)) := by
    simpa only [squarefreeHalfDirichletPartialSum] using
      tendstoLocallyUniformlyOn_squarefreeConvolutionHalf_partialSums.tendsto_at
        hermiteEulerCancellationPoint_mem_farHalf
  have hsource : Tendsto
      (fun N => squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
        boundaryHermiteJetCounterterm N (depth N) hermiteEulerCancellationPoint)
      atTop (nhds (LSeries squarefreeConvolutionHalf hermiteEulerCancellationPoint)) := by
    simpa using hdirichlet.add hcounter
  have hcancel :=
    tendsto_boundaryHermiteJet_correctedSource_euler_of_eventually_thirtyseven_div_eighty_le_depth
      hdepth
  have hzero : LSeries squarefreeConvolutionHalf hermiteEulerCancellationPoint = 0 :=
    tendsto_nhds_unique hsource hcancel
  have hs : 1 < hermiteEulerCancellationPoint.re := by
    norm_num [hermiteEulerCancellationPoint]
  have h2s : 1 < (2 * hermiteEulerCancellationPoint).re := by
    norm_num [hermiteEulerCancellationPoint]
  have hquot : riemannZeta hermiteEulerCancellationPoint /
      riemannZeta (2 * hermiteEulerCancellationPoint) ≠ 0 :=
    div_ne_zero (riemannZeta_ne_zero_of_one_lt_re hs)
      (riemannZeta_ne_zero_of_one_lt_re h2s)
  apply hquot
  rw [← LSeries_squarefreeConvolutionHalf_sq hs, hzero]
  norm_num

end

end RHTower
