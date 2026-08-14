import GaloisForLFunctions.HTGeometry.GeometricCDDConstraint
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The open family of finite rational CDD shells

A finite positive seed `a : ι → K` with multiplicities `m : ι → ℕ` defines the rational shell

`B_A(t) = ∏_j ((a j - t)/(a j + t))^(2 m j)`

and its one-sided scale orbit `∏_{k < N} B_A(q^k t)`.  This file proves the exact finite algebra of
that family: the value at the origin, the reflection identity `B_A(-t) = B_A(t)⁻¹`, the one-step
`q`-decimation constraint, the rapidity unitarity and crossing identities, the strict contraction of
every shell factor in the physical strip, unimodularity on the real axis, and the strictly
increasing unwrapped real-axis phase.  It also records the differential-algebraic stability of the
family under a nonzero rational CDD dressing.

The single-seed case is `GeometricCDDConstraint`; this file is the several-seed statement with
multiplicities, which is the family the open-parameter theorem quantifies over.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The finite rational CDD shell of a positive seed with multiplicities. -/
def cddShell {K : Type*} [Field K] (a : ι → K) (m : ι → ℕ) (t : K) : K :=
  ∏ j, ((a j - t) / (a j + t)) ^ (2 * m j)

/-- The one-sided scale orbit of the shell, truncated at `N` scales. -/
def cddShellOrbit {K : Type*} [Field K] (q : K) (a : ι → K) (m : ι → ℕ)
    (t : K) (N : ℕ) : K :=
  ∏ k ∈ Finset.range N, cddShell a m (q ^ k * t)

@[simp]
theorem cddShellOrbit_zero {K : Type*} [Field K] (q : K) (a : ι → K) (m : ι → ℕ)
    (t : K) : cddShellOrbit q a m t 0 = 1 := by
  simp [cddShellOrbit]

/-- The shell is normalized at the origin. -/
@[simp]
theorem cddShell_zero {K : Type*} [Field K] {a : ι → K} (m : ι → ℕ)
    (ha : ∀ j, a j ≠ 0) : cddShell a m 0 = 1 := by
  unfold cddShell
  apply Finset.prod_eq_one
  intro j _
  rw [sub_zero, add_zero, div_self (ha j), one_pow]

/-- The whole scale orbit is normalized at the origin. -/
@[simp]
theorem cddShellOrbit_at_zero {K : Type*} [Field K] (q : K) {a : ι → K} (m : ι → ℕ)
    (ha : ∀ j, a j ≠ 0) (N : ℕ) : cddShellOrbit q a m 0 N = 1 := by
  unfold cddShellOrbit
  apply Finset.prod_eq_one
  intro k _
  rw [mul_zero, cddShell_zero m ha]

/-- Reflection of the crossing coordinate inverts the shell. -/
theorem cddShell_neg_mul {K : Type*} [Field K] {a : ι → K} (m : ι → ℕ) {t : K}
    (hm : ∀ j, a j - t ≠ 0) (hp : ∀ j, a j + t ≠ 0) :
    cddShell a m (-t) * cddShell a m t = 1 := by
  unfold cddShell
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j _
  rw [sub_neg_eq_add, ← sub_eq_add_neg, ← mul_pow, div_mul_div_comm,
    show (a j + t) * (a j - t) = (a j - t) * (a j + t) from mul_comm _ _,
    div_self (mul_ne_zero (hm j) (hp j)), one_pow]

/-- Scaling the crossing coordinate shifts the orbit index by one. -/
theorem cddShell_succ_eq_scale {K : Type*} [Field K] (q : K) (a : ι → K) (m : ι → ℕ)
    (t : K) (k : ℕ) :
    cddShell a m (q ^ (k + 1) * t) = cddShell a m (q ^ k * (q * t)) := by
  rw [pow_succ]
  ring_nf

/-- **The exact finite `q`-decimation constraint.**  The new scale-zero shell is the boundary term
left by shifting every older scale. -/
theorem cddShellOrbit_succ_constraint {K : Type*} [Field K] (q : K) (a : ι → K)
    (m : ι → ℕ) (t : K) (N : ℕ) :
    cddShellOrbit q a m t (N + 1) = cddShell a m t * cddShellOrbit q a m (q * t) N := by
  rw [cddShellOrbit, Finset.prod_range_succ']
  simp_rw [cddShell_succ_eq_scale]
  rw [cddShellOrbit, pow_zero, one_mul, mul_comm]

/-- Reflection inverts every finite scale orbit away from its zeros and poles. -/
theorem cddShellOrbit_neg_mul {K : Type*} [Field K] (q : K) {a : ι → K} (m : ι → ℕ)
    {t : K} (N : ℕ)
    (hm : ∀ k < N, ∀ j, a j - q ^ k * t ≠ 0)
    (hp : ∀ k < N, ∀ j, a j + q ^ k * t ≠ 0) :
    cddShellOrbit q a m (-t) N * cddShellOrbit q a m t N = 1 := by
  rw [cddShellOrbit, cddShellOrbit, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro k hk
  rw [Finset.mem_range] at hk
  have hneg : q ^ k * (-t) = -(q ^ k * t) := by ring
  rw [hneg]
  exact cddShell_neg_mul m (hm k hk) (hp k hk)

/-- Rapidity unitarity of every nonsingular finite scale orbit. -/
theorem cddShellOrbit_rapidity_neg_mul (q C theta : ℂ) {a : ι → ℂ} (m : ι → ℕ) (N : ℕ)
    (hm : ∀ k < N, ∀ j,
      a j - q ^ k * geometricCDDCrossingCoordinate C theta ≠ 0)
    (hp : ∀ k < N, ∀ j,
      a j + q ^ k * geometricCDDCrossingCoordinate C theta ≠ 0) :
    cddShellOrbit q a m (geometricCDDCrossingCoordinate C (-theta)) N *
        cddShellOrbit q a m (geometricCDDCrossingCoordinate C theta) N = 1 := by
  rw [geometricCDDCrossingCoordinate_neg]
  exact cddShellOrbit_neg_mul q m N hm hp

/-- Crossing-period inversion of every nonsingular finite scale orbit. -/
theorem cddShellOrbit_rapidity_crossing_mul (q C theta : ℂ) {a : ι → ℂ} (m : ι → ℕ) (N : ℕ)
    (hm : ∀ k < N, ∀ j,
      a j - q ^ k * geometricCDDCrossingCoordinate C theta ≠ 0)
    (hp : ∀ k < N, ∀ j,
      a j + q ^ k * geometricCDDCrossingCoordinate C theta ≠ 0) :
    cddShellOrbit q a m
        (geometricCDDCrossingCoordinate C (theta + (Real.pi : ℂ) * Complex.I)) N *
        cddShellOrbit q a m (geometricCDDCrossingCoordinate C theta) N = 1 := by
  rw [geometricCDDCrossingCoordinate_add_pi_mul_I]
  exact cddShellOrbit_neg_mul q m N hm hp

/-- A positive real number is strictly closer to a point of the right half-plane than its
negative is. -/
theorem norm_sub_lt_norm_add_of_pos_re {a : ℝ} (ha : 0 < a) {t : ℂ} (ht : 0 < t.re) :
    ‖(a : ℂ) - t‖ < ‖(a : ℂ) + t‖ := by
  have hsq : ‖(a : ℂ) - t‖ ^ 2 < ‖(a : ℂ) + t‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [mul_pos ha ht]
  nlinarith [norm_nonneg ((a : ℂ) - t), norm_nonneg ((a : ℂ) + t), hsq]

/-- On the imaginary axis a positive real seed gives a unimodular factor. -/
theorem norm_sub_eq_norm_add_of_re_eq_zero (a : ℝ) {t : ℂ} (ht : t.re = 0) :
    ‖(a : ℂ) - t‖ = ‖(a : ℂ) + t‖ := by
  have hsq : ‖(a : ℂ) - t‖ ^ 2 = ‖(a : ℂ) + t‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, ht]
    ring
  have h1 : (0 : ℝ) ≤ ‖(a : ℂ) - t‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖(a : ℂ) + t‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

/-- **Every shell factor contracts in the physical strip.**  A positive seed and a crossing
coordinate with positive real part give a shell of modulus at most one. -/
theorem norm_cddShell_le_one {a : ι → ℝ} (ha : ∀ j, 0 < a j) (m : ι → ℕ)
    {t : ℂ} (ht : 0 < t.re) :
    ‖cddShell (fun j => ((a j : ℝ) : ℂ)) m t‖ ≤ 1 := by
  unfold cddShell
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro j _
    positivity
  · intro j _
    rw [norm_pow, norm_div]
    apply pow_le_one₀ (by positivity)
    rw [div_le_one]
    · exact le_of_lt (norm_sub_lt_norm_add_of_pos_re (ha j) ht)
    · exact lt_of_le_of_lt (norm_nonneg _) (norm_sub_lt_norm_add_of_pos_re (ha j) ht)

/-- **Unimodularity on the real rapidity axis.** -/
theorem norm_cddShell_eq_one {a : ι → ℝ} (ha : ∀ j, 0 < a j) (m : ι → ℕ)
    {t : ℂ} (ht : t.re = 0) :
    ‖cddShell (fun j => ((a j : ℝ) : ℂ)) m t‖ = 1 := by
  unfold cddShell
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro j _
  rw [norm_pow, norm_div, norm_sub_eq_norm_add_of_re_eq_zero (a j) ht,
    div_self, one_pow]
  have hpos : 0 < ‖((a j : ℝ) : ℂ) + t‖ := by
    rw [← norm_sub_eq_norm_add_of_re_eq_zero (a j) ht]
    have hre : (((a j : ℝ) : ℂ) - t).re = a j := by
      simp [Complex.sub_re, ht]
    refine norm_pos_iff.mpr fun hzero => ?_
    rw [hzero] at hre
    simp at hre
    exact absurd hre.symm (ne_of_gt (ha j))
  exact ne_of_gt hpos

/-- Every finite scale orbit of a positive seed is bounded by one in the physical strip. -/
theorem norm_cddShellOrbit_le_one {a : ι → ℝ} (ha : ∀ j, 0 < a j) (m : ι → ℕ)
    {q : ℝ} (hq : 0 < q) {t : ℂ} (ht : 0 < t.re) (N : ℕ) :
    ‖cddShellOrbit ((q : ℝ) : ℂ) (fun j => ((a j : ℝ) : ℂ)) m t N‖ ≤ 1 := by
  unfold cddShellOrbit
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro k _
    positivity
  · intro k _
    apply norm_cddShell_le_one ha m
    have hre : (((q : ℝ) : ℂ) ^ k * t).re = q ^ k * t.re := by
      simp [Complex.mul_re, ← Complex.ofReal_pow]
    rw [hre]
    exact mul_pos (pow_pos hq k) ht

/-- The imaginary part of the complex hyperbolic sine. -/
theorem sinh_im (theta : ℂ) :
    (Complex.sinh theta).im = Real.cosh theta.re * Real.sin theta.im := by
  have h : Complex.sinh theta
      = ((Real.sinh theta.re * Real.cos theta.im : ℝ) : ℂ)
        + ((Real.cosh theta.re * Real.sin theta.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im theta]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh]
    push_cast
    ring
  rw [h, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **The physical strip has positive crossing-coordinate real part.** -/
theorem geometricCDDCrossingCoordinate_re_pos {C : ℝ} (hC : 0 < C) {theta : ℂ}
    (h0 : 0 < theta.im) (hpi : theta.im < Real.pi) :
    0 < (geometricCDDCrossingCoordinate (C : ℂ) theta).re := by
  have hval : (geometricCDDCrossingCoordinate (C : ℂ) theta).re
      = Real.cosh theta.re * Real.sin theta.im / C := by
    unfold geometricCDDCrossingCoordinate
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, sinh_im]
    field_simp
    ring
  rw [hval]
  exact div_pos (mul_pos (Real.cosh_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hpi)) hC

/-- The continuous unwrapped real-axis scattering phase of a finite scale orbit of the shell.
The additive `π` records the fermionic sign in `S = -P`. -/
noncomputable def cddShellPhase (q C : ℝ) (a : ι → ℝ) (m : ι → ℕ)
    (theta : ℝ) (N : ℕ) : ℝ :=
  Real.pi + 4 * ∑ j, (m j : ℝ) * ∑ k ∈ Finset.range N,
    Real.arctan (q ^ k * Real.sinh theta / C / a j)

/-- The exact rapidity slope of the unwrapped shell phase. -/
noncomputable def cddShellPhaseSlope (q C : ℝ) (a : ι → ℝ) (m : ι → ℕ)
    (theta : ℝ) (N : ℕ) : ℝ :=
  4 * ∑ j, (m j : ℝ) * ∑ k ∈ Finset.range N,
    (q ^ k * Real.cosh theta / C / a j) /
      (1 + (q ^ k * Real.sinh theta / C / a j) ^ 2)

/-- The displayed slope is the actual derivative of the unwrapped shell phase. -/
theorem hasDerivAt_cddShellPhase (q C : ℝ) (a : ι → ℝ) (m : ι → ℕ)
    (theta : ℝ) (N : ℕ) :
    HasDerivAt (fun u => cddShellPhase q C a m u N)
      (cddShellPhaseSlope q C a m theta N) theta := by
  unfold cddShellPhase cddShellPhaseSlope
  have hterm : ∀ j : ι, ∀ k ∈ Finset.range N,
      HasDerivAt (fun u : ℝ => Real.arctan (q ^ k * Real.sinh u / C / a j))
        ((q ^ k * Real.cosh theta / C / a j) /
          (1 + (q ^ k * Real.sinh theta / C / a j) ^ 2)) theta := by
    intro j k _
    convert ((((Real.hasDerivAt_sinh theta).const_mul (q ^ k)).div_const C).div_const
      (a j)).arctan using 1
    all_goals ring
  have hj : ∀ j ∈ (Finset.univ : Finset ι),
      HasDerivAt (fun u : ℝ => (m j : ℝ) * ∑ k ∈ Finset.range N,
          Real.arctan (q ^ k * Real.sinh u / C / a j))
        ((m j : ℝ) * ∑ k ∈ Finset.range N,
          (q ^ k * Real.cosh theta / C / a j) /
            (1 + (q ^ k * Real.sinh theta / C / a j) ^ 2)) theta := by
    intro j _
    have := (HasDerivAt.sum (hterm j)).const_mul (m j : ℝ)
    simpa only [Finset.sum_apply] using this
  have hsum := HasDerivAt.sum hj
  have := (hsum.const_mul (4 : ℝ)).const_add Real.pi
  simpa only [Finset.sum_apply] using this

/-- **The unwrapped phase of every nonempty positive shell orbit is strictly increasing.** -/
theorem cddShellPhaseSlope_pos [Nonempty ι] {q C : ℝ} {a : ι → ℝ} {m : ι → ℕ}
    (hq : 0 < q) (hC : 0 < C) (ha : ∀ j, 0 < a j) (hm : ∀ j, 0 < m j)
    (theta : ℝ) (N : ℕ) :
    0 < cddShellPhaseSlope q C a m theta (N + 1) := by
  unfold cddShellPhaseSlope
  apply mul_pos (by norm_num)
  apply Finset.sum_pos
  · intro j _
    apply mul_pos (by exact_mod_cast hm j)
    apply Finset.sum_pos
    · intro k _
      apply div_pos
      · exact div_pos (div_pos (mul_pos (pow_pos hq k) (Real.cosh_pos theta)) hC) (ha j)
      · positivity
    · exact ⟨0, by simp⟩
  · exact Finset.univ_nonempty

/-- The derivative of the unwrapped phase of every nonempty positive shell orbit is positive. -/
theorem deriv_cddShellPhase_pos [Nonempty ι] {q C : ℝ} {a : ι → ℝ} {m : ι → ℕ}
    (hq : 0 < q) (hC : 0 < C) (ha : ∀ j, 0 < a j) (hm : ∀ j, 0 < m j)
    (theta : ℝ) (N : ℕ) :
    0 < deriv (fun u => cddShellPhase q C a m u (N + 1)) theta := by
  rw [(hasDerivAt_cddShellPhase q C a m theta (N + 1)).deriv]
  exact cddShellPhaseSlope_pos hq hC ha hm theta N

/-- **Stability of the family under a nonzero rational CDD dressing.**  A nonzero differentially
algebraic dressing cannot remove hypertranscendence from the shell orbit. -/
theorem hypertranscendentalOver_cdd_dressing_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {P R : E} (hR : DifferentialAlgebraicOver F R) (hR0 : R ≠ 0) :
    HypertranscendentalOver F (P * R) ↔ HypertranscendentalOver F P :=
  hypertranscendentalOver_mul_differentialAlgebraic_iff hR hR0

/-- A finite product of multipliable families is multipliable. -/
theorem multipliable_finset_prod {ι' : Type*} (F : ι' → ℕ → ℂ)
    (h : ∀ j, Multipliable (F j)) (s : Finset ι') :
    Multipliable (fun k => ∏ j ∈ s, F j k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      simp only [Finset.prod_insert hj]
      exact (h j).mul ih

/-- **Normal convergence of a single shell factor along the scale orbit.**  For a positive seed, a
contracting scale and a crossing coordinate in the closed right half-plane, the geometric decay of
`q^k t` makes the orbit product converge. -/
theorem multipliable_cddShellFactor {a q : ℝ} (ha : 0 < a) (hq0 : 0 < q) (hq1 : q < 1)
    {t : ℂ} (ht : 0 ≤ t.re) :
    Multipliable (fun k : ℕ =>
      ((a : ℂ) - ((q : ℝ) : ℂ) ^ k * t) / ((a : ℂ) + ((q : ℝ) : ℂ) ^ k * t)) := by
  have hqk : ∀ k : ℕ, (((q : ℝ) : ℂ) ^ k * t).re = q ^ k * t.re := by
    intro k
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  have hqnorm : ∀ k : ℕ, ‖((q : ℝ) : ℂ) ^ k * t‖ = q ^ k * ‖t‖ := by
    intro k
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
  have hden : ∀ k : ℕ, a ≤ ‖(a : ℂ) + ((q : ℝ) : ℂ) ^ k * t‖ := by
    intro k
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.add_re, Complex.ofReal_re, hqk k]
    have : 0 ≤ q ^ k * t.re := mul_nonneg (le_of_lt (pow_pos hq0 k)) ht
    linarith
  have hne : ∀ k : ℕ, (a : ℂ) + ((q : ℝ) : ℂ) ^ k * t ≠ 0 := by
    intro k hzero
    have := hden k
    rw [hzero, norm_zero] at this
    linarith
  have heq : ∀ k : ℕ,
      ((a : ℂ) - ((q : ℝ) : ℂ) ^ k * t) / ((a : ℂ) + ((q : ℝ) : ℂ) ^ k * t)
        = 1 + (-(2 * (((q : ℝ) : ℂ) ^ k * t))) / ((a : ℂ) + ((q : ℝ) : ℂ) ^ k * t) := by
    intro k
    have h := hne k
    field_simp
    ring
  have hsummable : Summable fun k : ℕ =>
      ‖(-(2 * (((q : ℝ) : ℂ) ^ k * t))) / ((a : ℂ) + ((q : ℝ) : ℂ) ^ k * t)‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (((summable_geometric_of_lt_one (le_of_lt hq0) hq1)).mul_left (2 * ‖t‖ / a))
    rw [norm_div, norm_neg, norm_mul, hqnorm k]
    have hpos : (0 : ℝ) < ‖(a : ℂ) + ((q : ℝ) : ℂ) ^ k * t‖ :=
      lt_of_lt_of_le ha (hden k)
    rw [div_le_iff₀ hpos]
    have hnum : ‖(2 : ℂ)‖ * (q ^ k * ‖t‖) = 2 * ‖t‖ * q ^ k := by
      rw [Complex.norm_ofNat]
      ring
    rw [hnum]
    have hstep : 2 * ‖t‖ / a * q ^ k * a ≤ 2 * ‖t‖ / a * q ^ k *
        ‖(a : ℂ) + ((q : ℝ) : ℂ) ^ k * t‖ := by
      apply mul_le_mul_of_nonneg_left (hden k)
      positivity
    refine le_trans (le_of_eq ?_) hstep
    field_simp
  have := multipliable_one_add_of_summable hsummable
  simpa only [← heq] using this

/-- **Normal convergence of the shell orbit.**  Every finite positive seed with multiplicities has a
convergent one-sided scale orbit on the closed right half-plane. -/
theorem multipliable_cddShellOrbit {a : ι → ℝ} (ha : ∀ j, 0 < a j) (m : ι → ℕ)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {t : ℂ} (ht : 0 ≤ t.re) :
    Multipliable (fun k : ℕ =>
      cddShell (fun j => ((a j : ℝ) : ℂ)) m (((q : ℝ) : ℂ) ^ k * t)) := by
  have hfactor : ∀ j : ι, Multipliable (fun k : ℕ =>
      (((a j : ℝ) : ℂ) - ((q : ℝ) : ℂ) ^ k * t) /
        (((a j : ℝ) : ℂ) + ((q : ℝ) : ℂ) ^ k * t)) :=
    fun j => multipliable_cddShellFactor (ha j) hq0 hq1 ht
  have hpow : ∀ j : ι, Multipliable (fun k : ℕ =>
      ((((a j : ℝ) : ℂ) - ((q : ℝ) : ℂ) ^ k * t) /
        (((a j : ℝ) : ℂ) + ((q : ℝ) : ℂ) ^ k * t)) ^ (2 * m j)) :=
    fun j => (hfactor j).pow (2 * m j)
  exact multipliable_finset_prod _ hpow Finset.univ

end GaloisForLFunctions.HTGeometry
