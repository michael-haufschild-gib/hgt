import GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion
import GaloisForLFunctions.HTGeometry.CommonRealPartTuranDeterminant

/-!
# The Turán minor of the Gaussian heat trace

The plain Gaussian heat trace cannot decide RH: it is a single positive-weight functional of the
divisor, and a real copy of large multiplicity dominates any off-critical partner sharing its
shell.  The first `2 x 2` Hankel minor does not have this defect, and this file makes both halves
precise for the actual Xi divisor.

Write `w q = xiSpectralPoint q ^ (2 : ℕ)` and

`M n t = sum_q (w q) ^ n * exp (-t * w q)`,
`D t   = Re (M 0 t) * Re (M 2 t) - Re (M 1 t) ^ (2 : ℕ)`.

Every `M n t` is real unconditionally, by the critical-line reflection of the divisor.  Under RH
the whole divisor is real and positive in the `w` coordinate, so `M n t` is the `n`-th moment of a
positive measure and `D t >= 0` is Cauchy--Schwarz.  A single strictly negative `D t` therefore
refutes RH.

The reason this test is not blind is the vertical-line law of
`CommonRealPartTuranDeterminant`: `Re w` is constant along each shell of the divisor, so a shell is
a configuration on one vertical line, and such a configuration has strictly negative Turán
determinant as soon as it carries two points at different heights.  An off-critical copy always
supplies such a pair, because its line conjugate lies in the same shell with the opposite
imaginary part.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## §1 Gaussian-damped moments of the squared divisor -/

/-- The `n`-th Gaussian-damped moment of the squared Xi divisor. -/
def xiGaussianHeatMoment (n : ℕ) (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, (xiSpectralPoint q ^ (2 : ℕ)) ^ n * xiGaussianHeatTerm t q

/-- Critical-line reflection conjugates each moment summand. -/
theorem xiGaussianHeatMonomialTerm_lineConj (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    (xiSpectralPoint (xiZeroCopyLineConjEquiv q) ^ (2 : ℕ)) ^ n *
        xiGaussianHeatTerm t (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) ((xiSpectralPoint q ^ (2 : ℕ)) ^ n * xiGaussianHeatTerm t q) := by
  rw [xiSpectralPoint_lineConj, xiGaussianHeatTerm_lineConj, ← map_pow, ← map_pow, map_mul]

/-- Every Gaussian-damped moment is real, without RH. -/
theorem star_xiGaussianHeatMoment (n : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (xiGaussianHeatMoment n t) = xiGaussianHeatMoment n t := by
  rw [xiGaussianHeatMoment, Complex.conj_tsum]
  calc
    (∑' q : XiZeroCopy,
        (starRingEnd ℂ) ((xiSpectralPoint q ^ (2 : ℕ)) ^ n * xiGaussianHeatTerm t q)) =
        ∑' q : XiZeroCopy,
          (xiSpectralPoint (xiZeroCopyLineConjEquiv q) ^ (2 : ℕ)) ^ n *
            xiGaussianHeatTerm t (xiZeroCopyLineConjEquiv q) := by
      exact tsum_congr fun q => (xiGaussianHeatMonomialTerm_lineConj n t q).symm
    _ = ∑' q : XiZeroCopy, (xiSpectralPoint q ^ (2 : ℕ)) ^ n * xiGaussianHeatTerm t q :=
      xiZeroCopyLineConjEquiv.tsum_eq
        (fun q => (xiSpectralPoint q ^ (2 : ℕ)) ^ n * xiGaussianHeatTerm t q)

/-- The real value of a Gaussian-damped moment. -/
def xiGaussianHeatMomentReal (n : ℕ) (t : ℝ) : ℝ := (xiGaussianHeatMoment n t).re

/-- **The Turán (second Hankel) minor of the Gaussian heat trace.** -/
def xiHeatTuranDefect (t : ℝ) : ℝ :=
  xiGaussianHeatMomentReal 0 t * xiGaussianHeatMomentReal 2 t -
    xiGaussianHeatMomentReal 1 t ^ (2 : ℕ)

/-! ## §2 Under RH the moments are those of a positive measure -/

/-- Under RH every squared copy is its own real part. -/
theorem xiSpectralSq_eq_ofReal_re_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    xiSpectralPoint q ^ (2 : ℕ) = (((xiSpectralPoint q ^ (2 : ℕ)).re : ℝ) : ℂ) := by
  obtain ⟨x, hx⟩ := xiSpectralPoint_real_of_rh hRH q
  have h2 : xiSpectralPoint q ^ (2 : ℕ) = ((x ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [hx]; push_cast; ring
  rw [h2, Complex.ofReal_re]

/-- Under RH each moment summand is a nonnegative real. -/
theorem xiGaussianHeatMonomialTerm_eq_ofReal_of_rh (hRH : RiemannHypothesis)
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    (xiSpectralPoint q ^ (2 : ℕ)) ^ n * xiGaussianHeatTerm t q =
      ((((xiSpectralPoint q ^ (2 : ℕ)).re) ^ n *
        Real.exp (-(t * (xiSpectralPoint q ^ (2 : ℕ)).re)) : ℝ) : ℂ) := by
  rw [xiGaussianHeatTerm, xiSpectralSq_eq_ofReal_re_of_rh hRH q]
  have hz : -(t : ℂ) * (((xiSpectralPoint q ^ (2 : ℕ)).re : ℝ) : ℂ) =
      ((-(t * (xiSpectralPoint q ^ (2 : ℕ)).re) : ℝ) : ℂ) := by
    push_cast; ring
  rw [Complex.ofReal_re, hz, ← Complex.ofReal_exp, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul]

/-- Under RH, the `n`-th moment is the `n`-th moment of the positive Gaussian-damped measure on
the squared divisor. -/
theorem xiGaussianHeatMomentReal_eq_tsum_of_rh (hRH : RiemannHypothesis)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    xiGaussianHeatMomentReal n t =
      ∑' q : XiZeroCopy, ((xiSpectralPoint q ^ (2 : ℕ)).re) ^ n *
        Real.exp (-(t * (xiSpectralPoint q ^ (2 : ℕ)).re)) := by
  rw [xiGaussianHeatMomentReal, xiGaussianHeatMoment,
    Complex.re_tsum (summable_xiGaussianHeatMonomialTerm ht n)]
  refine tsum_congr fun q => ?_
  rw [xiGaussianHeatMonomialTerm_eq_ofReal_of_rh hRH n t q, Complex.ofReal_re]

/-- Under RH the real moment families are summable. -/
theorem summable_xiHeatRealMoment_of_rh (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t)
    (n : ℕ) :
    Summable (fun q : XiZeroCopy => ((xiSpectralPoint q ^ (2 : ℕ)).re) ^ n *
      Real.exp (-(t * (xiSpectralPoint q ^ (2 : ℕ)).re))) := by
  have hc := summable_xiGaussianHeatMonomialTerm ht n
  have hre := (Complex.hasSum_re hc.hasSum).summable
  refine hre.congr fun q => ?_
  rw [xiGaussianHeatMonomialTerm_eq_ofReal_of_rh hRH n t q, Complex.ofReal_re]

/-- **RH makes the Turán minor nonnegative.**  Under RH the moments are those of a positive
measure on the positive axis, so the minor is the Cauchy--Schwarz determinant. -/
theorem xiHeatTuranDefect_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {t : ℝ} (ht : 0 < t) : 0 ≤ xiHeatTuranDefect t := by
  classical
  set x : XiZeroCopy → ℝ := fun q => (xiSpectralPoint q ^ (2 : ℕ)).re with hxdef
  set e : XiZeroCopy → ℝ := fun q => Real.exp (-(t * x q)) with hedef
  have hxpos : ∀ q, 0 < x q := fun q => xiSpectralSq_re_pos q
  have hepos : ∀ q, 0 < e q := fun q => Real.exp_pos _
  have hS0 : Summable (fun q => e q) := by
    have := summable_xiHeatRealMoment_of_rh hRH ht 0
    simpa using this
  have hS2 : Summable (fun q => x q ^ (2 : ℕ) * e q) := summable_xiHeatRealMoment_of_rh hRH ht 2
  have hS1 : Summable (fun q => x q * e q) := by
    have := summable_xiHeatRealMoment_of_rh hRH ht 1
    simpa using this
  have hM0 : xiGaussianHeatMomentReal 0 t = ∑' q, e q := by
    rw [xiGaussianHeatMomentReal_eq_tsum_of_rh hRH ht 0]
    simp [hedef, hxdef]
  have hM1 : xiGaussianHeatMomentReal 1 t = ∑' q, x q * e q := by
    rw [xiGaussianHeatMomentReal_eq_tsum_of_rh hRH ht 1]
    simp [hedef, hxdef]
  have hM2 : xiGaussianHeatMomentReal 2 t = ∑' q, x q ^ (2 : ℕ) * e q :=
    xiGaussianHeatMomentReal_eq_tsum_of_rh hRH ht 2
  have hS0nn : 0 ≤ ∑' q, e q := tsum_nonneg fun q => (hepos q).le
  have hS2nn : 0 ≤ ∑' q, x q ^ (2 : ℕ) * e q :=
    tsum_nonneg fun q => by positivity
  have hS1nn : 0 ≤ ∑' q, x q * e q :=
    tsum_nonneg fun q => mul_nonneg (hxpos q).le (hepos q).le
  have hbound : ∀ s : Finset XiZeroCopy,
      ∑ q ∈ s, x q * e q ≤ Real.sqrt ((∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q) := by
    intro s
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun q => Real.sqrt (e q)) (fun q => x q * Real.sqrt (e q))
    have hprod : ∀ q, Real.sqrt (e q) * (x q * Real.sqrt (e q)) = x q * e q := by
      intro q
      have : Real.sqrt (e q) * Real.sqrt (e q) = e q :=
        Real.mul_self_sqrt (hepos q).le
      calc
        Real.sqrt (e q) * (x q * Real.sqrt (e q))
            = x q * (Real.sqrt (e q) * Real.sqrt (e q)) := by ring
        _ = x q * e q := by rw [this]
    have hsq1 : ∀ q, Real.sqrt (e q) ^ (2 : ℕ) = e q := fun q =>
      Real.sq_sqrt (hepos q).le
    have hsq2 : ∀ q, (x q * Real.sqrt (e q)) ^ (2 : ℕ) = x q ^ (2 : ℕ) * e q := by
      intro q
      rw [mul_pow, hsq1]
    rw [Finset.sum_congr rfl (fun q _ => hprod q),
      Finset.sum_congr rfl (fun q _ => hsq1 q),
      Finset.sum_congr rfl (fun q _ => hsq2 q)] at hcs
    have hle0 : ∑ q ∈ s, e q ≤ ∑' q, e q :=
      hS0.sum_le_tsum s (fun q _ => (hepos q).le)
    have hle2 : ∑ q ∈ s, x q ^ (2 : ℕ) * e q ≤ ∑' q, x q ^ (2 : ℕ) * e q :=
      hS2.sum_le_tsum s (fun q _ => by positivity)
    have hnn : 0 ≤ ∑ q ∈ s, x q * e q :=
      Finset.sum_nonneg fun q _ => mul_nonneg (hxpos q).le (hepos q).le
    have hchain : (∑ q ∈ s, x q * e q) ^ (2 : ℕ) ≤
        (∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q := by
      refine le_trans hcs ?_
      have h0nn : 0 ≤ ∑ q ∈ s, e q := Finset.sum_nonneg fun q _ => (hepos q).le
      have h2nn : 0 ≤ ∑ q ∈ s, x q ^ (2 : ℕ) * e q :=
        Finset.sum_nonneg fun q _ => by positivity
      nlinarith
    exact (Real.le_sqrt hnn (mul_nonneg hS0nn hS2nn)).mpr hchain
  have hS1le : (∑' q, x q * e q) ≤
      Real.sqrt ((∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q) :=
    hS1.tsum_le_of_sum_le hbound
  have hsq : (∑' q, x q * e q) ^ (2 : ℕ) ≤ (∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q := by
    have hsqrt : Real.sqrt ((∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q) ^ (2 : ℕ) =
        (∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q :=
      Real.sq_sqrt (mul_nonneg hS0nn hS2nn)
    calc
      (∑' q, x q * e q) ^ (2 : ℕ)
          ≤ Real.sqrt ((∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q) ^ (2 : ℕ) := by
            exact pow_le_pow_left₀ hS1nn hS1le 2
      _ = (∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q := hsqrt
  rw [xiHeatTuranDefect, hM0, hM1, hM2]
  linarith

/-- **A single negative Turán minor refutes RH.** -/
theorem not_riemannHypothesis_of_xiHeatTuranDefect_neg {t : ℝ} (ht : 0 < t)
    (h : xiHeatTuranDefect t < 0) : ¬ RiemannHypothesis := fun hRH =>
  absurd (xiHeatTuranDefect_nonneg_of_riemannHypothesis hRH ht) (not_le.mpr h)

/-! ## §3 Why the Turán minor is not blind: shells are vertical-line configurations -/

open GaloisForLFunctions.HTGeometry

/-- The shell of the squared divisor at a prescribed real part. -/
def xiHeatShell (A : ℝ) : Finset XiZeroCopy := by
  classical
  exact (finite_xiHeatShell A).toFinset.filter
    (fun q => (xiSpectralPoint q ^ (2 : ℕ)).re = A)

theorem mem_xiHeatShell {A : ℝ} {q : XiZeroCopy} :
    q ∈ xiHeatShell A ↔ (xiSpectralPoint q ^ (2 : ℕ)).re = A := by
  classical
  rw [xiHeatShell, Finset.mem_filter, Set.Finite.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨le_of_eq h, h⟩⟩

/-- **The vertical-line law on an off-critical shell.**  Every shell of the squared divisor lies on
one vertical line, and an off-critical copy contributes together with its line conjugate two shell
points at opposite heights.  Hence the shell's Turán determinant is strictly negative — the exact
feature the plain trace lacks. -/
theorem xiHeatShell_turanDeterminant_re_neg_of_im_ne_zero {A : ℝ} {q₀ : XiZeroCopy}
    (hq₀ : (xiSpectralPoint q₀ ^ (2 : ℕ)).re = A)
    (h0 : (xiSpectralPoint q₀ ^ (2 : ℕ)).im ≠ 0) :
    (configTuranDeterminant (xiHeatShell A) (fun _ => (1 : ℝ))
      (fun q => xiSpectralPoint q ^ (2 : ℕ))).re < 0 := by
  classical
  set q₁ : XiZeroCopy := xiZeroCopyLineConjEquiv q₀ with hq₁
  have hconj : xiSpectralPoint q₁ ^ (2 : ℕ) =
      (starRingEnd ℂ) (xiSpectralPoint q₀ ^ (2 : ℕ)) := by
    rw [hq₁, xiSpectralPoint_lineConj, ← map_pow]
  have hq₁re : (xiSpectralPoint q₁ ^ (2 : ℕ)).re = A := by
    rw [hconj, Complex.conj_re, hq₀]
  have hq₁im : (xiSpectralPoint q₁ ^ (2 : ℕ)).im = -(xiSpectralPoint q₀ ^ (2 : ℕ)).im := by
    rw [hconj, Complex.conj_im]
  refine configTuranDeterminant_re_neg_of_common_re
    (A := A) (fun i _ => zero_le_one) (fun i hi => mem_xiHeatShell.mp hi)
    (mem_xiHeatShell.mpr hq₀) (mem_xiHeatShell.mpr hq₁re) one_pos one_pos ?_
  rw [hq₁im]
  intro hcontra
  apply h0
  linarith

end

end RHTower
