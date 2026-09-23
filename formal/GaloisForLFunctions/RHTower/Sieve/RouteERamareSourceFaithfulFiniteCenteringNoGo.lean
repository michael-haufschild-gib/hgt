import GaloisForLFunctions.RHTower.Sieve.RouteERamareIncidenceConditionalNegative
import GaloisForLFunctions.RHTower.Sieve.RouteERamareTernaryAntiscaleCapstone
import GaloisForLFunctions.RHTower.SecondMoment
import GaloisForLFunctions.HTGeometry.IncommensuratePeriodMeromorphicModel
import GaloisForLFunctions.HTGeometry.CompactFourierEntire

/-!
# Route E: source-faithful finite centering is impossible

The Ramaré incidence complement is a negative prime-load energy after its scalar integer mode is
centered.  This module classifies every finite positive-integer counterterm that could perform that
centering on a nondegenerate interval.  Finite exponential uniqueness forces the counterterm to
negate the literal Möbius packet coefficient by coefficient and to vanish off its support.  Hence a
source-faithful finite counterterm cannot center any nonempty Ramaré packet.

The positive survivor is sharp: every nonempty squarefree Ramaré packet, and therefore the actual
Ramaré bilinear form, has strictly positive squared-norm mass on every nondegenerate interval.  The
remaining Route E burden is quantitative control of this scalar mode, or a genuinely infinite or
source-overlapping compensation mechanism; no finite source-faithful spectral centering remains.
-/

open Complex Set
open GaloisForLFunctions

namespace RHTower.Sieve

open scoped ArithmeticFunction.Moebius

noncomputable section

/-- Purely imaginary exponent encoding the natural-number logarithmic phase. -/
def routeENaturalLogFrequency (n : ℕ) : ℂ :=
  (((2 * Real.pi * Real.log n : ℝ) : ℂ) * Complex.I)

/-- The Ramaré unit phase is the exponential at its natural logarithmic frequency. -/
theorem unitLogPhase_eq_exp_routeENaturalLogFrequency (w : ℝ) (n : ℕ) :
    unitLogPhase w n =
      Complex.exp (routeENaturalLogFrequency n * (w : ℂ)) := by
  unfold unitLogPhase routeENaturalLogFrequency
  congr 1
  push_cast
  ring

/-- Positive natural numbers have distinct Ramaré logarithmic frequencies. -/
theorem routeENaturalLogFrequency_injOn_positive :
    Set.InjOn routeENaturalLogFrequency {n : ℕ | 0 < n} := by
  intro a ha b hb hab
  have him := congrArg Complex.im hab
  simp only [routeENaturalLogFrequency, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at him
  have hlog : Real.log (a : ℝ) = Real.log (b : ℝ) := by
    nlinarith [Real.pi_pos]
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hexp := congrArg Real.exp hlog
  rw [Real.exp_log haR, Real.exp_log hbR] at hexp
  exact_mod_cast hexp

/-- A finite packet at positive natural logarithmic frequencies that vanishes on a nondegenerate
real interval has every coefficient zero. -/
theorem routeENaturalPacket_coeff_eq_zero_of_interval
    (S : Finset ℕ) (hpos : ∀ n ∈ S, 0 < n) (c : ℕ → ℂ)
    {t₀ r : ℝ} (hr : 0 < r)
    (hzero : ∀ t : ℝ, |t - t₀| < r →
      ∑ n ∈ S, c n * unitLogPhase t n = 0) :
    ∀ n ∈ S, c n = 0 := by
  let G : ℂ → ℂ := fun z =>
    ∑ n ∈ S, c n * Complex.exp (routeENaturalLogFrequency n * z)
  have hGdiff : Differentiable ℂ G := by
    dsimp only [G]
    fun_prop
  have hGall : ∀ z : ℂ, G z = 0 := by
    intro z
    apply GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval
      hGdiff hr
    intro t ht
    dsimp only [G]
    simpa only [unitLogPhase_eq_exp_routeENaturalLogFrequency] using hzero t ht
  apply GaloisForLFunctions.HTGeometry.exp_coeff_eq_zero_of_sum_eq_zero
    S routeENaturalLogFrequency
  · intro a ha b hb hab
    exact routeENaturalLogFrequency_injOn_positive (hpos a ha) (hpos b hb) hab
  · exact hGall

/-- Coefficient of a literal squarefree Ramaré packet plus an arbitrary finite counterterm. -/
def routeERamareFiniteCenteringCoefficient
    (P : Finset ℕ) (M : ℕ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  (if n ∈ ramareSquarefreeActiveSet P M then ((μ n : ℤ) : ℂ) else 0) + b n

/-- Exact finite-centering classification.  Vanishing on one nondegenerate interval forces the
unique counterterm: coefficientwise negation on the literal source and zero off the source. -/
theorem routeERamareFiniteCentering_classification
    (P : Finset ℕ) (M : ℕ) (U : Finset ℕ) (b : ℕ → ℂ)
    (hpos : ∀ n ∈ U, 0 < n) {t₀ r : ℝ} (hr : 0 < r) :
    (∀ t : ℝ, |t - t₀| < r →
      ∑ n ∈ U, routeERamareFiniteCenteringCoefficient P M b n * unitLogPhase t n = 0) ↔
    ∀ n ∈ U, b n =
      -(if n ∈ ramareSquarefreeActiveSet P M then ((μ n : ℤ) : ℂ) else 0) := by
  constructor
  · intro hzero n hn
    have hnzero := routeENaturalPacket_coeff_eq_zero_of_interval U hpos
      (routeERamareFiniteCenteringCoefficient P M b) hr hzero n hn
    unfold routeERamareFiniteCenteringCoefficient at hnzero
    linear_combination hnzero
  · intro hb t ht
    apply Finset.sum_eq_zero
    intro n hn
    rw [routeERamareFiniteCenteringCoefficient, hb n hn]
    simp

/-- **Route E finite-centering no-go.**  If the literal squarefree Ramaré packet is nonempty, no
finite counterterm that preserves every source coefficient can center it on any nondegenerate
interval, even if arbitrary new positive-integer frequencies are allowed. -/
theorem not_routeERamare_sourceFaithfulFiniteCentering
    (P : Finset ℕ) (M : ℕ)
    (hactive : (ramareSquarefreeActiveSet P M).Nonempty) :
    ¬ ∃ (U : Finset ℕ) (b : ℕ → ℂ) (t₀ r : ℝ),
      ramareSquarefreeActiveSet P M ⊆ U ∧
      (∀ n ∈ U, 0 < n) ∧ 0 < r ∧
      (∀ n ∈ ramareSquarefreeActiveSet P M, b n = 0) ∧
      ∀ t : ℝ, |t - t₀| < r →
        ∑ n ∈ U, routeERamareFiniteCenteringCoefficient P M b n *
          unitLogPhase t n = 0 := by
  rintro ⟨U, b, t₀, r, hsource, hpos, hr, hfaithful, hzero⟩
  obtain ⟨n, hn⟩ := hactive
  have hnU : n ∈ U := hsource hn
  have hclass := (routeERamareFiniteCentering_classification P M U b hpos hr).mp hzero
  have hb := hclass n hnU
  rw [if_pos hn, hfaithful n hn] at hb
  have hsf : Squarefree n := (Finset.mem_filter.mp hn).2
  have hmul := moebius_real_mul_self_eq_one_of_squarefree hsf
  have hmu0 : (((μ n : ℤ) : ℝ)) = 0 := by
    exact_mod_cast (neg_eq_zero.mp hb.symm)
  rw [hmu0] at hmul
  norm_num at hmul

/-- A nonempty literal squarefree Ramaré scalar packet cannot vanish throughout any nondegenerate
interval. -/
theorem routeERamareSquarefreeActiveScalar_not_zero_on_interval
    (P : Finset ℕ) (M : ℕ)
    (hactive : (ramareSquarefreeActiveSet P M).Nonempty)
    {t₀ r : ℝ} (hr : 0 < r) :
    ¬ ∀ t : ℝ, |t - t₀| < r →
      ∑ n ∈ ramareSquarefreeActiveSet P M, moebiusPhase t n = 0 := by
  intro hzero
  let S := ramareSquarefreeActiveSet P M
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    obtain ⟨hnactive, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnIcc, _⟩ := Finset.mem_filter.mp hnactive
    exact (Finset.mem_Icc.mp hnIcc).1
  have hcoeff := routeENaturalPacket_coeff_eq_zero_of_interval S hpos
    (fun n => ((μ n : ℤ) : ℂ)) hr (by
      intro t ht
      simpa only [S, moebiusPhase] using hzero t ht)
  obtain ⟨n, hn⟩ := hactive
  have hnS : n ∈ S := hn
  have hmu := hcoeff n hnS
  have hsf : Squarefree n := (Finset.mem_filter.mp hn).2
  have hmul := moebius_real_mul_self_eq_one_of_squarefree hsf
  have hmu0 : (((μ n : ℤ) : ℝ)) = 0 := by exact_mod_cast hmu
  rw [hmu0] at hmul
  norm_num at hmul

/-- **Positive survivor.**  Every nonempty literal squarefree Ramaré scalar packet has strictly
positive squared-norm mass on every nondegenerate interval. -/
theorem routeERamareSquarefreeActiveScalar_intervalEnergy_pos
    (P : Finset ℕ) (M : ℕ)
    (hactive : (ramareSquarefreeActiveSet P M).Nonempty)
    {t₀ r : ℝ} (hr : 0 < r) :
    0 < ∫ t in (t₀ - r)..(t₀ + r),
      ‖∑ n ∈ ramareSquarefreeActiveSet P M, moebiusPhase t n‖ ^ (2 : ℕ) := by
  let F : ℝ → ℂ := fun t =>
    ∑ n ∈ ramareSquarefreeActiveSet P M, moebiusPhase t n
  have hF : Continuous F := by
    dsimp only [F]
    exact continuous_finsetSum _ fun n _ => continuous_moebiusPhase n
  have hnot := routeERamareSquarefreeActiveScalar_not_zero_on_interval
    P M hactive (t₀ := t₀) hr
  push Not at hnot
  obtain ⟨t, ht, hne⟩ := hnot
  apply RHTower.intervalIntegral_pos_of_continuous_nonneg_of_exists_pos
      (hF.norm.pow 2) (fun _ _ => sq_nonneg _)
  refine ⟨t, ?_, ?_⟩
  · rw [abs_lt] at ht
    exact ⟨by linarith, by linarith⟩
  · have hnorm : 0 < ‖F t‖ := norm_pos_iff.mpr hne
    exact sq_pos_of_pos hnorm

/-- The actual Ramaré bilinear form inherits strict positive interval energy whenever its literal
squarefree active support is nonempty. -/
theorem routeERamareBilinear_intervalEnergy_pos
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ)
    (hactive : (ramareSquarefreeActiveSet P M).Nonempty)
    {t₀ r : ℝ} (hr : 0 < r) :
    0 < ∫ t in (t₀ - r)..(t₀ + r), ‖ramareBilinear P M t‖ ^ (2 : ℕ) := by
  simpa only [ramareBilinear_eq_squarefreeActiveSum hPprime M] using
    routeERamareSquarefreeActiveScalar_intervalEnergy_pos P M hactive hr

end

end RHTower.Sieve
