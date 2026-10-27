import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheFrobeniusLadderIsMetzler
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm

/-!
# The atomic form of `ζ` is Metzler below the spacing

Atomic tests `f_x = Σ_{n ≤ N} x_n g(· − log n)` with a nonnegative bump `g` supported in `[0, w]`.
Weil's form on them is `Q(f) = M(f) + 2C(f)² − 2S(f)²` with the Markov form
`M = 2θ′(0)‖·‖² + levyEnergy − primeSum` (SpacingScaleHarmonicAnalysis). Its polar form is the
**Markov pairing** (`markovPair`), symmetric and bilinear on compactly supported `C²` tests, so on
the atomic family `M(f_x) = Σ_{m,n} x_m x_n M(g_m, g_n)` (`levyMarkovForm_atomicTest_eq`).

* **Separated atoms meet nonpositively** (`markovPair_atom_nonpos`): if `|log n − log m| > w`,
  then `∫ g_m g_n = 0`, the Lévy cross integrand `(g_m − g_m(·+y))(g_n − g_n(·+y))` is
  pointwise `−g_m g_n(·+y) − g_m(·+y) g_n ≤ 0`, and the prime pairing is a sum of nonnegative
  terms. In the Euler gauge every off-diagonal entry of the Markov Gram is `≤ 0`.
* **The atomic intersection form is Metzler below the spacing**
  (`atomicIntersectionGram_isMetzler`): for `w < δ_N` the Gram of `H, V, g_1, …, g_N` — pole plane,
  pole row `(∫ g_n e^{−u/2}, ∫ g_n e^{u/2})`, atom block `−M(g_m, g_n)` — has nonnegative
  off-diagonal entries; it is connected through `H` and has a positive weight with positive image.
* **Weil positivity below the spacing is the trickle-down inequality**
  (`weilQuad_atomicTest_nonneg_iff_weightedTrickleDown`): by the block Hodge index theorem the
  Gram is hyperbolic iff `Q(f_x) ≥ 0` for every `x`, and by the weighted Metzler Hodge index theorem
  this holds iff `(TD_π)` holds.

The sign hypothesis of Lorentzian theory is therefore satisfied by `ζ` itself on separated atomic
families, and nothing else is: the remaining content of Weil positivity there is exactly the
trickle-down inequality.
-/

noncomputable section

open MeasureTheory Set Finset Matrix RHTower
open scoped Real

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

/-! ### The Markov pairing -/

/-- The atom `g(· − log n)`. -/
def atom (g : ℝ → ℝ) (n : ℕ) (u : ℝ) : ℝ := g (u - Real.log n)

/-- The prime pairing `Σ_k Λ_k (∫ f(t) d(t − log k) + ∫ f(t) d(t + log k))`. -/
def primePair (f d : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, vonMangoldtAtom k * ((∫ t, f t * d (t - Real.log k)) + ∫ t, f t * d (t + Real.log k))

/-- The **Markov pairing**, the polar form of `levyMarkovForm`. -/
def markovPair (f d : ℝ → ℝ) : ℝ :=
  2 * gammaHardyPhaseRate 0 * (∫ u, f u * d u) + (∫ y in Ioi 0, levyMixed f d y) - primePair f d

theorem markovPair_self (f : ℝ → ℝ) : markovPair f f = levyMarkovForm f := by
  unfold markovPair levyMarkovForm levyMixed primePair levyEnergy primeSum
  simp only [← sq]

theorem primePair_comm (f d : ℝ → ℝ) : primePair f d = primePair d f := by
  unfold primePair
  refine tsum_congr fun k => ?_
  congr 1
  have e1 : ∫ t, f t * d (t - Real.log k) = ∫ t, d t * f (t + Real.log k) := by
    rw [← integral_add_right_eq_self (fun t => f t * d (t - Real.log k)) (Real.log k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [add_sub_cancel_right]; ring)
  have e2 : ∫ t, f t * d (t + Real.log k) = ∫ t, d t * f (t - Real.log k) := by
    rw [← integral_sub_right_eq_self (fun t => f t * d (t + Real.log k)) (Real.log k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [sub_add_cancel]; ring)
  rw [e1, e2, add_comm]

theorem markovPair_comm (f d : ℝ → ℝ) : markovPair f d = markovPair d f := by
  unfold markovPair levyMixed
  rw [primePair_comm]
  congr 2
  · congr 1; exact integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)
  · refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)

/-- On tests supported in `[−R, R]` the prime pairing is a finite sum. -/
theorem primePair_eq_sum_of_supportedIn {R : ℝ} {f d : ℝ → ℝ} (hf : SupportedIn R f)
    (hd : SupportedIn R d) :
    primePair f d = ∑ k ∈ Finset.range (lagRange R), vonMangoldtAtom k *
      ((∫ t, f t * d (t - Real.log k)) + ∫ t, f t * d (t + Real.log k)) := by
  rw [primePair]
  refine tsum_eq_sum fun k hk => ?_
  have hk' : lagRange R ≤ k := by simpa using hk
  have hl := two_mul_lt_abs_log_of_lagRange_le hk'
  have e1 : ∀ t, f t * d (t - Real.log k) = 0 := fun t => by
    rw [sub_eq_add_neg]
    exact mul_shift_eq_zero_of_supportedIn hf hd (by rwa [abs_neg]) t
  have e2 : ∀ t, f t * d (t + Real.log k) = 0 := fun t => mul_shift_eq_zero_of_supportedIn hf hd hl t
  simp [e1, e2]

theorem integrable_mul_shift {f d : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hd : Continuous d) (c : ℝ) : Integrable fun t => f t * d (t + c) :=
  (hf.mul (hd.comp (continuous_add_const c))).integrable_of_hasCompactSupport hfc.mul_right

theorem supportedIn_sum {ι : Type*} (s : Finset ι) {R : ℝ} {d : ι → ℝ → ℝ}
    (hdR : ∀ i, SupportedIn R (d i)) (x : ι → ℝ) : SupportedIn R fun u => ∑ i ∈ s, x i * d i u :=
  fun u hu => sum_eq_zero fun i _ => by rw [hdR i u hu, mul_zero]

/-- **Linearity in the second argument** over finite sums of `C²` tests supported in `[−R, R]`. -/
theorem markovPair_sum_right {ι : Type*} (s : Finset ι) {R : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hfR : SupportedIn R f) {d : ι → ℝ → ℝ}
    (hd : ∀ i, ContDiff ℝ 2 (d i)) (hdc : ∀ i, HasCompactSupport (d i))
    (hdR : ∀ i, SupportedIn R (d i)) (x : ι → ℝ) :
    markovPair f (fun u => ∑ i ∈ s, x i * d i u) = ∑ i ∈ s, x i * markovPair f (d i) := by
  -- the `L²` pairing
  have h1 : ∫ u, f u * ∑ i ∈ s, x i * d i u = ∑ i ∈ s, x i * ∫ u, f u * d i u := by
    simp_rw [mul_sum]
    rw [integral_finsetSum _ fun i _ => by
      simpa [mul_left_comm] using
        (integrable_mul_shift hf.continuous hfc (hd i).continuous 0).const_mul (x i)]
    refine sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  -- the Lévy cross energy
  have h2 : ∫ y in Ioi 0, levyMixed f (fun u => ∑ i ∈ s, x i * d i u) y =
      ∑ i ∈ s, x i * ∫ y in Ioi 0, levyMixed f (d i) y := by
    have hpt : ∀ y, levyMixed f (fun u => ∑ i ∈ s, x i * d i u) y =
        ∑ i ∈ s, x i * levyMixed f (d i) y := fun y => by
      unfold levyMixed
      have e : ∀ u, (f u - f (u + y)) * (∑ i ∈ s, x i * d i u - ∑ i ∈ s, x i * d i (u + y)) =
          ∑ i ∈ s, x i * ((f u - f (u + y)) * (d i u - d i (u + y))) := fun u => by
        rw [← sum_sub_distrib, mul_sum]
        exact sum_congr rfl fun i _ => by ring
      simp_rw [e]
      rw [integral_finsetSum _ fun i _ =>
        (integrable_sub_shift_mul hf.continuous hfc (hd i).continuous y).const_mul (x i), mul_sum]
      exact sum_congr rfl fun i _ => by rw [integral_const_mul]; ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ =>
      ((integrableOn_levyMixed hf hfc (hd i) (hdc i)).const_mul (x i))]
    exact sum_congr rfl fun i _ => integral_const_mul _ _
  -- the prime pairing
  have h3 : primePair f (fun u => ∑ i ∈ s, x i * d i u) = ∑ i ∈ s, x i * primePair f (d i) := by
    rw [primePair_eq_sum_of_supportedIn hfR (supportedIn_sum s hdR x)]
    simp_rw [primePair_eq_sum_of_supportedIn hfR (hdR _)]
    have e : ∀ k c, ∫ t, f t * ∑ i ∈ s, x i * d i (t + c) = ∑ i ∈ s, x i * ∫ t, f t * d i (t + c) :=
      fun k c => by
        simp_rw [mul_sum]
        rw [integral_finsetSum _ fun i _ => by
          simpa [mul_left_comm] using
            (integrable_mul_shift hf.continuous hfc (hd i).continuous c).const_mul (x i)]
        refine sum_congr rfl fun i _ => ?_
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
    simp_rw [sub_eq_add_neg, e 0, mul_sum, ← sum_add_distrib, mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring
  unfold markovPair
  rw [h1, h2, h3]
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

end GaloisForLFunctions.ArithmeticLorentzianGeometry
