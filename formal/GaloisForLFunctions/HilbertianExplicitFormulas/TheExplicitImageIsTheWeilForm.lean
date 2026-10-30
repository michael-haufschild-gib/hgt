import GaloisForLFunctions.RHTower.XiWeilLineConjHilbert

/-!
# The explicit image of the same-point problem is the Weil form

An explicit formula evaluates zero sums `∑ m h(z)` with an entire weight `h` (spectral coordinate
`z = -i(ρ - 1/2)`, line reflection `z ↦ conj z`). The same-point (Hilbert) norm needs the weight
`|F|²`, which is not holomorphic. On the critical line, where `z` is real, the two can agree. Agreement
on the line already determines the explicit weight: by the identity theorem `h = F · F#`, where
`F# z = conj (F (conj z))` is the Weil weight. Consequently:

* every line-calibrated explicit statistic computes Weil's form, on finite reflection-closed
  configurations and on the multiplicity-exact Xi divisor;
* at a line-reflection pair `{z, conj z}` its same-point error is exactly `|F z - F (conj z)|²`;
* if it is correct at one off-line pair, the test is blind to that pair;
* an explicit statistic correct on every pair forces the test to be constant.

So no choice of test function lets an explicit formula reach past Weil's form: the gap between the
Hilbert norm and the explicit formula is the line-reflection defect, and nothing holomorphic
removes it.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HilbertianExplicitFormulas

noncomputable section

/-! ## Unique continuation from the real line -/

/-- An entire function vanishing on the real line vanishes identically. -/
theorem eq_zero_of_forall_real {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (h : ∀ x : ℝ, G x = 0) : G = 0 := by
  have han : AnalyticOnNhd ℂ G Set.univ := fun z _ => hG.analyticAt z
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)) ?_
    refine Eventually.of_forall fun n => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, one_div, inv_eq_zero]
    exact_mod_cast Nat.succ_ne_zero n
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), G z = 0 := by
    refine hseq.frequently (Frequently.of_forall fun n => ?_)
    have := h (1 / ((n : ℝ) + 1))
    push_cast at this
    exact this
  funext z
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ 0) hfreq (Set.mem_univ z)

/-- An entire function vanishing on the imaginary axis vanishes identically. -/
theorem eq_zero_of_forall_imaginary {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (h : ∀ y : ℝ, G (y * I) = 0) : G = 0 := by
  have hrot : (fun z => G (z * I)) = 0 :=
    eq_zero_of_forall_real (hG.comp (differentiable_id.mul_const I)) h
  funext z
  have := congrFun hrot (-(z * I))
  simpa [mul_assoc] using this

/-! ## Calibration rigidity -/

/-- The Weil weight `F · F#` of a test `F`. -/
def weilWeight (F : ℂ → ℂ) (z : ℂ) : ℂ := F z * RHTower.xiWeilSharp F z

theorem differentiable_weilWeight {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (weilWeight F) :=
  hF.mul (RHTower.differentiable_conj_reflect hF)

/-- On the real line the Weil weight is the same-point weight `|F|²`. -/
theorem weilWeight_ofReal (F : ℂ → ℂ) (x : ℝ) :
    weilWeight F x = ((‖F x‖ ^ 2 : ℝ) : ℂ) := by
  rw [weilWeight, RHTower.xiWeilSharp, Complex.conj_ofReal, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- **Calibration rigidity.** An entire weight that equals `|F|²` on the critical line is the Weil
weight `F · F#` everywhere. -/
theorem eq_weilWeight_of_calibrated {F h : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hh : Differentiable ℂ h) (hcal : ∀ x : ℝ, h x = ((‖F x‖ ^ 2 : ℝ) : ℂ)) :
    h = weilWeight F := by
  have hzero := eq_zero_of_forall_real (hh.sub (differentiable_weilWeight hF))
    (fun x => by simp [hcal x, weilWeight_ofReal])
  funext z
  exact sub_eq_zero.mp (congrFun hzero z)

/-- The pair identity `|a|² + |b|² - (a b̄ + b ā) = |a - b|²`. -/
theorem normSq_add_normSq_sub_eq (a b : ℂ) :
    ((‖a‖ ^ 2 + ‖b‖ ^ 2 : ℝ) : ℂ) - (a * (starRingEnd ℂ) b + b * (starRingEnd ℂ) a) =
      ((‖a - b‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] <;> ring

/-- **Same-point error of an explicit statistic.** At a line-reflection pair `{z, conj z}`, a
line-calibrated explicit weight misses the same-point value by exactly `|F z - F (conj z)|²`. -/
theorem samePoint_sub_explicit_pair {F h : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hh : Differentiable ℂ h) (hcal : ∀ x : ℝ, h x = ((‖F x‖ ^ 2 : ℝ) : ℂ)) (z : ℂ) :
    ((‖F z‖ ^ 2 + ‖F ((starRingEnd ℂ) z)‖ ^ 2 : ℝ) : ℂ) - (h z + h ((starRingEnd ℂ) z)) =
      ((‖F z - F ((starRingEnd ℂ) z)‖ ^ 2 : ℝ) : ℂ) := by
  rw [eq_weilWeight_of_calibrated hF hh hcal]
  simp only [weilWeight, RHTower.xiWeilSharp, Complex.conj_conj]
  exact normSq_add_normSq_sub_eq _ _

/-- An explicit statistic that is calibrated on the line and also correct at one pair
`{z, conj z}` forces the test to be blind to that pair. -/
theorem blind_of_explicit_eq_samePoint {F h : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hh : Differentiable ℂ h) (hcal : ∀ x : ℝ, h x = ((‖F x‖ ^ 2 : ℝ) : ℂ)) {z : ℂ}
    (hz : h z + h ((starRingEnd ℂ) z) =
      ((‖F z‖ ^ 2 + ‖F ((starRingEnd ℂ) z)‖ ^ 2 : ℝ) : ℂ)) :
    F z = F ((starRingEnd ℂ) z) := by
  have hpair := samePoint_sub_explicit_pair hF hh hcal z
  rw [hz, sub_self] at hpair
  have hsq : ‖F z - F ((starRingEnd ℂ) z)‖ ^ 2 = 0 := by exact_mod_cast hpair.symm
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))

/-- A test with `F z = F (conj z)` everywhere is constant: `u ↦ F (x + u) - F (x - u)` vanishes on
the imaginary axis, hence identically, and its derivative at `0` is `2 F' x`. -/
theorem const_of_forall_eq_conj {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hsym : ∀ z, F z = F ((starRingEnd ℂ) z)) : ∀ z w, F z = F w := by
  have hderiv_real : ∀ x : ℝ, deriv F x = 0 := by
    intro x
    have hdiff : Differentiable ℂ (fun u => F (x + u) - F (x - u)) :=
      (hF.comp (differentiable_const _ |>.add differentiable_id)).sub
        (hF.comp (differentiable_const _ |>.sub differentiable_id))
    have hzero := eq_zero_of_forall_imaginary hdiff (fun y => by
      have hc : (starRingEnd ℂ) ((x : ℂ) + y * I) = x - y * I := by
        simp [Complex.conj_ofReal]; ring
      show F (x + y * I) - F (x - y * I) = 0
      rw [hsym ((x : ℂ) + y * I), hc, sub_self])
    have h1 : HasDerivAt (fun u => F (x + u)) (deriv F x) 0 := by
      have := (hF ((x : ℂ) + 0)).hasDerivAt.comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_add (x : ℂ))
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun u => F (x - u)) (-deriv F x) 0 := by
      have := (hF ((x : ℂ) - 0)).hasDerivAt.comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_sub (x : ℂ))
      simpa [Function.comp_def] using this
    have h3 : HasDerivAt (fun u => F (x + u) - F (x - u)) (deriv F x - -deriv F x) 0 :=
      h1.sub h2
    rw [hzero] at h3
    have h4 := h3.unique (hasDerivAt_const (0 : ℂ) (0 : ℂ))
    have : (2 : ℂ) * deriv F x = 0 := by rw [two_mul]; simpa using h4
    simpa using this
  have hd0 : deriv F = 0 := eq_zero_of_forall_real hF.deriv hderiv_real
  exact is_const_of_deriv_eq_zero hF (fun x => congrFun hd0 x)

/-- **No explicit same-point formula.** If an entire weight reproduces the same-point sum on every
line-reflection pair, the test is constant. -/
theorem const_of_explicit_eq_samePoint_everywhere {F h : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hh : Differentiable ℂ h)
    (hall : ∀ z, h z + h ((starRingEnd ℂ) z) =
      ((‖F z‖ ^ 2 + ‖F ((starRingEnd ℂ) z)‖ ^ 2 : ℝ) : ℂ)) :
    ∀ z w, F z = F w := by
  have hcal : ∀ x : ℝ, h x = ((‖F x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have h2 := hall x
    rw [Complex.conj_ofReal, ← two_mul] at h2
    have h2' : (2 : ℂ) * h x = 2 * ((‖F x‖ ^ 2 : ℝ) : ℂ) := by
      rw [h2]; push_cast; ring
    exact mul_left_cancel₀ two_ne_zero h2'
  exact const_of_forall_eq_conj hF fun z => blind_of_explicit_eq_samePoint hF hh hcal (hall z)

/-! ## Finite reflection-closed configurations -/

section Finite

variable {ι : Type*} [Fintype ι]

/-- Same-point form of a weighted spectral configuration. -/
def samePointForm (m : ι → ℝ) (z : ι → ℂ) (F : ℂ → ℂ) : ℝ :=
  ∑ i, m i * ‖F (z i)‖ ^ 2

/-- Explicit statistic of a weighted spectral configuration. -/
def explicitStatistic (m : ι → ℝ) (z : ι → ℂ) (h : ℂ → ℂ) : ℂ :=
  ∑ i, (m i : ℂ) * h (z i)

/-- Line-reflection defect `½ ∑ m |F z - F (conj z)|²`. -/
def lineReflectionDefect (m : ι → ℝ) (z : ι → ℂ) (F : ℂ → ℂ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, m i * ‖F (z i) - F ((starRingEnd ℂ) (z i))‖ ^ 2

/-- **Finite calibration rigidity.** On a configuration closed under line reflection, every
line-calibrated explicit statistic is Weil's form, and it falls short of the same-point form by
exactly the line-reflection defect. -/
theorem samePointForm_sub_explicitStatistic {F h : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hh : Differentiable ℂ h) (hcal : ∀ x : ℝ, h x = ((‖F x‖ ^ 2 : ℝ) : ℂ))
    (m : ι → ℝ) (z : ι → ℂ) (σ : Equiv.Perm ι)
    (hz : ∀ i, z (σ i) = (starRingEnd ℂ) (z i)) (hm : ∀ i, m (σ i) = m i) :
    ((samePointForm m z F : ℝ) : ℂ) - explicitStatistic m z h =
      ((lineReflectionDefect m z F : ℝ) : ℂ) := by
  have hreidx : ∑ i, m i * ‖F ((starRingEnd ℂ) (z i))‖ ^ 2 = ∑ i, m i * ‖F (z i)‖ ^ 2 := by
    calc ∑ i, m i * ‖F ((starRingEnd ℂ) (z i))‖ ^ 2
        = ∑ i, m (σ i) * ‖F (z (σ i))‖ ^ 2 := by simp_rw [hm, hz]
      _ = ∑ i, m i * ‖F (z i)‖ ^ 2 := Equiv.sum_comp σ (fun i => m i * ‖F (z i)‖ ^ 2)
  have hcross : explicitStatistic m z h =
      ∑ i, (m i : ℂ) * (F (z i) * (starRingEnd ℂ) (F ((starRingEnd ℂ) (z i)))) := by
    rw [explicitStatistic, eq_weilWeight_of_calibrated hF hh hcal]
    rfl
  have hcross' : explicitStatistic m z h =
      ∑ i, (m i : ℂ) * (F ((starRingEnd ℂ) (z i)) * (starRingEnd ℂ) (F (z i))) := by
    rw [hcross]
    calc ∑ i, (m i : ℂ) * (F (z i) * (starRingEnd ℂ) (F ((starRingEnd ℂ) (z i))))
        = ∑ i, (m (σ i) : ℂ) *
            (F (z (σ i)) * (starRingEnd ℂ) (F ((starRingEnd ℂ) (z (σ i))))) :=
          (Equiv.sum_comp σ _).symm
      _ = _ := by simp_rw [hm, hz, Complex.conj_conj]
  have hpt : ∀ i, ((m i * ‖F (z i) - F ((starRingEnd ℂ) (z i))‖ ^ 2 : ℝ) : ℂ) =
      (m i : ℂ) * ((‖F (z i)‖ ^ 2 + ‖F ((starRingEnd ℂ) (z i))‖ ^ 2 : ℝ) : ℂ) -
        (m i : ℂ) * (F (z i) * (starRingEnd ℂ) (F ((starRingEnd ℂ) (z i)))) -
          (m i : ℂ) * (F ((starRingEnd ℂ) (z i)) * (starRingEnd ℂ) (F (z i))) := by
    intro i
    rw [Complex.ofReal_mul, ← normSq_add_normSq_sub_eq]
    ring
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [← Complex.ofReal_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
  rw [← hcross, ← hcross'] at hsum
  have hsplit : ∑ i, (m i : ℂ) *
      ((‖F (z i)‖ ^ 2 + ‖F ((starRingEnd ℂ) (z i))‖ ^ 2 : ℝ) : ℂ) =
      2 * ((samePointForm m z F : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_sum, mul_add, Finset.sum_add_distrib,
      hreidx, samePointForm]
    push_cast; ring
  rw [hsplit] at hsum
  rw [lineReflectionDefect, Complex.ofReal_mul, hsum]
  push_cast; ring

/-- On a reflection-closed configuration with nonnegative weights, a line-calibrated explicit
statistic equals the same-point form exactly when every weighted pair is blind. -/
theorem explicitStatistic_eq_samePointForm_iff {F h : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hh : Differentiable ℂ h) (hcal : ∀ x : ℝ, h x = ((‖F x‖ ^ 2 : ℝ) : ℂ))
    (m : ι → ℝ) (z : ι → ℂ) (σ : Equiv.Perm ι)
    (hz : ∀ i, z (σ i) = (starRingEnd ℂ) (z i)) (hm : ∀ i, m (σ i) = m i)
    (hpos : ∀ i, 0 < m i) :
    explicitStatistic m z h = samePointForm m z F ↔
      ∀ i, F (z i) = F ((starRingEnd ℂ) (z i)) := by
  have hid := samePointForm_sub_explicitStatistic hF hh hcal m z σ hz hm
  constructor
  · intro heq
    rw [heq, sub_self] at hid
    have hD : lineReflectionDefect m z F = 0 := by exact_mod_cast hid.symm
    rw [lineReflectionDefect, mul_eq_zero] at hD
    rcases hD with hD | hD
    · norm_num at hD
    · intro i
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
        mul_nonneg (hpos j).le (sq_nonneg _))).mp hD i (Finset.mem_univ i)
      rcases mul_eq_zero.mp hterm with h0 | h0
      · exact absurd h0 (hpos i).ne'
      · exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0))
  · intro hblind
    have hD : lineReflectionDefect m z F = 0 := by
      simp [lineReflectionDefect, hblind]
    rw [hD, Complex.ofReal_zero] at hid
    exact (sub_eq_zero.mp hid).symm

end Finite

/-! ## The multiplicity-exact Xi divisor -/

/-- Every line-calibrated explicit statistic on the actual Xi divisor is Weil's polarization. -/
theorem tsum_explicit_eq_xiWeilPolarization {F h : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hh : Differentiable ℂ h) (hcal : ∀ x : ℝ, h x = ((‖F x‖ ^ 2 : ℝ) : ℂ)) :
    ∑' q : RHTower.XiZeroCopy, h (RHTower.xiSpectralPoint q) =
      RHTower.xiWeilPolarization F F := by
  rw [eq_weilWeight_of_calibrated hF hh hcal]
  rfl

/-- **Hilbertian defect on the Xi divisor.** The same-point norm of the evaluation vector exceeds
every line-calibrated explicit statistic by half the squared distance to its line reflection. -/
theorem norm_sq_sub_explicit_eq_half_reflectionDefect {F h : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hh : Differentiable ℂ h) (hcal : ∀ x : ℝ, h x = ((‖F x‖ ^ 2 : ℝ) : ℂ))
    (hsq : RHTower.XiWeilSquareSummable F) :
    ‖RHTower.xiWeilEvaluationLp F hsq‖ ^ 2 -
        (∑' q : RHTower.XiZeroCopy, h (RHTower.xiSpectralPoint q)).re =
      (1 / 2 : ℝ) * ‖RHTower.xiWeilEvaluationLp F hsq -
        RHTower.xiWeilLineConjLinearIsometry (RHTower.xiWeilEvaluationLp F hsq)‖ ^ 2 := by
  set v := RHTower.xiWeilEvaluationLp F hsq
  rw [tsum_explicit_eq_xiWeilPolarization hF hh hcal,
    ← RHTower.xiWeilHilbertQuadratic_evaluation_eq_polarization_re F hsq,
    RHTower.xiWeilHilbertQuadratic, norm_sub_sq (𝕜 := ℂ),
    RHTower.xiWeilLineConjLinearIsometry.norm_map]
  have hre : RCLike.re (inner ℂ v (RHTower.xiWeilLineConjLinearIsometry v)) =
      (inner ℂ (RHTower.xiWeilLineConjLinearIsometry v) v).re := by
    rw [← inner_conj_symm]
    rfl
  rw [hre]
  ring

/-- On the Xi divisor a line-calibrated explicit statistic computes the same-point norm exactly when
the evaluation vector is fixed by line reflection, i.e. the test is blind to every off-line pair. -/
theorem explicit_eq_norm_sq_iff_lineConj_fixed {F h : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hh : Differentiable ℂ h) (hcal : ∀ x : ℝ, h x = ((‖F x‖ ^ 2 : ℝ) : ℂ))
    (hsq : RHTower.XiWeilSquareSummable F) :
    (∑' q : RHTower.XiZeroCopy, h (RHTower.xiSpectralPoint q)).re =
        ‖RHTower.xiWeilEvaluationLp F hsq‖ ^ 2 ↔
      RHTower.xiWeilLineConjLinearIsometry (RHTower.xiWeilEvaluationLp F hsq) =
        RHTower.xiWeilEvaluationLp F hsq := by
  have hid := norm_sq_sub_explicit_eq_half_reflectionDefect hF hh hcal hsq
  constructor
  · intro heq
    rw [heq, sub_self] at hid
    have h0 : ‖RHTower.xiWeilEvaluationLp F hsq -
        RHTower.xiWeilLineConjLinearIsometry (RHTower.xiWeilEvaluationLp F hsq)‖ = 0 := by
      nlinarith [norm_nonneg (RHTower.xiWeilEvaluationLp F hsq -
        RHTower.xiWeilLineConjLinearIsometry (RHTower.xiWeilEvaluationLp F hsq))]
    exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm
  · intro hfix
    rw [hfix, sub_self, norm_zero] at hid
    linarith

end

end GaloisForLFunctions.HilbertianExplicitFormulas
