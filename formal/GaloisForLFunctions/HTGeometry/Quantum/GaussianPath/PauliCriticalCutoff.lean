import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliAllClawCutoff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Absence of distinguished Pauli claws at the critical cutoff

The Gaussian tail has a reciprocal-cutoff factor. For the six terms
needed by a distinguished claw, this gives a summable probability
bound on dyadic intervals, even at the critical logarithmic cutoff.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The absolute Gaussian tail has the Mills upper bound at every positive cutoff. -/
theorem gaussianAbsoluteTailMass_mills_upper {t : ℝ} (ht : 0 < t) :
    gaussianAbsoluteTailMass t ≤
      ENNReal.ofReal ((2 / Real.sqrt (2 * Real.pi)) / t * Real.exp (-(t ^ 2 / 2))) := by
  let c := (Real.sqrt (2 * Real.pi))⁻¹
  let g (x : ℝ) := c * Real.exp (t ^ 2 / 2) * Real.exp (-t * x)
  have hg : IntegrableOn g (Ioi t) := by
    exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) t).const_mul _
  have hd (x : ℝ) (_ : x ∈ Ioi t) : gaussianPDFReal 0 1 x ≤ g x := by
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero, g, c]
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [sq_nonneg (x - t)])) (by positivity)
  have hi : (∫ x in Ioi t, g x) = c * Real.exp (-(t ^ 2 / 2)) / t := by
    have he : Real.exp (t ^ 2 / 2) * Real.exp (-t * t) = Real.exp (-(t ^ 2 / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [g]
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ht),
      neg_div_neg_eq, ← mul_div_assoc, mul_assoc, he]
  have hone : gaussianReal 0 1 (Ioi t) ≤ ENNReal.ofReal (c * Real.exp (-(t ^ 2 / 2)) / t) := by
    rw [gaussianReal_apply_eq_integral _ one_ne_zero, ← hi]
    exact ENNReal.ofReal_le_ofReal
      (setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn hg measurableSet_Ioi hd)
  have hmap : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hsym : gaussianReal 0 1 (Iio (-t)) = gaussianReal 0 1 (Ioi t) := by
    have he : (fun x : ℝ => -x) ⁻¹' Ioi t = Iio (-t) := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_Iio]
      constructor <;> intro h <;> linarith only [h]
    have hm : Measurable (fun x : ℝ => -x) := measurable_id.neg
    rw [← he, ← Measure.map_apply hm measurableSet_Ioi, hmap]
  have hsplit : {x : ℝ | t < |x|} = Ioi t ∪ Iio (-t) := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Ioi, mem_Iio, lt_abs]
    exact or_congr Iff.rfl (by constructor <;> intro h <;> linarith only [h])
  have hn : 0 ≤ c * Real.exp (-(t ^ 2 / 2)) / t := by dsimp [c]; positivity
  change gaussianReal 0 1 {x : ℝ | t < |x|} ≤ _
  rw [hsplit]
  refine (measure_union_le _ _).trans ?_
  rw [hsym]
  refine (add_le_add hone hone).trans_eq ?_
  rw [← ENNReal.ofReal_add hn hn]
  congr 1
  dsimp [c]
  ring

/-- Beyond one standard deviation, the absolute tail also has a lower
bound with the same reciprocal and exponential factors. -/
theorem gaussianAbsoluteTailMass_mills_lower {t : ℝ} (ht : 1 ≤ t) :
    ENNReal.ofReal ((Real.exp (-4) / Real.sqrt (2 * Real.pi)) / t * Real.exp (-(t ^ 2 / 2))) ≤
      gaussianAbsoluteTailMass t := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  let w := 1 / t
  have hw : 0 < w := by dsimp [w]; positivity
  have hw₁ : w ≤ 1 := (div_le_iff₀ ht₀).mpr (by simpa only [one_mul] using ht)
  have hw₂ : w ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ hw.le zero_le_one).mpr hw₁
  have htw : t * w = 1 := by dsimp [w]; field_simp
  have hsq : (t + 2 * w) ^ 2 ≤ t ^ 2 + 8 := by nlinarith only [hw₂, htw]
  refine (ENNReal.ofReal_le_ofReal ?_).trans (gaussianAbsoluteTailMass_interval_lower ht₀.le hw)
  calc
    _ = w / Real.sqrt (2 * Real.pi) * Real.exp (-(t ^ 2 / 2) - 4) := by
      rw [show -(t ^ 2 / 2) - 4 = -4 + -(t ^ 2 / 2) by ring, Real.exp_add]
      dsimp [w]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith only [hsq])) (by positivity)

/-- The six-coordinate window bound retains the sixth power of the Gaussian
reciprocal-cutoff factor. -/
theorem gaussian_measure_sixInFiveRows_mills (n : ℕ) {t : ℝ} (ht : 0 < t) :
    pathPauliDisorderLaw (sixInFiveRows n t) ≤
      ENNReal.ofReal (((n + 2 : ℕ) : ℝ) * (Nat.choose 60 6 : ℝ) *
        ((2 / Real.sqrt (2 * Real.pi)) / t) ^ 6 * Real.exp (-(3 * t ^ 2))) := by
  let a := (2 / Real.sqrt (2 * Real.pi)) / t
  let e := Real.exp (-(t ^ 2 / 2))
  have hpow : e ^ 6 = Real.exp (-(3 * t ^ 2)) := by
    dsimp [e]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hmul : (a * e) ^ 6 = a ^ 6 * Real.exp (-(3 * t ^ 2)) := by rw [mul_pow, hpow]
  have hnon : 0 ≤ a * e := by dsimp [a, e]; positivity
  refine (gaussian_measure_sixInFiveRows_le n t).trans ?_
  calc
    _ ≤ ((n + 2 : ℕ) : ENNReal) * (Nat.choose 60 6 : ENNReal) * ENNReal.ofReal (a * e) ^ 6 :=
      mul_le_mul_right (pow_le_pow_left' (gaussianAbsoluteTailMass_mills_upper ht) 6) _
    _ = ENNReal.ofReal (((n + 2 : ℕ) : ℝ) * (Nat.choose 60 6 : ℝ) * (a * e) ^ 6) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((n + 2 : ℕ) : ℝ) * (Nat.choose 60 6 : ℝ)),
        ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) (n + 2)), ENNReal.ofReal_pow hnon]
      simp only [ENNReal.ofReal_natCast]
    _ = _ := by rw [hmul, ← mul_assoc]

private def dyadicPrefix (k : ℕ) : ℕ := 2 ^ (k + 1) - 1

private theorem dyadicPrefix_cast (k : ℕ) : (dyadicPrefix k : ℝ) + 1 = (2 : ℝ) ^ (k + 1) := by
  have h : dyadicPrefix k + 1 = 2 ^ (k + 1) := by
    unfold dyadicPrefix
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos (by omega : 0 < (2 : ℕ)) _))
  exact_mod_cast h

private theorem dyadicPrefix_mono : Monotone dyadicPrefix := by
  intro k l h
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)) _

/-- Each dyadic interval uses its largest prefix and smallest threshold. -/
private def criticalDyadicEvent (k : ℕ) : Set PathPauliDisorder :=
  sixInFiveRows (dyadicPrefix (k + 1)) (clawCutoffScale (dyadicPrefix k))

private noncomputable def criticalTailConstant : ℝ :=
  3 * (Nat.choose 60 6 : ℝ) * (2 / Real.sqrt (2 * Real.pi)) ^ 6 / (Real.log 2 / 3) ^ 3

private theorem criticalDyadicEvent_bound (k : ℕ) :
    pathPauliDisorderLaw (criticalDyadicEvent k) ≤
      ENNReal.ofReal (criticalTailConstant * (1 / ((k : ℝ) + 1) ^ 3)) := by
  let n := dyadicPrefix k
  let m := dyadicPrefix (k + 1)
  let t := clawCutoffScale n
  let a := Real.log 2 / 3
  let b := 2 / Real.sqrt (2 * Real.pi)
  have ha : 0 < a := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hcast : (m : ℝ) + 1 = ((n : ℝ) + 1) * 2 := by
    rw [show (m : ℝ) + 1 = (2 : ℝ) ^ (k + 1 + 1) from dyadicPrefix_cast (k + 1),
      show (n : ℝ) + 1 = (2 : ℝ) ^ (k + 1) from dyadicPrefix_cast k, pow_succ]
  have hsize : ((m + 2 : ℕ) : ℝ) ≤ 3 * ((n : ℝ) + 1) := by
    push_cast
    linarith only [hcast, Nat.cast_nonneg (α := ℝ) n]
  have hlog : Real.log ((n : ℝ) + 1) = 3 * t ^ 2 := by
    rw [clawCutoffScale_sq n]
    ring
  have ht₂ : t ^ 2 = a * ((k : ℝ) + 1) := by
    rw [clawCutoffScale_sq n, show (n : ℝ) + 1 = (2 : ℝ) ^ (k + 1) from dyadicPrefix_cast k,
      Real.log_pow, Nat.cast_add, Nat.cast_one]
    dsimp [a]
    ring
  have ht : 0 < t := by
    have hp : 0 < t ^ 2 := by rw [ht₂]; positivity
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) fun hz => hp.ne' (by rw [← hz, zero_pow (by norm_num)])
  have ht₆ : t ^ 6 = (a * ((k : ℝ) + 1)) ^ 3 := by
    rw [show t ^ 6 = (t ^ 2) ^ 3 from pow_mul t 2 3, ht₂]
  have he : Real.exp (-(3 * t ^ 2)) = 1 / ((n : ℝ) + 1) := by
    rw [← hlog, Real.exp_neg, Real.exp_log hN, one_div]
  refine (gaussian_measure_sixInFiveRows_mills m ht).trans (ENNReal.ofReal_le_ofReal ?_)
  change ((m + 2 : ℕ) : ℝ) * (Nat.choose 60 6 : ℝ) * (b / t) ^ 6 *
    Real.exp (-(3 * t ^ 2)) ≤ _
  rw [he, div_pow, ht₆]
  calc
    _ = (((m + 2 : ℕ) : ℝ) / ((n : ℝ) + 1)) *
        ((Nat.choose 60 6 : ℝ) * b ^ 6 / (a * ((k : ℝ) + 1)) ^ 3) := by ring
    _ ≤ 3 * ((Nat.choose 60 6 : ℝ) * b ^ 6 / (a * ((k : ℝ) + 1)) ^ 3) :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ hN).mpr hsize) (by positivity)
    _ = _ := by
      rw [mul_pow]
      change _ = (3 * (Nat.choose 60 6 : ℝ) * b ^ 6 / a ^ 3) * (1 / ((k : ℝ) + 1) ^ 3)
      have hk : 0 < (k : ℝ) + 1 := by positivity
      field_simp [ha.ne', hk.ne']

private theorem criticalHit_implies_dyadic (ω : PathPauliDisorder) {K n : ℕ}
    (hn : dyadicPrefix K ≤ n) (hhit : ω ∈ sixInFiveRows n (clawCutoffScale n)) :
    ∃ k, K ≤ k ∧ ω ∈ criticalDyadicEvent k := by
  have hex : ∃ k, n < dyadicPrefix k := by
    refine ⟨n, ?_⟩
    have h := Nat.lt_two_pow_self (n := n + 1)
    unfold dyadicPrefix
    omega
  let k := Nat.find hex
  have hnk : n < dyadicPrefix k := Nat.find_spec hex
  have hk : K < k := by
    by_contra! h
    exact (not_lt_of_ge ((dyadicPrefix_mono h).trans hn)) hnk
  have hprev : dyadicPrefix (k - 1) ≤ n :=
    le_of_not_gt (Nat.find_min hex (show k - 1 < k by omega))
  have hscale : clawCutoffScale (dyadicPrefix (k - 1)) ≤ clawCutoffScale n := by
    unfold clawCutoffScale
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hprev 1)
  have hsucc : k - 1 + 1 = k := by omega
  refine ⟨k - 1, by omega, ?_⟩
  rw [criticalDyadicEvent, hsucc]
  exact sixInFiveRows_mono _ hnk.le (sixInFiveRows_antitone _ hscale hhit)

/-- The chance that any later prefix has a six-coordinate window at its
critical cutoff is bounded by the remaining inverse-cube dyadic sum. -/
theorem gaussian_measure_future_sixInFiveRows_critical :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ,
      pathPauliDisorderLaw {ω | ∃ n : ℕ, 2 ^ (K + 1) - 1 ≤ n ∧
        ω ∈ sixInFiveRows n (clawCutoffScale n)} ≤
      ∑' j : ℕ, ENNReal.ofReal (C * (1 / (((K + j : ℕ) : ℝ) + 1) ^ 3)) := by
  refine ⟨criticalTailConstant, by unfold criticalTailConstant; positivity, fun K => ?_⟩
  calc
    _ ≤ pathPauliDisorderLaw (⋃ j : ℕ, criticalDyadicEvent (K + j)) := by
      apply measure_mono
      rintro ω ⟨n, hn, hhit⟩
      obtain ⟨k, hk, hw⟩ := criticalHit_implies_dyadic ω hn hhit
      exact mem_iUnion.mpr ⟨k - K, by rwa [Nat.add_sub_of_le hk]⟩
    _ ≤ ∑' j : ℕ, pathPauliDisorderLaw (criticalDyadicEvent (K + j)) := measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum fun j => criticalDyadicEvent_bound (K + j)

/-- Almost surely no five-row window reaches six surviving coordinates
at the critical cutoff, for all sufficiently long prefixes. -/
theorem gaussian_ae_eventually_notMem_sixInFiveRows_critical :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ω ∉ sixInFiveRows n (clawCutoffScale n) := by
  have hs : Summable (fun k : ℕ => criticalTailConstant * (1 / ((k : ℝ) + 1) ^ 3)) := by
    have h := Real.summable_one_div_nat_pow.mpr (show 1 < 3 by omega)
    simpa only [Function.comp_def, Nat.cast_succ] using
      (h.comp_injective Nat.succ_injective).mul_left criticalTailConstant
  have hE : (∑' k, pathPauliDisorderLaw (criticalDyadicEvent k)) ≠ ⊤ :=
    ne_top_of_le_ne_top hs.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum criticalDyadicEvent_bound)
  filter_upwards [ae_eventually_notMem hE] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.mp hω
  refine eventually_atTop.mpr ⟨dyadicPrefix K, fun n hn hhit => ?_⟩
  obtain ⟨k, hk, hwin⟩ := criticalHit_implies_dyadic ω hn hhit
  exact hK k hk hwin

/-- At the critical cutoff, almost every draw eventually has no induced
claw with distinguishable leaves on any retained support. -/
theorem gaussian_ae_eventually_no_distinguishedClaw_critical :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ S : Set (PathLabel n),
        (∀ l ∈ S, clawCutoffScale n < |pathPauliDisorderShell ω n l|) →
        IsEmpty (DistinguishedPathClaw S) := by
  filter_upwards [gaussian_ae_eventually_notMem_sixInFiveRows_critical] with ω hω
  filter_upwards [hω] with n hn S hS
  exact ⟨fun C => hn (C.mem_sixInFiveRows ω _ hS)⟩

#print axioms gaussianAbsoluteTailMass_mills_upper
#print axioms gaussianAbsoluteTailMass_mills_lower
#print axioms gaussian_measure_sixInFiveRows_mills
#print axioms gaussian_measure_future_sixInFiveRows_critical
#print axioms gaussian_ae_eventually_notMem_sixInFiveRows_critical
#print axioms gaussian_ae_eventually_no_distinguishedClaw_critical

end GaloisForLFunctions.HTGeometry
