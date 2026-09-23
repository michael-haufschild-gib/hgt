/-
# The capacity--entropy--accessibility budget

The pointwise complete-union inequality, multiplied by the indicator of a return event and averaged,
says that the joint probability of returning and being easy is at most the circuit factor times the
capacity times the accessibility excess.  In logarithmic form: *circuit entropy plus accessibility
excess below capacity surprisal*.  The chi-square half of the accessibility divergence law follows
from the same normalization and the capacity window.

Main results:
* `measure_reachable_inter_le` — **`(11ae)`**, potential form.
* `measure_reachable_inter_le_accessAmp` — **`(11ae)`**, amplification form.
* `neg_log_measure_ge` — **`(11ae2)`**: the effective capacity surprisal minus the circuit entropy.
* `measure_reachable_le_exp` — **`(11ai)`**: the exponential-rate consequence.
* `piNormSq_accessAmp`, `le_piNormSq_accessAmp` — **`(11ab)`**: the chi-square lower bound.
-/
import GaloisForLFunctions.HTGeometry.ObserverExcisedUnion
import GaloisForLFunctions.HTGeometry.CapacityNormalizedAccessibility
import GaloisForLFunctions.HTGeometry.CapacityReplicaUncertainty

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-! ## Theorem G -/

/-- **`(11ae)`, potential form.**  The joint mass of the return event and the low-complexity event
is at most the circuit factor times the return-restricted first-entrance mass. -/
theorem measure_reachable_inter_le {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {A : Finset X} {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {M : ℝ} (hM : 1 ≤ M) {s : ℕ} (nu : X → ℝ) (hnu : ∀ x, 0 ≤ nu x)
    (R S : Finset X) (hSR : S ⊆ R) (hS : ∀ x ∈ S, ReachableWithin P A M s x) :
    (∑ x ∈ S, nu x)
      ≤ (M / a) ^ s * ∑ x ∈ R, nu x * hittingPotential P A a hP hrow ha.le ha1 x := by
  classical
  have hpow : (0 : ℝ) < (M / a) ^ s := by
    have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
    positivity
  have hind : ∀ x ∈ S, nu x
      ≤ (M / a) ^ s * (nu x * hittingPotential P A a hP hrow ha.le ha1 x) := by
    intro x hx
    have h1 := one_le_pow_mul_hittingPotential hP hrow ha ha1 hM (hS x hx)
    calc nu x = nu x * 1 := by ring
      _ ≤ nu x * ((M / a) ^ s * hittingPotential P A a hP hrow ha.le ha1 x) :=
        mul_le_mul_of_nonneg_left h1 (hnu x)
      _ = (M / a) ^ s * (nu x * hittingPotential P A a hP hrow ha.le ha1 x) := by ring
  have hSsum : (∑ x ∈ S, nu x)
      ≤ (M / a) ^ s * ∑ x ∈ S, nu x * hittingPotential P A a hP hrow ha.le ha1 x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hind
  refine le_trans hSsum (mul_le_mul_of_nonneg_left ?_ hpow.le)
  exact Finset.sum_le_sum_of_subset_of_nonneg hSR fun x _ _ =>
    mul_nonneg (hnu x) (hittingPotential_mem_unitInterval hP hrow ha.le ha1 x).1

/-- The first-entrance potential is the capacity times the accessibility amplification. -/
theorem hitting_eq_cap_mul_accessAmp {a cap : ℝ} (hcap : 0 < cap) (ha1 : a < 1) (h : X → ℝ)
    (x : X) : h x = cap / (1 - a) * accessAmp a cap h x := by
  have hden : (0 : ℝ) < 1 - a := by linarith
  rw [accessAmp]
  field_simp

/-- **`(11ae)`, amplification form.**  Capacity surprisal and accessibility excess appear
separately. -/
theorem measure_reachable_inter_le_accessAmp {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {A : Finset X} {a cap : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hcap : 0 < cap) {M : ℝ} (hM : 1 ≤ M) {s : ℕ} (nu : X → ℝ) (hnu : ∀ x, 0 ≤ nu x)
    (R S : Finset X) (hSR : S ⊆ R) (hS : ∀ x ∈ S, ReachableWithin P A M s x) :
    (∑ x ∈ S, nu x)
      ≤ (M / a) ^ s * (cap / (1 - a)) *
          ∑ x ∈ R, nu x *
            accessAmp a cap (hittingPotential P A a hP hrow ha.le ha1) x := by
  have hbase := measure_reachable_inter_le hP hrow ha ha1 hM nu hnu R S hSR hS
  have hrewrite : (∑ x ∈ R, nu x * hittingPotential P A a hP hrow ha.le ha1 x)
      = (cap / (1 - a)) *
          ∑ x ∈ R, nu x * accessAmp a cap (hittingPotential P A a hP hrow ha.le ha1) x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hitting_eq_cap_mul_accessAmp hcap ha1 (hittingPotential P A a hP hrow ha.le ha1) x]
    ring
  calc (∑ x ∈ S, nu x)
      ≤ (M / a) ^ s * ∑ x ∈ R, nu x * hittingPotential P A a hP hrow ha.le ha1 x := hbase
    _ = (M / a) ^ s * (cap / (1 - a)) *
          ∑ x ∈ R, nu x *
            accessAmp a cap (hittingPotential P A a hP hrow ha.le ha1) x := by
        rw [hrewrite]; ring

/-- **`(11ae2)`.**  In logarithmic form: the joint surprisal is at least the effective capacity
surprisal minus the circuit entropy. -/
theorem neg_log_measure_ge {p E Ma : ℝ} (s : ℕ) (hMa : 0 < Ma) (hp : 0 < p) (hE : 0 < E)
    (hle : p ≤ Ma ^ s * E) :
    -Real.log E - (s : ℝ) * Real.log Ma ≤ -Real.log p := by
  have hpow : (0 : ℝ) < Ma ^ s := by positivity
  have hlog : Real.log p ≤ Real.log (Ma ^ s * E) := Real.log_le_log hp hle
  rw [Real.log_mul (ne_of_gt hpow) (ne_of_gt hE), Real.log_pow] at hlog
  linarith

/-- **`(11ai)`.**  If the capacity term is exponentially small and the accessibility excess is
subexponential, the joint probability decays at the difference rate. -/
theorem measure_reachable_le_exp {p E Ma alpha beta D : ℝ} {s : ℕ}
    (hMa : 0 < Ma) (hs : (s : ℝ) ≤ beta * D)
    (hMa1 : 1 ≤ Ma) (hEbound : E ≤ Real.exp (-alpha * D))
    (hle : p ≤ Ma ^ s * E) :
    p ≤ Real.exp (-(alpha - beta * Real.log Ma) * D) := by
  have hpow : Ma ^ s = Real.exp ((s : ℝ) * Real.log Ma) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hlogMa : 0 ≤ Real.log Ma := Real.log_nonneg hMa1
  have hstep : (s : ℝ) * Real.log Ma ≤ beta * D * Real.log Ma :=
    mul_le_mul_of_nonneg_right hs hlogMa
  calc p ≤ Ma ^ s * E := hle
    _ ≤ Real.exp ((s : ℝ) * Real.log Ma) * Real.exp (-alpha * D) := by
        rw [hpow]
        exact mul_le_mul_of_nonneg_left hEbound (Real.exp_pos _).le
    _ = Real.exp ((s : ℝ) * Real.log Ma + -alpha * D) := by rw [← Real.exp_add]
    _ ≤ Real.exp (beta * D * Real.log Ma + -alpha * D) := by
        exact Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(alpha - beta * Real.log Ma) * D) := by
        congr 1
        ring

/-! ## `(11ab)`: the chi-square lower bound -/

theorem piNormSq_accessAmp (a cap : ℝ) (pi h : X → ℝ) :
    piNormSq pi (accessAmp a cap h) = ((1 - a) / cap) ^ (2 : ℕ) * piNormSq pi h := by
  rw [piNormSq, piNormSq, piInner, piInner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [accessAmp]
  ring

/-- **`(11ab)`.**  The chi-square divergence of the accessibility-biased law is at least
`(1−a)²/cap − 1`, hence at least `(1−a)²/π(A) − 1`. -/
theorem le_piNormSq_accessAmp {a cap : ℝ} {pi h : X → ℝ} (A : Finset X) (hcap : 0 < cap)
    (ha1 : a < 1) (hpi : ∀ x, 0 ≤ pi x) (hA : ∀ x ∈ A, h x = 1)
    (hcapA : cap ≤ ∑ x ∈ A, pi x) :
    (1 - a) ^ (2 : ℕ) / cap ≤ piNormSq pi (accessAmp a cap h) := by
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hmass := measure_le_piNormSq pi h A hpi hA
  rw [piNormSq_accessAmp]
  have hstep : ((1 - a) / cap) ^ (2 : ℕ) * cap ≤ ((1 - a) / cap) ^ (2 : ℕ) * piNormSq pi h :=
    mul_le_mul_of_nonneg_left (le_trans hcapA hmass) (by positivity)
  refine le_trans (le_of_eq ?_) hstep
  field_simp

end

end GaloisForLFunctions.HTGeometry
