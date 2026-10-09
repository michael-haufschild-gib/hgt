import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Causal integration of finite prime-difference packets

For continuous functions vanishing on the negative half-line, causal
integration commutes with every nonnegative backward shift difference.
One integration turns a shift difference into a moving interval integral.
The normalized square-root Riesz hinge is the causal monotone function
`max (1 - exp (-t)) 0`; these identities keep its cutoff intact.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.MobiusRieszSmoothing

def Causal (f : ℝ → ℝ) : Prop := ∀ t, t ≤ 0 → f t = 0

def primitive (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, f u

def difference (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := f t - f (t - a)

def primIter : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | r + 1, f => primitive (primIter r f)

@[simp] theorem primitive_zero (f : ℝ → ℝ) : primitive f 0 = 0 := by
  simp [primitive]

theorem hasDerivAt_primitive {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (primitive f) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    (hf.stronglyMeasurableAtFilter volume (𝓝 t)) hf.continuousAt

theorem continuous_primitive {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (primitive f) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_primitive hf t).continuousAt)

theorem causal_primitive {f : ℝ → ℝ} (hf : Causal f) : Causal (primitive f) := by
  intro t ht
  rw [primitive, intervalIntegral.integral_symm]
  have hz : (∫ u in t..0, f u) = 0 := by
    calc
      _ = ∫ _u in t..0, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le ht] at hu
        exact hf u hu.2
      _ = 0 := by simp
  rw [hz, neg_zero]

theorem continuous_difference {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Continuous (difference a f) :=
  hf.sub (hf.comp (continuous_id.sub continuous_const))

theorem causal_difference {f : ℝ → ℝ} (hf : Causal f) {a : ℝ} (ha : 0 ≤ a) :
    Causal (difference a f) := by
  intro t ht
  rw [difference, hf t ht, hf (t - a) (by linarith), sub_self]

theorem difference_primitive {f : ℝ → ℝ} (hf : Continuous f) (a t : ℝ) :
    difference a (primitive f) t = ∫ u in (t - a)..t, f u := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_primitive hf u) (hf.intervalIntegrable _ _)

theorem primitive_difference {f : ℝ → ℝ} (hf : Continuous f) (hfc : Causal f)
    {a : ℝ} (ha : 0 ≤ a) :
    primitive (difference a f) = difference a (primitive f) := by
  let F := fun t => primitive (difference a f) t - difference a (primitive f) t
  have hd (t : ℝ) : HasDerivAt F 0 t := by
    have hshift := (hasDerivAt_primitive hf (t - a)).comp t
      ((hasDerivAt_id' t).sub_const a)
    have hdiff : HasDerivAt (difference a (primitive f)) (difference a f t) t := by
      simpa only [difference, Function.comp_def, mul_one, Pi.sub_apply] using!
        (hasDerivAt_primitive hf t).sub hshift
    simpa only [sub_self, Pi.sub_apply, F] using!
      (hasDerivAt_primitive (continuous_difference hf a) t).sub hdiff
  funext t
  have heq := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0
  have hp := causal_primitive hfc (-a) (by linarith)
  simpa [F, difference, hp, sub_eq_zero] using heq

theorem primitive_nonneg {f : ℝ → ℝ} (hfc : Causal f) (hf : ∀ t, 0 ≤ f t) :
    ∀ t, 0 ≤ primitive f t := by
  intro t
  by_cases ht : 0 ≤ t
  · exact intervalIntegral.integral_nonneg ht (fun u _ => hf u)
  · rw [causal_primitive hfc t (le_of_not_ge ht)]

theorem continuous_primIter {f : ℝ → ℝ} (hf : Continuous f) (r : ℕ) :
    Continuous (primIter r f) := by
  induction r with
  | zero => exact hf
  | succ r ih => exact continuous_primitive ih

theorem causal_primIter {f : ℝ → ℝ} (hf : Causal f) (r : ℕ) :
    Causal (primIter r f) := by
  induction r with
  | zero => exact hf
  | succ r ih => exact causal_primitive ih

theorem primIter_nonneg {f : ℝ → ℝ} (hfc : Causal f) (hf : ∀ t, 0 ≤ f t) (r : ℕ) :
    ∀ t, 0 ≤ primIter r f t := by
  induction r with
  | zero => exact hf
  | succ r ih => exact primitive_nonneg (causal_primIter hfc r) ih

theorem primIter_add (r s : ℕ) (f : ℝ → ℝ) :
    primIter (r + s) f = primIter r (primIter s f) := by
  induction r with
  | zero => simp [primIter]
  | succ r ih => simp only [Nat.succ_add, primIter, ih]

theorem primIter_difference {f : ℝ → ℝ} (hf : Continuous f) (hfc : Causal f)
    {a : ℝ} (ha : 0 ≤ a) (r : ℕ) :
    primIter r (difference a f) = difference a (primIter r f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [primIter, ih, primitive_difference (continuous_primIter hf r)
        (causal_primIter hfc r) ha]
      rfl

/-- The square-root Riesz hinge after logarithmic change of scale and normalization. -/
def hinge (t : ℝ) : ℝ := max (1 - Real.exp (-t)) 0

theorem continuous_hinge : Continuous hinge := by unfold hinge; fun_prop

theorem causal_hinge : Causal hinge := by
  intro t ht
  have he : 1 ≤ Real.exp (-t) := by
    simpa using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ -t by linarith)
  exact max_eq_right (by linarith)

theorem monotone_hinge : Monotone hinge := by
  intro s t hst
  apply max_le_max _ le_rfl
  have he := Real.exp_le_exp.mpr (neg_le_neg hst)
  linarith

theorem hinge_of_nonneg {t : ℝ} (ht : 0 ≤ t) : hinge t = 1 - Real.exp (-t) := by
  have he : Real.exp (-t) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -t ≤ (0 : ℝ) by linarith)
  exact max_eq_left (by linarith)

def packet : List ℝ → ℝ → ℝ
  | [] => hinge
  | a :: A => difference a (packet A)

def smoothed (A : List ℝ) (r : ℕ) : ℝ → ℝ := primIter r (packet A)

theorem continuous_packet (A : List ℝ) : Continuous (packet A) := by
  induction A with
  | nil => exact continuous_hinge
  | cons a A ih => exact continuous_difference ih a

theorem causal_packet : ∀ A : List ℝ, (∀ a ∈ A, 0 ≤ a) → Causal (packet A) := by
  intro A
  induction A with
  | nil => intro _; exact causal_hinge
  | cons a A ih =>
      intro hA
      exact causal_difference (ih (fun b hb => hA b (by simp [hb]))) (hA a (by simp))

theorem continuous_smoothed (A : List ℝ) (r : ℕ) : Continuous (smoothed A r) :=
  continuous_primIter (continuous_packet A) r

theorem causal_smoothed {A : List ℝ} (hA : ∀ a ∈ A, 0 ≤ a) (r : ℕ) :
    Causal (smoothed A r) := causal_primIter (causal_packet A hA) r

/-- Each additional prime difference consumes one primitive and becomes a positive box integral. -/
theorem smoothed_cons_succ {A : List ℝ} (hA : ∀ a ∈ A, 0 ≤ a)
    {a : ℝ} (ha : 0 ≤ a) (r : ℕ) (t : ℝ) :
    smoothed (a :: A) (r + 1) t = ∫ u in (t - a)..t, smoothed A r u := by
  change primIter (r + 1) (difference a (packet A)) t = _
  rw [primIter_difference (continuous_packet A) (causal_packet A hA) ha]
  exact difference_primitive (continuous_smoothed A r) a t

end RHTower.MobiusRieszSmoothing
