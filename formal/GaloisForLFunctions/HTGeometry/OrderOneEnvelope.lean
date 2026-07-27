import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The order-one growth envelope

`OrderOneEnvelope f` says that `‖f s‖ ≤ exp (C (1 + ‖s‖) log (2 + ‖s‖))` holds globally for some
`C > 0`.  This is the growth class of entire functions of order at most one and arbitrary type: it
is closed under sums, products, scalar multiples and affine substitutions, and it contains the
exponential factors `n ^ (-s)`.

The class is stable enough to be assembled term by term from an explicit finite representation, and
it implies the subquadratic envelope `exp (C (1 + ‖s‖) ^ (3/2))` consumed by Hadamard-type
zero-existence criteria.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- The exponent of the order-one growth envelope. -/
noncomputable def orderOneWeight (C : ℝ) (s : ℂ) : ℝ :=
  C * (1 + ‖s‖) * Real.log (2 + ‖s‖)

/-- An entire-order-one growth envelope: a global bound `‖f s‖ ≤ exp (C (1+‖s‖) log (2+‖s‖))`. -/
def OrderOneEnvelope (f : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖f s‖ ≤ Real.exp (orderOneWeight C s)

/-- The shape factor `(1+‖s‖) log (2+‖s‖)` is at least `log 2`. -/
theorem log_two_le_shape (s : ℂ) :
    Real.log 2 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) := by
  have hs : 0 ≤ ‖s‖ := norm_nonneg s
  have hlog : Real.log 2 ≤ Real.log (2 + ‖s‖) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

theorem shape_nonneg (s : ℂ) : 0 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) := by
  have hs : 0 ≤ ‖s‖ := norm_nonneg s
  have h1 : (0 : ℝ) ≤ 1 + ‖s‖ := by linarith
  have h2 : (0 : ℝ) ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
  exact mul_nonneg h1 h2

theorem orderOneWeight_nonneg {C : ℝ} (hC : 0 ≤ C) (s : ℂ) : 0 ≤ orderOneWeight C s := by
  rw [orderOneWeight, mul_assoc]
  exact mul_nonneg hC (shape_nonneg s)

theorem orderOneWeight_add (C C' : ℝ) (s : ℂ) :
    orderOneWeight C s + orderOneWeight C' s = orderOneWeight (C + C') s := by
  rw [orderOneWeight, orderOneWeight, orderOneWeight]; ring

theorem orderOneWeight_mono {C C' : ℝ} (h : C ≤ C') (s : ℂ) :
    orderOneWeight C s ≤ orderOneWeight C' s := by
  rw [orderOneWeight, orderOneWeight, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right h (shape_nonneg s)

/-- Constants lie in the class. -/
theorem orderOneEnvelope_const (c : ℂ) : OrderOneEnvelope (fun _ => c) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ ‖c‖ := norm_nonneg c
  refine ⟨1 + ‖c‖ / Real.log 2, by positivity, fun s => ?_⟩
  have hfrac : (0 : ℝ) ≤ ‖c‖ / Real.log 2 := by positivity
  have hcancel : ‖c‖ / Real.log 2 * Real.log 2 = ‖c‖ := div_mul_cancel₀ _ hlog2.ne'
  have hkey : ‖c‖ ≤ orderOneWeight (1 + ‖c‖ / Real.log 2) s := by
    rw [orderOneWeight, mul_assoc]
    nlinarith [log_two_le_shape s, shape_nonneg s, hcancel]
  calc ‖c‖ ≤ orderOneWeight (1 + ‖c‖ / Real.log 2) s := hkey
    _ ≤ Real.exp (orderOneWeight (1 + ‖c‖ / Real.log 2) s) := by
        linarith [Real.add_one_le_exp (orderOneWeight (1 + ‖c‖ / Real.log 2) s)]

/-- The class only depends on the pointwise values. -/
theorem OrderOneEnvelope.congr {f g : ℂ → ℂ} (hf : OrderOneEnvelope f) (h : ∀ s, f s = g s) :
    OrderOneEnvelope g := by
  obtain ⟨C, hC, hb⟩ := hf
  exact ⟨C, hC, fun s => (h s) ▸ hb s⟩

theorem OrderOneEnvelope.add {f g : ℂ → ℂ} (hf : OrderOneEnvelope f) (hg : OrderOneEnvelope g) :
    OrderOneEnvelope (fun s => f s + g s) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ + C₂ + 1, by linarith, fun s => ?_⟩
  have hsum : ‖f s + g s‖ ≤ Real.exp (orderOneWeight C₁ s) + Real.exp (orderOneWeight C₂ s) :=
    (norm_add_le _ _).trans (add_le_add (h₁ s) (h₂ s))
  have he₁ := Real.exp_le_exp.mpr (orderOneWeight_mono (show C₁ ≤ C₁ + C₂ by linarith) s)
  have he₂ := Real.exp_le_exp.mpr (orderOneWeight_mono (show C₂ ≤ C₁ + C₂ by linarith) s)
  have htwo : (2 : ℝ) * Real.exp (orderOneWeight (C₁ + C₂) s) ≤
      Real.exp (orderOneWeight (C₁ + C₂ + 1) s) := by
    have hsplit : orderOneWeight (C₁ + C₂ + 1) s
        = orderOneWeight (C₁ + C₂) s + orderOneWeight 1 s := by
      rw [orderOneWeight_add]
    rw [hsplit, Real.exp_add]
    have h2le : (2 : ℝ) ≤ Real.exp (orderOneWeight 1 s) := by
      have hlog2 : Real.log 2 ≤ orderOneWeight 1 s := by
        rw [orderOneWeight, one_mul]; exact log_two_le_shape s
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp (orderOneWeight 1 s) := Real.exp_le_exp.mpr hlog2
    calc (2 : ℝ) * Real.exp (orderOneWeight (C₁ + C₂) s)
        = Real.exp (orderOneWeight (C₁ + C₂) s) * 2 := by ring
      _ ≤ Real.exp (orderOneWeight (C₁ + C₂) s) * Real.exp (orderOneWeight 1 s) :=
          mul_le_mul_of_nonneg_left h2le (Real.exp_pos _).le
  linarith

theorem OrderOneEnvelope.mul {f g : ℂ → ℂ} (hf : OrderOneEnvelope f) (hg : OrderOneEnvelope g) :
    OrderOneEnvelope (fun s => f s * g s) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, by linarith, fun s => ?_⟩
  rw [norm_mul, ← orderOneWeight_add, Real.exp_add]
  exact mul_le_mul (h₁ s) (h₂ s) (norm_nonneg _) (Real.exp_pos _).le

theorem OrderOneEnvelope.const_mul {f : ℂ → ℂ} (c : ℂ) (hf : OrderOneEnvelope f) :
    OrderOneEnvelope (fun s => c * f s) :=
  (orderOneEnvelope_const c).mul hf

/-- The class is closed under finite sums. -/
theorem OrderOneEnvelope.finsetSum {ι : Type*} (t : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ t, OrderOneEnvelope (f i)) :
    OrderOneEnvelope (fun s => ∑ i ∈ t, f i s) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using orderOneEnvelope_const 0
  | insert i t hi ih =>
      have hhead : OrderOneEnvelope (f i) := h i (Finset.mem_insert_self i t)
      have htail : OrderOneEnvelope (fun s => ∑ j ∈ t, f j s) :=
        ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      obtain ⟨C, hC, hb⟩ := hhead.add htail
      refine ⟨C, hC, fun s => ?_⟩
      show ‖∑ j ∈ insert i t, f j s‖ ≤ Real.exp (orderOneWeight C s)
      rw [Finset.sum_insert hi]
      exact hb s

/-- The exponential factor `n ^ (-s)` lies in the class. -/
theorem orderOneEnvelope_natCast_cpow_neg {n : ℕ} (hn : 0 < n) :
    OrderOneEnvelope (fun s => (n : ℂ) ^ (-s)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hfrac : (0 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by positivity
  refine ⟨1 + Real.log (n : ℝ) / Real.log 2, by positivity, fun s => ?_⟩
  have hs : 0 ≤ ‖s‖ := norm_nonneg s
  have hnorm : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s).re := by
    rw [show ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hnpos _
  rw [hnorm, Real.rpow_def_of_pos hnpos]
  refine Real.exp_le_exp.mpr ?_
  have hre : (-s).re = -s.re := by simp
  rw [hre]
  have hrele : -s.re ≤ ‖s‖ := by
    have h1 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    have h2 : -s.re ≤ |s.re| := neg_le_abs s.re
    linarith
  have hstep : Real.log (n : ℝ) * -s.re ≤ Real.log (n : ℝ) * ‖s‖ :=
    mul_le_mul_of_nonneg_left hrele hlogn
  refine hstep.trans ?_
  rw [orderOneWeight]
  have hlogs : Real.log 2 ≤ Real.log (2 + ‖s‖) := Real.log_le_log (by norm_num) (by linarith)
  have hlogsnn : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
  have c1 : Real.log (n : ℝ) * ‖s‖
      = Real.log (n : ℝ) / Real.log 2 * (Real.log 2 * ‖s‖) := by
    field_simp
  have c2 : Real.log (n : ℝ) / Real.log 2 * (Real.log 2 * ‖s‖) ≤
      Real.log (n : ℝ) / Real.log 2 * ((1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    refine mul_le_mul_of_nonneg_left ?_ hfrac
    nlinarith
  have c3 : Real.log (n : ℝ) / Real.log 2 * ((1 + ‖s‖) * Real.log (2 + ‖s‖)) ≤
      (1 + Real.log (n : ℝ) / Real.log 2) * (1 + ‖s‖) * Real.log (2 + ‖s‖) := by
    nlinarith [shape_nonneg s]
  rw [c1]
  exact c2.trans c3

/-- The class is closed under affine substitution. -/
theorem OrderOneEnvelope.comp_affine {f : ℂ → ℂ} (hf : OrderOneEnvelope f) (α β : ℂ) :
    OrderOneEnvelope (fun s => f (α * s + β)) := by
  obtain ⟨C, hC, hb⟩ := hf
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hα : (0 : ℝ) ≤ ‖α‖ := norm_nonneg α
  have hβ : (0 : ℝ) ≤ ‖β‖ := norm_nonneg β
  have hM1 : (1 : ℝ) ≤ 1 + ‖α‖ + ‖β‖ := by linarith
  have hlogM : 0 ≤ Real.log (1 + ‖α‖ + ‖β‖) := Real.log_nonneg hM1
  have hfrac : (0 : ℝ) ≤ Real.log (1 + ‖α‖ + ‖β‖) / Real.log 2 := by positivity
  refine ⟨C * (1 + ‖α‖ + ‖β‖) * (1 + Real.log (1 + ‖α‖ + ‖β‖) / Real.log 2), by positivity,
    fun s => ?_⟩
  have hs : 0 ≤ ‖s‖ := norm_nonneg s
  have hwnorm : ‖α * s + β‖ ≤ ‖α‖ * ‖s‖ + ‖β‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
  have hone : 1 + ‖α * s + β‖ ≤ (1 + ‖α‖ + ‖β‖) * (1 + ‖s‖) := by
    nlinarith [mul_nonneg hβ hs]
  have htwo : 2 + ‖α * s + β‖ ≤ (1 + ‖α‖ + ‖β‖) * (2 + ‖s‖) := by
    nlinarith [mul_nonneg hβ hs, mul_nonneg hα hs]
  have hlogw : Real.log (2 + ‖α * s + β‖) ≤
      Real.log (1 + ‖α‖ + ‖β‖) + Real.log (2 + ‖s‖) := by
    have hpos : (0 : ℝ) < 2 + ‖α * s + β‖ := by positivity
    have hstep := Real.log_le_log hpos htwo
    rwa [Real.log_mul (by linarith) (by positivity)] at hstep
  have hlogs2 : Real.log 2 ≤ Real.log (2 + ‖s‖) := Real.log_le_log (by norm_num) (by linarith)
  have hlogsnn : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
  have hlogM' : Real.log (1 + ‖α‖ + ‖β‖) ≤
      Real.log (1 + ‖α‖ + ‖β‖) / Real.log 2 * Real.log (2 + ‖s‖) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith
  have hlogw' : Real.log (2 + ‖α * s + β‖) ≤
      (1 + Real.log (1 + ‖α‖ + ‖β‖) / Real.log 2) * Real.log (2 + ‖s‖) := by
    nlinarith
  have hlogwnn : 0 ≤ Real.log (2 + ‖α * s + β‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (α * s + β)])
  have hkey : orderOneWeight C (α * s + β) ≤
      orderOneWeight (C * (1 + ‖α‖ + ‖β‖) * (1 + Real.log (1 + ‖α‖ + ‖β‖) / Real.log 2)) s := by
    rw [orderOneWeight, orderOneWeight]
    have hprod : (1 + ‖α * s + β‖) * Real.log (2 + ‖α * s + β‖) ≤
        ((1 + ‖α‖ + ‖β‖) * (1 + ‖s‖)) *
          ((1 + Real.log (1 + ‖α‖ + ‖β‖) / Real.log 2) * Real.log (2 + ‖s‖)) :=
      mul_le_mul hone hlogw' hlogwnn (by nlinarith)
    nlinarith [hC.le, hprod]
  exact (hb (α * s + β)).trans (Real.exp_le_exp.mpr hkey)

/-- The order-one envelope implies the subquadratic envelope `exp (C (1+‖s‖) ^ (3/2))`. -/
theorem OrderOneEnvelope.subquadratic {f : ℂ → ℂ} (hf : OrderOneEnvelope f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖f s‖ ≤ Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨2 * Real.sqrt 2 * C, by positivity, fun s => ?_⟩
  refine (hb s).trans (Real.exp_le_exp.mpr ?_)
  rw [orderOneWeight]
  have hx0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  have hpos : (0 : ℝ) < 2 + ‖s‖ := by linarith
  have h1x : (0 : ℝ) < 1 + ‖s‖ := by linarith
  have hlog : Real.log (2 + ‖s‖) ≤ 2 * Real.sqrt (2 + ‖s‖) := by
    have hsqpos : 0 < Real.sqrt (2 + ‖s‖) := Real.sqrt_pos.mpr hpos
    have hhalf : Real.log (2 + ‖s‖) = 2 * Real.log (Real.sqrt (2 + ‖s‖)) := by
      rw [Real.log_sqrt hpos.le]; ring
    have hle : Real.log (Real.sqrt (2 + ‖s‖)) ≤ Real.sqrt (2 + ‖s‖) - 1 :=
      Real.log_le_sub_one_of_pos hsqpos
    rw [hhalf]; linarith
  have hsqrt2 : Real.sqrt (2 + ‖s‖) ≤ Real.sqrt 2 * Real.sqrt (1 + ‖s‖) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hchain : Real.log (2 + ‖s‖) ≤ 2 * Real.sqrt 2 * Real.sqrt (1 + ‖s‖) := by
    nlinarith [Real.sqrt_nonneg (1 + ‖s‖), Real.sqrt_nonneg 2]
  have hpow : (1 + ‖s‖) ^ (3 / 2 : ℝ) = (1 + ‖s‖) * Real.sqrt (1 + ‖s‖) := by
    have h32 : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [h32, Real.rpow_add h1x, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hpow]
  have hstep : C * (1 + ‖s‖) * Real.log (2 + ‖s‖) ≤
      C * (1 + ‖s‖) * (2 * Real.sqrt 2 * Real.sqrt (1 + ‖s‖)) :=
    mul_le_mul_of_nonneg_left hchain (mul_nonneg hC.le h1x.le)
  nlinarith [hstep]

end GaloisForLFunctions.HTGeometry
