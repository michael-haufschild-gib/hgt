import GaloisForLFunctions.RHTower.DeningerExpSchwartz
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The collar exchange of the exponentially decreasing source

The two Fourier collars of the Möbius calculus are exchanged by

`(J h)(t) = e^{-t} h(-t)`,

which under `x ↦ log x` is the ray inversion `H_{Jh}(x) = x^{-1} H_h(1/x)`.  The exponential factor
is not of temperate growth, so `J` is *not* an operation of the Schwartz space; it is an operation
of the exponentially decreasing source, where the weight `e^{|t|}` is absorbed by moving the source
exponent from `A` to `A + 1`.

Because `|x|^k ≤ k! e^{|x|}`, a smooth function carrying exponential-weight bounds of every order
is automatically Schwartz.  That is the construction which turns the pointwise formula for `J h`
into an element of the source.

* `deningerPow_le_factorial_mul_exp` : `|x|^k ≤ k! e^{|x|}`.
* `deningerExpSchwartzOfBounds` : exponential bounds of every order build a Schwartz map.
* `deningerCollarExchange` : **the collar exchange `J`, as an operation of the source.**
* `deningerCollarExchange_involutive` : **`J² = 1`.**
-/

namespace RHTower

open SchwartzMap
open scoped ContDiff

noncomputable section

/-! ## Exponential bounds build Schwartz maps -/

/-- **Every power is dominated by the exponential**, with the factorial as constant. -/
theorem deningerPow_le_factorial_mul_exp (k : ℕ) (x : ℝ) :
    ‖x‖ ^ k ≤ (Nat.factorial k : ℝ) * Real.exp |x| := by
  have hnn : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hsum := Real.sum_le_exp_of_nonneg hnn (k + 1)
  have hmem : k ∈ Finset.range (k + 1) := Finset.self_mem_range_succ k
  have hterm : |x| ^ k / (Nat.factorial k : ℝ)
      ≤ ∑ i ∈ Finset.range (k + 1), |x| ^ i / (Nat.factorial i : ℝ) := by
    refine Finset.single_le_sum (f := fun i : ℕ => |x| ^ i / (Nat.factorial i : ℝ)) ?_ hmem
    intro i _
    positivity
  have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [Real.norm_eq_abs]
  rw [div_le_iff₀ hk] at hterm
  nlinarith [le_trans hterm (mul_le_mul_of_nonneg_right hsum hk.le)]

/-- **A smooth function with exponential-weight bounds of every order is Schwartz.** -/
def deningerExpSchwartzOfBounds (g : ℝ → ℂ) (hsmooth : ContDiff ℝ ∞ g)
    (hbd : ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, ∀ x : ℝ,
      Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n g x‖ ≤ C) : 𝓢(ℝ, ℂ) where
  toFun := g
  smooth' := hsmooth
  decay' k n := by
    obtain ⟨C, hC⟩ := hbd 1 n
    refine ⟨(Nat.factorial k : ℝ) * max C 0, fun x => ?_⟩
    have hnn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ n g x‖ := norm_nonneg _
    have hstep : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖
        ≤ ((Nat.factorial k : ℝ) * Real.exp |x|) * ‖iteratedFDeriv ℝ n g x‖ :=
      mul_le_mul_of_nonneg_right (deningerPow_le_factorial_mul_exp k x) hnn
    refine le_trans hstep ?_
    have hC' : Real.exp (1 * |x|) * ‖iteratedFDeriv ℝ n g x‖ ≤ max C 0 :=
      le_trans (hC x) (le_max_left _ _)
    rw [one_mul] at hC'
    have hassoc : ((Nat.factorial k : ℝ) * Real.exp |x|) * ‖iteratedFDeriv ℝ n g x‖
        = (Nat.factorial k : ℝ) * (Real.exp |x| * ‖iteratedFDeriv ℝ n g x‖) := by ring
    rw [hassoc]
    exact mul_le_mul_of_nonneg_left hC' (by positivity)

@[simp]
theorem deningerExpSchwartzOfBounds_apply (g : ℝ → ℂ) (hsmooth : ContDiff ℝ ∞ g)
    (hbd : ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, ∀ x : ℝ,
      Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n g x‖ ≤ C) (x : ℝ) :
    deningerExpSchwartzOfBounds g hsmooth hbd x = g x := rfl

theorem deningerExpSchwartzOfBounds_mem (g : ℝ → ℂ) (hsmooth : ContDiff ℝ ∞ g)
    (hbd : ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, ∀ x : ℝ,
      Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    deningerExpSchwartzOfBounds g hsmooth hbd ∈ DeningerExpSchwartz := hbd

/-! ## The collar weight -/

/-- The collar weight `e^{-t}`, as a complex-valued function of the real line. -/
def deningerCollarWeight (t : ℝ) : ℂ := ((Real.exp (-t) : ℝ) : ℂ)

theorem deningerCollarWeight_contDiff : ContDiff ℝ ∞ deningerCollarWeight := by
  have h1 : ContDiff ℝ ∞ fun t : ℝ => Real.exp (-t) :=
    Real.contDiff_exp.comp contDiff_neg
  exact Complex.ofRealCLM.contDiff.comp h1

/-- **Every derivative of the collar weight has norm `e^{-t}`.** -/
theorem deningerCollarWeight_norm_iteratedFDeriv (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n deningerCollarWeight x‖ = Real.exp (-x) := by
  have hcomp : deningerCollarWeight
      = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ fun t : ℝ => Real.exp (-1 * t) := by
    funext t
    rw [Function.comp_apply, deningerCollarWeight]
    norm_num
  have hcd : ContDiff ℝ ∞ fun t : ℝ => Real.exp (-1 * t) := by fun_prop
  rw [hcomp,
    (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ).norm_iteratedFDeriv_comp_left hcd.contDiffAt ENat.LEInfty.out,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul n (-1 : ℝ)]
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (Real.exp_pos _)]
  norm_num

/-! ## The collar exchange -/

/-- The pointwise formula `(J h)(t) = e^{-t} h(-t)` of the collar exchange. -/
def deningerCollarFun (h : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  deningerCollarWeight t * h (-t)

theorem deningerCollarFun_contDiff (h : 𝓢(ℝ, ℂ)) : ContDiff ℝ ∞ (deningerCollarFun h) := by
  have hneg : ContDiff ℝ ∞ fun t : ℝ => (h : ℝ → ℂ) (-t) :=
    h.smooth'.comp contDiff_neg
  exact deningerCollarWeight_contDiff.mul hneg

/-- Reflection preserves the norms of all derivatives. -/
theorem deningerReflect_norm_iteratedFDeriv (h : 𝓢(ℝ, ℂ)) (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (fun t : ℝ => (h : ℝ → ℂ) (-t)) x‖
      = ‖iteratedFDeriv ℝ n (h : ℝ → ℂ) (-x)‖ := by
  have hcomp : (fun t : ℝ => (h : ℝ → ℂ) (-t))
      = (h : ℝ → ℂ) ∘ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) := rfl
  rw [hcomp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
  rfl

/-- **The collar exchange lands in the source.**  The weight `e^{-t}` costs one unit of the source
exponent, which the source has at every level. -/
theorem deningerCollarFun_bounds {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, ∀ x : ℝ,
      Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n (deningerCollarFun h) x‖ ≤ C := by
  intro A n
  choose C hC using fun m : ℕ => hh (A + 1) m
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * max (C (n - i)) 0, fun x => ?_⟩
  have hneg : ContDiff ℝ ∞ fun t : ℝ => (h : ℝ → ℂ) (-t) := h.smooth'.comp contDiff_neg
  have hleib := norm_iteratedFDeriv_mul_le (f := deningerCollarWeight)
    (g := fun t : ℝ => (h : ℝ → ℂ) (-t)) deningerCollarWeight_contDiff hneg x
    (n := n) ENat.LEInfty.out
  have hexp : (0 : ℝ) < Real.exp (A * |x|) := Real.exp_pos _
  have hstep : Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n (deningerCollarFun h) x‖
      ≤ Real.exp (A * |x|) *
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i deningerCollarWeight x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun t : ℝ => (h : ℝ → ℂ) (-t)) x‖ :=
    mul_le_mul_of_nonneg_left hleib hexp.le
  refine le_trans hstep ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [deningerCollarWeight_norm_iteratedFDeriv, deningerReflect_norm_iteratedFDeriv]
  have hweight : Real.exp (A * |x|) * Real.exp (-x)
      ≤ Real.exp ((A + 1) * |(-x)|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hle : -x ≤ |x| := neg_le_abs x
    have habs : |(-x)| = |x| := abs_neg x
    rw [habs]
    nlinarith
  have hbase : Real.exp ((A + 1) * |(-x)|) *
      ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) (-x)‖ ≤ max (C (n - i)) 0 :=
    le_trans (hC (n - i) (-x)) (le_max_left _ _)
  have hnn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) (-x)‖ := norm_nonneg _
  have hmid : Real.exp (A * |x|) * Real.exp (-x) *
      ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) (-x)‖ ≤ max (C (n - i)) 0 :=
    le_trans (mul_le_mul_of_nonneg_right hweight hnn) hbase
  have hchoose : (0 : ℝ) ≤ (n.choose i : ℝ) := by positivity
  calc Real.exp (A * |x|) *
        ((n.choose i : ℝ) * Real.exp (-x) *
          ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) (-x)‖)
      = (n.choose i : ℝ) * (Real.exp (A * |x|) * Real.exp (-x) *
          ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) (-x)‖) := by ring
    _ ≤ (n.choose i : ℝ) * max (C (n - i)) 0 :=
        mul_le_mul_of_nonneg_left hmid hchoose

/-- **The collar exchange** `J h (t) = e^{-t} h(-t)`, as an operation of the exponentially
decreasing source. -/
def deningerCollarExchange (h : DeningerExpSchwartz) : DeningerExpSchwartz :=
  ⟨deningerExpSchwartzOfBounds (deningerCollarFun (h : 𝓢(ℝ, ℂ)))
      (deningerCollarFun_contDiff _) (deningerCollarFun_bounds h.2),
    deningerExpSchwartzOfBounds_mem _ _ _⟩

@[simp]
theorem deningerCollarExchange_apply (h : DeningerExpSchwartz) (t : ℝ) :
    ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = ((Real.exp (-t) : ℝ) : ℂ) * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t) := rfl

/-- **The collar exchange is an involution.**  The two exponential weights cancel and the two
reflections compose to the identity. -/
theorem deningerCollarExchange_involutive (h : DeningerExpSchwartz) :
    deningerCollarExchange (deningerCollarExchange h) = h := by
  ext t
  rw [deningerCollarExchange_apply, deningerCollarExchange_apply, neg_neg,
    ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    Complex.ofReal_one, one_mul]

end

end RHTower
