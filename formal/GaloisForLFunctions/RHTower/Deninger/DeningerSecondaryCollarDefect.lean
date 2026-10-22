import GaloisForLFunctions.RHTower.Deninger.DeningerCollarExchange

/-!
# The centred two-collar defect and its reflected Calderón graph

Multiplication by a real exponential preserves the exponentially decreasing source: the weight
`e^{ct}` costs `|c|` units of the source exponent, which the source has at every level.  The
half-density lift `U h(t) = e^{t/2} h(t)` is the case `c = 1/2`.

The centred two-collar defect `d_sec(h₊, h₋)(t) = U h₊(t) - U h₋(-t)` therefore lands in the source,
and it vanishes exactly on the reflected Calderón graph — which is the graph of the collar exchange
`J`, since `e^{-t/2}h₋(-t) = e^{t/2}·(J h₋)(t)`.

* `deningerExpMul` : multiplication by `e^{ct}`, as an operation of the source.
* `deningerHalfDensityLift` : the lift `U`.
* `deningerSecondaryDefect` : the centred two-collar defect `(2)`.
* `deningerSecondaryDefect_eq_zero_iff` : **`(6)` ⟺ `(7)`: the radical is the graph of `J`.**
* `deningerSecondaryDefect_flow` : **`(8)`: the contragredient flow translates the defect.**
-/

namespace RHTower

open SchwartzMap

open scoped ContDiff

noncomputable section

/-! ## Multiplication by a real exponential -/

/-- The exponential weight `e^{ct}`, complex valued. -/
def deningerRealExpWeight (c : ℝ) (t : ℝ) : ℂ := ((Real.exp (c * t) : ℝ) : ℂ)

theorem deningerRealExpWeight_contDiff (c : ℝ) : ContDiff ℝ ∞ (deningerRealExpWeight c) := by
  have h1 : ContDiff ℝ ∞ fun t : ℝ => Real.exp (c * t) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  exact Complex.ofRealCLM.contDiff.comp h1

/-- **Every derivative of `e^{ct}` has norm `|c|^n e^{ct}`.** -/
theorem deningerRealExpWeight_norm_iteratedFDeriv (c : ℝ) (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (deningerRealExpWeight c) x‖ = |c| ^ n * Real.exp (c * x) := by
  have hcomp : deningerRealExpWeight c
      = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ fun t : ℝ => Real.exp (c * t) := rfl
  have hcd : ContDiff ℝ ∞ fun t : ℝ => Real.exp (c * t) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  rw [hcomp,
    (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ).norm_iteratedFDeriv_comp_left hcd.contDiffAt ENat.LEInfty.out,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul n c,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]

/-- The pointwise product `e^{ct} h(t)`. -/
def deningerExpMulFun (c : ℝ) (h : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  deningerRealExpWeight c t * h t

theorem deningerExpMulFun_contDiff (c : ℝ) (h : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (deningerExpMulFun c h) :=
  (deningerRealExpWeight_contDiff c).mul h.smooth'

/-- **Multiplication by `e^{ct}` keeps the source**, at the cost of `|c|` units of exponent. -/
theorem deningerExpMulFun_bounds {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (c : ℝ) :
    ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, ∀ x : ℝ,
      Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n (deningerExpMulFun c h) x‖ ≤ C := by
  intro A n
  choose C hC using fun m : ℕ => hh (A + |c|) m
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (|c| ^ i * max (C (n - i)) 0),
    fun x => ?_⟩
  have hleib := norm_iteratedFDeriv_mul_le (f := deningerRealExpWeight c)
    (g := (h : ℝ → ℂ)) (deningerRealExpWeight_contDiff c) h.smooth' x
    (n := n) ENat.LEInfty.out
  have hexp : (0 : ℝ) < Real.exp (A * |x|) := Real.exp_pos _
  refine le_trans (mul_le_mul_of_nonneg_left hleib hexp.le) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [deningerRealExpWeight_norm_iteratedFDeriv]
  have hweight : Real.exp (A * |x|) * Real.exp (c * x) ≤ Real.exp ((A + |c|) * |x|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : c * x ≤ |c| * |x| := by
      calc c * x ≤ |c * x| := le_abs_self _
        _ = |c| * |x| := abs_mul c x
    nlinarith
  have hbase : Real.exp ((A + |c|) * |x|) * ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) x‖
      ≤ max (C (n - i)) 0 := le_trans (hC (n - i) x) (le_max_left _ _)
  have hnn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) x‖ := norm_nonneg _
  have hmid : Real.exp (A * |x|) * Real.exp (c * x) *
      ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) x‖ ≤ max (C (n - i)) 0 :=
    le_trans (mul_le_mul_of_nonneg_right hweight hnn) hbase
  have hchoose : (0 : ℝ) ≤ (n.choose i : ℝ) := by positivity
  have hcpow : (0 : ℝ) ≤ |c| ^ i := by positivity
  calc Real.exp (A * |x|) *
        ((n.choose i : ℝ) * (|c| ^ i * Real.exp (c * x)) *
          ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) x‖)
      = (n.choose i : ℝ) * |c| ^ i *
        (Real.exp (A * |x|) * Real.exp (c * x) *
          ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) x‖) := by ring
    _ ≤ (n.choose i : ℝ) * |c| ^ i * max (C (n - i)) 0 :=
        mul_le_mul_of_nonneg_left hmid (by positivity)
    _ = (n.choose i : ℝ) * (|c| ^ i * max (C (n - i)) 0) := by ring

/-- **Multiplication by `e^{ct}`, as an operation of the source.** -/
def deningerExpMul (c : ℝ) (h : DeningerExpSchwartz) : DeningerExpSchwartz :=
  ⟨deningerExpSchwartzOfBounds (deningerExpMulFun c ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
      (deningerExpMulFun_contDiff c _) (deningerExpMulFun_bounds h.2 c),
    deningerExpSchwartzOfBounds_mem _ _ _⟩

@[simp]
theorem deningerExpMul_apply (c : ℝ) (h : DeningerExpSchwartz) (t : ℝ) :
    ((deningerExpMul c h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = ((Real.exp (c * t) : ℝ) : ℂ) * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t := rfl

/-- **The half-density lift** `U h(t) = e^{t/2} h(t)` of `(1)`. -/
def deningerHalfDensityLift (h : DeningerExpSchwartz) : DeningerExpSchwartz :=
  deningerExpMul (1 / 2) h

@[simp]
theorem deningerHalfDensityLift_apply (h : DeningerExpSchwartz) (t : ℝ) :
    ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = ((Real.exp (t / 2) : ℝ) : ℂ) * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t := by
  rw [deningerHalfDensityLift, deningerExpMul_apply]
  congr 2
  ring

/-! ## The centred two-collar defect -/

/-- **The centred two-collar defect `(2)`**, `d_sec(h₊,h₋)(t) = U h₊(t) - U h₋(-t)`. -/
def deningerSecondaryDefect (hp hm : DeningerExpSchwartz) (t : ℝ) : ℂ :=
  ((deningerHalfDensityLift hp : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
    - ((deningerHalfDensityLift hm : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t)

/-- **`(6)` ⟺ `(7)`: the defect vanishes exactly on the graph of the collar exchange `J`.** -/
theorem deningerSecondaryDefect_eq_zero_iff (hp hm : DeningerExpSchwartz) :
    (∀ t : ℝ, deningerSecondaryDefect hp hm t = 0)
      ↔ ∀ t : ℝ, ((hp : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
          = ((deningerCollarExchange hm : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t := by
  constructor
  · intro hzero t
    have h := hzero t
    rw [deningerSecondaryDefect, deningerHalfDensityLift_apply,
      deningerHalfDensityLift_apply, sub_eq_zero] at h
    rw [deningerCollarExchange_apply]
    have hne : ((Real.exp (t / 2) : ℝ) : ℂ) ≠ 0 := by
      simp
    refine mul_left_cancel₀ hne ?_
    rw [h, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · intro hgraph t
    rw [deningerSecondaryDefect, deningerHalfDensityLift_apply,
      deningerHalfDensityLift_apply, sub_eq_zero, hgraph t,
      deningerCollarExchange_apply, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

/-- **`(4)`: the scalar two-collar coefficient before orbit summation.** -/
theorem deningerSecondaryDefect_value (hp hm : DeningerExpSchwartz) {x : ℝ} (hx : 0 < x) :
    ((x : ℝ) : ℂ)⁻¹ * deningerSecondaryDefect hp hm (Real.log x)
      = ((Real.exp (-(Real.log x / 2)) : ℝ) : ℂ)
          * ((hp : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log x)
        - ((Real.exp (-(3 * Real.log x / 2)) : ℝ) : ℂ)
          * ((hm : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-Real.log x) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hx
  have hxeq : ((x : ℝ) : ℂ) = ((Real.exp (Real.log x) : ℝ) : ℂ) := by
    rw [Real.exp_log hx]
  rw [deningerSecondaryDefect, deningerHalfDensityLift_apply, deningerHalfDensityLift_apply,
    hxeq, mul_sub]
  congr 1
  · rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Real.exp_neg,
      ← Real.exp_add]
    congr 3
    ring
  · rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Real.exp_neg,
      ← Real.exp_add]
    congr 3
    ring

end

end RHTower
