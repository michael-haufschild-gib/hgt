import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv
import GaloisForLFunctions.RHTower.WeilFunctionalLineIntegral

/-!
# The logarithmic derivative of a symmetric order-one function as a sum over zero pairs

Let `E` be entire with `E(1 − s) = ε E(s)` (`ε ≠ 0`), `E(2) ≠ 0`, and the order-one envelope
`‖E(s)‖ ≤ exp(C (1 + ‖s‖) log(2 + ‖s‖))`.  Index the zeros of `E` with multiplicity by `q ↦ ρ_q`.
Then at every `s` with `E(s) ≠ 0`

`E'/E(s) = ½ Σ_q (1/(s − ρ_q) + 1/(s − (1 − ρ_q)))`  (`hasSum_logDeriv_zeroPairs`),

the series converging absolutely.

**Proof.**  Hadamard's factorization of `f(z) = E(z + 2)` gives
`E'/E(s) = a + Σ_q (1/(s − ρ_q) + 1/(ρ_q − 2))`.  The functional equation gives
`E'/E(1 − s) = −E'/E(s)`, and subtracting the two expansions cancels both `a` and the convergence
factors `1/(ρ_q − 2)` term by term.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

noncomputable section

namespace RHTower.CompletionZeroPairs

open OrderOneHadamard WeilLineIntegral

variable {f : ℂ → ℂ}

theorem countable_zeroCopy (hf : AnalyticOnNhd ℂ f univ) : Countable (ZeroCopy f) := by
  have hS : Countable (ZeroSupport f) := by
    have hcov : (univ : Set (ZeroSupport f)) = ⋃ n : ℕ, {w : ZeroSupport f | ‖(w : ℂ)‖ ≤ n} := by
      refine (eq_univ_of_forall fun w => mem_iUnion.mpr ?_).symm
      obtain ⟨n, hn⟩ := exists_nat_ge ‖(w : ℂ)‖
      exact ⟨n, hn⟩
    have hc : (univ : Set (ZeroSupport f)).Countable := by
      rw [hcov]
      exact countable_iUnion fun n => (finite_zeroSupport_ball hf n).countable
    exact countable_univ_iff.mp hc
  infer_instance

theorem apply_zeroCopyPoint (hf : AnalyticOnNhd ℂ f univ) (q : ZeroCopy f) :
    f (zeroCopyPoint f q) = 0 := by
  by_contra h
  have hord : analyticOrderAt f (zeroCopyPoint f q) = 0 :=
    (hf _ (mem_univ _)).analyticOrderAt_eq_zero.mpr h
  apply q.1.2
  change (MeromorphicOn.divisor f univ) (zeroCopyPoint f q) = 0
  rw [divisor_univ_eq_analyticOrder hf, hord]
  rfl

/-- The order-one envelope survives the shift `z ↦ z + 2`. -/
theorem bound_shift {E : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖))) (z : ℂ) :
    ‖E (z + 2)‖ ≤ Real.exp (6 * C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  refine (hbound (z + 2)).trans (Real.exp_le_exp.mpr ?_)
  have hn : ‖z + 2‖ ≤ ‖z‖ + 2 := by
    calc ‖z + 2‖ ≤ ‖z‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + 2 := by simp
  have hz := norm_nonneg z
  have hl0 : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith)
  have hl : Real.log (2 + ‖z + 2‖) ≤ 2 * Real.log (2 + ‖z‖) := by
    rw [← Real.log_rpow (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    norm_num
    nlinarith
  have h1 : 1 + ‖z + 2‖ ≤ 3 * (1 + ‖z‖) := by linarith
  calc C * (1 + ‖z + 2‖) * Real.log (2 + ‖z + 2‖)
      ≤ C * (3 * (1 + ‖z‖)) * (2 * Real.log (2 + ‖z‖)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) hl
          (Real.log_nonneg (by linarith [norm_nonneg (z + 2)])) (by positivity)
    _ = 6 * C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by ring

/-- `E'/E(1 − s) = −E'/E(s)` under `E(1 − s) = ε E(s)`. -/
theorem logDeriv_one_sub {E : ℂ → ℂ} (hE : Differentiable ℂ E) {ε : ℂ} (hε : ε ≠ 0)
    (hsym : ∀ s, E (1 - s) = ε * E s) (s : ℂ) : logDeriv E (1 - s) = -logDeriv E s := by
  have h1 : logDeriv (fun s => E (1 - s)) s = logDeriv E (1 - s) * (-1) := by
    have := logDeriv_comp (f := E) (g := fun s : ℂ => 1 - s) (x := s) (hE _)
      ((differentiableAt_const _).sub differentiableAt_id)
    simp only [Function.comp_def] at this
    rw [this]
    congr 1
    simp
  have h2 : logDeriv (fun s => E (1 - s)) s = logDeriv E s := by
    rw [show (fun s => E (1 - s)) = fun s => ε * E s from funext hsym]
    exact logDeriv_const_mul s ε hε
  rw [h2] at h1
  linear_combination h1

/-- **The logarithmic derivative as a sum over zero pairs.** -/
theorem hasSum_logDeriv_zeroPairs {E : ℂ → ℂ} (hE : Differentiable ℂ E) {ε : ℂ} (hε : ε ≠ 0)
    (hsym : ∀ s, E (1 - s) = ε * E s) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖))) (h2 : E 2 ≠ 0)
    {s : ℂ} (hs : E s ≠ 0) :
    HasSum (fun q : ZeroCopy (fun z => E (z + 2)) =>
        (1 / 2 : ℂ) * gPair (zeroCopyPoint (fun z => E (z + 2)) q + 2) s) (logDeriv E s) := by
  set f : ℂ → ℂ := fun z => E (z + 2) with hfdef
  have hfd : Differentiable ℂ f := hE.comp (differentiable_id.add_const 2)
  have hf : AnalyticOnNhd ℂ f univ := hfd.differentiableOn.analyticOnNhd isOpen_univ
  have hf0 : f 0 ≠ 0 := by simpa [hfdef] using h2
  have hford : ∀ z, analyticOrderAt f z ≠ ⊤ := fun z =>
    hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ z)
      (by rw [(hf 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr hf0]; exact ENat.zero_ne_top)
  have hC6 : 0 ≤ 6 * C := by positivity
  have hbf := bound_shift hC hbound
  obtain ⟨a, b, hab⟩ := exists_expAffine_mul_hadamardProduct hC6 hf hf0 hford hbf
  have hsum := summable_inv_sq_zeroCopyPoint hC6 hf hf0 hbf
  have hane := zeroCopyPoint_ne_zero hf hf0
  set P := hadamardProduct f with hP
  have hPd : Differentiable ℂ P := fun z =>
    (hadamardProduct_analytic hf hf0 hsum z (mem_univ z)).differentiableAt
  -- the expansion of `f'/f`
  have hlog : ∀ w : ℂ, f w ≠ 0 →
      logDeriv f w = a + ∑' q, ((w - zeroCopyPoint f q)⁻¹ + (zeroCopyPoint f q)⁻¹) := by
    intro w hw
    have hwq : ∀ q, w ≠ zeroCopyPoint f q := fun q h => hw (h ▸ apply_zeroCopyPoint hf q)
    have hPw : P w ≠ 0 := by
      intro h0
      apply hw
      rw [hab w, h0, mul_zero]
    have hfeq : f = fun z => Complex.exp (a * z + b) * P z := funext hab
    have hlf : logDeriv f w = logDeriv (fun z => Complex.exp (a * z + b) * P z) w := by
      rw [hfeq]
    rw [hlf, logDeriv_mul (f := fun z => Complex.exp (a * z + b)) (g := P) w
      (Complex.exp_ne_zero _) hPw (by fun_prop) (hPd w)]
    rw [hP, hadamardProduct, logDeriv_canonicalProductE1Indexed hane hsum hwq]
    congr 1
    have hd : HasDerivAt (fun z => Complex.exp (a * z + b)) (Complex.exp (a * w + b) * a) w := by
      have := ((hasDerivAt_id w).const_mul a).add_const b
      simpa using this.cexp
    rw [logDeriv_apply, hd.deriv]
    field_simp
  -- transport to `E`
  have hEf : ∀ w : ℂ, logDeriv E w = logDeriv f (w - 2) := by
    intro w
    have hcomp : E = f ∘ fun w => w - 2 := by
      funext w
      simp [hfdef]
    rw [hcomp, logDeriv_comp (hfd _) (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - 2) w)]
    simp
  have hs' : E (1 - s) ≠ 0 := by rw [hsym]; exact mul_ne_zero hε hs
  have hf1 : f (s - 2) ≠ 0 := by simpa [hfdef] using hs
  have hf2 : f (1 - s - 2) ≠ 0 := by simpa [hfdef] using hs'
  have hq1 : ∀ q, s - 2 ≠ zeroCopyPoint f q := fun q h => hf1 (h ▸ apply_zeroCopyPoint hf q)
  have hq2 : ∀ q, 1 - s - 2 ≠ zeroCopyPoint f q := fun q h => hf2 (h ▸ apply_zeroCopyPoint hf q)
  have hT1 : Summable fun q => (s - 2 - zeroCopyPoint f q)⁻¹ + (zeroCopyPoint f q)⁻¹ := by
    refine (summable_canonicalProductE1LogDerivTerm hane hsum hq1).neg.congr fun q => ?_
    have h1 : s - 2 - zeroCopyPoint f q ≠ 0 := sub_ne_zero.mpr (hq1 q)
    have h2 : zeroCopyPoint f q - (s - 2) ≠ 0 := sub_ne_zero.mpr (hq1 q).symm
    rw [show zeroCopyPoint f q - (s - 2) = -(s - 2 - zeroCopyPoint f q) by ring, inv_neg]
    ring
  have hT2 : Summable fun q => (1 - s - 2 - zeroCopyPoint f q)⁻¹ + (zeroCopyPoint f q)⁻¹ := by
    refine (summable_canonicalProductE1LogDerivTerm hane hsum hq2).neg.congr fun q => ?_
    rw [show zeroCopyPoint f q - (1 - s - 2) = -(1 - s - 2 - zeroCopyPoint f q) by ring, inv_neg]
    ring
  have hE1 := hEf s
  have hE2 := hEf (1 - s)
  rw [hlog _ hf1] at hE1
  rw [hlog _ hf2, logDeriv_one_sub hE hε hsym] at hE2
  have hdiff := (hT1.hasSum.sub hT2.hasSum).mul_left (1 / 2 : ℂ)
  have hval : logDeriv E s = (1 / 2 : ℂ) *
      ((∑' q, ((s - 2 - zeroCopyPoint f q)⁻¹ + (zeroCopyPoint f q)⁻¹)) -
        ∑' q, ((1 - s - 2 - zeroCopyPoint f q)⁻¹ + (zeroCopyPoint f q)⁻¹)) := by
    linear_combination (1 / 2 : ℂ) * hE1 - (1 / 2 : ℂ) * hE2
  rw [hval]
  refine hdiff.congr_fun fun q => ?_
  simp only [gPair]
  have e1 : s - 2 - zeroCopyPoint f q = s - (zeroCopyPoint f q + 2) := by ring
  have e2 : 1 - s - 2 - zeroCopyPoint f q = -(s - (1 - (zeroCopyPoint f q + 2))) := by ring
  rw [e1, e2, inv_neg]
  simp only [one_div]
  ring

/-! ## Reflection of the zero divisor -/

/-- Under `f(c − z) = ε f(z)`, `ε ≠ 0`, the divisor is symmetric about `c/2`. -/
theorem divisor_reflect (hf : AnalyticOnNhd ℂ f univ) {c ε : ℂ} (hε : ε ≠ 0)
    (hsym : ∀ z, f (c - z) = ε * f z) (w : ℂ) :
    (MeromorphicOn.divisor f univ) (c - w) = (MeromorphicOn.divisor f univ) w := by
  have hg_an : AnalyticAt ℂ (fun z : ℂ => c - z) w := by fun_prop
  have hg_deriv : deriv (fun z : ℂ => c - z) w ≠ 0 := by
    have hg' : HasDerivAt (fun z : ℂ => c - z) (-1) w := by
      simpa using (hasDerivAt_id w).const_sub c
    rw [hg'.deriv]
    exact neg_ne_zero.mpr one_ne_zero
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := f) hg_an hg_deriv
  have hfun : f ∘ (fun z : ℂ => c - z) = (fun _ : ℂ => ε) * f := funext fun z => hsym z
  rw [hfun, analyticOrderAt_mul analyticAt_const (hf w (mem_univ w)),
    (analyticAt_const (v := ε)).analyticOrderAt_eq_zero.mpr hε, zero_add] at hcomp
  rw [divisor_univ_eq_analyticOrder hf, divisor_univ_eq_analyticOrder hf, ← hcomp]

/-- Reflection `w ↦ c − w` of the zero-divisor support. -/
def zeroSupportReflect (hf : AnalyticOnNhd ℂ f univ) {c ε : ℂ} (hε : ε ≠ 0)
    (hsym : ∀ z, f (c - z) = ε * f z) : ZeroSupport f ≃ ZeroSupport f where
  toFun w := ⟨c - (w : ℂ), by
    apply Function.mem_support.mpr
    rw [divisor_reflect hf hε hsym]
    exact Function.mem_support.mp w.2⟩
  invFun w := ⟨c - (w : ℂ), by
    apply Function.mem_support.mpr
    rw [divisor_reflect hf hε hsym]
    exact Function.mem_support.mp w.2⟩
  left_inv w := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

/-- Reflection lifted to the multiplicity copies. -/
def zeroCopyReflect (hf : AnalyticOnNhd ℂ f univ) {c ε : ℂ} (hε : ε ≠ 0)
    (hsym : ∀ z, f (c - z) = ε * f z) : ZeroCopy f ≃ ZeroCopy f :=
  Equiv.sigmaCongr (zeroSupportReflect hf hε hsym) (fun w => Equiv.cast (by
    change Fin ((MeromorphicOn.divisor f univ) ((w : ZeroSupport f) : ℂ)).toNat =
      Fin ((MeromorphicOn.divisor f univ) (c - ((w : ZeroSupport f) : ℂ))).toNat
    rw [divisor_reflect hf hε hsym]))

theorem zeroCopyPoint_reflect (hf : AnalyticOnNhd ℂ f univ) {c ε : ℂ} (hε : ε ≠ 0)
    (hsym : ∀ z, f (c - z) = ε * f z) (q : ZeroCopy f) :
    zeroCopyPoint f (zeroCopyReflect hf hε hsym q) = c - zeroCopyPoint f q := rfl

/-- The zeros of `E` with `E(1 − s) = ε E(s)`, indexed through `f(z) = E(z + 2)`, are permuted by
`ρ ↦ 1 − ρ`. -/
theorem exists_reflect_zeroCopy {E : ℂ → ℂ} (hE : Differentiable ℂ E) {ε : ℂ} (hε : ε ≠ 0)
    (hsym : ∀ s, E (1 - s) = ε * E s) :
    ∃ σ : ZeroCopy (fun z => E (z + 2)) ≃ ZeroCopy (fun z => E (z + 2)), ∀ q,
      zeroCopyPoint (fun z => E (z + 2)) (σ q) + 2 =
        1 - (zeroCopyPoint (fun z => E (z + 2)) q + 2) := by
  have hf : AnalyticOnNhd ℂ (fun z => E (z + 2)) univ :=
    (hE.comp (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ
  have hsym' : ∀ z, (fun z => E (z + 2)) (-3 - z) = ε * (fun z => E (z + 2)) z := by
    intro z
    simp only
    rw [← hsym (z + 2)]
    congr 1
    ring
  refine ⟨zeroCopyReflect hf hε hsym', fun q => ?_⟩
  rw [zeroCopyPoint_reflect]
  ring

end RHTower.CompletionZeroPairs
