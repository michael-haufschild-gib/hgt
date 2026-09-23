import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import GaloisForLFunctions.HTGeometry.ScalarTwoJetCalculus

/-!
# Twisted radial derivatives of rational-coefficient linear forms

A radial field carrying an envelope `E` with `E'/E = 2s/(r(r²−1))` has, for its coefficient `g`
(field `= E·g`), the twisted derivative `twist s g = g' + (2s/(r(r²−1))) g`: the plain derivative of
`E·g` is `E·twist s g`. Rational coefficients are written in Horner form over the monomial
denominator `r^p (r²−1)^q` (`ratCoef`); their derivative is explicit (`ratCoefDeriv`). The main
lemma `twist_linear` computes the twisted derivative of a linear form `∑ᵢ ratCoefᵢ · Xᵢ` in terms of
the twisted derivatives of the `Xᵢ`, and `twist_congr`/`twist_eventuallyEq_zero` transport the
twist along local equalities.
-/

namespace GaloisForLFunctions.HTGeometry.TwistedRadial

open Filter Topology GaloisForLFunctions.HTGeometry.ScalarTwoJet
noncomputable section

/-- Horner evaluation of a coefficient list. -/
def horner : List ℂ → ℂ → ℂ
  | [], _ => 0
  | c :: cs, x => c + x * horner cs x

/-- Formal derivative of the Horner form. -/
def hornerDeriv : List ℂ → ℂ → ℂ
  | [], _ => 0
  | _ :: cs, x => horner cs x + x * hornerDeriv cs x

theorem hasDerivAt_horner (cs : List ℂ) (x : ℂ) :
    HasDerivAt (horner cs) (hornerDeriv cs x) x := by
  induction cs with
  | nil => simpa [horner, hornerDeriv] using hasDerivAt_const x (0 : ℂ)
  | cons c cs ih =>
    have h := ((hasDerivAt_id x).mul ih).const_add c
    simp only [id, one_mul] at h
    simpa [horner, hornerDeriv] using h

/-- Real-variable Horner evaluation. -/
theorem hasDerivAt_horner_real (cs : List ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => horner cs r) (hornerDeriv cs r) r :=
  (hasDerivAt_horner cs r).comp_ofReal

/-- Rational coefficient `horner cs r / (r^p (r²−1)^q)`. -/
def ratCoef (cs : List ℂ) (p q : ℕ) (r : ℝ) : ℂ :=
  horner cs r / ((r : ℂ) ^ p * ((r : ℂ) ^ (2 : ℕ) - 1) ^ q)

/-- Its derivative, over the denominator `r^(p+1) (r²−1)^(q+1)`. -/
def ratCoefDeriv (cs : List ℂ) (p q : ℕ) (r : ℝ) : ℂ :=
  (hornerDeriv cs r * r * ((r : ℂ) ^ (2 : ℕ) - 1) -
      horner cs r * ((p : ℂ) * ((r : ℂ) ^ (2 : ℕ) - 1) + 2 * (q : ℂ) * (r : ℂ) ^ (2 : ℕ))) /
    ((r : ℂ) ^ (p + 1) * ((r : ℂ) ^ (2 : ℕ) - 1) ^ (q + 1))

theorem hasDerivAt_ratCoef (cs : List ℂ) (p q : ℕ) {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (hf : (r : ℂ) ^ (2 : ℕ) - 1 ≠ 0) :
    HasDerivAt (ratCoef cs p q) (ratCoefDeriv cs p q r) r := by
  have hR : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have hD : HasDerivAt (fun r : ℝ => (r : ℂ) ^ p * ((r : ℂ) ^ (2 : ℕ) - 1) ^ q)
      ((p : ℂ) * (r : ℂ) ^ (p - 1) * 1 * ((r : ℂ) ^ (2 : ℕ) - 1) ^ q +
        (r : ℂ) ^ p * ((q : ℂ) * ((r : ℂ) ^ (2 : ℕ) - 1) ^ (q - 1) * ((2 : ℂ) * (r : ℂ) ^ (2 - 1) * 1 - 0))) r :=
    (hR.pow p).mul (((hR.pow 2).sub (hasDerivAt_const r (1 : ℂ))).pow q)
  have hden : (r : ℂ) ^ p * ((r : ℂ) ^ (2 : ℕ) - 1) ^ q ≠ 0 := mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hf)
  have h := (hasDerivAt_horner_real cs r).div hD hden
  refine h.congr_deriv ?_
  unfold ratCoefDeriv
  rcases p with _ | p <;> rcases q with _ | q
  all_goals simp only [Nat.cast_zero, zero_mul, Nat.cast_succ, Nat.succ_sub_one, pow_zero, Nat.zero_sub]
  all_goals field_simp
  all_goals ring

/-- The twisted radial derivative `g' + (2s/(r(r²−1))) g`. -/
def twist (s : ℂ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv g r + 2 * s / ((r : ℂ) * ((r : ℂ) ^ (2 : ℕ) - 1)) * g r

/-- Iterated twisted derivative. -/
def twistIter (s : ℂ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, g => g
  | k + 1, g => twist s (twistIter s k g)

@[simp] theorem twistIter_zero (s : ℂ) (g : ℝ → ℂ) : twistIter s 0 g = g := rfl

@[simp] theorem twistIter_succ (s : ℂ) (k : ℕ) (g : ℝ → ℂ) :
    twistIter s (k + 1) g = twist s (twistIter s k g) := rfl

theorem twist_congr (s : ℂ) {g h : ℝ → ℂ} {r : ℝ} (hgh : g =ᶠ[𝓝 r] h) :
    twist s g r = twist s h r := by
  unfold twist
  rw [hgh.deriv_eq, hgh.eq_of_nhds]

theorem twist_eventuallyEq_zero (s : ℂ) {g : ℝ → ℂ} {r : ℝ} (hg : g =ᶠ[𝓝 r] fun _ => 0) :
    twist s g r = 0 := by
  rw [twist_congr s hg]
  simp [twist]

/-- Twisted derivative of a rational-coefficient linear form. -/
theorem twist_linear (s : ℂ) {n : ℕ} (cs : Fin n → List ℂ) (p q : Fin n → ℕ) (X : Fin n → ℝ → ℂ)
    {r : ℝ} (hr : (r : ℂ) ≠ 0) (hf : (r : ℂ) ^ (2 : ℕ) - 1 ≠ 0)
    (hX : ∀ i, DifferentiableAt ℝ (X i) r) :
    twist s (fun r => ∑ i, ratCoef (cs i) (p i) (q i) r * X i r) r =
      ∑ i, (ratCoefDeriv (cs i) (p i) (q i) r * X i r +
        ratCoef (cs i) (p i) (q i) r * twist s (X i) r) := by
  have hd : HasDerivAt (fun r => ∑ i, ratCoef (cs i) (p i) (q i) r * X i r)
      (∑ i, (ratCoefDeriv (cs i) (p i) (q i) r * X i r +
        ratCoef (cs i) (p i) (q i) r * deriv (X i) r)) r :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_ratCoef (cs i) (p i) (q i) hr hf).mul (hX i).hasDerivAt
  unfold twist
  rw [hd.deriv, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## Smoothness on the exterior -/

open Set
open scoped ContDiff

@[fun_prop] theorem contDiff_ofReal_real : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
@[fun_prop] theorem contDiff_horner (cs : List ℂ) : ContDiff ℝ ∞ (fun r : ℝ => horner cs r) := by
  induction cs with
  | nil => simpa [horner] using contDiff_const
  | cons c cs ih =>
    simp only [horner]
    exact contDiff_const.add (contDiff_ofReal_real.mul ih)
theorem contDiffOn_ratCoef (cs : List ℂ) (p q : ℕ) : ContDiffOn ℝ ∞ (ratCoef cs p q) (Ioi 1) := by
  have h0 : ∀ r ∈ Ioi (1 : ℝ), (r : ℂ) ^ p * ((r : ℂ) ^ (2 : ℕ) - 1) ^ q ≠ 0 := by
    intro r hr
    have hr1 : (1 : ℝ) < r := hr
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (by linarith : r ≠ 0)))
      (pow_ne_zero _ (by exact_mod_cast (by nlinarith : r ^ (2 : ℕ) - 1 ≠ 0)))
  have hden : ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ) ^ p * ((r : ℂ) ^ (2 : ℕ) - 1) ^ q) (Ioi 1) := by fun_prop
  have hinv : ContDiffOn ℝ ∞ (fun r : ℝ => ((r : ℂ) ^ p * ((r : ℂ) ^ (2 : ℕ) - 1) ^ q)⁻¹) (Ioi 1) :=
    hden.inv h0
  have hnum : ContDiffOn ℝ ∞ (fun r : ℝ => horner cs r) (Ioi 1) := (contDiff_horner cs).contDiffOn
  have := hnum.mul hinv
  refine this.congr ?_
  intro r _
  simp [ratCoef, div_eq_mul_inv]
theorem contDiffOn_twistWeight (s : ℂ) : ContDiffOn ℝ ∞ (fun r : ℝ => 2 * s / ((r : ℂ) * ((r : ℂ) ^ (2 : ℕ) - 1))) (Ioi 1) := by
  have h0 : ∀ r ∈ Ioi (1 : ℝ), (r : ℂ) * ((r : ℂ) ^ (2 : ℕ) - 1) ≠ 0 := by
    intro r hr
    have hr1 : (1 : ℝ) < r := hr
    exact mul_ne_zero (by exact_mod_cast (by linarith : r ≠ 0)) (by exact_mod_cast (by nlinarith : r ^ (2 : ℕ) - 1 ≠ 0))
  have hden : ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ) * ((r : ℂ) ^ (2 : ℕ) - 1)) (Ioi 1) := by fun_prop
  have := (contDiffOn_const (c := 2 * s)).mul (hden.inv h0)
  refine this.congr ?_
  intro r _
  simp [div_eq_mul_inv]
theorem contDiffOn_twist (s : ℂ) {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 1)) :
    ContDiffOn ℝ ∞ (twist s g) (Ioi 1) :=
  (hg.deriv_of_isOpen isOpen_Ioi (by simp)).add ((contDiffOn_twistWeight s).mul hg)
theorem contDiffOn_twistIter (s : ℂ) {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 1)) (k : ℕ) :
    ContDiffOn ℝ ∞ (twistIter s k g) (Ioi 1) := by
  induction k with
  | zero => simpa using hg
  | succ k ih => exact contDiffOn_twist s ih
theorem differentiableAt_twistIter (s : ℂ) {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 1)) (k : ℕ)
    {r : ℝ} (hr : 1 < r) : DifferentiableAt ℝ (twistIter s k g) r :=
  ((contDiffOn_twistIter s hg k).differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hr)

/-! ## Regularity from a linear second-order equation -/

/-- Smoothness from a linear second-order ODE with smooth coefficients on an open set: a `C¹`
function whose derivative is differentiable with `y'' = a y' + b y + c` is `C^∞`. -/
theorem contDiffOn_of_linear_ode {s : Set ℝ} (hs : IsOpen s) (y y1 a b c : ℝ → ℂ)
    (ha : ContDiffOn ℝ ∞ a s) (hb : ContDiffOn ℝ ∞ b s) (hc : ContDiffOn ℝ ∞ c s)
    (hy : ∀ x ∈ s, HasDerivAt y (y1 x) x)
    (hy1 : ∀ x ∈ s, HasDerivAt y1 (a x * y1 x + b x * y x + c x) x) :
    ContDiffOn ℝ ∞ y s := by
  have hdy : ∀ x ∈ s, deriv y x = y1 x := fun x hx => (hy x hx).deriv
  have hdy1 : ∀ x ∈ s, deriv y1 x = a x * y1 x + b x * y x + c x := fun x hx => (hy1 x hx).deriv
  have hdiff : DifferentiableOn ℝ y s := fun x hx => (hy x hx).differentiableAt.differentiableWithinAt
  have hdiff1 : DifferentiableOn ℝ y1 s := fun x hx => (hy1 x hx).differentiableAt.differentiableWithinAt
  -- key: for every n, y and y1 are C^n on s
  have key : ∀ n : ℕ, ContDiffOn ℝ n y s ∧ ContDiffOn ℝ n y1 s := by
    intro n
    induction n with
    | zero =>
      exact ⟨contDiffOn_zero.mpr hdiff.continuousOn, contDiffOn_zero.mpr hdiff1.continuousOn⟩
    | succ n ih =>
      have h1 : ContDiffOn ℝ (n + 1) y1 s := by
        rw [contDiffOn_succ_iff_deriv_of_isOpen hs]
        refine ⟨hdiff1, fun h => (WithTop.coe_ne_top h).elim, ?_⟩
        have : ContDiffOn ℝ n (fun x => a x * y1 x + b x * y x + c x) s :=
          ((ha.of_le (WithTop.coe_le_coe.mpr le_top)).mul ih.2).add ((hb.of_le (WithTop.coe_le_coe.mpr le_top)).mul ih.1) |>.add (hc.of_le (WithTop.coe_le_coe.mpr le_top))
        exact this.congr fun x hx => hdy1 x hx
      have h0 : ContDiffOn ℝ (n + 1) y s := by
        rw [contDiffOn_succ_iff_deriv_of_isOpen hs]
        refine ⟨hdiff, fun h => (WithTop.coe_ne_top h).elim, ?_⟩
        exact ih.2.congr fun x hx => hdy x hx
      exact ⟨h0, h1⟩
  exact contDiffOn_infty.mpr fun n => (key n).1

/-! ## Jets of twisted radial functions -/

/-- Derivative of the twisted derivative: `(twist s g)' = g'' + tw' g + tw g'`. -/
theorem hasDerivAt_twist (s : ℂ) {g g1 : ℝ → ℂ} {g2 : ℂ} {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (hf : (r : ℂ) ^ (2 : ℕ) - 1 ≠ 0)
    (hg : ∀ᶠ r' in 𝓝 r, HasDerivAt g (g1 r') r') (hg1 : HasDerivAt g1 g2 r) :
    HasDerivAt (twist s g)
      (g2 + (-(2 * s * (3 * (r : ℂ) ^ (2 : ℕ) - 1)) / ((r : ℂ) ^ (2 : ℕ) * ((r : ℂ) ^ (2 : ℕ) - 1) ^ (2 : ℕ))) * g r +
        2 * s / ((r : ℂ) * ((r : ℂ) ^ (2 : ℕ) - 1)) * g1 r) r := by
  have hdg : deriv g =ᶠ[𝓝 r] g1 := hg.mono fun r' h => h.deriv
  have h1 : HasDerivAt (deriv g) g2 r := hg1.congr_of_eventuallyEq hdg
  have hR : HasDerivAt (fun r' : ℝ => (r' : ℂ)) 1 r := by simpa using (hasDerivAt_id r).ofReal_comp
  have htw : HasDerivAt (fun r' : ℝ => 2 * s / ((r' : ℂ) * ((r' : ℂ) ^ (2 : ℕ) - 1)))
      (-(2 * s * (3 * (r : ℂ) ^ (2 : ℕ) - 1)) / ((r : ℂ) ^ (2 : ℕ) * ((r : ℂ) ^ (2 : ℕ) - 1) ^ (2 : ℕ))) r := by
    have h := (hasDerivAt_const r (2 * s)).div (hR.mul ((hR.pow 2).sub (hasDerivAt_const r (1 : ℂ))))
      (mul_ne_zero hr hf)
    refine h.congr_deriv ?_
    norm_num
    field_simp
    ring
  have h := h1.add (htw.mul hg.self_of_nhds)
  convert h using 1
  all_goals first | rfl | ring
/-- The two-jet of a radial function lifted to spacetime through the radial coordinate. -/
theorem ofField_radialLift {g g1 : ℝ → ℂ} {g2 : ℂ} {x : Fin 4 → ℝ}
    (hg : ∀ᶠ r in 𝓝 (x 1), HasDerivAt g (g1 r) r) (hg1 : HasDerivAt g1 g2 (x 1)) :
    ofField (fun y => g (y 1)) x =
      ⟨g (x 1), fun i => if i = 1 then g1 (x 1) else 0,
        fun i j => if i = 1 ∧ j = 1 then g2 else 0⟩ := by
  have hproj : ∀ y : Fin 4 → ℝ, HasFDerivAt (fun y : Fin 4 → ℝ => y 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1) y :=
    fun y => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).hasFDerivAt
  have hfirst : ∀ y : Fin 4 → ℝ, HasDerivAt g (g1 (y 1)) (y 1) → ∀ i,
      coordDeriv i (fun y => g (y 1)) y = if i = 1 then g1 (y 1) else 0 := by
    intro y hy i
    have hd := hy.hasFDerivAt.comp y (hproj y)
    simp only [coordDeriv, Function.comp_def] at hd ⊢
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Pi.single_apply]
    by_cases hi : i = 1
    · subst hi; simp
    · simp [hi, Ne.symm hi]
  ext i j
  · rfl
  · exact hfirst x hg.self_of_nhds i
  · have heq : coordDeriv j (fun y => g (y 1)) =ᶠ[𝓝 x] fun y => if j = 1 then g1 (y 1) else 0 := by
      have : ∀ᶠ y in 𝓝 x, HasDerivAt g (g1 (y 1)) (y 1) :=
        (continuous_apply 1).continuousAt.preimage_mem_nhds hg
      filter_upwards [this] with y hy
      exact hfirst y hy j
    change coordDeriv i (coordDeriv j (fun y => g (y 1))) x = _
    rw [show coordDeriv i (coordDeriv j (fun y => g (y 1))) x =
      fderiv ℝ (fun y => if j = 1 then g1 (y 1) else 0) x (Pi.single i 1) from by
        simp only [coordDeriv]; rw [heq.fderiv_eq]]
    by_cases hj : j = 1
    · subst hj
      have hd := hg1.hasFDerivAt.comp x (hproj x)
      simp only [Function.comp_def] at hd
      simp only [if_true]
      rw [hd.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Pi.single_apply]
      by_cases hi : i = 1
      · subst hi; simp
      · simp [hi, Ne.symm hi]
    · simp [hj]
end
end GaloisForLFunctions.HTGeometry.TwistedRadial
