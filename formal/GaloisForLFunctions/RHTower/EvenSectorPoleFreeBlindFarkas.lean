import GaloisForLFunctions.RHTower.EvenSectorPolarRigidity

/-!
# Farkas duality for even pole-free Weil positivity

Even pole-free tests reach every node `log n`, `n ≥ 2`, with either sign:
* `q(x − L/2) + q(x + L/2)` with the even pole-free profile `q` (`evenPolarNodeTest`), node value
  `+2‖q‖²/√n`;
* `o(x − L/2) − o(x + L/2)` with the odd pole-free profile
  `o = ((φ(· − 2r) − φ(· + 2r)) − κ(φ(· − r) − φ(· + r)))/(1 + κ)`, `κ = 2 cosh(r/2)`
  (`evenPolarMinusTest`), an even pole-free test with node value `−2‖o‖²/√n`.

**Theorem** (`exists_weilPositiveEvenPolar_iff`).  Some real weights are Weil-positive on all even
tests with `f̂(i/2) = 0` iff the archimedean energy is nonnegative on every nonnegative combination
of autocorrelations of such tests that vanishes at every `±log n`, `n ≥ 2`
(`PrimeBlindPositiveEvenPolar`).

Under RH, `Λ` is such a weight system.  Conversely, a certificate bounded below forces RH
(`riemannHypothesis_of_weilPositiveEvenPolar_of_ge`).  So pole-free even blind positivity is
RH-equivalent exactly when every even pole-free positive weight system can be chosen bounded below.
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided SeparatedBump

/-! ## The odd pole-free profile -/

/-- `κ = 2 cosh(r/2)`. -/
def oddPolarCoef (j : ℕ) : ℝ := 2 * Real.cosh ((nodeBump j).rOut / 2)

theorem oddPolarCoef_pos (j : ℕ) : 0 < oddPolarCoef j := by
  unfold oddPolarCoef; have := Real.cosh_pos ((nodeBump j).rOut / 2); positivity

/-- The odd pole-free profile `((φ(v − 2r) − φ(v + 2r)) − κ(φ(v − r) − φ(v + r)))/(1 + κ)`. -/
def oddPolarProfile (j : ℕ) (v : ℝ) : ℝ :=
  ((nodeBump j (v - 2 * (nodeBump j).rOut) - nodeBump j (v + 2 * (nodeBump j).rOut)) -
    oddPolarCoef j * (nodeBump j (v - (nodeBump j).rOut) - nodeBump j (v + (nodeBump j).rOut))) /
    (1 + oddPolarCoef j)

theorem contDiff_oddPolarProfile (j : ℕ) : ContDiff ℝ 2 (oddPolarProfile j) := by
  have h1 : ∀ c : ℝ, ContDiff ℝ 2 fun v => nodeBump j (v - c) := fun c =>
    (nodeBump j).contDiff.comp (contDiff_id.sub contDiff_const)
  have h2 : ∀ c : ℝ, ContDiff ℝ 2 fun v => nodeBump j (v + c) := fun c =>
    (nodeBump j).contDiff.comp (contDiff_id.add contDiff_const)
  exact (((h1 _).sub (h2 _)).sub (contDiff_const.mul ((h1 _).sub (h2 _)))).div_const _

theorem oddPolarProfile_eq_zero (j : ℕ) {u : ℝ} (hu : 6 * (nodeBump j).rOut / 2 < |u|) :
    oddPolarProfile j u = 0 := by
  have hr := (nodeBump j).rOut_pos
  set r := (nodeBump j).rOut
  have key : ∀ c : ℝ, 0 ≤ c → c ≤ 2 * r → r ≤ |u - c| ∧ r ≤ |u + c| := fun c hc0 hc2 => by
    have h1 := abs_sub_abs_le_abs_sub u c
    have h2 := abs_sub_abs_le_abs_sub u (-c)
    rw [abs_of_nonneg hc0] at h1
    rw [abs_neg, abs_of_nonneg hc0, sub_neg_eq_add] at h2
    constructor <;> linarith
  obtain ⟨a1, a2⟩ := key (2 * r) (by linarith) le_rfl
  obtain ⟨b1, b2⟩ := key r hr.le (by linarith)
  unfold oddPolarProfile
  rw [nodeBump_eq_zero j a1, nodeBump_eq_zero j a2, nodeBump_eq_zero j b1, nodeBump_eq_zero j b2]
  ring

/-- The odd profile is nonzero at `2r`. -/
theorem oddPolarProfile_two_r (j : ℕ) :
    oddPolarProfile j (2 * (nodeBump j).rOut) = 1 / (1 + oddPolarCoef j) := by
  have hr := (nodeBump j).rOut_pos
  set r := (nodeBump j).rOut
  unfold oddPolarProfile
  rw [sub_self, nodeBump_zero, nodeBump_eq_zero j (u := 2 * r + 2 * r)
    (by rw [abs_of_pos (by linarith)]; linarith), nodeBump_eq_zero j (u := 2 * r - r)
    (by rw [abs_of_pos (by linarith)]; linarith), nodeBump_eq_zero j (u := 2 * r + r)
    (by rw [abs_of_pos (by linarith)]; linarith)]
  ring

theorem integral_oddPolarProfile_sq_pos (j : ℕ) : 0 < ∫ u, oddPolarProfile j u ^ 2 := by
  have hk := oddPolarCoef_pos j
  refine integral_sq_pos_of (contDiff_oddPolarProfile j).continuous
    (fun u hu => oddPolarProfile_eq_zero j hu) (v := 2 * (nodeBump j).rOut) ?_
  rw [oddPolarProfile_two_r]
  positivity

theorem oddPolarProfileC_eq (j : ℕ) :
    (fun v => (oddPolarProfile j v : ℂ)) = fun v => ∑ k : Fin 4,
      (![1 / (1 + oddPolarCoef j), -(1 / (1 + oddPolarCoef j)),
        -(oddPolarCoef j / (1 + oddPolarCoef j)), oddPolarCoef j / (1 + oddPolarCoef j)] k : ℂ) *
        (fun w => (nodeBump j w : ℂ)) (v - ![2 * (nodeBump j).rOut, -(2 * (nodeBump j).rOut),
          (nodeBump j).rOut, -(nodeBump j).rOut] k) := by
  have hk : (1 : ℂ) + oddPolarCoef j ≠ 0 := by
    have := oddPolarCoef_pos j; exact_mod_cast (show (1 : ℝ) + oddPolarCoef j ≠ 0 by linarith)
  funext v
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, oddPolarProfile, sub_neg_eq_add]
  push_cast
  field_simp
  ring

/-- **The odd profile is pole-free.** -/
theorem paperFT_oddPolarProfile_I_div_two (j : ℕ) :
    paperFT (fun v => (oddPolarProfile j v : ℂ)) (I / 2) = 0 := by
  rw [oddPolarProfileC_eq, paperFT_sum_translate Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j)]
  set r := (nodeBump j).rOut with hr
  set κ := oddPolarCoef j with hκ
  have hk1 : 0 < 1 + κ := by have := oddPolarCoef_pos j; linarith
  have hsum : (∑ k : Fin 4, (![1 / (1 + κ), -(1 / (1 + κ)), -(κ / (1 + κ)), κ / (1 + κ)] k : ℂ) *
      Complex.exp (I * (I / 2) * ((![2 * r, -(2 * r), r, -r] k : ℝ) : ℂ))) = 0 := by
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, cexp_I_mul_I_div_two]
    have e1 : Real.exp (-(2 * r) / 2) = Real.exp (-r) := by ring_nf
    have e2 : Real.exp (-(-(2 * r)) / 2) = Real.exp r := by ring_nf
    have hκe : κ = Real.exp (r / 2) + Real.exp (-(r / 2)) := by
      rw [hκ, oddPolarCoef, ← hr, Real.cosh_eq]; ring
    have hreal : 1 / (1 + κ) * Real.exp (-r) - 1 / (1 + κ) * Real.exp r -
        κ / (1 + κ) * Real.exp (-r / 2) + κ / (1 + κ) * Real.exp (- -r / 2) = 0 := by
      have h1 : Real.exp r = Real.exp (r / 2) * Real.exp (r / 2) := by rw [← Real.exp_add]; ring_nf
      have h2 : Real.exp (-r) = Real.exp (-r / 2) * Real.exp (-r / 2) := by
        rw [← Real.exp_add]; ring_nf
      have h3 : Real.exp (- -r / 2) = Real.exp (r / 2) := by ring_nf
      have h4 : Real.exp (-(r / 2)) = Real.exp (-r / 2) := by ring_nf
      rw [h1, h2, h3, hκe, h4]
      field_simp
      ring_nf
    rw [e1, e2]
    have hc : ((1 / (1 + κ) * Real.exp (-r) - 1 / (1 + κ) * Real.exp r -
        κ / (1 + κ) * Real.exp (-r / 2) + κ / (1 + κ) * Real.exp (- -r / 2) : ℝ) : ℂ) = 0 := by
      rw [hreal, Complex.ofReal_zero]
    push_cast at hc ⊢
    linear_combination hc
  rw [hsum, zero_mul]

/-! ## The negative node test -/

/-- `o(x − L/2) − o(x + L/2)` with the odd pole-free profile; an even function. -/
def evenPolarMinusFn (j : ℕ) : ℝ → ℝ :=
  bumpSum (oddPolarProfile j) ![1, -1] ![Real.log j / 2, -(Real.log j / 2)]

theorem oddPolarProfile_neg (j : ℕ) (v : ℝ) : oddPolarProfile j (-v) = -oddPolarProfile j v := by
  unfold oddPolarProfile
  rw [show -v - 2 * (nodeBump j).rOut = -(v + 2 * (nodeBump j).rOut) by ring,
    show -v + 2 * (nodeBump j).rOut = -(v - 2 * (nodeBump j).rOut) by ring,
    show -v - (nodeBump j).rOut = -(v + (nodeBump j).rOut) by ring,
    show -v + (nodeBump j).rOut = -(v - (nodeBump j).rOut) by ring,
    nodeBump_neg, nodeBump_neg, nodeBump_neg, nodeBump_neg]
  ring

theorem evenPolarMinusFn_neg (j : ℕ) (x : ℝ) :
    evenPolarMinusFn j (-x) = evenPolarMinusFn j x := by
  simp only [evenPolarMinusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [show -x - Real.log j / 2 = -(x + Real.log j / 2) by ring,
    show -x - -(Real.log j / 2) = -(x - Real.log j / 2) by ring, oddPolarProfile_neg,
    oddPolarProfile_neg, show x - -(Real.log j / 2) = x + Real.log j / 2 by ring]
  ring

theorem contDiff_evenPolarMinusC (j : ℕ) : ContDiff ℝ 2 fun u => (evenPolarMinusFn j u : ℂ) := by
  have h : ContDiff ℝ 2 (evenPolarMinusFn j) :=
    contDiff_bumpSum (contDiff_oddPolarProfile j) _ _
  exact Complex.ofRealCLM.contDiff.comp h

theorem hasCompactSupport_evenPolarMinusC (j : ℕ) :
    HasCompactSupport fun u => (evenPolarMinusFn j u : ℂ) := by
  have h : HasCompactSupport (evenPolarMinusFn j) :=
    hasCompactSupport_bumpSum (fun u hu => oddPolarProfile_eq_zero j hu) _ _
  exact h.comp_left Complex.ofReal_zero

theorem paperFT_evenPolarMinus_I_div_two (j : ℕ) :
    paperFT (fun u => (evenPolarMinusFn j u : ℂ)) (I / 2) = 0 := by
  have e : (fun u => (evenPolarMinusFn j u : ℂ)) = fun u => ∑ k : Fin 2, (![1, -1] k : ℂ) *
      (fun v => (oddPolarProfile j v : ℂ)) (u - ![Real.log j / 2, -(Real.log j / 2)] k) := by
    funext u
    simp only [evenPolarMinusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    push_cast
    ring
  have hc : Continuous fun v => (oddPolarProfile j v : ℂ) :=
    Complex.continuous_ofReal.comp (contDiff_oddPolarProfile j).continuous
  have hcs : HasCompactSupport fun v => (oddPolarProfile j v : ℂ) :=
    (SeparatedBump.hasCompactSupport_of_abs_gt fun _ hu =>
      oddPolarProfile_eq_zero j hu).comp_left Complex.ofReal_zero
  rw [e, paperFT_sum_translate Finset.univ _ _ hc hcs, paperFT_oddPolarProfile_I_div_two,
    mul_zero]

/-- The negative pole-free even node test. -/
def evenPolarMinusTest (j : ℕ) : WeilEvenPolarTestFn :=
  ⟨⟨fun u => (evenPolarMinusFn j u : ℂ), contDiff_evenPolarMinusC j,
    hasCompactSupport_evenPolarMinusC j⟩, fun x => by simp only [evenPolarMinusFn_neg],
    paperFT_evenPolarMinus_I_div_two j⟩

theorem logVector_evenPolarMinusTest (j : LogIndex) :
    logVector (evenPolarMinusTest j).1 =
      Finsupp.single j (-(2 * (∫ u, oddPolarProfile j u ^ 2) / Real.sqrt j)) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (fun u => (evenPolarMinusFn j u : ℂ)) m = _
  unfold evenPolarMinusFn
  rw [logValue_evenPair j.2 _ (contDiff_oddPolarProfile j)
    (fun u hu => oddPolarProfile_eq_zero j hu) 1 (-1) m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm, h]; ring
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

/-! ## Farkas -/

/-- **Prime-blind positivity on even pole-free tests.** -/
def PrimeBlindPositiveEvenPolar : Prop :=
  ∀ c : WeilEvenPolarTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1.1 n) = 0) →
    0 ≤ c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1)

/-- **Even pole-free Farkas.** -/
theorem exists_weilPositiveEvenPolar_iff :
    (∃ lam : ℕ → ℝ, WeilPositiveEvenPolar lam) ↔ PrimeBlindPositiveEvenPolar := by
  constructor
  · rintro ⟨lam, hlam⟩ c hc hnull
    have hall : ∀ f : WeilEvenPolarTestFn,
        linearCombination ℝ (fun j : LogIndex => lam j) (logVector f.1) ≤
          weilArchRe (EF.weilTest f.1.1 f.1.1) := fun f => by
      have h := hlam f.1.1 f.1.2.1 f.1.2.2 f.2.1 f.2.2
      rw [re_weilFullFunctional_eq lam f.1] at h
      linarith
    have hsum : (c.sum fun f t => t • logVector f.1) = 0 := by
      ext j
      rw [Finsupp.sum_apply, Finsupp.coe_zero, Pi.zero_apply, ← hnull j j.2]
      refine Finsupp.sum_congr fun f _ => ?_
      rw [Finsupp.smul_apply, logVector_apply, smul_eq_mul]
    have hlin : (c.sum fun f t => linearCombination ℝ (fun j : LogIndex => lam j)
        (t • logVector f.1)) = 0 := by
      rw [← map_finsuppSum, hsum, map_zero]
    have h1 : (c.sum fun f t => linearCombination ℝ (fun j : LogIndex => lam j)
        (t • logVector f.1)) ≤ c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1) := by
      refine Finset.sum_le_sum fun f _ => ?_
      show linearCombination ℝ (fun j : LogIndex => lam j) (c f • logVector f.1) ≤
        c f * weilArchRe (EF.weilTest f.1.1 f.1.1)
      rw [map_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hall f) (hc f)
    linarith
  · intro h
    have hsqrt : ∀ j : LogIndex, 0 < Real.sqrt (j : ℕ) := fun j =>
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le two_pos j.2))
    have hplus : ∀ j : LogIndex, 0 < 2 * (∫ u, evenPolarProfile j u ^ 2) / Real.sqrt j :=
      fun j => div_pos (mul_pos two_pos (lt_of_lt_of_le
        (by have := integral_narrowBump_sq_pos 0; have := nodeScale_pos j; positivity)
        (le_integral_evenPolarProfile_sq j))) (hsqrt j)
    obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
      (fun f : WeilEvenPolarTestFn => logVector f.1)
      (fun f => weilArchRe (EF.weilTest f.1.1 f.1.1))
      (fun j => ⟨evenPolarMinusTest j, _, div_pos (mul_pos two_pos
        (integral_oddPolarProfile_sq_pos j)) (hsqrt j), logVector_evenPolarMinusTest j⟩)
      (fun j => ⟨evenPolarNodeTest j, _, hplus j, logVector_evenPolarNode j⟩)
      (fun c hc hnull => by
        have e : linearCombination ℝ (fun f : WeilEvenPolarTestFn =>
            weilArchRe (EF.weilTest f.1.1 f.1.1)) c =
            c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1) := by
          rw [linearCombination_apply]; simp only [smul_eq_mul]
        rw [e]
        refine h c hc fun n hn => ?_
        have h0 := congrArg (fun v : LogIndex →₀ ℝ => v ⟨n, hn⟩) hnull
        simp only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
          logVector_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h0
        exact h0)
    refine ⟨fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0, fun f hf hfc hfe h0 => ?_⟩
    have hT := hlam ⟨⟨f, hf, hfc⟩, hfe, h0⟩
    have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
        lam := funext fun j => by simp [j.2]
    rw [re_weilFullFunctional_eq _ ⟨f, hf, hfc⟩, e]
    exact sub_nonneg.mpr hT

end RHTower.EvenSector

end
