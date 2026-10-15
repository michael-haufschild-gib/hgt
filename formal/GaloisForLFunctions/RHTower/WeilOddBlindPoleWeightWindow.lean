import GaloisForLFunctions.RHTower.WeilParityPoleWeightWindows
import GaloisForLFunctions.RHTower.WeilOddConeOneSidedCriterion

/-!
# The prime-blind pole-weight window on odd tests

`PrimeBlindPositiveOddAt β` is nonnegativity of the archimedean functional with pole weight `β`
(`poleWeightArchRe β`) on every nonnegative combination of autocorrelations of odd tests whose
values at all `±log n`, `n ≥ 2`, vanish.  It involves no prime weights and no zeros.  On odd tests
the pole term is `−2|f̂(i/2)|² ≤ 0`, so the admissible `β` form a down-set
(`primeBlindPositiveOddAt_anti`).

**Odd Farkas** (`exists_weilPositiveOddAt_iff`).  `PrimeBlindPositiveOddAt β` holds iff some real
weights are Weil-positive at pole weight `β` on all odd tests.  The odd tests reaching a single
node `log j` with either sign are `φ(x − L/2) ± φ(x + L/2)`, `L = log j`, with `φ` odd for the
`+` sign and even for the `−` sign; their node value is `±2‖φ‖²/√j`.

**Theorem** (`exists_weilPositiveOdd_gt_vonMangoldt_of_primeBlindPositiveOddAt`).  If
`PrimeBlindPositiveOddAt β` holds for some `β > 1`, there are weights `lam` that are Weil-positive
on odd tests (pole weight `1`) and exceed `Λ` at some `n ≥ 2`.  So blind odd positivity above
pole weight `1` produces a second odd Weil-positive system, different from `Λ`.

**Corollary** (`not_primeBlindPositiveOddAt_of_le_vonMangoldt`).  If every odd Weil-positive
system lies below `Λ`, then blind odd positivity fails at every `β > 1`.

**Corollary** (`riemannHypothesis_imp_forall_primeBlindPositiveOddAt_iff`).  Under RH, and if every
odd Weil-positive system lies below `Λ`, the blind odd window is exactly `(−∞, 1]`.

Proof.  Odd Farkas gives `lam` at pole weight `β`; antitonicity gives pole weight `1`.  If `lam ≤ Λ`
on `n ≥ 2`, odd minorant rigidity makes `lam = Λ` there, so `Λ` itself would be odd Weil-positive at
`β > 1`, which fails unconditionally (`not_weilPositiveOddAt_vonMangoldt_of_one_lt`).
-/

open Complex MeasureTheory Set Finsupp Zeta23

noncomputable section

namespace RHTower

open WeilOneSided SeparatedBump EvenSector WeilPoleWeight

/-! ## Odd pair tests reaching one node with either sign -/

/-- `φ₋(x − L/2) + φ₋(x + L/2)` with the odd profile, `L = log j`; an odd function. -/
def oddPlusFn (j : ℕ) : ℝ → ℝ :=
  bumpSum (oddProfile j) ![1, 1] ![Real.log j / 2, -(Real.log j / 2)]

/-- `φ₊(x − L/2) − φ₊(x + L/2)` with the even profile, `L = log j`; an odd function. -/
def oddMinusFn (j : ℕ) : ℝ → ℝ :=
  bumpSum (evenProfile j) ![1, -1] ![Real.log j / 2, -(Real.log j / 2)]

theorem oddPlusFn_neg (j : ℕ) (x : ℝ) : oddPlusFn j (-x) = -oddPlusFn j x := by
  simp only [oddPlusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show -x - Real.log j / 2 = -(x + Real.log j / 2) by ring,
    show -x - -(Real.log j / 2) = -(x - Real.log j / 2) by ring, oddProfile_neg, oddProfile_neg]
  rw [show x - -(Real.log j / 2) = x + Real.log j / 2 by ring]
  ring

theorem oddMinusFn_neg (j : ℕ) (x : ℝ) : oddMinusFn j (-x) = -oddMinusFn j x := by
  simp only [oddMinusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show -x - Real.log j / 2 = -(x + Real.log j / 2) by ring,
    show -x - -(Real.log j / 2) = -(x - Real.log j / 2) by ring, evenProfile_neg, evenProfile_neg]
  rw [show x - -(Real.log j / 2) = x + Real.log j / 2 by ring]
  ring

theorem contDiff_oddPlusC (j : ℕ) : ContDiff ℝ 2 fun u => (oddPlusFn j u : ℂ) := by
  have h : ContDiff ℝ 2 (oddPlusFn j) := contDiff_bumpSum (contDiff_oddProfile j) _ _
  exact Complex.ofRealCLM.contDiff.comp h

theorem hasCompactSupport_oddPlusC (j : ℕ) :
    HasCompactSupport fun u => (oddPlusFn j u : ℂ) := by
  have h : HasCompactSupport (oddPlusFn j) :=
    hasCompactSupport_bumpSum (fun u hu => oddProfile_eq_zero j hu) _ _
  exact h.comp_left Complex.ofReal_zero

theorem contDiff_oddMinusC (j : ℕ) : ContDiff ℝ 2 fun u => (oddMinusFn j u : ℂ) := by
  have h : ContDiff ℝ 2 (oddMinusFn j) := contDiff_bumpSum (contDiff_evenProfile j) _ _
  exact Complex.ofRealCLM.contDiff.comp h

theorem hasCompactSupport_oddMinusC (j : ℕ) :
    HasCompactSupport fun u => (oddMinusFn j u : ℂ) := by
  have h : HasCompactSupport (oddMinusFn j) :=
    hasCompactSupport_bumpSum (fun u hu => evenProfile_eq_zero j hu) _ _
  exact h.comp_left Complex.ofReal_zero

/-- The odd test with node value `+2‖φ₋‖²/√j`. -/
def oddPlus (j : ℕ) : WeilOddTestFn :=
  ⟨⟨fun u => (oddPlusFn j u : ℂ), contDiff_oddPlusC j, hasCompactSupport_oddPlusC j⟩,
    fun x => by simp only [oddPlusFn_neg, Complex.ofReal_neg]⟩

/-- The odd test with node value `−2‖φ₊‖²/√j`. -/
def oddMinus (j : ℕ) : WeilOddTestFn :=
  ⟨⟨fun u => (oddMinusFn j u : ℂ), contDiff_oddMinusC j, hasCompactSupport_oddMinusC j⟩,
    fun x => by simp only [oddMinusFn_neg, Complex.ofReal_neg]⟩

theorem logVector_oddPlus (j : LogIndex) :
    logVector (oddPlus j).1 =
      Finsupp.single j (2 * (∫ u, oddProfile j u ^ 2) / Real.sqrt j) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (fun u => (oddPlusFn j u : ℂ)) m = _
  unfold oddPlusFn
  rw [logValue_evenPair j.2 _ (contDiff_oddProfile j) (fun u hu => oddProfile_eq_zero j hu) 1 1
    m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm, h]; ring
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

theorem logVector_oddMinus (j : LogIndex) :
    logVector (oddMinus j).1 =
      Finsupp.single j (-(2 * (∫ u, evenProfile j u ^ 2) / Real.sqrt j)) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (fun u => (oddMinusFn j u : ℂ)) m = _
  unfold oddMinusFn
  rw [logValue_evenPair j.2 _ (contDiff_evenProfile j) (fun u hu => evenProfile_eq_zero j hu) 1
    (-1) m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm, h]; ring
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

/-! ## The blind odd window -/

/-- Prime-blind positivity at pole weight `β` on nonnegative combinations of autocorrelations of
odd tests. -/
def PrimeBlindPositiveOddAt (β : ℝ) : Prop :=
  ∀ c : WeilOddTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1.1 n) = 0) →
    0 ≤ c.sum fun f t => t * poleWeightArchRe β f.1

theorem poleWeightArchRe_anti_of_odd {β β' : ℝ} (h : β ≤ β') (f : WeilOddTestFn) :
    poleWeightArchRe β' f.1 ≤ poleWeightArchRe β f.1 := by
  unfold poleWeightArchRe
  rw [re_weilPoleTerm_weilTest_of_odd f.1.2.1.continuous f.1.2.2 f.2]
  have := mul_nonneg (sub_nonneg.mpr h) (sq_nonneg ‖paperFT f.1.1 (I / 2)‖)
  nlinarith

/-- **The blind odd window is a down-set.** -/
theorem primeBlindPositiveOddAt_anti {β β' : ℝ} (h : β ≤ β')
    (hβ' : PrimeBlindPositiveOddAt β') : PrimeBlindPositiveOddAt β := fun c hc hnull =>
  (hβ' c hc hnull).trans (Finset.sum_le_sum fun f _ =>
    mul_le_mul_of_nonneg_left (poleWeightArchRe_anti_of_odd h f) (hc f))

theorem sum_logVector_odd_eq_zero {c : WeilOddTestFn →₀ ℝ}
    (hnull : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1.1 n) = 0) :
    (c.sum fun f t => t • logVector f.1) = 0 := by
  ext j
  rw [Finsupp.sum_apply, Finsupp.coe_zero, Pi.zero_apply, ← hnull j j.2]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [Finsupp.smul_apply, logVector_apply, smul_eq_mul]

/-- **Forward Farkas direction.** -/
theorem primeBlindPositiveOddAt_of_weilPositiveOddAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) : PrimeBlindPositiveOddAt β := by
  intro c hc hnull
  have h1 : 0 ≤ c.sum fun f t =>
      t * (weilPoleWeightFunctional β lam (EF.weilTest f.1.1 f.1.1)).re :=
    Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (h f.1.1 f.1.2.1 f.1.2.2 f.2)
  have hlin : (c.sum fun f t =>
      linearCombination ℝ (fun j : LogIndex => lam j) (t • logVector f.1)) = 0 := by
    rw [← map_finsuppSum, sum_logVector_odd_eq_zero hnull, map_zero]
  have e : (c.sum fun f t =>
      t * (weilPoleWeightFunctional β lam (EF.weilTest f.1.1 f.1.1)).re) =
      (c.sum fun f t => t * poleWeightArchRe β f.1) -
        c.sum fun f t => linearCombination ℝ (fun j : LogIndex => lam j) (t • logVector f.1) := by
    rw [← Finsupp.sum_sub]
    refine Finsupp.sum_congr fun f _ => ?_
    rw [re_weilPoleWeightFunctional_eq, map_smul, smul_eq_mul]
    ring
  linarith

/-- **Odd Farkas.**  Some real weights are Weil-positive at pole weight `β` on every odd test iff
prime-blind positivity holds on the odd cone at `β`. -/
theorem exists_weilPositiveOddAt_iff (β : ℝ) :
    (∃ lam : ℕ → ℝ, WeilPositiveOddAt β lam) ↔ PrimeBlindPositiveOddAt β := by
  constructor
  · rintro ⟨lam, h⟩
    exact primeBlindPositiveOddAt_of_weilPositiveOddAt h
  · intro h
    have hsqrt : ∀ j : LogIndex, 0 < Real.sqrt (j : ℕ) := fun j =>
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le two_pos j.2))
    obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
      (fun f : WeilOddTestFn => logVector f.1) (fun f => poleWeightArchRe β f.1)
      (fun j => ⟨oddMinus j, _, div_pos (mul_pos two_pos (integral_evenProfile_sq_pos j))
        (hsqrt j), logVector_oddMinus j⟩)
      (fun j => ⟨oddPlus j, _, div_pos (mul_pos two_pos (integral_oddProfile_sq_pos j))
        (hsqrt j), logVector_oddPlus j⟩)
      (fun c hc hnull => by
        have e : linearCombination ℝ (fun f : WeilOddTestFn => poleWeightArchRe β f.1) c =
            c.sum fun f t => t * poleWeightArchRe β f.1 := by
          rw [linearCombination_apply]; simp only [smul_eq_mul]
        rw [e]
        refine h c hc fun n hn => ?_
        have h0 := congrArg (fun v : LogIndex →₀ ℝ => v ⟨n, hn⟩) hnull
        simp only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
          logVector_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h0
        exact h0)
    refine ⟨fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0, fun f hf hfc hodd => ?_⟩
    rw [re_weilPoleWeightFunctional_eq β _ ⟨f, hf, hfc⟩]
    have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
        lam := funext fun j => by simp [j.2]
    rw [e]
    linarith [hlam ⟨⟨f, hf, hfc⟩, hodd⟩]

/-- **RH gives prime-blind positivity on odd tests at every pole weight `β ≤ 1`.** -/
theorem primeBlindPositiveOddAt_of_riemannHypothesis (hRH : RiemannHypothesis) {β : ℝ}
    (hβ : β ≤ 1) : PrimeBlindPositiveOddAt β :=
  primeBlindPositiveOddAt_of_weilPositiveOddAt
    ((riemannHypothesis_iff_weilPositiveOddAt_vonMangoldt hβ).mp hRH)

/-! ## Above pole weight `1` -/

/-- Odd Weil positivity at pole weight `β` depends on the weights only at `n ≥ 2`. -/
theorem weilPositiveOddAt_congr {β : ℝ} {lam lam' : ℕ → ℝ} (h : ∀ n, 2 ≤ n → lam n = lam' n)
    (hlam : WeilPositiveOddAt β lam) : WeilPositiveOddAt β lam' := fun f hf hfc hodd => by
  have h1 := hlam f hf hfc hodd
  rw [re_weilPoleWeightFunctional_eq β _ ⟨f, hf, hfc⟩] at h1 ⊢
  have e : (fun j : LogIndex => lam j) = fun j : LogIndex => lam' j :=
    funext fun j => h j j.2
  rwa [e] at h1

/-- **Blind odd positivity above pole weight `1` produces a second odd Weil-positive system.**
It is odd Weil-positive and exceeds `Λ` at some `n ≥ 2`. -/
theorem exists_weilPositiveOdd_gt_vonMangoldt_of_primeBlindPositiveOddAt {β : ℝ} (hβ : 1 < β)
    (h : PrimeBlindPositiveOddAt β) :
    ∃ lam : ℕ → ℝ, WeilPositiveOdd lam ∧
      ∃ n, 2 ≤ n ∧ (ArithmeticFunction.vonMangoldt n : ℝ) < lam n := by
  obtain ⟨lam, hlam⟩ := (exists_weilPositiveOddAt_iff β).mpr h
  have h1 : WeilPositiveOdd lam := weilPositiveOddAt_one_iff.mp (weilPositiveOddAt_anti hβ.le hlam)
  refine ⟨lam, h1, ?_⟩
  by_contra hcon
  push Not at hcon
  have heq := eq_vonMangoldt_of_weilPositiveOdd_of_le h1 hcon
  exact not_weilPositiveOddAt_vonMangoldt_of_one_lt hβ (weilPositiveOddAt_congr heq hlam)

/-- **If every odd Weil-positive system lies below `Λ`, blind odd positivity fails above `1`.** -/
theorem not_primeBlindPositiveOddAt_of_le_vonMangoldt
    (hthin : ∀ lam : ℕ → ℝ, WeilPositiveOdd lam →
      ∀ n, 2 ≤ n → lam n ≤ ArithmeticFunction.vonMangoldt n)
    {β : ℝ} (hβ : 1 < β) : ¬ PrimeBlindPositiveOddAt β := fun h => by
  obtain ⟨lam, hlam, n, hn, hlt⟩ := exists_weilPositiveOdd_gt_vonMangoldt_of_primeBlindPositiveOddAt
    hβ h
  exact absurd (hthin lam hlam n hn) (not_le.mpr hlt)

/-- **Under RH and odd thinness the blind odd window is exactly `(−∞, 1]`.** -/
theorem riemannHypothesis_imp_forall_primeBlindPositiveOddAt_iff (hRH : RiemannHypothesis)
    (hthin : ∀ lam : ℕ → ℝ, WeilPositiveOdd lam →
      ∀ n, 2 ≤ n → lam n ≤ ArithmeticFunction.vonMangoldt n) (β : ℝ) :
    PrimeBlindPositiveOddAt β ↔ β ≤ 1 := by
  refine ⟨fun h => ?_, primeBlindPositiveOddAt_of_riemannHypothesis hRH⟩
  by_contra hβ
  exact not_primeBlindPositiveOddAt_of_le_vonMangoldt hthin (not_le.mp hβ) h

end RHTower

end
