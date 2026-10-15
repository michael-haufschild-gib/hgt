import GaloisForLFunctions.RHTower.SeparatedBumpWeilPositivity
import GaloisForLFunctions.RHTower.WeilPoleWeightForcedOne
import GaloisForLFunctions.RHTower.EvenTestLaplacePositivity

/-!
# The even sector of the Weil cone

Restrict Weil positivity to autocorrelations of **even** tests (`f(−x) = f(x)`).

* `WeilPositiveEvenAt β lam`: Weil positivity at pole weight `β` on even tests;
  `PrimeBlindPositiveEvenAt β`: prime-blind positivity on nonnegative combinations of
  autocorrelations of even tests.
* **Monotone in the pole weight** (`weilPositiveEvenAt_mono`, `primeBlindPositiveEvenAt_mono`):
  the pole term of an even test is `2|f̂(i/2)|² ≥ 0`, so the even window in `β` is an up-set.
* **RH gives the even sector at every `β ≥ 1`** (`primeBlindPositiveEvenAt_of_riemannHypothesis`).
* **Even Farkas** (`exists_weilPositiveEvenAt_iff`): some real weights are Weil-positive at pole
  weight `β` on all even tests iff prime-blind positivity holds on the even cone at `β`.  The
  generators reaching each node `log j` with both signs are the even two-bump tests
  `p(x − L/2) + p(−x − L/2)`, `L = log j`, whose node value is `2∫p(v)p(−v)dv/√j`
  (`logValue_twoBump`): positive for an even profile, negative for an odd one.

Whether the even cone is thin at `β = 1` (so that RH is prime-blind positivity on even tests) is
open: the shifted-Gamma blind family is not even-type (`laplacePairing_xiShiftedGammaTest_neg`).
-/

open Complex MeasureTheory Set Finsupp Zeta23

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided SeparatedBump

/-! ## Even tests and the even cones -/

/-- Even Weil tests. -/
def EvenWeilTestFn : Type := {f : WeilTestFn // ∀ x, f.1 (-x) = f.1 x}

/-- Weil positivity at pole weight `β` on the autocorrelations of even tests. -/
def WeilPositiveEvenAt (β : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → (∀ x, f (-x) = f x) →
    0 ≤ (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f f)).re

/-- Prime-blind positivity at pole weight `β` on nonnegative combinations of autocorrelations of
even tests. -/
def PrimeBlindPositiveEvenAt (β : ℝ) : Prop :=
  ∀ c : EvenWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1.1 n) = 0) →
    0 ≤ c.sum fun f t => t * poleWeightArchRe β f.1

theorem weilPoleTerm_re_nonneg_of_even (f : EvenWeilTestFn) :
    0 ≤ (weilPoleTerm (EF.weilTest f.1.1 f.1.1)).re := by
  rw [weilPoleTerm_even f.1.2.1.continuous f.1.2.2 f.2, Complex.ofReal_re]
  positivity

theorem poleWeightArchRe_mono {β β' : ℝ} (h : β ≤ β') (f : EvenWeilTestFn) :
    poleWeightArchRe β f.1 ≤ poleWeightArchRe β' f.1 := by
  unfold poleWeightArchRe
  have := mul_le_mul_of_nonneg_right (by linarith : β - 1 ≤ β' - 1)
    (weilPoleTerm_re_nonneg_of_even f)
  linarith

/-- **The even window is an up-set.** -/
theorem primeBlindPositiveEvenAt_mono {β β' : ℝ} (h : β ≤ β') (hβ : PrimeBlindPositiveEvenAt β) :
    PrimeBlindPositiveEvenAt β' := fun c hc hnull =>
  (hβ c hc hnull).trans (Finset.sum_le_sum fun f _ =>
    mul_le_mul_of_nonneg_left (poleWeightArchRe_mono h f) (hc f))

theorem re_weilPoleWeightFunctional_mono {β β' : ℝ} (h : β ≤ β') (lam : ℕ → ℝ)
    (f : EvenWeilTestFn) :
    (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f.1.1 f.1.1)).re ≤
      (WeilPoleWeight.weilPoleWeightFunctional β' lam (EF.weilTest f.1.1 f.1.1)).re := by
  rw [re_weilPoleWeightFunctional_eq, re_weilPoleWeightFunctional_eq]
  linarith [poleWeightArchRe_mono h f]

/-- **Even Weil positivity is monotone in the pole weight.** -/
theorem weilPositiveEvenAt_mono {β β' : ℝ} (h : β ≤ β') {lam : ℕ → ℝ}
    (hβ : WeilPositiveEvenAt β lam) : WeilPositiveEvenAt β' lam := fun f hf hfc hev =>
  (hβ f hf hfc hev).trans (re_weilPoleWeightFunctional_mono h lam ⟨⟨f, hf, hfc⟩, hev⟩)

theorem weilPositiveEvenAt_of_weilPositiveAt {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveAt β lam) :
    WeilPositiveEvenAt β lam := fun f hf hfc _ => h f hf hfc

/-! ## The forward Farkas direction -/

theorem sum_logVector_eq_zero {c : EvenWeilTestFn →₀ ℝ}
    (hnull : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1.1 n) = 0) :
    (c.sum fun f t => t • logVector f.1) = 0 := by
  ext j
  rw [Finsupp.sum_apply, Finsupp.coe_zero, Pi.zero_apply, ← hnull j j.2]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [Finsupp.smul_apply, logVector_apply, smul_eq_mul]

/-- **Forward Farkas direction.** -/
theorem primeBlindPositiveEvenAt_of_weilPositiveEvenAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) : PrimeBlindPositiveEvenAt β := by
  intro c hc hnull
  have h1 : 0 ≤ c.sum fun f t =>
      t * (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f.1.1 f.1.1)).re :=
    Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (h f.1.1 f.1.2.1 f.1.2.2 f.2)
  have hlin : (c.sum fun f t =>
      linearCombination ℝ (fun j : LogIndex => lam j) (t • logVector f.1)) = 0 := by
    rw [← map_finsuppSum, sum_logVector_eq_zero hnull, map_zero]
  have e : (c.sum fun f t =>
      t * (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f.1.1 f.1.1)).re) =
      (c.sum fun f t => t * poleWeightArchRe β f.1) -
        c.sum fun f t => linearCombination ℝ (fun j : LogIndex => lam j) (t • logVector f.1) := by
    rw [← Finsupp.sum_sub]
    refine Finsupp.sum_congr fun f _ => ?_
    rw [re_weilPoleWeightFunctional_eq, map_smul, smul_eq_mul]
    ring
  linarith

theorem primeBlindPositiveEvenAt_of_primeBlindPositiveAt {β : ℝ} (h : PrimeBlindPositiveAt β) :
    PrimeBlindPositiveEvenAt β := by
  obtain ⟨lam, hlam⟩ := (exists_weilPositiveAt_iff β).mpr h
  exact primeBlindPositiveEvenAt_of_weilPositiveEvenAt (weilPositiveEvenAt_of_weilPositiveAt hlam)

/-- **RH gives prime-blind positivity on even tests at every pole weight `β ≥ 1`.** -/
theorem primeBlindPositiveEvenAt_of_riemannHypothesis (hRH : RiemannHypothesis) {β : ℝ}
    (hβ : 1 ≤ β) : PrimeBlindPositiveEvenAt β :=
  primeBlindPositiveEvenAt_mono hβ (primeBlindPositiveEvenAt_of_primeBlindPositiveAt
    (riemannHypothesis_iff_primeBlindPositiveAt_one.mp hRH))

/-! ## Even two-bump tests -/

/-- **Node values of a two-bump configuration.**  For `f = a₀ p(· − L/2) + a₁ p(· + L/2)` the
value at `log n` is `2 a₀ a₁ ‖p‖²/√n` if `log n = L` and `0` if `log n` is more than the width
away from `L`. -/
theorem logValue_twoBump {p : ℝ → ℝ} {δ L : ℝ} (hp : ContDiff ℝ 2 p)
    (hps : ∀ u, δ / 2 < |u| → p u = 0) (hL : 0 < L) (a₀ a₁ : ℝ) {n : ℕ}
    (hn0 : δ < Real.log n) (hgap : Real.log n = L ∨ δ < |Real.log n - L|) :
    logValue (fun u => (bumpSum p ![a₀, a₁] ![L / 2, -(L / 2)] u : ℂ)) n =
      if Real.log n = L then 2 * a₀ * a₁ * (∫ u, p u ^ 2) / Real.sqrt n else 0 := by
  rw [logValue_bumpSum, integral_bumpSum_mul_bumpSum_sub hp hps,
    integral_bumpSum_mul_bumpSum_sub hp hps]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  set ℓ := Real.log n with hℓdef
  have hz : ∀ c c' : ℝ, δ < |c - c'| → ∫ u, p (u - c) * p (u - c') = 0 := fun c c' h => by
    rw [show (fun u => p (u - c) * p (u - c')) = fun _ => 0 from
      funext fun u => mul_translate_eq_zero hps h u]
    simp
  have hsame : ∀ c : ℝ, ∫ u, p (u - c) * p (u - c) = ∫ u, p u ^ 2 := fun c => by
    have := integral_sub_right_eq_self (μ := volume) (fun u => p u ^ 2) c
    simpa [sq] using this
  have hℓ0 : δ < |ℓ| := lt_of_lt_of_le hn0 (le_abs_self _)
  have e00 : ∫ u, p (u - L / 2) * p (u - (ℓ + L / 2)) = 0 :=
    hz _ _ (by rw [show L / 2 - (ℓ + L / 2) = -ℓ by ring, abs_neg]; exact hℓ0)
  have e10 : ∫ u, p (u - -(L / 2)) * p (u - (ℓ + L / 2)) = 0 :=
    hz _ _ (by
      rw [show -(L / 2) - (ℓ + L / 2) = -(ℓ + L) by ring, abs_neg]
      exact lt_of_lt_of_le (by linarith) (le_abs_self _))
  have e11 : ∫ u, p (u - -(L / 2)) * p (u - (ℓ + -(L / 2))) = 0 :=
    hz _ _ (by rw [show -(L / 2) - (ℓ + -(L / 2)) = -ℓ by ring, abs_neg]; exact hℓ0)
  have f00 : ∫ u, p (u - L / 2) * p (u - (-ℓ + L / 2)) = 0 :=
    hz _ _ (by rw [show L / 2 - (-ℓ + L / 2) = ℓ by ring]; exact hℓ0)
  have f01 : ∫ u, p (u - L / 2) * p (u - (-ℓ + -(L / 2))) = 0 :=
    hz _ _ (by
      rw [show L / 2 - (-ℓ + -(L / 2)) = ℓ + L by ring]
      exact lt_of_lt_of_le (by linarith) (le_abs_self _))
  have f11 : ∫ u, p (u - -(L / 2)) * p (u - (-ℓ + -(L / 2))) = 0 :=
    hz _ _ (by rw [show -(L / 2) - (-ℓ + -(L / 2)) = ℓ by ring]; exact hℓ0)
  rw [e00, e10, e11, f00, f01, f11]
  split_ifs with hℓ
  · rw [show ℓ + -(L / 2) = L / 2 by rw [hℓ]; ring, hsame,
      show -ℓ + L / 2 = -(L / 2) by rw [hℓ]; ring, hsame]
    simp only [mul_zero, zero_add, add_zero]
    ring
  · have hfar : δ < |ℓ - L| := hgap.resolve_left hℓ
    rw [hz _ _ (by rw [show L / 2 - (ℓ + -(L / 2)) = -(ℓ - L) by ring, abs_neg]; exact hfar),
      hz _ _ (by rw [show -(L / 2) - (-ℓ + L / 2) = ℓ - L by ring]; exact hfar)]
    simp

/-- The bump of the node `j`: radius `1/(4(2j+3))`. -/
def nodeBump (j : ℕ) : ContDiffBump (0 : ℝ) := narrowBump (2 * j + 2)

theorem nodeBump_rOut (j : ℕ) : (nodeBump j).rOut = 1 / (4 * (2 * (j : ℝ) + 3)) := by
  show 1 / (4 * (((2 * j + 2 : ℕ) : ℝ) + 1)) = _
  push_cast; ring_nf

theorem nodeBump_eq_zero (j : ℕ) {u : ℝ} (hu : (nodeBump j).rOut ≤ |u|) : nodeBump j u = 0 :=
  (nodeBump j).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hu)

theorem nodeBump_zero (j : ℕ) : nodeBump j 0 = 1 :=
  (nodeBump j).one_of_mem_closedBall (Metric.mem_closedBall_self (nodeBump j).rIn_pos.le)

/-- The even profile `φ(v) + φ(−v)`. -/
def evenProfile (j : ℕ) (v : ℝ) : ℝ := nodeBump j v + nodeBump j (-v)

/-- The odd profile `φ(v − 2r) − φ(−v − 2r)`. -/
def oddProfile (j : ℕ) (v : ℝ) : ℝ :=
  nodeBump j (v - 2 * (nodeBump j).rOut) - nodeBump j (-v - 2 * (nodeBump j).rOut)

theorem contDiff_evenProfile (j : ℕ) : ContDiff ℝ 2 (evenProfile j) :=
  ((nodeBump j).contDiff).add ((nodeBump j).contDiff.comp contDiff_neg)

theorem contDiff_oddProfile (j : ℕ) : ContDiff ℝ 2 (oddProfile j) :=
  ((nodeBump j).contDiff.comp (contDiff_id.sub contDiff_const)).sub
    ((nodeBump j).contDiff.comp (contDiff_neg.sub contDiff_const))

theorem evenProfile_eq_zero (j : ℕ) {u : ℝ} (hu : 6 * (nodeBump j).rOut / 2 < |u|) :
    evenProfile j u = 0 := by
  have hr := (nodeBump j).rOut_pos
  unfold evenProfile
  rw [nodeBump_eq_zero j (by linarith), nodeBump_eq_zero j (by rw [abs_neg]; linarith), add_zero]

theorem oddProfile_eq_zero (j : ℕ) {u : ℝ} (hu : 6 * (nodeBump j).rOut / 2 < |u|) :
    oddProfile j u = 0 := by
  have hr := (nodeBump j).rOut_pos
  have h2r : |2 * (nodeBump j).rOut| = 2 * (nodeBump j).rOut := abs_of_pos (by linarith)
  have h1 := abs_sub_abs_le_abs_sub u (2 * (nodeBump j).rOut)
  have h2 := abs_sub_abs_le_abs_sub (-u) (2 * (nodeBump j).rOut)
  rw [h2r] at h1 h2
  rw [abs_neg] at h2
  unfold oddProfile
  rw [nodeBump_eq_zero j (by linarith), nodeBump_eq_zero j (by linarith), sub_zero]

theorem evenProfile_neg (j : ℕ) (v : ℝ) : evenProfile j (-v) = evenProfile j v := by
  unfold evenProfile; rw [neg_neg, add_comm]

theorem oddProfile_neg (j : ℕ) (v : ℝ) : oddProfile j (-v) = -oddProfile j v := by
  unfold oddProfile; rw [neg_neg]; ring

theorem integral_sq_pos_of {p : ℝ → ℝ} {R : ℝ} (hp : Continuous p) (hps : ∀ u, R < |u| → p u = 0)
    {v : ℝ} (hv : p v ≠ 0) : 0 < ∫ u, p u ^ 2 :=
  (hp.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((SeparatedBump.hasCompactSupport_of_abs_gt hps).comp_left (g := fun x : ℝ => x ^ 2)
      (by norm_num))
    (fun u => sq_nonneg _) (x := v) (pow_ne_zero 2 hv)

theorem integral_evenProfile_sq_pos (j : ℕ) : 0 < ∫ u, evenProfile j u ^ 2 :=
  integral_sq_pos_of (contDiff_evenProfile j).continuous (fun u hu => evenProfile_eq_zero j hu)
    (v := 0) (by unfold evenProfile; rw [neg_zero, nodeBump_zero]; norm_num)

theorem integral_oddProfile_sq_pos (j : ℕ) : 0 < ∫ u, oddProfile j u ^ 2 := by
  have hr := (nodeBump j).rOut_pos
  refine integral_sq_pos_of (contDiff_oddProfile j).continuous
    (fun u hu => oddProfile_eq_zero j hu) (v := 2 * (nodeBump j).rOut) ?_
  unfold oddProfile
  rw [sub_self, nodeBump_zero, nodeBump_eq_zero j (by
    rw [show -(2 * (nodeBump j).rOut) - 2 * (nodeBump j).rOut = -(4 * (nodeBump j).rOut) by ring,
      abs_neg, abs_of_pos (by linarith)]; linarith)]
  norm_num

/-! ## Even pair tests reaching one node with either sign -/

/-- `φ₊(x − L/2) + φ₊(x + L/2)` with the even profile, `L = log j`. -/
def evenPlusFn (j : ℕ) : ℝ → ℝ :=
  bumpSum (evenProfile j) ![1, 1] ![Real.log j / 2, -(Real.log j / 2)]

/-- `φ₋(x − L/2) − φ₋(x + L/2)` with the odd profile, `L = log j`; an even function. -/
def evenMinusFn (j : ℕ) : ℝ → ℝ :=
  bumpSum (oddProfile j) ![1, -1] ![Real.log j / 2, -(Real.log j / 2)]

theorem evenPlusFn_neg (j : ℕ) (x : ℝ) : evenPlusFn j (-x) = evenPlusFn j x := by
  simp only [evenPlusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show -x - Real.log j / 2 = -(x + Real.log j / 2) by ring,
    show -x - -(Real.log j / 2) = -(x - Real.log j / 2) by ring, evenProfile_neg, evenProfile_neg]
  rw [show x - -(Real.log j / 2) = x + Real.log j / 2 by ring]
  ring

theorem evenMinusFn_neg (j : ℕ) (x : ℝ) : evenMinusFn j (-x) = evenMinusFn j x := by
  simp only [evenMinusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show -x - Real.log j / 2 = -(x + Real.log j / 2) by ring,
    show -x - -(Real.log j / 2) = -(x - Real.log j / 2) by ring, oddProfile_neg, oddProfile_neg]
  rw [show x - -(Real.log j / 2) = x + Real.log j / 2 by ring]
  ring

theorem nodeWidth_lt (j : ℕ) (hj : 2 ≤ j) :
    6 * (nodeBump j).rOut < Real.log 2 ∧ 6 * (nodeBump j).rOut < 1 / ((j : ℝ) + 1) := by
  rw [nodeBump_rOut]
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : 6 * (1 / (4 * (2 * (j : ℝ) + 3))) = 3 / (2 * (2 * (j : ℝ) + 3)) := by
    field_simp; ring
  rw [h1]
  constructor
  · have := WeilExcess.seventeen_div_twentyfive_lt_log_two
    have : 3 / (2 * (2 * (j : ℝ) + 3)) ≤ 3 / 14 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith

/-- The node values of the even pair tests. -/
theorem logValue_evenPair {j : ℕ} (hj : 2 ≤ j) (p : ℝ → ℝ) (hp : ContDiff ℝ 2 p)
    (hps : ∀ u, 6 * (nodeBump j).rOut / 2 < |u| → p u = 0) (a₀ a₁ : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    logValue (fun u => (bumpSum p ![a₀, a₁] ![Real.log j / 2, -(Real.log j / 2)] u : ℂ)) m =
      if m = j then 2 * a₀ * a₁ * (∫ u, p u ^ 2) / Real.sqrt m else 0 := by
  obtain ⟨hw2, hwj⟩ := nodeWidth_lt j hj
  have hlog2 : Real.log 2 ≤ Real.log m := Real.log_le_log two_pos (by exact_mod_cast hm)
  have hlogj : 0 < Real.log j := Real.log_pos (by exact_mod_cast (by omega : 1 < j))
  have hiff : Real.log m = Real.log j ↔ m = j := by
    constructor
    · intro h
      by_contra hne
      have := WeilExcess.inv_succ_le_abs_log_sub (by omega) (by omega) hne
      rw [h, sub_self, abs_zero] at this
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    · rintro rfl; rfl
  have hgap : Real.log m = Real.log j ∨ 6 * (nodeBump j).rOut < |Real.log m - Real.log j| := by
    by_cases h : m = j
    · exact Or.inl (by rw [h])
    · exact Or.inr (lt_of_lt_of_le hwj (WeilExcess.inv_succ_le_abs_log_sub (by omega) (by omega) h))
  rw [logValue_twoBump hp hps hlogj a₀ a₁ (by linarith) hgap]
  simp only [hiff]

theorem contDiff_evenPlusC (j : ℕ) : ContDiff ℝ 2 fun u => (evenPlusFn j u : ℂ) := by
  have h : ContDiff ℝ 2 (evenPlusFn j) := contDiff_bumpSum (contDiff_evenProfile j) _ _
  exact Complex.ofRealCLM.contDiff.comp h

theorem hasCompactSupport_evenPlusC (j : ℕ) :
    HasCompactSupport fun u => (evenPlusFn j u : ℂ) := by
  have h : HasCompactSupport (evenPlusFn j) :=
    hasCompactSupport_bumpSum (fun u hu => evenProfile_eq_zero j hu) _ _
  exact h.comp_left Complex.ofReal_zero

theorem contDiff_evenMinusC (j : ℕ) : ContDiff ℝ 2 fun u => (evenMinusFn j u : ℂ) := by
  have h : ContDiff ℝ 2 (evenMinusFn j) := contDiff_bumpSum (contDiff_oddProfile j) _ _
  exact Complex.ofRealCLM.contDiff.comp h

theorem hasCompactSupport_evenMinusC (j : ℕ) :
    HasCompactSupport fun u => (evenMinusFn j u : ℂ) := by
  have h : HasCompactSupport (evenMinusFn j) :=
    hasCompactSupport_bumpSum (fun u hu => oddProfile_eq_zero j hu) _ _
  exact h.comp_left Complex.ofReal_zero

/-- The even test with node value `+2‖φ₊‖²/√j`. -/
def evenPlus (j : ℕ) : EvenWeilTestFn :=
  ⟨⟨fun u => (evenPlusFn j u : ℂ), contDiff_evenPlusC j, hasCompactSupport_evenPlusC j⟩,
    fun x => by simp only [evenPlusFn_neg]⟩

/-- The even test with node value `−2‖φ₋‖²/√j`. -/
def evenMinus (j : ℕ) : EvenWeilTestFn :=
  ⟨⟨fun u => (evenMinusFn j u : ℂ), contDiff_evenMinusC j, hasCompactSupport_evenMinusC j⟩,
    fun x => by simp only [evenMinusFn_neg]⟩

theorem logVector_evenPlus (j : LogIndex) :
    logVector (evenPlus j).1 =
      Finsupp.single j (2 * (∫ u, evenProfile j u ^ 2) / Real.sqrt j) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (fun u => (evenPlusFn j u : ℂ)) m = _
  unfold evenPlusFn
  rw [logValue_evenPair j.2 _ (contDiff_evenProfile j) (fun u hu => evenProfile_eq_zero j hu) 1 1
    m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm, h]; ring
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

theorem logVector_evenMinus (j : LogIndex) :
    logVector (evenMinus j).1 =
      Finsupp.single j (-(2 * (∫ u, oddProfile j u ^ 2) / Real.sqrt j)) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (fun u => (evenMinusFn j u : ℂ)) m = _
  unfold evenMinusFn
  rw [logValue_evenPair j.2 _ (contDiff_oddProfile j) (fun u hu => oddProfile_eq_zero j hu) 1 (-1)
    m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm, h]; ring
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

/-! ## Even Farkas -/

/-- **Even Farkas.**  Some real weights are Weil-positive at pole weight `β` on every even test iff
prime-blind positivity holds on the even cone at `β`. -/
theorem exists_weilPositiveEvenAt_iff (β : ℝ) :
    (∃ lam : ℕ → ℝ, WeilPositiveEvenAt β lam) ↔ PrimeBlindPositiveEvenAt β := by
  constructor
  · rintro ⟨lam, h⟩
    exact primeBlindPositiveEvenAt_of_weilPositiveEvenAt h
  · intro h
    have hsqrt : ∀ j : LogIndex, 0 < Real.sqrt (j : ℕ) := fun j =>
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le two_pos j.2))
    obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
      (fun f : EvenWeilTestFn => logVector f.1) (fun f => poleWeightArchRe β f.1)
      (fun j => ⟨evenMinus j, _, div_pos (mul_pos two_pos (integral_oddProfile_sq_pos j))
        (hsqrt j), logVector_evenMinus j⟩)
      (fun j => ⟨evenPlus j, _, div_pos (mul_pos two_pos (integral_evenProfile_sq_pos j))
        (hsqrt j), logVector_evenPlus j⟩)
      (fun c hc hnull => by
        have e : linearCombination ℝ (fun f : EvenWeilTestFn => poleWeightArchRe β f.1) c =
            c.sum fun f t => t * poleWeightArchRe β f.1 := by
          rw [linearCombination_apply]; simp only [smul_eq_mul]
        rw [e]
        refine h c hc fun n hn => ?_
        have h0 := congrArg (fun v : LogIndex →₀ ℝ => v ⟨n, hn⟩) hnull
        simp only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
          logVector_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h0
        exact h0)
    refine ⟨fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0, fun f hf hfc hev => ?_⟩
    rw [re_weilPoleWeightFunctional_eq β _ ⟨f, hf, hfc⟩]
    have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
        lam := funext fun j => by simp [j.2]
    rw [e]
    linarith [hlam ⟨⟨f, hf, hfc⟩, hev⟩]

end RHTower.EvenSector

end
