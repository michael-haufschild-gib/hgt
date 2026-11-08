import GaloisForLFunctions.CountingHolography.TheBornRuleOfABlackHole
import GaloisForLFunctions.CountingHolography.TheGenusTwoRung

/-!
# The Born rule at genus two

The genus-two black hole has two oscillators, `z² - t₁ z + q` and `z² - t₂ z + q`, the factors of its
numerator `L_q`. Its echo state is a pair of consecutive echoes for each oscillator, and one double tick
acts by the block companion matrix `genusTwoDelay` (`genusTwoDelay_mode`: every root of `L_q` is a mode).

* **The quadratic half holds at every `q`.** The sum of the two Krein squares is a Born rule
  (`genusTwoKrein_bornRule`), nondegenerate for every `q ≥ 2` (`det_genusTwoKrein_ne_zero`). This is the
  functional equation of genus two, read as a count law: the graph has a quadratic count covariant under
  the delay.
* **The count half holds exactly for `q ≤ 3`** (`exists_positive_bornRule_iff`): a positive Born rule
  exists iff `q ≤ 3`. For `q ≥ 4` no quadratic form on the echo states, of any shape, is positive and
  covariant, because the slow resonance is a mode and a positive Born rule puts every mode on the
  universal circle.

With `TheGenusTwoRung`: positive Born rule, count law at every level of the tower and criticality are
the same condition on the genus-two black hole, while the functional equation and the count law at the
first level hold well beyond it.

**Every Born rule.** A symmetric Born rule on the echo states is `c₁ 𝒬_{t₁} ⊕ c₂ 𝒬_{t₂}`
(`bornRule_genusTwo_eq`): covariance forbids pairing echoes of different oscillators, since `t₁ ≠ t₂`, and
fixes each block up to a weight. It is positive iff both weights are positive and both oscillators are
damped (`genusTwoKreinPair_positive_iff`). So the genus-two black hole has a two-parameter family of
quadratic counts, every one of them indefinite for `q ≥ 4`; a true curve would select the trace form
`c₁ = c₂`.

**Conservation and levels.** Along the ringdown a Born rule is multiplied by `qⁿ` after `n` double ticks
(`bornRule_pow`): the normalized count is a conserved Lyapunov functional of the echo state; and a Born
rule of one tick is a Born rule of the level `n` (`bornRule_pow_delay`). The count law of the level `n`
is the equal-weight member: the genus form is the sum of the level-`n` Krein squares of the two
oscillators (`genusForm_eq_kreinSum`). So the curve side (channel numbers) selects the trace form in the
family of Born rules of the graph side.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography

/-- **Conservation of a Born rule along the ringdown**: `S(Mⁿ x) = qⁿ S(x)`. -/
theorem bornRule_pow {d : Type*} [Fintype d] [DecidableEq d] {S M : Matrix d d ℝ} {q : ℝ}
    (h : IsBornRule S M q) (n : ℕ) (x : d → ℝ) :
    (M ^ n *ᵥ x) ⬝ᵥ S *ᵥ (M ^ n *ᵥ x) = q ^ n * (x ⬝ᵥ S *ᵥ x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, quad_of_bornRule h, ih, pow_succ]
    ring

/-- **A Born rule of one tick is a Born rule of every level**: `(Mⁿ)ᵀ S Mⁿ = qⁿ S`. -/
theorem bornRule_pow_delay {d : Type*} [Fintype d] [DecidableEq d] {S M : Matrix d d ℝ} {q : ℝ}
    (h : IsBornRule S M q) (n : ℕ) : IsBornRule S (M ^ n) (q ^ n) := by
  induction n with
  | zero => simp [IsBornRule]
  | succ n ih =>
    unfold IsBornRule at h ih ⊢
    rw [pow_succ, Matrix.transpose_mul, pow_succ]
    calc Mᵀ * (M ^ n)ᵀ * S * (M ^ n * M) = Mᵀ * ((M ^ n)ᵀ * S * M ^ n) * M := by
          simp only [Matrix.mul_assoc]
      _ = (q ^ n * q) • S := by rw [ih, Matrix.mul_smul, Matrix.smul_mul, h, smul_smul]

/-- The delay of the genus-two black hole on the echo states of its two oscillators. -/
def genusTwoDelay (q : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; -(q : ℝ), traceOne q, 0, 0; 0, 0, 0, 1; 0, 0, -(q : ℝ), traceTwo q]

/-- The sum of the Krein squares of the two oscillators. -/
def genusTwoKrein (q : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(q : ℝ), -traceOne q / 2, 0, 0; -traceOne q / 2, 1, 0, 0;
    0, 0, (q : ℝ), -traceTwo q / 2; 0, 0, -traceTwo q / 2, 1]

/-- **The quadratic half at genus two**: the sum of the Krein squares is a Born rule. -/
theorem genusTwoKrein_bornRule (q : ℕ) : IsBornRule (genusTwoKrein q) (genusTwoDelay q) q := by
  unfold IsBornRule
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [genusTwoDelay, genusTwoKrein, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- The form of the sum of the Krein squares. -/
theorem genusTwoKrein_quad (q : ℕ) (x : Fin 4 → ℝ) :
    x ⬝ᵥ genusTwoKrein q *ᵥ x =
      kreinSquare (q : ℝ) (traceOne q) (x 0) (x 1) + kreinSquare (q : ℝ) (traceTwo q) (x 2) (x 3) := by
  simp [genusTwoKrein, dotProduct, Matrix.mulVec, Fin.sum_univ_four, kreinSquare]
  ring

/-- The Born rule of genus two is nondegenerate at every `q ≥ 2`. -/
theorem det_genusTwoKrein_ne_zero {q : ℕ} (hq : 2 ≤ q) : (genusTwoKrein q).det ≠ 0 := by
  have hdet : (genusTwoKrein q).det = ((q : ℝ) - traceOne q ^ 2 / 4) * ((q : ℝ) - traceTwo q ^ 2 / 4) := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, genusTwoKrein, Fin.succAbove]
    ring
  rw [hdet]
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hr := genusTwoRoot_gt hq
  have h := genusTwoRoot_sq q
  have h1 : (q : ℝ) - traceOne q ^ 2 / 4 ≠ 0 := by
    intro h0
    have : traceOne q ^ 2 = 4 * q := by linarith
    rcases (by omega : q ≤ 3 ∨ 4 ≤ q) with h3 | h4
    · rcases (by omega : q = 2 ∨ q = 3) with rfl | rfl <;> unfold traceOne at this <;> push_cast at h hr this <;>
        nlinarith
    · have h4' : (4 : ℝ) ≤ q := by exact_mod_cast h4
      have ht : (q : ℝ) < traceOne q := by unfold traceOne; linarith
      nlinarith
  have h2 : (q : ℝ) - traceTwo q ^ 2 / 4 ≠ 0 := by
    intro h0
    have hle : traceTwo q ^ 2 = 4 * q := by linarith
    unfold traceTwo at hle
    nlinarith
  exact mul_ne_zero h1 h2

/-- **Every root of `L_q` is a mode of the delay.** -/
theorem genusTwoDelay_mode (q : ℕ) {z : ℂ} (hz : (genusTwoL q).eval z = 0) :
    IsMode (genusTwoDelay q) z := by
  rw [genusTwoL_eq_factors] at hz
  rcases mul_eq_zero.mp hz with h | h
  · refine ⟨![1, z, 0, 0], fun h0 => by simpa using congrFun h0 0, ?_⟩
    ext i
    fin_cases i <;> simp [cplx_apply, genusTwoDelay, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    · linear_combination -h
  · refine ⟨![0, 0, 1, z], fun h0 => by simpa using congrFun h0 2, ?_⟩
    ext i
    fin_cases i <;> simp [cplx_apply, genusTwoDelay, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    · linear_combination -h

/-- **The count half at genus two**: a positive Born rule on the echo states exists exactly when
`q ≤ 3`, where the black hole is critical. -/
theorem exists_positive_bornRule_iff {q : ℕ} (hq : 2 ≤ q) :
    (∃ S : Matrix (Fin 4) (Fin 4) ℝ, IsBornRule S (genusTwoDelay q) q ∧ IsPositive S) ↔ q ≤ 3 := by
  constructor
  · rintro ⟨S, hS, hpos⟩
    by_contra h3
    obtain ⟨z, hz, hbig⟩ := genusTwoL_off_circle (q := q) (by omega)
    have := normSq_eq_of_bornRule hS hpos (genusTwoDelay_mode q hz)
    rw [Complex.normSq_ofReal] at this
    nlinarith
  · intro h3
    refine ⟨genusTwoKrein q, genusTwoKrein_bornRule q, fun x hx => ?_⟩
    rw [genusTwoKrein_quad]
    have h1 := (traceOne_sq_le_iff hq).mpr h3
    have h2 := traceTwo_sq_le hq
    have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
    -- strict: at `q = 2, 3` neither trace is critical
    have s1 : traceOne q ^ 2 < 4 * q := by
      have hr := genusTwoRoot_gt hq
      have h := genusTwoRoot_sq q
      rcases (by omega : q = 2 ∨ q = 3) with rfl | rfl <;> unfold traceOne <;> push_cast at h hr ⊢ <;>
        nlinarith
    have s2 : traceTwo q ^ 2 < 4 * q := by
      have hr := genusTwoRoot_gt hq
      have h := genusTwoRoot_sq q
      unfold traceTwo
      nlinarith
    have pos (t : ℝ) (ht : t ^ 2 < 4 * q) (u v : ℝ) (huv : u ≠ 0 ∨ v ≠ 0) :
        0 < kreinSquare (q : ℝ) t u v := by
      rw [kreinSquare_eq_sum_sq ht.le]
      rcases huv with hu | hv
      · have : 0 < (Real.sqrt (q - t ^ 2 / 4) * u) ^ 2 := by
          have : 0 < Real.sqrt (q - t ^ 2 / 4) := Real.sqrt_pos.mpr (by linarith)
          positivity
        nlinarith [sq_nonneg (v - t * u / 2)]
      · by_cases hu : u = 0
        · subst hu
          simp only [mul_zero, sub_zero, zero_div]
          have : 0 < v ^ 2 := by positivity
          nlinarith [sq_nonneg (Real.sqrt (q - t ^ 2 / 4) * 0)]
        · have : 0 < (Real.sqrt (q - t ^ 2 / 4) * u) ^ 2 := by
            have : 0 < Real.sqrt (q - t ^ 2 / 4) := Real.sqrt_pos.mpr (by linarith)
            positivity
          nlinarith [sq_nonneg (v - t * u / 2)]
    have nn (t : ℝ) (ht : t ^ 2 < 4 * q) (u v : ℝ) : 0 ≤ kreinSquare (q : ℝ) t u v := by
      rw [kreinSquare_eq_sum_sq ht.le]
      positivity
    by_cases h01 : x 0 ≠ 0 ∨ x 1 ≠ 0
    · linarith [pos _ s1 _ _ h01, nn _ s2 (x 2) (x 3)]
    · push Not at h01
      have h23 : x 2 ≠ 0 ∨ x 3 ≠ 0 := by
        by_contra h23
        push Not at h23
        apply hx
        ext i
        fin_cases i <;> simp [h01.1, h01.2, h23.1, h23.2]
      linarith [pos _ s2 _ _ h23, nn _ s1 (x 0) (x 1)]

/-- **The count law selects the trace form.** The genus form of the level-`n` probes of the genus-two black
hole is the sum of the level-`n` Krein squares of its two oscillators: the member `c₁ = c₂` of the family
of Born rules. -/
theorem genusForm_eq_kreinSum (q n : ℕ) (x y : ℤ) :
    ((genusForm 2 ((q : ℤ) ^ n) (genusTwoTrace q n) x y : ℤ) : ℝ) =
      kreinSquare ((q : ℝ) ^ n) (towerTrace q (traceOne q) n) x y +
        kreinSquare ((q : ℝ) ^ n) (towerTrace q (traceTwo q) n) x y := by
  unfold genusForm kreinSquare
  push_cast
  rw [genusTwoTrace_cast]
  ring

/-! ### Every Born rule of genus two -/

/-- The weighted sum `c₁ 𝒬_{t₁} ⊕ c₂ 𝒬_{t₂}` of the Krein squares of the two oscillators. -/
def genusTwoKreinPair (q : ℕ) (c₁ c₂ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![c₁ * q, -(c₁ * traceOne q) / 2, 0, 0; -(c₁ * traceOne q) / 2, c₁, 0, 0;
    0, 0, c₂ * q, -(c₂ * traceTwo q) / 2; 0, 0, -(c₂ * traceTwo q) / 2, c₂]

theorem traceOne_ne_traceTwo {q : ℕ} (hq : 2 ≤ q) : traceOne q ≠ traceTwo q := by
  have hr := genusTwoRoot_gt hq
  unfold traceOne traceTwo
  intro h
  have hq' : (0 : ℝ) ≤ q := by positivity
  linarith

/-- **The Born rules of the genus-two black hole are the weighted sums of the two Krein squares.** A
symmetric form covariant under the delay pairs no echo of one oscillator with an echo of the other, and on
each oscillator it is a multiple of its Krein square. -/
theorem bornRule_genusTwo_eq {q : ℕ} (hq : 2 ≤ q) {S : Matrix (Fin 4) (Fin 4) ℝ} (hsym : Sᵀ = S)
    (h : IsBornRule S (genusTwoDelay q) q) : S = genusTwoKreinPair q (S 1 1) (S 3 3) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have ht := traceOne_ne_traceTwo hq
  have hs (i j : Fin 4) : S j i = S i j := by
    have := congrFun (congrFun hsym i) j
    rwa [Matrix.transpose_apply] at this
  have E (i j : Fin 4) : ((genusTwoDelay q)ᵀ * S * genusTwoDelay q) i j = q * S i j := by
    rw [h]
    simp
  have e00 := E 0 0
  have e01 := E 0 1
  have e02 := E 0 2
  have e03 := E 0 3
  have e12 := E 1 2
  have e13 := E 1 3
  have e22 := E 2 2
  have e23 := E 2 3
  simp [genusTwoDelay, Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e02 e03 e12 e13 e22 e23
  have s10 := hs 0 1
  have s32 := hs 2 3
  have f00 : S 0 0 = q * S 1 1 := mul_left_cancel₀ hq0 (by linear_combination -e00)
  have f01 : S 0 1 = -(S 1 1 * traceOne q) / 2 :=
    mul_left_cancel₀ hq0 (by linear_combination (-1 / 2 : ℝ) * e01 - ((q : ℝ) / 2) * s10)
  have f02 : S 0 2 = q * S 1 3 := mul_left_cancel₀ hq0 (by linear_combination -e02)
  have f03 : S 0 3 = -(S 1 3 * traceTwo q) - S 1 2 := mul_left_cancel₀ hq0 (by linear_combination -e03)
  have f12 : S 1 2 = -(S 0 3 + traceOne q * S 1 3) := mul_left_cancel₀ hq0 (by linear_combination -e12)
  have f22 : S 2 2 = q * S 3 3 := mul_left_cancel₀ hq0 (by linear_combination -e22)
  have f23 : S 2 3 = -(S 3 3 * traceTwo q) / 2 :=
    mul_left_cancel₀ hq0 (by linear_combination (-1 / 2 : ℝ) * e23 - ((q : ℝ) / 2) * s32)
  have h13 : S 1 3 = 0 := by
    have : (traceOne q - traceTwo q) * S 1 3 = 0 := by linear_combination f12 - f03
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht)
  have h02 : S 0 2 = 0 := by rw [f02, h13, mul_zero]
  have h12 : S 1 2 = 0 := by
    have : (traceOne q - traceTwo q) * S 1 2 = 0 := by
      linear_combination e13 - h02 - traceTwo q * f03 -
        (traceOne q * traceTwo q - q - traceTwo q ^ 2) * h13
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht)
  have h03 : S 0 3 = 0 := by rw [f03, h13, h12]; ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [genusTwoKreinPair] <;>
    linarith [hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3, f00, f01, h02, h03, h12, h13, f22, f23]

/-- **The positive Born rules of genus two.** A symmetric Born rule is positive iff both weights are
positive and both oscillators are damped. -/
theorem genusTwoKreinPair_positive_iff {q : ℕ} (hq : 2 ≤ q) {c₁ c₂ : ℝ} :
    IsPositive (genusTwoKreinPair q c₁ c₂) ↔
      0 < c₁ ∧ 0 < c₂ ∧ traceOne q ^ 2 < 4 * q ∧ traceTwo q ^ 2 < 4 * q := by
  have hquad (x : Fin 4 → ℝ) : x ⬝ᵥ genusTwoKreinPair q c₁ c₂ *ᵥ x =
      c₁ * kreinSquare (q : ℝ) (traceOne q) (x 0) (x 1) + c₂ * kreinSquare (q : ℝ) (traceTwo q) (x 2) (x 3) := by
    simp [genusTwoKreinPair, dotProduct, Matrix.mulVec, Fin.sum_univ_four, kreinSquare]
    ring
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  constructor
  · intro hpos
    have p1 := hpos ![0, 1, 0, 0] (by intro h; simpa using congrFun h 1)
    have p2 := hpos ![0, 0, 0, 1] (by intro h; simpa using congrFun h 3)
    have p3 := hpos ![2, traceOne q, 0, 0] (by intro h; simpa using congrFun h 0)
    have p4 := hpos ![0, 0, 2, traceTwo q] (by intro h; simpa using congrFun h 2)
    simp only [hquad] at p1 p2 p3 p4
    simp [kreinSquare] at p1 p2 p3 p4
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · have : 0 < c₁ * (4 * q - traceOne q ^ 2) := by nlinarith
      nlinarith [(pos_of_mul_pos_right this (by linarith : (0 : ℝ) ≤ c₁))]
    · have : 0 < c₂ * (4 * q - traceTwo q ^ 2) := by nlinarith
      nlinarith [(pos_of_mul_pos_right this (by linarith : (0 : ℝ) ≤ c₂))]
  · rintro ⟨h1, h2, s1, s2⟩ x hx
    rw [hquad]
    have pos (t : ℝ) (ht : t ^ 2 < 4 * q) (u v : ℝ) (huv : u ≠ 0 ∨ v ≠ 0) :
        0 < kreinSquare (q : ℝ) t u v := by
      rw [kreinSquare_eq_sum_sq ht.le]
      have hsq : 0 < Real.sqrt (q - t ^ 2 / 4) := Real.sqrt_pos.mpr (by linarith)
      rcases eq_or_ne u 0 with hu | hu
      · subst hu
        have hv : v ≠ 0 := huv.resolve_left (by simp)
        simp only [mul_zero, sub_zero, zero_div]
        have : 0 < v ^ 2 := by positivity
        nlinarith
      · have : 0 < (Real.sqrt (q - t ^ 2 / 4) * u) ^ 2 := by positivity
        nlinarith [sq_nonneg (v - t * u / 2)]
    have nn (t : ℝ) (ht : t ^ 2 < 4 * q) (u v : ℝ) : 0 ≤ kreinSquare (q : ℝ) t u v := by
      rw [kreinSquare_eq_sum_sq ht.le]
      positivity
    by_cases h01 : x 0 ≠ 0 ∨ x 1 ≠ 0
    · have := pos _ s1 _ _ h01
      have := nn _ s2 (x 2) (x 3)
      nlinarith
    · push Not at h01
      have h23 : x 2 ≠ 0 ∨ x 3 ≠ 0 := by
        by_contra h23
        push Not at h23
        apply hx
        ext i
        fin_cases i <;> simp [h01.1, h01.2, h23.1, h23.2]
      have := pos _ s2 _ _ h23
      have := nn _ s1 (x 0) (x 1)
      nlinarith

end GaloisForLFunctions.CountingHolography

end
