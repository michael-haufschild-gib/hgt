import GaloisForLFunctions.CountingHolography.TheCountLawAtEveryGenus
import GaloisForLFunctions.ArithmeticScatteringHolography.TheBlackHoleOfGenusTwo

/-!
# The genus-two rung

The 11-vertex black hole of genus two (`ArithmeticScatteringHolography.TheBlackHoleOfGenusTwo`) has the
functional equation of genus two for every `q`, and all its modes are on the critical circle exactly for
`q ≤ 3`. Its numerator factors as

  `L_q(z) = (z² - t₁ z + q)(z² - t₂ z + q)`,  `t₁ + t₂ = q - 2`,  `t₁ t₂ = 1 - 3q`,

so the trace of level `n` is the integer `a_n = V_n(t₁) + V_n(t₂)` (`genusTwoTrace_cast`), a sum of
two base-change towers. The channel numbers of level `n` are `2`, `2qⁿ`, `2(qⁿ + 1) - a_n`.

**The rung is decided.**

* At the first level a count law exists exactly for `q ≤ 19` (`genusTwo_firstLevel_iff`): the bound
  `(q - 2)² ≤ 16 q` of a genus-two curve.
* At every level it exists exactly for `q ≤ 3` (`genusTwo_tower_iff`), where the modes are damped.

So for `4 ≤ q ≤ 19` the graph has integral mode data, the functional equation, the sharp number of
trivial zeros and the count law at the first level, and a slow resonance
(`firstCountLaw_does_not_force_damping`). At genus one the first level is the whole law; from genus two
on the count law has to hold at every level, and it does exactly when the black hole is critical.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography

/-! ### The traces of the genus-two black hole -/

/-- The level-`n` trace of the genus-two black hole: the power sums of the roots of `L_q`, by Newton's
recurrence `a_{n+4} = (q-2) a_{n+3} + (q-1) a_{n+2} + q(q-2) a_{n+1} - q² a_n`. -/
def genusTwoTrace (q : ℤ) : ℕ → ℤ
  | 0 => 4
  | 1 => q - 2
  | 2 => q ^ 2 - 2 * q + 2
  | 3 => (q - 2) * (q + 1) ^ 2
  | n + 4 => (q - 2) * genusTwoTrace q (n + 3) + (q - 1) * genusTwoTrace q (n + 2) +
      q * (q - 2) * genusTwoTrace q (n + 1) - q ^ 2 * genusTwoTrace q n

/-- `√(q² + 8q)`, the discriminant of the two traces. -/
def genusTwoRoot (q : ℕ) : ℝ := Real.sqrt ((q : ℝ) ^ 2 + 8 * q)

/-- The fast trace `t₁ = (q - 2 + √(q² + 8q))/2`. -/
def traceOne (q : ℕ) : ℝ := ((q : ℝ) - 2 + genusTwoRoot q) / 2

/-- The slow trace `t₂ = (q - 2 - √(q² + 8q))/2`. -/
def traceTwo (q : ℕ) : ℝ := ((q : ℝ) - 2 - genusTwoRoot q) / 2

theorem genusTwoRoot_sq (q : ℕ) : genusTwoRoot q ^ 2 = (q : ℝ) ^ 2 + 8 * q :=
  Real.sq_sqrt (by positivity)

theorem genusTwoRoot_nonneg (q : ℕ) : 0 ≤ genusTwoRoot q := Real.sqrt_nonneg _

theorem traceOne_add_traceTwo (q : ℕ) : traceOne q + traceTwo q = (q : ℝ) - 2 := by
  unfold traceOne traceTwo
  ring

theorem traceOne_mul_traceTwo (q : ℕ) : traceOne q * traceTwo q = 1 - 3 * (q : ℝ) := by
  unfold traceOne traceTwo
  linear_combination (-1 / 4 : ℝ) * genusTwoRoot_sq q

/-- **`L_q` is the product of two oscillators.** -/
theorem genusTwoL_eq_factors (q : ℕ) (z : ℂ) :
    (genusTwoL q).eval z = (z ^ 2 - (traceOne q : ℂ) * z + q) * (z ^ 2 - (traceTwo q : ℂ) * z + q) :=
  genusTwoL_factor (by exact_mod_cast traceOne_add_traceTwo q)
    (by exact_mod_cast traceOne_mul_traceTwo q) z

/-- Each tower trace obeys the recurrence of `L_q`. -/
theorem towerTrace_genusTwo_step {q : ℕ} {t t' : ℝ} (hs : t + t' = (q : ℝ) - 2)
    (hp : t * t' = 1 - 3 * (q : ℝ)) (n : ℕ) :
    towerTrace q t (n + 4) = ((q : ℝ) - 2) * towerTrace q t (n + 3) +
      ((q : ℝ) - 1) * towerTrace q t (n + 2) + q * ((q : ℝ) - 2) * towerTrace q t (n + 1) -
        (q : ℝ) ^ 2 * towerTrace q t n := by
  have e4 := towerTrace_add_two q t (n + 2)
  have e3 := towerTrace_add_two q t (n + 1)
  have e2 := towerTrace_add_two q t n
  linear_combination e4 - t' * e3 + q * e2 +
    (towerTrace q t (n + 3) + q * towerTrace q t (n + 1)) * hs - towerTrace q t (n + 2) * hp

/-- **The traces are the sum of two base-change towers.** -/
theorem genusTwoTrace_cast (q n : ℕ) :
    (genusTwoTrace q n : ℝ) = towerTrace q (traceOne q) n + towerTrace q (traceTwo q) n := by
  have hs := traceOne_add_traceTwo q
  have hp := traceOne_mul_traceTwo q
  have hs' : traceTwo q + traceOne q = (q : ℝ) - 2 := by linarith
  have hp' : traceTwo q * traceOne q = 1 - 3 * (q : ℝ) := by linarith
  set u := towerTrace q (traceOne q)
  set w := towerTrace q (traceTwo q)
  have hu := towerTrace_genusTwo_step hs hp
  have hw := towerTrace_genusTwo_step hs' hp'
  have h2 (t : ℝ) : towerTrace q t 2 = t ^ 2 - 2 * q := towerTrace_two q t
  have h3 (t : ℝ) : towerTrace q t 3 = t ^ 3 - 3 * q * t := by
    rw [towerTrace_add_two, h2]
    simp only [towerTrace]
    ring
  suffices H : ∀ m, (genusTwoTrace q m : ℝ) = u m + w m ∧
      (genusTwoTrace q (m + 1) : ℝ) = u (m + 1) + w (m + 1) ∧
      (genusTwoTrace q (m + 2) : ℝ) = u (m + 2) + w (m + 2) ∧
      (genusTwoTrace q (m + 3) : ℝ) = u (m + 3) + w (m + 3) from (H n).1
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [genusTwoTrace, u, w, towerTrace]
      norm_num
    · simp only [genusTwoTrace, u, w, towerTrace]
      push_cast
      linarith
    · simp only [genusTwoTrace, u, w, h2]
      push_cast
      have : traceOne q ^ 2 + traceTwo q ^ 2 = ((q : ℝ) - 2) ^ 2 - 2 * (1 - 3 * q) := by
        rw [← hs, ← hp]
        ring
      linarith
    · simp only [genusTwoTrace, u, w, h3]
      push_cast
      have : traceOne q ^ 3 + traceTwo q ^ 3 =
          ((q : ℝ) - 2) ^ 3 - 3 * (1 - 3 * q) * ((q : ℝ) - 2) := by
        rw [← hs, ← hp]
        ring
      linear_combination (-1 : ℝ) * this + 3 * (q : ℝ) * hs
  | succ m ih =>
    obtain ⟨h0, h1, h2', h3'⟩ := ih
    refine ⟨h1, h2', h3', ?_⟩
    have e : genusTwoTrace q (m + 1 + 3) = ((q : ℤ) - 2) * genusTwoTrace q (m + 3) +
        ((q : ℤ) - 1) * genusTwoTrace q (m + 2) + q * ((q : ℤ) - 2) * genusTwoTrace q (m + 1) -
          (q : ℤ) ^ 2 * genusTwoTrace q m := rfl
    rw [e]
    push_cast
    rw [h0, h1, h2', h3']
    simp only [u, w]
    rw [show m + 1 + 3 = m + 4 by ring, hu m, hw m]
    ring

/-! ### The two traces -/

theorem genusTwoRoot_gt {q : ℕ} (hq : 2 ≤ q) : (q : ℝ) + 2 < genusTwoRoot q := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h := genusTwoRoot_sq q
  have h0 := genusTwoRoot_nonneg q
  nlinarith

/-- The slow factor is always on the circle. -/
theorem traceTwo_sq_le {q : ℕ} (hq : 2 ≤ q) : traceTwo q ^ 2 ≤ 4 * (q : ℝ) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hr := genusTwoRoot_gt hq
  have h := genusTwoRoot_sq q
  unfold traceTwo
  nlinarith

/-- The fast factor is on the circle exactly for `q ≤ 3`. -/
theorem traceOne_sq_le_iff {q : ℕ} (hq : 2 ≤ q) : traceOne q ^ 2 ≤ 4 * (q : ℝ) ↔ q ≤ 3 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hr := genusTwoRoot_gt hq
  have h := genusTwoRoot_sq q
  have h0 := genusTwoRoot_nonneg q
  constructor
  · intro hle
    by_contra h3
    have hq4 : (4 : ℝ) ≤ q := by exact_mod_cast (by omega : 4 ≤ q)
    have ht : (q : ℝ) < traceOne q := by unfold traceOne; linarith
    nlinarith
  · intro h3
    unfold traceOne
    rcases (by omega : q = 2 ∨ q = 3) with rfl | rfl
    · push_cast at h hr ⊢
      nlinarith
    · push_cast at h hr ⊢
      nlinarith

/-- An oscillator on the circle has `|V_n| ≤ 2 qⁿᐟ²`. -/
theorem abs_towerTrace_le {q t : ℝ} (h : t ^ 2 ≤ 4 * q) (n : ℕ) :
    |towerTrace q t n| ≤ 2 * Real.sqrt q ^ n := by
  obtain ⟨α, β, hs, hp, hna, hnb⟩ := exists_roots_on_circle h
  have hc := towerTrace_roots hs hp n
  have : ‖((towerTrace q t n : ℝ) : ℂ)‖ ≤ ‖α ^ n‖ + ‖β ^ n‖ := by
    rw [hc]
    exact norm_add_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs, _root_.norm_pow, _root_.norm_pow, hna, hnb] at this
  linarith

/-! ### The rung -/

/-- The count law at level `n` is the Weil bound `a_n² ≤ 16 qⁿ`. -/
theorem genusTwo_level_iff (q n : ℕ) :
    (∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ (K 0 1 : ℤ) = 2 ∧ (K 1 0 : ℤ) = 2 * (q : ℤ) ^ n ∧
      (K 1 1 : ℤ) = 2 * ((q : ℤ) ^ n + 1) - genusTwoTrace q n) ↔
      genusTwoTrace q n ^ 2 ≤ 16 * (q : ℤ) ^ n := by
  rw [exists_genusCountLaw_iff (by norm_num : (0 : ℤ) < 2)]
  constructor <;> intro h <;> linarith

/-- **The first level: a count law exists exactly for `q ≤ 19`.** -/
theorem genusTwo_firstLevel_iff {q : ℕ} (hq : 2 ≤ q) :
    (∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ (K 0 1 : ℤ) = 2 ∧ (K 1 0 : ℤ) = 2 * (q : ℤ) ^ 1 ∧
      (K 1 1 : ℤ) = 2 * ((q : ℤ) ^ 1 + 1) - genusTwoTrace q 1) ↔ q ≤ 19 := by
  rw [genusTwo_level_iff]
  simp only [genusTwoTrace, pow_one]
  constructor
  · intro h
    by_contra h19
    have : (20 : ℤ) ≤ q := by exact_mod_cast (by omega : 20 ≤ q)
    nlinarith
  · intro h
    have h' : (q : ℤ) ≤ 19 := by exact_mod_cast h
    have h2 : (2 : ℤ) ≤ q := by exact_mod_cast hq
    nlinarith

/-- **The tower: a count law at every level exists exactly for `q ≤ 3`**, where the modes are damped. -/
theorem genusTwo_tower_iff {q : ℕ} (hq : 2 ≤ q) :
    (∀ n, 1 ≤ n → ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ (K 0 1 : ℤ) = 2 ∧ (K 1 0 : ℤ) = 2 * (q : ℤ) ^ n ∧
      (K 1 1 : ℤ) = 2 * ((q : ℤ) ^ n + 1) - genusTwoTrace q n) ↔ q ≤ 3 := by
  simp only [genusTwo_level_iff]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hsq : ∀ n : ℕ, (Real.sqrt q ^ n) ^ 2 = (q : ℝ) ^ n := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hq0.le]
  have hr (n : ℕ) : 0 ≤ Real.sqrt q ^ n := by positivity
  -- the level bound in real form
  have hreal (n : ℕ) : genusTwoTrace q n ^ 2 ≤ 16 * (q : ℤ) ^ n ↔
      |towerTrace q (traceOne q) n + towerTrace q (traceTwo q) n| ≤ 4 * Real.sqrt q ^ n := by
    have hb : 0 ≤ 4 * Real.sqrt q ^ n := by positivity
    have e : |(genusTwoTrace q n : ℝ)| ≤ 4 * Real.sqrt q ^ n ↔
        ((genusTwoTrace q n : ℝ)) ^ 2 ≤ 16 * (q : ℝ) ^ n := by
      rw [← sq_le_sq₀ (abs_nonneg _) hb, sq_abs, mul_pow, hsq]
      norm_num
    rw [← genusTwoTrace_cast, e]
    constructor <;> intro h <;> exact_mod_cast h
  simp only [hreal]
  have hslow := abs_towerTrace_le (traceTwo_sq_le hq)
  constructor
  · intro h
    rw [← traceOne_sq_le_iff hq, ← tower_bound_iff hq0]
    refine ⟨6, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [towerTrace]
      norm_num
    · have h1 := h n hn
      have h2 := hslow n
      have := abs_add_le (towerTrace q (traceOne q) n + towerTrace q (traceTwo q) n)
        (-towerTrace q (traceTwo q) n)
      rw [abs_neg, add_neg_cancel_right] at this
      linarith
  · intro h3 n _
    have hfast := abs_towerTrace_le ((traceOne_sq_le_iff hq).mpr h3) n
    calc |towerTrace q (traceOne q) n + towerTrace q (traceTwo q) n|
        ≤ |towerTrace q (traceOne q) n| + |towerTrace q (traceTwo q) n| := abs_add_le _ _
      _ ≤ 4 * Real.sqrt q ^ n := by linarith [hslow n]

/-- **The first count law does not force damping at genus two.** For `4 ≤ q ≤ 19` the black hole has the
functional equation of genus two, the count law at the first level and a resonance off the critical
circle, and the count law fails at some level. -/
theorem firstCountLaw_does_not_force_damping {q : ℕ} (h4 : 4 ≤ q) (h19 : q ≤ 19) :
    (∀ w : ℂ, w ≠ 0 → (genusTwoL q).reverse.eval w =
        ((q : ℂ) * w ^ 2) ^ 2 * (genusTwoL q).reverse.eval (1 / ((q : ℂ) * w))) ∧
      (∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ (K 0 1 : ℤ) = 2 ∧ (K 1 0 : ℤ) = 2 * (q : ℤ) ^ 1 ∧
        (K 1 1 : ℤ) = 2 * ((q : ℤ) ^ 1 + 1) - genusTwoTrace q 1) ∧
      (∃ z : ℂ, (genusTwoL q).eval z = 0 ∧ Complex.normSq z ≠ q) ∧
      ∃ n, 1 ≤ n ∧ ¬ ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ (K 0 1 : ℤ) = 2 ∧
        (K 1 0 : ℤ) = 2 * (q : ℤ) ^ n ∧ (K 1 1 : ℤ) = 2 * ((q : ℤ) ^ n + 1) - genusTwoTrace q n := by
  refine ⟨genusTwoL_functional_equation (by omega), (genusTwo_firstLevel_iff (by omega)).mpr h19,
    ?_, ?_⟩
  · by_contra h
    push Not at h
    have := (genusTwo_critical_iff (q := q) (by omega)).mp h
    omega
  · by_contra h
    push Not at h
    have := (genusTwo_tower_iff (q := q) (by omega)).mp h
    omega

end GaloisForLFunctions.CountingHolography

end
