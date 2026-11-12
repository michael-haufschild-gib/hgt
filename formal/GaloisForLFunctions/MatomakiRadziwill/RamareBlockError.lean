import GaloisForLFunctions.MatomakiRadziwill.RamareBlocks

/-!
# The error of Ramaré's block decomposition

Coefficients `a(n) = f(n)/n` and `c(m) = f(m)/((ω(m)+1)m)` for a completely multiplicative
`|f| ≤ 1`.  The rough set is `S = {X < n ≤ 4X : n ∈ rest, ω(n) ≥ 1}` and the block decomposition is
`Σ_{p ∈ Pr} Σ_{m ∈ cof(blk p)} a(p)c(m) (pm)^{2πiw}` (`pairPoly`).  Reindexing by `n = pm`
(`pairPoly_eq_sum`), the difference with `Σ_{n ∈ S} a(n) n^{2πiw}` has coefficient (`errCoef`)

`e(n) = 1_S(n) a(n) − Σ_{p ∈ Pr, p ∣ n, n/p ∈ cof(blk p)} a(p) c(n/p)`,

and (`norm_errCoef_le`, `errCoef_eq_zero`)

* `|e(n)| ≤ 2/n` always (Ramaré's weights sum to at most one);
* `e(n) = 0` unless `X < n ≤ Xe^{1/H}`, or `4X < n < 4Xe^{1/H}`, or `p² ∣ n` for some `p ∈ Pr`:
  on the interior every factorisation is seen (`div_mem_cof`) and Ramaré's identity is exact.
-/

open Finset

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

open RHTower.Sieve

/-- `a(n) = f(n)/n`. -/
def coefA (f : ℕ → ℂ) (n : ℕ) : ℂ := f n / n

/-- `c(m) = f(m)/((ω(m)+1)m)`. -/
def coefC (f : ℕ → ℂ) (Pr : Finset ℕ) (m : ℕ) : ℂ := f m / (((omegaIn Pr m : ℝ) + 1) * m)

/-- The rough set of the scale: `X < n ≤ 4X`, `n ∈ rest`, `ω(n) ≥ 1`. -/
def roughSet (rest : ℕ → Prop) [DecidablePred rest] (Pr : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Ioc X (4 * X)).filter fun n => rest n ∧ 1 ≤ omegaIn Pr n

/-- The block decomposition, as a double sum. -/
def pairPoly (f : ℕ → ℂ) (Pr : Finset ℕ) (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ)
    (w : ℝ) : ℂ :=
  ∑ p ∈ Pr, ∑ m ∈ cof rest X H (blk H p), coefA f p * coefC f Pr m * unitLogPhase w (p * m)

/-- The primes of the scale through which `n` is seen by the decomposition. -/
def seenBy (Pr : Finset ℕ) (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ) (n : ℕ) :
    Finset ℕ :=
  Pr.filter fun p => p ∣ n ∧ n / p ∈ cof rest X H (blk H p)

/-- The coefficient of the decomposition error. -/
def errCoef (f : ℕ → ℂ) (Pr : Finset ℕ) (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ)
    (n : ℕ) : ℂ :=
  (if n ∈ roughSet rest Pr X then coefA f n else 0)
    - ∑ p ∈ seenBy Pr rest X H n, coefA f p * coefC f Pr (n / p)

theorem norm_coefA_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) : ‖coefA f n‖ ≤ 1 / n := by
  rw [coefA, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (hf n) (Nat.cast_nonneg n)

/-- `|a(p) c(n/p)| ≤ 1/(n(ω(n/p)+1))` for `p ∣ n`. -/
theorem norm_coefA_mul_coefC_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (Pr : Finset ℕ) {p n : ℕ}
    (hp : 0 < p) (hpn : p ∣ n) (hn : 0 < n) :
    ‖coefA f p * coefC f Pr (n / p)‖ ≤ 1 / ((n : ℝ) * ((omegaIn Pr (n / p) : ℝ) + 1)) := by
  obtain ⟨k, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left k hp]
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hw : (0 : ℝ) < (omegaIn Pr k : ℝ) + 1 := by positivity
  rw [coefA, coefC, norm_mul, norm_div, norm_div, Complex.norm_natCast, norm_mul,
    Complex.norm_natCast]
  have hnorm : ‖(((omegaIn Pr k : ℝ) + 1 : ℝ) : ℂ)‖ = (omegaIn Pr k : ℝ) + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  push_cast at hnorm ⊢
  rw [hnorm]
  have h1 : ‖f p‖ / (p : ℝ) ≤ 1 / p := div_le_div_of_nonneg_right (hf p) hp0.le
  have h2 : ‖f k‖ / (((omegaIn Pr k : ℝ) + 1) * k) ≤ 1 / (((omegaIn Pr k : ℝ) + 1) * k) :=
    div_le_div_of_nonneg_right (hf k) (by positivity)
  calc ‖f p‖ / (p : ℝ) * (‖f k‖ / (((omegaIn Pr k : ℝ) + 1) * k))
      ≤ 1 / p * (1 / (((omegaIn Pr k : ℝ) + 1) * k)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 1 / ((p * k : ℝ) * ((omegaIn Pr k : ℝ) + 1)) := by field_simp

/-- **The error coefficients are at most `2/n`.** -/
theorem norm_errCoef_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {Pr : Finset ℕ}
    (hPr : ∀ q ∈ Pr, q.Prime) (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ) {n : ℕ}
    (hn : 0 < n) : ‖errCoef f Pr rest X H n‖ ≤ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ‖(if n ∈ roughSet rest Pr X then coefA f n else 0)‖ ≤ 1 / n := by
    split_ifs
    · exact norm_coefA_le hf n
    · rw [norm_zero]; positivity
  have hsub : seenBy Pr rest X H n ⊆ Pr.filter (· ∣ n) := by
    intro p hp
    rw [seenBy, mem_filter] at hp
    rw [mem_filter]
    exact ⟨hp.1, hp.2.1⟩
  have h2 : ‖∑ p ∈ seenBy Pr rest X H n, coefA f p * coefC f Pr (n / p)‖ ≤ 1 / n := by
    calc ‖∑ p ∈ seenBy Pr rest X H n, coefA f p * coefC f Pr (n / p)‖
        ≤ ∑ p ∈ seenBy Pr rest X H n, ‖coefA f p * coefC f Pr (n / p)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Pr.filter (· ∣ n), ‖coefA f p * coefC f Pr (n / p)‖ :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _
      _ ≤ ∑ p ∈ Pr.filter (· ∣ n), 1 / ((n : ℝ) * ((omegaIn Pr (n / p) : ℝ) + 1)) := by
          refine sum_le_sum fun p hp => ?_
          rw [mem_filter] at hp
          exact norm_coefA_mul_coefC_le hf Pr (hPr p hp.1).pos hp.2 hn
      _ = (1 / n) * ∑ p ∈ Pr.filter (· ∣ n), (1 : ℝ) / ((omegaIn Pr (n / p) : ℝ) + 1) := by
          rw [mul_sum]
          refine sum_congr rfl fun p _ => ?_
          field_simp
      _ ≤ (1 / n) * 1 :=
          mul_le_mul_of_nonneg_left (sum_inv_omegaIn_div_le_one hPr n) (by positivity)
      _ = 1 / n := mul_one _
  calc ‖errCoef f Pr rest X H n‖ ≤ 1 / n + 1 / n := by
        rw [errCoef]
        exact le_trans (norm_sub_le _ _) (add_le_add h1 h2)
    _ = 2 / n := by ring

/-- On a prime `p ∣ n`: `a(p) c(n/p) = a(n)/(ω(n/p)+1)` (complete multiplicativity). -/
theorem coefA_mul_coefC_eq {f : ℕ → ℂ} (hmul : ∀ a b, f (a * b) = f a * f b) (Pr : Finset ℕ)
    {p n : ℕ} (hp : 0 < p) (hpn : p ∣ n) (hn : 0 < n) :
    coefA f p * coefC f Pr (n / p)
      = coefA f n * (((1 : ℝ) / ((omegaIn Pr (n / p) : ℝ) + 1) : ℝ) : ℂ) := by
  obtain ⟨k, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left k hp]
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hw : ((omegaIn Pr k : ℝ) + 1 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (omegaIn Pr k : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  rw [coefA, coefC, coefA, hmul]
  push_cast
  field_simp

/-- **The error vanishes off the boundary and the squareful integers.** -/
theorem errCoef_eq_zero {f : ℕ → ℂ} (hmul : ∀ a b, f (a * b) = f a * f b) {Pr : Finset ℕ}
    (hPr : ∀ q ∈ Pr, q.Prime) {rest : ℕ → Prop} [DecidablePred rest]
    (hrest : ∀ p ∈ Pr, ∀ m, rest (p * m) ↔ rest m) {X : ℕ} {H : ℝ} (hH : 0 < H) {n : ℕ}
    (hn : 0 < n)
    (hgood : (n : ℝ) ≤ X ∨ ((X : ℝ) * Real.exp (1 / H) < n ∧ (n : ℝ) ≤ 4 * X ∧
      ∀ p ∈ Pr, ¬ p ^ 2 ∣ n) ∨ 4 * X * Real.exp (1 / H) ≤ n) :
    errCoef f Pr rest X H n = 0 := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he1 : 1 ≤ Real.exp (1 / H) := Real.one_le_exp (by positivity)
  -- `p ∈ seenBy` forces `X < n < 4Xe^{1/H}` and `rest n`
  have hseen : ∀ p ∈ seenBy Pr rest X H n,
      (X : ℝ) < n ∧ (n : ℝ) < 4 * X * Real.exp (1 / H) ∧ rest n := by
    intro p hp
    rw [seenBy, mem_filter] at hp
    obtain ⟨hpPr, hpn, hm⟩ := hp
    have hp1 : 1 ≤ p := (hPr p hpPr).one_lt.le
    have h1 := lt_mul_of_mem_cof hH hp1 hm
    have h2 := mul_lt_of_mem_cof hH hp1 hm
    rw [Nat.mul_div_cancel' hpn] at h1 h2
    have hr : rest n := by
      have := (hrest p hpPr (n / p)).mpr (mem_cof.mp hm).2.2
      rwa [Nat.mul_div_cancel' hpn] at this
    exact ⟨h1, h2, hr⟩
  have hrough : n ∈ roughSet rest Pr X → (X : ℝ) < n ∧ (n : ℝ) ≤ 4 * X ∧ rest n ∧
      1 ≤ omegaIn Pr n := by
    intro h
    rw [roughSet, mem_filter, mem_Ioc] at h
    refine ⟨by exact_mod_cast h.1.1, by exact_mod_cast h.1.2, h.2.1, h.2.2⟩
  rcases hgood with hlow | ⟨hlo, hup, hsq⟩ | hhigh
  · -- below `X`: nothing
    have hS : n ∉ roughSet rest Pr X := fun h => by linarith [(hrough h).1]
    have hE : seenBy Pr rest X H n = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro p hp
      linarith [(hseen p hp).1]
    rw [errCoef, if_neg hS, hE, sum_empty, sub_zero]
  · -- the interior
    by_cases hr : rest n
    · have hall : seenBy Pr rest X H n = Pr.filter (· ∣ n) := by
        ext p
        rw [seenBy, mem_filter, mem_filter]
        constructor
        · rintro ⟨hp, hpn, -⟩; exact ⟨hp, hpn⟩
        · rintro ⟨hp, hpn⟩
          exact ⟨hp, hpn, div_mem_cof hrest hH hp (hPr p hp).one_lt.le hpn hlo hup hr⟩
      by_cases hω : 1 ≤ omegaIn Pr n
      · have hXlt : (X : ℝ) < n := lt_of_le_of_lt (by
          have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
          nlinarith) hlo
        have hS : n ∈ roughSet rest Pr X := by
          rw [roughSet, mem_filter, mem_Ioc]
          exact ⟨⟨by exact_mod_cast hXlt, by exact_mod_cast hup⟩, hr, hω⟩
        have hsum : ∑ p ∈ Pr.filter (· ∣ n), coefA f p * coefC f Pr (n / p) = coefA f n := by
          rw [sum_congr rfl fun p hp => coefA_mul_coefC_eq hmul Pr (hPr p (mem_filter.mp hp).1).pos
            (mem_filter.mp hp).2 hn, ← mul_sum, ← Complex.ofReal_sum,
            sum_inv_omegaIn_div_eq_one hPr hω hsq, Complex.ofReal_one, mul_one]
        rw [errCoef, if_pos hS, hall, hsum, sub_self]
      · have hS : n ∉ roughSet rest Pr X := fun h => hω (hrough h).2.2.2
        have hE : Pr.filter (· ∣ n) = ∅ := by
          have h0 : omegaIn Pr n = 0 := by omega
          exact card_eq_zero.mp h0
        rw [errCoef, if_neg hS, hall, hE, sum_empty, sub_zero]
    · have hS : n ∉ roughSet rest Pr X := fun h => hr (hrough h).2.2.1
      have hE : seenBy Pr rest X H n = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro p hp
        exact hr (hseen p hp).2.2
      rw [errCoef, if_neg hS, hE, sum_empty, sub_zero]
  · -- above `4Xe^{1/H}`: nothing
    have hS : n ∉ roughSet rest Pr X := by
      intro h
      obtain ⟨hXn, hn4, -, -⟩ := hrough h
      have hX0 : (0 : ℝ) < X := by linarith
      have : 4 * (X : ℝ) < 4 * X * Real.exp (1 / H) := by
        have he : 1 < Real.exp (1 / H) := Real.one_lt_exp_iff.mpr (by positivity)
        nlinarith
      linarith
    have hE : seenBy Pr rest X H n = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro p hp
      linarith [(hseen p hp).2.1]
    rw [errCoef, if_neg hS, hE, sum_empty, sub_zero]

end

end GaloisForLFunctions.MatomakiRadziwill
