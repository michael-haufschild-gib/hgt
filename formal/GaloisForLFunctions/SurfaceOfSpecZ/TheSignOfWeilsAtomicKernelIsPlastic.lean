import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanFrobeniusHasInfiniteRank

/-!
# The sign of Weil's atomic kernel is decided at the plastic ratio

Between atoms at `log m` and `log n`, `m ≠ n`, Weil's distribution is
`W(m, n) = C_∞(m, n) − P(m, n)` (`weilDeltaKernel`): the archimedean compensation (pole plane minus
cusp and jets) minus the prime kernel `P(m, n) = Λ(n/m)(n/m)^{−1/2}` (`m ∣ n`).

**The plastic law** (`weilDeltaKernel_neg_iff`, `weilDeltaKernel_pos_iff`,
`weilDeltaKernel_ne_zero`). For `0 < m < n`,

  `W(m, n) < 0 ⟺ n³ < n m² + m³ ⟺ n/m < ρ`,   `W(m, n) > 0 ⟺ n/m > ρ`,

with `ρ³ = ρ + 1` the plastic number, and `W(m, n) ≠ 0`. The primes never change the sign: at a
ratio `x = n/m ∈ ℕ` the compensation is `(x³ − x − 1)/((x² − 1)√x) > (x − 1)/√x ≥ Λ(x)/√x`
(`prime_lt_archCompensation`). The sign of Weil's off-diagonal kernel on integer atoms is set by the
archimedean place alone.

**The first Beurling–Deny criterion holds exactly on plastic windows**
(`atomForm_abs_le_iff`). For a finite set `S` of positive integers and any diagonal `d`, the form
`Q(x) = Σ_{i,j ∈ S} K(i, j) x_i x_j` with `K(i, i) = d_i`, `K(i, j) = W(i, j)` satisfies
`Q(|x|) ≤ Q(x)` for every diagonal and every `x` iff every pair of `S` lies within the plastic ratio.
Inside such a window the ground states of every diagonal completion can be taken nonnegative (the
Perron–Markov property); a single pair beyond the ratio breaks it. This is the atomic form of the
aperture `log ρ` past which Markov and Perron arguments for the window form fail.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory

theorem cube_sub_pos {x : ℝ} (hx : 2 ≤ x) : 0 < x ^ 3 - x - 1 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by positivity : (0 : ℝ) ≤ x ^ 2 + 2 * x + 3)]

theorem weilPrimeKernel_symm' (m n : ℕ) : weilPrimeKernel m n = weilPrimeKernel n m := by
  unfold weilPrimeKernel
  by_cases h1 : m ∣ n ∧ m ≠ n
  · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
    rw [if_pos h1, if_neg h2, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : n ∣ m ∧ n ≠ m
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_neg h1]

theorem archCompensation_symm (m n : ℕ) : archCompensation m n = archCompensation n m := by
  unfold archCompensation
  rw [abs_sub_comm, show (Real.log n - Real.log m) / 2 = -((Real.log m - Real.log n) / 2) by ring,
    Real.cosh_neg]

theorem weilDeltaKernel_symm (m n : ℕ) : weilDeltaKernel m n = weilDeltaKernel n m := by
  rw [weilDeltaKernel_eq, weilDeltaKernel_eq, archCompensation_symm, weilPrimeKernel_symm']

/-- **The primes never beat the compensation.** At an integral ratio `x = n/m ≥ 2`, `P(m, n) < C_∞(m, n)`. -/
theorem prime_lt_archCompensation {m n : ℕ} (hm : 0 < m) (hmn : m < n) (hdvd : m ∣ n) :
    weilPrimeKernel m n < archCompensation m n := by
  obtain ⟨x, rfl⟩ := hdvd
  have hx2 : 2 ≤ x := by
    rcases Nat.lt_or_ge x 2 with h | h
    · interval_cases x <;> omega
    · exact h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < x := by linarith
  have hP : weilPrimeKernel m (m * x) = Λ x / Real.sqrt x := by
    unfold weilPrimeKernel
    rw [if_pos ⟨dvd_mul_right m x, by omega⟩, Nat.mul_div_cancel_left x hm]
  have hC := sqrt_mul_archCompensation_eq_cubic hm hmn
  have hsq : Real.sqrt ((m : ℝ) * ((m * x : ℕ) : ℝ)) = m * Real.sqrt x := by
    rw [Nat.cast_mul, ← mul_assoc, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hm'.le]
  have hsx : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  -- `√(mn) C_∞ = m (x³ − x − 1)/(x² − 1)`
  have hd : (x : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hC' : archCompensation m (m * x) = ((x : ℝ) ^ 3 - x - 1) / (((x : ℝ) ^ 2 - 1) * Real.sqrt x) := by
    rw [hsq] at hC
    push_cast at hC
    have hd' : ((m : ℝ) * x) ^ 2 - (m : ℝ) ^ 2 = (m : ℝ) ^ 2 * ((x : ℝ) ^ 2 - 1) := by ring
    have hn3 : ((m : ℝ) * x) ^ 3 - m * x * (m : ℝ) ^ 2 - (m : ℝ) ^ 3 = (m : ℝ) ^ 3 * ((x : ℝ) ^ 3 - x - 1) := by
      ring
    rw [hd', hn3] at hC
    field_simp at hC ⊢
    nlinarith [hC]
  rw [hP, hC', div_lt_div_iff₀ hsx (mul_pos (by nlinarith) hsx)]
  -- `Λ(x) ≤ log x ≤ x − 1 < (x³ − x − 1)/(x² − 1)`
  have hΛ : Λ x ≤ (x : ℝ) - 1 :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_sub_one_of_pos hxpos)
  have hkey : ((x : ℝ) - 1) * ((x : ℝ) ^ 2 - 1) < (x : ℝ) ^ 3 - x - 1 := by nlinarith
  have hΛ0 : 0 ≤ Λ x := ArithmeticFunction.vonMangoldt_nonneg
  have hx21 : 0 < (x : ℝ) ^ 2 - 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hΛ hx21.le, Real.mul_self_sqrt hxpos.le]

/-- **Below the plastic ratio Weil's atomic kernel is negative.** -/
theorem weilDeltaKernel_neg_iff {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    weilDeltaKernel m n < 0 ↔ (n : ℝ) ^ 3 < n * m ^ 2 + m ^ 3 := by
  rw [weilDeltaKernel_eq]
  by_cases hdvd : m ∣ n
  · have hlt := prime_lt_archCompensation hm hmn hdvd
    obtain ⟨x, rfl⟩ := hdvd
    have hx2 : (2 : ℝ) ≤ x := by
      have : 2 ≤ x := by
        rcases Nat.lt_or_ge x 2 with h | h
        · interval_cases x <;> omega
        · exact h
      exact_mod_cast this
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    constructor
    · intro h; linarith
    · intro h
      exfalso
      push_cast at h
      have : ((m : ℝ) * x) ^ 3 - m * x * (m : ℝ) ^ 2 - (m : ℝ) ^ 3 =
          (m : ℝ) ^ 3 * ((x : ℝ) ^ 3 - x - 1) := by ring
      nlinarith [mul_pos (pow_pos hm' 3) (cube_sub_pos hx2)]
  · have hP : weilPrimeKernel m n = 0 := by
      unfold weilPrimeKernel
      rw [if_neg (fun h => hdvd h.1), if_neg (fun h => by
        have := Nat.le_of_dvd hm h.1; omega)]
    rw [hP, sub_zero]
    exact archCompensation_neg_iff hm hmn

/-- **Above the plastic ratio Weil's atomic kernel is positive**, prime ratios included. -/
theorem weilDeltaKernel_pos_iff {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    0 < weilDeltaKernel m n ↔ n * (m : ℝ) ^ 2 + m ^ 3 < n ^ 3 := by
  rw [weilDeltaKernel_eq]
  by_cases hdvd : m ∣ n
  · have hlt := prime_lt_archCompensation hm hmn hdvd
    obtain ⟨x, rfl⟩ := hdvd
    have hx2 : (2 : ℝ) ≤ x := by
      have : 2 ≤ x := by
        rcases Nat.lt_or_ge x 2 with h | h
        · interval_cases x <;> omega
        · exact h
      exact_mod_cast this
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    constructor
    · intro _
      push_cast
      have : ((m : ℝ) * x) ^ 3 - m * x * (m : ℝ) ^ 2 - (m : ℝ) ^ 3 =
          (m : ℝ) ^ 3 * ((x : ℝ) ^ 3 - x - 1) := by ring
      nlinarith [mul_pos (pow_pos hm' 3) (cube_sub_pos hx2)]
    · intro _; linarith
  · have hP : weilPrimeKernel m n = 0 := by
      unfold weilPrimeKernel
      rw [if_neg (fun h => hdvd h.1), if_neg (fun h => by
        have := Nat.le_of_dvd hm h.1; omega)]
    rw [hP, sub_zero]
    exact archCompensation_pos_iff hm hmn

/-- **Weil's atomic kernel never vanishes off the diagonal.** -/
theorem weilDeltaKernel_ne_zero {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    weilDeltaKernel m n ≠ 0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · intro h0
    have hn := (weilDeltaKernel_neg_iff hm h).not.mp (by rw [h0]; exact lt_irrefl 0)
    have hp := (weilDeltaKernel_pos_iff hm h).not.mp (by rw [h0]; exact lt_irrefl 0)
    push Not at hn hp
    have : (n : ℤ) ^ 3 = n * m ^ 2 + m ^ 3 := by
      have : (n : ℝ) ^ 3 = n * m ^ 2 + m ^ 3 := le_antisymm (by linarith) (by linarith)
      exact_mod_cast this
    exact cube_ne_plastic hm this
  · intro h0
    rw [weilDeltaKernel_symm] at h0
    have hn' := (weilDeltaKernel_neg_iff hn h).not.mp (by rw [h0]; exact lt_irrefl 0)
    have hp' := (weilDeltaKernel_pos_iff hn h).not.mp (by rw [h0]; exact lt_irrefl 0)
    push Not at hn' hp'
    have : (m : ℤ) ^ 3 = m * n ^ 2 + n ^ 3 := by
      have : (m : ℝ) ^ 3 = m * n ^ 2 + n ^ 3 := le_antisymm (by linarith) (by linarith)
      exact_mod_cast this
    exact cube_ne_plastic hn this

/-! ## The first Beurling–Deny criterion on atoms -/

/-- Two orders lie within the plastic ratio: `max³ < max·min² + min³`. -/
def WithinPlastic (m n : ℕ) : Prop :=
  (max m n : ℝ) ^ 3 < (max m n : ℝ) * (min m n : ℝ) ^ 2 + (min m n : ℝ) ^ 3

/-- The atomic Weil form with diagonal `d`. -/
def atomForm (S : Finset ℕ) (d : ℕ → ℝ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, (if i = j then d i else weilDeltaKernel i j) * x i * x j

theorem weilDeltaKernel_neg_of_withinPlastic {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (h : WithinPlastic m n) : weilDeltaKernel m n < 0 := by
  unfold WithinPlastic at h
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · rw [max_eq_right (by exact_mod_cast hlt.le), min_eq_left (by exact_mod_cast hlt.le)] at h
    exact (weilDeltaKernel_neg_iff hm hlt).mpr h
  · rw [max_eq_left (by exact_mod_cast hlt.le), min_eq_right (by exact_mod_cast hlt.le)] at h
    rw [weilDeltaKernel_symm]
    exact (weilDeltaKernel_neg_iff hn hlt).mpr h

theorem weilDeltaKernel_pos_of_not_withinPlastic {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (h : ¬ WithinPlastic m n) : 0 < weilDeltaKernel m n := by
  rcases lt_or_gt_of_ne (weilDeltaKernel_ne_zero hm hn hmn) with h1 | h1
  · exfalso
    apply h
    unfold WithinPlastic
    rcases lt_or_gt_of_ne hmn with hlt | hlt
    · rw [max_eq_right (by exact_mod_cast hlt.le), min_eq_left (by exact_mod_cast hlt.le)]
      exact (weilDeltaKernel_neg_iff hm hlt).mp h1
    · rw [max_eq_left (by exact_mod_cast hlt.le), min_eq_right (by exact_mod_cast hlt.le)]
      rw [weilDeltaKernel_symm] at h1
      exact (weilDeltaKernel_neg_iff hn hlt).mp h1
  · exact h1

/-- **The first Beurling–Deny criterion holds exactly on plastic windows.** For a finite set of
positive orders, `Q(|x|) ≤ Q(x)` holds for every diagonal and every vector iff every pair of distinct
orders lies within the plastic ratio. -/
theorem atomForm_abs_le_iff (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    (∀ (d x : ℕ → ℝ), atomForm S d (fun i => |x i|) ≤ atomForm S d x) ↔
      ∀ m ∈ S, ∀ n ∈ S, m ≠ n → WithinPlastic m n := by
  constructor
  · intro h m hm n hn hmn
    by_contra hw
    have hW := weilDeltaKernel_pos_of_not_withinPlastic (hS m hm) (hS n hn) hmn hw
    -- the vector `e_m − e_n`
    set x : ℕ → ℝ := fun i => if i = m then 1 else if i = n then -1 else 0
    have hval : ∀ (y : ℕ → ℝ), (∀ i, i ≠ m → i ≠ n → y i = 0) →
        atomForm S 0 y = 2 * weilDeltaKernel m n * y m * y n := by
      intro y hy
      unfold atomForm
      have hsub : ({m, n} : Finset ℕ) ⊆ S := by
        intro i hi
        rcases Finset.mem_insert.mp hi with h | h
        · exact h ▸ hm
        · exact (Finset.mem_singleton.mp h) ▸ hn
      rw [← Finset.sum_subset hsub (fun i _ hi => Finset.sum_eq_zero fun j _ => by
        have : y i = 0 := hy i (fun h => hi (h ▸ Finset.mem_insert_self _ _))
          (fun h => hi (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        rw [this]; ring)]
      rw [Finset.sum_pair hmn]
      rw [← Finset.sum_subset hsub (fun j _ hj => by
          have : y j = 0 := hy j (fun h => hj (h ▸ Finset.mem_insert_self _ _))
            (fun h => hj (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          rw [this]; ring),
        ← Finset.sum_subset hsub (fun j _ hj => by
          have : y j = 0 := hy j (fun h => hj (h ▸ Finset.mem_insert_self _ _))
            (fun h => hj (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          rw [this]; ring)]
      rw [Finset.sum_pair hmn, Finset.sum_pair hmn]
      simp [hmn, Ne.symm hmn]
      rw [weilDeltaKernel_symm n m]
      ring
    have hx : ∀ i, i ≠ m → i ≠ n → x i = 0 := fun i h1 h2 => by simp [x, h1, h2]
    have hax : ∀ i, i ≠ m → i ≠ n → |x i| = 0 := fun i h1 h2 => by simp [x, h1, h2]
    have h1 := hval x hx
    have h2 := hval (fun i => |x i|) hax
    have hxm : x m = 1 := by simp [x]
    have hxn : x n = -1 := by simp [x, Ne.symm hmn]
    have := h 0 x
    rw [h1, h2] at this
    simp only [hxm, hxn, abs_one, abs_neg] at this
    linarith
  · intro h d x
    have key : ∀ i ∈ S, ∀ j ∈ S, (if i = j then d i else weilDeltaKernel i j) * |x i| * |x j| ≤
        (if i = j then d i else weilDeltaKernel i j) * x i * x j := by
      intro i hi j hj
      split_ifs with hij
      · subst hij; rw [mul_assoc, mul_assoc, abs_mul_abs_self]
      · have hW := weilDeltaKernel_neg_of_withinPlastic (hS i hi) (hS j hj) hij (h i hi j hj hij)
        have habs : x i * x j ≤ |x i| * |x j| := by rw [← abs_mul]; exact le_abs_self _
        nlinarith
    exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => key i hi j hj

end GaloisForLFunctions.SurfaceOfSpecZ
