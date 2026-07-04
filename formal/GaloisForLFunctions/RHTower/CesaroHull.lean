/-
Docs 62–63 (Route C, the ordered-mixture obstruction): the Finset-algebra layer,
machine-checked.

* `abel_pos_mixture` — the exact Abel reformulation (doc 62 §1): a weighted sum
  Σ A_i·g_i equals a mixture of the PARTIAL SUMS with weights ΔA plus boundary
  — for decreasing nonneg A, a positive mixture.
* `pos_mixture_ne_zero` — the hull exclusion: a positive mixture of points
  strictly inside an open half-plane through 0 cannot vanish. A zero of the
  carrier is a SPREAD event, not an endpoint event.
* `carrier_ne_zero_of_psum_halfplane` — the m = 0 composed form: decreasing
  nonneg weights + half-plane-confined partial-sum trajectory ⟹ no zero.
* `carrier_ne_zero_of_cesaro_halfplane` — the m = 1 form (doc 62 §2.5): convex
  decreasing weights + half-plane-confined CESÀRO means ⟹ no zero. This is
  (CES-1)'s consumer: Route C is machine-checked from here down to
  `midCentral`'s creation bound, with the pass-count input (docs 63/64) the
  sole analytic hypothesis.
* `cesaroPsum_step` / `cesaroPsum_speed` — the discrete EMA recursion
  C_{k+1} − C_k = (S_{k+1} − C_k)/(k+1) and its speed bound (doc 63 §2's
  finite analog, exact).
-/
import Mathlib

namespace RHTower

open Finset Complex

/-- Partial sums `S_k = Σ_{i<k} g i` of the step sequence. -/
noncomputable def psum (g : ℕ → ℂ) (k : ℕ) : ℂ := ∑ i ∈ range k, g i

/-- Cesàro means of the partial sums: `C_k = (1/k)·Σ_{j=1..k} S_j`. -/
noncomputable def cesaroPsum (g : ℕ → ℂ) (k : ℕ) : ℂ :=
  (∑ j ∈ range k, psum g (j + 1)) / (k : ℂ)

/-- **Abel reformulation (doc 62 §1).** The carrier sum is the boundary term
plus the ΔA-mixture of partial sums. -/
theorem abel_pos_mixture (A : ℕ → ℝ) (g : ℕ → ℂ) (n : ℕ) :
    ∑ i ∈ range n, (A i : ℂ) * g i
      = (A (n - 1) : ℂ) * psum g n
        + ∑ i ∈ range (n - 1), (↑(A i - A (i + 1)) : ℂ) * psum g (i + 1) := by
  have h := Finset.sum_range_by_parts (fun i => (A i : ℂ)) g n
  simp only [smul_eq_mul] at h
  have hneg : ∑ i ∈ range (n - 1), (↑(A i - A (i + 1)) : ℂ) * psum g (i + 1)
      = -∑ i ∈ range (n - 1),
          (((A (i + 1) : ℂ)) - (A i : ℂ)) * ∑ j ∈ range (i + 1), g j := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold psum
    push_cast
    ring
  rw [hneg, ← sub_eq_add_neg]
  unfold psum
  exact h

/-- **Hull exclusion (doc 62 §1).** A positive mixture of points strictly
inside the open half-plane `{z : (u·z).re > 0}` cannot vanish. -/
theorem pos_mixture_ne_zero {s : Finset ℕ} {w : ℕ → ℝ} {P : ℕ → ℂ} {u : ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hhp : ∀ i ∈ s, 0 < (u * P i).re)
    (hex : ∃ i ∈ s, 0 < w i) :
    ∑ i ∈ s, (w i : ℂ) * P i ≠ 0 := by
  intro h0
  have hre : ∑ i ∈ s, w i * (u * P i).re = 0 := by
    have hz : (u * ∑ i ∈ s, (w i : ℂ) * P i).re = 0 := by
      rw [h0, mul_zero]; rfl
    rw [Finset.mul_sum, Complex.re_sum] at hz
    rw [← hz]
    apply Finset.sum_congr rfl
    intro i _
    rw [show u * ((w i : ℂ) * P i) = (w i : ℂ) * (u * P i) by ring,
      Complex.re_ofReal_mul]
  have hpos : 0 < ∑ i ∈ s, w i * (u * P i).re := by
    obtain ⟨i₀, hi₀, hwi₀⟩ := hex
    exact Finset.sum_pos'
      (fun i hi => mul_nonneg (hw i hi) (le_of_lt (hhp i hi)))
      ⟨i₀, hi₀, mul_pos hwi₀ (hhp i₀ hi₀)⟩
  linarith

/-- Mixture weights of the Abel form: `ΔA` on the interior, `A (n−1)` at the
boundary slot. -/
noncomputable def abelWeight (A : ℕ → ℝ) (n : ℕ) (i : ℕ) : ℝ :=
  if i < n - 1 then A i - A (i + 1) else A (n - 1)

theorem abelWeight_sum (A : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range n, abelWeight A n i = A 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m + 1 - 1 = m := by omega
  rw [Finset.sum_range_succ]
  have h1 : ∀ i ∈ range m, abelWeight A (m + 1) i = A i - A (i + 1) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    simp only [abelWeight, hm]
    rw [if_pos hi']
  rw [Finset.sum_congr rfl h1, Finset.sum_range_sub' A m]
  simp only [abelWeight, hm]
  rw [if_neg (lt_irrefl m)]
  ring

/-- The carrier sum as a single positive mixture of partial sums. -/
theorem carrier_eq_mixture (A : ℕ → ℝ) (g : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range n, (A i : ℂ) * g i
      = ∑ i ∈ range n, (abelWeight A n i : ℂ) * psum g (i + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m + 1 - 1 = m := by omega
  rw [abel_pos_mixture A g (m + 1), Finset.sum_range_succ]
  have h1 : ∀ i ∈ range m, (abelWeight A (m + 1) i : ℂ) * psum g (i + 1)
      = (↑(A i - A (i + 1)) : ℂ) * psum g (i + 1) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    simp only [abelWeight, hm]
    rw [if_pos hi']
  have hb : (abelWeight A (m + 1) m : ℝ) = A m := by
    simp only [abelWeight, hm]
    rw [if_neg (lt_irrefl m)]
  rw [Finset.sum_congr rfl h1, hb, hm]
  ring

/-- **The m = 0 obstruction theorem (doc 62 §§1,3).** Decreasing nonnegative
weights with `A 0 > 0`, and a partial-sum trajectory confined to an open
half-plane through the origin on `k = 1..n`: the carrier cannot vanish. -/
theorem carrier_ne_zero_of_psum_halfplane (A : ℕ → ℝ) (g : ℕ → ℂ) (n : ℕ)
    (hn : 1 ≤ n) (hdec : ∀ i, i + 1 < n → A (i + 1) ≤ A i)
    (hnn : 0 ≤ A (n - 1)) (hA0 : 0 < A 0) {u : ℂ}
    (hhp : ∀ k, 1 ≤ k → k ≤ n → 0 < (u * psum g k).re) :
    ∑ i ∈ range n, (A i : ℂ) * g i ≠ 0 := by
  rw [carrier_eq_mixture A g n hn]
  have hwnn : ∀ i ∈ range n, 0 ≤ abelWeight A n i := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    unfold abelWeight
    split
    · rename_i hlt
      have : i + 1 < n := by omega
      linarith [hdec i this]
    · exact hnn
  apply pos_mixture_ne_zero hwnn
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    exact hhp (i + 1) (by omega) (by omega)
  · by_contra hall
    push Not at hall
    have hzero : ∀ i ∈ range n, abelWeight A n i = 0 := by
      intro i hi
      exact le_antisymm (hall i hi) (hwnn i hi)
    have hA0' : (0 : ℝ) = A 0 := by
      rw [← abelWeight_sum A n hn]
      exact (Finset.sum_eq_zero hzero).symm
    linarith

/-- **The m = 1 obstruction theorem (doc 62 §2.5 / the (CES-1) consumer).**
Convex decreasing nonnegative weights (the Abel weights `ΔA` themselves
decreasing, strictly positive at 0, nonnegative at the edge) and CESÀRO means
of the partial sums confined to an open half-plane on `k = 1..n`: the carrier
cannot vanish. The half-plane hypothesis on the Cesàro path is exactly what
docs 63/64's pass-count bound supplies off the exceptional set — Route C's
sole remaining analytic input. -/
theorem carrier_ne_zero_of_cesaro_halfplane (A : ℕ → ℝ) (g : ℕ → ℂ) (n : ℕ)
    (hn : 1 ≤ n)
    (hconv : ∀ i, i + 1 < n → abelWeight A n (i + 1) ≤ abelWeight A n i)
    (hnn : 0 ≤ abelWeight A n (n - 1)) (h01 : 0 < abelWeight A n 0) {u : ℂ}
    (hhp : ∀ k, 1 ≤ k → k ≤ n → 0 < (u * cesaroPsum g k).re) :
    ∑ i ∈ range n, (A i : ℂ) * g i ≠ 0 := by
  rw [carrier_eq_mixture A g n hn]
  have hkey : ∀ k, 1 ≤ k → k ≤ n →
      0 < (u * psum (fun i => psum g (i + 1)) k).re := by
    intro k hk1 hkn
    have hcast : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hne : ((k : ℂ)) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hEq : psum (fun i => psum g (i + 1)) k = (k : ℂ) * cesaroPsum g k := by
      unfold cesaroPsum psum
      field_simp
    rw [hEq, show u * ((k : ℂ) * cesaroPsum g k)
        = ((k : ℝ) : ℂ) * (u * cesaroPsum g k) by push_cast; ring,
      Complex.re_ofReal_mul]
    exact mul_pos hcast (hhp k hk1 hkn)
  exact carrier_ne_zero_of_psum_halfplane (abelWeight A n)
    (fun i => psum g (i + 1)) n hn (fun i hi => hconv i hi) hnn h01 hkey

/-- **The discrete EMA recursion (doc 63 §2, finite analog — exact).**
`C_{k+1} − C_k = (S_{k+1} − C_k)/(k+1)`. -/
theorem cesaroPsum_step (g : ℕ → ℂ) (k : ℕ) (hk : 1 ≤ k) :
    cesaroPsum g (k + 1) - cesaroPsum g k
      = (psum g (k + 1) - cesaroPsum g k) / ((k : ℂ) + 1) := by
  have hk0 : ((k : ℂ)) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by
    have hcast : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast (by omega : k + 1 ≠ 0)
  unfold cesaroPsum
  rw [Finset.sum_range_succ]
  push_cast
  field_simp
  ring

/-- The EMA speed bound: each Cesàro step moves by the deviation over `k+1`. -/
theorem cesaroPsum_speed (g : ℕ → ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ‖cesaroPsum g (k + 1) - cesaroPsum g k‖
      = ‖psum g (k + 1) - cesaroPsum g k‖ / ((k : ℝ) + 1) := by
  rw [cesaroPsum_step g k hk, norm_div]
  congr 1
  have hcast : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_natCast]
  push_cast
  ring

/-- **The plateau split (doc 65 §1).** For a plateau+taper carrier (constant
weight `A0` below `M`), a zero of the carrier forces the plateau partial sum
down to the taper term's size: `‖S_M‖ = ‖T‖/A0`. The counting consumer pairs
this with a Chebyshev bound on the taper term `T` (pure MV) and one fixed-scale
anti-concentration input for `S_M` — Route C's minimal split. -/
theorem plateau_split {A : ℕ → ℝ} {g : ℕ → ℂ} {n M : ℕ} {A0 : ℝ}
    (hM : M ≤ n) (hplat : ∀ i < M, A i = A0) (hA0 : 0 < A0)
    (h0 : ∑ i ∈ range n, (A i : ℂ) * g i = 0) :
    ‖psum g M‖ = ‖∑ i ∈ Finset.Ico M n, (A i : ℂ) * g i‖ / A0 := by
  have hsplit : (A0 : ℂ) * psum g M + ∑ i ∈ Finset.Ico M n, (A i : ℂ) * g i
      = ∑ i ∈ range n, (A i : ℂ) * g i := by
    rw [← Finset.sum_range_add_sum_Ico (fun i => (A i : ℂ) * g i) hM]
    congr 1
    unfold psum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hplat i (Finset.mem_range.mp hi)]
  have hneg : (A0 : ℂ) * psum g M = -∑ i ∈ Finset.Ico M n, (A i : ℂ) * g i := by
    have := hsplit.trans h0
    linear_combination this
  have hnorm : A0 * ‖psum g M‖ = ‖∑ i ∈ Finset.Ico M n, (A i : ℂ) * g i‖ := by
    rw [← norm_neg (∑ i ∈ Finset.Ico M n, (A i : ℂ) * g i), ← hneg, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hA0.le]
  field_simp [hA0.ne']
  linarith [hnorm]

end RHTower
