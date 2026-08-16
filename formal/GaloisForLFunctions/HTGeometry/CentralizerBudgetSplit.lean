import GaloisForLFunctions.HTGeometry.ShortcutSpectralPhase

/-!
# The intrinsic circuit budget of a centralizer word

A word inside the spectral torus accumulates bandwidth additively, because adding lifts adds
Lipschitz constants: `s` letters of bandwidth at most `b` make a word of bandwidth at most `s b`.
That is the whole of the intrinsic budget bound.

The transverse half is unitary telescoping: replacing each letter of a word by a nearby centralizer
letter moves the product by at most the sum of the letter errors, so a word approximating a
centralizer element is itself approximated by a centralizer word whose bandwidth is budgeted.

The one-qubit example shows the budget cannot be inverted: a single elementary gate commuting with a
Hamiltonian of gap `δ` has bandwidth `π/δ`, unbounded as the gap closes.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-! ## Bandwidth of a centralizer word -/

/-- **Iterated `(8)`.**  Circular distance is subadditive along sums, so a word of `n` letters has
bandwidth at most the sum of the letter bandwidths. -/
theorem circDist_sum_le (a b : ℕ → ℝ) :
    ∀ n : ℕ, circDist (∑ i ∈ Finset.range n, a i) (∑ i ∈ Finset.range n, b i)
      ≤ ∑ i ∈ Finset.range n, circDist (a i) (b i) := by
  intro n
  induction n with
  | zero => simp [circDist, phaseGap]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    exact le_trans (circDist_add_le _ _ _ _) (by linarith [ih])

/-- A word of `n` letters of bandwidth at most `b` has bandwidth at most `n b`. -/
theorem circDist_sum_le_nsmul {a b : ℕ → ℝ} {c : ℝ} (hc : ∀ i, circDist (a i) (b i) ≤ c) (n : ℕ) :
    circDist (∑ i ∈ Finset.range n, a i) (∑ i ∈ Finset.range n, b i) ≤ (n : ℝ) * c := by
  refine le_trans (circDist_sum_le a b n) ?_
  calc ∑ i ∈ Finset.range n, circDist (a i) (b i) ≤ ∑ _i ∈ Finset.range n, c :=
        Finset.sum_le_sum fun i _ => hc i
    _ = (n : ℝ) * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Unitary telescoping -/

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- A product of contractions is a contraction. -/
theorem norm_listProd_le_one : ∀ (L : List A), (∀ a ∈ L, ‖a‖ ≤ 1) → ‖L.prod‖ ≤ 1
  | [], _ => by simp
  | (x :: L), h => by
    have hx : ‖x‖ ≤ 1 := h x (by simp)
    have hL : ‖L.prod‖ ≤ 1 := norm_listProd_le_one L fun a ha => h a (by simp [ha])
    have hmul : ‖x * L.prod‖ ≤ ‖x‖ * ‖L.prod‖ := norm_mul_le _ _
    have hnn : (0 : ℝ) ≤ ‖L.prod‖ := norm_nonneg _
    have : ‖x‖ * ‖L.prod‖ ≤ 1 := by nlinarith [hx, hL, hnn, norm_nonneg x]
    rw [List.prod_cons]
    linarith [hmul, this]

/-- **`(35)`: unitary telescoping.**  Replacing every letter by a nearby one moves the product by at
most the sum of the letter errors. -/
theorem norm_listProd_sub_le :
    ∀ (W Y : List A), (∀ a ∈ W, ‖a‖ ≤ 1) → (∀ a ∈ Y, ‖a‖ ≤ 1) → W.length = Y.length →
      ‖W.prod - Y.prod‖ ≤ (List.zipWith (fun a b => ‖a - b‖) W Y).sum
  | [], [], _, _, _ => by simp
  | (x :: W), (y :: Y), hW, hY, hlen => by
    have hlen' : W.length = Y.length := by
      simpa using hlen
    have hx : ‖x‖ ≤ 1 := hW x (by simp)
    have hYprod : ‖Y.prod‖ ≤ 1 := norm_listProd_le_one Y fun a ha => hY a (by simp [ha])
    have hrec : ‖W.prod - Y.prod‖ ≤ (List.zipWith (fun a b => ‖a - b‖) W Y).sum :=
      norm_listProd_sub_le W Y (fun a ha => hW a (by simp [ha])) (fun a ha => hY a (by simp [ha]))
        hlen'
    have hsplit : x * W.prod - y * Y.prod = x * (W.prod - Y.prod) + (x - y) * Y.prod := by
      noncomm_ring
    have h1 : ‖x * (W.prod - Y.prod)‖ ≤ ‖W.prod - Y.prod‖ := by
      refine le_trans (norm_mul_le _ _) ?_
      nlinarith [hx, norm_nonneg (W.prod - Y.prod)]
    have h2 : ‖(x - y) * Y.prod‖ ≤ ‖x - y‖ := by
      refine le_trans (norm_mul_le _ _) ?_
      nlinarith [hYprod, norm_nonneg (x - y)]
    rw [List.prod_cons, List.prod_cons, hsplit]
    calc ‖x * (W.prod - Y.prod) + (x - y) * Y.prod‖
        ≤ ‖x * (W.prod - Y.prod)‖ + ‖(x - y) * Y.prod‖ := norm_add_le _ _
      _ ≤ ‖W.prod - Y.prod‖ + ‖x - y‖ := by linarith [h1, h2]
      _ ≤ (List.zipWith (fun a b => ‖a - b‖) W Y).sum + ‖x - y‖ := by linarith [hrec]
      _ = (List.zipWith (fun a b => ‖a - b‖) (x :: W) (y :: Y)).sum := by
          simp [List.zipWith]
          ring

/-! ## The one-qubit obstruction -/

/-- The phase distance across the single gap of the one-qubit example is `π`. -/
theorem circDist_pi_zero : circDist Real.pi 0 = Real.pi := by
  have h : |Real.pi - 0| = Real.pi := by
    rw [sub_zero, abs_of_pos Real.pi_pos]
  rw [circDist_eq_abs_of_le_pi (by rw [h]), h]

/-- **`(29)`, and `(27)` fails.**  A single elementary gate commuting with a Hamiltonian of gap `δ`
has bandwidth `π/δ`, which exceeds any constant once the gap is small enough. -/
theorem exists_gap_bandwidth_gt (Amax : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ Amax < circDist Real.pi 0 / δ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨Real.pi / (|Amax| + 1), by positivity, ?_⟩
  rw [circDist_pi_zero, div_div_eq_mul_div, lt_div_iff₀ hpi]
  nlinarith [le_abs_self Amax, abs_nonneg Amax, hpi]

/-! ## Lipschitz constants are nonnegative -/

/-- Any admissible Lipschitz constant is nonnegative, so a bandwidth infimum of zero is a minimum. -/
theorem lip_nonneg {p : ℝ → ℝ} {L : ℝ} (hLip : ∀ x y, |p x - p y| ≤ L * |x - y|) : 0 ≤ L := by
  have h := hLip 0 1
  have habs : |(0 : ℝ) - 1| = 1 := by norm_num
  rw [habs, mul_one] at h
  exact le_trans (abs_nonneg _) h

end GaloisForLFunctions.HTGeometry
