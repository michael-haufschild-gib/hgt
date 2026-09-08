import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Basic

/-!
# The finite core of spaced-configuration detection by a positive pair form

Two finite statements, independent of the zeta function.

* For a `10`-spaced finite family of real ordinates, the Lorentzian-type sum
  `Σ_{k ≠ j} 1/(3 + (γ_j − γ_k)²)` is at most `1/25`: the points on either side of `γ_j` inject
  into `ℕ_{≥ 1}` through `⌊|γ_j − γ_k|/10⌋`.
* For a Hermitian-type pair array `P` on a finite set `Z` with nonnegative amplitudes `a`, diagonal
  `Re P_jj ≥ a_j²`, off-diagonal `|P_jk| ≤ 4 a_j a_k w_jk`, nonnegative sub-blocks, and a set
  `A = {a ≥ Θ}` whose internal weights are small (`Σ_{k ∈ A, k ≠ j} w_jk ≤ 1/25`) while the total
  weights are bounded (`Σ_k w_jk ≤ 8L`), the elements with `a_j ≥ 200 Θ L` are detected by the total
  real part: `Σ_{a_j ≥ 200ΘL} a_j² ≤ 2 Re Σ_{Z×Z} P + 25600 Θ² L² · #A`.
-/

open Finset

namespace RHTower

/-- `Σ_{i=1}^{M} 1/i² ≤ 2`. -/
theorem sum_Icc_inv_sq_le_two (M : ℕ) : ∑ i ∈ Finset.Icc 1 M, ((i : ℝ) ^ 2)⁻¹ ≤ 2 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · rw [← Finset.Ioc_insert_left hM, Finset.sum_insert (by simp)]
    have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := M) one_ne_zero hM
    have : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
    simp only [Nat.cast_one, one_pow, inv_one] at h ⊢
    linarith

/-- For a `10`-spaced family, the sum of `1/(3 + (γ_j − γ_k)²)` over `k ≠ j` is at most `1/25`. -/
theorem sum_inv_three_add_sq_le_of_spaced {ι : Type*} [DecidableEq ι] (A : Finset ι) (γ : ι → ℝ)
    (hsp : ∀ j ∈ A, ∀ k ∈ A, j ≠ k → 10 ≤ |γ j - γ k|) {j : ι} (hj : j ∈ A) :
    ∑ k ∈ A.erase j, 1 / (3 + (γ j - γ k) ^ 2) ≤ 1 / 25 := by
  classical
  let m : ι → ℕ := fun k => ⌊|γ j - γ k| / 10⌋₊
  let side : ι → Bool := fun k => decide (γ j < γ k)
  have hm1 : ∀ k ∈ A.erase j, 1 ≤ m k := by
    intro k hk
    obtain ⟨hkj, hkA⟩ := Finset.mem_erase.mp hk
    have := hsp j hj k hkA (Ne.symm hkj)
    exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ (by norm_num)]; linarith)
  have hterm : ∀ k ∈ A.erase j, 1 / (3 + (γ j - γ k) ^ 2) ≤ 1 / (100 * ((m k : ℝ)) ^ 2) := by
    intro k hk
    have h1 := hm1 k hk
    have hfl : (m k : ℝ) ≤ |γ j - γ k| / 10 := Nat.floor_le (by positivity)
    have hm0 : (0 : ℝ) < m k := by exact_mod_cast h1
    have h10 : 10 * (m k : ℝ) ≤ |γ j - γ k| := by
      rw [le_div_iff₀ (by norm_num)] at hfl; linarith
    have hsq : 100 * (m k : ℝ) ^ 2 ≤ (γ j - γ k) ^ 2 := by
      have := sq_abs (γ j - γ k)
      nlinarith [abs_nonneg (γ j - γ k)]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hinj : Set.InjOn (fun k => (side k, m k)) (A.erase j : Set ι) := by
    intro k hk k' hk' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hs, hmeq⟩ := heq
    by_contra hne
    have hkk' := hsp k (Finset.mem_of_mem_erase hk) k' (Finset.mem_of_mem_erase hk') hne
    have hd1 : (m k : ℝ) ≤ |γ j - γ k| / 10 := Nat.floor_le (by positivity)
    have hd2 : |γ j - γ k| / 10 < (m k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hd1' : (m k' : ℝ) ≤ |γ j - γ k'| / 10 := Nat.floor_le (by positivity)
    have hd2' : |γ j - γ k'| / 10 < (m k' : ℝ) + 1 := Nat.lt_floor_add_one _
    have hmr : (m k : ℝ) = m k' := by exact_mod_cast hmeq
    have hsides : (γ j < γ k ↔ γ j < γ k') := by
      have : decide (γ j < γ k) = decide (γ j < γ k') := hs
      simpa [decide_eq_decide] using this
    have hlt : |γ k - γ k'| < 10 := by
      rcases lt_or_ge (γ j) (γ k) with h | h
      · have h' := hsides.mp h
        rw [abs_of_neg (by linarith)] at hd1 hd2
        rw [abs_of_neg (by linarith)] at hd1' hd2'
        rw [abs_lt]; constructor <;> linarith
      · have h' : γ k' ≤ γ j := by
          by_contra hc; exact absurd (hsides.mpr (lt_of_not_ge hc)) (not_lt.mpr h)
        rw [abs_of_nonneg (by linarith)] at hd1 hd2
        rw [abs_of_nonneg (by linarith)] at hd1' hd2'
        rw [abs_lt]; constructor <;> linarith
    linarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ k ∈ A.erase j, m k ≤ M :=
    ⟨(A.erase j).sup m, fun k hk => Finset.le_sup (f := m) hk⟩
  calc ∑ k ∈ A.erase j, 1 / (3 + (γ j - γ k) ^ 2)
      ≤ ∑ k ∈ A.erase j, 1 / (100 * ((m k : ℝ)) ^ 2) := Finset.sum_le_sum hterm
    _ = ∑ p ∈ (A.erase j).image (fun k => (side k, m k)), 1 / (100 * ((p.2 : ℝ)) ^ 2) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ Finset.Icc 1 M, 1 / (100 * ((p.2 : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
          simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
          exact ⟨hm1 k hk, hM k hk⟩
        · intros; positivity
    _ = 2 * ∑ i ∈ Finset.Icc 1 M, 1 / (100 * ((i : ℝ)) ^ 2) := by
        simp only [Finset.sum_product, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
          nsmul_eq_mul, Nat.cast_ofNat]
    _ = 2 * ((1 / 100) * ∑ i ∈ Finset.Icc 1 M, ((i : ℝ) ^ 2)⁻¹) := by
        have hterm' : ∀ i : ℕ, (1 : ℝ) / (100 * ((i : ℝ)) ^ 2) = (1 / 100) * ((i : ℝ) ^ 2)⁻¹ :=
          fun i => by rw [one_div, mul_inv, one_div]
        simp only [hterm', Finset.mul_sum]
    _ ≤ 2 * ((1 / 100) * 2) := by gcongr; exact sum_Icc_inv_sq_le_two M
    _ = 1 / 25 := by norm_num

/-- The finite detection inequality for a positive pair array with a spaced high-amplitude set. -/
theorem spaced_configuration_energy {ι : Type*} [DecidableEq ι] (Z : Finset ι) (P : ι → ι → ℂ)
    (a : ι → ℝ) (w : ι → ι → ℝ) {Θ L : ℝ} (hΘ : 0 < Θ) (hL : 1 ≤ L)
    (ha : ∀ j, 0 ≤ a j) (hw : ∀ j k, 0 ≤ w j k) (hwsymm : ∀ j k, w j k = w k j)
    (h1 : ∀ j ∈ Z, a j ^ 2 ≤ (P j j).re)
    (h2 : ∀ j ∈ Z, ∀ k ∈ Z, ‖P j k‖ ≤ 4 * a j * a k * w j k)
    (h3 : ∀ R ⊆ Z, 0 ≤ (∑ j ∈ R, ∑ k ∈ R, P j k).re)
    (h4 : ∀ j ∈ Z.filter (fun j => Θ ≤ a j),
      ∑ k ∈ (Z.filter (fun j => Θ ≤ a j)).erase j, w j k ≤ 1 / 25)
    (h5 : ∀ j ∈ Z, ∑ k ∈ Z, w j k ≤ 8 * L) :
    ∑ j ∈ Z.filter (fun j => 200 * Θ * L ≤ a j), a j ^ 2
      ≤ 2 * (∑ j ∈ Z, ∑ k ∈ Z, P j k).re
        + 25600 * Θ ^ 2 * L ^ 2 * (Z.filter (fun j => Θ ≤ a j)).card := by
  classical
  set A := Z.filter (fun j => Θ ≤ a j) with hA
  set R := Z.filter (fun j => ¬ Θ ≤ a j) with hR
  have hAZ : A ⊆ Z := Finset.filter_subset _ _
  have hRZ : R ⊆ Z := Finset.filter_subset _ _
  have hRmem : ∀ k ∈ R, a k ≤ Θ := fun k hk => (not_le.mp (Finset.mem_filter.mp hk).2).le
  -- decomposition of the double sum
  have hsplit : (∑ j ∈ Z, ∑ k ∈ Z, P j k)
      = (∑ j ∈ A, ∑ k ∈ A, P j k) + (∑ j ∈ A, ∑ k ∈ R, P j k)
        + ((∑ j ∈ R, ∑ k ∈ A, P j k) + ∑ j ∈ R, ∑ k ∈ R, P j k) := by
    have hin : ∀ j, ∑ k ∈ Z, P j k = ∑ k ∈ A, P j k + ∑ k ∈ R, P j k := fun j => by
      rw [hA, hR, Finset.sum_filter_add_sum_filter_not]
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun j => Θ ≤ a j), ← hA, ← hR]
    simp only [hin, Finset.sum_add_distrib]
  have hre : (∑ j ∈ Z, ∑ k ∈ Z, P j k).re
      = (∑ j ∈ A, ∑ k ∈ A, P j k).re + (∑ j ∈ A, ∑ k ∈ R, P j k).re
        + ((∑ j ∈ R, ∑ k ∈ A, P j k).re + (∑ j ∈ R, ∑ k ∈ R, P j k).re) := by
    rw [hsplit]; simp only [Complex.add_re]
  -- (i) the `A × A` block
  have hAA : (21 / 25) * ∑ j ∈ A, a j ^ 2 ≤ (∑ j ∈ A, ∑ k ∈ A, P j k).re := by
    have hdiag : ∀ j ∈ A, ∑ k ∈ A, P j k = P j j + ∑ k ∈ A.erase j, P j k := fun j hj =>
      (Finset.add_sum_erase A (P j) hj).symm
    rw [Finset.sum_congr rfl hdiag, Finset.sum_add_distrib, Complex.add_re, Complex.re_sum,
      Complex.re_sum]
    have hd : ∑ j ∈ A, a j ^ 2 ≤ ∑ j ∈ A, (P j j).re :=
      Finset.sum_le_sum fun j hj => h1 j (hAZ hj)
    have hb : ∀ j ∈ A, -(∑ k ∈ A.erase j, 4 * a j * a k * w j k) ≤ (∑ k ∈ A.erase j, P j k).re := by
      intro j hj
      have hn : ‖∑ k ∈ A.erase j, P j k‖ ≤ ∑ k ∈ A.erase j, 4 * a j * a k * w j k :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk =>
          h2 j (hAZ hj) k (hAZ (Finset.mem_of_mem_erase hk)))
      have := Complex.abs_re_le_norm (∑ k ∈ A.erase j, P j k)
      linarith [(abs_le.mp this).1]
    have hcross : ∑ j ∈ A, ∑ k ∈ A.erase j, 4 * a j * a k * w j k ≤ (4 / 25) * ∑ j ∈ A, a j ^ 2 := by
      calc ∑ j ∈ A, ∑ k ∈ A.erase j, 4 * a j * a k * w j k
          ≤ ∑ j ∈ A, ∑ k ∈ A.erase j, (2 * a j ^ 2 * w j k + 2 * a k ^ 2 * w j k) := by
            gcongr with j hj k hk
            have := hw j k
            nlinarith [sq_nonneg (a j - a k)]
        _ = ∑ j ∈ A, ∑ k ∈ A.erase j, 2 * a j ^ 2 * w j k
            + ∑ j ∈ A, ∑ k ∈ A.erase j, 2 * a k ^ 2 * w j k := by
            simp only [Finset.sum_add_distrib]
        _ = ∑ j ∈ A, ∑ k ∈ A.erase j, 2 * a j ^ 2 * w j k
            + ∑ j ∈ A, ∑ k ∈ A.erase j, 2 * a j ^ 2 * w j k := by
            congr 1
            rw [Finset.sum_comm' (t' := A) (s' := fun k => A.erase k)]
            · simp only [hwsymm]
            · intro x y
              simp only [Finset.mem_erase]
              constructor
              · rintro ⟨hx, hyx, hy⟩; exact ⟨⟨fun h => hyx h.symm, hx⟩, hy⟩
              · rintro ⟨⟨hxy, hx⟩, hy⟩; exact ⟨hx, fun h => hxy h.symm, hy⟩
        _ = 4 * ∑ j ∈ A, a j ^ 2 * ∑ k ∈ A.erase j, w j k := by
            rw [← two_mul]
            simp only [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
        _ ≤ 4 * ∑ j ∈ A, a j ^ 2 * (1 / 25) := by
            gcongr with j hj
            exact h4 j hj
        _ = (4 / 25) * ∑ j ∈ A, a j ^ 2 := by rw [← Finset.sum_mul]; ring
    have hsum := Finset.sum_le_sum hb
    rw [Finset.sum_neg_distrib] at hsum
    linarith
  -- (ii) the two cross blocks
  have hcrossbound : ∀ j ∈ A, ∑ k ∈ R, 4 * a j * a k * w j k ≤ 32 * Θ * L * a j := by
    intro j hj
    have haj := ha j
    have h4aΘ : (0 : ℝ) ≤ 4 * a j * Θ := mul_nonneg (mul_nonneg (by norm_num) haj) hΘ.le
    calc ∑ k ∈ R, 4 * a j * a k * w j k
        ≤ ∑ k ∈ R, 4 * a j * Θ * w j k := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hRmem k hk) (by linarith)) (hw j k)
      _ = 4 * a j * Θ * ∑ k ∈ R, w j k := by rw [Finset.mul_sum]
      _ ≤ 4 * a j * Θ * ∑ k ∈ Z, w j k :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hRZ (fun k _ _ => hw j k)) h4aΘ
      _ ≤ 4 * a j * Θ * (8 * L) := mul_le_mul_of_nonneg_left (h5 j (hAZ hj)) h4aΘ
      _ = 32 * Θ * L * a j := by ring
  have hAR : -(32 * Θ * L * ∑ j ∈ A, a j) ≤ (∑ j ∈ A, ∑ k ∈ R, P j k).re := by
    have hn : ‖∑ j ∈ A, ∑ k ∈ R, P j k‖ ≤ 32 * Θ * L * ∑ j ∈ A, a j := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k hk => h2 j (hAZ hj) k (hRZ hk)).trans ?_
      exact hcrossbound j hj
    have := Complex.abs_re_le_norm (∑ j ∈ A, ∑ k ∈ R, P j k)
    linarith [(abs_le.mp this).1]
  have hRA : -(32 * Θ * L * ∑ j ∈ A, a j) ≤ (∑ j ∈ R, ∑ k ∈ A, P j k).re := by
    rw [Finset.sum_comm]
    have hn : ‖∑ k ∈ A, ∑ j ∈ R, P j k‖ ≤ 32 * Θ * L * ∑ j ∈ A, a j := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun j hj => h2 j (hRZ hj) k (hAZ hk)).trans ?_
      refine le_trans (le_of_eq ?_) (hcrossbound k hk)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hwsymm j k]; ring
    have := Complex.abs_re_le_norm (∑ k ∈ A, ∑ j ∈ R, P j k)
    linarith [(abs_le.mp this).1]
  -- (iii) the `R × R` block
  have hRR : 0 ≤ (∑ j ∈ R, ∑ k ∈ R, P j k).re := h3 R hRZ
  -- the lower bound `Re Σ P ≥ Σ_A ((21/25) a_j² − 64 Θ L a_j)`
  have hlow : ∑ j ∈ A, ((21 / 25) * a j ^ 2 - 64 * Θ * L * a j) ≤ (∑ j ∈ Z, ∑ k ∈ Z, P j k).re := by
    rw [hre, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith
  -- threshold split of `A`
  have hΘL : 0 < Θ * L := by positivity
  have hsplitA := Finset.sum_filter_add_sum_filter_not A (fun j => 200 * Θ * L ≤ a j)
    (fun j => (21 / 25) * a j ^ 2 - 64 * Θ * L * a j)
  have hhigh : ∀ j ∈ A.filter (fun j => 200 * Θ * L ≤ a j),
      (1 / 2) * a j ^ 2 ≤ (21 / 25) * a j ^ 2 - 64 * Θ * L * a j := by
    intro j hj
    have hja := (Finset.mem_filter.mp hj).2
    have := ha j
    nlinarith
  have hlowterm : ∀ j ∈ A.filter (fun j => ¬ 200 * Θ * L ≤ a j),
      -(12800 * Θ ^ 2 * L ^ 2) ≤ (21 / 25) * a j ^ 2 - 64 * Θ * L * a j := by
    intro j hj
    have hja := not_le.mp (Finset.mem_filter.mp hj).2
    have := ha j
    nlinarith
  have hsum1 := Finset.sum_le_sum hhigh
  have hsum2 := Finset.card_nsmul_le_sum _ _ _ hlowterm
  rw [nsmul_eq_mul] at hsum2
  have hcard : ((A.filter (fun j => ¬ 200 * Θ * L ≤ a j)).card : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_filter_le _ _
  -- identify the thresholded filter with `A.filter`
  have hfilt : Z.filter (fun j => 200 * Θ * L ≤ a j) = A.filter (fun j => 200 * Θ * L ≤ a j) := by
    rw [hA, Finset.filter_filter]
    refine Finset.filter_congr fun j _ => ?_
    constructor
    · intro h; exact ⟨le_trans (by nlinarith) h, h⟩
    · exact fun h => h.2
  rw [hfilt]
  rw [← Finset.mul_sum] at hsum1
  have hc2 : 12800 * Θ ^ 2 * L ^ 2 * ((A.filter (fun j => ¬ 200 * Θ * L ≤ a j)).card : ℝ)
      ≤ 12800 * Θ ^ 2 * L ^ 2 * (A.card : ℝ) := by gcongr
  linarith [hsum1, hsum2, hlow, hsplitA, hc2]

end RHTower
