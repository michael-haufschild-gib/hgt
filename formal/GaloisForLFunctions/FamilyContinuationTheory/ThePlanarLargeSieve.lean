import GaloisForLFunctions.RHTower.Sieve.LargeSieveSeparated

/-!
# The planar large sieve

The additive polynomial of the family continuation is a sum of additive characters of a planar
lattice at the reduced fractions of the columns. Its mean square over the rows is a large sieve
inequality for points of the torus `ℝ²/ℤ²`.

For frequencies `(x_r, y_r)` that are pairwise `δ`-separated in the maximum of the two circle
distances, `δ ≤ ½`, and `M ≥ 1/(2δ)`, put `Δ = (2N + δ⁻¹ ∑_{k ≤ M} 1/k)²`. Then

* `planarLargeSieve_bessel`: `∑_r |⟪φ_r, a⟫|² ≤ Δ ‖a‖²` for the rows `φ_r(m,n) = e(m x_r + n y_r)`,
  `m, n < N`;
* `planarLargeSieve_bilinear`, `sum_norm_sq_sum_mul_le`:
  `∑_{m,n<N} |∑_r c_r e(m x_r + n y_r)|² ≤ Δ ∑_r |c_r|²`.

Proof: Schur's test. The Gram entry of two rows is a product of two truncated geometric sums. A
geometric sum at circle level `k` (offset in `[kδ, (k+1)δ)`) is at most `N` for `k = 0` and
`1/(2kδ)` otherwise. The pair of levels and sides of the two offsets is injective on a separated
family, so a Gram row is dominated by the full sum over the cells, which is a square.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory

open Finset
open scoped InnerProductSpace
open _root_.RHTower.Sieve

/-- The planar exponential row of a pair of frequencies: `(m, n) ↦ ξ^m η^n` for `m, n < N`. -/
noncomputable def planeRow (N : ℕ) (ξ η : ℂ) : EuclideanSpace ℂ (Fin N × Fin N) :=
  WithLp.toLp 2 fun p : Fin N × Fin N => ξ ^ (p.1 : ℕ) * η ^ (p.2 : ℕ)

/-- The Gram entry of two planar rows is a product of two geometric correlations. -/
theorem inner_planeRow (N : ℕ) (ξ η ξ' η' : ℂ) :
    ⟪planeRow N ξ η, planeRow N ξ' η'⟫_ℂ =
      (∑ m ∈ range N, (starRingEnd ℂ) (ξ ^ m) * ξ' ^ m) *
        ∑ n ∈ range N, (starRingEnd ℂ) (η ^ n) * η' ^ n := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type,
    ← Fin.sum_univ_eq_sum_range (fun m => (starRingEnd ℂ) (ξ ^ m) * ξ' ^ m) N,
    ← Fin.sum_univ_eq_sum_range (fun n => (starRingEnd ℂ) (η ^ n) * η' ^ n) N, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  simp [planeRow, RCLike.inner_apply]
  ring

/-- Offsets with the same level and on the same side are closer than `δ` on the circle. -/
theorem toIntDist_sub_lt_of_levelOf_eq {δ u v : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hlev : levelOf δ u = levelOf δ v) (hside : 0 ≤ reduce u ↔ 0 ≤ reduce v) :
    toIntDist (u - v) < δ := by
  have hla := levelOf_mul_le (δ := δ) (x := u) hδ0
  have hlb := levelOf_mul_le (δ := δ) (x := v) hδ0
  have hua := lt_levelOf_succ_mul (δ := δ) (x := u) hδ0
  have hub := lt_levelOf_succ_mul (δ := δ) (x := v) hδ0
  rw [hlev] at hla hua
  have hda : |reduce u| = toIntDist u := rfl
  have hdb : |reduce v| = toIntDist v := rfl
  have hgap : |reduce u - reduce v| < δ := by
    rcases le_or_gt 0 (reduce u) with hpa | hna
    · have hpb : 0 ≤ reduce v := hside.mp hpa
      rw [abs_of_nonneg hpa] at hda
      rw [abs_of_nonneg hpb] at hdb
      rw [abs_lt]
      constructor <;> linarith
    · have hnb : reduce v < 0 := by
        by_contra hcon
        exact absurd (hside.mpr (not_lt.mp hcon)) (not_le.mpr hna)
      rw [abs_of_neg hna] at hda
      rw [abs_of_neg hnb] at hdb
      rw [abs_lt]
      constructor <;> linarith
  exact toIntDist_sub_lt (u := u) (v := v) (δ := δ) hδ hgap

/-- The bound for a truncated geometric sum whose frequency sits at circle level `k`. -/
noncomputable def levelBound (N : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then (N : ℝ) else 1 / (2 * δ * k)

theorem levelBound_nonneg (N : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (k : ℕ) : 0 ≤ levelBound N δ k := by
  unfold levelBound
  split_ifs <;> positivity

/-- A geometric correlation of two circle frequencies is bounded by the level of their offset. -/
theorem norm_sum_conj_circleFreq_le (N : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (a b : ℝ) :
    ‖∑ n ∈ range N, (starRingEnd ℂ) (circleFreq a ^ n) * circleFreq b ^ n‖
      ≤ levelBound N δ (levelOf δ (b - a)) := by
  unfold levelBound
  split_ifs with hk
  · calc ‖∑ n ∈ range N, (starRingEnd ℂ) (circleFreq a ^ n) * circleFreq b ^ n‖
        ≤ ∑ n ∈ range N, ‖(starRingEnd ℂ) (circleFreq a ^ n) * circleFreq b ^ n‖ :=
          norm_sum_le _ _
      _ = ∑ _n ∈ range N, (1 : ℝ) := by
          refine sum_congr rfl fun n _ => ?_
          rw [norm_mul, RCLike.norm_conj, norm_pow, norm_pow, norm_circleFreq, norm_circleFreq]
          simp
      _ = N := by simp
  · have hk1 : (1 : ℝ) ≤ (levelOf δ (b - a) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hle := levelOf_mul_le (δ := δ) (x := b - a) hδ0
    have hpos : 0 < (levelOf δ (b - a) : ℝ) * δ := by positivity
    have hchord := four_mul_toIntDist_le_norm_sub a b
    have hne : (starRingEnd ℂ) (circleFreq a) * circleFreq b ≠ 1 := by
      intro hcon
      rw [hcon, sub_self, norm_zero] at hchord
      linarith
    refine le_trans
      (norm_sum_conj_pow_mul_pow_le (norm_circleFreq a) (norm_circleFreq b).le hne N) ?_
    have hden : 0 < ‖(starRingEnd ℂ) (circleFreq a) * circleFreq b - 1‖ := by linarith
    rw [div_le_div_iff₀ hden (by positivity)]
    nlinarith

/-- The sum of the level bounds over the levels `0, …, M`. -/
theorem sum_levelBound (N : ℕ) (δ : ℝ) (M : ℕ) :
    ∑ k ∈ range (M + 1), levelBound N δ k =
      N + 1 / (2 * δ) * ∑ k ∈ Icc 1 M, 1 / (k : ℝ) := by
  induction M with
  | zero => simp [levelBound]
  | succ M ih =>
    rw [sum_range_succ, ih, sum_Icc_succ_top (by omega), mul_add]
    have hk : levelBound N δ (M + 1) = 1 / (2 * δ) * (1 / ((M + 1 : ℕ) : ℝ)) := by
      unfold levelBound
      rw [if_neg (by omega)]
      rw [one_div_mul_one_div]
    rw [hk]
    ring

/-- **A Gram row of a separated planar family.** -/
theorem sum_norm_inner_planeRow_le {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι)
    (x y : ι → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      δ ≤ toIntDist (x b - x a) ∨ δ ≤ toIntDist (y b - y a))
    {M : ℕ} (hM : 1 / (2 * δ) ≤ (M : ℝ)) (r : ι) :
    ∑ t ∈ s, ‖⟪planeRow N (circleFreq (x r)) (circleFreq (y r)),
        planeRow N (circleFreq (x t)) (circleFreq (y t))⟫_ℂ‖
      ≤ (2 * N + 1 / δ * ∑ k ∈ Icc 1 M, 1 / (k : ℝ)) ^ 2 := by
  classical
  -- the cell of a frequency: levels and sides of its two offsets from `r`
  set F : ι → (ℕ × Bool) × (ℕ × Bool) := fun t =>
    ((levelOf δ (x t - x r), decide (0 ≤ reduce (x t - x r))),
      (levelOf δ (y t - y r), decide (0 ≤ reduce (y t - y r)))) with hF
  set g : (ℕ × Bool) × (ℕ × Bool) → ℝ := fun p =>
    levelBound N δ p.1.1 * levelBound N δ p.2.1 with hg
  set B : Finset (ℕ × Bool) := range (M + 1) ×ˢ (univ : Finset Bool) with hB
  have hterm : ∀ t ∈ s, ‖⟪planeRow N (circleFreq (x r)) (circleFreq (y r)),
      planeRow N (circleFreq (x t)) (circleFreq (y t))⟫_ℂ‖ ≤ g (F t) := by
    intro t _
    rw [inner_planeRow, norm_mul]
    exact mul_le_mul (norm_sum_conj_circleFreq_le N hδ0 (x r) (x t))
      (norm_sum_conj_circleFreq_le N hδ0 (y r) (y t)) (norm_nonneg _)
      (levelBound_nonneg N hδ0 _)
  -- the cell separates the frequencies
  have hinj : ∀ a ∈ s, ∀ b ∈ s, F a = F b → a = b := by
    intro a ha b hb hab
    by_contra hne
    simp only [hF, Prod.mk.injEq, decide_eq_decide] at hab
    obtain ⟨⟨hlx, hsx⟩, hly, hsy⟩ := hab
    have hcx := toIntDist_sub_lt_of_levelOf_eq hδ0 hδ hlx hsx
    have hcy := toIntDist_sub_lt_of_levelOf_eq hδ0 hδ hly hsy
    have hex : (x a - x r) - (x b - x r) = x a - x b := by ring
    have hey : (y a - y r) - (y b - y r) = y a - y b := by ring
    rw [hex] at hcx
    rw [hey] at hcy
    rcases hsep b hb a ha (Ne.symm hne) with h | h <;> linarith
  have himg : s.image F ⊆ B ×ˢ B := by
    intro p hp
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hp
    simp only [hF, hB, mem_product, mem_range, mem_univ, and_true]
    exact ⟨Nat.lt_succ_of_le (levelOf_le hδ0 hM), Nat.lt_succ_of_le (levelOf_le hδ0 hM)⟩
  have hmono : ∑ p ∈ s.image F, g p ≤ ∑ p ∈ B ×ˢ B, g p :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun p _ _ =>
      mul_nonneg (levelBound_nonneg N hδ0 _) (levelBound_nonneg N hδ0 _)
  have hside : ∑ q ∈ B, levelBound N δ q.1 = 2 * ∑ k ∈ range (M + 1), levelBound N δ k := by
    rw [hB, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    norm_num
  have hrect : ∑ p ∈ B ×ˢ B, g p = (∑ q ∈ B, levelBound N δ q.1) ^ 2 := by
    rw [Finset.sum_product, sq, Finset.sum_mul_sum]
  calc ∑ t ∈ s, ‖⟪planeRow N (circleFreq (x r)) (circleFreq (y r)),
        planeRow N (circleFreq (x t)) (circleFreq (y t))⟫_ℂ‖
      ≤ ∑ t ∈ s, g (F t) := Finset.sum_le_sum hterm
    _ = ∑ p ∈ s.image F, g p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ B ×ˢ B, g p := hmono
    _ = (2 * N + 1 / δ * ∑ k ∈ Icc 1 M, 1 / (k : ℝ)) ^ 2 := by
        rw [hrect, hside, sum_levelBound]
        congr 1
        field_simp

/-- **The planar large sieve, Bessel form.** -/
theorem planarLargeSieve_bessel {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι)
    (x y : ι → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      δ ≤ toIntDist (x b - x a) ∨ δ ≤ toIntDist (y b - y a))
    {M : ℕ} (hM : 1 / (2 * δ) ≤ (M : ℝ)) (a : EuclideanSpace ℂ (Fin N × Fin N)) :
    ∑ r ∈ s, ‖⟪planeRow N (circleFreq (x r)) (circleFreq (y r)), a⟫_ℂ‖ ^ (2 : ℕ)
      ≤ (2 * N + 1 / δ * ∑ k ∈ Icc 1 M, 1 / (k : ℝ)) ^ 2 * ‖a‖ ^ (2 : ℕ) :=
  sum_norm_inner_sq_le_of_schur s
    (fun r => planeRow N (circleFreq (x r)) (circleFreq (y r))) (sq_nonneg _)
    (fun r _ => sum_norm_inner_planeRow_le N s x y hδ0 hδ hsep hM r) a

/-- **The planar large sieve, bilinear form.** -/
theorem planarLargeSieve_bilinear {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι)
    (x y : ι → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      δ ≤ toIntDist (x b - x a) ∨ δ ≤ toIntDist (y b - y a))
    {M : ℕ} (hM : 1 / (2 * δ) ≤ (M : ℝ)) (c : ι → ℂ) :
    ‖∑ r ∈ s, c r • planeRow N (circleFreq (x r)) (circleFreq (y r))‖ ^ (2 : ℕ)
      ≤ (2 * N + 1 / δ * ∑ k ∈ Icc 1 M, 1 / (k : ℝ)) ^ 2 * ∑ r ∈ s, ‖c r‖ ^ (2 : ℕ) :=
  norm_sum_smul_sq_le_of_schur s
    (fun r => planeRow N (circleFreq (x r)) (circleFreq (y r)))
    (fun r _ => sum_norm_inner_planeRow_le N s x y hδ0 hδ hsep hM r) c

/-- The bilinear form in coordinates: a mean square over the box `m, n < N`. -/
theorem norm_sq_sum_smul_planeRow {ι : Type*} (N : ℕ) (s : Finset ι) (ξ η : ι → ℂ)
    (c : ι → ℂ) :
    ‖∑ r ∈ s, c r • planeRow N (ξ r) (η r)‖ ^ (2 : ℕ)
      = ∑ p : Fin N × Fin N,
          ‖∑ r ∈ s, c r * ((ξ r) ^ (p.1 : ℕ) * (η r) ^ (p.2 : ℕ))‖ ^ (2 : ℕ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have happ : (∑ r ∈ s, c r • planeRow N (ξ r) (η r)) p
      = ∑ r ∈ s, c r * ((ξ r) ^ (p.1 : ℕ) * (η r) ^ (p.2 : ℕ)) := by
    simp [planeRow]
  rw [happ]

/-- **The planar large sieve as a mean square over the box.** -/
theorem sum_norm_sq_sum_mul_le {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι)
    (x y : ι → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      δ ≤ toIntDist (x b - x a) ∨ δ ≤ toIntDist (y b - y a))
    {M : ℕ} (hM : 1 / (2 * δ) ≤ (M : ℝ)) (c : ι → ℂ) :
    ∑ p : Fin N × Fin N,
        ‖∑ r ∈ s, c r * (circleFreq (x r) ^ (p.1 : ℕ) * circleFreq (y r) ^ (p.2 : ℕ))‖ ^ (2 : ℕ)
      ≤ (2 * N + 1 / δ * ∑ k ∈ Icc 1 M, 1 / (k : ℝ)) ^ 2 * ∑ r ∈ s, ‖c r‖ ^ (2 : ℕ) := by
  rw [← norm_sq_sum_smul_planeRow]
  exact planarLargeSieve_bilinear N s x y hδ0 hδ hsep hM c

end GaloisForLFunctions.FamilyContinuationTheory
