import GaloisForLFunctions.RHTower.Sieve.CircleDistance

/-!
# The Gram row of a family separated on the circle

A family of frequencies separated by `δ` in `ℝ/ℤ` has harmonic Gram rows:

`∑_{t ≠ r} ‖λ_t - λ_r‖^{-1} ≤ 2 δ^{-1} ∑_{1 ≤ k ≤ M} k^{-1}`,  `M ≥ (2δ)^{-1}`.

Unlike the real-line estimate of `SeparatedRowSum.lean`, the index ordering says nothing here — on
the circle the frequencies may wrap — so the count is made by *level* instead.  Reducing each
`λ_t - λ_r` modulo one gives an offset in `[-1/2, 1/2]` whose absolute value lies in some band
`[kδ, (k+1)δ)`.  Two frequencies in the same band on the same side of zero have offsets differing by
less than `δ`, hence lie within `δ` of each other on the circle (`toIntDist_sub_lt`), contradicting
the separation hypothesis.  So the level–side pair is injective, at most two frequencies occupy each
level, and every level is at most `(2δ)^{-1}` because the offsets never exceed `1/2`.

The resulting `δ^{-1} log δ^{-1}` is the honest ceiling of the absolute-value method, matching the
real-line bound: no ordering is used, only the separation.
-/

namespace RHTower.Sieve

open Finset

/-- The representative of a real number modulo one, taken in `[-1/2, 1/2]`. -/
noncomputable def reduce (x : ℝ) : ℝ := x - (round x : ℝ)

theorem toIntDist_eq_abs_reduce (x : ℝ) : toIntDist x = |reduce x| := rfl

/-- The band of a circle distance: the number of full `δ` steps it contains. -/
noncomputable def levelOf (δ x : ℝ) : ℕ := ⌊|reduce x| / δ⌋₊

/-- A separated frequency sits at a positive level. -/
theorem one_le_levelOf {δ x : ℝ} (hδ0 : 0 < δ) (hx : δ ≤ toIntDist x) : 1 ≤ levelOf δ x := by
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ hδ0, one_mul]
  exact hx

/-- The level is a lower bound for the circle distance. -/
theorem levelOf_mul_le {δ x : ℝ} (hδ0 : 0 < δ) : (levelOf δ x : ℝ) * δ ≤ toIntDist x := by
  have hnn : (0 : ℝ) ≤ |reduce x| / δ := by positivity
  have h := Nat.floor_le hnn
  rw [le_div_iff₀ hδ0] at h
  exact h

/-- The circle distance is below the next band. -/
theorem lt_levelOf_succ_mul {δ x : ℝ} (hδ0 : 0 < δ) :
    toIntDist x < ((levelOf δ x : ℝ) + 1) * δ := by
  have h := Nat.lt_floor_add_one (|reduce x| / δ)
  rw [div_lt_iff₀ hδ0] at h
  exact h

/-- Offsets never exceed a half, so levels never exceed `(2δ)^{-1}`. -/
theorem levelOf_le {δ x : ℝ} (hδ0 : 0 < δ) {M : ℕ} (hM : 1 / (2 * δ) ≤ (M : ℝ)) :
    levelOf δ x ≤ M := by
  have hhalf : |reduce x| ≤ 1 / 2 := toIntDist_le_half x
  have hprod : 1 / (2 * δ) * δ = 1 / 2 := by field_simp
  have h1 : 1 / (2 * δ) * δ ≤ (M : ℝ) * δ := mul_le_mul_of_nonneg_right hM (le_of_lt hδ0)
  rw [hprod] at h1
  have hbound : |reduce x| / δ ≤ (M : ℝ) := by
    rw [div_le_iff₀ hδ0]
    linarith
  calc levelOf δ x = ⌊|reduce x| / δ⌋₊ := rfl
    _ ≤ ⌊(M : ℝ)⌋₊ := Nat.floor_le_floor hbound
    _ = M := Nat.floor_natCast M

/-- **The Gram row of a `δ`-separated family on the circle is harmonic.** -/
theorem circle_row_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam : ι → ℝ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ toIntDist (lam b - lam a))
    {r : ι} (hr : r ∈ s) {M : ℕ} (hM : 1 / (2 * δ) ≤ (M : ℝ)) :
    ∑ t ∈ s.erase r, 1 / toIntDist (lam t - lam r)
      ≤ (2 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by
  classical
  set F : ι → ℕ × Bool :=
    fun t => (levelOf δ (lam t - lam r), decide (0 ≤ reduce (lam t - lam r))) with hF
  have hsep' : ∀ t ∈ s.erase r, δ ≤ toIntDist (lam t - lam r) := by
    intro t ht
    have ht' := Finset.mem_erase.mp ht
    exact hsep r hr t ht'.2 (Ne.symm ht'.1)
  -- termwise: the reciprocal distance is at most `δ⁻¹` times the reciprocal level
  have hterm : ∀ t ∈ s.erase r,
      1 / toIntDist (lam t - lam r) ≤ (1 / δ) * (1 / ((F t).1 : ℝ)) := by
    intro t ht
    have hs := hsep' t ht
    have hlev1 : 1 ≤ levelOf δ (lam t - lam r) := one_le_levelOf hδ0 hs
    have hlevR : (1 : ℝ) ≤ (levelOf δ (lam t - lam r) : ℝ) := by exact_mod_cast hlev1
    have hpos : (0 : ℝ) < (levelOf δ (lam t - lam r) : ℝ) * δ := by positivity
    have hle := levelOf_mul_le (δ := δ) (x := lam t - lam r) hδ0
    have hmain := one_div_le_one_div_of_le hpos hle
    have hval : 1 / ((levelOf δ (lam t - lam r) : ℝ) * δ)
        = (1 / δ) * (1 / (levelOf δ (lam t - lam r) : ℝ)) := by
      field_simp
    rw [hval] at hmain
    exact hmain
  -- the level–side pair separates the frequencies
  have hinj : ∀ a ∈ s.erase r, ∀ b ∈ s.erase r, F a = F b → a = b := by
    intro a ha b hb hab
    by_contra hne
    simp only [hF, Prod.mk.injEq, decide_eq_decide] at hab
    obtain ⟨hlev, hside⟩ := hab
    have hla := levelOf_mul_le (δ := δ) (x := lam a - lam r) hδ0
    have hlb := levelOf_mul_le (δ := δ) (x := lam b - lam r) hδ0
    have hua := lt_levelOf_succ_mul (δ := δ) (x := lam a - lam r) hδ0
    have hub := lt_levelOf_succ_mul (δ := δ) (x := lam b - lam r) hδ0
    rw [hlev] at hla hua
    -- both offsets lie in the band `[k δ, (k+1) δ)`, so they differ by less than `δ`
    have hgap : |reduce (lam a - lam r) - reduce (lam b - lam r)| < δ := by
      have hda : |reduce (lam a - lam r)| = toIntDist (lam a - lam r) := rfl
      have hdb : |reduce (lam b - lam r)| = toIntDist (lam b - lam r) := rfl
      rcases le_or_gt 0 (reduce (lam a - lam r)) with hpa | hna
      · have hpb : 0 ≤ reduce (lam b - lam r) := hside.mp hpa
        rw [abs_of_nonneg hpa] at hda
        rw [abs_of_nonneg hpb] at hdb
        rw [abs_lt]
        constructor <;> linarith [hla, hlb, hua, hub, hda, hdb]
      · have hnb : reduce (lam b - lam r) < 0 := by
          by_contra hcon
          exact absurd (hside.mpr (not_lt.mp hcon)) (not_le.mpr hna)
        rw [abs_of_neg hna] at hda
        rw [abs_of_neg hnb] at hdb
        rw [abs_lt]
        constructor <;> linarith [hla, hlb, hua, hub, hda, hdb]
    -- so they are within `δ` on the circle, contradicting separation
    have hclose := toIntDist_sub_lt (u := lam a - lam r) (v := lam b - lam r) (δ := δ) hδ hgap
    have heq : (lam a - lam r) - (lam b - lam r) = lam a - lam b := by ring
    rw [heq] at hclose
    have hfar : δ ≤ toIntDist (lam a - lam b) :=
      hsep b (Finset.mem_of_mem_erase hb) a (Finset.mem_of_mem_erase ha) (Ne.symm hne)
    linarith
  -- pass to the image and enlarge it to the full band × side rectangle
  have himg : (s.erase r).image F ⊆ Finset.Icc 1 M ×ˢ (Finset.univ : Finset Bool) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_Icc]
    exact ⟨one_le_levelOf hδ0 (hsep' t ht), levelOf_le hδ0 hM⟩
  have hsum_image : ∑ p ∈ (s.erase r).image F, 1 / ((p.1 : ℕ) : ℝ)
      = ∑ t ∈ s.erase r, 1 / ((F t).1 : ℝ) :=
    Finset.sum_image hinj
  have hnonneg : ∀ p ∈ Finset.Icc 1 M ×ˢ (Finset.univ : Finset Bool),
      p ∉ (s.erase r).image F → (0 : ℝ) ≤ 1 / ((p.1 : ℕ) : ℝ) := by
    intro p _ _
    positivity
  have hmono : ∑ p ∈ (s.erase r).image F, 1 / ((p.1 : ℕ) : ℝ)
      ≤ ∑ p ∈ Finset.Icc 1 M ×ˢ (Finset.univ : Finset Bool), 1 / ((p.1 : ℕ) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg himg hnonneg
  have hrect : ∑ p ∈ Finset.Icc 1 M ×ˢ (Finset.univ : Finset Bool), 1 / ((p.1 : ℕ) : ℝ)
      = 2 * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hconst : ∀ y : Bool, (1 : ℝ) / (((k, y).1 : ℕ) : ℝ) = 1 / (k : ℝ) := fun _ => rfl
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ (Finset.univ : Finset Bool)) => hconst y),
      Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    norm_num
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  calc ∑ t ∈ s.erase r, 1 / toIntDist (lam t - lam r)
      ≤ ∑ t ∈ s.erase r, (1 / δ) * (1 / ((F t).1 : ℝ)) := Finset.sum_le_sum hterm
    _ = (1 / δ) * ∑ t ∈ s.erase r, 1 / ((F t).1 : ℝ) := by rw [Finset.mul_sum]
    _ = (1 / δ) * ∑ p ∈ (s.erase r).image F, 1 / ((p.1 : ℕ) : ℝ) := by rw [hsum_image]
    _ ≤ (1 / δ) * (2 * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ)) := by
        rw [← hrect]
        exact mul_le_mul_of_nonneg_left hmono hδinv
    _ = (2 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by ring

end RHTower.Sieve
