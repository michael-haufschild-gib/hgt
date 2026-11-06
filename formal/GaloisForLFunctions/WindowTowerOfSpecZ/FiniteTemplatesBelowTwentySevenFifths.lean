import GaloisForLFunctions.WindowTowerOfSpecZ.FiniteTemplatesEndAtTwentySevenFifths
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.Pigeonhole

/-!
# Finite rational Hecke templates exist below spread `27/5`

**Theorem** (`exists_finite_hecke_template`). For every `X < 27/5` a finite set contains one and is
closed under the ratio-two, three and five neighbours in `[1, X)`. With
`no_finite_hecke_template_at_twentySeven_fifths`, spread `27/5` is the exact end of finite templates.

* **Shears.** Let `g₀ ≤ g₁, g₂` be generators in a window `[1, W)`. Then `q ↦ q` on `[1, W/g₀)`,
  `q ↦ q/g₀` above it, sends edges to paths for the generators `g₀, g₁/g₀, g₂/g₀` in `[1, W/g₀)`,
  at most two to one. Five shears carry `(2, 3, 5)` on `[1, X)` to `(10/9, 81/80, 16/15)` on `[1, X/5)`.
* **Two generators.** In a window `[1, Y)`, `Y < uv`, at most one of `q ↦ uq`, `q ↦ q/v` is
  allowed at each point, so a component is a path. It is finite: two points of a long orbit are
  close, closeness forces the same branch at every later step, so the ratio persists and a power of
  it stays bounded.
-/

namespace GaloisForLFunctions.WindowTowerOfSpecZ

/-! ## Edges -/

/-- An edge of ratio `g` in the window `[1, W)`. -/
def HEdge (W g q s : ℚ) : Prop := 1 ≤ q ∧ q < W ∧ 1 ≤ s ∧ s < W ∧ s = g * q

/-- Adjacency for a list of generators. -/
def HAdj (W : ℚ) (G : List ℚ) (q s : ℚ) : Prop := ∃ g ∈ G, HEdge W g q s ∨ HEdge W g s q

/-- A set closed under adjacency. -/
def HClosed (W : ℚ) (G : List ℚ) (T : Finset ℚ) : Prop := ∀ q ∈ T, ∀ s, HAdj W G q s → s ∈ T

theorem HClosed.mono {W : ℚ} {G G' : List ℚ} (h : ∀ g ∈ G', g ∈ G) {T : Finset ℚ}
    (hT : HClosed W G T) : HClosed W G' T := by
  intro q hq s ⟨g, hg, he⟩
  exact hT q hq s ⟨g, h g hg, he⟩

/-! ## The shear -/

/-- The retraction of a window onto the smaller window. -/
def shearMap (W' g₀ q : ℚ) : ℚ := if q < W' then q else q / g₀

section Shear

variable {W g₀ g₁ g₂ : ℚ} {T' : Finset ℚ}

/-- An edge of ratio at least `g₀` lands in the smaller window at its lower end, and its image is
connected. -/
private theorem shear_edge (hg₀ : 1 < g₀) {g : ℚ} (hg : g₀ ≤ g)
    (hT' : HClosed (W / g₀) [g₀, g₁ / g₀, g₂ / g₀] T') (hmem : g = g₀ ∨ g = g₁ ∨ g = g₂)
    {q s : ℚ} (he : HEdge W g q s) :
    (shearMap (W / g₀) g₀ q ∈ T' ↔ shearMap (W / g₀) g₀ s ∈ T') := by
  obtain ⟨hq1, hqW, hs1, hsW, rfl⟩ := he
  have hg0 : 0 < g₀ := by linarith only [hg₀]
  have hq' : q < W / g₀ := by
    rw [lt_div_iff₀ hg0]
    have := mul_le_mul_of_nonneg_right hg (by linarith only [hq1] : 0 ≤ q)
    linarith only [this, hsW, mul_comm q g₀]
  have hπq : shearMap (W / g₀) g₀ q = q := by simp [shearMap, hq']
  rw [hπq]
  have hclosed2 : ∀ {p r : ℚ}, HAdj (W / g₀) [g₀, g₁ / g₀, g₂ / g₀] p r →
      (p ∈ T' ↔ r ∈ T') := by
    intro p r hadj
    refine ⟨fun hp => hT' p hp r hadj, fun hr => hT' r hr p ?_⟩
    obtain ⟨g', hg', he'⟩ := hadj
    exact ⟨g', hg', he'.symm⟩
  by_cases hs' : g * q < W / g₀
  · have hπs : shearMap (W / g₀) g₀ (g * q) = g * q := by simp [shearMap, hs']
    rw [hπs]
    rcases hmem with rfl | rfl | rfl
    · exact hclosed2 ⟨g₀, by simp, Or.inl ⟨hq1, hq', hs1, hs', rfl⟩⟩
    · have hh : 1 ≤ g₁ / g₀ := by rwa [one_le_div hg0]
      have hm1 : 1 ≤ g₁ / g₀ * q := by nlinarith only [hh, hq1]
      have hm2 : g₁ / g₀ * q < W / g₀ := by
        have : g₁ / g₀ * q ≤ g₁ * q := by
          have h3 : g₁ / g₀ ≤ g₁ := div_le_self (by linarith only [hg, hg₀]) hg₀.le
          exact mul_le_mul_of_nonneg_right h3 (by linarith only [hq1])
        linarith only [this, hs']
      have e1 := hclosed2 (p := q) (r := g₁ / g₀ * q)
        ⟨g₁ / g₀, by simp, Or.inl ⟨hq1, hq', hm1, hm2, rfl⟩⟩
      have e2 := hclosed2 (p := g₁ / g₀ * q) (r := g₁ * q)
        ⟨g₀, by simp, Or.inl ⟨hm1, hm2, hs1, hs', by field_simp⟩⟩
      exact e1.trans e2
    · have hh : 1 ≤ g₂ / g₀ := by rwa [one_le_div hg0]
      have hm1 : 1 ≤ g₂ / g₀ * q := by nlinarith only [hh, hq1]
      have hm2 : g₂ / g₀ * q < W / g₀ := by
        have : g₂ / g₀ * q ≤ g₂ * q := by
          have h3 : g₂ / g₀ ≤ g₂ := div_le_self (by linarith only [hg, hg₀]) hg₀.le
          exact mul_le_mul_of_nonneg_right h3 (by linarith only [hq1])
        linarith only [this, hs']
      have e1 := hclosed2 (p := q) (r := g₂ / g₀ * q)
        ⟨g₂ / g₀, by simp, Or.inl ⟨hq1, hq', hm1, hm2, rfl⟩⟩
      have e2 := hclosed2 (p := g₂ / g₀ * q) (r := g₂ * q)
        ⟨g₀, by simp, Or.inl ⟨hm1, hm2, hs1, hs', by field_simp⟩⟩
      exact e1.trans e2
  · have hπs : shearMap (W / g₀) g₀ (g * q) = g * q / g₀ := by simp [shearMap, hs']
    rw [hπs]
    have hlt : g * q / g₀ < W / g₀ := div_lt_div_of_pos_right hsW hg0
    rcases hmem with rfl | rfl | rfl
    · have e : g₀ * q / g₀ = q := by field_simp
      rw [e]
    · have hh : 1 ≤ g₁ / g₀ := by rwa [one_le_div hg0]
      have e : g₁ * q / g₀ = g₁ / g₀ * q := by ring
      rw [e] at hlt ⊢
      exact hclosed2 ⟨g₁ / g₀, by simp, Or.inl ⟨hq1, hq',
        by nlinarith only [hh, hq1], hlt, rfl⟩⟩
    · have hh : 1 ≤ g₂ / g₀ := by rwa [one_le_div hg0]
      have e : g₂ * q / g₀ = g₂ / g₀ * q := by ring
      rw [e] at hlt ⊢
      exact hclosed2 ⟨g₂ / g₀, by simp, Or.inl ⟨hq1, hq',
        by nlinarith only [hh, hq1], hlt, rfl⟩⟩

/-- **The shear step.** A finite closed set in the smaller window lifts. -/
theorem HClosed.shear (hg₀ : 1 < g₀) (h1 : g₀ ≤ g₁) (h2 : g₀ ≤ g₂)
    (hT' : HClosed (W / g₀) [g₀, g₁ / g₀, g₂ / g₀] T') (hone : 1 < W / g₀) (h1T : (1 : ℚ) ∈ T') :
    ∃ T : Finset ℚ, 1 ∈ T ∧ HClosed W [g₀, g₁, g₂] T := by
  classical
  have hg0 : 0 < g₀ := by linarith only [hg₀]
  let T : Finset ℚ := (T' ∪ T'.image fun p => g₀ * p).filter fun q =>
    shearMap (W / g₀) g₀ q ∈ T'
  refine ⟨T, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ h1T, ?_⟩
    have : shearMap (W / g₀) g₀ 1 = 1 := by simp [shearMap, hone]
    rwa [this]
  · intro q hq s ⟨g, hg, he⟩
    have hqT := (Finset.mem_filter.mp hq).2
    have hmem : g = g₀ ∨ g = g₁ ∨ g = g₂ := by simpa using hg
    have hle : g₀ ≤ g := by
      rcases hmem with rfl | rfl | rfl
      · exact le_rfl
      · exact h1
      · exact h2
    have hsT : shearMap (W / g₀) g₀ s ∈ T' := by
      rcases he with he | he
      · exact (shear_edge hg₀ hle hT' hmem he).mp hqT
      · exact (shear_edge hg₀ hle hT' hmem he).mpr hqT
    refine Finset.mem_filter.mpr ⟨?_, hsT⟩
    by_cases hs' : s < W / g₀
    · have : shearMap (W / g₀) g₀ s = s := by simp [shearMap, hs']
      rw [this] at hsT
      exact Finset.mem_union_left _ hsT
    · have : shearMap (W / g₀) g₀ s = s / g₀ := by simp [shearMap, hs']
      rw [this] at hsT
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s / g₀, hsT, ?_⟩)
      field_simp

end Shear

/-! ## Two generators -/

/-- The move with multiplier `u` below and divisor `v` above. -/
def twoStep (u v Y q : ℚ) : ℚ := if q < Y / u then u * q else q / v

/-- Iterates of the move from one. -/
def twoOrbit (u v Y : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => twoStep u v Y (twoOrbit u v Y n)

section TwoGenerators

variable {u v Y : ℚ}

/-- Close points of an orbit take the same branch, so their ratio persists. -/
private theorem ratio_persists (hu : 1 < u) (hv : 1 < v)
    (hwin : ∀ n, 1 ≤ twoOrbit u v Y n ∧ twoOrbit u v Y n < Y)
    {i j : ℕ} {r : ℚ} (hr : twoOrbit u v Y j = r * twoOrbit u v Y i)
    (hr1 : r * Y < u * v) (hr2 : Y < r * (u * v)) (m : ℕ) :
    twoOrbit u v Y (j + m) = r * twoOrbit u v Y (i + m) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hv0 : 0 < v := by linarith only [hv]
  induction m with
  | zero => simpa using hr
  | succ m ih =>
    obtain ⟨p, hp⟩ : ∃ p, p = twoOrbit u v Y (i + m) := ⟨_, rfl⟩
    obtain ⟨p', hp'⟩ : ∃ p', p' = twoOrbit u v Y (j + m) := ⟨_, rfl⟩
    rw [← hp, ← hp'] at ih
    have hnext1 := hwin (i + m + 1)
    have hnext2 := hwin (j + m + 1)
    have hpw := hwin (i + m)
    rw [← hp] at hpw
    have hp'w := hwin (j + m)
    rw [← hp'] at hp'w
    have e1 : twoOrbit u v Y (i + (m + 1)) = twoStep u v Y p := by
      rw [hp]
      rfl
    have e2 : twoOrbit u v Y (j + (m + 1)) = twoStep u v Y p' := by
      rw [hp']
      rfl
    have e1' : twoOrbit u v Y (i + m + 1) = twoStep u v Y p := by
      rw [hp]
      rfl
    have e2' : twoOrbit u v Y (j + m + 1) = twoStep u v Y p' := by
      rw [hp']
      rfl
    rw [e1'] at hnext1
    rw [e2'] at hnext2
    rw [e1, e2]
    have hp0 : 0 < p := by linarith only [hpw.1]
    unfold twoStep at hnext1 hnext2 ⊢
    by_cases h1 : p < Y / u
    · by_cases h2 : p' < Y / u
      · rw [if_pos h1, if_pos h2, ih]
        ring
      · exfalso
        rw [if_neg h2] at hnext2
        have h3 : v ≤ p' := by
          have := hnext2.1
          rwa [one_le_div hv0] at this
        rw [lt_div_iff₀ hu0] at h1
        rw [ih] at h3
        have h4 : r * v * (p * u) < r * v * Y := by
          refine mul_lt_mul_of_pos_left h1 ?_
          have hr0 : 0 < r := by
            by_contra hneg
            have : r * p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hp0.le
            linarith only [this, h3, hv]
          positivity
        nlinarith only [h3, h4, hr1, hv0, hu0, hp0, mul_pos hu0 hv0]
    · by_cases h2 : p' < Y / u
      · exfalso
        rw [if_neg h1] at hnext1
        have h3 : v ≤ p := by
          have := hnext1.1
          rwa [one_le_div hv0] at this
        rw [lt_div_iff₀ hu0, ih] at h2
        nlinarith only [h3, h2, hr2, hu0, hv0, mul_pos hu0 hv0, hp0]
      · rw [if_neg h1, if_neg h2, ih]
        ring

/-- **Orbits leave the window.** With `Y < uv`, the orbit cannot stay in the window while its
points are distinct. -/
theorem twoOrbit_exits (hu : 1 < u) (hv : 1 < v) (hY : Y < u * v)
    (hinj : (∀ n, 1 ≤ twoOrbit u v Y n ∧ twoOrbit u v Y n < Y) →
      Function.Injective (twoOrbit u v Y)) :
    ∃ n, ¬(1 ≤ twoOrbit u v Y n ∧ twoOrbit u v Y n < Y) := by
  classical
  by_contra hall
  push Not at hall
  have hwin : ∀ n, 1 ≤ twoOrbit u v Y n ∧ twoOrbit u v Y n < Y := fun n =>
    ⟨(hall n).1, (hall n).2⟩
  have hY1 : 1 < Y := (hwin 0).1.trans_lt (hwin 0).2
  have hY0 : 0 < Y := by linarith only [hY1]
  have huv : 0 < u * v := by nlinarith only [hu, hv]
  have hinj' := hinj hwin
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = u * v / Y := ⟨_, rfl⟩
  have hρ1 : 1 < ρ := by rw [hρ, one_lt_div hY0]; exact hY
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ρ - 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith only [hρ1]
  -- Two points of the orbit are close.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Y / δ < M := exists_nat_gt _
  have hmaps : ∀ k ∈ Finset.range (M + 1), ⌊twoOrbit u v Y k / δ⌋₊ ∈ Finset.range M := by
    intro k _
    rw [Finset.mem_range]
    have h1 : twoOrbit u v Y k / δ < M :=
      (div_lt_div_of_pos_right (hwin k).2 hδ0).trans hM
    exact (Nat.floor_lt (by have := (hwin k).1; positivity)).mpr h1
  obtain ⟨i₀, _, j₀, _, hne, hfl⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simp : (Finset.range M).card < (Finset.range (M + 1)).card) hmaps
  obtain ⟨i, j, hij, hfloor⟩ : ∃ i j, i < j ∧ ⌊twoOrbit u v Y i / δ⌋₊ = ⌊twoOrbit u v Y j / δ⌋₊ := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i₀, j₀, h, hfl⟩
    · exact ⟨j₀, i₀, h, hfl.symm⟩
  obtain ⟨a, ha⟩ : ∃ a, a = twoOrbit u v Y i := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = twoOrbit u v Y j := ⟨_, rfl⟩
  rw [← ha, ← hb] at hfloor
  have haw := hwin i
  have hbw := hwin j
  rw [← ha] at haw
  rw [← hb] at hbw
  have ha0 : 0 < a := by linarith only [haw.1]
  have hb0 : 0 < b := by linarith only [hbw.1]
  have hclose : |a - b| < δ := by
    have h1 := Nat.floor_le (by positivity : 0 ≤ a / δ)
    have h2 := Nat.lt_floor_add_one (a / δ)
    have h3 := Nat.floor_le (by positivity : 0 ≤ b / δ)
    have h4 := Nat.lt_floor_add_one (b / δ)
    rw [← hfloor] at h3 h4
    have h5 : a / δ - b / δ < 1 := by linarith only [h2, h3]
    have h6 : b / δ - a / δ < 1 := by linarith only [h1, h4]
    rw [abs_lt]
    rw [← sub_div, div_lt_one hδ0] at h5
    rw [← sub_div, div_lt_one hδ0] at h6
    constructor <;> linarith only [h5, h6]
  obtain ⟨r, hr⟩ : ∃ r, r = b / a := ⟨_, rfl⟩
  have hra : b = r * a := by rw [hr]; field_simp
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrne : r ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hra
    have : twoOrbit u v Y j = twoOrbit u v Y i := by rw [← hb, ← ha, hra]
    exact hij.ne' (hinj' this)
  obtain ⟨hcl1, hcl2⟩ := abs_lt.mp hclose
  have hr1 : r * Y < u * v := by
    have h1 : r < ρ := by
      rw [hr, div_lt_iff₀ ha0]
      nlinarith only [hcl1, hδ, haw.1, hρ1]
    have h2 := mul_lt_mul_of_pos_right h1 hY0
    rw [hρ, div_mul_cancel₀ _ hY0.ne'] at h2
    exact h2
  have hr2 : Y < r * (u * v) := by
    have h1 : ρ⁻¹ < r := by
      rw [hr, inv_lt_comm₀ (by linarith only [hρ1]) (by positivity), inv_div,
        div_lt_iff₀ hb0]
      nlinarith only [hcl2, hδ, hbw.1, hρ1]
    have h2 := mul_lt_mul_of_pos_right h1 huv
    have h3 : ρ⁻¹ * (u * v) = Y := by
      rw [hρ, inv_div]
      field_simp
    rwa [h3] at h2
  have hpers := ratio_persists hu hv hwin (i := i) (j := j) (r := r) (by rw [← hb, ← ha, hra])
    hr1 hr2
  -- A power of the ratio stays bounded.
  obtain ⟨d, hd⟩ : ∃ d, d = j - i := ⟨_, rfl⟩
  have hjd : j = i + d := by omega
  have hpow : ∀ k : ℕ, twoOrbit u v Y (i + k * d) = r ^ k * a := by
    intro k
    induction k with
    | zero => simp [ha]
    | succ k ih =>
      have h1 := hpers (k * d)
      rw [ih] at h1
      have e : i + (k + 1) * d = j + k * d := by
        rw [hjd]
        ring
      rw [e, h1, pow_succ]
      ring
  rcases lt_or_gt_of_ne hrne with hlt | hgt
  · obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt Y (one_lt_inv₀ hr0 |>.mpr hlt)
    have h1 := (hwin (i + k * d)).1
    rw [hpow k] at h1
    have h2 : r ^ k * Y < 1 := by
      have hrk : 0 < r ^ k := by positivity
      rw [inv_pow, lt_inv_comm₀ hY0 hrk] at hk
      calc r ^ k * Y < Y⁻¹ * Y := mul_lt_mul_of_pos_right hk hY0
        _ = 1 := inv_mul_cancel₀ hY0.ne'
    have h3 : r ^ k * a < r ^ k * Y := mul_lt_mul_of_pos_left haw.2 (by positivity)
    linarith only [h1, h2, h3]
  · obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt Y hgt
    have h1 := (hwin (i + k * d)).2
    rw [hpow k] at h1
    have h2 : r ^ k * 1 ≤ r ^ k * a := mul_le_mul_of_nonneg_left haw.1 (by positivity)
    linarith only [h1, h2, hk]

end TwoGenerators

/-! ## The terminal window -/

section Terminal

private theorem padic_one_add {p : ℚ} (hp : p ≠ 0) {c d : ℤ} (h : padicValRat 2 p = c)
    {g : ℚ} (hg : g ≠ 0) (hgv : padicValRat 2 g = d) :
    padicValRat 2 (g * p) = d + c := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValRat.mul hg hp, hgv, h]

private theorem padic_values :
    padicValRat 2 (81 / 80 : ℚ) = -4 ∧ padicValRat 2 (16 / 15 : ℚ) = 4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  have h16 : padicValRat 2 (16 : ℚ) = 4 := by
    have h := padicValRat.pow (p := 2) (q := 2) (k := 4)
    rw [htwo] at h
    norm_num at h
    exact h
  have hodd (n : ℕ) (hn : ¬2 ∣ n) : padicValRat 2 (n : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hn]
    rfl
  have h81 : padicValRat 2 (81 : ℚ) = 0 := by
    have h := hodd 81 (by norm_num)
    norm_num at h
    exact h
  have h5 : padicValRat 2 (5 : ℚ) = 0 := by
    have h := hodd 5 (by norm_num)
    norm_num at h
    exact h
  have h15 : padicValRat 2 (15 : ℚ) = 0 := by
    have h := hodd 15 (by norm_num)
    norm_num at h
    exact h
  constructor
  · rw [show (81 / 80 : ℚ) = 81 / 5 / 16 by norm_num, padicValRat.div (by norm_num) (by norm_num),
      padicValRat.div (by norm_num) (by norm_num), h81, h5, h16]
    norm_num
  · rw [padicValRat.div (by norm_num) (by norm_num), h16, h15]
    norm_num

/-- Valuations along an orbit: each step shifts by the same amount. -/
private theorem padic_twoOrbit {u v Y : ℚ} {c : ℤ} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (huv : padicValRat 2 u = c) (hvv : padicValRat 2 v = -c) (n : ℕ) :
    twoOrbit u v Y n ≠ 0 ∧ padicValRat 2 (twoOrbit u v Y n) = n * c := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction n with
  | zero => simp [twoOrbit]
  | succ n ih =>
    obtain ⟨h0, hv⟩ := ih
    have e : twoOrbit u v Y (n + 1) = twoStep u v Y (twoOrbit u v Y n) := rfl
    rw [e]
    unfold twoStep
    split_ifs
    · refine ⟨mul_ne_zero hu0 h0, ?_⟩
      rw [padicValRat.mul hu0 h0, huv, hv]
      push_cast
      ring
    · refine ⟨div_ne_zero h0 hv0, ?_⟩
      rw [padicValRat.div h0 hv0, hvv, hv]
      push_cast
      ring

private theorem twoOrbit_injective {u v Y : ℚ} {c : ℤ} (hc : c ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (huv : padicValRat 2 u = c) (hvv : padicValRat 2 v = -c) :
    Function.Injective (twoOrbit u v Y) := by
  intro i j hij
  have h1 := (padic_twoOrbit (Y := Y) hu0 hv0 huv hvv i).2
  have h2 := (padic_twoOrbit (Y := Y) hu0 hv0 huv hvv j).2
  rw [hij, h2] at h1
  have := mul_right_cancel₀ hc h1
  exact_mod_cast this.symm

/-- **The terminal window has a finite closed set.** -/
theorem exists_terminal_closed {Y : ℚ} (hY1 : 1 < Y) (hY : Y < 27 / 25) :
    ∃ T : Finset ℚ, 1 ∈ T ∧ HClosed Y [10 / 9, 81 / 80, 16 / 15] T := by
  classical
  obtain ⟨hA, hB⟩ := padic_values
  have hYuv : Y < (81 / 80 : ℚ) * (16 / 15) := by norm_num; linarith only [hY]
  have hYvu : Y < (16 / 15 : ℚ) * (81 / 80) := by norm_num; linarith only [hY]
  obtain ⟨n, hn⟩ := Nat.find_x (twoOrbit_exits (u := 81 / 80) (v := 16 / 15) (Y := Y)
    (by norm_num) (by norm_num) hYuv fun _ =>
      twoOrbit_injective (c := -4) (by norm_num) (by norm_num) (by norm_num) hA
        (by rw [hB]; norm_num))
  obtain ⟨m, hm⟩ := Nat.find_x (twoOrbit_exits (u := 16 / 15) (v := 81 / 80) (Y := Y)
    (by norm_num) (by norm_num) hYvu fun _ =>
      twoOrbit_injective (c := 4) (by norm_num) (by norm_num) (by norm_num) hB
        (by rw [hA]; norm_num))
  obtain ⟨hnexit, hnwin⟩ := hn
  obtain ⟨hmexit, hmwin⟩ := hm
  push Not at hnwin hmwin
  obtain ⟨x, hx⟩ : ∃ x, x = twoOrbit (81 / 80) (16 / 15) Y := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = twoOrbit (16 / 15) (81 / 80) Y := ⟨_, rfl⟩
  rw [← hx] at hnexit hnwin
  rw [← hy] at hmexit hmwin
  have hx0 : x 0 = 1 := by rw [hx]; rfl
  have hy0 : y 0 = 1 := by rw [hy]; rfl
  have hxs (k : ℕ) : x (k + 1) = twoStep (81 / 80) (16 / 15) Y (x k) := by rw [hx]; rfl
  have hys (k : ℕ) : y (k + 1) = twoStep (16 / 15) (81 / 80) Y (y k) := by rw [hy]; rfl
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hnexit (by rw [hx0]; exact ⟨le_rfl, hY1⟩)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hmexit (by rw [hy0]; exact ⟨le_rfl, hY1⟩)
  -- Staying in the orbit: if the next point is in the window, its index is below the exit time.
  have hxnext {k : ℕ} (hk : k < n) (h1 : 1 ≤ x (k + 1)) (h2 : x (k + 1) < Y) : k + 1 < n := by
    by_contra hc
    have : k + 1 = n := by omega
    rw [this] at h1 h2
    exact hnexit ⟨h1, h2⟩
  have hynext {k : ℕ} (hk : k < m) (h1 : 1 ≤ y (k + 1)) (h2 : y (k + 1) < Y) : k + 1 < m := by
    by_contra hc
    have : k + 1 = m := by omega
    rw [this] at h1 h2
    exact hmexit ⟨h1, h2⟩
  let T : Finset ℚ := (Finset.range n).image x ∪ (Finset.range m).image y
  have hxT {k : ℕ} (hk : k < n) : x k ∈ T :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩)
  have hyT {k : ℕ} (hk : k < m) : y k ∈ T :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩)
  refine ⟨T, ?_, ?_⟩
  · have := hxT (Nat.pos_of_ne_zero hn0)
    rwa [hx0] at this
  intro q hq s ⟨g, hg, he⟩
  have hgcases : g = 10 / 9 ∨ g = 81 / 80 ∨ g = 16 / 15 := by simpa using hg
  -- The large generator has no edge in this window.
  have hgne : g = 81 / 80 ∨ g = 16 / 15 := by
    rcases hgcases with rfl | h | h
    · exfalso
      rcases he with ⟨h1, _, _, h4, h5⟩ | ⟨h1, _, _, h4, h5⟩ <;>
        · rw [h5] at h4
          linarith only [h1, h4, hY]
    · exact Or.inl h
    · exact Or.inr h
  rcases Finset.mem_union.mp hq with hqx | hqy
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hqx
    have hk' := Finset.mem_range.mp hk
    have hxk := hnwin k hk'
    rcases hgne with rfl | rfl
    · rcases he with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
      · -- `s = (81/80) x_k`
        have hbr : x k < Y / (81 / 80) := by
          rw [lt_div_iff₀ (by norm_num)]
          linarith only [h4, h5]
        have hnx : x (k + 1) = s := by
          rw [hxs, h5]
          simp [twoStep, hbr]
        rw [← hnx]
        rw [← hnx] at h3 h4
        exact hxT (hxnext hk' h3 h4)
      · -- `x_k = (81/80) s`
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · rw [hx0] at h5
          linarith only [h5, h1]
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hk'' : k' < n := by omega
          have hprev := hxs k'
          unfold twoStep at hprev
          split_ifs at hprev with hb
          · have : s = x k' := by
              rw [hprev] at h5
              linarith only [h5]
            rw [this]
            exact hxT hk''
          · exfalso
            have hge : (16 / 15 : ℚ) ≤ x k' := by
              have := hnwin k' hk''
              by_contra hc
              rw [not_le] at hc
              have h6 : Y / (81 / 80) ≤ x k' := not_lt.1 hb
              linarith only [hYuv, h6, hc, (by
                rw [div_le_iff₀ (by norm_num)] at h6
                exact h6 : Y ≤ x k' * (81 / 80))]
            rw [hprev] at h5
            have h7 : x k' = 16 / 15 * (81 / 80) * s := by
              rw [show (16 / 15 : ℚ) * (81 / 80) * s = 16 / 15 * (81 / 80 * s) by ring, ← h5]
              ring
            have h8 := (hnwin k' hk'').2
            rw [h7] at h8
            have hs1 : (1 : ℚ) ≤ s := h1
            norm_num at h8
            linarith only [h8, hs1, hY]
    · rcases he with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
      · -- `s = (16/15) x_k`
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · rw [hx0] at h5
          have hy1 : y 1 = s := by
            have h6 := hys 0
            rw [hy0] at h6
            have hbr : (1 : ℚ) < Y / (16 / 15) := by
              rw [lt_div_iff₀ (by norm_num)]
              rw [h5] at h4
              linarith only [h4]
            rw [h6, h5]
            simp [twoStep, hbr]
          have hm1 : 1 < m := by
            have := hynext (k := 0) (Nat.pos_of_ne_zero hm0)
            rw [hy1] at this
            exact this h3 h4
          rw [← hy1]
          exact hyT hm1
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hk'' : k' < n := by omega
          have hprev := hxs k'
          unfold twoStep at hprev
          split_ifs at hprev with hb
          · exfalso
            have h6 := (hnwin k' hk'').1
            rw [hprev] at h5
            rw [h5] at h4
            norm_num at h4
            linarith only [h4, h6, hY]
          · have : s = x k' := by
              rw [hprev] at h5
              linarith only [h5]
            rw [this]
            exact hxT hk''
      · -- `x_k = (16/15) s`
        have hbr : ¬ x k < Y / (81 / 80) := by
          rw [not_lt, div_le_iff₀ (by norm_num)]
          rw [h5]
          linarith only [h3, hY]
        have hnx : x (k + 1) = s := by
          rw [hxs, h5]
          unfold twoStep
          rw [← h5, if_neg hbr, h5]
          field_simp
        rw [← hnx]
        rw [← hnx] at h3 h4
        exact hxT (hxnext hk' h3 h4)
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hqy
    have hk' := Finset.mem_range.mp hk
    have hyk := hmwin k hk'
    rcases hgne with rfl | rfl
    · rcases he with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
      · -- `s = (81/80) y_k`
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · rw [hy0] at h5
          have hx1 : x 1 = s := by
            have h6 := hxs 0
            rw [hx0] at h6
            have hbr : (1 : ℚ) < Y / (81 / 80) := by
              rw [lt_div_iff₀ (by norm_num)]
              rw [h5] at h4
              linarith only [h4]
            rw [h6, h5]
            simp [twoStep, hbr]
          have hn1 : 1 < n := by
            have := hxnext (k := 0) (Nat.pos_of_ne_zero hn0)
            rw [hx1] at this
            exact this h3 h4
          rw [← hx1]
          exact hxT hn1
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hk'' : k' < m := by omega
          have hprev := hys k'
          unfold twoStep at hprev
          split_ifs at hprev with hb
          · exfalso
            have h6 := (hmwin k' hk'').1
            rw [hprev] at h5
            rw [h5] at h4
            norm_num at h4
            linarith only [h4, h6, hY]
          · have : s = y k' := by
              rw [hprev] at h5
              linarith only [h5]
            rw [this]
            exact hyT hk''
      · -- `y_k = (81/80) s`
        have hbr : ¬ y k < Y / (16 / 15) := by
          rw [not_lt, div_le_iff₀ (by norm_num)]
          rw [h5]
          linarith only [h3, hY]
        have hnx : y (k + 1) = s := by
          rw [hys, h5]
          unfold twoStep
          rw [← h5, if_neg hbr, h5]
          field_simp
        rw [← hnx]
        rw [← hnx] at h3 h4
        exact hyT (hynext hk' h3 h4)
    · rcases he with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
      · -- `s = (16/15) y_k`
        have hbr : y k < Y / (16 / 15) := by
          rw [lt_div_iff₀ (by norm_num)]
          linarith only [h4, h5]
        have hnx : y (k + 1) = s := by
          rw [hys, h5]
          simp [twoStep, hbr]
        rw [← hnx]
        rw [← hnx] at h3 h4
        exact hyT (hynext hk' h3 h4)
      · -- `y_k = (16/15) s`
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · rw [hy0] at h5
          linarith only [h5, h1]
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hk'' : k' < m := by omega
          have hprev := hys k'
          unfold twoStep at hprev
          split_ifs at hprev with hb
          · have : s = y k' := by
              rw [hprev] at h5
              linarith only [h5]
            rw [this]
            exact hyT hk''
          · exfalso
            rw [hprev] at h5
            have h7 : y k' = 81 / 80 * (16 / 15) * s := by
              rw [show (81 / 80 : ℚ) * (16 / 15) * s = 81 / 80 * (16 / 15 * s) by ring, ← h5]
              ring
            have h8 := (hmwin k' hk'').2
            rw [h7] at h8
            have hs1 : (1 : ℚ) ≤ s := h1
            norm_num at h8
            linarith only [h8, hs1, hY]

end Terminal

/-! ## The templates -/

/-- **The finite template below `27/5`.** -/
theorem exists_finite_hecke_template {X : ℚ} (hX : X < 27 / 5) :
    ∃ T : Finset ℚ, 1 ∈ T ∧ HeckeClosed X T := by
  classical
  -- It is enough to work near the threshold.
  obtain ⟨X', hX'⟩ : ∃ X', X' = max X (26 / 5) := ⟨_, rfl⟩
  have hX'hi : X' < 27 / 5 := by rw [hX']; exact max_lt hX (by norm_num)
  have hX'lo : 26 / 5 ≤ X' := by rw [hX']; exact le_max_right _ _
  have hXX' : X ≤ X' := by rw [hX']; exact le_max_left _ _
  obtain ⟨T₅, h₅1, h₅⟩ := exists_terminal_closed (Y := X' / 5) (by linarith only [hX'lo])
    (by linarith only [hX'hi])
  -- Five shears.
  have h4 : HClosed (2 * X' / 9 / (10 / 9)) [10 / 9, 9 / 8 / (10 / 9), 32 / 27 / (10 / 9)] T₅ := by
    have e : 2 * X' / 9 / (10 / 9) = X' / 5 := by ring
    rw [e]
    refine HClosed.mono ?_ h₅
    intro g hg
    norm_num at hg ⊢
    tauto
  obtain ⟨T₄, h₄1, h₄⟩ := HClosed.shear (W := 2 * X' / 9) (g₀ := 10 / 9) (g₁ := 9 / 8) (g₂ := 32 / 27)
    (by norm_num) (by norm_num) (by norm_num) h4
    (by rw [show 2 * X' / 9 / (10 / 9) = X' / 5 by ring]; linarith only [hX'lo]) h₅1
  have h3 : HClosed (X' / 4 / (9 / 8)) [9 / 8, 5 / 4 / (9 / 8), 4 / 3 / (9 / 8)] T₄ := by
    have e : X' / 4 / (9 / 8) = 2 * X' / 9 := by ring
    rw [e]
    refine HClosed.mono ?_ h₄
    intro g hg
    norm_num at hg ⊢
    tauto
  obtain ⟨T₃, h₃1, h₃⟩ := HClosed.shear (W := X' / 4) (g₀ := 9 / 8) (g₁ := 5 / 4) (g₂ := 4 / 3)
    (by norm_num) (by norm_num) (by norm_num) h3
    (by rw [show X' / 4 / (9 / 8) = 2 * X' / 9 by ring]; linarith only [hX'lo]) h₄1
  have h2 : HClosed (X' / 3 / (4 / 3)) [4 / 3, 3 / 2 / (4 / 3), 5 / 3 / (4 / 3)] T₃ := by
    have e : X' / 3 / (4 / 3) = X' / 4 := by ring
    rw [e]
    refine HClosed.mono ?_ h₃
    intro g hg
    norm_num at hg ⊢
    tauto
  obtain ⟨T₂, h₂1, h₂⟩ := HClosed.shear (W := X' / 3) (g₀ := 4 / 3) (g₁ := 3 / 2) (g₂ := 5 / 3)
    (by norm_num) (by norm_num) (by norm_num) h2
    (by rw [show X' / 3 / (4 / 3) = X' / 4 by ring]; linarith only [hX'lo]) h₃1
  have h1 : HClosed (X' / 2 / (3 / 2)) [3 / 2, 2 / (3 / 2), 5 / 2 / (3 / 2)] T₂ := by
    have e : X' / 2 / (3 / 2) = X' / 3 := by ring
    rw [e]
    refine HClosed.mono ?_ h₂
    intro g hg
    norm_num at hg ⊢
    tauto
  obtain ⟨T₁, h₁1, h₁⟩ := HClosed.shear (W := X' / 2) (g₀ := 3 / 2) (g₁ := 2) (g₂ := 5 / 2)
    (by norm_num) (by norm_num) (by norm_num) h1
    (by rw [show X' / 2 / (3 / 2) = X' / 3 by ring]; linarith only [hX'lo]) h₂1
  have h0 : HClosed (X' / 2) [2, 3 / 2, 5 / 2] T₁ := by
    refine HClosed.mono ?_ h₁
    intro g hg
    norm_num at hg ⊢
    tauto
  obtain ⟨T₀, h₀1, h₀⟩ := HClosed.shear (W := X') (g₀ := 2) (g₁ := 3) (g₂ := 5)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      refine HClosed.mono ?_ h0
      intro g hg
      norm_num at hg ⊢
      tauto)
    (by linarith only [hX'lo]) h₁1
  -- Restriction to the window of `X`.
  refine ⟨T₀.filter fun q => q < X ∨ q = 1, Finset.mem_filter.mpr ⟨h₀1, Or.inr rfl⟩, ?_⟩
  intro q hq s hs1 hsX hrel
  obtain ⟨hqT, hqX⟩ := Finset.mem_filter.mp hq
  have hq1 : 1 ≤ q := by
    by_contra hc
    rw [not_le] at hc
    rcases hqX with h | h
    · rcases hrel with h1 | h1 | h1 | h1 | h1 | h1 <;> linarith only [h1, hc, hs1, hsX, h]
    · rw [h] at hc
      exact lt_irrefl _ hc
  have hqX' : q < X' := by
    rcases hqX with h | h
    · linarith only [h, hXX']
    · rw [h]
      linarith only [hX'lo]
  have hsX' : s < X' := by linarith only [hsX, hXX']
  refine Finset.mem_filter.mpr ⟨?_, Or.inl hsX⟩
  have hedge (g : ℚ) (hg : g ∈ ([2, 3, 5] : List ℚ)) (he : s = g * q ∨ q = g * s) : s ∈ T₀ := by
    refine h₀ q hqT s ⟨g, hg, ?_⟩
    rcases he with he | he
    · exact Or.inl ⟨hq1, hqX', hs1, hsX', he⟩
    · exact Or.inr ⟨hs1, hsX', hq1, hqX', he⟩
  rcases hrel with h | h | h | h | h | h
  · exact hedge 2 (by simp) (Or.inl h)
  · exact hedge 2 (by simp) (Or.inr h)
  · exact hedge 3 (by simp) (Or.inl h)
  · exact hedge 3 (by simp) (Or.inr h)
  · exact hedge 5 (by simp) (Or.inl h)
  · exact hedge 5 (by simp) (Or.inr h)

/-- **Finite templates end exactly at `27/5`.** -/
theorem exists_finite_hecke_template_iff (X : ℚ) :
    (∃ T : Finset ℚ, 1 ∈ T ∧ HeckeClosed X T) ↔ X < 27 / 5 := by
  constructor
  · intro h
    by_contra hc
    exact no_finite_hecke_template_at_twentySeven_fifths (not_lt.1 hc) h
  · exact exists_finite_hecke_template

end GaloisForLFunctions.WindowTowerOfSpecZ
