import GaloisForLFunctions.WindowTowerOfSpecZ.FiniteTemplatesEndAtTwentySevenFifths
import GaloisForLFunctions.WindowTowerOfSpecZ.FiniteTemplatesControlRationalHeckeGraphs
import GaloisForLFunctions.WindowTowerOfSpecZ.PositivePrimeMultipliersLowerTateDimension
import Mathlib

/-!
# Finite rational Hecke templates exist below spread `27/5`

**Theorem** (`exists_finite_hecke_template`). For every `X < 27/5` a finite set contains one and is
closed under the ratio-two, three and five neighbours in `[1, X)`. With
`no_finite_hecke_template_at_twentySeven_fifths`, spread `27/5` is the exact end of finite templates
(`exists_finite_hecke_template_iff`).

**Theorem** (`tateFunction_nonneg_iff_template`). Below aperture `log(27/5)` the Tate horizon is exact:
one finite set of rationals in the window, independent of the dimension `k`, decides positivity at
every `k`.

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

theorem HAdj.symm {W : ℚ} {G : List ℚ} {q s : ℚ} (h : HAdj W G q s) : HAdj W G s q := by
  obtain ⟨g, hg, he⟩ := h
  exact ⟨g, hg, he.symm⟩

/-- A set closed under adjacency. -/
def HClosed (W : ℚ) (G : List ℚ) (T : Finset ℚ) : Prop := ∀ q ∈ T, ∀ s, HAdj W G q s → s ∈ T

theorem HClosed.mono {W : ℚ} {G G' : List ℚ} (h : ∀ g ∈ G', g ∈ G) {T : Finset ℚ}
    (hT : HClosed W G T) : HClosed W G' T := by
  intro q hq s ⟨g, hg, he⟩
  exact hT q hq s ⟨g, h g hg, he⟩

theorem HClosed.iff {W : ℚ} {G : List ℚ} {T : Finset ℚ} (hT : HClosed W G T) {p r : ℚ}
    (h : HAdj W G p r) : p ∈ T ↔ r ∈ T :=
  ⟨fun hp => hT p hp r h, fun hr => hT r hr p h.symm⟩

/-! ## The shear -/

/-- The retraction of a window onto the smaller window. -/
def shearMap (W' g₀ q : ℚ) : ℚ := if q < W' then q else q / g₀

/-- The image of an edge of ratio `g ≥ g₀` is connected, when `g₀` and either `g = g₀` or `g/g₀`
are generators of the smaller window. -/
private theorem shear_edge {W g₀ g : ℚ} {G : List ℚ} {T' : Finset ℚ} (hg₀ : 1 < g₀) (hg : g₀ ≤ g)
    (h0 : g₀ ∈ G) (hmem : g = g₀ ∨ g / g₀ ∈ G) (hT' : HClosed (W / g₀) G T') {q s : ℚ}
    (he : HEdge W g q s) :
    shearMap (W / g₀) g₀ q ∈ T' ↔ shearMap (W / g₀) g₀ s ∈ T' := by
  obtain ⟨hq1, hqW, hs1, hsW, rfl⟩ := he
  have hg0 : 0 < g₀ := by linarith only [hg₀]
  have hq0 : 0 ≤ q := by linarith only [hq1]
  have hq' : q < W / g₀ := by
    rw [lt_div_iff₀ hg0]
    have := mul_le_mul_of_nonneg_right hg hq0
    linarith only [this, hsW, mul_comm q g₀]
  have hπq : shearMap (W / g₀) g₀ q = q := by simp only [shearMap, if_pos hq']
  rw [hπq]
  -- The intermediate point `(g/g₀) q`.
  have hh : 1 ≤ g / g₀ := by rwa [one_le_div hg0]
  have hm1 : 1 ≤ g / g₀ * q := by nlinarith only [hh, hq1]
  have hm2 : g / g₀ * q < W / g₀ := by
    have e : g / g₀ * q = g * q / g₀ := by ring
    rw [e]
    exact div_lt_div_of_pos_right hsW hg0
  by_cases hs' : g * q < W / g₀
  · have hπs : shearMap (W / g₀) g₀ (g * q) = g * q := by simp only [shearMap, if_pos hs']
    rw [hπs]
    rcases hmem with h | h
    · have e : g * q = g₀ * q := by rw [h]
      rw [e]
      rw [e] at hs1 hs'
      exact hT'.iff ⟨g₀, h0, Or.inl ⟨hq1, hq', hs1, hs', rfl⟩⟩
    · have e1 := hT'.iff (p := q) (r := g / g₀ * q) ⟨g / g₀, h, Or.inl ⟨hq1, hq', hm1, hm2, rfl⟩⟩
      have e2 := hT'.iff (p := g / g₀ * q) (r := g * q)
        ⟨g₀, h0, Or.inl ⟨hm1, hm2, hs1, hs', by field_simp⟩⟩
      exact e1.trans e2
  · have hπs : shearMap (W / g₀) g₀ (g * q) = g / g₀ * q := by
      simp only [shearMap, if_neg hs']
      ring
    rw [hπs]
    rcases hmem with h | h
    · have e : g / g₀ * q = q := by
        rw [h, div_self hg0.ne', one_mul]
      rw [e]
    · exact hT'.iff ⟨g / g₀, h, Or.inl ⟨hq1, hq', hm1, hm2, rfl⟩⟩

/-- **The shear step.** A finite closed set in the smaller window lifts. -/
theorem HClosed.shear {W g₀ g₁ g₂ : ℚ} {T' : Finset ℚ} (hg₀ : 1 < g₀) (h1 : g₀ ≤ g₁) (h2 : g₀ ≤ g₂)
    (hT' : HClosed (W / g₀) [g₀, g₁ / g₀, g₂ / g₀] T') (hone : 1 < W / g₀) (h1T : (1 : ℚ) ∈ T') :
    ∃ T : Finset ℚ, 1 ∈ T ∧ HClosed W [g₀, g₁, g₂] T := by
  classical
  have hg0 : 0 < g₀ := by linarith only [hg₀]
  let T : Finset ℚ := (T' ∪ T'.image fun p => g₀ * p).filter fun q =>
    shearMap (W / g₀) g₀ q ∈ T'
  refine ⟨T, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ h1T, ?_⟩
    have : shearMap (W / g₀) g₀ 1 = 1 := by simp only [shearMap, if_pos hone]
    rwa [this]
  · intro q hq s ⟨g, hg, he⟩
    have hqT := (Finset.mem_filter.mp hq).2
    have hmem : g = g₀ ∨ g = g₁ ∨ g = g₂ := by simpa using hg
    have hle : g₀ ≤ g := by
      rcases hmem with h | h | h <;> rw [h]
      · exact h1
      · exact h2
    have hmem' : g = g₀ ∨ g / g₀ ∈ [g₀, g₁ / g₀, g₂ / g₀] := by
      rcases hmem with h | h | h
      · exact Or.inl h
      · rw [h]
        exact Or.inr (by simp)
      · rw [h]
        exact Or.inr (by simp)
    have h0 : g₀ ∈ [g₀, g₁ / g₀, g₂ / g₀] := by simp
    have hsT : shearMap (W / g₀) g₀ s ∈ T' := by
      rcases he with he | he
      · exact (shear_edge hg₀ hle h0 hmem' hT' he).mp hqT
      · exact (shear_edge hg₀ hle h0 hmem' hT' he).mpr hqT
    refine Finset.mem_filter.mpr ⟨?_, hsT⟩
    by_cases hs' : s < W / g₀
    · have : shearMap (W / g₀) g₀ s = s := by simp only [shearMap, if_pos hs']
      rw [this] at hsT
      exact Finset.mem_union_left _ hsT
    · have : shearMap (W / g₀) g₀ s = s / g₀ := by simp only [shearMap, if_neg hs']
      rw [this] at hsT
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s / g₀, hsT, ?_⟩)
      field_simp

/-! ## Two generators -/

/-- The move with multiplier `u` below and divisor `v` above. -/
def twoStep (u v Y q : ℚ) : ℚ := if q < Y / u then u * q else q / v

/-- Iterates of the move from one. -/
def twoOrbit (u v Y : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => twoStep u v Y (twoOrbit u v Y n)

/-- A point of the window. -/
def InWin (Y q : ℚ) : Prop := 1 ≤ q ∧ q < Y

section TwoGenerators

variable {u v Y : ℚ}

/-- Close points of an orbit take the same branch, so their ratio persists. -/
private theorem ratio_persists (hu : 1 < u) (hv : 1 < v)
    (hwin : ∀ n, InWin Y (twoOrbit u v Y n))
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
    have hnext1 := (hwin (i + m + 1)).1
    have hnext2 := (hwin (j + m + 1)).1
    have hpw := (hwin (i + m)).1
    rw [← hp] at hpw
    have hp'w := (hwin (j + m)).1
    rw [← hp'] at hp'w
    have e1 : twoOrbit u v Y (i + (m + 1)) = twoStep u v Y p := by rw [hp]; rfl
    have e2 : twoOrbit u v Y (j + (m + 1)) = twoStep u v Y p' := by rw [hp']; rfl
    have e1' : twoOrbit u v Y (i + m + 1) = twoStep u v Y p := by rw [hp]; rfl
    have e2' : twoOrbit u v Y (j + m + 1) = twoStep u v Y p' := by rw [hp']; rfl
    rw [e1'] at hnext1
    rw [e2'] at hnext2
    rw [e1, e2]
    have hp0 : 0 < p := by linarith only [hpw]
    have h1p : 1 ≤ r * p := by rw [← ih]; exact hp'w
    have hr0 : 0 < r := by
      by_contra hneg
      have : r * p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hp0.le
      linarith only [this, h1p]
    unfold twoStep at hnext1 hnext2 ⊢
    by_cases h1 : p < Y / u
    · by_cases h2 : p' < Y / u
      · rw [if_pos h1, if_pos h2, ih]
        ring
      · exfalso
        rw [if_neg h2] at hnext2
        have h3 : v ≤ p' := by rwa [one_le_div hv0] at hnext2
        rw [lt_div_iff₀ hu0] at h1
        rw [ih] at h3
        have h5 : r * (p * u) < r * Y := mul_lt_mul_of_pos_left h1 hr0
        have h6 : u * v ≤ u * (r * p) := mul_le_mul_of_nonneg_left h3 hu0.le
        linarith only [h5, h6, hr1]
    · by_cases h2 : p' < Y / u
      · exfalso
        rw [if_neg h1] at hnext1
        have h3 : v ≤ p := by rwa [one_le_div hv0] at hnext1
        rw [lt_div_iff₀ hu0, ih] at h2
        have h5 : r * u * v ≤ r * u * p :=
          mul_le_mul_of_nonneg_left h3 (mul_pos hr0 hu0).le
        linarith only [h5, h2, hr2]
      · rw [if_neg h1, if_neg h2, ih]
        ring

/-- **Orbits leave the window.** With `Y < uv`, the orbit of `1` cannot stay in the window while its
points are distinct. -/
theorem twoOrbit_exits (hu : 1 < u) (hv : 1 < v) (hY : Y < u * v)
    (hinj : Function.Injective (twoOrbit u v Y)) :
    ∃ n, ¬InWin Y (twoOrbit u v Y n) := by
  classical
  by_contra hall
  push Not at hall
  have hwin : ∀ n, InWin Y (twoOrbit u v Y n) := hall
  have hY1 : 1 < Y := (hwin 0).1.trans_lt (hwin 0).2
  have hY0 : 0 < Y := by linarith only [hY1]
  have huv : 0 < u * v := by nlinarith only [hu, hv]
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = u * v / Y := ⟨_, rfl⟩
  have hρ1 : 1 < ρ := by rw [hρ, one_lt_div hY0]; exact hY
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ρ - 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith only [hρ1]
  -- Two points of the orbit are close.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Y / δ < M := exists_nat_gt _
  have hmaps : Set.MapsTo (fun k => ⌊twoOrbit u v Y k / δ⌋₊) (Finset.range (M + 1) : Finset ℕ)
      (Finset.range M : Finset ℕ) := by
    intro k _
    have h1 : twoOrbit u v Y k / δ < M :=
      (div_lt_div_of_pos_right (hwin k).2 hδ0).trans hM
    have h0 : 0 ≤ twoOrbit u v Y k / δ :=
      div_nonneg (by linarith only [(hwin k).1]) hδ0.le
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr ((Nat.floor_lt h0).mpr h1))
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
    rw [← sub_div, div_lt_one hδ0] at h5 h6
    rw [abs_lt]
    constructor <;> linarith only [h5, h6]
  obtain ⟨r, hr⟩ : ∃ r, r = b / a := ⟨_, rfl⟩
  have hra : b = r * a := by rw [hr]; field_simp
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrne : r ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hra
    have : twoOrbit u v Y j = twoOrbit u v Y i := by rw [← hb, ← ha, hra]
    exact hij.ne' (hinj this)
  obtain ⟨hcl1, hcl2⟩ := abs_lt.mp hclose
  have hr1 : r * Y < u * v := by
    have h1 : r < ρ := by
      rw [hr, div_lt_iff₀ ha0]
      nlinarith only [hcl1, hδ, haw.1, hρ1, mul_nonneg (sub_nonneg.2 hρ1.le) (sub_nonneg.2 haw.1)]
    have h2 := mul_lt_mul_of_pos_right h1 hY0
    rw [hρ, div_mul_cancel₀ _ hY0.ne'] at h2
    exact h2
  have hr2 : Y < r * (u * v) := by
    have h1 : ρ⁻¹ < r := by
      rw [hr, inv_lt_comm₀ (by linarith only [hρ1]) (by positivity), inv_div, div_lt_iff₀ hb0]
      nlinarith only [hcl2, hδ, hbw.1, hρ1, mul_nonneg (sub_nonneg.2 hρ1.le) (sub_nonneg.2 hbw.1)]
    have h2 := mul_lt_mul_of_pos_right h1 huv
    have h3 : ρ⁻¹ * (u * v) = Y := by
      rw [hρ, inv_div, div_mul_cancel₀ _ huv.ne']
    rwa [h3] at h2
  have hpers := ratio_persists hu hv hwin (i := i) (j := j) (r := r)
    (by rw [← hb, ← ha, hra]) hr1 hr2
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
  · obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt Y ((one_lt_inv₀ hr0).mpr hlt)
    have h1 := (hwin (i + k * d)).1
    rw [hpow k] at h1
    have hrk : 0 < r ^ k := by positivity
    have h2 : r ^ k * Y < 1 := by
      rw [inv_pow, lt_inv_comm₀ hY0 hrk] at hk
      calc r ^ k * Y < Y⁻¹ * Y := mul_lt_mul_of_pos_right hk hY0
        _ = 1 := inv_mul_cancel₀ hY0.ne'
    have h3 : r ^ k * a < r ^ k * Y := mul_lt_mul_of_pos_left haw.2 hrk
    linarith only [h1, h2, h3]
  · obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt Y hgt
    have h1 := (hwin (i + k * d)).2
    rw [hpow k] at h1
    have h2 : r ^ k * 1 ≤ r ^ k * a := mul_le_mul_of_nonneg_left haw.1 (by positivity)
    linarith only [h1, h2, hk]

/-- The first exit time of the orbit. -/
theorem exists_first_exit (H : ∃ n, ¬InWin Y (twoOrbit u v Y n)) :
    ∃ n, ¬InWin Y (twoOrbit u v Y n) ∧ ∀ k < n, InWin Y (twoOrbit u v Y k) := by
  classical
  exact ⟨Nat.find H, Nat.find_spec H, fun k hk => not_not.1 (Nat.find_min H hk)⟩

/-- Every neighbour of a point of the orbit lies on the orbit or on the opposite orbit. -/
private theorem orbit_neighbour (hu : 1 < u) (hv : 1 < v) (hY : Y < u * v) {n m : ℕ}
    (hnexit : ¬InWin Y (twoOrbit u v Y n)) (hnwin : ∀ k < n, InWin Y (twoOrbit u v Y k))
    (hmexit : ¬InWin Y (twoOrbit v u Y m)) {k : ℕ} (hk : k < n) {s : ℚ} (hs : InWin Y s)
    (hrel : (s = u * twoOrbit u v Y k ∨ twoOrbit u v Y k = u * s) ∨
      (s = v * twoOrbit u v Y k ∨ twoOrbit u v Y k = v * s)) :
    (∃ i < n, twoOrbit u v Y i = s) ∨ (∃ i < m, twoOrbit v u Y i = s) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hv0 : 0 < v := by linarith only [hv]
  have hs1 := hs.1
  have hsY := hs.2
  -- A successor in the window is on the orbit.
  have hnext {j : ℕ} (hj : j < n) (he : twoOrbit u v Y (j + 1) = s) :
      ∃ i < n, twoOrbit u v Y i = s := by
    refine ⟨j + 1, lt_of_le_of_ne hj fun h => hnexit ?_, he⟩
    rw [← h, he]
    exact hs
  have hstep (j : ℕ) : twoOrbit u v Y (j + 1) = twoStep u v Y (twoOrbit u v Y j) := rfl
  have hstep' (j : ℕ) : twoOrbit v u Y (j + 1) = twoStep v u Y (twoOrbit v u Y j) := rfl
  obtain ⟨x, hx⟩ : ∃ x, x = twoOrbit u v Y k := ⟨_, rfl⟩
  rw [← hx] at hrel
  rcases hrel with (h | h) | (h | h)
  · -- `s = u x`
    refine Or.inl (hnext hk ?_)
    have hb : x < Y / u := by
      rw [lt_div_iff₀ hu0, mul_comm, ← h]
      exact hsY
    rw [hstep, ← hx, h]
    simp only [twoStep, if_pos hb]
  · -- `x = u s`
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      have hx1 : x = 1 := by rw [hx, hk0]; rfl
      rw [hx1] at h
      nlinarith only [h, hu, hs1]
    · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk'' : k' < n := by omega
      have hprev := hstep k'
      rw [← hk', ← hx] at hprev
      unfold twoStep at hprev
      split_ifs at hprev with hb
      · refine Or.inl ⟨k', hk'', ?_⟩
        rw [hprev] at h
        exact mul_left_cancel₀ hu0.ne' h
      · exfalso
        have h7 : twoOrbit u v Y k' = v * x := by rw [hprev]; field_simp
        have h8 := (hnwin k' hk'').2
        rw [h7, h] at h8
        have h9 : u * v * 1 ≤ u * v * s := mul_le_mul_of_nonneg_left hs1 (by positivity)
        linarith only [h8, h9, hY]
  · -- `s = v x`
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have hx1 : x = 1 := by rw [hx, hk0]; rfl
      rw [hx1, mul_one] at h
      have hb : (1 : ℚ) < Y / v := by
        rw [lt_div_iff₀ hv0, one_mul, ← h]
        exact hsY
      have hy1 : twoOrbit v u Y 1 = s := by
        rw [hstep' 0]
        show twoStep v u Y 1 = s
        simp only [twoStep, if_pos hb, mul_one, h]
      refine Or.inr ⟨1, ?_, hy1⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hmexit ⟨le_rfl, hs1.trans_lt hsY⟩
      have hm1 : m ≠ 1 := by
        rintro rfl
        rw [hy1] at hmexit
        exact hmexit hs
      omega
    · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk'' : k' < n := by omega
      have hprev := hstep k'
      rw [← hk', ← hx] at hprev
      unfold twoStep at hprev
      split_ifs at hprev with hb
      · exfalso
        have h6 := (hnwin k' hk'').1
        rw [hprev] at h
        have h9 : u * v * 1 ≤ u * v * twoOrbit u v Y k' :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
        rw [h] at hsY
        linarith only [hsY, h9, hY]
      · refine Or.inl ⟨k', hk'', ?_⟩
        rw [h, hprev]
        field_simp
  · -- `x = v s`
    refine Or.inl (hnext hk ?_)
    have hb : ¬x < Y / u := by
      rw [not_lt, div_le_iff₀ hu0, h]
      have h9 : u * v * 1 ≤ u * v * s := mul_le_mul_of_nonneg_left hs1 (by positivity)
      linarith only [h9, hY]
    have hval : twoStep u v Y x = x / v := by simp only [twoStep, if_neg hb]
    rw [hstep, ← hx, hval, h]
    field_simp

end TwoGenerators

/-! ## The terminal window -/

private theorem padic_values :
    padicValRat 2 (81 / 80 : ℚ) = -4 ∧ padicValRat 2 (16 / 15 : ℚ) = 4 := by
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

/-- Each step of an orbit shifts the valuation by the same amount. -/
private theorem padic_twoOrbit {u v Y : ℚ} {c : ℤ} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (huv : padicValRat 2 u = c) (hvv : padicValRat 2 v = -c) (n : ℕ) :
    twoOrbit u v Y n ≠ 0 ∧ padicValRat 2 (twoOrbit u v Y n) = n * c := by
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

/-- **The terminal window has a finite closed set.** The generator `10/9` has no edge below `27/25`,
and the other two generators give the two orbits of `1`. -/
theorem exists_terminal_closed {Y : ℚ} (hY1 : 1 < Y) (hY : Y < 27 / 25) :
    ∃ T : Finset ℚ, 1 ∈ T ∧ HClosed Y [10 / 9, 81 / 80, 16 / 15] T := by
  classical
  obtain ⟨hA, hB⟩ := padic_values
  have hYuv : Y < (81 / 80 : ℚ) * (16 / 15) := by
    norm_num
    linarith only [hY]
  have hYvu : Y < (16 / 15 : ℚ) * (81 / 80) := by
    norm_num
    linarith only [hY]
  have hBn : padicValRat 2 (16 / 15 : ℚ) = -(-4 : ℤ) := by rw [hB]; norm_num
  obtain ⟨n, hnexit, hnwin⟩ := exists_first_exit
    (twoOrbit_exits (u := 81 / 80) (v := 16 / 15) (Y := Y) (by norm_num) (by norm_num) hYuv
      (twoOrbit_injective (c := -4) (by norm_num) (by norm_num) (by norm_num) hA hBn))
  obtain ⟨m, hmexit, hmwin⟩ := exists_first_exit
    (twoOrbit_exits (u := 16 / 15) (v := 81 / 80) (Y := Y) (by norm_num) (by norm_num) hYvu
      (twoOrbit_injective (c := 4) (by norm_num) (by norm_num) (by norm_num) hB hA))
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hnexit ⟨le_rfl, hY1⟩
  let T : Finset ℚ := (Finset.range n).image (twoOrbit (81 / 80) (16 / 15) Y) ∪
    (Finset.range m).image (twoOrbit (16 / 15) (81 / 80) Y)
  have hxT {s : ℚ} (h : ∃ i < n, twoOrbit (81 / 80) (16 / 15) Y i = s) : s ∈ T := by
    obtain ⟨i, hi, rfl⟩ := h
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
  have hyT {s : ℚ} (h : ∃ i < m, twoOrbit (16 / 15) (81 / 80) Y i = s) : s ∈ T := by
    obtain ⟨i, hi, rfl⟩ := h
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
  refine ⟨T, hxT ⟨0, Nat.pos_of_ne_zero hn0, rfl⟩, ?_⟩
  intro q hq s ⟨g, hg, he⟩
  have hgcases : g = 10 / 9 ∨ g = 81 / 80 ∨ g = 16 / 15 := by simpa using hg
  obtain ⟨hq1, hs1, hsY, hre⟩ : 1 ≤ q ∧ 1 ≤ s ∧ s < Y ∧ (s = g * q ∨ q = g * s) := by
    rcases he with ⟨h1, _, h3, h4, h5⟩ | ⟨h1, h2, h3, _, h5⟩
    · exact ⟨h1, h3, h4, Or.inl h5⟩
    · exact ⟨h3, h1, h2, Or.inr h5⟩
  have hqY : q < Y := by
    rcases he with ⟨_, h2, _, _, _⟩ | ⟨_, _, _, h4, _⟩
    · exact h2
    · exact h4
  have hrel : (s = 81 / 80 * q ∨ q = 81 / 80 * s) ∨ (s = 16 / 15 * q ∨ q = 16 / 15 * s) := by
    rcases hgcases with h | h | h
    · exfalso
      rw [h] at hre
      rcases hre with h5 | h5 <;> linarith only [h5, hq1, hs1, hsY, hqY, hY]
    · rw [h] at hre
      exact Or.inl hre
    · rw [h] at hre
      exact Or.inr hre
  have hs : InWin Y s := ⟨hs1, hsY⟩
  rcases Finset.mem_union.mp hq with hqx | hqy
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hqx
    rcases orbit_neighbour (by norm_num) (by norm_num) hYuv hnexit hnwin hmexit
      (Finset.mem_range.mp hk) hs hrel with h | h
    · exact hxT h
    · exact hyT h
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hqy
    rcases orbit_neighbour (by norm_num) (by norm_num) hYvu hmexit hmwin hnexit
      (Finset.mem_range.mp hk) hs hrel.symm with h | h
    · exact hyT h
    · exact hxT h

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
  -- Five shears: each `mono` only rewrites the generator list.
  have e4 : 2 * X' / 9 / (10 / 9) = X' / 5 := by ring
  have h4 : HClosed (2 * X' / 9 / (10 / 9)) [10 / 9, 9 / 8 / (10 / 9), 32 / 27 / (10 / 9)] T₅ := by
    rw [e4]
    refine HClosed.mono (fun g hg => ?_) h₅
    norm_num at hg ⊢
    exact hg
  obtain ⟨T₄, h₄1, h₄⟩ := HClosed.shear (W := 2 * X' / 9) (g₀ := 10 / 9) (g₁ := 9 / 8) (g₂ := 32 / 27)
    (by norm_num) (by norm_num) (by norm_num) h4 (by rw [e4]; linarith only [hX'lo]) h₅1
  have e3 : X' / 4 / (9 / 8) = 2 * X' / 9 := by ring
  have h3 : HClosed (X' / 4 / (9 / 8)) [9 / 8, 5 / 4 / (9 / 8), 4 / 3 / (9 / 8)] T₄ := by
    rw [e3]
    refine HClosed.mono (fun g hg => ?_) h₄
    norm_num at hg ⊢
    tauto
  obtain ⟨T₃, h₃1, h₃⟩ := HClosed.shear (W := X' / 4) (g₀ := 9 / 8) (g₁ := 5 / 4) (g₂ := 4 / 3)
    (by norm_num) (by norm_num) (by norm_num) h3 (by rw [e3]; linarith only [hX'lo]) h₄1
  have e2 : X' / 3 / (4 / 3) = X' / 4 := by ring
  have h2 : HClosed (X' / 3 / (4 / 3)) [4 / 3, 3 / 2 / (4 / 3), 5 / 3 / (4 / 3)] T₃ := by
    rw [e2]
    refine HClosed.mono (fun g hg => ?_) h₃
    norm_num at hg ⊢
    tauto
  obtain ⟨T₂, h₂1, h₂⟩ := HClosed.shear (W := X' / 3) (g₀ := 4 / 3) (g₁ := 3 / 2) (g₂ := 5 / 3)
    (by norm_num) (by norm_num) (by norm_num) h2 (by rw [e2]; linarith only [hX'lo]) h₃1
  have e1 : X' / 2 / (3 / 2) = X' / 3 := by ring
  have h1 : HClosed (X' / 2 / (3 / 2)) [3 / 2, 2 / (3 / 2), 5 / 2 / (3 / 2)] T₂ := by
    rw [e1]
    refine HClosed.mono (fun g hg => ?_) h₂
    norm_num at hg ⊢
    tauto
  obtain ⟨T₁, h₁1, h₁⟩ := HClosed.shear (W := X' / 2) (g₀ := 3 / 2) (g₁ := 2) (g₂ := 5 / 2)
    (by norm_num) (by norm_num) (by norm_num) h1 (by rw [e1]; linarith only [hX'lo]) h₂1
  have h0 : HClosed (X' / 2) [2, 3 / 2, 5 / 2] T₁ := by
    refine HClosed.mono (fun g hg => ?_) h₁
    norm_num at hg ⊢
    tauto
  obtain ⟨T₀, h₀1, h₀⟩ := HClosed.shear (W := X') (g₀ := 2) (g₁ := 3) (g₂ := 5)
    (by norm_num) (by norm_num) (by norm_num) h0 (by linarith only [hX'lo]) h₁1
  -- Restriction to the window of `X`.
  refine ⟨T₀.filter fun q => (1 ≤ q ∧ q < X) ∨ q = 1,
    Finset.mem_filter.mpr ⟨h₀1, Or.inr rfl⟩, ?_⟩
  intro q hq s hs1 hsX hrel
  obtain ⟨hqT, hqX⟩ := Finset.mem_filter.mp hq
  have hq1 : 1 ≤ q := by
    rcases hqX with h | h
    · exact h.1
    · rw [h]
  have hqX' : q < X' := by
    rcases hqX with h | h
    · linarith only [h.2, hXX']
    · rw [h]
      linarith only [hX'lo]
  have hsX' : s < X' := by linarith only [hsX, hXX']
  refine Finset.mem_filter.mpr ⟨?_, Or.inl ⟨hs1, hsX⟩⟩
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

/-! ## The exact horizon -/

private theorem rat_lt_of_cast_lt {q : ℚ} (h : (q : ℝ) < 27 / 5) : q < 27 / 5 := by
  have e : ((27 / 5 : ℚ) : ℝ) = 27 / 5 := by norm_num
  rw [← e] at h
  exact Rat.cast_lt.mp h

/-- A closed template inside an aperture below `log(27/5)`. -/
theorem exists_aperture_template {A : ℝ} (hA0 : 0 < A) (hA : A < Real.log (27 / 5)) :
    ∃ T : Finset ℚ, 1 ∈ T ∧ (∀ q ∈ T, 1 ≤ q ∧ (q : ℝ) < Real.exp A) ∧
      ∀ q ∈ T, ∀ s : ℚ, 1 ≤ s → (s : ℝ) < Real.exp A →
        s = 2 * q ∨ q = 2 * s ∨ s = 3 * q ∨ q = 3 * s ∨ s = 5 * q ∨ q = 5 * s → s ∈ T := by
  classical
  have hexp : Real.exp A < 27 / 5 := (Real.lt_log_iff_exp_lt (by norm_num)).mp hA
  obtain ⟨R, hR1, hR2⟩ := exists_rat_btwn hexp
  have hR2' : R < 27 / 5 := rat_lt_of_cast_lt hR2
  obtain ⟨T₀, h1, hT⟩ := exists_finite_hecke_template hR2'
  have hone : ((1 : ℚ) : ℝ) < Real.exp A := by
    rw [Rat.cast_one]
    exact Real.one_lt_exp_iff.mpr hA0
  refine ⟨T₀.filter fun q => 1 ≤ q ∧ (q : ℝ) < Real.exp A,
    Finset.mem_filter.mpr ⟨h1, le_rfl, hone⟩, fun q hq => (Finset.mem_filter.mp hq).2, ?_⟩
  intro q hq s hs1 hsX hrel
  have hsR : s < R := by exact_mod_cast hsX.trans hR1
  exact Finset.mem_filter.mpr ⟨hT q (Finset.mem_filter.mp hq).1 s hs1 hsR hrel, hs1, hsX⟩

/-- **The template decides every rational Hecke form of the aperture.** -/
theorem rationalHeckePositive_iff_template {A : ℝ} (hA0 : 0 < A) (hA : A < Real.log (27 / 5)) :
    ∃ T : Finset ℚ, 1 ∈ T ∧ (∀ q ∈ T, 1 ≤ q ∧ (q : ℝ) < Real.exp A) ∧
      ∀ (N : ℕ) (c : ℕ → ℝ),
        RationalHeckePositive A N c ↔ ∀ y : ℚ → ℝ, 0 ≤ rationalHeckeForm N c T y := by
  classical
  obtain ⟨T, h1, hwin, hcl⟩ := exists_aperture_template hA0 hA
  refine ⟨T, h1, hwin, fun N c => ⟨fun h y => h T ?_ ?_ y, fun hT S hpos hspread y => ?_⟩⟩
  · intro q hq
    have : (1 : ℚ) ≤ q := (hwin q hq).1
    linarith only [this]
  · intro r hr s hs
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (hwin r hr).1
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (hwin s hs).1
    have h3 := Real.log_nonneg hr1
    have h4 : Real.log s < A := (Real.log_lt_iff_lt_exp (by linarith only [hs1])).mpr (hwin s hs).2
    linarith only [h3, h4]
  · by_cases hne : S.Nonempty
    · -- A rational ratio bound below the aperture.
      obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (S ×ˢ S) (fun p => (p.2 : ℝ) / p.1)
        (hne.product hne)
      have hp1 := (Finset.mem_product.mp hp).1
      have hp2 := (Finset.mem_product.mp hp).2
      have hp1pos : (0 : ℝ) < p.1 := by exact_mod_cast hpos _ hp1
      have hp2pos : (0 : ℝ) < p.2 := by exact_mod_cast hpos _ hp2
      have hfp : (p.2 : ℝ) / p.1 < Real.exp A := by
        rw [← Real.log_lt_iff_lt_exp (div_pos hp2pos hp1pos), Real.log_div hp2pos.ne' hp1pos.ne']
        exact hspread _ hp1 _ hp2
      obtain ⟨R, h1R, h2R⟩ := exists_rat_btwn hfp
      have hexp : Real.exp A < 27 / 5 := (Real.lt_log_iff_exp_lt (by norm_num)).mp hA
      refine rationalHeckeForm_nonneg_of_closed_template N c T R h1 ?_ hT S hpos ?_ y
      · intro n hn q hq s hs1 hsR hrel
        have hsX : (s : ℝ) < Real.exp A := by
          have : (s : ℝ) < R := by exact_mod_cast hsR
          exact this.trans h2R
        have hs5 : s < 27 / 5 := rat_lt_of_cast_lt (hsX.trans hexp)
        obtain ⟨hq1, hqX⟩ := hwin q hq
        have hq5 : q < 27 / 5 := rat_lt_of_cast_lt (hqX.trans hexp)
        have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        have hn5 : n ≤ 5 := by
          by_contra hc
          have h6 : (6 : ℚ) ≤ n := by
            have : 6 ≤ n := by omega
            exact_mod_cast this
          rcases hrel with he | he
          · nlinarith only [he, h6, hq1, hs5]
          · nlinarith only [he, h6, hs1, hq5]
        interval_cases n
        · norm_num at hrel
          exact hcl q hq s hs1 hsX (by tauto)
        · norm_num at hrel
          exact hcl q hq s hs1 hsX (by tauto)
        · -- Ratio four is two ratio-two steps.
          norm_num at hrel
          rcases hrel with he | he
          · have hmid : 2 * q ∈ T := by
              refine hcl q hq _ (by linarith only [hq1]) ?_ (Or.inl rfl)
              have hle : ((2 * q : ℚ) : ℝ) ≤ s := by
                have : 2 * q ≤ s := by rw [he]; linarith only [hq1]
                exact_mod_cast this
              exact hle.trans_lt hsX
            exact hcl _ hmid s hs1 hsX (Or.inl (by rw [he]; ring))
          · have hmid : 2 * s ∈ T := by
              refine hcl q hq _ (by linarith only [hs1]) ?_ (Or.inr (Or.inl (by rw [he]; ring)))
              have hle : ((2 * s : ℚ) : ℝ) ≤ q := by
                have : 2 * s ≤ q := by rw [he]; linarith only [hs1]
                exact_mod_cast this
              exact hle.trans_lt hqX
            exact hcl _ hmid s hs1 hsX (Or.inr (Or.inl rfl))
        · norm_num at hrel
          exact hcl q hq s hs1 hsX (by tauto)
      · intro r hr s hs
        have hr0 : (0 : ℝ) < r := by exact_mod_cast hpos r hr
        have h3 := hmax (r, s) (Finset.mem_product.mpr ⟨hr, hs⟩)
        have h4 : (s : ℝ) / r < R := h3.trans_lt h1R
        rw [div_lt_iff₀ hr0] at h4
        exact_mod_cast h4
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [rationalHeckeForm, Finset.sum_empty, mul_zero, Finset.sum_const_zero,
        add_zero, le_refl]

open ArithmeticDegenerationTheory CohomologyOfWindowsOfSpecZ in
/-- **The exact Tate horizon below `27/5`.** One finite set of rationals in the window, independent
of `k`, decides Tate positivity at every dimension. -/
theorem tateFunction_nonneg_iff_template {A : ℝ} (hA0 : 0 < A) (hA : A < Real.log (27 / 5)) :
    ∃ T : Finset ℚ, 1 ∈ T ∧ (∀ q ∈ T, 1 ≤ q ∧ (q : ℝ) < Real.exp A) ∧ ∀ k : ℝ,
      (∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k) ↔
        ∀ y : ℚ → ℝ, 0 ≤ rationalHeckeForm (windowLevel A)
          (fun n => jordanTotient k n / Real.sqrt n) T y := by
  obtain ⟨T, h1, hwin, hT⟩ := rationalHeckePositive_iff_template hA0 hA
  exact ⟨T, h1, hwin, fun k => (tateFunction_nonneg_iff_rationalHeckePositive A k).trans (hT _ _)⟩

end GaloisForLFunctions.WindowTowerOfSpecZ
