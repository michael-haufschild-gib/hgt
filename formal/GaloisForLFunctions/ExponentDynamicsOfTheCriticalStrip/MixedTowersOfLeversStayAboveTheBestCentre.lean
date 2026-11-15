import GaloisForLFunctions.FamilyContinuationTheory.MoebiusSignedGaussPairingsEndAtThreeFifths

/-!
# Mixed towers of levers stay above the best centre

A **lever** for a number `θ` is a map `T` on exponents with `θ ≤ b → θ ≤ T b`: it improves every
upper bound. This module develops the calculus of levers and applies it to the affine levers
`b ↦ (c + b)/k` of continuation frames.

* **A lever is a gap law.** For monotone `T` the lever property is `θ ≤ T θ`, i.e. `θ` avoids the
  set `excluded T = {b | T b < b}` (`isLever_iff_notMem_excluded`). A lever that holds on a family
  of worlds bites at no abscissa the family realizes (`disjoint_excluded_range_of_isLever`).
* **A wall is a fixed point.** Below a seed `s` the levers of a family confine `θ` to the allowed
  set `{b ≤ s | ∀ T, b ≤ T b}`; its supremum is the `wall` (`le_wall`). For monotone levers the wall
  is itself allowed, so it satisfies every lever and nothing further follows (`isLever_wall`).
  Closing the family under composition and pointwise minimum does not move the wall
  (`wall_generated`).
* **Mixed towers.** For frames `(c r, k r)` with `k r ≥ 2` the tower equations
  `V r = (c r + V (r + 1)) / k r` have one bounded solution, the Cantor series
  `towerValue c k r = ∑ⱼ c (r + j) / (k r ⋯ k (r + j))`. It lies between the infimum and the
  supremum of the centres `c r / (k r - 1)` (`IsTowerSolution.le_of_centres_ge`,
  `IsTowerSolution.le_of_centres_le`), it equals a lower bound of the centres only if every centre
  does (`IsTowerSolution.centres_eq_of_eq`), it bounds every tower over the frames
  (`IsTower.le_solution`) and it is a tower itself.
* **The Gauss class.** Every tower that mixes Möbius-signed Gauss pairings has value `≥ 3/5`, with
  equality iff every frame is `(3, 6)` (`three_fifths_le_towerValue_pairings`,
  `towerValue_pairings_eq_three_fifths_iff`); the constant sequence `3/5` is a tower over any
  sequence of pairings (`isTower_const_three_fifths`); and the wall of the finite-field Gauss
  levers below any seed `s ≥ 3/5` is exactly `3/5`, also after closing under composition and
  minimum (`wall_gaussLevers`, `wall_generated_gaussLevers`).
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open GaloisForLFunctions.FamilyContinuationTheory

/-! ### 1. Levers, gap laws and walls -/

/-- `T` is a **lever** for `θ`: every upper bound `b` of `θ` improves to `T b`. -/
def IsLever (θ : ℝ) (T : ℝ → ℝ) : Prop := ∀ b, θ ≤ b → θ ≤ T b

theorem IsLever.le_apply_self {θ : ℝ} {T : ℝ → ℝ} (h : IsLever θ T) : θ ≤ T θ := h θ le_rfl

/-- For a monotone map the lever property is the single inequality `θ ≤ T θ`. -/
theorem isLever_iff_le_apply_self {θ : ℝ} {T : ℝ → ℝ} (hT : Monotone T) :
    IsLever θ T ↔ θ ≤ T θ :=
  ⟨IsLever.le_apply_self, fun h _ hb => h.trans (hT hb)⟩

/-- The **gap** of a lever: the values at which it bites. -/
def excluded (T : ℝ → ℝ) : Set ℝ := {b | T b < b}

/-- **A lever is a gap law**: a monotone `T` is a lever for `θ` iff `θ` avoids its gap. -/
theorem isLever_iff_notMem_excluded {θ : ℝ} {T : ℝ → ℝ} (hT : Monotone T) :
    IsLever θ T ↔ θ ∉ excluded T := by
  rw [isLever_iff_le_apply_self hT, excluded, Set.mem_setOf_eq, not_lt]

/-- **Selectivity.** A lever valid for every world of a family bites at no abscissa the family
realizes. -/
theorem disjoint_excluded_range_of_isLever {ι : Type*} {Θ : ι → ℝ} {T : ℝ → ℝ}
    (h : ∀ i, IsLever (Θ i) T) : Disjoint (excluded T) (Set.range Θ) := by
  rw [Set.disjoint_right]
  rintro _ ⟨i, rfl⟩ hi
  exact absurd (h i).le_apply_self (not_le.mpr hi)

/-- Values below the seed `s` that no lever of the family forbids. -/
def allowed (𝒯 : Set (ℝ → ℝ)) (s : ℝ) : Set ℝ := {b | b ≤ s ∧ ∀ T ∈ 𝒯, b ≤ T b}

/-- The **wall** of a family of levers below a seed. -/
noncomputable def wall (𝒯 : Set (ℝ → ℝ)) (s : ℝ) : ℝ := sSup (allowed 𝒯 s)

theorem bddAbove_allowed (𝒯 : Set (ℝ → ℝ)) (s : ℝ) : BddAbove (allowed 𝒯 s) :=
  ⟨s, fun _ hb => hb.1⟩

/-- A seed and a family of levers bound `θ` by the wall. -/
theorem le_wall {𝒯 : Set (ℝ → ℝ)} {θ s : ℝ} (hs : θ ≤ s) (h : ∀ T ∈ 𝒯, IsLever θ T) :
    θ ≤ wall 𝒯 s :=
  le_csSup (bddAbove_allowed 𝒯 s) ⟨hs, fun T hT => (h T hT).le_apply_self⟩

/-- For monotone levers the wall is allowed (Tarski). -/
theorem wall_mem_allowed {𝒯 : Set (ℝ → ℝ)} {s : ℝ} (hmono : ∀ T ∈ 𝒯, Monotone T)
    (hne : (allowed 𝒯 s).Nonempty) : wall 𝒯 s ∈ allowed 𝒯 s :=
  ⟨csSup_le hne fun _ hb => hb.1, fun T hT => csSup_le hne fun _ hb =>
    (hb.2 T hT).trans (hmono T hT (le_csSup (bddAbove_allowed 𝒯 s) hb))⟩

/-- **Sharpness of the wall.** The wall satisfies every lever of the family: the seed and the
levers are consistent with `θ = wall`. -/
theorem isLever_wall {𝒯 : Set (ℝ → ℝ)} {s : ℝ} (hmono : ∀ T ∈ 𝒯, Monotone T)
    (hne : (allowed 𝒯 s).Nonempty) {T : ℝ → ℝ} (hT : T ∈ 𝒯) : IsLever (wall 𝒯 s) T :=
  (isLever_iff_le_apply_self (hmono T hT)).2 ((wall_mem_allowed hmono hne).2 T hT)

/-- Closure of a family of maps under composition and pointwise minimum. -/
inductive Generated (𝒯 : Set (ℝ → ℝ)) : (ℝ → ℝ) → Prop
  | of {T : ℝ → ℝ} : T ∈ 𝒯 → Generated 𝒯 T
  | comp {S T : ℝ → ℝ} : Generated 𝒯 S → Generated 𝒯 T → Generated 𝒯 (S ∘ T)
  | inf {S T : ℝ → ℝ} : Generated 𝒯 S → Generated 𝒯 T → Generated 𝒯 fun b => min (S b) (T b)

theorem Generated.monotone {𝒯 : Set (ℝ → ℝ)} (hmono : ∀ T ∈ 𝒯, Monotone T) {T : ℝ → ℝ}
    (h : Generated 𝒯 T) : Monotone T := by
  induction h with
  | of hT => exact hmono _ hT
  | comp _ _ ihS ihT => exact ihS.comp ihT
  | inf _ _ ihS ihT => exact fun a b hab => min_le_min (ihS hab) (ihT hab)

/-- **Composites do not lower a wall.** A value allowed by monotone levers is allowed by all
their composites and minima. -/
theorem allowed_generated {𝒯 : Set (ℝ → ℝ)} (hmono : ∀ T ∈ 𝒯, Monotone T) (s : ℝ) :
    allowed {T | Generated 𝒯 T} s = allowed 𝒯 s := by
  ext b
  refine ⟨fun hb => ⟨hb.1, fun T hT => hb.2 T (Generated.of hT)⟩, fun hb => ⟨hb.1, ?_⟩⟩
  intro T hT
  induction hT with
  | of hT => exact hb.2 _ hT
  | comp hS _ ihS ihT => exact ihS.trans (hS.monotone hmono ihT)
  | inf _ _ ihS ihT => exact le_min ihS ihT

theorem wall_generated {𝒯 : Set (ℝ → ℝ)} (hmono : ∀ T ∈ 𝒯, Monotone T) (s : ℝ) :
    wall {T | Generated 𝒯 T} s = wall 𝒯 s := by
  rw [wall, wall, allowed_generated hmono]

/-! ### 2. Towers over affine frames -/

/-- A **tower** over the levers `T r` with floor `σ₀`: `Θ r ≤ max σ₀ (T r (Θ (r + 1)))`. -/
def IsTower (σ₀ : ℝ) (T : ℕ → ℝ → ℝ) (Θ : ℕ → ℝ) : Prop :=
  ∀ r, Θ r ≤ max σ₀ (T r (Θ (r + 1)))

/-- A value that no lever lowers is a constant tower. -/
theorem isTower_const {σ₀ x : ℝ} {T : ℕ → ℝ → ℝ} (h : ∀ r, x ≤ T r x) :
    IsTower σ₀ T fun _ => x :=
  fun r => (h r).trans (le_max_right _ _)

/-- The affine lever `b ↦ (c r + b) / k r` of the `r`-th frame. -/
noncomputable def frameLever (c k : ℕ → ℝ) (r : ℕ) : ℝ → ℝ := pairingStep (c r) (k r)

theorem monotone_pairingStep {c k : ℝ} (hk : 0 ≤ k) : Monotone (pairingStep c k) := by
  intro a b hab
  unfold pairingStep
  exact div_le_div_of_nonneg_right (by linarith) hk

/-- Composition law of frames: `(c₁, k₁) ∘ (c₂, k₂) = (c₁ k₂ + c₂, k₁ k₂)`. -/
theorem pairingStep_comp {c₁ k₁ c₂ k₂ : ℝ} (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) (b : ℝ) :
    pairingStep c₁ k₁ (pairingStep c₂ k₂ b) = pairingStep (c₁ * k₂ + c₂) (k₁ * k₂) b := by
  unfold pairingStep
  field_simp
  ring

/-- **Convexity.** The centre of a composite frame is a convex combination of the two centres,
with weights `k₂ (k₁ - 1) / (k₁ k₂ - 1)` and `(k₂ - 1) / (k₁ k₂ - 1)`. -/
theorem composite_centre_eq_convex {c₁ k₁ c₂ k₂ : ℝ} (hk₁ : 1 < k₁) (hk₂ : 1 < k₂) :
    (c₁ * k₂ + c₂) / (k₁ * k₂ - 1) =
      k₂ * (k₁ - 1) / (k₁ * k₂ - 1) * (c₁ / (k₁ - 1)) +
        (k₂ - 1) / (k₁ * k₂ - 1) * (c₂ / (k₂ - 1)) := by
  have h1 : k₁ - 1 ≠ 0 := by linarith
  have h2 : k₂ - 1 ≠ 0 := by linarith
  have h12 : k₁ * k₂ - 1 ≠ 0 :=
    ne_of_gt (by linarith [mul_pos (sub_pos.2 hk₁) (sub_pos.2 hk₂)])
  field_simp

/-- `V` solves the tower equations of the frames: `V r = (c r + V (r + 1)) / k r`. -/
def IsTowerSolution (c k V : ℕ → ℝ) : Prop := ∀ r, V r = pairingStep (c r) (k r) (V (r + 1))

theorem IsTowerSolution.mul_eq {c k V : ℕ → ℝ} (hV : IsTowerSolution c k V)
    (hk : ∀ r, 2 ≤ k r) (r : ℕ) : k r * V r = c r + V (r + 1) := by
  have hk0 : k r ≠ 0 := by linarith [hk r]
  rw [hV r, pairingStep]
  field_simp

/-- A solution of the tower equations is a tower with equality in every step. -/
theorem IsTowerSolution.isTower {c k V : ℕ → ℝ} (hV : IsTowerSolution c k V) (σ₀ : ℝ) :
    IsTower σ₀ (frameLever c k) V :=
  fun r => (hV r).le.trans (le_max_right _ _)

private theorem tendsto_div_two_pow (M : ℝ) :
    Tendsto (fun n : ℕ => M / 2 ^ n) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- **A mixed tower stays above its lowest centre.** A bounded solution of the tower equations
whose frames all have centre `≥ f` is `≥ f`: the defect `D r = V r - f` satisfies
`k r * D r ≥ D (r + 1)`, so a negative value would double along the tower. -/
theorem IsTowerSolution.le_of_centres_ge {c k V : ℕ → ℝ} {f B : ℝ}
    (hV : IsTowerSolution c k V) (hk : ∀ r, 2 ≤ k r) (hB : ∀ r, |V r| ≤ B)
    (hc : ∀ r, f * (k r - 1) ≤ c r) (r : ℕ) : f ≤ V r := by
  have hM : 0 ≤ B + |f| := by linarith [abs_nonneg (V 0), hB 0, abs_nonneg f]
  have key : ∀ n r, -((B + |f|) / 2 ^ n) ≤ V r - f := by
    intro n
    induction n with
    | zero =>
      intro r
      have h1 := (abs_le.mp (hB r)).1
      simp only [pow_zero, div_one]
      linarith [le_abs_self f]
    | succ n ih =>
      intro r
      have h1 := ih (r + 1)
      have h2 := hV.mul_eq hk r
      have hE : 0 ≤ (B + |f|) / 2 ^ n := by positivity
      have hpow : (B + |f|) / 2 ^ (n + 1) = (B + |f|) / 2 ^ n / 2 := by
        rw [pow_succ, div_mul_eq_div_div]
      rw [hpow]
      by_contra hlt
      rw [not_le] at hlt
      -- `k r * (V r - f) ≥ V (r + 1) - f ≥ -E` while `k r * (V r - f) < -k r * E / 2 ≤ -E`
      have hp1 : 0 ≤ (k r - 2) * ((B + |f|) / 2 ^ n) := mul_nonneg (by linarith [hk r]) hE
      have hp2 : 0 < k r * (-((B + |f|) / 2 ^ n / 2) - (V r - f)) :=
        mul_pos (by linarith [hk r]) (by linarith)
      linarith [hc r]
  have hlim : Tendsto (fun n : ℕ => -((B + |f|) / 2 ^ n)) atTop (𝓝 (-0)) :=
    (tendsto_div_two_pow _).neg
  rw [neg_zero] at hlim
  linarith [le_of_tendsto' hlim fun n => key n r]

/-- **A mixed tower stays below its highest centre.** -/
theorem IsTowerSolution.le_of_centres_le {c k V : ℕ → ℝ} {f B : ℝ}
    (hV : IsTowerSolution c k V) (hk : ∀ r, 2 ≤ k r) (hB : ∀ r, |V r| ≤ B)
    (hc : ∀ r, c r ≤ f * (k r - 1)) (r : ℕ) : V r ≤ f := by
  have hneg : IsTowerSolution (fun r => -c r) k fun r => -V r := by
    intro r
    show -V r = (-c r + -V (r + 1)) / k r
    rw [hV r, pairingStep]
    ring
  have := hneg.le_of_centres_ge (f := -f) (B := B) hk (fun r => by rw [abs_neg]; exact hB r)
    (fun r => by linarith [hc r]) r
  linarith

/-- **Rigidity.** If every centre is `≥ f` and the tower value is `f`, every centre is `f`. -/
theorem IsTowerSolution.centres_eq_of_eq {c k V : ℕ → ℝ} {f B : ℝ}
    (hV : IsTowerSolution c k V) (hk : ∀ r, 2 ≤ k r) (hB : ∀ r, |V r| ≤ B)
    (hc : ∀ r, f * (k r - 1) ≤ c r) (h0 : V 0 = f) (r : ℕ) : c r = f * (k r - 1) := by
  have hge := hV.le_of_centres_ge hk hB hc
  have hall : ∀ r, V r = f := by
    intro r
    induction r with
    | zero => exact h0
    | succ r ih =>
      have h2 := hV.mul_eq hk r
      rw [ih] at h2
      linarith [hge (r + 1), hc r]
  have h2 := hV.mul_eq hk r
  rw [hall r, hall (r + 1)] at h2
  linarith

/-- The bounded solution of the tower equations is unique. -/
theorem IsTowerSolution.eq_of_bounded {c k V W : ℕ → ℝ} {B B' : ℝ}
    (hV : IsTowerSolution c k V) (hW : IsTowerSolution c k W) (hk : ∀ r, 2 ≤ k r)
    (hB : ∀ r, |V r| ≤ B) (hB' : ∀ r, |W r| ≤ B') (r : ℕ) : V r = W r := by
  have hD : IsTowerSolution (fun _ => 0) k fun r => V r - W r := by
    intro r
    show V r - W r = (0 + (V (r + 1) - W (r + 1))) / k r
    rw [hV r, hW r, pairingStep, pairingStep]
    ring
  have hDB : ∀ r, |V r - W r| ≤ B + B' := fun r =>
    (abs_sub _ _).trans (add_le_add (hB r) (hB' r))
  have h1 := hD.le_of_centres_ge (f := 0) hk hDB (fun r => by simp) r
  have h2 := hD.le_of_centres_le (f := 0) hk hDB (fun r => by simp) r
  linarith

/-- **The tower value bounds every tower.** A tower over the frames with seed `S` and floor
`σ₀ ≤ V r` lies below the bounded solution `V`. -/
theorem IsTower.le_solution {σ₀ S B : ℝ} {c k V Θ : ℕ → ℝ}
    (hΘ : IsTower σ₀ (frameLever c k) Θ) (hS : ∀ r, Θ r ≤ S)
    (hV : IsTowerSolution c k V) (hk : ∀ r, 2 ≤ k r) (hB : ∀ r, |V r| ≤ B)
    (hσ : ∀ r, σ₀ ≤ V r) (r : ℕ) : Θ r ≤ V r := by
  have hM : 0 ≤ |S| + B := by linarith [abs_nonneg S, abs_nonneg (V 0), hB 0]
  have key : ∀ n r, Θ r ≤ V r + (|S| + B) / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro r
      have h1 := (abs_le.mp (hB r)).1
      simp only [pow_zero, div_one]
      linarith [hS r, le_abs_self S]
    | succ n ih =>
      intro r
      have hk0 : 0 < k r := by linarith [hk r]
      have hE : 0 ≤ (|S| + B) / 2 ^ n := by positivity
      have hpow : (|S| + B) / 2 ^ (n + 1) = (|S| + B) / 2 ^ n / 2 := by
        rw [pow_succ, div_mul_eq_div_div]
      rw [hpow]
      refine (hΘ r).trans (max_le (by linarith [hσ r]) ?_)
      have h2 := hV.mul_eq hk r
      show (c r + Θ (r + 1)) / k r ≤ _
      rw [div_le_iff₀ hk0]
      linarith [ih (r + 1), mul_nonneg (sub_nonneg.2 (hk r)) hE]
  have hlim : Tendsto (fun n : ℕ => V r + (|S| + B) / 2 ^ n) atTop (𝓝 (V r + 0)) :=
    tendsto_const_nhds.add (tendsto_div_two_pow _)
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim fun n => key n r

/-! ### 3. The tower value as a Cantor series -/

/-- The denominator `k r ⋯ k (r + j)`. -/
noncomputable def towerDen (k : ℕ → ℝ) (r j : ℕ) : ℝ := ∏ i ∈ Finset.range (j + 1), k (r + i)

/-- The **tower value** `∑ⱼ c (r + j) / (k r ⋯ k (r + j))` of the frames from stage `r` on. -/
noncomputable def towerValue (c k : ℕ → ℝ) (r : ℕ) : ℝ := ∑' j, c (r + j) / towerDen k r j

theorem towerDen_zero (k : ℕ → ℝ) (r : ℕ) : towerDen k r 0 = k r := by
  simp [towerDen]

theorem towerDen_succ (k : ℕ → ℝ) (r j : ℕ) :
    towerDen k r (j + 1) = k r * towerDen k (r + 1) j := by
  unfold towerDen
  rw [Finset.prod_range_succ', add_zero, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [Nat.add_right_comm r 1 i, Nat.add_assoc]

theorem two_pow_mul_le_towerDen {k : ℕ → ℝ} (hk : ∀ r, 2 ≤ k r) (j r : ℕ) :
    2 ^ j * k (r + j) ≤ towerDen k r j := by
  induction j generalizing r with
  | zero => simp [towerDen_zero]
  | succ j ih =>
    have h1 := ih (r + 1)
    have h0 : (0 : ℝ) ≤ 2 ^ j * k (r + 1 + j) := by
      have := hk (r + 1 + j)
      positivity
    rw [towerDen_succ, pow_succ, show r + (j + 1) = r + 1 + j by omega]
    linarith [mul_nonneg (sub_nonneg.2 (hk r)) h0,
      mul_le_mul_of_nonneg_left h1 (by linarith [hk r] : (0 : ℝ) ≤ k r)]

/-- Each term of the Cantor series of frames with `0 ≤ c r ≤ k r` is at most `2⁻ʲ`. -/
theorem abs_towerTerm_le {c k : ℕ → ℝ} (hk : ∀ r, 2 ≤ k r) (hc0 : ∀ r, 0 ≤ c r)
    (hc : ∀ r, c r ≤ k r - 1) (r j : ℕ) : |c (r + j) / towerDen k r j| ≤ (1 / 2 : ℝ) ^ j := by
  have hkj : 0 < k (r + j) := by linarith [hk (r + j)]
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hden := two_pow_mul_le_towerDen hk j r
  have hden0 : 0 < towerDen k r j := lt_of_lt_of_le (by positivity) hden
  rw [abs_of_nonneg (div_nonneg (hc0 _) hden0.le), div_le_iff₀ hden0, one_div, inv_pow]
  have h1 : c (r + j) ≤ (2 ^ j)⁻¹ * (2 ^ j * k (r + j)) := by
    rw [← mul_assoc, inv_mul_cancel₀ hpow.ne', one_mul]
    linarith [hc (r + j)]
  exact h1.trans (mul_le_mul_of_nonneg_left hden (by positivity))

theorem summable_towerTerm {c k : ℕ → ℝ} (hk : ∀ r, 2 ≤ k r) (hc0 : ∀ r, 0 ≤ c r)
    (hc : ∀ r, c r ≤ k r - 1) (r : ℕ) : Summable fun j => c (r + j) / towerDen k r j :=
  Summable.of_norm_bounded summable_geometric_two fun j => by
    rw [Real.norm_eq_abs]
    exact abs_towerTerm_le hk hc0 hc r j

theorem abs_towerValue_le {c k : ℕ → ℝ} (hk : ∀ r, 2 ≤ k r) (hc0 : ∀ r, 0 ≤ c r)
    (hc : ∀ r, c r ≤ k r - 1) (r : ℕ) : |towerValue c k r| ≤ 2 := by
  rw [← Real.norm_eq_abs]
  exact tsum_of_norm_bounded hasSum_geometric_two fun j => by
    rw [Real.norm_eq_abs]
    exact abs_towerTerm_le hk hc0 hc r j

/-- The Cantor series solves the tower equations. -/
theorem isTowerSolution_towerValue {c k : ℕ → ℝ} (hk : ∀ r, 2 ≤ k r) (hc0 : ∀ r, 0 ≤ c r)
    (hc : ∀ r, c r ≤ k r - 1) : IsTowerSolution c k (towerValue c k) := by
  intro r
  have hterm : ∀ j, c (r + (j + 1)) / towerDen k r (j + 1) =
      c (r + 1 + j) / towerDen k (r + 1) j / k r := fun j => by
    rw [towerDen_succ, show r + (j + 1) = r + 1 + j by omega, div_mul_eq_div_div_swap]
  unfold towerValue pairingStep
  rw [(summable_towerTerm hk hc0 hc r).tsum_eq_zero_add]
  simp only [hterm, towerDen_zero, add_zero]
  rw [tsum_div_const, add_div]

/-- Centre bounds pass to the tower value. -/
theorem le_towerValue_of_centres_ge {c k : ℕ → ℝ} {f : ℝ} (hk : ∀ r, 2 ≤ k r)
    (hc0 : ∀ r, 0 ≤ c r) (hc : ∀ r, c r ≤ k r - 1) (hf : ∀ r, f * (k r - 1) ≤ c r) (r : ℕ) :
    f ≤ towerValue c k r :=
  (isTowerSolution_towerValue hk hc0 hc).le_of_centres_ge hk (abs_towerValue_le hk hc0 hc) hf r

theorem towerValue_le_of_centres_le {c k : ℕ → ℝ} {f : ℝ} (hk : ∀ r, 2 ≤ k r)
    (hc0 : ∀ r, 0 ≤ c r) (hc : ∀ r, c r ≤ k r - 1) (hf : ∀ r, c r ≤ f * (k r - 1)) (r : ℕ) :
    towerValue c k r ≤ f :=
  (isTowerSolution_towerValue hk hc0 hc).le_of_centres_le hk (abs_towerValue_le hk hc0 hc) hf r

/-- The tower value of frames with centres in `[0, 1]` lies in `[0, 1]`. -/
theorem towerValue_mem_Icc {c k : ℕ → ℝ} (hk : ∀ r, 2 ≤ k r) (hc0 : ∀ r, 0 ≤ c r)
    (hc : ∀ r, c r ≤ k r - 1) (r : ℕ) : towerValue c k r ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_towerValue_of_centres_ge hk hc0 hc (fun r => by simpa using hc0 r) r,
    towerValue_le_of_centres_le hk hc0 hc (fun r => by simpa using hc r) r⟩

/-! ### 4. The Gauss class -/

section GaussClass

variable {G : ℕ → Type*} [∀ r, CommGroup (G r)]

/-- Costs `c r` of a sequence of pairings. -/
noncomputable def pairingCosts (P : ∀ r, MoebiusGaussPairing (G r)) (r : ℕ) : ℝ := (P r).pairingC

/-- Periods `k r` of a sequence of pairings. -/
noncomputable def pairingPeriods (P : ∀ r, MoebiusGaussPairing (G r)) (r : ℕ) : ℝ :=
  ((P r).period : ℝ)

theorem three_le_pairingPeriods (hG : ∀ r, HasUniqueOrderTwo (G r))
    (P : ∀ r, MoebiusGaussPairing (G r)) (r : ℕ) : 3 ≤ pairingPeriods P r := by
  have := (P r).three_le_period (hG r)
  unfold pairingPeriods
  exact_mod_cast this

/-- Every Gauss frame has centre `≥ 3/5`, in the form `3/5 (k - 1) ≤ c`. -/
theorem three_fifths_mul_le_pairingCosts (hG : ∀ r, HasUniqueOrderTwo (G r))
    (P : ∀ r, MoebiusGaussPairing (G r)) (r : ℕ) :
    3 / 5 * (pairingPeriods P r - 1) ≤ pairingCosts P r := by
  have hk := three_le_pairingPeriods hG P r
  have hbar := (P r).three_fifths_le_coupledBarrier (hG r)
  unfold MoebiusGaussPairing.coupledBarrier at hbar
  have hpos : (0 : ℝ) < pairingPeriods P r - 1 := by linarith
  exact (le_div_iff₀ hpos).mp hbar

/-- **No mixed tower of Gauss pairings proves a bound below `3/5`.** Over any sequence of
pairings and any floor, every constant `x ≤ 3/5` is a tower. -/
theorem isTower_const_three_fifths (hG : ∀ r, HasUniqueOrderTwo (G r))
    (P : ∀ r, MoebiusGaussPairing (G r)) (σ₀ : ℝ) {x : ℝ} (hx : x ≤ 3 / 5) :
    IsTower σ₀ (frameLever (pairingCosts P) (pairingPeriods P)) fun _ => x := by
  refine isTower_const fun r => ?_
  have hk := three_le_pairingPeriods hG P r
  have hc := three_fifths_mul_le_pairingCosts hG P r
  show x ≤ (pairingCosts P r + x) / pairingPeriods P r
  rw [le_div_iff₀ (by linarith)]
  linarith [mul_nonneg (sub_nonneg.2 hx) (by linarith : (0 : ℝ) ≤ pairingPeriods P r - 1)]

/-- **Mixed towers of Gauss pairings have value `≥ 3/5`.** -/
theorem three_fifths_le_towerValue_pairings (hG : ∀ r, HasUniqueOrderTwo (G r))
    (P : ∀ r, MoebiusGaussPairing (G r))
    (hc : ∀ r, pairingCosts P r ≤ pairingPeriods P r - 1) (r : ℕ) :
    3 / 5 ≤ towerValue (pairingCosts P) (pairingPeriods P) r := by
  have hk : ∀ r, 2 ≤ pairingPeriods P r := fun r => by
    linarith [three_le_pairingPeriods hG P r]
  have hf := three_fifths_mul_le_pairingCosts hG P
  have hc0 : ∀ r, 0 ≤ pairingCosts P r := fun r => by
    linarith [hf r, three_le_pairingPeriods hG P r]
  exact le_towerValue_of_centres_ge hk hc0 hc hf r

/-- **Rigidity of the mixed wall.** The value of a mixed tower of Gauss pairings is `3/5` iff
every frame is the cubic–sextic frame `(3, 6)`. -/
theorem towerValue_pairings_eq_three_fifths_iff (hG : ∀ r, HasUniqueOrderTwo (G r))
    (P : ∀ r, MoebiusGaussPairing (G r))
    (hc : ∀ r, pairingCosts P r ≤ pairingPeriods P r - 1) :
    towerValue (pairingCosts P) (pairingPeriods P) 0 = 3 / 5 ↔
      ∀ r, (P r).pairingC = 3 ∧ (P r).period = 6 := by
  have hk3 := three_le_pairingPeriods hG P
  have hk : ∀ r, 2 ≤ pairingPeriods P r := fun r => by linarith [hk3 r]
  have hf := three_fifths_mul_le_pairingCosts hG P
  have hc0 : ∀ r, 0 ≤ pairingCosts P r := fun r => by linarith [hf r, hk3 r]
  have hsol := isTowerSolution_towerValue hk hc0 hc
  have hB := abs_towerValue_le hk hc0 hc
  constructor
  · intro h0 r
    have hcr := hsol.centres_eq_of_eq hk hB hf h0 r
    refine ((P r).coupledBarrier_eq_three_fifths_iff (hG r)).mp ?_
    have h3 : (3 : ℝ) ≤ ((P r).period : ℝ) := hk3 r
    unfold MoebiusGaussPairing.coupledBarrier
    rw [div_eq_iff (by linarith)]
    exact hcr
  · intro h
    have hcr : ∀ r, pairingCosts P r = 3 / 5 * (pairingPeriods P r - 1) := fun r => by
      unfold pairingCosts pairingPeriods
      rw [(h r).1, (h r).2]
      norm_num
    exact le_antisymm (hsol.le_of_centres_le hk hB (fun r => (hcr r).le) 0)
      (hsol.le_of_centres_ge hk hB hf 0)

/-- **The mixed tower theorem.** A tower over any sequence of Gauss pairings with centres
`≤ 1`, seed `1` and floor `σ₀ ≤ 3/5` is bounded by its tower value, the tower value is itself
such a tower, and it is `≥ 3/5`. -/
theorem mixed_tower_of_pairings (hG : ∀ r, HasUniqueOrderTwo (G r))
    (P : ∀ r, MoebiusGaussPairing (G r))
    (hc : ∀ r, pairingCosts P r ≤ pairingPeriods P r - 1) {σ₀ : ℝ} (hσ : σ₀ ≤ 3 / 5) :
    (∀ Θ : ℕ → ℝ, IsTower σ₀ (frameLever (pairingCosts P) (pairingPeriods P)) Θ →
        (∀ r, Θ r ≤ 1) → Θ 0 ≤ towerValue (pairingCosts P) (pairingPeriods P) 0) ∧
      IsTower σ₀ (frameLever (pairingCosts P) (pairingPeriods P))
        (towerValue (pairingCosts P) (pairingPeriods P)) ∧
      (∀ r, towerValue (pairingCosts P) (pairingPeriods P) r ≤ 1) ∧
      3 / 5 ≤ towerValue (pairingCosts P) (pairingPeriods P) 0 := by
  have hk3 := three_le_pairingPeriods hG P
  have hk : ∀ r, 2 ≤ pairingPeriods P r := fun r => by linarith [hk3 r]
  have hf := three_fifths_mul_le_pairingCosts hG P
  have hc0 : ∀ r, 0 ≤ pairingCosts P r := fun r => by linarith [hf r, hk3 r]
  have hsol := isTowerSolution_towerValue hk hc0 hc
  have hge := three_fifths_le_towerValue_pairings hG P hc
  exact ⟨fun Θ hΘ hS => hΘ.le_solution hS hsol hk (abs_towerValue_le hk hc0 hc)
      (fun r => hσ.trans (hge r)) 0,
    hsol.isTower σ₀, fun r => (towerValue_mem_Icc hk hc0 hc r).2, hge 0⟩

end GaussClass

/-! ### 5. The wall of the finite-field Gauss levers -/

/-- The affine levers of all Möbius-signed Gauss pairings over finite fields. -/
def gaussLevers : Set (ℝ → ℝ) :=
  {T | ∃ (F : Type) (_ : Field F) (_ : Fintype F) (P : MoebiusGaussPairing (MulChar F ℂ)),
    T = pairingStep P.pairingC P.period}

theorem monotone_of_mem_gaussLevers {T : ℝ → ℝ} (hT : T ∈ gaussLevers) : Monotone T := by
  obtain ⟨F, _, _, P, rfl⟩ := hT
  exact monotone_pairingStep (Nat.cast_nonneg _)

/-- Below a seed `s ≥ 3/5` the Gauss levers allow exactly the values `≤ 3/5`. -/
theorem allowed_gaussLevers {s : ℝ} (hs : 3 / 5 ≤ s) :
    allowed gaussLevers s = Set.Iic (3 / 5) := by
  ext b
  constructor
  · rintro ⟨-, hb⟩
    haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨P₀, hc₀, hk₀, -⟩ := exists_zmod_seven_canonical_pairing
    have h := hb _ ⟨ZMod 7, inferInstance, inferInstance, P₀, rfl⟩
    rw [hc₀, hk₀, pairingStep, le_div_iff₀ (by norm_num)] at h
    push_cast at h
    show b ≤ 3 / 5
    linarith
  · intro hb
    have hb' : b ≤ 3 / 5 := hb
    refine ⟨hb'.trans hs, ?_⟩
    rintro _ ⟨F, hF₁, hF₂, P, rfl⟩
    have hG := @mulChar_hasUniqueOrderTwo F hF₁ hF₂ ℂ _ _
    have hk : (3 : ℝ) ≤ P.period := by exact_mod_cast P.three_le_period hG
    have hbar := P.three_fifths_le_coupledBarrier hG
    unfold MoebiusGaussPairing.coupledBarrier at hbar
    have hc : 3 / 5 * ((P.period : ℝ) - 1) ≤ P.pairingC :=
      (le_div_iff₀ (by linarith)).mp hbar
    rw [pairingStep, le_div_iff₀ (by linarith)]
    linarith [mul_nonneg (sub_nonneg.2 hb') (by linarith : (0 : ℝ) ≤ (P.period : ℝ) - 1)]

/-- **The wall of the Gauss class is `3/5`** below every seed `s ≥ 3/5`. -/
theorem wall_gaussLevers {s : ℝ} (hs : 3 / 5 ≤ s) : wall gaussLevers s = 3 / 5 := by
  rw [wall, allowed_gaussLevers hs, csSup_Iic]

/-- Composites and minima of Gauss levers have the same wall `3/5`. -/
theorem wall_generated_gaussLevers {s : ℝ} (hs : 3 / 5 ≤ s) :
    wall {T | Generated gaussLevers T} s = 3 / 5 := by
  rw [wall_generated fun _ hT => monotone_of_mem_gaussLevers hT, wall_gaussLevers hs]

/-- A number with seed `s ≥ 3/5` for which every composite of Gauss levers is a lever is only
known to be `≤ 3/5`, and `3/5` itself satisfies all of them. -/
theorem gaussLevers_bound_and_sharpness {s : ℝ} (hs : 3 / 5 ≤ s) :
    (∀ θ : ℝ, θ ≤ s → (∀ T, Generated gaussLevers T → IsLever θ T) → θ ≤ 3 / 5) ∧
      ∀ T, Generated gaussLevers T → IsLever (3 / 5) T := by
  have hmono : ∀ T ∈ {T | Generated gaussLevers T}, Monotone T := fun T hT =>
    Generated.monotone (fun _ h => monotone_of_mem_gaussLevers h) hT
  have hne : (allowed {T | Generated gaussLevers T} s).Nonempty := by
    rw [allowed_generated fun _ hT => monotone_of_mem_gaussLevers hT, allowed_gaussLevers hs]
    exact ⟨3 / 5, Set.mem_Iic.mpr le_rfl⟩
  refine ⟨fun θ hθ h => ?_, fun T hT => ?_⟩
  · have : θ ≤ wall {T | Generated gaussLevers T} s := le_wall hθ fun T hT => h T hT
    rwa [wall_generated_gaussLevers hs] at this
  · have := isLever_wall hmono hne (T := T) hT
    rwa [wall_generated_gaussLevers hs] at this

#print axioms mixed_tower_of_pairings
#print axioms towerValue_pairings_eq_three_fifths_iff
#print axioms gaussLevers_bound_and_sharpness

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
