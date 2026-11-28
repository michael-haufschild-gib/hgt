import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.HigherOrderDysonJetAnticoncentration
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.MatchgateRankThreeEscape

/-! # Envelope semi-concavity sign audit and sharp `M = 2` convex/concave collar bounds at `1 / 10`

This module resolves the `k = 2` curvature sign and minimax quantifier structure of
`torusCriticalHeight e V s` at `e = 1 / 10`, pairing the exact universal `M = 2` collar theorems
for arbitrary infima of `c`-strongly concave functions and arbitrary suprema of `c`-strongly convex
functions with the three-part sign and minimax obstruction audit on `torusCriticalHeight`:

1. **Universal `M = 2` global collar bounds with zero index-set multiplicity (`|A|`-free):**
   - `isStronglyConcaveOn_iff_concaveOn_add_sq`, `isStronglyConcaveOn_of_deriv2_le_neg`, and
     `isStronglyConcaveOn_iInf`: `c`-strong concavity (`u ↦ f u + (c / 2) u^2` concave, implied by
     `f'' ≤ -c`) is preserved under pointwise infima over **arbitrary** nonempty index types `α`
     (with zero `|α|` dependence).
   - `stronglyConcaveOn_collar_subset_two_Icc` and `stronglyConcaveOn_parabola_collar_eq`: for
     every `c`-strongly concave `F` (`c > 0`) on convex `S ⊆ ℝ` and every `δ ≥ 0`, the closed collar
     `{u ∈ S | F u ∈ [e₀, e₀ + δ]}` lies in at most `2` closed intervals of combined length
     `≤ 2 * √(2 * δ / c)` (attained with equality on `(e₀, e₀ + δ]` by `e₀ + δ - (c / 2) u^2`).
   - `isStronglyConvexOn_iSup`, `stronglyConvexOn_collar_subset_two_Icc`,
     `gaussian_rotatingDirection_stronglyConcaveInf_anticoncentration`,
     `gaussian_rotatingDirection_stronglyConvexSup_anticoncentration`, and
     `fixed_tenth_locking_of_stronglyConvexSup_charts`: sign duality gives the exact dual `M = 2`
     theorem (`≤ 2 * √(2 * δ / c)`) for arbitrary suprema of `c`-strongly convex functions and locks
     `m_{1/10 + δ} = m_{1/10}` across `J` rotating-direction charts with probability bound
     `Q * J * (2 / √π) * √(δ / c)` and zero circuit-cardinality factor.
2. **Three-part sign and minimax obstruction audit on `torusCriticalHeight` at `e = 1 / 10`:**
   - **Minimax duality gap (`swapped_torusCriticalHeight_fixedTarget_ge_one` &
     `swapped_torusCriticalHeight_modPhase_ge_half`):** for every `N ≥ 1`, `d ≥ 1`, `V ∈ U(2^N)`,
     and every gate budget `s`, swapping `sup_θ inf_C` to `inf_W sup_θ` yields `≥ 1` (and `≥ 1 / 2`
     even modulo `θ`-dependent global phases `z(θ)`, including at `s = 2^(6 N)` where
     `torusCriticalHeight = 0`).
   - **Frozen-target `C*`-algebra semiconvexity, strictly positive curvature at `1 / 10`, and upward
     V-kinks (`convexOn_conjFlow_opNorm_add_four_sq`,
     `exists_frozenCircuit_tenth_pos_secondDeriv`, `exists_frozenCircuit_tenth_upward_vKink`):**
     every frozen-target conjugation norm `u ↦ ‖exp(-i u K) U₀ exp(i u K) - W_★‖` is globally
     `8 ‖K‖^2 ‖U₀‖`-semiconvex (`+ 4 ‖K‖^2 ‖U₀‖ u^2` is convex); at exact height `f(0) = 1 / 10`
     with `W_★ ∈ phaseCircuitMatrixImageAtMost N 1`, nearest-phase saddles satisfy `f'(0) = 0` and
     `f''(0) = 40 sin α sin β > 0` (strictly convex upward), while degenerate `2`-qubit saddles
     satisfy `f(u) = 2 sin(v₀ + |u|)` near `0`, violating concavity of `u ↦ f u - C u^2` on `[-r, r]`
     for **every** `C ∈ ℝ` and `r > 0`.
   - **Outer-`sup_θ` proliferation of `c`-strongly concave slices
     (`sup_stronglyConcave_collar_measure_ge`):** the supremum of `P ≥ 1` `c`-strongly concave
     parabolas accumulates collar measure `≥ 2 * (2 - √2) * P * √(δ / c)`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate BigOperators
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
open WeakBonds PrescribedTimes SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw GaloisForLFunctions.RHTower
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ

/-! ## Section 1: Universal `M = 2` global collar bounds for `c`-strongly concave infima and `c`-strongly convex suprema -/

section AbstractStrongCurvatureEnvelopes

/-- `c`-strong concavity of `f : ℝ → ℝ` on `S ⊆ ℝ`: `S` is convex and every convex combination
`a x + b y` (`a, b ≥ 0`, `a + b = 1`) gains at least `(c / 2) * a * b * (x - y)^2`. -/
def IsStronglyConcaveOn (c : ℝ) (S : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ S ∧ ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ∀ ⦃a b : ℝ⦄,
    0 ≤ a → 0 ≤ b → a + b = 1 →
    a * f x + b * f y + (c / 2) * a * b * (x - y) ^ 2 ≤ f (a * x + b * y)

/-- `c`-strong convexity of `g : ℝ → ℝ` on `S ⊆ ℝ`, defined by sign duality `-g`. -/
def IsStronglyConvexOn (c : ℝ) (S : Set ℝ) (g : ℝ → ℝ) : Prop :=
  IsStronglyConcaveOn c S (fun u => -g u)

private theorem quad_variance_identity {a b : ℝ} (hab : a + b = 1) (x y : ℝ) :
    a * x ^ 2 + b * y ^ 2 - (a * x + b * y) ^ 2 = a * b * (x - y) ^ 2 := by
  have hb : b = 1 - a := by linarith only [hab]
  rw [hb]; ring

/-- Exact equivalence between `IsStronglyConcaveOn c S f` and concavity of `u ↦ f u + (c / 2) * u^2`. -/
theorem isStronglyConcaveOn_iff_concaveOn_add_sq (c : ℝ) (S : Set ℝ) (f : ℝ → ℝ) :
    IsStronglyConcaveOn c S f ↔ ConcaveOn ℝ S (fun u => f u + (c / 2) * u ^ 2) := by
  constructor
  · rintro ⟨hconv, hstr⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have h1 := hstr hx hy ha hb hab
    have hq := quad_variance_identity hab x y
    linarith [show a * (f x + c / 2 * x ^ 2) + b * (f y + c / 2 * y ^ 2) -
        c / 2 * (a * x + b * y) ^ 2 =
      a * f x + b * f y + c / 2 * (a * x ^ 2 + b * y ^ 2 - (a * x + b * y) ^ 2) by ring,
      show c / 2 * (a * x ^ 2 + b * y ^ 2 - (a * x + b * y) ^ 2) =
        c / 2 * a * b * (x - y) ^ 2 by rw [hq]; ring]
  · rintro ⟨hconv, hconc⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    have h1 := hconc hx hy ha hb hab
    simp only [smul_eq_mul] at h1
    have hq := quad_variance_identity hab x y
    linarith [show a * (f x + c / 2 * x ^ 2) + b * (f y + c / 2 * y ^ 2) -
        c / 2 * (a * x + b * y) ^ 2 =
      a * f x + b * f y + c / 2 * a * b * (x - y) ^ 2 by linear_combination (c / 2) * hq]

/-- Exact equivalence between `IsStronglyConvexOn c S g` and convexity of `u ↦ g u - (c / 2) * u^2`. -/
theorem isStronglyConvexOn_iff_convexOn_sub_sq (c : ℝ) (S : Set ℝ) (g : ℝ → ℝ) :
    IsStronglyConvexOn c S g ↔ ConvexOn ℝ S (fun u => g u - (c / 2) * u ^ 2) := by
  rw [IsStronglyConvexOn, isStronglyConcaveOn_iff_concaveOn_add_sq]
  constructor
  · rintro ⟨hconv, hconc⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    have h1 := hconc hx hy ha hb hab
    simp only [smul_eq_mul] at h1 ⊢
    linarith only [h1]
  · rintro ⟨hconv, hcx⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    have h1 := hcx hx hy ha hb hab
    simp only [smul_eq_mul] at h1 ⊢
    linarith only [h1]

/-- Second-derivative criterion for `c`-strong concavity: if `f''(u) ≤ -c` across a convex set
`S ⊆ ℝ`, then `IsStronglyConcaveOn c S f`. -/
theorem isStronglyConcaveOn_of_deriv2_le_neg {c : ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ u ∈ S, HasDerivAt f (f' u) u)
    (hf' : ∀ u ∈ S, HasDerivAt f' (f'' u) u)
    (hle : ∀ u ∈ S, f'' u ≤ -c) :
    IsStronglyConcaveOn c S f := by
  rw [isStronglyConcaveOn_iff_concaveOn_add_sq]
  let h : ℝ → ℝ := fun u => f u + (c / 2) * u ^ 2
  let h' : ℝ → ℝ := fun u => f' u + c * u
  let h'' : ℝ → ℝ := fun u => f'' u + c
  have hh_deriv (u : ℝ) (hu : u ∈ S) : HasDerivAt h (h' u) u := by
    have hq : HasDerivAt (fun t : ℝ => (c / 2) * t ^ 2) (c * u) u := by
      simpa [show (c / 2) * (2 * u) = c * u by ring] using
        ((hasDerivAt_pow 2 u).const_mul (c / 2))
    exact (hf u hu).add hq
  have hh'_deriv (u : ℝ) (hu : u ∈ S) : HasDerivAt h' (h'' u) u := by
    have hl : HasDerivAt (fun t : ℝ => c * t) c u :=
      ((hasDerivAt_id' u).const_mul c).congr_deriv (mul_one c)
    exact (hf' u hu).add hl
  have hh'_anti : ∀ ⦃u v⦄, u ∈ S → v ∈ S → u ≤ v → h' v ≤ h' u := by
    intro u v hu hv huv
    rcases eq_or_lt_of_le huv with rfl | hlt
    · exact le_rfl
    · have hIcc : Icc u v ⊆ S := hS.ordConnected.out hu hv
      obtain ⟨η, hη_mem, hη_eq⟩ := exists_hasDerivAt_eq_slope h' h'' hlt
        (fun t ht => (hh'_deriv t (hIcc ht)).continuousAt.continuousWithinAt)
        (fun t ht => hh'_deriv t (hIcc (Ioo_subset_Icc_self ht)))
      have hη_nonpos : h'' η ≤ 0 := by
        dsimp only [h'']; linarith only [hle η (hIcc (Ioo_subset_Icc_self hη_mem))]
      rw [hη_eq, div_le_iff₀ (sub_pos.mpr hlt), zero_mul] at hη_nonpos
      linarith only [hη_nonpos]
  have hconc_ord : ∀ x ∈ S, ∀ y ∈ S, x < y → ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      a * h x + b * h y ≤ h (a * x + b * y) := by
    intro x hx y hy hxy a b ha hb hab
    let m : ℝ := a * x + b * y
    have hm_S : m ∈ S := hS hx hy ha.le hb.le hab
    have hmx : m - x = b * (y - x) := by
      dsimp only [m]; have ha' : a = 1 - b := by linarith only [hab]
      rw [ha']; ring
    have hym : y - m = a * (y - x) := by
      dsimp only [m]; have hb' : b = 1 - a := by linarith only [hab]
      rw [hb']; ring
    have hxm_lt : x < m := by
      have hpos : 0 < m - x := by rw [hmx]; exact mul_pos hb (sub_pos.mpr hxy)
      linarith only [hpos]
    have hmy_lt : m < y := by
      have hpos : 0 < y - m := by rw [hym]; exact mul_pos ha (sub_pos.mpr hxy)
      linarith only [hpos]
    have hIcc1 : Icc x m ⊆ S := hS.ordConnected.out hx hm_S
    have hIcc2 : Icc m y ⊆ S := hS.ordConnected.out hm_S hy
    obtain ⟨ξ₁, hξ₁_mem, hξ₁_eq⟩ := exists_hasDerivAt_eq_slope h h' hxm_lt
      (fun t ht => (hh_deriv t (hIcc1 ht)).continuousAt.continuousWithinAt)
      (fun t ht => hh_deriv t (hIcc1 (Ioo_subset_Icc_self ht)))
    obtain ⟨ξ₂, hξ₂_mem, hξ₂_eq⟩ := exists_hasDerivAt_eq_slope h h' hmy_lt
      (fun t ht => (hh_deriv t (hIcc2 ht)).continuousAt.continuousWithinAt)
      (fun t ht => hh_deriv t (hIcc2 (Ioo_subset_Icc_self ht)))
    have hslope_le : (h y - h m) / (y - m) ≤ (h m - h x) / (m - x) := by
      rw [← hξ₂_eq, ← hξ₁_eq]
      exact hh'_anti (hIcc1 (Ioo_subset_Icc_self hξ₁_mem))
        (hIcc2 (Ioo_subset_Icc_self hξ₂_mem)) (hξ₁_mem.2.le.trans hξ₂_mem.1.le)
    rw [hym, hmx] at hslope_le
    have hyx_pos : 0 < y - x := sub_pos.mpr hxy
    have hmul := mul_le_mul_of_nonneg_left hslope_le (mul_pos ha (mul_pos hb hyx_pos)).le
    have hlhs : a * (b * (y - x)) * ((h y - h m) / (a * (y - x))) = b * (h y - h m) := by
      field_simp [ha.ne', hyx_pos.ne']
    have hrhs : a * (b * (y - x)) * ((h m - h x) / (b * (y - x))) = a * (h m - h x) := by
      field_simp [hb.ne', hyx_pos.ne']
    rw [hlhs, hrhs] at hmul
    have hsum1 : (a + b) * h m = h m := by rw [hab, one_mul]
    linarith only [hmul, hsum1]
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have hb1 : b = 1 := by linarith only [hab]
    subst hb1; simp
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · have ha1 : a = 1 := by linarith only [hab]
      subst ha1; simp
    · rcases lt_trichotomy x y with hxy | rfl | hyx
      · exact hconc_ord x hx y hy hxy a b ha_pos hb_pos hab
      · have h1 : a * x + b * x = x := by linear_combination x * hab
        have h2 : a * h x + b * h x = h x := by linear_combination h x * hab
        rw [h1, h2]
      · have hord := hconc_ord y hy x hx hyx b a hb_pos ha_pos (by linarith only [hab])
        have hcomm_xy : a * x + b * y = b * y + a * x := add_comm _ _
        change a * h x + b * h y ≤ h (a * x + b * y)
        rw [hcomm_xy]
        linarith only [hord]

/-- Pointwise infimum over an **arbitrary** nonempty index type `α` preserves `c`-strong concavity
with zero `|α|` loss. -/
theorem isStronglyConcaveOn_iInf {α : Type*} [Nonempty α] {c : ℝ} {S : Set ℝ}
    {f : α → ℝ → ℝ} (hf : ∀ i : α, IsStronglyConcaveOn c S (f i))
    (hbdd : ∀ u ∈ S, BddBelow (Set.range fun i : α => f i u)) :
    IsStronglyConcaveOn c S (fun u => ⨅ i : α, f i u) := by
  obtain ⟨i₀⟩ := ‹Nonempty α›
  refine ⟨(hf i₀).1, fun x hx y hy a b ha hb hab => ?_⟩
  refine le_ciInf fun i => ?_
  have h1 := (hf i).2 hx hy ha hb hab
  have hfx : (⨅ j : α, f j x) ≤ f i x := ciInf_le (hbdd x hx) i
  have hfy : (⨅ j : α, f j y) ≤ f i y := ciInf_le (hbdd y hy) i
  have hax : a * (⨅ j : α, f j x) ≤ a * f i x := mul_le_mul_of_nonneg_left hfx ha
  have hby : b * (⨅ j : α, f j y) ≤ b * f i y := mul_le_mul_of_nonneg_left hfy hb
  linarith only [h1, hax, hby]

/-- Dual theorem: pointwise supremum over an **arbitrary** nonempty index type `α` preserves
`c`-strong convexity with zero `|α|` loss. -/
theorem isStronglyConvexOn_iSup {α : Type*} [Nonempty α] {c : ℝ} {S : Set ℝ}
    {g : α → ℝ → ℝ} (hg : ∀ i : α, IsStronglyConvexOn c S (g i))
    (hbdd : ∀ u ∈ S, BddAbove (Set.range fun i : α => g i u)) :
    IsStronglyConvexOn c S (fun u => ⨆ i : α, g i u) := by
  obtain ⟨i₀⟩ := ‹Nonempty α›
  refine ⟨(hg i₀).1, fun x hx y hy a b ha hb hab => ?_⟩
  change a * (-(⨆ i : α, g i x)) + b * (-(⨆ i : α, g i y)) + (c / 2) * a * b * (x - y) ^ 2 ≤
    -(⨆ i : α, g i (a * x + b * y))
  rw [le_neg]
  refine ciSup_le fun i => ?_
  have h1 := (hg i).2 hx hy ha hb hab
  have hgx : g i x ≤ ⨆ j : α, g j x := le_ciSup (hbdd x hx) i
  have hgy : g i y ≤ ⨆ j : α, g j y := le_ciSup (hbdd y hy) i
  have hax : a * g i x ≤ a * (⨆ j : α, g j x) := mul_le_mul_of_nonneg_left hgx ha
  have hby : b * g i y ≤ b * (⨆ j : α, g j y) := mul_le_mul_of_nonneg_left hgy hb
  linarith only [h1, hax, hby]

private theorem set_subset_Icc_of_abs_sub_le {A : Set ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ D) :
    ∃ a b : ℝ, a ≤ b ∧ b - a ≤ D ∧ A ⊆ Icc a b := by
  by_cases hne : A.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    have hA_ne : A.Nonempty := ⟨x₀, hx₀⟩
    have hbdd_below : BddBelow A := ⟨x₀ - D, fun x hx => by
      linarith only [(abs_le.mp (hdiam x hx x₀ hx₀)).1]⟩
    have hbdd_above : BddAbove A := ⟨x₀ + D, fun x hx => by
      linarith only [(abs_le.mp (hdiam x hx x₀ hx₀)).2]⟩
    let a := sInf A
    let b := sSup A
    have hab : a ≤ b := (csInf_le hbdd_below hx₀).trans (le_csSup hbdd_above hx₀)
    have hba_le : b - a ≤ D := by
      -- For every x ∈ A and y ∈ A, x - y ≤ D, hence sSup A ≤ D + sInf A.
      have hsup_le : b ≤ D + a := by
        refine csSup_le hA_ne fun x hx => ?_
        have ha_le : x - D ≤ a := le_csInf hA_ne fun y hy => by
          linarith only [(abs_le.mp (hdiam x hx y hy)).2]
        linarith only [ha_le]
      linarith only [hsup_le]
    exact ⟨a, b, hab, hba_le, fun x hx => ⟨csInf_le hbdd_below hx, le_csSup hbdd_above hx⟩⟩
  · exact ⟨0, 0, le_rfl, by simpa using hD, fun x hx => (hne ⟨x, hx⟩).elim⟩

/-- Universal `M = 2` closed-interval collar bound for `c`-strongly concave functions (`c > 0`,
`δ ≥ 0`) with sharp total width `2 * √(2 * δ / c)`:
`{u ∈ S | F u ∈ [e₀, e₀ + δ]}` is covered by two closed intervals `[a₁, b₁] ∪ [a₂, b₂]` satisfying
`(b₁ - a₁) + (b₂ - a₂) ≤ 2 * √(2 * δ / c)`. -/
theorem stronglyConcaveOn_collar_subset_two_Icc {c : ℝ} (hc : 0 < c) {S : Set ℝ} {F : ℝ → ℝ}
    (hF : IsStronglyConcaveOn c S F) (e₀ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ a₁ b₁ a₂ b₂ : ℝ, a₁ ≤ b₁ ∧ a₂ ≤ b₂ ∧
      (b₁ - a₁) + (b₂ - a₂) ≤ 2 * Real.sqrt (2 * δ / c) ∧
      {u ∈ S | F u ∈ Icc e₀ (e₀ + δ)} ⊆ Icc a₁ b₁ ∪ Icc a₂ b₂ := by
  let A := {u ∈ S | F u ∈ Icc e₀ (e₀ + δ)}
  let w := Real.sqrt (2 * δ / c)
  have hw_nn : 0 ≤ w := Real.sqrt_nonneg _
  have hw_sq : w ^ 2 = 2 * δ / c := Real.sq_sqrt (div_nonneg (by linarith only [hδ]) hc.le)
  by_cases hpeak : ∃ p ∈ S, e₀ + δ < F p
  · -- Case 2: a strict peak p ∈ S above e₀ + δ splits A into A_- (u < p) and A_+ (p < u),
    -- each of diameter ≤ √(2 δ / c).
    obtain ⟨p, hpS, hpF⟩ := hpeak
    let A_left := {u ∈ A | u < p}
    let A_right := {u ∈ A | p < u}
    have hflank_diam (x y : ℝ) (hx : x ∈ A) (hy : y ∈ A) (hpx : p < x) (hxy : x < y) :
        y - x ≤ w := by
      have hyp_pos : 0 < y - p := by linarith only [hpx, hxy]
      let lam : ℝ := (x - p) / (y - p)
      have hlam_pos : 0 < lam := div_pos (sub_pos.mpr hpx) hyp_pos
      have h1mlam_pos : 0 < 1 - lam := by
        have heq : 1 - lam = (y - x) / (y - p) := by dsimp only [lam]; field_simp [hyp_pos.ne']; ring
        rw [heq]; exact div_pos (sub_pos.mpr hxy) hyp_pos
      have hconv_x : (1 - lam) * p + lam * y = x := by
        dsimp only [lam]; field_simp [hyp_pos.ne']; ring
      have hstr := hF.2 hpS hy.1 h1mlam_pos.le hlam_pos.le (by ring)
      rw [hconv_x] at hstr
      have hFx_hi : F x ≤ e₀ + δ := hx.2.2
      have hFy_lo : e₀ ≤ F y := hy.2.1
      have hrhs_gt : e₀ + (1 - lam) * δ + (c / 2) * (1 - lam) * lam * (p - y) ^ 2 <
          (1 - lam) * F p + lam * F y + (c / 2) * (1 - lam) * lam * (p - y) ^ 2 := by
        have h1 : (1 - lam) * (e₀ + δ) < (1 - lam) * F p := mul_lt_mul_of_pos_left hpF h1mlam_pos
        have h2 : lam * e₀ ≤ lam * F y := mul_le_mul_of_nonneg_left hFy_lo hlam_pos.le
        linarith only [h1, h2]
      have hlam_ineq : (c / 2) * (1 - lam) * lam * (y - p) ^ 2 < lam * δ := by
        have hpy : (p - y) ^ 2 = (y - p) ^ 2 := by ring
        rw [← hpy]; linarith only [hstr, hFx_hi, hrhs_gt]
      have hdiv_lam : (c / 2) * (1 - lam) * (y - p) ^ 2 < δ := by
        have h1 : lam * ((c / 2) * (1 - lam) * (y - p) ^ 2) < lam * δ := by linarith only [hlam_ineq]
        exact lt_of_mul_lt_mul_left h1 hlam_pos.le
      have hprod_eq : (1 - lam) * (y - p) ^ 2 = (y - x) * (y - p) := by
        dsimp only [lam]; field_simp [hyp_pos.ne']; ring
      rw [mul_assoc, hprod_eq] at hdiv_lam
      have hsq_le : (y - x) ^ 2 ≤ (y - x) * (y - p) := by
        nlinarith only [hpx, hxy]
      have hc_sq : (c / 2) * (y - x) ^ 2 ≤ δ := by
        have h1 : (c / 2) * (y - x) ^ 2 ≤ (c / 2) * ((y - x) * (y - p)) :=
          mul_le_mul_of_nonneg_left hsq_le (by positivity)
        linarith only [h1, hdiv_lam]
      have hyx_sq : (y - x) ^ 2 ≤ w ^ 2 := by
        rw [hw_sq, le_div_iff₀ hc]
        linarith only [hc_sq]
      nlinarith only [hyx_sq, sub_pos.mpr hxy, hw_nn, sq_nonneg ((y - x) - w)]
    have hright_diam : ∀ x ∈ A_right, ∀ y ∈ A_right, |x - y| ≤ w := by
      rintro x ⟨hxA, hpx⟩ y ⟨hyA, hpy⟩
      rcases lt_trichotomy x y with hxy | rfl | hyx
      · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hxy)]; exact hflank_diam x y hxA hyA hpx hxy
      · simp [hw_nn]
      · rw [abs_of_pos (sub_pos.mpr hyx)]; exact hflank_diam y x hyA hxA hpy hyx
    -- Symmetric left flank via u ↦ -u.
    have hflank_left (x y : ℝ) (hx : x ∈ A) (hy : y ∈ A) (hyp : y < p) (hxy : x < y) :
        y - x ≤ w := by
      have hpx_pos : 0 < p - x := by linarith only [hyp, hxy]
      let lam : ℝ := (p - y) / (p - x)
      have hlam_pos : 0 < lam := div_pos (sub_pos.mpr hyp) hpx_pos
      have h1mlam_pos : 0 < 1 - lam := by
        have heq : 1 - lam = (y - x) / (p - x) := by dsimp only [lam]; field_simp [hpx_pos.ne']; ring
        rw [heq]; exact div_pos (sub_pos.mpr hxy) hpx_pos
      have hconv_y : (1 - lam) * p + lam * x = y := by
        dsimp only [lam]; field_simp [hpx_pos.ne']; ring
      have hstr := hF.2 hpS hx.1 h1mlam_pos.le hlam_pos.le (by ring)
      rw [hconv_y] at hstr
      have hFy_hi : F y ≤ e₀ + δ := hy.2.2
      have hFx_lo : e₀ ≤ F x := hx.2.1
      have hrhs_gt : e₀ + (1 - lam) * δ + (c / 2) * (1 - lam) * lam * (p - x) ^ 2 <
          (1 - lam) * F p + lam * F x + (c / 2) * (1 - lam) * lam * (p - x) ^ 2 := by
        have h1 : (1 - lam) * (e₀ + δ) < (1 - lam) * F p := mul_lt_mul_of_pos_left hpF h1mlam_pos
        have h2 : lam * e₀ ≤ lam * F x := mul_le_mul_of_nonneg_left hFx_lo hlam_pos.le
        linarith only [h1, h2]
      have hlam_ineq : lam * ((c / 2) * (1 - lam) * (p - x) ^ 2) < lam * δ := by
        linarith only [hstr, hFy_hi, hrhs_gt]
      have hdiv_lam : (c / 2) * ((1 - lam) * (p - x) ^ 2) < δ := by
        have h1 := lt_of_mul_lt_mul_left hlam_ineq hlam_pos.le
        linarith only [h1]
      have hprod_eq : (1 - lam) * (p - x) ^ 2 = (y - x) * (p - x) := by
        dsimp only [lam]; field_simp [hpx_pos.ne']; ring
      rw [hprod_eq] at hdiv_lam
      have hsq_le : (y - x) ^ 2 ≤ (y - x) * (p - x) := by nlinarith only [hyp, hxy]
      have hc_sq : (c / 2) * (y - x) ^ 2 ≤ δ := by
        have h1 := mul_le_mul_of_nonneg_left hsq_le (show (0 : ℝ) ≤ c / 2 by positivity)
        linarith only [h1, hdiv_lam]
      have hyx_sq : (y - x) ^ 2 ≤ w ^ 2 := by rw [hw_sq, le_div_iff₀ hc]; linarith only [hc_sq]
      nlinarith only [hyx_sq, sub_pos.mpr hxy, hw_nn, sq_nonneg ((y - x) - w)]
    have hleft_diam : ∀ x ∈ A_left, ∀ y ∈ A_left, |x - y| ≤ w := by
      rintro x ⟨hxA, hxp⟩ y ⟨hyA, hyp⟩
      rcases lt_trichotomy x y with hxy | rfl | hyx
      · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hxy)]; exact hflank_left x y hxA hyA hyp hxy
      · simp [hw_nn]
      · rw [abs_of_pos (sub_pos.mpr hyx)]; exact hflank_left y x hyA hxA hxp hyx
    obtain ⟨a₁, b₁, hab₁, hlen₁, hsub₁⟩ := set_subset_Icc_of_abs_sub_le hw_nn hleft_diam
    obtain ⟨a₂, b₂, hab₂, hlen₂, hsub₂⟩ := set_subset_Icc_of_abs_sub_le hw_nn hright_diam
    refine ⟨a₁, b₁, a₂, b₂, hab₁, hab₂, by linarith only [hlen₁, hlen₂], fun u hu => ?_⟩
    rcases lt_trichotomy u p with hup | rfl | hpu
    · exact Or.inl (hsub₁ ⟨hu, hup⟩)
    · exfalso; linarith only [hu.2.2, hpF]
    · exact Or.inr (hsub₂ ⟨hu, hpu⟩)
  · -- Case 1: F ≤ e₀ + δ everywhere on S, so A itself has diameter ≤ 2 * √(2 δ / c).
    push Not at hpeak
    have hdiam_all : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ 2 * w := by
      intro x hx y hy
      have hmid_S : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y ∈ S :=
        hF.1 hx.1 hy.1 (by norm_num) (by norm_num) (by norm_num)
      have hstr := hF.2 hx.1 hy.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      have hmid_hi : F ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) ≤ e₀ + δ := hpeak _ hmid_S
      have hx_lo : e₀ ≤ F x := hx.2.1
      have hy_lo : e₀ ≤ F y := hy.2.1
      have hc8 : (c / 8) * (x - y) ^ 2 ≤ δ := by linarith only [hstr, hmid_hi, hx_lo, hy_lo]
      have hsq_le : |x - y| ^ 2 ≤ (2 * w) ^ 2 := by
        rw [sq_abs, mul_pow, hw_sq, show (2 : ℝ) ^ 2 * (2 * δ / c) = 8 * δ / c by ring,
          le_div_iff₀ hc]
        linarith only [hc8]
      nlinarith only [hsq_le, abs_nonneg (x - y), hw_nn, sq_nonneg (|x - y| - 2 * w)]
    obtain ⟨a₁, b₁, hab₁, hlen₁, hsub₁⟩ :=
      set_subset_Icc_of_abs_sub_le (mul_nonneg two_pos.le hw_nn) hdiam_all
    exact ⟨a₁, b₁, 0, 0, hab₁, le_rfl, by linarith only [hlen₁], fun u hu => Or.inl (hsub₁ hu)⟩

/-- Exact sharpness of the `2 * √(2 * δ / c)` collar constant: for `F(u) = e₀ + δ - (c / 2) * u^2`
(`c > 0`, `δ > 0`), `IsStronglyConcaveOn c univ F` and
`(volume {u : ℝ | F u ∈ Ioc e₀ (e₀ + δ)}).toReal = 2 * √(2 * δ / c)`. -/
theorem stronglyConcaveOn_parabola_collar_eq {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (e₀ : ℝ) :
    let F : ℝ → ℝ := fun u => e₀ + δ - (c / 2) * u ^ 2
    IsStronglyConcaveOn c univ F ∧
      (volume {u : ℝ | F u ∈ Ioc e₀ (e₀ + δ)}).toReal = 2 * Real.sqrt (2 * δ / c) := by
  intro F
  have hstr : IsStronglyConcaveOn c univ F := by
    rw [isStronglyConcaveOn_iff_concaveOn_add_sq]
    have hconst : (fun u : ℝ => F u + (c / 2) * u ^ 2) = fun _ => e₀ + δ := by
      funext u; dsimp only [F]; ring
    rw [hconst]
    exact concaveOn_const (e₀ + δ) convex_univ
  refine ⟨hstr, ?_⟩
  let w := Real.sqrt (2 * δ / c)
  have hw_pos : 0 < w := Real.sqrt_pos.mpr (div_pos (by linarith only [hδ]) hc)
  have hw_sq : w ^ 2 = 2 * δ / c := Real.sq_sqrt (div_pos (by linarith only [hδ]) hc).le
  have hset_eq : {u : ℝ | F u ∈ Ioc e₀ (e₀ + δ)} = Ioo (-w) w := by
    ext u
    simp only [F, mem_setOf_eq, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨hlo, _⟩
      have hcu : (c / 2) * u ^ 2 < δ := by linarith only [hlo]
      have husq : u ^ 2 < w ^ 2 := by rw [hw_sq, lt_div_iff₀ hc]; linarith only [hcu]
      have habs : |u| < w := by
        by_contra hge
        have hge' : w ≤ |u| := not_lt.mp hge
        have hsq' : w ^ 2 ≤ u ^ 2 := by
          rw [← sq_abs u]; exact pow_le_pow_left₀ hw_pos.le hge' 2
        linarith only [husq, hsq']
      exact abs_lt.mp habs
    · rintro ⟨h1, h2⟩
      have habs : |u| < w := abs_lt.mpr ⟨h1, h2⟩
      have husq : u ^ 2 < w ^ 2 := by
        rw [← sq_abs u]
        exact pow_lt_pow_left₀ habs (abs_nonneg u) two_ne_zero
      rw [hw_sq, lt_div_iff₀ hc] at husq
      have hnn : 0 ≤ (c / 2) * u ^ 2 := mul_nonneg (by positivity) (sq_nonneg u)
      exact ⟨by linarith only [husq], by linarith only [hnn]⟩
  rw [hset_eq, Real.volume_Ioo, sub_neg_eq_add, ← two_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-- Dual `M = 2` closed-interval collar bound for `c`-strongly convex functions (`c > 0`, `δ ≥ 0`):
`{u ∈ S | G u ∈ [e₀, e₀ + δ]}` is covered by two closed intervals of combined length
`≤ 2 * √(2 * δ / c)`. -/
theorem stronglyConvexOn_collar_subset_two_Icc {c : ℝ} (hc : 0 < c) {S : Set ℝ} {G : ℝ → ℝ}
    (hG : IsStronglyConvexOn c S G) (e₀ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ a₁ b₁ a₂ b₂ : ℝ, a₁ ≤ b₁ ∧ a₂ ≤ b₂ ∧
      (b₁ - a₁) + (b₂ - a₂) ≤ 2 * Real.sqrt (2 * δ / c) ∧
      {u ∈ S | G u ∈ Icc e₀ (e₀ + δ)} ⊆ Icc a₁ b₁ ∪ Icc a₂ b₂ := by
  obtain ⟨a₁, b₁, a₂, b₂, hab₁, hab₂, hlen, hsub⟩ :=
    stronglyConcaveOn_collar_subset_two_Icc hc hG (-(e₀ + δ)) hδ
  refine ⟨a₁, b₁, a₂, b₂, hab₁, hab₂, hlen, fun u ⟨huS, hlo, hhi⟩ => hsub ⟨huS, ?_, ?_⟩⟩
  · linarith only [hhi]
  · linarith only [hlo]

private theorem gaussianReal_Icc_le_len {a b : ℝ} (_hab : a ≤ b) :
    (gaussianReal 0 1) (Icc a b) ≤ ENNReal.ofReal ((b - a) / Real.sqrt (2 * Real.pi)) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ measurableSet_Icc]
  have htop : ∀ t ∈ Icc a b,
      gaussianPDF 0 1 t ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) := by
    intro t _
    rw [gaussianPDF]
    apply ENNReal.ofReal_le_ofReal
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t]))
  refine (setLIntegral_mono' measurableSet_Icc htop).trans ?_
  rw [setLIntegral_const, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

private theorem gaussian_pi_rotating_two_Icc_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U)
    (w : EuclideanSpace ℝ ι) (hw : ‖w‖ = 1)
    {L e₀ δ : ℝ} (hL : 0 ≤ L)
    (hfib : ∀ y₀ : ι → ℝ, ∃ a₁ b₁ a₂ b₂ : ℝ, a₁ ≤ b₁ ∧ a₂ ≤ b₂ ∧
      (b₁ - a₁) + (b₂ - a₂) ≤ L ∧
      {t : ℝ | y₀ + t • w.ofLp ∈ U ∧ F (y₀ + t • w.ofLp) ∈ Ioc e₀ (e₀ + δ)} ⊆
        Icc a₁ b₁ ∪ Icc a₂ b₂) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real {x ∈ U | F x ∈ Ioc e₀ (e₀ + δ)} ≤
      L / Real.sqrt (2 * Real.pi) := by
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨R_iso, hR_single⟩ := exists_linearIsometryEquiv_single_eq i₀ hw
  let φ : (ι → ℝ) → (ι → ℝ) := fun z => (R_iso (WithLp.toLp 2 z)).ofLp
  have hmp_φ : MeasurePreserving φ γ_pi γ_pi :=
    measurePreserving_pi_gaussian_linearIsometryEquiv R_iso
  have hφ_upd (y : ι → ℝ) (t : ℝ) :
      φ (Function.update y i₀ t) = φ (Function.update y i₀ 0) + t • w.ofLp := by
    have hdec : Function.update y i₀ t =
        Function.update y i₀ 0 + t • (EuclideanSpace.single i₀ (1 : ℝ)).ofLp := by
      funext i
      by_cases hi : i = i₀
      · subst hi; simp
      · simp [hi]
    have hadd (z₁ z₂ : ι → ℝ) : φ (z₁ + z₂) = φ z₁ + φ z₂ := by
      change (R_iso (WithLp.toLp 2 z₁ + WithLp.toLp 2 z₂)).ofLp = _; rw [map_add]; rfl
    have hsmul (s : ℝ) (z : ι → ℝ) : φ (s • z) = s • φ z := by
      change (R_iso (s • WithLp.toLp 2 z)).ofLp = _; rw [map_smul]; rfl
    have he₀ : φ ((EuclideanSpace.single i₀ (1 : ℝ)).ofLp) = w.ofLp := by
      change (R_iso (EuclideanSpace.single i₀ 1)).ofLp = w.ofLp; rw [hR_single]
    rw [hdec, hadd, hsmul, he₀]
  let E_set : Set (ι → ℝ) := {x ∈ U | F x ∈ Ioc e₀ (e₀ + δ)}
  have hE_meas : MeasurableSet E_set := hU.inter (hF measurableSet_Ioc)
  have hpre_eq : γ_pi.real E_set = γ_pi.real (φ ⁻¹' E_set) :=
    (congrArg ENNReal.toReal (hmp_φ.measure_preimage hE_meas.nullMeasurableSet)).symm
  rw [hpre_eq]
  refine gaussian_pi_le_of_fiber_bound i₀ (hmp_φ.measurable hE_meas)
    (div_nonneg hL (by positivity)) fun y => ?_
  obtain ⟨a₁, b₁, a₂, b₂, hab₁, hab₂, hlen, hsub⟩ := hfib (φ (Function.update y i₀ 0))
  have hsub' : {t : ℝ | Function.update y i₀ t ∈ φ ⁻¹' E_set} ⊆ Icc a₁ b₁ ∪ Icc a₂ b₂ := by
    intro t ht
    apply hsub
    simpa only [mem_preimage, E_set, mem_setOf_eq, hφ_upd y t] using ht
  calc (gaussianReal 0 1) {t : ℝ | Function.update y i₀ t ∈ φ ⁻¹' E_set}
      ≤ (gaussianReal 0 1) (Icc a₁ b₁ ∪ Icc a₂ b₂) := measure_mono hsub'
    _ ≤ (gaussianReal 0 1) (Icc a₁ b₁) + (gaussianReal 0 1) (Icc a₂ b₂) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((b₁ - a₁) / Real.sqrt (2 * Real.pi)) +
          ENNReal.ofReal ((b₂ - a₂) / Real.sqrt (2 * Real.pi)) :=
        add_le_add (gaussianReal_Icc_le_len hab₁) (gaussianReal_Icc_le_len hab₂)
    _ = ENNReal.ofReal (((b₁ - a₁) + (b₂ - a₂)) / Real.sqrt (2 * Real.pi)) := by
        rw [← ENNReal.ofReal_add (div_nonneg (sub_nonneg.mpr hab₁) (by positivity))
          (div_nonneg (sub_nonneg.mpr hab₂) (by positivity)), add_div]
    _ ≤ ENNReal.ofReal (L / Real.sqrt (2 * Real.pi)) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hlen (by positivity))

/-- Rotating-direction product-Gaussian anti-concentration for arbitrary pointwise infima of
`c`-strongly concave families (`|α|`-free, `M = 2`):
`ℙ(x ∈ Ω ∧ F x ∈ Ioc e₀ (e₀ + δ)) ≤ J * (2 / √π) * √(δ / c)`. -/
theorem gaussian_rotatingDirection_stronglyConcaveInf_anticoncentration
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type*} [Nonempty α]
    {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    {Ω : Set (ι → ℝ)} (_hΩ : MeasurableSet Ω)
    {J : ℕ} (U : Fin J → Set (ι → ℝ)) (hU_meas : ∀ r, MeasurableSet (U r))
    (hcov : Ω ⊆ ⋃ r : Fin J, U r)
    (w : Fin J → EuclideanSpace ℝ ι) (hw : ∀ r, ‖w r‖ = 1)
    {c e₀ δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (hfib : ∀ r : Fin J, ∀ y₀ : ι → ℝ, ∃ (S : Set ℝ) (f : α → ℝ → ℝ),
      {t : ℝ | y₀ + t • (w r).ofLp ∈ U r} ⊆ S ∧
      (∀ i : α, IsStronglyConcaveOn c S (f i)) ∧
      (∀ t ∈ S, BddBelow (Set.range fun i : α => f i t)) ∧
      (∀ t ∈ S, F (y₀ + t • (w r).ofLp) = ⨅ i : α, f i t)) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ≤
      (J : ℝ) * (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  haveI : IsProbabilityMeasure γ_pi := by dsimp only [γ_pi]; infer_instance
  let L : ℝ := 2 * Real.sqrt (2 * δ / c)
  have hL_eq : L / Real.sqrt (2 * Real.pi) = (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
    dsimp only [L]
    rw [Real.sqrt_mul two_pos.le, show (2 : ℝ) * δ / c = 2 * (δ / c) by ring,
      Real.sqrt_mul two_pos.le]
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr two_pos).ne'
    have hspi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp [hs2, hspi]
  have hchart (r : Fin J) :
      γ_pi.real {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} ≤
        (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
    rw [← hL_eq]
    refine gaussian_pi_rotating_two_Icc_le hF (hU_meas r) (w r) (hw r)
      (by dsimp [L]; positivity) fun y₀ => ?_
    obtain ⟨S, f, hsub_S, hf_conc, hbdd, hF_eq⟩ := hfib r y₀
    have hinf_conc : IsStronglyConcaveOn c S (fun t => ⨅ i : α, f i t) :=
      isStronglyConcaveOn_iInf hf_conc hbdd
    obtain ⟨a₁, b₁, a₂, b₂, hab₁, hab₂, hlen, hsub_Icc⟩ :=
      stronglyConcaveOn_collar_subset_two_Icc hc hinf_conc e₀ hδ
    refine ⟨a₁, b₁, a₂, b₂, hab₁, hab₂, hlen, fun t ⟨htU, htF⟩ => hsub_Icc ⟨hsub_S htU, ?_⟩⟩
    rw [← hF_eq t (hsub_S htU)]
    exact Ioc_subset_Icc_self htF
  have hsub_u : {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ⊆
      ⋃ r ∈ (Finset.univ : Finset (Fin J)), {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} := by
    rintro x ⟨hxΩ, hxF⟩
    obtain ⟨r, hr⟩ := mem_iUnion.mp (hcov hxΩ)
    exact mem_iUnion₂.mpr ⟨r, Finset.mem_univ r, hr, hxF⟩
  calc γ_pi.real {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)}
      ≤ γ_pi.real (⋃ r ∈ (Finset.univ : Finset (Fin J)), {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)}) :=
          measureReal_mono hsub_u (measure_ne_top _ _)
    _ ≤ ∑ r ∈ (Finset.univ : Finset (Fin J)), γ_pi.real {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} :=
          measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _r : Fin J, (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) :=
          Finset.sum_le_sum fun r _ => hchart r
    _ = (J : ℝ) * (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- Dual rotating-direction product-Gaussian anti-concentration for arbitrary pointwise suprema of
`c`-strongly convex families (`|Θ|`-free, `M = 2`):
`ℙ(x ∈ Ω ∧ G x ∈ Ioc e₀ (e₀ + δ)) ≤ J * (2 / √π) * √(δ / c)`. -/
theorem gaussian_rotatingDirection_stronglyConvexSup_anticoncentration
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Θ : Type*} [Nonempty Θ]
    {G : (ι → ℝ) → ℝ} (hG : Measurable G)
    {Ω : Set (ι → ℝ)} (_hΩ : MeasurableSet Ω)
    {J : ℕ} (U : Fin J → Set (ι → ℝ)) (hU_meas : ∀ r, MeasurableSet (U r))
    (hcov : Ω ⊆ ⋃ r : Fin J, U r)
    (w : Fin J → EuclideanSpace ℝ ι) (hw : ∀ r, ‖w r‖ = 1)
    {c e₀ δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (hfib : ∀ r : Fin J, ∀ y₀ : ι → ℝ, ∃ (S : Set ℝ) (g : Θ → ℝ → ℝ),
      {t : ℝ | y₀ + t • (w r).ofLp ∈ U r} ⊆ S ∧
      (∀ θ : Θ, IsStronglyConvexOn c S (g θ)) ∧
      (∀ t ∈ S, BddAbove (Set.range fun θ : Θ => g θ t)) ∧
      (∀ t ∈ S, G (y₀ + t • (w r).ofLp) = ⨆ θ : Θ, g θ t)) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real {x ∈ Ω | G x ∈ Ioc e₀ (e₀ + δ)} ≤
      (J : ℝ) * (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  haveI : IsProbabilityMeasure γ_pi := by dsimp only [γ_pi]; infer_instance
  let L : ℝ := 2 * Real.sqrt (2 * δ / c)
  have hL_eq : L / Real.sqrt (2 * Real.pi) = (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
    dsimp only [L]
    rw [Real.sqrt_mul two_pos.le, show (2 : ℝ) * δ / c = 2 * (δ / c) by ring,
      Real.sqrt_mul two_pos.le]
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr two_pos).ne'
    have hspi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp [hs2, hspi]
  have hchart (r : Fin J) :
      γ_pi.real {x ∈ U r | G x ∈ Ioc e₀ (e₀ + δ)} ≤
        (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
    rw [← hL_eq]
    refine gaussian_pi_rotating_two_Icc_le hG (hU_meas r) (w r) (hw r)
      (by dsimp [L]; positivity) fun y₀ => ?_
    obtain ⟨S, g, hsub_S, hg_conv, hbdd, hG_eq⟩ := hfib r y₀
    have hsup_conv : IsStronglyConvexOn c S (fun t => ⨆ θ : Θ, g θ t) :=
      isStronglyConvexOn_iSup hg_conv hbdd
    obtain ⟨a₁, b₁, a₂, b₂, hab₁, hab₂, hlen, hsub_Icc⟩ :=
      stronglyConvexOn_collar_subset_two_Icc hc hsup_conv e₀ hδ
    refine ⟨a₁, b₁, a₂, b₂, hab₁, hab₂, hlen, fun t ⟨htU, htG⟩ => hsub_Icc ⟨hsub_S htU, ?_⟩⟩
    rw [← hG_eq t (hsub_S htU)]
    exact Ioc_subset_Icc_self htG
  have hsub_u : {x ∈ Ω | G x ∈ Ioc e₀ (e₀ + δ)} ⊆
      ⋃ r ∈ (Finset.univ : Finset (Fin J)), {x ∈ U r | G x ∈ Ioc e₀ (e₀ + δ)} := by
    rintro x ⟨hxΩ, hxG⟩
    obtain ⟨r, hr⟩ := mem_iUnion.mp (hcov hxΩ)
    exact mem_iUnion₂.mpr ⟨r, Finset.mem_univ r, hr, hxG⟩
  calc γ_pi.real {x ∈ Ω | G x ∈ Ioc e₀ (e₀ + δ)}
      ≤ γ_pi.real (⋃ r ∈ (Finset.univ : Finset (Fin J)), {x ∈ U r | G x ∈ Ioc e₀ (e₀ + δ)}) :=
          measureReal_mono hsub_u (measure_ne_top _ _)
    _ ≤ ∑ r ∈ (Finset.univ : Finset (Fin J)), γ_pi.real {x ∈ U r | G x ∈ Ioc e₀ (e₀ + δ)} :=
          measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _r : Fin J, (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) :=
          Finset.sum_le_sum fun r _ => hchart r
    _ = (J : ℝ) * (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- Direct fixed-`1 / 10` zero-drop locking `m_{1/10 + δ} = m_{1/10}` from `c`-strongly convex
supremum charts across all `Q = (4 N + 1)(2 N + 2)(2^N)^2` active circuit budgets, with zero
`Θ`-switching multiplicity loss (`M = 2` universally). -/
theorem fixed_tenth_locking_of_stronglyConvexSup_charts
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Θ : Type*} [Nonempty Θ]
    {N : ℕ} (hN : 2 ≤ N)
    (H : (ι → ℝ) → selfAdjoint (Register N))
    (hH_meas : ∀ j : ℕ, Measurable fun x => criticalHeight (H x) j)
    {Ω : ℕ → Set (ι → ℝ)} (hΩ_meas : ∀ j, MeasurableSet (Ω j))
    (J : ℕ) {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 ≤ δ)
    (hcharts : ∀ j < (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2,
      ∃ (U : Fin J → Set (ι → ℝ)) (w : Fin J → EuclideanSpace ℝ ι),
        (∀ r, MeasurableSet (U r)) ∧ Ω j ⊆ (⋃ r : Fin J, U r) ∧ (∀ r, ‖w r‖ = 1) ∧
        (∀ r : Fin J, ∀ y₀ : ι → ℝ, ∃ (S : Set ℝ) (g : Θ → ℝ → ℝ),
          {t : ℝ | y₀ + t • (w r).ofLp ∈ U r} ⊆ S ∧
          (∀ θ : Θ, IsStronglyConvexOn c S (g θ)) ∧
          (∀ t ∈ S, BddAbove (Set.range fun θ : Θ => g θ t)) ∧
          (∀ t ∈ S, criticalHeight (H (y₀ + t • (w r).ofLp)) j = ⨆ θ : Θ, g θ t))) :
    let Q := (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2
    let Ω_all := ⋂ j ∈ Finset.range Q, Ω j
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω_all | ∃ m₁ m₂ : ℕ,
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂} ≤
      (Q : ℝ) * (J : ℝ) * (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
  intro Q Ω_all
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  haveI : IsProbabilityMeasure γ_pi := by dsimp only [γ_pi]; infer_instance
  let Bad := {x : ι → ℝ | x ∈ Ω_all ∧ ∃ m₁ m₂ : ℕ,
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂}
  have hsub : Bad ⊆ ⋃ j ∈ Finset.range Q,
      {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} := by
    rintro x ⟨hxΩ, m₁, m₂, hm₁, hm₂, hne⟩
    have hnot_clear : ¬ (1 / 10 : ℝ) ∉ jumpTolerances (H x) δ := fun hclear =>
      hne ((maximum_eq_iff_criticalHeight_clearance hN (H x) (by norm_num) hδ0 hm₁ hm₂).2.mpr hclear)
    rw [not_not] at hnot_clear
    obtain ⟨j, _, hj_mem⟩ := hnot_clear
    have hj_lt_Q : j < Q := by
      by_contra hge
      have h0 := criticalHeight_eq_zero_of_exact_cap hN (H x) (Nat.le_of_not_lt hge)
      rw [h0] at hj_mem; linarith only [hj_mem.1]
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj_lt_Q,
      (mem_iInter₂.mp hxΩ) j (Finset.mem_range.mpr hj_lt_Q), hj_mem⟩
  calc γ_pi.real Bad
      ≤ γ_pi.real (⋃ j ∈ Finset.range Q,
          {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)}) :=
          measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range Q,
          γ_pi.real {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} :=
          measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range Q,
          (J : ℝ) * (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨U, w, hUm, hcov, hw, hfib⟩ := hcharts j (Finset.mem_range.mp hj)
          exact gaussian_rotatingDirection_stronglyConvexSup_anticoncentration
            (hH_meas j) (hΩ_meas j) U hUm hcov w hw (e₀ := (1 / 10 : ℝ)) hc hδ0 hfib
    _ = (Q : ℝ) * (J : ℝ) * (2 / Real.sqrt Real.pi) * Real.sqrt (δ / c) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end AbstractStrongCurvatureEnvelopes

/-! ## Section 2: Three-part sign and minimax obstruction audit on `torusCriticalHeight` at `e = 1 / 10` -/

/-! ### Audit B1: Minimax quantifier-swap duality gap (`≥ 1` fixed target, `≥ 1 / 2` modulo phase) -/

private theorem projectiveSpectralMatrix_zero_eq_one {N d : ℕ}
    (e : Config N ≃ Fin (d + 1)) (V : UGroup N) :
    projectiveSpectralMatrix e V (0 : Fin d → UnitAddCircle) = (1 : Register N) := by
  unfold projectiveSpectralMatrix
  have hdiag : (Matrix.diagonal fun q : Config N =>
      fourier 1 (RHTower.zeroAnchoredPhase d (0 : Fin d → UnitAddCircle) (e q))) = 1 := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      generalize e x = r
      rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨k, rfl⟩ <;>
        simp [RHTower.zeroAnchoredPhase]
    · simp [hxy]
  rw [hdiag, mul_one]
  exact (Unitary.mem_iff.mp V.2).2

private theorem mulVec_projectiveSpectralMatrix_eigenvector {N d : ℕ}
    (e : Config N ≃ Fin (d + 1)) (V : UGroup N)
    (θ : Fin d → UnitAddCircle) (r : Fin (d + 1)) :
    projectiveSpectralMatrix e V θ *ᵥ (fun x => V.val x (e.symm r)) =
      fourier 1 (RHTower.zeroAnchoredPhase d θ r) • (fun x => V.val x (e.symm r)) := by
  let M : Register N := V.val
  have hproj : projectiveSpectralMatrix e V θ =
      M * Matrix.diagonal (fun q : Config N => fourier 1 (RHTower.zeroAnchoredPhase d θ (e q))) *
        star M := rfl
  rw [hproj, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hstar_v : (star M) *ᵥ (fun x => M x (e.symm r)) =
      fun y => if y = e.symm r then 1 else 0 := by
    ext y
    have h1 := congrFun (congrFun (Unitary.mem_iff.mp V.2).1 y) (e.symm r)
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    exact h1
  rw [hstar_v]
  have hdiag_v : (Matrix.diagonal fun q : Config N =>
      fourier 1 (RHTower.zeroAnchoredPhase d θ (e q))) *ᵥ
        (fun y => if y = e.symm r then (1 : ℂ) else 0) =
      fun y => if y = e.symm r then fourier 1 (RHTower.zeroAnchoredPhase d θ r) else 0 := by
    ext y
    rw [Matrix.mulVec_diagonal]
    by_cases hy : y = e.symm r
    · subst hy; simp
    · simp [hy]
  rw [hdiag_v]
  ext x
  simp [Matrix.mulVec, dotProduct, M]
  ring

private theorem norm_eigenvector_col_eq_one {N : ℕ} (V : UGroup N) (q : Config N) :
    ‖(WithLp.toLp 2 (fun x : Config N => V.val x q) : EuclideanSpace ℂ (Config N))‖ = 1 := by
  let M : Register N := V.val
  have hsq : ‖(WithLp.toLp 2 (fun x : Config N => M x q) : EuclideanSpace ℂ (Config N))‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have h1 := congrFun (congrFun (Unitary.mem_iff.mp V.2).1 q) q
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.one_apply_eq] at h1
    have h2 : ((∑ x : Config N, ‖M x q‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
      push_cast; rfl
    exact_mod_cast h2
  nlinarith only [hsq,
    norm_nonneg (WithLp.toLp 2 (fun x : Config N => M x q) : EuclideanSpace ℂ (Config N)),
    sq_nonneg (‖(WithLp.toLp 2 (fun x : Config N => M x q) : EuclideanSpace ℂ (Config N))‖ - 1)]

private theorem fourier_one_half_eq_neg_one :
    fourier 1 (((1 / 2 : ℝ) : UnitAddCircle)) = (-1 : ℂ) := by
  rw [fourier_coe_apply]
  have hexp : (2 * ↑Real.pi * Complex.I * ↑(1 : ℤ) * ↑(1 / 2 : ℝ) / ↑(1 : ℝ) : ℂ) =
      ↑Real.pi * Complex.I := by push_cast; ring
  rw [hexp, Complex.exp_pi_mul_I]

/-- Quantifier-swap minimax gap (fixed projective target): for every `N`, every `d ≥ 1`, every
`V ∈ U(2^N)`, and every fixed matrix `W : Register N` (in particular every `W ∈ C_s`), there exists
`θ : Fin d → UnitAddCircle` with `1 ≤ ‖projectiveSpectralMatrix e V θ - W‖`. -/
theorem swapped_torusCriticalHeight_fixedTarget_ge_one {N d : ℕ} (hd : 1 ≤ d)
    (e : Config N ≃ Fin (d + 1)) (V : UGroup N) (W : Register N) :
    ∃ θ : Fin d → UnitAddCircle, 1 ≤ ‖projectiveSpectralMatrix e V θ - W‖ := by
  let k₀ : Fin d := ⟨0, hd⟩
  let θ_half : Fin d → UnitAddCircle := fun k => if k = k₀ then ((1 / 2 : ℝ) : UnitAddCircle) else 0
  let v₁ : Config N → ℂ := fun x => V.val x (e.symm k₀.succ)
  let ψ₁ : EuclideanSpace ℂ (Config N) := WithLp.toLp 2 v₁
  have hψ₁_norm : ‖ψ₁‖ = 1 := norm_eigenvector_col_eq_one V (e.symm k₀.succ)
  have hdiff_act :
      (projectiveSpectralMatrix e V 0 - projectiveSpectralMatrix e V θ_half) *ᵥ ψ₁.ofLp =
        (2 : ℂ) • ψ₁.ofLp := by
    have h0 := projectiveSpectralMatrix_zero_eq_one e V
    have h1 : projectiveSpectralMatrix e V θ_half *ᵥ v₁ = (-1 : ℂ) • v₁ := by
      have hv := mulVec_projectiveSpectralMatrix_eigenvector e V θ_half k₀.succ
      have hph : fourier 1 (RHTower.zeroAnchoredPhase d θ_half k₀.succ) = -1 := by
        simpa [RHTower.zeroAnchoredPhase, θ_half] using fourier_one_half_eq_neg_one
      rwa [hph] at hv
    change (projectiveSpectralMatrix e V 0 - projectiveSpectralMatrix e V θ_half) *ᵥ v₁ = (2 : ℂ) • v₁
    rw [Matrix.sub_mulVec, h0, Matrix.one_mulVec, h1]
    ext x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hdist2 : (2 : ℝ) ≤ ‖projectiveSpectralMatrix e V 0 - projectiveSpectralMatrix e V θ_half‖ := by
    have hle := Matrix.l2_opNorm_mulVec
      (projectiveSpectralMatrix e V 0 - projectiveSpectralMatrix e V θ_half) ψ₁
    have hψ₁_eq : (EuclideanSpace.equiv (Config N) ℂ).symm ψ₁.ofLp = ψ₁ := rfl
    rw [hdiff_act, map_smul, norm_smul, hψ₁_eq, hψ₁_norm, mul_one, mul_one] at hle
    simpa using hle
  have htri : ‖projectiveSpectralMatrix e V 0 - projectiveSpectralMatrix e V θ_half‖ ≤
      ‖projectiveSpectralMatrix e V 0 - W‖ + ‖projectiveSpectralMatrix e V θ_half - W‖ := by
    have heq : projectiveSpectralMatrix e V 0 - projectiveSpectralMatrix e V θ_half =
        (projectiveSpectralMatrix e V 0 - W) - (projectiveSpectralMatrix e V θ_half - W) := by abel
    rw [heq]; exact norm_sub_le _ _
  by_cases h0_ge : 1 ≤ ‖projectiveSpectralMatrix e V 0 - W‖
  · exact ⟨0, h0_ge⟩
  · exact ⟨θ_half, by linarith only [hdist2, htri, not_le.mp h0_ge]⟩

/-- Quantifier-swap minimax gap even modulo `θ`-dependent global phases: for every `N`, every
`d ≥ 1`, every `V ∈ U(2^N)`, and every fixed circuit `C : TwoQubitCircuit N` (at **any** gate count,
even above the exact synthesis cap `2^(6 N)` where `torusCriticalHeight = 0`), there exists
`θ : Fin d → UnitAddCircle` such that `1 / 2 ≤ ‖projectiveSpectralMatrix e V θ - z • C.eval‖` for
all unit-modulus `z ∈ ℂ`. -/
theorem swapped_torusCriticalHeight_modPhase_ge_half {N d : ℕ} (hd : 1 ≤ d)
    (e : Config N ≃ Fin (d + 1)) (V : UGroup N) (C : TwoQubitCircuit N) :
    ∃ θ : Fin d → UnitAddCircle, ∀ z : ℂ, ‖z‖ = 1 →
      (1 / 2 : ℝ) ≤ ‖projectiveSpectralMatrix e V θ - z • (C.eval : Register N)‖ := by
  let k₀ : Fin d := ⟨0, hd⟩
  let θ_half : Fin d → UnitAddCircle := fun k => if k = k₀ then ((1 / 2 : ℝ) : UnitAddCircle) else 0
  by_contra hnot
  push Not at hnot
  obtain ⟨z₀, hz₀, hlt₀⟩ := hnot 0
  obtain ⟨z₁, hz₁, hlt₁⟩ := hnot θ_half
  let w : ℂ := z₁ * star z₀
  have hzz₀ : star z₀ * z₀ = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hz₀, Complex.ofReal_one, one_pow]
  have hw_norm : ‖w‖ = 1 := by dsimp only [w]; rw [norm_mul, norm_star, hz₁, hz₀, mul_one]
  have hw_sub : ‖projectiveSpectralMatrix e V θ_half - w • (1 : Register N)‖ < 1 := by
    have h0_eq : projectiveSpectralMatrix e V 0 = 1 := projectiveSpectralMatrix_zero_eq_one e V
    rw [h0_eq] at hlt₀
    have hw_smul : ‖w • ((1 : Register N) - z₀ • (C.eval : Register N))‖ < 1 / 2 := by
      rw [norm_smul, hw_norm, one_mul]; exact hlt₀
    have hsmul_cancel : w • ((1 : Register N) - z₀ • (C.eval : Register N)) =
        w • (1 : Register N) - z₁ • (C.eval : Register N) := by
      rw [smul_sub, smul_smul]; dsimp only [w]; rw [mul_assoc, hzz₀, mul_one]
    rw [hsmul_cancel] at hw_smul
    have hdecomp : projectiveSpectralMatrix e V θ_half - w • (1 : Register N) =
        (projectiveSpectralMatrix e V θ_half - z₁ • (C.eval : Register N)) -
          (w • (1 : Register N) - z₁ • (C.eval : Register N)) := by abel
    rw [hdecomp]
    exact lt_of_le_of_lt (norm_sub_le _ _) (by linarith only [hlt₁, hw_smul])
  let v₀ : Config N → ℂ := fun x => V.val x (e.symm 0)
  let v₁ : Config N → ℂ := fun x => V.val x (e.symm k₀.succ)
  let ψ₀ : EuclideanSpace ℂ (Config N) := WithLp.toLp 2 v₀
  let ψ₁ : EuclideanSpace ℂ (Config N) := WithLp.toLp 2 v₁
  have hψ₀_n : ‖ψ₀‖ = 1 := norm_eigenvector_col_eq_one V (e.symm 0)
  have hψ₁_n : ‖ψ₁‖ = 1 := norm_eigenvector_col_eq_one V (e.symm k₀.succ)
  have hact₀ : ‖(1 : ℂ) - w‖ ≤ ‖projectiveSpectralMatrix e V θ_half - w • (1 : Register N)‖ := by
    have hle := Matrix.l2_opNorm_mulVec
      (projectiveSpectralMatrix e V θ_half - w • (1 : Register N)) ψ₀
    rw [hψ₀_n, mul_one] at hle
    have hmv : (projectiveSpectralMatrix e V θ_half - w • (1 : Register N)) *ᵥ ψ₀.ofLp =
        (1 - w) • ψ₀.ofLp := by
      have hv : projectiveSpectralMatrix e V θ_half *ᵥ v₀ = v₀ := by
        have h := mulVec_projectiveSpectralMatrix_eigenvector e V θ_half 0
        have hph : fourier 1 (RHTower.zeroAnchoredPhase d θ_half 0) = 1 := by
          simp [RHTower.zeroAnchoredPhase]
        rwa [hph, one_smul] at h
      change (projectiveSpectralMatrix e V θ_half - w • (1 : Register N)) *ᵥ v₀ = (1 - w) • v₀
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv]
      ext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hψ₀_eq : (EuclideanSpace.equiv (Config N) ℂ).symm ψ₀.ofLp = ψ₀ := rfl
    rwa [hmv, map_smul, norm_smul, hψ₀_eq, hψ₀_n, mul_one] at hle
  have hact₁ : ‖(-1 : ℂ) - w‖ ≤ ‖projectiveSpectralMatrix e V θ_half - w • (1 : Register N)‖ := by
    have hle := Matrix.l2_opNorm_mulVec
      (projectiveSpectralMatrix e V θ_half - w • (1 : Register N)) ψ₁
    rw [hψ₁_n, mul_one] at hle
    have hmv : (projectiveSpectralMatrix e V θ_half - w • (1 : Register N)) *ᵥ ψ₁.ofLp =
        (-1 - w) • ψ₁.ofLp := by
      have hv : projectiveSpectralMatrix e V θ_half *ᵥ v₁ = (-1 : ℂ) • v₁ := by
        have h := mulVec_projectiveSpectralMatrix_eigenvector e V θ_half k₀.succ
        have hph : fourier 1 (RHTower.zeroAnchoredPhase d θ_half k₀.succ) = -1 := by
          simpa [RHTower.zeroAnchoredPhase, θ_half] using fourier_one_half_eq_neg_one
        rwa [hph] at h
      change (projectiveSpectralMatrix e V θ_half - w • (1 : Register N)) *ᵥ v₁ = (-1 - w) • v₁
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv]
      ext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hψ₁_eq : (EuclideanSpace.equiv (Config N) ℂ).symm ψ₁.ofLp = ψ₁ := rfl
    rwa [hmv, map_smul, norm_smul, hψ₁_eq, hψ₁_n, mul_one] at hle
  have h2_le : (2 : ℝ) ≤ ‖(1 : ℂ) - w‖ + ‖(-1 : ℂ) - w‖ := by
    have h2 : (2 : ℂ) = ((1 : ℂ) - w) - ((-1 : ℂ) - w) := by ring
    have hn : (2 : ℝ) = ‖(2 : ℂ)‖ := by norm_num
    rw [hn, h2]
    exact norm_sub_le _ _
  linarith only [h2_le, hact₀, hact₁, hw_sub]

/-! ### Audit B2: Universal `C*`-algebra semiconvexity, strictly positive curvature at `1 / 10`, and upward V-kinks -/

section AbstractSemiconvexity

/-- Hahn–Banach-free Banach-space norm semiconvexity: for any `C^2` curve `γ : ℝ → E` into a real
normed space with `∀ u, ‖γ'' u‖ ≤ M` (`0 ≤ M`), `u ↦ ‖γ u‖ + M * u^2` is convex on `ℝ`. -/
theorem convexOn_norm_add_sq_of_norm_deriv2_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ γ' γ'' : ℝ → E} {M : ℝ} (hM : 0 ≤ M)
    (hγ : ∀ u : ℝ, HasDerivAt γ (γ' u) u)
    (hγ' : ∀ u : ℝ, HasDerivAt γ' (γ'' u) u)
    (hbdd : ∀ u : ℝ, ‖γ'' u‖ ≤ M) :
    ConvexOn ℝ univ (fun u : ℝ => ‖γ u‖ + M * u ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  let m : ℝ := a * x + b * y
  -- Bound the first-order Taylor remainder R(t) = γ(t) - γ(m) - (t - m) • γ'(m) by M * (t - m)^2.
  let R : ℝ → E := fun t => γ t - γ m - (t - m) • γ' m
  let R' : ℝ → E := fun t => γ' t - γ' m
  have hR_deriv (t : ℝ) : HasDerivAt R (R' t) t := by
    have hlin : HasDerivAt (fun s : ℝ => (s - m) • γ' m) (γ' m) t :=
      (((hasDerivAt_id' t).sub_const m).smul_const (γ' m)).congr_deriv (one_smul ℝ (γ' m))
    exact ((hγ t).sub_const (γ m)).sub hlin
  have hR'_deriv (t : ℝ) : HasDerivAt R' (γ'' t) t := (hγ' t).sub_const (γ' m)
  have hR_bound (t : ℝ) : ‖R t‖ ≤ M * (t - m) ^ 2 := by
    have hR'_le (s : ℝ) : ‖R' s‖ ≤ M * |s - m| := by
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun τ _ => (hR'_deriv τ).hasDerivWithinAt) (fun τ _ => hbdd τ)
        convex_univ (mem_univ m) (mem_univ s)
      simpa only [R', sub_self, sub_zero, Real.norm_eq_abs] using hmvt
    let S_seg : Set ℝ := uIcc m t
    have hS_conv : Convex ℝ S_seg := convex_uIcc m t
    have hR'_seg : ∀ s ∈ S_seg, ‖R' s‖ ≤ M * |t - m| := by
      intro s hs
      refine (hR'_le s).trans (mul_le_mul_of_nonneg_left ?_ hM)
      rw [mem_uIcc] at hs
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hsm : |s - m| = s - m := abs_of_nonneg (sub_nonneg.mpr h1)
        have htm : |t - m| = t - m := abs_of_nonneg (by linarith only [h1, h2])
        rw [hsm, htm]; linarith only [h2]
      · have hsm : |s - m| = -(s - m) := abs_of_nonpos (sub_nonpos.mpr h2)
        have htm : |t - m| = -(t - m) := abs_of_nonpos (by linarith only [h1, h2])
        rw [hsm, htm]; linarith only [h1]
    have hmvt2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := R) (s := S_seg)
      (fun s _ => (hR_deriv s).hasDerivWithinAt) hR'_seg
      hS_conv left_mem_uIcc right_mem_uIcc
    have hRm : R m = 0 := by simp [R]
    rw [hRm, sub_zero, Real.norm_eq_abs] at hmvt2
    calc ‖R t‖ ≤ M * |t - m| * |t - m| := hmvt2
      _ = M * (t - m) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  -- Combine γ(m) = a • γ(x) + b • γ(y) - a • R(x) - b • R(y) since a*(x - m) + b*(y - m) = 0.
  have hcomb : γ m = a • γ x + b • γ y - a • R x - b • R y := by
    dsimp only [R]
    simp only [smul_sub, smul_smul]
    have h1 : (a + b) • γ m = γ m := by rw [hab, one_smul]
    have h2 : (a * (x - m) + b * (y - m)) = 0 := by
      dsimp only [m]
      have hb' : b = 1 - a := by linarith only [hab]
      rw [hb']; ring
    -- Rearrange module terms cleanly.
    have hrhs : a • γ x + b • γ y - (a • γ x - a • γ m - (a * (x - m)) • γ' m) -
        (b • γ y - b • γ m - (b * (y - m)) • γ' m) =
        (a + b) • γ m + (a * (x - m) + b * (y - m)) • γ' m := by
      rw [add_smul, add_smul]; abel
    rw [hrhs, h1, h2, zero_smul, add_zero]
  have hnorm_m : ‖γ m‖ ≤ a * ‖γ x‖ + b * ‖γ y‖ + a * ‖R x‖ + b * ‖R y‖ := by
    conv_lhs => rw [hcomb]
    have htri1 := norm_sub_le (a • γ x + b • γ y - a • R x) (b • R y)
    have htri2 := norm_sub_le (a • γ x + b • γ y) (a • R x)
    have htri3 := norm_add_le (a • γ x) (b • γ y)
    simp only [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] at htri1 htri2 htri3
    linarith only [htri1, htri2, htri3]
  have hrem_sum : a * ‖R x‖ + b * ‖R y‖ ≤ M * (a * b * (x - y) ^ 2) := by
    calc a * ‖R x‖ + b * ‖R y‖
        ≤ a * (M * (x - m) ^ 2) + b * (M * (y - m) ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left (hR_bound x) ha)
            (mul_le_mul_of_nonneg_left (hR_bound y) hb)
      _ = M * (a * b * (x - y) ^ 2) := by
          dsimp only [m]
          have hb' : b = 1 - a := by linarith only [hab]
          rw [hb']; ring
  have hq := quad_variance_identity hab x y
  dsimp only [m] at hnorm_m ⊢
  linarith [hnorm_m, hrem_sum, show M * (a * x ^ 2 + b * y ^ 2 - (a * x + b * y) ^ 2) =
    M * (a * b * (x - y) ^ 2) by rw [hq]]

/-- Universal `C*`-algebra frozen-target semiconvexity: for every self-adjoint `K`, `U₀`, and
`W_star` in a `C*`-algebra `A`, `u ↦ ‖exp(-i u K) U₀ exp(i u K) - W_star‖ + 4 ‖K‖^2 ‖U₀‖ u^2` is
globally convex on `ℝ`. -/
theorem convexOn_conjFlow_opNorm_add_four_sq {A : Type*} [CStarAlgebra A]
    (K U₀ W_star : A) (hK : IsSelfAdjoint K) :
    ConvexOn ℝ univ (fun u : ℝ =>
      ‖NormedSpace.exp (u • (-Complex.I • K)) * U₀ *
        NormedSpace.exp (u • (Complex.I • K)) - W_star‖ +
        4 * ‖K‖ ^ 2 * ‖U₀‖ * u ^ 2) := by
  let X_m : A := -Complex.I • K
  let X_p : A := Complex.I • K
  have hXm_skew : X_m ∈ skewAdjoint A := by
    dsimp only [X_m]
    rw [skewAdjoint.mem_iff, star_smul, star_neg, Complex.star_def, Complex.conj_I,
      neg_neg, hK.star_eq, neg_smul, neg_neg]
  have hXp_skew : X_p ∈ skewAdjoint A := by
    dsimp only [X_p]
    rw [skewAdjoint.mem_iff, star_smul, Complex.star_def, Complex.conj_I, hK.star_eq, neg_smul]
  have hXm_norm : ‖X_m‖ = ‖K‖ := by dsimp only [X_m]; rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  have hXp_norm : ‖X_p‖ = ‖K‖ := by dsimp only [X_p]; rw [norm_smul, Complex.norm_I, one_mul]
  let E_m (u : ℝ) : A := NormedSpace.exp (u • X_m)
  let E_p (u : ℝ) : A := NormedSpace.exp (u • X_p)
  let C₁ : A := X_m * U₀ + U₀ * X_p
  let C₂ : A := X_m * C₁ + C₁ * X_p
  let γ (u : ℝ) : A := E_m u * U₀ * E_p u - W_star
  let γ' (u : ℝ) : A := E_m u * C₁ * E_p u
  let γ'' (u : ℝ) : A := E_m u * C₂ * E_p u
  have hconj_deriv (B : A) (u : ℝ) :
      HasDerivAt (fun s : ℝ => E_m s * B * E_p s) (E_m u * (X_m * B + B * X_p) * E_p u) u := by
    have hd1 : HasDerivAt E_m (E_m u * X_m) u := hasDerivAt_exp_smul_const X_m u
    have hd2 : HasDerivAt E_p (X_p * E_p u) u := hasDerivAt_exp_smul_const' X_p u
    have hd := (hd1.mul_const B).fun_mul hd2
    refine hd.congr_deriv ?_
    simp only [mul_add, add_mul, mul_assoc]
  have hγ_d (u : ℝ) : HasDerivAt γ (γ' u) u := by
    simpa only [sub_zero] using (hconj_deriv U₀ u).sub_const W_star
  have hγ'_d (u : ℝ) : HasDerivAt γ' (γ'' u) u := hconj_deriv C₁ u
  have hE_norm (u : ℝ) : ‖E_m u‖ ≤ 1 ∧ ‖E_p u‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial A with hsub | hnt
    · exact ⟨by simp [Subsingleton.elim (E_m u) 0], by simp [Subsingleton.elim (E_p u) 0]⟩
    · letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
      have hum := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem u hXm_skew)
      have hup := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem u hXp_skew)
      exact ⟨(CStarRing.norm_of_mem_unitary hum).le, (CStarRing.norm_of_mem_unitary hup).le⟩
  have hC₁_norm : ‖C₁‖ ≤ 2 * ‖K‖ * ‖U₀‖ := by
    dsimp only [C₁]
    have h1 : ‖X_m * U₀‖ ≤ ‖K‖ * ‖U₀‖ := (norm_mul_le _ _).trans_eq (by rw [hXm_norm])
    have h2 : ‖U₀ * X_p‖ ≤ ‖K‖ * ‖U₀‖ := (norm_mul_le _ _).trans_eq (by rw [hXp_norm, mul_comm])
    linarith only [norm_add_le (X_m * U₀) (U₀ * X_p), h1, h2]
  have hC₂_norm : ‖C₂‖ ≤ 4 * ‖K‖ ^ 2 * ‖U₀‖ := by
    dsimp only [C₂]
    have h1 : ‖X_m * C₁‖ ≤ ‖K‖ * (2 * ‖K‖ * ‖U₀‖) :=
      (norm_mul_le _ _).trans (by rw [hXm_norm]; exact mul_le_mul_of_nonneg_left hC₁_norm (norm_nonneg K))
    have h2 : ‖C₁ * X_p‖ ≤ (2 * ‖K‖ * ‖U₀‖) * ‖K‖ :=
      (norm_mul_le _ _).trans (by rw [hXp_norm]; exact mul_le_mul_of_nonneg_right hC₁_norm (norm_nonneg K))
    linarith [norm_add_le (X_m * C₁) (C₁ * X_p), h1, h2,
      show ‖K‖ * (2 * ‖K‖ * ‖U₀‖) + (2 * ‖K‖ * ‖U₀‖) * ‖K‖ = 4 * ‖K‖ ^ 2 * ‖U₀‖ by ring]
  have hγ''_norm (u : ℝ) : ‖γ'' u‖ ≤ 4 * ‖K‖ ^ 2 * ‖U₀‖ := by
    dsimp only [γ'']
    obtain ⟨hm, hp⟩ := hE_norm u
    calc ‖E_m u * C₂ * E_p u‖
        ≤ ‖E_m u * C₂‖ * ‖E_p u‖ := norm_mul_le _ _
      _ ≤ (‖E_m u‖ * ‖C₂‖) * 1 :=
          mul_le_mul (norm_mul_le _ _) hp (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ (1 * ‖C₂‖) * 1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (norm_nonneg _)) zero_le_one
      _ ≤ 4 * ‖K‖ ^ 2 * ‖U₀‖ := by linarith only [hC₂_norm]
  exact convexOn_norm_add_sq_of_norm_deriv2_le (by positivity) hγ_d hγ'_d hγ''_norm

end AbstractSemiconvexity

private theorem exp_neg_I_smul_involution {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] {P : A} (hP2 : P * P = 1) (u : ℝ) :
    NormedSpace.exp (u • (-Complex.I • P)) =
      (Real.cos u : ℂ) • (1 : A) + (-Complex.I * (Real.sin u : ℂ)) • P := by
  let F (s : ℝ) : A := (Real.cos s : ℂ) • (1 : A) + (-Complex.I * (Real.sin s : ℂ)) • P
  let G (s : ℝ) : A := NormedSpace.exp (s • (Complex.I • P)) * F s
  have hG_deriv (s : ℝ) : HasDerivAt G 0 s := by
    have hd1 : HasDerivAt (fun r : ℝ => NormedSpace.exp (r • (Complex.I • P)))
        (NormedSpace.exp (s • (Complex.I • P)) * (Complex.I • P)) s :=
      hasDerivAt_exp_smul_const (Complex.I • P) s
    have hd_cos : HasDerivAt (fun r : ℝ => (Real.cos r : ℂ)) (-(Real.sin s : ℂ)) s :=
      (Complex.ofRealCLM.hasDerivAt.scomp s (Real.hasDerivAt_cos s)).congr_deriv (by simp)
    have hd_sin0 : HasDerivAt (fun r : ℝ => (Real.sin r : ℂ)) (Real.cos s : ℂ) s :=
      (Complex.ofRealCLM.hasDerivAt.scomp s (Real.hasDerivAt_sin s)).congr_deriv (by simp)
    have hd_sin : HasDerivAt (fun r : ℝ => -Complex.I * (Real.sin r : ℂ))
        (-Complex.I * (Real.cos s : ℂ)) s :=
      hd_sin0.const_mul (-Complex.I)
    have hd2 : HasDerivAt F ((-(Real.sin s : ℂ)) • (1 : A) + (-Complex.I * (Real.cos s : ℂ)) • P) s :=
      (hd_cos.smul_const (1 : A)).add (hd_sin.smul_const P)
    refine (hd1.fun_mul hd2).congr_deriv ?_
    have hinner : (Complex.I • P) * F s +
        ((-(Real.sin s : ℂ)) • (1 : A) + (-Complex.I * (Real.cos s : ℂ)) • P) = 0 := by
      dsimp only [F]
      rw [mul_add, smul_mul_smul_comm, smul_mul_smul_comm, mul_one, hP2]
      have hI : Complex.I * (-Complex.I * (Real.sin s : ℂ)) = (Real.sin s : ℂ) := by
        rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
      rw [hI]
      simp only [neg_mul, neg_smul]
      abel
    calc NormedSpace.exp (s • (Complex.I • P)) * (Complex.I • P) * F s +
          NormedSpace.exp (s • (Complex.I • P)) *
            ((-(Real.sin s : ℂ)) • (1 : A) + (-Complex.I * (Real.cos s : ℂ)) • P)
        = NormedSpace.exp (s • (Complex.I • P)) *
            ((Complex.I • P) * F s +
              ((-(Real.sin s : ℂ)) • (1 : A) + (-Complex.I * (Real.cos s : ℂ)) • P)) := by
          rw [mul_assoc, ← mul_add]
      _ = 0 := by rw [hinner, mul_zero]
  have hG_const : G u = G 0 := by
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ => (hG_deriv s).hasDerivWithinAt) (fun _ _ => by rw [norm_zero])
      convex_univ (mem_univ 0) (mem_univ u)
    rw [zero_mul] at hmvt
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hmvt)
  have hG0 : G 0 = 1 := by simp [G, F, NormedSpace.exp_zero]
  have hexp_cancel : NormedSpace.exp (u • (-Complex.I • P)) *
      NormedSpace.exp (u • (Complex.I • P)) = 1 := by
    letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
    have hcomm : Commute (u • (-Complex.I • P)) (u • (Complex.I • P)) := by
      have hc : Commute (-Complex.I • P) (Complex.I • P) := by
        change (-Complex.I • P) * (Complex.I • P) = (Complex.I • P) * (-Complex.I • P)
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (-Complex.I) Complex.I]
      exact (hc.smul_left u).smul_right u
    rw [← NormedSpace.exp_add_of_commute hcomm, ← smul_add, neg_smul, neg_add_cancel, smul_zero,
      NormedSpace.exp_zero]
  calc NormedSpace.exp (u • (-Complex.I • P))
      = NormedSpace.exp (u • (-Complex.I • P)) * G u := by rw [hG_const, hG0, mul_one]
    _ = (NormedSpace.exp (u • (-Complex.I • P)) * NormedSpace.exp (u • (Complex.I • P))) * F u := by
        dsimp only [G]; rw [mul_assoc]
    _ = F u := by rw [hexp_cancel, one_mul]

private def qubitZeroDiagPhase {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) : Register N :=
  Matrix.diagonal fun x : Config N =>
    if x ⟨0, hN⟩ then Complex.exp (-(Complex.I * (θ : ℂ))) else Complex.exp (Complex.I * (θ : ℂ))

private theorem conj_mul_exp_I_real (z : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (z : ℂ))) * Complex.exp (Complex.I * (z : ℂ)) = 1 ∧
    (starRingEnd ℂ) (Complex.exp (-(Complex.I * (z : ℂ)))) *
      Complex.exp (-(Complex.I * (z : ℂ))) = 1 := by
  constructor
  · rw [← Complex.exp_conj, ← Complex.exp_add]
    have h0 : (starRingEnd ℂ) (Complex.I * (z : ℂ)) + Complex.I * (z : ℂ) = 0 := by
      simp [Complex.conj_ofReal]
    rw [h0, Complex.exp_zero]
  · rw [← Complex.exp_conj, ← Complex.exp_add]
    have h0 : (starRingEnd ℂ) (-(Complex.I * (z : ℂ))) + -(Complex.I * (z : ℂ)) = 0 := by
      simp [Complex.conj_ofReal]
    rw [h0, Complex.exp_zero]

private theorem qubitZeroDiagPhase_mem_unitary {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) :
    qubitZeroDiagPhase hN θ ∈ unitary (Register N) := by
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  dsimp only [qubitZeroDiagPhase]
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  obtain ⟨hpos, hneg⟩ := conj_mul_exp_I_real θ
  constructor <;> ext x y <;> by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, Complex.star_def]
    cases x ⟨0, hN⟩ <;> [exact hpos; exact hneg]
  · simp [hxy]
  · subst hxy
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, Complex.star_def]
    cases x ⟨0, hN⟩ <;> [exact (mul_comm _ _).trans hpos; exact (mul_comm _ _).trans hneg]
  · simp [hxy]

private theorem qubitZeroDiagPhase_mem_circuitAtMost_one {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) :
    qubitZeroDiagPhase (by omega) θ ∈ phaseCircuitMatrixImageAtMost N 1 := by
  let i₀ : Fin N := ⟨0, by omega⟩
  let i₁ : Fin N := ⟨1, by omega⟩
  have hi01 : i₀ ≠ i₁ := fun h => by have hv : 0 = 1 := congrArg Fin.val h; omega
  let d4 : Bool × Bool → ℂ := fun p =>
    if p.1 then Complex.exp (-(Complex.I * (θ : ℂ))) else Complex.exp (Complex.I * (θ : ℂ))
  let B4 : Matrix (Bool × Bool) (Bool × Bool) ℂ := Matrix.diagonal d4
  have hB4_su : B4 ∈ Matrix.specialUnitaryGroup (Bool × Bool) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      dsimp only [B4]
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      obtain ⟨hpos, hneg⟩ := conj_mul_exp_I_real θ
      ext p q
      by_cases hpq : p = q
      · subst hpq
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, Complex.star_def, d4]
        cases p.1 <;> [exact hpos; exact hneg]
      · simp [hpq]
    · dsimp only [B4]
      rw [Matrix.det_diagonal, Fintype.prod_prod_type]
      simp only [Fintype.prod_bool, d4, ↓reduceIte, Bool.false_eq_true]
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      have h0 : -(Complex.I * ↑θ) + -(Complex.I * ↑θ) +
          (Complex.I * ↑θ + Complex.I * ↑θ) = 0 := by ring
      rw [h0, Complex.exp_zero]
  let C : TwoQubitCircuit N := TwoQubitCircuit.singleOn i₀ i₁ hi01 ⟨B4, hB4_su⟩
  have hC_len : C.gateCount ≤ 1 := le_rfl
  refine mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, C, hC_len, ?_⟩
  rw [one_smul]
  dsimp only [C]
  rw [TwoQubitCircuit.singleOn_eval]
  have hlift_mat : (twoQubitLift i₀ i₁ hi01 ⟨B4, hB4_su⟩ : Register N) =
      twoQubitLiftMatrix i₀ i₁ hi01 B4 := by
    ext x y
    simp [twoQubitLift, twoQubitLiftMatrix, specialUnitaryAsUnitary,
      unitaryGroupReindex_coe, Quantum.tensorGate_val, Matrix.reindex_apply, Matrix.kronecker]
  have hdiag_lift : twoQubitLiftMatrix i₀ i₁ hi01 B4 = qubitZeroDiagPhase (by omega) θ := by
    dsimp only [B4]
    ext x y
    by_cases hxy : x = y
    · subst hxy
      simp [twoQubitLiftMatrix, splitTwoQubitConfig, Matrix.kronecker, d4, qubitZeroDiagPhase, i₀]
    · rw [qubitZeroDiagPhase, Matrix.diagonal_apply_ne _ hxy]
      dsimp only [twoQubitLiftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [Equiv.symm_symm]
      let sx := splitTwoQubitConfig i₀ i₁ hi01 x
      let sy := splitTwoQubitConfig i₀ i₁ hi01 y
      change (Matrix.kroneckerMap (· * ·) (Matrix.diagonal d4) 1) sx sy = 0
      rw [Matrix.kroneckerMap_apply]
      by_cases hp : sx.1 = sy.1
      · have hrest_ne : sx.2 ≠ sy.2 := fun hr =>
          hxy ((splitTwoQubitConfig i₀ i₁ hi01).injective (Prod.ext hp hr))
        rw [Matrix.one_apply_ne hrest_ne, mul_zero]
      · rw [Matrix.diagonal_apply_ne _ hp, zero_mul]
  simp only [hlift_mat, hdiag_lift]

private def pauliXZeroWord {N : ℕ} (hN : 1 ≤ N) : Fin N → Option (Fin 3) :=
  fun s => if s = ⟨0, hN⟩ then some 0 else none

private theorem finitePauliMatrix_pureX_apply_loc {N : ℕ} (S : Fin N → Bool)
    (P : Fin N → Option (Fin 3)) (hP : ∀ s, P s = if S s then some 0 else none)
    (x y : Config N) :
    finitePauliMatrix P x y = if y = (fun s => xor (x s) (S s)) then 1 else 0 := by
  unfold finitePauliMatrix
  by_cases hy : y = fun s => xor (x s) (S s)
  · subst hy
    rw [if_pos rfl]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [hP s]
    dsimp only
    cases x s <;> cases S s <;>
      simp [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli, Matrix.one_apply]
  · rw [if_neg hy]
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hy
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    rw [hP s]
    cases hx : x s <;> cases hS : S s <;> cases hy_s : y s <;>
      simp_all [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli]

private theorem star_mul_self_conj_pauliX_diagZ {N : ℕ} (hN : 1 ≤ N) (α β u : ℝ) :
    let X₀ : Register N := finitePauliMatrix (pauliXZeroWord hN)
    let A_mat : Register N :=
      NormedSpace.exp (u • (-Complex.I • X₀)) * qubitZeroDiagPhase hN α *
        NormedSpace.exp (u • (Complex.I • X₀)) - qubitZeroDiagPhase hN β
    star A_mat * A_mat =
      ((2 - 2 * Real.cos α * Real.cos β - 2 * Real.sin α * Real.sin β * Real.cos (2 * u) : ℝ) : ℂ) •
        (1 : Register N) := by
  intro X₀ A_mat
  let i₀ : Fin N := ⟨0, hN⟩
  let Z₀ : Register N := Matrix.diagonal fun x : Config N => if x i₀ then (-1 : ℂ) else 1
  have hX₀_sq : X₀ * X₀ = 1 := finitePauliMatrix_mul_self (pauliXZeroWord hN)
  have hX₀_sa : IsSelfAdjoint X₀ := (finitePauliMatrix_isHermitian (pauliXZeroWord hN)).isSelfAdjoint
  have hZ₀_sq : Z₀ * Z₀ = 1 := by
    dsimp only [Z₀]; rw [Matrix.diagonal_mul_diagonal]
    ext x y; by_cases hxy : x = y
    · subst hxy; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]; cases x i₀ <;> norm_num
    · simp [hxy]
  have hZ₀_sa : star Z₀ = Z₀ := by
    ext x y
    by_cases hxy : x = y
    · subst hxy; simp [Z₀]; cases x i₀ <;> simp
    · simp [Z₀, hxy, Ne.symm hxy]
  have hXZ_anti : X₀ * Z₀ = -(Z₀ * X₀) := by
    have hX_apply := finitePauliMatrix_pureX_apply_loc (fun s : Fin N => decide (s = i₀))
      (pauliXZeroWord hN) (fun s => by
        dsimp [pauliXZeroWord, i₀]
        by_cases hs : s = ⟨0, hN⟩ <;> simp [hs])
    ext x y
    rw [Matrix.mul_diagonal, Matrix.neg_apply, Matrix.diagonal_mul]
    dsimp only [X₀]
    rw [hX_apply x y]
    by_cases hflip : y = fun s => xor (x s) (decide (s = i₀))
    · subst hflip
      simp only [↓reduceIte, decide_true, Bool.xor_true]
      cases x i₀ <;> norm_num
    · simp [hflip]
  have hphase_eq (θ : ℝ) : qubitZeroDiagPhase hN θ =
      (Real.cos θ : ℂ) • (1 : Register N) + (Complex.I * (Real.sin θ : ℂ)) • Z₀ := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      simp only [qubitZeroDiagPhase, Z₀, i₀, Matrix.diagonal_apply_eq, Matrix.add_apply,
        Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      cases x ⟨0, hN⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
        rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        ring
      · simp only [↓reduceIte]
        have heq : -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [heq, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Real.cos_neg, Real.sin_neg]
        push_cast; ring
    · simp [qubitZeroDiagPhase, Z₀, hxy]
  have hexp_m := exp_neg_I_smul_involution hX₀_sq u
  have hexp_p : NormedSpace.exp (u • (Complex.I • X₀)) =
      (Real.cos u : ℂ) • (1 : Register N) + (Complex.I * (Real.sin u : ℂ)) • X₀ := by
    have hm := exp_neg_I_smul_involution hX₀_sq (-u)
    have hsm : (-u) • (-Complex.I • X₀) = u • (Complex.I • X₀) := by
      ext x y; simp [Complex.real_smul]
    rw [hsm, Real.cos_neg, Real.sin_neg] at hm
    simpa [mul_neg] using hm
  have hconj_Z : NormedSpace.exp (u • (-Complex.I • X₀)) * Z₀ *
      NormedSpace.exp (u • (Complex.I • X₀)) =
      (Real.cos (2 * u) : ℂ) • Z₀ + (Complex.I * (Real.sin (2 * u) : ℂ)) • (Z₀ * X₀) := by
    rw [hexp_m, hexp_p]
    have hcomm_Z : ((Real.cos u : ℂ) • (1 : Register N) + (-Complex.I * (Real.sin u : ℂ)) • X₀) * Z₀ =
        Z₀ * ((Real.cos u : ℂ) • (1 : Register N) + (Complex.I * (Real.sin u : ℂ)) • X₀) := by
      rw [add_mul, mul_add, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
        smul_mul_assoc, hXZ_anti, mul_smul_comm, smul_neg, ← neg_smul, neg_mul, neg_neg]
    rw [hcomm_Z, mul_assoc]
    have hsq_exp : ((Real.cos u : ℂ) • (1 : Register N) + (Complex.I * (Real.sin u : ℂ)) • X₀) *
        ((Real.cos u : ℂ) • (1 : Register N) + (Complex.I * (Real.sin u : ℂ)) • X₀) =
        (Real.cos (2 * u) : ℂ) • (1 : Register N) + (Complex.I * (Real.sin (2 * u) : ℂ)) • X₀ := by
      rw [mul_add, add_mul, add_mul]
      simp only [smul_mul_smul_comm, one_mul, mul_one, hX₀_sq]
      have hcos2 : (Real.cos u : ℂ) * (Real.cos u : ℂ) +
          (Complex.I * (Real.sin u : ℂ)) * (Complex.I * (Real.sin u : ℂ)) = (Real.cos (2 * u) : ℂ) := by
        rw [Real.cos_two_mul' u, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_pow]
        linear_combination (Real.sin u : ℂ) ^ 2 * Complex.I_mul_I
      have hsin2 : (Real.cos u : ℂ) * (Complex.I * (Real.sin u : ℂ)) +
          (Complex.I * (Real.sin u : ℂ)) * (Real.cos u : ℂ) = Complex.I * (Real.sin (2 * u) : ℂ) := by
        rw [Real.sin_two_mul, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]; ring
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination ((1 : Register N) x y) * hcos2 + (X₀ x y) * hsin2
    rw [hsq_exp, mul_add, mul_smul_comm, mul_one, mul_smul_comm]
  have hexp_1 : NormedSpace.exp (u • (-Complex.I • X₀)) * (1 : Register N) *
      NormedSpace.exp (u • (Complex.I • X₀)) = 1 := by
    rw [mul_one, hexp_m, hexp_p, mul_add, add_mul, add_mul]
    simp only [smul_mul_smul_comm, one_mul, mul_one, hX₀_sq]
    have h1 : (Real.cos u : ℂ) * (Real.cos u : ℂ) +
        (-Complex.I * (Real.sin u : ℂ)) * (Complex.I * (Real.sin u : ℂ)) = 1 := by
      have hc2 : ((Real.cos u ^ 2 + Real.sin u ^ 2 : ℝ) : ℂ) = 1 := by
        rw [Real.cos_sq_add_sin_sq u, Complex.ofReal_one]
      rw [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_pow] at hc2
      linear_combination hc2 - (Real.sin u : ℂ) ^ 2 * Complex.I_mul_I
    ext x y
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination ((1 : Register N) x y) * h1
  let a₀ : ℝ := Real.cos α - Real.cos β
  let a₁ : ℝ := Real.sin α * Real.cos (2 * u) - Real.sin β
  let a₂ : ℝ := -Real.sin α * Real.sin (2 * u)
  let Y_alt : Register N := (-Complex.I) • (Z₀ * X₀)
  have hY_sa : star Y_alt = Y_alt := by
    dsimp only [Y_alt]
    rw [star_smul, star_mul, hX₀_sa.star_eq, hZ₀_sa, Complex.star_def, map_neg, Complex.conj_I,
      neg_neg, hXZ_anti, smul_neg, ← neg_smul]
  have hY_sq : Y_alt * Y_alt = 1 := by
    dsimp only [Y_alt]
    rw [smul_mul_smul_comm]
    have hZX : (Z₀ * X₀) * (Z₀ * X₀) = -1 := by
      calc (Z₀ * X₀) * (Z₀ * X₀) = Z₀ * (X₀ * Z₀) * X₀ := by simp only [mul_assoc]
        _ = Z₀ * (-(Z₀ * X₀)) * X₀ := by rw [hXZ_anti]
        _ = -((Z₀ * Z₀) * (X₀ * X₀)) := by simp only [mul_neg, neg_mul, mul_assoc]
        _ = -1 := by rw [hZ₀_sq, hX₀_sq, mul_one]
    have hI2 : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
    rw [hZX, hI2, smul_neg, neg_smul, neg_neg, one_smul]
  have hZY_anti : Z₀ * Y_alt + Y_alt * Z₀ = 0 := by
    dsimp only [Y_alt]
    rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc Z₀ Z₀ X₀, hZ₀_sq, one_mul,
      mul_assoc Z₀ X₀ Z₀, hXZ_anti, mul_neg, ← mul_assoc Z₀ Z₀ X₀, hZ₀_sq, one_mul,
      smul_neg, add_neg_cancel]
  have hA_decomp : A_mat = (a₀ : ℂ) • (1 : Register N) +
      (Complex.I * (a₁ : ℂ)) • Z₀ + (Complex.I * (a₂ : ℂ)) • Y_alt := by
    dsimp only [A_mat]
    rw [hphase_eq α, hphase_eq β, mul_add, add_mul]
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [hexp_1, hconj_Z]
    dsimp only [Y_alt, a₀, a₁, a₂]
    ext x y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hstarA_A : star A_mat * A_mat = ((a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 : ℝ) : ℂ) • (1 : Register N) := by
    let H_im : Register N := (a₁ : ℂ) • Z₀ + (a₂ : ℂ) • Y_alt
    have hH_sa : star H_im = H_im := by
      dsimp only [H_im]
      rw [star_add, star_smul, star_smul, hZ₀_sa, hY_sa, Complex.star_def,
        Complex.conj_ofReal, Complex.conj_ofReal]
    have hH_sq : H_im * H_im = ((a₁ ^ 2 + a₂ ^ 2 : ℝ) : ℂ) • (1 : Register N) := by
      dsimp only [H_im]
      rw [mul_add, add_mul, add_mul]
      simp only [smul_mul_smul_comm, hZ₀_sq, hY_sq]
      have hcross : ((a₁ : ℂ) * (a₂ : ℂ)) • (Z₀ * Y_alt) + ((a₂ : ℂ) * (a₁ : ℂ)) • (Y_alt * Z₀) = 0 := by
        rw [mul_comm (a₂ : ℂ) (a₁ : ℂ), ← smul_add, hZY_anti, smul_zero]
      ext x y
      have hcx := congrFun (congrFun hcross x) y
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hcx
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.ofReal_add, Complex.ofReal_pow]
      linear_combination hcx
    have hA_H : A_mat = (a₀ : ℂ) • (1 : Register N) + Complex.I • H_im := by
      rw [hA_decomp]; dsimp only [H_im]
      ext x y; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    have hstarA_H : star A_mat = (a₀ : ℂ) • (1 : Register N) - Complex.I • H_im := by
      rw [hA_H, star_add, star_smul, star_one, star_smul, hH_sa, Complex.star_def,
        Complex.conj_ofReal, Complex.conj_I, neg_smul, sub_eq_add_neg]
    rw [hstarA_H, hA_H, sub_mul, mul_add, mul_add]
    simp only [smul_mul_smul_comm, one_mul, mul_one, hH_sq, smul_smul, Complex.I_mul_I]
    ext x y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_pow]
    ring
  have hsum_sq : a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 =
      2 - 2 * Real.cos α * Real.cos β - 2 * Real.sin α * Real.sin β * Real.cos (2 * u) := by
    dsimp only [a₀, a₁, a₂]
    have hcα := Real.cos_sq_add_sin_sq α
    have hcβ := Real.cos_sq_add_sin_sq β
    have hc2u := Real.cos_sq_add_sin_sq (2 * u)
    linear_combination hcα + hcβ + (Real.sin α) ^ 2 * hc2u
  rwa [hsum_sq] at hstarA_A

private theorem norm_sq_conj_pauliX_diagZ {N : ℕ} (hN : 1 ≤ N) (α β u : ℝ) :
    let X₀ : Register N := finitePauliMatrix (pauliXZeroWord hN)
    ‖NormedSpace.exp (u • (-Complex.I • X₀)) * qubitZeroDiagPhase hN α *
      NormedSpace.exp (u • (Complex.I • X₀)) - qubitZeroDiagPhase hN β‖ ^ 2 =
      2 - 2 * Real.cos α * Real.cos β - 2 * Real.sin α * Real.sin β * Real.cos (2 * u) := by
  intro X₀
  let A_mat : Register N :=
    NormedSpace.exp (u • (-Complex.I • X₀)) * qubitZeroDiagPhase hN α *
      NormedSpace.exp (u • (Complex.I • X₀)) - qubitZeroDiagPhase hN β
  let rhs : ℝ := 2 - 2 * Real.cos α * Real.cos β - 2 * Real.sin α * Real.sin β * Real.cos (2 * u)
  have hstar := star_mul_self_conj_pauliX_diagZ hN α β u
  change star A_mat * A_mat = (rhs : ℂ) • (1 : Register N) at hstar
  have hrhs_nn : 0 ≤ rhs := by
    dsimp only [rhs]
    have hcα := Real.cos_sq_add_sin_sq α
    have hcβ := Real.cos_sq_add_sin_sq β
    have hc2u := Real.cos_sq_add_sin_sq (2 * u)
    have hsum : (Real.cos α - Real.cos β) ^ 2 +
        (Real.sin α * Real.cos (2 * u) - Real.sin β) ^ 2 +
        (-Real.sin α * Real.sin (2 * u)) ^ 2 =
        2 - 2 * Real.cos α * Real.cos β - 2 * Real.sin α * Real.sin β * Real.cos (2 * u) := by
      linear_combination hcα + hcβ + (Real.sin α) ^ 2 * hc2u
    rw [← hsum]; positivity
  have h1_norm : ‖(1 : Register N)‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Submonoid.one_mem (unitary (Register N)))
  have hcs := CStarRing.norm_star_mul_self (x := A_mat)
  rw [hstar, norm_smul, Complex.norm_real, Real.norm_of_nonneg hrhs_nn, h1_norm, mul_one] at hcs
  exact (sq _).trans hcs.symm

/-- Norm distance along the conjugation flow `u ↦ ‖exp(-i u K) U₀ exp(i u K) - W_star‖`. -/
def conjTargetDist {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (K U₀ W_star : A) (u : ℝ) : ℝ :=
  ‖NormedSpace.exp (u • (-Complex.I • K)) * U₀ *
    NormedSpace.exp (u • (Complex.I • K)) - W_star‖

/-- Explicit nearest-phase frozen-circuit saddle at exact height `1 / 10` (`N ≥ 2`) with `f'(0) = 0`
and **strictly positive** second derivative `f''(0) > 0` (`W_star ∈ phaseCircuitMatrixImageAtMost N 1`),
violating `IsStronglyConcaveOn c [-r, r] f` for every `c > 0` and `r > 0`. -/
theorem exists_frozenCircuit_tenth_pos_secondDeriv {N : ℕ} (hN : 2 ≤ N) :
    ∃ (U₀ W_star K : Register N) (κ : ℝ),
      U₀ ∈ unitary (Register N) ∧
      W_star ∈ phaseCircuitMatrixImageAtMost N 1 ∧
      IsSelfAdjoint K ∧ ‖K‖ = 1 ∧ 0 < κ ∧
      conjTargetDist K U₀ W_star 0 = 1 / 10 ∧
      HasDerivAt (conjTargetDist K U₀ W_star) 0 0 ∧
      HasDerivAt (deriv (conjTargetDist K U₀ W_star)) κ 0 ∧
      (∀ c > 0, ∀ r > 0, ¬ IsStronglyConcaveOn c (Icc (-r) r) (conjTargetDist K U₀ W_star)) := by
  let β : ℝ := Real.arcsin (1 / 20)
  let α : ℝ := 3 * β
  have hβ_pos : 0 < β := Real.arcsin_pos.mpr (by norm_num)
  have hβ_lt : β < Real.pi / 6 := by
    rw [← Real.arcsin_sin (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 6)
      (by linarith [Real.pi_pos] : Real.pi / 6 ≤ Real.pi / 2), Real.sin_pi_div_six]
    exact Real.arcsin_lt_arcsin (by norm_num) (by norm_num) (by norm_num)
  have hα_pos : 0 < α := by dsimp [α]; positivity
  have hα_lt : α < Real.pi / 2 := by dsimp [α]; linarith only [hβ_lt]
  have hsinβ_pos : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ_pos (by linarith [Real.pi_pos, hβ_lt])
  have hsinα_pos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα_pos (by linarith [Real.pi_pos, hα_lt])
  let U₀ : Register N := qubitZeroDiagPhase (by omega) α
  let W_star : Register N := qubitZeroDiagPhase (by omega) β
  let K : Register N := finitePauliMatrix (pauliXZeroWord (by omega))
  have hU₀_unit : U₀ ∈ unitary (Register N) := qubitZeroDiagPhase_mem_unitary (by omega) α
  have hW_mem : W_star ∈ phaseCircuitMatrixImageAtMost N 1 :=
    qubitZeroDiagPhase_mem_circuitAtMost_one hN β
  have hK_sa : IsSelfAdjoint K := (finitePauliMatrix_isHermitian _).isSelfAdjoint
  have hK_norm : ‖K‖ = 1 := by
    have hK_unit : K ∈ unitary (Register N) := by
      rw [Unitary.mem_iff, hK_sa.star_eq]
      have hsq := finitePauliMatrix_mul_self (pauliXZeroWord (N := N) (by omega))
      exact ⟨hsq, hsq⟩
    exact CStarRing.norm_of_mem_unitary hK_unit
  let g : ℝ → ℝ := fun u =>
    2 - 2 * Real.cos α * Real.cos β - 2 * Real.sin α * Real.sin β * Real.cos (2 * u)
  let f : ℝ → ℝ := conjTargetDist K U₀ W_star
  have hg0 : g 0 = (1 / 10 : ℝ) ^ 2 := by
    dsimp only [g]
    rw [mul_zero, Real.cos_zero, mul_one]
    have hsub : 2 - 2 * Real.cos α * Real.cos β - 2 * Real.sin α * Real.sin β =
        2 - 2 * Real.cos (α - β) := by rw [Real.cos_sub]; ring
    have hαβ : α - β = 2 * β := by dsimp [α]; ring
    have hcos2 : 2 - 2 * Real.cos (2 * β) = 4 * Real.sin β ^ 2 := by
      rw [Real.cos_two_mul']; have hc := Real.cos_sq_add_sin_sq β; linear_combination -2 * hc
    have hsinβ : Real.sin β = 1 / 20 := Real.sin_arcsin (by norm_num) (by norm_num)
    rw [hsub, hαβ, hcos2, hsinβ]; norm_num
  have hg_pos (u : ℝ) : 0 < g u := by
    have hcos_le : Real.cos (2 * u) ≤ 1 := Real.cos_le_one (2 * u)
    have hprod_pos : 0 < 2 * Real.sin α * Real.sin β := by positivity
    have hge : g 0 ≤ g u := by
      dsimp only [g]; rw [mul_zero, Real.cos_zero]
      nlinarith only [hcos_le, hprod_pos]
    linarith only [hg0, hge]
  have hf_eq (u : ℝ) : f u = Real.sqrt (g u) := by
    have hsq : f u ^ 2 = g u := norm_sq_conj_pauliX_diagZ (by omega) α β u
    have hnn : 0 ≤ f u := by dsimp [f, conjTargetDist]; exact norm_nonneg _
    rw [← Real.sqrt_sq hnn, hsq]
  have hf0 : f 0 = 1 / 10 := by rw [hf_eq 0, hg0, Real.sqrt_sq (by norm_num)]
  let g' : ℝ → ℝ := fun u => 4 * Real.sin α * Real.sin β * Real.sin (2 * u)
  have hg_deriv (u : ℝ) : HasDerivAt g (g' u) u := by
    dsimp only [g, g']
    have hd_cos : HasDerivAt (fun s : ℝ => Real.cos (2 * s)) (-Real.sin (2 * u) * 2) u := by
      have h2 : HasDerivAt (fun s : ℝ => 2 * s) 2 u :=
        ((hasDerivAt_id' u).const_mul 2).congr_deriv (mul_one 2)
      exact ((Real.hasDerivAt_cos (2 * u)).scomp u h2).congr_deriv (by simp [smul_eq_mul]; ring)
    have hd := (hasDerivAt_const u (2 - 2 * Real.cos α * Real.cos β)).sub
      (hd_cos.const_mul (2 * Real.sin α * Real.sin β))
    refine hd.congr_deriv ?_; ring
  let f' : ℝ → ℝ := fun u => g' u / (2 * Real.sqrt (g u))
  have hf_deriv (u : ℝ) : HasDerivAt f (f' u) u := by
    have hfn : f = fun s => Real.sqrt (g s) := funext hf_eq
    rw [hfn]
    exact (hg_deriv u).sqrt (hg_pos u).ne'
  have hderiv_f_eq : deriv f = f' := funext fun u => (hf_deriv u).deriv
  have hf'0 : HasDerivAt f 0 0 := by
    have h0 : f' 0 = 0 := by dsimp [f', g']; simp
    exact (hf_deriv 0).congr_deriv h0
  let κ : ℝ := 40 * Real.sin α * Real.sin β
  have hκ_pos : 0 < κ := by dsimp [κ]; positivity
  have hf''0 : HasDerivAt (deriv f) κ 0 := by
    rw [hderiv_f_eq]
    have hg'_d0 : HasDerivAt g' (8 * Real.sin α * Real.sin β) 0 := by
      dsimp only [g']
      have h2 : HasDerivAt (fun s : ℝ => 2 * s) 2 (0 : ℝ) :=
        ((hasDerivAt_id' (0 : ℝ)).const_mul 2).congr_deriv (mul_one 2)
      have hd_sin : HasDerivAt (fun s : ℝ => Real.sin (2 * s)) 2 0 :=
        ((Real.hasDerivAt_sin (2 * 0)).scomp 0 h2).congr_deriv
          (by rw [mul_zero, Real.cos_zero, smul_eq_mul, mul_one])
      refine (hd_sin.const_mul (4 * Real.sin α * Real.sin β)).congr_deriv ?_
      ring
    have hden_d0 : HasDerivAt (fun u : ℝ => 2 * Real.sqrt (g u)) 0 0 := by
      have hd := ((hg_deriv 0).sqrt (hg_pos 0).ne').const_mul 2
      refine hd.congr_deriv ?_
      dsimp [g']; simp
    have hden0 : 2 * Real.sqrt (g 0) = 1 / 5 := by
      rw [hg0, Real.sqrt_sq (by norm_num)]; norm_num
    have hquot := hg'_d0.div hden_d0 (by rw [hden0]; norm_num)
    refine hquot.congr_deriv ?_
    dsimp [κ]
    rw [hden0]
    ring
  refine ⟨U₀, W_star, K, κ, hU₀_unit, hW_mem, hK_sa, hK_norm, hκ_pos, hf0, hf'0, hf''0, ?_⟩
  intro c hc r hr hstr
  let u₀ : ℝ := min r (Real.pi / 4)
  have hu₀_pos : 0 < u₀ := lt_min hr (by positivity)
  have hu₀_r : u₀ ≤ r := min_le_left _ _
  have hcos_lt1 : Real.cos (2 * u₀) < 1 := by
    have h2u_pos : 0 < 2 * u₀ := by positivity
    have h2u_le : 2 * u₀ ≤ Real.pi / 2 := by
      have hle : u₀ ≤ Real.pi / 4 := min_le_right _ _
      linarith only [hle]
    rw [← Real.cos_zero]
    exact Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
      ⟨h2u_pos.le, by linarith [Real.pi_pos, h2u_le]⟩ h2u_pos
  have hgu_gt : g 0 < g u₀ := by
    dsimp only [g]
    rw [mul_zero, Real.cos_zero]
    have hprod_pos : 0 < 2 * Real.sin α * Real.sin β := by positivity
    nlinarith only [hcos_lt1, hprod_pos]
  have hfu_gt : f 0 < f u₀ := by
    rw [hf_eq 0, hf_eq u₀]
    exact Real.sqrt_lt_sqrt (hg_pos 0).le hgu_gt
  have hf_even : f (-u₀) = f u₀ := by
    rw [hf_eq (-u₀), hf_eq u₀]
    congr 1; dsimp only [g]; rw [mul_neg, Real.cos_neg]
  have hu₀_mem : u₀ ∈ Icc (-r) r := ⟨by linarith only [hu₀_pos, hr], hu₀_r⟩
  have hnu₀_mem : -u₀ ∈ Icc (-r) r := ⟨by linarith only [hu₀_r], by linarith only [hu₀_pos, hr]⟩
  have hmid := @hstr.2 u₀ hu₀_mem (-u₀) hnu₀_mem (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  change (1 / 2 : ℝ) * f u₀ + (1 / 2) * f (-u₀) +
    (c / 2) * (1 / 2) * (1 / 2) * (u₀ - -u₀) ^ 2 ≤ f ((1 / 2 : ℝ) * u₀ + (1 / 2) * (-u₀)) at hmid
  have h0_eq : (1 / 2 : ℝ) * u₀ + (1 / 2 : ℝ) * (-u₀) = 0 := by ring
  rw [h0_eq, hf_even] at hmid
  have hquad_pos : 0 < (c / 2) * (1 / 2) * (1 / 2) * (u₀ - -u₀) ^ 2 := by
    have hsub : u₀ - -u₀ = 2 * u₀ := by ring
    rw [hsub]; positivity
  linarith only [hmid, hfu_gt, hquad_pos]

private def qubitOneProjFalse {N : ℕ} (hN : 2 ≤ N) : Register N :=
  Matrix.diagonal fun x : Config N => if x ⟨1, hN⟩ then 0 else 1

private def qubitOneProjTrue {N : ℕ} (hN : 2 ≤ N) : Register N :=
  Matrix.diagonal fun x : Config N => if x ⟨1, hN⟩ then 1 else 0

private theorem qubitOneProj_props {N : ℕ} (hN : 2 ≤ N) :
    qubitOneProjFalse hN + qubitOneProjTrue hN = 1 ∧
    qubitOneProjFalse hN * qubitOneProjFalse hN = qubitOneProjFalse hN ∧
    qubitOneProjTrue hN * qubitOneProjTrue hN = qubitOneProjTrue hN ∧
    qubitOneProjFalse hN * qubitOneProjTrue hN = 0 ∧
    qubitOneProjTrue hN * qubitOneProjFalse hN = 0 ∧
    star (qubitOneProjFalse hN) = qubitOneProjFalse hN ∧
    star (qubitOneProjTrue hN) = qubitOneProjTrue hN := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x y
    by_cases hxy : x = y
    · subst hxy; simp [qubitOneProjFalse, qubitOneProjTrue]; cases x ⟨1, hN⟩ <;> simp
    · simp [qubitOneProjFalse, qubitOneProjTrue, hxy]
  · dsimp [qubitOneProjFalse]; rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext x; cases x ⟨1, hN⟩ <;> simp
  · dsimp [qubitOneProjTrue]; rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext x; cases x ⟨1, hN⟩ <;> simp
  · dsimp [qubitOneProjFalse, qubitOneProjTrue]; rw [Matrix.diagonal_mul_diagonal]
    ext x y; by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]
  · dsimp [qubitOneProjFalse, qubitOneProjTrue]; rw [Matrix.diagonal_mul_diagonal]
    ext x y; by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]
  · ext x y; by_cases hxy : x = y
    · subst hxy; simp [qubitOneProjFalse]
    · simp [qubitOneProjFalse, hxy, Ne.symm hxy]
  · ext x y; by_cases hxy : x = y
    · subst hxy; simp [qubitOneProjTrue]
    · simp [qubitOneProjTrue, hxy, Ne.symm hxy]

/-- Exact block operator norm across orthogonal qubit-`1` projections when `D₀, D₁` are scalar
isometries up to `c₀, c₁ ≥ 0` (`star D_b * D_b = c_b^2 • 1`) commuting with `P_b`. -/
private theorem opNorm_qubitOneBlockSum_eq_max {N : ℕ} (hN : 2 ≤ N)
    {D₀ D₁ : Register N} {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hD₀_n : ‖D₀‖ = c₀) (hD₁_n : ‖D₁‖ = c₁)
    (hcomm₀ : D₀ * qubitOneProjFalse hN = qubitOneProjFalse hN * D₀)
    (hcomm₁ : D₁ * qubitOneProjTrue hN = qubitOneProjTrue hN * D₁)
    (hstar₀ : star D₀ * D₀ = ((c₀ ^ 2 : ℝ) : ℂ) • (1 : Register N))
    (hstar₁ : star D₁ * D₁ = ((c₁ ^ 2 : ℝ) : ℂ) • (1 : Register N)) :
    ‖D₀ * qubitOneProjFalse hN + D₁ * qubitOneProjTrue hN‖ = max c₀ c₁ := by
  obtain ⟨_, hP₀_sq, hP₁_sq, _, _, _, _⟩ := qubitOneProj_props hN
  let P₀ := qubitOneProjFalse hN
  let P₁ := qubitOneProjTrue hN
  apply le_antisymm
  · rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left hc₀) fun ψ => ?_
    let e_eucl := EuclideanSpace.equiv (Config N) ℂ
    let ψ₀ : EuclideanSpace ℂ (Config N) := e_eucl.symm (P₀ *ᵥ ψ.ofLp)
    let ψ₁ : EuclideanSpace ℂ (Config N) := e_eucl.symm (P₁ *ᵥ ψ.ofLp)
    let v₀ : Config N → ℂ := D₀ *ᵥ ψ₀.ofLp
    let v₁ : Config N → ℂ := D₁ *ᵥ ψ₁.ofLp
    let η : EuclideanSpace ℂ (Config N) := e_eucl.symm (P₀ *ᵥ v₀ + P₁ *ᵥ v₁)
    let η₀ : EuclideanSpace ℂ (Config N) := e_eucl.symm (P₀ *ᵥ v₀)
    let η₁ : EuclideanSpace ℂ (Config N) := e_eucl.symm (P₁ *ᵥ v₁)
    have hact_eq :
        ((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (D₀ * P₀ + D₁ * P₁)) ψ = η := by
      change e_eucl.symm ((D₀ * P₀ + D₁ * P₁) *ᵥ ψ.ofLp) = η
      dsimp only [η]
      congr 1
      rw [Matrix.add_mulVec]
      have h0 : (D₀ * P₀) *ᵥ ψ.ofLp = P₀ *ᵥ v₀ := by
        dsimp only [v₀, ψ₀]
        change (D₀ * P₀) *ᵥ ψ.ofLp = P₀ *ᵥ (D₀ *ᵥ (P₀ *ᵥ ψ.ofLp))
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hcomm₀, mul_assoc D₀ P₀ P₀, hP₀_sq]
      have h1 : (D₁ * P₁) *ᵥ ψ.ofLp = P₁ *ᵥ v₁ := by
        dsimp only [v₁, ψ₁]
        change (D₁ * P₁) *ᵥ ψ.ofLp = P₁ *ᵥ (D₁ *ᵥ (P₁ *ᵥ ψ.ofLp))
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hcomm₁, mul_assoc D₁ P₁ P₁, hP₁_sq]
      rw [h0, h1]
    have hη_pyth : ‖η‖ ^ 2 = ‖η₀‖ ^ 2 + ‖η₁‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      change ‖(P₀ *ᵥ v₀ + P₁ *ᵥ v₁) x‖ ^ 2 = ‖(P₀ *ᵥ v₀) x‖ ^ 2 + ‖(P₁ *ᵥ v₁) x‖ ^ 2
      simp only [Pi.add_apply, P₀, P₁, qubitOneProjFalse, qubitOneProjTrue, Matrix.mulVec_diagonal]
      cases x ⟨1, hN⟩ <;> simp
    have hψ_pyth : ‖ψ₀‖ ^ 2 + ‖ψ₁‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      change ‖(P₀ *ᵥ ψ.ofLp) x‖ ^ 2 + ‖(P₁ *ᵥ ψ.ofLp) x‖ ^ 2 = ‖ψ.ofLp x‖ ^ 2
      simp only [P₀, P₁, qubitOneProjFalse, qubitOneProjTrue, Matrix.mulVec_diagonal]
      cases x ⟨1, hN⟩ <;> simp
    have hP₀_contr : ‖η₀‖ ≤ ‖e_eucl.symm v₀‖ := by
      have hsq : ‖η₀‖ ^ 2 ≤ ‖e_eucl.symm v₀‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        refine Finset.sum_le_sum fun x _ => ?_
        change ‖(P₀ *ᵥ v₀) x‖ ^ 2 ≤ ‖v₀ x‖ ^ 2
        simp only [P₀, qubitOneProjFalse, Matrix.mulVec_diagonal]
        cases x ⟨1, hN⟩ <;> simp
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    have hP₁_contr : ‖η₁‖ ≤ ‖e_eucl.symm v₁‖ := by
      have hsq : ‖η₁‖ ^ 2 ≤ ‖e_eucl.symm v₁‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        refine Finset.sum_le_sum fun x _ => ?_
        change ‖(P₁ *ᵥ v₁) x‖ ^ 2 ≤ ‖v₁ x‖ ^ 2
        simp only [P₁, qubitOneProjTrue, Matrix.mulVec_diagonal]
        cases x ⟨1, hN⟩ <;> simp
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    have hη₀_le : ‖η₀‖ ≤ max c₀ c₁ * ‖ψ₀‖ := by
      have hmv := Matrix.l2_opNorm_mulVec D₀ ψ₀
      rw [hD₀_n] at hmv
      exact hP₀_contr.trans (hmv.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    have hη₁_le : ‖η₁‖ ≤ max c₀ c₁ * ‖ψ₁‖ := by
      have hmv := Matrix.l2_opNorm_mulVec D₁ ψ₁
      rw [hD₁_n] at hmv
      exact hP₁_contr.trans (hmv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
    have hsq_tot : ‖η‖ ^ 2 ≤ (max c₀ c₁ * ‖ψ‖) ^ 2 := by
      have h0s := pow_le_pow_left₀ (norm_nonneg _) hη₀_le 2
      have h1s := pow_le_pow_left₀ (norm_nonneg _) hη₁_le 2
      rw [hη_pyth, mul_pow, ← hψ_pyth, mul_add]
      rw [mul_pow] at h0s h1s
      linarith only [h0s, h1s]
    rw [hact_eq]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (le_max_of_le_left hc₀) (norm_nonneg ψ))).mp hsq_tot
  · have hcol_norm_sq (D : Register N) (c : ℝ)
        (hst : star D * D = ((c ^ 2 : ℝ) : ℂ) • (1 : Register N)) (x₀ : Config N) :
        ‖(EuclideanSpace.equiv (Config N) ℂ).symm (D *ᵥ (PiLp.single 2 x₀ (1 : ℂ)).ofLp)‖ ^ 2 = c ^ 2 := by
      let e₀ : EuclideanSpace ℂ (Config N) := PiLp.single 2 x₀ 1
      let y₀ : EuclideanSpace ℂ (Config N) := (EuclideanSpace.equiv (Config N) ℂ).symm (D *ᵥ e₀.ofLp)
      have h1 : ((‖y₀‖ ^ 2 : ℝ) : ℂ) = inner ℂ y₀ y₀ := by
        rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]; rfl
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
      have hdot : y₀.ofLp ⬝ᵥ star y₀.ofLp = (star D * D) x₀ x₀ := by
        change (D *ᵥ e₀.ofLp) ⬝ᵥ star (D *ᵥ e₀.ofLp) = _
        have hcol (x : Config N) : (D *ᵥ e₀.ofLp) x = D x x₀ := by
          simp [Matrix.mulVec, dotProduct, e₀, PiLp.single_apply]
        unfold dotProduct
        rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Pi.star_apply, hcol x, Matrix.conjTranspose_apply, mul_comm]
      rw [hdot, hst, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
      exact_mod_cast h1
    have hlow₀ : c₀ ≤ ‖D₀ * P₀ + D₁ * P₁‖ := by
      let x_f : Config N := fun _ => false
      let e_f : EuclideanSpace ℂ (Config N) := PiLp.single 2 x_f 1
      have hef_n : ‖e_f‖ = 1 := by simp [e_f]
      have hP₀_ef : P₀ *ᵥ e_f.ofLp = e_f.ofLp := by
        funext x; simp only [P₀, qubitOneProjFalse, Matrix.mulVec_diagonal]
        by_cases hx : x = x_f
        · subst hx; simp [e_f, x_f]
        · simp [e_f, hx]
      have hP₁_ef : P₁ *ᵥ e_f.ofLp = 0 := by
        funext x; simp only [P₁, qubitOneProjTrue, Matrix.mulVec_diagonal]
        by_cases hx : x = x_f
        · subst hx; simp [e_f, x_f]
        · simp [e_f, hx]
      have hact := Matrix.l2_opNorm_mulVec (D₀ * P₀ + D₁ * P₁) e_f
      rw [hef_n, mul_one, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hP₀_ef, hP₁_ef, Matrix.mulVec_zero, add_zero] at hact
      have hy_sq := hcol_norm_sq D₀ c₀ hstar₀ x_f
      have hy_eq : ‖(EuclideanSpace.equiv (Config N) ℂ).symm (D₀ *ᵥ e_f.ofLp)‖ = c₀ := by
        nlinarith only [hy_sq, norm_nonneg ((EuclideanSpace.equiv (Config N) ℂ).symm (D₀ *ᵥ e_f.ofLp)),
          hc₀, sq_nonneg (‖(EuclideanSpace.equiv (Config N) ℂ).symm (D₀ *ᵥ e_f.ofLp)‖ - c₀)]
      rwa [hy_eq] at hact
    have hlow₁ : c₁ ≤ ‖D₀ * P₀ + D₁ * P₁‖ := by
      let x_t : Config N := fun s => decide (s = ⟨1, hN⟩)
      let e_t : EuclideanSpace ℂ (Config N) := PiLp.single 2 x_t 1
      have het_n : ‖e_t‖ = 1 := by simp [e_t]
      have hP₀_et : P₀ *ᵥ e_t.ofLp = 0 := by
        funext x; simp only [P₀, qubitOneProjFalse, Matrix.mulVec_diagonal]
        by_cases hx : x = x_t
        · subst hx; simp [e_t, x_t]
        · simp [e_t, hx]
      have hP₁_et : P₁ *ᵥ e_t.ofLp = e_t.ofLp := by
        funext x; simp only [P₁, qubitOneProjTrue, Matrix.mulVec_diagonal]
        by_cases hx : x = x_t
        · subst hx; simp [e_t, x_t]
        · simp [e_t, hx]
      have hact := Matrix.l2_opNorm_mulVec (D₀ * P₀ + D₁ * P₁) e_t
      rw [het_n, mul_one, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hP₀_et, hP₁_et, Matrix.mulVec_zero, zero_add] at hact
      have hy_sq := hcol_norm_sq D₁ c₁ hstar₁ x_t
      have hy_eq : ‖(EuclideanSpace.equiv (Config N) ℂ).symm (D₁ *ᵥ e_t.ofLp)‖ = c₁ := by
        nlinarith only [hy_sq, norm_nonneg ((EuclideanSpace.equiv (Config N) ℂ).symm (D₁ *ᵥ e_t.ofLp)),
          hc₁, sq_nonneg (‖(EuclideanSpace.equiv (Config N) ℂ).symm (D₁ *ᵥ e_t.ofLp)‖ - c₁)]
      rwa [hy_eq] at hact
    exact max_le hlow₀ hlow₁

/-- Explicit degenerate `2`-qubit frozen-circuit saddle at exact height `1 / 10` (`N ≥ 2`) with an
upward linear V-kink `f(u) = 2 * sin(v₀ + |u|)` near `0`, violating concavity of
`u ↦ f u - C * u^2` on `[-r, r]` for **every** `C ∈ ℝ` (positive or negative) and every `r > 0`. -/
theorem exists_frozenCircuit_tenth_upward_vKink {N : ℕ} (hN : 2 ≤ N) :
    ∃ (U₀ W_star K : Register N),
      U₀ ∈ unitary (Register N) ∧
      W_star ∈ phaseCircuitMatrixImageAtMost N 1 ∧
      IsSelfAdjoint K ∧ ‖K‖ = 1 ∧
      conjTargetDist K U₀ W_star 0 = 1 / 10 ∧
      ∀ (C : ℝ) {r : ℝ}, 0 < r →
        ¬ ConcaveOn ℝ (Icc (-r) r) (fun u => conjTargetDist K U₀ W_star u - C * u ^ 2) := by
  let i₀ : Fin N := ⟨0, by omega⟩
  let i₁ : Fin N := ⟨1, hN⟩
  have hi01 : i₀ ≠ i₁ := fun h => by have hv : 0 = 1 := congrArg Fin.val h; omega
  let v₀ : ℝ := Real.arcsin (1 / 20)
  have hv₀_pos : 0 < v₀ := Real.arcsin_pos.mpr (by norm_num)
  have hv₀_lt : v₀ < Real.pi / 6 := by
    rw [← Real.arcsin_sin (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 6)
      (by linarith [Real.pi_pos] : Real.pi / 6 ≤ Real.pi / 2), Real.sin_pi_div_six]
    exact Real.arcsin_lt_arcsin (by norm_num) (by norm_num) (by norm_num)
  have hsin_v₀ : Real.sin v₀ = 1 / 20 := Real.sin_arcsin (by norm_num) (by norm_num)
  let K : Register N := finitePauliMatrix (pauliXZeroWord (by omega))
  have hK_sa : IsSelfAdjoint K := (finitePauliMatrix_isHermitian _).isSelfAdjoint
  have hK_sq : K * K = 1 := finitePauliMatrix_mul_self _
  have hK_unit : K ∈ unitary (Register N) := by
    rw [Unitary.mem_iff, hK_sa.star_eq]; exact ⟨hK_sq, hK_sq⟩
  have hK_norm : ‖K‖ = 1 := CStarRing.norm_of_mem_unitary hK_unit
  let W_star : Register N := qubitZeroDiagPhase (by omega) (Real.pi / 2)
  have hW_mem : W_star ∈ phaseCircuitMatrixImageAtMost N 1 :=
    qubitZeroDiagPhase_mem_circuitAtMost_one hN (Real.pi / 2)
  have hW_unit : W_star ∈ unitary (Register N) :=
    qubitZeroDiagPhase_mem_unitary (by omega) (Real.pi / 2)
  obtain ⟨hP_sum, hP₀_sq, hP₁_sq, hP₀₁_01, hP₀₁_10, hP₀_sa, hP₁_sa⟩ := qubitOneProj_props hN
  let P₀ : Register N := qubitOneProjFalse hN
  let P₁ : Register N := qubitOneProjTrue hN
  have hK_comm_diag (d_b : Bool → ℂ) :
      K * Matrix.diagonal (fun x : Config N => d_b (x i₁)) =
        Matrix.diagonal (fun x : Config N => d_b (x i₁)) * K := by
    have hX_apply := finitePauliMatrix_pureX_apply_loc (fun s : Fin N => decide (s = i₀))
      (pauliXZeroWord (by omega)) (fun s => by
        dsimp [pauliXZeroWord, i₀]
        by_cases hs : s = ⟨0, by omega⟩ <;> simp [hs])
    ext x y
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    dsimp only [K]
    rw [hX_apply x y]
    by_cases hflip : y = fun s => xor (x s) (decide (s = i₀))
    · subst hflip
      simp only [↓reduceIte, decide_eq_false hi01.symm, Bool.xor_false]
      ring
    · simp [hflip]
  have hKP₀ : K * P₀ = P₀ * K := hK_comm_diag (fun b => if b then 0 else 1)
  have hKP₁ : K * P₁ = P₁ * K := hK_comm_diag (fun b => if b then 1 else 0)
  have hWP₀ : W_star * P₀ = P₀ * W_star := by
    dsimp [W_star, qubitZeroDiagPhase, P₀, qubitOneProjFalse]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext x; ring
  have hWP₁ : W_star * P₁ = P₁ * W_star := by
    dsimp [W_star, qubitZeroDiagPhase, P₁, qubitOneProjTrue]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext x; ring
  let E_m (v : ℝ) : Register N := NormedSpace.exp (v • (-Complex.I • K))
  let E_p (v : ℝ) : Register N := NormedSpace.exp (v • (Complex.I • K))
  have hEm_eq (v : ℝ) : E_m v =
      (Real.cos v : ℂ) • (1 : Register N) + (-Complex.I * (Real.sin v : ℂ)) • K :=
    exp_neg_I_smul_involution hK_sq v
  have hEp_eq (v : ℝ) : E_p v = E_m (-v) := by
    dsimp only [E_p, E_m]
    congr 1
    ext x y; simp [Complex.real_smul]
  have hEm_comm_P₀ (v : ℝ) : E_m v * P₀ = P₀ * E_m v := by
    rw [hEm_eq v, add_mul, mul_add, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
      smul_mul_assoc, hKP₀, mul_smul_comm]
  have hEm_comm_P₁ (v : ℝ) : E_m v * P₁ = P₁ * E_m v := by
    rw [hEm_eq v, add_mul, mul_add, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
      smul_mul_assoc, hKP₁, mul_smul_comm]
  have hEp_comm_P₀ (v : ℝ) : E_p v * P₀ = P₀ * E_p v := by rw [hEp_eq]; exact hEm_comm_P₀ (-v)
  have hEp_comm_P₁ (v : ℝ) : E_p v * P₁ = P₁ * E_p v := by rw [hEp_eq]; exact hEm_comm_P₁ (-v)
  have hEm_add (u v : ℝ) : E_m u * E_m v = E_m (u + v) := by
    letI : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _
    dsimp only [E_m]
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl (-Complex.I • K)).smul_left u |>.smul_right v),
      ← add_smul]
  have hEp_add (u v : ℝ) : E_p v * E_p u = E_p (u + v) := by
    letI : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _
    dsimp only [E_p]
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl (Complex.I • K)).smul_left v |>.smul_right u),
      ← add_smul, add_comm v u]
  let B (v : ℝ) : Register N := E_m v * W_star * E_p v
  have hB_unit (v : ℝ) : B v ∈ unitary (Register N) := by
    letI : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _
    have hXm : -Complex.I • K ∈ skewAdjoint (Register N) := by
      rw [skewAdjoint.mem_iff, star_smul, star_neg, Complex.star_def, Complex.conj_I, neg_neg,
        hK_sa.star_eq, neg_smul, neg_neg]
    have hXp : Complex.I • K ∈ skewAdjoint (Register N) := by
      rw [skewAdjoint.mem_iff, star_smul, Complex.star_def, Complex.conj_I, hK_sa.star_eq, neg_smul]
    exact mul_mem (mul_mem (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem v hXm)) hW_unit)
      (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem v hXp))
  have hB_comm_P₀ (v : ℝ) : B v * P₀ = P₀ * B v := by
    dsimp only [B]
    calc E_m v * W_star * E_p v * P₀
        = E_m v * W_star * (E_p v * P₀) := by rw [mul_assoc]
      _ = E_m v * (W_star * P₀) * E_p v := by rw [hEp_comm_P₀]; simp only [mul_assoc]
      _ = (E_m v * P₀) * W_star * E_p v := by rw [hWP₀]; simp only [mul_assoc]
      _ = P₀ * (E_m v * W_star * E_p v) := by rw [hEm_comm_P₀]; simp only [mul_assoc]
  have hB_comm_P₁ (v : ℝ) : B v * P₁ = P₁ * B v := by
    dsimp only [B]
    calc E_m v * W_star * E_p v * P₁
        = E_m v * W_star * (E_p v * P₁) := by rw [mul_assoc]
      _ = E_m v * (W_star * P₁) * E_p v := by rw [hEp_comm_P₁]; simp only [mul_assoc]
      _ = (E_m v * P₁) * W_star * E_p v := by rw [hWP₁]; simp only [mul_assoc]
      _ = P₁ * (E_m v * W_star * E_p v) := by rw [hEm_comm_P₁]; simp only [mul_assoc]
  let U₀ : Register N := B v₀ * P₀ + B (-v₀) * P₁
  have hU₀_unit : U₀ ∈ unitary (Register N) := by
    rw [Unitary.mem_iff]
    have hstP₀ (v : ℝ) : star (B v * P₀) = P₀ * star (B v) := by
      rw [star_mul (B v) P₀, hP₀_sa]
    have hstP₁ (v : ℝ) : star (B v * P₁) = P₁ * star (B v) := by
      rw [star_mul (B v) P₁, hP₁_sa]
    have hstB_P₀ (v : ℝ) : star (B v) * P₀ = P₀ * star (B v) := by
      have h := congrArg star (hB_comm_P₀ v)
      rw [star_mul (B v) P₀, star_mul P₀ (B v), hP₀_sa] at h
      exact h.symm
    have hstB_P₁ (v : ℝ) : star (B v) * P₁ = P₁ * star (B v) := by
      have h := congrArg star (hB_comm_P₁ v)
      rw [star_mul (B v) P₁, star_mul P₁ (B v), hP₁_sa] at h
      exact h.symm
    constructor
    · dsimp only [U₀]
      rw [star_add, hstP₀, hstP₁, add_mul, mul_add, mul_add]
      have h00 : P₀ * star (B v₀) * (B v₀ * P₀) = P₀ := by
        calc P₀ * star (B v₀) * (B v₀ * P₀)
            = P₀ * (star (B v₀) * B v₀) * P₀ := by simp only [mul_assoc]
          _ = P₀ * P₀ := by rw [(Unitary.mem_iff.mp (hB_unit v₀)).1, mul_one]
          _ = P₀ := hP₀_sq
      have h11 : P₁ * star (B (-v₀)) * (B (-v₀) * P₁) = P₁ := by
        calc P₁ * star (B (-v₀)) * (B (-v₀) * P₁)
            = P₁ * (star (B (-v₀)) * B (-v₀)) * P₁ := by simp only [mul_assoc]
          _ = P₁ * P₁ := by rw [(Unitary.mem_iff.mp (hB_unit (-v₀))).1, mul_one]
          _ = P₁ := hP₁_sq
      have h01 : P₀ * star (B v₀) * (B (-v₀) * P₁) = 0 := by
        calc P₀ * star (B v₀) * (B (-v₀) * P₁)
            = P₀ * star (B v₀) * (P₁ * B (-v₀)) := by rw [hB_comm_P₁]
          _ = P₀ * (star (B v₀) * P₁) * B (-v₀) := by simp only [mul_assoc]
          _ = (P₀ * P₁) * star (B v₀) * B (-v₀) := by rw [hstB_P₁]; simp only [mul_assoc]
          _ = 0 := by rw [hP₀₁_01, zero_mul, zero_mul]
      have h10 : P₁ * star (B (-v₀)) * (B v₀ * P₀) = 0 := by
        calc P₁ * star (B (-v₀)) * (B v₀ * P₀)
            = P₁ * star (B (-v₀)) * (P₀ * B v₀) := by rw [hB_comm_P₀]
          _ = P₁ * (star (B (-v₀)) * P₀) * B v₀ := by simp only [mul_assoc]
          _ = (P₁ * P₀) * star (B (-v₀)) * B v₀ := by rw [hstB_P₀]; simp only [mul_assoc]
          _ = 0 := by rw [hP₀₁_10, zero_mul, zero_mul]
      rw [h00, h01, h10, h11, add_zero, zero_add, hP_sum]
    · dsimp only [U₀]
      rw [star_add, hstP₀, hstP₁, add_mul, mul_add, mul_add]
      have h00 : B v₀ * P₀ * (P₀ * star (B v₀)) = P₀ := by
        calc B v₀ * P₀ * (P₀ * star (B v₀))
            = B v₀ * (P₀ * P₀) * star (B v₀) := by simp only [mul_assoc]
          _ = P₀ * (B v₀ * star (B v₀)) := by rw [hP₀_sq, hB_comm_P₀, mul_assoc]
          _ = P₀ := by rw [(Unitary.mem_iff.mp (hB_unit v₀)).2, mul_one]
      have h11 : B (-v₀) * P₁ * (P₁ * star (B (-v₀))) = P₁ := by
        calc B (-v₀) * P₁ * (P₁ * star (B (-v₀)))
            = B (-v₀) * (P₁ * P₁) * star (B (-v₀)) := by simp only [mul_assoc]
          _ = P₁ * (B (-v₀) * star (B (-v₀))) := by rw [hP₁_sq, hB_comm_P₁, mul_assoc]
          _ = P₁ := by rw [(Unitary.mem_iff.mp (hB_unit (-v₀))).2, mul_one]
      have h01 : B v₀ * P₀ * (P₁ * star (B (-v₀))) = 0 := by
        calc B v₀ * P₀ * (P₁ * star (B (-v₀)))
            = B v₀ * (P₀ * P₁) * star (B (-v₀)) := by simp only [mul_assoc]
          _ = 0 := by rw [hP₀₁_01, mul_zero, zero_mul]
      have h10 : B (-v₀) * P₁ * (P₀ * star (B v₀)) = 0 := by
        calc B (-v₀) * P₁ * (P₀ * star (B v₀))
            = B (-v₀) * (P₁ * P₀) * star (B v₀) := by simp only [mul_assoc]
          _ = 0 := by rw [hP₀₁_10, mul_zero, zero_mul]
      rw [h00, h01, h10, h11, add_zero, zero_add, hP_sum]
  have hflow_decomp (u : ℝ) :
      E_m u * U₀ * E_p u - W_star =
        (B (u + v₀) - W_star) * P₀ + (B (u - v₀) - W_star) * P₁ := by
    have hB_shift (v : ℝ) : E_m u * (B v * P₀) * E_p u = B (u + v) * P₀ := by
      dsimp only [B]
      calc E_m u * (E_m v * W_star * E_p v * P₀) * E_p u
          = (E_m u * E_m v) * W_star * E_p v * (P₀ * E_p u) := by simp only [mul_assoc]
        _ = E_m (u + v) * W_star * (E_p v * E_p u) * P₀ := by
            rw [hEm_add, ← hEp_comm_P₀ u]; simp only [mul_assoc]
        _ = B (u + v) * P₀ := by rw [hEp_add]
    have hB_shift1 (v : ℝ) : E_m u * (B v * P₁) * E_p u = B (u + v) * P₁ := by
      dsimp only [B]
      calc E_m u * (E_m v * W_star * E_p v * P₁) * E_p u
          = (E_m u * E_m v) * W_star * E_p v * (P₁ * E_p u) := by simp only [mul_assoc]
        _ = E_m (u + v) * W_star * (E_p v * E_p u) * P₁ := by
            rw [hEm_add, ← hEp_comm_P₁ u]; simp only [mul_assoc]
        _ = B (u + v) * P₁ := by rw [hEp_add]
    have hW_split : W_star = W_star * P₀ + W_star * P₁ := by
      rw [← mul_add, hP_sum, mul_one]
    dsimp only [U₀]
    rw [mul_add, add_mul, hB_shift v₀, hB_shift1 (-v₀), show u + -v₀ = u - v₀ by ring]
    conv_lhs => arg 2; rw [hW_split]
    simp only [sub_mul]; abel
  have htrig_sin (v : ℝ) :
      2 - 2 * Real.cos (Real.pi / 2) * Real.cos (Real.pi / 2) -
        2 * Real.sin (Real.pi / 2) * Real.sin (Real.pi / 2) * Real.cos (2 * v) =
        (2 * |Real.sin v|) ^ 2 := by
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two, mul_pow, sq_abs, Real.cos_two_mul']
    have hc := Real.cos_sq_add_sin_sq v
    linear_combination -2 * hc
  have hB_star (v : ℝ) : star (B v - W_star) * (B v - W_star) =
      (((2 * |Real.sin v|) ^ 2 : ℝ) : ℂ) • (1 : Register N) := by
    have hst := star_mul_self_conj_pauliX_diagZ (N := N) (by omega) (Real.pi / 2) (Real.pi / 2) v
    change star (B v - W_star) * (B v - W_star) = _ at hst
    rwa [htrig_sin v] at hst
  have hB_norm (v : ℝ) : ‖B v - W_star‖ = 2 * |Real.sin v| := by
    have hsq := norm_sq_conj_pauliX_diagZ (N := N) (by omega) (Real.pi / 2) (Real.pi / 2) v
    change ‖B v - W_star‖ ^ 2 = _ at hsq
    rw [htrig_sin v] at hsq
    have hnn : 0 ≤ 2 * |Real.sin v| := by positivity
    nlinarith only [hsq, norm_nonneg (B v - W_star), hnn, sq_nonneg (‖B v - W_star‖ - 2 * |Real.sin v|)]
  have hf_local (u : ℝ) (hu : |u| ≤ v₀) :
      conjTargetDist K U₀ W_star u = 2 * Real.sin (v₀ + |u|) := by
    unfold conjTargetDist
    change ‖E_m u * U₀ * E_p u - W_star‖ = 2 * Real.sin (v₀ + |u|)
    rw [hflow_decomp u]
    let c₀ : ℝ := 2 * Real.sin (v₀ + u)
    let c₁ : ℝ := 2 * Real.sin (v₀ - u)
    have hsin_add_nn : 0 ≤ Real.sin (u + v₀) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [(abs_le.mp hu).1])
        (by linarith [(abs_le.mp hu).2, hv₀_lt, Real.pi_pos])
    have hsin_sub_nn : 0 ≤ Real.sin (v₀ - u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [(abs_le.mp hu).2])
        (by linarith [(abs_le.mp hu).1, hv₀_lt, Real.pi_pos])
    have hc₀_nn : 0 ≤ c₀ := by dsimp [c₀]; rw [add_comm v₀ u]; positivity
    have hc₁_nn : 0 ≤ c₁ := by dsimp [c₁]; positivity
    have hD₀_n : ‖B (u + v₀) - W_star‖ = c₀ := by
      dsimp [c₀]; rw [hB_norm (u + v₀), abs_of_nonneg hsin_add_nn, add_comm u v₀]
    have hD₁_n : ‖B (u - v₀) - W_star‖ = c₁ := by
      dsimp [c₁]
      have hneg : u - v₀ = -(v₀ - u) := by ring
      rw [hB_norm (u - v₀), hneg, Real.sin_neg, abs_neg, abs_of_nonneg hsin_sub_nn]
    have hstar₀ : star (B (u + v₀) - W_star) * (B (u + v₀) - W_star) =
        ((c₀ ^ 2 : ℝ) : ℂ) • (1 : Register N) := by
      rw [hB_star (u + v₀)]
      congr 2; dsimp [c₀]; rw [abs_of_nonneg hsin_add_nn, add_comm u v₀]
    have hstar₁ : star (B (u - v₀) - W_star) * (B (u - v₀) - W_star) =
        ((c₁ ^ 2 : ℝ) : ℂ) • (1 : Register N) := by
      rw [hB_star (u - v₀)]
      congr 2; dsimp [c₁]
      have hneg : u - v₀ = -(v₀ - u) := by ring
      rw [hneg, Real.sin_neg, abs_neg, abs_of_nonneg hsin_sub_nn]
    have hop := opNorm_qubitOneBlockSum_eq_max hN hc₀_nn hc₁_nn hD₀_n hD₁_n
      (by rw [sub_mul, mul_sub, hB_comm_P₀, hWP₀])
      (by rw [sub_mul, mul_sub, hB_comm_P₁, hWP₁])
      hstar₀ hstar₁
    change ‖(B (u + v₀) - W_star) * P₀ + (B (u - v₀) - W_star) * P₁‖ = max c₀ c₁ at hop
    rw [hop]
    dsimp only [c₀, c₁]
    rcases le_or_gt 0 u with hu0 | hu_neg
    · rw [abs_of_nonneg hu0, max_eq_left]
      refine mul_le_mul_of_nonneg_left ?_ two_pos.le
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [(abs_le.mp hu).2, Real.pi_pos])
        (by linarith [hv₀_lt, (abs_le.mp hu).2, Real.pi_pos])
        (by linarith only [hu0])
    · rw [abs_of_neg hu_neg, max_eq_right]
      · rw [show v₀ + -u = v₀ - u by ring]
      · refine mul_le_mul_of_nonneg_left ?_ two_pos.le
        exact Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [hv₀_pos, (abs_le.mp hu).1, Real.pi_pos])
          (by linarith [hv₀_lt, (abs_le.mp hu).1, Real.pi_pos])
          (by linarith only [hu_neg])
  have hf0 : conjTargetDist K U₀ W_star 0 = 1 / 10 := by
    rw [hf_local 0 (by simp [hv₀_pos.le]), abs_zero, add_zero, hsin_v₀]; norm_num
  refine ⟨U₀, W_star, K, hU₀_unit, hW_mem, hK_sa, hK_norm, hf0, ?_⟩
  intro C r hr hconc
  -- Choose u₁ = min r (min v₀ (1 / (2 * (|C| + 1)))) > 0: on [v₀, v₀ + u₁] ⊆ [0, π / 3], cos ≥ 1 / 2,
  -- so f(u₁) - f(0) = 2(sin(v₀ + u₁) - sin v₀) ≥ u₁, contradicting midpoint concavity of f(u) - C u^2!
  let u₁ : ℝ := min r (min v₀ (1 / (2 * (|C| + 1))))
  have hu₁_pos : 0 < u₁ := lt_min hr (lt_min hv₀_pos (by positivity))
  have hu₁_r : u₁ ≤ r := min_le_left _ _
  have hu₁_v₀ : u₁ ≤ v₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hu₁_C : u₁ ≤ 1 / (2 * (|C| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope Real.sin Real.cos
    (lt_add_of_pos_right v₀ hu₁_pos)
    Real.continuous_sin.continuousOn
    (fun t _ => Real.hasDerivAt_sin t)
  have hcos_ξ : (1 / 2 : ℝ) ≤ Real.cos ξ := by
    rw [← Real.cos_pi_div_three]
    exact Real.antitoneOn_cos
      ⟨by linarith [hv₀_pos, hξ_mem.1], by linarith [hξ_mem.2, hu₁_v₀, hv₀_lt, Real.pi_pos]⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      (by linarith [hξ_mem.2, hu₁_v₀, hv₀_lt])
  have hsin_gain : u₁ / 2 ≤ Real.sin (v₀ + u₁) - Real.sin v₀ := by
    have hsub : v₀ + u₁ - v₀ = u₁ := by ring
    rw [hsub] at hξ_eq
    -- hξ_eq : Real.cos ξ = (Real.sin (v₀ + u₁) - Real.sin v₀) / u₁
    have hm := mul_le_mul_of_nonneg_right hcos_ξ hu₁_pos.le
    have hdiv_mul : (Real.sin (v₀ + u₁) - Real.sin v₀) / u₁ * u₁ =
        Real.sin (v₀ + u₁) - Real.sin v₀ := div_mul_cancel₀ _ hu₁_pos.ne'
    rw [hξ_eq, hdiv_mul] at hm
    linarith only [hm]
  have hf_pos_u₁ : conjTargetDist K U₀ W_star u₁ = 2 * Real.sin (v₀ + u₁) := by
    rw [hf_local u₁ (by rw [abs_of_pos hu₁_pos]; exact hu₁_v₀), abs_of_pos hu₁_pos]
  have hf_neg_u₁ : conjTargetDist K U₀ W_star (-u₁) = 2 * Real.sin (v₀ + u₁) := by
    rw [hf_local (-u₁) (by rw [abs_neg, abs_of_pos hu₁_pos]; exact hu₁_v₀),
      abs_neg, abs_of_pos hu₁_pos]
  have hf_zero : conjTargetDist K U₀ W_star 0 = 2 * Real.sin v₀ := by
    rw [hf_local 0 (by simp [hv₀_pos.le]), abs_zero, add_zero]
  have hmid := hconc.2
    (show u₁ ∈ Icc (-r) r from ⟨by linarith only [hu₁_pos, hr], hu₁_r⟩)
    (show -u₁ ∈ Icc (-r) r from ⟨by linarith only [hu₁_r], by linarith only [hu₁_pos, hr]⟩)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have h0_eq : (1 / 2 : ℝ) * u₁ + (1 / 2 : ℝ) * (-u₁) = 0 := by ring
  rw [h0_eq, hf_pos_u₁, hf_neg_u₁, hf_zero] at hmid
  have hCu : C * u₁ ^ 2 ≤ (1 / 2 : ℝ) * u₁ := by
    have h1 : C * u₁ ≤ |C| * u₁ := mul_le_mul_of_nonneg_right (le_abs_self C) hu₁_pos.le
    have h2 : (|C| + 1) * u₁ ≤ 1 / 2 := by
      have hm := mul_le_mul_of_nonneg_left hu₁_C (show (0 : ℝ) ≤ |C| + 1 by positivity)
      have hrhs : (|C| + 1) * (1 / (2 * (|C| + 1))) = 1 / 2 := by
        have hne : |C| + 1 ≠ 0 := by positivity
        field_simp [hne]
      rwa [hrhs] at hm
    have h3 : C * u₁ ≤ 1 / 2 := by linarith only [h1, h2, hu₁_pos]
    have hm2 := mul_le_mul_of_nonneg_right h3 hu₁_pos.le
    linarith [hm2, show C * u₁ * u₁ = C * u₁ ^ 2 by ring]
  have hneg_sq : (-u₁) ^ 2 = u₁ ^ 2 := by ring
  rw [hneg_sq] at hmid
  linarith only [hmid, hsin_gain, hCu, hu₁_pos]

/-! ### Audit B3: Outer-`sup_θ` sawtooth proliferation of `c`-strongly concave slices -/

/-- Taking the pointwise supremum over `P ≥ 1` `c`-strongly concave functions **destroys** the
`M = 2` collar bound: the finite supremum `G(u) = ⨆ a : Fin P, (e₀ + 2 δ - (c / 2) (u - u_a)^2)`
accumulates Lebesgue collar measure `≥ 2 * (2 - √2) * P * √(δ / c)` inside `[0, 4 P √(δ / c)]`. -/
theorem sup_stronglyConcave_collar_measure_ge {P : ℕ} (hP : 1 ≤ P)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (e₀ : ℝ) :
    let s := Real.sqrt (δ / c)
    let g : Fin P → ℝ → ℝ := fun a u =>
      e₀ + 2 * δ - (c / 2) * (u - (4 * (a.val : ℝ) + 2) * s) ^ 2
    haveI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
    (∀ a : Fin P, IsStronglyConcaveOn c univ (g a)) ∧
      2 * (2 - Real.sqrt 2) * (P : ℝ) * s ≤
        (volume {u ∈ Icc 0 (4 * (P : ℝ) * s) | (⨆ a : Fin P, g a u) ∈ Ioc e₀ (e₀ + δ)}).toReal := by
  intro s g
  haveI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (div_pos hδ hc)
  have hs_sq : s ^ 2 = δ / c := Real.sq_sqrt (div_pos hδ hc).le
  have hcs_sq : c * s ^ 2 = δ := by rw [hs_sq, mul_div_cancel₀ _ hc.ne']
  have hg_conc (a : Fin P) : IsStronglyConcaveOn c univ (g a) := by
    rw [isStronglyConcaveOn_iff_concaveOn_add_sq]
    let u_a : ℝ := (4 * (a.val : ℝ) + 2) * s
    have haff : (fun u : ℝ => g a u + (c / 2) * u ^ 2) =
        fun u => (e₀ + 2 * δ - (c / 2) * u_a ^ 2) + (c * u_a) * u := by
      funext u; dsimp only [g, u_a]; ring
    rw [haff]
    refine ⟨convex_univ, fun x _ y _ p q _ _ hpq => ?_⟩
    simp only [smul_eq_mul]
    linear_combination (e₀ + 2 * δ - c / 2 * u_a ^ 2) * hpq
  refine ⟨hg_conc, ?_⟩
  -- √2 ∈ (1, 2) via squares.
  have hsqrt2_lt2 : Real.sqrt 2 < 2 := by
    calc Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  -- On each cell [4 a s, (4 a + 4) s], G(u) = g a u because |u - u_a| ≤ 2 s ≤ |u - u_b|.
  have hG_cell (a : Fin P) (u : ℝ)
      (hu_lo : 4 * (a.val : ℝ) * s ≤ u) (hu_hi : u ≤ (4 * (a.val : ℝ) + 4) * s) :
      (⨆ b : Fin P, g b u) = g a u := by
    apply le_antisymm
    · refine ciSup_le fun b => ?_
      dsimp only [g]
      have hdist_sq : (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 ≤
          (u - (4 * (b.val : ℝ) + 2) * s) ^ 2 := by
        have ha_abs : |u - (4 * (a.val : ℝ) + 2) * s| ≤ 2 * s :=
          abs_le.mpr ⟨by linarith only [hu_lo], by linarith only [hu_hi]⟩
        rcases lt_trichotomy b.val a.val with hlt | heq | hgt
        · have hb_le : (b.val : ℝ) + 1 ≤ (a.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
          have hb_dist : 2 * s ≤ u - (4 * (b.val : ℝ) + 2) * s := by
            nlinarith only [hu_lo, hb_le, hs_pos]
          rw [← sq_abs (u - (4 * (a.val : ℝ) + 2) * s)]
          exact pow_le_pow_left₀ (abs_nonneg _) (ha_abs.trans hb_dist) 2
        · rw [heq]
        · have hb_ge : (a.val : ℝ) + 1 ≤ (b.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
          have hb_dist : 2 * s ≤ (4 * (b.val : ℝ) + 2) * s - u := by
            nlinarith only [hu_hi, hb_ge, hs_pos]
          have hsq_rev : (u - (4 * (b.val : ℝ) + 2) * s) ^ 2 =
              ((4 * (b.val : ℝ) + 2) * s - u) ^ 2 := by ring
          rw [hsq_rev, ← sq_abs (u - (4 * (a.val : ℝ) + 2) * s)]
          exact pow_le_pow_left₀ (abs_nonneg _) (ha_abs.trans hb_dist) 2
      have hmul := mul_le_mul_of_nonneg_left hdist_sq (show (0 : ℝ) ≤ c / 2 by positivity)
      linarith only [hmul]
    · exact le_ciSup (Finite.bddAbove_range fun b : Fin P => g b u) a
  -- Define the disjoint collar pair K_a = Ioc (4a s) ((4a + 2 - √2) s) ∪ Ico ((4a + 2 + √2) s) ((4a + 4) s).
  let J_left (a : Fin P) : Set ℝ := Ioc (4 * (a.val : ℝ) * s) ((4 * (a.val : ℝ) + 2 - Real.sqrt 2) * s)
  let J_right (a : Fin P) : Set ℝ := Ico ((4 * (a.val : ℝ) + 2 + Real.sqrt 2) * s) ((4 * (a.val : ℝ) + 4) * s)
  let K_cell (a : Fin P) : Set ℝ := J_left a ∪ J_right a
  let Target : Set ℝ :=
    {u ∈ Icc 0 (4 * (P : ℝ) * s) | (⨆ a : Fin P, g a u) ∈ Ioc e₀ (e₀ + δ)}
  have hK_sub (a : Fin P) : K_cell a ⊆ Target := by
    intro u hu
    have ha_lt_P : (a.val : ℝ) + 1 ≤ (P : ℝ) := by exact_mod_cast a.isLt
    have ha_nn : (0 : ℝ) ≤ (a.val : ℝ) := Nat.cast_nonneg a.val
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hu_lo : 4 * (a.val : ℝ) * s ≤ u := h1.le
      have hu_hi : u ≤ (4 * (a.val : ℝ) + 4) * s := by nlinarith only [h2, hsqrt2_pos, hs_pos]
      refine ⟨⟨by nlinarith only [hu_lo, ha_nn, hs_pos],
        by nlinarith only [hu_hi, ha_lt_P, hs_pos]⟩, ?_⟩
      rw [hG_cell a u hu_lo hu_hi]
      dsimp only [g]
      have hd_lo : Real.sqrt 2 * s ≤ (4 * (a.val : ℝ) + 2) * s - u := by linarith only [h2]
      have hd_hi : (4 * (a.val : ℝ) + 2) * s - u < 2 * s := by linarith only [h1]
      have hsq_lo : (Real.sqrt 2 * s) ^ 2 ≤ (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 := by
        have hrev : (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 = ((4 * (a.val : ℝ) + 2) * s - u) ^ 2 := by ring
        rw [hrev]; exact pow_le_pow_left₀ (by positivity) hd_lo 2
      have hsq_hi : (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 < (2 * s) ^ 2 := by
        have hrev : (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 = ((4 * (a.val : ℝ) + 2) * s - u) ^ 2 := by ring
        rw [hrev]
        exact pow_lt_pow_left₀ hd_hi (by nlinarith only [hd_lo, hsqrt2_pos, hs_pos]) two_ne_zero
      rw [mul_pow, Real.sq_sqrt two_pos.le] at hsq_lo
      rw [mul_pow] at hsq_hi
      have hc_lo : δ ≤ (c / 2) * (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 := by
        have hm := mul_le_mul_of_nonneg_left hsq_lo (show (0 : ℝ) ≤ c / 2 by positivity)
        linarith [hm, show (c / 2) * (2 * s ^ 2) = c * s ^ 2 by ring, hcs_sq]
      have hc_hi : (c / 2) * (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 < 2 * δ := by
        have hm := mul_lt_mul_of_pos_left hsq_hi (show (0 : ℝ) < c / 2 by positivity)
        linarith [hm, show (c / 2) * ((2 : ℝ) ^ 2 * s ^ 2) = 2 * (c * s ^ 2) by ring, hcs_sq]
      exact ⟨by linarith only [hc_hi], by linarith only [hc_lo]⟩
    · have hu_lo : 4 * (a.val : ℝ) * s ≤ u := by nlinarith only [h1, hsqrt2_pos, hs_pos]
      have hu_hi : u ≤ (4 * (a.val : ℝ) + 4) * s := h2.le
      refine ⟨⟨by nlinarith only [hu_lo, ha_nn, hs_pos],
        by nlinarith only [hu_hi, ha_lt_P, hs_pos]⟩, ?_⟩
      rw [hG_cell a u hu_lo hu_hi]
      dsimp only [g]
      have hd_lo : Real.sqrt 2 * s ≤ u - (4 * (a.val : ℝ) + 2) * s := by linarith only [h1]
      have hd_hi : u - (4 * (a.val : ℝ) + 2) * s < 2 * s := by linarith only [h2]
      have hsq_lo : 2 * s ^ 2 ≤ (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 := by
        have hm := pow_le_pow_left₀ (by positivity) hd_lo 2
        rwa [mul_pow, Real.sq_sqrt two_pos.le] at hm
      have hsq_hi : (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 < 4 * s ^ 2 := by
        have hm := pow_lt_pow_left₀ hd_hi (by nlinarith only [hd_lo, hsqrt2_pos, hs_pos]) two_ne_zero
        rwa [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] at hm
      have hc_lo : δ ≤ (c / 2) * (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 := by
        have hm := mul_le_mul_of_nonneg_left hsq_lo (show (0 : ℝ) ≤ c / 2 by positivity)
        linarith [hm, show (c / 2) * (2 * s ^ 2) = c * s ^ 2 by ring, hcs_sq]
      have hc_hi : (c / 2) * (u - (4 * (a.val : ℝ) + 2) * s) ^ 2 < 2 * δ := by
        have hm := mul_lt_mul_of_pos_left hsq_hi (show (0 : ℝ) < c / 2 by positivity)
        linarith [hm, show (c / 2) * (4 * s ^ 2) = 2 * (c * s ^ 2) by ring, hcs_sq]
      exact ⟨by linarith only [hc_hi], by linarith only [hc_lo]⟩
  have hK_meas (a : Fin P) : MeasurableSet (K_cell a) :=
    measurableSet_Ioc.union measurableSet_Ico
  have hK_vol (a : Fin P) : volume (K_cell a) = ENNReal.ofReal (2 * (2 - Real.sqrt 2) * s) := by
    have hdisj_lr : Disjoint (J_left a) (J_right a) := Set.disjoint_left.mpr fun u hl hr => by
      nlinarith only [hl.2, hr.1, hsqrt2_pos, hs_pos]
    rw [measure_union hdisj_lr measurableSet_Ico, Real.volume_Ioc, Real.volume_Ico]
    have hlen1 : (4 * (a.val : ℝ) + 2 - Real.sqrt 2) * s - 4 * (a.val : ℝ) * s =
        (2 - Real.sqrt 2) * s := by ring
    have hlen2 : (4 * (a.val : ℝ) + 4) * s - (4 * (a.val : ℝ) + 2 + Real.sqrt 2) * s =
        (2 - Real.sqrt 2) * s := by ring
    have hnn : 0 ≤ (2 - Real.sqrt 2) * s := mul_nonneg (by linarith only [hsqrt2_lt2]) hs_pos.le
    rw [hlen1, hlen2, ← ENNReal.ofReal_add hnn hnn]
    congr 1; ring
  have hK_inside_open (a : Fin P) :
      K_cell a ⊆ Ioo (4 * (a.val : ℝ) * s) ((4 * (a.val : ℝ) + 4) * s) := by
    intro u hu
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, by nlinarith only [h2, hsqrt2_pos, hs_pos]⟩
    · exact ⟨by nlinarith only [h1, hsqrt2_pos, hs_pos], h2⟩
  have hK_disj (a b : Fin P) (hab : a ≠ b) : Disjoint (K_cell a) (K_cell b) := by
    refine Set.disjoint_left.mpr fun u hua hub => ?_
    have ha := hK_inside_open a hua
    have hb := hK_inside_open b hub
    rcases lt_trichotomy a.val b.val with hlt | heq | hgt
    · have hle : (a.val : ℝ) + 1 ≤ (b.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      nlinarith only [ha.2, hb.1, hle, hs_pos]
    · exact hab (Fin.ext heq)
    · have hle : (b.val : ℝ) + 1 ≤ (a.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      nlinarith only [hb.2, ha.1, hle, hs_pos]
  have hunion_sub : (⋃ a ∈ (Finset.univ : Finset (Fin P)), K_cell a) ⊆ Target :=
    iUnion₂_subset fun a _ => hK_sub a
  have hTarget_fin : volume Target < ⊤ := by
    refine lt_of_le_of_lt (measure_mono fun u hu => hu.1) ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hvol_union : volume (⋃ a ∈ (Finset.univ : Finset (Fin P)), K_cell a) =
      ENNReal.ofReal (2 * (2 - Real.sqrt 2) * (P : ℝ) * s) := by
    rw [measure_biUnion_finset (fun a _ b _ hab => hK_disj a b hab) (fun a _ => hK_meas a)]
    simp_rw [hK_vol]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast P,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg P)]
    congr 1; ring
  have hmono := ENNReal.toReal_mono hTarget_fin.ne (measure_mono hunion_sub)
  rw [hvol_union, ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg
    (mul_nonneg two_pos.le (by linarith only [hsqrt2_lt2])) (Nat.cast_nonneg P)) hs_pos.le)] at hmono
  exact hmono

#print axioms isStronglyConcaveOn_iff_concaveOn_add_sq
#print axioms isStronglyConcaveOn_of_deriv2_le_neg
#print axioms isStronglyConcaveOn_iInf
#print axioms isStronglyConvexOn_iSup
#print axioms stronglyConcaveOn_collar_subset_two_Icc
#print axioms stronglyConcaveOn_parabola_collar_eq
#print axioms stronglyConvexOn_collar_subset_two_Icc
#print axioms gaussian_rotatingDirection_stronglyConcaveInf_anticoncentration
#print axioms gaussian_rotatingDirection_stronglyConvexSup_anticoncentration
#print axioms fixed_tenth_locking_of_stronglyConvexSup_charts
#print axioms swapped_torusCriticalHeight_fixedTarget_ge_one
#print axioms swapped_torusCriticalHeight_modPhase_ge_half
#print axioms convexOn_conjFlow_opNorm_add_four_sq
#print axioms exists_frozenCircuit_tenth_pos_secondDeriv
#print axioms exists_frozenCircuit_tenth_upward_vKink
#print axioms sup_stronglyConcave_collar_measure_ge

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
