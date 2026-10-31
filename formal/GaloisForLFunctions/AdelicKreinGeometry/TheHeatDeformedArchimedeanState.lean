import GaloisForLFunctions.AdelicKreinGeometry.HeatGaussianResidueKernel
import GaloisForLFunctions.AdelicKreinGeometry.WeilsArchimedeanStateCountsTheZeros
import GaloisForLFunctions.HeckeKreinToeplitz.HeatCollisionsCountTheIndex
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Order.LiminfLimsup

/-!
# The heat-deformed archimedean state as a Pontryagin homotopy

From the Gaussian-weighted Riemann theta kernel `Φ_t(x) = Φ(x) e^{t x²}` of `H_t` alone (source data
only), this module constructs the **heat-deformed archimedean state**

`φ_c^{(t)}(x ↦ a x + b) = heatDilationKernel t |a| − c |a|^{−1/2} |b|`  (`heatArchState c t`)

on `AffineGroupQ = ℚ ⋊ ℚˣ` and establishes its unconditional Pontryagin index laws for all `c > 0`:

* **Source-only construction and time continuity** (`heatArchState`, `isHermKernel_heatArchState`,
  `continuousOn_heatArchState`): `heatDilationKernel t` is built purely from the tangent-disc
  Poisson–Jensen boundary integral of `log ‖H_t‖` and `(H_t'/H_t)` integrated against the entire
  Gaussian wave `e^{−z² − i z log v}` along `Im z = ∓1`. For each `g ∈ AffineGroupQ`,
  `t ↦ φ_c^{(t)}(g)` is continuous on `(0, ∞)` across all real-axis and off-axis collisions.
* **Finiteness and exact zero-counting formula** (`negIndex_heatArchState_lt_top`,
  `negIndex_heatArchState_eq`, `negIndex_heatArchState_eq_nonrealZeroCount`,
  `negIndex_heatArchState_eq_card_of_simple`): for every `t > 0`, `κ(φ_c^{(t)}) < ⊤` and
  `κ(φ_c^{(t)}) = heatRightZeroMultiplicity t + 1 = nonrealZeroCount t / 2 + 1`,
  the number of nonreal right zeros of `H_t` (counted with multiplicity) plus one.
* **Lower semicontinuity and monotonicity** (`lowerSemicontinuousAt_negIndex_heatArchState`,
  `lowerSemicontinuousOn_negIndex_heatArchState`, `antitoneOn_negIndex_heatArchState`):
  `t ↦ κ(φ_c^{(t)})` is lower semicontinuous on `(0, ∞)` (proved directly from pointwise time
  continuity of `φ_c^{(t)}` and `eventually_le_hermNegIndex`) and nonincreasing (`AntitoneOn`) on
  `(0, ∞)`.
* **Changes only at collisions, by one per collided pair** (`exists_right_negIndex_heatArchState_eq`,
  `exists_left_negIndex_heatArchState_eq_add_collisionPairs`,
  `eventually_negIndex_heatArchState_eq_iff_realMultipleZeros_eq_empty`,
  `negIndex_heatArchState_eq_add_interval_collisionPairs`,
  `negIndex_heatArchState_eq_iff_forall_realMultipleZeros_eq_empty`):
  `κ(φ_c^{(s)}) = κ(φ_c^{(t)})` for `s ∈ (t, t + δ)`,
  `κ(φ_c^{(s)}) = κ(φ_c^{(t)}) + heatCollisionPairs t` for `s ∈ (t − δ, t)` where
  `heatCollisionPairs t = ∑_{z ∈ realMultipleZeros t} ⌊m_t(z)/2⌋`, and on any `[t₁, t₂] ⊂ (0, ∞)`
  the total drop `κ(φ_c^{(t₁)}) − κ(φ_c^{(t₂)})` equals the sum of collided pairs in `(t₁, t₂]`.
* **Pontryagin homotopy corollaries**:
  * For `t ≥ 1/8`, `φ_c^{(t)} = archGlue 0 c` and `κ(φ_c^{(t)}) = 1`
    (`heatArchState_eq_archGlue_zero_of_eighth_le`, `negIndex_heatArchState_eq_one_of_eighth_le`).
  * `RiemannHypothesis ↔ ∀ t > 0, κ(φ_c^{(t)}) = 1` and
    `RiemannHypothesis ↔ ∀ s t > 0, κ(φ_c^{(s)}) = κ(φ_c^{(t)})`
    (`riemannHypothesis_iff_forall_negIndex_heatArchState_eq_one`,
    `riemannHypothesis_iff_negIndex_heatArchState_const`).
  * Small-time comparison with Weil's `t = 0` archimedean state `φ_c`:
    `κ(φ_c) ≤ liminf_{t → 0⁺} κ(φ_c^{(t)})`, and `κ(φ_c) < ⊤ ↔ ∃ M : ℕ, ∀ t > 0, κ(φ_c^{(t)}) ≤ M`
    (`negIndex_weilArchState_le_liminf_heatArchState`, `negIndex_weilArchState_lt_top_iff_bdd`).
-/

open Complex Set Filter Topology
open scoped ComplexConjugate BigOperators
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open RHTower RHTower.DeBruijn

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Source-defined heat-deformed archimedean state and time continuity -/

/-- **The heat-deformed archimedean state** `φ_c^{(t)} : AffineGroupQ → ℂ` built solely from the
Gaussian-weighted theta kernel `Φ_t(x) = Φ(x) e^{t x²}` of `H_t` (source data only) on positive
rational slopes and the archimedean successor `−c |a|^{−1/2} |b|` on shifts. -/
def heatArchState (c t : ℝ) : AffineGroupQ → ℂ :=
  archGlue (heatDilationKernel t) c

theorem heatArchState_apply (c t : ℝ) (g : AffineGroupQ) :
    heatArchState c t g = heatDilationKernel t (slopeAbs g) +
      conformalInduction Rat.AbsoluteValue.real 1 (fun m => (c : ℂ) * negAbsRat m) g :=
  rfl

/-- Archimedean gluing preserves Hermitian symmetry of the dilation kernel. -/
theorem isHermKernel_archGlue {K : posUnits → ℂ} (hK : IsHermKernel K) (c : ℝ) :
    IsHermKernel (archGlue K c) := fun g => by
  have h1 : K (slopeAbs g⁻¹) = conj (K (slopeAbs g)) := by rw [map_inv]; exact hK _
  have h2 := isHermKernel_conformalInduction (isConformal_negAbsRat c)
    (isHermKernel_ofReal_mul isHermKernel_negAbsRat c)
  show K (slopeAbs g⁻¹) + _ = conj (K (slopeAbs g) + _)
  rw [h1, h2 g, map_add]

/-- `φ_c^{(t)}` is a Hermitian kernel on `AffineGroupQ` for every `c, t ∈ ℝ`. -/
theorem isHermKernel_heatArchState (c t : ℝ) :
    IsHermKernel (heatArchState c t) :=
  isHermKernel_archGlue (isHermKernel_heatDilationKernel t) c

/-- Pointwise convergence of `φ_c^{(s)}(g) → φ_c^{(t₁)}(g)` as `s → t₁` (`t₁ > 0`). -/
theorem tendsto_heatArchState_nhds {t₁ : ℝ} (ht₁ : 0 < t₁) (c : ℝ) (g : AffineGroupQ) :
    Tendsto (fun s => heatArchState c s g) (𝓝 t₁) (𝓝 (heatArchState c t₁ g)) :=
  (tendsto_heatDilationKernel_nhds ht₁ (slopeAbs g)).add tendsto_const_nhds

/-- **Pointwise time continuity of `φ_c^{(t)}`** on `(0, ∞)` across all real and nonreal zero
collisions. -/
theorem continuousOn_heatArchState (c : ℝ) (g : AffineGroupQ) :
    ContinuousOn (fun t => heatArchState c t g) (Ioi 0) :=
  fun _ ht => (tendsto_heatArchState_nhds ht c g).mono_left nhdsWithin_le_nhds

/-! ### Finiteness and exact Pontryagin index at every `t > 0` -/

/-- For every `t > 0`, the Pontryagin index of `heatDilationKernel t` on `ℚ_{>0}` equals the total
multiplicity of the nonreal right zeros of `H_t`. -/
theorem negIndex_heatDilationKernel_eq {t : ℝ} (ht : 0 < t) :
    negIndex (heatDilationKernel t) = (heatRightZeroMultiplicity t : ℕ∞) := by
  have hfun : heatDilationKernel t =
      fun v => ∑ u ∈ heatRightZeroSet t, jordanPairKernel u (heatResiduePoly t u) v :=
    funext (heatDilationKernel_eq_sum_jordanPairKernel ht)
  have hsum : (∑ u ∈ heatRightZeroSet t, ((heatResiduePoly t u).natDegree + 1)) =
      heatRightZeroMultiplicity t :=
    Finset.sum_congr rfl fun u hu => natDegree_heatResiduePoly_add_one ht hu
  rw [hfun, negIndex_finset_sum_jordanPairKernel_eq
    (fun u hu => ((mem_heatRightZeroSet ht).mp hu).2)
    (fun u hu => heatResiduePoly_ne_zero ht hu), hsum]

/-- **Exact zero-counting formula for `φ_c^{(t)}`**: for every `c > 0` and `t > 0`,
`κ(φ_c^{(t)})` equals the number of nonreal right zeros of `H_t` (counted with multiplicity) plus
one. -/
theorem negIndex_heatArchState_eq {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    negIndex (heatArchState c t) = ((heatRightZeroMultiplicity t + 1 : ℕ) : ℕ∞) := by
  have hfun : heatDilationKernel t =
      fun v => ∑ u ∈ heatRightZeroSet t, jordanPairKernel u (heatResiduePoly t u) v :=
    funext (heatDilationKernel_eq_sum_jordanPairKernel ht)
  have hsum : (∑ u ∈ heatRightZeroSet t, ((heatResiduePoly t u).natDegree + 1)) =
      heatRightZeroMultiplicity t :=
    Finset.sum_congr rfl fun u hu => natDegree_heatResiduePoly_add_one ht hu
  unfold heatArchState
  rw [hfun, negIndex_archGlue_finset_sum_jordanPairKernel_eq
    (fun u hu => ((mem_heatRightZeroSet ht).mp hu).2)
    (fun u hu => abs_im_lt_half_of_riemannHeat_eq_zero ht ((mem_heatRightZeroSet ht).mp hu).1)
    (fun u hu => heatResiduePoly_ne_zero ht hu) hc, hsum]

/-- In terms of the total nonreal zero count `N(t)` of `H_t`: `κ(φ_c^{(t)}) = N(t) / 2 + 1`. -/
theorem negIndex_heatArchState_eq_nonrealZeroCount {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    negIndex (heatArchState c t) = ((nonrealZeroCount t / 2 + 1 : ℕ) : ℕ∞) := by
  rw [negIndex_heatArchState_eq hc ht, heatRightZeroMultiplicity_eq_div]

/-- **Finiteness of `κ(φ_c^{(t)})`** for every `c > 0` and `t > 0`. -/
theorem negIndex_heatArchState_lt_top {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    negIndex (heatArchState c t) < ⊤ := by
  rw [negIndex_heatArchState_eq hc ht]
  exact ENat.coe_lt_top _

theorem negIndex_heatArchState_ne_top {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    negIndex (heatArchState c t) ≠ ⊤ :=
  (negIndex_heatArchState_lt_top hc ht).ne

/-- Every `φ_c^{(t)}` (`c > 0, t > 0`) carries at least the archimedean successor's negative
square. -/
theorem one_le_negIndex_heatArchState {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    1 ≤ negIndex (heatArchState c t) := by
  rw [negIndex_heatArchState_eq hc ht]
  exact_mod_cast Nat.le_add_left 1 (heatRightZeroMultiplicity t)

/-- When all nonreal right zeros of `H_t` are simple, `κ(φ_c^{(t)}) = #(heatRightZeroSet t) + 1`. -/
theorem negIndex_heatArchState_eq_card_of_simple {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t)
    (hsimple : ∀ u ∈ heatRightZeroSet t, zeroMult (riemannHeat t) u = 1) :
    negIndex (heatArchState c t) = (((heatRightZeroSet t).card + 1 : ℕ) : ℕ∞) := by
  rw [negIndex_heatArchState_eq hc ht, heatRightZeroMultiplicity_eq_card_of_simple hsimple]

/-! ### Lower semicontinuity and monotonicity in `t` -/

/-- **Lower semicontinuity of `s ↦ κ(φ_c^{(s)})` at every `t > 0`**: proved directly from
pointwise time continuity of `φ_c^{(s)}` and spectral persistence of negative Gram eigenvalues. -/
theorem lowerSemicontinuousAt_negIndex_heatArchState (c : ℝ) {t : ℝ} (ht : 0 < t) :
    LowerSemicontinuousAt (fun s => negIndex (heatArchState c s)) t := by
  classical
  rw [lowerSemicontinuousAt_iff]
  intro y hy
  have hnot : ¬ negIndex (heatArchState c t) ≤ y := not_le_of_gt hy
  rw [negIndex_le_iff] at hnot
  simp only [not_forall, not_le] at hnot
  obtain ⟨n, x, hx⟩ := hnot
  have hev := eventually_le_hermNegIndex (H := fun s => gram (heatArchState c s) x)
    (gram_isHermitian (isHermKernel_heatArchState c t) x)
    (fun a b => tendsto_heatArchState_nhds ht c _)
  exact hev.mono fun s hs =>
    hx.trans_le ((Nat.cast_le.mpr hs).trans (hermNegIndex_gram_le_negIndex _ x))

/-- **Lower semicontinuity of `t ↦ κ(φ_c^{(t)})` on `(0, ∞)`.** -/
theorem lowerSemicontinuousOn_negIndex_heatArchState (c : ℝ) :
    LowerSemicontinuousOn (fun t => negIndex (heatArchState c t)) (Ioi 0) := by
  rw [lowerSemicontinuousOn_iff]
  intro t ht
  rw [lowerSemicontinuousWithinAt_iff]
  intro y hy
  exact ((lowerSemicontinuousAt_iff.mp
    (lowerSemicontinuousAt_negIndex_heatArchState c ht)) y hy).filter_mono nhdsWithin_le_nhds

/-- **Monotonicity (`AntitoneOn`) of `t ↦ κ(φ_c^{(t)})` on `(0, ∞)`.** -/
theorem antitoneOn_negIndex_heatArchState {c : ℝ} (hc : 0 < c) :
    AntitoneOn (fun t => negIndex (heatArchState c t)) (Ioi 0) := by
  intro s hs t ht hst
  dsimp only
  rw [negIndex_heatArchState_eq_nonrealZeroCount hc hs,
    negIndex_heatArchState_eq_nonrealZeroCount hc ht]
  exact Nat.cast_le.mpr (Nat.add_le_add_right
    (Nat.div_le_div_right (nonrealZeroCount_antitoneOn hs ht hst)) 1)

/-! ### Collided pairs and the exact collision jump law -/

/-- Number of collided conjugate pairs of nonreal zeros landing on `ℝ` at time `t`: each real
multiple zero of `H_t` of multiplicity `m ≥ 2` absorbs `⌊m / 2⌋` conjugate pairs (so `⌊m / 2⌋`
nonreal right zeros). -/
def heatCollisionPairs (t : ℝ) : ℕ :=
  ∑ z ∈ realMultipleZeros t, zeroMult (riemannHeat t) z / 2

theorem two_mul_heatCollisionPairs (t : ℝ) :
    2 * heatCollisionPairs t = collisionMass t := by
  unfold heatCollisionPairs collisionMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  omega

theorem heatCollisionPairs_eq_div (t : ℝ) :
    heatCollisionPairs t = collisionMass t / 2 := by
  rw [← two_mul_heatCollisionPairs, Nat.mul_div_cancel_left _ (by norm_num)]

theorem even_collisionMass (t : ℝ) : Even (collisionMass t) :=
  ⟨heatCollisionPairs t, by rw [← two_mul_heatCollisionPairs]; ring⟩

theorem heatCollisionPairs_eq_zero_iff_collisionMass_eq_zero (t : ℝ) :
    heatCollisionPairs t = 0 ↔ collisionMass t = 0 := by
  rw [← two_mul_heatCollisionPairs]
  omega

/-- No collided pairs occur at time `t` if and only if `H_t` has no real multiple zeros. -/
theorem heatCollisionPairs_eq_zero_iff_realMultipleZeros_eq_empty (t : ℝ) :
    heatCollisionPairs t = 0 ↔ realMultipleZeros t = ∅ := by
  by_cases h : 0 < t ∧ t ≤ 1 / 8
  · rw [heatCollisionPairs, Finset.sum_eq_zero_iff]
    constructor
    · intro h0
      refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
      obtain ⟨hz0, -, hd⟩ := (mem_realMultipleZeros h.1 h.2).mp hz
      have h2 := two_le_zeroMult_riemannHeat h.1.le hz0 hd
      have hz_zero := h0 z hz
      omega
    · intro hemp
      simp [hemp]
  · have hemp : realMultipleZeros t = ∅ := by
      rw [realMultipleZeros, dif_neg h]
    simp [heatCollisionPairs, hemp]

theorem heatCollisionPairs_eq_zero_of_eighth_le {t : ℝ} (ht : 1 / 8 ≤ t) :
    heatCollisionPairs t = 0 :=
  (heatCollisionPairs_eq_zero_iff_collisionMass_eq_zero t).mpr
    (collisionMass_eq_zero_of_eighth_le ht)

/-- **Right-constancy of `κ(φ_c^{(t)})`**: just after any `t > 0`, no nonreal zeros are created and
`κ(φ_c^{(s)}) = κ(φ_c^{(t)})`. -/
theorem exists_right_negIndex_heatArchState_eq {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    ∃ δ > 0, ∀ s, t < s → s < t + δ →
      negIndex (heatArchState c s) = negIndex (heatArchState c t) := by
  rcases lt_or_ge t (1 / 8) with ht8 | ht8
  · obtain ⟨δ, hδ, hR⟩ := exists_right_nonrealZeroCount ht ht8
    refine ⟨δ, hδ, fun s hts hsδ => ?_⟩
    rw [negIndex_heatArchState_eq_nonrealZeroCount hc (ht.trans hts),
      negIndex_heatArchState_eq_nonrealZeroCount hc ht, hR s hts hsδ]
  · refine ⟨1, one_pos, fun s hts _ => ?_⟩
    rw [negIndex_heatArchState_eq_nonrealZeroCount hc (ht.trans hts),
      negIndex_heatArchState_eq_nonrealZeroCount hc ht,
      nonrealZeroCount_eq_zero_of_le (ht8.trans hts.le),
      nonrealZeroCount_eq_zero_of_le ht8]

/-- **Left jump law of `κ(φ_c^{(t)})`**: just before any `t > 0`, `κ(φ_c^{(s)})` exceeds
`κ(φ_c^{(t)})` by exactly `heatCollisionPairs t` — one negative square per collided conjugate pair. -/
theorem exists_left_negIndex_heatArchState_eq_add_collisionPairs {c : ℝ} (hc : 0 < c) {t : ℝ}
    (ht : 0 < t) :
    ∃ δ > 0, ∀ s, t - δ < s → s < t →
      negIndex (heatArchState c s) =
        negIndex (heatArchState c t) + (heatCollisionPairs t : ℕ∞) := by
  rcases le_or_gt t (1 / 8) with ht8 | ht8
  · obtain ⟨δ, hδ, hL⟩ := exists_left_nonrealZeroCount ht ht8
    refine ⟨min δ (t / 2), lt_min hδ (by linarith), fun s hts hst => ?_⟩
    have hs0 : 0 < s := by
      have : min δ (t / 2) ≤ t / 2 := min_le_right _ _
      linarith
    have hsδ : t - δ < s := by
      have : min δ (t / 2) ≤ δ := min_le_left _ _
      linarith
    have hcount := hL s hsδ hst
    rw [← two_mul_heatRightZeroMultiplicity s, ← two_mul_heatRightZeroMultiplicity t,
      ← two_mul_heatCollisionPairs t] at hcount
    have hmult : heatRightZeroMultiplicity s =
        heatRightZeroMultiplicity t + heatCollisionPairs t := by omega
    rw [negIndex_heatArchState_eq hc hs0, negIndex_heatArchState_eq hc ht, hmult]
    norm_cast
    omega
  · refine ⟨t - 1 / 8, by linarith, fun s hts hst => ?_⟩
    have hs8 : 1 / 8 < s := by linarith
    have hs0 : 0 < s := by linarith
    rw [negIndex_heatArchState_eq_nonrealZeroCount hc hs0,
      negIndex_heatArchState_eq_nonrealZeroCount hc ht,
      nonrealZeroCount_eq_zero_of_le hs8.le, nonrealZeroCount_eq_zero_of_le ht8.le,
      heatCollisionPairs_eq_zero_of_eighth_le ht8.le]
    simp

/-- **Local constancy characterization**: near `t > 0`, `κ(φ_c^{(s)})` is locally constant at `t`
if and only if `heatCollisionPairs t = 0`. -/
theorem eventually_negIndex_heatArchState_eq_iff_collisionPairs_eq_zero {c : ℝ} (hc : 0 < c)
    {t : ℝ} (ht : 0 < t) :
    (∀ᶠ s in 𝓝 t, negIndex (heatArchState c s) = negIndex (heatArchState c t)) ↔
      heatCollisionPairs t = 0 := by
  constructor
  · intro hev
    obtain ⟨δ, hδ, hL⟩ := exists_left_negIndex_heatArchState_eq_add_collisionPairs hc ht
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    set η := min δ ε / 2
    have hη : 0 < η := by positivity
    set s := t - η
    have hdist : dist s t < ε := by
      rw [Real.dist_eq, show s - t = -η by ring, abs_neg, abs_of_pos hη]
      have : min δ ε ≤ ε := min_le_right _ _
      dsimp only [η]
      linarith
    have hs_gt : t - δ < s := by
      have : min δ ε ≤ δ := min_le_left _ _
      dsimp only [s, η]
      linarith
    have hs_lt : s < t := by dsimp only [s]; linarith
    have heq1 := hball hdist
    have heq2 := hL s hs_gt hs_lt
    rw [heq1, negIndex_heatArchState_eq hc ht] at heq2
    have hnat : heatRightZeroMultiplicity t + 1 =
        (heatRightZeroMultiplicity t + 1) + heatCollisionPairs t := by exact_mod_cast heq2
    omega
  · intro h0
    obtain ⟨δ₁, hδ₁, hL⟩ := exists_left_negIndex_heatArchState_eq_add_collisionPairs hc ht
    obtain ⟨δ₂, hδ₂, hR⟩ := exists_right_negIndex_heatArchState_eq hc ht
    set δ := min δ₁ δ₂
    have hδ : 0 < δ := lt_min hδ₁ hδ₂
    filter_upwards [Ioo_mem_nhds (by linarith : t - δ < t) (by linarith : t < t + δ)] with s hs
    rcases lt_trichotomy s t with hlt | rfl | hgt
    · rw [hL s (by linarith [min_le_left δ₁ δ₂, hs.1]) hlt, h0, Nat.cast_zero, add_zero]
    · rfl
    · exact hR s hgt (by linarith [min_le_right δ₁ δ₂, hs.2])

/-- Near `t > 0`, `κ(φ_c^{(s)})` changes at `t` if and only if `H_t` has a real multiple zero
(a collision on the critical line). -/
theorem eventually_negIndex_heatArchState_eq_iff_realMultipleZeros_eq_empty {c : ℝ} (hc : 0 < c)
    {t : ℝ} (ht : 0 < t) :
    (∀ᶠ s in 𝓝 t, negIndex (heatArchState c s) = negIndex (heatArchState c t)) ↔
      realMultipleZeros t = ∅ :=
  (eventually_negIndex_heatArchState_eq_iff_collisionPairs_eq_zero hc ht).trans
    (heatCollisionPairs_eq_zero_iff_realMultipleZeros_eq_empty t)

/-- Total nonreal right-zero multiplicity of `H_t` (`t > 0`) equals the finite sum of collided
pairs at all future times `s > t`. -/
theorem heatRightZeroMultiplicity_eq_sum_collisionPairs {t : ℝ} (ht : 0 < t) :
    heatRightZeroMultiplicity t =
      ∑ s ∈ (finite_collisionTimes ht).toFinset, heatCollisionPairs s := by
  have h := nonrealZeroCount_eq_sum_collisionMass ht
  rw [← two_mul_heatRightZeroMultiplicity] at h
  have hsum : (∑ s ∈ (finite_collisionTimes ht).toFinset, collisionMass s) =
      2 * ∑ s ∈ (finite_collisionTimes ht).toFinset, heatCollisionPairs s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => (two_mul_heatCollisionPairs s).symm
  rw [hsum] at h
  omega

/-- **Global collision decomposition of `κ(φ_c^{(t)})`**: `κ(φ_c^{(t)})` equals `1` plus the total
number of conjugate pairs colliding after time `t`. -/
theorem negIndex_heatArchState_eq_sum_collisionPairs {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    negIndex (heatArchState c t) =
      ((∑ s ∈ (finite_collisionTimes ht).toFinset, heatCollisionPairs s + 1 : ℕ) : ℕ∞) := by
  rw [negIndex_heatArchState_eq hc ht, heatRightZeroMultiplicity_eq_sum_collisionPairs ht]

/-- **Exact interval jump law**: for `0 < t₁ ≤ t₂`, the index drop between `t₁` and `t₂` equals the
sum of `heatCollisionPairs s` over all collision times `s ∈ (t₁, t₂]`. -/
theorem negIndex_heatArchState_eq_add_interval_collisionPairs {c : ℝ} (hc : 0 < c)
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) :
    negIndex (heatArchState c t₁) =
      negIndex (heatArchState c t₂) +
        ((∑ s ∈ (finite_collisionTimes ht₁).toFinset.filter (· ≤ t₂),
          heatCollisionPairs s : ℕ) : ℕ∞) := by
  classical
  have ht₂ : 0 < t₂ := ht₁.trans_le ht₁₂
  set P₁ := (finite_collisionTimes ht₁).toFinset
  set P₂ := (finite_collisionTimes ht₂).toFinset
  have hsplit := (Finset.sum_filter_add_sum_filter_not P₁ (· ≤ t₂) heatCollisionPairs).symm
  have hrest : P₁.filter (fun s => ¬ s ≤ t₂) = P₂ := by
    ext s
    simp only [P₁, P₂, Finset.mem_filter, Set.Finite.mem_toFinset, mem_setOf_eq, not_le]
    exact ⟨fun h => ⟨ h.2, h.1.2 ⟩, fun h => ⟨⟨ht₁₂.trans_lt h.1, h.2⟩, h.1⟩⟩
  rw [hrest] at hsplit
  rw [negIndex_heatArchState_eq_sum_collisionPairs hc ht₁,
    negIndex_heatArchState_eq_sum_collisionPairs hc ht₂]
  change ((∑ s ∈ P₁, heatCollisionPairs s + 1 : ℕ) : ℕ∞) =
    ((∑ s ∈ P₂, heatCollisionPairs s + 1 : ℕ) : ℕ∞) +
      ((∑ s ∈ P₁.filter (· ≤ t₂), heatCollisionPairs s : ℕ) : ℕ∞)
  rw [hsplit]
  norm_cast
  omega

/-- **Interval constancy iff collision-free**: on `(t₁, t₂]` (`0 < t₁ ≤ t₂`), `κ(φ_c^{(t)})` takes
the same value at `t₁` and `t₂` if and only if no collision occurs in `(t₁, t₂]`. -/
theorem negIndex_heatArchState_eq_iff_forall_realMultipleZeros_eq_empty {c : ℝ} (hc : 0 < c)
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) :
    negIndex (heatArchState c t₁) = negIndex (heatArchState c t₂) ↔
      ∀ s ∈ Ioc t₁ t₂, realMultipleZeros s = ∅ := by
  classical
  have ht₂ : 0 < t₂ := ht₁.trans_le ht₁₂
  rw [negIndex_heatArchState_eq_add_interval_collisionPairs hc ht₁ ht₁₂,
    negIndex_heatArchState_eq hc ht₂]
  set S := (finite_collisionTimes ht₁).toFinset.filter (· ≤ t₂)
  have hsum_iff :
      (((heatRightZeroMultiplicity t₂ + 1 : ℕ) : ℕ∞) +
          ((∑ s ∈ S, heatCollisionPairs s : ℕ) : ℕ∞) =
        ((heatRightZeroMultiplicity t₂ + 1 : ℕ) : ℕ∞)) ↔
      ∑ s ∈ S, heatCollisionPairs s = 0 := by
    constructor
    · intro h
      have hnat : (heatRightZeroMultiplicity t₂ + 1) + ∑ s ∈ S, heatCollisionPairs s =
          heatRightZeroMultiplicity t₂ + 1 := by exact_mod_cast h
      omega
    · intro h
      rw [h, Nat.cast_zero, add_zero]
  rw [hsum_iff, Finset.sum_eq_zero_iff]
  constructor
  · intro h0 s hs
    rw [← heatCollisionPairs_eq_zero_iff_realMultipleZeros_eq_empty]
    by_cases hc0 : collisionMass s = 0
    · exact (heatCollisionPairs_eq_zero_iff_collisionMass_eq_zero s).mpr hc0
    · exact h0 s (Finset.mem_filter.mpr
        ⟨(Set.Finite.mem_toFinset _).mpr ⟨hs.1, hc0⟩, hs.2⟩)
  · intro hemp s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
    have hgt : t₁ < s := ((Set.Finite.mem_toFinset _).mp hs1).1
    exact (heatCollisionPairs_eq_zero_iff_realMultipleZeros_eq_empty s).mpr (hemp s ⟨hgt, hs2⟩)

/-! ### Pontryagin homotopy corollaries and small-time comparison with `weilArchState` -/

/-- Beyond `t ≥ 1/8`, `H_t` has no nonreal zeros and `φ_c^{(t)}` coincides with the pure
archimedean successor `archGlue 0 c`. -/
theorem heatArchState_eq_archGlue_zero_of_eighth_le (c : ℝ) {t : ℝ} (ht : 1 / 8 ≤ t) :
    heatArchState c t = archGlue 0 c := by
  funext g
  simp only [heatArchState, archGlue, heatDilationKernel_eq_zero_of_eighth_le ht, Pi.zero_apply]

/-- Beyond `t ≥ 1/8`, `κ(φ_c^{(t)}) = 1` for every `c > 0`. -/
theorem negIndex_heatArchState_eq_one_of_eighth_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 1 / 8 ≤ t) :
    negIndex (heatArchState c t) = 1 := by
  rw [negIndex_heatArchState_eq hc (by linarith : 0 < t),
    heatRightZeroMultiplicity, heatRightZeroSet_eq_empty_of_eighth_le ht, Finset.sum_empty]
  rfl

/-- **RH equivalence (unit negative index)**: for `c > 0`, the Riemann Hypothesis holds if and only
if `κ(φ_c^{(t)}) = 1` for every `t > 0`. -/
theorem riemannHypothesis_iff_forall_negIndex_heatArchState_eq_one {c : ℝ} (hc : 0 < c) :
    RiemannHypothesis ↔ ∀ t > 0, negIndex (heatArchState c t) = 1 := by
  rw [riemannHypothesis_iff_forall_collisionMass_eq_zero]
  constructor
  · intro h t ht
    rw [negIndex_heatArchState_eq_sum_collisionPairs hc ht]
    have h0 : ∑ s ∈ (finite_collisionTimes ht).toFinset, heatCollisionPairs s = 0 :=
      Finset.sum_eq_zero fun s hs =>
        (heatCollisionPairs_eq_zero_iff_collisionMass_eq_zero s).mpr
          (h s (ht.trans ((Set.Finite.mem_toFinset _).mp hs).1))
    rw [h0]
    rfl
  · intro h t ht
    rw [← heatCollisionPairs_eq_zero_iff_collisionMass_eq_zero,
      ← eventually_negIndex_heatArchState_eq_iff_collisionPairs_eq_zero hc ht]
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [h s hs, h t ht]

/-- **RH equivalence (homotopy constancy)**: for `c > 0`, the Riemann Hypothesis holds if and only
if the Pontryagin index `κ(φ_c^{(t)})` is independent of `t ∈ (0, ∞)`. -/
theorem riemannHypothesis_iff_negIndex_heatArchState_const {c : ℝ} (hc : 0 < c) :
    RiemannHypothesis ↔
      ∀ s t, 0 < s → 0 < t → negIndex (heatArchState c s) = negIndex (heatArchState c t) := by
  rw [riemannHypothesis_iff_forall_negIndex_heatArchState_eq_one hc]
  constructor
  · intro h s t hs ht
    rw [h s hs, h t ht]
  · intro h t ht
    rw [h t (1 / 8) ht (by norm_num), negIndex_heatArchState_eq_one_of_eighth_le hc le_rfl]

/-- **Small-time Pontryagin domination (`t → 0⁺`)**: the Pontryagin index of Weil's `t = 0`
archimedean state `φ_c` is bounded above by `liminf_{t → 0⁺} κ(φ_c^{(t)})` (with strict gap equal
to the multiplicity excess of any multiple off-line zeros of `ξ`, which split into distinct zeros
of `H_t` for small `t > 0`). -/
theorem negIndex_weilArchState_le_liminf_heatArchState {c : ℝ} (hc : 0 < c) :
    negIndex (weilArchState c) ≤ liminf (fun t => negIndex (heatArchState c t)) (𝓝[>] 0) := by
  rw [negIndex_weilArchState_eq_add_one hc]
  rcases eq_or_ne (negIndex zetaKernel) ⊤ with htop | hne
  · rw [htop, top_add, top_le_iff]
    by_contra hL
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp hL
    have hev := (tendsto_atTop.mp (tendsto_collisionMassAfter_of_negIndex_eq_top htop))
      (2 * (M + 1))
    have hle : ((M + 1 : ℕ) : ℕ∞) ≤ liminf (fun t => negIndex (heatArchState c t)) (𝓝[>] 0) := by
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
      rw [← nonrealZeroCount_eq_collisionMassAfter htpos,
        ← two_mul_heatRightZeroMultiplicity t] at ht
      rw [negIndex_heatArchState_eq hc htpos]
      norm_cast
      omega
    rw [← hM] at hle
    norm_cast at hle
    omega
  · have hlt : negIndex zetaKernel < ⊤ := lt_top_iff_ne_top.mpr hne
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hk]
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [two_mul_negIndex_zetaKernel_le_collisionMassAfter hlt,
      self_mem_nhdsWithin] with t ht htpos
    rw [← hk, ← nonrealZeroCount_eq_collisionMassAfter htpos,
      ← two_mul_heatRightZeroMultiplicity t] at ht
    have hnat : 2 * k ≤ 2 * heatRightZeroMultiplicity t := by exact_mod_cast ht
    rw [negIndex_heatArchState_eq hc htpos]
    norm_cast
    omega

/-- **Finite-index stratum equivalence**: Weil's `t = 0` archimedean state `φ_c` (`c > 0`) has
finite Pontryagin index if and only if `κ(φ_c^{(t)})` is uniformly bounded for all `t > 0`. -/
theorem negIndex_weilArchState_lt_top_iff_bdd {c : ℝ} (hc : 0 < c) :
    negIndex (weilArchState c) < ⊤ ↔
      ∃ M : ℕ, ∀ t > 0, negIndex (heatArchState c t) ≤ M := by
  constructor
  · intro h
    have hζ : negIndex zetaKernel < ⊤ := by
      rw [negIndex_weilArchState_eq_add_one hc] at h
      exact lt_of_le_of_lt le_self_add h
    obtain ⟨hfin, -, hev⟩ := eventually_collisionMassAfter_eq_index hζ
    set K := hfin.toFinset.card + ∑ ρ ∈ hfin.toFinset, (ArithmeticOrientationGeometry.xiMult ρ - 1)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
    set t₀ := δ / 2
    have ht₀ : 0 < t₀ := by positivity
    have hK_eq : ∀ s, 0 < s → s < δ → negIndex (heatArchState c s) = ((K + 1 : ℕ) : ℕ∞) := by
      intro s hs0 hsδ
      have hdist : dist s 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
        exact hsδ
      have hcoll := hball hdist (mem_Ioi.mpr hs0)
      rw [← nonrealZeroCount_eq_collisionMassAfter hs0,
        ← two_mul_heatRightZeroMultiplicity s] at hcoll
      have hm : heatRightZeroMultiplicity s = K := by omega
      rw [negIndex_heatArchState_eq hc hs0, hm]
    refine ⟨K + 1, fun t ht => ?_⟩
    rcases lt_or_ge t δ with htδ | htδ
    · exact (hK_eq t ht htδ).le
    · calc negIndex (heatArchState c t)
          ≤ negIndex (heatArchState c t₀) :=
            antitoneOn_negIndex_heatArchState hc (mem_Ioi.mpr ht₀) (mem_Ioi.mpr ht)
              (by dsimp [t₀]; linarith)
        _ = ((K + 1 : ℕ) : ℕ∞) := hK_eq t₀ ht₀ (by dsimp [t₀]; linarith)
  · rintro ⟨M, hM⟩
    by_contra hnot
    have htop_weil : negIndex (weilArchState c) = ⊤ := top_unique (not_lt.mp hnot)
    have htop_ζ : negIndex zetaKernel = ⊤ := by
      by_contra hne
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
      rw [negIndex_weilArchState_eq_add_one hc, ← hk] at htop_weil
      exact ENat.coe_ne_top (k + 1) htop_weil
    have hev := (tendsto_atTop.mp (tendsto_collisionMassAfter_of_negIndex_eq_top htop_ζ))
      (2 * (M + 1))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
    set t₀ := δ / 2
    have ht₀ : 0 < t₀ := by positivity
    have hdist : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀]
      dsimp [t₀]; linarith
    have hcoll := hball hdist (mem_Ioi.mpr ht₀)
    rw [← nonrealZeroCount_eq_collisionMassAfter ht₀,
      ← two_mul_heatRightZeroMultiplicity t₀] at hcoll
    have hbound := hM t₀ ht₀
    rw [negIndex_heatArchState_eq hc ht₀] at hbound
    have hnat : heatRightZeroMultiplicity t₀ + 1 ≤ M := by exact_mod_cast hbound
    omega

end GaloisForLFunctions.AdelicKreinGeometry
