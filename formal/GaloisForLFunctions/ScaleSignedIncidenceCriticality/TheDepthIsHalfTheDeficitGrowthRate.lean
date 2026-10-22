import GaloisForLFunctions.ScaleSignedIncidenceCriticality.AUniformDeficitBoundAlreadyPassesTheGate

/-!
# The depth is half the growth rate of the deficit

A uniform deficit bound passes the trans-Nyquist gate because an off-line lattice's deficit grows
with the aperture. This module identifies the growth exactly: it is exponential, and its rate is
twice the depth. Both bounds are already in the corpus
(`SquareRootThreshold.latticeFloor_aperture_bounds`); what is new is that the rate — unlike every
prefactor — carries no trace of the scale, so it is the dilation invariant of
`TheDepthIsTheCompleteDilationInvariant` made quantitative.

* `weilFloorAtLevel_offLineLattice_exp` and `not_weilFloorAtLevel_offLineLattice_of_lt_exp` put the
  two bounds in the reading language: the deficit at aperture `a` lies between
  `L e^{δ(2a−L)} − 2a − L` and `(2a + L) e^{2δa}`.
* `deficitRateBelow` is the reading "the deficit is `O(e^{2βa})`". It holds at every rate above the
  depth (`deficitRateBelow_of_lt`) and fails at every nonnegative rate below it
  (`not_deficitRateBelow_of_lt`), so the depth is exactly the infimum of the admissible rates
  (`theDepthIsHalfTheDeficitGrowthRate`).

This is the positive counterpart of the programme's floors. The scale readings are blind to the
depth because they are coordinates along the dilation orbits; the *growth rate* of the deficit is
constant on orbits and separates them, and it is read off the same Weil data the floors are about —
only asymptotically in the aperture rather than at one aperture. A mechanism that estimates how
fast its deficit grows, rather than how large it is, is reading the invariant.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Two elementary exponential estimates -/

/-- `1 + x + x²/4 ≤ exp x` for `x ≥ 0`, by squaring `1 + x/2 ≤ exp (x/2)`. -/
theorem one_add_add_sq_quarter_le_exp {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 4 ≤ Real.exp x := by
  have h1 : 1 + x / 2 ≤ Real.exp (x / 2) := by
    have := Real.add_one_le_exp (x / 2)
    linarith
  have h0 : (0 : ℝ) ≤ 1 + x / 2 := by linarith
  have hsq : (1 + x / 2) ^ 2 ≤ Real.exp (x / 2) ^ 2 := by nlinarith
  have hexp : Real.exp (x / 2) ^ 2 = Real.exp x := by
    rw [sq, ← Real.exp_add, show x / 2 + x / 2 = x by ring]
  nlinarith [hsq, hexp]

/-- A linear function is dominated by an exponential with an explicit constant. -/
theorem linear_le_const_mul_exp {ε L a : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) (ha : 0 ≤ a) :
    2 * a + L ≤ (2 / ε + L) * Real.exp (ε * a) := by
  have h1 : 1 + ε * a ≤ Real.exp (ε * a) := by
    have := Real.add_one_le_exp (ε * a); linarith
  have h0 : (1 : ℝ) ≤ Real.exp (ε * a) := Real.one_le_exp (by positivity)
  have hinv : (0 : ℝ) ≤ 2 / ε := by positivity
  have hA : 2 / ε * (1 + ε * a) ≤ 2 / ε * Real.exp (ε * a) :=
    mul_le_mul_of_nonneg_left h1 hinv
  have hB : L * 1 ≤ L * Real.exp (ε * a) := mul_le_mul_of_nonneg_left h0 hL
  have hkey : 2 / ε * (1 + ε * a) = 2 / ε + 2 * a := by field_simp
  have hexpand : (2 / ε + L) * Real.exp (ε * a) =
      2 / ε * Real.exp (ε * a) + L * Real.exp (ε * a) := by ring
  rw [hexpand]
  linarith

/-! ### 2. The deficit in the reading language -/

/-- **Upper bound.** The deficit at aperture `a` never exceeds `(2a + L) e^{2δa}`. -/
theorem weilFloorAtLevel_offLineLattice_exp {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (ha : 0 < a) :
    WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a ((2 * a + L) * Real.exp (2 * δ * a)) := by
  rcases le_or_gt a (L / 2) with hsub | hsup
  · intro f hf hfs _ _
    have hpos : 0 ≤ ((offLineLatticeConfig hL hδ hδ').W f f).re :=
      (offLineLattice_weil_positive_iff hL hδ hδ' a).mpr hsub f hf hfs
    have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
      MeasureTheory.integral_nonneg fun _ => by positivity
    have hlev : (0 : ℝ) ≤ (2 * a + L) * Real.exp (2 * δ * a) := by positivity
    nlinarith
  · rw [offLineLattice_weilFloor_iff hL hδ hδ' hsup]
    have hbd := (latticeFloor_aperture_bounds hL hδ ha).1
    linarith

/-- **Lower bound.** Below `L e^{δ(2a−L)} − 2a − L` no level holds: the deficit is at least that. -/
theorem not_weilFloorAtLevel_offLineLattice_of_lt_exp {L δ a η : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (ha : L / 2 < a)
    (hη : η < L * Real.exp (δ * (2 * a - L)) - 2 * a - L) :
    ¬ WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a η := by
  rw [offLineLattice_weilFloor_iff hL hδ hδ' ha]
  have hbd := (latticeFloor_aperture_bounds hL hδ (by linarith : 0 < a)).2
  exact not_le.mpr (by linarith)

/-! ### 3. The rate reading -/

/-- The reading "the deficit grows no faster than `e^{2βa}`". -/
def deficitRateBelow (β : ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → WeilFloorAtLevel Z.1 a (C * Real.exp (2 * β * a))

/-- A larger admissible rate is a weaker requirement. -/
theorem deficitRateBelow_mono {β β' : ℝ} (hββ' : β ≤ β') {Z : TemperedZeroConfig}
    (h : deficitRateBelow β Z) : deficitRateBelow β' Z := by
  obtain ⟨C, hC, hall⟩ := h
  refine ⟨C, hC, fun a ha => ?_⟩
  intro f hf hfs hp hm
  have hle : C * Real.exp (2 * β * a) ≤ C * Real.exp (2 * β' * a) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC.le
  have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  have hbase := hall a ha f hf hfs hp hm
  have hstep : C * Real.exp (2 * β * a) * ∫ u, ‖f u‖ ^ 2 ≤
      C * Real.exp (2 * β' * a) * ∫ u, ‖f u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hle hint
  linarith

/-- **Every rate above the depth is admissible.** -/
theorem deficitRateBelow_of_lt {L δ β : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hβ : δ < β) : deficitRateBelow β (offLineLattice hL hδ hδ') := by
  have hε0 : (0 : ℝ) < 2 * (β - δ) := by linarith
  refine ⟨2 / (2 * (β - δ)) + L, by positivity, fun a ha => ?_⟩
  intro f hf hfs hp hm
  have hup := weilFloorAtLevel_offLineLattice_exp hL hδ hδ' ha f hf hfs hp hm
  have hlin : 2 * a + L ≤ (2 / (2 * (β - δ)) + L) * Real.exp (2 * (β - δ) * a) :=
    linear_le_const_mul_exp hε0 hL.le ha.le
  have hsplit : (2 / (2 * (β - δ)) + L) * Real.exp (2 * β * a) =
      ((2 / (2 * (β - δ)) + L) * Real.exp (2 * (β - δ) * a)) * Real.exp (2 * δ * a) := by
    rw [show ((2 / (2 * (β - δ)) + L) * Real.exp (2 * (β - δ) * a)) * Real.exp (2 * δ * a)
          = (2 / (2 * (β - δ)) + L) *
            (Real.exp (2 * (β - δ) * a) * Real.exp (2 * δ * a)) by ring,
      ← Real.exp_add, show 2 * (β - δ) * a + 2 * δ * a = 2 * β * a by ring]
  have hexp0 : (0 : ℝ) < Real.exp (2 * δ * a) := Real.exp_pos _
  have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  have hmono : (2 * a + L) * Real.exp (2 * δ * a) ≤
      (2 / (2 * (β - δ)) + L) * Real.exp (2 * β * a) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hlin hexp0.le
  have hstep : (2 * a + L) * Real.exp (2 * δ * a) * ∫ u, ‖f u‖ ^ 2 ≤
      (2 / (2 * (β - δ)) + L) * Real.exp (2 * β * a) * ∫ u, ‖f u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hmono hint
  have hup' : -((2 * a + L) * Real.exp (2 * δ * a) * ∫ u, ‖f u‖ ^ 2) ≤
      ((offLineLattice hL hδ hδ').1.W f f).re := hup
  linarith

/-- **No nonnegative rate below the depth is admissible.** -/
theorem not_deficitRateBelow_of_lt {L δ β : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hβ0 : 0 ≤ β) (hβ : β < δ) : ¬ deficitRateBelow β (offLineLattice hL hδ hδ') := by
  rintro ⟨C, hC, hall⟩
  set A : ℝ := L * Real.exp (-(δ * L)) with hA
  set c : ℝ := 2 * (δ - β) with hc
  have hA0 : 0 < A := by rw [hA]; positivity
  have hc0 : 0 < c := by rw [hc]; linarith
  set a : ℝ := max (L + 1) (4 * (2 + C + L) / (A * c ^ 2)) with hadef
  have haL1 : L + 1 ≤ a := le_max_left _ _
  have ha1 : (1 : ℝ) ≤ a := by linarith
  have haL : L / 2 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hbig : 4 * (2 + C + L) / (A * c ^ 2) ≤ a := le_max_right _ _
  have hslack : 2 + C + L ≤ A * c ^ 2 * a / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have h := hbig
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < A * c ^ 2)] at h
    nlinarith [h]
  have hquad : 1 + c * a + (c * a) ^ 2 / 4 ≤ Real.exp (c * a) :=
    one_add_add_sq_quarter_le_exp (by positivity)
  have hkey : C + 2 * a + L < A * Real.exp (c * a) := by
    have h1 : A * (1 + c * a + (c * a) ^ 2 / 4) ≤ A * Real.exp (c * a) :=
      mul_le_mul_of_nonneg_left hquad hA0.le
    have h2 : a * (2 + C + L) ≤ a * (A * c ^ 2 * a / 4) :=
      mul_le_mul_of_nonneg_left hslack ha0.le
    have h3 : 0 < A * c * a := by positivity
    have h4 : 0 ≤ (a - 1) * (C + L) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2, h3, h4]
  have hE0 : (0 : ℝ) < Real.exp (2 * β * a) := Real.exp_pos _
  have hE1 : (1 : ℝ) ≤ Real.exp (2 * β * a) := Real.one_le_exp (by positivity)
  have hid : Real.exp (δ * (2 * a - L)) =
      Real.exp (-(δ * L)) * (Real.exp (c * a) * Real.exp (2 * β * a)) := by
    rw [← Real.exp_add, ← Real.exp_add, hc]
    congr 1
    ring
  have hLHS : L * Real.exp (δ * (2 * a - L)) = (A * Real.exp (c * a)) * Real.exp (2 * β * a) := by
    rw [hid, hA]; ring
  have hlow : C * Real.exp (2 * β * a) < L * Real.exp (δ * (2 * a - L)) - 2 * a - L := by
    rw [hLHS]
    have hmul := mul_lt_mul_of_pos_right hkey hE0
    have hslack2 : 0 ≤ (2 * a + L) * (Real.exp (2 * β * a) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hmul, hslack2]
  exact not_weilFloorAtLevel_offLineLattice_of_lt_exp hL hδ hδ' haL hlow (hall a ha0)

/-! ### 4. The dictionary -/

/-- **The depth is half the growth rate of the deficit.** Every rate above the depth is admissible
and no nonnegative rate below it is, so the depth is the infimum of the admissible rates — a
quantity that, unlike every prefactor, does not involve the scale. -/
theorem theDepthIsHalfTheDeficitGrowthRate {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    (∀ β : ℝ, δ < β → deficitRateBelow β (offLineLattice hL hδ hδ')) ∧
      (∀ β : ℝ, 0 ≤ β → β < δ → ¬ deficitRateBelow β (offLineLattice hL hδ hδ')) ∧
      width (offLineLattice hL hδ hδ') = δ :=
  ⟨fun _ hβ => deficitRateBelow_of_lt hL hδ hδ' hβ,
    fun _ hβ0 hβ => not_deficitRateBelow_of_lt hL hδ hδ' hβ0 hβ,
    width_offLineLattice hL hδ hδ'⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
