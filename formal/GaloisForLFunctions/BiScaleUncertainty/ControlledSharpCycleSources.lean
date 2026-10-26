import GaloisForLFunctions.BiScaleUncertainty.SharpCycleDetectionOrder
import GaloisForLFunctions.BiScaleUncertainty.FirstOrderEnergyCollar
import GaloisForLFunctions.BiScaleUncertainty.DistantCopyEnergyTopology

/-!
# Exact-order ambiguity inside a controlled class of actual smooth sources

Every separated signed copy of the fixed unit-support seed belongs to one
constructed singular-energy class. Its central normalized correlation is the
seed's, its support radius is at most separation plus one, and normalized
closed observations retain the exact floor-plus-one detection threshold.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.SharpCycle
set_option autoImplicit false

/-- One actual energy ceiling contains every separation and every copy amplitude. -/
def controlledSource (T : Ioi (2 : ℝ)) (a : ℝ) : LevyEnergySource (copyEnergyCeiling seed 1) where
  source := source T a
  smooth := (source_smooth T a).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  mass_pos := source_mass_pos T a
  energy_le := normalizedArchEnergy_subtractCopy_le_copyEnergyCeiling
    (f := (seed : ℝ → ℝ)) seedBump.contDiff seed.hasCompactSupport seed_mass_pos
    (D := 1) (fun x hx => (seed_correlation_eq_zero_iff x).mpr hx.le)
    (by linarith only [show (2 : ℝ) < T from T.property]) a

/-- The entire fixed unit neighborhood has exactly the seed's normalized correlation. -/
theorem controlledSource_central (T : Ioi (2 : ℝ)) (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    (controlledSource T a).correlation x = autocorr seed x / autocorr seed 0 := by
  change autocorr (source T a) x / autocorr (source T a) 0 = _
  rw [source_central T a ⟨x, abs_lt.mp hx⟩, source_mass]
  have ha : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [ha, seed_mass_pos.ne']

/-- Actual correlations vanish at and beyond separation plus one. -/
theorem controlledSource_outside (T : Ioi (2 : ℝ)) (a : ℝ) {x : ℝ}
    (hx : (T : ℝ) + 1 ≤ |x|) : (controlledSource T a).correlation x = 0 := by
  have hT : 0 < (T : ℝ) := by linarith only [show (2 : ℝ) < T from T.property]
  have hzero : autocorr seed x = 0 := (seed_correlation_eq_zero_iff x).mpr (by linarith only [hx, hT])
  have hlower : |x| ≤ |x - T| + (T : ℝ) := by
    simpa only [sub_add_cancel, abs_of_pos hT] using abs_add_le (x - T) (T : ℝ)
  have hupper : |x| ≤ |x + T| + (T : ℝ) := by
    simpa only [add_sub_cancel_right, abs_of_pos hT] using abs_sub (x + T) (T : ℝ)
  have hl : autocorr seed (x - T) = 0 :=
    (seed_correlation_eq_zero_iff _).mpr (by linarith only [hx, hlower])
  have hr : autocorr seed (x + T) = 0 :=
    (seed_correlation_eq_zero_iff _).mpr (by linarith only [hx, hupper])
  change autocorr (source T a) x / autocorr (source T a) 0 = 0
  rw [source_correlation, hzero, hl, hr]
  ring

/-- One fixed positive collar works for all separations and amplitudes. -/
theorem controlledSource_uniform_collar (T : Ioi (2 : ℝ)) (a : ℝ) {x : ℝ}
    (hx : |x| ≤ EnergyCycle.firstOrderCollarRadius (copyEnergyCeiling seed 1)) :
    1 / 2 < (controlledSource T a).correlation x :=
  EnergyCycle.correlation_firstOrderCollar _ hx

/-- One fixed singular-energy modulus works for all the actual smooth copy sources. -/
theorem controlledSource_uniform_modulus (T : Ioi (2 : ℝ)) (a : ℝ)
    {η x y : ℝ} (hη : 0 < η) (hη1 : η < 1) (hxy : |x - y| ≤ η) :
    |(controlledSource T a).correlation x - (controlledSource T a).correlation y| ≤
      Real.sqrt (8 * copyEnergyCeiling seed 1 /
        (Real.exp (-(1 / 2 : ℝ)) * (-Real.log η))) :=
  EnergyCycle.correlation_logarithmic_modulus _ hη hη1 hxy

/-- Equal actual masses preserve detection under closed-product normalization. -/
theorem controlledSource_value_ne_iff (T : Ioi (2 : ℝ)) (a : ℝ) (l : List ℝ)
    (hs : l.sum = 0) :
    EnergyCycle.value (controlledSource T (-a)) l ≠ EnergyCycle.value (controlledSource T a) l ↔
      SeparatedCycle.rawProduct (source T (-a)) l ≠ SeparatedCycle.rawProduct (source T a) l := by
  rw [EnergyCycle.value_eq_normalized, EnergyCycle.value_eq_normalized]
  change SeparatedCycle.closedProduct (source T (-a)) l / autocorr (source T (-a)) 0 ^ l.length ≠
      SeparatedCycle.closedProduct (source T a) l / autocorr (source T a) 0 ^ l.length ↔ _
  have he : autocorr (source T (-a)) 0 = autocorr (source T a) 0 := by
    rw [source_mass, source_mass, neg_sq]
  rw [he, SeparatedCycle.closedProduct, SeparatedCycle.closedProduct, if_pos hs, if_pos hs]
  have hd : autocorr (source T a) 0 ^ l.length ≠ 0 := pow_ne_zero _ (source_mass_pos T a).ne'
  constructor
  · intro hn heq
    exact hn (congrArg (fun z : ℝ => z / autocorr (source T a) 0 ^ l.length) heq)
  · intro hn heq
    apply hn
    have hm := congrArg (fun z : ℝ => z * autocorr (source T a) 0 ^ l.length) heq
    simpa only [div_mul_cancel₀ _ hd] using hm

/-- The exact floor threshold persists for literal normalized observations in the controlled class. -/
theorem controlledSource_detects_iff (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ) :
    (∃ l : List ℝ, l.length = n ∧ l.sum = 0 ∧
      EnergyCycle.value (controlledSource T (-a)) l ≠ EnergyCycle.value (controlledSource T a) l) ↔
      a ≠ 0 ∧ ⌊(T : ℝ)⌋₊ < n := by
  rw [← detects_iff_floor T a n]
  constructor
  · rintro ⟨l, hl, hs, hn⟩
    exact ⟨l, hl, hs, (controlledSource_value_ne_iff T a l hs).mp hn⟩
  · rintro ⟨l, hl, hs, hn⟩
    exact ⟨l, hl, hs, (controlledSource_value_ne_iff T a l hs).mpr hn⟩

/-- The controlled class is explicitly nonempty and has arbitrarily large exact detection order. -/
theorem exists_controlled_sources_above_order (m : ℕ) :
    ∃ T : Ioi (2 : ℝ),
      (∀ n : ℕ, n ≤ m → ∀ l : List ℝ, l.length = n → l.sum = 0 →
        EnergyCycle.value (controlledSource T (-1)) l = EnergyCycle.value (controlledSource T 1) l) ∧
      (∃ l : List ℝ, l.length = firstOrder T ∧ l.sum = 0 ∧
        EnergyCycle.value (controlledSource T (-1)) l ≠ EnergyCycle.value (controlledSource T 1) l) := by
  let T : Ioi (2 : ℝ) := ⟨(m : ℝ) + 3, by
    change (2 : ℝ) < (m : ℝ) + 3
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith only [hm]⟩
  refine ⟨T, ?_, ?_⟩
  · intro n hn l hl hs
    by_contra he
    have hd := (controlledSource_detects_iff T 1 n).mp ⟨l, hl, hs, he⟩
    have hm : m ≤ ⌊(T : ℝ)⌋₊ := (Nat.le_floor_iff (by positivity : 0 ≤ (T : ℝ))).mpr
      (by dsimp [T]; linarith only [Nat.cast_nonneg (α := ℝ) m])
    omega
  · apply (controlledSource_detects_iff T 1 (firstOrder T)).mpr
    exact ⟨one_ne_zero, by unfold firstOrder; omega⟩

end GaloisForLFunctions.BiScaleUncertainty.SharpCycle
