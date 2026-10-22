import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheApertureCertificateIsBlindInEveryUnit
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.SquareRootThreshold.RelaxedHodgeExponentOfOffLineLattices

/-!
# The square-root precision law

This module is the quantitative core of the aperture face: how much certificate strength buys how
much depth.

Above the Nyquist aperture of a configuration the deficit of the Weil form becomes visible, and its
size is `weilFloorThreshold L δ = 2L(cosh(δL) − 1)` — quadratic in the depth, not linear
(`cube_mul_sq_le_weilFloorThreshold`). Inverting it gives the exact resolution limit of the depth
for a level-`η` certificate at a known scale,

`min ½ (arcosh(1 + η/(2L))/L)`   (`resolutionLimit_depth_levelReading`),

whence the **square-root law**: a certificate of strength `η` certifies only
`δ ≤ √(η/L³)` (`depthResolution_le_sqrt`). A mechanism aiming at depth `β` must therefore produce a
deficit of order `β²L³` — the budget of `theDeficitBudget`, which no adaptive policy escapes.

The same quadratic law read along the aperture axis gives the scale-free form. The deficit grows
like `e^{2δa}`, so the depth is *half the exponential growth rate of the deficit*
(`deficitRateBelow_of_lt`, `not_deficitRateBelow_of_lt`), and the infimum of the admissible rates is
exactly the depth (`sInf_rateSet`). That infimum is constant on dilation orbits and separates them,
so it is the faithful, scale-free reading whose existence `TheDepthIsTheCompleteDilationInvariant`
demands — the first quantity of the field with both properties.

A uniform deficit bound, by contrast, already passes the gate at every aperture
(`uniformDeficit`), so uniformity is not strength: only a rate is.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold
open Zeta23 _root_.RHTower

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

/-! ### 0. The two-coordinate lattice datum -/

/-- A lattice datum with both coordinates free: scale `L` and depth `δ`. -/
def ScaleDepthDatum : Type := {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2}

/-- The scale coordinate. -/
def sdScale (p : ScaleDepthDatum) : ℝ := p.1.1

/-- The depth coordinate: the invariant RH is about. -/
def sdDepth (p : ScaleDepthDatum) : ℝ := p.1.2

/-- The configuration of the datum. -/
noncomputable def sdConfig (p : ScaleDepthDatum) : ZeroConfig :=
  offLineLatticeConfig p.2.1 p.2.2.1 p.2.2.2

/-- The level-`η` Weil floor on aperture `a`, read on both coordinates. -/
def scaleDepthReading (a η : ℝ) (p : ScaleDepthDatum) : Prop :=
  WeilFloorAtLevel (sdConfig p) a η

/-- **The automatic region.** A datum whose scale satisfies `2a ≤ L` is Weil-positive at aperture
`a`, hence has a floor at every nonnegative level, whatever its depth. -/
theorem scaleDepthReading_of_dense {a η : ℝ} (hη : 0 ≤ η) (p : ScaleDepthDatum)
    (hp : 2 * a ≤ sdScale p) : scaleDepthReading a η p := by
  intro f hf hfs _ _
  have hpos : 0 ≤ ((sdConfig p).W f f).re :=
    (offLineLattice_weil_positive_iff p.2.1 p.2.2.1 p.2.2.2 a).mpr
      (by simp only [sdScale] at hp; linarith) f hf hfs
  have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  nlinarith

-- from TheDepthBecomesVisibleJustAboveTheNyquistAperture.lean
/-! ### 1. The lattice floor at the second aliasing step -/

/-- **The rank-two lattice floor.** At the second aliasing step the floor is `2 − 2cosh(δL)`,
read off the closed form `n − sinh(nδL)/sinh(δL)` of the lattice ground energy. -/
theorem latticeFloor_two {L δ : ℝ} (hδL : 0 < δ * L) :
    latticeFloor L δ 2 = 2 - 2 * Real.cosh (δ * L) := by
  have hs : Real.sinh (δ * L) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hδL)
  rw [latticeFloor_eq hδL 2]
  push_cast
  rw [show (2 : ℝ) * (δ * L) = 2 * (δ * L) from rfl, Real.sinh_two_mul]
  field_simp

/-! ### 2. The threshold just above the Nyquist aperture -/

/-- On `(L/2, L]` the aliasing index is exactly `2`. -/
theorem ceil_two_mul_div_eq_two {L a : ℝ} (hL : 0 < L) (ha : L / 2 < a) (haL : a ≤ L) :
    ⌈2 * a / L⌉₊ = 2 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor
  · rw [show ((2 : ℕ) - 1 : ℕ) = 1 from rfl]
    push_cast
    rw [lt_div_iff₀ hL]
    linarith
  · push_cast
    rw [div_le_iff₀ hL]
    linarith

/-- **The exact level threshold just above the Nyquist aperture.** -/
theorem weilFloorAtLevel_offLineLattice_iff_cosh {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : L / 2 < a) (haL : a ≤ L) (η : ℝ) :
    WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a η ↔
      2 * L * (Real.cosh (δ * L) - 1) ≤ η := by
  rw [offLineLattice_weilFloor_iff hL hδ hδ' ha η, ceil_two_mul_div_eq_two hL ha haL,
    latticeFloor_two (by positivity : 0 < δ * L)]
  constructor <;> intro h <;> nlinarith [h]

/-! ### 3. The threshold reads the depth -/

/-- The level threshold of a lattice at the second aliasing step. -/
noncomputable def weilFloorThreshold (L δ : ℝ) : ℝ := 2 * L * (Real.cosh (δ * L) - 1)

/-- **The threshold is strictly increasing in the depth.** -/
theorem weilFloorThreshold_strictMono {L : ℝ} (hL : 0 < L) {δ δ' : ℝ} (hδ : 0 < δ)
    (hlt : δ < δ') : weilFloorThreshold L δ < weilFloorThreshold L δ' := by
  have hδ'0 : 0 < δ' := hδ.trans hlt
  have hcosh : Real.cosh (δ * L) < Real.cosh (δ' * L) := by
    rw [Real.cosh_lt_cosh, abs_of_pos (by positivity : 0 < δ * L),
      abs_of_pos (by positivity : 0 < δ' * L)]
    exact mul_lt_mul_of_pos_right hlt hL
  have hprod : 0 < 2 * L * (Real.cosh (δ' * L) - Real.cosh (δ * L)) :=
    mul_pos (by linarith) (by linarith)
  simp only [weilFloorThreshold]
  linarith

/-- **The depth enters quadratically.** The first visible trace of an off-line pair of depth `δ`
is a deficit of order `L³δ²`: it has no first-order term in the depth. A mechanism with only
first-order sensitivity to the position of a zero therefore sees nothing, however far above the
Nyquist aperture it works. -/
theorem cube_mul_sq_le_weilFloorThreshold {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    L ^ 3 * δ ^ 2 ≤ weilFloorThreshold L δ := by
  set y : ℝ := δ * L / 2 with hy
  have hy0 : 0 ≤ y := by simp only [hy]; positivity
  have hsinh : y ≤ Real.sinh y := Real.self_le_sinh_iff.mpr hy0
  have hsq : y ^ 2 ≤ Real.sinh y ^ 2 := by nlinarith
  have hcosh : Real.cosh (δ * L) = 2 * Real.sinh y ^ 2 + 1 := by
    have h2 : δ * L = 2 * y := by simp only [hy]; ring
    rw [h2, Real.cosh_two_mul, Real.cosh_sq]
    ring
  have hykey : (δ * L) ^ 2 / 4 = y ^ 2 := by simp only [hy]; ring
  rw [weilFloorThreshold, hcosh]
  nlinarith [hsq, hykey, hL.le, sq_nonneg (δ * L)]

/-- Distinct depths are separated by an explicit level: at `η` between the two thresholds the
shallower lattice has the floor and the deeper one does not. -/
theorem exists_level_separating_depths {L : ℝ} (hL : 0 < L) {δ δ' : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hlt : δ < δ') (hδ'' : δ' ≤ 1 / 2) {a : ℝ} (ha : L / 2 < a) (haL : a ≤ L) :
    ∃ η : ℝ, WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a η ∧
      ¬ WeilFloorAtLevel (offLineLatticeConfig hL (hδ.trans hlt) hδ'') a η := by
  refine ⟨weilFloorThreshold L δ, ?_, ?_⟩
  · exact (weilFloorAtLevel_offLineLattice_iff_cosh hL hδ hδ' ha haL _).mpr le_rfl
  · intro h
    have := (weilFloorAtLevel_offLineLattice_iff_cosh hL (hδ.trans hlt) hδ'' ha haL _).mp h
    exact absurd this (not_le.mpr (weilFloorThreshold_strictMono hL hδ hlt))

/-- **The graded trans-Nyquist reading determines the depth.** The threshold map is injective on
depths, so the level at which a lattice acquires a Weil floor just above its Nyquist aperture
recovers its depth exactly. -/
theorem weilFloorThreshold_injOn {L : ℝ} (hL : 0 < L) :
    Set.InjOn (weilFloorThreshold L) (Ioc 0 (1 / 2)) := by
  intro δ hδ δ' hδ' heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd heq (ne_of_lt (weilFloorThreshold_strictMono hL hδ.1 h))
  · exact absurd heq.symm (ne_of_lt (weilFloorThreshold_strictMono hL hδ'.1 h))

/-- **The frontier of the aperture face.** Below the Nyquist aperture no certificate sees the
depth, however large its gap; just above it, the level threshold determines the depth exactly. -/
theorem theApertureFaceFrontier {L : ℝ} (hL : 0 < L) {a : ℝ} (ha : L / 2 < a) (haL : a ≤ L) :
    (∀ b η : ℝ, 0 < b → ∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain b η Z) ∧
      Set.InjOn (weilFloorThreshold L) (Ioc 0 (1 / 2)) ∧
      ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ hδ' : δ ≤ 1 / 2, ∀ η : ℝ,
        (WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a η ↔ weilFloorThreshold L δ ≤ η) :=
  ⟨fun _ η hb => exists_width_eq_half_apertureGain hb η, weilFloorThreshold_injOn hL,
    fun _ hδ hδ' η => weilFloorAtLevel_offLineLattice_iff_cosh hL hδ hδ' ha haL η⟩

-- from TheSquareRootPrecisionLawOfDepthResolution.lean
/-! ### 1. The depth resolution of a level -/

/-- The depth a level-`η` certificate resolves at scale `L`: the inverse of the threshold law. -/
noncomputable def depthResolution (L η : ℝ) : ℝ := Real.arcosh (1 + η / (2 * L)) / L

/-- **The threshold law inverted.** A depth has deficit at most `η` exactly when it is at most the
depth resolution of `η`. -/
theorem weilFloorThreshold_le_iff {L δ η : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hη : 0 ≤ η) :
    weilFloorThreshold L δ ≤ η ↔ δ ≤ depthResolution L η := by
  have h2L : (0 : ℝ) < 2 * L := by linarith
  have h1 : (1 : ℝ) ≤ 1 + η / (2 * L) := by
    have h : 0 ≤ η / (2 * L) := by positivity
    linarith
  have harc : Real.cosh (Real.arcosh (1 + η / (2 * L))) = 1 + η / (2 * L) := Real.cosh_arcosh h1
  have harcnn : 0 ≤ Real.arcosh (1 + η / (2 * L)) := Real.arcosh_nonneg h1
  have hδL : (0 : ℝ) < δ * L := by positivity
  have hstep : weilFloorThreshold L δ ≤ η ↔ Real.cosh (δ * L) ≤ 1 + η / (2 * L) := by
    rw [weilFloorThreshold]
    constructor
    · intro h
      have hd : Real.cosh (δ * L) - 1 ≤ η / (2 * L) := by
        rw [le_div_iff₀ h2L]; nlinarith
      linarith
    · intro h
      have hd : Real.cosh (δ * L) - 1 ≤ η / (2 * L) := by linarith
      rw [le_div_iff₀ h2L] at hd
      nlinarith
  rw [hstep, ← harc, Real.cosh_le_cosh, abs_of_pos hδL, abs_of_nonneg harcnn,
    depthResolution, le_div_iff₀ hL]

/-- The depth resolution is strictly positive at a positive level. -/
theorem depthResolution_pos {L η : ℝ} (hL : 0 < L) (hη : 0 < η) : 0 < depthResolution L η := by
  have h1 : (1 : ℝ) < 1 + η / (2 * L) := by
    have h : 0 < η / (2 * L) := by positivity
    linarith
  exact div_pos (Real.arcosh_pos h1) hL

/-! ### 2. The data of a depth family at one scale -/

/-- A depth of the lattice family: the datum a method studying a configuration of known scale
actually varies. -/
def DepthDatum : Type := {δ : ℝ // 0 < δ ∧ δ ≤ 1 / 2}

/-- The invariant: the depth itself. -/
def depth (d : DepthDatum) : ℝ := d.1

/-- The reading: the level-`η` Weil floor of the lattice of spacing `2π/L` on aperture `a`. -/
def levelReading {L : ℝ} (hL : 0 < L) (a η : ℝ) (d : DepthDatum) : Prop :=
  WeilFloorAtLevel (offLineLatticeConfig hL d.2.1 d.2.2) a η

/-- **The reading is exactly a depth bound.** -/
theorem levelReading_iff {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a) (haL : a ≤ L) (hη : 0 ≤ η)
    (d : DepthDatum) : levelReading hL a η d ↔ depth d ≤ depthResolution L η := by
  rw [levelReading, weilFloorAtLevel_offLineLattice_iff_cosh hL d.2.1 d.2.2 ha haL,
    ← weilFloorThreshold, weilFloorThreshold_le_iff hL d.2.1 hη]
  rfl

/-! ### 3. The exact limit -/

/-- **The first nontrivial exact limit.** A level-`η` certificate just above the Nyquist aperture
resolves the depth to exactly `min ½ (depthResolution L η)`, and the value is attained. -/
theorem resolutionLimit_depth_levelReading {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a)
    (haL : a ≤ L) (hη : 0 ≤ η) {d₀ : DepthDatum} (hd₀ : levelReading hL a η d₀) :
    resolutionLimit depth (levelReading hL a η) d₀ = min (1 / 2) (depthResolution L η) := by
  have hD : 0 < depthResolution L η :=
    lt_of_lt_of_le d₀.2.1 ((levelReading_iff hL ha haL hη d₀).mp hd₀)
  have hm0 : 0 < min (1 / 2 : ℝ) (depthResolution L η) := lt_min (by norm_num) hD
  have hmle : min (1 / 2 : ℝ) (depthResolution L η) ≤ 1 / 2 := min_le_left _ _
  have hbdd : BddAbove (depth '' shadow (levelReading hL a η) d₀) := by
    refine ⟨min (1 / 2) (depthResolution L η), ?_⟩
    rintro x ⟨d, hd, rfl⟩
    have hread : levelReading hL a η d := (mem_shadow_iff.mp hd) ▸ hd₀
    exact le_min d.2.2 ((levelReading_iff hL ha haL hη d).mp hread)
  refine le_antisymm (csSup_le (shadow_image_nonempty depth (levelReading hL a η) d₀) ?_) ?_
  · rintro x ⟨d, hd, rfl⟩
    have hread : levelReading hL a η d := (mem_shadow_iff.mp hd) ▸ hd₀
    exact le_min d.2.2 ((levelReading_iff hL ha haL hη d).mp hread)
  · set d₁ : DepthDatum := ⟨min (1 / 2) (depthResolution L η), hm0, hmle⟩ with hd₁
    have hread₁ : levelReading hL a η d₁ :=
      (levelReading_iff hL ha haL hη d₁).mpr (min_le_right _ _)
    have hmem : d₁ ∈ shadow (levelReading hL a η) d₀ := propext (iff_of_true hread₁ hd₀)
    exact le_csSup hbdd ⟨d₁, hmem, rfl⟩

/-! ### 4. The square-root precision law -/

/-- **The square-root precision law.** The depth resolution of a level is at most the square root
of the level divided by the cube of the scale. -/
theorem depthResolution_le_sqrt {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) :
    depthResolution L η ≤ Real.sqrt (η / L ^ 3) := by
  rcases le_or_gt (depthResolution L η) 0 with h | h
  · exact h.trans (Real.sqrt_nonneg _)
  · have hthr : weilFloorThreshold L (depthResolution L η) ≤ η :=
      (weilFloorThreshold_le_iff hL h hη).mpr le_rfl
    have hcube := cube_mul_sq_le_weilFloorThreshold hL h
    have hsq : depthResolution L η ^ 2 ≤ η / L ^ 3 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < L ^ 3)]
      nlinarith
    calc depthResolution L η = Real.sqrt (depthResolution L η ^ 2) :=
          (Real.sqrt_sq h.le).symm
      _ ≤ Real.sqrt (η / L ^ 3) := Real.sqrt_le_sqrt hsq

/-- **The limit obeys the square-root law.** A method controlling the Weil deficit to precision
`η` at scale `L` certifies no depth bound sharper than `√(η/L³)`. -/
theorem resolutionLimit_depth_levelReading_le_sqrt {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a)
    (haL : a ≤ L) (hη : 0 ≤ η) {d₀ : DepthDatum} (hd₀ : levelReading hL a η d₀) :
    resolutionLimit depth (levelReading hL a η) d₀ ≤ Real.sqrt (η / L ^ 3) := by
  rw [resolutionLimit_depth_levelReading hL ha haL hη hd₀]
  exact (min_le_right _ _).trans (depthResolution_le_sqrt hL hη)

-- from AUniformDeficitBoundAlreadyPassesTheGate.lean
/-! ### 1. Two elementary hyperbolic estimates -/

/-- `1 + y²/2 ≤ cosh y` for `y ≥ 0`, from `y/2 ≤ sinh (y/2)`. -/
theorem one_add_sq_half_le_cosh {y : ℝ} (hy : 0 ≤ y) : 1 + y ^ 2 / 2 ≤ Real.cosh y := by
  have hhalf : (0 : ℝ) ≤ y / 2 := by linarith
  have h1 : y / 2 ≤ Real.sinh (y / 2) := Real.self_le_sinh_iff.mpr hhalf
  have h0 : (0 : ℝ) ≤ Real.sinh (y / 2) := Real.sinh_nonneg_iff.mpr hhalf
  have h3 : Real.cosh y = 2 * Real.sinh (y / 2) ^ 2 + 1 := by
    have hc := Real.cosh_two_mul (y / 2)
    rw [show 2 * (y / 2) = y by ring, Real.cosh_sq] at hc
    linarith
  rw [h3]
  nlinarith

/-- `cosh (m x) · sinh x ≤ sinh ((m+1) x)` for `x ≥ 0`: drop the nonnegative summand of the
addition formula. -/
theorem cosh_mul_sinh_le_sinh_succ {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    Real.cosh ((m : ℝ) * x) * Real.sinh x ≤ Real.sinh (((m : ℝ) + 1) * x) := by
  have hmx : (0 : ℝ) ≤ (m : ℝ) * x := by positivity
  have hsplit : ((m : ℝ) + 1) * x = (m : ℝ) * x + x := by ring
  rw [hsplit, Real.sinh_add]
  have h1 : (0 : ℝ) ≤ Real.sinh ((m : ℝ) * x) := Real.sinh_nonneg_iff.mpr hmx
  have h2 : (0 : ℝ) < Real.cosh x := Real.cosh_pos x
  nlinarith

/-! ### 2. The lattice deficit grows without bound -/

/-- **The deficit of an off-line lattice outgrows every level.** At a suitable aperture the
polar-constrained Weil form of a depth-`δ` lattice falls below `−η‖f‖²`. -/
theorem exists_aperture_not_weilFloorAtLevel {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (η : ℝ) :
    ∃ a : ℝ, L / 2 < a ∧ ¬ WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a η := by
  have hx0 : (0 : ℝ) < δ * L := by positivity
  have hs0 : (0 : ℝ) < Real.sinh (δ * L) := Real.sinh_pos_iff.mpr hx0
  obtain ⟨m, hm⟩ := exists_nat_gt (max (4 / (δ * L) ^ 2) ((η + 1) / L))
  have hm1 : (4 : ℝ) / (δ * L) ^ 2 < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hm2 : (η + 1) / L < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_trans (by positivity) hm1
  have hmsq : (2 : ℝ) ≤ (m : ℝ) * (δ * L) ^ 2 / 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (δ * L) ^ 2)] at hm1
    linarith
  have hmL : η + 1 ≤ L * (m : ℝ) := by
    rw [div_lt_iff₀ hL] at hm2
    linarith
  -- the aliasing index `m + 1`
  have hratio : Real.cosh ((m : ℝ) * (δ * L)) ≤
      Real.sinh (((m : ℝ) + 1) * (δ * L)) / Real.sinh (δ * L) :=
    (le_div_iff₀ hs0).mpr (cosh_mul_sinh_le_sinh_succ hx0.le m)
  have hcosh : 1 + ((m : ℝ) * (δ * L)) ^ 2 / 2 ≤ Real.cosh ((m : ℝ) * (δ * L)) :=
    one_add_sq_half_le_cosh (by positivity)
  have hfloor : latticeFloor L δ (m + 1) ≤ (m : ℝ) - ((m : ℝ) * (δ * L)) ^ 2 / 2 := by
    rw [latticeFloor_eq hx0 (m + 1)]
    push_cast
    linarith
  have hdeep : η < -(L * latticeFloor L δ (m + 1)) := by
    have hmul := mul_le_mul_of_nonneg_left hfloor hL.le
    have hkey : L * ((m : ℝ) * ((m : ℝ) * (δ * L) ^ 2 / 2 - 1)) ≤
        -(L * latticeFloor L δ (m + 1)) := by linarith
    have hextra : 0 ≤ L * (m : ℝ) * ((m : ℝ) * (δ * L) ^ 2 / 2 - 2) :=
      mul_nonneg (mul_nonneg hL.le hmpos.le) (by linarith)
    linarith
  refine ⟨((m : ℝ) + 1) * L / 2, by nlinarith [hmpos], ?_⟩
  have hceil : ⌈2 * (((m : ℝ) + 1) * L / 2) / L⌉₊ = m + 1 := by
    rw [show 2 * (((m : ℝ) + 1) * L / 2) / L = ((m : ℝ) + 1) by field_simp]
    rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
  rw [offLineLattice_weilFloor_iff hL hδ hδ' (by nlinarith [hmpos] : L / 2 < ((m : ℝ) + 1) * L / 2)
    η, hceil]
  exact not_le.mpr hdeep

/-! ### 3. The uniform-deficit reading -/

/-- A **uniform deficit bound**: at every aperture the polar-constrained Weil form is at least
`−η‖f‖²`, with one level `η` for all apertures. No positivity is asked for. -/
def uniformDeficit (η : ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∀ a : ℝ, 0 < a → WeilFloorAtLevel Z.1 a η

/-- The on-line lattice satisfies it at every nonnegative level. -/
theorem uniformDeficit_onLineLattice {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) :
    uniformDeficit η (onLineLattice hL) := by
  intro a _ f hf hfs _ _
  have hpos : 0 ≤ ((onLineLattice hL).1.W f f).re := re_W_onLineLatticeConfig_nonneg hL f
  have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  nlinarith

/-- **No off-line lattice satisfies it, at any level.** -/
theorem not_uniformDeficit_offLineLattice {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (η : ℝ) : ¬ uniformDeficit η (offLineLattice hL hδ hδ') := by
  intro h
  obtain ⟨a, ha, hnot⟩ := exists_aperture_not_weilFloorAtLevel hL hδ hδ' η
  exact hnot (h a (by linarith))

/-! ### 4. It passes the gate -/

/-- **The uniform-deficit reading passes the trans-Nyquist gate.** It separates the pair that every
bounded-aperture reading identifies — a depth-`½` lattice against the on-line lattice — at every
level, while requiring no positivity. -/
theorem uniformDeficit_separates_the_transNyquist_pair {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) :
    uniformDeficit η (offLineLattice hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl) ≠
      uniformDeficit η (onLineLattice hL) := by
  intro heq
  exact not_uniformDeficit_offLineLattice hL (by norm_num) le_rfl η
    (heq ▸ uniformDeficit_onLineLattice hL hη)

/-- **The content of the unbounded certificate is the absence of growth.** The reading asks for no
margin and no positivity, only that one deficit level serve every aperture; that already decides
the trans-Nyquist pair, which no bounded reading does at any level or in any unit. -/
theorem theGateIsPassedByNonGrowth {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) :
    uniformDeficit η (onLineLattice hL) ∧
      (∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ hδ' : δ ≤ 1 / 2,
        ¬ uniformDeficit η (offLineLattice hL hδ hδ')) ∧
      uniformDeficit η (offLineLattice hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl) ≠
        uniformDeficit η (onLineLattice hL) :=
  ⟨uniformDeficit_onLineLattice hL hη,
    fun _ hδ hδ' => not_uniformDeficit_offLineLattice hL hδ hδ' η,
    uniformDeficit_separates_the_transNyquist_pair hL hη⟩

-- from TheDepthIsHalfTheDeficitGrowthRate.lean
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

-- from TheRateReadingIsFaithfulAndScaleFree.lean
/-! ### 1. The set of admissible rates -/

/-- The nonnegative rates at which the datum's deficit is `O(e^{2βa})`. -/
def rateSet (p : ScaleDepthDatum) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ deficitRateBelow β (offLineLattice p.2.1 p.2.2.1 p.2.2.2)}

theorem mem_rateSet_of_lt {p : ScaleDepthDatum} {β : ℝ} (hβ0 : 0 ≤ β) (hβ : sdDepth p < β) :
    β ∈ rateSet p :=
  ⟨hβ0, deficitRateBelow_of_lt p.2.1 p.2.2.1 p.2.2.2 hβ⟩

theorem notMem_rateSet_of_lt {p : ScaleDepthDatum} {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β < sdDepth p) : β ∉ rateSet p := fun hmem =>
  not_deficitRateBelow_of_lt p.2.1 p.2.2.1 p.2.2.2 hβ0 hβ hmem.2

/-! ### 2. The infimum is the depth -/

/-- **The infimum of the admissible rates is the depth.** -/
theorem sInf_rateSet (p : ScaleDepthDatum) : sInf (rateSet p) = sdDepth p := by
  have hd : (0 : ℝ) < sdDepth p := p.2.2.1
  have hne : (rateSet p).Nonempty :=
    ⟨sdDepth p + 1, mem_rateSet_of_lt (by linarith) (by linarith)⟩
  have hlb : ∀ β ∈ rateSet p, sdDepth p ≤ β := by
    intro β hβ
    by_contra hcon
    exact notMem_rateSet_of_lt hβ.1 (not_le.mp hcon) hβ
  refine le_antisymm ?_ (le_csInf hne hlb)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact csInf_le ⟨sdDepth p, hlb⟩ (mem_rateSet_of_lt (by linarith) (by linarith))

/-! ### 3. Faithful and scale-free -/

/-- **The rate reading separates the depths.** -/
theorem sdDepth_eq_of_rateSet_eq {p q : ScaleDepthDatum} (h : rateSet p = rateSet q) :
    sdDepth p = sdDepth q := by
  rw [← sInf_rateSet p, ← sInf_rateSet q, h]

/-- **The rate reading is scale-free**: it depends on the datum only through its depth, which is the
complete dilation invariant. -/
theorem sInf_rateSet_eq_of_sdDepth_eq {p q : ScaleDepthDatum} (h : sdDepth p = sdDepth q) :
    sInf (rateSet p) = sInf (rateSet q) := by
  rw [sInf_rateSet, sInf_rateSet, h]

/-- **The rate reading is the answer.** Its infimum is the depth, so it is constant on dilation
orbits and separates them — the two properties `TheDepthIsTheCompleteDilationInvariant` shows a
resolving reading must have, and which no scale reading of the field has. -/
theorem theRateReadingIsTheAnswer :
    (∀ p : ScaleDepthDatum, sInf (rateSet p) = sdDepth p) ∧
      (∀ p q : ScaleDepthDatum, rateSet p = rateSet q → sdDepth p = sdDepth q) ∧
      ∀ p q : ScaleDepthDatum, sdDepth p = sdDepth q → sInf (rateSet p) = sInf (rateSet q) :=
  ⟨sInf_rateSet, fun _ _ h => sdDepth_eq_of_rateSet_eq h,
    fun _ _ h => sInf_rateSet_eq_of_sdDepth_eq h⟩

-- from TheDeficitBudgetOfAnAdaptivePolicy.lean
/-! ### 1. Policies and the readings they define -/

/-- A policy reads, at each datum, the Weil floor at an aperture and a level chosen from the
datum's own scale. -/
def adaptiveReading (A η : ℝ → ℝ) (p : ScaleDepthDatum) : Prop :=
  WeilFloorAtLevel (sdConfig p) (A (sdScale p)) (η (sdScale p))

/-- A policy is *scale-matched* when its aperture lies just above the Nyquist aperture of the scale
it is applied to, and its level is nonnegative. -/
structure ScaleMatched (A η : ℝ → ℝ) : Prop where
  aperture_lb : ∀ L : ℝ, 0 < L → L / 2 < A L
  aperture_ub : ∀ L : ℝ, 0 < L → A L ≤ L
  level_nonneg : ∀ L : ℝ, 0 < L → 0 ≤ η L

/-- **A scale-matched policy reads exactly a depth bound.** -/
theorem adaptiveReading_iff {A η : ℝ → ℝ} (h : ScaleMatched A η) (p : ScaleDepthDatum) :
    adaptiveReading A η p ↔ sdDepth p ≤ depthResolution (sdScale p) (η (sdScale p)) := by
  have h1 := weilFloorAtLevel_offLineLattice_iff_cosh (L := sdScale p) (δ := sdDepth p)
    p.2.1 p.2.2.1 p.2.2.2 (h.aperture_lb _ p.2.1) (h.aperture_ub _ p.2.1) (η (sdScale p))
  have h2 := weilFloorThreshold_le_iff (L := sdScale p) (δ := sdDepth p) (η := η (sdScale p))
    p.2.1 p.2.2.1 (h.level_nonneg _ p.2.1)
  exact h1.trans h2

/-! ### 2. The budget suffices -/

/-- **The budget law, sufficiency.** A level policy bounded by `β² L³` certifies the depth bound
`β`: every datum the policy admits has depth at most `β`. -/
theorem certifies_of_budget {A η : ℝ → ℝ} (h : ScaleMatched A η) {β : ℝ} (hβ : 0 ≤ β)
    (hbudget : ∀ L : ℝ, 0 < L → η L ≤ β ^ 2 * L ^ 3) {p₀ : ScaleDepthDatum}
    (hp₀ : adaptiveReading A η p₀) :
    Certifies sdDepth (adaptiveReading A η) p₀ β := by
  intro p hp
  have hread : adaptiveReading A η p := (mem_shadow_iff.mp hp) ▸ hp₀
  have hL : 0 < sdScale p := p.2.1
  have hdepth := (adaptiveReading_iff h p).mp hread
  have hsqrt : depthResolution (sdScale p) (η (sdScale p)) ≤
      Real.sqrt (η (sdScale p) / sdScale p ^ 3) :=
    depthResolution_le_sqrt hL (h.level_nonneg _ hL)
  have hquot : η (sdScale p) / sdScale p ^ 3 ≤ β ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < sdScale p ^ 3)]
    exact hbudget _ hL
  have hfin : Real.sqrt (η (sdScale p) / sdScale p ^ 3) ≤ β := by
    have hs := Real.sqrt_le_sqrt hquot
    rwa [Real.sqrt_sq hβ] at hs
  exact hdepth.trans (hsqrt.trans hfin)

/-! ### 3. The budget is sharp -/

/-- **The budget law, sharpness.** If at some scale the level reaches the exact threshold of a depth
`β' > β`, the policy admits a datum of depth `β'` and certifies nothing below it. -/
theorem not_certifies_of_budget_violation {A η : ℝ → ℝ} (h : ScaleMatched A η) {β : ℝ}
    {L β' : ℝ} (hL : 0 < L) (hβ'0 : 0 < β') (hβ' : β' ≤ 1 / 2) (hlt : β < β')
    (hreach : weilFloorThreshold L β' ≤ η L) {p₀ : ScaleDepthDatum}
    (hp₀ : adaptiveReading A η p₀) :
    ¬ Certifies sdDepth (adaptiveReading A η) p₀ β := by
  set p : ScaleDepthDatum := ⟨(L, β'), hL, hβ'0, hβ'⟩ with hp
  have hread : adaptiveReading A η p :=
    (adaptiveReading_iff h p).mpr
      ((weilFloorThreshold_le_iff hL hβ'0 (h.level_nonneg _ hL)).mp hreach)
  have hmem : p ∈ shadow (adaptiveReading A η) p₀ := propext (iff_of_true hread hp₀)
  intro hcert
  exact absurd (hcert p hmem) (not_le.mpr hlt)

/-! ### 4. The law -/

/-- **The deficit budget law.** For a scale-matched policy the reading is exactly a depth bound; a
level budget `β² L³` certifies depth `β`; and reaching the threshold of a larger depth at any one
scale destroys the certificate. The tolerable deficit is cubic in the scale and quadratic in the
depth. -/
theorem theDeficitBudgetLaw {A η : ℝ → ℝ} (h : ScaleMatched A η) {β : ℝ} (hβ : 0 ≤ β)
    {p₀ : ScaleDepthDatum} (hp₀ : adaptiveReading A η p₀) :
    (∀ p : ScaleDepthDatum, adaptiveReading A η p ↔
        sdDepth p ≤ depthResolution (sdScale p) (η (sdScale p))) ∧
      ((∀ L : ℝ, 0 < L → η L ≤ β ^ 2 * L ^ 3) →
        Certifies sdDepth (adaptiveReading A η) p₀ β) ∧
      ∀ L β' : ℝ, 0 < L → 0 < β' → β' ≤ 1 / 2 → β < β' → weilFloorThreshold L β' ≤ η L →
        ¬ Certifies sdDepth (adaptiveReading A η) p₀ β :=
  ⟨adaptiveReading_iff h, fun hb => certifies_of_budget h hβ hb hp₀,
    fun _ _ hL hβ'0 hβ' hlt hreach =>
      not_certifies_of_budget_violation h hL hβ'0 hβ' hlt hreach hp₀⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
