import GaloisForLFunctions.RHTower.XiWardAERectangleAdmissibility

/-!
# Canonical transverse coarea scan for Ward source rectangles

The lower centered spectral coordinate of a strict-right Xi zero is its negative transverse
displacement.  This file fixes a source-defined scan of that interval.  The arctangent chart
maps the real scan parameter bijectively onto `(0, 1/2)`; a band of scan length `L` covers every
transverse displacement for exactly a parameter interval of length `L`.

The preceding almost-everywhere edge theorem makes the resulting moving contour levels lawful
without choosing them from the divisor.  This establishes the transverse component of a
canonical source producer only.  No response identity, height-cutoff transport, or energy bound
is asserted here.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- A canonical source-defined coordinate from the real scan line onto the positive transverse
half of the Xi critical strip. -/
def xiWardTransverseLevel (t : ℝ) : ℝ :=
  1 / 4 + Real.arctan t / (2 * Real.pi)

/-- The inverse chart on the positive transverse half-strip. -/
def xiWardTransverseCoordinate (a : ℝ) : ℝ :=
  Real.tan (2 * Real.pi * (a - 1 / 4))

/-- The transverse level remains strictly inside the source strip. -/
theorem xiWardTransverseLevel_mem_Ioo (t : ℝ) :
    xiWardTransverseLevel t ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
  unfold xiWardTransverseLevel
  have hden : 0 < 2 * Real.pi := by positivity
  have hlo := div_lt_div_of_pos_right (Real.neg_pi_div_two_lt_arctan t) hden
  have hhi := div_lt_div_of_pos_right (Real.arctan_lt_pi_div_two t) hden
  have hleft : (-(Real.pi / 2)) / (2 * Real.pi) = -(1 / 4 : ℝ) := by
    field_simp [Real.pi_ne_zero]
    norm_num
  have hright : (Real.pi / 2) / (2 * Real.pi) = (1 / 4 : ℝ) := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [hleft] at hlo
  rw [hright] at hhi
  constructor <;> linarith

/-- The canonical transverse chart is strictly monotone, hence contains no hidden
divisor-dependent choice. -/
theorem xiWardTransverseLevel_strictMono : StrictMono xiWardTransverseLevel := by
  intro s t hst
  unfold xiWardTransverseLevel
  have hden : 0 < 2 * Real.pi := by positivity
  linarith [div_lt_div_of_pos_right (Real.arctan_strictMono hst) hden]

theorem xiWardTransverseLevel_injective : Function.Injective xiWardTransverseLevel :=
  xiWardTransverseLevel_strictMono.injective

/-- The explicit tangent chart is an inverse for every positive transverse displacement. -/
theorem xiWardTransverseLevel_coordinate
    {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    xiWardTransverseLevel (xiWardTransverseCoordinate a) = a := by
  unfold xiWardTransverseLevel xiWardTransverseCoordinate
  have hlow : -(Real.pi / 2) < 2 * Real.pi * (a - 1 / 4) := by
    nlinarith [Real.pi_pos, ha.1]
  have hhigh : 2 * Real.pi * (a - 1 / 4) < Real.pi / 2 := by
    nlinarith [Real.pi_pos, ha.2]
  rw [Real.arctan_tan hlow hhigh]
  field_simp [Real.pi_ne_zero]
  ring

/-- A single canonical scan band has no zero-chosen transverse endpoints. -/
def xiWardCanonicalTransverseLower (L t : ℝ) : ℝ :=
  -xiWardTransverseLevel (t + L)

def xiWardCanonicalTransverseUpper (t : ℝ) : ℝ :=
  -xiWardTransverseLevel t

/-- Positive scan length gives an honest lower-half source rectangle band. -/
theorem xiWardCanonicalTransverseLower_lt_upper
    {L : ℝ} (hL : 0 < L) (t : ℝ) :
    xiWardCanonicalTransverseLower L t < xiWardCanonicalTransverseUpper t := by
  unfold xiWardCanonicalTransverseLower xiWardCanonicalTransverseUpper
  rw [neg_lt_neg_iff]
  exact xiWardTransverseLevel_strictMono (by linarith)

/-- Both canonical transverse edges lie strictly in the lower source half-strip. -/
theorem xiWardCanonicalTransverse_edges_mem_lowerHalf
    (L t : ℝ) :
    xiWardCanonicalTransverseLower L t ∈ Set.Ioo (-(1 / 2 : ℝ)) 0 ∧
      xiWardCanonicalTransverseUpper t ∈ Set.Ioo (-(1 / 2 : ℝ)) 0 := by
  unfold xiWardCanonicalTransverseLower xiWardCanonicalTransverseUpper
  obtain ⟨hL0, hLhalf⟩ := xiWardTransverseLevel_mem_Ioo (t + L)
  obtain ⟨ht0, hthalf⟩ := xiWardTransverseLevel_mem_Ioo t
  constructor <;> constructor <;> linarith

/-- Exact coarea selection law.  A transverse displacement `a` is in the canonical band at
parameter `t` precisely for the scan interval `[coordinate(a)-L, coordinate(a)]`, whose
ordinary length is `L`. -/
theorem mem_xiWardCanonicalTransverseBand_iff
    {a L t : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    a ∈ Set.Icc (xiWardTransverseLevel t) (xiWardTransverseLevel (t + L)) ↔
      t ∈ Set.Icc (xiWardTransverseCoordinate a - L)
        (xiWardTransverseCoordinate a) := by
  rw [Set.mem_Icc, Set.mem_Icc]
  have hcoord := xiWardTransverseLevel_coordinate ha
  have hleft : xiWardTransverseLevel t ≤ a ↔
      t ≤ xiWardTransverseCoordinate a := by
    simpa only [hcoord] using
      (xiWardTransverseLevel_strictMono.le_iff_le :
        xiWardTransverseLevel t ≤
          xiWardTransverseLevel (xiWardTransverseCoordinate a) ↔
            t ≤ xiWardTransverseCoordinate a)
  have hright : a ≤ xiWardTransverseLevel (t + L) ↔
      xiWardTransverseCoordinate a ≤ t + L := by
    simpa only [hcoord] using
      (xiWardTransverseLevel_strictMono.le_iff_le :
        xiWardTransverseLevel (xiWardTransverseCoordinate a) ≤
          xiWardTransverseLevel (t + L) ↔
            xiWardTransverseCoordinate a ≤ t + L)
  rw [hleft, hright]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The lower centered spectral ordinate `-a` is selected by exactly the same canonical scan
interval. -/
theorem neg_mem_xiWardCanonicalTransverseBand_iff
    {a L t : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    -a ∈ Set.Icc (xiWardCanonicalTransverseLower L t)
      (xiWardCanonicalTransverseUpper t) ↔
      t ∈ Set.Icc (xiWardTransverseCoordinate a - L)
        (xiWardTransverseCoordinate a) := by
  rw [xiWardCanonicalTransverseLower, xiWardCanonicalTransverseUpper,
    Set.mem_Icc]
  constructor
  · rintro ⟨hlower, hupper⟩
    apply (mem_xiWardCanonicalTransverseBand_iff ha).mp
    constructor <;> linarith
  · intro h
    obtain ⟨hleft, hright⟩ :=
      (mem_xiWardCanonicalTransverseBand_iff ha).mpr h
    constructor <;> linarith

end

end RHTower
