import GaloisForLFunctions.ScaleSignedIncidenceCriticality.OrdinateDataIsBlindToTheWidth
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.DepthResolutionNeedsAScaleBound

/-!
# The dichotomy is about coordinates, not boundedness

The programme explains its floors by boundedness: a bounded aperture, a bounded height, a bounded
radius, and the information sitting at infinity. `OrdinateDataIsBlindToTheWidth` already shows that
the explanation is incomplete — the exact ordinate set is unbounded data and still certifies nothing
about the width. This module completes the picture by computing what that unbounded reading *does*
determine, and it is the scale.

On the lattice family the ordinate set is `{2πk/L}`, and two such sets coincide only for equal
spacings (`sdScale_eq_of_ordinates_eq`): the ordinate reading **determines the scale exactly**,
with no bound on anything. At the same time it is constant in the depth
(`sdOrdinates_eq_of_sdScale_eq`), so its limit for the depth is the trivial `½`
(`resolutionLimit_sdDepth_sdOrdinates`).

`theDichotomyIsAboutCoordinates` states the pair. The conclusion is that the field's dichotomy is
not a boundedness phenomenon at all: it separates the *vertical* coordinate of a configuration,
which every natural reading sees and sees exactly, from the *horizontal* one, which carries RH and
which only readings coupling the two — the Weil form at unbounded aperture, a trans-Nyquist level, a
mass-and-certificate pair — can reach. Unbounded vertical data is worth no more than bounded
vertical data, and that is why the aperture ladder's limit is not the width.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

/-! ### 1. The ordinate reading of a lattice datum -/

/-- The ordinate set of the lattice datum `p`, computed from its scale alone. -/
def sdOrdinates (p : ScaleDepthDatum) : Set ℝ :=
  Set.range (fun k : ℤ => (k : ℝ) * (2 * Real.pi / sdScale p))

/-- **The reading is constant in the depth.** -/
theorem sdOrdinates_eq_of_sdScale_eq {p q : ScaleDepthDatum} (h : sdScale p = sdScale q) :
    sdOrdinates p = sdOrdinates q := by
  rw [sdOrdinates, sdOrdinates, h]

/-! ### 2. The reading determines the scale -/

/-- Two integer lattices of positive spacing coincide only if the spacings do. -/
theorem spacing_eq_of_range_eq {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (h : Set.range (fun k : ℤ => (k : ℝ) * c) = Set.range (fun k : ℤ => (k : ℝ) * c')) :
    c = c' := by
  obtain ⟨m, hm⟩ : c ∈ Set.range (fun k : ℤ => (k : ℝ) * c') := by
    rw [← h]; exact ⟨1, by norm_num⟩
  obtain ⟨n, hn⟩ : c' ∈ Set.range (fun k : ℤ => (k : ℝ) * c) := by
    rw [h]; exact ⟨1, by norm_num⟩
  have hm' : (m : ℝ) * c' = c := hm
  have hn' : (n : ℝ) * c = c' := hn
  have hmpos : (0 : ℤ) < m := by
    by_contra hcon
    have hle : (m : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hcon
    nlinarith [hm']
  have hnpos : (0 : ℤ) < n := by
    by_contra hcon
    have hle : (n : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hcon
    nlinarith [hn']
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ m)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ n)
  nlinarith [hm', hn']

/-- **The ordinate reading determines the scale exactly** — with no bound on the data. -/
theorem sdScale_eq_of_ordinates_eq {p q : ScaleDepthDatum} (h : sdOrdinates p = sdOrdinates q) :
    sdScale p = sdScale q := by
  have hp : (0 : ℝ) < 2 * Real.pi / sdScale p := by
    have := p.2.1; positivity
  have hq : (0 : ℝ) < 2 * Real.pi / sdScale q := by
    have := q.2.1; positivity
  have hc := spacing_eq_of_range_eq hp hq h
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpne : sdScale p ≠ 0 := ne_of_gt p.2.1
  have hqne : sdScale q ≠ 0 := ne_of_gt q.2.1
  rw [div_eq_div_iff hpne hqne] at hc
  exact (mul_left_cancel₀ (ne_of_gt hpi) hc).symm

/-! ### 3. The depth is untouched -/

/-- **The unbounded ordinate reading still has the trivial limit for the depth.** -/
theorem resolutionLimit_sdDepth_sdOrdinates (p : ScaleDepthDatum) :
    resolutionLimit sdDepth sdOrdinates p = 1 / 2 := by
  refine resolutionLimit_eq_of_mem_shadow_of_max (fun q => q.2.2.2) (e := ?_) ?_ ?_
  · exact ⟨(sdScale p, 1 / 2), p.2.1, by norm_num, le_rfl⟩
  · exact sdOrdinates_eq_of_sdScale_eq rfl
  · rfl

/-! ### 4. The dichotomy -/

/-- **The dichotomy is about coordinates.** One and the same unbounded reading determines the scale
exactly and the depth not at all: the split is between the vertical and the horizontal coordinate of
a configuration, not between bounded and unbounded data. -/
theorem theDichotomyIsAboutCoordinates (p : ScaleDepthDatum) :
    (∀ q : ScaleDepthDatum, sdOrdinates p = sdOrdinates q → sdScale p = sdScale q) ∧
      resolutionLimit sdDepth sdOrdinates p = 1 / 2 :=
  ⟨fun _ h => sdScale_eq_of_ordinates_eq h, resolutionLimit_sdDepth_sdOrdinates p⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
