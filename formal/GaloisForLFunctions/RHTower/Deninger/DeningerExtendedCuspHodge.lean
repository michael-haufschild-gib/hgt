import GaloisForLFunctions.RHTower.Deninger.DeningerProLogCuspHodge
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The extended cusp domain and its Green boundary pairing

On the cylindrical model of the prime cusp the coefficients of the logarithmic generator are
constant, so its energy density against the `b`-volume `dx dθ / x` is a constant multiple of
`x^{-1}`.  That is not integrable on the collar, but weighting by `x^{ε}` on the form — hence
`x^{2ε}` on the energy — makes it integrable for every positive `ε`, with total weighted energy
`1/(2ε)`.  So the logarithmic generator lies in every weighted space `x^{-ε}L²` and in none of them
for `ε = 0`: it is extended harmonic boundary data, not an `L²` bulk class, and the Poincaré
residue reads exactly its coefficient.

The boundary Green form of a leading packet is the leafwise wedge.  It is skew, every line is
isotropic for it, the symplectic orthogonal of a nonzero line is that line itself — so boundary
lines are Lagrangian — and the Hodge star carries a line to a transverse Lagrangian complement,
since the wedge of a nonzero form against its star is positive.

* `deningerLogEnergy_integrable_iff` : the weighted energy `(4)`.
* `deningerLogEnergy_integral` : its value `1/(2ε)`.
* `deningerGreenBoundary_orthogonal_eq_span` : boundary lines are Lagrangian `(6)`.
* `deningerGreenBoundary_star_transverse` : the star exchanges complementary Lagrangians.
-/

namespace RHTower

open MeasureTheory Set intervalIntegral

section ExtendedWeight

/-- **`(4)`: the weighted energy of the logarithmic generator.**  Against the `b`-volume the energy
density is `x^{2ε - 1}`, integrable on the collar exactly for positive weight.  In particular the
unweighted energy diverges and every positive weight is finite. -/
theorem deningerLogEnergy_integrable_iff {ε : ℝ} :
    IntegrableOn (fun x : ℝ => x ^ (2 * ε - 1)) (Ioo (0 : ℝ) 1) ↔ 0 < ε := by
  rw [integrableOn_Ioo_rpow_iff zero_lt_one]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- The unweighted energy of the logarithmic generator diverges: it is not an `L²` class. -/
theorem deningerLogEnergy_not_integrable :
    ¬ IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo (0 : ℝ) 1) := by
  intro hint
  have h : IntegrableOn (fun x : ℝ => x ^ (2 * (0 : ℝ) - 1)) (Ioo (0 : ℝ) 1) := by
    have hrw : (2 * (0 : ℝ) - 1) = (-1 : ℝ) := by ring
    rw [hrw]
    exact hint
  have := deningerLogEnergy_integrable_iff.mp h
  exact lt_irrefl 0 this

/-- The weighted energy is finite for every positive weight. -/
theorem deningerLogEnergy_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => x ^ (2 * ε - 1)) (Ioo (0 : ℝ) 1) :=
  deningerLogEnergy_integrable_iff.mpr hε

/-- **The weighted energy is `1/(2ε)`.** -/
theorem deningerLogEnergy_integral {ε : ℝ} (hε : 0 < ε) :
    ∫ x in (0 : ℝ)..1, x ^ (2 * ε - 1) = 1 / (2 * ε) := by
  have hgt : (-1 : ℝ) < 2 * ε - 1 := by linarith
  have hne : (2 * ε - 1) + 1 ≠ 0 := by
    intro hcon
    have : ε = 0 := by linarith
    exact (ne_of_gt hε) this
  rw [integral_rpow (Or.inl hgt)]
  have h1 : (1 : ℝ) ^ ((2 * ε - 1) + 1) = 1 := Real.one_rpow _
  have h0 : (0 : ℝ) ^ ((2 * ε - 1) + 1) = 0 := Real.zero_rpow hne
  rw [h1, h0]
  have hsum : (2 * ε - 1) + 1 = 2 * ε := by ring
  rw [hsum]
  ring

end ExtendedWeight

section GreenBoundary

/-- **The boundary Green form `(6)` is the leafwise wedge**, and every line is isotropic for it. -/
theorem deningerGreenBoundary_self (v : ℝ × ℝ) : deningerLeafWedge v v = 0 := by
  show v.1 * v.2 - v.2 * v.1 = 0
  ring

theorem deningerGreenBoundary_skew (v w : ℝ × ℝ) :
    deningerLeafWedge v w = -deningerLeafWedge w v := by
  show v.1 * w.2 - v.2 * w.1 = -(w.1 * v.2 - w.2 * v.1)
  ring

/-- **Boundary lines are Lagrangian.**  The symplectic orthogonal of a nonzero leading packet is
the line it spans, so the boundary values of extended harmonic forms are a maximal isotropic
subspace for the Green form. -/
theorem deningerGreenBoundary_orthogonal_eq_span {v : ℝ × ℝ} (hv : v ≠ 0) :
    {w : ℝ × ℝ | deningerLeafWedge v w = 0} = (Submodule.span ℝ {v} : Set (ℝ × ℝ)) := by
  have hne : ¬ (v.1 = 0 ∧ v.2 = 0) := by
    intro h
    exact hv (Prod.ext h.1 h.2)
  ext w
  constructor
  · intro hw
    have hw' : v.1 * w.2 - v.2 * w.1 = 0 := hw
    rcases not_and_or.mp hne with h1 | h2
    · refine Submodule.mem_span_singleton.mpr ⟨w.1 / v.1, ?_⟩
      refine Prod.ext ?_ ?_
      · show w.1 / v.1 * v.1 = w.1
        field_simp
      · show w.1 / v.1 * v.2 = w.2
        field_simp
        linarith [hw']
    · refine Submodule.mem_span_singleton.mpr ⟨w.2 / v.2, ?_⟩
      refine Prod.ext ?_ ?_
      · show w.2 / v.2 * v.1 = w.1
        field_simp
        linarith [hw']
      · show w.2 / v.2 * v.2 = w.2
        field_simp
  · intro hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    show v.1 * (c * v.2) - v.2 * (c * v.1) = 0
    ring

/-- **The star exchanges complementary Lagrangians.**  The Green form of a nonzero packet against
its Hodge star is positive, so the two boundary lines are transverse. -/
theorem deningerGreenBoundary_star_transverse {v : ℝ × ℝ} (hv : v ≠ 0) :
    0 < deningerLeafWedge v (deningerLeafStar v) :=
  deningerLeafWedge_star_pos hv

/-- Hence the line of a nonzero packet and the line of its star intersect trivially. -/
theorem deningerGreenBoundary_span_disjoint {v : ℝ × ℝ} (hv : v ≠ 0) :
    Submodule.span ℝ {v} ⊓ Submodule.span ℝ {deningerLeafStar v} = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro w ⟨hw1, hw2⟩
  have hzero : deningerLeafWedge v w = 0 := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw1
    show v.1 * (c * v.2) - v.2 * (c * v.1) = 0
    ring
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw2
  have hsmul : deningerLeafWedge v (c • deningerLeafStar v)
      = c * deningerLeafWedge v (deningerLeafStar v) := by
    show v.1 * (c * (deningerLeafStar v).2) - v.2 * (c * (deningerLeafStar v).1)
        = c * (v.1 * (deningerLeafStar v).2 - v.2 * (deningerLeafStar v).1)
    ring
  rw [hsmul] at hzero
  have hpos := deningerGreenBoundary_star_transverse hv
  have hc : c = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (ne_of_gt hpos)
  show c • deningerLeafStar v = 0
  rw [hc, zero_smul]

end GreenBoundary

end RHTower
