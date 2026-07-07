/-
The co-movement cancellation: the mirror orientation is a single-angle datum.

The mirror-edge incidence of the anchored pencil rotates the conjugated source
incidence by the mirror defect, and the source incidence itself carries the anchor's
phase at the point — both moved by the same prime set.  These two motions cancel
exactly: the defect is the tilt at the mirror point plus the tilt at the point, while
the source incidence divides by the anchor whose canonical phase IS the tilt at the
point.  What remains is a single P-controlled angle — the anchor tilt at the MIRROR
point — acting on a P-independent member phase:

  Im ι_P(1−s̄) = (1/‖A_P(1−s̄)‖) · Im( e^{−i·tilt_P(1−s̄)} · conj(−G(s)) ).

The joint (defect, source-value) reachability problem therefore collapses to the
reachability of one tilt angle, and the tilt at the mirror point is a prime-indexed
walk with the same sign law and bounds as the defect itself.
-/
import GaloisForLFunctions.RHTower.DefectSteering

noncomputable section

namespace RHTower

open Complex Metric

/-- Division by a nonvanishing polar form is scaling by the inverse modulus and
counter-rotation by the phase. -/
theorem div_polar_eq (z : ℂ) (r t : ℝ) :
    z / (((r : ℝ) : ℂ) * Complex.exp (((t : ℝ) : ℂ) * I))
      = ((r⁻¹ : ℝ) : ℂ) * (Complex.exp (-((t : ℝ) : ℂ) * I) * z) := by
  rw [div_eq_mul_inv, mul_inv, ← Complex.exp_neg]
  rw [show (-(((t : ℝ) : ℂ) * I)) = -((t : ℝ) : ℂ) * I from by ring]
  rw [show ((r : ℝ) : ℂ)⁻¹ = ((r⁻¹ : ℝ) : ℂ) from by push_cast; ring]
  ring

/-- **The cancellation theorem for the RS member**: the mirror-edge incidence
imaginary part of the anchored pencil depends on the prime set ONLY through the anchor
tilt at the mirror point (and its modulus there) — the point-side tilt inside the
defect cancels against the anchor phase of the source incidence, and the member phase
`conj(−completedGN N s)` carries no primes at all. -/
theorem im_incidence_anchored_mirror_tilt_only {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {N : ℕ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (incidence (eulerHeadAnchor P) (completedGN N) (1 - (starRingEnd ℂ) s)).im
      = (‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖)⁻¹
        * (Complex.exp (-((anchorTilt P (1 - (starRingEnd ℂ) s) : ℝ) : ℂ) * I)
            * (starRingEnd ℂ) (-(completedGN N s))).im := by
  have hre' : 0 < (1 - (starRingEnd ℂ) s).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hAne : eulerHeadAnchor P (1 - (starRingEnd ℂ) s) ≠ 0 :=
    eulerHeadAnchor_ne_zero hP hre'
  have hAnorm : (0 : ℝ) < ‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖ :=
    norm_pos_iff.mpr hAne
  unfold incidence
  rw [completedGN_lineReflection h0 h1]
  conv_lhs => rw [eulerHeadAnchor_polar P (1 - (starRingEnd ℂ) s)]
  rw [show -(starRingEnd ℂ) (completedGN N s) = (starRingEnd ℂ) (-(completedGN N s))
      from by rw [map_neg]]
  rw [div_polar_eq]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The cancellation theorem for the symmetric EM member** — same collapse, for the
member with machine-checked accuracy: the P-dependence of the mirror orientation is
exactly one angle, the anchor tilt at the mirror point. -/
theorem im_incidence_anchoredSEM_mirror_tilt_only {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {N : ℕ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (incidence (eulerHeadAnchor P) (completedSEM N) (1 - (starRingEnd ℂ) s)).im
      = (‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖)⁻¹
        * (Complex.exp (-((anchorTilt P (1 - (starRingEnd ℂ) s) : ℝ) : ℂ) * I)
            * (starRingEnd ℂ) (-(completedSEM N s))).im := by
  have hre' : 0 < (1 - (starRingEnd ℂ) s).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hAne : eulerHeadAnchor P (1 - (starRingEnd ℂ) s) ≠ 0 :=
    eulerHeadAnchor_ne_zero hP hre'
  have hAnorm : (0 : ℝ) < ‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖ :=
    norm_pos_iff.mpr hAne
  unfold incidence
  rw [completedSEM_lineReflection h0 h1]
  conv_lhs => rw [eulerHeadAnchor_polar P (1 - (starRingEnd ℂ) s)]
  rw [show -(starRingEnd ℂ) (completedSEM N s) = (starRingEnd ℂ) (-(completedSEM N s))
      from by rw [map_neg]]
  rw [div_polar_eq]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The mirror tilt is a prime-indexed walk with the defect's own sign law**: the
tilt at the mirror point is the sum of per-prime tilts there, each with the sign of
`sin(Im s·log q)` — the single angle that steers the mirror orientation inherits the
entire steering engine. -/
theorem anchorTilt_mirror_eq_sum (P : Finset ℕ) (s : ℂ) :
    anchorTilt P (1 - (starRingEnd ℂ) s)
      = ∑ q ∈ P, primeTilt q (1 - (starRingEnd ℂ) s) := rfl

/-- The mirror-point tilt increment has the sign of `sin(Im s·log q)` — positive
side. -/
theorem primeTilt_mirror_pos_iff {q : ℕ} (hq : 2 ≤ q) {s : ℂ} (h1 : s.re < 1) :
    0 < primeTilt q (1 - (starRingEnd ℂ) s) ↔ 0 < Real.sin (s.im * Real.log q) := by
  have hre' : 0 < (1 - (starRingEnd ℂ) s).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have him' : (1 - (starRingEnd ℂ) s).im = s.im := by
    simp [Complex.sub_im, Complex.conj_im]
  rw [primeTilt_pos_iff hq hre', him']

/-- The mirror-point tilt increment has the sign of `sin(Im s·log q)` — negative
side. -/
theorem primeTilt_mirror_neg_iff {q : ℕ} (hq : 2 ≤ q) {s : ℂ} (h1 : s.re < 1) :
    primeTilt q (1 - (starRingEnd ℂ) s) < 0 ↔ Real.sin (s.im * Real.log q) < 0 := by
  have hre' : 0 < (1 - (starRingEnd ℂ) s).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have him' : (1 - (starRingEnd ℂ) s).im = s.im := by
    simp [Complex.sub_im, Complex.conj_im]
  rw [primeTilt_neg_iff hq hre', him']

end RHTower
