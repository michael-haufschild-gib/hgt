import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompactModularPeriodization

/-!
# Sharp height obstruction to covering the core by integral cusp relocation

The existing modular-orbit height bound is attained on the imaginary axis by
identity or inversion. Thus its maximum is exactly `max(y,1/y)`. For every cutoff
strictly greater than one there is an explicit nonempty open height band from
which no integral cusp change reaches the cutoff.

This rules out the shortcut that would replace compact-core control with
relocation into sufficiently high cusp tails. It is not an obstruction to the
Selberg conjecture or to an argument coupling cusp and core energies.
-/

open Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace GaloisForLFunctions.RHTower.SelbergCuspRelocation
noncomputable section

/-- An actual point on the imaginary axis, covering all positive heights. -/
def imaginaryPoint (h : ℝ) : UpperHalfPlane :=
  ⟨(Real.exp h : ℂ) * Complex.I, by
    simpa only [Complex.mul_I_im, Complex.ofReal_re] using Real.exp_pos h⟩

/-- The corpus height bound transported from PSL₂ to the actual integral matrices. -/
theorem integral_orbit_height_le (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    (g • z).im ≤ max z.im (1 / z.im) := by
  simpa only [PSL2Z_mk_smul] using
    _root_.RHTower.D4BMModularCore.modular_orbit_height_le (QuotientGroup.mk g) z

private theorem inversion_height (h : ℝ) :
    (ModularGroup.S • imaginaryPoint h).im = 1 / Real.exp h := by
  rw [UpperHalfPlane.modular_S_smul]
  simp only [imaginaryPoint, UpperHalfPlane.im, Complex.inv_im, Complex.neg_im,
    Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_I, mul_one,
    Complex.normSq_ofReal, Complex.mul_I_im, Complex.ofReal_re, neg_neg]
  field_simp

/-- The orbit bound is sharp on the imaginary axis and its maximum is attained. -/
theorem imaginary_orbit_height_maximum (h : ℝ) :
    IsGreatest (Set.range (fun g : SL(2, ℤ) => (g • imaginaryPoint h).im))
      (max (Real.exp h) (1 / Real.exp h)) := by
  constructor
  · by_cases hh : Real.exp h ≤ 1 / Real.exp h
    · refine ⟨ModularGroup.S, ?_⟩
      change (ModularGroup.S • imaginaryPoint h).im = _
      rw [inversion_height, max_eq_right hh]
    · exact ⟨1, by simp only [one_smul, imaginaryPoint, UpperHalfPlane.im,
        Complex.mul_I_im, Complex.ofReal_re, max_eq_left (le_of_not_ge hh)]⟩
  · rintro y ⟨g, rfl⟩
    simpa only [imaginaryPoint, UpperHalfPlane.im, Complex.mul_I_im, Complex.ofReal_re] using
      integral_orbit_height_le g (imaginaryPoint h)

/-- Exact classification of cutoffs reachable from an imaginary-axis point. -/
theorem imaginary_reaches_cutoff_iff (h Y : ℝ) :
    (∃ g : SL(2, ℤ), Y ≤ (g • imaginaryPoint h).im) ↔
      Y ≤ max (Real.exp h) (1 / Real.exp h) := by
  constructor
  · rintro ⟨g, hg⟩
    exact hg.trans ((imaginary_orbit_height_maximum h).2 (Set.mem_range_self g))
  · intro hY
    obtain ⟨g, hg⟩ := (imaginary_orbit_height_maximum h).1
    exact ⟨g, by simpa only [hg] using hY⟩

/-- An entire reciprocal height band remains below the same bound under every integral matrix. -/
theorem reciprocal_band_orbit_bound {M : ℝ} (hM : 0 < M) (z : UpperHalfPlane)
    (hz : z.im ∈ Icc (1 / M) M) (g : SL(2, ℤ)) : (g • z).im ≤ M := by
  apply (integral_orbit_height_le g z).trans
  apply max_le hz.2
  apply (div_le_iff₀ z.im_pos).mpr
  have hh := (div_le_iff₀ hM).mp hz.1
  simpa only [mul_comm] using hh

/-- No integral cusp coordinate change moves the point `i` above height one. -/
theorem no_integral_relocation_above_one (u : ℝ) :
    ¬ ∃ g : SL(2, ℤ), 1 + Real.exp u ≤ (g • imaginaryPoint 0).im := by
  rw [imaginary_reaches_cutoff_iff]
  simp only [Real.exp_zero, div_one, max_self]
  linarith [Real.exp_pos u]

/-- An explicit open height band excluded from every cusp collar at cutoff `1+exp(u)`. -/
def coreBand (u : ℝ) : Set UpperHalfPlane :=
  {z | z.im ∈ Ioo (1 / (1 + Real.exp u)) (1 + Real.exp u)}

/-- The excluded band is open in the actual upper-half-plane topology. -/
theorem coreBand_open (u : ℝ) : IsOpen (coreBand u) :=
  isOpen_Ioo.preimage UpperHalfPlane.continuous_im

/-- The excluded band contains the point `i`. -/
theorem coreBand_nonempty (u : ℝ) : (coreBand u).Nonempty := by
  refine ⟨imaginaryPoint 0, ?_⟩
  change 1 / (1 + Real.exp u) < (imaginaryPoint 0).im ∧
    (imaginaryPoint 0).im < 1 + Real.exp u
  simp only [imaginaryPoint, UpperHalfPlane.im, Real.exp_zero,
    Complex.mul_I_im, Complex.ofReal_re]
  have he := Real.exp_pos u
  constructor
  · apply (div_lt_iff₀ (by linarith : 0 < 1 + Real.exp u)).mpr
    linarith
  · linarith

/-- Every point of the band stays strictly below the cutoff in every integral cusp coordinate. -/
theorem coreBand_no_relocation (u : ℝ) (z : UpperHalfPlane)
    (hz : z ∈ coreBand u) (g : SL(2, ℤ)) : (g • z).im < 1 + Real.exp u := by
  apply lt_of_le_of_lt (integral_orbit_height_le g z)
  apply max_lt hz.2
  apply (div_lt_iff₀ z.im_pos).mpr
  have hh := (div_lt_iff₀ (by linarith [Real.exp_pos u] : 0 < 1 + Real.exp u)).mp hz.1
  simpa only [mul_comm] using hh

/-- For every cutoff greater than one, a nonempty open set cannot be relocated into that cusp collar. -/
theorem exists_open_obstruction (u : ℝ) :
    ∃ U : Set UpperHalfPlane, IsOpen U ∧ U.Nonempty ∧
      ∀ z ∈ U, ∀ g : SL(2, ℤ), (g • z).im < 1 + Real.exp u :=
  ⟨coreBand u, coreBand_open u, coreBand_nonempty u, coreBand_no_relocation u⟩

end
end GaloisForLFunctions.RHTower.SelbergCuspRelocation
