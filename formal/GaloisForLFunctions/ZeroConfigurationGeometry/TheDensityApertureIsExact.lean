import GaloisForLFunctions.ZeroConfigurationGeometry.SparseClustersNeverCancel
import GaloisForLFunctions.ZeroConfigurationGeometry.BlindnessCostsTheDensityAperture

/-!
# The density aperture is exact

For configurations of depth `≤ 1/2` whose density is the same from above and from below, the
least aperture of a blind window is exactly `π` times the density.

* **Sufficiency at any depth** (`exists_window_blind_of_count_le_complex`). If the real parts of
  the points have count bound `(D, C)`, Hall matching into `D⁻¹ℤ` makes the configuration a
  complex perturbation of the lattice of depth `≤ 1/2`, blinded at every aperture `> πD`.
* **Necessity** (`pi_mul_le_aperture_of_blind`, Jensen). A nonzero window of aperture `A` blind to
  a configuration with at least `2Dρ − K` points in the large balls about every real point has
  `A ≥ πD`.
* **The threshold** (`blind_aperture_threshold`). For a configuration with both bounds, windows
  blind to it exist at every aperture `> πD`, and every nonzero one has aperture `≥ πD`.

This is the completeness radius of the exponentials on uniformly distributed configurations near
the real line. A configuration of upper uniform density larger than its lower density is the case
left to the Beurling–Malliavin radius.
-/

open MeasureTheory Complex Set Filter Metric
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- **Blind windows at the uniform density, at any depth `≤ 1/2`.** -/
theorem exists_window_blind_of_count_le_complex {ι : Type*} (lam : ι → ℂ) {D C r : ℝ}
    (hD : 0 < D) (him : ∀ i, |(lam i).im| ≤ 1 / 2)
    (hcount : ∀ (s : Finset ι) (a b : ℝ), a ≤ b → (∀ i ∈ s, (lam i).re ∈ Icc a b) →
      (s.card : ℝ) ≤ D * (b - a) + C)
    (hr : π * D < r) {z₀ : ℂ} (hz₀ : ∀ i, z₀ ≠ lam i) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ i, paperFT f (lam i) = 0) ∧ paperFT f z₀ ≠ 0 := by
  classical
  set h := D⁻¹ with hh_def
  have hh : 0 < h := inv_pos.mpr hD
  have hDh : D * h = 1 := by rw [hh_def]; field_simp
  have hcount' : ∀ (s : Finset ι) (a b : ℝ), a ≤ b → (∀ i ∈ s, D * (lam i).re ∈ Icc a b) →
      (s.card : ℝ) ≤ b - a + C := by
    intro s a b hab hs
    have := hcount s (a / D) (b / D) (div_le_div_of_nonneg_right hab hD.le) fun i hi => by
      obtain ⟨h1, h2⟩ := hs i hi
      exact ⟨(div_le_iff₀ hD).mpr (by linarith), (le_div_iff₀ hD).mpr (by linarith)⟩
    calc (s.card : ℝ) ≤ D * (b / D - a / D) + C := this
      _ = b - a + C := by field_simp
  obtain ⟨σ, hσ, hσd⟩ := exists_injective_near_int (fun i => D * (lam i).re) hcount'
  have hbound : ∀ i ∈ (Set.univ : Set ι), ‖lam i - (σ i : ℂ) * (h : ℂ)‖ ≤ (C + 1) / 2 * h + 1 / 2 := by
    intro i _
    have hre : |(lam i).re - (σ i : ℝ) * h| ≤ (C + 1) / 2 * h := by
      have e : (lam i).re - (σ i : ℝ) * h = h * (D * (lam i).re - σ i) := by
        rw [mul_sub, ← mul_assoc, mul_comm h D, hDh, one_mul, mul_comm]
      rw [e, abs_mul, abs_of_pos hh, mul_comm]
      exact mul_le_mul_of_nonneg_right (hσd i) hh.le
    have h1 := Complex.norm_le_abs_re_add_abs_im (lam i - (σ i : ℂ) * (h : ℂ))
    have e1 : (lam i - (σ i : ℂ) * (h : ℂ)).re = (lam i).re - (σ i : ℝ) * h := by simp
    have e2 : (lam i - (σ i : ℂ) * (h : ℂ)).im = (lam i).im := by simp
    rw [e1, e2] at h1
    linarith [him i]
  obtain ⟨f, hf, hfz, hf0⟩ := exists_window_blind_of_injOn_near_complex_lattice lam σ Set.univ
    (hσ.injOn) hh (by rw [hh_def, div_inv_eq_mul]; exact hr) hbound (fun i _ => him i)
    (fun i _ => hz₀ i)
  exact ⟨f, hf, fun i => hfz i (Set.mem_univ i), hf0⟩

/-- **The density aperture is exact.** For a configuration of depth `≤ 1/2` with count bound
`(D, C)` on its real parts and lower density `≥ D`, windows blind to it exist at every aperture
`> πD`, seeing any given point off it, and every nonzero window blind to it has aperture `≥ πD`. -/
theorem blind_aperture_threshold {ι : Type*} (lam : ι → ℂ) {D C : ℝ} (hD : 0 < D)
    (him : ∀ i, |(lam i).im| ≤ 1 / 2)
    (hcount : ∀ (s : Finset ι) (a b : ℝ), a ≤ b → (∀ i ∈ s, (lam i).re ∈ Icc a b) →
      (s.card : ℝ) ≤ D * (b - a) + C)
    (hlow : HasLowerDensityAtLeast (Set.range lam) D) :
    (∀ r, π * D < r → ∀ z₀ : ℂ, (∀ i, z₀ ≠ lam i) →
        ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ i, paperFT f (lam i) = 0) ∧ paperFT f z₀ ≠ 0) ∧
      ∀ (A : ℝ) (f : ℝ → ℂ), 0 ≤ A → ApertureWindow A f → f ≠ 0 →
        (∀ i, paperFT f (lam i) = 0) → π * D ≤ A :=
  ⟨fun _ hr _ hz₀ => exists_window_blind_of_count_le_complex lam hD him hcount hr hz₀,
    fun _ _ hA hf hne hfz => pi_mul_le_aperture_of_blind hA hf hne hlow (by
      rintro z ⟨i, rfl⟩
      exact hfz i)⟩

end GaloisForLFunctions.ZeroConfigurationGeometry
