import GaloisForLFunctions.FloorFreeArithmetic.FiniteTopLayersAreSeenOnEveryWindow
import GaloisForLFunctions.SurfaceOfSpecZ.OneSidedHasseWeilAtTheIntegerDegrees
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration

/-!
# Non-attainment is a law of configurations

The receiver "window non-attainment gives the abscissa law" uses nothing of `ζ` beyond three
properties of its zero configuration: temperedness, symmetry under complex conjugation, and the
absence of real zeros right of the critical line. It holds for every such configuration, in
particular for every model that fails the abscissa law: there the hypothesis fails. A producer
of non-attainment has to prove a statement that is false on the fakes.

* `exists_finite_top_of_not_abscissaLawAt_config`, `exists_finite_top_of_not_abscissaLaw_config`:
  a configuration that violates the abscissa law at a depth `h` has a finite nonempty active top
  layer at a depth beyond `h`.
* `uniform_attainment_of_not_abscissaLaw_config`: its normalized trace is attained on every
  late window of every length.
* `abscissaLaw_of_windowNonAttainment_config`: window non-attainment at every depth bounding
  the zeros gives the abscissa law of the configuration.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality
open ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa

variable {Z : ZeroConfig}

/-- The spline sees every zero right of the line, in every configuration. -/
theorem evenCoeff_spline_sees_config {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hre : 1 / 2 < ρ.re) :
    evenCoeff Z (boxSpline 1 3) (ρ - 1 / 2) ≠ 0 :=
  evenCoeff_sub_half_ne_zero_of_conj_symm Z (contDiff_boxSpline one_pos 2).continuous
    (hasCompactSupport_of_support_subset_abs (boxSpline_support one_pos 3))
    (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ
    (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith only [hre])))

/-- In a conjugation-symmetric configuration an active exponent `z` comes from the zero
`½ + z`. -/
theorem add_half_mem_of_evenCoeff_ne_zero (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier)
    {b : ℝ → ℂ} {z : ℂ} (hz : evenCoeff Z b z ≠ 0) : (1 / 2 + z) ∈ Z.carrier := by
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · exact h
  · have hc := hconj _ h
    have e : conj (1 / 2 + conj z) = 1 / 2 + z := by apply Complex.ext <;> simp
    rwa [e] at hc

/-- **Failure of the abscissa law at a depth is a finite top layer beyond that depth.** For a
conjugation-symmetric configuration without real zeros right of the line: if finitely many but
not zero zeros lie beyond the depth `h ≥ 0`, the deepest of them form a finite active top layer
at a depth `b > h`. -/
theorem exists_finite_top_of_not_abscissaLawAt_config
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier)
    (hnonreal : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → ρ.im ≠ 0) {h : ℝ} (hh : 0 ≤ h)
    (hnot : ¬ AbscissaLawAt Z h) :
    ∃ b : ℝ, h < b ∧ TopDepth Z b ∧ ∃ S : Finset ℂ,
      (∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b) ∧ S.Nonempty := by
  classical
  unfold AbscissaLawAt at hnot
  push Not at hnot
  obtain ⟨hfin, ρ, hρ, hgt⟩ := hnot
  obtain ⟨ρ₀, hρ₀, hmax⟩ := hfin.exists_maximalFor Complex.re (rightOf Z h) ⟨ρ, hρ, hgt⟩
  have hre : 1 / 2 + h < ρ₀.re := hρ₀.2
  have hall : ∀ τ ∈ Z.carrier, τ.re ≤ ρ₀.re := by
    intro τ hτ
    by_cases ht : 1 / 2 + h < τ.re
    · by_contra hn
      exact (not_le.mpr (lt_of_not_ge hn)) (hmax ⟨hτ, ht⟩ (lt_of_not_ge hn).le)
    · linarith only [hre, le_of_not_gt ht]
  let b := ρ₀.re - 1 / 2
  have hb : h < b := by dsimp [b]; linarith only [hre]
  have he : ∀ z : ℂ, ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := fun z => by norm_num
  have htop : TopDepth Z b := by
    intro z hz
    have hbound := hall _ (add_half_mem_of_evenCoeff_ne_zero hconj hz)
    rw [he] at hbound
    dsimp [b]
    linarith only [hbound]
  have hfinite : (positiveTopSupport Z b).Finite := by
    apply (hfin.preimage (f := fun z : ℂ => (1 / 2 : ℂ) + z)
      (add_right_injective (1 / 2 : ℂ)).injOn).subset
    intro z hz
    refine ⟨add_half_mem_of_evenCoeff_ne_zero hconj hz.2.2, ?_⟩
    rw [he, hz.1]
    dsimp [b]
    linarith only [hre]
  have hnonempty : (positiveTopSupport Z b).Nonempty := by
    have hsee := evenCoeff_spline_sees_config hρ₀.1 (by linarith only [hre, hh])
    have hzre : (ρ₀ - 1 / 2).re = b := by simp [b]
    have him : (ρ₀ - 1 / 2).im ≠ 0 := by
      have h0 := hnonreal ρ₀ hρ₀.1 (by linarith only [hre, hh])
      simpa using h0
    rcases lt_or_gt_of_ne him with hn | hp
    · refine ⟨conj (ρ₀ - 1 / 2), ?_⟩
      refine ⟨by simpa only [Complex.conj_re] using hzre,
        by simpa only [Complex.conj_im] using neg_pos.mpr hn, ?_⟩
      rw [SurfaceOfSpecZ.evenCoeff_conj]
      intro hzero
      exact hsee (by simpa only [Complex.conj_conj, map_zero] using congrArg conj hzero)
    · exact ⟨ρ₀ - 1 / 2, hzre, hp, hsee⟩
  exact ⟨b, hb, htop, hfinite.toFinset, fun z => Set.Finite.mem_toFinset hfinite,
    hfinite.toFinset_nonempty.mpr hnonempty⟩

/-- **Failure of the abscissa law is a finite top layer.** For a conjugation-symmetric
configuration without real zeros right of the line. -/
theorem exists_finite_top_of_not_abscissaLaw_config
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier)
    (hnonreal : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → ρ.im ≠ 0) (hnot : ¬ AbscissaLaw Z) :
    ∃ b : ℝ, 0 < b ∧ TopDepth Z b ∧ ∃ S : Finset ℂ,
      (∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b) ∧ S.Nonempty := by
  unfold AbscissaLaw at hnot
  push Not at hnot
  obtain ⟨h, hh, hnotAt⟩ := hnot
  obtain ⟨b, hb, htop, S, hS, hne⟩ :=
    exists_finite_top_of_not_abscissaLawAt_config hconj hnonreal hh hnotAt
  exact ⟨b, hh.trans_lt hb, htop, S, hS, hne⟩

/-- The active exponents of positive real part are not real. -/
theorem im_ne_zero_of_evenCoeff_ne_zero (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier)
    (hnonreal : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → ρ.im ≠ 0) {b : ℝ} (hb : 0 < b) {z : ℂ}
    (hz : evenCoeff Z (boxSpline 1 3) z ≠ 0) (hre : z.re = b) : z.im ≠ 0 := by
  have hmem := add_half_mem_of_evenCoeff_ne_zero hconj hz
  have he : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
  have him : ((1 / 2 : ℂ) + z).im = z.im := by norm_num
  have h0 := hnonreal _ hmem (by rw [he, hre]; linarith only [hb])
  rwa [him] at h0

/-- **Uniform attainment in every configuration.** A tempered conjugation-symmetric
configuration without real zeros right of the line that violates the abscissa law has a depth
`b > 0` at which its normalized trace is attained on every late window of every length. -/
theorem uniform_attainment_of_not_abscissaLaw_config (hZ : TemperedConfig Z)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier)
    (hnonreal : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → ρ.im ≠ 0) (hnot : ¬ AbscissaLaw Z) :
    ∃ b : ℝ, 0 < b ∧ TopDepth Z b ∧ ∀ L : ℝ, 0 < L →
      ∃ c U : ℝ, 0 < c ∧ ∀ T : ℝ, U ≤ T → ∃ u ∈ Icc T (T + L), c ≤ |normTrace Z b u| := by
  obtain ⟨b, hb, htop, S, hS, hne⟩ :=
    exists_finite_top_of_not_abscissaLaw_config hconj hnonreal hnot
  exact ⟨b, hb, htop, fun L hL =>
    finite_top_seen_on_every_window hZ htop hL S hS hne
      (fun z hz hre => im_ne_zero_of_evenCoeff_ne_zero hconj hnonreal hb hz hre)⟩

/-- **Window non-attainment gives the abscissa law of a configuration.** -/
theorem abscissaLaw_of_windowNonAttainment_config (hZ : TemperedConfig Z)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier)
    (hnonreal : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → ρ.im ≠ 0)
    (h : ∀ b : ℝ, 0 < b → TopDepth Z b → ∃ L : ℝ, 0 < L ∧ WindowNonAttainment Z b L) :
    AbscissaLaw Z := by
  by_contra hnot
  obtain ⟨b, hb, htop, S, hS, hne⟩ :=
    exists_finite_top_of_not_abscissaLaw_config hconj hnonreal hnot
  obtain ⟨L, hL, hN⟩ := h b hb htop
  exact not_windowNonAttainment_of_finite_top hZ htop hL S hS hne
    (fun z hz hre => im_ne_zero_of_evenCoeff_ne_zero hconj hnonreal hb hz hre) hN

end GaloisForLFunctions.FloorFreeArithmetic
