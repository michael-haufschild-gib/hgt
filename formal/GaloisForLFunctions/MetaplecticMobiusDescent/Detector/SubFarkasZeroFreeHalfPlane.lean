import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubFarkasHighTransport
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane

/-!
# Unconditional Sub-Farkas Zero-Free Half-Plane Below `16799 / 19200`

Combining the common detector bounds of `SubFarkasHighTransport` at the Gram-admissible cubic-probe
geometry `(17 / 48, 2299 / 4800, 801 / 4800)` (`lowBoundary = 16799 / 19200 < 40535 / 46328 <
20999 / 24000`, signal shift `-19799 / 28800`) with regularized Mellin continuation over all
primitive Hecke characters of `K = ℚ(ω)` establishes:

* `hecke_beta_le_sub_farkas`: `HeckeZeroSupremum.beta ≤ 16799 / 19200`.
* `hecke_ne_zero_of_sub_farkas_lt_re`: every Hecke `L`-function of `ℚ(ω)` is nonzero on
  `Re s > 16799 / 19200` away from `(s = 1, χ.residue = 1)`.
* `DirichletCharacter.LFunction_ne_zero_of_sub_farkas_lt_re`: every Dirichlet `L`-function is
  nonzero on `Re s > 16799 / 19200` away from `(χ = 1, s = 1)`.
* `riemannZeta_ne_zero_of_sub_farkas_lt_re`, `riemannZeta_ne_zero_of_re_lt_sub_farkas_left`,
  and `riemannZeta_zero_mem_sub_farkas_strip`: `riemannZeta` is nonzero on `Re s > 16799 / 19200`
  and on `0 < Re s < 2401 / 19200`, confining every zero with `Re s > 0` to
  `[2401 / 19200, 16799 / 19200]`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Classical

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

namespace SubFarkasZeroFree

open HeckeFamily HeckeZeroSupremum

/-- Unconditionally, the supremum `HeckeZeroSupremum.beta` of real parts of zeros across all Hecke
`L`-functions of `ℚ(ω)` satisfies `beta ≤ 16799 / 19200 = 7 / 8 - 1 / 19200`. -/
theorem hecke_beta_le_sub_farkas : HeckeZeroSupremum.beta ≤ 16799 / 19200 := by
  by_contra hn
  have hβ : (16799 / 19200 : ℝ) < HeckeZeroSupremum.beta := lt_of_not_ge hn
  obtain ⟨loss, σ, hloss, hloss_lt, hσ, hprobe⟩ :=
    SubFarkasHighTransport.exists_subFarkas_common_probe hβ
  set a : ℝ := max (16799 / 19200 + loss) (HeckeZeroSupremum.beta - σ)
  have ha_lt_β : a < HeckeZeroSupremum.beta :=
    max_lt (by linarith only [hloss_lt]) (by linarith only [hσ])
  have ha_gt_4350 : (43 / 50 : ℝ) < a :=
    lt_of_lt_of_le (by linarith only [hloss])
      (le_max_left (16799 / 19200 + loss) (HeckeZeroSupremum.beta - σ))
  have ha_lt_two : a < 2 :=
    lt_of_lt_of_le ha_lt_β (HeckeZeroSupremum.beta_le_one.trans (by norm_num))
  obtain ⟨η, ρ, _hp, hhalf, _hone, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta (ε := HeckeZeroSupremum.beta - a)
      (by linarith only [ha_lt_β]) (by linarith only [ha_gt_4350])
  have hρa : a < ρ.re := by linarith only [hnear]
  obtain ⟨χ, H, J, hmask, hH43, hb43, hJ, herr⟩ := hprobe η
  have hH78 : AnalyticOnNhd ℂ H {s : ℂ | 7 / 8 < s.re} :=
    hH43.mono fun s hs => by
      change (43 / 50 : ℝ) < s.re
      change (7 / 8 : ℝ) < s.re at hs
      linarith only [hs]
  have hb78 : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2 :=
    fun s hs => hb43 s (by linarith only [hs])
  have hHa : AnalyticOnNhd ℂ H {s : ℂ | a < s.re} :=
    hH43.mono fun s hs => by
      change (43 / 50 : ℝ) < s.re
      change a < s.re at hs
      linarith only [ha_gt_4350, hs]
  have htop : HeckeSignal.signal χ H (-19799 / 28800) =O[atTop]
      (fun Z : ℝ => Z ^ (a + (-19799 / 28800))) := by
    have hmax : max (10799 / 57600 + loss) (HeckeZeroSupremum.beta - 19799 / 28800 - σ) =
        a + (-19799 / 28800) := by
      have h1 : 10799 / 57600 + loss = (16799 / 19200 + loss) + (-19799 / 28800) := by ring
      have h2 : HeckeZeroSupremum.beta - 19799 / 28800 - σ =
          (HeckeZeroSupremum.beta - σ) + (-19799 / 28800) := by ring
      rw [h1, h2]
      exact max_add_add_right _ _ _
    simpa only [hmax] using
      Continuation.common_signal_bound J (HeckeSignal.signal χ H (-19799 / 28800))
        (10799 / 57600 + loss) (HeckeZeroSupremum.beta - 19799 / 28800 - σ) hJ herr
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr fun hc => hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc)
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask (by linarith only [hhalf]) hχpole,
      hz, zero_mul]
  have hHd : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re} := hH78.differentiableOn
  have hne : LFunction χ ρ ≠ 0 :=
    Continuation.nonzero_of_regularized_signal a 1 (-19799 / 28800)
      (LFunction χ) (HeckeSignal.regularL χ) (HeckeSignal.targetRegularizer χ)
      (Continuation.gaussianMultiplier H) (HeckeSignal.signal χ H (-19799 / 28800))
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (HeckeSignal.regularL_entire χ)).mono (Set.subset_univ _))
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (HeckeSignal.targetRegularizer_entire χ)).mono (Set.subset_univ _))
      (Continuation.gaussianMultiplier_analytic hHa)
      (HeckeSignal.signal_locallyIntegrable χ H hHd hb78 (-19799 / 28800))
      htop
      (HeckeSignal.signal_rapidDecayAtZero χ H hHd hb78 (-19799 / 28800))
      (fun s hs => by
        have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
        have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
        have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
        rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
          HeckeSignal.signalMellin_eq_amplitude χ H hHd hb78 (-19799 / 28800) a ha_lt_two htop hs]
        unfold HeckeSignal.amplitude HeckeSignal.quotient Continuation.gaussianMultiplier
        rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
        have hn := LFunction_ne_zero_of_one_lt_re χ hs1
        field_simp)
      hρa
      (HeckeSignal.regularL_eq χ
        (by intro h; rw [h, Complex.zero_re] at hρa; linarith only [ha_gt_4350, hρa]) hχpole)
      (HeckeSignal.targetRegularizer_ne_zero χ hχpole)
      (Continuation.gaussianMultiplier_ne_zero (hb43 ρ (ha_gt_4350.trans hρa)))
  exact hne hzχ

/-- Strict numerical improvements over both the Farkas linear-obstruction benchmark
`40535 / 46328` and the sub-seven-eighths benchmark `20999 / 24000`. -/
theorem hecke_beta_lt_farkas_and_sub_seven_eighths :
    HeckeZeroSupremum.beta ≤ 16799 / 19200 ∧
    (16799 / 19200 : ℝ) < 40535 / 46328 ∧
    (40535 / 46328 : ℝ) < 20999 / 24000 :=
  ⟨hecke_beta_le_sub_farkas, by norm_num, by norm_num⟩

/-- Every Hecke `L`-function of `ℚ(ω)` is nonzero on `Re s > 16799 / 19200` away from its pole. -/
theorem hecke_ne_zero_of_sub_farkas_lt_re (χ : Character) (s : ℂ)
    (hs : (16799 / 19200 : ℝ) < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_beta_lt χ (hecke_beta_le_sub_farkas.trans_lt hs) hpole

/-- Every Dirichlet `L`-function is nonzero on `Re s > 16799 / 19200` away from `(χ = 1, s = 1)`. -/
theorem dirichlet_sub_farkas_nonzero (q : ℕ) (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : (16799 / 19200 : ℝ) < s.re) (hexc : ¬(χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  letI : NeZero q := ⟨hq⟩
  exact SubSevenEighthsZeroFree.dirichlet_ne_zero_of_hecke (by norm_num)
    hecke_ne_zero_of_sub_farkas_lt_re χ hs hexc

end SubFarkasZeroFree

/-- Every Dirichlet `L`-function is nonzero on `Re s > 16799 / 19200` away from `(χ = 1, s = 1)`. -/
theorem DirichletCharacter.LFunction_ne_zero_of_sub_farkas_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : (16799 / 19200 : ℝ) < s.re)
    (hpole : ¬(χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  SubFarkasZeroFree.dirichlet_sub_farkas_nonzero q (NeZero.ne q) χ s hs hpole

/-- `riemannZeta` has no zeros on the open half-plane `Re s > 16799 / 19200`. -/
theorem riemannZeta_ne_zero_of_sub_farkas_lt_re {s : ℂ}
    (hs : (16799 / 19200 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := DirichletCharacter.LFunction_ne_zero_of_sub_farkas_lt_re
    (1 : DirichletCharacter ℂ 1) hs (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

/-- Functional reflection `s ↦ 1 - s` transfers the `16799 / 19200` right half-plane to nonvanishing
of `riemannZeta` on `0 < Re s < 2401 / 19200` (`= 1 / 8 + 1 / 19200 > 3001 / 24000`). -/
theorem riemannZeta_ne_zero_of_re_lt_sub_farkas_left {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < (2401 / 19200 : ℝ)) : riemannZeta s ≠ 0 := by
  intro hzero
  have hs0 : s ≠ 0 := by
    intro hs
    simp only [hs, Complex.zero_re, lt_self_iff_false] at h0
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
  have hcompleted : completedRiemannZeta s = 0 := by
    have hz := (riemannZeta_def_of_ne_zero hs0).symm.trans hzero
    exact (div_eq_zero_iff.mp hz).resolve_right hΓ
  have hsub : (1 : ℂ) - s ≠ 0 := by
    intro hs
    have he : s = 1 := (sub_eq_zero.mp hs).symm
    rw [he, Complex.one_re] at h1
    norm_num at h1
  have hreflect : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero hsub, completedRiemannZeta_one_sub, hcompleted, zero_div]
  apply riemannZeta_ne_zero_of_sub_farkas_lt_re (s := 1 - s) _ hreflect
  simp only [Complex.sub_re, Complex.one_re]
  linarith only [h1]

/-- Every zero of `riemannZeta` with `Re s > 0` lies in the closed symmetric strip
`[2401 / 19200, 16799 / 19200]`. -/
theorem riemannZeta_zero_mem_sub_farkas_strip {s : ℂ}
    (h0 : 0 < s.re) (hzero : riemannZeta s = 0) :
    s.re ∈ Set.Icc (2401 / 19200 : ℝ) (16799 / 19200 : ℝ) := by
  constructor
  · exact le_of_not_gt fun hs => riemannZeta_ne_zero_of_re_lt_sub_farkas_left h0 hs hzero
  · exact le_of_not_gt fun hs => riemannZeta_ne_zero_of_sub_farkas_lt_re hs hzero

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

end
