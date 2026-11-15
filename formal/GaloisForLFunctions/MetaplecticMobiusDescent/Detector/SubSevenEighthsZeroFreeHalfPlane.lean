import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsHighTransport

/-!
# Unconditional Zero-Free Half-Plane Below Seven Eighths

Combining the common detector bounds of `SubSevenEighthsHighTransport` at the balanced cubic-probe
geometry `(17/48, 479/1000, 1001/6000)` (`lowBoundary = 20999/24000 = 7/8 - 1/24000`) with
regularized Mellin continuation over all primitive Hecke characters of `K = ℚ(ω)` establishes:

* `hecke_beta_le_sub_seven_eighths`: `HeckeZeroSupremum.beta ≤ 20999 / 24000`.
* `hecke_ne_zero_of_sub_seven_eighths_lt_re`: every Hecke `L`-function of `ℚ(ω)` is nonzero on
  `Re s > 20999 / 24000` away from `(s = 1, χ.residue = 1)`.
* `DirichletCharacter.LFunction_ne_zero_of_sub_seven_eighths_lt_re`: every Dirichlet `L`-function is
  nonzero on `Re s > 20999 / 24000` away from `(χ = 1, s = 1)`.
* `riemannZeta_ne_zero_of_sub_seven_eighths_lt_re`, `riemannZeta_ne_zero_of_re_lt_sub_one_eighth`,
  and `riemannZeta_zero_mem_sub_quasiRH_strip`: `riemannZeta` is nonzero on `Re s > 20999 / 24000`
  and on `0 < Re s < 3001 / 24000`, confining every zero with `Re s > 0` to
  `[3001 / 24000, 20999 / 24000]`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Classical

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

namespace SubSevenEighthsZeroFree

open HeckeFamily HeckeZeroSupremum

/-- Unconditionally, the supremum `HeckeZeroSupremum.beta` of real parts of zeros across all Hecke
`L`-functions of `ℚ(ω)` satisfies `beta ≤ 20999 / 24000 = 7 / 8 - 1 / 24000`. -/
theorem hecke_beta_le_sub_seven_eighths : HeckeZeroSupremum.beta ≤ 20999 / 24000 := by
  by_contra hn
  have hβ : (20999 / 24000 : ℝ) < HeckeZeroSupremum.beta := lt_of_not_ge hn
  obtain ⟨loss, σ, hloss, hloss_lt, hσ, hprobe⟩ :=
    SubSevenEighthsHighTransport.exists_sub_common_probe hβ
  set a : ℝ := max (20999 / 24000 + loss) (HeckeZeroSupremum.beta - σ)
  have ha_lt_β : a < HeckeZeroSupremum.beta := max_lt (by linarith) (by linarith)
  have ha_gt_4350 : (43 / 50 : ℝ) < a :=
    lt_of_lt_of_le (by linarith) (le_max_left (20999 / 24000 + loss) (HeckeZeroSupremum.beta - σ))
  have ha_lt_two : a < 2 :=
    lt_of_lt_of_le ha_lt_β (HeckeZeroSupremum.beta_le_one.trans (by norm_num))
  obtain ⟨η, ρ, _hp, hhalf, _hone, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta (ε := HeckeZeroSupremum.beta - a)
      (by linarith) (by linarith)
  have hρa : a < ρ.re := by linarith
  obtain ⟨χ, H, J, hmask, hH43, hb43, hJ, herr⟩ := hprobe η
  have hH78 : AnalyticOnNhd ℂ H {s : ℂ | 7 / 8 < s.re} :=
    hH43.mono fun s hs => by
      change (43 / 50 : ℝ) < s.re
      change (7 / 8 : ℝ) < s.re at hs
      linarith
  have hb78 : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2 :=
    fun s hs => hb43 s (by linarith)
  have hHa : AnalyticOnNhd ℂ H {s : ℂ | a < s.re} :=
    hH43.mono fun s hs => by
      change (43 / 50 : ℝ) < s.re
      change a < s.re at hs
      linarith
  have htop : HeckeSignal.signal χ H (-24749 / 36000) =O[atTop]
      (fun Z : ℝ => Z ^ (a + (-24749 / 36000))) := by
    have hmax : max (13499 / 72000 + loss) (HeckeZeroSupremum.beta - 24749 / 36000 - σ) =
        a + (-24749 / 36000) := by
      calc max (13499 / 72000 + loss) (HeckeZeroSupremum.beta - 24749 / 36000 - σ)
        _ = max ((20999 / 24000 + loss) + (-24749 / 36000))
              ((HeckeZeroSupremum.beta - σ) + (-24749 / 36000)) := by
              congr 1 <;> ring
        _ = a + (-24749 / 36000) := max_add_add_right _ _ _
    simpa only [hmax] using
      Continuation.common_signal_bound J (HeckeSignal.signal χ H (-24749 / 36000))
        (13499 / 72000 + loss) (HeckeZeroSupremum.beta - 24749 / 36000 - σ) hJ herr
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr fun hc => hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc)
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask (by linarith) hχpole,
      hz, zero_mul]
  have hHd : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re} := hH78.differentiableOn
  have hne : LFunction χ ρ ≠ 0 :=
    Continuation.nonzero_of_regularized_signal a 1 (-24749 / 36000)
      (LFunction χ) (HeckeSignal.regularL χ) (HeckeSignal.targetRegularizer χ)
      (Continuation.gaussianMultiplier H) (HeckeSignal.signal χ H (-24749 / 36000))
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (HeckeSignal.regularL_entire χ)).mono (Set.subset_univ _))
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (HeckeSignal.targetRegularizer_entire χ)).mono (Set.subset_univ _))
      (Continuation.gaussianMultiplier_analytic hHa)
      (HeckeSignal.signal_locallyIntegrable χ H hHd hb78 (-24749 / 36000))
      htop
      (HeckeSignal.signal_rapidDecayAtZero χ H hHd hb78 (-24749 / 36000))
      (fun s hs => by
        have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
        have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
        have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
        rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
          HeckeSignal.signalMellin_eq_amplitude χ H hHd hb78 (-24749 / 36000) a ha_lt_two htop hs]
        unfold HeckeSignal.amplitude HeckeSignal.quotient Continuation.gaussianMultiplier
        rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
        have hn := LFunction_ne_zero_of_one_lt_re χ hs1
        field_simp)
      hρa
      (HeckeSignal.regularL_eq χ (by intro h; rw [h, Complex.zero_re] at hρa; linarith) hχpole)
      (HeckeSignal.targetRegularizer_ne_zero χ hχpole)
      (Continuation.gaussianMultiplier_ne_zero (hb43 ρ (ha_gt_4350.trans hρa)))
  exact hne hzχ

/-- Every Hecke `L`-function of `ℚ(ω)` is nonzero on `Re s > 20999 / 24000` away from its pole. -/
theorem hecke_ne_zero_of_sub_seven_eighths_lt_re (χ : Character) (s : ℂ)
    (hs : (20999 / 24000 : ℝ) < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_beta_lt χ (hecke_beta_le_sub_seven_eighths.trans_lt hs) hpole

/-- Norm base change transfers any positive Hecke zero-free half-plane `Re s > B` (`B > 0`) to all
Dirichlet `L`-functions away from the principal pole `(χ = 1, s = 1)`. -/
theorem dirichlet_ne_zero_of_hecke {B : ℝ} (hB : 0 < B)
    (hH : ∀ (η : Character) (s : ℂ), B < s.re → (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : B < s.re)
    (hexc : ¬(χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have h := hH (HeckeDirichlet.character χ) s hs (Or.inl hs1)
  rw [HeckeDirichlet.LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

/--Every Dirichlet `L`-function is nonzero on `Re s > 20999 / 24000` away from `(χ = 1, s = 1)`. -/
theorem dirichlet_sub_seven_eighths_nonzero (q : ℕ) (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : (20999 / 24000 : ℝ) < s.re) (hexc : ¬(χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  letI : NeZero q := ⟨hq⟩
  exact dirichlet_ne_zero_of_hecke (by norm_num) hecke_ne_zero_of_sub_seven_eighths_lt_re χ hs hexc

end SubSevenEighthsZeroFree

/-- Every Dirichlet `L`-function is nonzero on `Re s > 20999 / 24000` away from `(χ = 1, s = 1)`. -/
theorem DirichletCharacter.LFunction_ne_zero_of_sub_seven_eighths_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : (20999 / 24000 : ℝ) < s.re)
    (hpole : ¬(χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  SubSevenEighthsZeroFree.dirichlet_sub_seven_eighths_nonzero q (NeZero.ne q) χ s hs hpole

/-- `riemannZeta` has no zeros on the open half-plane `Re s > 20999 / 24000`. -/
theorem riemannZeta_ne_zero_of_sub_seven_eighths_lt_re {s : ℂ}
    (hs : (20999 / 24000 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := DirichletCharacter.LFunction_ne_zero_of_sub_seven_eighths_lt_re
    (1 : DirichletCharacter ℂ 1) hs (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

/-- Functional reflection `s ↦ 1 - s` transfers the `20999 / 24000` right half-plane to nonvanishing
of `riemannZeta` on `0 < Re s < 3001 / 24000` (`= 1 / 8 + 1 / 24000`). -/
theorem riemannZeta_ne_zero_of_re_lt_sub_one_eighth {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < (3001 / 24000 : ℝ)) : riemannZeta s ≠ 0 := by
  intro hzero
  have hs0 : s ≠ 0 := by
    intro hs
    simpa only [hs, Complex.zero_re, lt_self_iff_false] using h0
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
  apply riemannZeta_ne_zero_of_sub_seven_eighths_lt_re (s := 1 - s) _ hreflect
  simp only [Complex.sub_re, Complex.one_re]
  linarith only [h1]

/-- Every zero of `riemannZeta` with `Re s > 0` lies in the closed symmetric strip
`[3001 / 24000, 20999 / 24000]`. -/
theorem riemannZeta_zero_mem_sub_quasiRH_strip {s : ℂ}
    (h0 : 0 < s.re) (hzero : riemannZeta s = 0) :
    s.re ∈ Set.Icc (3001 / 24000 : ℝ) (20999 / 24000 : ℝ) := by
  constructor
  · exact le_of_not_gt fun hs => riemannZeta_ne_zero_of_re_lt_sub_one_eighth h0 hs hzero
  · exact le_of_not_gt fun hs => riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hs hzero

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

end
