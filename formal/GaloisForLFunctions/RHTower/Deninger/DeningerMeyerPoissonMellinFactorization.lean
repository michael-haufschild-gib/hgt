import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogMellin
import GaloisForLFunctions.RHTower.BoundedExponentDilationOperator
import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge
import GaloisForLFunctions.RHTower.ZetaTruncatedExtension

/-!
# Mellin factorization and zero annihilation of Meyer Poisson boundaries

This file proves the exact spectral factorization of Meyer's positive
dilation sum:

`M(Zg)(s) = ζ(s) M(g)(s)`.

Absolute convergence first gives the identity on `Re(s) > 1`.  For a Meyer
source, its image under the genuine all-weight logarithmic Poisson map has an
entire faithful Mellin transform.  The source Mellin transform is analytic on
`Re(s) > 0`, so the identity theorem propagates the factorization across the
punctured right half-plane.

Consequently, every actual Poisson boundary is spectrally annihilated at every
zeta zero with positive real part.  This is the concrete radical theorem
needed for Paugam's spectral pairing to descend to Meyer's quotient.

No Riemann-hypothesis premise, spectral trace premise, numerical computation,
or positivity assumption occurs.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Classical

namespace RHTower

noncomputable section

/--
Mellin multiplier law for the full positive dilation sum on its
absolute-convergence half-plane.
-/
theorem mellin_deningerMeyerSum
    {g : ℝ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hgm :
      AEStronglyMeasurable g
        (volume.restrict (Ioi 0)))
    (hg :
      IntegrableOn
        (fun x : ℝ => x ^ (s.re - 1) * ‖g x‖)
        (Ioi 0)) :
    mellin (deningerMeyerSum g) s =
      riemannZeta s * mellin g s := by
  have hconv : MellinConvergent g s :=
    (mellin_convergent_iff_norm
      (subset_refl _) measurableSet_Ioi hgm).mpr hg
  set F : ℕ → ℝ → ℂ := fun n x =>
    (x : ℂ) ^ (s - 1) •
      g (((n : ℝ) + 1) * x) with hF
  have hFint :
      ∀ n : ℕ,
        Integrable (F n)
          (volume.restrict (Ioi 0)) := by
    intro n
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by
      positivity
    have hcomp :
        MellinConvergent
          (fun t : ℝ =>
            g (((n : ℝ) + 1) * t)) s :=
      (MellinConvergent.comp_mul_left hn0).mpr
        hconv
    exact hcomp
  have hnorm :
      ∀ n : ℕ,
        (∫ x in Ioi (0 : ℝ), ‖F n x‖) =
          ((n : ℝ) + 1) ^ (-s.re) *
            ∫ x in Ioi (0 : ℝ),
              x ^ (s.re - 1) * ‖g x‖ := by
    intro n
    rw [hF]
    simpa only [Nat.cast_add, Nat.cast_one] using
      integral_norm_cpow_smul_comp_mul
        (g := g) (s := s)
        (show n + 1 ≠ 0 by omega)
  have hsummable :
      Summable fun n : ℕ =>
        ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    have hbase0 :
        Summable fun n : ℕ =>
          (n : ℝ) ^ (-s.re) := by
      rw [Real.summable_nat_rpow]
      linarith
    have hbase :
        Summable fun n : ℕ =>
          ((n : ℝ) + 1) ^ (-s.re) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).mpr hbase0
    have hI :
        (0 : ℝ) ≤
          ∫ x in Ioi (0 : ℝ),
            x ^ (s.re - 1) * ‖g x‖ :=
      setIntegral_nonneg measurableSet_Ioi
        (fun x hx =>
          mul_nonneg
            (Real.rpow_nonneg hx.le _)
            (norm_nonneg _))
    refine
      Summable.of_nonneg_of_le
        (fun n => ?_) (fun n => ?_)
        (hbase.mul_right
          (∫ x in Ioi (0 : ℝ),
            x ^ (s.re - 1) * ‖g x‖))
    · exact integral_nonneg (fun x => norm_nonneg _)
    · rw [hnorm n]
  have hsum :=
    hasSum_integral_of_summable_integral_norm
      hFint hsummable
  have hpoint :
      ∀ x : ℝ,
        (∑' n : ℕ, F n x) =
          (x : ℂ) ^ (s - 1) •
            deningerMeyerSum g x := by
    intro x
    simp only [hF, smul_eq_mul, deningerMeyerSum]
    exact tsum_mul_left
  have hterm :
      ∀ n : ℕ,
        (∫ x in Ioi (0 : ℝ), F n x) =
          ((n : ℂ) + 1) ^ (-s) *
            mellin g s := by
    intro n
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by
      positivity
    have hcongr :
        (∫ x in Ioi (0 : ℝ), F n x) =
          mellin
            (fun t : ℝ =>
              g (((n : ℝ) + 1) * t)) s := by
      rw [mellin]
    rw [hcongr,
      mellin_comp_mul_left g s hn0, smul_eq_mul]
    push_cast
    rfl
  have hmel :
      (∫ x in Ioi (0 : ℝ),
          ∑' n : ℕ, F n x) =
        mellin (deningerMeyerSum g) s := by
    rw [mellin]
    exact
      setIntegral_congr_fun measurableSet_Ioi
        (fun x _ => hpoint x)
  rw [← hmel, ← hsum.tsum_eq]
  rw [tsum_congr hterm, tsum_mul_right]
  calc
    (∑' n : ℕ, ((n : ℂ) + 1) ^ (-s)) *
          mellin g s =
        (∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s) *
          mellin g s := by
      congr 1
      apply tsum_congr
      intro n
      rw [Complex.cpow_neg, one_div]
    _ = riemannZeta s * mellin g s := by
      rw [←
        zeta_eq_tsum_one_div_nat_add_one_cpow hs]

/-- A Schwartz function has arbitrary real-power decay at positive infinity. -/
theorem schwartzMap_isBigO_atTop_rpow
    (f : SchwartzMap ℝ ℂ) (a : ℝ) :
    (f : ℝ → ℂ) =O[atTop]
      fun x : ℝ => x ^ (-a) := by
  have h :=
    (f.isBigO_cocompact_rpow (-a)).mono
      atTop_le_cocompact
  apply h.congr'
  · exact Filter.Eventually.of_forall fun _ => rfl
  · filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]

/-- A Schwartz function is bounded at the positive punctured origin. -/
theorem schwartzMap_isBigO_nhdsGT_zero_one
    (f : SchwartzMap ℝ ℂ) :
    (f : ℝ → ℂ) =O[𝓝[>] 0]
      fun _ : ℝ => (1 : ℝ) := by
  exact
    ((f.continuous.tendsto 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ

/-- Every Schwartz Mellin integral converges throughout `Re(s) > 0`. -/
theorem schwartzMap_mellinConvergent_of_re_pos
    (f : SchwartzMap ℝ ℂ) {s : ℂ}
    (hs : 0 < s.re) :
    MellinConvergent f s := by
  apply mellinConvergent_of_isBigO_rpow
    (a := s.re + 1) (b := 0)
  · exact
      (f.continuous.locallyIntegrable
        (μ := volume)).locallyIntegrableOn _
  · exact
      schwartzMap_isBigO_atTop_rpow
        f (s.re + 1)
  · linarith
  · have hone :
        (fun x : ℝ => x ^ (-(0 : ℝ))) =
          fun _ : ℝ => (1 : ℝ) := by
      funext x
      rw [neg_zero, Real.rpow_zero]
    rw [hone]
    exact schwartzMap_isBigO_nhdsGT_zero_one f
  · exact hs

/-- The Schwartz Mellin transform is holomorphic on `Re(s) > 0`. -/
theorem differentiableAt_mellin_schwartzMap_of_re_pos
    (f : SchwartzMap ℝ ℂ) {s : ℂ}
    (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin f) s := by
  apply mellin_differentiableAt_of_isBigO_rpow
    (a := s.re + 1) (b := 0)
  · exact
      (f.continuous.locallyIntegrable
        (μ := volume)).locallyIntegrableOn _
  · exact
      schwartzMap_isBigO_atTop_rpow
        f (s.re + 1)
  · linarith
  · have hone :
        (fun x : ℝ => x ^ (-(0 : ℝ))) =
          fun _ : ℝ => (1 : ℝ) := by
      funext x
      rw [neg_zero, Real.rpow_zero]
    rw [hone]
    exact schwartzMap_isBigO_nhdsGT_zero_one f
  · exact hs

/--
The faithful logarithmic transform of an actual Meyer boundary agrees with
the classical ray Mellin transform of the dilation sum, with exact signs.
-/
theorem deningerMeyerStrongLogMellin_boundary_eq_mellin
    (f : DeningerMeyerCap) (s : ℂ) :
    deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogSumLM f) s =
      mellin (deningerMeyerSum f) s := by
  rw [mellin_eq_integral_exp_neg_mul_log,
    deningerMeyerStrongLogMellin,
    ← integral_neg_eq_self
      (fun u : ℝ =>
        Complex.exp (-s * (u : ℂ)) *
          deningerMeyerSum f
            (Real.exp (-u))) volume]
  apply integral_congr_ae
  filter_upwards with t
  rw [deningerMeyerStrongLogMellinJet,
    deningerMeyerStrongLogSumLM_apply]
  simp only [pow_zero, one_mul, neg_neg]
  congr 2
  push_cast
  ring

/--
Absolute-convergence form of the exact Meyer boundary factorization.
-/
theorem
    deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin
    (f : DeningerMeyerCap) {s : ℂ}
    (hs : 1 < s.re) :
    deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogSumLM f) s =
      riemannZeta s * mellin f s := by
  rw [deningerMeyerStrongLogMellin_boundary_eq_mellin]
  apply mellin_deningerMeyerSum hs
  · exact
      f.val.continuous.aestronglyMeasurable.restrict
  · have hconv :=
      schwartzMap_mellinConvergent_of_re_pos
        f.val (lt_trans one_pos hs)
    exact
      (mellin_convergent_iff_norm
        (subset_refl _) measurableSet_Ioi
        f.val.continuous.aestronglyMeasurable.restrict).mp
          hconv

/--
Analytic-continuation form of the factorization on
`{Re(s) > 0} ∖ {1}`.
-/
theorem
    deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin_of_re_pos
    (f : DeningerMeyerCap) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogSumLM f) s =
      riemannZeta s * mellin f s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} \ {1}
  let F : ℂ → ℂ := fun z =>
    deningerMeyerStrongLogMellin
      (deningerMeyerStrongLogSumLM f) z
  let G : ℂ → ℂ := fun z =>
    riemannZeta z * mellin f z
  have hUopen : IsOpen U :=
    (isOpen_lt
      continuous_const Complex.continuous_re).sdiff
      isClosed_singleton
  have hFan : AnalyticOnNhd ℂ F U := by
    exact
      (analyticOnNhd_deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogSumLM f).property).mono
          (subset_univ U)
  have hGan : AnalyticOnNhd ℂ G U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact
      ((differentiableAt_riemannZeta hz.2).mul
        (differentiableAt_mellin_schwartzMap_of_re_pos
          f.val hz.1)).differentiableWithinAt
  have h2mem : (2 : ℂ) ∈ U := by
    exact ⟨by simp, by simp⟩
  have hevent : F =ᶠ[𝓝 (2 : ℂ)] G := by
    have hhalf :
        {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt
        continuous_const Complex.continuous_re).mem_nhds
          (by simp)
    filter_upwards [hhalf] with z hz
    exact
      deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin
        f hz
  have hEqOn : Set.EqOn F G U :=
    hFan.eqOn_of_preconnected_of_eventuallyEq hGan
      isPreconnected_halfplane_punctured
        h2mem hevent
  exact hEqOn ⟨hs0, hs1⟩

/--
**Poisson-boundary zero annihilation.**  Every genuine Meyer boundary has
zero faithful spectral transform at every zeta zero in the positive
half-plane.
-/
theorem
    deningerMeyerStrongLogMellin_boundary_zero_at_zeta_zero
    (f : DeningerMeyerCap) {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1)
    (hζ : riemannZeta ρ = 0) :
    deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogSumLM f) ρ = 0 := by
  rw [
    deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin_of_re_pos
      f hρ0 hρ1,
    hζ, zero_mul]

end

end RHTower
