import GaloisForLFunctions.HTGeometry.ProjectiveChoiTensorMajorantWindowLaw
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw

/-!
# Finite-detuning tensor-majorant window law

Finite Fourier resolution needs no asymptotic Diophantine hypothesis.  Rational independence makes
every retained nonconstant mode nonresonant, hence the finite packet has a positive minimum
detuning.  This module turns that spectroscopically finite datum into a translated-window
`1 / (T * Delta)` discrepancy bound for the positive tensor Fejer majorant.
-/

open Real intervalIntegral MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- Minimum absolute detuning in the nonconstant tensor-Fejer packet.  The empty packet receives
the harmless value one. -/
noncomputable def finitePacketDetuningFloor
    (N : ℕ) (omega : Fin d → ℝ) : ℝ :=
  let S := nonconstantPacketIndexSet N d
  if hS : S.Nonempty then
    (S.image fun k => |packetFreq omega k|).min' (hS.image _)
  else 1

theorem finitePacketDetuningFloor_pos
    {omega : Fin d → ℝ} (homega : RationallyIndependentFrequency omega)
    (N : ℕ) :
    0 < finitePacketDetuningFloor N omega := by
  classical
  rw [finitePacketDetuningFloor]
  split_ifs with hS
  · let A := (nonconstantPacketIndexSet N d).image fun k => |packetFreq omega k|
    have hmem := Finset.min'_mem A (hS.image _)
    rw [Finset.mem_image] at hmem
    obtain ⟨k, hk, hkeq⟩ := hmem
    rw [← hkeq]
    apply abs_pos.mpr
    intro hfreq
    have hdet : finiteTorusCharacterDetuning (packetCharacter k) omega = 0 := by
      rw [show finiteTorusCharacterDetuning (packetCharacter k) omega =
          KleinbockMargulis.dotProd (packetCharacter k) omega by rfl,
        dotProd_packetCharacter]
      exact hfreq
    exact packetCharacter_ne_zero_of_mem_nonconstantPacketIndexSet hk
      (homega (packetCharacter k) hdet)
  · norm_num

theorem finitePacketDetuningFloor_le
    {omega : Fin d → ℝ} (N : ℕ)
    {k : Fin d → ℕ × ℕ} (hk : k ∈ nonconstantPacketIndexSet N d) :
    finitePacketDetuningFloor N omega ≤ |packetFreq omega k| := by
  classical
  rw [finitePacketDetuningFloor]
  split_ifs with hS
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  · exact (hS ⟨k, hk⟩).elim

/-- A separated finite packet differs from its Haar constant by at most its aggregate oscillatory
cost. -/
theorem norm_window_mean_sub_const_le
    {ι : Type*} [Fintype ι]
    (a0 : ℂ) (c : ι → ℂ) (beta : ι → ℝ)
    {betaMin coeffBound T : ℝ}
    (hbetaMin : 0 < betaMin) (hbeta : ∀ i, betaMin ≤ |beta i|)
    (hcoeffBound : 0 ≤ coeffBound) (hc : ∀ i, ‖c i‖ ≤ coeffBound)
    (hT : 0 < T) (u : ℝ) :
    ‖((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            (a0 + ∑ i, c i *
              Complex.exp ((t : ℂ) * (beta i : ℂ) * Complex.I))) - a0‖ ≤
      (Fintype.card ι : ℝ) * coeffBound * (2 / (T * betaMin)) := by
  classical
  have hint : IntervalIntegrable
      (fun t : ℝ => ∑ i, c i *
        Complex.exp ((t : ℂ) * (beta i : ℂ) * Complex.I))
      volume u (u + T) := by
    have hcont : Continuous fun t : ℝ => ∑ i, c i *
        Complex.exp ((t : ℂ) * (beta i : ℂ) * Complex.I) := by
      refine continuous_finsetSum _ fun i _ => ?_
      fun_prop
    exact hcont.intervalIntegrable u (u + T)
  have hcenter :
      ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            (a0 + ∑ i, c i *
              Complex.exp ((t : ℂ) * (beta i : ℂ) * Complex.I))) - a0 =
        (1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ i, c i *
              Complex.exp ((t : ℂ) * (beta i : ℂ) * Complex.I) := by
    let J : ℂ := ∫ t in u..(u + T),
      ∑ i, c i * Complex.exp ((t : ℂ) * (beta i : ℂ) * Complex.I)
    have hadd :
        (∫ t in u..(u + T),
          (a0 + ∑ i, c i *
            Complex.exp ((t : ℂ) * (beta i : ℂ) * Complex.I))) =
          (T : ℂ) * a0 + J := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hint,
        intervalIntegral.integral_const, add_sub_cancel_left, Complex.real_smul]
    rw [hadd]
    change (1 / (T : ℂ)) * ((T : ℂ) * a0 + J) - a0 =
      (1 / (T : ℂ)) * J
    have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hT
    field_simp
    ring
  rw [hcenter]
  exact norm_window_mean_le c beta hbetaMin hbeta hcoeffBound hc hT u

/-- Rational independence gives a completely finite, spectroscopically calibrated upper window
law for every translated tensor majorant. -/
theorem rationallyIndependent_periodicProductFejerMajorant_windowMean_le
    {omega : Fin d → ℝ} (homega : RationallyIndependentFrequency omega)
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    (c : Fin d → ℝ) (u T : ℝ) (hT : 0 < T) :
    (1 / T) * ∫ t in u..(u + T),
        periodicProductFejerMajorant N rho c (fun j => t * omega j) ≤
      (rho / (2 * π) + periodicTentFejerError N rho) ^ d +
        ((nonconstantPacketIndexSet N d).card : ℝ) *
          ((((N : ℝ) + 1)⁻¹ *
            (rho / (2 * π) + periodicTentFejerError N rho)) ^ d) *
          (2 / (T * finitePacketDetuningFloor N omega)) := by
  classical
  let S := nonconstantPacketIndexSet N d
  let mu : ℝ :=
    (rho / (2 * π) + periodicTentFejerError N rho) ^ d
  let A : ℝ := (((N : ℝ) + 1)⁻¹ *
    (rho / (2 * π) + periodicTentFejerError N rho)) ^ d
  have hdelta : 0 < finitePacketDetuningFloor N omega :=
    finitePacketDetuningFloor_pos homega N
  have hA : 0 ≤ A := by
    dsimp [A]
    have hsum : 0 ≤ rho / (2 * π) + periodicTentFejerError N rho :=
      add_nonneg (div_nonneg hrho.le (by positivity))
        (periodicTentFejerError_pos N hrho).le
    exact pow_nonneg (mul_nonneg (inv_nonneg.mpr (by positivity)) hsum) _
  have hdisc := norm_window_mean_sub_const_le
    (ι := {k // k ∈ S}) (mu : ℂ)
    (fun k => majorantPacketAmp N rho (periodicTentFejerError N rho) c k.1)
    (fun k => packetFreq omega k.1)
    hdelta
    (fun k => finitePacketDetuningFloor_le N k.2)
    hA
    (fun k => norm_majorantPacketAmp_le N hrho hrhopi
      (periodicTentFejerError_pos N hrho).le c k.1)
    hT u
  have hpoint : ∀ t : ℝ,
      ((periodicProductFejerMajorant N rho c
          (fun j => t * omega j) : ℝ) : ℂ) =
        (mu : ℂ) +
          ∑ k : {k // k ∈ S},
            majorantPacketAmp N rho (periodicTentFejerError N rho) c k.1 *
              Complex.exp ((t : ℂ) * (packetFreq omega k.1 : ℂ) * Complex.I) := by
    intro t
    rw [periodicProductFejerMajorant_eq_const_add N hrho hrhopi]
    congr 1
    rw [Finset.sum_coe_sort S (fun k =>
      majorantPacketAmp N rho (periodicTentFejerError N rho) c k *
        Complex.exp ((t : ℂ) * (packetFreq omega k : ℂ) * Complex.I))]
    exact Finset.sum_congr rfl fun k _ =>
      majorantPacketMode_linearPhase N rho (periodicTentFejerError N rho)
        c omega k t
  have hInt :
      (∫ t in u..(u + T),
        ((periodicProductFejerMajorant N rho c
          (fun j => t * omega j) : ℝ) : ℂ)) =
        ∫ t in u..(u + T),
          ((mu : ℂ) +
            ∑ k : {k // k ∈ S},
              majorantPacketAmp N rho (periodicTentFejerError N rho) c k.1 *
                Complex.exp ((t : ℂ) * (packetFreq omega k.1 : ℂ) * Complex.I)) :=
    intervalIntegral.integral_congr fun t _ => hpoint t
  rw [← hInt] at hdisc
  let Z : ℂ :=
    ((1 / (T : ℂ)) *
      ∫ t in u..(u + T),
        ((periodicProductFejerMajorant N rho c
          (fun j => t * omega j) : ℝ) : ℂ)) - (mu : ℂ)
  have hre : Z.re ≤ ‖Z‖ :=
    le_trans (le_abs_self Z.re) (Complex.abs_re_le_norm Z)
  have hupper : Z.re ≤
      ((S.card : ℝ) * A *
        (2 / (T * finitePacketDetuningFloor N omega))) := by
    exact hre.trans (by simpa [Z, S, A] using hdisc)
  have hcont := continuous_periodicProductFejerMajorant N rho c omega
  have hreal : Z.re =
      ((1 / T) * (∫ t in u..(u + T),
        periodicProductFejerMajorant N rho c (fun j => t * omega j))) - mu := by
    dsimp [Z]
    rw [re_window_mean_ofReal hcont hT u]
  rw [hreal] at hupper
  dsimp [S, A, mu] at hupper ⊢
  linarith

/-- Finite unions of draw-adaptive cubes inherit the explicit finite-detuning tensor law. -/
theorem rationallyIndependent_finiteCubeVisit_tensorMajorantWindowUpper
    {omega : Fin d → ℝ} (homega : RationallyIndependentFrequency omega)
    (N m : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrhopi : 2 * rho ≤ π)
    (centers : Fin m → Fin d → ℝ) (u T : ℝ) (hT : 0 < T) :
    (volume (finiteCubeVisit rho centers omega ∩ Set.Ioc u (u + T))).toReal ≤
      (2 : ℝ) ^ d * T *
        (((m : ℕ) : ℝ) *
            (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
          ((m : ℕ) : ℝ) * ((nonconstantPacketIndexSet N d).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
            (2 / (T * finitePacketDetuningFloor N omega))) := by
  have h2rho : 0 < 2 * rho := by positivity
  have hsingle (a : Fin m) :=
    rationallyIndependent_periodicProductFejerMajorant_windowMean_le
      homega N h2rho hrhopi (centers a) u T hT
  have hcont : ∀ a : Fin m, Continuous fun t : ℝ =>
      periodicProductTent (2 * rho) (centers a) (fun j => t * omega j) :=
    fun a => continuous_periodicProductTent (2 * rho) (centers a) omega
  have hsumInt :
      (1 / T) * ∫ t in u..(u + T),
          ∑ a : Fin m, periodicProductTent (2 * rho) (centers a)
            (fun j => t * omega j) ≤
        ((m : ℕ) : ℝ) *
            (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
          ((m : ℕ) : ℝ) * ((nonconstantPacketIndexSet N d).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
            (2 / (T * finitePacketDetuningFloor N omega)) := by
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      calc
        ∑ a : Fin m, (1 / T) *
            ∫ t in u..(u + T),
              periodicProductTent (2 * rho) (centers a)
                (fun j => t * omega j) ≤
          ∑ a : Fin m, (1 / T) *
            ∫ t in u..(u + T),
              periodicProductFejerMajorant N (2 * rho) (centers a)
                (fun j => t * omega j) := by
            exact Finset.sum_le_sum fun a _ =>
              mul_le_mul_of_nonneg_left
                (intervalIntegral.integral_mono_on (by linarith)
                  ((hcont a).intervalIntegrable _ _)
                  ((continuous_periodicProductFejerMajorant N (2 * rho)
                    (centers a) omega).intervalIntegrable _ _)
                  (fun t _ => periodicProductTent_le_periodicProductFejerMajorant
                    N h2rho (centers a) _))
                (by positivity)
        _ ≤ ∑ _a : Fin m,
            ((2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
              ((nonconstantPacketIndexSet N d).card : ℝ) *
                ((((N : ℝ) + 1)⁻¹ *
                  (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
                (2 / (T * finitePacketDetuningFloor N omega))) := by
              exact Finset.sum_le_sum fun a _ => hsingle a
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    · intro a _
      exact (hcont a).intervalIntegrable u (u + T)
  have hle : u ≤ u + T := by linarith
  have hfin : volume (Set.Ioc u (u + T)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hIf : IntegrableOn
      (Set.indicator (finiteCubeVisit rho centers omega) (fun _ => (1 : ℝ)))
      (Set.Ioc u (u + T)) :=
    (integrableOn_const (C := (1 : ℝ)) hfin (by simp)).indicator
      (measurableSet_finiteCubeVisit rho centers omega)
  have hIg : IntegrableOn
      (fun t => (2 : ℝ) ^ d * ∑ a : Fin m,
        periodicProductTent (2 * rho) (centers a) (fun j => t * omega j))
      (Set.Ioc u (u + T)) := by
    have hc : Continuous fun t : ℝ => ∑ a : Fin m,
        periodicProductTent (2 * rho) (centers a) (fun j => t * omega j) :=
      continuous_finsetSum _ fun a _ => hcont a
    exact (continuous_const.mul hc).intervalIntegrable u (u + T) |>.1
  have hmono :
      ∫ t in Set.Ioc u (u + T),
          Set.indicator (finiteCubeVisit rho centers omega) (fun _ => (1 : ℝ)) t ≤
        ∫ t in Set.Ioc u (u + T),
          (2 : ℝ) ^ d * ∑ a : Fin m,
            periodicProductTent (2 * rho) (centers a) (fun j => t * omega j) :=
    setIntegral_mono_on hIf hIg measurableSet_Ioc fun t _ =>
      indicator_finiteCubeVisit_le_scaled_sum_tent hrho centers omega t
  have hind :
      ∫ t in Set.Ioc u (u + T),
          Set.indicator (finiteCubeVisit rho centers omega) (fun _ => (1 : ℝ)) t =
        (volume (finiteCubeVisit rho centers omega ∩ Set.Ioc u (u + T))).toReal := by
    rw [setIntegral_indicator (measurableSet_finiteCubeVisit rho centers omega),
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    rw [Set.inter_comm]
  have hright :
      ∫ t in Set.Ioc u (u + T),
          (2 : ℝ) ^ d * ∑ a : Fin m,
            periodicProductTent (2 * rho) (centers a) (fun j => t * omega j) =
        (2 : ℝ) ^ d * ∫ t in u..(u + T),
          ∑ a : Fin m, periodicProductTent (2 * rho) (centers a)
            (fun j => t * omega j) := by
    rw [← intervalIntegral.integral_of_le hle,
      intervalIntegral.integral_const_mul]
  rw [hind, hright] at hmono
  have hTmul := mul_le_mul_of_nonneg_left hsumInt hT.le
  have hInt :
      (∫ t in u..(u + T),
        ∑ a : Fin m, periodicProductTent (2 * rho) (centers a)
          (fun j => t * omega j)) ≤
        T *
          (((m : ℕ) : ℝ) *
              (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
            ((m : ℕ) : ℝ) * ((nonconstantPacketIndexSet N d).card : ℝ) *
              ((((N : ℝ) + 1)⁻¹ *
                (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
              (2 / (T * finitePacketDetuningFloor N omega))) := by
    calc
      (∫ t in u..(u + T),
        ∑ a : Fin m, periodicProductTent (2 * rho) (centers a)
          (fun j => t * omega j)) =
          T * ((1 / T) * ∫ t in u..(u + T),
            ∑ a : Fin m, periodicProductTent (2 * rho) (centers a)
              (fun j => t * omega j)) := by field_simp
      _ ≤ _ := hTmul
  exact hmono.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hInt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d))

end

end GaloisForLFunctions.HTGeometry
