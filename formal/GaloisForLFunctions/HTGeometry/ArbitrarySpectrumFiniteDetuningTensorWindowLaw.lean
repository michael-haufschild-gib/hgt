import GaloisForLFunctions.HTGeometry.FiniteDetuningTensorMajorantWindowLaw

/-!
# Arbitrary-spectrum finite-detuning tensor window law

Every finite Fejer packet splits into exactly resonant sheets, which persist on every time window,
and nonresonant sheets, whose translated-window contribution is controlled by the smallest nonzero
detuning.  The split needs no rational-independence or genericity assumption.
-/

open Real intervalIntegral MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- Nonconstant tensor-Fejer packet sheets with exactly zero temporal frequency. -/
noncomputable def resonantPacketIndexSet
    (N : ℕ) (omega : Fin d → ℝ) : Finset (Fin d → ℕ × ℕ) :=
  (nonconstantPacketIndexSet N d).filter fun k => packetFreq omega k = 0

/-- Nonconstant tensor-Fejer packet sheets with nonzero temporal frequency. -/
noncomputable def nonresonantPacketIndexSet
    (N : ℕ) (omega : Fin d → ℝ) : Finset (Fin d → ℕ × ℕ) :=
  (nonconstantPacketIndexSet N d).filter fun k => packetFreq omega k ≠ 0

/-- Minimum absolute nonzero detuning in a finite tensor-Fejer packet.  If every retained sheet is
resonant, the harmless value one is used. -/
noncomputable def finitePacketNonzeroDetuningFloor
    (N : ℕ) (omega : Fin d → ℝ) : ℝ :=
  let Q := nonresonantPacketIndexSet N omega
  if hQ : Q.Nonempty then
    (Q.image fun k => |packetFreq omega k|).min' (hQ.image _)
  else 1

theorem finitePacketNonzeroDetuningFloor_pos
    (N : ℕ) (omega : Fin d → ℝ) :
    0 < finitePacketNonzeroDetuningFloor N omega := by
  classical
  rw [finitePacketNonzeroDetuningFloor]
  split_ifs with hQ
  · let A := (nonresonantPacketIndexSet N omega).image fun k => |packetFreq omega k|
    have hmem := Finset.min'_mem A (hQ.image _)
    rw [Finset.mem_image] at hmem
    obtain ⟨k, hk, hkeq⟩ := hmem
    rw [← hkeq]
    exact abs_pos.mpr (Finset.mem_filter.mp hk).2
  · norm_num

theorem finitePacketNonzeroDetuningFloor_le
    (N : ℕ) (omega : Fin d → ℝ)
    {k : Fin d → ℕ × ℕ} (hk : k ∈ nonresonantPacketIndexSet N omega) :
    finitePacketNonzeroDetuningFloor N omega ≤ |packetFreq omega k| := by
  classical
  rw [finitePacketNonzeroDetuningFloor]
  split_ifs with hQ
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  · exact (hQ ⟨k, hk⟩).elim

theorem resonantPacketIndexSet_card_add_nonresonantPacketIndexSet_card
    (N : ℕ) (omega : Fin d → ℝ) :
    (resonantPacketIndexSet N omega).card +
        (nonresonantPacketIndexSet N omega).card =
      (nonconstantPacketIndexSet N d).card := by
  classical
  rw [resonantPacketIndexSet, nonresonantPacketIndexSet,
    ← Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter_not
        (nonconstantPacketIndexSet N d) (nonconstantPacketIndexSet N d)
        (fun k => packetFreq omega k = 0)),
    Finset.filter_union_filter_not_eq]

theorem resonantPacketIndexSet_eq_empty_of_rationallyIndependent
    {omega : Fin d → ℝ} (homega : RationallyIndependentFrequency omega)
    (N : ℕ) :
    resonantPacketIndexSet N omega = ∅ := by
  classical
  rw [resonantPacketIndexSet, Finset.filter_eq_empty_iff]
  intro k hk hfreq
  have hdet : finiteTorusCharacterDetuning (packetCharacter k) omega = 0 := by
    rw [show finiteTorusCharacterDetuning (packetCharacter k) omega =
        KleinbockMargulis.dotProd (packetCharacter k) omega by rfl,
      dotProd_packetCharacter]
    exact hfreq
  exact packetCharacter_ne_zero_of_mem_nonconstantPacketIndexSet hk
    (homega (packetCharacter k) hdet)

theorem nonresonantPacketIndexSet_eq_nonconstant_of_rationallyIndependent
    {omega : Fin d → ℝ} (homega : RationallyIndependentFrequency omega)
    (N : ℕ) :
    nonresonantPacketIndexSet N omega = nonconstantPacketIndexSet N d := by
  classical
  rw [nonresonantPacketIndexSet, Finset.filter_eq_self]
  intro k hk hfreq
  have hdet : finiteTorusCharacterDetuning (packetCharacter k) omega = 0 := by
    rw [show finiteTorusCharacterDetuning (packetCharacter k) omega =
        KleinbockMargulis.dotProd (packetCharacter k) omega by rfl,
      dotProd_packetCharacter]
    exact hfreq
  exact packetCharacter_ne_zero_of_mem_nonconstantPacketIndexSet hk
    (homega (packetCharacter k) hdet)

/-- Every translated tensor-Fejer majorant has a persistent resonant contribution and an inverse-
window nonresonant correction. -/
theorem arbitrarySpectrum_periodicProductFejerMajorant_windowMean_le
    (omega : Fin d → ℝ)
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    (c : Fin d → ℝ) (u T : ℝ) (hT : 0 < T) :
    (1 / T) * ∫ t in u..(u + T),
        periodicProductFejerMajorant N rho c (fun j => t * omega j) ≤
      (rho / (2 * π) + periodicTentFejerError N rho) ^ d +
        ((resonantPacketIndexSet N omega).card : ℝ) *
          ((((N : ℝ) + 1)⁻¹ *
            (rho / (2 * π) + periodicTentFejerError N rho)) ^ d) +
        ((nonresonantPacketIndexSet N omega).card : ℝ) *
          ((((N : ℝ) + 1)⁻¹ *
            (rho / (2 * π) + periodicTentFejerError N rho)) ^ d) *
          (2 / (T * finitePacketNonzeroDetuningFloor N omega)) := by
  classical
  let S := nonconstantPacketIndexSet N d
  let Z := resonantPacketIndexSet N omega
  let Q := nonresonantPacketIndexSet N omega
  let mu : ℝ :=
    (rho / (2 * π) + periodicTentFejerError N rho) ^ d
  let A : ℝ := (((N : ℝ) + 1)⁻¹ *
    (rho / (2 * π) + periodicTentFejerError N rho)) ^ d
  let amp : (Fin d → ℕ × ℕ) → ℂ := fun k =>
    majorantPacketAmp N rho (periodicTentFejerError N rho) c k
  let beta : (Fin d → ℕ × ℕ) → ℝ := fun k => packetFreq omega k
  let a0 : ℂ := (mu : ℂ) + ∑ k ∈ Z, amp k
  have hdelta : 0 < finitePacketNonzeroDetuningFloor N omega :=
    finitePacketNonzeroDetuningFloor_pos N omega
  have hA : 0 ≤ A := by
    dsimp [A]
    have hsum : 0 ≤ rho / (2 * π) + periodicTentFejerError N rho :=
      add_nonneg (div_nonneg hrho.le (by positivity))
        (periodicTentFejerError_pos N hrho).le
    exact pow_nonneg (mul_nonneg (inv_nonneg.mpr (by positivity)) hsum) _
  have hdisc := norm_window_mean_sub_const_le
    (ι := {k // k ∈ Q}) a0
    (fun k => amp k.1) (fun k => beta k.1)
    hdelta
    (fun k => finitePacketNonzeroDetuningFloor_le N omega k.2)
    hA
    (fun k => by
      dsimp [amp, A]
      exact norm_majorantPacketAmp_le N hrho hrhopi
        (periodicTentFejerError_pos N hrho).le c k.1)
    hT u
  have hpoint : ∀ t : ℝ,
      ((periodicProductFejerMajorant N rho c
          (fun j => t * omega j) : ℝ) : ℂ) =
        a0 + ∑ k : {k // k ∈ Q},
          amp k.1 * Complex.exp ((t : ℂ) * (beta k.1 : ℂ) * Complex.I) := by
    intro t
    rw [periodicProductFejerMajorant_eq_const_add N hrho hrhopi]
    have hsplit := Finset.sum_filter_add_sum_filter_not S
      (fun k => beta k = 0)
      (fun k => majorantPacketMode N rho (periodicTentFejerError N rho) c
        (fun j => t * omega j) k)
    have hZ :
        ∑ k ∈ S with beta k = 0,
            majorantPacketMode N rho (periodicTentFejerError N rho) c
              (fun j => t * omega j) k =
          ∑ k ∈ Z, amp k := by
      apply Finset.sum_congr
      · rfl
      · intro k hk
        have hkzero : beta k = 0 := (Finset.mem_filter.mp hk).2
        rw [majorantPacketMode_linearPhase N rho
          (periodicTentFejerError N rho) c omega k t]
        simp [amp, beta, hkzero]
    have hQ :
        ∑ k ∈ S with ¬ beta k = 0,
            majorantPacketMode N rho (periodicTentFejerError N rho) c
              (fun j => t * omega j) k =
          ∑ k : {k // k ∈ Q},
            amp k.1 * Complex.exp ((t : ℂ) * (beta k.1 : ℂ) * Complex.I) := by
      rw [Finset.sum_coe_sort Q (fun k =>
        amp k * Complex.exp ((t : ℂ) * (beta k : ℂ) * Complex.I))]
      apply Finset.sum_congr
      · rfl
      · intro k hk
        rw [majorantPacketMode_linearPhase N rho
          (periodicTentFejerError N rho) c omega k t]
    rw [← hsplit, hZ, hQ]
    simp only [a0]
    ring
  have hInt :
      (∫ t in u..(u + T),
        ((periodicProductFejerMajorant N rho c
          (fun j => t * omega j) : ℝ) : ℂ)) =
        ∫ t in u..(u + T),
          (a0 + ∑ k : {k // k ∈ Q},
            amp k.1 * Complex.exp ((t : ℂ) * (beta k.1 : ℂ) * Complex.I)) :=
    intervalIntegral.integral_congr fun t _ => hpoint t
  rw [← hInt] at hdisc
  let W : ℂ :=
    (1 / (T : ℂ)) *
      ∫ t in u..(u + T),
        ((periodicProductFejerMajorant N rho c
          (fun j => t * omega j) : ℝ) : ℂ)
  have hWre : W.re =
      (1 / T) * ∫ t in u..(u + T),
        periodicProductFejerMajorant N rho c (fun j => t * omega j) := by
    dsimp [W]
    rw [re_window_mean_ofReal
      (continuous_periodicProductFejerMajorant N rho c omega) hT u]
  have hresNorm : ‖∑ k ∈ Z, amp k‖ ≤ (Z.card : ℝ) * A := by
    calc
      ‖∑ k ∈ Z, amp k‖ ≤ ∑ k ∈ Z, ‖amp k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Z, A := by
        exact Finset.sum_le_sum fun k _ => by
          dsimp [amp, A]
          exact norm_majorantPacketAmp_le N hrho hrhopi
            (periodicTentFejerError_pos N hrho).le c k
      _ = (Z.card : ℝ) * A := by simp
  have hre : W.re ≤ mu + ‖∑ k ∈ Z, amp k‖ + ‖W - a0‖ := by
    have hdecomp : W = a0 + (W - a0) := by abel
    have hzre : (∑ k ∈ Z, amp k).re ≤ ‖∑ k ∈ Z, amp k‖ :=
      le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    have hwre : (W - a0).re ≤ ‖W - a0‖ :=
      le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    calc
      W.re = (a0 + (W - a0)).re := congrArg Complex.re hdecomp
      _ = a0.re + (W - a0).re := rfl
      _ = mu + (∑ k ∈ Z, amp k).re + (W - a0).re := by
        simp only [a0, Complex.add_re, Complex.ofReal_re]
      _ ≤ mu + ‖∑ k ∈ Z, amp k‖ + ‖W - a0‖ := by linarith
  calc
    (1 / T) * ∫ t in u..(u + T),
        periodicProductFejerMajorant N rho c (fun j => t * omega j) = W.re :=
      hWre.symm
    _ ≤ mu + ‖∑ k ∈ Z, amp k‖ + ‖W - a0‖ := hre
    _ ≤ mu + (Z.card : ℝ) * A +
        (Q.card : ℝ) * A *
          (2 / (T * finitePacketNonzeroDetuningFloor N omega)) := by
      have hd : ‖W - a0‖ ≤ (Q.card : ℝ) * A *
          (2 / (T * finitePacketNonzeroDetuningFloor N omega)) := by
        simpa [W, Q, amp, beta] using hdisc
      linarith
    _ = _ := by rfl

/-- Finite unions of cubes inherit the arbitrary-spectrum resonance-census law. -/
theorem arbitrarySpectrum_finiteCubeVisit_tensorMajorantWindowUpper
    (omega : Fin d → ℝ)
    (N m : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrhopi : 2 * rho ≤ π)
    (centers : Fin m → Fin d → ℝ) (u T : ℝ) (hT : 0 < T) :
    (volume (finiteCubeVisit rho centers omega ∩ Set.Ioc u (u + T))).toReal ≤
      (2 : ℝ) ^ d * T * (m : ℝ) *
        ((2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
          ((resonantPacketIndexSet N omega).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) +
          ((nonresonantPacketIndexSet N omega).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
            (2 / (T * finitePacketNonzeroDetuningFloor N omega))) := by
  have h2rho : 0 < 2 * rho := by positivity
  have hsingle (a : Fin m) :=
    arbitrarySpectrum_periodicProductFejerMajorant_windowMean_le
      omega N h2rho hrhopi (centers a) u T hT
  have hcont : ∀ a : Fin m, Continuous fun t : ℝ =>
      periodicProductTent (2 * rho) (centers a) (fun j => t * omega j) :=
    fun a => continuous_periodicProductTent (2 * rho) (centers a) omega
  have hsumInt :
      (1 / T) * ∫ t in u..(u + T),
          ∑ a : Fin m, periodicProductTent (2 * rho) (centers a)
            (fun j => t * omega j) ≤
        (m : ℝ) *
          ((2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
            ((resonantPacketIndexSet N omega).card : ℝ) *
              ((((N : ℝ) + 1)⁻¹ *
                (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) +
            ((nonresonantPacketIndexSet N omega).card : ℝ) *
              ((((N : ℝ) + 1)⁻¹ *
                (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
              (2 / (T * finitePacketNonzeroDetuningFloor N omega))) := by
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
              ((resonantPacketIndexSet N omega).card : ℝ) *
                ((((N : ℝ) + 1)⁻¹ *
                  (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) +
              ((nonresonantPacketIndexSet N omega).card : ℝ) *
                ((((N : ℝ) + 1)⁻¹ *
                  (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
                (2 / (T * finitePacketNonzeroDetuningFloor N omega))) := by
              exact Finset.sum_le_sum fun a _ => hsingle a
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
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
  have hmono := setIntegral_mono_on hIf hIg measurableSet_Ioc fun t _ =>
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
        T * (m : ℝ) *
          ((2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
            ((resonantPacketIndexSet N omega).card : ℝ) *
              ((((N : ℝ) + 1)⁻¹ *
                (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) +
            ((nonresonantPacketIndexSet N omega).card : ℝ) *
              ((((N : ℝ) + 1)⁻¹ *
                (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
              (2 / (T * finitePacketNonzeroDetuningFloor N omega))) := by
    calc
      (∫ t in u..(u + T),
        ∑ a : Fin m, periodicProductTent (2 * rho) (centers a)
          (fun j => t * omega j)) =
          T * ((1 / T) * ∫ t in u..(u + T),
            ∑ a : Fin m, periodicProductTent (2 * rho) (centers a)
              (fun j => t * omega j)) := by field_simp
      _ ≤ _ := by simpa only [mul_assoc] using hTmul
  exact hmono.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hInt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d))

end

end GaloisForLFunctions.HTGeometry
