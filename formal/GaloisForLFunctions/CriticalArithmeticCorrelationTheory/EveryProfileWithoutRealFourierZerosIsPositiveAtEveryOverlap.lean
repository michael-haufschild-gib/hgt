import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.EveryProfileWithoutRealFourierZerosKeepsAGammaReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilFormKeepsADefectReserveAtEveryOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapPositivityAtEveryOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapConductorFloor
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy

/-!
# Every profile without real Fourier zeros is positive at every overlap

The fixed-overlap positivity of the tilted spline uses three profile inputs: the Gamma reserve,
the defect reserve built on it, and the conductor floor `(2/M) ∫_{t>c} |φ̂(2πt)|²`. Each needs only
that the profile is `C²`, supported in `[0, 1]`, and has a Fourier transform without real zeros.
For every such profile and every `c > 0` the complete Weil matrix is eventually positive definite
(`eventually_noRealZero_completeWeilMatrix_posDef`), its low spectrum is counted by the completed
conductor energies, and its bottom converges to the completed shell energy.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology RHTower
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics ArithmeticEffectivityTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell ArithmeticCastelnuovoSeveri Zeta23

section NoRealZero

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
  (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
include hφ hsupp hFT

/-- The Gamma form pays the logarithmic coefficient counterterm with a strictly
subunit prime-defect cost, uniformly in the horizon at every fixed overlap. -/
theorem exists_noRealZero_gamma_defect_payment {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
        Real.log N * (∑ n ∈ Icc 1 N, x n ^ 2) -
            (1 - a) * poleDefect N x - C * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
          archForm (atomicTest N x (atomDilate φ (c / N))) /
            ((c / N) * ∫ u, φ u ^ 2) := by
  obtain ⟨a₀, ha₀, b, hb, hband⟩ := exists_noRealZero_archForm_reserve hφ hsupp hFT hc
  let δ := min a₀ (1 / 2)
  have hδ : 0 < δ := lt_min ha₀ (by norm_num)
  have hδa : δ ≤ a₀ := min_le_left _ _
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  -- The cutoff separates low atoms and makes their defect cost smaller than the tail reserve.
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 (max (4 * c) (128 * Real.exp 2 * c / δ)))
  have hL1R : (1 : ℝ) < L := (le_max_left _ _).trans_lt hL
  have hL1 : 1 ≤ L := by exact_mod_cast hL1R.le
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hLc : 4 * c ≤ L :=
    (le_max_left (4 * c) _).trans ((le_max_right _ _).trans hL.le)
  have hLδ : 128 * Real.exp 2 * c / δ ≤ L :=
    (le_max_right (4 * c) _).trans ((le_max_right _ _).trans hL.le)
  let A := separatedCrossMassCost
  let B := 1 + 2 * c * Real.exp c
  let C₀ := |Real.log c - 2 * gammaHardyPhaseRate 0| + 2 * c * A
  let R := Real.log (2 * (L : ℝ))
  let J := (Real.log 4 + 4) + (Real.log 8 + 4)
  let T := (1 + 4 / δ) * (R + J) + R
  let C := C₀ + b + 2 * Real.pi * B + (1 - δ) * T
  have hA : 0 ≤ A := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    dsimp only [A, separatedCrossMassCost]
    positivity
  have hB : 1 ≤ B := by
    have hp : 0 ≤ 2 * c * Real.exp c := by positivity
    dsimp only [B]
    linarith only [hp]
  have hB0 : 0 ≤ B := by linarith only [hB]
  have hC₀ : 0 ≤ C₀ := add_nonneg (abs_nonneg _) (by positivity)
  have hR : 0 ≤ R := Real.log_nonneg (by nlinarith only [hL1R])
  have hJ : 0 ≤ J := by
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    have h8 := Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)
    dsimp only [J]
    linarith only [h4, h8]
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hδle : 0 ≤ 1 - δ := by linarith only [hδ1]
  refine ⟨δ / 2, by positivity, C, by dsimp only [C]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop L] with N hLN
  intro x
  let M := N / L
  let w := c / (N : ℝ)
  let g := atomDilate φ w
  let y := atomicTailCoefficients M x
  let S := ∑ n ∈ Icc 1 N, x n ^ 2
  let S₀ := ∑ n ∈ Icc 1 M, x n ^ 2
  let S₁ := ∑ n ∈ Icc 1 N, y n ^ 2
  let G := w * ∫ u, φ u ^ 2
  have hM : 1 ≤ M := Nat.div_pos hLN (by omega)
  have hMN : M ≤ N := Nat.div_le_self N L
  have hN : 1 ≤ N := hL1.trans hLN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hML : (M : ℝ) * L ≤ N := by exact_mod_cast Nat.div_mul_le_self N L
  have hNML : (N : ℝ) < (M + 1) * L := by
    have ht := Nat.lt_mul_div_succ N (show 0 < L by omega)
    have ht' : N < (M + 1) * L := by simpa only [M, Nat.mul_comm] using ht
    exact_mod_cast ht'
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNRM : (N : ℝ) ≤ 2 * L * M := by
    nlinarith only [hNML, mul_nonneg (sub_nonneg.mpr hM1R) hLR.le]
  have hw : 0 < w := div_pos hc hNR
  have hwN : w * N = c := by dsimp only [w]; field_simp [hNR.ne']
  have hwM : w * M ≤ c / L := by
    apply (le_div_iff₀ hLR).mpr
    calc
      _ = w * ((M : ℝ) * L) := by ring
      _ ≤ w * N := mul_le_mul_of_nonneg_left hML hw.le
      _ = c := hwN
  have hwMc : w * M ≤ c := by
    calc
      _ ≤ w * N := mul_le_mul_of_nonneg_left (by exact_mod_cast hMN) hw.le
      _ = c := hwN
  have hw1 : w ≤ 1 := by
    apply (div_le_one hNR).mpr
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [hLc, hLNR, hc]
  have hsep : w ≤ atomSpacing M / 2 := by
    have hfour : 4 * w * M ≤ 1 := by
      have hl : 4 * (c / (L : ℝ)) ≤ 1 := by
        rw [← mul_div_assoc, div_le_one hLR]
        exact hLc
      nlinarith only [hwM, hl]
    have hbound : w ≤ (1 / ((M : ℝ) + 1)) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).mpr
      nlinarith only [hfour, mul_nonneg hw.le (sub_nonneg.mpr hM1R)]
    exact hbound.trans (div_le_div_of_nonneg_right (atomSpacing_bounds hM).1 (by norm_num))
  have hsmall : 32 * Real.exp 2 * w * M ≤ δ / 4 := by
    have hcost : 32 * Real.exp 2 * (c / (L : ℝ)) ≤ δ / 4 := by
      have hl := (div_le_iff₀ hδ).mp hLδ
      have hd : (128 * Real.exp 2 * c) / (L : ℝ) ≤ δ :=
        (div_le_iff₀ hLR).mpr (by nlinarith only [hl])
      have he : (128 * Real.exp 2 * c) / (L : ℝ) = 4 * (32 * Real.exp 2 * (c / L)) := by ring
      rw [he] at hd
      linarith only [hd]
    calc
      _ = (32 * Real.exp 2) * (w * M) := by ring
      _ ≤ (32 * Real.exp 2) * (c / (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hwM (by positivity)
      _ ≤ _ := hcost
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hratio : Real.log N - Real.log M ≤ R := by
    rw [← Real.log_div hNR.ne' hMR.ne']
    exact Real.log_le_log (div_pos hNR hMR) ((div_le_iff₀ hMR).mpr hNRM)
  have hS : 0 ≤ S := sum_nonneg fun n _ => sq_nonneg _
  have hS₀ : 0 ≤ S₀ := sum_nonneg fun n _ => sq_nonneg _
  have hS₁ : 0 ≤ S₁ := sum_nonneg fun n _ => sq_nonneg _
  have hsplit : S₀ + S₁ = S := sum_sq_prefix_add_tail hMN x
  have hS₀S : S₀ ≤ S := by linarith only [hsplit, hS₁]
  have hS₁S : S₁ ≤ S := by linarith only [hsplit, hS₀]
  have hG : 0 < G := mul_pos hw (integral_sq_pos_of_noRealZero hφ hsupp hFT)
  have hg : ContDiff ℝ 2 g := hφ.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g := hasCompactSupport_atomDilate hw.ne' (hasCompactSupport_of_unitSupport hsupp)
  have hsupp := (atom_support_of_unitSupport hsupp) hw
  have hmass : (∫ u, g u ^ 2) = G := integral_atomDilate_sq hw
  have hD : 0 ≤ poleDefect N x := poleDefect_nonneg N x
  have hDM : poleDefect M x ≤ poleDefect N x := poleDefect_prefix_le hMN x
  have hlogw : Real.log (1 / w) = Real.log N - Real.log c := by
    dsimp only [w]
    rw [one_div_div, Real.log_div hNR.ne' hc.ne']
  -- Keep the unit self-energy coefficient on the separated prefix.
  have hlo : Real.log N * S₀ - C₀ * S - δ / 4 * poleDefect N x ≤
      archForm (atomicTest M x g) / G := by
    have hraw := archForm_atomicTest_ge_separated_defect hg hgc hsupp hM hw hw1 hsep x
    rw [hmass] at hraw
    have hcoef : Real.log N - C₀ ≤
        2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - 2 * w * M * separatedCrossMassCost := by
      have habs := le_abs_self (Real.log c - 2 * gammaHardyPhaseRate 0)
      have hcost := mul_le_mul_of_nonneg_right hwMc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
      rw [hlogw]
      dsimp only [C₀, A]
      dsimp only [A] at hcost
      linarith only [habs, hcost]
    have hpay : 32 * Real.exp 2 * w * M * poleDefect M x ≤ δ / 4 * poleDefect N x :=
      mul_le_mul hsmall hDM (poleDefect_nonneg M x) (by positivity)
    have hleft := mul_le_mul_of_nonneg_right hcoef hS₀
    have hmassCost := mul_le_mul_of_nonneg_left hS₀S hC₀
    have hl : Real.log N * S₀ - C₀ * S - δ / 4 * poleDefect N x ≤
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - 2 * w * M * separatedCrossMassCost) *
          S₀ - 32 * Real.exp 2 * w * M * poleDefect M x := by
      linarith only [hleft, hpay, hmassCost]
    apply (le_div_iff₀ hG).mpr
    have hlG := mul_le_mul_of_nonneg_left hl hG.le
    simpa only [mul_comm G] using hlG.trans hraw
  -- The explicit Fourier floor supplies a positive logarithmic reserve on the tail.
  have hhi : δ * Real.log N * S₁ - b * S ≤ archForm (atomicTest N y g) / G := by
    have hh := hband N hN y
    have ha := mul_le_mul_of_nonneg_right hδa (mul_nonneg hlog hS₁)
    have hbS := mul_le_mul_of_nonneg_left hS₁S hb
    change (a₀ * Real.log N - b) * S₁ ≤ archForm (atomicTest N y g) / G at hh
    linarith only [hh, ha, hbS]
  have hordered := atomicTest_prefix_tail_ordered hsupp hM
    (by have hp := atomSpacing_pos hM; linarith only [hsep, hp]) N x
  obtain ⟨boundary, hleft, hright⟩ := hordered
  have hcross := archForm_add_ge_of_ordered
    (contDiff_atomicTest hg M x) (hasCompactSupport_atomicTest hsupp M x)
    (contDiff_atomicTest hg N y) (hasCompactSupport_atomicTest hsupp N y) hleft hright
  rw [← atomicTest_eq_prefix_add_tail hMN x g] at hcross
  have hloMass : (∫ u, atomicTest M x g u ^ 2) = S₀ * G := by
    rw [integral_atomicTest_sq hg hgc hsupp
      (by have hp := atomSpacing_pos hM; linarith only [hsep, hp]), hmass]
  have hhiMass : (∫ u, atomicTest N y g u ^ 2) ≤ G * B * S₁ := by
    have h := integral_atomicTest_sq_le_fixed_overlap hg.continuous hgc hc hN hsupp y
    rw [hmass] at h
    exact h
  have hphysical : (∫ u, atomicTest M x g u ^ 2) + (∫ u, atomicTest N y g u ^ 2) ≤ G * B * S := by
    have hlow := mul_le_mul_of_nonneg_right hB (mul_nonneg hG.le hS₀)
    have hsplitMass := congrArg (fun z : ℝ => G * B * z) hsplit
    rw [hloMass]
    linarith only [hhiMass, hlow, hsplitMass]
  have hcombined : archForm (atomicTest M x g) / G + archForm (atomicTest N y g) / G -
      2 * Real.pi * B * S ≤ archForm (atomicTest N x g) / G := by
    apply (le_div_iff₀ hG).mpr
    have he : (archForm (atomicTest M x g) / G + archForm (atomicTest N y g) / G -
        2 * Real.pi * B * S) * G = archForm (atomicTest M x g) + archForm (atomicTest N y g) -
          2 * Real.pi * (G * B * S) := by field_simp [hG.ne']
    rw [he]
    have hpaid := mul_le_mul_of_nonneg_left hphysical (by positivity : 0 ≤ 2 * Real.pi)
    linarith only [hcross, hpaid]
  -- Pay the tail logarithm at near-unit defect cost before combining the source bounds.
  have htail : Real.log N * S₁ ≤ (1 + δ / 4) * poleDefect N x + T * S := by
    have ht := log_mul_tail_mass_le_defect hM hMN x (show 0 < 4 / δ by positivity)
    have he : 1 / (4 / δ) = δ / 4 := by field_simp [hδ.ne']
    rw [he] at ht
    have hcut : cutoffPrimeCost M N ≤ R + J := by
      unfold cutoffPrimeCost
      dsimp only [J]
      linarith only [hratio]
    have hcoeff : (1 + 4 / δ) * cutoffPrimeCost M N + Real.log N - Real.log M ≤ T := by
      have hc' := mul_le_mul_of_nonneg_left hcut (by positivity : 0 ≤ 1 + 4 / δ)
      dsimp only [T]
      linarith only [hc', hratio]
    have hm := mul_le_mul_of_nonneg_right hcoeff hS
    change Real.log N * S₁ ≤ _ at ht
    linarith only [ht, hm]
  have htpay := mul_le_mul_of_nonneg_left htail hδle
  have hgain : (δ / 4 + (1 - δ) * (1 + δ / 4)) * poleDefect N x ≤
      (1 - δ / 2) * poleDefect N x := by
    nlinarith only [mul_nonneg (sq_nonneg δ) hD]
  change Real.log N * S - (1 - δ / 2) * poleDefect N x - C * S ≤ _
  dsimp only [C]
  have hsplitLog := congrArg (fun z : ℝ => Real.log N * z) hsplit
  linarith only [hlo, hhi, hcombined, htpay, hgain, hsplitLog]


/-- The complete signed form keeps a prime-defect reserve. -/
theorem exists_noRealZero_complete_defect_reserve {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
        a * poleDefect N x - C * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
          weilQuad (atomicTest N x (atomDilate φ (c / N))) /
            ((c / N) * ∫ u, φ u ^ 2) := by
  obtain ⟨a, ha, C, hC, hgamma⟩ := exists_noRealZero_gamma_defect_payment hφ hsupp hFT hc
  let A := arithmeticRelativeCost c (a / 2)
  refine ⟨a / 2, by positivity, C + |A|, add_nonneg hC (abs_nonneg A), ?_⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt c
  filter_upwards [hgamma, eventually_overlapArithmeticEnergy_ge_defect hc
    (show 0 < a / 2 by positivity), eventually_ge_atTop N₀, eventually_ge_atTop 1]
    with N hgam har hNN₀ hN
  intro x
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / (N : ℝ) := div_pos hc hNR
  have hw1 : c / (N : ℝ) ≤ 1 := by
    apply (div_le_one hNR).mpr
    exact hN₀.le.trans (by exact_mod_cast hNN₀)
  let g := atomDilate φ (c / N)
  have hg : ContDiff ℝ 2 g := hφ.comp (contDiff_id.div_const _)
  have hφM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  have hgc : HasCompactSupport g := hasCompactSupport_atomDilate hw.ne' (hasCompactSupport_of_unitSupport hsupp)
  have hsupp := (atom_support_of_unitSupport hsupp) hw
  have hmass : (∫ u, g u ^ 2) = (c / N) * ∫ u, φ u ^ 2 := integral_atomDilate_sq hw
  have hG : 0 < ∫ u, g u ^ 2 := by rw [hmass]; exact mul_pos hw hφM
  have hs := har _ hw hw1 le_rfl g hg.continuous hgc hsupp hG x
  have he := weilQuad_atomicTest_div_eq_arithmetic_add_gamma hg hsupp N x
  rw [hmass] at he
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  have hcost := mul_le_mul_of_nonneg_right (le_abs_self A) hS
  have hgamx := hgam x
  change (1 - a / 2) * poleDefect N x - A * _ ≤ overlapArithmeticEnergy g N x at hs
  change _ = overlapArithmeticEnergy g N x + _ - _ at he
  linarith only [hs, he, hgamx, hcost]



/-- Without real Fourier zeros the spectral tail beyond every overlap is positive. -/
theorem integral_shellSpectrum_pos_of_noRealZero (c : ℝ) :
    0 < ∫ t in Set.Ioi c, shellSpectrum φ t := by
  have hφc := (hasCompactSupport_of_unitSupport hsupp)
  have hcont := continuous_shellSpectrum hφ.continuous hφc
  have hpos : ∀ t : ℝ, 0 < shellSpectrum φ t := fun t =>
    sq_pos_of_pos (norm_pos_iff.mpr (hFT (2 * Real.pi * t)))
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (c + 1) (c + 2)).Nonempty from ⟨c + 1, le_rfl, by linarith⟩) hcont.continuousOn
  have hsub : Set.Icc (c + 1) (c + 2) ⊆ Set.Ioi c := fun t ht => by
    simp only [Set.mem_Ioi]; linarith [ht.1]
  have hint := integrableOn_shellSpectrum_Ioi hφ hφc c
  calc (0 : ℝ) < shellSpectrum φ t₀ := hpos t₀
    _ = ∫ t in Set.Icc (c + 1) (c + 2), shellSpectrum φ t₀ := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc]
        norm_num
    _ ≤ ∫ t in Set.Icc (c + 1) (c + 2), shellSpectrum φ t :=
        setIntegral_mono_on (integrableOn_const (by simp))
          (hint.mono_set hsub) measurableSet_Icc fun t ht => hmin ht
    _ ≤ ∫ t in Set.Ioi c, shellSpectrum φ t :=
        setIntegral_mono_set hint (ae_of_all _ fun t => shellSpectrum_nonneg t)
          (Eventually.of_forall hsub)

/-- **Uniform conductor floor** at every positive overlap. -/
theorem exists_noRealZero_conductor_floor {c : ℝ} (hc : 0 < c) :
    ∃ e : ℝ, 0 < e ∧ ∀ m : ℕ, 0 < m → e ≤ completedConductorEnergy φ c m :=
  ⟨2 / (∫ u, φ u ^ 2) * ∫ t in Set.Ioi c, shellSpectrum φ t,
    mul_pos (div_pos zero_lt_two (integral_sq_pos_of_noRealZero hφ hsupp hFT))
      (integral_shellSpectrum_pos_of_noRealZero hφ hsupp hFT c),
    fun _ hm => completedConductorEnergy_ge_shellTail hφ
      hsupp (integral_sq_pos_of_noRealZero hφ hsupp hFT) hc hm⟩


/-- The complete Weil matrix retains a positive prime-defect fraction at every fixed overlap, in
matrix coordinates. -/
theorem exists_noRealZero_completeWeilEnergy_reserve {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, ∃ β : ℝ, 0 < β ∧ ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + β * poleDefect N (primeHorizonExtension x) ≤
        completeWeilEnergy φ c N x := by
  obtain ⟨β, hβ, C, -, hres⟩ := exists_noRealZero_complete_defect_reserve hφ hsupp hFT hc
  refine ⟨-C, β, hβ, ?_⟩
  filter_upwards [hres, eventually_ge_atTop 1] with N hN hN1
  intro x
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c / N := div_pos hc hNR
  have hmass : (∫ u, atomDilate φ (c / N) u ^ 2) =
      (c / N) * ∫ u, φ u ^ 2 := integral_atomDilate_sq hw
  have h := hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at h
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ
    hsupp hc hN1, hmass]
  linarith only [h]

/-- **Reduction to quasimodes.** At a fixed overlap the boosted-spline complete Weil matrix is
eventually positive definite as soon as the normalized Ramanujan vectors are norm quasimodes
with the completed conductor energies. -/
theorem eventually_noRealZero_completeWeilMatrix_posDef_of_quasimodes {c : ℝ} (hc : 0 < c)
    (hquasi : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m •
          normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix φ c N).PosDef := by
  obtain ⟨a, β, hβ, hres⟩ := exists_noRealZero_completeWeilEnergy_reserve hφ hsupp hFT hc
  obtain ⟨e, he, hfloor⟩ := exists_noRealZero_conductor_floor hφ hsupp hFT hc
  exact eventually_completeWeilMatrix_posDef_of_reserve_quasimodes hβ hres hquasi he hfloor



/-- **Positivity at every fixed overlap** for every profile without real Fourier zeros. -/
theorem eventually_noRealZero_completeWeilMatrix_posDef {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix φ c N).PosDef :=
  eventually_noRealZero_completeWeilMatrix_posDef_of_quasimodes hφ hsupp hFT hc fun _ hm =>
    tendsto_completeWeilMatrix_ramanujan_quasimode_norm hφ hsupp
      (integral_sq_pos_of_noRealZero hφ hsupp hFT) hc hm

/-- **Exact low spectral counts at every overlap.** -/
theorem noRealZero_spectral_count_eq {c : ℝ} (hc : 0 < c) (T : ℝ)
    (hT : ∀ m : ℕ, 0 < m → completedConductorEnergy φ c m ≠ T) :
    ∀ᶠ N : ℕ in atTop, (completeWeilSpectralSublevel φ c N T).card =
      (completedEnergySublevel φ hc T).card := by
  obtain ⟨a, β, hβ, hres⟩ := exists_noRealZero_completeWeilEnergy_reserve hφ hsupp hFT hc
  exact eventually_completeWeil_spectral_count_eq_of_reserve_quasimodes hc hβ hres
    (fun _ hm => tendsto_completeWeilMatrix_ramanujan_quasimode_norm hφ hsupp
      (integral_sq_pos_of_noRealZero hφ hsupp hFT) hc hm) T hT

/-- **The bottom of the spectrum** converges to the completed shell energy. -/
theorem noRealZero_spectrum_bottom {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∀ i, completedShellEnergy φ c - ε < completeWeilEigenvalue φ c N i) ∧
        ∃ i, |completeWeilEigenvalue φ c N i - completedShellEnergy φ c| < ε := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  obtain ⟨a, β, hβ, hres⟩ := exists_noRealZero_completeWeilEnergy_reserve hφ hsupp hFT hc
  have h := eventually_completeWeil_spectrum_bottom_of_reserve_quasimodes hφ hsupp hM hc hβ hres
    (fun _ hm => tendsto_completeWeilMatrix_ramanujan_quasimode_norm hφ hsupp hM hc hm) hε
  rwa [completedEnergyFloor_eq_completedShellEnergy hφ hsupp hM hc] at h

end NoRealZero

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
