import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.Stage1TrueVertexBudgetAndFarkasBarrier
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubFarkasSelectedInverseMoments
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.Stage1TrueVertexLowProbe
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.Stage1TrueVertexPrincipalComparison
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane

/-!
# Unconditional Zero-Free Half-Plane Below `139989 / 160000` (`1 - σ₀ = 20011 / 160000 > 2401 / 19200`)

At the Gram-admissible Stage-1 edge geometry `(lx, ly, ℓ) = (2111/6000, 19249/40000, 20033/120000)`
(`(X, Y, Z) = (Z^{2111/6000}, Z^{19249/40000}, Z)`, `M = 99967/120000 > 4/5`, `1 + 3ℓ ≤ 2M`,
Gram gap `2 lx - ly - ℓ = 111/2000 > 0`), reparametrizing the prime-slot base as
`Z' = Z^{20033/20000}` (`ell' j = (20033/20000) · D.ell j`, `∑ j, ell' j = 20033/120000`) couples
`D : HighData subDelta` with its Stage-1 dual partner `D_dual` via
`stage1_source_moments_combined` (which requires only `51 / 100 ≤ HeckeZeroSupremum.beta`):

* Small and large physical dyadic tails (`rowNorm < Z^{20033/2000000}` and
  `rowNorm ≥ Z^{97813/120000 + (20033/20000) D.t}`) and central cube contour truncation save fixed
  powers below `Z^{β - 495527/720000}` whenever `139989/160000 ≤ β`.
* On `supportedFloorRows` (`a = 51/100`), the `Z`-exponent saves `> 1/250` below
  `268847/1440000 = 139989/160000 - 495527/720000`.
* On `supportedNonfloorRows` (`51/100 < a ≤ 1`), dyadic shells `d' < 1/2` (`d_Z ≤ 20033/40000`)
  save `> 1/25` under Stage-0 `actual_nonfloor_class_from_raw_moments`, while shells
  `1/2 ≤ d' ≤ 5/6` save `1/100000 - O(D.t) > 1/200000` under Stage-1
  `actual_nonfloor_class_from_raw_moments_sub16799` via `rowExponent_balanced_stage1_vertex`.
* Combining with `stage1Vertex_actual_ray_principal_comparison`,
  `stage1Vertex_normalized_compensatedPhysicalProbe_low`, and regularized Mellin continuation over
  all primitive Hecke characters of `K = ℚ(ω)` establishes unconditionally:
  - `hecke_beta_le_stage1_vertex`: `HeckeZeroSupremum.beta ≤ 139989 / 160000 < 3281 / 3750 < 16799 / 19200`.
  - `hecke_ne_zero_of_stage1_vertex_lt_re`, `DirichletCharacter.LFunction_ne_zero_of_stage1_vertex_lt_re`,
    `riemannZeta_ne_zero_of_stage1_vertex_lt_re`: nonvanishing on `Re s > 139989 / 160000`.
  - `riemannZeta_ne_zero_of_re_lt_stage1_vertex_left` and `riemannZeta_zero_mem_stage1_vertex_strip`:
    `riemannZeta` has no zeros on `0 < Re s < 20011 / 160000` (`= 0.12506875 > 469 / 3750 >
    2401 / 19200 > 3001 / 24000`), confining every zero with `Re s > 0` to
    `[20011 / 160000, 139989 / 160000]`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics Complex
open scoped BigOperators Classical Topology ContDiff SchwartzMap ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

namespace Stage1TrueVertexHighTransport

open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands Parameters
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open HeckeDetectorAdaptiveCutoff HeckeDetectorRawFiber
open SubSevenEighthsHighTransport Stage1DualSixthFreeEnergy SubFarkasSelectedInverseMoments
open GaloisForLFunctions.FamilyContinuationTheory

local notation "O" => Eisenstein.O

/-! ### Stage-1 combined source moments assuming only `51 / 100 ≤ HeckeZeroSupremum.beta` -/

/-- Combined Stage-0 (`d' < 1 / 2` via `counts_0`) and Stage-1 (`1 / 2 ≤ d' ≤ 5 / 6` via `counts_1`
at `εm = 15 * D.t`) unconditional source-moment supply assuming only
`51 / 100 ≤ HeckeZeroSupremum.beta`. -/
theorem stage1_source_moments_combined
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (ht_eq : D_dual.t = D.t)
    (hfine : ∀ j, D.ell j ≤ detectorMesh subDelta D.t / 200)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (F : ProbeFinalAssembly.SourceData D)
    (hmod : F.modulus = F_dual.modulus)
    (hW_eq : F.W = F_dual.W)
    (counts_0 : CountParameters F.modulus ⊤ D.t)
    (counts_1 : CountParametersSub16799 F.modulus ⊤ (15 * D.t)) :
    ∃ τ : ℝ, 0 < τ ∧ τ < (1 / 200 : ℝ) / 2 ∧ 4 * τ < (1 / 200) * D.cost ∧ τ < D.t ∧
      2 * τ ≤ D.t ∧ τ * (2 + 4 * D.eps) < D.t ∧
      ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z' : ℝ in atTop,
        SourceMomentBound F counts_0 η Z' τ (C * Z' ^ D.t) (Z' ^ (2 * τ)) ∧
        ∀ rows : Finset FreeRow, ∀ d' a : ℝ,
          1 / 2 ≤ d' → d' ≤ 5 / 6 → 51 / 100 < a → a ≤ 1 →
          (∀ u ∈ rows, u.val ≠ 1 ∧ Z' ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
            (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
            rowNorm u ≤ Z' ^ (d' - D.t)) →
          ∀ i : ℕ, ∀ z : ℂ, z.re = 17 / 50 → |z.im| ≤ Z' ^ (2 * τ) →
            SourceMomentsAtSub16799 F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
              (fun _ y => (F.w y : ℂ)) Z' d' a D.ε τ (5 / 6) 2 D.t D.t i z subDelta
              (if 2 * a - 1 ≤ 5 / 6 then counts_1.cB else counts_1.cH)
              (if 2 * a - 1 ≤ 5 / 6 then counts_1.kB else counts_1.kH)
              (C * Z' ^ D.t) (Z' ^ (2 * τ)) (15 * D.t) := by
  have hβ_hi : HeckeZeroSupremum.beta ≤ 7 / 8 :=
    HeckeCommonProbe.beta_le_seven_eighths ProbeFinalAssemblyUnconditional.common_probe
  have ht_pos : 0 < D.t := D.t_pos
  let Label := Sum Bool (RayQuotient.Characters F.modulus ⊤)
  letI : Fintype Label := Fintype.ofFinite _
  have hcert : ∀ bΦ : ℝ, 0 < bΦ →
      CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α := Fin D.N) F.modulus ⊤ le_top
        (fun x => conj (F.W x)) 2 (1 / 4) (9 / 4) bΦ 0 1 (33 / 50) (33 / 50) 2
        (CenteredMomentDetectorPlainMomentParameters.kappaPlain D)
        (CenteredMomentDetectorPlainMomentParameters.stageError D)
        (CenteredMomentEnergyWidthSchedule.count 2
          (CenteredMomentDetectorPlainMomentParameters.stageError D)) := by
    intro bΦ hbΦ
    have hp := CenteredMomentDetectorPlainMomentParameters.fixed_parameters D
    have hsubD : subDelta = 1 / 100000000 := rfl
    exact CenteredMomentEnergyCertifiedExistence.terminal_certificate (α := Fin D.N)
      F.modulus ⊤ le_top (fun x => conj (F.W x)) 1 2 (1 / 4) (9 / 4) bΦ 0 1
      (33 / 50) (33 / 50) 2
      (CenteredMomentDetectorPlainMomentParameters.kappaPlain D)
      (CenteredMomentDetectorPlainMomentParameters.stageError D)
      (by norm_num) (CenteredMomentDetectorPlainSlotProfile.conjugate_source_support F)
      (Complex.conjCLE.contDiff.comp (F.W.smooth (⊤ : ℕ∞)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num)
      hp.2.2.2.2.1.le hp.2.2.1 hβ51
      (by unfold CenteredMomentDetectorPlainMomentParameters.kappaPlain; linarith)
  obtain ⟨hp, hz⟩ := plain_inputs F hcert
  let mesh := detectorMesh subDelta D.t
  have hmesh : 0 < mesh := detectorMesh_pos subDelta_pos D.t_pos
  obtain ⟨J_0, hJ_0, hmom_0⟩ := source_moments F counts_0 mesh hmesh hfine hp hz
  obtain ⟨Jr_B, hraw_B⟩ := ProbeDetectorInverseRawField.fixed_raw_profiles
    counts_1.cB counts_1.kB counts_1.cB_pos counts_1.kB_pos
  obtain ⟨Jr_H, hraw_H⟩ := ProbeDetectorInverseRawField.fixed_raw_profiles
    counts_1.cH counts_1.kH counts_1.cH_pos counts_1.kH_pos
  obtain ⟨Jim, him⟩ := ProbeDetectorInverseMarkedField.source_batch_inverse_marked F.modulus ⊤ le_top F
  obtain ⟨Jm, hm⟩ := ProbeDetectorPlainMarkedFineField.source_batch_plain_marked_fine F mesh hmesh hfine hp
  obtain ⟨Ju, hu⟩ := ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked D F hz
  obtain ⟨τ_dual, J_sel, hτ_dual_pos, _hτ_dual_le, hsel_all⟩ :=
    source_batch_selected_inverse_marked_sub16799 hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual
      emb hemb F_dual F hmod hW_eq
  let J_nat : ℕ := Jr_B + Jr_H + Jim + Jm + Ju + J_sel
  let J_big : ℝ := J_0 + (J_nat : ℝ) + 8 / τ_dual + 1
  have hJ_big : 0 ≤ J_big := by dsimp only [J_big]; positivity
  obtain ⟨τ, hτ, hτd, hτcost, hτt, hτJ, hτeps⟩ := D.height_choice J_big hJ_big
  have hτ2 : 2 * τ ≤ D.t := by nlinarith only [hτJ, hτ, hJ_big]
  have hτ1 : τ ≤ 1 := by linarith only [hτt, D.t_small]
  have h2τ_le_dual : 2 * τ ≤ τ_dual / 4 := by
    have h1 : 2 * τ * (8 / τ_dual) ≤ D.t := by
      have hle : 8 / τ_dual ≤ J_big := by
        dsimp only [J_big]; have := Nat.cast_nonneg (α := ℝ) J_nat; linarith only [hJ_0, this]
      have hm_le := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 * τ)
      linarith only [hm_le, hτJ, hτ]
    have h2 : 2 * τ * (8 / τ_dual) ≤ 1 := h1.trans (D.t_small.trans (by norm_num))
    have h3 := (div_le_iff₀ hτ_dual_pos).mp (by rwa [← mul_div_assoc] at h2 : (2 * τ * 8) / τ_dual ≤ 1)
    linarith only [h3, hτ_dual_pos]
  refine ⟨τ, hτ, hτd, hτcost, hτt, hτ2, hτeps, ?_⟩
  intro η
  obtain ⟨C₀, hC₀, hb₀_all⟩ := hmom_0 η
  let data_η := sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η
  choose CrB_l hCrB_l hb_rawB using fun l : Label => hraw_B (data_η l)
  choose CrH_l hCrH_l hb_rawH using fun l : Label => hraw_H (data_η l)
  let Cr : ℝ := 1 + (∑ l : Label, CrB_l l) + ∑ l : Label, CrH_l l
  have hCr_pos : 0 < Cr := by
    have h1 := Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => (hCrB_l l).le)
    have h2 := Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => (hCrH_l l).le)
    dsimp only [Cr]; linarith only [h1, h2]
  have hCrB_le (l : Label) : CrB_l l ≤ Cr := by
    have h1 := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hCrB_l j).le) (Finset.mem_univ l)
    have h2 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hCrH_l j).le)
    dsimp only [Cr]; linarith only [h1, h2]
  have hCrH_le (l : Label) : CrH_l l ≤ Cr := by
    have h1 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hCrB_l j).le)
    have h2 := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hCrH_l j).le) (Finset.mem_univ l)
    dsimp only [Cr]; linarith only [h1, h2]
  obtain ⟨Cim, hCim, him_η⟩ := him η
  obtain ⟨Cm, hCm, hm_η⟩ := hm η
  obtain ⟨Cu, hCu, hu_η⟩ := hu η
  obtain ⟨Csel, hCsel, hsel_η⟩ := hsel_all η
  let C_sum : ℝ := C₀ + Cr + Cim + Cm + Cu + Csel
  let C_tot : ℝ := C_sum * (2 : ℝ) ^ J_big
  have hCtot_pos : 0 < C_tot := by dsimp only [C_tot, C_sum]; positivity
  refine ⟨C_tot, hCtot_pos, ?_⟩
  filter_upwards [hb₀_all τ hτ hτ1, him_η, hm_η, hu_η, hsel_η,
    (tendsto_rpow_atTop (div_pos hτ_dual_pos (by norm_num : (0 : ℝ) < 4))).eventually
      (eventually_ge_atTop (2 : ℝ))] with Z' hb₀ him_z hm_z hu_z hsel_z h2_qtr
  have hZ1 : 1 < Z' := him_z.1
  have hZp : 0 < Z' := zero_lt_one.trans hZ1
  have h2τ_J0 : 2 * τ * (1 + J_0) ≤ D.t := by
    have hle : 1 + J_0 ≤ J_big := by
      dsimp only [J_big]; have := Nat.cast_nonneg (α := ℝ) J_nat
      have : 0 ≤ 8 / τ_dual := by positivity
      linarith only [this, ‹0 ≤ (J_nat : ℝ)›]
    nlinarith only [hle, hτJ, hτ]
  have hb₀_abs : SourceMomentBound F counts_0 η Z' τ (C_tot * Z' ^ D.t) (Z' ^ (2 * τ)) := by
    have h1 := polynomial_height_absorption C₀ Z' τ J_0 D.t hC₀.le hZ1.le hτ.le hJ_0
      (by linarith only [h2τ_J0])
    have h2 : C₀ * (2 : ℝ) ^ J_0 ≤ C_tot := by
      dsimp only [C_tot, C_sum]
      exact mul_le_mul (by linarith only [hCr_pos, hCim, hCm, hCu, hCsel])
        (Real.rpow_le_rpow_of_exponent_le one_le_two (by
          dsimp only [J_big]; have := Nat.cast_nonneg (α := ℝ) J_nat
          have : 0 ≤ 8 / τ_dual := by positivity
          linarith only [this, ‹0 ≤ (J_nat : ℝ)›]))
        (Real.rpow_nonneg zero_le_two _) (by positivity)
    exact hb₀.mono_constant hZp.le (h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hZp.le _)))
  refine ⟨hb₀_abs, ?_⟩
  intro rows d' a hd_lo hd_hi _ha _ha1 hrows i z hz_re hz_im
    q B hB_sub hdata hrev _hslots hwidths hprof hupper hext _hmesh _hbin _hfam
    bin label left right hne
  let height : ℝ := Z' ^ (2 * τ)
  have hh0 : 0 ≤ height := Real.rpow_nonneg hZp.le _
  have hh1 : 1 ≤ height := Real.one_le_rpow hZ1.le (by positivity)
  have hpow_nat (K : ℕ) (hK : K ≤ J_nat) :
      (1 + height) ^ K ≤ (2 : ℝ) ^ J_big * Z' ^ D.t := by
    have h2J : 2 * τ * (J_nat : ℝ) ≤ D.t := by
      have hle : (J_nat : ℝ) ≤ J_big := by
        dsimp only [J_big]; have : 0 ≤ 8 / τ_dual := by positivity
        linarith only [hJ_0, this]
      nlinarith only [hle, hτJ, hτ]
    calc (1 + height) ^ K
        ≤ (1 + height) ^ J_nat := pow_le_pow_right₀ (by linarith only [hh0]) hK
      _ ≤ (2 * height) ^ J_nat := pow_le_pow_left₀ (by positivity) (by linarith only [hh1]) J_nat
      _ = (2 : ℝ) ^ (J_nat : ℝ) * Z' ^ (2 * τ * (J_nat : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_natCast (Z' ^ (2 * τ)),
            ← Real.rpow_mul hZp.le]
      _ ≤ (2 : ℝ) ^ J_big * Z' ^ D.t :=
          mul_le_mul
            (Real.rpow_le_rpow_of_exponent_le one_le_two (by
              dsimp only [J_big]; have : 0 ≤ 8 / τ_dual := by positivity
              linarith only [hJ_0, this]))
            (Real.rpow_le_rpow_of_exponent_le hZ1.le h2J)
            (Real.rpow_nonneg hZp.le _) (Real.rpow_nonneg zero_le_two _)
  have hcoef_le {c : ℝ} {K : ℕ} (hc0 : 0 ≤ c) (hc : c ≤ C_sum) (hK : K ≤ J_nat) :
      c * (1 + height) ^ K ≤ C_tot * Z' ^ D.t := by
    calc c * (1 + height) ^ K
        ≤ C_sum * ((2 : ℝ) ^ J_big * Z' ^ D.t) :=
          mul_le_mul hc (hpow_nat K hK) (pow_nonneg (by positivity) _)
            (by dsimp only [C_sum]; positivity)
      _ = C_tot * Z' ^ D.t := by dsimp only [C_tot]; ring
  have hd_200 : (1 / 200 : ℝ) ≤ d' := by linarith only [hd_lo]
  have hU1 : 1 < Z' ^ d' := Real.one_lt_rpow hZ1 (by linarith only [hd_lo])
  have hUp : 0 < Z' ^ d' := zero_lt_one.trans hU1
  let F_fib := B.fiber bin label left right hne
  have hfd : F_fib.rowData = data_η label := by change B.data label = data_η label; rw [hdata]
  have hrows_lo : ∀ u ∈ rows, Z' ^ (1 / 100 : ℝ) ≤ rowNorm u := fun u hu => (hrows u hu).2.1
  have him_val := him_z.2 d' hd_200 a D.ε (cutoffSub16799 (2 * a - 1) q) (Z' ^ τ)
    ((Z' ^ d') ^ (τ / (2 * (5 / 6)))) i B hdata hprof hupper hwidths
    (fun s => by rw [hext]; exact hz_re) bin label left right hne height hh0
  have hmarked := hm_z.2 rows hrows_lo d' hd_200 a (cutoffSub16799 (2 * a - 1) q) (Z' ^ τ)
    ((Z' ^ d') ^ (τ / (2 * (5 / 6)))) i B hB_sub hdata hprof hwidths
    (fun s => by rw [hupper]) (fun s => by rw [hext]; exact hz_re)
    bin label left right hne height hh0 (fun s => by rw [hext]; exact hz_im)
  have hunmarked := hu_z.2 rows hrows_lo d' hd_200 a (cutoffSub16799 (2 * a - 1) q) (Z' ^ τ)
    ((Z' ^ d') ^ (τ / (2 * (5 / 6)))) i B hB_sub hdata hprof hwidths
    bin label left right hne height hh0
  have hbase_Dt : Moments F_fib subDelta
      (if 2 * a - 1 ≤ 5 / 6 then counts_1.cB else counts_1.cH)
      (if 2 * a - 1 ≤ 5 / 6 then counts_1.kB else counts_1.kH)
      (C_tot * Z' ^ D.t) height D.t := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn σ hσ t ht
      rw [hfd]
      split_ifs with hδ56
      · have hpB := hb_rawB label F_fib.reverse n hn (Z' ^ d') hUp
          (cutoffSub16799 (2 * a - 1) q) F_fib.r σ hσ height t hh0 ht
        have hcB : CrB_l label * (1 + height) ^ Jr_B ≤ C_tot * Z' ^ D.t :=
          hcoef_le (hCrB_l label).le
            (by dsimp only [C_sum]; linarith only [hCrB_le label, hC₀, hCim, hCm, hCu, hCsel])
            (by dsimp only [J_nat]; omega)
        exact ⟨ProbeFinalAssembly.rawMoment_mono_constant hpB.1 hcB,
          ProbeFinalAssembly.rawMoment_mono_constant hpB.2 hcB⟩
      · have hpH := hb_rawH label F_fib.reverse n hn (Z' ^ d') hUp
          (cutoffSub16799 (2 * a - 1) q) F_fib.r σ hσ height t hh0 ht
        have hcH : CrH_l label * (1 + height) ^ Jr_H ≤ C_tot * Z' ^ D.t :=
          hcoef_le (hCrH_l label).le
            (by dsimp only [C_sum]; linarith only [hCrH_le label, hC₀, hCim, hCm, hCu, hCsel])
            (by dsimp only [J_nat]; omega)
        exact ⟨ProbeFinalAssembly.rawMoment_mono_constant hpH.1 hcH,
          ProbeFinalAssembly.rawMoment_mono_constant hpH.2 hcH⟩
    · intro sel hsel hc1 hc2 n hn σ hσ t ht
      exact (him_val sel hsel hc1 hc2 n hn σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right
          (hcoef_le hCim.le (by dsimp only [C_sum]; linarith only [hC₀, hCr_pos, hCm, hCu, hCsel])
            (by dsimp only [J_nat]; omega))
          (Real.rpow_nonneg hUp.le _))
    · intro sel hsel hc j k hjk σ hσ t ht
      exact (hmarked sel hsel hc j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right
          (hcoef_le hCm.le (by dsimp only [C_sum]; linarith only [hC₀, hCr_pos, hCim, hCu, hCsel])
            (by dsimp only [J_nat]; omega))
          (Real.rpow_nonneg hUp.le _))
    · intro j k hjk σ hσ t ht
      exact (hunmarked j k hjk σ hσ t ht).1.trans
        (mul_le_mul_of_nonneg_right
          (hcoef_le hCu.le (by dsimp only [C_sum]; linarith only [hC₀, hCr_pos, hCim, hCm, hCsel])
            (by dsimp only [J_nat]; omega))
          (Real.rpow_nonneg hUp.le _))
  have hz_im_dual : |z.im| ≤ (1 / 2 : ℝ) * ((Z' ^ d') ^ (3 / (2 * d'))) ^ τ_dual := by
    have h1 : Z' ^ (2 * τ) ≤ Z' ^ (τ_dual / 4) :=
      Real.rpow_le_rpow_of_exponent_le hZ1.le h2τ_le_dual
    have h2 : 2 * Z' ^ (τ_dual / 4) ≤ Z' ^ τ_dual := by
      have hprod : 2 * Z' ^ (τ_dual / 4) ≤ Z' ^ (τ_dual / 4) * Z' ^ (τ_dual / 4) :=
        mul_le_mul_of_nonneg_right h2_qtr (Real.rpow_nonneg hZp.le _)
      rw [← Real.rpow_add hZp, show τ_dual / 4 + τ_dual / 4 = τ_dual / 2 by ring] at hprod
      exact hprod.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith only [hτ_dual_pos]))
    have h3 : Z' ^ τ_dual ≤ ((Z' ^ d') ^ (3 / (2 * d'))) ^ τ_dual := by
      have hZ_le : Z' ≤ (Z' ^ d') ^ (3 / (2 * d')) := by
        rw [← Real.rpow_mul hZp.le, show d' * (3 / (2 * d')) = (3 / 2 : ℝ) by
          field_simp [(by linarith only [hd_lo] : d' ≠ 0)]]
        exact (Real.rpow_one Z').symm.le.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num))
      exact Real.rpow_le_rpow hZp.le hZ_le hτ_dual_pos.le
    linarith only [hz_im, h1, h2, h3]
  refine ⟨moments_mono_eps hU1.le (by positivity) (by linarith only [ht_pos]) hbase_Dt, ?_⟩
  intro hr0 hr1 selected hselected hcap n hn s hs t ht
  have hs_val := hsel_z.2 d' hd_lo hd_hi a D.ε (cutoffSub16799 (2 * a - 1) q) (Z' ^ τ)
    ((Z' ^ d') ^ (τ / (2 * (5 / 6)))) i B hdata hprof hupper hwidths z hz_re hz_im_dual hext
    bin label left right hne height hh0 hr0 hr1 selected hselected hcap n hn s hs t ht
  exact hs_val.trans (mul_le_mul_of_nonneg_right
    (hcoef_le hCsel.le (by dsimp only [C_sum]; linarith only [hC₀, hCr_pos, hCim, hCm, hCu])
      (by dsimp only [J_nat]; omega))
    (Real.rpow_nonneg hUp.le _))

/-! ### Fine-mesh parameter data and `Z' = Z^{20033/20000}` scaling -/

theorem exists_stage1Vertex_high_data_fine :
    ∃ D : HighData subDelta,
      D.t ≤ min (subDelta / 8) (1 / 100000000) ∧
      (∀ j, D.ell j ≤ detectorMesh subDelta D.t / 200) ∧
      2000 * D.ε ≤ D.t ∧
      2000 * D.e ≤ D.t ∧
      ((D.N : ℝ) + 8) * D.eps ≤ D.t ∧
      D.e ≤ ((7 / 8 : ℝ) * D.rmin) / 4 := by
  let t : ℝ := subDelta / 8
  have ht : 0 < t := by dsimp [t, subDelta]; norm_num
  have ht_le : t ≤ min (subDelta / 8) (1 / 100000000) := by dsimp [t, subDelta]; norm_num
  have htΔ : t < subDelta / 4 := by dsimp [t, subDelta]; norm_num
  have ht1 : t ≤ 1 / 100000000 := by dsimp [t, subDelta]; norm_num
  obtain ⟨N, hN, ell, rmin, hr, hell, hsum, hbounds, _⟩ :=
    exists_physical_slot_lengths (1 / 200) (7 / 8)
      (min t (detectorMesh subDelta t)) t (by norm_num) (by norm_num)
      (lt_min ht (detectorMesh_pos subDelta_pos ht)) ht
  let small := t / ((N : ℝ) + 2000)
  have hden : 0 < (N : ℝ) + 2000 := by positivity
  have hsmall : 0 < small := div_pos ht hden
  have hst0 : small ≤ t / 2000 :=
    div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  let ellMin := (7 / 8 : ℝ) * rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε, e, κ, cost, _, hε, hε1, hεgap, hεa, he, he1, heell, hea, hκ, hκ1, hcost,
    hdet, hphase, _, _, _, _, _⟩ :=
    exists_detector_scales t rmin t (1 / 200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small / 2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepss : eps ≤ small := by dsimp [eps]; linarith only [hsmall]
  have heps1 : eps ≤ 1 := by linarith only [hepss, hst0, ht1]
  have heN : ((N : ℝ) + 2000) * eps ≤ t := by
    have h := (le_div_iff₀ hden).mp hepss
    simpa only [mul_comm] using h
  have he8 : ((N : ℝ) + 8) * eps ≤ t := by nlinarith only [heN, heps.le]
  have hεt : 2000 * ε ≤ t := by linarith only [hεa, hst0]
  have het : 2000 * e ≤ t := by linarith only [hea, hst0]
  let sigma := min (t / 2) (ellMin / 4)
  have hs : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma ≤ t / 2 := min_le_left _ _
  have hsell : sigma ≤ ellMin / 4 := min_le_right _ _
  refine ⟨{
    t := t, N := N, ell := ell, rmin := rmin, ε := ε, e := e, κ := κ,
    cost := cost, eps := eps, sigma := sigma
    t_pos := ht, t_delta := htΔ, t_small := ht1, slots_pos := hN
    slots_injective := hell, slots_sum := hsum
    slots_bounds := fun j => ⟨(hbounds j).1, (hbounds j).2.1, (hbounds j).2.2.2⟩
    rmin_pos := hr, epsilon_pos := hε, epsilon_small := hε1, epsilon_gap := hεgap
    e_pos := he, e_small := he1, kappa_pos := hκ, kappa_small := hκ1, cost_pos := hcost
    eps_pos := heps, eps_small := heps1, sigma_pos := hs
    detector_budget := by linarith only [hdet]
    phase_budget := hphase
    count_budget := by dsimp [t, subDelta] at hεt ht1 ⊢; linarith only [hεt, ht1]
    central_budget := by dsimp [t, subDelta] at hεt het he8 ht1 ⊢; nlinarith only [hεt, het, he8, ht1]
    geometric_budget := by linarith only [hst2, het, ht1]
    principal_budget := by linarith only [hst2, ht1]
    window_budget := by change sigma + e ≤ (7 / 8) * ellMin; linarith only [hsell, heell, hmin]
    floor_budget := by linarith only [hst2, het, he8, ht1]
    high_saving := by linarith only [hst2, ht]
    height_choice := ?_ }, ht_le, ?_, hεt, het, he8, heell⟩
  · intro J hJ
    let τ := min ((1 / 200 : ℝ) * cost / 16) (min (1 / 800) (t / (4 * (J + 7))))
    have htau : 0 < τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ ≤ (1 / 200 : ℝ) * cost / 16 := min_le_left _ _
    have hτd : τ ≤ 1 / 800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ ≤ t / (4 * (J + 7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ * (4 * (J + 7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0 ≤ τ * J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    exact ⟨τ, htau, by linarith only [hτd], by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau], by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · intro j
    calc ell j
        ≤ (1 / 200 : ℝ) * min t (detectorMesh subDelta t) := (hbounds j).2.2.1
      _ ≤ (1 / 200 : ℝ) * detectorMesh subDelta t :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ = detectorMesh subDelta t / 200 := by ring

lemma stage1Vertex_scale_tendsto : Tendsto (fun Z : ℝ => Z ^ (20033 / 20000 : ℝ)) atTop atTop :=
  tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 20033 / 20000)

lemma stage1Vertex_scale_slot_eq {K : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (ell : Fin K → ℝ) :
    (fun j => (Z ^ (20033 / 20000 : ℝ)) ^ (ell j)) =
      (fun j => Z ^ ((20033 / 20000 : ℝ) * ell j)) := by
  funext j
  rw [← Real.rpow_mul hZ]

lemma stage1Vertex_scale_low_cutoff {Z : ℝ} (hZ : 0 ≤ Z) :
    (Z ^ (20033 / 20000 : ℝ)) ^ (1 / 100 : ℝ) = Z ^ (20033 / 2000000 : ℝ) := by
  rw [← Real.rpow_mul hZ]
  norm_num

lemma stage1Vertex_scale_high_cutoff {Z t : ℝ} (hZ : 0 ≤ Z) :
    (Z ^ (20033 / 20000 : ℝ)) ^ ((97813 / 120198 : ℝ) + t) =
      Z ^ ((97813 / 120000 : ℝ) + (20033 / 20000 : ℝ) * t) := by
  rw [← Real.rpow_mul hZ]
  exact congrArg (fun x : ℝ => Z ^ x) (by ring)

/-! ### Piece 1: Small physical dyadic tail (`rowNorm < Z^{20033/2000000}`) -/

lemma stage1Vertex_small_source_scale {K : ℕ} {Z : ℝ} (hZ : 0 < Z) (length : Fin K → ℝ)
    (hl : ∑ i, length i = 20033 / 120000) (σ : ℝ) :
    (∏ i, (Z ^ (length i)) ^ (17 / 50 : ℝ)) *
      ((Z ^ (2111 / 6000 : ℝ)) ^ (1 / 2 - (17 / 50 : ℝ)) * Z ^ (σ + (17 / 50 : ℝ) - 1) *
        (Z ^ (19249 / 40000 : ℝ)) ^ ((1 / 2 : ℝ) - 1)) =
      Z ^ (σ - 787559 / 1000000) := by
  have hp : (∏ i, (Z ^ (length i)) ^ (17 / 50 : ℝ)) =
      Z ^ ((20033 / 120000 : ℝ) * (17 / 50)) := by
    calc _ = ∏ i, Z ^ (length i * (17 / 50 : ℝ)) :=
          Finset.prod_congr rfl fun i _ => (Real.rpow_mul hZ.le _ _).symm
      _ = Z ^ (∑ i, length i * (17 / 50 : ℝ)) := (Real.rpow_sum_of_pos hZ _ _).symm
      _ = _ := by rw [← Finset.sum_mul, hl]
  rw [hp, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  exact congrArg (fun x : ℝ => Z ^ x) (by ring)

theorem stage1Vertex_small_physical_tail (K : ℕ) (e a b B : ℝ)
    (he : 0 < e) (he' : e < 1 / 1000) (ha : 0 < a) (hb : 0 < b) (hB : 0 ≤ B)
    (hβ : (139989 / 160000 : ℝ) ≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (hfirst : FirstTail (1 / 4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : Character) (Z : ℝ), 1 ≤ Z →
      ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal) (_hT : ∀ i P, P ∈ T i → P.val ∉ S),
      (∀ P : (∀ i, T i), Function.Injective (fun i => (P i).val)) →
      ∀ length : Fin K → ℝ, (∀ i, 0 ≤ length i) → (∑ i, length i) = 20033 / 120000 →
      ∀ W : Fin K → ℝ → ℂ, (∀ i, Function.support (W i) ⊆ Icc a b) → (∀ i y, ‖W i y‖ ≤ B) →
      ‖finitePhysicalRows S hmax η (rowBand 1 (Z ^ (20033 / 2000000 : ℝ))) T W
        (fun i => Z ^ (length i)) W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z‖ ≤
        C * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ) *
          Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 - 7 / 100 + 8 * e) := by
  let σ : ℝ := max (7 / 8 : ℝ) HeckeZeroSupremum.beta + 8 * e
  have hσ78 : (7 / 8 : ℝ) ≤ σ := by dsimp [σ]; linarith [le_max_left (7 / 8 : ℝ) HeckeZeroSupremum.beta]
  have hσβ : HeckeZeroSupremum.beta + 8 * e ≤ σ := by
    dsimp [σ]; linarith [le_max_right (7 / 8 : ℝ) HeckeZeroSupremum.beta]
  have hσ3 : σ ≤ 3 := by
    have hmax1 : max (7 / 8 : ℝ) HeckeZeroSupremum.beta ≤ 1 :=
      max_le (by norm_num) HeckeZeroSupremum.beta_le_one
    dsimp [σ]; linarith
  have hσ_upper : σ ≤ HeckeZeroSupremum.beta + 11 / 160000 + 8 * e := by
    have hmax_le : max (7 / 8 : ℝ) HeckeZeroSupremum.beta ≤ HeckeZeroSupremum.beta + 11 / 160000 :=
      max_le (by linarith) (by linarith)
    dsimp [σ]; linarith
  obtain ⟨Ci, hCi, hmain⟩ := calibrated_physical_dyad_integral K e (1 / 4) a b (17 / 50) B
    σ (1 / 2) he he' (by norm_num) (by norm_num) ha hb le_rfl hB hσ78 hσβ le_rfl
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Ds, hDs, hsmall⟩ := small_dyadic_square_sum
  let N0 : ℝ := ‖((1 / (2 * Real.pi) : ℝ) : ℂ) ^ 3‖
  have hN0 : 0 ≤ N0 := norm_nonneg _
  refine ⟨(1 + N0) * (Ci * Ds), by positivity, ?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1 ≤ Z ^ (length i) := Real.one_le_rpow hZ (hl0 i)
  let L := Z ^ (20033 / 2000000 : ℝ)
  let F := smallDyadicIndices L
  let A : ℝ := Ci * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ) * Z ^ (σ - 787559 / 1000000)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hdyad (n : ℕ) (_hn : n ∈ F) :
      ‖finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i => Z ^ (length i)) W0 W1
        (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z‖ ≤ N0 * (A * ((2 : ℝ) ^ n) ^ (2 : ℝ)) := by
    have hR : ∀ u ∈ smallDyadicRows L n, u.val ≠ 1 ∧
        (2 : ℝ) ^ n ≤ ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ∧
        ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤ 2 * (2 : ℝ) ^ n := by
      intro u hu
      have hh := mem_dyadicRows.mp (mem_smallDyadicRows.mp hu).1
      exact ⟨hh.1, by simpa only [one_mul, rowNorm] using hh.2.1,
        by simpa only [one_mul, rowNorm] using hh.2.2.le⟩
    have hnorm := norm_finitePhysicalRows_le_absolute e σ (1 / 2) (17 / 50) he he'
      hσ78 hσβ hσ3 le_rfl (by norm_num) le_rfl S hS hmax hfirst η (smallDyadicRows L n)
      (fun u hu => (hR u hu).1) T hT hdis W (fun i => Z ^ (length i)) W0 W1
      a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    have hUn : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hh := (hmain η ((2 : ℝ) ^ n) hUn (smallDyadicRows L n) hR T hT hdis
      (fun i => Z ^ (length i)) hYp W hWS hWB (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
    have hpow : ((2 : ℝ) ^ n) ^ (8 / 5 + (1 / 4 : ℝ) - (17 / 50 : ℝ)) ≤ ((2 : ℝ) ^ n) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hUn (by norm_num)
    have hsc := stage1Vertex_small_source_scale hZ0 length hl σ
    have habs : absolutePhysicalDyadIntegral S hS hmax η (smallDyadicRows L n) T hT W
        (fun i => Z ^ (length i)) W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z
        σ (1 / 2) (17 / 50) ≤ A * ((2 : ℝ) ^ n) ^ (2 : ℝ) := by
      calc _ ≤ Ci * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ) *
              ((2 : ℝ) ^ n) ^ (8 / 5 + (1 / 4 : ℝ) - (17 / 50 : ℝ)) *
              Z ^ (σ - 787559 / 1000000) := by
            apply hh.trans_eq; rw [mul_assoc (Ci * _ * _), hsc]
        _ ≤ Ci * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ) * ((2 : ℝ) ^ n) ^ (2 : ℝ) *
              Z ^ (σ - 787559 / 1000000) := by gcongr
        _ = A * ((2 : ℝ) ^ n) ^ (2 : ℝ) := by dsimp [A]; ring
    exact hnorm.trans (mul_le_mul_of_nonneg_left habs hN0)
  have heq := sum_small_dyadicRows L (physicalRowValue S hmax η T W (fun i => Z ^ (length i))
    W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z)
  change finitePhysicalRows S hmax η (rowBand 1 L) T W (fun i => Z ^ (length i)) W0 W1
      (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z =
    ∑ n ∈ F, finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i => Z ^ (length i))
      W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z at heq
  rw [heq]
  have hexp : Z ^ (σ - 787559 / 1000000) * (L ^ (2 : ℝ)) ≤
      Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 - 7 / 100 + 8 * e) := by
    dsimp [L]
    rw [← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc _ ≤ ∑ n ∈ F, ‖finitePhysicalRows S hmax η (smallDyadicRows L n) T W
          (fun i => Z ^ (length i)) W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ F, N0 * (A * ((2 : ℝ) ^ n) ^ (2 : ℝ)) := Finset.sum_le_sum hdyad
    _ = N0 * (A * ∑ n ∈ F, ((2 : ℝ) ^ n) ^ (2 : ℝ)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ N0 * (A * (Ds * L ^ (2 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (hsmall L (Real.rpow_pos_of_pos hZ0 _) F (fun n hn => mem_smallDyadicIndices.mp hn)) hA)
          hN0
    _ ≤ (1 + N0) * (A * (Ds * L ^ (2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (1 + N0) * (Ci * Ds) * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ) *
          (Z ^ (σ - 787559 / 1000000) * L ^ (2 : ℝ)) := by dsimp [A]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

/-! ### Piece 2: Large physical dyadic tail (`rowNorm ≥ Z^{97813/120000 + ζ_Z}`) -/

lemma stage1Vertex_large_source_scale {K : ℕ} {Z : ℝ} (hZ : 0 < Z) (length : Fin K → ℝ)
    (hl : ∑ i, length i = 20033 / 120000) (r : ℝ) :
    (∏ i, (Z ^ (length i)) ^ r) *
      ((Z ^ (2111 / 6000 : ℝ)) ^ (1 / 2 - r) * Z ^ (2 + r - 1) *
        (Z ^ (19249 / 40000 : ℝ)) ^ ((2 : ℝ) - 1)) =
      Z ^ ((198857 / 120000 : ℝ) + (97813 / 120000 : ℝ) * r) := by
  have hp : (∏ i, (Z ^ (length i)) ^ r) = Z ^ ((20033 / 120000 : ℝ) * r) := by
    calc _ = ∏ i, Z ^ (length i * r) :=
          Finset.prod_congr rfl fun i _ => (Real.rpow_mul hZ.le _ _).symm
      _ = Z ^ (∑ i, length i * r) := (Real.rpow_sum_of_pos hZ _ _).symm
      _ = _ := by rw [← Finset.sum_mul, hl]
  rw [hp, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  exact congrArg (fun x : ℝ => Z ^ x) (by ring)

lemma stage1Vertex_large_geometric_scale (Z ζ r : ℝ) (hZ : 0 < Z) (n : ℕ) :
    Z ^ ((198857 / 120000 : ℝ) + (97813 / 120000 : ℝ) * r) *
      (Z ^ ((97813 / 120000 : ℝ) + ζ) * (2 : ℝ) ^ n) ^ (8 / 5 + (1 / 4 : ℝ) - r) =
      Z ^ ((198857 / 120000 : ℝ) + ((97813 / 120000 : ℝ) + ζ) * (37 / 20 : ℝ) - ζ * r) *
        ((2 : ℝ) ^ ((37 / 20 : ℝ) - r)) ^ n := by
  rw [show (8 / 5 + (1 / 4 : ℝ) - r) = (37 / 20 : ℝ) - r by norm_num]
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity), ← Real.rpow_mul hZ.le]
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (n : ℝ),
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← mul_assoc, ← Real.rpow_add hZ]
  exact congrArg (fun x : ℝ => Z ^ x * ((2 : ℝ) ^ ((37 / 20 : ℝ) - r)) ^ n) (by ring)

theorem stage1Vertex_large_physical_tail (K : ℕ) (a b B ζ : ℝ) (hζ : 0 < ζ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0 ≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (hfirst : FirstTail (1 / 4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : Character) (Z : ℝ), 1 ≤ Z →
      ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal) (_hT : ∀ i P, P ∈ T i → P.val ∉ S),
      (∀ P : (∀ i, T i), Function.Injective (fun i => (P i).val)) →
      ∀ length : Fin K → ℝ, (∀ i, 0 ≤ length i) → (∑ i, length i) = 20033 / 120000 →
      ∀ W : Fin K → ℝ → ℂ, (∀ i, Function.support (W i) ⊆ Icc a b) → (∀ i y, ‖W i y‖ ≤ B) →
      Summable (fun n => finitePhysicalRows S hmax η
        (dyadicRows (Z ^ ((97813 / 120000 : ℝ) + ζ)) n) T W (fun i => Z ^ (length i))
        W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z) ∧
      (∑' n, ‖finitePhysicalRows S hmax η
        (dyadicRows (Z ^ ((97813 / 120000 : ℝ) + ζ)) n) T W (fun i => Z ^ (length i))
        W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z‖) ≤
        C * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ) * Z ^ (-1 : ℝ) := by
  obtain ⟨r, hr0⟩ := exists_gt (max (37 / 20 : ℝ)
    (((198857 / 120000 : ℝ) + ((97813 / 120000 : ℝ) + ζ) * (37 / 20 : ℝ) + 1) / ζ))
  have hr37 : (37 / 20 : ℝ) < r := (le_max_left _ _).trans_lt hr0
  have hr17 : (17 / 50 : ℝ) ≤ r := by linarith
  have hr_save : (198857 / 120000 : ℝ) + ((97813 / 120000 : ℝ) + ζ) * (37 / 20 : ℝ) - ζ * r ≤ -1 := by
    have hdiv := (div_lt_iff₀ hζ).mp ((le_max_right _ _).trans_lt hr0)
    nlinarith
  obtain ⟨Ci, hCi, hmain⟩ := calibrated_physical_dyad_integral K (1 / 2000) (1 / 4) a b r B
    2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha hb hr17 hB
    (by norm_num) (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num)
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hq : (2 : ℝ) ^ ((37 / 20 : ℝ) - r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let N0 : ℝ := ‖((1 / (2 * Real.pi) : ℝ) : ℂ) ^ 3‖
  have hN0 : 0 ≤ N0 := norm_nonneg _
  refine ⟨(1 + N0) * (Ci * (1 - (2 : ℝ) ^ ((37 / 20 : ℝ) - r))⁻¹),
    mul_pos (by positivity) (mul_pos hCi (inv_pos.mpr (sub_pos.mpr hq))), ?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1 ≤ Z ^ (length i) := Real.one_le_rpow hZ (hl0 i)
  let U0 := Z ^ ((97813 / 120000 : ℝ) + ζ)
  let f : ℕ → ℂ := fun n => finitePhysicalRows S hmax η (dyadicRows U0 n) T W
    (fun i => Z ^ (length i)) W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z
  let g : ℕ → ℝ := fun n =>
    Z ^ ((198857 / 120000 : ℝ) + ((97813 / 120000 : ℝ) + ζ) * (37 / 20 : ℝ) - ζ * r) *
      ((2 : ℝ) ^ ((37 / 20 : ℝ) - r)) ^ n
  let A : ℝ := (1 + N0) * Ci * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ)
  have hg_sum : Summable g :=
    (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) hq).mul_left _
  have hfn (n : ℕ) : ‖f n‖ ≤ A * g n := by
    have hR : ∀ u ∈ dyadicRows U0 n, u.val ≠ 1 ∧
        U0 * (2 : ℝ) ^ n ≤ ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ∧
        ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤ 2 * (U0 * (2 : ℝ) ^ n) := by
      intro u hu; have hh := mem_dyadicRows.mp hu; exact ⟨hh.1, hh.2.1, hh.2.2.le⟩
    have hnorm := norm_finitePhysicalRows_le_absolute (1 / 2000) 2 2 r
      (by norm_num) (by norm_num) (by norm_num) (by linarith [HeckeZeroSupremum.beta_le_one])
      (by norm_num) (by norm_num) (by norm_num) hr17 S hS hmax hfirst η (dyadicRows U0 n)
      (fun u hu => (hR u hu).1) T hT hdis W (fun i => Z ^ (length i)) W0 W1
      a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    have hUn : 1 ≤ U0 * (2 : ℝ) ^ n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hZ (by linarith)) (one_le_pow₀ (by norm_num))
    have hh := (hmain η (U0 * (2 : ℝ) ^ n) hUn (dyadicRows U0 n) hR T hT hdis
      (fun i => Z ^ (length i)) hYp W hWS hWB (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
    have hsc := stage1Vertex_large_source_scale hZ0 length hl r
    have hgeo := stage1Vertex_large_geometric_scale Z ζ r hZ0 n
    have habs : absolutePhysicalDyadIntegral S hS hmax η (dyadicRows U0 n) T hT W
        (fun i => Z ^ (length i)) W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z 2 2 r ≤
        Ci * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ) * g n := by
      apply hh.trans_eq
      rw [mul_assoc (Ci * _ * _), hsc]
      calc _ = Ci * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ) *
              (Z ^ ((198857 / 120000 : ℝ) + (97813 / 120000 : ℝ) * r) *
                (U0 * (2 : ℝ) ^ n) ^ (8 / 5 + (1 / 4 : ℝ) - r)) := by ring
        _ = _ := by dsimp [U0, g]; rw [hgeo]
    calc ‖f n‖ ≤ N0 * (Ci * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ) * g n) :=
          hnorm.trans (mul_le_mul_of_nonneg_left habs hN0)
      _ ≤ (1 + N0) * (Ci * (η.modulus.absNorm : ℝ) ^ (1 / 4 : ℝ) * g n) :=
          mul_le_mul_of_nonneg_right (by linarith) (by dsimp [g]; positivity)
      _ = A * g n := by dsimp [A]; ring
  have hf_norm : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hfn (hg_sum.mul_left A)
  refine ⟨hf_norm.of_norm, ?_⟩
  have hexp : Z ^ ((198857 / 120000 : ℝ) + ((97813 / 120000 : ℝ) + ζ) * (37 / 20 : ℝ) - ζ * r) ≤
      Z ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hZ hr_save
  calc (∑' n, ‖f n‖) ≤ ∑' n, A * g n := hf_norm.tsum_le_tsum hfn (hg_sum.mul_left A)
    _ = A * ∑' n, g n := tsum_mul_left
    _ = A * (Z ^ ((198857 / 120000 : ℝ) + ((97813 / 120000 : ℝ) + ζ) * (37 / 20 : ℝ) - ζ * r) *
        (1 - (2 : ℝ) ^ ((37 / 20 : ℝ) - r))⁻¹) := by
      dsimp [g]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) hq]
    _ ≤ A * (Z ^ (-1 : ℝ) * (1 - (2 : ℝ) ^ ((37 / 20 : ℝ) - r))⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [A]; positivity)
      exact mul_le_mul_of_nonneg_right hexp (inv_nonneg.mpr (sub_nonneg.mpr hq.le))
    _ = _ := by dsimp [A]; ring

/-! ### Piece 3: Central cube contour truncation on `rowBand L U_cut` -/

lemma stage1Vertex_central_prime_tuple_count {K : ℕ} (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal)
    (Z b : ℝ) (hZ : 1 ≤ Z) (hb : 0 ≤ b) (length : Fin K → ℝ)
    (hl : ∑ j, length j = 20033 / 120000)
    (hT : ∀ j P, P ∈ T j → (P.val.absNorm : ℝ) ≤ b * Z ^ (length j)) :
    (Fintype.card (∀ j, T j) : ℝ) ≤ (128 * b) ^ K * Z := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hc (j : Fin K) : ((T j).card : ℝ) ≤ 128 * b * Z ^ (length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val)
      (b * Z ^ (length j)) (by positivity)
      (by intro I hI; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI; exact p.property.ne_zero)
      (by intro I hI; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI; exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective, mul_assoc] using hh
  rw [Fintype.card_pi, Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc _ ≤ ∏ j, 128 * b * Z ^ (length j) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun j _ => hc j)
    _ = (128 * b) ^ K * Z ^ (20033 / 120000 : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.rpow_sum_of_pos hZ0, hl]
    _ ≤ (128 * b) ^ K * Z := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : (20033 / 120000 : ℝ) ≤ 1)

theorem stage1Vertex_finite_cube_saving {ι : Type*} [Fintype ι] (K : ℕ) (τ_Z b ζ A e : ℝ)
    (hτ : 0 < τ_Z) (hb : 0 < b) (hζ : ζ ≤ 1 / 100) (hA : 0 ≤ A)
    (he : 0 < e) (he' : e < 1 / 1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (hfirst : FirstTail (4 * e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Character) (Z : ℝ), 1 ≤ Z → ∀ R : Finset FreeRow,
      (∀ u ∈ R, u.val ≠ 1 ∧ ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤
        Z ^ ((97813 / 120000 : ℝ) + ζ)) →
      ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S),
      (∀ P : (∀ i, T i), Function.Injective (fun i => (P i).val)) →
      ∀ length : Fin K → ℝ, (∑ j, length j) = 20033 / 120000 →
      (∀ j P, P ∈ T j → (P.val.absNorm : ℝ) ≤ b * Z ^ (length j)) →
      ∀ W : Fin K → ℝ → ℂ, (∀ j y, ‖W j y‖ ≤ A) →
      ∀ (a B H : FreeRow → ℝ) (idx : FreeRow → ℕ) (ψ : FreeRow → ι → Character),
      (∀ u ∈ R, (51 / 100 : ℝ) ≤ a u ∧ a u ≤ 1 ∧ 2 < B u ∧ Z ^ τ_Z ≤ H u ∧
        H u ≤ (3 * idx u + 2 : ℕ) * B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u))
          (3 * (idx u + 1 : ℕ) * B u) < a u + 2 * e) →
      ‖finitePhysicalRows S hmax η R T W (fun j => Z ^ (length j)) W0 W1
          (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z -
        finiteCentralCubeRows S hS hmax η R T hT W (fun j => Z ^ (length j)) W0 W1
          (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z e a H‖ ≤
        C * (η.modulus.absNorm : ℝ) ^ 2 * Z ^ (-1 : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((14 : ℝ) / τ_Z)
  have hN' : 14 < τ_Z * N := ((div_lt_iff₀ hτ).mp hN).trans_eq (mul_comm _ _)
  obtain ⟨Cr, hCr, hrow⟩ := uniform_original_row_cube_error (ι := ι) K e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨128 * (128 * b) ^ K * A ^ K * (Cr * (b ^ K) ^ 3), by positivity, ?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z ^ ((97813 / 120000 : ℝ) + ζ) ≤ Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (by linarith : (97813 / 120000 : ℝ) + ζ ≤ 1)
  have hcR : (R.card : ℝ) ≤ 128 * Z := freeRow_count R Z hZ (fun u hu => (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀ j, T j) : ℝ) ≤ (128 * b) ^ K * Z :=
    stage1Vertex_central_prime_tuple_count T Z b hZ hb.le length hl hp
  let E : ℝ := (Cr * (b ^ K) ^ 3) * (η.modulus.absNorm : ℝ) ^ 2 * Z ^ (-3 : ℝ)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have herr (u : FreeRow) (hu : u ∈ R) (P : ∀ j, T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j => primaryIdealGenerator (P j).val.val)
          W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z u -
        centralCubeIntegral S hS hmax (fun j => (P j).val) (fun j => hT j _ (P j).property)
          η u W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z (a u) e (H u)‖ ≤ E := by
    rcases hbin u hu with ⟨ha, ha', hB, hHlo, hH, hzero⟩
    have hH0 : 0 ≤ H u := (Real.rpow_nonneg hZ0.le _).trans hHlo
    have hm := hrow η u (hR u hu).1 (fun j => (P j).val) (hdis P)
      (fun j => hT j _ (P j).property) (ψ u) (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ
      (a u) (B u) (H u) (idx u) ha ha' hB hH0 hH hzero
    have huZ : ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤ Z := (hR u hu).2.trans hrange
    have hp_prod : (∏ j, ((P j).val.val.absNorm : ℝ)) ≤ b ^ K * Z := by
      calc _ ≤ ∏ j, b * Z ^ (length j) :=
            Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun j _ => hp j _ (P j).property)
        _ = b ^ K * Z ^ (20033 / 120000 : ℝ) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              ← Real.rpow_sum_of_pos hZ0, hl]
        _ ≤ b ^ K * Z := mul_le_mul_of_nonneg_left
            (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : (20033 / 120000 : ℝ) ≤ 1))
            (by positivity)
    have hcost : contourArithmeticCost η u (fun j => (P j).val) ≤
        (η.modulus.absNorm : ℝ) ^ 2 * (b ^ K) ^ 3 * Z ^ (9 : ℝ) := by
      have hp0 : 0 ≤ ∏ j, ((P j).val.val.absNorm : ℝ) :=
        Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
      unfold contourArithmeticCost
      calc _ ≤ (η.modulus.absNorm : ℝ) ^ 2 * Z ^ 6 * (b ^ K * Z) ^ 3 :=
            mul_le_mul (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (Nat.cast_nonneg _) huZ 6) (sq_nonneg _))
              (pow_le_pow_left₀ hp0 hp_prod 3) (pow_nonneg hp0 3) (by positivity)
        _ = (η.modulus.absNorm : ℝ) ^ 2 * (b ^ K) ^ 3 * (Z ^ (6 : ℝ) * Z ^ (3 : ℝ)) := by
            have h63 : Z ^ (6 : ℝ) * Z ^ (3 : ℝ) = Z ^ 6 * Z ^ 3 := by norm_num
            rw [h63]; ring
        _ = _ := by rw [← Real.rpow_add hZ0]; norm_num
    have hscale : (Z ^ (2111 / 6000 : ℝ)) ^ (1 / 2 - (17 / 50 : ℝ)) * Z ^ (2 + (17 / 50 : ℝ) - 1) *
        (Z ^ (19249 / 40000 : ℝ)) ^ ((1 - a u - 6 * e) - 1) ≤ Z ^ (2 : ℝ) := by
      rw [← Real.rpow_mul hZ0.le, ← Real.rpow_mul hZ0.le,
        ← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    have hden : Z ^ (τ_Z * N) ≤ height (H u) ^ N := by
      rw [Real.rpow_mul_natCast hZ0.le]
      apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
      simp only [height, abs_of_nonneg hH0]; linarith
    have hsave : Z ^ (11 : ℝ) / Z ^ (τ_Z * N) ≤ Z ^ (-3 : ℝ) := by
      rw [← Real.rpow_sub hZ0]; exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    apply hm.trans
    calc _ ≤ Cr * ((η.modulus.absNorm : ℝ) ^ 2 * (b ^ K) ^ 3 * Z ^ (9 : ℝ)) * Z ^ (2 : ℝ) /
            height (H u) ^ N := by
          apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hCr) hscale
            (by positivity) (by positivity)
      _ = (Cr * (b ^ K) ^ 3 * (η.modulus.absNorm : ℝ) ^ 2) *
            (Z ^ (11 : ℝ) / height (H u) ^ N) := by
          have hh : Z ^ (9 : ℝ) * Z ^ (2 : ℝ) = Z ^ (11 : ℝ) := by
            rw [← Real.rpow_add hZ0]; norm_num
          rw [show Cr * ((η.modulus.absNorm : ℝ) ^ 2 * (b ^ K) ^ 3 * Z ^ (9 : ℝ)) * Z ^ (2 : ℝ) =
              (Cr * (b ^ K) ^ 3 * (η.modulus.absNorm : ℝ) ^ 2) * (Z ^ (9 : ℝ) * Z ^ (2 : ℝ)) by ring,
            hh, mul_div_assoc]
      _ ≤ (Cr * (b ^ K) ^ 3 * (η.modulus.absNorm : ℝ) ^ 2) *
            (Z ^ (11 : ℝ) / Z ^ (τ_Z * N)) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden)
            (by positivity)
      _ ≤ E := by dsimp [E]; exact mul_le_mul_of_nonneg_left hsave (by positivity)
  have hw (P : ∀ j, T j) :
      ‖∏ j, W j (((P j).val.val.absNorm : ℝ) / Z ^ (length j))‖ ≤ A ^ K := by
    rw [norm_prod]
    calc _ ≤ ∏ _j : Fin K, A := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralCubeRows
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ u ∈ R, ‖(∑ P : (∀ j, T j), (∏ j, W j (((P j).val.val.absNorm : ℝ) / Z ^ (length j))) *
            rowIntegral η S (calibrationForSet S hmax) (fun j => primaryIdealGenerator (P j).val.val)
              W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z u) -
          ∑ P : (∀ j, T j), (∏ j, W j (((P j).val.val.absNorm : ℝ) / Z ^ (length j))) *
            centralCubeIntegral S hS hmax (fun j => (P j).val) (fun j => hT j _ (P j).property)
              η u W0 W1 (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z (a u) e (H u)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _u ∈ R, ∑ _P : (∀ j, T j), A ^ K * E := by
        apply Finset.sum_le_sum; intro u hu
        rw [← Finset.sum_sub_distrib]
        apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun P _ => ?_)
        rw [← mul_sub, norm_mul]
        exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card : ℝ) * (Fintype.card (∀ j, T j) : ℝ) * (A ^ K * E) := by simp; ring
    _ ≤ (128 * Z) * ((128 * b) ^ K * Z) * (A ^ K * E) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity))
          (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
        have hz : Z ^ (2 : ℝ) * Z ^ (-3 : ℝ) = Z ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hZ0]; norm_num
        dsimp [E]
        rw [show (128 * Z) * ((128 * b) ^ K * Z) *
            (A ^ K * (Cr * (b ^ K) ^ 3 * (η.modulus.absNorm : ℝ) ^ 2 * Z ^ (-3 : ℝ))) =
          128 * (128 * b) ^ K * A ^ K * (Cr * (b ^ K) ^ 3) * (η.modulus.absNorm : ℝ) ^ 2 *
            (Z ^ (2 : ℝ) * Z ^ (-3 : ℝ)) by rw [Real.rpow_two]; ring, hz]

/-! ### Piece 4: Floor rows (`a = 51/100`) at `(Z^{2111/6000}, Z^{19249/40000}, Z)` -/

private lemma stage1VertexPoolOutside (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N → ℝ) :
    ∀ j P, P ∈ pool (RayQuotient.identityClass M H) S c b (Y j) → P.val ∉ S :=
  fun _ P hP => ((mem_pool _ S c b _ P).mp hP).2.2.2

private lemma stage1Vertex_cubeArithmeticSum_pool_congr {K : ℕ} (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal) (η : Character)
    (R : Finset FreeRow) {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ}
    (WC : Fin K → ℝ → ℂ) {Y₁ Y₂ : Fin K → ℝ} (hY : Y₁ = Y₂)
    (hPS₁ : ∀ j P, P ∈ pool (RayQuotient.identityClass M H) S 1 2 (Y₁ j) → P.val ∉ S)
    (hPS₂ : ∀ j P, P ∈ pool (RayQuotient.identityClass M H) S 1 2 (Y₂ j) → P.val ∉ S)
    (a e : ℝ) (t : HeightSpace) :
    cubeArithmeticSum S hS hmax η R
      (fun j => pool (RayQuotient.identityClass M H) S 1 2 (Y₁ j)) hPS₁ WC Y₁ a e t =
    cubeArithmeticSum S hS hmax η R
      (fun j => pool (RayQuotient.identityClass M H) S 1 2 (Y₂ j)) hPS₂ WC Y₂ a e t := by
  subst hY; rfl

theorem stage1Vertex_floor_rows_saving (D : HighData subDelta)
    (he_t : 2000 * D.e ≤ D.t) (heps_t : ((D.N : ℝ) + 8) * D.eps ≤ D.t)
    (F : SourceData D) (n : ℕ) (τ : ℝ)
    (hτ : 0 < τ) (_hτcost : 4 * τ < (1 / 200) * D.cost) (hτeps : τ * (2 + 4 * D.eps) < D.t) :
    let ell' : Fin D.N → ℝ := fun j => (20033 / 20000 : ℝ) * D.ell j
    ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      let Z' : ℝ := Z ^ (20033 / 20000 : ℝ)
      let Yp : Fin D.N → ℝ := fun j => Z ^ (ell' j)
      let T : Fin D.N → Finset HeckeIdealSeries.PrimeIdeal :=
        fun j => pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
      let normer := sourceResidueConstant F.W F.W F.modulus *
        (Probe.principalScalar Finset.univ Z (20033 / 120000)
          (slotMass T (residueWeights (fun _ => F.w) Yp)) : ℂ)
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z' ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z' ^ ((97813 / 120198 : ℝ) + D.t)) →
      ∀ idx : FreeRow → ℕ, (∀ u ∈ rows, idx u ≤ n) →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3 * (idx u + 1 : ℕ) * Z' ^ τ) < 51 / 100 + 2 * D.e) →
      normer ≠ 0 ∧
      ‖finiteCentralCubeRows F.S F.exclusions F.maximal η rows T
          (stage1VertexPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp) (fun _ y => (F.w y : ℂ)) Yp
          F.W F.W (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e
          (fun _ => 51 / 100) (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ) / normer‖ ≤
        C * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) * Z ^ (268847 / 1440000 - 1 / 250 : ℝ) := by
  intro ell'
  let WC : Fin D.N → ℝ → ℂ := fun _ y => (F.w y : ℂ)
  have hWC (j : Fin D.N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp F.smooth
  have hWCs (j : Fin D.N) : Function.support (WC j) ⊆ Ioo 1 2 := by
    intro y hy; apply F.support; intro hh; exact hy (by dsimp [WC]; rw [hh]; simp)
  have hWCB (j : Fin D.N) (y : ℝ) : ‖WC j y‖ ≤ 1 := by
    simpa only [WC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (F.bounded y).1]
      using (F.bounded y).2
  obtain ⟨Ca, hCa, harith⟩ := actual_global_floor_cube_arithmetic F.modulus ⊤ le_top
    D.N n D.e D.eps 1 2 1 D.t (1 / 200) (7 / 8) D.rmin τ D.ε D.κ D.cost D.t (1 / 100) D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    D.t_pos.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos
    D.kappa_pos D.cost_pos.le D.t_pos (by norm_num) D.phase_budget D.epsilon_gap
    D.t_pos (by linarith) hτeps F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j => (D.slots_bounds j).2.1) (fun j => (D.slots_bounds j).2.2)
    WC hWCs hWC hWCB D.slots_sum
  obtain ⟨Cp, hCp, hprofile⟩ := actual_common_cube_aggregate_norm F.W F.W 1 2 1 2
    (by norm_num) (by norm_num) F.complex_support F.complex_support
  have hell'_pos (j : Fin D.N) : 0 < ell' j := mul_pos (by norm_num) (D.slots_bounds j).1
  have hell'_sum : ∑ j, ell' j = 20033 / 120000 := by
    dsimp [ell']; rw [← Finset.mul_sum, D.slots_sum]; norm_num
  obtain ⟨Cn, hCn, hnormer⟩ := ProbePhysical.stage1Vertex_ray_normalizer_inverse F.modulus ⊤ le_top
    F.S F.exclusions 1 2 (by norm_num) (by norm_num) ell' hell'_pos hell'_sum
    (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact) (fun _ => F.support)
    (fun _ y => (F.bounded y).1) (fun _ => F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t / 8) (div_pos D.t_pos (by norm_num))
  refine ⟨(n + 1 : ℕ) * (Cp * Ca * Cn), by positivity, ?_⟩
  intro η
  filter_upwards [stage1Vertex_scale_tendsto.eventually (harith η),
    stage1Vertex_scale_tendsto.eventually (source_cube_height_eventually τ hτ),
    hnormer, eventually_ge_atTop (1 : ℝ)] with Z hb hZ' hn hZ
  dsimp only at hn ⊢
  intro rows hrows idx hidx hbin
  refine ⟨hn.1, ?_⟩
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  let Z' : ℝ := Z ^ (20033 / 20000 : ℝ)
  have hZ'p : 0 < Z' := Real.rpow_pos_of_pos hZp _
  let Yp : Fin D.N → ℝ := fun j => Z ^ (ell' j)
  let T : Fin D.N → Finset HeckeIdealSeries.PrimeIdeal :=
    fun j => pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
  let hT := stage1VertexPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp
  let normer := sourceResidueConstant F.W F.W F.modulus *
    (Probe.principalScalar Finset.univ Z (20033 / 120000)
      (slotMass T (residueWeights (fun _ => F.w) Yp)) : ℂ)
  let Ri : ℕ → Finset FreeRow := fun i => rows.filter (fun u => idx u = i)
  have hv_le : (97813 / 120198 : ℝ) + D.t ≤ 7 / 8 - D.t := by linarith [D.t_small]
  have hpart := finiteCentralCubeRows_bin_partition F.S F.exclusions F.maximal η rows T hT WC Yp
    F.W F.W (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e (Z' ^ τ) idx (fun _ => 0) n 0
    (fun u hu => ⟨hidx u hu, le_rfl⟩)
  have heq : finiteCentralCubeRows F.S F.exclusions F.maximal η rows T hT WC Yp F.W F.W
      (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e
      (fun _ => 51 / 100) (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ) =
      ∑ i ∈ Finset.range (n + 1),
        finiteCentralCubeRows F.S F.exclusions F.maximal η (Ri i) T hT WC Yp F.W F.W
          (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e
          (fun _ => 51 / 100) (fun _ => (3 * i + 1 : ℕ) * Z' ^ τ) := by
    simpa [cubeBinRows, Ri] using hpart
  have hcell (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      ‖finiteCentralCubeRows F.S F.exclusions F.maximal η (Ri i) T hT WC Yp F.W F.W
          (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e
          (fun _ => 51 / 100) (fun _ => (3 * i + 1 : ℕ) * Z' ^ τ) / normer‖ ≤
        (Cp * Ca * Cn) * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
          Z ^ (268847 / 1440000 - 1 / 250 : ℝ) := by
    have hsub : Ri i ⊆ rows := Finset.filter_subset _ _
    have hrows_i : ∀ u ∈ Ri i, u.val ≠ 1 ∧ Z' ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z' ^ ((7 / 8 : ℝ) - D.t) := fun u hu => by
      have hru := hrows u (hsub hu)
      exact ⟨hru.1, hru.2.1, hru.2.2.1,
        hru.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ'.1 hv_le)⟩
    have hnorm_i : ∀ u ∈ Ri i, rowNorm u ≤ Z' ^ ((97813 / 120198 : ℝ) + D.t) :=
      fun u hu => (hrows u (hsub hu)).2.2.2
    have hbin_i : ∀ u ∈ Ri i, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3 * (i + 1 : ℕ) * Z' ^ τ) < 51 / 100 + 2 * D.e := fun u hu => by
      have hh := hbin u (hsub hu); rwa [(Finset.mem_filter.mp hu).2] at hh
    have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have har_i := hb (7 / 8) (by norm_num) le_rfl ((97813 / 120198 : ℝ) + D.t)
      (by linarith [D.t_pos]) (Ri i) hrows_i hnorm_i i hi_le hbin_i
    let vf : ℝ := ((97813 / 120198 : ℝ) + D.t) * (67 / 100 + 12 * D.e + D.eps * ((D.N : ℝ) + 8)) +
      D.t - 1 / 40 + D.t / 6
    let mass : ℝ := Ca * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) * Z' ^ vf
    have har_i' : ∀ t : HeightSpace,
        ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z' ^ τ ∧ |t.2| ≤ (3 * i + 1 : ℕ) * Z' ^ τ) ∧
          |t.1.2| ≤ (3 * i + 1 : ℕ) * Z' ^ τ) →
        ‖cubeArithmeticSum F.S F.exclusions F.maximal η (Ri i) T hT WC Yp (51 / 100) D.e t‖ ≤
          mass := fun t ht => by
      have hh := har_i t ht; dsimp only at hh
      rwa [stage1Vertex_cubeArithmeticSum_pool_congr F.S F.exclusions F.maximal η (Ri i) WC
        (stage1Vertex_scale_slot_eq hZp.le D.ell) _ hT (51 / 100) D.e t] at hh
    have hheight : (3 * i + 1 : ℕ) * Z' ^ τ ≤ (3 * i + 2 : ℕ) * Z' ^ τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show 3 * i + 1 ≤ 3 * i + 2 by omega))
        (Real.rpow_nonneg hZ'p.le _)
    have hp := hprofile D.e (51 / 100) (Z' ^ τ) ((3 * i + 1 : ℕ) * Z' ^ τ) i
      D.e_pos D.e_small le_rfl (by norm_num) hZ'.2 hheight F.S F.exclusions F.maximal F.first
      η (Ri i) (fun u hu => (hrows_i u hu).1) T hT (rayCubeFamily F.modulus ⊤ le_top) hbin_i
      WC Yp (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z
      (Real.rpow_pos_of_pos hZp _) (Real.rpow_pos_of_pos hZp _) hZp mass
      (by dsimp [mass]; positivity) har_i'
    rw [div_eq_mul_inv, norm_mul]
    have hm := mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    apply hm.trans
    have hexp_eq : ((Z ^ (2111 / 6000 : ℝ)) ^ (4 / 25 : ℝ) * Z ^ ((51 / 100 : ℝ) + 16 * D.e - 33 / 50) *
        (Z ^ (19249 / 40000 : ℝ)) ^ (-(51 / 100 : ℝ) - 6 * D.e)) * Z' ^ vf * Z ^ (D.t / 8) =
        Z ^ ((-22639 / 37500 : ℝ) + (20751 / 40000 : ℝ) * (51 / 100) +
          (262253 / 20000 : ℝ) * D.e + (20033 / 20000 : ℝ) * vf + D.t / 8) := by
      dsimp [Z']
      rw [← Real.rpow_mul hZp.le, ← Real.rpow_mul hZp.le, ← Real.rpow_mul hZp.le,
        ← Real.rpow_add hZp, ← Real.rpow_add hZp, ← Real.rpow_add hZp, ← Real.rpow_add hZp]
      exact congrArg (fun x : ℝ => Z ^ x) (by ring)
    have hexp_le : (-22639 / 37500 : ℝ) + (20751 / 40000 : ℝ) * (51 / 100) +
        (262253 / 20000 : ℝ) * D.e + (20033 / 20000 : ℝ) * vf + D.t / 8 ≤
        268847 / 1440000 - 1 / 250 := by
      dsimp [vf]
      have hdt := D.t_small; have he_pos := D.e_pos; have heps_pos := D.eps_pos
      nlinarith [he_t, heps_t]
    calc _ = (Cp * Ca * Cn) * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
            (((Z ^ (2111 / 6000 : ℝ)) ^ (4 / 25 : ℝ) * Z ^ ((51 / 100 : ℝ) + 16 * D.e - 33 / 50) *
              (Z ^ (19249 / 40000 : ℝ)) ^ (-(51 / 100 : ℝ) - 6 * D.e)) * Z' ^ vf * Z ^ (D.t / 8)) := by
          dsimp [mass]; ring
      _ = (Cp * Ca * Cn) * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
            Z ^ ((-22639 / 37500 : ℝ) + (20751 / 40000 : ℝ) * (51 / 100) +
              (262253 / 20000 : ℝ) * D.e + (20033 / 20000 : ℝ) * vf + D.t / 8) := by rw [hexp_eq]
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZ hexp_le) (by positivity)
  rw [heq, Finset.sum_div]
  calc _ ≤ ∑ i ∈ Finset.range (n + 1),
          ‖finiteCentralCubeRows F.S F.exclusions F.maximal η (Ri i) T hT WC Yp F.W F.W
            (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e
            (fun _ => 51 / 100) (fun _ => (3 * i + 1 : ℕ) * Z' ^ τ) / normer‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (n + 1),
          (Cp * Ca * Cn) * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
            Z ^ (268847 / 1440000 - 1 / 250 : ℝ) := Finset.sum_le_sum hcell
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ### Piece 5: Nonfloor rows (`51/100 < a ≤ 1`) via Stage-0 (`d' < 1/2`) + Stage-1 (`1/2 ≤ d' ≤ 5/6`) -/

lemma stage1Vertex_nonfloor_low_dyad_exponent_bound (D : HighData subDelta)
    (hε_t : 2000 * D.ε ≤ D.t) (he_t : 2000 * D.e ≤ D.t)
    (heps_t : ((D.N : ℝ) + 8) * D.eps ≤ D.t)
    {τ d' v' a q : ℝ} (hτ2 : 2 * τ ≤ D.t)
    (hd'0 : 0 ≤ d') (hd'lt : d' < 1 / 2) (_hv'0 : 0 ≤ v') (hv'le : v' ≤ d')
    (hdv : d' - v' ≤ 2 * D.t) (ha : 51 / 100 < a) (ha1 : a ≤ 1)
    (hq0 : 0 ≤ q) (hq : q ≤ (2 * a - 1) / 2) :
    ((4 / 25 : ℝ) * (2111 / 6000) + (a + 16 * D.e - 33 / 50) + (19249 / 40000 : ℝ) * (-a - 6 * D.e)) +
      (20033 / 20000 : ℝ) * (D.t + 2 * τ + D.t +
        d' * adaptiveRowExponent (2 * a - 1) q subDelta D.ε D.t D.t D.t +
        v' * (a - 1 / 2 + 12 * D.e + D.eps * ((D.N : ℝ) + 8) - 17 / 50) +
        D.t - 2 / 75 + q / 6 + D.t / 6) +
      D.t / 8 + D.t / 8 ≤
      268847 / 1440000 - 1 / 200000 := by
  let δ : ℝ := 2 * a - 1
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  have hδ0 : 0 ≤ δ := hδ_pos.le
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  let x : ℝ := q / δ
  have hx0 : 0 ≤ x := div_nonneg hq0 hδ0
  have hx : x ≤ 1 / 2 := (div_le_iff₀ hδ_pos).mpr (by dsimp [δ] at hq ⊢; linarith)
  have hxd : x * δ = q := div_mul_cancel₀ q hδ_pos.ne'
  let d_Z : ℝ := (20033 / 20000 : ℝ) * v'
  have hd_Z_hi : d_Z ≤ 20033 / 40000 := by dsimp [d_Z]; linarith
  let R₀ : ℝ := if δ ≤ 5 / 6 then Budget.rowCount δ x else 1 - δ
  have hR₀_bounds : 0 ≤ R₀ ∧ R₀ ≤ 4 := by
    dsimp [R₀]; split_ifs with hδ56
    · have hsl := Budget.rowCount_slope_bounds hδ0 hδ56 hx0 hx
      exact ⟨by linarith [hsl.1], by linarith [hsl.2, hδ0]⟩
    · exact ⟨by linarith, by linarith⟩
  have hadapt : adaptiveRowExponent δ q subDelta D.ε D.t D.t D.t ≤
      R₀ + subDelta / 4 + 159 * D.ε + 9 * D.t := by
    unfold adaptiveRowExponent; dsimp [R₀]; split_ifs with hδ56
    · rw [balancedRowCount_eq_rowCount hδ0 hδ56 hx]; linarith
    · have := subDelta_pos; linarith [D.epsilon_pos, D.t_pos]
  have hd_adapt : d' * adaptiveRowExponent δ q subDelta D.ε D.t D.t D.t ≤
      v' * R₀ + 2 * D.t * 4 + (1 / 2) * (subDelta / 4 + 159 * D.ε + 9 * D.t) := by
    have h1 := mul_le_mul_of_nonneg_left hadapt hd'0
    have h2 : d' * R₀ ≤ v' * R₀ + 2 * D.t * 4 := by
      nlinarith [hR₀_bounds.1, hR₀_bounds.2, hdv, hv'le, D.t_pos]
    have h3 : d' * (subDelta / 4 + 159 * D.ε + 9 * D.t) ≤
        (1 / 2) * (subDelta / 4 + 159 * D.ε + 9 * D.t) :=
      mul_le_mul_of_nonneg_right hd'lt.le (by have := subDelta_pos; linarith [D.epsilon_pos, D.t_pos])
    linarith
  have hmain_id : ((4 / 25 : ℝ) * (2111 / 6000) + (a - 33 / 50) - (19249 / 40000 : ℝ) * a) +
      (20033 / 20000 : ℝ) * (v' * R₀ + v' * (a - 1 / 2 - 17 / 50) - 2 / 75 + q / 6) =
      268847 / 1440000 + Budget.rowExponent (2111 / 6000) (19249 / 40000) (20033 / 120000)
        (139989 / 160000) (17 / 50) δ q R₀ d_Z := by
    dsimp [δ, d_Z]; unfold Budget.rowExponent; ring
  have hcert : Budget.rowExponent (2111 / 6000) (19249 / 40000) (20033 / 120000)
      (139989 / 160000) (17 / 50) δ q R₀ d_Z ≤ -(1 / 25) := by
    dsimp only [R₀]; split_ifs with hδ56
    · have h78 := Budget.rowExponent_balanced_subSevenEighths hδ0 hδ56 hx0 hx le_rfl
        (add_zero (1219 / 1500 : ℝ)).symm.le
      have hsl := Budget.rowCount_slope_bounds hδ0 hδ56 hx0 hx
      rw [← hxd]
      have hdiff : Budget.rowExponent (2111 / 6000) (19249 / 40000) (20033 / 120000)
            (139989 / 160000) (17 / 50) δ (x * δ) (Budget.rowCount δ x) d_Z -
          Budget.rowExponent (17 / 48) (479 / 1000) (1001 / 6000)
            (20999 / 24000) (17 / 50) δ (x * δ) (Budget.rowCount δ x) (1219 / 1500) =
          (d_Z - 1219 / 1500) * (Budget.rowCount δ x + δ / 2 - 17 / 50) +
          (-(25789 / 36000000) - (89 / 80000) * δ + (13 / 120000) * (x * δ)) := by
        unfold Budget.rowExponent; ring
      have hdrop : (d_Z - 1219 / 1500) * (Budget.rowCount δ x + δ / 2 - 17 / 50) ≤ -(1 / 20) := by
        nlinarith only [hd_Z_hi, hsl.1, hsl.2]
      have hxd_le : x * δ ≤ 1 / 2 := by nlinarith only [hx, hδ1, hx0, hδ0]
      linarith only [h78, hdiff, hdrop, hδ0, hδ1, hx0, hxd_le]
    · have hhi := Budget.rowExponent_high_delta_stage1_vertex (le_of_not_ge hδ56) hδ1 hq
        (le_rfl : (0 : ℝ) ≤ 0) (by linarith only [hd_Z_hi] : d_Z ≤ 97813 / 120000 + 0)
      linarith only [hhi]
  have hv_err : v' * (12 * D.e + D.eps * ((D.N : ℝ) + 8)) ≤
      (1 : ℝ) * (12 * D.e + ((D.N : ℝ) + 8) * D.eps) := by
    have hv1 : v' ≤ 1 := by linarith
    have herr0 : 0 ≤ 12 * D.e + ((D.N : ℝ) + 8) * D.eps := by
      have := D.e_pos; have := D.eps_pos; positivity
    nlinarith
  have hsubD : subDelta = 1 / 100000000 := rfl
  have := D.t_small; have := D.e_pos; have := D.epsilon_pos
  linarith

lemma stage1Vertex_nonfloor_high_dyad_exponent_bound (D : HighData subDelta)
    (ht_le : D.t ≤ subDelta / 8)
    (hε_t : 2000 * D.ε ≤ D.t) (he_t : 2000 * D.e ≤ D.t)
    (heps_t : ((D.N : ℝ) + 8) * D.eps ≤ D.t)
    {τ d' v' a q : ℝ} (hτ2 : 2 * τ ≤ D.t)
    (hd'0 : 1 / 2 ≤ d') (hd'hi : d' ≤ 5 / 6) (_hv'0 : 0 ≤ v') (hv'hi : v' ≤ 97813 / 120198 + D.t)
    (hdv : d' - v' ≤ 2 * D.t) (ha : 51 / 100 < a) (ha1 : a ≤ 1)
    (hq0 : 0 ≤ q) (hq : q ≤ (2 * a - 1) / 2) :
    ((4 / 25 : ℝ) * (2111 / 6000) + (a + 16 * D.e - 33 / 50) + (19249 / 40000 : ℝ) * (-a - 6 * D.e)) +
      (20033 / 20000 : ℝ) * (D.t + 2 * τ + D.t +
        d' * adaptiveRowExponentSub16799 (2 * a - 1) q subDelta D.ε (15 * D.t) D.t D.t +
        v' * (a - 1 / 2 + 12 * D.e + D.eps * ((D.N : ℝ) + 8) - 17 / 50) +
        D.t - 2 / 75 + q / 6 + D.t / 6) +
      D.t / 8 + D.t / 8 ≤
      268847 / 1440000 - 1 / 200000 := by
  let δ : ℝ := 2 * a - 1
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  have hδ0 : 0 ≤ δ := hδ_pos.le
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  let x : ℝ := q / δ
  have hx0 : 0 ≤ x := div_nonneg hq0 hδ0
  have hx : x ≤ 1 / 2 := (div_le_iff₀ hδ_pos).mpr (by dsimp [δ] at hq ⊢; linarith)
  have hxd : x * δ = q := div_mul_cancel₀ q hδ_pos.ne'
  let d_Z : ℝ := (20033 / 20000 : ℝ) * v'
  let ζ_Z : ℝ := (20033 / 20000 : ℝ) * D.t
  have hζ_Z : 0 ≤ ζ_Z := mul_nonneg (by norm_num) D.t_pos.le
  have hd_Z : d_Z ≤ 97813 / 120000 + ζ_Z := by dsimp [d_Z, ζ_Z]; linarith
  let R₁ : ℝ := if δ ≤ 5 / 6 then Budget.rowCountSub16799 δ x else 1 - δ
  have hR₁_bounds : 0 ≤ R₁ ∧ R₁ ≤ 4 := by
    dsimp [R₁]; split_ifs with hδ56
    · have hsl := Budget.rowCountSub16799_slope_bounds hδ0 hδ56 hx0 hx
      exact ⟨by linarith [hsl.1], by linarith [hsl.2, hδ0]⟩
    · exact ⟨by linarith, by linarith⟩
  have hadapt : adaptiveRowExponentSub16799 δ q subDelta D.ε (15 * D.t) D.t D.t ≤
      R₁ + subDelta / 4 + 159 * D.ε + 23 * D.t := by
    unfold adaptiveRowExponentSub16799; dsimp [R₁]; split_ifs with hδ56
    · linarith
    · have := subDelta_pos; linarith [D.epsilon_pos, D.t_pos]
  have hd_adapt : d' * adaptiveRowExponentSub16799 δ q subDelta D.ε (15 * D.t) D.t D.t ≤
      v' * R₁ + 2 * D.t * 4 + (5 / 6) * (subDelta / 4 + 159 * D.ε + 23 * D.t) := by
    have h1 := mul_le_mul_of_nonneg_left hadapt ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hd'0)
    have h2 : d' * R₁ ≤ v' * R₁ + 2 * D.t * 4 := by
      rcases le_total d' v' with hle | hle
      · have hle_m : d' * R₁ ≤ v' * R₁ := mul_le_mul_of_nonneg_right hle hR₁_bounds.1
        have ht0 := D.t_pos
        linarith only [hle_m, ht0]
      · nlinarith only [hle, hR₁_bounds.1, hR₁_bounds.2, hdv]
    have h3 : d' * (subDelta / 4 + 159 * D.ε + 23 * D.t) ≤
        (5 / 6) * (subDelta / 4 + 159 * D.ε + 23 * D.t) :=
      mul_le_mul_of_nonneg_right hd'hi (by
        have hsd := subDelta_pos; have he0 := D.epsilon_pos; have ht0 := D.t_pos
        linarith only [hsd, he0, ht0])
    linarith only [h1, h2, h3]
  have hmain_id : ((4 / 25 : ℝ) * (2111 / 6000) + (a - 33 / 50) - (19249 / 40000 : ℝ) * a) +
      (20033 / 20000 : ℝ) * (v' * R₁ + v' * (a - 1 / 2 - 17 / 50) - 2 / 75 + q / 6) =
      268847 / 1440000 + Budget.rowExponent (2111 / 6000) (19249 / 40000) (20033 / 120000)
        (139989 / 160000) (17 / 50) δ q R₁ d_Z := by
    dsimp [δ, d_Z]; unfold Budget.rowExponent; ring
  have hcert : Budget.rowExponent (2111 / 6000) (19249 / 40000) (20033 / 120000)
      (139989 / 160000) (17 / 50) δ q R₁ d_Z ≤ -(1 / 100000) + 3 * ζ_Z := by
    dsimp [R₁]; split_ifs with hδ56
    · rw [← hxd]
      exact Budget.rowExponent_balanced_stage1_vertex hδ0 hδ56 hx0 hx hζ_Z hd_Z
    · have hhi := Budget.rowExponent_high_delta_stage1_vertex (le_of_not_ge hδ56) hδ1 hq hζ_Z hd_Z
      linarith
  have hv_err : v' * (12 * D.e + D.eps * ((D.N : ℝ) + 8)) ≤
      (1 : ℝ) * (12 * D.e + ((D.N : ℝ) + 8) * D.eps) := by
    have hv1 : v' ≤ 1 := by linarith [D.t_small]
    have herr0 : 0 ≤ 12 * D.e + ((D.N : ℝ) + 8) * D.eps := by
      have := D.e_pos; have := D.eps_pos; positivity
    nlinarith
  have hsubD : subDelta = 1 / 100000000 := rfl
  have := D.e_pos; have := D.epsilon_pos; have := D.t_pos
  dsimp [ζ_Z] at hcert
  linarith

theorem stage1Vertex_nonfloor_rows_saving (D : HighData subDelta)
    (ht_le : D.t ≤ subDelta / 8)
    (hε_t : 2000 * D.ε ≤ D.t) (he_t : 2000 * D.e ≤ D.t)
    (heps_t : ((D.N : ℝ) + 8) * D.eps ≤ D.t)
    (F : SourceData D)
    (counts_0 : CountParameters F.modulus ⊤ D.t)
    (counts_1 : CountParametersSub16799 F.modulus ⊤ (15 * D.t))
    (n : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτd : τ < (1 / 200 : ℝ) / 2)
    (hτcost : 4 * τ < (1 / 200) * D.cost) (_hτt : τ < D.t) (hτ2 : 2 * τ ≤ D.t)
    (hτeps : τ * (2 + 4 * D.eps) < D.t) :
    let ell' : Fin D.N → ℝ := fun j => (20033 / 20000 : ℝ) * D.ell j
    ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      let Z' : ℝ := Z ^ (20033 / 20000 : ℝ)
      let Yp : Fin D.N → ℝ := fun j => Z ^ (ell' j)
      let T : Fin D.N → Finset HeckeIdealSeries.PrimeIdeal :=
        fun j => pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
      let normer := sourceResidueConstant F.W F.W F.modulus *
        (Probe.principalScalar Finset.univ Z (20033 / 120000)
          (slotMass T (residueWeights (fun _ => F.w) Yp)) : ℂ)
      ∀ C0 : ℝ, 0 ≤ C0 →
      SourceMomentBound F counts_0 η Z' τ (C0 * Z' ^ D.t) (Z' ^ (2 * τ)) →
      (∀ rows : Finset FreeRow, ∀ d' a : ℝ,
        1 / 2 ≤ d' → d' ≤ 5 / 6 → 51 / 100 < a → a ≤ 1 →
        (∀ u ∈ rows, u.val ≠ 1 ∧ Z' ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
          (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
          rowNorm u ≤ Z' ^ (d' - D.t)) →
        ∀ i : ℕ, ∀ z : ℂ, z.re = 17 / 50 → |z.im| ≤ Z' ^ (2 * τ) →
          SourceMomentsAtSub16799 F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
            (fun _ y => (F.w y : ℂ)) Z' d' a D.ε τ (5 / 6) 2 D.t D.t i z subDelta
            (if 2 * a - 1 ≤ 5 / 6 then counts_1.cB else counts_1.cH)
            (if 2 * a - 1 ≤ 5 / 6 then counts_1.kB else counts_1.kH)
            (C0 * Z' ^ D.t) (Z' ^ (2 * τ)) (15 * D.t)) →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z' ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z' ^ ((97813 / 120198 : ℝ) + D.t)) →
      ∀ idx grid : FreeRow → ℕ,
      (∀ u ∈ rows, idx u ≤ n ∧ grid u ≤ ⌊(49 / 100 : ℝ) / D.e⌋₊ ∧
        grid u ≠ 0 ∧ 51 / 100 + D.e * grid u ≤ 1) →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3 * (idx u + 1 : ℕ) * Z' ^ τ) < 51 / 100 + D.e * grid u + 2 * D.e) →
      (∀ u ∈ rows, 51 / 100 + D.e * grid u ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3 * idx u : ℕ) * Z' ^ τ)) →
      normer ≠ 0 ∧
      ‖finiteCentralCubeRows F.S F.exclusions F.maximal η rows T
          (stage1VertexPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp) (fun _ y => (F.w y : ℂ)) Yp
          F.W F.W (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e
          (fun u => 51 / 100 + D.e * grid u) (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ) / normer‖ ≤
        C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
          Z ^ (268847 / 1440000 - 1 / 200000 : ℝ) := by
  intro ell'
  let WC : Fin D.N → ℝ → ℂ := fun _ y => (F.w y : ℂ)
  have hWC (j : Fin D.N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp F.smooth
  have hWCs (j : Fin D.N) : Function.support (WC j) ⊆ Ioo 1 2 := by
    intro y hy; apply F.support; intro hh; exact hy (by dsimp [WC]; rw [hh]; simp)
  have hWCB (j : Fin D.N) (y : ℝ) : ‖WC j y‖ ≤ 1 := by
    simpa only [WC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (F.bounded y).1]
      using (F.bounded y).2
  obtain ⟨Cc₀, hCc₀, hclass₀⟩ := actual_nonfloor_class_from_raw_moments F.modulus ⊤ le_top
    D.N n D.e D.eps 1 2 1 D.t (1 / 200) (7 / 8) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    D.t_pos.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos
    D.kappa_pos D.cost_pos.le D.t_pos D.phase_budget D.epsilon_gap D.t_pos (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j => (D.slots_bounds j).2.1) (fun j => (D.slots_bounds j).2.2)
    WC hWCs hWC hWCB D.slots_sum (by norm_num) D.epsilon_small D.kappa_small hτd hτcost
    (by nlinarith [D.detector_budget]) F.w F.smooth F.compact F.positive_support
    (fun y => (F.bounded y).1) F.nonzero 1 2 1 (by norm_num) (by norm_num) (by norm_num)
    F.support (fun y => (F.bounded y).2) D.t subDelta D.t D.t (2 * τ) D.t
    D.t_pos subDelta_pos.le subDelta_le_eighth D.t_pos D.t_pos (by linarith) counts_0
  obtain ⟨Cc₁, hCc₁, hclass₁⟩ := actual_nonfloor_class_from_raw_moments_sub16799 F.modulus ⊤ le_top
    D.N n D.e D.eps 1 2 1 D.t (1 / 2) (5 / 6) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    D.t_pos.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos
    D.kappa_pos D.cost_pos.le D.t_pos D.phase_budget D.epsilon_gap D.t_pos
    (by linarith [D.cost_pos]) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j => by have h78 := (D.slots_bounds j).2.1; linarith [D.rmin_pos])
    (fun j => by have h200 := (D.slots_bounds j).2.2; linarith [D.t_pos])
    WC hWCs hWC hWCB D.slots_sum (by norm_num) D.epsilon_small D.kappa_small
    (by linarith) (by linarith [D.cost_pos]) (by nlinarith [D.detector_budget])
    (15 * D.t) subDelta D.t D.t (2 * τ) D.t
    (by linarith [D.t_pos]) subDelta_pos.le subDelta_le_eighth D.t_pos D.t_pos (by linarith) counts_1
  let Cc : ℝ := max Cc₀ Cc₁
  have hCc : 0 < Cc := hCc₀.trans_le (le_max_left _ _)
  obtain ⟨Cp, hCp, hprofile⟩ := actual_common_cube_aggregate_norm F.W F.W 1 2 1 2
    (by norm_num) (by norm_num) F.complex_support F.complex_support
  have hell'_pos (j : Fin D.N) : 0 < ell' j := mul_pos (by norm_num) (D.slots_bounds j).1
  have hell'_sum : ∑ j, ell' j = 20033 / 120000 := by
    dsimp [ell']; rw [← Finset.mul_sum, D.slots_sum]; norm_num
  obtain ⟨Cn, hCn, hnormer⟩ := ProbePhysical.stage1Vertex_ray_normalizer_inverse F.modulus ⊤ le_top
    F.S F.exclusions 1 2 (by norm_num) (by norm_num) ell' hell'_pos hell'_sum
    (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact) (fun _ => F.support)
    (fun _ y => (F.bounded y).1) (fun _ => F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t / 8) (div_pos D.t_pos (by norm_num))
  obtain ⟨Cd, hCd, hdyad⟩ := canonical_dyad_cost (D.t / 8) (div_pos D.t_pos (by norm_num))
  let m : ℕ := ⌊(49 / 100 : ℝ) / D.e⌋₊
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound D.t : ℝ) ^ D.N + 1
  have hcardCost : 0 < cardCost := by dsimp [cardCost]; positivity
  refine ⟨Cd * (n + 1 : ℕ) * (m + 1 : ℕ) * (Cp * cardCost * Cc * Cn), by positivity, ?_⟩
  intro η
  have hcond_56 : (97813 / 120198 : ℝ) + D.t + 2 * D.t ≤ 5 / 6 := by linarith [D.t_small]
  filter_upwards [stage1Vertex_scale_tendsto.eventually (hclass₀ η),
    stage1Vertex_scale_tendsto.eventually (hclass₁ η),
    stage1Vertex_scale_tendsto.eventually (sourceDyad_geometry_eventually (1 / 200) (5 / 6) D.t
      ((97813 / 120198 : ℝ) + D.t) (by norm_num) (by norm_num) D.t_pos hcond_56),
    stage1Vertex_scale_tendsto.eventually (HeckeDyadic.constant_absorbed_eventually (3 * (n : ℝ) + 1) τ hτ),
    stage1Vertex_scale_tendsto.eventually (source_cube_height_eventually τ hτ),
    hnormer, eventually_ge_atTop (1 : ℝ)] with Z hcl₀ hcl₁ hgeo hnheight hZ' hn hZ
  dsimp only at hn ⊢
  intro C0 hC0 hmom₀ hmom₁ rows hrows idx grid hlabels hnext hcurrent
  refine ⟨hn.1, ?_⟩
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  let Z' : ℝ := Z ^ (20033 / 20000 : ℝ)
  have hZ'p : 0 < Z' := Real.rpow_pos_of_pos hZp _
  let Yp : Fin D.N → ℝ := fun j => Z ^ (ell' j)
  let T : Fin D.N → Finset HeckeIdealSeries.PrimeIdeal :=
    fun j => pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
  let hT := stage1VertexPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp
  let normer := sourceResidueConstant F.W F.W F.modulus *
    (Probe.principalScalar Finset.univ Z (20033 / 120000)
      (slotMass T (residueWeights (fun _ => F.w) Yp)) : ℂ)
  let CellBound : ℝ := (Cp * cardCost * Cc * Cn) * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
    Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 : ℝ)
  have hCellBound : 0 ≤ CellBound := by
    dsimp only [CellBound]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hC0) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg hZp.le _)
  let FC : Finset FreeRow → (FreeRow → ℝ) → (FreeRow → ℝ) → ℂ := fun R a H =>
    finiteCentralCubeRows F.S F.exclusions F.maximal η R T hT WC Yp F.W F.W
      (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e a H
  have hcell (k : ℕ) (_hk : k ∈ smallDyadicIndices (Z' ^ ((97813 / 120198 : ℝ) + D.t)))
      (i : ℕ) (hi : i ∈ Finset.range (n + 1)) (j : ℕ) (_hj : j ∈ Finset.range (m + 1)) :
      ‖FC (cubeBinRows (rows ∩ dyadicRows 1 k) idx grid i j)
        (fun _ => 51 / 100 + D.e * j) (fun _ => (3 * i + 1 : ℕ) * Z' ^ τ) / normer‖ ≤
        CellBound := by
    let Rk := rows ∩ dyadicRows 1 k
    let Rij := cubeBinRows Rk idx grid i j
    have hsubk : Rij ⊆ Rk := Finset.filter_subset _ _
    have hsub : Rij ⊆ rows := hsubk.trans Finset.inter_subset_left
    by_cases hne' : Rij.Nonempty
    · have hg := hgeo rows (fun u hu => ⟨(hrows u hu).1, (hrows u hu).2.1, (hrows u hu).2.2.2⟩)
        k (hne'.mono hsubk)
      obtain ⟨u0, hu0⟩ := hne'
      have hu0j : grid u0 = j := ((mem_cubeBinRows Rk idx grid i j u0).mp hu0).2.2
      have hju : j ≠ 0 := hu0j ▸ (hlabels u0 (hsub hu0)).2.2.1
      let a : ℝ := 51 / 100 + D.e * j
      have ha : 51 / 100 < a := by
        have hjp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hju
        have he0 := D.e_pos
        dsimp only [a]; nlinarith only [hjp, he0]
      have ha' : a ≤ 1 := by dsimp only [a]; simpa only [hu0j] using (hlabels u0 (hsub hu0)).2.2.2
      have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hnext' : ∀ u ∈ Rij, detectorMaximum
          (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
          (3 * (i + 1 : ℕ) * Z' ^ τ) < a + 2 * D.e := fun u hu => by
        have hh := hnext u (hsub hu)
        have hm' := (mem_cubeBinRows Rk idx grid i j u).mp hu
        dsimp only [a]; rwa [hm'.2.1, hm'.2.2] at hh
      have hcurrent' : ∀ u ∈ Rij, a ≤ detectorMaximum
          (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
          ((3 * i : ℕ) * Z' ^ τ) := fun u hu => by
        have hh := hcurrent u (hsub hu)
        have hm' := (mem_cubeBinRows Rk idx grid i j u).mp hu
        dsimp only [a]; rwa [hm'.2.1, hm'.2.2] at hh
      let d' : ℝ := sourceDyadConductor Z' D.t k
      let v' : ℝ := sourceDyadExponent Z' k
      have hrows_Rij : ∀ u ∈ Rij, u.val ≠ 1 ∧ Z' ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
          (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
          rowNorm u ≤ Z' ^ (d' - D.t) :=
        fun u hu => ⟨(hrows u (hsub hu)).1, (hrows u (hsub hu)).2.1,
          (hrows u (hsub hu)).2.2.1, hg.2.2.2.2.2 u (hsubk hu)⟩
      have hnorm_Rij : ∀ u ∈ Rij, Z' ^ v' ≤ rowNorm u ∧ rowNorm u ≤ 2 * Z' ^ v' :=
        fun u hu => hg.2.2.2.2.1 u (hsubk hu)
      have hh_le : (3 * i + 1 : ℕ) * Z' ^ τ ≤ Z' ^ (2 * τ) := by
        have hi_real : (i : ℝ) ≤ n := by exact_mod_cast hi_le
        calc _ ≤ (3 * (n : ℝ) + 1) * Z' ^ τ := by
                push_cast
                exact mul_le_mul_of_nonneg_right (by linarith only [hi_real]) (Real.rpow_nonneg hZ'p.le _)
          _ ≤ Z' ^ τ * Z' ^ τ := mul_le_mul_of_nonneg_right hnheight (Real.rpow_nonneg hZ'p.le _)
          _ = Z' ^ (2 * τ) := by rw [← Real.rpow_add hZ'p]; congr 1; ring
      let scale_a : ℝ := (Z ^ (2111 / 6000 : ℝ)) ^ (4 / 25 : ℝ) *
        Z ^ (a + 16 * D.e - 33 / 50) * (Z ^ (19249 / 40000 : ℝ)) ^ (-a - 6 * D.e)
      have hscale_pos : 0 < scale_a := by
        dsimp only [scale_a]
        exact mul_pos (mul_pos (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _)
          (Real.rpow_pos_of_pos hZp _)) (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _)
      let A_arith : ℝ := cardCost * Cc * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
        Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) / scale_a
      have hA_arith : 0 ≤ A_arith := by
        dsimp only [A_arith]
        exact div_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcardCost.le hCc.le) hC0)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hZp.le _))
          hscale_pos.le
      have harith_Rij : ∀ t : HeightSpace,
          ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z' ^ τ ∧ |t.2| ≤ (3 * i + 1 : ℕ) * Z' ^ τ) ∧
            |t.1.2| ≤ (3 * i + 1 : ℕ) * Z' ^ τ) →
          ‖cubeArithmeticSum F.S F.exclusions F.maximal η Rij T hT WC Yp a D.e t‖ ≤ A_arith := by
        intro t ht
        let z : ℂ := (17 / 50 : ℂ) + t.1.2 * Complex.I
        have hz_re : z.re = 17 / 50 := by
          dsimp only [z]; norm_num [Complex.add_re, Complex.mul_re]
        have hz_im : |z.im| ≤ Z' ^ (2 * τ) := by
          have him : z.im = t.1.2 := by
            dsimp only [z]; norm_num [Complex.add_im, Complex.mul_im]
          rw [him]; exact ht.2.trans hh_le
        let Q := physical F.modulus ⊤ (fun u : FreeRow => u.val) WC (fun _ => 2)
          (fun s => D.ell s / d') (fun _ => z) (Z' ^ d')
        let B_single : ℝ := Cc * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
          Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) / scale_a
        have hB_single : 0 ≤ B_single := by
          dsimp only [B_single]
          exact div_nonneg
            (mul_nonneg (mul_nonneg (mul_nonneg hCc.le hC0)
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hZp.le _))
            hscale_pos.le
        have hpart_c := cubeArithmeticSum_class_uniform F.S F.exclusions F.maximal η Rij T hT
          WC Yp a D.e t (Finset.univ : Finset (Fin D.N)) (Z' ^ d') ((2 * a - 1) / 2) D.t
          D.t_pos (by linarith only [ha']) (fun s => D.ell s / d') Q B_single hB_single (by
            intro bin hbin_ne
            rcases lt_or_ge d' (1 / 2) with hd'_lt | hd'_ge
            · have hmom_t := hmom₀ Rij d' a hg.2.2.1 (hg.2.2.2.1.trans (by norm_num))
                ha ha' hrows_Rij i z hz_re hz_im
              have hp_cl := hcl₀ d' hg.2.2.1 (hg.2.2.2.1.trans (by norm_num)) v' a C0
                hg.1 ha ha' hC0 Rij hrows_Rij hnorm_Rij i hi_le hnext' hcurrent' t ht hmom_t bin hbin_ne
              have hp_bound := hp_cl.2.2; dsimp only at hp_bound
              rw [stage1Vertex_cubeArithmeticSum_pool_congr F.S F.exclusions F.maximal η _ WC
                (stage1Vertex_scale_slot_eq hZp.le D.ell) _ hT a D.e t] at hp_bound
              let q := classMean (Finset.univ : Finset (Fin D.N)) ((2 * a - 1) / 2) D.t
                (fun s => D.ell s / d') bin
              let E_q : ℝ := D.t + 2 * τ + D.t +
                d' * adaptiveRowExponent (2 * a - 1) q subDelta D.ε D.t D.t D.t +
                v' * (a - 1 / 2 + 12 * D.e + D.eps * ((D.N : ℝ) + 8) - 17 / 50) +
                D.t - 2 / 75 + q / 6 + D.t / 6
              have hexp_q := stage1Vertex_nonfloor_low_dyad_exponent_bound D hε_t he_t heps_t hτ2
                (by have h1 := hg.2.2.1; linarith only [h1]) hd'_lt hg.1
                (by have ht0 := D.t_pos; dsimp only [d', v', sourceDyadConductor]; linarith only [ht0])
                (add_sub_cancel_left (sourceDyadExponent Z' k) (2 * D.t)).le
                ha ha' hp_cl.1 hp_cl.2.1
              have hscale_Z : scale_a * Z' ^ E_q ≤
                  Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) := by
                dsimp only [scale_a, Z']
                rw [← Real.rpow_mul hZp.le, ← Real.rpow_mul hZp.le, ← Real.rpow_mul hZp.le,
                  ← Real.rpow_add hZp, ← Real.rpow_add hZp, ← Real.rpow_add hZp]
                exact Real.rpow_le_rpow_of_exponent_le hZ (by dsimp only [E_q]; linarith only [hexp_q])
              have hdiv : Z' ^ E_q ≤
                  Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) / scale_a :=
                (le_div_iff₀ hscale_pos).mpr (by rwa [mul_comm])
              apply hp_bound.trans; dsimp only [B_single]; rw [mul_div_assoc]
              exact mul_le_mul
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (le_max_left Cc₀ Cc₁) hC0)
                  (Real.rpow_nonneg (Nat.cast_nonneg _) _))
                hdiv (Real.rpow_nonneg hZ'p.le _)
                (mul_nonneg (mul_nonneg hCc.le hC0) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
            · have hmom_t := hmom₁ Rij d' a hd'_ge hg.2.2.2.1 ha ha' hrows_Rij i z hz_re hz_im
              have hp_cl := hcl₁ d' hd'_ge hg.2.2.2.1 v' a C0
                hg.1 ha ha' hC0 Rij hrows_Rij hnorm_Rij i hi_le hnext' hcurrent' t ht hmom_t bin hbin_ne
              have hp_bound := hp_cl.2.2; dsimp only at hp_bound
              rw [stage1Vertex_cubeArithmeticSum_pool_congr F.S F.exclusions F.maximal η _ WC
                (stage1Vertex_scale_slot_eq hZp.le D.ell) _ hT a D.e t] at hp_bound
              let q := classMean (Finset.univ : Finset (Fin D.N)) ((2 * a - 1) / 2) D.t
                (fun s => D.ell s / d') bin
              let E_q : ℝ := D.t + 2 * τ + D.t +
                d' * adaptiveRowExponentSub16799 (2 * a - 1) q subDelta D.ε (15 * D.t) D.t D.t +
                v' * (a - 1 / 2 + 12 * D.e + D.eps * ((D.N : ℝ) + 8) - 17 / 50) +
                D.t - 2 / 75 + q / 6 + D.t / 6
              have hexp_q := stage1Vertex_nonfloor_high_dyad_exponent_bound D ht_le hε_t he_t heps_t hτ2
                hd'_ge hg.2.2.2.1 hg.1 hg.2.1
                (add_sub_cancel_left (sourceDyadExponent Z' k) (2 * D.t)).le
                ha ha' hp_cl.1 hp_cl.2.1
              have hscale_Z : scale_a * Z' ^ E_q ≤
                  Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) := by
                dsimp only [scale_a, Z']
                rw [← Real.rpow_mul hZp.le, ← Real.rpow_mul hZp.le, ← Real.rpow_mul hZp.le,
                  ← Real.rpow_add hZp, ← Real.rpow_add hZp, ← Real.rpow_add hZp]
                exact Real.rpow_le_rpow_of_exponent_le hZ (by dsimp only [E_q]; linarith only [hexp_q])
              have hdiv : Z' ^ E_q ≤
                  Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) / scale_a :=
                (le_div_iff₀ hscale_pos).mpr (by rwa [mul_comm])
              apply hp_bound.trans; dsimp only [B_single]; rw [mul_div_assoc]
              exact mul_le_mul
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (le_max_right Cc₀ Cc₁) hC0)
                  (Real.rpow_nonneg (Nat.cast_nonneg _) _))
                hdiv (Real.rpow_nonneg hZ'p.le _)
                (mul_nonneg (mul_nonneg hCc.le hC0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
        simp only [Finset.card_univ, Fintype.card_fin] at hpart_c
        apply hpart_c.trans; dsimp only [B_single, A_arith, cardCost]
        calc _ ≤ ((HeckeDetectorClassBudget.alphabetBound D.t : ℝ) ^ D.N + 1) *
                (Cc * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
                  Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) / scale_a) :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hB_single
          _ = _ := by ring
      have hheight : (3 * i + 1 : ℕ) * Z' ^ τ ≤ (3 * i + 2 : ℕ) * Z' ^ τ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show 3 * i + 1 ≤ 3 * i + 2 by omega))
          (Real.rpow_nonneg hZ'p.le _)
      have hp_int := hprofile D.e a (Z' ^ τ) ((3 * i + 1 : ℕ) * Z' ^ τ) i
        D.e_pos D.e_small ha.le ha' hZ'.2 hheight F.S F.exclusions F.maximal F.first
        η Rij (fun u hu => (hrows_Rij u hu).1) T hT (rayCubeFamily F.modulus ⊤ le_top) hnext'
        WC Yp (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z
        (Real.rpow_pos_of_pos hZp _) (Real.rpow_pos_of_pos hZp _) hZp A_arith hA_arith harith_Rij
      dsimp only [FC]
      rw [div_eq_mul_inv, norm_mul]
      have hm_int := mul_le_mul hp_int hn.2 (norm_nonneg _)
        (mul_nonneg (mul_nonneg hCp.le hscale_pos.le) hA_arith)
      have hprod_eq : Cp * scale_a * A_arith * (Cn * Z ^ (D.t / 8)) = CellBound := by
        dsimp only [A_arith, CellBound]
        have h1 : scale_a * (cardCost * Cc * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
            Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) / scale_a) =
          cardCost * Cc * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
            Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) :=
          mul_div_cancel₀ _ hscale_pos.ne'
        calc Cp * scale_a * (cardCost * Cc * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
                Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) / scale_a) *
                (Cn * Z ^ (D.t / 8))
            = Cp * (scale_a * (cardCost * Cc * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
                Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) / scale_a)) *
                (Cn * Z ^ (D.t / 8)) := by ring
          _ = (Cp * cardCost * Cc * Cn) * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
                (Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 - D.t / 8 : ℝ) * Z ^ (D.t / 8)) := by
              rw [h1]; ring
          _ = (Cp * cardCost * Cc * Cn) * C0 * (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
                Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 : ℝ) := by
              rw [← Real.rpow_add hZp]; congr 2; ring
      exact hm_int.trans_eq hprod_eq
    · have he_empty : Rij = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [FC, show cubeBinRows (rows ∩ dyadicRows 1 k) idx grid i j = ∅ from he_empty,
        finiteCentralCubeRows, Finset.sum_empty, zero_div, norm_zero] using hCellBound
  have hpartition : FC rows (fun u => 51 / 100 + D.e * grid u)
      (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ) =
      ∑ k ∈ smallDyadicIndices (Z' ^ ((97813 / 120198 : ℝ) + D.t)),
        FC (rows ∩ dyadicRows 1 k) (fun u => 51 / 100 + D.e * grid u)
          (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ) := by
    unfold FC finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu => ⟨(hrows u hu).1, (hrows u hu).2.2.2⟩) _
  change ‖FC rows (fun u => 51 / 100 + D.e * grid u)
    (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ) / normer‖ ≤ _
  rw [hpartition, Finset.sum_div]
  have hdyad_card : ((smallDyadicIndices (Z' ^ ((97813 / 120198 : ℝ) + D.t))).card : ℝ) ≤
      Cd * Z ^ (D.t / 8) := by
    have htsm := D.t_small
    dsimp only [Z']; rw [stage1Vertex_scale_high_cutoff hZp.le]
    exact hdyad Z ((97813 / 120000 : ℝ) + (20033 / 20000 : ℝ) * D.t) hZ (by linarith only [htsm])
  calc _ ≤ ∑ _k ∈ smallDyadicIndices (Z' ^ ((97813 / 120198 : ℝ) + D.t)),
          (n + 1 : ℕ) * (m + 1 : ℕ) * CellBound := by
        apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        have hpart_b := finiteCentralCubeRows_bin_partition F.S F.exclusions F.maximal η
          (rows ∩ dyadicRows 1 k) T hT WC Yp F.W F.W (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ))
          Z D.e (Z' ^ τ) idx grid n m
          (fun u hu => ⟨(hlabels u (Finset.mem_inter.mp hu).1).1,
            (hlabels u (Finset.mem_inter.mp hu).1).2.1⟩)
        dsimp only [FC]; rw [hpart_b, Finset.sum_div]
        apply (norm_sum_le _ _).trans
        calc _ ≤ ∑ _i ∈ Finset.range (n + 1), ∑ _j ∈ Finset.range (m + 1), CellBound := by
              apply Finset.sum_le_sum; intro i hi; rw [Finset.sum_div]
              exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hcell k hk i hi j hj)
          _ = _ := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ = ((smallDyadicIndices (Z' ^ ((97813 / 120198 : ℝ) + D.t))).card : ℝ) *
          ((n + 1 : ℕ) * (m + 1 : ℕ) * CellBound) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cd * Z ^ (D.t / 8)) * ((n + 1 : ℕ) * (m + 1 : ℕ) * CellBound) :=
        mul_le_mul_of_nonneg_right hdyad_card
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hCellBound)
    _ = _ := by
        dsimp only [CellBound]
        calc _ = Cd * (n + 1 : ℕ) * (m + 1 : ℕ) * (Cp * cardCost * Cc * Cn) * C0 *
                (η.modulus.absNorm : ℝ) ^ (2 * D.eps) *
                (Z ^ (D.t / 8) * Z ^ (268847 / 1440000 - 1 / 200000 - D.t / 8 : ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add hZp]; congr 2; ring

/-! ### Piece 6: Unconditional Stage-1 common-probe contract at `139989 / 160000` -/

def stage1VertexProbe (D : HighData subDelta) (F : SourceData D) (η : Character) (Z : ℝ) : ℂ :=
  let ell' : Fin D.N → ℝ := fun j => (20033 / 20000 : ℝ) * D.ell j
  let Yp : Fin D.N → ℝ := fun j => Z ^ (ell' j)
  let T : Fin D.N → Finset HeckeIdealSeries.PrimeIdeal :=
    fun j => pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
  let normer := sourceResidueConstant F.W F.W F.modulus *
    (Probe.principalScalar Finset.univ Z (20033 / 120000)
      (slotMass T (residueWeights (fun _ => F.w) Yp)) : ℂ)
  compensatedPhysicalProbe η (calibrationForSet F.S F.maximal) F.W F.W
    (fun j => canonicalSlotSupport (T j)) (fun _ y => (F.w y : ℂ)) Yp
    (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z / normer

/-- **Unconditional Stage-1 true-vertex common-probe theorem (`139989 / 160000`):** whenever
`139989 / 160000 < β`, there exist fixed margins `0 < loss < β - 139989 / 160000` and `0 < σ`
such that for every character `η`, the excluded-prime character `χ = η.excludePrimes F.S`,
correction `H = sourceCorrection η F.S`, and normalized detector `J = stage1VertexProbe D F η`
satisfy both `J = O(Z^{268847 / 1440000 + loss})` and
`J - signal χ H (-495527 / 720000) = O(Z^{β - 495527 / 720000 - σ})`. -/
theorem exists_stage1Vertex_common_probe (hβ : (139989 / 160000 : ℝ) < HeckeZeroSupremum.beta) :
    ∃ loss σ : ℝ, 0 < loss ∧ loss < HeckeZeroSupremum.beta - 139989 / 160000 ∧ 0 < σ ∧
      ∀ η : Character, ∃ (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
        (∀ I, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧
        AnalyticOnNhd ℂ H {s : ℂ | 43 / 50 < s.re} ∧
        (∀ s : ℂ, 43 / 50 < s.re → ‖H s - 1‖ ≤ 1 / 2) ∧
        J =O[atTop] (fun Z : ℝ => Z ^ (268847 / 1440000 + loss)) ∧
        (fun Z => J Z - HeckeSignal.signal χ H (-495527 / 720000) Z) =O[atTop]
          (fun Z : ℝ => Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 - σ)) := by
  obtain ⟨D, ht_le_min, hfine, hε_t, he_t, heps_t, he_ell⟩ := exists_stage1Vertex_high_data_fine
  obtain ⟨D_dual, emb, ht_eq, hde_dual, _hdε_dual, h2000_eps_d, h2000_e_d, hfine_d, hemb⟩ :=
    exists_dual_high_data_explicit D ht_le_min hfine
  obtain ⟨F_dual⟩ := exists_source_data D_dual
  let F : SourceData D := transferSourceDataUp F_dual hde_dual
  obtain ⟨counts_0⟩ := source_count_parameters F
  obtain ⟨counts_1⟩ := exists_count_parameters_sub16799 F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x => (F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x => (F.bounded x).2) (15 * D.t) (by linarith [D.t_pos])
  have hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta := by linarith only [hβ]
  obtain ⟨τ, hτ, hτd, hτcost, hτt, hτ2, hτeps, hsource⟩ :=
    stage1_source_moments_combined hβ51 D D_dual ht_eq hfine h2000_eps_d h2000_e_d hfine_d
      emb hemb F_dual F rfl rfl counts_0 counts_1
  obtain ⟨n, hn_pos, hwidth⟩ := exists_source_cube_bin_number D.e D.e_pos
  let ell' : Fin D.N → ℝ := fun j => (20033 / 20000 : ℝ) * D.ell j
  let ellMin' : ℝ := (20033 / 20000 : ℝ) * ((7 / 8 : ℝ) * D.rmin)
  have hell'_pos (j : Fin D.N) : 0 < ell' j := mul_pos (by norm_num) (D.slots_bounds j).1
  have hell'_min (j : Fin D.N) : ellMin' ≤ ell' j :=
    mul_le_mul_of_nonneg_left (D.slots_bounds j).2.1 (by norm_num)
  have hell'_inj : Function.Injective ell' :=
    fun i j hij => D.slots_injective (mul_left_cancel₀ (by norm_num : (20033 / 20000 : ℝ) ≠ 0) hij)
  have hell'_sum : ∑ j, ell' j = 20033 / 120000 := by
    dsimp [ell']; rw [← Finset.mul_sum, D.slots_sum]; norm_num
  have hmin'_pos : 0 < ellMin' := by dsimp [ellMin']; have := D.rmin_pos; positivity
  let loss : ℝ := (HeckeZeroSupremum.beta - 139989 / 160000) / 2
  let σ : ℝ := min (1 / 200000) ((7 / 16 : ℝ) * D.rmin)
  have hloss : 0 < loss := by dsimp [loss]; linarith
  have hloss_lt : loss < HeckeZeroSupremum.beta - 139989 / 160000 := by dsimp [loss]; linarith
  have hσ : 0 < σ := lt_min (by norm_num) (mul_pos (by norm_num) D.rmin_pos)
  have hσ_num : σ ≤ 1 / 200000 := min_le_left _ _
  have hσ_rmin : σ ≤ (7 / 16 : ℝ) * D.rmin := min_le_right _ _
  have hfirst14 : FirstTail (1 / 4) F.S := F.first.mono_parameter (by linarith [D.e_small])
  obtain ⟨Cs, hCs, hsmall_tail⟩ := stage1Vertex_small_physical_tail D.N D.e 1 2 1
    D.e_pos D.e_small (by norm_num) (by norm_num) (by norm_num) hβ.le
    F.S F.exclusions F.maximal hfirst14 F.W F.W 1 2 1 2
    (by norm_num) (by norm_num) F.complex_support F.complex_support
  obtain ⟨Cl, hCl, hlarge_tail⟩ := stage1Vertex_large_physical_tail D.N 1 2 1
    ((20033 / 20000 : ℝ) * D.t) (mul_pos (by norm_num) D.t_pos)
    (by norm_num) (by norm_num) (by norm_num) F.S F.exclusions F.maximal hfirst14
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
  obtain ⟨Cc, hCc, hcube⟩ := stage1Vertex_finite_cube_saving
    (ι := RayQuotient.Characters F.modulus ⊤) D.N ((20033 / 20000 : ℝ) * τ) 2
    ((20033 / 20000 : ℝ) * D.t) 1 D.e (mul_pos (by norm_num) hτ) (by norm_num)
    (by linarith [D.t_small]) (by norm_num) D.e_pos D.e_small
    F.S F.exclusions F.maximal F.first F.W F.W 1 2 1 2
    (by norm_num) (by norm_num) F.complex_support F.complex_support
  obtain ⟨Cf, hCf, hfloor⟩ := stage1Vertex_floor_rows_saving D he_t heps_t F n τ hτ hτcost hτeps
  obtain ⟨Cnf, hCnf, hnonfloor⟩ := stage1Vertex_nonfloor_rows_saving D
    (ht_le_min.trans (min_le_left _ _)) hε_t he_t heps_t F counts_0 counts_1 n τ
    hτ hτd hτcost hτt hτ2 hτeps
  obtain ⟨Cn, hCn, hnormer⟩ := ProbePhysical.stage1Vertex_ray_normalizer_inverse F.modulus ⊤ le_top
    F.S F.exclusions 1 2 (by norm_num) (by norm_num) ell' hell'_pos hell'_sum
    (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact) (fun _ => F.support)
    (fun _ y => (F.bounded y).1) (fun _ => F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t / 8) (div_pos D.t_pos (by norm_num))
  have hlow_all := ProbePhysical.stage1Vertex_normalized_compensatedPhysicalProbe_low F.modulus ⊤ le_top
    F.S F.exclusions F.maximal 1 2 1 loss (by norm_num) (by norm_num) hloss
    ell' hell'_pos hell'_inj hell'_sum (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact)
    (fun _ => F.support) (fun _ => F.bounded) (fun _ => F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
  refine ⟨loss, σ, hloss, hloss_lt, hσ, ?_⟩
  intro η
  have hH_diff := PrincipalSignalComparison.sub_sourceCorrection_differentiable η F.S F.exclusions
  have hH_bnd := PrincipalSignalComparison.sub_sourceCorrection_bound η F.S F.exclusions
  obtain ⟨Clow, hClow, hlow⟩ := hlow_all η
  obtain ⟨Cp, hCp, hprinc⟩ :=
    ProbePrincipalNormalized.stage1Vertex_actual_ray_principal_comparison
      F.modulus ⊤ le_top η F.S F.exclusions 1 2 1 ellMin' (by norm_num) (by norm_num)
      (by norm_num) hmin'_pos ell' hell'_min hell'_inj hell'_sum
      (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact) (fun _ => F.support)
      (fun _ => F.bounded) (fun _ => F.nonzero)
      F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
      F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
      D.e (D.t / 8) D.e_pos (by linarith [he_t, D.t_small]) (div_pos D.t_pos (by norm_num))
      (by linarith [D.e_pos]) (by linarith [HeckeZeroSupremum.beta_le_one, D.e_small])
  obtain ⟨Cm, hCm, hmom_η⟩ := hsource η
  refine ⟨η.excludePrimes F.S F.exclusions.prime, sourceCorrection η F.S, stage1VertexProbe D F η,
    excludePrimes_mask η F.S F.exclusions.prime,
    hH_diff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re),
    hH_bnd, ?_, ?_⟩
  · apply isBigO_rpow_of_eventual_norm_bound
    exact ⟨Clow, hClow, hlow.mono fun Z h => h.2⟩
  · apply isBigO_rpow_of_eventual_norm_bound
    let Qη : ℝ := (η.modulus.absNorm : ℝ)
    let Ctot : ℝ := Cn * ((Cs + Cl) * Qη ^ (1 / 4 : ℝ) + Cc * Qη ^ 2) +
      2 * Cp + Cf * Qη ^ (2 * D.eps) + Cnf * Cm * Qη ^ (2 * D.eps) + 1
    refine ⟨Ctot, by dsimp [Ctot]; positivity, ?_⟩
    filter_upwards [hnormer, hprinc, hfloor η, hnonfloor η,
      stage1Vertex_scale_tendsto.eventually hmom_η,
      stage1Vertex_scale_tendsto.eventually (source_cube_height_eventually τ hτ),
      power_pool_tuples_eventually_injective (RayQuotient.identityClass F.modulus ⊤) F.S
        (fun _ : Fin D.N => (1 : ℝ)) (fun _ => (2 : ℝ)) ell'
        (fun _ => by norm_num) (fun _ => by norm_num) hell'_inj,
      eventually_ge_atTop (1 : ℝ)] with Z hn hpr hf hnf hmomZ hZ' hdis hZ
    dsimp only at hn hpr ⊢
    have hZp : 0 < Z := zero_lt_one.trans_le hZ
    let Z' : ℝ := Z ^ (20033 / 20000 : ℝ)
    let Yp : Fin D.N → ℝ := fun j => Z ^ (ell' j)
    let T : Fin D.N → Finset HeckeIdealSeries.PrimeIdeal :=
      fun j => pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
    let hT := stage1VertexPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp
    let WC : Fin D.N → ℝ → ℂ := fun _ y => (F.w y : ℂ)
    let normer := sourceResidueConstant F.W F.W F.modulus *
      (Probe.principalScalar Finset.univ Z (20033 / 120000)
        (slotMass T (residueWeights (fun _ => F.w) Yp)) : ℂ)
    let L : ℝ := Z ^ (20033 / 2000000 : ℝ)
    let U_cut : ℝ := Z ^ ((97813 / 120000 : ℝ) + (20033 / 20000 : ℝ) * D.t)
    have hL_eq : Z' ^ (1 / 100 : ℝ) = L := stage1Vertex_scale_low_cutoff hZp.le
    have hU_eq : Z' ^ ((97813 / 120198 : ℝ) + D.t) = U_cut := stage1Vertex_scale_high_cutoff hZp.le
    have hWS (j : Fin D.N) : Function.support (WC j) ⊆ Icc 1 2 := by
      intro y hy; apply Ioo_subset_Icc_self (F.support _); intro hh
      exact hy (by dsimp [WC]; rw [hh]; simp)
    have hWCB (j : Fin D.N) (y : ℝ) : ‖WC j y‖ ≤ 1 := by
      simpa only [WC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (F.bounded y).1]
        using (F.bounded y).2
    have hpool (j : Fin D.N) (P : HeckeIdealSeries.PrimeIdeal) (hP : P ∈ T j) :
        (P.val.absNorm : ℝ) ≤ 2 * Z ^ (ell' j) := by
      have hh := (pool_norm_bounds (RayQuotient.identityClass F.modulus ⊤) F.S
        (by norm_num) (by norm_num) (Real.rpow_pos_of_pos hZp _) P hP).2
      simpa only [mul_comm] using hh
    obtain ⟨idx, grid, hbins⟩ := exists_source_cube_bins D.e (Z' ^ τ) D.e_pos hZ'.2
      n hn_pos hwidth F.S F.exclusions.prime η (rayCubeFamily F.modulus ⊤ le_top)
    let R_band := rowBand L U_cut
    have hdec := canonical_physical_probe_partition F.S F.exclusions F.maximal η T
      (fun j P hP => outside_prime_supported F.S F.exclusions.bad P (hT j P hP)) WC Yp
      F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
      (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z L U_cut
      (Real.rpow_pos_of_pos hZp _) (Real.rpow_pos_of_pos hZp _) hZp
      (Real.one_le_rpow hZ (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [D.t_pos]))
    have hs_val := hsmall_tail η Z hZ T hT hdis ell' (fun j => (hell'_pos j).le)
      hell'_sum WC hWS hWCB
    have hl_val := hlarge_tail η Z hZ T hT hdis ell' (fun j => (hell'_pos j).le)
      hell'_sum WC hWS hWCB
    have hsmall_sum : (∑ k ∈ smallDyadicIndices L, finitePhysicalRows F.S F.maximal η
        (smallDyadicRows L k) T WC Yp F.W F.W (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z) =
        finitePhysicalRows F.S F.maximal η (rowBand 1 L) T WC Yp F.W F.W
          (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z :=
      (sum_small_dyadicRows L (physicalRowValue F.S F.maximal η T WC Yp F.W F.W
        (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z)).symm
    have hcube_val := hcube η Z hZ R_band
      (fun u hu => ⟨(mem_rowBand.mp hu).1, (mem_rowBand.mp hu).2.2.le⟩)
      T hT hdis ell' hell'_sum hpool WC hWCB
      (fun u => 51 / 100 + D.e * grid u) (fun _ => Z' ^ τ)
      (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ) idx (rayCubeFamily F.modulus ⊤ le_top)
      (fun u _ => by
        rcases hbins u with ⟨_, _, _, ha0, ha1, hBH, _hbuf, _, _, hnext, _⟩
        have hτ_eq : Z ^ ((20033 / 20000 : ℝ) * τ) = Z' ^ τ := Real.rpow_mul hZp.le _ _
        refine ⟨ha0, ha1, hZ'.2, hτ_eq.le.trans hBH, ?_, hnext⟩
        have hZ'p : 0 < Z' := Real.rpow_pos_of_pos hZp _
        have : 0 ≤ Z' ^ τ := Real.rpow_nonneg hZ'p.le _
        linarith)
    let P_pool := principalPhysicalPool η F.S T WC Yp F.W F.W
      (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z
    let C_band := finiteCentralCubeRows F.S F.exclusions F.maximal η R_band T hT WC Yp
      F.W F.W (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e
      (fun u => 51 / 100 + D.e * grid u) (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ)
    let C_fl := finiteCentralCubeRows F.S F.exclusions F.maximal η
      (supportedFloorRows F.S F.maximal R_band grid) T hT WC Yp
      F.W F.W (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e
      (fun _ => 51 / 100) (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ)
    let C_nf := finiteCentralCubeRows F.S F.exclusions F.maximal η
      (supportedNonfloorRows F.S F.maximal R_band grid) T hT WC Yp
      F.W F.W (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e
      (fun u => 51 / 100 + D.e * grid u) (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ)
    have hsplit : C_band = C_fl + C_nf :=
      finiteCentralCubeRows_supported_split F.S F.exclusions F.maximal η R_band T hT WC Yp
        F.W F.W (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z D.e grid
        (fun u => (3 * idx u + 1 : ℕ) * Z' ^ τ)
    have hfl_rows : ∀ u ∈ supportedFloorRows F.S F.maximal R_band grid,
        u.val ≠ 1 ∧ Z' ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z' ^ ((97813 / 120198 : ℝ) + D.t) := fun u hu => by
      rcases (mem_supportedFloorRows F.S F.maximal R_band grid u).mp hu with ⟨hur, hcal, _⟩
      have hm := mem_rowBand.mp hur; rw [hL_eq, hU_eq]; exact ⟨hm.1, hm.2.1, hcal, hm.2.2.le⟩
    have hfl_val := (hf (supportedFloorRows F.S F.maximal R_band grid) hfl_rows idx
      (fun u _ => (hbins u).2.1)
      (fun u hu => by
        have hg := ((mem_supportedFloorRows F.S F.maximal R_band grid u).mp hu).2.2
        simpa only [hg, Nat.cast_zero, mul_zero, add_zero] using (hbins u).2.2.2.2.2.2.2.2.2.1)).2
    have hnf_rows : ∀ u ∈ supportedNonfloorRows F.S F.maximal R_band grid,
        u.val ≠ 1 ∧ Z' ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z' ^ ((97813 / 120198 : ℝ) + D.t) := fun u hu => by
      rcases (mem_supportedNonfloorRows F.S F.maximal R_band grid u).mp hu with ⟨hur, hcal, _⟩
      have hm := mem_rowBand.mp hur; rw [hL_eq, hU_eq]; exact ⟨hm.1, hm.2.1, hcal, hm.2.2.le⟩
    have hnf_val := (hnf Cm hCm.le hmomZ.1 hmomZ.2 (supportedNonfloorRows F.S F.maximal R_band grid)
      hnf_rows idx grid
      (fun u hu => ⟨(hbins u).2.1, (hbins u).2.2.1,
        ((mem_supportedNonfloorRows F.S F.maximal R_band grid u).mp hu).2.2,
        (hbins u).2.2.2.2.1⟩)
      (fun u _ => (hbins u).2.2.2.2.2.2.2.2.2.1)
      (fun u _ => by simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (hbins u).2.2.2.2.2.2.2.1)).2
    let E_target : ℝ := Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 - σ)
    have hE_target : 0 ≤ E_target := Real.rpow_nonneg hZp.le _
    have hexp_s : Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 - 7 / 100 + 8 * D.e) *
        Z ^ (D.t / 8) ≤ E_target := by
      rw [← Real.rpow_add hZp]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith [he_t, D.t_small, hσ_num])
    have hexp_neg1 : Z ^ (-1 : ℝ) * Z ^ (D.t / 8) ≤ E_target := by
      rw [← Real.rpow_add hZp]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith [D.t_small, hβ, hσ_num])
    have hexp_p1 : Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 - 1 / 1200 + D.t / 8) ≤ E_target :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith [D.t_small, hσ_num])
    have hexp_p2 : Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 + D.e - (43 / 50) * ellMin') ≤
        E_target := by
      apply Real.rpow_le_rpow_of_exponent_le hZ; dsimp [ellMin']
      have := D.rmin_pos; linarith [he_ell, hσ_rmin]
    have hexp_fl : Z ^ (268847 / 1440000 - 1 / 250 : ℝ) ≤ E_target :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hβ, hσ_num])
    have hexp_nf : Z ^ (268847 / 1440000 - 1 / 200000 : ℝ) ≤ E_target :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hβ, hσ_num])
    have hrem_raw : ‖compensatedPhysicalProbe η (calibrationForSet F.S F.maximal) F.W F.W
          (fun j => canonicalSlotSupport (T j)) WC Yp
          (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z - P_pool - C_band‖ ≤
        Cs * Qη ^ (1 / 4 : ℝ) * Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 - 7 / 100 + 8 * D.e) +
          Cl * Qη ^ (1 / 4 : ℝ) * Z ^ (-1 : ℝ) + Cc * Qη ^ 2 * Z ^ (-1 : ℝ) := by
      rw [hsmall_sum] at hdec
      have hdecomp : compensatedPhysicalProbe η (calibrationForSet F.S F.maximal) F.W F.W
          (fun j => canonicalSlotSupport (T j)) WC Yp
          (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z - P_pool - C_band =
        (finitePhysicalRows F.S F.maximal η (rowBand 1 L) T WC Yp F.W F.W
            (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z +
          ∑' k : ℕ, finitePhysicalRows F.S F.maximal η (dyadicRows U_cut k) T WC Yp F.W F.W
            (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z) +
        (finitePhysicalRows F.S F.maximal η R_band T WC Yp F.W F.W
            (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z - C_band) := by
        rw [hdec]; dsimp [P_pool, principalPhysicalPool, R_band]; ring
      rw [hdecomp]
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans
          (add_le_add hs_val ((norm_tsum_le_tsum_norm hl_val.1.norm).trans hl_val.2)))
        hcube_val)
    have hrem_norm : ‖(compensatedPhysicalProbe η (calibrationForSet F.S F.maximal) F.W F.W
          (fun j => canonicalSlotSupport (T j)) WC Yp
          (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z - P_pool - C_band) / normer‖ ≤
        Cn * ((Cs + Cl) * Qη ^ (1 / 4 : ℝ) + Cc * Qη ^ 2) * E_target := by
      rw [div_eq_mul_inv, norm_mul]
      calc _ ≤ (Cs * Qη ^ (1 / 4 : ℝ) *
                Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 - 7 / 100 + 8 * D.e) +
              Cl * Qη ^ (1 / 4 : ℝ) * Z ^ (-1 : ℝ) + Cc * Qη ^ 2 * Z ^ (-1 : ℝ)) *
              (Cn * Z ^ (D.t / 8)) :=
            mul_le_mul hrem_raw hn.2 (norm_nonneg _) (by positivity)
        _ = Cn * Cs * Qη ^ (1 / 4 : ℝ) *
              (Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 - 7 / 100 + 8 * D.e) * Z ^ (D.t / 8)) +
            Cn * Cl * Qη ^ (1 / 4 : ℝ) * (Z ^ (-1 : ℝ) * Z ^ (D.t / 8)) +
            Cn * Cc * Qη ^ 2 * (Z ^ (-1 : ℝ) * Z ^ (D.t / 8)) := by ring
        _ ≤ Cn * Cs * Qη ^ (1 / 4 : ℝ) * E_target +
            Cn * Cl * Qη ^ (1 / 4 : ℝ) * E_target +
            Cn * Cc * Qη ^ 2 * E_target := by gcongr
        _ = _ := by ring
    have hpr_bound : ‖P_pool / normer -
        HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection η F.S) (-495527 / 720000) Z‖ ≤ 2 * Cp * E_target := by
      calc _ ≤ Cp * (Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 - 1 / 1200 + D.t / 8) +
              Z ^ (HeckeZeroSupremum.beta - 495527 / 720000 + D.e - (43 / 50) * ellMin')) := hpr.2
        _ ≤ Cp * (E_target + E_target) :=
            mul_le_mul_of_nonneg_left (add_le_add hexp_p1 hexp_p2) hCp.le
        _ = 2 * Cp * E_target := by ring
    have hfl_bound : ‖C_fl / normer‖ ≤ Cf * Qη ^ (2 * D.eps) * E_target :=
      hfl_val.trans (mul_le_mul_of_nonneg_left hexp_fl (by positivity))
    have hnf_bound : ‖C_nf / normer‖ ≤ Cnf * Cm * Qη ^ (2 * D.eps) * E_target :=
      hnf_val.trans (mul_le_mul_of_nonneg_left hexp_nf (by positivity))
    have hid_tot : stage1VertexProbe D F η Z -
        HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection η F.S) (-495527 / 720000) Z =
      (compensatedPhysicalProbe η (calibrationForSet F.S F.maximal) F.W F.W
          (fun j => canonicalSlotSupport (T j)) WC Yp
          (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z - P_pool - C_band) / normer +
      (P_pool / normer - HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection η F.S) (-495527 / 720000) Z) +
      (C_fl / normer + C_nf / normer) := by
      unfold stage1VertexProbe; dsimp only [ell', Yp, T, normer]; rw [hsplit]; ring
    rw [hid_tot]
    have hsum4 : ‖(compensatedPhysicalProbe η (calibrationForSet F.S F.maximal) F.W F.W
          (fun j => canonicalSlotSupport (T j)) WC Yp
          (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z - P_pool - C_band) / normer +
        (P_pool / normer - HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection η F.S) (-495527 / 720000) Z) +
        (C_fl / normer + C_nf / normer)‖ ≤
        (Cn * ((Cs + Cl) * Qη ^ (1 / 4 : ℝ) + Cc * Qη ^ 2) +
          2 * Cp + Cf * Qη ^ (2 * D.eps) + Cnf * Cm * Qη ^ (2 * D.eps)) * E_target := by
      calc _ ≤ (‖(compensatedPhysicalProbe η (calibrationForSet F.S F.maximal) F.W F.W
                (fun j => canonicalSlotSupport (T j)) WC Yp
                (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z - P_pool - C_band) / normer‖ +
              ‖P_pool / normer - HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
                (sourceCorrection η F.S) (-495527 / 720000) Z‖) +
              (‖C_fl / normer‖ + ‖C_nf / normer‖) :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
        _ ≤ (Cn * ((Cs + Cl) * Qη ^ (1 / 4 : ℝ) + Cc * Qη ^ 2) * E_target +
              2 * Cp * E_target) +
            (Cf * Qη ^ (2 * D.eps) * E_target + Cnf * Cm * Qη ^ (2 * D.eps) * E_target) :=
            add_le_add (add_le_add hrem_norm hpr_bound) (add_le_add hfl_bound hnf_bound)
        _ = _ := by ring
    exact hsum4.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hE_target)

end Stage1TrueVertexHighTransport

/-! ### Part 7: Unconditional Zero-Free Half-Plane Below `139989 / 160000` (`1 - σ₀ = 20011 / 160000`) -/

namespace Stage1TrueVertexZeroFree

open HeckeFamily HeckeZeroSupremum

/-- Unconditionally, the supremum `HeckeZeroSupremum.beta` of real parts of zeros across all Hecke
`L`-functions of `ℚ(ω)` satisfies `beta ≤ 139989 / 160000` (`< 3281 / 3750 < 16799 / 19200`). -/
theorem hecke_beta_le_stage1_vertex : HeckeZeroSupremum.beta ≤ 139989 / 160000 := by
  by_contra hn
  have hβ : (139989 / 160000 : ℝ) < HeckeZeroSupremum.beta := lt_of_not_ge hn
  obtain ⟨loss, σ, hloss, hloss_lt, hσ, hprobe⟩ :=
    Stage1TrueVertexHighTransport.exists_stage1Vertex_common_probe hβ
  set a : ℝ := max (139989 / 160000 + loss) (HeckeZeroSupremum.beta - σ)
  have ha_lt_β : a < HeckeZeroSupremum.beta :=
    max_lt (by linarith only [hloss_lt]) (by linarith only [hσ])
  have ha_gt_4350 : (43 / 50 : ℝ) < a :=
    lt_of_lt_of_le (by linarith only [hloss])
      (le_max_left (139989 / 160000 + loss) (HeckeZeroSupremum.beta - σ))
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
  have htop : HeckeSignal.signal χ H (-495527 / 720000) =O[atTop]
      (fun Z : ℝ => Z ^ (a + (-495527 / 720000))) := by
    have hmax : max (268847 / 1440000 + loss) (HeckeZeroSupremum.beta - 495527 / 720000 - σ) =
        a + (-495527 / 720000) := by
      have h1 : 268847 / 1440000 + loss = (139989 / 160000 + loss) + (-495527 / 720000) := by ring
      have h2 : HeckeZeroSupremum.beta - 495527 / 720000 - σ =
          (HeckeZeroSupremum.beta - σ) + (-495527 / 720000) := by ring
      rw [h1, h2]
      exact max_add_add_right _ _ _
    simpa only [hmax] using
      Continuation.common_signal_bound J (HeckeSignal.signal χ H (-495527 / 720000))
        (268847 / 1440000 + loss) (HeckeZeroSupremum.beta - 495527 / 720000 - σ) hJ herr
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr fun hc => hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc)
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask (by linarith only [hhalf]) hχpole,
      hz, zero_mul]
  have hHd : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re} := hH78.differentiableOn
  have hne : LFunction χ ρ ≠ 0 :=
    Continuation.nonzero_of_regularized_signal a 1 (-495527 / 720000)
      (LFunction χ) (HeckeSignal.regularL χ) (HeckeSignal.targetRegularizer χ)
      (Continuation.gaussianMultiplier H) (HeckeSignal.signal χ H (-495527 / 720000))
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (HeckeSignal.regularL_entire χ)).mono (Set.subset_univ _))
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (HeckeSignal.targetRegularizer_entire χ)).mono (Set.subset_univ _))
      (Continuation.gaussianMultiplier_analytic hHa)
      (HeckeSignal.signal_locallyIntegrable χ H hHd hb78 (-495527 / 720000))
      htop
      (HeckeSignal.signal_rapidDecayAtZero χ H hHd hb78 (-495527 / 720000))
      (fun s hs => by
        have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
        have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
        have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
        rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
          HeckeSignal.signalMellin_eq_amplitude χ H hHd hb78 (-495527 / 720000) a ha_lt_two htop hs]
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

/-- Strict numerical improvements over all previous cubic-probe benchmarks (`3281/3750`,
`16799/19200`, `40535/46328`, `20999/24000`). -/
theorem hecke_beta_lt_previous_benchmarks :
    HeckeZeroSupremum.beta ≤ 139989 / 160000 ∧
    (139989 / 160000 : ℝ) < 3281 / 3750 ∧
    (3281 / 3750 : ℝ) < 16799 / 19200 ∧
    (16799 / 19200 : ℝ) < 40535 / 46328 ∧
    (40535 / 46328 : ℝ) < 20999 / 24000 :=
  ⟨hecke_beta_le_stage1_vertex, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Every Hecke `L`-function of `ℚ(ω)` is nonzero on `Re s > 139989 / 160000` away from its pole. -/
theorem hecke_ne_zero_of_stage1_vertex_lt_re (χ : Character) (s : ℂ)
    (hs : (139989 / 160000 : ℝ) < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_beta_lt χ (hecke_beta_le_stage1_vertex.trans_lt hs) hpole

/-- Every Dirichlet `L`-function is nonzero on `Re s > 139989 / 160000` away from `(χ = 1, s = 1)`. -/
theorem dirichlet_stage1_vertex_nonzero (q : ℕ) (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : (139989 / 160000 : ℝ) < s.re) (hexc : ¬(χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  letI : NeZero q := ⟨hq⟩
  exact SubSevenEighthsZeroFree.dirichlet_ne_zero_of_hecke (by norm_num)
    hecke_ne_zero_of_stage1_vertex_lt_re χ hs hexc

end Stage1TrueVertexZeroFree

/-- Every Dirichlet `L`-function is nonzero on `Re s > 139989 / 160000` away from `(χ = 1, s = 1)`. -/
theorem DirichletCharacter.LFunction_ne_zero_of_stage1_vertex_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : (139989 / 160000 : ℝ) < s.re)
    (hpole : ¬(χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Stage1TrueVertexZeroFree.dirichlet_stage1_vertex_nonzero q (NeZero.ne q) χ s hs hpole

/-- `riemannZeta` has no zeros on the open half-plane `Re s > 139989 / 160000`. -/
theorem riemannZeta_ne_zero_of_stage1_vertex_lt_re {s : ℂ}
    (hs : (139989 / 160000 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := DirichletCharacter.LFunction_ne_zero_of_stage1_vertex_lt_re
    (1 : DirichletCharacter ℂ 1) hs (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

/-- Functional reflection `s ↦ 1 - s` transfers the `139989 / 160000` right half-plane to
nonvanishing of `riemannZeta` on `0 < Re s < 20011 / 160000`
(`= 0.12506875 > 469 / 3750 > 2401 / 19200 > 3001 / 24000`). -/
theorem riemannZeta_ne_zero_of_re_lt_stage1_vertex_left {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < (20011 / 160000 : ℝ)) : riemannZeta s ≠ 0 := by
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
  apply riemannZeta_ne_zero_of_stage1_vertex_lt_re (s := 1 - s) _ hreflect
  simp only [Complex.sub_re, Complex.one_re]
  linarith only [h1]

/-- Every zero of `riemannZeta` with `Re s > 0` lies in `[20011 / 160000, 139989 / 160000]`. -/
theorem riemannZeta_zero_mem_stage1_vertex_strip {s : ℂ}
    (h0 : 0 < s.re) (hzero : riemannZeta s = 0) :
    s.re ∈ Set.Icc (20011 / 160000 : ℝ) (139989 / 160000 : ℝ) := by
  constructor
  · exact le_of_not_gt fun hs => riemannZeta_ne_zero_of_re_lt_stage1_vertex_left h0 hs hzero
  · exact le_of_not_gt fun hs => riemannZeta_ne_zero_of_stage1_vertex_lt_re hs hzero

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

end
