import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProposition22PaperConditions
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenCompressedRetainedBoxFamily
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProposition22ErrorPaperScale
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProposition22ErrorSupport

/-!
# Unconditional paper-scale assembly of Matomäki--Teräväinen Proposition 2.2
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction

noncomputable section

/-- Exact finite decomposition asserted by Proposition 2.2, including its quantitative family and
error clauses; every piece is divisor-bounded with the fixed exponent `5` and every Type-II
(2.11) coefficient is `0` or `1`. -/
structure MTProposition22Decomposition (A : ℕ) (X epsilon : ℝ) (Y : ℕ) where
  ι : Type
  indexSet : Finset ι
  piece : ι → ArithmeticFunction ℂ
  error : ArithmeticFunction ℂ
  identity :
    mtHarmanProposition22SourceAF (mtProposition22ZNat X)
        (mtProposition22QNat X) (mtProposition22DNat X epsilon)
        (mtProposition22ENat X epsilon) Y =
      ∑ i ∈ indexSet, piece i + error
  piece_shape : ∀ i ∈ indexSet,
    MTUniformProposition22Piece 5 X (Y : ℝ) (mtLowerCutoff X)
      (mtProposition22ZReal X) (mtPaperWidth A X) epsilon (piece i)
  family_card : (indexSet.card : ℝ) ≤ Real.exp ((Real.log (Real.log X)) ^ 5)
  error_support : ∀ {n : ℕ}, error n ≠ 0 →
    (Y : ℝ) / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * (Y : ℝ)
  error_mean_square :
    ∑ n ∈ Finset.Icc 1 (8 * Y), ‖error n‖ ^ 2 ≤
      ((92224 : ℝ) * (5 : ℝ) ^ 35 + 7232) * (Y : ℝ) *
        (Real.log X) ^ (-((A : ℕ) : ℝ))

set_option maxHeartbeats 800000 in
/-- Proposition 2.2 at its literal paper cutoffs, with an explicit valid sufficiently-small range
`0 < ε ≤ 1/100`. -/
theorem eventually_nonempty_mtProposition22Decomposition
    (A : ℕ) (hA : 5 ≤ A) {epsilon : ℝ} (hepsilon0 : 0 < epsilon)
    (hepsilon : epsilon ≤ 1 / 100) :
    ∀ᶠ X : ℝ in atTop, ∀ Y : ℕ,
      X ^ (1 - epsilon / 100) < (Y : ℝ) →
      (Y : ℝ) ≤ X / 2 →
      Nonempty (MTProposition22Decomposition A X epsilon Y) := by
  have hAone : 1 ≤ A := one_le_two.trans (by omega)
  have hspare := (tendsto_rpow_atTop (div_pos hepsilon0 (by norm_num : (0 : ℝ) < 4))).eventually_ge_atTop 3
  filter_upwards [eventually_exists_mtProposition22CeilRootedSchedule A hepsilon0 hepsilon,
    eventually_sum_normSq_mtHarmanProposition22ErrorAF_le_paper A hA,
    eventually_card_mtHarmanCompressedRetainedBoxIndexSet_le_exp_log_log_fifth A,
    eventually_mtPaperWidth_depthDilation_le_prev A hAone,
    eventually_mtLogDepth_le_two_mul_log_log_cube,
    eventually_mtLogDepth_le_log,
    hspare] with X hschedule herrorX hcountX hcollarX hdepthCubeX hdepthLogX hspareX
  intro Y hYlower hYupper
  obtain ⟨hcuts, start, hdelta, hz₀, hroot, cert, _⟩ := hschedule
  let delta := mtPaperWidth A X
  let z0 := mtLowerCutoffNat X
  let z := mtProposition22ZNat X
  let Q := mtProposition22QNat X
  let D := mtProposition22DNat X epsilon
  let E := mtProposition22ENat X epsilon
  let recRoot := mtProposition22ZReal X
  let recDepth := mtMinimalGeometricDepth delta start recRoot hdelta
  let data : MTFiniteIterationSourceData recDepth :=
    MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
      z0 (mtTruncationNat X) start recRoot delta hdelta hz₀ hroot
  let maxDepth := Nat.floor (Real.log ((4 * Y : ℕ) : ℝ) / Real.log (z0 : ℝ))
  let j : Fin (recDepth + 1) := Fin.last recDepth
  let N := 4 * Y
  let endpointQ := mtPaperAlignedEndpoint z0 Q delta
  let endpointD := mtPaperAlignedEndpoint z0 D delta
  let outerQ := Q - z0
  let outerD := D - z0
  let activeQ := mtPaperAlignedActiveBlockIndices outerQ z0 Q delta
  let S := mtHarmanCompressedRetainedBoxIndexSet (outerD := outerD)
    activeQ endpointQ endpointD (E : ℝ) data maxDepth j delta N start (Y : ℝ)
  let F : MTHarmanRetainedBoxIndex outerQ outerD recDepth → ArithmeticFunction ℂ :=
    mtHarmanRetainedBoxAF endpointQ endpointD z Q D data delta
  let boundary := mtHarmanProductBoundaryErrorAF (outerQ := outerQ) (outerD := outerD)
    endpointQ endpointD z Q D (E : ℝ) data maxDepth j delta N start (Y : ℝ)
  let c := mtHarmanProposition22ErrorAF (outerD := outerD)
    endpointD z Q D E data maxDepth j Y boundary
  have hXone : 1 < X := one_lt_two.trans_le hcuts.X_two
  have hYone : 1 ≤ Y := by
    have hexponent : 0 ≤ 1 - epsilon / 100 := by linarith
    have hpowOne : 1 ≤ X ^ (1 - epsilon / 100) :=
      Real.one_le_rpow (one_le_two.trans hcuts.X_two) hexponent
    have : (1 : ℝ) < (Y : ℝ) := hpowOne.trans_lt hYlower
    exact_mod_cast this.le
  have hYsqrt : X ^ (1 / 2 : ℝ) ≤ (Y : ℝ) := by
    have hexponent : (1 / 2 : ℝ) ≤ 1 - epsilon / 100 := by linarith
    exact (Real.rpow_le_rpow_of_exponent_le
      (one_le_two.trans hcuts.X_two) hexponent).trans hYlower.le
  have hNtwoX : (N : ℝ) ≤ 2 * X := by
    dsimp [N]
    push_cast
    linarith
  have hNone : 1 ≤ N := by dsimp [N]; omega
  have hNfourX : (N : ℝ) ≤ 4 * X := hNtwoX.trans (by linarith [hcuts.X_two])
  have hmaxCube : (maxDepth : ℝ) ≤ 2 * (Real.log (Real.log X)) ^ 3 := by
    dsimp [maxDepth, z0]
    exact hdepthCubeX (4 * Y) (by omega) hNfourX
  have hmaxLog : (maxDepth : ℝ) ≤ Real.log X := by
    dsimp [maxDepth, z0]
    exact hdepthLogX (4 * Y) (by omega) hNfourX
  have hcollar : (1 + delta) ^ (maxDepth + 5) ≤
      1 + mtPaperWidth (A - 1) X := by
    dsimp [delta, maxDepth, z0]
    exact hcollarX (4 * Y)
      (Nat.floor (Real.log ((4 * Y : ℕ) : ℝ) /
        Real.log (mtLowerCutoffNat X : ℝ)) + 5) (by omega) hNfourX le_rfl
  have hdilation : ∀ R : ℕ, R ≤ maxDepth + 5 → (1 + delta) ^ R ≤ 2 := by
    intro R hR
    calc
      (1 + delta) ^ R ≤ (1 + delta) ^ (maxDepth + 5) :=
        pow_le_pow_right₀ (by linarith [hdelta]) hR
      _ ≤ 1 + mtPaperWidth (A - 1) X := hcollar
      _ ≤ 2 := by linarith [hcuts.previous_delta_le_one]
  have hz0One : 1 ≤ z0 := by
    dsimp [z0]
    exact one_le_two.trans hcuts.lower_two
  have hz0Q : z0 ≤ Q := by dsimp [z0, Q]; exact hcuts.lower_le_Q
  have hz0D : z0 ≤ D := by
    dsimp [z0, D]
    exact hcuts.lower_le_z.trans hcuts.z_le_D
  have hendpointQ : ∀ i, 2 ≤ endpointQ i := fun i => by
    dsimp [endpointQ]
    exact hcuts.lower_two.trans
      (mtPaperAlignedEndpoint_mem_Icc hz0One hz0Q hdelta.le hcuts.progress i).1
  have hendpointD : ∀ i, 2 ≤ endpointD i := fun i => by
    dsimp [endpointD]
    exact hcuts.lower_two.trans
      (mtPaperAlignedEndpoint_mem_Icc hz0One hz0D hdelta.le hcuts.progress i).1
  have hmonoQ : Monotone endpointQ := by
    dsimp [endpointQ]
    exact mtPaperAlignedEndpoint_monotone hz0One hz0Q hdelta.le hcuts.progress
  have hmonoD : Monotone endpointD := by
    dsimp [endpointD]
    exact mtPaperAlignedEndpoint_monotone hz0One hz0D hdelta.le hcuts.progress
  have hbandQ : ∀ i, mtAdjacentBlockUpperScale endpointQ i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpointQ i := by
    intro i
    exact mtPaperAlignedEndpoint_band hdelta.le i
  have hbandD : ∀ i, mtAdjacentBlockUpperScale endpointD i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpointD i := by
    intro i
    exact mtPaperAlignedEndpoint_band hdelta.le i
  have hsourceQ : primesIco z Q ⊆ primesIco (endpointQ 0) (endpointQ outerQ) := by
    intro q hq
    have hq' := mem_primesIco.mp hq
    apply mem_primesIco.mpr
    refine ⟨?_, ?_, hq'.2.2⟩
    · simpa [endpointQ, z0, z] using hcuts.lower_le_z.trans hq'.1
    · rw [show endpointQ outerQ = Q by
        dsimp [endpointQ, outerQ]
        exact mtPaperAlignedEndpoint_sub_eq hz0One hz0Q hdelta.le hcuts.progress]
      exact hq'.2.1
  have hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 (mtTruncationNat X) start delta recRoot hdelta hz₀ hroot).block := by
    dsimp [data, recDepth]
    exact ofMinimalGeometricCeilRootedSchedule_block_eq_ofMinimalGeometricSchedule_block
      z0 (mtTruncationNat X) start recRoot hdelta hz₀ hroot
  have hz0Data : data.z₀ = z0 := rfl
  have hDData : data.D = mtTruncationNat X := rfl
  change MTGridFreeDilationCertificate data A X at cert
  have hcutoff : data.cutoff j = z := by
    dsimp [data, j, z, recDepth, recRoot]
    exact MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_cutoff_last
      (mtLowerCutoffNat X) (mtTruncationNat X) start (mtProposition22ZReal X)
        (mtPaperWidth A X) hdelta hz₀ hroot
  have heScale : ∀ e : ℕ, e ≤ mtUpperAdicIndex delta data.D →
      mtUpperAdicScale delta e ≤ X ^ (epsilon / 4) := by
    intro e he
    exact (mtUpperAdicScale_lt_of_le_index hdelta hcuts.trunc_pos
      (by simpa [hDData] using he)).le.trans hcuts.trunc_small
  have hbaseSmall : ∀ e : ℕ, e ≤ mtUpperAdicIndex delta data.D →
      mtUpperAdicScale delta e * mtBaseOuterScale delta (0 : Fin 1) *
        X ^ (epsilon / 2) ≤ X ^ (1 / 2 + epsilon) := by
    intro e he
    have he' := heScale e he
    have hbase : mtBaseOuterScale delta (0 : Fin 1) ≤ X ^ (0 : ℝ) := by
      simp [mtBaseOuterScale]
      exact (inv_le_one₀ (by linarith [hdelta] : 0 < 1 + delta)).2 (by linarith [hdelta])
    have hfirst := mul_le_rpow_add_of_le (one_le_two.trans hcuts.X_two)
      (mtUpperAdicScale_pos hdelta e).le (mtBaseOuterScale_pos hdelta (0 : Fin 1)).le
      he' hbase
    have hsecond := mul_le_rpow_add_of_le (one_le_two.trans hcuts.X_two)
      (mul_nonneg (mtUpperAdicScale_pos hdelta e).le
        (mtBaseOuterScale_pos hdelta (0 : Fin 1)).le)
      (Real.rpow_nonneg (by linarith [hcuts.X_two]) _)
      hfirst (le_refl (X ^ (epsilon / 2)))
    exact hsecond.trans (Real.rpow_le_rpow_of_exponent_le
      (one_le_two.trans hcuts.X_two) (by linarith))
  have honeSmall : ∀ (i : Fin outerQ) (e : ℕ),
      e ≤ mtUpperAdicIndex delta data.D →
      mtUpperAdicScale delta e * mtOnePrimeOuterScale endpointQ i *
        X ^ (epsilon / 2) ≤ X ^ (1 / 2 + epsilon) := by
    intro i e he
    have honeQ : mtOnePrimeOuterScale endpointQ i ≤ (Q : ℝ) := by
      dsimp [mtOnePrimeOuterScale, mtAdjacentBlockLowerScale]
      have hendpoint := (mtPaperAlignedEndpoint_mem_Icc hz0One hz0Q hdelta.le
        hcuts.progress i.1).2
      have hsub : endpointQ i.1 - 1 ≤ endpointQ i.1 := Nat.sub_le _ _
      exact_mod_cast hsub.trans hendpoint
    have hone : mtOnePrimeOuterScale endpointQ i ≤ X ^ (1 / 2 + epsilon / 4) := by
      calc
        _ ≤ (Q : ℝ) := honeQ
        _ ≤ 3 * X ^ (1 / 2 : ℝ) := hcuts.Q_le_three_sqrt
        _ ≤ X ^ (epsilon / 4) * X ^ (1 / 2 : ℝ) := by gcongr
        _ = X ^ (1 / 2 + epsilon / 4) := by
          rw [← Real.rpow_add (by linarith [hcuts.X_two])]
          congr 1
          ring
    have hfirst := mul_le_rpow_add_of_le (one_le_two.trans hcuts.X_two)
      (mtUpperAdicScale_pos hdelta e).le
      (mtOnePrimeOuterScale_pos hendpointQ i).le (heScale e he) hone
    have hsecond := mul_le_rpow_add_of_le (one_le_two.trans hcuts.X_two)
      (mul_nonneg (mtUpperAdicScale_pos hdelta e).le
        (mtOnePrimeOuterScale_pos hendpointQ i).le)
      (Real.rpow_nonneg (by linarith [hcuts.X_two]) _)
      hfirst (le_refl (X ^ (epsilon / 2)))
    simpa only [show epsilon / 4 + (1 / 2 + epsilon / 4) + epsilon / 2 =
      1 / 2 + epsilon by ring] using hsecond
  have hfamilyCard : (S.card : ℝ) ≤ Real.exp ((Real.log (Real.log X)) ^ 5) := by
    have hdataDone : 1 ≤ data.D := by rw [hDData]; exact hcuts.trunc_pos
    have hdataDtwoX : (data.D : ℝ) ≤ 2 * X := by
      rw [hDData]
      exact hcuts.trunc_le_two_X
    dsimp [S, activeQ, endpointQ, endpointD, outerQ, outerD, Q, D, E, delta, N,
      recRoot, recDepth, data, maxDepth, j]
    exact hcountX (mtProposition22QNat X) (mtProposition22DNat X epsilon)
      hcuts.lower_le_Q hcuts.Q_le_X (hcuts.lower_le_z.trans hcuts.z_le_D)
      hcuts.D_le_X (mtProposition22ENat X epsilon : ℝ) start
      (mtProposition22ZReal X) hdelta hcuts.X_two hcuts.root_le_X
      _ hdataDone hdataDtwoX _ _ hmaxCube
      (4 * Y) hNone hNtwoX start (Y : ℝ)
  have hrootOne : 1 ≤ mtGeometricLevel delta start 0 := by
    have hz0OneReal : (1 : ℝ) ≤ (z0 : ℝ) := by exact_mod_cast hz0One
    exact hz0OneReal.trans hz₀
  have hz0RealLevel : mtLowerCutoff X ≤ mtGeometricLevel delta start 0 := by
    have hlowerCeil : mtLowerCutoff X ≤ (z0 : ℝ) := by
      dsimp [z0, mtLowerCutoffNat]
      exact Nat.le_ceil _
    exact hlowerCeil.trans hz₀
  have hpieceShape : ∀ idx ∈ S,
      MTUniformProposition22Piece 5 X (Y : ℝ) (mtLowerCutoff X)
        (mtProposition22ZReal X) (mtPaperWidth A X) epsilon (F idx) := by
    intro idx hidx
    have hidxFull := mtHarmanCompressedRetainedBoxIndexSet_subset
      (outerD := outerD) activeQ endpointQ endpointD (E : ℝ)
      data maxDepth j delta N start (Y : ℝ) hidx
    have hpiece := mtHarmanRetainedBox_isProposition22Piece_exactThresholds
      (X := X) (Y := (Y : ℝ)) (z0Real := mtLowerCutoff X)
      (epsilon := epsilon) (DReal := mtProposition22DReal X epsilon)
      (EReal := mtProposition22EReal X epsilon)
      z0 z0 z Q D (mtTruncationNat X) start hdelta hcuts.lower_two
      hz0Q hz0D hcuts.progress rfl hz₀ hroot data hblocks hz0Data hDData
      maxDepth j N hXone hepsilon0 (by linarith) rfl hrootOne le_rfl le_rfl
      hcuts.lower_real_one hz0RealLevel hdilation heScale hbaseSmall honeSmall
      idx (by simpa [activeQ, endpointQ, endpointD, E, mtProposition22EReal,
        delta, N] using hidxFull)
    simpa [F, endpointQ, endpointD, delta] using hpiece
  have hz0DataLt : 1 < data.z₀ := by
    rw [hz0Data]
    exact one_lt_two.trans_le hcuts.lower_two
  have hdepth : maxDepth =
      Nat.floor (Real.log ((4 * Y : ℕ) : ℝ) / Real.log (data.z₀ : ℝ)) := by
    dsimp [maxDepth]
    rw [hz0Data]
  have hidentityRaw := mtHarmanProposition22SourceAF_eq_retained_add_error
    (outerQ := outerQ) (outerD := outerD) endpointQ endpointD z Q D E
    (fun i => one_le_two.trans (hendpointD i)) hmonoD hmonoQ hsourceQ
    data maxDepth j hdelta start Y hcutoff hz0DataLt hdepth
  have hcompressed := sum_mtHarmanCompressedRetainedBoxAF_eq_main
    (outerQ := outerQ) (outerD := outerD) (outerStart := z0) (Qouter := Q)
    endpointD z Q D (E : ℝ) data maxDepth j delta N start (Y : ℝ)
  have hidentity : mtHarmanProposition22SourceAF z Q D E Y =
      ∑ idx ∈ S, F idx + c := by
    calc
      mtHarmanProposition22SourceAF z Q D E Y =
          mtHarmanRetainedBoxMainAF (outerQ := outerQ) (outerD := outerD)
            endpointQ endpointD z Q D (E : ℝ) data maxDepth j delta N start
              (Y : ℝ) + c := by
        simpa [c, boundary, N] using hidentityRaw
      _ = ∑ idx ∈ S, F idx + c := by
        rw [← show (∑ idx ∈ S, F idx) =
            mtHarmanRetainedBoxMainAF (outerQ := outerQ) (outerD := outerD)
              endpointQ endpointD z Q D (E : ℝ) data maxDepth j delta N start
                (Y : ℝ) by
          simpa [S, F, activeQ, endpointQ] using hcompressed]
  have herrorSupport : ∀ {n : ℕ}, c n ≠ 0 →
      (Y : ℝ) / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * (Y : ℝ) := by
    intro n hn
    apply mtHarmanProposition22ErrorAF_support_four_eight
      (outerQ := outerQ) (outerD := outerD) endpointQ endpointD z Q D E
      hendpointQ hbandQ hendpointD hbandD z0 (mtTruncationNat X) start
      hdelta hz₀ hroot data hblocks hz0Data hDData maxDepth j N Y hYone
      hcuts.previous_delta_nonneg hcuts.previous_delta_le_one hcollar
    simpa [c, boundary] using hn
  have herrorMeanSquare :
      ∑ n ∈ Finset.Icc 1 (8 * Y), ‖c n‖ ^ 2 ≤
        ((92224 : ℝ) * (5 : ℝ) ^ 35 + 7232) * (Y : ℝ) *
          (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
    have hbound := herrorX (outerQ := outerQ) endpointQ endpointD z Q D E Y
      hcuts.lower_le_z hcuts.z_le_D hcuts.D_le_X
      (by dsimp [endpointD, z0, D, delta]) hYone hYupper hYsqrt
      hendpointQ hmonoQ hbandQ hsourceQ hendpointD hmonoD hbandD
      z0 (mtTruncationNat X) start recRoot hdelta hz₀ hroot data cert
      hblocks hz0Data hDData maxDepth j hmaxLog hcollar
    simpa [c, boundary, outerD, z0, delta, N] using hbound
  exact ⟨{
    ι := MTHarmanRetainedBoxIndex outerQ outerD recDepth
    indexSet := S
    piece := F
    error := c
    identity := by simpa [z, Q, D, E] using hidentity
    piece_shape := hpieceShape
    family_card := hfamilyCard
    error_support := herrorSupport
    error_mean_square := herrorMeanSquare
  }⟩

end

end RHTower.Sieve
