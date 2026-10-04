import GaloisForLFunctions.RHTower.SoninGammaRemainderOperator

/-!
# Full Gamma remainder response from its actual ground integral

The literal strong-integral remainder has a cutoff-independent nuclear
bound on every physical Fourier time-band tail. Its admitted ground limit
constructs a genuine Schatten-one limit with a bound on every original
cutoff error. A fixed exact response map transports this to the complete
Sonin response pair, preserving both source directions and all time-band
channels. The singular homogeneous Gamma reference remains separate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower
local notation "Op" => (SoninL2 →L[ℂ] SoninL2)

open scoped BigOperators
local notation "S1" => SchattenOneOperator SoninL2

private theorem monomial_tail_norm (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (ε δ R S : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    let K := gammaClockRemainderOperator ε R hε-gammaClockRemainderOperator δ S hδ
    ‖K (soninCutoffMonomial a n)‖ ≤ a^n*‖K (soninCutoffMonomial a 0)‖ := by
  dsimp only
  have h := gammaClockRemainder_tail_monomial_energy a ha n ε δ R S hε hδ
  dsimp only at h
  have hp : a^(2*n) = (a^n)^2 := by rw [mul_comm 2 n, pow_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg ha _) (norm_nonneg _))).mp
  rw [mul_pow, ← hp]
  have hpos : 0 ≤ a^(2*n)*(n:ℝ)*((n:ℝ)+1)*
      ‖soninDilationResolvent ((n:ℝ)+1/2) (by positivity)
        ((gammaClockRemainderOperator ε R hε-gammaClockRemainderOperator δ S hδ)
          (soninCutoffMonomial a 0))‖^2 := by positivity
  linarith

private theorem degree_relative_mass (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    a^n * ‖soninCutoffMonomial a 0‖ ≤ ((n+1:ℕ):ℝ) * ‖soninCutoffMonomial a n‖ := by
  apply (sq_le_sq₀ (mul_nonneg (pow_nonneg ha _) (norm_nonneg _)) (by positivity)).mp
  rw [mul_pow, mul_pow, norm_sq_soninCutoffMonomial a ha 0, norm_sq_soninCutoffMonomial a ha n]
  simp only [mul_zero, zero_add, pow_one, Nat.cast_add, Nat.cast_one, Nat.cast_zero, div_one]
  have hn : 0 < 2*(n:ℝ)+1 := by positivity
  rw [← mul_div_assoc, le_div_iff₀ hn]
  have hp : a^(2*n+1) = (a^n)^2*a := by rw [pow_add, pow_mul]; ring
  rw [hp]
  have hpos : 0 ≤ 2*a*(a^n)^2*(n:ℝ)^2 := by positivity
  nlinarith

private theorem ground_norm_pos (a : ℝ) (ha : 0 < a) :
    0 < ‖soninCutoffMonomial a 0‖ := by
  have h := norm_sq_soninCutoffMonomial a ha.le 0
  simp only [mul_zero, zero_add, pow_one, Nat.cast_zero, div_one] at h
  nlinarith [norm_nonneg (soninCutoffMonomial a 0)]

private theorem output_operator_norm (D T : SoninL2 →L[ℂ] SoninL2) (f : SoninL2)
    (e : ℝ) (he : 0 ≤ e) (hT : ∀ x, T x ∈ Submodule.span ℂ ({f} : Set SoninL2))
    (hD : ‖D f‖ ≤ e*‖f‖) : ‖D ∘L T‖ ≤ e*‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg he (norm_nonneg _))
  intro x
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hT x)
  change ‖D (T x)‖ ≤ (e*‖T‖)*‖x‖
  calc
    _ = ‖c‖*‖D f‖ := by rw [← hc, map_smul, norm_smul]
    _ ≤ ‖c‖*(e*‖f‖) := mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    _ = e*‖T x‖ := by rw [← hc, norm_smul]; ring
    _ ≤ e*(‖T‖*‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) he
    _ = _ := by ring

private theorem nuclear_norm_le {ι : Type*}
    (A : ι → SoninL2 →L[ℂ] SoninL2) (T : SoninL2 →L[ℂ] SoninL2)
    (hA : ∀ i, HasRankLE (A i) 1) (hn : Summable (fun i => ‖A i‖)) (hS : HasSum A T) :
    traceNorm SoninL2 T ≤ ∑' i, ‖A i‖ := by
  let B : ι → SchattenOneOperator SoninL2 := fun i =>
    ⟨A i, memSchattenClass_of_hasRankLE one_pos (hA i)⟩
  have hnorm (i : ι) : ‖B i‖ = ‖A i‖ := traceNorm_eq_norm_of_hasRankLE_one (hA i)
  have hnB : Summable (fun i => ‖B i‖) := hn.congr (fun i => (hnorm i).symm)
  have hB : Summable B := Summable.of_norm hnB
  have hSA : HasSum A ((∑' i, B i : SchattenOneOperator SoninL2) : SoninL2 →L[ℂ] SoninL2) :=
    (schattenOneCoeCLM (H := SoninL2)).hasSum hB.hasSum
  have heq := hSA.unique hS
  have hbound : ‖∑' i, B i‖ ≤ ∑' i, ‖A i‖ := by
    simpa only [hnorm] using norm_tsum_le_tsum_norm hnB
  change traceNorm SoninL2 ((∑' i, B i : SchattenOneOperator SoninL2) :
    SoninL2 →L[ℂ] SoninL2) ≤ _ at hbound
  rwa [heq] at hbound


/-- The actual finite remainder on the physical time-band operator, in genuine Schatten one. -/
def gammaClockRemainderTimeBandCutoff (a c d : ℝ) (ha : 0 < a)
    (ε R : ℝ) (hε : 0 < ε) : S1 :=
  ⟨gammaClockRemainderOperator ε R hε ∘L
      fullTimeBandFourier (-a) a c d (neg_le_self ha.le),
    memSchattenClass_one_comp_left
      (memSchattenClass_one_fullTimeBandFourier (-a) a c d (neg_le_self ha.le)) _⟩

/-- Every two-cutoff nuclear difference is controlled by its literal ground difference. -/
theorem gammaClockRemainder_timeBand_tail_bound (a c d : ℝ) (ha : 0 < a)
    (ε δ R S : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ‖gammaClockRemainderTimeBandCutoff a c d ha ε R hε-
        gammaClockRemainderTimeBandCutoff a c d ha δ S hδ‖ ≤
      soninGroundNuclearConstant a c d ha *
        ‖(gammaClockRemainderOperator ε R hε-gammaClockRemainderOperator δ S hδ)
          (soninCutoffMonomial a 0)‖ := by
  change traceNorm SoninL2 ((gammaClockRemainderOperator ε R hε-
    gammaClockRemainderOperator δ S hδ) ∘L
    fullTimeBandFourier (-a) a c d (neg_le_self ha.le)) ≤ _
  let K := gammaClockRemainderOperator ε R hε-gammaClockRemainderOperator δ S hδ
  let A := fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha.le)
  let T := fullTimeBandFourier (-a) a c d (neg_le_self ha.le)
  let e := ‖K (soninCutoffMonomial a 0)‖ / ‖soninCutoffMonomial a 0‖
  have he : 0 ≤ e := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hg := ground_norm_pos a ha
  have hcolumn (n : ℕ) : ‖K (soninCutoffMonomial a n)‖ ≤
      (e*((n+1:ℕ):ℝ)) * ‖soninCutoffMonomial a n‖ := by
    calc
      _ ≤ a^n * ‖K (soninCutoffMonomial a 0)‖ := monomial_tail_norm a ha.le n ε δ R S hε hδ
      _ = e*(a^n * ‖soninCutoffMonomial a 0‖) := by dsimp [e]; field_simp
      _ ≤ e*(((n+1:ℕ):ℝ) * ‖soninCutoffMonomial a n‖) :=
        mul_le_mul_of_nonneg_left (degree_relative_mass a ha.le n) he
      _ = _ := by ring
  have htail (n : ℕ) : ‖K ∘L A n‖ ≤ e*(((n+1:ℕ):ℝ)*‖A n‖) := by
    have h := output_operator_norm K (A n) (soninCutoffMonomial a n)
      (e*((n+1:ℕ):ℝ)) (by positivity)
      (fullTimeBandFourierTaylorTerm_mem_span_cutoffMonomial a c d ha.le n) (hcolumn n)
    simpa only [mul_assoc] using h
  have hw : Summable (fun n => ((n+1:ℕ):ℝ)*‖A n‖) :=
    summable_succ_mul_norm_fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha.le)
  have hn : Summable (fun n => ‖K ∘L A n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail (hw.mul_left e)
  have hS : HasSum (fun n => K ∘L A n) (K ∘L T) :=
    (hasSum_fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha.le)).mul_left K
  calc
    _ ≤ ∑' n, ‖K ∘L A n‖ := nuclear_norm_le _ _
      (fun n => (hasRankLE_fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha.le) n).comp_left K) hn hS
    _ ≤ ∑' n, e*(((n+1:ℕ):ℝ)*‖A n‖) := Summable.tsum_le_tsum htail hn (hw.mul_left e)
    _ = _ := by rw [tsum_mul_left]; dsimp [soninGroundNuclearConstant, e, A, K]; ring

private theorem ground_constant_nonneg (a c d : ℝ) (ha : 0 < a) :
    0 ≤ soninGroundNuclearConstant a c d ha := by
  unfold soninGroundNuclearConstant
  exact div_nonneg (tsum_nonneg (fun _ => by positivity)) (norm_nonneg _)

private theorem timeBand_dist_bound (a c d : ℝ) (ha : 0 < a)
    (ε δ R S : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    dist (gammaClockRemainderTimeBandCutoff a c d ha ε R hε)
        (gammaClockRemainderTimeBandCutoff a c d ha δ S hδ) ≤
      soninGroundNuclearConstant a c d ha *
        dist (gammaGroundTruncated a ε R-gammaHomogeneousGroundTruncated a ε R)
          (gammaGroundTruncated a δ S-gammaHomogeneousGroundTruncated a δ S) := by
  have h := gammaClockRemainder_timeBand_tail_bound a c d ha ε δ R S hε hδ
  rw [sub_apply, gammaClockRemainderOperator_ground, gammaClockRemainderOperator_ground] at h
  simpa only [dist_eq_norm] using! h

private theorem exists_completion (a c d : ℝ) (ha : 0 < a) :
    ∃ T : S1, ∀ (ε R : ℝ) (hε : 0 < ε),
      ‖gammaClockRemainderTimeBandCutoff a c d ha ε R hε-T‖ ≤
        soninGroundNuclearConstant a c d ha *
          ‖gammaGroundTruncated a ε R-gammaHomogeneousGroundTruncated a ε R-
            gammaClockRemainderGround a‖ := by
  let C := soninGroundNuclearConstant a c d ha
  have hC : 0 ≤ C := ground_constant_nonneg a c d ha
  let g : ℕ → SoninL2 := fun n => gammaGroundTruncated a (1/((n:ℝ)+1)) n-
    gammaHomogeneousGroundTruncated a (1/((n:ℝ)+1)) n
  let F : ℕ → S1 := fun n => gammaClockRemainderTimeBandCutoff a c d ha
    (1/((n:ℝ)+1)) n (by positivity)
  have heps : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => by change 0 < 1/((n:ℝ)+1); positivity)⟩
  have hg : Tendsto g atTop (𝓝 (gammaClockRemainderGround a)) :=
    gammaGroundTruncated_sub_homogeneous_tendsto a ha.le heps tendsto_natCast_atTop_atTop
  have hFG (m n : ℕ) : dist (F m) (F n) ≤ C*dist (g m) (g n) := by
    exact timeBand_dist_bound a c d ha (1/((m:ℝ)+1)) (1/((n:ℝ)+1)) m n
      (by positivity) (by positivity)
  have hF : CauchySeq F := by
    apply Metric.cauchySeq_iff.mpr
    intro η hη
    have hCp : 0 < C+1 := by linarith
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hg.cauchySeq (η/(C+1)) (div_pos hη hCp)
    refine ⟨N, fun m hm n hn => ?_⟩
    calc
      dist (F m) (F n) ≤ C*dist (g m) (g n) := hFG m n
      _ ≤ (C+1)*dist (g m) (g n) := by nlinarith [show 0 ≤ dist (g m) (g n) from dist_nonneg]
      _ < (C+1)*(η/(C+1)) := mul_lt_mul_of_pos_left (hN m hm n hn) hCp
      _ = η := mul_div_cancel₀ η hCp.ne'
  obtain ⟨T,hT⟩ := cauchySeq_tendsto_of_complete hF
  refine ⟨T, fun ε R hε => ?_⟩
  have hbound (n : ℕ) :
      dist (gammaClockRemainderTimeBandCutoff a c d ha ε R hε) (F n) ≤
        C*dist (gammaGroundTruncated a ε R-gammaHomogeneousGroundTruncated a ε R) (g n) := by
    exact timeBand_dist_bound a c d ha ε (1/((n:ℝ)+1)) R n hε (by positivity)
  have h := le_of_tendsto_of_tendsto (tendsto_const_nhds.dist hT)
    (tendsto_const_nhds.mul (tendsto_const_nhds.dist hg)) (Eventually.of_forall hbound)
  simpa only [dist_eq_norm, C] using h

/-- The actual Gamma remainder's physical time-band completion in Schatten one. -/
def gammaClockRemainderTimeBand (a c d : ℝ) (ha : 0 < a) : S1 :=
  Classical.choose (exists_completion a c d ha)

/-- The admitted ground remainder controls the complete nuclear cutoff error. -/
theorem gammaClockRemainderTimeBand_cutoff_bound (a c d : ℝ) (ha : 0 < a)
    (ε R : ℝ) (hε : 0 < ε) :
    ‖gammaClockRemainderTimeBandCutoff a c d ha ε R hε-gammaClockRemainderTimeBand a c d ha‖ ≤
      soninGroundNuclearConstant a c d ha *
        ‖gammaGroundTruncated a ε R-gammaHomogeneousGroundTruncated a ε R-
          gammaClockRemainderGround a‖ :=
  Classical.choose_spec (exists_completion a c d ha) ε R hε

/-- Every cofinal pair of actual cutoffs converges to the same nuclear remainder. -/
theorem gammaClockRemainderTimeBand_tendsto (a c d : ℝ) (ha : 0 < a)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ε R : ι → ℝ) (hpos : ∀ i, 0 < ε i)
    (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) :
    Tendsto (fun i => gammaClockRemainderTimeBandCutoff a c d ha (ε i) (R i) (hpos i))
      l (𝓝 (gammaClockRemainderTimeBand a c d ha)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hg := gammaGroundTruncated_sub_homogeneous_tendsto a ha.le hε hR
  have hz : Tendsto (fun i => soninGroundNuclearConstant a c d ha *
      ‖gammaGroundTruncated a (ε i) (R i)-gammaHomogeneousGroundTruncated a (ε i) (R i)-
        gammaClockRemainderGround a‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (tendsto_const_nhds (x := soninGroundNuclearConstant a c d ha)).mul
        ((hg.sub (tendsto_const_nhds (x := gammaClockRemainderGround a))).norm)
  exact squeeze_zero (fun _ => dist_nonneg) (fun i => by
    simpa only [dist_eq_norm] using gammaClockRemainderTimeBand_cutoff_bound a c d ha (ε i) (R i) (hpos i)) hz

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

private def nuclearSandwich (L R : Op) : S1 →L[ℂ] S1 :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨L ∘L T.val ∘L R,
        memSchattenClass_one_comp_right (memSchattenClass_one_comp_left T.property L) R⟩
      map_add' := by
        intro S T
        apply SchattenOneOperator.ext
        apply ContinuousLinearMap.ext
        intro x
        change L (S.val (R x)+T.val (R x)) = _
        exact map_add L _ _
      map_smul' := by
        intro c T
        apply SchattenOneOperator.ext
        apply ContinuousLinearMap.ext
        intro x
        change L (c • T.val (R x)) = _
        exact map_smul L c _ }
    (‖L‖*‖R‖) (fun T => by
      change traceNorm SoninL2 ((L ∘L T.val) ∘L R) ≤ _
      calc
        _ ≤ traceNorm SoninL2 (L ∘L T.val)*‖R‖ :=
          traceNorm_comp_right_le (memSchattenClass_one_comp_left T.property L).one_summable R
        _ ≤ (‖L‖*traceNorm SoninL2 T.val)*‖R‖ :=
          mul_le_mul_of_nonneg_right (traceNorm_comp_left_le T.summable L) (norm_nonneg _)
        _ = _ := by rw [SchattenOneOperator.norm_def]; ring)

private def fourierOp : Op := fourierUnitary.toLinearIsometry.toContinuousLinearMap
private def inverseFourierOp : Op := fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap
private def physicalBand (a : ℝ) (ha : 0 < a) : Op :=
  fullTimeBandFourier (-a) a (-a) a (neg_le_self ha.le)

private theorem fourierPhysical_factor (a : ℝ) (ha : 0 < a) :
    (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection =
      inverseFourierOp * physicalBand a ha := by
  dsimp only [centralPhysicalForbidden,centralFourierForbidden]
  rw [← indicatorCutoff_eq_physicalForbidden_starProjection,
    ← fourierCutoff_eq_fourierForbidden_starProjection]
  apply ContinuousLinearMap.ext
  intro f
  change fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
    (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f) =
      fourierUnitary.symm (physicalBand a ha f)
  rw [fourierCutoff_apply,physicalBand,fullTimeBandFourier_eq_cutoffFourierCutoff]
  rfl

private theorem physicalFourier_factor (a : ℝ) (ha : 0 < a) :
    (centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection =
      l2Reflection * physicalBand a ha * fourierOp := by
  dsimp only [centralPhysicalForbidden,centralFourierForbidden]
  rw [← indicatorCutoff_eq_physicalForbidden_starProjection,
    ← fourierCutoff_eq_fourierForbidden_starProjection]
  apply ContinuousLinearMap.ext
  intro f
  change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
    (fourierUnitary.symm (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (fourierUnitary f))) = l2Reflection (physicalBand a ha (fourierUnitary f))
  rw [fourierUnitary_symm_eq_reflection_fourier,← l2Reflection_indicatorCutoff_central,
    physicalBand,fullTimeBandFourier_eq_cutoffFourierCutoff]
  rfl

private def leftSourceFromPhysical (a : ℝ) (ha : 0 < a) : S1 →L[ℂ] S1 :=
  nuclearSandwich l2Reflection
    (fourierOp*(1-(centralPhysicalForbidden a).starProjection*soninCorrectionSourceRightFactor a ha)) +
  nuclearSandwich inverseFourierOp (soninCorrectionSourceRightFactor a ha)

private def responseFromPhysical (a : ℝ) (ha : 0 < a) : S1 →L[ℝ] (S1 × S1) :=
  (soninPairedResponseForward a).comp
    (((leftSourceFromPhysical a ha).prod (leftSourceFromPhysical a ha)).restrictScalars ℝ)

private theorem native_inverse_fourier_commute (ε R : ℝ) (hε : 0 < ε) :
    gammaClockRemainderOperator ε R hε * inverseFourierOp =
      inverseFourierOp * gammaClockRemainderOperator ε R hε := by
  apply ContinuousLinearMap.ext
  intro f
  apply fourierUnitary.injective
  change fourierUnitary (gammaClockRemainderOperator ε R hε (fourierUnitary.symm f)) =
    fourierUnitary (fourierUnitary.symm (gammaClockRemainderOperator ε R hε f))
  rw [fourier_gammaClockRemainderOperator,fourierUnitary.apply_symm_apply,
    fourierUnitary.apply_symm_apply]

private theorem sourceFromPhysical_apply (a : ℝ) (ha : 0 < a)
    (ε R : ℝ) (hε : 0 < ε) :
    (leftSourceFromPhysical a ha (gammaClockRemainderTimeBandCutoff a (-a) a ha ε R hε)).val =
      gammaClockRemainderOperator ε R hε * centralSoninProjectionCorrection a := by
  let D := gammaClockRemainderOperator ε R hε
  let A := (centralPhysicalForbidden a).starProjection
  let B := (centralFourierForbidden a).starProjection
  let W := soninCorrectionSourceRightFactor a ha
  have hDR : D*l2Reflection=l2Reflection*D := by
    apply ContinuousLinearMap.ext
    intro f
    exact (reflection_gammaClockRemainderOperator ε R hε f).symm
  have hDU : D*inverseFourierOp=inverseFourierOp*D := native_inverse_fourier_commute ε R hε
  have hJ : centralSoninProjectionCorrection a=A*B*(1-A*W)+B*A*W :=
    centralSoninProjectionCorrection_eq_timeBand_rightFactors a ha
  have hAB : A*B=l2Reflection*physicalBand a ha*fourierOp := physicalFourier_factor a ha
  have hBA : B*A=inverseFourierOp*physicalBand a ha := fourierPhysical_factor a ha
  change l2Reflection*(D*physicalBand a ha)*(fourierOp*(1-A*W)) +
    inverseFourierOp*(D*physicalBand a ha)*W = D*centralSoninProjectionCorrection a
  rw [hJ,hAB,hBA]
  calc
    _ = (D*l2Reflection)*physicalBand a ha*(fourierOp*(1-A*W)) +
      (D*inverseFourierOp)*physicalBand a ha*W := by
        rw [hDR,hDU]
        noncomm_ring
    _ = _ := by noncomm_ring

private theorem responseFromPhysical_apply (a : ℝ) (ha : 0 < a)
    (ε R : ℝ) (hε : 0 < ε) :
    responseFromPhysical a ha (gammaClockRemainderTimeBandCutoff a (-a) a ha ε R hε) =
      soninNuclearResponsePair a ha (gammaClockRemainderOperator ε R hε) := by
  rw [← soninPairedResponseForward_apply]
  apply congrArg (soninPairedResponseForward a)
  apply Prod.ext <;> apply SchattenOneOperator.ext
  · exact sourceFromPhysical_apply a ha ε R hε
  · change (leftSourceFromPhysical a ha
      (gammaClockRemainderTimeBandCutoff a (-a) a ha ε R hε)).val =
      adjoint (gammaClockRemainderOperator ε R hε)*centralSoninProjectionCorrection a
    rw [adjoint_gammaClockRemainderOperator]
    exact sourceFromPhysical_apply a ha ε R hε


/-- The complete Sonin response of the actual admitted Gamma remainder. -/
def gammaClockRemainderResponse (a : ℝ) (ha : 0 < a) : S1 × S1 :=
  responseFromPhysical a ha (gammaClockRemainderTimeBand a (-a) a ha)

/-- Full response convergence for every cofinal pair of the original Gamma remainder cutoffs. -/
theorem gammaClockRemainderResponse_tendsto (a : ℝ) (ha : 0 < a)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ε R : ι → ℝ) (hpos : ∀ i, 0 < ε i)
    (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) :
    Tendsto (fun i => soninNuclearResponsePair a ha
      (gammaClockRemainderOperator (ε i) (R i) (hpos i)))
      l (𝓝 (gammaClockRemainderResponse a ha)) := by
  have h := (responseFromPhysical a ha).continuous.continuousAt.tendsto.comp
    (gammaClockRemainderTimeBand_tendsto a (-a) a ha ε R hpos hε hR)
  exact h.congr (fun i => responseFromPhysical_apply a ha (ε i) (R i) (hpos i))

end RHTower
