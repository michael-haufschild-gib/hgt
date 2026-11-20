import GaloisForLFunctions.HTGeometry.Quantum.TranslatedCircuitExcursion
import GaloisForLFunctions.HTGeometry.UniformProjectiveContinuousCircuitFirstReturnLaw

/-!
# Time occupation of a projective circuit tube

A dense static orbit supplies one physical time shift for each anchored
spectral reflection. At any observation time the shifted evolutions are
projectively separated. A fixed target accepts at most one shift. Comparing
Lebesgue lengths gives a bound uniform in the observation interval's origin.
-/

open MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- If different translates of a time set are disjoint, its occupation of
every interval is bounded by the interval length plus the span of the shifts. -/
private theorem occupation_of_separated_translates {ι : Type*} [Fintype ι]
    (τ : ι → ℝ) (S : ℝ) (hS : 0 ≤ S) (hs : ∀ i, τ i ∈ Icc 0 S)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hdis : ∀ t i j, t + τ i ∈ B → t + τ j ∈ B → i = j)
    (A T : ℝ) (hT : 0 ≤ T) :
    (Fintype.card ι : ℝ) * volume.real (B ∩ Icc A (A+T)) ≤ T+S := by
  let K := B ∩ Icc A (A+T)
  let f (i : ι) := (fun t : ℝ => t+τ i) ⁻¹' K
  have hm : MeasurableSet K := hB.inter measurableSet_Icc
  have hfm (i : ι) : MeasurableSet (f i) := hm.preimage (measurable_id.add_const _)
  have hval (i : ι) : volume (f i) = volume K :=
    (measurePreserving_add_right volume (τ i)).measure_preimage hm.nullMeasurableSet
  have hfin : volume K ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hpair : Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro t hi hj
    exact hij (hdis t i j hi.1 hj.1)
  have hsub : (⋃ i, f i) ⊆ Icc (A-S) (A+T) := by
    intro t ht
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ht
    have hb : t + τ i ∈ Icc A (A+T) := hi.2
    exact ⟨by linarith only [hb.1,(hs i).2], by linarith only [hb.2,(hs i).1]⟩
  calc
    _ = ∑ i : ι, volume.real (f i) := by simp [Measure.real, hval, K]
    _ = volume.real (⋃ i, f i) := (measureReal_iUnion_fintype hpair hfm
      (fun i => (hval i).symm ▸ hfin)).symm
    _ ≤ volume.real (Icc (A-S) (A+T)) := measureReal_mono hsub measure_Icc_lt_top.ne
    _ = T+S := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring

private def phased (A : Reg n) : Set (Reg n) :=
  (fun z : ℂ => z • A) '' Metric.sphere 0 1

private theorem phased_compact (A : Reg n) : IsCompact (phased A) :=
  (isCompact_sphere (0 : ℂ) 1).image (by fun_prop)

private theorem phased_nonempty (A : Reg n) : (phased A).Nonempty :=
  ⟨(1 : ℂ) • A, 1, by simp, rfl⟩

/-- Physical times within projective operator distance 2/5 of a fixed target. -/
private def phaseTube (H W : Reg n) : Set ℝ :=
  {t | Metric.infDist (unitaryEvolution H t) (phased W) ≤ 2/5}

private theorem phaseTube_iff (H W : Reg n) (t : ℝ) :
    t ∈ phaseTube H W ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ ‖unitaryEvolution H t - c • W‖ ≤ 2/5 := by
  constructor
  · intro ht
    obtain ⟨_,⟨c,hc,rfl⟩,hd⟩ := exists_compactTarget_minDist
      (phased_compact W) (phased_nonempty W) (unitaryEvolution H t)
    exact ⟨c,by simpa using hc, by simpa only [← hd,dist_eq_norm] using
      (show Metric.infDist (unitaryEvolution H t) (phased W) ≤ 2/5 from ht)⟩
  · rintro ⟨c,hc,h⟩
    apply (Metric.infDist_le_dist_of_mem (show c • W ∈ phased W from ⟨c,by simpa using hc,rfl⟩)).trans
    simpa only [dist_eq_norm] using h

private theorem phaseTube_measurable (H : selfAdjoint (Reg n)) (W : Reg n) :
    MeasurableSet (phaseTube (H : Reg n) W) := by
  have hL : LipschitzWith ⟨‖(H : Reg n)‖,norm_nonneg _⟩ (unitaryEvolution (H : Reg n)) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    change dist (unitaryEvolution (H : Reg n) t) (unitaryEvolution H u) ≤ ‖(H : Reg n)‖ * dist t u
    rw [dist_eq_norm,Real.dist_eq]
    exact norm_unitaryEvolution_time_sub_le H.2 t u
  exact (isClosed_compactTargetCaptureTimeSet _ hL.continuous (phased W) _).measurableSet

/-- Undo right translation by a unitary and remove the common scalar phase. -/
private theorem untranslate_error (X A : Reg n) (U : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (z c : ℂ) (hz : ‖z‖ = 1) :
    ‖X - (z⁻¹*c) • (A * (U⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).val)‖ =
      ‖z • (X * (U : Reg n)) - c • A‖ := by
  have h1 : (U⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).val * (U : Reg n) = 1 :=
    congrArg Subtype.val (inv_mul_cancel U)
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
  rw [← CStarRing.norm_mul_coe_unitary _ U, sub_mul, Matrix.smul_mul, mul_assoc, h1, mul_one]
  have hf : z • (X*(U : Reg n) - (z⁻¹*c) • A) = z • (X*(U : Reg n)) - c • A := by
    rw [smul_sub, smul_smul, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
  rw [← hf,norm_smul,hz,one_mul]

private theorem cannot_share_center (X Y A : Reg n)
    (hsep : ∀ z : ℂ, ‖z‖ = 1 → 1 ≤ ‖X - z • Y‖)
    (b c : ℂ) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hX : ‖X-b • A‖ < 1/2) (hY : ‖Y-c • A‖ < 1/2) : False := by
  let z := b/c
  have hz : ‖z‖ = 1 := by simp [z,hb,hc]
  have hzc : z*c = b := div_mul_cancel₀ _ (norm_ne_zero_iff.mp (by rw [hc]; exact one_ne_zero))
  have hclose : ‖b • A - z • Y‖ = ‖Y-c • A‖ := by
    rw [← hzc, ← smul_smul, ← smul_sub, norm_smul, hz,one_mul,norm_sub_rev]
  have h := norm_sub_le_norm_sub_add_norm_sub X (b • A) (z • Y)
  rw [hclose] at h
  linarith only [h,hsep z hz,hX,hY]

private def evolutionUnitary (H : selfAdjoint (Reg n)) (t : ℝ) :
    Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  ⟨unitaryEvolution (H : Reg n) t,unitaryEvolution_mem_unitary H.2 t⟩

/-- A tube hit after a spectral-sign shift becomes a hit of one common
backwards-translated target in spectral coordinates. -/
private theorem shifted_hit_center (H : selfAdjoint (Reg n)) (B W : Reg n)
    (s u : ℝ) (z : ℂ) (hz : ‖z‖ = 1) (hs : ‖unitaryEvolution (H : Reg n) s - z • B‖ < 1/40)
    (hx : s+u ∈ phaseTube (H : Reg n) W) :
    ∃ b : ℂ, ‖b‖ = 1 ∧
      ‖B-b • (W * ((evolutionUnitary H u)⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).val)‖ < 1/2 := by
  let U := evolutionUnitary H u
  obtain ⟨c,hc,hh⟩ := (phaseTube_iff (H : Reg n) W (s+u)).mp hx
  refine ⟨z⁻¹*c,by rw [norm_mul,norm_inv,hz,hc,inv_one,one_mul],?_⟩
  rw [untranslate_error B W (evolutionUnitary H u) z c hz]
  have hp : unitaryEvolution (H : Reg n) s * (U : Reg n) = unitaryEvolution H (s+u) := by
    change unitaryEvolution (H : Reg n) s * unitaryEvolution H u = unitaryEvolution H (s+u)
    simpa only [add_sub_cancel_right] using unitaryEvolution_sub_mul H (s+u) u
  have hnear : ‖unitaryEvolution (H : Reg n) (s+u) - z • (B*(U : Reg n))‖ < 1/40 := by
    rw [← hp, ← Matrix.smul_mul, ← sub_mul, CStarRing.norm_mul_coe_unitary]
    exact hs
  rw [norm_sub_rev] at hnear
  have h := norm_sub_le_norm_sub_add_norm_sub (z • (B*(U : Reg n)))
    (unitaryEvolution (H : Reg n) (s+u)) (c • W)
  change ‖z • (B*(U : Reg n)) - c • W‖ < 1/2
  linarith only [h,hh,hnear]

/-- One overhead S works for all targets, all time offsets and all observation
intervals on this Hamiltonian. Each projective tube occupies at most the
fraction 2^(−d), up to the additive interval-length correction S. -/
theorem spectral_sign_occupation_bound {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i))) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (W : Reg n) (offset A T : ℝ), 0 ≤ T →
      (2:ℝ)^d * volume.real
        ({t | ∃ c : ℂ, ‖c‖ = 1 ∧ ‖unitaryEvolution (H : Reg n) (t+offset) - c • W‖ ≤ 2/5}
          ∩ Icc A (A+T)) ≤ T+S := by
  classical
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let B := anchoredSpectralBooleanReflection e V
  have visits (x : Fin d → Bool) : ∃ s : ℝ, 0 ≤ s ∧ ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖unitaryEvolution (H : Reg n) s - z • B x‖ < 1/40 := by
    obtain ⟨G,_,hh⟩ := syndetic_approach_spectral_signs e H.2.isHermitian hmax x
    obtain ⟨s,hs,z,hz,hd⟩ := hh 0
    exact ⟨s,hs.1,z,hz,hd⟩
  choose s hs z hz hhit using visits
  let S : ℝ := ∑ x, s x
  have hsS (x) : s x ≤ S := Finset.single_le_sum (fun y _ => hs y) (Finset.mem_univ x)
  have hS : 0 ≤ S := Finset.sum_nonneg fun x _ => hs x
  refine ⟨S,hS,?_⟩
  intro W offset A T hT
  let hits := (fun t : ℝ => t+offset) ⁻¹' phaseTube (H : Reg n) W
  have hm : MeasurableSet hits := (phaseTube_measurable H W).preimage (measurable_id.add_const _)
  have hdis (t : ℝ) (i j : Fin d → Bool) (hi : t+s i ∈ hits) (hj : t+s j ∈ hits) : i = j := by
    let u := t+offset
    let P := W * ((evolutionUnitary H u)⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).val
    have hc (x : Fin d → Bool) (hx : t+s x ∈ hits) : ∃ b : ℂ, ‖b‖ = 1 ∧ ‖B x-b • P‖ < 1/2 := by
      apply shifted_hit_center H (B x) W (s x) u (z x) (hz x) (hhit x)
      change t+s x+offset ∈ phaseTube (H : Reg n) W at hx
      rwa [show s x+u = t+s x+offset by dsimp [u]; ring]
    by_contra hn
    obtain ⟨b,hb,hbi⟩ := hc i hi
    obtain ⟨c,hc',hcj⟩ := hc j hj
    exact cannot_share_center (B i) (B j) P
      (anchoredSpectralBooleanReflection_projective_separated e V hn) b c hb hc' hbi hcj
  have h := occupation_of_separated_translates s S hS (fun i => ⟨hs i,hsS i⟩) hits hm hdis A T hT
  have he : hits = {t | ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖unitaryEvolution (H : Reg n) (t+offset) - c • W‖ ≤ 2/5} := by
    ext t
    exact phaseTube_iff (H : Reg n) W (t+offset)
  simpa only [he,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using h

/-- Starting times whose following physical window contains some unitary
achievable to fixed error by at most s arbitrary two-qubit gates. -/
def circuitWindowHits (H : Reg n) (s : ℕ) (W : ℝ) : Set ℝ :=
  {u | ∃ t ∈ Icc u (u+W), HasProjectiveCircuitApproximation n (1/10 : ℝ) s
    (unitaryEvolution H t)}

/-- Bound the fraction of window starts with a downward fluctuation at any
time inside the window. The circuit architecture, continuous gates, and
global phase may depend on the time of the fluctuation. -/
theorem spectral_sign_window_occupation {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i))) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (s : ℕ) (W mesh : ℝ), 0 < mesh → ‖(H : Reg n)‖*mesh ≤ 1/40 →
      ∀ A T : ℝ, 0 ≤ T →
      (2:ℝ)^d * volume.real (circuitWindowHits (H : Reg n) s W ∩ Icc A (A+T)) ≤
        (plateauGridCount W mesh : ℝ) * ((atMostQuarterCircuitNet n s).card : ℝ) * (T+S) := by
  classical
  obtain ⟨S,hS,hh⟩ := spectral_sign_occupation_bound e H hmax
  refine ⟨S,hS,?_⟩
  intro s W mesh hm hs A T hT
  let N := plateauGridCount W mesh
  let net := atMostQuarterCircuitNet n s
  let I := Fin N × {U // U ∈ net}
  let τ (j : Fin N) := (j.val : ℝ)*mesh
  let f (i : I) : Set ℝ := {u | ∃ c : ℂ, ‖c‖ = 1 ∧
    ‖unitaryEvolution (H : Reg n) (u+τ i.1) - c • (i.2.val : Reg n)‖ ≤ 2/5} ∩ Icc A (A+T)
  have hsub : circuitWindowHits (H : Reg n) s W ∩ Icc A (A+T) ⊆ ⋃ i, f i := by
    rintro u ⟨⟨t,ht,c,hc,C,hC,he⟩,hu⟩
    obtain ⟨j,hj⟩ := exists_plateauGrid_near hm u ht
    obtain ⟨V,hV,hCV⟩ := atMostQuarterCircuitNet_cover C hC
    refine Set.mem_iUnion.mpr ⟨(j,⟨V,hV⟩),⟨⟨c,hc,?_⟩,hu⟩⟩
    have hnear : ‖unitaryEvolution (H : Reg n) t - unitaryEvolution H (u+τ j)‖ ≤ 1/40 :=
      (norm_unitaryEvolution_time_sub_le H.2 _ _).trans
        ((mul_le_mul_of_nonneg_left hj (norm_nonneg _)).trans hs)
    have hnet : ‖c • (C.eval : Reg n) - c • (V : Reg n)‖ ≤ 1/4 := by
      rw [← smul_sub, norm_smul, hc, one_mul]
      simpa only [dist_eq_norm] using hCV
    have ha := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution (H : Reg n) (u+τ j))
      (unitaryEvolution (H : Reg n) t) (c • (V : Reg n))
    have hb := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution (H : Reg n) t)
      (c • (C.eval : Reg n)) (c • (V : Reg n))
    rw [norm_sub_rev] at hnear
    change ‖unitaryEvolution (H : Reg n) (u+τ j) - c • (V : Reg n)‖ ≤ 2/5
    linarith only [ha,hb,hnear,hnet,he]
  have hf : (⋃ i, f i) ⊆ Icc A (A+T) := Set.iUnion_subset fun _ => inter_subset_right
  have hvol := measureReal_mono (μ := volume) hsub
    (measure_ne_top_of_subset hf measure_Icc_lt_top.ne)
  have hb (i : I) : (2:ℝ)^d * volume.real (f i) ≤ T+S := hh _ _ A T hT
  calc
    _ ≤ (2:ℝ)^d * ∑ i : I, volume.real (f i) :=
      mul_le_mul_of_nonneg_left (hvol.trans (measureReal_iUnion_fintype_le f)) (by positivity)
    _ = ∑ i : I, (2:ℝ)^d * volume.real (f i) := Finset.mul_sum _ _ _
    _ ≤ ∑ _i : I, (T+S) := Finset.sum_le_sum fun i _ => hb i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,I,Fintype.card_prod,
      Fintype.card_fin,Fintype.card_coe,nsmul_eq_mul,Nat.cast_mul,N,net]

/-- A Gaussian path has overwhelming long-time occupation of entire hard
windows. The finite observation correction is uniform in the origin A.
The same draw retains the two-query locality signal at every time. -/
theorem gaussianPath_rare_circuitWindowHits_and_permanentLocality :
    ∀ᶠ L : ℕ in Filter.atTop,
    ∀ᵐ p ∂(centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1),
      let n := L*2
      let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
      let r := excursionGateBudget n
      let W := translatedExcursionWidth n ‖(H : Reg n)‖
      (∃ S : ℝ, 0 ≤ S ∧ ∀ A T : ℝ, 0 ≤ T →
        ((r+1:ℝ)^r) * volume.real (circuitWindowHits (H : Reg n) r W ∩ Icc A (A+T)) ≤ T+S) ∧
      RHTower.NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  have hcof : Filter.Tendsto (fun L : ℕ => L*2) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    exact Filter.eventually_atTop.2 ⟨N,fun L h => by omega⟩
  filter_upwards [Filter.eventually_ge_atTop 1,
    hcof.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier,
    RHTower.eventually_pairQubit_twoLocalPauli_separator] with L hL he hsep
  have hnull := (nearestNeighborPathLocalMaximalSet_dense_residual_fullMeasure (L := L) hL).2.2
  have hμ : centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1 ≪
      (volume : Measure (Fin (nearestNeighborPathLocalParameterCount L) → ℝ)) := by
    simpa [centredProductGaussian] using (productGaussian_absolutelyContinuous
      (nearestNeighborPathLocalParameterCount L) one_ne_zero (fun _ => 0))
  have hgood : ∀ᵐ p ∂(centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1),
      p ∈ nearestNeighborPathLocalMaximalSet L := ae_iff.mpr (hμ hnull)
  filter_upwards [hgood] with p hp
  refine ⟨?_,RHTower.nearestNeighborPath_permanentLocalityHaarSeparation hL hp hsep⟩
  let n := L*2
  let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
  let d := RHTower.nearestNeighborPathProjectiveDimension L
  let e : (Fin n → Bool) ≃ Fin (d+1) := (pairQubitPathConfigurationEquiv L).symm.trans
    (RHTower.nearestNeighborPathConfigChoiEquiv L)
  have hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i)) :=
    (RHTower.pairQubitProjectivePauliSeed_maximallyProjective hp).comp_equiv e.symm
  obtain ⟨S,hS,hh⟩ := spectral_sign_window_occupation e H hmax
  refine ⟨S,hS,?_⟩
  intro A T hT
  let r := excursionGateBudget n
  let M := (r+1)^r
  let m := 1/(40*(‖(H : Reg n)‖+1))
  have hm : 0 < m := by dsimp [m]; positivity
  have hs : ‖(H : Reg n)‖ * m ≤ 1/40 := by
    dsimp [m]; rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  let W := translatedExcursionWidth n ‖(H : Reg n)‖
  have hcount : plateauGridCount W m = M := by
    change ⌈(((M-1 : ℕ) : ℝ)*m)/m⌉₊ + 1 = M
    rw [mul_div_cancel_right₀ _ hm.ne', Nat.ceil_natCast]
    have hp' : 0 < M := by dsimp [M]; positivity
    omega
  have hd : 2^n = 4^L := by dsimp [n]; rw [mul_comm L 2, pow_mul]; norm_num
  have hdim : d = 2^n-1 := by
    have h := RHTower.nearestNeighborPathProjectiveDimension_add_one L
    rw [← hd] at h; dsimp [d]; omega
  have he' : atMostQuarterCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) <
      ((2^d : ℕ) : ℝ) := by simpa only [hdim] using he
  have hN : M * M * (atMostQuarterCircuitNet n r).card < 2^d := by
    rw [show M*M = (r+1)^(2*r) by rw [two_mul,pow_add]]
    exact translated_excursion_square_card (by dsimp [n];omega) he'
  let V := volume.real (circuitWindowHits (H : Reg n) r W ∩ Icc A (A+T))
  let N : ℝ := ((atMostQuarterCircuitNet n r).card : ℝ)
  have hsmall : (M:ℝ)*(M:ℝ)*N ≤ (2:ℝ)^d := by dsimp only [N]; exact_mod_cast hN.le
  have hobs := hh r W m hm hs A T hT
  rw [hcount] at hobs
  change (2:ℝ)^d * V ≤ (M:ℝ)*N*(T+S) at hobs
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have ht : (M:ℝ)*V ≤ T+S := by
    by_cases hMN : 0 < (M:ℝ)*N
    · apply le_of_mul_le_mul_left _ hMN
      calc
        (M:ℝ)*N*((M:ℝ)*V) = ((M:ℝ)*(M:ℝ)*N)*V := by ring
        _ ≤ (2:ℝ)^d*V := mul_le_mul_of_nonneg_right hsmall hV
        _ ≤ _ := hobs
    · have hz : (M:ℝ)*N = 0 := le_antisymm (le_of_not_gt hMN) (by dsimp [N]; positivity)
      rw [hz, zero_mul] at hobs
      have hzero : V = 0 := le_antisymm (nonpos_of_mul_nonpos_right hobs (by positivity)) hV
      rw [hzero,mul_zero]; linarith
  simpa only [M,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using ht

#print axioms gaussianPath_rare_circuitWindowHits_and_permanentLocality

end
end GaloisForLFunctions.HTGeometry
