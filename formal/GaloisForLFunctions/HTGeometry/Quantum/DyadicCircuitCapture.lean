import GaloisForLFunctions.HTGeometry.Quantum.AttainedOrbitCircuitMaximum
import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity
import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceAvoidance

/-!
# Conditional rarity of circuit shortcuts at doubled observation times

Adding independent half turns to the relative eigenphases leaves the doubled
unitary fixed. Within one such family a fixed circuit-net point captures at
most one sign choice. The resulting bound survives conditioning on every
measurable event at the doubled phase, and iterates along the dyadic clock.
-/

open Set MeasureTheory Filter Complex
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
private abbrev Tor (d : ℕ) := Fin d → UnitAddCircle

/-- Squaring the full propagator doubles its relative eigenphases. -/
def doubleSpectralPhase (x : Tor d) : Tor d := (2 : ℤ) • x

private theorem double_preserves : MeasurePreserving (doubleSpectralPhase (d := d)) volume volume :=
  Measure.measurePreserving_zsmul volume (by norm_num : (2 : ℤ) ≠ 0)

private theorem double_sign_translate (θ : Tor d) (b : Fin d → Bool) :
    doubleSpectralPhase (θ + anchoredBooleanProjectivePhase b) = doubleSpectralPhase θ := by
  have hhalf : ((1/2 : ℝ) : UnitAddCircle) + ((1/2 : ℝ) : UnitAddCircle) = 0 := by
    rw [← AddCircle.coe_add,show (1/2:ℝ)+1/2 = 1 by norm_num]
    exact AddCircle.coe_period (1:ℝ)
  have hz : (2 : ℤ) • anchoredBooleanProjectivePhase b = 0 := by
    funext i
    rw [two_zsmul]
    cases hb : b i
    · simp [anchoredBooleanProjectivePhase,hb]
    · simpa [anchoredBooleanProjectivePhase,hb] using hhalf
  rw [doubleSpectralPhase,zsmul_add,hz,add_zero]
  rfl

private theorem sign_chord (θ : Tor d) (b c : Fin d → Bool) {i : Fin d} (hi : b i ≠ c i) :
    ‖(fourier 1 ((θ+anchoredBooleanProjectivePhase b) i) : ℂ)
      - fourier 1 ((θ+anchoredBooleanProjectivePhase c) i)‖ = 2 := by
  have hf : (fourier 1 (((1/2:ℝ) : UnitAddCircle)) : ℂ) = -1 := by
    rw [fourier_one]; exact coe_toCircle_half
  simp only [Pi.add_apply,fourier_one_add,← mul_sub,norm_mul,norm_fourier_one,one_mul]
  cases hb : b i <;> cases hc : c i
  · exact (hi (hb.trans hc.symm)).elim
  · norm_num [anchoredBooleanProjectivePhase,hb,hc,hf]
  · norm_num [anchoredBooleanProjectivePhase,hb,hc,hf]
  · exact (hi (hb.trans hc.symm)).elim

/-- Even after revealing an arbitrary measurable event at the doubled phase,
a tube around one operator captures at most one of the independent sign lifts. -/
private theorem conditional_point_tube {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (W : Reg n)
    (F : Set (Tor d)) (hF : MeasurableSet F) :
    (2:ℝ)^d * volume.real
      (projectiveSpectralPointTube e V W (2/5:ℝ) ∩ doubleSpectralPhase ⁻¹' F) ≤ volume.real F := by
  let K := projectiveSpectralPointTube e V W (2/5:ℝ) ∩ doubleSpectralPhase ⁻¹' F
  let A (b : Fin d → Bool) := (fun θ : Tor d => θ+anchoredBooleanProjectivePhase b) ⁻¹' K
  have hm : MeasurableSet K := (isClosed_projectiveSpectralPointTube e V W _).measurableSet.inter
    (hF.preimage double_preserves.measurable)
  have hmA (b) : MeasurableSet (A b) := hm.preimage (measurable_id.add_const _)
  have hv (b) : volume.real (A b) = volume.real K :=
    (measurePreserving_add_right volume _).measureReal_preimage hm.nullMeasurableSet
  have hdis : Pairwise (fun b c => Disjoint (A b) (A c)) := by
    intro b c hbc
    rw [Set.disjoint_left]
    intro θ hb hc
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hbc
    have h := projectiveSpectralPointTube_pair_chord e V W (2/5:ℝ) hb.1 hc.1 i
    rw [sign_chord θ b c hi] at h
    norm_num at h
  have hsub : (⋃ b, A b) ⊆ doubleSpectralPhase ⁻¹' F := by
    intro θ hθ
    obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hθ
    have h : doubleSpectralPhase (θ+anchoredBooleanProjectivePhase b) ∈ F := hb.2
    rwa [double_sign_translate] at h
  calc
    _ = ∑ b : Fin d → Bool, volume.real (A b) := by
      simp only [hv,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
        Fintype.card_bool,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,K]
    _ = volume.real (⋃ b, A b) := (measureReal_iUnion_fintype hdis hmA).symm
    _ ≤ volume.real (doubleSpectralPhase ⁻¹' F) := measureReal_mono hsub
    _ = volume.real F := double_preserves.measureReal_preimage hF.nullMeasurableSet

/-- Conditional circuit capture under arbitrary future information at the
doubled phase. Gate locations, gates and global phase may depend on the root. -/
theorem conditional_doubled_phase_circuit_capture {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (s : ℕ) (F : Set (Tor d)) (hF : MeasurableSet F) :
    (2:ℝ)^d * volume.real
      (projectiveContinuousCircuitCaptureTarget e V s (1/10:ℝ) ∩ doubleSpectralPhase ⁻¹' F) ≤
      ((atMostQuarterCircuitNet n s).card : ℝ) * volume.real F := by
  let N := atMostQuarterCircuitNet n s
  let A (W : ↥N) := projectiveSpectralPointTube e V (W.val : Reg n) (2/5:ℝ) ∩ doubleSpectralPhase ⁻¹' F
  have hs : projectiveContinuousCircuitCaptureTarget e V s (1/10:ℝ) ∩ doubleSpectralPhase ⁻¹' F ⊆
      ⋃ W, A W := by
    rintro θ ⟨hθ,hf⟩
    obtain ⟨c,hc,C,hC,hcheap⟩ := (mem_projectiveContinuousCircuitCaptureTarget_iff e V s _ θ).mp hθ
    obtain ⟨W,hW,hCW⟩ := atMostQuarterCircuitNet_cover C hC
    refine Set.mem_iUnion.mpr ⟨⟨W,hW⟩,(mem_projectiveSpectralPointTube_iff e V _ _ θ).mpr ⟨c,hc,?_⟩,hf⟩
    have hnet : ‖c • (C.eval : Reg n) - c • (W : Reg n)‖ ≤ 1/4 := by
      rw [← smul_sub,norm_smul,hc,one_mul]
      simpa only [dist_eq_norm] using hCW
    linarith only [norm_sub_le_norm_sub_add_norm_sub (projectiveSpectralMatrix e V θ)
      (c • (C.eval : Reg n)) (c • (W : Reg n)),hcheap,hnet]
  calc
    _ ≤ (2:ℝ)^d * ∑ W, volume.real (A W) :=
      mul_le_mul_of_nonneg_left ((measureReal_mono hs).trans (measureReal_iUnion_fintype_le A)) (by positivity)
    _ = ∑ W, (2:ℝ)^d * volume.real (A W) := Finset.mul_sum _ _ _
    _ ≤ ∑ _W : ↥N, volume.real F := Finset.sum_le_sum fun W _ => conditional_point_tube e V _ F hF
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,N]

/-- Phase points admitting an affordable circuit at every observation in a
run of successive doublings, including the initial phase for a nonempty run. -/
def dyadicCircuitCapture {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (s : ℕ) : ℕ → Set (Tor d)
  | 0 => univ
  | k+1 => projectiveContinuousCircuitCaptureTarget e V s (1/10:ℝ) ∩
      doubleSpectralPhase ⁻¹' dyadicCircuitCapture e V s k

private theorem dyadicCircuitCapture_closed {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (s k : ℕ) :
    IsClosed (dyadicCircuitCapture e V s k) := by
  induction k with
  | zero => exact isClosed_univ
  | succ k ih =>
    exact (isClosed_projectiveContinuousCircuitCaptureTarget e V s _).inter
      (ih.preimage (by unfold doubleSpectralPhase; fun_prop))

/-- Each additional dyadic observation contributes a fresh circuit-net
factor divided by the full projective sign count. -/
theorem volume_dyadicCircuitCapture_le {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (s k : ℕ) :
    volume.real (dyadicCircuitCapture e V s k) ≤
      (((atMostQuarterCircuitNet n s).card : ℝ)/(2:ℝ)^d)^k := by
  let p := ((atMostQuarterCircuitNet n s).card : ℝ)/(2:ℝ)^d
  have hp : 0 ≤ p := by dsimp [p]; positivity
  change _ ≤ p^k
  induction k with
  | zero => simp only [dyadicCircuitCapture,RHTower.measureReal_torus_univ,pow_zero,le_refl]
  | succ k ih =>
    have hc := conditional_doubled_phase_circuit_capture e V s _ (dyadicCircuitCapture_closed e V s k).measurableSet
    calc
      _ ≤ p * volume.real (dyadicCircuitCapture e V s k) := by
        dsimp only [p]
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^d)).mpr
        rw [mul_comm]
        exact hc
      _ ≤ p*p^k := mul_le_mul_of_nonneg_left ih hp
      _ = _ := (pow_succ' p k).symm

#print axioms conditional_doubled_phase_circuit_capture
#print axioms volume_dyadicCircuitCapture_le

/-- Actual observation times at which the physical circuit threshold
is met at all k dyadic multiples of the time. -/
def physicalDyadicCircuitHits (H : selfAdjoint (Reg n)) (s k : ℕ) : Set ℝ :=
  {t | ∀ j < k, HasProjectiveCircuitApproximation n (1/10:ℝ) s
    (unitaryEvolution (H : Reg n) ((2:ℝ)^j*t))}

private theorem physical_dyadic_preimage {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (s k : ℕ) :
    physicalDyadicCircuitHits H s k =
      finiteClockPhasePoint (RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i))) ⁻¹'
        dyadicCircuitCapture e (hermitianEigenbasisUnitary H.2.isHermitian) s k := by
  let E := fun i => H.2.isHermitian.eigenvalues (e.symm i)
  let Φ := RHTower.projectivePhysicalPhaseFlowHom E
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  have hd (t : ℝ) : doubleSpectralPhase (Φ t) = Φ (2*t) := by
    rw [doubleSpectralPhase,two_zsmul,two_mul,map_add]
  ext t
  change (∀ j < k, HasProjectiveCircuitApproximation n (1/10:ℝ) s
    (unitaryEvolution (H : Reg n) ((2:ℝ)^j*t))) ↔ Φ t ∈ dyadicCircuitCapture e V s k
  induction k generalizing t with
  | zero => simp [dyadicCircuitCapture]
  | succ k ih =>
    change _ ↔ Φ t ∈ projectiveContinuousCircuitCaptureTarget e V s _ ∧
      doubleSpectralPhase (Φ t) ∈ dyadicCircuitCapture e V s k
    rw [hd, ← ih]
    have h0 := physical_circuit_approximation_iff_spectral_capture e H s (1/10:ℝ) t
    have htime (j : ℕ) : (2:ℝ)^j*(2*t) = (2:ℝ)^(j+1)*t := by rw [pow_succ]; ring
    constructor
    · intro h
      refine ⟨h0.mp (by simpa only [pow_zero,one_mul] using h 0 (Nat.zero_lt_succ _)),?_⟩
      intro j hj
      rw [htime]
      exact h (j+1) (Nat.succ_lt_succ hj)
    · rintro ⟨hfirst,hrest⟩ j hj
      cases j with
      | zero => simpa only [pow_zero,one_mul] using h0.mpr hfirst
      | succ j =>
        rw [← htime]
        exact hrest j (Nat.lt_of_succ_lt_succ hj)

/-- One-sided time occupation of k successive shortcuts on the same
maximally projective static orbit. -/
theorem physical_dyadic_capture_limsup_le {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i)))
    (s k : ℕ) :
    atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ) (physicalDyadicCircuitHits H s k)) ≤
      ENNReal.ofReal ((((atMostQuarterCircuitNet n s).card : ℝ)/(2:ℝ)^d)^k) := by
  let E := fun i => H.2.isHermitian.eigenvalues (e.symm i)
  let ω := RHTower.zeroProjectiveFrequency E
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let A := dyadicCircuitCapture e V s k
  have hc : IsClosed A := dyadicCircuitCapture_closed e V s k
  have heq (T : ℝ) : (windowProbabilityMeasure T : Measure ℝ) (physicalDyadicCircuitHits H s k) =
      (clockPhaseWindowLaw ω T : Measure (Tor d)) A := by
    rw [physical_dyadic_preimage e H s k,clockPhaseWindowLaw,ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (finiteClockPhasePoint_continuous ω).measurable hc.measurableSet]
  simp only [heq]
  apply (oneSided_closedTarget_limsup_le_volume ω
    (RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent E hmax) hc).trans
  have h := ENNReal.ofReal_le_ofReal (volume_dyadicCircuitCapture_le e V s k)
  rwa [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h

/-- Spectral histories with k hard doublings followed by a prescribed event. -/
def dyadicHardPrehistory {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (s : ℕ) (F : Set (Tor d)) : ℕ → Set (Tor d)
  | 0 => F
  | k+1 => (projectiveContinuousCircuitCaptureTarget e V s (1/10:ℝ))ᶜ ∩
      doubleSpectralPhase ⁻¹' dyadicHardPrehistory e V s F k

private theorem measurable_hard_prehistory {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (s : ℕ) (F : Set (Tor d)) (hF : MeasurableSet F)
    (k : ℕ) : MeasurableSet (dyadicHardPrehistory e V s F k) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    exact (isClosed_projectiveContinuousCircuitCaptureTarget e V s _).measurableSet.compl.inter
      (ih.preimage double_preserves.measurable)

/-- Conditioning on any final event, including a recurrence, leaves
a quantitative fraction of histories hard at every preceding doubling. -/
theorem volume_dyadicHardPrehistory_ge {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (s : ℕ) (F : Set (Tor d)) (hF : MeasurableSet F) (k : ℕ) :
    (max 0 (1-((atMostQuarterCircuitNet n s).card : ℝ)/(2:ℝ)^d))^k * volume.real F ≤
      volume.real (dyadicHardPrehistory e V s F k) := by
  let A := projectiveContinuousCircuitCaptureTarget e V s (1/10:ℝ)
  let α := ((atMostQuarterCircuitNet n s).card : ℝ)/(2:ℝ)^d
  let p := max 0 (1-α)
  have hp : 0 ≤ p := le_max_left _ _
  change p^k * volume.real F ≤ _
  induction k with
  | zero => simp [dyadicHardPrehistory]
  | succ k ih =>
    let G := dyadicHardPrehistory e V s F k
    let E := doubleSpectralPhase ⁻¹' G
    have hm := measurable_hard_prehistory e V s F hF k
    have hE : volume.real E = volume.real G := double_preserves.measureReal_preimage hm.nullMeasurableSet
    have hpart : E ⊆ (A ∩ E) ∪ (Aᶜ ∩ E) := by
      intro x hx
      by_cases h : x ∈ A
      · exact Or.inl ⟨h,hx⟩
      · exact Or.inr ⟨h,hx⟩
    have hsum := (measureReal_mono (μ := volume) hpart).trans (measureReal_union_le _ _)
    rw [hE] at hsum
    have hcap : volume.real (A ∩ E) ≤ α * volume.real G := by
      dsimp only [α]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^d)).mpr
      rw [mul_comm]
      exact conditional_doubled_phase_circuit_capture e V s G hm
    have hgood : p * volume.real G ≤ volume.real (Aᶜ ∩ E) := by
      rcases le_total 0 (1-α) with h | h
      · rw [show p = 1-α from max_eq_right h,sub_mul,one_mul]
        linarith only [hsum,hcap]
      · rw [show p = 0 from max_eq_left h,zero_mul]
        exact ENNReal.toReal_nonneg
    rw [pow_succ',mul_assoc]
    exact (mul_le_mul_of_nonneg_left ih hp).trans hgood

/-- A stationary one-sided physical clock sees the same lower bound for
every open terminal spectral event. -/
theorem physical_hard_prehistory_liminf {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i)))
    (s k : ℕ) (F : Set (Tor d)) (hF : IsOpen F) :
    let E := fun i => H.2.isHermitian.eigenvalues (e.symm i)
    let V := hermitianEigenbasisUnitary H.2.isHermitian
    ENNReal.ofReal ((max 0 (1-((atMostQuarterCircuitNet n s).card : ℝ)/(2:ℝ)^d))^k * volume.real F) ≤
      atTop.liminf (fun T => (clockPhaseWindowLaw (RHTower.zeroProjectiveFrequency E) T : Measure (Tor d))
        (dyadicHardPrehistory e V s F k)) := by
  let E := fun i => H.2.isHermitian.eigenvalues (e.symm i)
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  have ho (j : ℕ) : IsOpen (dyadicHardPrehistory e V s F j) := by
    induction j with
    | zero => exact hF
    | succ j ih =>
      exact (isClosed_projectiveContinuousCircuitCaptureTarget e V s _).isOpen_compl.inter
        (ih.preimage (by unfold doubleSpectralPhase; fun_prop))
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (clockPhaseWindowLaw_tendsto_haar _ (RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent E hmax))
    (ho k)
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hlim
  refine le_trans ?_ hlim
  have h := ENNReal.ofReal_le_ofReal (volume_dyadicHardPrehistory_ge e V s F hF.measurableSet k)
  rwa [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h

#print axioms volume_dyadicHardPrehistory_ge
#print axioms physical_hard_prehistory_liminf

/-- In an ordinary static Gaussian chain, k consecutive affordable
observations on the doubling clock have upper time fraction at most
(r+1)^(−2rk), with the same H, error, and gate budget at every observation. -/
theorem gaussianPath_dyadic_short_circuit_runs :
    ∀ᶠ L : ℕ in atTop,
    ∀ᵐ p ∂(centredProductGaussian
      (Fin (StaticLocalLaboratoryComplexityGrowthLaw.nearestNeighborPathLocalParameterCount L)) 1),
      let n := L*2
      let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
      let r := excursionGateBudget n
      (∀ k : ℕ, atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ)
        (physicalDyadicCircuitHits H r k)) ≤ ENNReal.ofReal ((1/(r+1:ℝ)^(2*r))^k)) ∧
        RHTower.NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  have hcof : Tendsto (fun L : ℕ => L*2) atTop atTop := by
    rw [tendsto_atTop]; intro N; exact eventually_atTop.2 ⟨N,fun L h => by omega⟩
  filter_upwards [eventually_ge_atTop 1,hcof.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier,
    RHTower.eventually_pairQubit_twoLocalPauli_separator] with L hL hent hsep
  have hnull := (StaticLocalLaboratoryComplexityGrowthLaw.nearestNeighborPathLocalMaximalSet_dense_residual_fullMeasure (L := L) hL).2.2
  let m := StaticLocalLaboratoryComplexityGrowthLaw.nearestNeighborPathLocalParameterCount L
  have hμ : centredProductGaussian (Fin m) 1 ≪ (volume : Measure (Fin m → ℝ)) := by
    simpa [centredProductGaussian] using (productGaussian_absolutelyContinuous m one_ne_zero (fun _ => 0))
  have ha : ∀ᵐ p ∂(centredProductGaussian (Fin m) 1),
      p ∈ StaticLocalLaboratoryComplexityGrowthLaw.nearestNeighborPathLocalMaximalSet L := ae_iff.mpr (hμ hnull)
  filter_upwards [ha] with p hp
  refine ⟨fun k => ?_,RHTower.nearestNeighborPath_permanentLocalityHaarSeparation hL hp hsep⟩
  let n := L*2
  let d := 2^n-1
  let r := excursionGateBudget n
  let e : (Fin n → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hpos : 0 < (2:ℕ)^n := by positivity
                  dsimp [d]; omega))
  let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
  have hmax := (RHTower.pairQubitProjectivePauliSeed_maximallyProjective hp).comp_equiv e.symm
  apply (physical_dyadic_capture_limsup_le e H hmax r k).trans
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul,mul_comm]
  have hh := translated_excursion_square_card (n := n) (d := d) (by dsimp [n]; omega) hent
  exact_mod_cast hh.le

#print axioms gaussianPath_dyadic_short_circuit_runs

end
end GaloisForLFunctions.HTGeometry
