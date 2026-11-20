import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid
import GaloisForLFunctions.RHTower.PairQubitProjectiveSeedLocalCompilerData

/-!
# Long excursions away from continuous two-qubit circuits

At each sample, translate the same circuit net by the inverse physical
increment. A single anchored spectral reflection avoids the entire union.
The norm speed of the Hamiltonian extends the certificate between samples.
-/

open Set Topology MeasureTheory
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev QMat (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- One choice of spectral signs works simultaneously for arbitrary unitary
increments at every sample. The circuit and its global phase are free to
change from sample to sample. -/
theorem exists_reflection_avoiding_translated_circuits {n d s M : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (U : Fin M → Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hcard : M * (atMostQuarterCircuitNet n s).card < 2^d) :
    ∃ x : Fin d → Bool, ∀ j : Fin M, ∀ c : ℂ, ‖c‖ = 1 →
      ∀ C : TwoQubitCircuit n, C.gateCount ≤ s → (3/20 : ℝ) <
        ‖anchoredSpectralBooleanReflection e V x * (U j : QMat n) - c • (C.eval : QMat n)‖ := by
  classical
  let net := atMostQuarterCircuitNet n s
  let targets := (Finset.univ (α := Fin M) ×ˢ net).image
    (fun p => (p.2 : QMat n) * (((U p.1)⁻¹) : QMat n))
  have hc : targets.card < Fintype.card (Fin d → Bool) := by
    apply Finset.card_image_le.trans_lt
    simpa only [Finset.card_product, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fun, Fintype.card_bool, net] using hcard
  obtain ⟨x, hx⟩ := exists_projectively_far_from_small_net
    (anchoredSpectralBooleanReflection e V) 1 (2/5)
    (fun hxy c hc => anchoredSpectralBooleanReflection_projective_separated e V hxy c hc)
    (by norm_num) targets hc
  refine ⟨x, ?_⟩
  intro j c hc C hC
  obtain ⟨W, hW, hCW⟩ := atMostQuarterCircuitNet_cover C hC
  have hm : (W : QMat n) * ((U j)⁻¹ : QMat n) ∈ targets :=
    Finset.mem_image.mpr ⟨(j,W), Finset.mem_product.mpr ⟨Finset.mem_univ _,hW⟩,rfl⟩
  have hfar := hx _ hm c hc
  let B := anchoredSpectralBooleanReflection e V x
  have he : (B - c • ((W : QMat n) * ((U j)⁻¹ : QMat n))) * (U j : QMat n) =
      B * (U j : QMat n) - c • (W : QMat n) := by
    rw [sub_mul, Matrix.smul_mul, mul_assoc]
    have hh : ((U j)⁻¹ : QMat n) * (U j : QMat n) = 1 :=
      congrArg Subtype.val (inv_mul_cancel (U j))
    rw [hh, mul_one]
  change (2/5 : ℝ) < ‖B - c • ((W : QMat n) * ((U j)⁻¹ : QMat n))‖ at hfar
  rw [← CStarRing.norm_mul_coe_unitary _ (U j), he] at hfar
  have hmove : ‖c • (C.eval : QMat n) - c • (W : QMat n)‖ ≤ 1/4 := by
    rw [← smul_sub, norm_smul, hc, one_mul]
    exact hCW
  have ht := norm_sub_le_norm_sub_add_norm_sub (B * (U j : QMat n))
    (c • (C.eval : QMat n)) (c • (W : QMat n))
  change 3/20 < ‖B * (U j : QMat n) - c • (C.eval : QMat n)‖
  linarith only [ht,hfar,hmove]

/-- A chosen spectral sign pattern recurs syndetically up to global phase. -/
private theorem syndetic_approach_spectral_signs {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) {H : QMat n} (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy (fun i => hH.eigenvalues (e.symm i)))
    (x : Fin d → Bool) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ a : ℝ, ∃ u ∈ Icc a (a+G), ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖unitaryEvolution H u - z • anchoredSpectralBooleanReflection e
        (hermitianEigenbasisUnitary hH) x‖ < 1/40 := by
  let V := hermitianEigenbasisUnitary hH
  let B := anchoredSpectralBooleanReflection e V x
  let O := (projectiveSpectralMatrix e V) ⁻¹' Metric.ball B (1/40 : ℝ)
  have ho : IsOpen O := Metric.isOpen_ball.preimage (continuous_projectiveSpectralMatrix e V)
  have hn : O.Nonempty := by
    refine ⟨anchoredBooleanProjectivePhase x, ?_⟩
    simp [O, B, Metric.mem_ball, projectiveSpectralMatrix_anchoredBooleanProjectivePhase]
  obtain ⟨G,hG,hh⟩ := denseAddOrbit_open_hits_syndetically
    (RHTower.projectivePhysicalPhaseFlowHom (fun i => hH.eigenvalues (e.symm i)))
    (RHTower.denseRange_projectivePhysicalPhaseFlowHom _ hmax) ho hn
  refine ⟨G,hG,?_⟩
  intro a
  obtain ⟨u,hu,ho'⟩ := hh a
  let z := Complex.exp (-(Complex.I * (u * hH.eigenvalues (e.symm 0))))
  have hz : ‖z‖ = 1 := by simp [z, Complex.norm_exp]
  refine ⟨u,hu,z,hz,?_⟩
  rw [unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix e hH]
  change ‖z • _ - z • B‖ < 1/40
  rw [← smul_sub, norm_smul, hz, one_mul]
  exact ho'

/-- The closed interval has prescribed width W. The entropy price of its
duration is one translated net per time sample. -/
theorem translatedNet_physical_hard_window {n d s : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (QMat n))
    (hmax : MaximallyProjectiveEnergy (fun i => (Matrix.isHermitian_iff_isSelfAdjoint.mpr H.2).eigenvalues (e.symm i)))
    (W mesh : ℝ) (hm : 0 < mesh) (hspeed : ‖(H : QMat n)‖ * mesh ≤ 1/40)
    (hcard : plateauGridCount W mesh * (atMostQuarterCircuitNet n s).card < 2^d) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ a : ℝ, ∃ u ∈ Icc a (a+G), ∀ t ∈ Icc u (u+W),
      ProjectiveCircuitSeparated n (1/10 : ℝ) s (unitaryEvolution (H : QMat n) t) := by
  let τ (j : Fin (plateauGridCount W mesh)) : ℝ := (j.val : ℝ) * mesh
  let U (j : Fin (plateauGridCount W mesh)) : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
    ⟨unitaryEvolution (H : QMat n) (τ j), unitaryEvolution_mem_unitary H.2 _⟩
  let V := hermitianEigenbasisUnitary (Matrix.isHermitian_iff_isSelfAdjoint.mpr H.2)
  obtain ⟨x,hx⟩ := exists_reflection_avoiding_translated_circuits e V U hcard
  let B := anchoredSpectralBooleanReflection e V x
  obtain ⟨G,hG,hh⟩ := syndetic_approach_spectral_signs e (Matrix.isHermitian_iff_isSelfAdjoint.mpr H.2) hmax x
  refine ⟨G,hG,?_⟩
  intro a
  obtain ⟨u,hu,z,hz,hclose⟩ := hh a
  refine ⟨u,hu,?_⟩
  intro t ht c hc C hC
  obtain ⟨j,hj⟩ := exists_plateauGrid_near hm u ht
  let v := u + τ j
  have hstep : ‖unitaryEvolution (H : QMat n) t - unitaryEvolution H v‖ ≤ 1/40 :=
    (norm_unitaryEvolution_time_sub_le H.2 t v).trans
      ((mul_le_mul_of_nonneg_left hj (norm_nonneg _)).trans hspeed)
  have hprod : unitaryEvolution (H : QMat n) u * (U j : QMat n) =
      unitaryEvolution H v := by
    simpa only [v, add_sub_cancel_right] using unitaryEvolution_sub_mul H v (τ j)
  have hnear : ‖unitaryEvolution (H : QMat n) v - z • (B * (U j : QMat n))‖ < 1/40 := by
    rw [← hprod, ← Matrix.smul_mul, ← sub_mul, CStarRing.norm_mul_coe_unitary]
    exact hclose
  have hfar := hx j (z⁻¹*c) (by rw [norm_mul,norm_inv,hz,hc,inv_one,one_mul]) C hC
  have hfactor : z • (B * (U j : QMat n) - (z⁻¹*c) • (C.eval : QMat n)) =
      z • (B * (U j : QMat n)) - c • (C.eval : QMat n) := by
    rw [smul_sub, smul_smul, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)), one_mul]
  have hfar' : 3/20 < ‖z • (B * (U j : QMat n)) - c • (C.eval : QMat n)‖ := by
    rw [← hfactor, norm_smul, hz, one_mul]
    exact hfar
  have htri := norm_sub_le_norm_sub_add_norm_sub (z • (B * (U j : QMat n)))
    (unitaryEvolution (H : QMat n) v) (c • (C.eval : QMat n))
  have htri' := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution (H : QMat n) v)
    (unitaryEvolution H t) (c • (C.eval : QMat n))
  rw [norm_sub_rev] at hnear hstep
  linarith only [htri,htri',hnear,hstep,hfar']

/-- Increasing the allowed gate count from r to 2r pays for (r+1)^r
different translations of the entire smaller circuit net. -/
private theorem translated_net_entropy_budget {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ((r+1 : ℝ)^r) * atMostQuarterCircuitEntropyBound n r ≤
      atMostQuarterCircuitEntropyBound n (2*r) := by
  let q (i : ℕ) : ℝ := ((n*n : ℕ) : ℝ)^i * (1+16*(i : ℝ))^(32*i)
  let b (i : ℕ) := 1 + q i
  have hn' : 1 ≤ ((n*n : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega : n ≠ 0) (by omega : n ≠ 0))
  have hq (i : ℕ) : 1 ≤ q i :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn' _)
      (one_le_pow₀ (by linarith only [Nat.cast_nonneg (α := ℝ) i] : (1:ℝ) ≤ 1+16*(i:ℝ)) _)
  have hterm (i : ℕ) : (r+1 : ℝ)^r * b i ≤ b (r+i) := by
    let v : ℝ := 1+16*((r+i : ℕ) : ℝ)
    have hv : 2 ≤ v := by dsimp [v]; push_cast; exact_mod_cast (by omega : 2 ≤ 1+16*(r+i))
    have hrbase : (r:ℝ)+1 ≤ v := by dsimp [v]; push_cast; linarith only [Nat.cast_nonneg (α := ℝ) i,Nat.cast_nonneg (α := ℝ) r]
    have hrest : (r+1 : ℝ)^r * 2 ≤ v^(32*r) := calc
      _ ≤ v^r * v := mul_le_mul (pow_le_pow_left₀ (by positivity) hrbase _) hv (by norm_num) (by exact pow_nonneg (by linarith only [hv]) _)
      _ = v^(r+1) := (pow_succ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
    have grow : q i ≤ ((n*n : ℕ) : ℝ)^(r+i) * v^(32*i) := by
      unfold q
      apply mul_le_mul (pow_le_pow_right₀ hn' (by omega))
      · apply pow_le_pow_left₀ (by positivity)
        dsimp [v]; push_cast; linarith only [Nat.cast_nonneg (α := ℝ) i,Nat.cast_nonneg (α := ℝ) r]
      · positivity
      · positivity
    have hnew : v^(32*r) * (((n*n : ℕ) : ℝ)^(r+i) * v^(32*i)) = q (r+i) := by
      unfold q
      rw [Nat.mul_add, pow_add]
      change v^(32*r) * _ = _ * (v^(32*r) * v^(32*i))
      ring
    calc
      _ ≤ (r+1:ℝ)^r * (2 * q i) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [b]; linarith only [hq i]
      _ = ((r+1:ℝ)^r * 2) * q i := by ring
      _ ≤ v^(32*r) * (((n*n : ℕ) : ℝ)^(r+i) * v^(32*i)) :=
        mul_le_mul hrest grow (by linarith only [hq i]) (by positivity)
      _ ≤ b (r+i) := by rw [hnew]; dsimp [b]; linarith
  change _ * (∑ i ∈ Finset.range (r+1), b i) ≤ ∑ i ∈ Finset.range (2*r+1), b i
  rw [Finset.mul_sum, show 2*r+1 = r+(r+1) by omega, Finset.sum_range_add]
  have h0 : 0 ≤ ∑ i ∈ Finset.range r, b i :=
    Finset.sum_nonneg fun i _ => by dsimp [b]; linarith only [hq i]
  exact (Finset.sum_le_sum fun i _ => hterm i).trans (le_add_of_nonneg_left h0)

/-- Number of arbitrary continuous two-qubit gates excluded throughout an
excursion. The net entropy saved by halving the budget pays for time samples. -/
def excursionGateBudget (n : ℕ) := nearHilbertContinuousCircuitBudget n / 2

/-- Physical duration in units of inverse generator speed. -/
def translatedExcursionWidth (n : ℕ) (speed : ℝ) : ℝ :=
  let r := excursionGateBudget n
  (((r+1)^r - 1 : ℕ) : ℝ) * (1/(40*(speed+1)))

private theorem translated_excursion_card {n d : ℕ} (hn : 1 ≤ n)
    (he : atMostQuarterCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) <
      ((2^d : ℕ) : ℝ)) :
    let r := excursionGateBudget n
    (r+1)^r * (atMostQuarterCircuitNet n r).card < 2^d := by
  let s := nearHilbertContinuousCircuitBudget n
  let r := excursionGateBudget n
  have hhalf : 2*r ≤ s := by dsimp [r, excursionGateBudget,s]; omega
  have hmono : atMostQuarterCircuitEntropyBound n (2*r) ≤ atMostQuarterCircuitEntropyBound n s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => by positivity)
  have htrade : ((r+1 : ℝ)^r) * atMostQuarterCircuitEntropyBound n r ≤
      atMostQuarterCircuitEntropyBound n (2*r) := by
    by_cases hz : r = 0
    · simp [hz]
    · exact translated_net_entropy_budget hn (by omega)
  have h := ((mul_le_mul_of_nonneg_left (atMostQuarterCircuitNet_card_real_le n r)
    (by positivity : 0 ≤ (r+1:ℝ)^r)).trans (htrade.trans hmono)).trans_lt he
  change (r+1)^r * (atMostQuarterCircuitNet n r).card < 2^d
  exact_mod_cast h

/-- Every sufficiently long ordinary Gaussian nearest-neighbour path almost
surely has recurrent intervals of explicit width on which every continuous
two-qubit circuit of near-Hilbert size fails at fixed operator error, while
one local experiment separates the same evolution from Haar at every time. -/
theorem gaussianPath_translatedCircuitExcursions_and_permanentLocality :
    ∀ᶠ L : ℕ in Filter.atTop,
    ∀ᵐ p ∂(centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1),
      let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
      (∃ G : ℝ, 0 ≤ G ∧ ∀ a : ℝ, ∃ u ∈ Icc a (a+G),
        ∀ t ∈ Icc u (u + translatedExcursionWidth (L*2) ‖(H : QMat (L*2))‖),
          ProjectiveCircuitSeparated (L*2) (1/10 : ℝ) (excursionGateBudget (L*2))
            (unitaryEvolution (H : QMat (L*2)) t)) ∧
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
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (nearestNeighborPathLocalParameterCount L) → ℝ)) :=
    by simpa [centredProductGaussian] using (productGaussian_absolutelyContinuous
      (nearestNeighborPathLocalParameterCount L) one_ne_zero (fun _ => 0))
  have hgood : ∀ᵐ p ∂(centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1),
      p ∈ nearestNeighborPathLocalMaximalSet L :=
    MeasureTheory.ae_iff.mpr (hμ hnull)
  filter_upwards [hgood] with p hp
  refine ⟨?_, RHTower.nearestNeighborPath_permanentLocalityHaarSeparation hL hp hsep⟩
  let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
  let d := RHTower.nearestNeighborPathProjectiveDimension L
  let e : (Fin (L*2) → Bool) ≃ Fin (d+1) := (pairQubitPathConfigurationEquiv L).symm.trans
    (RHTower.nearestNeighborPathConfigChoiEquiv L)
  have hmax : MaximallyProjectiveEnergy (fun i =>
      (Matrix.isHermitian_iff_isSelfAdjoint.mpr H.2).eigenvalues (e.symm i)) :=
    (RHTower.pairQubitProjectivePauliSeed_maximallyProjective hp).comp_equiv e.symm
  have hd : 2^(L*2) = 4^L := by rw [mul_comm L 2, pow_mul]; norm_num
  have hdim : d = 2^(L*2)-1 := by
    have h := RHTower.nearestNeighborPathProjectiveDimension_add_one L
    rw [← hd] at h
    dsimp [d]
    omega
  have he' : atMostQuarterCircuitEntropyBound (L*2) (nearHilbertContinuousCircuitBudget (L*2)) <
      ((2^d : ℕ) : ℝ) := by simpa only [hdim] using he
  let r := excursionGateBudget (L*2)
  let m := 1/(40*(‖(H : QMat (L*2))‖+1))
  have hm : 0 < m := by dsimp [m]; positivity
  have hs : ‖(H : QMat (L*2))‖ * m ≤ 1/40 := by
    dsimp [m]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  apply translatedNet_physical_hard_window e H hmax _ m hm hs
  have hcount : plateauGridCount (translatedExcursionWidth (L*2) ‖(H : QMat (L*2))‖) m =
      (r+1)^r := by
    change ⌈((((r+1)^r-1 : ℕ) : ℝ)*m)/m⌉₊ + 1 = _
    rw [mul_div_cancel_right₀ _ hm.ne', Nat.ceil_natCast]
    have hp : 0 < (r+1)^r := by positivity
    omega
  rw [hcount]
  exact translated_excursion_card (by omega) he'

#print axioms gaussianPath_translatedCircuitExcursions_and_permanentLocality

end
end GaloisForLFunctions.HTGeometry
