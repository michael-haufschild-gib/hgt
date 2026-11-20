import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline
import GaloisForLFunctions.HTGeometry.ContinuousCircuitExponentialPlateauBudgetLaw

/-!
# First robust exponential circuit threshold on a static Gaussian path

The first crossing is measured from identity by distance to a compact circuit
image. Its certification margin pays for an accurate increment compiler.
Every polynomial-size circuit is consequently excluded for an exponentially
long interval after that particular crossing.
-/

open Set Filter MeasureTheory
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Operator distance to the entire phase-saturated physical circuit budget. -/
def orbitCircuitDistance (H : selfAdjoint (Reg n)) (P : ℕ) (t : ℝ) : ℝ :=
  Metric.infDist (unitaryEvolution (H : Reg n) t) (phaseCircuitMatrixImageAtMost n P)

private theorem continuous_orbitCircuitDistance (H : selfAdjoint (Reg n)) (P : ℕ) :
    Continuous (orbitCircuitDistance H P) := by
  have hL : LipschitzWith ⟨‖(H : Reg n)‖,norm_nonneg _⟩ (unitaryEvolution (H : Reg n)) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm,Real.dist_eq]
    exact norm_unitaryEvolution_time_sub_le H.2 u v
  exact (Metric.continuous_infDist_pt _).comp hL.continuous

private theorem first_crossing (f : ℝ → ℝ) (hf : Continuous f) (c B : ℝ) (hB : 0 ≤ B)
    (hstart : ∀ t ∈ Icc 0 B, f t < c) (hreach : ∃ v, 0 ≤ v ∧ c ≤ f v) :
    ∃ σ : ℝ, B < σ ∧ f σ = c ∧ ∀ t ∈ Ico 0 σ, f t < c := by
  obtain ⟨v,hv,hvc⟩ := hreach
  have h0 := hstart 0 ⟨le_rfl,hB⟩
  obtain ⟨t,ht,hf0⟩ := intermediate_value_Icc hv hf.continuousOn (show c ∈ Icc (f 0) (f v) from ⟨h0.le,hvc⟩)
  let K := Icc 0 v ∩ f ⁻¹' {c}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  obtain ⟨σ,hσ,hmin⟩ := hK.exists_isMinOn (show K.Nonempty from ⟨t,ht,hf0⟩) continuous_id.continuousOn
  have he : f σ = c := hσ.2
  have hσB : B < σ := by
    by_contra! h
    exact (hstart σ ⟨hσ.1.1,h⟩).ne he
  refine ⟨σ,hσB,he,?_⟩
  intro u hu
  by_contra! h
  obtain ⟨s,hs,hfs⟩ := intermediate_value_Icc hu.1 hf.continuousOn
    (show c ∈ Icc (f 0) (f u) from ⟨h0.le,h⟩)
  have hmem : s ∈ K := ⟨⟨hs.1,hs.2.trans (hu.2.le.trans hσ.1.2)⟩,hfs⟩
  have hle : σ ≤ s := hmin hmem
  exact (not_lt_of_ge hle) (hs.2.trans_lt hu.2)

/-- Use the generator norm to express the compiler's exponential interval
in the original physical clock without restricting the Gaussian draw. -/
private theorem normalized_path_increment {L : ℕ} (hL : 1 ≤ L)
    (H : selfAdjoint (Reg (L*2))) (hloc : HasPauliWeightAtMost (Fin (L*2)) 2 H)
    (t : ℝ) (ht : |t| ≤ (continuousCircuitPlateauWidth L : ℝ)/(1+‖(H : Reg (L*2))‖)) :
    HasProjectiveCircuitApproximation (L*2) (1/100:ℝ) (continuousCircuitPlateauCompilerCost L)
      (unitaryEvolution (H : Reg (L*2)) t) := by
  let h := ‖(H : Reg (L*2))‖
  let m := continuousCircuitPlateauLabelCount L
  let R := continuousCircuitPlateauRepetitions L
  have hr : 0 < (R : ℝ) := by exact_mod_cast continuousCircuitPlateauRepetitions_pos L
  have hh : 0 ≤ h := norm_nonneg _
  have hx : |t*h| ≤ continuousCircuitPlateauWidth L := by
    rw [abs_mul,abs_of_nonneg hh]
    exact (mul_le_mul_of_nonneg_left (show h ≤ 1+h by linarith) (abs_nonneg t)).trans
      ((le_div_iff₀ (show 0 < 1+h by positivity)).mp ht)
  have hstrength : (1:ℝ) ≤ L+2 := by linarith only [Nat.cast_nonneg (α := ℝ) L]
  have hsmall := continuousCircuitPlateau_compiler_small hx zero_le_one hstrength
  have herr := continuousCircuitPlateau_compiler_error hx zero_le_one hstrength
  have hsmall' : |t/(R:ℝ)| * m * h ≤ 1 := by
    rw [abs_div,abs_of_pos hr]
    rw [abs_div,abs_mul,abs_of_nonneg hh,abs_of_pos hr,mul_one] at hsmall
    convert hsmall using 1 <;> ring
  obtain ⟨c,hc,C,hC,he⟩ := exists_twoLocal_projectiveTrotterCircuit_normBound
    (by omega : 2 ≤ L*2) H hloc t R (continuousCircuitPlateauRepetitions_pos L) hsmall'
  refine ⟨c,hc,C,hC.le,he.trans ?_⟩
  rw [abs_mul,abs_of_nonneg hh,one_pow,mul_one] at herr
  change 3*(m:ℝ)^3*h^2*|t| ^2 / R ≤ 1/100
  convert herr using 1 <;> ring

private theorem reaches_robust_threshold {n d P : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i)))
    (hent : atMostQuarterCircuitEntropyBound n P < ((2^d : ℕ) : ℝ)) :
    ∃ v : ℝ, 0 ≤ v ∧ 9/80 ≤ orbitCircuitDistance H P v := by
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  obtain ⟨x,hx⟩ := exists_anchoredSpectralBooleanReflection_atMostCircuit_fixedError e V hent
  let B := anchoredSpectralBooleanReflection e V x
  obtain ⟨G,_,hG⟩ := syndetic_approach_spectral_signs e H.2.isHermitian hmax x
  obtain ⟨v,hv,z,hz,hnear⟩ := hG 0
  refine ⟨v,hv.1,?_⟩
  by_contra! h
  obtain ⟨c,hc,C,hC,hcheap⟩ := (hasProjectiveCircuitApproximation_iff_infDist
    (unitaryEvolution (H : Reg n) v) P (9/80:ℝ)).mpr h.le
  have hf := hx (z⁻¹*c) (by rw [norm_mul,norm_inv,hz,hc,inv_one,one_mul]) C hC
  have hid : z • (B - (z⁻¹*c) • (C.eval : Reg n)) = z • B - c • (C.eval : Reg n) := by
    rw [smul_sub,smul_smul,← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)),one_mul]
  have hfar : 3/20 < ‖z • B - c • (C.eval : Reg n)‖ := by
    rw [← hid,norm_smul,hz,one_mul]; exact hf
  change ‖unitaryEvolution (H : Reg n) v - z • B‖ < 1/40 at hnear
  rw [norm_sub_rev] at hnear
  linarith only [norm_sub_le_norm_sub_add_norm_sub (z • B) (unitaryEvolution (H : Reg n) v)
    (c • (C.eval : Reg n)),hfar,hnear,hcheap]

/-- From identity, the first robust crossing of the exponential budget is
itself at least exponentially late in intrinsic time. Every threshold up to
half that budget has a literal first re-entry after the crossing, preceded
by an exponential exclusion interval and bounded by a Dirichlet deadline. -/
theorem gaussianPath_first_robust_saturation_and_return :
    ∀ᶠ L : ℕ in atTop,
    ∀ᵐ p ∂(centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1),
      let n := L*2
      let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
      let P := nearHilbertContinuousCircuitBudget n
      let r := excursionGateBudget n
      let B := (continuousCircuitPlateauWidth L : ℝ)/(1+‖(H : Reg n)‖)
      (∃ σ : ℝ, B < σ ∧ orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        (∀ t ∈ Icc (σ-B) (σ+B), ProjectiveCircuitSeparated n (1/10:ℝ) r (unitaryEvolution (H : Reg n) t)) ∧
        ∀ s ≤ r, ∃ v : ℝ, σ+B < v ∧ v ≤ (σ+1)*(100:ℝ)^(2^n-1) ∧
          HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution (H : Reg n) v) ∧
          ∀ t ∈ Ico σ v, ProjectiveCircuitSeparated n (1/10:ℝ) s (unitaryEvolution (H : Reg n) t)) ∧
        RHTower.NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  have hcof : Tendsto (fun L : ℕ => L*2) atTop atTop := by
    rw [tendsto_atTop]; intro N; exact eventually_atTop.2 ⟨N,fun L h => by omega⟩
  filter_upwards [eventually_ge_atTop 1,hcof.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier,
    eventually_two_mul_continuousCircuitPlateauCompilerCost_le_nearHilbert,
    RHTower.eventually_pairQubit_twoLocalPauli_separator] with L hL hent hcost hsep
  have hnull := (nearestNeighborPathLocalMaximalSet_dense_residual_fullMeasure (L := L) hL).2.2
  have hμ : centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1 ≪
      (volume : Measure (Fin (nearestNeighborPathLocalParameterCount L) → ℝ)) := by
    simpa [centredProductGaussian] using (productGaussian_absolutelyContinuous
      (nearestNeighborPathLocalParameterCount L) one_ne_zero (fun _ => 0))
  have ha : ∀ᵐ p ∂(centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1),
      p ∈ nearestNeighborPathLocalMaximalSet L := ae_iff.mpr (hμ hnull)
  filter_upwards [ha] with p hp
  refine ⟨?_,RHTower.nearestNeighborPath_permanentLocalityHaarSeparation hL hp hsep⟩
  let n := L*2
  let d := 2^n-1
  let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
  let U := unitaryEvolution (H : Reg n)
  let P := nearHilbertContinuousCircuitBudget n
  let r := excursionGateBudget n
  let B := (continuousCircuitPlateauWidth L : ℝ)/(1+‖(H : Reg n)‖)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let e : (Fin n → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hpos : 0 < (2:ℕ)^n := by positivity
                  dsimp [d]; omega))
  have hmax := (RHTower.pairQubitProjectivePauliSeed_maximallyProjective hp).comp_equiv e.symm
  have hinc (t : ℝ) (ht : |t| ≤ B) := normalized_path_increment hL H
    (RHTower.pairQubitProjectivePauliSeed_hasPauliWeightAtMost_two L p) t ht
  have hcost' : 2*continuousCircuitPlateauCompilerCost L ≤ P := hcost
  have hprefix (t : ℝ) (ht : t ∈ Icc 0 B) : orbitCircuitDistance H P t < 9/80 := by
    obtain ⟨c,hc,C,hC,he⟩ := hinc t (by simpa only [abs_of_nonneg ht.1] using ht.2)
    have h := (hasProjectiveCircuitApproximation_iff_infDist (U t) P (1/100:ℝ)).mp
      ⟨c,hc,C,by omega,he⟩
    change orbitCircuitDistance H P t ≤ 1/100 at h
    linarith
  obtain ⟨σ,hσ,heq,hprior⟩ := first_crossing _ (continuous_orbitCircuitDistance H P) (9/80) B hB
    hprefix (reaches_robust_threshold e H hmax hent)
  have hσ0 := hB.trans hσ.le
  have hlate : ProjectiveCircuitSeparated n (11/100:ℝ) P (U σ) := by
    intro c hc C hC
    by_contra! h
    have h' := (hasProjectiveCircuitApproximation_iff_infDist (U σ) P (11/100:ℝ)).mp ⟨c,hc,C,hC,h⟩
    change orbitCircuitDistance H P σ ≤ 11/100 at h'
    linarith
  have hwin (t : ℝ) (ht : t ∈ Icc (σ-B) (σ+B)) : ProjectiveCircuitSeparated n (1/10:ℝ) r (U t) := by
    have hτ : |σ-t| ≤ B := abs_le.mpr ⟨by linarith only [ht.2],by linarith only [ht.1]⟩
    have hc := projectiveCircuitSeparated_unitaryEvolution_backward_cone H
      (by omega : continuousCircuitPlateauCompilerCost L ≤ P) hlate (hinc (σ-t) hτ)
      (by norm_num : (1/10:ℝ)+1/100 ≤ 11/100)
    rw [show σ-(σ-t) = t by ring] at hc
    apply hc.mono_budget
    change P/2 ≤ P-continuousCircuitPlateauCompilerCost L
    omega
  refine ⟨σ,hσ,heq,hprior,hwin,?_⟩
  intro s hs
  obtain ⟨v,hv,he,hgap⟩ := projective_first_circuit_visit_deadline e H σ s
  refine ⟨v,?_,by simpa only [abs_of_nonneg hσ0] using hv.2,he,hgap⟩
  by_contra! h
  obtain ⟨c,hc,C,hC,heC⟩ := he
  exact (not_lt_of_ge heC) (hwin v ⟨(sub_le_self _ hB).trans hv.1,h⟩ c hc C (hC.trans hs))

#print axioms gaussianPath_first_robust_saturation_and_return

end
end GaloisForLFunctions.HTGeometry
