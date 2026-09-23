import GaloisForLFunctions.RHTower.DeningerDampedCompleteXiPacket
import GaloisForLFunctions.RHTower.DeningerDampedOriginalGreenMellin
import GaloisForLFunctions.RHTower.DeningerOriginalGreenXiResolventBound
import GaloisForLFunctions.RHTower.DeningerOriginalGreenGaussianEnvelope

/-! # Literal original-prime Green fields in the full Xi norm -/

open Complex Filter Topology
noncomputable section
namespace RHTower
open DeningerMeyerGaussianGreen
open scoped TensorProduct

/-- One source constant, independent of the prefix and native Xi copy. -/
def deningerDampedXiGaussianBound (a : {a : ℝ // 1<a}) : ℝ :=
  Real.exp (2*∑' k : ℕ, deningerDampedXiStepWeight a.val (k+1))

private theorem prefix_pointwise_exp_bound (a : {a : ℝ // 1<a}) (n : ℕ) (q : XiZeroCopy) :
    ‖deningerDampedXiPrefix a n q‖ ≤
      Real.exp (2*∑ k ∈ Finset.range n, deningerDampedXiStepWeight a.val (k+1))*
        ‖deningerDampedXiPrefix a 0 q‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ Real.exp (2*deningerDampedXiStepWeight a.val (n+1))*‖deningerDampedXiPrefix a n q‖ :=
        (deningerDampedXiPrefix_pointwise_bounds a n q).1
      _ ≤ Real.exp (2*deningerDampedXiStepWeight a.val (n+1))*
          (Real.exp (2*∑ k ∈ Finset.range n, deningerDampedXiStepWeight a.val (k+1))*
            ‖deningerDampedXiPrefix a 0 q‖) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc,← Real.exp_add,Finset.sum_range_succ]; congr 2; ring

/-- All actual source prefixes retain a common Gaussian envelope. -/
theorem deningerDampedXiPrefix_gaussian_bound (a : {a : ℝ // 1<a}) (n : ℕ) (q : XiZeroCopy) :
    ‖deningerDampedXiPrefix a n q‖ ≤
      deningerDampedXiGaussianBound a*‖reflectedGaussianHorizonGrade q‖ := by
  have hzero : deningerDampedXiPrefix a 0 q = reflectedGaussianHorizonGrade q := by
    have hP : GaloisForLFunctions.primesLE 0 = ∅ := by
      ext p
      simp only [GaloisForLFunctions.mem_primesLE,Finset.notMem_empty,iff_false,not_le]
      exact p.property.pos
    simp [deningerDampedXiPrefix_apply,hP,deningerDampedPrimeListSource,reflectedGaussianHorizonGrade]
  have h := prefix_pointwise_exp_bound a n q
  rw [hzero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact ((deningerDampedXiStepWeight_summable a.property).comp_injective
    (fun _ _ h => Nat.add_right_cancel h)).sum_le_tsum _
      (fun _ _ => deningerDampedXiStepWeight_nonneg a.val _)

private theorem prefix_coordinate_tendsto (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    Tendsto (fun n => deningerDampedXiPrefix a n q) atTop (𝓝 (deningerDampedXiField a q)) :=
  ((lp.evalCLM ℂ (fun _ : XiZeroCopy => ℂ) 2 q).continuous.tendsto _).comp
    (deningerDampedXiPrefix_tendsto a)

theorem deningerDampedXiField_gaussian_bound (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    ‖deningerDampedXiField a q‖ ≤
      deningerDampedXiGaussianBound a*‖reflectedGaussianHorizonGrade q‖ :=
  le_of_tendsto (prefix_coordinate_tendsto a q).norm
    (Eventually.of_forall (fun n => deningerDampedXiPrefix_gaussian_bound a n q))

/-- A common square-summable envelope controls every original prime and source prefix. -/
theorem exists_deningerOriginalPrimeGreenXi_envelope (a : {a : ℝ // 1<a}) :
    ∃ b : XiZeroCopy → ℝ, Summable (fun q => b q^(2 : ℕ)) ∧
      (∀ p : Nat.Primes, ∀ n q, ‖deningerDampedXiPrefix a n q/(1-(p : ℂ)^(-(q.1 : ℂ)))‖ ≤ b q) ∧
      (∀ p : Nat.Primes, ∀ q, ‖deningerDampedXiField a q/(1-(p : ℂ)^(-(q.1 : ℂ)))‖ ≤ b q) := by
  obtain ⟨C,hC,hbound⟩ := exists_deningerOriginalPrimeGreen_inverse_norm_bound
  let b : XiZeroCopy → ℝ := fun q =>
    (deningerDampedXiGaussianBound a*C)*((1+|(q.1 : ℂ).im|)^(2 : ℕ)*‖reflectedGaussianHorizonGrade q‖)
  have hsum : Summable (fun q => b q^(2 : ℕ)) := by
    have hscaled : Summable (fun q : XiZeroCopy =>
        (deningerDampedXiGaussianBound a*C)^(2 : ℕ) *
          ((1+|(q.1 : ℂ).im|)^(2 : ℕ)*‖reflectedGaussianHorizonGrade q‖)^(2 : ℕ)) :=
      summable_deningerGaussian_polynomial_envelope_sq.mul_left ((deningerDampedXiGaussianBound a*C)^(2 : ℕ))
    exact hscaled.congr (fun q => (mul_pow _ _ 2).symm)
  have hdom (p : Nat.Primes) (q : XiZeroCopy) (z : ℂ)
      (hz : ‖z‖ ≤ deningerDampedXiGaussianBound a*‖reflectedGaussianHorizonGrade q‖) :
      ‖z/(1-(p : ℂ)^(-(q.1 : ℂ)))‖ ≤ b q := by
    have hi := hbound p q.1
    rw [deningerOriginalGreen_prime_weight] at hi
    rw [div_eq_mul_inv,norm_mul]
    calc
      _ ≤ (deningerDampedXiGaussianBound a*‖reflectedGaussianHorizonGrade q‖)*
          (C*(1+|(q.1 : ℂ).im|)^(2 : ℕ)) :=
        mul_le_mul hz hi (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      _ = _ := by dsimp [b]; ring
  exact ⟨b,hsum,(fun p n q => hdom p q _ (deningerDampedXiPrefix_gaussian_bound a n q)),
    (fun p q => hdom p q _ (deningerDampedXiField_gaussian_bound a q))⟩

private theorem green_prefix_mem (a : {a : ℝ // 1<a}) (p : Nat.Primes) (n : ℕ) :
    Memℓp (fun q : XiZeroCopy => deningerDampedXiPrefix a n q/(1-(p : ℂ)^(-(q.1 : ℂ)))) 2 := by
  obtain ⟨b,hs,hp,_⟩ := exists_deningerOriginalPrimeGreenXi_envelope a
  apply HilbertSchmidt.memℓp_of_sq
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun q => pow_le_pow_left₀ (norm_nonneg _) (hp p n q) 2) hs

private theorem green_field_mem (a : {a : ℝ // 1<a}) (p : Nat.Primes) :
    Memℓp (fun q : XiZeroCopy => deningerDampedXiField a q/(1-(p : ℂ)^(-(q.1 : ℂ)))) 2 := by
  obtain ⟨b,hs,_,hg⟩ := exists_deningerOriginalPrimeGreenXi_envelope a
  apply HilbertSchmidt.memℓp_of_sq
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun q => pow_le_pow_left₀ (norm_nonneg _) (hg p q) 2) hs

def deningerOriginalPrimeGreenXiPrefix (a : {a : ℝ // 1<a}) (p : Nat.Primes) (n : ℕ) : XiDivisorL2 :=
  ⟨fun q => deningerDampedXiPrefix a n q/(1-(p : ℂ)^(-(q.1 : ℂ))),green_prefix_mem a p n⟩

def deningerOriginalPrimeGreenXiField (a : {a : ℝ // 1<a}) (p : Nat.Primes) : XiDivisorL2 :=
  ⟨fun q => deningerDampedXiField a q/(1-(p : ℂ)^(-(q.1 : ℂ))),green_field_mem a p⟩

/-- Finite Green coordinates are admitted literal integrals of the actual finite source. -/
theorem deningerOriginalPrimeGreenXiPrefix_mellin
    (a : {a : ℝ // 1<a}) (p : Nat.Primes) (n : ℕ) (q : XiZeroCopy) :
    MeasureTheory.Integrable (deningerMeyerStrongLogMellinJet 0 (q.1 : ℂ)
      (deningerL1OriginalGreenSum
        (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList) (Real.log (p : ℕ)))) ∧
    deningerOriginalPrimeGreenXiPrefix a p n q = deningerMeyerStrongLogMellin
      (deningerL1OriginalGreenSum
        (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList) (Real.log (p : ℕ)))
      (q.1 : ℂ) := by
  let f := deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList
  have hL : 0 < Real.log (p : ℕ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hs := (xi_divisor_support_re_mem_open_unit q.1).1
  have hjet (g : ℝ → ℂ) : deningerMeyerStrongLogMellinJet 0 (q.1 : ℂ) g =
      (fun t : ℝ => Complex.exp ((q.1 : ℂ)*(t : ℂ))*g t) := by
    funext t
    simp only [deningerMeyerStrongLogMellinJet,pow_zero,one_mul]
  have hf : MeasureTheory.Integrable (fun t : ℝ => Complex.exp ((q.1 : ℂ)*(t : ℂ))*f.val t) := by
    simpa only [hjet] using
      integrable_deningerMeyerStrongLogMellinJet f.property 0 (q.1 : ℂ)
  constructor
  · simpa only [hjet] using
      deningerL1OriginalGreenSum_weighted_integrable hL hs hf
  · change deningerMeyerStrongLogMellin f (q.1 : ℂ)/(1-(p : ℂ)^(-(q.1 : ℂ))) =
      deningerMeyerStrongLogMellin (deningerL1OriginalGreenSum f (Real.log (p : ℕ))) (q.1 : ℂ)
    simpa only [deningerMeyerStrongLogMellin,deningerMeyerStrongLogMellinJet,pow_zero,one_mul,
      deningerOriginalGreen_prime_weight] using (deningerL1OriginalGreenSum_mellin hL hs hf).symm

/-- Original-prime Green admission is convergence in the original full Xi norm. -/
theorem deningerOriginalPrimeGreenXiPrefix_tendsto (a : {a : ℝ // 1<a}) (p : Nat.Primes) :
    Tendsto (deningerOriginalPrimeGreenXiPrefix a p) atTop (𝓝 (deningerOriginalPrimeGreenXiField a p)) := by
  obtain ⟨b,hs,hp,hg⟩ := exists_deningerOriginalPrimeGreenXi_envelope a
  exact deningerXi_tendsto_of_dominated hs (hp p) (hg p)
    (fun q => (prefix_coordinate_tendsto a q).div_const _)

/-- Every admitted coordinate is the literal Mellin integral of the same Green source. -/
theorem deningerOriginalPrimeGreenXiField_mellin (a : {a : ℝ // 1<a}) (p : Nat.Primes) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenXiField a p q = deningerMeyerStrongLogMellin
      (deningerDampedOriginalPrimeGreen ⟨a.val,by linarith [a.property]⟩ p) (q.1 : ℂ) := by
  change deningerDampedXiField a q/(1-(p : ℂ)^(-(q.1 : ℂ))) = _
  rw [deningerDampedXiField_apply,deningerDampedOriginalPrimeGreen_mellin]
  · exact (xi_divisor_support_re_mem_open_unit q.1).1
  · linarith [(xi_divisor_support_re_mem_open_unit q.1).1,a.property]
  · linarith [(xi_divisor_support_re_mem_open_unit q.1).2,a.property]

theorem deningerOriginalPrimeGreenXiField_apply_ne_zero
    (a : {a : ℝ // 1<a}) (p : Nat.Primes) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenXiField a p q ≠ 0 :=
  div_ne_zero (deningerDampedXiField_apply_ne_zero a q)
    (deningerOriginalGreen_prime_denominator_ne_zero p (xi_divisor_support_re_mem_open_unit q.1).1)

theorem deningerOriginalPrimeGreenXiField_residue_normalization
    (a : {a : ℝ // 1<a}) (p : Nat.Primes) (q : XiZeroCopy) :
    (deningerOriginalPrimeGreenXiField a p q*xiGaussianGammaResidueNormalizer q)*
      xiGaussianGammaResiduePacket q = deningerOriginalPrimeGreenXiField a p q :=
  horizonGrade_mul_normalizer_mul_packet (deningerOriginalPrimeGreenXiField a p) q

/-- Same prime and native depth, with the literal Green coefficient retained. -/
def deningerOriginalPrimeGreenXiTateChain (a : {a : ℝ // 1<a}) (p : Nat.Primes)
    (q : XiZeroCopy) (n : ℕ) : DeningerGammaSixCofinalMeyerTateDegreeOneSource :=
  ccmRationalAdelicOrdinaryPrimeCycleAtom p ⊗ₜ[ℂ]
    (deningerOriginalPrimeGreenXiField a p q • deningerGammaSixCofinalAveragingPacket n)

def deningerOriginalPrimeGreenXiGraphPrefix (a : {a : ℝ // 1<a}) (p : Nat.Primes) (n : ℕ) :
    DeningerXiFullGammaGraph :=
  deningerXiGraphSpreadCLM (deningerOriginalPrimeGreenXiField a p)
    (deningerGammaSixCofinalFiniteGraphAdmission (deningerGammaSixCofinalAveragingPacket n))

/-- The full graph vector is the actual differential of the declared original-prime chain. -/
theorem deningerOriginalPrimeGreenXiGraphPrefix_apply
    (a : {a : ℝ // 1<a}) (p : Nat.Primes) (n : ℕ) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenXiGraphPrefix a p n q =
      deningerGammaSixCofinalMeyerTateCompletedDifferential (deningerOriginalPrimeGreenXiTateChain a p q n) := by
  change deningerOriginalPrimeGreenXiField a p q •
    deningerGammaSixCofinalFiniteGraphAdmission (deningerGammaSixCofinalAveragingPacket n) = _
  rw [deningerOriginalPrimeGreenXiTateChain,deningerGammaSixCofinalMeyerTateCompletedDifferential_primeAtom,map_smul]

def deningerOriginalPrimeGreenXiGraphBoundary (a : {a : ℝ // 1<a}) (p : Nat.Primes) :
    DeningerXiFullGammaGraph :=
  deningerXiGraphSpreadCLM (deningerOriginalPrimeGreenXiField a p) deningerGammaSixCofinalGraphSingularVector

/-- Whole-divisor convergence at the same native Tate depth. -/
theorem deningerOriginalPrimeGreenXiGraphPrefix_tendsto (a : {a : ℝ // 1<a}) (p : Nat.Primes) :
    Tendsto (deningerOriginalPrimeGreenXiGraphPrefix a p) atTop
      (𝓝 (deningerOriginalPrimeGreenXiGraphBoundary a p)) :=
  ((deningerXiGraphSpreadCLM (deningerOriginalPrimeGreenXiField a p)).continuous.tendsto _).comp
    tendsto_deningerGammaSixCofinalFiniteGraphAdmission_averagingPacket

/-- Admission retains the fixed physical reading with the exact nonzero source coefficient. -/
theorem deningerOriginalPrimeGreenXiGraphBoundary_physical
    (a : {a : ℝ // 1<a}) (p : Nat.Primes) (q : XiZeroCopy) :
    deningerGammaSixCofinalGraphPhysicalTransport (2*(q.1 : ℂ).re-1)
      (deningerOriginalPrimeGreenXiGraphBoundary a p q) =
    deningerOriginalPrimeGreenXiField a p q •
      deningerGammaSixFixedSoninPhysicalReceiver (2*(q.1 : ℂ).re-1) := by
  change deningerGammaSixCofinalGraphPhysicalTransport _
    (deningerOriginalPrimeGreenXiField a p q • deningerGammaSixCofinalGraphSingularVector) = _
  rw [map_smul,deningerGammaSixCofinalGraphPhysicalTransport_singularVector]

end RHTower
