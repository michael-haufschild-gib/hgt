import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PrimeVarianceAfterACommonSieve

/-!
# Global square-mean cost of sieving through quadratic logarithmic height

At zero tilt the local cost is exactly the half-power sieve product. The
deleted prime row costs at most the number of primes. Both costs are
subexponential, uniformly over every subset of the primes through T².
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory _root_.RHTower

/-- A set of primes below `T²` has at most `T²` elements. -/
theorem card_sieving_primes_le {T : ℝ} (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) : (P.card:ℝ) ≤ T^2 := by
  let e : Nat.Primes ↪ ℕ := ⟨Subtype.val,Subtype.coe_injective⟩
  have hsub : P.map e ⊆ Icc 1 ⌊T^2⌋₊ := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := mem_map.1 hn
    exact mem_Icc.2 ⟨p.2.one_le,Nat.le_floor (hP p hp)⟩
  have h := card_le_card hsub
  simp only [card_map,Nat.card_Icc,Nat.add_sub_cancel] at h
  exact (show (P.card:ℝ) ≤ (⌊T^2⌋₊:ℕ) by exact_mod_cast h).trans (Nat.floor_le (sq_nonneg T))

private theorem sq_le_quadratic_sieve_cost {T : ℝ} (hT : 3 ≤ T) :
    T^2 ≤ Real.exp (8*Real.sqrt T+64*T/Real.log T) := by
  have ht : 0 < T := by linarith only [hT]
  have hl : 0 < Real.log T := Real.log_pos (by linarith only [hT])
  have hroot := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 ht)
  rw [Real.log_sqrt ht.le] at hroot
  rw [← Real.exp_log (sq_pos_of_pos ht),Real.log_pow,Real.exp_le_exp]
  push_cast
  linarith only [hroot,Real.sqrt_nonneg T,div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤64) ht.le) hl.le]

/-- Every quadratic-height sieve perturbs the ordinary polar error by a
function with a subexponential global L² norm, uniformly across all subsets. -/
theorem criticalState_quadratic_sieve_square_perturbation {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes, (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) →
      let g := fun t : ℝ => ordinaryPrimePolarError Φ t-commonSievedPrimeError P Φ t
      MemLp g 2 ∧ lpNorm g 2 volume ≤ Real.exp (ε*T) := by
  let B := lpNorm (tiltedIntegerError Φ 0) 2 volume
  let D := (1/2:ℝ)⁻¹*lpNorm Φ 2 volume
  have hB : 0 ≤ B := lpNorm_nonneg
  have hD : 0 ≤ D := mul_nonneg (by norm_num) lpNorm_nonneg
  filter_upwards [eventually_ge_atTop (3:ℝ),eventually_ge_atTop (B+D),
    eventually_quadratic_sieve_cost_le_exp hε] with T hT hBD hcost
  intro P hP
  have h := criticalState_commonSieve_tilted_norm hW ht hF hc he hC hb
    (β := 0) le_rfl (by norm_num) P
  simp only [zero_mul,Real.exp_zero,one_mul,sub_zero,tiltSieveFactor_zero] at h
  let K := Real.exp (8*Real.sqrt T+64*T/Real.log T)
  have h1 : (∏ p ∈ P, (1-(Real.sqrt (p:ℕ))⁻¹)⁻¹) ≤ K := sieve_half_cost_le P hT hP
  have h2 : (P.card:ℝ) ≤ K := (card_sieving_primes_le P hP).trans (sq_le_quadratic_sieve_cost hT)
  refine ⟨h.1,h.2.trans ?_⟩
  calc _ ≤ K*B+K*D := add_le_add (mul_le_mul_of_nonneg_right h1 hB) (mul_le_mul_of_nonneg_right h2 hD)
    _ = (B+D)*K := by ring
    _ ≤ T*K := mul_le_mul_of_nonneg_right hBD (Real.exp_pos _).le
    _ ≤ _ := hcost

/-- Reverse triangle inequality for two L² amplitudes on any smaller measure. -/
private theorem abs_lpNorm_sub_le_global {f g : ℝ → ℝ} {ν : Measure ℝ} (hν : ν ≤ volume)
    (hf : MemLp f 2 ν) (hd : MemLp (f-g) 2 volume) :
    |lpNorm g 2 ν-lpNorm f 2 ν| ≤ lpNorm (f-g) 2 volume := by
  have hl := hd.mono_measure hν
  have hg : MemLp g 2 ν := by simpa only [sub_sub_cancel] using hf.sub hl
  have hdiff : lpNorm (f-g) 2 ν ≤ lpNorm (f-g) 2 volume := by
    rw [← toReal_eLpNorm hl.1,← toReal_eLpNorm hd.1]
    exact ENNReal.toReal_mono hd.2.ne (eLpNorm_mono_measure _ hν)
  apply le_trans _ hdiff
  rw [abs_le]
  have h1 := lpNorm_le_lpNorm_add_lpNorm_sub (f := g) hf (by norm_num)
  have h2 := lpNorm_le_lpNorm_add_lpNorm_sub' (f := f) hg (by norm_num)
  constructor <;> linarith only [h1,h2]

/-- On every observable submeasure where the polar error is square
integrable, the two square-root variances differ subexponentially. -/
theorem criticalState_quadratic_sieve_sqrt_variance {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes, (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) →
      ∀ ν : Measure ℝ, ν ≤ volume → MemLp (ordinaryPrimePolarError Φ) 2 ν →
        |lpNorm (commonSievedPrimeError P Φ) 2 ν-lpNorm (ordinaryPrimePolarError Φ) 2 ν| ≤ Real.exp (ε*T) := by
  filter_upwards [criticalState_quadratic_sieve_square_perturbation hW ht hF hc he hC hb hε] with T h
  intro P hP ν hν hf
  exact (abs_lpNorm_sub_le_global hν hf (h P hP).1).trans (h P hP).2

/-- On each finite time window the polar ordinary-prime error is square integrable. -/
theorem memLp_ordinaryPolar_on_window {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (he : F =ᵐ[volume] Φ) (T : ℝ) :
    MemLp (ordinaryPrimePolarError Φ) 2 (volume.restrict (Ioc 0 T)) := by
  let ν := (volume : Measure ℝ).restrict (Ioc 0 T)
  let d := |zetaZeroAbscissa-1/2|+1
  let E := ordinaryPrimePolarError Φ
  let f := fun t : ℝ => Real.exp (-(d*t))*E t
  have hd : zetaZeroAbscissa-1/2 < d := (le_abs_self _).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  have hf : MemLp f 2 ν := (memLp_damped_ordinaryPrimePolarError hW ht hF he hd).mono_measure
    (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)
  have hundo (t : ℝ) : Real.exp (d*t)*f t=E t := by
    dsimp only [f]; rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
  have hm : AEStronglyMeasurable E ν := ((show AEStronglyMeasurable (fun t : ℝ => Real.exp (d*t)) ν by fun_prop).mul hf.1).congr
    (Eventually.of_forall hundo)
  apply (hf.norm.const_mul (Real.exp (d*T))).mono' hm
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with t ht0
  change ‖E t‖ ≤ Real.exp (d*T)*‖f t‖
  rw [← hundo t,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht0.2
    (add_nonneg (abs_nonneg _) zero_le_one))) (norm_nonneg _)

/-- Uniform square-root variance transfer on the actual prime observation
intervals for every positive exponential comparison rate. -/
theorem riemannHypothesis_or_quadratic_sieve_square_mean : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes,
        (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) →
        let ν := (volume : Measure ℝ).restrict (Ioc 0 T)
        |lpNorm (commonSievedPrimeError P Φ) 2 ν-lpNorm (ordinaryPrimePolarError Φ) 2 ν| ≤ Real.exp (ε*T) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun ε hε => ?_⟩
  filter_upwards [criticalState_quadratic_sieve_sqrt_variance hW ht hF hc he hC hb hε] with T h
  exact fun P hP => h P hP _ Measure.restrict_le_self (memLp_ordinaryPolar_on_window hW ht hF he T)

#print axioms riemannHypothesis_or_quadratic_sieve_square_mean
#print axioms criticalState_quadratic_sieve_square_perturbation
#print axioms criticalState_quadratic_sieve_sqrt_variance
end GaloisForLFunctions.ExclusionOfTheCriticalState
