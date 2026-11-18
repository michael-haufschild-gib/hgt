import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.WeightedSquareErrorAfterSieving
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ExponentiallyIntegrableChangeOfPrimeVariance

/-!
# Prime variance after removing the same primes from both rows

Each deleted prime is a translate of the tilted state whose coefficient
is bounded independently of the prime. Together with the weighted error
of the sifted density this gives an exponentially small late variance error.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

/-- Actual finite contribution of the primes removed from the ordinary-prime wave. -/
def removedPrimeWave (P : Finset Nat.Primes) (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ P, Real.log (p:ℕ)*continuousIntegerAtom Φ (p:ℕ) t

/-- The ordinary-prime error with the same finite sieve on both rows. -/
def commonSievedPrimeError (P : Finset Nat.Primes) (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (ordinaryPrimeWave Φ t).re-removedPrimeWave P Φ t-sievedIntegerReference P Φ t

private def removedPrimeCoefficient (β : ℝ) (p : Nat.Primes) : ℝ :=
  Real.log (p:ℕ)*Real.exp (-((1/2-β)*Real.log (p:ℕ)))

private theorem removedPrimeCoefficient_bounds {β : ℝ} (hβ : β < 1/2) (p : Nat.Primes) :
    0 ≤ removedPrimeCoefficient β p ∧ removedPrimeCoefficient β p ≤ (1/2-β)⁻¹ := by
  have hl := Real.log_natCast_nonneg (p:ℕ)
  have hδ := sub_pos.2 hβ
  refine ⟨mul_nonneg hl (Real.exp_pos _).le,?_⟩
  rw [removedPrimeCoefficient,Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _),
    ← div_eq_inv_mul,le_div_iff₀ hδ]
  linarith only [Real.add_one_le_exp ((1/2-β)*Real.log (p:ℕ))]

private theorem norm_scaled_translate {ψ : ℝ → ℝ} (hψ : MemLp ψ 2) (L a : ℝ) (ha : 0 ≤ a) :
    let g := a • (fun t => ψ (t-L))
    MemLp g 2 ∧ lpNorm g 2 volume=a*lpNorm ψ 2 volume := by
  let G := fun t => ψ (t-L)
  have hm := measurePreserving_sub_right volume L
  have hG : MemLp G 2 := hψ.comp_measurePreserving hm
  have h : eLpNorm G 2 volume = eLpNorm ψ 2 volume := eLpNorm_comp_measurePreserving (p := 2) hψ.1 hm
  have hn : lpNorm G 2 volume = lpNorm ψ 2 volume := by
    rw [← toReal_eLpNorm hG.1,← toReal_eLpNorm hψ.1,h]
  refine ⟨hG.const_smul a,?_⟩
  change lpNorm (a • G) 2 volume = _
  rw [lpNorm_const_smul,hn]
  change ‖a‖*lpNorm ψ 2 volume=_
  rw [Real.norm_eq_abs,abs_of_nonneg ha]

private theorem removedPrimeWave_tilt_eq (Φ : ℝ → ℝ) (β : ℝ) (P : Finset Nat.Primes) :
    (fun t : ℝ => Real.exp (β*t)*removedPrimeWave P Φ t) =
      ∑ p ∈ P, removedPrimeCoefficient β p •
        (fun t : ℝ => Real.exp (β*(t-Real.log (p:ℕ)))*Φ (t-Real.log (p:ℕ))) := by
  funext t
  simp only [removedPrimeWave,Finset.mul_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  let L := Real.log (p:ℕ)
  have hx : 0 < ((p:ℕ):ℝ) := by exact_mod_cast p.2.pos
  have hr : (Real.sqrt (p:ℕ))⁻¹=Real.exp (-(L/2)) := by rw [Real.exp_neg,Real.exp_half,Real.exp_log hx]
  have he : -((1/2-β)*L)+β*(t-L)=β*t+ -(L/2) := by ring
  have hphase := congrArg Real.exp he
  rw [Real.exp_add,Real.exp_add] at hphase
  rw [continuousIntegerAtom,hr]
  change Real.exp (β*t)*(L*(Real.exp (-(L/2))*Φ (t-L)))=
    (L*Real.exp (-((1/2-β)*L)))*(Real.exp (β*(t-L))*Φ (t-L))
  linear_combination -L*Φ (t-L)*hphase

/-- The L² cost of deleting actual primes is linear in their number. -/
theorem removedPrimeWave_tilted_norm {Φ : ℝ → ℝ} {β : ℝ} (hβ : β < 1/2)
    (hψ : MemLp (fun t : ℝ => Real.exp (β*t)*Φ t) 2) (P : Finset Nat.Primes) :
    let f := fun t : ℝ => Real.exp (β*t)*removedPrimeWave P Φ t
    MemLp f 2 ∧ lpNorm f 2 volume ≤ P.card*((1/2-β)⁻¹*lpNorm (fun t : ℝ => Real.exp (β*t)*Φ t) 2 volume) := by
  let ψ := fun t : ℝ => Real.exp (β*t)*Φ t
  let g := fun p : Nat.Primes => removedPrimeCoefficient β p • (fun t => ψ (t-Real.log (p:ℕ)))
  have h (p : Nat.Primes) : MemLp (g p) 2 ∧ lpNorm (g p) 2 volume=
      removedPrimeCoefficient β p*lpNorm ψ 2 volume :=
    norm_scaled_translate (ψ := ψ) hψ (Real.log (p:ℕ)) _ (removedPrimeCoefficient_bounds hβ p).1
  dsimp only
  rw [removedPrimeWave_tilt_eq]
  change MemLp (∑ p ∈ P, g p) 2 ∧ lpNorm (∑ p ∈ P, g p) 2 volume ≤ _
  have hm (p) (_ : p ∈ P) : MemLp (g p) 2 := (h p).1
  refine ⟨memLp_finsetSum' P hm,(lpNorm_sum_le hm (by norm_num)).trans ?_⟩
  calc _ ≤ ∑ _p ∈ P, (1/2-β)⁻¹*lpNorm ψ 2 volume := Finset.sum_le_sum fun p _ =>
             ((h p).2.le.trans (mul_le_mul_of_nonneg_right (removedPrimeCoefficient_bounds hβ p).2 lpNorm_nonneg))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,ψ]

private theorem memLp_tilted_state {F Φ : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    (he : F =ᵐ[volume] Φ) {β : ℝ} (hβ : 0 ≤ β) : MemLp (fun u : ℝ => Real.exp (β*u)*Φ u) 2 := by
  have hc := criticalHalfLineEnergyDomain_exp_min_mul hd hβ
  have h : MemLp (fun u : ℝ => Real.exp (β*min u 0)*F u) 2 :=
    (memLp_two_iff_integrable_sq_norm hc.meas.aestronglyMeasurable).2 (by simpa only [Real.norm_eq_abs,sq_abs] using hc.sq)
  apply MemLp.ae_eq _ h
  filter_upwards [he] with u hu
  rcases le_total u 0 with hl | hl
  · rw [min_eq_left hl,hu]
  · rw [← hu,hd.support u hl,mul_zero,mul_zero]

/-- The square integral of a real L² representative is its squared norm. -/
theorem integral_sq_eq_lpNorm_sq {f : ℝ → ℝ} (hf : MemLp f 2) :
    (∫ t, f t^2)=(lpNorm f 2 volume)^2 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.1]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs]
  rw [show (2:ℝ)⁻¹=1/2 by norm_num,← Real.sqrt_eq_rpow,Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

private theorem natCast_le_four_pow (n : ℕ) : (n:ℝ) ≤ (4:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_succ,pow_succ]
    linarith only [ih,one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) (n := n)]

/-- The two contributions to the L² perturbation are the normalized
sieve product and the finite sum over the deleted primes. -/
theorem criticalState_commonSieve_tilted_norm {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1/2) (P : Finset Nat.Primes) :
    let g := fun t : ℝ => Real.exp (β*t)*(ordinaryPrimePolarError Φ t-commonSievedPrimeError P Φ t)
    MemLp g 2 ∧ lpNorm g 2 volume ≤ (∏ p ∈ P, tiltSieveFactor β p)*lpNorm (tiltedIntegerError Φ β) 2 volume+
      P.card*((1/2-β)⁻¹*lpNorm (fun t => Real.exp (β*t)*Φ t) 2 volume) := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let n := fun t : ℝ => Real.exp (β*t)*sievedReferenceError P Φ A t
  let l := fun t : ℝ => Real.exp (β*t)*removedPrimeWave P Φ t
  have hs := criticalState_sieved_integer_quadrature hW ht hF hc he hC hb hβ hβ' P
  have hl := removedPrimeWave_tilted_norm hβ'
    (memLp_tilted_state (criticalHalfLineEnergyDomain_of_groundState hF) he hβ) P
  have hn : MemLp n 2 := hs.1
  have hh : MemLp l 2 := hl.1
  have heq : (fun t : ℝ => Real.exp (β*t)*(ordinaryPrimePolarError Φ t-commonSievedPrimeError P Φ t))=n+l := by
    funext t
    simp only [n,l,Pi.add_apply,ordinaryPrimePolarError,commonSievedPrimeError,sievedReferenceError,A]
    ring
  dsimp only
  rw [heq]
  exact ⟨hn.add hh,(lpNorm_add_le hn (by norm_num)).trans (add_le_add hs.2.1 hl.2)⟩

/-- The change of the prime wave itself has finite weighted L² norm at all
subcritical tilts. The same bound covers every common sieve. -/
theorem criticalState_commonSieve_tilted_error {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1/2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ P : Finset Nat.Primes,
      let g := fun t : ℝ => Real.exp (β*t)*(ordinaryPrimePolarError Φ t-commonSievedPrimeError P Φ t)
      MemLp g 2 ∧ lpNorm g 2 volume ≤ (4:ℝ)^P.card*B := by
  let B := lpNorm (tiltedIntegerError Φ β) 2 volume
  let D := (1/2-β)⁻¹*lpNorm (fun t => Real.exp (β*t)*Φ t) 2 volume
  have hB : 0 ≤ B := lpNorm_nonneg
  have hD : 0 ≤ D := mul_nonneg (inv_nonneg.2 (sub_nonneg.2 hβ'.le)) lpNorm_nonneg
  refine ⟨B+D,add_nonneg hB hD,fun P => ?_⟩
  obtain ⟨hg,hg'⟩ := criticalState_commonSieve_tilted_norm hW ht hF hc he hC hb hβ hβ' P
  have hprod : (∏ p ∈ P, tiltSieveFactor β p) ≤ (4:ℝ)^P.card := by
    calc _ ≤ ∏ _p ∈ P, (4:ℝ) := Finset.prod_le_prod (fun _ _ => tiltSieveFactor_nonneg ..)
           (fun _ _ => tiltSieveFactor_le_four hβ'.le _)
      _ = _ := by simp
  refine ⟨hg,hg'.trans ?_⟩
  rw [mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right hprod hB) (mul_le_mul_of_nonneg_right (natCast_le_four_pow _) hD)

/-- Uniform variance transfer for a common sieve. The constant depends on
the state and the tilt, and is independent of every removed prime. -/
theorem criticalState_commonSieve_variance_bound {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1-zetaZeroAbscissa) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ P : Finset Nat.Primes,
      let v := fun t : ℝ => Real.exp (r*t)*|(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|
      IntegrableOn v (Ioi 0) ∧ (∫ t in Ioi (0:ℝ), v t) ≤ M*(16:ℝ)^P.card := by
  obtain ⟨d,hd,hd'⟩ := exists_between (by linarith only [hr'] : zetaZeroAbscissa-1/2 < 1/2-r)
  have hd0 := (sub_nonneg.2 half_le_zetaZeroAbscissa).trans_lt hd
  let β := r+d
  have hβ : 0 ≤ β := add_nonneg hr hd0.le
  have hβ' : β < 1/2 := by dsimp only [β]; linarith only [hd']
  obtain ⟨B,hB,hbound⟩ := criticalState_commonSieve_tilted_error hW ht hF hc he hC hb hβ hβ'
  let E := ordinaryPrimePolarError Φ
  let J := ∫ t in Ioi (0:ℝ), (Real.exp (-(d*t))*E t)^2
  have hJ : 0 ≤ J := integral_nonneg fun _ => sq_nonneg _
  refine ⟨J+2*B^2,by positivity,fun P => ?_⟩
  let G := fun t : ℝ => E t-commonSievedPrimeError P Φ t
  let g := fun t : ℝ => Real.exp (β*t)*G t
  obtain ⟨hg,hnorm⟩ := hbound P
  have hE := memLp_damped_ordinaryPrimePolarError hW ht hF he hd
  have hcmp := weighted_variance_change_bound (E := E) (G := G) (d := d) (β := β) (r := r)
    le_rfl (by dsimp only [β]; linarith only [hd0,hr]) hE (hg.mono_measure Measure.restrict_le_self)
  have heq (t : ℝ) : E t-G t=commonSievedPrimeError P Φ t := by dsimp only [G]; ring
  dsimp only at hcmp
  simp_rw [heq] at hcmp
  refine ⟨hcmp.1,hcmp.2.trans ?_⟩
  have hi : Integrable (fun t => g t^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  have hsq : (∫ t in Ioi (0:ℝ), g t^2) ≤ (16:ℝ)^P.card*B^2 := by
    calc _ ≤ ∫ t, g t^2 := setIntegral_le_integral hi (Eventually.of_forall fun _ => sq_nonneg _)
      _ = _ := integral_sq_eq_lpNorm_sq hg
      _ ≤ ((4:ℝ)^P.card*B)^2 := pow_le_pow_left₀ lpNorm_nonneg hnorm 2
      _ = _ := by rw [mul_pow,← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  change J+2*(∫ t in Ioi (0:ℝ), g t^2) ≤ (J+2*B^2)*(16:ℝ)^P.card
  have hdom := le_mul_of_one_le_right hJ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 16) (n := P.card))
  linarith only [hdom,hsq]

/-- A weighted absolute moment on the full positive ray controls every
tail by the value of the inverse weight at its lower endpoint. -/
theorem abs_tail_le_exp_neg_mul {f : ℝ → ℝ} {r U : ℝ} (hr : 0 ≤ r) (hU : 0 ≤ U)
    (hi : IntegrableOn (fun t : ℝ => Real.exp (r*t)*|f t|) (Ioi 0)) :
    (∫ t in Ioi U, |f t|) ≤ Real.exp (-(r*U))*(∫ t in Ioi (0:ℝ), Real.exp (r*t)*|f t|) := by
  let A := Real.exp (-(r*U))
  let w := fun t : ℝ => Real.exp (r*t)*|f t|
  have hs : Ioi U ⊆ Ioi 0 := Ioi_subset_Ioi hU
  have hA : 0 ≤ A := (Real.exp_pos _).le
  calc _ ≤ ∫ t in Ioi U, A*w t := by
           apply integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) ((hi.mono_set hs).const_mul A)
           filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
           change |f t| ≤ A*(Real.exp (r*t)*|f t|)
           rw [← mul_assoc]
           apply le_mul_of_one_le_left (abs_nonneg _)
           dsimp only [A]; rw [← Real.exp_add,Real.one_le_exp_iff]
           linarith only [mul_le_mul_of_nonneg_left (le_of_lt ht) hr]
    _ ≤ ∫ t in Ioi (0:ℝ), A*w t := setIntegral_mono_set (hi.const_mul A)
           (Eventually.of_forall fun t => mul_nonneg hA (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)))
           (Eventually.of_forall fun _ => @hs _)
    _ = _ := integral_const_mul ..

/-- Every late-ray bound is simultaneous in the lower cutoff and the
choice of the common sieve. -/
theorem criticalState_commonSieve_variance_tail {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1-zetaZeroAbscissa) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (P : Finset Nat.Primes) (U : ℝ), 0 ≤ U →
      (∫ t in Ioi U, |(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) ≤
        Real.exp (-(r*U))*(M*(16:ℝ)^P.card) := by
  obtain ⟨M,hM,hm⟩ := criticalState_commonSieve_variance_bound hW ht hF hc he hC hb hr hr'
  exact ⟨M,hM,fun P U hU => (abs_tail_le_exp_neg_mul hr hU (hm P).1).trans
    (mul_le_mul_of_nonneg_left (hm P).2 (Real.exp_pos _).le)⟩

/-- The total tail discrepancy of all subsets of a single prime pool.
The bound therefore allows a different subset at each observation time. -/
theorem criticalState_commonSieve_all_subsets {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1-zetaZeroAbscissa) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Q : Finset Nat.Primes) (U : ℝ), 0 ≤ U →
      (∑ P ∈ Q.powerset, ∫ t in Ioi U, |(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) ≤
        Real.exp (-(r*U))*M*(17:ℝ)^Q.card := by
  obtain ⟨M,hM,h⟩ := criticalState_commonSieve_variance_tail hW ht hF hc he hC hb hr hr'
  refine ⟨M,hM,fun Q U hU => (Finset.sum_le_sum (fun P (_ : P ∈ Q.powerset) => h P U hU)).trans_eq ?_⟩
  have heq := Finset.prod_one_add (f := fun _ : Nat.Primes => (16:ℝ)) Q
  simp only [Finset.prod_const,show (1:ℝ)+16=17 by norm_num] at heq
  simp_rw [← mul_assoc]; rw [← Finset.mul_sum,← heq]

/-- The same confined state satisfies the variance bound for all subcritical
rates and all finite prime sets. -/
theorem riemannHypothesis_or_commonSieve_variance_bound : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ r : ℝ, 0 ≤ r → r < 1-zetaZeroAbscissa → ∃ M : ℝ, 0 ≤ M ∧ ∀ P : Finset Nat.Primes,
        let v := fun t : ℝ => Real.exp (r*t)*|(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|
        IntegrableOn v (Ioi 0) ∧ (∫ t in Ioi (0:ℝ), v t) ≤ M*(16:ℝ)^P.card := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hΦ,he,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,he,fun _ => criticalState_commonSieve_variance_bound hW ht hF hΦ he hC hb⟩

#print axioms riemannHypothesis_or_commonSieve_variance_bound
#print axioms criticalState_commonSieve_all_subsets
#print axioms removedPrimeWave_tilted_norm
end GaloisForLFunctions.ExclusionOfTheCriticalState
