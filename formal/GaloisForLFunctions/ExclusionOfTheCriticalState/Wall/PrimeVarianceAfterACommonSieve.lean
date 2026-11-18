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

/-- The L² cost of deleting actual primes is linear in their number. -/
theorem removedPrimeWave_tilted_norm {Φ : ℝ → ℝ} {β : ℝ} (hβ : β < 1/2)
    (hψ : MemLp (fun t : ℝ => Real.exp (β*t)*Φ t) 2) (P : Finset Nat.Primes) :
    let f := fun t : ℝ => Real.exp (β*t)*removedPrimeWave P Φ t
    MemLp f 2 ∧ lpNorm f 2 volume ≤ P.card*((1/2-β)⁻¹*lpNorm (fun t : ℝ => Real.exp (β*t)*Φ t) 2 volume) := by
  let ψ := fun t : ℝ => Real.exp (β*t)*Φ t
  let δ := 1/2-β
  have hδ : 0 < δ := sub_pos.2 hβ
  let L := fun p : Nat.Primes => Real.log (p:ℕ)
  let a := fun p : Nat.Primes => L p*Real.exp (-(δ*L p))
  let g := fun (p : Nat.Primes) (t : ℝ) => ψ (t-L p)
  have hcoef (p : Nat.Primes) : 0 ≤ a p ∧ a p ≤ δ⁻¹ := by
    have hl := Real.log_natCast_nonneg (p:ℕ)
    refine ⟨mul_nonneg hl (Real.exp_pos _).le,?_⟩
    dsimp only [a]; rw [Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _),← div_eq_inv_mul,le_div_iff₀ hδ]
    linarith only [Real.add_one_le_exp (δ*L p)]
  have trans (p : Nat.Primes) : MemLp (g p) 2 ∧ lpNorm (g p) 2 volume=lpNorm ψ 2 volume := by
    have hm := measurePreserving_sub_right volume (L p)
    have h : MemLp (g p) 2 := hψ.comp_measurePreserving hm
    refine ⟨h,?_⟩
    rw [← toReal_eLpNorm h.1,← toReal_eLpNorm hψ.1]
    exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving hψ.1 hm)
  have he : (fun t : ℝ => Real.exp (β*t)*removedPrimeWave P Φ t) = ∑ p ∈ P, a p • g p := by
    funext t
    simp only [removedPrimeWave,Finset.mul_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hx : 0 < ((p:ℕ):ℝ) := by exact_mod_cast p.2.pos
    have hr : (Real.sqrt (p:ℕ))⁻¹=Real.exp (-(L p/2)) := by
      rw [Real.exp_neg,Real.exp_half,Real.exp_log hx]
    dsimp only [g,ψ,a,continuousIntegerAtom]
    rw [hr]
    have hlog : -(δ*L p)+β*(t-L p)=β*t+ -(L p/2) := by dsimp only [δ]; ring
    have hphase := congrArg Real.exp hlog
    rw [Real.exp_add,Real.exp_add] at hphase
    change Real.exp (β*t)*(L p*(Real.exp (-(L p/2))*_))=_
    linear_combination -L p*Φ (t-L p)*hphase
  have hm (p : Nat.Primes) (_ : p ∈ P) : MemLp (a p • g p) 2 := (trans p).1.const_smul _
  dsimp only; rw [he]
  refine ⟨memLp_finsetSum' P hm,(lpNorm_sum_le hm (by norm_num)).trans ?_⟩
  calc _ ≤ ∑ _p ∈ P, δ⁻¹*lpNorm ψ 2 volume := by
           refine Finset.sum_le_sum fun p _ => ?_
           rw [lpNorm_const_smul,(trans p).2]
           change ‖a p‖*lpNorm ψ 2 volume ≤ _
           rw [Real.norm_eq_abs,abs_of_nonneg (hcoef p).1]
           exact mul_le_mul_of_nonneg_right (hcoef p).2 lpNorm_nonneg
    _ = _ := by simp

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

private theorem integral_sq_eq_lpNorm_sq {f : ℝ → ℝ} (hf : MemLp f 2) :
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
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let E := ordinaryPrimePolarError Φ
  let ψ := fun t : ℝ => Real.exp (β*t)*Φ t
  let J := ∫ t in Ioi (0:ℝ), (Real.exp (-(d*t))*E t)^2
  let B := lpNorm (tiltedIntegerError Φ β) 2 volume
  let B' := (1/2-β)⁻¹*lpNorm ψ 2 volume
  have hJ : 0 ≤ J := integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ B := lpNorm_nonneg
  have hB' : 0 ≤ B' := mul_nonneg (inv_nonneg.2 (sub_nonneg.2 hβ'.le)) lpNorm_nonneg
  have hψ := memLp_tilted_state (criticalHalfLineEnergyDomain_of_groundState hF) he hβ
  refine ⟨J+2*(B+B')^2,by positivity,fun P => ?_⟩
  let N := sievedReferenceError P Φ A
  let L := removedPrimeWave P Φ
  let G := fun t : ℝ => N t+L t
  let g := fun t : ℝ => Real.exp (β*t)*G t
  let n := fun t : ℝ => Real.exp (β*t)*N t
  let l := fun t : ℝ => Real.exp (β*t)*L t
  have hsieve := criticalState_sieved_integer_quadrature hW ht hF hc he hC hb hβ hβ' P
  have hremove := removedPrimeWave_tilted_norm hβ' hψ P
  have hn : MemLp n 2 := hsieve.1
  have hl : MemLp l 2 := hremove.1
  have hsplit : g=n+l := by funext t; exact mul_add ..
  have hg : MemLp g 2 := hsplit.symm ▸ hn.add hl
  have hnorm : lpNorm g 2 volume ≤ (4:ℝ)^P.card*(B+B') := by
    rw [hsplit,mul_add]
    exact (lpNorm_add_le hn (by norm_num)).trans (add_le_add hsieve.2.2
      (hremove.2.trans (mul_le_mul_of_nonneg_right (natCast_le_four_pow _) hB')))
  have hE := memLp_damped_ordinaryPrimePolarError hW ht hF he hd
  have hcmp := weighted_variance_change_bound (E := E) (G := G) (d := d) (β := β) (r := r)
    le_rfl (by dsimp only [β]; linarith only [hd0,hr]) hE (hg.mono_measure Measure.restrict_le_self)
  have heq (t : ℝ) : E t-G t=commonSievedPrimeError P Φ t := by
    dsimp only [E,G,N,L,ordinaryPrimePolarError,commonSievedPrimeError,sievedReferenceError,A]
    ring
  dsimp only at hcmp
  simp_rw [heq] at hcmp
  refine ⟨hcmp.1,hcmp.2.trans ?_⟩
  have hi : Integrable (fun t => g t^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  have hsq : (∫ t in Ioi (0:ℝ), g t^2) ≤ (16:ℝ)^P.card*(B+B')^2 := by
    calc _ ≤ ∫ t, g t^2 := setIntegral_le_integral hi (Eventually.of_forall fun _ => sq_nonneg _)
      _ = _ := integral_sq_eq_lpNorm_sq hg
      _ ≤ ((4:ℝ)^P.card*(B+B'))^2 := pow_le_pow_left₀ lpNorm_nonneg hnorm 2
      _ = _ := by rw [mul_pow,← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  change J+2*(∫ t in Ioi (0:ℝ), g t^2) ≤ (J+2*(B+B')^2)*(16:ℝ)^P.card
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
#print axioms removedPrimeWave_tilted_norm
end GaloisForLFunctions.ExclusionOfTheCriticalState
