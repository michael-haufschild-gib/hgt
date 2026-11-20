import Mathlib.Analysis.Fourier.ZMod
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import GaloisForLFunctions.TransThresholdPairCorrelation.TotientGridPairLaw
import GaloisForLFunctions.BezoutValuationIncidence.CyclotomicIncidenceRecurrenceAndArbitraryPhaseObservability
import GaloisForLFunctions.SignFreePurityMechanisms.ThePointCountOfSpecZIsLogarithmic

/-!
# The exact length of a finite sampler for short periods

The coefficients of a polynomial are finite sampling weights. They give
equal mass to all classes of every modulus up to K exactly when the
polynomial contains the cyclotomic factors of orders 2 through K.
Their total degree is the minimum span of a nonzero signed sampler.
Positive integer weights also suffice on the support of a product of
uniform laws for moduli in the upper half of the alphabet.
-/

open Finset Polynomial Filter Topology
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

noncomputable section

/-- The mass of the coefficients in each residue class. -/
def classMass (k : ℕ) (p : ℂ[X]) (j : ZMod k) : ℂ :=
  ∑ n ∈ p.support, if (n : ZMod k) = j then p.coeff n else 0

/-- Exact sampling of each short quotient, with arbitrary total mass. -/
def EquidistributesThrough (K : ℕ) (p : ℂ[X]) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ K → ∀ j : ZMod k, classMass k p j = p.eval 1/k

private theorem class_test {k : ℕ} [NeZero k] (p : ℂ[X]) (f : ZMod k → ℂ) :
    ∑ j, classMass k p j*f j = ∑ n ∈ p.support, p.coeff n*f (n:ZMod k) := by
  simp only [classMass,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  simp [ite_mul]

private theorem char_values {k : ℕ} [NeZero k] (p : ℂ[X]) (j : ZMod k) :
    ZMod.dft (classMass k p) j = p.eval (ZMod.stdAddChar (-j)) := by
  rw [ZMod.dft_apply, Polynomial.eval_eq_sum]
  simp only [smul_eq_mul,← mul_neg, mul_comm (ZMod.stdAddChar _), class_test]
  apply sum_congr rfl
  intro n _
  rw [← nsmul_eq_mul,AddChar.map_nsmul_eq_pow]

private theorem classes_of_vanishing {K : ℕ} {p : ℂ[X]}
    (hv : ∀ k ∈ Icc 2 K, ∀ z : ℂ, IsPrimitiveRoot z k → p.eval z = 0) :
    EquidistributesThrough K p := by
  intro k hk hK j
  letI : NeZero k := ⟨hk.ne'⟩
  have hf (u : ZMod k) : ZMod.dft (classMass k p) u = if u=0 then p.eval 1 else 0 := by
    rw [char_values]
    by_cases hu : u=0
    · simp [hu,AddChar.map_zero_eq_one]
    rw [if_neg hu]
    let z : ℂ := ZMod.stdAddChar (-u)
    have hpow : z^k=1 := by
      rw [show z^k = ZMod.stdAddChar (k • (-u)) from (AddChar.map_nsmul_eq_pow _ _ _).symm]
      simp [nsmul_eq_mul,AddChar.map_zero_eq_one]
    have hn : z ≠ 1 := by
      intro h
      have he : -u = 0 := ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm)
      exact hu (neg_eq_zero.mp he)
    have hd := orderOf_dvd_of_pow_eq_one hpow
    have hpos := Nat.pos_of_dvd_of_pos hd hk
    have hne := mt orderOf_eq_one_iff.mp hn
    exact hv (orderOf z) (mem_Icc.mpr ⟨by omega,(Nat.le_of_dvd hk hd).trans hK⟩) z (IsPrimitiveRoot.orderOf z)
  have H := ZMod.invDFT_apply (ZMod.dft (classMass k p)) j
  simpa only [LinearEquiv.symm_apply_apply,hf,mul_ite,smul_eq_mul,Finset.sum_ite_eq',mem_univ,
    if_true,zero_mul,AddChar.map_zero_eq_one,one_mul,mul_zero,div_eq_inv_mul] using H

private theorem vanishing_of_classes {K : ℕ} {p : ℂ[X]} (h : EquidistributesThrough K p)
    {k : ℕ} (hk : k ∈ Icc 2 K) {z : ℂ} (hz : IsPrimitiveRoot z k) : p.eval z = 0 := by
  have hk1 := (mem_Icc.mp hk).1
  have hk0 : 0 < k := by omega
  letI : NeZero k := ⟨hk0.ne'⟩
  have H := class_test p (fun j : ZMod k => z^j.val)
  have hg : ∑ j : ZMod k, z^j.val = 0 := by
    cases k with
    | zero => omega
    | succ t => exact (Fin.sum_univ_eq_sum_range (fun n => z^n) _).trans (hz.geom_sum_eq_zero hk1)
  simp only [h k hk0 (mem_Icc.mp hk).2,←mul_sum,hg,mul_zero,ZMod.val_natCast] at H
  rw [Polynomial.eval_eq_sum]
  exact (show (∑ n ∈ p.support, p.coeff n*z^n) = 0 by
    simpa only [hz.eq_orderOf,pow_mod_orderOf] using H.symm)

/-- All distinct nonconstant characters seen by at least one of the short quotients. -/
def shortPeriodNodes (K : ℕ) := (Icc 2 K).biUnion fun k => primitiveRoots k ℂ

theorem equidistributesThrough_iff_nodes (K : ℕ) (p : ℂ[X]) :
    EquidistributesThrough K p ↔ ∀ z ∈ shortPeriodNodes K, p.IsRoot z := by
  constructor
  · intro h z hz
    obtain ⟨k,hk,hz⟩ := mem_biUnion.mp hz
    exact vanishing_of_classes h hk (isPrimitiveRoot_of_mem_primitiveRoots hz)
  · intro h
    apply classes_of_vanishing
    intro k hk z hz
    exact h z (mem_biUnion.mpr ⟨k,hk,(mem_primitiveRoots (by have := (mem_Icc.mp hk).1; omega)).mpr hz⟩)

private theorem node_disjoint (K : ℕ) : ((Icc 2 K : Finset ℕ) : Set ℕ).PairwiseDisjoint
    (fun k => primitiveRoots k ℂ) :=
  fun _ _ _ _ h => IsPrimitiveRoot.disjoint h

/-- The monic filter with one zero at each nontrivial frequency of denominator at most K. -/
def shortPeriodFilter (K : ℕ) : ℂ[X] := ∏ z ∈ shortPeriodNodes K, (X - C z)

/-- The same filter has integer cyclotomic factors, without repeated roots. -/
theorem shortPeriodFilter_eq_cyclotomics (K : ℕ) :
    shortPeriodFilter K = ∏ k ∈ Icc 2 K, cyclotomic k ℂ := by
  classical
  rw [shortPeriodFilter,shortPeriodNodes,prod_biUnion (node_disjoint K)]
  apply prod_congr rfl
  intro k hk
  exact (cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp k
    (by have := (mem_Icc.mp hk).1; omega))).symm

/-- Taking one ordinary difference of the optimal averaging filter recovers
the universal incidence annihilator on the same alphabet. -/
theorem incidence_annihilator_from_sampler {K : ℕ} (hK : 1 ≤ K) :
    (BezoutValuationIncidence.cyclotomicIncidencePolynomial K).map Complex.ofRealHom =
      (X-1)*shortPeriodFilter K := by
  classical
  have he : Icc 1 K = insert 1 (Icc 2 K) := by ext t; simp; omega
  rw [BezoutValuationIncidence.cyclotomicIncidencePolynomial, Polynomial.map_prod,he,
    prod_insert (by simp),map_cyclotomic,cyclotomic_one,shortPeriodFilter_eq_cyclotomics]
  simp only [map_cyclotomic]

theorem shortPeriodFilter_degree (K : ℕ) :
    (shortPeriodFilter K).natDegree = ∑ k ∈ Icc 2 K, k.totient := by
  classical
  rw [shortPeriodFilter, natDegree_finsetProd_X_sub_C_eq_card _ id, shortPeriodNodes, card_biUnion (node_disjoint K)]
  exact sum_congr rfl fun k _ => Complex.card_primitiveRoots k

/-- All simultaneous equal-mass laws form the principal ideal generated by the filter. -/
theorem equidistributesThrough_iff_dvd (K : ℕ) (p : ℂ[X]) :
    EquidistributesThrough K p ↔ shortPeriodFilter K ∣ p := by
  classical
  by_cases hp : p=0
  · subst p
    simp [EquidistributesThrough,classMass]
  rw [equidistributesThrough_iff_nodes]
  symm
  change ((shortPeriodNodes K).val.map (fun z => X-C z)).prod ∣ p ↔ _
  rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hp,Multiset.le_iff_subset (shortPeriodNodes K).nodup]
  simp only [Multiset.subset_def,Finset.mem_val,Polynomial.mem_roots hp]

/-- Exact minimum degree and uniqueness up to scale for an extremal finite sampler. -/
theorem finite_sampler_minimum (K : ℕ) :
    EquidistributesThrough K (shortPeriodFilter K) ∧ (shortPeriodFilter K).eval 1 ≠ 0 ∧
    ∀ p : ℂ[X], p ≠ 0 → EquidistributesThrough K p →
      (∑ k ∈ Icc 2 K, k.totient) ≤ p.natDegree ∧
      (p.natDegree = ∑ k ∈ Icc 2 K, k.totient → p = shortPeriodFilter K * C p.leadingCoeff) := by
  classical
  refine ⟨(equidistributesThrough_iff_dvd _ _).mpr dvd_rfl,?_,?_⟩
  · rw [shortPeriodFilter,Polynomial.eval_prod]
    apply prod_ne_zero_iff.mpr
    intro z hz
    obtain ⟨k,hk,hz⟩ := mem_biUnion.mp hz
    simpa using sub_ne_zero.mpr ((isPrimitiveRoot_of_mem_primitiveRoots hz).ne_one (mem_Icc.mp hk).1).symm
  · intro p hp h
    have hd := (equidistributesThrough_iff_dvd K p).mp h
    rw [←shortPeriodFilter_degree]
    exact ⟨natDegree_le_of_dvd hd hp,fun he => eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
      (monic_prod_X_sub_C id _) hd he.le⟩

/-- The optimal finite span is asymptotic to 3 K² / π². -/
theorem shortPeriodFilter_quadratic :
    Tendsto (fun K : ℕ => ((shortPeriodFilter K).natDegree : ℝ)/(K:ℝ)^2)
      atTop (𝓝 (3/Real.pi^2)) := by
  have ht := GaloisForLFunctions.TransThresholdPairCorrelation.tendsto_sum_totient_div_sq
  have hz : Tendsto (fun K : ℕ => 1/(K:ℝ)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  rw [←sub_zero (3/Real.pi^2)]
  apply (ht.sub hz).congr'
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hU : Icc 1 K = insert 1 (Icc 2 K) := by ext t; simp; omega
  rw [shortPeriodFilter_degree,hU,sum_insert (by simp),Nat.totient_one]
  push_cast
  ring

/-- Nonnegative integer weights from independent uniform residue blocks in the
upper half of the alphabet. Every shorter modulus divides one of those block sizes. -/
def positiveShortSampler (K : ℕ) : ℕ[X] :=
  ∏ t ∈ Ioc (K/2) K, ∑ i ∈ range t, X^i

theorem positiveShortSampler_uniform (K : ℕ) :
    EquidistributesThrough K ((positiveShortSampler K).map (Nat.castRingHom ℂ)) ∧
      0 < (positiveShortSampler K).eval 1 ∧
      (positiveShortSampler K).natDegree ≤ ∑ t ∈ Ioc (K/2) K, (t-1) := by
  constructor
  · apply classes_of_vanishing
    intro k hk z hz
    obtain ⟨hk2,hkK⟩ := mem_Icc.mp hk
    have hk0 : 0 < k := by omega
    let t := K/k*k
    have hmod := Nat.mod_lt K hk0
    have hs : t + K%k = K := by dsimp [t]; rw [Nat.mul_comm,Nat.div_add_mod]
    have ht : k ≤ t := by
      have h := (Nat.le_div_iff_mul_le hk0).mpr (by simpa using hkK : 1*k ≤ K)
      simpa using Nat.mul_le_mul_right k h
    have hmem : t ∈ Ioc (K/2) K := mem_Ioc.mpr ⟨by omega,by omega⟩
    simp only [positiveShortSampler,Polynomial.map_prod,Polynomial.eval_prod]
    apply Finset.prod_eq_zero hmem
    simp only [Polynomial.map_sum,Polynomial.map_pow,Polynomial.map_X,Polynomial.eval_geom_sum]
    have hpow : z^t=1 := by dsimp [t]; rw [Nat.mul_comm,pow_mul,hz.pow_eq_one,one_pow]
    exact (mul_eq_zero.mp ((geom_sum_mul z t).trans (by rw [hpow,sub_self]))).resolve_right
      (sub_ne_zero.mpr (hz.ne_one hk2))
  constructor
  · rw [positiveShortSampler,Polynomial.eval_prod]
    apply prod_pos
    intro t ht
    simpa [Polynomial.eval_geom_sum] using (Nat.zero_le (K/2)).trans_lt (mem_Ioc.mp ht).1
  · rw [positiveShortSampler,natDegree_prod_of_monic _ _ (fun t ht =>
      monic_geom_sum_X (by have := (mem_Ioc.mp ht).1; omega))]
    apply sum_le_sum
    intro t ht
    apply natDegree_sum_le_of_forall_le
    intro i hi
    simp only [natDegree_X_pow]
    have := mem_range.mp hi
    omega

/-- The minimum-span signed sampler before normalization has integer coefficients. -/
def integralShortSampler (K : ℕ) : ℤ[X] := ∏ k ∈ Icc 2 K, cyclotomic k ℤ

private theorem integral_map (K : ℕ) :
    (integralShortSampler K).map (Int.castRingHom ℂ) = shortPeriodFilter K := by
  simp only [integralShortSampler,Polynomial.map_prod,map_cyclotomic,shortPeriodFilter_eq_cyclotomics]

/-- Exact mass of the monic integral filter. -/
theorem integralShortSampler_mass (K : ℕ) : (integralShortSampler K).eval 1 = Nat.lcmUpto K := by
  have hpos (n : ℕ) (hn : 2 ≤ n) : 0 < (cyclotomic n ℤ).eval 1 := by
    rcases eq_or_lt_of_le hn with rfl | h
    · norm_num [cyclotomic_two]
    · exact cyclotomic_pos h
  have hp : 0 < (integralShortSampler K).eval 1 := by
    rw [integralShortSampler,Polynomial.eval_prod]
    exact prod_pos fun n hn => hpos n (mem_Icc.mp hn).1
  have he : Real.log (((integralShortSampler K).eval 1 : ℤ):ℝ) = Chebyshev.psi (K:ℝ) := by
    rw [integralShortSampler,Polynomial.eval_prod,Int.cast_prod,Real.log_prod (fun n hn =>
        Int.cast_ne_zero.mpr (hpos n (mem_Icc.mp hn).1).ne'),Chebyshev.psi,Nat.floor_natCast]
    calc _ = ∑ n ∈ Icc 2 K, ArithmeticFunction.vonMangoldt n :=
           sum_congr rfl fun n hn => (SignFreePurityMechanisms.vonMangoldt_eq_log_eval_one_cyclotomic
             (mem_Icc.mp hn).1).symm
         _ = _ := sum_subset (fun n hn => mem_Ioc.mpr ⟨by have := (mem_Icc.mp hn).1; omega,(mem_Icc.mp hn).2⟩)
           (fun n hn h => by
             obtain rfl : n=1 := by have := mem_Ioc.mp hn; have := mt mem_Icc.mpr h; omega
             simp)
  rw [Chebyshev.psi_eq_log_lcmUpto] at he
  have hv := Real.strictMonoOn_log.injOn (by exact_mod_cast hp)
    (by exact_mod_cast Nat.lcmUpto_pos K) he
  exact_mod_cast hv

/-- Every exact integral sampler has total mass divisible by this same least common multiple.
The monic extremizer attains the minimum nonzero mass and minimum span simultaneously. -/
theorem integral_sampler_mass_divisibility (K : ℕ) (p : ℤ[X])
    (h : EquidistributesThrough K (p.map (Int.castRingHom ℂ))) :
    (Nat.lcmUpto K : ℤ) ∣ p.eval 1 := by
  have hd := (equidistributesThrough_iff_dvd K _).mp h
  rw [←integral_map] at hd
  have hm : (integralShortSampler K).Monic := monic_prod_of_monic _ _ (fun n _ => cyclotomic.monic n ℤ)
  obtain ⟨q,hq⟩ := (Polynomial.map_dvd_map (Int.castRingHom ℂ) Int.cast_injective hm).mp hd
  exact ⟨q.eval 1,by rw [hq,Polynomial.eval_mul,integralShortSampler_mass]⟩


end

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
