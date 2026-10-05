import GaloisForLFunctions.RHTower.ChiRamanujanJointBaseLimit
import GaloisForLFunctions.RHTower.ChiRamanujanMixedBaseLimit

/-!
# Complete masked Mellin source

Factor the original labelled prime product with both contractions excluded.
The allowed first/second coincidence contributes its exact local response,
not the product of two independent responses. The growing base-product limit
proves eventual nonvanishing of every local denominator, so the final moving
family identities have no nonvanishing premise. Both original cofactors and
the entire unlabelled valuation trace remain in the completed source.

The full-row expansion retains all collision corrections, including the
triple term c*(2*a*b-d). Actual response row asymptotics and physical signed
axes cancellation are still separate obligations.
-/

open scoped BigOperators Topology
open Filter
noncomputable section
namespace RHTower.BAGTrace

def criticalLocalMellinBase (p : Nat.Primes) (s t : ℂ) : ℂ :=
  weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p s) (cubicPrimeBase p t)

def criticalFirstMellinResponse (p : Nat.Primes) (s t : ℂ) : ℂ :=
  (cubicPrimeBase p s)⁻¹ *
    weightedConeEulerMinusOne (cubicPrimeBase p 1) (cubicPrimeBase p s) (cubicPrimeBase p t) /
      criticalLocalMellinBase p s t

def criticalSecondMellinResponse (p : Nat.Primes) (s t : ℂ) : ℂ :=
  (cubicPrimeBase p t)⁻¹ *
    weightedConeEulerMinusOne (cubicPrimeBase p 1) (cubicPrimeBase p s) (cubicPrimeBase p t) /
      criticalLocalMellinBase p s t

def criticalThirdMellinResponse (p : Nat.Primes) (s t : ℂ) : ℂ :=
  weightedConeEuler (cubicPrimeBase p 1) (cubicPrimeBase p s) (cubicPrimeBase p t) 1 /
    criticalLocalMellinBase p s t

def criticalPairMellinResponse (p : Nat.Primes) (s t : ℂ) : ℂ :=
  (cubicPrimeBase p s)⁻¹ * (cubicPrimeBase p t)⁻¹ *
    weightedConeEulerMinusTwo (cubicPrimeBase p 1) (cubicPrimeBase p s) (cubicPrimeBase p t) /
      criticalLocalMellinBase p s t

private theorem label_pair_local (P : Finset Nat.Primes) (p r ℓ : P)
    (hpr : p ≠ r) (s t : ℂ) (hE : criticalLocalMellinBase ℓ s t ≠ 0) :
    (cubicPrimeBase ℓ s)^(-criticalLabelShift p ℓ)*
      (cubicPrimeBase ℓ t)^(-criticalLabelShift p ℓ)*
      weightedConeEuler (cubicPrimeBase ℓ 1) (cubicPrimeBase ℓ s) (cubicPrimeBase ℓ t)
        (criticalLabelShift r ℓ-criticalLabelShift p ℓ-criticalLabelShift p ℓ) =
      criticalLocalMellinBase ℓ s t *
        (if ℓ=p then criticalPairMellinResponse ℓ s t else 1)*
        (if ℓ=r then criticalThirdMellinResponse ℓ s t else 1) := by
  by_cases hp : ℓ=p
  · subst ℓ
    simp only [criticalLabelShift,if_true,if_neg hpr]
    norm_num only [weightedConeEuler,Int.reduceSub,Int.reduceNeg,
      Int.reduceEq,if_true,if_false,zpow_neg_one,mul_one]
    unfold criticalPairMellinResponse
    field_simp
  · by_cases hr : ℓ=r
    · subst ℓ
      simp only [criticalLabelShift,if_neg hp,if_true,sub_zero,neg_zero,zpow_zero,one_mul]
      unfold criticalThirdMellinResponse
      field_simp
    · simp [criticalLabelShift,hp,hr,weightedConeEuler,criticalLocalMellinBase]

private theorem label_distinct_local (P : Finset Nat.Primes) (p q r ℓ : P)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (s t : ℂ)
    (hE : criticalLocalMellinBase ℓ s t ≠ 0) :
    (cubicPrimeBase ℓ s)^(-criticalLabelShift p ℓ)*
      (cubicPrimeBase ℓ t)^(-criticalLabelShift q ℓ)*
      weightedConeEuler (cubicPrimeBase ℓ 1) (cubicPrimeBase ℓ s) (cubicPrimeBase ℓ t)
        (criticalLabelShift r ℓ-criticalLabelShift p ℓ-criticalLabelShift q ℓ) =
      criticalLocalMellinBase ℓ s t *
        (if ℓ=p then criticalFirstMellinResponse ℓ s t else 1)*
        (if ℓ=q then criticalSecondMellinResponse ℓ s t else 1)*
        (if ℓ=r then criticalThirdMellinResponse ℓ s t else 1) := by
  by_cases hp : ℓ=p
  · subst ℓ
    simp only [criticalLabelShift,if_true,if_neg hpq,if_neg hpr,sub_zero]
    norm_num only [weightedConeEuler,Int.reduceSub,Int.reduceNeg,
      Int.reduceEq,if_true,if_false,zpow_neg_one,zpow_zero,mul_one,one_mul]
    unfold criticalFirstMellinResponse
    field_simp
  · by_cases hq : ℓ=q
    · subst ℓ
      simp only [criticalLabelShift,if_true,if_neg hp,if_neg hqr,sub_zero]
      norm_num only [weightedConeEuler,Int.reduceSub,Int.reduceNeg,
        Int.reduceEq,if_true,if_false,zpow_neg_one,zpow_zero,mul_one,one_mul]
      unfold criticalSecondMellinResponse
      field_simp
    · by_cases hr : ℓ=r
      · subst ℓ
        simp only [criticalLabelShift,if_neg hp,if_neg hq,if_true,
          sub_zero,neg_zero,zpow_zero,one_mul]
        unfold criticalThirdMellinResponse
        field_simp
      · simp [criticalLabelShift,hp,hq,hr,weightedConeEuler,criticalLocalMellinBase]

private theorem label_factored (P : Finset Nat.Primes) (p q r : P)
    (hpr : p ≠ r) (hqr : q ≠ r) (s t : ℂ)
    (hE : ∀ ℓ : P, criticalLocalMellinBase ℓ s t ≠ 0) :
    criticalWeightedLabelEuler P p q r s t =
      (criticalPrimeNormalization P : ℂ)^3 *
      (∏ ℓ : P, criticalLocalMellinBase ℓ s t) *
      (criticalPrimeLabelWeight p : ℂ)*(criticalPrimeLabelWeight q : ℂ)*
      (criticalPrimeLabelWeight r : ℂ)*criticalThirdMellinResponse r s t *
      (if p=q then criticalPairMellinResponse p s t else
        criticalFirstMellinResponse p s t*criticalSecondMellinResponse q s t) := by
  unfold criticalWeightedLabelEuler
  push_cast
  by_cases hpq : p=q
  · subst q
    simp_rw [label_pair_local P p r _ hpr s t (hE _)]
    simp only [Finset.prod_mul_distrib,Fintype.prod_ite_eq',if_true]
    ring
  · simp_rw [label_distinct_local P p q r _ hpq hpr hqr s t (hE _)]
    simp only [Finset.prod_mul_distrib,Fintype.prod_ite_eq',if_neg hpq]
    ring

private theorem masked_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w a b c d : ι → ℂ) :
    (∑ r, ∑ p, ∑ q, if p=r ∨ q=r then 0 else
      w p*w q*w r*c r*(if p=q then d p else a p*b q)) =
    ∑ r, w r*c r*((∑ p, if p=r then 0 else w p*a p)*
      (∑ q, if q=r then 0 else w q*b q)+
      ∑ p, if p=r then 0 else (w p)^2*(d p-a p*b p)) := by
  apply Finset.sum_congr rfl
  intro r _
  have he (p q : ι) : (if p=r ∨ q=r then 0 else
      w p*w q*w r*c r*(if p=q then d p else a p*b q)) =
      w r*c r*((if p=r then 0 else w p*a p)*(if q=r then 0 else w q*b q)+
        (if p=q ∧ p≠r then (w p)^2*(d p-a p*b p) else 0)) := by
    by_cases hpr : p=r
    · subst p
      simp
    · by_cases hqr : q=r
      · subst q
        simp [hpr]
      · by_cases hpq : p=q
        · subst q
          simp [hpr]
          ring
        · simp [hpr,hqr,hpq]
          ring
  simp_rw [he]
  have hd (p : ι) : (∑ q, if p=q ∧ p≠r then (w p)^2*(d p-a p*b p) else 0) =
      if p=r then 0 else (w p)^2*(d p-a p*b p) := by
    by_cases hpr : p=r
    · simp [hpr]
    · simp [hpr]
  simp_rw [← Finset.mul_sum,Finset.sum_add_distrib,hd]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The complete three-label response, with both contractions excluded
and the coincident first/second label retained exactly. -/
def criticalMaskedMellinResponse (P : Finset Nat.Primes) (s t : ℂ) : ℂ :=
  ∑ r : P, (criticalPrimeLabelWeight r : ℂ)*criticalThirdMellinResponse r s t *
    ((∑ p : P, if p=r then 0 else
      (criticalPrimeLabelWeight p : ℂ)*criticalFirstMellinResponse p s t)*
     (∑ q : P, if q=r then 0 else
      (criticalPrimeLabelWeight q : ℂ)*criticalSecondMellinResponse q s t)+
     ∑ p : P, if p=r then 0 else (criticalPrimeLabelWeight p : ℂ)^2*
       (criticalPairMellinResponse p s t-
        criticalFirstMellinResponse p s t*criticalSecondMellinResponse p s t))

private theorem cone_response_eq (P : Finset Nat.Primes) (s t : ℂ)
    (hE : ∀ ℓ : P, criticalLocalMellinBase ℓ s t ≠ 0) :
    criticalWeightedConeEuler P s t = (criticalPrimeNormalization P : ℂ)^3 *
      (∏ ℓ : P, criticalLocalMellinBase ℓ s t)*criticalMaskedMellinResponse P s t := by
  have he (p q r : P) : (if p=r ∨ q=r then 0 else criticalWeightedLabelEuler P p q r s t) =
      ((criticalPrimeNormalization P : ℂ)^3 * (∏ ℓ : P, criticalLocalMellinBase ℓ s t))*
      (if p=r ∨ q=r then 0 else
        (criticalPrimeLabelWeight p : ℂ)*(criticalPrimeLabelWeight q : ℂ)*
        (criticalPrimeLabelWeight r : ℂ)*criticalThirdMellinResponse r s t*
        (if p=q then criticalPairMellinResponse p s t else
          criticalFirstMellinResponse p s t*criticalSecondMellinResponse q s t)) := by
    by_cases hm : p=r ∨ q=r
    · simp [hm]
    · rw [if_neg hm,if_neg hm,label_factored P p q r
        (fun h => hm (.inl h)) (fun h => hm (.inr h)) s t hE]
      ring
  unfold criticalWeightedConeEuler
  simp_rw [he,← Finset.mul_sum]
  rw [masked_rows]
  rfl

/-- Every local unlabelled factor is eventually nonzero on the actual
growing two-variable Mellin family, without a nonvanishing premise. -/
theorem criticalLocalMellinBase_eventually_ne_zero (u v : ℂ) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Sieve.primeSubtypeLE N,
      criticalLocalMellinBase p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)) ≠ 0 := by
  have h := (criticalJointBaseProduct_tendsto u v).eventually_ne (Complex.exp_ne_zero _)
  filter_upwards [h] with N hN p
  have hp := (Finset.prod_ne_zero_iff.mp hN) p.val p.property
  exact (mul_ne_zero_iff.mp hp).2

/-- Exact collision-aware assembly of the full growing labelled cone. -/
theorem criticalWeightedConeEuler_moving_response (u v : ℂ) :
    ∀ᶠ N : ℕ in atTop,
      criticalWeightedConeEuler (Sieve.primeSubtypeLE N)
        (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)) =
      (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ)^3 *
      (∏ p : Sieve.primeSubtypeLE N,
        criticalLocalMellinBase p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)))*
      criticalMaskedMellinResponse (Sieve.primeSubtypeLE N)
        (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)) := by
  filter_upwards [criticalLocalMellinBase_eventually_ne_zero u v] with N hN
  exact cone_response_eq _ _ _ hN

private theorem moving_re_eventually_pos (u : ℂ) :
    ∀ᶠ N : ℕ in atTop, 0 < (1+u/(Real.log N : ℂ)).re := by
  have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp (tendsto_drift_zero 1)
  have hd : Tendsto (fun N : ℕ => u/(Real.log N : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_one,
      Complex.ofReal_zero,mul_zero,mul_one_div] using h.const_mul u
  have ht := (Complex.continuous_re.tendsto _).comp
    ((tendsto_const_nhds (x := (1 : ℂ))).add hd)
  exact ht.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < (1+(0 : ℂ)).re))

/-- The original completed growing source is exactly its entire unlabelled
cofactor trace times the complete collision-aware labelled response. -/
theorem criticalCompletedConeEuler_moving_response (u v : ℂ) :
    ∀ᶠ N : ℕ in atTop,
      criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
        (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)) =
      (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ)^3 *
      criticalMaskedMellinResponse (Sieve.primeSubtypeLE N)
        (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)) *
      (criticalCofactor (Sieve.primeSubtypeLE N) (1+u/(Real.log N : ℂ))*
        criticalCofactor (Sieve.primeSubtypeLE N) (1+v/(Real.log N : ℂ))*
        weightedTrace 1 (u/(Real.log N : ℂ)) (v/(Real.log N : ℂ))
          (Sieve.primeSubtypeLE N)) := by
  filter_upwards [criticalWeightedConeEuler_moving_response u v,
    moving_re_eventually_pos u,moving_re_eventually_pos v] with N hN hu hv
  rw [criticalCompletedConeEuler,hN,weightedTrace_eq hu hv]
  have hp : (∏ p : Sieve.primeSubtypeLE N,
      criticalLocalMellinBase p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ))) =
      ∏ p ∈ Sieve.primeSubtypeLE N,
        weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p (1+u/(Real.log N : ℂ)))
          (cubicPrimeBase p (1+v/(Real.log N : ℂ))) :=
    Finset.prod_coe_sort (Sieve.primeSubtypeLE N)
      (fun p : Nat.Primes => criticalLocalMellinBase p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)))
  rw [hp]
  ring

private theorem excluded_response_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w a b c d : ι → ℂ) :
    (∑ r, w r*c r*((∑ p, if p=r then 0 else w p*a p)*
      (∑ q, if q=r then 0 else w q*b q)+
      ∑ p, if p=r then 0 else (w p)^2*(d p-a p*b p))) =
    (∑ p,w p*a p)*(∑ p,w p*b p)*(∑ p,w p*c p)+
    (∑ p,w p*c p)*(∑ p,(w p)^2*(d p-a p*b p))-
    (∑ p,w p*a p)*(∑ p,(w p)^2*b p*c p)-
    (∑ p,w p*b p)*(∑ p,(w p)^2*a p*c p)+
    ∑ p,(w p)^3*c p*(2*a p*b p-d p) := by
  have hex (f : ι → ℂ) (r : ι) :
      (∑ p,if p=r then 0 else f p) = (∑ p,f p)-f r := by
    have he (p : ι) : (if p=r then 0 else f p) = f p-(if p=r then f p else 0) := by
      by_cases hp : p=r <;> simp [hp]
    simp_rw [he,Finset.sum_sub_distrib]
    simp
  simp_rw [hex]
  have he (r : ι) :
      w r*c r*(((∑ p,w p*a p)-w r*a r)*((∑ p,w p*b p)-w r*b r)+
        ((∑ p,(w p)^2*(d p-a p*b p))-(w r)^2*(d r-a r*b r))) =
      (∑ p,w p*a p)*(∑ p,w p*b p)*(w r*c r)+
      (∑ p,(w p)^2*(d p-a p*b p))*(w r*c r)-
      (∑ p,w p*a p)*((w r)^2*b r*c r)-
      (∑ p,w p*b p)*((w r)^2*a r*c r)+
      (w r)^3*c r*(2*a r*b r-d r) := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

/-- Exact full-row expansion: the product of the three unrestricted response
rows plus every pair and triple collision correction. -/
theorem criticalMaskedMellinResponse_expansion (P : Finset Nat.Primes) (s t : ℂ) :
    let w : P → ℂ := fun p => criticalPrimeLabelWeight p
    let a : P → ℂ := fun p => criticalFirstMellinResponse p s t
    let b : P → ℂ := fun p => criticalSecondMellinResponse p s t
    let c : P → ℂ := fun p => criticalThirdMellinResponse p s t
    let d : P → ℂ := fun p => criticalPairMellinResponse p s t
    criticalMaskedMellinResponse P s t =
      (∑ p,w p*a p)*(∑ p,w p*b p)*(∑ p,w p*c p)+
      (∑ p,w p*c p)*(∑ p,(w p)^2*(d p-a p*b p))-
      (∑ p,w p*a p)*(∑ p,(w p)^2*b p*c p)-
      (∑ p,w p*b p)*(∑ p,(w p)^2*a p*c p)+
      ∑ p,(w p)^3*c p*(2*a p*b p-d p) :=
  excluded_response_expansion _ _ _ _ _

/-- The full original mixed-frequency source factors into the complete masked
response and both growing coprime cofactors. All local nonvanishing is proved. -/
theorem criticalCompletedConeEuler_mixed_response (u v : ℂ) (tau : ℝˣ) :
    ∀ᶠ N : ℕ in atTop,
      criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
        (1+u/(Real.log N : ℂ)) (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)) =
      (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ)^3 *
      criticalMaskedMellinResponse (Sieve.primeSubtypeLE N)
        (1+u/(Real.log N : ℂ)) (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)) *
      (criticalCofactor (Sieve.primeSubtypeLE N) (1+u/(Real.log N : ℂ))*
        criticalCofactor (Sieve.primeSubtypeLE N) (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I))*
        weightedTrace 1 (u/(Real.log N : ℂ)) (v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)
          (Sieve.primeSubtypeLE N)) := by
  filter_upwards [criticalMixedLocalEuler_eventually_ne_zero u v tau,
    moving_re_eventually_pos u,moving_re_eventually_pos v] with N hE hu hv
  have hv' : 0 < (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)).re := by simpa using hv
  have hE' : ∀ p : Sieve.primeSubtypeLE N,
      criticalLocalMellinBase p (1+u/(Real.log N : ℂ))
        (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)) ≠ 0 := hE
  rw [criticalCompletedConeEuler,cone_response_eq _ _ _ hE',weightedTrace_eq hu hv']
  have hp : (∏ p : Sieve.primeSubtypeLE N,
      criticalLocalMellinBase p (1+u/(Real.log N : ℂ)) (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I))) =
      ∏ p ∈ Sieve.primeSubtypeLE N,
        weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p (1+u/(Real.log N : ℂ)))
          (cubicPrimeBase p (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I))) :=
    Finset.prod_coe_sort (Sieve.primeSubtypeLE N)
      (fun p : Nat.Primes => criticalLocalMellinBase p (1+u/(Real.log N : ℂ))
        (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)))
  rw [hp]
  ring

end RHTower.BAGTrace
