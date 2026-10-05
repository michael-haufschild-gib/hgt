import GaloisForLFunctions.RHTower.ChiRamanujanShiftedCubicTrace
import GaloisForLFunctions.RHTower.ChiRamanujanCriticalGridSource

/-!
# Signed balanced cone with the two physical label exclusions

The actual critical grid normalizes each local base as `(1-z)*c_z(i)`
and each distinguished prime as `(1-z)*z*c_z(i+1)`. Sum the complete
finite-prime valuation pair lattice, retaining exactly the labels left by
both physical contraction projectors. The signed trace is an explicit
negative sum of squares, strictly negative exactly when two primes remain.

Numerator cofactors, the full physical profile and its growing cancellation
are separate obligations. This finite valuation-support trace is not the
complete denominator-restricted rational action or an RH proof.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

def criticalPrimeNormalization (P : Finset Nat.Primes) : ℝ :=
  ∏ p : P, (1-1/((p : Nat.Primes) : ℝ))

theorem criticalPrimeNormalization_pos (P : Finset Nat.Primes) :
    0 < criticalPrimeNormalization P := by
  apply Finset.prod_pos
  intro p hp
  have hh : (1 : ℝ) < ((p : Nat.Primes) : ℝ) := by exact_mod_cast p.val.property.one_lt
  have hi : 1/((p : Nat.Primes) : ℝ) < 1 := by
    simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ)<1) hh
  exact sub_pos.mpr hi

def criticalPrimeLabelWeight (p : Nat.Primes) : ℝ := Real.log (p : ℝ)/(p : ℝ)

def criticalThirdLabelWeight (p : Nat.Primes) : ℝ := Real.log (p : ℝ)/((p : ℝ)-1)

def criticalLabelShift {P : Finset Nat.Primes} (p ℓ : P) : ℤ := if ℓ=p then 1 else 0

def criticalLabeledCone (P : Finset Nat.Primes) (p q r : P) (v : P → ℤ × ℤ) : ℝ :=
  criticalPrimeNormalization P^3 * criticalPrimeLabelWeight p * criticalPrimeLabelWeight q *
    criticalPrimeLabelWeight r * ∏ ℓ : P,
      shiftedLocalTriple (1/((ℓ : Nat.Primes) : ℝ))
        (criticalLabelShift p ℓ) (criticalLabelShift q ℓ) (criticalLabelShift r ℓ) (v ℓ)

private lemma labeled_local_hasSum (P : Finset Nat.Primes) (p q r ℓ : P)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    HasSum (shiftedLocalTriple (1/((ℓ : Nat.Primes) : ℝ))
      (criticalLabelShift p ℓ) (criticalLabelShift q ℓ) (criticalLabelShift r ℓ))
      ((if ℓ=r then -(1-1/((ℓ : Nat.Primes) : ℝ))⁻¹ else 1)*
        (1-1/((ℓ : Nat.Primes) : ℝ))⁻¹^2) := by
  convert primeShiftedLocalTriple_hasSum ℓ.val
    (criticalLabelShift p ℓ) (criticalLabelShift q ℓ) (criticalLabelShift r ℓ) using 1
  by_cases hr : ℓ=r
  · subst ℓ
    have hr0 : ((r : Nat.Primes) : ℝ) ≠ 0 := by exact_mod_cast r.val.property.ne_zero
    simp only [criticalLabelShift, Ne.symm hpr, Ne.symm hqr, if_false, if_true,
      zero_add, coefficient]
    norm_num
    field_simp
  · have hc : criticalLabelShift r ℓ=0 := by simp [criticalLabelShift,hr]
    have hs : 0 ≤ criticalLabelShift p ℓ+criticalLabelShift q ℓ := by
      unfold criticalLabelShift
      split_ifs <;> omega
    have he : coefficient (1/((ℓ : Nat.Primes) : ℝ))
        (criticalLabelShift p ℓ+criticalLabelShift q ℓ)=1 := by
      rw [coefficient,if_neg (by omega),if_pos hs]
    rw [if_neg hr,hc]
    simp only [neg_zero,zpow_zero,sub_zero,one_mul,he]

private lemma labeled_raw_hasSum (P : Finset Nat.Primes) (p q r : P)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    HasSum (fun v : P → ℤ × ℤ => ∏ ℓ : P,
      shiftedLocalTriple (1/((ℓ : Nat.Primes) : ℝ))
        (criticalLabelShift p ℓ) (criticalLabelShift q ℓ) (criticalLabelShift r ℓ) (v ℓ))
      (-(1-1/((r : Nat.Primes) : ℝ))⁻¹ * (criticalPrimeNormalization P)⁻¹^2) := by
  have h := finite_product_hasSum P _ _ (fun ℓ => labeled_local_hasSum P p q r ℓ hpr hqr)
  convert h using 1
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ r),
    Finset.prod_pow, Finset.prod_inv_distrib]
  rfl

theorem criticalLabeledCone_hasSum (P : Finset Nat.Primes) (p q r : P)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    HasSum (criticalLabeledCone P p q r)
      (-criticalPrimeNormalization P * criticalThirdLabelWeight r *
        criticalPrimeLabelWeight p * criticalPrimeLabelWeight q) := by
  have h := (labeled_raw_hasSum P p q r hpr hqr).mul_left
    (criticalPrimeNormalization P^3 * criticalPrimeLabelWeight p *
      criticalPrimeLabelWeight q * criticalPrimeLabelWeight r)
  convert h using 1 <;> try rfl
  have hA := (criticalPrimeNormalization_pos P).ne'
  have hr : (1 : ℝ) < ((r : Nat.Primes) : ℝ) := by exact_mod_cast r.val.property.one_lt
  have hr0 : ((r : Nat.Primes) : ℝ) ≠ 0 := by linarith
  have hr1 : ((r : Nat.Primes) : ℝ)-1 ≠ 0 := by linarith
  unfold criticalThirdLabelWeight criticalPrimeLabelWeight
  field_simp

def criticalLabelRow (P : Finset Nat.Primes) (r : P) : ℝ :=
  ∑ p : P, if p=r then 0 else criticalPrimeLabelWeight p

def criticalNoncontractingCone (P : Finset Nat.Primes) (v : P → ℤ × ℤ) : ℝ :=
  ∑ r : P, ∑ p : P, ∑ q : P,
    if p=r ∨ q=r then 0 else criticalLabeledCone P p q r v

private lemma label_row_square (P : Finset Nat.Primes) (r : P) (c : ℝ) :
    (∑ p : P, ∑ q : P, if p=r ∨ q=r then 0 else
      c*criticalPrimeLabelWeight p*criticalPrimeLabelWeight q) = c*criticalLabelRow P r^2 := by
  have he (p q : P) : (if p=r ∨ q=r then 0 else
      c*criticalPrimeLabelWeight p*criticalPrimeLabelWeight q) =
      c*(if p=r then 0 else criticalPrimeLabelWeight p)*
        (if q=r then 0 else criticalPrimeLabelWeight q) := by
    by_cases hp : p=r <;> by_cases hq : q=r <;> simp [hp,hq]
  simp only [he, ← Finset.mul_sum, ← Finset.sum_mul, criticalLabelRow, pow_two]
  ring

theorem criticalNoncontractingCone_hasSum (P : Finset Nat.Primes) :
    HasSum (criticalNoncontractingCone P)
      (-criticalPrimeNormalization P *
        ∑ r : P, criticalThirdLabelWeight r * criticalLabelRow P r^2) := by
  have h (r p q : P) : HasSum
      (fun v => if p=r ∨ q=r then 0 else criticalLabeledCone P p q r v)
      (if p=r ∨ q=r then 0 else -criticalPrimeNormalization P * criticalThirdLabelWeight r *
        criticalPrimeLabelWeight p * criticalPrimeLabelWeight q) := by
    by_cases h : p=r ∨ q=r
    · simpa only [if_pos h] using (hasSum_zero (β := P → ℤ × ℤ) (α := ℝ))
    · simpa only [if_neg h] using criticalLabeledCone_hasSum P p q r
        (fun hp => h (Or.inl hp)) (fun hq => h (Or.inr hq))
  have hs := hasSum_sum (s := Finset.univ) (fun r _ =>
    hasSum_sum (s := Finset.univ) (fun p _ =>
      hasSum_sum (s := Finset.univ) (fun q _ => h r p q)))
  convert hs using 1 <;> try rfl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [label_row_square P r (-criticalPrimeNormalization P*criticalThirdLabelWeight r)]
  ring

theorem criticalLabelRow_eq (P : Finset Nat.Primes) (r : P) :
    criticalLabelRow P r = (∑ p : P, criticalPrimeLabelWeight p)-criticalPrimeLabelWeight r := by
  calc
    _ = ∑ p : P, (criticalPrimeLabelWeight p-
        (if p=r then criticalPrimeLabelWeight r else 0)) := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases h : p=r <;> simp [h]
    _ = _ := by simp [Finset.sum_sub_distrib]

private lemma label_weight_pos (p : Nat.Primes) : 0 < criticalPrimeLabelWeight p := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  exact div_pos (Real.log_pos hp) (by linarith)

private lemma third_weight_pos (p : Nat.Primes) : 0 < criticalThirdLabelWeight p := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  exact div_pos (Real.log_pos hp) (by linarith)

theorem criticalNoncontractingCone_tsum_nonpos (P : Finset Nat.Primes) :
    (∑' v, criticalNoncontractingCone P v) ≤ 0 := by
  rw [(criticalNoncontractingCone_hasSum P).tsum_eq]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (criticalPrimeNormalization_pos P).le)
    (Finset.sum_nonneg (fun r _ => mul_nonneg (third_weight_pos r).le (sq_nonneg _)))

theorem criticalNoncontractingCone_tsum_neg_iff (P : Finset Nat.Primes) :
    (∑' v, criticalNoncontractingCone P v) < 0 ↔ ∃ p q : P, p ≠ q := by
  rw [(criticalNoncontractingCone_hasSum P).tsum_eq]
  constructor
  · intro hn
    by_contra h
    push Not at h
    have hr (r : P) : criticalLabelRow P r=0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [if_pos (h p r)]
    simp only [hr,zero_pow (by omega : 2 ≠ 0),mul_zero,Finset.sum_const_zero] at hn
    exact lt_irrefl _ hn
  · rintro ⟨p,q,hpq⟩
    have hrow : 0 < criticalLabelRow P q := by
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset P))
        (f := fun r : P => if r=q then (0 : ℝ) else criticalPrimeLabelWeight r)
        (fun r _ => by split_ifs <;> first | exact le_rfl | exact (label_weight_pos r).le)
        (Finset.mem_univ p)
      rw [if_neg hpq] at h
      exact (label_weight_pos p).trans_le h
    have hs : 0 < ∑ r : P, criticalThirdLabelWeight r*criticalLabelRow P r^2 :=
      Finset.sum_pos' (fun r _ => mul_nonneg (third_weight_pos r).le (sq_nonneg _))
        ⟨q,Finset.mem_univ q,mul_pos (third_weight_pos q) (sq_pos_of_pos hrow)⟩
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (criticalPrimeNormalization_pos P)) hs

end RHTower.BAGTrace
