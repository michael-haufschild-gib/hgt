import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.IndependentQuotientDigitsAtOneNumerator
import GaloisForLFunctions.HTGeometry.ThreeFiveOrbitKorobovBound

/-!
# Exponential laws for grouped quotient digits

At a fixed two-adic order the signs of all odd cores reverse together.
Earlier signs remain fixed. This gives a conditional two-point average even
when the weights depend on earlier bits and when many denominators share
an order. Dividing each exponential by its conditional mean gives an exact
identity at every starting numerator.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open Finset
noncomputable section
open scoped Classical

/-- The coefficient at order i may depend on the first i bits of q.
All denominators in this sum have the same two-adic order. -/
def groupedQuotientDigit {ι : Type*} (D : ℕ → Finset ι) (d : ℕ → ι → ℕ)
    (a : ℕ → ι → ℕ → ℝ) (H U i q : ℕ) : ℝ :=
  ∑ t ∈ D i, a i t (q % 2^i)*quotientSign (2^i*d i t) (H+q*U)

private theorem grouped_flip {ι : Type*} (D : ℕ → Finset ι) (d : ℕ → ι → ℕ)
    (a : ℕ → ι → ℕ → ℝ) (H U : ℕ) (hu : Odd U) (hd : ∀ i, ∀ t∈D i, d i t∣U)
    {i j : ℕ} (hij : i≤j) (q : ℕ) :
    groupedQuotientDigit D d a H U i (2^j+q) = if i=j then
      -groupedQuotientDigit D d a H U i q else groupedQuotientDigit D d a H U i q := by
  have hm : (2^j+q)%2^i = q%2^i := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 hij),Nat.zero_add,Nat.mod_mod]
  unfold groupedQuotientDigit
  rw [hm]
  by_cases he : i=j
  · rw [if_pos he,← sum_neg_distrib]
    refine sum_congr rfl fun t ht => ?_
    rw [quotientSign_dyadic_translate hu (hd i t ht) hij,if_pos he,mul_neg]
  · rw [if_neg he]
    refine sum_congr rfl fun t ht => ?_
    rw [quotientSign_dyadic_translate hu (hd i t ht) hij,if_neg he]

private def expWeight (x : ℝ) : ℝ := Real.exp x / Real.cosh x

private theorem expWeight_pair (x : ℝ) : expWeight x+expWeight (-x)=2 := by
  rw [expWeight,expWeight,Real.cosh_neg,← add_div,div_eq_iff (Real.cosh_pos x).ne',Real.cosh_eq]
  ring

/-- Exactly normalized exponential moment with the realized conditional
cosh factors. No independence within an order is required. -/
theorem grouped_quotient_exponential_identity {ι : Type*}
    (D : ℕ → Finset ι) (d : ℕ → ι → ℕ) (a : ℕ → ι → ℕ → ℝ)
    (H U : ℕ) (hu : Odd U) (hd : ∀ i, ∀ t∈D i, d i t∣U) (k : ℕ) :
    let X := groupedQuotientDigit D d a H U
    ∑ q ∈ range (2^k), ∏ i ∈ range k, Real.exp (X i q)/Real.cosh (X i q) = (2:ℝ)^k := by
  let X := groupedQuotientDigit D d a H U
  let W (k q : ℕ) := ∏ i ∈ range k, expWeight (X i q)
  change ∑ q ∈ range (2^k), W k q = (2:ℝ)^k
  induction k with
  | zero => simp [W]
  | succ k ih =>
    have block (q : ℕ) : W (k+1) q + W (k+1) (2^k+q) = W k q*2 := by
      have unchanged : W k (2^k+q)=W k q := by
        refine prod_congr rfl fun i hi => ?_
        have hi' := mem_range.mp hi
        exact congrArg expWeight ((grouped_flip D d a H U hu hd hi'.le q).trans (if_neg hi'.ne))
      have flip : X k (2^k+q) = -X k q :=
        (grouped_flip D d a H U hu hd (le_refl k) q).trans (if_pos rfl)
      change (∏ i ∈ range (k+1), expWeight (X i q))+
        (∏ i ∈ range (k+1), expWeight (X i (2^k+q)))=_
      rw [prod_range_succ,prod_range_succ]
      change W k q*expWeight (X k q)+W k (2^k+q)*expWeight (X k (2^k+q))=_
      rw [unchanged,flip,← mul_add,expWeight_pair]
    rw [pow_succ,Nat.mul_two,sum_range_add,← sum_add_distrib,sum_congr rfl (fun q _ => block q),
      ← sum_mul,ih,pow_succ]

/-- The observed squared increments control the exponential moment for
each progression. Opposite signs within a dyadic order cancel before
the square is taken. -/
theorem grouped_quotient_self_normalized {ι : Type*}
    (D : ℕ → Finset ι) (d : ℕ → ι → ℕ) (a : ℕ → ι → ℕ → ℝ)
    (H U : ℕ) (hu : Odd U) (hd : ∀ i, ∀ t∈D i, d i t∣U) (k : ℕ) :
    let X := groupedQuotientDigit D d a H U
    ∑ q ∈ range (2^k), Real.exp ((∑ i ∈ range k, X i q) -
      (∑ i ∈ range k, (X i q)^2)/2) ≤ (2:ℝ)^k := by
  let X := groupedQuotientDigit D d a H U
  apply le_trans _ (grouped_quotient_exponential_identity D d a H U hu hd k).le
  refine sum_le_sum fun q _ => ?_
  rw [sum_div,← sum_sub_distrib,Real.exp_sum]
  refine prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i _ => ?_
  rw [Real.exp_sub]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.cosh_pos _) (Real.cosh_le_exp_half_sq _)

/-- Finite-block one-sided bound at a prescribed level of the realized
quadratic variation. The weights can already include any exponential tilt. -/
theorem grouped_quotient_tail {ι : Type*}
    (D : ℕ → Finset ι) (d : ℕ → ι → ℕ) (a : ℕ → ι → ℕ → ℝ)
    (H U : ℕ) (hu : Odd U) (hd : ∀ i, ∀ t∈D i, d i t∣U) (k : ℕ) (b v : ℝ) :
    let X := groupedQuotientDigit D d a H U
    (((range (2^k)).filter fun q => b ≤ (∑ i ∈ range k, X i q) ∧
      (∑ i ∈ range k,(X i q)^2) ≤ v).card : ℝ) ≤ (2:ℝ)^k*Real.exp (v/2-b) := by
  let X := groupedQuotientDigit D d a H U
  let E (q : ℕ) := (∑ i ∈ range k, X i q) - (∑ i ∈ range k, (X i q)^2)/2
  let S := (range (2^k)).filter fun q => b ≤ (∑ i ∈ range k, X i q) ∧ (∑ i ∈ range k,(X i q)^2)≤v
  have h : (S.card:ℝ)*Real.exp (b-v/2) ≤ (2:ℝ)^k := calc
    _ = ∑ _ ∈ S, Real.exp (b-v/2) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ∑ q ∈ S, Real.exp (E q) := by
      refine sum_le_sum fun q hq => Real.exp_le_exp.mpr ?_
      obtain ⟨hs,hv⟩ := (mem_filter.mp hq).2
      dsimp only [E]
      linarith only [hs,hv]
    _ ≤ ∑ q ∈ range (2^k), Real.exp (E q) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => (Real.exp_pos _).le
    _ ≤ _ := grouped_quotient_self_normalized D d a H U hu hd k
  change (S.card:ℝ) ≤ _
  rw [show v/2-b= -(b-v/2) by ring,Real.exp_neg,←div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr h

/-- Signed contribution from the denominators of one two-adic order. -/
def fixedBandQuotientLevel (S : Finset ℕ) (a : ℕ → ℝ) (i H : ℕ) : ℝ :=
  ∑ n ∈ S.filter (fun n => n.factorization 2=i), a n*quotientSign n H

private theorem oddCore_factorization (n : ℕ) (hn : 0<n) :
    Odd (n / 2^(n.factorization 2)) ∧ n=2^(n.factorization 2)*(n/2^(n.factorization 2)) := by
  obtain ⟨i,d,ho,he⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hd : d≠0 := by obtain ⟨j,hj⟩ := ho; omega
  have hnd : ¬2∣d := by
    obtain ⟨j,hj⟩ := ho
    rintro ⟨b,hb⟩
    omega
  have hv : n.factorization 2=i := by
    rw [he,Nat.factorization_mul (by positivity) hd,Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,Nat.factorization_eq_zero_of_not_dvd hnd,add_zero]
  have hquot : n/2^i=d := by rw [he,Nat.mul_div_cancel_left _ (by positivity)]
  rw [hv,hquot]
  exact ⟨ho,he⟩

/-- Odd step and depth of the dyadic decomposition of a common multiple. -/
def quotientOddStep (L : ℕ) := L/2^(L.factorization 2)

def quotientDepth (L : ℕ) := L.factorization 2+1

/-- For any positive common multiple L of the denominators, the odd part
of L is the progression step and twice its two-part is the block length.
The identity holds for all starting numerators and all signed weights. -/
theorem fixed_band_quotient_exponential (S : Finset ℕ) {L : ℕ} (hL : 0<L)
    (hdiv : ∀ n∈S, n∣L) :
    let U := quotientOddStep L
    let k := quotientDepth L
    ∀ (H : ℕ) (a : ℕ → ℝ),
      ∑ q ∈ range (2^k), Real.exp (∑ n ∈ S, a n*quotientSign n (H+q*U)) /
        (∏ i ∈ range k, Real.cosh (fixedBandQuotientLevel S a i (H+q*U))) = (2:ℝ)^k := by
  let v (n : ℕ) := n.factorization 2
  let d (n : ℕ) := n/2^(v n)
  let U := quotientOddStep L
  let k := quotientDepth L
  let D (i : ℕ) := S.filter fun n => v n=i
  have hp (n : ℕ) (hn : n∈S) : 0<n := Nat.pos_of_dvd_of_pos (hdiv n hn) hL
  have hu : Odd U := (oddCore_factorization L hL).1
  have hd : ∀ i, ∀ n∈D i, d n∣U := fun _ n hn =>
    Nat.ordCompl_dvd_ordCompl_of_dvd (hdiv n (mem_filter.mp hn).1) 2
  dsimp only
  intro H a
  let X := groupedQuotientDigit D (fun _ n => d n) (fun _ n _ => a n) H U
  have levels (i q : ℕ) : X i q = fixedBandQuotientLevel S a i (H+q*U) := by
    refine sum_congr rfl fun n hn => ?_
    obtain ⟨hs,hi⟩ := mem_filter.mp hn
    have he := (oddCore_factorization n (hp n hs)).2
    change n=2^(v n)*d n at he
    change v n=i at hi
    rw [hi] at he
    change a n*quotientSign (2^i*d n) (H+q*U) = a n*quotientSign n (H+q*U)
    rw [← he]
  have allLevels (q : ℕ) : ∑ i ∈ range k, X i q = ∑ n ∈ S, a n*quotientSign n (H+q*U) := by
    simp only [levels,fixedBandQuotientLevel,sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun n hn => ?_
    have hv : v n∈range k := mem_range.mpr (Nat.lt_succ_of_le
      (((Nat.factorization_le_iff_dvd (hp n hn).ne' hL.ne').mpr (hdiv n hn)) 2))
    rw [sum_eq_single_of_mem (v n) hv]
    · exact if_pos rfl
    · intro i _ hi
      exact if_neg hi.symm
  have h := grouped_quotient_exponential_identity D (fun _ n => d n)
    (fun _ n _ => a n) H U hu hd k
  change (∑ q ∈ range (2^k), ∏ i ∈ range k, Real.exp (X i q)/Real.cosh (X i q)) = _ at h
  rw [← h]
  refine sum_congr rfl fun q _ => ?_
  rw [prod_div_distrib,←Real.exp_sum,allLevels]
  simp only [levels,U,k]

/-- The exponential identity on a contiguous interval of exactly twice
the least common multiple. Summing over the odd residue classes eliminates
the progression restriction without enlarging the common period. -/
theorem contiguous_band_quotient_exponential (S : Finset ℕ) (hp : ∀ n∈S, 0<n)
    (H : ℕ) (a : ℕ → ℝ) :
    let L := S.lcm id
    ∑ r ∈ range (2*L), Real.exp (∑ n ∈ S, a n*quotientSign n (H+r)) /
      (∏ i ∈ range (quotientDepth L), Real.cosh (fixedBandQuotientLevel S a i (H+r))) =
      ((2*L : ℕ):ℝ) := by
  let L := S.lcm id
  let U := quotientOddStep L
  let k := quotientDepth L
  let F (x : ℕ) := Real.exp (∑ n ∈ S, a n*quotientSign n x) /
    (∏ i ∈ range k, Real.cosh (fixedBandQuotientLevel S a i x))
  have hL : 0<L := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun n hn => (hp n hn).ne'))
  have hd (n : ℕ) (hn : n∈S) : n∣L := Finset.dvd_lcm (f:=id) hn
  have period : U*2^k=2*L := calc
    _ = (2^(L.factorization 2)*(L/2^(L.factorization 2)))*2 := by
      dsimp only [U,k,quotientOddStep,quotientDepth]
      rw [pow_succ]
      ring
    _ = 2*L := by rw [← (oddCore_factorization L hL).2,Nat.mul_comm]
  have block (r : ℕ) : ∑ q ∈ range (2^k), F ((H+r)+q*U)=(2:ℝ)^k :=
    fixed_band_quotient_exponential S hL hd (H+r) a
  change (∑ r ∈ range (2*L), F (H+r))=((2*L:ℕ):ℝ)
  rw [← period,HTGeometry.ThreeFiveOrbit.sum_range_mul_eq_sum_sum]
  have inner (r : ℕ) : ∑ q ∈ range (2^k), F (H+(r+U*q))=(2:ℝ)^k := by
    simpa only [Nat.mul_comm U,Nat.add_assoc] using block r
  rw [sum_congr rfl (fun r _ => inner r),sum_const,card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_ofNat]

/-- The exactly normalized exponential of the centered prime discrepancy
has mean one on a full contiguous period, for every real tilt. -/
theorem centered_prime_exponential_identity (S : Finset ℕ) (hp : ∀ n∈S, 0<n) (H : ℕ) (l : ℝ) :
    let L := S.lcm id
    ∑ q ∈ range (2*L), Real.exp (l*centeredQuotientReading S (H+q)) /
      (∏ i ∈ range (quotientDepth L),
        Real.cosh (l*fixedBandQuotientLevel S ordinaryPrimeExcessCoeff i (H+q))) = ((2*L:ℕ):ℝ) := by
  simpa only [centeredQuotientReading_eq,fixedBandQuotientLevel,mul_sum,mul_assoc] using
    contiguous_band_quotient_exponential S hp H (fun n => l*ordinaryPrimeExcessCoeff n)

#print axioms contiguous_band_quotient_exponential
#print axioms fixed_band_quotient_exponential
#print axioms centered_prime_exponential_identity

#print axioms grouped_quotient_exponential_identity
#print axioms grouped_quotient_self_normalized
#print axioms grouped_quotient_tail

end
end GaloisForLFunctions.ExclusionOfTheCriticalState
