import GaloisForLFunctions.RHTower.ChiRamanujanFinsuppTrace
/-!
# Complete shifted valuation cubic trace

Square-sieved critical differentiation singles out prime factors. The associated
valuation shifts cannot be treated by the unshifted trace. This leaf sums the
full shifted pair lattice absolutely, evaluates every integer shift, classifies
its zero set, and specializes to all actual critical prime reciprocals and
finite prime sets. Matching these valuations to the complete physical action
and estimating its growing profile remain separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace


def shiftedLocalTriple (z : ℝ) (a b c : ℤ) (v : ℤ × ℤ) : ℝ :=
  coefficient z (v.1+a)*coefficient z (v.2+b)*coefficient z (v.1+v.2+c)*z^(v.1+v.2)

private lemma coefficient_bound (z : ℝ) (i : ℤ) :
    |coefficient z i| ≤ 1+|z/(1-z)| := by
  unfold coefficient
  split_ifs <;> simp only [abs_one,abs_zero,neg_div,abs_neg] <;>
    linarith [abs_nonneg (z/(1-z))]

private lemma weighted_coefficient {z : ℝ} (hz : z ≠ 0) (i : ℤ) :
    coefficient z i*z^i = geometric z i-(1-z)⁻¹*atom (-1) i := by
  by_cases hi : i = -1
  · subst i
    simp [coefficient,geometric,atom]
    field_simp
  · by_cases h0 : 0 ≤ i <;> simp [coefficient,geometric,atom,hi,h0]

private lemma shifted_weighted_summable {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (a : ℤ) :
    Summable (fun i : ℤ => coefficient z (i+a)*z^i) := by
  have h := ((geometric_hasSum (show |z| < 1 by rwa [abs_of_pos hz])).sub
    ((atom_hasSum (-1)).mul_left (1-z)⁻¹)).summable
  have hc : Summable (fun i : ℤ => coefficient z i*z^i) :=
    h.congr (fun i => (weighted_coefficient hz.ne' i).symm)
  have ht := ((Equiv.addRight a).summable_iff.mpr hc).mul_left (z^(-a))
  apply ht.congr
  intro i
  change z^(-a)*(coefficient z (i+a)*z^(i+a))=coefficient z (i+a)*z^i
  rw [zpow_add₀ hz.ne',zpow_neg]
  field_simp

theorem shiftedLocalTriple_summable {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (a b c : ℤ) : Summable (shiftedLocalTriple z a b c) := by
  have hp := summable_mul_of_summable_norm
    (shifted_weighted_summable hz hz1 a).norm
    (shifted_weighted_summable hz hz1 b).norm
  apply (hp.norm.mul_left (1+|z/(1-z)|)).of_norm_bounded
  intro v
  simp only [shiftedLocalTriple,Real.norm_eq_abs,abs_mul,zpow_add₀ hz.ne',
    abs_of_pos (zpow_pos hz _)]
  nlinarith [mul_le_mul_of_nonneg_left (coefficient_bound z (v.1+v.2+c))
    (mul_nonneg (mul_nonneg (abs_nonneg (coefficient z (v.1+a)))
      (abs_nonneg (coefficient z (v.2+b))))
      (mul_nonneg (zpow_pos hz v.1).le (zpow_pos hz v.2).le))]

private lemma shifted_row {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (a b c i : ℤ) :
    HasSum (fun j : ℤ => shiftedLocalTriple z a b c (i,j))
      (if i=b-c then z^(-c)*coefficient z (a+b-c)*(1-z)⁻¹^2 else 0) := by
  have h := ((Equiv.addRight b).hasSum_iff.mpr (localDilation_hasSum hz hz1 (i+c-b))).mul_left
    (coefficient z (i+a)*z^(i-b))
  have hf (j : ℤ) : coefficient z (i+a)*z^(i-b)*localDilation z (i+c-b) (j+b) =
      shiftedLocalTriple z a b c (i,j) := by
    unfold localDilation shiftedLocalTriple
    rw [show j+b+(i+c-b)=i+j+c by omega]
    rw [← mul_assoc,← mul_assoc]
    rw [zpow_sub₀ hz.ne',zpow_add₀ hz.ne',zpow_add₀ hz.ne']
    field_simp
  have h' := h.congr_fun (fun j => (hf j).symm)
  convert h' using 1 <;> try rfl
  by_cases hi : i=b-c
  · subst i
    simp only [sub_add_cancel,sub_self,if_pos,show b-c-b = -c by omega,
      show b-c+a=a+b-c by omega]
    ring
  · rw [if_neg hi,if_neg (show i+c-b ≠ 0 by omega),mul_zero]

theorem shiftedLocalTriple_hasSum {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (a b c : ℤ) :
    HasSum (shiftedLocalTriple z a b c) (z^(-c)*coefficient z (a+b-c)*(1-z)⁻¹^2) := by
  have hs := shiftedLocalTriple_summable hz hz1 a b c
  convert hs.hasSum using 1
  rw [hs.tsum_prod]
  simp_rw [(shifted_row hz hz1 a b c _).tsum_eq]
  simp

/-- Exact support of the complete signed shifted trace. -/
theorem shiftedLocalTriple_tsum_eq_zero_iff {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (a b c : ℤ) : (∑' v, shiftedLocalTriple z a b c v)=0 ↔ a+b-c < -1 := by
  rw [(shiftedLocalTriple_hasSum hz hz1 a b c).tsum_eq]
  have hc (i : ℤ) : coefficient z i=0 ↔ i < -1 := by
    by_cases hi : i = -1
    · subst i
      simp [coefficient,hz.ne',ne_of_gt (sub_pos.mpr hz1)]
    · by_cases h0 : 0 ≤ i
      · simp [coefficient,hi,h0,show ¬i < -1 by omega]
      · simp [coefficient,hi,h0,show i < -1 by omega]
  simp only [mul_eq_zero,zpow_ne_zero _ hz.ne',false_or,
    pow_eq_zero_iff (by omega : 2 ≠ 0),inv_eq_zero,
    ne_of_gt (sub_pos.mpr hz1),or_false,hc]

/-- A first-coordinate distinguished-prime shift has a nonzero positive trace. -/
theorem firstTaggedLocalTriple_hasSum {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasSum (fun v => z*shiftedLocalTriple z 1 0 0 v) (z/(1-z)^2) := by
  convert (shiftedLocalTriple_hasSum hz hz1 1 0 0).mul_left z using 1 <;> try rfl
  simp [coefficient,div_eq_mul_inv,inv_pow]

/-- A third-coordinate distinguished-prime shift has a nonzero negative trace. -/
theorem thirdTaggedLocalTriple_hasSum {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasSum (fun v => z*shiftedLocalTriple z 0 0 1 v) (-z/(1-z)^3) := by
  convert (shiftedLocalTriple_hasSum hz hz1 0 0 1).mul_left z using 1 <;> try rfl
  simp [coefficient]
  field_simp

/-- The critical reciprocal of every actual prime satisfies the entire trace law. -/
theorem primeShiftedLocalTriple_hasSum (p : Nat.Primes) (a b c : ℤ) :
    HasSum (shiftedLocalTriple (1/(p : ℝ)) a b c)
      ((1/(p : ℝ))^(-c)*coefficient (1/(p : ℝ)) (a+b-c)*(1-1/(p : ℝ))⁻¹^2) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  apply shiftedLocalTriple_hasSum (by positivity)
  simpa using one_div_lt_one_div_of_lt (show (0 : ℝ)<1 by positivity) hp

/-- Full finite-prime valuation lattice, with arbitrary shifts in all three slots. -/
theorem finitePrimeShiftedCubic_hasSum (P : Finset Nat.Primes) (a b c : Nat.Primes → ℤ) :
    HasSum (fun v : P → ℤ × ℤ => ∏ p : P,
      shiftedLocalTriple (1/((p : Nat.Primes) : ℝ)) (a p) (b p) (c p) (v p))
      (∏ p : P, (1/((p : Nat.Primes) : ℝ))^(-c p)*
        coefficient (1/((p : Nat.Primes) : ℝ)) (a p+b p-c p)*
          (1-1/((p : Nat.Primes) : ℝ))⁻¹^2) :=
  finite_product_hasSum P _ _ (fun p => primeShiftedLocalTriple_hasSum p (a p) (b p) (c p))

end RHTower.BAGTrace
