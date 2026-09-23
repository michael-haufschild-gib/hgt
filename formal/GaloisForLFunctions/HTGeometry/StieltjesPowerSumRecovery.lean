import Mathlib
import GaloisForLFunctions.HTGeometry.StieltjesCorankTrdeg
import GaloisForLFunctions.HTGeometry.TranscendenceDegreeOneVariable

/-!
# Recovering the even power sums from the Laurent coefficients

`f1-inversion-single-prime-stieltjes-collapse`, §2′.

The exponential generating function `g(y) = y/(1 − e^{−y}) = ∑ₖ B⁺ₖ yᵏ/k!` satisfies the algebraic
differential relation

```text
y · g'(y) = g(y) · (1 + y − g(y)),
```

obtained from `g·(e^y − 1) = y e^y` by differentiating, multiplying by `y`, and cancelling the
non-zero-divisor `e^y − 1`.  Rescaling and multiplying over a finite multiplier system therefore
gives, for the Laurent block `h = ∏ᵢ g(Lᵢ y)`,

```text
y · h'(y) = h(y) · ∑ᵢ (1 + Lᵢ y − g(Lᵢ y)),
```

whose right-hand factor has `k`-th coefficient `−B⁺ₖ pₖ / k!` for `k ≥ 2`, with `pₖ` the `k`-th
power sum of the multiplier logarithms.  Reading the identity coefficientwise expresses every such
coefficient as a rational polynomial in the block coefficients; since `B_{2m} ≠ 0`, every *even*
power sum is recovered.
-/

open PowerSeries

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The differential relation of the Bernoulli generating function -/

/-- **The Bernoulli generating function satisfies `y g' = g (1 + y − g)`.** -/
theorem bernoulliSeries_deriv_id (A : Type*) [CommRing A] [IsDomain A] [Algebra ℚ A] :
    X * (d⁄dX A) (bernoulli'PowerSeries A)
      = bernoulli'PowerSeries A * (1 + X - bernoulli'PowerSeries A) := by
  set g : PowerSeries A := bernoulli'PowerSeries A with hg
  have hkey : g * (exp A - 1) = X * exp A := bernoulli'PowerSeries_mul_exp_sub_one A
  have hDexp : (d⁄dX A) (exp A) = exp A := derivative_exp A
  have hne : exp A - 1 ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.coeff 1) h
    simp [PowerSeries.coeff_exp, PowerSeries.coeff_one] at hc
  have hdiff : (d⁄dX A) g * (exp A - 1) + g * exp A = exp A + X * exp A := by
    have h := congrArg (d⁄dX A) hkey
    rw [Derivation.leibniz, Derivation.leibniz] at h
    simp only [map_sub, hDexp, derivative_X, Derivation.map_one_eq_zero, sub_zero,
      smul_eq_mul] at h
    linear_combination h
  have hmul : X * ((d⁄dX A) g * (exp A - 1)) + X * (g * exp A)
      = X * exp A + X * (X * exp A) := by
    linear_combination X * hdiff
  have hsub : (exp A - 1) * (X * (d⁄dX A) g + g * g - g - X * g) = 0 := by
    have e1 : X * (g * exp A) = g * (X * exp A) := by ring
    rw [e1, ← hkey] at hmul
    linear_combination hmul
  have hzero : X * (d⁄dX A) g + g * g - g - X * g = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd h hne
    · exact h
  linear_combination hzero

/-! ## Rescaling and products -/

theorem X_mul_deriv_rescale {A : Type*} [CommRing A] (a : A) (f : PowerSeries A) :
    X * (d⁄dX A) (rescale a f) = rescale a (X * (d⁄dX A) f) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, coeff_derivative, PowerSeries.coeff_rescale,
        PowerSeries.coeff_rescale, PowerSeries.coeff_succ_X_mul, coeff_derivative]
      ring

/-- The rescaled Bernoulli generating function satisfies the rescaled relation. -/
theorem rescale_bernoulliSeries_deriv_id {A : Type*} [CommRing A] [IsDomain A] [Algebra ℚ A]
    (a : A) :
    X * (d⁄dX A) (rescale a (bernoulli'PowerSeries A))
      = rescale a (bernoulli'PowerSeries A)
        * (1 + PowerSeries.C a * X - rescale a (bernoulli'PowerSeries A)) := by
  rw [X_mul_deriv_rescale, bernoulliSeries_deriv_id]
  rw [map_mul, map_sub, map_add, map_one, PowerSeries.rescale_X]

/-- **Product form of a logarithmic-derivative relation.**  If every factor satisfies
`X·f' = f·u`, then the product satisfies `X·(∏f)' = (∏f)·(∑u)`. -/
theorem X_mul_deriv_prod {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f u : ι → PowerSeries A)
    (h : ∀ i ∈ s, X * (d⁄dX A) (f i) = f i * u i) :
    X * (d⁄dX A) (∏ i ∈ s, f i) = (∏ i ∈ s, f i) * ∑ i ∈ s, u i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hmem : ∀ i ∈ s, X * (d⁄dX A) (f i) = f i * u i :=
        fun i hi => h i (Finset.mem_cons_of_mem hi)
      have hprev := ih hmem
      have hA := h a (Finset.mem_cons_self a s)
      rw [Finset.prod_cons, Finset.sum_cons, Derivation.leibniz]
      have hexp : X * (f a • (d⁄dX A) (∏ i ∈ s, f i) + (∏ i ∈ s, f i) • (d⁄dX A) (f a))
          = f a * (X * (d⁄dX A) (∏ i ∈ s, f i))
            + (∏ i ∈ s, f i) * (X * (d⁄dX A) (f a)) := by
        simp only [smul_eq_mul]
        ring
      rw [hexp, hprev, hA]
      ring

/-! ## The Laurent block and its logarithmic-derivative factor -/

/-- The Bernoulli generating function over the multiplier-log polynomial ring. -/
def blockGen (r : ℕ) : PowerSeries (MvPolynomial (Fin r) ℚ) :=
  bernoulli'PowerSeries (MvPolynomial (Fin r) ℚ)

theorem coeff_blockGen (r m : ℕ) :
    PowerSeries.coeff m (blockGen r)
      = MvPolynomial.C (bernoulli' m / (m.factorial : ℚ)) := by
  rw [blockGen, bernoulli'PowerSeries, PowerSeries.coeff_mk]
  rfl

theorem scaledFactor_eq_rescale (r : ℕ) (i : Fin r) :
    scaledFactor r (fun k => bernoulli' k / (k.factorial : ℚ)) i
      = rescale (MvPolynomial.X i) (blockGen r) := by
  refine PowerSeries.ext fun m => ?_
  rw [scaledFactor, PowerSeries.coeff_mk, PowerSeries.coeff_rescale, coeff_blockGen]
  exact mul_comm _ _

theorem beurlingBlock_eq_prod (r : ℕ) :
    beurlingBlock r = ∏ i : Fin r, rescale (MvPolynomial.X i) (blockGen r) := by
  rw [beurlingBlock, symmetricBlock]
  exact Finset.prod_congr rfl fun i _ => scaledFactor_eq_rescale r i

/-- The logarithmic-derivative factor of the Laurent block. -/
def blockQ (r : ℕ) : PowerSeries (MvPolynomial (Fin r) ℚ) :=
  ∑ i : Fin r, (1 + PowerSeries.C (MvPolynomial.X i) * X
    - rescale (MvPolynomial.X i) (blockGen r))

/-- **The Laurent block satisfies `X·h′ = h·Q`.** -/
theorem X_mul_deriv_beurlingBlock (r : ℕ) :
    X * (d⁄dX (MvPolynomial (Fin r) ℚ)) (beurlingBlock r) = beurlingBlock r * blockQ r := by
  rw [beurlingBlock_eq_prod, blockQ]
  refine X_mul_deriv_prod Finset.univ _ _ fun i _ => ?_
  exact rescale_bernoulliSeries_deriv_id (MvPolynomial.X i)

/-! ## The coefficients of the logarithmic-derivative factor -/

theorem coeff_blockQ (r m : ℕ) :
    PowerSeries.coeff m (blockQ r)
      = ∑ i : Fin r, ((if m = 0 then (1 : MvPolynomial (Fin r) ℚ) else 0)
          + (if m = 1 then MvPolynomial.X i else 0)
          - (MvPolynomial.X i) ^ m * MvPolynomial.C (bernoulli' m / (m.factorial : ℚ))) := by
  rw [blockQ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, map_add, PowerSeries.coeff_rescale, coeff_blockGen]
  congr 1
  congr 1
  · rw [PowerSeries.coeff_one]
  · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    split_ifs with h
    · rw [mul_one]
    · rw [mul_zero]

theorem coeff_blockQ_zero (r : ℕ) : PowerSeries.coeff 0 (blockQ r) = 0 := by
  rw [coeff_blockQ]
  refine Finset.sum_eq_zero fun i _ => ?_
  norm_num

theorem coeff_blockQ_of_two_le {r m : ℕ} (hm : 2 ≤ m) :
    PowerSeries.coeff m (blockQ r)
      = -(MvPolynomial.C (bernoulli' m / (m.factorial : ℚ))
          * ∑ i : Fin r, (MvPolynomial.X i) ^ m) := by
  rw [coeff_blockQ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_neg (by omega), if_neg (by omega)]
  ring


/-! ## The coefficient recursion -/


theorem coeff_zero_beurlingBlock (r : ℕ) :
    PowerSeries.coeff 0 (beurlingBlock r) = 1 := by
  rw [beurlingBlock_eq_prod, PowerSeries.coeff_zero_eq_constantCoeff, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale, coeff_blockGen]
  norm_num

theorem beurlingBlock_recursion (r k : ℕ) :
    PowerSeries.coeff (k+1) (beurlingBlock r) * ((k : MvPolynomial (Fin r) ℚ) + 1)
      = ∑ a ∈ Finset.range (k+1),
          PowerSeries.coeff a (beurlingBlock r) * PowerSeries.coeff (k+1-a) (blockQ r) := by
  have hid := X_mul_deriv_beurlingBlock r
  have hl := congrArg (PowerSeries.coeff (k+1)) hid
  rw [PowerSeries.coeff_succ_X_mul, coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] at hl
  simp only [Nat.sub_self, coeff_blockQ_zero, mul_zero, add_zero] at hl
  exact hl

/-- Bernoulli numbers of even positive index are nonzero. -/
theorem bernoulli_two_mul_ne_zero {k : ℕ} (hk : k ≠ 0) : bernoulli (2 * k) ≠ 0 := by
  intro h
  have hs := hasSum_zeta_nat hk
  have hval : ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) *
      (bernoulli (2 * k) : ℝ) / (2 * k).factorial) = 0 := by
    rw [h]
    norm_num
  rw [hval] at hs
  have hone : (1 : ℝ) / (1 : ℕ) ^ (2 * k) ≤ 0 := by
    refine le_hasSum hs 1 fun j _ => ?_
    positivity
  norm_num at hone


/-! ## Values at a multiplier-log family -/

/-- The value of the `m`-th logarithmic-derivative coefficient at a multiplier-log family. -/
def qVal {r : ℕ} (L : Fin r → ℝ) (m : ℕ) : ℝ :=
  MvPolynomial.aeval L (PowerSeries.coeff m (blockQ r))

theorem blockCoeffVal_zero {r : ℕ} (L : Fin r → ℝ) : blockCoeffVal L 0 = 1 := by
  rw [blockCoeffVal, coeff_zero_beurlingBlock, map_one]

theorem qVal_zero {r : ℕ} (L : Fin r → ℝ) : qVal L 0 = 0 := by
  rw [qVal, coeff_blockQ_zero, map_zero]

theorem blockCoeffVal_recursion {r : ℕ} (L : Fin r → ℝ) (k : ℕ) :
    blockCoeffVal L (k+1) * ((k : ℝ) + 1)
      = ∑ a ∈ Finset.range (k+1), blockCoeffVal L a * qVal L (k+1-a) := by
  have h := congrArg (MvPolynomial.aeval L) (beurlingBlock_recursion r k)
  simpa [blockCoeffVal, qVal] using h

theorem prod_mem_stieltjesField {r : ℕ} (L : Fin r → ℝ) :
    (∏ i, L i) ∈ stieltjesField L := by
  have h0 : stieltjesVal L 0 = (∏ i, L i)⁻¹ := by
    rw [stieltjesVal, blockCoeffVal_zero, one_div]
  have hmem : stieltjesVal L 0 ∈ stieltjesField L :=
    IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩
  rw [h0] at hmem
  simpa using (stieltjesField L).inv_mem hmem

theorem blockCoeffVal_mem_stieltjesField {r : ℕ} {L : Fin r → ℝ} (hL : (∏ i, L i) ≠ 0) (k : ℕ) :
    blockCoeffVal L k ∈ stieltjesField L := by
  have hval : blockCoeffVal L k = stieltjesVal L k * ∏ i, L i := by
    rw [stieltjesVal, div_mul_cancel₀ _ hL]
  rw [hval]
  exact (stieltjesField L).mul_mem (IntermediateField.subset_adjoin ℚ _ ⟨k, rfl⟩)
    (prod_mem_stieltjesField L)

theorem qVal_mem_stieltjesField {r : ℕ} {L : Fin r → ℝ} (hL : (∏ i, L i) ≠ 0) (m : ℕ) :
    qVal L m ∈ stieltjesField L := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => rw [qVal_zero]; exact zero_mem _
    | (k+1), ih =>
      have hrec := blockCoeffVal_recursion L k
      rw [Finset.sum_range_succ'] at hrec
      simp only [Nat.sub_zero, blockCoeffVal_zero, one_mul] at hrec
      have hq : qVal L (k+1)
          = blockCoeffVal L (k+1) * ((k : ℝ) + 1)
            - ∑ a ∈ Finset.range k, blockCoeffVal L (a+1) * qVal L (k + 1 - (a+1)) := by
        linarith [hrec]
      rw [hq]
      refine (stieltjesField L).sub_mem ?_ ?_
      · refine (stieltjesField L).mul_mem (blockCoeffVal_mem_stieltjesField hL _) ?_
        have : ((k : ℝ) + 1) = ((((k : ℚ) + 1 : ℚ)) : ℝ) := by push_cast; ring
        rw [this]
        exact (stieltjesField L).algebraMap_mem _
      · refine Subalgebra.sum_mem _ fun a ha => ?_
        refine (stieltjesField L).mul_mem (blockCoeffVal_mem_stieltjesField hL _) ?_
        exact ih (k + 1 - (a+1)) (by omega)



/-! ## The even power sums are recovered -/

theorem qVal_of_two_le {r : ℕ} (L : Fin r → ℝ) {m : ℕ} (hm : 2 ≤ m) :
    qVal L m
      = -(((bernoulli' m / (m.factorial : ℚ) : ℚ) : ℝ) * ∑ i, (L i) ^ m) := by
  rw [qVal, coeff_blockQ_of_two_le hm]
  simp [MvPolynomial.aeval_X]

/-- **Every even power sum of the multiplier logs lies in the Laurent-coefficient field.** -/
theorem sum_pow_even_mem_stieltjesField {r : ℕ} {L : Fin r → ℝ} (hL : (∏ i, L i) ≠ 0)
    {m : ℕ} (hm : m ≠ 0) :
    (∑ i, (L i) ^ (2 * m)) ∈ stieltjesField L := by
  have h2 : 2 ≤ 2 * m := by omega
  have hne1 : 2 * m ≠ 1 := by omega
  have hbne : bernoulli' (2 * m) ≠ 0 := by
    rw [← bernoulli_eq_bernoulli'_of_ne_one hne1]
    exact bernoulli_two_mul_ne_zero hm
  set c : ℚ := bernoulli' (2 * m) / ((2 * m).factorial : ℚ) with hc
  have hcne : (c : ℝ) ≠ 0 := by
    rw [hc]
    have hfac : ((2 * m).factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have : (bernoulli' (2 * m) / ((2 * m).factorial : ℚ)) ≠ 0 := div_ne_zero hbne hfac
    exact_mod_cast this
  have hq := qVal_of_two_le L h2
  have hmem := qVal_mem_stieltjesField hL (2 * m)
  have hsum : (∑ i, (L i) ^ (2 * m)) = -(qVal L (2 * m)) / (c : ℝ) := by
    rw [hq, hc]
    field_simp
  rw [hsum]
  refine (stieltjesField L).div_mem ((stieltjesField L).neg_mem hmem) ?_
  exact (stieltjesField L).algebraMap_mem c


/-! ## Newton's identities on the squares -/


/-- The negated squares of the multiplier logs. -/
def negSq {r : ℕ} (L : Fin r → ℝ) (i : Fin r) : ℝ := -((L i) ^ (2 : ℕ))

theorem aeval_psum_negSq {r : ℕ} (L : Fin r → ℝ) (k : ℕ) :
    MvPolynomial.aeval (negSq L) (MvPolynomial.psum (Fin r) ℚ k)
      = (-1) ^ k * ∑ i, (L i) ^ (2 * k) := by
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, negSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow, pow_mul]

theorem ratPow_mem_stieltjesField {r : ℕ} (L : Fin r → ℝ) (k : ℕ) :
    ((-1 : ℝ)) ^ k ∈ stieltjesField L := by
  have h : ((-1 : ℝ)) ^ k = (((-1 : ℚ) ^ k : ℚ) : ℝ) := by push_cast; ring
  rw [h]
  exact (stieltjesField L).algebraMap_mem _

theorem aeval_psum_negSq_mem {r : ℕ} {L : Fin r → ℝ} (hL : (∏ i, L i) ≠ 0) {k : ℕ} (hk : k ≠ 0) :
    MvPolynomial.aeval (negSq L) (MvPolynomial.psum (Fin r) ℚ k) ∈ stieltjesField L := by
  rw [aeval_psum_negSq]
  exact (stieltjesField L).mul_mem (ratPow_mem_stieltjesField L k)
    (sum_pow_even_mem_stieltjesField hL hk)

/-- **Newton's identities recover the elementary symmetric functions of the negated squares.** -/
theorem aeval_esymm_negSq_mem {r : ℕ} {L : Fin r → ℝ} (hL : (∏ i, L i) ≠ 0) (k : ℕ) :
    MvPolynomial.aeval (negSq L) (MvPolynomial.esymm (Fin r) ℚ k) ∈ stieltjesField L := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [MvPolynomial.esymm_zero, map_one]
      exact one_mem _
    · have h := congrArg (MvPolynomial.aeval (negSq L))
        (MvPolynomial.mul_esymm_eq_sum (Fin r) ℚ k)
      rw [map_mul, map_mul, map_sum] at h
      have hmem : (MvPolynomial.aeval (negSq L) ((k : MvPolynomial (Fin r) ℚ)))
          * MvPolynomial.aeval (negSq L) (MvPolynomial.esymm (Fin r) ℚ k)
          ∈ stieltjesField L := by
        rw [h]
        refine (stieltjesField L).mul_mem ?_ ?_
        · rw [map_pow, map_neg, map_one]
          exact ratPow_mem_stieltjesField L (k + 1)
        · refine Subalgebra.sum_mem _ fun a ha => ?_
          rw [Finset.mem_filter] at ha
          have hsum : a.1 + a.2 = k := List.Nat.mem_antidiagonal.mp ha.1
          rw [map_mul, map_mul, map_pow, map_neg, map_one]
          refine (stieltjesField L).mul_mem
            ((stieltjesField L).mul_mem (ratPow_mem_stieltjesField L a.1) (ih a.1 ha.2)) ?_
          exact aeval_psum_negSq_mem hL (by omega)
      have hcast : (MvPolynomial.aeval (negSq L) ((k : MvPolynomial (Fin r) ℚ))) = (k : ℝ) := by
        rw [map_natCast]
      rw [hcast] at hmem
      have hkne : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hkmem : ((k : ℝ)) ∈ stieltjesField L := by
        have : ((k : ℝ)) = (((k : ℚ) : ℚ) : ℝ) := by push_cast; ring
        rw [this]
        exact (stieltjesField L).algebraMap_mem _
      have hdiv := (stieltjesField L).div_mem hmem hkmem
      have heq : ((k : ℝ) * MvPolynomial.aeval (negSq L) (MvPolynomial.esymm (Fin r) ℚ k))
          / (k : ℝ) = MvPolynomial.aeval (negSq L) (MvPolynomial.esymm (Fin r) ℚ k) := by
        field_simp
      rwa [heq] at hdiv


/-! ## Vieta and the transcendence-degree identity -/

/-- The Vieta expansion of the monic polynomial with the negated squares as roots. -/
theorem vieta_negSq {r : ℕ} (L : Fin r → ℝ) (x : ℝ) :
    ∑ j ∈ Finset.range (r + 1),
        MvPolynomial.aeval (negSq L) (MvPolynomial.esymm (Fin r) ℚ j) * x ^ (r - j)
      = ∏ l : Fin r, (x + negSq L l) := by
  set s : Multiset ℝ := Multiset.map (negSq L) Finset.univ.val with hs
  have hcard : Multiset.card s = r := by
    rw [hs, Multiset.card_map]
    simp
  have hvieta := Multiset.prod_X_add_C_eq_sum_esymm s
  have hev := congrArg (Polynomial.eval x) hvieta
  rw [hcard, Polynomial.eval_finsetSum] at hev
  have hlhs : Polynomial.eval x (Multiset.map (fun c => Polynomial.X + Polynomial.C c) s).prod
      = ∏ l : Fin r, (x + negSq L l) := by
    rw [Polynomial.eval_multiset_prod, Multiset.map_map, hs, Multiset.map_map]
    rw [Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp
  rw [hlhs] at hev
  have hterm : ∀ j : ℕ, Polynomial.eval x (Polynomial.C (s.esymm j) * Polynomial.X ^ (r - j))
      = MvPolynomial.aeval (negSq L) (MvPolynomial.esymm (Fin r) ℚ j) * x ^ (r - j) := by
    intro j
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      MvPolynomial.aeval_esymm_eq_multiset_esymm]
  calc ∑ j ∈ Finset.range (r + 1),
        MvPolynomial.aeval (negSq L) (MvPolynomial.esymm (Fin r) ℚ j) * x ^ (r - j)
      = ∑ j ∈ Finset.range (r + 1),
          Polynomial.eval x (Polynomial.C (s.esymm j) * Polynomial.X ^ (r - j)) :=
        Finset.sum_congr rfl fun j _ => (hterm j).symm
    _ = ∏ l : Fin r, (x + negSq L l) := hev.symm


/-- **Each squared multiplier log is algebraic over the Laurent-coefficient field.** -/
theorem isAlgebraic_sq_over_stieltjesField {r : ℕ} {L : Fin r → ℝ} (hL : (∏ i, L i) ≠ 0)
    (i : Fin r) : IsAlgebraic ↥(stieltjesField L) ((L i) ^ (2 : ℕ)) := by
  have hr : 1 ≤ r := i.pos
  set E : ℕ → ℝ := fun j => MvPolynomial.aeval (negSq L) (MvPolynomial.esymm (Fin r) ℚ j) with hEdef
  have hEmem : ∀ j, E j ∈ stieltjesField L := fun j => aeval_esymm_negSq_mem hL j
  have hE0 : E 0 = 1 := by
    rw [hEdef]
    simp [MvPolynomial.esymm_zero]
  set q : Polynomial ↥(stieltjesField L) :=
    ∑ j ∈ Finset.range (r + 1),
      Polynomial.C (⟨E j, hEmem j⟩ : ↥(stieltjesField L)) * Polynomial.X ^ (r - j) with hq
  refine ⟨q, ?_, ?_⟩
  · intro h0
    have hcoeff : Polynomial.coeff q r = (⟨E 0, hEmem 0⟩ : ↥(stieltjesField L)) := by
      rw [hq, Polynomial.finsetSum_coeff]
      have hsingle : ∑ b ∈ Finset.range (r + 1),
          (Polynomial.C (⟨E b, hEmem b⟩ : ↥(stieltjesField L))
            * Polynomial.X ^ (r - b)).coeff r
          = (Polynomial.C (⟨E 0, hEmem 0⟩ : ↥(stieltjesField L))
            * Polynomial.X ^ (r - 0)).coeff r := by
        refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos r)) ?_
        intro j hj hj0
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        have hjr : j ≤ r := by
          have := Finset.mem_range.mp hj
          omega
        rw [if_neg (by omega), mul_zero]
      rw [hsingle, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Nat.sub_zero,
        if_pos rfl, mul_one]
    rw [h0] at hcoeff
    have hzero : (0 : ℝ) = 1 := by
      have hval := congrArg Subtype.val hcoeff.symm
      simp only [hE0] at hval
      simpa using hval.symm
    exact absurd hzero (by norm_num)
  · have hmapped : Polynomial.aeval ((L i) ^ (2 : ℕ)) q
        = ∑ j ∈ Finset.range (r + 1), E j * ((L i) ^ (2 : ℕ)) ^ (r - j) := by
      rw [hq, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rfl
    rw [hmapped, hEdef, vieta_negSq]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [negSq]
    ring

/-- **Each multiplier log is algebraic over the Laurent-coefficient field.** -/
theorem isAlgebraic_log_over_stieltjesField {r : ℕ} {L : Fin r → ℝ} (hL : (∏ i, L i) ≠ 0)
    (i : Fin r) : IsAlgebraic ↥(stieltjesField L) (L i) := by
  obtain ⟨p, hp0, hp⟩ := isAlgebraic_sq_over_stieltjesField hL i
  refine ⟨p.comp (Polynomial.X ^ (2 : ℕ)), ?_, ?_⟩
  · intro h
    rcases Polynomial.comp_eq_zero_iff.mp h with h1 | ⟨_, h2⟩
    · exact hp0 h1
    · have hc := congrArg (fun t => Polynomial.coeff t 2) h2
      simp at hc
  · rw [Polynomial.aeval_comp]
    simpa using hp


/-- **§2′.**  The Laurent-coefficient field and the multiplier-log field have the same
transcendence degree over `ℚ`. -/
theorem trdeg_stieltjesField_eq_logField {r : ℕ} {L : Fin r → ℝ} (hL : (∏ i, L i) ≠ 0) :
    Algebra.trdeg ℚ ↥(stieltjesField L) = Algebra.trdeg ℚ ↥(logField L) := by
  have hle : stieltjesField L ≤ logField L := stieltjesField_le_logField L
  letI : Algebra ↥(stieltjesField L) ↥(logField L) :=
    (IntermediateField.inclusion hle).toAlgebra
  haveI : IsScalarTower ℚ ↥(stieltjesField L) ↥(logField L) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥(stieltjesField L) ↥(logField L) ℝ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic ↥(stieltjesField L) ↥(logField L) := by
    constructor
    intro x
    have hsub : logField L
        ≤ (algebraicClosure ↥(stieltjesField L) ℝ).restrictScalars ℚ := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro y ⟨i, rfl⟩
      exact mem_algebraicClosure_iff.mpr (isAlgebraic_log_over_stieltjesField hL i)
    have hx : IsAlgebraic ↥(stieltjesField L) ((x : ℝ)) :=
      mem_algebraicClosure_iff.mp (hsub x.2)
    exact (isAlgebraic_algebraMap_iff
      (R := ↥(stieltjesField L)) (S := ↥(logField L)) (A := ℝ)
      (Subtype.val_injective)).mp hx
  exact (trdeg_eq_of_isAlgebraic (A := ℚ) (K := ↥(stieltjesField L))
    (L := ↥(logField L))).symm

end GaloisForLFunctions.HTGeometry
