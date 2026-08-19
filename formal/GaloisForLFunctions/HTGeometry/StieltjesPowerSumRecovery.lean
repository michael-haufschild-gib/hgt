import Mathlib
import GaloisForLFunctions.HTGeometry.StieltjesCorankTrdeg

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

end GaloisForLFunctions.HTGeometry
