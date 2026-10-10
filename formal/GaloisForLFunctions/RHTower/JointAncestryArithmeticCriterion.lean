import GaloisForLFunctions.RHTower.JointAncestryKroneckerLineCriterion

/-!
# The arithmetic (zero-free) form of the vertical criterion

The lag function has the prime side (genus-kernel explicit formula): `Φ(0) = 2 + γ − log 4π` and,
for `L ≠ 0`, with `X = e^{|L|}`,

`Φ(L) = X^{-1/2} [(X − ψ(X)) + X (Σ_{n ≤ X} Λ(n)/n − |L| + γ) − log 2π + Σ_{k ≥ 1} X^{-2k}/(2k(2k+1))]`.

The value of the `1`-dressed aggregate at the character `Σ_p (x_p − y_p) e_p` is
`∏_p p^{-|x_p − y_p|} · Φ(Σ_p (y_p − x_p) log p)`.  Combining the vertical criterion with the Fejér limit:

**RH ⟹** for every finite prime set `P`, every box size `K` and every real `τ`,

`0 ≤ Re Σ_{x, y ∈ [0,K]^P} ∏_{p ∈ P} p^{-|x_p − y_p| − iτ(x_p − y_p)} · Φ(Σ_p (y_p − x_p) log p)`,

and **conversely** nonnegativity of all these finite sums forces RH unless the off-line zeros form a
chain with no farthest zero.  The sums involve only `ψ`, the partial sums of `Λ(n)/n`, `γ`, `log 2π`
and the trivial-zero series: the criterion contains no zeros.
-/

open Complex Filter Topology
open scoped ComplexConjugate BigOperators
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-- The prime side of the lag function. -/
def jasPrimeLag (L : ℝ) : ℂ :=
  if L = 0 then poleSharpConstant else
    Real.exp (-|L| / 2) *
      (((Real.exp |L| - Chebyshev.psi (Real.exp |L|) : ℝ) : ℂ) +
        Real.exp |L| * (((∑ n ∈ Finset.Icc 1 ⌊Real.exp |L|⌋₊, vonMangoldt n / (n : ℝ) : ℝ) : ℂ) -
          |L| + Real.eulerMascheroniConstant) -
        Real.log (2 * Real.pi) + trivialZeroSeries (Real.exp |L|))

/-- The lag function equals its prime side for every real lag. -/
theorem weilLagFunction_eq_jasPrimeLag (L : ℝ) : weilLagFunction L = jasPrimeLag L := by
  unfold jasPrimeLag
  split_ifs with h
  · rw [h, weilLagFunction_zero]
  · have hL : 0 < |L| := abs_pos.mpr h
    rw [← weilLagFunction_eq_prime_side hL]
    rcases le_or_gt 0 L with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, weilLagFunction_neg]

/-! ## The aggregate on a Fejér box -/

theorem jasLogPos_jasVecChar_sub (P : Finset Nat.Primes) (x y : ↥P → ℕ) :
    jasLogPos (jasVecChar P x - jasVecChar P y) =
      ∑ i : ↥P, (((x i : ℤ) - y i).toNat : ℝ) * Real.log (i : Nat.Primes) := by
  rw [jasLogPos, Finsupp.sum_of_support_subset _ (support_jasVecChar_sub_subset P x y) _
    (fun i _ => by simp), ← Finset.sum_coe_sort P]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sub_apply, jasVecChar_apply, jasVecChar_apply]

theorem jasLogNeg_jasVecChar_sub (P : Finset Nat.Primes) (x y : ↥P → ℕ) :
    jasLogNeg (jasVecChar P x - jasVecChar P y) =
      ∑ i : ↥P, ((-((x i : ℤ) - y i)).toNat : ℝ) * Real.log (i : Nat.Primes) := by
  rw [jasLogNeg, Finsupp.sum_of_support_subset _ (support_jasVecChar_sub_subset P x y) _
    (fun i _ => by simp), ← Finset.sum_coe_sort P]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sub_apply, jasVecChar_apply, jasVecChar_apply]

theorem toNat_neg_sub_toNat (k : ℤ) : (((-k).toNat : ℤ) : ℝ) - ((k.toNat : ℤ) : ℝ) = ((-k : ℤ) : ℝ) := by
  have : ((-k).toNat : ℤ) - (k.toNat : ℤ) = -k := by omega
  exact_mod_cast this

theorem toNat_add_toNat_neg (k : ℤ) : ((k.toNat : ℕ) : ℝ) + (((-k).toNat : ℕ) : ℝ) = (k.natAbs : ℝ) := by
  have : (k.toNat : ℤ) + ((-k).toNat : ℤ) = (k.natAbs : ℤ) := by omega
  exact_mod_cast this

/-- The lag of the character `x − y`: `Σ_p (y_p − x_p) log p`. -/
theorem jasLogNeg_sub_jasLogPos_jasVecChar_sub (P : Finset Nat.Primes) (x y : ↥P → ℕ) :
    jasLogNeg (jasVecChar P x - jasVecChar P y) - jasLogPos (jasVecChar P x - jasVecChar P y) =
      ∑ i : ↥P, ((y i : ℝ) - x i) * Real.log (i : Nat.Primes) := by
  rw [jasLogNeg_jasVecChar_sub, jasLogPos_jasVecChar_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_mul]
  congr 1
  have h := toNat_neg_sub_toNat ((x i : ℤ) - y i)
  push_cast at h ⊢
  linarith

/-- The size of the character `x − y`: `Σ_p |x_p − y_p| log p`. -/
theorem jasLogSize_jasVecChar_sub (P : Finset Nat.Primes) (x y : ↥P → ℕ) :
    jasLogSize (jasVecChar P x - jasVecChar P y) =
      ∑ i : ↥P, ((((x i : ℤ) - y i).natAbs : ℕ) : ℝ) * Real.log (i : Nat.Primes) := by
  rw [jasLogSize, jasLogPos_jasVecChar_sub, jasLogNeg_jasVecChar_sub, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← add_mul, toNat_add_toNat_neg]

/-- **The `1`-dressed aggregate on a Fejér box, in arithmetic form.** -/
theorem jasDressedLagAggregate_one_jasVecChar_sub (P : Finset Nat.Primes) (x y : ↥P → ℕ) :
    jasDressedLagAggregate 1 (jasVecChar P x - jasVecChar P y) =
      (∏ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-(((x i : ℤ) - y i).natAbs : ℝ)) : ℝ) *
        jasPrimeLag (∑ i : ↥P, ((y i : ℝ) - x i) * Real.log (i : Nat.Primes)) := by
  have hexp : Real.exp (-1 * ∑ i : ↥P, ((((x i : ℤ) - y i).natAbs : ℕ) : ℝ) *
      Real.log (i : Nat.Primes)) =
      ∏ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-(((x i : ℤ) - y i).natAbs : ℝ)) := by
    rw [neg_one_mul, ← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hp : (0 : ℝ) < (((i : Nat.Primes) : ℕ) : ℝ) := by
      exact_mod_cast (i : Nat.Primes).2.pos
    rw [Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [jasDressedLagAggregate, jasLogSize_jasVecChar_sub,
    jasLogNeg_sub_jasLogPos_jasVecChar_sub, weilLagFunction_eq_jasPrimeLag, hexp]

/-- The arithmetic Fejér form at the vertical point `(p^{-iτ})_p`. -/
def jasArithmeticForm (P : Finset Nat.Primes) (K : ℕ) (τ : ℝ) : ℂ :=
  ∑ x ∈ jasFejerBox P K, ∑ y ∈ jasFejerBox P K,
    jasFejerCoeff P (fun i => jasVerticalPoint τ i) x *
      conj (jasFejerCoeff P (fun i => jasVerticalPoint τ i) y) *
      ((∏ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-(((x i : ℤ) - y i).natAbs : ℝ)) : ℝ) *
        jasPrimeLag (∑ i : ↥P, ((y i : ℝ) - x i) * Real.log (i : Nat.Primes)))

theorem jasArithmeticForm_eq (P : Finset Nat.Primes) (K : ℕ) (τ : ℝ) :
    jasArithmeticForm P K τ = jasFejerForm (1 / 2 + 1 / 2) P (fun i => jasVerticalPoint τ i) K := by
  rw [jasArithmeticForm, jasFejerForm, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [jasDressedLagAggregate_one_jasVecChar_sub]

/-- **RH implies the arithmetic criterion.** -/
theorem re_jasArithmeticForm_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    (P : Finset Nat.Primes) (K : ℕ) (τ : ℝ) : 0 ≤ (jasArithmeticForm P K τ).re := by
  have hpsd := jasDressedPSD_of_riemannHypothesis hRH (σ := 1 / 2 + 1 / 2) (by norm_num)
  rw [jasArithmeticForm_eq]
  exact hpsd _ (jasFejerBox P K) _ (jasVecChar P) (jasVecChar_injective P).injOn

/-- **The arithmetic criterion forces RH up to a chain.**  If every arithmetic Fejér form is
nonnegative, then RH holds or the off-line zeros form a chain with no farthest zero. -/
theorem riemannHypothesis_or_chain_of_arithmetic
    (h : ∀ (P : Finset Nat.Primes) (K : ℕ) (τ : ℝ), 0 ≤ (jasArithmeticForm P K τ).re) :
    RiemannHypothesis ∨ ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
      ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2| := by
  refine riemannHypothesis_or_chain_of_vertical_one fun P τ => ?_
  exact re_tsum_prod_jasHoloLocal_nonneg_of_fejer (by norm_num) P _
    (fun i => norm_jasVerticalPoint τ i) fun K => by
      rw [← jasArithmeticForm_eq]
      exact h P K τ

end

end RHTower
