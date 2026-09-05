import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleSecondConvergence

/-!
# Coprime deletion-cylinder closure at a zeta zero

For coprime positive moduli `p,q`, the pointwise product of their deletion coefficients is the
alternating combination of the `p`, `q`, and `pq` deletion channels:

```text
a_p a_q = a_p + a_q - a_{pq}.
```

Consequently every positive-half-plane zeta zero closes the degree-two coprime cylinder path under
the same ordinary chronological cutoffs.  This strengthens the family of closed level-one tests;
it does not force a chronological second level to vanish.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace RHTower

/-- Coprime deletion coefficients multiply by inclusion--exclusion through the product modulus. -/
theorem blockDeletionCoefficient_mul_eq_add_sub_product_of_coprime
    {p q : ℕ} (hpq : Nat.Coprime p q) (n : ℕ) :
    blockDeletionCoefficient p n * blockDeletionCoefficient q n =
      blockDeletionCoefficient p n + blockDeletionCoefficient q n -
        blockDeletionCoefficient (p * q) n := by
  have hprod : p * q ∣ n ↔ p ∣ n ∧ q ∣ n := by
    constructor
    · intro h
      exact ⟨dvd_trans (dvd_mul_right p q) h,
        dvd_trans (dvd_mul_left q p) h⟩
    · rintro ⟨hp, hq⟩
      exact hpq.mul_dvd_of_dvd_of_dvd hp hq
  by_cases hp : p ∣ n
  all_goals by_cases hq : q ∣ n
  all_goals simp [blockDeletionCoefficient, hp, hq, hprod] <;> ring

/-- Weighted pointwise product of two actual-modulus deletion channels. -/
def coprimeEulerDeletionProductWeightedJump
    (p q : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  (blockDeletionCoefficient p (n + 1) : ℂ) *
    (blockDeletionCoefficient q (n + 1) : ℂ) *
      (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)

/-- Actual modulus and zero-indexed canonical deletion parameters agree. -/
theorem eulerDeletionWeightedJump_pred
    {p : ℕ} (hp : 0 < p) (s : ℂ) (n : ℕ) :
    eulerDeletionWeightedJump (p - 1) s n =
      (blockDeletionCoefficient p (n + 1) : ℂ) *
        (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  rw [eulerDeletionWeightedJump, eulerDeletionDirichletCoefficient]
  rw [Nat.sub_add_cancel hp]

/-- Degree-two coprime cylinder jump is an exact three-channel alternating sum. -/
theorem coprimeEulerDeletionProductWeightedJump_eq
    {p q : ℕ} (hpq : Nat.Coprime p q) (s : ℂ) (n : ℕ) :
    coprimeEulerDeletionProductWeightedJump p q s n =
      (blockDeletionCoefficient p (n + 1) : ℂ) *
          (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) +
        (blockDeletionCoefficient q (n + 1) : ℂ) *
          (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) -
        (blockDeletionCoefficient (p * q) (n + 1) : ℂ) *
          (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  rw [coprimeEulerDeletionProductWeightedJump]
  have hcoeff := blockDeletionCoefficient_mul_eq_add_sub_product_of_coprime hpq (n + 1)
  have hcoeffC :
      (blockDeletionCoefficient p (n + 1) : ℂ) *
          (blockDeletionCoefficient q (n + 1) : ℂ) =
        (blockDeletionCoefficient p (n + 1) : ℂ) +
          (blockDeletionCoefficient q (n + 1) : ℂ) -
          (blockDeletionCoefficient (p * q) (n + 1) : ℂ) := by
    exact_mod_cast hcoeff
  rw [hcoeffC]
  ring

/-- Exact finite degree-two cylinder decomposition, with one common chronological cutoff. -/
theorem coprimeEulerDeletionProduct_prefix_eq
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, coprimeEulerDeletionProductWeightedJump p q s n =
      (∑ n ∈ Finset.range N, eulerDeletionWeightedJump (p - 1) s n) +
        (∑ n ∈ Finset.range N, eulerDeletionWeightedJump (q - 1) s n) -
        ∑ n ∈ Finset.range N, eulerDeletionWeightedJump (p * q - 1) s n := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [coprimeEulerDeletionProductWeightedJump_eq hpq,
    eulerDeletionWeightedJump_pred hp, eulerDeletionWeightedJump_pred hq,
    eulerDeletionWeightedJump_pred (Nat.mul_pos hp hq)]

/-- Every positive-half-plane zeta zero closes every degree-two coprime deletion cylinder. -/
theorem tendsto_coprimeEulerDeletionProduct_prefix_of_zeta_zero
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    {rho : ℂ} (hrhoRe : 0 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    Tendsto
      (fun N => ∑ n ∈ Finset.range N,
        coprimeEulerDeletionProductWeightedJump p q rho n)
      atTop (nhds 0) := by
  have hpT := tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero
    (p - 1) hrhoRe hrho1 hzeta
  have hqT := tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero
    (q - 1) hrhoRe hrho1 hzeta
  have hpqT := tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero
    (p * q - 1) hrhoRe hrho1 hzeta
  have hcomb := (hpT.add hqT).sub hpqT
  have hsame : Tendsto
      (fun N => ∑ n ∈ Finset.range N,
        coprimeEulerDeletionProductWeightedJump p q rho n)
      atTop (nhds (0 + 0 - 0)) := by
    apply hcomb.congr'
    exact Filter.Eventually.of_forall fun N =>
      (coprimeEulerDeletionProduct_prefix_eq hp hq hpq rho N).symm
  simpa only [zero_add, zero_sub, neg_zero] using hsame

/-! ## Arbitrary finite pairwise-coprime cylinder products -/

/-- Generic inclusion--exclusion rewrites a nonempty product of complements as an alternating
sum of complements of subset products. -/
private theorem prod_one_sub_eq_sum_nonempty_one_sub_prod
    {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (hB : B.Nonempty) (g : ι → ℤ) :
    (∏ p ∈ B, (1 - g p)) =
      ∑ S ∈ B.powerset.erase ∅,
        (-1 : ℤ) ^ (S.card + 1) * (1 - ∏ p ∈ S, g p) := by
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one]
  have hempty : (∅ : Finset ι) ∈ B.powerset := by simp
  have hsplit (f : Finset ι → ℤ) :
      ∑ S ∈ B.powerset, f S = f ∅ + ∑ S ∈ B.powerset.erase ∅, f S := by
    rw [← Finset.sum_erase_add B.powerset f hempty, add_comm]
  have hsign : (∑ S ∈ B.powerset.erase ∅, (-1 : ℤ) ^ S.card) = -1 := by
    have hz : (∑ S ∈ B.powerset, (-1 : ℤ) ^ S.card) = 0 := by
      exact Finset.sum_powerset_neg_one_pow_card_of_nonempty hB
    rw [hsplit] at hz
    simpa using eq_neg_of_add_eq_zero_right hz
  rw [hsplit]
  simp only [Finset.prod_empty, mul_one]
  calc
    1 + ∑ S ∈ B.powerset.erase ∅, (-1 : ℤ) ^ S.card * ∏ i ∈ S, g i =
        -(∑ S ∈ B.powerset.erase ∅, (-1 : ℤ) ^ S.card) +
          ∑ S ∈ B.powerset.erase ∅, (-1 : ℤ) ^ S.card * ∏ i ∈ S, g i := by
            rw [hsign]
            ring
    _ = ∑ S ∈ B.powerset.erase ∅,
        ((-1 : ℤ) ^ (S.card + 1) * (1 - ∏ i ∈ S, g i)) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S hS
      rw [pow_succ]
      ring

/-- For a pairwise-coprime family, its product divides `n` exactly when every member does. -/
theorem finset_prod_dvd_iff_of_pairwise_coprime (S : Finset ℕ)
    (hpair : (S : Set ℕ).Pairwise Nat.Coprime) (n : ℕ) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
      have hpairS : (S : Set ℕ).Pairwise Nat.Coprime := by
        intro a ha b hb hab
        exact hpair (by simp [ha]) (by simp [hb]) hab
      have hpC : Nat.Coprime p (∏ q ∈ S, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        exact hpair (by simp) (by simp [hq]) (by rintro rfl; exact hpS hq)
      rw [Finset.prod_insert hpS]
      constructor
      · intro h q hq
        rw [Finset.mem_insert] at hq
        rcases hq with hqp | hq
        · subst q
          exact dvd_trans (dvd_mul_right p (∏ q ∈ S, q)) h
        · have hprod : (∏ q ∈ S, q) ∣ n :=
            dvd_trans (dvd_mul_left (∏ q ∈ S, q) p) h
          exact (ih hpairS).1 hprod q hq
      · intro hall
        have hp : p ∣ n := hall p (Finset.mem_insert_self p S)
        have hs : (∏ q ∈ S, q) ∣ n := (ih hpairS).2 fun q hq =>
          hall q (Finset.mem_insert_of_mem hq)
        exact hpC.mul_dvd_of_dvd_of_dvd hp hs

/-- Every finite pairwise-coprime deletion cylinder is an alternating sum of single deletion
channels indexed by nonempty subset products. -/
theorem prod_blockDeletionCoefficient_eq_alternating
    (B : Finset ℕ) (hB : B.Nonempty)
    (hpair : (B : Set ℕ).Pairwise Nat.Coprime) (n : ℕ) :
    (∏ p ∈ B, blockDeletionCoefficient p n) =
      ∑ S ∈ B.powerset.erase ∅,
        (-1 : ℤ) ^ (S.card + 1) *
          blockDeletionCoefficient (∏ p ∈ S, p) n := by
  let g : ℕ → ℤ := fun p => (p : ℤ) * if p ∣ n then 1 else 0
  have hgeneric := prod_one_sub_eq_sum_nonempty_one_sub_prod B hB g
  calc
    (∏ p ∈ B, blockDeletionCoefficient p n) = ∏ p ∈ B, (1 - g p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [g, blockDeletionCoefficient]
    _ = ∑ S ∈ B.powerset.erase ∅,
        (-1 : ℤ) ^ (S.card + 1) * (1 - ∏ p ∈ S, g p) := hgeneric
    _ = ∑ S ∈ B.powerset.erase ∅,
        (-1 : ℤ) ^ (S.card + 1) *
          blockDeletionCoefficient (∏ p ∈ S, p) n := by
      apply Finset.sum_congr rfl
      intro S hS
      have hSB : S ⊆ B := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS)
      have hpairS : (S : Set ℕ).Pairwise Nat.Coprime := by
        intro p hp q hq hpq
        exact hpair (hSB hp) (hSB hq) hpq
      have hdvd := finset_prod_dvd_iff_of_pairwise_coprime S hpairS n
      congr 1
      rw [Finset.prod_mul_distrib, Finset.prod_boole]
      simp [blockDeletionCoefficient, hdvd]

/-- Weighted path attached to a finite deletion cylinder. -/
def eulerDeletionCylinderWeightedJump
    (B : Finset ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  ((∏ p ∈ B, blockDeletionCoefficient p (n + 1) : ℤ) : ℂ) *
    (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)

/-- Every nonempty subset product of positive moduli is positive. -/
private theorem subset_prod_pos
    {B S : Finset ℕ} (hpos : ∀ p ∈ B, 0 < p) (hSB : S ⊆ B) :
    0 < ∏ p ∈ S, p := by
  exact Finset.prod_pos fun p hp => hpos p (hSB hp)

/-- Pointwise finite-cylinder weighted jump decomposition. -/
theorem eulerDeletionCylinderWeightedJump_eq_alternating
    (B : Finset ℕ) (hB : B.Nonempty) (hpos : ∀ p ∈ B, 0 < p)
    (hpair : (B : Set ℕ).Pairwise Nat.Coprime) (s : ℂ) (n : ℕ) :
    eulerDeletionCylinderWeightedJump B s n =
      ∑ S ∈ B.powerset.erase ∅,
        ((-1 : ℤ) ^ (S.card + 1) : ℂ) *
          eulerDeletionWeightedJump ((∏ p ∈ S, p) - 1) s n := by
  rw [eulerDeletionCylinderWeightedJump,
    prod_blockDeletionCoefficient_eq_alternating B hB hpair]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S hS
  have hSB : S ⊆ B := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS)
  have hprodpos := subset_prod_pos hpos hSB
  rw [eulerDeletionWeightedJump_pred hprodpos]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf

/-- Exact common-cutoff expansion of an arbitrary finite pairwise-coprime deletion cylinder. -/
theorem eulerDeletionCylinder_prefix_eq_alternating
    (B : Finset ℕ) (hB : B.Nonempty) (hpos : ∀ p ∈ B, 0 < p)
    (hpair : (B : Set ℕ).Pairwise Nat.Coprime) (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, eulerDeletionCylinderWeightedJump B s n =
      ∑ S ∈ B.powerset.erase ∅,
        ((-1 : ℤ) ^ (S.card + 1) : ℂ) *
          ∑ n ∈ Finset.range N,
            eulerDeletionWeightedJump ((∏ p ∈ S, p) - 1) s n := by
  simp_rw [eulerDeletionCylinderWeightedJump_eq_alternating B hB hpos hpair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]

/-- Every positive-half-plane zeta zero closes every nonempty finite pairwise-coprime deletion
cylinder under ordinary common cutoffs. -/
theorem tendsto_eulerDeletionCylinder_prefix_of_zeta_zero
    (B : Finset ℕ) (hB : B.Nonempty) (hpos : ∀ p ∈ B, 0 < p)
    (hpair : (B : Set ℕ).Pairwise Nat.Coprime)
    {rho : ℂ} (hrhoRe : 0 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    Tendsto
      (fun N => ∑ n ∈ Finset.range N, eulerDeletionCylinderWeightedJump B rho n)
      atTop (nhds 0) := by
  have hterms : ∀ S ∈ B.powerset.erase ∅,
      Tendsto
        (fun N => ((-1 : ℤ) ^ (S.card + 1) : ℂ) *
          ∑ n ∈ Finset.range N,
            eulerDeletionWeightedJump ((∏ p ∈ S, p) - 1) rho n)
        atTop (nhds 0) := by
    intro S hS
    exact tendsto_const_nhds.mul
      (tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero
        ((∏ p ∈ S, p) - 1) hrhoRe hrho1 hzeta) |>.trans
          (by simp)
  have hsum := tendsto_finsetSum (B.powerset.erase ∅) hterms
  have hsame : Tendsto
      (fun N => ∑ n ∈ Finset.range N, eulerDeletionCylinderWeightedJump B rho n)
      atTop (nhds (∑ S ∈ B.powerset.erase ∅, (0 : ℂ))) := by
    apply hsum.congr'
    exact Filter.Eventually.of_forall fun N =>
      (eulerDeletionCylinder_prefix_eq_alternating B hB hpos hpair rho N).symm
  simpa using hsame

end RHTower
