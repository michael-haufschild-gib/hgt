import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin

/-!
# The exponential orbit weight on a finite prime-valuation lattice

At a fixed aperture the visible prime alphabet is finite, so the valuation lattice is `ℤ^P` with
`P` finite.  The exponential weight `w_ρ(ν) = ρ^{|ν|₁}` is square summable there, and its lattice
mass is the coordinate mass to the power of the rank, because the `ℓ¹` length splits coordinatewise
and each coordinate carries the two-sided geometric series `(1+x)/(1-x)`.  The product is computed
in `ℝ≥0∞`, where infinite sums are unconditional and the first-coordinate split is
`ENNReal.tsum_prod'`.  The weight's edge ratios are pinched between `ρ^{|s|₁}` and `ρ^{-|s|₁}`,
which is what makes the weighted valuation shifts bounded.
-/

open Finset
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- The `ℓ¹` length of a valuation vector. -/
def orbitLength {P : Type*} [Fintype P] (ν : P → ℤ) : ℕ := ∑ p, (ν p).natAbs

/-- The exponential orbit weight `ρ^{|ν|₁}`. -/
def orbitWeight {P : Type*} [Fintype P] (ρ : ℝ) (ν : P → ℤ) : ℝ := ρ ^ orbitLength ν

theorem orbitWeight_pos {P : Type*} [Fintype P] {ρ : ℝ} (hρ : 0 < ρ) (ν : P → ℤ) :
    0 < orbitWeight ρ ν := pow_pos hρ _

theorem orbitWeight_zero {P : Type*} [Fintype P] (ρ : ℝ) :
    orbitWeight ρ (0 : P → ℤ) = 1 := by
  have h : orbitLength (0 : P → ℤ) = 0 := by
    simp [orbitLength]
  rw [orbitWeight, h, pow_zero]

/-- The `ℓ¹` length is subadditive. -/
theorem orbitLength_add_le {P : Type*} [Fintype P] (ν s : P → ℤ) :
    orbitLength (ν + s) ≤ orbitLength ν + orbitLength s := by
  rw [orbitLength, orbitLength, orbitLength, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  exact Int.natAbs_add_le (ν p) (s p)

/-- **`(16)`: the weight ratio across a step is at most `ρ^{-|s|₁}`.** -/
theorem orbitWeight_le_ratio {P : Type*} [Fintype P] {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1)
    (ν s : P → ℤ) :
    orbitWeight ρ ν ≤ orbitWeight ρ (ν + s) * (ρ ^ orbitLength s)⁻¹ := by
  have hpow : (0:ℝ) < ρ ^ orbitLength s := pow_pos hρ0 _
  rw [le_mul_inv_iff₀ hpow, orbitWeight, orbitWeight, ← pow_add]
  exact pow_le_pow_of_le_one hρ0.le hρ (orbitLength_add_le ν s)

/-! ## The two-sided geometric coordinate mass -/

private theorem shift_natAbs (n : ℕ) : (-((n : ℤ) + 1)).natAbs = n + 1 := by
  have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hcast, Int.natAbs_neg, Int.natAbs_natCast]

private theorem summable_pow_natAbs_cast {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun n : ℕ => x ^ ((n : ℤ)).natAbs := by
  have hbase : Summable fun n : ℕ => x ^ n := summable_geometric_of_lt_one hx0 hx
  refine hbase.congr fun n => ?_
  rw [Int.natAbs_natCast n]

private theorem summable_pow_natAbs_shift {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun n : ℕ => x ^ (-((n : ℤ) + 1)).natAbs := by
  have hbase : Summable fun n : ℕ => x ^ n := summable_geometric_of_lt_one hx0 hx
  have hmul : Summable fun n : ℕ => x * x ^ n := hbase.mul_left x
  refine hmul.congr fun n => ?_
  rw [shift_natAbs n, pow_succ]
  ring

/-- The two-sided geometric family of a ratio below one is summable. -/
theorem summable_pow_natAbs {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun m : ℤ => x ^ m.natAbs :=
  Summable.of_nat_of_neg_add_one (summable_pow_natAbs_cast hx0 hx)
    (summable_pow_natAbs_shift hx0 hx)

/-- **The exact two-sided geometric mass `(1+x)/(1-x)`.** -/
theorem tsum_pow_natAbs {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    (∑' m : ℤ, x ^ m.natAbs) = (1 + x) / (1 - x) := by
  have hsplit : (∑' m : ℤ, x ^ m.natAbs)
      = (∑' n : ℕ, x ^ ((n : ℤ)).natAbs) + ∑' n : ℕ, x ^ (-((n : ℤ) + 1)).natAbs :=
    tsum_of_nat_of_neg_add_one (summable_pow_natAbs_cast hx0 hx)
      (summable_pow_natAbs_shift hx0 hx)
  have e1 : (∑' n : ℕ, x ^ ((n : ℤ)).natAbs) = (1 - x)⁻¹ := by
    rw [tsum_congr (fun n : ℕ => by rw [Int.natAbs_natCast n] :
      ∀ n : ℕ, x ^ ((n : ℤ)).natAbs = x ^ n)]
    exact tsum_geometric_of_lt_one hx0 hx
  have e2 : (∑' n : ℕ, x ^ (-((n : ℤ) + 1)).natAbs) = x * (1 - x)⁻¹ := by
    rw [tsum_congr (fun n : ℕ => by rw [shift_natAbs n, pow_succ]; ring :
      ∀ n : ℕ, x ^ (-((n : ℤ) + 1)).natAbs = x * x ^ n), tsum_mul_left,
      tsum_geometric_of_lt_one hx0 hx]
  rw [hsplit, e1, e2, div_eq_mul_inv]
  ring

/-! ## The rank product, computed in `ℝ≥0∞` -/

/-- Splitting the first coordinate of a valuation of rank `k+1`. -/
def consValuationEquiv (k : ℕ) : ℤ × (Fin k → ℤ) ≃ (Fin (k + 1) → ℤ) :=
  Fin.consEquiv fun _ : Fin (k + 1) => ℤ

theorem consValuationEquiv_apply (k : ℕ) (q : ℤ × (Fin k → ℤ)) :
    (consValuationEquiv k q : Fin (k + 1) → ℤ) = Fin.cons q.1 q.2 := rfl

theorem orbitLength_consValuationEquiv (k : ℕ) (q : ℤ × (Fin k → ℤ)) :
    orbitLength (consValuationEquiv k q) = (q.1).natAbs + orbitLength q.2 := by
  rw [orbitLength, orbitLength, Fin.sum_univ_succ, consValuationEquiv_apply, Fin.cons_zero]
  simp only [Fin.cons_succ]

/-- **The rank product formula.**  In `ℝ≥0∞` the lattice mass is the coordinate mass raised to the
rank. -/
theorem tsum_pow_orbitLength_fin (x : ℝ≥0∞) (n : ℕ) :
    (∑' ν : Fin n → ℤ, x ^ orbitLength ν) = (∑' m : ℤ, x ^ m.natAbs) ^ n := by
  induction n with
  | zero =>
      haveI : Subsingleton (Fin 0 → ℤ) := ⟨fun f g => funext fun i => i.elim0⟩
      haveI : Unique (Fin 0 → ℤ) := uniqueOfSubsingleton (0 : Fin 0 → ℤ)
      have hlen : orbitLength (default : Fin 0 → ℤ) = 0 := by
        simp [orbitLength]
      rw [tsum_eq_single default (fun b hb => absurd (Subsingleton.elim b default) hb),
        pow_zero, hlen, pow_zero]
  | succ k ih =>
      have hre : (∑' ν : Fin (k + 1) → ℤ, x ^ orbitLength ν)
          = ∑' q : ℤ × (Fin k → ℤ), x ^ orbitLength (consValuationEquiv k q) :=
        ((consValuationEquiv k).tsum_eq
          (fun ν : Fin (k + 1) → ℤ => x ^ orbitLength ν)).symm
      have hterm : (∑' q : ℤ × (Fin k → ℤ), x ^ orbitLength (consValuationEquiv k q))
          = ∑' q : ℤ × (Fin k → ℤ), x ^ (q.1).natAbs * x ^ orbitLength q.2 := by
        refine tsum_congr fun q => ?_
        rw [orbitLength_consValuationEquiv k q, pow_add]
      have hsplit : (∑' q : ℤ × (Fin k → ℤ), x ^ (q.1).natAbs * x ^ orbitLength q.2)
          = ∑' (a : ℤ) (v : Fin k → ℤ), x ^ a.natAbs * x ^ orbitLength v :=
        ENNReal.tsum_prod'
      have hinner : ∀ a : ℤ, (∑' v : Fin k → ℤ, x ^ a.natAbs * x ^ orbitLength v)
          = x ^ a.natAbs * ∑' v : Fin k → ℤ, x ^ orbitLength v :=
        fun a => ENNReal.tsum_mul_left
      rw [hre, hterm, hsplit, tsum_congr hinner, ENNReal.tsum_mul_right, ih, pow_succ]
      ring

/-- Reindexing valuations along an enumeration of the alphabet. -/
def valuationReindex {P : Type*} [Fintype P] (e : P ≃ Fin (Fintype.card P)) :
    (Fin (Fintype.card P) → ℤ) ≃ (P → ℤ) := Equiv.arrowCongr e.symm (Equiv.refl ℤ)

theorem valuationReindex_apply {P : Type*} [Fintype P] (e : P ≃ Fin (Fintype.card P))
    (ν : Fin (Fintype.card P) → ℤ) (p : P) : valuationReindex e ν p = ν (e p) := rfl

theorem orbitLength_valuationReindex {P : Type*} [Fintype P] (e : P ≃ Fin (Fintype.card P))
    (ν : Fin (Fintype.card P) → ℤ) : orbitLength (valuationReindex e ν) = orbitLength ν := by
  rw [orbitLength, orbitLength]
  refine (Fintype.sum_equiv e.symm (fun i : Fin (Fintype.card P) => (ν i).natAbs)
    (fun p : P => (valuationReindex e ν p).natAbs) fun i => ?_).symm
  rw [valuationReindex_apply, Equiv.apply_symm_apply]

/-- The rank product transported to an arbitrary finite alphabet. -/
theorem tsum_pow_orbitLength {P : Type*} [Fintype P] (x : ℝ≥0∞) :
    (∑' ν : P → ℤ, x ^ orbitLength ν) = (∑' m : ℤ, x ^ m.natAbs) ^ Fintype.card P := by
  have e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  have hre : (∑' ν : P → ℤ, x ^ orbitLength ν)
      = ∑' ν : Fin (Fintype.card P) → ℤ, x ^ orbitLength (valuationReindex e ν) :=
    ((valuationReindex e).tsum_eq (fun ν : P → ℤ => x ^ orbitLength ν)).symm
  rw [hre, tsum_congr (fun ν => by rw [orbitLength_valuationReindex e ν]),
    tsum_pow_orbitLength_fin]

/-! ## Square summability of the weight -/

/-- **`(9)`: the orbit weight is square summable at every finite aperture.** -/
theorem summable_orbitWeight_sq {P : Type*} [Fintype P] {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    Summable fun ν : P → ℤ => orbitWeight ρ ν ^ 2 := by
  have hx0 : (0:ℝ) ≤ ρ ^ 2 := by positivity
  have hx : ρ ^ 2 < 1 := by nlinarith
  set y : ℝ≥0 := ⟨ρ ^ 2, hx0⟩ with hy
  have hycoe : ((y : ℝ≥0) : ℝ) = ρ ^ 2 := rfl
  have hcoe : ∀ ν : P → ℤ, orbitWeight ρ ν ^ 2 = ((y ^ orbitLength ν : ℝ≥0) : ℝ) := by
    intro ν
    rw [orbitWeight, ← pow_mul, mul_comm (orbitLength ν) 2, pow_mul, NNReal.coe_pow, hycoe]
  have hZ : Summable fun m : ℤ => ((y : ℝ≥0) : ℝ) ^ m.natAbs := by
    rw [hycoe]
    exact summable_pow_natAbs hx0 hx
  have hZnn : Summable fun m : ℤ => y ^ m.natAbs := by
    rw [← NNReal.summable_coe]
    refine hZ.congr fun m => ?_
    rw [NNReal.coe_pow]
  have hZtop : (∑' m : ℤ, (y : ℝ≥0∞) ^ m.natAbs) ≠ ⊤ := by
    have hcoe' : ∀ m : ℤ, ((y ^ m.natAbs : ℝ≥0) : ℝ≥0∞) = (y : ℝ≥0∞) ^ m.natAbs := by
      intro m
      rw [ENNReal.coe_pow]
    rw [← tsum_congr hcoe']
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hZnn
  have hmass : (∑' ν : P → ℤ, (y : ℝ≥0∞) ^ orbitLength ν) ≠ ⊤ := by
    rw [tsum_pow_orbitLength]
    exact ENNReal.pow_ne_top hZtop
  have hnn : Summable fun ν : P → ℤ => y ^ orbitLength ν := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    have hcoe' : ∀ ν : P → ℤ, ((y ^ orbitLength ν : ℝ≥0) : ℝ≥0∞)
        = (y : ℝ≥0∞) ^ orbitLength ν := by
      intro ν
      rw [ENNReal.coe_pow]
    rw [tsum_congr hcoe']
    exact hmass
  rw [← NNReal.summable_coe] at hnn
  refine hnn.congr fun ν => ?_
  rw [hcoe ν]

/-- **`(9)`: the exact lattice mass of the squared orbit weight.** -/
theorem tsum_orbitWeight_sq {P : Type*} [Fintype P] {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    (∑' ν : P → ℤ, orbitWeight ρ ν ^ 2)
      = ((1 + ρ ^ 2) / (1 - ρ ^ 2)) ^ Fintype.card P := by
  have hx0 : (0:ℝ) ≤ ρ ^ 2 := by positivity
  have hx : ρ ^ 2 < 1 := by nlinarith
  set y : ℝ≥0 := ⟨ρ ^ 2, hx0⟩ with hy
  have hycoe : ((y : ℝ≥0) : ℝ) = ρ ^ 2 := rfl
  have hcoe : ∀ ν : P → ℤ, orbitWeight ρ ν ^ 2 = ((y ^ orbitLength ν : ℝ≥0) : ℝ) := by
    intro ν
    rw [orbitWeight, ← pow_mul, mul_comm (orbitLength ν) 2, pow_mul, NNReal.coe_pow, hycoe]
  have hZ : Summable fun m : ℤ => ((y : ℝ≥0) : ℝ) ^ m.natAbs := by
    rw [hycoe]
    exact summable_pow_natAbs hx0 hx
  have hZnn : Summable fun m : ℤ => y ^ m.natAbs := by
    rw [← NNReal.summable_coe]
    refine hZ.congr fun m => ?_
    rw [NNReal.coe_pow]
  have hlat : Summable fun ν : P → ℤ => y ^ orbitLength ν := by
    have hbase := summable_orbitWeight_sq (P := P) hρ0 hρ
    rw [← NNReal.summable_coe]
    refine hbase.congr fun ν => ?_
    rw [hcoe ν]
  have hcoeZ : ∀ m : ℤ, ((y ^ m.natAbs : ℝ≥0) : ℝ≥0∞) = (y : ℝ≥0∞) ^ m.natAbs := by
    intro m
    rw [ENNReal.coe_pow]
  have hcoeL : ∀ ν : P → ℤ, ((y ^ orbitLength ν : ℝ≥0) : ℝ≥0∞) = (y : ℝ≥0∞) ^ orbitLength ν := by
    intro ν
    rw [ENNReal.coe_pow]
  have hmassE : ((∑' ν : P → ℤ, y ^ orbitLength ν : ℝ≥0) : ℝ≥0∞)
      = ((∑' m : ℤ, y ^ m.natAbs : ℝ≥0) : ℝ≥0∞) ^ Fintype.card P := by
    rw [ENNReal.coe_tsum hlat, ENNReal.coe_tsum hZnn, tsum_congr hcoeZ, tsum_congr hcoeL,
      tsum_pow_orbitLength]
  have hmassN : (∑' ν : P → ℤ, y ^ orbitLength ν) = (∑' m : ℤ, y ^ m.natAbs) ^ Fintype.card P := by
    have := hmassE
    rw [← ENNReal.coe_pow] at this
    exact_mod_cast this
  have hcoord : ((∑' m : ℤ, y ^ m.natAbs : ℝ≥0) : ℝ) = (1 + ρ ^ 2) / (1 - ρ ^ 2) := by
    rw [NNReal.coe_tsum]
    have hfun : ∀ m : ℤ, ((y ^ m.natAbs : ℝ≥0) : ℝ) = (ρ ^ 2) ^ m.natAbs := by
      intro m
      rw [NNReal.coe_pow, hycoe]
    rw [tsum_congr hfun]
    exact tsum_pow_natAbs hx0 hx
  have hfinal : (∑' ν : P → ℤ, orbitWeight ρ ν ^ 2)
      = ((∑' ν : P → ℤ, y ^ orbitLength ν : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_tsum]
    exact tsum_congr hcoe
  rw [hfinal, hmassN, NNReal.coe_pow, hcoord]

end

end RHTower
