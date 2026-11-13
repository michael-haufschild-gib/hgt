import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexOfAQuotientOfLFunctionsCountsItsZerosAndItsPoles

/-!
# The index of an integer combination of configurations counts its net multiplicities

Let `Z_q` be tempered configurations and `n_q` integers, zero for almost all `q`. The net
multiplicity of the combination at a point `ρ` is `Σ_q n_q m_{Z_q}(ρ)` (`netMult`), and its
defect points are the points right of the critical line with net multiplicity `≠ 0` and the
points on the line with net multiplicity `< 0` (`combinationDefect`).

**Theorem** (`exists_le_negIndex_combination_iff`). The form `Σ_q n_q W_{Z_q}` has `m` negative
squares on some family of `m` tests iff the combination has at least `m` defect points.

Proof. Repeat `Z_q` `n_q` times in a first family if `n_q > 0` and `−n_q` times in a second
family if `n_q < 0`. The difference of the sums of Weil's forms of the two families is
`Σ_q n_q W_{Z_q}`, the difference of their multiplicities is the net multiplicity, and the index
law of a quotient of products applies.
-/

open Finset Matrix
open Zeta23 GaloisForLFunctions.HTGeometry
open scoped Classical

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri

/-! ### Repeated indices -/

/-- A sum over indices repeated `a q` times. -/
theorem sum_sigma_fin {ι M : Type*} [Fintype ι] [AddCommMonoid M] (a : ι → ℕ) (g : ι → M) :
    ∑ k : (Σ q : ι, Fin (a q)), g k.1 = ∑ q : ι, a q • g q := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

variable {ι : Type*}

/-- Repeating `g q` for `n q` times in a first sum if `n q > 0`, and `−n q` times in a second
sum if `n q < 0`: the difference is the integer combination. -/
theorem sum_sigma_fin_sub {M : Type*} [AddCommGroup M] [Module ℂ M] (n : ι →₀ ℤ) (g : ι → M) :
    ∑ k : (Σ q : n.support, Fin (n q).toNat), g k.1 -
        ∑ k : (Σ q : n.support, Fin (-(n q)).toNat), g k.1 =
      n.sum fun q k => (k : ℂ) • g q := by
  rw [sum_sigma_fin (fun q : n.support => (n q).toNat) (fun q => g q),
    sum_sigma_fin (fun q : n.support => (-(n q)).toNat) (fun q => g q),
    ← Finset.sum_sub_distrib, Finsupp.sum, ← Finset.sum_coe_sort n.support]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
  congr 1
  have h : ((n q).toNat : ℤ) - ((-(n q)).toNat : ℤ) = n q := by omega
  have h' := congrArg (Int.cast : ℤ → ℂ) h
  push_cast at h'
  exact h'

/-- The same for natural numbers, as an integer. -/
theorem natCast_sum_sigma_fin_sub (n : ι →₀ ℤ) (e : ι → ℕ) :
    ((∑ k : (Σ q : n.support, Fin (n q).toNat), e k.1 : ℕ) : ℤ) -
        ((∑ k : (Σ q : n.support, Fin (-(n q)).toNat), e k.1 : ℕ) : ℤ) =
      n.sum fun q k => k * (e q : ℤ) := by
  rw [sum_sigma_fin (fun q : n.support => (n q).toNat) (fun q => e q),
    sum_sigma_fin (fun q : n.support => (-(n q)).toNat) (fun q => e q),
    Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib, Finsupp.sum,
    ← Finset.sum_coe_sort n.support]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_eq_mul, smul_eq_mul, Nat.cast_mul, Nat.cast_mul, ← sub_mul]
  congr 1
  omega

/-! ### Integer combinations of configurations -/

/-- The net multiplicity of the combination `Σ_q n_q Z_q` at a point. -/
def netMult (n : ι →₀ ℤ) (Z : ι → ZeroConfig) (ρ : ℂ) : ℤ :=
  n.sum fun q k => k * (extMult (Z q) ρ : ℤ)

/-- The defect points of the combination `Σ_q n_q Z_q`: the points right of the critical line
with net multiplicity `≠ 0` and the points on the line with net multiplicity `< 0`. -/
def combinationDefect (n : ι →₀ ℤ) (Z : ι → ZeroConfig) : Set ℂ :=
  {ρ | 1 / 2 < ρ.re ∧ netMult n Z ρ ≠ 0} ∪ {ρ | ρ.re = 1 / 2 ∧ netMult n Z ρ < 0}

/-- The defect points of the two families of repeated configurations are those of the
combination. -/
theorem virtualDefect_repeated (n : ι →₀ ℤ) (Z : ι → ZeroConfig) :
    virtualDefect
        (superposeFamily fun k : (Σ q : n.support, Fin (n q).toNat) => Z k.1)
        (superposeFamily fun k : (Σ q : n.support, Fin (-(n q)).toNat) => Z k.1) =
      combinationDefect n Z := by
  ext ρ
  have hnet := natCast_sum_sigma_fin_sub n fun q => extMult (Z q) ρ
  rw [mem_virtualDefect_superposeFamily, combinationDefect, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_setOf_eq, netMult, ← hnet]
  refine or_congr (and_congr_right fun _ => ?_) (and_congr_right fun _ => ?_)
  · rw [Ne, Ne, sub_eq_zero, Nat.cast_inj]
  · rw [sub_neg, Nat.cast_lt]

/-- **The index of an integer combination of configurations.** The form `Σ_q n_q W_{Z_q}` has
`m` negative squares on some family of `m` tests iff the combination has at least `m` defect
points. -/
theorem exists_le_negIndex_combination_iff (n : ι →₀ ℤ) (Z : ι → ZeroConfig)
    (hZ : ∀ q, SquareRootThreshold.TemperedConfig (Z q)) (m : ℕ) :
    (∃ f : Fin m → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        m ≤ hermNegIndex (n.sum fun q k => (k : ℂ) • zeroGram (Z q) f)) ↔
      (m : ℕ∞) ≤ (combinationDefect n Z).encard := by
  rw [← virtualDefect_repeated n Z,
    ← exists_le_negIndex_quotient_iff
      (fun k : (Σ q : n.support, Fin (n q).toNat) => Z k.1)
      (fun k : (Σ q : n.support, Fin (-(n q)).toNat) => Z k.1)
      (fun k => hZ k.1) (fun k => hZ k.1) m]
  refine exists_congr fun f => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [sum_sigma_fin_sub n fun q => zeroGram (Z q) f]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
