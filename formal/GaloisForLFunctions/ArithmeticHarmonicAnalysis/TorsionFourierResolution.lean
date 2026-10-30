import Mathlib.Analysis.Fourier.ZMod

/-!
# Exact resolution on finite torsion grids

Independent torsion phases read a frequency vector only modulo their order.
Fourier inversion recovers the sum of coefficients in each residue fibre;
vanishing on the whole grid is exactly cancellation inside every fibre.
The statements include all collisions, at every support size.
-/

open Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ) [NeZero q]

/-- The character of a residue vector on the full torsion grid. -/
def torsionPhase (a t : ι → ZMod q) : ℂ :=
  ∏ i, ZMod.stdAddChar (t i * a i)

private theorem conj_stdAddChar (z : ZMod q) :
    conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj]
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe]

omit [DecidableEq ι] in
/-- Multiplication and conjugation subtract residue frequencies. -/
theorem torsionPhase_mul_conj (a b t : ι → ZMod q) :
    torsionPhase q a t * conj (torsionPhase q b t) = torsionPhase q (a - b) t := by
  simp only [torsionPhase, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [conj_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [Pi.sub_apply]
  ring

/-- A complete torsion average retains exactly the zero residue vector. -/
theorem sum_torsionPhase (a : ι → ZMod q) :
    (∑ t : ι → ZMod q, torsionPhase q a t) =
      if a = 0 then (q : ℂ) ^ Fintype.card ι else 0 := by
  classical
  unfold torsionPhase
  rw [← Fintype.prod_sum (fun i (z : ZMod q) => ZMod.stdAddChar (z * a i))]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  by_cases ha : a = 0
  · simp only [ha, Pi.zero_apply, if_true, ZMod.card, prod_const, card_univ]
  · rw [if_neg ha]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp only [if_neg hi, Nat.cast_zero])

/-- Distinct residue vectors are orthogonal on the complete torsion grid. -/
theorem sum_torsionPhase_mul_conj (a b : ι → ZMod q) :
    (∑ t : ι → ZMod q, torsionPhase q a t * conj (torsionPhase q b t)) =
      if a = b then (q : ℂ) ^ Fintype.card ι else 0 := by
  simp only [torsionPhase_mul_conj, sum_torsionPhase, sub_eq_zero]

variable {κ : Type*}

/-- A finite polynomial sampled on the torsion grid. -/
def torsionPolynomial (S : Finset κ) (e : κ → ι → ZMod q)
    (c : κ → ℂ) (t : ι → ZMod q) : ℂ :=
  ∑ n ∈ S, c n * torsionPhase q (e n) t

/-- The coefficient visible at a given residue frequency. -/
def residueCoefficient (S : Finset κ) (e : κ → ι → ZMod q)
    (c : κ → ℂ) (r : ι → ZMod q) : ℂ := by
  classical
  exact ∑ n ∈ S with e n = r, c n

/-- Fourier inversion recovers the entire coefficient fibre, including collisions. -/
theorem torsion_coefficient_recovery (S : Finset κ) (e : κ → ι → ZMod q)
    (c : κ → ℂ) (r : ι → ZMod q) :
    (∑ t, torsionPolynomial q S e c t * conj (torsionPhase q r t)) =
      (q : ℂ) ^ Fintype.card ι * residueCoefficient q S e c r := by
  classical
  simp only [torsionPolynomial, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, sum_torsionPhase_mul_conj]
  rw [residueCoefficient, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> ring

/-- The residue fibres reconstruct every sampled value exactly. -/
theorem torsionPolynomial_eq_sum_residueCoefficient (S : Finset κ)
    (e : κ → ι → ZMod q) (c : κ → ℂ) (t : ι → ZMod q) :
    torsionPolynomial q S e c t =
      ∑ r, residueCoefficient q S e c r * torsionPhase q r t := by
  classical
  simp only [residueCoefficient, Finset.sum_filter, Finset.sum_mul,
    ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, torsionPolynomial]

/-- Vanishing on the whole grid is precisely cancellation in every residue fibre. -/
theorem torsionPolynomial_vanishes_iff (S : Finset κ) (e : κ → ι → ZMod q)
    (c : κ → ℂ) :
    (∀ t, torsionPolynomial q S e c t = 0) ↔
      ∀ r, residueCoefficient q S e c r = 0 := by
  constructor
  · intro h r
    have hr := torsion_coefficient_recovery q S e c r
    simp only [h, zero_mul, Finset.sum_const_zero] at hr
    exact (mul_eq_zero.mp hr.symm).resolve_left
      (pow_ne_zero _ (by exact_mod_cast NeZero.ne q))
  · intro h t
    rw [torsionPolynomial_eq_sum_residueCoefficient]
    simp only [h, zero_mul, Finset.sum_const_zero]

/-- Parseval retains squared fibre sums, rather than the ungrouped coefficients. -/
theorem torsion_parseval (S : Finset κ) (e : κ → ι → ZMod q) (c : κ → ℂ) :
    (∑ t, torsionPolynomial q S e c t * conj (torsionPolynomial q S e c t)) =
      (q : ℂ) ^ Fintype.card ι *
        ∑ r, residueCoefficient q S e c r * conj (residueCoefficient q S e c r) := by
  classical
  have hc (t : ι → ZMod q) : conj (torsionPolynomial q S e c t) =
      ∑ r, conj (residueCoefficient q S e c r) * conj (torsionPhase q r t) := by
    rw [torsionPolynomial_eq_sum_residueCoefficient, map_sum]
    exact Finset.sum_congr rfl fun r _ => map_mul _ _ _
  simp only [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = (∑ t, torsionPolynomial q S e c t * conj (torsionPhase q r t)) *
        conj (residueCoefficient q S e c r) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          ring
    _ = _ := by rw [torsion_coefficient_recovery]; ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
