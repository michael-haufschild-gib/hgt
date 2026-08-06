import Mathlib
import GaloisForLFunctions.RHTower.GibbsCurrentGap

/-!
# The zero potential equals an arithmetic ratio

The logarithmic derivative of the gas at the parity point is, on one side, the Coulomb sum
of the zeros against that point, and on the other side an explicit ratio of two
Möbius-weighted Laplace sums — the second weighted by the number of prime factors.  For a
finite set `S` with `J_S(x) = P_S(-1,x) ≠ 0`,

  `∑_ζ 1/(1+ζ)  =  (∑_T |T|·(-1)^{|T|}·e^{-x·e(T)}) / J_S(x)`,

so the geometry of the zero set is not merely constrained by arithmetic: at the parity
point it *is* an arithmetic ratio.
-/

namespace RHTower.GibbsGas

open Polynomial

/-- The logarithmic derivative of a product of linear factors is the Coulomb sum. -/
theorem eval_derivative_multiset_prod (s : Multiset ℂ) (w : ℂ)
    (hw : ∀ ζ ∈ s, w - ζ ≠ 0) :
    Polynomial.eval w (Polynomial.derivative ((s.map (fun ζ => X - C ζ)).prod))
      = Polynomial.eval w ((s.map (fun ζ => X - C ζ)).prod)
        * (s.map (fun ζ => (w - ζ)⁻¹)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : w - a ≠ 0 := hw a (Multiset.mem_cons_self a s)
    have hs : ∀ ζ ∈ s, w - ζ ≠ 0 := fun ζ hζ => hw ζ (Multiset.mem_cons_of_mem hζ)
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [ih hs, Multiset.map_cons, Multiset.sum_cons]
    field_simp

/-- The gas polynomial written over its zero multiset. -/
theorem gibbsPoly_eq_prod_roots (S : Finset ℕ) (x : ℝ) :
    gibbsPoly S x
      = Polynomial.C (gibbsPoly S x).leadingCoeff
        * (((gibbsPoly S x).roots.map (fun ζ => X - C ζ)).prod) := by
  have hsplits : (gibbsPoly S x).Splits := IsAlgClosed.splits _
  exact hsplits.eq_prod_roots

/-- **The parity-point Coulomb sum is an arithmetic ratio.**  Division-free form. -/
theorem gibbs_coulomb_sum_eq (S : Finset ℕ) (x : ℝ)
    (hJ : gibbsDiagC S x (-1) ≠ 0) :
    gibbsDiagC S x (-1) * (((gibbsPoly S x).roots.map (fun ζ => (1 + ζ)⁻¹)).sum)
      = -Polynomial.eval (-1) (Polynomial.derivative (gibbsPoly S x)) := by
  classical
  set rts := (gibbsPoly S x).roots with hrts
  set lc := (gibbsPoly S x).leadingCoeff with hlc
  set Q : Polynomial ℂ := (rts.map (fun ζ => X - C ζ)).prod with hQ
  have hfac : gibbsPoly S x = Polynomial.C lc * Q := gibbsPoly_eq_prod_roots S x
  -- no zero sits at the parity point
  have hne : ∀ ζ ∈ rts, (-1 : ℂ) - ζ ≠ 0 := by
    intro ζ hζ hzero
    have hz : ζ = -1 := by linear_combination -hzero
    apply hJ
    rw [← hz, ← gibbsPoly_eval]
    exact (Polynomial.mem_roots (gibbsPoly_ne_zero S x)).mp hζ
  -- evaluate the factorization and its derivative at the parity point
  have hevalQ : Polynomial.eval (-1 : ℂ) (gibbsPoly S x)
      = lc * Polynomial.eval (-1 : ℂ) Q := by
    rw [hfac]
    simp [Polynomial.eval_mul, Polynomial.eval_C]
  have hderiv : Polynomial.eval (-1 : ℂ) (Polynomial.derivative (gibbsPoly S x))
      = lc * Polynomial.eval (-1 : ℂ) (Polynomial.derivative Q) := by
    rw [hfac, Polynomial.derivative_C_mul]
    simp [Polynomial.eval_mul, Polynomial.eval_C]
  have hcoul := eval_derivative_multiset_prod rts (-1 : ℂ) hne
  -- the two Coulomb sums differ by a sign
  have hsign : (rts.map (fun ζ => ((-1 : ℂ) - ζ)⁻¹)).sum
      = -((rts.map (fun ζ => (1 + ζ)⁻¹)).sum) := by
    have hgen : ∀ s : Multiset ℂ,
        (s.map (fun ζ => ((-1 : ℂ) - ζ)⁻¹)).sum
          = -((s.map (fun ζ => (1 + ζ)⁻¹)).sum) := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
          ih]
        rw [show (-1 : ℂ) - a = -(1 + a) from by ring, inv_neg]
        ring
    exact hgen rts
  calc gibbsDiagC S x (-1) * ((rts.map (fun ζ => (1 + ζ)⁻¹)).sum)
      = (lc * Polynomial.eval (-1 : ℂ) Q) * ((rts.map (fun ζ => (1 + ζ)⁻¹)).sum) := by
        rw [← gibbsPoly_eval, hevalQ]
    _ = -(lc * (Polynomial.eval (-1 : ℂ) Q
          * ((rts.map (fun ζ => ((-1 : ℂ) - ζ)⁻¹)).sum))) := by
        rw [hsign]; ring
    _ = -(lc * Polynomial.eval (-1 : ℂ) (Polynomial.derivative Q)) := by
        rw [hcoul]
    _ = -Polynomial.eval (-1 : ℂ) (Polynomial.derivative (gibbsPoly S x)) := by
        rw [hderiv]

/-- The derivative of the gas in the configuration basis. -/
theorem gibbsPoly_derivative_eval (S : Finset ℕ) (x : ℝ) (z : ℂ) :
    Polynomial.eval z (Polynomial.derivative (gibbsPoly S x))
      = ∑ T ∈ S.powerset,
          gibbsWeight x T * (T.card : ℂ) * z ^ (T.card - 1) := by
  rw [gibbsPoly, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  ring

end RHTower.GibbsGas
