import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Quartic blindness and sixth-order phase coupling on coprime residue rows

Exact CRT averaging over factorial periods reduces literal arithmetic averages
to two independent centered residue rows. Fourth-order translated products
cannot see a relative sign, while the sixth zero-lag moment contains a signed
cubic cross term. All averaging identities use finite bijections and symbolic
polynomial algebra.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
set_option autoImplicit false

/-- Centered divisibility row on a finite residue group. -/
def residueRow (p : ℕ) [NeZero p] (x : ZMod p) : ℝ :=
  if x = 0 then (p : ℝ)-1 else -1

/-- Exact power sum of a centered residue row. -/
theorem sum_residueRow_pow (p : ℕ) [NeZero p] (j : ℕ) :
    (∑ x : ZMod p, residueRow p x ^ j) =
      ((p : ℝ)-1)^j + ((p : ℝ)-1)*(-1)^j := by
  calc
    _ = ∑ x : ZMod p,
        ((if x = 0 then ((p : ℝ)-1)^j - (-1)^j else 0) + (-1)^j) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = 0 <;> simp [residueRow,hx]
    _ = ((p : ℝ)-1)^j - (-1)^j + (p : ℝ)*(-1)^j := by
      simp [Finset.sum_add_distrib, ZMod.card]
    _ = _ := by ring

/-- Translation preserves the zero mean of each centered residue row. -/
theorem sum_residueRow_shift (p : ℕ) [NeZero p] (h : ZMod p) :
    (∑ x : ZMod p, residueRow p (x+h)) = 0 := by
  calc
    _ = ∑ x : ZMod p, residueRow p x :=
      Fintype.sum_equiv (Equiv.addRight h) _ _ (fun _ => rfl)
    _ = 0 := by
      have H := sum_residueRow_pow p 1
      simp only [pow_one] at H
      rw [H]
      ring

private theorem sum_period_blocks (f : ℕ → ℝ) (p : ℕ)
    (hf : ∀ n, f (n+p) = f n) (k : ℕ) :
    (∑ n ∈ Finset.range (p*k), f n) = (k : ℝ) * ∑ n ∈ Finset.range p, f n := by
  have hs (j n : ℕ) : f (n+p*j) = f n := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ, ← Nat.add_assoc, hf, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have ht (n : ℕ) : f (p*k+n) = f n := by rw [Nat.add_comm, hs]
    simp_rw [ht]
    push_cast
    ring

/-- Exact CRT averaging of two residue coordinates over the factorial period. -/
theorem factorial_average_three_five (N : ℕ) (F : ZMod 3 → ZMod 5 → ℝ) :
    (∑ n ∈ Finset.range (N+10).factorial, F n n) / ((N+10).factorial : ℝ) =
      (∑ x : ZMod 3, ∑ y : ZMod 5, F x y) / 15 := by
  have hd3 : 3 ∣ (N+10).factorial := Nat.dvd_factorial (by omega) (by omega)
  have hd5 : 5 ∣ (N+10).factorial := Nat.dvd_factorial (by omega) (by omega)
  have hd : 15 ∣ (N+10).factorial :=
    (by norm_num : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd hd3 hd5
  obtain ⟨k,hk⟩ := hd
  have hper (n : ℕ) : F ((n+15 : ℕ) : ZMod 3) ((n+15 : ℕ) : ZMod 5) = F n n := by
    have h3 : (15 : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff 15 3).mpr (by norm_num)
    have h5 : (15 : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff 15 5).mpr (by norm_num)
    simp [Nat.cast_add,h3,h5]
  have heq : (∑ n ∈ Finset.range 15, F n n) = ∑ x : ZMod 3, ∑ y : ZMod 5, F x y := by
    let e : ZMod 15 ≃+* ZMod 3 × ZMod 5 :=
      ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 5)
    have hz (z : ZMod 15) : e z = ((z.val : ZMod 3), (z.val : ZMod 5)) := by
      calc
        e z = e (z.val : ZMod 15) := by rw [ZMod.natCast_zmod_val]
        _ = _ := map_natCast e z.val
    calc
      _ = ∑ z : ZMod 15, F z.val z.val := (Fin.sum_univ_eq_sum_range _ 15).symm
      _ = ∑ z : ZMod 3 × ZMod 5, F z.1 z.2 := by
        refine Fintype.sum_equiv e.toEquiv _ _ ?_
        intro z
        change F z.val z.val = F (e z).1 (e z).2
        rw [hz]
      _ = _ := Fintype.sum_prod_type _
  have hk0 : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := by
      intro h
      have hP : (N+10).factorial = 0 := by simpa [h] using hk
      exact Nat.factorial_ne_zero _ hP
    exact_mod_cast this
  rw [hk, sum_period_blocks (fun n => F n n) 15 hper k, heq]
  push_cast
  field_simp

private def pairSum (F : ZMod 3 → ZMod 5 → ℝ) : ℝ := ∑ x, ∑ y, F x y

private theorem pairSum_add (F G : ZMod 3 → ZMod 5 → ℝ) :
    pairSum (fun x y => F x y + G x y) = pairSum F + pairSum G := by
  simp [pairSum, Finset.sum_add_distrib]

private theorem pairSum_smul (c : ℝ) (F : ZMod 3 → ZMod 5 → ℝ) :
    pairSum (fun x y => c * F x y) = c * pairSum F := by
  simp [pairSum, Finset.mul_sum]

private theorem pairSum_sep (f : ZMod 3 → ℝ) (g : ZMod 5 → ℝ) :
    pairSum (fun x y => f x * g y) = (∑ x, f x) * ∑ y, g y := by
  unfold pairSum
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- Exact sixth power average for two independent centered prime rows. -/
theorem residue_pair_sixth (a b : ℝ) :
    (∑ x : ZMod 3, ∑ y : ZMod 5, (a*residueRow 3 x+b*residueRow 5 y)^6) / 15 =
      22*a^6+360*a^4*b^2+480*a^3*b^3+1560*a^2*b^4+820*b^6 := by
  have heq : (fun x : ZMod 3 => fun y : ZMod 5 => (a*residueRow 3 x+b*residueRow 5 y)^6) =
      (fun x y =>
        a^6*(residueRow 3 x^6*residueRow 5 y^0) +
        (6*a^5*b)*(residueRow 3 x^5*residueRow 5 y^1) +
        (15*a^4*b^2)*(residueRow 3 x^4*residueRow 5 y^2) +
        (20*a^3*b^3)*(residueRow 3 x^3*residueRow 5 y^3) +
        (15*a^2*b^4)*(residueRow 3 x^2*residueRow 5 y^4) +
        (6*a*b^5)*(residueRow 3 x^1*residueRow 5 y^5) +
        b^6*(residueRow 3 x^0*residueRow 5 y^6)) := by
    funext x y
    ring
  change pairSum _ / 15 = _
  rw [heq]
  simp only [pairSum_add, pairSum_smul, pairSum_sep, sum_residueRow_pow]
  norm_num
  ring

/-- All four-lag row products are invariant under an independent coefficient sign flip. -/
theorem residue_pair_quartic_flip (a b : ℝ) (h : Fin 4 → ZMod 3) (k : Fin 4 → ZMod 5) :
    (∑ x : ZMod 3, ∑ y : ZMod 5,
      ∏ i, (a*residueRow 3 (x+h i)+b*residueRow 5 (y+k i))) =
    ∑ x : ZMod 3, ∑ y : ZMod 5,
      ∏ i, (a*residueRow 3 (x+h i)+(-b)*residueRow 5 (y+k i)) := by
  let f (i : Fin 4) (x : ZMod 3) := residueRow 3 (x+h i)
  let g (i : Fin 4) (y : ZMod 5) := residueRow 5 (y+k i)
  have hf (i : Fin 4) : (∑ x, f i x) = 0 := sum_residueRow_shift 3 (h i)
  have hg (i : Fin 4) : (∑ y, g i y) = 0 := sum_residueRow_shift 5 (k i)
  have heq : (fun x y => (∏ i, (a*f i x+b*g i y)) -
        ∏ i, (a*f i x+(-b)*g i y)) =
      (fun x y =>
        (2*a^3*b)*((f 0 x*f 1 x*f 2 x)*g 3 y +
          (f 0 x*f 1 x*f 3 x)*g 2 y +
          (f 0 x*f 2 x*f 3 x)*g 1 y +
          (f 1 x*f 2 x*f 3 x)*g 0 y) +
        (2*a*b^3)*(f 0 x*(g 1 y*g 2 y*g 3 y) +
          f 1 x*(g 0 y*g 2 y*g 3 y) +
          f 2 x*(g 0 y*g 1 y*g 3 y) +
          f 3 x*(g 0 y*g 1 y*g 2 y))) := by
    funext x y
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change (a*f 0 x+b*g 0 y)*((a*f 1 x+b*g 1 y)*((a*f 2 x+b*g 2 y)*(a*f 3 x+b*g 3 y))) -
      (a*f 0 x+(-b)*g 0 y)*((a*f 1 x+(-b)*g 1 y)*((a*f 2 x+(-b)*g 2 y)*(a*f 3 x+(-b)*g 3 y))) = _
    ring
  apply sub_eq_zero.mp
  change pairSum (fun x y => ∏ i, (a*f i x+b*g i y)) -
    pairSum (fun x y => ∏ i, (a*f i x+(-b)*g i y)) = 0
  have hsub (F G : ZMod 3 → ZMod 5 → ℝ) :
      pairSum F - pairSum G = pairSum (fun x y => F x y - G x y) := by
    simp [pairSum, Finset.sum_sub_distrib]
  rw [hsub,heq]
  simp only [pairSum_add, pairSum_smul, pairSum_sep, hf,hg,mul_zero,zero_mul,add_zero]

/-- Two-lag row averages are also invariant under an independent sign flip. -/
theorem residue_pair_quadratic_flip (a b : ℝ) (h : Fin 2 → ZMod 3) (k : Fin 2 → ZMod 5) :
    (∑ x : ZMod 3, ∑ y : ZMod 5,
      ∏ i, (a*residueRow 3 (x+h i)+b*residueRow 5 (y+k i))) =
    ∑ x : ZMod 3, ∑ y : ZMod 5,
      ∏ i, (a*residueRow 3 (x+h i)+(-b)*residueRow 5 (y+k i)) := by
  let f (i : Fin 2) (x : ZMod 3) := residueRow 3 (x+h i)
  let g (i : Fin 2) (y : ZMod 5) := residueRow 5 (y+k i)
  have hf (i : Fin 2) : (∑ x, f i x) = 0 := sum_residueRow_shift 3 (h i)
  have hg (i : Fin 2) : (∑ y, g i y) = 0 := sum_residueRow_shift 5 (k i)
  have heq : (fun x y => (∏ i, (a*f i x+b*g i y)) -
        ∏ i, (a*f i x+(-b)*g i y)) =
      (fun x y => (2*a*b)*(f 0 x*g 1 y+f 1 x*g 0 y)) := by
    funext x y
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change (a*f 0 x+b*g 0 y)*(a*f 1 x+b*g 1 y) -
      (a*f 0 x+(-b)*g 0 y)*(a*f 1 x+(-b)*g 1 y) = _
    ring
  apply sub_eq_zero.mp
  change pairSum (fun x y => ∏ i, (a*f i x+b*g i y)) -
    pairSum (fun x y => ∏ i, (a*f i x+(-b)*g i y)) = 0
  have hsub (F G : ZMod 3 → ZMod 5 → ℝ) :
      pairSum F - pairSum G = pairSum (fun x y => F x y - G x y) := by
    simp [pairSum, Finset.sum_sub_distrib]
  rw [hsub,heq]
  simp only [pairSum_smul,pairSum_add,pairSum_sep,hf,hg,mul_zero,add_zero]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
