import GaloisForLFunctions.BiScaleUncertainty.SieveTripleFourier
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Exact finite CRT and centered residue moments

Complete arithmetic periods give product-residue averages by an explicit CRT
bijection. A coordinate appearing once has zero mean; consequently independent
centered rows have quadratic and quartic data determined by coefficient squares.
All finite supports, empty products, and zero coefficients are included.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false

private theorem sum_period_blocks (f : ℕ → ℝ) (p : ℕ)
    (hf : ∀ n, f (n+p) = f n) (k : ℕ) :
    (∑ n ∈ Finset.range (p*k), f n) = (k : ℝ) * ∑ n ∈ Finset.range p, f n := by
  have hs (j n : ℕ) : f (n+p*j) = f n := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ,← Nat.add_assoc,hf,ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih]
    have ht (n : ℕ) : f (p*k+n) = f n := by rw [Nat.add_comm,hs]
    simp_rw [ht]
    push_cast
    ring

/-- Exact CRT averaging for any finite coprime family over any multiple of its period. -/
theorem period_average_crt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (hc : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (P : ℕ) (hP : 0 < P) (hd : (∏ i, p i) ∣ P)
    (F : (∀ i, ZMod (p i)) → ℝ) :
    (∑ n ∈ Finset.range P, F (fun i => (n : ZMod (p i)))) / (P : ℝ) =
      (∑ x : ∀ i, ZMod (p i), F x) / ((∏ i, p i : ℕ) : ℝ) := by
  let Q := ∏ i, p i
  have hQ : 0 < Q := Finset.prod_pos (fun i _ => NeZero.pos (p i))
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  let e := ZMod.prodEquivPi p hc
  have hcast (i : ι) : (Q : ZMod (p i)) = 0 :=
    (ZMod.natCast_eq_zero_iff Q (p i)).mpr (Finset.dvd_prod_of_mem p (Finset.mem_univ i))
  have hper (n : ℕ) : F (fun i => ((n+Q : ℕ) : ZMod (p i))) =
      F (fun i => (n : ZMod (p i))) := by
    congr 1
    funext i
    simp only [Nat.cast_add,hcast,add_zero]
  have he (z : ZMod Q) : e z = fun i => (z.val : ZMod (p i)) := by
    calc
      e z = e (z.val : ZMod Q) := by rw [ZMod.natCast_zmod_val]
      _ = _ := by ext i; simp only [map_natCast]; rfl
  have hbase : (∑ n ∈ Finset.range Q, F (fun i => (n : ZMod (p i)))) =
      ∑ x : ∀ i, ZMod (p i), F x := by
    calc
      _ = ∑ z : ZMod Q, F (fun i => (z.val : ZMod (p i))) := by
        have hh := sum_zmod_val (P := Q) (fun n => (F (fun i => (n : ZMod (p i))) : ℂ))
        exact_mod_cast hh.symm
      _ = _ := Fintype.sum_equiv e.toEquiv _ _ (fun z => congrArg F (he z).symm)
  obtain ⟨k,hk⟩ := hd
  change P = Q*k at hk
  have hk0 : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := by intro hz; rw [hk,hz,Nat.mul_zero] at hP; omega
    exact_mod_cast this
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ
  change _ = (∑ x : ∀ i, ZMod (p i), F x) / (Q : ℝ)
  rw [hk,sum_period_blocks (fun n => F (fun i => (n : ZMod (p i)))) Q hper k,hbase]
  push_cast
  field_simp

/-- Expanding translated linear forms separates coefficients from independent residue factors. -/
theorem sum_linear_products {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] {m : ℕ}
    (a : ι → ℝ) (f : Fin m → ∀ i, β i → ℝ) :
    (∑ x : ∀ i, β i, ∏ j, ∑ i, a i*f j i (x i)) =
      ∑ t : Fin m → ι, (∏ j, a (t j)) * ∑ x : ∀ i, β i, ∏ j, f j (t j) (x (t j)) := by
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.mul_sum]

/-- A factor occurring at just one independent coordinate has zero total mean. -/
theorem sum_pi_lone_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (i : ι) (f : β i → ℝ) (g : (∀ j : {j // j ≠ i}, β j) → ℝ)
    (hf : ∑ x, f x = 0) :
    (∑ x : ∀ i, β i, f (x i) * g (fun j => x j)) = 0 := by
  calc
    _ = ∑ y : β i × (∀ j : {j // j ≠ i}, β j), f y.1 * g y.2 :=
      Fintype.sum_equiv (Equiv.piSplitAt i β) _ _ (fun _ => rfl)
    _ = (∑ x, f x) * ∑ y, g y := by
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = 0 := by rw [hf,zero_mul]

private theorem lone_four_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (i j k l : ι)
    (A : β i → ℝ) (B : β j → ℝ) (C : β k → ℝ) (D : β l → ℝ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hA : ∑ x, A x = 0) :
    (∑ x : ∀ i, β i, A (x i)*B (x j)*C (x k)*D (x l)) = 0 := by
  have h := sum_pi_lone_factor i A
    (fun y => B (y ⟨j,Ne.symm hij⟩)*C (y ⟨k,Ne.symm hik⟩)*D (y ⟨l,Ne.symm hil⟩)) hA
  convert h using 1
  apply Finset.sum_congr rfl
  intro x _
  dsimp
  ring

private theorem quartic_term_equal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (a b : ι → ℝ) (f : Fin 4 → ∀ i, β i → ℝ)
    (hsq : ∀ i, (a i)^2 = (b i)^2) (hf : ∀ t i, ∑ x, f t i x = 0) (i j k l : ι) :
    a i*a j*a k*a l * (∑ x : ∀ i, β i, f 0 i (x i)*f 1 j (x j)*f 2 k (x k)*f 3 l (x l)) =
      b i*b j*b k*b l * (∑ x : ∀ i, β i, f 0 i (x i)*f 1 j (x j)*f 2 k (x k)*f 3 l (x l)) := by
  by_cases hij : i = j
  · subst j
    by_cases hkl : k = l
    · subst l
      have hp := congrArg₂ (fun x y : ℝ => x*y) (hsq i) (hsq k)
      have hc : a i*a i*a k*a k = b i*b i*b k*b k := by nlinarith only [hp]
      rw [hc]
    · by_cases hik : i = k
      · subst k
        have hz : (∑ x : ∀ i, β i, f 0 i (x i)*f 1 i (x i)*f 2 i (x i)*f 3 l (x l)) = 0 := by
          convert lone_four_zero l i i i (f 3 l) (f 0 i) (f 1 i) (f 2 i)
            (Ne.symm hkl) (Ne.symm hkl) (Ne.symm hkl) (hf 3 l) using 1
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [hz]; simp
      · have hz : (∑ x : ∀ i, β i, f 0 i (x i)*f 1 i (x i)*f 2 k (x k)*f 3 l (x l)) = 0 := by
          convert lone_four_zero k i i l (f 2 k) (f 0 i) (f 1 i) (f 3 l)
            (Ne.symm hik) (Ne.symm hik) hkl (hf 2 k) using 1
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [hz]; simp
  · by_cases hik : i = k
    · subst k
      by_cases hjl : j = l
      · subst l
        have hp := congrArg₂ (fun x y : ℝ => x*y) (hsq i) (hsq j)
        have hc : a i*a j*a i*a j = b i*b j*b i*b j := by nlinarith only [hp]
        rw [hc]
      · have hz : (∑ x : ∀ i, β i, f 0 i (x i)*f 1 j (x j)*f 2 i (x i)*f 3 l (x l)) = 0 := by
          convert lone_four_zero j i i l (f 1 j) (f 0 i) (f 2 i) (f 3 l)
            (Ne.symm hij) (Ne.symm hij) hjl (hf 1 j) using 1
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [hz]; simp
    · by_cases hil : i = l
      · subst l
        by_cases hjk : j = k
        · subst k
          have hp := congrArg₂ (fun x y : ℝ => x*y) (hsq i) (hsq j)
          have hc : a i*a j*a j*a i = b i*b j*b j*b i := by nlinarith only [hp]
          rw [hc]
        · have hz : (∑ x : ∀ i, β i, f 0 i (x i)*f 1 j (x j)*f 2 k (x k)*f 3 i (x i)) = 0 := by
            convert lone_four_zero j i k i (f 1 j) (f 0 i) (f 2 k) (f 3 i)
              (Ne.symm hij) hjk (Ne.symm hij) (hf 1 j) using 1
            apply Finset.sum_congr rfl
            intro x _
            ring
          rw [hz]; simp
      · rw [lone_four_zero i j k l (f 0 i) (f 1 j) (f 2 k) (f 3 l) hij hik hil (hf 0 i)]
        simp

/-- Independent centered rows have quartic observations depending only on coefficient squares. -/
theorem independent_quartic_eq_of_sq_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (a b : ι → ℝ) (f : Fin 4 → ∀ i, β i → ℝ)
    (hsq : ∀ i, (a i)^2 = (b i)^2) (hf : ∀ t i, ∑ x, f t i x = 0) :
    (∑ x : ∀ i, β i, ∏ t, ∑ i, a i*f t i (x i)) =
      ∑ x : ∀ i, β i, ∏ t, ∑ i, b i*f t i (x i) := by
  rw [sum_linear_products,sum_linear_products]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.prod_univ_four]
  exact quartic_term_equal a b f hsq hf (t 0) (t 1) (t 2) (t 3)

/-- The same square-only law holds for all translated quadratic observations. -/
theorem independent_quadratic_eq_of_sq_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (a b : ι → ℝ) (f : Fin 2 → ∀ i, β i → ℝ)
    (hsq : ∀ i, (a i)^2 = (b i)^2) (hf : ∀ t i, ∑ x, f t i x = 0) :
    (∑ x : ∀ i, β i, ∏ t, ∑ i, a i*f t i (x i)) =
      ∑ x : ∀ i, β i, ∏ t, ∑ i, b i*f t i (x i) := by
  rw [sum_linear_products,sum_linear_products]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.prod_univ_two]
  by_cases ht : t 0 = t 1
  · rw [ht]
    have hh : a (t 1)*a (t 1) = b (t 1)*b (t 1) := by simpa only [pow_two] using hsq (t 1)
    rw [hh]
  · have hz : (∑ x : ∀ i, β i, f 0 (t 0) (x (t 0))*f 1 (t 1) (x (t 1))) = 0 := by
      exact sum_pi_lone_factor (t 0) (f 0 (t 0))
        (fun y => f 1 (t 1) (y ⟨t 1,Ne.symm ht⟩)) (hf 0 (t 0))
    rw [hz]
    simp

/-- Distinct coprime coordinate periods divide any common ambient period jointly. -/
theorem coprime_prod_dvd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hc : Pairwise (fun i j => Nat.Coprime (p i) (p j))) (P : ℕ) (hd : ∀ i, p i ∣ P) :
    (∏ i, p i) ∣ P := by
  have aux (s : Finset ι) : (∏ i ∈ s, p i) ∣ P := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hcop : Nat.Coprime (p a) (∏ i ∈ s, p i) := by
        apply Nat.Coprime.prod_right
        intro i hi
        apply hc
        intro heq
        exact ha (heq.symm ▸ hi)
      exact hcop.mul_dvd_of_dvd_of_dvd (hd a) ih
  exact aux Finset.univ

/-- Products of odd coordinate periods remain odd, including the empty product. -/
theorem odd_period_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (ho : ∀ i, Odd (p i)) : Odd (∏ i, p i) := by
  have aux (s : Finset ι) : Odd (∏ i ∈ s, p i) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0,rfl⟩
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (ho a).mul ih
  exact aux Finset.univ

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
