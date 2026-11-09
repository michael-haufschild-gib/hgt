import GaloisForLFunctions.HTGeometry.AlternantVandermondeDivisibility
import GaloisForLFunctions.HTGeometry.ResidueRootFamilyTransfer
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The discriminant of a monic root polynomial

Evaluating the derivative at every labelled root pairs each difference with
its reverse. This gives the Sylvester discriminant as the Vandermonde square,
including repeated roots and positive characteristic.
-/

noncomputable section
open Finset Polynomial
namespace GaloisForLFunctions.HTGeometry
variable {R : Type*} [CommRing R]

/-- Every ordered pair of distinct labels contributes its root difference. -/
def orderedRootDifferenceProduct {n : ℕ} (x : Fin n → R) : R :=
  ∏ i, ∏ j, if i = j then 1 else x i - x j

/-- Pairing reverse ordered differences produces the discriminant sign. -/
theorem orderedRootDifferenceProduct_eq {n : ℕ} (x : Fin n → R) :
    orderedRootDifferenceProduct x =
      (-1) ^ (n * (n - 1) / 2) * vandermondeProd x ^ 2 := by
  induction n with
  | zero => simp [orderedRootDifferenceProduct, vandermondeProd]
  | succ m ih =>
    have hrow (i : Fin m) :
        (∏ j : Fin (m + 1), if i.succ = j then 1 else x i.succ - x j) =
          (x i.succ - x 0) *
            ∏ j : Fin m, if i = j then 1 else x i.succ - x j.succ := by
      rw [Fin.prod_univ_succ]
      simp only [Fin.succ_ne_zero, ↓reduceIte, Fin.succ_inj]
    have hzero : (∏ j : Fin (m + 1), if (0 : Fin (m + 1)) = j then 1 else x 0 - x j) =
        ∏ j : Fin m, (x 0 - x j.succ) := by
      rw [Fin.prod_univ_succ]
      simp only [↓reduceIte, one_mul]
      apply Finset.prod_congr rfl
      intro j _
      rw [if_neg (Fin.succ_ne_zero j).symm]
    have hneg : (∏ j : Fin m, (x 0 - x j.succ)) =
        (-1) ^ m * ∏ j : Fin m, (x j.succ - x 0) := by
      have ht (j : Fin m) : x 0 - x j.succ = -(x j.succ - x 0) := (neg_sub _ _).symm
      simp_rw [ht]
      rw [Finset.prod_neg]
      simp only [card_univ, Fintype.card_fin]
    have hexp : (m + 1) * ((m + 1) - 1) / 2 = m + m * (m - 1) / 2 := by
      have he : (m + 1) * m = m * (m - 1) + 2 * m := by
        cases m with
        | zero => rfl
        | succ m => simp only [Nat.succ_sub_one]; ring
      change (m + 1) * m / 2 = m + m * (m - 1) / 2
      rw [he]
      omega
    rw [orderedRootDifferenceProduct, Fin.prod_univ_succ, hzero]
    simp_rw [hrow]
    rw [Finset.prod_mul_distrib, hneg]
    change _ * (_ * orderedRootDifferenceProduct (x ∘ Fin.succ)) = _
    rw [ih, vandermondeProd_succ, hexp, pow_add]
    ring

/-- The product of root derivatives is the product of all ordered root differences. -/
theorem prod_eval_derivative_rootPolynomial {n : ℕ} (x : Fin n → R) :
    (∏ i, Polynomial.eval (x i) (Polynomial.derivative (∏ j, (X - C (x j))))) =
      orderedRootDifferenceProduct x := by
  classical
  rw [orderedRootDifferenceProduct]
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_derivative_prod_X_sub_C]
  calc
    (∏ j ∈ univ.erase i, (x i - x j)) =
        ∏ j ∈ univ.erase i, if i = j then 1 else x i - x j := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg (Ne.symm (Finset.mem_erase.mp hj).1)]
    _ = ∏ j, if i = j then 1 else x i - x j := by
      apply Finset.prod_subset (Finset.erase_subset i univ)
      intro j _ hj
      have he : j = i := by simpa only [Finset.mem_erase, Finset.mem_univ,
        and_true, not_not] using hj
      simp only [he, ↓reduceIte]

section Domain
variable [IsDomain R]

/-- A split monic polynomial has a labelled root tuple retaining all multiplicities. -/
theorem exists_root_tuple_of_monic_splits {f : R[X]} (hf : f.Monic)
    (hs : f.Splits) {n : ℕ} (hn : f.natDegree = n) :
    ∃ x : Fin n → R, f = ∏ j, (X - C (x j)) := by
  classical
  have hl : f.roots.toList.length = n := by
    rw [Multiset.length_toList, ← hs.natDegree_eq_card_roots, hn]
  have hp (l : List R) : (l.map (fun a => X - C a)).prod =
      ∏ i : Fin l.length, (X - C (l.get i)) := by
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  refine ⟨fun i => f.roots.toList.get ((finCongr hl).symm i), ?_⟩
  conv_lhs => rw [hs.eq_prod_roots_of_monic hf, ← Multiset.coe_toList f.roots,
    Multiset.map_coe, Multiset.prod_coe, hp]
  exact Fintype.prod_equiv (finCongr hl) _ _ (fun i => by
    change X - C (f.roots.toList.get i) =
      X - C (f.roots.toList.get ((finCongr hl).symm ((finCongr hl) i)))
    rw [Equiv.symm_apply_apply])

/-- A monic root polynomial has one degree for each label, even when roots collide. -/
theorem natDegree_rootPolynomial {n : ℕ} (x : Fin n → R) :
    (∏ j, (X - C (x j))).natDegree = n := by
  rw [Polynomial.natDegree_prod_of_monic univ (fun j : Fin n => X - C (x j))
    (fun j _ => monic_X_sub_C (x j))]
  simp only [natDegree_X_sub_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- The Sylvester resultant of a root polynomial and its derivative retains every collision. -/
theorem resultant_rootPolynomial_derivative {n : ℕ} (x : Fin n → R) :
    Polynomial.resultant (∏ j, (X - C (x j)))
      (Polynomial.derivative (∏ j, (X - C (x j)))) n (n - 1) =
        (-1) ^ (n * (n - 1) / 2) * vandermondeProd x ^ 2 := by
  classical
  let f : R[X] := ∏ j, (X - C (x j))
  have hm : f.Monic := monic_prod_X_sub_C x univ
  have hn : f.natDegree = n := natDegree_rootPolynomial x
  have hs : f.Splits := Polynomial.Splits.prod (fun j _ => Polynomial.Splits.X_sub_C (x j))
  have hd : f.derivative.natDegree ≤ n - 1 := by
    simpa only [hn] using Polynomial.natDegree_derivative_le f
  have hr : f.roots = univ.val.map x := by
    have he : f = ((univ.val.map x).map (fun a => X - C a)).prod := by
      rw [Multiset.map_map]
      rfl
    rw [he, roots_multiset_prod_X_sub_C]
  have h := Polynomial.resultant_eq_prod_eval f f.derivative (n - 1) hd hs
  rw [hn, hm.leadingCoeff, one_pow, one_mul, hr, Multiset.map_map] at h
  change Polynomial.resultant f f.derivative n (n - 1) = _
  rw [h]
  change (∏ i, Polynomial.eval (x i) f.derivative) = _
  rw [prod_eval_derivative_rootPolynomial, orderedRootDifferenceProduct_eq]

/-- The actual Sylvester discriminant is the Vandermonde square in every characteristic. -/
theorem discr_rootPolynomial {n : ℕ} (x : Fin n → R) :
    Polynomial.discr (∏ j, (X - C (x j))) = vandermondeProd x ^ 2 := by
  classical
  cases n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, vandermondeProd, one_pow]
    exact Polynomial.discr_C 1
  | succ n =>
    let f : R[X] := ∏ j, (X - C (x j))
    have hm : f.Monic := monic_prod_X_sub_C x univ
    have hn : f.natDegree = n + 1 := natDegree_rootPolynomial x
    have hd : 0 < f.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
    have h := Polynomial.resultant_deriv hd
    rw [hn, hm.leadingCoeff, mul_one, resultant_rootPolynomial_derivative] at h
    have hsign : (-1 : R) ^ ((n + 1) * ((n + 1) - 1) / 2) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact (mul_left_cancel₀ hsign h).symm

end Domain

/-- Monicity makes discriminants compatible with coefficient maps, even noninjective maps. -/
theorem map_discr_of_monic {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) {f : R[X]} (hf : f.Monic) :
    φ f.discr = (f.map φ).discr := by
  by_cases hz : f.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hf hz
    have hR : (1 : R[X]).discr = 1 := Polynomial.discr_C 1
    have hS : (1 : S[X]).discr = 1 := Polynomial.discr_C 1
    rw [Polynomial.map_one, hR, hS, map_one]
  have hn : 0 < f.natDegree := Nat.pos_of_ne_zero hz
  have hnm : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
  have hm := hf.map φ
  have hd : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hn
  have hdm : 0 < (f.map φ).degree := natDegree_pos_iff_degree_pos.mp (by omega)
  have he : (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) * φ f.discr =
      (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) * (f.map φ).discr := calc
    (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) * φ f.discr =
        φ (Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1)) := by
      simpa only [map_mul, map_pow, map_neg, map_one, hf.leadingCoeff, mul_one]
        using (congrArg φ (Polynomial.resultant_deriv hd)).symm
    _ = Polynomial.resultant (f.map φ) (f.map φ).derivative
        f.natDegree (f.natDegree - 1) := by
      rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
    _ = (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) * (f.map φ).discr := by
      simpa only [hnm, hm.leadingCoeff, mul_one] using Polynomial.resultant_deriv hdm
  have h := congrArg (fun y => (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) * y) he
  simpa only [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] using h

#print axioms orderedRootDifferenceProduct_eq
#print axioms exists_root_tuple_of_monic_splits
#print axioms prod_eval_derivative_rootPolynomial
#print axioms resultant_rootPolynomial_derivative
#print axioms discr_rootPolynomial
#print axioms map_discr_of_monic

end GaloisForLFunctions.HTGeometry
