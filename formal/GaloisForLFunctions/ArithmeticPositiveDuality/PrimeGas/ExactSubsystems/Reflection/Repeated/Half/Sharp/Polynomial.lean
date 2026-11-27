import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Coefficients

/-! # Deforming one coefficient while preserving positive spectral weights -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Sharp

open Polynomial Finset Filter Topology ZeroConfigurationGeometry

variable {n : ℕ}

def plusPoly (u : Fin n → ℝ) : ℝ[X] := ∏ i, (X+C (u i))

private def negRoots (u : Fin n → ℝ) := univ.val.map (fun i => -u i)

private theorem factors (u : Fin n → ℝ) :
    plusPoly u = ((negRoots u).map (fun x => X-C x)).prod := by
  simp only [negRoots,Multiset.map_map,Function.comp_apply,C_neg,sub_neg_eq_add,plusPoly,prod_map_val]

private theorem root_list (u : Fin n → ℝ) : (plusPoly u).roots=negRoots u := by
  rw [factors,roots_multiset_prod_X_sub_C]

private theorem degree_plus (u : Fin n → ℝ) : (plusPoly u).natDegree=n := by
  rw [factors,natDegree_multiset_prod_X_sub_C_eq_card]
  simp only [negRoots,Multiset.card_map,← Finset.card_def,card_univ,Fintype.card_fin]

private theorem monic_plus (u : Fin n → ℝ) : (plusPoly u).Monic := by
  rw [factors]
  exact monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

theorem coeff_plus (u : Fin n → ℝ) {j : ℕ} (hj : j ≤ n) :
    (plusPoly u).coeff j = elementary u (n-j) := by
  have size : (univ : Finset (Fin n)).card=n := by rw [card_univ,Fintype.card_fin]
  rw [plusPoly,Finset.prod_X_add_C_coeff _ _ (hj.trans_eq size.symm),size,elementary,esymm_map_val]

theorem constant_plus (u : Fin n → ℝ) : (plusPoly u).coeff 0=∏ i, u i := by
  rw [coeff_zero_eq_eval_zero,plusPoly,eval_prod]
  simp only [eval_add,eval_X,eval_C,zero_add]

private theorem simple_pure (u : Fin n → ℝ) (hi : Function.Injective u) (hu : ∀ i, 0<u i ∧ u i<2) :
    IsPure (plusPoly u) ∧ ¬IsFrobeniusCollision (plusPoly u) := by
  have nonzero := (monic_plus u).ne_zero
  have inside (x : ℝ) (hx : x ∈ (plusPoly u).roots) : -2<x ∧ x<0 := by
    rw [root_list] at hx
    obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp hx
    exact ⟨neg_lt_neg (hu i).2,neg_neg_of_pos (hu i).1⟩
  have simple : (plusPoly u).roots.Nodup := by
    rw [root_list,negRoots]
    exact univ.nodup.map (fun i j h => hi (neg_injective h))
  constructor
  · refine ⟨splits_iff_card_roots.mpr ?_,fun x hx => ?_⟩
    · rw [root_list,degree_plus]
      simp only [negRoots,Multiset.card_map,← Finset.card_def,card_univ,Fintype.card_fin]
    · have h := inside x hx
      exact abs_le.mpr ⟨h.1.le,by linarith only [h.2]⟩
  · rintro (⟨x,hx,hdx⟩ | h₂ | h₂)
    · have h := (one_lt_rootMultiplicity_iff_isRoot nonzero).mpr ⟨hx,hdx⟩
      rw [← count_roots] at h
      exact h.not_ge (Multiset.nodup_iff_count_le_one.mp simple x)
    · have h := (inside 2 ((mem_roots nonzero).mpr h₂)).2
      linarith only [h]
    · exact (inside (-2) ((mem_roots nonzero).mpr h₂)).1.false

private theorem weights_of_negative_roots (P : ℝ[X]) (hm : P.Monic) (hs : P.Splits) (hd : P.natDegree=n)
    (hr : ∀ x ∈ P.roots, x<0) : ∃ u : Fin n → ℝ, (∀ i, 0<u i) ∧ plusPoly u=P := by
  obtain ⟨m,f,hf⟩ := multiset_eq_map_univ_val P.roots
  have size := congrArg Multiset.card hf
  simp only [Multiset.card_map,← Finset.card_def,card_univ,Fintype.card_fin,splits_iff_card_roots.mp hs,hd] at size
  subst m
  refine ⟨fun i => -f i,fun i => neg_pos.mpr (hr _ ?_),?_⟩
  · rw [← hf]
    exact Multiset.mem_map.mpr ⟨i,mem_univ_val i,rfl⟩
  · calc plusPoly (fun i => -f i) = (P.roots.map (fun r => X-C r)).prod := by
            rw [← hf,Multiset.map_map]
            simp only [Function.comp_apply,plusPoly,C_neg,sub_eq_add_neg,prod_map_val]
         _ = P := (hs.eq_prod_roots_of_monic hm).symm

/-- Moving a coefficient of degree below the dimension in the positive direction preserves
positive weights for a sufficiently small displacement. -/
theorem perturb_coefficient (u : Fin n → ℝ) (hi : Function.Injective u)
    (hu : ∀ i, 0<u i ∧ u i<2) {r : ℕ} (hr : r<n) :
    ∃ (v : Fin n → ℝ) (a : ℝ), 0<a ∧ (∀ i, 0<v i) ∧ plusPoly v=plusPoly u+monomial r a := by
  let P := fun a : ℝ => plusPoly u+monomial r a
  have lower (a : ℝ) : (monomial r a).natDegree < (plusPoly u).natDegree :=
    (natDegree_monomial_le a).trans_lt (hr.trans_eq (degree_plus u).symm)
  have degree (a : ℝ) : (P a).natDegree=n :=
    (natDegree_add_eq_left_of_natDegree_lt (lower a)).trans (degree_plus u)
  have monic (a : ℝ) : (P a).Monic :=
    (monic_plus u).add_of_left (degree_lt_degree (lower a))
  have cont (j : ℕ) : Continuous fun a => (P a).coeff j := by
    simp only [P,coeff_add,coeff_monomial]
    split_ifs
    · exact continuous_const.add continuous_id
    · exact continuous_const
  have orig : P 0=plusPoly u := by simp [P]
  obtain ⟨pure,free⟩ := simple_pure u hi hu
  have near := eventually_pure_of_simple (fun a => (degree a).le) cont (t₀ := 0)
    (orig ▸ pure) (degree 0) (orig ▸ free)
  obtain ⟨a,ha,split,_⟩ := near.exists_gt
  have hneg (x : ℝ) (hx : x ∈ (P a).roots) : x<0 := by
    by_contra! hn
    have hp : 0 < (P a).eval x := by
      simp only [P,eval_add,plusPoly,eval_prod,eval_X,eval_C,eval_monomial]
      exact add_pos_of_pos_of_nonneg (prod_pos fun i _ => add_pos_of_nonneg_of_pos hn (hu i).1)
        (mul_nonneg ha.le (pow_nonneg hn _))
    exact hp.ne' ((mem_roots (monic a).ne_zero).mp hx)
  obtain ⟨v,hv,he⟩ := weights_of_negative_roots (P a) (monic a) split (degree a) hneg
  exact ⟨v,a,ha,hv,he⟩

#print axioms perturb_coefficient

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Sharp
