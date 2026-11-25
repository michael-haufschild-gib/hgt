import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder.LeftLimits

/-! # Two monomials of an annihilating equation have comparable sizes at contact -/

open Set Filter Topology Polynomial
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder
open BudgetComparisons
noncomputable section

/-- A maximal term of a cancelling sum is bounded by the number of terms
times its runner-up. Both comparisons survive reordering by polynomial degree. -/
private theorem comparable_pair (S : Finset ℕ) (hS : S.Nonempty) (a : ℕ → ℝ)
    (ha : ∀ i∈S, a i≠0) (hsum : ∑ i∈S,a i=0) :
    ∃ i∈S, ∃ j∈S, i<j ∧ |a i|≤(S.card:ℝ)*|a j| ∧ |a j|≤(S.card:ℝ)*|a i| := by
  obtain ⟨i,hi,hmax⟩ := S.exists_max_image (fun i => |a i|) hS
  have heq := (Finset.sum_erase_add S a hi).trans hsum
  have hrest : (S.erase i).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty,zero_add] at heq
    exact ha i hi heq
  obtain ⟨j,hj,hle⟩ := (S.erase i).exists_max_image (fun j => |a j|) hrest
  have hji := Finset.ne_of_mem_erase hj
  have hjS := Finset.mem_of_mem_erase hj
  have h₁ : |a i|≤(S.card:ℝ)*|a j| := by
    have hab : |a i|=|∑ k∈S.erase i,a k| := by rw [show (∑ k∈S.erase i,a k)= -a i by linarith only [heq],abs_neg]
    rw [hab]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hb := Finset.sum_le_sum (fun k hk => hle k hk)
    rw [Finset.sum_const,nsmul_eq_mul] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card (Finset.erase_subset ..))) (abs_nonneg _))
  have h₂ : |a j|≤(S.card:ℝ)*|a i| := (hmax j hjS).trans
    (le_mul_of_one_le_left (abs_nonneg _) (by
      exact_mod_cast (show 1 ≤ S.card from Finset.card_pos.mpr hS) : (1:ℝ) ≤ S.card))
  rcases lt_or_gt_of_ne hji with h|h
  · exact ⟨j,hjS,i,hi,h,h₂,h₁⟩
  · exact ⟨i,hi,j,hjS,h,h₁,h₂⟩

/-- A nonzero analytic coefficient has an exact positive leading modulus
to the left of every date, including where its value vanishes. -/
theorem coefficient_order (a : coefficients) (hn : a≠0) (v : ℝ) :
    ∃ r : ℕ, ∃ A>0, Tendsto (fun t => |atTime t a|/(v-t)^r) (𝓝[<] v) (𝓝 A) := by
  let g (t : ℝ) := atTime t a
  have ha : AnalyticOnNhd ℝ g univ := analytic_coefficient a
  have hne : ¬∀ᶠ t in 𝓝 v, g t=0 := by
    intro hz
    have h := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ v) hz
    exact hn (Subtype.ext (funext fun t => h (mem_univ t)))
  obtain ⟨r,k,hk,hv,hfac⟩ := (ha v (mem_univ _)).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  refine ⟨r,|k v|,abs_pos.mpr hv,(hk.continuousAt.abs.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
  filter_upwards [nhdsWithin_le_nhds hfac,self_mem_nhdsWithin] with t ht htv
  change |k t|=|g t|/(v-t)^r
  rw [ht,smul_eq_mul,abs_mul,abs_pow,abs_sub_comm,abs_of_pos (sub_pos.mpr htv)]
  field_simp [(sub_pos.mpr htv).ne']

/-- The same two distinct degrees stay comparable on dates arbitrarily
close to the selected contact. Pigeonholing is over polynomial support. -/
theorem frequent_balance {f : ℝ → ℝ} (p : coefficients[X]) (hp : p≠0)
    (hzero : aeval f p=0) (v : ℝ) (hpos : ∀ᶠ t in 𝓝[<] v, 0<f t) :
    let term := fun i t => atTime t (p.coeff i)*f t^i
    let M := (p.support.card:ℝ)
    ∃ i∈p.support, ∃ j∈p.support, i<j ∧ ∃ᶠ t in 𝓝[<] v,
      |term i t|≤M*|term j t| ∧ |term j t|≤M*|term i t| := by
  intro term M
  have hs := Polynomial.support_nonempty.mpr hp
  have nonzero (i : ℕ) (hi : i∈p.support) : ∀ᶠ t in 𝓝[<] v, atTime t (p.coeff i)≠0 := by
    obtain ⟨r,A,hA,hlim⟩ := coefficient_order _ (mem_support_iff.mp hi) v
    filter_upwards [hlim.eventually_const_lt hA] with t ht
    exact fun hz => by simpa only [hz,abs_zero,zero_div,lt_self_iff_false] using ht
  have all := (p.support.eventually_all).mpr nonzero
  have hfreq : ∃ᶠ t in 𝓝[<] v, ∃ i∈p.support, ∃ j∈p.support, i<j ∧
      |term i t|≤M*|term j t| ∧ |term j t|≤M*|term i t| := by
    apply Filter.Eventually.frequently
    filter_upwards [all,hpos] with t hne ht
    apply comparable_pair _ hs (fun i => term i t)
    · exact fun i hi => mul_ne_zero (hne i hi) (pow_ne_zero _ ht.ne')
    · have h := (aeval_atTime p f t).symm.trans (congrFun hzero t)
      rwa [eval₂_eq_sum,Polynomial.sum] at h
  obtain ⟨i,hi,h⟩ := p.support.frequently_exists.mp hfreq
  obtain ⟨j,hj,hij⟩ := p.support.frequently_exists.mp h
  obtain ⟨_,hij'⟩ := (hij.mono fun _ hh => hh.1).exists
  exact ⟨i,hi,j,hj,hij',hij.mono fun _ hh => hh.2⟩

#print axioms frequent_balance
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder
