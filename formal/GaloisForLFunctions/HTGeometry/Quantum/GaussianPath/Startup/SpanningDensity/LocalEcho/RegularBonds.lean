import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.SparseMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.GaussianBonds

/-! # Selecting crossed bonds with bounded neighborhoods and nonvanishing longitudinal coupling -/
open Filter MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section

/-- At a reciprocal cutoff q, at most 7q times the path length must be
removed from any bond set to ensure both local estimates. -/
theorem gaussian_regular_bonds :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let q : ℝ := 1/(k+1:ℕ)
      ∀ᶠ n : ℕ in atTop, ∀ E : Finset (Fin (n+1)),
        let u := pathPauliDisorderShell ω n
        ∃ G ⊆ E, (E.card:ℝ) ≤ G.card+7*q*(n+1:ℕ) ∧
          ∀ e∈G, q/2 ≤ |u (zz e)| ∧ localMass u e ≤ B/q := by
  classical
  obtain ⟨_,B,_,hB,hm⟩ := gaussian_path_eventual_coefficient_mass
  let L := 2*43^2*B
  refine ⟨L,by dsimp only [L]; positivity,?_⟩
  filter_upwards [hm,gaussian_subset_longitudinal_mass] with ω hω hmass k
  intro q
  have hq : 0 < q := by dsimp only [q]; positivity
  filter_upwards [hω,hmass k] with n hn hmass
  intro E u
  let S := E.filter fun e => |u (zz e)| < q/2
  let T := E.filter fun e => L/q < localMass u e
  let G := E.filter fun e => q/2 ≤ |u (zz e)| ∧ localMass u e ≤ L/q
  have hweak := hmass S
  have hsum : (∑ e∈S, |u (zz e)|) ≤ S.card*(q/2) := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (s:=S)
      (fun e he => ((Finset.mem_filter.mp he).2 : |u (zz e)| < q/2).le)
  change q*((S.card:ℝ)-3*q*(n+1:ℕ)) ≤ ∑ e∈S, |u (zz e)| at hweak
  have hS : (S.card:ℝ) ≤ 6*q*(n+1:ℕ) := by
    apply (mul_le_mul_iff_right₀ hq).mp
    linarith only [hsum,hweak]
  have hL : 0 < L := by dsimp only [L]; positivity
  have hrow : (T.card:ℝ)*(L/q) ≤ ∑ e∈T, localMass u e := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (s:=T)
      (fun e he => ((Finset.mem_filter.mp he).2 : L/q < localMass u e).le)
  have htotal := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun e _ _ => localMass_nonneg u e)).trans (sum_localMass u)
  have hmul := mul_le_mul_of_nonneg_left hn.2 (show 0 ≤ (43:ℝ)^2 by positivity)
  have hbound : (T.card:ℝ)*(L/q) ≤ L*(n+1:ℕ) := by
    apply (hrow.trans htotal).trans
    dsimp only [L]
    change 43^2*‖u‖^2 ≤ 43^2*(B*(n+2:ℕ)) at hmul
    push_cast at hmul ⊢
    nlinarith only [hmul,mul_nonneg hB.le (Nat.cast_nonneg n : 0 ≤ (n:ℝ))]
  have hT : (T.card:ℝ) ≤ q*(n+1:ℕ) := by
    apply (mul_le_mul_iff_left₀ (div_pos hL hq)).mp
    exact hbound.trans_eq (by field_simp [hq.ne'])
  have hsub : E ⊆ G ∪ (S∪T) := by
    intro e he
    by_cases h : |u (zz e)| < q/2
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,h⟩))
    by_cases hh : localMass u e ≤ L/q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,le_of_not_gt h,hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,lt_of_not_ge hh⟩))
  have hc := (Finset.card_le_card hsub).trans ((Finset.card_union_le ..).trans
    (Nat.add_le_add_left (Finset.card_union_le S T) _))
  have hc' : (E.card:ℝ) ≤ G.card+(S.card+T.card) := by exact_mod_cast hc
  exact ⟨G,Finset.filter_subset ..,by linarith only [hS,hT,hc'],fun _ he => (Finset.mem_filter.mp he).2⟩

#print axioms gaussian_regular_bonds
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
