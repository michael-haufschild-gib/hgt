import GaloisForLFunctions.RHTower.Sieve.SeparatedCount
import GaloisForLFunctions.RHTower.Sieve.IntegerRowSum

/-! # Harmonic cost of half-periods at separated positive frequencies -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section

/-- The j-th positive detuning costs at most one j-th of the longest
allowed half-period. This compares the full clock with its sharp harmonic price. -/
theorem harmonic_span (F : Finset ℝ) {γ : ℝ} (hγ : 0<γ)
    (hpos : ∀ w∈F, γ≤w) (hsep : ∀ u∈F, ∀ v∈F, u≠v → γ≤|u-v|) :
    ∑ w∈F, π/w ≤ (π/γ)*∑ j∈range F.card, 1/((j:ℝ)+1) := by
  classical
  induction F using Finset.strongInduction with
  | H F ih =>
    rcases F.eq_empty_or_nonempty with rfl|hn
    · simp
    let m := F.max' hn
    have hm : m∈F := F.max'_mem _
    have hgm := hpos m hm
    let S := F.erase m
    have hsub : S⊆F := erase_subset _ _
    have hi := ih S (erase_ssubset hm) (fun w hw => hpos w (hsub hw))
      (fun u hu v hv => hsep u (hsub hu) v (hsub hv))
    have hc := RHTower.Sieve.card_le_of_separated (s:=F) (u:=id) (c:=γ)
      hγ (sub_nonneg.mpr hgm) hsep (fun w hw => ⟨hpos w hw,
        (F.le_max' w hw).trans_eq (by dsimp only [id,m]; ring)⟩)
    have hsize : S.card+1=F.card := card_erase_add_one hm
    have hprod : γ*((S.card:ℝ)+1)≤m := by
      rw [←hsize,Nat.cast_add,Nat.cast_one] at hc
      have hh := mul_le_mul_of_nonneg_right hc hγ.le
      rw [add_mul,div_mul_cancel₀ _ hγ.ne',one_mul] at hh
      linarith only [hh]
    have ht : π/m ≤ (π/γ)*(1/((S.card:ℝ)+1)) := by
      rw [mul_one_div,div_div]
      exact div_le_div_of_nonneg_left pi_pos.le (mul_pos hγ (by positivity)) hprod
    rw [←Finset.add_sum_erase F (fun w => π/w) hm,←hsize,sum_range_succ,mul_add]
    change π/m+(∑ w∈S, π/w)≤_
    linarith only [hi,ht]

/-- Irrespective of the number of distinct replica collisions, the
duration of the positive clock grows only logarithmically in the number
of separated, nonzero absolute frequencies. -/
theorem logarithmic_span (F : Finset ℝ) {γ : ℝ} (hγ : 0<γ)
    (hpos : ∀ w∈F, γ≤w) (hsep : ∀ u∈F, ∀ v∈F, u≠v → γ≤|u-v|) :
    ∑ w∈F, π/w ≤ (π/γ)*(1+log F.card) := by
  apply (harmonic_span F hγ hpos hsep).trans
  apply mul_le_mul_of_nonneg_left _ (div_pos pi_pos hγ).le
  rw [←RHTower.Sieve.sum_Icc_one_div_eq_sum_range]
  exact RHTower.Sieve.sum_Icc_one_div_le_one_add_log F.card

#print axioms logarithmic_span
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
