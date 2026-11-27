import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.FrequencyCount.Interpolation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.Dephasing
import GaloisForLFunctions.RHTower.Sieve.IntegerRowSum

/-! # Duration of the half-period clock relative to any positive clock -/
open Finset Real
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {J : Type*} [Fintype J]

/-- Each positive cancellation contributes two distinct real interpolation nodes. -/
theorem positive_band_count (F : Finset ℝ) (p t : J → ℝ) (hp : ∀ j, 0≤p j)
    (hm : ∑ j, p j=1) {a b W : ℝ} (hab : a≤b) (hr : ∀ j, t j∈Set.Icc a b)
    (hW : 0≤W) (hf : ∀ w∈F, 0<w ∧ w≤W)
    (hz : ∀ w∈F, ∑ j, (p j:ℂ)*wave w (t j)=0) :
    ((F.card:ℝ)+F.card)*log 2≤(b-a)*W := by
  classical
  let v : F ⊕ F → ℝ := Sum.elim (fun i => i.val) (fun i => -i.val)
  have hi : Function.Injective v := by
    intro i k h
    cases i with
    | inl i =>
      cases k with
      | inl k => exact congrArg Sum.inl (Subtype.ext h)
      | inr k =>
        change i.val= -k.val at h
        linarith only [(hf _ i.property).1,(hf _ k.property).1,h]
    | inr i =>
      cases k with
      | inl k =>
        change -i.val=k.val at h
        linarith only [(hf _ i.property).1,(hf _ k.property).1,h]
      | inr k => exact congrArg Sum.inr (Subtype.ext (neg_injective h))
  have hb (i : F ⊕ F) : |v i|≤W := by
    cases i with
    | inl i => simpa only [v,Sum.elim_inl,abs_of_pos (hf _ i.property).1] using (hf _ i.property).2
    | inr i => simpa only [v,Sum.elim_inr,abs_neg,abs_of_pos (hf _ i.property).1] using (hf _ i.property).2
  have hc (i : F ⊕ F) : ∑ j, (p j:ℂ)*wave (v i) (t j)=0 := by
    cases i with
    | inl i => exact hz _ i.property
    | inr i =>
      have hn (j : J) : conj (wave i.val (t j))=wave (-i.val) (t j) := by
        have h := wave_diff 0 i.val (t j)
        simpa only [wave,zero_mul,Complex.ofReal_zero,Complex.exp_zero,one_mul,zero_sub] using h
      simpa only [map_sum,map_mul,Complex.conj_ofReal,hn,map_zero,v,Sum.elim_inr] using
        congrArg (fun z : ℂ => conj z) (hz _ i.property)
  let e := (Fintype.equivFin (F ⊕ F)).symm
  have h := cancellation_count (v ∘ e) (hi.comp e.injective) p t hp hm hab hr hW
    (fun i => hb (e i)) (fun i => hc (e i))
  simpa only [Fintype.card_sum,Fintype.card_coe,Nat.cast_add] using h

/-- With no restriction on frequency separation, the total half-period
span exceeds that of any positive cancelling clock by at most a harmonic factor. -/
theorem competitive_span (F : Finset ℝ) (p t : J → ℝ) (hp : ∀ j, 0≤p j)
    (hm : ∑ j, p j=1) {a b : ℝ} (hab : a≤b) (hr : ∀ j, t j∈Set.Icc a b)
    (hf : ∀ w∈F, 0<w) (hz : ∀ w∈F, ∑ j, (p j:ℂ)*wave w (t j)=0) :
    ∑ w∈F, π/w ≤ (π*((b-a)/(2*log 2)))*∑ j∈range F.card, 1/((j:ℝ)+1) := by
  classical
  induction F using Finset.strongInduction with
  | H F ih =>
    rcases F.eq_empty_or_nonempty with rfl|hn
    · simp
    let m := F.max' hn
    have hmF : m∈F := F.max'_mem _
    let S := F.erase m
    have hsub : S⊆F := erase_subset _ _
    have hi := ih S (erase_ssubset hmF) (fun w hw => hf w (hsub hw)) (fun w hw => hz w (hsub hw))
    have hmpos := hf m hmF
    have hc := positive_band_count F p t hp hm hab hr hmpos.le (fun w hw => ⟨hf w hw,F.le_max' w hw⟩) hz
    have hsize : S.card+1=F.card := card_erase_add_one hmF
    rw [←hsize,Nat.cast_add,Nat.cast_one] at hc
    have hlog : 0<2*log (2:ℝ) := mul_pos (by norm_num) (log_pos (by norm_num))
    have hj : 0<(S.card:ℝ)+1 := by positivity
    have ht : 1/m ≤ ((b-a)/(2*log 2))*(1/((S.card:ℝ)+1)) := by
      rw [mul_one_div,div_div,div_le_div_iff₀ hmpos (mul_pos hlog hj)]
      linarith only [hc]
    have hprice := mul_le_mul_of_nonneg_left ht pi_pos.le
    rw [mul_one_div,←mul_assoc] at hprice
    rw [←Finset.add_sum_erase F (fun w => π/w) hmF,←hsize,sum_range_succ,mul_add]
    exact (add_le_add hprice hi).trans_eq (add_comm _ _)

/-- The comparison with every competing clock depends only logarithmically
on the number of distinct positive frequencies. -/
theorem competitive_log_span (F : Finset ℝ) (p t : J → ℝ) (hp : ∀ j, 0≤p j)
    (hm : ∑ j, p j=1) {a b : ℝ} (hab : a≤b) (hr : ∀ j, t j∈Set.Icc a b)
    (hf : ∀ w∈F, 0<w) (hz : ∀ w∈F, ∑ j, (p j:ℂ)*wave w (t j)=0) :
    ∑ w∈F, π/w ≤ π*((b-a)/(2*log 2))*(1+log F.card) := by
  apply (competitive_span F p t hp hm hab hr hf hz).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg pi_pos.le (div_nonneg (sub_nonneg.mpr hab)
    (mul_nonneg (by norm_num) (log_nonneg (by norm_num)))))
  rw [←RHTower.Sieve.sum_Icc_one_div_eq_sum_range]
  exact RHTower.Sieve.sum_Icc_one_div_le_one_add_log F.card

#print axioms competitive_log_span
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
