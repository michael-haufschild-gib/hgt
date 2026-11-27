import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.HalfPeriods

/-! # Sharp minimum duration of a positive clock cancelling one frequency -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section

/-- A positive clock supported in an open semicircle cannot cancel its
frequency. Two equally weighted dates half a period apart attain equality. -/
theorem half_period_floor {I : Type*} [Fintype I] (p t : I → ℝ) (hp : ∀ i, 0≤p i)
    (hm : ∑ i, p i=1) {w a b : ℝ} (hw : 0<w) (ht : ∀ i, t i∈Set.Icc a b)
    (hc : ∑ i, (p i:ℂ)*wave w (t i)=0) : π≤w*(b-a) := by
  by_contra! hn
  let m := (a+b)/2
  have hzero : ∑ i, (p i:ℂ)*wave w (t i-m)=0 := by
    have h (i : I) : (p i:ℂ)*wave w (t i-m)=((p i:ℂ)*wave w (t i))*wave w (-m) := by
      rw [sub_eq_add_neg,wave_add,mul_assoc]
    simp only [h,←sum_mul,hc,zero_mul]
  have hpos (i : I) : 0<Real.cos (w*(t i-m)) := by
    have hlo := mul_le_mul_of_nonneg_left (ht i).1 hw.le
    have hhi := mul_le_mul_of_nonneg_left (ht i).2 hw.le
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> dsimp only [m] <;> linarith only [hlo,hhi,hn]
  have hread (i : I) : ((p i:ℂ)*wave w (t i-m)).re=p i*Real.cos (w*(t i-m)) := by
    rw [Complex.re_ofReal_mul]
    let x := w*(t i-m)
    change p i*(Complex.exp ((x:ℂ)*Complex.I)).re=p i*Real.cos x
    simp only [Complex.exp_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,sub_zero,mul_one,add_zero,Real.exp_zero,one_mul]
  have he := congrArg Complex.re hzero
  simp only [Complex.re_sum,hread,Complex.zero_re] at he
  obtain ⟨i,hi⟩ : ∃ i, 0<p i := by
    by_contra! hall
    have hh : ∑ i, p i≤0 := sum_nonpos (fun j _ => hall j)
    linarith only [hh,hm]
  exact (Finset.sum_pos' (fun j _ => mul_nonneg (hp j) (hpos j).le)
    ⟨i,mem_univ _,mul_pos hi (hpos i)⟩).ne' he

/-- Some sampled date attains at least the average. Discontinuous
observables, including circuit-event indicators, are allowed. -/
theorem exists_sample_ge (ws : List ℝ) (f : ℝ → ℂ) (a : ℝ) :
    ∃ t∈Set.Icc a (a+length ws), (average ws f a).re≤(f t).re := by
  induction ws generalizing a with
  | nil => exact ⟨a,⟨le_rfl,by simp [length]⟩,le_rfl⟩
  | cons w ws ih =>
    let h := π/|w|
    have hh : 0≤h := div_nonneg pi_pos.le (abs_nonneg _)
    have hlen : length (w::ws)=h+length ws := rfl
    change ∃ t∈_, ((average ws f a+average ws f (a+h))/2).re≤(f t).re
    rw [show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.div_ofReal_re,Complex.add_re]
    rcases le_total (average ws f a).re (average ws f (a+h)).re with h'|h'
    · obtain ⟨t,ht,hv⟩ := ih (a+h)
      refine ⟨t,⟨(le_add_of_nonneg_right hh).trans ht.1,ht.2.trans_eq (by rw [hlen,add_assoc])⟩,?_⟩
      linarith only [h',hv]
    · obtain ⟨t,ht,hv⟩ := ih a
      refine ⟨t,⟨ht.1,ht.2.trans (by rw [hlen]; linarith only [hh])⟩,?_⟩
      linarith only [h',hv]

#print axioms half_period_floor
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
