import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.InverseTime
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.GaussianSlab

/-! # One lifted winding at all dates under a Gaussian field increment -/

open MeasureTheory ProbabilityTheory Finset WithLp
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
noncomputable section

/-- A single dual test prices the entire date interval. The deterministic center
may be any real packet; the independent field enters through its local slopes. -/
theorem winding_price {I J : Type*} [Fintype I] [Fintype J] (Q : I → J → ℝ)
    (A b w : J → ℝ) (η d x T U : ℝ) (hη : η≠0) (hd : 0<d) (hx : 0≤x) (hT : 0<T)
    (hw : (∑ j, w j)=0) (hb : (∑ j, w j*b j)=0)
    (hm : 0<∑ i, (∑ j, w j*Q i j)^2)
    (hsize : d^2*(∑ j, |w j|)^2 ≤ ∑ i, (∑ j, w j*Q i j)^2) :
    (Measure.pi fun _ : I => gaussianReal 0 1).real
      {g | windingWindow (fun j => A j+η*∑ i, g i*Q i j) b x T U} ≤ x/(T*|η| * d) := by
  let m (i : I) := ∑ j, w j*Q i j
  let v (i : I) := η*m i
  let L := ∑ j, |w j|
  let σ := ‖toLp 2 m‖
  have hσ₂ : σ^2=∑ i, m i^2 := EuclideanSpace.real_norm_sq_eq (toLp 2 m)
  have hσ : 0<σ := by
    have hn : 0≤σ := norm_nonneg _
    nlinarith only [hσ₂,hm,hn]
  have hL : 0≤L := sum_nonneg fun j _ => abs_nonneg _
  have hnorm : ‖toLp 2 v‖=|η| * σ := by
    change ‖η • (toLp 2 m : EuclideanSpace ℝ I)‖=|η| * σ
    rw [norm_smul,Real.norm_eq_abs]
  have hv : 0<‖toLp 2 v‖ := hnorm ▸ mul_pos (abs_pos.mpr hη) hσ
  have hcut : d*L≤σ := by
    apply (sq_le_sq₀ (mul_nonneg hd.le hL) hσ.le).mp
    simpa only [mul_pow,hσ₂] using hsize
  let a := ∑ j, w j*A j
  let δ := (x/2)*L/T
  have hδ : 0≤δ := div_nonneg (mul_nonneg (div_nonneg hx zero_le_two) hL) hT.le
  apply (measureReal_mono (s₂:={g : I → ℝ | |a+∑ i, g i*v i|≤δ}) ?_ (measure_ne_top _ _)).trans
    (le_trans (affine_slab_price v a δ hδ hv) ?_)
  · intro g hg
    have ht := winding_test _ b w hT.le hw hb hg
    have hid : (∑ j, w j*(A j+η*∑ i, g i*Q i j))=a+∑ i, g i*v i := by
      rw [show (∑ j, w j*(A j+η*∑ i, g i*Q i j))=a+∑ j, ∑ i, w j*(η*(g i*Q i j)) by
        simp only [a,mul_add,mul_sum,sum_add_distrib]]
      congr 1
      rw [sum_comm]
      exact sum_congr rfl fun i _ => by
        simp only [v,m,mul_sum]
        exact sum_congr rfl fun j _ => by ring
    rw [hid,mul_comm T] at ht
    exact (le_div_iff₀ hT).mpr ht
  · rw [hnorm]
    apply (div_le_div_iff₀ (mul_pos (abs_pos.mpr hη) hσ) (mul_pos (mul_pos hT (abs_pos.mpr hη)) hd)).mpr
    calc
      2*δ*(T*|η| * d) = (x*|η|)*(d*L) := by dsimp only [δ]; field_simp
      _ ≤ (x*|η|)*σ := mul_le_mul_of_nonneg_left hcut (mul_nonneg hx (abs_nonneg _))
      _ = _ := mul_assoc ..

#print axioms winding_price
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
