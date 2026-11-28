import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.SitePair
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCouplings.Resampling
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.UnivariateSublevel
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! # Gaussian small-ball bound for the response surviving retiming -/

open MeasureTheory ProbabilityTheory Set Function Polynomial
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
open private standard_gaussian_le_volume from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.UnivariateSublevel
noncomputable section

private theorem quadratic_slice (u v w r : ℝ) (hu : u≠0) (hr : 0≤r) :
    gaussianReal 0 1 {x : ℝ | |u*x^2+v*x+w| < |u| * r^2} ≤ ENNReal.ofReal (4*r) := by
  let P : ℂ[X] := C (u:ℂ)*X^2+C (v:ℂ)*X+C (w:ℂ)
  have hu' : (u:ℂ)≠0 := by exact_mod_cast hu
  have hd : P.natDegree=2 := natDegree_quadratic hu'
  have hl : P.leadingCoeff=(u:ℂ) := leadingCoeff_quadratic hu'
  have hf (x : ℝ) : P.eval (x:ℂ)=((u*x^2+v*x+w:ℝ):ℂ) := by
    simp [P]
  have h := gaussian_polynomial_sublevel P r hr
  simp only [hf,hl,hd,Complex.norm_real,Real.norm_eq_abs,Nat.cast_ofNat] at h
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (h.trans_eq (by ring))

/-- Raw determinant of the adjacent onsite field rotation against the quadratic energy observable. -/
def edgeResponse {n : ℕ} (h : Coeff n) (e : Fin (n+1)) (a b : Fin 3) : ℝ :=
  h (leftSite e a)*squareTrace h (rightSite e b)-h (rightSite e b)*squareTrace h (leftSite e a)

private theorem continuous_edgeResponse {n : ℕ} (e : Fin (n+1)) (a b : Fin 3) :
    Continuous (fun h : Coeff n => edgeResponse h e a b) := by
  have hc : Continuous (fun h : Coeff n => (generator h).val) := by
    simp only [generator,pathHamiltonian_eq_sum]
    fun_prop
  unfold edgeResponse squareTrace Matrix.trace
  fun_prop

/-- For any edge, the normalized trace determinant has sublevel probability at most
six times the cube root of the tolerance divided by two. The constants are independent of
the prefix length and the chosen pair of onsite Pauli axes. -/
theorem gaussian_edge_response {n : ℕ} (e : Fin (n+1)) (a b : Fin 3) (r : ℝ) (hr : 0<r) :
    (fieldLaw n).real {h | |edgeResponse h e a b|<2*(2:ℝ)^(n+2)*r^3} ≤ 6*r := by
  let γ := gaussianReal 0 1
  let μ := fieldLaw n
  let p := leftSite e a
  let l := edgeLabel e a b
  let D := (2:ℝ)^(n+2)
  let S := {h : Coeff n | |edgeResponse h e a b|<2*D*r^3}
  let B := {h : Coeff n | |h l|<r}
  have hS : MeasurableSet S := measurableSet_lt (continuous_edgeResponse e a b).abs.measurable measurable_const
  have hB : MeasurableSet B := measurableSet_lt (measurable_pi_apply l).abs measurable_const
  have hlp : l≠p := Sum.inr_ne_inl
  have hd : 0<D := pow_pos (by norm_num) _
  have hb : μ B ≤ ENNReal.ofReal (2*r) := by
    let I := Ioo (-r) r
    have he : B=(fun h : Coeff n => h l) ⁻¹' I := by
      ext h
      change |h l|<r ↔ -r<h l ∧ h l<r
      exact abs_lt
    rw [he,(measurePreserving_eval (fun _ : PathLabel n => γ) l).measure_preimage measurableSet_Ioo.nullMeasurableSet]
    exact (standard_gaussian_le_volume I).trans (by rw [Real.volume_Ioo]; apply ENNReal.ofReal_le_ofReal; linarith)
  have hpres := PrefixCouplings.resample_preserving γ p
  simp only [Measure.infinitePi_eq_pi] at hpres
  have hs : μ (S \ B) ≤ ENNReal.ofReal (4*r) := by
    rw [←hpres.measure_preimage (hS.diff hB).nullMeasurableSet]
    rw [Measure.prod_apply ((hS.diff hB).preimage hpres.measurable)]
    calc
      _ ≤ ∫⁻ _h : Coeff n, ENNReal.ofReal (4*r) ∂μ := by
        apply lintegral_mono
        intro h
        change γ {x : ℝ | update h p x ∈ S \ B} ≤ _
        by_cases hh : |h l|<r
        · have hem : {x : ℝ | update h p x ∈ S \ B}=∅ := eq_empty_iff_forall_notMem.mpr (by
            intro x hx
            exact hx.2 (by change |update h p x l|<r; rwa [update_of_ne hlp]))
          simp only [hem,measure_empty,zero_le]
        · let u := 2*D*h l
          let y := update h p 0
          let v := squareTrace y (rightSite e b)
          let w := -(h (rightSite e b)*squareTrace y p)
          have hu : u≠0 := mul_ne_zero (mul_ne_zero (by norm_num) hd.ne') (abs_pos.mp (hr.trans_le (le_of_not_gt hh)))
          refine (measure_mono ?_).trans (quadratic_slice u v w r hu hr.le)
          intro x hx
          have he : edgeResponse (update h p x) e a b=u*x^2+v*x+w := by
            simpa only [edgeResponse,u,v,w,y,p,D,l,sub_eq_add_neg] using edge_response_polynomial h e a b x
          have hsmall := hx.1
          change |edgeResponse (update h p x) e a b|<2*D*r^3 at hsmall
          change |u*x^2+v*x+w| < |u| * r^2
          rw [←he]
          apply hsmall.trans_le
          dsimp only [u]
          rw [abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hd.le)]
          calc
            _ = (2*D*r)*r^2 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_of_not_gt hh) (by positivity)) (sq_nonneg r)
      _ = _ := by simp [μ]
  have hm : μ S ≤ ENNReal.ofReal (6*r) := calc
    _ ≤ μ (B ∪ (S \ B)) := measure_mono (fun h hh => by by_cases hB' : h∈B; exact Or.inl hB'; exact Or.inr ⟨hh,hB'⟩)
    _ ≤ _ := measure_union_le ..
    _ ≤ ENNReal.ofReal (2*r)+ENNReal.ofReal (4*r) := add_le_add hb hs
    _ = _ := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hm).trans_eq (ENNReal.toReal_ofReal (by positivity))

#print axioms gaussian_edge_response
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
