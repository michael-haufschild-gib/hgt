import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.UnivariateSublevel

/-! # Gaussian sublevel bounds at points with a resolved polynomial derivative -/

open Polynomial MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open private standard_gaussian_le_volume from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.UnivariateSublevel
noncomputable section

/-- A large logarithmic derivative forces a nearby root, with multiplicity
entering only through the polynomial degree. -/
theorem near_root_of_derivative (P : ℂ[X]) (z : ℂ) {r : ℝ} (hr : 0<r)
    (h : (P.natDegree:ℝ)*‖P.eval z‖<r*‖P.derivative.eval z‖) :
    ∃ b∈P.roots, ‖z-b‖≤r := by
  classical
  by_cases hp : P=0
  · simp [hp] at h
  by_cases hz : P.eval z=0
  · exact ⟨z,(mem_roots hp).mpr hz,by simpa only [sub_self,norm_zero] using hr.le⟩
  by_contra! hfar
  let L := P.roots.map (fun b => (1:ℂ)/(z-b))
  have hsum : ‖L.sum‖≤(P.natDegree:ℝ)/r := by
    apply (norm_multiset_sum_le _).trans
    have hbound (x) (hx : x∈L.map (fun w => ‖w‖)) : x≤1/r := by
      obtain ⟨w,hw,rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := Multiset.mem_map.mp hw
      rw [norm_div,norm_one]
      exact one_div_le_one_div_of_le hr (hfar b hb).le
    have hh := Multiset.sum_le_card_nsmul _ (1/r) hbound
    simpa only [L,Multiset.card_map,←(IsAlgClosed.splits P).natDegree_eq_card_roots,
      nsmul_eq_mul,mul_one_div] using hh
  have he := (IsAlgClosed.splits P).eval_derivative_eq_eval_mul_sum hz
  change P.derivative.eval z=P.eval z*L.sum at he
  rw [he,norm_mul] at h
  have hb := (le_div_iff₀ hr).mp hsum
  nlinarith only [h,mul_le_mul_of_nonneg_right hb (norm_nonneg (P.eval z))]

/-- The Gaussian cost is linear in radius when the derivative resolves
the uncertainty. This holds for every polynomial, regardless of its coefficients. -/
theorem gaussian_resolved_sublevel (P : ℂ[X]) {r : ℝ} (hr : 0<r) :
    (gaussianReal 0 1).real {x : ℝ | (P.natDegree:ℝ)*‖P.eval (x:ℂ)‖<
      r*‖P.derivative.eval (x:ℂ)‖} ≤ 2*P.natDegree*r := by
  classical
  let R := P.roots.toFinset
  let I (b : R) := Icc (b.val.re-r) (b.val.re+r)
  have hs : {x : ℝ | (P.natDegree:ℝ)*‖P.eval (x:ℂ)‖<r*‖P.derivative.eval (x:ℂ)‖} ⊆ ⋃ b : R, I b := by
    intro x hx
    obtain ⟨b,hb,hd⟩ := near_root_of_derivative P (x:ℂ) hr hx
    have hδ := (Complex.abs_re_le_norm ((x:ℂ)-b)).trans hd
    change |x-b.re|≤r at hδ
    obtain ⟨hl,hu⟩ := abs_le.mp hδ
    refine mem_iUnion.mpr ⟨⟨b,Multiset.mem_toFinset.mpr hb⟩,?_⟩
    exact ⟨by change b.re-r≤x; linarith only [hl],by change x≤b.re+r; linarith only [hu]⟩
  have hI (b : R) : (gaussianReal 0 1).real (I b)≤2*r := by
    have hh := ENNReal.toReal_mono (measure_Icc_lt_top.ne) (standard_gaussian_le_volume (I b))
    change _ ≤ volume.real (I b) at hh
    refine hh.trans_eq ?_
    change volume.real (Icc (b.val.re-r) (b.val.re+r))=2*r
    rw [Real.volume_real_Icc_of_le (by linarith only [hr])]
    ring
  have hcard : (R.card:ℝ)≤P.natDegree := by exact_mod_cast P.roots.toFinset_card_le.trans P.card_roots'
  calc
    _ ≤ _ := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ ∑ b : R, (gaussianReal 0 1).real (I b) := measureReal_iUnion_fintype_le I
    _ ≤ ∑ _b : R, 2*r := Finset.sum_le_sum fun b _ => hI b
    _ = R.card*(2*r) := by simp
    _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right hcard hr.le]

#print axioms gaussian_resolved_sublevel
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
