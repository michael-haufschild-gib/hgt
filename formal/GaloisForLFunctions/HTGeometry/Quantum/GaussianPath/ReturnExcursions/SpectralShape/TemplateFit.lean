import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.MomentStability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.MomentPolynomial
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.FourthMoment.EnergyBound
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance

/-! # A fitted winding template determines squared physical skewness -/

open Finset
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
noncomputable section
variable {I : Type*} [Fintype I]

def centered (b : I → ℝ) (i : I) : ℝ := b i-(𝔼 j, b j)

private theorem moment_div (k : ℕ) (b : I → ℝ) (a : ℝ) :
    moment k (fun i => b i/a)=moment k b/a^k := by
  simp only [moment,div_pow,expect_div]

private theorem shape_div (b : I → ℝ) (a : ℝ) (ha : a≠0) :
    shape (fun i => b i/a)=shape b := by
  unfold shape
  rw [moment_div,moment_div]
  by_cases h : moment 2 b=0
  · simp [h]
  · field_simp

private theorem centered_error [Nonempty I] (E b : I → ℝ) (hE : (𝔼 i, E i)=0) (t p x : ℝ)
    (hf : ∀ i, |t*E i-b i-p|≤x) (i : I) : |centered b i-t*E i|≤2*x := by
  have hmean := (abs_expect_le univ (fun j => t*E j-b j-p)).trans
    (expect_le univ_nonempty (fun j _ => hf j))
  rw [expect_sub_distrib,expect_sub_distrib,←mul_expect,hE,mul_zero,zero_sub,Fintype.expect_const] at hmean
  have hdiff := abs_sub_le (t*E i-b i-p) (0:ℝ) (-(𝔼 j, b j)-p)
  simp only [sub_zero,zero_sub,abs_neg] at hdiff
  rw [show centered b i-t*E i=-((t*E i-b i-p)-(-(𝔼 j, b j)-p)) by dsimp only [centered]; ring,abs_neg]
  linarith only [hdiff,hf i,hmean]

/-- A fit at any positive time, allowing an arbitrary common phase and any
permutation of the winding entries, imposes one sextic inequality on the same
physical couplings. Its right side decreases inversely with the fitting time. -/
theorem template_constraint {n : ℕ} (h : PathShell n) (b : (Fin (n+2)→Bool) → ℝ)
    (e : (Fin (n+2)→Bool) ≃ (Fin (n+2)→Bool)) {t p x : ℝ}
    (ht : 0<t) (hR : 0<‖h‖) (hx : 0≤x) (hres : 16*x≤t*‖h‖)
    (hf : ∀ i, |t*(isSelfAdjoint_pathHamiltonian h).isHermitian.eigenvalues i-b (e i)-p|≤x) :
    t*|skewConstraint (shape (centered b)) h|≤16000*x*‖h‖^5 := by
  let R := ‖h‖
  let D := (2:ℝ)^(n+2)
  let E := (isSelfAdjoint_pathHamiltonian h).isHermitian.eigenvalues
  let d := fun i => b (e i)
  let u := fun i => E i/R
  let v := fun i => centered d i/(t*R)
  let δ := 2*x/(t*R)
  have hD : 0<D := pow_pos (by norm_num) _
  have hcard : (Fintype.card (Fin (n+2)→Bool):ℝ)=D := by simp [D]
  obtain ⟨he₁,he₂⟩ := FluxOccupation.path_spectral_moments h
  have hmean : (𝔼 i, E i)=0 := by rw [Fintype.expect_eq_sum_div_card,he₁,zero_div]
  have hv₂ : moment 2 E=R^2 := by
    rw [moment,Fintype.expect_eq_sum_div_card,hcard,he₂,←EuclideanSpace.real_norm_sq_eq]
    push_cast
    exact mul_div_cancel_left₀ _ hD.ne'
  have hv₃ : moment 3 E=thirdMoment h := by
    rw [moment,Fintype.expect_eq_sum_div_card,hcard,sum_pow_eigenvalues_eq_trace_pow_re']
    rfl
  have hv₄ : moment 4 E≤43*R^4 := by
    have hh := SpectralGapMass.Bulk.FourthMoment.path_fourth_moment h
    have hsum : 0≤∑ i, h i^4 := sum_nonneg fun i _ => by positivity
    change (∑ i, E i^4)+42*D*(∑ i, h i^4)≤43*D*(∑ i, h i^2)^2 at hh
    rw [←EuclideanSpace.real_norm_sq_eq] at hh
    rw [moment,Fintype.expect_eq_sum_div_card,hcard,div_le_iff₀ hD]
    change _ ≤ 43*‖h‖^4*D
    linarith only [hh,mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤42) hD.le) hsum]
  have htr : 0<t*R := mul_pos ht hR
  have hδ : δ≤1/8 := (div_le_iff₀ htr).mpr (by linarith only [hres])
  have hfit (i) : |v i-u i|≤δ := by
    have heq : v i-u i=(centered d i-t*E i)/(t*R) := by
      dsimp only [v,u]
      field_simp [ht.ne',hR.ne']
    rw [heq,abs_div,abs_of_pos htr]
    exact div_le_div_of_nonneg_right (centered_error E d hmean t p x hf i) htr.le
  have hu : moment 2 u=1 := by rw [show u=(fun i => E i/R) from rfl,moment_div,hv₂,div_self (pow_ne_zero _ hR.ne')]
  have hu₄ : moment 4 u≤43 := by
    change moment 4 (fun i => E i/R)≤43
    rw [moment_div,div_le_iff₀ (pow_pos hR 4)]
    exact hv₄
  have hh := (shape_stability u v (div_nonneg (by positivity) htr.le) hδ hfit hu hu₄).2
  have hmb : (𝔼 i, d i)=(𝔼 i, b i) := Fintype.expect_equiv e _ _ (fun _ => rfl)
  have hc (k : ℕ) : moment k (centered d)=moment k (centered b) :=
    Fintype.expect_equiv e _ _ (fun i => by dsimp only [centered]; rw [hmb])
  have hsv : shape v=shape (centered b) := by
    change shape (fun i => centered d i/(t*R))=_
    rw [shape_div _ _ htr.ne',shape,shape,hc,hc]
  rw [hsv,show u=(fun i => E i/R) from rfl,moment_div,hv₃] at hh
  have heq : skewConstraint (shape (centered b)) h=
      ((thirdMoment h/R^3)^2-shape (centered b))*R^6 := by
    dsimp only [skewConstraint,R]
    field_simp [hR.ne']
  rw [heq,abs_mul,abs_of_nonneg (pow_nonneg hR.le 6)]
  have hh' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (pow_nonneg hR.le 6)) ht.le
  apply hh'.trans_eq
  dsimp only [δ,R]
  field_simp [ht.ne',hR.ne']
  ring

#print axioms template_constraint
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
