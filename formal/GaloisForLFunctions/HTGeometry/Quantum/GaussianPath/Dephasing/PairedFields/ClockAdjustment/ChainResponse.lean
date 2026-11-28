import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.CollectiveResponse
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.EdgeFamily
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.FourthMoment.EnergyBound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.GaussianVariance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.DateTail

/-! # A local field with inverse-square-root angular response on a Gaussian chain -/

open Real Filter MeasureTheory Set Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
open SpectralEdge
open private continuous_edgeResponse from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.GaussianPair
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- A tangent local field of Euclidean norm at most one with the indicated
level-averaged squared response, uniformly over changes of time and global phase. -/
def hasAngularResponse {n : ℕ} (h : Coeff n) (r : ℝ) : Prop :=
  ∃ f : Coeff n, (∑ i, f i^2) ≤ 1 ∧ (∑ i, h i*f i)=0 ∧
    ∀ t φ : ℝ, let E := (generator h).2.isHermitian.eigenvalues
      (2:ℝ)^(n+2)*r^6 ≤ (172*13^3:ℝ)*((n+2:ℕ):ℝ)*∑ j, (localSlope h f j+t*E j+φ)^2

private theorem response_of_total {n : ℕ} (h : Coeff n) (r : ℝ) (hr : 0<r)
    (hv : (∑ i, h i^2) ≤ 13*((n+2:ℕ):ℝ))
    (hm : ((n+1:ℕ):ℝ)*((2:ℝ)^(n+2)*r^3) ≤ ∑ e, |edgeResponse h e 0 1|) :
    hasAngularResponse h r := by
  let K : ℝ := (n+2:ℕ)
  let D := (2:ℝ)^(n+2)
  let H := 13*K
  let R := sqrt H
  let V := ∑ i, h i^2
  let E := (generator h).2.isHermitian.eigenvalues
  have hK : 0<K := Nat.cast_pos.mpr (by omega)
  have hD : 0<D := pow_pos (by norm_num) _
  have hH : 0<H := mul_pos (by norm_num) hK
  have hR : 0<R := sqrt_pos.mpr hH
  have hR₂ : R^2=H := sq_sqrt hH.le
  have hV : 0≤V := sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨g,hperp,hg,hresponse⟩ := collective_field h
  let f (i : PathLabel n) := g i/R
  have hscale (i) : R*f i=g i := by
    dsimp only [f]
    rw [←mul_div_assoc,mul_comm R (g i),mul_div_cancel_right₀ _ hR.ne']
  refine ⟨f,?_,?_,?_⟩
  · simp only [f,div_pow,hR₂,←sum_div]
    rw [div_le_one hH]
    exact hg.trans hv
  · simp only [f,div_eq_mul_inv,←mul_assoc,←sum_mul,hperp,zero_mul]
  · intro t φ
    let Z := ∑ j, (localSlope h f j+t*E j+φ)^2
    have hz : 0≤Z := sum_nonneg fun _ _ => sq_nonneg _
    have hs (j) : localSlope h g j=R*localSlope h f j := by
      simp only [localSlope,mul_sum,←mul_assoc,hscale]
    have he := hresponse (R*t) (R*φ)
    change _ ≤ (∑ j, E j^4)*∑ j, (localSlope h g j+R*t*E j+R*φ)^2 at he
    have hscaled : (∑ j, (localSlope h g j+R*t*E j+R*φ)^2)=H*Z := by
      dsimp only [Z]
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [hs,←hR₂]
      ring
    rw [hscaled] at he
    have hfour := SpectralGapMass.Bulk.FourthMoment.path_fourth_moment (WithLp.toLp 2 h)
    have hdrop : (∑ j, E j^4) ≤ 43*D*V^2 := by
      change (∑ j, E j^4)+42*D*(∑ i, h i^4) ≤ 43*D*V^2 at hfour
      exact (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hD.le)
        (sum_nonneg fun _ _ => by positivity))).trans hfour
    have hvar : V^2≤H^2 := pow_le_pow_left₀ hV hv 2
    have htop := mul_le_mul_of_nonneg_right (hdrop.trans (mul_le_mul_of_nonneg_left hvar
      (mul_nonneg (by norm_num) hD.le))) (mul_nonneg hH.le hz)
    have hmK : K/2 ≤ ((n+1:ℕ):ℝ) := by dsimp only [K]; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) n]
    have hcut := pow_le_pow_left₀ (mul_nonneg (half_pos hK).le (mul_nonneg hD.le (pow_nonneg hr.le 3)))
      ((mul_le_mul_of_nonneg_right hmK (mul_nonneg hD.le (pow_nonneg hr.le 3))).trans hm) 2
    have htotal := hcut.trans (he.trans htop)
    change D*r^6 ≤ (172*13^3:ℝ)*K*Z
    apply le_of_mul_le_mul_left (a:=D*K^2/4) _ (by positivity)
    dsimp only [H] at htotal
    linarith only [htotal]

/-- On a frozen chain, outside one event eventually absent almost surely, failure of
an angular RMS response of order r³/√K has probability at most 12r on every prefix. -/
theorem gaussian_collective_response :
    ∃ B : ℕ → Set PathPauliDisorder, (∀ n, MeasurableSet (B n)) ∧
      (∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω∉B n) ∧
      ∀ (n : ℕ) (r : ℝ), 0<r →
        pathPauliDisorderLaw.real ({ω | ¬hasAngularResponse (fun i => pathPauliDisorderShell ω n i) r} \ B n) ≤ 12*r := by
  let X (n : ℕ) (ω : PathPauliDisorder) : Coeff n := fun i => pathPauliDisorderShell ω n i
  let K (n : ℕ) : ℝ := (n+2:ℕ)
  let B (n : ℕ) := X n ⁻¹' {h : Coeff n | 13*K n<∑ i, h i^2}
  have hB (n) : MeasurableSet (B n) := by
    apply MeasurableSet.preimage _ (BlockDilations.prefix_measure n).measurable
    exact measurableSet_lt measurable_const (Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)
  refine ⟨B,hB,?_,?_⟩
  · filter_upwards [SpectralGapMass.Bulk.gaussian_variance_per_site] with ω hw
    filter_upwards [hw.eventually_lt_const (by norm_num : (12:ℝ)<13)] with n hn
    exact not_lt_of_ge ((div_lt_iff₀ (show 0<K n by dsimp [K]; positivity)).mp hn).le
  · intro n r hr
    let A := {h : Coeff n | (∑ e, |edgeResponse h e 0 1|)<((n+1:ℕ):ℝ)*((2:ℝ)^(n+2)*r^3)}
    have ha : MeasurableSet A := measurableSet_lt (Finset.measurable_fun_sum _ fun e _ =>
      (continuous_edgeResponse e 0 1).abs.measurable) measurable_const
    refine (measureReal_mono (s₂:=X n ⁻¹' A) ?_ (measure_ne_top _ _)).trans ?_
    · rintro ω ⟨hfail,hbound⟩
      by_contra hm
      exact hfail (response_of_total (X n ω) r hr (le_of_not_gt hbound) (le_of_not_gt hm))
    · rw [(BlockDilations.prefix_measure n).measureReal_preimage ha.nullMeasurableSet]
      simpa only [A,fieldLaw,Fintype.card_fin,id_eq] using gaussian_edge_family (n:=n) id (fun _ => 0) (fun _ => 1) r hr

#print axioms gaussian_collective_response
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
