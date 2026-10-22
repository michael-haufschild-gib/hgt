import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMIngoingCoordinates
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuadraticIngoingCorrection

namespace RHTower.D4BMQuadraticIngoingEndpoints
open GaloisForLFunctions.HTGeometry D4BMIngoingCoordinates
open Filter Topology
noncomputable section

/-- The corrected ingoing tensor is polynomial in inverse radius before restoring its envelope. -/
def compactMetric (s u B aS aV S Sx Sy : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let C := aS^(2 : ℕ)*B^(2 : ℕ)*s^(2 : ℕ)*u^(2 : ℕ)*((s+1)^(2 : ℕ)*u^(2 : ℕ)-4)*S^(2 : ℕ)/8
  let V := aS*aV*B^(2 : ℕ)*s*(s+1)*S/2
  let T0 := V*u*(1-u^(2 : ℕ))*Sy
  let T1 := -V*u*(1-u^(2 : ℕ))*Sx
  let R0 := -V*u^(3 : ℕ)*Sy
  let R1 := V*u^(3 : ℕ)*Sx
  fun i j => match i.val, j.val with
    | 0, 1 | 1, 0 => C
    | 0, 2 | 2, 0 => T0
    | 0, 3 | 3, 0 => T1
    | 1, 2 | 2, 1 => R0
    | 1, 3 | 3, 1 => R1
    | _, _ => 0

private def staticMetric (s r B aS aV S Sx Sy : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let C := aS^(2 : ℕ)*B^(2 : ℕ)*s^(2 : ℕ)*((s+1)^(2 : ℕ)-4*r^(2 : ℕ))*S^(2 : ℕ)/(8*r^(4 : ℕ))
  let V := aS*aV*B^(2 : ℕ)*s*(s+1)*(r^(2 : ℕ)-1)*S/(2*r^(3 : ℕ))
  !![0,C,V*Sy,-V*Sx; C,2*C/(r^(2 : ℕ)-1),0,0; V*Sy,0,0,0; -V*Sx,0,0,0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem metric_values (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    (D4BMQuadraticIngoingCorrection.correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy).metric =
      staticMetric s r B aS aV S Sx Sy := by
  let C := (((aS^(2 : ℕ)*s^(2 : ℕ)/8)*B^(2 : ℕ))*((s+1)^(2 : ℕ)+(-4)*(r*r)))*
    ((r⁻¹*r⁻¹)*(r⁻¹*r⁻¹))*(S*S)
  let V := ((((aS*aV*s*(s+1)/2)*B^(2 : ℕ))*(r*r+(-1)))*((r⁻¹*r⁻¹)*r⁻¹))*S
  have hm : (D4BMQuadraticIngoingCorrection.correctionJet
      s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy).metric =
      !![0,C,V*Sy,V*(-Sx); C,(2*C)*(r*r+(-1))⁻¹,0,0;
        V*Sy,0,0,0; V*(-Sx),0,0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hm]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [staticMetric, C, V]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hf]
  all_goals try simp only [true_or]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- Applying the actual coordinate differential to the complete correction jet's metric
removes every singular horizon denominator. -/
theorem metric_pullback (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    pullback r (D4BMQuadraticIngoingCorrection.correctionJet
      s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy).metric =
      compactMetric s r⁻¹ B aS aV S Sx Sy := by
  rw [metric_values _ _ _ _ _ _ _ _ _ _ _ _ _ hr hf]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [pullback, jacobian, Matrix.mul_apply, Fin.sum_univ_succ,
    staticMetric, compactMetric]
  all_goals field_simp [hr, hf]
  all_goals try simp only [true_or]
  all_goals ring

/-- The regular radial field retains the original time and radial branch. -/
def field (s aS aV S Sx Sy : ℂ) (v : ℝ) (u : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  compactMetric s u (compactEnvelope s 1 v u) aS aV S Sx Sy

/-- The regular expression is the actual pullback of the original correction's
metric values, with its physical envelope, at every exterior point. -/
theorem field_eq_pullback (s aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (x : Fin 4 → ℝ) (hr : 1 < x 1) :
    pullback (x 1 : ℂ) (D4BMQuadraticIngoingCorrection.correctionJet s
      (x 1) (x 3) (D4BMFundamentalScalarMetric.envelope s 1 (staticPoint x))
      aS aV S Sx Sy Sxx Sxy Sxxx Sxxy).metric =
      field s aS aV S Sx Sy (x 0) (x 1 : ℂ)⁻¹ := by
  have h0 : (x 1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hr))
  have hf : (x 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (x 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith
    exact_mod_cast h
  rw [metric_pullback _ _ _ _ _ _ _ _ _ _ _ _ _ h0 hf, envelope_staticPoint _ _ _ hr]
  rfl

/-- Every radial derivative of the actual correction extends across the physical horizon. -/
theorem field_contDiffAt (s aS aV S Sx Sy : ℂ) (v : ℝ) (u : ℂ)
    (hu : 1+u ∈ Complex.slitPlane) (m : WithTop ℕ∞) (i j : Fin 4) :
    ContDiffAt ℂ m (fun z => field s aS aV S Sx Sy v z i j) u := by
  have hB := compactEnvelope_contDiffAt s 1 v u hu m
  fin_cases i <;> fin_cases j <;> dsimp [field, compactMetric]
  all_goals fun_prop (disch := assumption)

/-- Exact finite horizon value of every correction component. -/
theorem field_horizon (s aS aV S Sx Sy : ℂ) (v : ℝ) (i j : Fin 4) :
    Tendsto (fun u => field s aS aV S Sx Sy v u i j) (nhds 1)
      (nhds (compactMetric s 1 (Complex.exp (s*((v : ℂ)+Complex.log 2)))
        aS aV S Sx Sy i j)) := by
  simpa [field, compactEnvelope, show (1 : ℂ)+1=2 by norm_num] using
    (field_contDiffAt s aS aV S Sx Sy v 1
      (by norm_num [Complex.mem_slitPlane_iff]) 0 i j).continuousAt.tendsto

/-- Every unnormalized ingoing component vanishes at the asymptotic boundary. -/
theorem field_boundary (s aS aV S Sx Sy : ℂ) (v : ℝ) (i j : Fin 4) :
    Tendsto (fun u => field s aS aV S Sx Sy v u i j) (nhds 0) (nhds 0) := by
  have h := (field_contDiffAt s aS aV S Sx Sy v 0
    (by norm_num [Complex.mem_slitPlane_iff]) 0 i j).continuousAt.tendsto
  have hz : field s aS aV S Sx Sy v 0 = 0 := by
    ext k l
    fin_cases k <;> fin_cases l <;> simp [field, compactMetric]
  simpa only [hz, Matrix.zero_apply] using h

/-- The boundary limit is zero along the original positive physical radius. -/
theorem field_radius_boundary (s aS aV S Sx Sy : ℂ) (v : ℝ) (i j : Fin 4) :
    Tendsto (fun r : ℝ => field s aS aV S Sx Sy v (r : ℂ)⁻¹ i j)
      atTop (nhds 0) := by
  have hi : Tendsto (fun r : ℝ => (r : ℂ)⁻¹) atTop (nhds 0) := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_zero, Function.comp_def] using!
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  exact (field_boundary s aS aV S Sx Sy v i j).comp hi

end
end RHTower.D4BMQuadraticIngoingEndpoints
