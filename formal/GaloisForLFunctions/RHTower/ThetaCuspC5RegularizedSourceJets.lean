import GaloisForLFunctions.RHTower.ThetaCuspC5RegularizedAction
/-! Exact all-order source jets of the regularized intrinsic action primitives.
The two compact averages retain the complete curvature: their endpoint jets
are fixed by one and two integrations. Reflection identifies every jet with
the actual translated curvature. These identities remove formal-series
assumptions from the inverse-source/clock germ problem. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology
open scoped ContDiff
noncomputable section
local notation "e" => completedCurvatureEven
local notation "c" => thetaCuspLogCurvature
local notation "E" => completedDecayEvenPrimitive
local notation "Q" => thetaCuspReflectedLogAction
local notation "Eb" => curvaturePrimitiveFactor
local notation "Qb" => curvatureActionFactor

private theorem smooth_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) := by
  simpa only [iteratedDeriv_one] using HTGeometry.contDiff_top_iteratedDeriv_real f hf 1
private theorem smooth_at_nat {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) : ContDiffAt ℝ n f 0 :=
  hf.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))

private theorem coordinate_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    deriv (fun t => t*f t)=fun t => f t+t*deriv f t := by
  funext t
  have h := (hasDerivAt_id t).mul ((hf.differentiable (by simp) t).hasDerivAt)
  simpa only [Pi.mul_def,id_eq,one_mul] using h.deriv

/-- Multiplication by the coordinate shifts the actual endpoint jet by one. -/
theorem iteratedDeriv_coordinate_mul_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv (n+1) (fun t => t*f t) 0=(n+1:ℕ)*iteratedDeriv n f 0 := by
  induction n generalizing f with
  | zero => simp only [Nat.zero_add,iteratedDeriv_one,coordinate_deriv hf,zero_mul,add_zero,
      iteratedDeriv_zero,Nat.cast_one,one_mul]
  | succ n ih =>
      rw [iteratedDeriv_succ',coordinate_deriv hf]
      have hc : ContDiff ℝ ∞ (fun t => t*deriv f t) := contDiff_id.mul (smooth_deriv hf)
      have hadd := iteratedDeriv_add (smooth_at_nat hf (n+1)) (smooth_at_nat hc (n+1))
      change iteratedDeriv (n+1) (f+(fun t => t*deriv f t)) 0 = _
      rw [hadd,ih (smooth_deriv hf),←iteratedDeriv_succ']
      push_cast
      ring

/-- Every endpoint jet of the actual first divided primitive is the corresponding
curvature jet divided by its exact integration multiplicity. -/
theorem curvaturePrimitiveFactor_jet (u : ℝ) (n : ℕ) :
    iteratedDeriv n (Eb u) 0=iteratedDeriv n (e u) 0/(n+1:ℕ) := by
  have hd : deriv (E u)=e u := funext fun t => (hasDerivAt_completedDecayEvenPrimitive u t).deriv
  have hf : E u=fun t => t*Eb u t := funext (completedDecayEvenPrimitive_factor u)
  have hh := iteratedDeriv_coordinate_mul_zero (curvaturePrimitiveFactor_smooth u) n
  rw [←hf,iteratedDeriv_succ',hd] at hh
  apply (eq_div_iff (by positivity : ((n+1:ℕ):ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using hh.symm

/-- The triangular average carries the exact two successive integration factors
at every jet order. -/
theorem curvatureActionFactor_jet (u : ℝ) (n : ℕ) :
    iteratedDeriv n (Qb u) 0=2*iteratedDeriv n (e u) 0/((n+1:ℕ)*(n+2:ℕ)) := by
  have hd : deriv (Q u)=fun t => 2*E u t := by
    funext t
    have hh := (hasDerivAt_thetaCuspReflectedLogAction u t).deriv
    rw [hh,completedDecayEvenPrimitive_eq]
    ring
  have hf : Q u=fun t => t*(t*Qb u t) := by
    funext t
    rw [thetaCuspReflectedLogAction_factor u t]
    ring
  have hc : ContDiff ℝ ∞ (fun t => t*Qb u t) := contDiff_id.mul (curvatureActionFactor_smooth u)
  have hh := iteratedDeriv_coordinate_mul_zero hc (n+1)
  have hi := iteratedDeriv_coordinate_mul_zero (curvatureActionFactor_smooth u) n
  rw [←hf,iteratedDeriv_succ',hd,iteratedDeriv_const_mul_field,
    iteratedDeriv_succ',show deriv (E u)=e u from funext fun t => (hasDerivAt_completedDecayEvenPrimitive u t).deriv,
    hi] at hh
  apply (eq_div_iff (by positivity : (((n+1:ℕ):ℝ)*((n+2:ℕ):ℝ)) ≠ 0)).mpr
  convert! hh.symm using 1
  push_cast
  ring

private theorem curvature_smooth : ContDiff ℝ ∞ c := by
  unfold thetaCuspLogCurvature
  exact (HTGeometry.contDiff_top_iteratedDeriv_real thetaCuspLogSource contDiff_thetaCuspLogSource 2).neg

/-- Exact parity and translated source identification of all reflected-curvature jets. -/
theorem completedCurvatureEven_jet_zero (u : ℝ) (n : ℕ) :
    iteratedDeriv n (e u) 0=(1+(-1:ℝ)^n)*iteratedDeriv n c u/2 := by
  have hp : ContDiff ℝ ∞ (fun t : ℝ => c (u+t)) := curvature_smooth.comp (contDiff_const.add contDiff_id)
  have hm : ContDiff ℝ ∞ (fun t : ℝ => c (u-t)) := curvature_smooth.comp (contDiff_const.sub contDiff_id)
  have he : e u=fun t => (1/2:ℝ)*(c (u+t)+c (u-t)) := by
    funext t
    unfold completedCurvatureEven
    ring
  rw [he,iteratedDeriv_const_mul_field]
  have hh := iteratedDeriv_add (smooth_at_nat hp n) (smooth_at_nat hm n)
  simp only [Pi.add_def] at hh
  rw [hh,iteratedDeriv_comp_const_add,iteratedDeriv_comp_const_sub]
  simp only [add_zero,sub_zero,smul_eq_mul]
  ring

end
end RHTower.ThetaCuspDefect
