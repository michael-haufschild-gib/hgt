import GaloisForLFunctions.RHTower.ThetaCuspC5IntrinsicActionProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
/-! A strict Bose-budget profile obtained from the first nonzero intrinsic-action
correction. Global inverse-source/clock comparison remains open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
local notation "F" => intrinsicActionProfile
local notation "Q" => thetaCuspReflectedLogAction
local notation "E" => completedDecayEvenPrimitive

private theorem positive_from_derivative {f g : ℝ → ℝ} (h0 : f 0=0)
    (hd : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, 0 < x → 0 < g x)
    {x : ℝ} (hx : 0 < x) : 0 < f x := by
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro y _; exact (hd y).continuousAt.continuousWithinAt
    · intro y hy
      rw [(hd y).deriv]
      exact hg y (by simpa only [interior_Ici,mem_Ioi] using hy)
  simpa only [h0] using hm (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) hx.le hx

private theorem sinh_tangent_reserve_pos {x : ℝ} (hx : 0 < x) :
    0 < x*Real.cosh x-Real.sinh x := by
  have hd (y : ℝ) : HasDerivAt (fun z => z*Real.cosh z-Real.sinh z)
      (y*Real.sinh y) y := by
    convert! ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y) using 1
    dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
    ring
  exact positive_from_derivative (by simp) hd
    (fun y hy => mul_pos hy (Real.sinh_pos_iff.mpr hy)) hx

/-- Exact hyperbolic reserve for the quadratic enrichment of the action profile. -/
def enrichedBoseReserve (x : ℝ) : ℝ :=
  (15+4*x^2)*x*Real.cosh x-(15+9*x^2)*Real.sinh x

theorem enrichedBoseReserve_pos {x : ℝ} (hx : 0 < x) : 0 < enrichedBoseReserve x := by
  have hd (y : ℝ) : HasDerivAt enrichedBoseReserve
      (3*y*(y*Real.cosh y-Real.sinh y)+4*y^3*Real.sinh y) y := by
    have h2 := (hasDerivAt_id y).pow 2
    convert! ((((h2.const_mul 4).const_add 15).mul (hasDerivAt_id y)).mul
      (Real.hasDerivAt_cosh y)).sub
        (((h2.const_mul 9).const_add 15).mul (Real.hasDerivAt_sinh y)) using 1
    dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
    ring
  apply positive_from_derivative (by simp [enrichedBoseReserve]) hd _ hx
  intro y hy
  exact add_pos (mul_pos (by positivity) (sinh_tangent_reserve_pos hy))
    (mul_pos (by positivity) (Real.sinh_pos_iff.mpr hy))

private theorem enriched_bose_scalar_pos {q : ℝ} (hq : 0 < q) :
    0 < (1+q^2/15)*(4+8/(Real.exp q-1)-8/q)-2*q/3 := by
  have hr : 0 < Real.exp q-1 := by
    have hh := Real.exp_lt_exp.mpr hq
    rw [Real.exp_zero] at hh
    linarith
  have he : Real.exp q=(Real.exp (q/2))^2 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hh : ((1+q^2/15)*(4+8/(Real.exp q-1)-8/q)-2*q/3)*
      (q*(Real.exp q-1))=(16/15:ℝ)*Real.exp (q/2)*enrichedBoseReserve (q/2) := by
    unfold enrichedBoseReserve
    rw [Real.sinh_eq,Real.cosh_eq,Real.exp_neg]
    field_simp [hq.ne',hr.ne',(Real.exp_pos (q/2)).ne']
    rw [he]
    ring
  have hp := mul_pos (mul_pos (by norm_num : (0:ℝ)<16/15) (Real.exp_pos (q/2)))
    (enrichedBoseReserve_pos (show 0<q/2 by positivity))
  rw [←hh] at hp
  exact (mul_pos_iff_of_pos_right (mul_pos hq hr)).mp hp

/-- The first nonzero correction supplied by the unused intrinsic Bose budget. -/
def enrichedActionProfile (u t : ℝ) : ℝ := F u t*(1+(Q u t)^2/15)

theorem enrichedActionProfile_pos (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < enrichedActionProfile u t := by
  unfold enrichedActionProfile
  exact mul_pos (intrinsicActionProfile_pos u ht) (by positivity)

theorem hasDerivAt_enrichedActionProfile (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (enrichedActionProfile u)
      (F u t*(actionProfileLogRate u t*(1+(Q u t)^2/15)+4*Q u t*E u t/15)) t := by
  have hQ : HasDerivAt (Q u) (2*E u t) t := by
    convert! hasDerivAt_thetaCuspReflectedLogAction u t using 1
    rw [completedDecayEvenPrimitive_eq]
    ring
  convert! (hasDerivAt_intrinsicActionProfile u ht).mul
    (((hQ.pow 2).div_const 15).const_add 1) using 1
  dsimp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
  ring

/-- The enriched profile satisfies the full Bose budget strictly at every positive displacement. -/
theorem enrichedActionProfile_bose_budget (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < (c5CompletedBoseWeight u t-5)*enrichedActionProfile u t-
      5*t*deriv (enrichedActionProfile u) t := by
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  have hE : 0 < E u t := by
    have hh := descentDenominator_pos u ht
    unfold descentDenominator at hh
    exact (mul_pos_iff_of_pos_left ht).mp hh
  have hr : 0 < Real.exp (Q u t)-1 := by
    have hh := Real.exp_lt_exp.mpr hQ
    rw [Real.exp_zero] at hh
    linarith
  have hp := mul_pos (mul_pos (intrinsicActionProfile_pos u ht) (show 0<2*t*E u t by positivity))
    (enriched_bose_scalar_pos hQ)
  rw [(hasDerivAt_enrichedActionProfile u ht).deriv]
  have hid : (c5CompletedBoseWeight u t-5)*enrichedActionProfile u t-
      5*t*(F u t*(actionProfileLogRate u t*(1+(Q u t)^2/15)+4*Q u t*E u t/15))=
      F u t*(2*t*E u t)*((1+(Q u t)^2/15)*
        (4+8/(Real.exp (Q u t)-1)-8/Q u t)-2*Q u t/3) := by
    unfold enrichedActionProfile c5CompletedBoseWeight thetaCuspReflectedActionVelocity actionProfileLogRate
    rw [show thetaCuspReflectedLogJetOne u t=2*E u t by rw [completedDecayEvenPrimitive_eq]; ring]
    field_simp [ht.ne',hQ.ne',hr.ne']
    ring
  rw [hid]
  exact hp

end
end RHTower.ThetaCuspDefect
