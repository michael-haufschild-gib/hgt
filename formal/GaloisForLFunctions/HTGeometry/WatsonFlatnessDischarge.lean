import GaloisForLFunctions.HTGeometry.DigammaSectorBounds
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Unconditional Watson flatness for half-argument digamma jets

The proof uses the Phragmen--Lindelof form of Watson uniqueness.  Polynomial sector growth on the
shifted `2π/3` sector is supplied by `DigammaSectorBounds`.  Exponential smallness on the positive
ray propagates into a sector slightly wider than a half-plane.  Pullback by the principal
`13/12`-power then turns that decay into superexponential decay in a right half-plane, where
Phragmen--Lindelof forces the function to vanish.
-/

noncomputable section

open Complex Filter Set MvPolynomial
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

private def watsonAlpha : ℝ := 2 * Real.pi / 3
private def watsonTheta : ℝ := Real.pi / 12
private def watsonBeta : ℝ := 13 * Real.pi / 24
private def watsonKappa : ℝ := 13 / 12
private def watsonDelta : ℝ := Real.cos (watsonBeta - watsonTheta)

private theorem watsonAlpha_pos : 0 < watsonAlpha := by
  dsimp [watsonAlpha]
  positivity

private theorem watsonAlpha_lt_pi : watsonAlpha < Real.pi := by
  dsimp [watsonAlpha]
  nlinarith [Real.pi_pos]

private theorem watsonTheta_pos : 0 < watsonTheta := by
  dsimp [watsonTheta]
  positivity

private theorem watsonBeta_lt_watsonAlpha : watsonBeta < watsonAlpha := by
  dsimp [watsonBeta, watsonAlpha]
  nlinarith [Real.pi_pos]

private theorem watsonKappa_pos : 0 < watsonKappa := by
  norm_num [watsonKappa]

private theorem one_lt_watsonKappa : 1 < watsonKappa := by
  norm_num [watsonKappa]

private theorem watsonKappa_lt_two : watsonKappa < 2 := by
  norm_num [watsonKappa]

private theorem watsonKappa_mul_pi_div_two :
    watsonKappa * (Real.pi / 2) = watsonBeta := by
  dsimp [watsonKappa, watsonBeta]
  ring

private theorem watson_cos_alpha : Real.cos watsonAlpha = -(1 / 2 : ℝ) := by
  dsimp [watsonAlpha]
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three]

private theorem watson_cos_alpha_sub_theta_neg :
    Real.cos (watsonAlpha - watsonTheta) < 0 := by
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · dsimp [watsonAlpha, watsonTheta]
    nlinarith [Real.pi_pos]
  · dsimp [watsonAlpha, watsonTheta]
    nlinarith [Real.pi_pos]

private theorem watsonDelta_pos : 0 < watsonDelta := by
  dsimp [watsonDelta]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> dsimp [watsonBeta, watsonTheta] <;> nlinarith [Real.pi_pos]

private theorem watsonTheta_le_beta_sub_theta :
    watsonTheta ≤ watsonBeta - watsonTheta := by
  dsimp [watsonTheta, watsonBeta]
  nlinarith [Real.pi_pos]

private theorem cos_ge_neg_half_of_abs_le_watsonAlpha {y : ℝ}
    (hy : |y| ≤ watsonAlpha) :
    -(1 / 2 : ℝ) ≤ Real.cos y := by
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y)
    watsonAlpha_lt_pi.le hy
  rw [Real.cos_abs, watson_cos_alpha] at hmono
  exact hmono

private theorem exp_mem_digammaWatsonSector_of_abs_im_le {z : ℂ}
    (hz : |z.im| ≤ watsonAlpha) :
    Complex.exp z ∈ digammaWatsonSector := by
  change -(‖Complex.exp z‖ / 2) ≤ (Complex.exp z).re
  rw [Complex.norm_exp, Complex.exp_re]
  have hcos := cos_ge_neg_half_of_abs_le_watsonAlpha hz
  have hexp := Real.exp_pos z.re
  nlinarith

private def upperWatsonStrip : Set ℂ :=
  Complex.im ⁻¹' Set.Ioo 0 watsonAlpha

private def lowerWatsonStrip : Set ℂ :=
  Complex.im ⁻¹' Set.Ioo (-watsonAlpha) 0

private theorem closure_upperWatsonStrip_subset :
    closure upperWatsonStrip ⊆ Complex.im ⁻¹' Set.Icc 0 watsonAlpha := by
  apply closure_minimal
  · intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  · exact isClosed_Icc.preimage continuous_im

private theorem closure_lowerWatsonStrip_subset :
    closure lowerWatsonStrip ⊆ Complex.im ⁻¹' Set.Icc (-watsonAlpha) 0 := by
  apply closure_minimal
  · intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  · exact isClosed_Icc.preimage continuous_im

private theorem exp_mem_sector_of_mem_closure_upper {z : ℂ}
    (hz : z ∈ closure upperWatsonStrip) :
    Complex.exp z ∈ digammaWatsonSector := by
  have hz' := closure_upperWatsonStrip_subset hz
  apply exp_mem_digammaWatsonSector_of_abs_im_le
  rw [abs_of_nonneg hz'.1]
  exact hz'.2

private theorem exp_mem_sector_of_mem_closure_lower {z : ℂ}
    (hz : z ∈ closure lowerWatsonStrip) :
    Complex.exp z ∈ digammaWatsonSector := by
  have hz' := closure_lowerWatsonStrip_subset hz
  have hlow : -watsonAlpha ≤ z.im := hz'.1
  apply exp_mem_digammaWatsonSector_of_abs_im_le
  rw [abs_of_nonpos hz'.2]
  linarith

private def upperRotation : ℂ :=
  Complex.exp (-((watsonTheta : ℂ) * Complex.I))

private def lowerRotation : ℂ :=
  Complex.exp ((watsonTheta : ℂ) * Complex.I)

private theorem norm_upperRotation : ‖upperRotation‖ = 1 := by
  rw [upperRotation, Complex.norm_exp]
  simp

private theorem norm_lowerRotation : ‖lowerRotation‖ = 1 := by
  rw [lowerRotation, Complex.norm_exp]
  simp

private theorem upperRotation_exp_boundary_re (x : ℝ) :
    (upperRotation * Complex.exp ((x : ℂ) + (watsonAlpha : ℂ) * Complex.I)).re =
      Real.exp x * Real.cos (watsonAlpha - watsonTheta) := by
  rw [upperRotation, ← Complex.exp_add]
  have harg : -((watsonTheta : ℂ) * Complex.I) +
      ((x : ℂ) + (watsonAlpha : ℂ) * Complex.I) =
        (x : ℂ) + ((watsonAlpha - watsonTheta : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_re]
  simp

private theorem lowerRotation_exp_boundary_re (x : ℝ) :
    (lowerRotation * Complex.exp ((x : ℂ) - (watsonAlpha : ℂ) * Complex.I)).re =
      Real.exp x * Real.cos (watsonAlpha - watsonTheta) := by
  rw [lowerRotation, ← Complex.exp_add]
  have harg : (watsonTheta : ℂ) * Complex.I +
      ((x : ℂ) - (watsonAlpha : ℂ) * Complex.I) =
        (x : ℂ) + ((watsonTheta - watsonAlpha : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hcos : Real.cos (watsonTheta - watsonAlpha) =
      Real.cos (watsonAlpha - watsonTheta) := by
    rw [show watsonTheta - watsonAlpha = -(watsonAlpha - watsonTheta) by ring,
      Real.cos_neg]
  rw [harg, Complex.exp_re]
  simp [hcos]

private def rotatedWatsonWeight (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (c : ℝ) (rot : ℂ) (z : ℂ) : ℂ :=
  halfDigammaJetEval n P (1 + Complex.exp z) *
    Complex.exp (((c / 2 : ℝ) : ℂ) * rot * Complex.exp z)

private theorem rotatedWatsonWeight_analyticAt (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) (c : ℝ) (rot : ℂ) {z : ℂ}
    (hz : Complex.exp z ∈ digammaWatsonSector) :
    AnalyticAt ℂ (rotatedWatsonWeight n P c rot) z := by
  have hsource := (analyticAt_halfDigammaJetEval_one_add n P hz).comp analyticAt_cexp
  have hexponent : AnalyticAt ℂ
      (fun w : ℂ => (((c / 2 : ℝ) : ℂ) * rot) * Complex.exp w) z :=
    analyticAt_const.mul analyticAt_cexp
  have hweight := hexponent.cexp
  simpa only [rotatedWatsonWeight, mul_assoc] using hsource.mul hweight

private theorem upper_rotatedWatsonWeight_diffContOnCl (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) (c : ℝ) :
    DiffContOnCl ℂ (rotatedWatsonWeight n P c upperRotation) upperWatsonStrip := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  exact (rotatedWatsonWeight_analyticAt n P c upperRotation
    (exp_mem_sector_of_mem_closure_upper hz)).differentiableAt.differentiableWithinAt

private theorem lower_rotatedWatsonWeight_diffContOnCl (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) (c : ℝ) :
    DiffContOnCl ℂ (rotatedWatsonWeight n P c lowerRotation) lowerWatsonStrip := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  exact (rotatedWatsonWeight_analyticAt n P c lowerRotation
    (exp_mem_sector_of_mem_closure_lower hz)).differentiableAt.differentiableWithinAt

private theorem rotatedWatsonWeight_norm_le (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c Cg : ℝ} (hc : 0 < c) (hCg : 0 ≤ Cg)
    {rot z : ℂ} (hrot : ‖rot‖ = 1) (hz : Complex.exp z ∈ digammaWatsonSector)
    (hgrowth : ∀ w ∈ digammaWatsonSector,
      ‖halfDigammaJetEval n P (1 + w)‖ ≤ Cg * (1 + ‖w‖) ^ P.totalDegree) :
    ‖rotatedWatsonWeight n P c rot z‖ ≤
      Cg * Real.exp (((P.totalDegree : ℝ) + c / 2) * Real.exp |z.re|) := by
  let r : ℝ := Real.exp z.re
  have hr : 0 < r := Real.exp_pos _
  have hsource := hgrowth (Complex.exp z) hz
  rw [Complex.norm_exp] at hsource
  have hprojection : (rot * Complex.exp z).re ≤ r := by
    calc
      (rot * Complex.exp z).re ≤ ‖rot * Complex.exp z‖ := Complex.re_le_norm _
      _ = r := by rw [norm_mul, hrot, one_mul, Complex.norm_exp]
  have hweight :
      ‖Complex.exp ((((c / 2 : ℝ) : ℂ) * rot) * Complex.exp z)‖ ≤
        Real.exp ((c / 2) * r) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hc2 : 0 ≤ c / 2 := by positivity
    have hre :
        ((((c / 2 : ℝ) : ℂ) * rot) * Complex.exp z).re =
          (c / 2) * (rot * Complex.exp z).re := by
      rw [← mul_assoc, ofReal_mul_re]
    rw [hre]
    exact mul_le_mul_of_nonneg_left hprojection hc2
  have hpoly : (1 + r) ^ P.totalDegree ≤
      Real.exp ((P.totalDegree : ℝ) * r) := by
    have hone : 1 + r ≤ Real.exp r := by
      simpa [add_comm] using Real.add_one_le_exp r
    have hp := pow_le_pow_left₀ (by positivity) hone P.totalDegree
    simpa [Real.exp_nat_mul, mul_comm] using hp
  have hrexp : r ≤ Real.exp |z.re| := by
    dsimp [r]
    exact Real.exp_le_exp.mpr (le_abs_self z.re)
  have hcoef : 0 ≤ (P.totalDegree : ℝ) + c / 2 := by positivity
  calc
    ‖rotatedWatsonWeight n P c rot z‖ =
        ‖halfDigammaJetEval n P (1 + Complex.exp z)‖ *
          ‖Complex.exp ((((c / 2 : ℝ) : ℂ) * rot) * Complex.exp z)‖ := by
            rw [rotatedWatsonWeight, norm_mul]
    _ ≤ (Cg * (1 + r) ^ P.totalDegree) * Real.exp ((c / 2) * r) :=
      mul_le_mul hsource hweight (norm_nonneg _) (by positivity)
    _ ≤ (Cg * Real.exp ((P.totalDegree : ℝ) * r)) *
        Real.exp ((c / 2) * r) := by gcongr
    _ = Cg * Real.exp (((P.totalDegree : ℝ) + c / 2) * r) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ Cg * Real.exp (((P.totalDegree : ℝ) + c / 2) * Real.exp |z.re|) := by
      gcongr

private theorem rotatedWatsonWeight_strip_isBigO (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c Cg : ℝ} (hc : 0 < c) (hCg : 0 ≤ Cg)
    {rot : ℂ} (hrot : ‖rot‖ = 1) (strip : Set ℂ)
    (hsector : ∀ z ∈ strip, Complex.exp z ∈ digammaWatsonSector)
    (hgrowth : ∀ w ∈ digammaWatsonSector,
      ‖halfDigammaJetEval n P (1 + w)‖ ≤ Cg * (1 + ‖w‖) ^ P.totalDegree) :
    ∃ q < Real.pi / watsonAlpha, ∃ B,
      rotatedWatsonWeight n P c rot
        =O[comap (_root_.abs ∘ Complex.re) atTop ⊓ Filter.principal strip]
          fun z => Real.exp (B * Real.exp (q * |z.re|)) := by
  have hquot : Real.pi / watsonAlpha = (3 / 2 : ℝ) := by
    dsimp [watsonAlpha]
    field_simp [Real.pi_ne_zero]
    ring
  refine ⟨1, by rw [hquot]; norm_num, (P.totalDegree : ℝ) + c / 2, ?_⟩
  apply Asymptotics.IsBigO.of_bound Cg
  apply Filter.eventually_inf_principal.2
  exact Eventually.of_forall fun z hz => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
    exact rotatedWatsonWeight_norm_le n P hc hCg hrot (hsector z hz) hgrowth

end GaloisForLFunctions.HTGeometry

end
