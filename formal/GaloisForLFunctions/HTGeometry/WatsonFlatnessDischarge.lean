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
  change AnalyticAt ℂ (fun w : ℂ =>
    halfDigammaJetEval n P (1 + Complex.exp w) *
      Complex.exp ((((c / 2 : ℝ) : ℂ) * rot) * Complex.exp w)) z
  simpa only [Function.comp_apply] using! hsource.mul hweight

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
      rw [mul_assoc]
      simp [Complex.mul_re]
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
      rw [mul_assoc, ← Real.exp_add]
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
  refine ⟨1, by rw [hquot]; norm_num, (P.totalDegree : ℝ) + c / 2, ?_⟩
  apply Asymptotics.IsBigO.of_bound Cg
  apply Filter.eventually_inf_principal.2
  exact Eventually.of_forall fun z hz => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
    exact rotatedWatsonWeight_norm_le n P hc hCg hrot (hsector z hz) hgrowth

private theorem exists_one_add_pow_mul_exp_neg_bound (d : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 0 ≤ r →
      (1 + r) ^ d * Real.exp (-b * r) ≤ M := by
  have ht0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) b hb
  have hshift := ht0.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have ht : Tendsto
      (fun r : ℝ => (1 + r) ^ d * Real.exp (-b * r)) atTop (nhds 0) := by
    have hmul := hshift.const_mul (Real.exp b)
    convert hmul using 1
    · funext r
      simp only [Function.comp_apply, id_eq, Real.rpow_natCast]
      calc
        (1 + r) ^ d * Real.exp (-b * r) =
            (1 + r) ^ d * (Real.exp b * Real.exp (-b * (1 + r))) := by
          rw [← Real.exp_add]
          congr 2
          ring
        _ = Real.exp b * ((1 + r) ^ d * Real.exp (-b * (1 + r))) := by ring
    · simp
  have hevlt : ∀ᶠ r : ℝ in atTop,
      (1 + r) ^ d * Real.exp (-b * r) < 1 :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨R, hR⟩ := eventually_atTop.mp hevlt
  let R₀ : ℝ := max R 0
  let M : ℝ := max 1 ((1 + R₀) ^ d)
  refine ⟨M, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro r hr
  by_cases hlarge : R ≤ r
  · exact (hR r hlarge).le.trans (le_max_left _ _)
  · have hrR : r ≤ R₀ := by
      dsimp [R₀]
      exact le_max_of_le_left (le_of_not_ge hlarge)
    have hpow : (1 + r) ^ d ≤ (1 + R₀) ^ d := by gcongr
    have hexp : Real.exp (-b * r) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) hr)
    calc
      (1 + r) ^ d * Real.exp (-b * r) ≤ (1 + R₀) ^ d * 1 :=
        mul_le_mul hpow hexp (by positivity) (by positivity)
      _ ≤ M := by simp [M]

private theorem exists_real_boundary_rotatedWatsonWeight_bound (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c Cg : ℝ} (hc : 0 < c) (hCg : 0 ≤ Cg)
    {rot : ℂ} (hrot : ‖rot‖ = 1)
    (hgrowth : ∀ w ∈ digammaWatsonSector,
      ‖halfDigammaJetEval n P (1 + w)‖ ≤ Cg * (1 + ‖w‖) ^ P.totalDegree)
    (hO : (fun σ : ℝ => halfDigammaJetEval n P σ)
      =O[atTop] fun σ => Real.exp (-c * σ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ,
      ‖rotatedWatsonWeight n P c rot x‖ ≤ M := by
  obtain ⟨K, hK, hKO⟩ := hO.exists_nonneg
  obtain ⟨S, hS⟩ := eventually_atTop.mp hKO.bound
  let T : ℝ := max S 1
  let M₀ : ℝ := Cg * T ^ P.totalDegree * Real.exp ((c / 2) * T)
  let M : ℝ := max K M₀
  have hT : 1 ≤ T := le_max_right _ _
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro x
  let r : ℝ := Real.exp x
  have hr : 0 < r := Real.exp_pos _
  have hsector : (r : ℂ) ∈ digammaWatsonSector := by
    change -(‖(r : ℂ)‖ / 2) ≤ ((r : ℂ)).re
    simp [Complex.norm_real, Real.norm_of_nonneg hr.le]
    nlinarith
  have hweight :
      ‖Complex.exp ((((c / 2 : ℝ) : ℂ) * rot) * Complex.exp (x : ℂ))‖ ≤
        Real.exp ((c / 2) * r) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hprojection : (rot * Complex.exp (x : ℂ)).re ≤ r := by
      calc
        (rot * Complex.exp (x : ℂ)).re ≤ ‖rot * Complex.exp (x : ℂ)‖ :=
          Complex.re_le_norm _
        _ = r := by rw [norm_mul, hrot, one_mul, Complex.norm_exp]; simp [r]
    have hre : ((((c / 2 : ℝ) : ℂ) * rot) * Complex.exp (x : ℂ)).re =
        (c / 2) * (rot * Complex.exp (x : ℂ)).re := by
      rw [mul_assoc]
      simp [Complex.mul_re]
    rw [hre]
    exact mul_le_mul_of_nonneg_left hprojection (by positivity)
  have hexpreal : Complex.exp (x : ℂ) = (r : ℂ) := by
    dsimp [r]
    exact (Complex.ofReal_exp x).symm
  rw [hexpreal] at hweight
  rw [rotatedWatsonWeight, norm_mul, hexpreal]
  by_cases hfar : S ≤ 1 + r
  · have hsource := hS (1 + r) hfar
    have hsource' : ‖halfDigammaJetEval n P (1 + (r : ℂ))‖ ≤
        K * Real.exp (-c * (1 + r)) := by
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hsource
    have htotal :
        (K * Real.exp (-c * (1 + r))) * Real.exp ((c / 2) * r) ≤ K := by
      rw [mul_assoc, ← Real.exp_add]
      have hexp : Real.exp (-c * (1 + r) + c / 2 * r) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hcr : 0 ≤ c * r := mul_nonneg hc.le hr.le
        norm_num only [Real.exp_zero]
        nlinarith
      simpa using mul_le_mul_of_nonneg_left hexp hK
    have hmain := (mul_le_mul hsource' hweight (norm_nonneg _) (by positivity)).trans htotal
    exact hmain.trans (by
      show K ≤ M
      dsimp [M]
      exact le_max_left _ _)
  · have hsmall : 1 + r ≤ T := by
      have : 1 + r < S := lt_of_not_ge hfar
      exact this.le.trans (le_max_left _ _)
    have hrT : r ≤ T := by linarith
    have hsource := hgrowth (r : ℂ) hsector
    simp only [Complex.norm_real, Real.norm_of_nonneg hr.le] at hsource
    have hpow : (1 + r) ^ P.totalDegree ≤ T ^ P.totalDegree := by gcongr
    have hexp : Real.exp ((c / 2) * r) ≤ Real.exp ((c / 2) * T) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hrT (by positivity)
    have htotal :
        (Cg * (1 + r) ^ P.totalDegree) * Real.exp ((c / 2) * r) ≤ M₀ := by
      dsimp [M₀]
      gcongr
    have hmain := (mul_le_mul hsource hweight (norm_nonneg _) (by positivity)).trans htotal
    exact hmain.trans (by
      show M₀ ≤ M
      dsimp [M]
      exact le_max_right _ _)

private theorem exists_outer_boundary_rotatedWatsonWeight_bound (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c Cg : ℝ} (hc : 0 < c) (hCg : 0 ≤ Cg)
    {rot : ℂ} (boundary : ℝ → ℂ)
    (hboundary_re : ∀ x, (boundary x).re = x)
    (hboundary_sector : ∀ x, Complex.exp (boundary x) ∈ digammaWatsonSector)
    (hprojection : ∀ x,
      (rot * Complex.exp (boundary x)).re =
        Real.exp x * Real.cos (watsonAlpha - watsonTheta))
    (hgrowth : ∀ w ∈ digammaWatsonSector,
      ‖halfDigammaJetEval n P (1 + w)‖ ≤ Cg * (1 + ‖w‖) ^ P.totalDegree) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ,
      ‖rotatedWatsonWeight n P c rot (boundary x)‖ ≤ M := by
  let b : ℝ := -(c / 2 * Real.cos (watsonAlpha - watsonTheta))
  have hb : 0 < b := by
    dsimp [b]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg (by positivity) watson_cos_alpha_sub_theta_neg)
  obtain ⟨M₀, hM₀, hbound⟩ :=
    exists_one_add_pow_mul_exp_neg_bound P.totalDegree hb
  let M : ℝ := Cg * M₀
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro x
  let r : ℝ := Real.exp x
  have hr : 0 < r := Real.exp_pos _
  have hsource := hgrowth (Complex.exp (boundary x)) (hboundary_sector x)
  have hnormexp : ‖Complex.exp (boundary x)‖ = r := by
    rw [Complex.norm_exp, hboundary_re]
  rw [hnormexp] at hsource
  have hweight :
      ‖Complex.exp ((((c / 2 : ℝ) : ℂ) * rot) * Complex.exp (boundary x))‖ =
        Real.exp (-b * r) := by
    rw [Complex.norm_exp]
    have hre : ((((c / 2 : ℝ) : ℂ) * rot) * Complex.exp (boundary x)).re =
        (c / 2) * (rot * Complex.exp (boundary x)).re := by
      rw [mul_assoc]
      simp [Complex.mul_re]
    rw [hre, hprojection]
    apply congrArg Real.exp
    dsimp [b, r]
    ring
  have htail := hbound r hr.le
  rw [rotatedWatsonWeight, norm_mul, hweight]
  calc
    ‖halfDigammaJetEval n P (1 + Complex.exp (boundary x))‖ * Real.exp (-b * r)
        ≤ (Cg * (1 + r) ^ P.totalDegree) * Real.exp (-b * r) :=
      mul_le_mul_of_nonneg_right hsource (by positivity)
    _ = Cg * ((1 + r) ^ P.totalDegree * Real.exp (-b * r)) := by ring
    _ ≤ Cg * M₀ := mul_le_mul_of_nonneg_left htail hCg
    _ = M := rfl

private def upperBoundary (x : ℝ) : ℂ :=
  (x : ℂ) + (watsonAlpha : ℂ) * Complex.I

private def lowerBoundary (x : ℝ) : ℂ :=
  (x : ℂ) - (watsonAlpha : ℂ) * Complex.I

private theorem upperBoundary_re (x : ℝ) : (upperBoundary x).re = x := by
  simp [upperBoundary]

private theorem lowerBoundary_re (x : ℝ) : (lowerBoundary x).re = x := by
  simp [lowerBoundary]

private theorem exp_upperBoundary_mem_sector (x : ℝ) :
    Complex.exp (upperBoundary x) ∈ digammaWatsonSector := by
  apply exp_mem_digammaWatsonSector_of_abs_im_le
  simp only [upperBoundary, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add,
    add_zero, abs_of_nonneg watsonAlpha_pos.le, le_refl]

private theorem exp_lowerBoundary_mem_sector (x : ℝ) :
    Complex.exp (lowerBoundary x) ∈ digammaWatsonSector := by
  apply exp_mem_digammaWatsonSector_of_abs_im_le
  simp only [lowerBoundary, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_sub, abs_neg,
    add_zero, abs_of_nonneg watsonAlpha_pos.le, le_refl]

private theorem upperBoundary_projection (x : ℝ) :
    (upperRotation * Complex.exp (upperBoundary x)).re =
      Real.exp x * Real.cos (watsonAlpha - watsonTheta) := by
  exact upperRotation_exp_boundary_re x

private theorem lowerBoundary_projection (x : ℝ) :
    (lowerRotation * Complex.exp (lowerBoundary x)).re =
      Real.exp x * Real.cos (watsonAlpha - watsonTheta) := by
  exact lowerRotation_exp_boundary_re x

private theorem exists_upper_rotatedWatsonWeight_bound (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c : ℝ} (hc : 0 < c)
    (hO : (fun σ : ℝ => halfDigammaJetEval n P σ)
      =O[atTop] fun σ => Real.exp (-c * σ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.im → z.im ≤ watsonAlpha →
      ‖rotatedWatsonWeight n P c upperRotation z‖ ≤ C := by
  obtain ⟨Cg, hCg, hgrowth⟩ := exists_halfDigammaJetEval_one_add_norm_le n P
  obtain ⟨Cr, hCr, hreal⟩ :=
    exists_real_boundary_rotatedWatsonWeight_bound n P hc hCg norm_upperRotation hgrowth hO
  obtain ⟨Co, hCo, houter⟩ :=
    exists_outer_boundary_rotatedWatsonWeight_bound n P hc hCg upperBoundary
      upperBoundary_re exp_upperBoundary_mem_sector upperBoundary_projection hgrowth
  let C : ℝ := max Cr Co
  have hB := rotatedWatsonWeight_strip_isBigO n P hc hCg norm_upperRotation
    upperWatsonStrip (fun z hz => exp_mem_sector_of_mem_closure_upper (subset_closure hz)) hgrowth
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro z hz0 hzα
  apply PhragmenLindelof.horizontal_strip
      (f := rotatedWatsonWeight n P c upperRotation)
      (a := 0) (b := watsonAlpha) (C := C)
      (upper_rotatedWatsonWeight_diffContOnCl n P c)
      (by simpa [upperWatsonStrip] using hB)
  · intro w hw
    have hweq : w = (w.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hw]
    rw [hweq]
    exact (hreal w.re).trans (by dsimp [C]; exact le_max_left _ _)
  · intro w hw
    have hweq : w = upperBoundary w.re := by
      apply Complex.ext
      · simp [upperBoundary]
      · simp [upperBoundary, hw]
    rw [hweq]
    exact (houter w.re).trans (by dsimp [C]; exact le_max_right _ _)
  · exact hz0
  · exact hzα

private theorem exists_lower_rotatedWatsonWeight_bound (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c : ℝ} (hc : 0 < c)
    (hO : (fun σ : ℝ => halfDigammaJetEval n P σ)
      =O[atTop] fun σ => Real.exp (-c * σ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, -watsonAlpha ≤ z.im → z.im ≤ 0 →
      ‖rotatedWatsonWeight n P c lowerRotation z‖ ≤ C := by
  obtain ⟨Cg, hCg, hgrowth⟩ := exists_halfDigammaJetEval_one_add_norm_le n P
  obtain ⟨Cr, hCr, hreal⟩ :=
    exists_real_boundary_rotatedWatsonWeight_bound n P hc hCg norm_lowerRotation hgrowth hO
  obtain ⟨Co, hCo, houter⟩ :=
    exists_outer_boundary_rotatedWatsonWeight_bound n P hc hCg lowerBoundary
      lowerBoundary_re exp_lowerBoundary_mem_sector lowerBoundary_projection hgrowth
  let C : ℝ := max Cr Co
  have hB := rotatedWatsonWeight_strip_isBigO n P hc hCg norm_lowerRotation
    lowerWatsonStrip (fun z hz => exp_mem_sector_of_mem_closure_lower (subset_closure hz)) hgrowth
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro z hzα hz0
  apply PhragmenLindelof.horizontal_strip
      (f := rotatedWatsonWeight n P c lowerRotation)
      (a := -watsonAlpha) (b := 0) (C := C)
      (lower_rotatedWatsonWeight_diffContOnCl n P c)
      (by
        have hquot : Real.pi / (0 - -watsonAlpha) = Real.pi / watsonAlpha := by ring_nf
        simpa [lowerWatsonStrip, hquot] using hB)
  · intro w hw
    have hweq : w = lowerBoundary w.re := by
      apply Complex.ext
      · simp [lowerBoundary]
      · simp [lowerBoundary, hw]
    rw [hweq]
    exact (houter w.re).trans (by dsimp [C]; exact le_max_right _ _)
  · intro w hw
    have hweq : w = (w.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hw]
    rw [hweq]
    exact (hreal w.re).trans (by dsimp [C]; exact le_max_left _ _)
  · exact hzα
  · exact hz0

private theorem exists_upper_log_sector_decay (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c : ℝ} (hc : 0 < c)
    (hO : (fun σ : ℝ => halfDigammaJetEval n P σ)
      =O[atTop] fun σ => Real.exp (-c * σ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → 0 ≤ z.arg → z.arg ≤ watsonAlpha →
      ‖halfDigammaJetEval n P (1 + z)‖ ≤
        C * Real.exp (-(c / 2) * (upperRotation * z).re) := by
  obtain ⟨C, hC, hbound⟩ := exists_upper_rotatedWatsonWeight_bound n P hc hO
  refine ⟨C, hC, ?_⟩
  intro z hz0 harg0 hargα
  let w : ℂ := Complex.log z
  have hwim : w.im = z.arg := by simp [w, Complex.log_im]
  have hwbound := hbound w (by rw [hwim]; exact harg0) (by rw [hwim]; exact hargα)
  have hexplog : Complex.exp w = z := by simpa [w] using Complex.exp_log hz0
  have hnormweight :
      ‖Complex.exp ((((c / 2 : ℝ) : ℂ) * upperRotation) * z)‖ =
        Real.exp ((c / 2) * (upperRotation * z).re) := by
    rw [Complex.norm_exp]
    have hre : ((((c / 2 : ℝ) : ℂ) * upperRotation) * z).re =
        (c / 2) * (upperRotation * z).re := by
      rw [mul_assoc]
      simp [Complex.mul_re]
    rw [hre]
  rw [rotatedWatsonWeight, norm_mul, hexplog, hnormweight] at hwbound
  have hpos : 0 < Real.exp ((c / 2) * (upperRotation * z).re) := Real.exp_pos _
  have hdiv := (le_div_iff₀ hpos).2 hwbound
  calc
    ‖halfDigammaJetEval n P (1 + z)‖
        ≤ C / Real.exp ((c / 2) * (upperRotation * z).re) := hdiv
    _ = C * Real.exp (-(c / 2) * (upperRotation * z).re) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring

private theorem exists_lower_log_sector_decay (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c : ℝ} (hc : 0 < c)
    (hO : (fun σ : ℝ => halfDigammaJetEval n P σ)
      =O[atTop] fun σ => Real.exp (-c * σ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → -watsonAlpha ≤ z.arg → z.arg ≤ 0 →
      ‖halfDigammaJetEval n P (1 + z)‖ ≤
        C * Real.exp (-(c / 2) * (lowerRotation * z).re) := by
  obtain ⟨C, hC, hbound⟩ := exists_lower_rotatedWatsonWeight_bound n P hc hO
  refine ⟨C, hC, ?_⟩
  intro z hz0 hargα harg0
  let w : ℂ := Complex.log z
  have hwim : w.im = z.arg := by simp [w, Complex.log_im]
  have hwbound := hbound w (by rw [hwim]; exact hargα) (by rw [hwim]; exact harg0)
  have hexplog : Complex.exp w = z := by simpa [w] using Complex.exp_log hz0
  have hnormweight :
      ‖Complex.exp ((((c / 2 : ℝ) : ℂ) * lowerRotation) * z)‖ =
        Real.exp ((c / 2) * (lowerRotation * z).re) := by
    rw [Complex.norm_exp]
    have hre : ((((c / 2 : ℝ) : ℂ) * lowerRotation) * z).re =
        (c / 2) * (lowerRotation * z).re := by
      rw [mul_assoc]
      simp [Complex.mul_re]
    rw [hre]
  rw [rotatedWatsonWeight, norm_mul, hexplog, hnormweight] at hwbound
  have hpos : 0 < Real.exp ((c / 2) * (lowerRotation * z).re) := Real.exp_pos _
  have hdiv := (le_div_iff₀ hpos).2 hwbound
  calc
    ‖halfDigammaJetEval n P (1 + z)‖
        ≤ C / Real.exp ((c / 2) * (lowerRotation * z).re) := hdiv
    _ = C * Real.exp (-(c / 2) * (lowerRotation * z).re) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring

private theorem watsonBeta_lt_pi : watsonBeta < Real.pi :=
  watsonBeta_lt_watsonAlpha.trans watsonAlpha_lt_pi

private theorem upperRotation_re : upperRotation.re = Real.cos watsonTheta := by
  rw [upperRotation, Complex.exp_re]
  simp [Real.cos_neg]

private theorem upperRotation_im : upperRotation.im = -Real.sin watsonTheta := by
  rw [upperRotation, Complex.exp_im]
  simp [Real.sin_neg]

private theorem lowerRotation_re : lowerRotation.re = Real.cos watsonTheta := by
  rw [lowerRotation, Complex.exp_re]
  simp

private theorem lowerRotation_im : lowerRotation.im = Real.sin watsonTheta := by
  rw [lowerRotation, Complex.exp_im]
  simp

private theorem arg_cpow_watsonKappa {w : ℂ} (hw0 : w ≠ 0) (hwre : 0 ≤ w.re) :
    (w ^ (watsonKappa : ℂ)).arg = w.arg * watsonKappa := by
  have hargabs : |w.arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr hwre
  have hphiLower : -Real.pi < w.arg * watsonKappa := by
    have hargLower : -(Real.pi / 2) ≤ w.arg := (abs_le.mp hargabs).1
    have : -watsonBeta ≤ w.arg * watsonKappa := by
      rw [← watsonKappa_mul_pi_div_two]
      nlinarith [watsonKappa_pos]
    exact (neg_lt_neg watsonBeta_lt_pi).trans_le this
  have hphiUpper : w.arg * watsonKappa ≤ Real.pi := by
    have hargUpper : w.arg ≤ Real.pi / 2 := (abs_le.mp hargabs).2
    have : w.arg * watsonKappa ≤ watsonBeta := by
      rw [← watsonKappa_mul_pi_div_two]
      nlinarith [watsonKappa_pos]
    exact this.trans watsonBeta_lt_pi.le
  rw [Complex.cpow_ofReal]
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
    (Complex.arg_mul_cos_add_sin_mul_I
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr hw0) watsonKappa)
      ⟨hphiLower, hphiUpper⟩)

private theorem upperRotation_cpow_re (w : ℂ) :
    (upperRotation * w ^ (watsonKappa : ℂ)).re =
      ‖w‖ ^ watsonKappa * Real.cos (w.arg * watsonKappa - watsonTheta) := by
  rw [Complex.mul_re, upperRotation_re, upperRotation_im,
    Complex.cpow_ofReal_re, Complex.cpow_ofReal_im, Real.cos_sub]
  ring

private theorem lowerRotation_cpow_re (w : ℂ) :
    (lowerRotation * w ^ (watsonKappa : ℂ)).re =
      ‖w‖ ^ watsonKappa * Real.cos (w.arg * watsonKappa + watsonTheta) := by
  rw [Complex.mul_re, lowerRotation_re, lowerRotation_im,
    Complex.cpow_ofReal_re, Complex.cpow_ofReal_im, Real.cos_add]
  ring

private theorem upperRotation_cpow_re_lower {w : ℂ}
    (hwre : 0 ≤ w.re) (hwim : 0 ≤ w.im) :
    watsonDelta * ‖w‖ ^ watsonKappa ≤
      (upperRotation * w ^ (watsonKappa : ℂ)).re := by
  have hargabs : |w.arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr hwre
  have harg0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hwim
  have hargUpper : w.arg ≤ Real.pi / 2 := (abs_le.mp hargabs).2
  let u : ℝ := w.arg * watsonKappa - watsonTheta
  have huUpper : u ≤ watsonBeta - watsonTheta := by
    dsimp [u]
    rw [← watsonKappa_mul_pi_div_two]
    nlinarith [watsonKappa_pos]
  have huLower : -(watsonBeta - watsonTheta) ≤ u := by
    dsimp [u]
    nlinarith [watsonTheta_le_beta_sub_theta, watsonKappa_pos]
  have huabs : |u| ≤ watsonBeta - watsonTheta := abs_le.mpr ⟨huLower, huUpper⟩
  have hcos : watsonDelta ≤ Real.cos u := by
    have hangle : watsonBeta - watsonTheta ≤ Real.pi := by
      dsimp [watsonBeta, watsonTheta]
      nlinarith [Real.pi_pos]
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg u)
      hangle huabs
    rw [Real.cos_abs] at hmono
    exact hmono
  rw [upperRotation_cpow_re]
  dsimp [u] at hcos
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right hcos
      (Real.rpow_nonneg (norm_nonneg w) watsonKappa))

private theorem lowerRotation_cpow_re_lower {w : ℂ}
    (hwre : 0 ≤ w.re) (hwim : w.im < 0) :
    watsonDelta * ‖w‖ ^ watsonKappa ≤
      (lowerRotation * w ^ (watsonKappa : ℂ)).re := by
  have hargabs : |w.arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr hwre
  have harg0 : w.arg < 0 := Complex.arg_neg_iff.mpr hwim
  have hargLower : -(Real.pi / 2) ≤ w.arg := (abs_le.mp hargabs).1
  let u : ℝ := w.arg * watsonKappa + watsonTheta
  have huLower : -(watsonBeta - watsonTheta) ≤ u := by
    dsimp [u]
    rw [← watsonKappa_mul_pi_div_two]
    nlinarith [watsonKappa_pos]
  have huUpper : u ≤ watsonBeta - watsonTheta := by
    dsimp [u]
    nlinarith [watsonTheta_le_beta_sub_theta, watsonKappa_pos]
  have huabs : |u| ≤ watsonBeta - watsonTheta := abs_le.mpr ⟨huLower, huUpper⟩
  have hcos : watsonDelta ≤ Real.cos u := by
    have hangle : watsonBeta - watsonTheta ≤ Real.pi := by
      dsimp [watsonBeta, watsonTheta]
      nlinarith [Real.pi_pos]
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg u)
      hangle huabs
    rw [Real.cos_abs] at hmono
    exact hmono
  rw [lowerRotation_cpow_re]
  dsimp [u] at hcos
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right hcos
      (Real.rpow_nonneg (norm_nonneg w) watsonKappa))

private theorem exists_cpow_rightHalfPlane_decay (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c : ℝ} (hc : 0 < c)
    (hO : (fun σ : ℝ => halfDigammaJetEval n P σ)
      =O[atTop] fun σ => Real.exp (-c * σ)) :
    ∃ C d : ℝ, 0 ≤ C ∧ 0 < d ∧ ∀ w : ℂ, 0 ≤ w.re → w ≠ 0 →
      ‖halfDigammaJetEval n P (1 + w ^ (watsonKappa : ℂ))‖ ≤
        C * Real.exp (-d * ‖w‖ ^ watsonKappa) := by
  obtain ⟨Cu, hCu, hu⟩ := exists_upper_log_sector_decay n P hc hO
  obtain ⟨Cl, hCl, hl⟩ := exists_lower_log_sector_decay n P hc hO
  let C : ℝ := max Cu Cl
  let d : ℝ := (c / 2) * watsonDelta
  have hd : 0 < d := mul_pos (by positivity) watsonDelta_pos
  refine ⟨C, d, by dsimp [C]; positivity, hd, ?_⟩
  intro w hwre hw0
  have harg := arg_cpow_watsonKappa hw0 hwre
  have hcpow0 : w ^ (watsonKappa : ℂ) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero
      (Complex.ofReal_ne_zero.mpr watsonKappa_pos.ne')).2 hw0
  by_cases hwim : 0 ≤ w.im
  · have harg0 : 0 ≤ (w ^ (watsonKappa : ℂ)).arg := by
      rw [harg]
      exact mul_nonneg (Complex.arg_nonneg_iff.mpr hwim) watsonKappa_pos.le
    have hargα : (w ^ (watsonKappa : ℂ)).arg ≤ watsonAlpha := by
      rw [harg]
      have hargUpper := (abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hwre)).2
      have hbeta : w.arg * watsonKappa ≤ watsonBeta := by
        rw [← watsonKappa_mul_pi_div_two]
        nlinarith [watsonKappa_pos]
      exact hbeta.trans watsonBeta_lt_watsonAlpha.le
    have hraw := hu (w ^ (watsonKappa : ℂ))
      hcpow0 harg0 hargα
    have hproj := upperRotation_cpow_re_lower hwre hwim
    have hexp : Real.exp (-(c / 2) *
        (upperRotation * w ^ (watsonKappa : ℂ)).re) ≤
        Real.exp (-d * ‖w‖ ^ watsonKappa) := by
      apply Real.exp_le_exp.mpr
      dsimp [d]
      nlinarith [mul_pos (show 0 < c / 2 by positivity) watsonDelta_pos]
    have hCuC : Cu ≤ C := by dsimp [C]; exact le_max_left _ _
    exact hraw.trans <| (mul_le_mul_of_nonneg_left hexp hCu).trans <|
      mul_le_mul_of_nonneg_right hCuC (Real.exp_nonneg _)
  · have hwim' : w.im < 0 := lt_of_not_ge hwim
    have harg0 : (w ^ (watsonKappa : ℂ)).arg ≤ 0 := by
      rw [harg]
      exact mul_nonpos_of_nonpos_of_nonneg (Complex.arg_neg_iff.mpr hwim').le
        watsonKappa_pos.le
    have hargα : -watsonAlpha ≤ (w ^ (watsonKappa : ℂ)).arg := by
      rw [harg]
      have hargLower := (abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hwre)).1
      have hbeta : -watsonBeta ≤ w.arg * watsonKappa := by
        rw [← watsonKappa_mul_pi_div_two]
        nlinarith [watsonKappa_pos]
      exact (neg_le_neg watsonBeta_lt_watsonAlpha.le).trans hbeta
    have hraw := hl (w ^ (watsonKappa : ℂ))
      hcpow0 hargα harg0
    have hproj := lowerRotation_cpow_re_lower hwre hwim'
    have hexp : Real.exp (-(c / 2) *
        (lowerRotation * w ^ (watsonKappa : ℂ)).re) ≤
        Real.exp (-d * ‖w‖ ^ watsonKappa) := by
      apply Real.exp_le_exp.mpr
      dsimp [d]
      nlinarith [mul_pos (show 0 < c / 2 by positivity) watsonDelta_pos]
    have hClC : Cl ≤ C := by dsimp [C]; exact le_max_right _ _
    exact hraw.trans <| (mul_le_mul_of_nonneg_left hexp hCl).trans <|
      mul_le_mul_of_nonneg_right hClC (Real.exp_nonneg _)

private def watsonCpowPullback (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (w : ℂ) : ℂ :=
  halfDigammaJetEval n P (1 + w ^ (watsonKappa : ℂ))

private theorem cpow_watsonKappa_mem_sector {w : ℂ} (hwre : 0 ≤ w.re) :
    w ^ (watsonKappa : ℂ) ∈ digammaWatsonSector := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp [digammaWatsonSector, watsonKappa_pos.ne']
  have hargabs : |w.arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr hwre
  have hphiabs : |w.arg * watsonKappa| ≤ watsonAlpha := by
    rw [abs_mul, abs_of_pos watsonKappa_pos]
    have hbeta : |w.arg| * watsonKappa ≤ watsonBeta := by
      rw [← watsonKappa_mul_pi_div_two]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_right hargabs watsonKappa_pos.le)
    exact hbeta.trans watsonBeta_lt_watsonAlpha.le
  have hcos := cos_ge_neg_half_of_abs_le_watsonAlpha hphiabs
  change -(‖w ^ (watsonKappa : ℂ)‖ / 2) ≤ (w ^ (watsonKappa : ℂ)).re
  rw [Complex.norm_cpow_real, Complex.cpow_ofReal_re]
  nlinarith [Real.rpow_nonneg (norm_nonneg w) watsonKappa]

private theorem watsonCpowPullback_analyticAt (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ (watsonCpowPullback n P) w := by
  have hcpow : AnalyticAt ℂ (fun z : ℂ => z ^ (watsonKappa : ℂ)) w :=
    analyticAt_id.cpow analyticAt_const (Complex.mem_slitPlane_iff.mpr (Or.inl hw))
  have houter := analyticAt_halfDigammaJetEval_one_add n P
    (cpow_watsonKappa_mem_sector hw.le)
  have hcomp := AnalyticAt.comp (f := fun z : ℂ => z ^ (watsonKappa : ℂ))
    (x := w) houter hcpow
  simpa [watsonCpowPullback, Function.comp_def] using! hcomp

private theorem watsonCpowPullback_diffContOnCl (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    DiffContOnCl ℂ (watsonCpowPullback n P) {w : ℂ | 0 < w.re} := by
  constructor
  · intro w hw
    exact (watsonCpowPullback_analyticAt n P hw).differentiableAt.differentiableWithinAt
  · rw [closure_setOf_lt_re]
    intro w hw
    have hcpow : ContinuousAt (fun z : ℂ => z ^ (watsonKappa : ℂ)) w :=
      Complex.continuousAt_cpow_const_of_re_pos (Or.inl hw) (by
        simp [watsonKappa_pos])
    have houter := (analyticAt_halfDigammaJetEval_one_add n P
      (cpow_watsonKappa_mem_sector hw)).continuousAt
    have hcomp := ContinuousAt.comp
      (f := fun z : ℂ => z ^ (watsonKappa : ℂ)) (x := w) houter hcpow
    simpa [watsonCpowPullback, Function.comp_def] using! hcomp.continuousWithinAt

private theorem exists_watsonCpowPullback_bound (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c : ℝ} (hc : 0 < c)
    (hO : (fun σ : ℝ => halfDigammaJetEval n P σ)
      =O[atTop] fun σ => Real.exp (-c * σ)) :
    ∃ D C d : ℝ, 0 ≤ D ∧ 0 ≤ C ∧ 0 < d ∧
      (∀ w : ℂ, 0 ≤ w.re → ‖watsonCpowPullback n P w‖ ≤ D) ∧
      (∀ w : ℂ, 0 ≤ w.re → w ≠ 0 →
        ‖watsonCpowPullback n P w‖ ≤ C * Real.exp (-d * ‖w‖ ^ watsonKappa)) := by
  obtain ⟨C, d, hC, hd, hdecay⟩ := exists_cpow_rightHalfPlane_decay n P hc hO
  obtain ⟨Cg, hCg, hgrowth⟩ := exists_halfDigammaJetEval_one_add_norm_le n P
  let D : ℝ := max C Cg
  have hzero : ‖watsonCpowPullback n P 0‖ ≤ Cg := by
    have h := hgrowth 0 (by simp [digammaWatsonSector])
    simpa [watsonCpowPullback, watsonKappa_pos.ne'] using h
  have hbounded : ∀ w : ℂ, 0 ≤ w.re → ‖watsonCpowPullback n P w‖ ≤ D := by
    intro w hwre
    rcases eq_or_ne w 0 with rfl | hw0
    · exact hzero.trans (by dsimp [D]; exact le_max_right _ _)
    · have h := hdecay w hwre hw0
      have hexp : Real.exp (-d * ‖w‖ ^ watsonKappa) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le)
          (Real.rpow_nonneg (norm_nonneg w) _)
      have hCe : C * Real.exp (-d * ‖w‖ ^ watsonKappa) ≤ C := by
        simpa using mul_le_mul_of_nonneg_left hexp hC
      have hCD : C ≤ D := by dsimp [D]; exact le_max_left _ _
      exact h.trans (hCe.trans hCD)
  exact ⟨D, C, d, by dsimp [D]; positivity, hC, hd, hbounded, hdecay⟩

private theorem watsonCpowPullback_superpolynomialDecay (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {C d : ℝ} (hC : 0 ≤ C) (hd : 0 < d)
    (hdecay : ∀ w : ℂ, 0 ≤ w.re → w ≠ 0 →
      ‖watsonCpowPullback n P w‖ ≤ C * Real.exp (-d * ‖w‖ ^ watsonKappa)) :
    Asymptotics.SuperpolynomialDecay atTop Real.exp
      (fun x : ℝ => ‖watsonCpowPullback n P x‖) := by
  intro m
  have hratio : Tendsto (fun x : ℝ => d * x ^ (watsonKappa - 1)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr one_lt_watsonKappa)).const_mul_atTop hd
  have hdom : ∀ᶠ x : ℝ in atTop, (m : ℝ) + 1 ≤ d * x ^ (watsonKappa - 1) :=
    hratio.eventually_ge_atTop ((m : ℝ) + 1)
  have hupper : Tendsto (fun x : ℝ => C * Real.exp (-x)) atTop (nhds 0) :=
    by
      simpa [Function.comp_def] using
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul C
  refine squeeze_zero'
    (Eventually.of_forall fun x => mul_nonneg (by positivity) (norm_nonneg _)) ?_ hupper
  filter_upwards [eventually_gt_atTop (0 : ℝ), hdom] with x hx hdx
  have hxpow : x ^ watsonKappa = x * x ^ (watsonKappa - 1) := by
    calc
      x ^ watsonKappa = x ^ (1 + (watsonKappa - 1)) := by
        congr 1
        ring
      _ = x ^ (1 : ℝ) * x ^ (watsonKappa - 1) := by rw [Real.rpow_add hx]
      _ = x * x ^ (watsonKappa - 1) := by rw [Real.rpow_one]
  have hsource := hdecay (x : ℂ) (by simp [hx.le]) (Complex.ofReal_ne_zero.mpr hx.ne')
  have hxnorm : ‖(x : ℂ)‖ ^ watsonKappa = x ^ watsonKappa := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  rw [hxnorm] at hsource
  have hexponent : (m : ℝ) * x - d * x ^ watsonKappa ≤ -x := by
    rw [hxpow]
    have hxmul : ((m : ℝ) + 1) * x ≤ (d * x ^ (watsonKappa - 1)) * x :=
      mul_le_mul_of_nonneg_right hdx hx.le
    nlinarith
  calc
      Real.exp x ^ m * ‖watsonCpowPullback n P (x : ℂ)‖
          ≤ Real.exp x ^ m * (C * Real.exp (-d * x ^ watsonKappa)) :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = C * Real.exp ((m : ℝ) * x - d * x ^ watsonKappa) := by
        rw [← Real.exp_nat_mul]
        calc
          Real.exp ((m : ℝ) * x) * (C * Real.exp (-d * x ^ watsonKappa)) =
              C * (Real.exp ((m : ℝ) * x) * Real.exp (-d * x ^ watsonKappa)) := by ring
          _ = C * Real.exp ((m : ℝ) * x - d * x ^ watsonKappa) := by
            rw [← Real.exp_add]
            congr 2
            ring
      _ ≤ C * Real.exp (-x) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hC

private theorem halfDigammaJetEval_eventually_zero_of_exp_decay (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {c : ℝ} (hc : 0 < c)
    (hO : (fun σ : ℝ => halfDigammaJetEval n P σ)
      =O[atTop] fun σ => Real.exp (-c * σ)) :
    ∀ᶠ σ : ℝ in atTop, halfDigammaJetEval n P σ = 0 := by
  obtain ⟨D, C, d, hD, hC, hd, hbounded, hdecay⟩ :=
    exists_watsonCpowPullback_bound n P hc hO
  have hexp : ∃ q < (2 : ℝ), ∃ B,
      watsonCpowPullback n P
        =O[Bornology.cobounded ℂ ⊓ Filter.principal {w : ℂ | 0 < w.re}]
          fun w => Real.exp (B * ‖w‖ ^ q) := by
    refine ⟨1, by norm_num, 0, ?_⟩
    apply Asymptotics.IsBigO.of_bound D
    apply Filter.eventually_inf_principal.2
    exact Eventually.of_forall fun w hw => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, zero_mul, Real.exp_zero, mul_one]
      exact hbounded w hw.le
  have hsuper := watsonCpowPullback_superpolynomialDecay n P hC hd hdecay
  have him : ∃ B : ℝ, ∀ x : ℝ, ‖watsonCpowPullback n P (x * Complex.I)‖ ≤ B := by
    refine ⟨D, fun x => hbounded _ ?_⟩
    simp
  have hzero := PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay
    (watsonCpowPullback_diffContOnCl n P) hexp hsuper him
  have hreal : ∀ t : ℝ, 0 ≤ t → halfDigammaJetEval n P (1 + t) = 0 := by
    intro t ht
    let x : ℝ := t ^ watsonKappa⁻¹
    have hx : 0 ≤ x := Real.rpow_nonneg ht _
    have hpow : ((x : ℂ) ^ (watsonKappa : ℂ)) = (t : ℂ) := by
      rw [← Complex.ofReal_cpow hx]
      apply Complex.ofReal_inj.mpr
      dsimp [x]
      rw [← Real.rpow_mul ht, inv_mul_cancel₀ watsonKappa_pos.ne', Real.rpow_one]
    have hw := hzero (show (0 : ℝ) ≤ (x : ℂ).re by simpa)
    simpa [watsonCpowPullback, hpow] using hw
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with σ hσ
  have ht : 0 ≤ σ - 1 := sub_nonneg.mpr hσ
  simpa using hreal (σ - 1) ht

/-- **Unconditional Watson flatness.**  An exponentially small differential polynomial in the
half-argument digamma jets vanishes on the far positive real ray. -/
theorem watsonFlatness : WatsonFlatness := by
  intro n P c hc hO
  exact halfDigammaJetEval_eventually_zero_of_exp_decay n P hc hO

/-- **Unconditional quantitative Holder theorem** for half-argument digamma jets. -/
theorem quantitativeHolder : QuantitativeHolder :=
  GaloisForLFunctions.quantitativeHolder_of_watsonFlatness watsonFlatness

end GaloisForLFunctions.HTGeometry

end
