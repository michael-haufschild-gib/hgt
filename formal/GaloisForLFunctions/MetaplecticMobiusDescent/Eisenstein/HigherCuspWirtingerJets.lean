import GaloisForLFunctions.HTGeometry.ComplexAnalysis.AntiholomorphicJets
import GaloisForLFunctions.HTGeometry.SmoothTruncation
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.CuspAveragesAndBesselMellin

/-!
# Pure Wirtinger jets under cusp inversion

Centered cusp inversion differs from its conjugate-affine part by `|z|²` times a smooth map.
Smooth composition preserves this divisibility, so every pure antiholomorphic jet at the center
is the corresponding holomorphic jet at the inverse center, multiplied by the expected power
of the conjugate-linear coefficient.
-/

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology
open HTGeometry

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
noncomputable section

/-- The constant vertical and conjugate-affine horizontal part of inverse cusp coordinates. -/
def inverseCuspAffine (c d : ℂ) (v : ℝ) (z : ℂ) : ℝ × ℂ :=
  (1 / (‖c‖ ^ 2 * v), -d / c + (-1 / (c ^ 2 * (v : ℂ) ^ 2)) * conj z)

/-- The smooth coefficient of the squared-norm error in inverse cusp coordinates. -/
def inverseCuspRemainder (c : ℂ) (v : ℝ) (z : ℂ) : ℝ × ℂ :=
  (-1 / (‖c‖ ^ 2 * v * (v ^ 2 + Complex.normSq z)),
    conj z / (c ^ 2 * (v : ℂ) ^ 2 * ((v ^ 2 + Complex.normSq z : ℝ) : ℂ)))

lemma contDiff_inverseCuspAffine (c d : ℂ) (v : ℝ) :
    ContDiff ℝ ∞ (inverseCuspAffine c d v) :=
  contDiff_const.prodMk
    (contDiff_const.add (contDiff_const.mul Complex.conjCLE.contDiff))

private lemma contDiff_cusp_normSq : ContDiff ℝ ∞ (Complex.normSq : ℂ → ℝ) := by
  change ContDiff ℝ ∞ (fun z : ℂ => z.re * z.re + z.im * z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

lemma contDiff_inverseCuspRemainder (c : ℂ) (v : ℝ) (hc : c ≠ 0) (hv : 0 < v) :
    ContDiff ℝ ∞ (inverseCuspRemainder c v) := by
  have hq : ContDiff ℝ ∞ (fun z => v ^ 2 + Complex.normSq z) :=
    contDiff_const.add contDiff_cusp_normSq
  have hq0 (z : ℂ) : v ^ 2 + Complex.normSq z ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) (Complex.normSq_nonneg z))
  have hc0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hr : ContDiff ℝ ∞ (fun z : ℂ =>
      -1 / (‖c‖ ^ 2 * v * (v ^ 2 + Complex.normSq z))) := by
    exact contDiff_const.div (contDiff_const.mul hq) (fun z =>
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)) hv.ne') (hq0 z))
  have hz : ContDiff ℝ ∞ (fun z : ℂ => conj z) := Complex.conjCLE.contDiff
  have hi : ContDiff ℝ ∞ (fun z : ℂ => conj z /
      (c ^ 2 * (v : ℂ) ^ 2 * ((v ^ 2 + Complex.normSq z : ℝ) : ℂ))) := by
    have hrec : ContDiff ℝ ∞ (fun z : ℂ => (1 : ℝ) / (v ^ 2 + Complex.normSq z)) :=
      contDiff_const.div hq hq0
    have heq : (fun z : ℂ => conj z /
        (c ^ 2 * (v : ℂ) ^ 2 * ((v ^ 2 + Complex.normSq z : ℝ) : ℂ))) =
        fun z => (1 / (c ^ 2 * (v : ℂ) ^ 2)) * conj z *
          (((1 : ℝ) / (v ^ 2 + Complex.normSq z) : ℝ) : ℂ) := by
      funext z
      change conj z / (c ^ 2 * (v : ℂ) ^ 2 * ((v ^ 2 + Complex.normSq z : ℝ) : ℂ)) =
        (1 / (c ^ 2 * (v : ℂ) ^ 2)) * conj z *
          (((1 : ℝ) / (v ^ 2 + Complex.normSq z) : ℝ) : ℂ)
      rw [Complex.ofReal_div, Complex.ofReal_one]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    exact (contDiff_const.mul hz).mul (Complex.ofRealCLM.contDiff.comp hrec)
  exact hr.prodMk hi

/-- The nonlinear part of cusp inversion has an exact squared-norm factor. -/
lemma inverseCuspCoordinates_eq_affine_add_normSq (c d : ℂ) (v : ℝ)
    (hc : c ≠ 0) (hv : 0 < v) (z : ℂ) :
    inverseCuspCoordinates c d v z =
      inverseCuspAffine c d v z + Complex.normSq z • inverseCuspRemainder c v z := by
  have hq0 : v ^ 2 + Complex.normSq z ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) (Complex.normSq_nonneg z))
  have hc0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hqc : ((v ^ 2 + Complex.normSq z : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hq0
  apply Prod.ext
  · change v / (‖c‖ ^ 2 * (v ^ 2 + ‖z‖ ^ 2)) =
      1 / (‖c‖ ^ 2 * v) + Complex.normSq z *
        (-1 / (‖c‖ ^ 2 * v * (v ^ 2 + Complex.normSq z)))
    rw [← Complex.normSq_eq_norm_sq z]
    field_simp [norm_ne_zero_iff.mpr hc, hv.ne', hq0]
    ring
  · change -d / c - star z / (c ^ 2 * ((v ^ 2 + ‖z‖ ^ 2 : ℝ) : ℂ)) =
      -d / c + (-1 / (c ^ 2 * (v : ℂ) ^ 2)) * conj z +
        (Complex.normSq z : ℂ) *
          (conj z / (c ^ 2 * (v : ℂ) ^ 2 * ((v ^ 2 + Complex.normSq z : ℝ) : ℂ)))
    rw [← Complex.normSq_eq_norm_sq z]
    simp only [Complex.star_def]
    field_simp [hc, hc0, hqc]
    simp only [Complex.ofReal_add, Complex.ofReal_pow]
    ring

lemma contDiff_inverseCuspCoordinates (c d : ℂ) (v : ℝ) (hc : c ≠ 0) (hv : 0 < v) :
    ContDiff ℝ ∞ (inverseCuspCoordinates c d v) := by
  have heq := funext (inverseCuspCoordinates_eq_affine_add_normSq c d v hc hv)
  rw [heq]
  exact (contDiff_inverseCuspAffine c d v).add
    (contDiff_cusp_normSq.smul (contDiff_inverseCuspRemainder c v hc hv))

lemma inverseCuspCoordinates_zero (c d : ℂ) (v : ℝ) (hc : c ≠ 0) (hv : 0 < v) :
    inverseCuspCoordinates c d v 0 = (1 / (‖c‖ ^ 2 * v), -d / c) := by
  rw [inverseCuspCoordinates_eq_affine_add_normSq c d v hc hv]
  simp [inverseCuspAffine]

/-- Every pure antiholomorphic jet of a globally smooth cusp function reflects exactly. -/
theorem inverse_cusp_iterated_wirtinger_rule (c d : ℂ) (v : ℝ) (hc : c ≠ 0) (hv : 0 < v)
    {F : ℝ × ℂ → ℂ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    iteratedDzbar n (fun z => F (inverseCuspCoordinates c d v z)) 0 =
      (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ n *
        iteratedDz n (fun z => F (1 / (‖c‖ ^ 2 * v), z)) (-d / c) := by
  have heq : (fun z => F (inverseCuspCoordinates c d v z)) =
      fun z => F (inverseCuspAffine c d v z +
        Complex.normSq z • inverseCuspRemainder c v z) := by
    funext z
    rw [inverseCuspCoordinates_eq_affine_add_normSq c d v hc hv]
  rw [heq, iteratedDzbar_normSq_perturbation hF (contDiff_inverseCuspAffine c d v)
    (contDiff_inverseCuspRemainder c v hc hv)]
  change iteratedDzbar n (fun z =>
    (fun w => F (1 / (‖c‖ ^ 2 * v), w)) (-d / c + (-1 / (c ^ 2 * (v : ℂ) ^ 2)) * conj z)) 0 = _
  have hs : ContDiff ℝ ∞ (fun z => F (1 / (‖c‖ ^ 2 * v), z)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  simp only [iteratedDzbar_comp_conj_affine hs, map_zero, mul_zero, add_zero]

/-- The higher cusp reflection law only requires smoothness near the inverse cusp center. -/
theorem inverse_cusp_iterated_wirtinger_rule_of_contDiffOn
    (c d : ℂ) (v : ℝ) (hc : c ≠ 0) (hv : 0 < v)
    {F : ℝ × ℂ → ℂ} {U : Set (ℝ × ℂ)} (hU : IsOpen U)
    (hp : (1 / (‖c‖ ^ 2 * v), -d / c) ∈ U) (hF : ContDiffOn ℝ ∞ F U) (n : ℕ) :
    iteratedDzbar n (fun z => F (inverseCuspCoordinates c d v z)) 0 =
      (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ n *
        iteratedDz n (fun z => F (1 / (‖c‖ ^ 2 * v), z)) (-d / c) := by
  obtain ⟨G, hG, hGF⟩ := exists_contDiff_eventuallyEq hU hp hF
  have hGF' : G =ᶠ[nhds (1 / (‖c‖ ^ 2 * v), -d / c)] F := hGF
  have hT : Tendsto (inverseCuspCoordinates c d v) (nhds 0)
      (nhds (1 / (‖c‖ ^ 2 * v), -d / c)) := by
    simpa only [inverseCuspCoordinates_zero c d v hc hv] using
      (contDiff_inverseCuspCoordinates c d v hc hv).continuous.continuousAt.tendsto (x := 0)
  have hTG : (fun z => G (inverseCuspCoordinates c d v z)) =ᶠ[nhds 0]
      (fun z => F (inverseCuspCoordinates c d v z)) := hGF'.comp_tendsto hT
  have hsG : (fun z => G (1 / (‖c‖ ^ 2 * v), z)) =ᶠ[nhds (-d / c)]
      (fun z => F (1 / (‖c‖ ^ 2 * v), z)) :=
    hGF'.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto (-d / c))
  rw [← (iteratedDzbar_eventuallyEq hTG n).self_of_nhds,
    inverse_cusp_iterated_wirtinger_rule c d v hc hv hG,
    (iteratedDz_eventuallyEq hsG n).self_of_nhds]

/-- The angular phase acquired at a cusp has modulus one. -/
lemma norm_cuspAngularPhase (c : ℂ) (hc : c ≠ 0) : ‖-conj c / c‖ = 1 := by
  rw [norm_div, norm_neg, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hc)]

private lemma cusp_normalization_factor (c : ℂ) (v : ℝ) (hc : c ≠ 0) (hv : 0 < v)
    (n : ℕ) :
    (v : ℂ) ^ n * (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ (n + 1) =
      (-conj c / c) ^ (n + 1) / ((‖c‖ ^ 2 * v ^ 2 : ℝ) : ℂ) *
        ((1 / (‖c‖ ^ 2 * v) : ℝ) : ℂ) ^ n := by
  have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hconjc : conj c ≠ 0 := by simpa only [Complex.star_def] using star_ne_zero.mpr hc
  have hnC : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  have hphase : -1 / (c ^ 2 * (v : ℂ) ^ 2) =
      (-conj c / c) / ((‖c‖ ^ 2 * v ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow v, hnC]
    field_simp [hc, hvC, hconjc]
  have hstep : (v : ℂ) * (-1 / (c ^ 2 * (v : ℂ) ^ 2)) =
      (-conj c / c) * ((1 / (‖c‖ ^ 2 * v) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, hnC]
    field_simp [hc, hvC, hconjc]
  calc
    _ = (-1 / (c ^ 2 * (v : ℂ) ^ 2)) *
        ((v : ℂ) * (-1 / (c ^ 2 * (v : ℂ) ^ 2))) ^ n := by
      rw [mul_pow, pow_succ]
      ring
    _ = _ := by rw [hstep, hphase, mul_pow, pow_succ]; ring

/-- Multiplying the derivative of order `n+1` by `v^n` leaves one order-independent
reflection scale and an angular phase of modulus one. -/
theorem inverse_cusp_normalized_iterated_wirtinger_rule
    (c d : ℂ) (v : ℝ) (hc : c ≠ 0) (hv : 0 < v)
    {F : ℝ × ℂ → ℂ} {U : Set (ℝ × ℂ)} (hU : IsOpen U)
    (hp : (1 / (‖c‖ ^ 2 * v), -d / c) ∈ U) (hF : ContDiffOn ℝ ∞ F U) (n : ℕ) :
    (v : ℂ) ^ n * iteratedDzbar (n + 1) (fun z => F (inverseCuspCoordinates c d v z)) 0 =
      (-conj c / c) ^ (n + 1) / ((‖c‖ ^ 2 * v ^ 2 : ℝ) : ℂ) *
        (((1 / (‖c‖ ^ 2 * v) : ℝ) : ℂ) ^ n *
          iteratedDz (n + 1) (fun z => F (1 / (‖c‖ ^ 2 * v), z)) (-d / c)) := by
  rw [inverse_cusp_iterated_wirtinger_rule_of_contDiffOn c d v hc hv hU hp hF,
    ← mul_assoc, cusp_normalization_factor c v hc hv, mul_assoc]

/-- Every normalized pure-jet order has the same absolute cusp-reflection factor. -/
theorem norm_inverse_cusp_normalized_iterated_wirtinger
    (c d : ℂ) (v : ℝ) (hc : c ≠ 0) (hv : 0 < v)
    {F : ℝ × ℂ → ℂ} {U : Set (ℝ × ℂ)} (hU : IsOpen U)
    (hp : (1 / (‖c‖ ^ 2 * v), -d / c) ∈ U) (hF : ContDiffOn ℝ ∞ F U) (n : ℕ) :
    ‖(v : ℂ) ^ n * iteratedDzbar (n + 1) (fun z => F (inverseCuspCoordinates c d v z)) 0‖ =
      (‖c‖ ^ 2 * v ^ 2)⁻¹ *
        ‖((1 / (‖c‖ ^ 2 * v) : ℝ) : ℂ) ^ n *
          iteratedDz (n + 1) (fun z => F (1 / (‖c‖ ^ 2 * v), z)) (-d / c)‖ := by
  rw [inverse_cusp_normalized_iterated_wirtinger_rule c d v hc hv hU hp hF,
    norm_mul, norm_div, norm_pow, norm_cuspAngularPhase c hc, one_pow,
    Complex.norm_of_nonneg (by positivity : 0 ≤ ‖c‖ ^ 2 * v ^ 2), one_div]

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
