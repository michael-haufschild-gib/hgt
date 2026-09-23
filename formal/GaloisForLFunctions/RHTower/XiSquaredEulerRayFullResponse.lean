import GaloisForLFunctions.RHTower.XiSquaredEulerRayTwoPointPositivity
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# The full Xi squared-Euler response

The finite squared-zero packet from `XiSquaredEulerRayTwoPointPositivity` is not an auxiliary
truncation.  On the positive real Euler ray it sums absolutely over the complete
multiplicity-exact Xi divisor and is exactly the real logarithmic derivative of `xi`.

The relative-resolvent identity fixes the normalization: if `x > 0`, then

`xi'(1/2+x) / (x * xi(1/2+x)) = sum_q Re (x^(2 : ℕ) + a_q^(2 : ℕ))^(-1)`.

Here `a_q` is the centered Xi spectral point.  Each real part is the chamber response already
controlled by the source height gap.  Consequently the actual infinite Xi response is strictly
decreasing, its radius-weighted response is strictly increasing, and every two-node response
determinant is strictly positive without RH.  Thus a negative Euler-ray detector for an off-line
zero cannot occur at one or two nodes even after all cross-orbit correlations are restored.

This theorem does not control the mixed exterior-cubic terms of the full response and is not an
RH proof.
-/

open Set Complex Function
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Exact identification of one orbit with one reciprocal-square resolvent term -/

lemma xiSpectralPoint_sq_re_eq_squaredEulerOrbitT (q : XiZeroCopy) :
    (xiSpectralPoint q ^ 2).re = xiSquaredEulerOrbitT q := by
  simp only [xiSpectralPoint, xiSquaredEulerOrbitT, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

lemma xiSpectralPoint_sq_im_sq_eq_squaredEulerOrbitCharge (q : XiZeroCopy) :
    (xiSpectralPoint q ^ 2).im ^ 2 = xiSquaredEulerOrbitCharge q := by
  simp only [xiSpectralPoint, xiSquaredEulerOrbitCharge, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

lemma xiSquaredEulerResolvent_den_ne (q : XiZeroCopy) (x : ℝ) :
    xiSpectralPoint q ^ 2 + (x : ℂ) ^ 2 ≠ 0 := by
  apply Complex.ne_zero_of_re_pos
  rw [Complex.add_re, xiSpectralPoint_sq_re_eq_squaredEulerOrbitT]
  simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have ht := (xiSquaredEulerOrbit_mem_chamber q).1
  nlinarith [sq_nonneg x]

/-- The paired reciprocal-square resolvent at the imaginary centered point is the ordinary
reciprocal of the squared spectral point shifted by `x^(2 : ℕ)`. -/
theorem xiReciprocalSquareResolventTerm_neg_mul_I_eq
    (q : XiZeroCopy) (x : ℝ) :
    xiReciprocalSquareResolventTerm (-(x : ℂ) * I) q =
      (xiSpectralPoint q ^ 2 + (x : ℂ) ^ 2)⁻¹ := by
  have ha := xiSpectralPoint_ne_zero q
  have hd := xiSquaredEulerResolvent_den_ne q x
  rw [xiReciprocalSquareResolventTerm, xiZeroCopyReciprocalSquare]
  field_simp [ha, hd]
  rw [Complex.I_sq]
  ring

/-- The real part of one exact Xi resolvent term is precisely its squared-Euler chamber atom. -/
theorem xiReciprocalSquareResolventTerm_neg_mul_I_re_eq
    (q : XiZeroCopy) (x : ℝ) :
    (xiReciprocalSquareResolventTerm (-(x : ℂ) * I) q).re =
      xiSquaredEulerOrbitResponse q (x ^ 2) := by
  have hxre : ((x : ℂ) ^ 2).re = x ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have hxim : ((x : ℂ) ^ 2).im = 0 := by
    simp [pow_two, Complex.mul_im]
  have himprod :
      (xiSpectralPoint q ^ 2).im * (xiSpectralPoint q ^ 2).im =
        xiSquaredEulerOrbitCharge q := by
    simpa only [pow_two] using
      xiSpectralPoint_sq_im_sq_eq_squaredEulerOrbitCharge q
  rw [xiReciprocalSquareResolventTerm_neg_mul_I_eq,
    Complex.inv_re, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    xiSpectralPoint_sq_re_eq_squaredEulerOrbitT, hxre, hxim, add_zero,
    himprod]
  simp only [xiSquaredEulerOrbitResponse, squaredEulerOrbitResponse, pow_two]

/-! ## The full multiplicity-exact Xi response -/

private noncomputable def xiSquaredEulerWitness : XiZeroCopy := by
  let rho : ℂ := Classical.choose xiDivisorSupport_infinite.nonempty
  have hrho : rho ∈ (MeromorphicOn.divisor xi Set.univ).support :=
    Classical.choose_spec xiDivisorSupport_infinite.nonempty
  let rhoSupport : XiDivisorSupport := ⟨rho, hrho⟩
  have hpos := xi_divisor_pos_on_support rhoSupport
  have hn : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (rhoSupport : ℂ)) := by
    omega
  exact ⟨rhoSupport, ⟨0, hn⟩⟩

/-- The complete squared-Euler radial response, with every Xi zero repeated by analytic
multiplicity. -/
def xiSquaredEulerFullResponse (u : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiSquaredEulerOrbitResponse q u

lemma XiC_neg_mul_I_ne (x : ℝ) : XiC (-(x : ℂ) * I) ≠ 0 := by
  apply XiC_ne_zero_of_abs_re_le_nine_halves
  norm_num [Complex.mul_re]

/-- The full response is absolutely summable at every nonnegative radial parameter. -/
theorem summable_xiSquaredEulerOrbitResponse {u : ℝ} (hu : 0 ≤ u) :
    Summable (fun q : XiZeroCopy => xiSquaredEulerOrbitResponse q u) := by
  let x := Real.sqrt u
  have hx2 : x ^ 2 = u := Real.sq_sqrt hu
  have hsum := summable_xiReciprocalSquareResolventTerm (XiC_neg_mul_I_ne x)
  have hsumre : Summable (fun q : XiZeroCopy =>
      (xiReciprocalSquareResolventTerm (-(x : ℂ) * I) q).re) := by
    exact (hsum.mapL Complex.reCLM).congr (fun _ => rfl)
  apply hsumre.congr
  intro q
  rw [xiReciprocalSquareResolventTerm_neg_mul_I_re_eq q x, hx2]

/-- The complete Xi response is strictly positive on the closed nonnegative radial ray. -/
theorem xiSquaredEulerFullResponse_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < xiSquaredEulerFullResponse u := by
  rw [xiSquaredEulerFullResponse]
  exact (summable_xiSquaredEulerOrbitResponse hu).tsum_pos
    (fun q => (xiSquaredEulerOrbitResponse_pos q hu).le)
    xiSquaredEulerWitness
    (xiSquaredEulerOrbitResponse_pos xiSquaredEulerWitness hu)

/-- Strict radial decrease survives the complete infinite Xi divisor. -/
theorem strictAntiOn_xiSquaredEulerFullResponse :
    StrictAntiOn xiSquaredEulerFullResponse (Ici 0) := by
  intro u hu v hv huv
  rw [xiSquaredEulerFullResponse, xiSquaredEulerFullResponse]
  exact (summable_xiSquaredEulerOrbitResponse hv).tsum_lt_tsum
    (i := xiSquaredEulerWitness)
    (fun q => (strictAntiOn_xiSquaredEulerOrbitResponse q hu hv huv).le)
    (strictAntiOn_xiSquaredEulerOrbitResponse xiSquaredEulerWitness hu hv huv)
    (summable_xiSquaredEulerOrbitResponse hu)

/-- Strict increase of the radius-weighted response also survives the complete divisor. -/
theorem strictMonoOn_mul_xiSquaredEulerFullResponse :
    StrictMonoOn (fun u => u * xiSquaredEulerFullResponse u) (Ici 0) := by
  intro u hu v hv huv
  have hsumu : Summable (fun q : XiZeroCopy =>
      u * xiSquaredEulerOrbitResponse q u) :=
    (summable_xiSquaredEulerOrbitResponse hu).mul_left u
  have hsumv : Summable (fun q : XiZeroCopy =>
      v * xiSquaredEulerOrbitResponse q v) :=
    (summable_xiSquaredEulerOrbitResponse hv).mul_left v
  have hlt :
      (∑' q : XiZeroCopy, u * xiSquaredEulerOrbitResponse q u) <
        ∑' q : XiZeroCopy, v * xiSquaredEulerOrbitResponse q v :=
    hsumu.tsum_lt_tsum (i := xiSquaredEulerWitness)
      (fun q =>
        (strictMonoOn_mul_xiSquaredEulerOrbitResponse q hu hv huv).le)
      (strictMonoOn_mul_xiSquaredEulerOrbitResponse
        xiSquaredEulerWitness hu hv huv)
      hsumv
  simpa only [xiSquaredEulerFullResponse, tsum_mul_left] using hlt

/-! ## Exact analytic identification -/

/-- Exact complex normalization of the full reciprocal-square divisor response. -/
theorem logDeriv_xi_eulerRay_div_eq_tsum_xiReciprocalSquareResolventTerm
    {x : ℝ} (hx : 0 < x) :
    logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) / (x : ℂ) =
      ∑' q : XiZeroCopy,
        xiReciprocalSquareResolventTerm (-(x : ℂ) * I) q := by
  let z : ℂ := -(x : ℂ) * I
  let S : ℂ := ∑' q : XiZeroCopy,
    xiReciprocalSquareResolventTerm z q
  have hXi : XiC z ≠ 0 := XiC_neg_mul_I_ne x
  have hcoord : (1 / 2 : ℂ) + z * I = (1 / 2 : ℂ) + (x : ℂ) := by
    dsimp only [z]
    rw [mul_assoc, I_mul_I]
    ring
  have hmaster :
      I * logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) = (x : ℂ) * I * S := by
    calc
      I * logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) =
          logDeriv XiC z := by
        rw [logDeriv_XiC_eq_mul_I_logDeriv_xi, hcoord]
      _ = xiRelativeResolventTrace z :=
        logDeriv_XiC_eq_relativeResolventTrace hXi
      _ = -z * S :=
        xiRelativeResolventTrace_eq_reciprocalSquareResolvent hXi
      _ = (x : ℂ) * I * S := by dsimp only [z]; ring
  have hL :
      logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) = (x : ℂ) * S := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc
      I * logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) =
          (x : ℂ) * I * S := hmaster
      _ = I * ((x : ℂ) * S) := by ring
  change logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) / (x : ℂ) = S
  rw [hL]
  field_simp [hx.ne']

/-- The full chamber response is the real positive-Euler logarithmic derivative of Xi. -/
theorem xiSquaredEulerFullResponse_eq_logDeriv {x : ℝ} (hx : 0 < x) :
    xiSquaredEulerFullResponse (x ^ 2) =
      (logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) / (x : ℂ)).re := by
  have hsum := summable_xiReciprocalSquareResolventTerm (XiC_neg_mul_I_ne x)
  rw [xiSquaredEulerFullResponse]
  calc
    (∑' q : XiZeroCopy, xiSquaredEulerOrbitResponse q (x ^ 2)) =
        ∑' q : XiZeroCopy,
          (xiReciprocalSquareResolventTerm (-(x : ℂ) * I) q).re := by
      apply tsum_congr
      intro q
      exact (xiReciprocalSquareResolventTerm_neg_mul_I_re_eq q x).symm
    _ = (∑' q : XiZeroCopy,
          xiReciprocalSquareResolventTerm (-(x : ℂ) * I) q).re := by
      exact (Complex.re_tsum hsum).symm
    _ = (logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) / (x : ℂ)).re := by
      rw [logDeriv_xi_eulerRay_div_eq_tsum_xiReciprocalSquareResolventTerm hx]

/-! ## The actual infinite Xi response kernel -/

/-- The full positive-Euler logarithmic derivative, assembled from the exact Xi divisor. -/
def xiSquaredEulerFullQ (x : ℝ) : ℝ :=
  x * xiSquaredEulerFullResponse (x ^ 2)

/-- On the positive Euler ray the divisor definition is exactly the real logarithmic derivative
of `xi`; no finite-cutoff limit remains. -/
theorem xiSquaredEulerFullQ_eq_logDeriv_re {x : ℝ} (hx : 0 < x) :
    xiSquaredEulerFullQ x =
      (logDeriv xi ((1 / 2 : ℂ) + (x : ℂ))).re := by
  rw [xiSquaredEulerFullQ, xiSquaredEulerFullResponse_eq_logDeriv hx,
    Complex.div_re, Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
  field_simp [hx.ne']
  ring

/-- The actual infinite-divisor Euler response kernel. -/
def xiSquaredEulerFullKernel (x y : ℝ) : ℝ :=
  eulerRayResponseKernel xiSquaredEulerFullQ x y

/-- The full Xi response kernel has a strictly positive diagonal at every positive node. -/
theorem xiSquaredEulerFullKernel_diag_pos {x : ℝ} (hx : 0 < x) :
    0 < xiSquaredEulerFullKernel x x := by
  have hprofile := xiSquaredEulerFullResponse_pos (sq_nonneg x)
  have hdiag : xiSquaredEulerFullKernel x x =
      xiSquaredEulerFullResponse (x ^ 2) := by
    rw [xiSquaredEulerFullKernel, eulerRayResponseKernel,
      xiSquaredEulerFullQ]
    field_simp [hx.ne']
  rw [hdiag]
  exact hprofile

/-- **Full Xi two-node response barrier.**  Every pair of distinct positive Euler nodes has
strictly positive determinant for the complete multiplicity-exact Xi divisor, without RH. -/
theorem xiSquaredEulerFullKernel_twoPoint_det_pos
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < xiSquaredEulerFullKernel x x * xiSquaredEulerFullKernel y y -
      xiSquaredEulerFullKernel x y ^ 2 := by
  have hy : 0 < y := hx.trans hxy
  have hsq : x ^ 2 < y ^ 2 := by nlinarith
  have hdecreaseProfile :=
    strictAntiOn_xiSquaredEulerFullResponse (sq_nonneg x) (sq_nonneg y) hsq
  have hincreaseProfile :=
    strictMonoOn_mul_xiSquaredEulerFullResponse (sq_nonneg x) (sq_nonneg y) hsq
  have hdecrease : xiSquaredEulerFullQ y / y < xiSquaredEulerFullQ x / x := by
    simpa [xiSquaredEulerFullQ, hx.ne', hy.ne'] using hdecreaseProfile
  have hincrease : x * xiSquaredEulerFullQ x < y * xiSquaredEulerFullQ y := by
    simpa [xiSquaredEulerFullQ, pow_two, mul_assoc] using hincreaseProfile
  simpa only [xiSquaredEulerFullKernel] using
    eulerRayResponseKernel_twoPoint_det_pos
      xiSquaredEulerFullQ hx hxy hdecrease hincrease

end

end RHTower
