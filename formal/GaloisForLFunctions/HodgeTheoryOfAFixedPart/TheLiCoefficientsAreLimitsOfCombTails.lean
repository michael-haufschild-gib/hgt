import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheDampedLiTailsReachTheLiCoefficients
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.SmoothTruncationPreservesTheDampedTail
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheNormalFormOfThePairingOfTheDegreePoints
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.OneInequalityPerPrimeOnTheComb

/-!
# Laguerre tails on the comb

The damped Laguerre profile has integrable exponentially weighted value and
derivative. Smooth truncations therefore converge in the spectral Weil form.
Sampling the translated truncations realizes the Li ladder on finite combs.
-/

open Complex MeasureTheory Set Filter Topology
open _root_.RHTower GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ Zeta23

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

/-- Coefficients of the Laguerre polynomial in the Li tail. -/
def liTailCoefficient (n k : ℕ) : ℝ :=
  (n.choose (k + 1) : ℝ) * (-1) ^ k / (k.factorial : ℝ)

/-- The smooth profile whose restriction to the positive half-line is the damped Li tail. -/
def liTailProfile (n : ℕ) (ε x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, liTailCoefficient n k *
    (x ^ k * Real.exp (-((1 / 2 + ε) * x)))

theorem contDiff_liTailProfile (n : ℕ) (ε : ℝ) : ContDiff ℝ 2 (liTailProfile n ε) := by
  unfold liTailProfile
  fun_prop

private theorem liTailProfile_weighted (n : ℕ) (ε x : ℝ) :
    liTailProfile n ε x * Real.exp (x / 2) =
      ∑ k ∈ Finset.range n, liTailCoefficient n k * (x ^ k * Real.exp (-(ε * x))) := by
  rw [liTailProfile, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have he : Real.exp (-((1 / 2 + ε) * x)) * Real.exp (x / 2) =
      Real.exp (-(ε * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = liTailCoefficient n k * (x ^ k *
        (Real.exp (-((1 / 2 + ε) * x)) * Real.exp (x / 2))) := by ring
    _ = _ := by rw [he]

private theorem hasDerivAt_liTailProfile (n : ℕ) (ε x : ℝ) :
    HasDerivAt (liTailProfile n ε)
      (∑ k ∈ Finset.range n, liTailCoefficient n k *
        (((k : ℝ) * x ^ (k - 1) - (1 / 2 + ε) * x ^ k) *
          Real.exp (-((1 / 2 + ε) * x)))) x := by
  unfold liTailProfile
  apply HasDerivAt.fun_sum
  intro k _
  have hp := (hasDerivAt_id x).pow k
  have he := (((hasDerivAt_id x).const_mul (1 / 2 + ε)).neg).exp
  exact ((hp.mul he).const_mul (liTailCoefficient n k)).congr_deriv (by dsimp; ring)

private theorem deriv_liTailProfile_weighted (n : ℕ) (ε x : ℝ) :
    deriv (liTailProfile n ε) x * Real.exp (x / 2) =
      ∑ k ∈ Finset.range n, liTailCoefficient n k *
        ((k : ℝ) * (x ^ (k - 1) * Real.exp (-(ε * x))) -
          (1 / 2 + ε) * (x ^ k * Real.exp (-(ε * x)))) := by
  rw [(hasDerivAt_liTailProfile n ε x).deriv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have he : Real.exp (-((1 / 2 + ε) * x)) * Real.exp (x / 2) =
      Real.exp (-(ε * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = liTailCoefficient n k * ((k : ℝ) * x ^ (k - 1) - (1 / 2 + ε) * x ^ k) *
        (Real.exp (-((1 / 2 + ε) * x)) * Real.exp (x / 2)) := by ring
    _ = _ := by rw [he]; ring

private theorem integrableOn_real_monomial_exp {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(ε * x))) (Ioi 0) := by
  have h := (integrableOn_natPow_mul_cexp
    (c := (ε : ℂ)) (by simpa using hε) k).norm
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [Complex.ofReal_re] using norm_natPow_mul_cexp (c := (ε : ℂ)) hx.le k

/-- Exponential damping makes the weighted Li tail integrable. -/
theorem integrableOn_weighted_liTailProfile (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x => |liTailProfile n ε x| * Real.exp (x / 2)) (Ioi 0) := by
  have h : IntegrableOn (fun x => ∑ k ∈ Finset.range n,
      liTailCoefficient n k * (x ^ k * Real.exp (-(ε * x)))) (Ioi 0) :=
    integrable_finsetSum _ fun k _ => (integrableOn_real_monomial_exp hε k).const_mul _
  refine h.abs.congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [← liTailProfile_weighted, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- The weighted derivative remains integrable despite the one-sided tail's jump at zero. -/
theorem integrableOn_weighted_deriv_liTailProfile (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x => |deriv (liTailProfile n ε) x| * Real.exp (x / 2)) (Ioi 0) := by
  have h : IntegrableOn (fun x => ∑ k ∈ Finset.range n, liTailCoefficient n k *
      ((k : ℝ) * (x ^ (k - 1) * Real.exp (-(ε * x))) -
        (1 / 2 + ε) * (x ^ k * Real.exp (-(ε * x))))) (Ioi 0) :=
    integrable_finsetSum _ fun k _ =>
      (((integrableOn_real_monomial_exp hε (k - 1)).const_mul (k : ℝ)).sub
        ((integrableOn_real_monomial_exp hε k).const_mul (1 / 2 + ε))).const_mul _
  refine h.abs.congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [← deriv_liTailProfile_weighted, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- A finite factorial sum bounds the exponentially weighted Laguerre profile. -/
theorem weighted_liTailProfile_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 ≤ x) :
    |liTailProfile n ε x| * Real.exp (x / 2) ≤
      ∑ k ∈ Finset.range n, |liTailCoefficient n k| * ((k.factorial : ℝ) / ε ^ k) := by
  rw [← abs_of_pos (Real.exp_pos (x / 2)), ← abs_mul, liTailProfile_weighted]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hx k), abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial_div_pow' hε hx k)
    (abs_nonneg _)

theorem ofReal_liTailProfile_eq_damped (n : ℕ) (ε : ℝ) {x : ℝ} (hx : 0 < x) :
    (liTailProfile n ε x : ℂ) = dampedLiTestFun n ε x := by
  have he : Complex.exp (-((x : ℂ) / 2)) * Complex.exp (-((ε : ℂ) * x)) =
      Complex.exp (-((1 / 2 + (ε : ℂ)) * x)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [liTailProfile, dampedLiTestFun, suzukiLiTestFun, if_pos hx,
    liTailCoefficient, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_add, Complex.ofReal_exp, Complex.ofReal_ofNat,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [show Complex.exp (-((x : ℂ) / 2)) *
      ((n.choose (k + 1) : ℂ) * (-1) ^ k / (k.factorial : ℂ) * (x : ℂ) ^ k) *
      Complex.exp (-((ε : ℂ) * x)) =
        ((n.choose (k + 1) : ℂ) * (-1) ^ k / (k.factorial : ℂ)) * (x : ℂ) ^ k *
        (Complex.exp (-((x : ℂ) / 2)) * Complex.exp (-((ε : ℂ) * x))) by ring, he]
  ring

private theorem dampedLiTestFun_zero_of_neg (n : ℕ) (ε : ℝ) {x : ℝ} (hx : x < 0) :
    dampedLiTestFun n ε x = 0 := by
  simp only [dampedLiTestFun, suzukiLiTestFun, if_neg hx.not_gt, if_neg hx.ne, zero_mul]

/-- Smooth finite Laguerre tails converge to the shifted Li resolvent at each zero. -/
theorem tendsto_paperFT_smoothLiTail (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Tendsto (fun R : ℝ => Zeta23.paperFT
      (fun x => (smoothTail (liTailProfile n ε) R x : ℂ)) z) atTop
      (𝓝 (suzukiEntireFourier (dampedLiTestFun n ε) z)) := by
  have he : (∫ x in Ioi (0 : ℝ), (liTailProfile n ε x : ℂ) * Complex.exp (I * z * x)) =
      suzukiEntireFourier (dampedLiTestFun n ε) z := by
    unfold suzukiEntireFourier
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    have hne : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
    filter_upwards [hne] with x hx
    rcases lt_or_gt_of_ne hx with hx | hx
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from not_lt.mpr hx.le),
        dampedLiTestFun_zero_of_neg n ε hx, zero_mul]
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), ofReal_liTailProfile_eq_damped n ε hx]
  rw [← he]
  exact tendsto_paperFT_smoothTail (contDiff_liTailProfile n ε)
    (integrableOn_weighted_liTailProfile n hε) hz

/-- A horizon-independent bound for the Fourier transforms of the compact tails. -/
def liTailFourierBound (n : ℕ) (ε : ℝ) : ℝ :=
  2 * (∑ k ∈ Finset.range n, |liTailCoefficient n k| * ((k.factorial : ℝ) / ε ^ k)) +
    ∫ x in Ioi (0 : ℝ), |deriv (liTailProfile n ε) x| * Real.exp (x / 2)

theorem liTailFourierBound_nonneg (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ liTailFourierBound n ε := by
  unfold liTailFourierBound
  apply add_nonneg
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity)
  · exact integral_nonneg fun _ => by positivity

/-- The reflected spectral product of a compact Laguerre tail. -/
def compactLiZeroTerm (n : ℕ) (ε R : ℝ) (q : XiZeroCopy) : ℂ :=
  Zeta23.paperFT (fun x => (smoothTail (liTailProfile n ε) R x : ℂ)) (-xiSpectralPoint q) *
    (starRingEnd ℂ) (Zeta23.paperFT
      (fun x => (smoothTail (liTailProfile n ε) R x : ℂ))
      ((starRingEnd ℂ) (-xiSpectralPoint q)))

private theorem spectral_abs_im_le_half (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| ≤ 1 / 2 := by
  rw [xiSpectralPoint_eq_support, abs_le]
  exact ⟨(abs_im_xiSpectralPointSupport_lt q.1).1.le,
    (abs_im_xiSpectralPointSupport_lt q.1).2.le⟩

/-- The summable inverse-square majorant is uniform in the cutoff horizon. -/
theorem norm_compactLiZeroTerm_le (n : ℕ) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (q : XiZeroCopy) :
    ‖compactLiZeroTerm n ε R q‖ ≤ liTailFourierBound n ε ^ 2 * (1 / xiCopyOrdinate q ^ 2) := by
  have hg : 0 < |xiCopyOrdinate q| := lt_trans (by norm_num) (four_lt_abs_xiCopyOrdinate q)
  have hre : (xiSpectralPoint q).re = xiCopyOrdinate q := by simp [xiSpectralPoint, xiCopyOrdinate]
  have hn : |xiCopyOrdinate q| ≤ ‖xiSpectralPoint q‖ := hre ▸ Complex.abs_re_le_norm _
  have hc := liTailFourierBound_nonneg n hε
  have hb (z : ℂ) (hz : |z.im| ≤ 1 / 2) (hzn : ‖z‖ = ‖xiSpectralPoint q‖) :
      ‖Zeta23.paperFT (fun x => (smoothTail (liTailProfile n ε) R x : ℂ)) z‖ ≤
        liTailFourierBound n ε / |xiCopyOrdinate q| := by
    have hgz : |xiCopyOrdinate q| ≤ ‖z‖ := hzn.symm ▸ hn
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hg.trans_le hgz)
    have hh := norm_paperFT_smoothTail_le (contDiff_liTailProfile n ε)
      (Finset.sum_nonneg fun k _ => by positivity : 0 ≤ ∑ k ∈ Finset.range n,
        |liTailCoefficient n k| * ((k.factorial : ℝ) / ε ^ k))
      (fun x hx => weighted_liTailProfile_le n hε hx)
      (integrableOn_weighted_deriv_liTailProfile n hε) hR hz hz0
    exact hh.trans (div_le_div_of_nonneg_left hc hg hgz)
  have h1 := hb (-xiSpectralPoint q)
    (by simpa only [Complex.neg_im, abs_neg] using spectral_abs_im_le_half q) (norm_neg _)
  have h2 := hb ((starRingEnd ℂ) (-xiSpectralPoint q))
    (by simpa only [Complex.conj_im, Complex.neg_im, neg_neg] using spectral_abs_im_le_half q)
    (by simp only [norm_conj, norm_neg])
  rw [compactLiZeroTerm, norm_mul, norm_conj]
  refine (mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg hc hg.le)).trans_eq ?_
  rw [← sq, div_pow, sq_abs]
  ring

/-- Smooth compact tails recover the damped Li spectral form, with multiplicities. -/
theorem tendsto_compactLiZeroSum (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => ∑' q, compactLiZeroTerm n ε R q) atTop
      (𝓝 (dampedLiWeilForm n ε)) := by
  apply tendsto_tsum_of_dominated_convergence
    (summable_inv_sq_xiCopyOrdinate.mul_left (liTailFourierBound n ε ^ 2))
  · intro q
    rw [dampedLiZeroTerm_eq_fourier n hε.le q]
    exact (tendsto_paperFT_smoothLiTail n hε
      (by simpa only [Complex.neg_im, abs_neg] using spectral_abs_im_le_half q)).mul
      (Complex.continuous_conj.tendsto _ |>.comp
        (tendsto_paperFT_smoothLiTail n hε
          (by simpa only [Complex.conj_im, Complex.neg_im, neg_neg] using spectral_abs_im_le_half q)))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR q
    exact norm_compactLiZeroTerm_le n hε hR q

private theorem li_tsum_copies_eq_carrier (F : ℂ → ℂ)
    (hF : Summable (fun q : XiZeroCopy => F (xiSpectralPoint q))) :
    (∑' q : XiZeroCopy, F (xiSpectralPoint q)) =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * F (gammaOf ρ) := by
  rw [hF.tsum_sigma]
  rw [← xiDivisorZetaCarrierEquiv.tsum_eq
    (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) * F (gammaOf ρ))]
  apply tsum_congr
  intro ρ
  have he (q : XiZeroCopy) : xiSpectralPoint q = gammaOf (q.1 : ℂ) := by
    simp only [xiSpectralPoint, gammaOf, div_eq_mul_inv, Complex.inv_I]
  simp only [he, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, xiDivisorZetaCarrierEquiv_multiplicity]
  rfl

private theorem li_paperFT_comp_neg (f : ℝ → ℂ) (z : ℂ) :
    paperFT (fun x => f (-x)) z = paperFT f (-z) := by
  unfold paperFT
  rw [← integral_neg_eq_self (fun x : ℝ => f x * Complex.exp (I * -z * (x : ℂ))) volume]
  congr 1
  funext x
  push_cast
  ring_nf

private theorem li_copies_reflected_W (g : ℝ → ℂ)
    (hs : Summable (fun q : XiZeroCopy => paperFT g (-xiSpectralPoint q) *
      (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (-xiSpectralPoint q))))) :
    (∑' q : XiZeroCopy, paperFT g (-xiSpectralPoint q) *
      (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (-xiSpectralPoint q)))) =
      zetaZeroConfig.W (fun x => g (-x)) (fun x => g (-x)) := by
  rw [li_tsum_copies_eq_carrier
    (fun z => paperFT g (-z) * (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (-z)))) hs]
  unfold ZeroConfig.W
  apply tsum_congr
  intro ρ
  simp only [ZeroConfig.Wsummand, li_paperFT_comp_neg, map_neg, mul_assoc]

/-- Reflection and translation place the finite tail in the sampling window.
The coordinate at a degree point is `x=log(4 exp(R) N/m)`. -/
def liCombPacket (n : ℕ) (ε R u : ℝ) : ℝ :=
  smoothTail (liTailProfile n ε) R (R + Real.log 4 - u)

theorem contDiff_liCombPacket (n : ℕ) (ε R : ℝ) : ContDiff ℝ 2 (liCombPacket n ε R) :=
  (contDiff_smoothTail (contDiff_liTailProfile n ε) R).comp
    (contDiff_const.sub contDiff_id)

theorem hasCompactSupport_liCombPacket (n : ℕ) (ε : ℝ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (liCombPacket n ε R) := by
  have h := (hasCompactSupport_smoothTail (liTailProfile n ε) hR).comp_homeomorph
    (Homeomorph.neg ℝ)
  have ht := h.comp_homeomorph (Homeomorph.subRight (R + Real.log 4))
  convert ht using 1
  funext u
  dsimp [liCombPacket]
  congr 1
  change R + Real.log 4 - u = -(u - (R + Real.log 4))
  ring

/-- The sampled real packet has exactly the reflected, multiplicity-counted spectral form. -/
theorem zeroSum_liCombPacket (n : ℕ) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    zeroSum (liCombPacket n ε R) = (∑' q, compactLiZeroTerm n ε R q).re := by
  let f := smoothTail (liTailProfile n ε) R
  have hf := contDiff_smoothTail (contDiff_liTailProfile n ε) R
  have hfc := hasCompactSupport_smoothTail (liTailProfile n ε) hR
  have ht := zeroSum_translate_packet (hf.comp contDiff_id.neg)
    (hfc.comp_homeomorph (Homeomorph.neg ℝ)) (R + Real.log 4)
  change zeroSum (fun u => f (-(u - (R + Real.log 4)))) = zeroSum (fun u => f (-u)) at ht
  have he : liCombPacket n ε R = fun u => f (-(u - (R + Real.log 4))) := by
    funext u
    dsimp [liCombPacket, f]
    congr 1
    ring
  have hs : Summable (compactLiZeroTerm n ε R) :=
    Summable.of_norm_bounded
      (summable_inv_sq_xiCopyOrdinate.mul_left (liTailFourierBound n ε ^ 2))
      (norm_compactLiZeroTerm_le n hε hR)
  have hW := li_copies_reflected_W (fun x => (f x : ℂ)) hs
  calc
    _ = zeroSum (fun u => f (-u)) := by rw [he]; exact ht
    _ = _ := congrArg Complex.re hW.symm

/-- Compact tail forms tend to the damped Li form. -/
theorem tendsto_zeroSum_liCombPacket (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => zeroSum (liCombPacket n ε R)) atTop
      (𝓝 (dampedLiWeilForm n ε).re) := by
  have h := Complex.continuous_re.tendsto _ |>.comp (tendsto_compactLiZeroSum n hε)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (zeroSum_liCombPacket n hε hR).symm

/-- The integer window containing the translated finite tail. -/
def liCombWindow (R : ℝ) : ℕ := ⌈Real.exp (R + Real.log 4)⌉₊ + 1

/-- The finite comb form of the smooth Laguerre tail. -/
def liCombTail (n : ℕ) (ε R : ℝ) (N : ℕ) : ℝ :=
  combForm (Finset.Ioc N (N + 3 * liCombWindow R * N)) (sampleCoord (liCombPacket n ε R) N)

/-- For each compact tail, refining the integer comb recovers its Weil form. -/
theorem tendsto_liCombTail (n : ℕ) (ε : ℝ) {R : ℝ} (hR : 0 < R) :
    Tendsto (liCombTail n ε R) atTop (𝓝 (zeroSum (liCombPacket n ε R))) := by
  apply tendsto_combForm_sample (contDiff_liCombPacket n ε R)
    (hasCompactSupport_liCombPacket n ε hR) (show 1 ≤ liCombWindow R by unfold liCombWindow; omega)
  intro u hu
  unfold liCombPacket smoothTail
  rw [tailPlateau_zero hR, zero_mul]
  rcases hu with hu | hu
  · exact Or.inr (by
      have hl : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
      linarith only [hu, hl])
  · exact Or.inl (by
      have hK : Real.exp (R + Real.log 4) ≤ (liCombWindow R : ℝ) := by
        unfold liCombWindow
        push_cast
        exact (Nat.le_ceil _).trans (by linarith)
      have hl := Real.log_le_log (Real.exp_pos _) hK
      rw [Real.log_exp] at hl
      linarith only [hu, hl])

/-- Every paired Li coefficient is a limit of finite comb forms of explicitly damped,
smoothly truncated Laguerre tails. Both the tail horizon and the sampling scale diverge. -/
theorem exists_liCombTail_sequence (n : ℕ) :
    ∃ (R : ℕ → ℝ) (N : ℕ → ℕ),
      (∀ m : ℕ, (m : ℝ) + 1 ≤ R m) ∧ (∀ m : ℕ, m ≤ N m) ∧
      Tendsto (fun m : ℕ => liCombTail n (1 / ((m : ℝ) + 1)) (R m) (N m)) atTop
        (𝓝 (xiLiPaired n).re) := by
  classical
  have happ (m : ℕ) : ∃ R : ℝ, ∃ N : ℕ, (m : ℝ) + 1 ≤ R ∧ m ≤ N ∧
      dist (liCombTail n (1 / ((m : ℝ) + 1)) R N)
        (dampedLiWeilForm n (1 / ((m : ℝ) + 1))).re < 1 / ((m : ℝ) + 1) := by
    let ε : ℝ := 1 / ((m : ℝ) + 1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hδ : 0 < ε / 2 := half_pos hε
    have hRlim := Metric.tendsto_nhds.mp (tendsto_zeroSum_liCombPacket n hε) (ε / 2) hδ
    obtain ⟨R, hR, hRc⟩ := ((eventually_ge_atTop ((m : ℝ) + 1)).and hRlim).exists
    have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
    have hNlim := Metric.tendsto_nhds.mp (tendsto_liCombTail n ε hR0) (ε / 2) hδ
    obtain ⟨N, hN, hNc⟩ := ((eventually_ge_atTop m).and hNlim).exists
    refine ⟨R, N, hR, hN, ?_⟩
    calc
      _ ≤ dist (liCombTail n ε R N) (zeroSum (liCombPacket n ε R)) +
          dist (zeroSum (liCombPacket n ε R)) (dampedLiWeilForm n ε).re := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hNc hRc
      _ = _ := by dsimp [ε]; ring
  choose R N hR hN happ using happ
  refine ⟨R, N, hR, hN, ?_⟩
  have hε : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hL := Complex.continuous_re.tendsto _ |>.comp ((tendsto_dampedLiWeilForm n).comp hε)
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hsmall := hε.eventually (gt_mem_nhds (half_pos hδ))
  have hclose := Metric.tendsto_nhds.mp hL (δ / 2) (half_pos hδ)
  filter_upwards [hsmall, hclose] with m hm hm'
  calc
    _ ≤ dist (liCombTail n (1 / ((m : ℝ) + 1)) (R m) (N m))
        (dampedLiWeilForm n (1 / ((m : ℝ) + 1))).re +
        dist (dampedLiWeilForm n (1 / ((m : ℝ) + 1))).re (xiLiPaired n).re := dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add ((happ m).trans hm) hm'
    _ = δ := by ring

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
