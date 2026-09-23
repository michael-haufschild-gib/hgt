import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeActualPhaseEscape

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Rounding `exp(t)` upward to a natural number changes its logarithm by `o(1)`. -/
theorem tendsto_log_natCeil_exp_sub
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) :
    Tendsto (fun k ↦ Real.log (⌈Real.exp (t k)⌉₊ : ℝ) - t k)
      atTop (nhds 0) := by
  let x : ℕ → ℝ := fun k ↦ Real.exp (t k)
  let n : ℕ → ℕ := fun k ↦ ⌈x k⌉₊
  have hx : Tendsto x atTop atTop := Real.tendsto_exp_atTop.comp ht
  have hxinv : Tendsto (fun k ↦ (x k)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hx
  have hupper : Tendsto (fun k ↦ 1 + (x k)⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hxinv
  have hratio : Tendsto (fun k ↦ (n k : ℝ) / x k) atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hupper
    · filter_upwards with k
      have hxpos : 0 < x k := by exact Real.exp_pos _
      apply (le_div_iff₀ hxpos).2
      simpa [n] using Nat.le_ceil (x k)
    · filter_upwards with k
      have hxpos : 0 < x k := by exact Real.exp_pos _
      have hnlt : (n k : ℝ) < x k + 1 := by
        exact Nat.ceil_lt_add_one hxpos.le
      apply (div_le_iff₀ hxpos).2
      have hxne : x k ≠ 0 := ne_of_gt hxpos
      field_simp [hxne]
      linarith
  have hlogratio : Tendsto (fun k ↦ Real.log ((n k : ℝ) / x k))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  convert hlogratio using 1
  funext k
  change Real.log (n k : ℝ) - t k = Real.log ((n k : ℝ) / x k)
  have hxne : x k ≠ 0 := by simp [x]
  have hnpos : 0 < n k := by
    dsimp only [n]
    exact Nat.ceil_pos.2 (Real.exp_pos _)
  rw [Real.log_div (by exact_mod_cast ne_of_gt hnpos) hxne]
  simp [x]

/-- Cofinal translations with exact target phase modulo `2π`. -/
def twoEdgeLogMeshPhaseTarget (beta theta : ℝ) (k : ℕ) : ℝ :=
  (theta + (k : ℝ) * (2 * Real.pi)) / beta

/-- Natural aperture obtained by rounding the exponential of a target translation. -/
def twoEdgeLogMeshPhaseIndex (beta theta : ℝ) (k : ℕ) : ℕ :=
  ⌈Real.exp (2 * twoEdgeLogMeshPhaseTarget beta theta k)⌉₊

/-- Actual logarithmic translation of the rounded natural aperture. -/
def twoEdgeLogMeshPhaseTranslation (beta theta : ℝ) (k : ℕ) : ℝ :=
  Real.log (twoEdgeLogMeshPhaseIndex beta theta k) / 2

theorem tendsto_twoEdgeLogMeshPhaseTarget_atTop
    {beta : ℝ} (hbeta : 0 < beta) (theta : ℝ) :
    Tendsto (twoEdgeLogMeshPhaseTarget beta theta) atTop atTop := by
  have hperiod : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hmul : Tendsto (fun k : ℕ ↦ (k : ℝ) * (2 * Real.pi))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hperiod
  have hadd : Tendsto (fun k : ℕ ↦ theta + (k : ℝ) * (2 * Real.pi))
      atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ ?_
    filter_upwards [hmul.eventually_ge_atTop (b - theta)] with k hk
    linarith
  exact hadd.atTop_div_const hbeta

theorem twoEdgeLogMeshPhaseTarget_mul
    {beta : ℝ} (hbeta : beta ≠ 0) (theta : ℝ) (k : ℕ) :
    beta * twoEdgeLogMeshPhaseTarget beta theta k =
      theta + (k : ℝ) * (2 * Real.pi) := by
  rw [twoEdgeLogMeshPhaseTarget]
  field_simp

theorem tendsto_twoEdgeLogMeshPhaseTranslation_sub_target
    {beta : ℝ} (hbeta : 0 < beta) (theta : ℝ) :
    Tendsto (fun k ↦ twoEdgeLogMeshPhaseTranslation beta theta k -
      twoEdgeLogMeshPhaseTarget beta theta k) atTop (nhds 0) := by
  have ht := tendsto_twoEdgeLogMeshPhaseTarget_atTop hbeta theta
  have h2t : Tendsto (fun k ↦ 2 * twoEdgeLogMeshPhaseTarget beta theta k)
      atTop atTop := ht.const_mul_atTop (by norm_num)
  have hround := tendsto_log_natCeil_exp_sub h2t
  have hhalf := hround.const_mul (1 / 2 : ℝ)
  convert hhalf using 1
  · funext k
    rw [twoEdgeLogMeshPhaseTranslation, twoEdgeLogMeshPhaseIndex]
    ring
  · norm_num

theorem tendsto_twoEdgeLogMeshPhaseTranslation_atTop
    {beta : ℝ} (hbeta : 0 < beta) (theta : ℝ) :
    Tendsto (twoEdgeLogMeshPhaseTranslation beta theta) atTop atTop := by
  have ht := tendsto_twoEdgeLogMeshPhaseTarget_atTop hbeta theta
  have herr := tendsto_twoEdgeLogMeshPhaseTranslation_sub_target hbeta theta
  refine tendsto_atTop.2 fun b ↦ ?_
  have herrBound : ∀ᶠ k in atTop,
      -1 < twoEdgeLogMeshPhaseTranslation beta theta k -
        twoEdgeLogMeshPhaseTarget beta theta k :=
    (tendsto_order.1 herr).1 (-1) (by norm_num)
  filter_upwards [ht.eventually_ge_atTop (b + 1), herrBound] with k htk hek
  linarith

theorem tendsto_twoEdgeLogMeshPhaseIndex_atTop
    {beta : ℝ} (hbeta : 0 < beta) (theta : ℝ) :
    Tendsto (twoEdgeLogMeshPhaseIndex beta theta) atTop atTop := by
  have ht := tendsto_twoEdgeLogMeshPhaseTarget_atTop hbeta theta
  have h2t : Tendsto (fun k ↦ 2 * twoEdgeLogMeshPhaseTarget beta theta k)
      atTop atTop := ht.const_mul_atTop (by norm_num)
  exact tendsto_nat_ceil_atTop.comp (Real.tendsto_exp_atTop.comp h2t)

theorem exp_neg_logMeshPhase_eq_target_mul_error
    {beta : ℝ} (hbeta : beta ≠ 0) (theta a : ℝ) (k : ℕ) :
    Complex.exp (-((a : ℂ) * (beta : ℂ) * I)) =
      Complex.exp (-((theta : ℂ) * I)) *
        Complex.exp (-(((beta *
          (a - twoEdgeLogMeshPhaseTarget beta theta k) : ℝ) : ℂ) * I)) := by
  have hp := twoEdgeLogMeshPhaseTarget_mul hbeta theta k
  have hpC := congrArg (↑Complex.ofReal) hp
  push_cast at hpC
  have hdecomp :
      -((a : ℂ) * (beta : ℂ) * I) =
        -((theta : ℂ) * I) +
          -((k : ℂ) * (2 * (Real.pi : ℂ) * I)) +
          -(((beta * (a - twoEdgeLogMeshPhaseTarget beta theta k) : ℝ) : ℂ) * I) := by
    rw [mul_comm (a : ℂ) (beta : ℂ)]
    rw [show (beta : ℂ) * (a : ℂ) =
        (beta : ℂ) * (twoEdgeLogMeshPhaseTarget beta theta k : ℂ) +
          (beta * (a - twoEdgeLogMeshPhaseTarget beta theta k) : ℝ) by
      push_cast
      ring]
    rw [hpC]
    ring
  rw [hdecomp, Complex.exp_add, Complex.exp_add]
  have hperiod :
      Complex.exp (-((k : ℂ) * (2 * (Real.pi : ℂ) * I))) = 1 := by
    rw [Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I]
    simp
  rw [hperiod]
  ring

theorem tendsto_exp_neg_logMeshPhase
    {beta : ℝ} (hbeta : 0 < beta) (theta : ℝ) :
    Tendsto (fun k ↦ Complex.exp (-((twoEdgeLogMeshPhaseTranslation beta theta k : ℂ) *
        (beta : ℂ) * I))) atTop
      (nhds (Complex.exp (-((theta : ℂ) * I)))) := by
  have herr := tendsto_twoEdgeLogMeshPhaseTranslation_sub_target hbeta theta
  have hscaled : Tendsto (fun k ↦ beta *
      (twoEdgeLogMeshPhaseTranslation beta theta k -
        twoEdgeLogMeshPhaseTarget beta theta k)) atTop (nhds 0) := by
    simpa using herr.const_mul beta
  have hcomplex : Tendsto (fun k ↦
      -(((beta * (twoEdgeLogMeshPhaseTranslation beta theta k -
        twoEdgeLogMeshPhaseTarget beta theta k) : ℝ) : ℂ) * I))
      atTop (nhds 0) := by
    convert (hscaled.ofReal.neg.mul_const I) using 1 <;> simp
  have hexp := hcomplex.cexp
  have hmul := hexp.const_mul (Complex.exp (-((theta : ℂ) * I)))
  convert hmul using 1
  · funext k
    exact exp_neg_logMeshPhase_eq_target_mul_error (ne_of_gt hbeta) theta _ k
  · simp

theorem realExp_re_mul_twoEdgeExponentialMode
    (w P Q : ℂ) (a : ℝ) :
  (Real.exp (a * w.re) : ℂ) * twoEdgeExponentialMode w P Q a =
      Complex.exp (((2 * a * w.re : ℝ) : ℂ) +
          ((a * w.im : ℝ) : ℂ) * I) * P +
        Complex.exp (-(((a * w.im : ℝ) : ℂ) * I)) * Q := by
  rw [twoEdgeExponentialMode]
  have hpos : (a : ℂ) * w =
      ((a * w.re : ℝ) : ℂ) + ((a * w.im : ℝ) : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im w]
    push_cast
    ring
  have hneg : -(a : ℂ) * w =
      -((a * w.re : ℝ) : ℂ) + -((a * w.im : ℝ) : ℂ) * I := by
    rw [show -(a : ℂ) * w = -((a : ℂ) * w) by ring, hpos]
    ring
  rw [hpos, hneg]
  simp only [mul_add, mul_assoc]
  rw [show (Real.exp (a * w.re) : ℂ) =
      Complex.exp ((a * w.re : ℝ) : ℂ) by simp]
  rw [show Complex.exp ((a * w.re : ℝ) : ℂ) *
      (Complex.exp (((a * w.re : ℝ) : ℂ) +
        ((a * w.im : ℝ) : ℂ) * I) * P) =
      (Complex.exp ((a * w.re : ℝ) : ℂ) *
        Complex.exp (((a * w.re : ℝ) : ℂ) +
          ((a * w.im : ℝ) : ℂ) * I)) * P by ring]
  rw [show Complex.exp ((a * w.re : ℝ) : ℂ) *
      (Complex.exp (-((a * w.re : ℝ) : ℂ) +
        -((a * w.im : ℝ) : ℂ) * I) * Q) =
      (Complex.exp ((a * w.re : ℝ) : ℂ) *
        Complex.exp (-((a * w.re : ℝ) : ℂ) +
          -((a * w.im : ℝ) : ℂ) * I)) * Q by ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  apply congrArg₂ (fun x y : ℂ ↦ x + y)
  · congr 1
    push_cast
    ring_nf
  · congr 1
    ring_nf

theorem tendsto_twoEdgeLogMesh_decayingEdge_zero
    {w : ℂ} (hwre : w.re < 0) (hwim : 0 < w.im) (theta : ℝ) (P : ℂ) :
    Tendsto (fun k ↦
      Complex.exp (((2 * twoEdgeLogMeshPhaseTranslation w.im theta k * w.re : ℝ) : ℂ) +
        ((twoEdgeLogMeshPhaseTranslation w.im theta k * w.im : ℝ) : ℂ) * I) * P)
      atTop (nhds 0) := by
  have ha := tendsto_twoEdgeLogMeshPhaseTranslation_atTop hwim theta
  have hbot : Tendsto (fun k ↦
      2 * twoEdgeLogMeshPhaseTranslation w.im theta k * w.re)
      atTop atBot := by
    have hmul := ha.atTop_mul_const_of_neg (by linarith : 2 * w.re < 0)
    convert hmul using 1
    funext k
    ring
  have hexp : Tendsto (fun k ↦ Real.exp
      (2 * twoEdgeLogMeshPhaseTranslation w.im theta k * w.re))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hbot
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert hexp.mul_const ‖P‖ using 1
  · funext k
    rw [norm_mul, Complex.norm_exp]
    simp
  · simp

theorem tendsto_realExp_re_mul_twoEdgeExponentialMode_logMesh
    {w : ℂ} (hwre : w.re < 0) (hwim : 0 < w.im)
    (theta : ℝ) (P Q : ℂ) :
    Tendsto (fun k ↦
      (Real.exp (twoEdgeLogMeshPhaseTranslation w.im theta k * w.re) : ℂ) *
        twoEdgeExponentialMode w P Q
          (twoEdgeLogMeshPhaseTranslation w.im theta k))
      atTop (nhds (Complex.exp (-((theta : ℂ) * I)) * Q)) := by
  have hdecay := tendsto_twoEdgeLogMesh_decayingEdge_zero hwre hwim theta P
  have hphase := tendsto_exp_neg_logMeshPhase hwim theta
  have hgrow := hphase.mul_const Q
  have hsum := hdecay.add hgrow
  convert hsum using 1
  · funext k
    simpa using realExp_re_mul_twoEdgeExponentialMode w P Q
      (twoEdgeLogMeshPhaseTranslation w.im theta k)
  · simp

theorem exists_twoEdgeDominant_nonreal_phase (Q : ℂ) (hQ : Q ≠ 0) :
    ∃ theta : ℝ, (theta = 0 ∨ theta = Real.pi / 2) ∧
      (Complex.exp (-((theta : ℂ) * I)) * Q).im ≠ 0 := by
  by_cases him : Q.im = 0
  · have hre : Q.re ≠ 0 := by
      intro hre
      apply hQ
      apply Complex.ext
      · exact hre
      · exact him
    refine ⟨Real.pi / 2, Or.inr rfl, ?_⟩
    have hexp : Complex.exp (-(((Real.pi / 2 : ℝ) : ℂ) * I)) = -I := by
      rw [show -(((Real.pi / 2 : ℝ) : ℂ) * I) =
          -(Real.pi : ℂ) / 2 * I by push_cast; ring]
      exact Complex.exp_neg_pi_div_two_mul_I
    rw [hexp]
    simp only [Complex.mul_im, I_re, zero_mul, neg_im, I_im,
      neg_mul, one_mul, zero_add]
    exact neg_ne_zero.mpr hre
  · refine ⟨0, Or.inl rfl, ?_⟩
    simpa using him

/-- Off-axis two-edge phase escapes on the exact natural logarithmic aperture mesh. -/
theorem twoEdgeExponentialMode_logMesh_cofinally_nonreal
    {w P Q : ℂ} (hwre : w.re < 0) (hwim : 0 < w.im) (hQ : Q ≠ 0) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (twoEdgeExponentialMode w P Q (Real.log n / 2)).im ≠ 0 := by
  obtain ⟨theta, _, hlimit⟩ := exists_twoEdgeDominant_nonreal_phase Q hQ
  have hscaled :=
    tendsto_realExp_re_mul_twoEdgeExponentialMode_logMesh hwre hwim theta P Q
  have himscaled : Tendsto (fun k ↦
      ((Real.exp (twoEdgeLogMeshPhaseTranslation w.im theta k * w.re) : ℂ) *
        twoEdgeExponentialMode w P Q
          (twoEdgeLogMeshPhaseTranslation w.im theta k)).im)
      atTop (nhds (Complex.exp (-((theta : ℂ) * I)) * Q).im) := by
    simpa [Function.comp_def] using
      (Complex.continuous_im.tendsto _).comp hscaled
  have heventNonzero : ∀ᶠ k in atTop,
      ((Real.exp (twoEdgeLogMeshPhaseTranslation w.im theta k * w.re) : ℂ) *
        twoEdgeExponentialMode w P Q
          (twoEdgeLogMeshPhaseTranslation w.im theta k)).im ≠ 0 :=
    himscaled.eventually_ne hlimit
  have hindex := tendsto_twoEdgeLogMeshPhaseIndex_atTop hwim theta
  intro N
  have heventIndex : ∀ᶠ k in atTop, N ≤ twoEdgeLogMeshPhaseIndex w.im theta k :=
    hindex.eventually_ge_atTop N
  obtain ⟨k, hkIndex, hkNonzero⟩ :=
    (heventIndex.and heventNonzero).exists
  refine ⟨twoEdgeLogMeshPhaseIndex w.im theta k, hkIndex, ?_⟩
  rw [← twoEdgeLogMeshPhaseTranslation]
  intro hzero
  apply hkNonzero
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, hzero, mul_zero, zero_mul,
    add_zero]

/-- Every D2 point has cofinally many nonreal actual physical phases on the exact
natural logarithmic aperture mesh. -/
theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_logMesh_cofinally_nonreal_at_gaussianRatD2
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    {q : ℚ × ℚ}
    (hre : 0 < (gaussianRatPoint q).re)
    (hhalf : (gaussianRatPoint q).re < 1 / 2)
    (hhigh : 233 / 20 < (gaussianRatPoint q).im) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2)
        (primeFluxContourCoordinate (gaussianRatPoint q))).im ≠ 0 := by
  let s : ℂ := gaussianRatPoint q
  let z : ℂ := primeFluxContourCoordinate s
  let w : ℂ := s - 1 / 2
  have hwz : I * z = w := by
    dsimp only [z, w]
    exact I_mul_primeFluxContourCoordinate s
  have hwre_eq : w.re = s.re - 1 / 2 := by simp [w]
  have hwim_eq : w.im = s.im := by simp [w]
  have hwre : w.re < 0 := by
    rw [hwre_eq]
    dsimp only [s]
    linarith
  have hwim : 0 < w.im := by
    rw [hwim_eq]
    dsimp only [s]
    linarith
  have hlower : -1 / 2 < w.re := by
    rw [hwre_eq]
    dsimp only [s]
    linarith
  have hupper : w.re < 1 / 2 := by linarith
  have hQ : xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) ≠ 0 := by
    apply xiPhysicalThetaAbelEntireModeAmplitude_ne_zero_of_openStrip hL hA hc
    · simp only [neg_re]
      linarith
    · simp only [neg_re]
      linarith
    · simp only [neg_re, ne_eq, neg_eq_zero]
      exact ne_of_lt hwre
  intro N
  obtain ⟨n, hnN, hnim⟩ := twoEdgeExponentialMode_logMesh_cofinally_nonreal
    hwre hwim hQ N
  refine ⟨n, hnN, ?_⟩
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform_eq_twoEdgeExponentialMode, hwz]
  exact hnim

/-- Therefore natural aperture sampling does not restore universal real-part order
transport for actual squared physical weights at any D2 point. -/
theorem physicalTwoEdgeSquare_logMesh_cofinally_not_realPartMonotone_at_gaussianRatD2
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    {q : ℚ × ℚ}
    (hre : 0 < (gaussianRatPoint q).re)
    (hhalf : (gaussianRatPoint q).re < 1 / 2)
    (hhigh : 233 / 20 < (gaussianRatPoint q).im) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ¬ ComplexRealPartMonotoneMultiplier
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2)
          (primeFluxContourCoordinate (gaussianRatPoint q)) ^ (2 : ℕ)) := by
  intro N
  obtain ⟨n, hnN, hnim⟩ :=
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_logMesh_cofinally_nonreal_at_gaussianRatD2
      hL hA hc hre hhalf hhigh N
  refine ⟨n, hnN, ?_⟩
  rw [physicalTwoEdgeSquare_realPartMonotone_iff_realPhase]
  exact hnim

end

end RHTower
