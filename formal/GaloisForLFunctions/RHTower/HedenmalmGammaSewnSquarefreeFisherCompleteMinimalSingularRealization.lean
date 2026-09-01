import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherBesselHilbertStabilityWall
import GaloisForLFunctions.HTGeometry.MinimalCompleteSystem
import GaloisForLFunctions.RHTower.DiagonalMultiplierSpectrum
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster
import GaloisForLFunctions.HTGeometry.GeometricThetaUnbounded
import GaloisForLFunctions.RHTower.MobiusCriticalFisherConnectionInertia

/-!
# Complete-minimal singular realization of the physical MSC columns

The Bessel wall leaves one genuine survivor: singular positive Hilbert geometry. This module
classifies how large that survivor is. For every `rho` with positive real part and every aperture
`sigma > 1`, it constructs an exact physical MSC source/overlap realization whose normalized modes
form a complete minimal system in an infinite-dimensional Hilbert space.

Two disjoint cofinal prime subsequences pin the two head coordinates. Every mode also has a private
tail coordinate. The exact MSC coefficient product is at most one, so each tail retains at least
half of the unit energy. Private tails give an explicit biorthogonal system and hence minimality.
Completeness follows because an orthogonal annihilator has vanishing tail coordinates along both
prime subsequences, forcing both head coordinates, and then every private tail coordinate, to zero.

For `Re rho ≤ 1`, the prior Bessel wall makes every such realization violate every finite Bessel
bound. Therefore positivity, infinite dimension, completeness, and minimality have no RH force for
MSC; finite analysis stability is the exact dividing line.
-/

open Complex Filter Set Topology
open scoped Topology InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource.CompleteMinimalSingular

open RHTower
open Classical

abbrev H := lp (fun _ : (Fin 2 ⊕ ℕ) => ℂ) 2

def e0 : H := lp.single 2 (Sum.inl 0) 1
def e1 : H := lp.single 2 (Sum.inl 1) 1
def tail (n : ℕ) : H := lp.single 2 (Sum.inr n) 1

def mode (c d s : ℕ → ℂ) (n : ℕ) : H :=
  c n • e0 + d n • e1 + s n • tail n

theorem inner_mode_left (c d s : ℕ → ℂ) (n : ℕ) (x : H) :
    inner ℂ (mode c d s n) x =
      star (c n) * x (Sum.inl 0) + star (d n) * x (Sum.inl 1) +
        star (s n) * x (Sum.inr n) := by
  simp [mode, e0, e1, tail, lp.inner_single_left]
  ring

theorem inner_mode_mode (c d s : ℕ → ℂ) (n : ℕ) :
    inner ℂ (mode c d s n) (mode c d s n) =
      (‖c n‖ ^ 2 + ‖d n‖ ^ 2 + ‖s n‖ ^ 2 : ℝ) := by
  rw [inner_mode_left]
  simp [mode, e0, e1, tail, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lp.single_apply]
  repeat' rw [mul_comm (starRingEnd ℂ _), Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  norm_cast

theorem norm_mode (c d s : ℕ → ℂ) (n : ℕ)
    (hs : ‖c n‖ ^ 2 + ‖d n‖ ^ 2 + ‖s n‖ ^ 2 = 1) :
    ‖mode c d s n‖ = 1 := by
  have h := inner_mode_mode c d s n
  rw [inner_self_eq_norm_sq_to_K, hs] at h
  norm_num at h
  rcases h with h | h
  · exact h
  · exfalso
    have hr := congrArg Complex.re h
    simp at hr
    nlinarith [norm_nonneg (mode c d s n)]

theorem inner_tail_mode (c d s : ℕ → ℂ) (i j : ℕ) :
    inner ℂ ((star (s i))⁻¹ • tail i) (mode c d s j) =
      if i = j then (s i)⁻¹ * s i else 0 := by
  simp [mode, e0, e1, tail, lp.inner_single_left, lp.single_apply]
  split_ifs with h
  · subst j
    simp [mul_comm]
  · simp [h]

def dualMode (s : ℕ → ℂ) (n : ℕ) : H :=
  (star (s n))⁻¹ • tail n

theorem isDualSystem_mode (c d s : ℕ → ℂ) (hsne : ∀ n, s n ≠ 0) :
    GaloisForLFunctions.HTGeometry.IsDualSystem ℂ (mode c d s) (dualMode s) where
  inner_self i := by
    rw [dualMode, inner_tail_mode]
    simp [hsne i]
  inner_ne i j hij := by
    rw [dualMode, inner_tail_mode]
    simp [hij]

theorem isMinimalSystem_mode (c d s : ℕ → ℂ) (hsne : ∀ n, s n ≠ 0) :
    GaloisForLFunctions.HTGeometry.IsMinimalSystem ℂ (mode c d s) :=
  (isDualSystem_mode c d s hsne).isMinimalSystem

theorem tendsto_mul_zero_of_norm_le_one {f g : ℕ → ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n => f n * g n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg (f n * g n))
    _ (by simpa using hg.norm)
  filter_upwards with n
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_right (hf n) (norm_nonneg (g n))

theorem tendsto_tail_apply {q : ℕ → ℕ} (hq : Function.Injective q) (x : H) :
    Tendsto (fun k => x (Sum.inr (q k))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := GaloisForLFunctions.RHTower.tendsto_inner_lp_single_zero
    (q := fun k => Sum.inr (q k)) (Sum.inr_injective.comp hq) x
  rw [tendsto_zero_iff_norm_tendsto_zero] at h
  simpa [lp.inner_single_right, RCLike.inner_apply] using h

theorem isCompleteSystem_mode
    (c d s : ℕ → ℂ) (q r : ℕ → ℕ)
    (hq : Function.Injective q) (hr : Function.Injective r)
    (hcq : ∀ k, ‖c (q k)‖ = 1 / 2)
    (hdr : ∀ k, ‖d (r k)‖ = 1 / 2)
    (hdq : Tendsto (fun k => d (q k)) atTop (𝓝 0))
    (hcr : Tendsto (fun k => c (r k)) atTop (𝓝 0))
    (hsle : ∀ n, ‖s n‖ ≤ 1) (hsne : ∀ n, s n ≠ 0) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ (mode c d s) := by
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero]
  intro x hx
  have hxq : Tendsto
      (fun k => star (s (q k)) * x (Sum.inr (q k))) atTop (𝓝 0) := by
    apply tendsto_mul_zero_of_norm_le_one
    · intro k
      simpa using hsle (q k)
    · exact tendsto_tail_apply hq x
  have hdx : Tendsto (fun k => star (d (q k)) * x (Sum.inl 1)) atTop (𝓝 0) := by
    simpa using hdq.star.mul_const (x (Sum.inl 1))
  have hleftq : Tendsto
      (fun k => star (c (q k)) * x (Sum.inl 0)) atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun k => -(star (d (q k)) * x (Sum.inl 1) +
          star (s (q k)) * x (Sum.inr (q k)))) atTop (𝓝 0) := by
      simpa using (hdx.add hxq).neg
    have heq : (fun k => star (c (q k)) * x (Sum.inl 0)) =
        fun k => -(star (d (q k)) * x (Sum.inl 1) +
          star (s (q k)) * x (Sum.inr (q k))) := by
      funext k
      have hk := hx (q k)
      rw [inner_mode_left] at hk
      linear_combination hk
    rw [heq]
    exact hsum
  have hleftqnorm : Tendsto
      (fun k => ‖star (c (q k)) * x (Sum.inl 0)‖) atTop (𝓝 0) := by
    simpa using hleftq.norm
  have hconstq : (fun k => ‖star (c (q k)) * x (Sum.inl 0)‖) =
      fun _ : ℕ => (1 / 2 : ℝ) * ‖x (Sum.inl 0)‖ := by
    funext k
    rw [norm_mul, norm_star, hcq]
  rw [hconstq] at hleftqnorm
  have hx0norm : (1 / 2 : ℝ) * ‖x (Sum.inl 0)‖ = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hleftqnorm
  have hx0 : x (Sum.inl 0) = 0 := by
    rw [mul_eq_zero] at hx0norm
    exact norm_eq_zero.mp (hx0norm.resolve_left (by norm_num))
  have hxr : Tendsto
      (fun k => star (s (r k)) * x (Sum.inr (r k))) atTop (𝓝 0) := by
    apply tendsto_mul_zero_of_norm_le_one
    · intro k
      simpa using hsle (r k)
    · exact tendsto_tail_apply hr x
  have hcx : Tendsto (fun k => star (c (r k)) * x (Sum.inl 0)) atTop (𝓝 0) := by
    simpa using hcr.star.mul_const (x (Sum.inl 0))
  have hleftr : Tendsto
      (fun k => star (d (r k)) * x (Sum.inl 1)) atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun k => -(star (c (r k)) * x (Sum.inl 0) +
          star (s (r k)) * x (Sum.inr (r k)))) atTop (𝓝 0) := by
      simpa using (hcx.add hxr).neg
    have heq : (fun k => star (d (r k)) * x (Sum.inl 1)) =
        fun k => -(star (c (r k)) * x (Sum.inl 0) +
          star (s (r k)) * x (Sum.inr (r k))) := by
      funext k
      have hk := hx (r k)
      rw [inner_mode_left] at hk
      linear_combination hk
    rw [heq]
    exact hsum
  have hleftrnorm : Tendsto
      (fun k => ‖star (d (r k)) * x (Sum.inl 1)‖) atTop (𝓝 0) := by
    simpa using hleftr.norm
  have hconstr : (fun k => ‖star (d (r k)) * x (Sum.inl 1)‖) =
      fun _ : ℕ => (1 / 2 : ℝ) * ‖x (Sum.inl 1)‖ := by
    funext k
    rw [norm_mul, norm_star, hdr]
  rw [hconstr] at hleftrnorm
  have hx1norm : (1 / 2 : ℝ) * ‖x (Sum.inl 1)‖ = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hleftrnorm
  have hx1 : x (Sum.inl 1) = 0 := by
    rw [mul_eq_zero] at hx1norm
    exact norm_eq_zero.mp (hx1norm.resolve_left (by norm_num))
  apply lp.ext
  funext i
  rcases i with i | n
  · fin_cases i <;> assumption
  · have hn := hx n
    rw [inner_mode_left, hx0, hx1] at hn
    simp only [mul_zero, zero_add] at hn
    exact (mul_eq_zero.mp hn).resolve_left (star_ne_zero.mpr (hsne n))

def sourceAnchorIndex (k : ℕ) : ℕ :=
  (RHTower.nthPrimeSubtype (2 * k + 1) : ℕ)

def overlapAnchorIndex (k : ℕ) : ℕ :=
  (RHTower.nthPrimeSubtype (2 * k + 2) : ℕ)

theorem sourceAnchorIndex_injective : Function.Injective sourceAnchorIndex := by
  intro i j h
  have hidx := RHTower.nthPrimeSubtype_strictMono.injective h
  omega

theorem overlapAnchorIndex_injective : Function.Injective overlapAnchorIndex := by
  intro i j h
  have hidx := RHTower.nthPrimeSubtype_strictMono.injective h
  omega

theorem sourceAnchorIndex_prime (k : ℕ) : Nat.Prime (sourceAnchorIndex k) :=
  (RHTower.nthPrimeSubtype (2 * k + 1)).prop

theorem overlapAnchorIndex_prime (k : ℕ) : Nat.Prime (overlapAnchorIndex k) :=
  (RHTower.nthPrimeSubtype (2 * k + 2)).prop

theorem sourceAnchorIndex_squarefree (k : ℕ) : Squarefree (sourceAnchorIndex k) :=
  (sourceAnchorIndex_prime k).squarefree

theorem overlapAnchorIndex_squarefree (k : ℕ) : Squarefree (overlapAnchorIndex k) :=
  (overlapAnchorIndex_prime k).squarefree

theorem overlapAnchorIndex_not_mem_sourceRange (k : ℕ) :
    overlapAnchorIndex k ∉ Set.range sourceAnchorIndex := by
  rintro ⟨j, hj⟩
  have hidx := RHTower.nthPrimeSubtype_strictMono.injective hj
  omega

theorem sourceAnchorIndex_not_mem_overlapRange (k : ℕ) :
    sourceAnchorIndex k ∉ Set.range overlapAnchorIndex := by
  rintro ⟨j, hj⟩
  have hidx := RHTower.nthPrimeSubtype_strictMono.injective hj
  omega

def sourceWeight (rho : ℂ) (sigma : ℝ) (n : ℕ) : ℂ :=
  RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
    (RHTower.mscPhysicalZeroCoordinate rho sigma) n

def overlapWeight (sigma : ℝ) (n : ℕ) : ℂ :=
  RHTower.infiniteMobiusSignedWeight sigma n

def productWeight (rho : ℂ) (sigma : ℝ) (n : ℕ) : ℝ :=
  ‖sourceWeight rho sigma n‖ * ‖overlapWeight sigma n‖

theorem productWeight_eq
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    productWeight rho sigma n =
      RHTower.squarefreeMobiusMass rho.re n /
        RHTower.squarefreeMobiusTotal sigma := by
  exact RHTower.HedenmalmThetaSource.norm_mul_norm_mscPhysicalSource_eq
    rho hsigma n

theorem squarefreeMobiusMass_le_one_of_pos
    {u : ℝ} (hu : 0 < u) (n : ℕ) :
    RHTower.squarefreeMobiusMass u n ≤ 1 := by
  rw [RHTower.squarefreeMobiusMass]
  split_ifs with hn
  · have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact not_squarefree_zero hn
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0) (by linarith)
  · norm_num

theorem one_le_squarefreeMobiusTotal
    {sigma : ℝ} (hsigma : 1 < sigma) :
    1 ≤ RHTower.squarefreeMobiusTotal sigma := by
  calc
    1 = RHTower.squarefreeMobiusMass sigma 1 := by
      simp [RHTower.squarefreeMobiusMass]
    _ ≤ ∑' n : ℕ, RHTower.squarefreeMobiusMass sigma n :=
      (RHTower.summable_squarefreeMobiusMass hsigma).le_tsum 1
        (fun j _ => RHTower.squarefreeMobiusMass_nonneg sigma j)
    _ = RHTower.squarefreeMobiusTotal sigma := rfl

theorem productWeight_le_one
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) (n : ℕ) :
    productWeight rho sigma n ≤ 1 := by
  rw [productWeight_eq rho hsigma]
  apply (div_le_one (RHTower.squarefreeMobiusTotal_pos hsigma)).2
  exact (squarefreeMobiusMass_le_one_of_pos hrho n).trans
    (one_le_squarefreeMobiusTotal hsigma)

theorem overlapWeight_ne_zero_of_squarefree
    {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ} (hn : Squarefree n) :
    overlapWeight sigma n ≠ 0 :=
  RHTower.infiniteMobiusSignedWeight_ne_zero_of_squarefree hsigma hn

theorem sourceWeight_ne_zero_of_squarefree
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ} (hn : Squarefree n) :
    sourceWeight rho sigma n ≠ 0 := by
  rw [sourceWeight,
    RHTower.infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp]
  exact mul_ne_zero (Complex.exp_ne_zero _) (overlapWeight_ne_zero_of_squarefree hsigma hn)

theorem sourceAnchorIndex_strictMono : StrictMono sourceAnchorIndex := by
  intro i j hij
  apply RHTower.nthPrimeSubtype_strictMono
  omega

theorem overlapAnchorIndex_strictMono : StrictMono overlapAnchorIndex := by
  intro i j hij
  apply RHTower.nthPrimeSubtype_strictMono
  omega

theorem tendsto_productWeight_sourceAnchor
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) :
    Tendsto (fun k => productWeight rho sigma (sourceAnchorIndex k))
      atTop (𝓝 0) := by
  have hpow :=
    (GaloisForLFunctions.HTGeometry.tendsto_natCast_rpow_neg_atTop hrho).comp
      sourceAnchorIndex_strictMono.tendsto_atTop
  have hdiv := hpow.div_const (RHTower.squarefreeMobiusTotal sigma)
  have hdiv0 : Tendsto
      (fun k => ((sourceAnchorIndex k : ℝ) ^ (-rho.re)) /
        RHTower.squarefreeMobiusTotal sigma) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hdiv
  apply hdiv0.congr'
  filter_upwards with k
  rw [productWeight_eq rho hsigma, RHTower.squarefreeMobiusMass,
    if_pos (sourceAnchorIndex_squarefree k)]

theorem tendsto_productWeight_overlapAnchor
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) :
    Tendsto (fun k => productWeight rho sigma (overlapAnchorIndex k))
      atTop (𝓝 0) := by
  have hpow :=
    (GaloisForLFunctions.HTGeometry.tendsto_natCast_rpow_neg_atTop hrho).comp
      overlapAnchorIndex_strictMono.tendsto_atTop
  have hdiv := hpow.div_const (RHTower.squarefreeMobiusTotal sigma)
  have hdiv0 : Tendsto
      (fun k => ((overlapAnchorIndex k : ℝ) ^ (-rho.re)) /
        RHTower.squarefreeMobiusTotal sigma) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hdiv
  apply hdiv0.congr'
  filter_upwards with k
  rw [productWeight_eq rho hsigma, RHTower.squarefreeMobiusMass,
    if_pos (overlapAnchorIndex_squarefree k)]

def singularModeNorm (rho : ℂ) (sigma : ℝ) (n : ℕ) : ℝ :=
  if n ∈ Set.range overlapAnchorIndex then ‖overlapWeight sigma n‖
  else if Squarefree n then ‖sourceWeight rho sigma n‖⁻¹
  else 1

theorem singularModeNorm_pos
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    0 < singularModeNorm rho sigma n := by
  classical
  rw [singularModeNorm]
  split_ifs with hB hn
  · obtain ⟨k, rfl⟩ := hB
    exact norm_pos_iff.mpr
      (overlapWeight_ne_zero_of_squarefree hsigma (overlapAnchorIndex_squarefree k))
  · exact inv_pos.mpr (norm_pos_iff.mpr (sourceWeight_ne_zero_of_squarefree rho hsigma hn))
  · norm_num

def sourceHeadCoeff (rho : ℂ) (sigma : ℝ) (n : ℕ) : ℂ :=
  sourceWeight rho sigma n * (singularModeNorm rho sigma n : ℂ) / 2

def overlapHeadCoeff (rho : ℂ) (sigma : ℝ) (n : ℕ) : ℂ :=
  overlapWeight sigma n / ((singularModeNorm rho sigma n : ℂ) * 2)

theorem norm_sourceHeadCoeff_of_overlapAnchor
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (k : ℕ) :
    ‖sourceHeadCoeff rho sigma (overlapAnchorIndex k)‖ =
      productWeight rho sigma (overlapAnchorIndex k) / 2 := by
  have hbpos : 0 < ‖overlapWeight sigma (overlapAnchorIndex k)‖ :=
    norm_pos_iff.mpr
      (overlapWeight_ne_zero_of_squarefree hsigma (overlapAnchorIndex_squarefree k))
  rw [sourceHeadCoeff, singularModeNorm, if_pos ⟨k, rfl⟩,
    norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hbpos, norm_ofNat, productWeight]

theorem norm_overlapHeadCoeff_of_overlapAnchor
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (k : ℕ) :
    ‖overlapHeadCoeff rho sigma (overlapAnchorIndex k)‖ = 1 / 2 := by
  have hbpos : 0 < ‖overlapWeight sigma (overlapAnchorIndex k)‖ :=
    norm_pos_iff.mpr
      (overlapWeight_ne_zero_of_squarefree hsigma (overlapAnchorIndex_squarefree k))
  rw [overlapHeadCoeff, singularModeNorm, if_pos ⟨k, rfl⟩,
    norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hbpos, norm_ofNat]
  field_simp

theorem norm_sourceHeadCoeff_of_sourceAnchor
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (k : ℕ) :
    ‖sourceHeadCoeff rho sigma (sourceAnchorIndex k)‖ = 1 / 2 := by
  have hapos : 0 < ‖sourceWeight rho sigma (sourceAnchorIndex k)‖ :=
    norm_pos_iff.mpr
      (sourceWeight_ne_zero_of_squarefree rho hsigma (sourceAnchorIndex_squarefree k))
  rw [sourceHeadCoeff, singularModeNorm,
    if_neg (sourceAnchorIndex_not_mem_overlapRange k),
    if_pos (sourceAnchorIndex_squarefree k), norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos),
    norm_ofNat]
  field_simp

theorem norm_overlapHeadCoeff_of_sourceAnchor
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (k : ℕ) :
    ‖overlapHeadCoeff rho sigma (sourceAnchorIndex k)‖ =
      productWeight rho sigma (sourceAnchorIndex k) / 2 := by
  have hapos : 0 < ‖sourceWeight rho sigma (sourceAnchorIndex k)‖ :=
    norm_pos_iff.mpr
      (sourceWeight_ne_zero_of_squarefree rho hsigma (sourceAnchorIndex_squarefree k))
  rw [overlapHeadCoeff, singularModeNorm,
    if_neg (sourceAnchorIndex_not_mem_overlapRange k),
    if_pos (sourceAnchorIndex_squarefree k), norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos),
    norm_ofNat, productWeight]
  field_simp

theorem norm_sourceHeadCoeff_of_mem_overlapRange
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ}
    (hB : n ∈ Set.range overlapAnchorIndex) :
    ‖sourceHeadCoeff rho sigma n‖ = productWeight rho sigma n / 2 := by
  obtain ⟨k, rfl⟩ := hB
  exact norm_sourceHeadCoeff_of_overlapAnchor rho hsigma k

theorem norm_overlapHeadCoeff_of_mem_overlapRange
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ}
    (hB : n ∈ Set.range overlapAnchorIndex) :
    ‖overlapHeadCoeff rho sigma n‖ = 1 / 2 := by
  obtain ⟨k, rfl⟩ := hB
  exact norm_overlapHeadCoeff_of_overlapAnchor rho hsigma k

theorem norm_sourceHeadCoeff_of_not_mem_overlapRange_of_squarefree
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ}
    (hB : n ∉ Set.range overlapAnchorIndex) (hn : Squarefree n) :
    ‖sourceHeadCoeff rho sigma n‖ = 1 / 2 := by
  have hapos : 0 < ‖sourceWeight rho sigma n‖ :=
    norm_pos_iff.mpr (sourceWeight_ne_zero_of_squarefree rho hsigma hn)
  rw [sourceHeadCoeff, singularModeNorm, if_neg hB, if_pos hn,
    norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hapos), norm_ofNat]
  field_simp

theorem norm_overlapHeadCoeff_of_not_mem_overlapRange_of_squarefree
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ}
    (hB : n ∉ Set.range overlapAnchorIndex) (hn : Squarefree n) :
    ‖overlapHeadCoeff rho sigma n‖ = productWeight rho sigma n / 2 := by
  have hapos : 0 < ‖sourceWeight rho sigma n‖ :=
    norm_pos_iff.mpr (sourceWeight_ne_zero_of_squarefree rho hsigma hn)
  rw [overlapHeadCoeff, singularModeNorm, if_neg hB, if_pos hn,
    norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hapos), norm_ofNat, productWeight]
  field_simp

theorem sourceWeight_eq_zero_of_not_squarefree
    (rho : ℂ) (sigma : ℝ) {n : ℕ} (hn : ¬ Squarefree n) :
    sourceWeight rho sigma n = 0 := by
  rw [sourceWeight,
    RHTower.infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp,
    RHTower.infiniteMobiusSignedWeight]
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  simp

theorem overlapWeight_eq_zero_of_not_squarefree
    (sigma : ℝ) {n : ℕ} (hn : ¬ Squarefree n) :
    overlapWeight sigma n = 0 := by
  rw [overlapWeight, RHTower.infiniteMobiusSignedWeight]
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  simp

theorem headEnergy_le_half
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) (n : ℕ) :
    ‖sourceHeadCoeff rho sigma n‖ ^ 2 +
      ‖overlapHeadCoeff rho sigma n‖ ^ 2 ≤ 1 / 2 := by
  by_cases hB : n ∈ Set.range overlapAnchorIndex
  · rw [norm_sourceHeadCoeff_of_mem_overlapRange rho hsigma hB,
      norm_overlapHeadCoeff_of_mem_overlapRange rho hsigma hB]
    have hp0 : 0 ≤ productWeight rho sigma n := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hp1 := productWeight_le_one rho hsigma hrho n
    nlinarith
  · by_cases hn : Squarefree n
    · rw [norm_sourceHeadCoeff_of_not_mem_overlapRange_of_squarefree rho hsigma hB hn,
        norm_overlapHeadCoeff_of_not_mem_overlapRange_of_squarefree rho hsigma hB hn]
      have hp0 : 0 ≤ productWeight rho sigma n := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hp1 := productWeight_le_one rho hsigma hrho n
      nlinarith
    · rw [sourceHeadCoeff, overlapHeadCoeff,
        sourceWeight_eq_zero_of_not_squarefree rho sigma hn,
        overlapWeight_eq_zero_of_not_squarefree sigma hn]
      simp

def tailCoeff (rho : ℂ) (sigma : ℝ) (n : ℕ) : ℂ :=
  Real.sqrt (1 - (‖sourceHeadCoeff rho sigma n‖ ^ 2 +
    ‖overlapHeadCoeff rho sigma n‖ ^ 2))

theorem tailCoeff_norm_sq
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) (n : ℕ) :
    ‖tailCoeff rho sigma n‖ ^ 2 =
      1 - (‖sourceHeadCoeff rho sigma n‖ ^ 2 +
        ‖overlapHeadCoeff rho sigma n‖ ^ 2) := by
  rw [tailCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
  linarith [headEnergy_le_half rho hsigma hrho n]

theorem tailCoeff_ne_zero
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) (n : ℕ) :
    tailCoeff rho sigma n ≠ 0 := by
  rw [← norm_pos_iff, tailCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_pos.2 (by linarith [headEnergy_le_half rho hsigma hrho n])

theorem norm_tailCoeff_le_one
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) (n : ℕ) :
    ‖tailCoeff rho sigma n‖ ≤ 1 := by
  have hs := tailCoeff_norm_sq rho hsigma hrho n
  have hnonneg : 0 ≤ ‖sourceHeadCoeff rho sigma n‖ ^ 2 +
      ‖overlapHeadCoeff rho sigma n‖ ^ 2 := by positivity
  nlinarith [norm_nonneg (tailCoeff rho sigma n)]

def normalizedSingularMode (rho : ℂ) (sigma : ℝ) : ℕ → H :=
  mode (sourceHeadCoeff rho sigma) (overlapHeadCoeff rho sigma) (tailCoeff rho sigma)

theorem norm_normalizedSingularMode
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) (n : ℕ) :
    ‖normalizedSingularMode rho sigma n‖ = 1 := by
  apply norm_mode
  rw [tailCoeff_norm_sq rho hsigma hrho n]
  ring

theorem tendsto_overlapHeadCoeff_sourceAnchor
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) :
    Tendsto (fun k => overlapHeadCoeff rho sigma (sourceAnchorIndex k))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_productWeight_sourceAnchor rho hsigma hrho).div_const 2
  have h0 : Tendsto
      (fun k => productWeight rho sigma (sourceAnchorIndex k) / 2)
      atTop (𝓝 0) := by simpa using h
  apply h0.congr'
  filter_upwards with k
  exact (norm_overlapHeadCoeff_of_sourceAnchor rho hsigma k).symm

theorem tendsto_sourceHeadCoeff_overlapAnchor
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) :
    Tendsto (fun k => sourceHeadCoeff rho sigma (overlapAnchorIndex k))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_productWeight_overlapAnchor rho hsigma hrho).div_const 2
  have h0 : Tendsto
      (fun k => productWeight rho sigma (overlapAnchorIndex k) / 2)
      atTop (𝓝 0) := by simpa using h
  apply h0.congr'
  filter_upwards with k
  exact (norm_sourceHeadCoeff_of_overlapAnchor rho hsigma k).symm

theorem isCompleteSystem_normalizedSingularMode
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ
      (normalizedSingularMode rho sigma) := by
  apply isCompleteSystem_mode
    (q := sourceAnchorIndex) (r := overlapAnchorIndex)
  · exact sourceAnchorIndex_injective
  · exact overlapAnchorIndex_injective
  · exact norm_sourceHeadCoeff_of_sourceAnchor rho hsigma
  · exact norm_overlapHeadCoeff_of_overlapAnchor rho hsigma
  · exact tendsto_overlapHeadCoeff_sourceAnchor rho hsigma hrho
  · exact tendsto_sourceHeadCoeff_overlapAnchor rho hsigma hrho
  · exact norm_tailCoeff_le_one rho hsigma hrho
  · exact tailCoeff_ne_zero rho hsigma hrho

theorem isMinimalSystem_normalizedSingularMode
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) :
    GaloisForLFunctions.HTGeometry.IsMinimalSystem ℂ
      (normalizedSingularMode rho sigma) := by
  exact isMinimalSystem_mode _ _ _ (tailCoeff_ne_zero rho hsigma hrho)

def singularMode (rho : ℂ) (sigma : ℝ) (n : ℕ) : H :=
  (singularModeNorm rho sigma n : ℂ) • normalizedSingularMode rho sigma n

theorem norm_singularMode
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) (n : ℕ) :
    ‖singularMode rho sigma n‖ = singularModeNorm rho sigma n := by
  rw [singularMode, norm_smul, norm_normalizedSingularMode rho hsigma hrho,
    mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (singularModeNorm_pos rho hsigma n)]

theorem singularMode_ne_zero
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) (n : ℕ) :
    singularMode rho sigma n ≠ 0 := by
  rw [← norm_pos_iff, norm_singularMode rho hsigma hrho]
  exact singularModeNorm_pos rho hsigma n

theorem normalized_singularMode
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) (n : ℕ) :
    RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode
      (singularMode rho sigma) n = normalizedSingularMode rho sigma n := by
  have ht : (singularModeNorm rho sigma n : ℂ) ≠ 0 := by
    exact_mod_cast (singularModeNorm_pos rho hsigma n).ne'
  rw [RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode,
    norm_singularMode rho hsigma hrho, singularMode, smul_smul,
    inv_mul_cancel₀ ht, one_smul]

def singularSource : H := 2 • e0
def singularOverlap : H := 2 • e1

theorem inner_normalizedSingularMode_source
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    inner ℂ (normalizedSingularMode rho sigma n) singularSource =
      star (sourceWeight rho sigma n) * singularModeNorm rho sigma n := by
  have ht := (singularModeNorm_pos rho hsigma n).ne'
  rw [normalizedSingularMode, inner_mode_left]
  simp [singularSource, e0, sourceHeadCoeff, RCLike.star_def]

theorem inner_normalizedSingularMode_overlap
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    inner ℂ (normalizedSingularMode rho sigma n) singularOverlap =
      star (overlapWeight sigma n) / singularModeNorm rho sigma n := by
  have ht := (singularModeNorm_pos rho hsigma n).ne'
  rw [normalizedSingularMode, inner_mode_left]
  simp [singularOverlap, e1, overlapHeadCoeff, RCLike.star_def]
  field_simp

def IsMSCPhysicalOverlapCompleteMinimalHilbertRealization
    (rho : ℂ) (sigma : ℝ) (modes : ℕ → H) (source overlap : H) : Prop :=
  RHTower.HedenmalmThetaSource.IsMSCPhysicalOverlapHilbertRealization
      rho sigma modes source overlap ∧
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ
      (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes) ∧
    GaloisForLFunctions.HTGeometry.IsMinimalSystem ℂ
      (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes)

theorem isMSCPhysicalOverlapHilbertRealization_singular
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) :
    RHTower.HedenmalmThetaSource.IsMSCPhysicalOverlapHilbertRealization
      rho sigma (singularMode rho sigma) singularSource singularOverlap := by
  refine ⟨singularMode_ne_zero rho hsigma hrho, ?_, ?_⟩
  · intro n
    rw [normalized_singularMode rho hsigma hrho,
      inner_normalizedSingularMode_source rho hsigma,
      norm_singularMode rho hsigma hrho]
    rfl
  · intro n
    rw [normalized_singularMode rho hsigma hrho,
      inner_normalizedSingularMode_overlap rho hsigma,
      norm_singularMode rho hsigma hrho]
    rfl

theorem isMSCPhysicalOverlapCompleteMinimalHilbertRealization_singular
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) :
    IsMSCPhysicalOverlapCompleteMinimalHilbertRealization rho sigma
      (singularMode rho sigma) singularSource singularOverlap := by
  refine ⟨isMSCPhysicalOverlapHilbertRealization_singular rho hsigma hrho, ?_, ?_⟩
  · rw [show RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode
        (singularMode rho sigma) = normalizedSingularMode rho sigma by
      funext n
      exact normalized_singularMode rho hsigma hrho n]
    exact isCompleteSystem_normalizedSingularMode rho hsigma hrho
  · rw [show RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode
        (singularMode rho sigma) = normalizedSingularMode rho sigma by
      funext n
      exact normalized_singularMode rho hsigma hrho n]
    exact isMinimalSystem_normalizedSingularMode rho hsigma hrho

theorem exists_mscPhysicalOverlapCompleteMinimalHilbertRealization
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re) :
    ∃ (modes : ℕ → H) (source overlap : H),
      IsMSCPhysicalOverlapCompleteMinimalHilbertRealization
        rho sigma modes source overlap := by
  exact ⟨singularMode rho sigma, singularSource, singularOverlap,
    isMSCPhysicalOverlapCompleteMinimalHilbertRealization_singular rho hsigma hrho⟩

theorem exists_mscPhysicalOverlapCompleteMinimalNonBesselRealization
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma)
    (hrho0 : 0 < rho.re) (hrho1 : rho.re ≤ 1) :
    ∃ (modes : ℕ → H) (source overlap : H),
      IsMSCPhysicalOverlapCompleteMinimalHilbertRealization
        rho sigma modes source overlap ∧
      ∀ B : ℝ, ∃ packet : Finset ℕ, ∃ x : H,
        B * ‖x‖ ^ 2 <
          ∑ n ∈ packet,
            ‖inner ℂ
              (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes n) x‖ ^ 2 := by
  refine ⟨singularMode rho sigma, singularSource, singularOverlap,
    isMSCPhysicalOverlapCompleteMinimalHilbertRealization_singular rho hsigma hrho0, ?_⟩
  intro B
  exact RHTower.HedenmalmThetaSource.exists_besselViolation_of_re_le_one
    rho hsigma hrho1 (singularMode rho sigma) singularSource singularOverlap
      (isMSCPhysicalOverlapHilbertRealization_singular rho hsigma hrho0) B

/-- Strict-right route kill. The actual four-unit MSC regular germ coexists with an explicit
infinite-dimensional positive complete-minimal realization of both literal arithmetic columns.
That realization violates every finite Bessel bound. Thus completeness and minimality do not
convert the MSC germ into RH; a proof must manufacture genuine analysis stability. -/
theorem strictRightXiZero_mscCompleteMinimalSingularRouteKill
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : RHTower.xi rho = 0) {sigma : ℝ} (hsigma : 1 < sigma) :
    (∃ k : ℕ, analyticOrderAt RHTower.xi rho = (k + 1 : ℕ) ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧
        (∀ tau : ℝ, 1 < tau →
          AnalyticAt ℂ (RHTower.mscPhysicalRegularGerm rho g tau)
              (RHTower.mscPhysicalZeroCoordinate rho tau) ∧
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                  (tau : ℂ) ((tau - 1 : ℝ) : ℂ) v /
                GaloisForLFunctions.squarefreeBoundaryOverlap
                  (tau : ℂ) ((tau - 1 : ℝ) : ℂ) v) =ᶠ[
              𝓝[≠] (RHTower.mscPhysicalZeroCoordinate rho tau)]
                fun v => 2 * ((k + 1 : ℕ) : ℂ) /
                  (v - RHTower.mscPhysicalZeroCoordinate rho tau) +
                    RHTower.mscPhysicalRegularGerm rho g tau v) ∧
          Tendsto
            (fun tau : ℝ =>
              Complex.normSq
                (RHTower.mscPhysicalRegularGerm rho g tau
                  (RHTower.mscPhysicalZeroCoordinate rho tau)))
            (nhdsWithin 1 (Set.Ioi 1)) (nhds 4)) ∧
      ∃ (modes : ℕ → H) (source overlap : H),
        IsMSCPhysicalOverlapCompleteMinimalHilbertRealization
          rho sigma modes source overlap ∧
        ∀ B : ℝ, ∃ packet : Finset ℕ, ∃ x : H,
          B * ‖x‖ ^ 2 <
            ∑ n ∈ packet,
              ‖inner ℂ
                (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes n) x‖ ^ 2 := by
  have hcm := isMSCPhysicalOverlapCompleteMinimalHilbertRealization_singular
    rho hsigma (by linarith : 0 < rho.re)
  have hwall := RHTower.HedenmalmThetaSource.strictRightXiZero_mscBesselHilbertStabilityWall
    hhalf hone hzero hsigma (singularMode rho sigma) singularSource singularOverlap
  rcases hwall with ⟨hregular, _, hviolation⟩
  exact ⟨hregular, singularMode rho sigma, singularSource, singularOverlap,
    hcm, hviolation hcm.1⟩

end RHTower.HedenmalmThetaSource.CompleteMinimalSingular
