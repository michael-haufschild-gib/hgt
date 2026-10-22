import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfArithmeticWeld
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinFullXiSum
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitGlobalZeroCount
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# The selected zeta-zero Mellin packet in Route T tends to zero

Let `N_X = X^{1000/299}`, `H_X = N_X / X^{999/1000}` and let `K_X(s)` be the width-normalized
Mellin transform `H_X⁻¹ ∫ w(x) x^{s-1} dx` of the smooth window
`w = smoothWeight(N_X + H_X, H_X) - smoothWeight(N_X, H_X)`, supported in `[N_X, N_X + 2H_X]`
(`routeTNormalizedSmoothWindowMellin`). The contour residue packet
`2πi ∑ ord_w((s-1)ζ) K_X(w)`, over the zeros `w` of `(s-1)ζ(s)` in the rectangle
`[-1/2, 2] × [-T_X, T_X]` at the selected height `T_X ∈ (X-3, X-2)`, is rewritten as `2πi` times a
sum of `K_X(ρ)` over multiplicity copies of the zeros `ρ` of `ξ` with `|Im ρ| ≤ T_X`. Splitting at
`Re ρ = 7/10`, the low-real part is bounded with the global zero count and `|K_X(ρ)| ≤ N_X^{Re ρ - 1}`
by `O(X log X · X^{-300/299})`, and the high-real part by the physical high-zero weighted mass,
which tends to zero by the imported zero-density estimate. Hence the whole packet tends to zero.

## Main results

- `routeTSelectedXiSupport_map_eq_zetaZeros`: for `T ≥ 0`, the distinct `ξ` zeros with
  `|Im ρ| ≤ T` are exactly the zeros of `(s-1)ζ(s)` in `[-1/2, 2] × [-T, T]`.
- `routeTSelectedZetaMultiplicitySum_eq_xiCopySum`: the multiplicity-weighted zeta-zero sum of
  `K` over that rectangle equals the sum of `K` over `ξ` zero copies.
- `norm_inghamRouteTBufferedSelectedXiMellinLowRealPacket_le`: the `Re ρ < 7/10` part has norm at
  most `C (1 + X) log(2 + X) X^{-300/299}` for `X ≥ 12`.
- `norm_inghamRouteTBufferedSelectedXiMellinHighRealPacket_le`: the `Re ρ ≥ 7/10` part is at most
  `inghamRouteTHighZeroWeightedMass X` for `X ≥ 12`.
- `tendsto_inghamRouteTBufferedSelectedXiMellinPacket_zero`: the full `ξ`-zero Mellin packet tends
  to `0` as `X → ∞`.
- `inghamRouteTBufferedSelectedNegativeHalfZeroPacket_eq_xiPacket`,
  `tendsto_inghamRouteTBufferedSelectedNegativeHalfZeroPacket_zero`: the selected contour zero
  packet equals `2πi` times the `ξ` packet and tends to `0`.

## Hypotheses

The main results are unconditional: the statements take no analytic premise. The only conditions
are `T ≥ 0` for the zero correspondence and `X ≥ 12` for the explicit bounds; the limits are as
`X → ∞`.
-/

open Complex Filter Topology Set Finset
open RHTower RHTower.Sieve

namespace RHTower.Sieve

noncomputable section

/-- The divisor multiplicity of a zero `ρ` of `ξ` equals its analytic order `ord_ρ ξ`. -/
theorem routeT_xiSupportMultiplicity_eq_analyticOrderAt_toNat
    (rho : RHTower.XiDivisorSupport) :
    RHTower.xiSupportMultiplicity rho =
      (analyticOrderAt RHTower.xi (rho : ℂ)).toNat := by
  rw [RHTower.xiSupportMultiplicity,
    MeromorphicOn.divisor_apply RHTower.xi_analyticOnNhd_univ.meromorphicOn
      (Set.mem_univ (rho : ℂ)),
    (RHTower.xi_analyticOnNhd_univ (rho : ℂ) (Set.mem_univ _)).meromorphicOrderAt_eq]
  have hcoe : ((((analyticOrderAt RHTower.xi (rho : ℂ)).toNat : ℕ) : ℕ∞)) =
      analyticOrderAt RHTower.xi (rho : ℂ) :=
    ENat.coe_toNat (RHTower.xi_orderAt_ne_top (rho : ℂ))
  rw [← hcoe]
  simp

def routeTSelectedXiSupportValEmbedding : RHTower.XiDivisorSupport ↪ ℂ where
  toFun rho := (rho : ℂ)
  inj' := Subtype.coe_injective

def routeTSelectedXiSpectralLower (T : ℝ) : ℂ :=
  ((-T : ℝ) : ℂ) + ((-(1 / 2 : ℝ) : ℝ) : ℂ) * I

def routeTSelectedXiSpectralUpper (T : ℝ) : ℂ :=
  ((T : ℝ) : ℂ) + (((1 / 2 : ℝ) : ℝ) : ℂ) * I

def routeTSelectedZetaLower (T : ℝ) : ℂ :=
  ((-(1 / 2 : ℝ) : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I

def routeTSelectedZetaUpper (T : ℝ) : ℂ :=
  ((2 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I

/-- Multiplicity copies of the zeros `ρ` of `ξ` whose spectral point lies in
`[-T, T] × [-1/2, 1/2]`, that is, with `|Im ρ| ≤ T`. -/
def routeTSelectedXiCopyPacket (T : ℝ) : Finset RHTower.XiZeroCopy :=
  RHTower.xiZeroCopyClosedRectangle
    (routeTSelectedXiSpectralLower T) (routeTSelectedXiSpectralUpper T)

/-- The distinct zeros of `ξ` underlying `routeTSelectedXiCopyPacket T`. -/
def routeTSelectedXiSupportPacket (T : ℝ) : Finset RHTower.XiDivisorSupport :=
  (routeTSelectedXiCopyPacket T).image Sigma.fst

theorem routeTSelectedXiCopyPacket_fst_eq_mem
    {T : ℝ} {q r : RHTower.XiZeroCopy} (hqr : q.1 = r.1) :
    q ∈ routeTSelectedXiCopyPacket T ↔ r ∈ routeTSelectedXiCopyPacket T := by
  have hspectral : RHTower.xiSpectralPoint q = RHTower.xiSpectralPoint r := by
    simp only [RHTower.xiSpectralPoint, hqr]
  simp only [routeTSelectedXiCopyPacket, RHTower.mem_xiZeroCopyClosedRectangle,
    hspectral]

/-- For `T ≥ 0`, the distinct zeros of `ξ` with `|Im ρ| ≤ T` are exactly the zeros of
`(s-1)ζ(s)` in the closed rectangle `[-1/2, 2] × [-T, T]`. -/
theorem routeTSelectedXiSupport_map_eq_zetaZeros
    {T : ℝ} (hT : 0 ≤ T) :
    (routeTSelectedXiSupportPacket T).map routeTSelectedXiSupportValEmbedding =
      zetaResidueUnitClosedRectangleZeros
        (routeTSelectedZetaLower T) (routeTSelectedZetaUpper T) := by
  classical
  ext w
  rw [Finset.mem_map, mem_zetaResidueUnitClosedRectangleZeros]
  constructor
  · rintro ⟨rho, hrho, rfl⟩
    rw [routeTSelectedXiSupportPacket, Finset.mem_image] at hrho
    obtain ⟨q, hq, hqrho⟩ := hrho
    have hspectral := RHTower.mem_xiZeroCopyClosedRectangle.mp hq
    have hcoords := Complex.mem_reProdIm.mp hspectral
    have hstrip := RHTower.xi_divisor_support_re_mem_open_unit rho
    have hspectralRe : (RHTower.xiSpectralPoint q).re = (rho : ℂ).im := by
      simp [RHTower.xiSpectralPoint, Complex.mul_re, hqrho]
    have him : (rho : ℂ).im ∈ Set.Icc (-T) T := by
      simpa [routeTSelectedXiCopyPacket, routeTSelectedXiSpectralLower,
        routeTSelectedXiSpectralUpper, uIcc_of_le (by linarith : -T ≤ T),
        hspectralRe] using hcoords.1
    constructor
    · apply Complex.mem_reProdIm.mpr
      constructor
      · have hre : (rho : ℂ).re ∈ Set.Icc (-(1 / 2 : ℝ)) 2 := by
          constructor <;> linarith
        have hlre : (routeTSelectedZetaLower T).re = -(1 / 2 : ℝ) := by
          simp [routeTSelectedZetaLower]
        have hure : (routeTSelectedZetaUpper T).re = 2 := by
          simp [routeTSelectedZetaUpper]
        rw [hlre, hure]
        rw [uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 2)]
        simpa [routeTSelectedXiSupportValEmbedding] using hre
      · have hlim : (routeTSelectedZetaLower T).im = -T := by
          simp [routeTSelectedZetaLower]
        have huim : (routeTSelectedZetaUpper T).im = T := by
          simp [routeTSelectedZetaUpper]
        rw [hlim, huim]
        rw [uIcc_of_le (by linarith : -T ≤ T)]
        simpa [routeTSelectedXiSupportValEmbedding] using him
    · have hxi := RHTower.xi_eq_zero_of_mem_divisor_support rho
      have hzeta :=
        (RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1
      have hrho1 : (rho : ℂ) ≠ 1 := by
        intro heq
        rw [heq, Complex.one_re] at hstrip
        exact (lt_irrefl 1) hstrip.2
      change zetaResidueUnit (rho : ℂ) = 0
      rw [zetaResidueUnit, Function.update_of_ne hrho1, hzeta, mul_zero]
  · intro hw
    have hwcoords := Complex.mem_reProdIm.mp hw.1
    have hwre : w.re ∈ Set.uIcc (-(1 / 2 : ℝ)) 2 := by
      simpa [routeTSelectedZetaLower, routeTSelectedZetaUpper] using hwcoords.1
    rw [uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 2)] at hwre
    have hwim : w.im ∈ Set.uIcc (-T) T := by
      simpa [routeTSelectedZetaLower, routeTSelectedZetaUpper] using hwcoords.2
    rw [uIcc_of_le (by linarith : -T ≤ T)] at hwim
    have hw1 : w ≠ 1 := by
      intro heq
      rw [heq, zetaResidueUnit_one] at hw
      norm_num at hw
    have hzeta : riemannZeta w = 0 := by
      by_contra hne
      exact ((zetaResidueUnit_ne_zero_iff hw1).2 hne) hw.2
    have hnontrivial : ∀ n : ℕ, w ≠ -(2 * ((n : ℂ) + 1)) := by
      intro n hn
      have hre := congrArg Complex.re hn
      have hn0 : (0 : ℝ) ≤ n := by positivity
      norm_num at hre
      linarith [hwre.1]
    have hxi : RHTower.xi w = 0 :=
      RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr
        ⟨hzeta, hnontrivial⟩
    let rho : RHTower.XiDivisorSupport :=
      ⟨w, RHTower.mem_xi_divisor_support_of_eq_zero hxi⟩
    let q : RHTower.XiZeroCopy :=
      ⟨rho, ⟨0, RHTower.xiSupportMultiplicity_pos rho⟩⟩
    refine ⟨rho, ?_, rfl⟩
    rw [routeTSelectedXiSupportPacket, Finset.mem_image]
    refine ⟨q, ?_, rfl⟩
    apply RHTower.mem_xiZeroCopyClosedRectangle.mpr
    apply Complex.mem_reProdIm.mpr
    have hstrip := RHTower.xi_zero_re_mem_open_unit hxi
    have hspectralRe : (RHTower.xiSpectralPoint q).re = w.im := by
      simp [q, rho, RHTower.xiSpectralPoint, Complex.mul_re]
    have hspectralIm : (RHTower.xiSpectralPoint q).im = 1 / 2 - w.re := by
      simp [q, rho, RHTower.xiSpectralPoint, Complex.mul_im]
    constructor
    · simpa [routeTSelectedXiCopyPacket, routeTSelectedXiSpectralLower,
        routeTSelectedXiSpectralUpper, uIcc_of_le (by linarith : -T ≤ T),
        hspectralRe] using hwim
    · have him : (RHTower.xiSpectralPoint q).im ∈
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
        rw [hspectralIm]
        constructor <;> linarith
      simpa [routeTSelectedXiCopyPacket, routeTSelectedXiSpectralLower,
        routeTSelectedXiSpectralUpper,
        uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] using him

/-- Summing a function of the underlying zero over multiplicity copies equals the
multiplicity-weighted sum over distinct zeros. -/
theorem sum_routeTSelectedXiCopyPacket_eq_supportMultiplicitySum
    (target : RHTower.XiDivisorSupport → ℂ) (T : ℝ) :
    ∑ q ∈ routeTSelectedXiCopyPacket T, target q.1 =
      ∑ rho ∈ routeTSelectedXiSupportPacket T,
        (RHTower.xiSupportMultiplicity rho : ℂ) * target rho := by
  classical
  let S : Finset RHTower.XiZeroCopy := routeTSelectedXiCopyPacket T
  let B : Finset RHTower.XiDivisorSupport := routeTSelectedXiSupportPacket T
  let Q : Finset RHTower.XiZeroCopy := B.biUnion RHTower.xiZeroCopyFiber
  have hdisj : (B : Set RHTower.XiDivisorSupport).PairwiseDisjoint
      RHTower.xiZeroCopyFiber := by
    intro rho hrho tau htau hne
    change Disjoint (RHTower.xiZeroCopyFiber rho) (RHTower.xiZeroCopyFiber tau)
    rw [Finset.disjoint_left]
    intro q hqrho hqtau
    have hr := RHTower.mem_xiZeroCopyFiber.mp hqrho
    have ht := RHTower.mem_xiZeroCopyFiber.mp hqtau
    exact hne (hr.symm.trans ht)
  have hSQ : S = Q := by
    ext q
    constructor
    · intro hq
      rw [show Q = B.biUnion RHTower.xiZeroCopyFiber from rfl,
        Finset.mem_biUnion]
      refine ⟨q.1, ?_, RHTower.mem_xiZeroCopyFiber.mpr rfl⟩
      change q.1 ∈ (routeTSelectedXiCopyPacket T).image Sigma.fst
      rw [Finset.mem_image]
      exact ⟨q, (show q ∈ routeTSelectedXiCopyPacket T from hq), rfl⟩
    · intro hq
      rw [show Q = B.biUnion RHTower.xiZeroCopyFiber from rfl,
        Finset.mem_biUnion] at hq
      obtain ⟨rho, hrhoB, hqrho⟩ := hq
      rw [show B = routeTSelectedXiSupportPacket T from rfl,
        routeTSelectedXiSupportPacket, Finset.mem_image] at hrhoB
      obtain ⟨r, hrS, hreq⟩ := hrhoB
      have hfst : q.1 = r.1 :=
        (RHTower.mem_xiZeroCopyFiber.mp hqrho).trans hreq.symm
      exact (routeTSelectedXiCopyPacket_fst_eq_mem hfst).2 hrS
  rw [show routeTSelectedXiCopyPacket T = S from rfl, hSQ,
    show Q = B.biUnion RHTower.xiZeroCopyFiber from rfl,
    Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro rho hrho
  calc
    ∑ q ∈ RHTower.xiZeroCopyFiber rho, target q.1 =
        ∑ _q ∈ RHTower.xiZeroCopyFiber rho, target rho := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [RHTower.mem_xiZeroCopyFiber.mp hq]
    _ = (RHTower.xiZeroCopyFiber rho).card • target rho :=
      Finset.sum_const (target rho)
    _ = (RHTower.xiSupportMultiplicity rho : ℂ) * target rho := by
      rw [RHTower.card_xiZeroCopyFiber]
      simp [RHTower.xiSupportMultiplicity, nsmul_eq_mul]

/-- For `T ≥ 0`, `∑ ord_w((s-1)ζ) K_{N,H}(w)` over the zeros of `(s-1)ζ(s)` in
`[-1/2, 2] × [-T, T]` equals `∑ K_{N,H}(ρ_q)` over the `ξ` zero copies with `|Im ρ| ≤ T`. -/
theorem routeTSelectedZetaMultiplicitySum_eq_xiCopySum
    {N H T : ℝ} (hT : 0 ≤ T) :
    (∑ w ∈ zetaResidueUnitClosedRectangleZeros
        (routeTSelectedZetaLower T) (routeTSelectedZetaUpper T),
      ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
        routeTNormalizedSmoothWindowMellin N H w) =
      ∑ q ∈ routeTSelectedXiCopyPacket T,
        routeTNormalizedSmoothWindowMellin N H (q.1 : ℂ) := by
  classical
  let B := routeTSelectedXiSupportPacket T
  have hmap : B.map routeTSelectedXiSupportValEmbedding =
      zetaResidueUnitClosedRectangleZeros
        (routeTSelectedZetaLower T) (routeTSelectedZetaUpper T) := by
    simpa only [B] using routeTSelectedXiSupport_map_eq_zetaZeros hT
  calc
    (∑ w ∈ zetaResidueUnitClosedRectangleZeros
          (routeTSelectedZetaLower T) (routeTSelectedZetaUpper T),
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
          routeTNormalizedSmoothWindowMellin N H w) =
        ∑ w ∈ B.map routeTSelectedXiSupportValEmbedding,
          ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
            routeTNormalizedSmoothWindowMellin N H w := by rw [hmap]
    _ = ∑ rho ∈ B,
          ((analyticOrderAt zetaResidueUnit (rho : ℂ)).toNat : ℂ) *
            routeTNormalizedSmoothWindowMellin N H (rho : ℂ) := by
      rw [Finset.sum_map]
      rfl
    _ = ∑ rho ∈ B,
          (RHTower.xiSupportMultiplicity rho : ℂ) *
            routeTNormalizedSmoothWindowMellin N H (rho : ℂ) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have hstrip := RHTower.xi_divisor_support_re_mem_open_unit rho
      rw [routeT_xiSupportMultiplicity_eq_analyticOrderAt_toNat,
        ← analyticOrderAt_zetaResidueUnit_eq_xi_of_mem_strip hstrip]
    _ = ∑ q ∈ routeTSelectedXiCopyPacket T,
          routeTNormalizedSmoothWindowMellin N H (q.1 : ℂ) := by
      symm
      simpa only [B] using sum_routeTSelectedXiCopyPacket_eq_supportMultiplicitySum
        (fun rho => routeTNormalizedSmoothWindowMellin N H (rho : ℂ)) T

/-- The `ξ` zero copies with `|Im ρ| ≤ T_X`, at the selected contour height `T_X`. -/
def inghamRouteTBufferedSelectedXiCopyPacket (X : ℕ) : Finset RHTower.XiZeroCopy :=
  routeTSelectedXiCopyPacket (inghamRouteTBufferedNegativeHalfHeight X)

theorem inghamRouteTBufferedSelectedXiCopyPacket_subset_lowOrdinate
    {X : ℕ} (hX : 12 ≤ X) :
    inghamRouteTBufferedSelectedXiCopyPacket X ⊆
      inghamRouteTXiLowOrdinatePacket X := by
  intro q hq
  have hX4 : 4 ≤ X := by omega
  rw [mem_inghamRouteTXiLowOrdinatePacket_iff hX4]
  have hrect := RHTower.mem_xiZeroCopyClosedRectangle.mp hq
  have hcoords := Complex.mem_reProdIm.mp hrect
  have hspec := (inghamRouteTBufferedNegativeHalfHeight_spec hX).1
  have hT0 : 0 ≤ inghamRouteTBufferedNegativeHalfHeight X := by
    have hXR : (12 : ℝ) ≤ X := by exact_mod_cast hX
    linarith [hspec.1]
  have hspectralRe : (RHTower.xiSpectralPoint q).re =
      ((q.1 : RHTower.XiDivisorSupport) : ℂ).im := by
    simp [RHTower.xiSpectralPoint, Complex.mul_re]
  have him : ((q.1 : RHTower.XiDivisorSupport) : ℂ).im ∈
      Set.Icc (-inghamRouteTBufferedNegativeHalfHeight X)
        (inghamRouteTBufferedNegativeHalfHeight X) := by
    simpa [inghamRouteTBufferedSelectedXiCopyPacket, routeTSelectedXiCopyPacket,
      routeTSelectedXiSpectralLower, routeTSelectedXiSpectralUpper,
      uIcc_of_le (by linarith :
        -inghamRouteTBufferedNegativeHalfHeight X ≤
          inghamRouteTBufferedNegativeHalfHeight X), hspectralRe] using hcoords.1
  exact (abs_le.mpr him).trans hspec.2.le

def inghamRouteTBufferedSelectedXiLowRealPacket (X : ℕ) :
    Finset RHTower.XiZeroCopy :=
  (inghamRouteTBufferedSelectedXiCopyPacket X).filter fun q =>
    ((q.1 : RHTower.XiDivisorSupport) : ℂ).re < 7 / 10

def inghamRouteTBufferedSelectedXiHighRealPacket (X : ℕ) :
    Finset RHTower.XiZeroCopy :=
  (inghamRouteTBufferedSelectedXiCopyPacket X).filter fun q =>
    7 / 10 ≤ ((q.1 : RHTower.XiDivisorSupport) : ℂ).re

theorem inghamRouteTBufferedSelectedXiLowRealPacket_subset
    {X : ℕ} (hX : 12 ≤ X) :
    inghamRouteTBufferedSelectedXiLowRealPacket X ⊆
      inghamRouteTXiLowRealPacket X := by
  intro q hq
  rw [inghamRouteTBufferedSelectedXiLowRealPacket, Finset.mem_filter] at hq
  rw [inghamRouteTXiLowRealPacket, Finset.mem_filter]
  exact ⟨inghamRouteTBufferedSelectedXiCopyPacket_subset_lowOrdinate hX hq.1, hq.2⟩

theorem inghamRouteTBufferedSelectedXiHighRealPacket_subset
    {X : ℕ} (hX : 12 ≤ X) :
    inghamRouteTBufferedSelectedXiHighRealPacket X ⊆
      inghamRouteTXiHighRealPacket X := by
  intro q hq
  rw [inghamRouteTBufferedSelectedXiHighRealPacket, Finset.mem_filter] at hq
  rw [inghamRouteTXiHighRealPacket, Finset.mem_filter]
  exact ⟨inghamRouteTBufferedSelectedXiCopyPacket_subset_lowOrdinate hX hq.1, hq.2⟩

def inghamRouteTBufferedSelectedXiMellinLowRealPacket (X : ℕ) : ℂ :=
  ∑ q ∈ inghamRouteTBufferedSelectedXiLowRealPacket X,
    routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)

def inghamRouteTBufferedSelectedXiMellinHighRealPacket (X : ℕ) : ℂ :=
  ∑ q ∈ inghamRouteTBufferedSelectedXiHighRealPacket X,
    routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)

/-- The `ξ`-zero Mellin packet `∑ K_X(ρ_q)` over the selected zero copies. -/
def inghamRouteTBufferedSelectedXiMellinPacket (X : ℕ) : ℂ :=
  ∑ q ∈ inghamRouteTBufferedSelectedXiCopyPacket X,
    routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)

/-- For `X ≥ 12`, the part of the packet from zeros with `Re ρ < 7/10` has norm at most
`C_ξ (1 + X) log(2 + X) X^{-300/299}`, by `|K_X(ρ)| ≤ N_X^{Re ρ - 1}` and the global zero count. -/
theorem norm_inghamRouteTBufferedSelectedXiMellinLowRealPacket_le
    {X : ℕ} (hX : 12 ≤ X) :
    ‖inghamRouteTBufferedSelectedXiMellinLowRealPacket X‖ ≤
      RHTower.xiZeroCountEnvelopeConstant * (1 + (X : ℝ)) *
        Real.log (2 + (X : ℝ)) * (X : ℝ) ^ (-(300 / 299 : ℝ)) := by
  have hX4 : 4 ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  have hXR1 : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hNpos := inghamRouteTMellinPhysicalCenter_pos hX1
  have hNone := inghamRouteTMellinPhysicalCenter_one_le hX1
  have hHpos := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  let E : ℝ := (X : ℝ) ^ (-(300 / 299 : ℝ))
  have hpoint : ∀ q ∈ inghamRouteTBufferedSelectedXiLowRealPacket X,
      ‖routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)‖ ≤ E := by
    intro q hq
    have hrelt : ((q.1 : RHTower.XiDivisorSupport) : ℂ).re < 7 / 10 :=
      (Finset.mem_filter.mp hq).2
    have hstrip := RHTower.xi_divisor_support_re_mem_open_unit q.1
    have hkernel := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
      hNpos hHpos hstrip.2.le
    have hmono : inghamRouteTMellinPhysicalCenter X ^
          (((q.1 : RHTower.XiDivisorSupport) : ℂ).re - 1) ≤
        inghamRouteTMellinPhysicalCenter X ^ ((7 / 10 : ℝ) - 1) :=
      Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
    have hexact : inghamRouteTMellinPhysicalCenter X ^ ((7 / 10 : ℝ) - 1) = E := by
      rw [inghamRouteTMellinPhysicalCenter_rpow_sub_one hX1]
      dsimp only [E]
      congr 1
      unfold inghamRouteTPhysicalScaleExponent
      norm_num
    exact hkernel.trans (hmono.trans_eq hexact)
  have hcardNat := Finset.card_le_card
    (inghamRouteTBufferedSelectedXiLowRealPacket_subset hX)
  have hcardSub : ((inghamRouteTBufferedSelectedXiLowRealPacket X).card : ℝ) ≤
      ((inghamRouteTXiLowRealPacket X).card : ℝ) := by exact_mod_cast hcardNat
  have hcard := hcardSub.trans (card_inghamRouteTXiLowRealPacket_le_global hX4)
  have hE0 : 0 ≤ E := Real.rpow_nonneg (zero_le_one.trans hXR1) _
  unfold inghamRouteTBufferedSelectedXiMellinLowRealPacket
  calc
    ‖∑ q ∈ inghamRouteTBufferedSelectedXiLowRealPacket X,
        routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)‖ ≤
      ∑ q ∈ inghamRouteTBufferedSelectedXiLowRealPacket X,
        ‖routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ inghamRouteTBufferedSelectedXiLowRealPacket X, E :=
      Finset.sum_le_sum fun q hq => hpoint q hq
    _ = ((inghamRouteTBufferedSelectedXiLowRealPacket X).card : ℝ) * E := by
      simp [nsmul_eq_mul]
    _ ≤ (RHTower.xiZeroCountEnvelopeConstant * (1 + (X : ℝ)) *
          Real.log (2 + (X : ℝ))) * E :=
      mul_le_mul_of_nonneg_right hcard hE0
    _ = _ := by rfl

/-- For `X ≥ 12`, the part of the packet from zeros with `Re ρ ≥ 7/10` has norm at most the
physical high-zero weighted mass `∑ X^{(1000/299)(Re w - 1)} · mult(w)`. -/
theorem norm_inghamRouteTBufferedSelectedXiMellinHighRealPacket_le
    {X : ℕ} (hX : 12 ≤ X) :
    ‖inghamRouteTBufferedSelectedXiMellinHighRealPacket X‖ ≤
      inghamRouteTHighZeroWeightedMass X := by
  have hX4 : 4 ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  have hNpos := inghamRouteTMellinPhysicalCenter_pos hX1
  have hHpos := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  unfold inghamRouteTBufferedSelectedXiMellinHighRealPacket
  calc
    ‖∑ q ∈ inghamRouteTBufferedSelectedXiHighRealPacket X,
        routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)‖ ≤
      ∑ q ∈ inghamRouteTBufferedSelectedXiHighRealPacket X,
        ‖routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ inghamRouteTBufferedSelectedXiHighRealPacket X,
        (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent *
          (((q.1 : RHTower.XiDivisorSupport) : ℂ).re - 1)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hstrip := RHTower.xi_divisor_support_re_mem_open_unit q.1
      have hkernel := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
        hNpos hHpos hstrip.2.le
      exact hkernel.trans_eq
        (inghamRouteTMellinPhysicalCenter_rpow_sub_one hX1
          (((q.1 : RHTower.XiDivisorSupport) : ℂ).re))
    _ ≤ ∑ q ∈ inghamRouteTXiHighRealPacket X,
        (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent *
          (((q.1 : RHTower.XiDivisorSupport) : ℂ).re - 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (inghamRouteTBufferedSelectedXiHighRealPacket_subset hX)
        (fun q _ _ => Real.rpow_nonneg (by positivity) _)
    _ ≤ inghamRouteTHighZeroWeightedMass X :=
      inghamRouteTXiHighRealCopiedWeight_le_highMass hX4

theorem inghamRouteTBufferedSelectedXiMellinPacket_eq_low_add_high (X : ℕ) :
    inghamRouteTBufferedSelectedXiMellinPacket X =
      inghamRouteTBufferedSelectedXiMellinLowRealPacket X +
        inghamRouteTBufferedSelectedXiMellinHighRealPacket X := by
  classical
  rw [inghamRouteTBufferedSelectedXiMellinPacket,
    inghamRouteTBufferedSelectedXiMellinLowRealPacket,
    inghamRouteTBufferedSelectedXiMellinHighRealPacket,
    inghamRouteTBufferedSelectedXiLowRealPacket,
    inghamRouteTBufferedSelectedXiHighRealPacket]
  simpa only [not_lt] using (Finset.sum_filter_add_sum_filter_not
    (inghamRouteTBufferedSelectedXiCopyPacket X)
    (fun q : RHTower.XiZeroCopy =>
      ((q.1 : RHTower.XiDivisorSupport) : ℂ).re < 7 / 10)
    (fun q => routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ))).symm

/-- The low-real (`Re ρ < 7/10`) part of the `ξ` packet tends to zero as `X → ∞`. -/
theorem tendsto_norm_inghamRouteTBufferedSelectedXiMellinLowRealPacket_zero :
    Tendsto (fun X : ℕ =>
      ‖inghamRouteTBufferedSelectedXiMellinLowRealPacket X‖) atTop (𝓝 0) := by
  let C : ℝ := RHTower.xiZeroCountEnvelopeConstant
  have hC : 0 < C := RHTower.xiZeroCountEnvelopeConstant_pos
  have hcore := tendsto_nat_log_mul_rpow_neg_one_div_299_zero
  have hupper : Tendsto (fun X : ℕ =>
      (4 * C) * (Real.log (X : ℝ) * (X : ℝ) ^ (-(1 / 299 : ℝ))))
      atTop (𝓝 0) := by
    simpa using hcore.const_mul (4 * C)
  refine squeeze_zero' (by filter_upwards with X; exact norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
  have hb := norm_inghamRouteTBufferedSelectedXiMellinLowRealPacket_le hX
  have hXR : (4 : ℝ) ≤ X := by exact_mod_cast (show 4 ≤ X by omega)
  have hXpos : (0 : ℝ) < X := by linarith
  have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by linarith)
  have hadd : 1 + (X : ℝ) ≤ 2 * X := by linarith
  have hquad : 2 + (X : ℝ) ≤ (X : ℝ) ^ (2 : ℕ) := by nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 + (X : ℝ)) hquad
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hfac : (1 + (X : ℝ)) * Real.log (2 + (X : ℝ)) ≤
      4 * (X : ℝ) * Real.log (X : ℝ) := by
    calc
      (1 + (X : ℝ)) * Real.log (2 + (X : ℝ)) ≤
          (2 * (X : ℝ)) * (2 * Real.log (X : ℝ)) :=
        mul_le_mul hadd hlog (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + X))
          (by positivity)
      _ = 4 * (X : ℝ) * Real.log (X : ℝ) := by ring
  have hweight0 : 0 ≤ (X : ℝ) ^ (-(300 / 299 : ℝ)) :=
    Real.rpow_nonneg hXpos.le _
  have hfacC : C * ((1 + (X : ℝ)) * Real.log (2 + (X : ℝ))) ≤
      C * (4 * (X : ℝ) * Real.log (X : ℝ)) :=
    mul_le_mul_of_nonneg_left hfac hC.le
  have hcollapse : (X : ℝ) * (X : ℝ) ^ (-(300 / 299 : ℝ)) =
      (X : ℝ) ^ (-(1 / 299 : ℝ)) := by
    calc
      (X : ℝ) * (X : ℝ) ^ (-(300 / 299 : ℝ)) =
          (X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (-(300 / 299 : ℝ)) := by
        rw [Real.rpow_one]
      _ = (X : ℝ) ^ ((1 : ℝ) + -(300 / 299 : ℝ)) :=
        (Real.rpow_add hXpos _ _).symm
      _ = (X : ℝ) ^ (-(1 / 299 : ℝ)) := by
        congr 1
        norm_num
  calc
    ‖inghamRouteTBufferedSelectedXiMellinLowRealPacket X‖ ≤
        C * (1 + (X : ℝ)) * Real.log (2 + (X : ℝ)) *
          (X : ℝ) ^ (-(300 / 299 : ℝ)) := by simpa only [C] using hb
    _ = C * ((1 + (X : ℝ)) * Real.log (2 + (X : ℝ))) *
          (X : ℝ) ^ (-(300 / 299 : ℝ)) := by ring
    _ ≤ C * (4 * (X : ℝ) * Real.log (X : ℝ)) *
          (X : ℝ) ^ (-(300 / 299 : ℝ)) :=
      mul_le_mul_of_nonneg_right hfacC hweight0
    _ = (4 * C) *
        (Real.log (X : ℝ) * (X : ℝ) ^ (-(1 / 299 : ℝ))) := by
      rw [← hcollapse]
      ring

/-- The high-real (`Re ρ ≥ 7/10`) part of the `ξ` packet tends to zero as `X → ∞`, via the
zero-density limit of the high-zero weighted mass. -/
theorem tendsto_norm_inghamRouteTBufferedSelectedXiMellinHighRealPacket_zero :
    Tendsto (fun X : ℕ =>
      ‖inghamRouteTBufferedSelectedXiMellinHighRealPacket X‖) atTop (𝓝 0) := by
  refine squeeze_zero' (by filter_upwards with X; exact norm_nonneg _) ?_
    tendsto_inghamRouteTHighZeroWeightedMass_zero
  filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
  exact norm_inghamRouteTBufferedSelectedXiMellinHighRealPacket_le hX

/-- The full selected `ξ`-zero Mellin packet `∑ K_X(ρ_q)` tends to `0` as `X → ∞`. -/
theorem tendsto_inghamRouteTBufferedSelectedXiMellinPacket_zero :
    Tendsto inghamRouteTBufferedSelectedXiMellinPacket atTop (𝓝 0) := by
  have hlo : Tendsto inghamRouteTBufferedSelectedXiMellinLowRealPacket atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      tendsto_norm_inghamRouteTBufferedSelectedXiMellinLowRealPacket_zero
  have hhi : Tendsto inghamRouteTBufferedSelectedXiMellinHighRealPacket atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      tendsto_norm_inghamRouteTBufferedSelectedXiMellinHighRealPacket_zero
  apply (tendsto_congr' (Filter.Eventually.of_forall fun X =>
    inghamRouteTBufferedSelectedXiMellinPacket_eq_low_add_high X)).mpr
  simpa using hlo.add hhi

/-- For `X ≥ 12`, the contour zero packet on `[-1/2, 2] × [-T_X, T_X]` equals `2πi` times the
selected `ξ`-zero Mellin packet. -/
theorem inghamRouteTBufferedSelectedNegativeHalfZeroPacket_eq_xiPacket
    {X : ℕ} (hX : 12 ≤ X) :
    inghamRouteTBufferedSelectedNegativeHalfZeroPacket X =
      2 * Real.pi * I * inghamRouteTBufferedSelectedXiMellinPacket X := by
  have hspec := (inghamRouteTBufferedNegativeHalfHeight_spec hX).1
  have hT0 : 0 ≤ inghamRouteTBufferedNegativeHalfHeight X := by
    have hXR : (12 : ℝ) ≤ X := by exact_mod_cast hX
    linarith [hspec.1]
  have hsum := routeTSelectedZetaMultiplicitySum_eq_xiCopySum
    (N := inghamRouteTMellinPhysicalCenter X)
    (H := inghamRouteTMellinBufferedPhysicalWidth X) hT0
  have hlower :
      (((-1 / 2 : ℝ) : ℂ) +
        ((-inghamRouteTBufferedNegativeHalfHeight X : ℝ) : ℂ) * I) =
        routeTSelectedZetaLower (inghamRouteTBufferedNegativeHalfHeight X) := by
    norm_num [routeTSelectedZetaLower]
  have hupper :
      (((2 : ℝ) : ℂ) + (inghamRouteTBufferedNegativeHalfHeight X : ℂ) * I) =
        routeTSelectedZetaUpper (inghamRouteTBufferedNegativeHalfHeight X) := by
    simp [routeTSelectedZetaUpper]
  rw [inghamRouteTBufferedSelectedNegativeHalfZeroPacket,
    routeTNormalizedZetaRegularMellinZeroPacket,
    inghamRouteTBufferedSelectedXiMellinPacket,
    inghamRouteTBufferedSelectedXiCopyPacket]
  rw [hlower, hupper, hsum]

/-- The selected contour zero packet `2πi ∑ ord_w K_X(w)` tends to `0` as `X → ∞`. -/
theorem tendsto_inghamRouteTBufferedSelectedNegativeHalfZeroPacket_zero :
    Tendsto inghamRouteTBufferedSelectedNegativeHalfZeroPacket atTop (𝓝 0) := by
  have hscaled : Tendsto (fun X : ℕ =>
      2 * Real.pi * I * inghamRouteTBufferedSelectedXiMellinPacket X)
      atTop (𝓝 0) := by
    simpa using tendsto_inghamRouteTBufferedSelectedXiMellinPacket_zero.const_mul
      (2 * Real.pi * I)
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
  exact (inghamRouteTBufferedSelectedNegativeHalfZeroPacket_eq_xiPacket hX).symm

end

end RHTower.Sieve
