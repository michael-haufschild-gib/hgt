import GaloisForLFunctions.RHTower.LeeYangRestrictionZeroCount
import GaloisForLFunctions.HTGeometry.LocallyUniformZeroCountTransfer
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.XiHeightAdaptiveHedenmalmCensusCollision
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# No stability route in prime fields reaches `Ξ`

**Theorem** (`not_tendsto_lyApprox_mul_XiC`).  Fix `lam0 > 0`.  Take a sequence of Lee–Yang data
whose frequencies are all `≥ lam0`, together with entire zero-free normalizers `hₙ`.  The normalized
restrictions `hₙ · fₙ` cannot converge locally uniformly on `ℂ` to `E · XiC` for any entire
zero-free `E`.  The prime fields `e^{−iz log p}` have frequencies `log p ≥ log 2`.  So no half-plane-
property, ferromagnetic Lee–Yang or other stable polynomial in prime-field variables gives `Ξ` as
such a limit.

**Proof.**
* *Quasi-linear limit counts* (`zeroSumBall_mul_le_of_tendsto`).  A restriction has
  `|n(T) − 2T·D| ≤ 2S` for its zero count in `(−T, T)` (`abs_zeroCount_sub_le`).  Frequencies
  `≥ lam0` give `S ≤ κ D`, with `κ = 2π/lam0`.  Zero counts in discs pass to locally uniform limits.
  Hence the limit count `c` satisfies `c(T₀)(T₁ − κ) ≤ c(T₁)(T₀ + κ)` for admissible `κ < T₁ < T₀`,
  so `c` grows at most linearly.
* *Superlinear `Ξ` count.*  The disc of radius `T` contains the centered images of all `ξ`-zeros of
  ordinate in `(0, T − 1]`.  By Riemann–von Mangoldt the count is `≥ (T−1) log(T−1)/(4π)` for
  large `T`.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower.LeeYangCount

noncomputable section

/-- A Lee–Yang approximant: a datum and an entire zero-free normalizer. -/
structure LYApprox where
  ι : Type
  [ft : Fintype ι]
  datum : LeeYangDatum ι
  normalizer : ℂ → ℂ
  normalizer_differentiable : Differentiable ℂ normalizer
  normalizer_ne_zero : ∀ z, normalizer z ≠ 0

attribute [instance] LYApprox.ft

namespace LYApprox

variable (A : LYApprox)

/-- The normalized section `h · f`. -/
def sect (z : ℂ) : ℂ := A.normalizer z * A.datum.restr z

theorem differentiable_sect : Differentiable ℂ A.sect :=
  A.normalizer_differentiable.mul A.datum.differentiable_restr

theorem sect_eq_zero_iff {z : ℂ} : A.sect z = 0 ↔ A.datum.restr z = 0 := by
  rw [sect, mul_eq_zero, or_iff_right (A.normalizer_ne_zero z)]

theorem zeroMult_sect (z : ℂ) :
    zeroMult A.sect z = (analyticOrderAt A.datum.restr z).toNat := by
  have h1 : AnalyticAt ℂ A.normalizer z := A.normalizer_differentiable.analyticAt z
  have h2 : AnalyticAt ℂ A.datum.restr z := A.datum.differentiable_restr.analyticAt z
  have hmul : analyticOrderAt A.sect z =
      analyticOrderAt A.normalizer z + analyticOrderAt A.datum.restr z :=
    analyticOrderAt_mul h1 h2
  have h0 : analyticOrderAt A.normalizer z = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (A.normalizer_ne_zero z))
  rw [zeroMult, hmul, h0, zero_add]

/-- **Linear count in discs.** -/
theorem abs_zeroSumBall_sub_le {T : ℝ} (hT : 0 < T) (hpos : A.datum.restr (T : ℂ) ≠ 0)
    (hneg : A.datum.restr ((-T : ℝ) : ℂ) ≠ 0) :
    |(zeroSumBall A.sect 0 T).re - 2 * T * A.datum.density| ≤
      2 * (degSum A.datum.P : ℝ) := by
  have hsphere : ∀ ζ ∈ sphere (0 : ℂ) T, A.sect ζ ≠ 0 := by
    intro ζ hζ hzero
    rw [sect_eq_zero_iff] at hzero
    have him := A.datum.restr_im_eq_zero_of_eq_zero hzero
    rw [mem_sphere_zero_iff_norm] at hζ
    have hζre : ζ = (ζ.re : ℂ) := Complex.ext rfl (by simp [him])
    have habs : |ζ.re| = T := by
      rw [← hζ, hζre, Complex.norm_real, Real.norm_eq_abs]
      simp
    rcases abs_eq hT.le |>.mp habs with h | h
    · rw [hζre, h] at hzero; exact hpos hzero
    · rw [hζre, h] at hzero; exact hneg (by exact_mod_cast hzero)
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall (c := 0) hT
    (lt_add_one T) isOpen_univ (subset_univ _) A.differentiable_sect.differentiableOn hsphere
  have hmem : ∀ z, z ∈ Z ↔ z ∈ (uIcc (-T) T ×ℂ uIcc (-1 : ℝ) 1) ∧ A.datum.restr z = 0 := by
    intro z
    constructor
    · intro hz
      have hb := hZball z hz
      have hzero : A.sect z = 0 := (hZzero z hb).mpr hz
      rw [sect_eq_zero_iff] at hzero
      have him := A.datum.restr_im_eq_zero_of_eq_zero hzero
      refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hzero⟩
      · rw [mem_ball_zero_iff] at hb
        have : |z.re| < T := (Complex.abs_re_le_norm z).trans_lt hb
        rw [uIcc_of_le (by linarith)]
        exact ⟨by linarith [neg_abs_le z.re], by linarith [le_abs_self z.re]⟩
      · rw [him, uIcc_of_le (by norm_num)]
        exact ⟨by norm_num, by norm_num⟩
    · rintro ⟨hrect, hzero⟩
      have him := A.datum.restr_im_eq_zero_of_eq_zero hzero
      have hzre : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
      rw [Complex.mem_reProdIm, uIcc_of_le (by linarith)] at hrect
      have hlt : |z.re| < T := by
        rcases lt_or_eq_of_le (abs_le.mpr ⟨hrect.1.1, hrect.1.2⟩) with h | h
        · exact h
        · exfalso
          rcases abs_eq hT.le |>.mp h with h' | h'
          · rw [hzre, h'] at hzero; exact hpos hzero
          · rw [hzre, h'] at hzero; exact hneg (by exact_mod_cast hzero)
      have hb : z ∈ ball (0 : ℂ) T := by
        rw [mem_ball_zero_iff, hzre, Complex.norm_real, Real.norm_eq_abs]
        exact hlt
      exact (hZzero z hb).mp ((A.sect_eq_zero_iff).mpr hzero)
  have hcount := A.datum.abs_zeroCount_sub_le (show -T < T by linarith)
    (by exact_mod_cast hneg) hpos Z hmem
  have hre : (zeroSumBall A.sect 0 T).re =
      ∑ w ∈ Z, ((analyticOrderAt A.datum.restr w).toNat : ℝ) := by
    rw [hsum, Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [zeroMult_sect]
    simp
  rw [hre]
  have : T - -T = 2 * T := by ring
  rw [this] at hcount
  linarith [hcount]

/-- Frequencies `≥ lam0` bound the total degree by the density: `lam0 S ≤ 2π D`. -/
theorem degSum_le_density {lam0 : ℝ} (hfreq : ∀ j, lam0 ≤ A.datum.freq j) :
    lam0 * (degSum A.datum.P : ℝ) ≤ 2 * Real.pi * A.datum.density := by
  rw [LeeYangDatum.density, degSum]
  push_cast
  rw [Finset.mul_sum, ← mul_assoc, mul_one_div_cancel (by positivity), one_mul]
  exact Finset.sum_le_sum fun j _ => by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hfreq j) (Nat.cast_nonneg _)

theorem density_nonneg : 0 ≤ A.datum.density := by
  rw [LeeYangDatum.density]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (A.datum.freq_pos j).le)

end LYApprox

/-- **Quasi-linear limit counts.**  If normalized Lee–Yang restrictions with frequencies `≥ lam0`
converge locally uniformly to `F`, then `c(T) = zeroSumBall F 0 T` satisfies
`c(T₀)(T₁ − κ) ≤ c(T₁)(T₀ + κ)`, with `κ = 2π/lam0`, for radii `κ < T₁ < T₀` whose circles avoid the
zeros of `F`. -/
theorem zeroSumBall_mul_le_of_tendsto {A : ℕ → LYApprox} {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hfreq : ∀ n j, lam0 ≤ (A n).datum.freq j) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hconv : TendstoLocallyUniformly (fun n => (A n).sect) F atTop)
    {T₀ T₁ : ℝ} (hκ : 2 * Real.pi / lam0 < T₁) (h10 : T₁ < T₀)
    (hT₀ : ∀ z ∈ sphere (0 : ℂ) T₀, F z ≠ 0) (hT₁ : ∀ z ∈ sphere (0 : ℂ) T₁, F z ≠ 0) :
    (zeroSumBall F 0 T₀).re * (T₁ - 2 * Real.pi / lam0) ≤
      (zeroSumBall F 0 T₁).re * (T₀ + 2 * Real.pi / lam0) := by
  set κ := 2 * Real.pi / lam0 with hκdef
  have hκpos : 0 < κ := by positivity
  have hT₁pos : 0 < T₁ := lt_trans hκpos hκ
  have hT₀pos : 0 < T₀ := lt_trans hT₁pos h10
  have hc₀ := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
    (fun n => (A n).differentiable_sect) hF hconv hT₀pos (lt_add_one T₀) hT₀
  have hc₁ := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
    (fun n => (A n).differentiable_sect) hF hconv hT₁pos (lt_add_one T₁) hT₁
  have hpt : ∀ x : ℂ, Tendsto (fun n => (A n).sect x) atTop (𝓝 (F x)) := fun x =>
    (tendstoLocallyUniformlyOn_univ.mpr hconv).tendsto_at (mem_univ x)
  have hsph : ∀ {T : ℝ}, 0 < T → (∀ z ∈ sphere (0 : ℂ) T, F z ≠ 0) →
      F (T : ℂ) ≠ 0 ∧ F ((-T : ℝ) : ℂ) ≠ 0 := by
    intro T hT h
    exact ⟨h _ (by simp [abs_of_pos hT]), h _ (by simp [abs_of_pos hT])⟩
  have hev : ∀ᶠ n in atTop, (A n).sect (T₀ : ℂ) ≠ 0 ∧ (A n).sect ((-T₀ : ℝ) : ℂ) ≠ 0 ∧
      (A n).sect (T₁ : ℂ) ≠ 0 ∧ (A n).sect ((-T₁ : ℝ) : ℂ) ≠ 0 :=
    ((hpt _).eventually_ne (hsph hT₀pos hT₀).1).and (((hpt _).eventually_ne
      (hsph hT₀pos hT₀).2).and (((hpt _).eventually_ne (hsph hT₁pos hT₁).1).and
        ((hpt _).eventually_ne (hsph hT₁pos hT₁).2)))
  obtain ⟨n, hn₀, hn₁, ⟨h₁, h₂, h₃, h₄⟩⟩ := (hc₀.and (hc₁.and hev)).exists
  have hne : ∀ {x : ℂ}, (A n).sect x ≠ 0 → (A n).datum.restr x ≠ 0 := fun h h' =>
    h (((A n).sect_eq_zero_iff).mpr h')
  have hb₀ := (A n).abs_zeroSumBall_sub_le hT₀pos (hne h₁) (hne h₂)
  have hb₁ := (A n).abs_zeroSumBall_sub_le hT₁pos (hne h₃) (hne h₄)
  rw [hn₀] at hb₀
  rw [hn₁] at hb₁
  set D := (A n).datum.density
  set S : ℝ := (degSum (A n).datum.P : ℝ)
  have hD := (A n).density_nonneg
  have hSD : S ≤ κ * D := by
    have := (A n).degSum_le_density (hfreq n)
    rw [hκdef, div_mul_eq_mul_div, le_div_iff₀ hlam0]
    linarith
  rw [abs_le] at hb₀ hb₁
  have hup : (zeroSumBall F 0 T₀).re ≤ 2 * D * (T₀ + κ) := by nlinarith
  have hlow : 2 * D * (T₁ - κ) ≤ (zeroSumBall F 0 T₁).re := by nlinarith
  have hpos₁ : 0 ≤ T₁ - κ := by linarith
  have hpos₀ : 0 ≤ T₀ + κ := by linarith
  calc (zeroSumBall F 0 T₀).re * (T₁ - κ) ≤ 2 * D * (T₀ + κ) * (T₁ - κ) :=
        mul_le_mul_of_nonneg_right hup hpos₁
    _ = 2 * D * (T₁ - κ) * (T₀ + κ) := by ring
    _ ≤ (zeroSumBall F 0 T₁).re * (T₀ + κ) := mul_le_mul_of_nonneg_right hlow hpos₀

/-! ## The superlinear count of `Ξ` -/

/-- Radii avoiding the zeros of an entire function that is not identically zero exist in every
unit interval. -/
theorem exists_admissible_radius {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) (M : ℝ) :
    ∃ T ∈ Ioo M (M + 1), ∀ z ∈ sphere (0 : ℂ) T, F z ≠ 0 := by
  have han : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  set R : ℝ := |M| + 1 with hR
  have hfin := RHTower.entire_zeros_closedRectangle_finite han ⟨0, hF0⟩
    (⟨-R, -R⟩ : ℂ) (⟨R, R⟩ : ℂ)
  set Zs := hfin.toFinset with hZs
  obtain ⟨T, hT, hTnot⟩ := (Set.Ioo_infinite (show M < M + 1 by linarith)).exists_notMem_finset
    (Zs.image fun z => ‖z‖)
  refine ⟨T, hT, fun z hz hzero => hTnot ?_⟩
  rw [mem_sphere_zero_iff_norm] at hz
  rw [Finset.mem_image]
  refine ⟨z, ?_, hz⟩
  rw [hZs, Set.Finite.mem_toFinset]
  refine ⟨?_, hzero⟩
  have hTR : T ≤ R := by
    have := hT.2
    have := le_abs_self M
    linarith
  have hre : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans (hz.le.trans hTR)
  have him : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans (hz.le.trans hTR)
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  rw [Complex.mem_reProdIm]
  constructor
  · show z.re ∈ uIcc (-R) R
    rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith [neg_abs_le z.re], by linarith [le_abs_self z.re]⟩
  · show z.im ∈ uIcc (-R) R
    rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith [neg_abs_le z.im], by linarith [le_abs_self z.im]⟩

/-- The disc of radius `T` sees every `ξ`-zero of ordinate in `(0, T − 1]`. -/
theorem xiZeroCount_le_zeroSumBall {E : ℂ → ℂ} (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0)
    {T : ℝ} (hT : 1 ≤ T) (hsph : ∀ z ∈ sphere (0 : ℂ) T, E z * XiC z ≠ 0) :
    (xiZeroCount (T - 1) : ℝ) ≤ (zeroSumBall (fun z => E z * XiC z) 0 T).re := by
  classical
  set F : ℂ → ℂ := fun z => E z * XiC z with hFdef
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hFd : Differentiable ℂ F := hE.mul hXiCd
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall (c := 0)
    (by linarith : (0 : ℝ) < T) (lt_add_one T) isOpen_univ (subset_univ _) hFd.differentiableOn hsph
  have hzm : ∀ z, zeroMult F z = (analyticOrderAt XiC z).toNat := by
    intro z
    have hmul : analyticOrderAt F z = analyticOrderAt E z + analyticOrderAt XiC z :=
      analyticOrderAt_mul (hE.analyticAt z) (hXiCd.analyticAt z)
    have h0 : analyticOrderAt E z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr (hEne z))
    rw [zeroMult, hmul, h0, zero_add]
  set g : XiDivisorSupport → ℂ := fun ρ => ((ρ : ℂ) - 1 / 2) * (-I) with hg
  have hXiCg : ∀ ρ : XiDivisorSupport, XiC (g ρ) = xi (ρ : ℂ) := by
    intro ρ
    rw [XiC]
    congr 1
    simp only [hg]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [mul_assoc, hI, mul_one]
    ring
  set S := xiSupportsPos (T - 1)
  have hsub : S.image g ⊆ Z := by
    intro z hz
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
    rw [mem_xiSupportsPos] at hρ
    have hzero : xi (ρ : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support ρ
    obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hzero
    have hball : g ρ ∈ ball (0 : ℂ) T := by
      rw [mem_ball_zero_iff]
      simp only [hg, norm_mul, norm_neg, Complex.norm_I, mul_one]
      have hn : ‖(ρ : ℂ) - 1 / 2‖ ≤ |((ρ : ℂ) - 1 / 2).re| + |((ρ : ℂ) - 1 / 2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      have hre : |((ρ : ℂ) - 1 / 2).re| < 1 / 2 := by
        rw [abs_lt]
        simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
        constructor <;> linarith
      have him : |((ρ : ℂ) - 1 / 2).im| ≤ T - 1 := by
        simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero]
        exact hρ.1
      linarith
    exact (hZzero _ hball).mp (by simp only [hFdef]; rw [hXiCg, hzero, mul_zero])
  have hinj : Set.InjOn g ↑S := by
    intro a _ b _ hab
    apply Subtype.ext
    have := congrArg (fun w => w * I + 1 / 2) hab
    simp only [hg] at this
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [mul_assoc, hI, mul_one, mul_assoc, hI, mul_one] at this
    linear_combination this
  have hcount : (xiZeroCount (T - 1) : ℝ) = ∑ z ∈ S.image g, (zeroMult F z : ℝ) := by
    rw [xiZeroCount_eq_pos_sum (by linarith), Finset.sum_image hinj]
    push_cast
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hzm, hg, analyticOrderAt_XiC_centeredCoordinate, xiSupportMultiplicity_eq_analyticOrderAt_toNat]
  rw [hcount, hsum, Complex.re_sum]
  simp only [Complex.natCast_re]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _

/-! ## The no-go theorem -/

/-- **No stability route in prime fields reaches `Ξ`.**  Normalized Lee–Yang restrictions with all
frequencies `≥ lam0 > 0` never converge locally uniformly on `ℂ` to `E · XiC` with `E` entire and
zero-free. -/
theorem not_tendsto_lyApprox_mul_XiC {A : ℕ → LYApprox} {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hfreq : ∀ n j, lam0 ≤ (A n).datum.freq j) {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hEne : ∀ z, E z ≠ 0) :
    ¬ TendstoLocallyUniformly (fun n => (A n).sect) (fun z => E z * XiC z) atTop := by
  intro hconv
  set F : ℂ → ℂ := fun z => E z * XiC z with hFdef
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hFd : Differentiable ℂ F := hE.mul hXiCd
  have hF0 : F 0 ≠ 0 := mul_ne_zero (hEne 0) XiC_zero_ne
  set κ := 2 * Real.pi / lam0 with hκ
  have hκpos : 0 < κ := by positivity
  -- a fixed admissible inner radius
  obtain ⟨T₁, hT₁, hsph₁⟩ := exists_admissible_radius hFd hF0 (κ + 1)
  set c₁ := (zeroSumBall F 0 T₁).re
  set K := c₁ / (T₁ - κ) with hK
  have hT₁κ : 1 < T₁ - κ := by linarith [hT₁.1]
  -- Riemann–von Mangoldt
  obtain ⟨Tstar, hTstar4, hclose⟩ := exists_xiZeroCount_close (1 / (4 * Real.pi)) (by positivity)
  set M := max (max (T₁ + 1) (Tstar + 1)) (max (κ + 2) (Real.exp (16 * Real.pi * (|K| + 1)) + 2))
    with hM
  obtain ⟨T₀, hT₀, hsph₀⟩ := exists_admissible_radius hFd hF0 M
  have hM1 : T₁ + 1 ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hM2 : Tstar + 1 ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hM3 : κ + 2 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM4 : Real.exp (16 * Real.pi * (|K| + 1)) + 2 ≤ M :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hT₀M := hT₀.1
  -- quasi-linear upper bound
  have hquasi := zeroSumBall_mul_le_of_tendsto hlam0 hfreq hFd hconv (by linarith [hT₁.1])
    (by linarith) hsph₀ hsph₁
  have hupper : (zeroSumBall F 0 T₀).re ≤ K * (T₀ + κ) := by
    rw [hK, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    linarith
  -- superlinear lower bound
  have hlower := xiZeroCount_le_zeroSumBall hE hEne (by linarith) hsph₀
  have hRVM := hclose (T₀ - 1) (by linarith)
  rw [abs_le] at hRVM
  have hlogpos : 16 * Real.pi * (|K| + 1) ≤ Real.log (T₀ - 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hπ := Real.pi_pos
  have hT₀1 : T₀ / 2 ≤ T₀ - 1 := by linarith
  have hlog0 : 0 ≤ Real.log (T₀ - 1) := by nlinarith [abs_nonneg K]
  have hxlow : (1 / (4 * Real.pi)) * ((T₀ - 1) * Real.log (T₀ - 1)) ≤ (xiZeroCount (T₀ - 1) : ℝ) := by
    have h := hRVM.1
    have : (1 / (2 * Real.pi)) * ((T₀ - 1) * Real.log (T₀ - 1)) -
        (1 / (4 * Real.pi)) * ((T₀ - 1) * Real.log (T₀ - 1)) =
        (1 / (4 * Real.pi)) * ((T₀ - 1) * Real.log (T₀ - 1)) := by
      field_simp; ring
    linarith
  -- the contradiction
  have hbig : 2 * (|K| + 1) * T₀ ≤ (1 / (4 * Real.pi)) * ((T₀ - 1) * Real.log (T₀ - 1)) := by
    have h1 : (T₀ / 2) * (16 * Real.pi * (|K| + 1)) ≤ (T₀ - 1) * Real.log (T₀ - 1) :=
      mul_le_mul hT₀1 hlogpos (by positivity) (by linarith)
    calc 2 * (|K| + 1) * T₀ = (1 / (4 * Real.pi)) * ((T₀ / 2) * (16 * Real.pi * (|K| + 1))) := by
          field_simp; ring
      _ ≤ (1 / (4 * Real.pi)) * ((T₀ - 1) * Real.log (T₀ - 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  have hKbound : K * (T₀ + κ) ≤ |K| * (2 * T₀) := by
    have h1 : K * (T₀ + κ) ≤ |K| * (T₀ + κ) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    have h2 : |K| * (T₀ + κ) ≤ |K| * (2 * T₀) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K)
    linarith
  nlinarith [abs_nonneg K]

end

end RHTower.LeeYangCount
