import GaloisForLFunctions.RHTower.XiGaussianOneSidedIdentityRH

/-!
# One-sided zero-side identities kill their Xi atoms

Let `A` and `B` be holomorphic on the strip `|Im z| < 1/2 + η`, with
`‖A z‖, ‖B z‖ ≤ K / (1 + ‖z‖²)` there. Write `γ_q` for the centered Xi zeros, with multiplicity. If
for every positive frequency `u`

`∑_q A(γ_q) e^{-iuγ_q} = ∫_ℝ B(t) e^{-iut} dt`,

then `A` vanishes at every centered Xi zero.

This is the common core of the zero-side receivers for restricted Weil eigenvectors: with
`A = F·Ψ` and `B = κ F·Ψ`, where `F` is the limiting transform and `Ψ` the transform of a fixed test,
it says `F·Ψ` vanishes on the Xi divisor.

**Proof.** Shift the line integral to `Im z = -Y`, `Y = 1/2 + η/2`; the vertical edges vanish by the
decay of `B`. Lift the zeros to `γ + iY` in the upper half-plane. Summability of the atoms is
`∑ 1/|γ|² < ∞`. One-sided Laplace atom rigidity then applies.
-/

open Complex MeasureTheory Set Filter Topology Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Inverse-square domination on the strip. -/
def StripInvSqDominated (η K : ℝ) (A : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, |z.im| < 1 / 2 + η → ‖A z‖ ≤ K / (1 + ‖z‖ ^ 2)

theorem integrable_line_of_stripInvSqDominated {η K : ℝ} {B : ℂ → ℂ}
    (hB : ∀ z : ℂ, |z.im| < 1 / 2 + η → DifferentiableAt ℂ B z)
    (hdom : StripInvSqDominated η K B) {y : ℝ} (hy : |y| < 1 / 2 + η) (u : ℝ) (hu : 0 ≤ u)
    (hyneg : y ≤ 0) :
    Integrable (fun x : ℝ => B ((x : ℂ) + (y : ℂ) * I) * cexp (-(I * ((x : ℂ) + (y : ℂ) * I)) * u)) := by
  have him : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * I).im = y := by intro x; simp
  have hcont : Continuous fun x : ℝ =>
      B ((x : ℂ) + (y : ℂ) * I) * cexp (-(I * ((x : ℂ) + (y : ℂ) * I)) * u) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hBc : ContinuousAt B ((x : ℂ) + (y : ℂ) * I) :=
      (hB _ (by rw [him]; exact hy)).continuousAt
    have hline : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) := by fun_prop
    have hcomp : ContinuousAt (fun x : ℝ => B ((x : ℂ) + (y : ℂ) * I)) x :=
      ContinuousAt.comp (g := B) hBc hline.continuousAt
    have he : Continuous fun x : ℝ => cexp (-(I * ((x : ℂ) + (y : ℂ) * I)) * u) := by fun_prop
    exact hcomp.mul he.continuousAt
  have hK : 0 ≤ K := by
    have := le_trans (norm_nonneg _) (hdom ((y : ℂ) * I) (by simpa using hy))
    exact nonneg_of_mul_nonneg_left (by simpa [div_eq_mul_inv] using this)
      (inv_pos.mpr (by positivity))
  have hdomInt : Integrable fun x : ℝ => K * (1 + x ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul K
  refine hdomInt.mono' hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [norm_mul, norm_cexp_neg_I_mul_ofReal, him]
  have hexp : Real.exp (u * y) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hnorm : x ^ 2 ≤ ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; nlinarith [sq_nonneg y]
  have hb := hdom ((x : ℂ) + (y : ℂ) * I) (by rw [him]; exact hy)
  calc ‖B ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (u * y)
      ≤ K / (1 + ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2) * 1 := by
        gcongr
    _ ≤ K * (1 + x ^ 2)⁻¹ := by
        rw [mul_one, div_eq_mul_inv]
        gcongr

/-- Horizontal contour shift of `B(z) e^{-iuz}` from the real line to `Im z = -Y`. -/
theorem integral_line_shift_of_stripInvSqDominated {η K Y : ℝ} {B : ℂ → ℂ}
    (hB : ∀ z : ℂ, |z.im| < 1 / 2 + η → DifferentiableAt ℂ B z)
    (hdom : StripInvSqDominated η K B) (hY : 0 < Y) (hYW : Y < 1 / 2 + η) {u : ℝ} (hu : 0 ≤ u) :
    (∫ x : ℝ, B (x : ℂ) * cexp (-(I * (x : ℂ)) * u)) =
      ∫ x : ℝ, B ((x : ℂ) + ((-Y : ℝ) : ℂ) * I) *
        cexp (-(I * ((x : ℂ) + ((-Y : ℝ) : ℂ) * I)) * u) := by
  set G : ℂ → ℂ := fun z => B z * cexp (-(I * z) * u) with hG
  have hzero : (fun x : ℝ => B (x : ℂ) * cexp (-(I * (x : ℂ)) * u)) =
      fun x : ℝ => G ((x : ℂ) + ((0 : ℝ) : ℂ) * I) := by
    funext x; simp [hG]
  have hW : 0 < 1 / 2 + η := by linarith
  have hK : 0 ≤ K := by
    have := le_trans (norm_nonneg _) (hdom 0 (by simp; linarith))
    simpa using this
  rw [hzero]
  have hstrip : ∀ z : ℂ, z.im ∈ uIcc 0 (-Y) → |z.im| < 1 / 2 + η := by
    intro z hz
    rw [uIcc_of_ge (by linarith)] at hz
    rw [abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  have hres := integral_line_shift (G := G) (a := 0) (b := -Y)
    (fun z hz => (hB z (hstrip z hz)).mul (by fun_prop))
    (by
      have := integrable_line_of_stripInvSqDominated hB hdom (y := 0) (by simpa using hW) u hu
        le_rfl
      simpa [hG] using this)
    (by
      have := integrable_line_of_stripInvSqDominated hB hdom (y := -Y)
        (by rw [abs_neg, abs_of_pos hY]; exact hYW) u hu (by linarith)
      simpa [hG] using this)
    (by
      have hedge : ∀ R : ℝ, ∀ s : ℝ, (s = R ∨ s = -R) →
          ‖∫ y in (0 : ℝ)..(-Y), G ((s : ℂ) + (y : ℂ) * I)‖ ≤
            K / (1 + R ^ 2) * |(-Y) - 0| := by
        intro R s hs
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro y hy
        rw [uIoc_of_ge (by linarith)] at hy
        have him : ((s : ℂ) + (y : ℂ) * I).im = y := by simp
        have hyabs : |((s : ℂ) + (y : ℂ) * I).im| < 1 / 2 + η := by
          rw [him, abs_lt]; constructor <;> linarith [hy.1, hy.2]
        have hb := hdom _ hyabs
        rw [hG, norm_mul, norm_cexp_neg_I_mul_ofReal, him]
        have hexp : Real.exp (u * y) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [hy.2]
        have hsR : R ^ 2 ≤ ‖(s : ℂ) + (y : ℂ) * I‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          have : s ^ 2 = R ^ 2 := by rcases hs with rfl | rfl <;> ring
          simp; nlinarith [sq_nonneg y]
        calc ‖B ((s : ℂ) + (y : ℂ) * I)‖ * Real.exp (u * y)
            ≤ K / (1 + ‖(s : ℂ) + (y : ℂ) * I‖ ^ 2) * 1 := by gcongr
          _ ≤ K / (1 + R ^ 2) := by
              rw [mul_one]
              gcongr
      have hlim : Tendsto (fun R : ℝ => 2 * (K / (1 + R ^ 2) * |(-Y) - 0|)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun R : ℝ => K / (1 + R ^ 2)) atTop (𝓝 0) := by
          apply Tendsto.div_atTop tendsto_const_nhds
          apply tendsto_atTop_add_const_left
          exact tendsto_pow_atTop (by norm_num)
        have := (h1.mul_const (|(-Y) - 0|)).const_mul 2
        simpa using this
      refine squeeze_zero (fun R => by positivity) (fun R => ?_) hlim
      have h1 := hedge R R (Or.inl rfl)
      have h2 := hedge R (-R) (Or.inr rfl)
      push_cast at h2
      linarith)
  simpa [hG] using hres

/-- **One-sided Xi atom rigidity.** -/
theorem eq_zero_of_xiOneSidedIdentity {η K : ℝ} (hη : 0 < η) {A B : ℂ → ℂ}
    (hBdiff : ∀ z : ℂ, |z.im| < 1 / 2 + η → DifferentiableAt ℂ B z)
    (hA : StripInvSqDominated η K A) (hB : StripInvSqDominated η K B)
    (hid : ∀ u : ℝ, 0 < u →
      ∑' q : XiZeroCopy, A (xiSpectralPoint q) * cexp (-(I * xiSpectralPoint q) * u) =
        ∫ t : ℝ, B (t : ℂ) * cexp (-(I * (t : ℂ)) * u))
    (q : XiZeroCopy) : A (xiSpectralPoint q) = 0 := by
  classical
  set Y : ℝ := 1 / 2 + η / 2 with hYdef
  have hY : 0 < Y := by rw [hYdef]; linarith
  have hYW : Y < 1 / 2 + η := by rw [hYdef]; linarith
  set m : XiDivisorSupport → ℕ :=
    fun ρ => Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) with hm
  set γ : XiDivisorSupport → ℂ := xiSpectralPointSupport with hγ
  set p : XiDivisorSupport → ℂ := fun ρ => γ ρ + (Y : ℂ) * I with hp
  set c : XiDivisorSupport → ℂ := fun ρ => (m ρ : ℂ) * A (γ ρ) with hc
  have hγim : ∀ ρ, |(γ ρ).im| < 1 / 2 := by
    intro ρ
    have := xiSpectralPointSupport_im_mem ρ
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  have hγW : ∀ ρ, |(γ ρ).im| < 1 / 2 + η := fun ρ => lt_trans (hγim ρ) (by linarith)
  have hpim : ∀ ρ, (p ρ).im = (γ ρ).im + Y := by intro ρ; simp [hp]
  have hγne : ∀ ρ, γ ρ ≠ 0 := by
    intro ρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_support ρ
    exact xiSpectralPoint_ne_zero q
  have hK : 0 ≤ K := by
    have := le_trans (norm_nonneg _) (hA 0 (by simp; linarith))
    simpa using this
  have hAinv : ∀ z : ℂ, |z.im| < 1 / 2 + η → z ≠ 0 → ‖A z‖ ≤ K / ‖z‖ ^ 2 := by
    intro z hz hz0
    have hpos : 0 < ‖z‖ ^ 2 := by positivity
    calc ‖A z‖ ≤ K / (1 + ‖z‖ ^ 2) := hA z hz
      _ ≤ K / ‖z‖ ^ 2 := by gcongr; linarith
  have hmcast : ∀ ρ, ((m ρ : ℕ) : ℝ) = ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    intro ρ
    have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
      le_of_lt (xi_divisor_pos_on_support ρ)
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  have hcsum : Summable fun ρ => ‖c ρ‖ := by
    refine Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) (fun ρ => ?_)
      (xi_zero_multiplicity_centered_inv_sq_summable.mul_left K)
    rw [hc, norm_mul, Complex.norm_natCast, hmcast]
    have hb := hAinv (γ ρ) (hγW ρ) (hγne ρ)
    rw [hγ, norm_xiSpectralPointSupport] at hb
    have hd : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      exact_mod_cast le_of_lt (xi_divisor_pos_on_support ρ)
    calc ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖A (xiSpectralPointSupport ρ)‖
        ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (K / ‖(ρ : ℂ) - 1 / 2‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hb hd
      _ = K * (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2) := by
          ring
  -- the boundary function on the shifted line
  set h : ℝ → ℂ := fun t => B ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) with hhdef
  have hhint : Integrable h := by
    have := integrable_line_of_stripInvSqDominated hBdiff hB (y := -Y)
      (by rw [abs_neg, abs_of_pos hY]; exact hYW) 0 le_rfl (by linarith)
    refine this.congr (ae_of_all _ fun t => ?_)
    simp [hhdef]
  have hlap : ∀ u : ℝ, 0 < u →
      ∑' ρ, c ρ * cexp (-(I * p ρ) * u) = ∫ t : ℝ, h t * cexp (-(I * t) * u) := by
    intro u hu
    have hfac : ∀ z : ℂ, cexp (-(I * (z - (Y : ℂ) * I)) * u) =
        cexp (-(I * z) * u) * cexp (-((Y * u : ℝ) : ℂ)) := by
      intro z
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
      rw [I_sq]
      ring
    have hexpne : cexp (-((Y * u : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hGsum : Summable fun q : XiZeroCopy =>
        A (xiSpectralPoint q) * cexp (-(I * xiSpectralPoint q) * u) := by
      refine Summable.of_norm_bounded
        (g := fun q : XiZeroCopy => K * Real.exp (u / 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
        (xiSpectralPoint_inv_sq_summable.mul_left _) (fun q => ?_)
      have hq := hAinv (xiSpectralPoint q) (hγW q.1) (xiSpectralPoint_ne_zero q)
      rw [norm_mul, norm_cexp_neg_I_mul_ofReal]
      have hexp : Real.exp (u * (xiSpectralPoint q).im) ≤ Real.exp (u / 2) := by
        apply Real.exp_le_exp.mpr
        have hlt : (xiSpectralPoint q).im < 1 / 2 := (abs_lt.mp (hγim q.1)).2
        nlinarith
      calc ‖A (xiSpectralPoint q)‖ * Real.exp (u * (xiSpectralPoint q).im)
          ≤ K / ‖xiSpectralPoint q‖ ^ 2 * Real.exp (u / 2) := by gcongr
        _ = K * Real.exp (u / 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
    have hlhs : ∑' q : XiZeroCopy, A (xiSpectralPoint q) * cexp (-(I * xiSpectralPoint q) * u) =
        ∑' ρ, (m ρ : ℂ) * (A (γ ρ) * cexp (-(I * γ ρ) * u)) := by
      rw [hGsum.tsum_sigma' (fun ρ => (hasSum_fintype _).summable)]
      refine tsum_congr fun ρ => ?_
      rw [tsum_fintype]
      simp only [xiSpectralPoint_eq_support, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hγ, hm]
    have hlhs' : ∑' ρ, (m ρ : ℂ) * (A (γ ρ) * cexp (-(I * γ ρ) * u)) =
        (∑' ρ, c ρ * cexp (-(I * p ρ) * u)) * cexp (-((Y * u : ℝ) : ℂ)) := by
      rw [← tsum_mul_right]
      refine tsum_congr fun ρ => ?_
      have hγp : γ ρ = p ρ - (Y : ℂ) * I := by simp [hp]
      rw [hc]
      conv_lhs => rw [hγp]
      rw [hfac (p ρ), ← hγp]
      ring
    have hrhs : (∫ t : ℝ, B (t : ℂ) * cexp (-(I * (t : ℂ)) * u)) =
        (∫ t : ℝ, h t * cexp (-(I * t) * u)) * cexp (-((Y * u : ℝ) : ℂ)) := by
      rw [integral_line_shift_of_stripInvSqDominated hBdiff hB hY hYW hu.le,
        ← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      have hshift : ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) = (t : ℂ) - (Y : ℂ) * I := by
        push_cast; ring
      simp only [hhdef]
      rw [hshift, hfac (t : ℂ)]
      ring
    have := hid u hu
    rw [hlhs, hlhs', hrhs] at this
    exact mul_right_cancel₀ hexpne this
  have hpinj : Function.Injective p := by
    intro ρ τ hρτ
    apply xiSpectralPointSupport_injective
    simpa [hp] using hρτ
  have hppos : ∀ ρ, 0 < (p ρ).im := by
    intro ρ
    rw [hpim]
    linarith [(abs_lt.mp (hγim ρ)).1]
  have hpB : ∀ ρ, (p ρ).im ≤ 1 / 2 + Y := by
    intro ρ
    rw [hpim]
    linarith [(abs_lt.mp (hγim ρ)).2]
  have hpdisc : ∀ z : ℂ, 0 < z.im → ∃ r > 0, ∀ ρ, p ρ ∈ ball z r → p ρ = z := by
    intro z _
    obtain ⟨r, hr, hball⟩ := exists_ball_xiSpectralPointSupport_eq (z - (Y : ℂ) * I)
    refine ⟨r, hr, fun ρ hρ => ?_⟩
    have hmem : γ ρ ∈ ball (z - (Y : ℂ) * I) r := by
      rw [mem_ball, dist_eq_norm] at hρ ⊢
      have : γ ρ - (z - (Y : ℂ) * I) = p ρ - z := by simp [hp]; ring
      rw [this]; exact hρ
    have := hball ρ hmem
    simp only [hp]
    rw [show xiSpectralPointSupport ρ = γ ρ from rfl] at this
    rw [this]; ring
  have hc0 := eq_zero_of_oneSidedLaplace_eq hpinj hcsum hppos hpB hpdisc hhint hlap q.1
  have hm0 : (m q.1 : ℂ) ≠ 0 := by
    have hpos := xi_divisor_pos_on_support q.1
    have : 0 < m q.1 := by simp only [hm]; omega
    exact_mod_cast this.ne'
  rw [hc] at hc0
  have hA0 := (mul_eq_zero.mp hc0).resolve_left hm0
  simpa [hγ, xiSpectralPoint_eq_support] using hA0

end

end RHTower
