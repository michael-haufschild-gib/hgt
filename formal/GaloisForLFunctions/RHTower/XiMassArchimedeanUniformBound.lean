import GaloisForLFunctions.RHTower.XiMassEulerContourSourceIdentity
import GaloisForLFunctions.RHTower.RectangleLocalWeightedCauchyResidue
import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# Uniform complex-time bound for the mass archimedean edge

The mass-weighted completed archimedean bottom integral shifts exactly to the centered real line.
The only crossed zero is the simple factor at `s = 1`, whose centered mass frequency is real for
`a > 1/2`.  Consequently the complete archimedean contribution is uniformly bounded on every
positive complex-time vertical line.  All RH-strength growth is therefore confined to the prime
channel of the exact mass source identity.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Centered-to-Euler affine coordinate. -/
def xiMassCenteredArchPoint (z : ℂ) : ℂ := 1 / 2 + z * I

/-- The unique archimedean zero crossed between depth `c>1/2` and the centered line. -/
def xiMassArchPole : ℂ := -I / 2

/-- Nonvanishing factor after extracting the centered `s-1` zero. -/
def xiMassCenteredArchCofactor (z : ℂ) : ℂ :=
  (xiMassCenteredArchPoint z * I / 2) * Gammaℝ (xiMassCenteredArchPoint z)

/-- Natural joint domain for the mass branch and the right-half-plane Gamma factor. -/
def xiMassArchShiftDomain (a : ℝ) : Set ℂ :=
  xiMassStrip a ∩ {z : ℂ | z.im < 1 / 2}

theorem isOpen_xiMassArchShiftDomain (a : ℝ) : IsOpen (xiMassArchShiftDomain a) := by
  exact (isOpen_xiMassStrip a).inter
    (isOpen_lt Complex.continuous_im continuous_const)

theorem xiMassCenteredArchPoint_re (z : ℂ) :
    (xiMassCenteredArchPoint z).re = 1 / 2 - z.im := by
  simp [xiMassCenteredArchPoint, Complex.mul_re, sub_eq_add_neg]

theorem xiMassCenteredArchPoint_re_pos {a : ℝ} {z : ℂ}
    (hz : z ∈ xiMassArchShiftDomain a) :
    0 < (xiMassCenteredArchPoint z).re := by
  change z ∈ xiMassStrip a ∧ z.im < 1 / 2 at hz
  rw [xiMassCenteredArchPoint_re]
  linarith [hz.2]

theorem archFactor_centered_factorization (z : ℂ) :
    archFactor (xiMassCenteredArchPoint z) =
      (z - xiMassArchPole) * xiMassCenteredArchCofactor z := by
  have hs : xiMassCenteredArchPoint z - 1 = I * (z - xiMassArchPole) := by
    unfold xiMassCenteredArchPoint xiMassArchPole
    apply Complex.ext
    · simp [Complex.mul_re]
      ring
    · simp [Complex.mul_im]
  rw [archFactor, hs]
  unfold xiMassCenteredArchCofactor
  ring

theorem analyticOnNhd_xiMassCenteredArchCofactor {a : ℝ} :
    AnalyticOnNhd ℂ xiMassCenteredArchCofactor (xiMassArchShiftDomain a) := by
  intro z hz
  have hs : AnalyticAt ℂ xiMassCenteredArchPoint z := by
    unfold xiMassCenteredArchPoint
    fun_prop
  have hG0 : Gammaℝ (xiMassCenteredArchPoint z) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (xiMassCenteredArchPoint_re_pos hz)
  have hG : AnalyticAt ℂ (fun w => Gammaℝ (xiMassCenteredArchPoint w)) z :=
    (Gammaℝ_analyticAt hG0).comp hs
  have hprod : AnalyticAt ℂ (fun w => xiMassCenteredArchPoint w * I) z :=
    hs.mul analyticAt_const
  have hdiv : AnalyticAt ℂ (fun w => xiMassCenteredArchPoint w * I / 2) z :=
    hprod.div_const
  exact hdiv.mul hG

theorem xiMassCenteredArchCofactor_ne_zero {a : ℝ} {z : ℂ}
    (hz : z ∈ xiMassArchShiftDomain a) :
    xiMassCenteredArchCofactor z ≠ 0 := by
  have hs0 : xiMassCenteredArchPoint z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.zero_re] at hre
    linarith [xiMassCenteredArchPoint_re_pos hz]
  have hG0 : Gammaℝ (xiMassCenteredArchPoint z) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (xiMassCenteredArchPoint_re_pos hz)
  unfold xiMassCenteredArchCofactor
  exact mul_ne_zero (div_ne_zero (mul_ne_zero hs0 I_ne_zero) (by norm_num)) hG0

private theorem xiMassArchRectangle_subset_domain
    {a c R : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hR : 0 < R) :
    (uIcc ((((-R : ℝ) : ℂ) - c * I)).re ((R : ℂ)).re ×ℂ
      uIcc ((((-R : ℝ) : ℂ) - c * I)).im ((R : ℂ)).im) ⊆
      xiMassArchShiftDomain a := by
  intro z hz
  have hre : -R ≤ z.re ∧ z.re ≤ R := by
    have := (Complex.mem_reProdIm.mp hz).1
    have hRR : -R ≤ R := by linarith
    rw [show ((((-R : ℝ) : ℂ) - c * I)).re = -R by simp [Complex.mul_re],
      show ((R : ℂ)).re = R by simp, uIcc_of_le hRR] at this
    exact this
  have him : -c ≤ z.im ∧ z.im ≤ 0 := by
    have := (Complex.mem_reProdIm.mp hz).2
    have hc0 : -c ≤ 0 := by linarith
    rw [show ((((-R : ℝ) : ℂ) - c * I)).im = -c by simp [Complex.mul_im],
      show ((R : ℂ)).im = 0 by simp, uIcc_of_le hc0] at this
    exact this
  change z ∈ xiMassStrip a ∧ z.im < 1 / 2
  constructor
  · change |z.im| < a
    rw [abs_lt]
    constructor <;> linarith
  · linarith

/-- Finite rectangle extracts exactly the crossed archimedean zero. -/
theorem rectIntegral_xiMass_mul_logDeriv_centeredArchFactor
    {a c R : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hR : 0 < R)
    (τ : ℂ) :
    rectIntegral
      (fun z => xiMassAnalyticTest a τ z *
        logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z)
      (((-R : ℝ) : ℂ) - c * I) (R : ℂ) =
        2 * Real.pi * I * xiMassAnalyticTest a τ xiMassArchPole := by
  let z₁ : ℂ := (((-R : ℝ) : ℂ) - c * I)
  let z₂ : ℂ := (R : ℂ)
  let U : Set ℂ := xiMassArchShiftDomain a
  let ρ : Unit → ℂ := fun _ => xiMassArchPole
  let m : Unit → ℕ := fun _ => 1
  let h : ℂ → ℂ := xiMassCenteredArchCofactor
  have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    simpa only [z₁, z₂, U] using xiMassArchRectangle_subset_domain hhalf hca hR
  have hin : ∀ i ∈ ({()} : Finset Unit),
      z₁.re < (ρ i).re ∧ (ρ i).re < z₂.re ∧
        z₁.im < (ρ i).im ∧ (ρ i).im < z₂.im := by
    intro i _
    have hi : i = () := Subsingleton.elim _ _
    subst i
    have hz₁re : z₁.re = -R := by simp [z₁, Complex.mul_re]
    have hz₂re : z₂.re = R := by simp [z₂]
    have hz₁im : z₁.im = -c := by simp [z₁, Complex.mul_im]
    have hz₂im : z₂.im = 0 := by simp [z₂]
    have hρre : (ρ ()).re = 0 := by
      simp [ρ, xiMassArchPole]
    have hρim : (ρ ()).im = -(1 / 2) := by
      norm_num [ρ, xiMassArchPole, Complex.div_im, Complex.normSq]
    rw [hz₁re, hz₂re, hz₁im, hz₂im, hρre, hρim]
    constructor
    · linarith
    constructor
    · exact hR
    constructor <;> linarith
  have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
    ({()} : Finset Unit) ρ m
    (f := fun z => archFactor (xiMassCenteredArchPoint z))
    (g := xiMassAnalyticTest a τ) (h := h) (z₁ := z₁) (z₂ := z₂) (U := U)
    (isOpen_xiMassArchShiftDomain a)
    ((analyticOnNhd_xiMassAnalyticTest ha τ).mono (fun _ hz => hz.1))
    hin hsub analyticOnNhd_xiMassCenteredArchCofactor
    (fun z hz => xiMassCenteredArchCofactor_ne_zero hz)
    (fun z _ => by
      rw [archFactor_centered_factorization]
      simp only [Finset.prod_singleton, m, ρ, h, pow_one])
  simpa only [z₁, z₂, ρ, m, Finset.sum_singleton, Nat.cast_one, one_mul] using hres

theorem logDeriv_centeredArchFactor_eq_I_mul (z : ℂ)
    (hpos : 0 < (xiMassCenteredArchPoint z).re) :
    logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z =
      I * logDeriv archFactor (xiMassCenteredArchPoint z) := by
  have hs : HasDerivAt xiMassCenteredArchPoint I z := by
    change HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I z
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id z).mul_const I).const_add (1 / 2 : ℂ)
  have harch := hasDerivAt_archFactor_of_re_pos hpos
  have hcomp := harch.comp z hs
  change HasDerivAt (fun w => archFactor (xiMassCenteredArchPoint w))
    (archFactorDeriv (xiMassCenteredArchPoint z) * I) z at hcomp
  rw [logDeriv_apply, logDeriv_apply, hcomp.deriv, harch.deriv]
  ring

/-- Same finite residue law in the original Euler logarithmic-derivative normalization. -/
theorem rectIntegral_xiMass_mul_archLogDeriv
    {a c R : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hR : 0 < R)
    (τ : ℂ) :
    rectIntegral
      (fun z => xiMassAnalyticTest a τ z *
        logDeriv archFactor (xiMassCenteredArchPoint z))
      (((-R : ℝ) : ℂ) - c * I) (R : ℂ) =
        2 * Real.pi * xiMassAnalyticTest a τ xiMassArchPole := by
  have hres := rectIntegral_xiMass_mul_logDeriv_centeredArchFactor hhalf hca hR τ
  have hcongr : rectIntegral
      (fun z => xiMassAnalyticTest a τ z *
        logDeriv archFactor (xiMassCenteredArchPoint z))
      (((-R : ℝ) : ℂ) - c * I) (R : ℂ) =
      (-I) * rectIntegral
        (fun z => xiMassAnalyticTest a τ z *
          logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z)
        (((-R : ℝ) : ℂ) - c * I) (R : ℂ) := by
    let z₁ : ℂ := (((-R : ℝ) : ℂ) - c * I)
    let z₂ : ℂ := (R : ℂ)
    let S : Set ℂ := uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im
    have hsub : S ⊆ xiMassArchShiftDomain a := by
      simpa only [S, z₁, z₂] using xiMassArchRectangle_subset_domain hhalf hca hR
    have hedges : rectIntegral
        (fun z => xiMassAnalyticTest a τ z *
          logDeriv archFactor (xiMassCenteredArchPoint z)) z₁ z₂ =
        rectIntegral
          (fun z => (-I) * (xiMassAnalyticTest a τ z *
            logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z)) z₁ z₂ := by
      apply rectIntegral_congr (S := S)
      · intro z hz
        rw [logDeriv_centeredArchFactor_eq_I_mul z
          (xiMassCenteredArchPoint_re_pos (hsub hz))]
        calc
          xiMassAnalyticTest a τ z * logDeriv archFactor (xiMassCenteredArchPoint z) =
              (-I * I) * (xiMassAnalyticTest a τ z *
                logDeriv archFactor (xiMassCenteredArchPoint z)) := by
            rw [neg_mul, Complex.I_mul_I]
            ring
          _ = -I * (xiMassAnalyticTest a τ z *
                (I * logDeriv archFactor (xiMassCenteredArchPoint z))) := by ring
      · intro x hx
        apply Complex.mem_reProdIm.mpr
        exact ⟨by simpa [Complex.mul_re] using hx,
          by simp [Complex.mul_im]⟩
      · intro x hx
        apply Complex.mem_reProdIm.mpr
        exact ⟨by simpa [Complex.mul_re] using hx,
          by simp [Complex.mul_im]⟩
      · intro y hy
        apply Complex.mem_reProdIm.mpr
        exact ⟨by simp [Complex.mul_re],
          by simpa [Complex.mul_im] using hy⟩
      · intro y hy
        apply Complex.mem_reProdIm.mpr
        exact ⟨by simp [Complex.mul_re],
          by simpa [Complex.mul_im] using hy⟩
    rw [show (((-R : ℝ) : ℂ) - c * I) = z₁ by rfl,
      show (R : ℂ) = z₂ by rfl, hedges, rectIntegral_const_mul]
  rw [hcongr, hres]
  calc
    -I * (2 * Real.pi * I * xiMassAnalyticTest a τ xiMassArchPole) =
        2 * Real.pi * (-I * I) * xiMassAnalyticTest a τ xiMassArchPole := by ring
    _ = 2 * Real.pi * xiMassAnalyticTest a τ xiMassArchPole := by
      rw [neg_mul, Complex.I_mul_I]
      ring

/-- Euler point on a vertical side of the centered archimedean shift rectangle. -/
def xiMassArchVerticalEulerPoint (R y : ℝ) : ℂ :=
  xiMassCenteredArchPoint ((R : ℂ) + y * I)

theorem xiMassArchVerticalEulerPoint_eq (R y : ℝ) :
    xiMassArchVerticalEulerPoint R y =
      (((1 / 2 - y : ℝ) : ℂ) + R * I) := by
  unfold xiMassArchVerticalEulerPoint xiMassCenteredArchPoint
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp [Complex.mul_im]

theorem xiMassArchVerticalEulerPoint_re (R y : ℝ) :
    (xiMassArchVerticalEulerPoint R y).re = 1 / 2 - y := by
  rw [xiMassArchVerticalEulerPoint_eq]
  simp [Complex.mul_re]

theorem xiMassArchVerticalEulerPoint_im (R y : ℝ) :
    (xiMassArchVerticalEulerPoint R y).im = R := by
  rw [xiMassArchVerticalEulerPoint_eq]
  simp [Complex.mul_im]

/-- Digamma grows at most linearly, uniformly across the whole finite shift depth. -/
theorem norm_digamma_xiMassArchVerticalEulerPoint_half_le
    {c R y : ℝ} (hy : -c ≤ y ∧ y ≤ 0)
    (hR : max 2 (1 / 2 + c) ≤ |R|) :
    ‖Complex.digamma (xiMassArchVerticalEulerPoint R y / 2)‖ ≤
      |R| + GaloisForLFunctions.digammaVerticalLogConstant := by
  let σ : ℝ := (1 / 2 - y) / 2
  let t : ℝ := |R| / 2
  have hσ : 0 < σ := by dsimp only [σ]; linarith
  have ht1 : 1 ≤ t := by
    dsimp only [t]
    have := le_trans (le_max_left 2 (1 / 2 + c)) hR
    linarith
  have hσt : σ ≤ t := by
    dsimp only [σ, t]
    have htop := le_trans (le_max_right 2 (1 / 2 + c)) hR
    linarith
  have hbound := GaloisForLFunctions.norm_digamma_vertical_le_log hσ ht1 hσt
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hlog : Real.log t ≤ |R| := by
    have h := Real.log_le_sub_one_of_pos ht
    dsimp only [t] at h ⊢
    linarith [abs_nonneg R]
  have hfinal : Real.log t + GaloisForLFunctions.digammaVerticalLogConstant ≤
      |R| + GaloisForLFunctions.digammaVerticalLogConstant := by linarith
  by_cases hR0 : 0 ≤ R
  · have harg : xiMassArchVerticalEulerPoint R y / 2 =
        (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;>
        simp [xiMassArchVerticalEulerPoint_eq, σ, t, abs_of_nonneg hR0,
          Complex.mul_re, Complex.mul_im]
    rw [harg]
    exact hbound.trans hfinal
  · have hRneg : R < 0 := lt_of_not_ge hR0
    have harg : xiMassArchVerticalEulerPoint R y / 2 =
        (starRingEnd ℂ) ((((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I)) := by
      apply Complex.ext <;>
        simp [xiMassArchVerticalEulerPoint_eq, σ, t, abs_of_neg hRneg,
          Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im] <;> ring
    rw [harg, ReflectedDigammaAnomaly.digamma_conj, norm_conj]
    exact hbound.trans hfinal

/-- Uniform constant for vertical-side archimedean logarithmic growth. -/
def xiMassArchVerticalGrowthConstant : ℝ :=
  2 + |Real.log Real.pi| / 2 +
    GaloisForLFunctions.digammaVerticalLogConstant / 2

theorem xiMassArchVerticalGrowthConstant_nonneg :
    0 ≤ xiMassArchVerticalGrowthConstant := by
  unfold xiMassArchVerticalGrowthConstant
  have hD : 0 ≤ GaloisForLFunctions.digammaVerticalLogConstant := by
    unfold GaloisForLFunctions.digammaVerticalLogConstant
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  positivity

/-- Archimedean logarithmic derivative has one uniform linear majorant on both vertical sides. -/
theorem norm_logDeriv_archFactor_xiMassArchVertical_le
    {c R y : ℝ} (hy : -c ≤ y ∧ y ≤ 0)
    (hR : max 2 (1 / 2 + c) ≤ |R|) :
    ‖logDeriv archFactor (xiMassArchVerticalEulerPoint R y)‖ ≤
      xiMassArchVerticalGrowthConstant + |R| / 2 := by
  let s : ℂ := xiMassArchVerticalEulerPoint R y
  have hsre : s.re = 1 / 2 - y := xiMassArchVerticalEulerPoint_re R y
  have hsim : s.im = R := xiMassArchVerticalEulerPoint_im R y
  have hRtwo : 2 ≤ |R| := (le_max_left 2 (1 / 2 + c)).trans hR
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, abs_zero] at hRtwo
    norm_num at hRtwo
  have hs0 : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [hsim, Complex.zero_im] at him
    exact hR0 him
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    rw [hsim, Complex.one_im] at him
    exact hR0 him
  have hspos : 0 < s.re := by rw [hsre]; linarith
  have hsNorm : 1 ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    rw [hsim] at him
    linarith
  have hsSubNorm : 1 ≤ ‖s - 1‖ := by
    have him := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, hsim, Complex.one_im, sub_zero] at him
    linarith
  have hInv : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (norm_pos_iff.mpr hs0)).2 hsNorm
  have hInvSub : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).2 hsSubNorm
  have hgamma : ‖GaloisForLFunctions.gammaRealLogConnection s‖ ≤
      |Real.log Real.pi| / 2 +
        (|R| + GaloisForLFunctions.digammaVerticalLogConstant) / 2 := by
    unfold GaloisForLFunctions.gammaRealLogConnection
    change ‖-((Real.log Real.pi : ℂ) / 2) + Complex.digamma (s / 2) / 2‖ ≤ _
    calc
      ‖-((Real.log Real.pi : ℂ) / 2) + Complex.digamma (s / 2) / 2‖ ≤
          ‖-((Real.log Real.pi : ℂ) / 2)‖ + ‖Complex.digamma (s / 2) / 2‖ :=
        norm_add_le _ _
      _ = |Real.log Real.pi| / 2 + ‖Complex.digamma (s / 2)‖ / 2 := by
        simp only [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_ofNat]
      _ ≤ _ := by
        have hdig := norm_digamma_xiMassArchVerticalEulerPoint_half_le hy hR
        change ‖Complex.digamma (xiMassArchVerticalEulerPoint R y / 2)‖ ≤ _ at hdig
        dsimp only [s]
        nlinarith
  rw [logDeriv_archFactor_closed hspos hs0 hs1]
  calc
    ‖1 / s + 1 / (s - 1) + GaloisForLFunctions.gammaRealLogConnection s‖ ≤
        ‖1 / s‖ + ‖1 / (s - 1)‖ +
          ‖GaloisForLFunctions.gammaRealLogConnection s‖ := by
      calc
        _ ≤ ‖1 / s + 1 / (s - 1)‖ +
            ‖GaloisForLFunctions.gammaRealLogConnection s‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 1 + 1 + (|Real.log Real.pi| / 2 +
        (|R| + GaloisForLFunctions.digammaVerticalLogConstant) / 2) := by
      exact add_le_add (add_le_add hInv hInvSub) hgamma
    _ = xiMassArchVerticalGrowthConstant + |R| / 2 := by
      unfold xiMassArchVerticalGrowthConstant
      ring

/-- Mass-weighted archimedean integrand on a vertical side. -/
def xiMassArchVerticalIntegrand (a : ℝ) (τ : ℂ) (R y : ℝ) : ℂ :=
  xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
    logDeriv archFactor (xiMassArchVerticalEulerPoint R y)

/-- Explicit side majorant; exponential horizontal decay absorbs linear Gamma growth. -/
def xiMassArchVerticalMajorant (c : ℝ) (τ : ℂ) (R : ℝ) : ℝ :=
  c * Real.exp (-τ.re * |R| + |τ.im| * c) *
    (xiMassArchVerticalGrowthConstant + |R| / 2)

theorem xiMassArchVerticalMajorant_nonneg {c : ℝ} (hc : 0 ≤ c) (τ : ℂ) (R : ℝ) :
    0 ≤ xiMassArchVerticalMajorant c τ R := by
  unfold xiMassArchVerticalMajorant
  exact mul_nonneg
    (mul_nonneg hc (Real.exp_pos _).le)
    (add_nonneg xiMassArchVerticalGrowthConstant_nonneg (by positivity))

theorem norm_xiMassArchVerticalIntegrand_le
    {a c R y : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (hy : -c ≤ y ∧ y ≤ 0)
    (hR : max 2 (1 / 2 + c) ≤ |R|) :
    ‖xiMassArchVerticalIntegrand a τ R y‖ ≤
      Real.exp (-τ.re * |R| + |τ.im| * c) *
        (xiMassArchVerticalGrowthConstant + |R| / 2) := by
  have hc0 : 0 < c := lt_trans (by norm_num) hhalf
  have hyabs : |y| ≤ c := by rw [abs_le]; constructor <;> linarith
  have hzmem : ((R : ℂ) + y * I) ∈ xiMassStrip a := by
    change |(((R : ℂ) + y * I)).im| < a
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      zero_mul, mul_one, zero_add]
    simpa using hyabs.trans_lt hca
  have hm0 := norm_xiMassAnalyticTest_le
    (lt_trans (lt_trans (by norm_num) hhalf) hca) hτ.le hzmem
  have hm : ‖xiMassAnalyticTest a τ ((R : ℂ) + y * I)‖ ≤
      Real.exp (-τ.re * |R| + |τ.im| * c) := by
    calc
      _ ≤ Real.exp (-τ.re * |(((R : ℂ) + y * I)).re| +
          |τ.im| * |(((R : ℂ) + y * I)).im|) := hm0
      _ ≤ _ := by
        rw [Real.exp_le_exp]
        have hre : |(((R : ℂ) + y * I)).re| = |R| := by
          simp [Complex.mul_re]
        have him : |(((R : ℂ) + y * I)).im| = |y| := by
          simp [Complex.mul_im]
        rw [hre, him]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hyabs (abs_nonneg τ.im))
  have ha := norm_logDeriv_archFactor_xiMassArchVertical_le hy hR
  rw [xiMassArchVerticalIntegrand, norm_mul]
  exact mul_le_mul hm ha (norm_nonneg _) (Real.exp_pos _).le

/-- Quantitative bound for either finite vertical side. -/
theorem norm_integral_xiMassArchVerticalIntegrand_le
    {a c R : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re)
    (hR : max 2 (1 / 2 + c) ≤ |R|) :
    ‖∫ y in -c..0, xiMassArchVerticalIntegrand a τ R y‖ ≤
      xiMassArchVerticalMajorant c τ R := by
  have hc0 : 0 < c := lt_trans (by norm_num) hhalf
  have hpoint : ∀ y ∈ uIoc (-c) 0,
      ‖xiMassArchVerticalIntegrand a τ R y‖ ≤
        Real.exp (-τ.re * |R| + |τ.im| * c) *
          (xiMassArchVerticalGrowthConstant + |R| / 2) := by
    intro y hy
    have hyIoc : y ∈ Ioc (-c) 0 := by
      simpa [uIoc_of_le (by linarith : -c ≤ 0)] using hy
    exact norm_xiMassArchVerticalIntegrand_le hhalf hca hτ
      ⟨hyIoc.1.le, hyIoc.2⟩ hR
  calc
    ‖∫ y in -c..0, xiMassArchVerticalIntegrand a τ R y‖ ≤
        (Real.exp (-τ.re * |R| + |τ.im| * c) *
          (xiMassArchVerticalGrowthConstant + |R| / 2)) * |0 - (-c)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = xiMassArchVerticalMajorant c τ R := by
      rw [abs_of_nonneg (by linarith : 0 ≤ 0 - -c)]
      unfold xiMassArchVerticalMajorant
      ring

theorem tendsto_xiMassArchVerticalMajorant_atTop
    {c : ℝ} (_hhalf : 1 / 2 < c) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (xiMassArchVerticalMajorant c τ) atTop (𝓝 0) := by
  let C : ℝ := xiMassArchVerticalGrowthConstant
  have hpow (n : ℕ) :
      Tendsto (fun R : ℝ => R ^ n * Real.exp (-τ.re * R)) atTop (𝓝 0) := by
    have hraw := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) τ.re hτ
    apply hraw.congr'
    filter_upwards with R
    exact congrArg (fun u : ℝ => u * Real.exp (-τ.re * R))
      (Real.rpow_natCast R n)
  have hpoly : Tendsto (fun R : ℝ =>
      (C + R / 2) * Real.exp (-τ.re * R)) atTop (𝓝 0) := by
    have h0 := (hpow 0).const_mul C
    have h1 := (hpow 1).const_mul (1 / 2 : ℝ)
    have hsum := h0.add h1
    convert hsum using 1
    · funext R
      ring
    · norm_num
  have hscaled := hpoly.const_mul (c * Real.exp (|τ.im| * c))
  have hscaled' : Tendsto (fun R : ℝ =>
      c * Real.exp (|τ.im| * c) *
        ((C + R / 2) * Real.exp (-τ.re * R))) atTop (𝓝 0) := by
    simpa using hscaled
  apply hscaled'.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR0
  unfold xiMassArchVerticalMajorant
  rw [show |R| = R by exact abs_of_nonneg hR0]
  dsimp only [C]
  rw [Real.exp_add]
  ring

/-- Right archimedean side vanishes as the rectangle exhausts horizontally. -/
theorem tendsto_integral_xiMassArchVerticalIntegrand_right_atTop
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun R : ℝ => ∫ y in -c..0,
      xiMassArchVerticalIntegrand a τ R y) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_xiMassArchVerticalMajorant_atTop hhalf hτ)
  filter_upwards [eventually_ge_atTop (max 2 (1 / 2 + c))] with R hR
  have hR0 : 0 ≤ R := by
    have : 2 ≤ R := (le_max_left 2 (1 / 2 + c)).trans hR
    linarith
  simpa [abs_of_nonneg hR0] using
    (norm_integral_xiMassArchVerticalIntegrand_le hhalf hca hτ
      (show max 2 (1 / 2 + c) ≤ |R| by simpa [abs_of_nonneg hR0] using hR))

/-- Left archimedean side vanishes as the rectangle exhausts horizontally. -/
theorem tendsto_integral_xiMassArchVerticalIntegrand_left_atTop
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun R : ℝ => ∫ y in -c..0,
      xiMassArchVerticalIntegrand a τ (-R) y) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_xiMassArchVerticalMajorant_atTop hhalf hτ)
  filter_upwards [eventually_ge_atTop (max 2 (1 / 2 + c))] with R hR
  have hR0 : 0 ≤ R := by
    have : 2 ≤ R := (le_max_left 2 (1 / 2 + c)).trans hR
    linarith
  have hbound := norm_integral_xiMassArchVerticalIntegrand_le hhalf hca hτ
    (R := -R) (show max 2 (1 / 2 + c) ≤ |-R| by
      rw [abs_neg, abs_of_nonneg hR0]
      exact hR)
  simpa [xiMassArchVerticalMajorant, abs_of_nonneg hR0] using hbound

/-- Archimedean integrand on the centered real line after contour shift. -/
def xiMassCenteredArchIntegrand (a : ℝ) (τ : ℂ) (x : ℝ) : ℂ :=
  xiMassAnalyticTest a τ (x : ℂ) *
    logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))

theorem continuous_xiMassCenteredArchTest {a : ℝ} (ha : 0 < a) (τ : ℂ) :
    Continuous (fun x : ℝ => xiMassAnalyticTest a τ (x : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hz : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    change HasDerivAt (⇑Complex.ofRealCLM) 1 x
    exact Complex.ofRealCLM.hasDerivAt
  have hmem : (x : ℂ) ∈ xiMassStrip a := by
    change |((x : ℂ)).im| < a
    simpa using ha
  exact ((hasDerivAt_xiMassAnalyticTest ha τ hmem).comp x hz).continuousAt

theorem continuous_xiMassCenteredArchLogDeriv :
    Continuous (fun x : ℝ =>
      logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))) := by
  let s : ℝ → ℂ := fun x => xiMassCenteredArchPoint (x : ℂ)
  have hs : Continuous s := by
    dsimp only [s, xiMassCenteredArchPoint]
    fun_prop
  have hsre : ∀ x : ℝ, (s x).re = 1 / 2 := by
    intro x
    simp [s, xiMassCenteredArchPoint, Complex.mul_re]
  have hmaps : MapsTo s univ {z : ℂ | 0 < z.re} := by
    intro x _
    simp only [mem_setOf_eq, hsre]
    norm_num
  have hderiv : Continuous (fun x : ℝ => archFactorDeriv (s x)) :=
    continuousOn_archFactorDeriv.comp_continuous hs (fun x => hmaps (mem_univ x))
  have hfactor : Continuous (fun x : ℝ => archFactor (s x)) :=
    archFactor_analyticOnNhd_re_pos.continuousOn.comp_continuous hs
      (fun x => hmaps (mem_univ x))
  have hfactor0 : ∀ x : ℝ, archFactor (s x) ≠ 0 := by
    intro x
    have hs0 : s x ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      rw [hsre, Complex.zero_re] at hre
      norm_num at hre
    have hs1 : s x ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      rw [hsre, Complex.one_re] at hre
      norm_num at hre
    exact archFactor_ne_zero hs0 hs1
      (Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num))
  rw [show (fun x : ℝ => logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))) =
      fun x : ℝ => archFactorDeriv (s x) / archFactor (s x) by
    funext x
    rw [logDeriv_apply, (hasDerivAt_archFactor_of_re_pos
      (by rw [hsre]; norm_num)).deriv]]
  exact hderiv.div hfactor hfactor0

theorem continuous_xiMassCenteredArchIntegrand {a : ℝ} (ha : 0 < a) (τ : ℂ) :
    Continuous (xiMassCenteredArchIntegrand a τ) := by
  exact (continuous_xiMassCenteredArchTest ha τ).mul
    continuous_xiMassCenteredArchLogDeriv

theorem norm_xiMassCenteredArchIntegrand_le
    {a σ u x : ℝ} (ha : 0 < a) (hσ : 0 < σ) (hx : 2 ≤ |x|) :
    ‖xiMassCenteredArchIntegrand a (σ + u * I) x‖ ≤
      Real.exp (-(σ * |x|)) *
        (xiMassArchVerticalGrowthConstant + |x| / 2) := by
  have hmem : (x : ℂ) ∈ xiMassStrip a := by
    change |((x : ℂ)).im| < a
    simpa using ha
  have hm0 := norm_xiMassAnalyticTest_le ha (show 0 ≤ (σ + u * I : ℂ).re by
    simp [Complex.mul_re]; exact hσ.le) hmem
  have hm : ‖xiMassAnalyticTest a (σ + u * I) (x : ℂ)‖ ≤
      Real.exp (-(σ * |x|)) := by
    simpa [Complex.mul_re, Complex.mul_im] using hm0
  have harch := norm_logDeriv_archFactor_xiMassArchVertical_le
    (c := (1 : ℝ)) (R := x) (y := 0)
    (show -(1 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0 by norm_num)
    (show max 2 (1 / 2 + (1 : ℝ)) ≤ |x| by norm_num at hx ⊢; exact hx)
  rw [xiMassCenteredArchIntegrand, norm_mul]
  have hpoint : xiMassCenteredArchPoint (x : ℂ) =
      xiMassArchVerticalEulerPoint x 0 := by
    unfold xiMassArchVerticalEulerPoint
    simp
  rw [hpoint]
  exact mul_le_mul hm harch (norm_nonneg _) (Real.exp_pos _).le

/-- Height-independent `L¹` majorant on the centered line. -/
def xiMassCenteredArchMajorant (σ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(σ * |x|)) *
    (xiMassArchVerticalGrowthConstant + |x| / 2)

theorem integrable_xiMassCenteredArchMajorant {σ : ℝ} (hσ : 0 < σ) :
    Integrable (xiMassCenteredArchMajorant σ) := by
  have hC : 0 ≤ xiMassArchVerticalGrowthConstant :=
    xiMassArchVerticalGrowthConstant_nonneg
  have hmajor : Integrable (fun x : ℝ =>
      xiMassArchVerticalGrowthConstant * Real.exp (-(σ * |x|)) +
        (1 / 2 : ℝ) * (|x| * Real.exp (-(σ * |x|)))) :=
    ((integrable_exp_neg_mul_abs hσ).const_mul xiMassArchVerticalGrowthConstant).add
      ((integrable_abs_mul_exp_neg_mul_abs hσ).const_mul (1 / 2 : ℝ))
  apply hmajor.congr
  filter_upwards with x
  unfold xiMassCenteredArchMajorant
  ring

theorem integrable_xiMassCenteredArchIntegrand
    {a σ u : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    Integrable (xiMassCenteredArchIntegrand a (σ + u * I)) := by
  let S : Set ℝ := {x : ℝ | 2 ≤ |x|}
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have htail : IntegrableOn (xiMassCenteredArchIntegrand a (σ + u * I)) S := by
    refine (integrable_xiMassCenteredArchMajorant hσ).integrableOn.mono'
      (continuous_xiMassCenteredArchIntegrand ha (σ + u * I)).aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict hS] with x hx
    exact norm_xiMassCenteredArchIntegrand_le ha hσ hx
  have hcompact : IntegrableOn (xiMassCenteredArchIntegrand a (σ + u * I))
      (Icc (-2) 2) :=
    (continuous_xiMassCenteredArchIntegrand ha (σ + u * I)).integrableOn_Icc
  have hcover : Icc (-2 : ℝ) 2 ∪ S = univ := by
    ext x
    simp only [mem_union, mem_Icc, mem_univ, iff_true, S, mem_setOf_eq]
    by_cases h : |x| ≤ 2
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr (by linarith)
  rw [← integrableOn_univ, ← hcover]
  exact hcompact.union htail

/-- On the real axis the principal mass frequency is the positive real square root. -/
theorem xiMassAnalyticSqrt_ofReal_eq {a x : ℝ} (ha : 0 < a) :
    xiMassAnalyticSqrt a (x : ℂ) = ((Real.sqrt (x ^ 2 + a ^ 2) : ℝ) : ℂ) := by
  let w : ℂ := xiMassAnalyticSqrt a (x : ℂ)
  let r : ℝ := Real.sqrt (x ^ 2 + a ^ 2)
  have hbase : 0 < x ^ 2 + a ^ 2 := by nlinarith [sq_pos_of_pos ha]
  have hr : 0 < r := Real.sqrt_pos.2 hbase
  have hmem : (x : ℂ) ∈ xiMassStrip a := by
    change |((x : ℂ)).im| < a
    simpa using ha
  have hw : 0 < w.re := xiMassAnalyticSqrt_re_pos ha hmem
  have hsq : w ^ 2 = (r : ℂ) ^ 2 := by
    rw [show w ^ 2 = xiMassAnalyticArg a (x : ℂ) by
      exact xiMassAnalyticSqrt_sq a (x : ℂ)]
    have hr2 : r ^ 2 = x ^ 2 + a ^ 2 := Real.sq_sqrt hbase.le
    unfold xiMassAnalyticArg
    push_cast
    exact_mod_cast hr2.symm
  have hprod : (w - (r : ℂ)) * (w + (r : ℂ)) = 0 := by
    calc
      _ = w ^ 2 - (r : ℂ) ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith

theorem norm_xiMassAnalyticTest_ofReal_eq
    {a σ u x : ℝ} (ha : 0 < a) :
    ‖xiMassAnalyticTest a (σ + u * I) (x : ℂ)‖ =
      Real.exp (-σ * Real.sqrt (x ^ 2 + a ^ 2)) := by
  rw [xiMassAnalyticTest, xiMassAnalyticSqrt_ofReal_eq ha, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem norm_xiMassCenteredArchIntegrand_verticalTime_eq
    {a σ u x : ℝ} (ha : 0 < a) :
    ‖xiMassCenteredArchIntegrand a (σ + u * I) x‖ =
      ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖ := by
  unfold xiMassCenteredArchIntegrand
  rw [norm_mul, norm_mul]
  have hm : ‖xiMassAnalyticTest a (σ + u * I) (x : ℂ)‖ =
      ‖xiMassAnalyticTest a (σ : ℂ) (x : ℂ)‖ := by
    rw [norm_xiMassAnalyticTest_ofReal_eq ha]
    have hzero := norm_xiMassAnalyticTest_ofReal_eq
      (a := a) (σ := σ) (u := 0) (x := x) ha
    simpa using hzero.symm
  rw [hm]

/-- Centered-line integral has one height-independent `L¹` bound. -/
theorem norm_integral_xiMassCenteredArchIntegrand_le_baseNorm
    {a σ u : ℝ} (ha : 0 < a) (_hσ : 0 < σ) :
    ‖∫ x : ℝ, xiMassCenteredArchIntegrand a (σ + u * I) x‖ ≤
      ∫ x : ℝ, ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖ := by
  calc
    ‖∫ x : ℝ, xiMassCenteredArchIntegrand a (σ + u * I) x‖ ≤
        ∫ x : ℝ, ‖xiMassCenteredArchIntegrand a (σ + u * I) x‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact norm_xiMassCenteredArchIntegrand_verticalTime_eq ha

/-- Positive real mass frequency of the unique crossed archimedean zero. -/
def xiMassArchPoleFrequency (a : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 - 1 / 4)

theorem xiMassArchPoleFrequency_pos {a : ℝ} (hhalf : 1 / 2 < a) :
    0 < xiMassArchPoleFrequency a := by
  unfold xiMassArchPoleFrequency
  apply Real.sqrt_pos.2
  nlinarith [sq_pos_of_pos (show 0 < a by linarith)]

/-- The crossed mass root is real; hence its time oscillation has unit modulus. -/
theorem xiMassAnalyticSqrt_archPole_eq {a : ℝ} (hhalf : 1 / 2 < a) :
    xiMassAnalyticSqrt a xiMassArchPole = (xiMassArchPoleFrequency a : ℂ) := by
  let w : ℂ := xiMassAnalyticSqrt a xiMassArchPole
  let r : ℝ := xiMassArchPoleFrequency a
  have ha : 0 < a := lt_trans (by norm_num) hhalf
  have hr : 0 < r := xiMassArchPoleFrequency_pos hhalf
  have hmem : xiMassArchPole ∈ xiMassStrip a := by
    change |xiMassArchPole.im| < a
    norm_num [xiMassArchPole, Complex.div_im, Complex.normSq]
    exact hhalf
  have hw : 0 < w.re := xiMassAnalyticSqrt_re_pos ha hmem
  have hr2 : r ^ 2 = a ^ 2 - 1 / 4 := by
    unfold r xiMassArchPoleFrequency
    exact Real.sq_sqrt (by nlinarith [sq_pos_of_pos ha])
  have hp2 : xiMassArchPole ^ 2 = (-1 / 4 : ℂ) := by
    unfold xiMassArchPole
    rw [div_pow, neg_sq, Complex.I_sq]
    norm_num
  have harg : xiMassAnalyticArg a xiMassArchPole = ((a ^ 2 - 1 / 4 : ℝ) : ℂ) := by
    rw [xiMassAnalyticArg, hp2]
    push_cast
    ring
  have hsq : w ^ 2 = (r : ℂ) ^ 2 := by
    rw [show w ^ 2 = xiMassAnalyticArg a xiMassArchPole by
      exact xiMassAnalyticSqrt_sq a xiMassArchPole, harg]
    exact_mod_cast hr2.symm
  have hprod : (w - (r : ℂ)) * (w + (r : ℂ)) = 0 := by
    calc
      _ = w ^ 2 - (r : ℂ) ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith

theorem norm_xiMassAnalyticTest_archPole_eq
    {a σ u : ℝ} (hhalf : 1 / 2 < a) :
    ‖xiMassAnalyticTest a (σ + u * I) xiMassArchPole‖ =
      Real.exp (-σ * xiMassArchPoleFrequency a) := by
  rw [xiMassAnalyticTest, xiMassAnalyticSqrt_archPole_eq hhalf, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem tendsto_integral_xiMassBottomArchIntegrand_atTop
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun R : ℝ => ∫ x in -R..R, xiMassBottomArchIntegrand a c τ x)
      atTop (𝓝 (∫ x : ℝ, xiMassBottomArchIntegrand a c τ x)) := by
  exact intervalIntegral_tendsto_integral
    (integrable_xiMassBottomArchIntegrand hhalf hca hτ)
    (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id

theorem tendsto_integral_xiMassCenteredArchIntegrand_atTop
    {a σ u : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    Tendsto (fun R : ℝ => ∫ x in -R..R,
      xiMassCenteredArchIntegrand a (σ + u * I) x)
      atTop (𝓝 (∫ x : ℝ, xiMassCenteredArchIntegrand a (σ + u * I) x)) := by
  exact intervalIntegral_tendsto_integral
    (integrable_xiMassCenteredArchIntegrand ha hσ)
    (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id

theorem xiMassCenteredArchPoint_bottom_eq (c x : ℝ) :
    xiMassCenteredArchPoint ((x : ℂ) - c * I) = xiMassBottomEulerPoint c x := by
  unfold xiMassCenteredArchPoint xiMassBottomEulerPoint
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem xiMassArchContourIntegrand_bottom_eq (a c : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassAnalyticTest a τ ((x : ℂ) - c * I) *
        logDeriv archFactor (xiMassCenteredArchPoint ((x : ℂ) - c * I)) =
      xiMassBottomArchIntegrand a c τ x := by
  rw [xiMassBottomArchIntegrand, xiMassBottomTest,
    xiMassCenteredArchPoint_bottom_eq]

theorem xiMassArchContourIntegrand_bottom_add_neg_eq
    (a c : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassAnalyticTest a τ ((x : ℂ) + -(c * I)) *
        logDeriv archFactor (xiMassCenteredArchPoint ((x : ℂ) + -(c * I))) =
      xiMassBottomArchIntegrand a c τ x := by
  simpa [sub_eq_add_neg] using xiMassArchContourIntegrand_bottom_eq a c τ x

/-- Exact infinite contour shift: bottom Gamma source equals centered source plus crossed residue. -/
theorem integral_xiMassBottomArch_eq_centered_add_residue
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassBottomArchIntegrand a c τ x) =
      (∫ x : ℝ, xiMassCenteredArchIntegrand a τ x) +
        2 * Real.pi * xiMassAnalyticTest a τ xiMassArchPole := by
  let F : ℂ → ℂ := fun z => xiMassAnalyticTest a τ z *
    logDeriv archFactor (xiMassCenteredArchPoint z)
  have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  have hbottom := tendsto_integral_xiMassBottomArchIntegrand_atTop hhalf hca hτ
  have hcentered : Tendsto (fun R : ℝ => ∫ x in -R..R,
      xiMassCenteredArchIntegrand a τ x) atTop
      (𝓝 (∫ x : ℝ, xiMassCenteredArchIntegrand a τ x)) := by
    have hτform : τ = (τ.re : ℂ) + τ.im * I := by
      apply Complex.ext <;> simp
    rw [hτform]
    exact tendsto_integral_xiMassCenteredArchIntegrand_atTop ha hτ
  have hright := tendsto_integral_xiMassArchVerticalIntegrand_right_atTop
    hhalf hca hτ
  have hleft := tendsto_integral_xiMassArchVerticalIntegrand_left_atTop
    hhalf hca hτ
  have hlim := ((hbottom.sub hcentered).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hlim' : Tendsto (fun R : ℝ =>
      rectIntegral F (((-R : ℝ) : ℂ) - c * I) (R : ℂ)) atTop
      (𝓝 ((∫ x : ℝ, xiMassBottomArchIntegrand a c τ x) -
        (∫ x : ℝ, xiMassCenteredArchIntegrand a τ x))) := by
    simpa [rectIntegral, F, xiMassCenteredArchIntegrand,
      xiMassArchVerticalIntegrand, xiMassArchVerticalEulerPoint,
      xiMassArchContourIntegrand_bottom_add_neg_eq, smul_eq_mul,
      sub_eq_add_neg] using hlim
  have heventually : ∀ᶠ R : ℝ in atTop,
      rectIntegral F (((-R : ℝ) : ℂ) - c * I) (R : ℂ) =
        2 * Real.pi * xiMassAnalyticTest a τ xiMassArchPole := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact rectIntegral_xiMass_mul_archLogDeriv hhalf hca hR τ
  have hconst : Tendsto (fun _ : ℝ =>
      2 * Real.pi * xiMassAnalyticTest a τ xiMassArchPole) atTop
      (𝓝 (2 * Real.pi * xiMassAnalyticTest a τ xiMassArchPole)) :=
    tendsto_const_nhds
  have heventually' : ∀ᶠ R : ℝ in atTop,
      2 * Real.pi * xiMassAnalyticTest a τ xiMassArchPole =
        rectIntegral F (((-R : ℝ) : ℂ) - c * I) (R : ℂ) :=
    heventually.mono fun _ h => h.symm
  have htarget := tendsto_nhds_unique hlim' (hconst.congr' heventually')
  exact sub_eq_iff_eq_add'.mp htarget

/-- Explicit height-independent bound for the entire bottom archimedean channel. -/
def xiMassBottomArchUniformBound (a σ : ℝ) : ℝ :=
  (∫ x : ℝ, ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖) +
    2 * Real.pi * Real.exp (-σ * xiMassArchPoleFrequency a)

theorem xiMassBottomArchUniformBound_nonneg
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    0 ≤ xiMassBottomArchUniformBound a σ := by
  unfold xiMassBottomArchUniformBound
  have hint := integrable_xiMassCenteredArchIntegrand (a := a) (σ := σ) (u := 0) ha hσ
  have hnorm : 0 ≤ ∫ x : ℝ, ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖ := by
    apply MeasureTheory.integral_nonneg
    exact fun _ => norm_nonneg _
  positivity

/-- Archimedean bottom source is uniformly bounded on each positive complex-time vertical line. -/
theorem norm_integral_xiMassBottomArchIntegrand_le_uniform
    {a c σ u : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 0 < σ) :
    ‖∫ x : ℝ, xiMassBottomArchIntegrand a c (σ + u * I) x‖ ≤
      xiMassBottomArchUniformBound a σ := by
  have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  rw [integral_xiMassBottomArch_eq_centered_add_residue hhalf hca
    (show 0 < (σ + u * I : ℂ).re by simp [Complex.mul_re]; exact hσ)]
  calc
    ‖(∫ x : ℝ, xiMassCenteredArchIntegrand a (σ + u * I) x) +
        2 * Real.pi * xiMassAnalyticTest a (σ + u * I) xiMassArchPole‖ ≤
      ‖∫ x : ℝ, xiMassCenteredArchIntegrand a (σ + u * I) x‖ +
        ‖2 * Real.pi * xiMassAnalyticTest a (σ + u * I) xiMassArchPole‖ :=
      norm_add_le _ _
    _ ≤ (∫ x : ℝ, ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖) +
        2 * Real.pi * Real.exp (-σ * xiMassArchPoleFrequency a) := by
      apply add_le_add (norm_integral_xiMassCenteredArchIntegrand_le_baseNorm ha hσ)
      rw [norm_mul, norm_xiMassAnalyticTest_archPole_eq
        (show 1 / 2 < a by linarith)]
      simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    _ = xiMassBottomArchUniformBound a σ := by
      rfl

end

end RHTower
