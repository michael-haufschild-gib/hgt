import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SchurLendingOddHodgeIndexPastFirstPrime
import GaloisForLFunctions.SquareRootThreshold.WindowCertificatesAndThePrimeWeight
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheLocalGeometryOfAReflectionPair

/-!
# Positivity beyond isotropy does not localize

Every positivity theorem for Weil's form on a carrier closed under point convolution or under a
multiplicative correspondence ends in blindness, half-blindness or isotropy at off-line pairs
(`TheLocalGeometryOfAReflectionPair`, `coupled_isotropy`). This file shows that the restriction is
not positivity itself but localization.

* **Full fibres at finite aperture** (`exists_mem_realTestsAt_mellinAt_ne_zero`). For every
  aperture `a > 0` and any two points `s₁, s₂ ∈ ℂ` there is a real `C²` test supported in `[−a, a]`
  whose transform is nonzero at both. The probe `φ(u) cos(γu)` (`apertureProbe`) has
  `Re ĝ(s) = ∫ φ(u) e^{(σ − ½)u} cos²(γu) du > 0` at `s = σ + iγ`
  (`re_mellinAt_apertureProbe_pos`); two probes are combined.
* **Positivity beyond isotropy exists** (`positivity_beyond_isotropy_at_finite_aperture`). For
  `a ≤ 3/10` the carrier `realTestsAt a` is Weil-positive, and at every pair `{ρ, ρ*}` it contains a
  test seeing both points: it is neither blind nor half-blind, so its fibres are not forced to be
  isotropic.
* **It is source-blind.** The same positivity holds for the explicit formula of every prime weight
  `w : ℕ → ℝ` (the window `[−3/10, 3/10]` meets no prime), so it holds on the whole gauge orbit
  of the primes and for every fake source. It cannot distinguish `ζ` from anything.

So positivity beyond isotropy is available exactly where the carrier does not localize, and there
it carries no arithmetic. A forcing positivity must localize at off-line pairs, which multiplicative
symmetry does only hyperbolically; the open problem is a localizing carrier whose local symmetry at
off-line pairs is not hyperbolic.
-/

open Complex MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri

/-- A smooth bump on `[−a, a]`, equal to `1` on `[−a/2, a/2]`. -/
def apertureBump {a : ℝ} (ha : 0 < a) : ContDiffBump (0 : ℝ) :=
  ⟨a / 2, a, half_pos ha, half_lt_self ha⟩

/-- The **aperture probe** `φ(u) cos(γu)` at height `γ`. -/
def apertureProbe {a : ℝ} (ha : 0 < a) (γ : ℝ) : ℝ → ℝ :=
  fun u => apertureBump ha u * Real.cos (γ * u)

theorem contDiff_apertureProbe {a : ℝ} (ha : 0 < a) (γ : ℝ) :
    ContDiff ℝ 2 (apertureProbe ha γ) :=
  (apertureBump ha).contDiff.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

theorem tsupport_apertureProbe {a : ℝ} (ha : 0 < a) (γ : ℝ) :
    tsupport (apertureProbe ha γ) ⊆ Icc (-a) a := by
  refine (tsupport_mul_subset_left).trans ?_
  rw [(apertureBump ha).tsupport_eq, Real.closedBall_eq_Icc, zero_sub, zero_add]
  rfl

theorem hasCompactSupport_apertureProbe {a : ℝ} (ha : 0 < a) (γ : ℝ) :
    HasCompactSupport (apertureProbe ha γ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport _).trans (tsupport_apertureProbe ha γ))

/-- The probe as an element of `realTestsAt a`. -/
def apertureTest {a : ℝ} (ha : 0 < a) (γ : ℝ) : realTestsAt a :=
  ⟨⟨apertureProbe ha γ, contDiff_apertureProbe ha γ, hasCompactSupport_apertureProbe ha γ⟩,
    tsupport_apertureProbe ha γ⟩

/-- **The probe sees `s`**: `Re ĝ(s) = ∫ φ(u) e^{(σ − ½)u} cos²(γu) du > 0` for `γ = Im s`. -/
theorem re_mellinAt_apertureProbe_pos {a : ℝ} (ha : 0 < a) (s : ℂ) :
    0 < (mellinAt (apertureProbe ha s.im) s).re := by
  have hint := integrable_mellinAt (contDiff_apertureProbe ha s.im).continuous
    (hasCompactSupport_apertureProbe ha s.im) s
  rw [mellinAt, ← integral_re hint]
  have hre : ∀ u : ℝ, ((apertureProbe ha s.im u : ℂ) * Complex.exp ((s - 1 / 2) * u)).re =
      apertureBump ha u * Real.exp ((s.re - 1 / 2) * u) * Real.cos (s.im * u) ^ 2 := by
    intro u
    rw [Complex.re_ofReal_mul, Complex.exp_re]
    simp only [apertureProbe, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, mul_zero, sub_zero, zero_div]
    ring
  simp_rw [hre]
  have hcont : Continuous fun u : ℝ =>
      apertureBump ha u * Real.exp ((s.re - 1 / 2) * u) * Real.cos (s.im * u) ^ 2 :=
    ((apertureBump ha).continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2)
  have hcs : HasCompactSupport fun u : ℝ =>
      apertureBump ha u * Real.exp ((s.re - 1 / 2) * u) * Real.cos (s.im * u) ^ 2 :=
    ((apertureBump ha).hasCompactSupport.mul_right).mul_right
  refine hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun u => mul_nonneg (mul_nonneg (apertureBump ha).nonneg (Real.exp_pos _).le) (sq_nonneg _))
    (x := 0) ?_
  rw [(apertureBump ha).one_of_mem_closedBall (by simp [(half_pos ha).le])]
  simp

/-- The transform is additive on `realTestsAt a`. -/
theorem mellinAt_realTestsAt_add {a : ℝ} (f g : realTestsAt a) (s : ℂ) :
    mellinAt ((f + g : realTestsAt a) : ℝ → ℝ) s = mellinAt (f : ℝ → ℝ) s + mellinAt (g : ℝ → ℝ) s :=
  mellinAt_add f.1.2.1.continuous f.1.2.2 g.1.2.1.continuous g.1.2.2 s

/-- **Full fibres at finite aperture.** For any two points there is a test supported in `[−a, a]`
whose transform is nonzero at both. -/
theorem exists_mem_realTestsAt_mellinAt_ne_zero {a : ℝ} (ha : 0 < a) (s₁ s₂ : ℂ) :
    ∃ f : realTestsAt a, mellinAt (f : ℝ → ℝ) s₁ ≠ 0 ∧ mellinAt (f : ℝ → ℝ) s₂ ≠ 0 := by
  set f₁ := apertureTest ha s₁.im
  set f₂ := apertureTest ha s₂.im
  have h₁ : mellinAt (f₁ : ℝ → ℝ) s₁ ≠ 0 := fun h => by
    have := re_mellinAt_apertureProbe_pos ha s₁
    rw [show apertureProbe ha s₁.im = (f₁ : ℝ → ℝ) from rfl, h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have h₂ : mellinAt (f₂ : ℝ → ℝ) s₂ ≠ 0 := fun h => by
    have := re_mellinAt_apertureProbe_pos ha s₂
    rw [show apertureProbe ha s₂.im = (f₂ : ℝ → ℝ) from rfl, h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  by_cases h12 : mellinAt (f₁ : ℝ → ℝ) s₂ = 0
  · by_cases h21 : mellinAt (f₂ : ℝ → ℝ) s₁ = 0
    · refine ⟨f₁ + f₂, ?_, ?_⟩
      · rw [mellinAt_realTestsAt_add, h21, add_zero]; exact h₁
      · rw [mellinAt_realTestsAt_add, h12, zero_add]; exact h₂
    · exact ⟨f₂, h21, h₂⟩
  · exact ⟨f₁, h₁, h12⟩

/-- **Positivity beyond isotropy at finite aperture, and its source-blindness.** For
`0 < a ≤ 3/10`: Weil's form is coercive on `realTestsAt a`; at any two points (in particular at
`ρ` and `ρ* = 1 − ρ̄`) the carrier contains a test seeing both; and the same positivity holds for
the explicit formula of every prime weight `w`. -/
theorem positivity_beyond_isotropy_at_finite_aperture {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 3 / 10) :
    (∀ f : realTestsAt a,
      1 / 5000 * ∫ u, (f : ℝ → ℝ) u ^ 2 ≤ weilPair (f : ℝ → ℝ) (f : ℝ → ℝ)) ∧
    (∀ s₁ s₂ : ℂ, ∃ f : realTestsAt a, mellinAt (f : ℝ → ℝ) s₁ ≠ 0 ∧ mellinAt (f : ℝ → ℝ) s₂ ≠ 0) ∧
    (∀ (w : ℕ → ℝ) (f : realTestsAt a),
      1 / 5000 * ∫ u, ‖cx (f : ℝ → ℝ) u‖ ^ 2 ≤
        (RHTower.weilFullFunctional w (Zeta23.EF.weilTest (cx (f : ℝ → ℝ)) (cx (f : ℝ → ℝ)))).re) := by
  refine ⟨fun f => weilPair_ge_of_mem_realTestsAt ha f,
    fun s₁ s₂ => exists_mem_realTestsAt_mellinAt_ne_zero ha0 s₁ s₂, fun w f => ?_⟩
  refine SquareRootThreshold.re_weilFullFunctional_ge_of_aperture_le_threeTenths w
    (cx_contDiff f.1.2.1) ?_
  refine (closure_mono ?_).trans (f.2.trans (Icc_subset_Icc (by linarith) ha))
  intro u hu
  simp only [Function.mem_support, cx, ne_eq, Complex.ofReal_eq_zero] at hu ⊢
  exact hu

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
