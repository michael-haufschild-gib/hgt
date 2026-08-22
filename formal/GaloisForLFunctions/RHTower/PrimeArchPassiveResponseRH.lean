import GaloisForLFunctions.HTGeometry.FiniteKMSFluctuationDissipation
import GaloisForLFunctions.HTGeometry.AnalyticCofiniteTransfer
import GaloisForLFunctions.HTGeometry.LogDerivNoZero
import GaloisForLFunctions.RHTower.XiWeilOneCauchyGate
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# Passive-response value producers for the prime--archimedean anti-Herglotz gate

This file directly connects finite Kubo/Lehmann response values to the existing source-side
anti-Herglotz criterion for RH.  A fixed nonnegative spectral representation supplies the sign
immediately.  More physically, a pointwise thermodynamic limit of canonical finite KMS/Wightman
responses retains the closed upper-half-plane sign even while its finite Hilbert-space dimensions
grow.

The remaining input is a source-value comparison or convergence theorem, not a positivity or
passivity hypothesis.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- A source-value representation by one finite passive response supplies the anti-Herglotz gate. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_finitePassiveResponse
    {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ)
    (hintensity : ∀ a, 0 ≤ intensity a)
    (hvalue : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        continuedPrimeArchSourceRelativeTrace z =
          HTGeometry.finitePassiveResponse intensity frequency z) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzpos hzhalf hzeta
  rw [hvalue z hzpos hzhalf hzeta]
  exact HTGeometry.finitePassiveResponse_im_nonpos
    intensity frequency hintensity hzpos

/-- The same passive source representation directly supplies the one-Cauchy divided-difference
gate used by the Weil and Hedenmalm consumers. -/
theorem continuedPrimeArchUpperCauchyDiagonalNonnegative_of_finitePassiveResponse
    {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ)
    (hintensity : ∀ a, 0 ≤ intensity a)
    (hvalue : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        continuedPrimeArchSourceRelativeTrace z =
          HTGeometry.finitePassiveResponse intensity frequency z) :
    ContinuedPrimeArchUpperCauchyDiagonalNonnegative :=
  continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz.mpr
    (continuedPrimeArchUpperAntiHerglotz_of_finitePassiveResponse
      intensity frequency hintensity hvalue)

/-- A finite passive-response realization of the continued source proves RH. -/
theorem riemannHypothesis_of_finitePassiveResponse
    {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ)
    (hintensity : ∀ a, 0 ≤ intensity a)
    (hvalue : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        continuedPrimeArchSourceRelativeTrace z =
          HTGeometry.finitePassiveResponse intensity frequency z) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperAntiHerglotz_of_finitePassiveResponse
      intensity frequency hintensity hvalue)

/-- No fixed finite resolvent can represent the continued prime--archimedean source.

The finite real-frequency response is analytic off its finite frequency set.  Agreement near the
unconditionally regular point `I / 4` analytically continues the differential identity
`XiC' = R * XiC` across that complement.  The identity makes `XiC` zero-free there, contradicting
the infinite Xi divisor.  Thus finite systems are excluded independently of passivity; the
growing-dimension thermodynamic limits below remain the finite-system survivor. -/
theorem not_continuedPrimeArchSourceRelativeTrace_eq_finitePassiveResponse
    {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ) :
    ¬ (∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        continuedPrimeArchSourceRelativeTrace z =
          HTGeometry.finitePassiveResponse intensity frequency z) := by
  intro hvalue
  let S : Set ℂ := Set.range (fun a => (frequency a : ℂ))
  have hS : S.Finite := Set.finite_range _
  have hSopen : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  let R : ℂ → ℂ := fun z => ∑ a, (intensity a : ℂ) /
    (z - (frequency a : ℂ))
  have hR : AnalyticOnNhd ℂ R Sᶜ := by
    intro z hz
    dsimp [R]
    rw [show (fun w => ∑ a, (intensity a : ℂ) /
      (w - (frequency a : ℂ))) = ∑ a, fun w => (intensity a : ℂ) /
        (w - (frequency a : ℂ)) by
      funext w
      simp]
    apply Finset.analyticAt_sum Finset.univ
    intro a ha
    apply analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    apply sub_ne_zero.mpr
    intro h
    apply hz
    exact ⟨a, h.symm⟩
  let H : ℂ → ℂ := fun z => deriv XiC z - R z * XiC z
  have hH : AnalyticOnNhd ℂ H Sᶜ := by
    intro z hz
    exact (XiC_analytic z (Set.mem_univ z)).deriv.sub
      ((hR z hz).mul (XiC_analytic z (Set.mem_univ z)))
  let z₀ : ℂ := Complex.I / 4
  have hzeta₀ : riemannZeta (1 / 2 + z₀ * Complex.I) ≠ 0 := by
    have hcoord : (1 / 2 : ℂ) + z₀ * Complex.I = ((1 / 4 : ℝ) : ℂ) := by
      dsimp [z₀]
      apply Complex.ext <;> norm_num
    rw [hcoord]
    exact riemannZeta_real_strip_ne_zero (by norm_num) (by norm_num)
  have hs₀ne : (1 / 2 : ℂ) + z₀ * Complex.I ≠ 1 := by
    intro h
    have hcoord : (1 / 2 : ℂ) + z₀ * Complex.I = ((1 / 4 : ℝ) : ℂ) := by
      dsimp [z₀]
      apply Complex.ext <;> norm_num
    rw [hcoord] at h
    norm_num at h
  let s₀ : ℂ := (1 / 2 : ℂ) + z₀ * Complex.I
  have hzetacont : ContinuousAt
      (fun z : ℂ => riemannZeta (1 / 2 + z * Complex.I)) z₀ := by
    have hparam : ContinuousAt (fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I) z₀ := by
      fun_prop
    have houter : ContinuousAt riemannZeta s₀ := by
      exact (differentiableAt_riemannZeta hs₀ne).continuousAt
    simpa [s₀, Function.comp_def] using houter.comp_of_eq hparam (by rfl)
  have hzetanear : ∀ᶠ z in 𝓝 z₀,
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 :=
    hzetacont.eventually_ne hzeta₀
  have hposnear : ∀ᶠ z in 𝓝 z₀, 0 < z.im :=
    (isOpen_lt continuous_const Complex.continuous_im).eventually_mem (by
      dsimp [z₀]
      norm_num)
  have hhalfnear : ∀ᶠ z in 𝓝 z₀, z.im < 1 / 2 :=
    (isOpen_lt Complex.continuous_im continuous_const).eventually_mem (by
      dsimp [z₀]
      norm_num)
  have hHev : H =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hzetanear, hposnear, hhalfnear] with z hzeta hzpos hzhalf
    have hspos : 0 < (1 / 2 + z * Complex.I).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.div_re, Complex.one_re, Complex.one_im, zero_mul, mul_one]
      norm_num
      linarith
    have hslt : (1 / 2 + z * Complex.I).re < 1 := by
      simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.div_re, Complex.one_re, Complex.one_im, zero_mul, mul_one]
      norm_num
      linarith
    have hsne : (1 / 2 : ℂ) + z * Complex.I ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      rw [Complex.one_re] at hre
      exact (ne_of_lt hslt) hre
    have hXi : XiC z ≠ 0 :=
      XiC_ne_zero_of_continuedPrimeArch_domain hspos hsne hzeta
    have hsource : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z :=
      (continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hspos hsne hzeta).trans
        (logDeriv_XiC_eq_relativeResolventTrace hXi).symm
    have hvalueR : continuedPrimeArchSourceRelativeTrace z = R z := by
      simpa only [R, HTGeometry.finitePassiveResponse] using hvalue z hzpos hzhalf hzeta
    dsimp [H]
    apply sub_eq_zero.mpr
    rw [← hvalueR, hsource, logDeriv_apply]
    exact (div_mul_cancel₀ _ hXi).symm
  have hz₀S : z₀ ∈ Sᶜ := by
    rw [Set.mem_compl_iff]
    rintro ⟨a, ha⟩
    have him := congrArg Complex.im ha
    dsimp [z₀] at him
    norm_num at him
  have hHzero : Set.EqOn H 0 Sᶜ :=
    hH.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (GaloisForLFunctions.HTGeometry.isPreconnected_compl_finite hS) hz₀S hHev
  let w₀ : ℂ := -Complex.I
  have hw₀S : w₀ ∈ Sᶜ := by
    rw [Set.mem_compl_iff]
    rintro ⟨a, ha⟩
    have him := congrArg Complex.im ha
    dsimp [w₀] at him
    norm_num at him
  have hXi₀ : XiC w₀ ≠ 0 := by
    apply XiC_ne_zero_of_one_lt_centered_re
    dsimp [w₀]
    norm_num
  have hnozero : ∀ z ∈ Sᶜ, XiC z ≠ 0 := by
    apply GaloisForLFunctions.HTGeometry.ne_zero_of_deriv_eq_mul hSopen
      (GaloisForLFunctions.HTGeometry.isPreconnected_compl_finite hS)
      (XiC_analytic.mono (Set.subset_univ _)) hR
    · intro z hz
      have h := hHzero hz
      dsimp [H] at h
      exact sub_eq_zero.mp h
    · exact hw₀S
    · exact hXi₀
  letI : Infinite XiDivisorSupport :=
    Set.infinite_coe_iff.mpr xiDivisorSupport_infinite
  have hexists : ∃ ρ : XiDivisorSupport, xiSpectralPointSupport ρ ∉ S := by
    by_contra h
    push Not at h
    have hsub : Set.range xiSpectralPointSupport ⊆ S := by
      rintro z ⟨ρ, rfl⟩
      exact h ρ
    have hfin : (Set.range xiSpectralPointSupport).Finite := hS.subset hsub
    exact (Set.infinite_range_of_injective xiSpectralPointSupport_injective) hfin
  obtain ⟨ρ, hρ⟩ := hexists
  have hXiρ : XiC (xiSpectralPointSupport ρ) = 0 := by
    change xi (1 / 2 + xiSpectralPointSupport ρ * Complex.I) = 0
    have hcoord : (1 / 2 : ℂ) + xiSpectralPointSupport ρ * Complex.I = ρ := by
      dsimp [xiSpectralPointSupport]
      rw [mul_assoc]
      have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
        rw [neg_mul, Complex.I_mul_I]
        ring
      rw [hI, mul_one]
      ring
    rw [hcoord]
    exact xi_eq_zero_of_mem_divisor_support ρ
  exact (hnozero _ hρ) hXiρ

/-- Pointwise convergence of canonical finite KMS responses transfers passivity to the continued
prime--archimedean source.  The finite Hilbert-space dimension may grow with `N`. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_finiteKMSWightmanResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzpos hzhalf hzeta
  have hlim := hconv z hzpos hzhalf hzeta
  have himlim : Tendsto
      (fun N ↦ (HTGeometry.finiteTransitionPassiveResponse
        (HTGeometry.finiteKMSWightmanTransitionIntensity
          (β N) (energy N) (amplitude N)) (energy N) z).im)
      atTop (nhds (continuedPrimeArchSourceRelativeTrace z).im) :=
    (Complex.continuous_im.tendsto _).comp hlim
  exact isClosed_Iic.mem_of_tendsto himlim
    (Filter.Eventually.of_forall fun N ↦
      HTGeometry.finiteKMSWightmanTransitionPassiveResponse_im_nonpos
        (β N) (energy N) (amplitude N) hzpos)

/-- Pointwise convergence of energy-weighted KMS fluctuation--dissipation responses transfers the
same anti-Herglotz sign to the continued prime--archimedean source.  The FDT sign law discharges the
nonnegative-intensity hypothesis from `β N ≥ 0`. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_finiteKMSDissipativeResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hβ : ∀ N, 0 ≤ β N)
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSDissipativeTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzpos hzhalf hzeta
  have hlim := hconv z hzpos hzhalf hzeta
  have himlim : Tendsto
      (fun N ↦ (HTGeometry.finiteTransitionPassiveResponse
        (HTGeometry.finiteKMSDissipativeTransitionIntensity
          (β N) (energy N) (amplitude N)) (energy N) z).im)
      atTop (nhds (continuedPrimeArchSourceRelativeTrace z).im) :=
    (Complex.continuous_im.tendsto _).comp hlim
  exact isClosed_Iic.mem_of_tendsto himlim
    (Filter.Eventually.of_forall fun N ↦
      HTGeometry.finiteKMSDissipativeTransitionPassiveResponse_im_nonpos
        (β N) (energy N) (amplitude N) (hβ N) hzpos)

/-- The pointwise thermodynamic KMS limit also supplies the source one-Cauchy gate. -/
theorem continuedPrimeArchUpperCauchyDiagonalNonnegative_of_finiteKMSWightmanResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    ContinuedPrimeArchUpperCauchyDiagonalNonnegative :=
  continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz.mpr
    (continuedPrimeArchUpperAntiHerglotz_of_finiteKMSWightmanResponse_tendsto
      d β energy amplitude hconv)

/-- **Thermodynamic passive-response RH capstone.**  Canonical KMS positivity is structural; the
only remaining input is pointwise convergence of the source-defined responses to the continued
prime--archimedean trace on its natural upper-half-strip domain. -/
theorem riemannHypothesis_of_finiteKMSWightmanResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperAntiHerglotz_of_finiteKMSWightmanResponse_tendsto
      d β energy amplitude hconv)

/-- **Fluctuation--dissipation RH capstone.**  If source-defined finite KMS dissipative responses
converge pointwise to the continued prime--archimedean relative trace, their structural passivity
proves RH.  The convergence statement remains the source-facing obligation. -/
theorem riemannHypothesis_of_finiteKMSDissipativeResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hβ : ∀ N, 0 ≤ β N)
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSDissipativeTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperAntiHerglotz_of_finiteKMSDissipativeResponse_tendsto
      d β energy amplitude hβ hconv)

end

end RHTower
