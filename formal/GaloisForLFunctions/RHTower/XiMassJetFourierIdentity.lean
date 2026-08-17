import GaloisForLFunctions.RHTower.XiMassJetFourierDerivative
import GaloisForLFunctions.RHTower.XiMassJetTransport
import GaloisForLFunctions.RHTower.XiMassFourierBesselIdentity
import GaloisForLFunctions.RHTower.XiMassJetPolynomialBridge
import GaloisForLFunctions.RHTower.XiMassJetPrimeTail
import GaloisForLFunctions.RHTower.XiMassPolynomialPrimeAtomization

/-!
# The jet Fourier transform is the iterated jet of the mass profile

The Fourier side and the Bessel side satisfy the same dispersion recursion: multiplying the receiver
by `x² + 4a⁴` is applying `4a⁴ − ∂_h²` to its transform.  Both sides start at the mass profile, so
they agree at every jet order on the spacelike region — the identification that welds the transport
estimates of the jet hierarchy to the arithmetic side of the criterion.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

theorem ofReal_mem_xiMassHeightRegion {σ u h : ℝ} (hσ : 0 < σ) (hh : |u| < h) :
    ((h : ℝ) : ℂ) ∈ xiMassHeightRegion ((σ : ℂ) + (u : ℂ) * I) := by
  rw [mem_xiMassHeightRegion]
  have hre : ((((σ : ℂ) + (u : ℂ) * I) ^ 2 + ((h : ℝ) : ℂ) ^ 2)).re
      = σ ^ 2 - u ^ 2 + h ^ 2 := by
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  rw [hre]
  have habs : |u| ^ 2 = u ^ 2 := sq_abs u
  have h0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  nlinarith [hh, habs, h0, hσ]

/-- The iterated jet is holomorphic on the spacelike region. -/
theorem differentiableOn_xiMassJetIterate {a : ℝ} (ha : 0 < a) (τ : ℂ) (k : ℕ) :
    DifferentiableOn ℂ (xiMassJetIterate a τ k) (xiMassHeightRegion τ) := by
  have hexp : DifferentiableOn ℂ
      (fun ζ : ℂ => Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ζ)) (xiMassHeightRegion τ) :=
    (((differentiableOn_xiMassHeightRadius τ).const_mul (-(a : ℂ)))).cexp
  have hcarrier : DifferentiableOn ℂ
      (fun ζ : ℂ => Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ζ) * xiCausticIterate a τ k ζ)
      (xiMassHeightRegion τ) := hexp.mul (differentiableOn_xiCausticIterate ha τ k)
  exact hcarrier.congr (fun x hx => xiMassJetIterate_eqOn ha τ k hx)

theorem analyticOnNhd_xiMassJetIterate {a : ℝ} (ha : 0 < a) (τ : ℂ) (k : ℕ) :
    AnalyticOnNhd ℂ (xiMassJetIterate a τ k) (xiMassHeightRegion τ) :=
  (differentiableOn_xiMassJetIterate ha τ k).analyticOnNhd (isOpen_xiMassHeightRegion τ)

/-- **The Fourier side is the iterated jet.** -/
theorem xiMassJetFourierDeriv_eq_jetIterate {a σ u : ℝ} (ha : 0 < a) (hσ : 0 < σ) (k : ℕ) :
    ∀ h : ℝ, |u| < h →
      xiMassJetFourierDeriv a k 0 ((σ : ℂ) + (u : ℂ) * I) h
        = xiMassJetIterate a ((σ : ℂ) + (u : ℂ) * I) k (h : ℂ) := by
  set τ : ℂ := (σ : ℂ) + (u : ℂ) * I with hτdef
  have hτre : τ.re = σ := by rw [hτdef]; simp [Complex.mul_re]
  have hτim : τ.im = u := by rw [hτdef]; simp [Complex.mul_im]
  have hτpos : 0 < τ.re := by rw [hτre]; exact hσ
  have hopen : IsOpen {t : ℝ | |u| < t} := isOpen_lt continuous_const continuous_id
  induction k with
  | zero =>
      intro h hh
      have hh0 : 0 < h := lt_of_le_of_lt (abs_nonneg u) hh
      have hstrip : τ ∈ xiMassBesselStrip h := by
        refine ⟨hτpos, ?_⟩
        rw [hτim]
        exact hh
      have hfour : xiMassJetFourierDeriv a 0 0 τ h
          = stripFourier (xiMassAnalyticTest a τ) ((h : ℝ) : ℂ) := by
        rw [xiMassJetFourierDeriv, stripFourier]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [xiMassJetIntegrand, pow_zero, one_mul]
      rw [hfour, stripFourier_xiMass_eq_bessel ha hh0 hstrip]
      rfl
  | succ k ih =>
      intro h hh
      have hmemnb : {t : ℝ | |u| < t} ∈ nhds h := hopen.mem_nhds hh
      -- the jet is holomorphic at every real height of the region
      have hreg : ∀ t : ℝ, |u| < t → ((t : ℝ) : ℂ) ∈ xiMassHeightRegion τ := by
        intro t ht
        rw [hτdef]
        exact ofReal_mem_xiMassHeightRegion hσ ht
      have hd1 : ∀ t : ℝ, |u| < t →
          HasDerivAt (fun s : ℝ => xiMassJetIterate a τ k (s : ℂ))
            (deriv (xiMassJetIterate a τ k) ((t : ℝ) : ℂ)) t := by
        intro t ht
        have hdiff : DifferentiableAt ℂ (xiMassJetIterate a τ k) ((t : ℝ) : ℂ) :=
          (differentiableOn_xiMassJetIterate ha τ k).differentiableAt
            ((isOpen_xiMassHeightRegion τ).mem_nhds (hreg t ht))
        exact hdiff.hasDerivAt.comp_ofReal
      -- the first Fourier derivative is the complex derivative of the jet
      have hstep1 : ∀ t : ℝ, |u| < t →
          xiMassJetFourierDeriv a k 1 τ t = deriv (xiMassJetIterate a τ k) ((t : ℝ) : ℂ) := by
        intro t ht
        have hA := hasDerivAt_xiMassJetFourierDeriv ha k 0 hτpos t
        have hcongr : (fun s : ℝ => xiMassJetFourierDeriv a k 0 τ s)
            =ᶠ[nhds t] (fun s : ℝ => xiMassJetIterate a τ k (s : ℂ)) := by
          filter_upwards [hopen.mem_nhds ht] with s hs
          exact ih s hs
        have hB := hA.congr_of_eventuallyEq hcongr.symm
        exact hB.unique (hd1 t ht)
      -- the second Fourier derivative is the second complex derivative of the jet
      have hd2 : HasDerivAt (fun s : ℝ => deriv (xiMassJetIterate a τ k) ((s : ℝ) : ℂ))
          (deriv (deriv (xiMassJetIterate a τ k)) ((h : ℝ) : ℂ)) h := by
        have hana := analyticOnNhd_xiMassJetIterate ha τ k
        have hdiff : DifferentiableAt ℂ (deriv (xiMassJetIterate a τ k)) ((h : ℝ) : ℂ) :=
          (hana.deriv).differentiableOn.differentiableAt
            ((isOpen_xiMassHeightRegion τ).mem_nhds (hreg h hh))
        exact hdiff.hasDerivAt.comp_ofReal
      have hstep2 : xiMassJetFourierDeriv a k 2 τ h
          = deriv (deriv (xiMassJetIterate a τ k)) ((h : ℝ) : ℂ) := by
        have hA := hasDerivAt_xiMassJetFourierDeriv ha k 1 hτpos h
        have hcongr : (fun s : ℝ => xiMassJetFourierDeriv a k 1 τ s)
            =ᶠ[nhds h] (fun s : ℝ => deriv (xiMassJetIterate a τ k) ((s : ℝ) : ℂ)) := by
          filter_upwards [hmemnb] with s hs
          exact hstep1 s hs
        have hB := hA.congr_of_eventuallyEq hcongr.symm
        exact hB.unique hd2
      rw [xiMassJetFourierDeriv_succ ha k hτpos h, ih h hh, hstep2,
        xiMassJetIterate_succ]

/-! ## The receiver in explicit power form, and the atom identification -/

/-- The jet-modified test is the `2N`-th power of the dispersion polynomial times the mass test. -/
theorem xiMassJetAnalyticTest_eq_pow {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) (τ z : ℂ) :
    xiMassJetAnalyticTest a N τ z
      = (z ^ 2 + 4 * (a : ℂ) ^ 4) ^ (2 * N) * xiMassAnalyticTest a τ z := by
  rw [xiMassJetAnalyticTest_eq_poly ha N τ z, xiMassPolyAnalyticTest,
    evalRealPolynomial_xiMassJetPoly, ← pow_mul]
  have hcast : (z ^ 2 + ((4 * a ^ 4 : ℝ) : ℂ)) = z ^ 2 + 4 * (a : ℂ) ^ 4 := by
    push_cast
    ring
  rw [hcast]
  congr 2
  ring

/-- **The jet-modified strip Fourier transform is the iterated jet of the mass profile.** -/
theorem stripFourier_xiMassJetAnalyticTest_eq_jetIterate {a σ u : ℝ} (ha : 1 / 2 < a)
    (hσ : 0 < σ) (N : ℕ) {h : ℝ} (hh : |u| < h) :
    stripFourier (xiMassJetAnalyticTest a N ((σ : ℂ) + (u : ℂ) * I)) ((h : ℝ) : ℂ)
      = xiMassJetIterate a ((σ : ℂ) + (u : ℂ) * I) (2 * N) ((h : ℝ) : ℂ) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hfour : stripFourier (xiMassJetAnalyticTest a N ((σ : ℂ) + (u : ℂ) * I)) ((h : ℝ) : ℂ)
      = xiMassJetFourierDeriv a (2 * N) 0 ((σ : ℂ) + (u : ℂ) * I) h := by
    rw [stripFourier, xiMassJetFourierDeriv]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show xiMassJetAnalyticTest a N ((σ : ℂ) + (u : ℂ) * I) ((x : ℝ) : ℂ) *
        Complex.exp (-(I * ((h : ℝ) : ℂ) * ((x : ℝ) : ℂ)))
      = (-(I * ((x : ℝ) : ℂ))) ^ 0 * xiMassJetIntegrand a (2 * N) ((σ : ℂ) + (u : ℂ) * I) h x
    rw [xiMassJetAnalyticTest_eq_pow ha N _ ((x : ℝ) : ℂ)]
    simp only [xiMassJetIntegrand, pow_zero, one_mul]
  rw [hfour]
  exact xiMassJetFourierDeriv_eq_jetIterate ha0 hσ (2 * N) h hh

/-- **The filtered centred prime atom is the jet prime atom.** -/
theorem xiMassPolyCenteredPrimeAtom_eq_jetPrimeAtom {a σ u : ℝ} (ha : 1 / 2 < a) (hσ : 0 < σ)
    (N : ℕ) {p : ℕ} (hp : |u| < Real.log p) :
    xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a ((σ : ℂ) + (u : ℂ) * I) p
      = xiMassJetPrimeAtom a ((σ : ℂ) + (u : ℂ) * I) (2 * N) p := by
  have htest : xiMassPolyAnalyticTest (xiMassJetPoly a N) a ((σ : ℂ) + (u : ℂ) * I)
      = xiMassJetAnalyticTest a N ((σ : ℂ) + (u : ℂ) * I) := by
    funext z
    exact (xiMassJetAnalyticTest_eq_poly ha N _ z).symm
  rw [xiMassPolyCenteredPrimeAtom, xiMassJetPrimeAtom, htest,
    stripFourier_xiMassJetAnalyticTest_eq_jetIterate ha hσ N hp]

end

end RHTower
