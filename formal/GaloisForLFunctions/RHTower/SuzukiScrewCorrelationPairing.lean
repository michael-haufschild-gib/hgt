import GaloisForLFunctions.RHTower.SuzukiScrewDistributionalKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
# The two-variable screw pairing is the kernel against the cross-correlation

The restricted Weil form is a two-variable pairing `∫∫ K (x - y) f y h x`, while the screw function
enters through the one-variable difference coordinate.  The two are the same object: the shear
`x = u + y` is measure preserving, so

```text
∫∫ K (x - y) f y h x = ∫ K u * (∫ f y * h (u + y) dy) du.
```

The proof is two applications of Fubini separated by one translation of the inner variable.  Both
integrands are continuous on an explicit compact rectangle and vanish outside it, which is where the
hypothesis that the support difference stays in `(0, ∞)` is used — the kernel is unbounded at the
origin.

Combined with the atom-free integration-by-parts identity, this puts the whole chain
`-g'' → K → ∫∫ K(x-y) f y h x → ∫ K c_(f,h)` in one place, and gives the positive cross coupling
in the difference variable.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set MeasureTheory

/-- The cross-correlation `c_(f,h)(u) = ∫ f y * h (u + y) dy`. -/
def screwCrossCorr (f h : ℝ → ℝ) (u : ℝ) : ℝ := ∫ y : ℝ, f y * h (u + y)

/-- The one-variable form of the restricted Weil pairing: the regular kernel against the
cross-correlation. -/
def screwCorrelationForm (f h : ℝ → ℝ) : ℝ :=
  ∫ u : ℝ, screwRegularKernel u * screwCrossCorr f h u

/-- The two-variable integrand of the regular screw form. -/
def screwFormIntegrand (f h : ℝ → ℝ) (x y : ℝ) : ℝ := screwRegularKernel (x - y) * f y * h x

/-- The same integrand after the shear `x = u + y`. -/
def screwShearIntegrand (f h : ℝ → ℝ) (y u : ℝ) : ℝ := screwRegularKernel u * f y * h (u + y)

theorem screwRegularForm_eq_integral_uncurry (f h : ℝ → ℝ) :
    screwRegularForm f h = ∫ p : ℝ × ℝ, Function.uncurry (screwFormIntegrand f h) p := rfl

/-! ## Integrability of the two shear-related integrands -/

theorem integrable_uncurry_screwFormIntegrand {f h : ℝ → ℝ}
    (hfc : Continuous f) (hhc : Continuous h)
    (hfs : HasCompactSupport f) (hhs : HasCompactSupport h)
    (hsep : ∀ x ∈ tsupport h, ∀ y ∈ tsupport f, 0 < x - y) :
    Integrable (Function.uncurry (screwFormIntegrand f h)) (volume.prod volume) := by
  have hKh : IsCompact (tsupport h) := hhs
  have hKf : IsCompact (tsupport f) := hfs
  have hsupp : Function.support (Function.uncurry (screwFormIntegrand f h))
      ⊆ tsupport h ×ˢ tsupport f := by
    intro p hp
    have hne : screwRegularKernel (p.1 - p.2) * f p.2 * h p.1 ≠ 0 := hp
    have h1 : h p.1 ≠ 0 := by
      intro hz; rw [hz, mul_zero] at hne; exact hne rfl
    have h2 : f p.2 ≠ 0 := by
      intro hz; rw [hz, mul_zero, zero_mul] at hne; exact hne rfl
    exact Set.mem_prod.mpr ⟨subset_tsupport h h1, subset_tsupport f h2⟩
  have hcont : ContinuousOn (Function.uncurry (screwFormIntegrand f h))
      (tsupport h ×ˢ tsupport f) := by
    have hker : ContinuousOn (fun p : ℝ × ℝ => screwRegularKernel (p.1 - p.2))
        (tsupport h ×ˢ tsupport f) := by
      refine ContinuousOn.comp continuousOn_screwRegularKernel
        ((continuous_fst.sub continuous_snd).continuousOn) ?_
      intro p hp
      obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
      exact hsep p.1 hp1 p.2 hp2
    exact (hker.mul ((hfc.comp continuous_snd).continuousOn)).mul
      ((hhc.comp continuous_fst).continuousOn)
  rw [← Measure.volume_eq_prod]
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    (hcont.integrableOn_compact (hKh.prod hKf))

theorem integrable_uncurry_screwShearIntegrand {f h : ℝ → ℝ}
    (hfc : Continuous f) (hhc : Continuous h)
    (hfs : HasCompactSupport f) (hhs : HasCompactSupport h)
    (hsep : ∀ x ∈ tsupport h, ∀ y ∈ tsupport f, 0 < x - y) :
    Integrable (Function.uncurry (screwShearIntegrand f h)) (volume.prod volume) := by
  have hKh : IsCompact (tsupport h) := hhs
  have hKf : IsCompact (tsupport f) := hfs
  set D : Set ℝ := (fun p : ℝ × ℝ => p.1 - p.2) '' (tsupport h ×ˢ tsupport f) with hD
  have hDc : IsCompact D := (hKh.prod hKf).image (continuous_fst.sub continuous_snd)
  have hDpos : ∀ u ∈ D, 0 < u := by
    rintro u ⟨p, hp, rfl⟩
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    exact hsep p.1 hp1 p.2 hp2
  have hsupp : Function.support (Function.uncurry (screwShearIntegrand f h))
      ⊆ tsupport f ×ˢ D := by
    intro p hp
    have hne : screwRegularKernel p.2 * f p.1 * h (p.2 + p.1) ≠ 0 := hp
    have h1 : h (p.2 + p.1) ≠ 0 := by
      intro hz; rw [hz, mul_zero] at hne; exact hne rfl
    have h2 : f p.1 ≠ 0 := by
      intro hz; rw [hz, mul_zero, zero_mul] at hne; exact hne rfl
    refine Set.mem_prod.mpr ⟨subset_tsupport f h2, ?_⟩
    refine ⟨(p.2 + p.1, p.1),
      Set.mem_prod.mpr ⟨subset_tsupport h h1, subset_tsupport f h2⟩, ?_⟩
    simp
  have hcont : ContinuousOn (Function.uncurry (screwShearIntegrand f h))
      (tsupport f ×ˢ D) := by
    have hker : ContinuousOn (fun p : ℝ × ℝ => screwRegularKernel p.2) (tsupport f ×ˢ D) := by
      refine ContinuousOn.comp continuousOn_screwRegularKernel continuous_snd.continuousOn ?_
      intro p hp
      exact hDpos p.2 (Set.mem_prod.mp hp).2
    exact (hker.mul ((hfc.comp continuous_fst).continuousOn)).mul
      ((hhc.comp (continuous_snd.add continuous_fst)).continuousOn)
  rw [← Measure.volume_eq_prod]
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    (hcont.integrableOn_compact (hKf.prod hDc))

/-! ## The shear identity -/

/-- **The two-variable regular screw pairing equals the kernel paired with the
cross-correlation.** -/
theorem screwRegularForm_eq_screwCorrelationForm (f h : ℝ → ℝ)
    (hfc : Continuous f) (hhc : Continuous h)
    (hfs : HasCompactSupport f) (hhs : HasCompactSupport h)
    (hsep : ∀ x ∈ tsupport h, ∀ y ∈ tsupport f, 0 < x - y) :
    screwRegularForm f h = screwCorrelationForm f h := by
  have hFint := integrable_uncurry_screwFormIntegrand hfc hhc hfs hhs hsep
  have hGint := integrable_uncurry_screwShearIntegrand hfc hhc hfs hhs hsep
  calc screwRegularForm f h
      = ∫ p : ℝ × ℝ, Function.uncurry (screwFormIntegrand f h) p :=
        screwRegularForm_eq_integral_uncurry f h
    _ = ∫ x : ℝ, ∫ y : ℝ, screwFormIntegrand f h x y := by
        rw [Measure.volume_eq_prod ℝ ℝ]
        exact (integral_integral hFint).symm
    _ = ∫ y : ℝ, ∫ x : ℝ, screwFormIntegrand f h x y := integral_integral_swap hFint
    _ = ∫ y : ℝ, ∫ u : ℝ, screwShearIntegrand f h y u := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        calc ∫ x : ℝ, screwFormIntegrand f h x y
            = ∫ u : ℝ, screwFormIntegrand f h (u + y) y :=
              (integral_add_right_eq_self (fun x => screwFormIntegrand f h x y) y).symm
          _ = ∫ u : ℝ, screwShearIntegrand f h y u := by
              simp only [screwFormIntegrand, screwShearIntegrand, add_sub_cancel_right]
    _ = ∫ u : ℝ, ∫ y : ℝ, screwShearIntegrand f h y u := integral_integral_swap hGint
    _ = screwCorrelationForm f h := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show (∫ y : ℝ, screwShearIntegrand f h y u)
          = screwRegularKernel u * screwCrossCorr f h u
        have hpt : ∀ y : ℝ, screwShearIntegrand f h y u
            = screwRegularKernel u * (f y * h (u + y)) := by
          intro y
          simp only [screwShearIntegrand]
          ring
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
        rfl

/-! ## The positive cross coupling in the difference variable -/

/-- **Positive cross coupling read in the difference variable.**  For every aperture `a > t_*/2`
two disjointly supported nonnegative smooth bumps inside `(-a, a)` have strictly positive pairing
of the regular screw kernel against their cross-correlation. -/
theorem exists_disjoint_positive_screwCorrelationForm {a : ℝ} (ha : screwSignThreshold / 2 < a) :
    ∃ f h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ ContDiff ℝ (⊤ : ℕ∞) h ∧
      (∀ x, 0 ≤ f x) ∧ (∀ x, 0 ≤ h x) ∧
      Function.support f ⊆ Ioo (-a) a ∧ Function.support h ⊆ Ioo (-a) a ∧
      Disjoint (Function.support f) (Function.support h) ∧
      0 < screwCorrelationForm f h := by
  obtain ⟨f, h, hfd, hhd, hfnn, hhnn, _, _, hfsub, hhsub, hdisj, hfcs, hhcs, hsep, hpos⟩ :=
    exists_disjoint_positive_screwRegularForm ha
  have hsep' : ∀ x ∈ tsupport h, ∀ y ∈ tsupport f, 0 < x - y := fun x hx y hy =>
    lt_trans screwSignThreshold_pos (hsep x hx y hy).1
  refine ⟨f, h, hfd, hhd, hfnn, hhnn, hfsub, hhsub, hdisj, ?_⟩
  rw [← screwRegularForm_eq_screwCorrelationForm f h hfd.continuous hhd.continuous hfcs hhcs hsep']
  exact hpos

end GaloisForLFunctions.RHTower

end
