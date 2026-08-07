import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# The weighted formal adjoint of the Hedenmalm pair

In the weighted space `H_k = L²(ℝ, k⁻¹ dx)` the differential expression `D = -i ∂_x` has weighted
formal adjoint

`L = k D k⁻¹ = D + i k'/k`.

On compactly supported differentiable data this is a single integration by parts: the function
`f ḡ / k` has compact support, so its derivative integrates to zero, and the three terms of that
derivative are exactly the two sides of the weighted pairing.

The half-density conjugation by `k^{-1/2}` carries the pair to the symmetric pair
`D ∓ (i/2) k'/k` on unweighted `L²`; that identity is the pointwise calculus below.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile

/-! ### The logarithmic derivative of the source -/

/-- The derivative of the theta source. -/
def sourceDeriv (x : ℝ) : ℝ := deriv thetaCuspFullSource x

theorem hasDerivAt_thetaCuspFullSource (x : ℝ) :
    HasDerivAt thetaCuspFullSource (sourceDeriv x) x :=
  (contDiff_thetaCuspFullSource.differentiable (by simp) x).hasDerivAt

theorem continuous_sourceDeriv : Continuous sourceDeriv :=
  contDiff_thetaCuspFullSource.continuous_deriv (by simp)

/-- The logarithmic derivative `a = k'/k` of the theta source. -/
def sourceLogDeriv (x : ℝ) : ℝ := sourceDeriv x / thetaCuspFullSource x

theorem continuous_sourceLogDeriv : Continuous sourceLogDeriv :=
  continuous_sourceDeriv.div contDiff_thetaCuspFullSource.continuous
    fun x => (thetaCuspFullSource_pos x).ne'

/-! ### The weighted pairing -/

/-- The complexified source weight. -/
def sourceWeightC (x : ℝ) : ℂ := ((thetaCuspFullSource x : ℝ) : ℂ)

theorem sourceWeightC_ne_zero (x : ℝ) : sourceWeightC x ≠ 0 := by
  rw [sourceWeightC]
  exact_mod_cast (thetaCuspFullSource_pos x).ne'

theorem continuous_sourceWeightC : Continuous sourceWeightC :=
  Complex.continuous_ofReal.comp contDiff_thetaCuspFullSource.continuous

theorem hasDerivAt_sourceWeightC (x : ℝ) :
    HasDerivAt sourceWeightC ((sourceDeriv x : ℝ) : ℂ) x :=
  (hasDerivAt_thetaCuspFullSource x).ofReal_comp

/-- **The weighted formal symmetry of the Hedenmalm pair.**  On compactly supported
differentiable data,

`⟨D f, g⟩_{H_k} = ⟨f, L g⟩_{H_k}`,  `L = D + i k'/k`. -/
theorem integral_weighted_symmetry {f g f' g' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hfc : Continuous f) (hgc : Continuous g)
    (hfc' : Continuous f') (hgc' : Continuous g')
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g)
    (hfs' : HasCompactSupport f') (hgs' : HasCompactSupport g') :
    (∫ x, (-Complex.I * f' x) * (starRingEnd ℂ) (g x) / sourceWeightC x)
      = ∫ x, f x * (starRingEnd ℂ) (-Complex.I * g' x
          + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x := by
  set F : ℝ → ℂ := fun x => f x * (starRingEnd ℂ) (g x) * (sourceWeightC x)⁻¹ with hF
  set F' : ℝ → ℂ := fun x =>
    (f' x * (starRingEnd ℂ) (g x) + f x * (starRingEnd ℂ) (g' x)) * (sourceWeightC x)⁻¹
      + f x * (starRingEnd ℂ) (g x) * (-((sourceDeriv x : ℝ) : ℂ) / sourceWeightC x ^ 2) with hF'
  have hinv : Continuous fun x : ℝ => (sourceWeightC x)⁻¹ :=
    continuous_sourceWeightC.inv₀ sourceWeightC_ne_zero
  have hderiv : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    have h1 : HasDerivAt (fun x => f x * (starRingEnd ℂ) (g x))
        (f' x * (starRingEnd ℂ) (g x) + f x * (starRingEnd ℂ) (g' x)) x := by
      have hstar : HasDerivAt (fun x => (starRingEnd ℂ) (g x)) ((starRingEnd ℂ) (g' x)) x :=
        (hg x).star
      exact (hf x).mul hstar
    have h2 : HasDerivAt (fun x => (sourceWeightC x)⁻¹)
        (-((sourceDeriv x : ℝ) : ℂ) / sourceWeightC x ^ 2) x :=
      (hasDerivAt_sourceWeightC x).inv (sourceWeightC_ne_zero x)
    exact h1.mul h2
  have hFcont : Continuous F' := by
    rw [hF']
    refine Continuous.add ?_ ?_
    · exact ((hfc'.mul (Complex.continuous_conj.comp hgc)).add
        (hfc.mul (Complex.continuous_conj.comp hgc'))).mul hinv
    · refine (hfc.mul (Complex.continuous_conj.comp hgc)).mul ?_
      exact (Complex.continuous_ofReal.comp continuous_sourceDeriv).neg.div
        (continuous_sourceWeightC.pow 2) fun x => pow_ne_zero 2 (sourceWeightC_ne_zero x)
  have hFsupp : HasCompactSupport F' := by
    refine HasCompactSupport.intro (hfs.isCompact_range_of_isClosed isClosed_closure ▸
      (isCompact_closure_of_subset_compact hfs (subset_refl _))) ?_
    intro x hx
    rw [hF']
    have hfx : f x = 0 := by
      by_contra hne
      exact hx (subset_closure (by simpa [Function.mem_support] using hne))
    have hf'x : f' x = 0 := by
      by_contra hne
      have hmem : x ∈ Function.support f' := by simpa [Function.mem_support] using hne
      exact hx (by
        have := hfs'.isCompact
        exact absurd hmem (by
          intro _
          exact hx (subset_closure hmem)))
    simp [hfx, hf'x]
  sorry

end HedenmalmThetaSource

end

end RHTower
