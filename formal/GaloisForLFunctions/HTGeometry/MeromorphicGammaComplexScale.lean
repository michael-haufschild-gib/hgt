import GaloisForLFunctions.HTGeometry.DiscretePeriodGaugeClassification
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit
import GaloisForLFunctions.HTGeometry.OddPowerCanonicalProductGammaRay
import GaloisForLFunctions.HTGeometry.OnePowerCanonicalProductHypertranscendence

/-!
# Gamma at an arbitrary complex scale, and the odd-exponent open core

The corpus carries `Γ(z+b)` and `Γ(nz+a)` for a natural scale `n` as elements of the global
meromorphic differential field.  An arbitrary nonzero complex scale is obtained by transporting the
shift element along the scaling automorphism `z ↦ a z`, which is already available as
`complexScaleMeroEquiv`.

The point of the construction is the odd-exponent canonical product: the ray-product identity
`W_p(z^p) = ∏_{j<p} Γ(ω^j z + 1)⁻¹` places the remaining open core of the integer-exponent
dichotomy inside the meromorphic differential field, as the hypertranscendence over `ℂ(X)` of a
finite product of reciprocal Gamma elements at the `p` distinct scales `ω^j`.  The corpus's
superselection layer settles the common-scale and natural-scale cases; this file is the substrate on
which the root-of-unity scale case has to be decided.
-/

namespace HTGeometry

open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher Filter Set Topology

noncomputable section

open scoped UnivMeroFieldInstances

/-- The entire germ of `z ↦ Γ(a z + b)⁻¹`. -/
def reciprocalGammaScaleShiftAnalytic (a b : ℂ) : analyticSubring (Set.univ : Set ℂ) :=
  univAnalytic (fun z => reciprocalGammaEntire (a * z + b)) (by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact (contDiff_reciprocalGammaEntire.differentiable (by simp)).comp
      ((differentiable_const a).mul differentiable_id |>.add (differentiable_const b)))

@[simp] theorem univGermEval_reciprocalGammaScaleShiftAnalytic (a b z : ℂ) :
    univGermEval z
        ((reciprocalGammaScaleShiftAnalytic a b : analyticSubring Set.univ) :
          Germ (Filter.principal Set.univ) ℂ)
      = reciprocalGammaEntire (a * z + b) := rfl

/-- Scaling the coordinate carries the reciprocal-Gamma shift germ to the reciprocal-Gamma
scale-shift germ. -/
theorem complexScaleAnalyticEquiv_reciprocalGammaShiftAnalytic
    (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    complexScaleAnalyticEquiv a ha (reciprocalGammaShiftAnalytic b)
      = reciprocalGammaScaleShiftAnalytic a b := by
  apply Subtype.ext
  apply univGerm_ext
  intro z
  rw [univGermEval_complexScaleAnalyticEquiv]
  rfl

/-- **Gamma at an arbitrary nonzero complex scale**, as an element of the global meromorphic
differential field: the class of `z ↦ Γ(a z + b)`. -/
def gammaScaleShiftMero (a : ℂ) (ha : a ≠ 0) (b : ℂ) : meroField (Set.univ : Set ℂ) :=
  complexScaleMeroEquiv a ha (gammaShiftMero b)

theorem gammaScaleShiftMero_eq (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    gammaScaleShiftMero a ha b
      = (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
          (reciprocalGammaScaleShiftAnalytic a b))⁻¹ := by
  rw [gammaScaleShiftMero, gammaShiftMero, map_inv₀, complexScaleMeroEquiv_algebraMap,
    complexScaleAnalyticEquiv_reciprocalGammaShiftAnalytic]

theorem gammaScaleShiftMero_ne_zero (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    gammaScaleShiftMero a ha b ≠ 0 := by
  rw [gammaScaleShiftMero]
  exact (map_ne_zero_iff _ (complexScaleMeroEquiv a ha).injective).mpr
    (gammaShiftMero_ne_zero b)

/-- The reciprocal-Gamma ray product at the `p`-th roots of unity, as a meromorphic element. -/
def gammaRayProductMero (p : ℕ) (ω : ℂ) (hω : ω ≠ 0) : meroField (Set.univ : Set ℂ) :=
  ∏ j ∈ Finset.range p, (gammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω) 1)⁻¹

/-- The analytic ray product `z ↦ ∏_{j<p} Γ(ω^j z + 1)⁻¹` is entire. -/
theorem analyticOnNhd_gammaRayProduct (p : ℕ) (ω : ℂ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹) Set.univ := by
  intro z _
  refine Finset.analyticAt_fun_prod (Finset.range p) fun j _ => ?_
  have hd : Differentiable ℂ (fun z : ℂ => (Complex.Gamma (ω ^ j * z + 1))⁻¹) := by
    have h : Differentiable ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) :=
      Complex.differentiable_one_div_Gamma
    exact h.comp ((differentiable_const _).mul differentiable_id |>.add (differentiable_const 1))
  exact ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) z (Set.mem_univ z))

/-- The meromorphic realization of the analytic ray product is the meromorphic ray product. -/
theorem analyticMeroElement_gammaRayProduct (p : ℕ) {ω : ℂ} (hω : ω ≠ 0) :
    analyticMeroElement
        (fun z : ℂ => ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹)
        (analyticOnNhd_gammaRayProduct p ω)
      = gammaRayProductMero p ω hω := by
  have hfac : ∀ j : ℕ,
      (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
        (reciprocalGammaScaleShiftAnalytic (ω ^ j) 1))
        = (gammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω) 1)⁻¹ := by
    intro j
    rw [gammaScaleShiftMero_eq, inv_inv]
  have hprodGerm : ∀ (s : Finset ℕ) (F : ℕ → analyticSubring (Set.univ : Set ℂ)) (z : ℂ),
      univGermEval z ((∏ j ∈ s, F j : analyticSubring (Set.univ : Set ℂ)) :
        Germ (Filter.principal (Set.univ : Set ℂ)) ℂ)
        = ∏ j ∈ s, univGermEval z ((F j : analyticSubring (Set.univ : Set ℂ)) :
            Germ (Filter.principal (Set.univ : Set ℂ)) ℂ) := by
    classical
    intro s F z
    induction s using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih]
        exact univGermEval_analyticSubring_mul z _ _
  have hel : analyticFunctionElement
      (fun z : ℂ => ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹)
      (analyticOnNhd_gammaRayProduct p ω)
      = ∏ j ∈ Finset.range p, reciprocalGammaScaleShiftAnalytic (ω ^ j) 1 := by
    apply Subtype.ext
    apply univGerm_ext
    intro z
    rw [hprodGerm]
    change (fun z : ℂ => ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹) z
      = ∏ j ∈ Finset.range p, reciprocalGammaEntire (ω ^ j * z + 1)
    exact Finset.prod_congr rfl fun j _ => rfl
  rw [gammaRayProductMero, Finset.prod_congr rfl fun j _ => (hfac j).symm,
    ← map_prod, analyticMeroElement, hel]

/-- **The odd-exponent open core, in the meromorphic differential field.**  For odd `p ≥ 3` the
canonical product `W_p` with zeros `-n^p` is hypertranscendental exactly when the reciprocal-Gamma
ray product at the `p`-th roots of unity is hypertranscendental over `ℂ(X)`.

This is the last gate of the integer-exponent dichotomy.  The corpus settles the analogous statement
for a common scale and for natural scales; here the `p` scales are the `p`-th roots of unity, whose
pole rays are pairwise distinct precisely because `p` is odd. -/
theorem hypertranscendental_powerCanonicalProduct_odd_iff_mero {p : ℕ} (hp : 1 < p) (hodd : Odd p)
    {ω : ℂ} (hω : IsPrimitiveRoot ω p) :
    Hypertranscendental (powerCanonicalProduct (p : ℝ))
      ↔ HypertranscendentalOver (RatFunc ℂ)
          (gammaRayProductMero p ω (hω.ne_zero (by omega))) := by
  have hωne : ω ≠ 0 := hω.ne_zero (by omega)
  have hbridge := analyticMeroElement_gammaRayProduct p hωne
  rw [hypertranscendental_powerCanonicalProduct_odd_iff hp hodd hω]
  constructor
  · intro hHT hmero
    refine hHT (differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement
      (analyticOnNhd_gammaRayProduct p ω) ?_)
    rw [hbridge]
    exact hmero
  · intro hHT hDA
    refine hHT ?_
    rw [← hbridge]
    exact differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
      (analyticOnNhd_gammaRayProduct p ω) hDA

end

end HTGeometry

