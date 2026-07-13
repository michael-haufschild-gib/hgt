import GaloisForLFunctions.HTGeometry.MagnitudeSurvivalAssembly
import GaloisForLFunctions.HTGeometry.MagnitudeADEBridge
import GaloisForLFunctions.HTGeometry.GenericJetInjectivity
import GaloisForLFunctions.HTGeometry.TaylorFormalBridge

/-!
# Inhomogeneous magnitude survival

The magnitude survival criterion of `MagnitudeSurvivalAssembly` handles a differential polynomial
that is *homogeneous* of a fixed jet-arity `D`.  A general annihilating polynomial `Q` is
inhomogeneous: its monomials have different total jet-degrees.  This file lifts the whole survival
machine to `coeff N (aeval (formalJets n F) Q)` for an arbitrary `Q`, indexing the atoms by a
dependent-arity sigma of `(monomial, antidiagonal-split)` pairs and regrouping by the arity-free
key.  The upshot `aeval_coeff_ne_zero_of_dominant` is the general-arity analog of
`diffPoly_coeff_ne_zero_of_dominant_complex`: a single minimal-valuation atom with nonzero weight
and dominating gap forces the coefficient nonzero — the step every superlacunar magnitude witness
needs to defeat an *arbitrary* differential relation.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

/-- The dependent-arity index of contributing `(monomial, antidiagonal-split)` pairs for
`coeff N (aeval (formalJets n F) Q)`: monomials of `X`-degree `≤ N`, each split across its
jet-factors by an antidiagonal summing to the remaining degree `N - m 0`. -/
noncomputable def sigmaIdx (n N : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    Finset (Σ m : Fin (n + 2) →₀ ℕ, Fin (∑ j : Fin (n + 1), m j.succ) →₀ ℕ) :=
  (Q.support.filter (fun m => m 0 ≤ N)).sigma
    (fun m => (Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag (N - m 0))

/-- Arity-free atom key of a sigma element: the multiset of jet-derivative orders
`x.2 t + flatOrder (…) t`, collected order-blind into `ℕ →₀ ℕ`. -/
noncomputable def atomKeyOf (n : ℕ)
    (x : Σ m : Fin (n + 2) →₀ ℕ, Fin (∑ j : Fin (n + 1), m j.succ) →₀ ℕ) : ℕ →₀ ℕ :=
  key (fun t => x.2 t + flatOrder (fun j => x.1 j.succ) t)

/-- Descending-factorial weight of a sigma element (its Leibniz multiplicity). -/
noncomputable def atomDescProd (n : ℕ)
    (x : Σ m : Fin (n + 2) →₀ ℕ, Fin (∑ j : Fin (n + 1), m j.succ) →₀ ℕ) : ℂ :=
  ∏ t, (((x.2 t + flatOrder (fun j => x.1 j.succ) t).descFactorial
        (flatOrder (fun j => x.1 j.succ) t) : ℂ))

/-- `coeff N (aeval …)` flattened over the dependent sigma of contributing pairs. -/
theorem coeff_aeval_sigma_pair_sum (n N : ℕ) (F : ℂ⟦X⟧) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    (coeff N) (aeval (formalJets n F) Q)
      = ∑ x ∈ sigmaIdx n N Q,
          MvPolynomial.coeff x.1 Q *
            ∏ t, (coeff (x.2 t + flatOrder (fun j => x.1 j.succ) t)) F
              * (((x.2 t + flatOrder (fun j => x.1 j.succ) t).descFactorial
                  (flatOrder (fun j => x.1 j.succ) t) : ℂ)) := by
  rw [coeff_aeval_eq_filtered_pair_sum, sigmaIdx, Finset.sum_sigma]

/-- `coeff N (aeval …)` regrouped by the arity-free atom key into
`∑_ν (ν.prod coeff) · (weight ν)`. -/
theorem coeff_aeval_regrouped_complex (n N : ℕ) (F : ℂ⟦X⟧) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    (coeff N) (aeval (formalJets n F) Q)
      = ∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
          (ν.prod (fun i j => (coeff i F) ^ j))
            * (∑ x ∈ (sigmaIdx n N Q).filter (fun x => atomKeyOf n x = ν),
                MvPolynomial.coeff x.1 Q * atomDescProd n x) := by
  classical
  have hpair : (coeff N) (aeval (formalJets n F) Q)
      = ∑ x ∈ sigmaIdx n N Q,
          MvPolynomial.coeff x.1 Q
            * ((atomKeyOf n x).prod (fun i j => (coeff i F) ^ j)) * atomDescProd n x := by
    rw [coeff_aeval_sigma_pair_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib, atomKeyOf, atomDescProd,
      prod_eq_key_prod (fun t => x.2 t + flatOrder (fun j => x.1 j.succ) t) (fun i => coeff i F)]
    ring
  rw [hpair, ← Finset.sum_fiberwise_of_maps_to
    (g := atomKeyOf n) (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨_, hkey⟩ := Finset.mem_filter.mp hx
  rw [hkey]; ring

/-- Inhomogeneous weight of an atom key `ν` in `coeff N (aeval (formalJets n F) Q)`: the total
polynomial-coefficient-weighted Leibniz multiplicity of the pairs realizing `ν`. -/
noncomputable def aevalWeight (n N : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (ν : ℕ →₀ ℕ) : ℂ :=
  ∑ x ∈ (sigmaIdx n N Q).filter (fun x => atomKeyOf n x = ν),
    MvPolynomial.coeff x.1 Q * atomDescProd n x

/-- The regrouping, restated with the packaged weight `aevalWeight`. -/
theorem coeff_aeval_regrouped_weight (n N : ℕ) (F : ℂ⟦X⟧) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    (coeff N) (aeval (formalJets n F) Q)
      = ∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
          (ν.prod (fun i j => (coeff i F) ^ j)) * aevalWeight n N Q ν := by
  rw [coeff_aeval_regrouped_complex]; rfl

/-- **Inhomogeneous magnitude survival criterion.**  If in `coeff N (aeval (formalJets n F) Q)`
one atom key `ν₀` has nonzero weight and strictly minimal valuation `∑ᵢ ν i · b i` with a gap `G`
exceeding `log(mass / ‖weight ν₀‖)`, then that coefficient is nonzero — defeating the differential
relation `Q` at level `N`. -/
theorem aeval_coeff_ne_zero_of_dominant (n N : ℕ) (F : ℂ⟦X⟧) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {b : ℕ → ℝ} (hb : ∀ i, ‖coeff i F‖ = Real.exp (- b i))
    (ν₀ : ℕ →₀ ℕ) (hν₀ : ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hw₀ : aevalWeight n N Q ν₀ ≠ 0) {G : ℝ}
    (hgap : ∀ ν ∈ ((sigmaIdx n N Q).image (atomKeyOf n)).erase ν₀,
        ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤ ν.sum (fun i k => (k : ℝ) * b i))
    (hG : (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
        < ‖aevalWeight n N Q ν₀‖ * Real.exp G) :
    (coeff N) (aeval (formalJets n F) Q) ≠ 0 := by
  classical
  rw [coeff_aeval_regrouped_weight]
  rw [Finset.sum_congr rfl fun ν (_ : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n)) =>
      mul_comm (ν.prod (fun i j => (coeff i F) ^ j)) (aevalWeight n N Q ν)]
  exact weighted_sum_ne_zero_of_min_valuation_complex _
    (fun ν => ν.sum (fun i k => (k : ℝ) * b i)) _
    (fun ν => norm_aval (f := F) hb ν) _ hν₀ hw₀ hgap hG

/-- The Leibniz weight of any sigma element is nonzero: each descending-factorial factor
`(l t + k).descFactorial k` is positive. -/
theorem atomDescProd_ne_zero (n : ℕ)
    (x : Σ m : Fin (n + 2) →₀ ℕ, Fin (∑ j : Fin (n + 1), m j.succ) →₀ ℕ) :
    atomDescProd n x ≠ 0 := by
  rw [atomDescProd]
  refine Finset.prod_ne_zero_iff.mpr fun t _ => ?_
  rw [Ne, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt, not_lt]
  exact Nat.le_add_left _ _

/-- **Singleton-fiber weight nonvanishing.**  If exactly one contributing pair realizes the atom
key `ν₀`, and its monomial has nonzero polynomial coefficient, then `aevalWeight ν₀ ≠ 0`. -/
theorem aevalWeight_singleton_ne_zero (n N : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (ν₀ : ℕ →₀ ℕ)
    (x₀ : Σ m : Fin (n + 2) →₀ ℕ, Fin (∑ j : Fin (n + 1), m j.succ) →₀ ℕ)
    (hfiber : (sigmaIdx n N Q).filter (fun x => atomKeyOf n x = ν₀) = {x₀})
    (hc : MvPolynomial.coeff x₀.1 Q ≠ 0) :
    aevalWeight n N Q ν₀ ≠ 0 := by
  rw [aevalWeight, hfiber, Finset.sum_singleton]
  exact mul_ne_zero hc (atomDescProd_ne_zero n x₀)

/-- **A nonzero-weight atom always exists.**  For any nonzero differential polynomial `Q`, some
coefficient level `N` carries an appearing atom key `ν` with nonzero grouped weight.  This is the
contrapositive of the tree's generic jet-substitution injectivity: the grouped weights are the
series-independent universal coefficients, so if all of them vanished, `Q` would annihilate the
jets of *every* series, forcing `Q = 0`. -/
theorem exists_nonzero_aevalWeight {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ} (hQ : Q ≠ 0) :
    ∃ N : ℕ, ∃ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), aevalWeight n N Q ν ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hQ
  apply formalJets_substitution_injective
  intro G
  ext N
  rw [coeff_aeval_regrouped_weight, map_zero]
  refine Finset.sum_eq_zero fun ν hν => ?_
  rw [hcon N ν hν, mul_zero]

/-- **Magnitude-dominance ⟹ analytic hypertranscendence.**  The capstone of the inhomogeneous
magnitude engine: if for every nonzero differential relation `Q` some coefficient level exhibits a
minimal-valuation atom with nonzero weight dominating the remaining mass by its valuation gap, then
the smooth function `f` (with Taylor magnitudes `exp (-b i)`) is hypertranscendental.  Each concrete
magnitude witness reduces to supplying the per-`Q` dominance data `hdom`. -/
theorem hypertranscendental_of_magnitude_dominance {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) {b : ℕ → ℝ}
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (- b i))
    (hdom : ∀ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ), Q ≠ 0 →
      ∃ (N : ℕ) (ν₀ : ℕ →₀ ℕ) (G : ℝ),
        ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
        aevalWeight n N Q ν₀ ≠ 0 ∧
        (∀ ν ∈ ((sigmaIdx n N Q).image (atomKeyOf n)).erase ν₀,
            ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤ ν.sum (fun i k => (k : ℝ) * b i)) ∧
        (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
            < ‖aevalWeight n N Q ν₀‖ * Real.exp G) :
    Hypertranscendental f := by
  refine hypertranscendental_of_diffPoly_coeff_ne_zero hf (fun n Q hQ => ?_)
  obtain ⟨N, ν₀, G, hν₀, hw₀, hgap, hG⟩ := hdom n Q hQ
  exact ⟨N, aeval_coeff_ne_zero_of_dominant n N (taylorPS f) Q hb ν₀ hν₀ hw₀ hgap hG⟩

end GaloisForLFunctions
