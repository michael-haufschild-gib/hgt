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
  push Not at hcon
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

/-- If `Q` has integer coefficients, every grouped weight `aevalWeight` is an integer: it is a
`ℤ`-combination (the polynomial coefficients) of products of descending factorials. -/
theorem aevalWeight_isInt (n N : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (ν : ℕ →₀ ℕ)
    (hQ : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ)) :
    ∃ w : ℤ, aevalWeight n N Q ν = (w : ℂ) := by
  classical
  rw [aevalWeight]
  refine Finset.sum_induction _ (fun c => ∃ z : ℤ, c = (z : ℂ)) ?_ ⟨0, by simp⟩ ?_
  · rintro a b ⟨za, ha⟩ ⟨zb, hb⟩
    exact ⟨za + zb, by rw [ha, hb]; push_cast; ring⟩
  · intro x _
    obtain ⟨zc, hzc⟩ := hQ x.1
    refine ⟨zc * ∏ t, ((x.2 t + flatOrder (fun j => x.1 j.succ) t).descFactorial
        (flatOrder (fun j => x.1 j.succ) t) : ℤ), ?_⟩
    rw [hzc, atomDescProd]
    push_cast
    ring

/-- A nonzero integer weight has modulus at least one — the load-bearing Mahler integrality payoff:
an integer-normalized coefficient identity has weights that are either zero (dropped) or `≥ 1`. -/
theorem aevalWeight_norm_ge_one (n N : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (ν : ℕ →₀ ℕ)
    (hQ : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hne : aevalWeight n N Q ν ≠ 0) :
    1 ≤ ‖aevalWeight n N Q ν‖ := by
  obtain ⟨w, hw⟩ := aevalWeight_isInt n N Q ν hQ
  rw [hw]
  have hw0 : w ≠ 0 := by rintro rfl; simp [hw] at hne
  rw [Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hw0

/-- **Weight-mass bound.**  The total grouped-weight mass is bounded by the polynomial-coefficient-
weighted Leibniz mass over all contributing pairs: `∑_ν ‖aevalWeight ν‖ ≤ ∑_x ‖coeff x.1 Q‖ ·
‖atomDescProd x‖`.  Since the pair count and each descending-factorial factor are polynomially
bounded in `N`, this gives `log(mass) = O(log N)` — the bound the superlacunary valuation gap must
beat. -/
theorem aevalWeight_mass_le (n N : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
      ≤ ∑ x ∈ sigmaIdx n N Q, ‖MvPolynomial.coeff x.1 Q‖ * ‖atomDescProd n x‖ := by
  classical
  have hfib : (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        ∑ x ∈ (sigmaIdx n N Q).filter (fun x => atomKeyOf n x = ν),
          ‖MvPolynomial.coeff x.1 Q‖ * ‖atomDescProd n x‖)
      = ∑ x ∈ sigmaIdx n N Q, ‖MvPolynomial.coeff x.1 Q‖ * ‖atomDescProd n x‖ :=
    Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx) _
  refine le_trans (Finset.sum_le_sum fun ν _ => ?_) hfib.le
  rw [aevalWeight]
  refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
  rw [norm_mul]

/-- **Integer-normalized magnitude survival criterion (Mahler payoff).**  When the differential
relation `Q` has integer coefficients, a minimal-valuation atom `ν₀` with nonzero weight and a gap
`G` merely exceeding the log of the total mass forces `coeff N ≠ 0`.  Integrality removes the
`‖aevalWeight ν₀‖⁻¹` factor: a nonzero integer weight is `≥ 1`, so the dominance condition is the
clean `mass < exp G`.  This is the exact Archimedean tropical bend of the log-superlacunary family:
no phase choice can cancel one atom that beats the whole remaining recurrence by a valuation gap
exceeding the log of its polynomially-bounded mass. -/
theorem aeval_coeff_ne_zero_of_int_dominant (n N : ℕ) (F : ℂ⟦X⟧) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {b : ℕ → ℝ} (hb : ∀ i, ‖coeff i F‖ = Real.exp (- b i))
    (hQ : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (ν₀ : ℕ →₀ ℕ) (hν₀ : ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hw₀ : aevalWeight n N Q ν₀ ≠ 0) {G : ℝ}
    (hgap : ∀ ν ∈ ((sigmaIdx n N Q).image (atomKeyOf n)).erase ν₀,
        ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤ ν.sum (fun i k => (k : ℝ) * b i))
    (hmass : (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) < Real.exp G) :
    (coeff N) (aeval (formalJets n F) Q) ≠ 0 := by
  refine aeval_coeff_ne_zero_of_dominant n N F Q hb ν₀ hν₀ hw₀ hgap ?_
  calc (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
      < Real.exp G := hmass
    _ = 1 * Real.exp G := (one_mul _).symm
    _ ≤ ‖aevalWeight n N Q ν₀‖ * Real.exp G := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg G)
        exact aevalWeight_norm_ge_one n N Q ν₀ hQ hw₀

/-- **Log-superlacunary hypertranscendence, reduced to its two imported inputs.**
A smooth `f` with Taylor magnitudes `‖coeff i (taylorPS f)‖ = exp(-b i)` is hypertranscendental
once:
* `hmahler` — the Mahler integer-normalization interface (Mahler 1971): any differential relation
  satisfied by `f` can be replaced by a nonzero one with integer coefficients;
* `hintdom` — the integer-dominance realization (the Archimedean tropical bend supplied by the
  superlacunar profile): for every nonzero integer-coefficient relation, some coefficient level
  carries a minimal-valuation atom whose weight dominates the total mass by its valuation gap.

Everything between these two interfaces — the atom regrouping, the integrality payoff
(`aevalWeight_norm_ge_one`), the domination (`aeval_coeff_ne_zero_of_int_dominant`), and the
reduction of hypertranscendence to jet survival — is discharged unconditionally by this file. -/
theorem hypertranscendental_of_mahler_and_int_dominance {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) {b : ℕ → ℝ}
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (- b i))
    (hmahler : ∀ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ), Q ≠ 0 →
        aeval (formalJets n (taylorPS f)) Q = 0 →
        ∃ (n' : ℕ) (Q' : MvPolynomial (Fin (n' + 2)) ℂ), Q' ≠ 0 ∧
          (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q' = (z : ℂ)) ∧
          aeval (formalJets n' (taylorPS f)) Q' = 0)
    (hintdom : ∀ (n' : ℕ) (Q' : MvPolynomial (Fin (n' + 2)) ℂ), Q' ≠ 0 →
        (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q' = (z : ℂ)) →
        ∃ (N : ℕ) (ν₀ : ℕ →₀ ℕ) (G : ℝ),
          ν₀ ∈ (sigmaIdx n' N Q').image (atomKeyOf n') ∧
          aevalWeight n' N Q' ν₀ ≠ 0 ∧
          (∀ ν ∈ ((sigmaIdx n' N Q').image (atomKeyOf n')).erase ν₀,
              ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤ ν.sum (fun i k => (k : ℝ) * b i)) ∧
          (∑ ν ∈ (sigmaIdx n' N Q').image (atomKeyOf n'), ‖aevalWeight n' N Q' ν‖) < Real.exp G) :
    Hypertranscendental f := by
  refine hypertranscendental_of_aeval_survives hf (fun n Q hQ => ?_)
  intro hrel
  obtain ⟨n', Q', hQ', hint, hrel'⟩ := hmahler n Q hQ hrel
  obtain ⟨N, ν₀, G, hν₀, hw₀, hgap, hmass⟩ := hintdom n' Q' hQ' hint
  have hne := aeval_coeff_ne_zero_of_int_dominant n' N (taylorPS f) Q' hb hint ν₀ hν₀ hw₀ hgap hmass
  rw [hrel', map_zero] at hne
  exact hne rfl

end GaloisForLFunctions
