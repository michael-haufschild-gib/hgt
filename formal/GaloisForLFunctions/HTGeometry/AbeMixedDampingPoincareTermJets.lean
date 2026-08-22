import GaloisForLFunctions.HTGeometry.AbeDampedPoincareTermJetExpansion
import GaloisForLFunctions.HTGeometry.MultivariateJetCompositionLaw

/-!
# All mixed jets of literal damped Poincaré summands

The directional formula for Abe's multiplier extends to every ordered coordinate word.  Therefore
each actual mixed Poincaré-summand jet is a translated exponential multiplier times a source factor
which is a finite polynomial in the damping time.  No summability assertion is made here; this is
the exact termwise expansion whose explicit coefficient sources must later be normally summed.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The finite source factor left after an ordered mixed-coordinate derivative of a damped seed.
The last coordinate is differentiated first, matching `wordPartialDerivEntire`. -/
def abeExponentialDampingMixedJetFactor {d : ℕ} : {n : ℕ} →
    (Fin n → Fin d) → ℂ → MultivariateEntire d → MultivariateEntire d →
      MultivariateEntire d
  | 0, _, _, _, seed => seed
  | n + 1, word, t, Θ, seed =>
      abeExponentialDampingMixedJetFactor (Fin.init word) t Θ
        ((t • partialDerivEntire (coordinateJetDirection (word (Fin.last n))) Θ) * seed +
          partialDerivEntire (coordinateJetDirection (word (Fin.last n))) seed)

/-- Every ordered mixed derivative of a damped seed is the multiplier times its exact recursive
mixed-jet factor. -/
theorem wordPartialDerivEntire_abeExponentialDampingMultiplier_mul_mixed {d : ℕ} :
    ∀ {n : ℕ} (word : Fin n → Fin d) (t : ℂ) (Θ seed : MultivariateEntire d),
      wordPartialDerivEntire word (abeExponentialDampingMultiplier t Θ * seed) =
        abeExponentialDampingMultiplier t Θ *
          abeExponentialDampingMixedJetFactor word t Θ seed
  | 0, word, t, Θ, seed => by
      simp [wordPartialDerivEntire, abeExponentialDampingMixedJetFactor]
  | n + 1, word, t, Θ, seed => by
      rw [wordPartialDerivEntire, partialDerivEntire_mul,
        partialDerivEntire_abeExponentialDampingMultiplier_eq]
      have hproduct :
          (abeExponentialDampingMultiplier t Θ *
              (t • partialDerivEntire (coordinateJetDirection (word (Fin.last n))) Θ)) * seed +
            abeExponentialDampingMultiplier t Θ *
              partialDerivEntire (coordinateJetDirection (word (Fin.last n))) seed =
            abeExponentialDampingMultiplier t Θ *
              ((t • partialDerivEntire (coordinateJetDirection (word (Fin.last n))) Θ) * seed +
                partialDerivEntire (coordinateJetDirection (word (Fin.last n))) seed) := by
        ext x
        change ((abeExponentialDampingMultiplier t Θ).1 x *
              (t * (partialDerivEntire (coordinateJetDirection (word (Fin.last n))) Θ).1 x)) *
              seed.1 x +
            (abeExponentialDampingMultiplier t Θ).1 x *
              (partialDerivEntire (coordinateJetDirection (word (Fin.last n))) seed).1 x =
          (abeExponentialDampingMultiplier t Θ).1 x *
            ((t * (partialDerivEntire (coordinateJetDirection (word (Fin.last n))) Θ).1 x) *
              seed.1 x +
            (partialDerivEntire (coordinateJetDirection (word (Fin.last n))) seed).1 x)
        ring
      rw [hproduct, wordPartialDerivEntire_abeExponentialDampingMultiplier_mul_mixed]
      rfl

/-- A constant entire-source family is a degree-zero damping polynomial. -/
theorem hasFiniteDampingPolynomial_const {d : ℕ} (f : MultivariateEntire d) :
    HasFiniteDampingPolynomial (fun _ : ℂ => f) := by
  refine ⟨Unit, inferInstance, fun _ => 0, fun _ => f, ?_⟩
  intro t
  simp

/-- The one-step mixed-jet recurrence preserves finite polynomial dependence on damping time. -/
theorem HasFiniteDampingPolynomial.partialDeriv_step {d : ℕ} (v : Fin d → ℂ)
    (A : MultivariateEntire d) (F : ℂ → MultivariateEntire d)
    (hF : HasFiniteDampingPolynomial F) :
    HasFiniteDampingPolynomial (fun t => (t • A) * F t +
      partialDerivEntire v (F t)) := by
  rcases hF with ⟨ι, hι, degree, coefficient, hpolynomial⟩
  letI : Fintype ι := hι
  refine ⟨Sum ι ι, inferInstance,
    Sum.elim (fun i => degree i + 1) degree,
    Sum.elim (fun i => A * coefficient i)
      (fun i => partialDerivEntire v (coefficient i)), ?_⟩
  intro t
  change (t • A) * F t + partialDerivEntire v (F t) = _
  rw [hpolynomial t, partialDerivEntire_fintypeSum_smul, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [multivariateEntire_mul_t_smul_sum]

/-- Applying an ordered mixed-jet factor to a polynomial source family preserves finite polynomial
dependence on damping time. -/
theorem hasFiniteDampingPolynomial_abeExponentialDampingMixedJetFactor_aux {d : ℕ} :
    ∀ {n : ℕ} (word : Fin n → Fin d) (Θ : MultivariateEntire d)
      (F : ℂ → MultivariateEntire d),
      HasFiniteDampingPolynomial F →
        HasFiniteDampingPolynomial (fun t =>
          abeExponentialDampingMixedJetFactor word t Θ (F t))
  | 0, word, Θ, F, hF => by
      simpa [abeExponentialDampingMixedJetFactor] using hF
  | n + 1, word, Θ, F, hF => by
      simpa [abeExponentialDampingMixedJetFactor] using
        hasFiniteDampingPolynomial_abeExponentialDampingMixedJetFactor_aux
          (Fin.init word) Θ
          (fun t => (t • partialDerivEntire
            (coordinateJetDirection (word (Fin.last n))) Θ) * F t +
              partialDerivEntire (coordinateJetDirection (word (Fin.last n))) (F t))
          (hF.partialDeriv_step (coordinateJetDirection (word (Fin.last n)))
            (partialDerivEntire (coordinateJetDirection (word (Fin.last n))) Θ))

/-- The mixed-jet source factor of a fixed damped seed is a finite polynomial in damping time. -/
theorem hasFiniteDampingPolynomial_abeExponentialDampingMixedJetFactor {d : ℕ}
    {n : ℕ} (word : Fin n → Fin d) (Θ seed : MultivariateEntire d) :
    HasFiniteDampingPolynomial (fun t =>
      abeExponentialDampingMixedJetFactor word t Θ seed) :=
  hasFiniteDampingPolynomial_abeExponentialDampingMixedJetFactor_aux word Θ
    (fun _ => seed) (hasFiniteDampingPolynomial_const seed)

/-- Every ordered mixed derivative of a literally damped Poincaré summand is the translated
multiplier times its exact mixed-jet source factor. -/
theorem wordPartialDerivEntire_poincareTermEntire_abeExponentialDampingSeed {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} {n : ℕ} (ψ : AutomorphicFactor d Γ)
    (word : Fin n → Fin d) (Θ seed : MultivariateEntire d) (t : ℂ) (γ : Γ) :
    wordPartialDerivEntire word
      (poincareTermEntire ψ (abeExponentialDampingMultiplier t Θ * seed) γ) =
      abeExponentialDampingMultiplier t (multivariateEntireTranslate Θ γ.1) *
        abeExponentialDampingMixedJetFactor word t (multivariateEntireTranslate Θ γ.1)
          (poincareTermEntire ψ seed γ) := by
  rw [poincareTermEntire_abeExponentialDampingSeed_eq]
  exact wordPartialDerivEntire_abeExponentialDampingMultiplier_mul_mixed word t
    (multivariateEntireTranslate Θ γ.1) (poincareTermEntire ψ seed γ)

/-- The actual multi-index jet of a literally damped Poincaré summand is the translated
exponential multiplier times an explicit finite polynomial source factor. -/
theorem multiIndexJetEvalCLM_poincareTermEntire_abeExponentialDampingSeed {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (x : Fin d → ℂ) (a : Fin d →₀ ℕ) (Θ seed : MultivariateEntire d)
    (t : ℂ) (γ : Γ) :
    multiIndexJetEvalCLM x a
      (poincareTermEntire ψ (abeExponentialDampingMultiplier t Θ * seed) γ) =
      (abeExponentialDampingMultiplier t (multivariateEntireTranslate Θ γ.1)).1 x *
        (abeExponentialDampingMixedJetFactor (multiIndexWord a) t
          (multivariateEntireTranslate Θ γ.1) (poincareTermEntire ψ seed γ)).1 x := by
  rw [multiIndexJetEvalCLM_apply, orderedPartialJetEvalCLM_eq_wordPartialDerivEntire,
    wordPartialDerivEntire_poincareTermEntire_abeExponentialDampingSeed]
  rfl

/-- The coefficient source factor in every fixed multi-index Poincaré-summand jet is a finite
polynomial in damping time. -/
theorem hasFiniteDampingPolynomial_poincareTermEntire_abeExponentialDampingSeed_multiIndexJet
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (a : Fin d →₀ ℕ) (Θ seed : MultivariateEntire d) (γ : Γ) :
    HasFiniteDampingPolynomial (fun t =>
      abeExponentialDampingMixedJetFactor (multiIndexWord a) t
        (multivariateEntireTranslate Θ γ.1) (poincareTermEntire ψ seed γ)) :=
  hasFiniteDampingPolynomial_abeExponentialDampingMixedJetFactor (multiIndexWord a)
    (multivariateEntireTranslate Θ γ.1) (poincareTermEntire ψ seed γ)

end

end GaloisForLFunctions.HTGeometry
