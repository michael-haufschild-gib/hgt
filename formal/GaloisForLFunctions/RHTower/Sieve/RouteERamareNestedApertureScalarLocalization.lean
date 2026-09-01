import GaloisForLFunctions.RHTower.Sieve.RouteERamareIncidenceConditionalNegative

/-!
# Route E: nested Ramaré aperture scalar localization

For nested incidence apertures, subtracting the two exact complement forms removes the complete
scalar mass already visible at the smaller aperture.  The difference is supported by only two
mechanisms: polarization against integers newly activated by the larger aperture, and variation
of normalized incidence-block energy.

The arithmetic specialization is source-faithful: it uses the literal Möbius phase and the actual
Ramaré prime off-diagonal.  Its integrated form is the inter-modulus cancellation identity needed
before Route E's moving Gallagher estimates.  Thus no artificial centering, coefficient change, or
absolute-value estimate is introduced.
-/

namespace RHTower.Sieve

open Finset

/--
Exact scalar localization for two nested finite incidence systems.  All scalar mass on `S₀`
cancels; only its polarization against the activation seam `S₁ \ S₀`, the seam norm, and the
old-minus-new normalized incidence energy remain.
-/
theorem routeE_nestedIncidenceComplement_sub_eq_activationSeam_add_energyDifference
    { ι₀ ι₁ κ : Type*} [DecidableEq ι₀] [DecidableEq ι₁] [DecidableEq κ]
    (P₀ : Finset ι₀) (P₁ : Finset ι₁) (S₀ S₁ : Finset κ)
    (F₀ : κ → Finset ι₀) (F₁ : κ → Finset ι₁) (c : κ → ℂ)
    (hS : S₀ ⊆ S₁)
    (hF₀sub : ∀ n ∈ S₀, F₀ n ⊆ P₀) (hF₀ne : ∀ n ∈ S₀, (F₀ n).Nonempty)
    (hF₁sub : ∀ n ∈ S₁, F₁ n ⊆ P₁) (hF₁ne : ∀ n ∈ S₁, (F₁ n).Nonempty) :
    (∑ n ∈ S₁, ∑ m ∈ S₁,
        routeEIncidenceComplement (F₁ n) (F₁ m) *
          (c n * (starRingEnd ℂ) (c m)).re) -
      (∑ n ∈ S₀, ∑ m ∈ S₀,
        routeEIncidenceComplement (F₀ n) (F₀ m) *
          (c n * (starRingEnd ℂ) (c m)).re) =
      2 * ((∑ n ∈ S₀, c n) *
          (starRingEnd ℂ) (∑ n ∈ S₁ \ S₀, c n)).re +
        Complex.normSq (∑ n ∈ S₁ \ S₀, c n) +
        (∑ p ∈ P₀, Complex.normSq
          (routeENormalizedIncidenceBlock S₀ F₀ c p)) -
        ∑ p ∈ P₁, Complex.normSq
          (routeENormalizedIncidenceBlock S₁ F₁ c p) := by
  rw [routeE_incidenceComplement_decomposition P₁ S₁ F₁ c hF₁sub hF₁ne,
    routeE_incidenceComplement_decomposition P₀ S₀ F₀ c hF₀sub hF₀ne]
  have hsplit : (∑ n ∈ S₁, c n) =
      (∑ n ∈ S₀, c n) + ∑ n ∈ S₁ \ S₀, c n := by
    rw [← Finset.sum_union]
    · congr 1
      exact (Finset.union_sdiff_of_subset hS).symm
    · exact Finset.disjoint_left.mpr fun x hx₀ hx₁ =>
        (Finset.mem_sdiff.mp hx₁).2 hx₀
  rw [hsplit, Complex.normSq_add]
  ring

/-- Enlarging a designated-prime aperture can only enlarge its active integer set. -/
theorem ramareActiveSet_mono {P Q : Finset ℕ} {M : ℕ} (hPQ : P ⊆ Q) :
    ramareActiveSet P M ⊆ ramareActiveSet Q M := by
  intro n hn
  rw [ramareActiveSet] at hn ⊢
  rcases Finset.mem_filter.mp hn with ⟨hnI, ⟨p, hp⟩⟩
  refine Finset.mem_filter.mpr ⟨hnI, ⟨p, ?_⟩⟩
  rw [mem_primeFactorsIn] at hp ⊢
  exact ⟨hPQ hp.1, hp.2⟩

/-- Arithmetic nested-aperture localization for arbitrary source coefficients. -/
theorem ramareIncidenceComplement_nestedAperture
    (P Q : Finset ℕ) (M : ℕ) (c : ℕ → ℂ) (hPQ : P ⊆ Q) :
    (∑ n ∈ ramareActiveSet Q M, ∑ m ∈ ramareActiveSet Q M,
        ramareIncidenceComplement Q n m *
          (c n * (starRingEnd ℂ) (c m)).re) -
      (∑ n ∈ ramareActiveSet P M, ∑ m ∈ ramareActiveSet P M,
        ramareIncidenceComplement P n m *
          (c n * (starRingEnd ℂ) (c m)).re) =
      2 * ((∑ n ∈ ramareActiveSet P M, c n) *
          (starRingEnd ℂ)
            (∑ n ∈ ramareActiveSet Q M \ ramareActiveSet P M, c n)).re +
        Complex.normSq
          (∑ n ∈ ramareActiveSet Q M \ ramareActiveSet P M, c n) +
        (∑ p ∈ P, Complex.normSq
          (routeENormalizedIncidenceBlock (ramareActiveSet P M)
            (primeFactorsIn P) c p)) -
        ∑ q ∈ Q, Complex.normSq
          (routeENormalizedIncidenceBlock (ramareActiveSet Q M)
            (primeFactorsIn Q) c q) := by
  classical
  have hPsub : ∀ n ∈ ramareActiveSet P M, primeFactorsIn P n ⊆ P := by
    intro n hn p hp
    exact (mem_primeFactorsIn.mp hp).1
  have hPne : ∀ n ∈ ramareActiveSet P M, (primeFactorsIn P n).Nonempty := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hQsub : ∀ n ∈ ramareActiveSet Q M, primeFactorsIn Q n ⊆ Q := by
    intro n hn q hq
    exact (mem_primeFactorsIn.mp hq).1
  have hQne : ∀ n ∈ ramareActiveSet Q M, (primeFactorsIn Q n).Nonempty := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  simpa [routeEIncidenceComplement, ramareIncidenceComplement] using
    routeE_nestedIncidenceComplement_sub_eq_activationSeam_add_energyDifference
      P Q (ramareActiveSet P M) (ramareActiveSet Q M)
      (primeFactorsIn P) (primeFactorsIn Q) c
      (ramareActiveSet_mono hPQ) hPsub hPne hQsub hQne

/-- The exact source-faithful remainder exposed by enlarging a Ramaré prime aperture. -/
noncomputable def ramareNestedApertureResidual
    (P Q : Finset ℕ) (M : ℕ) (w : ℝ) : ℝ :=
  2 * ((∑ n ∈ ramareActiveSet P M, moebiusPhase w n) *
      (starRingEnd ℂ)
        (∑ n ∈ ramareActiveSet Q M \ ramareActiveSet P M,
          moebiusPhase w n)).re +
    Complex.normSq
      (∑ n ∈ ramareActiveSet Q M \ ramareActiveSet P M,
        moebiusPhase w n) +
    (∑ p ∈ P, Complex.normSq
      (routeENormalizedIncidenceBlock (ramareActiveSet P M)
        (primeFactorsIn P) (moebiusPhase w) p)) -
    ∑ q ∈ Q, Complex.normSq
      (routeENormalizedIncidenceBlock (ramareActiveSet Q M)
        (primeFactorsIn Q) (moebiusPhase w) q)

/--
Pointwise inter-modulus cancellation for the literal Möbius Ramaré off-diagonal.  No old scalar
mass remains.
-/
theorem ramarePrimeOffDiagonalIntegrand_nestedAperture
    {P Q : Finset ℕ} (hPQ : P ⊆ Q)
    (hPprime : ∀ p ∈ P, p.Prime) (hQprime : ∀ q ∈ Q, q.Prime)
    (M : ℕ) (w : ℝ) :
    ramarePrimeOffDiagonalIntegrand Q M w -
        ramarePrimeOffDiagonalIntegrand P M w =
      ramareNestedApertureResidual P Q M w := by
  classical
  simp only [ramarePrimeOffDiagonalIntegrand]
  rw [ramarePrimeOffDiagonalIntegrand_eq_integerIncidence hQprime,
    ramarePrimeOffDiagonalIntegrand_eq_integerIncidence hPprime]
  simpa only [ramareNestedApertureResidual] using
    ramareIncidenceComplement_nestedAperture P Q M (moebiusPhase w) hPQ

/-- The finite prime-pair Ramaré integrand is continuous in Mellin frequency. -/
theorem continuous_ramarePrimeOffDiagonalIntegrand (P : Finset ℕ) (M : ℕ) :
    Continuous (ramarePrimeOffDiagonalIntegrand P M) := by
  classical
  change Continuous fun w : ℝ =>
    ∑ p ∈ P, ∑ q ∈ P.erase p,
      ((moebiusPhase w p * ramareCofactorPoly P M p w) *
        (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re
  apply continuous_finsetSum
  intro p hp
  apply continuous_finsetSum
  intro q hq
  refine Complex.continuous_re.comp ?_
  exact (((continuous_moebiusPhase p).mul (continuous_ramareCofactorPoly P M p)).mul
    (Complex.continuous_conj.comp
      ((continuous_moebiusPhase q).mul (continuous_ramareCofactorPoly P M q))))

/--
Integrated nested-aperture identity for the physical Gallagher off-diagonal.  Downstream estimates
need control only `ramareNestedApertureResidual`, not either aperture's full scalar mode.
-/
theorem ramarePrimeOffDiagonal_nestedAperture
    {P Q : Finset ℕ} (hPQ : P ⊆ Q)
    (hPprime : ∀ p ∈ P, p.Prime) (hQprime : ∀ q ∈ Q, q.Prime)
    (M : ℕ) (W : ℝ) :
    ramarePrimeOffDiagonal Q M W - ramarePrimeOffDiagonal P M W =
      ∫ w in Set.Icc (-W) W, ramareNestedApertureResidual P Q M w := by
  rw [ramarePrimeOffDiagonal_eq_integral_integrand,
    ramarePrimeOffDiagonal_eq_integral_integrand]
  rw [← MeasureTheory.integral_sub
    (continuous_ramarePrimeOffDiagonalIntegrand Q M).integrableOn_Icc
    (continuous_ramarePrimeOffDiagonalIntegrand P M).integrableOn_Icc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with w
  exact ramarePrimeOffDiagonalIntegrand_nestedAperture hPQ hPprime hQprime M w

end RHTower.Sieve
