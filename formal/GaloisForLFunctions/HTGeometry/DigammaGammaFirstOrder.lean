import GaloisForLFunctions.HTGeometry.InverseGammaPoleCluster
import GaloisForLFunctions.HTGeometry.VanishingResidueFirstOrderObstruction

/-!
# Digamma after Gamma has differential order at least two

The reciprocal-Gamma branches give, at every negative integer, a cluster of simple poles of
`digamma ∘ Gamma` whose nonzero residues tend to zero.  The general vanishing-residue cluster
obstruction therefore rules out every polynomial-coefficient first-order algebraic differential
relation.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Complex Filter Topology Set

noncomputable section

/-- One fixed reciprocal-Gamma pole branch at every negative integer. -/
def chosenReciprocalGammaPoleBranch (n : ℕ) : ReciprocalGammaPoleBranch n :=
  Classical.choice (reciprocalGammaPoleBranch_nonempty n)

/-- A tail threshold beyond which every reciprocal-integer sample is a genuine nonzero-residue
pole of `digamma ∘ Gamma`. -/
def digammaGammaClusterStart (n : ℕ) : ℕ :=
  Classical.choose <| eventually_atTop.1
    (chosenReciprocalGammaPoleBranch n).factorial_cluster_eventually

theorem digammaGammaClusterStart_spec (n : ℕ) :
    ∀ m ≥ digammaGammaClusterStart n,
      Complex.Gamma
          (chosenReciprocalGammaPoleBranch n ((m : ℂ)⁻¹)) = -(m : ℂ) ∧
      inverseGammaBranchResidueInterpolation
          (chosenReciprocalGammaPoleBranch n) ((m : ℂ)⁻¹) ≠ 0 ∧
      Tendsto
        (fun z : ℂ => (z - chosenReciprocalGammaPoleBranch n ((m : ℂ)⁻¹)) *
          Complex.digamma (Complex.Gamma z))
        (𝓝[≠] (chosenReciprocalGammaPoleBranch n ((m : ℂ)⁻¹)))
        (𝓝 (inverseGammaBranchResidueInterpolation
          (chosenReciprocalGammaPoleBranch n) ((m : ℂ)⁻¹))) :=
  Classical.choose_spec <| eventually_atTop.1
    (chosenReciprocalGammaPoleBranch n).factorial_cluster_eventually

def digammaGammaClusterIndex (n m : ℕ) : ℕ := digammaGammaClusterStart n + m

def digammaGammaClusterPole (n m : ℕ) : ℂ :=
  chosenReciprocalGammaPoleBranch n ((digammaGammaClusterIndex n m : ℂ)⁻¹)

def digammaGammaClusterResidue (n m : ℕ) : ℂ :=
  inverseGammaBranchResidueInterpolation (chosenReciprocalGammaPoleBranch n)
    ((digammaGammaClusterIndex n m : ℂ)⁻¹)

theorem tendsto_digammaGammaClusterIndex (n : ℕ) :
    Tendsto (digammaGammaClusterIndex n) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with m hm
  simp only [digammaGammaClusterIndex]
  omega

theorem tendsto_digammaGammaClusterPole (n : ℕ) :
    Tendsto (digammaGammaClusterPole n) atTop (𝓝 (-(n : ℂ))) := by
  have hinv := tendsto_natCast_inv_complex.comp (tendsto_digammaGammaClusterIndex n)
  have hbranch := (chosenReciprocalGammaPoleBranch n).analyticAt_zero.continuousAt.tendsto.comp hinv
  have hzero := (chosenReciprocalGammaPoleBranch n).map_zero
  simpa [digammaGammaClusterPole, Function.comp_apply, hzero] using hbranch

theorem tendsto_digammaGammaClusterResidue_zero (n : ℕ) :
    Tendsto (digammaGammaClusterResidue n) atTop (𝓝 0) := by
  have hinv := tendsto_natCast_inv_complex.comp (tendsto_digammaGammaClusterIndex n)
  have hres := (analyticAt_inverseGammaBranchResidueInterpolation
    (chosenReciprocalGammaPoleBranch n)).continuousAt.tendsto.comp hinv
  simpa [digammaGammaClusterResidue, inverseGammaBranchResidueInterpolation] using hres

theorem digammaGammaCluster_good (n m : ℕ) :
    digammaGammaClusterResidue n m ≠ 0 ∧
    Tendsto
      (fun z : ℂ => (z - digammaGammaClusterPole n m) *
        Complex.digamma (Complex.Gamma z))
      (𝓝[≠] (digammaGammaClusterPole n m))
      (𝓝 (digammaGammaClusterResidue n m)) := by
  have h := digammaGammaClusterStart_spec n (digammaGammaClusterIndex n m) (by
    simp [digammaGammaClusterIndex])
  simpa [digammaGammaClusterPole, digammaGammaClusterResidue] using ⟨h.2.1, h.2.2⟩

theorem meromorphicAt_digamma_comp_Gamma_clusterPole (n m : ℕ) :
    MeromorphicAt (fun z : ℂ => Complex.digamma (Complex.Gamma z))
      (digammaGammaClusterPole n m) := by
  have hspec := digammaGammaClusterStart_spec n (digammaGammaClusterIndex n m) (by
    simp [digammaGammaClusterIndex])
  have hindex : (digammaGammaClusterIndex n m : ℂ) ≠ 0 := by
    intro hzero
    apply hspec.2.1
    simp [inverseGammaBranchResidueInterpolation, hzero]
  have hoff : ∀ k : ℕ, digammaGammaClusterPole n m ≠ -(k : ℂ) := by
    intro k hk
    have hvalue := hspec.1
    rw [show chosenReciprocalGammaPoleBranch n
        ((digammaGammaClusterIndex n m : ℂ)⁻¹) = digammaGammaClusterPole n m by rfl,
      hk, Complex.Gamma_neg_nat_eq_zero] at hvalue
    apply hindex
    exact neg_eq_zero.mp hvalue.symm
  have hGamma : AnalyticAt ℂ Complex.Gamma (digammaGammaClusterPole n m) :=
    analyticAt_Gamma _ hoff
  simpa [Function.comp_def] using
    Complex.meromorphic_digamma.meromorphicAt.comp_analyticAt hGamma

theorem digammaGammaCluster_deriv_principalPart (n m : ℕ) :
    Tendsto
      (fun z : ℂ => (z - digammaGammaClusterPole n m) ^ 2 *
        deriv (fun w : ℂ => Complex.digamma (Complex.Gamma w)) z)
      (𝓝[≠] (digammaGammaClusterPole n m))
      (𝓝 (-digammaGammaClusterResidue n m)) := by
  exact tendsto_deriv_of_meromorphicAt_of_simplePoleResidue
    (meromorphicAt_digamma_comp_Gamma_clusterPole n m)
    (digammaGammaCluster_good n m).1
    (digammaGammaCluster_good n m).2

/-- **No first-order ADE for `digamma ∘ Gamma`.**  Every nonempty finite first-order row

`Σ A_(i,j)(z) (digamma (Gamma z))^i ((digamma ∘ Gamma)'(z))^j`

with nonzero polynomial coefficients is nonzero at some complex point. -/
theorem digamma_comp_Gamma_no_firstOrderPolynomialRelation
    (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (A : (ℕ × ℕ) → Polynomial ℂ) (hA : ∀ p ∈ S, A p ≠ 0) :
    ∃ z : ℂ, firstOrderPolynomialRowEval S A
      (fun w : ℂ => Complex.digamma (Complex.Gamma w)) z ≠ 0 := by
  apply exists_firstOrderPolynomialRowEval_ne_zero_of_infiniteVanishingResidueClusters
    S hS A hA (fun w : ℂ => Complex.digamma (Complex.Gamma w))
      (fun n : ℕ => -(n : ℂ))
      (fun a b h => by
        have h' : (a : ℂ) = (b : ℂ) := neg_injective h
        exact_mod_cast h')
      digammaGammaClusterPole digammaGammaClusterResidue
  · exact tendsto_digammaGammaClusterPole
  · exact tendsto_digammaGammaClusterResidue_zero
  · exact fun n m => (digammaGammaCluster_good n m).1
  · exact fun n m => (digammaGammaCluster_good n m).2
  · exact digammaGammaCluster_deriv_principalPart

/-- **`digamma ∘ Gamma` has differential order at least two.**  It satisfies no nonzero
algebraic differential equation of order at most one with complex polynomial coefficients.

This is the differential-order predicate used throughout `HTGeometry`, not merely a preselected
finite-row formulation: `firstOrderRowPolynomial` canonically converts an arbitrary witness in
`z,f,f'` into the row excluded above. -/
theorem not_differentiallyAlgebraicOfOrder_one_digamma_comp_Gamma :
    ¬ DifferentiallyAlgebraicOfOrder
      (fun z : ℂ => Complex.digamma (Complex.Gamma z)) 1 := by
  rintro ⟨P, hP, hrelation⟩
  let f : ℂ → ℂ := fun z => Complex.digamma (Complex.Gamma z)
  obtain ⟨z, hz⟩ := digamma_comp_Gamma_no_firstOrderPolynomialRelation
    (firstOrderRowSupport P) (firstOrderRowSupport_nonempty hP)
    (firstOrderRowCoefficient P) (fun _ hp => firstOrderRowCoefficient_ne_zero hp)
  apply hz
  change firstOrderPolynomialRowEval
    ((firstOrderRowPolynomial P).support.image finTwoExponentPair)
    (fun p => (firstOrderRowPolynomial P).coeff (exponentPairFinTwo p)) f z = 0
  rw [firstOrderPolynomialRowEval_eq_mvPolynomial_eval₂]
  rw [← firstOrderRowPolynomial_eval P z (f z) (deriv f z)]
  have htail :
      Fin.cons (f z) (fun _ : Fin 1 => deriv f z) =
        fun j : Fin 2 => iteratedDeriv (j : ℕ) f z := by
    funext j
    fin_cases j
    · simp
    · change deriv f z = iteratedDeriv 1 f z
      simp
  rw [htail]
  simpa [f] using hrelation z

end

end GaloisForLFunctions.HTGeometry
