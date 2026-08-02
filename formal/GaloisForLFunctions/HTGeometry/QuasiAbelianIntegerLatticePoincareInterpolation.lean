import GaloisForLFunctions.HTGeometry.QuasiAbelianIntegerLatticeSeparator
import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareSeries
import GaloisForLFunctions.HTGeometry.QuasiAbelianGaussianFlatSeed

/-!
# Exact mixed-jet interpolation by integer-lattice Poincare series

The explicit flat separator supplies one seed column per packet point.  Normal convergence is
the only analytic input: once it is available for those literal polynomial-multiplied seeds, the
zero-index term supplies the prescribed jet and every other lattice term vanishes to full packet
order.  Summing the columns proves surjectivity for the same fixed automorphic factor.
-/

open Filter Function Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Exact local-normal-convergence obligation for the explicit flat separator seeds.  This is not
jet-ampleness hidden in a structure: it only says the concrete Poincare family constructed in
`QuasiAbelianIntegerLatticeSeparator` converges after multiplication by any polynomial. -/
def AutomorphicFactor.GaussianFlatIntegerLatticeSeedsNormallySummable
    {d : ℕ} (ψ : AutomorphicFactor d (standardIntegerLattice d)) : Prop :=
  ∀ (I : Type u) [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (m : ℕ) (hm : 0 < m),
    ∃ σ : Fin d → ℝ, (∀ c, 0 < σ c) ∧
      ∀ (target : I) (P : MvPolynomial (Fin d) ℂ),
        let S := flatIntegerLatticePacketSeparatorData w hdistinct target m hm
        let D := gaussianFlatSeedData σ (w target) hm
        SummableLocallyUniformlyOn
          (fun γ ↦ poincareTerm ψ
            (multivariateEntireMul S.bump
              (multivariateEntireMul D.damping
                (mvPolynomialMultivariateEntire P))) γ)
          Set.univ

/-- Distinct classes modulo any additive subgroup have distinct chosen lifts. -/
theorem injective_of_pairwiseDistinctModulo
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    {I : Type*} {w : I → Fin d → ℂ}
    (h : PairwiseDistinctModulo Γ w) : Function.Injective w := by
  intro i j hij
  by_contra hne
  apply h hne
  rw [hij, sub_self]
  exact Γ.zero_mem

/-- Every requested packet order is strictly below one plus their finite sum. -/
theorem packetOrder_lt_succ_sum
    {I : Type*} [Fintype I] (m : I → ℕ) (i : I) :
    m i < (∑ j, m j) + 1 := by
  have hle : m i ≤ ∑ j, m j :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- **Abe integer-lattice base theorem, all finite mixed orders.**  Local normal convergence of
the literal flat polynomial seeds implies all-order jet ampleness of the fixed factor.  No tensor
power, abstract surjectivity field, or derivative-exchange assumption occurs in the proof. -/
theorem AutomorphicFactor.jetAmpleEveryFiniteOrder_standardIntegerLattice
    {d : ℕ} (ψ : AutomorphicFactor d (standardIntegerLattice d))
    (hnormal :
      AutomorphicFactor.GaussianFlatIntegerLatticeSeedsNormallySummable.{u} ψ) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} ψ := by
  intro I _ _ w m hdistinct hm prescribed
  classical
  let desired : I → (Fin d →₀ ℕ) → ℂ := fun i a ↦
    if ha : Finsupp.degree a < m i then prescribed ⟨i, ⟨a, ha⟩⟩ else 0
  have hdesired (i : I) (a : Fin d →₀ ℕ) (ha : Finsupp.degree a < m i) :
      desired i a = prescribed ⟨i, ⟨a, ha⟩⟩ := by
    dsimp only [desired]
    rw [dif_pos ha]
  obtain ⟨P, hP⟩ := exists_mvPolynomial_multiIndexJetEvalCLM_eq_arbitrary
    w (injective_of_pairwiseDistinctModulo hdistinct) m desired
  let poly : MultivariateEntire d := mvPolynomialMultivariateEntire P
  let M : ℕ := (∑ i, m i) + 1
  have hM : 0 < M := by simp [M]
  obtain ⟨σ, hσ, hnormalSeed⟩ := hnormal I w hdistinct M hM
  let S : (i : I) → FlatIntegerLatticePacketSeparatorData w i M := fun i ↦
    flatIntegerLatticePacketSeparatorData w hdistinct i M hM
  let D : (i : I) → GaussianFlatSeedData (w i) M := fun i ↦
    gaussianFlatSeedData σ (w i) hM
  let seed : I → MultivariateEntire d := fun i ↦
    multivariateEntireMul (S i).bump
      (multivariateEntireMul (D i).damping poly)
  have hseedFactor (i : I) :
      seed i = multivariateEntireMul (multivariateEntirePow (S i).normalized M)
        (multivariateEntireMul (S i).geom
          (multivariateEntireMul (D i).damping poly)) := by
    dsimp only [seed]
    rw [(S i).factorization]
    ext x
    simp only [multivariateEntireMul_apply, multivariateEntirePow_apply]
    ring
  have hseedNormal (i : I) : SummableLocallyUniformlyOn
      (fun γ ↦ poincareTerm ψ (seed i) γ) Set.univ := by
    exact hnormalSeed i P
  let form : I → ψ.forms := fun i ↦
    poincareSeriesAutomorphicForm ψ (seed i) (hseedNormal i)
  have hcolumn (i j : I) (a : Fin d →₀ ℕ)
      (ha : Finsupp.degree a < m j) :
      multiIndexJetEvalCLM (w j) a (form i).1 =
        if hji : j = i then prescribed ⟨j, ⟨a, ha⟩⟩ else 0 := by
    have haM : Finsupp.degree a < M :=
      lt_trans ha (packetOrder_lt_succ_sum m j)
    have htranslateZero : ∀ γ : standardIntegerLattice d, γ ≠ 0 →
        (S i).normalized.1 (w j + γ.1) = 0 := by
      intro γ hγ
      obtain ⟨k, hk⟩ := γ.property
      rw [← hk]
      apply (S i).normalized_zero j k
      by_cases hji : j = i
      · right
        intro hkzero
        apply hγ
        apply Subtype.ext
        rw [← hk, hkzero]
        ext c
        simp [integerCastVector]
      · exact Or.inl hji
    have hseries :=
      multiIndexJetEvalCLM_poincareSeriesEntire_eq_seed_of_powerZeros
        ψ (seed i) (S i).normalized
        (multivariateEntireMul (S i).geom
          (multivariateEntireMul (D i).damping poly))
        (hseedNormal i) (hseedFactor i) (w j) htranslateZero a haM
    change multiIndexJetEvalCLM (w j) a
      (poincareSeriesEntire ψ (seed i) (hseedNormal i)) = _
    rw [hseries]
    by_cases hji : j = i
    · subst j
      rw [(S i).preserves_target (multivariateEntireMul (D i).damping poly) a haM]
      rw [(D i).preserves_target poly a haM]
      rw [hP i a ha]
      rw [hdesired i a ha]
      simp
    · have hkill := (S i).kills_undesired
        (multivariateEntireMul (D i).damping poly) j 0 a (Or.inl hji) haM
      have hzero : multiIndexJetEvalCLM (w j) a (seed i) = 0 := by
        have hpoint : w j + integerCastVector (0 : Fin d → ℤ) = w j := by
          ext c
          simp [integerCastVector]
        rw [hpoint] at hkill
        exact hkill
      rw [hzero]
      simp [hji]
  refine ⟨∑ i, form i, ?_⟩
  funext q
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single q.1]
  · simpa using hcolumn q.1 q.1 q.2.1 q.2.2
  · intro i hi hineq
    simpa [Ne.symm hineq] using hcolumn i q.1 q.2.1 q.2.2
  · simp

end

end GaloisForLFunctions.HTGeometry
