import GaloisForLFunctions.HTGeometry.FiniteEtaleRationalFiberRank
import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationPurity
import GaloisForLFunctions.HTGeometry.CriticalBlockSourceExplicitMeridianElimination
import GaloisForLFunctions.HTGeometry.CriticalBlockFieldNontrivial
import GaloisForLFunctions.HTGeometry.CriticalSchurCollisionSupportBound
import GaloisForLFunctions.HTGeometry.FixedFieldDichotomy
import GaloisForLFunctions.HTGeometry.TranspositionBlockInvariance

/-!
# Full critical geometric monodromy

Purity makes every nontrivial block normalization finite etale.  The two explicit source
meridians collapse its fibre over the identity.  Finite-etale fibre rank, flat rank constancy, and
the fixed-field index formula then force the block stabilizer to be the whole Galois group,
contradicting properness.  Thus the action is primitive; the unconditional Schur transposition
makes the geometric monodromy the full symmetric group.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Pointwise

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 3000000

variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

private theorem isBlock_smul
    {G X : Type*} [Group G] [MulAction G X] {B : Set X}
    (hB : MulAction.IsBlock G B) (g : G) : MulAction.IsBlock G (g • B) := by
  intro g₁ g₂ hne
  simpa only [smul_smul] using
    hB (g₁ := g₁ * g) (g₂ := g₂ * g) (by simpa only [smul_smul] using hne)

/-- The actual higher-rank critical geometric monodromy action is primitive. -/
theorem criticalGeometricMonodromy_isPreprimitive :
    MulAction.IsPreprimitive (criticalGeometricMonodromy ℂ m n)
      (criticalGeometricSheet ℂ m n) := by
  classical
  letI : MulAction.IsPretransitive (criticalGeometricMonodromy ℂ m n)
      (criticalGeometricSheet ℂ m n) :=
    criticalGeometricMonodromy_isPretransitive ℂ Fact.out Fact.out
  by_contra hprim
  obtain ⟨B, hB, hB2, hBne⟩ := exists_block_of_not_isPreprimitive hprim
  obtain ⟨x, hx, y, hy, hxy⟩ := hB2
  obtain ⟨g, hg⟩ : ∃ g : criticalGeometricMonodromy ℂ m n,
      g • x = criticalSourceNormalClosureEmbedding ℂ m n :=
    MulAction.exists_smul_eq (criticalGeometricMonodromy ℂ m n) x
      (criticalSourceNormalClosureEmbedding ℂ m n)
  let B' : Set (criticalGeometricSheet ℂ m n) := g • B
  have hB' : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B' :=
    isBlock_smul hB g
  have hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B' := by
    rw [← hg]
    exact Set.smul_mem_smul_set hx
  have hB2' : ∃ x ∈ B', ∃ y ∈ B', x ≠ y := by
    refine ⟨g • x, Set.smul_mem_smul_set hx, g • y, Set.smul_mem_smul_set hy, ?_⟩
    exact (MulAction.injective g).ne hxy
  have hBne' : B' ≠ Set.univ := by
    intro h
    apply hBne
    have hs := congrArg (fun S : Set (criticalGeometricSheet ℂ m n) ↦ g⁻¹ • S) h
    simpa [B', smul_smul] using hs
  letI : Module.Flat (criticalObservationChartRing ℂ m n)
      (CriticalBlockNormalization ℂ B') :=
    criticalBlockNormalization_flat_of_sourceChart_flat ℂ hB' hmem
  letI : Algebra.FormallyEtale (criticalObservationChartRing ℂ m n)
      (CriticalBlockNormalization ℂ B') :=
    criticalBlockNormalization_formallyEtale ℂ hB' hmem hB2'
  letI : Algebra.Etale (criticalObservationChartRing ℂ m n)
      (CriticalBlockNormalization ℂ B') :=
    Algebra.Etale.of_formallyUnramified_of_flat
  have hanalytic :=
    criticalBlockCover_fiber_subsingleton_of_explicit_source_meridians hB' hmem
  let chi : AlgSpec (criticalObservationChartRing ℂ m n) :=
    (criticalObservationComplexPointHomeomorph m n).symm 1
  obtain ⟨psi, hpsi⟩ := surjective_criticalBlockNormalizationProjection B' chi
  have hfiber : Subsingleton
      {phi : AlgSpec (CriticalBlockNormalization ℂ B') //
        phi.comp (IsScalarTower.toAlgHom ℂ (criticalObservationChartRing ℂ m n)
          (CriticalBlockNormalization ℂ B')) = chi} := by
    constructor
    rintro ⟨phi, hphi⟩ ⟨phi', hphi'⟩
    apply Subtype.ext
    have ha : (criticalBlockAnalyticProjection (m := m) (n := n) (B := B')) phi = 1 := by
      change criticalObservationComplexPointHomeomorph m n
        (phi.comp (IsScalarTower.toAlgHom ℂ (criticalObservationChartRing ℂ m n)
          (CriticalBlockNormalization ℂ B'))) = 1
      rw [hphi]
      exact (criticalObservationComplexPointHomeomorph m n).apply_symm_apply 1
    have ha' : (criticalBlockAnalyticProjection (m := m) (n := n) (B := B')) phi' = 1 := by
      change criticalObservationComplexPointHomeomorph m n
        (phi'.comp (IsScalarTower.toAlgHom ℂ (criticalObservationChartRing ℂ m n)
          (CriticalBlockNormalization ℂ B'))) = 1
      rw [hphi']
      exact (criticalObservationComplexPointHomeomorph m n).apply_symm_apply 1
    have heq := hanalytic.elim
      (⟨phi, by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using ha⟩ :
        (criticalBlockAnalyticProjection (m := m) (n := n) (B := B')) ⁻¹'
          {(1 : ComplexTorusAffineChart (n + m - 2))})
      ⟨phi', by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using ha'⟩
    exact congrArg (fun z :
      (criticalBlockAnalyticProjection (m := m) (n := n) (B := B')) ⁻¹'
        {(1 : ComplexTorusAffineChart (n + m - 2))} ↦ z.1) heq
  have hlocal : Module.rankAtStalk (CriticalBlockNormalization ℂ B')
      ((⊥ : PrimeSpectrum ℂ).comap chi.toRingHom) = 1 :=
    Algebra.rankAtStalk_eq_one_of_algSpec_fiber_subsingleton chi psi hpsi hfiber
  let p₀ : PrimeSpectrum (criticalObservationChartRing ℂ m n) :=
    ⟨⊥, Ideal.isPrime_bot⟩
  have hgeneric : Module.rankAtStalk (CriticalBlockNormalization ℂ B') p₀ = 1 := by
    rw [Module.rankAtStalk_eq_of_le_of_finite_of_flat
      (CriticalBlockNormalization ℂ B') (p := p₀)
      (q := (⊥ : PrimeSpectrum ℂ).comap chi.toRingHom) bot_le]
    exact hlocal
  let A := criticalObservationChartRing ℂ m n
  let F := criticalObservationField ℂ m n
  let C := CriticalBlockNormalization ℂ B'
  let M := CriticalBlockFixedField ℂ B'
  have hmodel : Module.finrank A C = 1 := by
    rw [← Ideal.finrank_fiber_eq_finrank (M := C) (⊥ : Ideal A)]
    rw [Ideal.finrank_fiber_eq_rankAtStalk]
    exact hgeneric
  have hdegree : Module.finrank F M = 1 := by
    calc
      Module.finrank F M = Module.finrank A C :=
        Algebra.IsAlgebraic.finrank_of_isFractionRing A F C M
      _ = 1 := hmodel
  letI : FiniteDimensional F (criticalNormalClosure ℂ m n) :=
    criticalNormalClosure_finiteDimensional ℂ Fact.out Fact.out
  letI : IsGalois F (criticalNormalClosure ℂ m n) :=
    criticalNormalClosure_isGalois ℂ Fact.out Fact.out
  have hindex : (criticalBlockStabilizer ℂ B').index = 1 := by
    rw [← finrank_fixedField_eq_index (criticalBlockStabilizer ℂ B')]
    exact hdegree
  exact criticalBlockStabilizer_ne_top_of_mem_of_ne_univ ℂ hmem hBne'
    (Subgroup.index_eq_one.mp hindex)

/-- The actual higher-rank critical geometric monodromy over the complex numbers is the full
symmetric group. -/
theorem criticalGeometricMonodromy_eq_top :
    criticalGeometricMonodromy ℂ m n = ⊤ :=
  criticalGeometricMonodromy_eq_top_of_isPreprimitive ℂ
    criticalGeometricMonodromy_isPreprimitive

end

end GaloisForLFunctions.HTGeometry
