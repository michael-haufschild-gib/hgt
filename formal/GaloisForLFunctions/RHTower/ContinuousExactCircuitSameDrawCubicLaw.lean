import GaloisForLFunctions.RHTower.CompactExactCircuitNetTransferLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix Set Metric

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The canonical rank augmentation costs only one occupied replica direction. -/
theorem finrank_pairQubitRankAugmentedEndpoint_residual_le
    {L : ℕ} {C : Type*}
    (V : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin (L * 2))) ℂ)
    (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r
        (physicalUnitaryChoiResidualTarget (fun c =>
          finiteGaussianHermitianPencilReindexedEndpoint
            (pairQubitPathUnitaryReindex L
              (pairQubitRankAugmentedEndpoint
                (fun c => unitaryGroupReindex
                  (pairQubitPathConfigurationEquiv L).symm (V c)) c))))) ≤
      Module.finrank ℂ (replicaTargetSpan r
        (physicalUnitaryChoiResidualTarget (fun c =>
          finiteGaussianHermitianPencilReindexedEndpoint (V c)))) + 1 := by
  let targetC := physicalUnitaryChoiResidualTarget (fun c =>
    finiteGaussianHermitianPencilReindexedEndpoint (V c))
  let targetD := physicalUnitaryChoiResidualTarget (fun _ : Unit =>
    finiteGaussianHermitianPencilReindexedEndpoint
      (pairQubitPathUnitaryReindex L (pairQubitCanonicalTracelessEndpoint L)))
  have hfamily : (physicalUnitaryChoiResidualTarget (fun c =>
      finiteGaussianHermitianPencilReindexedEndpoint
        (pairQubitPathUnitaryReindex L
          (pairQubitRankAugmentedEndpoint
            (fun c => unitaryGroupReindex
              (pairQubitPathConfigurationEquiv L).symm (V c)) c)))) =
      Sum.elim targetC targetD := by
    funext c
    cases c with
    | inl c =>
        simp only [physicalUnitaryChoiResidualTarget,
          pairQubitRankAugmentedEndpoint, Sum.elim_inl]
        rw [show pairQubitPathUnitaryReindex L
            (unitaryGroupReindex (pairQubitPathConfigurationEquiv L).symm (V c)) = V c by
          exact unitaryGroupReindex_apply_symm (pairQubitPathConfigurationEquiv L) (V c)]
        rfl
    | inr u =>
        rfl
  rw [hfamily]
  refine (finrank_replicaTargetSpan_sum_le_add r targetC targetD).trans ?_
  gcongr
  exact finrank_replicaTargetSpan_le_card r targetD

/-- Every finite subfamily of the exact-depth continuum has an augmented
residual design whose occupied dimension is bounded independently of net size. -/
theorem finrank_pairQubitExactCircuitRankAugmentedEndpoint_residual_le
    {L s : ℕ} {C : Type*}
    (V : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin (L * 2))) ℂ)
    (hV : ∀ c, V c ∈ TwoQubitArchitecture.circuitImageExact (L * 2) s)
    (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r
        (physicalUnitaryChoiResidualTarget (fun c =>
          finiteGaussianHermitianPencilReindexedEndpoint
            (pairQubitPathUnitaryReindex L
              (pairQubitRankAugmentedEndpoint
                (fun c => unitaryGroupReindex
                  (pairQubitPathConfigurationEquiv L).symm (V c)) c))))) ≤
      ((L * 2) * (L * 2)) ^ s * (r * s + 1) ^ (s * 16) + 1 := by
  exact (finrank_pairQubitRankAugmentedEndpoint_residual_le V r).trans
    (Nat.add_le_add_right
      (finrank_physicalResidual_exactCircuitImage_le V hV r) 1)

/-- Compact exact-depth circuit image has a finite internal net in matrix
operator norm, rather than only in its inherited entrywise metric. -/
theorem exists_finite_internal_exactCircuitOperatorNet
    {n s : ℕ} (hn : 2 ≤ n) {eps : ℝ} (heps : 0 < eps) :
    ∃ net : Finset (Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ),
      (∀ V ∈ net, V ∈ TwoQubitArchitecture.circuitImageExact n s) ∧
      net.Nonempty ∧
      ∀ U ∈ TwoQubitArchitecture.circuitImageExact n s,
        ∃ V ∈ net,
          ‖(U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) -
            (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)‖ < eps := by
  let K := TwoQubitArchitecture.circuitImageExact n s
  let opBall : K → Set
      (Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) := fun V =>
    {U | ‖(U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) -
      (V.1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)‖ < eps}
  have hopen : ∀ V : K, IsOpen (opBall V) := by
    intro V
    exact isOpen_lt
      (continuous_norm.comp (continuous_subtype_val.sub continuous_const))
      continuous_const
  have hcover : K ⊆ ⋃ V : K, opBall V := by
    intro U hUK
    refine Set.mem_iUnion.mpr ⟨⟨U, hUK⟩, ?_⟩
    simp [opBall, heps]
  obtain ⟨centers, hcenters⟩ :=
    (TwoQubitArchitecture.isCompact_circuitImageExact n s).elim_finite_subcover
      opBall hopen hcover
  let net : Finset (Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :=
    centers.image Subtype.val
  have hKne : K.Nonempty := circuitImageExact_nonempty_of_two_le hn s
  have hnetne : net.Nonempty := by
    obtain ⟨U, hUK⟩ := hKne
    obtain ⟨V, hV⟩ := Set.mem_iUnion.mp (hcenters hUK)
    obtain ⟨hVcenter, -⟩ := Set.mem_iUnion.mp hV
    exact ⟨V.1, Finset.mem_image.mpr ⟨V, hVcenter, rfl⟩⟩
  refine ⟨net, ?_, hnetne, ?_⟩
  · intro V hVnet
    obtain ⟨W, -, hWV⟩ := Finset.mem_image.mp hVnet
    rw [← hWV]
    exact W.2
  · intro U hUK
    obtain ⟨V, hV⟩ := Set.mem_iUnion.mp (hcenters hUK)
    obtain ⟨hVcenter, hUV⟩ := Set.mem_iUnion.mp hV
    exact ⟨V.1, Finset.mem_image.mpr ⟨V, hVcenter, rfl⟩, hUV⟩

/-- Same-draw growth and continuous exact-depth circuit exclusion. The
probabilistic budget depends on occupied polynomial rank, not covering number. -/
theorem exists_pairQubitProjective_growth_noContinuousExactCircuitReturn
    {L : ℕ} (hL : 2 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L)
    {rho scale : ℝ} (hrho : 0 ≤ rho)
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    (hscale : scale ≠ 0)
    (s : ℕ) {r : ℕ} (hr : 0 < r) {delta kappa : ℝ}
    (hdelta : 0 < delta) (hkappa : 0 < kappa)
    {guard eta returnRadius thetaN thetaW radius : ℝ}
    (hguard : 0 ≤ guard)
    (hTpos : 0 < 2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard)
    (hreturnPos : 0 < returnRadius)
    (hthetaW : 0 < thetaW) (hgap : thetaW < thetaN)
    (hradius : 0 < radius)
    (hmeshReturn : thetaN - thetaW ≤ returnRadius)
    (hreturnT : returnRadius ≤ 2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard)
    (hguardStart : guard ≤ returnRadius)
    (hscalarBudget :
      Real.sqrt (1 - inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) /
          (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ (2 : ℕ))) +
        (2 * Real.pi * (L : ℝ) ^ (3 : ℕ)) *
          (rho * nearestNeighborPathLocalGeneratorMass L +
            |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ (3 : ℕ))) < eta)
    (hselect : pairQubitWeakTwoLocalGrowthFailureBudget L +
        Real.exp (-twoLocalAnchorTransverseUniformRate (L * 2) r scale
          (pairQubitProjectiveSeedGrowingReplicaOscillationCeiling L rho scale)) /
            kappa < 1)
    (hmoment :
      ((((L * 2) * (L * 2)) ^ s * (r * s + 1) ^ (s * 16) + 1 : ℕ) : ℝ) *
        ((r.factorial : ℝ) *
            (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ ^ r +
          kappa +
          Real.exp (-(((2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard) * delta) ^ (2 : ℕ)) / 2)) <
        gaussianFloorTwo *
          (((thetaN - thetaW) /
              pairQubitProjectiveStaticChoiSpeedCeiling L rho scale) /
            (2 * (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard))) *
              (thetaW ^ (2 : ℕ)) ^ r) :
    ∃ x : TwoLocalPauliCoefficientSpace (L * 2),
      x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
      MaximallyProjectiveEnergy
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) ∧
      ¬ ∃ t ∈ Icc
          (returnRadius + (thetaN - thetaW) /
            staticChoiSpeed
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
          (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard),
        ∃ U ∈ TwoQubitArchitecture.circuitImageExact (L * 2) s,
          eta + thetaN + radius ≤ ‖inner ℂ
            (staticSpectralChoiVector
              (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) t
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
            (GaloisForLFunctions.RHTower.choiVector
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
                L p scale x
                  (unitaryGroupReindex
                    (pairQubitPathConfigurationEquiv L).symm U) :
                Matrix (Fin (Fintype.card
                  (FiniteQubitConfiguration (Fin (L * 2)))))
                  (Fin (Fintype.card
                    (FiniteQubitConfiguration (Fin (L * 2))))) ℂ))‖ := by
  obtain ⟨net, hnetK, hnetne, hcover⟩ :=
    exists_finite_internal_exactCircuitOperatorNet (by omega : 2 ≤ L * 2) hradius
  letI : Nonempty {V // V ∈ net} := Finset.nonempty_coe_sort.mpr hnetne
  let V : net → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin (L * 2))) ℂ := fun w => w.1
  let Upair : net → Matrix.unitaryGroup (Config (PairQubit L)) ℂ := fun w =>
    unitaryGroupReindex (pairQubitPathConfigurationEquiv L).symm (V w)
  let Uaug := pairQubitRankAugmentedEndpoint Upair
  have hrank : Module.finrank ℂ (replicaTargetSpan r
      (physicalUnitaryChoiResidualTarget (fun c =>
        finiteGaussianHermitianPencilReindexedEndpoint
          (pairQubitPathUnitaryReindex L (Uaug c))))) ≤
      ((L * 2) * (L * 2)) ^ s * (r * s + 1) ^ (s * 16) + 1 := by
    exact finrank_pairQubitExactCircuitRankAugmentedEndpoint_residual_le V
      (fun w => hnetK w.1 w.2) r
  have hmoment' :
      (Module.finrank ℂ (replicaTargetSpan r
          (physicalUnitaryChoiResidualTarget (fun c =>
            finiteGaussianHermitianPencilReindexedEndpoint
              (pairQubitPathUnitaryReindex L (Uaug c))))) : ℝ) *
        ((r.factorial : ℝ) *
            (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ ^ r +
          kappa +
          Real.exp (-(((2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard) * delta) ^ (2 : ℕ)) / 2)) <
        gaussianFloorTwo *
          (((thetaN - thetaW) /
              pairQubitProjectiveStaticChoiSpeedCeiling L rho scale) /
            (2 * (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard))) *
              (thetaW ^ (2 : ℕ)) ^ r := by
    refine (mul_le_mul_of_nonneg_right (by exact_mod_cast hrank) ?_).trans_lt hmoment
    positivity
  have hpos : 0 < Module.finrank ℂ (replicaTargetSpan r
      (physicalUnitaryChoiResidualTarget (fun c =>
        finiteGaussianHermitianPencilReindexedEndpoint
          (pairQubitPathUnitaryReindex L (Uaug c))))) := by
    exact pairQubitRankAugmentedEndpoint_residual_finrank_pos (by omega) r Upair
  obtain ⟨x, hx, hmax, hnoAug⟩ :=
    exists_pairQubitProjective_growth_noCompleteTargetReturn hL hp hrho hseed hscale
      Uaug hr hdelta hkappa hpos hguard hTpos hreturnPos hthetaW hgap
      hmeshReturn hreturnT hguardStart hscalarBudget hselect hmoment'
  refine ⟨x, hx, hmax, ?_⟩
  let onset := returnRadius + (thetaN - thetaW) /
    staticChoiSpeed
      (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)
  let finish := 2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard
  let state : {t : ℝ // t ∈ Icc onset finish} →
      EuclideanSpace ℂ
        (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) ×
          Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) := fun t =>
    staticSpectralChoiVector
      (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) t.1
      (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)
  let target : {U // U ∈ TwoQubitArchitecture.circuitImageExact (L * 2) s} →
      EuclideanSpace ℂ
        (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) ×
          Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) := fun U =>
    GaloisForLFunctions.RHTower.choiVector
      (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint L p scale x
        (unitaryGroupReindex (pairQubitPathConfigurationEquiv L).symm U.1) :
          Matrix (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))))
            (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) ℂ)
  let netTarget : net → EuclideanSpace ℂ
      (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) ×
        Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) := fun w =>
    GaloisForLFunctions.RHTower.choiVector
      (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint L p scale x (Upair w) :
        Matrix (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))))
          (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) ℂ)
  have hchoice : ∀ U : {U // U ∈ TwoQubitArchitecture.circuitImageExact (L * 2) s},
      ∃ w : net, ‖(U.1 : Matrix
          (FiniteQubitConfiguration (Fin (L * 2)))
          (FiniteQubitConfiguration (Fin (L * 2))) ℂ) -
        (w.1 : Matrix
          (FiniteQubitConfiguration (Fin (L * 2)))
          (FiniteQubitConfiguration (Fin (L * 2))) ℂ)‖ < radius := by
    intro U
    obtain ⟨W, hWnet, hdist⟩ := hcover U.1 U.2
    exact ⟨⟨W, hWnet⟩, hdist⟩
  choose netIndex hnetIndex using hchoice
  have hstateNorm : ∀ t, ‖state t‖ = 1 := by
    intro t
    exact staticSpectralChoiVector_norm
      (Fintype.card_pos : 0 < Fintype.card
        (FiniteQubitConfiguration (Fin (L * 2)))) _ _
  have hnetApprox : ∀ U, ‖target U - netTarget (netIndex U)‖ ≤ radius := by
    intro U
    let P := twoLocalPauliGaussianHermitianPencil (L * 2)
    let Hfin := P.affineReindexedHamiltonian
      (pairQubitProjectivePauliSeed L p) (scale • x)
    have hHfin : Hfin.IsHermitian :=
      P.affineReindexedHamiltonian_isHermitian
        (pairQubitProjectivePauliSeed_isHermitian L p) (scale • x)
    have hLip := norm_choiVector_hermitianSpectralEndpoint_sub_le
      (Fintype.card_pos : 0 < Fintype.card
        (FiniteQubitConfiguration (Fin (L * 2)))) hHfin
      (finiteGaussianHermitianPencilReindexedEndpoint U.1)
      (finiteGaussianHermitianPencilReindexedEndpoint (netIndex U).1)
    rw [norm_finiteGaussianHermitianPencilReindexedEndpoint_sub_eq] at hLip
    have hdist : ‖(U.1 : Matrix
        (FiniteQubitConfiguration (Fin (L * 2)))
        (FiniteQubitConfiguration (Fin (L * 2))) ℂ) -
        ((netIndex U).1 : Matrix
          (FiniteQubitConfiguration (Fin (L * 2)))
          (FiniteQubitConfiguration (Fin (L * 2))) ℂ)‖ < radius := by
      exact hnetIndex U
    have hcore := hLip.trans hdist.le
    have hendpointU : hermitianSpectralEndpoint hHfin
        (finiteGaussianHermitianPencilReindexedEndpoint U.1) =
      pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint L p scale x
        (unitaryGroupReindex (pairQubitPathConfigurationEquiv L).symm U.1) := by
      have hproof : hHfin = P.affineReindexedHamiltonian_isHermitian
          (pairQubitProjectivePauliSeed_isHermitian L p) (scale • x) :=
        Subsingleton.elim _ _
      rw [hproof]
      unfold pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
      unfold FiniteGaussianHermitianPencil.scaledAffineSpectralEndpoint
      unfold FiniteGaussianHermitianPencil.affineSpectralEndpoint
      rw [show pairQubitPathUnitaryReindex L
          (unitaryGroupReindex (pairQubitPathConfigurationEquiv L).symm U.1) = U.1 by
        exact unitaryGroupReindex_apply_symm (pairQubitPathConfigurationEquiv L) U.1]
    have hendpointW : hermitianSpectralEndpoint hHfin
        (finiteGaussianHermitianPencilReindexedEndpoint (netIndex U).1) =
      pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint L p scale x
        (Upair (netIndex U)) := by
      have hproof : hHfin = P.affineReindexedHamiltonian_isHermitian
          (pairQubitProjectivePauliSeed_isHermitian L p) (scale • x) :=
        Subsingleton.elim _ _
      rw [hproof]
      unfold pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
      unfold FiniteGaussianHermitianPencil.scaledAffineSpectralEndpoint
      unfold FiniteGaussianHermitianPencil.affineSpectralEndpoint
      rw [show pairQubitPathUnitaryReindex L (Upair (netIndex U)) =
          (netIndex U).1 by
        exact unitaryGroupReindex_apply_symm
          (pairQubitPathConfigurationEquiv L) (netIndex U).1]
    rw [hendpointU, hendpointW] at hcore
    simpa [target, netTarget] using hcore
  have hnoNet : ¬ ∃ t : {t : ℝ // t ∈ Icc onset finish}, ∃ w : net,
      eta + thetaN ≤ ‖inner ℂ (state t) (netTarget w)‖ := by
    rintro ⟨t, w, hhit⟩
    apply hnoAug
    refine ⟨t.1, ?_, Sum.inl w, ?_⟩
    · exact t.2
    · simpa [onset, finish, state, netTarget, Uaug,
        pairQubitRankAugmentedEndpoint] using hhit
  have hnoFull := no_innerCapture_of_finiteNet state hstateNorm target netTarget
    netIndex hnetApprox hnoNet
  rintro ⟨t, ht, U, hUK, hhit⟩
  apply hnoFull
  exact ⟨⟨t, by simpa [onset, finish] using ht⟩, ⟨U, hUK⟩,
    by simpa [state, target] using hhit⟩

end

end RHTower
