import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeTerminalOutputCharge
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion

/-!
# The actual Wiman-charge frame in a finite cascade branch

Every constituent Wiman charge embeds canonically in every deeper actual branch field.  A
Kronecker derivation for an earlier state annihilates all later charges, while its own charge has
nonzero response.  These exact laws give the triangular Jacobian used to replace the state frame
by the actual charge/output frame.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

/-- Canonical inclusion of one adjacent-state terminal component into any branch containing it. -/
noncomputable def nonautonomousFiniteCascadeTerminalComponentInclusion
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {j M : ℕ} (h : j + 1 ≤ M) :
    NonautonomousFiniteCascadeTerminalComponentField hfan j →ₐ[ℂ]
      NonautonomousFiniteCascadeBranchField hfan M := by
  let A := NonautonomousFiniteCascadeTerminalComponentField hfan j
  let B := NonautonomousFiniteCascadeBranchField hfan (j + 1)
  let T := NonautonomousFiniteCascadeBranchField hfan M
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (nonautonomousFiniteCascadeBranchInclusion hfan h).comp
    (IsScalarTower.toAlgHom ℂ A B)

@[simp] theorem nonautonomousFiniteCascadeTerminalComponentInclusion_input
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {j M : ℕ} (h : j + 1 ≤ M) :
    nonautonomousFiniteCascadeTerminalComponentInclusion hfan h
        (terminalLeadingStateInComponent hfan j) =
      nonautonomousFiniteCascadeStateInBranchField hfan M ⟨j, by omega⟩ := by
  apply Subtype.ext
  rfl

@[simp] theorem nonautonomousFiniteCascadeTerminalComponentInclusion_output
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {j M : ℕ} (h : j + 1 ≤ M) :
    nonautonomousFiniteCascadeTerminalComponentInclusion hfan h
        (nonautonomousFiniteCascadeTerminalOutputInComponent hfan j) =
      nonautonomousFiniteCascadeStateInBranchField hfan M ⟨j + 1, by omega⟩ := by
  apply Subtype.ext
  rfl

/-- Actual Wiman charge of one layer, embedded in any branch containing that layer. -/
noncomputable def nonautonomousFiniteCascadeWimanChargeInBranch
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {M : ℕ} (j : Fin M) : NonautonomousFiniteCascadeBranchField hfan M :=
  nonautonomousFiniteCascadeTerminalComponentInclusion hfan
      (Nat.succ_le_iff.mpr j.isLt)
    (nonautonomousFiniteCascadeTerminalChargedVelocityInComponent hfan j)

/-- Wiman charges commute with every canonical inclusion in the finite actual branch tower. -/
@[simp] theorem nonautonomousFiniteCascadeBranchInclusion_WimanCharge
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {N M : ℕ} (hNM : N ≤ M) (j : Fin N) :
    nonautonomousFiniteCascadeBranchInclusion hfan hNM
        (nonautonomousFiniteCascadeWimanChargeInBranch hfan j) =
      nonautonomousFiniteCascadeWimanChargeInBranch hfan
        ⟨j, lt_of_lt_of_le j.isLt hNM⟩ := by
  apply Subtype.ext
  rfl

/-- A state-coordinate derivation annihilates every strictly later Wiman charge. -/
theorem nonautonomousFiniteCascadeCoordinateDerivation_laterWimanCharge_eq_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j k : Fin M) (hjk : (j : ℕ) < (k : ℕ))
    (P : Derivation ℂ (NonautonomousFiniteCascadeBranchField hfan M)
      (NonautonomousFiniteCascadeBranchField hfan M))
    (hP : ∀ i, P (nonautonomousFiniteCascadeStateInBranchField hfan M i) =
      algebraMap ℂ _ (if (i : ℕ) = (j : ℕ) then 1 else 0)) :
    P (nonautonomousFiniteCascadeWimanChargeInBranch hfan k) = 0 := by
  classical
  have hkM : (k : ℕ) + 1 ≤ M := Nat.succ_le_iff.mpr k.isLt
  let A := NonautonomousFiniteCascadeTerminalComponentField hfan (k : ℕ)
  let B := NonautonomousFiniteCascadeBranchField hfan M
  let g := nonautonomousFiniteCascadeTerminalComponentInclusion hfan hkM
  let pairCoordinate : Fin 2 →
      NonautonomousFiniteCascadeTerminalPairField hfan (k : ℕ) := fun i =>
    ⟨nonautonomousFiniteCascadeTerminalStatePair hfan (k : ℕ) i,
      IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)⟩
  have hpairTop : IntermediateField.adjoin ℂ (Set.range pairCoordinate) = ⊤ := by
    simpa [pairCoordinate] using
      (adjoin_range_lift_eq_top
        (nonautonomousFiniteCascadeTerminalStatePair hfan (k : ℕ))
        (nonautonomousFiniteCascadeTerminalStatePair hfan (k : ℕ)) rfl)
  have h1k : ∀ i, i < (k : ℕ) + 1 → DifferentiallyAlgebraicOfOrder (f i) 1 :=
    fun i hi => h1 i (lt_of_lt_of_le hi hkM)
  letI : Algebra.IsAlgebraic
      (NonautonomousFiniteCascadeTerminalPairField hfan (k : ℕ)) A :=
    nonautonomousFiniteCascadeTerminalComponent_isAlgebraic hfan hall k h1k
  let D₀ : Derivation ℂ A A := 0
  let u := terminalLeadingStateInComponent hfan (k : ℕ)
  let y := nonautonomousFiniteCascadeTerminalOutputInComponent hfan (k : ℕ)
  have hgu : g u =
      nonautonomousFiniteCascadeStateInBranchField hfan M ⟨k, by omega⟩ := by
    exact nonautonomousFiniteCascadeTerminalComponentInclusion_input hfan hkM
  have hgy : g y =
      nonautonomousFiniteCascadeStateInBranchField hfan M ⟨(k : ℕ) + 1, by omega⟩ := by
    exact nonautonomousFiniteCascadeTerminalComponentInclusion_output hfan hkM
  have hmapPair : ∀ i : Fin 2,
      g (D₀ (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan (k : ℕ)) A
        (pairCoordinate i))) =
      P (g (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan (k : ℕ)) A
        (pairCoordinate i))) := by
    intro i
    fin_cases i
    · change g (D₀ u) = P (g u)
      rw [show D₀ u = 0 by rfl, map_zero, hgu, hP]
      simp
      omega
    · change g (D₀ y) = P (g y)
      rw [show D₀ y = 0 by rfl, map_zero, hgy, hP]
      simp
      omega
  have hintertwine : ∀ a : A, g (D₀ a) = P (g a) :=
    derivation_map_eq_of_isAlgebraic_tower_adjoin
      pairCoordinate hpairTop g D₀ P hmapPair
  let w := nonautonomousFiniteCascadeTerminalChargedVelocityInComponent hfan (k : ℕ)
  change P (g w) = 0
  rw [← hintertwine w]
  simp [D₀]

/-- A prescribed Kronecker derivation for a layer has nonzero response on that layer's actual
Wiman charge, inside any branch containing the layer. -/
theorem nonautonomousFiniteCascadeCoordinateDerivation_WimanCharge_ne_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j : Fin M)
    (P : Derivation ℂ (NonautonomousFiniteCascadeBranchField hfan M)
      (NonautonomousFiniteCascadeBranchField hfan M))
    (hP : ∀ i, P (nonautonomousFiniteCascadeStateInBranchField hfan M i) =
      algebraMap ℂ _ (if (i : ℕ) = (j : ℕ) then 1 else 0)) :
    P (nonautonomousFiniteCascadeWimanChargeInBranch hfan j) ≠ 0 := by
  classical
  let B := NonautonomousFiniteCascadeBranchField hfan M
  let state : Fin (M + 1) → B :=
    nonautonomousFiniteCascadeStateInBranchField hfan M
  have hjM : (j : ℕ) + 1 ≤ M := Nat.succ_le_iff.mpr j.isLt
  let g := nonautonomousFiniteCascadeTerminalComponentInclusion hfan hjM
  have h1j : ∀ k, k < (j : ℕ) + 1 → DifferentiallyAlgebraicOfOrder (f k) 1 :=
    fun k hk => h1 k (lt_of_lt_of_le hk hjM)
  obtain ⟨_M, _a, q, Nram, _hNram, _z₀, _R, _hR, _z, _hq, _phi, _Bv,
      _hslope, _hz₀eq, _hzeq, _hcharge, _hgrade, _hbiGrade, hdata⟩ :=
    exists_nonautonomousFiniteCascadeTerminal_normalizedVelocity_residueCoefficient
      hfan hall j h1j
  rcases hdata with ⟨_hBv, _hstate, _hxA, _hxB, _huA, _huB, _C, _hC, _hzNe,
    _hresU, _hresX, _hcoeff, _hext, _hlowerInj, _huPole, _hactualCharge,
    D, hDu, hDy, _hDtransport, hDnonzero⟩
  let u := terminalLeadingStateInComponent hfan (j : ℕ)
  let y := nonautonomousFiniteCascadeTerminalOutputInComponent hfan (j : ℕ)
  let w := nonautonomousFiniteCascadeTerminalChargedVelocityInComponent hfan (j : ℕ)
  let c : NonautonomousFiniteCascadeTerminalComponentField hfan (j : ℕ) :=
    algebraMap ℂ _ ((-((Nram * q : ℕ) : ℤ) : ℂ))
  have hDu' : D u = c * u := by
    simpa [u, c, terminalLeadingStateInComponent] using hDu
  have hDy' : D y = 0 := by
    simpa [y, nonautonomousFiniteCascadeTerminalOutputInComponent] using hDy
  have hDnonzero' : D w ≠ 0 := by
    simpa [w, nonautonomousFiniteCascadeTerminalChargedVelocityInComponent,
      nonautonomousFiniteCascadeTerminalVelocityInComponent,
      nonautonomousFiniteCascadeTerminalOutputInComponent,
      terminalLeadingStateInComponent] using hDnonzero
  let DL : Derivation ℂ B B := g (c * u) • P
  let pairCoordinate : Fin 2 →
      NonautonomousFiniteCascadeTerminalPairField hfan (j : ℕ) := fun i =>
    ⟨nonautonomousFiniteCascadeTerminalStatePair hfan (j : ℕ) i,
      IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)⟩
  have hpairTop : IntermediateField.adjoin ℂ (Set.range pairCoordinate) = ⊤ := by
    simpa [pairCoordinate] using
      (adjoin_range_lift_eq_top
        (nonautonomousFiniteCascadeTerminalStatePair hfan (j : ℕ))
        (nonautonomousFiniteCascadeTerminalStatePair hfan (j : ℕ)) rfl)
  letI : Algebra.IsAlgebraic
      (NonautonomousFiniteCascadeTerminalPairField hfan (j : ℕ))
      (NonautonomousFiniteCascadeTerminalComponentField hfan (j : ℕ)) :=
    nonautonomousFiniteCascadeTerminalComponent_isAlgebraic hfan hall j h1j
  have hgu : g u = state ⟨j, by omega⟩ := by
    exact nonautonomousFiniteCascadeTerminalComponentInclusion_input hfan hjM
  have hgy : g y = state ⟨(j : ℕ) + 1, by omega⟩ := by
    exact nonautonomousFiniteCascadeTerminalComponentInclusion_output hfan hjM
  have hmapPair : ∀ i : Fin 2,
      g (D (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan (j : ℕ))
        (NonautonomousFiniteCascadeTerminalComponentField hfan (j : ℕ))
        (pairCoordinate i))) =
      DL (g (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan (j : ℕ))
        (NonautonomousFiniteCascadeTerminalComponentField hfan (j : ℕ))
        (pairCoordinate i))) := by
    intro i
    fin_cases i
    · change g (D u) = DL (g u)
      change g (D u) = g (c * u) * P (g u)
      rw [hDu', map_mul, hgu, hP]
      simp
    · change g (D y) = DL (g y)
      change g (D y) = g (c * u) * P (g y)
      rw [hDy', map_zero, hgy, hP]
      simp
  have hintertwine : ∀ a :
      NonautonomousFiniteCascadeTerminalComponentField hfan (j : ℕ),
      g (D a) = DL (g a) :=
    derivation_map_eq_of_isAlgebraic_tower_adjoin
      pairCoordinate hpairTop g D DL hmapPair
  change P (g w) ≠ 0
  intro hzero
  apply hDnonzero'
  have hz : g (D w) = 0 := by
    rw [hintertwine w]
    simp [DL, hzero]
  exact g.injective (by simpa using hz)

/-- The actual Wiman-charge coordinates, followed by the literal terminal output. -/
noncomputable def nonautonomousFiniteCascadeWimanChargeOutputFrame
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (M : ℕ) : Fin (M + 1) → NonautonomousFiniteCascadeBranchField hfan M :=
  Fin.lastCases
    (nonautonomousFiniteCascadeStateInBranchField hfan M (Fin.last M))
    (fun j : Fin M => nonautonomousFiniteCascadeWimanChargeInBranch hfan j)

/-- A simultaneous Kronecker frame of derivations exists on every actual finite branch field. -/
theorem exists_nonautonomousFiniteCascadeBranchCoordinateDerivations
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ) :
    let B := NonautonomousFiniteCascadeBranchField hfan M
    let state : Fin (M + 1) → B :=
      nonautonomousFiniteCascadeStateInBranchField hfan M
    ∃ P : Fin (M + 1) → Derivation ℂ B B,
      ∀ i j, P i (state j) = algebraMap ℂ B (if (j : ℕ) = (i : ℕ) then 1 else 0) := by
  classical
  let B := NonautonomousFiniteCascadeBranchField hfan M
  let state : Fin (M + 1) → B :=
    nonautonomousFiniteCascadeStateInBranchField hfan M
  have hAI : AlgebraicIndependent ℂ state :=
    algebraicIndependent_nonautonomousFiniteCascadeStateInBranchField hfan hall M
  choose P hP using fun i : Fin (M + 1) =>
    exists_derivation_prescribed hAI (fun j => if (j : ℕ) = (i : ℕ) then 1 else 0)
  exact ⟨P, hP⟩

/-- The actual Wiman-charge/terminal-output frame is algebraically independent.  The proof uses
one global branch-coordinate family; its Jacobian is lower triangular with nonzero diagonal. -/
theorem algebraicIndependent_nonautonomousFiniteCascadeWimanChargeOutputFrame
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1) :
    AlgebraicIndependent ℂ (nonautonomousFiniteCascadeWimanChargeOutputFrame hfan M) := by
  classical
  let B := NonautonomousFiniteCascadeBranchField hfan M
  let state : Fin (M + 1) → B :=
    nonautonomousFiniteCascadeStateInBranchField hfan M
  let frame : Fin (M + 1) → B :=
    nonautonomousFiniteCascadeWimanChargeOutputFrame hfan M
  obtain ⟨P, hP⟩ :=
    exists_nonautonomousFiniteCascadeBranchCoordinateDerivations hfan hall M
  let J : Matrix (Fin (M + 1)) (Fin (M + 1)) B :=
    Matrix.of fun i j => P i (frame j)
  have htri : J.BlockTriangular (fun i : Fin (M + 1) => OrderDual.toDual i) := by
    intro i j
    refine Fin.lastCases
      (motive := fun j =>
        OrderDual.toDual j < OrderDual.toDual i → J i j = 0)
      ?_ (fun k : Fin M => ?_) j
    · intro hij
      have hij' : (i : ℕ) < ((Fin.last M : Fin (M + 1)) : ℕ) :=
        OrderDual.toDual_lt_toDual.mp hij
      simp only [J, Matrix.of_apply, frame,
        nonautonomousFiniteCascadeWimanChargeOutputFrame, Fin.lastCases_last]
      rw [hP]
      simp
      omega
    · intro hij
      have hij' : (i : ℕ) < ((k.castSucc : Fin (M + 1)) : ℕ) :=
        OrderDual.toDual_lt_toDual.mp hij
      let i' : Fin M := ⟨i, by omega⟩
      simp only [J, Matrix.of_apply, frame,
        nonautonomousFiniteCascadeWimanChargeOutputFrame, Fin.lastCases_castSucc]
      apply nonautonomousFiniteCascadeCoordinateDerivation_laterWimanCharge_eq_zero
        hfan hall M h1 i' k
      · change (i : ℕ) < (k : ℕ)
        exact hij'
      · intro s
        simpa [i'] using hP i s
  have hdiag : ∀ i : Fin (M + 1), J i i ≠ 0 := by
    intro i
    refine Fin.lastCases ?_ (fun j : Fin M => ?_) i
    · simp only [J, Matrix.of_apply, frame,
        nonautonomousFiniteCascadeWimanChargeOutputFrame, Fin.lastCases_last]
      rw [hP]
      simp
    · simp only [J, Matrix.of_apply, frame,
        nonautonomousFiniteCascadeWimanChargeOutputFrame, Fin.lastCases_castSucc]
      apply nonautonomousFiniteCascadeCoordinateDerivation_WimanCharge_ne_zero
        hfan hall M h1 j (P j.castSucc)
      intro s
      convert hP j.castSucc s using 1
      all_goals simp
  have hdet : J.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular _ htri]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i
  refine algebraicIndependent_of_domain_jacobian (K := ℂ) frame
    (fun i => fun x => P i x) ?_ ?_ ?_ J hdet ?_
  · intro i a b
    exact map_add (P i) a b
  · intro i a b
    simpa only [smul_eq_mul] using (P i).leibniz a b
  · intro i c
    exact (P i).map_algebraMap c
  · intro i j
    rfl

/-- The clock-anchored Wiman frame replaces the first charge by the rational clock, retains every
strictly positive-layer charge, and ends with the literal terminal output. -/
noncomputable def nonautonomousFiniteCascadeClockWimanOutputFrame
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (M : ℕ) (i : Fin (M + 1)) : NonautonomousFiniteCascadeBranchField hfan M :=
  if hi₀ : (i : ℕ) = 0 then
    nonautonomousFiniteCascadeStateInBranchField hfan M ⟨0, by omega⟩
  else if hiM : (i : ℕ) = M then
    nonautonomousFiniteCascadeStateInBranchField hfan M (Fin.last M)
  else
    nonautonomousFiniteCascadeWimanChargeInBranch hfan ⟨i, by omega⟩

/-- The clock, every positive-layer actual Wiman charge, and the terminal output form an exact
algebraically independent coordinate frame over the complex constants. -/
theorem algebraicIndependent_nonautonomousFiniteCascadeClockWimanOutputFrame
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1) :
    AlgebraicIndependent ℂ (nonautonomousFiniteCascadeClockWimanOutputFrame hfan M) := by
  classical
  let B := NonautonomousFiniteCascadeBranchField hfan M
  let state : Fin (M + 1) → B :=
    nonautonomousFiniteCascadeStateInBranchField hfan M
  let frame : Fin (M + 1) → B :=
    nonautonomousFiniteCascadeClockWimanOutputFrame hfan M
  obtain ⟨P, hP⟩ :=
    exists_nonautonomousFiniteCascadeBranchCoordinateDerivations hfan hall M
  let J : Matrix (Fin (M + 1)) (Fin (M + 1)) B :=
    Matrix.of fun i j => P i (frame j)
  have htri : J.BlockTriangular (fun i : Fin (M + 1) => OrderDual.toDual i) := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := OrderDual.toDual_lt_toDual.mp hij
    by_cases hj₀ : (j : ℕ) = 0
    · omega
    by_cases hjM : (j : ℕ) = M
    · simp only [J, Matrix.of_apply, frame,
        nonautonomousFiniteCascadeClockWimanOutputFrame, hj₀, hjM, dite_false, dite_true]
      rw [hP]
      simp
      omega
    · let i' : Fin M := ⟨i, by omega⟩
      let j' : Fin M := ⟨j, by omega⟩
      simp only [J, Matrix.of_apply, frame,
        nonautonomousFiniteCascadeClockWimanOutputFrame, hj₀, hjM, dite_false]
      apply nonautonomousFiniteCascadeCoordinateDerivation_laterWimanCharge_eq_zero
        hfan hall M h1 i' j'
      · exact hij'
      · intro s
        simpa [i'] using hP i s
  have hdiag : ∀ i : Fin (M + 1), J i i ≠ 0 := by
    intro i
    by_cases hi₀ : (i : ℕ) = 0
    · simp only [J, Matrix.of_apply, frame,
        nonautonomousFiniteCascadeClockWimanOutputFrame, hi₀, dite_true]
      rw [hP]
      simp
    by_cases hiM : (i : ℕ) = M
    · simp only [J, Matrix.of_apply, frame,
        nonautonomousFiniteCascadeClockWimanOutputFrame, hi₀, hiM, dite_false, dite_true]
      rw [hP]
      simp
      exact hiM
    · let i' : Fin M := ⟨i, by omega⟩
      simp only [J, Matrix.of_apply, frame,
        nonautonomousFiniteCascadeClockWimanOutputFrame, hi₀, hiM, dite_false]
      apply nonautonomousFiniteCascadeCoordinateDerivation_WimanCharge_ne_zero
        hfan hall M h1 i' (P i)
      intro s
      simpa [i'] using hP i s
  have hdet : J.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular _ htri]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i
  refine algebraicIndependent_of_domain_jacobian (K := ℂ) frame
    (fun i => fun x => P i x) ?_ ?_ ?_ J hdet ?_
  · intro i a b
    exact map_add (P i) a b
  · intro i a b
    simpa only [smul_eq_mul] using (P i).leibniz a b
  · intro i c
    exact (P i).map_algebraMap c
  · intro i j
    rfl

/-- The finite actual branch field is algebraic over its Wiman-charge/terminal-output frame. -/
theorem nonautonomousFiniteCascadeBranchField_isAlgebraic_WimanChargeOutputFrame
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin ℂ
        (Set.range (nonautonomousFiniteCascadeWimanChargeOutputFrame hfan M)))
      (NonautonomousFiniteCascadeBranchField hfan M) := by
  let E := NonautonomousRamifiedCascadeStateField hfan M
  let B := NonautonomousFiniteCascadeBranchField hfan M
  let stateE : Fin (M + 1) → E :=
    nonautonomousCascadeStateFamilyInStateField hfan M
  have hstateE : AlgebraicIndependent ℂ stateE :=
    algebraicIndependent_nonautonomousCascadeStateFamilyInStateField hfan hall M
  have hstateBasis : IsTranscendenceBasis ℂ stateE := by
    apply hstateE.isTranscendenceBasis_iff_isAlgebraic.mpr
    constructor
    intro a
    apply GaloisForLFunctions.isAlgebraic_algebraAdjoin_of_mem_intermediateField_adjoin
    rw [adjoin_range_nonautonomousCascadeStateFamilyInStateField_eq_top hfan M]
    trivial
  have hEtr : Algebra.trdeg ℂ E = (M + 1 : Cardinal) := by
    simpa [E] using hstateBasis.cardinalMk_eq_trdeg.symm
  have hEB : E ≤ B := by
    intro x hx
    exact IntermediateField.algebraMap_mem
      (NonautonomousFiniteCascadeBranchFieldOverState hfan M) ⟨x, hx⟩
  letI : Algebra E B := (IntermediateField.inclusion hEB).toRingHom.toAlgebra
  letI : IsScalarTower ℂ E B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional E B :=
    finiteDimensional_nonautonomousFiniteCascadeBranchFieldOverState hfan hall h1
  letI : Algebra.IsAlgebraic E B := Algebra.IsAlgebraic.of_finite E B
  have hzero : Algebra.trdeg E B = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have hsum := trdeg_add_eq ℂ E (A := B)
  have hBtr : Algebra.trdeg ℂ B = (M + 1 : Cardinal) := by
    rw [hEtr, hzero, add_zero] at hsum
    exact hsum.symm
  exact isAlgebraic_adjoin_of_algebraicIndependent_fin_of_trdeg_eq
    (nonautonomousFiniteCascadeWimanChargeOutputFrame hfan M)
    (algebraicIndependent_nonautonomousFiniteCascadeWimanChargeOutputFrame
      hfan hall M h1)
    (by simpa [B] using hBtr)

/-- The finite actual branch field is algebraic over its literal full state frame. -/
theorem nonautonomousFiniteCascadeBranchField_isAlgebraic_stateFrame
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin ℂ
        (Set.range (nonautonomousFiniteCascadeStateInBranchField hfan M)))
      (NonautonomousFiniteCascadeBranchField hfan M) := by
  letI : Algebra.IsAlgebraic
      (IntermediateField.adjoin ℂ
        (Set.range (nonautonomousFiniteCascadeWimanChargeOutputFrame hfan M)))
      (NonautonomousFiniteCascadeBranchField hfan M) :=
    nonautonomousFiniteCascadeBranchField_isAlgebraic_WimanChargeOutputFrame
      hfan hall M h1
  exact isAlgebraic_adjoin_of_algebraicIndependent_fin
    (nonautonomousFiniteCascadeWimanChargeOutputFrame hfan M)
    (nonautonomousFiniteCascadeStateInBranchField hfan M)
    (algebraicIndependent_nonautonomousFiniteCascadeWimanChargeOutputFrame
      hfan hall M h1)
    (algebraicIndependent_nonautonomousFiniteCascadeStateInBranchField hfan hall M)

/-- Every derivation of an actual finite branch is the state-coordinate directional derivative
with its literal values on the state frame as coefficients. -/
theorem nonautonomousFiniteCascadeDerivation_coordinate_decomposition
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1)
    (D : Derivation ℂ (NonautonomousFiniteCascadeBranchField hfan M)
      (NonautonomousFiniteCascadeBranchField hfan M))
    (P : Fin (M + 1) → Derivation ℂ
      (NonautonomousFiniteCascadeBranchField hfan M)
      (NonautonomousFiniteCascadeBranchField hfan M))
    (hP : ∀ i j, P i (nonautonomousFiniteCascadeStateInBranchField hfan M j) =
      algebraMap ℂ _ (if (j : ℕ) = (i : ℕ) then 1 else 0)) :
    ∀ a, D a = ∑ i, D (nonautonomousFiniteCascadeStateInBranchField hfan M i) • P i a := by
  classical
  let B := NonautonomousFiniteCascadeBranchField hfan M
  let state : Fin (M + 1) → B :=
    nonautonomousFiniteCascadeStateInBranchField hfan M
  let Q : Derivation ℂ B B :=
    ∑ i, D (state i) • P i
  letI : Algebra.IsAlgebraic
      (IntermediateField.adjoin ℂ (Set.range state)) B :=
    nonautonomousFiniteCascadeBranchField_isAlgebraic_stateFrame hfan hall M h1
  have hsumApply (S : Finset (Fin (M + 1))) (a : B) :
      (∑ i ∈ S, D (state i) • P i) a =
        ∑ i ∈ S, D (state i) * P i a := by
    induction S using Finset.induction with
    | empty => simp
    | @insert i S hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          Derivation.add_apply, Derivation.smul_apply, ih]
        simp only [smul_eq_mul]
  have hQapply : ∀ a : B, Q a = ∑ i, D (state i) * P i a := by
    intro a
    simpa [Q] using hsumApply Finset.univ a
  have hDQ : ∀ a : B, (AlgHom.id ℂ B) (D a) = Q ((AlgHom.id ℂ B) a) := by
    apply derivation_map_eq_of_isAlgebraic_adjoin state (AlgHom.id ℂ B) D Q
    intro j
    simp only [AlgHom.id_apply]
    change D (state j) = Q (state j)
    rw [hQapply]
    rw [Finset.sum_eq_single j]
    · rw [hP]
      simp
    · intro i _ hij
      rw [hP]
      have hval : (j : ℕ) ≠ (i : ℕ) := fun h => hij (Fin.ext h.symm)
      simp [hval]
    · simp
  intro a
  have h := hDQ a
  rw [hQapply] at h
  simpa only [AlgHom.id_apply, smul_eq_mul, state] using h

/-- A coordinate derivation strictly above a lower branch annihilates that complete embedded
algebraic branch, not merely its state generators. -/
theorem nonautonomousFiniteCascadeCoordinateDerivation_lowerBranch_eq_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N M : ℕ}
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j : Fin (M + 1)) (hNj : N < (j : ℕ))
    (P : Derivation ℂ (NonautonomousFiniteCascadeBranchField hfan M)
      (NonautonomousFiniteCascadeBranchField hfan M))
    (hP : ∀ i, P (nonautonomousFiniteCascadeStateInBranchField hfan M i) =
      algebraMap ℂ _ (if (i : ℕ) = (j : ℕ) then 1 else 0))
    (x : NonautonomousFiniteCascadeBranchField hfan N) :
    P (nonautonomousFiniteCascadeBranchInclusion hfan (by omega : N ≤ M) x) = 0 := by
  classical
  let A := NonautonomousFiniteCascadeBranchField hfan N
  let B := NonautonomousFiniteCascadeBranchField hfan M
  let state : Fin (N + 1) → A :=
    nonautonomousFiniteCascadeStateInBranchField hfan N
  let g : A →ₐ[ℂ] B := nonautonomousFiniteCascadeBranchInclusion hfan (by omega : N ≤ M)
  let D₀ : Derivation ℂ A A := 0
  letI : Algebra.IsAlgebraic
      (IntermediateField.adjoin ℂ (Set.range state)) A :=
    nonautonomousFiniteCascadeBranchField_isAlgebraic_stateFrame
      hfan hall N (fun k hk => h1 k (by omega))
  have hmap : ∀ i, g (D₀ (state i)) = P (g (state i)) := by
    intro i
    rw [show D₀ (state i) = 0 by rfl, map_zero]
    have hg : g (state i) =
        nonautonomousFiniteCascadeStateInBranchField hfan M ⟨i, by omega⟩ := by
      exact nonautonomousFiniteCascadeBranchInclusion_state hfan (by omega) i
    rw [hg, hP]
    simp
    omega
  have hintertwine : ∀ a : A, g (D₀ a) = P (g a) :=
    derivation_map_eq_of_isAlgebraic_adjoin state g D₀ P hmap
  rw [← hintertwine x]
  simp [D₀]

/-- A state-coordinate derivation strictly above a Wiman layer's successor state annihilates
that charge.  Together with `nonautonomousFiniteCascadeCoordinateDerivation_laterWimanCharge_eq_zero`,
this says the coordinate support of layer `k` is contained in the adjacent pair `k, k + 1`. -/
theorem nonautonomousFiniteCascadeCoordinateDerivation_aboveWimanCharge_eq_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j : Fin (M + 1)) (k : Fin M) (hkj : (k : ℕ) + 1 < (j : ℕ))
    (P : Derivation ℂ (NonautonomousFiniteCascadeBranchField hfan M)
      (NonautonomousFiniteCascadeBranchField hfan M))
    (hP : ∀ i, P (nonautonomousFiniteCascadeStateInBranchField hfan M i) =
      algebraMap ℂ _ (if (i : ℕ) = (j : ℕ) then 1 else 0)) :
    P (nonautonomousFiniteCascadeWimanChargeInBranch hfan k) = 0 := by
  let k' : Fin ((k : ℕ) + 1) := Fin.last (k : ℕ)
  have hkM : (k : ℕ) + 1 ≤ M := Nat.succ_le_iff.mpr k.isLt
  rw [← nonautonomousFiniteCascadeBranchInclusion_WimanCharge hfan hkM k']
  exact nonautonomousFiniteCascadeCoordinateDerivation_lowerBranch_eq_zero
    hfan hall h1 j hkj P hP
      (nonautonomousFiniteCascadeWimanChargeInBranch hfan k')

/-- Exact adjacent-coordinate support of every actual Wiman charge. -/
theorem nonautonomousFiniteCascadeCoordinateDerivation_WimanCharge_eq_zero_of_not_adjacent
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j : Fin (M + 1)) (k : Fin M)
    (hjk : (j : ℕ) ≠ (k : ℕ)) (hjks : (j : ℕ) ≠ (k : ℕ) + 1)
    (P : Derivation ℂ (NonautonomousFiniteCascadeBranchField hfan M)
      (NonautonomousFiniteCascadeBranchField hfan M))
    (hP : ∀ i, P (nonautonomousFiniteCascadeStateInBranchField hfan M i) =
      algebraMap ℂ _ (if (i : ℕ) = (j : ℕ) then 1 else 0)) :
    P (nonautonomousFiniteCascadeWimanChargeInBranch hfan k) = 0 := by
  by_cases hjklt : (j : ℕ) < (k : ℕ)
  · let j' : Fin M := ⟨j, by omega⟩
    apply nonautonomousFiniteCascadeCoordinateDerivation_laterWimanCharge_eq_zero
      hfan hall M h1 j' k
    · exact hjklt
    · intro i
      simpa [j'] using hP i
  · apply nonautonomousFiniteCascadeCoordinateDerivation_aboveWimanCharge_eq_zero
      hfan hall M h1 j k
    · omega
    · exact hP

/-- Exact bidiagonal chain rule for the time derivative of an actual Wiman charge: only the
layer's input and output state velocities can occur. -/
theorem nonautonomousFiniteCascadeDerivation_WimanCharge_bidiagonal
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1)
    (D : Derivation ℂ (NonautonomousFiniteCascadeBranchField hfan M)
      (NonautonomousFiniteCascadeBranchField hfan M))
    (P : Fin (M + 1) → Derivation ℂ
      (NonautonomousFiniteCascadeBranchField hfan M)
      (NonautonomousFiniteCascadeBranchField hfan M))
    (hP : ∀ i j, P i (nonautonomousFiniteCascadeStateInBranchField hfan M j) =
      algebraMap ℂ _ (if (j : ℕ) = (i : ℕ) then 1 else 0))
    (k : Fin M) :
    let k₀ : Fin (M + 1) := ⟨k, by omega⟩
    let k₁ : Fin (M + 1) := ⟨(k : ℕ) + 1, by omega⟩
    let w := nonautonomousFiniteCascadeWimanChargeInBranch hfan k
    D w =
      D (nonautonomousFiniteCascadeStateInBranchField hfan M k₀) * P k₀ w +
      D (nonautonomousFiniteCascadeStateInBranchField hfan M k₁) * P k₁ w := by
  classical
  let k₀ : Fin (M + 1) := ⟨k, by omega⟩
  let k₁ : Fin (M + 1) := ⟨(k : ℕ) + 1, by omega⟩
  let w := nonautonomousFiniteCascadeWimanChargeInBranch hfan k
  have hkne : k₀ ≠ k₁ := by
    intro h
    have := Fin.ext_iff.mp h
    simp [k₀, k₁] at this
  have hdecomp :=
    nonautonomousFiniteCascadeDerivation_coordinate_decomposition
      hfan hall M h1 D P hP w
  rw [show D w = ∑ i, D (nonautonomousFiniteCascadeStateInBranchField hfan M i) *
      P i w by simpa only [smul_eq_mul] using hdecomp]
  calc
    ∑ i, D (nonautonomousFiniteCascadeStateInBranchField hfan M i) * P i w =
        ∑ i ∈ ({k₀, k₁} : Finset (Fin (M + 1))),
          D (nonautonomousFiniteCascadeStateInBranchField hfan M i) * P i w := by
      symm
      apply Finset.sum_subset (by simp)
      intro i _ hi
      have hi₀ : (i : ℕ) ≠ (k : ℕ) := by
        intro hik
        apply hi
        have : i = k₀ := Fin.ext hik
        simp [this]
      have hi₁ : (i : ℕ) ≠ (k : ℕ) + 1 := by
        intro hik
        apply hi
        have : i = k₁ := Fin.ext hik
        simp [this]
      rw [nonautonomousFiniteCascadeCoordinateDerivation_WimanCharge_eq_zero_of_not_adjacent
        hfan hall M h1 i k hi₀ hi₁ (P i) (hP i)]
      simp
    _ = D (nonautonomousFiniteCascadeStateInBranchField hfan M k₀) * P k₀ w +
        D (nonautonomousFiniteCascadeStateInBranchField hfan M k₁) * P k₁ w := by
      simp [hkne]

end

end GaloisForLFunctions.HTGeometry
