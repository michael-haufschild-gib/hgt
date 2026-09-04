import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeTerminalOutputCharge
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion
import GaloisForLFunctions.HTGeometry.BigradedCorank

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

/-- Algebraic independence detected after reduction modulo a valuation maximal ideal already
holds for the integral lifts in the ambient field. -/
theorem algebraicIndependent_of_valuationSubring_residue
    {C K ι : Type*} [Field C] [Field K] [Algebra C K]
    (B : ValuationSubring K) [Algebra C B]
    [Algebra C (IsLocalRing.ResidueField B)]
    (hcB : ∀ c : C, ((algebraMap C B c : B) : K) = algebraMap C K c)
    (hcR : ∀ c : C, IsLocalRing.residue B (algebraMap C B c) =
      algebraMap C (IsLocalRing.ResidueField B) c)
    (u : ι → B)
    (hres : AlgebraicIndependent C
      (fun i => IsLocalRing.residue B (u i))) :
    AlgebraicIndependent C (fun i => (u i : K)) := by
  let ρ : B →ₐ[C] IsLocalRing.ResidueField B :=
    { IsLocalRing.residue B with
      commutes' := hcR }
  let inclusion : B →ₐ[C] K :=
    { B.toSubring.subtype with
      commutes' := hcB }
  have hB : AlgebraicIndependent C u := by
    apply AlgebraicIndependent.of_comp ρ
    exact hres
  exact hB.map' (f := inclusion) fun x y h => Subtype.ext h

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

@[simp] theorem nonautonomousFiniteCascadeTerminalComponentInclusion_velocity
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {j M : ℕ} (h : j + 1 ≤ M) :
    nonautonomousFiniteCascadeTerminalComponentInclusion hfan h
        (nonautonomousFiniteCascadeTerminalVelocityInComponent hfan j) =
      nonautonomousFiniteCascadeBranchInclusion hfan h
        (nonautonomousFiniteCascadeTerminalVelocitySucc hfan j) := by
  apply Subtype.ext
  rfl

/-- Actual Wiman charge of one layer, embedded in any branch containing that layer. -/
noncomputable def nonautonomousFiniteCascadeWimanChargeInBranch
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {M : ℕ} (j : Fin M) : NonautonomousFiniteCascadeBranchField hfan M :=
  nonautonomousFiniteCascadeTerminalComponentInclusion hfan
      (Nat.succ_le_iff.mpr j.isLt)
    (nonautonomousFiniteCascadeTerminalChargedVelocityInComponent hfan j)

/-- Every literal cascade state is nonzero in its actual finite branch field. -/
theorem nonautonomousFiniteCascadeStateInBranchField_ne_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (i : Fin (M + 1)) :
    nonautonomousFiniteCascadeStateInBranchField hfan M i ≠ 0 := by
  have hAI :=
    algebraicIndependent_nonautonomousFiniteCascadeStateInBranchField hfan hall M
  exact hAI.ne_zero i

/-- Literal logarithmic velocity of one actual state inside the complete finite branch field. -/
noncomputable def nonautonomousFiniteCascadeLogarithmicRate
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (M : ℕ) (i : Fin (M + 1)) : NonautonomousFiniteCascadeBranchField hfan M :=
  nonautonomousFiniteCascadeDerivativeInBranchField hfan M i /
    nonautonomousFiniteCascadeStateInBranchField hfan M i

/-- Every actual logarithmic rate is nonzero. -/
theorem nonautonomousFiniteCascadeLogarithmicRate_ne_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (i : Fin (M + 1)) :
    nonautonomousFiniteCascadeLogarithmicRate hfan M i ≠ 0 :=
  div_ne_zero
    (nonautonomousFiniteCascadeDerivativeInBranchField_ne_zero hfan hall M i)
    (nonautonomousFiniteCascadeStateInBranchField_ne_zero hfan hall M i)

/-- The logarithmic rate of the clock is its reciprocal. -/
theorem nonautonomousFiniteCascadeLogarithmicRate_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (M : ℕ) :
    nonautonomousFiniteCascadeLogarithmicRate hfan M ⟨0, by omega⟩ =
      (nonautonomousFiniteCascadeStateInBranchField hfan M ⟨0, by omega⟩)⁻¹ := by
  have hd : nonautonomousFiniteCascadeDerivativeInBranchField hfan M ⟨0, by omega⟩ = 1 := by
    apply Subtype.ext
    simpa using cascadeMeroDeriv_zero hfan
  rw [nonautonomousFiniteCascadeLogarithmicRate, hd, one_div]

/-- Exact terminal-linear law for every actual cascade state. -/
theorem nonautonomousFiniteCascadeDerivation_state_eq_logarithmicRate_mul
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {M : ℕ}
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1)
    (i : Fin (M + 1)) :
    nonautonomousFiniteCascadeDerivation hfan hall h1
        (nonautonomousFiniteCascadeStateInBranchField hfan M i) =
      nonautonomousFiniteCascadeLogarithmicRate hfan M i *
        nonautonomousFiniteCascadeStateInBranchField hfan M i := by
  rw [nonautonomousFiniteCascadeDerivation_state]
  simp only [nonautonomousFiniteCascadeLogarithmicRate]
  field_simp [nonautonomousFiniteCascadeStateInBranchField_ne_zero hfan hall M i]

/-- A literal Wiman charge is exactly the adjacent quotient of actual state and derivative
ratios. -/
theorem nonautonomousFiniteCascadeWimanChargeInBranch_eq
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (M : ℕ) (k : Fin M) :
    nonautonomousFiniteCascadeWimanChargeInBranch hfan k =
      nonautonomousFiniteCascadeStateInBranchField hfan M ⟨k, by omega⟩ *
        (nonautonomousFiniteCascadeDerivativeInBranchField hfan M
              ⟨(k : ℕ) + 1, by omega⟩ /
          nonautonomousFiniteCascadeDerivativeInBranchField hfan M ⟨k, by omega⟩ /
          nonautonomousFiniteCascadeStateInBranchField hfan M
            ⟨(k : ℕ) + 1, by omega⟩) := by
  have hkM : (k : ℕ) + 1 ≤ M := Nat.succ_le_iff.mpr k.isLt
  have hv :
      nonautonomousFiniteCascadeBranchInclusion hfan hkM
          (nonautonomousFiniteCascadeTerminalVelocitySucc hfan k) =
        nonautonomousFiniteCascadeDerivativeInBranchField hfan M
              ⟨(k : ℕ) + 1, by omega⟩ /
          nonautonomousFiniteCascadeDerivativeInBranchField hfan M ⟨k, by omega⟩ := by
    simp only [nonautonomousFiniteCascadeTerminalVelocitySucc,
      nonautonomousFiniteCascadeVelocityInBranchField, map_div₀,
      nonautonomousFiniteCascadeBranchInclusion_derivative]
    congr 2
  rw [nonautonomousFiniteCascadeWimanChargeInBranch,
    nonautonomousFiniteCascadeTerminalChargedVelocityInComponent,
    map_mul, map_div₀,
    nonautonomousFiniteCascadeTerminalComponentInclusion_input,
    nonautonomousFiniteCascadeTerminalComponentInclusion_output,
    nonautonomousFiniteCascadeTerminalComponentInclusion_velocity, hv]

/-- Every literal Wiman charge is nonzero on the actual analytic cascade component. -/
theorem nonautonomousFiniteCascadeWimanChargeInBranch_ne_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ) (k : Fin M) :
    nonautonomousFiniteCascadeWimanChargeInBranch hfan k ≠ 0 := by
  rw [nonautonomousFiniteCascadeWimanChargeInBranch_eq]
  exact mul_ne_zero
    (nonautonomousFiniteCascadeStateInBranchField_ne_zero hfan hall M ⟨k, by omega⟩)
    (div_ne_zero
      (div_ne_zero
        (nonautonomousFiniteCascadeDerivativeInBranchField_ne_zero hfan hall M
          ⟨(k : ℕ) + 1, by omega⟩)
        (nonautonomousFiniteCascadeDerivativeInBranchField_ne_zero hfan hall M
          ⟨k, by omega⟩))
      (nonautonomousFiniteCascadeStateInBranchField_ne_zero hfan hall M
        ⟨(k : ℕ) + 1, by omega⟩))

/-- Exact actual-branch recurrence: every layer multiplies the preceding logarithmic rate by
its literal Wiman charge. -/
theorem nonautonomousFiniteCascadeLogarithmicRate_succ
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (k : Fin M) :
    nonautonomousFiniteCascadeLogarithmicRate hfan M
        ⟨(k : ℕ) + 1, by omega⟩ =
      nonautonomousFiniteCascadeLogarithmicRate hfan M ⟨k, by omega⟩ *
        nonautonomousFiniteCascadeWimanChargeInBranch hfan k := by
  rw [nonautonomousFiniteCascadeWimanChargeInBranch_eq]
  simp only [nonautonomousFiniteCascadeLogarithmicRate]
  field_simp [
    nonautonomousFiniteCascadeStateInBranchField_ne_zero hfan hall M ⟨k, by omega⟩,
    nonautonomousFiniteCascadeStateInBranchField_ne_zero hfan hall M
      ⟨(k : ℕ) + 1, by omega⟩,
    nonautonomousFiniteCascadeDerivativeInBranchField_ne_zero hfan hall M
      ⟨k, by omega⟩]

/-- Totalized natural-number indexing of actual Wiman charges, used only to state finite prefix
products without dependent casts. -/
noncomputable def nonautonomousFiniteCascadeWimanChargeAt
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (M k : ℕ) : NonautonomousFiniteCascadeBranchField hfan M :=
  if hk : k < M then nonautonomousFiniteCascadeWimanChargeInBranch hfan ⟨k, hk⟩ else 1

@[simp] theorem nonautonomousFiniteCascadeWimanChargeAt_of_lt
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (M k : ℕ) (hk : k < M) :
    nonautonomousFiniteCascadeWimanChargeAt hfan M k =
      nonautonomousFiniteCascadeWimanChargeInBranch hfan ⟨k, hk⟩ := by
  simp [nonautonomousFiniteCascadeWimanChargeAt, hk]

/-- Every actual logarithmic rate is the reciprocal clock times the product of preceding literal
Wiman charges. -/
theorem nonautonomousFiniteCascadeLogarithmicRate_prefix_product
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M n : ℕ) (hn : n ≤ M) :
    nonautonomousFiniteCascadeLogarithmicRate hfan M ⟨n, by omega⟩ =
      (nonautonomousFiniteCascadeStateInBranchField hfan M ⟨0, by omega⟩)⁻¹ *
        ∏ k ∈ Finset.range n,
          nonautonomousFiniteCascadeWimanChargeAt hfan M k := by
  induction n with
  | zero =>
      simpa only [Finset.prod_range_zero, Finset.prod_empty, mul_one] using
        nonautonomousFiniteCascadeLogarithmicRate_zero hfan M
  | succ n ih =>
      rw [nonautonomousFiniteCascadeLogarithmicRate_succ hfan hall M ⟨n, by omega⟩,
        ih (by omega), Finset.prod_range_succ]
      simp [nonautonomousFiniteCascadeWimanChargeAt, show n < M by omega]
      ring

/-- Terminal logarithmic derivative is the reciprocal clock times all actual Wiman charges. -/
theorem nonautonomousFiniteCascadeLogarithmicRate_terminal_product
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ) :
    nonautonomousFiniteCascadeLogarithmicRate hfan M (Fin.last M) =
      (nonautonomousFiniteCascadeStateInBranchField hfan M ⟨0, by omega⟩)⁻¹ *
        ∏ k ∈ Finset.range M,
          nonautonomousFiniteCascadeWimanChargeAt hfan M k := by
  convert nonautonomousFiniteCascadeLogarithmicRate_prefix_product
    hfan hall M M le_rfl using 1
  congr 1

/-- Exact terminal-state evolution in the actual branch, expressed in the complete literal Wiman
charge frame. -/
theorem nonautonomousFiniteCascadeDerivation_terminalState_eq_chargeProduct_mul
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1) :
    nonautonomousFiniteCascadeDerivation hfan hall h1
        (nonautonomousFiniteCascadeStateInBranchField hfan M (Fin.last M)) =
      ((nonautonomousFiniteCascadeStateInBranchField hfan M ⟨0, by omega⟩)⁻¹ *
          ∏ k ∈ Finset.range M,
            nonautonomousFiniteCascadeWimanChargeAt hfan M k) *
        nonautonomousFiniteCascadeStateInBranchField hfan M (Fin.last M) := by
  rw [nonautonomousFiniteCascadeDerivation_state_eq_logarithmicRate_mul
      hfan hall h1 (Fin.last M),
    nonautonomousFiniteCascadeLogarithmicRate_terminal_product hfan hall M]

/-- Exact terminal factorization adapted to the Wiman valuation: the derivative of the new
terminal state is the retained lower terminal derivative times the normalized terminal velocity
unit times the new state pole. -/
theorem nonautonomousFiniteCascadeDerivation_terminalStateSucc_eq_lowerDerivative_mul_normalizedVelocity_mul
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    nonautonomousFiniteCascadeDerivation hfan hall h1
        (nonautonomousFiniteCascadeTerminalStateSucc hfan N) =
      nonautonomousFiniteCascadeBranchInclusionSucc hfan N
          (nonautonomousFiniteCascadeDerivativeInBranchField hfan N (Fin.last N)) *
        (nonautonomousFiniteCascadeTerminalVelocitySucc hfan N /
          nonautonomousFiniteCascadeTerminalStateSucc hfan N) *
        nonautonomousFiniteCascadeTerminalStateSucc hfan N := by
  rw [nonautonomousFiniteCascadeTerminalStateSucc,
    nonautonomousFiniteCascadeDerivation_state,
    ← nonautonomousFiniteCascadeTerminalDerivativeSucc hfan hall N]
  rw [mul_assoc, div_mul_cancel₀]
  exact nonautonomousFiniteCascadeStateInBranchField_ne_zero hfan hall (N + 1)
    (Fin.last (N + 1))

/-- Exact terminal equation in the algebraically independent Wiman-charge/output frame.  Its
coefficient splits into the retained lower logarithmic rate and the new terminal charge. -/
theorem nonautonomousFiniteCascadeDerivation_terminalStateSucc_eq_lowerLogarithmicRate_mul_charge_mul
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    nonautonomousFiniteCascadeDerivation hfan hall h1
        (nonautonomousFiniteCascadeTerminalStateSucc hfan N) =
      nonautonomousFiniteCascadeBranchInclusionSucc hfan N
          (nonautonomousFiniteCascadeLogarithmicRate hfan N (Fin.last N)) *
        nonautonomousFiniteCascadeWimanChargeInBranch hfan (Fin.last N) *
        nonautonomousFiniteCascadeTerminalStateSucc hfan N := by
  rw [nonautonomousFiniteCascadeDerivation_terminalStateSucc_eq_lowerDerivative_mul_normalizedVelocity_mul
      hfan hall N h1,
    nonautonomousFiniteCascadeWimanChargeInBranch_eq]
  simp only [nonautonomousFiniteCascadeLogarithmicRate, map_div₀,
    nonautonomousFiniteCascadeBranchInclusionSucc_state,
    nonautonomousFiniteCascadeBranchInclusionSucc_derivative,
    nonautonomousFiniteCascadeTerminalStateSucc,
    nonautonomousFiniteCascadeTerminalVelocitySucc,
    nonautonomousFiniteCascadeVelocityInBranchField]
  have hcast : (Fin.last N).castSucc =
      (⟨N, by omega⟩ : Fin (N + 2)) := by
    apply Fin.ext
    simp
  have hterminal : Fin.last (N + 1) =
      (⟨N + 1, by omega⟩ : Fin (N + 2)) := by
    apply Fin.ext
    simp
  simp [hcast, hterminal]
  field_simp [nonautonomousFiniteCascadeStateInBranchField_ne_zero hfan hall (N + 1),
    nonautonomousFiniteCascadeDerivativeInBranchField_ne_zero hfan hall (N + 1)]
  simp

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

/-- A state-coordinate derivation annihilates a Wiman charge whenever it kills both adjacent
states defining that charge. -/
theorem nonautonomousFiniteCascadeCoordinateDerivation_WimanCharge_eq_zero_of_ne
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
      simp [Ne.symm hjk]
    · change g (D₀ y) = P (g y)
      rw [show D₀ y = 0 by rfl, map_zero, hgy, hP]
      simp [Ne.symm hjks]
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
    · have hM₀ : M ≠ 0 := by omega
      have hframe : frame j =
          nonautonomousFiniteCascadeStateInBranchField hfan M (Fin.last M) := by
        simp [frame, nonautonomousFiniteCascadeClockWimanOutputFrame,
          hjM, hM₀]
      change P i (frame j) = 0
      rw [hframe, hP]
      simp
      omega
    · let i' : Fin M := ⟨i, by omega⟩
      let j' : Fin M := ⟨j, by omega⟩
      have hframe : frame j =
          nonautonomousFiniteCascadeWimanChargeInBranch hfan j' := by
        simp [frame, nonautonomousFiniteCascadeClockWimanOutputFrame,
          hj₀, hjM, j']
      change P i (frame j) = 0
      rw [hframe]
      apply nonautonomousFiniteCascadeCoordinateDerivation_laterWimanCharge_eq_zero
        hfan hall M h1 i' j'
      · exact hij'
      · intro s
        simpa [i'] using hP i s
  have hdiag : ∀ i : Fin (M + 1), J i i ≠ 0 := by
    intro i
    by_cases hi₀ : (i : ℕ) = 0
    · have hframe : frame i =
          nonautonomousFiniteCascadeStateInBranchField hfan M ⟨0, by omega⟩ := by
        simp [frame, nonautonomousFiniteCascadeClockWimanOutputFrame, hi₀]
      change P i (frame i) ≠ 0
      rw [hframe, hP]
      simp [hi₀]
    by_cases hiM : (i : ℕ) = M
    · have hM₀ : M ≠ 0 := by omega
      have hframe : frame i =
          nonautonomousFiniteCascadeStateInBranchField hfan M (Fin.last M) := by
        simp [frame, nonautonomousFiniteCascadeClockWimanOutputFrame,
          hiM, hM₀]
      change P i (frame i) ≠ 0
      rw [hframe, hP]
      simp [hiM]
    · let i' : Fin M := ⟨i, by omega⟩
      have hframe : frame i =
          nonautonomousFiniteCascadeWimanChargeInBranch hfan i' := by
        simp [frame, nonautonomousFiniteCascadeClockWimanOutputFrame,
          hi₀, hiM, i']
      change P i (frame i) ≠ 0
      rw [hframe]
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

/-- Every rational-clock coefficient in the finite branch lies in the field generated by the
literal clock over `ℂ`. -/
theorem nonautonomousFiniteBranch_algebraMap_mem_clockAdjoin
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (M : ℕ) (r : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) (NonautonomousFiniteCascadeBranchField hfan M) r ∈
      IntermediateField.adjoin ℂ
        {nonautonomousFiniteCascadeStateInBranchField hfan M ⟨0, by omega⟩} := by
  let A := IntermediateField.adjoin ℂ
    {nonautonomousFiniteCascadeStateInBranchField hfan M ⟨0, by omega⟩}
  have hX : algebraMap (RatFunc ℂ)
      (NonautonomousFiniteCascadeBranchField hfan M) RatFunc.X ∈ A := by
    rw [nonautonomousFiniteBranch_algebraMap_X]
    exact IntermediateField.subset_adjoin ℂ _ (Set.mem_singleton _)
  have hpoly : ∀ p : Polynomial ℂ,
      algebraMap (RatFunc ℂ) (NonautonomousFiniteCascadeBranchField hfan M)
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) ∈ A := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add, map_add]
        exact A.add_mem hp hq
    | monomial n a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
        refine A.mul_mem ?_ (A.pow_mem hX n)
        change algebraMap (RatFunc ℂ) (NonautonomousFiniteCascadeBranchField hfan M)
          (algebraMap ℂ (RatFunc ℂ) a) ∈ A
        rw [← IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ)
          (NonautonomousFiniteCascadeBranchField hfan M)]
        exact A.algebraMap_mem a
  induction r using RatFunc.induction_on with
  | _ p q hq =>
      rw [map_div₀]
      exact A.div_mem (hpoly p) (hpoly q)

/-- Positive-layer Wiman charges followed by the terminal output: the `M` genuine hidden
coordinates after the rational clock is moved into the coefficient field. -/
noncomputable def nonautonomousFiniteCascadeHiddenWimanOutputFrame
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (M : ℕ) (i : Fin M) : NonautonomousFiniteCascadeBranchField hfan M :=
  nonautonomousFiniteCascadeClockWimanOutputFrame hfan M i.succ

/-- The hidden Wiman/output frame is algebraically independent over the actual rational clock
field `ℂ(z)`. -/
theorem algebraicIndependent_ratFunc_nonautonomousFiniteCascadeHiddenWimanOutputFrame
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (M : ℕ)
    (h1 : ∀ k, k < M → DifferentiallyAlgebraicOfOrder (f k) 1) :
    AlgebraicIndependent (RatFunc ℂ)
      (nonautonomousFiniteCascadeHiddenWimanOutputFrame hfan M) := by
  classical
  let B := NonautonomousFiniteCascadeBranchField hfan M
  let frame : Fin (M + 1) → B :=
    nonautonomousFiniteCascadeClockWimanOutputFrame hfan M
  let clock : Fin 1 → B := fun _ => frame 0
  let hidden : Fin M → B :=
    nonautonomousFiniteCascadeHiddenWimanOutputFrame hfan M
  let e : Sum (Fin M) (Fin 1) → Fin (M + 1) :=
    Sum.elim (fun i => i.succ) (fun _ => 0)
  have he : Function.Injective e := by
    intro i j hij
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            congr 1
            apply Fin.ext
            have hv := congrArg Fin.val hij
            simpa [e] using hv
        | inr j =>
            exfalso
            have hv := congrArg Fin.val hij
            simp [e] at hv
    | inr i =>
        cases j with
        | inl j =>
            exfalso
            have hv := congrArg Fin.val hij
            simp [e] at hv
        | inr j =>
            exact congrArg Sum.inr (Subsingleton.elim i j)
  have hjoint : AlgebraicIndependent ℂ (Sum.elim hidden clock) := by
    have hcomp :=
      (algebraicIndependent_nonautonomousFiniteCascadeClockWimanOutputFrame
        hfan hall M h1).comp e he
    convert hcomp using 1
    funext i
    cases i <;> rfl
  let A := IntermediateField.adjoin ℂ
    {nonautonomousFiniteCascadeStateInBranchField hfan M ⟨0, by omega⟩}
  have hhiddenA : AlgebraicIndependent A hidden := by
    have hsplit :=
      (algebraicIndependent_sumElim_intermediateField_iff clock hidden).mp hjoint
    have hrange : Set.range clock =
        {nonautonomousFiniteCascadeStateInBranchField hfan M ⟨0, by omega⟩} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        simp [clock, frame, nonautonomousFiniteCascadeClockWimanOutputFrame]
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        refine ⟨0, ?_⟩
        simp [clock, frame, nonautonomousFiniteCascadeClockWimanOutputFrame]
    have hrel := hsplit.2
    rw [hrange] at hrel
    simpa [A] using hrel
  let ratToA : RatFunc ℂ →+* A :=
    (algebraMap (RatFunc ℂ) B).codRestrict A
      (nonautonomousFiniteBranch_algebraMap_mem_clockAdjoin hfan M)
  letI : Algebra (RatFunc ℂ) A := ratToA.toAlgebra
  letI : IsScalarTower (RatFunc ℂ) A B :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hrestricted : AlgebraicIndependent (RatFunc ℂ) hidden :=
    AlgebraicIndependent.restrictScalars
      (algebraMap (RatFunc ℂ) A).injective hhiddenA
  simpa [hidden] using hrestricted

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
  exact nonautonomousFiniteCascadeCoordinateDerivation_WimanCharge_eq_zero_of_ne
    hfan hall M h1 j k (by omega) (by omega) P hP

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
  exact nonautonomousFiniteCascadeCoordinateDerivation_WimanCharge_eq_zero_of_ne
    hfan hall M h1 j k hjk hjks P hP

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
  change D w =
    D (nonautonomousFiniteCascadeStateInBranchField hfan M k₀) * P k₀ w +
      D (nonautonomousFiniteCascadeStateInBranchField hfan M k₁) * P k₁ w
  have hkne : k₀ ≠ k₁ := by
    intro h
    have := Fin.ext_iff.mp h
    simp [k₀, k₁] at this
  have hdecomp :=
    nonautonomousFiniteCascadeDerivation_coordinate_decomposition
      hfan hall M h1 D P hP w
  rw [hdecomp]
  simp only [smul_eq_mul]
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
