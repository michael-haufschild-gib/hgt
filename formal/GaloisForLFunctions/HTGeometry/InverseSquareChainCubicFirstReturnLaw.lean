import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
import GaloisForLFunctions.HTGeometry.StaticLocalExactReturnReflectionLaw
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw
import GaloisForLFunctions.HTGeometry.ProjectiveSeedWeakTwoLocalGrowthLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

def firstInverseCubeBridgeConfig {L : ℕ} (hL : 2 ≤ L) :
    Config (PairQubit L) := fun q =>
  decide (q = (⟨0, by omega⟩, true) ∨ q = (⟨1, by omega⟩, false))

theorem firstInverseCubeBridgeConfig_true_iff {L : ℕ} (hL : 2 ≤ L)
    (q : PairQubit L) :
    firstInverseCubeBridgeConfig hL q = true ↔
      q = (⟨0, by omega⟩, true) ∨ q = (⟨1, by omega⟩, false) := by
  simp [firstInverseCubeBridgeConfig]

theorem inverseSquareMatchingEnergy_firstInverseCubeBridgeConfig_eq_zero
    {L : ℕ} (hL : 2 ≤ L) :
    inverseSquareMatchingEnergy (firstInverseCubeBridgeConfig hL) = 0 := by
  unfold inverseSquareMatchingEnergy
  apply Finset.sum_eq_zero
  intro j hj
  simp only [ite_eq_right_iff]
  intro hboth
  have hfalse :=
    (firstInverseCubeBridgeConfig_true_iff hL (j, false)).mp hboth.1
  have htrue :=
    (firstInverseCubeBridgeConfig_true_iff hL (j, true)).mp hboth.2
  rcases hfalse with hfalse | hfalse <;>
    rcases htrue with htrue | htrue <;> simp_all

theorem inverseCubeBridgeEnergy_firstInverseCubeBridgeConfig
    {L : ℕ} (hL : 2 ≤ L) :
    inverseCubeBridgeEnergy (firstInverseCubeBridgeConfig hL) =
      1 / (L : ℝ) ^ 3 := by
  unfold inverseCubeBridgeEnergy
  let j0 : Fin L := ⟨0, by omega⟩
  have hsum :
      (∑ j : Fin L, if h : j.val + 1 < L then
        if firstInverseCubeBridgeConfig hL (j, true) = true ∧
            firstInverseCubeBridgeConfig hL (⟨j.val + 1, h⟩, false) = true
          then (1 : ℝ) else 0
        else 0) = 1 := by
    rw [Finset.sum_eq_single j0]
    · have hsucc : j0.val + 1 < L := by dsimp [j0]; omega
      simp only [hsucc, dite_true]
      have h0 : firstInverseCubeBridgeConfig hL (j0, true) = true := by
        apply (firstInverseCubeBridgeConfig_true_iff hL _).2
        left
        rfl
      have h1 : firstInverseCubeBridgeConfig hL (⟨j0.val + 1, hsucc⟩, false) = true := by
        apply (firstInverseCubeBridgeConfig_true_iff hL _).2
        right
        rfl
      simp [h0, h1]
    · intro j hj hjne
      by_cases hsucc : j.val + 1 < L
      · simp only [hsucc, dite_true]
        have hnot : firstInverseCubeBridgeConfig hL (j, true) ≠ true := by
          intro hjtrue
          rcases (firstInverseCubeBridgeConfig_true_iff hL _).mp hjtrue with h | h
          · apply hjne
            apply Fin.ext
            simpa [j0] using congrArg (fun q => q.1.val) h
          · simp at h
        simp [hnot]
      · simp [hsucc]
    · simp
  rw [hsum, mul_one]

theorem inverseSquareChainEnergy_firstInverseCubeBridgeConfig
    {L : ℕ} (hL : 2 ≤ L) :
    inverseSquareChainEnergy (firstInverseCubeBridgeConfig hL) =
      1 / (L : ℝ) ^ 3 := by
  rw [inverseSquareChainEnergy,
    inverseSquareMatchingEnergy_firstInverseCubeBridgeConfig_eq_zero hL,
    inverseCubeBridgeEnergy_firstInverseCubeBridgeConfig hL, zero_add]

def inverseSquareChainCubicReturnSeparation (L : ℕ) (guard : ℝ) : ℝ :=
  2 * (guard / (L : ℝ) ^ 3) / Real.pi

theorem inverseSquareChainCubicReturnSeparation_le_norm_sub_one_of_le_halfPeriod
    {L : ℕ} (hL : 2 ≤ L) {guard t : ℝ}
    (hguard : 0 ≤ guard) (hgt : guard ≤ t)
    (ht : t ≤ Real.pi * (L : ℝ) ^ 3) :
    inverseSquareChainCubicReturnSeparation L guard ≤
      ‖inverseSquareChainEvolution L t - 1‖ := by
  let x := firstInverseCubeBridgeConfig hL
  let phi := t / (L : ℝ) ^ 3
  have hLpos : (0 : ℝ) < L := by positivity
  have ht0 : 0 ≤ t := hguard.trans hgt
  have hphi0 : 0 ≤ phi := by
    dsimp [phi]
    exact div_nonneg ht0 (by positivity)
  have hphipi : phi ≤ Real.pi := by
    dsimp [phi]
    rwa [div_le_iff₀ (by positivity)]
  have hentry :
      (inverseSquareChainEvolution L t - 1) x x =
        Complex.exp (-(Complex.I * (phi : ℂ))) - 1 := by
    rw [inverseSquareChainEvolution_diagonal]
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply,
      ↓reduceIte]
    rw [inverseSquareChainEnergy_firstInverseCubeBridgeConfig hL]
    dsimp [phi]
    congr 1
    push_cast
    field_simp
  have hchord := phase_chord_lower hphi0 hphipi
  have hop := GaloisForLFunctions.HTGeometry.norm_entry_le_l2_opNorm
    (inverseSquareChainEvolution L t - 1) x x
  calc
    inverseSquareChainCubicReturnSeparation L guard =
        2 * (guard / (L : ℝ) ^ 3) / Real.pi := rfl
    _ ≤ 2 * phi / Real.pi := by
      gcongr
      exact div_le_div_of_nonneg_right hgt (by positivity)
    _ ≤ ‖Complex.exp (-(Complex.I * (phi : ℂ))) - 1‖ := hchord
    _ = ‖(inverseSquareChainEvolution L t - 1) x x‖ := by rw [hentry]
    _ ≤ ‖inverseSquareChainEvolution L t - 1‖ := hop

theorem norm_exp_neg_I_mul_two_pi_sub_sub_one (phi : ℝ) :
    ‖Complex.exp (-(Complex.I * (phi : ℂ))) - 1‖ =
      ‖Complex.exp (-(Complex.I * ((2 * Real.pi - phi : ℝ) : ℂ))) - 1‖ := by
  have hbase :
      ‖Complex.exp (-(phi : ℂ) * Complex.I) - 1‖ =
        ‖Complex.exp (-((2 * Real.pi - phi : ℝ) : ℂ) * Complex.I) - 1‖ := by
    rw [show (1 : ℂ) = Complex.exp (-((0 : ℝ) : ℂ) * Complex.I) by norm_num]
    rw [norm_expI_sub_eq phi 0, norm_expI_sub_eq (2 * Real.pi - phi) 0]
    simp only [sub_zero]
    rw [show (2 * Real.pi - phi) / 2 = Real.pi - phi / 2 by ring,
      Real.sin_pi_sub]
  convert hbase using 1 <;> congr 2 <;> ring

theorem inverseSquareChainCubicReturnSeparation_le_norm_sub_one
    {L : ℕ} (hL : 2 ≤ L) {guard t : ℝ}
    (hguard : 0 ≤ guard)
    (ht : t ∈ Set.Icc guard
      (2 * Real.pi * (L : ℝ) ^ 3 - guard)) :
    inverseSquareChainCubicReturnSeparation L guard ≤
      ‖inverseSquareChainEvolution L t - 1‖ := by
  by_cases hhalf : t ≤ Real.pi * (L : ℝ) ^ 3
  · exact inverseSquareChainCubicReturnSeparation_le_norm_sub_one_of_le_halfPeriod
      hL hguard ht.1 hhalf
  · let x := firstInverseCubeBridgeConfig hL
    let phi := t / (L : ℝ) ^ 3
    let psi := 2 * Real.pi - phi
    have hLpos : (0 : ℝ) < L := by positivity
    have hden : 0 < (L : ℝ) ^ 3 := by positivity
    have htop : t ≤ 2 * Real.pi * (L : ℝ) ^ 3 := by
      exact ht.2.trans (sub_le_self _ hguard)
    have hpsi0 : 0 ≤ psi := by
      dsimp [psi, phi]
      rw [sub_nonneg, div_le_iff₀ hden]
      exact htop
    have hpsipi : psi ≤ Real.pi := by
      have hnot := lt_of_not_ge hhalf
      have hphiPi : Real.pi ≤ phi := by
        dsimp [phi]
        rw [le_div_iff₀ hden]
        exact hnot.le
      dsimp [psi]
      nlinarith
    have hguardPsi : guard / (L : ℝ) ^ 3 ≤ psi := by
      dsimp [psi, phi]
      rw [div_le_iff₀ hden]
      have hcancel : t / (L : ℝ) ^ 3 * (L : ℝ) ^ 3 = t := by
        exact div_mul_cancel₀ t (ne_of_gt hden)
      rw [sub_mul, hcancel]
      nlinarith [ht.2]
    have hentry :
        (inverseSquareChainEvolution L t - 1) x x =
          Complex.exp (-(Complex.I * (phi : ℂ))) - 1 := by
      rw [inverseSquareChainEvolution_diagonal]
      simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply,
        ↓reduceIte]
      rw [inverseSquareChainEnergy_firstInverseCubeBridgeConfig hL]
      dsimp [phi]
      congr 1
      push_cast
      field_simp
    have hchord := phase_chord_lower hpsi0 hpsipi
    have hreflect := norm_exp_neg_I_mul_two_pi_sub_sub_one phi
    have hop := GaloisForLFunctions.HTGeometry.norm_entry_le_l2_opNorm
      (inverseSquareChainEvolution L t - 1) x x
    calc
      inverseSquareChainCubicReturnSeparation L guard =
          2 * (guard / (L : ℝ) ^ 3) / Real.pi := rfl
      _ ≤ 2 * psi / Real.pi := by gcongr
      _ ≤ ‖Complex.exp (-(Complex.I * (psi : ℂ))) - 1‖ := hchord
      _ = ‖Complex.exp (-(Complex.I * (phi : ℂ))) - 1‖ := hreflect.symm
      _ = ‖(inverseSquareChainEvolution L t - 1) x x‖ := by rw [hentry]
      _ ≤ ‖inverseSquareChainEvolution L t - 1‖ := hop

theorem inverseSquareChainCubicReturnSeparation_sub_perturbation_le
    {L : ℕ} (hL : 2 ≤ L)
    (K : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ)
    (hK : IsSelfAdjoint K) {guard t : ℝ}
    (hguard : 0 ≤ guard)
    (ht : t ∈ Set.Icc guard
      (2 * Real.pi * (L : ℝ) ^ 3 - guard)) :
    inverseSquareChainCubicReturnSeparation L guard -
        |t| * ‖K - inverseSquareChainHamiltonian L‖ ≤
      ‖unitaryEvolution K t - 1‖ := by
  have hseed := inverseSquareChainCubicReturnSeparation_le_norm_sub_one
    hL hguard ht
  have hduhamel := GaloisForLFunctions.HTGeometry.norm_unitaryEvolution_sub_le
    (inverseSquareChainHamiltonian L) K
    (inverseSquareChainHamiltonian_isSelfAdjoint L) hK t
  have hduhamel' :
      ‖unitaryEvolution (inverseSquareChainHamiltonian L) t -
          unitaryEvolution K t‖ ≤
        |t| * ‖K - inverseSquareChainHamiltonian L‖ := by
    simpa only [norm_sub_rev K (inverseSquareChainHamiltonian L)] using hduhamel
  have htriangle :
      ‖inverseSquareChainEvolution L t - 1‖ ≤
        ‖inverseSquareChainEvolution L t - unitaryEvolution K t‖ +
          ‖unitaryEvolution K t - 1‖ := by
    simpa only [dist_eq_norm] using
      (dist_triangle (inverseSquareChainEvolution L t) (unitaryEvolution K t) 1)
  dsimp [inverseSquareChainEvolution] at hseed htriangle
  linarith

theorem inverseSquareChainCubicReturn_halfSeparation_le_of_perturbationBudget
    {L : ℕ} (hL : 2 ≤ L)
    (K : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ)
    (hK : IsSelfAdjoint K) {guard t : ℝ}
    (hguard : 0 ≤ guard)
    (ht : t ∈ Set.Icc guard
      (2 * Real.pi * (L : ℝ) ^ 3 - guard))
    (hbudget : |t| * ‖K - inverseSquareChainHamiltonian L‖ ≤
      inverseSquareChainCubicReturnSeparation L guard / 2) :
    inverseSquareChainCubicReturnSeparation L guard / 2 ≤
      ‖unitaryEvolution K t - 1‖ := by
  have h := inverseSquareChainCubicReturnSeparation_sub_perturbation_le
    hL K hK hguard ht
  linarith

theorem norm_projectiveSeedWeakTwoLocalHamiltonian_sub_inverseSquareChain_le
    {L : ℕ} (hL : 2 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L) :
    ‖projectiveSeedWeakTwoLocalHamiltonian L p scale x -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3) := by
  rw [projectiveSeedWeakTwoLocalHamiltonian]
  rw [show nearestNeighborPathLocalHamiltonian L p +
      (scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x -
        inverseSquareChainHamiltonian L =
      (nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L) +
          (scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x by abel]
  calc
    ‖(nearestNeighborPathLocalHamiltonian L p -
          inverseSquareChainHamiltonian L) +
        (scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x‖ ≤
      ‖nearestNeighborPathLocalHamiltonian L p -
          inverseSquareChainHamiltonian L‖ +
        ‖(scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x‖ :=
      norm_add_le _ _
    _ ≤ rho * nearestNeighborPathLocalGeneratorMass L +
        |scale| * ‖pairQubitReindexedTwoLocalPauliHamiltonian L x‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add hseed le_rfl
    _ ≤ rho * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3) := by
      gcongr
      exact norm_pairQubitReindexedTwoLocalPauliHamiltonian_le_eighteen_mul_cube_of_mem_box
        (by omega : 1 ≤ L) hx

/-- One ordinary static two-local draw has no identity re-entry throughout
the complete post-guard cubic window whenever its one-draw perturbation
budget fits inside half the explicit bridge-phase separation. -/
theorem projectiveSeedWeakTwoLocal_cubicReturn_halfSeparation_le
    {L : ℕ} (hL : 2 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale guard : ℝ} (hguard : 0 ≤ guard)
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    (hbudget : (2 * Real.pi * (L : ℝ) ^ 3) *
        (rho * nearestNeighborPathLocalGeneratorMass L +
          |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) ≤
      inverseSquareChainCubicReturnSeparation L guard / 2)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L)
    {t : ℝ}
    (ht : t ∈ Set.Icc guard
      (2 * Real.pi * (L : ℝ) ^ 3 - guard)) :
    inverseSquareChainCubicReturnSeparation L guard / 2 ≤
      ‖unitaryEvolution
        (projectiveSeedWeakTwoLocalHamiltonian L p scale x) t - 1‖ := by
  let K := projectiveSeedWeakTwoLocalHamiltonian L p scale x
  have hdiff :=
    norm_projectiveSeedWeakTwoLocalHamiltonian_sub_inverseSquareChain_le
      hL (rho := rho) (scale := scale) hseed hx
  have ht0 : 0 ≤ t := hguard.trans ht.1
  have htmax : |t| ≤ 2 * Real.pi * (L : ℝ) ^ 3 := by
    rw [abs_of_nonneg ht0]
    exact ht.2.trans (sub_le_self _ hguard)
  have hperiod0 : 0 ≤ 2 * Real.pi * (L : ℝ) ^ 3 := by positivity
  have htimeBudget : |t| * ‖K - inverseSquareChainHamiltonian L‖ ≤
      inverseSquareChainCubicReturnSeparation L guard / 2 := by
    calc
      |t| * ‖K - inverseSquareChainHamiltonian L‖ ≤
          (2 * Real.pi * (L : ℝ) ^ 3) *
            ‖K - inverseSquareChainHamiltonian L‖ :=
        mul_le_mul_of_nonneg_right htmax (norm_nonneg _)
      _ ≤ (2 * Real.pi * (L : ℝ) ^ 3) *
          (rho * nearestNeighborPathLocalGeneratorMass L +
            |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hdiff hperiod0
      _ ≤ inverseSquareChainCubicReturnSeparation L guard / 2 := hbudget
  exact inverseSquareChainCubicReturn_halfSeparation_le_of_perturbationBudget
    hL K (projectiveSeedWeakTwoLocalHamiltonian_isSelfAdjoint L p scale x)
      hguard ht htimeBudget

/-- Same ordinary time-independent local draw has robust linear laboratory
growth and a continuous identity-free interval extending to cubic time. -/
theorem projectiveSeedWeakTwoLocal_sameDraw_growth_and_cubicFirstReturnExclusion
    {L : ℕ} (hL : 2 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho T epsilon scale guard : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    (hT : 0 ≤ T) (hepsilon : 0 < epsilon)
    (hepsilonMax : epsilon ≤ 1 / 200)
    (hgrowthBudget : T *
        (rho * nearestNeighborPathLocalGeneratorMass L +
          |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) ≤ epsilon)
    (hguard : 0 ≤ guard)
    (hreturnBudget : (2 * Real.pi * (L : ℝ) ^ 3) *
        (rho * nearestNeighborPathLocalGeneratorMass L +
          |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) ≤
      inverseSquareChainCubicReturnSeparation L guard / 2)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L) :
    (∀ t : ℝ,
      2048 * Real.pi * epsilon ≤ t →
      t ≤ epsilon * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * epsilon)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L epsilon
          (unitaryEvolution
            (projectiveSeedWeakTwoLocalHamiltonian L p scale x) t)) ∧
    (∀ t ∈ Set.Icc guard
        (2 * Real.pi * (L : ℝ) ^ 3 - guard),
      inverseSquareChainCubicReturnSeparation L guard / 2 ≤
        ‖unitaryEvolution
          (projectiveSeedWeakTwoLocalHamiltonian L p scale x) t - 1‖) := by
  constructor
  · exact projectiveSeedWeakTwoLocal_uniform_laboratory_growth
      (by omega : 1 ≤ L) hseed hT hepsilon hepsilonMax hgrowthBudget hx
  · intro t ht
    exact projectiveSeedWeakTwoLocal_cubicReturn_halfSeparation_le
      hL hguard hseed hreturnBudget hx ht

end

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
