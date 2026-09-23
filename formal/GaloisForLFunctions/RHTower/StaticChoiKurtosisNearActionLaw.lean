import GaloisForLFunctions.RHTower.StaticChoiCentralizerCommutatorBridge
import GaloisForLFunctions.HTGeometry.ChoiShortcutEnergyDefectKurtosisLaw
import GaloisForLFunctions.RHTower.StaticChoiPhysicalActionTransportLaw
import GaloisForLFunctions.HTGeometry.PauliXorIncidenceHypercontractivityLaw
import GaloisForLFunctions.RHTower.ReturnExcisedGrowingReplicaPseudodeterminantLaw

/-!
# Fourth-moment suppression of static Choi near-action

For a diagonal spectral source with energies `energy`, let `Q` be normalized
Hilbert--Schmidt commutator energy and let `M4(a)` be its normalized fourth
moment about any real center `a`. The existing unistochastic transport
inequality and diagonal-centralizer mass estimate give

`Q^(2 : ℕ) <= 16 * M4(a) * (1 - centralizerMass^(2 : ℕ))`,

hence `nearAction r delta <= exp (-r * Q^(2 : ℕ) / (16 * M4(a)))`.
The proof includes empty dimension, scalar spectra, zero fourth moment,
arbitrary replica count, and arbitrary near-action threshold.

For every time anchor, the same estimate retains the exact squared norm of
the anchor-subtracted Choi target: its near-action is at most
`(residualNormSq - Q^(2 : ℕ) / (16 * M4(a)))^r`. The nonnegativity of this base is
derived from the source and target, not assumed.

For the weight-`q` projection of every real Pauli coefficient family, the
corpus's hypercontractive kurtosis law yields the physical estimate

`nearAction r delta <= exp (-r * (HS([H,U])^(2 : ℕ) / tr(H^(2 : ℕ)))^(2 : ℕ) / (16 * 9^(4*q)))`.

The displayed ratio uses Lean's total division at zero. No spectral-gap,
global spectral-width, ensemble, activation, or moment-bound assumption is
introduced. Locality is enforced by an explicit coefficient projection.

## Scope

These are pointwise target near-action estimates, derived from existing
transport and hypercontractivity results. No external-literature novelty
claim is made. They do not bound the complete circuit incidence action:
commuting targets have zero activation, and no initial cutoff, ordered
first-entry interval, surviving sheet multiplicity, or occupied-image
capacity is eliminated by this estimate.
-/

open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalized fourth spectral moment; subtract a center in the argument. -/
def normalizedSpectralFourthMoment {d : ℕ} (energy : Fin d → ℝ) : ℝ :=
  (d : ℝ)⁻¹ * ∑ i, energy i ^ (4 : ℕ)

theorem normalizedSpectralFourthMoment_nonneg {d : ℕ}
    (energy : Fin d → ℝ) : 0 ≤ normalizedSpectralFourthMoment energy := by
  unfold normalizedSpectralFourthMoment
  positivity

/-- Fourth-moment transport controls commutator activation by off-diagonal mass. -/
theorem normalizedSpectralCommutatorEnergy_sq_le_fourthMoment_offDiagonal
    {d : ℕ} (energy : Fin d → ℝ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    normalizedSpectralCommutatorEnergy energy (U : Matrix (Fin d) (Fin d) ℂ) ^ (2 : ℕ) ≤
      16 * normalizedSpectralFourthMoment energy *
        normalizedSpectralOffDiagonalMass (U : Matrix (Fin d) (Fin d) ℂ) := by
  let W := (U : Matrix (Fin d) (Fin d) ℂ)
  have hrow : ∀ i, ∑ j, ‖W i j‖ ^ (2 : ℕ) = 1 :=
    sum_sq_norm_row_of_unitary U.2
  have hcol : ∀ j, ∑ i, ‖W i j‖ ^ (2 : ℕ) = 1 := by
    intro j
    simpa [W, finiteUnitaryEntryWeight, Complex.sq_norm] using
      sum_finiteUnitaryEntryWeight_column U j
  have ht := doublyStochastic_quadraticTransport_sq_le_offDiag_fourth
    energy (fun i j => ‖W i j‖ ^ (2 : ℕ)) (fun i j => sq_nonneg _) hrow hcol
  have he : normalizedSpectralCommutatorEnergy energy W =
      (d : ℝ)⁻¹ * ∑ i, ∑ j, (energy i - energy j) ^ (2 : ℕ) * ‖W i j‖ ^ (2 : ℕ) := by
    unfold normalizedSpectralCommutatorEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  change normalizedSpectralCommutatorEnergy energy W ^ (2 : ℕ) ≤ _
  rw [he]
  calc
    ((d : ℝ)⁻¹ * ∑ i, ∑ j, (energy i - energy j) ^ (2 : ℕ) * ‖W i j‖ ^ (2 : ℕ)) ^ (2 : ℕ) =
        ((d : ℝ)⁻¹) ^ (2 : ℕ) *
          (∑ i, ∑ j, (energy i - energy j) ^ (2 : ℕ) * ‖W i j‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ ≤ ((d : ℝ)⁻¹) ^ (2 : ℕ) *
        (16 * (∑ i, ∑ j, if i = j then 0 else ‖W i j‖ ^ (2 : ℕ)) *
          ∑ i, energy i ^ (4 : ℕ)) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    _ = _ := by
      unfold normalizedSpectralFourthMoment normalizedSpectralOffDiagonalMass
      dsimp [W]
      ring

/-- Commutator activation is invariant under a common spectral energy shift. -/
theorem normalizedSpectralCommutatorEnergy_sub_const
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ)
    (W : Matrix (Fin d) (Fin d) ℂ) :
    normalizedSpectralCommutatorEnergy (fun i => energy i - a) W =
      normalizedSpectralCommutatorEnergy energy W := by
  unfold normalizedSpectralCommutatorEnergy
  simp only [sub_sub_sub_cancel_right]

/-- Quartic activation is bounded by centralizer deficit, including zero moment. -/
theorem normalizedSpectralQuarticActivation_le_centralizerDeficit
    (d : ℕ) (energy : Fin d → ℝ) (a : ℝ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    normalizedSpectralCommutatorEnergy energy (U : Matrix (Fin d) (Fin d) ℂ) ^ (2 : ℕ) /
        (16 * normalizedSpectralFourthMoment (fun i => energy i - a)) ≤
      1 - unitaryDiagonalCentralizerMass (U : Matrix (Fin d) (Fin d) ℂ) ^ (2 : ℕ) := by
  by_cases hd : d = 0
  · subst d
    simp [normalizedSpectralCommutatorEnergy, unitaryDiagonalCentralizerMass]
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  let W := (U : Matrix (Fin d) (Fin d) ℂ)
  let M := normalizedSpectralFourthMoment (fun i => energy i - a)
  have hm0 : 0 ≤ M := normalizedSpectralFourthMoment_nonneg _
  have hb0 : 0 ≤ 1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ) := by
    have hl := unitaryDiagonalCentralizerMass_nonneg W
    have hu := unitaryDiagonalCentralizerMass_le_one hdpos U.2
    nlinarith
  have hcomm := normalizedSpectralCommutatorEnergy_sq_le_fourthMoment_offDiagonal
    (fun i => energy i - a) U
  rw [normalizedSpectralCommutatorEnergy_sub_const] at hcomm
  have hoff := normalizedSpectralOffDiagonalMass_le_one_sub_centralizerMass_sq
    hdpos U.2
  change normalizedSpectralCommutatorEnergy energy W ^ (2 : ℕ) / (16 * M) ≤ _
  by_cases hm : M = 0
  · simpa [hm] using hb0
  · have hmpos : 0 < M := lt_of_le_of_ne hm0 (Ne.symm hm)
    apply (div_le_iff₀ (by positivity : 0 < 16 * M)).2
    calc
      normalizedSpectralCommutatorEnergy energy W ^ (2 : ℕ) ≤
          16 * M * normalizedSpectralOffDiagonalMass W := hcomm
      _ ≤ 16 * M * (1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hoff (by positivity)
      _ = _ := by ring

/-- Replica suppression from centered fourth moment, without a spectral-width factor. -/
theorem directStaticChoiTargetNearActionMass_le_exp_centeredFourthMoment
    (d : ℕ) (energy : Fin d → ℝ) (a : ℝ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (GaloisForLFunctions.RHTower.choiVector (U : Matrix (Fin d) (Fin d) ℂ))
        energy r δ ≤
      Real.exp (-(r : ℝ) *
        (normalizedSpectralCommutatorEnergy energy
            (U : Matrix (Fin d) (Fin d) ℂ) ^ (2 : ℕ) /
          (16 * normalizedSpectralFourthMoment (fun i => energy i - a)))) := by
  let W := (U : Matrix (Fin d) (Fin d) ℂ)
  let b := normalizedSpectralCommutatorEnergy energy W ^ (2 : ℕ) /
    (16 * normalizedSpectralFourthMoment (fun i => energy i - a))
  have hnear : directStaticChoiTargetNearActionMass
      (GaloisForLFunctions.RHTower.choiVector W) energy r δ ≤
      unitaryDiagonalCentralizerMass W ^ (2 * r) := by
    by_cases hd : d = 0
    · subst d
      simpa [directStaticChoiCentralizerMass, unitaryDiagonalCentralizerMass] using
        directStaticChoiTargetNearActionMass_le_centralizerMass_pow
          (GaloisForLFunctions.RHTower.choiVector W) energy r δ
    · exact directStaticChoiTargetNearActionMass_choiVector_le
        (Nat.pos_of_ne_zero hd) W energy r δ
  have hb := normalizedSpectralQuarticActivation_le_centralizerDeficit d energy a U
  have hbase : unitaryDiagonalCentralizerMass W ^ (2 : ℕ) ≤ Real.exp (-b) := by
    have hexp := Real.add_one_le_exp (-b)
    change b ≤ 1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ) at hb
    linarith
  have hpow := pow_le_pow_left₀ (sq_nonneg (unitaryDiagonalCentralizerMass W)) hbase r
  rw [← pow_mul] at hpow
  refine hnear.trans (hpow.trans_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  dsimp [b, W]
  ring

/-- Return removal retains its exact residual norm while fourth-moment
activation supplies an additional additive defect before taking replicas. -/
theorem directStaticChoiTargetNearActionMass_anchorResidual_le_quarticDefect
    (n : ℕ) (energy : Fin (n + 1) → ℝ) (anchor a : ℝ)
    (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (r : ℕ) (δ : ℝ) :
    let target := GaloisForLFunctions.RHTower.choiVector
      (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    let residual := staticChoiAnchorResidual energy anchor target
    directStaticChoiTargetNearActionMass residual energy r δ ≤
      (‖residual‖ ^ (2 : ℕ) -
        normalizedSpectralCommutatorEnergy energy
            (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ^ (2 : ℕ) /
          (16 * normalizedSpectralFourthMoment (fun i => energy i - a))) ^ r := by
  dsimp only
  let W := (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  let target := GaloisForLFunctions.RHTower.choiVector W
  let residual := staticChoiAnchorResidual energy anchor target
  let M := normalizedSpectralFourthMoment (fun i => energy i - a)
  let Q := normalizedSpectralCommutatorEnergy energy W
  have hM0 : 0 ≤ M := normalizedSpectralFourthMoment_nonneg _
  have hoff0 : 0 ≤ normalizedSpectralOffDiagonalMass W := by
    unfold normalizedSpectralOffDiagonalMass
    positivity
  have hcomm := normalizedSpectralCommutatorEnergy_sq_le_fourthMoment_offDiagonal
    (fun i => energy i - a) U
  rw [normalizedSpectralCommutatorEnergy_sub_const] at hcomm
  have hratio : Q ^ (2 : ℕ) / (16 * M) ≤ normalizedSpectralOffDiagonalMass W := by
    by_cases hM : M = 0
    · simpa [hM] using hoff0
    · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hM)
      apply (div_le_iff₀ (by positivity : 0 < 16 * M)).2
      simpa [Q, M, W, mul_comm] using hcomm
  have hsplit := diagonalMass_add_offDiagonalMass_eq_norm_sq residual
  have hoff := offDiagonalMass_staticChoiAnchorResidual_choiVector_eq
    (Nat.succ_pos n) energy anchor W
  change (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
    if i = j then 0 else ‖residual (i, j)‖ ^ (2 : ℕ)) =
      normalizedSpectralOffDiagonalMass W at hoff
  rw [hoff] at hsplit
  have hmass := directStaticChoiCentralizerMass_sq_le_diagonalMass
    (Nat.succ_pos n) residual
  have hbase : directStaticChoiCentralizerMass residual ^ (2 : ℕ) ≤
      ‖residual‖ ^ (2 : ℕ) - Q ^ (2 : ℕ) / (16 * M) := by linarith
  have hnear := directStaticChoiTargetNearActionMass_le_centralizerMass_pow
    residual energy r δ
  rw [pow_mul] at hnear
  exact hnear.trans (pow_le_pow_left₀ (sq_nonneg _) hbase r)

/-- A coefficient projection, not a spectral or probabilistic assumption. -/
def cutoffPauliCubeCoefficients {n : ℕ} (q : ℕ) (c : QubitCube n → ℝ) :
    QubitCube n → ℝ :=
  fun s => if cubeWeight s ≤ q then c s else 0

/-- Every real coefficient family constructs an ordinary fixed-locality Hamiltonian.
The rate incurs no Hilbert-space dimension or global spectral width factor. -/
theorem localPauli_directStaticChoiNearActionMass_le_exp_kurtosis
    (n q : ℕ) (c : QubitCube n → ℝ)
    (U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (r : ℕ) (δ : ℝ) :
    let coeff := cutoffPauliCubeCoefficients q c
    let hH := pauliHamiltonian_isHermitian coeff
    let W := hermitianSpectralEndpoint hH U
    let E := ((2 ^ n : ℕ) : ℝ)⁻¹ * ∑ i, hH.eigenvalues i ^ (2 : ℕ)
    directStaticChoiTargetNearActionMass
        (GaloisForLFunctions.RHTower.choiVector
          (W : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
        hH.eigenvalues r δ ≤
      Real.exp (-(r : ℝ) *
        (normalizedSpectralCommutatorEnergy hH.eigenvalues
            (W : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) ^ (2 : ℕ) /
          (16 * (9 ^ q : ℝ) ^ (4 : ℕ) * E ^ (2 : ℕ)))) := by
  dsimp only
  let coeff := cutoffPauliCubeCoefficients q c
  let hH := pauliHamiltonian_isHermitian coeff
  let Ue := hermitianSpectralEndpoint hH U
  let W := (Ue : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
  let D : ℝ := ((2 ^ n : ℕ) : ℝ)
  let E := D⁻¹ * ∑ i, hH.eigenvalues i ^ (2 : ℕ)
  let M := normalizedSpectralFourthMoment hH.eigenvalues
  let K : ℝ := (9 ^ q : ℝ) ^ (4 : ℕ)
  let Q := normalizedSpectralCommutatorEnergy hH.eigenvalues W
  let B := 16 * K * E ^ (2 : ℕ)
  have hdpos : 0 < (2 : ℕ) ^ n := pow_pos (by omega) n
  have hDpos : 0 < D := by dsimp [D]; exact_mod_cast hdpos
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hdegree : ∀ s, coeff s ≠ 0 → cubeWeight s ≤ q := by
    intro s hs
    by_contra h
    exact hs (if_neg h)
  have hk := pauliHamiltonian_eigenKurtosis coeff hdegree
  have hM : M ≤ K * E ^ (2 : ℕ) := by
    have hk' : D * (∑ i, hH.eigenvalues i ^ (4 : ℕ)) ≤
        K * (∑ i, hH.eigenvalues i ^ (2 : ℕ)) ^ (2 : ℕ) := by
      simpa only [Fintype.card_fin] using hk
    calc
      M = D⁻¹ ^ (2 : ℕ) * (D * ∑ i, hH.eigenvalues i ^ (4 : ℕ)) := by
        dsimp [M, normalizedSpectralFourthMoment]
        change D⁻¹ * _ = _
        field_simp
      _ ≤ D⁻¹ ^ (2 : ℕ) * (K * (∑ i, hH.eigenvalues i ^ (2 : ℕ)) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hk' (sq_nonneg _)
      _ = K * E ^ (2 : ℕ) := by dsimp [E]; ring
  have hs0 := unitaryDiagonalCentralizerMass_nonneg W
  have hs1 := unitaryDiagonalCentralizerMass_le_one hdpos Ue.2
  have hdef : 0 ≤ 1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ) := by nlinarith
  have hQ : Q ^ (2 : ℕ) ≤ B * (1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ)) := by
    calc
      Q ^ (2 : ℕ) ≤ 16 * M * normalizedSpectralOffDiagonalMass W :=
        normalizedSpectralCommutatorEnergy_sq_le_fourthMoment_offDiagonal
          hH.eigenvalues Ue
      _ ≤ 16 * M * (1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left
          (normalizedSpectralOffDiagonalMass_le_one_sub_centralizerMass_sq hdpos Ue.2)
          (mul_nonneg (by positivity) (normalizedSpectralFourthMoment_nonneg _))
      _ ≤ 16 * (K * E ^ (2 : ℕ)) * (1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by positivity)) hdef
      _ = _ := by dsimp [B]; ring
  have hB0 : 0 ≤ B := by dsimp [B, K]; positivity
  have hb : Q ^ (2 : ℕ) / B ≤ 1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ) := by
    by_cases hB : B = 0
    · simpa [hB] using hdef
    · apply (div_le_iff₀ (lt_of_le_of_ne hB0 (Ne.symm hB))).2
      nlinarith [hQ]
  have hbase : unitaryDiagonalCentralizerMass W ^ (2 : ℕ) ≤
      Real.exp (-(Q ^ (2 : ℕ) / B)) := by
    have hexp := Real.add_one_le_exp (-(Q ^ (2 : ℕ) / B))
    linarith
  have hpow := pow_le_pow_left₀ (sq_nonneg (unitaryDiagonalCentralizerMass W)) hbase r
  rw [← pow_mul] at hpow
  have hnear := directStaticChoiTargetNearActionMass_choiVector_le
    hdpos W hH.eigenvalues r δ
  refine hnear.trans (hpow.trans_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  dsimp [B, Q, K, E, D, W, Ue, hH, coeff]
  ring

/-- Physical form: the activation is the commutator energy divided by source
Hilbert--Schmidt energy. The dimension factors cancel, also at zero energy. -/
theorem localPauli_directStaticChoiNearActionMass_le_exp_physicalEnergyRatio
    (n q : ℕ) (c : QubitCube n → ℝ)
    (U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (r : ℕ) (δ : ℝ) :
    let coeff := cutoffPauliCubeCoefficients q c
    let H := pauliHamiltonian coeff
    let hH := pauliHamiltonian_isHermitian coeff
    directStaticChoiTargetNearActionMass
        (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH U :
            Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
        hH.eigenvalues r δ ≤
      Real.exp (-(r : ℝ) *
        (finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) -
              (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) * H) ^ (2 : ℕ) /
          (16 * (9 ^ q : ℝ) ^ (4 : ℕ) * (Matrix.trace (H * H)).re ^ (2 : ℕ)))) := by
  dsimp only
  let coeff := cutoffPauliCubeCoefficients q c
  let H := pauliHamiltonian coeff
  let hH := pauliHamiltonian_isHermitian coeff
  have hdpos : 0 < (2 : ℕ) ^ n := pow_pos (by omega) n
  have hdR : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hdpos
  have h := localPauli_directStaticChoiNearActionMass_le_exp_kurtosis n q c U r δ
  dsimp only at h
  rw [normalizedSpectralCommutatorEnergy_hermitianSpectralEndpoint hdpos hH U] at h
  rw [← trace_mul_self_re_eq_sum_sq_eigenvalues H hH] at h
  refine h.trans_eq ?_
  congr 2
  rw [mul_pow]
  have hden : 16 * (9 ^ q : ℝ) ^ (4 : ℕ) *
      (((2 ^ n : ℕ) : ℝ)⁻¹ * (Matrix.trace (H * H)).re) ^ (2 : ℕ) =
      (((2 ^ n : ℕ) : ℝ)⁻¹) ^ (2 : ℕ) *
        (16 * (9 ^ q : ℝ) ^ (4 : ℕ) * (Matrix.trace (H * H)).re ^ (2 : ℕ)) := by ring
  rw [hden, mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero (ne_of_gt hdR)))]

end

end RHTower
