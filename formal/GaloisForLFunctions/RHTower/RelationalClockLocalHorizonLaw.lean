import GaloisForLFunctions.RHTower.LocalHorizonQuantumReturnLaw

/-!
# Relational-clock extension of the universal local-horizon law

The fixed-endpoint path models admit exact unitary clock translations indexed
by every real shift.  Conditional clock covariance is equivalent to global
stationarity under the diagonal clock--system shift, and every state history
used in the universal local-horizon construction satisfies both conditions.

Consequently, the local-horizon ambiguity is not an artifact of treating time
as an external primitive: the same theorem holds inside a globally stationary
relational description, for every finite observation radius and every future
probability in the closed unit interval.

This is a finite constrained quantum-history theorem.  It does not identify
the constraint with a gravitational Wheeler--DeWitt operator or assume a
cosmological spacetime.
-/

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace RHTower.ParityForecast

private theorem scaledPhase_mul_neg
    (T : ℝ) (n : ℕ) (t : ℝ) (j : Fin (n + 1)) :
    scaledPhase T n t j * scaledPhase T n (-t) j = 1 := by
  unfold scaledPhase
  rw [← Complex.exp_add]
  have hzero :
      (((2 * Real.pi * scaledEnergy T n j * t : ℝ) : ℂ) * I) +
          (((2 * Real.pi * scaledEnergy T n j * -t : ℝ) : ℂ) * I) = 0 := by
    push_cast
    ring_nf
  rw [hzero, Complex.exp_zero]

private theorem scaledPhase_neg_mul
    (T : ℝ) (n : ℕ) (t : ℝ) (j : Fin (n + 1)) :
    scaledPhase T n (-t) j * scaledPhase T n t j = 1 := by
  rw [mul_comm, scaledPhase_mul_neg]

/-- Spectral phase translation as an exact unitary on the finite clock space. -/
def spectralTimeEvolution
    {T : ℝ} (hT : 0 < T) (n : ℕ) (t : ℝ) :
    ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n where
  toFun x := WithLp.toLp 2 fun j => x j * scaledPhase T n t j
  invFun x := WithLp.toLp 2 fun j => x j * scaledPhase T n (-t) j
  left_inv x := by
    ext j
    change
      (x j * scaledPhase T n t j) *
          scaledPhase T n (-t) j = x j
    rw [mul_assoc, scaledPhase_mul_neg, mul_one]
  right_inv x := by
    ext j
    change
      (x j * scaledPhase T n (-t) j) *
          scaledPhase T n t j = x j
    rw [mul_assoc, scaledPhase_neg_mul, mul_one]
  map_add' x y := by
    ext j
    change
      (x j + y j) * scaledPhase T n t j =
        x j * scaledPhase T n t j +
          y j * scaledPhase T n t j
    ring_nf
  map_smul' c x := by
    ext j
    change
      (c * x j) * scaledPhase T n t j =
        c * (x j * scaledPhase T n t j)
    ring_nf
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    simp [scaledPhase_norm hT n t j]

@[simp] theorem spectralTimeEvolution_apply
    {T : ℝ} (hT : 0 < T) (n : ℕ) (t : ℝ)
    (x : ClockSpace n) (j : Fin (n + 1)) :
    spectralTimeEvolution hT n t x j =
      x j * scaledPhase T n t j :=
  rfl

theorem scaledPhase_add
    (T : ℝ) (n : ℕ) (s t : ℝ) (j : Fin (n + 1)) :
    scaledPhase T n (s + t) j =
      scaledPhase T n s j * scaledPhase T n t j := by
  unfold scaledPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- The spectral unitaries form an exact representation of all real shifts. -/
theorem spectralTimeEvolution_add
    {T : ℝ} (hT : 0 < T) (n : ℕ) (s t : ℝ)
    (x : ClockSpace n) :
    spectralTimeEvolution hT n s
        (spectralTimeEvolution hT n t x) =
      spectralTimeEvolution hT n (s + t) x := by
  ext j
  simp only [spectralTimeEvolution_apply]
  rw [scaledPhase_add]
  ring_nf

@[simp] theorem spectralTimeEvolution_zero
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    (x : ClockSpace n) :
    spectralTimeEvolution hT n 0 x = x := by
  ext j
  simp [spectralTimeEvolution_apply, scaledPhase]

theorem spectralTimeEvolution_scaledInterpolatedClockAt
    {T : ℝ} (hT : 0 < T) (n : ℕ) (θ s t : ℝ) :
    spectralTimeEvolution hT n s
        (scaledInterpolatedClockAt T n θ t) =
      scaledInterpolatedClockAt T n θ (s + t) := by
  ext j
  simp only [spectralTimeEvolution_apply,
    scaledInterpolatedClockAt, finiteIndexPhasedWeightKet_apply]
  rw [scaledPhase_add]
  ring_nf

/-- Clock translation transported from spectral to physical path coordinates. -/
def FixedEndpointPathModel.timeEvolution
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T)
    (t : ℝ) :
    ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n :=
  M.unitary.trans ((spectralTimeEvolution hT n t).trans M.unitary.symm)

theorem FixedEndpointPathModel.timeEvolution_add
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T)
    (s t : ℝ) (x : ClockSpace n) :
    M.timeEvolution hT s (M.timeEvolution hT t x) =
      M.timeEvolution hT (s + t) x := by
  apply M.unitary.injective
  simp only [FixedEndpointPathModel.timeEvolution,
    LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  exact spectralTimeEvolution_add hT n s t (M.unitary x)

@[simp] theorem FixedEndpointPathModel.timeEvolution_zero
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T)
    (x : ClockSpace n) :
    M.timeEvolution hT 0 x = x := by
  apply M.unitary.injective
  simp [FixedEndpointPathModel.timeEvolution]

@[simp] theorem FixedEndpointPathModel.timeEvolution_norm
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T)
    (t : ℝ) (x : ClockSpace n) :
    ‖M.timeEvolution hT t x‖ = ‖x‖ :=
  (M.timeEvolution hT t).norm_map x

/-- Conditional path states are covariant under every real clock shift. -/
theorem FixedEndpointPathModel.timeEvolution_stateAt
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T)
    (s t : ℝ) :
    M.timeEvolution hT s (M.stateAt t) =
      M.stateAt (s + t) := by
  apply M.unitary.injective
  simp only [FixedEndpointPathModel.timeEvolution,
    LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply,
    FixedEndpointPathModel.stateAt]
  rw [map_smul,
    spectralTimeEvolution_scaledInterpolatedClockAt]

/-- Diagonal shift of a complete clock-conditioned history. -/
def FixedEndpointPathModel.historyDiagonalShift
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T)
    (s : ℝ) (history : ℝ → ClockSpace n) :
    ℝ → ClockSpace n :=
  fun t => M.timeEvolution hT s (history (t - s))

/-- Global stationarity under every diagonal clock--system shift. -/
def FixedEndpointPathModel.IsRelationallyStationary
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T)
    (history : ℝ → ClockSpace n) : Prop :=
  ∀ s, M.historyDiagonalShift hT s history = history

/-- Covariance of every state conditional on an internal clock reading. -/
def FixedEndpointPathModel.IsClockCovariant
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T)
    (history : ℝ → ClockSpace n) : Prop :=
  ∀ s t, history (s + t) = M.timeEvolution hT s (history t)

/-- Exact finite quantum evolution-without-evolution equivalence. -/
theorem FixedEndpointPathModel.isClockCovariant_iff_stationary
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T)
    (history : ℝ → ClockSpace n) :
    M.IsClockCovariant hT history ↔
      M.IsRelationallyStationary hT history := by
  constructor
  · intro hcov s
    funext t
    unfold FixedEndpointPathModel.historyDiagonalShift
    rw [← hcov s (t - s)]
    congr 1
    ring_nf
  · intro hstat s t
    have hs := congrFun (hstat s) (s + t)
    unfold FixedEndpointPathModel.historyDiagonalShift at hs
    symm
    convert hs using 1
    ring_nf

/-- The complete constructed history is globally stationary. -/
theorem FixedEndpointPathModel.stateAt_relationallyStationary
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T) :
    M.IsRelationallyStationary hT M.stateAt := by
  intro s
  funext t
  unfold FixedEndpointPathModel.historyDiagonalShift
  rw [M.timeEvolution_stateAt hT]
  congr 1
  ring_nf

/-- The same constructed history is an exact family of conditional states. -/
theorem FixedEndpointPathModel.stateAt_clockCovariant
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (hT : 0 < T) :
    M.IsClockCovariant hT M.stateAt :=
  (M.isClockCovariant_iff_stationary hT M.stateAt).mpr
    (M.stateAt_relationallyStationary hT)

/-- One relationally stationary realization compared with a common baseline. -/
def RelationalPathComparison
    (R q : ℕ) (T H δ p : ℝ) (hT : 0 < T)
    (hsize : R + 2 ≤ endpointN q + 1)
    (baseline : FixedEndpointPathModel T (endpointN q) 0)
    (model :
      FixedEndpointPathModel T (endpointN q) (Real.sqrt p)) : Prop :=
  NearestNeighborHamiltonian model.hamiltonian ∧
  ContinuousLinearMap.adjoint model.hamiltonian =
    model.hamiltonian ∧
  (∀ x : ClockSpace (endpointN q),
    model.unitary (model.hamiltonian x) =
      scaledClockHamiltonian T (endpointN q) (model.unitary x)) ∧
  (∀ i j : Fin (R + 2),
    (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2 →
    inner ℂ
        (EuclideanSpace.basisFun
          (Fin (endpointN q + 1)) ℂ
          (Fin.castLE hsize i))
        (model.hamiltonian
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ
            (Fin.castLE hsize j))) =
      inner ℂ
        (EuclideanSpace.basisFun
          (Fin (endpointN q + 1)) ℂ
          (Fin.castLE hsize i))
        (baseline.hamiltonian
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ
            (Fin.castLE hsize j)))) ∧
  (∀ t : ℝ, |t| ≤ H →
    |model.returnProbability t -
      baseline.returnProbability t| < δ) ∧
  model.returnProbability T = p ∧
  model.IsRelationallyStationary hT model.stateAt

/-- One dimension and one stationary baseline realize every future probability. -/
def UniversalRelationalLocalHorizonWitness
    (R : ℕ) (T H δ : ℝ) (hT : 0 < T) : Prop :=
  ∃ q : ℕ,
    ∃ _horder : 2 * R + 2 < endpointN q,
    ∃ hsize : R + 2 ≤ endpointN q + 1,
    ∃ baseline : FixedEndpointPathModel T (endpointN q) 0,
      NearestNeighborHamiltonian baseline.hamiltonian ∧
      ContinuousLinearMap.adjoint baseline.hamiltonian =
        baseline.hamiltonian ∧
      (∀ x : ClockSpace (endpointN q),
        baseline.unitary (baseline.hamiltonian x) =
          scaledClockHamiltonian T (endpointN q)
            (baseline.unitary x)) ∧
      baseline.IsRelationallyStationary hT baseline.stateAt ∧
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        ∃ model :
            FixedEndpointPathModel
              T (endpointN q) (Real.sqrt p),
          RelationalPathComparison
            R q T H δ p hT hsize baseline model

/--
**Universal relational local-horizon law.**

For every local radius, every target time, every strict prior window,
every positive tolerance, and every future probability, one common finite
dimension contains isospectral self-adjoint nearest-neighbor Hamiltonians
with exactly the same local prefix, arbitrarily close prior return records,
and the prescribed exact future return.  Every member is simultaneously an
exact conditional clock history and a globally stationary clock--system
history.
-/
theorem universalRelationalLocalHorizon_every_future_probability
    (R : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    UniversalRelationalLocalHorizonWitness R T H δ hT := by
  obtain ⟨q, horder, hsize, baseline, hbaseNN, hbaseSA, hall⟩ :=
    localHorizon_every_future_probability
      R T H hT hH0 hHT hδ
  refine ⟨q, horder, hsize, baseline, hbaseNN, hbaseSA,
    baseline.intertwines,
    baseline.stateAt_relationallyStationary hT, ?_⟩
  intro p hp
  obtain ⟨M, hMNN, hMSA, hintertwines, hlocal, hprior, htarget⟩ :=
    hall p hp
  refine ⟨M, hMNN, hMSA, hintertwines, hlocal,
    hprior, htarget, ?_⟩
  exact M.stateAt_relationallyStationary hT

end RHTower.ParityForecast
