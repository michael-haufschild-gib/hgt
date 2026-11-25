import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.NearHilbertOnset
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.PrescribedTolerance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonalLaw

/-! # Spectral-jet geometry of critical heights and quadratic-precision locking near 1/10

This module establishes three structural results on `criticalHeight H s`:
1. **Longitudinal and commutant jet nullity:** on maximally projective spectra,
   `criticalHeight H s` equals the eigenframe torus functional `torusCriticalHeight e V s`,
   and is invariant under nonzero time-scale rescalings, scalar energy shifts, and arbitrary
   commuting maximally projective deformations `[H₁, H₂] = 0`.
2. **Transverse unitary sensitivity and boundary regimes:** conjugating `H` by `W ∈ U(2^N)`
   changes `criticalHeight` by at most `2 ‖W - 1‖` (hence `2 ‖K‖`-Lipschitz along transverse
   flows `e^{-i u K}`), fixes `s = 0` identically, clears `13 / 125` deterministically for all
   `s ≤ 2^N / (7 * (N + 1))` and all eigenbases `V ∈ U(2^N)`, and collapses below any `ε > 0`
   at `s = 2^N * (2 * N + 1)` on an open positive-Gaussian-measure set.
3. **Scale-`2^{-Θ(N²)}` critical-height anti-concentration and direct locking:** zero gate loss
   `m_{e + δ} = m_e` is equivalent to `e ∉ jumpTolerances H δ`, whose Lebesgue measure is at
   most `2^{6N} * δ`, yielding direct universal quadratic-precision locking onto `m_{1/10}`
   under local clearance, across `1 - 2^{-Θ(N²)}` of sub-Gaussian micro-windows around `1/10`,
   and for almost every prescribed tolerance. -/

open Set Filter MeasureTheory Real Topology Matrix
open scoped Matrix.Norms.L2Operator ENNReal
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ

/-- Real nonzero rescaling of a self-adjoint register generator. -/
def scaleSelfAdjoint {N : ℕ} (c : ℝ) (H : selfAdjoint (Register N)) : selfAdjoint (Register N) :=
  ⟨(c : ℂ) • H.val, by
    rw [selfAdjoint.mem_iff, star_smul, Complex.star_def, Complex.conj_ofReal, H.2.star_eq]⟩

/-- Real identity-shift of a self-adjoint register generator. -/
def shiftSelfAdjoint {N : ℕ} (a : ℝ) (H : selfAdjoint (Register N)) : selfAdjoint (Register N) :=
  ⟨H.val + (a : ℂ) • (1 : Register N), by
    rw [selfAdjoint.mem_iff, star_add, star_smul, star_one,
      Complex.star_def, Complex.conj_ofReal, H.2.star_eq]⟩

/-- Transverse unitary conjugation `W H W*` of a self-adjoint register generator. -/
def conjSelfAdjoint {N : ℕ} (W : UGroup N) (H : selfAdjoint (Register N)) :
    selfAdjoint (Register N) :=
  ⟨W.val * H.val * star W.val, by
    rw [selfAdjoint.mem_iff, star_mul, star_mul, star_star, H.2.star_eq, mul_assoc]⟩

/-- Supremum of the projective circuit distance over the independent spectral-phase torus
in a fixed unitary eigenframe `V`. -/
def torusCriticalHeight {N d : ℕ} (e : Config N ≃ Fin (d + 1)) (V : UGroup N) (s : ℕ) : ℝ :=
  sSup (range fun θ : Fin d → UnitAddCircle =>
    Metric.infDist (projectiveSpectralMatrix e V θ) (phaseCircuitMatrixImageAtMost N s))

/-- Starting tolerances whose `δ`-shift crosses at least one critical height below the
exact synthesis cap `2^(6N)`. -/
def jumpTolerances {N : ℕ} (H : selfAdjoint (Register N)) (δ : ℝ) : Set ℝ :=
  {e : ℝ | ∃ j < 2 ^ (6 * N), criticalHeight H j ∈ Ioc e (e + δ)}

private theorem bddAbove_orbitCircuitDistance {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) :
    BddAbove (range (orbitCircuitDistance H s)) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨z, hz, C, hC, he⟩ := (hasProjectiveCircuitApproximation_iff_infDist
    (unitaryEvolution H.val t) 0 (2 : ℝ)).mpr (orbitCircuitDistance_zeroGate_lt_two H t).le
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp
    ⟨z, hz, C, hC.trans (Nat.zero_le _), he⟩

private theorem bddAbove_torusDistance {N d : ℕ} (e : Config N ≃ Fin (d + 1))
    (V : UGroup N) (s : ℕ) :
    BddAbove (range fun θ : Fin d → UnitAddCircle =>
      Metric.infDist (projectiveSpectralMatrix e V θ) (phaseCircuitMatrixImageAtMost N s)) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨θ, rfl⟩
  have hmem : (1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N) ∈
      phaseCircuitMatrixImageAtMost N s :=
    mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩
  refine (Metric.infDist_le_dist_of_mem hmem).trans ?_
  rw [dist_eq_norm, one_smul, TwoQubitCircuit.one_eval]
  have hps_unit : projectiveSpectralMatrix e V θ ∈ unitary (Register N) := by
    unfold projectiveSpectralMatrix
    refine mul_mem (mul_mem V.2 ?_) (Unitary.star_mem V.2)
    rw [Unitary.mem_iff, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    constructor <;> ext i j <;> by_cases hij : i = j
    · subst hij
      simp only [diagonal_apply_eq, one_apply_eq]
      exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
    · simp [hij]
    · subst hij
      simp only [diagonal_apply_eq, one_apply_eq]
      rw [mul_comm]
      exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
    · simp [hij]
  exact (norm_sub_le _ _).trans (by
    rw [CStarRing.norm_of_mem_unitary hps_unit, CStarRing.norm_of_mem_unitary (1 : UGroup N).2]
    norm_num)

/-- Nonzero real rescaling of the generator reparametrizes physical time and leaves
`criticalHeight` identically unchanged. -/
theorem criticalHeight_scaleSelfAdjoint {N : ℕ} (H : selfAdjoint (Register N))
    {c : ℝ} (hc : c ≠ 0) (s : ℕ) :
    criticalHeight (scaleSelfAdjoint c H) s = criticalHeight H s := by
  have hev (t : ℝ) : unitaryEvolution (scaleSelfAdjoint c H).val t =
      unitaryEvolution H.val (c * t) := by
    unfold unitaryEvolution scaleSelfAdjoint
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  have hrange : range (orbitCircuitDistance (scaleSelfAdjoint c H) s) =
      range (orbitCircuitDistance H s) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨c * t, by simp only [orbitCircuitDistance, hev]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨c⁻¹ * u, by simp only [orbitCircuitDistance, hev, mul_inv_cancel_left₀ hc]⟩
  unfold criticalHeight
  rw [hrange]

private theorem approx_unit_smul {N s : ℕ} {ε : ℝ} {X : Register N} {z : ℂ} (hz : ‖z‖ = 1) :
    HasProjectiveCircuitApproximation N ε s (z • X) ↔
      HasProjectiveCircuitApproximation N ε s X := by
  have move (Y : Register N) (a : ℂ) (ha : ‖a‖ = 1)
      (h : HasProjectiveCircuitApproximation N ε s Y) :
      HasProjectiveCircuitApproximation N ε s (a • Y) := by
    obtain ⟨c, hc, C, hC, he⟩ := h
    refine ⟨a * c, by rw [norm_mul, ha, hc, one_mul], C, hC, ?_⟩
    rwa [← smul_smul, ← smul_sub, norm_smul, ha, one_mul]
  refine ⟨fun h => ?_, move X z hz⟩
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  simpa only [smul_smul, inv_mul_cancel₀ hz0, one_smul] using
    move (z • X) z⁻¹ (by rw [norm_inv, hz, inv_one]) h

/-- Adding a real multiple of the identity multiplies the propagator by a global phase
and leaves `criticalHeight` identically unchanged. -/
theorem criticalHeight_shiftSelfAdjoint {N : ℕ} (H : selfAdjoint (Register N))
    (a : ℝ) (s : ℕ) :
    criticalHeight (shiftSelfAdjoint a H) s = criticalHeight H s := by
  have hev (t : ℝ) : unitaryEvolution (shiftSelfAdjoint a H).val t =
      Complex.exp (-(Complex.I * (t * a))) • unitaryEvolution H.val t := by
    unfold unitaryEvolution shiftSelfAdjoint
    let z : ℂ := -(Complex.I * (t * a))
    have hsplit : t • (-Complex.I • (H.val + (a : ℂ) • (1 : Register N))) =
        t • (-Complex.I • H.val) + Matrix.diagonal (fun _ : Config N => z) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq,
          Matrix.diagonal_apply_eq, Complex.real_smul, smul_eq_mul, z]
        ring
      · simp [hij]
    have hcomm : Commute (t • (-Complex.I • H.val)) (Matrix.diagonal fun _ : Config N => z) := by
      have hd : Matrix.diagonal (fun _ : Config N => z) = z • (1 : Register N) := by
        ext i j; by_cases hij : i = j <;> simp [hij]
      rw [hd]
      exact (Commute.one_right _).smul_right z
    have hexp_diag : NormedSpace.exp (Matrix.diagonal fun _ : Config N => z) =
        Complex.exp z • (1 : Register N) := by
      rw [Matrix.exp_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
          Pi.coe_exp, Complex.exp_eq_exp_ℂ, mul_one, smul_eq_mul]
      · simp [hij]
    letI : NormedAlgebra ℚ (Register N) := NormedAlgebra.restrictScalars ℚ ℂ _
    rw [hsplit, NormedSpace.exp_add_of_commute hcomm, hexp_diag, Matrix.mul_smul, mul_one]
  have hdist (t : ℝ) : orbitCircuitDistance (shiftSelfAdjoint a H) s t =
      orbitCircuitDistance H s t := by
    apply le_antisymm
    · apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      rw [hev]
      exact (approx_unit_smul (by simp [Complex.norm_exp])).mpr
        ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr le_rfl)
    · apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      exact (approx_unit_smul (z := Complex.exp (-(Complex.I * (t * a))))
        (by simp [Complex.norm_exp])).mp (hev t ▸
          (hasProjectiveCircuitApproximation_iff_infDist ..).mpr le_rfl)
  unfold criticalHeight
  rw [show orbitCircuitDistance (shiftSelfAdjoint a H) s = orbitCircuitDistance H s from funext hdist]

/-- On every Hamiltonian with maximally projective spectrum, `criticalHeight H s` depends
only on the projective eigenbasis via `torusCriticalHeight`. -/
theorem criticalHeight_eq_torusCriticalHeight {N d : ℕ}
    (e : Config N ≃ Fin (d + 1)) (H : selfAdjoint (Register N))
    (hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i)))
    (s : ℕ) :
    criticalHeight H s = torusCriticalHeight e (hermitianEigenbasisUnitary H.2.isHermitian) s := by
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  apply le_antisymm
  · refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨t, rfl⟩
    have hall : ∀ θ : Fin d → UnitAddCircle,
        HasProjectiveCircuitApproximation N (torusCriticalHeight e V s) s
          (projectiveSpectralMatrix e V θ) := fun θ =>
      (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
        (le_csSup (bddAbove_torusDistance e V s) (mem_range_self θ))
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      ((uniform_circuit_budget_iff_all_spectral_phases e H hmax s _).mpr hall t)
  · refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨θ, rfl⟩
    have hall : ∀ t : ℝ,
        HasProjectiveCircuitApproximation N (criticalHeight H s) s
          (unitaryEvolution H.val t) := fun t =>
      (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
        (le_csSup (bddAbove_orbitCircuitDistance H s) (mem_range_self t))
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      ((uniform_circuit_budget_iff_all_spectral_phases e H hmax s _).mp hall θ)

private theorem maximallyProjective_diagonal_in_eigenbasis {N d : ℕ}
    (e : Config N ≃ Fin (d + 1)) (V : UGroup N) (H : selfAdjoint (Register N))
    (d₂ : Config N → ℝ)
    (hH : H.val = V.val * Matrix.diagonal (fun i => (d₂ i : ℂ)) * star V.val)
    (hmax : MaximallyProjectiveEnergy (fun i => d₂ (e.symm i))) (s : ℕ) :
    criticalHeight H s = torusCriticalHeight e V s := by
  have hev (t : ℝ) : unitaryEvolution H.val t =
      Complex.exp (-(Complex.I * (t * d₂ (e.symm 0)))) •
        projectiveSpectralMatrix e V
          (RHTower.projectivePhysicalPhaseFlow (fun i => d₂ (e.symm i)) t) := by
    rw [hH, unitaryEvolution_conj_diagonal V.val V.2 d₂ t]
    let anchor : ℂ := Complex.exp (-(Complex.I * (t * d₂ (e.symm 0))))
    have hdiag : Matrix.diagonal (fun i : Config N =>
        Complex.exp (-(Complex.I * (t * d₂ i)))) =
        anchor • Matrix.diagonal (fun q : Config N =>
          fourier 1 (RHTower.zeroAnchoredPhase d
            (RHTower.projectivePhysicalPhaseFlow (fun i => d₂ (e.symm i)) t) (e q))) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.diagonal_apply_eq]
        simp only [smul_eq_mul]
        generalize hr : e i = r
        rcases Fin.eq_zero_or_eq_succ r with hzero | ⟨k, hsucc⟩
        · rw [hzero] at hr ⊢
          have hi : i = e.symm 0 := e.injective (by simpa using hr)
          simp [RHTower.zeroAnchoredPhase, anchor, hi]
        · rw [hsucc] at hr ⊢
          rw [RHTower.fourier_projectiveChoiPhase_eq_exp]
          have hi : i = e.symm k.succ := e.injective (by simpa using hr)
          rw [hi]
          unfold anchor RHTower.zeroProjectiveFrequency
          rw [← Complex.exp_add]
          congr 1
          simp
          ring
      · simp [hij]
    rw [hdiag, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  let Φ := RHTower.projectivePhysicalPhaseFlowHom (fun i => d₂ (e.symm i))
  have hiff (ε : ℝ) :
      (∀ t : ℝ, HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val t)) ↔
        ∀ θ : Fin d → UnitAddCircle, HasProjectiveCircuitApproximation N ε s
          (projectiveSpectralMatrix e V θ) := by
    let A := projectiveContinuousCircuitCaptureTarget e V s ε
    have ht (t : ℝ) : HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val t) ↔
        Φ t ∈ A := by
      rw [hev t]
      exact (approx_unit_smul (by simp [Complex.norm_exp])).trans
        (mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε _).symm
    constructor
    · intro h θ
      have hsub : range Φ ⊆ A := by rintro _ ⟨t, rfl⟩; exact (ht t).mp (h t)
      exact (mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε θ).mp
        (closure_minimal hsub (isClosed_projectiveContinuousCircuitCaptureTarget e V s ε)
          (RHTower.denseRange_projectivePhysicalPhaseFlowHom _ hmax θ))
    · intro h t
      exact (ht t).mpr ((mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε _).mpr (h _))
  apply le_antisymm
  · refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨t, rfl⟩
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      ((hiff _).mpr (fun θ => (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
        (le_csSup (bddAbove_torusDistance e V s) (mem_range_self θ))) t)
  · refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨θ, rfl⟩
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      ((hiff _).mp (fun t => (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
        (le_csSup (bddAbove_orbitCircuitDistance H s) (mem_range_self t))) θ)

/-- Commutant / longitudinal rigidity: any two commuting self-adjoint generators with
maximally projective spectra have identical `criticalHeight` at every gate budget. -/
theorem criticalHeight_eq_of_commute {N d : ℕ}
    (e : Config N ≃ Fin (d + 1)) (H₁ H₂ : selfAdjoint (Register N))
    (hmax₁ : MaximallyProjectiveEnergy (fun i => H₁.2.isHermitian.eigenvalues (e.symm i)))
    (hmax₂ : MaximallyProjectiveEnergy (fun i => H₂.2.isHermitian.eigenvalues (e.symm i)))
    (hcomm : Commute H₁.val H₂.val) (s : ℕ) :
    criticalHeight H₁ s = criticalHeight H₂ s := by
  classical
  let V₁ := hermitianEigenbasisUnitary H₁.2.isHermitian
  let E₁ := H₁.2.isHermitian.eigenvalues
  let E₂ := H₂.2.isHermitian.eigenvalues
  have hinj₁ : Function.Injective E₁ := by
    intro a b hab
    exact e.injective (hmax₁.injective (by simpa only [E₁, Equiv.symm_apply_apply] using hab))
  have hinj₂ : Function.Injective E₂ := by
    intro a b hab
    exact e.injective (hmax₂.injective (by simpa only [E₂, Equiv.symm_apply_apply] using hab))
  let M : Register N := star V₁.val * H₂.val * V₁.val
  have hH₁_diag : star V₁.val * H₁.val * V₁.val = Matrix.diagonal (fun i => (E₁ i : ℂ)) := by
    have hspec := isHermitian_eq_conj_diagonal H₁.2.isHermitian
    change H₁.val = V₁.val * Matrix.diagonal (fun i => (E₁ i : ℂ)) * star V₁.val at hspec
    rw [hspec]
    exact star_conj_cancel V₁.2 _
  have hM_comm : Matrix.diagonal (fun i => (E₁ i : ℂ)) * M =
      M * Matrix.diagonal (fun i => (E₁ i : ℂ)) := by
    rw [← hH₁_diag]
    dsimp only [M]
    have hV : V₁.val * star V₁.val = 1 := (Unitary.mem_iff.mp V₁.2).2
    calc (star V₁.val * H₁.val * V₁.val) * (star V₁.val * H₂.val * V₁.val)
        = star V₁.val * H₁.val * (V₁.val * star V₁.val) * H₂.val * V₁.val := by
            simp only [mul_assoc]
      _ = star V₁.val * (H₁.val * H₂.val) * V₁.val := by
            rw [hV, mul_one]; simp only [mul_assoc]
      _ = star V₁.val * (H₂.val * H₁.val) * V₁.val := by rw [hcomm.eq]
      _ = star V₁.val * H₂.val * (V₁.val * star V₁.val) * H₁.val * V₁.val := by
            rw [hV, mul_one]; simp only [mul_assoc]
      _ = (star V₁.val * H₂.val * V₁.val) * (star V₁.val * H₁.val * V₁.val) := by
            simp only [mul_assoc]
  have hM_herm : M.IsHermitian := by
    rw [Matrix.IsHermitian, ← star_eq_conjTranspose]
    dsimp only [M]
    rw [star_mul, star_mul, star_star, H₂.2.star_eq, mul_assoc]
  let d₂ : Config N → ℝ := fun i => (M i i).re
  have hM_eq : M = Matrix.diagonal (fun i => (d₂ i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      have hself : star (M i i) = M i i := by
        simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hM_herm.eq i) i
      exact Complex.ext rfl (by
        have him := congrArg Complex.im hself
        simp only [Complex.star_def, Complex.conj_im] at him
        rw [Complex.ofReal_im]
        linarith)
    · rw [Matrix.diagonal_apply_ne _ hij]
      have hentry := congrArg (fun A : Register N => A i j) hM_comm
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
      have hzero : ((E₁ i : ℂ) - (E₁ j : ℂ)) * M i j = 0 := by linear_combination hentry
      refine (mul_eq_zero.mp hzero).resolve_left ?_
      exact sub_ne_zero.mpr (fun heq => hij (hinj₁ (Complex.ofReal_injective heq)))
  have hH₂_conj : H₂.val = V₁.val * Matrix.diagonal (fun i => (d₂ i : ℂ)) * star V₁.val := by
    have hV : V₁.val * star V₁.val = 1 := (Unitary.mem_iff.mp V₁.2).2
    calc H₂.val = (V₁.val * star V₁.val) * H₂.val * (V₁.val * star V₁.val) := by
            rw [hV, one_mul, mul_one]
      _ = V₁.val * M * star V₁.val := by dsimp only [M]; simp only [mul_assoc]
      _ = V₁.val * Matrix.diagonal (fun i => (d₂ i : ℂ)) * star V₁.val := by rw [hM_eq]
  have hchar : (Matrix.diagonal fun i => (d₂ i : ℂ)).charpoly =
      (Matrix.diagonal fun j => (E₂ j : ℂ)).charpoly := by
    have hc₁ : M.charpoly = H₂.val.charpoly := by
      dsimp only [M]
      rw [Matrix.charpoly_mul_comm, ← mul_assoc, (Unitary.mem_iff.mp V₁.2).2, one_mul]
    let V₂ := hermitianEigenbasisUnitary H₂.2.isHermitian
    have hspec₂ : H₂.val = V₂.val * Matrix.diagonal (fun j => (E₂ j : ℂ)) * star V₂.val :=
      isHermitian_eq_conj_diagonal H₂.2.isHermitian
    have hc₂ : H₂.val.charpoly = (Matrix.diagonal fun j => (E₂ j : ℂ)).charpoly := by
      rw [hspec₂, Matrix.charpoly_mul_comm, ← mul_assoc, (Unitary.mem_iff.mp V₂.2).1, one_mul]
    rw [← hM_eq, hc₁, hc₂]
  have hspec_rev : ∀ j, ∃ i, E₂ j = d₂ i := by
    intro j
    have hroot : Polynomial.IsRoot (Matrix.diagonal fun k => (E₂ k : ℂ)).charpoly (E₂ j : ℂ) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mp (by rw [spectrum_diagonal]; exact ⟨j, rfl⟩)
    rw [← hchar, ← Matrix.mem_spectrum_iff_isRoot_charpoly, spectrum_diagonal] at hroot
    obtain ⟨i, hi⟩ := hroot
    exact ⟨i, Complex.ofReal_injective hi.symm⟩
  choose ψ hψ using hspec_rev
  have hψ_inj : Function.Injective ψ := fun a b hab =>
    hinj₂ (by rw [hψ a, hψ b, hab])
  let σ : Config N ≃ Config N := Equiv.ofBijective ψ ⟨hψ_inj, Finite.injective_iff_surjective.mp hψ_inj⟩
  let perm₂ : Config N ≃ Config N := σ.symm
  have hd₂_max : MaximallyProjectiveEnergy (fun i => d₂ (e.symm i)) := by
    have heq : (fun i => d₂ (e.symm i)) = (fun j => E₂ (e.symm j)) ∘ (e.symm.trans (perm₂.trans e)) := by
      funext i
      simp only [Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
      have h1 : ψ (perm₂ (e.symm i)) = e.symm i := σ.apply_symm_apply (e.symm i)
      exact ((hψ (perm₂ (e.symm i))).trans (congrArg d₂ h1)).symm
    rw [heq]
    exact maximallyProjectiveEnergy_equiv _ hmax₂
  rw [criticalHeight_eq_torusCriticalHeight e H₁ hmax₁ s,
    maximallyProjective_diagonal_in_eigenbasis e V₁ H₂ d₂ hH₂_conj hd₂_max s]

/-- Propagator covariance under transverse unitary conjugation `W H W*`. -/
theorem unitaryEvolution_conjSelfAdjoint {N : ℕ} (W : UGroup N)
    (H : selfAdjoint (Register N)) (t : ℝ) :
    unitaryEvolution (conjSelfAdjoint W H).val t =
      W.val * unitaryEvolution H.val t * star W.val := by
  have hinv : W.val⁻¹ = star W.val := inv_eq_star_of_mem_unitary W.2
  have hunit : IsUnit W.val :=
    ⟨⟨W.val, star W.val, (Unitary.mem_iff.mp W.2).2, (Unitary.mem_iff.mp W.2).1⟩, rfl⟩
  change unitaryEvolution (W.val * H.val * star W.val) t = _
  rw [← hinv, unitaryEvolution_conj W.val H.val hunit t]

/-- Transverse unitary conjugation `H ↦ W H W*` changes `criticalHeight` by at most
`2 ‖W - 1‖` uniformly across all gate budgets. -/
theorem abs_criticalHeight_conjSelfAdjoint_sub_le {N : ℕ} (W : UGroup N)
    (H : selfAdjoint (Register N)) (s : ℕ) :
    |criticalHeight (conjSelfAdjoint W H) s - criticalHeight H s| ≤ 2 * ‖W.val - 1‖ := by
  have step (U : UGroup N) (K : selfAdjoint (Register N)) :
      criticalHeight (conjSelfAdjoint U K) s ≤ criticalHeight K s + 2 * ‖U.val - 1‖ := by
    refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨t, rfl⟩
    let X := unitaryEvolution K.val t
    have hX : ‖X‖ ≤ 1 := (CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary K.2 t)).le
    have hU : ‖U.val‖ ≤ 1 := (CStarRing.norm_of_mem_unitary U.2).le
    have hsplit : U.val * X * star U.val - X =
        (U.val - 1) * X * star U.val + X * star (U.val - 1) := by
      rw [star_sub, star_one]; noncomm_ring
    have hnorm : ‖U.val * X * star U.val - X‖ ≤ 2 * ‖U.val - 1‖ := by
      rw [hsplit]
      have h₁ : ‖(U.val - 1) * X * star U.val‖ ≤ ‖U.val - 1‖ := calc
        ‖(U.val - 1) * X * star U.val‖ ≤ ‖(U.val - 1) * X‖ * ‖star U.val‖ := norm_mul_le _ _
        _ ≤ (‖U.val - 1‖ * 1) * 1 := mul_le_mul
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hX (norm_nonneg _)))
            (by simpa only [norm_star] using hU) (norm_nonneg _) (by positivity)
        _ = ‖U.val - 1‖ := by ring
      have h₂ : ‖X * star (U.val - 1)‖ ≤ ‖U.val - 1‖ := calc
        ‖X * star (U.val - 1)‖ ≤ ‖X‖ * ‖star (U.val - 1)‖ := norm_mul_le _ _
        _ ≤ 1 * ‖U.val - 1‖ := mul_le_mul hX (by rw [norm_star]) (norm_nonneg _) zero_le_one
        _ = ‖U.val - 1‖ := one_mul _
      linarith only [norm_add_le ((U.val - 1) * X * star U.val) (X * star (U.val - 1)), h₁, h₂]
    have hinf : orbitCircuitDistance (conjSelfAdjoint U K) s t ≤
        orbitCircuitDistance K s t + 2 * ‖U.val - 1‖ := by
      unfold orbitCircuitDistance
      rw [unitaryEvolution_conjSelfAdjoint]
      refine (Metric.infDist_le_infDist_add_dist (y := X)).trans ?_
      rw [dist_eq_norm]
      exact add_le_add le_rfl hnorm
    exact hinf.trans (add_le_add (le_csSup (bddAbove_orbitCircuitDistance K s) (mem_range_self t)) le_rfl)
  have hinv_conj : conjSelfAdjoint W⁻¹ (conjSelfAdjoint W H) = H := by
    apply Subtype.ext
    change W⁻¹.val * (W.val * H.val * star W.val) * star W⁻¹.val = H.val
    have hW1 : star W.val * W.val = 1 := (Unitary.mem_iff.mp W.2).1
    have hinv_val : W⁻¹.val = star W.val := rfl
    rw [hinv_val, star_star]
    calc star W.val * (W.val * H.val * star W.val) * W.val
        = (star W.val * W.val) * H.val * (star W.val * W.val) := by simp only [mul_assoc]
      _ = H.val := by rw [hW1, one_mul, mul_one]
  have hnorm_inv : ‖W⁻¹.val - 1‖ = ‖W.val - 1‖ := by
    have h : W⁻¹.val - (1 : Register N) = star (W.val - 1) := by
      rw [star_sub, star_one]; rfl
    rw [h, norm_star]
  have h1 := step W H
  have h2 := step W⁻¹ (conjSelfAdjoint W H)
  rw [hinv_conj, hnorm_inv] at h2
  exact abs_sub_le_iff.mpr ⟨by linarith only [h1], by linarith only [h2]⟩

/-- Along any self-adjoint transverse generator `K`, rotating the eigenbasis by `e^{-i u K}`
moves `criticalHeight` with Lipschitz constant `2 ‖K‖`. -/
theorem abs_criticalHeight_transverseFlow_sub_le {N : ℕ}
    (K H : selfAdjoint (Register N)) (u v : ℝ) (s : ℕ) :
    let W (r : ℝ) : UGroup N := ⟨unitaryEvolution K.val r, unitaryEvolution_mem_unitary K.2 r⟩
    |criticalHeight (conjSelfAdjoint (W u) H) s -
      criticalHeight (conjSelfAdjoint (W v) H) s| ≤ 2 * ‖K.val‖ * |u - v| := by
  intro W
  have hcomp : conjSelfAdjoint (W u) H = conjSelfAdjoint (W (u - v)) (conjSelfAdjoint (W v) H) := by
    apply Subtype.ext
    have hmul : unitaryEvolution K.val (u - v) * unitaryEvolution K.val v =
        unitaryEvolution K.val u := unitaryEvolution_sub_mul K u v
    dsimp only [conjSelfAdjoint, W]
    calc unitaryEvolution K.val u * H.val * star (unitaryEvolution K.val u)
        = (unitaryEvolution K.val (u - v) * unitaryEvolution K.val v) * H.val *
            star (unitaryEvolution K.val (u - v) * unitaryEvolution K.val v) := by rw [hmul]
      _ = unitaryEvolution K.val (u - v) *
            (unitaryEvolution K.val v * H.val * star (unitaryEvolution K.val v)) *
            star (unitaryEvolution K.val (u - v)) := by rw [star_mul]; simp only [mul_assoc]
  rw [hcomp]
  refine (abs_criticalHeight_conjSelfAdjoint_sub_le (W (u - v)) _ s).trans ?_
  have hd : ‖(W (u - v)).val - 1‖ ≤ ‖K.val‖ * |u - v| := by
    have h0 : unitaryEvolution K.val 0 = 1 := by simp [unitaryEvolution]
    simpa only [W, h0, sub_zero] using norm_unitaryEvolution_time_sub_le K.2 (u - v) 0
  linarith only [mul_le_mul_of_nonneg_left hd two_pos.le]

/-- Central atom at `s = 0`: every transverse unitary conjugation leaves `criticalHeight H 0`
identically invariant. -/
theorem criticalHeight_conjSelfAdjoint_zero {N : ℕ} (W : UGroup N)
    (H : selfAdjoint (Register N)) :
    criticalHeight (conjSelfAdjoint W H) 0 = criticalHeight H 0 := by
  have heval_zero (C : TwoQubitCircuit N) (hC : C.gateCount ≤ 0) :
      (C.eval : Register N) = 1 := by
    have h0 : C.gateCount = 0 := Nat.eq_zero_of_le_zero hC
    unfold TwoQubitCircuit.eval TwoQubitArchitecture.contraction
    have hnil : (List.ofFn fun i : Fin C.gateCount => C.architecture.gateLift i (C.gates i)) = [] :=
      List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
        obtain ⟨i, _⟩ := List.mem_ofFn.mp hx
        exact Fin.elim0 (h0 ▸ i)
    rw [hnil]
    rfl
  have hdist (t : ℝ) : orbitCircuitDistance (conjSelfAdjoint W H) 0 t =
      orbitCircuitDistance H 0 t := by
    apply le_antisymm
    · apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      obtain ⟨c, hc, C, hC, herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist
        (unitaryEvolution H.val t) 0 _).mpr (le_rfl : orbitCircuitDistance H 0 t ≤ _)
      refine ⟨c, hc, TwoQubitCircuit.one N, le_rfl, ?_⟩
      rw [unitaryEvolution_conjSelfAdjoint, TwoQubitCircuit.one_eval, Submonoid.coe_one]
      rw [heval_zero C hC] at herr
      have hconj : W.val * unitaryEvolution H.val t * star W.val - c • (1 : Register N) =
          W.val * (unitaryEvolution H.val t - c • (1 : Register N)) * star W.val := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          mul_one, (Unitary.mem_iff.mp W.2).2]
      rw [hconj, l2_opNorm_unitary_conj_eq W.2]
      exact herr
    · apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      obtain ⟨c, hc, C, hC, herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist
        (unitaryEvolution (conjSelfAdjoint W H).val t) 0 _).mpr
          (le_rfl : orbitCircuitDistance (conjSelfAdjoint W H) 0 t ≤ _)
      refine ⟨c, hc, TwoQubitCircuit.one N, le_rfl, ?_⟩
      rw [TwoQubitCircuit.one_eval, Submonoid.coe_one]
      rw [unitaryEvolution_conjSelfAdjoint, heval_zero C hC] at herr
      have hconj : W.val * (unitaryEvolution H.val t - c • (1 : Register N)) * star W.val =
          W.val * unitaryEvolution H.val t * star W.val - c • (1 : Register N) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          mul_one, (Unitary.mem_iff.mp W.2).2]
      rw [← l2_opNorm_unitary_conj_eq W.2, hconj]
      exact herr
  unfold criticalHeight
  rw [show orbitCircuitDistance (conjSelfAdjoint W H) 0 = orbitCircuitDistance H 0 from funext hdist]

/-- Deterministic sub-Hilbert clearance across all eigenframes: for all sufficiently large `N`,
every unitary eigenbasis `V ∈ U(2^N)` and every budget `s ≤ 2^N / (7 * (N + 1))` satisfy
`13 / 125 < torusCriticalHeight e V s`. -/
theorem eventually_torusCriticalHeight_gt_thirteen_125 :
    ∀ᶠ N : ℕ in atTop, ∀ (d : ℕ) (e : Config N ≃ Fin (d + 1)) (V : UGroup N) (s : ℕ),
      s ≤ 2 ^ N / (7 * (N + 1)) → 13 / 125 < torusCriticalHeight e V s := by
  obtain ⟨h13_mem, h13_log⟩ := thirteen_125_entropy
  obtain ⟨hx, htol⟩ := physicalArc_full h13_mem
  have hcon : ContinuousAt (fun z : ℝ => Real.log z + 32 * Real.log 2 / (7 : ℕ))
      (physicalArc (13 / 125)) :=
    (Real.continuousAt_log hx.1.ne').add continuousAt_const
  obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff.mp (hcon.eventually_lt_const h13_log)
  let y := physicalArc (13 / 125) + min (1 - physicalArc (13 / 125)) δ / 2
  have hmin : 0 < min (1 - physicalArc (13 / 125)) δ := lt_min (sub_pos.mpr hx.2) hδ
  have hxy : physicalArc (13 / 125) < y := by dsimp only [y]; linarith only [hmin]
  have hy1 : y < 1 := by dsimp only [y]; linarith only [min_le_left (1 - physicalArc (13 / 125)) δ, hmin]
  have hy_mem : y ∈ Ioo (0 : ℝ) 1 := ⟨hx.1.trans hxy, hy1⟩
  have hyb : Real.log y + 32 * Real.log 2 / (7 : ℕ) < Real.log (4 / 5) := hsub (by
    rw [Real.dist_eq, show y - physicalArc (13 / 125) = min (1 - physicalArc (13 / 125)) δ / 2 by
      dsimp only [y]; ring, abs_of_pos (half_pos hmin)]
    linarith only [min_le_right (1 - physicalArc (13 / 125)) δ, hmin])
  let η := (zeroGateArcTolerance y - 13 / 125) / 2
  have hη : 0 < η := half_pos (sub_pos.mpr (htol ▸ strictMonoOn_zeroGateArcTolerance_full
    ⟨hx.1.le, hx.2.le⟩ ⟨hy_mem.1.le, hy_mem.2.le⟩ hxy))
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * Real.pi / η)
  have hm' : 0 < m := Nat.cast_pos.mp ((div_pos Real.two_pi_pos hη).trans hm)
  have hgrid : 2 * Real.pi / m ≤ η := (div_le_iff₀ (Nat.cast_pos.mpr hm')).mpr
    (by simpa only [mul_comm η] using ((div_lt_iff₀ hη).mp hm).le)
  have hprice : (13 / 125 : ℝ) + η + 2 * Real.pi / m ≤ zeroGateArcTolerance y := by
    dsimp only [η] at hgrid ⊢
    linarith only [hgrid]
  filter_upwards [positive_budget_exponent 7 (by decide) η y (4 / 5) hη hy_mem.1 (by norm_num) hyb,
    eventually_ge_atTop (max m 1)] with N hpos_exp hNm d e V s hs
  let B₇ := 2 ^ N / (7 * (N + 1))
  have hDpos : 0 < 2 ^ N := Nat.two_pow_pos N
  have hmD : (m : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) :=
    by exact_mod_cast (le_max_left m 1).trans (hNm.trans (Nat.lt_two_pow_self (n := N)).le)
  have hyD : y ^ (2 ^ N) ≤ y ^ (2 ^ N - 1) := by
    calc y ^ (2 ^ N) = y ^ (2 ^ N - 1) * y := by rw [← pow_succ, Nat.sub_add_cancel hDpos]
      _ ≤ y ^ (2 ^ N - 1) * 1 := mul_le_mul_of_nonneg_left hy_mem.2.le (pow_nonneg hy_mem.1.le _)
      _ = _ := mul_one _
  have hmy : (m : ℝ) * y ^ (2 ^ N) ≤ zeroGateArcDensity (2 ^ N) y :=
    mul_le_mul hmD hyD (pow_nonneg hy_mem.1.le _) (Nat.cast_nonneg _)
  let E : ℝ := ((B₇ : ℝ) + 1) * ((((N : ℝ) + 1) ^ 2) * (1 + 4 * (B₇ : ℝ) / η) ^ 32) ^ B₇
  have hvol := UnitaryBalls.circuit_volume_bound e V B₇ m hm' hη ⟨hy_mem.1.le, hy_mem.2⟩ hprice
  have hlt_one : volume.real (projectiveContinuousCircuitCaptureTarget e V B₇ (13 / 125)) < 1 := by
    have h1 : (m : ℝ) * E * y ^ (2 ^ N) = E * ((m : ℝ) * y ^ (2 ^ N)) := by ring
    change _ ≤ (m : ℝ) * E * y ^ (2 ^ N) at hvol
    have hle := (hvol.trans_eq h1).trans_lt
      ((mul_le_mul_of_nonneg_left hmy (by dsimp only [E]; positivity)).trans_lt hpos_exp)
    exact hle.trans (pow_lt_one₀ (by norm_num) (by norm_num) hDpos.ne')
  have hprob : IsProbabilityMeasure (volume : Measure (Fin d → UnitAddCircle)) := by
    rw [← finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume (d := Fin d)]
    infer_instance
  have hne_univ : projectiveContinuousCircuitCaptureTarget e V B₇ (13 / 125) ≠ univ := fun heq => by
    rw [heq, probReal_univ] at hlt_one
    exact lt_irrefl _ hlt_one
  obtain ⟨θ, hθ⟩ := nonempty_compl.mpr hne_univ
  have hgt : 13 / 125 < Metric.infDist (projectiveSpectralMatrix e V θ)
      (phaseCircuitMatrixImageAtMost N s) := by
    by_contra! hle
    obtain ⟨c, hc, C, hC, herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist
      (projectiveSpectralMatrix e V θ) s (13 / 125 : ℝ)).mpr hle
    exact hθ ((mem_projectiveContinuousCircuitCaptureTarget_iff e V B₇ (13 / 125) θ).mpr
      ⟨c, hc, C, hC.trans hs, herr⟩)
  exact hgt.trans_le (le_csSup (bddAbove_torusDistance e V s) (mem_range_self θ))

/-- Above the exact synthesis cap `(4N + 1)(2N + 2)4^N`, `criticalHeight H s` vanishes
identically for every self-adjoint generator. -/
theorem criticalHeight_eq_zero_of_exact_cap {N s : ℕ} (hN : 2 ≤ N)
    (H : selfAdjoint (Register N)) (hs : (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2 ≤ s) :
    criticalHeight H s = 0 := by
  apply le_antisymm
  · refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨t, rfl⟩
    obtain ⟨z, hz, C, hC, he⟩ := (DiagonalSynthesis.exact_evolution_gate_cap hN H t).approx le_rfl
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z, hz, C, hC.trans hs, he⟩
  · exact (Metric.infDist_nonneg).trans
      (le_csSup (bddAbove_orbitCircuitDistance H s) (mem_range_self 0))

/-- Open positive-Gaussian-measure collapse of `criticalHeight` at the diagonal budget
`2^(n+2) * (2*(n+2) + 1)` below any positive tolerance `ε`. -/
theorem gaussian_open_criticalHeight_collapse (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ O : Set (PrescribedTimes.PrefixIndex n → ℝ), IsOpen O ∧
      0 < (Measure.pi fun _ : PrescribedTimes.PrefixIndex n => ProbabilityTheory.gaussianReal 0 1) O ∧
      ∀ x ∈ O, criticalHeight (PrescribedTimes.prefixGenerator n x)
        (2 ^ (n + 2) * (2 * (n + 2) + 1)) ≤ ε := by
  obtain ⟨O, hO, hpos, hcap⟩ := WeakBonds.gaussian_open_all_time_gate_cap n hε
  refine ⟨O, hO, hpos, fun x hx => csSup_le (range_nonempty _) ?_⟩
  rintro _ ⟨t, rfl⟩
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp (hcap x hx t)

private theorem jumpTolerances_eq_biUnion {N : ℕ} (H : selfAdjoint (Register N)) (δ : ℝ) :
    jumpTolerances H δ =
      ⋃ j ∈ Finset.range (2 ^ (6 * N)), Ico (criticalHeight H j - δ) (criticalHeight H j) := by
  ext e
  simp only [jumpTolerances, mem_setOf_eq, Finset.mem_range, mem_iUnion, exists_prop,
    mem_Ioc, mem_Ico]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]

/-- The critical-height jump locus at scale `δ` is Borel measurable and has Lebesgue measure
at most `2^(6N) * δ` deterministically for every generator `H`. -/
theorem measurableSet_jumpTolerances {N : ℕ} (H : selfAdjoint (Register N)) (δ : ℝ) :
    MeasurableSet (jumpTolerances H δ) := by
  rw [jumpTolerances_eq_biUnion]
  exact Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Ico

private theorem measure_jumpTolerances_ne_top {N : ℕ} (H : selfAdjoint (Register N)) (δ : ℝ) :
    volume (jumpTolerances H δ) ≠ ⊤ := by
  rw [jumpTolerances_eq_biUnion]
  exact ((measure_biUnion_finset_le _ _).trans_lt
    (ENNReal.sum_lt_top.mpr fun _ _ =>
      (measure_ne_top_of_subset Ico_subset_Icc_self measure_Icc_lt_top.ne).lt_top)).ne

theorem volume_jumpTolerances_le {N : ℕ} (H : selfAdjoint (Register N)) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume.real (jumpTolerances H δ) ≤ (2 : ℝ) ^ (6 * N) * δ := by
  rw [jumpTolerances_eq_biUnion]
  refine (measureReal_biUnion_finset_le _ _).trans_eq ?_
  calc ∑ j ∈ Finset.range (2 ^ (6 * N)),
          volume.real (Ico (criticalHeight H j - δ) (criticalHeight H j))
      = ∑ _j ∈ Finset.range (2 ^ (6 * N)), δ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Real.volume_real_Ico_of_le (sub_le_self _ hδ), sub_sub_cancel]
    _ = (2 : ℝ) ^ (6 * N) * δ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- A gate budget falls strictly short of the recurrent orbit maximum at `e` precisely when
its critical height exceeds `e`. -/
theorem below_criticalHeight_iff {N m : ℕ} (H : selfAdjoint (Register N)) {e : ℝ}
    (hm : IsRecurrentOrbitCircuitMaximumAt H e m) (j : ℕ) :
    e < criticalHeight H j ↔ j < m := by
  constructor
  · intro h
    by_contra! hj
    refine h.not_ge (csSup_le (range_nonempty _) ?_)
    rintro _ ⟨t, rfl⟩
    obtain ⟨z, hz, C, hC, herr⟩ := hm.1 t
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z, hz, C, hC.trans hj, herr⟩
  · intro hj
    obtain ⟨t, ht⟩ := required_at_some_date hm
    have hh : e < orbitCircuitDistance H j t := lt_of_not_ge fun h =>
      hj.not_ge (ht j ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr h))
    exact hh.trans_le (le_csSup (bddAbove_orbitCircuitDistance H j) (mem_range_self t))

/-- Exact zero-drop equivalence: across `[e, e + δ]`, the recurrent orbit maximum stays
unchanged if and only if no critical height lies in `(e, e + δ]`, if and only if
`e ∉ jumpTolerances H δ`. -/
theorem maximum_eq_iff_criticalHeight_clearance {N m n : ℕ} (hN : 2 ≤ N)
    (H : selfAdjoint (Register N)) {e δ : ℝ} (he : 0 ≤ e) (hδ : 0 ≤ δ)
    (hm : IsRecurrentOrbitCircuitMaximumAt H e m)
    (hn : IsRecurrentOrbitCircuitMaximumAt H (e + δ) n) :
    (m = n ↔ ∀ j : ℕ, criticalHeight H j ∉ Ioc e (e + δ)) ∧
      (m = n ↔ e ∉ jumpTolerances H δ) := by
  have hnm : n ≤ m := by
    obtain ⟨t, ht⟩ := required_at_some_date hn
    obtain ⟨z, hz, C, hC, herr⟩ := hm.1 t
    exact ht m ⟨z, hz, C, hC, herr.trans (le_add_of_nonneg_right hδ)⟩
  have hcap : m ≤ 2 ^ (6 * N) := by
    obtain ⟨t, ht⟩ := required_at_some_date hm
    have hpow_le : (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2 ≤ 2 ^ (6 * N) := by
      have h1 (k : ℕ) : k + 1 ≤ 2 ^ k := by
        induction k with
        | zero => decide
        | succ k ih => rw [pow_succ]; omega
      have hN1 := h1 N
      calc (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2
          ≤ (4 * 2 ^ N) * (2 * 2 ^ N) * (2 ^ N) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
        _ = 2 ^ (3 + N + N + N * 2) := by rw [pow_add, pow_add, pow_add, pow_mul]; ring
        _ ≤ 2 ^ (6 * N) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (ht _ ((DiagonalSynthesis.exact_evolution_gate_cap hN H t).approx he)).trans hpow_le
  have h1 : m = n ↔ ∀ j : ℕ, criticalHeight H j ∉ Ioc e (e + δ) := by
    constructor
    · rintro rfl j ⟨hlo, hhi⟩
      have hlt : j < m := (below_criticalHeight_iff H hm j).mp hlo
      have hlt' : j < m := hlt
      exact hhi.not_gt ((below_criticalHeight_iff H hn j).mpr hlt')
    · intro hclear
      rcases eq_or_lt_of_le hnm with rfl | hlt
      · rfl
      · obtain ⟨_, hlo, hhi⟩ := criticalHeight_of_maximum_drop hN H he hm hn hlt
        exact (hclear n ⟨hlo, hhi⟩).elim
  refine ⟨h1, h1.trans ?_⟩
  constructor
  · rintro hall ⟨j, _, hj⟩
    exact hall j hj
  · intro hno j hj
    have hlt : j < 2 ^ (6 * N) := ((below_criticalHeight_iff H hm j).mp hj.1).trans_le hcap
    exact hno ⟨j, hlt, hj⟩

private theorem quad_bits_growth {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      let b := ⌊δ ^ 2 * (N : ℝ) ^ 2⌋₊
      16 ≤ b ∧ 6 * N + 2 + b / 2 ≤ b ∧ b / 4 + 4 ≤ b / 2 ∧
        (N : ℝ) ≤ 3 * δ ^ 2 * (N : ℝ) ^ 2 ∧ b ≤ 2 ^ N := by
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt (max (20 / δ ^ 2) (1 / (3 * δ ^ 2)))
  have hlim : Tendsto (fun N : ℕ => δ ^ 2 * (N : ℝ) ^ 2 / (2 : ℝ) ^ N) atTop (𝓝 0) := by
    simpa only [mul_div_assoc', mul_zero] using
      (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)).const_mul (δ ^ 2)
  filter_upwards [eventually_ge_atTop (M₁ + 20),
    hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hNM hN2
  intro b
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hM_lt : max (20 / δ ^ 2) (1 / (3 * δ ^ 2)) < (N : ℝ) :=
    hM₁.trans_le (by exact_mod_cast (by omega : M₁ ≤ N))
  have h20 : 20 < (N : ℝ) * δ ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hδ)).mp ((le_max_left _ _).trans_lt hM_lt)
  have h20N : 20 * (N : ℝ) < δ ^ 2 * (N : ℝ) ^ 2 := by nlinarith only [h20, hN_pos]
  have h20_nat : 20 * N ≤ b := Nat.le_floor (by exact_mod_cast h20N.le)
  have h3 : 1 < (N : ℝ) * (3 * δ ^ 2) :=
    (div_lt_iff₀ (by positivity)).mp ((le_max_right _ _).trans_lt hM_lt)
  have hfloor_le : (b : ℝ) ≤ (2 : ℝ) ^ N :=
    (Nat.floor_le (by positivity)).trans (((div_lt_iff₀ (by positivity)).mp hN2).le.trans_eq (one_mul _))
  refine ⟨by omega, by omega, by omega, by nlinarith only [h3, hN_pos], by exact_mod_cast hfloor_le⟩

private theorem quad_sim_of_binary {N b : ℕ} {γ α : ℝ} (hγα : γ < α) (hα : α < 1)
    (H : selfAdjoint (Register N))
    (hN_le_3 : (N : ℝ) ≤ 3 * (((α - γ) / 12) ^ 2) * (N : ℝ) ^ 2)
    (hb_eq : b = ⌊(((α - γ) / 12) ^ 2) * (N : ℝ) ^ 2⌋₊)
    (henv1 : (N : ℝ) * (1 + (2 : ℝ) ^ (γ * (N : ℝ))) * (2 : ℝ) ^ (5 * N.sqrt + 17) ≤
      (2 : ℝ) ^ ((γ + (α - γ) / 6) * (N : ℝ)))
    (henv2 : (N : ℝ) * (1 + (2 : ℝ) ^ (γ * (N : ℝ))) * (2 : ℝ) ^ (5 * N.sqrt + 17) ≤
      (2 : ℝ) ^ (α * (N : ℝ)))
    (hcomp : ∀ (t : ℝ) (b' d : ℕ), N ≤ d → (2 : ℝ) ^ b' * ((N : ℝ) * (1 + |t|)) ≤ (2 : ℝ) ^ d →
      ∃ s : ℕ, HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ b') s (unitaryEvolution H.val t) ∧
        (s : ℝ) ≤ (N : ℝ) * (1 + |t|) * (2 : ℝ) ^ (5 * d.sqrt + 17))
    {t : ℝ} (ht : |t| ≤ (2 : ℝ) ^ (γ * (N : ℝ))) :
    HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ b) ⌊(2 : ℝ) ^ (α * (N : ℝ))⌋₊
      (unitaryEvolution H.val t) := by
  let δ := (α - γ) / 12
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hγα]
  let d := b + N
  have hF1 : 1 ≤ (2 : ℝ) ^ (5 * N.sqrt + 17) := one_le_pow₀ (by norm_num)
  have hvolN : (N : ℝ) * (1 + |t|) ≤ (2 : ℝ) ^ N := by
    have h1 : (N : ℝ) * (1 + |t|) ≤ (2 : ℝ) ^ (α * (N : ℝ)) :=
      (le_mul_of_one_le_right (by positivity) hF1).trans
        ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right ht 1)
          (Nat.cast_nonneg N)) (zero_le_one.trans hF1)).trans henv2)
    refine h1.trans ?_
    simpa only [one_mul, rpow_natCast] using rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right hα.le (Nat.cast_nonneg N))
  have hscaled : (2 : ℝ) ^ b * ((N : ℝ) * (1 + |t|)) ≤ (2 : ℝ) ^ d :=
    (mul_le_mul_of_nonneg_left hvolN (by positivity)).trans_eq
      (by dsimp only [d]; rw [pow_add (2 : ℝ) b N])
  obtain ⟨s, hfit, hs_le⟩ := hcomp t b d (Nat.le_add_left N b) hscaled
  have hdsqrt : (d.sqrt : ℝ) ≤ 2 * δ * (N : ℝ) := by
    have hd_le : (d : ℝ) ≤ (2 * δ * (N : ℝ)) ^ 2 := by
      have hfl : (b : ℝ) ≤ δ ^ 2 * (N : ℝ) ^ 2 := hb_eq ▸ Nat.floor_le (by positivity)
      dsimp only [d, δ] at hfl ⊢
      push_cast
      nlinarith only [hfl, hN_le_3]
    have hsq : ((d.sqrt : ℝ)) ^ 2 ≤ (d : ℝ) := by exact_mod_cast Nat.sqrt_le' d
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp (hsq.trans hd_le)
  have hs_exp : (s : ℝ) ≤ (2 : ℝ) ^ (α * (N : ℝ)) := by
    have hbase : (N : ℝ) * (1 + |t|) * (2 : ℝ) ^ 17 ≤ (2 : ℝ) ^ ((γ + (α - γ) / 6) * (N : ℝ)) := by
      have h17 : (2 : ℝ) ^ 17 ≤ (2 : ℝ) ^ (5 * N.sqrt + 17) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_add_left 17 _)
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_right ht 1) (Nat.cast_nonneg N))
        h17 (by positivity) (by positivity)).trans henv1
    have h5 : ((2 : ℝ) ^ (5 * d.sqrt) : ℝ) ≤ (2 : ℝ) ^ ((5 / 6 * (α - γ)) * (N : ℝ)) := by
      rw [← rpow_natCast]
      apply rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      dsimp only [δ] at hdsqrt
      linarith only [hdsqrt]
    calc (s : ℝ) ≤ (N : ℝ) * (1 + |t|) * (2 : ℝ) ^ (5 * d.sqrt + 17) := hs_le
      _ = ((N : ℝ) * (1 + |t|) * (2 : ℝ) ^ 17) * (2 : ℝ) ^ (5 * d.sqrt) := by rw [pow_add]; ring
      _ ≤ (2 : ℝ) ^ ((γ + (α - γ) / 6) * (N : ℝ)) * (2 : ℝ) ^ ((5 / 6 * (α - γ)) * (N : ℝ)) :=
          mul_le_mul hbase h5 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (α * (N : ℝ)) := by
          rw [← rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; ring
  exact LocalPatches.approx_enlarge hfit le_rfl (Nat.le_floor hs_exp)

/-- Scale-`2^{-Θ(N²)}` critical-height anti-concentration, active-budget localization,
sharp `1/10` direct-locking dichotomy, and guaranteed `2^{-Θ(N²)}`-nearby quadratic-precision
locking onto the exact same-error maximum `m_e`. -/
theorem gaussian_quadratic_locking_and_anticoncentration :
    ∃ C : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ γ α : ℝ, 0 ≤ γ → γ < α → α < 1 → ∀ᶠ k : ℕ in atTop,
        let N := k + 3
        let D : ℕ := 2 ^ N
        let H := chainGenerator ω k
        let G := (2 : ℝ) ^ (D ^ C)
        let B₇ := D / (7 * (N + 1))
        let cap := (4 * N + 1) * (2 * N + 2) * D ^ 2
        let b := ⌊(((α - γ) / 12) ^ 2) * (N : ℝ) ^ 2⌋₊
        let δ_quad := 2 / (2 : ℝ) ^ b
        let L := ⌊(2 : ℝ) ^ (α * (N : ℝ))⌋₊
        let R := (2 : ℝ) ^ (γ * (N : ℝ))
        volume.real (jumpTolerances H δ_quad) ≤ 1 / (2 : ℝ) ^ (b / 2) ∧
        (∀ j ≤ B₇, 13 / 125 < criticalHeight H j) ∧
        (∀ j ≥ cap, criticalHeight H j = 0) ∧
        (∃ m₁₀ > B₇, IsRecurrentOrbitCircuitMaximumAt H (1 / 10) m₁₀ ∧
          (((∀ j : ℕ, B₇ < j → j < cap → criticalHeight H j ∉ Ioc (1 / 10) (1 / 10 + δ_quad)) ∧
              IsRecurrentOrbitCircuitMaximumAt H (1 / 10 + δ_quad) m₁₀ ∧
              ∀ a : ℝ, ∃ z ∈ Icc a (a + G), ∀ t : ℝ, |t| ≤ R → ∀ j : ℕ,
                HasProjectiveCircuitApproximation N (1 / 10) j (unitaryEvolution H.val (z + t)) →
                  m₁₀ ≤ j + L) ∨
            ∃ j : ℕ, B₇ < j ∧ j < cap ∧ criticalHeight H j ∈ Ioc (1 / 10) (1 / 10 + δ_quad))) ∧
        volume.real (Icc (1 / 10 - 1 / (2 : ℝ) ^ (b / 4)) (1 / 10 + 1 / (2 : ℝ) ^ (b / 4)) ∩
            jumpTolerances H δ_quad) ≤
          (1 / (2 : ℝ) ^ (b / 4)) *
            (volume.real (Icc (1 / 10 - 1 / (2 : ℝ) ^ (b / 4)) (1 / 10 + 1 / (2 : ℝ) ^ (b / 4))) / 2) ∧
        (∃ e_star : ℝ, |e_star - 1 / 10| ≤ 1 / (2 : ℝ) ^ (b / 2) ∧
          e_star ∈ Ioc (0 : ℝ) (13 / 125 - δ_quad) \ jumpTolerances H δ_quad) ∧
        (∀ e ∈ Ioc (0 : ℝ) (13 / 125 - δ_quad), e ∉ jumpTolerances H δ_quad →
          ∃ m > B₇, IsRecurrentOrbitCircuitMaximumAt H e m ∧
            IsRecurrentOrbitCircuitMaximumAt H (e + δ_quad) m ∧
            ∀ a : ℝ, ∃ z ∈ Icc a (a + G), ∀ t : ℝ, |t| ≤ R → ∀ j : ℕ,
              HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val (z + t)) →
                m ≤ j + L) := by
  obtain ⟨C, hprof⟩ := SpectralJets.HighPrecision.gaussian_uniform_profile_recurrence
  refine ⟨C, ?_⟩
  obtain ⟨h13_mem, h13_log⟩ := thirteen_125_entropy
  have h13_neg : log (physicalArc (13 / 125)) + 32 * log 2 / (7 : ℕ) < 0 := by
    have hneg : log (4 / 5 : ℝ) < 0 := log_neg (by norm_num) (by norm_num)
    linarith only [h13_log, hneg]
  filter_upwards [hprof, gaussian_orbit_maximum_full_range,
    LocalPatches.gaussian_binary_precision_compiler,
    gaussian_path_all_prefixes_maximally_projective] with ω hrep hmax hbin hspec
  intro γ α hγ hγα hα
  have hδ_pos : 0 < (α - γ) / 12 := by linarith only [hγα]
  filter_upwards [hrep, hmax (13 / 125) h13_mem 7 (by decide) h13_neg,
    (tendsto_add_atTop_nat 1).eventually hbin,
    (tendsto_add_atTop_nat 3).eventually (quad_bits_growth hδ_pos),
    (tendsto_add_atTop_nat 3).eventually eventually_torusCriticalHeight_gt_thirteen_125,
    (tendsto_add_atTop_nat 3).eventually
      (LocalPatches.binary_compiler_envelope hγ (show γ < γ + (α - γ) / 6 by linarith only [hγα])),
    (tendsto_add_atTop_nat 3).eventually
      (LocalPatches.binary_compiler_envelope hγ hγα)] with k hr hm13 hcomp hqg htorus henv1 henv2
  intro N D H G B₇ cap b δ_quad L R
  obtain ⟨hb16, hb_half, hb_quarter, hN_le_3, hb_le_D⟩ := hqg
  have hN2 : 2 ≤ N := by dsimp only [N]; omega
  have hloc := hasPauliWeightAtMost_pathHamiltonian (pathPauliDisorderShell ω (k + 1))
    (isSelfAdjoint_pathHamiltonian _)
  have hδ0 : 0 < δ_quad := by dsimp only [δ_quad]; positivity
  -- Jump measure bound: 2^(6N) * (2 / 2^b) ≤ 1 / 2^(b/2) (strictly < 2 / 2^(b/2))
  have hjump_strict : (2 : ℝ) ^ (6 * N) * δ_quad ≤ 1 / (2 : ℝ) ^ (b / 2 + 1) := by
    dsimp only [δ_quad]
    rw [show (2 : ℝ) ^ (6 * N) * (2 / (2 : ℝ) ^ b) = (2 : ℝ) ^ (6 * N + 1) / (2 : ℝ) ^ b by
      rw [pow_succ]; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by dsimp only [N, b] at hb_half ⊢; omega)
  have hhalf_le : 1 / (2 : ℝ) ^ (b / 2 + 1) ≤ 1 / (2 : ℝ) ^ (b / 2) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _))
  have hvol_jump : volume.real (jumpTolerances H δ_quad) ≤ 1 / (2 : ℝ) ^ (b / 2) :=
    (volume_jumpTolerances_le H hδ0.le).trans (hjump_strict.trans hhalf_le)
  -- Active window: j ≤ B₇ has criticalHeight > 13/125, j ≥ cap has criticalHeight = 0
  let e_idx := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  have hmax_e : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e_idx.symm i)) :=
    maximallyProjectiveEnergy_equiv e_idx.symm (hspec k)
  have hlow_clear (j : ℕ) (hj : j ≤ B₇) : 13 / 125 < criticalHeight H j := by
    rw [criticalHeight_eq_torusCriticalHeight e_idx H hmax_e j]
    exact htorus (2 ^ N - 1) e_idx _ j hj
  have hhigh_zero (j : ℕ) (hj : cap ≤ j) : criticalHeight H j = 0 :=
    criticalHeight_eq_zero_of_exact_cap hN2 H hj
  -- Compiler + recurrence helper for any e > 0 with clearance
  have hsim_quad (t : ℝ) (ht : |t| ≤ R) :
      HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ b) L (unitaryEvolution H.val t) :=
    quad_sim_of_binary hγα hα H hN_le_3 rfl henv1 henv2 hcomp ht
  have hr_le : 1 / (2 : ℝ) ^ D ≤ 1 / (2 : ℝ) ^ b :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hb_le_D)
  obtain ⟨m₁₃, hm13_gt, hm13_rec⟩ := hm13
  have hlock_at (e : ℝ) (he : e ∈ Ioc (0 : ℝ) (13 / 125 - δ_quad))
      (hclear : e ∉ jumpTolerances H δ_quad) :
      ∃ m > B₇, IsRecurrentOrbitCircuitMaximumAt H e m ∧
        IsRecurrentOrbitCircuitMaximumAt H (e + δ_quad) m ∧
        ∀ a : ℝ, ∃ z ∈ Icc a (a + G), ∀ t : ℝ, |t| ≤ R → ∀ j : ℕ,
          HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val (z + t)) →
            m ≤ j + L := by
    obtain ⟨m, hm⟩ := twoLocal_exists_recurrent_maximum_at hN2 H hloc e he.1
    obtain ⟨n, hn⟩ := twoLocal_exists_recurrent_maximum_at hN2 H hloc (e + δ_quad) (add_pos he.1 hδ0)
    have hmn : m = n :=
      (maximum_eq_iff_criticalHeight_clearance hN2 H he.1.le hδ0.le hm hn).2.mpr hclear
    subst n
    have hm_ge : m₁₃ ≤ m := by
      obtain ⟨u, hu⟩ := required_at_some_date hm13_rec
      obtain ⟨z, hz, C, hC, herr⟩ := hn.1 u
      exact hu m ⟨z, hz, C, hC, herr.trans (by linarith only [he.2])⟩
    obtain ⟨v, hv⟩ := required_at_some_date hn
    refine ⟨m, hm13_gt.trans_le hm_ge, hm, hn, fun a => ?_⟩
    obtain ⟨z, hz, hz_prof⟩ := hr a v
    refine ⟨z, hz, fun t ht j hfit => ?_⟩
    have hh := affordable_add_time H hfit (hsim_quad (-t) (by rwa [abs_neg]))
    rw [show z + t + -t = z by ring] at hh
    have hd_z : orbitCircuitDistance H (j + L) z ≤ e + 1 / (2 : ℝ) ^ b :=
      (hasProjectiveCircuitApproximation_iff_infDist ..).mp hh
    have hgap := (abs_le.mp (hz_prof 0 (j + L))).1
    simp only [add_zero] at hgap
    apply hv (j + L)
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
    change orbitCircuitDistance H (j + L) v ≤ e + 2 / (2 : ℝ) ^ b
    change -(1 / (2 : ℝ) ^ D) ≤ orbitCircuitDistance H (j + L) z - orbitCircuitDistance H (j + L) v at hgap
    have htwo : 1 / (2 : ℝ) ^ b + 1 / (2 : ℝ) ^ b = 2 / (2 : ℝ) ^ b := by ring
    linarith only [hd_z, hgap, hr_le, htwo]
  -- Numerical bounds on δ_quad, 2^-(b/2), and 2^-(b/4)
  have hδ_tiny : δ_quad ≤ 2 / 65536 := by
    dsimp only [δ_quad]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (calc (65536 : ℝ) = (2 : ℝ) ^ 16 := by norm_num
        _ ≤ (2 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hb16)
  have hhalf_tiny : 1 / (2 : ℝ) ^ (b / 2) ≤ 1 / 256 :=
    one_div_le_one_div_of_le (by norm_num)
      (calc (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
        _ ≤ (2 : ℝ) ^ (b / 2) := pow_le_pow_right₀ (by norm_num) (by dsimp only [N, b] at hb16 ⊢; omega))
  -- Dichotomy at e = 1/10
  have h10_range : (1 / 10 : ℝ) ∈ Ioc (0 : ℝ) (13 / 125 - δ_quad) :=
    ⟨by norm_num, by linarith only [hδ_tiny]⟩
  have hdich : ∃ m₁₀ > B₇, IsRecurrentOrbitCircuitMaximumAt H (1 / 10) m₁₀ ∧
      (((∀ j : ℕ, B₇ < j → j < cap → criticalHeight H j ∉ Ioc (1 / 10) (1 / 10 + δ_quad)) ∧
          IsRecurrentOrbitCircuitMaximumAt H (1 / 10 + δ_quad) m₁₀ ∧
          ∀ a : ℝ, ∃ z ∈ Icc a (a + G), ∀ t : ℝ, |t| ≤ R → ∀ j : ℕ,
            HasProjectiveCircuitApproximation N (1 / 10) j (unitaryEvolution H.val (z + t)) →
              m₁₀ ≤ j + L) ∨
        ∃ j : ℕ, B₇ < j ∧ j < cap ∧ criticalHeight H j ∈ Ioc (1 / 10) (1 / 10 + δ_quad)) := by
    by_cases hjump : (1 / 10 : ℝ) ∈ jumpTolerances H δ_quad
    · obtain ⟨j, _, hj_mem⟩ := hjump
      obtain ⟨m₁₀, hm₁₀⟩ := twoLocal_exists_recurrent_maximum_at hN2 H hloc (1 / 10) (by norm_num)
      have hm_ge : m₁₃ ≤ m₁₀ := by
        obtain ⟨u, hu⟩ := required_at_some_date hm13_rec
        obtain ⟨z, hz, C, hC, herr⟩ := hm₁₀.1 u
        exact hu m₁₀ ⟨z, hz, C, hC, herr.trans (by norm_num)⟩
      have hj_gt : B₇ < j := by
        by_contra! hle
        have hgt := hlow_clear j hle
        linarith only [hgt, hj_mem.2, h10_range.2]
      have hj_lt : j < cap := by
        by_contra! hge
        have hz0 := hhigh_zero j hge
        rw [hz0] at hj_mem
        linarith only [hj_mem.1]
      exact ⟨m₁₀, hm13_gt.trans_le hm_ge, hm₁₀, Or.inr ⟨j, hj_gt, hj_lt, hj_mem⟩⟩
    · obtain ⟨m₁₀, hm₁₀_gt, hm₁₀, hm₁₀_coarse, hrec⟩ := hlock_at (1 / 10) h10_range hjump
      obtain ⟨hiff, hiff_jump⟩ := maximum_eq_iff_criticalHeight_clearance hN2 H
        (by norm_num) hδ0.le hm₁₀ hm₁₀_coarse
      have hall := hiff.mp rfl
      exact ⟨m₁₀, hm₁₀_gt, hm₁₀, Or.inl ⟨fun j _ _ => hall j, hm₁₀_coarse, hrec⟩⟩
  -- Micro-window anti-concentration on [1/10 - 2^-(b/4), 1/10 + 2^-(b/4)]
  let ρ := 1 / (2 : ℝ) ^ (b / 4)
  have hρ_pos : 0 < ρ := by dsimp only [ρ]; positivity
  have hmicro : volume.real (Icc (1 / 10 - ρ) (1 / 10 + ρ) ∩ jumpTolerances H δ_quad) ≤
      ρ * (volume.real (Icc (1 / 10 - ρ) (1 / 10 + ρ)) / 2) := by
    have hvol_I : volume.real (Icc (1 / 10 - ρ) (1 / 10 + ρ)) / 2 = ρ := by
      rw [Real.volume_real_Icc_of_le (by linarith only [hρ_pos])]
      ring
    rw [hvol_I]
    have hsub_meas : volume.real (Icc (1 / 10 - ρ) (1 / 10 + ρ) ∩ jumpTolerances H δ_quad) ≤
        1 / (2 : ℝ) ^ (b / 2) :=
      (measureReal_mono inter_subset_right (measure_jumpTolerances_ne_top H δ_quad)).trans hvol_jump
    refine hsub_meas.trans ?_
    dsimp only [ρ]
    rw [one_div_mul_one_div, ← pow_add]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by dsimp only [N, b] at hb_quarter ⊢; omega))
  -- Existence of e_star with |e_star - 1/10| ≤ 1 / 2^(b/2) outside jumpTolerances
  have hex_star : ∃ e_star : ℝ, |e_star - 1 / 10| ≤ 1 / (2 : ℝ) ^ (b / 2) ∧
      e_star ∈ Ioc (0 : ℝ) (13 / 125 - δ_quad) \ jumpTolerances H δ_quad := by
    let η₂ := 1 / (2 : ℝ) ^ (b / 2)
    let J := Icc (1 / 10 - η₂) (1 / 10 + η₂)
    have hη₂_pos : 0 < η₂ := by dsimp only [η₂]; positivity
    have hJ_vol : volume.real J = 2 * η₂ := by
      rw [Real.volume_real_Icc_of_le (by linarith only [hη₂_pos])]; ring
    have hJ_inter : volume.real (J ∩ jumpTolerances H δ_quad) < volume.real J := by
      have hle : volume.real (J ∩ jumpTolerances H δ_quad) ≤ 1 / (2 : ℝ) ^ (b / 2 + 1) :=
        (measureReal_mono inter_subset_right (measure_jumpTolerances_ne_top H δ_quad)).trans
          ((volume_jumpTolerances_le H hδ0.le).trans hjump_strict)
      have hlt : 1 / (2 : ℝ) ^ (b / 2 + 1) < 2 * η₂ := by
        have h1 : 1 / (2 : ℝ) ^ (b / 2 + 1) = η₂ / 2 := by
          dsimp only [η₂]; rw [pow_succ]; ring
        linarith only [h1, hη₂_pos]
      exact hle.trans_lt (hJ_vol ▸ hlt)
    have hne : (J \ jumpTolerances H δ_quad).Nonempty := by
      by_contra hempty
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hempty
      rw [inter_eq_self_of_subset_left hempty] at hJ_inter
      exact lt_irrefl _ hJ_inter
    obtain ⟨e_star, heJ, he_clear⟩ := hne
    refine ⟨e_star, abs_sub_le_iff.mpr ⟨by linarith only [heJ.2], by linarith only [heJ.1]⟩,
      ⟨?_, ?_⟩, he_clear⟩
    · dsimp only [J, η₂] at heJ
      linarith only [heJ.1, hhalf_tiny]
    · dsimp only [J, η₂] at heJ
      linarith only [heJ.2, hhalf_tiny, hδ_tiny]
  exact ⟨hvol_jump, hlow_clear, hhigh_zero, hdich, hmicro, hex_star, hlock_at⟩

private theorem summable_quad_jump_measures {δ : ℝ} (hδ : 0 < δ) :
    Summable fun k : ℕ =>
      (2 : ℝ) ^ (6 * (k + 3)) * (2 / (2 : ℝ) ^ ⌊δ ^ 2 * ((k + 3 : ℕ) : ℝ) ^ 2⌋₊) := by
  have hev : ∀ᶠ k : ℕ in atTop,
      (2 : ℝ) ^ (6 * (k + 3)) * (2 / (2 : ℝ) ^ ⌊δ ^ 2 * ((k + 3 : ℕ) : ℝ) ^ 2⌋₊) ≤
        (1 / 2 : ℝ) ^ k := by
    filter_upwards [(tendsto_add_atTop_nat 3).eventually (quad_bits_growth hδ)] with k hqg
    obtain ⟨_, hb_half, _, _, _⟩ := hqg
    let N := k + 3
    let b := ⌊δ ^ 2 * (N : ℝ) ^ 2⌋₊
    change (2 : ℝ) ^ (6 * N) * (2 / (2 : ℝ) ^ b) ≤ (1 / 2 : ℝ) ^ k
    rw [_root_.one_div_pow, show (2 : ℝ) ^ (6 * N) * (2 / (2 : ℝ) ^ b) =
      (2 : ℝ) ^ (6 * N + 1) / (2 : ℝ) ^ b by rw [pow_succ]; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by dsimp only [N, b] at hb_half ⊢; omega)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  refine (summable_nat_add_iff K).mp <| Summable.of_nonneg_of_le
    (fun _ => by positivity) (fun m => ?_)
    (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  exact (hK (m + K) (Nat.le_add_left K m)).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right m K))

/-- Explicit sub-Gaussian tail measure bound on tolerances experiencing any critical-height
jump at or beyond prefix `K`. -/
theorem volume_tail_jumpTolerances_le (ω : PathPauliDisorder) (δ : ℕ → ℝ)
    (hδ : ∀ k, 0 ≤ δ k) (K : ℕ) :
    volume (⋃ k ≥ K, jumpTolerances (chainGenerator ω k) (δ k)) ≤
      ∑' m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (6 * (m + K + 3)) * δ (m + K)) := by
  have hsub : (⋃ k ≥ K, jumpTolerances (chainGenerator ω k) (δ k)) ⊆
      ⋃ m : ℕ, jumpTolerances (chainGenerator ω (m + K)) (δ (m + K)) := by
    rintro e ⟨_, ⟨k, rfl⟩, ⟨_, ⟨hk, rfl⟩, he⟩⟩
    exact mem_iUnion.mpr ⟨k - K, by rwa [Nat.sub_add_cancel hk]⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun m => ?_))
  rw [← ENNReal.ofReal_toReal (measure_jumpTolerances_ne_top (chainGenerator ω (m + K)) (δ (m + K)))]
  exact ENNReal.ofReal_le_ofReal (volume_jumpTolerances_le _ (hδ (m + K)))

private theorem ae_prescribed_quad_clearance {γ α : ℝ} (hγα : γ < α) :
    ∀ᵐ e : ℝ ∂volume, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k + 3
      let b := ⌊(((α - γ) / 12) ^ 2) * (N : ℝ) ^ 2⌋₊
      e ∉ jumpTolerances (chainGenerator ω k) (2 / (2 : ℝ) ^ b) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let δ_fn (k : ℕ) : ℝ := 2 / (2 : ℝ) ^ ⌊(((α - γ) / 12) ^ 2) * ((k + 3 : ℕ) : ℝ) ^ 2⌋₊
  have hδ0 (k : ℕ) : 0 ≤ δ_fn k := by dsimp only [δ_fn]; positivity
  let J (k : ℕ) : Set (PathPauliDisorder × ℝ) :=
    {p | p.2 ∈ jumpTolerances (chainGenerator p.1 k) (δ_fn k)}
  have hJ_meas (k : ℕ) : MeasurableSet (J k) := by
    have heq : J k = ⋃ j ∈ Finset.range (2 ^ (6 * (k + 3))),
        {p : PathPauliDisorder × ℝ |
          criticalHeight (chainGenerator p.1 k) j - δ_fn k ≤ p.2 ∧
            p.2 < criticalHeight (chainGenerator p.1 k) j} := by
      ext p
      simp only [J, mem_setOf_eq, jumpTolerances_eq_biUnion, mem_iUnion, exists_prop, mem_Ico]
    rw [heq]
    refine Finset.measurableSet_biUnion _ fun j _ => ?_
    have hh : Measurable (fun p : PathPauliDisorder × ℝ => criticalHeight (chainGenerator p.1 k) j) :=
      (measurable_threshold k j).comp measurable_fst
    exact (measurableSet_le (hh.sub_const _) measurable_snd).inter (measurableSet_lt measurable_snd hh)
  let E : Set (PathPauliDisorder × ℝ) :=
    {p | ∀ᶠ k : ℕ in atTop, p ∉ J k}
  have hE_meas : MeasurableSet E := by
    have heq : E = ⋃ K : ℕ, ⋂ k : ℕ, ⋂ (_ : K ≤ k), (J k)ᶜ := by
      ext p
      simp only [E, mem_setOf_eq, eventually_atTop, mem_iUnion, mem_iInter, mem_compl_iff]
    rw [heq]
    exact MeasurableSet.iUnion fun K => MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun _ => (hJ_meas k).compl
  have hsum := summable_quad_jump_measures (show 0 < (α - γ) / 12 by linarith only [hγα])
  have hω_all : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᵐ e : ℝ ∂volume, (ω, e) ∈ E := by
    refine Eventually.of_forall fun ω => ?_
    let f (k : ℕ) (e : ℝ) : ℝ≥0∞ := (jumpTolerances (chainGenerator ω k) (δ_fn k)).indicator 1 e
    have hf_meas (k : ℕ) : Measurable (f k) :=
      measurable_const.indicator (measurableSet_jumpTolerances _ _)
    have htsum_lt : (∫⁻ e, ∑' k, f k e) < ⊤ := by
      rw [lintegral_tsum fun k => (hf_meas k).aemeasurable]
      have hterm (k : ℕ) : (∫⁻ e, f k e) ≤
          ENNReal.ofReal ((2 : ℝ) ^ (6 * (k + 3)) * δ_fn k) := by
        dsimp only [f]
        rw [lintegral_indicator_one (measurableSet_jumpTolerances _ _),
          ← ENNReal.ofReal_toReal (measure_jumpTolerances_ne_top (chainGenerator ω k) (δ_fn k))]
        exact ENNReal.ofReal_le_ofReal (volume_jumpTolerances_le _ (hδ0 k))
      refine (ENNReal.tsum_le_tsum hterm).trans_lt ?_
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
      exact ENNReal.ofReal_lt_top
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun k => (hf_meas k).aemeasurable) htsum_lt.ne]
      with e hfin
    have hlim := (ENNReal.summable_toReal hfin.ne).tendsto_atTop_zero
    filter_upwards [hlim.eventually_lt_const zero_lt_one] with k hk he_mem
    have h1 : (f k e).toReal = 1 := by
      dsimp only [f]
      change e ∈ jumpTolerances (chainGenerator ω k) (δ_fn k) at he_mem
      rw [indicator_of_mem he_mem, Pi.one_apply, ENNReal.toReal_one]
    linarith only [hk, h1]
  exact (Measure.ae_ae_comm hE_meas).mp hω_all

/-- Universal quadratic-precision locking for prescribed tolerances: for fixed `0 ≤ γ < α < 1`,
almost every tolerance `e ∈ (0, 13 / 125)` chosen before the disorder eventually avoids
`jumpTolerances` at the universal quadratic scale `2 / 2^⌊((α - γ)/12)² N²⌋` and locks directly
onto the exact same-error maximum `m_e` without `(ω, e)`-dependent precision exponents. -/
theorem gaussian_prescribed_quadratic_locking {γ α : ℝ} (hγ : 0 ≤ γ)
    (hγα : γ < α) (hα : α < 1) :
    ∃ C : ℕ, ∀ᵐ e : ℝ ∂volume, e ∈ Ioo (0 : ℝ) (13 / 125) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let N := k + 3
        let D : ℕ := 2 ^ N
        let H := chainGenerator ω k
        let b := ⌊(((α - γ) / 12) ^ 2) * (N : ℝ) ^ 2⌋₊
        let δ_quad := 2 / (2 : ℝ) ^ b
        e ∉ jumpTolerances H δ_quad ∧
        ∃ m > D / (7 * (N + 1)),
          IsRecurrentOrbitCircuitMaximumAt H e m ∧
          IsRecurrentOrbitCircuitMaximumAt H (e + δ_quad) m ∧
          ∀ a : ℝ, ∃ z ∈ Icc a (a + (2 : ℝ) ^ (D ^ C)),
            ∀ t : ℝ, |t| ≤ (2 : ℝ) ^ (γ * (N : ℝ)) → ∀ j : ℕ,
              HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val (z + t)) →
                m ≤ j + ⌊(2 : ℝ) ^ (α * (N : ℝ))⌋₊ := by
  obtain ⟨C, hmain⟩ := gaussian_quadratic_locking_and_anticoncentration
  refine ⟨C, ?_⟩
  filter_upwards [ae_prescribed_quad_clearance hγα] with e hclear he
  filter_upwards [hclear, hmain] with ω hω_clear hω_main
  have hδ_pos : 0 < (α - γ) / 12 := by linarith only [hγα]
  have hgap : 0 < 13 / 125 - e := sub_pos.mpr he.2
  have hlim_δ : Tendsto (fun k : ℕ =>
      (2 : ℝ) / (2 : ℝ) ^ ⌊(((α - γ) / 12) ^ 2) * ((k + 3 : ℕ) : ℝ) ^ 2⌋₊) atTop (𝓝 0) :=
    squeeze_zero (fun _ => by positivity)
      (fun k => le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num)))
      (summable_quad_jump_measures hδ_pos).tendsto_atTop_zero
  filter_upwards [hω_clear, hω_main γ α hγ hγα hα, hlim_δ.eventually_lt_const hgap]
    with k hk_clear hk_main hk_δ
  intro N D H b δ_quad
  obtain ⟨_, _, _, _, _, _, hlock_at⟩ := hk_main
  have he_mem : e ∈ Ioc (0 : ℝ) (13 / 125 - δ_quad) := ⟨he.1, by linarith only [hk_δ]⟩
  exact ⟨hk_clear, hlock_at e he_mem hk_clear⟩

#print axioms criticalHeight_scaleSelfAdjoint
#print axioms criticalHeight_shiftSelfAdjoint
#print axioms criticalHeight_eq_torusCriticalHeight
#print axioms criticalHeight_eq_of_commute
#print axioms abs_criticalHeight_conjSelfAdjoint_sub_le
#print axioms abs_criticalHeight_transverseFlow_sub_le
#print axioms criticalHeight_conjSelfAdjoint_zero
#print axioms eventually_torusCriticalHeight_gt_thirteen_125
#print axioms maximum_eq_iff_criticalHeight_clearance
#print axioms gaussian_quadratic_locking_and_anticoncentration
#print axioms gaussian_prescribed_quadratic_locking

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau

