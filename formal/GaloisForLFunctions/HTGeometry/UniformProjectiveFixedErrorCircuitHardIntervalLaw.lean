import GaloisForLFunctions.HTGeometry.UniformFixedErrorSpectralTorusCircuitHardnessLaw
import GaloisForLFunctions.HTGeometry.ProjectiveSpectralCircuitHardIntervalLaw
import GaloisForLFunctions.HTGeometry.DiagonalProjectorClockPackingLaw
import GaloisForLFunctions.HTGeometry.MaximallyProjectivePhysicalCircuitHardIntervalLaw

/-!
# Uniform projective fixed-error circuit-hard intervals

Fixing one Boolean spectral sign leaves `2^(D-1)` reflections.  Distinct
anchored reflections stay operator-norm distance at least one after every
global rephasing.  Quantitative continuous-circuit nets therefore leave a
reflection uniformly far from every bounded circuit, even projectively.

Maximal projective spectral rank makes one autonomous Hamiltonian visit a
neighbourhood of that reflection syndetically.  The resulting physical hard
intervals have the system-size-independent operator error `1/10`.
-/

open Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem exists_projectively_far_from_small_net
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (p : ι → X) (δ r : ℝ)
    (hsep : ∀ {x y : ι}, x ≠ y → ∀ c : ℂ, ‖c‖ = 1 →
      δ ≤ ‖p x - c • p y‖)
    (hr : 2 * r < δ) (net : Finset X)
    (hcard : net.card < Fintype.card ι) :
    ∃ x : ι, ∀ W ∈ net, ∀ c : ℂ, ‖c‖ = 1 →
      r < ‖p x - c • W‖ := by
  classical
  by_contra h
  push Not at h
  choose W hW c hc hdist using h
  let f : ι → {x // x ∈ net} := fun x => ⟨W x, hW x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hcy : c y ≠ 0 := norm_ne_zero_iff.mp (by rw [hc y]; norm_num)
    let z : ℂ := c x / c y
    have hz : ‖z‖ = 1 := by simp [z, hc x, hc y]
    have hWxy : W x = W y := congrArg Subtype.val hxy
    have hscalar : z * c y = c x := by
      dsimp [z]
      exact div_mul_cancel₀ (c x) hcy
    have hupper : ‖p x - z • p y‖ ≤ 2 * r := by
      calc
        ‖p x - z • p y‖ ≤
            ‖p x - c x • W x‖ + ‖c x • W x - z • p y‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = ‖p x - c x • W x‖ + ‖z • (c y • W y - p y)‖ := by
          congr 1
          rw [hWxy]
          congr 1
          rw [← hscalar]
          module
        _ = ‖p x - c x • W x‖ + ‖c y • W y - p y‖ := by
          rw [norm_smul, hz, one_mul]
        _ = ‖p x - c x • W x‖ + ‖p y - c y • W y‖ := by
          congr 1
          exact norm_sub_rev _ _
        _ ≤ r + r := add_le_add (hdist x) (hdist y)
        _ = 2 * r := by ring
    exact (not_lt_of_ge (hsep hne z hz)) (hupper.trans_lt hr)
  exact (Nat.not_le_of_lt hcard) (by
    simpa using Fintype.card_le_of_injective f hf)

def anchoredBooleanPacket {d : ℕ} (x : Fin d → Bool) : Fin (d + 1) → ℂ :=
  Fin.cases 1 (fun i => if x i then -1 else 1)

def anchoredSpectralBooleanReflection {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (x : Fin d → Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
    Matrix.diagonal (anchoredBooleanPacket x ∘ e) *
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1

/-- Anchoring one sign removes the antipodal collision: two distinct Boolean
reflections stay distance at least one under every relative global phase. -/
theorem anchoredSpectralBooleanReflection_projective_separated
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    {x y : Fin d → Bool} (hxy : x ≠ y)
    (c : ℂ) (_hc : ‖c‖ = 1) :
    1 ≤ ‖anchoredSpectralBooleanReflection e V x -
      c • anchoredSpectralBooleanReflection e V y‖ := by
  have hdiff :
      anchoredSpectralBooleanReflection e V x -
          c • anchoredSpectralBooleanReflection e V y =
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
          (Matrix.diagonal (anchoredBooleanPacket x ∘ e) -
            c • Matrix.diagonal (anchoredBooleanPacket y ∘ e)) *
          (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 := by
    simp only [anchoredSpectralBooleanReflection, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hdiff]
  have hVinv : (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 =
      star (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by simp
  rw [hVinv, l2_opNorm_unitary_conj_eq V.2]
  have hdiag :
      Matrix.diagonal (anchoredBooleanPacket x ∘ e) -
          c • Matrix.diagonal (anchoredBooleanPacket y ∘ e) =
        Matrix.diagonal (fun q =>
          anchoredBooleanPacket x (e q) - c * anchoredBooleanPacket y (e q)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  let f : (Fin n → Bool) → ℂ := fun q =>
    anchoredBooleanPacket x (e q) - c * anchoredBooleanPacket y (e q)
  have hanchor : ‖(1 : ℂ) - c‖ ≤ ‖f‖ := by
    have h := norm_le_pi_norm f (e.symm 0)
    simpa [f, anchoredBooleanPacket] using h
  have hpoint : ∃ i : Fin d, x i ≠ y i := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  obtain ⟨i, hi⟩ := hpoint
  have htail : ‖(1 : ℂ) + c‖ ≤ ‖f‖ := by
    have h := norm_le_pi_norm f (e.symm i.succ)
    cases hxi : x i <;> cases hyi : y i
    · simp [hxi, hyi] at hi
    · simpa [f, anchoredBooleanPacket, hxi, hyi, norm_neg, add_comm] using h
    · have h' : ‖(-1 : ℂ) - c‖ ≤ ‖f‖ := by
        simpa [f, anchoredBooleanPacket, hxi, hyi] using h
      rw [show (-1 : ℂ) - c = -(1 + c) by ring, norm_neg] at h'
      exact h'
    · simp [hxi, hyi] at hi
  have htwo : (2 : ℝ) ≤ ‖(1 : ℂ) - c‖ + ‖(1 : ℂ) + c‖ := by
    calc
      (2 : ℝ) = ‖((1 : ℂ) - c) + (1 + c)‖ := by norm_num
      _ ≤ ‖(1 : ℂ) - c‖ + ‖(1 : ℂ) + c‖ := norm_add_le _ _
  nlinarith

/-- If continuous-circuit metric entropy is below the anchored Boolean
carrier, one reflection is uniformly hard even after arbitrary rephasing. -/
theorem exists_anchoredSpectralBooleanReflection_atMostCircuit_fixedError
    {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hEntropy : atMostQuarterCircuitEntropyBound n s < ((2 ^ d : ℕ) : ℝ)) :
    ∃ x : Fin d → Bool,
      ∀ c : ℂ, ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
        C.gateCount ≤ s → (3 / 20 : ℝ) <
          ‖anchoredSpectralBooleanReflection e V x -
            c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  classical
  let net := atMostQuarterCircuitNet n s
  let matrixNet : Finset (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
    net.image Subtype.val
  have hmatrixNetCard : matrixNet.card = net.card := by
    exact Finset.card_image_of_injective net Subtype.val_injective
  have hnetCardReal : ((net.card : ℕ) : ℝ) < ((2 ^ d : ℕ) : ℝ) :=
    (atMostQuarterCircuitNet_card_real_le n s).trans_lt hEntropy
  have hcard : matrixNet.card < Fintype.card (Fin d → Bool) := by
    rw [hmatrixNetCard]
    have : net.card < 2 ^ d := by exact_mod_cast hnetCardReal
    simpa using this
  obtain ⟨x, hx⟩ := exists_projectively_far_from_small_net
    (p := anchoredSpectralBooleanReflection e V)
    (δ := (1 : ℝ)) (r := (2 / 5 : ℝ))
    (fun hxy c hc =>
      anchoredSpectralBooleanReflection_projective_separated e V hxy c hc)
    (by norm_num) matrixNet hcard
  refine ⟨x, ?_⟩
  intro c hc C hCs
  obtain ⟨W, hW, hCW⟩ := atMostQuarterCircuitNet_cover C hCs
  have hWmatrix :
      (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈ matrixNet := by
    exact Finset.mem_image.mpr ⟨W, hW, rfl⟩
  have hfar := hx W hWmatrix c hc
  have hmove :
      ‖c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
          c • (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤ (1 / 4 : ℝ) := by
    rw [← smul_sub, norm_smul, hc, one_mul]
    simpa [dist_eq_norm] using hCW
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (anchoredSpectralBooleanReflection e V x)
    (c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    (c • (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
  linarith

def anchoredBooleanProjectivePhase {d : ℕ}
    (x : Fin d → Bool) : Fin d → UnitAddCircle :=
  fun i => if x i then ((1 / 2 : ℝ) : UnitAddCircle) else 0

theorem projectiveSpectralMatrix_anchoredBooleanProjectivePhase
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (x : Fin d → Bool) :
    projectiveSpectralMatrix e V (anchoredBooleanProjectivePhase x) =
      anchoredSpectralBooleanReflection e V x := by
  have hdiag :
      Matrix.diagonal (fun q => fourier 1
          (RHTower.zeroAnchoredPhase d (anchoredBooleanProjectivePhase x) (e q))) =
        Matrix.diagonal (anchoredBooleanPacket x ∘ e) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      simp only [Function.comp_apply]
      generalize hr : e i = r
      refine Fin.cases ?_ (fun k => ?_) r
      · simp [RHTower.zeroAnchoredPhase, anchoredBooleanPacket]
      · change fourier 1 (anchoredBooleanProjectivePhase x k) =
          anchoredBooleanPacket x k.succ
        cases hx : x k
        · simp [anchoredBooleanProjectivePhase, anchoredBooleanPacket, hx]
        · rw [show anchoredBooleanProjectivePhase x k =
              ((1 / 2 : ℝ) : UnitAddCircle) by
                simp [anchoredBooleanProjectivePhase, hx]]
          rw [fourier_one]
          simpa [anchoredBooleanPacket, hx] using coe_toCircle_half
    · simp [Matrix.diagonal_apply_ne _ hij]
  simp only [projectiveSpectralMatrix, anchoredSpectralBooleanReflection]
  rw [hdiag]

theorem exists_uniformFixedError_projectivePhase_continuousCircuitHard
    {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hEntropy : atMostQuarterCircuitEntropyBound n s < ((2 ^ d : ℕ) : ℝ)) :
    ∃ x : Fin d → UnitAddCircle,
      ∀ c : ℂ, ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
        C.gateCount ≤ s → (3 / 20 : ℝ) <
          ‖projectiveSpectralMatrix e V x -
            c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  obtain ⟨x, hx⟩ :=
    exists_anchoredSpectralBooleanReflection_atMostCircuit_fixedError e V hEntropy
  refine ⟨anchoredBooleanProjectivePhase x, ?_⟩
  rw [projectiveSpectralMatrix_anchoredBooleanProjectivePhase]
  exact hx

/-- Maximal spectral rank turns projective packing into syndetic hard
intervals at the universal error `1/10`. -/
theorem maximallyProjective_projectiveSpectralCircuitHardIntervals_uniformError_of_entropy
    {n d s : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hEntropy : atMostQuarterCircuitEntropyBound n s < ((2 ^ d : ℕ) : ℝ)) :
    ∃ W : ℝ, 0 < W ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ a : ℝ, ∃ u ∈ Set.Icc a (a + L),
        ∀ t ∈ Set.Icc u (u + W),
          ∀ c : ℂ, ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
            C.gateCount ≤ s → (1 / 10 : ℝ) ≤
              ‖projectiveSpectralMatrix e V
                  (RHTower.projectivePhysicalPhaseFlow energy t) -
                c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  obtain ⟨x, hhard⟩ :=
    exists_uniformFixedError_projectivePhase_continuousCircuitHard e V hEntropy
  have hucP : UniformContinuous (projectiveSpectralMatrix e V) :=
    CompactSpace.uniformContinuous_of_continuous
      (continuous_projectiveSpectralMatrix e V)
  have hucFlow := RHTower.uniformContinuous_projectivePhysicalPhaseFlow energy
  have huc : UniformContinuous (fun t : ℝ =>
      projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy t)) :=
    hucP.comp hucFlow
  obtain ⟨eta, heta, hmod⟩ :=
    (Metric.uniformContinuous_iff.mp huc) (1 / 80 : ℝ) (by norm_num)
  let U : Set (Fin d → UnitAddCircle) :=
    (projectiveSpectralMatrix e V) ⁻¹'
      Metric.ball (projectiveSpectralMatrix e V x) (1 / 80 : ℝ)
  have hUopen : IsOpen U :=
    Metric.isOpen_ball.preimage (continuous_projectiveSpectralMatrix e V)
  have hUne : U.Nonempty := by
    refine ⟨x, ?_⟩
    simp [U, Metric.mem_ball]
  obtain ⟨L, hL, hhit⟩ := denseAddOrbit_open_hits_syndetically
    (RHTower.projectivePhysicalPhaseFlowHom energy)
    (RHTower.denseRange_projectivePhysicalPhaseFlowHom energy hmax)
    hUopen hUne
  refine ⟨eta / 2, by positivity, L, hL, ?_⟩
  intro a
  obtain ⟨u, hu, huU⟩ := hhit a
  change RHTower.projectivePhysicalPhaseFlow energy u ∈ U at huU
  refine ⟨u, hu, ?_⟩
  have huclose :
      ‖projectiveSpectralMatrix e V
          (RHTower.projectivePhysicalPhaseFlow energy u) -
        projectiveSpectralMatrix e V x‖ < (1 / 80 : ℝ) := by
    simpa [U, Metric.mem_ball, dist_eq_norm] using huU
  intro t ht c hc C hCs
  have htu : dist t u < eta := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hmove := hmod htu
  rw [dist_eq_norm] at hmove
  have htclose :
      ‖projectiveSpectralMatrix e V
          (RHTower.projectivePhysicalPhaseFlow energy t) -
        projectiveSpectralMatrix e V x‖ < (1 / 40 : ℝ) := by
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy t))
      (projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy u))
      (projectiveSpectralMatrix e V x)
    linarith
  have hseed := hhard c hc C hCs
  have htclose' :
      ‖projectiveSpectralMatrix e V x -
        projectiveSpectralMatrix e V
          (RHTower.projectivePhysicalPhaseFlow energy t)‖ < (1 / 40 : ℝ) := by
    simpa [norm_sub_rev] using htclose
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (projectiveSpectralMatrix e V x)
    (projectiveSpectralMatrix e V
      (RHTower.projectivePhysicalPhaseFlow energy t))
    (c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
  linarith

/-- Physical Schrödinger form of the universal fixed-error hard-interval law. -/
theorem maximallyProjective_unitaryEvolution_circuitHardIntervals_uniformError_of_entropy
    {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    {H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy (fun i => hH.eigenvalues (e.symm i)))
    (hEntropy : atMostQuarterCircuitEntropyBound n s < ((2 ^ d : ℕ) : ℝ)) :
    ∃ W : ℝ, 0 < W ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ a : ℝ, ∃ u ∈ Set.Icc a (a + L),
        ∀ t ∈ Set.Icc u (u + W),
          ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
            (1 / 10 : ℝ) ≤ ‖unitaryEvolution H t -
              (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  obtain ⟨W, hW, L, hL, hhard⟩ :=
    maximallyProjective_projectiveSpectralCircuitHardIntervals_uniformError_of_entropy
      (fun i => hH.eigenvalues (e.symm i)) hmax e
      (hermitianEigenbasisUnitary hH) hEntropy
  refine ⟨W, hW, L, hL, ?_⟩
  intro a
  obtain ⟨u, hu, huHard⟩ := hhard a
  refine ⟨u, hu, ?_⟩
  intro t ht C hCs
  let anchor : ℂ :=
    Complex.exp (-(Complex.I * (t * hH.eigenvalues (e.symm 0))))
  have hanchor : ‖anchor‖ = 1 := by
    unfold anchor
    rw [Complex.norm_exp]
    simp
  have hproj := huHard t ht anchor⁻¹
    (by rw [norm_inv, hanchor, inv_one]) C hCs
  rw [unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix]
  change (1 / 10 : ℝ) ≤ ‖anchor • projectiveSpectralMatrix e
      (hermitianEigenbasisUnitary hH)
        (RHTower.projectivePhysicalPhaseFlow
          (fun i => hH.eigenvalues (e.symm i)) t) -
      (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖
  have hfactor : anchor • projectiveSpectralMatrix e
        (hermitianEigenbasisUnitary hH)
          (RHTower.projectivePhysicalPhaseFlow
            (fun i => hH.eigenvalues (e.symm i)) t) -
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      anchor • (projectiveSpectralMatrix e
        (hermitianEigenbasisUnitary hH)
          (RHTower.projectivePhysicalPhaseFlow
            (fun i => hH.eigenvalues (e.symm i)) t) -
        anchor⁻¹ • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by
    rw [smul_sub, smul_smul,
      mul_inv_cancel₀ (Complex.exp_ne_zero _), one_smul]
  rw [hfactor, norm_smul, hanchor, one_mul]
  exact hproj

end

end GaloisForLFunctions.HTGeometry
