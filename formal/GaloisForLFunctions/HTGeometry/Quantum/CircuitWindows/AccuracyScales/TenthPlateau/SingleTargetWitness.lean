import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.NearHilbertOnset
import GaloisForLFunctions.HTGeometry.LagrangeSpectralProjector
import GaloisForLFunctions.HTGeometry.ObserverInvisibleRayPreservation
import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.FixedDate
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortArcHaar
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEcho
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.GlobalPhase.CriticalGap
import GaloisForLFunctions.HTGeometry.QuenchedFixedTimeTransfer
import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity
import GaloisForLFunctions.HTGeometry.HaferkampLiftedPauliTransport
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.PrescribedTolerance

/-! # Single-target non-commutative witnesses and detuning-free upper bounds on `τ_P`

This module investigates single-target non-commutative witnesses for upper-bounding
`τ_s = tenthPlateauOnset H s` (in particular at the canonical exponential budget
`P = nearHilbertContinuousCircuitBudget N` and Hilbert-scale budget `B₇ = 2^N / (7 * (N + 1))`)
without full-torus detuning `2^(D^c)`:

1. **Detuning-free single-date onset certification:** any single date `T ≥ 0` at which
   `e^{-i T H}` fails `(1/10, s)`-affordability pins `1 / (20 * (‖H‖ + 1)) < τ_s < T` and
   `orbitCircuitDistance H s τ_s = 1 / 10`. Both single non-commutative commutator witnesses
   `‖[U(T)* A U(T), B]‖ > circuitCommutatorCap N s A B + 2 / 5` and single separated unitary
   targets certify `τ_s < T` with zero phase-torus detuning.
2. **Witness obstructions and non-local commutator survivor:**
   - *Single-site Pauli OTOC collapse:* for any distinct wires `i ≠ j`, single-site Paulis
     `Z_i, X_j` commute at `t = 0` yet satisfy `circuitCommutatorCap N s Z_i X_j = 2` for every
     `s ≥ 1`, attaining the universal contraction ceiling at one gate.
   - *Rank-one / partial-swap non-commutative witness:* a local rank-one projector `|x₀⟩⟨x₀|`
     paired with a rank-two partial swap `W* (|x₀⟩⟨x₁| + |x₁⟩⟨x₀|) W` has norm `1`, attains
     commutator norm `1` at `U(T) = W`, and obeys `circuitCommutatorCap N s A B ≤ 1 / 2` whenever
     all `s`-gate states have amplitude sum at most `1 / 4` along `(W* |x₀⟩, W* |x₁⟩)`.
   - *Arbitrary single-unitary barriers:* non-commuting unitaries `W ∈ U(2^N)` incur a permanent
     off-diagonal floor `‖(V* W V)_{a b}‖ ≤ ‖e^{-i t H} - z • W‖` (`a ≠ b`), and on every
     maximally projective generator every single unitary `W ∈ U(2^N)` has capture density at
     most `D * (physicalArc r + 1 / D)^D` and syndetic clock horizon `G + 1 ≥ Ω(b^{-D})`.
3. **Detuning-free upper bounds on `τ_P` and `τ_{B₇}`:**
   - *1D boundary-field spectral-jet onset bound:* as `w_n → 0⁺` and `T_n * w_n → ∞` (including
     polynomial dates `T_n`), at most a `(4 / 5)^D + o(1)` fraction of terminal fields `b + w_n u`
     has `τ_s ≥ T_n` for any `s ≤ B₇` (including `s = P`).
   - *Quenched-to-fixed-time ensemble onset transfer:* on the unperturbed Gaussian ensemble,
     `limsup_{t → ∞} ℙ(∀ s ≤ B₇, τ_s(H_N) < t) ≥ 1 - (4 / 5)^D` with zero full-torus
     detuning. -/

open Set Filter MeasureTheory Real Topology Matrix
open scoped Matrix.Norms.L2Operator ENNReal ComplexConjugate Kronecker
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ

/-- Matrix commutator `[X, Y] = X Y - Y X`. -/
def matrixCommutator {I : Type*} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  X * Y - Y * X

/-- Maximum operator-norm commutator `‖[C* A C, B]‖` attainable by two-qubit circuits of
at most `s` gates. -/
def circuitCommutatorCap (N s : ℕ) (A B : Register N) : ℝ :=
  sSup (range fun C : {C : TwoQubitCircuit N // C.gateCount ≤ s} =>
    ‖matrixCommutator (star (C.val.eval : Register N) * A * (C.val.eval : Register N)) B‖)

/-- Single-site Pauli label placing axis `p` on wire `i` and identity elsewhere. -/
def singleSitePauliLabel {N : ℕ} (i : Fin N) (p : Fin 3) : Fin N → Option (Fin 3) :=
  fun q => if q = i then some p else none

/-- Elementary matrix unit `|a⟩⟨b|` on register configurations. -/
def configMatrixUnit {N : ℕ} (a b : Config N) : Register N :=
  fun i j => if i = a ∧ j = b then 1 else 0

private theorem early_tenth_bound {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) :
    0 < 1 / (20 * (‖H.val‖ + 1)) ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / (20 * (‖H.val‖ + 1))), orbitCircuitDistance H s t < 1 / 10 := by
  let r₀ := 1 / (20 * (‖H.val‖ + 1))
  have hden : 0 < 20 * (‖H.val‖ + 1) := by positivity
  have hr₀ : 0 < r₀ := div_pos zero_lt_one hden
  refine ⟨hr₀, fun t ht => ?_⟩
  have hstep : ‖unitaryEvolution H.val t - 1‖ ≤ t * ‖H.val‖ := by
    have h0 : unitaryEvolution H.val 0 = 1 := by simp [unitaryEvolution]
    have h := norm_unitaryEvolution_time_sub_le H.2 t 0
    rw [h0, sub_zero, abs_of_nonneg ht.1, mul_comm] at h
    exact h
  have hlt : t * ‖H.val‖ < 1 / 10 := by
    have h1 : t * ‖H.val‖ ≤ r₀ * ‖H.val‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    have h2 : r₀ * ‖H.val‖ < r₀ * (‖H.val‖ + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hr₀
    have h3 : r₀ * (‖H.val‖ + 1) = 1 / 20 := by
      dsimp only [r₀]
      field_simp [hden.ne']
    linarith only [h1, h2, h3]
  have hfit : HasProjectiveCircuitApproximation N (t * ‖H.val‖) s (unitaryEvolution H.val t) := by
    refine ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, ?_⟩
    simpa only [one_smul, TwoQubitCircuit.one_eval, Submonoid.coe_one] using hstep
  exact ((hasProjectiveCircuitApproximation_iff_infDist ..).mp hfit).trans_lt hlt

/-- Every nonnegative time at or before `tenthPlateauOnset H s` is `(1/10, s)`-affordable,
with no nonemptiness side condition on the hard set. -/
theorem affordable_of_le_tenthPlateauOnset {N s : ℕ} (H : selfAdjoint (Register N))
    {T : ℝ} (hT0 : 0 ≤ T) (hT : T ≤ tenthPlateauOnset H s) :
    HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val T) := by
  let E := {t : ℝ | 0 ≤ t ∧
    ¬ HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val t)}
  by_cases hE : E.Nonempty
  · obtain ⟨B, hB0, hBnot⟩ := hE
    have hB_gt : 1 / 10 < orbitCircuitDistance H s B :=
      lt_of_not_ge fun hle => hBnot ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr hle)
    obtain ⟨hr₀, hearly⟩ := early_tenth_bound H s
    exact (tenthPlateauOnset_spec H hr₀ hB0 hearly hB_gt).2.2.1 T ⟨hT0, hT⟩
  · by_contra hnot
    exact hE ⟨T, hT0, hnot⟩

/-- Single-date detuning-free onset certification: if `e^{-i T H}` is not `(1/10, s)`-affordable
at a single date `T ≥ 0`, then `tenthPlateauOnset H s` is strictly between
`1 / (20 * (‖H‖ + 1))` and `T` and attains distance `1 / 10`. -/
theorem tenthPlateauOnset_lt_of_not_affordable {N s : ℕ} (H : selfAdjoint (Register N))
    {T : ℝ} (hT0 : 0 ≤ T)
    (hnot : ¬ HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val T)) :
    let τ := tenthPlateauOnset H s
    1 / (20 * (‖H.val‖ + 1)) < τ ∧ τ < T ∧
      (∀ t ∈ Icc 0 τ, HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val t)) ∧
      orbitCircuitDistance H s τ = 1 / 10 ∧
      (∀ δ : ℝ, 0 < δ → 0 < volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc τ (τ + δ))) := by
  obtain ⟨hr₀, hearly⟩ := early_tenth_bound H s
  have hT_gt : 1 / 10 < orbitCircuitDistance H s T :=
    lt_of_not_ge fun hle => hnot ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr hle)
  exact tenthPlateauOnset_spec H hr₀ hT0 hearly hT_gt

/-- Monotonicity of `tenthPlateauOnset` across budgets once the larger budget eventually fails. -/
theorem tenthPlateauOnset_mono {N s₁ s₂ : ℕ} (H : selfAdjoint (Register N))
    (hs : s₁ ≤ s₂)
    (hfail : ∃ T : ℝ, 0 ≤ T ∧
      ¬ HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s₂ (unitaryEvolution H.val T)) :
    tenthPlateauOnset H s₁ ≤ tenthPlateauOnset H s₂ := by
  obtain ⟨T, hT0, hnot⟩ := hfail
  refine csInf_le_csInf ⟨0, fun _ ht => ht.1⟩ ⟨T, hT0, hnot⟩ ?_
  rintro t ⟨ht0, hnot₂⟩
  refine ⟨ht0, fun ⟨z, hz, C, hC, herr⟩ => hnot₂ ⟨z, hz, C, hC.trans hs, herr⟩⟩

private theorem bddAbove_circuitCommutator {N s : ℕ} (A B : Register N) :
    BddAbove (range fun C : {C : TwoQubitCircuit N // C.gateCount ≤ s} =>
      ‖matrixCommutator (star (C.val.eval : Register N) * A * (C.val.eval : Register N)) B‖) := by
  refine ⟨2 * ‖A‖ * ‖B‖, ?_⟩
  rintro _ ⟨C, rfl⟩
  let X := star (C.val.eval : Register N) * A * (C.val.eval : Register N)
  have hU : ‖(C.val.eval : Register N)‖ ≤ 1 :=
    (CStarRing.norm_of_mem_unitary C.val.eval.2).le
  have hX : ‖X‖ ≤ ‖A‖ := calc
    ‖star (C.val.eval : Register N) * A * (C.val.eval : Register N)‖
        ≤ ‖star (C.val.eval : Register N) * A‖ * ‖(C.val.eval : Register N)‖ := norm_mul_le _ _
    _ ≤ (1 * ‖A‖) * 1 := mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (by simpa only [norm_star] using hU) (norm_nonneg _)))
        hU (norm_nonneg _) (by positivity)
    _ = ‖A‖ := by ring
  unfold matrixCommutator
  calc ‖X * B - B * X‖ ≤ ‖X * B‖ + ‖B * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖B‖ + ‖B‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := add_le_add
        (mul_le_mul_of_nonneg_right hX (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hX (norm_nonneg _))
    _ = 2 * ‖A‖ * ‖B‖ := by ring

private theorem conjugate_diff_norm {N : ℕ} (U V A : Register N)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hA : ‖A‖ ≤ 1) :
    ‖star U * A * U - star V * A * V‖ ≤ 2 * ‖U - V‖ := by
  have h : star U * A * U - star V * A * V = star (U - V) * A * U + star V * A * (U - V) := by
    rw [star_sub]; noncomm_ring
  have h₁ : ‖star (U - V) * A * U‖ ≤ ‖U - V‖ := calc
    ‖star (U - V) * A * U‖ ≤ ‖star (U - V) * A‖ * ‖U‖ := norm_mul_le _ _
    _ ≤ (‖U - V‖ * 1) * 1 := mul_le_mul
        ((norm_mul_le _ _).trans (by rw [norm_star]; exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)))
        hU (norm_nonneg _) (by positivity)
    _ = ‖U - V‖ := by ring
  have h₂ : ‖star V * A * (U - V)‖ ≤ ‖U - V‖ := calc
    ‖star V * A * (U - V)‖ ≤ ‖star V * A‖ * ‖U - V‖ := norm_mul_le _ _
    _ ≤ (1 * 1) * ‖U - V‖ := mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul (by simpa only [norm_star] using hV) hA (norm_nonneg _) zero_le_one))
        le_rfl (norm_nonneg _) (by positivity)
    _ = ‖U - V‖ := by ring
  rw [h]
  linarith only [norm_add_le (star (U - V) * A * U) (star V * A * (U - V)), h₁, h₂]

/-- Universal commutator-deficit bound: the excess of `‖[U(T)* A U(T), B]‖` over the `s`-gate
commutator capacity is at most `4 * orbitCircuitDistance H s T`. -/
theorem commutator_deficit_le_four_orbitCircuitDistance {N s : ℕ}
    (H : selfAdjoint (Register N)) {A B : Register N} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (T : ℝ) :
    ‖matrixCommutator (star (unitaryEvolution H.val T) * A * unitaryEvolution H.val T) B‖ -
      circuitCommutatorCap N s A B ≤ 4 * orbitCircuitDistance H s T := by
  let U := unitaryEvolution H.val T
  obtain ⟨z, hz, C, hC, herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist
    U s (orbitCircuitDistance H s T)).mpr le_rfl
  let V : Register N := z • (C.eval : Register N)
  have hU : ‖U‖ ≤ 1 := (CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary H.2 T)).le
  have hV : ‖V‖ ≤ 1 := by
    simp only [V, norm_smul, hz, one_mul, (CStarRing.norm_of_mem_unitary C.eval.2).le]
  have hphase : star V * A * V = star (C.eval : Register N) * A * (C.eval : Register N) := by
    simp only [V, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show z * star z = 1 by simp [Complex.mul_conj', hz], one_smul]
  let X := star U * A * U
  let Y := star V * A * V
  have hcomm_sub : matrixCommutator X B - matrixCommutator Y B = matrixCommutator (X - Y) B := by
    unfold matrixCommutator; noncomm_ring
  have hdiff : ‖matrixCommutator X B‖ - ‖matrixCommutator Y B‖ ≤ 4 * ‖U - V‖ := by
    have hle : ‖matrixCommutator X B‖ - ‖matrixCommutator Y B‖ ≤ ‖matrixCommutator (X - Y) B‖ := by
      rw [← hcomm_sub]
      exact norm_sub_norm_le (matrixCommutator X B) (matrixCommutator Y B)
    have hXY : ‖X - Y‖ ≤ 2 * ‖U - V‖ := conjugate_diff_norm U V A hU hV hA
    have hcomm_le : ‖matrixCommutator (X - Y) B‖ ≤ 2 * ‖X - Y‖ := calc
      ‖(X - Y) * B - B * (X - Y)‖ ≤ ‖(X - Y) * B‖ + ‖B * (X - Y)‖ := norm_sub_le _ _
      _ ≤ ‖X - Y‖ * ‖B‖ + ‖B‖ * ‖X - Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖X - Y‖ * 1 + 1 * ‖X - Y‖ := add_le_add
          (mul_le_mul_of_nonneg_left hB (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
      _ = 2 * ‖X - Y‖ := by ring
    linarith only [hle, hXY, hcomm_le]
  have hcap : ‖matrixCommutator Y B‖ ≤ circuitCommutatorCap N s A B := by
    dsimp only [Y]
    rw [hphase]
    exact le_csSup (bddAbove_circuitCommutator A B) (mem_range_self (⟨C, hC⟩ : {C : TwoQubitCircuit N // C.gateCount ≤ s}))
  linarith only [hdiff, hcap, herr]

/-- Detuning-free single non-commutative commutator witness bound on `tenthPlateauOnset H s`. -/
theorem tenthPlateauOnset_lt_of_commutator_witness {N s : ℕ}
    (H : selfAdjoint (Register N)) {A B : Register N} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    {T : ℝ} (hT0 : 0 ≤ T)
    (hwit : circuitCommutatorCap N s A B + 2 / 5 <
      ‖matrixCommutator (star (unitaryEvolution H.val T) * A * unitaryEvolution H.val T) B‖) :
    1 / (20 * (‖H.val‖ + 1)) < tenthPlateauOnset H s ∧ tenthPlateauOnset H s < T ∧
      orbitCircuitDistance H s (tenthPlateauOnset H s) = 1 / 10 := by
  have hnot : ¬ HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val T) := by
    intro hfit
    have hd := (hasProjectiveCircuitApproximation_iff_infDist ..).mp hfit
    have hc := commutator_deficit_le_four_orbitCircuitDistance (s := s) H hA hB T
    change orbitCircuitDistance H s T ≤ 1 / 10 at hd
    linarith only [hwit, hc, hd]
  obtain ⟨hlo, hhi, _, heq, _⟩ := tenthPlateauOnset_lt_of_not_affordable H hT0 hnot
  exact ⟨hlo, hhi, heq⟩

/-- Detuning-free single unitary target witness bound on `tenthPlateauOnset H s`. -/
theorem tenthPlateauOnset_lt_of_unitary_witness {N s : ℕ}
    (H : selfAdjoint (Register N)) {W : Register N} {r T : ℝ} (hT0 : 0 ≤ T)
    (hsep : ProjectiveCircuitSeparated N (1 / 10 + r) s W)
    (hclose : ∃ z : ℂ, ‖z‖ = 1 ∧ ‖unitaryEvolution H.val T - z • W‖ ≤ r) :
    1 / (20 * (‖H.val‖ + 1)) < tenthPlateauOnset H s ∧ tenthPlateauOnset H s < T ∧
      orbitCircuitDistance H s (tenthPlateauOnset H s) = 1 / 10 := by
  obtain ⟨z, hz, herr⟩ := hclose
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have hnot : ¬ HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val T) := by
    rintro ⟨c, hc, C, hC, hfit⟩
    have hfar := hsep (z⁻¹ * c) (by rw [norm_mul, norm_inv, hz, inv_one, one_mul, hc]) C hC
    have htri : ‖W - (z⁻¹ * c) • (C.eval : Register N)‖ ≤ 1 / 10 + r := by
      have hscale : ‖W - (z⁻¹ * c) • (C.eval : Register N)‖ =
          ‖z • W - c • (C.eval : Register N)‖ := by
        have h1 : z • (W - (z⁻¹ * c) • (C.eval : Register N)) =
            z • W - c • (C.eval : Register N) := by
          rw [smul_sub, smul_smul, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
        rw [← h1, norm_smul, hz, one_mul]
      rw [hscale, norm_sub_rev (z • W)]
      exact (norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution H.val T) _).trans
        (by rw [norm_sub_rev]; linarith only [hfit, herr])
    exact hfar.not_ge htri
  obtain ⟨hlo, hhi, _, heq, _⟩ := tenthPlateauOnset_lt_of_not_affordable H hT0 hnot
  exact ⟨hlo, hhi, heq⟩

/-- Every matrix entry is bounded in modulus by the `L²` operator norm. -/
theorem norm_entry_le_l2_opNorm {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (a b : I) :
    ‖M a b‖ ≤ ‖M‖ := by
  have hsingle : ‖(EuclideanSpace.single b (1 : ℂ) : EuclideanSpace ℂ I)‖ = 1 := by simp
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single b (1 : ℂ))
  rw [hsingle, mul_one] at h
  have hcol : M *ᵥ (EuclideanSpace.single b (1 : ℂ) : EuclideanSpace ℂ I).ofLp =
      fun i => M i b := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_ite_eq']
  have hcoord := PiLp.norm_apply_le
    ((EuclideanSpace.equiv I ℂ).symm (M *ᵥ (EuclideanSpace.single b (1 : ℂ)).ofLp)) a
  rw [hcol] at h hcoord
  exact le_trans hcoord h

private theorem pauli_mul_entry {N : ℕ} (P Q : Fin N → Option (Fin 3)) (x z : Config N) :
    (finitePauliMatrix P * finitePauliMatrix Q) x z =
      ∏ s, (boolPauliOption (P s) * boolPauliOption (Q s)) (x s) (z s) := by
  rw [Matrix.mul_apply]
  change (∑ y : Config N,
    (∏ s, boolPauliOptionEntry (P s) (x s, y s)) *
      ∏ s, boolPauliOptionEntry (Q s) (y s, z s)) = _
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun s (b : Bool) =>
    boolPauliOptionEntry (P s) (x s, b) * boolPauliOptionEntry (Q s) (b, z s))]
  rfl

/-- Single-site Pauli OTOC collapse at `1` gate: for any distinct wires `i ≠ j`,
`Z_i` and `X_j` commute at `t = 0`, yet `circuitCommutatorCap N s Z_i X_j = 2` for every
`s ≥ 1`, attaining the universal unitary commutator ceiling `2`. -/
theorem circuitCommutatorCap_singleSitePauli_eq_two {N s : ℕ} (hs : 1 ≤ s)
    (i j : Fin N) (hij : i ≠ j) :
    let Z_i := finitePauliMatrix (singleSitePauliLabel i 2)
    let X_j := finitePauliMatrix (singleSitePauliLabel j 0)
    matrixCommutator Z_i X_j = 0 ∧
      (∀ U : UGroup N, ‖matrixCommutator (star U.val * Z_i * U.val) X_j‖ ≤ 2) ∧
      circuitCommutatorCap N s Z_i X_j = 2 := by
  intro Z_i X_j
  have hZi_unit : Z_i ∈ unitary (Register N) := by
    rw [Unitary.mem_iff, star_eq_conjTranspose, (finitePauliMatrix_isHermitian _).eq]
    exact ⟨finitePauliMatrix_mul_self _, finitePauliMatrix_mul_self _⟩
  have hXj_unit : X_j ∈ unitary (Register N) := by
    rw [Unitary.mem_iff, star_eq_conjTranspose, (finitePauliMatrix_isHermitian _).eq]
    exact ⟨finitePauliMatrix_mul_self _, finitePauliMatrix_mul_self _⟩
  have hZi_norm : ‖Z_i‖ = 1 := CStarRing.norm_of_mem_unitary hZi_unit
  have hXj_norm : ‖X_j‖ = 1 := CStarRing.norm_of_mem_unitary hXj_unit
  -- 1. [Z_i, X_j] = 0 for i ≠ j
  have hcomm0 : matrixCommutator Z_i X_j = 0 := by
    unfold matrixCommutator
    rw [sub_eq_zero]
    ext x z
    rw [pauli_mul_entry, pauli_mul_entry]
    refine Finset.prod_congr rfl fun q _ => ?_
    by_cases hqi : q = i
    · subst hqi
      simp [singleSitePauliLabel, hij, boolPauliOption]
    · by_cases hqj : q = j
      · subst hqj
        simp [singleSitePauliLabel, hij.symm, boolPauliOption]
      · simp [singleSitePauliLabel, hqi, hqj, boolPauliOption]
  -- 2. Universal ceiling ≤ 2
  have hceil (U : UGroup N) : ‖matrixCommutator (star U.val * Z_i * U.val) X_j‖ ≤ 2 := by
    have hconj_unit : star U.val * Z_i * U.val ∈ unitary (Register N) :=
      mul_mem (mul_mem (Unitary.star_mem U.2) hZi_unit) U.2
    have h1 : ‖star U.val * Z_i * U.val‖ = 1 := CStarRing.norm_of_mem_unitary hconj_unit
    unfold matrixCommutator
    calc ‖(star U.val * Z_i * U.val) * X_j - X_j * (star U.val * Z_i * U.val)‖
        ≤ ‖(star U.val * Z_i * U.val) * X_j‖ + ‖X_j * (star U.val * Z_i * U.val)‖ := norm_sub_le _ _
      _ ≤ ‖star U.val * Z_i * U.val‖ * ‖X_j‖ + ‖X_j‖ * ‖star U.val * Z_i * U.val‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 := by rw [h1, hXj_norm]; norm_num
  -- 3. Attainment at 1 gate via Haferkamp SU(4) Pauli transport
  refine ⟨hcomm0, hceil, le_antisymm ?_ ?_⟩
  · refine csSup_le ⟨_, mem_range_self
      (⟨TwoQubitCircuit.one N, Nat.zero_le _⟩ : {C : TwoQubitCircuit N // C.gateCount ≤ s})⟩ ?_
    rintro _ ⟨C, rfl⟩
    exact hceil C.val.eval
  · obtain ⟨G, c, _, htrans⟩ := finitePauliMatrix_exists_twoQubitLift_transport
      (singleSitePauliLabel i 2) i j hij (Or.inl (by simp [singleSitePauliLabel]))
    have hupd : updateTwoQubitPauliLabel (singleSitePauliLabel i 2) i j none (some 2) =
        singleSitePauliLabel j 2 := by
      funext q
      by_cases hqi : q = i
      · subst hqi
        simp [updateTwoQubitPauliLabel, singleSitePauliLabel, hij]
      · by_cases hqj : q = j
        · subst hqj
          simp [updateTwoQubitPauliLabel, singleSitePauliLabel]
        · simp [updateTwoQubitPauliLabel, singleSitePauliLabel, hqi, hqj]
    rw [hupd] at htrans
    let Z_j := finitePauliMatrix (singleSitePauliLabel j 2)
    have hZj_unit : Z_j ∈ unitary (Register N) := by
      rw [Unitary.mem_iff, star_eq_conjTranspose, (finitePauliMatrix_isHermitian _).eq]
      exact ⟨finitePauliMatrix_mul_self _, finitePauliMatrix_mul_self _⟩
    have hZj_norm : ‖Z_j‖ = 1 := CStarRing.norm_of_mem_unitary hZj_unit
    let L := twoQubitLift i j hij G
    have hc_norm : ‖c‖ = 1 := by
      have hn := congrArg norm htrans
      rw [← star_eq_conjTranspose, l2_opNorm_unitary_conj_eq L.2, hZi_norm,
        norm_smul, hZj_norm, mul_one] at hn
      exact hn.symm
    let C := TwoQubitCircuit.singleOn i j hij G⁻¹
    have hC_count : C.gateCount ≤ s := hs
    have hC_eval : (C.eval : Register N) = star (L : Register N) := by
      rw [TwoQubitCircuit.singleOn_eval]
      have htensor : Quantum.tensorGate (specialUnitaryAsUnitary G)
          (1 : Matrix.unitaryGroup ({q : Fin N // q ≠ i ∧ q ≠ j} → Bool) ℂ) *
          Quantum.tensorGate (specialUnitaryAsUnitary G⁻¹)
            (1 : Matrix.unitaryGroup ({q : Fin N // q ≠ i ∧ q ≠ j} → Bool) ℂ) = 1 := by
        apply Subtype.ext
        change ((G.val ⊗ₖ (1 : Matrix _ _ ℂ)) * ((star G.val) ⊗ₖ (1 : Matrix _ _ ℂ))) = 1
        rw [← Matrix.mul_kronecker_mul, mul_one,
          (Unitary.mem_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup G.2)).2,
          Matrix.one_kronecker_one]
      have hmul : twoQubitLift i j hij G * twoQubitLift i j hij G⁻¹ = 1 := by
        unfold twoQubitLift
        rw [← map_mul, htensor, map_one]
      have hinv : twoQubitLift i j hij G⁻¹ = L⁻¹ := mul_left_cancel (hmul.trans (mul_inv_cancel L).symm)
      rw [hinv]
      rfl
    have hC_conj : star (C.eval : Register N) * Z_i * (C.eval : Register N) = c • Z_j := by
      rw [hC_eval, star_star, star_eq_conjTranspose]
      exact htrans
    let x₀ : Config N := fun _ => false
    let y₀ : Config N := Function.update x₀ j true
    have hentry : (matrixCommutator (c • Z_j) X_j) y₀ x₀ = -(2 * c) := by
      have hsmul : matrixCommutator (c • Z_j) X_j = c • (Z_j * X_j - X_j * Z_j) := by
        unfold matrixCommutator; rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      rw [hsmul, Matrix.smul_apply, Matrix.sub_apply, pauli_mul_entry, pauli_mul_entry]
      have hp1 : (∏ q : Fin N, (boolPauliOption (singleSitePauliLabel j 2 q) *
          boolPauliOption (singleSitePauliLabel j 0 q)) (y₀ q) (x₀ q)) = -1 := by
        rw [Finset.prod_eq_single j]
        · simp [y₀, x₀, singleSitePauliLabel, boolPauliOption, finiteQubitPauli, Matrix.mul_apply]
        · intro q _ hqj
          simp [y₀, x₀, singleSitePauliLabel, hqj, boolPauliOption]
        · simp
      have hp2 : (∏ q : Fin N, (boolPauliOption (singleSitePauliLabel j 0 q) *
          boolPauliOption (singleSitePauliLabel j 2 q)) (y₀ q) (x₀ q)) = 1 := by
        rw [Finset.prod_eq_single j]
        · simp [y₀, x₀, singleSitePauliLabel, boolPauliOption, finiteQubitPauli, Matrix.mul_apply]
        · intro q _ hqj
          simp [y₀, x₀, singleSitePauliLabel, hqj, boolPauliOption]
        · simp
      rw [hp1, hp2]
      simp only [smul_eq_mul]
      ring
    have hnorm_ge : 2 ≤ ‖matrixCommutator (star (C.eval : Register N) * Z_i * (C.eval : Register N)) X_j‖ := by
      rw [hC_conj]
      have hle := norm_entry_le_l2_opNorm (matrixCommutator (c • Z_j) X_j) y₀ x₀
      rw [hentry, norm_neg, norm_mul, hc_norm, mul_one] at hle
      norm_num at hle
      exact hle
    exact hnorm_ge.trans (le_csSup (bddAbove_circuitCommutator Z_i X_j)
      (mem_range_self (⟨C, hC_count⟩ : {C : TwoQubitCircuit N // C.gateCount ≤ s})))

private theorem norm_configMatrixUnit {N : ℕ} (a b : Config N) :
    ‖configMatrixUnit a b‖ = 1 := by
  letI : Nonempty (Config N) := ⟨a⟩
  have hstar (x y : Config N) : star (configMatrixUnit x y) = configMatrixUnit y x := by
    ext i j
    simp only [configMatrixUnit, Matrix.star_apply]
    by_cases h : j = x ∧ i = y
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩, star_one]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), star_zero]
  have hmul : configMatrixUnit b a * configMatrixUnit a b = configMatrixUnit b b := by
    ext i j
    simp only [configMatrixUnit, Matrix.mul_apply]
    rw [Finset.sum_eq_single a
      (fun k _ hka => by simp [hka]) (by simp)]
    by_cases hi : i = b <;> by_cases hj : j = b <;> simp [hi, hj]
  have hdiag_idem : configMatrixUnit b b * configMatrixUnit b b = configMatrixUnit b b := by
    ext i j
    simp only [configMatrixUnit, Matrix.mul_apply]
    rw [Finset.sum_eq_single b (fun k _ hkb => by simp [hkb]) (by simp)]
    by_cases hi : i = b <;> by_cases hj : j = b <;> simp [hi, hj]
  have hdiag_ne : configMatrixUnit b b ≠ 0 := fun h0 => by
    have := congrFun (congrFun h0 b) b
    simp [configMatrixUnit] at this
  have hdiag_norm : ‖configMatrixUnit b b‖ = 1 := by
    have hsq := CStarRing.norm_star_mul_self (x := configMatrixUnit b b)
    rw [hstar b b, hdiag_idem] at hsq
    have hpos : 0 < ‖configMatrixUnit b b‖ := norm_pos_iff.mpr hdiag_ne
    nlinarith only [hsq, hpos]
  have hsq := CStarRing.norm_star_mul_self (x := configMatrixUnit a b)
  rw [hstar a b, hmul, hdiag_norm] at hsq
  nlinarith only [hsq, norm_nonneg (configMatrixUnit a b)]

/-- Positive non-local commutator survivor: a rank-one basis projector `A = |x₀⟩⟨x₀|` and
conjugate partial swap `B = W* (|x₀⟩⟨x₁| + |x₁⟩⟨x₀|) W` (`x₀ ≠ x₁`) both have norm `1`,
satisfy `‖[V* A V, B]‖ ≤ 2 * (‖(V W*)_{x₀,x₀}‖ + ‖(V W*)_{x₀,x₁}‖)` for every `V ∈ U(2^N)`
and `‖[W* A W, B]‖ = 1`, certifying `tenthPlateauOnset H s < T` whenever `U(T) = W` and
all `s`-gate circuits satisfy `‖(C W*)_{x₀,x₀}‖ + ‖(C W*)_{x₀,x₁}‖ ≤ 1 / 4`. -/
theorem rankOne_partialSwap_commutator_witness {N : ℕ} (x₀ x₁ : Config N) (hx : x₀ ≠ x₁)
    (W : UGroup N) :
    let A := configMatrixUnit x₀ x₀
    let S₀₁ := configMatrixUnit x₀ x₁ + configMatrixUnit x₁ x₀
    let B := star W.val * S₀₁ * W.val
    ‖A‖ = 1 ∧ ‖B‖ = 1 ∧
      (∀ V : UGroup N,
        ‖matrixCommutator (star V.val * A * V.val) B‖ ≤
          2 * (‖(V.val * star W.val) x₀ x₀‖ + ‖(V.val * star W.val) x₀ x₁‖)) ∧
      ‖matrixCommutator (star W.val * A * W.val) B‖ = 1 ∧
      (∀ (s : ℕ) (H : selfAdjoint (Register N)) (T : ℝ), 0 ≤ T →
        unitaryEvolution H.val T = W.val →
        (∀ C : TwoQubitCircuit N, C.gateCount ≤ s →
          ‖((C.eval : Register N) * star W.val) x₀ x₀‖ +
            ‖((C.eval : Register N) * star W.val) x₀ x₁‖ ≤ 1 / 4) →
        circuitCommutatorCap N s A B ≤ 1 / 2 ∧
          1 / (20 * (‖H.val‖ + 1)) < tenthPlateauOnset H s ∧
          tenthPlateauOnset H s < T ∧
          orbitCircuitDistance H s (tenthPlateauOnset H s) = 1 / 10) := by
  intro A S₀₁ B
  letI : Nonempty (Config N) := ⟨x₀⟩
  have hA_norm : ‖A‖ = 1 := norm_configMatrixUnit x₀ x₀
  have hunit_mul (a b c d : Config N) :
      configMatrixUnit a b * configMatrixUnit c d =
        if b = c then configMatrixUnit a d else 0 := by
    ext i j
    simp only [configMatrixUnit, Matrix.mul_apply]
    rw [Finset.sum_eq_single b (fun k _ hkb => by simp [hkb]) (by simp)]
    by_cases hbc : b = c <;> by_cases hi : i = a <;> by_cases hj : j = d <;>
      simp [configMatrixUnit, hbc, hi, hj]
  have hunit_star (a b : Config N) : star (configMatrixUnit a b) = configMatrixUnit b a := by
    ext i j
    simp only [configMatrixUnit, Matrix.star_apply]
    by_cases h : j = a ∧ i = b
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩, star_one]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), star_zero]
  let P₀₁ := configMatrixUnit x₀ x₀ + configMatrixUnit x₁ x₁
  have hP_star : star P₀₁ = P₀₁ := by
    dsimp only [P₀₁]; rw [star_add, hunit_star, hunit_star]
  have hP_idem : P₀₁ * P₀₁ = P₀₁ := by
    dsimp only [P₀₁]
    rw [add_mul, mul_add, mul_add, hunit_mul, hunit_mul, hunit_mul, hunit_mul]
    simp [hx, hx.symm]
  have hP_ne : P₀₁ ≠ 0 := fun h0 => by
    have := congrFun (congrFun h0 x₀) x₀
    simp [P₀₁, configMatrixUnit, hx] at this
  have hP_norm : ‖P₀₁‖ = 1 := by
    have hsq := CStarRing.norm_star_mul_self (x := P₀₁)
    rw [hP_star, hP_idem] at hsq
    have hpos : 0 < ‖P₀₁‖ := norm_pos_iff.mpr hP_ne
    nlinarith only [hsq, hpos]
  have hS_star : star S₀₁ = S₀₁ := by
    dsimp only [S₀₁]; rw [star_add, hunit_star, hunit_star, add_comm]
  have hS_sq : S₀₁ * S₀₁ = P₀₁ := by
    dsimp only [S₀₁, P₀₁]
    rw [add_mul, mul_add, mul_add, hunit_mul, hunit_mul, hunit_mul, hunit_mul]
    simp [hx, hx.symm]
  have hS_norm : ‖S₀₁‖ = 1 := by
    have hsq := CStarRing.norm_star_mul_self (x := S₀₁)
    rw [hS_star, hS_sq, hP_norm] at hsq
    nlinarith only [hsq, norm_nonneg S₀₁]
  have hB_norm : ‖B‖ = 1 := by
    dsimp only [B]
    have h := l2_opNorm_unitary_conj_eq (Unitary.star_mem W.2) S₀₁
    simpa only [star_star] using h.trans hS_norm
  -- Commutator upper bound for arbitrary V ∈ U(2^N)
  have hV_bound (V : UGroup N) :
      ‖matrixCommutator (star V.val * A * V.val) B‖ ≤
        2 * (‖(V.val * star W.val) x₀ x₀‖ + ‖(V.val * star W.val) x₀ x₁‖) := by
    let Q := V.val * star W.val
    have hQ_unit : Q ∈ unitary (Register N) := mul_mem V.2 (Unitary.star_mem W.2)
    have hQ_norm : ‖Q‖ = 1 := CStarRing.norm_of_mem_unitary hQ_unit
    have hconj_eq : matrixCommutator (star V.val * A * V.val) B =
        star W.val * matrixCommutator (star Q * A * Q) S₀₁ * W.val := by
      dsimp only [B, Q, matrixCommutator]
      rw [star_mul, star_star]
      calc (star V.val * A * V.val) * (star W.val * S₀₁ * W.val) -
            (star W.val * S₀₁ * W.val) * (star V.val * A * V.val)
          = star W.val * ((W.val * star V.val) * A * (V.val * star W.val) * S₀₁) * W.val -
              star W.val * (S₀₁ * (W.val * star V.val) * A * (V.val * star W.val)) * W.val := by
            have h1 : (star W.val * W.val) = 1 := (Unitary.mem_iff.mp W.2).1
            calc (star V.val * A * V.val) * (star W.val * S₀₁ * W.val) -
                  (star W.val * S₀₁ * W.val) * (star V.val * A * V.val)
                = (star W.val * W.val) * (star V.val * A * V.val * star W.val * S₀₁ * W.val) -
                    (star W.val * S₀₁ * W.val * star V.val * A * V.val) * (star W.val * W.val) := by
                  rw [h1, one_mul, mul_one]; simp only [mul_assoc]
              _ = _ := by simp only [mul_assoc]
        _ = star W.val * (((W.val * star V.val) * A * (V.val * star W.val)) * S₀₁ -
              S₀₁ * ((W.val * star V.val) * A * (V.val * star W.val))) * W.val := by
            noncomm_ring
    have hnorm_conj : ‖matrixCommutator (star V.val * A * V.val) B‖ =
        ‖matrixCommutator (star Q * A * Q) S₀₁‖ := by
      rw [hconj_eq]
      have h := l2_opNorm_unitary_conj_eq (Unitary.star_mem W.2)
        (matrixCommutator (star Q * A * Q) S₀₁)
      simpa only [star_star] using h
    rw [hnorm_conj]
    have hAQ (b : Config N) : A * Q * configMatrixUnit b b = Q x₀ b • configMatrixUnit x₀ b := by
      ext i j
      simp only [A, configMatrixUnit, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single b (fun k _ hkb => by simp [hkb]) (by simp)]
      by_cases hj : j = b
      · subst hj
        simp only [and_self, if_true, mul_one]
        rw [Finset.sum_eq_single x₀ (fun k _ hk0 => by simp [hk0]) (by simp)]
        by_cases hi : i = x₀ <;> simp [hi]
      · simp [hj]
    have hAS : A * Q * S₀₁ =
        Q x₀ x₁ • configMatrixUnit x₀ x₀ + Q x₀ x₀ • configMatrixUnit x₀ x₁ := by
      have hS_split : S₀₁ = configMatrixUnit x₀ x₀ * S₀₁ + configMatrixUnit x₁ x₁ * S₀₁ := by
        dsimp only [S₀₁]
        rw [mul_add, mul_add, hunit_mul, hunit_mul, hunit_mul, hunit_mul]
        simp [hx, hx.symm]
      calc A * Q * S₀₁ = A * Q * (configMatrixUnit x₀ x₀ * S₀₁ + configMatrixUnit x₁ x₁ * S₀₁) := by
              conv_lhs => rw [hS_split]
        _ = (A * Q * configMatrixUnit x₀ x₀) * S₀₁ + (A * Q * configMatrixUnit x₁ x₁) * S₀₁ := by
              noncomm_ring
        _ = (Q x₀ x₀ • configMatrixUnit x₀ x₀) * (configMatrixUnit x₀ x₁ + configMatrixUnit x₁ x₀) +
              (Q x₀ x₁ • configMatrixUnit x₀ x₁) * (configMatrixUnit x₀ x₁ + configMatrixUnit x₁ x₀) := by
              rw [hAQ x₀, hAQ x₁]
        _ = Q x₀ x₁ • configMatrixUnit x₀ x₀ + Q x₀ x₀ • configMatrixUnit x₀ x₁ := by
              simp only [Matrix.smul_mul, mul_add, hunit_mul, if_true, if_neg hx, if_neg hx.symm,
                smul_zero, zero_add, add_comm]
    have hprod_le : ‖(star Q * A * Q) * S₀₁‖ ≤ ‖Q x₀ x₀‖ + ‖Q x₀ x₁‖ := calc
      ‖(star Q * A * Q) * S₀₁‖ = ‖star Q * (A * Q * S₀₁)‖ := by simp only [mul_assoc]
      _ ≤ ‖star Q‖ * ‖A * Q * S₀₁‖ := norm_mul_le _ _
      _ = ‖A * Q * S₀₁‖ := by rw [norm_star, hQ_norm, one_mul]
      _ ≤ ‖Q x₀ x₁ • configMatrixUnit x₀ x₀‖ + ‖Q x₀ x₀ • configMatrixUnit x₀ x₁‖ := by
          rw [hAS]; exact norm_add_le _ _
      _ = ‖Q x₀ x₀‖ + ‖Q x₀ x₁‖ := by
          rw [norm_smul, norm_smul, norm_configMatrixUnit, norm_configMatrixUnit,
            mul_one, mul_one, add_comm]
    have hprod_le' : ‖S₀₁ * (star Q * A * Q)‖ ≤ ‖Q x₀ x₀‖ + ‖Q x₀ x₁‖ := by
      have hQAQ_star : star (star Q * A * Q) = star Q * A * Q := by
        have hconj_star (M : Register N) : star (star M * A * M) = star M * A * M := by
          have hA_star : star A = A := hunit_star x₀ x₀
          rw [star_mul, star_mul, star_star, hA_star, ← mul_assoc]
        exact hconj_star Q
      have hst : star ((star Q * A * Q) * S₀₁) = S₀₁ * (star Q * A * Q) := by
        rw [star_mul, hS_star, hQAQ_star]
      rw [← hst, norm_star]
      exact hprod_le
    unfold matrixCommutator
    linarith only [norm_sub_le ((star Q * A * Q) * S₀₁) (S₀₁ * (star Q * A * Q)), hprod_le, hprod_le']
  -- Exact commutator norm = 1 at V = W
  have hW_eq : ‖matrixCommutator (star W.val * A * W.val) B‖ = 1 := by
    have hWW : W.val * star W.val = 1 := (Unitary.mem_iff.mp W.2).2
    have hcomm_W : matrixCommutator (star W.val * A * W.val) B =
        star W.val * (configMatrixUnit x₀ x₁ - configMatrixUnit x₁ x₀) * W.val := by
      have hAS₀ : A * S₀₁ - S₀₁ * A = configMatrixUnit x₀ x₁ - configMatrixUnit x₁ x₀ := by
        dsimp only [A, S₀₁]
        rw [mul_add, add_mul, hunit_mul, hunit_mul, hunit_mul, hunit_mul]
        simp [hx, hx.symm]
      dsimp only [B, matrixCommutator]
      calc (star W.val * A * W.val) * (star W.val * S₀₁ * W.val) -
            (star W.val * S₀₁ * W.val) * (star W.val * A * W.val)
          = star W.val * A * (W.val * star W.val) * S₀₁ * W.val -
              star W.val * S₀₁ * (W.val * star W.val) * A * W.val := by simp only [mul_assoc]
        _ = star W.val * (A * S₀₁ - S₀₁ * A) * W.val := by rw [hWW]; noncomm_ring
        _ = star W.val * (configMatrixUnit x₀ x₁ - configMatrixUnit x₁ x₀) * W.val := by rw [hAS₀]
    rw [hcomm_W]
    have hiso := l2_opNorm_unitary_conj_eq (Unitary.star_mem W.2)
      (configMatrixUnit x₀ x₁ - configMatrixUnit x₁ x₀)
    rw [star_star] at hiso
    rw [hiso]
    let D₀₁ := configMatrixUnit x₀ x₁ - configMatrixUnit x₁ x₀
    have hD_sq : star D₀₁ * D₀₁ = P₀₁ := by
      dsimp only [D₀₁, P₀₁]
      rw [star_sub, hunit_star, hunit_star, sub_mul, mul_sub, mul_sub,
        hunit_mul, hunit_mul, hunit_mul, hunit_mul]
      simp [hx, hx.symm, sub_neg_eq_add, add_comm]
    have hsq := CStarRing.norm_star_mul_self (x := D₀₁)
    rw [hD_sq, hP_norm] at hsq
    nlinarith only [hsq, norm_nonneg D₀₁]
  refine ⟨hA_norm, hB_norm, hV_bound, hW_eq, ?_⟩
  intro s H T hT0 hUT hcap_in
  have hcap_le : circuitCommutatorCap N s A B ≤ 1 / 2 := by
    refine csSup_le ⟨_, mem_range_self
      (⟨TwoQubitCircuit.one N, Nat.zero_le _⟩ : {C : TwoQubitCircuit N // C.gateCount ≤ s})⟩ ?_
    rintro _ ⟨C, rfl⟩
    have hv := hV_bound C.val.eval
    have hin := hcap_in C.val C.property
    linarith only [hv, hin]
  have hwit : circuitCommutatorCap N s A B + 2 / 5 <
      ‖matrixCommutator (star (unitaryEvolution H.val T) * A * unitaryEvolution H.val T) B‖ := by
    rw [hUT, hW_eq]
    linarith only [hcap_le]
  exact ⟨hcap_le, tenthPlateauOnset_lt_of_commutator_witness H hA_norm.le hB_norm.le hT0 hwit⟩

/-- Off-diagonal penalty for non-commutative unitary targets: for any `a ≠ b`, the off-diagonal
matrix element of `W` in `H`'s eigenbasis lower-bounds `‖e^{-i t H} - z • W‖` for all `t ∈ ℝ`
and unit phases `z`. -/
theorem single_unitary_offDiag_floor {N : ℕ} (H : selfAdjoint (Register N))
    (W : Register N) {a b : Config N} (hab : a ≠ b) (t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    let V := hermitianEigenbasisUnitary H.2.isHermitian
    ‖(star V.val * W * V.val) a b‖ ≤ ‖unitaryEvolution H.val t - z • W‖ := by
  intro V
  have hconj : star V.val * (unitaryEvolution H.val t - z • W) * V.val =
      Matrix.diagonal (fun i => Complex.exp (-(Complex.I * (t * H.2.isHermitian.eigenvalues i)))) -
        z • (star V.val * W * V.val) := by
    rw [unitaryEvolution_spectral H.2.isHermitian]
    change star V.val * (V.val * Matrix.diagonal _ * star V.val - z • W) * V.val = _
    rw [Matrix.mul_sub, Matrix.sub_mul, star_conj_cancel V.2, Matrix.mul_smul, Matrix.smul_mul]
  have hiso := l2_opNorm_unitary_conj_eq (Unitary.star_mem V.2) (unitaryEvolution H.val t - z • W)
  rw [star_star, hconj] at hiso
  rw [← hiso]
  have hentry := norm_entry_le_l2_opNorm
    (Matrix.diagonal (fun i => Complex.exp (-(Complex.I * (t * H.2.isHermitian.eigenvalues i)))) -
      z • (star V.val * W * V.val)) a b
  simpa only [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hab, zero_sub,
    Matrix.smul_apply, smul_eq_mul, norm_neg, norm_mul, hz, one_mul] using hentry

/-- If a target `W` has an off-diagonal entry larger than `r` in `H`'s eigenbasis,
the physical trajectory never enters the projective `r`-ball around `W` at any real time. -/
theorem single_unitary_visitSet_empty_of_offDiag_gt {N : ℕ} (H : selfAdjoint (Register N))
    (W : Register N) {a b : Config N} (hab : a ≠ b) {r : ℝ}
    (hr : r < ‖(star (hermitianEigenbasisUnitary H.2.isHermitian).val * W *
      (hermitianEigenbasisUnitary H.2.isHermitian).val) a b‖) :
    {t : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ ‖unitaryEvolution H.val t - z • W‖ ≤ r} = ∅ := by
  ext t
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨z, hz, hle⟩
  exact hr.not_ge ((single_unitary_offDiag_floor H W hab t hz).trans hle)

private theorem isClosed_singleTargetCapture {N d : ℕ} (e : Config N ≃ Fin (d + 1))
    (V W : UGroup N) (r : ℝ) :
    IsClosed {x : Fin d → UnitAddCircle |
      ∃ c : ℂ, ‖c‖ = 1 ∧ ‖projectiveSpectralMatrix e V x - c • W.val‖ ≤ r} := by
  let K : Set (Register N) := (fun z : ℂ => z • W.val) '' Metric.sphere (0 : ℂ) 1
  have hK_compact : IsCompact K :=
    (isCompact_sphere (0 : ℂ) 1).image (continuous_id.smul continuous_const)
  have hK_ne : K.Nonempty := ⟨(1 : ℂ) • W.val, ⟨1, mem_sphere_zero_iff_norm.mpr norm_one, rfl⟩⟩
  have heq : {x : Fin d → UnitAddCircle |
      ∃ c : ℂ, ‖c‖ = 1 ∧ ‖projectiveSpectralMatrix e V x - c • W.val‖ ≤ r} =
      {x | Metric.infDist (projectiveSpectralMatrix e V x) K ≤ r} := by
    ext x
    constructor
    · rintro ⟨c, hc, hle⟩
      have hmem : c • W.val ∈ K := ⟨c, mem_sphere_zero_iff_norm.mpr hc, rfl⟩
      exact (Metric.infDist_le_dist_of_mem hmem).trans (by rwa [dist_eq_norm])
    · intro hinf
      obtain ⟨Y, ⟨c, hc, rfl⟩, hmin⟩ := exists_compactTarget_minDist hK_compact hK_ne
        (projectiveSpectralMatrix e V x)
      exact ⟨c, mem_sphere_zero_iff_norm.mp hc, by rw [← dist_eq_norm, hmin]; exact hinf⟩
  rw [heq]
  exact isClosed_le ((Metric.continuous_infDist_pt K).comp (continuous_projectiveSpectralMatrix e V))
    continuous_const

private theorem volume_singleTargetCapture_le {N d : ℕ}
    (e : Config N ≃ Fin (d + 1)) (V W : UGroup N) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 2)
    (hx_lt : physicalArc r + 1 / ((2 ^ N : ℕ) : ℝ) < 1) :
    volume.real {x : Fin d → UnitAddCircle |
      ∃ c : ℂ, ‖c‖ = 1 ∧ ‖projectiveSpectralMatrix e V x - c • W.val‖ ≤ r} ≤
      ((2 ^ N : ℕ) : ℝ) * (physicalArc r + 1 / ((2 ^ N : ℕ) : ℝ)) ^ (2 ^ N) := by
  let D : ℕ := 2 ^ N
  have hD_pos : 0 < (D : ℝ) := by positivity
  obtain ⟨hx_arc, htol⟩ := physicalArc_full hr
  let C : Register N := (V⁻¹ * W * V).val
  have hC_unit : C ∈ unitary (Register N) := (V⁻¹ * W * V).2
  let A := {x : Fin d → UnitAddCircle |
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖projectiveSpectralMatrix e V x - c • W.val‖ ≤ r}
  have hA_meas : MeasurableSet A := (isClosed_singleTargetCapture e V W r).measurableSet
  have hpre : (UnitaryBalls.anchorMap e) ⁻¹' A =
      UnitaryBalls.rotations {z : UnitAddTorus (Config N) |
        ‖C - UnitaryBalls.packet z‖ ≤ zeroGateArcTolerance (physicalArc r)} := by
    ext z
    rw [UnitaryBalls.rotations_iff_physical, htol]
    let q : ℂ := (z (e.symm 0)).toCircle
    have hq : ‖q‖ = 1 := Circle.norm_coe _
    have hq0 : q ≠ 0 := fun h0 => by simp [h0] at hq
    have hVCV : V.val * C * star V.val = W.val := by
      change ((V * (V⁻¹ * W * V) * V⁻¹ : UGroup N) : Register N) = W.val
      simp [mul_assoc]
    constructor
    · rintro ⟨c, hc, hle⟩
      refine ⟨q * c, by rw [norm_mul, hq, hc, one_mul], ?_⟩
      rw [← l2_opNorm_unitary_conj_eq V.2, Matrix.mul_sub, Matrix.sub_mul,
        UnitaryBalls.absolute_packet e V z, Matrix.mul_smul, Matrix.smul_mul, hVCV,
        ← smul_smul, ← smul_sub, norm_smul, hq, one_mul]
      exact hle
    · rintro ⟨c, hc, hle⟩
      refine ⟨q⁻¹ * c, by rw [norm_mul, norm_inv, hq, inv_one, one_mul, hc], ?_⟩
      have h1 : V.val * (UnitaryBalls.packet z - c • C) * star V.val =
          q • (projectiveSpectralMatrix e V (UnitaryBalls.anchorMap e z) - (q⁻¹ * c) • W.val) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, UnitaryBalls.absolute_packet e V z,
          Matrix.mul_smul, Matrix.smul_mul, hVCV, smul_sub, smul_smul, ← mul_assoc,
          mul_inv_cancel₀ hq0, one_mul]
      have hiso := l2_opNorm_unitary_conj_eq V.2 (UnitaryBalls.packet z - c • C)
      rw [h1, norm_smul, hq, one_mul] at hiso
      exact hiso.trans_le hle
  rw [← (UnitaryBalls.anchor_preserving e).measureReal_preimage hA_meas.nullMeasurableSet, hpre]
  let δ := 1 / (D : ℝ)
  have hδ : 0 < δ := one_div_pos.mpr hD_pos
  have hb := UnitaryBalls.volume_projective_unitary_ball hC_unit hx_arc.1.le hδ.le hx_lt
  have ht := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (add_nonneg hx_arc.1.le hδ.le),
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at ht
  change δ * volume.real _ ≤ (physicalArc r + δ) ^ D at ht
  have hmul := mul_le_mul_of_nonneg_left ht hD_pos.le
  have hDδ : (D : ℝ) * δ = 1 := mul_one_div_cancel hD_pos.ne'
  rwa [← mul_assoc, hDδ, one_mul] at hmul

/-- Doubly-exponential capture-density ceiling and syndetic clock lower bound for arbitrary
(commuting or non-commutative) single unitary targets `W ∈ U(2^N)` on maximally projective
Hamiltonians. -/
theorem single_unitary_witness_clock_obstruction {r b : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 2) (hb : b ∈ Ioo (physicalArc r) 1) :
    let y := (physicalArc r + b) / 2
    let η := (zeroGateArcTolerance y - r) / 2
    0 < η ∧ ∀ᶠ N : ℕ in atTop,
      let D : ℕ := 2 ^ N
      ∀ (d : ℕ) (e : Config N ≃ Fin (d + 1)) (H : selfAdjoint (Register N)),
        MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i)) →
        ∀ W : UGroup N,
          (atTop.limsup (fun T : ℝ => (windowProbabilityMeasure T : Measure ℝ)
            {t : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ ‖unitaryEvolution H.val t - z • W.val‖ ≤ r}) ≤
            ENNReal.ofReal (b ^ D)) ∧
          ∀ G : ℝ, 0 ≤ G →
            (∀ u : ℝ, ∃ t ∈ Icc u (u + G),
              ∃ z : ℂ, ‖z‖ = 1 ∧ ‖unitaryEvolution H.val t - z • W.val‖ ≤ r) →
            min 1 (η / (‖H.val‖ + 1)) ≤ b ^ D * (G + 1) := by
  intro y η
  obtain ⟨hx_arc, htol⟩ := physicalArc_full hr
  have hy_mem : y ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp only [y]; linarith only [hx_arc.1, hb.1],
    by dsimp only [y]; linarith only [hx_arc.2, hb.2]⟩
  have hxy : physicalArc r < y := by dsimp only [y]; linarith only [hb.1]
  have hyb : y < b := by dsimp only [y]; linarith only [hb.1]
  have hη_pos : 0 < η := half_pos (sub_pos.mpr (htol ▸ strictMonoOn_zeroGateArcTolerance_full
    ⟨hx_arc.1.le, hx_arc.2.le⟩ ⟨hy_mem.1.le, hy_mem.2.le⟩ hxy))
  refine ⟨hη_pos, ?_⟩
  let z_mid := (y + b) / 2
  have hyz : y < z_mid := by dsimp only [z_mid]; linarith only [hyb]
  have hzb : z_mid < b := by dsimp only [z_mid]; linarith only [hyb]
  have hb_pos : 0 < b := hx_arc.1.trans hb.1
  have hratio_lt : z_mid / b < 1 := (div_lt_one hb_pos).mpr hzb
  have hratio_nn : 0 ≤ z_mid / b := div_nonneg (by dsimp only [z_mid]; linarith only [hy_mem.1, hb_pos]) hb_pos.le
  have hpow_lim : Tendsto (fun D : ℕ => (D : ℝ) * (z_mid / b) ^ D) atTop (𝓝 0) := by
    rcases eq_or_lt_of_le hratio_nn with h0 | hpos
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with D hD
      rw [← h0, zero_pow (by omega), mul_zero]
    · have h1 : 1 < (z_mid / b)⁻¹ := (one_lt_inv₀ hpos).mpr hratio_lt
      simpa only [pow_one, div_eq_mul_inv, inv_pow, inv_inv] using
        tendsto_pow_const_div_const_pow_of_one_lt 1 h1
  have hD_atTop : Tendsto (fun N : ℕ => (2 : ℕ) ^ N) atTop atTop :=
    tendsto_atTop_mono (fun N => (Nat.lt_two_pow_self (n := N)).le) tendsto_id
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (1 / (z_mid - y))
  filter_upwards [hD_atTop.eventually (eventually_ge_atTop (M₀ + 1)),
    hD_atTop.eventually (hpow_lim.eventually_lt_const zero_lt_one)] with N hDM hDpow
  intro D d e H hmax W
  have h1D_lt : 1 / (D : ℝ) < z_mid - y := by
    have hgt : 1 / (z_mid - y) < (D : ℝ) := hM₀.trans_le (by exact_mod_cast (by dsimp only [D]; omega : M₀ ≤ D))
    exact (div_lt_iff₀ (by positivity : 0 < (D : ℝ))).mpr
      ((div_lt_iff₀ (sub_pos.mpr hyz)).mp hgt |> fun h => by linarith only [h])
  have hy_add_le : y + 1 / (D : ℝ) ≤ z_mid := by linarith only [h1D_lt]
  have hz_lt1 : z_mid < 1 := hzb.trans hb.2
  have hDz_lt_b : (D : ℝ) * z_mid ^ D ≤ b ^ D := by
    have hdiv : (D : ℝ) * (z_mid / b) ^ D ≤ 1 := hDpow.le
    rw [div_pow, mul_div_assoc', div_le_one (pow_pos hb_pos D)] at hdiv
    exact hdiv
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let f := RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i))
  have hind : RationallyIndependentFrequency f :=
    RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent _ hmax
  -- Helper: upper density bound for any radius s_rad ∈ Ioo 0 2 with physicalArc s_rad ≤ y
  have density_le (s_rad : ℝ) (hs_mem : s_rad ∈ Ioo (0 : ℝ) 2) (hs_arc : physicalArc s_rad ≤ y) :
      atTop.limsup (fun T : ℝ => (windowProbabilityMeasure T : Measure ℝ)
        {t : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ ‖unitaryEvolution H.val t - z • W.val‖ ≤ s_rad}) ≤
        ENNReal.ofReal (b ^ D) := by
    let A := {x : Fin d → UnitAddCircle |
      ∃ c : ℂ, ‖c‖ = 1 ∧ ‖projectiveSpectralMatrix e V x - c • W.val‖ ≤ s_rad}
    have hA_closed : IsClosed A := isClosed_singleTargetCapture e V W s_rad
    have hset : {t : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ ‖unitaryEvolution H.val t - z • W.val‖ ≤ s_rad} =
        finiteClockPhasePoint f ⁻¹' A := by
      ext t
      simp only [mem_setOf_eq, mem_preimage]
      rw [unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix e H.2.isHermitian t]
      let a : ℂ := Complex.exp (-(Complex.I * (t * H.2.isHermitian.eigenvalues (e.symm 0))))
      have ha : ‖a‖ = 1 := by simp [a, Complex.norm_exp]
      have ha0 : a ≠ 0 := fun h0 => by simp [h0] at ha
      change (∃ z : ℂ, ‖z‖ = 1 ∧ ‖a • projectiveSpectralMatrix e V (finiteClockPhasePoint f t) - z • W.val‖ ≤ s_rad) ↔
        ∃ c : ℂ, ‖c‖ = 1 ∧ ‖projectiveSpectralMatrix e V (finiteClockPhasePoint f t) - c • W.val‖ ≤ s_rad
      constructor
      · rintro ⟨z, hz, hle⟩
        refine ⟨a⁻¹ * z, by rw [norm_mul, norm_inv, ha, inv_one, one_mul, hz], ?_⟩
        have h1 : a⁻¹ • (a • projectiveSpectralMatrix e V (finiteClockPhasePoint f t) - z • W.val) =
            projectiveSpectralMatrix e V (finiteClockPhasePoint f t) - (a⁻¹ * z) • W.val := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ ha0, one_smul, smul_smul]
        rw [← h1, norm_smul, norm_inv, ha, inv_one, one_mul]
        exact hle
      · rintro ⟨c, hc, hle⟩
        refine ⟨a * c, by rw [norm_mul, ha, hc, one_mul], ?_⟩
        have h1 : a • (projectiveSpectralMatrix e V (finiteClockPhasePoint f t) - c • W.val) =
            a • projectiveSpectralMatrix e V (finiteClockPhasePoint f t) - (a * c) • W.val := by
          rw [smul_sub, smul_smul]
        rw [← h1, norm_smul, ha, one_mul]
        exact hle
    have hport := oneSided_closedTarget_limsup_le_volume f hind hA_closed
    have hmap_eq : (fun T : ℝ => (windowProbabilityMeasure T : Measure ℝ) (finiteClockPhasePoint f ⁻¹' A)) =
        (fun T : ℝ => (clockPhaseWindowLaw f T : Measure (UnitAddTorus (Fin d))) A) := by
      funext T
      rw [clockPhaseWindowLaw, ProbabilityMeasure.toMeasure_map,
        Measure.map_apply (finiteClockPhasePoint_continuous f).measurable hA_closed.measurableSet]
    rw [hset, hmap_eq]
    refine hport.trans ?_
    have harc_s := (physicalArc_full hs_mem).1
    have hs_add_lt : physicalArc s_rad + 1 / (D : ℝ) < 1 :=
      (add_le_add hs_arc le_rfl).trans_lt (hy_add_le.trans_lt hz_lt1)
    have hvol := volume_singleTargetCapture_le e V W hs_mem hs_add_lt
    have hvol_b : volume.real A ≤ b ^ D :=
      (hvol.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg harc_s.1.le (by positivity))
          ((add_le_add hs_arc le_rfl).trans hy_add_le) D)
        (by positivity))).trans hDz_lt_b
    rw [← ENNReal.ofReal_toReal (measure_ne_top volume A)]
    exact ENNReal.ofReal_le_ofReal hvol_b
  refine ⟨density_le r hr hxy.le, fun G hG hsyn => ?_⟩
  -- Enlarged target at radius r' = zeroGateArcTolerance y
  let r' := zeroGateArcTolerance y
  have hr'_mem : r' ∈ Ioo (0 : ℝ) 2 := ⟨by
      rw [← show zeroGateArcTolerance 0 = 0 by simp [zeroGateArcTolerance]]
      exact strictMonoOn_zeroGateArcTolerance_full ⟨le_rfl, zero_le_one⟩ ⟨hy_mem.1.le, hy_mem.2.le⟩ hy_mem.1,
    by
      have h1 : zeroGateArcTolerance 1 = 2 := by
        unfold zeroGateArcTolerance; rw [mul_one, sin_pi_div_two, mul_one]
      rw [← h1]
      exact strictMonoOn_zeroGateArcTolerance_full ⟨hy_mem.1.le, hy_mem.2.le⟩ ⟨zero_le_one, le_rfl⟩ hy_mem.2⟩
  have hr'_arc : physicalArc r' = y :=
    strictMonoOn_zeroGateArcTolerance_full.injOn
      ⟨(physicalArc_full hr'_mem).1.1.le, (physicalArc_full hr'_mem).1.2.le⟩
      ⟨hy_mem.1.le, hy_mem.2.le⟩ (physicalArc_full hr'_mem).2
  let S' := {t : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ ‖unitaryEvolution H.val t - z • W.val‖ ≤ r'}
  let δ := min 1 (η / (‖H.val‖ + 1))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hη_pos (by positivity))
  have hδ_le1 : δ ≤ 1 := min_le_left _ _
  have hspeed : δ * ‖H.val‖ ≤ η := calc
    δ * ‖H.val‖ ≤ (η / (‖H.val‖ + 1)) * (‖H.val‖ + 1) :=
      mul_le_mul (min_le_right _ _) (le_add_of_nonneg_right zero_le_one) (norm_nonneg _) (by positivity)
    _ = η := div_mul_cancel₀ η (by positivity)
  have hG1_pos : 0 < G + 1 := by linarith only [hG]
  -- In each block m ∈ ℕ, pick t_m ∈ [m*(G+1) + 1, (m+1)*(G+1)] hitting the r-ball
  choose tm htm_mem z_m hzm_norm hzm_close using fun m : ℕ => hsyn ((m : ℝ) * (G + 1) + 1)
  have hblock_sub (m : ℕ) : Ioc (tm m - δ) (tm m) ⊆ S' ∩ Ioc ((m : ℝ) * (G + 1)) (((m + 1 : ℕ) : ℝ) * (G + 1)) := by
    intro s ⟨hs_lo, hs_hi⟩
    refine ⟨⟨z_m m, hzm_norm m, ?_⟩, ?_, ?_⟩
    · have hstep := norm_unitaryEvolution_time_sub_le H.2 s (tm m)
      have habs : |s - tm m| ≤ δ := by
        rw [abs_of_nonpos (sub_nonpos.mpr hs_hi)]; linarith only [hs_lo]
      have hst : ‖unitaryEvolution H.val s - unitaryEvolution H.val (tm m)‖ ≤ η :=
        hstep.trans ((mul_le_mul_of_nonneg_left habs (norm_nonneg _)).trans
          (by rw [mul_comm]; exact hspeed))
      refine (norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution H.val (tm m)) _).trans ?_
      have hrr' : r + η ≤ r' := by dsimp only [η, r'] at hη_pos ⊢; linarith only [hη_pos]
      linarith only [hst, hzm_close m, hrr']
    · linarith only [hs_lo, (htm_mem m).1, hδ_le1]
    · push_cast
      linarith only [hs_hi, (htm_mem m).2]
  have hcount_vol (M : ℕ) (hM : 1 ≤ M) :
      ENNReal.ofReal (δ / (G + 1)) ≤
        (windowProbabilityMeasure ((M : ℝ) * (G + 1)) : Measure ℝ) S' := by
    have hT_pos : 0 < (M : ℝ) * (G + 1) := mul_pos (by exact_mod_cast hM) hG1_pos
    have hdisj : Pairwise fun m₁ m₂ : ℕ => Disjoint (Ioc (tm m₁ - δ) (tm m₁)) (Ioc (tm m₂ - δ) (tm m₂)) := by
      intro m₁ m₂ hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine disjoint_left.mpr fun x hx₁ hx₂ => ?_
        have h1 := (hblock_sub m₁ hx₁).2.2
        have h2 := (hblock_sub m₂ hx₂).2.1
        have hm_le : ((m₁ + 1 : ℕ) : ℝ) * (G + 1) ≤ (m₂ : ℝ) * (G + 1) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) hG1_pos.le
        linarith only [h1, h2, hm_le]
      · refine disjoint_left.mpr fun x hx₁ hx₂ => ?_
        have h1 := (hblock_sub m₂ hx₂).2.2
        have h2 := (hblock_sub m₁ hx₁).2.1
        have hm_le : ((m₂ + 1 : ℕ) : ℝ) * (G + 1) ≤ (m₁ : ℝ) * (G + 1) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hgt) hG1_pos.le
        linarith only [h1, h2, hm_le]
    let U := ⋃ m ∈ Finset.range M, Ioc (tm m - δ) (tm m)
    have hU_sub : U ⊆ S' ∩ Ioc 0 ((M : ℝ) * (G + 1)) := by
      rintro x hx
      obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.mp hx
      have hm_lt : m < M := Finset.mem_range.mp hm
      obtain ⟨hxS, hx_lo, hx_hi⟩ := hblock_sub m hxm
      refine ⟨hxS, (mul_nonneg (Nat.cast_nonneg m) hG1_pos.le).trans_lt hx_lo, hx_hi.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm_lt) hG1_pos.le
    have hU_vol : volume U = (M : ℝ≥0∞) * ENNReal.ofReal δ := by
      rw [measure_biUnion_finset (fun m₁ _ m₂ _ hne => hdisj hne) (fun _ _ => measurableSet_Ioc)]
      simp only [Real.volume_Ioc, sub_sub_cancel, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hwin_eq : (windowProbabilityMeasure ((M : ℝ) * (G + 1)) : Measure ℝ) S' =
        (ENNReal.ofReal ((M : ℝ) * (G + 1)))⁻¹ * volume (S' ∩ Ioc 0 ((M : ℝ) * (G + 1))) := by
      have hS'_meas : MeasurableSet S' := by
        let K : Set (Register N) := (fun z : ℂ => z • W.val) '' Metric.sphere (0 : ℂ) 1
        have hK_c : IsCompact K :=
          (isCompact_sphere (0 : ℂ) 1).image (continuous_id.smul continuous_const)
        have hK_ne : K.Nonempty := ⟨(1 : ℂ) • W.val, ⟨1, mem_sphere_zero_iff_norm.mpr norm_one, rfl⟩⟩
        have heq : S' = {t | Metric.infDist (unitaryEvolution H.val t) K ≤ r'} := by
          ext t; constructor
          · rintro ⟨z, hz, hle⟩
            have hmem : z • W.val ∈ K := ⟨z, mem_sphere_zero_iff_norm.mpr hz, rfl⟩
            exact (Metric.infDist_le_dist_of_mem hmem).trans (by rwa [dist_eq_norm])
          · intro hinf
            obtain ⟨Y, ⟨c, hc, rfl⟩, hmin⟩ := exists_compactTarget_minDist hK_c hK_ne (unitaryEvolution H.val t)
            exact ⟨c, mem_sphere_zero_iff_norm.mp hc, by rw [← dist_eq_norm, hmin]; exact hinf⟩
        rw [heq]
        have hL : LipschitzWith ⟨‖H.val‖, norm_nonneg _⟩ (unitaryEvolution H.val) :=
          LipschitzWith.of_dist_le_mul fun x y => by
            rw [dist_eq_norm, Real.dist_eq]; exact norm_unitaryEvolution_time_sub_le H.2 x y
        exact (isClosed_le ((Metric.continuous_infDist_pt K).comp hL.continuous) continuous_const).measurableSet
      change (((ENNReal.ofReal (windowLength ((M : ℝ) * (G + 1))))⁻¹ •
        volume.restrict (Ioc 0 (windowLength ((M : ℝ) * (G + 1))))) : Measure ℝ) S' = _
      rw [windowLength_eq hT_pos, Measure.smul_apply, Measure.restrict_apply hS'_meas, smul_eq_mul]
    rw [hwin_eq]
    have hmono := mul_le_mul_of_nonneg_left (measure_mono (μ := volume) hU_sub)
      (zero_le : 0 ≤ (ENNReal.ofReal ((M : ℝ) * (G + 1)))⁻¹)
    have hM_ne : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega : 0 < M)).ne'
    have hG1_ne : G + 1 ≠ 0 := hG1_pos.ne'
    have hreal_eq : δ / (G + 1) = ((M : ℝ) * (G + 1))⁻¹ * ((M : ℝ) * δ) := by field_simp
    have heq_vol : ENNReal.ofReal (δ / (G + 1)) =
        (ENNReal.ofReal ((M : ℝ) * (G + 1)))⁻¹ * volume U := by
      rw [hreal_eq, ENNReal.ofReal_mul (inv_nonneg.mpr hT_pos.le),
        ENNReal.ofReal_inv_of_pos hT_pos, hU_vol]
      simp only [ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
    rw [heq_vol]; exact hmono
  -- Compare constant sequence ≤ limsup along M * (G + 1) → ∞
  have htend_M : Tendsto (fun M : ℕ => (M : ℝ) * (G + 1)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hG1_pos
  have hlimsup_sub : ENNReal.ofReal (δ / (G + 1)) ≤
      atTop.limsup (fun T : ℝ => (windowProbabilityMeasure T : Measure ℝ) S') := by
    by_contra! hlt
    have hev_T := eventually_lt_of_limsup_lt hlt
    obtain ⟨M, hM1, hM_lt⟩ := ((eventually_ge_atTop 1).and (htend_M.eventually hev_T)).exists
    exact hM_lt.not_ge (hcount_vol M hM1)
  have hfinal := hlimsup_sub.trans (density_le r' hr'_mem hr'_arc.le)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hb_pos.le D)).mp hfinal
  exact (div_le_iff₀ hG1_pos).mp hreal

private def anchoredLagrangePacket {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (E : I → ℝ) (r : I) (x : UnitAddTorus {j // j ≠ r}) : Matrix I I ℂ :=
  ∑ j, (fourier 1 (relativeUnitPhasePacket r x j) : ℂ) • lagrangeSpectralProjector E j H

private def anchoredPacketCapture {N : ℕ}
    (H : Register N) (E : Config N → ℝ) (r : Config N) (s : ℕ) (η : ℝ) :
    Set (UnitAddTorus {i : Config N // i ≠ r}) :=
  {x | HasProjectiveCircuitApproximation N η s (anchoredLagrangePacket H E r x)}

private theorem anchoredWeight_at_clock {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℝ) (r j : I) (t : ℝ) :
    anchorPhase E r t *
      (fourier 1 (relativeUnitPhasePacket r
        (finiteClockPhasePoint (projectiveFrequency (fun i => -E i) r) t) j) : ℂ) =
      anchorPhase E j t := by
  rcases eq_or_ne j r with rfl | hj
  · simp [relativeUnitPhasePacket]
  · simp only [relativeUnitPhasePacket, dif_pos hj, finiteClockPhasePoint, projectiveFrequency,
      fourier_coe_apply, anchorPhase, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
    ring

private theorem anchoredLagrangePacket_mulVec_eigen {I : Type*} [Fintype I] [DecidableEq I]
    {H : Matrix I I ℂ} {E : I → ℝ} {v : I → I → ℂ}
    (he : IsOrthoEigenBasis H v E) (hi : Function.Injective E) (r : I)
    (x : UnitAddTorus {j // j ≠ r}) (j : I) :
    anchoredLagrangePacket H E r x *ᵥ v j =
      (fourier 1 (relativeUnitPhasePacket r x j) : ℂ) • v j := by
  rw [anchoredLagrangePacket, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, lagrangeSpectralProjector_mulVec_eigen he hi]
  rw [Finset.sum_eq_single j (fun l _ hn => by simp [Ne.symm hn]) (by simp)]
  simp only [ite_true]

private theorem evolution_eq_anchoredLagrangePacket {I : Type*} [Fintype I] [DecidableEq I]
    {H : Matrix I I ℂ} {E : I → ℝ} {v : I → I → ℂ}
    (he : IsOrthoEigenBasis H v E) (hi : Function.Injective E) (r : I) (t : ℝ) :
    unitaryEvolution H t = anchorPhase E r t • anchoredLagrangePacket H E r
      (finiteClockPhasePoint (projectiveFrequency (fun i => -E i) r) t) := by
  set x := finiteClockPhasePoint (projectiveFrequency (fun i => -E i) r) t
  have hline (j : I) :
      unitaryEvolution H t *ᵥ v j =
        (anchorPhase E r t • anchoredLagrangePacket H E r x) *ᵥ v j := by
    rw [QuantumAlg.unitaryEvolution_mulVec_of_eigenvector (he.eigen j), Matrix.smul_mulVec,
      anchoredLagrangePacket_mulVec_eigen he hi, smul_smul, anchoredWeight_at_clock]
    rfl
  apply Matrix.ext_iff_mulVec.mpr
  intro u
  conv_lhs => rw [← he.complete u]
  conv_rhs => rw [← he.complete u]
  rw [Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hline j]

private theorem continuous_anchoredLagrangePacket {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (E : I → ℝ) (r : I) :
    Continuous (anchoredLagrangePacket H E r) := by
  refine continuous_finsetSum _ fun j _ => ?_
  have hphase : Continuous (fun x : UnitAddTorus {k // k ≠ r} =>
      (fourier 1 (relativeUnitPhasePacket r x j) : ℂ)) := by
    refine (fourier 1).continuous.comp ?_
    by_cases hj : j ≠ r
    · simpa only [relativeUnitPhasePacket, dif_pos hj] using
        (continuous_apply (⟨j, hj⟩ : {k : I // k ≠ r}))
    · simp only [relativeUnitPhasePacket, dif_neg hj]
      exact continuous_const
  exact hphase.smul continuous_const

private theorem isClosed_anchoredPacketCapture {N : ℕ}
    (H : Register N) (E : Config N → ℝ) (r : Config N) (s : ℕ) (η : ℝ) :
    IsClosed (anchoredPacketCapture H E r s η) := by
  have hset : anchoredPacketCapture H E r s η =
      {x | Metric.infDist (anchoredLagrangePacket H E r x) (phaseCircuitMatrixImageAtMost N s) ≤ η} :=
    Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist _ _ _
  rw [hset]
  exact isClosed_le
    ((Metric.continuous_infDist_pt _).comp (continuous_anchoredLagrangePacket H E r))
    continuous_const

private theorem anchoredLagrangePacket_freezing {I : Type*} [Fintype I] [DecidableEq I]
    {K : ℝ → Matrix I I ℂ} {E : ℝ → I → ℝ} (hK : Continuous K) (hE : Continuous E)
    {b : ℝ} (hb : Function.Injective (E b)) (r : I) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z in 𝓝 b, ∀ x,
      ‖anchoredLagrangePacket (K z) (E z) r x - anchoredLagrangePacket (K b) (E b) r x‖ < δ := by
  let P (z : ℝ) (j : I) := lagrangeSpectralProjector (E z) j (K z)
  have hc : Tendsto (fun z => ∑ j ∈ Finset.univ, ‖P z j - P b j‖) (𝓝 b)
      (𝓝 (∑ j ∈ Finset.univ, ‖P b j - P b j‖)) :=
    tendsto_finsetSum Finset.univ fun j _ =>
      ((continuousAt_lagrangeSpectralProjector hE hK j hb).sub continuousAt_const).norm.tendsto
  have hzero : (∑ j ∈ Finset.univ, ‖P b j - P b j‖) = 0 := by simp
  filter_upwards [hc.eventually_lt_const (hzero.trans_lt hδ)] with z hz x
  have hsum_le :
      ‖anchoredLagrangePacket (K z) (E z) r x - anchoredLagrangePacket (K b) (E b) r x‖ ≤
        ∑ j, ‖P z j - P b j‖ := by
    rw [anchoredLagrangePacket, anchoredLagrangePacket, ← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
    refine (norm_sum_le _ _).trans_eq ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
  exact hsum_le.trans_lt hz

private theorem boundary_fixed_date_circuit_capture :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ b ∉ B,
      let E := SpectralJets.BoundaryField.orderedBoundaryEnergy ω k
      let K := SpectralJets.BoundaryField.boundaryHamiltonian ω k
      ∀ (r : Config (k + 3)) (s : ℕ) (ε η : ℝ), ε < η → ∀ w T : ℕ → ℝ,
        Tendsto w atTop (𝓝 0) → (∀ᶠ n in atTop, 0 < w n) →
        Tendsto (fun n => T n * w n) atTop atTop →
        atTop.limsup (fun n => (unitIntervalProbabilityMeasure : Measure ℝ)
          {u | HasProjectiveCircuitApproximation (k + 3) ε s
            (unitaryEvolution (K (b + w n * u)) (T n))}) ≤
          volume (anchoredPacketCapture (K b) (E b) r s η) := by
  filter_upwards [SpectralJets.BoundaryField.FieldWindows.gaussian_boundary_fixed_date_haar,
    SpectralJets.BoundaryField.gaussian_boundary_projective_slopes] with ω hh hs k
  obtain ⟨B₁, hB₁, h⟩ := hh k
  obtain ⟨B₂, hB₂, hc⟩ := hs k
  refine ⟨B₁ ∪ B₂, hB₁.union hB₂, ?_⟩
  intro b hb E K r s ε η hε w T hw hp ht
  obtain ⟨hf, hμ⟩ := h b (fun h0 => hb (Or.inl h0)) r
  have hmax := (hc b (fun h0 => hb (Or.inr h0))).1
  have hE (j : Config (k + 3)) : Continuous fun z => E z j :=
    SpectralJets.BoundaryField.continuous_orderedBoundaryEnergy ω k j
  have hK : Continuous K := continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hnear_inj : ∀ᶠ z in 𝓝 b, Function.Injective (E z) := by
    have hp_ij (i j : Config (k + 3)) : ∀ᶠ z in 𝓝 b, E z i = E z j → i = j := by
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ _ => hij
      · have hne := ((hE i).sub (hE j)).continuousAt.tendsto.eventually
          (isOpen_compl_singleton.mem_nhds
            (show E b i - E b j ∈ ({0} : Set ℝ)ᶜ from sub_ne_zero.mpr (hmax.injective.ne hij)))
        exact hne.mono fun z hz hEq => (hz (sub_eq_zero.mpr hEq)).elim
    exact (eventually_all.mpr fun i => eventually_all.mpr (hp_ij i)).mono fun _ hall _ _ => hall _ _
  have hnear := (anchoredLagrangePacket_freezing hK (continuous_pi hE) hmax.injective r
    (sub_pos.mpr hε)).and hnear_inj
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let f (z : ℝ) := projectiveFrequency (fun i => -E z i) r
  let X := anchoredPacketCapture (K b) (E b) r s η
  have hclosed : IsClosed X := isClosed_anchoredPacketCapture ..
  have hu := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (hμ w T hw hp ht) hclosed
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hu
  have hle_ev : (fun n => (unitIntervalProbabilityMeasure : Measure ℝ)
      {u | HasProjectiveCircuitApproximation (k + 3) ε s
        (unitaryEvolution (K (b + w n * u)) (T n))}) ≤ᶠ[atTop]
      (fun n => (SpectralJets.BoundaryField.FieldWindows.fieldWindowLaw f hf b (w n) (T n) : Measure _) X) := by
    filter_upwards [hp, hw.eventually_lt_const hρ] with n hn hn'
    have hfield_meas :
        (SpectralJets.BoundaryField.FieldWindows.fieldWindowLaw f hf b (w n) (T n) : Measure _) X =
          (unitIntervalProbabilityMeasure : Measure ℝ)
            {u | finiteClockPhasePoint (f (b + w n * u)) (T n) ∈ X} := by
      have h1 := congrArg ENNReal.ofReal
        (SpectralJets.BoundaryField.FieldWindows.fieldWindowLaw_real f hf b (w n) (T n) hclosed.measurableSet)
      simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h1
    rw [hfield_meas]
    apply measure_mono_ae
    have hsup : ∀ᵐ u ∂(unitIntervalProbabilityMeasure : Measure ℝ), u ∈ Ioc (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hsup] with u hu hfit
    let z := b + w n * u
    let x := finiteClockPhasePoint (f z) (T n)
    have hz : z ∈ Metric.ball b ρ := by
      rw [Metric.mem_ball, Real.dist_eq, show z - b = w n * u by dsimp [z]; ring,
        abs_of_nonneg (mul_nonneg hn.le hu.1.le)]
      exact (mul_le_of_le_one_right hn.le hu.2).trans_lt hn'
    obtain ⟨hfreeze, hi⟩ := hball hz
    let e_fin := Fintype.equivFin (Config (k + 3))
    let p := (e_fin.trans (Tuple.sort
      ((SpectralJets.BoundaryField.boundaryHermitian ω k z).eigenvalues ∘ e_fin.symm))).trans e_fin.symm
    have he := (isOrthoEigenBasis_hermitian (K z)
      (SpectralJets.BoundaryField.boundaryHermitian ω k z)).reindex p
    have hmat : unitaryEvolution (K z) (T n) =
        anchorPhase (E z) r (T n) • anchoredLagrangePacket (K z) (E z) r x :=
      evolution_eq_anchoredLagrangePacket he hi r (T n)
    let a := anchorPhase (E z) r (T n)
    have ha : ‖a‖ = 1 := by simp [a, anchorPhase, Complex.norm_exp]
    have ha0 : a ≠ 0 := fun hn0 => by simp [hn0] at ha
    change HasProjectiveCircuitApproximation (k + 3) ε s (unitaryEvolution (K z) (T n)) at hfit
    rw [hmat] at hfit
    obtain ⟨c, hc_norm, C, hC, herr⟩ := hfit
    refine ⟨a⁻¹ * c, by rw [norm_mul, norm_inv, ha, inv_one, one_mul, hc_norm], C, hC, ?_⟩
    have hraw : ‖anchoredLagrangePacket (K z) (E z) r x - (a⁻¹ * c) • (C.eval : Register (k + 3))‖ ≤ ε := by
      have h1 : a⁻¹ • (a • anchoredLagrangePacket (K z) (E z) r x - c • (C.eval : Register (k + 3))) =
          anchoredLagrangePacket (K z) (E z) r x - (a⁻¹ * c) • (C.eval : Register (k + 3)) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ ha0, one_smul, smul_smul]
      rw [← h1, norm_smul, norm_inv, ha, inv_one, one_mul]
      exact herr
    have hfr := hfreeze x
    rw [norm_sub_rev] at hfr
    exact (norm_sub_le_norm_sub_add_norm_sub _ (anchoredLagrangePacket (K z) (E z) r x) _).trans
      (by linarith only [hraw, hfr])
  exact (Filter.limsup_le_limsup hle_ev).trans hu

private theorem volume_packetCapture_eq_projectiveTarget {N d : ℕ}
    {K : Register N} {E : Config N → ℝ} {v : Config N → Config N → ℂ}
    (he : IsOrthoEigenBasis K v E) (hi : Function.Injective E)
    (r : Config N) (hcard : d + 1 = 2 ^ N) (s : ℕ) (η : ℝ) :
    ∃ (e : Config N ≃ Fin (d + 1)) (V : UGroup N),
      volume (anchoredPacketCapture K E r s η) =
        volume (projectiveContinuousCircuitCaptureTarget e V s η) := by
  classical
  let e₀ : Config N ≃ Fin (d + 1) :=
    (Fintype.equivFin (Config N)).trans
      (finCongr (by simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, hcard]))
  let e : Config N ≃ Fin (d + 1) := (Equiv.swap r (e₀.symm 0)).trans e₀
  have her : e r = 0 := by simp [e]
  have he0 : e.symm 0 = r := e.injective (by simp [her])
  -- Orthonormal eigenbasis columns form a unitary matrix V
  let Vmat : Register N := fun i j => v j i
  have hV_star_mul : star Vmat * Vmat = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    have horth := he.orth j k
    simpa only [Vmat, Matrix.star_apply, Complex.star_def, finiteComplexInner, Matrix.one_apply] using horth
  have hV_unit : Vmat ∈ unitary (Register N) :=
    Unitary.mem_iff.mpr ⟨hV_star_mul, mul_eq_one_comm.mp hV_star_mul⟩
  let V : UGroup N := ⟨Vmat, hV_unit⟩
  -- Equivalence {i : Config N // i ≠ r} ≃ Fin d
  let σ : {i : Config N // i ≠ r} ≃ Fin d :=
    { toFun := fun i => (e i.val).pred (fun h0 => i.2 (e.injective (h0.trans her.symm)))
      invFun := fun k => ⟨e.symm k.succ, fun hr => Fin.succ_ne_zero k (by rw [← he0] at hr; exact e.symm.injective hr)⟩
      left_inv := fun i => Subtype.ext (by simp [Fin.succ_pred])
      right_inv := fun k => by simp [Fin.pred_succ] }
  let ι : UnitAddTorus (Fin d) →+ UnitAddTorus {i : Config N // i ≠ r} :=
    { toFun := fun θ i => θ (σ i)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hι_pres : MeasurePreserving ι volume volume := by
    letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
    letI : (volume : Measure (UnitAddTorus (Fin d))).IsAddHaarMeasure := {}
    letI : (volume : Measure (UnitAddTorus {i : Config N // i ≠ r})).IsAddHaarMeasure := {}
    refine ι.measurePreserving (continuous_pi fun i => continuous_apply (σ i)) ?_ (by simp [measure_univ])
    intro y
    refine ⟨fun k => y (σ.symm k), ?_⟩
    funext i
    change y (σ.symm (σ i)) = y i
    rw [Equiv.symm_apply_apply]
  have hmat_eq (θ : Fin d → UnitAddCircle) :
      anchoredLagrangePacket K E r (ι θ) =
        projectiveSpectralMatrix e V θ := by
    have hline (j : Config N) :
        anchoredLagrangePacket K E r (ι θ) *ᵥ v j =
          projectiveSpectralMatrix e V θ *ᵥ v j := by
      have hp := anchoredLagrangePacket_mulVec_eigen he hi r (ι θ) j
      have hstar_v : star Vmat *ᵥ v j = Pi.single j 1 := by
        ext k
        rw [Matrix.mulVec, dotProduct]
        have horth := he.orth k j
        simpa only [Vmat, Matrix.star_apply, Complex.star_def, finiteComplexInner,
          Pi.single_apply, eq_comm] using horth
      have hps : projectiveSpectralMatrix e V θ *ᵥ v j =
          (fourier 1 (RHTower.zeroAnchoredPhase d θ (e j)) : ℂ) • v j := by
        have hinv_v : (V⁻¹ : UGroup N).val *ᵥ v j = Pi.single j 1 := hstar_v
        unfold projectiveSpectralMatrix
        rw [← Matrix.mulVec_mulVec, hinv_v, ← Matrix.mulVec_mulVec,
          Matrix.diagonal_mulVec_single, mul_one]
        ext i
        simp [V, Vmat, mul_comm]
      rw [hp, hps]
      congr 2
      by_cases hj : j = r
      · subst hj
        rw [her, RHTower.zeroAnchoredPhase, Fin.cases_zero]
        simp [relativeUnitPhasePacket]
      · simp only [relativeUnitPhasePacket, dif_pos hj]
        have hej : e j = (σ ⟨j, hj⟩).succ :=
          (Fin.succ_pred (e j) (fun h0 => hj (e.injective (h0.trans her.symm)))).symm
        rw [hej, RHTower.zeroAnchoredPhase, Fin.cases_succ]
        rfl
    apply Matrix.ext_iff_mulVec.mpr
    intro u
    conv_lhs => rw [← he.complete u]
    conv_rhs => rw [← he.complete u]
    rw [Matrix.mulVec_sum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hline j]
  refine ⟨e, V, ?_⟩
  have hclosed := isClosed_anchoredPacketCapture K E r s η
  rw [← hι_pres.measure_preimage hclosed.measurableSet.nullMeasurableSet]
  congr 1
  ext θ
  change HasProjectiveCircuitApproximation N η s
      (anchoredLagrangePacket K E r (ι θ)) ↔
    θ ∈ projectiveContinuousCircuitCaptureTarget e V s η
  rw [hmat_eq θ, hasProjectiveCircuitApproximation_iff_infDist]
  rfl

/-- Detuning-free single-date boundary-field onset bound: along almost every Gaussian chain and
all sufficiently long prefixes `N = k + 3`, outside a countable set of baseline terminal-`Z`
couplings `b`, for any shrinking field window `w_n → 0⁺` and single prescribed dates `T_n ≥ 0`
with `T_n * w_n → ∞` (zero full-torus detuning), the fraction of terminal couplings `u ∈ [0, 1]`
whose `1/10`-onset `τ_s` (`s ≤ B₇`, including `s = P`) reaches or exceeds `T_n` has upper limit
at most `(4 / 5)^(2^N)`. -/
theorem gaussian_detuning_free_boundary_field_onset_bound :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k + 3
      let D : ℕ := 2 ^ N
      let P := nearHilbertContinuousCircuitBudget N
      let B₇ := D / (7 * (N + 1))
      let H_field (z : ℝ) : selfAdjoint (Register N) :=
        ⟨SpectralJets.BoundaryField.boundaryHamiltonian ω k z,
          (SpectralJets.BoundaryField.boundaryHermitian ω k z).isSelfAdjoint⟩
      P ≤ B₇ ∧
      ∃ B : Set ℝ, B.Countable ∧ ∀ b ∉ B,
        ∀ w T : ℕ → ℝ,
          Tendsto w atTop (𝓝 0) →
          (∀ᶠ n in atTop, 0 < w n) →
          (∀ᶠ n in atTop, 0 ≤ T n) →
          Tendsto (fun n => T n * w n) atTop atTop →
          atTop.limsup (fun n => (unitIntervalProbabilityMeasure : Measure ℝ)
            {u | ∃ s ≤ B₇, T n ≤ tenthPlateauOnset (H_field (b + w n * u)) s}) ≤
            ENNReal.ofReal ((4 / 5 : ℝ) ^ D) := by
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
    dsimp only [η] at hgrid ⊢; linarith only [hgrid]
  filter_upwards [boundary_fixed_date_circuit_capture,
    SpectralJets.BoundaryField.gaussian_boundary_projective_slopes] with ω hcap hslopes
  filter_upwards [(tendsto_add_atTop_nat 3).eventually
      (positive_budget_exponent 7 (by decide) η y (4 / 5) hη hy_mem.1 (by norm_num) hyb),
    eventually_ge_atTop m] with k hpos_exp hkm
  intro N D P B₇ H_field
  have hPB : P ≤ B₇ := (Nat.le_div_iff_mul_le (by positivity)).mpr <|
    (Nat.mul_le_mul_left P (Nat.mul_le_mul_right (N + 1) (by decide : 7 ≤ 64))).trans
      (Nat.div_mul_le_self D (64 * (N + 1)))
  obtain ⟨B₁, hB₁, hc₁⟩ := hcap k
  obtain ⟨B₂, hB₂, hc₂⟩ := hslopes k
  refine ⟨hPB, B₁ ∪ B₂, hB₁.union hB₂, fun b hb w T hw hp hT0 hTw => ?_⟩
  let r_anc : Config N := fun _ => false
  have hlim := hc₁ b (fun h => hb (Or.inl h)) r_anc B₇ (1 / 10) (13 / 125) (by norm_num) w T hw hp hTw
  -- Monotonicity of sets: if ∃ s ≤ B₇, T n ≤ tenthPlateauOnset H' s, then affordable at B₇
  have hmono_ev : (fun n => (unitIntervalProbabilityMeasure : Measure ℝ)
      {u | ∃ s ≤ B₇, T n ≤ tenthPlateauOnset (H_field (b + w n * u)) s}) ≤ᶠ[atTop]
      (fun n => (unitIntervalProbabilityMeasure : Measure ℝ)
        {u | HasProjectiveCircuitApproximation N (1 / 10) B₇
          (unitaryEvolution (SpectralJets.BoundaryField.boundaryHamiltonian ω k (b + w n * u)) (T n))}) := by
    filter_upwards [hT0] with n hn0
    refine measure_mono ?_
    rintro u ⟨s, hsB, hle_τ⟩
    obtain ⟨z, hz, C, hC, herr⟩ := affordable_of_le_tenthPlateauOnset
      (H_field (b + w n * u)) hn0 hle_τ
    exact ⟨z, hz, C, hC.trans hsB, herr⟩
  refine (Filter.limsup_le_limsup hmono_ev).trans (hlim.trans ?_)
  -- Bound volume (packetCapture ...) ≤ (4/5)^D
  let K_b := SpectralJets.BoundaryField.boundaryHamiltonian ω k b
  let E_b := SpectralJets.BoundaryField.orderedBoundaryEnergy ω k b
  have hinj_b : Function.Injective E_b := (hc₂ b (fun h => hb (Or.inr h))).1.injective
  let e_fin := Fintype.equivFin (Config N)
  let perm := (e_fin.trans (Tuple.sort ((SpectralJets.BoundaryField.boundaryHermitian ω k b).eigenvalues ∘ e_fin.symm))).trans e_fin.symm
  have he_ortho := (isOrthoEigenBasis_hermitian K_b
    (SpectralJets.BoundaryField.boundaryHermitian ω k b)).reindex perm
  have hDpos : 0 < D := Nat.two_pow_pos N
  have hcard : (D - 1) + 1 = D := Nat.sub_add_cancel hDpos
  obtain ⟨e_idx, V_b, hvol_eq⟩ := volume_packetCapture_eq_projectiveTarget
    he_ortho hinj_b r_anc hcard B₇ (13 / 125)
  change volume (anchoredPacketCapture K_b E_b r_anc B₇ (13 / 125)) =
    volume (projectiveContinuousCircuitCaptureTarget e_idx V_b B₇ (13 / 125)) at hvol_eq
  rw [hvol_eq, ← ENNReal.ofReal_toReal (measure_ne_top volume _)]
  apply ENNReal.ofReal_le_ofReal
  have hmD : (m : ℝ) ≤ (D : ℝ) :=
    by exact_mod_cast (hkm.trans (by dsimp only [N]; omega : k ≤ N)).trans (Nat.lt_two_pow_self (n := N)).le
  have hyD : y ^ D ≤ y ^ (D - 1) := by
    calc y ^ D = y ^ (D - 1) * y := by rw [← pow_succ, Nat.sub_add_cancel hDpos]
      _ ≤ y ^ (D - 1) * 1 := mul_le_mul_of_nonneg_left hy_mem.2.le (pow_nonneg hy_mem.1.le _)
      _ = _ := mul_one _
  have hmy : (m : ℝ) * y ^ D ≤ zeroGateArcDensity D y :=
    mul_le_mul hmD hyD (pow_nonneg hy_mem.1.le _) (Nat.cast_nonneg _)
  let E_cap : ℝ := ((B₇ : ℝ) + 1) * ((((N : ℝ) + 1) ^ 2) * (1 + 4 * (B₇ : ℝ) / η) ^ 32) ^ B₇
  have hvol := UnitaryBalls.circuit_volume_bound e_idx V_b B₇ m hm' hη ⟨hy_mem.1.le, hy_mem.2⟩ hprice
  have h1 : (m : ℝ) * E_cap * y ^ D = E_cap * ((m : ℝ) * y ^ D) := by ring
  change _ ≤ (m : ℝ) * E_cap * y ^ D at hvol
  exact ((hvol.trans_eq h1).trans
    ((mul_le_mul_of_nonneg_left hmy (by dsimp only [E_cap]; positivity)).trans hpos_exp.le))

/-- Detuning-free common-time ensemble onset transfer: for all sufficiently long prefixes
`N = k + 3`, Tonelli–Fatou transfer of qualitative Kronecker–Weyl occupation (with zero
full-torus detuning) proves that the upper limit across deterministic dates `t → ∞` of the
Gaussian disorder probability that every budget `s ≤ B₇` (including `P`) has already crossed
its `1/10`-onset `τ_s < t` is at least `1 - (4 / 5)^(2^N)`. -/
theorem gaussian_detuning_free_common_time_onset :
    ∀ᶠ k : ℕ in atTop,
      let N := k + 3
      let D : ℕ := 2 ^ N
      let P := nearHilbertContinuousCircuitBudget N
      let B₇ := D / (7 * (N + 1))
      P ≤ B₇ ∧
      ENNReal.ofReal (1 - (4 / 5 : ℝ) ^ D) ≤
        atTop.limsup (fun t : ℝ => pathPauliDisorderLaw
          {ω | ∀ s ≤ B₇,
            tenthPlateauOnset (chainGenerator ω k) s < t ∧
            orbitCircuitDistance (chainGenerator ω k) s
              (tenthPlateauOnset (chainGenerator ω k) s) = 1 / 10}) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  obtain ⟨_, h13_log⟩ := thirteen_125_entropy
  have h10_mem : (1 / 10 : ℝ) ∈ Ioo (0 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  obtain ⟨hx10, htol10⟩ := physicalArc_full h10_mem
  have h10_log : Real.log (physicalArc (1 / 10)) + 32 * Real.log 2 / (7 : ℕ) < Real.log (4 / 5) := by
    have hm : physicalArc (1 / 10) ≤ physicalArc (13 / 125) := by
      unfold physicalArc
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (arcsin_le_arcsin (by norm_num)) two_pos.le) pi_pos.le
    linarith only [Real.log_le_log hx10.1 hm, h13_log]
  have hcon : ContinuousAt (fun z : ℝ => Real.log z + 32 * Real.log 2 / (7 : ℕ))
      (physicalArc (1 / 10)) :=
    (Real.continuousAt_log hx10.1.ne').add continuousAt_const
  obtain ⟨δ, hδ, hsub_log⟩ := Metric.eventually_nhds_iff.mp (hcon.eventually_lt_const h10_log)
  let y := physicalArc (1 / 10) + min (1 - physicalArc (1 / 10)) δ / 2
  have hmin : 0 < min (1 - physicalArc (1 / 10)) δ := lt_min (sub_pos.mpr hx10.2) hδ
  have hxy : physicalArc (1 / 10) < y := by dsimp only [y]; linarith only [hmin]
  have hy1 : y < 1 := by dsimp only [y]; linarith only [min_le_left (1 - physicalArc (1 / 10)) δ, hmin]
  have hy_mem : y ∈ Ioo (0 : ℝ) 1 := ⟨hx10.1.trans hxy, hy1⟩
  have hyb : Real.log y + 32 * Real.log 2 / (7 : ℕ) < Real.log (4 / 5) := hsub_log (by
    rw [Real.dist_eq, show y - physicalArc (1 / 10) = min (1 - physicalArc (1 / 10)) δ / 2 by
      dsimp only [y]; ring, abs_of_pos (half_pos hmin)]
    linarith only [min_le_right (1 - physicalArc (1 / 10)) δ, hmin])
  let η := (zeroGateArcTolerance y - 1 / 10) / 2
  have hη : 0 < η := half_pos (sub_pos.mpr (htol10 ▸ strictMonoOn_zeroGateArcTolerance_full
    ⟨hx10.1.le, hx10.2.le⟩ ⟨hy_mem.1.le, hy_mem.2.le⟩ hxy))
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * Real.pi / η)
  have hm' : 0 < m := Nat.cast_pos.mp ((div_pos Real.two_pi_pos hη).trans hm)
  have hgrid : 2 * Real.pi / m ≤ η := (div_le_iff₀ (Nat.cast_pos.mpr hm')).mpr
    (by simpa only [mul_comm η] using ((div_lt_iff₀ hη).mp hm).le)
  have hprice : (1 / 10 : ℝ) + η + 2 * Real.pi / m ≤ zeroGateArcTolerance y := by
    dsimp only [η] at hgrid ⊢; linarith only [hgrid]
  filter_upwards [(tendsto_add_atTop_nat 3).eventually
      (positive_budget_exponent 7 (by decide) η y (4 / 5) hη hy_mem.1 (by norm_num) hyb),
    eventually_ge_atTop m] with k hpos_exp hkm
  intro N D P B₇
  have hPB : P ≤ B₇ := (Nat.le_div_iff_mul_le (by positivity)).mpr <|
    (Nat.mul_le_mul_left P (Nat.mul_le_mul_right (N + 1) (by decide : 7 ≤ 64))).trans
      (Nat.div_mul_le_self D (64 * (N + 1)))
  refine ⟨hPB, ?_⟩
  let S : Set (PathPauliDisorder × ℝ) :=
    {p | 0 < p.2 ∧ ¬ HasProjectiveCircuitApproximation N (1 / 10) B₇
      (unitaryEvolution (chainGenerator p.1 k).val p.2)}
  have hS_meas : MeasurableSet S := by
    let n := k + 1
    have hcont : Continuous (fun p : (PrescribedTimes.PrefixIndex n → ℝ) × ℝ =>
        PrescribedTimes.pathGateDistance n B₇ p.1 p.2) :=
      PrescribedTimes.continuous_distance n B₇
    have hmap : Measurable (fun p : PathPauliDisorder × ℝ =>
        (PrescribedTimes.ShortWindows.prefixPoint k p.1, p.2)) :=
      ((gaussian_pauli_prefix_coordinates_law n).measurable.comp measurable_fst).prodMk
        measurable_snd
    have heq : S = {p | 0 < p.2} ∩
        ((fun p : PathPauliDisorder × ℝ => (PrescribedTimes.ShortWindows.prefixPoint k p.1, p.2)) ⁻¹'
          {q | 1 / 10 < PrescribedTimes.pathGateDistance n B₇ q.1 q.2}) := by
      ext ⟨ω, t⟩
      simp only [S, mem_setOf_eq, mem_inter_iff, mem_preimage,
        hasProjectiveCircuitApproximation_iff_infDist, not_le]
      refine and_congr_right fun _ => ?_
      have hgen : PrescribedTimes.numberedGenerator n
          (PrescribedTimes.ShortWindows.prefixPoint k ω) = (chainGenerator ω k).val :=
        PrescribedTimes.numberedGenerator_shell (pathPauliDisorderShell ω n)
      simp only [PrescribedTimes.pathGateDistance, hgen]
      rfl
    rw [heq]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      ((isOpen_lt continuous_const hcont).measurableSet.preimage hmap)
  -- Conull quenched occupation at this fixed prefix k
  let Q : Set PathPauliDisorder :=
    {ω | atTop.limsup (fun T : ℝ => quenchedTimeFraction Sᶜ ω T) ≤ ENNReal.ofReal ((4 / 5 : ℝ) ^ D)}
  have hae_Q : ∀ᵐ ω ∂pathPauliDisorderLaw, ω ∈ Q := by
    filter_upwards [PhaseBoundary.gaussian_uniform_affordable_fraction] with ω hlim
    let e_idx := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
    let V := hermitianEigenbasisUnitary (chainGenerator ω k).2.isHermitian
    have hDpos : 0 < D := Nat.two_pow_pos N
    have hmD : (m : ℝ) ≤ (D : ℝ) :=
      by exact_mod_cast (hkm.trans (by dsimp only [N]; omega : k ≤ N)).trans (Nat.lt_two_pow_self (n := N)).le
    have hyD : y ^ D ≤ y ^ (D - 1) := by
      calc y ^ D = y ^ (D - 1) * y := by rw [← pow_succ, Nat.sub_add_cancel hDpos]
        _ ≤ y ^ (D - 1) * 1 := mul_le_mul_of_nonneg_left hy_mem.2.le (pow_nonneg hy_mem.1.le _)
        _ = _ := mul_one _
    have hmy : (m : ℝ) * y ^ D ≤ zeroGateArcDensity D y :=
      mul_le_mul hmD hyD (pow_nonneg hy_mem.1.le _) (Nat.cast_nonneg _)
    let E_cap : ℝ := ((B₇ : ℝ) + 1) * ((((N : ℝ) + 1) ^ 2) * (1 + 4 * (B₇ : ℝ) / η) ^ 32) ^ B₇
    have hvol := UnitaryBalls.circuit_volume_bound e_idx V B₇ m hm' hη ⟨hy_mem.1.le, hy_mem.2⟩ hprice
    have hupper : volume.real (projectiveContinuousCircuitCaptureTarget e_idx V B₇ (1 / 10)) < (4 / 5 : ℝ) ^ D := by
      have h1 : (m : ℝ) * E_cap * y ^ D = E_cap * ((m : ℝ) * y ^ D) := by ring
      change _ ≤ (m : ℝ) * E_cap * y ^ D at hvol
      exact (hvol.trans_eq h1).trans_lt
        ((mul_le_mul_of_nonneg_left hmy (by dsimp only [E_cap]; positivity)).trans_lt hpos_exp)
    have hhi := (hlim k B₇ (1 / 10) (fun _ => 0)).eventually_lt_const hupper
    have hfrac_ev : ∀ᶠ T : ℝ in atTop,
        quenchedTimeFraction Sᶜ ω T ≤ ENNReal.ofReal ((4 / 5 : ℝ) ^ D) := by
      filter_upwards [hhi, eventually_gt_atTop (0 : ℝ)] with T hT_lt hT_pos
      have hsub : Prod.mk ω ⁻¹' Sᶜ ∩ Ioc 0 T ⊆ visitSet (chainGenerator ω k) B₇ (1 / 10) ∩ Icc 0 T := by
        rintro t ⟨htS, htI⟩
        have hfit : HasProjectiveCircuitApproximation N (1 / 10) B₇
            (unitaryEvolution (chainGenerator ω k).val t) := by
          by_contra hnot
          exact htS ⟨htI.1, hnot⟩
        exact ⟨hfit, htI.1.le, htI.2⟩
      have hvol_le : volume (Prod.mk ω ⁻¹' Sᶜ ∩ Ioc 0 T) ≤
          ENNReal.ofReal ((4 / 5 : ℝ) ^ D * T) := by
        have hfin : volume (visitSet (chainGenerator ω k) B₇ (1 / 10) ∩ Icc 0 T) ≠ ⊤ :=
          measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
        refine (measure_mono hsub).trans ?_
        rw [← ENNReal.ofReal_toReal hfin]
        apply ENNReal.ofReal_le_ofReal
        rw [zero_add, visitFraction, sub_zero, div_lt_iff₀ hT_pos] at hT_lt
        exact hT_lt.le
      rw [quenchedTimeFraction]
      refine (ENNReal.div_le_div_right hvol_le (ENNReal.ofReal T)).trans ?_
      rw [ENNReal.ofReal_mul (by positivity),
        ENNReal.mul_div_cancel_right (by simp [hT_pos]) ENNReal.ofReal_ne_top]
    exact (Filter.limsup_le_limsup hfrac_ev).trans_eq (Filter.limsup_const _)
  -- Measurable conull subset G ⊆ Q with probability 1
  let G : Set PathPauliDisorder := (toMeasurable pathPauliDisorderLaw Qᶜ)ᶜ
  have hG_meas : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hG_sub : G ⊆ Q := fun ω hω => by_contra fun hn => hω (subset_toMeasurable _ _ hn)
  have hQc_zero : pathPauliDisorderLaw Qᶜ = 0 := ae_iff.mp hae_Q
  have hG_one : pathPauliDisorderLaw G = 1 := by
    have htm_zero : pathPauliDisorderLaw (toMeasurable pathPauliDisorderLaw Qᶜ) = 0 := by
      rw [measure_toMeasurable, hQc_zero]
    rw [measure_compl (measurableSet_toMeasurable _ _) (measure_ne_top _ _),
      measure_univ, htm_zero, tsub_zero]
  have havg := le_liminf_quenchedWindowAverage (γ := pathPauliDisorderLaw) hS_meas hG_meas
    (c := 1 - ENNReal.ofReal ((4 / 5 : ℝ) ^ D))
    (fun ω hω => le_liminf_quenchedTimeFraction_of_limsup_compl_le hS_meas ω (hG_sub hω))
  rw [hG_one, mul_one] at havg
  have hsup := le_limsup_quenchedFixedTimeProb S havg
  have hsub_ofReal : ENNReal.ofReal (1 - (4 / 5 : ℝ) ^ D) ≤ 1 - ENNReal.ofReal ((4 / 5 : ℝ) ^ D) := by
    rw [ENNReal.ofReal_sub 1 (pow_nonneg (by norm_num) D), ENNReal.ofReal_one]
  have hle_ev : (fun t : ℝ => quenchedFixedTimeProb pathPauliDisorderLaw S t) ≤ᶠ[atTop]
      (fun t : ℝ => pathPauliDisorderLaw
        {ω | ∀ s ≤ B₇,
          tenthPlateauOnset (chainGenerator ω k) s < t ∧
          orbitCircuitDistance (chainGenerator ω k) s
            (tenthPlateauOnset (chainGenerator ω k) s) = 1 / 10}) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht_pos
    refine measure_mono fun ω ⟨_, hnotB₇⟩ s hsB => ?_
    have hnots : ¬ HasProjectiveCircuitApproximation N (1 / 10) s
        (unitaryEvolution (chainGenerator ω k).val t) :=
      fun ⟨z, hz, C, hC, herr⟩ => hnotB₇ ⟨z, hz, C, hC.trans hsB, herr⟩
    obtain ⟨_, hlt, _, heq, _⟩ := tenthPlateauOnset_lt_of_not_affordable (chainGenerator ω k) ht_pos.le hnots
    exact ⟨hlt, heq⟩
  exact (hsub_ofReal.trans hsup).trans (Filter.limsup_le_limsup hle_ev)

#print axioms affordable_of_le_tenthPlateauOnset
#print axioms tenthPlateauOnset_lt_of_not_affordable
#print axioms tenthPlateauOnset_lt_of_commutator_witness
#print axioms tenthPlateauOnset_lt_of_unitary_witness
#print axioms norm_entry_le_l2_opNorm
#print axioms circuitCommutatorCap_singleSitePauli_eq_two
#print axioms rankOne_partialSwap_commutator_witness
#print axioms single_unitary_offDiag_floor
#print axioms single_unitary_witness_clock_obstruction
#print axioms gaussian_detuning_free_boundary_field_onset_bound
#print axioms gaussian_detuning_free_common_time_onset

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau

