import GaloisForLFunctions.HTGeometry.PhasePacketOrderReflection
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Data.Rat.Denumerable

/-!
# The phase-kernel admission gauge

Let `μ` be a finite measure and `η` a finite signed measure on `ℝ`.  The admission gauge
`κ_μ(η) = inf {c ≥ 0 : η + cμ ≥ 0} ∈ [0, ∞]` is computed three ways.

* **Packet thresholds** `(FKA.8)`: `κ_μ(η) = sup r_{t,z}(η | μ)` over all phase packets, where
  `r = (-Q_η/Q_μ)_+` when `Q_μ > 0`, `r = ∞` when `Q_μ = 0 > Q_η`, and `r = 0` otherwise.
* **Kernel pencils** `(FKA.9)`: `κ_μ(η) ≤ c` exactly when every Hermitian pencil
  `K_η(t) + c K_μ(t)` is positive semidefinite.
* **Radon–Nikodym** `(FKA.10)`: `κ_μ(η) < ∞` exactly when `η⁻ ≪ μ` with essentially bounded
  density, and then `κ_μ(η) = ess sup dη⁻/dμ`.

Finally `(FKA.13)`: along the canonical enumeration `q_0 = 0, q_1, …` of `ℚ`, the gauges `κ_N` of
the nested finite pencils on `span {e^{-i q_0 x}, …, e^{-i q_N x}}` increase to `κ_μ(η)`.
-/

open MeasureTheory Complex Filter Topology Set Matrix
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PhaseKernel

/-! ## The gauge and the packet thresholds -/

section Gauge

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

/-- `(FKA.3)`  The positive compensation gauge `κ_μ(η) = inf {c ≥ 0 : η + cμ ≥ 0}`. -/
def admissionGauge (η : SignedMeasure ℝ) : ℝ≥0∞ :=
  ⨅ (c : ℝ≥0) (_ : 0 ≤ η + (c : ℝ) • μ.toSignedMeasure), (c : ℝ≥0∞)

/-- `(FKA.4)`  The defect threshold of a phase packet. -/
def packetThreshold (η : SignedMeasure ℝ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) : ℝ≥0∞ :=
  if 0 < packetEnergy μ t z then
    ENNReal.ofReal (-signedPacketEnergy η t z / packetEnergy μ t z)
  else if signedPacketEnergy η t z < 0 then ⊤ else 0

omit [IsFiniteMeasure μ] in
/-- A threshold is at most `c` exactly when the compensated packet energy is nonnegative. -/
theorem packetThreshold_le_iff (η : SignedMeasure ℝ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ)
    (c : ℝ≥0) :
    packetThreshold μ η t z ≤ c ↔ 0 ≤ signedPacketEnergy η t z + c * packetEnergy μ t z := by
  unfold packetThreshold
  split_ifs with hpos hneg
  · rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal,
      div_le_iff₀ hpos]
    constructor <;> intro h <;> linarith
  · have h0 : packetEnergy μ t z = 0 :=
      le_antisymm (not_lt.mp hpos) (packetEnergy_nonneg _ _ _)
    rw [h0, mul_zero, add_zero]
    simp only [top_le_iff, ENNReal.coe_ne_top, false_iff, not_le]
    exact hneg
  · have h0 : packetEnergy μ t z = 0 :=
      le_antisymm (not_lt.mp hpos) (packetEnergy_nonneg _ _ _)
    rw [h0, mul_zero, add_zero]
    simp only [zero_le, true_iff]
    exact not_lt.mp hneg

omit [IsFiniteMeasure μ] in
theorem packetThreshold_congr (η : SignedMeasure ℝ) {m n : ℕ} {t : Fin m → ℝ} {z : Fin m → ℂ}
    {t' : Fin n → ℝ} {z' : Fin n → ℂ} (h : phasePacket t z = phasePacket t' z') :
    packetThreshold μ η t z = packetThreshold μ η t' z' := by
  unfold packetThreshold signedPacketEnergy packetEnergy
  rw [h]

theorem packetEnergy_add_smul (P : Measure ℝ) [IsFiniteMeasure P] (c : ℝ≥0) {m : ℕ}
    (t : Fin m → ℝ) (z : Fin m → ℂ) :
    packetEnergy (P + c • μ) t z = packetEnergy P t z + c * packetEnergy μ t z := by
  unfold packetEnergy
  rw [integral_add_measure (integrable_normSq_phasePacket P t z)
    ((integrable_normSq_phasePacket μ t z).smul_measure_nnreal), integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul]

theorem add_smul_eq_sub (η : SignedMeasure ℝ) (c : ℝ≥0) :
    η + (c : ℝ) • μ.toSignedMeasure =
      (η.toJordanDecomposition.posPart + c • μ).toSignedMeasure -
        η.toJordanDecomposition.negPart.toSignedMeasure := by
  conv_lhs => rw [signedMeasure_eq_sub η]
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_smul, NNReal.smul_def]
  abel

/-- `(FKA.11)`  `η + cμ ≥ 0` exactly when every compensated packet energy is nonnegative. -/
theorem nonneg_add_smul_iff (η : SignedMeasure ℝ) (c : ℝ≥0) :
    0 ≤ η + (c : ℝ) • μ.toSignedMeasure ↔
      ∀ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ),
        0 ≤ signedPacketEnergy η t z + c * packetEnergy μ t z := by
  rw [add_smul_eq_sub, toSignedMeasure_sub_nonneg_iff, le_iff_forall_packetEnergy_le]
  refine forall_congr' fun m => forall_congr' fun t => forall_congr' fun z => ?_
  rw [packetEnergy_add_smul, signedPacketEnergy]
  constructor <;> intro h <;> linarith

/-- `(FKA.11)` with rational phases. -/
theorem nonneg_add_smul_iff_rational (η : SignedMeasure ℝ) (c : ℝ≥0) :
    0 ≤ η + (c : ℝ) • μ.toSignedMeasure ↔
      ∀ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), IsRationalPacket t →
        0 ≤ signedPacketEnergy η t z + c * packetEnergy μ t z := by
  rw [add_smul_eq_sub, toSignedMeasure_sub_nonneg_iff, le_iff_forall_rationalPacketEnergy_le]
  refine forall_congr' fun m => forall_congr' fun t => forall_congr' fun z =>
    imp_congr_right fun _ => ?_
  rw [packetEnergy_add_smul, signedPacketEnergy]
  constructor <;> intro h <;> linarith

/-- The infimum of the finite upper bounds of an extended real is itself. -/
theorem iInf_nnreal_ge (S : ℝ≥0∞) : ⨅ (c : ℝ≥0) (_ : S ≤ (c : ℝ≥0∞)), (c : ℝ≥0∞) = S := by
  refine le_antisymm ?_ (le_iInf₂ fun c hc => hc)
  rcases eq_or_ne S ⊤ with h | h
  · rw [h]
    exact le_top
  · exact (iInf₂_le S.toNNReal (by rw [ENNReal.coe_toNNReal h])).trans
      (by rw [ENNReal.coe_toNNReal h])

/-- `(FKA.8)`  **Phase-kernel admission conservation.**  The gauge is the worst packet
threshold. -/
theorem admissionGauge_eq_iSup_packetThreshold (η : SignedMeasure ℝ) :
    admissionGauge μ η =
      ⨆ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), packetThreshold μ η t z := by
  have hfeas : ∀ c : ℝ≥0, 0 ≤ η + (c : ℝ) • μ.toSignedMeasure ↔
      (⨆ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), packetThreshold μ η t z) ≤ c := by
    intro c
    rw [nonneg_add_smul_iff]
    simp only [iSup_le_iff, packetThreshold_le_iff]
  unfold admissionGauge
  simp_rw [hfeas]
  exact iInf_nnreal_ge _

theorem packetThreshold_le_admissionGauge (η : SignedMeasure ℝ) {m : ℕ} (t : Fin m → ℝ)
    (z : Fin m → ℂ) : packetThreshold μ η t z ≤ admissionGauge μ η := by
  rw [admissionGauge_eq_iSup_packetThreshold]
  exact le_iSup₂_of_le m t (le_iSup (fun z => packetThreshold μ η t z) z)

theorem admissionGauge_le_iff (η : SignedMeasure ℝ) (c : ℝ≥0) :
    admissionGauge μ η ≤ c ↔ 0 ≤ η + (c : ℝ) • μ.toSignedMeasure := by
  rw [admissionGauge_eq_iSup_packetThreshold, nonneg_add_smul_iff]
  simp only [iSup_le_iff, packetThreshold_le_iff]

end Gauge

/-! ## Hermitian kernel pencils -/

/-- The kernel matrix `(ν̂(t_k - t_j))_{j,k}` of a finite measure. -/
def measureKernelMatrix (ν : Measure ℝ) {m : ℕ} (t : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun j k => fourierTransform ν (t k - t j)

/-- `(FKA.9)`  The Hermitian pencil `K_η(t) + c K_μ(t)`. -/
def kernelPencil (μ : Measure ℝ) (η : SignedMeasure ℝ) (c : ℝ≥0) {m : ℕ} (t : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  kernelMatrix η t + ((c : ℝ) : ℂ) • measureKernelMatrix μ t

theorem conj_fourierTransform (ν : Measure ℝ) (s : ℝ) :
    conj (fourierTransform ν s) = fourierTransform ν (-s) := by
  unfold fourierTransform
  rw [← integral_conj]
  congr 1
  funext x
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem kernelPencil_isHermitian (μ : Measure ℝ) (η : SignedMeasure ℝ) (c : ℝ≥0) {m : ℕ}
    (t : Fin m → ℝ) : (kernelPencil μ η c t).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro j k
  simp only [kernelPencil, measureKernelMatrix, kernelMatrix, signedFourier, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, star_add, star_mul', star_sub, RCLike.star_def,
    conj_fourierTransform, Complex.conj_ofReal, neg_sub]

theorem dotProduct_kernelPencil (μ : Measure ℝ) [IsFiniteMeasure μ] (η : SignedMeasure ℝ)
    (c : ℝ≥0) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) :
    star z ⬝ᵥ (kernelPencil μ η c t *ᵥ z) =
      ((signedPacketEnergy η t z + c * packetEnergy μ t z : ℝ) : ℂ) := by
  have h1 := signedPacketForm_eq η t z
  have h2 := packetForm_eq_packetEnergy μ t z
  unfold signedPacketForm at h1
  unfold packetForm at h2
  push_cast
  rw [← h1, ← h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [dotProduct, Matrix.mulVec, kernelPencil, Matrix.add_apply, Matrix.smul_apply,
    kernelMatrix, measureKernelMatrix, Pi.star_apply, RCLike.star_def, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- A pencil is positive semidefinite exactly when every compensated packet energy is
nonnegative. -/
theorem kernelPencil_posSemidef_iff (μ : Measure ℝ) [IsFiniteMeasure μ] (η : SignedMeasure ℝ)
    (c : ℝ≥0) {m : ℕ} (t : Fin m → ℝ) :
    (kernelPencil μ η c t).PosSemidef ↔
      ∀ z : Fin m → ℂ, 0 ≤ signedPacketEnergy η t z + c * packetEnergy μ t z := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  simp only [kernelPencil_isHermitian, true_and, dotProduct_kernelPencil, Complex.zero_le_real]

/-- `(FKA.9)`  `κ_μ(η) ≤ c` exactly when every finite Hermitian pencil `K_η + c K_μ` is positive
semidefinite. -/
theorem admissionGauge_le_iff_kernelPencil (μ : Measure ℝ) [IsFiniteMeasure μ]
    (η : SignedMeasure ℝ) (c : ℝ≥0) :
    admissionGauge μ η ≤ c ↔ ∀ (m : ℕ) (t : Fin m → ℝ), (kernelPencil μ η c t).PosSemidef := by
  rw [admissionGauge_le_iff, nonneg_add_smul_iff]
  simp only [kernelPencil_posSemidef_iff]

/-- `(FKA.9)`  The gauge is the least `c ≥ 0` making every pencil positive semidefinite. -/
theorem admissionGauge_eq_iInf_kernelPencil (μ : Measure ℝ) [IsFiniteMeasure μ]
    (η : SignedMeasure ℝ) :
    admissionGauge μ η =
      ⨅ (c : ℝ≥0) (_ : ∀ (m : ℕ) (t : Fin m → ℝ), (kernelPencil μ η c t).PosSemidef),
        (c : ℝ≥0∞) := by
  have h : ∀ c : ℝ≥0, (∀ (m : ℕ) (t : Fin m → ℝ), (kernelPencil μ η c t).PosSemidef) ↔
      admissionGauge μ η ≤ c := fun c => (admissionGauge_le_iff_kernelPencil μ η c).symm
  simp_rw [h]
  exact (iInf_nnreal_ge _).symm

/-! ## The Radon–Nikodym gauge -/

section RadonNikodym

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

/-- Compensation of a signed measure only has to dominate its negative Jordan part. -/
theorem nonneg_add_smul_iff_negPart_le (η : SignedMeasure ℝ) (c : ℝ≥0) :
    0 ≤ η + (c : ℝ) • μ.toSignedMeasure ↔ η.toJordanDecomposition.negPart ≤ c • μ := by
  rw [add_smul_eq_sub, toSignedMeasure_sub_nonneg_iff]
  constructor
  · intro h
    obtain ⟨S, hS, hPS, hNS⟩ := η.toJordanDecomposition.mutuallySingular
    rw [Measure.le_iff] at h ⊢
    intro A hA
    calc η.toJordanDecomposition.negPart A
        ≤ η.toJordanDecomposition.negPart (A ∩ S) + η.toJordanDecomposition.negPart (A \ S) :=
          measure_le_inter_add_sdiff _ _ _
      _ = η.toJordanDecomposition.negPart (A ∩ S) := by
          rw [measure_mono_null (show A \ S ⊆ Sᶜ from fun x hx => hx.2) hNS, add_zero]
      _ ≤ (η.toJordanDecomposition.posPart + c • μ) (A ∩ S) := h _ (hA.inter hS)
      _ = (c • μ) (A ∩ S) := by
          rw [Measure.add_apply, measure_mono_null inter_subset_right hPS, zero_add]
      _ ≤ (c • μ) A := measure_mono inter_subset_left
  · intro h
    exact h.trans (Measure.le_add_left le_rfl)

/-- Domination `ν ≤ cμ` is absolute continuity with density at most `c`. -/
theorem le_smul_iff_rnDeriv_le (ν : Measure ℝ) [IsFiniteMeasure ν] (c : ℝ≥0) :
    ν ≤ c • μ ↔ ν ≪ μ ∧ ν.rnDeriv μ ≤ᵐ[μ] fun _ => (c : ℝ≥0∞) := by
  constructor
  · intro h
    have hac : ν ≪ μ := fun A hA => by
      have := h A
      rw [Measure.smul_apply, hA, smul_zero] at this
      exact le_antisymm this bot_le
    refine ⟨hac, ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (Measure.measurable_rnDeriv _ _) fun s hs _ => ?_⟩
    rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]
    have := h s
    rwa [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
  · rintro ⟨hac, hle⟩
    rw [Measure.le_iff]
    intro A hA
    rw [← Measure.setLIntegral_rnDeriv hac A, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      ← setLIntegral_const]
    exact lintegral_mono_ae (ae_restrict_of_ae hle)

open scoped Classical in
/-- `(FKA.10)`  **Radon–Nikodym gauge.**  `κ_μ(η) = ess sup dη⁻/dμ` when `η⁻ ≪ μ`, and `∞`
otherwise. -/
theorem admissionGauge_eq_essSup (η : SignedMeasure ℝ) :
    admissionGauge μ η =
      if η.toJordanDecomposition.negPart ≪ μ then
        essSup (η.toJordanDecomposition.negPart.rnDeriv μ) μ
      else ⊤ := by
  unfold admissionGauge
  simp_rw [nonneg_add_smul_iff_negPart_le, le_smul_iff_rnDeriv_le]
  split_ifs with hac
  · simp only [hac, true_and]
    have h : ∀ c : ℝ≥0, (η.toJordanDecomposition.negPart.rnDeriv μ ≤ᵐ[μ]
        fun _ => (c : ℝ≥0∞)) ↔ essSup (η.toJordanDecomposition.negPart.rnDeriv μ) μ ≤ c :=
      fun c => ⟨fun h => essSup_le_of_ae_le _ h,
        fun h => Filter.Eventually.mono ae_le_essSup fun x hx => hx.trans h⟩
    simp_rw [h]
    exact iInf_nnreal_ge _
  · simp [hac]

/-- `(FKA.10)`  The gauge is finite exactly when `η⁻ ≪ μ` with essentially bounded density. -/
theorem admissionGauge_lt_top_iff (η : SignedMeasure ℝ) :
    admissionGauge μ η < ⊤ ↔ η.toJordanDecomposition.negPart ≪ μ ∧
      essSup (η.toJordanDecomposition.negPart.rnDeriv μ) μ < ⊤ := by
  rw [admissionGauge_eq_essSup]
  split_ifs with hac
  · simp [hac]
  · simp [hac]

end RadonNikodym

/-! ## Cofinal rational pencils -/

section Cofinal

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

/-- `(FKA.12)`  The canonical rational phases `q_0 = 0, q_1, q_2, …` enumerating `ℚ`. -/
def ratPhase (n : ℕ) : ℝ := if n = 0 then 0 else ((Denumerable.ofNat ℚ (n - 1) : ℚ) : ℝ)

theorem ratPhase_zero : ratPhase 0 = 0 := rfl

theorem exists_ratPhase_eq (q : ℚ) : ∃ n, ratPhase n = q :=
  ⟨Denumerable.eqv ℚ q + 1, by
    simp only [ratPhase, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    exact_mod_cast (Denumerable.eqv ℚ).symm_apply_apply q⟩

theorem isRationalPacket_ratPhase (N : ℕ) : IsRationalPacket fun j : Fin N => ratPhase j := by
  intro j
  by_cases h : (j : ℕ) = 0
  · exact ⟨0, by simp [ratPhase, h]⟩
  · exact ⟨Denumerable.ofNat ℚ ((j : ℕ) - 1), by simp [ratPhase, h]⟩

/-- `(FKA.12)`  The truncated gauge `κ_N`: the worst threshold among packets in
`span {e^{-i q_0 x}, …, e^{-i q_N x}}`. -/
def truncatedGauge (η : SignedMeasure ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨆ z : Fin (N + 1) → ℂ, packetThreshold μ η (fun j => ratPhase j) z

/-- `κ_N` is the generalized negative eigenvalue of the `N`-th finite rational pencil. -/
theorem truncatedGauge_le_iff (η : SignedMeasure ℝ) (N : ℕ) (c : ℝ≥0) :
    truncatedGauge μ η N ≤ c ↔
      (kernelPencil μ η c fun j : Fin (N + 1) => ratPhase j).PosSemidef := by
  rw [truncatedGauge, kernelPencil_posSemidef_iff]
  simp only [iSup_le_iff, packetThreshold_le_iff]

theorem phasePacket_snoc_zero (N : ℕ) (z : Fin (N + 1) → ℂ) :
    phasePacket (fun j : Fin (N + 2) => ratPhase j) (Fin.snoc z 0) =
      phasePacket (fun j : Fin (N + 1) => ratPhase j) z := by
  funext x
  unfold phasePacket
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero, Fin.val_castSucc]

omit [IsFiniteMeasure μ] in
theorem truncatedGauge_mono (η : SignedMeasure ℝ) : Monotone (truncatedGauge μ η) := by
  refine monotone_nat_of_le_succ fun N => iSup_le fun z => ?_
  rw [packetThreshold_congr μ η (phasePacket_snoc_zero N z).symm]
  exact le_iSup (fun z' : Fin (N + 1 + 1) → ℂ =>
    packetThreshold μ η (fun j => ratPhase j) z') (Fin.snoc z 0)

theorem truncatedGauge_le_admissionGauge (η : SignedMeasure ℝ) (N : ℕ) :
    truncatedGauge μ η N ≤ admissionGauge μ η :=
  iSup_le fun z => packetThreshold_le_admissionGauge μ η _ z

/-- Every rational packet is a packet in some truncated rational span. -/
theorem exists_ratPhase_packet {m : ℕ} {t : Fin m → ℝ} (ht : IsRationalPacket t)
    (z : Fin m → ℂ) :
    ∃ (N : ℕ) (w : Fin (N + 1) → ℂ),
      phasePacket (fun j : Fin (N + 1) => ratPhase j) w = phasePacket t z := by
  choose q hq using ht
  choose n hn using fun j => exists_ratPhase_eq (q j)
  set N := Finset.univ.sup n with hN
  have hlt : ∀ j, n j < N + 1 := fun j => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j))
  classical
  refine ⟨N, fun i => ∑ j, if (⟨n j, hlt j⟩ : Fin (N + 1)) = i then z j else 0, ?_⟩
  funext x
  unfold phasePacket
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  simp only
  rw [hn j, hq j]

theorem iSup_truncatedGauge (η : SignedMeasure ℝ) :
    ⨆ N, truncatedGauge μ η N = admissionGauge μ η := by
  refine le_antisymm (iSup_le (truncatedGauge_le_admissionGauge μ η)) ?_
  set S := ⨆ N, truncatedGauge μ η N
  rcases eq_or_ne S ⊤ with hS | hS
  · rw [hS]
    exact le_top
  · have hc : (S.toNNReal : ℝ≥0∞) = S := ENNReal.coe_toNNReal hS
    rw [← hc, admissionGauge_le_iff, nonneg_add_smul_iff_rational]
    intro m t z ht
    obtain ⟨N, w, hw⟩ := exists_ratPhase_packet ht z
    rw [← packetThreshold_le_iff, hc, packetThreshold_congr μ η hw.symm]
    exact (le_iSup (fun w' : Fin (N + 1) → ℂ => packetThreshold μ η (fun j => ratPhase j) w')
      w).trans (le_iSup (truncatedGauge μ η) N)

/-- `(FKA.13)`  **Cofinal finite-matrix reconstruction.**  `κ_N ↑ κ_μ(η)`. -/
theorem tendsto_truncatedGauge (η : SignedMeasure ℝ) :
    Tendsto (truncatedGauge μ η) atTop (𝓝 (admissionGauge μ η)) := by
  rw [← iSup_truncatedGauge]
  exact tendsto_atTop_iSup (truncatedGauge_mono μ η)

end Cofinal

end GaloisForLFunctions.HTGeometry.PhaseKernel
