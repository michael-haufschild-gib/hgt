import GaloisForLFunctions.HTGeometry.ResetPathSingularity
import GaloisForLFunctions.HTGeometry.ConstitutiveThetaHasseKMSExecutionBalance
import GaloisForLFunctions.HTGeometry.ConstitutiveHasseGlobalRenewal

/-!
# Hasse recovery: exact execution defects and the modular parameter transport

For a scale `t > 0` the Hasse recovery law is geometric, `κ_t(n) = (1 - r) r^n` with
`r = r(t) = (1 - e^{-t})/2 ∈ (0, 1/2)`; the Toeplitz KMS history layers carry the same law
`p_q(n) = (1 - q) q^n` at `q = r(t)`.

* **Theorem 8.2, `(RFDM.35)`–`(RFDM.37)`**: for the geometric law the deterministic-return and
  fresh-reset couplings are separated by `TV = 2q/(1+q)`,
  `D(Δ ‖ p ⊗ p) = -log(1-q) - q/(1-q) log q` and `D(p ⊗ p ‖ Δ) = ∞`.
* **Theorem 7.1, `(RFDM.30)`–`(RFDM.31)`**: the same at `q = r(t)` for the Hasse recovery law
  of every positive-scale observer.
* **Corollary 7.2, `(RFDM.32)`**: both defects are strictly increasing in `t`, so they balance
  under `t ↦ 1/t` exactly at `t = 1`.
* **Theorem 8.1, `(RFDM.34a)`–`(RFDM.34e)`**: the adjacent-depth ratio of `κ_t` is `r(t)`,
  `βE = -log r(t)`, the scale `t(q) = -log(1 - 2q)` is the unique one with recovery law `p_q`,
  and reflection transports to the involution `Θ(q) = r(1/t(q))` of `(0, 1/2)` with unique fixed
  point `q_* = (1 - e^{-1})/2`.
-/

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ResetDilation

/-! ### The geometric layer law -/

section GeometricLayer

variable {q : ℝ}

theorem geometricLayerMass_nonneg (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    0 ≤ geometricLayerMass q n :=
  mul_nonneg (sub_nonneg.2 hq1.le) (pow_nonneg hq0 n)

theorem geometricLayerMass_pos (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    0 < geometricLayerMass q n :=
  mul_pos (sub_pos.2 hq1) (pow_pos hq0 n)

theorem geometricLayerMass_le_one (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    geometricLayerMass q n ≤ 1 := by
  have h1 : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1.le
  have h2 : 1 - q ≤ 1 := by linarith
  calc geometricLayerMass q n = (1 - q) * q ^ n := rfl
    _ ≤ 1 * 1 := mul_le_mul h2 h1 (pow_nonneg hq0 n) zero_le_one
    _ = 1 := one_mul 1

theorem summable_geometricLayerMass (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (geometricLayerMass q) :=
  (summable_geometric_of_lt_one hq0 hq1).mul_left (1 - q)

theorem summable_geometricLayerShannonTerm (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (geometricLayerShannonTerm q) := by
  have hnat : Summable fun n : ℕ => (n : ℝ) * geometricLayerMass q n :=
    (AbelianZetaParameters.summable_natCast_mul_geometric hq0.le hq1).congr fun n => by
      simp only [geometricLayerMass]; ring
  refine (((summable_geometricLayerMass hq0.le hq1).mul_left (-Real.log (1 - q))).add
    (hnat.mul_left (-Real.log q))).congr fun n => ?_
  unfold geometricLayerShannonTerm geometricLayerMass
  rw [Real.log_mul (sub_pos.2 hq1).ne' (pow_ne_zero n hq0.ne'), Real.log_pow]
  ring

/-- **`(RFDM.34)`** the geometric layer law `p_q(n) = (1 - q) q^n` as a probability mass
function. -/
def geometricLayerPMF (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (geometricLayerMass q n), by
    rw [ENNReal.summable.hasSum_iff, ← ENNReal.ofReal_tsum_of_nonneg
      (geometricLayerMass_nonneg hq0 hq1) (summable_geometricLayerMass hq0 hq1),
      tsum_geometricLayerMass_eq_one hq0 hq1, ENNReal.ofReal_one]⟩

theorem geometricLayerPMF_apply (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    geometricLayerPMF q hq0 hq1 n = ENNReal.ofReal (geometricLayerMass q n) := rfl

theorem mass_geometricLayerPMF (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    mass (geometricLayerPMF q hq0 hq1) n = geometricLayerMass q n :=
  ENNReal.toReal_ofReal (geometricLayerMass_nonneg hq0 hq1 n)

/-- **Theorem 8.2, `(RFDM.35)`**: `TV(Δ_{p_q}, p_q ⊗ p_q) = 2q/(1+q)`. -/
theorem geometricLayer_totalVariation (hq0 : 0 ≤ q) (hq1 : q < 1) :
    FormationExcess.totalVariation (diagonalVector (geometricLayerPMF q hq0 hq1))
      (productVector (geometricLayerPMF q hq0 hq1)) = geometricExecutionTV q := by
  rw [totalVariation_diagonal_product, geometricExecutionTV_eq_one_sub_purity hq0 hq1]
  simp only [mass_geometricLayerPMF]

/-- **Theorem 8.2, `(RFDM.36)`**: `D(Δ_{p_q} ‖ p_q ⊗ p_q) = -log(1-q) - q/(1-q) log q`. -/
theorem geometricLayer_klDiv_diagonal_product (hq0 : 0 < q) (hq1 : q < 1) :
    klDiv (diagonalCoupling (geometricLayerPMF q hq0.le hq1))
        (productCoupling (geometricLayerPMF q hq0.le hq1)) =
      ENNReal.ofReal (geometricExecutionEntropy q) := by
  have hterm : ∀ n, Real.negMulLog (mass (geometricLayerPMF q hq0.le hq1) n) =
      geometricLayerShannonTerm q n := fun n => by
    rw [mass_geometricLayerPMF, Real.negMulLog_def, geometricLayerShannonTerm]
  rw [klDiv_diagonal_product, ← tsum_geometricLayerShannonTerm hq0 hq1,
    ENNReal.ofReal_tsum_of_nonneg (fun n => ?_) (summable_geometricLayerShannonTerm hq0 hq1)]
  · exact tsum_congr fun n => by rw [hterm]
  · rw [← hterm]
    exact Real.negMulLog_nonneg (mass_nonneg _ n)
      (by rw [mass_geometricLayerPMF]; exact geometricLayerMass_le_one hq0.le hq1 n)

/-- **Theorem 8.2, `(RFDM.37)`**: `D(p_q ⊗ p_q ‖ Δ_{p_q}) = ∞`. -/
theorem geometricLayer_klDiv_product_diagonal (hq0 : 0 < q) (hq1 : q < 1) :
    klDiv (productCoupling (geometricLayerPMF q hq0.le hq1))
      (diagonalCoupling (geometricLayerPMF q hq0.le hq1)) = ⊤ :=
  klDiv_product_diagonal_eq_top _ (i := 0) (j := 1) zero_ne_one
    (ENNReal.ofReal_pos.2 (geometricLayerMass_pos hq0 hq1 0)).ne'
    (ENNReal.ofReal_pos.2 (geometricLayerMass_pos hq0 hq1 1)).ne'

end GeometricLayer

/-! ### Theorem 7.1: the Hasse execution defect -/

section HasseDefect

theorem hassePacketRatio_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hassePacketRatio t := by
  unfold hassePacketRatio
  have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

theorem hassePacketRatio_lt_one (t : ℝ) : hassePacketRatio t < 1 :=
  (hassePacketRatio_lt_half t).trans (by norm_num)

/-- **`(RFDM.29)`** the Hasse recovery law `κ_t(n) = (1 - r(t)) r(t)^n`. -/
def hasseRecoveryPMF (t : ℝ) (ht : 0 ≤ t) : PMF ℕ :=
  geometricLayerPMF (hassePacketRatio t) (hassePacketRatio_nonneg ht) (hassePacketRatio_lt_one t)

/-- The recovery kernel of a Hasse history profile is the Hasse recovery law at its scale. -/
theorem HasseHistoryProfile.kernel_eq_hasseRecoveryPMF {X : Type*} [MeasurableSpace X]
    (T : HasseHistoryProfile X) (x : X) :
    T.kernel x = (hasseRecoveryPMF (T.scale x) (T.scale_pos x).le).toMeasure := by
  refine Measure.ext_of_singleton fun n => ?_
  rw [T.kernel_apply_singleton, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton n)]
  rfl

theorem hasseRecoveryPMF_not_dirac {t : ℝ} (ht : 0 < t) :
    ¬ ∃ n, hasseRecoveryPMF t ht.le = PMF.pure n := by
  rintro ⟨n, hn⟩
  have hq := hassePacketRatio_mem_Ioo ht
  have h0 := geometricLayerMass_pos hq.1 hq.2 n
  have h1 := geometricLayerMass_pos hq.1 hq.2 (n + 1)
  have := congrArg (fun p : PMF ℕ => p (n + 1)) hn
  simp only [hasseRecoveryPMF, geometricLayerPMF_apply, PMF.pure_apply,
    if_neg (Nat.succ_ne_self n)] at this
  exact (ENNReal.ofReal_pos.2 h1).ne' this

/-- **Theorem 7.1, `(RFDM.30)`–`(RFDM.31)`**: the Hasse recovery law at a positive scale has
execution defects `TV = 2r/(1+r)`, `D(Δ ‖ κ ⊗ κ) = -log(1-r) - r/(1-r) log r` and
`D(κ ⊗ κ ‖ Δ) = ∞`. -/
theorem hasse_execution_defect {t : ℝ} (ht : 0 < t) :
    FormationExcess.totalVariation (diagonalVector (hasseRecoveryPMF t ht.le))
        (productVector (hasseRecoveryPMF t ht.le)) =
        2 * hassePacketRatio t / (1 + hassePacketRatio t) ∧
      klDiv (diagonalCoupling (hasseRecoveryPMF t ht.le))
          (productCoupling (hasseRecoveryPMF t ht.le)) =
        ENNReal.ofReal (-Real.log (1 - hassePacketRatio t) -
          hassePacketRatio t / (1 - hassePacketRatio t) * Real.log (hassePacketRatio t)) ∧
      klDiv (productCoupling (hasseRecoveryPMF t ht.le))
          (diagonalCoupling (hasseRecoveryPMF t ht.le)) = ⊤ := by
  have hq := hassePacketRatio_mem_Ioo ht
  exact ⟨geometricLayer_totalVariation _ _, geometricLayer_klDiv_diagonal_product hq.1 hq.2,
    geometricLayer_klDiv_product_diagonal hq.1 hq.2⟩

theorem strictMono_hassePacketRatio : StrictMono hassePacketRatio := fun s t hst => by
  unfold hassePacketRatio
  have : Real.exp (-t) < Real.exp (-s) := Real.exp_lt_exp.2 (neg_lt_neg hst)
  linarith

/-- The total-variation execution defect `V(t) = 2r(t)/(1 + r(t))`. -/
def hasseExecutionTV (t : ℝ) : ℝ := geometricExecutionTV (hassePacketRatio t)

/-- The directed-KL execution defect `J(t) = -log(1-r(t)) - r(t)/(1-r(t)) log r(t)`. -/
def hasseExecutionEntropy (t : ℝ) : ℝ := geometricExecutionEntropy (hassePacketRatio t)

theorem strictMonoOn_hasseExecutionTV : StrictMonoOn hasseExecutionTV (Set.Ioi 0) :=
  fun s hs t _ hst => strictMonoOn_geometricExecutionTV
    (show -1 < hassePacketRatio s by linarith [(hassePacketRatio_mem_Ioo hs).1])
    (show -1 < hassePacketRatio t by linarith [hassePacketRatio_nonneg (le_of_lt
      (lt_trans (Set.mem_Ioi.1 hs) hst))])
    (strictMono_hassePacketRatio hst)

theorem strictMonoOn_hasseExecutionEntropy :
    StrictMonoOn hasseExecutionEntropy (Set.Ioi 0) :=
  fun _ hs _ ht hst => strictMonoOn_geometricExecutionEntropy (hassePacketRatio_mem_Ioo hs)
    (hassePacketRatio_mem_Ioo ht) (strictMono_hassePacketRatio hst)

theorem inv_eq_self_iff_of_pos {t : ℝ} (ht : 0 < t) : t⁻¹ = t ↔ t = 1 := by
  constructor
  · intro h
    have h2 : t * t = 1 := by
      calc t * t = t * t⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel₀ ht.ne'
    nlinarith
  · rintro rfl; exact inv_one

/-- **Corollary 7.2, `(RFDM.32)`**: both execution defects are strictly increasing in the scale,
so `V(t) = V(1/t)` and `J(t) = J(1/t)` hold exactly at `t = 1`. -/
theorem hasse_execution_balance {t : ℝ} (ht : 0 < t) :
    (hasseExecutionTV t = hasseExecutionTV t⁻¹ ↔ t = 1) ∧
      (hasseExecutionEntropy t = hasseExecutionEntropy t⁻¹ ↔ t = 1) := by
  have hti : t⁻¹ ∈ Set.Ioi (0 : ℝ) := inv_pos.2 ht
  refine ⟨⟨fun h => ?_, fun h => by rw [h, inv_one]⟩, ⟨fun h => ?_, fun h => by rw [h, inv_one]⟩⟩
  · exact (inv_eq_self_iff_of_pos ht).1 (strictMonoOn_hasseExecutionTV.injOn ht hti h).symm
  · exact (inv_eq_self_iff_of_pos ht).1
      (strictMonoOn_hasseExecutionEntropy.injOn ht hti h).symm

/-- The logarithmic-scale theta Hasse ratio is the Hasse ratio at scale `e^x`. -/
theorem thetaHasseRatio_eq (x : ℝ) : thetaHasseRatio x = hassePacketRatio (Real.exp x) := rfl

end HasseDefect

/-! ### Theorem 8.1: Hasse-to-KMS modular parameter transport -/

section ModularTransport

/-- **`(RFDM.34a)`** the adjacent-depth ratio of the Hasse recovery law is `q(t) = r(t)`. -/
theorem hassePacketRecovery_succ_div {t : ℝ} (ht : 0 < t) (n : ℕ) :
    hassePacketRecovery t (n + 1) / hassePacketRecovery t n = hassePacketRatio t :=
  geometricLayerMass_succ_div n (hassePacketRatio_mem_Ioo ht).1 (hassePacketRatio_mem_Ioo ht).2

/-- **`(RFDM.34b)`** the modular product `βE = log(κ_t(n)/κ_t(n+1)) = -log r(t)`, for every
depth `n`. -/
theorem log_hassePacketRecovery_div_succ {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Real.log (hassePacketRecovery t n / hassePacketRecovery t (n + 1)) =
      -Real.log (hassePacketRatio t) := by
  rw [← inv_div, hassePacketRecovery_succ_div ht, Real.log_inv]

/-- **`(RFDM.34c)`** the Hasse scale `t(q) = -log(1 - 2q)` attached to a KMS ratio `q`. -/
def hasseScaleOfRatio (q : ℝ) : ℝ := -Real.log (1 - 2 * q)

theorem hasseScaleOfRatio_hassePacketRatio (t : ℝ) :
    hasseScaleOfRatio (hassePacketRatio t) = t := by
  rw [hasseScaleOfRatio, hassePacketRatio,
    show 1 - 2 * ((1 - Real.exp (-t)) / 2) = Real.exp (-t) by ring, Real.log_exp, neg_neg]

theorem hassePacketRatio_hasseScaleOfRatio {q : ℝ} (hq : q < 1 / 2) :
    hassePacketRatio (hasseScaleOfRatio q) = q := by
  rw [hassePacketRatio, hasseScaleOfRatio, neg_neg, Real.exp_log (by linarith)]
  ring

theorem hasseScaleOfRatio_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1 / 2) :
    0 < hasseScaleOfRatio q := by
  rw [hasseScaleOfRatio, neg_pos]
  exact Real.log_neg (by linarith) (by linarith)

/-- **Theorem 8.1, `(RFDM.34c)`**: for `q ∈ (0, 1/2)` the scale `t(q) = -log(1 - 2q)` is the
unique Hasse scale whose recovery law is the KMS layer law `p_q`. -/
theorem hasseRecovery_eq_geometricLayer_iff {q : ℝ} (hq1 : q < 1 / 2) (t : ℝ) :
    (∀ n, hassePacketRecovery t n = geometricLayerMass q n) ↔ t = hasseScaleOfRatio q := by
  constructor
  · intro h
    have h0 := h 0
    simp only [hassePacketRecovery, geometricLayerMass, pow_zero, mul_one] at h0
    have hr : hassePacketRatio t = q := by linarith
    rw [← hr, hasseScaleOfRatio_hassePacketRatio]
  · rintro rfl n
    rw [hassePacketRecovery, hassePacketRatio_hasseScaleOfRatio hq1]
    rfl

/-- **`(RFDM.34d)`** functional-equation reflection `t ↦ 1/t` transported to the KMS ratio:
`Θ(q) = r(1/t(q))`. -/
def modularReflection (q : ℝ) : ℝ := hassePacketRatio (hasseScaleOfRatio q)⁻¹

/-- **Theorem 8.1, `(RFDM.34d)`–`(RFDM.34e)`**: `Θ` maps `(0, 1/2)` to itself, `Θ² = I`, and
`Θ(q) = q` exactly at `q_* = (1 - e^{-1})/2`. -/
theorem modularReflection_laws {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1 / 2) :
    modularReflection q ∈ Set.Ioo 0 (1 / 2) ∧ modularReflection (modularReflection q) = q ∧
      (modularReflection q = q ↔ q = (1 - Real.exp (-1)) / 2) := by
  have ht := hasseScaleOfRatio_pos hq0 hq1
  have hti : 0 < (hasseScaleOfRatio q)⁻¹ := inv_pos.2 ht
  refine ⟨⟨(hassePacketRatio_mem_Ioo hti).1, hassePacketRatio_lt_half _⟩, ?_, ?_⟩
  · rw [modularReflection, modularReflection, hasseScaleOfRatio_hassePacketRatio, inv_inv,
      hassePacketRatio_hasseScaleOfRatio hq1]
  · have hfix : modularReflection q = q ↔ (hasseScaleOfRatio q)⁻¹ = hasseScaleOfRatio q := by
      have h := strictMono_hassePacketRatio.injective.eq_iff (a := (hasseScaleOfRatio q)⁻¹)
        (b := hasseScaleOfRatio q)
      rwa [hassePacketRatio_hasseScaleOfRatio hq1] at h
    rw [hfix, inv_eq_self_iff_of_pos ht]
    constructor
    · intro h
      rw [← hassePacketRatio_hasseScaleOfRatio hq1, h]
      rfl
    · intro h
      rw [h, show (1 - Real.exp (-1)) / 2 = hassePacketRatio 1 from rfl,
        hasseScaleOfRatio_hassePacketRatio]

end ModularTransport

end GaloisForLFunctions.HTGeometry.ResetDilation
