import GaloisForLFunctions.HTGeometry.BernoulliShiftEntropy
import GaloisForLFunctions.HTGeometry.KMSGibbsDensityExecutionEntropy

/-!
# Frozen formed-history entropy classification and the source-alternation no-go

* **§1, `(HEO.1)`–`(HEO.4)`**: the regenerative lift `R̂((y,a)) = δ_{Ry} ⊗ κ_{Ry}` carries
  `E_κ(μ)` to `E_κ(R_*μ)` and is endpoint-information-neutral:
  `D(E_κ μ ‖ E_κ ν) = D(μ ‖ ν) = D(E_κ R_*μ ‖ E_κ R_*ν)`.
* **Theorem 2.1, `(HEO.5)`–`(HEO.13)`**: a strict formed-history lift — a mod-zero measurable
  bijection `Θ : (A^ℤ, p^ℤ) → (A^ℤ, q^ℤ)` with measurable inverse, `Θ_* p^ℤ = q^ℤ` and
  `Θ S = S Θ` mod zero — forces `H(p) = H(q)`, because it preserves Kolmogorov–Sinai entropy and
  `h_KS(S, p^ℤ) = H(p)`.  The formation-entropy anomaly `𝔄_p(x) = H(p_x) - H(p_{θx})` vanishes at
  every liftable parameter, is odd under the involution and additive over independent products.
* **Theorem 3.1, `(HEO.14)`–`(HEO.19)`**: for the geometric Hasse family
  `p_x(n) = (1 - q(x)) q(x)^n`, `q(x) = (1 - e^{-e^x})/2`, a strict lift from `x` to `-x` exists
  iff `𝔄(x) = 0` iff `x = 0`; `𝔄` is odd, strictly increasing, with derivative
  `h'(q(x)) q'(x) + h'(q(-x)) q'(-x) > 0`.
* **§4, `(HEO.20)`–`(HEO.21)`**:
  `h_KS(S, P_x) = H(p_q) = D(Δ_{p_q} ‖ p_q ⊗ p_q) = S_vN(ρ_q) = h(q)`, so the anomaly has four
  exact realizations.
* **§5, `(HEO.24)`–`(HEO.26)`**: for the source-natural alternating law
  `P^alt_x = ⊗_j p_{θ^j x}` the shift satisfies `S_* P^alt_x = P^alt_{θx}` for every `x` — it is a
  strict lift at every parameter — `S²` fixes each phase law, and the two-coordinate entropy
  `H(p_x) + H(p_{θx})` is reflection-invariant.
-/

open MeasureTheory InformationTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry.ObservableEntropy
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FrozenHistory

/-! ### §1: the regenerative endpoint lift -/

section Regenerative

variable {Y H : Type*} [MeasurableSpace Y] [MeasurableSpace H]

/-- **`(HEO.3)`–`(HEO.4)`** the regenerative lift is endpoint-information-neutral. -/
theorem regenerativeLift_endpoint_neutral (κ : Kernel Y H) [IsMarkovKernel κ] {R : Y → Y}
    (hR : Measurable R) (hinv : ∀ y, R (R y) = y) (μ ν : Measure Y) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    formationLiftKernel κ R hR ∘ₘ splitFormation μ κ = splitFormation (μ.map R) κ ∧
      klDiv (splitFormation μ κ) (splitFormation ν κ) = klDiv μ ν ∧
      klDiv (splitFormation (μ.map R) κ) (splitFormation (ν.map R) κ) = klDiv μ ν := by
  let e : Y ≃ᵐ Y := ⟨⟨R, R, hinv, hinv⟩, hR, hR⟩
  have hemb : MeasurableEmbedding R := e.measurableEmbedding
  refine ⟨formationLiftKernel_naturality μ κ R hR, klDiv_splitFormation μ ν κ, ?_⟩
  haveI : IsFiniteMeasure (μ.map R) := Measure.isFiniteMeasure_map μ R
  haveI : IsFiniteMeasure (ν.map R) := Measure.isFiniteMeasure_map ν R
  rw [klDiv_splitFormation, klDiv_map_measurableEmbedding hemb]

end Regenerative

/-! ### §2: strict formed-history lifts -/

section Lift

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]

/-- **`(HEO.7)`–`(HEO.8)`** a strict formed-history lift from `P` to `Q`: a mod-zero measurable
bijection with measurable inverse carrying `P` to `Q` and commuting with the shift mod zero. -/
structure StrictHistoryLift (P Q : Measure (ℤ → A)) where
  /-- the lift `Θ` -/
  toFun : (ℤ → A) → ℤ → A
  /-- its inverse -/
  invFun : (ℤ → A) → ℤ → A
  measurable_toFun : Measurable toFun
  measurable_invFun : Measurable invFun
  left_inv : ∀ᵐ ω ∂P, invFun (toFun ω) = ω
  right_inv : ∀ᵐ ω ∂Q, toFun (invFun ω) = ω
  map_eq : P.map toFun = Q
  comm : toFun ∘ leftShift =ᵐ[P] leftShift ∘ toFun

variable {P Q : Measure (ℤ → A)}

namespace StrictHistoryLift

/-- The identity lift. -/
def refl (P : Measure (ℤ → A)) : StrictHistoryLift P P where
  toFun := id
  invFun := id
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id
  left_inv := ae_of_all _ fun _ => rfl
  right_inv := ae_of_all _ fun _ => rfl
  map_eq := Measure.map_id
  comm := ae_of_all _ fun _ => rfl

omit [MeasurableSingletonClass A] [Countable A] in
theorem measurePreserving (L : StrictHistoryLift P Q) : MeasurePreserving L.toFun P Q :=
  ⟨L.measurable_toFun, L.map_eq⟩

omit [MeasurableSingletonClass A] [Countable A] in
theorem map_invFun (L : StrictHistoryLift P Q) : Q.map L.invFun = P := by
  have key : (P.map L.toFun).map L.invFun = P := by
    rw [Measure.map_map L.measurable_invFun L.measurable_toFun,
      Measure.map_congr (show L.invFun ∘ L.toFun =ᵐ[P] id from L.left_inv), Measure.map_id]
  rwa [L.map_eq] at key

omit [MeasurableSingletonClass A] [Countable A] in
/-- The target law is shift-invariant when the source law is. -/
theorem measurePreserving_shift_target (L : StrictHistoryLift P Q)
    (hS : MeasurePreserving leftShift P P) : MeasurePreserving leftShift Q Q := by
  refine ⟨measurable_leftShift, ?_⟩
  rw [← L.map_eq, Measure.map_map measurable_leftShift L.measurable_toFun,
    ← Measure.map_congr L.comm, ← Measure.map_map L.measurable_toFun measurable_leftShift,
    hS.map_eq]

/-- The inverse commutes with the shift mod zero. -/
theorem comm_inv (L : StrictHistoryLift P Q) (hS : MeasurePreserving leftShift P P) :
    L.invFun ∘ leftShift =ᵐ[Q] leftShift ∘ L.invFun := by
  have key : ∀ᵐ ω ∂(P.map L.toFun), (L.invFun ∘ leftShift) ω = (leftShift ∘ L.invFun) ω := by
    rw [ae_map_iff L.measurable_toFun.aemeasurable
      (measurableSet_eq_fun (L.measurable_invFun.comp measurable_leftShift)
        (measurable_leftShift.comp L.measurable_invFun))]
    have h2 : ∀ᵐ ω ∂P, L.invFun (L.toFun (leftShift ω)) = leftShift ω :=
      hS.quasiMeasurePreserving.ae L.left_inv
    filter_upwards [L.comm, h2, L.left_inv] with ω e1 e2 e3
    simp only [Function.comp_apply] at e1 ⊢
    rw [← e1, e2, e3]
  rw [L.map_eq] at key
  exact key

/-- The inverse of a strict formed-history lift. -/
def symm (L : StrictHistoryLift P Q) (hS : MeasurePreserving leftShift P P) :
    StrictHistoryLift Q P where
  toFun := L.invFun
  invFun := L.toFun
  measurable_toFun := L.measurable_invFun
  measurable_invFun := L.measurable_toFun
  left_inv := L.right_inv
  right_inv := L.left_inv
  map_eq := L.map_invFun
  comm := L.comm_inv hS

/-- A strict formed-history lift preserves Kolmogorov–Sinai entropy. -/
theorem ksEntropy_eq (L : StrictHistoryLift P Q) (hS : MeasurePreserving leftShift P P) :
    ksEntropy Q leftShift = ksEntropy P leftShift :=
  le_antisymm (ksEntropy_le_of_factor P L.measurePreserving hS measurable_leftShift L.comm)
    (ksEntropy_le_of_factor Q (L.symm hS).measurePreserving (L.measurePreserving_shift_target hS)
      measurable_leftShift (L.symm hS).comm)

end StrictHistoryLift

/-- **Theorem 2.1, `(HEO.10)`**: a strict formed-history lift between Bernoulli histories of
finite base entropy forces equal base entropies. -/
theorem shannonEntropy_eq_of_lift {p q : Measure A} [IsProbabilityMeasure p]
    [IsProbabilityMeasure q] (hp : shannonEntropy p ≠ ⊤) (hq : shannonEntropy q ≠ ⊤)
    (L : StrictHistoryLift (bernoulliLaw p) (bernoulliLaw q)) :
    shannonEntropy p = shannonEntropy q := by
  rw [← ksEntropy_bernoulli p hp, ← ksEntropy_bernoulli q hq,
    L.ksEntropy_eq (measurePreserving_leftShift p)]

/-- **`(HEO.9)`** the formation-entropy anomaly `𝔄_p(x) = H(p_x) - H(p_{θx})`. -/
def entropyAnomaly {X : Type*} (p : X → Measure A) (θ : X → X) (x : X) : ℝ :=
  (shannonEntropy (p x)).toReal - (shannonEntropy (p (θ x))).toReal

/-- **Theorem 2.1, `(HEO.10)`**: the anomaly vanishes at every liftable parameter. -/
theorem entropyAnomaly_eq_zero_of_lift {X : Type*} (p : X → Measure A)
    [∀ x, IsProbabilityMeasure (p x)] (θ : X → X) (hfin : ∀ x, shannonEntropy (p x) ≠ ⊤) {x : X}
    (L : StrictHistoryLift (bernoulliLaw (p x)) (bernoulliLaw (p (θ x)))) :
    entropyAnomaly p θ x = 0 := by
  rw [entropyAnomaly, shannonEntropy_eq_of_lift (hfin x) (hfin (θ x)) L, sub_self]

omit [MeasurableSingletonClass A] [Countable A] in
/-- **`(HEO.11)`** the anomaly is odd under the involution. -/
theorem entropyAnomaly_involution {X : Type*} (p : X → Measure A) {θ : X → X}
    (hθ : ∀ x, θ (θ x) = x) (x : X) : entropyAnomaly p θ (θ x) = -entropyAnomaly p θ x := by
  rw [entropyAnomaly, entropyAnomaly, hθ, neg_sub]

/-- Shannon entropy is additive over independent products. -/
theorem shannonEntropy_prod {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    [Countable B] (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    shannonEntropy (μ.prod ν) = shannonEntropy μ + shannonEntropy ν := by
  have hid : (id : A × B → A × B) = pairObs Prod.fst Prod.snd := rfl
  have hindep : ∀ a b, μ.prod ν (Prod.fst ⁻¹' {a} ∩ Prod.snd ⁻¹' {b}) =
      μ.prod ν (Prod.fst ⁻¹' {a}) * μ.prod ν (Prod.snd ⁻¹' {b}) := by
    intro a b
    rw [← Set.prod_eq, Measure.prod_prod, show Prod.fst ⁻¹' {a} = ({a} : Set A) ×ˢ univ by
      ext; simp, show Prod.snd ⁻¹' {b} = (univ : Set A) ×ˢ ({b} : Set B) by ext; simp,
      Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one, one_mul]
  rw [shannonEntropy, hid, obsEntropy_pairObs_of_indep _ measurable_fst measurable_snd hindep,
    obsEntropy_eq_shannonEntropy_map _ measurable_fst,
    obsEntropy_eq_shannonEntropy_map _ measurable_snd, Measure.map_fst_prod,
    Measure.map_snd_prod, measure_univ, measure_univ, one_smul, one_smul]

/-- **`(HEO.12)`** the anomaly is additive over independent formation families. -/
theorem entropyAnomaly_prod {X B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    [Countable B] (p : X → Measure A) (q : X → Measure B) [∀ x, IsProbabilityMeasure (p x)]
    [∀ x, IsProbabilityMeasure (q x)] (θ : X → X) (hp : ∀ x, shannonEntropy (p x) ≠ ⊤)
    (hq : ∀ x, shannonEntropy (q x) ≠ ⊤) (x : X) :
    entropyAnomaly (fun x => (p x).prod (q x)) θ x =
      entropyAnomaly p θ x + entropyAnomaly q θ x := by
  simp only [entropyAnomaly, shannonEntropy_prod, ENNReal.toReal_add (hp _) (hq _)]
  ring

end Lift

/-! ### §3: the geometric Hasse family -/

section Geometric

theorem thetaHasseRatio_lt_one (x : ℝ) : thetaHasseRatio x < 1 :=
  (thetaHasseRatio_lt_half x).trans (by norm_num)

/-- **`(HEO.14)`** the geometric recovery law `p_x(n) = (1 - q(x)) q(x)^n`,
`q(x) = (1 - e^{-e^x})/2`. -/
def geometricRecoveryLaw (x : ℝ) : Measure ℕ :=
  (ResetDilation.geometricLayerPMF (thetaHasseRatio x) (thetaHasseRatio_pos x).le
    (thetaHasseRatio_lt_one x)).toMeasure

instance (x : ℝ) : IsProbabilityMeasure (geometricRecoveryLaw x) := by
  unfold geometricRecoveryLaw; infer_instance

/-- **`(HEO.15)`** `H(p_x) = h(q(x)) = -log(1-q) - q/(1-q) log q`. -/
theorem shannonEntropy_geometricRecoveryLaw (x : ℝ) :
    shannonEntropy (geometricRecoveryLaw x) =
      ENNReal.ofReal (geometricExecutionEntropy (thetaHasseRatio x)) := by
  have hq0 := thetaHasseRatio_pos x
  have hq1 := thetaHasseRatio_lt_one x
  rw [shannonEntropy, obsEntropy, ← tsum_geometricLayerShannonTerm hq0 hq1,
    ENNReal.ofReal_tsum_of_nonneg (fun n => ?_)
      (ResetDilation.summable_geometricLayerShannonTerm hq0 hq1)]
  · refine tsum_congr fun n => ?_
    rw [preimage_id, geometricRecoveryLaw, PMF.toMeasure_apply_singleton _ _
      (measurableSet_singleton n), entropyTerm, ResetDilation.geometricLayerPMF_apply,
      ENNReal.toReal_ofReal (ResetDilation.geometricLayerMass_nonneg hq0.le hq1 n),
      Real.negMulLog_def, geometricLayerShannonTerm]
  · change 0 ≤ Real.negMulLog (geometricLayerMass (thetaHasseRatio x) n)
    exact Real.negMulLog_nonneg (ResetDilation.geometricLayerMass_nonneg hq0.le hq1 n)
      (ResetDilation.geometricLayerMass_le_one hq0.le hq1 n)

theorem shannonEntropy_geometricRecoveryLaw_ne_top (x : ℝ) :
    shannonEntropy (geometricRecoveryLaw x) ≠ ⊤ := by
  rw [shannonEntropy_geometricRecoveryLaw]; exact ENNReal.ofReal_ne_top

theorem geometricExecutionEntropy_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ geometricExecutionEntropy q := by
  rw [← tsum_geometricLayerShannonTerm hq0 hq1]
  refine tsum_nonneg fun n => ?_
  change 0 ≤ Real.negMulLog (geometricLayerMass q n)
  exact Real.negMulLog_nonneg (ResetDilation.geometricLayerMass_nonneg hq0.le hq1 n)
    (ResetDilation.geometricLayerMass_le_one hq0.le hq1 n)

/-- **`(HEO.17)`** the geometric anomaly `𝔄(x) = h(q(x)) - h(q(-x))`. -/
def geometricAnomaly (x : ℝ) : ℝ :=
  geometricExecutionEntropy (thetaHasseRatio x) - geometricExecutionEntropy (thetaHasseRatio (-x))

theorem geometricAnomaly_eq_entropyAnomaly (x : ℝ) :
    geometricAnomaly x = entropyAnomaly geometricRecoveryLaw (fun x => -x) x := by
  rw [geometricAnomaly, entropyAnomaly, shannonEntropy_geometricRecoveryLaw,
    shannonEntropy_geometricRecoveryLaw,
    ENNReal.toReal_ofReal (geometricExecutionEntropy_nonneg (thetaHasseRatio_pos _)
      (thetaHasseRatio_lt_one _)),
    ENNReal.toReal_ofReal (geometricExecutionEntropy_nonneg (thetaHasseRatio_pos _)
      (thetaHasseRatio_lt_one _))]

/-- **`(HEO.19)`** `𝔄` is odd and strictly increasing. -/
theorem geometricAnomaly_odd_strictMono :
    (∀ x, geometricAnomaly (-x) = -geometricAnomaly x) ∧ StrictMono geometricAnomaly := by
  refine ⟨fun x => by rw [geometricAnomaly, geometricAnomaly, neg_neg, neg_sub], fun x y hxy => ?_⟩
  have h1 := strictMono_thetaHasseExecutionEntropy hxy
  have h2 := strictMono_thetaHasseExecutionEntropy (neg_lt_neg hxy)
  simp only at h1 h2
  rw [geometricAnomaly, geometricAnomaly]
  linarith

/-- **`(HEO.16)`** `q'(x) = e^{x - e^x}/2`. -/
theorem hasDerivAt_thetaHasseRatio (x : ℝ) :
    HasDerivAt thetaHasseRatio (Real.exp (x - Real.exp x) / 2) x := by
  have h1 : HasDerivAt (fun y => -Real.exp y) (-Real.exp x) x := (Real.hasDerivAt_exp x).neg
  have h2 := (h1.exp.const_sub 1).div_const 2
  refine h2.congr_deriv ?_
  rw [Real.exp_sub, Real.exp_neg]
  field_simp

/-- **`(HEO.19)`** `𝔄'(x) = h'(q(x)) q'(x) + h'(q(-x)) q'(-x) > 0`. -/
theorem hasDerivAt_geometricAnomaly (x : ℝ) :
    HasDerivAt geometricAnomaly
      (-Real.log (thetaHasseRatio x) / (1 - thetaHasseRatio x) ^ 2 *
          (Real.exp (x - Real.exp x) / 2) +
        -Real.log (thetaHasseRatio (-x)) / (1 - thetaHasseRatio (-x)) ^ 2 *
          (Real.exp (-x - Real.exp (-x)) / 2)) x ∧
      0 < -Real.log (thetaHasseRatio x) / (1 - thetaHasseRatio x) ^ 2 *
          (Real.exp (x - Real.exp x) / 2) +
        -Real.log (thetaHasseRatio (-x)) / (1 - thetaHasseRatio (-x)) ^ 2 *
          (Real.exp (-x - Real.exp (-x)) / 2) := by
  have hJ : ∀ y : ℝ, HasDerivAt geometricExecutionEntropy
      (-Real.log (thetaHasseRatio y) / (1 - thetaHasseRatio y) ^ 2) (thetaHasseRatio y) :=
    fun y => hasDerivAt_geometricExecutionEntropy (thetaHasseRatio_pos y).ne'
      (thetaHasseRatio_lt_one y).ne
  have h1 := (hJ x).comp x (hasDerivAt_thetaHasseRatio x)
  have h2 := (hJ (-x)).comp x ((hasDerivAt_thetaHasseRatio (-x)).comp x (hasDerivAt_neg x))
  have hpos : ∀ y : ℝ, 0 < -Real.log (thetaHasseRatio y) / (1 - thetaHasseRatio y) ^ 2 *
      (Real.exp (y - Real.exp y) / 2) := fun y => by
    have hlog : Real.log (thetaHasseRatio y) < 0 :=
      Real.log_neg (thetaHasseRatio_pos y) (thetaHasseRatio_lt_one y)
    have hden : 0 < (1 - thetaHasseRatio y) ^ 2 := by
      have := thetaHasseRatio_lt_one y
      exact pow_pos (by linarith) 2
    exact mul_pos (div_pos (neg_pos.2 hlog) hden) (by positivity)
  refine ⟨?_, add_pos (hpos x) (hpos (-x))⟩
  exact (h1.sub h2).congr_deriv (by ring)

/-- **Theorem 3.1, `(HEO.18)`**: for the geometric formed histories, a strict formed-history lift
from `x` to `-x` exists iff `𝔄(x) = 0` iff `x = 0`. -/
theorem frozenHistory_classification (x : ℝ) :
    List.TFAE [Nonempty (StrictHistoryLift (bernoulliLaw (geometricRecoveryLaw x))
        (bernoulliLaw (geometricRecoveryLaw (-x)))), geometricAnomaly x = 0, x = 0] := by
  tfae_have 1 → 2 := fun ⟨L⟩ => by
    rw [geometricAnomaly_eq_entropyAnomaly]
    exact entropyAnomaly_eq_zero_of_lift geometricRecoveryLaw (fun x => -x)
      shannonEntropy_geometricRecoveryLaw_ne_top L
  tfae_have 2 → 3 := fun h => by
    have h' : geometricExecutionEntropy (thetaHasseRatio x) =
        geometricExecutionEntropy (thetaHasseRatio (-x)) := by
      rw [geometricAnomaly, sub_eq_zero] at h; exact h
    have := strictMono_thetaHasseExecutionEntropy.injective h'
    linarith
  tfae_have 3 → 1 := fun h => by
    subst h
    rw [neg_zero]
    exact ⟨StrictHistoryLift.refl _⟩
  tfae_finish

end Geometric

/-! ### §4: the four-organ conservation identity -/

section FourOrgan

/-- **`(HEO.20)`** `h_KS(S, P_x) = H(p_q) = D(Δ_{p_q} ‖ p_q ⊗ p_q) = S_vN(ρ_q) = h(q)` at
`q = q(x)`, with `S_vN(ρ_q) = -Tr(ρ_q log ρ_q)`. -/
theorem fourOrgan_entropy (x : ℝ) :
    ksEntropy (bernoulliLaw (geometricRecoveryLaw x)) leftShift =
        shannonEntropy (geometricRecoveryLaw x) ∧
      shannonEntropy (geometricRecoveryLaw x) =
        klDiv (ResetDilation.diagonalCoupling (ResetDilation.geometricLayerPMF (thetaHasseRatio x)
            (thetaHasseRatio_pos x).le (thetaHasseRatio_lt_one x)))
          (ResetDilation.productCoupling (ResetDilation.geometricLayerPMF (thetaHasseRatio x)
            (thetaHasseRatio_pos x).le (thetaHasseRatio_lt_one x))) ∧
      shannonEntropy (geometricRecoveryLaw x) = ENNReal.ofReal (vonNeumannEntropy
        (ResetDilation.gibbsDensity (thetaHasseRatio x) (thetaHasseRatio_pos x).le
          (thetaHasseRatio_lt_one x))) ∧
      shannonEntropy (geometricRecoveryLaw x) = ENNReal.ofReal (-ContinuousLinearMap.opTrace
        (ResetDilation.realCFC (fun t : ℝ => t * Real.log t)
          (ResetDilation.gibbsDensity (thetaHasseRatio x) (thetaHasseRatio_pos x).le
            (thetaHasseRatio_lt_one x)))).re ∧
      shannonEntropy (geometricRecoveryLaw x) =
        ENNReal.ofReal (geometricExecutionEntropy (thetaHasseRatio x)) := by
  have hq0 := thetaHasseRatio_pos x
  have hq1 := thetaHasseRatio_lt_one x
  refine ⟨ksEntropy_bernoulli _ (shannonEntropy_geometricRecoveryLaw_ne_top x), ?_, ?_, ?_,
    shannonEntropy_geometricRecoveryLaw x⟩
  · rw [shannonEntropy_geometricRecoveryLaw,
      ResetDilation.geometricLayer_klDiv_diagonal_product hq0 hq1]
  · rw [shannonEntropy_geometricRecoveryLaw, ResetDilation.vonNeumannEntropy_gibbsDensity hq0 hq1]
  · rw [shannonEntropy_geometricRecoveryLaw,
      ResetDilation.opTrace_cfc_mul_log_gibbsDensity hq0 hq1, Complex.ofReal_re]

/-- **`(HEO.21)`** the anomaly in its four realizations: Kolmogorov–Sinai entropy, directed path
divergence, von Neumann entropy of the KMS state, and Shannon entropy. -/
theorem geometricAnomaly_four_realizations (x : ℝ) :
    geometricAnomaly x = (ksEntropy (bernoulliLaw (geometricRecoveryLaw x)) leftShift).toReal -
        (ksEntropy (bernoulliLaw (geometricRecoveryLaw (-x))) leftShift).toReal ∧
      geometricAnomaly x =
        (klDiv (ResetDilation.diagonalCoupling (ResetDilation.geometricLayerPMF (thetaHasseRatio x)
            (thetaHasseRatio_pos x).le (thetaHasseRatio_lt_one x)))
          (ResetDilation.productCoupling (ResetDilation.geometricLayerPMF (thetaHasseRatio x)
            (thetaHasseRatio_pos x).le (thetaHasseRatio_lt_one x)))).toReal -
        (klDiv (ResetDilation.diagonalCoupling (ResetDilation.geometricLayerPMF
            (thetaHasseRatio (-x)) (thetaHasseRatio_pos (-x)).le (thetaHasseRatio_lt_one (-x))))
          (ResetDilation.productCoupling (ResetDilation.geometricLayerPMF (thetaHasseRatio (-x))
            (thetaHasseRatio_pos (-x)).le (thetaHasseRatio_lt_one (-x))))).toReal ∧
      geometricAnomaly x =
        vonNeumannEntropy (ResetDilation.gibbsDensity (thetaHasseRatio x)
            (thetaHasseRatio_pos x).le (thetaHasseRatio_lt_one x)) -
          vonNeumannEntropy (ResetDilation.gibbsDensity (thetaHasseRatio (-x))
            (thetaHasseRatio_pos (-x)).le (thetaHasseRatio_lt_one (-x))) := by
  have hJ : ∀ y : ℝ, (shannonEntropy (geometricRecoveryLaw y)).toReal =
      geometricExecutionEntropy (thetaHasseRatio y) := fun y => by
    rw [shannonEntropy_geometricRecoveryLaw, ENNReal.toReal_ofReal
      (geometricExecutionEntropy_nonneg (thetaHasseRatio_pos y) (thetaHasseRatio_lt_one y))]
  refine ⟨?_, ?_, ?_⟩
  · rw [(fourOrgan_entropy x).1, (fourOrgan_entropy (-x)).1, hJ, hJ, geometricAnomaly]
  · rw [← (fourOrgan_entropy x).2.1, ← (fourOrgan_entropy (-x)).2.1, hJ, hJ, geometricAnomaly]
  · rw [ResetDilation.vonNeumannEntropy_gibbsDensity (thetaHasseRatio_pos x)
      (thetaHasseRatio_lt_one x), ResetDilation.vonNeumannEntropy_gibbsDensity
      (thetaHasseRatio_pos (-x)) (thetaHasseRatio_lt_one (-x)), geometricAnomaly]

end FourOrgan

/-! ### §5: the source-natural alternating history -/

section Alternating

variable {A X : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
  (p : X → Measure A) [∀ x, IsProbabilityMeasure (p x)] {θ : X → X}

/-- The parameter at time `j` of the alternating history: `x` at even times, `θ x` at odd times. -/
def altParam (θ : X → X) (x : X) (j : ℤ) : X := if Even j then x else θ x

/-- **`(HEO.24)`** the alternating product law `P^alt_x = ⊗_j p_{θ^j x}`. -/
def altLaw (θ : X → X) (x : X) : Measure (ℤ → A) :=
  Measure.infinitePi fun j => p (altParam θ x j)

instance (x : X) : IsProbabilityMeasure (altLaw p θ x) := by unfold altLaw; infer_instance

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A] in
theorem altParam_shift (hθ : ∀ x, θ (θ x) = x) (x : X) (j : ℤ) :
    altParam θ (θ x) (j + -1) = altParam θ x j := by
  unfold altParam
  have : Even (j + -1) ↔ ¬ Even j := by
    rw [Int.even_add, even_neg]; simp
  by_cases hj : Even j
  · rw [if_neg (by tauto), if_pos hj, hθ]
  · rw [if_pos (by tauto), if_neg hj]

omit [MeasurableSingletonClass A] [Countable A] in
/-- **`(HEO.25)`** `S_* P^alt_x = P^alt_{θx}` for every `x`. -/
theorem altLaw_map_leftShift (hθ : ∀ x, θ (θ x) = x) (x : X) :
    (altLaw p θ x).map leftShift = altLaw p θ (θ x) := by
  have h := Measure.infinitePi_map_piCongrLeft (fun j => p (altParam θ (θ x) j))
    (Equiv.addRight (-1 : ℤ))
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => A) (Equiv.addRight (-1 : ℤ))) =
      leftShift := by
    funext ω j
    rw [MeasurableEquiv.coe_piCongrLeft]
    have := Equiv.piCongrLeft_apply_apply (fun _ : ℤ => A) (Equiv.addRight (-1 : ℤ)) ω (j + 1)
    simp only [Equiv.coe_addRight, add_neg_cancel_right] at this
    exact this
  have hlaw : (fun i => p (altParam θ (θ x) ((Equiv.addRight (-1 : ℤ)) i))) =
      fun i => p (altParam θ x i) := by
    funext i
    rw [Equiv.coe_addRight, altParam_shift hθ]
  rw [hfun, hlaw] at h
  exact h

omit [MeasurableSingletonClass A] [Countable A] in
/-- **`(HEO.25)`** the two-step shift preserves each phase law. -/
theorem altLaw_map_leftShift_two (hθ : ∀ x, θ (θ x) = x) (x : X) :
    (altLaw p θ x).map (leftShift^[2]) = altLaw p θ x := by
  rw [Function.iterate_succ, Function.iterate_one, ← Measure.map_map measurable_leftShift
    measurable_leftShift, altLaw_map_leftShift p hθ, altLaw_map_leftShift p hθ, hθ]

/-- **`(HEO.25)`** the shift is a strict formed-history lift between the alternating phase laws
at every parameter. -/
def altShiftLift (hθ : ∀ x, θ (θ x) = x) (x : X) :
    StrictHistoryLift (altLaw p θ x) (altLaw p θ (θ x)) where
  toFun := leftShift
  invFun := rightShift
  measurable_toFun := measurable_leftShift
  measurable_invFun := measurable_rightShift
  left_inv := ae_of_all _ rightShift_leftShift
  right_inv := ae_of_all _ leftShift_rightShift
  map_eq := altLaw_map_leftShift p hθ x
  comm := ae_of_all _ fun _ => rfl

/-- **`(HEO.26)`** the two-coordinate entropy of the alternating history is
`H(p_x) + H(p_{θx})`, which is invariant under reflection. -/
theorem altLaw_twoCoordinate_entropy (hθ : ∀ x, θ (θ x) = x) (x : X) :
    obsEntropy (altLaw p θ x) (fun ω : ℤ → A => (ω 0, ω 1)) =
        shannonEntropy (p x) + shannonEntropy (p (θ x)) ∧
      obsEntropy (altLaw p θ (θ x)) (fun ω : ℤ → A => (ω 0, ω 1)) =
        obsEntropy (altLaw p θ x) (fun ω : ℤ → A => (ω 0, ω 1)) := by
  have h01 : ∀ y, obsEntropy (altLaw p θ y) (fun ω : ℤ → A => (ω 0, ω 1)) =
      shannonEntropy (p y) + shannonEntropy (p (θ y)) := by
    intro y
    have hp0 : altParam θ y 0 = y := by simp [altParam]
    have hp1 : altParam θ y 1 = θ y := by simp [altParam]
    have hm0 : (altLaw p θ y).map (fun ω : ℤ → A => ω 0) = p y := by
      have := (measurePreserving_eval_infinitePi (fun j => p (altParam θ y j)) 0).map_eq
      rw [hp0] at this
      exact this
    have hm1 : (altLaw p θ y).map (fun ω : ℤ → A => ω 1) = p (θ y) := by
      have := (measurePreserving_eval_infinitePi (fun j => p (altParam θ y j)) 1).map_eq
      rw [hp1] at this
      exact this
    have hindep : ∀ a b, altLaw p θ y ((fun ω : ℤ → A => ω 0) ⁻¹' {a} ∩
        (fun ω : ℤ → A => ω 1) ⁻¹' {b}) = altLaw p θ y ((fun ω : ℤ → A => ω 0) ⁻¹' {a}) *
          altLaw p θ y ((fun ω : ℤ → A => ω 1) ⁻¹' {b}) := by
      intro a b
      classical
      let t : ℤ → Set A := fun j => if j = 0 then {a} else if j = 1 then {b} else univ
      have hset : (fun ω : ℤ → A => ω 0) ⁻¹' {a} ∩ (fun ω : ℤ → A => ω 1) ⁻¹' {b} =
          (({0, 1} : Finset ℤ) : Set ℤ).pi t := by
        ext ω
        simp [t]
      rw [hset, altLaw, Measure.infinitePi_pi _ (fun i _ => by
          simp only [t]; split_ifs <;> first | exact measurableSet_singleton _ |
            exact MeasurableSet.univ), Finset.prod_pair (by norm_num)]
      rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton a),
        ← Measure.map_apply (measurable_pi_apply 1) (measurableSet_singleton b)]
      rw [show altLaw p θ y = Measure.infinitePi (fun j => p (altParam θ y j)) from rfl] at hm0 hm1
      rw [hm0, hm1, hp0, hp1]
      simp [t]
    rw [show (fun ω : ℤ → A => (ω 0, ω 1)) = pairObs (fun ω : ℤ → A => ω 0)
        (fun ω : ℤ → A => ω 1) from rfl,
      obsEntropy_pairObs_of_indep _ (measurable_pi_apply 0) (measurable_pi_apply 1) hindep,
      obsEntropy_eq_shannonEntropy_map _ (measurable_pi_apply 0),
      obsEntropy_eq_shannonEntropy_map _ (measurable_pi_apply 1), hm0, hm1]
  refine ⟨h01 x, ?_⟩
  rw [h01, h01, hθ, add_comm]

end Alternating

end GaloisForLFunctions.HTGeometry.FrozenHistory
