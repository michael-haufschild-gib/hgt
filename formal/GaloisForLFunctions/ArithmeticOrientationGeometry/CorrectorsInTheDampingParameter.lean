import GaloisForLFunctions.ArithmeticOrientationGeometry.CorrectorsAndTheLefschetzTrace
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationRateIsTheDepthOfTheDeepestSeenZero

/-!
# Correctors in the damping parameter

On the scale flow, correctors convert relative compensation into absolute energy by an identity
(`CorrectorsAndTheLefschetzTrace`). This module adds the damping parameter `ε` and asks the
question of the review at every fixed small damping.

**Damping is a family of automorphisms of the correspondence algebra.** Weighting a correspondence
by the character `g ↦ e^{−ε s(g)}` (`ScalingDatum.damp`) is multiplicative for convolution
(`damp_conv`), composes additively in `ε` (`damp_damp`), is the identity at `ε = 0`
(`damp_zero_left`), and conjugates the Rosati involution to the opposite damping
(`rosati_damp`): `(α_ε ξ)′ = α_{−ε}(ξ′)`. So damping does not commute with the involution whose
positivity is the orientation; the damped trace `τ_x ∘ α_ε` pairs `ξ` with the one-sided damped
correlation `e^{−ε s(g)} c_x(g)` (`traceAt_damp`).

**Damped correctors exist on every pair of scales** (`isCorrector_damp_twoPoint`). For every
damping and every two scales the correspondence `c(h)[g] − c(g)[h]`, `c(k) = e^{−εs(k)}(e^{s(k)} + 1)`,
has vanishing damped pole trace; its damped Lefschetz trace is minus its damped primitive trace.
Relative compensation is always available.

**The damped orbit energy** (`dampedEnergy`). For a cycle of a configuration,
`E_x(ε) = sup_{t ≥ 0} e^{−εt}|c_x(t)| ∈ [0, ∞]` is antitone in `ε` and at least `|c_x(0)|`; on a
symmetric tempered configuration it is finite iff `x` is blind above depth `ε`
(`dampedEnergy_lt_top_iff_blindAbove`).

**Relative to absolute without loss** (`dampedEnergy_tfae`). On a symmetric tempered configuration
the following are equivalent: `x` is oriented; `E_x(0) < ∞`; `E_x(ε) < ∞` for every `ε > 0`, with
no control of how the constants grow as `ε ↓ 0`; `E_x(ε) = c_x(0)` for every `ε ≥ 0`. Finiteness of
the damped energy at every positive damping already yields the exact absolute energy `c_x(0)`: on
an orbit no horizon-free or damping-uniform bound on the relative loss is needed. For `ζ` and one
spectrally generic test this is RH (`riemannHypothesis_iff_forall_damped_bounded`).
-/

noncomputable section

open Finset Filter
open scoped ENNReal
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)
open ScalingDatum (conv rosati rosati_single rosati_add)

/-! ### Convolution on point masses -/

section Convolution

variable {G : Type*} [AddCommGroup G]

theorem conv_add_left (ξ₁ ξ₂ η : Correspondence G) :
    conv (ξ₁ + ξ₂) η = conv ξ₁ η + conv ξ₂ η := by
  rw [conv, Finsupp.sum_add_index' (fun _ => by simp) (fun g a b => by
    simp only [add_mul, Finsupp.single_add, Finsupp.sum_add]), ← conv, ← conv]

theorem conv_add_right (ξ η₁ η₂ : Correspondence G) :
    conv ξ (η₁ + η₂) = conv ξ η₁ + conv ξ η₂ := by
  simp only [conv]
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun h b c => by rw [mul_add, Finsupp.single_add])]

theorem conv_zero_left (η : Correspondence G) : conv 0 η = 0 := by simp [conv]

theorem conv_zero_right (ξ : Correspondence G) : conv ξ 0 = 0 := by simp [conv]

theorem conv_single_single (g h : G) (a b : ℝ) :
    conv (Finsupp.single g a) (Finsupp.single h b) = Finsupp.single (g + h) (a * b) := by
  rw [conv, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

end Convolution

namespace ScalingDatum

variable {G : Type*} [AddCommGroup G] {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (D : ScalingDatum G E)

/-! ### Damping automorphisms -/

/-- **Damping** a correspondence by `ε`: weight each scale by the character `e^{−ε s(g)}`. -/
def damp (ε : ℝ) (ξ : Correspondence G) : Correspondence G :=
  ξ.sum fun g a => Finsupp.single g (Real.exp (-ε * D.scale g) * a)

theorem damp_single (ε : ℝ) (g : G) (a : ℝ) :
    D.damp ε (Finsupp.single g a) = Finsupp.single g (Real.exp (-ε * D.scale g) * a) := by
  rw [damp, Finsupp.sum_single_index (by simp)]

theorem damp_add (ε : ℝ) (ξ η : Correspondence G) :
    D.damp ε (ξ + η) = D.damp ε ξ + D.damp ε η := by
  rw [damp, Finsupp.sum_add_index' (fun _ => by simp) (fun g a b => by
    rw [mul_add, Finsupp.single_add]), ← damp, ← damp]

theorem damp_zero (ε : ℝ) : D.damp ε 0 = 0 := by simp [damp]

/-- Damping is multiplicative for convolution: the weight is a character. -/
theorem damp_conv (ε : ℝ) (ξ η : Correspondence G) :
    D.damp ε (conv ξ η) = conv (D.damp ε ξ) (D.damp ε η) := by
  induction ξ using Finsupp.induction_linear with
  | zero => rw [conv_zero_left, D.damp_zero, conv_zero_left]
  | add ξ₁ ξ₂ h₁ h₂ => rw [conv_add_left, D.damp_add, h₁, h₂, D.damp_add, conv_add_left]
  | single g a =>
    induction η using Finsupp.induction_linear with
    | zero => rw [conv_zero_right, D.damp_zero, conv_zero_right]
    | add η₁ η₂ k₁ k₂ => rw [conv_add_right, D.damp_add, k₁, k₂, D.damp_add, conv_add_right]
    | single h b =>
      rw [conv_single_single, D.damp_single, D.damp_single, D.damp_single, conv_single_single,
        map_add, mul_add, Real.exp_add]
      congr 1
      ring

/-- Damping by `0` is the identity. -/
theorem damp_zero_left (ξ : Correspondence G) : D.damp 0 ξ = ξ := by
  induction ξ using Finsupp.induction_linear with
  | zero => exact D.damp_zero 0
  | add ξ η hξ hη => rw [D.damp_add, hξ, hη]
  | single g a => rw [D.damp_single, neg_zero, zero_mul, Real.exp_zero, one_mul]

/-- Dampings compose additively. -/
theorem damp_damp (ε δ : ℝ) (ξ : Correspondence G) :
    D.damp ε (D.damp δ ξ) = D.damp (ε + δ) ξ := by
  induction ξ using Finsupp.induction_linear with
  | zero => rw [D.damp_zero, D.damp_zero, D.damp_zero]
  | add ξ η hξ hη => rw [D.damp_add, D.damp_add, hξ, hη, D.damp_add]
  | single g a =>
    rw [D.damp_single, D.damp_single, D.damp_single, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring

/-- **Damping conjugates the Rosati involution to the opposite damping.** -/
theorem rosati_damp (ε : ℝ) (ξ : Correspondence G) :
    rosati (D.damp ε ξ) = D.damp (-ε) (rosati ξ) := by
  induction ξ using Finsupp.induction_linear with
  | zero => rw [D.damp_zero, show rosati (0 : Correspondence G) = 0 from Finsupp.mapDomain_zero,
      D.damp_zero]
  | add ξ η hξ hη => rw [D.damp_add, rosati_add, hξ, hη, rosati_add, D.damp_add]
  | single g a =>
    rw [D.damp_single, rosati_single, rosati_single, D.damp_single, map_neg]
    congr 2
    ring

/-- **The damped trace** pairs `ξ` with the one-sided damped correlation `e^{−εs(g)} c_x(g)`. -/
theorem traceAt_damp (ε : ℝ) (x : E) (ξ : Correspondence G) :
    D.traceAt x (D.damp ε ξ) = ξ.sum fun g a => a * (Real.exp (-ε * D.scale g) * D.orbitCorr x g) := by
  induction ξ using Finsupp.induction_linear with
  | zero => simp [D.damp_zero, traceAt, corr_zero, PolarSurface.defect, PolarSurface.polar]
  | add ξ η hξ hη =>
    rw [D.damp_add, D.traceAt_add, hξ, hη,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single g a =>
    rw [D.damp_single, D.traceAt_single_smul, Finsupp.sum_single_index (zero_mul _)]
    ring

/-! ### Damped correctors -/

theorem poleTrace_single (g : G) (a : ℝ) :
    D.poleTrace (Finsupp.single g a) = a * (Real.exp (D.scale g) + 1) := by
  rw [poleTrace, Finsupp.sum_single_index (zero_mul _)]

theorem poleTrace_add (ξ η : Correspondence G) :
    D.poleTrace (ξ + η) = D.poleTrace ξ + D.poleTrace η := by
  rw [poleTrace, Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), ← poleTrace,
    ← poleTrace]

/-- The damped pole weight `c(k) = e^{−εs(k)}(e^{s(k)} + 1)` of a scale. -/
def dampedPoleWeight (ε : ℝ) (k : G) : ℝ := Real.exp (-ε * D.scale k) * (Real.exp (D.scale k) + 1)

theorem dampedPoleWeight_pos (ε : ℝ) (k : G) : 0 < D.dampedPoleWeight ε k :=
  mul_pos (Real.exp_pos _) (by positivity)

/-- **Damped correctors exist on every pair of scales.** At every damping `ε` and for all scales
`g, h`, the correspondence `c(h)[g] − c(g)[h]` becomes a corrector after damping. -/
theorem isCorrector_damp_twoPoint (ε : ℝ) (g h : G) :
    D.IsCorrector (D.damp ε (Finsupp.single g (D.dampedPoleWeight ε h) +
      Finsupp.single h (-D.dampedPoleWeight ε g))) := by
  rw [IsCorrector, D.damp_add, D.damp_single, D.damp_single, D.poleTrace_add, D.poleTrace_single,
    D.poleTrace_single]
  simp only [dampedPoleWeight]
  ring

/-- **The damped conservation law.** For a damped corrector the Lefschetz trace of the damped
correspondence is minus its primitive trace, independently of the fibre degrees of the cycle. -/
theorem lefschetzTrace_damp_of_corrector {ε : ℝ} {ξ : Correspondence G}
    (hξ : D.IsCorrector (D.damp ε ξ)) (x : E) :
    D.lefschetzTrace x (D.damp ε ξ) = -D.primTrace x (D.damp ε ξ) :=
  D.lefschetzTrace_of_corrector hξ x

end ScalingDatum

/-! ### The damped orbit energy -/

section Energy

variable (Z : ZeroConfig) (hZ : TemperedConfig Z) (x : ScalingCycle)

/-- **The damped orbit energy** `E_x(ε) = sup_{t ≥ 0} e^{−εt}|c_x(t)| ∈ [0, ∞]`. -/
def dampedEnergy (ε : ℝ) : ℝ≥0∞ :=
  ⨆ t : ℝ, ⨆ (_ : 0 ≤ t),
    ENNReal.ofReal (Real.exp (-ε * t) * |(configScalingDatum Z hZ).orbitCorr x t|)

theorem le_dampedEnergy (ε : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (-ε * t) * |(configScalingDatum Z hZ).orbitCorr x t|) ≤
      dampedEnergy Z hZ x ε :=
  le_iSup₂_of_le t ht le_rfl

/-- The damped energy is at least the absolute value of the energy `c_x(0)`. -/
theorem ofReal_abs_orbitCorr_zero_le (ε : ℝ) :
    ENNReal.ofReal |(configScalingDatum Z hZ).orbitCorr x 0| ≤ dampedEnergy Z hZ x ε := by
  have h := le_dampedEnergy Z hZ x ε (le_refl 0)
  rwa [mul_zero, Real.exp_zero, one_mul] at h

/-- The damped energy is antitone in the damping. -/
theorem dampedEnergy_antitone : Antitone (dampedEnergy Z hZ x) := by
  intro ε ε' h
  refine iSup₂_le fun t ht => (ENNReal.ofReal_le_ofReal ?_).trans (le_dampedEnergy Z hZ x ε ht)
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _)

theorem dampedEnergy_le_ofReal {ε K : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → |(configScalingDatum Z hZ).orbitCorr x t| ≤ K * Real.exp (ε * t)) :
    dampedEnergy Z hZ x ε ≤ ENNReal.ofReal K := by
  refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_
  have he : Real.exp (-ε * t) * Real.exp (ε * t) = 1 := by
    rw [← Real.exp_add, show -ε * t + ε * t = 0 by ring, Real.exp_zero]
  calc Real.exp (-ε * t) * |(configScalingDatum Z hZ).orbitCorr x t|
      ≤ Real.exp (-ε * t) * (K * Real.exp (ε * t)) :=
        mul_le_mul_of_nonneg_left (h t ht) (Real.exp_pos _).le
    _ = K := by rw [mul_left_comm, he, mul_one]

/-- **Finite damped energy is a growth bound.** -/
theorem dampedEnergy_lt_top_iff (ε : ℝ) :
    dampedEnergy Z hZ x ε < ⊤ ↔
      ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → |(configScalingDatum Z hZ).orbitCorr x t| ≤ K * Real.exp (ε * t) := by
  constructor
  · intro hE
    refine ⟨(dampedEnergy Z hZ x ε).toReal, fun t ht => ?_⟩
    have h1 := (ENNReal.ofReal_le_iff_le_toReal hE.ne).mp (le_dampedEnergy Z hZ x ε ht)
    have he : Real.exp (ε * t) * Real.exp (-ε * t) = 1 := by
      rw [← Real.exp_add, show ε * t + -ε * t = 0 by ring, Real.exp_zero]
    calc |(configScalingDatum Z hZ).orbitCorr x t|
        = Real.exp (ε * t) * (Real.exp (-ε * t) * |(configScalingDatum Z hZ).orbitCorr x t|) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (ε * t) * (dampedEnergy Z hZ x ε).toReal :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  · rintro ⟨K, hK⟩
    exact (dampedEnergy_le_ofReal Z hZ x hK).trans_lt ENNReal.ofReal_lt_top

/-- On a symmetric tempered configuration the damped energy at `ε ≥ 0` is finite iff `x` is blind
above depth `ε`. -/
theorem dampedEnergy_lt_top_iff_blindAbove (hFE : FESymmetric Z) {ε : ℝ} (hε : 0 ≤ ε) :
    dampedEnergy Z hZ x ε < ⊤ ↔ BlindAbove Z ε x.2.2 := by
  rw [dampedEnergy_lt_top_iff, orbitCorr_rate_iff_blindAbove Z hZ hFE hε]

/-- Blindness above every positive depth is blindness to the off-line zeros. -/
theorem blindOffLine_of_forall_blindAbove {f : ℝ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → BlindAbove Z ε f) : BlindOffLine Z f := by
  rw [← blindAbove_zero_iff]
  intro ρ hρ hdeep
  exact h (|ρ.re - 1 / 2| / 2) (by linarith) ρ hρ (by linarith)

/-- An oriented cycle has damped energy exactly `c_x(0)` at every damping `ε ≥ 0`. -/
theorem dampedEnergy_eq_of_hasseWeil
    (h : ∀ t : ℝ, (configScalingDatum Z hZ).HasseWeilAt x t) {ε : ℝ} (hε : 0 ≤ ε) :
    dampedEnergy Z hZ x ε = ENNReal.ofReal ((configScalingDatum Z hZ).orbitCorr x 0) := by
  have hc0 : 0 ≤ (configScalingDatum Z hZ).orbitCorr x 0 := (abs_nonneg _).trans (h 0)
  refine le_antisymm (iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_) ?_
  · have he : Real.exp (-ε * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc Real.exp (-ε * t) * |(configScalingDatum Z hZ).orbitCorr x t|
        ≤ 1 * |(configScalingDatum Z hZ).orbitCorr x t| :=
          mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h t
  · have h0 := ofReal_abs_orbitCorr_zero_le Z hZ x ε
    rwa [abs_of_nonneg hc0] at h0

/-- **Relative to absolute without loss.** On a symmetric tempered configuration the following are
equivalent for a cycle `x`: it is oriented; its undamped energy is finite; its damped energy is
finite at every positive damping (constants arbitrary); its damped energy equals `c_x(0)` at every
damping `ε ≥ 0`. -/
theorem dampedEnergy_tfae (hFE : FESymmetric Z) :
    List.TFAE [∀ t : ℝ, (configScalingDatum Z hZ).HasseWeilAt x t,
      dampedEnergy Z hZ x 0 < ⊤,
      ∀ ε : ℝ, 0 < ε → dampedEnergy Z hZ x ε < ⊤,
      ∀ ε : ℝ, 0 ≤ ε →
        dampedEnergy Z hZ x ε = ENNReal.ofReal ((configScalingDatum Z hZ).orbitCorr x 0)] := by
  tfae_have 1 → 4 := fun h ε hε => dampedEnergy_eq_of_hasseWeil Z hZ x h hε
  tfae_have 4 → 2 := fun h => by rw [h 0 le_rfl]; exact ENNReal.ofReal_lt_top
  tfae_have 2 → 3 := fun h ε hε => (dampedEnergy_antitone Z hZ x hε.le).trans_lt h
  tfae_have 3 → 1 := fun h => by
    have hb : BlindOffLine Z x.2.2 := blindOffLine_of_forall_blindAbove Z fun ε hε =>
      (dampedEnergy_lt_top_iff_blindAbove Z hZ x hFE hε.le).mp (h ε hε)
    exact ((orientation_tfae Z hZ hFE x).out 0 2).mpr hb
  tfae_finish

/-- **For `ζ`**: for a spectrally generic real test, RH holds iff for every `ε > 0` there is `K`
with `|W(f, f(· − t))| ≤ K e^{εt}` for all `t ≥ 0`. -/
theorem riemannHypothesis_iff_forall_damped_bounded (x : ScalingCycle)
    (hgen : RealSpectrallyGeneric zetaZeroConfig x.2.2) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
      |zetaScalingDatum.orbitCorr x t| ≤ K * Real.exp (ε * t) := by
  have hT := dampedEnergy_tfae zetaZeroConfig temperedConfig_zetaZeroConfig x
    fesSymmetric_zetaZeroConfig
  rw [riemannHypothesis_iff_hasseWeil_of_generic x hgen]
  have h1 : (∀ t : ℝ, zetaScalingDatum.HasseWeilAt x t) ↔
      ∀ t : ℝ, (configScalingDatum zetaZeroConfig temperedConfig_zetaZeroConfig).HasseWeilAt x t :=
    forall_congr' fun t => zeta_hasseWeilAt_iff x t
  refine h1.trans ((hT.out 0 2).trans (forall₂_congr fun ε _ => ?_))
  rw [dampedEnergy_lt_top_iff]
  simp only [configScalingDatum_zeta_orbitCorr]

end Energy

end GaloisForLFunctions.ArithmeticOrientationGeometry
