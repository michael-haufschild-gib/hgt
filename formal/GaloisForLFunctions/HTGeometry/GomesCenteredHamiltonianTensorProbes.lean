import GaloisForLFunctions.HTGeometry.GomesFinitePolynomialEnergyRigidity

/-!
# Quadratic tensor probes restore energy-independent reconstruction

The common-base tensor-composition idea in arXiv:2509.25276v7 section 5.2 exposes
a reconstruction boundary in this scalar model. After discarding each scalar energy
reference, all affine probes remain blind to affine profile slopes. One quadratic probe
restores the full first-order connection, and one origin value restores the profile.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Tensoring profiles on the same base adds their potentials and the exact drift cross term. -/
theorem gomesDilatonPotential_tensor_add (H K : ℝ[X]) (x : ℝ) :
    dilatonPotential (H + K) x = dilatonPotential H x + dilatonPotential K x +
      H.derivative.eval x * K.derivative.eval x / 2 := by
  simp only [dilatonPotential, derivative_add, eval_add]
  ring

/-- Energy centering retains the variable part of the tensor cross term exactly. -/
theorem gomesDilatonCenteredPotential_tensor_add (H K : ℝ[X]) (x : ℝ) :
    gomesDilatonCenteredPotential (H + K) x =
      gomesDilatonCenteredPotential H x + gomesDilatonCenteredPotential K x +
        (H.derivative.eval x * K.derivative.eval x -
          H.derivative.eval 0 * K.derivative.eval 0) / 2 := by
  unfold gomesDilatonCenteredPotential
  rw [gomesDilatonPotential_tensor_add, gomesDilatonPotential_tensor_add]
  ring

/-- Constant profile amplitude remains invisible after energy centering. -/
theorem gomesDilatonCenteredPotential_constant (H : ℝ[X]) (c : ℝ) :
    gomesDilatonCenteredPotential (H + C c) = gomesDilatonCenteredPotential H := by
  funext x
  simp [gomesDilatonCenteredPotential, dilatonPotential]

/-- Every affine profile has the same vanishing energy-independent potential. -/
theorem gomesDilatonCenteredPotential_affine (a b : ℝ) :
    gomesDilatonCenteredPotential (C a * X + C b) = 0 := by
  funext x
  simp only [gomesDilatonCenteredPotential, gomesDilatonPotential_affine, sub_self, Pi.zero_apply]

/-- No common affine tensor probe can distinguish two affine profiles after energy centering. -/
theorem gomesDilatonCenteredPotential_affine_probes_blind (a b c d r s : ℝ) :
    gomesDilatonCenteredPotential ((C a * X + C b) + (C r * X + C s)) =
      gomesDilatonCenteredPotential ((C c * X + C d) + (C r * X + C s)) := by
  have h (u v : ℝ) : (C u * X + C v : ℝ[X]) + (C r * X + C s) =
      C (u + r) * X + C (v + s) := by
    simp only [map_add]
    ring
  rw [h, h, gomesDilatonCenteredPotential_affine, gomesDilatonCenteredPotential_affine]

/-- A fixed quadratic tensor probe restores all first-order connection information. -/
theorem gomesDilatonCenteredPotential_quadratic_probe_iff (H K : ℝ[X]) :
    (gomesDilatonCenteredPotential H = gomesDilatonCenteredPotential K ∧
      gomesDilatonCenteredPotential (H + X ^ 2) =
        gomesDilatonCenteredPotential (K + X ^ 2)) ↔
          dilatonSuperchargeCLM H = dilatonSuperchargeCLM K := by
  constructor
  · rintro ⟨hb, hp⟩
    apply (gomesDilatonConnection_eq_iff H K).mpr
    have hproduct : (H.derivative - K.derivative) * X = 0 := by
      apply Polynomial.funext
      intro x
      have hx := congrFun hb x
      have ht := congrFun hp x
      rw [gomesDilatonCenteredPotential_tensor_add, gomesDilatonCenteredPotential_tensor_add] at ht
      simp only [pow_two, derivative_mul, derivative_X, one_mul, mul_one,
        eval_add, eval_X, add_zero, mul_zero] at ht
      simp only [eval_mul, eval_sub, eval_X, eval_zero]
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right X_ne_zero)
  · intro h
    obtain ⟨c, hc⟩ := (gomesDilatonConnection_constant_iff H K).mp h
    constructor
    · rw [hc, gomesDilatonCenteredPotential_constant]
    · have hs : H + X ^ 2 = (K + X ^ 2) + C c := by rw [hc]; ring
      rw [hs, gomesDilatonCenteredPotential_constant]

/-- All energy-independent tensor-context observations contain exactly the connection information. -/
theorem gomesDilatonCenteredPotential_all_tensor_contexts_iff (H K : ℝ[X]) :
    (∀ R : ℝ[X], gomesDilatonCenteredPotential (H + R) =
      gomesDilatonCenteredPotential (K + R)) ↔
        dilatonSuperchargeCLM H = dilatonSuperchargeCLM K := by
  constructor
  · intro h
    apply (gomesDilatonCenteredPotential_quadratic_probe_iff H K).mp
    exact ⟨by simpa only [add_zero] using h 0, h (X ^ 2)⟩
  · intro h R
    obtain ⟨c, hc⟩ := (gomesDilatonConnection_constant_iff H K).mp h
    have hs : H + R = (K + R) + C c := by rw [hc]; ring
    rw [hs, gomesDilatonCenteredPotential_constant]

/-- Two energy-independent potential observations, before and after the fixed quadratic probe. -/
def gomesDilatonCenteredTensorRecord (H : ℝ[X]) : (ℝ → ℝ) × (ℝ → ℝ) :=
  (gomesDilatonCenteredPotential H, gomesDilatonCenteredPotential (H + X ^ 2))

/-- The quadratic-probe record forgets only the constant log-amplitude. -/
theorem gomesDilatonCenteredTensorRecord_eq_iff (H K : ℝ[X]) :
    gomesDilatonCenteredTensorRecord H = gomesDilatonCenteredTensorRecord K ↔
      ∃ c : ℝ, H = K + C c := by
  rw [gomesDilatonCenteredTensorRecord, gomesDilatonCenteredTensorRecord, Prod.mk.injEq,
    gomesDilatonCenteredPotential_quadratic_probe_iff, gomesDilatonConnection_constant_iff]

/-- One origin value restores exact recovery from the energy-independent tensor record. -/
theorem gomesDilatonCenteredTensorRecord_origin_iff (H K : ℝ[X]) :
    (gomesDilatonCenteredTensorRecord H = gomesDilatonCenteredTensorRecord K ∧
      H.eval 0 = K.eval 0) ↔ H = K := by
  rw [gomesDilatonCenteredTensorRecord_eq_iff, ← gomesDilatonConnection_constant_iff,
    gomesDilatonConnection_origin_iff]

/-- The augmented quadratic-probe observation embeds every real polynomial profile faithfully. -/
theorem gomesDilatonCenteredTensorRecord_augmented_injective :
    Function.Injective (fun H : ℝ[X] => (gomesDilatonCenteredTensorRecord H, H.eval 0)) := by
  intro H K h
  exact (gomesDilatonCenteredTensorRecord_origin_iff H K).mp (Prod.mk.inj h)

end GaloisForLFunctions.HTGeometry
