import GaloisForLFunctions.HTGeometry.GomesCenteredHamiltonianTensorProbes

/-!
# Exact choice of energy-centered reconstruction probes

The common-base tensor observation from the Gomes scalar experiment admits a minimal
probe criterion: nonzero second derivative is necessary and sufficient for universal
connection reconstruction. The proof extracts a constant polynomial product from the
two observations and uses degree rigidity to eliminate its nonconstant factor.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A polynomial product is constant exactly when a factor vanishes or both factors are constant. -/
theorem gomesPolynomial_product_derivative_zero_iff (A B : ℝ[X]) :
    (A * B).derivative = 0 ↔ A = 0 ∨ B = 0 ∨ (A.derivative = 0 ∧ B.derivative = 0) := by
  by_cases ha : A = 0
  · simp [ha]
  by_cases hb : B = 0
  · simp [hb]
  simp only [ha, hb, false_or, derivative_eq_zero, natDegree_mul ha hb, Nat.add_eq_zero_iff]

/-- Equal centered observations before and after a probe are exactly a constant cross-term condition. -/
theorem gomesDilatonCenteredPotential_probe_cross_term_iff (H K R : ℝ[X]) :
    (gomesDilatonCenteredPotential H = gomesDilatonCenteredPotential K ∧
      gomesDilatonCenteredPotential (H + R) = gomesDilatonCenteredPotential (K + R)) ↔
        gomesDilatonCenteredPotential H = gomesDilatonCenteredPotential K ∧
          ((H.derivative - K.derivative) * R.derivative).derivative = 0 := by
  constructor
  · rintro ⟨hb, ht⟩
    refine ⟨hb, ?_⟩
    have hp : (H.derivative - K.derivative) * R.derivative =
        C ((H.derivative.eval 0 - K.derivative.eval 0) * R.derivative.eval 0) := by
      apply Polynomial.funext
      intro x
      have hb' := congrFun hb x
      have ht' := congrFun ht x
      rw [gomesDilatonCenteredPotential_tensor_add,
        gomesDilatonCenteredPotential_tensor_add] at ht'
      simp only [eval_mul, eval_sub, eval_C]
      nlinarith
    rw [hp, derivative_C]
  · rintro ⟨hb, hd⟩
    refine ⟨hb, ?_⟩
    have hp := eq_C_of_derivative_eq_zero hd
    have hx (x : ℝ) := congrArg (Polynomial.eval x) hp
    funext x
    rw [gomesDilatonCenteredPotential_tensor_add,
      gomesDilatonCenteredPotential_tensor_add]
    have hb' := congrFun hb x
    have h0 := hx 0
    have hh := hx x
    simp only [eval_mul, eval_sub, eval_C] at h0 hh
    nlinarith

/-- Every non-affine polynomial probe restores all connection information after energy centering. -/
theorem gomesDilatonCenteredPotential_nonaffine_probe_iff
    (R : {R : ℝ[X] // R.derivative.derivative ≠ 0}) (H K : ℝ[X]) :
    (gomesDilatonCenteredPotential H = gomesDilatonCenteredPotential K ∧
      gomesDilatonCenteredPotential (H + R.val) = gomesDilatonCenteredPotential (K + R.val)) ↔
        dilatonSuperchargeCLM H = dilatonSuperchargeCLM K := by
  rw [gomesDilatonCenteredPotential_probe_cross_term_iff,
    gomesPolynomial_product_derivative_zero_iff]
  constructor
  · rintro ⟨_, h⟩
    apply (gomesDilatonConnection_eq_iff H K).mpr
    rcases h with hz | hz | ⟨_, hz⟩
    · exact sub_eq_zero.mp hz
    · exact False.elim (R.property (by rw [hz, derivative_zero]))
    · exact False.elim (R.property hz)
  · intro h
    have hd := (gomesDilatonConnection_eq_iff H K).mp h
    have hb := ((gomesDilatonCenteredPotential_quadratic_probe_iff H K).mpr h).1
    exact ⟨hb, Or.inl (sub_eq_zero.mpr hd)⟩

/-- A freely chosen polynomial probe together with the unperturbed centered observation. -/
def gomesDilatonCenteredProbeRecord (R H : ℝ[X]) : (ℝ → ℝ) × (ℝ → ℝ) :=
  (gomesDilatonCenteredPotential H, gomesDilatonCenteredPotential (H + R))

/-- Non-affine probe records have exactly the constant-amplitude fibers. -/
theorem gomesDilatonCenteredProbeRecord_nonaffine_fibers
    (R : {R : ℝ[X] // R.derivative.derivative ≠ 0}) (H K : ℝ[X]) :
    gomesDilatonCenteredProbeRecord R.val H = gomesDilatonCenteredProbeRecord R.val K ↔
      ∃ c : ℝ, H = K + C c := by
  rw [gomesDilatonCenteredProbeRecord, gomesDilatonCenteredProbeRecord, Prod.mk.injEq,
    gomesDilatonCenteredPotential_nonaffine_probe_iff, gomesDilatonConnection_constant_iff]

/-- Adding one origin value to any non-affine probe makes profile reconstruction injective. -/
theorem gomesDilatonCenteredProbeRecord_nonaffine_augmented_injective
    (R : {R : ℝ[X] // R.derivative.derivative ≠ 0}) :
    Function.Injective (fun H : ℝ[X] => (gomesDilatonCenteredProbeRecord R.val H, H.eval 0)) := by
  intro H K h
  have hh := Prod.mk.inj h
  have hc := (gomesDilatonCenteredProbeRecord_nonaffine_fibers R H K).mp hh.1
  apply (gomesDilatonConnection_origin_iff H K).mp
  exact ⟨(gomesDilatonConnection_constant_iff H K).mpr hc, hh.2⟩

/-- The two fixed profiles zero and X collide under precisely the affine probes. -/
theorem gomesDilatonCenteredProbeRecord_zero_X_iff (R : ℝ[X]) :
    gomesDilatonCenteredProbeRecord R 0 = gomesDilatonCenteredProbeRecord R X ↔
      R.derivative.derivative = 0 := by
  rw [gomesDilatonCenteredProbeRecord, gomesDilatonCenteredProbeRecord, Prod.mk.injEq,
    gomesDilatonCenteredPotential_probe_cross_term_iff]
  have hb : gomesDilatonCenteredPotential 0 = gomesDilatonCenteredPotential X := by
    funext x
    simp [gomesDilatonCenteredPotential, dilatonPotential]
  simp only [hb, true_and, derivative_zero, derivative_X, zero_sub, neg_mul, one_mul,
    derivative_neg, neg_eq_zero]

/-- Nonzero probe curvature is both necessary and sufficient for universal connection recovery. -/
theorem gomesDilatonCenteredProbeRecord_universal_iff (R : ℝ[X]) :
    (∀ H K : ℝ[X], gomesDilatonCenteredProbeRecord R H = gomesDilatonCenteredProbeRecord R K ↔
      dilatonSuperchargeCLM H = dilatonSuperchargeCLM K) ↔
        R.derivative.derivative ≠ 0 := by
  constructor
  · intro h hz
    have hc := (h 0 X).mp ((gomesDilatonCenteredProbeRecord_zero_X_iff R).mpr hz)
    have hd := (gomesDilatonConnection_eq_iff 0 X).mp hc
    exact zero_ne_one (by simpa only [derivative_zero, derivative_X] using hd)
  · intro h H K
    rw [gomesDilatonCenteredProbeRecord, gomesDilatonCenteredProbeRecord, Prod.mk.injEq]
    exact gomesDilatonCenteredPotential_nonaffine_probe_iff ⟨R, h⟩ H K

/-- Origin-augmented reconstruction is injective exactly for the non-affine probes. -/
theorem gomesDilatonCenteredProbeRecord_augmented_injective_iff (R : ℝ[X]) :
    Function.Injective (fun H : ℝ[X] => (gomesDilatonCenteredProbeRecord R H, H.eval 0)) ↔
      R.derivative.derivative ≠ 0 := by
  constructor
  · intro hi hz
    have he : (0 : ℝ[X]) = X := hi (Prod.ext
      ((gomesDilatonCenteredProbeRecord_zero_X_iff R).mpr hz) (by simp))
    exact X_ne_zero he.symm
  · intro h
    exact gomesDilatonCenteredProbeRecord_nonaffine_augmented_injective ⟨R, h⟩

end GaloisForLFunctions.HTGeometry
