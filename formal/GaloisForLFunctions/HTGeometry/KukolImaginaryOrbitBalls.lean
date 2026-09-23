import GaloisForLFunctions.HTGeometry.KukolUnipotentLorentz

/-!
# Explicit balls for imaginary unipotent orbit domains

Completing the square in Kukol, arXiv:2609.10214, Proposition 3.2 identifies
the imaginary orbit domain with an intersection of balls. Here every strict
future input is constructed in exponential coordinates, so positivity, a
positive radius and a nonempty orbit domain are proved without admission
premises. The description holds in arbitrary real inner-product spaces;
finite-dimensionality is not required for boundedness or connectedness.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive quadratic coefficient of an imaginary unipotent orbit. -/
def kukolOrbitCoefficient (r a : ℝ) : ℝ := (Real.exp r)^(2 : ℕ)+a^(2 : ℕ)

theorem kukolOrbitCoefficient_pos (r a : ℝ) : 0 < kukolOrbitCoefficient r a := by
  unfold kukolOrbitCoefficient
  positivity

/-- Linear drift of the imaginary orbit constraint. -/
def kukolOrbitDrift (r a : ℝ) (x z : E) : E := Real.exp r • x-a • z

/-- Completing the orbit quadratic determines its unique center. -/
def kukolOrbitCenter (r a : ℝ) (x z : E) : E :=
  (kukolOrbitCoefficient r a)⁻¹ • kukolOrbitDrift r a x z

/-- The positive squared radius of the admissible imaginary orbit. -/
def kukolOrbitRadiusSq (r s a : ℝ) (x z : E) : ℝ :=
  (Real.exp s + ‖kukolOrbitDrift r a x z‖^(2 : ℕ)/kukolOrbitCoefficient r a) /
    kukolOrbitCoefficient r a

theorem kukolOrbitRadiusSq_pos (r s a : ℝ) (x z : E) :
    0 < kukolOrbitRadiusSq r s a x z := by
  unfold kukolOrbitRadiusSq
  exact div_pos (add_pos_of_pos_of_nonneg (Real.exp_pos s)
    (div_nonneg (sq_nonneg _) (kukolOrbitCoefficient_pos r a).le))
      (kukolOrbitCoefficient_pos r a)

/-- Exact completion of the square, valid in every real inner-product space. -/
theorem kukolOrbit_complete_square (r a : ℝ) (B u : E) :
    kukolOrbitCoefficient r a * ‖u-(kukolOrbitCoefficient r a)⁻¹ • B‖^(2 : ℕ) =
      kukolOrbitCoefficient r a * ‖u‖^(2 : ℕ)-2*inner ℝ B u+‖B‖^(2 : ℕ)/kukolOrbitCoefficient r a := by
  have hA := (kukolOrbitCoefficient_pos r a).ne'
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real, real_inner_comm u B]
  field_simp
  ring

/-- Kukol's imaginary orbit slice is exactly an ordinary open ball. -/
theorem kukolImaginaryAction_ball_iff (u : E) (a b r s : ℝ) (x z : E) :
    kukolImaginaryAction u (a,b,x) (kukolStrictState r s z) ∈ kukolFuture ↔
      u ∈ Metric.ball (kukolOrbitCenter r a x z) (Real.sqrt (kukolOrbitRadiusSq r s a x z)) := by
  have hA := kukolOrbitCoefficient_pos r a
  have hcomplete := kukolOrbit_complete_square r a (kukolOrbitDrift r a x z) u
  have hdrift : inner ℝ (kukolOrbitDrift r a x z) u =
      Real.exp r * inner ℝ x u-a*inner ℝ z u := by
    simp [kukolOrbitDrift, inner_sub_left, inner_smul_left]
  simp only [kukolFuture, Set.mem_setOf_eq, kukolImaginaryAction, kukolStrictState,
    Real.exp_pos, true_and]
  change 0 < kukolQuadratic (kukolImaginaryAction u (a,b,x) (kukolStrictState r s z)) ↔ _
  rw [kukolQuadratic_imaginaryAction, kukolQuadratic_strictState]
  simp only [kukolStrictState]
  rw [Metric.mem_ball, dist_eq_norm, Real.lt_sqrt (norm_nonneg _)]
  unfold kukolOrbitRadiusSq kukolOrbitCenter
  rw [lt_div_iff₀ hA]
  rw [← hdrift]
  change 0 < Real.exp s + 2*inner ℝ (kukolOrbitDrift r a x z) u -
    kukolOrbitCoefficient r a*‖u‖^(2 : ℕ) ↔ _
  constructor <;> intro h <;> nlinarith [hcomplete]

/-- Strict future inputs produce nonempty imaginary orbit balls. -/
theorem kukolImaginaryAction_zero_future (a b r s : ℝ) (x z : E) :
    kukolImaginaryAction (0 : E) (a,b,x) (kukolStrictState r s z) ∈ kukolFuture := by
  simpa [kukolImaginaryAction] using kukolStrictState_mem_future r s z

/-- Every such orbit parameter domain is bounded, including infinite-dimensional carriers. -/
theorem kukolImaginaryAction_bounded (a b r s : ℝ) (x z : E) :
    Bornology.IsBounded {u : E |
      kukolImaginaryAction u (a,b,x) (kukolStrictState r s z) ∈ kukolFuture} := by
  have he : {u : E | kukolImaginaryAction u (a,b,x) (kukolStrictState r s z) ∈ kukolFuture} =
      Metric.ball (kukolOrbitCenter r a x z) (Real.sqrt (kukolOrbitRadiusSq r s a x z)) := by
    ext u
    exact kukolImaginaryAction_ball_iff u a b r s x z
  rw [he]
  exact Metric.isBounded_ball

/-- Simultaneous strict future inputs always leave a connected admissible parameter set. -/
theorem kukolImaginaryAction_strict_family_connected {ι : Type*}
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) :
    IsConnected {u : E | ∀ i, kukolImaginaryAction u (v i) (kukolStrictState (r i) (s i) (z i))
      ∈ kukolFuture} := by
  refine ⟨⟨0, ?_⟩, kukolImaginaryAction_family_preconnected v
    (fun i => kukolStrictState (r i) (s i) (z i))⟩
  intro i
  exact kukolImaginaryAction_zero_future (v i).1 (v i).2.1 (r i) (s i) (v i).2.2 (z i)

end GaloisForLFunctions.HTGeometry
