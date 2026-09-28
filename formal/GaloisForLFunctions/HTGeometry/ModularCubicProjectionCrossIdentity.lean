import GaloisForLFunctions.HTGeometry.ModularCubicProjectionTransgression

/-!
# Projection cross identity and ordinary-trace erasure of the cubic transgression

Two statements of the modular cubic projection transgression law (MCPT) used inside
`ModularCubicProjectionTransgression` but not exported there:

* (MCPT.3) for idempotents `r, q, p` and `a = r - q`, `b = q - p`:
  `a² b + a b² = [a b, q]`;
* ordinary trace (`σ = id`) erases the modular anomaly: `M₃_id(r, q, p) = 0`, hence every
  ordinary trace kills the cubic projection associator.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A G : Type*} [Ring A] [AddCommGroup G]

/-- **(MCPT.3)** Projection cross identity. -/
theorem projection_cross_eq_modularCommutator
    (r q p : A) (hr : r * r = r) (hq : q * q = q) (hp : p * p = p) :
    (r - q) ^ (2 : ℕ) * (q - p) + (r - q) * (q - p) ^ (2 : ℕ) =
      modularCommutator ((r - q) * (q - p)) q := by
  have hqqp : q * (q * p) = q * p := by rw [← mul_assoc, hq]
  simp only [modularCommutator]
  noncomm_ring [hr, hq, hp, hqqp]

/-- The ordinary (untwisted) modular anomaly vanishes identically. -/
@[simp] theorem cubicProjectionModularAnomaly_id (r q p : A) :
    cubicProjectionModularAnomaly (RingHom.id A) r q p = 0 :=
  cubicProjectionModularAnomaly_eq_zero_of_fixed _ r q p rfl rfl rfl

/-- **Ordinary trace erases the transgression:** every tracial functional (`τ(xy) = τ(yx)`)
annihilates the cubic projection associator of three idempotents. -/
theorem tracial_map_cubicProjectionAssociatorAlgebra_eq_zero
    (tau : A →+ G) (htau : ∀ x y : A, tau (x * y) = tau (y * x))
    (r q p : A) (hr : r * r = r) (hq : q * q = q) (hp : p * p = p) :
    tau (cubicProjectionAssociatorAlgebra r q p) = 0 := by
  have h : IsSigmaTrace (RingHom.id A) tau := fun x y => htau x y
  rw [h.map_cubicProjectionAssociatorAlgebra r q p hr hq hp,
    cubicProjectionModularAnomaly_id, map_zero]

end GaloisForLFunctions.HTGeometry
