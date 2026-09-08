import GaloisForLFunctions.HTGeometry.TorusTrigPolynomial

/-!
# Torus angular selection with internal spectators

The angular/physical tensor separation in §3 of arXiv:2608.29825 applies to the
corpus's product-torus harmonics. Here its exact abelian angular coefficient is
frequency addition. Finite physical tensors and the existing trigonometric
polynomials inherit an exact sparse contraction law. This is a torus analogue,
not an identification with the paper's SO(3) Wigner coefficients.
-/

open Complex Set MeasureTheory
attribute [local instance] instMeasureSpaceUnitAddCircle

namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {d : Type} [Fintype d] [DecidableEq d]

/-- The actual triple-character Haar integral. -/
def torusCollisionAngular (k m n : d → ℤ) : ℂ :=
  ∫ x : UnitAddTorus d,
    UnitAddTorus.mFourier (-k) x *
      (UnitAddTorus.mFourier m x * UnitAddTorus.mFourier n x)

/-- Haar averaging admits precisely the output frequency equal to the input sum. -/
theorem torusCollisionAngular_selection (k m n : d → ℤ) :
    torusCollisionAngular k m n = if k = m + n then 1 else 0 := by
  simpa only [torusCollisionAngular, UnitAddTorus.mFourierCoeff, smul_eq_mul,
    UnitAddTorus.mFourier_add] using mFourierCoeff_mFourier (m + n) k

/-- A physical coefficient independent of angle factors out of the Haar tensor. -/
theorem torusCollision_spectator (k m n : d → ℤ) (b : ℂ) :
    (∫ x : UnitAddTorus d, b * (UnitAddTorus.mFourier (-k) x *
      (UnitAddTorus.mFourier m x * UnitAddTorus.mFourier n x))) =
      if k = m + n then b else 0 := by
  rw [integral_const_mul, ← torusCollisionAngular, torusCollisionAngular_selection]
  split <;> simp_all

/-- Gain and loss use the same angular selection coefficient. -/
theorem torusCollision_gain_loss (k m n : d → ℤ) (gain loss : ℂ) :
    torusCollisionAngular k m n * gain - torusCollisionAngular k m n * loss =
      if k = m + n then gain - loss else 0 := by
  rw [torusCollisionAngular_selection]
  split <;> simp_all

/-- Finite internal coupling tensor evaluated on the actual angular harmonics. -/
def torusCollisionPacket (s t : Finset (d → ℤ))
    (B : (d → ℤ) → (d → ℤ) → ℂ) (x : UnitAddTorus d) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ t, B m n *
    (UnitAddTorus.mFourier m x * UnitAddTorus.mFourier n x)

/-- An arbitrary finite physical tensor contracts only over frequency-matching pairs. -/
theorem torusCollisionPacket_coefficient (s t : Finset (d → ℤ))
    (B : (d → ℤ) → (d → ℤ) → ℂ) (k : d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusCollisionPacket s t B) k =
      ∑ m ∈ s, ∑ n ∈ t, if k = m + n then B m n else 0 := by
  classical
  have hsplit : (fun x : UnitAddTorus d => UnitAddTorus.mFourier (-k) x •
      torusCollisionPacket s t B x) = fun x => ∑ m ∈ s, ∑ n ∈ t,
        B m n * (UnitAddTorus.mFourier (-k) x *
          (UnitAddTorus.mFourier m x * UnitAddTorus.mFourier n x)) := by
    funext x
    simp only [torusCollisionPacket, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hi (m n : d → ℤ) : Integrable (fun x : UnitAddTorus d =>
      B m n * (UnitAddTorus.mFourier (-k) x *
        (UnitAddTorus.mFourier m x * UnitAddTorus.mFourier n x))) :=
    integrable_torus_of_continuous (continuous_const.mul
      ((UnitAddTorus.mFourier (-k)).continuous.mul
        ((UnitAddTorus.mFourier m).continuous.mul (UnitAddTorus.mFourier n).continuous)))
  rw [UnitAddTorus.mFourierCoeff, hsplit,
    integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => hi m n))]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_finsetSum _ (fun n _ => hi m n)]
  exact Finset.sum_congr rfl (fun n _ => torusCollision_spectator k m n (B m n))

omit [DecidableEq d] in
/-- Multiplying the corpus's trigonometric polynomials is an exact collision packet. -/
theorem torusTrigPoly_mul_eq_collisionPacket
    (p q : (d → ℤ) →₀ ℂ) (x : UnitAddTorus d) :
    torusTrigPoly p x * torusTrigPoly q x =
      torusCollisionPacket p.support q.support (fun m n => p m * q n) x := by
  classical
  simp only [torusTrigPoly, torusCollisionPacket, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The quadratic Fourier response has no contributions outside the input sumset. -/
theorem torusTrigPoly_product_coefficient
    (p q : (d → ℤ) →₀ ℂ) (k : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => torusTrigPoly p x * torusTrigPoly q x) k =
      ∑ m ∈ p.support, ∑ n ∈ q.support, if k = m + n then p m * q n else 0 := by
  simp_rw [torusTrigPoly_mul_eq_collisionPacket]
  exact torusCollisionPacket_coefficient _ _ _ _

end
end GaloisForLFunctions.HTGeometry
