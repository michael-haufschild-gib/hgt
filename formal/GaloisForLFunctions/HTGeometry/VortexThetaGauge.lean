import GaloisForLFunctions.HTGeometry.GammaGerbeThetaCocycle

/-!
# Theta large-gauge multipliers and charge balance

The gauge transformations in arXiv:2609.09298, Sections 2.2 and 2.7, can be read directly
on the corpus's existing Jacobi theta cocycles. A charge-l mode has quadratic multiplier;
a degree-d charged block has d*l modes and hence cubic coefficient d*l^(3 : ℕ). A balanced
four-theta quotient has both periods exactly, including its totalized values at zeros.
-/

open Complex Finset
namespace GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.GerbeCharacteristic
noncomputable section
local notation "Ⅱ" => (2 * (Real.pi : ℂ) * Complex.I)

/-- `N` theta modes of an integral gauge charge. -/
def vortexJacobiBlock (τ u : ℂ) (N : ℕ) (l : ℤ) (z : ℂ) : ℂ :=
  thetaProd (fun w => jacobiTheta₂ w τ) u N ((l : ℂ) * z)

/-- The gauge multiplier has quadratic charge dependence for each individual mode. -/
theorem vortexJacobiBlock_large_gauge (τ u : ℂ) (N : ℕ) (l : ℤ) (z : ℂ) :
    vortexJacobiBlock τ u N l (z + τ) =
      Complex.exp (-Ⅱ * ((N : ℂ) * (l : ℂ) ^ (2 : ℕ) * (z + τ / 2) +
        (l : ℂ) * u * ((N : ℂ) * ((N : ℂ) - 1) / 2))) *
          vortexJacobiBlock τ u N l z := by
  have h := thetaProd_shift (θ := fun w => jacobiTheta₂ w τ)
    (τ := τ) (κ := -(τ / 2)) (jacobiTheta₂_add_one τ) (jacobiTheta₂_add_tau τ)
    u N l 0 ((l : ℂ) * z)
  have hleft : vortexJacobiBlock τ u N l (z + τ) =
      ∏ i ∈ Finset.range N,
        jacobiTheta₂ ((l : ℂ) * z + (i : ℂ) * u + (l : ℂ) * τ + (0 : ℤ)) τ := by
    unfold vortexJacobiBlock thetaProd
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    push_cast
    ring
  rw [hleft, h]
  congr 2
  ring

/-- A degree-`d` field of charge magnitude `l` has `d*l` modes, turning the quadratic
single-mode multiplier into the cubic coefficient `d*l^(3 : ℕ)`. -/
theorem vortexJacobiBlock_cubic_charge (τ u : ℂ) (d l : ℕ) (z : ℂ) :
    vortexJacobiBlock τ u (d * l) (l : ℤ) (z + τ) =
      Complex.exp (-Ⅱ * ((d : ℂ) * (l : ℂ) ^ (3 : ℕ) * (z + τ / 2) +
        (l : ℂ) * u * (((d : ℂ) * l) * ((d : ℂ) * l - 1) / 2))) *
          vortexJacobiBlock τ u (d * l) (l : ℤ) z := by
  rw [vortexJacobiBlock_large_gauge]
  congr 2
  push_cast
  ring

/-- Four theta factors with balanced translation parameters. -/
def vortexBalancedThetaRatio (τ a b c z : ℂ) : ℂ :=
  (jacobiTheta₂ (z + a) τ * jacobiTheta₂ (z + b) τ) /
    (jacobiTheta₂ (z + c) τ * jacobiTheta₂ (z + (a + b - c)) τ)

theorem vortexBalancedThetaRatio_period_one (τ a b c z : ℂ) :
    vortexBalancedThetaRatio τ a b c (z + 1) = vortexBalancedThetaRatio τ a b c z := by
  unfold vortexBalancedThetaRatio
  have h (w : ℂ) : z + 1 + w = (z + w) + 1 := by ring
  simp only [h, jacobiTheta₂_add_one]

/-- Equal quadratic degree and balanced flavor shifts cancel the full large-gauge multiplier.
The equation also holds at zeros, using Lean's total division. -/
theorem vortexBalancedThetaRatio_period_tau (τ a b c z : ℂ) :
    vortexBalancedThetaRatio τ a b c (z + τ) = vortexBalancedThetaRatio τ a b c z := by
  unfold vortexBalancedThetaRatio
  have h (w : ℂ) : z + τ + w = (z + w) + τ := by ring
  simp only [h, jacobiTheta₂_add_tau]
  have hm (A B C D : ℂ) : (Complex.exp A * B) * (Complex.exp C * D) =
      Complex.exp (A + C) * (B * D) := by rw [Complex.exp_add]; ring
  simp only [hm]
  have he : Ⅱ * (-(τ / 2) - (z + a)) + Ⅱ * (-(τ / 2) - (z + b)) =
      Ⅱ * (-(τ / 2) - (z + c)) + Ⅱ * (-(τ / 2) - (z + (a + b - c))) := by ring
  rw [he]
  exact mul_div_mul_left _ _ (Complex.exp_ne_zero _)

/-- The balanced quotient descends through every integral large gauge transformation. -/
theorem vortexBalancedThetaRatio_lattice (τ a b c z : ℂ) (k j : ℤ) :
    vortexBalancedThetaRatio τ a b c (z + (k : ℂ) * τ + j) =
      vortexBalancedThetaRatio τ a b c z := by
  have ht : Function.Periodic (vortexBalancedThetaRatio τ a b c) τ :=
    vortexBalancedThetaRatio_period_tau τ a b c
  have ho : Function.Periodic (vortexBalancedThetaRatio τ a b c) 1 :=
    vortexBalancedThetaRatio_period_one τ a b c
  rw [show (j : ℂ) = (j : ℂ) * 1 by ring]
  rw [(ho.int_mul j) (z + (k : ℂ) * τ), (ht.int_mul k) z]

end
end GaloisForLFunctions.HTGeometry
