import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeHeckeAdjointAction

/-!
# The multiplicative Weyl discriminant on probe sectors

Braverman–Kazhdan (arXiv:2610.17317, §5.4) use the determinant of
one minus conjugation transverse to a torus. On the probe reflection
hull the two transverse characters are -q² and -q⁻². Their Weyl
factor acts on every observable through its sector-exchanging part.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})
local notation "A" => Module.End ℂ (reflectionHull p)

/-- Multiplicative adjoint action at every invertible Hecke parameter. -/
def hullHeckeConjugation (q : ℂ) (X : A) : A := hullHecke p q * X * hullHecke p q⁻¹

private theorem hecke_pos_left (q : ℂ) :
    hullHecke p q * hullPositive p = q^2 • hullPositive p := by
  have hp : hullPositive p * hullPositive p = hullPositive p := hullPositive_idempotent p
  rw [hullHecke, sub_mul, smul_mul_assoc, hp,
    hullNegative_mul_hullPositive, sub_zero]

private theorem hecke_pos_right (q : ℂ) :
    hullPositive p * hullHecke p q = q^2 • hullPositive p := by
  have hp : hullPositive p * hullPositive p = hullPositive p := hullPositive_idempotent p
  rw [hullHecke, mul_sub, mul_smul_comm, hp,
    hullPositive_mul_hullNegative, sub_zero]

private theorem hecke_neg_left (q : ℂ) :
    hullHecke p q * hullNegative p = -hullNegative p := by
  have hn : hullNegative p * hullNegative p = hullNegative p := hullNegative_idempotent p
  rw [hullHecke, sub_mul, smul_mul_assoc, hullPositive_mul_hullNegative,
    smul_zero, zero_sub, hn]

private theorem hecke_neg_right (q : ℂ) :
    hullNegative p * hullHecke p q = -hullNegative p := by
  have hn : hullNegative p * hullNegative p = hullNegative p := hullNegative_idempotent p
  rw [hullHecke, mul_sub, mul_smul_comm, hullNegative_mul_hullPositive,
    smul_zero, zero_sub, hn]

/-- Inverse parameters realize inverse Hecke elements on every hull. -/
theorem hullHecke_inverse (q : ℂ) (hq : q ≠ 0) : hullHecke p q * hullHecke p q⁻¹ = 1 := by
  calc
    hullHecke p q * hullHecke p q⁻¹ =
      (q⁻¹)^2 • (hullHecke p q * hullPositive p) - hullHecke p q * hullNegative p := by
        change hullHecke p q * ((q⁻¹)^2 • hullPositive p - hullNegative p) = _
        rw [mul_sub, mul_smul_comm]
    _ = 1 := by
      rw [hecke_pos_left, hecke_neg_left, smul_smul, ← mul_pow, inv_mul_cancel₀ hq,
        one_pow, one_smul, sub_neg_eq_add, hullPositive_add_hullNegative]

/-- The two off-diagonal blocks carry reciprocal torus characters. -/
theorem hullHeckeConjugation_mixed_weights (q : ℂ) (X : A) :
    hullHeckeConjugation p q (hullPositive p * X * hullNegative p) =
        -(q^2) • (hullPositive p * X * hullNegative p) ∧
      hullHeckeConjugation p q (hullNegative p * X * hullPositive p) =
        -((q⁻¹)^2) • (hullNegative p * X * hullPositive p) := by
  have reassoc (a b x c d : A) : a * (b*x*c) * d = (a*b)*x*(c*d) := by
    simp only [mul_assoc]
  constructor
  · rw [hullHeckeConjugation, reassoc, hecke_pos_left, hecke_neg_right,
      mul_neg (q^2 • hullPositive p * X) (hullNegative p), smul_mul_assoc, smul_mul_assoc]
    exact (neg_smul (q^2) (hullPositive p * X * hullNegative p)).symm
  · rw [hullHeckeConjugation, reassoc, hecke_neg_left, hecke_pos_right,
      neg_mul (hullNegative p) X, neg_mul (hullNegative p * X) ((q⁻¹)^2 • hullPositive p),
      mul_smul_comm]
    exact (neg_smul ((q⁻¹)^2) (hullNegative p * X * hullPositive p)).symm

/-- Every mixed observable is exactly the sum of its two oriented off-diagonal blocks. -/
theorem hullMixedPart_blocks (X : A) :
    hullMixedPart p X = hullPositive p * X * hullNegative p + hullNegative p * X * hullPositive p := by
  simp only [hullMixedPart, hullPositive, hullNegative, smul_mul_assoc, mul_smul_comm, add_mul,
    sub_mul, mul_add, mul_sub, one_mul, mul_one, smul_add, smul_sub, smul_smul]
  module

/-- The multiplicative adjoint fixes precisely the commutant of the Hecke element. -/
theorem hullHeckeConjugation_fixed_iff (q : ℂ) (hq : q ≠ 0) (X : A) :
    hullHeckeConjugation p q X = X ↔ Commute (hullHecke p q) X := by
  have hr : hullHecke p q⁻¹ * hullHecke p q = 1 := by
    simpa only [inv_inv] using hullHecke_inverse p q⁻¹ (inv_ne_zero hq)
  constructor
  · intro h
    have he := congrArg (fun Y : A => Y * hullHecke p q) h
    change hullHecke p q * X * hullHecke p q⁻¹ * hullHecke p q = _ at he
    rwa [mul_assoc (hullHecke p q * X), hr, mul_one] at he
  · intro h
    rw [hullHeckeConjugation, h.eq, mul_assoc, hullHecke_inverse p q hq, mul_one]

private theorem inverse_commutator (q : ℂ) (hq : q ≠ 0) (X : A) :
    hullHeckeCommutator p q⁻¹ X = (q^2)⁻¹ • hullHeckeCommutator p q X := by
  have h : ((q⁻¹)^2+1)/2 = (q^2)⁻¹*((q^2+1)/2) := by field_simp [hq]; ring
  rw [hullHeckeCommutator_eq, hullHeckeCommutator_eq, h, mul_smul]

/-- The symmetric difference of conjugations is the Weyl factor times the mixed projection. -/
theorem hullHeckeWeyl_discriminant (q : ℂ) (hq : q ≠ 0) (X : A) :
    (X - hullHeckeConjugation p q X) - (hullHeckeConjugation p q⁻¹ X - X) =
      ((q^2)⁻¹ * (q^2+1)^2) • hullMixedPart p X := by
  let T := hullHecke p q
  let U := hullHecke p q⁻¹
  have hTU : T*U = 1 := hullHecke_inverse p q hq
  have hUT : U*T = 1 := by simpa only [inv_inv] using hullHecke_inverse p q⁻¹ (inv_ne_zero hq)
  calc
    _ = hullHeckeCommutator p q (hullHeckeCommutator p q⁻¹ X) := by
      simp only [hullHeckeConjugation, inv_inv]
      change (X - T*X*U) - (U*X*T-X) = T*(U*X-X*U) - (U*X-X*U)*T
      rw [mul_sub, sub_mul, ← mul_assoc T U X, hTU, one_mul, mul_assoc X U T, hUT, mul_one,
        ← mul_assoc T X U]
    _ = (q^2)⁻¹ • hullHeckeCommutator p q (hullHeckeCommutator p q X) := by
      rw [inverse_commutator p q hq]
      change T*((q^2)⁻¹ • _) - ((q^2)⁻¹ • _)*T = (q^2)⁻¹ • (T*_ - _*T)
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    _ = _ := by rw [hullHeckeCommutator_square, smul_smul]

/-- The symmetric difference has exactly the same kernel as the single Frobenius-type difference. -/
theorem hullHeckeWeyl_zero_iff (q : ℂ) (hq : q ≠ 0) (X : A) :
    (X - hullHeckeConjugation p q X) - (hullHeckeConjugation p q⁻¹ X - X) = 0 ↔
      hullHeckeConjugation p q X = X := by
  rw [hullHeckeWeyl_discriminant p q hq, smul_eq_zero, mul_eq_zero,
    or_iff_right (inv_ne_zero (pow_ne_zero _ hq)), sq_eq_zero_iff, add_eq_zero_iff_eq_neg,
    hullMixedPart_zero_iff, hullHeckeConjugation_fixed_iff p q hq, hullHecke_commute_iff]

#print axioms hullHecke_inverse
#print axioms hullHeckeConjugation_mixed_weights
#print axioms hullMixedPart_blocks
#print axioms hullHeckeConjugation_fixed_iff
#print axioms hullHeckeWeyl_discriminant
#print axioms hullHeckeWeyl_zero_iff

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
