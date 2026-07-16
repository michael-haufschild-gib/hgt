import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Module.LinearMap.End

/-!
# The cubic quantum multinomial identity

At a primitive cubic relation `q²+q+1=0`, pairwise `q`-commuting elements have a classical-looking
cube: every mixed noncommutative word cancels.  This is the algebraic engine behind finite
generalized-Clifford representations of Fermat cubic horizons.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [Ring R]

/-- The cubic quantum binomial identity in an arbitrary noncommutative ring. -/
theorem quantumBinomial_cube_two (q X Y : R)
    (hqX : q * X = X * q) (hqY : q * Y = Y * q)
    (hq : q ^ 2 + q + 1 = 0)
    (hXY : X * Y = q * Y * X) :
    (X + Y) ^ 3 = X ^ 3 + Y ^ 3 := by
  have hX2Y : X * X * Y = q ^ 2 * (Y * X * X) := by
    calc
      X * X * Y = X * (X * Y) := by simp [mul_assoc]
      _ = X * (q * Y * X) := by rw [hXY]
      _ = (X * q) * Y * X := by simp [mul_assoc]
      _ = (q * X) * Y * X := by rw [← hqX]
      _ = q * (X * Y) * X := by simp [mul_assoc]
      _ = q * (q * Y * X) * X := by rw [hXY]
      _ = q ^ 2 * (Y * X * X) := by simp [pow_two, mul_assoc]
  have hXYX : X * Y * X = q * (Y * X * X) := by
    rw [hXY]
    simp [mul_assoc]
  have hYXY : Y * X * Y = q * (Y * Y * X) := by
    calc
      Y * X * Y = Y * (X * Y) := by simp [mul_assoc]
      _ = Y * (q * Y * X) := by rw [hXY]
      _ = (Y * q) * Y * X := by simp [mul_assoc]
      _ = (q * Y) * Y * X := by rw [← hqY]
      _ = q * (Y * Y * X) := by simp [mul_assoc]
  have hXY2 : X * Y * Y = q ^ 2 * (Y * Y * X) := by
    calc
      X * Y * Y = (X * Y) * Y := rfl
      _ = (q * Y * X) * Y := by rw [hXY]
      _ = q * (Y * X * Y) := by simp [mul_assoc]
      _ = q * (q * (Y * Y * X)) := by rw [hYXY]
      _ = q ^ 2 * (Y * Y * X) := by simp [pow_two, mul_assoc]
  have hzeroX :
      Y * X * X + q * (Y * X * X) + q * (q * (Y * X * X)) = 0 := by
    calc
      _ = (1 + q + q ^ 2) * (Y * X * X) := by noncomm_ring
      _ = 0 := by
        have : 1 + q + q ^ 2 = 0 := by
          simpa [add_comm, add_left_comm, add_assoc] using hq
        rw [this, zero_mul]
  have hzeroY :
      Y * Y * X + q * (Y * Y * X) + q * (q * (Y * Y * X)) = 0 := by
    calc
      _ = (1 + q + q ^ 2) * (Y * Y * X) := by noncomm_ring
      _ = 0 := by
        have : 1 + q + q ^ 2 = 0 := by
          simpa [add_comm, add_left_comm, add_assoc] using hq
        rw [this, zero_mul]
  have hgroupX : X * X * Y + X * Y * X + Y * X * X = 0 := by
    rw [hX2Y, hXYX]
    simpa [pow_two, mul_assoc, add_comm, add_left_comm, add_assoc] using hzeroX
  have hgroupY : X * Y * Y + Y * X * Y + Y * Y * X = 0 := by
    rw [hXY2, hYXY]
    simpa [pow_two, mul_assoc, add_comm, add_left_comm, add_assoc] using hzeroY
  calc
    (X + Y) ^ 3 =
        X ^ 3 + (X * X * Y + X * Y * X + Y * X * X) +
          (X * Y * Y + Y * X * Y + Y * Y * X) + Y ^ 3 := by
      noncomm_ring
    _ = X ^ 3 + Y ^ 3 := by rw [hgroupX, hgroupY]; simp

/-- Three pairwise `q`-commuting elements satisfy the Fermat cubic identity. -/
theorem quantumMultinomial_cube_three (q X Y Z : R)
    (hqX : q * X = X * q) (hqY : q * Y = Y * q) (hqZ : q * Z = Z * q)
    (hq : q ^ 2 + q + 1 = 0)
    (hXY : X * Y = q * Y * X)
    (hXZ : X * Z = q * Z * X)
    (hYZ : Y * Z = q * Z * Y) :
    (X + Y + Z) ^ 3 = X ^ 3 + Y ^ 3 + Z ^ 3 := by
  have hqXY : q * (X + Y) = (X + Y) * q := by
    noncomm_ring [hqX, hqY]
  have hXYZ : (X + Y) * Z = q * Z * (X + Y) := by
    noncomm_ring [hXZ, hYZ]
  rw [quantumBinomial_cube_two q (X + Y) Z hqXY hqZ hq hXYZ,
    quantumBinomial_cube_two q X Y hqX hqY hq hXY]

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A cubic root-of-unity triple of endomorphisms linearizes the Fermat cubic form. -/
theorem quantumFermatCubic_endomorphism
    (ω a b c : K) (X Y Z : Module.End K M)
    (hω : ω ^ 2 + ω + 1 = 0)
    (hX3 : X ^ 3 = 1) (hY3 : Y ^ 3 = 1) (hZ3 : Z ^ 3 = 1)
    (hXY : X * Y = ω • (Y * X))
    (hXZ : X * Z = ω • (Z * X))
    (hYZ : Y * Z = ω • (Z * Y)) :
    (a • X + b • Y + c • Z) ^ 3 =
      (a ^ 3 + b ^ 3 + c ^ 3) • (1 : Module.End K M) := by
  let q : Module.End K M := ω • 1
  have hq_comm (T : Module.End K M) : q * T = T * q := by
    ext m
    simp [q]
  have hq : q ^ 2 + q + 1 = 0 := by
    calc
      q ^ 2 + q + 1 = (ω ^ 2 + ω + 1) • (1 : Module.End K M) := by
        simp [q, smul_pow, add_smul]
      _ = 0 := by rw [hω]; simp
  have hXY' : (a • X) * (b • Y) = q * (b • Y) * (a • X) := by
    calc
      (a • X) * (b • Y) = (a * b) • (X * Y) := by
        simp [smul_mul_smul_comm]
      _ = (a * b) • (ω • (Y * X)) := by rw [hXY]
      _ = q * (b • Y) * (a • X) := by
        simp [q, smul_mul_smul_comm, smul_smul]
        congr 1
        ac_rfl
  have hXZ' : (a • X) * (c • Z) = q * (c • Z) * (a • X) := by
    calc
      (a • X) * (c • Z) = (a * c) • (X * Z) := by
        simp [smul_mul_smul_comm]
      _ = (a * c) • (ω • (Z * X)) := by rw [hXZ]
      _ = q * (c • Z) * (a • X) := by
        simp [q, smul_mul_smul_comm, smul_smul]
        congr 1
        ac_rfl
  have hYZ' : (b • Y) * (c • Z) = q * (c • Z) * (b • Y) := by
    calc
      (b • Y) * (c • Z) = (b * c) • (Y * Z) := by
        simp [smul_mul_smul_comm]
      _ = (b * c) • (ω • (Z * Y)) := by rw [hYZ]
      _ = q * (c • Z) * (b • Y) := by
        simp [q, smul_mul_smul_comm, smul_smul]
        congr 1
        ac_rfl
  rw [quantumMultinomial_cube_three q (a • X) (b • Y) (c • Z)
    (hq_comm _) (hq_comm _) (hq_comm _) hq hXY' hXZ' hYZ']
  simp [smul_pow, hX3, hY3, hZ3, add_smul]

end GaloisForLFunctions.HTGeometry
