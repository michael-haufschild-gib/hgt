import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicRadicalContraction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.OppositeRadicalAveraging
import Mathlib.Tactic.Abel

/-! For an integral projection `P`, the diagonal action specified
by `P + p^m(1-P)` contracts the opposite radical. Pulling back a
lift of the forward radical through the first diagonal step gives a
lift of the opposite radical. -/

noncomputable section

open Matrix GlobalTheory.OppRad
open scoped Classical

namespace GlobalTheory.GLp

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

local notation "φ" => RingHom.mapMatrix (m := Fin n) (PadicInt.toZMod (p := g))
local notation "ι" => RingHom.mapMatrix (m := Fin n) (algebraMap ℤ_[g] ℚ_[g])
local notation "red" => integralReduction g (Fin n)
local notation "inc" => integralInclusion g (Fin n)

private theorem exists_unit (A : Matrix (Fin n) (Fin n) ℤ_[g]) (u : GL (Fin n) (ZMod g)) (h : φ A = u.val) :
    ∃ k : GL (Fin n) ℤ_[g], k.val = A ∧ red k = u := by
  have hdet : IsUnit A.det := by
    by_contra h'
    have h1 : A.det ∈ IsLocalRing.maximalIdeal ℤ_[g] := h'
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, h] at h1
    exact (Matrix.isUnits_det_units u).ne_zero h1
  exact ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, rfl, Units.ext h⟩

private theorem exists_div {N : Matrix (Fin n) (Fin n) ℤ_[g]} (h : φ N = 0) :
    ∃ M : Matrix (Fin n) (Fin n) ℤ_[g], N = (g : Matrix (Fin n) (Fin n) ℤ_[g]) * M := by
  have : ∀ i j, ∃ c, c * (g : ℤ_[g]) = N i j := fun i j => by
    have : N i j ∈ RingHom.ker (PadicInt.toZMod (p := g)) := congrFun (congrFun h i) j
    rwa [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at this
  choose M hM using this
  refine ⟨Matrix.of M, ?_⟩
  ext i j
  rw [← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul, Matrix.of_apply, ← hM, mul_comm]

private theorem red_nat : φ (g : Matrix (Fin n) (Fin n) ℤ_[g]) = 0 := by
  rw [map_natCast, ← nsmul_one, ← Nat.cast_smul_eq_nsmul (ZMod g), ZMod.natCast_self, zero_smul]

private theorem idem_mul {A R : Type} [CommRing A] [Ring R] [Algebra A R] {P : R} (h : P * P = P) (s t : A) :
    (P + s • (1 - P)) * (P + t • (1 - P)) = P + (s * t) • (1 - P) := by
  have h1 : P * (1 - P) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  have h2 : (1 - P) * P = 0 := by rw [sub_mul, h, one_mul, sub_self]
  have h3 : (1 - P) * (1 - P) = 1 - P := by rw [sub_mul, h1, one_mul, sub_zero]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, h, h1, h2, h3, smul_zero, add_zero, zero_add, smul_smul,
    mul_comm]

variable {P : Matrix (Fin n) (Fin n) ℤ_[g]}

def projectionTorus (hP : P * P = P) (m : ℕ) : GL (Fin n) ℚ_[g] :=
  have h : ι P * ι P = ι P := by rw [← map_mul, hP]
  have h0 : (g : ℚ_[g]) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero)
  ⟨ι P + (g : ℚ_[g]) ^ m • (1 - ι P), ι P + ((g : ℚ_[g]) ^ m)⁻¹ • (1 - ι P),
    by rw [idem_mul h, mul_inv_cancel₀ h0, one_smul, add_sub_cancel],
    by rw [idem_mul h, inv_mul_cancel₀ h0, one_smul, add_sub_cancel]⟩

theorem projectionTorus_val (hP : P * P = P) (m : ℕ) : (projectionTorus hP m).val = ι (P + g ^ m • (1 - P)) := by
  rw [map_add, map_nsmul, map_sub, map_one, ← Nat.cast_smul_eq_nsmul ℚ_[g], Nat.cast_pow]
  rfl

theorem projectionTorus_zero (hP : P * P = P) : projectionTorus hP 0 = 1 :=
  Units.ext (by rw [projectionTorus_val, pow_zero, one_smul, add_sub_cancel, map_one, Units.val_one])

theorem projectionTorus_succ (hP : P * P = P) (m : ℕ) : projectionTorus hP (m + 1) = projectionTorus hP m * projectionTorus hP 1 :=
  Units.ext ((congrArg (fun s => ι P + s • (1 - ι P)) (pow_add _ _ _)).trans
    (idem_mul (by rw [← map_mul, hP]) _ _).symm)

theorem conjugate_forward_radical (hP : P * P = P) {k : GL (Fin n) ℤ_[g]} (hk : red k ∈ U (φ P) (1 - φ P)) :
    ∃ k', red k' ∈ U (1 - φ P) (φ P) ∧ projectionTorus hP 1 * inc k' = inc k * projectionTorus hP 1 := by
  have hp : φ P * φ P = φ P := by rw [← map_mul, hP]
  obtain ⟨x, hx⟩ : ∃ x, φ k.val = 1 + φ P * (x * (1 - φ P)) :=
    ⟨(red k).val - 1, by rw [hk.2, hk.1, add_sub_cancel]; rfl⟩
  have hp' : ∀ r, φ P * (φ P * r) = φ P * r := fun r => by rw [← mul_assoc, hp]
  obtain ⟨M, hM⟩ := exists_div (N := (1 - P) * k.val * P) (by
    rw [map_mul, map_mul, map_sub, map_one, hx]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, add_zero, zero_add, zero_mul])
  have hx2 : (1 - φ P) * (φ M * φ P) * ((1 - φ P) * (φ M * φ P)) = 0 := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, add_zero]
  obtain ⟨k', h1, h2⟩ := exists_unit (P * k.val * P + (1 - P) * k.val * (1 - P) +
    (g : Matrix (Fin n) (Fin n) ℤ_[g]) * (P * k.val * (1 - P)) + (1 - P) * (M * P)) (un _ hx2) (by
      simp only [map_add, map_mul, map_sub, map_one, red_nat, hx, un_val, zero_mul]
      simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, add_zero]
      abel)
  refine ⟨k', h2 ▸ un_mem _ ?_ ?_, Units.ext ?_⟩
  · simp only [mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, sub_zero]
  · simp only [mul_assoc, hp]
  · change (projectionTorus hP 1).val * ι k'.val = ι k.val * (projectionTorus hP 1).val
    rw [projectionTorus_val, ← map_mul, ← map_mul, h1]
    congr 1
    have hP' : ∀ r, P * (P * r) = P * r := fun r => by rw [← mul_assoc, hP]
    have hM' : g • ((1 - P) * (M * P)) = (1 - P) * k.val * P := by
      rw [← mul_smul_comm, ← smul_mul_assoc, nsmul_eq_mul, ← hM]
      simp only [mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul, sub_self, sub_zero]
    have e : (P + g • (1 - P)) * ((1 - P) * (M * P)) = g • ((1 - P) * (M * P)) := by
      simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul, sub_self, sub_zero,
        smul_mul_assoc, zero_add, smul_zero, add_zero, add_sub_cancel_left]
    rw [pow_one, ← nsmul_eq_mul, mul_add _ _ ((1 - P) * _), e, hM']
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul, sub_self, sub_zero,
        smul_mul_assoc, mul_smul_comm, zero_add, add_zero, smul_zero, smul_sub, smul_add]
    abel

theorem conjugate_opposite_radical (hP : P * P = P) {u : GL (Fin n) (ZMod g)} (hu : u ∈ U (1 - φ P) (φ P)) (m : ℕ) :
    ∃ k k', red k = u ∧ red k' = 1 ∧ projectionTorus hP (m + 1) * inc k = inc k' * projectionTorus hP (m + 1) := by
  obtain ⟨y, rfl⟩ := integralReduction_surjective g (Fin n) u
  have hP' : ∀ r, P * (P * r) = P * r := fun r => by rw [← mul_assoc, hP]
  obtain ⟨k, h1, h2⟩ := exists_unit (1 + (1 - P) * ((y.val - 1) * P)) (red y) (by
    simp only [map_add, map_mul, map_sub, map_one]
    change 1 + _ * (((red y).val - 1) * _) = _
    rw [hu.2, hu.1, add_sub_cancel])
  obtain ⟨k', h3, h4⟩ := exists_unit (1 + (g : Matrix (Fin n) (Fin n) ℤ_[g]) ^ (m + 1) * ((1 - P) * ((y.val - 1) * P)))
    1 (by simp only [map_add, map_mul, map_pow, red_nat, map_one, pow_succ, mul_zero, zero_mul, add_zero, Units.val_one])
  refine ⟨k, k', h2, h4, Units.ext ?_⟩
  change (projectionTorus hP _).val * ι k.val = ι k'.val * (projectionTorus hP _).val
  rw [projectionTorus_val, ← map_mul, ← map_mul, h1, h3]
  congr 1
  generalize y.val - 1 = z
  rw [← Nat.cast_pow, ← nsmul_eq_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul,
    sub_self, sub_zero, smul_mul_assoc, mul_smul_comm, zero_add, add_zero, smul_zero, smul_sub, smul_add]
  abel

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.conjugate_forward_radical
#print axioms GlobalTheory.GLp.conjugate_opposite_radical
