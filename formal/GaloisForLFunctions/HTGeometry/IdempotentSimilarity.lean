/-
# Nearby idempotents are conjugate

Two idempotents of a Banach algebra at distance less than one are conjugate by a unit.  The
intertwiner is the classical

  `u = q p + (1 − q)(1 − p)`,

whose product with the same expression in the opposite order is `1 − (p − q)^(2 : ℕ)`, hence invertible
by the geometric series.

Main results:
* `idempotentIntertwiner`, `idempotentIntertwiner_mul_swap` — the intertwiner and the product law.
* `idempotentIntertwiner_mul_left` — the intertwining relation `u p = q u`.
* `exists_unit_conj_of_norm_sub_lt_one`, `exists_eq_conj_of_norm_sub_lt_one` — **nearby idempotents
  are conjugate**.
* `finrank_range_eq_of_norm_sub_lt_one` — **nearby idempotent operators have equal rank**.
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [NormedRing A] [CompleteSpace A] {p q : A}

/-- The classical intertwiner `q p + (1 − q)(1 − p)` of two idempotents. -/
def idempotentIntertwiner (p q : A) : A := q * p + (1 - q) * (1 - p)

omit [CompleteSpace A] in
/-- The intertwiner and its transpose multiply to `1 − (p − q)^(2 : ℕ)`. -/
theorem idempotentIntertwiner_mul_swap (hp : p * p = p) (hq : q * q = q) :
    idempotentIntertwiner p q * idempotentIntertwiner q p = 1 - (p - q) * (p - q) := by
  have hpp : ∀ x : A, p * (p * x) = p * x := fun x => by rw [← mul_assoc, hp]
  simp only [idempotentIntertwiner, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    mul_assoc, hpp, hp, hq]
  abel

omit [CompleteSpace A] in
/-- The intertwining relation `u p = q u`. -/
theorem idempotentIntertwiner_mul_left (hp : p * p = p) (hq : q * q = q) :
    idempotentIntertwiner p q * p = q * idempotentIntertwiner p q := by
  have hqq : ∀ x : A, q * (q * x) = q * x := fun x => by rw [← mul_assoc, hq]
  simp only [idempotentIntertwiner, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    mul_assoc, hqq, hp, hq]
  abel

/-- The intertwiner is a unit when the two idempotents are at distance less than one. -/
theorem isUnit_idempotentIntertwiner (hp : p * p = p) (hq : q * q = q) (h : ‖p - q‖ < 1) :
    IsUnit (idempotentIntertwiner p q) := by
  have hnorm : ‖(p - q) * (p - q)‖ < 1 := by
    have hle : ‖(p - q) * (p - q)‖ ≤ ‖p - q‖ * ‖p - q‖ := norm_mul_le _ _
    nlinarith [norm_nonneg (p - q)]
  obtain ⟨w, hw⟩ := isUnit_one_sub_of_norm_lt_one hnorm
  have hsym : (q - p) * (q - p) = (p - q) * (p - q) := by noncomm_ring
  have h1 : idempotentIntertwiner p q * idempotentIntertwiner q p = (w : A) := by
    rw [idempotentIntertwiner_mul_swap hp hq, hw]
  have h2 : idempotentIntertwiner q p * idempotentIntertwiner p q = (w : A) := by
    rw [idempotentIntertwiner_mul_swap hq hp, hsym, hw]
  have hUr : idempotentIntertwiner p q * (idempotentIntertwiner q p * (↑w⁻¹ : A)) = 1 := by
    rw [← mul_assoc, h1, w.mul_inv]
  have hlU : ((↑w⁻¹ : A) * idempotentIntertwiner q p) * idempotentIntertwiner p q = 1 := by
    rw [mul_assoc, h2, w.inv_mul]
  have hlr : ((↑w⁻¹ : A) * idempotentIntertwiner q p)
      = idempotentIntertwiner q p * (↑w⁻¹ : A) :=
    calc ((↑w⁻¹ : A) * idempotentIntertwiner q p)
        = ((↑w⁻¹ : A) * idempotentIntertwiner q p) * 1 := (mul_one _).symm
      _ = ((↑w⁻¹ : A) * idempotentIntertwiner q p)
            * (idempotentIntertwiner p q * (idempotentIntertwiner q p * (↑w⁻¹ : A))) := by
          rw [hUr]
      _ = (((↑w⁻¹ : A) * idempotentIntertwiner q p) * idempotentIntertwiner p q)
            * (idempotentIntertwiner q p * (↑w⁻¹ : A)) := by noncomm_ring
      _ = idempotentIntertwiner q p * (↑w⁻¹ : A) := by rw [hlU, one_mul]
  exact ⟨⟨idempotentIntertwiner p q, idempotentIntertwiner q p * (↑w⁻¹ : A), hUr,
    by rw [← hlr]; exact hlU⟩, rfl⟩

/-- **Two idempotents at distance less than one are intertwined by a unit.** -/
theorem exists_unit_conj_of_norm_sub_lt_one (hp : p * p = p) (hq : q * q = q) (h : ‖p - q‖ < 1) :
    ∃ u : Aˣ, (u : A) * p = q * (u : A) := by
  obtain ⟨u, hu⟩ := isUnit_idempotentIntertwiner hp hq h
  exact ⟨u, by rw [hu]; exact idempotentIntertwiner_mul_left hp hq⟩

/-- **Two idempotents at distance less than one are conjugate.** -/
theorem exists_eq_conj_of_norm_sub_lt_one (hp : p * p = p) (hq : q * q = q) (h : ‖p - q‖ < 1) :
    ∃ u : Aˣ, q = (u : A) * p * (↑u⁻¹ : A) := by
  obtain ⟨u, hu⟩ := exists_unit_conj_of_norm_sub_lt_one hp hq h
  exact ⟨u, by rw [hu, mul_assoc, u.mul_inv, mul_one]⟩

/-! ## Ranges of nearby idempotent operators -/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Conjugate operators have ranges related by the conjugating map. -/
theorem range_eq_map_of_conj {p q : H →L[ℂ] H} {u : (H →L[ℂ] H)ˣ}
    (hu : (u : H →L[ℂ] H) * p = q * (u : H →L[ℂ] H)) :
    LinearMap.range (q : H →ₗ[ℂ] H)
      = Submodule.map ((u : H →L[ℂ] H) : H →ₗ[ℂ] H) (LinearMap.range (p : H →ₗ[ℂ] H)) := by
  have hlin : ((u : H →L[ℂ] H) : H →ₗ[ℂ] H) ∘ₗ (p : H →ₗ[ℂ] H)
      = (q : H →ₗ[ℂ] H) ∘ₗ ((u : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    ext x
    simpa using congrArg (fun f : H →L[ℂ] H => f x) hu
  have hsurj : Function.Surjective ((u : H →L[ℂ] H) : H →ₗ[ℂ] H) := fun y =>
    ⟨(↑u⁻¹ : H →L[ℂ] H) y, by
      have h1 := congrArg (fun f : H →L[ℂ] H => f y) u.mul_inv
      simp only [mul_apply_eq_comp, one_apply_eq_self] at h1
      exact h1⟩
  rw [← LinearMap.range_comp, hlin, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]

/-- **Two idempotent operators at distance less than one have the same rank.** -/
theorem finrank_range_eq_of_norm_sub_lt_one {p q : H →L[ℂ] H}
    (hp : p * p = p) (hq : q * q = q) (h : ‖p - q‖ < 1) :
    Module.finrank ℂ (LinearMap.range (q : H →ₗ[ℂ] H))
      = Module.finrank ℂ (LinearMap.range (p : H →ₗ[ℂ] H)) := by
  obtain ⟨u, hu⟩ := exists_unit_conj_of_norm_sub_lt_one hp hq h
  have hinv : ∀ x : H, (↑u⁻¹ : H →L[ℂ] H) ((u : H →L[ℂ] H) x) = x := fun x => by
    have h1 := congrArg (fun f : H →L[ℂ] H => f x) u.inv_mul
    simp only [mul_apply_eq_comp, one_apply_eq_self] at h1
    exact h1
  have hinj : Function.Injective ((u : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
    Function.LeftInverse.injective hinv
  rw [range_eq_map_of_conj hu]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

end GaloisForLFunctions.HTGeometry
