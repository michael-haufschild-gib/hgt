import GaloisForLFunctions.AdelicKreinGeometry.TheWitnessComplementIsPositive
import GaloisForLFunctions.ArithmeticPositiveDuality.TheCriticalLineOfTheIntegerSuccessorIsTheKakutaniWall

/-!
# Hecke-supported states have index zero or infinity

A function on `Aff(ℚ)` is **Hecke-supported** when `φ(x ↦ ax + b) ≠ 0` forces `den(a)·b ∈ ℤ`:
the successor is read only through the integers, as for the Hecke states
`φ_s(x ↦ ax + b) = (nd)^{−s}·1[db ∈ ℤ]`, `a = ±n/d`, and the Haar state `φ_{1/2}`.

* **Arithmetic escape** (`exists_escape_isHeckeSupported`). For finite families `x, y` choose a
  prime `P` larger than every denominator in sight and `t = (x ↦ x + 1/P)`. The shift of
  `x_a⁻¹ t y_b` is `(β + 1/P)/α` with `β = b_y − b_x`, `α = a_x`, and
  `d(β + 1/P)/α ∈ ℤ` would force `P ∣ d·den(α)·den(β)` (`den_ne_one_of_prime`). So every
  Hecke-supported state vanishes between `x` and `t y`.
* **The affine zero-or-infinity law** (`negIndex_eq_zero_or_top_of_isHeckeSupported`). A Hermitian
  Hecke-supported function on `Aff(ℚ)` has index `0` or `∞`: a Pontryagin state that reads the
  successor through `ℤ` is positive.
* **The Kakutani wall is an index wall** (`negIndex_heckeState`). The Hecke state of exponent `s`
  has index `0` for `s ≥ 1/2` and `∞` for `s < 1/2`. Below the critical line no Hecke state is a
  Pontryagin state; the wall is crossed from positivity to infinite index in one step.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Hecke support and arithmetic escape -/

/-- **Hecke support**: `φ(x ↦ ax + b) ≠ 0` only if `den(a)·b ∈ ℤ`. -/
def IsHeckeSupported (φ : AffineGroupQ → ℂ) : Prop :=
  ∀ g, φ g ≠ 0 → (((affSlope g).den : ℚ) * affShift g).den = 1

theorem isHeckeSupported_heckeState (s : ℝ) : IsHeckeSupported (heckeState s) := by
  intro g hg
  by_contra h
  exact hg (by simp [heckeState, h])

theorem affSlope_inv_mul_translation_mul (x y : AffineGroupQ) (c : ℚ) :
    affSlope (x⁻¹ * (translation c * y)) = (affSlope x)⁻¹ * affSlope y := by
  rw [affSlope_mul, affSlope_inv, affSlope_mul, affSlope_translation, one_mul]

theorem affShift_inv_mul_translation_mul (x y : AffineGroupQ) (c : ℚ) :
    affShift (x⁻¹ * (translation c * y)) = (affShift y - affShift x + c) / affSlope x := by
  rw [affShift_mul, affSlope_inv, affShift_inv, affShift_mul, affSlope_translation,
    affShift_translation, one_mul]
  have := affSlope_ne_zero x
  field_simp
  ring

/-- **A large prime denominator cannot be cleared.** If the prime `P` divides none of `d`,
`den α`, `den β`, then `d·(β + 1/P)/α` is not an integer. -/
theorem den_ne_one_of_prime {P : ℕ} (hP : P.Prime) {d : ℕ} {α β : ℚ} (hα : α ≠ 0)
    (hd : ¬ P ∣ d) (hF : ¬ P ∣ α.den) (hE : ¬ P ∣ β.den) :
    ((d : ℚ) * ((β + 1 / P) / α)).den ≠ 1 := by
  intro h1
  obtain ⟨N, hN⟩ := (den_eq_one_iff_exists _).mp h1
  set A := α.num
  set F := α.den
  set B := β.num
  set E := β.den
  have hαe : α = (A : ℚ) / F := (Rat.num_div_den α).symm
  have hβe : β = (B : ℚ) / E := (Rat.num_div_den β).symm
  have hPpos : (P : ℚ) ≠ 0 := by exact_mod_cast hP.pos.ne'
  have hEpos : (E : ℚ) ≠ 0 := by exact_mod_cast β.den_pos.ne'
  have hFpos : (F : ℚ) ≠ 0 := by exact_mod_cast α.den_pos.ne'
  have hAne : (A : ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mpr hα
  rw [hαe, hβe] at hN
  have e : (((d : ℤ) * F * (B * P + E) : ℤ) : ℚ) = ((N * A * E * P : ℤ) : ℚ) := by
    push_cast
    rw [hN]
    field_simp
    ring
  have e' : ((d : ℤ) * F * (B * P + E) : ℤ) = N * A * E * P := by exact_mod_cast e
  have hdiv : (P : ℤ) ∣ (d : ℤ) * F * E := ⟨N * A * E - d * F * B, by linear_combination e'⟩
  have hPz : Prime (P : ℤ) := Nat.prime_iff_prime_int.mp hP
  rcases hPz.dvd_or_dvd hdiv with h | h
  · rcases hPz.dvd_or_dvd h with h | h
    · exact hd (Int.natCast_dvd_natCast.mp h)
    · exact hF (Int.natCast_dvd_natCast.mp h)
  · exact hE (Int.natCast_dvd_natCast.mp h)

/-- **Arithmetic escape.** Translation by `1/P` for a large prime `P` separates any two finite
families for every Hecke-supported function. -/
theorem exists_escape_isHeckeSupported {φ : AffineGroupQ → ℂ} (hφ : IsHeckeSupported φ)
    {m n : ℕ} (x : Fin m → AffineGroupQ) (y : Fin n → AffineGroupQ) :
    ∃ t, ∀ a b, φ ((x a)⁻¹ * (t * y b)) = 0 := by
  set f : Fin m → Fin n → ℕ := fun a b => ((affSlope (x a))⁻¹ * affSlope (y b)).den +
    (affSlope (x a)).den + (affShift (y b) - affShift (x a)).den
  set bound : ℕ := ∑ a, ∑ b, f a b
  obtain ⟨P, hPge, hP⟩ := Nat.exists_infinite_primes (bound + 1)
  refine ⟨translation (1 / P), fun a b => ?_⟩
  by_contra hne
  have h1 := hφ _ hne
  rw [affSlope_inv_mul_translation_mul, affShift_inv_mul_translation_mul] at h1
  have hfab : f a b ≤ bound :=
    (Finset.single_le_sum (f := fun b => f a b) (fun _ _ => Nat.zero_le _) (mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, f a b) (fun _ _ => Nat.zero_le _) (mem_univ a))
  have hnd : ∀ v : ℕ, 0 < v → v ≤ f a b → ¬ P ∣ v := fun v hv hvb hdv => by
    have := Nat.le_of_dvd hv hdv
    omega
  exact den_ne_one_of_prime hP (affSlope_ne_zero _)
    (hnd _ (Rat.den_pos _) (by simp only [f]; omega))
    (hnd _ (Rat.den_pos _) (by simp only [f]; omega))
    (hnd _ (Rat.den_pos _) (by simp only [f]; omega)) h1

/-- **The affine zero-or-infinity law.** A Hermitian Hecke-supported function on `Aff(ℚ)` has index
`0` or `∞`. -/
theorem negIndex_eq_zero_or_top_of_isHeckeSupported {φ : AffineGroupQ → ℂ} (hk : IsHermKernel φ)
    (hφ : IsHeckeSupported φ) : negIndex φ = 0 ∨ negIndex φ = ⊤ :=
  negIndex_eq_zero_or_top_of_escape hk fun _ _ x y => exists_escape_isHeckeSupported hφ x y

/-- A Hecke-supported Pontryagin state is positive definite. -/
theorem isPosDefOnGroup_of_isHeckeSupported {φ : AffineGroupQ → ℂ} (hk : IsHermKernel φ)
    (hφ : IsHeckeSupported φ) (hfin : negIndex φ < ⊤) : IsPosDefOnGroup φ := by
  rcases negIndex_eq_zero_or_top_of_isHeckeSupported hk hφ with h | h
  · exact isPosDefKernel_iff_isPosDefOnGroup.mp ((isPosDefKernel_iff hk).mpr h)
  · exact absurd h hfin.ne

/-! ### The Kakutani wall as an index wall -/

/-- Inverting the slope leaves the slope weight unchanged: `|num|·den` is symmetric. -/
theorem slopeWeight_inv (t : ℝ) (g : AffineGroupQ) : slopeWeight t g⁻¹ = slopeWeight t g := by
  set r := affSlope g
  have hr : r ≠ 0 := affSlope_ne_zero g
  have hnum : (r.num : ℤ) ≠ 0 := Rat.num_ne_zero.mpr hr
  have hden : ((r.den : ℤ)) ≠ 0 := by exact_mod_cast r.den_pos.ne'
  have hg : affSlope g = ((r.num : ℤ) : ℚ) / ((r.den : ℤ) : ℚ) := by
    push_cast; exact (Rat.num_div_den r).symm
  have hginv : affSlope g⁻¹ = ((r.den : ℤ) : ℚ) / ((r.num : ℤ) : ℚ) := by
    rw [affSlope_inv, hg, inv_div]
  rw [slopeWeight_of_int t hnum hden hginv, slopeWeight_of_int t hden hnum hg, Nat.gcd_comm]
  ring

/-- The Hecke states are Hermitian at every exponent. -/
theorem isHermKernel_heckeState (s : ℝ) : IsHermKernel (heckeState s) := fun g => by
  rw [heckeState_eq_mul, heckeState_eq_mul, slopeWeight_inv,
    IsPosDefOnGroup.map_inv isPosDefOnGroup_haarState g, map_mul, Complex.conj_ofReal]
  rfl

/-- **The Kakutani wall is an index wall.** The Hecke state `(nd)^{−s}·1[db ∈ ℤ]` has no negative
square for `s ≥ 1/2` and infinitely many for `s < 1/2`. -/
theorem negIndex_heckeState (s : ℝ) :
    negIndex (heckeState s) = if 1 / 2 ≤ s then 0 else ⊤ := by
  split_ifs with hs
  · exact (isPosDefKernel_iff_isPosDefOnGroup.mpr
      ((isPosDefOnGroup_heckeState_iff s).mpr hs)).negIndex_eq_zero
  · rcases negIndex_eq_zero_or_top_of_isHeckeSupported (isHermKernel_heckeState s)
      (isHeckeSupported_heckeState s) with h | h
    · exact absurd ((isPosDefOnGroup_heckeState_iff s).mp (isPosDefKernel_iff_isPosDefOnGroup.mp
        ((isPosDefKernel_iff (isHermKernel_heckeState s)).mpr h))) hs
    · exact h

end GaloisForLFunctions.AdelicKreinGeometry
