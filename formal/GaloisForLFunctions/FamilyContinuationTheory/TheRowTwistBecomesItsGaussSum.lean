import GaloisForLFunctions.FamilyContinuationTheory.TwistedColumnsCorrelateThroughOneResidue

/-!
# The row twist becomes its Gauss sum

The probe pairs an additive column of modulus `a` with a row that carries a multiplicative twist
of modulus `b`. Poisson summation in the row, for coprime moduli, is one term:

`∑_{m mod ab} column_a(f)(m) · g(m mod b) · e(−mk/ab) = a · f(k b⁻¹) · ĝ(−k a⁻¹)`
(`sum_column_mul_row_of_coprime`),

`ĝ` the finite Fourier transform of the row twist. For a character `φ` of modulus `b` the transform
at a unit is `\bar φ` times the Gauss sum of `φ` (`rowTransform_mulChar_unit`): the row twist enters
the frequency side through its Gauss sum, and the column through one value. In the family
continuation this Gauss sum, multiplied by the theta coefficient of the row, is the source of the
Möbius sign; the column contributes its mass.

Proof: a function of `m mod b` is the conjugate of the additive column of its transform (Fourier
inversion), and the correlation of two columns of coprime moduli is one term.
-/

open scoped ComplexConjugate
open Finset

namespace GaloisForLFunctions.FamilyContinuationTheory

/-- Fourier inversion on `ℤ/N`. -/
theorem sum_rowTransform_mul_stdAddChar {N : ℕ} [NeZero N] (g : ZMod N → ℂ) (y : ZMod N) :
    ∑ t : ZMod N, rowTransform g t * ZMod.stdAddChar (-(y * t)) = (N : ℂ) * g y := by
  unfold rowTransform
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h : ∀ z : ZMod N,
      ∑ t : ZMod N, g z * ZMod.stdAddChar (z * t) * ZMod.stdAddChar (-(y * t))
        = g z * (if z - y = 0 then (N : ℂ) else 0) := by
    intro z
    rw [← sum_stdAddChar_mul (z - y), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [h]
  rw [Finset.sum_eq_single y]
  · simp [mul_comm]
  · intro z _ hz
    rw [if_neg (sub_ne_zero.mpr hz), mul_zero]
  · intro hy
    exact absurd (Finset.mem_univ y) hy

variable {a b : ℕ} [NeZero a] [NeZero b]

omit [NeZero a] in
/-- A function of the residue modulo `b` is the conjugate of the additive column of its
transform. -/
theorem conj_column_conj_rowTransform (g : ZMod b → ℂ) (m : ZMod (a * b)) :
    conj (column (dvd_mul_left b a) (fun t => conj (rowTransform g t)) m) =
      (b : ℂ) * g (ZMod.castHom (dvd_mul_left b a) (ZMod b) m) := by
  unfold column
  rw [map_sum, ← sum_rowTransform_mul_stdAddChar g]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, Complex.conj_conj, ← AddChar.map_neg_eq_conj]

/-- **Poisson summation in the row for coprime moduli.** The coefficient at the frequency `k` of
an additive column times a row twist is one value of the column times one value of the transform
of the twist. -/
theorem sum_column_mul_row_of_coprime (hab : a.Coprime b) (f : ZMod a → ℂ) (g : ZMod b → ℂ)
    (k : ZMod (a * b)) :
    ∑ m : ZMod (a * b), column (dvd_mul_right a b) f m *
        g (ZMod.castHom (dvd_mul_left b a) (ZMod b) m) * ZMod.stdAddChar (-(m * k)) =
      (a : ℂ) * (f (firstResidue a b k) * rowTransform g (secondResidue a b k)) := by
  have hb : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne b)
  have h := sum_column_mul_conj_column_of_coprime hab f (fun t => conj (rowTransform g t)) k
  simp_rw [conj_column_conj_rowTransform] at h
  rw [Complex.conj_conj] at h
  apply mul_left_cancel₀ hb
  rw [Finset.mul_sum]
  calc ∑ m : ZMod (a * b), (b : ℂ) * (column (dvd_mul_right a b) f m *
          g (ZMod.castHom (dvd_mul_left b a) (ZMod b) m) * ZMod.stdAddChar (-(m * k)))
      = ∑ m : ZMod (a * b), column (dvd_mul_right a b) f m *
          ((b : ℂ) * g (ZMod.castHom (dvd_mul_left b a) (ZMod b) m)) *
            ZMod.stdAddChar (-(m * k)) :=
        Finset.sum_congr rfl fun m _ => by ring
    _ = ((a * b : ℕ) : ℂ) * (f (firstResidue a b k) * rowTransform g (secondResidue a b k)) := h
    _ = (b : ℂ) * ((a : ℂ) * (f (firstResidue a b k) * rowTransform g (secondResidue a b k))) := by
        push_cast
        ring

omit [NeZero a] in
/-- The transform of a character at a unit is the conjugate value times the Gauss sum. -/
theorem rowTransform_mulChar_unit (φ : MulChar (ZMod b) ℂ) (u : (ZMod b)ˣ) :
    rowTransform φ (u : ZMod b) =
      φ ((u⁻¹ : (ZMod b)ˣ) : ZMod b) * gaussSum φ ZMod.stdAddChar := by
  have hshift : rowTransform φ (u : ZMod b) =
      gaussSum φ (ZMod.stdAddChar.mulShift (u : ZMod b)) := by
    unfold rowTransform gaussSum
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [AddChar.mulShift_apply, mul_comm (u : ZMod b) y]
  have h := gaussSum_mulShift φ ZMod.stdAddChar u
  have hone : φ ((u⁻¹ : (ZMod b)ˣ) : ZMod b) * φ (u : ZMod b) = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  rw [hshift, ← h, ← mul_assoc, hone, one_mul]

/-- **The coefficient of a character row at a unit frequency.** The column gives one value, the
row twist its Gauss sum. -/
theorem sum_column_mul_char_row_of_coprime (hab : a.Coprime b) (f : ZMod a → ℂ)
    (φ : MulChar (ZMod b) ℂ) (k : ZMod (a * b)) (u : (ZMod b)ˣ)
    (hu : secondResidue a b k = (u : ZMod b)) :
    ∑ m : ZMod (a * b), column (dvd_mul_right a b) f m *
        φ (ZMod.castHom (dvd_mul_left b a) (ZMod b) m) * ZMod.stdAddChar (-(m * k)) =
      (a : ℂ) * (f (firstResidue a b k) *
        (φ ((u⁻¹ : (ZMod b)ˣ) : ZMod b) * gaussSum φ ZMod.stdAddChar)) := by
  rw [sum_column_mul_row_of_coprime hab f φ k, hu, rowTransform_mulChar_unit]

end GaloisForLFunctions.FamilyContinuationTheory
