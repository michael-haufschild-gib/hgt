import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleWeylCharacter
import Mathlib.Algebra.Algebra.Field

/-!
# Prime-local diagonal reciprocity for the finite-adele character

For a height-one place `v`, the finite standard character evaluates the
diagonal rational `m / p_v ^ n` as that same rational modulo `ℤ`. The local
term at `v` is fixed by the all-depth normalization, while every other local
term vanishes because `p_v` is a unit there.

Consequently, the finite character cancels the negative archimedean character
on every prime-local lattice `ℤ[1 / p_v]`. This is exactly the diagonal
product law needed by a fixed-`p` spherical perfection stage. The extension
from prime-power denominators to arbitrary rational denominators remains a
separate primary-decomposition theorem.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Filter Function IsDedekindDomain
open scoped RestrictedProduct

noncomputable def fieldOneRationalUnitAddCircleCharacter :
    ℚ →+ UnitAddCircle where
  toFun q := ((q : ℝ) : UnitAddCircle)
  map_zero' := by simp
  map_add' x y := by
    change
      ((↑(x + y) : ℝ) : UnitAddCircle) =
        (↑x : ℝ) + (↑y : ℝ)
    rw [Rat.cast_add]
    rfl

variable (p : ℕ) [hp : Fact p.Prime]

theorem fieldOnePadicStandardUnitAddCircleCharacter_int_div_pow
    (m : ℤ) (n : ℕ) :
    fieldOnePadicStandardUnitAddCircleCharacter p
        ((m : ℚ_[p]) / (p : ℚ_[p]) ^ n) =
      fieldOneRationalUnitAddCircleCharacter
        ((m : ℚ) / (p : ℚ) ^ n) := by
  rw [div_eq_mul_inv]
  have hmul :
      (m : ℚ_[p]) * ((p : ℚ_[p]) ^ n)⁻¹ =
        m • (((p : ℚ_[p]) ^ n)⁻¹) := by
    rw [zsmul_eq_mul]
  rw [hmul, map_zsmul,
    fieldOnePadicStandardUnitAddCircleCharacter_inv_pow]
  rw [← map_zsmul]
  simp only [zsmul_eq_mul, mul_one]
  rw [ZMod.toAddCircle_intCast]
  change
    (((m : ℝ) / (p ^ n : ℕ) : ℝ) : UnitAddCircle) =
      (((((m : ℚ) / (p : ℚ) ^ n : ℚ) : ℝ)) : UnitAddCircle)
  congr 1
  norm_cast

theorem fieldOneFiniteAdeleLocalUnitCharacter_algebraMap_int_div_pow
    (v : HeightOneSpectrum ℤ) (m : ℤ) (n : ℕ) :
    fieldOneFiniteAdeleLocalUnitCharacter v
        (algebraMap ℚ (v.adicCompletion ℚ)
          ((m : ℚ) /
            (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n)) =
      fieldOneRationalUnitAddCircleCharacter
        ((m : ℚ) /
          (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n) := by
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  change
    fieldOnePadicStandardUnitAddCircleCharacter
      (Rat.HeightOneSpectrum.primesEquiv v)
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
        (algebraMap ℚ (v.adicCompletion ℚ)
          ((m : ℚ) /
            (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n))) =
      fieldOneRationalUnitAddCircleCharacter
        ((m : ℚ) /
          (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n)
  have heq :
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
          (algebraMap ℚ (v.adicCompletion ℚ)
            ((m : ℚ) /
              (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n)) =
        algebraMap ℚ
          ℚ_[Rat.HeightOneSpectrum.primesEquiv v]
          ((m : ℚ) /
            (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n) :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.commutes _
  rw [heq]
  have hcast :
      algebraMap ℚ
          ℚ_[Rat.HeightOneSpectrum.primesEquiv v]
          ((m : ℚ) /
            (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n) =
        (m : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) /
          (Rat.HeightOneSpectrum.primesEquiv v :
            ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) ^ n := by
    calc
      algebraMap ℚ
          ℚ_[Rat.HeightOneSpectrum.primesEquiv v]
          ((m : ℚ) /
            (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n) =
          ((((m : ℚ) /
            (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n) : ℚ) :
              ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) :=
        map_ratCast
          (algebraMap ℚ
            ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) _
      _ = (m : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) /
          (Rat.HeightOneSpectrum.primesEquiv v :
            ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) ^ n := by
        norm_cast
  rw [hcast]
  exact
    fieldOnePadicStandardUnitAddCircleCharacter_int_div_pow
      (Rat.HeightOneSpectrum.primesEquiv v) m n

theorem fieldOnePadic_int_div_primePow_mem_integers_of_ne
    {q : ℕ} [hq : Fact q.Prime] (hpq : p ≠ q)
    (m : ℤ) (n : ℕ) :
    (m : ℚ_[p]) / (q : ℚ_[p]) ^ n ∈ PadicInt.subring p := by
  change ‖(m : ℚ_[p]) / (q : ℚ_[p]) ^ n‖ ≤ 1
  have hnormq : ‖(q : ℚ_[p])‖ = 1 := by
    rw [show (q : ℚ_[p]) = ((q : ℚ) : ℚ_[p]) by norm_cast,
      Padic.eq_padicNorm,
      padicNorm.padicNorm_of_prime_of_ne hpq]
    norm_num
  rw [norm_div, norm_pow, hnormq, one_pow, div_one]
  exact Padic.norm_int_le_one m

theorem fieldOneFiniteAdele_algebraMap_int_div_pow_mem_integers_of_ne
    {v w : HeightOneSpectrum ℤ} (hvw : w ≠ v)
    (m : ℤ) (n : ℕ) :
    algebraMap ℚ (w.adicCompletion ℚ)
        ((m : ℚ) /
          (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n) ∈
      w.adicCompletionIntegers ℚ := by
  let pv := Rat.HeightOneSpectrum.primesEquiv v
  let pw := Rat.HeightOneSpectrum.primesEquiv w
  letI : Fact (Nat.Prime pv) := ⟨pv.2⟩
  letI : Fact (Nat.Prime pw) := ⟨pw.2⟩
  have hpw_ne_pv : (pw : ℕ) ≠ (pv : ℕ) := by
    intro h
    apply hvw
    apply (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).injective
    exact Subtype.ext h
  let x : w.adicCompletion ℚ :=
    algebraMap ℚ (w.adicCompletion ℚ)
      ((m : ℚ) / (pv : ℚ) ^ n)
  have hy :
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv w x ∈
        PadicInt.subring pw := by
    rw [show
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv w x =
        algebraMap ℚ ℚ_[pw] ((m : ℚ) / (pv : ℚ) ^ n) by
          exact
            (Rat.HeightOneSpectrum.adicCompletion.padicEquiv w).commutes _]
    have hcast :
        algebraMap ℚ ℚ_[pw] ((m : ℚ) / (pv : ℚ) ^ n) =
          (m : ℚ_[pw]) / (pv : ℚ_[pw]) ^ n := by
      calc
        algebraMap ℚ ℚ_[pw] ((m : ℚ) / (pv : ℚ) ^ n) =
            ((((m : ℚ) / (pv : ℚ) ^ n) : ℚ) : ℚ_[pw]) :=
          map_ratCast (algebraMap ℚ ℚ_[pw]) _
        _ = (m : ℚ_[pw]) / (pv : ℚ_[pw]) ^ n := by
          norm_cast
    rw [hcast]
    exact
      fieldOnePadic_int_div_primePow_mem_integers_of_ne
        pw hpw_ne_pv m n
  obtain ⟨z, hz, hzx⟩ :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn w).surjOn hy
  have hzx' : z = x :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv w).injective hzx
  change x ∈ w.adicCompletionIntegers ℚ
  rw [← hzx']
  exact hz

theorem fieldOneFiniteAdeleStandardUnitAddCircleCharacter_algebraMap_int_div_pow
    (v : HeightOneSpectrum ℤ) (m : ℤ) (n : ℕ) :
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter
        (algebraMap ℚ FieldOneFiniteAdele
          ((m : ℚ) /
            (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n)) =
      fieldOneRationalUnitAddCircleCharacter
        ((m : ℚ) /
          (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n) := by
  let q : ℚ :=
    (m : ℚ) /
      (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n
  change
    (∑ᶠ w, fieldOneFiniteAdeleLocalUnitCharacter w
      ((algebraMap ℚ FieldOneFiniteAdele q) w)) =
      fieldOneRationalUnitAddCircleCharacter q
  calc
    (∑ᶠ w, fieldOneFiniteAdeleLocalUnitCharacter w
        ((algebraMap ℚ FieldOneFiniteAdele q) w)) =
        fieldOneFiniteAdeleLocalUnitCharacter v
          ((algebraMap ℚ FieldOneFiniteAdele q) v) :=
      finsum_eq_single
        (fun w : HeightOneSpectrum ℤ =>
          fieldOneFiniteAdeleLocalUnitCharacter w
            ((algebraMap ℚ FieldOneFiniteAdele q) w))
        v
        (fun w hw => by
          apply
            fieldOneFiniteAdeleLocalUnitCharacter_vanishes_on_integers
          rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
          exact
            fieldOneFiniteAdele_algebraMap_int_div_pow_mem_integers_of_ne
              hw m n)
    _ = fieldOneRationalUnitAddCircleCharacter q := by
      rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
      exact
        fieldOneFiniteAdeleLocalUnitCharacter_algebraMap_int_div_pow
          v m n

/-- Additive-circle character on `ℝ × 𝔸_f` with the archimedean sign chosen
to cancel the finite standard character on diagonal rationals. -/
noncomputable def fieldOneSemilocalStandardUnitAddCircleCharacter :
    (ℝ × FieldOneFiniteAdele) →+ UnitAddCircle where
  toFun x :=
    -((x.1 : ℝ) : UnitAddCircle) +
      fieldOneFiniteAdeleStandardUnitAddCircleCharacter x.2
  map_zero' := by simp
  map_add' x y := by
    change
      -(((x.1 + y.1 : ℝ)) : UnitAddCircle) +
          fieldOneFiniteAdeleStandardUnitAddCircleCharacter
            (x.2 + y.2) =
        (-((x.1 : ℝ) : UnitAddCircle) +
            fieldOneFiniteAdeleStandardUnitAddCircleCharacter x.2) +
          (-((y.1 : ℝ) : UnitAddCircle) +
            fieldOneFiniteAdeleStandardUnitAddCircleCharacter y.2)
    rw [show
      (((x.1 + y.1 : ℝ)) : UnitAddCircle) =
        ((x.1 : ℝ) : UnitAddCircle) +
          ((y.1 : ℝ) : UnitAddCircle) by rfl,
      map_add]
    abel

theorem fieldOneSemilocalStandardUnitAddCircleCharacter_diagonal_int_div_pow
    (v : HeightOneSpectrum ℤ) (m : ℤ) (n : ℕ) :
    fieldOneSemilocalStandardUnitAddCircleCharacter
        ((((m : ℚ) /
          (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n : ℚ) : ℝ),
          algebraMap ℚ FieldOneFiniteAdele
            ((m : ℚ) /
              (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n)) = 0 := by
  change
    -(((((m : ℚ) /
      (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n : ℚ) : ℝ)) :
        UnitAddCircle) +
      fieldOneFiniteAdeleStandardUnitAddCircleCharacter
        (algebraMap ℚ FieldOneFiniteAdele
          ((m : ℚ) /
            (Rat.HeightOneSpectrum.primesEquiv v : ℚ) ^ n)) = 0
  rw [
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter_algebraMap_int_div_pow]
  exact neg_add_cancel _

end

end GaloisForLFunctions.RHTower
