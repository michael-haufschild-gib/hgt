/-
# Euclidean algorithm for Bourgain's Eisenstein integers

Division rounds the two rational coefficients of `x / y` in the basis
`(1,ω)`.  The coefficient errors lie in `[-1/2,1/2]`, where the Eisenstein
norm `a²-ab+b²` is at most `3/4`.  Hence every nonzero divisor has a
strictly smaller remainder.
-/
import GaloisForLFunctions.RHTower.BourgainEisensteinInt
import Mathlib.Algebra.EuclideanDomain.Int

namespace RHTower.BourgainEisensteinInt

/-- Nearest-lattice-point quotient in the basis `(1,ω)`. -/
instance instDiv : Div BourgainEisensteinInt :=
  ⟨fun x y =>
    ⟨round (((x * conj y).re : ℚ) / norm y),
      round (((x * conj y).im : ℚ) / norm y)⟩⟩

theorem div_def (x y : BourgainEisensteinInt) :
    x / y =
      ⟨round (((x * conj y).re : ℚ) / norm y),
        round (((x * conj y).im : ℚ) / norm y)⟩ :=
  rfl

/-- The Eisenstein norm of two simultaneous rounding errors is `< 1`. -/
theorem rounding_error_norm_lt_one (a b : ℚ) :
    (a - round a) ^ (2 : ℕ) -
          (a - round a) * (b - round b) +
          (b - round b) ^ (2 : ℕ) < 1 := by
  have ha : |a - round a| ≤ (1 / 2 : ℚ) := by
    simpa using abs_sub_round a
  have hb : |b - round b| ≤ (1 / 2 : ℚ) := by
    simpa using abs_sub_round b
  have ha2 :
      (a - round a) ^ (2 : ℕ) ≤ (1 / 2 : ℚ) ^ (2 : ℕ) :=
    sq_le_sq.mpr (by
      simpa only [abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2)]
        using ha)
  have hb2 :
      (b - round b) ^ (2 : ℕ) ≤ (1 / 2 : ℚ) ^ (2 : ℕ) :=
    sq_le_sq.mpr (by
      simpa only [abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2)]
        using hb)
  nlinarith [sq_nonneg ((a - round a) + (b - round b))]

/-- Denominator-free norm identity behind Euclidean division. -/
theorem norm_sub_mul_mul_norm
    (x y q : BourgainEisensteinInt) :
    norm (x - y * q) * norm y =
      ((x * conj y).re - norm y * q.re) ^ (2 : ℕ) -
        ((x * conj y).re - norm y * q.re) *
          ((x * conj y).im - norm y * q.im) +
        ((x * conj y).im - norm y * q.im) ^ (2 : ℕ) := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases q with ⟨m, n⟩
  simp only [norm, conj, sub_eq_add_neg, re_add, im_add, re_neg,
    im_neg, re_mul, im_mul]
  ring

/-- Exact rational identity comparing a remainder norm to coefficient
rounding errors. -/
theorem norm_sub_mul_div
    (x y q : BourgainEisensteinInt) (hy : y ≠ 0) :
    (norm (x - y * q) : ℚ) / norm y =
      ((((x * conj y).re : ℚ) / norm y) - q.re) ^ (2 : ℕ) -
        ((((x * conj y).re : ℚ) / norm y) - q.re) *
          ((((x * conj y).im : ℚ) / norm y) - q.im) +
        ((((x * conj y).im : ℚ) / norm y) - q.im) ^ (2 : ℕ) := by
  have hnorm : (norm y : ℚ) ≠ 0 := by
    exact_mod_cast (mt norm_eq_zero.mp hy)
  have hpoly := norm_sub_mul_mul_norm x y q
  have hpolyQ :
      (norm (x - y * q) : ℚ) * norm y =
        (((x * conj y).re : ℚ) - norm y * q.re) ^ (2 : ℕ) -
          (((x * conj y).re : ℚ) - norm y * q.re) *
            (((x * conj y).im : ℚ) - norm y * q.im) +
          (((x * conj y).im : ℚ) - norm y * q.im) ^ (2 : ℕ) := by
    exact_mod_cast hpoly
  field_simp [hnorm]
  nlinarith

instance instMod : Mod BourgainEisensteinInt :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : BourgainEisensteinInt) :
    x % y = x - y * (x / y) :=
  rfl

/-- Euclidean remainder strictly decreases the positive-definite norm. -/
theorem norm_mod_lt (x : BourgainEisensteinInt)
    {y : BourgainEisensteinInt} (hy : y ≠ 0) :
    norm (x % y) < norm y := by
  let a : ℚ := ((x * conj y).re : ℚ) / norm y
  let b : ℚ := ((x * conj y).im : ℚ) / norm y
  have herr := rounding_error_norm_lt_one a b
  have hqre : ((x / y).re : ℚ) = round a := by
    rw [div_def]
  have hqim : ((x / y).im : ℚ) = round b := by
    rw [div_def]
  have hratio :
      (norm (x % y) : ℚ) / norm y =
        (a - round a) ^ (2 : ℕ) -
          (a - round a) * (b - round b) +
          (b - round b) ^ (2 : ℕ) := by
    rw [mod_def, norm_sub_mul_div x y (x / y) hy]
    rw [← hqre, ← hqim]
  have hnormpos : (0 : ℚ) < norm y := by
    exact_mod_cast norm_pos.mpr hy
  have hratio_lt : (norm (x % y) : ℚ) / norm y < 1 := by
    rw [hratio]
    exact herr
  have hlt : (norm (x % y) : ℚ) < norm y :=
    (div_lt_one hnormpos).mp hratio_lt
  exact_mod_cast hlt

theorem intCast_natAbs_norm (x : BourgainEisensteinInt) :
    ((norm x).natAbs : ℤ) = norm x := by
  exact Int.natAbs_of_nonneg (norm_nonneg x)

theorem natAbs_norm_mod_lt (x : BourgainEisensteinInt)
    {y : BourgainEisensteinInt} (hy : y ≠ 0) :
    (norm (x % y)).natAbs < (norm y).natAbs := by
  apply Int.ofNat_lt.mp
  rw [intCast_natAbs_norm, intCast_natAbs_norm]
  exact norm_mod_lt x hy

theorem norm_le_norm_mul_left (x : BourgainEisensteinInt)
    {y : BourgainEisensteinInt} (hy : y ≠ 0) :
    (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [norm_mul, Int.natAbs_mul]
  have hyone : 1 ≤ (norm y).natAbs := by
    apply Int.ofNat_le.mp
    rw [intCast_natAbs_norm]
    exact Int.add_one_le_of_lt (norm_pos.mpr hy)
  exact le_mul_of_one_le_right (Nat.zero_le _) hyone

/-- Eisenstein integers form a Euclidean domain. -/
instance instEuclideanDomain : EuclideanDomain BourgainEisensteinInt :=
  { instCommRing,
    instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro x
      ext <;> simp [div_def]
    quotient_mul_add_remainder_eq := by
      intro x y
      simp [mod_def]
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun x _ hy =>
      not_lt_of_ge (norm_le_norm_mul_left x hy) }

end RHTower.BourgainEisensteinInt
