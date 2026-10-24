import GaloisForLFunctions.goldbach.ReflectedProductDeterminant

/-!
# The exact conductor of a reflected product row

Bézout reduction retains the compatibility divisor of the row. The remaining
parameter occupies one residue class modulo the quotient modulus, so its
reflected product has conductor `p * h * y / gcd(q * h,y)`.
-/

namespace GaloisForLFunctions.Goldbach

noncomputable section
set_option autoImplicit false

/-- The exact period after dividing a linear congruence by its common gcd. -/
def linearCongruenceModulus (a : ℕ) (y : ℕ+) : ℕ+ :=
  ⟨(y : ℕ) / Nat.gcd a (y : ℕ),
    Nat.div_pos (Nat.le_of_dvd y.pos (Nat.gcd_dvd_right a (y : ℕ)))
      (Nat.gcd_pos_of_pos_right a y.pos)⟩

/-- The particular integer solution selected by the actual Bézout coefficient. -/
def linearCongruenceResidue (a : ℕ) (y : ℕ+) (T : ℤ) : ℤ :=
  Int.gcdA (a : ℤ) (y : ℤ) * (T / (Nat.gcd a (y : ℕ) : ℤ))

private theorem linear_gcd_factor_a (a : ℕ) (y : ℕ+) :
    (Nat.gcd a (y : ℕ) : ℤ) * ((a / Nat.gcd a (y : ℕ) : ℕ) : ℤ) = (a : ℤ) := by
  exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left a (y : ℕ))

private theorem linear_gcd_factor_y (a : ℕ) (y : ℕ+) :
    (Nat.gcd a (y : ℕ) : ℤ) * (linearCongruenceModulus a y : ℤ) = (y : ℤ) := by
  change (Nat.gcd a (y : ℕ) : ℤ) * (((y : ℕ) / Nat.gcd a (y : ℕ) : ℕ) : ℤ) = _
  exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right a (y : ℕ))

/-- The original Bézout coefficients give a unit relation for the two reduced integers. -/
theorem linearCongruence_reduced_bezout (a : ℕ) (y : ℕ+) :
    ((a / Nat.gcd a (y : ℕ) : ℕ) : ℤ) * Int.gcdA (a : ℤ) (y : ℤ) +
      (linearCongruenceModulus a y : ℤ) * Int.gcdB (a : ℤ) (y : ℤ) = 1 := by
  have hg : (Nat.gcd a (y : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_right a y.pos).ne'
  have hb := Int.gcd_eq_gcd_ab (a : ℤ) (y : ℤ)
  change (Nat.gcd a (y : ℕ) : ℤ) =
    (a : ℤ) * Int.gcdA (a : ℤ) (y : ℤ) +
      (y : ℤ) * Int.gcdB (a : ℤ) (y : ℤ) at hb
  apply mul_left_cancel₀ hg
  calc
    _ = (a : ℤ) * Int.gcdA (a : ℤ) (y : ℤ) +
        (y : ℤ) * Int.gcdB (a : ℤ) (y : ℤ) := by
      rw [mul_add, ← mul_assoc, linear_gcd_factor_a, ← mul_assoc, linear_gcd_factor_y]
    _ = (Nat.gcd a (y : ℕ) : ℤ) := hb.symm
    _ = _ := by ring

/-- The complete solution class, including the compatibility divisor and zero slope. -/
theorem linearCongruence_iff_gcd_and_residue (a : ℕ) (y : ℕ+) (T s : ℤ) :
    Int.ModEq (y : ℤ) ((a : ℤ) * s) T ↔
      (Nat.gcd a (y : ℕ) : ℤ) ∣ T ∧
        Int.ModEq (linearCongruenceModulus a y : ℤ) (linearCongruenceResidue a y T) s := by
  let g : ℕ := Nat.gcd a (y : ℕ)
  let a₀ : ℤ := ((a / g : ℕ) : ℤ)
  let b : ℤ := (linearCongruenceModulus a y : ℤ)
  let α : ℤ := Int.gcdA (a : ℤ) (y : ℤ)
  let β : ℤ := Int.gcdB (a : ℤ) (y : ℤ)
  let t : ℤ := T / (g : ℤ)
  have hg : (g : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_right a y.pos).ne'
  have ha : (g : ℤ) * a₀ = (a : ℤ) := linear_gcd_factor_a a y
  have hy : (g : ℤ) * b = (y : ℤ) := linear_gcd_factor_y a y
  have hbez : a₀ * α + b * β = 1 := linearCongruence_reduced_bezout a y
  simp only [Int.modEq_iff_dvd]
  change (y : ℤ) ∣ T - (a : ℤ) * s ↔ (g : ℤ) ∣ T ∧ b ∣ s - α * t
  constructor
  · rintro ⟨k, hk⟩
    have hTdiv : (g : ℤ) ∣ T := by
      refine ⟨a₀ * s + b * k, ?_⟩
      calc
        T = (a : ℤ) * s + (y : ℤ) * k := by linear_combination hk
        _ = (g : ℤ) * (a₀ * s + b * k) := by rw [← ha, ← hy]; ring
    have hT : (g : ℤ) * t = T := by
      simpa only [mul_comm] using Int.ediv_mul_cancel hTdiv
    have hred : t - a₀ * s = b * k := by
      apply mul_left_cancel₀ hg
      calc
        _ = T - (a : ℤ) * s := by rw [mul_sub, hT, ← mul_assoc, ha]
        _ = (y : ℤ) * k := hk
        _ = _ := by rw [← hy]; ring
    refine ⟨hTdiv, β * s - α * k, ?_⟩
    linear_combination -s * hbez - α * hred
  · rintro ⟨hTdiv, l, hl⟩
    have hT : (g : ℤ) * t = T := by
      simpa only [mul_comm] using Int.ediv_mul_cancel hTdiv
    have hred : t - a₀ * s = b * (β * t - a₀ * l) := by
      linear_combination -t * hbez - a₀ * hl
    refine ⟨β * t - a₀ * l, ?_⟩
    calc
      T - (a : ℤ) * s = (g : ℤ) * (t - a₀ * s) := by rw [mul_sub, hT, ← mul_assoc, ha]
      _ = (y : ℤ) * (β * t - a₀ * l) := by rw [hred, ← mul_assoc, hy]

/-- The full reflected-product conductor, including the noncoprime row quotient. -/
def reflectedRowModulus (p h : ℕ+) (q : ℕ) (y : ℕ+) : ℕ+ :=
  ⟨(p : ℕ) * (h : ℕ) * (linearCongruenceModulus (q * (h : ℕ)) y : ℕ),
    Nat.mul_pos (Nat.mul_pos p.pos h.pos) (linearCongruenceModulus _ y).pos⟩

/-- The actual residue selected by the Bézout solution of the second row equation. -/
def reflectedRowResidue (p h : ℕ+) (q : ℕ) (y : ℕ+) (T : ℤ) : ℤ :=
  T - (p : ℤ) * (h : ℤ) * linearCongruenceResidue (q * (h : ℕ)) y T

private theorem reflectedRowModulus_cast (p h : ℕ+) (q : ℕ) (y : ℕ+) :
    (reflectedRowModulus p h q y : ℤ) =
      (p : ℤ) * (h : ℤ) * (linearCongruenceModulus (q * (h : ℕ)) y : ℤ) := by
  change (((p : ℕ) * (h : ℕ) * (linearCongruenceModulus (q * (h : ℕ)) y : ℕ) : ℕ) : ℤ) = _
  simp only [Nat.cast_mul]

/-- Two reflected row equations are exactly one compatibility divisor and one product residue. -/
theorem reflectedRow_iff_conductor (p h : ℕ+) (q : ℕ) (y : ℕ+) (T u : ℤ) :
    (∃ r z : ℤ, (h : ℤ) ∣ r ∧ u + (p : ℤ) * r = T ∧
      (y : ℤ) * z + (q : ℤ) * r = T) ↔
      (Nat.gcd (q * (h : ℕ)) (y : ℕ) : ℤ) ∣ T ∧
        Int.ModEq (reflectedRowModulus p h q y : ℤ) (reflectedRowResidue p h q y T) u := by
  constructor
  · rintro ⟨r, z, ⟨s, hs⟩, hu, hz⟩
    have hlin : Int.ModEq (y : ℤ) (((q * (h : ℕ) : ℕ) : ℤ) * s) T := by
      rw [Int.modEq_iff_dvd]
      refine ⟨z, ?_⟩
      rw [hs] at hz
      push_cast
      linear_combination -hz
    obtain ⟨hg, hb⟩ := (linearCongruence_iff_gcd_and_residue (q * (h : ℕ)) y T s).mp hlin
    rcases Int.modEq_iff_dvd.mp hb with ⟨k, hk⟩
    refine ⟨hg, Int.modEq_iff_dvd.mpr ⟨-k, ?_⟩⟩
    rw [reflectedRowModulus_cast, reflectedRowResidue]
    rw [hs] at hu
    linear_combination hu - (p : ℤ) * (h : ℤ) * hk
  · rintro ⟨hg, hu⟩
    rcases Int.modEq_iff_dvd.mp hu with ⟨k, hk⟩
    let s : ℤ := linearCongruenceResidue (q * (h : ℕ)) y T -
      (linearCongruenceModulus (q * (h : ℕ)) y : ℤ) * k
    have hb : Int.ModEq (linearCongruenceModulus (q * (h : ℕ)) y : ℤ)
        (linearCongruenceResidue (q * (h : ℕ)) y T) s := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-k, by dsimp [s]; ring⟩
    have hlin := (linearCongruence_iff_gcd_and_residue (q * (h : ℕ)) y T s).mpr ⟨hg, hb⟩
    rcases Int.modEq_iff_dvd.mp hlin with ⟨z, hz⟩
    refine ⟨(h : ℤ) * s, z, ⟨s, rfl⟩, ?_, ?_⟩
    · rw [reflectedRowResidue, reflectedRowModulus_cast] at hk
      dsimp [s]
      linear_combination hk
    · push_cast at hz
      linear_combination -hz

/-- The compatible reflected row contains exactly one parameter and one second-row value. -/
theorem reflectedRow_existsUnique_iff_conductor
    (p h : ℕ+) (q : ℕ) (y : ℕ+) (T u : ℤ) :
    (∃! w : ℤ × ℤ, (h : ℤ) ∣ w.1 ∧ u + (p : ℤ) * w.1 = T ∧
      (y : ℤ) * w.2 + (q : ℤ) * w.1 = T) ↔
      (Nat.gcd (q * (h : ℕ)) (y : ℕ) : ℤ) ∣ T ∧
        Int.ModEq (reflectedRowModulus p h q y : ℤ) (reflectedRowResidue p h q y T) u := by
  constructor
  · rintro ⟨w, hw, _⟩
    exact (reflectedRow_iff_conductor p h q y T u).mp ⟨w.1, w.2, hw⟩
  · intro hc
    obtain ⟨r, z, hr, hu, hz⟩ := (reflectedRow_iff_conductor p h q y T u).mpr hc
    refine ⟨(r, z), ⟨hr, hu, hz⟩, ?_⟩
    rintro ⟨r', z'⟩ ⟨_, hu', hz'⟩
    have hp : (p : ℤ) ≠ 0 := by exact_mod_cast p.pos.ne'
    have hy : (y : ℤ) ≠ 0 := by exact_mod_cast y.pos.ne'
    have hr' : r' = r := by
      apply mul_left_cancel₀ hp
      linear_combination hu' - hu
    have hzeq : z' = z := by
      rw [hr'] at hz'
      apply mul_left_cancel₀ hy
      linear_combination hz' - hz
    exact Prod.ext hr' hzeq

/-- Both finite endpoints survive the passage to the actual row conductor and hyperbolic strip. -/
theorem reflectedRow_bounded_iff_conductor
    (p h : ℕ+) (q : ℕ) (y : ℕ+) (T u X R : ℤ) :
    (∃ r z : ℤ, 0 < r ∧ r ≤ R ∧ (h : ℤ) ∣ r ∧ X < z ∧ z ≤ 2 * X ∧
      u + (p : ℤ) * r = T ∧ (y : ℤ) * z + (q : ℤ) * r = T) ↔
      (Nat.gcd (q * (h : ℕ)) (y : ℕ) : ℤ) ∣ T ∧
        Int.ModEq (reflectedRowModulus p h q y : ℤ) (reflectedRowResidue p h q y T) u ∧
          0 < T - u ∧ T - u ≤ R * (p : ℤ) ∧
            T * ((q : ℤ) - (p : ℤ)) + X * ((p : ℤ) * (y : ℤ)) < (q : ℤ) * u ∧
              (q : ℤ) * u ≤ T * ((q : ℤ) - (p : ℤ)) + (2 * X) * ((p : ℤ) * (y : ℤ)) := by
  have hpy : (0 : ℤ) < (p : ℤ) * (y : ℤ) := by
    exact mul_pos (by exact_mod_cast p.pos) (by exact_mod_cast y.pos)
  constructor
  · rintro ⟨r, z, hr, hR, hh, hzlo, hzhi, hu, hz⟩
    have hc := (reflectedRow_iff_conductor p h q y T u).mp ⟨r, z, hh, hu, hz⟩
    have hd := (reflectedValues_determinant_iff p (q : ℤ) (h : ℤ) T R u ((y : ℤ) * z)).mp
      ⟨r, hr, hR, hh, hu, hz⟩
    have he : (q : ℤ) * u = T * ((q : ℤ) - (p : ℤ)) + z * ((p : ℤ) * (y : ℤ)) := by
      linear_combination hd.1
    refine ⟨hc.1, hc.2, hd.2.2.1, hd.2.2.2, ?_, ?_⟩
    · have hm := (mul_lt_mul_iff_left₀ hpy).mpr hzlo
      linarith only [he, hm]
    · have hm := (mul_le_mul_iff_left₀ hpy).mpr hzhi
      linarith only [he, hm]
  · rintro ⟨hg, hc, hpos, hR, hlo, hhi⟩
    obtain ⟨r, z, hh, hu, hz⟩ := (reflectedRow_iff_conductor p h q y T u).mpr ⟨hg, hc⟩
    have hd : (q : ℤ) * u - (p : ℤ) * ((y : ℤ) * z) =
        T * ((q : ℤ) - (p : ℤ)) := by
      linear_combination (q : ℤ) * hu - (p : ℤ) * hz
    have hm : Int.ModEq ((p : ℤ) * (h : ℤ)) u T := by
      rw [Int.modEq_iff_dvd]
      rcases hh with ⟨s, hs⟩
      refine ⟨s, ?_⟩
      rw [hs] at hu
      linear_combination -hu
    obtain ⟨r', hr', hR', hh', hu', hz'⟩ :=
      (reflectedValues_determinant_iff p (q : ℤ) (h : ℤ) T R u ((y : ℤ) * z)).mpr
        ⟨hd, hm, hpos, hR⟩
    have he : (q : ℤ) * u = T * ((q : ℤ) - (p : ℤ)) + z * ((p : ℤ) * (y : ℤ)) := by
      linear_combination hd
    refine ⟨r', z, hr', hR', hh', ?_, ?_, hu', hz'⟩
    · apply (mul_lt_mul_iff_left₀ hpy).mp
      linarith only [he, hlo]
    · apply (mul_le_mul_iff_left₀ hpy).mp
      linarith only [he, hhi]

end
end GaloisForLFunctions.Goldbach
