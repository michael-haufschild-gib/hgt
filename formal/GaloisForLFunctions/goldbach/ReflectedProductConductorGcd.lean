import GaloisForLFunctions.goldbach.ReflectedProductConductor

/-!
# The gcd carried by a reflected product conductor

Factoring the gcd with the dilation step separates the residue gcd into
an exact common factor and a reduced determinant. The reduced Bézout
identity removes the inverse coefficient without a coprimality premise.
-/

namespace GaloisForLFunctions.Goldbach

noncomputable section
set_option autoImplicit false

/-- Factoring the actual gcd removes the coprime part of a product modulus. -/
theorem gcd_product_eq_gcd_mul_quotient (v : ℤ) (c : ℕ+) (b : ℤ) :
    Int.gcd v ((c : ℤ) * b) =
      Int.gcd v (c : ℤ) * Int.gcd (v / (Int.gcd v (c : ℤ) : ℤ)) b := by
  have hc : (c : ℤ) ≠ 0 := by exact_mod_cast c.pos.ne'
  have hg : 0 < Int.gcd v (c : ℤ) := Int.gcd_pos_of_ne_zero_right v hc
  have hv : (Int.gcd v (c : ℤ) : ℤ) * (v / (Int.gcd v (c : ℤ) : ℤ)) = v := by
    simpa only [mul_comm] using Int.ediv_mul_cancel (Int.gcd_dvd_left v (c : ℤ))
  have hcf : (Int.gcd v (c : ℤ) : ℤ) *
      ((c : ℤ) / (Int.gcd v (c : ℤ) : ℤ)) = (c : ℤ) := by
    simpa only [mul_comm] using Int.ediv_mul_cancel (Int.gcd_dvd_right v (c : ℤ))
  calc
    Int.gcd v ((c : ℤ) * b) =
        Int.gcd ((Int.gcd v (c : ℤ) : ℤ) * (v / (Int.gcd v (c : ℤ) : ℤ)))
          ((Int.gcd v (c : ℤ) : ℤ) * (((c : ℤ) / (Int.gcd v (c : ℤ) : ℤ)) * b)) := by
      rw [hv, ← mul_assoc, hcf]
    _ = Int.gcd v (c : ℤ) *
        Int.gcd (v / (Int.gcd v (c : ℤ) : ℤ))
          (((c : ℤ) / (Int.gcd v (c : ℤ) : ℤ)) * b) := by
      rw [Int.gcd_mul_left, Int.natAbs_natCast]
    _ = _ := by rw [Int.gcd_mul_right_right_of_gcd_eq_one (Int.gcd_ediv_gcd_ediv_gcd hg)]

/-- Bézout reflection preserves an explicit reduced determinant gcd for every integer target. -/
theorem bezoutReflection_gcd (c : ℕ+) (a : ℕ) (y : ℕ+) (T t : ℤ) :
    Int.gcd (T - (c : ℤ) * Int.gcdA (a : ℤ) (y : ℤ) * t)
        ((c : ℤ) * (linearCongruenceModulus a y : ℤ)) =
      Int.gcd T (c : ℤ) *
        Int.gcd (((a / Nat.gcd a (y : ℕ) : ℕ) : ℤ) *
          (T / (Int.gcd T (c : ℤ) : ℤ)) -
            ((c : ℤ) / (Int.gcd T (c : ℤ) : ℤ)) * t)
          (linearCongruenceModulus a y : ℤ) := by
  let A : ℤ := T - (c : ℤ) * Int.gcdA (a : ℤ) (y : ℤ) * t
  let d : ℕ := Int.gcd T (c : ℤ)
  let a₀ : ℤ := ((a / Nat.gcd a (y : ℕ) : ℕ) : ℤ)
  let b : ℤ := (linearCongruenceModulus a y : ℤ)
  let α : ℤ := Int.gcdA (a : ℤ) (y : ℤ)
  let β : ℤ := Int.gcdB (a : ℤ) (y : ℤ)
  let T₀ : ℤ := T / (d : ℤ)
  let c₀ : ℤ := (c : ℤ) / (d : ℤ)
  have hAc : Int.gcd A (c : ℤ) = d := by
    dsimp [A, d]
    rw [mul_assoc, Int.gcd_sub_mul_left_left]
  have hc : (c : ℤ) ≠ 0 := by exact_mod_cast c.pos.ne'
  have hd : (d : ℤ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_right T hc).ne'
  have hT : (d : ℤ) * T₀ = T := by
    simpa only [mul_comm] using Int.ediv_mul_cancel (Int.gcd_dvd_left T (c : ℤ))
  have hcf : (d : ℤ) * c₀ = (c : ℤ) := by
    simpa only [mul_comm] using Int.ediv_mul_cancel (Int.gcd_dvd_right T (c : ℤ))
  have hdA : (d : ℤ) ∣ A := by
    rw [← hAc]
    exact Int.gcd_dvd_left A (c : ℤ)
  have hAf : (d : ℤ) * (A / (d : ℤ)) = A := by
    simpa only [mul_comm] using Int.ediv_mul_cancel hdA
  have hA : A / (d : ℤ) = T₀ - c₀ * α * t := by
    apply mul_left_cancel₀ hd
    calc
      _ = A := hAf
      _ = (d : ℤ) * (T₀ - c₀ * α * t) := by
        dsimp only [A, α]
        rw [mul_sub, hT, ← mul_assoc, ← mul_assoc, hcf]
  have hbez : a₀ * α + b * β = 1 := linearCongruence_reduced_bezout a y
  have hab : Int.gcd a₀ b = 1 :=
    Nat.dvd_one.mp (Int.gcd_dvd_iff.mpr ⟨α, β, hbez.symm⟩)
  have hdet : a₀ * T₀ - c₀ * t = a₀ * (A / (d : ℤ)) - b * (c₀ * β * t) := by
    rw [hA]
    linear_combination c₀ * t * hbez
  change Int.gcd A ((c : ℤ) * b) = d * Int.gcd (a₀ * T₀ - c₀ * t) b
  rw [gcd_product_eq_gcd_mul_quotient, hAc, hdet,
    Int.gcd_sub_mul_left_left, Int.gcd_mul_right_left_of_gcd_eq_one hab]

/-- The reduced determinant uses only target, slopes, and their actual gcd divisors. -/
def reflectedRowReducedDeterminant (p h : ℕ+) (q : ℕ) (y : ℕ+) (T : ℤ) : ℤ :=
  let g : ℕ := Nat.gcd (q * (h : ℕ)) (y : ℕ)
  let d : ℤ := (Int.gcd T ((p : ℤ) * (h : ℤ)) : ℤ)
  (((q * (h : ℕ)) / g : ℕ) : ℤ) * (T / d) -
    (((p : ℤ) * (h : ℤ)) / d) * (T / (g : ℤ))

/-- The exact residue gcd retains every nonunit row and removes the Bézout inverse. -/
theorem reflectedRow_gcd_eq_reducedDeterminant
    (p h : ℕ+) (q : ℕ) (y : ℕ+) (T : ℤ) :
    Int.gcd (reflectedRowResidue p h q y T) (reflectedRowModulus p h q y : ℤ) =
      Int.gcd T ((p : ℤ) * (h : ℤ)) *
        Int.gcd (reflectedRowReducedDeterminant p h q y T)
          (linearCongruenceModulus (q * (h : ℕ)) y : ℤ) := by
  have hcast : ((p * h : ℕ+) : ℤ) = (p : ℤ) * (h : ℤ) := by
    change (((p : ℕ) * (h : ℕ) : ℕ) : ℤ) = _
    exact Nat.cast_mul _ _
  have hmod : (reflectedRowModulus p h q y : ℤ) =
      ((p : ℤ) * (h : ℤ)) * (linearCongruenceModulus (q * (h : ℕ)) y : ℤ) := by
    change (((p : ℕ) * (h : ℕ) * (linearCongruenceModulus (q * (h : ℕ)) y : ℕ) : ℕ) : ℤ) = _
    simp only [Nat.cast_mul]
  have he := bezoutReflection_gcd (p * h) (q * (h : ℕ)) y T
    (T / (Nat.gcd (q * (h : ℕ)) (y : ℕ) : ℤ))
  rw [hcast] at he
  rw [hmod]
  simpa only [reflectedRowResidue, linearCongruenceResidue,
    reflectedRowReducedDeterminant, mul_assoc] using he

end
end GaloisForLFunctions.Goldbach
