/-
# Primitivity of coprime lifted Dirichlet-character products

For primitive characters at coprime positive levels, their lifts to the product
level have a primitive product. The proof is conductor-theoretic: factor the
product through its conductor, cancel either lifted factor, and force each
coprime level divisor back into that conductor.
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic

noncomputable section

namespace RHTower

open DirichletCharacter

variable {K : Type*} [CommRing K] {n m : ℕ}

/-- The conductor of a product of lifted characters retains the original level
of its primitive first factor when the two source levels are coprime.  The
target level and its two lift certificates are explicit, so CRT constructions
can use this theorem without proof-indexed `changeLevel` coercion issues. -/
theorem lifted_coprime_product_left_conductor_dvd_at_level {N : ℕ} [NeZero N]
    (χ : DirichletCharacter K n) (ψ : DirichletCharacter K m) (hcop : n.Coprime m)
    (hχ : χ.IsPrimitive) (hn : n ∣ N) (hm : m ∣ N) :
    n ∣ ((χ.changeLevel hn) * (ψ.changeLevel hm)).conductor := by
  let χN : DirichletCharacter K N := χ.changeLevel hn
  let ψN : DirichletCharacter K N := ψ.changeLevel hm
  let θ : DirichletCharacter K N := χN * ψN
  change n ∣ θ.conductor
  let c := θ.conductor
  have hcN : c ∣ N := by
    exact DirichletCharacter.conductor_dvd_level θ
  have hL : c.lcm m ∣ N := Nat.lcm_dvd hcN hm
  let η : DirichletCharacter K (c.lcm m) := θ.primitiveCharacter.mul ψ⁻¹
  have hη : η.changeLevel hL = χN := by
    dsimp [η]
    rw [DirichletCharacter.mul, MonoidHom.map_mul, ← DirichletCharacter.changeLevel_trans,
      ← DirichletCharacter.changeLevel_trans, DirichletCharacter.changeLevel_primitiveCharacter]
    simp only [χN, ψN, θ, map_inv, mul_inv_cancel_right]
  have hχNfac : χN.FactorsThrough (c.lcm m) := ⟨hL, η, hη.symm⟩
  have hnL : n ∣ c.lcm m := by
    rw [← hχ, ← DirichletCharacter.conductor_changeLevel χ hn]
    exact DirichletCharacter.conductor_dvd_of_mem_conductorSet χN hχNfac
  exact hcop.dvd_of_dvd_mul_right (dvd_trans hnL (Nat.lcm_dvd_mul c m))

variable [NeZero n] [NeZero m]

/-- The conductor of a product of a lifted primitive character with a coprime-level
character contains the primitive character's original level. -/
theorem lifted_coprime_product_left_conductor_dvd (χ : DirichletCharacter K n)
    (ψ : DirichletCharacter K m) (hcop : n.Coprime m)
    (hχ : χ.IsPrimitive) :
    n ∣ ((χ.changeLevel (n.dvd_mul_right m)) *
      (ψ.changeLevel (m.dvd_mul_left n))).conductor := by
  let χN : DirichletCharacter K (n * m) := χ.changeLevel (n.dvd_mul_right m)
  let ψN : DirichletCharacter K (n * m) := ψ.changeLevel (m.dvd_mul_left n)
  let θ : DirichletCharacter K (n * m) := χN * ψN
  change n ∣ θ.conductor
  let c := θ.conductor
  have hcN : c ∣ n * m := by
    exact DirichletCharacter.conductor_dvd_level θ
  have hL : c.lcm m ∣ n * m := Nat.lcm_dvd hcN (m.dvd_mul_left n)
  let η : DirichletCharacter K (c.lcm m) := θ.primitiveCharacter.mul ψ⁻¹
  have hη : η.changeLevel hL = χN := by
    dsimp [η]
    rw [DirichletCharacter.mul, MonoidHom.map_mul, ← DirichletCharacter.changeLevel_trans,
      ← DirichletCharacter.changeLevel_trans, DirichletCharacter.changeLevel_primitiveCharacter]
    simp only [χN, ψN, θ, map_inv, mul_inv_cancel_right]
  have hχNfac : χN.FactorsThrough (c.lcm m) := ⟨hL, η, hη.symm⟩
  have hnL : n ∣ c.lcm m := by
    rw [← hχ, ← DirichletCharacter.conductor_changeLevel χ (n.dvd_mul_right m)]
    exact DirichletCharacter.conductor_dvd_of_mem_conductorSet χN hχNfac
  exact hcop.dvd_of_dvd_mul_right (dvd_trans hnL (Nat.lcm_dvd_mul c m))

/-- Lifting primitive coprime characters to their product level and multiplying them is primitive. -/
theorem lifted_coprime_product_isPrimitive (χ : DirichletCharacter K n)
    (ψ : DirichletCharacter K m) (hcop : n.Coprime m)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) :
    ((χ.changeLevel (n.dvd_mul_right m)) * (ψ.changeLevel (m.dvd_mul_left n))).IsPrimitive := by
  let χN : DirichletCharacter K (n * m) := χ.changeLevel (n.dvd_mul_right m)
  let ψN : DirichletCharacter K (n * m) := ψ.changeLevel (m.dvd_mul_left n)
  let θ : DirichletCharacter K (n * m) := χN * ψN
  rw [DirichletCharacter.isPrimitive_def]
  change θ.conductor = n * m
  let c := θ.conductor
  have hcN : c ∣ n * m := by
    exact DirichletCharacter.conductor_dvd_level θ
  have hL : c.lcm m ∣ n * m := Nat.lcm_dvd hcN (m.dvd_mul_left n)
  let η : DirichletCharacter K (c.lcm m) := θ.primitiveCharacter.mul ψ⁻¹
  have hη : η.changeLevel hL = χN := by
    dsimp [η]
    rw [DirichletCharacter.mul, MonoidHom.map_mul, ← DirichletCharacter.changeLevel_trans,
      ← DirichletCharacter.changeLevel_trans, DirichletCharacter.changeLevel_primitiveCharacter]
    simp only [χN, ψN, θ, map_inv, mul_inv_cancel_right]
  have hχNfac : χN.FactorsThrough (c.lcm m) := ⟨hL, η, hη.symm⟩
  have hnL : n ∣ c.lcm m := by
    rw [← hχ, ← DirichletCharacter.conductor_changeLevel χ (n.dvd_mul_right m)]
    exact DirichletCharacter.conductor_dvd_of_mem_conductorSet χN hχNfac
  have hnC : n ∣ c := hcop.dvd_of_dvd_mul_right
    (dvd_trans hnL (Nat.lcm_dvd_mul c m))
  have hL' : c.lcm n ∣ n * m := Nat.lcm_dvd hcN (n.dvd_mul_right m)
  let η' : DirichletCharacter K (c.lcm n) := θ.primitiveCharacter.mul χ⁻¹
  have hη' : η'.changeLevel hL' = ψN := by
    dsimp [η']
    rw [DirichletCharacter.mul, MonoidHom.map_mul, ← DirichletCharacter.changeLevel_trans,
      ← DirichletCharacter.changeLevel_trans, DirichletCharacter.changeLevel_primitiveCharacter]
    simp [χN, ψN, θ, map_inv, mul_assoc]
  have hψNfac : ψN.FactorsThrough (c.lcm n) := ⟨hL', η', hη'.symm⟩
  have hmL : m ∣ c.lcm n := by
    rw [← hψ, ← DirichletCharacter.conductor_changeLevel ψ (m.dvd_mul_left n)]
    exact DirichletCharacter.conductor_dvd_of_mem_conductorSet ψN hψNfac
  have hmC : m ∣ c := hcop.symm.dvd_of_dvd_mul_right
    (dvd_trans hmL (Nat.lcm_dvd_mul c n))
  have hNC : n * m ∣ c := hcop.mul_dvd_of_dvd_of_dvd hnC hmC
  exact dvd_antisymm hcN hNC

end RHTower
