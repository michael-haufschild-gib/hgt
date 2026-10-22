import GaloisForLFunctions.RHTower.Suzuki.SuzukiOrbitCarrier

/-!
# Finite recurrence type admits every physical Gamma weight

Near an opposite-end collision the valuation `ν` sits at physical distance `δ_ν = |2a - ℓ(ν)|`,
i.e. at boundary depth `L_ν = -log δ_ν`.  Finite recurrence type is the statement that the depth
grows at most linearly in the `ℓ¹` length.  Then the exponential orbit weight `ρ = e^{-κ}` beats
the physical Gamma weight `e^{σL}` as soon as `σ R < κ`: the weighted activations are square
summable, because each is dominated by the orbit weight of the smaller ratio `e^{-(κ - σR)}`.
-/

open Finset

namespace RHTower

noncomputable section

/-- The physical distance of a valuation to the opposite end of the aperture. -/
def apertureDefect (a : ℝ) {P : Type*} [Fintype P] (ℓ : (P → ℤ) → ℝ) (ν : P → ℤ) : ℝ :=
  |2 * a - ℓ ν|

/-- The boundary depth `L_ν = -log δ_ν` of a valuation. -/
def apertureDepth (a : ℝ) {P : Type*} [Fintype P] (ℓ : (P → ℤ) → ℝ) (ν : P → ℤ) : ℝ :=
  -Real.log (apertureDefect a ℓ ν)

theorem orbitWeight_exp {P : Type*} [Fintype P] (κ : ℝ) (ν : P → ℤ) :
    orbitWeight (Real.exp (-κ)) ν = Real.exp (-κ * orbitLength ν) := by
  rw [orbitWeight, ← Real.exp_nat_mul]
  congr 1
  ring

/-- **`(25)`: at finite recurrence type the physical Gamma weight is beaten by the orbit weight.** -/
theorem weighted_activation_le {P : Type*} [Fintype P] {a κ σ R : ℝ} (hσ : 0 ≤ σ)
    (ℓ : (P → ℤ) → ℝ) (ν : P → ℤ)
    (hdepth : apertureDepth a ℓ ν ≤ R * orbitLength ν) :
    Real.exp (σ * apertureDepth a ℓ ν) * orbitWeight (Real.exp (-κ)) ν
      ≤ orbitWeight (Real.exp (-(κ - σ * R))) ν := by
  rw [orbitWeight_exp, orbitWeight_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul : σ * apertureDepth a ℓ ν ≤ σ * (R * orbitLength ν) :=
    mul_le_mul_of_nonneg_left hdepth hσ
  nlinarith [hmul]

/-- **`(26)`: finite recurrence type gives weighted endpoint summability.** -/
theorem summable_weighted_apertureActivation {P : Type*} [Fintype P] {a κ σ R : ℝ}
    (hσ : 0 ≤ σ) (hgap : σ * R < κ) (ℓ : (P → ℤ) → ℝ)
    (hdepth : ∀ ν : P → ℤ, apertureDepth a ℓ ν ≤ R * orbitLength ν) :
    Summable fun ν : P → ℤ =>
      (Real.exp (σ * apertureDepth a ℓ ν) * orbitWeight (Real.exp (-κ)) ν) ^ (2 : ℕ) := by
  have hρ0 : (0:ℝ) ≤ Real.exp (-(κ - σ * R)) := (Real.exp_pos _).le
  have hρ1 : Real.exp (-(κ - σ * R)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    linarith
  have hdom : Summable fun ν : P → ℤ => orbitWeight (Real.exp (-(κ - σ * R))) ν ^ (2 : ℕ) :=
    summable_orbitWeight_sq hρ0 hρ1
  refine hdom.of_nonneg_of_le (fun ν => sq_nonneg _) ?_
  intro ν
  have hpos : 0 ≤ Real.exp (σ * apertureDepth a ℓ ν) * orbitWeight (Real.exp (-κ)) ν := by
    have := (Real.exp_pos (σ * apertureDepth a ℓ ν)).le
    have h2 := (orbitWeight_pos (Real.exp_pos (-κ)) ν).le
    positivity
  exact pow_le_pow_left₀ hpos (weighted_activation_le hσ ℓ ν (hdepth ν)) 2

/-- The same bound survives multiplication by any fixed grade weight bounded on the lattice. -/
theorem summable_weighted_apertureActivation_grade {P : Type*} [Fintype P] {a κ σ R C : ℝ}
    (hσ : 0 ≤ σ) (hgap : σ * R < κ) (ℓ : (P → ℤ) → ℝ)
    (hdepth : ∀ ν : P → ℤ, apertureDepth a ℓ ν ≤ R * orbitLength ν)
    (g : (P → ℤ) → ℝ) (hg : ∀ ν, |g ν| ≤ C) :
    Summable fun ν : P → ℤ =>
      (g ν * (Real.exp (σ * apertureDepth a ℓ ν) * orbitWeight (Real.exp (-κ)) ν)) ^ (2 : ℕ) := by
  have hbase := summable_weighted_apertureActivation hσ hgap ℓ hdepth
  have hdom : Summable fun ν : P → ℤ =>
      C ^ (2 : ℕ) * (Real.exp (σ * apertureDepth a ℓ ν) * orbitWeight (Real.exp (-κ)) ν) ^ (2 : ℕ) :=
    hbase.mul_left _
  refine hdom.of_nonneg_of_le (fun ν => sq_nonneg _) ?_
  intro ν
  have habs : |g ν| ^ (2 : ℕ) ≤ C ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) (hg ν) 2
  calc (g ν * (Real.exp (σ * apertureDepth a ℓ ν) * orbitWeight (Real.exp (-κ)) ν)) ^ (2 : ℕ)
      = |g ν| ^ (2 : ℕ) * (Real.exp (σ * apertureDepth a ℓ ν) * orbitWeight (Real.exp (-κ)) ν) ^ (2 : ℕ) := by
        rw [sq_abs]
        ring
    _ ≤ C ^ (2 : ℕ) * (Real.exp (σ * apertureDepth a ℓ ν) * orbitWeight (Real.exp (-κ)) ν) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right habs (sq_nonneg _)

end

end RHTower
