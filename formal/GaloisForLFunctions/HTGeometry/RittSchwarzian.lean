import GaloisForLFunctions.HTGeometry.RittJetDefect

/-!
# The Schwarzian of a linearizer

The first three jets of a linearizer shift by

`σ(dτ) = (q/ρ)·dτ`,  `σ(d²τ) = (q/ρ²)·d²τ + λ₂·dτ`,
`σ(d³τ) = (q/ρ³)·d³τ + λ₃·d²τ + μ·dτ`,

with `λ₂ = −q(dρ)/ρ³`, `λ₃ = −3q(dρ)/ρ⁴` and `μ = −q(d²ρ)/ρ⁴ + 3q(dρ)²/ρ⁵`, all read off the defect
recursion.  Substituting into

`S = d³τ/dτ − (3/2)·(d²τ/dτ)²`

the coefficient of `d²τ/dτ` cancels exactly — `λ₃/(q/ρ) = 3·(q/ρ²)·λ₂/(q/ρ)²` — which is the whole
point of the constant `3/2`, and what is left is

`σ S = ρ^{−2}·S − (d²ρ)/ρ³ + (3/2)·(dρ)²/ρ⁴`.

The inhomogeneity is `−(1/ρ²)` times the Schwarzian derivative of the map, `d²ρ/ρ − (3/2)(dρ/ρ)²`,
which vanishes exactly for a Möbius transformation.  So for a map of degree at least two the
Schwarzian of the linearizer solves an affine transport equation with multiplier `ρ^{−2}` and a
nonzero constant inhomogeneity.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

/-- The base derivation is odd. -/
theorem dK_neg (Fr : RittFrame K L) (x : K) : Fr.dK (-x) = -Fr.dK x := by
  have hm1 : Fr.dK (-1 : K) = 0 := by
    have h := Fr.dK_mul (-1 : K) (-1 : K)
    rw [neg_mul_neg, one_mul, Fr.dK_one] at h
    linear_combination h / 2
  have h1 : Fr.dK ((-1 : K) * x) = Fr.dK (-1 : K) * x + (-1 : K) * Fr.dK x := Fr.dK_mul _ _
  rw [hm1, zero_mul, zero_add, neg_one_mul, neg_one_mul] at h1
  exact h1

/-- The Schwarzian combination of the first three jets. -/
noncomputable def schwarzianJet (Fr : RittFrame K L) (τ : L) : L :=
  Fr.d^[3] τ / Fr.d τ - (3 / 2 : L) * (Fr.d^[2] τ / Fr.d τ) ^ 2

/-- The second jet shifts with defect `λ₂·dτ`. -/
theorem sigma_jet_two (Fr : RittFrame K L) {τ : L} {q : K} (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) :
    Fr.σ (Fr.d^[2] τ) = algebraMap K L (q / Fr.ρ ^ 2) * Fr.d^[2] τ
      + algebraMap K L (-(q * Fr.dK Fr.ρ / Fr.ρ ^ 3)) * Fr.d τ := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have h := RittFrame.jetDefect_succ (Fr := Fr) (τ := τ) (q := q) 1
  rw [RittFrame.jetDefect_one hqconst hshift, Fr.d_zero, mul_zero, add_zero,
    RittFrame.dK_level_multiplier hqconst 1] at h
  have hcoef : -(((1 : ℕ) : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (1 + 1)) / Fr.ρ
      = -(q * Fr.dK Fr.ρ / Fr.ρ ^ 3) := by
    push_cast
    field_simp
  have h2 : Fr.jetDefect τ q 2
      = algebraMap K L (-(q * Fr.dK Fr.ρ / Fr.ρ ^ 3)) * Fr.d^[1] τ := by
    rw [← hcoef]
    exact h
  rw [RittFrame.jetDefect, sub_eq_iff_eq_add'] at h2
  exact h2

/-- The third jet shifts with defect `λ₃·d²τ + μ·dτ`. -/
theorem sigma_jet_three (Fr : RittFrame K L) {τ : L} {q : K} (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) :
    Fr.σ (Fr.d^[3] τ) = algebraMap K L (q / Fr.ρ ^ 3) * Fr.d^[3] τ
      + algebraMap K L (-(3 * q * Fr.dK Fr.ρ / Fr.ρ ^ 4)) * Fr.d^[2] τ
      + algebraMap K L (-(q * Fr.dK (Fr.dK Fr.ρ) / Fr.ρ ^ 4)
          + 3 * q * (Fr.dK Fr.ρ) ^ 2 / Fr.ρ ^ 5) * Fr.d τ := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  set lam2 : K := -(q * Fr.dK Fr.ρ / Fr.ρ ^ 3) with hlam2
  have hdef2 : Fr.jetDefect τ q 2 = algebraMap K L lam2 * Fr.d τ := by
    have h := sigma_jet_two Fr hqconst hshift
    rw [RittFrame.jetDefect]
    rw [h]
    ring
  have h := RittFrame.jetDefect_succ (Fr := Fr) (τ := τ) (q := q) 2
  rw [hdef2, RittFrame.d_algebraMap_mul, RittFrame.dK_level_multiplier hqconst 2] at h
  have hd1 : Fr.d (Fr.d τ) = Fr.d^[2] τ := rfl
  rw [hd1] at h
  -- collect the two coefficients
  have hdlam2 : Fr.dK lam2
      = -(q * Fr.dK (Fr.dK Fr.ρ) / Fr.ρ ^ 3) + 3 * q * (Fr.dK Fr.ρ) ^ 2 / Fr.ρ ^ 4 := by
    rw [hlam2, dK_neg]
    have hnum : Fr.dK (q * Fr.dK Fr.ρ) = q * Fr.dK (Fr.dK Fr.ρ) := by
      rw [Fr.dK_mul, hqconst, zero_mul, zero_add]
    rw [Fr.dK_div (pow_ne_zero 3 hρ0), hnum]
    have hpow : Fr.dK (Fr.ρ ^ 3) = 3 * Fr.ρ ^ 2 * Fr.dK Fr.ρ := by
      have := Fr.dK_pow_succ Fr.ρ 2
      push_cast at this
      rw [this]
      ring
    rw [hpow]
    field_simp
    ring
  have hc2 : -(((2 : ℕ) : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (2 + 1)) / Fr.ρ + lam2 * (Fr.ρ)⁻¹
      = -(3 * q * Fr.dK Fr.ρ / Fr.ρ ^ 4) := by
    rw [hlam2]
    push_cast
    field_simp
    ring
  have hc1 : (Fr.ρ)⁻¹ * Fr.dK lam2
      = -(q * Fr.dK (Fr.dK Fr.ρ) / Fr.ρ ^ 4) + 3 * q * (Fr.dK Fr.ρ) ^ 2 / Fr.ρ ^ 5 := by
    rw [hdlam2]
    field_simp
  rw [RittFrame.jetDefect, sub_eq_iff_eq_add'] at h
  rw [h]
  rw [← hc2, ← hc1]
  simp only [map_add, map_mul]
  ring

/-- **The Schwarzian of a linearizer solves an affine transport equation.**  Its multiplier is
`ρ^{−2}` and its inhomogeneity is minus the Schwarzian derivative of the map divided by `ρ²`. -/
theorem sigma_schwarzianJet (Fr : RittFrame K L) {τ : L} {q : K} (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0) (hdτ : Fr.d τ ≠ 0) :
    Fr.σ (schwarzianJet Fr τ)
      = algebraMap K L ((Fr.ρ ^ 2)⁻¹) * schwarzianJet Fr τ
        + algebraMap K L (-(Fr.dK (Fr.dK Fr.ρ) / Fr.ρ ^ 3)
            + (3 / 2) * (Fr.dK Fr.ρ) ^ 2 / Fr.ρ ^ 4) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hQ : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq
  have hR : algebraMap K L Fr.ρ ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hρ0
  have h1 : Fr.σ (Fr.d τ) = algebraMap K L (q / Fr.ρ) * Fr.d τ :=
    Fr.sigma_d_eq_of_shift hqconst hshift
  have h2 := sigma_jet_two Fr hqconst hshift
  have h3 := sigma_jet_three Fr hqconst hshift
  have h32 : Fr.σ ((3 : L) / 2) = (3 : L) / 2 := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have hσd : Fr.σ (Fr.d τ) ≠ 0 := by
    rw [h1]
    exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K L).injective).mpr
      (div_ne_zero hq hρ0)) hdτ
  rw [schwarzianJet]
  simp only [map_sub, map_div₀, map_mul, map_pow, map_ofNat]
  rw [h1, h2, h3]
  simp only [map_add, map_neg, map_mul, map_div₀, map_pow, map_ofNat, map_inv₀]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
