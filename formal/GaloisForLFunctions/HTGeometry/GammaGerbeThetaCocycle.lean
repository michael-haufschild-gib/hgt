import GaloisForLFunctions.HTGeometry.GammaGerbeDixmierDouadyGenerator
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# The theta cocycle behind the gamma gerbe

Felder–Henriques–Rossi–Zhu's group-direction cochain is the finite theta product
`Δ(M, W) = ∏_{j < M} θ(W + j u)`, and its group-cocycle defect is the exponential of the explicit
polynomial whose coboundary is the Dixmier–Douady cocycle.  This file derives the defect from the
two quasi-periodicity laws of `θ` alone, written with the sign absorbed into the exponential:

`θ(z + 1) = θ(z)`,   `θ(z + τ) = exp(2πi(κ - z)) θ(z)`.

Iterating gives the shift by an arbitrary integral multiple of `τ`, and telescoping the product over
the shifted arguments produces exactly the Felder–Henriques–Rossi–Zhu exponent.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions

namespace GerbeCharacteristic

variable {θ : ℂ → ℂ} {τ κ : ℂ}

/-- The circle constant of the exponential normalisation. -/
local notation "Ⅱ" => (2 * (Real.pi : ℂ) * Complex.I)

/-- Periodicity under an integral shift. -/
theorem theta_add_intCast (hper : ∀ z, θ (z + 1) = θ z) (j : ℤ) (z : ℂ) :
    θ (z + (j : ℂ)) = θ z := by
  induction j using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have harg : z + (((n : ℤ) + 1 : ℤ) : ℂ) = (z + ((n : ℤ) : ℂ)) + 1 := by push_cast; ring
      rw [harg, hper, ih]
  | pred n ih =>
      have harg : (z + ((-(n : ℤ) - 1 : ℤ) : ℂ)) + 1 = z + ((-(n : ℤ) : ℤ) : ℂ) := by
        push_cast; ring
      have h := hper (z + ((-(n : ℤ) - 1 : ℤ) : ℂ))
      rw [harg] at h
      rw [← h, ih]

/-- The downward quasi-period law. -/
theorem theta_sub_tau (hq : ∀ z, θ (z + τ) = Complex.exp (Ⅱ * (κ - z)) * θ z) (z : ℂ) :
    θ (z - τ) = Complex.exp (-(Ⅱ * (κ - (z - τ)))) * θ z := by
  have h := hq (z - τ)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, ← Complex.exp_add]
  simp

/-- **The `τ`-shift law.**  Iterating the quasi-period law in both directions gives the shift by an
arbitrary integral multiple of `τ`. -/
theorem theta_add_zsmul_tau (hq : ∀ z, θ (z + τ) = Complex.exp (Ⅱ * (κ - z)) * θ z)
    (k : ℤ) (z : ℂ) :
    θ (z + (k : ℂ) * τ) =
      Complex.exp (Ⅱ * ((k : ℂ) * κ - (k : ℂ) * z - τ * ((k : ℂ) * ((k : ℂ) - 1) / 2))) * θ z := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have harg : z + (((n : ℤ) + 1 : ℤ) : ℂ) * τ = (z + ((n : ℤ) : ℂ) * τ) + τ := by
        push_cast; ring
      have hexp : Complex.exp (Ⅱ * (κ - (z + ((n : ℤ) : ℂ) * τ))) *
          Complex.exp (Ⅱ * (((n : ℤ) : ℂ) * κ - ((n : ℤ) : ℂ) * z -
            τ * (((n : ℤ) : ℂ) * (((n : ℤ) : ℂ) - 1) / 2))) =
          Complex.exp (Ⅱ * (((((n : ℤ) + 1 : ℤ) : ℂ) * κ) - (((n : ℤ) + 1 : ℤ) : ℂ) * z -
            τ * ((((n : ℤ) + 1 : ℤ) : ℂ) * ((((n : ℤ) + 1 : ℤ) : ℂ) - 1) / 2))) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [harg, hq, ih, ← mul_assoc, hexp]
  | pred n ih =>
      have harg : z + ((-(n : ℤ) - 1 : ℤ) : ℂ) * τ = (z + ((-(n : ℤ) : ℤ) : ℂ) * τ) - τ := by
        push_cast; ring
      have hexp : Complex.exp (-(Ⅱ * (κ - ((z + ((-(n : ℤ) : ℤ) : ℂ) * τ) - τ)))) *
          Complex.exp (Ⅱ * ((((-(n : ℤ) : ℤ) : ℂ) * κ) - ((-(n : ℤ) : ℤ) : ℂ) * z -
            τ * (((-(n : ℤ) : ℤ) : ℂ) * (((-(n : ℤ) : ℤ) : ℂ) - 1) / 2))) =
          Complex.exp (Ⅱ * ((((-(n : ℤ) - 1 : ℤ) : ℂ) * κ) - ((-(n : ℤ) - 1 : ℤ) : ℂ) * z -
            τ * (((-(n : ℤ) - 1 : ℤ) : ℂ) * ((((-(n : ℤ) - 1 : ℤ)) : ℂ) - 1) / 2))) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [harg, theta_sub_tau hq, ih, ← mul_assoc, hexp]

/-- The shift by an arbitrary lattice element of the fibre. -/
theorem theta_add_lattice (hper : ∀ z, θ (z + 1) = θ z)
    (hq : ∀ z, θ (z + τ) = Complex.exp (Ⅱ * (κ - z)) * θ z) (k j : ℤ) (z : ℂ) :
    θ (z + (k : ℂ) * τ + (j : ℂ)) =
      Complex.exp (Ⅱ * ((k : ℂ) * κ - (k : ℂ) * z - τ * ((k : ℂ) * ((k : ℂ) - 1) / 2))) * θ z := by
  rw [theta_add_intCast hper j, theta_add_zsmul_tau hq k z]

/-! ## The finite theta product and its group-cocycle defect -/

/-- The Felder–Henriques–Rossi–Zhu group-direction cochain: a finite theta product. -/
def thetaProd (θ : ℂ → ℂ) (u : ℂ) (M : ℕ) (W : ℂ) : ℂ :=
  ∏ i ∈ Finset.range M, θ (W + (i : ℂ) * u)

theorem sum_range_cast (N : ℕ) : (∑ i ∈ Finset.range N, (i : ℂ)) = (N : ℂ) * ((N : ℂ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Shifting the whole product by a lattice element multiplies it by the explicit exponential. -/
theorem thetaProd_shift (hper : ∀ z, θ (z + 1) = θ z)
    (hq : ∀ z, θ (z + τ) = Complex.exp (Ⅱ * (κ - z)) * θ z)
    (u : ℂ) (N : ℕ) (k j : ℤ) (Z : ℂ) :
    (∏ i ∈ Finset.range N, θ (Z + (i : ℂ) * u + (k : ℂ) * τ + (j : ℂ))) =
      Complex.exp (Ⅱ * ((N : ℂ) * (k : ℂ) * κ -
          (k : ℂ) * ((N : ℂ) * Z + u * ((N : ℂ) * ((N : ℂ) - 1) / 2)) -
          (N : ℂ) * τ * ((k : ℂ) * ((k : ℂ) - 1) / 2))) *
        ∏ i ∈ Finset.range N, θ (Z + (i : ℂ) * u) := by
  have hterm : ∀ i ∈ Finset.range N,
      θ (Z + (i : ℂ) * u + (k : ℂ) * τ + (j : ℂ)) =
        Complex.exp (Ⅱ * ((k : ℂ) * κ - (k : ℂ) * (Z + (i : ℂ) * u) -
          τ * ((k : ℂ) * ((k : ℂ) - 1) / 2))) * θ (Z + (i : ℂ) * u) := by
    intro i _
    exact theta_add_lattice hper hq k j (Z + (i : ℂ) * u)
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sum_range_cast]
  ring

/-- **The group-cocycle defect of the theta product.**  This is Felder–Henriques–Rossi–Zhu's
Proposition 3.15: the defect is the exponential of `-2πi` times the gerbe exponent. -/
theorem thetaProd_cocycle (hper : ∀ z, θ (z + 1) = θ z)
    (hq : ∀ z, θ (z + τ) = Complex.exp (Ⅱ * (κ - z)) * θ z)
    (u : ℂ) (M N : ℕ) (k j : ℤ) (W : ℂ) :
    thetaProd θ u M W * thetaProd θ u N (W + (M : ℂ) * u + (k : ℂ) * τ + (j : ℂ)) =
      Complex.exp (-(Ⅱ * ((N : ℂ) * (k : ℂ) *
          (W + (M : ℂ) * u + (((N : ℂ) - 1) / 2) * u + (((k : ℂ) - 1) / 2) * τ - κ)))) *
        thetaProd θ u (M + N) W := by
  have hsplit : thetaProd θ u (M + N) W =
      thetaProd θ u M W * ∏ i ∈ Finset.range N, θ (W + ((M : ℂ) + (i : ℂ)) * u) := by
    unfold thetaProd
    rw [Finset.prod_range_add]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast
    ring_nf
  have hshift : thetaProd θ u N (W + (M : ℂ) * u + (k : ℂ) * τ + (j : ℂ)) =
      Complex.exp (Ⅱ * ((N : ℂ) * (k : ℂ) * κ -
          (k : ℂ) * ((N : ℂ) * (W + (M : ℂ) * u) + u * ((N : ℂ) * ((N : ℂ) - 1) / 2)) -
          (N : ℂ) * τ * ((k : ℂ) * ((k : ℂ) - 1) / 2))) *
        ∏ i ∈ Finset.range N, θ (W + (M : ℂ) * u + (i : ℂ) * u) := by
    unfold thetaProd
    have := thetaProd_shift hper hq u N k j (W + (M : ℂ) * u)
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) this
    congr 1
    ring
  have hprod : (∏ i ∈ Finset.range N, θ (W + (M : ℂ) * u + (i : ℂ) * u)) =
      ∏ i ∈ Finset.range N, θ (W + ((M : ℂ) + (i : ℂ)) * u) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    ring
  have hexp : Complex.exp (Ⅱ * ((N : ℂ) * (k : ℂ) * κ -
        (k : ℂ) * ((N : ℂ) * (W + (M : ℂ) * u) + u * ((N : ℂ) * ((N : ℂ) - 1) / 2)) -
        (N : ℂ) * τ * ((k : ℂ) * ((k : ℂ) - 1) / 2))) =
      Complex.exp (-(Ⅱ * ((N : ℂ) * (k : ℂ) *
        (W + (M : ℂ) * u + (((N : ℂ) - 1) / 2) * u + (((k : ℂ) - 1) / 2) * τ - κ)))) := by
    congr 1
    ring
  rw [hsplit, hshift, hprod, hexp]
  ring

/-! ## Identification with the gerbe exponent, and the capstone -/

/-- The defect exponent of the theta product is the gamma-gerbe exponent, in the coordinates
`W = w/α₃`, `u = α₁/α₃`, `τ = α₂/α₃`, with `μ(a) = m₀`, the `α₂`-coefficient `m₁` and `ν(a) = n₀`. -/
theorem thetaProd_defect_eq_gammaGerbeExponent (A : Fin 3 → ℂ) (hA : A 2 ≠ 0) (κ w : ℂ)
    (m n : TripticLattice) :
    (n 0 : ℂ) * (m 1 : ℂ) *
        (w / A 2 + (m 0 : ℂ) * (A 0 / A 2) + (((n 0 : ℂ) - 1) / 2) * (A 0 / A 2) +
          (((m 1 : ℂ) - 1) / 2) * (A 1 / A 2) - κ) =
      gammaGerbeExponentOf A κ w m n := by
  unfold gammaGerbeExponentOf
  field_simp
  ring

/-- **The gamma gerbe admits no holomorphic trivialisation.**  The integral coboundary of the
gamma-gerbe exponent is the Dixmier–Douady cocycle `ν`, and `ν` is not a coboundary; a holomorphic
nowhere-vanishing trivialisation would make it one. -/
theorem coboundary_gammaGerbeExponent_not_coboundary (A : Fin 3 → ℂ) (hA : A 2 ≠ 0) (κ w : ℂ) :
    ¬ ∃ g : TripticLattice → TripticLattice → ℤ,
      ∀ l m n : TripticLattice,
        -gammaGerbeExponentOf A κ (w + framePairing A l) m n +
            gammaGerbeExponentOf A κ w (l + m) n -
            gammaGerbeExponentOf A κ w l (m + n) + gammaGerbeExponentOf A κ w l m =
          ((coboundary₂ g l m n : ℤ) : ℂ) := by
  rintro ⟨g, hg⟩
  refine gammaGerbeDD_not_coboundary ⟨g, ?_⟩
  funext l m n
  have h := hg l m n
  rw [coboundary_gammaGerbeExponentOf A hA κ w l m n] at h
  exact_mod_cast h

/-! ## The unconditional instance: mathlib's two-variable Jacobi theta -/

theorem jacobiTheta₂_add_one (τ z : ℂ) : jacobiTheta₂ (z + 1) τ = jacobiTheta₂ z τ :=
  jacobiTheta₂_add_left z τ

theorem jacobiTheta₂_add_tau (τ z : ℂ) :
    jacobiTheta₂ (z + τ) τ = Complex.exp (Ⅱ * (-(τ / 2) - z)) * jacobiTheta₂ z τ := by
  rw [jacobiTheta₂_add_left' z τ]
  congr 2
  ring

/-- **The group-cocycle defect of the genuine theta product, unconditionally.** -/
theorem jacobiThetaProd_cocycle (τ u : ℂ) (M N : ℕ) (k j : ℤ) (W : ℂ) :
    thetaProd (fun z => jacobiTheta₂ z τ) u M W *
        thetaProd (fun z => jacobiTheta₂ z τ) u N (W + (M : ℂ) * u + (k : ℂ) * τ + (j : ℂ)) =
      Complex.exp (-(Ⅱ * ((N : ℂ) * (k : ℂ) *
          (W + (M : ℂ) * u + (((N : ℂ) - 1) / 2) * u + (((k : ℂ) - 1) / 2) * τ - -(τ / 2))))) *
        thetaProd (fun z => jacobiTheta₂ z τ) u (M + N) W :=
  thetaProd_cocycle (jacobiTheta₂_add_one τ) (jacobiTheta₂_add_tau τ) u M N k j W

/-- **The gamma gerbe is unconditionally non-trivialisable.**  The group-direction cocycle of the
genuine theta-product cochain is the exponential of `-2πi` times the gerbe exponent, whose integral
coboundary is the Dixmier–Douady generator; no holomorphic nowhere-vanishing cochain trivialises
it. -/
theorem jacobiThetaProd_gerbe_not_trivialisable (A : Fin 3 → ℂ) (hA : A 2 ≠ 0) (τ w : ℂ) :
    ¬ ∃ g : TripticLattice → TripticLattice → ℤ,
      ∀ l m n : TripticLattice,
        -gammaGerbeExponentOf A (-(τ / 2)) (w + framePairing A l) m n +
            gammaGerbeExponentOf A (-(τ / 2)) w (l + m) n -
            gammaGerbeExponentOf A (-(τ / 2)) w l (m + n) +
            gammaGerbeExponentOf A (-(τ / 2)) w l m =
          ((coboundary₂ g l m n : ℤ) : ℂ) :=
  coboundary_gammaGerbeExponent_not_coboundary A hA (-(τ / 2)) w

end GerbeCharacteristic

end GaloisForLFunctions
