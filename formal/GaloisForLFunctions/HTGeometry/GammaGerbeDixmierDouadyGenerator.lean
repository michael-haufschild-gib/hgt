import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.FinCases

/-!
# The Dixmier–Douady class of the gamma gerbe is a generator

For a triptic curve `E = [ℂ/Λ]` with `Λ` of rank three the fibre is contractible, so the
equivariant cohomology reduces to the group cohomology of `ℤ³`, and the Dixmier–Douady class of the
gamma gerbe is represented by the explicit integral group `3`-cocycle

`ν(λ, μ, ν) = - n₁ m₂ ℓ₃`,   `λ = Σ ℓᵢ αᵢ`, `μ = Σ mᵢ αᵢ`, `ν = Σ nᵢ αᵢ`.

This file proves, with no analytic input, that `ν` is a `3`-cocycle and is not a coboundary: the
alternation on the standard basis kills every coboundary and sends `ν` to `1`.  Since that
alternation is an additive map to `ℤ`, the class of `ν` generates the image, so `ν` represents a
generator of `H³(ℤ³, ℤ) ≅ ℤ`.

The alternation is the concrete form of the Dixmier–Douady detector: a holomorphic nowhere-vanishing
trivialisation of a gerbe cocycle makes the associated integral class a coboundary, so a cocycle
with nonzero alternation admits none.
-/

noncomputable section

namespace GaloisForLFunctions

namespace GerbeCharacteristic

/-- The lattice of a triptic curve. -/
abbrev TripticLattice : Type := Fin 3 → ℤ

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The inhomogeneous group coboundary of a `1`-cochain, for a trivial action. -/
def coboundary₁ (h : TripticLattice → M) : TripticLattice → TripticLattice → M :=
  fun a b => h b - h (a + b) + h a

/-- The inhomogeneous group coboundary of a `2`-cochain, for a trivial action. -/
def coboundary₂ (g : TripticLattice → TripticLattice → M) :
    TripticLattice → TripticLattice → TripticLattice → M :=
  fun a b c => g b c - g (a + b) c + g a (b + c) - g a b

/-- The inhomogeneous group coboundary of a `3`-cochain, for a trivial action. -/
def coboundary₃ (f : TripticLattice → TripticLattice → TripticLattice → M) :
    TripticLattice → TripticLattice → TripticLattice → TripticLattice → M :=
  fun a b c d => f b c d - f (a + b) c d + f a (b + c) d - f a b (c + d) + f a b c

/-- The cochain groups form a complex in the first two available degrees. -/
theorem coboundary₂_coboundary₁ (h : TripticLattice → M) :
    coboundary₂ (coboundary₁ h) = 0 := by
  funext a b c
  simp only [coboundary₂, coboundary₁, Pi.zero_apply, add_assoc]
  abel

theorem coboundary₃_coboundary₂ (g : TripticLattice → TripticLattice → M) :
    coboundary₃ (coboundary₂ g) = 0 := by
  funext a b c d
  simp only [coboundary₃, coboundary₂, Pi.zero_apply, add_assoc]
  abel

theorem coboundary₂_add (g₁ g₂ : TripticLattice → TripticLattice → M) :
    coboundary₂ (fun a b => g₁ a b + g₂ a b) =
      fun a b c => coboundary₂ g₁ a b c + coboundary₂ g₂ a b c := by
  funext a b c
  simp only [coboundary₂]
  abel

/-- **The exponential detector.**  Let `E` be a surjective homomorphism of coefficient groups --- the
exponential `O -> O^×` on a cover with simply connected patches.  If a cocycle `φ` valued in the
target is a coboundary there, then the integral class obtained from any lift of `φ` is a coboundary
in the kernel-valued complex.  Hence a lift whose coboundary is not a coboundary certifies that `φ`
is not a coboundary. -/
theorem coboundary₂_lift_eq_coboundary₂_kernel (E : M →+ N) (hE : Function.Surjective E)
    {φ : TripticLattice → TripticLattice → N} {ψ : TripticLattice → N}
    (hφ : φ = coboundary₁ ψ)
    {Φ : TripticLattice → TripticLattice → M} (hΦ : ∀ a b, E (Φ a b) = φ a b) :
    ∃ k : TripticLattice → TripticLattice → M,
      (∀ a b, E (k a b) = 0) ∧ coboundary₂ Φ = coboundary₂ k := by
  classical
  choose Ψ hΨ using fun x => hE (ψ x)
  refine ⟨fun a b => Φ a b - coboundary₁ Ψ a b, ?_, ?_⟩
  · intro a b
    have hE1 : E (coboundary₁ Ψ a b) = coboundary₁ ψ a b := by
      simp only [coboundary₁, map_add, map_sub, hΨ]
    rw [map_sub, hΦ, hE1, hφ, sub_self]
  · funext a b c
    have hsplit : Φ = fun a b => (Φ a b - coboundary₁ Ψ a b) + coboundary₁ Ψ a b := by
      funext a b; abel
    rw [hsplit, coboundary₂_add, coboundary₂_coboundary₁]
    simp

/-- The standard basis of the triptic lattice. -/
def basisVec (i : Fin 3) : TripticLattice := Pi.single i 1

@[simp] theorem basisVec_apply (i j : Fin 3) : basisVec i j = if j = i then 1 else 0 := by
  simp [basisVec, Pi.single_apply, eq_comm]

/-- The alternation of a `3`-cochain over the standard basis: the pairing with the top exterior
power of the lattice. -/
def alternation (f : TripticLattice → TripticLattice → TripticLattice → ℤ) : ℤ :=
  f (basisVec 0) (basisVec 1) (basisVec 2) + f (basisVec 1) (basisVec 2) (basisVec 0) +
      f (basisVec 2) (basisVec 0) (basisVec 1) -
    f (basisVec 1) (basisVec 0) (basisVec 2) - f (basisVec 0) (basisVec 2) (basisVec 1) -
      f (basisVec 2) (basisVec 1) (basisVec 0)

/-- **The Dixmier–Douady cocycle of the gamma gerbe**, `ν(λ,μ,ν) = -n₁ m₂ ℓ₃` in the
Felder–Henriques–Rossi–Zhu framing. -/
def gammaGerbeDD : TripticLattice → TripticLattice → TripticLattice → ℤ :=
  fun a b c => -(c 0 * b 1 * a 2)

/-- The gamma-gerbe Dixmier–Douady cochain is a group `3`-cocycle. -/
theorem coboundary₃_gammaGerbeDD : coboundary₃ gammaGerbeDD = 0 := by
  funext a b c d
  simp only [coboundary₃, gammaGerbeDD, Pi.add_apply, Pi.zero_apply]
  ring

/-- **The alternation kills every coboundary.** -/
theorem alternation_coboundary₂ (g : TripticLattice → TripticLattice → ℤ) :
    alternation (coboundary₂ g) = 0 := by
  simp only [alternation, coboundary₂]
  rw [show basisVec 1 + basisVec 0 = basisVec 0 + basisVec 1 from add_comm _ _,
    show basisVec 2 + basisVec 1 = basisVec 1 + basisVec 2 from add_comm _ _,
    show basisVec 0 + basisVec 2 = basisVec 2 + basisVec 0 from add_comm _ _,
    show basisVec 2 + basisVec 0 = basisVec 0 + basisVec 2 from add_comm _ _,
    show basisVec 0 + basisVec 1 = basisVec 1 + basisVec 0 from add_comm _ _,
    show basisVec 1 + basisVec 2 = basisVec 2 + basisVec 1 from add_comm _ _]
  ring

/-- **The alternation of the gamma-gerbe cocycle is `1`.** -/
theorem alternation_gammaGerbeDD : alternation gammaGerbeDD = 1 := by
  simp [alternation, gammaGerbeDD]

/-- **The gamma-gerbe Dixmier–Douady cocycle is not a coboundary.** -/
theorem gammaGerbeDD_not_coboundary :
    ¬ ∃ g : TripticLattice → TripticLattice → ℤ, gammaGerbeDD = coboundary₂ g := by
  rintro ⟨g, hg⟩
  have h := alternation_gammaGerbeDD
  rw [hg, alternation_coboundary₂] at h
  exact absurd h (by decide)

/-- **Every integral multiple of the class is detected.**  The alternation is additive, so the class
of the gamma-gerbe cocycle generates the image of the alternation, which is all of `ℤ`. -/
theorem alternation_add (f₁ f₂ : TripticLattice → TripticLattice → TripticLattice → ℤ) :
    alternation (fun a b c => f₁ a b c + f₂ a b c) = alternation f₁ + alternation f₂ := by
  simp only [alternation]
  ring

theorem alternation_zsmul (n : ℤ) (f : TripticLattice → TripticLattice → TripticLattice → ℤ) :
    alternation (fun a b c => n * f a b c) = n * alternation f := by
  simp only [alternation]
  ring

/-- No nonzero multiple of the gamma-gerbe cocycle is a coboundary: the class has infinite order,
and its alternation `-1` generates `ℤ`. -/
theorem zsmul_gammaGerbeDD_not_coboundary {n : ℤ} (hn : n ≠ 0) :
    ¬ ∃ g : TripticLattice → TripticLattice → ℤ,
      (fun a b c => n * gammaGerbeDD a b c) = coboundary₂ g := by
  rintro ⟨g, hg⟩
  have h : alternation (fun a b c => n * gammaGerbeDD a b c) = 0 := by
    rw [hg, alternation_coboundary₂]
  rw [alternation_zsmul, alternation_gammaGerbeDD, mul_one] at h
  exact hn h

/-- **The detector in its robust form.**  A `3`-cochain with nonzero alternation is not a
coboundary. -/
theorem not_coboundary_of_alternation_ne_zero
    {f : TripticLattice → TripticLattice → TripticLattice → ℤ} (hf : alternation f ≠ 0) :
    ¬ ∃ g : TripticLattice → TripticLattice → ℤ, f = coboundary₂ g := by
  rintro ⟨g, rfl⟩
  exact hf (alternation_coboundary₂ g)

/-- The alternation only depends on the cohomology class. -/
theorem alternation_add_coboundary₂
    (f : TripticLattice → TripticLattice → TripticLattice → ℤ)
    (g : TripticLattice → TripticLattice → ℤ) :
    alternation (fun a b c => f a b c + coboundary₂ g a b c) = alternation f := by
  rw [alternation_add, alternation_coboundary₂, add_zero]

/-- **Everything cohomologous to the gamma-gerbe cocycle is a generator too.**  This is the form the
Felder--Henriques--Rossi--Zhu identification is consumed in: only the class of the integral cocycle
matters, not the particular polynomial representative. -/
theorem not_coboundary_of_cohomologous_gammaGerbeDD
    {f : TripticLattice → TripticLattice → TripticLattice → ℤ}
    {g : TripticLattice → TripticLattice → ℤ}
    (hf : f = fun a b c => gammaGerbeDD a b c + coboundary₂ g a b c) :
    ¬ ∃ h : TripticLattice → TripticLattice → ℤ, f = coboundary₂ h := by
  refine not_coboundary_of_alternation_ne_zero ?_
  rw [hf, alternation_add_coboundary₂, alternation_gammaGerbeDD]
  decide

/-! ## The gamma-gerbe exponent and its coboundary -/

/-- The exponent of the group-direction component of the gamma-gerbe cocycle, in the framing
`(α₁, α₂, α₃)` with `αᵢ(x)` recorded as `A i`.  For `μ = Σ mᵢ αᵢ` and `ν = Σ nᵢ αᵢ`,

`P(μ, ν; w) = (n₁ m₂ / α₃) [ w + ((2m₁ + n₁ - 1)/2) α₁ + ((m₂ - 1)/2) α₂ + (1/2) α₃ ]`. -/
def gammaGerbeExponent (A : Fin 3 → ℂ) (w : ℂ) (m n : TripticLattice) : ℂ :=
  ((n 0 : ℂ) * (m 1 : ℂ)) / A 2 *
    (w + ((2 * (m 0 : ℂ) + (n 0 : ℂ) - 1) / 2) * A 0 +
      (((m 1 : ℂ) - 1) / 2) * A 1 + (1 / 2) * A 2)

/-- The pairing `λ(x) = Σ ℓᵢ αᵢ(x)` of a lattice element with the frame. -/
def framePairing (A : Fin 3 → ℂ) (l : TripticLattice) : ℂ :=
  (l 0 : ℂ) * A 0 + (l 1 : ℂ) * A 1 + (l 2 : ℂ) * A 2

/-- The gerbe exponent with a general theta normalisation constant `κ`; `κ = -1/2` is the
Felder–Henriques–Rossi–Zhu normalisation. -/
def gammaGerbeExponentOf (A : Fin 3 → ℂ) (κ : ℂ) (w : ℂ) (m n : TripticLattice) : ℂ :=
  ((n 0 : ℂ) * (m 1 : ℂ)) / A 2 *
    (w + ((2 * (m 0 : ℂ) + (n 0 : ℂ) - 1) / 2) * A 0 +
      (((m 1 : ℂ) - 1) / 2) * A 1 - κ * A 2)

theorem gammaGerbeExponentOf_neg_half (A : Fin 3 → ℂ) (w : ℂ) (m n : TripticLattice) :
    gammaGerbeExponentOf A (-(1 / 2)) w m n = gammaGerbeExponent A w m n := by
  unfold gammaGerbeExponentOf gammaGerbeExponent
  ring

/-- **The Dixmier–Douady computation, for any theta normalisation.**  The normalisation constant
contributes a bilinear term whose coboundary vanishes, so the integral class does not depend on
it. -/
theorem coboundary_gammaGerbeExponentOf (A : Fin 3 → ℂ) (hA : A 2 ≠ 0) (κ w : ℂ)
    (l m n : TripticLattice) :
    -gammaGerbeExponentOf A κ (w + framePairing A l) m n +
        gammaGerbeExponentOf A κ w (l + m) n -
      gammaGerbeExponentOf A κ w l (m + n) + gammaGerbeExponentOf A κ w l m =
      ((gammaGerbeDD l m n : ℤ) : ℂ) := by
  simp only [gammaGerbeExponentOf, framePairing, gammaGerbeDD, Pi.add_apply]
  push_cast
  field_simp
  ring

/-- **The Dixmier–Douady computation.**  The group coboundary of the gamma-gerbe exponent, with the
translation acting on the fibre coordinate, is the integral cocycle `ν`.  This is the identity
behind Felder–Henriques–Rossi–Zhu's determination of the class. -/
theorem coboundary_gammaGerbeExponent (A : Fin 3 → ℂ) (hA : A 2 ≠ 0) (w : ℂ)
    (l m n : TripticLattice) :
    -gammaGerbeExponent A (w + framePairing A l) m n +
        gammaGerbeExponent A w (l + m) n -
      gammaGerbeExponent A w l (m + n) + gammaGerbeExponent A w l m =
      ((gammaGerbeDD l m n : ℤ) : ℂ) := by
  simp only [gammaGerbeExponent, framePairing, gammaGerbeDD, Pi.add_apply]
  push_cast
  field_simp
  ring

end GerbeCharacteristic

end GaloisForLFunctions
