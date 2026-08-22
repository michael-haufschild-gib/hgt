import GaloisForLFunctions.HTGeometry.MultivariateEntireCauchyEstimate
import GaloisForLFunctions.HTGeometry.MultivariateEntireCommMonoid
import GaloisForLFunctions.HTGeometry.MultivariateEntireJetVanishingProduct

/-!
# Abe's exponential damping multiplier

The analytic multiplier used in Abe's Poincare construction is the entire function
`exp (t * (Θ - 1))`.  This file constructs it inside `MultivariateEntire` and records its
two exact algebraic properties: lattice invariance is inherited from `Θ`, and its value at a
normalization point of `Θ` is one.  No estimate or asymptotic assertion is packaged here.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Composition of a multivariate entire function with the complex exponential. -/
def multivariateEntireCexp {d : ℕ} (f : MultivariateEntire d) : MultivariateEntire d :=
  ⟨⟨fun x => Complex.exp (f.1 x), Complex.continuous_exp.comp f.1.continuous⟩,
    fun x v => (f.property x v).cexp⟩

/-- Abe's exponential damping multiplier, parametrized by its complex damping time. -/
def abeExponentialDampingMultiplier {d : ℕ} (t : ℂ) (Θ : MultivariateEntire d) :
    MultivariateEntire d :=
  multivariateEntireCexp (t • (Θ - 1))

theorem multivariateEntireCexp_apply {d : ℕ} (f : MultivariateEntire d) (x : Fin d → ℂ) :
    (multivariateEntireCexp f).1 x = Complex.exp (f.1 x) := rfl

theorem abeExponentialDampingMultiplier_apply {d : ℕ} (t : ℂ) (Θ : MultivariateEntire d)
    (x : Fin d → ℂ) :
    (abeExponentialDampingMultiplier t Θ).1 x = Complex.exp (t * (Θ.1 x - 1)) := by
  rw [abeExponentialDampingMultiplier, multivariateEntireCexp_apply]
  change Complex.exp (t * ((Θ - 1).1 x)) = Complex.exp (t * (Θ.1 x - 1))
  congr 2
  change Θ.1 x - (1 : MultivariateEntire d).1 x = Θ.1 x - 1
  rw [multivariateEntire_one_apply]

/-- The exponential multiplier inherits the period group of its profile. -/
theorem abeExponentialDampingMultiplier_invariant {d : ℕ} (t : ℂ)
    (Θ : MultivariateEntire d) {ΓH : AddSubgroup (Fin d → ℂ)}
    (hΘ : ∀ η ∈ ΓH, ∀ x, Θ.1 (x + η) = Θ.1 x) :
    ∀ η ∈ ΓH, ∀ x, (abeExponentialDampingMultiplier t Θ).1 (x + η)
      = (abeExponentialDampingMultiplier t Θ).1 x := by
  intro η hη x
  rw [abeExponentialDampingMultiplier_apply, abeExponentialDampingMultiplier_apply, hΘ η hη x]

/-- At a point where the profile equals one, the multiplier equals one exactly. -/
theorem abeExponentialDampingMultiplier_at_center {d : ℕ} (t : ℂ)
    (Θ : MultivariateEntire d) (p : Fin d → ℂ) (hΘ : Θ.1 p = 1) :
    (abeExponentialDampingMultiplier t Θ).1 p = 1 := by
  rw [abeExponentialDampingMultiplier_apply, hΘ]
  norm_num

/-- The exponential multiplier has no zeros. -/
theorem abeExponentialDampingMultiplier_apply_ne_zero {d : ℕ} (t : ℂ)
    (Θ : MultivariateEntire d) (x : Fin d → ℂ) :
    (abeExponentialDampingMultiplier t Θ).1 x ≠ 0 := by
  rw [abeExponentialDampingMultiplier_apply]
  exact Complex.exp_ne_zero _

/-- Reversing the damping time gives the multiplicative inverse multiplier. -/
theorem abeExponentialDampingMultiplier_mul_neg {d : ℕ} (t : ℂ) (Θ : MultivariateEntire d) :
    abeExponentialDampingMultiplier t Θ * abeExponentialDampingMultiplier (-t) Θ = 1 := by
  ext x
  rw [multivariateEntire_mul_apply, abeExponentialDampingMultiplier_apply,
    abeExponentialDampingMultiplier_apply, multivariateEntire_one_apply, ← Complex.exp_add]
  convert Complex.exp_zero using 1
  ring_nf

/-- Multiplication by the exponential multiplier is injective. -/
theorem abeExponentialDampingMultiplier_mul_injective {d : ℕ} (t : ℂ)
    (Θ : MultivariateEntire d) :
    Function.Injective (fun f : MultivariateEntire d => abeExponentialDampingMultiplier t Θ * f) := by
  intro f g hfg
  have hleft := congrArg (fun q : MultivariateEntire d => abeExponentialDampingMultiplier (-t) Θ * q) hfg
  have hinv : abeExponentialDampingMultiplier (-t) Θ * abeExponentialDampingMultiplier t Θ = 1 := by
    rw [mul_comm, abeExponentialDampingMultiplier_mul_neg]
  calc
    f = 1 * f := (one_mul f).symm
    _ = (abeExponentialDampingMultiplier (-t) Θ * abeExponentialDampingMultiplier t Θ) * f := by
      rw [hinv]
    _ = abeExponentialDampingMultiplier (-t) Θ * (abeExponentialDampingMultiplier t Θ * f) := by
      rw [mul_assoc]
    _ = abeExponentialDampingMultiplier (-t) Θ * (abeExponentialDampingMultiplier t Θ * g) := hleft
    _ = (abeExponentialDampingMultiplier (-t) Θ * abeExponentialDampingMultiplier t Θ) * g := by
      rw [mul_assoc]
    _ = 1 * g := by rw [hinv]
    _ = g := one_mul g

/-- A directional derivative of Abe's multiplier is its value times the scaled directional
derivative of the profile. -/
theorem partialDerivEntire_abeExponentialDampingMultiplier {d : ℕ} (v : Fin d → ℂ) (t : ℂ)
    (Θ : MultivariateEntire d) (x : Fin d → ℂ) :
    (partialDerivEntire v (abeExponentialDampingMultiplier t Θ)).1 x =
      (abeExponentialDampingMultiplier t Θ).1 x * (t * (partialDerivEntire v Θ).1 x) := by
  have hderivM :=
    (hasDerivAt_multivariateEntire_line v (abeExponentialDampingMultiplier t Θ) x 0).deriv
  simp only [zero_smul, add_zero] at hderivM
  have hderivΘ := (hasDerivAt_multivariateEntire_line v Θ x 0).deriv
  simp only [zero_smul, add_zero] at hderivΘ
  have hinner : HasDerivAt (fun s : ℂ => t * (Θ.1 (x + s • v) - 1))
      (t * fderiv ℂ (Θ.1 : (Fin d → ℂ) → ℂ) x v) 0 := by
    simpa only [zero_smul, add_zero] using
      ((hasDerivAt_multivariateEntire_line v Θ x 0).sub_const 1).const_mul t
  have hexp := hinner.cexp
  rw [partialDerivEntire_apply, partialDerivEntire_apply, ← hderivM, ← hderivΘ,
    abeExponentialDampingMultiplier_apply]
  have hline : (fun s : ℂ => (abeExponentialDampingMultiplier t Θ).1 (x + s • v)) =
      (fun s : ℂ => Complex.exp (t * (Θ.1 (x + s • v) - 1))) := by
    funext s
    rw [abeExponentialDampingMultiplier_apply]
  rw [hline]
  simpa only [zero_smul, add_zero, ← hderivΘ] using hexp.deriv

/-- Multiplication by Abe's multiplier preserves and reflects every finite order of jet
vanishing. -/
theorem allJetsVanish_abeExponentialDampingMultiplier_iff {d n : ℕ} (p : Fin d → ℂ) (t : ℂ)
    (Θ f : MultivariateEntire d) :
    AllJetsVanish n p (abeExponentialDampingMultiplier t Θ * f) ↔ AllJetsVanish n p f := by
  constructor
  · intro h
    have hprod := AllJetsVanish.mul_left n (abeExponentialDampingMultiplier (-t) Θ) h
    have hinv : abeExponentialDampingMultiplier (-t) Θ * abeExponentialDampingMultiplier t Θ = 1 := by
      rw [mul_comm, abeExponentialDampingMultiplier_mul_neg]
    have hident : abeExponentialDampingMultiplier (-t) Θ *
        (abeExponentialDampingMultiplier t Θ * f) = f := by
      calc
        abeExponentialDampingMultiplier (-t) Θ * (abeExponentialDampingMultiplier t Θ * f) =
            (abeExponentialDampingMultiplier (-t) Θ * abeExponentialDampingMultiplier t Θ) * f :=
          (mul_assoc _ _ _).symm
        _ = 1 * f := by rw [hinv]
        _ = f := one_mul f
    rw [hident] at hprod
    exact hprod
  · exact AllJetsVanish.mul_left n _

end

end GaloisForLFunctions.HTGeometry
