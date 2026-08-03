import Mathlib.Analysis.SpecialFunctions.Exponential
import GaloisForLFunctions.HTGeometry.ContinuumChronometricGravity

/-!
# Ordered clock tomography from a controlled pulse family

A controlled clock pulse family is `U_j(λ_j) = exp(λ_j a_j)`, applied in a fixed causal order. Its
characteristic functional in a state `ω` is `λ ↦ ω(U_0(λ_0) ⋯ U_{n-1}(λ_{n-1}))`. Differentiating
once in each coupling at zero recovers the complete ordered correlation `ω(a_0 ⋯ a_{n-1})`.

Together with the two-quadrature Ramsey recovery of the complex expectation, this closes the
tomography step: two readout bases plus one derivative in each control parameter reconstruct every
ordered correlation of the generators, not merely moduli or symmetrized parts.

Everything here is stated in a unital Banach algebra, where `exp` is entire and the pulse family is
literally the exponential of the generator.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- Iterated mixed derivative at zero, differentiating one coupling at a time in causal order. -/
noncomputable def nestedDerivAtZero : (n : ℕ) → ((Fin n → ℂ) → ℂ) → ℂ
  | 0, F => F (Fin.elim0)
  | (n + 1), F => deriv (fun t : ℂ => nestedDerivAtZero n fun v => F (Fin.cons t v)) 0

@[simp] theorem nestedDerivAtZero_zero (F : (Fin 0 → ℂ) → ℂ) :
    nestedDerivAtZero 0 F = F Fin.elim0 := rfl

theorem nestedDerivAtZero_succ (n : ℕ) (F : (Fin (n + 1) → ℂ) → ℂ) :
    nestedDerivAtZero (n + 1) F =
      deriv (fun t : ℂ => nestedDerivAtZero n fun v => F (Fin.cons t v)) 0 := rfl

section BanachAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- Ordered product `a 0 * a 1 * ⋯ * a (n-1)` of generators. -/
def orderedProduct : (n : ℕ) → (Fin n → 𝔸) → 𝔸
  | 0, _ => 1
  | (n + 1), a => a 0 * orderedProduct n fun i => a i.succ

omit [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] in
@[simp] theorem orderedProduct_zero (a : Fin 0 → 𝔸) : orderedProduct 0 a = 1 := rfl

omit [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] in
@[simp] theorem orderedProduct_succ (n : ℕ) (a : Fin (n + 1) → 𝔸) :
    orderedProduct (n + 1) a = a 0 * orderedProduct n fun i => a i.succ := rfl

/-- Causally ordered family of controlled clock pulses `exp(λ_0 a_0) ⋯ exp(λ_{n-1} a_{n-1})`. -/
noncomputable def pulseProduct : (n : ℕ) → (Fin n → 𝔸) → (Fin n → ℂ) → 𝔸
  | 0, _, _ => 1
  | (n + 1), a, l =>
      NormedSpace.exp (l 0 • a 0) * pulseProduct n (fun i => a i.succ) fun i => l i.succ

omit [CompleteSpace 𝔸] in
@[simp] theorem pulseProduct_zero (a : Fin 0 → 𝔸) (l : Fin 0 → ℂ) :
    pulseProduct 0 a l = 1 := rfl

omit [CompleteSpace 𝔸] in
@[simp] theorem pulseProduct_succ (n : ℕ) (a : Fin (n + 1) → 𝔸) (l : Fin (n + 1) → ℂ) :
    pulseProduct (n + 1) a l =
      NormedSpace.exp (l 0 • a 0) * pulseProduct n (fun i => a i.succ) fun i => l i.succ := rfl

omit [CompleteSpace 𝔸] in
/-- Scaling every generator scales the ordered product by the corresponding power. -/
theorem orderedProduct_smul (c : ℂ) :
    ∀ (n : ℕ) (a : Fin n → 𝔸),
      orderedProduct n (fun i => c • a i) = c ^ n • orderedProduct n a
  | 0, _ => by simp
  | (n + 1), a => by
    rw [orderedProduct_succ, orderedProduct_succ, orderedProduct_smul c n fun i => a i.succ]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
    congr 1
    ring

/-- **Ordered-product recovery from the controlled characteristic functional.**

One derivative in each coupling, taken at zero in causal order, turns the state value of the
ordered pulse family into the state value of the ordered product of its generators. -/
theorem nestedDerivAtZero_pulseProduct :
    ∀ (n : ℕ) (a : Fin n → 𝔸) (omega : 𝔸 →L[ℂ] ℂ),
      nestedDerivAtZero n (fun l => omega (pulseProduct n a l)) =
        omega (orderedProduct n a)
  | 0, _, _ => rfl
  | (n + 1), a, omega => by
    rw [nestedDerivAtZero_succ]
    set P : 𝔸 := orderedProduct n fun i => a i.succ with hP
    have hinner : ∀ t : ℂ,
        nestedDerivAtZero n (fun v => omega (pulseProduct (n + 1) a (Fin.cons t v))) =
          omega (NormedSpace.exp (t • a 0) * P) := by
      intro t
      have hrw :
          (fun v : Fin n → ℂ => omega (pulseProduct (n + 1) a (Fin.cons t v))) =
            fun v : Fin n → ℂ =>
              (omega.comp ((ContinuousLinearMap.mul ℂ 𝔸) (NormedSpace.exp (t • a 0))))
                (pulseProduct n (fun i => a i.succ) v) := by
        funext v
        simp [pulseProduct_succ]
      rw [hrw, nestedDerivAtZero_pulseProduct n (fun i => a i.succ)]
      rfl
    simp only [hinner]
    have hexp : HasDerivAt (fun t : ℂ => NormedSpace.exp (t • a 0)) (a 0) 0 := by
      have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) (a 0) 0
      simpa using h
    have hmul : HasDerivAt (fun t : ℂ => NormedSpace.exp (t • a 0) * P) (a 0 * P) 0 :=
      hexp.mul_const P
    have hcomp : HasDerivAt (fun t : ℂ => omega (NormedSpace.exp (t • a 0) * P))
        (omega (a 0 * P)) 0 :=
      omega.hasFDerivAt.comp_hasDerivAt 0 hmul
    rw [hcomp.deriv, orderedProduct_succ]

/-- **Weyl-normalized form.** With `U_j(λ) = exp(iλΦ_j)` the mixed derivative carries the factor
`i^n`, so `i^{-n}` times the derivative is the ordered correlation. -/
theorem nestedDerivAtZero_pulseProduct_imaginary
    (n : ℕ) (phi : Fin n → 𝔸) (omega : 𝔸 →L[ℂ] ℂ) :
    nestedDerivAtZero n
        (fun l => omega (pulseProduct n (fun i => Complex.I • phi i) l)) =
      Complex.I ^ n * omega (orderedProduct n phi) := by
  rw [nestedDerivAtZero_pulseProduct n (fun i => Complex.I • phi i) omega,
    orderedProduct_smul Complex.I n phi]
  simp [smul_eq_mul]

/-- **Phase-complete ordered clock tomography.**

Any reported characteristic functional whose two Ramsey quadratures agree with those of the
controlled pulse family is the pulse family's own characteristic functional, so differentiating the
reported data in each coupling recovers the complete ordered correlation. -/
theorem ordered_correlation_of_ramsey_quadratures
    (n : ℕ) (phi : Fin n → 𝔸) (omega : 𝔸 →L[ℂ] ℂ)
    (report : (Fin n → ℂ) → ℂ)
    (hreport : ∀ l : Fin n → ℂ,
      chronometricRamseyQuadratures (report l) =
        chronometricRamseyQuadratures
          (omega (pulseProduct n (fun i => Complex.I • phi i) l))) :
    nestedDerivAtZero n report = Complex.I ^ n * omega (orderedProduct n phi) := by
  have hfun : report =
      fun l => omega (pulseProduct n (fun i => Complex.I • phi i) l) := by
    funext l
    exact chronometricRamseyQuadratures_injective (hreport l)
  rw [hfun]
  exact nestedDerivAtZero_pulseProduct_imaginary n phi omega

end BanachAlgebra

end GaloisForLFunctions.HTGeometry
