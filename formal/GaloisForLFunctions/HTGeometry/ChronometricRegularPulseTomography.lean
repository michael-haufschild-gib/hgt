import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.Complemented
import GaloisForLFunctions.HTGeometry.ChronometricOrderedTomography

/-!
# Ordered clock tomography for a regular family with unbounded generators

A physical controlled clock pulse `U_j(λ) = exp(iλΦ(f_j))` is a strongly continuous one-parameter
unitary group whose generator is unbounded. The only structure the ordered-correlation recovery
actually uses is:

* each pulse is a bounded operator for each fixed coupling;
* the generators share one invariant domain, on which they are merely linear — no continuity,
  boundedness, self-adjointness or group law is required;
* on that domain each pulse family is differentiable at zero coupling with derivative `i` times its
  generator.

Under exactly these hypotheses, differentiating the characteristic functional once in each coupling
at zero recovers the complete ordered correlation `iⁿ ω(Φ_0 ⋯ Φ_{n-1} v)`.

This is the regular-family form of the recovery identity: the generators here are genuinely
unbounded linear maps on a domain, not elements of a Banach algebra.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- Iterated mixed derivative at zero in real couplings, one coupling at a time in causal order. -/
noncomputable def nestedRealDerivAtZero : (n : ℕ) → ((Fin n → ℝ) → ℂ) → ℂ
  | 0, F => F Fin.elim0
  | (n + 1), F => deriv (fun t : ℝ => nestedRealDerivAtZero n fun v => F (Fin.cons t v)) 0

@[simp] theorem nestedRealDerivAtZero_zero (F : (Fin 0 → ℝ) → ℂ) :
    nestedRealDerivAtZero 0 F = F Fin.elim0 := rfl

theorem nestedRealDerivAtZero_succ (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℂ) :
    nestedRealDerivAtZero (n + 1) F =
      deriv (fun t : ℝ => nestedRealDerivAtZero n fun v => F (Fin.cons t v)) 0 := rfl

section RegularFamily

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Causally ordered application of a controlled pulse family to a state vector. -/
def orderedPulseApply :
    (n : ℕ) → (Fin n → ℝ → (H →L[ℂ] H)) → (Fin n → ℝ) → H → H
  | 0, _, _, x => x
  | (n + 1), pulse, l, x =>
      pulse 0 (l 0) (orderedPulseApply n (fun i => pulse i.succ) (fun i => l i.succ) x)

@[simp] theorem orderedPulseApply_zero (pulse : Fin 0 → ℝ → (H →L[ℂ] H))
    (l : Fin 0 → ℝ) (x : H) : orderedPulseApply 0 pulse l x = x := rfl

@[simp] theorem orderedPulseApply_succ (n : ℕ) (pulse : Fin (n + 1) → ℝ → (H →L[ℂ] H))
    (l : Fin (n + 1) → ℝ) (x : H) :
    orderedPulseApply (n + 1) pulse l x =
      pulse 0 (l 0) (orderedPulseApply n (fun i => pulse i.succ) (fun i => l i.succ) x) := rfl

variable {D : Submodule ℂ H}

/-- Causally ordered composite of the generators, as a linear map of the common domain. -/
def orderedGenerator : (n : ℕ) → (Fin n → (D →ₗ[ℂ] D)) → (D →ₗ[ℂ] D)
  | 0, _ => LinearMap.id
  | (n + 1), gen => (gen 0).comp (orderedGenerator n fun i => gen i.succ)

@[simp] theorem orderedGenerator_zero (gen : Fin 0 → (D →ₗ[ℂ] D)) :
    orderedGenerator 0 gen = LinearMap.id := rfl

@[simp] theorem orderedGenerator_succ (n : ℕ) (gen : Fin (n + 1) → (D →ₗ[ℂ] D)) :
    orderedGenerator (n + 1) gen =
      (gen 0).comp (orderedGenerator n fun i => gen i.succ) := rfl

/-- **Ordered correlation recovery for a regular pulse family with unbounded generators.**

One derivative in each real coupling, taken at zero in causal order, turns the characteristic
functional of the controlled pulse family into `iⁿ` times the ordered generator correlation. -/
theorem nestedRealDerivAtZero_orderedPulseApply :
    ∀ (n : ℕ) (pulse : Fin n → ℝ → (H →L[ℂ] H)) (gen : Fin n → (D →ₗ[ℂ] D)),
      (∀ (j : Fin n) (v : D),
          HasDerivAt (fun t : ℝ => pulse j t (v : H))
            (Complex.I • ((gen j v : D) : H)) 0) →
        ∀ (omega : H →L[ℂ] ℂ) (v : D),
          nestedRealDerivAtZero n
              (fun l => omega (orderedPulseApply n pulse l (v : H))) =
            Complex.I ^ n * omega ((orderedGenerator n gen v : D) : H)
  | 0, _, _, _, omega, v => by simp
  | (n + 1), pulse, gen, hderiv, omega, v => by
    rw [nestedRealDerivAtZero_succ]
    set W : D := orderedGenerator n (fun i => gen i.succ) v with hW
    have hinner : ∀ t : ℝ,
        nestedRealDerivAtZero n
            (fun w => omega (orderedPulseApply (n + 1) pulse (Fin.cons t w) (v : H))) =
          Complex.I ^ n * omega (pulse 0 t (W : H)) := by
      intro t
      have hrw :
          (fun w : Fin n → ℝ =>
              omega (orderedPulseApply (n + 1) pulse (Fin.cons t w) (v : H))) =
            fun w : Fin n → ℝ =>
              (omega.comp (pulse 0 t))
                (orderedPulseApply n (fun i => pulse i.succ) w (v : H)) := by
        funext w
        simp [orderedPulseApply_succ]
      rw [hrw,
        nestedRealDerivAtZero_orderedPulseApply n (fun i => pulse i.succ) (fun i => gen i.succ)
          (fun j w => hderiv j.succ w) (omega.comp (pulse 0 t)) v]
      rfl
    simp only [hinner]
    have hbase : HasDerivAt (fun t : ℝ => pulse 0 t (W : H))
        (Complex.I • ((gen 0 W : D) : H)) 0 := hderiv 0 W
    have hcomp : HasDerivAt (fun t : ℝ => omega (pulse 0 t (W : H)))
        (omega (Complex.I • ((gen 0 W : D) : H))) 0 :=
      (omega.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hbase
    have hscaled : HasDerivAt (fun t : ℝ => Complex.I ^ n * omega (pulse 0 t (W : H)))
        (Complex.I ^ n * omega (Complex.I • ((gen 0 W : D) : H))) 0 :=
      hcomp.const_mul _
    rw [hscaled.deriv, orderedGenerator_succ]
    simp only [map_smul, smul_eq_mul, LinearMap.comp_apply, ← hW]
    ring

end RegularFamily

/-! ## The hypothesis class is inhabited -/

section ScalarPulses

/-- Scalar controlled pulses `exp(i λ c)` on `ℂ`, with generator multiplication by `c`. -/
noncomputable def scalarPulse (c : ℝ) (t : ℝ) : ℂ →L[ℂ] ℂ :=
  (t * c : ℝ) • Complex.I |> Complex.exp |> fun z => z • (ContinuousLinearMap.id ℂ ℂ)

@[simp] theorem scalarPulse_apply (c t : ℝ) (z : ℂ) :
    scalarPulse c t z = Complex.exp (Complex.I * (t * c : ℝ)) * z := by
  simp [scalarPulse, Complex.exp, mul_comm]

/-- Multiplication by a real scalar, as a linear endomorphism of the whole space. -/
noncomputable def scalarGenerator (c : ℝ) : (⊤ : Submodule ℂ ℂ) →ₗ[ℂ] (⊤ : Submodule ℂ ℂ) :=
  (c : ℂ) • LinearMap.id

@[simp] theorem scalarGenerator_apply (c : ℝ) (v : (⊤ : Submodule ℂ ℂ)) :
    ((scalarGenerator c v : (⊤ : Submodule ℂ ℂ)) : ℂ) = (c : ℂ) * (v : ℂ) := rfl

theorem hasDerivAt_scalarPulse (c : ℝ) (v : (⊤ : Submodule ℂ ℂ)) :
    HasDerivAt (fun t : ℝ => scalarPulse c t (v : ℂ))
      (Complex.I • ((scalarGenerator c v : (⊤ : Submodule ℂ ℂ)) : ℂ)) 0 := by
  have hbase : HasDerivAt (fun t : ℝ => Complex.I * (t * c : ℝ))
      (Complex.I * (c : ℂ)) 0 := by
    have h : HasDerivAt (fun t : ℝ => ((t : ℂ) * (c : ℂ))) ((c : ℂ)) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (c : ℂ)
    simpa [mul_comm] using h.const_mul Complex.I
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (t * c : ℝ)))
      (Complex.exp (Complex.I * ((0 : ℝ) * c : ℝ)) * (Complex.I * (c : ℂ))) 0 :=
    hbase.cexp
  have hmul := hexp.mul_const (v : ℂ)
  have hrw : (fun t : ℝ => Complex.exp (Complex.I * (t * c : ℝ)) * (v : ℂ)) =
      fun t : ℝ => scalarPulse c t (v : ℂ) := by
    funext t
    rw [scalarPulse_apply]
  rw [hrw] at hmul
  have hval : Complex.I • ((scalarGenerator c v : (⊤ : Submodule ℂ ℂ)) : ℂ) =
      Complex.exp (Complex.I * ((0 : ℝ) * c : ℝ)) * (Complex.I * (c : ℂ)) * (v : ℂ) := by
    have h0 : Complex.exp (Complex.I * ((0 : ℝ) * c : ℝ)) = 1 := by norm_num
    rw [h0, scalarGenerator_apply]
    simp only [smul_eq_mul]
    ring
  rw [hval]
  exact hmul

/-- **The regular-family hypotheses are satisfiable.** Scalar phase pulses with real frequencies
form a regular family with a common invariant domain. -/
theorem exists_regularPulseFamily (n : ℕ) (c : Fin n → ℝ) :
    ∃ (pulse : Fin n → ℝ → (ℂ →L[ℂ] ℂ))
      (gen : Fin n → ((⊤ : Submodule ℂ ℂ) →ₗ[ℂ] (⊤ : Submodule ℂ ℂ))),
      ∀ (j : Fin n) (v : (⊤ : Submodule ℂ ℂ)),
        HasDerivAt (fun t : ℝ => pulse j t (v : ℂ))
          (Complex.I • ((gen j v : (⊤ : Submodule ℂ ℂ)) : ℂ)) 0 :=
  ⟨fun j => scalarPulse (c j), fun j => scalarGenerator (c j),
    fun j v => hasDerivAt_scalarPulse (c j) v⟩

end ScalarPulses

end GaloisForLFunctions.HTGeometry
