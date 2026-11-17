import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicHypergeometricFormalODE

import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Exact formal biconfluent-Heun termination

The differential operator gives the full three-term coefficient recurrence,
including its singular initial equation. Polynomial termination requires
spectral tuning, a terminal zero, and every exceptional resonant tail zero.
For nonnegative real part of the exponent parameter, only the usual two
conditions remain. This extends the truncation mechanism in Castro,
arXiv:2611.20963, while retaining the collision equations.
-/

open scoped PowerSeries
noncomputable section
namespace GaloisForLFunctions.HTGeometry.Heun
open _root_.RHTower

/-- The canonical biconfluent-Heun expression on actual formal power series. -/
def formalAction (α β γ q : ℂ) (f : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  PowerSeries.X * PowerSeries.derivative ℂ (PowerSeries.derivative ℂ f) +
    PowerSeries.C (1 + α) * PowerSeries.derivative ℂ f -
    PowerSeries.C β * hypergeometricEulerOperator f -
    PowerSeries.C 2 * (PowerSeries.X * hypergeometricEulerOperator f) +
    PowerSeries.C (γ - α - 2) * (PowerSeries.X * f) - PowerSeries.C q * f

/-- Coefficient recurrence, including the singular initial equation. -/
def CoefficientRecurrence (α β γ q : ℂ) (d : ℕ → ℂ) : Prop :=
  (1 + α) * d 1 = q * d 0 ∧ ∀ n : ℕ,
    ((n + 2 : ℕ) : ℂ) * (((n + 2 : ℕ) : ℂ) + α) * d (n + 2) =
      (β * ((n + 1 : ℕ) : ℂ) + q) * d (n + 1) +
        (2 * ((n + 1 : ℕ) : ℂ) + α - γ) * d n

private theorem coeff_formalAction_zero (α β γ q : ℂ) (f : ℂ⟦X⟧) :
    PowerSeries.coeff 0 (formalAction α β γ q f) =
      (1 + α) * PowerSeries.coeff 1 f - q * PowerSeries.coeff 0 f := by
  simp only [formalAction, map_sub (PowerSeries.coeff 0), map_add (PowerSeries.coeff 0), PowerSeries.coeff_zero_X_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_derivative,
    coeff_hypergeometricEulerOperator, Nat.cast_zero, zero_mul, mul_zero, mul_one, zero_add, add_zero, sub_zero]

private theorem coeff_formalAction_succ (α β γ q : ℂ) (f : ℂ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff (n + 1) (formalAction α β γ q f) =
      ((n + 2 : ℕ) : ℂ) * (((n + 2 : ℕ) : ℂ) + α) * PowerSeries.coeff (n + 2) f -
        ((β * ((n + 1 : ℕ) : ℂ) + q) * PowerSeries.coeff (n + 1) f +
          (2 * ((n + 1 : ℕ) : ℂ) + α - γ) * PowerSeries.coeff n f) := by
  simp only [formalAction, map_sub (PowerSeries.coeff (n + 1)), map_add (PowerSeries.coeff (n + 1)), PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
    coeff_hypergeometricEulerOperator, show n + 1 + 1 = n + 2 by omega,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- The recurrence is equivalent to the actual differential equation, with no omitted collision equation. -/
theorem formalAction_eq_zero_iff (α β γ q : ℂ) (f : ℂ⟦X⟧) :
    formalAction α β γ q f = 0 ↔
      CoefficientRecurrence α β γ q (fun n => PowerSeries.coeff n f) := by
  constructor
  · intro h
    have h0 := congrArg (PowerSeries.coeff 0) h
    rw [coeff_formalAction_zero, map_zero] at h0
    refine ⟨sub_eq_zero.mp h0, ?_⟩
    intro n
    have hn := congrArg (PowerSeries.coeff (n + 1)) h
    rw [coeff_formalAction_succ, map_zero] at hn
    exact sub_eq_zero.mp hn
  · rintro ⟨h0, hs⟩
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => rw [coeff_formalAction_zero, map_zero]; exact sub_eq_zero.mpr h0
    | succ n => rw [coeff_formalAction_succ, map_zero]; exact sub_eq_zero.mpr (hs n)

/-- At resonance, vanishing of the exceptional free tail coefficient is the exact extra termination condition. -/
theorem recurrence_tail_zero_iff (α β γ q : ℂ) (N : ℕ) (d : ℕ → ℂ)
    (hd : CoefficientRecurrence α β γ q d) (hγ : γ = α + 2 * N + 2) :
    (∀ r : ℕ, N < r → d r = 0) ↔
      d (N + 1) = 0 ∧ ∀ r : ℕ, N + 1 < r → (r : ℂ) + α = 0 → d r = 0 := by
  constructor
  · intro h
    exact ⟨h _ (by omega), fun r hr _ => h r (by omega)⟩
  · rintro ⟨hfirst, hres⟩ r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr
      by_cases hboundary : r = N + 1
      · rw [hboundary]
        exact hfirst
      · have hr' : N + 1 < r := by omega
        by_cases hz : (r : ℂ) + α = 0
        · exact hres r hr' hz
        · let n := r - 2
          have hn : n + 2 = r := by dsimp [n]; omega
          have hnN : N ≤ n := by omega
          have hp : d (n + 1) = 0 := ih (n + 1) (by omega) (by omega)
          have hb : (2 * ((n + 1 : ℕ) : ℂ) + α - γ) * d n = 0 := by
            by_cases he : n = N
            · rw [he, hγ]
              push_cast
              ring
            · rw [ih n (by omega) (by omega), mul_zero]
          have hrec := hd.2 n
          rw [hp, mul_zero, zero_add, hb, hn] at hrec
          have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
          exact (mul_eq_zero.mp hrec).resolve_left (mul_ne_zero hr0 hz)

/-- The formal solution terminates precisely after the tuned coefficient and every resonant tail coefficient vanish. -/
theorem formal_solution_tail_zero_iff (α β γ q : ℂ) (N : ℕ) (f : ℂ⟦X⟧)
    (hf : formalAction α β γ q f = 0) (hγ : γ = α + 2 * N + 2) :
    (∀ r : ℕ, N < r → PowerSeries.coeff r f = 0) ↔
      PowerSeries.coeff (N + 1) f = 0 ∧
        ∀ r : ℕ, N + 1 < r → (r : ℂ) + α = 0 → PowerSeries.coeff r f = 0 :=
  recurrence_tail_zero_iff α β γ q N _ ((formalAction_eq_zero_iff α β γ q f).mp hf) hγ

/-- The physical nonnegative parameter range has no tail resonance, so one terminal coefficient suffices. -/
theorem formal_solution_tail_zero_iff_of_nonneg_re (α β γ q : ℂ) (N : ℕ) (f : ℂ⟦X⟧)
    (hf : formalAction α β γ q f = 0) (hγ : γ = α + 2 * N + 2) (hα : 0 ≤ α.re) :
    (∀ r : ℕ, N < r → PowerSeries.coeff r f = 0) ↔ PowerSeries.coeff (N + 1) f = 0 := by
  rw [formal_solution_tail_zero_iff α β γ q N f hf hγ]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    intro r hr hz
    have hRe := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hRe
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    linarith only [hRe, hα, hrpos]

/-- The leading coefficient of a terminating nonzero solution forces the spectral tuning. -/
theorem recurrence_tuning_of_tail_zero (α β γ q : ℂ) (N : ℕ) (d : ℕ → ℂ)
    (hd : CoefficientRecurrence α β γ q d) (hN : d N ≠ 0)
    (htail : ∀ r : ℕ, N < r → d r = 0) : γ = α + 2 * N + 2 := by
  have hrec := hd.2 N
  rw [htail (N + 2) (by omega), htail (N + 1) (by omega), mul_zero,
    mul_zero, zero_add] at hrec
  have hfactor := (mul_eq_zero.mp hrec.symm).resolve_right hN
  push_cast at hfactor
  linear_combination -hfactor

/-- Exact termination criterion, including the spectral tuning and every resonant collision. -/
theorem recurrence_exact_degree_iff (α β γ q : ℂ) (N : ℕ) (d : ℕ → ℂ)
    (hd : CoefficientRecurrence α β γ q d) (hN : d N ≠ 0) :
    (∀ r : ℕ, N < r → d r = 0) ↔
      γ = α + 2 * N + 2 ∧ d (N + 1) = 0 ∧
        ∀ r : ℕ, N + 1 < r → (r : ℂ) + α = 0 → d r = 0 := by
  constructor
  · intro h
    have hγ := recurrence_tuning_of_tail_zero α β γ q N d hd hN h
    exact ⟨hγ, (recurrence_tail_zero_iff α β γ q N d hd hγ).mp h⟩
  · rintro ⟨hγ, ht⟩
    exact (recurrence_tail_zero_iff α β γ q N d hd hγ).mpr ht

/-- A series has no coefficients beyond degree `N` exactly when its truncation is the whole series. -/
theorem eq_trunc_iff_tail_zero (N : ℕ) (f : ℂ⟦X⟧) :
    f = (PowerSeries.trunc (N + 1) f : ℂ⟦X⟧) ↔
      ∀ r : ℕ, N < r → PowerSeries.coeff r f = 0 := by
  constructor
  · intro h r hr
    have he := congrArg (PowerSeries.coeff r) h
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_neg (by omega)] at he
    exact he
  · intro h
    apply PowerSeries.ext
    intro r
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hr
    · rfl
    · exact h r (by omega)

/-- Polynomial termination of an actual Heun solution is characterized by tuning and collision data. -/
theorem formal_solution_eq_trunc_iff (α β γ q : ℂ) (N : ℕ) (f : ℂ⟦X⟧)
    (hf : formalAction α β γ q f = 0) (hN : PowerSeries.coeff N f ≠ 0) :
    f = (PowerSeries.trunc (N + 1) f : ℂ⟦X⟧) ↔
      γ = α + 2 * N + 2 ∧ PowerSeries.coeff (N + 1) f = 0 ∧
        ∀ r : ℕ, N + 1 < r → (r : ℂ) + α = 0 → PowerSeries.coeff r f = 0 := by
  rw [eq_trunc_iff_tail_zero]
  exact recurrence_exact_degree_iff α β γ q N _
    ((formalAction_eq_zero_iff α β γ q f).mp hf) hN

/-- In the nonnegative parameter range, tuning and one terminal coefficient are necessary and sufficient. -/
theorem formal_solution_eq_trunc_iff_of_nonneg_re (α β γ q : ℂ) (N : ℕ) (f : ℂ⟦X⟧)
    (hf : formalAction α β γ q f = 0) (hN : PowerSeries.coeff N f ≠ 0) (hα : 0 ≤ α.re) :
    f = (PowerSeries.trunc (N + 1) f : ℂ⟦X⟧) ↔
      γ = α + 2 * N + 2 ∧ PowerSeries.coeff (N + 1) f = 0 := by
  rw [eq_trunc_iff_tail_zero]
  constructor
  · intro ht
    exact ⟨recurrence_tuning_of_tail_zero α β γ q N _
      ((formalAction_eq_zero_iff α β γ q f).mp hf) hN ht, ht _ (by omega)⟩
  · rintro ⟨hγ, ht⟩
    exact (formal_solution_tail_zero_iff_of_nonneg_re α β γ q N f hf hγ hα).mpr ht

#print axioms formal_solution_eq_trunc_iff
#print axioms formal_solution_eq_trunc_iff_of_nonneg_re

#print axioms recurrence_exact_degree_iff

#print axioms formalAction_eq_zero_iff
#print axioms recurrence_tail_zero_iff
#print axioms formal_solution_tail_zero_iff
#print axioms formal_solution_tail_zero_iff_of_nonneg_re

end GaloisForLFunctions.HTGeometry.Heun
