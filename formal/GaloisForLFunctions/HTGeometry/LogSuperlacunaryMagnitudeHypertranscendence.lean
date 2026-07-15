import GaloisForLFunctions.HTGeometry.DigammaPolynomialCarrier
import GaloisForLFunctions.HTGeometry.FormalMahlerIntegerNormalization
import GaloisForLFunctions.HTGeometry.MagnitudeIntegerDominance

/-!
# Eventual log-superlacunary Taylor magnitudes force hypertranscendence

This module closes the finite-prefix gap in the log-superlacunary magnitude theorem. Polynomial
addition is implemented as an invertible translation of every jet coordinate, so differential
algebraicity is invariant under changing finitely many Taylor coefficients. The bad prefix is then
filled by a finite correction polynomial and the unconditional integer-normalized magnitude theorem
applies to the corrected function.
-/

open Filter Finset PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

def jetPolynomialSub (n : ℕ) (p : Polynomial ℂ) :
    Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
  Fin.cases (MvPolynomial.X 0) fun j =>
    MvPolynomial.X j.succ -
      Polynomial.aeval (MvPolynomial.X 0) ((⇑Polynomial.derivative)^[(j : ℕ)] p)

def jetPolynomialAdd (n : ℕ) (p : Polynomial ℂ) :
    Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
  Fin.cases (MvPolynomial.X 0) fun j =>
    MvPolynomial.X j.succ +
      Polynomial.aeval (MvPolynomial.X 0) ((⇑Polynomial.derivative)^[(j : ℕ)] p)

theorem DifferentiallyAlgebraic.add_polynomial {f : ℂ → ℂ}
    (hf : DifferentiallyAlgebraic f) (hfs : ContDiff ℂ (⊤ : ℕ∞) f)
    (p : Polynomial ℂ) :
    DifferentiallyAlgebraic (fun z => f z + p.eval z) := by
  obtain ⟨n, P, hP0, hPz⟩ := hf
  let σ := jetPolynomialSub n p
  let τ := jetPolynomialAdd n p
  let Q := MvPolynomial.bind₁ σ P
  have hτσ : (fun i => MvPolynomial.bind₁ τ (σ i)) =
      (MvPolynomial.X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
    funext i
    induction i using Fin.cases with
    | zero => simp [σ, τ, jetPolynomialSub, jetPolynomialAdd]
    | succ j =>
        simp only [σ, τ, jetPolynomialSub, jetPolynomialAdd, Fin.cases_succ,
          map_sub, MvPolynomial.bind₁_X_right]
        rw [← Polynomial.aeval_algHom_apply (MvPolynomial.bind₁ τ) (MvPolynomial.X 0)
          ((⇑Polynomial.derivative)^[(j : ℕ)] p), MvPolynomial.bind₁_X_right]
        simp [τ, jetPolynomialAdd]
  have hQ0 : Q ≠ 0 := by
    intro hQ
    apply hP0
    have hback : MvPolynomial.bind₁ τ Q = P := by
      rw [show Q = MvPolynomial.bind₁ σ P by rfl, MvPolynomial.bind₁_bind₁, hτσ,
        MvPolynomial.bind₁_X_left]
      simp
    rw [← hback, hQ, map_zero]
  refine ⟨n, Q, hQ0, ?_⟩
  intro z
  rw [show Q = MvPolynomial.bind₁ σ P by rfl, eval_bind₁]
  have hsplit (j : Fin (n + 1)) :
      iteratedDeriv (j : ℕ) (fun w => f w + p.eval w) z =
        iteratedDeriv (j : ℕ) f z +
          ((⇑Polynomial.derivative)^[(j : ℕ)] p).eval z := by
    have hp : ContDiffAt ℂ (j : ℕ) (fun w : ℂ => p.eval w) z := by
      have h := (Polynomial.contDiff_aeval (𝕜 := ℂ) p
        ((j : ℕ) : WithTop ℕ∞)).contDiffAt (x := z)
      simpa only [Polynomial.coe_aeval_eq_eval] using h
    rw [show (fun w => f w + p.eval w) = f + (fun w => p.eval w) from rfl,
      iteratedDeriv_add
      (hfs.contDiffAt.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤)))
      hp,
      iteratedDeriv_polynomial_eval]
  have hvec : (fun i => MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) =>
        iteratedDeriv (j : ℕ) (fun w => f w + p.eval w) z) (σ i)) =
      Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) := by
    funext i
    induction i using Fin.cases with
    | zero => simp [σ, jetPolynomialSub]
    | succ j =>
        simp only [σ, jetPolynomialSub, Fin.cases_succ, map_sub,
          MvPolynomial.eval_X, Fin.cons_succ]
        rw [eval_aeval_X0, Fin.cons_zero, hsplit j]
        ring
  rw [hvec]
  exact hPz z

theorem contDiff_polynomial_eval (p : Polynomial ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => p.eval z) := by
  simpa only [Polynomial.coe_aeval_eq_eval] using
    (Polynomial.contDiff_aeval (𝕜 := ℂ) p (⊤ : ℕ∞))

theorem differentiallyAlgebraic_add_polynomial_iff {f : ℂ → ℂ}
    (hfs : ContDiff ℂ (⊤ : ℕ∞) f) (p : Polynomial ℂ) :
    DifferentiallyAlgebraic (fun z => f z + p.eval z) ↔
      DifferentiallyAlgebraic f := by
  constructor
  · intro h
    have hsum : ContDiff ℂ (⊤ : ℕ∞) (fun z => f z + p.eval z) :=
      hfs.add (contDiff_polynomial_eval p)
    simpa using DifferentiallyAlgebraic.add_polynomial h hsum (-p)
  · intro h
    exact DifferentiallyAlgebraic.add_polynomial h hfs p

theorem hypertranscendental_add_polynomial_iff {f : ℂ → ℂ}
    (hfs : ContDiff ℂ (⊤ : ℕ∞) f) (p : Polynomial ℂ) :
    Hypertranscendental (fun z => f z + p.eval z) ↔ Hypertranscendental f :=
  (differentiallyAlgebraic_add_polynomial_iff hfs p).not

theorem taylorPS_polynomial_eval (p : Polynomial ℂ) :
    taylorPS (fun z : ℂ => p.eval z) = (p : PowerSeries ℂ) := by
  ext k
  rw [coeff_taylorPS, iteratedDeriv_polynomial_eval, Polynomial.coeff_coe,
    ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

def finiteTaylorCorrection (F : PowerSeries ℂ) (T : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range T,
    Polynomial.monomial i ((Real.exp (-1) : ℂ) - PowerSeries.coeff i F)

@[simp]
theorem coeff_finiteTaylorCorrection (F : PowerSeries ℂ) (T i : ℕ) :
    Polynomial.coeff (finiteTaylorCorrection F T) i =
      if i < T then (Real.exp (-1) : ℂ) - PowerSeries.coeff i F else 0 := by
  classical
  by_cases hi : i < T
  · simp [finiteTaylorCorrection, Polynomial.coeff_monomial, eq_comm, hi]
  · simp [finiteTaylorCorrection, Polynomial.coeff_monomial, eq_comm, hi]

/-- Eventual log-superlacunarity, including an arbitrary finite Taylor prefix, forces
hypertranscendence. -/
theorem hypertranscendental_of_eventually_logSuperlacunary {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) {b : ℕ → ℝ}
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hbpos : ∀ᶠ i in atTop, 0 < b i)
    (hratio : Tendsto (fun i => b (i + 1) / b i) atTop atTop) :
    Hypertranscendental f := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hb.and hbpos)
  let F := taylorPS f
  let p := finiteTaylorCorrection F T
  let g : ℂ → ℂ := fun z => f z + p.eval z
  let b' : ℕ → ℝ := fun i => if i < T then 1 else b i
  have hp : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => p.eval z) :=
    contDiff_polynomial_eval p
  have hgsm : ContDiff ℂ (⊤ : ℕ∞) g := by
    exact hf.add hp
  have htaylor : taylorPS g = F + (p : PowerSeries ℂ) := by
    change taylorPS (fun z => f z + p.eval z) = _
    rw [show (fun z => f z + p.eval z) = f + (fun z => p.eval z) from rfl,
      taylorPS_add hf hp, taylorPS_polynomial_eval]
  have hb' : ∀ i, ‖PowerSeries.coeff i (taylorPS g)‖ = Real.exp (-b' i) := by
    intro i
    rw [htaylor, map_add, Polynomial.coeff_coe,
      coeff_finiteTaylorCorrection]
    by_cases hi : i < T
    · simp [b', hi, Complex.norm_exp]
    · have hiT : T ≤ i := Nat.le_of_not_gt hi
      simp only [if_neg hi, add_zero]
      rw [show b' i = b i by simp [b', hi]]
      change ‖PowerSeries.coeff i F‖ = Real.exp (-b i)
      simpa only [F] using (hT i hiT).1
  have hb'pos : ∀ i, 0 < b' i := by
    intro i
    by_cases hi : i < T
    · simp [b', hi]
    · exact (by simpa [b', hi] using (hT i (Nat.le_of_not_gt hi)).2)
  have hratio' : Tendsto (fun i => b' (i + 1) / b' i) atTop atTop := by
    refine hratio.congr' ?_
    filter_upwards [eventually_ge_atTop T] with i hi
    have hi0 : ¬ i < T := Nat.not_lt.mpr hi
    have hi1 : ¬ i + 1 < T := Nat.not_lt.mpr (hi.trans (Nat.le_add_right i 1))
    simp [b', hi0, hi1]
  have hg : Hypertranscendental g :=
    hypertranscendental_of_mahler_logSuperlacunary hgsm hb' hb'pos hratio'
      (fun _n _Q hQ hrel => formal_mahler_integer_normalization hQ hrel)
  exact (hypertranscendental_add_polynomial_iff hf p).mp hg

end

end GaloisForLFunctions

