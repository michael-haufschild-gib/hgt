import GaloisForLFunctions.HTGeometry.AutonomousDifferentialAlgebraic
import GaloisForLFunctions.HTGeometry.FundamentalParallelogram

/-!
# A periodic differentially algebraic function has an autonomous equation

The corpus records the easy direction: a nonzero autonomous annihilator makes a function
differentially algebraic.  The converse is false in general — `z` itself satisfies only equations
mentioning the point slot — but it is true for periodic functions, and that is the direction the
period layer needs.

The mechanism is elimination of the point slot along the period.  Split a differential polynomial
`P` as a polynomial in the point variable with coefficients in the jet variables.  All jets of a
periodic function are periodic, so at `z + k·c` the jet vector is the one at `z` and the relation
says the univariate polynomial obtained by evaluating the coefficients on that jet vector vanishes at
`z + k·c` for **every** integer `k`.  A polynomial with infinitely many roots is zero, so every
coefficient vanishes on the jets — and the leading one is a nonzero autonomous relation.

* `periodic_iteratedDeriv` — the jets of a periodic function are periodic;
* **`exists_autonomousJet_of_periodic`** — the descent;
* `differentiallyAlgebraic_of_autonomousJet` — the converse, by dropping the point slot;
* **`differentiallyAlgebraic_iff_autonomousJet_of_periodic`** — for a periodic function,
  differential algebraicity *is* autonomous differential algebraicity.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- Every iterated derivative of a periodic function is periodic. -/
theorem periodic_iteratedDeriv {f : ℂ → ℂ} {c : ℂ} (h : Function.Periodic f c) (j : ℕ) :
    Function.Periodic (iteratedDeriv j f) c := by
  induction j with
  | zero => simpa [iteratedDeriv_zero] using h
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact periodic_deriv ih

/-- The jet vector of a periodic function is unchanged along the period lattice. -/
theorem iteratedDeriv_add_zsmul {f : ℂ → ℂ} {c : ℂ} (h : Function.Periodic f c) (j : ℕ) (k : ℤ)
    (z : ℂ) : iteratedDeriv j f (z + k • c) = iteratedDeriv j f z :=
  ((periodic_iteratedDeriv h j).zsmul k) z

/-! ### The descent -/

/-- **Elimination of the point slot along a period.**  A differentially algebraic periodic function
satisfies a nonzero algebraic differential equation with no dependence on the point. -/
theorem exists_autonomousJet_of_periodic {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hper : Function.Periodic f c) (hDA : DifferentiallyAlgebraic f) :
    ∃ (n : ℕ) (R : MvPolynomial (Fin (n + 1)) ℂ), R ≠ 0 ∧
      ∀ z, eval (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) R = 0 := by
  obtain ⟨n, P, hP0, hP⟩ := hDA
  set Pc : Polynomial (MvPolynomial (Fin (n + 1)) ℂ) := finSuccEquiv ℂ (n + 1) P with hPcdef
  have hPc0 : Pc ≠ 0 := by
    intro h0
    apply hP0
    have := congrArg (finSuccEquiv ℂ (n + 1)).symm h0
    simpa [hPcdef] using this
  have hcoeff : ∀ z : ℂ, ∀ m : ℕ,
      eval (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) (Pc.coeff m) = 0 := by
    intro z m
    set v : Fin (n + 1) → ℂ := fun j => iteratedDeriv (j : ℕ) f z with hv
    have hroot : ∀ k : ℤ,
        Polynomial.eval (z + k • c) (Polynomial.map (eval v) Pc) = 0 := by
      intro k
      have hjet : (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f (z + k • c)) = v := by
        funext j
        rw [hv]
        exact iteratedDeriv_add_zsmul hper (j : ℕ) k z
      have hz := hP (z + k • c)
      rw [hjet, eval_eq_eval_mv_eval'] at hz
      exact hz
    have hinf : {x : ℂ | (Polynomial.map (eval v) Pc).IsRoot x}.Infinite := by
      refine Set.Infinite.mono (s := Set.range fun k : ℤ => z + k • c) ?_ ?_
      · rintro _ ⟨k, rfl⟩
        exact hroot k
      · refine Set.infinite_range_of_injective ?_
        intro k l hkl
        have : (k : ℂ) * c = (l : ℂ) * c := by
          simpa [zsmul_eq_mul] using add_left_cancel hkl
        have hkl' : (k : ℂ) = (l : ℂ) := mul_right_cancel₀ hc this
        exact_mod_cast hkl'
    have hzero : Polynomial.map (eval v) Pc = 0 :=
      Polynomial.eq_zero_of_infinite_isRoot _ hinf
    have := congrArg (fun p : Polynomial ℂ => p.coeff m) hzero
    simpa [Polynomial.coeff_map] using this
  refine ⟨n, Pc.coeff Pc.natDegree, ?_, fun z => hcoeff z Pc.natDegree⟩
  exact Polynomial.leadingCoeff_ne_zero.mpr hPc0

/-! ### The converse and the equivalence -/

/-- An autonomous relation in the jets is a differential relation: adjoin the point slot and forget
it. -/
theorem differentiallyAlgebraic_of_autonomousJet {f : ℂ → ℂ} {n : ℕ}
    {R : MvPolynomial (Fin (n + 1)) ℂ} (hR : R ≠ 0)
    (h : ∀ z, eval (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) R = 0) :
    DifferentiallyAlgebraic f := by
  refine ⟨n, rename Fin.succ R, ?_, fun z => ?_⟩
  · intro h0
    exact hR (rename_injective _ (Fin.succ_injective _) (by simpa using h0))
  · rw [eval_rename]
    exact h z

/-- **For a periodic function, differential algebraicity is autonomous differential
algebraicity.** -/
theorem differentiallyAlgebraic_iff_autonomousJet_of_periodic {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hper : Function.Periodic f c) :
    DifferentiallyAlgebraic f ↔
      ∃ (n : ℕ) (R : MvPolynomial (Fin (n + 1)) ℂ), R ≠ 0 ∧
        ∀ z, eval (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) R = 0 := by
  refine ⟨exists_autonomousJet_of_periodic hc hper, ?_⟩
  rintro ⟨n, R, hR, h⟩
  exact differentiallyAlgebraic_of_autonomousJet hR h

/-- **Hypertranscendence of a periodic function is exactly the absence of an autonomous
equation.** -/
theorem hypertranscendental_iff_no_autonomousJet_of_periodic {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hper : Function.Periodic f c) :
    Hypertranscendental f ↔
      ∀ (n : ℕ) (R : MvPolynomial (Fin (n + 1)) ℂ),
        (∀ z, eval (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) R = 0) → R = 0 := by
  rw [Hypertranscendental, differentiallyAlgebraic_iff_autonomousJet_of_periodic hc hper]
  constructor
  · intro h n R hRz
    by_contra hR
    exact h ⟨n, R, hR, hRz⟩
  · rintro h ⟨n, R, hR, hRz⟩
    exact hR (h n R hRz)

end GaloisForLFunctions.HTGeometry
