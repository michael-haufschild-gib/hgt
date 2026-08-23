import GaloisForLFunctions.HTGeometry.GeneralDirichletLandau

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Mixed iterated derivative of an additive two-variable kernel. -/
def mixedAddIteratedDeriv (p q : ℕ) (F : ℂ → ℂ) (s t : ℂ) : ℂ :=
  iteratedDeriv p (fun u => iteratedDeriv q (fun v => F (u + v)) t) s

/-- Mixed derivatives of `F(s+t)` combine to the corresponding one-variable derivative. -/
theorem mixedAddIteratedDeriv_eq (p q : ℕ) (F : ℂ → ℂ) (s t : ℂ) :
    mixedAddIteratedDeriv p q F s t = iteratedDeriv (p + q) F (s + t) := by
  unfold mixedAddIteratedDeriv
  have hinner : (fun u => iteratedDeriv q (fun v => F (u + v)) t) =
      fun u => iteratedDeriv q F (u + t) := by
    funext u
    exact congrFun (iteratedDeriv_comp_const_add q F u) t
  rw [hinner]
  rw [show iteratedDeriv p (fun u => iteratedDeriv q F (u + t)) =
      fun u => iteratedDeriv p (iteratedDeriv q F) (u + t) from
    iteratedDeriv_comp_add_const p (iteratedDeriv q F) t]
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate]
  rw [Function.iterate_add_apply]

/-- Positive natural coordinates used by ordinary Dirichlet series. -/
abbrev positiveDirichletCoordinate := {n : ℕ // 0 < n}

/-- Natural logarithmic frequency on positive integers. -/
def positiveDirichletLogFrequency (n : positiveDirichletCoordinate) : ℝ := Real.log n.1

theorem positiveDirichletLogFrequency_nonneg (n : positiveDirichletCoordinate) :
    0 ≤ positiveDirichletLogFrequency n := by
  rw [positiveDirichletLogFrequency]
  exact Real.log_nonneg (by exact_mod_cast n.2)

/-- Nonnegative Dirichlet coefficients, finite at `sigma0`, with one positive coefficient above
frequency zero. Analytic prerequisites are carried as data, not theorem premises. -/
structure PositiveDiagonalCompletionDirichletData (sigma0 : ℝ) where
  coeff : ℕ → ℝ
  coeff_nonneg : ∀ n : ℕ, 0 < n → 0 ≤ coeff n
  summable_at : Summable (gdTwistTerm
    (fun n : positiveDirichletCoordinate => coeff n.1) positiveDirichletLogFrequency sigma0 0)
  positiveAtom : {n : ℕ // 1 < n ∧ 0 < coeff n}

namespace PositiveDiagonalCompletionDirichletData

variable {sigma0 : ℝ} (D : PositiveDiagonalCompletionDirichletData sigma0)

/-- Coefficient family on positive coordinates. -/
def positiveCoeff (n : positiveDirichletCoordinate) : ℝ := D.coeff n.1

theorem positiveCoeff_nonneg (n : positiveDirichletCoordinate) : 0 ≤ D.positiveCoeff n :=
  D.coeff_nonneg n.1 n.2

/-- Dirichlet completion symbol as a general Dirichlet series with frequencies `log n`. -/
def series (s : ℂ) : ℂ := gdSeries D.positiveCoeff positiveDirichletLogFrequency s

private def witnessCoordinate : positiveDirichletCoordinate :=
  ⟨D.positiveAtom.1, lt_trans Nat.zero_lt_one D.positiveAtom.2.1⟩

private theorem witnessTerm_pos (sigma : ℝ) (k : ℕ) :
    0 < gdTwistTerm D.positiveCoeff positiveDirichletLogFrequency sigma k
      D.witnessCoordinate := by
  rw [gdTwistTerm, positiveCoeff, positiveDirichletLogFrequency]
  have hlog : 0 < Real.log (D.positiveAtom.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast D.positiveAtom.2.1)
  have hcoeff : 0 < D.coeff D.positiveAtom.1 := D.positiveAtom.2.2
  positivity

private theorem moment_pos_of_summable (sigma : ℝ) (k : ℕ)
    (hsum : Summable (gdTwistTerm D.positiveCoeff positiveDirichletLogFrequency sigma k)) :
    0 < gdMoment D.positiveCoeff positiveDirichletLogFrequency sigma k := by
  have hnonneg : ∀ j : positiveDirichletCoordinate,
      0 ≤ gdTwistTerm D.positiveCoeff positiveDirichletLogFrequency sigma k j :=
    gdTwistTerm_nonneg D.positiveCoeff_nonneg positiveDirichletLogFrequency_nonneg sigma k
  have hle : gdTwistTerm D.positiveCoeff positiveDirichletLogFrequency sigma k
      D.witnessCoordinate ≤ gdMoment D.positiveCoeff positiveDirichletLogFrequency sigma k := by
    rw [gdMoment]
    simpa using hsum.sum_le_tsum {D.witnessCoordinate} (fun j _ => hnonneg j)
  exact (D.witnessTerm_pos sigma k).trans_le hle

/-- Finite critical symbol of a nonzero nonnegative correction is strictly positive. -/
theorem criticalValue_pos :
    0 < gdMoment D.positiveCoeff positiveDirichletLogFrequency sigma0 0 :=
  D.moment_pos_of_summable sigma0 0 D.summable_at

/-- Every logarithmic moment strictly to the right of the finite abscissa is finite and positive. -/
theorem shiftedMoment_pos (h : {x : ℝ // 0 < x}) (k : ℕ) :
    0 < gdMoment D.positiveCoeff positiveDirichletLogFrequency (sigma0 + h.1) k := by
  exact D.moment_pos_of_summable _ k
    (summable_gdTwistTerm D.positiveCoeff_nonneg positiveDirichletLogFrequency_nonneg
      D.summable_at h.2 k)

/-- Exact even derivative formula for the positive completion symbol. -/
theorem iteratedDeriv_series_even (h : {x : ℝ // 0 < x}) (m : ℕ) :
    iteratedDeriv (2 * m) D.series (((sigma0 + h.1 : ℝ) : ℂ)) =
      ((gdMoment D.positiveCoeff positiveDirichletLogFrequency
        (sigma0 + h.1) (2 * m) : ℝ) : ℂ) := by
  change iteratedDeriv (2 * m) (gdSeries D.positiveCoeff positiveDirichletLogFrequency)
      (((sigma0 + h.1 : ℝ) : ℂ)) = _
  simpa [pow_mul] using
    (iteratedDeriv_gdSeries D.positiveCoeff_nonneg positiveDirichletLogFrequency_nonneg
      D.summable_at h.2 (2 * m))

/-- Every even derivative strictly to the right has strictly positive real part. -/
theorem re_iteratedDeriv_series_even_pos (h : {x : ℝ // 0 < x}) (m : ℕ) :
    0 < (iteratedDeriv (2 * m) D.series (((sigma0 + h.1 : ℝ) : ℂ))).re := by
  rw [D.iteratedDeriv_series_even h m]
  exact D.shiftedMoment_pos h (2 * m)

/-- At a reflected pair whose real sum lies strictly right of the finite abscissa, the mixed jet
is the positive even logarithmic moment. -/
theorem mixed_conj_even_eq_moment
    (s : {z : ℂ // sigma0 < 2 * z.re}) (m : ℕ) :
    mixedAddIteratedDeriv m m D.series s.1 (star s.1) =
      ((gdMoment D.positiveCoeff positiveDirichletLogFrequency
        (2 * s.1.re) (2 * m) : ℝ) : ℂ) := by
  let h : {x : ℝ // 0 < x} := ⟨2 * s.1.re - sigma0, by linarith [s.2]⟩
  rw [mixedAddIteratedDeriv_eq]
  have horder : m + m = 2 * m := by omega
  rw [horder]
  have hpoint : s.1 + star s.1 = (((sigma0 + h.1 : ℝ) : ℂ)) := by
    apply Complex.ext
    · simp [h]
      ring
    · simp
  rw [hpoint, D.iteratedDeriv_series_even h m]
  congr 3
  simp [h]

/-- The reflected mixed even jet is strictly positive. -/
theorem re_mixed_conj_even_pos
    (s : {z : ℂ // sigma0 < 2 * z.re}) (m : ℕ) :
    0 < (mixedAddIteratedDeriv m m D.series s.1 (star s.1)).re := by
  rw [D.mixed_conj_even_eq_moment s m]
  let h : {x : ℝ // 0 < x} := ⟨2 * s.1.re - sigma0, by linarith [s.2]⟩
  have hcenter : sigma0 + h.1 = 2 * s.1.re := by simp [h]
  rw [← hcenter]
  exact D.shiftedMoment_pos h (2 * m)

end PositiveDiagonalCompletionDirichletData

end

end RHTower
