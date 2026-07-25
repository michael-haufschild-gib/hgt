import GaloisForLFunctions.HTGeometry.ShiftTwistDescent
import Mathlib

/-!
# Forward differences and decay of polynomial values

The forward difference `fwdDiff P = P(X+1) - P` lowers the degree by exactly one and multiplies the
leading coefficient by the degree.  Iterating it `deg P` times therefore produces the constant
`(deg P)! * leadingCoeff P`.

Since each forward difference of a sequence tending to zero again tends to zero, a polynomial whose
values along the natural numbers tend to zero must vanish.  This is the elementary decay principle
used to force an exponentially small rational function to be identically zero.
-/

open Polynomial Filter

namespace HTGeometry

/-- The forward difference operator on `C[X]`. -/
noncomputable def fwdDiff (P : ℂ[X]) : ℂ[X] := P.comp (X + 1) - P

theorem fwdDiff_eq_shiftTwist (P : ℂ[X]) :
    fwdDiff P = shiftTwist (RingEquiv.refl ℂ) 1 P - P := by
  rw [fwdDiff, shiftTwist_refl, Polynomial.C_1]

@[simp] theorem fwdDiff_eval (P : ℂ[X]) (z : ℂ) :
    (fwdDiff P).eval z = P.eval (z + 1) - P.eval z := by
  simp [fwdDiff]

/-- Above the subleading degree the forward difference vanishes. -/
theorem fwdDiff_coeff_of_natDegree_le (P : ℂ[X]) {k : ℕ} (hk : P.natDegree ≤ k) :
    (fwdDiff P).coeff k = 0 := by
  rw [fwdDiff_eq_shiftTwist, Polynomial.coeff_sub]
  rcases eq_or_lt_of_le hk with rfl | hlt
  · have h1 : (shiftTwist (RingEquiv.refl ℂ) 1 P).coeff P.natDegree = P.leadingCoeff := by
      have := shiftTwist_leadingCoeff (RingEquiv.refl ℂ) 1 P
      rw [Polynomial.leadingCoeff, shiftTwist_natDegree] at this
      simpa using this
    rw [h1]
    exact sub_self _
  · have h2 : (shiftTwist (RingEquiv.refl ℂ) 1 P).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [shiftTwist_natDegree]; exact hlt)
    rw [h2, Polynomial.coeff_eq_zero_of_natDegree_lt hlt, sub_zero]

/-- At the subleading degree the forward difference records `deg * leadingCoeff`. -/
theorem fwdDiff_coeff_sub_one {P : ℂ[X]} (hP : 0 < P.natDegree) :
    (fwdDiff P).coeff (P.natDegree - 1) = (P.natDegree : ℂ) * P.leadingCoeff := by
  rw [fwdDiff_eq_shiftTwist, Polynomial.coeff_sub,
    shiftTwist_coeff_sub_one (sigma := RingEquiv.refl ℂ) (c := (1 : ℂ)) (P := P) rfl hP]
  simp only [RingEquiv.refl_apply, mul_one]
  rw [Polynomial.leadingCoeff]
  ring

/-- The forward difference of a nonconstant polynomial has degree one less. -/
theorem natDegree_fwdDiff {P : ℂ[X]} (hP : 0 < P.natDegree) :
    (fwdDiff P).natDegree = P.natDegree - 1 := by
  have hne : (fwdDiff P).coeff (P.natDegree - 1) ≠ 0 := by
    rw [fwdDiff_coeff_sub_one hP]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      (Polynomial.leadingCoeff_ne_zero.mpr (fun h => by simp [h] at hP))
  refine le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_)
    (Polynomial.le_natDegree_of_ne_zero hne)
  intro k hk
  exact fwdDiff_coeff_of_natDegree_le P (by omega)

theorem leadingCoeff_fwdDiff {P : ℂ[X]} (hP : 0 < P.natDegree) :
    (fwdDiff P).leadingCoeff = (P.natDegree : ℂ) * P.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_fwdDiff hP, fwdDiff_coeff_sub_one hP]

/-- **Iterated forward differences of a polynomial reach a constant.**  Applying `fwdDiff` exactly
`deg P` times yields `(deg P)! * leadingCoeff P`. -/
theorem fwdDiff_iterate_natDegree (d : ℕ) :
    ∀ P : ℂ[X], P.natDegree = d →
      fwdDiff^[d] P = Polynomial.C ((d.factorial : ℂ) * P.leadingCoeff) := by
  induction d with
  | zero =>
      intro P hP
      simp only [Function.iterate_zero, id_eq, Nat.factorial_zero, Nat.cast_one, one_mul]
      rw [Polynomial.leadingCoeff, hP]
      exact Polynomial.eq_C_of_natDegree_eq_zero hP
  | succ d ih =>
      intro P hP
      have hpos : 0 < P.natDegree := by omega
      have hdeg : (fwdDiff P).natDegree = d := by rw [natDegree_fwdDiff hpos, hP]; omega
      rw [Function.iterate_succ_apply, ih _ hdeg, leadingCoeff_fwdDiff hpos, hP]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      ring

/-- Forward differencing preserves decay of the values along the natural numbers. -/
theorem tendsto_fwdDiff_of_tendsto {P : ℂ[X]}
    (h : Tendsto (fun n : ℕ => P.eval (n : ℂ)) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (fwdDiff P).eval (n : ℂ)) atTop (nhds 0) := by
  have hshift : Tendsto (fun n : ℕ => P.eval ((n : ℂ) + 1)) atTop (nhds 0) := by
    have hcomp : Tendsto (fun n : ℕ => P.eval (((n + 1 : ℕ) : ℂ))) atTop (nhds 0) :=
      h.comp (Filter.tendsto_add_atTop_nat 1)
    refine hcomp.congr fun n => ?_
    push_cast
    ring_nf
  have := hshift.sub h
  simpa using this

/-- **Polynomial decay principle.**  A polynomial whose values along the natural numbers tend to
zero is the zero polynomial. -/
theorem eq_zero_of_tendsto_eval_nat {P : ℂ[X]}
    (h : Tendsto (fun n : ℕ => P.eval (n : ℂ)) atTop (nhds 0)) :
    P = 0 := by
  classical
  by_contra hne
  set d : ℕ := P.natDegree with hd
  -- decay survives `d` forward differences
  have hiter : ∀ k : ℕ, Tendsto (fun n : ℕ => (fwdDiff^[k] P).eval (n : ℂ)) atTop (nhds 0) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ihk =>
        have := tendsto_fwdDiff_of_tendsto ihk
        refine this.congr fun n => ?_
        rw [Function.iterate_succ_apply']
  have hconst := hiter d
  rw [fwdDiff_iterate_natDegree d P hd.symm] at hconst
  simp only [Polynomial.eval_C] at hconst
  have hzero : (d.factorial : ℂ) * P.leadingCoeff = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  have hfac : (d.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  exact (Polynomial.leadingCoeff_ne_zero.mpr hne)
    ((mul_eq_zero.mp hzero).resolve_left hfac)

/-- A crude polynomial growth bound: values are controlled by `max 1 ‖z‖ ^ deg`. -/
theorem norm_eval_le_pow (P : ℂ[X]) (z : ℂ) :
    ‖P.eval z‖ ≤ (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * max 1 ‖z‖ ^ P.natDegree := by
  have hM : (1 : ℝ) ≤ max 1 ‖z‖ := le_max_left _ _
  have hMz : ‖z‖ ≤ max 1 ‖z‖ := le_max_right _ _
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖z‖ ^ i ≤ (max 1 ‖z‖) ^ i := pow_le_pow_left₀ (norm_nonneg _) hMz i
    _ ≤ (max 1 ‖z‖) ^ P.natDegree :=
        pow_le_pow_right₀ hM (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- **Geometric decay kills a polynomial.**  If the values of `P` along the natural numbers are
eventually dominated by `C * n ^ k * r ^ n` with `r < 1`, then `P = 0`. -/
theorem eq_zero_of_norm_eval_le_geometric {P : ℂ[X]} {C r : ℝ} {k : ℕ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ᶠ n : ℕ in atTop, ‖P.eval (n : ℂ)‖ ≤ C * (n : ℝ) ^ k * r ^ n) :
    P = 0 := by
  refine eq_zero_of_tendsto_eval_nat ?_
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hgeo : Tendsto (fun n : ℕ => (n : ℝ) ^ k * r ^ n) atTop (nhds 0) := by
    have : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k this).tendsto_atTop_zero
  have hCgeo : Tendsto (fun n : ℕ => C * ((n : ℝ) ^ k * r ^ n)) atTop (nhds 0) := by
    simpa using hgeo.const_mul C
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hCgeo
  filter_upwards [hbound] with n hn
  calc ‖P.eval (n : ℂ)‖ ≤ C * (n : ℝ) ^ k * r ^ n := hn
    _ = C * ((n : ℝ) ^ k * r ^ n) := by ring

end HTGeometry
