import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.WindowDifferences
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.LongMoebiusSecondMomentRigidity

/-!
# Newton reconstruction of the long Möbius second moment

At fixed arithmetic cutoff, Gregory–Newton interpolation reconstructs a long
window from its first short window and the binomial differences at that same
origin. Every higher row consists of signed Möbius pairs with a positive
power of the frequency chord. This gives an exact criterion with arbitrary
height-dependent mesh size.
-/

open Complex Finset MeasureTheory Filter
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

noncomputable section

private abbrev criticalPoly (X : ℕ) (t : ℝ) : ℂ :=
  RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X) (((1/2 : ℝ) : ℂ) + (t : ℂ)*I)

private theorem energy_continuous (X : ℕ) : Continuous fun t : ℝ => ‖criticalPoly X t‖^2 := by
  have h := RHTower.differentiable_edPoly moebiusMollifierCoeff
    (s := Finset.Icc 1 X) (fun _ hi => (Finset.mem_Icc.mp hi).1)
  exact (h.continuous.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).norm.pow 2

private theorem window_eq_moment (X : ℕ) (h t : ℝ) :
    twistedWindow moebiusMollifierCoeff moebiusMollifierCoeff (Finset.Icc 1 X) (1/2) 0 h t =
      ((∫ v in t..(t+h), ‖criticalPoly X v‖^2 : ℝ) : ℂ) := by
  unfold twistedWindow
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun v _ => ?_
  rw [show criticalPoly X v = cdpoly moebiusMollifierCoeff (Finset.Icc 1 X) (1/2) v from
    RHTower.edPoly_line _ (fun n hn => (Finset.mem_Icc.mp hn).1) _ _]
  simp [Complex.mul_conj']

/-- A Newton row expressed only with the original arithmetic weights, gaps and short window kernels. -/
def moebiusNewtonRow (X r : ℕ) (t h : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
    windowPairWeight moebiusMollifierCoeff moebiusMollifierCoeff (1/2) m n *
      (expInt (Real.log n - Real.log m) t h * windowChord (Real.log n - Real.log m) h ^ r)

/-- Binomial differences in the starting height, at the exact cutoff and with its signs. -/
theorem moebiusNewtonRow_eq_difference (X r : ℕ) (t h : ℝ) :
    moebiusNewtonRow X r t h = (fwdDiff h)^[r]
      (fun s : ℝ => ((∫ v in s..(s+h), ‖criticalPoly X v‖^2 : ℝ) : ℂ)) t := by
  simp_rw [← window_eq_moment]
  rw [twistedWindow_difference]
  simp [moebiusNewtonRow]

/-- The row is a signed binomial combination of measured short-window energies. -/
theorem moebiusNewtonRow_samples (X r : ℕ) (t h : ℝ) :
    moebiusNewtonRow X r t h = ∑ j ∈ range (r+1), ((-1 : ℤ)^(r-j) * r.choose j) •
      ((∫ v in (t+j • h)..(t+j • h+h), ‖criticalPoly X v‖^2 : ℝ) : ℂ) := by
  rw [moebiusNewtonRow_eq_difference, fwdDiff_iter_eq_sum_shift]

/-- Exact reconstruction on any arithmetic grid, including signed and zero steps. -/
theorem moebius_energy_newton (X N : ℕ) (t h : ℝ) :
    ((∫ v in t..(t+N • h), ‖criticalPoly X v‖^2 : ℝ) : ℂ) =
      ∑ k ∈ range N, (N.choose (k+1)) • moebiusNewtonRow X k t h := by
  let F : ℝ → ℂ := fun s => ((∫ v in t..s, ‖criticalPoly X v‖^2 : ℝ) : ℂ)
  have hinc : fwdDiff h F = fun s => ((∫ v in s..(s+h), ‖criticalPoly X v‖^2 : ℝ) : ℂ) := by
    funext s
    have htel := intervalIntegral.integral_add_adjacent_intervals
      ((energy_continuous X).intervalIntegrable (μ := volume) t s)
      ((energy_continuous X).intervalIntegrable (μ := volume) s (s+h))
    change ((_ : ℝ) : ℂ) - ((_ : ℝ) : ℂ) = _
    rw [← Complex.ofReal_sub]
    exact congrArg Complex.ofReal (by linarith only [htel])
  change F (t+N • h) = _
  rw [shift_eq_sum_fwdDiff_iter h F N t, sum_range_succ']
  have ht : F t = 0 := by simp [F]
  simp only [Function.iterate_zero, id_eq, ht, smul_zero, add_zero, zero_add]
  refine sum_congr rfl fun k _ => ?_
  rw [Function.iterate_succ_apply, hinc, moebiusNewtonRow_eq_difference]

/-- Reassembled energy at a prescribed number `N+1` of short windows. -/
def moebiusNewtonEnergy (X N : ℕ) (T : ℝ) : ℝ :=
  (∑ k ∈ range (N+1), (Nat.choose (N+1) (k+1)) •
    moebiusNewtonRow X k 1 ((T-1)/((N : ℝ)+1))).re

theorem moebiusNewtonEnergy_exact (X N : ℕ) (T : ℝ) :
    moebiusNewtonEnergy X N T = ∫ t in (1 : ℝ)..T, ‖criticalPoly X t‖^2 := by
  unfold moebiusNewtonEnergy
  rw [← moebius_energy_newton]
  have h : 1 + (N+1) • ((T-1)/((N : ℝ)+1)) = T := by
    rw [nsmul_eq_mul, Nat.cast_succ]
    field_simp
    ring
  rw [h, Complex.ofReal_re]

/-- Any height- and length-dependent mesh gives the same long-polynomial RH criterion. -/
theorem riemannHypothesis_iff_cofinal_moebius_newton (mesh : ℝ → ℝ → ℕ) :
    RiemannHypothesis ↔ ∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ →
      ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ T : ℝ in atTop,
        moebiusNewtonEnergy ⌊T^θ⌋₊ (mesh θ T) T ≤ C*T^K := by
  simpa only [moebiusNewtonEnergy_exact] using riemannHypothesis_iff_cofinal_pure_moebius_moment

#print axioms moebiusNewtonRow_samples
#print axioms moebius_energy_newton
#print axioms riemannHypothesis_iff_cofinal_moebius_newton

end

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
