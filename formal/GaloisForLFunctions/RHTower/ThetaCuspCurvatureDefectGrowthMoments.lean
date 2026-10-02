import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthKernel
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectCumulants
/-!
# Complete ordinary-moment C5 defect growth sign

The exact seventh-order growth functional is positive on each literal
point-and-ray theta component. Countable moment transport proves strict
positivity for the complete ordinary spectral measure. The logarithmic
cumulant growth inequality, with its modular-center cancellation, remains
an independent target.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

def growthFunctional (q : ℝ) (m : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, growthCoefficient q (j+2)*m (j+2)

theorem growthFunctional_smul (q a : ℝ) (m : ℕ → ℝ) :
    growthFunctional q (fun j => a*m j) = a*growthFunctional q m := by
  unfold growthFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem growthFunctional_bare {q : ℝ} (hq : 0 < q) (d : ℝ) :
    growthFunctional q (bareMoment q d) = d/q^8*growthKernel q d := by
  unfold growthFunctional growthKernel
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num only [Nat.reduceAdd]
  unfold bareMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold momentNumeratorTwo momentNumeratorThree momentNumeratorFour
    momentNumeratorFive momentNumeratorSix momentNumeratorSeven
  field_simp [hq.ne']
  ring

theorem atom_growthFunctional_eq {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
    growthFunctional q (atomMoment n q) =
      Real.exp (-(3/2)*thetaCuspLikelihoodGap n)*Real.exp (-q*thetaCuspLikelihoodGap n)*
        (thetaCuspLikelihoodGap n+1)*thetaCuspLikelihoodGap n/q^8*
          growthKernel q (thetaCuspLikelihoodGap n) := by
  have heq : atomMoment n q = fun j =>
      (Real.exp (-(3/2)*thetaCuspLikelihoodGap n)*Real.exp (-q*thetaCuspLikelihoodGap n)*
        (thetaCuspLikelihoodGap n+1))*bareMoment q (thetaCuspLikelihoodGap n) j := by
    funext j
    exact atomMoment_eq_bare hn hq j
  rw [heq,growthFunctional_smul,growthFunctional_bare hq]
  ring

theorem atom_growthFunctional_pos {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 3/2 ≤ q) :
    0 < growthFunctional q (atomMoment n q) := by
  have hq0 : 0 < q := by linarith
  have hd : 3 ≤ thetaCuspLikelihoodGap n := by
    unfold thetaCuspLikelihoodGap
    have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [atom_growthFunctional_eq hn hq0]
  have hk := growthKernel_pos hq hd
  positivity

theorem hasSum_atomGrowth {q : ℝ} (hq : 0 < q) :
    HasSum (fun n : ℕ => growthFunctional q (atomMoment (n+2) q))
      (growthFunctional q (thetaCuspHigherLikelihoodSpectralMoment q)) := by
  unfold growthFunctional
  have h (j : ℕ) : HasSum
      (fun n : ℕ => growthCoefficient q (j+2)*atomMoment (n+2) q (j+2))
      (growthCoefficient q (j+2)*thetaCuspHigherLikelihoodSpectralMoment q (j+2)) :=
    (hasSum_atomMoment hq (j+2)).mul_left _
  exact hasSum_sum (fun j _ => h j)

theorem full_growthFunctional_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < growthFunctional q (thetaCuspHigherLikelihoodSpectralMoment q) := by
  have hs := hasSum_atomGrowth (show 0 < q by linarith)
  have hp (n : ℕ) : 0 < growthFunctional q (atomMoment (n+2) q) :=
    atom_growthFunctional_pos (by omega) hq
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos (fun n => (hp n).le) 0 (hp 0)
end
end RHTower.ThetaCuspDefect
