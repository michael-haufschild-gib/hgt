import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Moments
import GaloisForLFunctions.HTGeometry.FiniteKMSPurityNormalization

/-! # Signed scale in unlabelled finite Gibbs measurements -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration

open Finset Real Repeated
open _root_.HTGeometry (finiteGibbsStateWeight finiteGibbsPartition finiteGibbsPartition_pos
  finiteGibbsStateWeight_add_const sum_finiteGibbsStateWeight_eq_one)

variable {n : ℕ}

/-- Independent unit-temperature reference for a finite energy sample. -/
def law (x : Fin n → ℝ) := finiteGibbsStateWeight 1 x

/-- The sum of centered cubes, multiplied by n³ to avoid division. -/
def cubic (x : Fin n → ℝ) := ∑ i, ((n:ℝ)*x i-∑ j,x j)^3

def surprisalCubic (q : Fin n → ℝ) := cubic fun i => -log (q i)

theorem cubic_shift (x : Fin n → ℝ) (c : ℝ) : cubic (fun i => x i+c)=cubic x := by
  simp only [cubic,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  refine sum_congr rfl fun i _ => ?_
  ring

theorem cubic_scale (x : Fin n → ℝ) (c : ℝ) : cubic (fun i => c*x i)=c^3*cubic x := by
  unfold cubic
  rw [←Finset.mul_sum,Finset.mul_sum (s:=univ) (f:=fun i => ((n:ℝ)*x i-∑ j,x j)^3)]
  refine sum_congr rfl fun i _ => ?_
  ring

theorem cubic_gibbs [NeZero n] (x : Fin n → ℝ) : surprisalCubic (law x)=cubic x := by
  have eqn : (fun i => -log (law x i)) = fun i => x i+log (finiteGibbsPartition 1 x) := by
    funext i
    rw [law,finiteGibbsStateWeight,log_div (exp_ne_zero _) (finiteGibbsPartition_pos 1 x).ne',log_exp]
    ring
  rw [surprisalCubic,eqn,cubic_shift]

theorem cubic_matches {p q : Fin n → ℝ} (h : Matches p q) : surprisalCubic p=surprisalCubic q := by
  obtain ⟨e,he⟩ := h
  have total : (∑ i,-log (p i))=∑ j,-log (q j) :=
    Fintype.sum_equiv e _ _ fun i => congrArg (fun t : ℝ => -log t) (he i)
  unfold surprisalCubic cubic
  rw [total]
  exact Fintype.sum_equiv e _ _ fun i => by simp only [he i]

/-- Two Bernoulli coincidence readings determine the multiset of three
normalized Gibbs probabilities. Orders zero and one are fixed by normalization. -/
theorem copies_iff (x y : Fin 3 → ℝ) :
    (moment (law x) 2=moment (law y) 2 ∧ moment (law x) 3=moment (law y) 3) ↔
    Matches (law x) (law y) := by
  constructor
  · intro h
    apply (matches_iff_moments _ _).mpr
    intro j hj
    rw [Fintype.card_fin] at hj
    obtain rfl|rfl|rfl|rfl : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    · simp only [moment,pow_zero]
    · simp only [moment,pow_one,law,sum_finiteGibbsStateWeight_eq_one]
    · exact h.1
    · exact h.2
  · exact fun h => ⟨moment_congr h 2,moment_congr h 3⟩

/-- Two unlabeled modes cannot distinguish a Hamiltonian from its negative. -/
theorem two_reversed (x : Fin 2 → ℝ) : Matches (law (fun i => -x i)) (law x) := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  have eqn : (fun i => -x i)=(fun i => x (e i)+(-(x 0+x 1))) := by
    funext i
    fin_cases i <;> simp [e]
  have part : finiteGibbsPartition 1 (fun i => x (e i))=finiteGibbsPartition 1 x :=
    Fintype.sum_equiv e _ _ fun _ => rfl
  refine ⟨e,fun i => ?_⟩
  rw [eqn,law,finiteGibbsStateWeight_add_const,law,finiteGibbsStateWeight,finiteGibbsStateWeight,part]

#print axioms cubic_gibbs
#print axioms cubic_matches
#print axioms copies_iff
#print axioms two_reversed

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration
