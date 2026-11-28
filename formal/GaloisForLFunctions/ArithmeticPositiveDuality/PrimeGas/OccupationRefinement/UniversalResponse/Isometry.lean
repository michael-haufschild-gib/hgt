import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.BornLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Isometry
import GaloisForLFunctions.RHTower.WeilProducerZetaQuotientBohrRecurrence

/-! # Universal norm-preserving response to quantum branch probabilities -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open Finset ModeCapacities CoassociativeSplitting

def routing (A : ℝ → ℂ) (u v : ℕ → ℝ) : Kernel := fun a b => A (branch u v a.val b.val)

def conserving (A : ℝ → ℂ) :=
  ∀ (u v : ℕ → ℝ), positive u → positive v → isometric (routing A u v)

theorem branch_mem {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (a b : ℕ+) :
    branch u v a.val b.val∈Shares := by
  refine ⟨branch_pos hu hv a b,?_⟩
  rw [←branch_sum hu hv (a*b)]
  have hd : (a.val,b.val)∈(a*b).val.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,(a*b).ne_zero⟩
  apply single_le_sum (f:=fun d : ℕ × ℕ => branch u v d.1 d.2) _ hd
  intro d mem
  let x := divisorsAntidiagonalFactors (a*b) ⟨d,mem⟩
  exact (branch_pos hu hv x.1 x.2).le

theorem conserving_of_born {A : ℝ → ℂ} (h : born A) : conserving A := by
  intro u v hu hv
  have re : (1/2:ℂ).re=1/2 := by norm_num
  have ref := (CoassociativeSplitting.isometric_iff _).mp ((conserving_iff _ hu hv).mpr re)
  apply (CoassociativeSplitting.isometric_iff _).mpr
  intro n
  refine (ref n).congr_fun fun x => ?_
  by_cases he : x.1*x.2=n
  · simp only [shell,if_pos he,routing,kernel_norm _ hu hv,re,
      show (2:ℝ)*(1/2)=1 by norm_num,Real.rpow_one,h _ (branch_mem hu hv x.1 x.2)]
  · simp only [shell,if_neg he]

/-- On a single elementary shell the two shares can be any prescribed
complementary positive probabilities. -/
theorem elementary_read {A : ℝ → ℂ} (h : conserving A) {x : ℝ} (hx : x∈Set.Ioo (0:ℝ) 1) :
    ‖A x‖^2+‖A (1-x)‖^2=1 := by
  let u := fun _ : ℕ => x
  let v := fun _ : ℕ => 1-x
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  have hleft : positive u := fun _ => hx.1
  have hright : positive v := fun _ => sub_pos.mpr hx.2
  have ray (j k : ℕ) : branch u v (p.val^j) (p.val^k)=binomial x (1-x) j k :=
    (branch_on_ray u v p j k).trans (prime_ray hx.1 (sub_pos.mpr hx.2) p j k)
  have total : x+(1-x)=1 := by ring
  have first : branch u v 1 2=1-x := by simpa [binomial,total,p] using ray 0 1
  have last : branch u v 2 1=x := by simpa [binomial,total,p] using ray 1 0
  have normalized := (CoassociativeSplitting.isometric_iff _).mp (h u v hleft hright)
  have eqn := (finite_shell (routing A u v) 2).unique (normalized 2)
  change (∑ d : (2:ℕ).divisorsAntidiagonal, ‖A (branch u v d.val.1 d.val.2)‖^2)=1 at eqn
  rw [univ_eq_attach,sum_attach _ (fun d : ℕ × ℕ => ‖A (branch u v d.1 d.2)‖^2),
    RHTower.divisorsAntidiagonal_of_prime Nat.prime_two] at eqn
  simpa [first,last,add_comm] using eqn

/-- Global conservation among sequential responses forces the Born rule
even without a separate boundedness or regularity condition. -/
theorem conserving_iff_born (A : ℝ → ℂ) (seq : sequential A) : conserving A ↔ born A := by
  refine ⟨fun con => ?_,conserving_of_born⟩
  have half := elementary_read con (x:=1/2) ⟨by norm_num,by norm_num⟩
  rw [show (1:ℝ)-1/2=1/2 by norm_num,←two_mul] at half
  have nz : A (1/2)≠0 := by intro eqn; norm_num [eqn] at half
  have eqn := seq 1 ⟨zero_lt_one,le_rfl⟩ (1/2) ⟨by norm_num,by norm_num⟩
  rw [one_mul] at eqn
  have unit : A 1=1 := mul_right_cancel₀ nz (eqn.symm.trans (one_mul _).symm)
  have bound : bounded A := by
    refine ⟨1,fun x hx => ?_⟩
    rcases hx.2.lt_or_eq with lt|rfl
    · have eqn := elementary_read con (x:=x) ⟨hx.1,lt⟩
      apply (sq_le_one_iff₀ (norm_nonneg _)).mp
      linarith only [eqn,sq_nonneg ‖A (1-x)‖]
    · rw [unit,norm_one]
  exact ((born_iff A).mp ⟨seq,bound,half⟩).2

#print axioms conserving_of_born
#print axioms elementary_read
#print axioms conserving_iff_born

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
