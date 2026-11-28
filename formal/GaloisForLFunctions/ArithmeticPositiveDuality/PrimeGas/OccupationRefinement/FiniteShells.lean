import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Channels

/-! # Finite Born sums on every integer shell -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement

open Finset CoassociativeSplitting

/-- The full pair-basis sum on an integer shell is its finite divisor sum. -/
theorem finite_shell (F : Kernel) (n : ℕ+) :
    HasSum (shell F n) (∑ d : n.val.divisorsAntidiagonal,
      ‖F (divisorsAntidiagonalFactors n d).1 (divisorsAntidiagonalFactors n d).2‖^2) := by
  let e : n.val.divisorsAntidiagonal ↪ ℕ+ × ℕ+ :=
    ⟨divisorsAntidiagonalFactors n,fun a b h => Subtype.ext
      (congrArg (fun x : ℕ+ × ℕ+ => (x.1.val,x.2.val)) h)⟩
  have inside (x : ℕ+ × ℕ+) (h : x.1*x.2=n) : x ∈ Set.range e :=
    ⟨⟨(x.1.val,x.2.val),Nat.mem_divisorsAntidiagonal.mpr ⟨congrArg PNat.val h,n.ne_zero⟩⟩,rfl⟩
  have outside (x : ℕ+ × ℕ+) (hx : x ∉ Set.range e) : shell F n x=0 :=
    if_neg fun h => hx (inside x h)
  apply (e.injective.hasSum_iff outside).mp
  have eqn : shell F n ∘ e = fun d => ‖F (e d).1 (e d).2‖^2 :=
    funext fun d => if_pos (show (e d).1*(e d).2=n from PNat.coe_injective (divisorsAntidiagonalFactors_eq d))
  rw [eqn]
  exact hasSum_fintype _

/-- The response exponent is twice the real part of the complex composition parameter. -/
def response (u v : ℝ) (n : ℕ+) (x : ℝ) :=
  ∑ d ∈ n.val.divisorsAntidiagonal, (probability u v d.1 d.2)^x

theorem shell_response (s : ℂ) {u v : ℝ} (hu : 0<u) (hv : 0<v) (n : ℕ+) :
    HasSum (shell (amplitude s u v) n) (response u v n (2*s.re)) := by
  have H := finite_shell (amplitude s u v) n
  simp only [norm_sq s hu hv] at H
  change HasSum _ (∑ d : n.val.divisorsAntidiagonal, (probability u v d.val.1 d.val.2)^(2*s.re)) at H
  rw [univ_eq_attach,Finset.sum_attach _ (fun d : ℕ × ℕ => (probability u v d.1 d.2)^(2*s.re))] at H
  exact H

private theorem prob_pos_on {u v : ℝ} (hu : 0<u) (hv : 0<v) {n : ℕ+} {d : ℕ × ℕ}
    (hd : d∈n.val.divisorsAntidiagonal) : 0<probability u v d.1 d.2 := by
  let x := divisorsAntidiagonalFactors n ⟨d,hd⟩
  exact probability_pos hu hv x.1 x.2

private theorem prob_lt_one {u v : ℝ} (hu : 0<u) (hv : 0<v) (n : ℕ+) (hn : 1<n.val)
    {d : ℕ × ℕ} (hd : d∈n.val.divisorsAntidiagonal) : probability u v d.1 d.2<1 := by
  have left : (1,n.val) ∈ n.val.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul _,n.ne_zero⟩
  have right : (n.val,1) ∈ n.val.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one _,n.ne_zero⟩
  have other : ∃ e ∈ n.val.divisorsAntidiagonal,e≠d := by
    by_cases eqn : (1,n.val)=d
    · exact ⟨_,right,fun h => hn.ne (congrArg Prod.fst (eqn.trans h.symm))⟩
    · exact ⟨_,left,eqn⟩
  obtain ⟨e,he,diff⟩ := other
  rw [←probability_sum hu hv n]
  exact single_lt_sum diff hd he (prob_pos_on hu hv he) (fun b hb _ => (prob_pos_on hu hv hb).le)

/-- Each nonvacuum shell separately measures the unique conservation exponent. -/
theorem response_strictAnti {u v : ℝ} (hu : 0<u) (hv : 0<v) (n : ℕ+) (hn : 1<n.val) :
    StrictAnti (response u v n) := by
  intro x y h
  apply sum_lt_sum_of_nonempty
  · exact ⟨(1,n.val),Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul _,n.ne_zero⟩⟩
  · intro d hd
    exact Real.strictAnti_rpow_of_base_lt_one (prob_pos_on hu hv hd) (prob_lt_one hu hv n hn hd) h

#print axioms finite_shell
#print axioms shell_response
#print axioms response_strictAnti

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement
