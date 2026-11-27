import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.UnitDirections

/-! # The unique reciprocal candidate in an unweighted shell triangle -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real Set

private def balance (E F x : ℝ) := exp (-x*E)+exp (-x*F)

private theorem balance_strict {E F : ℝ} (e : 0<E) (f : 0<F) : StrictAnti (balance E F) := by
  intro x y lt
  exact add_lt_add (exp_lt_exp.mpr (mul_lt_mul_of_pos_right (neg_lt_neg lt) e))
    (exp_lt_exp.mpr (mul_lt_mul_of_pos_right (neg_lt_neg lt) f))

private theorem balance_root {E F : ℝ} (e : 0<E) (ef : E<F) :
    ∃ w : ℝ, 0<w ∧ ∀ v, balance E F v=1 ↔ v=w := by
  let T := log 2/E
  have l : 0<log 2 := log_pos one_lt_two
  have p : 0<T := div_pos l e
  have first : exp (-T*E)=(2 : ℝ)⁻¹ := by rw [neg_mul,show T*E=log 2 from div_mul_cancel₀ _ e.ne',exp_neg,exp_log zero_lt_two]
  have last : balance E F T<1 := by
    have lt := exp_lt_exp.mpr (mul_lt_mul_of_neg_left ef (neg_lt_zero.mpr p))
    rw [first] at lt
    unfold balance
    rw [first]
    linarith only [lt]
  have start : 1<balance E F 0 := by simp only [balance,neg_zero,zero_mul,exp_zero]; exact lt_add_of_pos_right _ zero_lt_one
  have cont : Continuous (balance E F) := by unfold balance; fun_prop
  obtain ⟨w,range,eq⟩ := intermediate_value_Icc' p.le cont.continuousOn
    (show (1 : ℝ) ∈ Icc (balance E F T) (balance E F 0) from ⟨last.le,start.le⟩)
  have pos : 0<w := range.1.lt_of_ne (by intro z; rw [← z] at eq; exact start.ne eq.symm)
  exact ⟨w,pos,fun v => by rw [← eq,(balance_strict e (e.trans ef)).injective.eq_iff]⟩

private theorem forward_balance (a b c : ℕ+) (v : ℝ) :
    balance (energy c-energy b) (energy c-energy a) v=1 ↔
      shellPower v a+shellPower v b=shellPower v c := by
  have expRatio (n : ℕ+) : exp (-v*(energy c-energy n))=relativePower v n c := by
    rw [relativePower_exp]; congr 1; ring
  rw [balance,expRatio,expRatio,relativePower,relativePower,← add_div,
    div_eq_one_iff_eq (shellPower_pos v c).ne',add_comm]

private theorem reverse_balance (a b c : ℕ+) (v : ℝ) :
    balance (energy b-energy a) (energy c-energy a) v=1 ↔
      shellPower (-v) b+shellPower (-v) c=shellPower (-v) a := by
  rw [balance,← relativePower_exp,← relativePower_exp,relativePower,relativePower,← add_div,
    div_eq_one_iff_eq (shellPower_pos (-v) a).ne']

private theorem reciprocal_at_source {a b c : ℕ+} {t : ℝ} (ht : 0<t)
    (rel : shellPower t a+shellPower t b=shellPower t c) :
    (shellPower (-t) b+shellPower (-t) c=shellPower (-t) a) ↔ b*b=a*c := by
  let A := shellPower t a
  let B := shellPower t b
  let C := shellPower t c
  have ap : 0<A := shellPower_pos _ _
  have bp : 0<B := shellPower_pos _ _
  have cp : 0<C := shellPower_pos _ _
  have neg (n : ℕ+) : shellPower (-t) n=(shellPower t n)⁻¹ := by rw [shellPower_exp,shellPower_exp,neg_mul,exp_neg]
  have mul (i j : ℕ+) : shellPower t (i*j)=shellPower t i*shellPower t j := by
    rw [shellPower_exp,energy_mul,mul_add,exp_add,← shellPower_exp,← shellPower_exp]
  have inj : Function.Injective (shellPower t) := by
    intro i j eq
    rw [shellPower_exp,shellPower_exp,exp_injective.eq_iff,mul_right_inj' ht.ne'] at eq
    have h := congrArg exp eq
    simp only [energy,exp_log (Nat.cast_pos.mpr i.pos),exp_log (Nat.cast_pos.mpr j.pos)] at h
    exact PNat.coe_injective (Nat.cast_injective (R := ℝ) h)
  rw [neg,neg,neg,← inj.eq_iff,mul,mul]
  change (B⁻¹+C⁻¹=A⁻¹) ↔ B*B=A*C
  have eq : A+B=C := rel
  constructor
  · intro h
    field_simp [ap.ne',bp.ne',cp.ne'] at h
    nlinarith only [h,congrArg (B*·) eq]
  · intro h
    field_simp [ap.ne',bp.ne',cp.ne']
    nlinarith only [h,congrArg (B*·) eq]

/-- Outside the forward and reciprocal readings both specified shell ratios
are algebraic. The two candidates coincide precisely in geometric progression. -/
theorem unit_triangle_candidates (a b c : ℕ+) (ab : energy a<energy b) (bc : energy b<energy c)
    {t : ℝ} (ht : 0<t) (rel : shellPower t a+shellPower t b=shellPower t c) :
    ∃ w : ℝ, 0<w ∧ (∀ v, shellPower (-v) b+shellPower (-v) c=shellPower (-v) a ↔ v=w) ∧
      (t=w ↔ b*b=a*c) ∧ ∀ u ∈ accumulated t,
        u=t ∨ u=w ∨ algebraicPair (delta a c) (delta b c) u := by
  obtain ⟨w,wp,test⟩ := balance_root (sub_pos.mpr ab) (sub_lt_sub_right bc (energy a))
  have reverse (v : ℝ) := (reverse_balance a b c v).symm.trans (test v)
  have strict := balance_strict (sub_pos.mpr bc) (sub_pos.mpr (ab.trans bc))
  have source := (forward_balance a b c t).mpr rel
  refine ⟨w,wp,reverse,(reverse t).symm.trans (reciprocal_at_source ht rel),?_⟩
  rintro u ⟨hp,m,hm,force⟩
  have up {d e : ℕ+} (de : energy d<energy e) : shellPower u d<shellPower u e := by
    rw [shellPower_exp,shellPower_exp]; exact exp_lt_exp.mpr (mul_lt_mul_of_pos_left de hp)
  have down {d e : ℕ+} (de : energy d<energy e) : shellPower (-u) e<shellPower (-u) d := by
    rw [shellPower_exp,shellPower_exp]; exact exp_lt_exp.mpr (mul_lt_mul_of_neg_left de (neg_lt_zero.mpr hp))
  rcases (scaled_forcing_iff ht hp hm).mp force with plus | minus
  · rcases unit_signed_alternative hm rel plus with (h | h | h) | alg
    · exact Or.inl (strict.injective (((forward_balance a b c u).mpr h).trans source.symm))
    · exfalso; linarith only [h,up ab,shellPower_pos u c]
    · exfalso; linarith only [h,up bc,shellPower_pos u a]
    · exact Or.inr (Or.inr alg)
  · rcases unit_signed_alternative hm rel minus with (h | h | h) | alg
    · exfalso; linarith only [h,down bc,shellPower_pos (-u) a]
    · exact Or.inr (Or.inl ((reverse u).mp h))
    · exfalso; linarith only [h,down ab,shellPower_pos (-u) c]
    · exact Or.inr (Or.inr (algebraicPair_neg alg))

#print axioms unit_triangle_candidates

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
