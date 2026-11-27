import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.Stabilization

/-! # The mixed resonance of shells two, three and seven -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real Set MvPolynomial

private theorem singleton_subdivision {t : ℝ} (ht : 0<t) (P : PolynomialRing)
    (root : ∀ v, value v P=0 ↔ v=t) (d : ℕ) (hd : 0<d) : Attainable {t/d} := by
  have dp := (Nat.cast_pos.mpr hd : 0<(d : ℝ))
  have tp := div_pos ht dp
  have eval (v : ℝ) : value v (expand d P)=value (v*d) P := by
    change aeval (coordinates v) (expand d P)=aeval (coordinates (v*d)) P
    rw [aeval_expand]
    have powers : (coordinates v)^d=coordinates (v*d) := funext fun p =>
      (rpow_mul_natCast (Nat.cast_nonneg p.val) v d).symm
    rw [powers]
  have unique (v : ℝ) : value v (expand d P)=0 ↔ v=t/d := by
    rw [eval,root,eq_div_iff dp.ne']
  apply (attainable_iff _).mpr
  have nz : expand d P ≠ 0 := fun h => tp.ne ((unique 0).mp (by rw [h,map_zero]))
  refine ⟨_,nz,Set.ext fun s => ?_⟩
  change s=t/d ↔ 0<s ∧ (value s (expand d P)=0 ∨ value (-s) (expand d P)=0)
  rw [unique,unique]
  constructor
  · rintro rfl
    exact ⟨tp,Or.inl rfl⟩
  · rintro ⟨hs,eq | eq⟩
    · exact eq
    · linarith only [hs,tp,eq]

/-- The genuine mixed relation 2^t+3^t=7^t has a unique real solution in
(0,1). At every reciprocal integer scale it is an exact isolated blind
reading; across all rational dilations its unavoidable companions are finite. -/
theorem two_three_seven :
    ∃ t : ℝ, 0<t ∧ t<1 ∧
      (∀ v : ℝ, shellPower v 2+shellPower v 3=shellPower v 7 ↔ v=t) ∧
      (∀ d : ℕ, 0<d → Attainable {t/d}) ∧ (accumulated t).Finite := by
  let f (s : ℝ) := relativePower s 2 7+relativePower s 3 7
  have log_lt (a b : ℕ+) (h : a.val<b.val) : energy a<energy b :=
    log_lt_log (Nat.cast_pos.mpr a.pos) (Nat.cast_lt.mpr h)
  have e23 : energy 2<energy 3 := log_lt 2 3 (by norm_num)
  have e37 : energy 3<energy 7 := log_lt 3 7 (by norm_num)
  have asExp (s : ℝ) : f s=exp (s*(energy 2-energy 7))+exp (s*(energy 3-energy 7)) := by
    simp only [f,relativePower_exp]
  have anti : StrictAnti f := by
    intro x y lt
    rw [asExp,asExp]
    exact add_lt_add (exp_lt_exp.mpr (mul_lt_mul_of_neg_right lt (sub_neg.mpr (e23.trans e37))))
      (exp_lt_exp.mpr (mul_lt_mul_of_neg_right lt (sub_neg.mpr e37)))
  have cont : Continuous f := by
    rw [show f=(fun s => exp (s*(energy 2-energy 7))+exp (s*(energy 3-energy 7))) from funext asExp]
    fun_prop
  have left : 1<f 0 := by rw [asExp]; norm_num
  have right : f 1<1 := by norm_num [f,relativePower,shellPower]
  obtain ⟨t,interval,eq⟩ := intermediate_value_Icc' (zero_le_one : (0 : ℝ)≤1) cont.continuousOn
    (show (1 : ℝ) ∈ Set.Icc (f 1) (f 0) from ⟨right.le,left.le⟩)
  have ht : 0<t := interval.1.lt_of_ne (by intro h; rw [← h] at eq; exact left.ne eq.symm)
  have upper : t<1 := interval.2.lt_of_ne (by intro h; rw [h] at eq; exact right.ne eq)
  have root (v : ℝ) : shellPower v 2+shellPower v 3=shellPower v 7 ↔ v=t := by
    have test : f v=1 ↔ shellPower v 2+shellPower v 3=shellPower v 7 := by
      change shellPower v 2/shellPower v 7+shellPower v 3/shellPower v 7=1 ↔ _
      rw [← add_div,div_eq_one_iff_eq (shellPower_pos v 7).ne']
    rw [← test,← eq,anti.injective.eq_iff]
  let P : PolynomialRing := atom 2+atom 3-atom 7
  have read (v : ℝ) : value v P=0 ↔ v=t := by
    simp only [P,map_sub,map_add,value_atom,← shellPower_exp,sub_eq_zero,root]
  have rel : shellRelation (-1) 1 1 3 7 2 t := by
    simp only [shellRelation,Int.cast_neg,Int.cast_one,neg_mul,one_mul]
    linarith only [(root t).mpr rfl]
  exact ⟨t,ht,upper,root,singleton_subdivision ht P read,
    three_shell_finite 3 7 2 e23 (e23.trans e37) e37.ne (-1) 1 1 (by norm_num)
      one_ne_zero one_ne_zero ht rel⟩

#print axioms two_three_seven

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
