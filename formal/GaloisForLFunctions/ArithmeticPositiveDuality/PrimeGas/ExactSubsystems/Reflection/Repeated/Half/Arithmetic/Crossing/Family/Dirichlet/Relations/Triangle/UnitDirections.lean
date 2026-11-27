import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.PhaseRatios
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.ShellRelation

/-! # Algebraic gap coordinates away from real triangle directions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real IntermediateField

/-- A torsion triangle with positive lengths has a degenerate real balance
or two algebraic lengths, recovered by solving with the conjugate equation. -/
private theorem direction_alternative {x y : ℝ} {U V : ℂ} {m : ℕ}
    (hm : 0 < m) (hu : U^m=1) (hv : V^m=1) (xp : 0<x) (yp : 0<y)
    (eq : (x : ℂ)*U+(y : ℂ)*V=1) :
    (x+y=1 ∨ x=y+1 ∨ y=x+1) ∨ (IsAlgebraic ℚ (x : ℂ) ∧ IsAlgebraic ℚ (y : ℂ)) := by
  obtain ⟨p,q⟩ := triangle_equations hm hu hv eq
  by_cases det : phaseDet U V=0
  · left
    rw [det,mul_zero] at p q
    have sign {z : ℂ} (unit : z^m=1) (inv : z=z⁻¹) : z=1 ∨ z= -1 := by
      have nz : z ≠ 0 := norm_pos_iff.mp (by rw [phase_norm hm unit]; exact zero_lt_one)
      have prod : (z-1)*(z+1)=0 := by
        calc _ = z*z-1 := by ring
             _ = z*z⁻¹-1 := congrArg (fun w : ℂ => z*w-1) inv
             _ = 0 := by rw [mul_inv_cancel₀ nz,sub_self]
      exact (mul_eq_zero.mp prod).imp sub_eq_zero.mp (fun h => eq_neg_of_add_eq_zero_left h)
    rcases sign hu (sub_eq_zero.mp q.symm) with u | u <;>
      rcases sign hv (sub_eq_zero.mp p.symm).symm with v | v <;>
      rw [u,v] at eq <;> have real := congrArg Complex.re eq <;>
      simp only [mul_one,mul_neg,Complex.add_re,Complex.neg_re,Complex.ofReal_re,Complex.one_re] at real
    · exact Or.inl real
    · exact Or.inr (Or.inl (by linarith only [real]))
    · exact Or.inr (Or.inr (by linarith only [real]))
    · exfalso; linarith only [real,xp,yp]
  · right
    let K := algebraicClosure ℚ ℂ
    have a : U ∈ K := mem_algebraicClosure_iff.mpr (torsion_algebraic ℚ hm hu)
    have b : V ∈ K := mem_algebraicClosure_iff.mpr (torsion_algebraic ℚ hm hv)
    have d : phaseDet U V ∈ K := K.sub_mem (K.mul_mem a (K.inv_mem b)) (K.mul_mem (K.inv_mem a) b)
    rw [(eq_div_iff det).mpr p,(eq_div_iff det).mpr q]
    exact ⟨mem_algebraicClosure_iff.mp (K.div_mem (K.sub_mem (K.inv_mem b) b) d),
      mem_algebraicClosure_iff.mp (K.div_mem (K.sub_mem a (K.inv_mem a)) d)⟩

/-- A signed forced target of an unweighted relation has one length equal
to the sum of the other two, or both specified gap coordinates are algebraic. -/
theorem unit_signed_alternative {a b c : ℕ+} {t v : ℝ} {m : ℕ} (hm : 0 < m)
    (rel : shellPower t a+shellPower t b=shellPower t c) (spec : TorsionSpecialization m t v) :
    (shellPower v a+shellPower v b=shellPower v c ∨
      shellPower v b+shellPower v c=shellPower v a ∨ shellPower v a+shellPower v c=shellPower v b) ∨
      algebraicPair (delta a c) (delta b c) v := by
  have src : shellRelation 1 1 1 a b c t := by simpa only [shellRelation,Int.cast_one,one_mul] using rel
  obtain ⟨U,V,up,vp,eq⟩ := twisted_relation hm one_ne_zero src spec
  let x := relativePower v a c
  let y := relativePower v b c
  have cast (d : ℕ+) : (relativePower v d c : ℂ)=gapExp (delta d c) v := by rw [relativePower_exp]; rfl
  have clean : (x : ℂ)*U+(y : ℂ)*V=1 := by
    simpa only [x,y,cast,Int.cast_one,div_one,Rat.cast_one,one_mul] using eq
  have cp := shellPower_pos v c
  rcases direction_alternative hm up vp (div_pos (shellPower_pos v a) cp) (div_pos (shellPower_pos v b) cp) clean with h | alg
  · left
    change shellPower v a/shellPower v c+shellPower v b/shellPower v c=1 ∨
      shellPower v a/shellPower v c=shellPower v b/shellPower v c+1 ∨
      shellPower v b/shellPower v c=shellPower v a/shellPower v c+1 at h
    rcases h with h | h | h <;> field_simp [cp.ne'] at h
    · exact Or.inl h
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)
  · right
    unfold algebraicPair
    rw [← cast a,← cast b]
    exact alg

theorem algebraicPair_neg {E F v : ℝ} (h : algebraicPair E F (-v)) : algebraicPair E F v := by
  have neg (D : ℝ) : gapExp D v=(gapExp D (-v))⁻¹ := by
    simp only [gapExp,neg_mul,exp_neg,Complex.ofReal_inv,inv_inv]
  unfold algebraicPair
  rw [neg E,neg F]
  exact ⟨h.1.inv,h.2.inv⟩

#print axioms unit_signed_alternative
#print axioms algebraicPair_neg

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
