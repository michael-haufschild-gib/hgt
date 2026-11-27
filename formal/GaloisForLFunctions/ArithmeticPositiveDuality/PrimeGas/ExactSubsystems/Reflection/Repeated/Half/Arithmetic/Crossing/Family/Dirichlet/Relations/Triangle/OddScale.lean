import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.UnitDirections
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Descent.GapInvariant

/-! # Odd dilations exclude the reciprocal nonalgebraic triangle reading -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real IntermediateField

private theorem odd_directions {x y : ℝ} {U V : ℂ} {m : ℕ} (odd : Odd m)
    (up : U^m=1) (vp : V^m=1) (eq : (x : ℂ)*U+(y : ℂ)*V=1) :
    x+y=1 ∨ IsAlgebraic ℚ x ∧ IsAlgebraic ℚ y := by
  have hm : 0 < m := odd.pos
  obtain ⟨p,q⟩ := triangle_equations hm up vp eq
  by_cases det : phaseDet U V=0
  · rw [det,mul_zero] at p q
    have one {z : ℂ} (power : z^m=1) (inv : z=z⁻¹) : z=1 := by
      have nz : z ≠ 0 := norm_pos_iff.mp (by rw [phase_norm hm power]; exact zero_lt_one)
      have square : z^2=1 := by
        calc z^2=z*z⁻¹ := by rw [sq,← inv]
             _=1 := mul_inv_cancel₀ nz
      rcases sq_eq_one_iff.mp square with same | neg
      · exact same
      · rw [neg,odd.neg_one_pow] at power
        norm_num at power
    rw [one up (sub_eq_zero.mp q.symm),one vp (sub_eq_zero.mp p.symm).symm,mul_one,mul_one,
      ← Complex.ofReal_add,← Complex.ofReal_one] at eq
    exact Or.inl (Complex.ofReal_injective eq)
  · let K := algebraicClosure ℚ ℂ
    have a : U ∈ K := mem_algebraicClosure_iff.mpr (torsion_algebraic ℚ hm up)
    have b : V ∈ K := mem_algebraicClosure_iff.mpr (torsion_algebraic ℚ hm vp)
    have d : phaseDet U V ∈ K := K.sub_mem (K.mul_mem a (K.inv_mem b)) (K.mul_mem (K.inv_mem a) b)
    have recover {s : ℝ} {z : ℂ} (mem : z ∈ K) (row : (s : ℂ)*phaseDet U V=z) : IsAlgebraic ℚ s := by
      apply (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective).mp
      change IsAlgebraic ℚ (s : ℂ)
      rw [(eq_div_iff det).mpr row]
      exact mem_algebraicClosure_iff.mp (K.div_mem mem d)
    exact Or.inr ⟨recover (K.sub_mem (K.inv_mem b) b) p,recover (K.sub_mem a (K.inv_mem a)) q⟩

/-- Any distinct reading forced at an odd scale has two specified
algebraic gap coordinates, even if the reciprocal balance is distinct. -/
theorem odd_triangle_forcing (a b c : ℕ+) (ab : energy a<energy b) (bc : energy b<energy c)
    {t u : ℝ} (ht : 0<t) (hu : 0<u) {m : ℕ} (odd : Odd m)
    (rel : shellPower t a+shellPower t b=shellPower t c) (forces : Forces (t*m) (u*m)) :
    u=t ∨ IsAlgebraic ℚ (relativePower u a c) ∧ IsAlgebraic ℚ (relativePower u b c) := by
  have hm : 0 < m := odd.pos
  let f (v : ℝ) := relativePower v a c+relativePower v b c
  have anti : StrictAnti f := by
    intro v w lt
    simp only [f,relativePower_exp]
    exact add_lt_add (exp_lt_exp.mpr (mul_lt_mul_of_neg_right lt (sub_neg.mpr (ab.trans bc))))
      (exp_lt_exp.mpr (mul_lt_mul_of_neg_right lt (sub_neg.mpr bc)))
  have source : f t=1 := by
    dsimp only [f,relativePower]
    rw [← add_div,rel,div_self (shellPower_pos t c).ne']
  have src : shellRelation 1 1 1 a b c t := by simpa only [shellRelation,Int.cast_one,one_mul] using rel
  have signed (v : ℝ) (s : TorsionSpecialization m t v) :
      v=t ∨ IsAlgebraic ℚ (relativePower v a c) ∧ IsAlgebraic ℚ (relativePower v b c) := by
    obtain ⟨U,V,up,vp,eq⟩ := twisted_relation hm one_ne_zero src s
    have cast (d : ℕ+) : gapExp (delta d c) v=(relativePower v d c : ℂ) := by rw [relativePower_exp]; rfl
    simp only [Int.cast_one,div_one,Rat.cast_one,one_mul,cast] at eq
    exact (odd_directions odd up vp eq).imp (fun h => anti.injective (h.trans source.symm)) id
  rcases (scaled_forcing_iff ht hu hm).mp forces with pos | neg
  · exact signed u pos
  · rcases signed (-u) neg with eq | alg
    · exfalso; linarith only [eq,ht,hu]
    · exact Or.inr (by simpa only [relativePower_exp,neg_mul,exp_neg,inv_inv] using And.intro alg.1.inv alg.2.inv)

/-- With a transcendental gap, a distinct mutually forcing reading can
never be forced from the source by an odd integer dilation. -/
theorem odd_triangle_mutual (a b c : ℕ+) (ab : energy a<energy b) (bc : energy b<energy c)
    {t u : ℝ} (ht : 0<t) (hu : 0<u) {m : ℕ} (odd : Odd m)
    (rel : shellPower t a+shellPower t b=shellPower t c) (forces : Forces (t*m) (u*m))
    (back : t ∈ accumulated u) :
    u=t ∨ IsAlgebraic ℚ (relativePower t a c) ∧ IsAlgebraic ℚ (relativePower t b c) :=
  (odd_triangle_forcing a b c ab bc ht hu odd rel forces).imp_right fun h =>
    ⟨gap_algebraic_transfer hu back a c h.1,gap_algebraic_transfer hu back b c h.2⟩

#print axioms odd_triangle_forcing
#print axioms odd_triangle_mutual

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
