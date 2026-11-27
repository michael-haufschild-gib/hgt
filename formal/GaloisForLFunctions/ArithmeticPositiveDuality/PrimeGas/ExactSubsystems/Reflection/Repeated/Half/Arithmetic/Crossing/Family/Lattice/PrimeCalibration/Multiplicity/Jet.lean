import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Grid

/-! # First-order reflection of a single normalized probability vector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Real Finset
open _root_.HTGeometry (finiteGibbsStateWeight)

variable {I : Type*} [Fintype I]

/-- Signed comparison at moment order v, recovered from one probability vector. -/
def lawDefect (P : I → ℝ) (v : ℝ) := oddTrace (centered (Observation.information P)) v

/-- The derivative at order one is itself a finite statistic of the same law. -/
theorem defect_derivative (P : I → ℝ) :
    let u := centered (Observation.information P)
    HasDerivAt (lawDefect P) (∑ i, u i*(exp (u i)+exp (-u i))) 1 := by
  dsimp only
  let u := centered (Observation.information P)
  have term (i : I) : HasDerivAt (fun v : ℝ => oddTerm v (u i))
      (u i*(exp (u i)+exp (-u i))) 1 := by
    have h : HasDerivAt (fun v : ℝ => v*u i) (u i) 1 := by
      simpa only [id_eq,one_mul] using (hasDerivAt_id (1 : ℝ)).mul_const (u i)
    have neg : HasDerivAt (fun v : ℝ => -v*u i) (-u i) 1 := by
      rw [show (fun v : ℝ => -v*u i)=-(fun v : ℝ => v*u i) by
        funext v; exact neg_mul v (u i)]
      exact h.neg
    have ep : HasDerivAt (fun v : ℝ => exp (v*u i)) (exp (u i)*u i) 1 := by
      simpa only [one_mul] using h.exp
    have en : HasDerivAt (fun v : ℝ => exp (-v*u i)) (exp (-u i)*(-u i)) 1 := by
      simpa only [neg_one_mul] using neg.exp
    rw [show u i*(exp (u i)+exp (-u i))=exp (u i)*u i-exp (-u i)*(-u i) by ring]
    exact ep.sub en
  exact HasDerivAt.fun_sum fun i _ => term i

theorem gibbs_defect (k : I → ℕ) (q : Nat.Primes) (d v : ℝ) :
    lawDefect (finiteGibbsStateWeight d (primeModes q k)) v=
      oddTrace (centered (levels k)) (v*(d*log q.val)) := by
  rw [lawDefect,funext (Observation.gibbs_information _ _),centered_affine,Sparse.mode_grid,centered_affine]
  apply sum_congr rfl
  intro i _
  simp only [oddTerm,neg_mul,mul_assoc]

/-- Restoring the common exponential factor turns the centered trace
into the signed difference of two occupation power sums. -/
theorem weighted_defect [Nonempty I] (k : I → ℕ) {c : ℕ}
    (align : 2*(∑ i, k i)=Fintype.card I*c) (bounded : ∀ i, k i≤c) (t : ℝ) :
    exp (t*(c : ℝ)/2)*oddTrace (centered (levels k)) t =
      (∑ i, (exp t)^k i)-(∑ i, (exp t)^(c-k i)) := by
  have realAlign : 2*(∑ i, (k i : ℝ))=(Fintype.card I : ℝ)*(c : ℝ) := by exact_mod_cast align
  have nz : (Fintype.card I : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have mean : meanEnergy (levels k)=(c : ℝ)/2 := by
    change (∑ i, (k i : ℝ))/(Fintype.card I : ℝ)=_
    apply (div_eq_iff nz).mpr
    linarith only [realAlign]
  rw [oddTrace,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  simp only [oddTerm,centered,mean,levels,mul_sub,←exp_add,←exp_nat_mul,Nat.cast_sub (bounded i)]
  congr 1 <;> congr 1 <;> ring

/-- The signed response polynomial of the extremal preparation. -/
def profile (b x : ℝ) := (b*x-1)*(x-b)*(1+x)*(1-x^4)*(1-x^8)*(1-x^12)

private theorem simple_factor {g h : ℝ → ℝ} {a : ℝ} (dg : HasDerivAt g a 1)
    (dh : DifferentiableAt ℝ h 1) (root : g 1=0) (slope : a≠0) (unit : h 1≠0) :
    ¬HasDerivAt (fun v => g v*h v) 0 1 := by
  intro flat
  have eq := (dg.mul dh.hasDerivAt).unique flat
  rw [root,zero_mul,add_zero] at eq
  exact mul_ne_zero slope unit eq

/-- Away from zero damping all real zeros of the response are simple,
on either side of the critical line. -/
theorem simple_profile {a b : ℝ} (ha : a≠0) (hb : 1<b)
    (root : profile b (exp a)=0) :
    ¬HasDerivAt (fun v : ℝ => profile b (exp (v*a))) 0 1 := by
  let x (v : ℝ) := exp (v*a)
  have dx : HasDerivAt x (exp a*a) 1 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (1 : ℝ)).mul_const a).exp
  have dxnz : exp a*a≠0 := mul_ne_zero (exp_ne_zero a) ha
  let u (v : ℝ) := b*x v-1
  let w (v : ℝ) := x v-b
  let h (v : ℝ) := (1+x v)*(1-x v^4)*(1-x v^8)*(1-x v^12)
  have xone : x 1=exp a := by simp only [x,one_mul]
  have nz (j : ℕ) (hj : j≠0) : 1-x 1^j≠0 := by
    rw [xone,←exp_nat_mul]
    exact sub_ne_zero.mpr fun eq => mul_ne_zero (Nat.cast_ne_zero.mpr hj) ha ((exp_eq_one_iff _).mp eq.symm)
  have hn : h 1≠0 := by
    have first : 1+x 1≠0 := (add_pos zero_lt_one (exp_pos _)).ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero first (nz 4 (by omega))) (nz 8 (by omega))) (nz 12 (by omega))
  have du : HasDerivAt u (b*(exp a*a)) 1 := (dx.const_mul b).sub_const 1
  have dw : HasDerivAt w (exp a*a) 1 := dx.sub_const b
  have dh : DifferentiableAt ℝ h 1 := by dsimp only [h,x]; fun_prop
  have product : (fun v => profile b (exp (v*a)))=fun v => (u v*w v)*h v := by
    funext v; dsimp only [profile,u,w,h,x]; ring
  have atOne : (u 1*w 1)*h 1=0 := by
    rw [←congrFun product 1,one_mul,root]
  have separate : ¬(u 1=0 ∧ w 1=0) := by
    rintro ⟨gu,gw⟩
    change x 1-b=0 at gw
    change b*x 1-1=0 at gu
    rw [sub_eq_zero.mp gw] at gu
    have lt := mul_lt_mul_of_pos_left hb (zero_lt_one.trans hb)
    rw [mul_one] at lt
    linarith only [hb,lt,gu]
  rcases mul_eq_zero.mp ((mul_eq_zero.mp atOne).resolve_right hn) with gu | gw
  · have wu : w 1≠0 := fun hw => separate ⟨gu,hw⟩
    have eq : (fun v => (u v*w v)*h v)=fun v => u v*(w v*h v) := by funext v; ring
    rw [product,eq]
    exact simple_factor du (dw.differentiableAt.mul dh) gu
      (mul_ne_zero (zero_lt_one.trans hb).ne' dxnz) (mul_ne_zero wu hn)
  · have uu : u 1≠0 := fun hu => separate ⟨hu,gw⟩
    have eq : (fun v => (u v*w v)*h v)=fun v => w v*(u v*h v) := by funext v; ring
    rw [product,eq]
    exact simple_factor dw (du.differentiableAt.mul dh) gw dxnz (mul_ne_zero uu hn)

#print axioms gibbs_defect
#print axioms weighted_defect
#print axioms defect_derivative
#print axioms simple_profile

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
