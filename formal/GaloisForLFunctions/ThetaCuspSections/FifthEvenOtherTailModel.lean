import GaloisForLFunctions.ThetaCuspSections.FifthEvenOtherTailCoefficients
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTailRateMoments
/-!
# Cubic-reserve payments for the remaining unequal theta pairs

For each pair, clear the gamma and exponential denominators and expand
at radial scale three. The finite coefficient certificates and the positive
binomial tail give positivity of both endpoint matrices on the full ray.
Convexity covers the actual gamma mass and exponential weight.
-/
noncomputable section
open Matrix
namespace GaloisForLFunctions.ThetaCuspSections.FifthOtherTail
open FifthAtomTail FifthLeadingPair FifthRateTail

/-- Every binomial coefficient of the cleared cubic reserve is positive. -/
theorem reserve_coefficient_pos (N d : ℕ) (hd : d≤N+1) :
 0<(12*(Nat.choose (N+1) d:ℝ)-(Nat.choose N d:ℝ))/9216 := by
 have hp : (0:ℝ)<(Nat.choose (N+1) d:ℝ) := by
  exact_mod_cast Nat.choose_pos hd
 have hm : (Nat.choose N d:ℝ)≤(Nat.choose (N+1) d:ℝ) := by
  exact_mod_cast Nat.choose_le_succ N d
 linarith only [hp,hm]

/-- One eighth of the cubic gamma reserve is strict from scale three. -/
theorem cubic_eighth_pos {q : ℝ} (hq : 3≤q) :
 0<3/(256*q^2)-3/(1024*q^3) := by
 have hq0 : 0<q := by linarith only [hq]
 have h4 : 0<4*q-1 := by linarith only [hq]
 have he : 3/(256*q^2)-3/(1024*q^3)=3*(4*q-1)/(1024*q^3) := by
  field_simp [hq0.ne']
  ring
 rw [he]
 exact div_pos (mul_pos (by norm_num) h4) (mul_pos (by norm_num) (pow_pos hq0 3))

namespace p14

/-- The gamma endpoint moments after multiplication by the radial scale cubed. -/
def crossScaled (upper : Bool) : ℕ → ℝ → ℝ
 | 0, q => q^3/17+3*q^2/(2*(17:ℝ)^2)+3*q/(4*(17:ℝ)^3)-
    (if upper then 0 else 3/(8*(17:ℝ)^4))
 | n+1, q => q^(n+4)/17+((2*n+5:ℕ):ℝ)/(2*17)*crossScaled upper n q

/-- The signed moment comparison after clearing all positive radial powers. -/
def clearedMoment (upper : Bool) (q : ℝ) (k : ℕ) : ℝ :=
 (3*q^46/256-3*q^45/1024)*linearMoment (fun n => g n 0 1) k+
  (2*16*3^45/(20:ℝ)^15)*pairLinear (fun n => crossScaled upper n q) k

/-- Hankel matrix of the cleared pair comparison. -/
def clearedMatrix (upper : Bool) (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 fun i j => clearedMoment upper q (i.val+j.val)

theorem powerCoeff_expand (n : ℕ) (hn : n≤46) (y : ℝ) :
 (3*(1+y))^n=∑ d ∈ Finset.range 47, powerCoeff n d*y^d := by
 calc
  _ = ∑ d ∈ Finset.range (n+1), powerCoeff n d*y^d := by
   rw [mul_pow,add_comm (1:ℝ),add_pow,Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro d hd
   simp only [powerCoeff,one_pow,mul_one]
   ring
  _ = _ := by
   apply Finset.sum_subset (Finset.range_mono (by omega))
   intro d hd hdn
   have hnd : n<d := by simp only [Finset.mem_range] at hd hdn; omega
   simp only [powerCoeff,Nat.choose_eq_zero_of_lt hnd,Nat.cast_zero,zero_mul]

private def coeffEval (f : ℕ → ℝ) (y : ℝ) : ℝ :=
 ∑ d ∈ Finset.range 47, f d*y^d

private theorem coeffEval_add (f h : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => f d+h d) y=coeffEval f y+coeffEval h y := by
 simp only [coeffEval,add_mul,Finset.sum_add_distrib]

private theorem coeffEval_sub (f h : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => f d-h d) y=coeffEval f y-coeffEval h y := by
 simp only [coeffEval,sub_mul,Finset.sum_sub_distrib]

private theorem coeffEval_smul (c : ℝ) (f : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => c*f d) y=c*coeffEval f y := by
 simp only [coeffEval,mul_assoc,Finset.mul_sum]

private theorem coeffEval_one (y : ℝ) :
 coeffEval (fun d => if d=0 then 1 else 0) y=1 := by
 simp [coeffEval]

private theorem coeffEval_power (n : ℕ) (hn : n≤46) (y : ℝ) :
 coeffEval (powerCoeff n) y=(3*(1+y))^n := (powerCoeff_expand n hn y).symm

private theorem crossCoeff_zero (upper : Bool) :
 crossCoeff 17 upper 0=fun d =>
  ((1/17)*powerCoeff 3 d+(3/(2*(17:ℝ)^2))*powerCoeff 2 d+(3/(4*(17:ℝ)^3))*powerCoeff 1 d)-
   (if upper then 0 else 3/(8*(17:ℝ)^4))*(if d=0 then 1 else 0) := by
 funext d
 simp only [crossCoeff]
 split_ifs <;> ring

private theorem crossCoeff_succ (upper : Bool) (n : ℕ) :
 crossCoeff 17 upper (n+1)=fun d => (1/17)*powerCoeff (n+4) d+
  (((2*n+5:ℕ):ℝ)/(2*17))*crossCoeff 17 upper n d := by
 funext d
 simp only [crossCoeff]
 ring

/-- Every scaled gamma endpoint is the binomial expansion of its radial polynomial. -/
theorem crossCoeff_expand (upper : Bool) (n : ℕ) (hn : n≤18) (y : ℝ) :
 crossScaled upper n (3*(1+y))=coeffEval (crossCoeff 17 upper n) y := by
 revert hn
 induction n with
 | zero =>
   intro hn
   rw [crossCoeff_zero,coeffEval_sub,coeffEval_add,coeffEval_add,
    coeffEval_smul,coeffEval_smul,coeffEval_smul,coeffEval_smul,
    coeffEval_power 3 (by norm_num),coeffEval_power 2 (by norm_num),
    coeffEval_power 1 (by norm_num),coeffEval_one]
   simp only [crossScaled]
   ring
 | succ n ih =>
   intro hn
   rw [crossCoeff_succ,coeffEval_add,coeffEval_smul,coeffEval_smul,
    coeffEval_power (n+4) (by omega),← ih (by omega)]
   simp only [crossScaled]
   ring

/-- Scaled pair moments have degree at most three above their power index. -/
theorem crossCoeff_eq_zero (upper : Bool) (n d : ℕ) (hd : n+3<d) :
 crossCoeff 17 upper n d=0 := by
 revert hd
 induction n with
 | zero =>
   intro hd
   have h3 : 3<d := by omega
   have h2 : 2<d := by omega
   have h1 : 1<d := by omega
   have h0 : d≠0 := by omega
   simp only [crossCoeff,powerCoeff,Nat.choose_eq_zero_of_lt h3,
    Nat.choose_eq_zero_of_lt h2,Nat.choose_eq_zero_of_lt h1,
    Nat.cast_zero,zero_mul,zero_div,mul_zero,add_zero,h0,ite_false]
   cases upper <;> norm_num
 | succ n ih =>
   intro hd
   rw [crossCoeff,ih (by omega)]
   simp only [powerCoeff,Nat.choose_eq_zero_of_lt (show n+4<d by omega),
    Nat.cast_zero,zero_mul,zero_div,mul_zero,add_zero]

private theorem pairLinear_coeffEval (upper : Bool) (y : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => coeffEval (crossCoeff 17 upper n) y) k=
  coeffEval (fun d => pairLinear (fun n => crossCoeff 17 upper n d) k) y := by
 rw [pairLinear_sum k hk]
 dsimp only [coeffEval]
 simp only [Finset.mul_sum]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro d hd
 rw [pairLinear_sum k hk,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro n hn
 ring

/-- Every coefficient above degree twenty-one contains only the positive mass reserve. -/
theorem pairLinear_crossCoeff_zero (upper : Bool) (d k : ℕ) (hd : 22≤d) (hk : k≤8) :
 pairLinear (fun n => crossCoeff 17 upper n d) k=0 := by
 rw [pairLinear_sum k hk]
 apply Finset.sum_eq_zero
 intro n hn
 have hn18 : n≤18 := by
  have hn19 := Finset.mem_range.mp hn
  omega
 rw [crossCoeff_eq_zero upper n d (by omega),mul_zero]

private theorem coefficientMatrix_endpoints_agree (d : ℕ) (hd : d≠0) :
 coefficientMatrix false d=coefficientMatrix true d := by
 ext i j
 dsimp only [coefficientMatrix,momentCoeff]
 have he : (fun n => crossCoeff 17 false n d)=(fun n => crossCoeff 17 true n d) :=
  funext (fun n => crossCoeff_endpoints_agree 17 n d hd)
 rw [he]

private theorem lower_coefficient_posDef (d : ℕ) (hd : d≤21) :
 (coefficientMatrix false d).PosDef := by
 interval_cases d
 · exact Lower0.coefficient_posDef
 · exact Lower1.coefficient_posDef
 · exact Lower2.coefficient_posDef
 · exact Lower3.coefficient_posDef
 · exact Lower4.coefficient_posDef
 · exact Lower5.coefficient_posDef
 · exact Lower6.coefficient_posDef
 · exact Lower7.coefficient_posDef
 · exact Lower8.coefficient_posDef
 · exact Lower9.coefficient_posDef
 · exact Lower10.coefficient_posDef
 · exact Lower11.coefficient_posDef
 · exact Lower12.coefficient_posDef
 · exact Lower13.coefficient_posDef
 · exact Lower14.coefficient_posDef
 · exact Lower15.coefficient_posDef
 · exact Lower16.coefficient_posDef
 · exact Lower17.coefficient_posDef
 · exact Lower18.coefficient_posDef
 · exact Lower19.coefficient_posDef
 · exact Lower20.coefficient_posDef
 · exact Lower21.coefficient_posDef

/-- Every coefficient of either normalized endpoint matrix is positive definite. -/
theorem coefficientMatrix_posDef (upper : Bool) (d : ℕ) (hd : d≤46) :
 (coefficientMatrix upper d).PosDef := by
 by_cases hlow : d≤21
 · cases upper with
   | false => exact lower_coefficient_posDef d hlow
   | true =>
     by_cases hz : d=0
     · subst d
       exact Upper0.coefficient_posDef
     · rw [← coefficientMatrix_endpoints_agree d hz]
       exact lower_coefficient_posDef d hlow
 · have hhigh : 22≤d := by omega
   have he : coefficientMatrix upper d=
     ((12*(Nat.choose 46 d:ℝ)-(Nat.choose 45 d:ℝ))/9216) • model 0 1 := by
    ext i j
    dsimp only [coefficientMatrix,momentCoeff,model,Matrix.smul_apply,smul_eq_mul]
    rw [pairLinear_crossCoeff_zero upper d (i.val+j.val) hhigh (by omega),
      mul_zero,add_zero,moment_eq_linearMoment _ _ _ (by omega)]
   rw [he]
   exact mass_model_posDef.smul (reserve_coefficient_pos 45 d hd)

private theorem pairLinear_crossScaled_expansion (upper : Bool) (y : ℝ)
 (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => crossScaled upper n (3*(1+y))) k=
  coeffEval (fun d => pairLinear (fun n => crossCoeff 17 upper n d) k) y := by
 rw [← pairLinear_coeffEval upper y k hk,
   pairLinear_sum k hk (fun n => crossScaled upper n (3*(1+y))),
   pairLinear_sum k hk (fun n => coeffEval (crossCoeff 17 upper n) y)]
 apply Finset.sum_congr rfl
 intro n hn
 have hn18 : n≤18 := by
  have hn19 := Finset.mem_range.mp hn
  omega
 rw [crossCoeff_expand upper n hn18 y]

private theorem clearedMoment_normalized_expansion (upper : Bool) (y : ℝ)
 (k : ℕ) (hk : k≤8) :
 clearedMoment upper (3*(1+y)) k=(3:ℝ)^48*coeffEval (fun d => momentCoeff upper d k) y := by
 have he : (fun d => momentCoeff upper d k)=
   (fun d => ((1/(768*3^46))*linearMoment (fun n => g n 0 1) k)*powerCoeff 46 d-
    ((1/(9216*3^45))*linearMoment (fun n => g n 0 1) k)*powerCoeff 45 d+
    (2*16/(27*(20:ℝ)^15))*pairLinear (fun n => crossCoeff 17 upper n d) k) := by
  funext d
  dsimp only [momentCoeff,powerCoeff]
  ring
 rw [he,coeffEval_add,coeffEval_sub,coeffEval_smul,coeffEval_smul,coeffEval_smul,
   coeffEval_power 46 (by norm_num),coeffEval_power 45 (by norm_num),
   ← pairLinear_crossScaled_expansion upper y k hk]
 generalize 3*(1+y)=q
 dsimp only [clearedMoment]
 ring

private theorem matrix_sum_apply {ι : Type} (s : Finset ι)
 (f : ι → Matrix (Fin 5) (Fin 5) ℝ) (i j : Fin 5) :
 (∑ d ∈ s, f d) i j=∑ d ∈ s, f d i j := by
 let ev : Matrix (Fin 5) (Fin 5) ℝ →+ ℝ :=
  { toFun := fun M => M i j
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
 exact map_sum ev f s

private theorem clearedMatrix_normalized_expansion (upper : Bool) (y : ℝ) :
 clearedMatrix upper (3*(1+y))=(3:ℝ)^48 •
  (∑ d ∈ Finset.range 47, y^d • coefficientMatrix upper d) := by
 ext i j
 simp only [clearedMatrix,Matrix.smul_apply,matrix_sum_apply,smul_eq_mul,coefficientMatrix]
 rw [clearedMoment_normalized_expansion upper y (i.val+j.val) (by omega)]
 congr 1
 dsimp only [coeffEval]
 exact Finset.sum_congr rfl (fun d _ => by ring)

private theorem weightedCoefficients_posDef (upper : Bool) (y : ℝ) (hy : 0≤y) :
 (∑ d ∈ Finset.range 47, y^d • coefficientMatrix upper d).PosDef := by
 have hs (n : ℕ) (hn : n≤46) :
   (∑ d ∈ Finset.range (n+1), y^d • coefficientMatrix upper d).PosDef := by
  revert hn
  induction n with
  | zero =>
    intro hn
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,one_smul,zero_add]
      using coefficientMatrix_posDef upper 0 (by norm_num)
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ]
    exact (ih (by omega)).add_posSemidef
      ((coefficientMatrix_posDef upper (n+1) hn).posSemidef.smul (pow_nonneg hy _))
 exact hs 46 le_rfl

/-- Both cleared gamma endpoint matrices are strict on the entire scale-three ray. -/
theorem clearedMatrix_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (clearedMatrix upper q).PosDef := by
 let y := q/3-1
 have hy : 0≤y := by dsimp only [y]; linarith only [hq]
 have he : q=3*(1+y) := by dsimp only [y]; ring
 rw [he,clearedMatrix_normalized_expansion]
 exact (weightedCoefficients_posDef upper y hy).smul (by positivity)

/-- The exact pair model with its allocated cubic gamma reserve. -/
def reserveModel (q z w : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 (3/(256*q^2)-3/(1024*q^3))*linearMoment (fun n => g n 0 1) (i.val+j.val)+
  (2*16)*w*pairLinear (fun n => gRate 17 n q z) (i.val+j.val)

private theorem crossScaled_eq (upper : Bool) (n : ℕ) {q : ℝ} (hq : q≠0) :
 crossScaled upper n q=q^3*gRate 17 n q (if upper then zUpper 17 q else zLower 17 q) := by
 induction n with
 | zero =>
   cases upper <;> simp only [crossScaled,gRate,zLower,zUpper,Bool.false_eq_true,ite_false,ite_true]
   all_goals (field_simp [hq] <;> simp only [mul_zero,sub_zero])
 | succ n ih =>
   simp only [crossScaled,gRate,ih]
   rw [show n+4=n+1+3 by omega,pow_add]
   ring

/-- Clearing the exponential and gamma denominators preserves the literal model. -/
theorem clearedMatrix_eq (upper : Bool) {q : ℝ} (hq : q≠0) :
 clearedMatrix upper q=q^48 • reserveModel q
   (if upper then zUpper 17 q else zLower 17 q) (3^45/((20:ℝ)^15*q^45)) := by
 ext i j
 dsimp only [clearedMatrix,clearedMoment,reserveModel,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => crossScaled upper n q)=
   (fun n => q^3*gRate 17 n q (if upper then zUpper 17 q else zLower 17 q)) from
   funext (fun n => crossScaled_eq upper n hq),pairLinear_smul _ _ _ (by omega)]
 field_simp [hq]

/-- Both extreme gamma masses fit the allocated first-atom correction. -/
theorem endpoint_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (reserveModel q (if upper then zUpper 17 q else zLower 17 q)
  (3^45/((20:ℝ)^15*q^45))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hp : (clearedMatrix upper q).PosDef := clearedMatrix_posDef upper hq
 rw [clearedMatrix_eq upper hq0.ne'] at hp
 have h := hp.smul (inv_pos.mpr (pow_pos hq0 48))
 simpa only [smul_smul,inv_mul_cancel₀ (pow_pos hq0 48).ne',one_smul] using h

private theorem model_affine_gamma (q a b t w : ℝ) :
 reserveModel q ((1-t)*a+t*b) w=
  (1-t) • reserveModel q a w+t • reserveModel q b w := by
 ext i j
 dsimp only [reserveModel,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => gRate 17 n q ((1-t)*a+t*b))=
   (fun n => (1-t)*gRate 17 n q a+t*gRate 17 n q b) from
   funext (gRate_affine 17 q a b t),pairLinear_affine _ _ _ _ (by omega)]
 ring

private theorem model_affine_weight (q z a b t : ℝ) :
 reserveModel q z ((1-t)*a+t*b)=
  (1-t) • reserveModel q z a+t • reserveModel q z b := by
 ext i j
 dsimp only [reserveModel,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 ring

private theorem convex_posDef {A B : Matrix (Fin 5) (Fin 5) ℝ}
 (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
 ((1-t) • A+t • B).PosDef := by
 by_cases hz : t=0
 · simpa only [hz,sub_zero,one_smul,zero_smul,add_zero] using hA
 have hp := (hB.smul (lt_of_le_of_ne ht (Ne.symm hz))).add_posSemidef
   (hA.posSemidef.smul (sub_nonneg.mpr ht1))
 simpa only [add_comm] using hp

/-- Every enclosed gamma mass is paid at the maximal polynomial weight. -/
theorem gamma_interval_posDef {q z : ℝ} (hq : 3≤q)
 (hzL : zLower 17 q≤z) (hzU : z≤zUpper 17 q) :
 (reserveModel q z (3^45/((20:ℝ)^15*q^45))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hd : 0<zUpper 17 q-zLower 17 q := by
  dsimp only [zLower,zUpper]
  ring_nf
  positivity
 have ht : 0≤(z-zLower 17 q)/(zUpper 17 q-zLower 17 q) :=
  div_nonneg (sub_nonneg.mpr hzL) hd.le
 have ht1 : (z-zLower 17 q)/(zUpper 17 q-zLower 17 q)≤1 := by
  apply (div_le_one hd).mpr
  linarith only [hzU]
 have he : z=(1-(z-zLower 17 q)/(zUpper 17 q-zLower 17 q))*zLower 17 q+
   ((z-zLower 17 q)/(zUpper 17 q-zLower 17 q))*zUpper 17 q := by
  field_simp [hd.ne']
  ring
 rw [he,model_affine_gamma]
 exact convex_posDef (endpoint_posDef false hq) (endpoint_posDef true hq) ht ht1

/-- The complete nonnegative weight interval fits the cubic gamma reserve. -/
theorem reserveModel_posDef {q z w : ℝ} (hq : 3≤q)
 (hzL : zLower 17 q≤z) (hzU : z≤zUpper 17 q) (hw : 0≤w)
 (hwU : w≤3^45/((20:ℝ)^15*q^45)) : (reserveModel q z w).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hW : 0<3^45/((20:ℝ)^15*q^45) := by positivity
 have ht : 0≤w/(3^45/((20:ℝ)^15*q^45)) := div_nonneg hw hW.le
 have ht1 : w/(3^45/((20:ℝ)^15*q^45))≤1 := (div_le_one hW).mpr hwU
 have h0 : (reserveModel q z 0).PosDef := by
  have he : reserveModel q z 0=(3/(256*q^2)-3/(1024*q^3)) • model 0 1 := by
   ext i j
   dsimp only [reserveModel,model,Matrix.smul_apply,smul_eq_mul]
   rw [moment_eq_linearMoment _ _ _ (by omega)]
   ring
  rw [he]
  exact mass_model_posDef.smul (cubic_eighth_pos hq)
 have he : w=(1-w/(3^45/((20:ℝ)^15*q^45)))*0+
   (w/(3^45/((20:ℝ)^15*q^45)))*(3^45/((20:ℝ)^15*q^45)) := by
  field_simp [hW.ne']
  ring
 rw [he,model_affine_weight]
 exact convex_posDef h0 (gamma_interval_posDef hq hzL hzU) ht ht1

end p14

namespace p23

/-- The gamma endpoint moments after multiplication by the radial scale cubed. -/
def crossScaled (upper : Bool) : ℕ → ℝ → ℝ
 | 0, q => q^3/13+3*q^2/(2*(13:ℝ)^2)+3*q/(4*(13:ℝ)^3)-
    (if upper then 0 else 3/(8*(13:ℝ)^4))
 | n+1, q => q^(n+4)/13+((2*n+5:ℕ):ℝ)/(2*13)*crossScaled upper n q

/-- The signed moment comparison after clearing all positive radial powers. -/
def clearedMoment (upper : Bool) (q : ℝ) (k : ℕ) : ℝ :=
 (3*q^34/256-3*q^33/1024)*linearMoment (fun n => g n 0 1) k+
  (2*36*3^33/(20:ℝ)^11)*pairLinear (fun n => crossScaled upper n q) k

/-- Hankel matrix of the cleared pair comparison. -/
def clearedMatrix (upper : Bool) (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 fun i j => clearedMoment upper q (i.val+j.val)

theorem powerCoeff_expand (n : ℕ) (hn : n≤34) (y : ℝ) :
 (3*(1+y))^n=∑ d ∈ Finset.range 35, powerCoeff n d*y^d := by
 calc
  _ = ∑ d ∈ Finset.range (n+1), powerCoeff n d*y^d := by
   rw [mul_pow,add_comm (1:ℝ),add_pow,Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro d hd
   simp only [powerCoeff,one_pow,mul_one]
   ring
  _ = _ := by
   apply Finset.sum_subset (Finset.range_mono (by omega))
   intro d hd hdn
   have hnd : n<d := by simp only [Finset.mem_range] at hd hdn; omega
   simp only [powerCoeff,Nat.choose_eq_zero_of_lt hnd,Nat.cast_zero,zero_mul]

private def coeffEval (f : ℕ → ℝ) (y : ℝ) : ℝ :=
 ∑ d ∈ Finset.range 35, f d*y^d

private theorem coeffEval_add (f h : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => f d+h d) y=coeffEval f y+coeffEval h y := by
 simp only [coeffEval,add_mul,Finset.sum_add_distrib]

private theorem coeffEval_sub (f h : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => f d-h d) y=coeffEval f y-coeffEval h y := by
 simp only [coeffEval,sub_mul,Finset.sum_sub_distrib]

private theorem coeffEval_smul (c : ℝ) (f : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => c*f d) y=c*coeffEval f y := by
 simp only [coeffEval,mul_assoc,Finset.mul_sum]

private theorem coeffEval_one (y : ℝ) :
 coeffEval (fun d => if d=0 then 1 else 0) y=1 := by
 simp [coeffEval]

private theorem coeffEval_power (n : ℕ) (hn : n≤34) (y : ℝ) :
 coeffEval (powerCoeff n) y=(3*(1+y))^n := (powerCoeff_expand n hn y).symm

private theorem crossCoeff_zero (upper : Bool) :
 crossCoeff 13 upper 0=fun d =>
  ((1/13)*powerCoeff 3 d+(3/(2*(13:ℝ)^2))*powerCoeff 2 d+(3/(4*(13:ℝ)^3))*powerCoeff 1 d)-
   (if upper then 0 else 3/(8*(13:ℝ)^4))*(if d=0 then 1 else 0) := by
 funext d
 simp only [crossCoeff]
 split_ifs <;> ring

private theorem crossCoeff_succ (upper : Bool) (n : ℕ) :
 crossCoeff 13 upper (n+1)=fun d => (1/13)*powerCoeff (n+4) d+
  (((2*n+5:ℕ):ℝ)/(2*13))*crossCoeff 13 upper n d := by
 funext d
 simp only [crossCoeff]
 ring

/-- Every scaled gamma endpoint is the binomial expansion of its radial polynomial. -/
theorem crossCoeff_expand (upper : Bool) (n : ℕ) (hn : n≤18) (y : ℝ) :
 crossScaled upper n (3*(1+y))=coeffEval (crossCoeff 13 upper n) y := by
 revert hn
 induction n with
 | zero =>
   intro hn
   rw [crossCoeff_zero,coeffEval_sub,coeffEval_add,coeffEval_add,
    coeffEval_smul,coeffEval_smul,coeffEval_smul,coeffEval_smul,
    coeffEval_power 3 (by norm_num),coeffEval_power 2 (by norm_num),
    coeffEval_power 1 (by norm_num),coeffEval_one]
   simp only [crossScaled]
   ring
 | succ n ih =>
   intro hn
   rw [crossCoeff_succ,coeffEval_add,coeffEval_smul,coeffEval_smul,
    coeffEval_power (n+4) (by omega),← ih (by omega)]
   simp only [crossScaled]
   ring

/-- Scaled pair moments have degree at most three above their power index. -/
theorem crossCoeff_eq_zero (upper : Bool) (n d : ℕ) (hd : n+3<d) :
 crossCoeff 13 upper n d=0 := by
 revert hd
 induction n with
 | zero =>
   intro hd
   have h3 : 3<d := by omega
   have h2 : 2<d := by omega
   have h1 : 1<d := by omega
   have h0 : d≠0 := by omega
   simp only [crossCoeff,powerCoeff,Nat.choose_eq_zero_of_lt h3,
    Nat.choose_eq_zero_of_lt h2,Nat.choose_eq_zero_of_lt h1,
    Nat.cast_zero,zero_mul,zero_div,mul_zero,add_zero,h0,ite_false]
   cases upper <;> norm_num
 | succ n ih =>
   intro hd
   rw [crossCoeff,ih (by omega)]
   simp only [powerCoeff,Nat.choose_eq_zero_of_lt (show n+4<d by omega),
    Nat.cast_zero,zero_mul,zero_div,mul_zero,add_zero]

private theorem pairLinear_coeffEval (upper : Bool) (y : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => coeffEval (crossCoeff 13 upper n) y) k=
  coeffEval (fun d => pairLinear (fun n => crossCoeff 13 upper n d) k) y := by
 rw [pairLinear_sum k hk]
 dsimp only [coeffEval]
 simp only [Finset.mul_sum]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro d hd
 rw [pairLinear_sum k hk,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro n hn
 ring

/-- Every coefficient above degree twenty-one contains only the positive mass reserve. -/
theorem pairLinear_crossCoeff_zero (upper : Bool) (d k : ℕ) (hd : 22≤d) (hk : k≤8) :
 pairLinear (fun n => crossCoeff 13 upper n d) k=0 := by
 rw [pairLinear_sum k hk]
 apply Finset.sum_eq_zero
 intro n hn
 have hn18 : n≤18 := by
  have hn19 := Finset.mem_range.mp hn
  omega
 rw [crossCoeff_eq_zero upper n d (by omega),mul_zero]

private theorem coefficientMatrix_endpoints_agree (d : ℕ) (hd : d≠0) :
 coefficientMatrix false d=coefficientMatrix true d := by
 ext i j
 dsimp only [coefficientMatrix,momentCoeff]
 have he : (fun n => crossCoeff 13 false n d)=(fun n => crossCoeff 13 true n d) :=
  funext (fun n => crossCoeff_endpoints_agree 13 n d hd)
 rw [he]

private theorem lower_coefficient_posDef (d : ℕ) (hd : d≤21) :
 (coefficientMatrix false d).PosDef := by
 interval_cases d
 · exact Lower0.coefficient_posDef
 · exact Lower1.coefficient_posDef
 · exact Lower2.coefficient_posDef
 · exact Lower3.coefficient_posDef
 · exact Lower4.coefficient_posDef
 · exact Lower5.coefficient_posDef
 · exact Lower6.coefficient_posDef
 · exact Lower7.coefficient_posDef
 · exact Lower8.coefficient_posDef
 · exact Lower9.coefficient_posDef
 · exact Lower10.coefficient_posDef
 · exact Lower11.coefficient_posDef
 · exact Lower12.coefficient_posDef
 · exact Lower13.coefficient_posDef
 · exact Lower14.coefficient_posDef
 · exact Lower15.coefficient_posDef
 · exact Lower16.coefficient_posDef
 · exact Lower17.coefficient_posDef
 · exact Lower18.coefficient_posDef
 · exact Lower19.coefficient_posDef
 · exact Lower20.coefficient_posDef
 · exact Lower21.coefficient_posDef

/-- Every coefficient of either normalized endpoint matrix is positive definite. -/
theorem coefficientMatrix_posDef (upper : Bool) (d : ℕ) (hd : d≤34) :
 (coefficientMatrix upper d).PosDef := by
 by_cases hlow : d≤21
 · cases upper with
   | false => exact lower_coefficient_posDef d hlow
   | true =>
     by_cases hz : d=0
     · subst d
       exact Upper0.coefficient_posDef
     · rw [← coefficientMatrix_endpoints_agree d hz]
       exact lower_coefficient_posDef d hlow
 · have hhigh : 22≤d := by omega
   have he : coefficientMatrix upper d=
     ((12*(Nat.choose 34 d:ℝ)-(Nat.choose 33 d:ℝ))/9216) • model 0 1 := by
    ext i j
    dsimp only [coefficientMatrix,momentCoeff,model,Matrix.smul_apply,smul_eq_mul]
    rw [pairLinear_crossCoeff_zero upper d (i.val+j.val) hhigh (by omega),
      mul_zero,add_zero,moment_eq_linearMoment _ _ _ (by omega)]
   rw [he]
   exact mass_model_posDef.smul (reserve_coefficient_pos 33 d hd)

private theorem pairLinear_crossScaled_expansion (upper : Bool) (y : ℝ)
 (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => crossScaled upper n (3*(1+y))) k=
  coeffEval (fun d => pairLinear (fun n => crossCoeff 13 upper n d) k) y := by
 rw [← pairLinear_coeffEval upper y k hk,
   pairLinear_sum k hk (fun n => crossScaled upper n (3*(1+y))),
   pairLinear_sum k hk (fun n => coeffEval (crossCoeff 13 upper n) y)]
 apply Finset.sum_congr rfl
 intro n hn
 have hn18 : n≤18 := by
  have hn19 := Finset.mem_range.mp hn
  omega
 rw [crossCoeff_expand upper n hn18 y]

private theorem clearedMoment_normalized_expansion (upper : Bool) (y : ℝ)
 (k : ℕ) (hk : k≤8) :
 clearedMoment upper (3*(1+y)) k=(3:ℝ)^36*coeffEval (fun d => momentCoeff upper d k) y := by
 have he : (fun d => momentCoeff upper d k)=
   (fun d => ((1/(768*3^34))*linearMoment (fun n => g n 0 1) k)*powerCoeff 34 d-
    ((1/(9216*3^33))*linearMoment (fun n => g n 0 1) k)*powerCoeff 33 d+
    (2*36/(27*(20:ℝ)^11))*pairLinear (fun n => crossCoeff 13 upper n d) k) := by
  funext d
  dsimp only [momentCoeff,powerCoeff]
  ring
 rw [he,coeffEval_add,coeffEval_sub,coeffEval_smul,coeffEval_smul,coeffEval_smul,
   coeffEval_power 34 (by norm_num),coeffEval_power 33 (by norm_num),
   ← pairLinear_crossScaled_expansion upper y k hk]
 generalize 3*(1+y)=q
 dsimp only [clearedMoment]
 ring

private theorem matrix_sum_apply {ι : Type} (s : Finset ι)
 (f : ι → Matrix (Fin 5) (Fin 5) ℝ) (i j : Fin 5) :
 (∑ d ∈ s, f d) i j=∑ d ∈ s, f d i j := by
 let ev : Matrix (Fin 5) (Fin 5) ℝ →+ ℝ :=
  { toFun := fun M => M i j
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
 exact map_sum ev f s

private theorem clearedMatrix_normalized_expansion (upper : Bool) (y : ℝ) :
 clearedMatrix upper (3*(1+y))=(3:ℝ)^36 •
  (∑ d ∈ Finset.range 35, y^d • coefficientMatrix upper d) := by
 ext i j
 simp only [clearedMatrix,Matrix.smul_apply,matrix_sum_apply,smul_eq_mul,coefficientMatrix]
 rw [clearedMoment_normalized_expansion upper y (i.val+j.val) (by omega)]
 congr 1
 dsimp only [coeffEval]
 exact Finset.sum_congr rfl (fun d _ => by ring)

private theorem weightedCoefficients_posDef (upper : Bool) (y : ℝ) (hy : 0≤y) :
 (∑ d ∈ Finset.range 35, y^d • coefficientMatrix upper d).PosDef := by
 have hs (n : ℕ) (hn : n≤34) :
   (∑ d ∈ Finset.range (n+1), y^d • coefficientMatrix upper d).PosDef := by
  revert hn
  induction n with
  | zero =>
    intro hn
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,one_smul,zero_add]
      using coefficientMatrix_posDef upper 0 (by norm_num)
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ]
    exact (ih (by omega)).add_posSemidef
      ((coefficientMatrix_posDef upper (n+1) hn).posSemidef.smul (pow_nonneg hy _))
 exact hs 34 le_rfl

/-- Both cleared gamma endpoint matrices are strict on the entire scale-three ray. -/
theorem clearedMatrix_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (clearedMatrix upper q).PosDef := by
 let y := q/3-1
 have hy : 0≤y := by dsimp only [y]; linarith only [hq]
 have he : q=3*(1+y) := by dsimp only [y]; ring
 rw [he,clearedMatrix_normalized_expansion]
 exact (weightedCoefficients_posDef upper y hy).smul (by positivity)

/-- The exact pair model with its allocated cubic gamma reserve. -/
def reserveModel (q z w : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 (3/(256*q^2)-3/(1024*q^3))*linearMoment (fun n => g n 0 1) (i.val+j.val)+
  (2*36)*w*pairLinear (fun n => gRate 13 n q z) (i.val+j.val)

private theorem crossScaled_eq (upper : Bool) (n : ℕ) {q : ℝ} (hq : q≠0) :
 crossScaled upper n q=q^3*gRate 13 n q (if upper then zUpper 13 q else zLower 13 q) := by
 induction n with
 | zero =>
   cases upper <;> simp only [crossScaled,gRate,zLower,zUpper,Bool.false_eq_true,ite_false,ite_true]
   all_goals (field_simp [hq] <;> simp only [mul_zero,sub_zero])
 | succ n ih =>
   simp only [crossScaled,gRate,ih]
   rw [show n+4=n+1+3 by omega,pow_add]
   ring

/-- Clearing the exponential and gamma denominators preserves the literal model. -/
theorem clearedMatrix_eq (upper : Bool) {q : ℝ} (hq : q≠0) :
 clearedMatrix upper q=q^36 • reserveModel q
   (if upper then zUpper 13 q else zLower 13 q) (3^33/((20:ℝ)^11*q^33)) := by
 ext i j
 dsimp only [clearedMatrix,clearedMoment,reserveModel,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => crossScaled upper n q)=
   (fun n => q^3*gRate 13 n q (if upper then zUpper 13 q else zLower 13 q)) from
   funext (fun n => crossScaled_eq upper n hq),pairLinear_smul _ _ _ (by omega)]
 field_simp [hq]

/-- Both extreme gamma masses fit the allocated first-atom correction. -/
theorem endpoint_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (reserveModel q (if upper then zUpper 13 q else zLower 13 q)
  (3^33/((20:ℝ)^11*q^33))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hp : (clearedMatrix upper q).PosDef := clearedMatrix_posDef upper hq
 rw [clearedMatrix_eq upper hq0.ne'] at hp
 have h := hp.smul (inv_pos.mpr (pow_pos hq0 36))
 simpa only [smul_smul,inv_mul_cancel₀ (pow_pos hq0 36).ne',one_smul] using h

private theorem model_affine_gamma (q a b t w : ℝ) :
 reserveModel q ((1-t)*a+t*b) w=
  (1-t) • reserveModel q a w+t • reserveModel q b w := by
 ext i j
 dsimp only [reserveModel,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => gRate 13 n q ((1-t)*a+t*b))=
   (fun n => (1-t)*gRate 13 n q a+t*gRate 13 n q b) from
   funext (gRate_affine 13 q a b t),pairLinear_affine _ _ _ _ (by omega)]
 ring

private theorem model_affine_weight (q z a b t : ℝ) :
 reserveModel q z ((1-t)*a+t*b)=
  (1-t) • reserveModel q z a+t • reserveModel q z b := by
 ext i j
 dsimp only [reserveModel,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 ring

private theorem convex_posDef {A B : Matrix (Fin 5) (Fin 5) ℝ}
 (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
 ((1-t) • A+t • B).PosDef := by
 by_cases hz : t=0
 · simpa only [hz,sub_zero,one_smul,zero_smul,add_zero] using hA
 have hp := (hB.smul (lt_of_le_of_ne ht (Ne.symm hz))).add_posSemidef
   (hA.posSemidef.smul (sub_nonneg.mpr ht1))
 simpa only [add_comm] using hp

/-- Every enclosed gamma mass is paid at the maximal polynomial weight. -/
theorem gamma_interval_posDef {q z : ℝ} (hq : 3≤q)
 (hzL : zLower 13 q≤z) (hzU : z≤zUpper 13 q) :
 (reserveModel q z (3^33/((20:ℝ)^11*q^33))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hd : 0<zUpper 13 q-zLower 13 q := by
  dsimp only [zLower,zUpper]
  ring_nf
  positivity
 have ht : 0≤(z-zLower 13 q)/(zUpper 13 q-zLower 13 q) :=
  div_nonneg (sub_nonneg.mpr hzL) hd.le
 have ht1 : (z-zLower 13 q)/(zUpper 13 q-zLower 13 q)≤1 := by
  apply (div_le_one hd).mpr
  linarith only [hzU]
 have he : z=(1-(z-zLower 13 q)/(zUpper 13 q-zLower 13 q))*zLower 13 q+
   ((z-zLower 13 q)/(zUpper 13 q-zLower 13 q))*zUpper 13 q := by
  field_simp [hd.ne']
  ring
 rw [he,model_affine_gamma]
 exact convex_posDef (endpoint_posDef false hq) (endpoint_posDef true hq) ht ht1

/-- The complete nonnegative weight interval fits the cubic gamma reserve. -/
theorem reserveModel_posDef {q z w : ℝ} (hq : 3≤q)
 (hzL : zLower 13 q≤z) (hzU : z≤zUpper 13 q) (hw : 0≤w)
 (hwU : w≤3^33/((20:ℝ)^11*q^33)) : (reserveModel q z w).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hW : 0<3^33/((20:ℝ)^11*q^33) := by positivity
 have ht : 0≤w/(3^33/((20:ℝ)^11*q^33)) := div_nonneg hw hW.le
 have ht1 : w/(3^33/((20:ℝ)^11*q^33))≤1 := (div_le_one hW).mpr hwU
 have h0 : (reserveModel q z 0).PosDef := by
  have he : reserveModel q z 0=(3/(256*q^2)-3/(1024*q^3)) • model 0 1 := by
   ext i j
   dsimp only [reserveModel,model,Matrix.smul_apply,smul_eq_mul]
   rw [moment_eq_linearMoment _ _ _ (by omega)]
   ring
  rw [he]
  exact mass_model_posDef.smul (cubic_eighth_pos hq)
 have he : w=(1-w/(3^33/((20:ℝ)^11*q^33)))*0+
   (w/(3^33/((20:ℝ)^11*q^33)))*(3^33/((20:ℝ)^11*q^33)) := by
  field_simp [hW.ne']
  ring
 rw [he,model_affine_weight]
 exact convex_posDef h0 (gamma_interval_posDef hq hzL hzU) ht ht1

end p23

namespace p24

/-- The gamma endpoint moments after multiplication by the radial scale cubed. -/
def crossScaled (upper : Bool) : ℕ → ℝ → ℝ
 | 0, q => q^3/20+3*q^2/(2*(20:ℝ)^2)+3*q/(4*(20:ℝ)^3)-
    (if upper then 0 else 3/(8*(20:ℝ)^4))
 | n+1, q => q^(n+4)/20+((2*n+5:ℕ):ℝ)/(2*20)*crossScaled upper n q

/-- The signed moment comparison after clearing all positive radial powers. -/
def clearedMoment (upper : Bool) (q : ℝ) (k : ℕ) : ℝ :=
 (3*q^55/256-3*q^54/1024)*linearMoment (fun n => g n 0 1) k+
  (2*64*3^54/(20:ℝ)^18)*pairLinear (fun n => crossScaled upper n q) k

/-- Hankel matrix of the cleared pair comparison. -/
def clearedMatrix (upper : Bool) (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 fun i j => clearedMoment upper q (i.val+j.val)

theorem powerCoeff_expand (n : ℕ) (hn : n≤55) (y : ℝ) :
 (3*(1+y))^n=∑ d ∈ Finset.range 56, powerCoeff n d*y^d := by
 calc
  _ = ∑ d ∈ Finset.range (n+1), powerCoeff n d*y^d := by
   rw [mul_pow,add_comm (1:ℝ),add_pow,Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro d hd
   simp only [powerCoeff,one_pow,mul_one]
   ring
  _ = _ := by
   apply Finset.sum_subset (Finset.range_mono (by omega))
   intro d hd hdn
   have hnd : n<d := by simp only [Finset.mem_range] at hd hdn; omega
   simp only [powerCoeff,Nat.choose_eq_zero_of_lt hnd,Nat.cast_zero,zero_mul]

private def coeffEval (f : ℕ → ℝ) (y : ℝ) : ℝ :=
 ∑ d ∈ Finset.range 56, f d*y^d

private theorem coeffEval_add (f h : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => f d+h d) y=coeffEval f y+coeffEval h y := by
 simp only [coeffEval,add_mul,Finset.sum_add_distrib]

private theorem coeffEval_sub (f h : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => f d-h d) y=coeffEval f y-coeffEval h y := by
 simp only [coeffEval,sub_mul,Finset.sum_sub_distrib]

private theorem coeffEval_smul (c : ℝ) (f : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => c*f d) y=c*coeffEval f y := by
 simp only [coeffEval,mul_assoc,Finset.mul_sum]

private theorem coeffEval_one (y : ℝ) :
 coeffEval (fun d => if d=0 then 1 else 0) y=1 := by
 simp [coeffEval]

private theorem coeffEval_power (n : ℕ) (hn : n≤55) (y : ℝ) :
 coeffEval (powerCoeff n) y=(3*(1+y))^n := (powerCoeff_expand n hn y).symm

private theorem crossCoeff_zero (upper : Bool) :
 crossCoeff 20 upper 0=fun d =>
  ((1/20)*powerCoeff 3 d+(3/(2*(20:ℝ)^2))*powerCoeff 2 d+(3/(4*(20:ℝ)^3))*powerCoeff 1 d)-
   (if upper then 0 else 3/(8*(20:ℝ)^4))*(if d=0 then 1 else 0) := by
 funext d
 simp only [crossCoeff]
 split_ifs <;> ring

private theorem crossCoeff_succ (upper : Bool) (n : ℕ) :
 crossCoeff 20 upper (n+1)=fun d => (1/20)*powerCoeff (n+4) d+
  (((2*n+5:ℕ):ℝ)/(2*20))*crossCoeff 20 upper n d := by
 funext d
 simp only [crossCoeff]
 ring

/-- Every scaled gamma endpoint is the binomial expansion of its radial polynomial. -/
theorem crossCoeff_expand (upper : Bool) (n : ℕ) (hn : n≤18) (y : ℝ) :
 crossScaled upper n (3*(1+y))=coeffEval (crossCoeff 20 upper n) y := by
 revert hn
 induction n with
 | zero =>
   intro hn
   rw [crossCoeff_zero,coeffEval_sub,coeffEval_add,coeffEval_add,
    coeffEval_smul,coeffEval_smul,coeffEval_smul,coeffEval_smul,
    coeffEval_power 3 (by norm_num),coeffEval_power 2 (by norm_num),
    coeffEval_power 1 (by norm_num),coeffEval_one]
   simp only [crossScaled]
   ring
 | succ n ih =>
   intro hn
   rw [crossCoeff_succ,coeffEval_add,coeffEval_smul,coeffEval_smul,
    coeffEval_power (n+4) (by omega),← ih (by omega)]
   simp only [crossScaled]
   ring

/-- Scaled pair moments have degree at most three above their power index. -/
theorem crossCoeff_eq_zero (upper : Bool) (n d : ℕ) (hd : n+3<d) :
 crossCoeff 20 upper n d=0 := by
 revert hd
 induction n with
 | zero =>
   intro hd
   have h3 : 3<d := by omega
   have h2 : 2<d := by omega
   have h1 : 1<d := by omega
   have h0 : d≠0 := by omega
   simp only [crossCoeff,powerCoeff,Nat.choose_eq_zero_of_lt h3,
    Nat.choose_eq_zero_of_lt h2,Nat.choose_eq_zero_of_lt h1,
    Nat.cast_zero,zero_mul,zero_div,mul_zero,add_zero,h0,ite_false]
   cases upper <;> norm_num
 | succ n ih =>
   intro hd
   rw [crossCoeff,ih (by omega)]
   simp only [powerCoeff,Nat.choose_eq_zero_of_lt (show n+4<d by omega),
    Nat.cast_zero,zero_mul,zero_div,mul_zero,add_zero]

private theorem pairLinear_coeffEval (upper : Bool) (y : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => coeffEval (crossCoeff 20 upper n) y) k=
  coeffEval (fun d => pairLinear (fun n => crossCoeff 20 upper n d) k) y := by
 rw [pairLinear_sum k hk]
 dsimp only [coeffEval]
 simp only [Finset.mul_sum]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro d hd
 rw [pairLinear_sum k hk,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro n hn
 ring

/-- Every coefficient above degree twenty-one contains only the positive mass reserve. -/
theorem pairLinear_crossCoeff_zero (upper : Bool) (d k : ℕ) (hd : 22≤d) (hk : k≤8) :
 pairLinear (fun n => crossCoeff 20 upper n d) k=0 := by
 rw [pairLinear_sum k hk]
 apply Finset.sum_eq_zero
 intro n hn
 have hn18 : n≤18 := by
  have hn19 := Finset.mem_range.mp hn
  omega
 rw [crossCoeff_eq_zero upper n d (by omega),mul_zero]

private theorem coefficientMatrix_endpoints_agree (d : ℕ) (hd : d≠0) :
 coefficientMatrix false d=coefficientMatrix true d := by
 ext i j
 dsimp only [coefficientMatrix,momentCoeff]
 have he : (fun n => crossCoeff 20 false n d)=(fun n => crossCoeff 20 true n d) :=
  funext (fun n => crossCoeff_endpoints_agree 20 n d hd)
 rw [he]

private theorem lower_coefficient_posDef (d : ℕ) (hd : d≤21) :
 (coefficientMatrix false d).PosDef := by
 interval_cases d
 · exact Lower0.coefficient_posDef
 · exact Lower1.coefficient_posDef
 · exact Lower2.coefficient_posDef
 · exact Lower3.coefficient_posDef
 · exact Lower4.coefficient_posDef
 · exact Lower5.coefficient_posDef
 · exact Lower6.coefficient_posDef
 · exact Lower7.coefficient_posDef
 · exact Lower8.coefficient_posDef
 · exact Lower9.coefficient_posDef
 · exact Lower10.coefficient_posDef
 · exact Lower11.coefficient_posDef
 · exact Lower12.coefficient_posDef
 · exact Lower13.coefficient_posDef
 · exact Lower14.coefficient_posDef
 · exact Lower15.coefficient_posDef
 · exact Lower16.coefficient_posDef
 · exact Lower17.coefficient_posDef
 · exact Lower18.coefficient_posDef
 · exact Lower19.coefficient_posDef
 · exact Lower20.coefficient_posDef
 · exact Lower21.coefficient_posDef

/-- Every coefficient of either normalized endpoint matrix is positive definite. -/
theorem coefficientMatrix_posDef (upper : Bool) (d : ℕ) (hd : d≤55) :
 (coefficientMatrix upper d).PosDef := by
 by_cases hlow : d≤21
 · cases upper with
   | false => exact lower_coefficient_posDef d hlow
   | true =>
     by_cases hz : d=0
     · subst d
       exact Upper0.coefficient_posDef
     · rw [← coefficientMatrix_endpoints_agree d hz]
       exact lower_coefficient_posDef d hlow
 · have hhigh : 22≤d := by omega
   have he : coefficientMatrix upper d=
     ((12*(Nat.choose 55 d:ℝ)-(Nat.choose 54 d:ℝ))/9216) • model 0 1 := by
    ext i j
    dsimp only [coefficientMatrix,momentCoeff,model,Matrix.smul_apply,smul_eq_mul]
    rw [pairLinear_crossCoeff_zero upper d (i.val+j.val) hhigh (by omega),
      mul_zero,add_zero,moment_eq_linearMoment _ _ _ (by omega)]
   rw [he]
   exact mass_model_posDef.smul (reserve_coefficient_pos 54 d hd)

private theorem pairLinear_crossScaled_expansion (upper : Bool) (y : ℝ)
 (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => crossScaled upper n (3*(1+y))) k=
  coeffEval (fun d => pairLinear (fun n => crossCoeff 20 upper n d) k) y := by
 rw [← pairLinear_coeffEval upper y k hk,
   pairLinear_sum k hk (fun n => crossScaled upper n (3*(1+y))),
   pairLinear_sum k hk (fun n => coeffEval (crossCoeff 20 upper n) y)]
 apply Finset.sum_congr rfl
 intro n hn
 have hn18 : n≤18 := by
  have hn19 := Finset.mem_range.mp hn
  omega
 rw [crossCoeff_expand upper n hn18 y]

private theorem clearedMoment_normalized_expansion (upper : Bool) (y : ℝ)
 (k : ℕ) (hk : k≤8) :
 clearedMoment upper (3*(1+y)) k=(3:ℝ)^57*coeffEval (fun d => momentCoeff upper d k) y := by
 have he : (fun d => momentCoeff upper d k)=
   (fun d => ((1/(768*3^55))*linearMoment (fun n => g n 0 1) k)*powerCoeff 55 d-
    ((1/(9216*3^54))*linearMoment (fun n => g n 0 1) k)*powerCoeff 54 d+
    (2*64/(27*(20:ℝ)^18))*pairLinear (fun n => crossCoeff 20 upper n d) k) := by
  funext d
  dsimp only [momentCoeff,powerCoeff]
  ring
 rw [he,coeffEval_add,coeffEval_sub,coeffEval_smul,coeffEval_smul,coeffEval_smul,
   coeffEval_power 55 (by norm_num),coeffEval_power 54 (by norm_num),
   ← pairLinear_crossScaled_expansion upper y k hk]
 generalize 3*(1+y)=q
 dsimp only [clearedMoment]
 ring

private theorem matrix_sum_apply {ι : Type} (s : Finset ι)
 (f : ι → Matrix (Fin 5) (Fin 5) ℝ) (i j : Fin 5) :
 (∑ d ∈ s, f d) i j=∑ d ∈ s, f d i j := by
 let ev : Matrix (Fin 5) (Fin 5) ℝ →+ ℝ :=
  { toFun := fun M => M i j
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
 exact map_sum ev f s

private theorem clearedMatrix_normalized_expansion (upper : Bool) (y : ℝ) :
 clearedMatrix upper (3*(1+y))=(3:ℝ)^57 •
  (∑ d ∈ Finset.range 56, y^d • coefficientMatrix upper d) := by
 ext i j
 simp only [clearedMatrix,Matrix.smul_apply,matrix_sum_apply,smul_eq_mul,coefficientMatrix]
 rw [clearedMoment_normalized_expansion upper y (i.val+j.val) (by omega)]
 congr 1
 dsimp only [coeffEval]
 exact Finset.sum_congr rfl (fun d _ => by ring)

private theorem weightedCoefficients_posDef (upper : Bool) (y : ℝ) (hy : 0≤y) :
 (∑ d ∈ Finset.range 56, y^d • coefficientMatrix upper d).PosDef := by
 have hs (n : ℕ) (hn : n≤55) :
   (∑ d ∈ Finset.range (n+1), y^d • coefficientMatrix upper d).PosDef := by
  revert hn
  induction n with
  | zero =>
    intro hn
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,one_smul,zero_add]
      using coefficientMatrix_posDef upper 0 (by norm_num)
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ]
    exact (ih (by omega)).add_posSemidef
      ((coefficientMatrix_posDef upper (n+1) hn).posSemidef.smul (pow_nonneg hy _))
 exact hs 55 le_rfl

/-- Both cleared gamma endpoint matrices are strict on the entire scale-three ray. -/
theorem clearedMatrix_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (clearedMatrix upper q).PosDef := by
 let y := q/3-1
 have hy : 0≤y := by dsimp only [y]; linarith only [hq]
 have he : q=3*(1+y) := by dsimp only [y]; ring
 rw [he,clearedMatrix_normalized_expansion]
 exact (weightedCoefficients_posDef upper y hy).smul (by positivity)

/-- The exact pair model with its allocated cubic gamma reserve. -/
def reserveModel (q z w : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 (3/(256*q^2)-3/(1024*q^3))*linearMoment (fun n => g n 0 1) (i.val+j.val)+
  (2*64)*w*pairLinear (fun n => gRate 20 n q z) (i.val+j.val)

private theorem crossScaled_eq (upper : Bool) (n : ℕ) {q : ℝ} (hq : q≠0) :
 crossScaled upper n q=q^3*gRate 20 n q (if upper then zUpper 20 q else zLower 20 q) := by
 induction n with
 | zero =>
   cases upper <;> simp only [crossScaled,gRate,zLower,zUpper,Bool.false_eq_true,ite_false,ite_true]
   all_goals (field_simp [hq] <;> simp only [mul_zero,sub_zero])
 | succ n ih =>
   simp only [crossScaled,gRate,ih]
   rw [show n+4=n+1+3 by omega,pow_add]
   ring

/-- Clearing the exponential and gamma denominators preserves the literal model. -/
theorem clearedMatrix_eq (upper : Bool) {q : ℝ} (hq : q≠0) :
 clearedMatrix upper q=q^57 • reserveModel q
   (if upper then zUpper 20 q else zLower 20 q) (3^54/((20:ℝ)^18*q^54)) := by
 ext i j
 dsimp only [clearedMatrix,clearedMoment,reserveModel,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => crossScaled upper n q)=
   (fun n => q^3*gRate 20 n q (if upper then zUpper 20 q else zLower 20 q)) from
   funext (fun n => crossScaled_eq upper n hq),pairLinear_smul _ _ _ (by omega)]
 field_simp [hq]

/-- Both extreme gamma masses fit the allocated first-atom correction. -/
theorem endpoint_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (reserveModel q (if upper then zUpper 20 q else zLower 20 q)
  (3^54/((20:ℝ)^18*q^54))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hp : (clearedMatrix upper q).PosDef := clearedMatrix_posDef upper hq
 rw [clearedMatrix_eq upper hq0.ne'] at hp
 have h := hp.smul (inv_pos.mpr (pow_pos hq0 57))
 simpa only [smul_smul,inv_mul_cancel₀ (pow_pos hq0 57).ne',one_smul] using h

private theorem model_affine_gamma (q a b t w : ℝ) :
 reserveModel q ((1-t)*a+t*b) w=
  (1-t) • reserveModel q a w+t • reserveModel q b w := by
 ext i j
 dsimp only [reserveModel,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => gRate 20 n q ((1-t)*a+t*b))=
   (fun n => (1-t)*gRate 20 n q a+t*gRate 20 n q b) from
   funext (gRate_affine 20 q a b t),pairLinear_affine _ _ _ _ (by omega)]
 ring

private theorem model_affine_weight (q z a b t : ℝ) :
 reserveModel q z ((1-t)*a+t*b)=
  (1-t) • reserveModel q z a+t • reserveModel q z b := by
 ext i j
 dsimp only [reserveModel,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 ring

private theorem convex_posDef {A B : Matrix (Fin 5) (Fin 5) ℝ}
 (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
 ((1-t) • A+t • B).PosDef := by
 by_cases hz : t=0
 · simpa only [hz,sub_zero,one_smul,zero_smul,add_zero] using hA
 have hp := (hB.smul (lt_of_le_of_ne ht (Ne.symm hz))).add_posSemidef
   (hA.posSemidef.smul (sub_nonneg.mpr ht1))
 simpa only [add_comm] using hp

/-- Every enclosed gamma mass is paid at the maximal polynomial weight. -/
theorem gamma_interval_posDef {q z : ℝ} (hq : 3≤q)
 (hzL : zLower 20 q≤z) (hzU : z≤zUpper 20 q) :
 (reserveModel q z (3^54/((20:ℝ)^18*q^54))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hd : 0<zUpper 20 q-zLower 20 q := by
  dsimp only [zLower,zUpper]
  ring_nf
  positivity
 have ht : 0≤(z-zLower 20 q)/(zUpper 20 q-zLower 20 q) :=
  div_nonneg (sub_nonneg.mpr hzL) hd.le
 have ht1 : (z-zLower 20 q)/(zUpper 20 q-zLower 20 q)≤1 := by
  apply (div_le_one hd).mpr
  linarith only [hzU]
 have he : z=(1-(z-zLower 20 q)/(zUpper 20 q-zLower 20 q))*zLower 20 q+
   ((z-zLower 20 q)/(zUpper 20 q-zLower 20 q))*zUpper 20 q := by
  field_simp [hd.ne']
  ring
 rw [he,model_affine_gamma]
 exact convex_posDef (endpoint_posDef false hq) (endpoint_posDef true hq) ht ht1

/-- The complete nonnegative weight interval fits the cubic gamma reserve. -/
theorem reserveModel_posDef {q z w : ℝ} (hq : 3≤q)
 (hzL : zLower 20 q≤z) (hzU : z≤zUpper 20 q) (hw : 0≤w)
 (hwU : w≤3^54/((20:ℝ)^18*q^54)) : (reserveModel q z w).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hW : 0<3^54/((20:ℝ)^18*q^54) := by positivity
 have ht : 0≤w/(3^54/((20:ℝ)^18*q^54)) := div_nonneg hw hW.le
 have ht1 : w/(3^54/((20:ℝ)^18*q^54))≤1 := (div_le_one hW).mpr hwU
 have h0 : (reserveModel q z 0).PosDef := by
  have he : reserveModel q z 0=(3/(256*q^2)-3/(1024*q^3)) • model 0 1 := by
   ext i j
   dsimp only [reserveModel,model,Matrix.smul_apply,smul_eq_mul]
   rw [moment_eq_linearMoment _ _ _ (by omega)]
   ring
  rw [he]
  exact mass_model_posDef.smul (cubic_eighth_pos hq)
 have he : w=(1-w/(3^54/((20:ℝ)^18*q^54)))*0+
   (w/(3^54/((20:ℝ)^18*q^54)))*(3^54/((20:ℝ)^18*q^54)) := by
  field_simp [hW.ne']
  ring
 rw [he,model_affine_weight]
 exact convex_posDef h0 (gamma_interval_posDef hq hzL hzU) ht ht1

end p24

namespace p34

/-- The gamma endpoint moments after multiplication by the radial scale cubed. -/
def crossScaled (upper : Bool) : ℕ → ℝ → ℝ
 | 0, q => q^3/25+3*q^2/(2*(25:ℝ)^2)+3*q/(4*(25:ℝ)^3)-
    (if upper then 0 else 3/(8*(25:ℝ)^4))
 | n+1, q => q^(n+4)/25+((2*n+5:ℕ):ℝ)/(2*25)*crossScaled upper n q

/-- The signed moment comparison after clearing all positive radial powers. -/
def clearedMoment (upper : Bool) (q : ℝ) (k : ℕ) : ℝ :=
 (3*q^70/256-3*q^69/1024)*linearMoment (fun n => g n 0 1) k+
  (2*144*3^69/(20:ℝ)^23)*pairLinear (fun n => crossScaled upper n q) k

/-- Hankel matrix of the cleared pair comparison. -/
def clearedMatrix (upper : Bool) (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 fun i j => clearedMoment upper q (i.val+j.val)

theorem powerCoeff_expand (n : ℕ) (hn : n≤70) (y : ℝ) :
 (3*(1+y))^n=∑ d ∈ Finset.range 71, powerCoeff n d*y^d := by
 calc
  _ = ∑ d ∈ Finset.range (n+1), powerCoeff n d*y^d := by
   rw [mul_pow,add_comm (1:ℝ),add_pow,Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro d hd
   simp only [powerCoeff,one_pow,mul_one]
   ring
  _ = _ := by
   apply Finset.sum_subset (Finset.range_mono (by omega))
   intro d hd hdn
   have hnd : n<d := by simp only [Finset.mem_range] at hd hdn; omega
   simp only [powerCoeff,Nat.choose_eq_zero_of_lt hnd,Nat.cast_zero,zero_mul]

private def coeffEval (f : ℕ → ℝ) (y : ℝ) : ℝ :=
 ∑ d ∈ Finset.range 71, f d*y^d

private theorem coeffEval_add (f h : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => f d+h d) y=coeffEval f y+coeffEval h y := by
 simp only [coeffEval,add_mul,Finset.sum_add_distrib]

private theorem coeffEval_sub (f h : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => f d-h d) y=coeffEval f y-coeffEval h y := by
 simp only [coeffEval,sub_mul,Finset.sum_sub_distrib]

private theorem coeffEval_smul (c : ℝ) (f : ℕ → ℝ) (y : ℝ) :
 coeffEval (fun d => c*f d) y=c*coeffEval f y := by
 simp only [coeffEval,mul_assoc,Finset.mul_sum]

private theorem coeffEval_one (y : ℝ) :
 coeffEval (fun d => if d=0 then 1 else 0) y=1 := by
 simp [coeffEval]

private theorem coeffEval_power (n : ℕ) (hn : n≤70) (y : ℝ) :
 coeffEval (powerCoeff n) y=(3*(1+y))^n := (powerCoeff_expand n hn y).symm

private theorem crossCoeff_zero (upper : Bool) :
 crossCoeff 25 upper 0=fun d =>
  ((1/25)*powerCoeff 3 d+(3/(2*(25:ℝ)^2))*powerCoeff 2 d+(3/(4*(25:ℝ)^3))*powerCoeff 1 d)-
   (if upper then 0 else 3/(8*(25:ℝ)^4))*(if d=0 then 1 else 0) := by
 funext d
 simp only [crossCoeff]
 split_ifs <;> ring

private theorem crossCoeff_succ (upper : Bool) (n : ℕ) :
 crossCoeff 25 upper (n+1)=fun d => (1/25)*powerCoeff (n+4) d+
  (((2*n+5:ℕ):ℝ)/(2*25))*crossCoeff 25 upper n d := by
 funext d
 simp only [crossCoeff]
 ring

/-- Every scaled gamma endpoint is the binomial expansion of its radial polynomial. -/
theorem crossCoeff_expand (upper : Bool) (n : ℕ) (hn : n≤18) (y : ℝ) :
 crossScaled upper n (3*(1+y))=coeffEval (crossCoeff 25 upper n) y := by
 revert hn
 induction n with
 | zero =>
   intro hn
   rw [crossCoeff_zero,coeffEval_sub,coeffEval_add,coeffEval_add,
    coeffEval_smul,coeffEval_smul,coeffEval_smul,coeffEval_smul,
    coeffEval_power 3 (by norm_num),coeffEval_power 2 (by norm_num),
    coeffEval_power 1 (by norm_num),coeffEval_one]
   simp only [crossScaled]
   ring
 | succ n ih =>
   intro hn
   rw [crossCoeff_succ,coeffEval_add,coeffEval_smul,coeffEval_smul,
    coeffEval_power (n+4) (by omega),← ih (by omega)]
   simp only [crossScaled]
   ring

/-- Scaled pair moments have degree at most three above their power index. -/
theorem crossCoeff_eq_zero (upper : Bool) (n d : ℕ) (hd : n+3<d) :
 crossCoeff 25 upper n d=0 := by
 revert hd
 induction n with
 | zero =>
   intro hd
   have h3 : 3<d := by omega
   have h2 : 2<d := by omega
   have h1 : 1<d := by omega
   have h0 : d≠0 := by omega
   simp only [crossCoeff,powerCoeff,Nat.choose_eq_zero_of_lt h3,
    Nat.choose_eq_zero_of_lt h2,Nat.choose_eq_zero_of_lt h1,
    Nat.cast_zero,zero_mul,zero_div,mul_zero,add_zero,h0,ite_false]
   cases upper <;> norm_num
 | succ n ih =>
   intro hd
   rw [crossCoeff,ih (by omega)]
   simp only [powerCoeff,Nat.choose_eq_zero_of_lt (show n+4<d by omega),
    Nat.cast_zero,zero_mul,zero_div,mul_zero,add_zero]

private theorem pairLinear_coeffEval (upper : Bool) (y : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => coeffEval (crossCoeff 25 upper n) y) k=
  coeffEval (fun d => pairLinear (fun n => crossCoeff 25 upper n d) k) y := by
 rw [pairLinear_sum k hk]
 dsimp only [coeffEval]
 simp only [Finset.mul_sum]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro d hd
 rw [pairLinear_sum k hk,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro n hn
 ring

/-- Every coefficient above degree twenty-one contains only the positive mass reserve. -/
theorem pairLinear_crossCoeff_zero (upper : Bool) (d k : ℕ) (hd : 22≤d) (hk : k≤8) :
 pairLinear (fun n => crossCoeff 25 upper n d) k=0 := by
 rw [pairLinear_sum k hk]
 apply Finset.sum_eq_zero
 intro n hn
 have hn18 : n≤18 := by
  have hn19 := Finset.mem_range.mp hn
  omega
 rw [crossCoeff_eq_zero upper n d (by omega),mul_zero]

private theorem coefficientMatrix_endpoints_agree (d : ℕ) (hd : d≠0) :
 coefficientMatrix false d=coefficientMatrix true d := by
 ext i j
 dsimp only [coefficientMatrix,momentCoeff]
 have he : (fun n => crossCoeff 25 false n d)=(fun n => crossCoeff 25 true n d) :=
  funext (fun n => crossCoeff_endpoints_agree 25 n d hd)
 rw [he]

private theorem lower_coefficient_posDef (d : ℕ) (hd : d≤21) :
 (coefficientMatrix false d).PosDef := by
 interval_cases d
 · exact Lower0.coefficient_posDef
 · exact Lower1.coefficient_posDef
 · exact Lower2.coefficient_posDef
 · exact Lower3.coefficient_posDef
 · exact Lower4.coefficient_posDef
 · exact Lower5.coefficient_posDef
 · exact Lower6.coefficient_posDef
 · exact Lower7.coefficient_posDef
 · exact Lower8.coefficient_posDef
 · exact Lower9.coefficient_posDef
 · exact Lower10.coefficient_posDef
 · exact Lower11.coefficient_posDef
 · exact Lower12.coefficient_posDef
 · exact Lower13.coefficient_posDef
 · exact Lower14.coefficient_posDef
 · exact Lower15.coefficient_posDef
 · exact Lower16.coefficient_posDef
 · exact Lower17.coefficient_posDef
 · exact Lower18.coefficient_posDef
 · exact Lower19.coefficient_posDef
 · exact Lower20.coefficient_posDef
 · exact Lower21.coefficient_posDef

/-- Every coefficient of either normalized endpoint matrix is positive definite. -/
theorem coefficientMatrix_posDef (upper : Bool) (d : ℕ) (hd : d≤70) :
 (coefficientMatrix upper d).PosDef := by
 by_cases hlow : d≤21
 · cases upper with
   | false => exact lower_coefficient_posDef d hlow
   | true =>
     by_cases hz : d=0
     · subst d
       exact Upper0.coefficient_posDef
     · rw [← coefficientMatrix_endpoints_agree d hz]
       exact lower_coefficient_posDef d hlow
 · have hhigh : 22≤d := by omega
   have he : coefficientMatrix upper d=
     ((12*(Nat.choose 70 d:ℝ)-(Nat.choose 69 d:ℝ))/9216) • model 0 1 := by
    ext i j
    dsimp only [coefficientMatrix,momentCoeff,model,Matrix.smul_apply,smul_eq_mul]
    rw [pairLinear_crossCoeff_zero upper d (i.val+j.val) hhigh (by omega),
      mul_zero,add_zero,moment_eq_linearMoment _ _ _ (by omega)]
   rw [he]
   exact mass_model_posDef.smul (reserve_coefficient_pos 69 d hd)

private theorem pairLinear_crossScaled_expansion (upper : Bool) (y : ℝ)
 (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => crossScaled upper n (3*(1+y))) k=
  coeffEval (fun d => pairLinear (fun n => crossCoeff 25 upper n d) k) y := by
 rw [← pairLinear_coeffEval upper y k hk,
   pairLinear_sum k hk (fun n => crossScaled upper n (3*(1+y))),
   pairLinear_sum k hk (fun n => coeffEval (crossCoeff 25 upper n) y)]
 apply Finset.sum_congr rfl
 intro n hn
 have hn18 : n≤18 := by
  have hn19 := Finset.mem_range.mp hn
  omega
 rw [crossCoeff_expand upper n hn18 y]

private theorem clearedMoment_normalized_expansion (upper : Bool) (y : ℝ)
 (k : ℕ) (hk : k≤8) :
 clearedMoment upper (3*(1+y)) k=(3:ℝ)^72*coeffEval (fun d => momentCoeff upper d k) y := by
 have he : (fun d => momentCoeff upper d k)=
   (fun d => ((1/(768*3^70))*linearMoment (fun n => g n 0 1) k)*powerCoeff 70 d-
    ((1/(9216*3^69))*linearMoment (fun n => g n 0 1) k)*powerCoeff 69 d+
    (2*144/(27*(20:ℝ)^23))*pairLinear (fun n => crossCoeff 25 upper n d) k) := by
  funext d
  dsimp only [momentCoeff,powerCoeff]
  ring
 rw [he,coeffEval_add,coeffEval_sub,coeffEval_smul,coeffEval_smul,coeffEval_smul,
   coeffEval_power 70 (by norm_num),coeffEval_power 69 (by norm_num),
   ← pairLinear_crossScaled_expansion upper y k hk]
 generalize 3*(1+y)=q
 dsimp only [clearedMoment]
 ring

private theorem matrix_sum_apply {ι : Type} (s : Finset ι)
 (f : ι → Matrix (Fin 5) (Fin 5) ℝ) (i j : Fin 5) :
 (∑ d ∈ s, f d) i j=∑ d ∈ s, f d i j := by
 let ev : Matrix (Fin 5) (Fin 5) ℝ →+ ℝ :=
  { toFun := fun M => M i j
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
 exact map_sum ev f s

private theorem clearedMatrix_normalized_expansion (upper : Bool) (y : ℝ) :
 clearedMatrix upper (3*(1+y))=(3:ℝ)^72 •
  (∑ d ∈ Finset.range 71, y^d • coefficientMatrix upper d) := by
 ext i j
 simp only [clearedMatrix,Matrix.smul_apply,matrix_sum_apply,smul_eq_mul,coefficientMatrix]
 rw [clearedMoment_normalized_expansion upper y (i.val+j.val) (by omega)]
 congr 1
 dsimp only [coeffEval]
 exact Finset.sum_congr rfl (fun d _ => by ring)

private theorem weightedCoefficients_posDef (upper : Bool) (y : ℝ) (hy : 0≤y) :
 (∑ d ∈ Finset.range 71, y^d • coefficientMatrix upper d).PosDef := by
 have hs (n : ℕ) (hn : n≤70) :
   (∑ d ∈ Finset.range (n+1), y^d • coefficientMatrix upper d).PosDef := by
  revert hn
  induction n with
  | zero =>
    intro hn
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,one_smul,zero_add]
      using coefficientMatrix_posDef upper 0 (by norm_num)
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ]
    exact (ih (by omega)).add_posSemidef
      ((coefficientMatrix_posDef upper (n+1) hn).posSemidef.smul (pow_nonneg hy _))
 exact hs 70 le_rfl

/-- Both cleared gamma endpoint matrices are strict on the entire scale-three ray. -/
theorem clearedMatrix_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (clearedMatrix upper q).PosDef := by
 let y := q/3-1
 have hy : 0≤y := by dsimp only [y]; linarith only [hq]
 have he : q=3*(1+y) := by dsimp only [y]; ring
 rw [he,clearedMatrix_normalized_expansion]
 exact (weightedCoefficients_posDef upper y hy).smul (by positivity)

/-- The exact pair model with its allocated cubic gamma reserve. -/
def reserveModel (q z w : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 (3/(256*q^2)-3/(1024*q^3))*linearMoment (fun n => g n 0 1) (i.val+j.val)+
  (2*144)*w*pairLinear (fun n => gRate 25 n q z) (i.val+j.val)

private theorem crossScaled_eq (upper : Bool) (n : ℕ) {q : ℝ} (hq : q≠0) :
 crossScaled upper n q=q^3*gRate 25 n q (if upper then zUpper 25 q else zLower 25 q) := by
 induction n with
 | zero =>
   cases upper <;> simp only [crossScaled,gRate,zLower,zUpper,Bool.false_eq_true,ite_false,ite_true]
   all_goals (field_simp [hq] <;> simp only [mul_zero,sub_zero])
 | succ n ih =>
   simp only [crossScaled,gRate,ih]
   rw [show n+4=n+1+3 by omega,pow_add]
   ring

/-- Clearing the exponential and gamma denominators preserves the literal model. -/
theorem clearedMatrix_eq (upper : Bool) {q : ℝ} (hq : q≠0) :
 clearedMatrix upper q=q^72 • reserveModel q
   (if upper then zUpper 25 q else zLower 25 q) (3^69/((20:ℝ)^23*q^69)) := by
 ext i j
 dsimp only [clearedMatrix,clearedMoment,reserveModel,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => crossScaled upper n q)=
   (fun n => q^3*gRate 25 n q (if upper then zUpper 25 q else zLower 25 q)) from
   funext (fun n => crossScaled_eq upper n hq),pairLinear_smul _ _ _ (by omega)]
 field_simp [hq]

/-- Both extreme gamma masses fit the allocated first-atom correction. -/
theorem endpoint_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (reserveModel q (if upper then zUpper 25 q else zLower 25 q)
  (3^69/((20:ℝ)^23*q^69))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hp : (clearedMatrix upper q).PosDef := clearedMatrix_posDef upper hq
 rw [clearedMatrix_eq upper hq0.ne'] at hp
 have h := hp.smul (inv_pos.mpr (pow_pos hq0 72))
 simpa only [smul_smul,inv_mul_cancel₀ (pow_pos hq0 72).ne',one_smul] using h

private theorem model_affine_gamma (q a b t w : ℝ) :
 reserveModel q ((1-t)*a+t*b) w=
  (1-t) • reserveModel q a w+t • reserveModel q b w := by
 ext i j
 dsimp only [reserveModel,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => gRate 25 n q ((1-t)*a+t*b))=
   (fun n => (1-t)*gRate 25 n q a+t*gRate 25 n q b) from
   funext (gRate_affine 25 q a b t),pairLinear_affine _ _ _ _ (by omega)]
 ring

private theorem model_affine_weight (q z a b t : ℝ) :
 reserveModel q z ((1-t)*a+t*b)=
  (1-t) • reserveModel q z a+t • reserveModel q z b := by
 ext i j
 dsimp only [reserveModel,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 ring

private theorem convex_posDef {A B : Matrix (Fin 5) (Fin 5) ℝ}
 (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
 ((1-t) • A+t • B).PosDef := by
 by_cases hz : t=0
 · simpa only [hz,sub_zero,one_smul,zero_smul,add_zero] using hA
 have hp := (hB.smul (lt_of_le_of_ne ht (Ne.symm hz))).add_posSemidef
   (hA.posSemidef.smul (sub_nonneg.mpr ht1))
 simpa only [add_comm] using hp

/-- Every enclosed gamma mass is paid at the maximal polynomial weight. -/
theorem gamma_interval_posDef {q z : ℝ} (hq : 3≤q)
 (hzL : zLower 25 q≤z) (hzU : z≤zUpper 25 q) :
 (reserveModel q z (3^69/((20:ℝ)^23*q^69))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hd : 0<zUpper 25 q-zLower 25 q := by
  dsimp only [zLower,zUpper]
  ring_nf
  positivity
 have ht : 0≤(z-zLower 25 q)/(zUpper 25 q-zLower 25 q) :=
  div_nonneg (sub_nonneg.mpr hzL) hd.le
 have ht1 : (z-zLower 25 q)/(zUpper 25 q-zLower 25 q)≤1 := by
  apply (div_le_one hd).mpr
  linarith only [hzU]
 have he : z=(1-(z-zLower 25 q)/(zUpper 25 q-zLower 25 q))*zLower 25 q+
   ((z-zLower 25 q)/(zUpper 25 q-zLower 25 q))*zUpper 25 q := by
  field_simp [hd.ne']
  ring
 rw [he,model_affine_gamma]
 exact convex_posDef (endpoint_posDef false hq) (endpoint_posDef true hq) ht ht1

/-- The complete nonnegative weight interval fits the cubic gamma reserve. -/
theorem reserveModel_posDef {q z w : ℝ} (hq : 3≤q)
 (hzL : zLower 25 q≤z) (hzU : z≤zUpper 25 q) (hw : 0≤w)
 (hwU : w≤3^69/((20:ℝ)^23*q^69)) : (reserveModel q z w).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hW : 0<3^69/((20:ℝ)^23*q^69) := by positivity
 have ht : 0≤w/(3^69/((20:ℝ)^23*q^69)) := div_nonneg hw hW.le
 have ht1 : w/(3^69/((20:ℝ)^23*q^69))≤1 := (div_le_one hW).mpr hwU
 have h0 : (reserveModel q z 0).PosDef := by
  have he : reserveModel q z 0=(3/(256*q^2)-3/(1024*q^3)) • model 0 1 := by
   ext i j
   dsimp only [reserveModel,model,Matrix.smul_apply,smul_eq_mul]
   rw [moment_eq_linearMoment _ _ _ (by omega)]
   ring
  rw [he]
  exact mass_model_posDef.smul (cubic_eighth_pos hq)
 have he : w=(1-w/(3^69/((20:ℝ)^23*q^69)))*0+
   (w/(3^69/((20:ℝ)^23*q^69)))*(3^69/((20:ℝ)^23*q^69)) := by
  field_simp [hW.ne']
  ring
 rw [he,model_affine_weight]
 exact convex_posDef h0 (gamma_interval_posDef hq hzL hzU) ht ht1

end p34

end GaloisForLFunctions.ThetaCuspSections.FifthOtherTail
