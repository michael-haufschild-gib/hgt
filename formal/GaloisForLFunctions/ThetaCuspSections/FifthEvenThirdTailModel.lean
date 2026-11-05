import GaloisForLFunctions.ThetaCuspSections.FifthEvenThirdTailCoefficients
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTailRateMoments
/-!
# Gamma-reserve payment for theta atoms one and three

A twenty-four-power exponential envelope reduces the two gamma endpoints
to polynomial matrices in `q/3-1`. Each coefficient is positive definite;
the exact expansion and convexity recover the complete rate-ten model.
-/
noncomputable section
open Matrix
namespace GaloisForLFunctions.ThetaCuspSections.FifthThirdTail
open FifthAtomTail FifthLeadingPair FifthRateTail

theorem powerCoeff_expand (n : ℕ) (hn : n≤26) (y : ℝ) :
 (3*(1+y))^n=∑ d ∈ Finset.range 27, powerCoeff n d*y^d := by
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
 ∑ d ∈ Finset.range 27, f d*y^d

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

private theorem coeffEval_power (n : ℕ) (hn : n≤26) (y : ℝ) :
 coeffEval (powerCoeff n) y=(3*(1+y))^n := (powerCoeff_expand n hn y).symm

private theorem crossCoeff_zero (upper : Bool) :
 crossCoeff upper 0=fun d =>
  ((1/10)*powerCoeff 3 d+(3/200)*powerCoeff 2 d+(3/4000)*powerCoeff 1 d)-
   (if upper then 0 else 3/80000)*(if d=0 then 1 else 0) := by
 funext d
 simp only [crossCoeff]
 split_ifs <;> ring

private theorem crossCoeff_succ (upper : Bool) (n : ℕ) :
 crossCoeff upper (n+1)=fun d => (1/10)*powerCoeff (n+4) d+
  (((2*n+5:ℕ):ℝ)/20)*crossCoeff upper n d := by
 funext d
 simp only [crossCoeff]
 ring

/-- Every scaled gamma endpoint is the binomial expansion of its radial polynomial. -/
theorem crossCoeff_expand (upper : Bool) (n : ℕ) (hn : n≤18) (y : ℝ) :
 crossScaled upper n (3*(1+y))=coeffEval (crossCoeff upper n) y := by
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

/-- Scaled rate-ten moments have degree at most three above their power index. -/
theorem crossCoeff_eq_zero (upper : Bool) (n d : ℕ) (hd : n+3<d) :
 crossCoeff upper n d=0 := by
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

private theorem thirdLinear_coeffEval (upper : Bool) (y : ℝ) (k : ℕ) (hk : k≤8) :
 thirdLinear (fun n => coeffEval (crossCoeff upper n) y) k=
  coeffEval (fun d => thirdLinear (fun n => crossCoeff upper n d) k) y := by
 rw [thirdLinear_sum k hk]
 dsimp only [coeffEval]
 simp only [Finset.mul_sum]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro d hd
 rw [thirdLinear_sum k hk,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro n hn
 ring

/-- Every coefficient above degree twenty-one contains only the positive mass reserve. -/
theorem thirdLinear_crossCoeff_zero (upper : Bool) (d k : ℕ) (hd : 22≤d) (hk : k≤8) :
 thirdLinear (fun n => crossCoeff upper n d) k=0 := by
 rw [thirdLinear_sum k hk]
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
 have he : (fun n => crossCoeff false n d)=(fun n => crossCoeff true n d) :=
  funext (fun n => crossCoeff_endpoints_agree n d hd)
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
theorem coefficientMatrix_posDef (upper : Bool) (d : ℕ) (hd : d≤26) :
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
   have he : coefficientMatrix upper d=((1/8)*(Nat.choose 26 d:ℝ)) • model 0 1 := by
    ext i j
    dsimp only [coefficientMatrix,momentCoeff,model,Matrix.smul_apply,smul_eq_mul]
    rw [thirdLinear_crossCoeff_zero upper d (i.val+j.val) hhigh (by omega),
      mul_zero,add_zero,moment_eq_linearMoment _ _ _ (by omega)]
   rw [he]
   have hc : (0:ℝ)<(Nat.choose 26 d:ℝ) := by exact_mod_cast Nat.choose_pos hd
   exact mass_model_posDef.smul (mul_pos (by norm_num) hc)

private theorem thirdLinear_crossScaled_expansion (upper : Bool) (y : ℝ)
 (k : ℕ) (hk : k≤8) :
 thirdLinear (fun n => crossScaled upper n (3*(1+y))) k=
  coeffEval (fun d => thirdLinear (fun n => crossCoeff upper n d) k) y := by
 rw [← thirdLinear_coeffEval upper y k hk,
   thirdLinear_sum k hk (fun n => crossScaled upper n (3*(1+y))),
   thirdLinear_sum k hk (fun n => coeffEval (crossCoeff upper n) y)]
 apply Finset.sum_congr rfl
 intro n hn
 have hn18 : n≤18 := by
  have hn19 := Finset.mem_range.mp hn
  omega
 rw [crossCoeff_expand upper n hn18 y]

private theorem clearedMoment_normalized_expansion (upper : Bool) (y : ℝ)
 (k : ℕ) (hk : k≤8) :
 clearedMoment upper (3*(1+y)) k=(3:ℝ)^27*coeffEval (fun d => momentCoeff upper d k) y := by
 have he : (fun d => momentCoeff upper d k)=
   (fun d => ((1/(8*3^26))*linearMoment (fun n => g n 0 1) k)*powerCoeff 26 d+
    (18/(27*(20:ℝ)^8))*thirdLinear (fun n => crossCoeff upper n d) k) := by
  funext d
  dsimp only [momentCoeff,powerCoeff]
  ring
 rw [he,coeffEval_add,coeffEval_smul,coeffEval_smul,
   coeffEval_power 26 (by norm_num),← thirdLinear_crossScaled_expansion upper y k hk]
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
 clearedMatrix upper (3*(1+y))=(3:ℝ)^27 •
  (∑ d ∈ Finset.range 27, y^d • coefficientMatrix upper d) := by
 ext i j
 simp only [clearedMatrix,Matrix.smul_apply,matrix_sum_apply,smul_eq_mul,coefficientMatrix]
 rw [clearedMoment_normalized_expansion upper y (i.val+j.val) (by omega)]
 congr 1
 dsimp only [coeffEval]
 exact Finset.sum_congr rfl (fun d _ => by ring)

private theorem weightedCoefficients_posDef (upper : Bool) (y : ℝ) (hy : 0≤y) :
 (∑ d ∈ Finset.range 27, y^d • coefficientMatrix upper d).PosDef := by
 have hs (n : ℕ) (hn : n≤26) :
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
 exact hs 26 le_rfl

/-- Both cleared gamma endpoint matrices are strict on the entire scale-three ray. -/
theorem clearedMatrix_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (clearedMatrix upper q).PosDef := by
 let y := q/3-1
 have hy : 0≤y := by dsimp only [y]; linarith only [hq]
 have he : q=3*(1+y) := by dsimp only [y]; ring
 rw [he,clearedMatrix_normalized_expansion]
 exact (weightedCoefficients_posDef upper y hy).smul (by positivity)

/-- The exact pair model with its allocated first-atom gamma correction. -/
def reserveModel (q z w : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 (3/(8*q))*linearMoment (fun n => g n 0 1) (i.val+j.val)+
  18*w*thirdLinear (fun n => gRate 10 n q z) (i.val+j.val)

private theorem crossScaled_eq (upper : Bool) (n : ℕ) {q : ℝ} (hq : q≠0) :
 crossScaled upper n q=q^3*gRate 10 n q (if upper then zUpper 10 q else zLower 10 q) := by
 induction n with
 | zero =>
   cases upper <;> simp only [crossScaled,gRate,zLower,zUpper,Bool.false_eq_true,ite_false,ite_true]
   all_goals (field_simp [hq]; ring)
 | succ n ih =>
   simp only [crossScaled,gRate,ih]
   rw [show n+4=n+1+3 by omega,pow_add]
   ring

/-- Clearing the exponential and gamma denominators preserves the literal model. -/
theorem clearedMatrix_eq (upper : Bool) {q : ℝ} (hq : q≠0) :
 clearedMatrix upper q=q^27 • reserveModel q
   (if upper then zUpper 10 q else zLower 10 q) (3^24/((20:ℝ)^8*q^24)) := by
 ext i j
 dsimp only [clearedMatrix,clearedMoment,reserveModel,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => crossScaled upper n q)=
   (fun n => q^3*gRate 10 n q (if upper then zUpper 10 q else zLower 10 q)) from
   funext (fun n => crossScaled_eq upper n hq),thirdLinear_smul _ _ _ (by omega)]
 field_simp [hq]

/-- Both extreme gamma masses fit the allocated first-atom correction. -/
theorem endpoint_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (reserveModel q (if upper then zUpper 10 q else zLower 10 q)
  (3^24/((20:ℝ)^8*q^24))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hp : (clearedMatrix upper q).PosDef := clearedMatrix_posDef upper hq
 rw [clearedMatrix_eq upper hq0.ne'] at hp
 have h := hp.smul (inv_pos.mpr (pow_pos hq0 27))
 simpa only [smul_smul,inv_mul_cancel₀ (pow_pos hq0 27).ne',one_smul] using h

private theorem model_affine_gamma (q a b t w : ℝ) :
 reserveModel q ((1-t)*a+t*b) w=
  (1-t) • reserveModel q a w+t • reserveModel q b w := by
 ext i j
 dsimp only [reserveModel,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => gRate 10 n q ((1-t)*a+t*b))=
   (fun n => (1-t)*gRate 10 n q a+t*gRate 10 n q b) from
   funext (gRate_affine 10 q a b t),thirdLinear_affine _ _ _ _ (by omega)]
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
 (hzL : zLower 10 q≤z) (hzU : z≤zUpper 10 q) :
 (reserveModel q z (3^24/((20:ℝ)^8*q^24))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hd : 0<zUpper 10 q-zLower 10 q := by
  dsimp only [zLower,zUpper]
  ring_nf
  positivity
 have ht : 0≤(z-zLower 10 q)/(zUpper 10 q-zLower 10 q) :=
  div_nonneg (sub_nonneg.mpr hzL) hd.le
 have ht1 : (z-zLower 10 q)/(zUpper 10 q-zLower 10 q)≤1 := by
  apply (div_le_one hd).mpr
  linarith only [hzU]
 have he : z=(1-(z-zLower 10 q)/(zUpper 10 q-zLower 10 q))*zLower 10 q+
   ((z-zLower 10 q)/(zUpper 10 q-zLower 10 q))*zUpper 10 q := by
  field_simp [hd.ne']
  ring
 rw [he,model_affine_gamma]
 exact convex_posDef (endpoint_posDef false hq) (endpoint_posDef true hq) ht ht1

/-- The complete nonnegative weight interval fits the first gamma correction. -/
theorem reserveModel_posDef {q z w : ℝ} (hq : 3≤q)
 (hzL : zLower 10 q≤z) (hzU : z≤zUpper 10 q) (hw : 0≤w)
 (hwU : w≤3^24/((20:ℝ)^8*q^24)) : (reserveModel q z w).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hW : 0<3^24/((20:ℝ)^8*q^24) := by positivity
 have ht : 0≤w/(3^24/((20:ℝ)^8*q^24)) := div_nonneg hw hW.le
 have ht1 : w/(3^24/((20:ℝ)^8*q^24))≤1 := (div_le_one hW).mpr hwU
 have h0 : (reserveModel q z 0).PosDef := by
  have he : reserveModel q z 0=(3/(8*q)) • model 0 1 := by
   ext i j
   dsimp only [reserveModel,model,Matrix.smul_apply,smul_eq_mul]
   rw [moment_eq_linearMoment _ _ _ (by omega)]
   ring
  rw [he]
  exact mass_model_posDef.smul (by positivity)
 have he : w=(1-w/(3^24/((20:ℝ)^8*q^24)))*0+
   (w/(3^24/((20:ℝ)^8*q^24)))*(3^24/((20:ℝ)^8*q^24)) := by
  field_simp [hW.ne']
  ring
 rw [he,model_affine_weight]
 exact convex_posDef h0 (gamma_interval_posDef hq hzL hzU) ht ht1

end GaloisForLFunctions.ThetaCuspSections.FifthThirdTail
