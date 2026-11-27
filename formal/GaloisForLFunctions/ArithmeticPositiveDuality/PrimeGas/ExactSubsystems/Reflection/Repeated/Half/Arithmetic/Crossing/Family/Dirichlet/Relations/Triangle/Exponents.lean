import GaloisForLFunctions.RHTower.SixExponentials.Main

/-! # Six exponentials and common fields of radical powers -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real Set IntermediateField
open scoped IntermediateField

/-- The complex scalar recording a real energy gap at order v. -/
def gapExp (E v : ℝ) : ℂ := (exp (v*E) : ℝ)

def algebraicPair (E F v : ℝ) : Prop := IsAlgebraic ℚ (gapExp E v) ∧ IsAlgebraic ℚ (gapExp F v)

def independentGaps (E F : ℝ) : Prop := ∀ i j : ℤ, (i : ℝ)*E+(j : ℝ)*F=0 → i=0 ∧ j=0

private theorem rational_relation (v : ℝ) (rat : ¬Irrational v) (w : ℝ) :
    ∃ (n : ℕ) (i j : ℤ), 0<n ∧ (n : ℝ)*v=(i : ℝ)+(j : ℝ)*w := by
  obtain ⟨q,rfl⟩ := exists_rat_of_not_irrational rat
  refine ⟨q.den,q.num,0,q.den_pos,?_⟩
  rw [Int.cast_zero,zero_mul,add_zero,Rat.cast_def,mul_div_cancel₀ _ (Nat.cast_pos.mpr q.den_pos : 0<(q.den : ℝ)).ne']

private theorem pair_with_one {w : ℝ} (irr : Irrational w) {i j : ℤ}
    (eq : (i : ℝ)+(j : ℝ)*w=0) : i=0 ∧ j=0 := by
  by_cases hz : j=0
  · rw [hz,Int.cast_zero,zero_mul,add_zero] at eq
    exact ⟨Int.cast_eq_zero.mp eq,hz⟩
  · apply False.elim
    apply irr
    refine ⟨-(i : ℚ)/j,?_⟩
    rw [Rat.cast_div,Rat.cast_neg,Rat.cast_intCast,Rat.cast_intCast,div_eq_iff (Int.cast_ne_zero.mpr hz)]
    linarith only [eq,mul_comm (j : ℝ) w]

/-- If 1,w,v all give algebraic pairs, six exponentials supplies an integer
relation. Irrationality of w makes the coefficient of v nonzero. -/
private theorem denominator {E F w v : ℝ} (ind : independentGaps E F)
    (one : algebraicPair E F 1) (wAlg : algebraicPair E F w) (vAlg : algebraicPair E F v)
    (irr : Irrational w) : ∃ (n : ℕ) (i j : ℤ), 0<n ∧ (n : ℝ)*v=(i : ℝ)+(j : ℝ)*w := by
  have row (i j : ℤ) (h : (i : ℂ)*(E : ℂ)+(j : ℂ)*(F : ℂ)=0) : i=0 ∧ j=0 := by
    apply ind i j
    exact_mod_cast h
  have matrix : ∀ i : Fin 2, ∀ j : Fin 3,
      IsAlgebraic ℚ (Complex.exp (![↑E,↑F] i * ![(1 : ℂ),↑w,↑v] j)) := by
    have ex (A x : ℝ) : Complex.exp ((A : ℂ)*(x : ℂ))=gapExp A x := by
      rw [gapExp,Complex.ofReal_exp,Complex.ofReal_mul,mul_comm]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
        Matrix.tail_cons,Fin.mk_one,Fin.isValue,Fin.reduceFinMk]
    · simpa only [← Complex.ofReal_one,ex] using one.1
    · rw [ex]; exact wAlg.1
    · rw [ex]; exact vAlg.1
    · simpa only [← Complex.ofReal_one,ex] using one.2
    · rw [ex]; exact wAlg.2
    · rw [ex]; exact vAlg.2
  have dep := mt (GaloisForLFunctions.RHTower.SixExponentials.six_exponentials row) (not_not.mpr matrix)
  push Not at dep
  obtain ⟨i,j,k,eq,notall⟩ := dep
  have realEq : (i : ℝ)+(j : ℝ)*w+(k : ℝ)*v=0 := by
    rw [mul_one] at eq
    exact_mod_cast eq
  have nz : k ≠ 0 := by
    intro zero
    rw [zero,Int.cast_zero,zero_mul,add_zero] at realEq
    obtain ⟨hi,hj⟩ := pair_with_one irr realEq
    simp_all
  cases k with
  | ofNat n =>
    refine ⟨n,-i,-j,Nat.pos_of_ne_zero (fun h => nz (by rw [h]; rfl)),?_⟩
    change (i : ℝ)+(j : ℝ)*w+(n : ℝ)*v=0 at realEq
    simp only [Int.cast_neg]
    linarith only [realEq]
  | negSucc n =>
    refine ⟨n+1,i,j,Nat.succ_pos n,?_⟩
    push_cast at realEq ⊢
    linarith only [realEq]

private theorem field_for_pair (E F w : ℝ) (one : algebraicPair E F 1) (hw : algebraicPair E F w) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧
      gapExp E 1 ∈ K ∧ gapExp F 1 ∈ K ∧ gapExp E w ∈ K ∧ gapExp F w ∈ K := by
  classical
  let S : Finset ℂ := {gapExp E 1,gapExp F 1,gapExp E w,gapExp F w}
  let K := IntermediateField.adjoin ℚ (↑S : Set ℂ)
  have integral : ∀ z ∈ (↑S : Set ℂ), IsIntegral ℚ z := by
    intro z hz
    simp only [S,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    exacts [one.1.isIntegral,one.2.isIntegral,hw.1.isIntegral,hw.2.isIntegral]
  refine ⟨K,IntermediateField.finiteDimensional_adjoin integral,?_⟩
  have inc : ∀ z ∈ S, z ∈ K := fun _ hz => IntermediateField.subset_adjoin ℚ (↑S : Set ℂ) hz
  exact ⟨inc _ (by simp [S]),inc _ (by simp [S]),inc _ (by simp [S]),inc _ (by simp [S])⟩

private theorem power_mem (K : IntermediateField ℚ ℂ) (E w v : ℝ)
    (base : gapExp E 1 ∈ K) (second : gapExp E w ∈ K) (n : ℕ) (i j : ℤ)
    (eq : (n : ℝ)*v=(i : ℝ)+(j : ℝ)*w) : (gapExp E v)^n ∈ K := by
  have ex : (gapExp E v)^n=(gapExp E 1)^i*(gapExp E w)^j := by
    simp only [gapExp,Complex.ofReal_exp,← Complex.exp_nat_mul,← Complex.exp_int_mul,
      ← Complex.exp_add,one_mul,Complex.ofReal_mul]
    apply congrArg Complex.exp
    have rel : (n : ℂ)*(v : ℂ)=(i : ℂ)+(j : ℂ)*(w : ℂ) := by exact_mod_cast eq
    linear_combination (E : ℂ)*rel
  rw [ex]
  exact K.mul_mem (K.pow_mem base _) (K.pow_mem second _)

/-- A fixed number field contains positive integral powers of both coordinates
of every algebraic pair. The exponent can depend on the pair. -/
theorem common_radical_field {E F : ℝ} (ind : independentGaps E F) (one : algebraicPair E F 1) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ ∀ v : ℝ, algebraicPair E F v →
      ∃ n : ℕ, 0<n ∧ (gapExp E v)^n ∈ K ∧ (gapExp F v)^n ∈ K := by
  have witness : ∃ w : ℝ, algebraicPair E F w ∧ ∀ v, algebraicPair E F v →
      ∃ (n : ℕ) (i j : ℤ), 0<n ∧ (n : ℝ)*v=(i : ℝ)+(j : ℝ)*w := by
    by_cases extra : ∃ w, algebraicPair E F w ∧ Irrational w
    · obtain ⟨w,hw,irr⟩ := extra
      exact ⟨w,hw,fun _ hv => denominator ind one hw hv irr⟩
    · exact ⟨1,one,fun v hv => rational_relation v (fun irr => extra ⟨v,hv,irr⟩) 1⟩
  obtain ⟨w,hw,den⟩ := witness
  obtain ⟨K,f,e₁,f₁,ew,fw⟩ := field_for_pair E F w one hw
  refine ⟨K,f,fun v hv => ?_⟩
  obtain ⟨n,i,j,hn,eq⟩ := den v hv
  exact ⟨n,hn,power_mem K E w v e₁ ew n i j eq,power_mem K F w v f₁ fw n i j eq⟩

#print axioms common_radical_field

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
