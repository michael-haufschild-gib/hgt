import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.Words

/-! # Raising the contact order of an exponential word by one -/
open NormedSpace Set
namespace GaloisForLFunctions.HTGeometry.ProductFormula
noncomputable section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Entire divisibility of the error by the indicated power of time. -/
def Contact (p : ℕ) (w : List A) (x : A) : Prop :=
  ∃ E : ℂ → A, Differentiable ℂ E ∧ ∀ z, word w z - exp (z • x) = z^p • E z

private theorem divide_zero (f : ℂ → A) (hf : Differentiable ℂ f) (h0 : f 0 = 0) :
    Differentiable ℂ (dslope f 0) ∧ ∀ z : ℂ, z • dslope f 0 z = f z := by
  refine ⟨differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := univ)
    (by simp)).mpr hf.differentiableOn),fun z => ?_⟩
  simpa only [sub_zero,h0] using sub_smul_dslope f 0 z

theorem flow_entire (x : A) : Differentiable ℂ (fun z : ℂ => exp (z • x)) :=
  fun z => (hasDerivAt_exp_smul_const x z).differentiableAt

/-- The ordered product and the exponential of the sum have the same tangent. -/
theorem contact_two (w : List A) : Contact 2 w w.sum := by
  let f (z : ℂ) := word w z - exp (z • w.sum)
  obtain ⟨hd,h⟩ := divide_zero f ((word_entire w).sub (flow_entire _)) (by simp [f])
  have hder : HasDerivAt f 0 0 := by
    simpa only [f,Pi.sub_def,zero_smul,exp_zero,one_mul,sub_self] using
      (word_derivative_zero w).sub (hasDerivAt_exp_smul_const w.sum (0:ℂ))
  obtain ⟨hdd,hh⟩ := divide_zero (dslope f 0) hd (by rw [dslope_same,hder.deriv])
  refine ⟨_,hdd,fun z => ?_⟩
  change f z = _
  rw [← h z,← hh z,smul_smul,pow_two]

/-- Two positive forward steps cancel one reversed leading error. -/
theorem exists_weights (p : ℕ) (hp : 2 ≤ p) :
    ∃ a b : ℝ, 1 ≤ a ∧ a ≤ 2 ∧ 1 ≤ b ∧ b ≤ 3 ∧ 2*a = 1+b ∧ 2*a^p=b^p := by
  have hpow : 2*(2:ℝ)^p ≤ 3^p := by
    induction p, hp using Nat.le_induction with
    | base => norm_num
    | succ n hn ih => rw [pow_succ,pow_succ]; nlinarith only [ih,show 0 ≤ (3:ℝ)^n by positivity]
  let f (x : ℝ) := 2*x^p - (2*x-1)^p
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hz : (0:ℝ) ∈ Icc (f 2) (f 1) := by
    constructor
    · dsimp [f]; norm_num only [show (2:ℝ)*2-1=3 by norm_num]; exact sub_nonpos.mpr hpow
    · norm_num [f]
  obtain ⟨a,ha,he⟩ := intermediate_value_Icc' (show (1:ℝ)≤2 by norm_num) hf.continuousOn hz
  exact ⟨a,2*a-1,ha.1,ha.2,by linarith [ha.1],by linarith [ha.2],by ring,sub_eq_zero.mp he⟩

/-- Two forward copies followed by a reversed copy of the input word. -/
def raised (w : List A) (a b : ℝ) := scaleWord a w ++ scaleWord a w ++ scaleWord (-b) w.reverse

theorem contact_raised {p : ℕ} {w : List A} {x : A} (h : Contact p w x)
    {a b : ℝ} (ht : 2*a=1+b) (hc : 2*a^p=b^p) : Contact (p+1) (raised w a b) x := by
  obtain ⟨E,hE,he⟩ := h
  let S := word w
  let U (z : ℂ) := exp (z • x)
  let T (z : ℂ) := word w.reverse (-(b:ℂ)*z)
  let V (c : ℝ) (z : ℂ) := (c:ℂ)^p • E ((c:ℂ)*z)
  let L (z : ℂ) := (V a z*S ((a:ℂ)*z) + U ((a:ℂ)*z)*V a z - U z*V b z)*T z
  have hlin (c : ℂ) : Differentiable ℂ (fun z : ℂ => c*z) := differentiable_id.const_mul c
  have hV c : Differentiable ℂ (V c) := (hE.comp (hlin c)).const_smul ((c:ℂ)^p)
  have hU := flow_entire x
  have hL : Differentiable ℂ L := by
    exact ((((hV a).mul ((word_entire w).comp (hlin a))).add
      ((hU.comp (hlin a)).mul (hV a))).sub (hU.mul (hV b))).mul ((word_entire w.reverse).comp (hlin _))
  have hc' : (a:ℂ)^p+(a:ℂ)^p=(b:ℂ)^p := by exact_mod_cast (show a^p+a^p=b^p by linarith only [hc])
  have hL0 : L 0 = 0 := by simp [L,V,S,U,T,← add_smul,hc']
  obtain ⟨hD,hdiv⟩ := divide_zero L hL hL0
  refine ⟨_,hD,fun z => ?_⟩
  have hres (c : ℝ) : S ((c:ℂ)*z) - U ((c:ℂ)*z) = z^p • V c z := by
    rw [he,mul_pow,mul_comm,← smul_smul]
  have ht' : (2:ℂ)*a=1+b := by exact_mod_cast ht
  have hadd : U ((a:ℂ)*z) * U ((a:ℂ)*z) = U z * U ((b:ℂ)*z) := by
    dsimp only [U]; rw [flow_add,flow_add]
    congr 2
    linear_combination z*ht'
  have hinv : S ((b:ℂ)*z)*T z = 1 := by
    simpa only [S,T,neg_mul] using word_mul_reverse w ((b:ℂ)*z)
  have hstep : (S ((a:ℂ)*z)*S ((a:ℂ)*z) - U z*S ((b:ℂ)*z)) =
      z^p • (V a z*S ((a:ℂ)*z) + U ((a:ℂ)*z)*V a z - U z*V b z) := by
    rw [smul_sub,smul_add,← smul_mul_assoc,← mul_smul_comm,← mul_smul_comm,← hres,← hres]
    rw [sub_mul,mul_sub,mul_sub,hadd]
    abel
  change word (raised w a b) z - U z = _
  simp only [raised,word_append,word_scale,Complex.ofReal_neg]
  change (S ((a:ℂ)*z)*S ((a:ℂ)*z))*T z - U z = _
  calc
    _ = (S ((a:ℂ)*z)*S ((a:ℂ)*z) - U z*S ((b:ℂ)*z))*T z := by rw [sub_mul,mul_assoc (U z),hinv,mul_one]
    _ = z^p • L z := by rw [hstep,smul_mul_assoc]
    _ = _ := by rw [← hdiv z,smul_smul,pow_succ]

end
end GaloisForLFunctions.HTGeometry.ProductFormula
