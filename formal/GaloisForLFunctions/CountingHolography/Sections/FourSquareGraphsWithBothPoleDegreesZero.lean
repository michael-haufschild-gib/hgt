import GaloisForLFunctions.CountingHolography.Sections.TwoPoleFreeIntegerTranslates

/-!
# Four square graphs with both pole degrees zero

The square-root conductors a, b, sa, sb have signs 1, −2, −2, 1.
Reciprocal reflection exchanges the extreme graphs and the middle graphs.
The choice a = 2n, b = 4n+3, s = 2(n+1) cancels both pole moments exactly.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology RenormalizedIntersectionTheory ArithmeticOrientationGeometry ArithmeticScatteringHolography

/-- Present a signed divisor by graph labels, including repeated labels. -/
def integralGraphSum {ι : Type*} [Fintype ι] {N : ℕ} (v : ι → Fin N) (c : ι → ℤ) : Fin N → ℤ :=
  ∑ i, Pi.single (v i) (c i)

theorem sum_integralGraphSum {ι : Type*} [Fintype ι] {N : ℕ} (v : ι → Fin N) (c : ι → ℤ) (f : Fin N → ℝ) :
    ∑ j, f j*(integralGraphSum v c j:ℝ) = ∑ i, f (v i)*(c i:ℝ) := by
  simp only [integralGraphSum,Finset.sum_apply,Int.cast_sum,mul_sum]
  rw [sum_comm]
  simp only [Pi.single_apply,Int.cast_ite,Int.cast_zero,mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true]

theorem integralGraphSum_mass {ι : Type*} [Fintype ι] {N : ℕ} (v : ι → Fin N) (c : ι → ℤ) :
    ∑ j, |(integralGraphSum v c j:ℝ)| ≤ ∑ i, |(c i:ℝ)| := by
  simp only [integralGraphSum,Finset.sum_apply,Int.cast_sum]
  refine (sum_le_sum fun j _ => abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  rw [sum_comm]
  simp only [Pi.single_apply,Int.cast_ite,Int.cast_zero,apply_ite abs,abs_zero,sum_ite_eq',mem_univ,if_true]

/-- Pull the Gram matrix back to the finite set of labels before summing. -/
theorem integerProbe_integralGraphSum {ι : Type*} [Fintype ι] {N : ℕ} (v : ι → Fin N) (c : ι → ℤ) :
    integerProbe N (integralGraphSum v c) = ∑ i, (∑ j, realSplineTrace
      (Real.log ((v i:ℝ)+1)-Real.log ((v j:ℝ)+1))*(c j:ℝ))*(c i:ℝ) := by
  let a := integralGraphSum v c
  let R (i : Fin N) := ∑ j, (atomGram N i (v j)).re*(c j:ℝ)
  have row (i : Fin N) : (∑ j, (atomGram N i j).re*(a i:ℝ)*(a j:ℝ)) = R i*(a i:ℝ) := by
    have he : R i = ∑ j, (atomGram N i j).re*(a j:ℝ) :=
      (sum_integralGraphSum v c fun j => (atomGram N i j).re).symm
    rw [he,sum_mul]
    exact sum_congr rfl fun j _ => mul_right_comm _ _ _
  change integerProbe N a = _
  rw [integerProbe_eq_sum]
  simp_rw [row]
  rw [sum_integralGraphSum v c R]
  simp only [R,realSplineTrace,atomGram_eq_splineSeries]

/-- For one negative graph of multiplicity B, normalize all positive
square-root conductors by its square-root conductor. The deficit in total
positive multiplicity is exactly a sum of positive squared displacements. -/
theorem singleton_pole_dispersion {ι : Type*} [Fintype ι] (c : ι → ℕ) (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) {B : ℝ} (hp : ∑ i, (c i:ℝ)*x i = B)
    (hm : ∑ i, (c i:ℝ)/x i = B) :
    ∑ i, (c i:ℝ)*(x i-1)^2/(2*x i) = B-∑ i, (c i:ℝ) := by
  have he (i : ι) : (c i:ℝ)*(x i-1)^2/(2*x i) =
      ((c i:ℝ)*x i+(c i:ℝ)/x i)/2-(c i:ℝ) := by field_simp [(hx i).ne'] <;> ring
  simp_rw [he]
  rw [sum_sub_distrib,← sum_div,sum_add_distrib,hp,hm]
  ring

/-- Each positive graph lies within multiplicative distance B of the
single negative graph when the two pole moments agree. -/
theorem singleton_pole_conductor_bounds {ι : Type*} [Fintype ι] (c : ι → ℕ) (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) {B : ℝ} (hp : ∑ i, (c i:ℝ)*x i = B)
    (hm : ∑ i, (c i:ℝ)/x i = B) {i : ι} (hi : 0 < c i) :
    x i ≤ B ∧ 1 ≤ B*x i := by
  have h₁ : (c i:ℝ)*x i ≤ B := (single_le_sum (s := univ) (f := fun j => (c j:ℝ)*x j)
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hx j).le) (mem_univ i)).trans_eq hp
  have h₂ : (c i:ℝ)/x i ≤ B := (single_le_sum (s := univ) (f := fun j => (c j:ℝ)/x j)
    (fun j _ => div_nonneg (Nat.cast_nonneg _) (hx j).le) (mem_univ i)).trans_eq hm
  have hc : 1 ≤ (c i:ℝ) := by exact_mod_cast hi
  exact ⟨(le_mul_of_one_le_left (hx i).le hc).trans h₁,hc.trans ((div_le_iff₀ (hx i)).mp h₂)⟩

private def roots (n : ℕ) : Fin 4 → ℕ :=
  let a := 2*n
  let b := 4*n+3
  let s := 2*(n+1)
  ![a,b,s*a,s*b]

private def coeff : Fin 4 → ℤ := ![1,-2,-2,1]

private theorem weightedFourSum (f : Fin 4 → ℝ) :
    (∑ i, f i*(coeff i:ℝ)) = f 0-2*f 1-2*f 2+f 3 := by
  rw [Fin.sum_univ_four]
  change f 0*(1:ℤ)+f 1*(-2:ℤ)+f 2*(-2:ℤ)+f 3*(1:ℤ) = _
  push_cast
  ring

def fourSquareHorizon (n : ℕ) := (∑ i, (roots n i)^2)+1

private def label (n : ℕ) (i : Fin 4) : Fin (fourSquareHorizon n) :=
  ⟨(roots n i)^2-1,by
    have h := single_le_sum (s := univ) (f := fun j => (roots n j)^2) (fun _ _ => Nat.zero_le _) (mem_univ i)
    unfold fourSquareHorizon
    omega⟩

private theorem roots_pos {n : ℕ} (hn : 0 < n) (i : Fin 4) : 0 < roots n i := by
  fin_cases i <;> simp [roots] <;> positivity

private theorem conductor {n : ℕ} (hn : 0 < n) (i : Fin 4) : ((label n i:Fin (fourSquareHorizon n)):ℝ)+1 =
    (roots n i:ℝ)^2 := by
  change (((roots n i)^2-1 : ℕ):ℝ)+1 = _
  rw [Nat.cast_sub (pow_pos (roots_pos hn i) 2),Nat.cast_one,sub_add_cancel,Nat.cast_pow]

/-- Four signed graphs with reciprocal symmetry in their square-root conductors. -/
def fourSquareDivisor (n : ℕ) := integralGraphSum (label n) coeff

theorem fourSquareDivisor_mass (n : ℕ) : ∑ i, |(fourSquareDivisor n i:ℝ)| ≤ 6 :=
  (integralGraphSum_mass (label n) coeff).trans (by
    rw [Fin.sum_univ_four]
    change |((1:ℤ):ℝ)|+|((-2:ℤ):ℝ)|+|((-2:ℤ):ℝ)|+|((1:ℤ):ℝ)| ≤ 6
    norm_num)

theorem fourSquareDivisor_degrees {n : ℕ} (hn : 0 < n) :
    positivePoleDegree (fourSquareDivisor n) = 0 ∧ negativePoleDegree (fourSquareDivisor n) = 0 := by
  have hpos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hroot (i : Fin 4) : Real.sqrt (((label n i:Fin (fourSquareHorizon n)):ℝ)+1) = (roots n i:ℝ) := by
    rw [conductor hn,Real.sqrt_sq (Nat.cast_nonneg _)]
  constructor
  · rw [positivePoleDegree,fourSquareDivisor,sum_integralGraphSum,weightedFourSum]
    simp only [hroot]
    change ((2*n:ℕ):ℝ)-2*((4*n+3:ℕ):ℝ)-2*((2*(n+1)*(2*n):ℕ):ℝ)+((2*(n+1)*(4*n+3):ℕ):ℝ)=0
    push_cast
    ring
  · rw [negativePoleDegree,fourSquareDivisor,sum_integralGraphSum,weightedFourSum]
    simp only [hroot]
    change ((2*n:ℕ):ℝ)⁻¹-2*((4*n+3:ℕ):ℝ)⁻¹-2*((2*(n+1)*(2*n):ℕ):ℝ)⁻¹+
      ((2*(n+1)*(4*n+3):ℕ):ℝ)⁻¹=0
    push_cast
    field_simp [hpos.ne', show (4*(n:ℝ)+3) ≠ 0 by positivity,show (n:ℝ)+1 ≠ 0 by positivity]
    ring

private theorem even_trace (x : ℝ) : realSplineTrace (-x) = realSplineTrace x := by
  have he := zetaScalingDatum.orbitCorr_neg splineCycle x
  simpa only [orbitCorr_splineCycle_eq,realSplineTrace] using he

private theorem rectangle (x t h : ℝ) :
    let z : Fin 4 → ℝ := ![x,x+h,x+t,x+t+h]
    (∑ i, (∑ j, realSplineTrace (z i-z j)*(coeff j:ℝ))*(coeff i:ℝ)) =
      10*realSplineTrace 0-8*realSplineTrace h+
        2*(realSplineTrace (t+h)-4*realSplineTrace t+4*realSplineTrace (t-h)) := by
  let z : Fin 4 → ℝ := ![x,x+h,x+t,x+t+h]
  change (∑ i, (∑ j, realSplineTrace (z i-z j)*(coeff j:ℝ))*(coeff i:ℝ)) = _
  simp_rw [weightedFourSum]
  simp only [show z 0 = x from rfl,show z 1 = x+h from rfl,show z 2 = x+t from rfl,
    show z 3 = x+t+h from rfl,sub_self]
  simp only [show x-(x+h) = -h by ring,show x-(x+t) = -t by ring,show x-(x+t+h) = -(t+h) by ring,
    show x+h-x = h by ring,show x+h-(x+t) = -(t-h) by ring,show x+h-(x+t+h) = -t by ring,
    show x+t-x = t by ring,show x+t-(x+h) = t-h by ring,show x+t-(x+t+h) = -h by ring,
    show x+t+h-x=t+h by ring,show x+t+h-(x+h)=t by ring,show x+t+h-(x+t)=h by ring,even_trace]
  ring

/-- The long lags are a forward second difference, with step the log ratio
of the two lower conductors. -/
theorem integerProbe_fourSquareDivisor {n : ℕ} (hn : 0 < n) :
    let t := 2*Real.log (2*((n:ℝ)+1))
    let h := 2*Real.log ((4*(n:ℝ)+3)/(2*n))
    integerProbe _ (fourSquareDivisor n) = 10*realSplineTrace 0-8*realSplineTrace h+
      2*(realSplineTrace (t+h)-4*realSplineTrace t+4*realSplineTrace (t-h)) := by
  let a : ℝ := 2*n
  let b : ℝ := 4*n+3
  let s : ℝ := 2*((n:ℝ)+1)
  let x := 2*Real.log a
  let h := 2*Real.log (b/a)
  let t := 2*Real.log s
  have ha : 0 < a := mul_pos two_pos (Nat.cast_pos.mpr hn)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hs : 0 < s := by dsimp only [s]; positivity
  have hlog : ∀ i : Fin 4, Real.log (((label n i:Fin (fourSquareHorizon n)):ℝ)+1) =
      (![x,x+h,x+t,x+t+h] : Fin 4 → ℝ) i := by
    intro i
    rw [conductor hn,Real.log_pow]
    have hr (j : Fin 4) : (roots n j:ℝ) = (![a,b,s*a,s*b] : Fin 4 → ℝ) j := by
      fin_cases j <;> simp [roots,a,b,s]
    rw [hr]
    fin_cases i <;> simp [x,h,t,Real.log_div hb.ne' ha.ne',Real.log_mul hs.ne' ha.ne',Real.log_mul hs.ne' hb.ne'] <;> ring
  unfold fourSquareDivisor
  rw [integerProbe_integralGraphSum]
  simp_rw [hlog]
  exact rectangle x t h

#print axioms integerProbe_fourSquareDivisor
#print axioms fourSquareDivisor_degrees
#print axioms fourSquareDivisor_mass

end GaloisForLFunctions.CountingHolography.Sections
