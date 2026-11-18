import GaloisForLFunctions.RHTower.AdamsOperations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The first three traces of a reciprocal cubic Euler factor

For the polynomial X³ − A X² + conj(A) X − 1, the second and third
power sums are determined by A. Their square means can use the second
moment of A once, saving two powers of its uniform bound. This treats
the square and cube terms separately in the prime-power estimate of
arXiv:2610.18928, Lemma 2.3.
-/

noncomputable section
open Finset
open scoped ComplexConjugate
namespace GaloisForLFunctions.SelbergClass.CubicTraces

def squareTrace (A : ℂ) := A^2 - 2 * conj A
def cubeTrace (A : ℂ) := A^3 - 3 * A * conj A + 3

/-- Newton identities for an arbitrary triple, before specializing its determinant. -/
theorem newton_three (α : Fin 3 → ℂ) :
    let A := adamsPowerSum α 1
    let B := α 0 * α 1 + α 0 * α 2 + α 1 * α 2
    adamsPowerSum α 2 = A^2 - 2*B ∧
      adamsPowerSum α 3 = A^3 - 3*A*B + 3*(α 0*α 1*α 2) := by
  simp only [adamsPowerSum, Fin.sum_univ_three, pow_one]
  constructor <;> ring

/-- Exact traces of every determinant-one triple with reciprocal coefficients. -/
theorem reciprocal_traces (α : Fin 3 → ℂ) :
    α 0*α 1*α 2 = 1 → α 0*α 1 + α 0*α 2 + α 1*α 2 = conj (adamsPowerSum α 1) →
    adamsPowerSum α 2 = squareTrace (adamsPowerSum α 1) ∧
      adamsPowerSum α 3 = cubeTrace (adamsPowerSum α 1) := by
  intro hd hb
  simpa only [hd,hb,mul_one,squareTrace,cubeTrace] using newton_three α

/-- Sharp radial bound for the square trace and the centered cube trace. -/
theorem radial_bounds (A : ℂ) :
    ‖squareTrace A‖ ≤ ‖A‖*(‖A‖+2) ∧ ‖cubeTrace A - 3‖ ≤ ‖A‖^2*(‖A‖+3) := by
  constructor
  · calc
      _ ≤ ‖A^2‖ + ‖2 * conj A‖ := norm_sub_le _ _
      _ = _ := by rw [norm_pow,norm_mul,Complex.norm_conj]; norm_num <;> ring
  · rw [cubeTrace,add_sub_cancel_right]
    calc
      _ ≤ ‖A^3‖ + ‖3*A*conj A‖ := norm_sub_le _ _
      _ = _ := by simp only [norm_pow,norm_mul,Complex.norm_conj]; norm_num <;> ring

/-- On the negative real ray both radial inequalities are equalities. -/
theorem negative_ray (r : NNReal) :
    ‖squareTrace (-((r:ℝ):ℂ))‖ = (r:ℝ)*(r+2) ∧
    ‖cubeTrace (-((r:ℝ):ℂ))-3‖ = (r:ℝ)^2*(r+3) := by
  have h₁ : squareTrace (-((r:ℝ):ℂ)) = (((r:ℝ)*((r:ℝ)+2):ℝ):ℂ) := by
    simp only [squareTrace,map_neg,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_add,
      Complex.ofReal_ofNat]; ring
  have h₂ : cubeTrace (-((r:ℝ):ℂ))-3 = -((((r:ℝ)^2*((r:ℝ)+3):ℝ):ℂ)) := by
    simp only [cubeTrace,map_neg,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_add,
      Complex.ofReal_pow,Complex.ofReal_ofNat]; ring
  rw [h₁,h₂,norm_neg,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
  exact ⟨rfl,rfl⟩

/-- Uniform height of the first trace on a finite family, including the empty family. -/
def height {ι : Type*} (S : Finset ι) (A : ι → ℂ) : NNReal := S.sup fun i => ‖A i‖₊

/-- The constant contribution eighteen per index handles nonzero cube trace at A=0. -/
theorem second_moments {ι : Type*} (S : Finset ι) (A : ι → ℂ) :
    let H : ℝ := height S A
    let M := ∑ i ∈ S, ‖A i‖^2
    (∑ i ∈ S, ‖squareTrace (A i)‖^2) ≤ (H+2)^2*M ∧
    (∑ i ∈ S, ‖cubeTrace (A i)‖^2) ≤ 2*H^2*(H+3)^2*M + 18*S.card := by
  let H : ℝ := height S A
  have hH : 0 ≤ H := (height S A).property
  have bound (i) (hi : i ∈ S) : ‖A i‖ ≤ H := Finset.le_sup (f := fun j => ‖A j‖₊) hi
  constructor
  · rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have h := (radial_bounds (A i)).1.trans
      (mul_le_mul_of_nonneg_left (add_le_add_left (bound i hi) 2) (norm_nonneg _))
    calc
      _ ≤ (‖A i‖*(H+2))^2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := by ring
  · change _ ≤ 2*H^2*(H+3)^2*(∑ i ∈ S, ‖A i‖^2) + 18*S.card
    rw [mul_sum,show 18*(S.card:ℝ) = ∑ _i ∈ S, (18:ℝ) by simp [mul_comm],← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    let r := ‖A i‖
    have hr : 0 ≤ r := norm_nonneg _
    have hrH := bound i hi
    have hb : ‖cubeTrace (A i) - 3‖ ≤ r * (H*(H+3)) := by
      refine (radial_bounds (A i)).2.trans ?_
      change r^2*(r+3) ≤ _
      rw [sq,mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hrH (add_le_add_left hrH 3)
        (by positivity) hH) hr
    have ht := norm_add_le (cubeTrace (A i)-3) (3:ℂ)
    rw [sub_add_cancel] at ht
    norm_num at ht
    have h := pow_le_pow_left₀ (norm_nonneg _) (ht.trans (add_le_add_left hb 3)) 2
    calc
      _ ≤ (r*(H*(H+3))+3)^2 := h
      _ ≤ _ := by change _ ≤ 2*H^2*(H+3)^2*r^2 + 18; nlinarith only [sq_nonneg (r*(H*(H+3))-3)]

/-- With height measured at Y^(5/14), the quadratic and cubic height
factors cost only Y^(5/7) and Y^(10/7), respectively. -/
theorem height_factors (Y C : NNReal) (hY : 1≤Y) :
    let t := (Y:ℝ) ^ (5/14:ℝ)
    ((C:ℝ)*t+2)^2 ≤ (C+2:ℝ)^2*(Y:ℝ)^(5/7:ℝ) ∧
    ((C:ℝ)*t)^2*((C:ℝ)*t+3)^2 ≤ (C:ℝ)^2*(C+3:ℝ)^2*(Y:ℝ)^(10/7:ℝ) := by
  let t := (Y:ℝ) ^ (5/14:ℝ)
  have ht : 1 ≤ t := Real.one_le_rpow (by exact_mod_cast hY) (by norm_num)
  have hp (n : ℕ) : t^n = (Y:ℝ)^((5/14:ℝ)*(n:ℝ)) :=
    (Real.rpow_mul_natCast Y.property _ n).symm
  have h₂ : t^2 = (Y:ℝ)^(5/7:ℝ) := by rw [hp]; norm_num
  have h₄ : t^4 = (Y:ℝ)^(10/7:ℝ) := by rw [hp]; norm_num
  have step (j : ℝ) (hj : 0 ≤ j) : ((C:ℝ)*t+j)^2 ≤ (((C:ℝ)+j)*t)^2 :=
    pow_le_pow_left₀ (by positivity) (by nlinarith only [mul_nonneg hj (sub_nonneg.mpr ht)]) 2
  constructor
  · calc
      _ ≤ _ := step 2 (by norm_num)
      _ = _ := by rw [mul_pow,h₂]
  · calc
      _ ≤ ((C:ℝ)*t)^2 * (((C:ℝ)+3)*t)^2 := mul_le_mul_of_nonneg_left (step 3 (by norm_num)) (sq_nonneg _)
      _ = (C:ℝ)^2*(C+3:ℝ)^2*t^4 := by ring
      _ = _ := by rw [h₄]

/-- Normalize by the observed height and mean of the first trace on primes
below N. At the base cutoff Y=N+1 the exponents are 12/7 and 17/7,
giving 6/7 and 17/21 in the corresponding prime-power cutoffs. -/
theorem prime_mean_bounds (N : ℕ) (A : ℕ → ℂ) :
    let S := (range N).filter Nat.Prime
    let Y : ℝ := N+1
    let C := (height S A:ℝ)/Y^(5/14:ℝ)
    let D := (∑ p ∈ S, ‖A p‖^2)/Y
    (∑ p ∈ S, ‖squareTrace (A p)‖^2) ≤ (C+2)^2*D*Y^(12/7:ℝ) ∧
    (∑ p ∈ S, ‖cubeTrace (A p)‖^2) ≤ (2*C^2*(C+3)^2*D+18)*Y^(17/7:ℝ) := by
  let S := (range N).filter Nat.Prime
  let Y : NNReal := N+1
  let t := (Y:ℝ)^(5/14:ℝ)
  have hy : 1 ≤ Y := by simp [Y]
  have hy' : 1 ≤ (Y:ℝ) := by exact_mod_cast hy
  have hy₀ := one_pos.trans_le hy'
  have ht : 0<t := Real.rpow_pos_of_pos hy₀ _
  let C : NNReal := height S A / ⟨t,ht.le⟩
  let M := ∑ p ∈ S, ‖A p‖^2
  let D := M/(Y:ℝ)
  have hM : 0 ≤ M := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ D := div_nonneg hM hy₀.le
  have hC : (C:ℝ)*t = height S A := div_mul_cancel₀ _ ht.ne'
  have hmass : D*(Y:ℝ)=M := div_mul_cancel₀ _ hy₀.ne'
  have hpow (a : ℝ) : (Y:ℝ)^a * Y = (Y:ℝ)^(a+1) := by rw [Real.rpow_add hy₀,Real.rpow_one]
  have hc : (S.card:ℝ) ≤ (Y:ℝ) := by
    have h := (card_filter_le (range N) Nat.Prime).trans_eq (card_range N)
    exact le_trans (by exact_mod_cast h : (S.card:ℝ) ≤ N) (by change (N:ℝ) ≤ N+1; linarith)
  have hbig : (Y:ℝ) ≤ (Y:ℝ)^(17/7:ℝ) :=
    Real.self_le_rpow_of_one_le hy' (by norm_num)
  obtain ⟨u,v⟩ := second_moments S A
  obtain ⟨b₂,b₃⟩ := height_factors Y C hy
  change ((C:ℝ)*t+2)^2 ≤ _ at b₂
  change ((C:ℝ)*t)^2*((C:ℝ)*t+3)^2 ≤ _ at b₃
  rw [hC] at b₂ b₃
  change _ ≤ ((C:ℝ)+2)^2*D*(Y:ℝ)^(12/7:ℝ) ∧
    _ ≤ (2*(C:ℝ)^2*((C:ℝ)+3)^2*D+18)*(Y:ℝ)^(17/7:ℝ)
  constructor
  · calc
      _ ≤ _ := u
      _ ≤ _ := mul_le_mul_of_nonneg_right b₂ hM
      _ = _ := by
        rw [← hmass,show (12/7:ℝ)=5/7+1 by norm_num,← hpow]; ring
  · calc
      _ ≤ _ := v
      _ ≤ 2*((C:ℝ)^2*((C:ℝ)+3)^2*(Y:ℝ)^(10/7:ℝ))*M + 18*(Y:ℝ)^(17/7:ℝ) := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b₃ (by norm_num : (0:ℝ)≤2)) hM
        linarith only [h, mul_le_mul_of_nonneg_left (hc.trans hbig) (by norm_num : (0:ℝ)≤18)]
      _ = _ := by
        rw [← hmass,show (17/7:ℝ)=10/7+1 by norm_num,← hpow]; ring

/-- Positive logarithmic derivative coefficient for the tensor with the dual. -/
def tensorWeight {ι : Type*} [Fintype ι] (α : ι → ℂ) (k p : ℕ) : ℝ :=
  (adamsPowerSum (satakeTensorParameters α (fun i => conj (α i))) k).re * Real.log p

/-- Each local square is exactly the tensor logarithmic coefficient times log p. -/
theorem square_as_tensor {ι : Type*} [Fintype ι] (α : ι → ℂ) (k p : ℕ) :
    (‖adamsPowerSum α k‖*Real.log p)^2 = tensorWeight α k p * Real.log p := by
  simp only [tensorWeight,adamsPowerSum_tensor_selfDual_normSq,Complex.ofReal_re,
    Complex.normSq_eq_norm_sq,mul_pow]
  ring

/-- For every local parameter system the positive tensor Chebyshev sum
controls the total squared logarithmic mass with exactly one outside
logarithm. Each prime power is indexed by its base and exponent. -/
theorem tensor_chebyshev_bound {ι : Type*} [Fintype ι] (α : ℕ → ι → ℂ) (N : ℕ) :
    let P := ((Icc 2 N) ×ˢ (Icc 1 N)).filter fun b => b.1.Prime ∧ b.1^b.2 ≤ N
    (∑ b ∈ P, (‖adamsPowerSum (α b.1) b.2‖*Real.log b.1)^2) ≤
      (∑ b ∈ P, tensorWeight (α b.1) b.2 b.1)*Real.log N := by
  dsimp only
  rw [sum_mul]
  apply sum_le_sum
  intro b hb
  obtain ⟨hp,hN⟩ := mem_Icc.mp (mem_product.mp (mem_filter.mp hb).1).1
  have hp₁ : (1:ℝ) ≤ b.1 := by exact_mod_cast (show 1≤b.1 by omega)
  rw [square_as_tensor]
  apply mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans_le hp₁) (by exact_mod_cast hN))
  simp only [tensorWeight,adamsPowerSum_tensor_selfDual_normSq,Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Real.log_nonneg hp₁)

end GaloisForLFunctions.SelbergClass.CubicTraces

#print axioms GaloisForLFunctions.SelbergClass.CubicTraces.newton_three
#print axioms GaloisForLFunctions.SelbergClass.CubicTraces.reciprocal_traces
#print axioms GaloisForLFunctions.SelbergClass.CubicTraces.radial_bounds
#print axioms GaloisForLFunctions.SelbergClass.CubicTraces.negative_ray
#print axioms GaloisForLFunctions.SelbergClass.CubicTraces.second_moments
#print axioms GaloisForLFunctions.SelbergClass.CubicTraces.height_factors
#print axioms GaloisForLFunctions.SelbergClass.CubicTraces.prime_mean_bounds
#print axioms GaloisForLFunctions.SelbergClass.CubicTraces.square_as_tensor
#print axioms GaloisForLFunctions.SelbergClass.CubicTraces.tensor_chebyshev_bound
