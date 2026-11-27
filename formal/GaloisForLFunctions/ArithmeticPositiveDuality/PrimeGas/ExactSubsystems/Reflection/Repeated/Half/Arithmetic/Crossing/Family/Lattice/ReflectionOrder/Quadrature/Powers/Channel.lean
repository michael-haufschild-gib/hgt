import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Thermal
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Projection

/-! # Exact blind heights and sharp sensitivity on physical prime-power shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers

open Real Finset
open PrimeCalibration (log_pos_prime)

def radial (p : Nat.Primes) (σ : ℝ) := (σ-1/2)*log p.val

/-- Reciprocal real reading of the actual normalized divisor channel on p^n. -/
def reading (p : Nat.Primes) (n : ℕ+) (s : ℂ) := amplitude (projection s ((atom p)^n.val))

private theorem projected_prime (p : Nat.Primes) (s : ℂ) :
    projection s (atom p)=Complex.exp (-(coordinate p s)) := by
  have hp : 0<(p.val : ℝ) := Nat.cast_pos.mpr p.property.pos
  have root : sqrt (p.val : ℝ)=exp (log p.val/2) := by rw [exp_half,exp_log hp]
  rw [projected_heat,heat,energy,atom,label_one_quantum,root,Complex.ofReal_exp,←Complex.exp_add]
  congr 1
  simp only [coordinate,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

private theorem projected_pow (s : ℂ) (n : ℕ+) (k : ℕ) :
    projection s (n^k)=(projection s n)^k := by
  induction k with
  | zero => simp [projected_heat,heat,energy]
  | succ k ih => rw [pow_succ,projection_mul,ih,pow_succ]

theorem reading_formula (p : Nat.Primes) (n : ℕ+) (s : ℂ) :
    reading p n s= -(2*sinh ((n : ℝ)*radial p s.re)*cos ((n : ℝ)*(s.im*log p.val))) := by
  rw [reading,projected_pow,projected_prime,←Complex.exp_nat_mul,first]
  have coordRe : (coordinate p s).re=radial p s.re := by
    simp only [coordinate,radial,Complex.mul_re,Complex.sub_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
  have coordIm : (coordinate p s).im=s.im*log p.val := by
    simp only [coordinate,Complex.mul_im,Complex.sub_im,Complex.ofReal_im,Complex.ofReal_re,
      mul_zero,zero_add,sub_zero]
  simp only [Complex.mul_re,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,zero_mul,
    sub_zero,add_zero,Complex.neg_re,Complex.neg_im,coordRe,coordIm,mul_neg,sinh_neg,cos_neg,neg_mul]

variable {I : Type*} [Fintype I] [Nonempty I]

/-- Either splitting is isometric, or all occupations have the same
two-adic valuation and the height is an odd quarter period of their gcd. -/
theorem blind_heights (p : Nat.Primes) (k : I → ℕ+) (s : ℂ) :
    (∀ i, reading p (k i) s=0) ↔ s.re=1/2 ∨
      ((∀ i j, (k i : ℕ).factorization 2=(k j : ℕ).factorization 2) ∧
      ∃ m : ℤ, s.im=(2*(m : ℝ)+1)*π/(2*(fundamental k : ℝ)*log p.val)) := by
  have hp := log_pos_prime p
  have hg : 0<(fundamental k : ℝ) := Nat.cast_pos.mpr (fundamental_pos k)
  by_cases line : s.re=1/2
  · simp only [line,reading_formula,radial,sub_self,zero_mul,mul_zero,sinh_zero,neg_zero,
      true_or,implies_true]
  · have xne : radial p s.re≠0 := mul_ne_zero (sub_ne_zero.mpr line) hp.ne'
    have test (i : I) : reading p (k i) s=0 ↔ cos ((k i : ℝ)*(s.im*log p.val))=0 := by
      have kn : (k i : ℝ)≠0 := Nat.cast_ne_zero.mpr (k i).ne_zero
      rw [reading_formula,neg_eq_zero,mul_eq_zero,or_iff_right
        (mul_ne_zero (by norm_num) (sinh_ne_zero.mpr (mul_ne_zero kn xne)))]
    simp only [test,line,false_or,common_phases]
    apply and_congr_right
    intro _
    apply exists_congr
    intro m
    rw [eq_div_iff (by positivity : 2*(fundamental k : ℝ)*log p.val≠0),
      eq_div_iff (by norm_num : (2 : ℝ)≠0)]
    constructor <;> intro h <;> linarith only [h]

/-- A prescribed list works at all complex temperatures precisely when
it contains two occupations of different two-adic valuations. -/
theorem uniform_isometry (p : Nat.Primes) (k : I → ℕ+) :
    (∀ s : ℂ, (∀ i, reading p (k i) s=0) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ↔
      ∃ i j, (k i : ℕ).factorization 2≠(k j : ℕ).factorization 2 := by
  classical
  constructor
  · intro detector
    by_contra! same
    let t := π/(2*(fundamental k : ℝ)*log p.val)
    let s : ℂ := ⟨0,t⟩
    have hit := (blind_heights p k s).mpr (Or.inr ⟨same,0,by simp [s,t]⟩)
    have line := (split_isometric_iff s).mp ((detector s).mp hit)
    change (0 : ℝ)=1/2 at line
    norm_num at line
  · rintro ⟨i,j,hij⟩ s
    rw [blind_heights,split_isometric_iff]
    exact or_iff_left (fun h => hij (h.1 i j))

/-- Measured maximum, normalized by occupation in each channel. -/
def jointError (p : Nat.Primes) (k : I → ℕ+) (s : ℂ) :=
  peak fun i => |reading p (k i) s| / (k i : ℝ)

theorem joint_formula (p : Nat.Primes) (k : I → ℕ+) (s : ℂ) (off : radial p s.re≠0) :
    jointError p k s=2*|sinh (radial p s.re)| * sensitivity k (radial p s.re) (s.im*log p.val) := by
  let x := radial p s.re
  let y := s.im*log p.val
  let b (i : I) := amplification (k i) x * |cos ((k i : ℝ)*y)|
  let c := 2*|sinh x|
  have hc : 0<c := mul_pos (by norm_num) (abs_pos.mpr (sinh_ne_zero.mpr off))
  have point (i : I) : |reading p (k i) s| / (k i : ℝ)=c*b i := by
    rw [reading_formula,abs_neg,abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    change (2*|sinh ((k i : ℝ)*x)| * |cos ((k i : ℝ)*y)|)/(k i : ℝ)=
      c * (amplification (k i) x * |cos ((k i : ℝ)*y)|)
    dsimp only [amplification,c]
    have kn : (k i : ℝ)≠0 := Nat.cast_ne_zero.mpr (k i).ne_zero
    have nx : |sinh x|≠0 := abs_ne_zero.mpr (sinh_ne_zero.mpr off)
    field_simp [kn,nx]
  change peak _=c*peak b
  apply le_antisymm
  · exact peak_le.mpr fun i => (point i).trans_le (mul_le_mul_of_nonneg_left (to_peak b i) hc.le)
  · obtain ⟨i,eq⟩ := peak_value b
    rw [eq,←point]
    exact to_peak (fun j => |reading p (k j) s| / (k j : ℝ)) i

/-- The optimal gain of the actual prime-power channels on each punctured
strip about the isometry line is the same finite arithmetic constant. -/
theorem sharp_channel_gain (p : Nat.Primes) (k : I → ℕ+) (δ K : ℝ) (hδ : 0<δ) :
    (∀ s : ℂ, radial p s.re≠0 → |radial p s.re|<δ →
      2*|sinh (radial p s.re)| * K ≤ jointError p k s) ↔ K≤gain k := by
  have hp := log_pos_prime p
  constructor
  · intro bound
    apply (sharp_local_gain k δ hδ K).mp
    intro x y hx small
    let s : ℂ := ⟨x/log p.val+1/2,y/log p.val⟩
    have realPart : radial p s.re=x := by
      change (x/log p.val+1/2-1/2)*log p.val=x
      rw [add_sub_cancel_right,div_mul_cancel₀ _ hp.ne']
    have phasePart : s.im*log p.val=y := div_mul_cancel₀ _ hp.ne'
    have h := bound s (by rwa [realPart]) (by rwa [realPart])
    rw [joint_formula p k s (by rwa [realPart]),realPart,phasePart] at h
    exact (mul_le_mul_iff_right₀ (mul_pos (by norm_num) (abs_pos.mpr (sinh_ne_zero.mpr hx)))).mp h
  · intro h s hx _
    rw [joint_formula p k s hx]
    exact mul_le_mul_of_nonneg_left (h.trans (sensitivity_lower k _ _ hx)) (by positivity)

#print axioms reading_formula
#print axioms blind_heights
#print axioms uniform_isometry
#print axioms joint_formula
#print axioms sharp_channel_gain

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers
