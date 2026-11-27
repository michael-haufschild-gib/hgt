import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum.Phases
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Channel

/-! # Sharp growth exponent of raw elementary shell observations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum.Growth

open Real Set
open PrimeCalibration (log_pos_prime)

def displacement (s : ℂ) := |s.re-1/2|

/-- Absolute reading after division by the power p^β. -/
def adjusted (s : ℂ) (β : ℝ) (p : Nat.Primes) := |reading p 1 s| / (p.val : ℝ)^β

private theorem power_pos (p : Nat.Primes) (β : ℝ) : 0 < (p.val : ℝ)^β :=
  rpow_pos_of_pos (Nat.cast_pos.mpr p.property.pos) β

/-- The two reciprocal radial amplitudes are the powers p^d and p^(-d). -/
theorem raw_formula (p : Nat.Primes) (s : ℂ) :
    |reading p 1 s|=((p.val : ℝ)^(displacement s)-(p.val : ℝ)^(-displacement s)) *
      strength p s.im := by
  have hpos := (Nat.cast_pos.mpr p.property.pos : 0 < (p.val : ℝ))
  rw [reading_formula,abs_neg,abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  simp only [PNat.one_coe,Nat.cast_one,one_mul]
  rw [abs_sinh,radial,abs_mul,abs_of_pos (log_pos_prime p),sinh_eq]
  simp only [rpow_def_of_pos hpos,strength,displacement,mul_neg]
  rw [mul_comm (log p.val) |s.re-1/2|]
  ring

private theorem exact_scale (p : Nat.Primes) (s : ℂ) :
    adjusted s (displacement s) p =
      (1-((p.val : ℝ)^(2*displacement s))⁻¹)*strength p s.im := by
  have hp := (Nat.cast_pos.mpr p.property.pos : 0 < (p.val : ℝ))
  have hn := (power_pos p (displacement s)).ne'
  rw [adjusted,raw_formula,rpow_neg hp.le,two_mul,rpow_add hp]
  field_simp [hn]

private theorem rebalance (p : Nat.Primes) (s : ℂ) (β : ℝ) :
    adjusted s β p=(p.val : ℝ)^(displacement s-β)*adjusted s (displacement s) p := by
  have hp := (Nat.cast_pos.mpr p.property.pos : 0 < (p.val : ℝ))
  rw [adjusted,adjusted,rpow_sub hp]
  field_simp [(power_pos p β).ne',(power_pos p (displacement s)).ne']

private theorem growing (e K : ℝ) (he : 0 < e) :
    ∃ n : ℕ, ∀ p : Nat.Primes, n < p.val → K < (p.val : ℝ)^e := by
  obtain ⟨n,hn⟩ := exists_nat_gt (exp (K/e))
  refine ⟨n,fun p large => ?_⟩
  have bound : exp (K/e)<(p.val : ℝ) := hn.trans (Nat.cast_lt.mpr large)
  have lift := log_lt_log (exp_pos _) bound
  rw [log_exp,div_lt_iff₀ he] at lift
  rw [rpow_def_of_pos (Nat.cast_pos.mpr p.property.pos)]
  linarith only [lift,add_one_le_exp (log p.val*e)]

private theorem scale_le (p : Nat.Primes) (s : ℂ) : adjusted s (displacement s) p ≤ 1 := by
  rw [exact_scale]
  exact (mul_le_of_le_one_left (abs_nonneg _)
    (sub_le_self 1 (inv_nonneg.mpr (power_pos p _).le))).trans (strength_le p _)

/-- At the exact radial exponent the unit upper bound is sharp on
every prime tail, at every height off the isometry line. -/
theorem sharp_tail (s : ℂ) (off : s.re≠1/2) (N : ℕ) :
    IsLUB {y : ℝ | ∃ p : Nat.Primes, N < p.val ∧ y=adjusted s (displacement s) p} 1 := by
  have hd : 0 < displacement s := abs_pos.mpr (sub_ne_zero.mpr off)
  constructor
  · rintro y ⟨p,_,rfl⟩; exact scale_le p s
  · intro c bound
    by_contra! small
    let ε := (1-c)/2
    have ep : 0 < ε := by dsimp only [ε]; linarith only [small]
    obtain ⟨n,hn⟩ := growing (2*displacement s) (1/ε) (by positivity)
    obtain ⟨p,cut,high⟩ := near_one s.im (1-ε) (by linarith only [ep]) (max N n)
    have large := hn p ((le_max_right _ _).trans_lt cut)
    have tiny : ((p.val : ℝ)^(2*displacement s))⁻¹ < ε := by
      rw [←one_div,div_lt_iff₀ (power_pos p _)]
      have h := (div_lt_iff₀ ep).mp large
      linarith only [h]
    have observed := bound (show adjusted s (displacement s) p ∈
      {y : ℝ | ∃ q : Nat.Primes, N < q.val ∧ y=adjusted s (displacement s) q} from
      ⟨p,(le_max_left _ _).trans_lt cut,rfl⟩)
    rw [exact_scale] at observed
    have loss := mul_le_mul_of_nonneg_left (strength_le p s.im)
      (inv_nonneg.mpr (power_pos p (2*displacement s)).le)
    dsimp only [ε] at high tiny
    linarith only [high,tiny,loss,observed]

/-- The admissible powers bounding all raw readings form a closed
half-line off the isometry line. On the line every power is admissible. -/
theorem rate_iff (s : ℂ) (N : ℕ) (β : ℝ) :
    (∃ C : ℝ, ∀ p : Nat.Primes, N < p.val → adjusted s β p ≤ C) ↔
      s.re=1/2 ∨ displacement s ≤ β := by
  constructor
  · rintro ⟨C,bound⟩
    by_contra! fail
    obtain ⟨off,below⟩ := fail
    obtain ⟨n,scale⟩ := growing (displacement s-β) (2*(|C|+1)) (sub_pos.mpr below)
    have near : ∃ p : Nat.Primes, max N n < p.val ∧ 1/2 < adjusted s (displacement s) p := by
      by_contra! no
      have absurdity := (sharp_tail s off (max N n)).2 (show (1/2 : ℝ) ∈ upperBounds
        {y : ℝ | ∃ p : Nat.Primes, max N n < p.val ∧ y=adjusted s (displacement s) p} by
        rintro _ ⟨p,cut,rfl⟩; exact no p cut)
      norm_num at absurdity
    obtain ⟨p,cut,hit⟩ := near
    have high := scale p ((le_max_right _ _).trans_lt cut)
    have upper := bound p ((le_max_left _ _).trans_lt cut)
    rw [rebalance] at upper
    have strict := mul_lt_mul_of_pos_left hit (power_pos p (displacement s-β))
    linarith only [strict,high,upper,le_abs_self C]
  · rintro (line | enough)
    · refine ⟨0,fun p _ => ?_⟩
      simp only [adjusted,raw_formula,displacement,line,sub_self,abs_zero,neg_zero,rpow_zero,
        zero_mul,zero_div,le_rfl]
    · refine ⟨1,fun p _ => ?_⟩
      have hn : 0 ≤ adjusted s (displacement s) p := div_nonneg (abs_nonneg _) (power_pos _ _).le
      have shrink : (p.val : ℝ)^(displacement s-β) ≤ 1 :=
        rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.property.one_le) (sub_nonpos.mpr enough)
      rw [rebalance]
      exact (mul_le_of_le_one_left hn shrink).trans (scale_le p s)

/-- A finite upper bound on any tail of the raw reciprocal readings
already characterizes isometric divisor splitting. -/
theorem bounded_iff_isometry (s : ℂ) (N : ℕ) :
    (∃ C : ℝ, ∀ p : Nat.Primes, N < p.val → |reading p 1 s| ≤ C) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  have criterion := rate_iff s N 0
  simpa only [adjusted,rpow_zero,div_one,displacement,abs_nonpos_iff,sub_eq_zero,or_self,
    split_isometric_iff] using criterion

#print axioms raw_formula
#print axioms sharp_tail
#print axioms rate_iff
#print axioms bounded_iff_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum.Growth
