import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheIntegerWaveHasVanishingMeanAbsoluteError
import GaloisForLFunctions.RHTower.ThetaDivisorBernsteinGauge
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusRightInverse
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization

/-!
# Ordered Möbius inversion of the centered integer wave

Confinement makes the uncentered double sum absolutely convergent. After
density subtraction the harmonic Möbius sums must be taken in natural order.
Their zeroth and first logarithmic moments recover the state and the
polar-subtracted Mangoldt wave, respectively.
-/

noncomputable section
open MeasureTheory Filter Topology Finset ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

/-- Centered contribution from all multiples of a single divisor. -/
def centredMultipleRow (Φ : ℝ → ℝ) (A : ℝ) (d : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt d)⁻¹*(integerReferenceWave Φ (t-Real.log d)-Real.exp ((t-Real.log d)/2)*A)

private theorem atom_at_product (Φ : ℝ → ℝ) (d n : ℕ) (t : ℝ) :
    continuousIntegerAtom Φ (d*n:ℕ) t = (Real.sqrt d)⁻¹*continuousIntegerAtom Φ n (t-Real.log d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [continuousIntegerAtom]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [continuousIntegerAtom]
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [continuousIntegerAtom,continuousIntegerAtom,Nat.cast_mul,Real.sqrt_mul hd'.le,
    Real.log_mul hd'.ne' hn'.ne',mul_inv_rev]
  rw [show t-(Real.log d+Real.log n)=(t-Real.log d)-Real.log n by ring]; ring

private theorem summable_divisor_atoms {Φ : ℝ → ℝ} {C : ℝ} (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {w : ℕ → ℝ} (hw : Summable fun d : ℕ => |w d|/(d:ℝ)^2) (t : ℝ) :
    Summable (fun q : ℕ × ℕ => w q.1*continuousIntegerAtom Φ (q.1*q.2:ℕ) t) := by
  let v := fun n : ℕ => 1/(n:ℝ)^2
  have hv : Summable v := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h := hw.mul_of_nonneg (g := v) hv (fun _ => div_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun _ => by dsimp only [v]; positivity)
  apply Summable.of_norm_bounded (h.mul_left (C*Real.exp (2*t)))
  rintro ⟨d,n⟩
  rw [Real.norm_eq_abs,abs_mul]
  rcases Nat.eq_zero_or_pos (d*n) with h0 | hp
  · rcases Nat.mul_eq_zero.1 h0 with rfl | rfl <;> simp [continuousIntegerAtom,v]
  have ha := continuousIntegerAtom_bound hb (by exact_mod_cast hp : (1:ℝ) ≤ (d*n:ℕ)) t
  apply (mul_le_mul_of_nonneg_left ha (abs_nonneg (w d))).trans_eq
  dsimp only [v]; rw [Nat.cast_mul,mul_pow]; ring

/-- Grouping the absolutely convergent double sum by product gives the
divisor sum of the coefficients against the original integer atoms. -/
private theorem hasSum_multiple_reference {Φ : ℝ → ℝ} {C : ℝ} (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {w : ℕ → ℝ} (hw : Summable fun d : ℕ => |w d|/(d:ℝ)^2) (t : ℝ) :
    HasSum (fun d : ℕ => (w d*(Real.sqrt d)⁻¹)*integerReferenceWave Φ (t-Real.log d))
      (∑' n : ℕ, (∑ d ∈ n.divisors, w d)*continuousIntegerAtom Φ n t) := by
  let f := fun q : ℕ × ℕ => w q.1*continuousIntegerAtom Φ (q.1*q.2:ℕ) t
  have hs : Summable f := summable_divisor_atoms hb hw t
  have hz (q : ℕ × ℕ) (hq : q.1=0 ∨ q.2=0) : f q=0 := by
    rcases hq with h | h <;> simp [f,h,continuousIntegerAtom]
  have hfib (n : ℕ) : (∑' z : (fun q : ℕ × ℕ => q.1*q.2) ⁻¹' {n}, f z) =
      (∑ d ∈ n.divisors, w d)*continuousIntegerAtom Φ n t := by
    change (∑' z : {q : ℕ × ℕ // q.1*q.2=n}, f z) = _
    rw [(divisorFiber_tsum hz n).2,Finset.sum_mul]
    calc _ = ∑ q ∈ n.divisorsAntidiagonal, w q.1*continuousIntegerAtom Φ n t :=
               Finset.sum_congr rfl fun q hq => by dsimp only [f]; rw [(Nat.mem_divisorsAntidiagonal.1 hq).1]
      _ = _ := Nat.sum_divisorsAntidiagonal (fun d _ => w d*continuousIntegerAtom Φ n t)
  have hy := hs.hasSum.tsum_fiberwise (fun q : ℕ × ℕ => q.1*q.2)
  simp_rw [hfib] at hy
  rw [hy.tsum_eq,hs.tsum_prod]
  apply hs.prod.hasSum.congr_fun
  intro d
  simp only [f,atom_at_product,← mul_assoc,tsum_mul_left,tsum_continuousIntegerAtom hb]

private theorem scaled_polar_row (d : ℕ) (t : ℝ) :
    (Real.sqrt d)⁻¹*Real.exp ((t-Real.log d)/2)=(d:ℝ)⁻¹*Real.exp (t/2) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  rw [sub_div,Real.exp_sub,Real.exp_half (Real.log _),Real.exp_log hd']
  calc _ = ((Real.sqrt d)^2)⁻¹*Real.exp (t/2) := by rw [← inv_pow,div_eq_mul_inv]; ring
    _ = _ := by rw [Real.sq_sqrt hd'.le]

/-- The density term uses the ordered harmonic mean of the coefficients. -/
private theorem tendsto_centered_multiple_rows {Φ : ℝ → ℝ} {C : ℝ} (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {w : ℕ → ℝ} (hw : Summable fun d : ℕ => |w d|/(d:ℝ)^2) {M : ℝ}
    (hM : Tendsto (fun N : ℕ => ∑ d ∈ range (N+1), w d/(d:ℝ)) atTop (𝓝 M))
    (A t : ℝ) : Tendsto (fun N : ℕ => ∑ d ∈ range (N+1), w d*centredMultipleRow Φ A d t) atTop
      (𝓝 ((∑' n : ℕ, (∑ d ∈ n.divisors, w d)*continuousIntegerAtom Φ n t)-M*(Real.exp (t/2)*A))) := by
  have h := (hasSum_multiple_reference hb hw t).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  apply (h.sub (hM.mul_const (Real.exp (t/2)*A))).congr'
  refine Eventually.of_forall fun N => ?_
  change (∑ d ∈ range (N+1), _) - (∑ d ∈ range (N+1), _)*(Real.exp (t/2)*A) = _
  rw [Finset.sum_mul,← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  dsimp only [centredMultipleRow]
  linear_combination w d*A*scaled_polar_row d t

private def realMoebius (d : ℕ) : ℝ := ((moebius d : ℤ) : ℝ)

private theorem abs_realMoebius_le (d : ℕ) : |realMoebius d| ≤ 1 := by
  dsimp only [realMoebius]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- Möbius inversion recovers the state exactly, even after subtracting
the full polar density in every divisor row. -/
theorem tendsto_moebius_centredMultipleRow {Φ : ℝ → ℝ} {C : ℝ} (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    (A t : ℝ) : Tendsto (fun N : ℕ => ∑ d ∈ range (N+1), ((moebius d : ℤ):ℝ)*centredMultipleRow Φ A d t)
      atTop (𝓝 (Φ t)) := by
  have hw : Summable fun d : ℕ => |realMoebius d|/(d:ℝ)^2 :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun d => div_le_div_of_nonneg_right (abs_realMoebius_le d) (sq_nonneg _))
      ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num))
  have hM := deningerHarmonicPartial_tendsto
  rw [deningerHarmonicLimit_eq_zero] at hM
  have h := tendsto_centered_multiple_rows hb hw hM A t
  have hv : (∑' n : ℕ, (if n=1 then (1:ℝ) else 0)*continuousIntegerAtom Φ n t)=Φ t := by
    rw [tsum_eq_single 1 (fun n hn => by rw [if_neg hn,zero_mul])]
    simp [continuousIntegerAtom]
  simpa only [realMoebius,deningerMobiusDivisorSumReal,zero_mul,sub_zero,hv] using h

/-- The first logarithmic moment of the same ordered rows is the actual
von Mangoldt wave minus its polar density. -/
theorem tendsto_moebius_log_centredMultipleRow {Φ : ℝ → ℝ} {C : ℝ} (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    (A t : ℝ) : Tendsto (fun N : ℕ => ∑ d ∈ range (N+1),
      (-((moebius d : ℤ):ℝ)*Real.log d)*centredMultipleRow Φ A d t) atTop
        (𝓝 ((∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t)-Real.exp (t/2)*A)) := by
  let w := fun d : ℕ => -realMoebius d*Real.log d
  have hw : Summable fun d : ℕ => |w d|/(d:ℝ)^2 := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ GaloisForLFunctions.summable_log_nat_div_sq
    intro d
    rw [show |w d|=|realMoebius d| *Real.log d by simp [w,abs_mul,abs_of_nonneg (Real.log_natCast_nonneg d)]]
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_right (abs_realMoebius_le d)
      (Real.log_natCast_nonneg d)).trans_eq (one_mul _)) (sq_nonneg _)
  have hM : Tendsto (fun N : ℕ => ∑ d ∈ range (N+1), w d/(d:ℝ)) atTop (𝓝 1) := by
    simpa only [Sieve.moebiusLogHarmonicPartial,Sieve.moebiusLogHarmonicTerm,Real.rpow_neg_one,
      w,realMoebius,div_eq_mul_inv] using Sieve.tendsto_moebiusLogHarmonicPartial_one
  have hcoef (n : ℕ) : (∑ d ∈ n.divisors, w d)=vonMangoldt n := by
    simp only [w,realMoebius,neg_mul,sum_neg_distrib,deningerMobiusLogDivisorSum,neg_neg]
  simpa only [hcoef,one_mul] using tendsto_centered_multiple_rows hb hw hM A t

#print axioms tendsto_moebius_centredMultipleRow
#print axioms tendsto_moebius_log_centredMultipleRow
end GaloisForLFunctions.ExclusionOfTheCriticalState
