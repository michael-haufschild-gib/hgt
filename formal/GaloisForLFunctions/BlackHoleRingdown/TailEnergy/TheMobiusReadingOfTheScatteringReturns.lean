import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.PrimePowerReturnsForceSignedCancellation
import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation

/-!
# Möbius inversion of the scattering returns

Translations by logarithmic delays compose by multiplication of their
denominators. The finite translation sums therefore realize Dirichlet
convolution on every observation window. Inverting the ordinary return
weight φ(n)/n by Möbius-weighted translations leaves just μ(n)/n at time
2 log n. The growing mean term is included for every compact pulse.
-/

open Finset Complex MeasureTheory Set ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace GaloisForLFunctions.BlackHoleRingdown.ReturnCancellation
noncomputable section
open scoped Classical

/-- Delayed single-bounce reading through the given denominator cutoff. -/
def finiteDelayReading (a : ℕ → ℂ) (h : CompactPulse) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, a n*bounce h (t-echoDelay n)

private theorem bounce_above_denominator (h : CompactPulse) {S B t : ℝ}
    (hs : ∀ s : ℝ, S < |s| → h s = 0) (ht : t ≤ B) {n : ℕ}
    (hn : pathReturnCutoff (B+S) < n) : bounce h (t-echoDelay n)=0 := by
  have hp := Nat.zero_lt_of_lt hn
  have hexp := (Nat.le_ceil (Real.exp ((B+S)/2))).trans (Nat.cast_le.mpr hn.le)
  have hlog := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hp)).mpr hexp
  unfold bounce
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro v hv
  have hlarge : S < |t-echoDelay n-v| := by
    refine lt_of_lt_of_le ?_ (neg_le_abs _)
    unfold echoDelay
    linarith only [ht,hlog,(show (0:ℝ)<v from hv)]
  rw [hs _ hlarge,zero_mul]

private theorem delay_product {a b : ℕ} (ha : 0<a) (hb : 0<b) :
    echoDelay (a*b) = echoDelay a + echoDelay b := by
  simp only [echoDelay,Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr ha.ne')
    (Nat.cast_ne_zero.mpr hb.ne'),mul_add]

/-- Successive finite translation filters multiply by Dirichlet convolution.
All terms in the square of cutoffs lying past the product cutoff vanish by
the support of the input pulse. -/
theorem finiteDelayReading_convolution (a b : ℕ → ℂ) (h : CompactPulse) {S B t : ℝ}
    (hs : ∀ s : ℝ, S < |s| → h s = 0) (ht : t ≤ B) :
    let N := pathReturnCutoff (B+S)
    ∑ d ∈ Icc 1 N, a d*finiteDelayReading b h N (t-echoDelay d) =
      finiteDelayReading (fun n => ∑ z ∈ n.divisorsAntidiagonal, a z.1*b z.2) h N t := by
  let N := pathReturnCutoff (B+S)
  let J := Finset.Icc 1 N
  let W (p : ℕ × ℕ) := a p.1*b p.2*bounce h (t-echoDelay (p.1*p.2))
  let U := (J ×ˢ J).filter fun p => p.1*p.2 ≤ N
  have fibres (n : ℕ) (hn : n∈J) :
      U.filter (fun p => p.1*p.2=n) = n.divisorsAntidiagonal := by
    ext p
    rw [mem_filter,Nat.mem_divisorsAntidiagonal]
    constructor
    · exact fun hp => ⟨hp.2,Nat.ne_of_gt (mem_Icc.mp hn).1⟩
    · rintro ⟨he,hn0⟩
      have hx : 0<p.1 := Nat.pos_of_ne_zero fun h0 => hn0 (by simpa [h0] using he.symm)
      have hy : 0<p.2 := Nat.pos_of_ne_zero fun h0 => hn0 (by simpa [h0] using he.symm)
      have hxn : p.1≤n := Nat.le_of_dvd (mem_Icc.mp hn).1 ⟨p.2,he.symm⟩
      have hyn : p.2≤n := Nat.le_of_dvd (mem_Icc.mp hn).1 ⟨p.1,by rw [← he,Nat.mul_comm]⟩
      exact ⟨mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_Icc.mpr ⟨hx,hxn.trans (mem_Icc.mp hn).2⟩,mem_Icc.mpr ⟨hy,hyn.trans (mem_Icc.mp hn).2⟩⟩,
        he.trans_le (mem_Icc.mp hn).2⟩,he⟩
  have hmap (p : ℕ × ℕ) (hp : p∈U) : p.1*p.2∈J := by
    obtain ⟨hp,hle⟩ := mem_filter.mp hp
    obtain ⟨h₁,h₂⟩ := mem_product.mp hp
    exact mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp h₁).1 (mem_Icc.mp h₂).1,hle⟩
  have hzero (p : ℕ × ℕ) (hp : p∈J ×ˢ J) (hn : p∉U) : W p = 0 := by
    have hlate : N<p.1*p.2 := lt_of_not_ge fun hle => hn (mem_filter.mpr ⟨hp,hle⟩)
    simp only [W,bounce_above_denominator h hs ht hlate,mul_zero]
  change ∑ d ∈ J, a d*finiteDelayReading b h N (t-echoDelay d) = _
  calc
    _ = ∑ p ∈ J ×ˢ J, W p := by
      rw [sum_product]
      refine sum_congr rfl fun d hd => ?_
      rw [finiteDelayReading,mul_sum]
      refine sum_congr rfl fun c hc => ?_
      dsimp only [W]
      rw [delay_product (mem_Icc.mp hd).1 (mem_Icc.mp hc).1,sub_add_eq_sub_sub,mul_assoc]
    _ = ∑ p ∈ U, W p := (sum_subset (filter_subset _ _) hzero).symm
    _ = ∑ n ∈ J, ∑ z ∈ n.divisorsAntidiagonal, W z := by
      rw [← sum_fiberwise_of_maps_to hmap W]
      exact sum_congr rfl fun n hn => by rw [fibres n hn]
    _ = _ := by
      refine sum_congr rfl fun n _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun z hz => by simp only [W,(Nat.mem_divisorsAntidiagonal.mp hz).1]

/-- Möbius-weighted delayed observations recover a single signed bounce
per squarefree denominator, with coefficient μ(n)/n. -/
theorem finite_mobius_scattering_returns (h : CompactPulse) (B : ℝ) :
    ∃ N : ℕ, ∀ t ≤ B,
      (∑ d ∈ Icc 1 N, (μ d : ℂ)*(pulseReflected h (t-echoDelay d) +
        meanCoefficient h * cexp (((t-echoDelay d:ℝ):ℂ)/2))) =
      finiteDelayReading (fun n => (μ n : ℂ)/n) h N t := by
  obtain ⟨S,_,hs⟩ := h.exists_support_bound
  let N := pathReturnCutoff (B+S)
  refine ⟨N,fun t ht => ?_⟩
  have hconv := finiteDelayReading_convolution (fun d => (μ d : ℂ))
    (fun n => (echoWeight n : ℂ)) h hs ht
  have hinv (n : ℕ) (hn : 0<n) :
      ∑ z ∈ n.divisorsAntidiagonal, (μ z.1 : ℂ)*(echoWeight z.2 : ℂ) = (μ n : ℂ)/n := by
    apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun a => (μ a : ℂ)/a) (g := fun a => (echoWeight a : ℂ))).mp _ n hn
    intro m hm
    exact_mod_cast _root_.RHTower.Sieve.sum_moebius_div_divisors_eq_totient_div hm
  calc
    _ = ∑ d ∈ Icc 1 N, (μ d : ℂ)*finiteDelayReading (fun n => (echoWeight n : ℂ)) h N (t-echoDelay d) := by
      refine sum_congr rfl fun d hd => congrArg ((μ d : ℂ)*·) ?_
      have hp : 1 ≤ (d:ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
      have hd0 : 0 ≤ echoDelay d := mul_nonneg (by norm_num) (Real.log_nonneg hp)
      exact (finite_return_sum h hs (show t-echoDelay d ≤ B by linarith only [ht,hd0])).symm
    _ = _ := hconv.trans (sum_congr rfl fun n hn =>
      congrArg (· * bounce h (t-echoDelay n)) (hinv n (mem_Icc.mp hn).1))

#print axioms finiteDelayReading_convolution
#print axioms finite_mobius_scattering_returns

end
end GaloisForLFunctions.BlackHoleRingdown.ReturnCancellation
