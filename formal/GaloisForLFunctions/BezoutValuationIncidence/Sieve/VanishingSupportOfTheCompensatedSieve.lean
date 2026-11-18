import GaloisForLFunctions.BezoutValuationIncidence.Sieve.IndependentPrimeSquareCompensation
import GaloisForLFunctions.HTGeometry.PrimeOccupationCompletionProduct

/-!
# Vanishing support and the third moment of compensated primitive triples

Multiplying the local surviving fractions gives a Mertens product times an
absolutely convergent positive correction. Thus the weight, although of
mean one, is supported on a fraction asymptotic to C/log N. Its normalized
third moment has the cyclotomic correction ζ(2)ζ(3)/ζ(6).
-/

noncomputable section
open Finset Filter Topology
open scoped Classical
namespace GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments

abbrev PrimeIndex (N : ℕ) := ↥((N+1).primesBelow)

def indexPrime (N : ℕ) (i : PrimeIndex N) : Nat.Primes :=
  ⟨i.val,(Nat.mem_primesBelow.mp i.property).2⟩

theorem index_injective (N : ℕ) : Function.Injective (indexPrime N) :=
  fun _ _ he => Subtype.ext (congrArg (fun q : Nat.Primes => q.val) he)

private def survive (q : ℕ) : ℝ := 1-((q : ℝ)-1)*rayMass q

def supportProduct (N : ℕ) : ℝ := ∏ q ∈ (N+1).primesBelow, survive q

/-- The numerical product is the actual support fraction of all primitive
triples for arbitrary unit parameters at every prime. -/
theorem supportProduct_eq (N : ℕ)
    (K : ∀ i : PrimeIndex N, (RingAt i.val 1)ˣ) (r : ∀ i : PrimeIndex N, (ZMod i.val)ˣ) :
    mean (mark (fun x => globalWeight (indexPrime N) (index_injective N) K r x≠0)) =
      supportProduct N := by
  rw [product_support]
  exact prod_attach _ survive

private def excess (q : ℕ) : ℝ := (3*(q : ℝ)-1)/(q*((q : ℝ)^2-1))

private theorem excess_bounds {q : ℕ} (hq : q.Prime) :
    0 ≤ excess q ∧ excess q ≤ 4/(q : ℝ)^2 := by
  have h : (2 : ℝ)≤q := by exact_mod_cast hq.two_le
  have hp : (0 : ℝ)<q := by linarith only [h]
  have hd : 0 < (q : ℝ)^2-1 := by nlinarith only [h,sq_nonneg ((q : ℝ)-2)]
  unfold excess
  refine ⟨div_nonneg (by linarith only [h]) (mul_pos hp hd).le,?_⟩
  rw [div_le_div_iff₀ (mul_pos hp hd) (pow_pos hp 2)]
  have he : 0 ≤ (q : ℝ)^2+q-4 := by nlinarith only [h,sq_nonneg ((q : ℝ)-2)]
  nlinarith only [mul_nonneg hp.le he]

private theorem survival_factor {q : ℕ} (hq : q.Prime) :
    survive q = (1-((q : ℝ))⁻¹)*(1+excess q) := by
  have h : (1 : ℝ)<q := by exact_mod_cast hq.one_lt
  have hp : (0 : ℝ)<q := one_pos.trans h
  have hd : (q : ℝ)^2-1≠0 := by nlinarith only [h,sq_nonneg ((q : ℝ)-1)]
  unfold survive rayMass excess
  field_simp
  ring

private def logCorrection (q : ℕ) : ℝ := if q.Prime then Real.log (1+excess q) else 0

private theorem summable_correction : Summable logCorrection := by
  have base := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2)).mul_left (4 : ℝ)
  refine Summable.of_nonneg_of_le (f := fun n : ℕ => 4*(1/(n : ℝ)^2)) ?_ ?_ base
  · intro n
    by_cases h : n.Prime
    · rw [logCorrection,if_pos h]
      exact Real.log_nonneg (by linarith only [(excess_bounds h).1])
    · simp [logCorrection,h]
  · intro n
    by_cases h : n.Prime
    · rw [logCorrection,if_pos h,mul_one_div]
      have he := Real.log_le_sub_one_of_pos (show 0<1+excess n by
        linarith only [(excess_bounds h).1])
      linarith only [he,(excess_bounds h).2]
    · simp only [logCorrection,if_neg h]
      positivity

/-- Positive constant governing the surviving fraction. -/
def supportConstant : ℝ := Real.exp (-Real.eulerMascheroniConstant) *
  Real.exp (∑' n, logCorrection n)

theorem supportConstant_pos : 0<supportConstant := mul_pos (Real.exp_pos _) (Real.exp_pos _)

private theorem support_decomposition (N : ℕ) :
    supportProduct N = RHTower.mertensPrimeProduct N *
      Real.exp (∑ n ∈ range (N+1), logCorrection n) := by
  have he : ∑ n ∈ range (N+1), logCorrection n =
      ∑ n ∈ (N+1).primesBelow, Real.log (1+excess n) := by
    rw [show (N+1).primesBelow=(range (N+1)).filter Nat.Prime from rfl,sum_filter]
    rfl
  rw [supportProduct,← RHTower.primesBelow_prod_eq_mertensPrimeProduct,he,Real.exp_sum,
    ← prod_mul_distrib]
  refine prod_congr rfl fun q hq => ?_
  have h := (Nat.mem_primesBelow.mp hq).2
  rw [survival_factor h,Real.exp_log (by linarith only [(excess_bounds h).1])]

theorem support_asymptotic :
    Tendsto (fun N : ℕ => supportProduct N * Real.log N) atTop (𝓝 supportConstant) := by
  have h := summable_correction.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  apply (RHTower.tendsto_mertensPrimeProduct_mul_log.mul ((Real.continuous_exp.tendsto _).comp h)).congr
  intro n
  rw [support_decomposition]
  change RHTower.mertensPrimeProduct n * Real.log n * Real.exp (∑ k ∈ range (n+1), logCorrection k) = _
  ring

/-- Exact unbiasedness is carried by a fraction tending to zero. -/
theorem support_vanishes : Tendsto supportProduct atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := support_asymptotic.mul (tendsto_inv_atTop_zero.comp hlog)
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hl : Real.log (n : ℝ)≠0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  change supportProduct n * Real.log n * (Real.log n)⁻¹=_
  field_simp

/-- Third moment divided by the primorial. -/
def normalizedThird (N : ℕ) : ℝ :=
  ∏ p ∈ (N+1).primesBelow, (1-(p : ℝ)⁻¹+((p : ℝ)⁻¹)^2)

theorem third_moment_eq (N : ℕ)
    (K : ∀ i : PrimeIndex N, (RingAt i.val 1)ˣ) (r : ∀ i : PrimeIndex N, (ZMod i.val)ˣ) :
    mean (fun x => (globalWeight (indexPrime N) (index_injective N) K r x)^3) /
        (∏ q ∈ (N+1).primesBelow, (q : ℝ)) = normalizedThird N := by
  let f (q : ℕ) := 1+((q:ℝ)^3-q)*rayMass q
  rw [product_moment _ _ _ _ 2]
  change (∏ i : PrimeIndex N, f i.val)/(∏ q ∈ (N+1).primesBelow, (q:ℝ)) = _
  rw [show (∏ i : PrimeIndex N, f i.val) = ∏ q ∈ (N+1).primesBelow, f q from prod_attach _ f,
    ← prod_div_distrib,normalizedThird]
  exact prod_congr rfl fun q hq => third_factor ⟨q,(Nat.mem_primesBelow.mp hq).2⟩

private def zetaProduct (k N : ℕ) : ℂ :=
  ∏ p ∈ (N+1).primesBelow, (1-((p : ℂ)^k)⁻¹)⁻¹

private theorem zeta_product_limit (k : ℕ) (hk : 2≤k) :
    Tendsto (zetaProduct k) atTop (𝓝 (riemannZeta (k : ℂ))) :=
  (_root_.HTGeometry.tendsto_prod_primesBelow_riemannZeta hk).comp (tendsto_add_atTop_nat 1)

private theorem cyclotomic_factor {p : ℕ} (hp : p.Prime) :
    (1-(p : ℝ)⁻¹+((p : ℝ)⁻¹)^2) =
      (1-(p : ℝ)⁻¹)*((1-((p : ℝ)^2)⁻¹)⁻¹*(1-((p : ℝ)^3)⁻¹)⁻¹/(1-((p : ℝ)^6)⁻¹)⁻¹) := by
  have h : (1 : ℝ)<p := by exact_mod_cast hp.one_lt
  have h₀ : (0 : ℝ)<p := one_pos.trans h
  have hd (k : ℕ) (hk : k≠0) : 1-((p : ℝ)^k)⁻¹≠0 := by
    intro he
    have hb := one_lt_pow₀ h hk
    have hpk := (pow_pos h₀ k).ne'
    field_simp at he
    linarith only [hb,he]
  let x := (p:ℝ)⁻¹
  have h₂ : 1-x^2≠0 := by simpa only [x,inv_pow] using hd 2 (by norm_num)
  have h₃ : 1-x^3≠0 := by simpa only [x,inv_pow] using hd 3 (by norm_num)
  simp only [← inv_pow]
  change 1-x+x^2=(1-x)*((1-x^2)⁻¹*(1-x^3)⁻¹/(1-x^6)⁻¹)
  calc
    _ = (1-x)*(1-x^6)/((1-x^2)*(1-x^3)) := (eq_div_iff (mul_ne_zero h₂ h₃)).2 (by ring)
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring

private theorem third_decomposition (N : ℕ) :
    (normalizedThird N : ℂ) = (RHTower.mertensPrimeProduct N : ℂ) *
      (zetaProduct 2 N * zetaProduct 3 N / zetaProduct 6 N) := by
  rw [← RHTower.primesBelow_prod_eq_mertensPrimeProduct,normalizedThird,zetaProduct,
    zetaProduct,zetaProduct]
  push_cast
  rw [← prod_mul_distrib,← prod_div_distrib,← prod_mul_distrib]
  exact prod_congr rfl fun p hp => by
    have h := congrArg Complex.ofReal (cyclotomic_factor (Nat.mem_primesBelow.mp hp).2)
    push_cast at h
    exact h

/-- The third moment has the exact zeta constant e^(−γ) ζ(2)ζ(3)/ζ(6)
after primorial and logarithmic normalization. -/
theorem third_asymptotic :
    Tendsto (fun N : ℕ => (normalizedThird N : ℂ)*(Real.log N : ℂ)) atTop
      (𝓝 ((Real.exp (-Real.eulerMascheroniConstant) : ℂ) *
        (riemannZeta 2*riemannZeta 3/riemannZeta 6))) := by
  have hm := (Complex.continuous_ofReal.tendsto _).comp RHTower.tendsto_mertensPrimeProduct_mul_log
  have h₂ := zeta_product_limit 2 (by norm_num)
  have h₃ := zeta_product_limit 3 (by norm_num)
  have h₆ := zeta_product_limit 6 (by norm_num)
  have hn : riemannZeta (6 : ℂ)≠0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  apply (hm.mul ((h₂.mul h₃).div h₆ hn)).congr
  intro n
  rw [third_decomposition]
  change ((RHTower.mertensPrimeProduct n * Real.log n : ℝ) : ℂ)*
    (zetaProduct 2 n*zetaProduct 3 n/zetaProduct 6 n) = _
  rw [Complex.ofReal_mul]
  ring

end GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments

#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.index_injective
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.supportProduct_eq
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.supportConstant_pos
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.support_asymptotic
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.support_vanishes
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.third_moment_eq
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.third_asymptotic
