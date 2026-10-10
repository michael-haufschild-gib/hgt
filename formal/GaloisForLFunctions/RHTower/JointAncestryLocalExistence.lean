import GaloisForLFunctions.RHTower.JointAncestryDressingTwoExistence

/-!
# Local existence at the target dressing `σ = 1`

Restrict the dressed aggregate to rational characters supported on a fixed finite set `S` of
primes.  At `σ = 1` (`c = ½`) the two radii of a zero `ρ = β + iγ` at a prime `p` are
`r₁ = p^{−(β+½)}`, `r₂ = p^{−(3/2−β)}`: both lie in `[t³, t]` with `t = p^{−1/2}` and `r₁ r₂ = t⁴`.
Hence `r₁² + r₂² ≤ t² + t⁶`, and the local phase width obeys the sharp bound

`tan W_p ≤ √(p / (p² + p + 1))`

(attained as `β → 0, 1`).  So whenever `Σ_{p ∈ S} √(p/(p²+p+1)) + 1/14 ≤ π/2` every zero has a
nonnegative sector on `S`, and the aggregate restricted to `S` is positive semidefinite at `σ = 1`,
unconditionally (`jasDressedPSDOn_one_of_sum_le`).  This covers `S = {2, 3, 5}`
(`jasDressedPSDOn_one_two_three_five`).

Full existence at `σ = 1` needs every finite `S`.  The per-zero bound cannot provide it, since
`Σ_p √(p/(p²+p+1)) = ∞`: off-line zeros near the edge of the strip can rotate their own sector by
an unbounded angle once enough primes are used.  The open content of JAS existence is therefore
compensation between zeros over infinitely many primes.
-/

open Complex MeasureTheory
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Positivity of the dressed aggregate on characters supported in `S`. -/
def JasDressedPSDOn (S : Finset Nat.Primes) (σ : ℝ) : Prop :=
  ∀ (ι : Type) (t : Finset ι) (c : ι → ℂ) (n : ι → Nat.Primes →₀ ℤ), Set.InjOn n t →
    (∀ i ∈ t, (n i).support ⊆ S) →
      0 ≤ (∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasDressedLagAggregate σ (n i - n j)).re

theorem JasDressedPSD.on {σ : ℝ} (h : JasDressedPSD σ) (S : Finset Nat.Primes) :
    JasDressedPSDOn S σ := fun ι t c n hinj _ => h ι t c n hinj

/-- **Per-zero phase budgets on `S` force positivity on `S`.** -/
theorem jasDressedPSDOn_of_phaseBudget {c : ℝ} (hc : 0 < c) (S : Finset Nat.Primes)
    (hbudget : ∀ q : XiZeroCopy,
      |(1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).arg| +
        ∑ p ∈ S, jasPhaseWidth (jasR1 ((q.1 : ℂ) + c) p) (jasR2 ((q.1 : ℂ) - c) p) ≤ Real.pi / 2) :
    JasDressedPSDOn S (1 / 2 + c) := by
  classical
  intro ι t cc n _ hn
  have hc' : (1 / 2 + c - 1 / 2 : ℝ) = c := by ring
  have hs : ∀ i j, Summable (fun q : XiZeroCopy => cc i * conj (cc j) *
      (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) := by
    intro i j
    have := (summable_jasDressedCoeff_term (1 / 2 + c) (n i - n j)).mul_left (cc i * conj (cc j))
    simpa only [hc'] using this
  have hswap : ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) * jasDressedLagAggregate (1 / 2 + c) (n i - n j) =
      ∑' q : XiZeroCopy, ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
        (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    simp_rw [jasDressedLagAggregate_eq_tsum, hc', ← tsum_mul_left]
    rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum fun j _ => hs i j]
  have hsumm : Summable (fun q : XiZeroCopy => ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
      (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) :=
    summable_sum fun i _ => summable_sum fun j _ => hs i j
  rw [hswap, Complex.re_tsum hsumm]
  refine tsum_nonneg fun q => ?_
  have h0 : 0 < (q.1 : ℂ).re + c := by
    linarith [(xi_divisor_support_re_mem_open_unit q.1).1]
  have h1 : 0 < 1 - (q.1 : ℂ).re + c := by
    linarith [(xi_divisor_support_re_mem_open_unit q.1).2]
  set w : ℂ := 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) with hw
  have hterm : ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
      (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) =
      w * ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
        jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hw]; ring
  rw [hterm, gram_jasDressedCoeff_eq_integral h0 h1 S t cc n hn, ← integral_const_mul]
  set f : (↥S → UnitAddCircle) → ℂ := fun x => ∑ i ∈ t, cc i * jasCharBar S (n i) x with hf
  have hcont : Continuous fun x => w * (f x * conj (f x) * jasSectorDensity (q.1 : ℂ) c S x) := by
    refine continuous_const.mul ?_
    have hfc : Continuous f :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_jasCharBar S _)
    exact (hfc.mul (Complex.continuous_conj.comp hfc)).mul (continuous_jasSectorDensity h0 h1 S)
  have hint := hcont.integrable_of_hasCompactSupport (μ := Measure.pi fun _ => jasCircleHaar)
    (HasCompactSupport.of_compactSpace _)
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  refine integral_nonneg fun x => ?_
  have hpos := re_mul_jasSectorDensity_nonneg h0 h1 S (hbudget q) x
  rw [show w * (f x * conj (f x) * jasSectorDensity (q.1 : ℂ) c S x) =
      ((Complex.normSq (f x) : ℝ) : ℂ) * (w * jasSectorDensity (q.1 : ℂ) c S x) by
    rw [← Complex.mul_conj]; ring, Complex.re_ofReal_mul]
  exact mul_nonneg (Complex.normSq_nonneg _) hpos

/-! ## The sharp local width at `σ = 1` -/

/-- Two radii in `[t³, t]` with product `t⁴` have phase width at most
`arctan √(t²/(1 + t² + t⁴))`, hence at most `√(t²/(1 + t² + t⁴))`. -/
theorem jasPhaseWidth_le_of_product {r₁ r₂ t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h₁ : r₁ ≤ t) (h₂ : r₂ ≤ t) (h₁' : t ^ 3 ≤ r₁) (h₂' : t ^ 3 ≤ r₂)
    (hprod : r₁ * r₂ = t ^ 4) :
    jasPhaseWidth r₁ r₂ ≤ Real.sqrt (t ^ 2 / (1 + t ^ 2 + t ^ 4)) := by
  unfold jasPhaseWidth
  have hr₁0 : 0 < r₁ := lt_of_lt_of_le (by positivity) h₁'
  have hr₂0 : 0 < r₂ := lt_of_lt_of_le (by positivity) h₂'
  -- `r₁² + r₂² ≤ t² + t⁶`
  have hs : r₁ ^ 2 + r₂ ^ 2 ≤ t ^ 2 + t ^ 6 := by
    have hm : 0 ≤ (t ^ 2 - r₁ ^ 2) * (t ^ 2 - r₂ ^ 2) :=
      mul_nonneg (by nlinarith) (by nlinarith)
    have hp2 : r₁ ^ 2 * r₂ ^ 2 = t ^ 8 := by
      rw [← mul_pow, hprod]; ring
    have ht2 : 0 < t ^ 2 := by positivity
    nlinarith
  have hD : 0 < (1 - r₁ ^ 2) * (1 - r₂ ^ 2) := mul_pos (by nlinarith) (by nlinarith)
  have hDexp : (1 - r₁ ^ 2) * (1 - r₂ ^ 2) = 1 - (r₁ ^ 2 + r₂ ^ 2) + t ^ 8 := by
    have h8 : r₁ ^ 2 * r₂ ^ 2 = t ^ 8 := by rw [← mul_pow, hprod]; ring
    linear_combination h8
  have hN : |r₁ - r₂| ^ 2 = (r₁ ^ 2 + r₂ ^ 2) - 2 * t ^ 4 := by
    rw [sq_abs]; nlinarith [hprod]
  -- the squared ratio is increasing in `s = r₁² + r₂²`; evaluate at `s = t² + t⁶`
  have hratio_sq : (|r₁ - r₂| / Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2))) ^ 2 ≤
      t ^ 2 / (1 + t ^ 2 + t ^ 4) := by
    rw [div_pow, Real.sq_sqrt hD.le, hN, hDexp]
    have hden2 : 0 < 1 + t ^ 2 + t ^ 4 := by positivity
    have hden1 : 0 < 1 - (r₁ ^ 2 + r₂ ^ 2) + t ^ 8 := by rw [← hDexp]; exact hD
    rw [div_le_div_iff₀ hden1 hden2]
    have ht6 : t ^ 6 < 1 := by
      have : t ^ 6 < 1 ^ 6 := pow_lt_pow_left₀ ht1 ht0.le (by norm_num)
      simpa using this
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 1 - t ^ 6 by linarith),
      sq_nonneg t, sq_nonneg (t ^ 2), pow_pos ht0 2, pow_pos ht0 4, pow_pos ht0 6]
  have hratio_nn : 0 ≤ |r₁ - r₂| / Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by positivity
  have hratio : |r₁ - r₂| / Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) ≤
      Real.sqrt (t ^ 2 / (1 + t ^ 2 + t ^ 4)) :=
    Real.le_sqrt_of_sq_le hratio_sq
  exact (arctan_le_self_of_nonneg' hratio_nn).trans hratio

/-- `p^{−1/2}`. -/
def jasHalfRadius (p : Nat.Primes) : ℝ := Real.exp (-(1 / 2) * Real.log p)

theorem jasHalfRadius_pos (p : Nat.Primes) : 0 < jasHalfRadius p := Real.exp_pos _

theorem jasHalfRadius_lt_one (p : Nat.Primes) : jasHalfRadius p < 1 := by
  unfold jasHalfRadius
  rw [Real.exp_lt_one_iff]
  nlinarith [log_prime_pos p]

theorem jasHalfRadius_sq (p : Nat.Primes) : jasHalfRadius p ^ 2 = ((p : ℕ) : ℝ)⁻¹ := by
  unfold jasHalfRadius
  rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(1 / 2) * Real.log p) = -Real.log p by
    push_cast; ring, Real.exp_neg, Real.exp_log (by exact_mod_cast (p : Nat.Primes).2.pos)]

/-- **The local width at `σ = 1` is at most `√(p/(p²+p+1))`.** -/
theorem jasHalfRadius_pow (p : Nat.Primes) (k : ℕ) :
    jasHalfRadius p ^ k = Real.exp (-((k : ℝ) / 2) * Real.log p) := by
  unfold jasHalfRadius
  rw [← Real.exp_nat_mul]
  congr 1; ring

theorem jasPhaseWidth_one_le (q : XiZeroCopy) (p : Nat.Primes) :
    jasPhaseWidth (jasR1 ((q.1 : ℂ) + ((1 / 2 : ℝ) : ℂ)) p)
        (jasR2 ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ)) p) ≤
      Real.sqrt (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) ^ 2 + (p : ℕ) + 1)) := by
  obtain ⟨hβ0, hβ1⟩ := xiZeroCopy_re_mem_open_unit q
  have hl := log_prime_pos p
  have hr₁ : jasR1 ((q.1 : ℂ) + ((1 / 2 : ℝ) : ℂ)) p =
      Real.exp (-(((q.1 : ℂ)).re + 1 / 2) * Real.log p) := jasR1_dressed _ _ _
  have hr₂ : jasR2 ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ)) p =
      Real.exp (-(1 - ((q.1 : ℂ)).re + 1 / 2) * Real.log p) := jasR2_dressed _ _ _
  have e1 : jasHalfRadius p = Real.exp (-(1 / 2) * Real.log p) := rfl
  have e3 := jasHalfRadius_pow p 3
  have e4 := jasHalfRadius_pow p 4
  have hw := jasPhaseWidth_le_of_product (r₁ := jasR1 ((q.1 : ℂ) + ((1 / 2 : ℝ) : ℂ)) p)
    (r₂ := jasR2 ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ)) p) (jasHalfRadius_pos p) (jasHalfRadius_lt_one p)
    (by rw [hr₁, e1]; exact Real.exp_le_exp.mpr (by nlinarith))
    (by rw [hr₂, e1]; exact Real.exp_le_exp.mpr (by nlinarith))
    (by rw [hr₁, e3]; exact Real.exp_le_exp.mpr (by push_cast; nlinarith))
    (by rw [hr₂, e3]; exact Real.exp_le_exp.mpr (by push_cast; nlinarith))
    (by rw [hr₁, hr₂, e4, ← Real.exp_add]; congr 1; push_cast; ring)
  refine hw.trans (le_of_eq ?_)
  congr 1
  have h2 := jasHalfRadius_sq p
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (p : Nat.Primes).2.pos
  have h4 : jasHalfRadius p ^ 4 = (((p : ℕ) : ℝ)⁻¹) ^ 2 := by
    rw [show jasHalfRadius p ^ 4 = (jasHalfRadius p ^ 2) ^ 2 by ring, h2]
  rw [h4, h2]
  field_simp

/-- **Local existence at `σ = 1`.** -/
theorem jasDressedPSDOn_one_of_sum_le (S : Finset Nat.Primes)
    (hS : ∑ p ∈ S, Real.sqrt (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) ^ 2 + (p : ℕ) + 1)) + 1 / 14 ≤
      Real.pi / 2) :
    JasDressedPSDOn S 1 := by
  have h := jasDressedPSDOn_of_phaseBudget (c := 1 / 2) (by norm_num) S fun q => by
    have harg := abs_arg_jasWeight_le q
    have hw := Finset.sum_le_sum fun p (_ : p ∈ S) => jasPhaseWidth_one_le q p
    linarith
  norm_num at h
  exact h

theorem sqrt_div_sqrt_le {a b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (h : a ≤ c ^ 2 * b) :
    Real.sqrt a / Real.sqrt b ≤ c := by
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hb)]
  calc Real.sqrt a ≤ Real.sqrt (c ^ 2 * b) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt b := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- **Positivity at `σ = 1` on the `{2, 3, 5}`-characters, unconditionally.** -/
theorem jasDressedPSDOn_one_two_three_five :
    JasDressedPSDOn {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩, ⟨5, Nat.prime_five⟩} 1 := by
  refine jasDressedPSDOn_one_of_sum_le _ ?_
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num
  have h2 : Real.sqrt 2 / Real.sqrt 7 ≤ 0.54 := sqrt_div_sqrt_le (by norm_num) (by norm_num) (by norm_num)
  have h3 : Real.sqrt 3 / Real.sqrt 13 ≤ 0.49 :=
    sqrt_div_sqrt_le (by norm_num) (by norm_num) (by norm_num)
  have h5 : Real.sqrt 5 / Real.sqrt 31 ≤ 0.41 :=
    sqrt_div_sqrt_le (by norm_num) (by norm_num) (by norm_num)
  have hpi := Real.pi_gt_d2
  linarith

end

end RHTower
