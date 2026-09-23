import GaloisForLFunctions.RHTower.JointAncestryGammaThetaSeparateNormalizationWall
import GaloisForLFunctions.HTGeometry.InfiniteProductNonvanishing

/-!
# JAS Gamma--theta reflection-prefix conditioning wall

After aperture-independent fourth-power renormalization, the literal synchronized-lcm Gamma
factor is `1 - D_x(p)`, where the existing sharp theorem gives `Summable D_x ↔ 1/2 < x`.
This module converts that additive wall into its exact multiplicative form. Prefix products vanish
for `x ≤ 1/2`, whereas for `x > 1/2` they converge to a nonzero infinite product. Consequently
the forward and reflected diagonal prefixes are uniformly two-sided comparable on the open strip
exactly at `x = 1/2`.

The specialization `x = 1/4` is an unconditional construction-class no-go: no divisor-independent
diagonal Gamma gauge of this literal form can implement uniformly conditioned reflection transport
throughout the strip. The positive survivor is sharp: any viable JAS producer must use genuinely
non-diagonal infinite-support polarization before the existing prime-Haar Cauchy discriminator can
force Xi divisors to the critical line.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Renormalized synchronized-lcm Gamma factor over the first `N` canonical primes. -/
def jasGammaThetaLocalRenormalizedFourthPrefix (x : ℝ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N,
    (jasGammaThetaLocalRenormalizedFourthFactor x (natEquivPrimes n) : ℂ)

/-- Uniform two-sided conditioning of forward and reflected diagonal Gamma prefixes. -/
def JASGammaThetaReflectionPrefixesUniformlyComparable (x : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ,
    c ≤ ‖jasGammaThetaLocalRenormalizedFourthPrefix x N /
      jasGammaThetaLocalRenormalizedFourthPrefix (1 - x) N‖ ∧
    c ≤ ‖jasGammaThetaLocalRenormalizedFourthPrefix (1 - x) N /
      jasGammaThetaLocalRenormalizedFourthPrefix x N‖

theorem jasGammaThetaLocalRenormalizedFourthFactor_pos
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    0 < jasGammaThetaLocalRenormalizedFourthFactor x p := by
  let q := xiMobiusContinuousApertureDiskNode x p
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hq2 : q ^ (2 : ℕ) < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hq1) (add_pos hq0 zero_lt_one)]
  rw [jasGammaThetaLocalRenormalizedFourthFactor_eq]
  change 0 < (1 - q ^ (2 : ℕ)) ^ (4 : ℕ) / (1 + q ^ (4 : ℕ))
  positivity

theorem jasGammaThetaLocalRenormalizedDefect_nonneg
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    0 ≤ jasGammaThetaLocalRenormalizedDefect x p := by
  exact (sq_nonneg (xiMobiusContinuousApertureDiskNode x p)).trans
    (xiMobiusContinuousApertureDiskNode_sq_le_jasGammaThetaLocalRenormalizedDefect hx p)

theorem jasGammaThetaLocalRenormalizedDefect_lt_one
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    jasGammaThetaLocalRenormalizedDefect x p < 1 := by
  rw [jasGammaThetaLocalRenormalizedDefect]
  linarith [jasGammaThetaLocalRenormalizedFourthFactor_pos hx p]

private theorem tendsto_jasGammaThetaPrimePrefixSets :
    Tendsto Finset.range atTop (atTop : Filter (Finset ℕ)) := by
  refine Filter.tendsto_atTop.2 fun s => ?_
  refine Filter.eventually_atTop.2 ⟨s.sup id + 1, fun N hN => ?_⟩
  intro n hn
  rw [Finset.mem_range]
  exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)) hN

private theorem tendsto_jasGammaThetaLocalRenormalizedFourthPrefix_zero_of_not_summable
    (x : ℝ) (hx : 0 < x)
    (hdiv : ¬ Summable (jasGammaThetaLocalRenormalizedDefect x)) :
    Tendsto (jasGammaThetaLocalRenormalizedFourthPrefix x) atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun n =>
    jasGammaThetaLocalRenormalizedDefect x (natEquivPrimes n)
  have hd0 : ∀ n, 0 ≤ d n := fun n => by
    exact jasGammaThetaLocalRenormalizedDefect_nonneg hx _
  have hd1 : ∀ n, d n ≤ 1 := fun n => by
    exact (jasGammaThetaLocalRenormalizedDefect_lt_one hx _).le
  have hdivNat : ¬ Summable d := by
    intro hsum
    apply hdiv
    exact (Equiv.summable_iff natEquivPrimes).mp (by
      simpa [d, Function.comp_def] using hsum)
  have hsumFinset : Tendsto (fun s : Finset ℕ => ∑ n ∈ s, d n) atTop atTop :=
    tendsto_finsetSum_atTop_of_not_summable hd0 hdivNat
  have hsum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, d n) atTop atTop :=
    hsumFinset.comp tendsto_jasGammaThetaPrimePrefixSets
  have hneg : Tendsto (fun N : ℕ => -(∑ n ∈ Finset.range N, d n)) atTop atBot := by
    rw [← tendsto_neg_atTop_iff]
    simpa using hsum
  have hexp : Tendsto (fun N : ℕ => Real.exp (-(∑ n ∈ Finset.range N, d n)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hneg
  have hupper : ∀ N : ℕ,
      ∏ n ∈ Finset.range N,
          jasGammaThetaLocalRenormalizedFourthFactor x (natEquivPrimes n) ≤
        Real.exp (-(∑ n ∈ Finset.range N, d n)) := by
    intro N
    have h := prod_one_sub_le_exp_neg (κ := (1 : ℝ)) (lam := d) 0 N
      (fun n => by simpa using hd0 n) (fun n => by simpa using hd1 n)
    simpa [d, jasGammaThetaLocalRenormalizedDefect] using h
  have hreal : Tendsto (fun N : ℕ =>
      ∏ n ∈ Finset.range N,
        jasGammaThetaLocalRenormalizedFourthFactor x (natEquivPrimes n))
      atTop (𝓝 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun N => Finset.prod_nonneg fun n _ =>
        (jasGammaThetaLocalRenormalizedFourthFactor_pos hx _).le)
      (Eventually.of_forall hupper) hexp
  have hcast := (Complex.continuous_ofReal.tendsto 0).comp hreal
  change Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N,
    (jasGammaThetaLocalRenormalizedFourthFactor x (natEquivPrimes n) : ℂ))
      atTop (𝓝 0)
  convert hcast using 1 <;> simp [Function.comp_def]

private theorem summable_norm_neg_jasGammaThetaLocalRenormalizedDefect_nat
    {x : ℝ} (hx : 0 < x) (hhalf : 1 / 2 < x) :
    Summable (fun n : ℕ =>
      ‖-((jasGammaThetaLocalRenormalizedDefect x (natEquivPrimes n) : ℝ) : ℂ)‖) := by
  have hprime : Summable (jasGammaThetaLocalRenormalizedDefect x) :=
    (summable_jasGammaThetaLocalRenormalizedDefect_iff x hx).2 hhalf
  have hnat : Summable (jasGammaThetaLocalRenormalizedDefect x ∘ natEquivPrimes) :=
    (Equiv.summable_iff natEquivPrimes).2 hprime
  refine hnat.congr fun n => ?_
  simp only [Function.comp_apply, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_of_nonneg (jasGammaThetaLocalRenormalizedDefect_nonneg hx _)).symm

/-- To the right of the half-wall, the renormalized Gamma prefix converges to its absolutely
convergent infinite product. -/
theorem tendsto_jasGammaThetaLocalRenormalizedFourthPrefix_tprod
    {x : ℝ} (hx : 0 < x) (hhalf : 1 / 2 < x) :
    Tendsto (jasGammaThetaLocalRenormalizedFourthPrefix x) atTop
      (𝓝 (∏' n : ℕ,
        (jasGammaThetaLocalRenormalizedFourthFactor x (natEquivPrimes n) : ℂ))) := by
  have hu := summable_norm_neg_jasGammaThetaLocalRenormalizedDefect_nat hx hhalf
  have hm0 : Multipliable (fun n : ℕ =>
      1 + -((jasGammaThetaLocalRenormalizedDefect x (natEquivPrimes n) : ℝ) : ℂ)) :=
    multipliable_one_add_of_summable hu
  have hm : Multipliable (fun n : ℕ =>
      (jasGammaThetaLocalRenormalizedFourthFactor x (natEquivPrimes n) : ℂ)) := by
    simpa [jasGammaThetaLocalRenormalizedDefect] using hm0
  exact hm.hasProd.comp tendsto_jasGammaThetaPrimePrefixSets

/-- The right-half-plane infinite Gamma product is nonzero. -/
theorem tprod_jasGammaThetaLocalRenormalizedFourthFactor_ne_zero
    {x : ℝ} (hx : 0 < x) (hhalf : 1 / 2 < x) :
    (∏' n : ℕ,
      (jasGammaThetaLocalRenormalizedFourthFactor x (natEquivPrimes n) : ℂ)) ≠ 0 := by
  have hu := summable_norm_neg_jasGammaThetaLocalRenormalizedDefect_nat hx hhalf
  have hne0 : ∀ n : ℕ,
      1 + -((jasGammaThetaLocalRenormalizedDefect x (natEquivPrimes n) : ℝ) : ℂ) ≠ 0 := by
    intro n
    have hpos := jasGammaThetaLocalRenormalizedFourthFactor_pos hx (natEquivPrimes n)
    rw [jasGammaThetaLocalRenormalizedDefect]
    push_cast
    simpa using Complex.ofReal_ne_zero.mpr hpos.ne'
  have hne := tprod_one_add_ne_zero_of_summable hu hne0
  simpa [jasGammaThetaLocalRenormalizedDefect] using hne

/-- Sharp product-collapse wall for the literal renormalized synchronized-lcm Gamma factors. -/
theorem tendsto_jasGammaThetaLocalRenormalizedFourthPrefix_zero_iff
    (x : ℝ) (hx : 0 < x) :
    Tendsto (jasGammaThetaLocalRenormalizedFourthPrefix x) atTop (𝓝 0) ↔
      x ≤ 1 / 2 := by
  constructor
  · intro hzero
    by_contra hnot
    have hhalf : 1 / 2 < x := lt_of_not_ge hnot
    have hlimit := tendsto_jasGammaThetaLocalRenormalizedFourthPrefix_tprod hx hhalf
    have hne := tprod_jasGammaThetaLocalRenormalizedFourthFactor_ne_zero hx hhalf
    have heq := tendsto_nhds_unique hzero hlimit
    exact hne heq.symm
  · intro hxhalf
    have hdiv : ¬ Summable (jasGammaThetaLocalRenormalizedDefect x) := by
      intro hsum
      have hright :=
        (summable_jasGammaThetaLocalRenormalizedDefect_iff x hx).1 hsum
      linarith
    exact tendsto_jasGammaThetaLocalRenormalizedFourthPrefix_zero_of_not_summable
      x hx hdiv

theorem jasGammaThetaLocalRenormalizedFourthPrefix_ne_zero
    {x : ℝ} (hx : 0 < x) (N : ℕ) :
    jasGammaThetaLocalRenormalizedFourthPrefix x N ≠ 0 := by
  induction N with
  | zero => simp [jasGammaThetaLocalRenormalizedFourthPrefix]
  | succ N ih =>
      simp only [jasGammaThetaLocalRenormalizedFourthPrefix,
        Finset.prod_range_succ] at ih ⊢
      exact mul_ne_zero ih (Complex.ofReal_ne_zero.mpr
        (jasGammaThetaLocalRenormalizedFourthFactor_pos hx (natEquivPrimes N)).ne')

/-- Below the half-wall, the forward/reflected diagonal prefix ratio collapses to zero. -/
theorem tendsto_jasGammaThetaLocalRenormalizedReflectionPrefixRatio_zero_of_lt_half
    {x : ℝ} (hx : 0 < x) (hhalf : x < 1 / 2) :
    Tendsto (fun N : ℕ =>
      jasGammaThetaLocalRenormalizedFourthPrefix x N /
        jasGammaThetaLocalRenormalizedFourthPrefix (1 - x) N)
      atTop (𝓝 0) := by
  have hy : 0 < 1 - x := by linarith
  have hyhalf : 1 / 2 < 1 - x := by linarith
  have hnum :=
    (tendsto_jasGammaThetaLocalRenormalizedFourthPrefix_zero_iff x hx).2 hhalf.le
  have hden := tendsto_jasGammaThetaLocalRenormalizedFourthPrefix_tprod hy hyhalf
  have hden0 := tprod_jasGammaThetaLocalRenormalizedFourthFactor_ne_zero hy hyhalf
  change Tendsto
    (jasGammaThetaLocalRenormalizedFourthPrefix x /
      jasGammaThetaLocalRenormalizedFourthPrefix (1 - x)) atTop (𝓝 0)
  simpa using hnum.div hden hden0

/-- Above the half-wall, the reflected/forward diagonal prefix ratio collapses to zero. -/
theorem tendsto_jasGammaThetaLocalRenormalizedReflectionPrefixRatio_zero_of_half_lt
    {x : ℝ} (hx1 : x < 1) (hhalf : 1 / 2 < x) :
    Tendsto (fun N : ℕ =>
      jasGammaThetaLocalRenormalizedFourthPrefix (1 - x) N /
        jasGammaThetaLocalRenormalizedFourthPrefix x N)
      atTop (𝓝 0) := by
  have hy : 0 < 1 - x := by linarith
  have hyhalf : 1 - x < 1 / 2 := by linarith
  have hnum :=
    (tendsto_jasGammaThetaLocalRenormalizedFourthPrefix_zero_iff (1 - x) hy).2 hyhalf.le
  have hden := tendsto_jasGammaThetaLocalRenormalizedFourthPrefix_tprod
    (lt_trans (by norm_num : 0 < (1 / 2 : ℝ)) hhalf) hhalf
  have hden0 := tprod_jasGammaThetaLocalRenormalizedFourthFactor_ne_zero
    (lt_trans (by norm_num : 0 < (1 / 2 : ℝ)) hhalf) hhalf
  change Tendsto
    (jasGammaThetaLocalRenormalizedFourthPrefix (1 - x) /
      jasGammaThetaLocalRenormalizedFourthPrefix x) atTop (𝓝 0)
  simpa using hnum.div hden hden0

/-- Uniform two-sided diagonal reflection conditioning occurs only at the reflection fixed point. -/
theorem jasGammaThetaReflectionPrefixesUniformlyComparable_iff
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    JASGammaThetaReflectionPrefixesUniformlyComparable x ↔ x = 1 / 2 := by
  constructor
  · rintro ⟨c, hc, hbound⟩
    rcases lt_trichotomy x (1 / 2 : ℝ) with hlt | heq | hgt
    · have hratio :=
        tendsto_jasGammaThetaLocalRenormalizedReflectionPrefixRatio_zero_of_lt_half hx hlt
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hratio) c hc
      have hsmall := hN N le_rfl
      rw [dist_zero_right] at hsmall
      exact False.elim ((not_lt_of_ge (hbound N).1) hsmall)
    · exact heq
    · have hratio :=
        tendsto_jasGammaThetaLocalRenormalizedReflectionPrefixRatio_zero_of_half_lt hx1 hgt
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hratio) c hc
      have hsmall := hN N le_rfl
      rw [dist_zero_right] at hsmall
      exact False.elim ((not_lt_of_ge (hbound N).2) hsmall)
  · intro heq
    subst x
    refine ⟨1, zero_lt_one, fun N => ?_⟩
    have hne := jasGammaThetaLocalRenormalizedFourthPrefix_ne_zero
      (x := (1 / 2 : ℝ)) (by norm_num) N
    norm_num
    have hnorm : ‖jasGammaThetaLocalRenormalizedFourthPrefix (1 / 2) N‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hne
    rw [div_self hnorm]

/-- Unconditional construction-class no-go: the diagonal Gamma reflection transport cannot be
uniformly conditioned throughout the open strip. -/
theorem not_forall_openStrip_jasGammaThetaReflectionPrefixesUniformlyComparable :
    ¬ ∀ x : ℝ, 0 < x → x < 1 →
      JASGammaThetaReflectionPrefixesUniformlyComparable x := by
  intro h
  have hquarter := h (1 / 4) (by norm_num) (by norm_num)
  have heq := (jasGammaThetaReflectionPrefixesUniformlyComparable_iff
    (1 / 4) (by norm_num) (by norm_num)).1 hquarter
  norm_num at heq

end

end RHTower
