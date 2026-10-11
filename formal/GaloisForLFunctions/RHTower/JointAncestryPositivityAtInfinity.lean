import GaloisForLFunctions.RHTower.JointAncestryLargePrimeMaximalExclusion
import GaloisForLFunctions.RHTower.JointAncestryWeilEulerUnconditional

/-!
# Route JAS needs positivity only at infinity

`JasDressedPSDAbove X σ` asks for positivity of the `σ`-dressed aggregate on the rational characters
supported on primes `p > X`.  The farthest-zero exclusion on large primes is unconditional, so

* `σ ≤ 1` and positivity above some `X` give RH or an off-line chain
  (`riemannHypothesis_or_chain_of_jasDressedPSDAbove`);
* **RH ⟺ (positivity at level `σ` above some `X`, for every `σ > 1`) ∧ no off-line chain**
  (`riemannHypothesis_iff_forall_gt_one_jasDressedPSDAtInfinity_and_not_chain`), and the same with
  quasi-RH in place of the chain condition;
* in Weil form (`riemannHypothesis_iff_weilEulerAtInfinity_and_not_chain`): RH holds iff there is no
  off-line chain and, for every `σ > 1`, Weil's lag form is nonnegative on every Euler vector
  `m ↦ e_w(m) m^{−σ}` supported on the integers whose prime factors all exceed some `X(σ)`.

So the existence half of the route lives entirely in the absolutely convergent range `σ > 1` and
on arbitrarily large primes.  There positivity holds unconditionally above `σ = 3/2`, and below
`3/2` it is a zero-free half-plane statement.  Without any hypothesis, positivity at infinity at
every level above `1` gives RH or a chain approaching `Re s = 1`
(`riemannHypothesis_or_forall_not_halfPlane_of_forall_jasDressedPSDAtInfinity`).
-/

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-- Positivity of the `σ`-dressed aggregate on characters supported on primes beyond some `X`. -/
def JasDressedPSDAtInfinity (σ : ℝ) : Prop := ∃ X : ℕ, JasDressedPSDAbove X σ

theorem JasDressedPSD.above {σ : ℝ} (h : JasDressedPSD σ) (X : ℕ) : JasDressedPSDAbove X σ :=
  fun S _ => h.on S

/-- **Pointwise positivity on the sub-tori of `S` forces positivity on `S`.** -/
theorem jasDressedPSDOn_of_pointwise {c : ℝ} (hc : 0 < c) (S : Finset Nat.Primes)
    (hpt : ∀ (P : Finset Nat.Primes), P ⊆ S → ∀ (w : ↥P → ℂ), (∀ i, ‖w i‖ = 1) →
      0 ≤ (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
        ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
          (w i)).re) :
    JasDressedPSDOn S (1 / 2 + c) := by
  classical
  intro ι t cc n _ hS
  set P : Finset Nat.Primes := t.biUnion (fun i => (n i).support) with hP
  have hn : ∀ i ∈ t, (n i).support ⊆ P := fun i hi p hp =>
    Finset.mem_biUnion.mpr ⟨i, hi, hp⟩
  have hc' : (1 / 2 + c - 1 / 2 : ℝ) = c := by ring
  set μ : Measure (↥P → UnitAddCircle) := Measure.pi fun _ => jasCircleHaar with hμ
  set f : (↥P → UnitAddCircle) → ℂ := fun x => ∑ i ∈ t, cc i * jasCharBar P (n i) x with hf
  set wt : XiZeroCopy → ℂ := fun q => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) with hwt
  set C : ℝ := ∏ i : ↥P, jasCircleBound c i with hC
  set Mf : ℝ := (∑ i ∈ t, ‖cc i‖) ^ 2 with hMf
  have hfc : Continuous f :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_jasCharBar P _)
  have hfb : ∀ x, ‖f x * conj (f x)‖ ≤ Mf := by
    intro x
    rw [norm_mul, Complex.norm_conj, ← sq, hMf]
    have : ‖f x‖ ≤ ∑ i ∈ t, ‖cc i‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, norm_jasCharBar, mul_one]
    gcongr
  have hre : ∀ q : XiZeroCopy, 0 < (q.1 : ℂ).re ∧ (q.1 : ℂ).re < 1 :=
    fun q => xi_divisor_support_re_mem_open_unit q.1
  -- the zero-by-zero integrands
  set F : XiZeroCopy → (↥P → UnitAddCircle) → ℂ := fun q x =>
    wt q * (f x * conj (f x) * jasSectorDensity (q.1 : ℂ) c P x) with hF
  have hFc : ∀ q, Continuous (F q) := by
    intro q
    have h0 : 0 < (q.1 : ℂ).re + c := by linarith [(hre q).1]
    have h1 : 0 < 1 - (q.1 : ℂ).re + c := by linarith [(hre q).2]
    exact continuous_const.mul ((hfc.mul (Complex.continuous_conj.comp hfc)).mul
      (continuous_jasSectorDensity h0 h1 P))
  have hFb : ∀ q x, ‖F q x‖ ≤ ‖wt q‖ * (Mf * C) := by
    intro q x
    rw [hF, norm_mul, norm_mul]
    gcongr
    · exact hfb x
    · exact norm_jasSectorDensity_le hc (hre q).1 (hre q).2 P x
  have hwsum : Summable fun q => ‖wt q‖ := summable_inv_mul_one_sub.norm
  -- the quadratic form as a zero sum of Gram integrals
  have hs : ∀ i j, Summable (fun q : XiZeroCopy => cc i * conj (cc j) *
      (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) := by
    intro i j
    have := (summable_jasDressedCoeff_term (1 / 2 + c) (n i - n j)).mul_left (cc i * conj (cc j))
    simpa only [hc'] using this
  have hQ : ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) * jasDressedLagAggregate (1 / 2 + c) (n i - n j) =
      ∑' q : XiZeroCopy, ∫ x, F q x ∂μ := by
    simp_rw [jasDressedLagAggregate_eq_tsum, hc', ← tsum_mul_left]
    have hex : ∑ i ∈ t, ∑ j ∈ t, ∑' q : XiZeroCopy, cc i * conj (cc j) *
        (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) =
        ∑' q : XiZeroCopy, ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
          (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
            ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
      rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Summable.tsum_finsetSum fun j _ => hs i j]
    rw [hex]
    refine tsum_congr fun q => ?_
    have h0 : 0 < (q.1 : ℂ).re + c := by linarith [(hre q).1]
    have h1 : 0 < 1 - (q.1 : ℂ).re + c := by linarith [(hre q).2]
    rw [hF]
    simp only
    rw [integral_const_mul, ← gram_jasDressedCoeff_eq_integral h0 h1 P t cc n hn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hwt]
    ring
  -- exchange of the zero sum and the torus integral
  have hint : ∀ q, Integrable (F q) μ := fun q =>
    (hFc q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsumint : Summable fun q => ∫ x, ‖F q x‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun x => norm_nonneg _)
      (fun q => ?_) (hwsum.mul_right (Mf * C))
    have hb := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ‖F q x‖)
      (C := ‖wt q‖ * (Mf * C)) (Filter.Eventually.of_forall fun x => by
        rw [norm_norm]; exact hFb q x)
    rw [probReal_univ, mul_one] at hb
    exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at hb)
  rw [hQ, integral_tsum_of_summable_integral_norm hint hsumint]
  -- the integrand is a nonnegative weight times the pointwise zero sum
  have hcontS : Continuous fun x => ∑' q, F q x :=
    continuous_tsum hFc (hwsum.mul_right (Mf * C)) hFb
  have hintS : Integrable (fun x => ∑' q, F q x) μ :=
    hcontS.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hreS := integral_re hintS
  simp only [RCLike.re_to_complex] at hreS
  rw [← hreS]
  refine integral_nonneg fun x => ?_
  have hPS : P ⊆ S := fun p hp => by
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    exact hS i hi hpi
  have hpx := hpt P hPS (fun i => fourier 1 (x i)) (fun i => norm_fourier_unit _ _)
  have heq : ∑' q, F q x = ((Complex.normSq (f x) : ℝ) : ℂ) *
      ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
        ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
          (fourier 1 (x i)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [hF, ← Complex.mul_conj]
    simp only
    unfold jasSectorDensity jasHoloCircle
    rw [hwt]
    ring
  show 0 ≤ (∑' q, F q x).re
  rw [heq, Complex.re_ofReal_mul]
  exact mul_nonneg (Complex.normSq_nonneg _) hpx

/-- **Unconditional exclusion at infinity.**  Positivity above some `X` at a level `σ ≤ 1` forces RH
or an off-line chain. -/
theorem riemannHypothesis_or_chain_of_jasDressedPSDAbove {X : ℕ} {σ : ℝ} (hσ : σ ≤ 1)
    (h : JasDressedPSDAbove X σ) : RiemannHypothesis ∨ JasOffLineChain := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  by_cases hch : JasOffLineChain
  · exact Or.inr hch
  obtain ⟨q₀, hoff, hmax⟩ := exists_farthest_offLine_of_not_jasOffLineChain hch hRH
  have hpos : 0 < |(q₀.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  exact absurd h (not_jasDressedPSDAbove_of_maximal_offLine X q₀ hoff hmax (by linarith))

/-- Without a chain, positivity at infinity at every level above `1` forces RH. -/
theorem riemannHypothesis_of_forall_jasDressedPSDAtInfinity_of_not_chain
    (h : ∀ σ : ℝ, 1 < σ → JasDressedPSDAtInfinity σ) (hch : ¬ JasOffLineChain) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q₀, hoff, hmax⟩ := exists_farthest_offLine_of_not_jasOffLineChain hch hRH
  have hpos : 0 < |(q₀.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  obtain ⟨X, hX⟩ := h (1 + |(q₀.1 : ℂ).re - 1 / 2| / 2) (by linarith)
  exact not_jasDressedPSDAbove_of_maximal_offLine X q₀ hoff hmax (by linarith) hX

/-- Under a half-plane bound `α < ½`, positivity at infinity at every level above `1` excludes
chains. -/
theorem not_chain_of_forall_jasDressedPSDAtInfinity_of_xiZeroHalfPlaneBound {alpha : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha)
    (h : ∀ σ : ℝ, 1 < σ → JasDressedPSDAtInfinity σ) : ¬ JasOffLineChain := by
  intro hch
  obtain ⟨q₁, hq₁⟩ := hch.1
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
  have hδ : 0 < sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hq₁)) (le_csSup hbdd ⟨q₁, rfl⟩)
  obtain ⟨X, hX⟩ := h (1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) / 2)
    (by linarith)
  have := one_add_sSup_le_of_jasDressedPSDAbove_of_chain halpha0 halpha hXi hX hch
  linarith

/-- **No hypothesis.**  Positivity at infinity at every level above `1` gives RH, or else no
half-plane bound below `½` holds (the off-line zeros approach `Re s = 1`). -/
theorem riemannHypothesis_or_forall_not_halfPlane_of_forall_jasDressedPSDAtInfinity
    (h : ∀ σ : ℝ, 1 < σ → JasDressedPSDAtInfinity σ) :
    RiemannHypothesis ∨ ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 / 2 → ¬ XiZeroHalfPlaneBound alpha := by
  by_cases hq : ∃ alpha : ℝ, 0 ≤ alpha ∧ alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha
  · obtain ⟨alpha, h0, h1, hXi⟩ := hq
    exact Or.inl (riemannHypothesis_of_forall_jasDressedPSDAtInfinity_of_not_chain h
      (not_chain_of_forall_jasDressedPSDAtInfinity_of_xiZeroHalfPlaneBound h0 h1 hXi h))
  · push Not at hq
    exact Or.inr fun alpha h0 h1 hXi => absurd hXi (hq alpha h0 h1)

theorem forall_jasDressedPSDAtInfinity_of_riemannHypothesis (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) : JasDressedPSDAtInfinity σ :=
  ⟨0, (jasDressedPSD_of_riemannHypothesis hRH hσ).above 0⟩

/-- **Capstone at infinity.**  RH holds iff there is no off-line chain and, for every `σ > 1`, the
`σ`-dressed aggregate is positive semidefinite on the characters of all sufficiently large primes. -/
theorem riemannHypothesis_iff_forall_gt_one_jasDressedPSDAtInfinity_and_not_chain :
    RiemannHypothesis ↔ (∀ σ : ℝ, 1 < σ → JasDressedPSDAtInfinity σ) ∧ ¬ JasOffLineChain :=
  ⟨fun hRH => ⟨fun σ hσ => forall_jasDressedPSDAtInfinity_of_riemannHypothesis hRH (by linarith),
      not_jasOffLineChain_of_riemannHypothesis hRH⟩,
    fun h => riemannHypothesis_of_forall_jasDressedPSDAtInfinity_of_not_chain h.1 h.2⟩

/-- **Capstone at infinity, quasi-RH form.** -/
theorem riemannHypothesis_iff_forall_gt_one_jasDressedPSDAtInfinity_and_quasi :
    RiemannHypothesis ↔ (∀ σ : ℝ, 1 < σ → JasDressedPSDAtInfinity σ) ∧
      ∃ alpha : ℝ, 0 ≤ alpha ∧ alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha := by
  constructor
  · intro hRH
    refine ⟨fun σ hσ => forall_jasDressedPSDAtInfinity_of_riemannHypothesis hRH (by linarith),
      0, le_rfl, by norm_num, fun ρ hρ => ?_⟩
    have := xi_zero_re_eq_half_of_RH hRH hρ
    linarith
  · rintro ⟨h, alpha, h0, h1, hXi⟩
    exact riemannHypothesis_of_forall_jasDressedPSDAtInfinity_of_not_chain h
      (not_chain_of_forall_jasDressedPSDAtInfinity_of_xiZeroHalfPlaneBound h0 h1 hXi h)

/-- Weil positivity on the Euler vectors of a prime set `S` gives positivity on `S`. -/
theorem jasDressedPSDOn_of_weilEulerForm_nonneg {σ : ℝ} (hσ : 1 / 2 < σ) (S : Finset Nat.Primes)
    (h : ∀ P : Finset Nat.Primes, P ⊆ S → ∀ w : ↥P → ℂ, (∀ i, ‖w i‖ = 1) →
      0 ≤ (weilEulerForm P w σ).re) : JasDressedPSDOn S σ := by
  obtain ⟨c, rfl⟩ : ∃ c, σ = 1 / 2 + c := ⟨σ - 1 / 2, by ring⟩
  have hc : 0 < c := by linarith
  refine jasDressedPSDOn_of_pointwise hc S fun P hP w hw => ?_
  have hd := jasZeroSumDensity_eq_weilEulerForm hc P hw
  unfold jasZeroSumDensity at hd
  rw [hd, ← Complex.ofReal_prod, Complex.re_ofReal_mul]
  exact mul_nonneg (prod_one_sub_exp_pos hc P).le (h P hP w hw)

/-- **Capstone at infinity, Weil form.**  RH holds iff there is no off-line chain and, for every
`σ > 1`, Weil's lag form is nonnegative on every Euler vector `m ↦ e_w(m) m^{−σ}` supported on the
integers all of whose prime factors exceed some `X(σ)`. -/
theorem riemannHypothesis_iff_weilEulerAtInfinity_and_not_chain :
    RiemannHypothesis ↔ (∀ σ : ℝ, 1 < σ → ∃ X : ℕ, ∀ P : Finset Nat.Primes,
      (∀ p ∈ P, X < (p : ℕ)) → ∀ w : ↥P → ℂ, (∀ i, ‖w i‖ = 1) → 0 ≤ (weilEulerForm P w σ).re) ∧
        ¬ JasOffLineChain := by
  rw [riemannHypothesis_iff_forall_gt_one_jasDressedPSDAtInfinity_and_not_chain]
  refine and_congr_left' (forall_congr' fun σ => forall_congr' fun hσ => ?_)
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X, fun P hP w hw => weilEulerForm_nonneg_of_on (by linarith) (hX P hP) P subset_rfl w hw⟩
  · rintro ⟨X, hX⟩
    exact ⟨X, fun S hS => jasDressedPSDOn_of_weilEulerForm_nonneg (by linarith) S
      fun P hP w hw => hX P (fun p hp => hS p (hP hp)) w hw⟩

end

end RHTower
