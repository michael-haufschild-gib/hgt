import Mathlib

/-!
# The kernel `1/(1 − xy)` on the unit square

Beukers' proof that `ζ(2)` has finite irrationality exponent rests on the integrals
`J(r, s) = ∫₀¹∫₀¹ xʳ yˢ /(1 − xy) dx dy = Σ_{k ≥ 0} 1/((k + r + 1)(k + s + 1))`.

* `integral_pow_div_one_sub_mul` : for `0 ≤ y < 1`, `∫₀¹ xʳ/(1 − xy) dx = Σ_k yᵏ/(r + k + 1)`.
* `kernelPair_self` : `J(r, r) = π²/6 − Σ_{j ≤ r} 1/j²`.
* `kernelPair_of_lt` : for `s < r`, `J(r, s) = (Σ_{j=s+1}^{r} 1/j)/(r − s)`.
* `integrable_tsum_of_nonneg` : a nonnegative series of integrable functions with summable
  integrals is integrable.
-/

open MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.HTGeometry.BeukersZetaTwo

/-- A nonnegative series of integrable functions with summable integrals is integrable. -/
theorem integrable_tsum_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} (hF : ∀ i, Integrable (F i) μ) (h0 : ∀ i a, 0 ≤ F i a)
    (hs : ∀ᵐ a ∂μ, Summable fun i => F i a) (hsum : Summable fun i => ∫ a, F i a ∂μ) :
    Integrable (fun a => ∑' i, F i a) μ := by
  have hmeas : AEStronglyMeasurable (fun a => ∑' i, F i a) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N a => ∑ i ∈ Finset.range N, F i a)
      (fun N => (integrable_finsetSum _ fun i _ => hF i).aestronglyMeasurable) ?_
    filter_upwards [hs] with a ha
    exact ha.hasSum.tendsto_sum_nat
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  have hpt : ∀ᵐ a ∂μ, ‖∑' i, F i a‖ₑ = ∑' i, ENNReal.ofReal (F i a) := by
    filter_upwards [hs] with a ha
    rw [Real.enorm_eq_ofReal (tsum_nonneg fun i => h0 i a), ENNReal.ofReal_tsum_of_nonneg
      (fun i => h0 i a) ha]
  rw [lintegral_congr_ae hpt, lintegral_tsum fun i =>
    (hF i).aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  have hi : ∀ i, ∫⁻ a, ENNReal.ofReal (F i a) ∂μ = ENNReal.ofReal (∫ a, F i a ∂μ) := fun i =>
    (ofReal_integral_eq_lintegral_ofReal (hF i) (Eventually.of_forall fun a => h0 i a)).symm
  simp_rw [hi]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun a => h0 i a) hsum]
  exact ENNReal.ofReal_lt_top

/-- `Σ_k yᵏ/(r + k + 1)`, the inner kernel integral. -/
noncomputable def kernelInner (r : ℕ) (y : ℝ) : ℝ := ∑' k : ℕ, y ^ k / ((r : ℝ) + k + 1)

theorem integral_pow_Ioc (m : ℕ) : ∫ x in Ioc (0 : ℝ) 1, x ^ m = 1 / ((m : ℝ) + 1) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  simp

theorem integrableOn_pow_Ioc (m : ℕ) (c : ℝ) :
    Integrable (fun x : ℝ => x ^ m * c) (volume.restrict (Ioc (0 : ℝ) 1)) :=
  ((continuous_pow m).mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- **Inner kernel integral.**  For `0 ≤ y < 1`, `∫₀¹ xʳ/(1 − xy) dx = Σ_k yᵏ/(r + k + 1)`. -/
theorem integral_pow_div_one_sub_mul {r : ℕ} {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y) = kernelInner r y := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  set F : ℕ → ℝ → ℝ := fun k x => x ^ (r + k) * y ^ k with hFdef
  have hF : ∀ k, Integrable (F k) (volume.restrict (Ioc (0 : ℝ) 1)) := fun k =>
    integrableOn_pow_Ioc (r + k) (y ^ k)
  have hint : ∀ k : ℕ, ∫ x in Ioc (0 : ℝ) 1, F k x = y ^ k / ((r : ℝ) + k + 1) := by
    intro k
    simp only [hFdef]
    rw [integral_mul_const, integral_pow_Ioc]
    push_cast
    ring
  have hnorm : ∀ k : ℕ, ∫ x in Ioc (0 : ℝ) 1, ‖F k x‖ = y ^ k / ((r : ℝ) + k + 1) := by
    intro k
    rw [← hint k]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    simp only [hFdef, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (pow_nonneg hx.1.le _) (pow_nonneg hy0 _))
  have hsum : Summable fun k : ℕ => y ^ k / ((r : ℝ) + k + 1) :=
    (summable_geometric_of_lt_one hy0 hy1).of_nonneg_of_le (fun k => by positivity)
      fun k => div_le_self (pow_nonneg hy0 k) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k),
        (Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
  have h := hasSum_integral_of_summable_integral_norm hF (by simp_rw [hnorm]; exact hsum)
  have hpt : ∀ x ∈ Ioc (0 : ℝ) 1, x ^ r / (1 - x * y) = ∑' k, F k x := by
    intro x hx
    have hxy0 : 0 ≤ x * y := mul_nonneg hx.1.le hy0
    have hxy1 : x * y < 1 := by nlinarith [hx.2]
    simp only [hFdef]
    have e : ∀ k : ℕ, x ^ (r + k) * y ^ k = x ^ r * (x * y) ^ k := fun k => by ring
    simp_rw [e]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hxy0 hxy1, div_eq_mul_inv]
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, ← h.tsum_eq]
  simp_rw [hint]
  rfl

/-- `J(r, s) = Σ_k 1/((k + r + 1)(k + s + 1))`. -/
noncomputable def kernelPair (r s : ℕ) : ℝ :=
  ∑' k : ℕ, 1 / (((k : ℝ) + r + 1) * ((k : ℝ) + s + 1))

theorem kernelPair_term_le (r s k : ℕ) :
    1 / (((k : ℝ) + r + 1) * ((k : ℝ) + s + 1)) ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem summable_kernelPair (r s : ℕ) :
    Summable fun k : ℕ => 1 / (((k : ℝ) + r + 1) * ((k : ℝ) + s + 1)) := by
  have h2 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  exact h2.of_nonneg_of_le (fun k => by positivity) (kernelPair_term_le r s)

/-- **Outer kernel integral.**  `∫₀¹ yˢ (Σ_k yᵏ/(r + k + 1)) dy = J(r, s)`, and the integrand is
integrable. -/
theorem integral_pow_mul_kernelInner (r s : ℕ) :
    Integrable (fun y => y ^ s * kernelInner r y) (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      ∫ y in Ioc (0 : ℝ) 1, y ^ s * kernelInner r y = kernelPair r s := by
  set G : ℕ → ℝ → ℝ := fun k y => y ^ (s + k) * (1 / ((r : ℝ) + k + 1)) with hGdef
  have hG : ∀ k, Integrable (G k) (volume.restrict (Ioc (0 : ℝ) 1)) := fun k =>
    integrableOn_pow_Ioc (s + k) _
  have hint : ∀ k : ℕ, ∫ y in Ioc (0 : ℝ) 1, G k y =
      1 / (((k : ℝ) + r + 1) * ((k : ℝ) + s + 1)) := by
    intro k
    simp only [hGdef]
    rw [integral_mul_const, integral_pow_Ioc]
    push_cast
    field_simp
    ring
  have hG0 : ∀ k y, y ∈ Ioc (0 : ℝ) 1 → 0 ≤ G k y := fun k y hy => by
    simp only [hGdef]; exact mul_nonneg (pow_nonneg hy.1.le _) (by positivity)
  have hsumint : Summable fun k => ∫ y in Ioc (0 : ℝ) 1, G k y := by
    simp_rw [hint]; exact summable_kernelPair r s
  have hpt : ∀ y ∈ Ioo (0 : ℝ) 1, y ^ s * kernelInner r y = ∑' k, G k y := by
    intro y hy
    simp only [hGdef, kernelInner]
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [pow_add]; ring
  have hae : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      y ^ s * kernelInner r y = ∑' k, G k y := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 1 := ae_iff.mpr (by simp)
    filter_upwards [hne] with y hy1 hy
    exact hpt y ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩
  -- the series of nonnegative integrable functions
  have hsumm : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)), Summable fun k => G k y := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 1 := ae_iff.mpr (by simp)
    filter_upwards [hne] with y hy1 hy
    have hy1' : y < 1 := lt_of_le_of_ne hy.2 hy1
    simp only [hGdef]
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      ((summable_geometric_of_lt_one hy.1.le hy1').mul_left (y ^ s))
    · exact mul_nonneg (pow_nonneg hy.1.le _) (by positivity)
    rw [pow_add]
    have : 1 / ((r : ℝ) + k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k),
        (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    have hp : 0 ≤ y ^ s * y ^ k := mul_nonneg (pow_nonneg hy.1.le _) (pow_nonneg hy.1.le _)
    nlinarith
  -- restrict to the nonnegative representatives on `Ioc 0 1`
  set G' : ℕ → ℝ → ℝ := fun k y => if y ∈ Ioc (0 : ℝ) 1 then G k y else 0 with hG'def
  have hGG' : ∀ k, G k =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] G' k := fun k => by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun y hy => by simp only [hG'def, if_pos hy]
  have hG'int : ∀ k, Integrable (G' k) (volume.restrict (Ioc (0 : ℝ) 1)) := fun k =>
    (hG k).congr (hGG' k)
  have hG'0 : ∀ k y, 0 ≤ G' k y := fun k y => by
    simp only [hG'def]; split_ifs with h
    · exact hG0 k y h
    · exact le_refl 0
  have hG'sum : Summable fun k => ∫ y in Ioc (0 : ℝ) 1, G' k y := by
    refine hsumint.congr fun k => ?_
    exact integral_congr_ae (hGG' k)
  have hG'summ : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)), Summable fun k => G' k y := by
    have hmem : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)), y ∈ Ioc (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hsumm, hmem] with y hy hymem
    simp only [hG'def, if_pos hymem]
    exact hy
  have hInt := integrable_tsum_of_nonneg hG'int hG'0 hG'summ hG'sum
  have hae' : (fun y => y ^ s * kernelInner r y) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun y => ∑' k, G' k y := by
    have hmem : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)), y ∈ Ioc (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hae, hmem] with y hy hymem
    rw [hy]
    simp only [hG'def, if_pos hymem]
  refine ⟨hInt.congr hae'.symm, ?_⟩
  rw [integral_congr_ae hae']
  have h := hasSum_integral_of_summable_integral_norm hG'int
    (by
      refine hG'sum.congr fun k => ?_
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [Real.norm_eq_abs, abs_of_nonneg (hG'0 k y)])
  rw [← h.tsum_eq, kernelPair]
  refine tsum_congr fun k => ?_
  rw [← hint k]
  exact (integral_congr_ae (hGG' k)).symm

/-- **Diagonal value.**  `J(r, r) = π²/6 − Σ_{j ≤ r} 1/j²`. -/
theorem kernelPair_self (r : ℕ) :
    kernelPair r r = Real.pi ^ 2 / 6 - ∑ j ∈ Finset.range (r + 1), 1 / (j : ℝ) ^ 2 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add (r + 1)
  rw [hasSum_zeta_two.tsum_eq] at h
  rw [← h, add_sub_cancel_left, kernelPair]
  refine tsum_congr fun k => ?_
  push_cast
  ring

/-- **Off-diagonal value.**  For `s < r`, `J(r, s) = (Σ_{j=s+1}^{r} 1/j)/(r − s)`. -/
theorem kernelPair_of_lt {r s : ℕ} (hsr : s < r) :
    kernelPair r s = (∑ j ∈ Finset.Ico (s + 1) (r + 1), 1 / (j : ℝ)) / ((r : ℝ) - s) := by
  set d := r - s with hd
  have hdpos : 0 < d := by omega
  have hrs : (r : ℝ) - s = d := by rw [hd]; push_cast [hsr.le]; ring
  -- partial fractions
  have hpf : ∀ k : ℕ, 1 / (((k : ℝ) + r + 1) * ((k : ℝ) + s + 1)) =
      (1 / ((k : ℝ) + s + 1) - 1 / ((k : ℝ) + s + 1 + d)) / d := by
    intro k
    have hr : (r : ℝ) = s + d := by rw [← hrs]; ring
    rw [hr]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    field_simp
    ring
  -- telescoping
  set g : ℕ → ℝ := fun k => 1 / ((k : ℝ) + s + 1) with hg
  have htel : HasSum (fun k : ℕ => g k - g (k + d)) (∑ k ∈ Finset.range d, g k) := by
    have hg0 : Tendsto g atTop (𝓝 0) := by
      have : Tendsto (fun k : ℕ => (k : ℝ) + s + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
          tendsto_natCast_atTop_atTop)
      refine this.inv_tendsto_atTop.congr fun k => ?_
      simp [hg]
    have hnn : ∀ k, 0 ≤ g k - g (k + d) := fun k => by
      simp only [hg]
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    have hpart : ∀ N, ∑ k ∈ Finset.range N, (g k - g (k + d)) =
        ∑ k ∈ Finset.range d, g k - ∑ k ∈ Finset.range d, g (N + k) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        have e1 := Finset.sum_range_succ (fun k => g (N + k)) d
        have e2 := Finset.sum_range_succ' (fun k => g (N + k)) d
        simp only [add_zero] at e2
        have e3 : ∑ k ∈ Finset.range d, g (N + (k + 1)) = ∑ k ∈ Finset.range d, g (N + 1 + k) :=
          Finset.sum_congr rfl fun k _ => by rw [show N + (k + 1) = N + 1 + k by ring]
        rw [show N + d = N + d from rfl] at e1
        linarith [e1, e2, e3, show g (N + d) = g (N + d) from rfl]
    simp_rw [hpart]
    have hlim : Tendsto (fun N => ∑ k ∈ Finset.range d, g (N + k)) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.range d) fun k _ =>
        hg0.comp (tendsto_add_atTop_nat k)
      simpa [Function.comp, add_comm] using this
    simpa using tendsto_const_nhds.sub hlim
  have hval : ∑ k ∈ Finset.range d, g k = ∑ j ∈ Finset.Ico (s + 1) (r + 1), 1 / (j : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range, show r + 1 - (s + 1) = d by omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hg]; push_cast; ring
  rw [kernelPair]
  have hsum := (htel.div_const (d : ℝ)).tsum_eq
  rw [← hval, hrs, ← hsum]
  refine tsum_congr fun k => ?_
  rw [hpf]
  simp only [hg]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry.BeukersZetaTwo
