import GaloisForLFunctions.SurfaceOfSpecZ.TheTensorPowersHaveACommonAbscissa
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheReflectionSectorsOfTheHodgeDefect

/-!
# The primes in a residue class, from both sides

* **Removing a convergent part keeps a weight sampling** (`SamplingWeight.of_le_of_summable_sub`):
  if `w` is sampling, `0 ≤ w' ≤ w` and `Σ (w − w')(n)/n < ∞`, then `w'` is sampling. Hence the
  primes alone in a residue class, `log p · 1_{p ≡ a}`, are sampling (`samplingWeight_primeResidue`):
  the prime powers `pᵏ`, `k ≥ 2`, have a convergent series at `s = 1`.
* **The upper side at sampling sets** (`onLine_of_bddAbove_of_samplingWeight`): an upper bound on
  the spline traces where a sampling weight is nonzero puts every zero of a tempered configuration
  with attained maximal real part on the line, real zeros included. The mean of `F` tends to the real
  top coefficient `e_b ≥ 0` (`tendsto_wMean_real`), the bound forces `e_b = 0`, and then
  `F² ≤ E(2|K|n^{−b} − F)` kills `Σ_{Re z = b}|e_z|²`.
* **For `ζ`** (`exists_re_gt_of_bddBelow_primes_mod`, `exists_re_gt_of_bddAbove_primes_mod`): a
  bound from either side at the primes `p ≡ a (mod q)` leaves no deepest off-line zero: every zero
  right of the line is exceeded by another. Hence
  (`riemannHypothesis_iff_bddBelow_primes_mod_and_topAttained`) RH holds iff the traces are bounded
  below at the primes `p ≡ a (mod q)` and the off-line zeros, if any, have one of largest real part;
  the same from above.

The Dirichlet series of these degrees carries the zeros of every `L(s, χ)` mod `q`, which is why the
Landau route of the prime degrees does not apply and attainment enters. The two sides of `ζ` agree
here because `ζ` has no real zeros in the strip.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ArithmeticFunction

/-! ### Perturbing a sampling weight -/

theorem summable_wSeries_of_le {v : ℕ → ℝ} (h0 : ∀ j, 0 ≤ v j) (hle : ∀ j, v j ≤ Λ (j + 1))
    {s : ℂ} (hs : 1 < s.re) : Summable fun j : ℕ => (v j : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
  refine Summable.of_norm_bounded (summable_vonMangoldt_rpow hs) fun j => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 j),
    norm_natCast_add_one_cpow, Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (hle j) (by positivity)

/-- **Removing a convergent part keeps a weight sampling.** -/
theorem SamplingWeight.of_le_of_summable_sub {w w' : ℕ → ℝ} (hw : SamplingWeight w)
    (h0 : ∀ j, 0 ≤ w' j) (hle : ∀ j, w' j ≤ w j)
    (hsum : Summable fun j : ℕ => (w j - w' j) * ((j : ℝ) + 1) ^ (-(1 : ℝ))) :
    SamplingWeight w' := by
  set h : ℕ → ℝ := fun j => w j - w' j with hhdef
  have hh0 : ∀ j, 0 ≤ h j := fun j => sub_nonneg.mpr (hle j)
  have hhw : ∀ j, h j ≤ w j := fun j => by have := h0 j; simp only [hhdef]; linarith
  have hw's : ∀ σ : ℝ, 1 < σ → Summable fun j : ℕ => w' j * ((j : ℝ) + 1) ^ (-σ) := fun σ hσ =>
    Summable.of_nonneg_of_le (fun j => mul_nonneg (h0 j) (by positivity))
      (fun j => mul_le_mul_of_nonneg_right (hle j) (by positivity)) (hw.summable hσ)
  set H := ∑' j : ℕ, h j * ((j : ℝ) + 1) ^ (-(1 : ℝ)) with hHdef
  -- the removed part is bounded by `H` on `Re s ≥ 1`
  have hpow : ∀ j : ℕ, ∀ t : ℝ, 1 ≤ t → ((j : ℝ) + 1) ^ (-t) ≤ ((j : ℝ) + 1) ^ (-(1 : ℝ)) :=
    fun j t ht => Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j])
      (by linarith)
  have hhs : ∀ t : ℝ, 1 ≤ t → Summable fun j : ℕ => h j * ((j : ℝ) + 1) ^ (-t) := fun t ht =>
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hh0 j) (by positivity))
      (fun j => mul_le_mul_of_nonneg_left (hpow j t ht) (hh0 j)) hsum
  have hHb : ∀ t : ℝ, 1 ≤ t → wSum h t ≤ H := fun t ht =>
    Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hpow j t ht) (hh0 j)) (hhs t ht)
      hsum
  have hsub : ∀ σ : ℝ, 1 < σ → wSum w' σ = wSum w σ - wSum h σ := by
    intro σ hσ
    rw [wSum, wSum, wSum, ← (hw.summable hσ).tsum_sub (hhs σ hσ.le)]
    refine tsum_congr fun j => ?_
    simp only [hhdef]; ring
  have hatTop : Tendsto (wSum w') (𝓝[>] 1) atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-H) hw.tendsto_atTop)
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [hsub σ hσ]
    linarith [hHb σ (le_of_lt hσ)]
  refine ⟨h0, hw's, hatTop, fun c hc hre => ?_⟩
  have hsubC : ∀ σ : ℝ, 1 < σ →
      wSeries w' ((σ : ℂ) + c) = wSeries w ((σ : ℂ) + c) - wSeries h ((σ : ℂ) + c) := by
    intro σ hσ
    have hs : 1 < ((σ : ℂ) + c).re := by simp; linarith
    rw [wSeries, wSeries, wSeries, ← (hw.summable_series hs).tsum_sub
      (hw.summable_series_of_le hh0 hhw hs)]
    refine tsum_congr fun j => ?_
    simp only [hhdef]; push_cast; ring
  have hnormh : ∀ σ : ℝ, 1 < σ → ‖wSeries h ((σ : ℂ) + c)‖ ≤ H := by
    intro σ hσ
    have hs : 1 < ((σ : ℂ) + c).re := by simp; linarith
    calc ‖wSeries h ((σ : ℂ) + c)‖ ≤ ∑' j : ℕ, ‖(h j : ℂ) * ((j : ℂ) + 1) ^ (-((σ : ℂ) + c))‖ :=
          norm_tsum_le_tsum_norm (hw.summable_series_of_le hh0 hhw hs).norm
      _ = wSum h ((σ : ℂ) + c).re := by
          rw [wSum]
          refine tsum_congr fun j => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hh0 j),
            norm_natCast_add_one_cpow, Complex.neg_re]
      _ ≤ H := hHb _ hs.le
  -- `‖wSeries w (σ + c)‖ / wSum w σ → 0`
  have hrel : Tendsto (fun σ : ℝ => ‖wSeries w ((σ : ℂ) + c)‖ / wSum w σ) (𝓝[>] 1) (𝓝 0) := by
    have := (hw.tendsto_off c hc hre).norm
    rw [norm_zero] at this
    refine this.congr' ?_
    filter_upwards [hw.eventually_pos] with σ hV
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV]
  have hinv : Tendsto (fun σ : ℝ => H / wSum w σ) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hw.tendsto_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbig : ∀ᶠ σ in 𝓝[>] (1 : ℝ), 2 * |H| + 1 ≤ wSum w σ :=
    hw.tendsto_atTop.eventually (eventually_ge_atTop _)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using (hrel.const_mul 2).add (hinv.const_mul 2))
  filter_upwards [self_mem_nhdsWithin, hbig] with σ hσ hB
  have hσ1 : 1 < σ := hσ
  have hHn := hHb σ hσ1.le
  have hH0 : 0 ≤ H := tsum_nonneg fun j => mul_nonneg (hh0 j) (by positivity)
  have hwpos : 0 < wSum w σ := by linarith [abs_nonneg H]
  have hw'half : wSum w σ / 2 ≤ wSum w' σ := by
    rw [hsub σ hσ1]; linarith [le_abs_self H, wSum_nonneg_of hh0 σ]
  have hw'pos : 0 < wSum w' σ := by linarith
  rw [hsubC σ hσ1, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw'pos,
    div_le_iff₀ hw'pos]
  have hn := norm_sub_le (wSeries w ((σ : ℂ) + c)) (wSeries h ((σ : ℂ) + c))
  have hnh := hnormh σ hσ1
  have hexp : (2 * (‖wSeries w ((σ : ℂ) + c)‖ / wSum w σ) + 2 * (H / wSum w σ)) * wSum w' σ ≥
      ‖wSeries w ((σ : ℂ) + c)‖ + H := by
    have hge : (2 * (‖wSeries w ((σ : ℂ) + c)‖ / wSum w σ) + 2 * (H / wSum w σ)) * (wSum w σ / 2) =
        ‖wSeries w ((σ : ℂ) + c)‖ + H := by field_simp
    have hnn : 0 ≤ 2 * (‖wSeries w ((σ : ℂ) + c)‖ / wSum w σ) + 2 * (H / wSum w σ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hw'half hnn]
  linarith
where
  wSum_nonneg_of {v : ℕ → ℝ} (h0 : ∀ j, 0 ≤ v j) (σ : ℝ) : 0 ≤ wSum v σ :=
    tsum_nonneg fun j => mul_nonneg (h0 j) (by positivity)

/-! ### The primes in a residue class -/

section ResidueClass

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- `log p · 1_{p ≡ a}` at `n = j + 1`. -/
def primeResidueWeight (a : ZMod q) (j : ℕ) : ℝ := if (j + 1).Prime then residueWeight a j else 0

omit [NeZero q] in
theorem prime_and_mod_of_primeResidueWeight_ne_zero {j : ℕ} (hj : primeResidueWeight a j ≠ 0) :
    (j + 1).Prime ∧ ((j + 1 : ℕ) : ZMod q) = a := by
  unfold primeResidueWeight at hj
  split_ifs at hj with hp
  · refine ⟨hp, ?_⟩
    have hj' : vonMangoldt.residueClass a (j + 1) ≠ 0 := hj
    simp only [vonMangoldt.residueClass, Set.indicator_apply, Set.mem_setOf_eq] at hj'
    split_ifs at hj' with hmod
    · exact hmod
    · exact absurd rfl hj'
  · exact absurd rfl hj

/-- **The primes in a residue class are a sampling set.** -/
theorem samplingWeight_primeResidue (ha : IsUnit a) : SamplingWeight (primeResidueWeight a) := by
  refine (samplingWeight_residueClass ha).of_le_of_summable_sub (fun j => ?_) (fun j => ?_) ?_
  · unfold primeResidueWeight; split_ifs
    · exact residueWeight_nonneg j
    · exact le_rfl
  · unfold primeResidueWeight; split_ifs
    · exact le_rfl
    · exact residueWeight_nonneg j
  · refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      (summable_higherWeight (by norm_num : (1 : ℝ) / 2 < 1))
    · unfold primeResidueWeight; split_ifs
      · simp
      · rw [sub_zero]; exact mul_nonneg (residueWeight_nonneg j) (by positivity)
    · unfold primeResidueWeight higherWeight; split_ifs
      · simp
      · rw [sub_zero]
        exact mul_le_mul_of_nonneg_right (residueWeight_le j) (by positivity)

omit [NeZero q] in
/-- A bound at the primes `p ≡ a (mod q)` is a bound where the prime residue weight is nonzero. -/
theorem bound_of_primeResidueWeight_ne_zero {Z : ZeroConfig} {P : ℝ → Prop}
    (hK : ∀ p : ℕ, p.Prime → (p : ZMod q) = a → P (2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re)) :
    ∀ j : ℕ, primeResidueWeight a j ≠ 0 →
      P (2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) := by
  intro j hj
  obtain ⟨hp, hmod⟩ := prime_and_mod_of_primeResidueWeight_ne_zero hj
  have := hK (j + 1) hp hmod
  push_cast at this
  exact this

end ResidueClass

/-! ### The upper side at sampling sets -/

/-- An upper bound `2 Re S(log n) ≤ K` gives `F(log n) ≤ |K| n^{−b}`. -/
theorem normTrace_le_of_le {Z : ZeroConfig} {b K : ℝ} {j : ℕ}
    (h1 : 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re ≤ K) :
    normTrace Z b (Real.log ((j : ℝ) + 1)) ≤ |K| * ((j : ℝ) + 1) ^ (-b) := by
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hexp : Real.exp (-(b * Real.log ((j : ℝ) + 1))) = ((j : ℝ) + 1) ^ (-b) := by
    rw [Real.rpow_def_of_pos hj0]; ring_nf
  have hpb : 0 < ((j : ℝ) + 1) ^ (-b) := by positivity
  rw [normTrace, hexp]
  have h3 := mul_le_mul_of_nonneg_right h1 hpb.le
  have h4 : K * ((j : ℝ) + 1) ^ (-b) ≤ |K| * ((j : ℝ) + 1) ^ (-b) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hpb.le
  linarith

section Upper

variable {w : ℕ → ℝ} (hw : SamplingWeight w) {Z : ZeroConfig} {b : ℝ}
include hw

/-- **The relative mean of `F` is the real top coefficient.** -/
theorem tendsto_wMean_real (hZ : TemperedConfig Z) (h : TopDepth Z b) :
    Tendsto (fun σ => wMean w Z b σ / wSum w σ) (𝓝[>] 1)
      (𝓝 (evenCoeff Z (boxSpline 1 3) b).re) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hc : Tendsto (fun σ : ℝ => ∑' z, e z * wSeries w ((σ : ℂ) + (b - z)) / (wSum w σ : ℂ))
      (𝓝[>] 1) (𝓝 (∑' z : ℂ, if z = (b : ℂ) then e z else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hE (fun z => ?_) ?_
    · by_cases hzb : z = (b : ℂ)
      · have hconst : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
            e z * wSeries w ((σ : ℂ) + (b - z)) / (wSum w σ : ℂ) = e z := by
          filter_upwards [hw.eventually_pos] with σ hV
          rw [hzb, sub_self, add_zero, ← ofReal_wSum, mul_div_assoc,
            div_self (by exact_mod_cast hV.ne'), mul_one]
        simp only [if_pos hzb]
        exact tendsto_const_nhds.congr' (hconst.mono fun σ h => h.symm)
      · simp only [if_neg hzb]
        by_cases hz : e z = 0
        · simp [hz]
        have h1 := h z hz
        have hne : (b : ℂ) - z ≠ 0 := fun h0 => hzb (by linear_combination -h0)
        have := (hw.tendsto_off ((b : ℂ) - z) hne (by simp; linarith)).const_mul (e z)
        simpa [mul_div_assoc] using this
    · filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hV
      intro z
      have hσ1 : 1 < σ := hσ
      by_cases hz : e z = 0
      · simp [hz]
      have h1 := h z hz
      have hres : 1 < ((σ : ℂ) + (b - z)).re := by simp; linarith
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV, norm_mul, div_le_iff₀ hV]
      have hb1 := hw.norm_wSeries_le hres
      have hb2 : wSum w ((σ : ℂ) + (b - z)).re ≤ wSum w σ := hw.antitone hσ1 (by simp; linarith)
      exact mul_le_mul_of_nonneg_left (hb1.trans hb2) (norm_nonneg _)
  rw [tsum_ite_eq] at hc
  have hc' := (Complex.continuous_re.tendsto _).comp hc
  refine (hc'.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hrat : ((wMean w Z b σ / wSum w σ : ℝ) : ℂ) =
      ∑' z, e z * wSeries w ((σ : ℂ) + (b - z)) / (wSum w σ : ℂ) := by
    rw [Complex.ofReal_div, ofReal_wMean hw hZ h hσ, tsum_div_const]
  simp only [Function.comp_def]
  rw [← hrat, Complex.ofReal_re]

theorem wMean_le_of_upper (hZ : TemperedConfig Z) (h : TopDepth Z b) {K : ℝ}
    (hK : ∀ j : ℕ, w j ≠ 0 → 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re ≤ K)
    {σ : ℝ} (hσ : 1 < σ) (hb0 : 0 ≤ b) :
    wMean w Z b σ ≤ |K| * wSum w (σ + b) := by
  have hεsum := hw.summable (show 1 < σ + b by linarith)
  rw [wSum, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_wMean hw hZ h hσ) (hεsum.mul_left _)
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hp : 0 < ((j : ℝ) + 1) ^ (-σ) := by positivity
  have hsplit : ((j : ℝ) + 1) ^ (-(σ + b)) = ((j : ℝ) + 1) ^ (-σ) * ((j : ℝ) + 1) ^ (-b) := by
    rw [← Real.rpow_add hj0]; ring_nf
  rw [hsplit]
  by_cases hw0 : w j = 0
  · rw [hw0]; simp
  have hle := normTrace_le_of_le (b := b) (hK j hw0)
  have hwp : 0 ≤ w j * ((j : ℝ) + 1) ^ (-σ) := mul_nonneg (hw.nonneg j) hp.le
  have := mul_le_mul_of_nonneg_right hle hwp
  calc w j * normTrace Z b (Real.log ((j : ℝ) + 1)) * ((j : ℝ) + 1) ^ (-σ) =
        normTrace Z b (Real.log ((j : ℝ) + 1)) * (w j * ((j : ℝ) + 1) ^ (-σ)) := by ring
    _ ≤ |K| * ((j : ℝ) + 1) ^ (-b) * (w j * ((j : ℝ) + 1) ^ (-σ)) := this
    _ = _ := by ring

/-- **From above, `F² ≤ E(2|K|n^{−b} − F)`** at the sampled degrees. -/
theorem wSqMean_le_of_upper (hZ : TemperedConfig Z) (h : TopDepth Z b) {K : ℝ}
    (hK : ∀ j : ℕ, w j ≠ 0 → 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re ≤ K)
    {σ : ℝ} (hσ : 1 < σ) (hb0 : 0 ≤ b) :
    wSqMean w Z b σ ≤ 2 * (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * |K| * wSum w (σ + b) -
      (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * wMean w Z b σ := by
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  have hεsum := hw.summable (show 1 < σ + b by linarith)
  have hS₁sum := summable_wMean hw hZ h hσ
  have hrhs : Summable fun j : ℕ =>
      2 * E * |K| * (w j * ((j : ℝ) + 1) ^ (-(σ + b))) -
        E * (w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ)) :=
    (hεsum.mul_left _).sub (hS₁sum.mul_left E)
  calc wSqMean w Z b σ
      ≤ ∑' j : ℕ, (2 * E * |K| * (w j * ((j : ℝ) + 1) ^ (-(σ + b))) -
          E * (w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ))) := by
        refine Summable.tsum_le_tsum (fun j => ?_) (summable_wSqMean hw hZ h hσ) hrhs
        have hw0 := hw.nonneg j
        have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have hp : 0 < ((j : ℝ) + 1) ^ (-σ) := by positivity
        have hsplit : ((j : ℝ) + 1) ^ (-(σ + b)) = ((j : ℝ) + 1) ^ (-σ) * ((j : ℝ) + 1) ^ (-b) := by
          rw [← Real.rpow_add hj0]; ring_nf
        rw [hsplit]
        by_cases hw00 : w j = 0
        · rw [hw00]; simp
        have hup := normTrace_le_of_le (b := b) (hK j hw00)
        have hFb := abs_normTrace_le hZ h (log_add_one_nonneg j)
        set f := normTrace Z b (Real.log ((j : ℝ) + 1))
        have habs : |f| ≤ 2 * (|K| * ((j : ℝ) + 1) ^ (-b)) - f := by
          rcases le_total 0 f with h0 | h0
          · rw [abs_of_nonneg h0]; linarith
          · rw [abs_of_nonpos h0]; nlinarith [abs_nonneg K, (by positivity : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ (-b))]
        have hsq : f ^ 2 ≤ E * (2 * (|K| * ((j : ℝ) + 1) ^ (-b)) - f) := by
          calc f ^ 2 = |f| * |f| := by rw [← sq_abs, sq]
            _ ≤ E * |f| := mul_le_mul_of_nonneg_right hFb (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left habs hE0
        have hwp : 0 ≤ w j * ((j : ℝ) + 1) ^ (-σ) := mul_nonneg hw0 hp.le
        have h5 := mul_le_mul_of_nonneg_right hsq hwp
        calc w j * f ^ 2 * ((j : ℝ) + 1) ^ (-σ) = f ^ 2 * (w j * ((j : ℝ) + 1) ^ (-σ)) := by ring
          _ ≤ E * (2 * (|K| * ((j : ℝ) + 1) ^ (-b)) - f) * (w j * ((j : ℝ) + 1) ^ (-σ)) := h5
          _ = _ := by ring
    _ = 2 * E * |K| * wSum w (σ + b) - E * wMean w Z b σ := by
        rw [(hεsum.mul_left _).tsum_sub (hS₁sum.mul_left E), tsum_mul_left, tsum_mul_left]
        rfl

end Upper

/-- **The upper side at a sampling set sees every attained top layer.** -/
theorem onLine_of_bddAbove_of_samplingWeight {w : ℕ → ℝ} (hw : SamplingWeight w)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ j : ℕ, w j ≠ 0 → 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  rcases (half_le_of_max hρ₀ hmax).eq_or_lt with hb | hoff
  · exact onLine_of_max_eq_half hmax hb.symm
  exfalso
  set b : ℝ := ρ₀.re - 1 / 2 with hbdef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have htop : TopDepth Z b := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
  have hz₀ : evenCoeff Z (boxSpline 1 3) (ρ₀ - 1 / 2) ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z hb3.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₀
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  have hpos := re_tsum_diagWeight_pos hZ htop hz₀ (by simp [hbdef])
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  set R := (evenCoeff Z (boxSpline 1 3) b).re with hRdef
  have hR0 : 0 ≤ R := by
    by_cases hmem : (1 / 2 + (b : ℂ)) ∈ Z.carrier
    · exact (evenCoeff_spline_pos_of_real Z hmem (by simpa using hb0) (by simp)).le
    · have hzero : evenCoeff Z (boxSpline 1 3) b = 0 := by
        by_contra hz
        rcases mem_of_evenCoeff_ne_zero hz with h | h
        · exact hmem h
        · exact hmem (by simpa using h)
      rw [hRdef, hzero, Complex.zero_re]
  have hlimε : Tendsto (fun σ => wSum w (σ + b) / wSum w σ) (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ)))
      ((tendsto_const_nhds (x := wSum w (1 + b))).div_atTop hw.tendsto_atTop) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact div_nonneg (hw.wSum_nonneg _) (hw.wSum_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : 1 < σ := hσ
      exact div_le_div_of_nonneg_right (hw.antitone (by linarith) (by linarith))
        (hw.wSum_nonneg _)
  have hlim₁ := tendsto_wMean_real hw hZ htop
  have hRle : R ≤ 0 := by
    have hup : Tendsto (fun σ => |K| * (wSum w (σ + b) / wSum w σ)) (𝓝[>] 1) (𝓝 0) := by
      simpa using hlimε.const_mul |K|
    refine le_of_tendsto_of_tendsto hlim₁ hup ?_
    filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hV
    have hσ1 : 1 < σ := hσ
    rw [div_le_iff₀ hV, mul_div_assoc', div_mul_cancel₀ _ hV.ne']
    exact wMean_le_of_upper hw hZ htop hK hσ1 hb0.le
  have hR : R = 0 := le_antisymm hRle hR0
  have hrhs : Tendsto (fun σ => 2 * E * |K| * (wSum w (σ + b) / wSum w σ) -
      E * (wMean w Z b σ / wSum w σ)) (𝓝[>] 1) (𝓝 0) := by
    have := (hlimε.const_mul (2 * E * |K|)).sub (hlim₁.const_mul E)
    rw [← hRdef, hR] at this
    simpa using this
  have hle : (∑' q, diagWeight Z b q).re ≤ 0 := by
    refine le_of_tendsto_of_tendsto (tendsto_wSqMean hw hZ htop) hrhs ?_
    filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hV
    have hσ1 : 1 < σ := hσ
    have h := wSqMean_le_of_upper hw hZ htop hK hσ1 hb0.le
    rw [div_le_iff₀ hV]
    have : (2 * E * |K| * (wSum w (σ + b) / wSum w σ) - E * (wMean w Z b σ / wSum w σ)) *
        wSum w σ = 2 * E * |K| * wSum w (σ + b) - E * wMean w Z b σ := by field_simp
    rw [this]; exact h
  linarith

/-! ### `ζ` at the primes in a residue class -/

section Zeta

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- **From below at the primes `p ≡ a (mod q)`, no off-line zero of `ζ` is deepest.** -/
theorem exists_re_gt_of_bddBelow_primes_mod (ha : IsUnit a) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → (p : ZMod q) = a →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hoff : 1 / 2 < ρ₀.re) :
    ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re := by
  by_contra hno
  push Not at hno
  have hmem := re_mem_of_bddBelow_of_samplingWeight (samplingWeight_primeResidue ha)
    zetaZeroConfig temperedConfig_zetaZeroConfig hρ₀ hoff hno
    (bound_of_primeResidueWeight_ne_zero (P := fun x => -K ≤ x) hK)
  exact zetaZeroConfig_im_ne_zero' _ hmem (Complex.ofReal_im _)

/-- **From above at the primes `p ≡ a (mod q)`, no off-line zero of `ζ` is deepest.** -/
theorem exists_re_gt_of_bddAbove_primes_mod (ha : IsUnit a) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → (p : ZMod q) = a →
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re ≤ K)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hoff : 1 / 2 < ρ₀.re) :
    ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re := by
  by_contra hno
  push Not at hno
  have h := onLine_of_bddAbove_of_samplingWeight (samplingWeight_primeResidue ha)
    zetaZeroConfig temperedConfig_zetaZeroConfig hρ₀ hno
    (bound_of_primeResidueWeight_ne_zero (P := fun x => x ≤ K) hK) ρ₀ hρ₀
  linarith

/-- If no off-line zero is deepest, and the off-line zeros have a deepest member when there are
any, then RH. -/
theorem riemannHypothesis_of_noDeepest
    (hno : ∀ ρ₀ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ₀.re → ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re →
      ∃ ρ₀ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ'.re ≤ ρ₀.re) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_zetaZeroConfig_onLine]
  intro ρ hρ
  by_contra hne
  -- an off-line zero right of the line
  obtain ⟨ρ', hρ', hρ'h⟩ : ∃ ρ' ∈ zetaZeroConfig.carrier, 1 / 2 < ρ'.re := by
    rcases lt_or_gt_of_ne hne with h | h
    · refine ⟨_, zetaZeroConfig.reflect_mem ρ hρ, ?_⟩
      have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
      rw [hrefl]; linarith
    · exact ⟨ρ, hρ, h⟩
  obtain ⟨ρ₀, hρ₀, hmax⟩ := htop ρ' hρ' hρ'h
  obtain ⟨ρ'', hρ'', hgt⟩ := hno ρ₀ hρ₀ (lt_of_lt_of_le hρ'h (hmax ρ' hρ'))
  linarith [hmax ρ'' hρ'']

/-- **RH from below at the primes in a residue class, given an attained top.** -/
theorem riemannHypothesis_iff_bddBelow_primes_mod_and_topAttained (ha : IsUnit a) :
    RiemannHypothesis ↔
      (∃ K : ℝ, ∀ p : ℕ, p.Prime → (p : ZMod q) = a →
        -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) ∧
      (∀ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re →
        ∃ ρ₀ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ'.re ≤ ρ₀.re) := by
  constructor
  · intro hRH
    refine ⟨⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖, fun p hp _ => ?_⟩,
      fun ρ hρ h => ?_⟩
    · exact (abs_le.mp (abs_two_re_lagStructure_le_of_RH hRH (Real.log_natCast_nonneg p))).1
    · have := riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH ρ hρ; linarith
  · rintro ⟨⟨K, hK⟩, htop⟩
    exact riemannHypothesis_of_noDeepest
      (fun ρ₀ hρ₀ hoff => exists_re_gt_of_bddBelow_primes_mod ha hK hρ₀ hoff) htop

/-- **RH from above at the primes in a residue class, given an attained top.** -/
theorem riemannHypothesis_iff_bddAbove_primes_mod_and_topAttained (ha : IsUnit a) :
    RiemannHypothesis ↔
      (∃ K : ℝ, ∀ p : ℕ, p.Prime → (p : ZMod q) = a →
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re ≤ K) ∧
      (∀ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re →
        ∃ ρ₀ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ'.re ≤ ρ₀.re) := by
  constructor
  · intro hRH
    refine ⟨⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖, fun p hp _ => ?_⟩,
      fun ρ hρ h => ?_⟩
    · exact (abs_le.mp (abs_two_re_lagStructure_le_of_RH hRH (Real.log_natCast_nonneg p))).2
    · have := riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH ρ hρ; linarith
  · rintro ⟨⟨K, hK⟩, htop⟩
    exact riemannHypothesis_of_noDeepest
      (fun ρ₀ hρ₀ hoff => exists_re_gt_of_bddAbove_primes_mod ha hK hρ₀ hoff) htop

end Zeta

end GaloisForLFunctions.SurfaceOfSpecZ
