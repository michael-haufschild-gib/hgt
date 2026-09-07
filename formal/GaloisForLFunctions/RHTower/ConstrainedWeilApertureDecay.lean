import GaloisForLFunctions.RHTower.ConstrainedWeilApertureConstantTerm
import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# Decay norms of the normalised ray-term polynomials

For a copy `q` that is *far* from the centre in ordinate (`|Re z_q − γ| ≥ 1` and `|Re z_q + γ| ≥ 1`)
every nonzero sum of two exponents of the `−Θ`-shifted pair polynomial has modulus at least
`m₀ = min 1 (min Θ g)`, where `g` is a positive lower bound for `|Re z_q|` and `|γ|`: the imaginary
parts of such sums are `±2ν₁, ±ν₁, ±2ν₂, ±ν₂, ±2 Re z_q, ±2γ` (all of modulus `≥ min 1 g` up to the
factor `2`), and when the imaginary part vanishes the real part is `−2Θ`.  Together with the
coefficient bounds `‖κ(c)‖, ‖ρ(c)‖ ≤ M e^{|Re c|/4}/‖c‖ ≤ M e^{Θ/4}` (as `‖c‖ ≥ |Im c| ≥ 1`) this gives
`decayNorm (normalizedRayTermPoly Θ γ q) ≤ (8 M e^{Θ/4})² / (4 m₀ ‖z_q‖²)` for far copies, which is
summable over the copies.
-/

open MeasureTheory Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem norm_ge_of_abs_re {m : ℝ} {x : ℂ} (h : m ≤ |x.re|) : m ≤ ‖x‖ :=
  h.trans (Complex.abs_re_le_norm x)

theorem norm_ge_of_abs_im {m : ℝ} {x : ℂ} (h : m ≤ |x.im|) : m ≤ ‖x‖ :=
  h.trans (Complex.abs_im_le_norm x)

/-- A copy is far from the centre `γ` when both `|Re z_q − γ| ≥ 1` and `|Re z_q + γ| ≥ 1`. -/
def FarFromCentre (γ : ℝ) (q : XiZeroCopy) : Prop :=
  1 ≤ |(xiSpectralPoint q).re - γ| ∧ 1 ≤ |(xiSpectralPoint q).re + γ|

/-- **Exponent-sum lower bound for far copies.**  With `m₀ = min 1 (min Θ g)`, `g ≤ |Re z_q|`,
`g ≤ |γ|`, `|Im z_q| ≤ Θ`, every nonzero sum of two exponents of the shifted pair polynomial has
modulus at least `m₀`. -/
theorem shiftedPairPoly_pairSum_norm_ge {Θ g γ : ℝ} (hΘ : 0 < Θ) (hg : 0 < g) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ Θ) (hz : g ≤ |(xiSpectralPoint q).re|) (hγ : g ≤ |γ|)
    (hfar : FarFromCentre γ q) :
    ∀ p ∈ shiftedPairPoly Θ γ q, ∀ r ∈ shiftedPairPoly Θ γ q,
      p.2 + r.2 ≠ 0 → min 1 (min Θ g) ≤ ‖p.2 + r.2‖ := by
  have hc₁ : rayFreq₁ γ q ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [rayFreq₁_im, Complex.zero_im] at this
    have h1 := hfar.1
    rw [this, abs_zero] at h1
    linarith
  have hc₂ : rayFreq₂ γ q ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [rayFreq₂_im, Complex.zero_im] at this
    have h1 := hfar.2
    rw [this, abs_zero] at h1
    linarith
  rw [shiftedPairPoly_explicit Θ γ hc₁ hc₂]
  intro p hp r hr _
  have hm0 : 0 ≤ min 1 (min Θ g) := le_min zero_le_one (le_min hΘ.le hg.le)
  have hm1 : min 1 (min Θ g) ≤ 1 := min_le_left _ _
  have hmΘ : min 1 (min Θ g) ≤ Θ := (min_le_right _ _).trans (min_le_left _ _)
  have hmg : min 1 (min Θ g) ≤ g := (min_le_right _ _).trans (min_le_right _ _)
  have hm1sq : (min 1 (min Θ g)) ^ 2 ≤ 1 := by nlinarith
  have hmgsq : (min 1 (min Θ g)) ^ 2 ≤ g ^ 2 := by nlinarith
  have hb := abs_le.mp hq
  have hν₁sq : 1 ≤ ((xiSpectralPoint q).re - γ) ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hfar.1 2
    rwa [one_pow, sq_abs] at this
  have hν₂sq : 1 ≤ ((xiSpectralPoint q).re + γ) ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hfar.2 2
    rwa [one_pow, sq_abs] at this
  have hzsq : g ^ 2 ≤ (xiSpectralPoint q).re ^ 2 := by
    have := pow_le_pow_left₀ hg.le hz 2
    rwa [sq_abs] at this
  have hγsq : g ^ 2 ≤ γ ^ 2 := by
    have := pow_le_pow_left₀ hg.le hγ 2
    rwa [sq_abs] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hr
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact norm_ge_of_abs_re (by
        simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.zero_re,
          rayFreq₁_re, rayFreq₂_re]
        exact le_abs.mpr (Or.inr (by linarith)))
    | exact norm_ge_of_abs_im ((abs_of_nonneg hm0).symm.le.trans (sq_le_sq.mp (by
        simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, rayFreq₁_im, rayFreq₂_im]
        nlinarith [hν₁sq, hν₂sq, hzsq, hγsq, hm1sq, hmgsq])))

/-! ## Coefficient sums and decay norms of far copies -/

theorem norm_rayFreq₁_ge_one (γ : ℝ) {q : XiZeroCopy} (hfar : FarFromCentre γ q) :
    1 ≤ ‖rayFreq₁ γ q‖ :=
  le_trans (by rw [rayFreq₁_im]; exact hfar.1) (Complex.abs_im_le_norm _)

theorem norm_rayFreq₂_ge_one (γ : ℝ) {q : XiZeroCopy} (hfar : FarFromCentre γ q) :
    1 ≤ ‖rayFreq₂ γ q‖ :=
  le_trans (by rw [rayFreq₂_im]; exact hfar.2) (Complex.abs_im_le_norm _)

/-- A coefficient bound `M e^{|Re c|/4}/‖c‖` gives `M e^{Θ/4}` when `‖c‖ ≥ 1` and `|Re c| ≤ Θ`. -/
theorem coeff_bound_far {M Θ : ℝ} (hM : 0 ≤ M) {c : ℂ} (hc : 1 ≤ ‖c‖) (hre : |c.re| ≤ Θ) {x : ℂ}
    (hx : ‖x‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖) : ‖x‖ ≤ M * Real.exp (Θ / 4) := by
  refine hx.trans ?_
  have h1 : Real.exp (|c.re| / 4) ≤ Real.exp (Θ / 4) := Real.exp_le_exp.mpr (by linarith)
  calc M * Real.exp (|c.re| / 4) / ‖c‖ ≤ M * Real.exp (|c.re| / 4) / 1 := by
        gcongr
    _ = M * Real.exp (|c.re| / 4) := div_one _
    _ ≤ M * Real.exp (Θ / 4) := mul_le_mul_of_nonneg_left h1 hM

/-- **Coefficient sum of a far copy**: at most `8 M e^{Θ/4}`. -/
theorem coeffSum_shiftedPairPoly_le {Θ M : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖)
    (γ : ℝ) {q : XiZeroCopy} (hq : |(xiSpectralPoint q).im| ≤ Θ) (hfar : FarFromCentre γ q) :
    ExpPoly.coeffSum (shiftedPairPoly Θ γ q) ≤ 8 * (M * Real.exp (Θ / 4)) := by
  have h1 := norm_rayFreq₁_ge_one γ hfar
  have h2 := norm_rayFreq₂_ge_one γ hfar
  have hc₁ : rayFreq₁ γ q ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have hc₂ : rayFreq₂ γ q ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; linarith
  have hre₁ : |(rayFreq₁ γ q).re| ≤ Θ := by rw [rayFreq₁_re, abs_neg]; exact hq
  have hre₂ : |(rayFreq₂ γ q).re| ≤ Θ := by rw [rayFreq₂_re, abs_neg]; exact hq
  have hnre₁ : |(-rayFreq₁ γ q).re| ≤ Θ := by rw [Complex.neg_re, abs_neg]; exact hre₁
  have hnre₂ : |(-rayFreq₂ γ q).re| ≤ Θ := by rw [Complex.neg_re, abs_neg]; exact hre₂
  have hn₁ : 1 ≤ ‖-rayFreq₁ γ q‖ := by rw [norm_neg]; exact h1
  have hn₂ : 1 ≤ ‖-rayFreq₂ γ q‖ := by rw [norm_neg]; exact h2
  have b1 := coeff_bound_far hM h1 hre₁ (hMb _ hc₁).1
  have b2 := coeff_bound_far hM h1 hre₁ (hMb _ hc₁).2
  have b3 := coeff_bound_far hM hn₁ hnre₁ (hMb _ (neg_ne_zero.mpr hc₁)).1
  have b4 := coeff_bound_far hM hn₁ hnre₁ (hMb _ (neg_ne_zero.mpr hc₁)).2
  have b5 := coeff_bound_far hM h2 hre₂ (hMb _ hc₂).1
  have b6 := coeff_bound_far hM h2 hre₂ (hMb _ hc₂).2
  have b7 := coeff_bound_far hM hn₂ hnre₂ (hMb _ (neg_ne_zero.mpr hc₂)).1
  have b8 := coeff_bound_far hM hn₂ hnre₂ (hMb _ (neg_ne_zero.mpr hc₂)).2
  rw [shiftedPairPoly_explicit Θ γ hc₁ hc₂]
  simp only [ExpPoly.coeffSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, norm_neg]
  linarith

/-- **Decay norm of a far copy**: `≤ (8 M e^{Θ/4})² / (4 m₀ ‖z_q‖²)`. -/
theorem decayNorm_normalizedRayTermPoly_le_far {Θ g γ M : ℝ} (hΘ : 0 < Θ) (hg : 0 < g) (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖)
    {q : XiZeroCopy} (hq : |(xiSpectralPoint q).im| ≤ Θ) (hz : g ≤ |(xiSpectralPoint q).re|)
    (hγ : g ≤ |γ|) (hfar : FarFromCentre γ q) :
    ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q)
      ≤ (8 * (M * Real.exp (Θ / 4))) ^ 2 / min 1 (min Θ g) * (1 / (4 * ‖xiSpectralPoint q‖ ^ 2)) := by
  have hm0 : 0 < min 1 (min Θ g) := lt_min one_pos (lt_min hΘ hg)
  have hpair := shiftedPairPoly_pairSum_norm_ge hΘ hg hq hz hγ hfar
  rw [normalizedRayTermPoly_eq, ExpPoly.decayNorm_smul]
  have hmul := ExpPoly.decayNorm_mul_le (shiftedPairPoly Θ γ q) (shiftedPairPoly Θ γ q) hm0 hpair
  have hcs := coeffSum_shiftedPairPoly_le hM hMb γ hq hfar
  have hcs0 := ExpPoly.coeffSum_nonneg (shiftedPairPoly Θ γ q)
  have hw : ‖-(1 / 4 : ℂ) / xiSpectralPoint q ^ 2‖ = 1 / (4 * ‖xiSpectralPoint q‖ ^ 2) := by
    rw [norm_div, norm_neg, norm_div, norm_one, norm_pow, Complex.norm_ofNat]
    ring
  rw [hw]
  have hsq : ExpPoly.coeffSum (shiftedPairPoly Θ γ q) * ExpPoly.coeffSum (shiftedPairPoly Θ γ q)
      ≤ (8 * (M * Real.exp (Θ / 4))) ^ 2 := by
    rw [← sq]
    exact pow_le_pow_left₀ hcs0 hcs 2
  have hz0 : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  calc 1 / (4 * ‖xiSpectralPoint q‖ ^ 2)
        * ExpPoly.decayNorm (ExpPoly.mul (shiftedPairPoly Θ γ q) (shiftedPairPoly Θ γ q))
      ≤ 1 / (4 * ‖xiSpectralPoint q‖ ^ 2)
        * (ExpPoly.coeffSum (shiftedPairPoly Θ γ q) * ExpPoly.coeffSum (shiftedPairPoly Θ γ q)
          / min 1 (min Θ g)) := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ ≤ 1 / (4 * ‖xiSpectralPoint q‖ ^ 2) * ((8 * (M * Real.exp (Θ / 4))) ^ 2 / min 1 (min Θ g)) := by
        gcongr
    _ = (8 * (M * Real.exp (Θ / 4))) ^ 2 / min 1 (min Θ g) * (1 / (4 * ‖xiSpectralPoint q‖ ^ 2)) := by
        ring

/-! ## Summability of the decay norms over the copies -/

theorem xiSpectralPoint_re_eq_im (q : XiZeroCopy) : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint]

/-- Copies that are not far from the centre lie in one of two ordinate bands, hence are finite. -/
theorem finite_not_farFromCentre (γ : ℝ) : {q : XiZeroCopy | ¬ FarFromCentre γ q}.Finite := by
  have h1 := finite_xiZeroCopy_band γ (zero_le_one)
  have h2 := finite_xiZeroCopy_band (-γ) (zero_le_one)
  refine (h1.union h2).subset ?_
  intro q hq
  simp only [FarFromCentre, mem_setOf_eq, not_and_or, not_le] at hq
  simp only [mem_union, mem_setOf_eq, ← xiSpectralPoint_re_eq_im]
  rcases hq with hq | hq
  · left; exact hq.le
  · right; rw [sub_neg_eq_add]; exact hq.le

/-- **Summability of the decay norms.**  If `|Im z_q| ≤ Θ` for all copies, `g ≤ |Re z_q|` for all
copies and `g ≤ |γ|`, then `Σ_q decayNorm (normalizedRayTermPoly Θ γ q) < ∞`. -/
theorem summable_decayNorm_normalizedRayTermPoly {Θ g γ : ℝ} (hΘ : 0 < Θ) (hg : 0 < g)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ)
    (hord : ∀ q : XiZeroCopy, g ≤ |(xiSpectralPoint q).re|) (hγ : g ≤ |γ|) :
    Summable (fun q : XiZeroCopy => ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q)) := by
  classical
  obtain ⟨M, hM, hMb⟩ := exists_plateau_coeff_bound
  set K : ℝ := (8 * (M * Real.exp (Θ / 4))) ^ 2 / min 1 (min Θ g) with hK
  have hK0 : 0 ≤ K := by
    have : 0 < min 1 (min Θ g) := lt_min one_pos (lt_min hΘ hg)
    positivity
  set F : Finset XiZeroCopy := (finite_not_farFromCentre γ).toFinset with hF
  have hsum1 : Summable (fun q : XiZeroCopy => K * (1 / (4 * ‖xiSpectralPoint q‖ ^ 2))) := by
    have := xiSpectralPoint_inv_sq_summable.mul_left (K / 4)
    refine this.congr fun q => ?_
    ring
  have hsum2 : Summable (fun q : XiZeroCopy =>
      if q ∈ F then ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q) else 0) := by
    refine summable_of_ne_finset_zero (s := F) fun q hq => ?_
    simp [hq]
  refine Summable.of_nonneg_of_le (fun q => ExpPoly.decayNorm_nonneg _) (fun q => ?_)
    (hsum1.add hsum2)
  by_cases hfar : FarFromCentre γ q
  · have hqF : q ∉ F := by
      simp only [hF, Set.Finite.mem_toFinset, mem_setOf_eq, not_not]
      exact hfar
    rw [if_neg hqF, add_zero]
    exact decayNorm_normalizedRayTermPoly_le_far hΘ hg hM hMb (hall q) (hord q) hγ hfar
  · have hqF : q ∈ F := by
      simp only [hF, Set.Finite.mem_toFinset, mem_setOf_eq]
      exact hfar
    rw [if_pos hqF]
    have : 0 ≤ K * (1 / (4 * ‖xiSpectralPoint q‖ ^ 2)) := by positivity
    linarith

end

end RHTower
