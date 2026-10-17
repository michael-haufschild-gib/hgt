import GaloisForLFunctions.RHTower.LineShiftHalfPlaneHolomorphic
import GaloisForLFunctions.RHTower.TrivialWeightBoostedProducer
import GaloisForLFunctions.RHTower.PrimeBlindKernelSpectral

/-!
# The cone-existence ladder for the trivial weights

Call `μ` an admissible growth exponent if `|ζ(σ + it)| ≤ K (1 + |t|)^μ` for `σ ≥ ½`, `|t| ≥ 1`
(`ZetaGrowthExponent μ`); admissible exponents are `≥ 0` (`ZetaGrowthExponent.nonneg`).

**Theorem** (`trivialWeights_boostedWeilCone`).  For every admissible `μ` and every `θ > μ` there is
`C > 0` such that `λ ≡ 1` (on `n ≥ 2`) lies in the Weil cone whose archimedean density is
`Ω_ζ + C(1 + |t|)^θ`, with the same pole and prime comb:

`0 ≤ Re W_{λ≡1}(f ⋆ f̃) + (1/2π) ∫ |f̂(r)|² C (1 + |r|)^θ dr`   for every `f ∈ C²_c`.

Unconditionally this holds for every `θ > ¼` (`trivialWeights_boostedWeilCone_of_quarter_lt`, the
convexity rung).

Proof.  For `0 ≤ μ < θ < 1` the function `archPart(s) + c(s + ½)^θ − (ζ(s) − 1)` is a Herglotz
function on `Re s > ½` for large `c` (`exists_herglotz_trivialWeights_boosted_of_growth`: the pole
at `1` cancels, `|ζ(s) − 1/(s−1)| ≪ (2 + |t|)^μ`, `Re ψ(s/2)` is bounded below and
`Re (s + ½)^θ ≥ cos(θπ/2)|s + ½|^θ`).  The Herglotz line-integral inequality of the corpus bridge,
applied to `W_{λ≡1} + c(s + ½)^θ`, and a shift of the boost term to the critical line
(`LineShiftOn.integral_line_shift_critical_on`), where `Re (1 + it)^θ ≤ (1 + |t|)^θ`, give the
inequality.  Larger `θ` only enlarge the density.
-/

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real ComplexConjugate
open Zeta23 Zeta23.WeilEF

namespace RHTower.TrivialWeightCone

open RelaxedHerglotz

noncomputable section

/-! ### Admissible growth exponents -/

/-- `|ζ(σ + it)| ≤ K (1 + |t|)^μ` on `σ ≥ ½`, `|t| ≥ 1`. -/
def ZetaGrowthExponent (μ : ℝ) : Prop :=
  ∃ K : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ K * (1 + |s.im|) ^ μ

/-- `|ζ(2 + it)| ≥ 1/3`. -/
theorem third_le_norm_riemannZeta_two_add (t : ℝ) : 1 / 3 ≤ ‖riemannZeta (2 + t * I)‖ := by
  set s : ℂ := 2 + t * I with hs
  have hre : s.re = 2 := by simp [hs]
  have h1 : 1 < s.re := by rw [hre]; norm_num
  have hsum : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s := by
    have h := LSeriesSummable_one_iff.mpr h1
    have h2 := (summable_nat_add_iff (f := LSeries.term (fun _ => (1 : ℂ)) s) 1).mpr h
    refine h2.congr fun n => ?_
    simp [LSeries.term]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1, hsum.tsum_eq_zero_add]
  have hzero : 1 / (((0 : ℕ) : ℂ) + 1) ^ s = 1 := by simp
  rw [hzero]
  -- the tail is at most `π²/6 − 1 < 2/3`
  have htail : ‖∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    have hR : HasSum (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
      have h := hasSum_zeta_two
      rw [← hasSum_nat_add_iff' 2] at h
      simpa [Finset.sum_range_succ] using h
    refine tsum_of_norm_bounded hR fun n => ?_
    rw [norm_div, norm_one, show ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast_cpow_of_pos (by omega), hre]
    norm_num
  have hpi : Real.pi ^ 2 / 6 - 1 < 2 / 3 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have := norm_sub_norm_le (1 : ℂ) (-(∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s))
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

/-- **Admissible exponents are nonnegative.** -/
theorem ZetaGrowthExponent.nonneg {μ : ℝ} (h : ZetaGrowthExponent μ) : 0 ≤ μ := by
  obtain ⟨K, hK⟩ := h
  by_contra hμ
  push Not at hμ
  have hbound : ∀ t : ℝ, 1 ≤ |t| → 1 / 3 ≤ K * (1 + |t|) ^ μ := fun t ht => by
    have := hK (2 + t * I) (by simp; norm_num) (by simpa using ht)
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at this
    simp at this
    exact (third_le_norm_riemannZeta_two_add t).trans this
  have htend : Tendsto (fun T : ℝ => |K| * (1 + T) ^ μ) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < -μ)).comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    simpa [Function.comp_def, neg_neg] using this.const_mul |K|
  obtain ⟨T, hT⟩ := ((htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))).and
    (eventually_ge_atTop 1)).exists
  have h1 := hbound T (by rw [abs_of_pos (by linarith [hT.2])]; exact hT.2)
  rw [abs_of_pos (by linarith [hT.2])] at h1
  have h2 : K * (1 + T) ^ μ ≤ |K| * (1 + T) ^ μ :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg (by linarith [hT.2]) _)
  linarith [hT.1]

/-! ### The parametric producer -/

theorem exists_norm_zetaRegular_le_of_growth {μ : ℝ} (hμ : ZetaGrowthExponent μ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 < s.re → ‖RelaxedHerglotz.zetaRegular s‖ ≤ K * (2 + |s.im|) ^ μ := by
  have hμ0 := hμ.nonneg
  obtain ⟨K₀, hK₀⟩ := hμ
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (2 : ℝ))⁻¹ with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  set R : Set ℂ := {s : ℂ | 1 / 2 ≤ s.re} ∩ closedBall 0 4 with hR
  have hRc : IsCompact R :=
    (isCompact_closedBall 0 4).inter_left (isClosed_le continuous_const Complex.continuous_re)
  obtain ⟨M, hM⟩ := hRc.exists_bound_of_continuousOn RelaxedHerglotz.continuous_zetaRegular.continuousOn
  set K : ℝ := max (|K₀| + 1) (max (Z + 1) (max M 0)) with hKdef
  have hK1 : |K₀| + 1 ≤ K := le_max_left _ _
  have hK2 : Z + 1 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK3 : M ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hK0 : 0 ≤ K := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨K, hK0, fun s hs => ?_⟩
  have hbase : (1 : ℝ) ≤ (2 + |s.im|) ^ μ :=
    Real.one_le_rpow (by linarith [abs_nonneg s.im]) hμ0
  by_cases hbig : 2 < s.re
  · have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hbig; linarith
    rw [RelaxedHerglotz.zetaRegular_of_ne hs1]
    have hz := RelaxedHerglotz.norm_riemannZeta_le_tsum_rpow (by norm_num : (1 : ℝ) < 2) hbig.le
    have hinv : ‖1 / (s - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      have : 1 ≤ ‖s - 1‖ := by
        have := Complex.abs_re_le_norm (s - 1)
        rw [sub_re, one_re] at this
        linarith [le_abs_self (s.re - 1)]
      rw [div_le_one (by linarith)]; exact this
    calc ‖riemannZeta s - 1 / (s - 1)‖ ≤ Z + 1 := (norm_sub_le _ _).trans (by linarith)
      _ ≤ K := hK2
      _ ≤ K * (2 + |s.im|) ^ μ := le_mul_of_one_le_right hK0 hbase
  push Not at hbig
  by_cases ht : 1 ≤ |s.im|
  · have hs1 : s ≠ 1 := fun h => by rw [h, one_im, abs_zero] at ht; linarith
    rw [RelaxedHerglotz.zetaRegular_of_ne hs1]
    have hz := hK₀ s hs.le ht
    have hinv : ‖1 / (s - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      have : 1 ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        rw [sub_im, one_im, sub_zero] at this
        linarith
      rw [div_le_one (by linarith)]; exact this
    have hmono : (1 + |s.im|) ^ μ ≤ (2 + |s.im|) ^ μ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hμ0
    calc ‖riemannZeta s - 1 / (s - 1)‖ ≤ K₀ * (1 + |s.im|) ^ μ + 1 :=
          (norm_sub_le _ _).trans (by linarith)
      _ ≤ |K₀| * (2 + |s.im|) ^ μ + (2 + |s.im|) ^ μ := by
          have := mul_le_mul (le_abs_self K₀) hmono (Real.rpow_nonneg (by positivity) _)
            (abs_nonneg _)
          linarith
      _ = (|K₀| + 1) * (2 + |s.im|) ^ μ := by ring
      _ ≤ K * (2 + |s.im|) ^ μ := mul_le_mul_of_nonneg_right hK1 (by positivity)
  · push Not at ht
    have hmem : s ∈ R := by
      refine ⟨hs.le, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 4 := by rw [abs_of_pos (by linarith)]; linarith
    calc ‖RelaxedHerglotz.zetaRegular s‖ ≤ M := hM s hmem
      _ ≤ K := hK3
      _ ≤ K * (2 + |s.im|) ^ μ := le_mul_of_one_le_right hK0 hbase

/-- **The parametric producer.**  For an admissible `μ` and `μ < θ < 1`, some `c > 0` makes
`archPart(s) + c(s + ½)^θ − (ζ(s) − 1)` a Herglotz function on `Re s > ½`. -/
theorem exists_herglotz_trivialWeights_boosted_of_growth {μ θ : ℝ} (hμ : ZetaGrowthExponent μ)
    (hθ : μ < θ) (hθ1 : θ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) ∧
      ∀ s : ℂ, 1 < s.re →
        Φ s = WeilHerglotz.weilFunction (fun _ => 1) s + c * (s + 1 / 2) ^ (θ : ℂ) := by
  have hμ0 := hμ.nonneg
  have hθ0 : 0 < θ := by linarith
  obtain ⟨K₂, hK₂, hzeta⟩ := exists_norm_zetaRegular_le_of_growth hμ
  obtain ⟨K₁, hdig⟩ := RelaxedHerglotz.exists_lower_bound_re_digamma_half
  set A : ℝ := max K₁ 0 / 2 + Real.log Real.pi / 2 + K₂ with hA
  have hlogpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hA0 : 0 ≤ A := by have := le_max_right K₁ 0; positivity
  set κ : ℝ := Real.cos (θ * (Real.pi / 2)) with hκ
  have hκ0 : 0 < κ :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  set c : ℝ := 3 * (A + 1) / κ with hc
  have hc0 : 0 < c := by positivity
  set Φ : ℂ → ℂ := fun s => Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s + 1
    - RelaxedHerglotz.zetaRegular s + c * (s + 1 / 2) ^ (θ : ℂ) with hΦ
  refine ⟨c, hc0, Φ, ?_, ?_, ?_⟩
  · intro s hs
    simp only [mem_setOf_eq] at hs
    have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
    have hslit : s + 1 / 2 ∈ slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (((((differentiableAt_digamma_of_re_pos (by simp; linarith)).comp s
      ((differentiableAt_id).div_const 2)).div_const 2).sub_const _).add
      ((differentiableAt_const _).div differentiableAt_id hs0) |>.add_const _ |>.sub
      (RelaxedHerglotz.differentiable_zetaRegular s)).add ((differentiableAt_const _).mul ?_)
    exact (differentiableAt_id.add_const _).cpow_const hslit
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    have hX1 : (1 : ℝ) ≤ (2 + |s.im|) ^ θ :=
      Real.one_le_rpow (by linarith [abs_nonneg s.im]) hθ0.le
    have hZ : ‖RelaxedHerglotz.zetaRegular s‖ ≤ K₂ * (2 + |s.im|) ^ θ := by
      refine (hzeta s hs).trans (mul_le_mul_of_nonneg_left ?_ hK₂)
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im]) hθ.le
    have hZre : (RelaxedHerglotz.zetaRegular s).re ≤ K₂ * (2 + |s.im|) ^ θ :=
      (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans hZ)
    have hD : -max K₁ 0 ≤ (Complex.digamma (s / 2)).re :=
      (neg_le_neg (le_max_left K₁ 0)).trans (hdig s hs.le)
    have hinv : 0 ≤ (1 / s).re := by
      rw [one_div, Complex.inv_re]; exact div_nonneg hs0.le (Complex.normSq_nonneg _)
    have hpow : κ * ‖s + 1 / 2‖ ^ θ ≤ ((s + 1 / 2) ^ (θ : ℂ)).re :=
      RelaxedHerglotz.cos_mul_rpow_le_re_cpow (by simp; linarith) hθ0.le hθ1.le
    have hnorm : (2 + |s.im|) ^ θ ≤ 3 * ‖s + 1 / 2‖ ^ θ := by
      have h3 : (3 : ℝ) ^ θ ≤ 3 := by
        calc (3 : ℝ) ^ θ ≤ 3 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1.le
          _ = 3 := Real.rpow_one 3
      calc (2 + |s.im|) ^ θ ≤ (3 * ‖s + 1 / 2‖) ^ θ :=
            Real.rpow_le_rpow (by positivity) (RelaxedHerglotz.two_add_abs_im_le_three_mul_norm hs) hθ0.le
        _ = 3 ^ θ * ‖s + 1 / 2‖ ^ θ := Real.mul_rpow (by norm_num) (norm_nonneg _)
        _ ≤ 3 * ‖s + 1 / 2‖ ^ θ :=
            mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (norm_nonneg _) _)
    have hre : (Φ s).re = (Complex.digamma (s / 2)).re / 2 - Real.log Real.pi / 2 + (1 / s).re + 1
        - (RelaxedHerglotz.zetaRegular s).re + c * ((s + 1 / 2) ^ (θ : ℂ)).re := by
      simp only [hΦ, Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re,
        Complex.ofReal_re, Complex.re_ofReal_mul]
    have hcκ : c * κ = 3 * (A + 1) := by rw [hc]; field_simp
    have hboost : (A + 1) * (2 + |s.im|) ^ θ ≤ c * ((s + 1 / 2) ^ (θ : ℂ)).re := by
      calc (A + 1) * (2 + |s.im|) ^ θ ≤ (A + 1) * (3 * ‖s + 1 / 2‖ ^ θ) :=
            mul_le_mul_of_nonneg_left hnorm (by linarith)
        _ = c * (κ * ‖s + 1 / 2‖ ^ θ) := by rw [← mul_assoc c, hcκ]; ring
        _ ≤ c * ((s + 1 / 2) ^ (θ : ℂ)).re := mul_le_mul_of_nonneg_left hpow hc0.le
    rw [hre]
    set B : ℝ := max K₁ 0 / 2 + Real.log Real.pi / 2 + 1 with hB
    have hB1 : B ≤ B * (2 + |s.im|) ^ θ :=
      le_mul_of_one_le_right (by have := le_max_right K₁ 0; positivity) hX1
    have hsplit : (A + 1) * (2 + |s.im|) ^ θ = B * (2 + |s.im|) ^ θ + K₂ * (2 + |s.im|) ^ θ := by
      rw [hA, hB]; ring
    linarith
  · intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl 1 hs
    rw [WeilHerglotz.weilFunction, RelaxedHerglotz.LSeries_lamC_one hs]
    simp only [hΦ]
    rw [RelaxedHerglotz.zetaRegular_of_ne hs1]
    ring

/-! ### From the boosted producer to the boosted Weil cone -/

theorem rpow_le_one_add {x θ : ℝ} (hx : 0 ≤ x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : x ^ θ ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_one hx h hθ0
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hθ1
    rw [Real.rpow_one] at this
    linarith

/-- `‖(σ + it + ½)^θ‖ ≤ 3(1 + |t|)` for `0 ≤ σ ≤ 3/2`, `0 ≤ θ ≤ 1`. -/
theorem norm_boost_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {σ t : ℝ} (h1 : 0 ≤ σ) (h2 : σ ≤ 3 / 2) :
    ‖((σ : ℂ) + t * I + 1 / 2) ^ (θ : ℂ)‖ ≤ 3 * (1 + |t|) := by
  rw [Complex.norm_cpow_real]
  refine (rpow_le_one_add (norm_nonneg _) hθ0 hθ1).trans ?_
  have : ‖(σ : ℂ) + t * I + 1 / 2‖ ≤ 2 + |t| := by
    have e : (σ : ℂ) + t * I + 1 / 2 = ((σ + 1 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
    rw [e]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero, add_im, mul_im, zero_add]
    rw [abs_of_nonneg (by linarith)]
    linarith
  linarith [abs_nonneg t]

theorem boost_conj {θ : ℝ} {s : ℂ} (hs : 0 < s.re) :
    (conj s + 1 / 2) ^ (θ : ℂ) = conj ((s + 1 / 2) ^ (θ : ℂ)) := by
  have hy : 0 < (conj (s + 1 / 2)).re := by simp; linarith
  have hne : (conj (s + 1 / 2)).arg ≠ Real.pi := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy)
    intro h
    rw [h, abs_of_pos Real.pi_pos] at this
    linarith [Real.pi_pos]
  have h := Complex.cpow_conj (conj (s + 1 / 2)) (θ : ℂ) hne
  rw [Complex.conj_ofReal, Complex.conj_conj] at h
  have e : conj s + 1 / 2 = conj (s + 1 / 2) := by
    rw [map_add, map_div₀, map_one, map_ofNat]
  rw [e, h]

theorem hsl_one (σ : ℝ) (hσ : 1 < σ) :
    Summable fun n : ℕ => |(fun _ : ℕ => (1 : ℝ)) n| / (n : ℝ) ^ σ := by
  simpa using Real.summable_one_div_nat_rpow.mpr hσ

theorem integrable_normSq_paperFT_mul_rpow {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 3) :
    Integrable fun r : ℝ => ‖paperFT f r‖ ^ 2 * (1 + |r|) ^ θ := by
  obtain ⟨D, hD0, hD⟩ := WeilOneSided.exists_norm_paperFT_le_decay (⟨f, hf, hfc⟩ : WeilOneSided.WeilTestFn)
  have hbi : Integrable fun r : ℝ => D ^ 2 * (1 + ‖r‖) ^ (-(4 - θ)) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 4 - θ) (by simp; linarith)).const_mul _
  have hcont : Continuous fun r : ℝ => ‖paperFT f r‖ ^ 2 * (1 + |r|) ^ θ := by
    have h1 : Continuous fun r : ℝ => paperFT f r :=
      (WeilEF.differentiable_paperFT hf.continuous hfc).continuous.comp Complex.continuous_ofReal
    exact (h1.norm.pow 2).mul ((continuous_const.add continuous_abs).rpow_const
      fun r => Or.inr hθ0)
  refine hbi.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  have h1r : 0 < 1 + |r| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs]
  have hsq : ‖paperFT f r‖ ^ 2 ≤ (D / (1 + |r|) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hD r) 2
  have hpow : (1 + |r|) ^ (-(4 - θ)) = (1 + |r|) ^ θ / (1 + |r|) ^ (4 : ℝ) := by
    rw [show -(4 - θ) = θ - 4 by ring, Real.rpow_sub h1r]
  have h4 : (1 + |r|) ^ (4 : ℝ) = ((1 + |r|) ^ 2) ^ 2 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [hpow, h4]
  calc ‖paperFT f r‖ ^ 2 * (1 + |r|) ^ θ ≤ (D / (1 + |r|) ^ 2) ^ 2 * (1 + |r|) ^ θ :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = D ^ 2 * ((1 + |r|) ^ θ / ((1 + |r|) ^ 2) ^ 2) := by field_simp

/-- **The boosted Weil cone from a boosted producer.** -/
theorem weilCone_of_boostedProducer {θ c : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hc : 0 < c)
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re →
      Φ s = WeilHerglotz.weilFunction (fun _ => 1) s + c * (s + 1 / 2) ^ (θ : ℂ))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ (weilFullFunctional (fun _ => 1) (EF.weilTest f f)).re +
      1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * c * (1 + |r|) ^ θ) := by
  obtain ⟨D, hD0, hD⟩ := WeilAtomic.norm_Hfn_weilTest_le hf hfc
  obtain ⟨A, hA0, hAW⟩ := WeilAtomic.norm_weilFunction_le (lam := fun _ => 1) hsl_one
    (c := 5 / 4) (by norm_num) (by norm_num)
  set q : ℂ → ℂ := fun s => (s + 1 / 2) ^ (θ : ℂ) with hq
  set W : ℂ → ℂ := WeilHerglotz.weilFunction (fun _ => 1) with hW
  set G : ℂ → ℂ := fun s => W s + c * q s with hG
  set k := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  have hqd : DifferentiableOn ℂ q {s : ℂ | -(1 / 2) < s.re} := fun s hs =>
    ((differentiableAt_id.add_const _).cpow_const (Complex.mem_slitPlane_iff.mpr
      (Or.inl (by simp at hs ⊢; linarith)))).differentiableWithinAt
  have hqb : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 5 / 4 → ‖q (σ + t * I)‖ ≤ 3 * (1 + |t|) :=
    fun σ t h1 h2 => norm_boost_le hθ0.le hθ1.le (by linarith) (by linarith)
  -- the Herglotz line-integral inequality for `G`
  have hGconj : ∀ s : ℂ, 1 < s.re → G (conj s) = conj (G s) := by
    intro s hs
    simp only [hG, hq, hW]
    rw [WeilSpectral.weilFunction_conj, boost_conj (by linarith), map_add, map_mul,
      Complex.conj_ofReal]
  have hΦG : ∀ s : ℂ, 1 < s.re → Φ s = G s := hΦ
  have hconj : ∀ s : ℂ, 1 / 2 < s.re → Φ (conj s) = conj (Φ s) := fun s hs =>
    AtomDomination.herglotz_conj_of hΦd hΦG hGconj hs
  have hGb : ∀ t : ℝ, ‖G (((5 / 4 : ℝ) : ℂ) + t * I)‖ ≤ (A + 3 * c) * (1 + |t|) := by
    intro t
    simp only [hG]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have h1 := hAW t
    have h2 := hqb (5 / 4) t (by norm_num) le_rfl
    nlinarith [abs_nonneg t]
  have key := AtomDomination.re_lineIntegral_nonneg_of_herglotz hΦd hΦre hconj hΦG
    (by positivity) hGb hf hfc
  -- split the line integral
  set F : ℝ → ℂ := fun t => Hfn k (((5 / 4 : ℝ) : ℂ) + t * I) + Hfn k (1 - ((5 / 4 : ℝ) : ℂ) - t * I)
    with hF
  have hFc : Continuous F := by
    have hHd := (WeilLineIntegral.differentiable_Hfn hkd hkc).continuous
    exact (hHd.comp (by fun_prop : Continuous fun t : ℝ => ((5 / 4 : ℝ) : ℂ) + t * I)).add
      (hHd.comp (by fun_prop : Continuous fun t : ℝ => 1 - ((5 / 4 : ℝ) : ℂ) - t * I))
  have hFb : ∀ t : ℝ, ‖F t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := by
    intro t
    have e : (1 : ℂ) - ((5 / 4 : ℝ) : ℂ) - t * I = (((-1 / 4 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      push_cast; ring
    simp only [hF]
    rw [e]
    have h1 := hD (5 / 4) t (by norm_num) (by norm_num)
    have h2 := hD (-1 / 4) (-t) (by norm_num) (by norm_num)
    rw [neg_sq] at h2
    have h3 : 2 * D / (1 + t ^ 2) ^ 2 = D / (1 + t ^ 2) ^ 2 + D / (1 + t ^ 2) ^ 2 := by ring
    rw [h3]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have hline_cont : ∀ g : ℂ → ℂ, (∀ t : ℝ, ContinuousAt g (((5 / 4 : ℝ) : ℂ) + t * I)) →
      Continuous fun t : ℝ => g (((5 / 4 : ℝ) : ℂ) + t * I) := by
    intro g hg
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ContinuousAt.comp (g := g) (f := fun t : ℝ => ((5 / 4 : ℝ) : ℂ) + t * I) (hg t)
      (by fun_prop)
  have hqc : ∀ t : ℝ, ContinuousAt q (((5 / 4 : ℝ) : ℂ) + t * I) := fun t =>
    (LineShiftOn.differentiableAt_of_on hqd (by simp; norm_num)).continuousAt
  have hΦc : ∀ t : ℝ, ContinuousAt Φ (((5 / 4 : ℝ) : ℂ) + t * I) := fun t =>
    (LineShiftOn.differentiableAt_of_on hΦd (by simp; norm_num)).continuousAt
  have hWline : ∀ t : ℝ, W (((5 / 4 : ℝ) : ℂ) + t * I) =
      Φ (((5 / 4 : ℝ) : ℂ) + t * I) - c * q (((5 / 4 : ℝ) : ℂ) + t * I) := by
    intro t
    rw [hΦ _ (by simp; norm_num)]
    ring
  have hWc : Continuous fun t : ℝ => W (((5 / 4 : ℝ) : ℂ) + t * I) := by
    simp_rw [hWline]
    exact (hline_cont Φ hΦc).sub (continuous_const.mul (hline_cont q hqc))
  have hdom : ∀ B : ℝ, 0 ≤ B → Integrable fun t : ℝ => 2 * D / (1 + t ^ 2) ^ 2 * (B * (1 + |t|)) := by
    intro B hB
    refine (integrable_inv_one_add_sq.const_mul (4 * D * B)).mono' (by fun_prop) ?_
    refine Eventually.of_forall fun t => ?_
    have h1 : 0 < 1 + t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsq : (1 + |t|) ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
    calc 2 * D / (1 + t ^ 2) ^ 2 * (B * (1 + |t|)) ≤ 2 * D / (1 + t ^ 2) ^ 2 * (B * (2 * (1 + t ^ 2))) := by
          gcongr
      _ = 4 * D * B * (1 + t ^ 2)⁻¹ := by field_simp; ring
  have hIW : Integrable fun t : ℝ => F t * W (((5 / 4 : ℝ) : ℂ) + t * I) :=
    (hdom A hA0).mono' (hFc.mul hWc).aestronglyMeasurable (Eventually.of_forall fun t => by
      rw [norm_mul]; exact mul_le_mul (hFb t) (hAW t) (norm_nonneg _) (by positivity))
  have hIq : Integrable fun t : ℝ => F t * q (((5 / 4 : ℝ) : ℂ) + t * I) :=
    (hdom 3 (by norm_num)).mono' (hFc.mul (hline_cont q hqc)).aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [norm_mul]
        exact mul_le_mul (hFb t) (hqb (5 / 4) t (by norm_num) le_rfl) (norm_nonneg _) (by positivity))
  have hsplit : ∫ t : ℝ, F t * G (((5 / 4 : ℝ) : ℂ) + t * I) =
      (∫ t : ℝ, F t * W (((5 / 4 : ℝ) : ℂ) + t * I)) +
        c * ∫ t : ℝ, F t * q (((5 / 4 : ℝ) : ℂ) + t * I) := by
    rw [← integral_const_mul, ← integral_add hIW (hIq.const_mul _)]
    congr 1
    funext t
    simp only [hG]
    ring
  have hWeil : weilFullFunctional (fun _ => 1) k =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F t * W (((5 / 4 : ℝ) : ℂ) + t * I) :=
    WeilLineIntegral.weilFullFunctional_eq_line_integral hsl_one hkd hkc (by norm_num) (by norm_num)
  -- shift the boost to the critical line
  have hshift := LineShiftOn.integral_line_shift_critical_on hkd hkc hD (q := q) (a₀ := -(1 / 2))
    (by norm_num) hqd (b := 5 / 4) (A := 3) (by norm_num) (by norm_num) (by norm_num) hqb
  have hcrit : ∀ t : ℝ, (Hfn k ((1 / 2 : ℝ) + t * I) + Hfn k ((1 / 2 : ℝ) - t * I)) *
      q ((1 / 2 : ℝ) + t * I) =
      ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) * ((1 : ℂ) + t * I) ^ (θ : ℂ) := by
    intro t
    rw [hk, AtomDomination.Hfn_weilTest_critical hf.continuous hfc,
      AtomDomination.Hfn_weilTest_critical_neg hf.continuous hfc]
    simp only [hq]
    congr 1
    · push_cast; ring
    · congr 1; push_cast; ring
  simp_rw [hcrit] at hshift
  -- the critical-line boost integral is bounded by the density `(1 + |t|)^θ`
  set a : ℝ → ℝ := fun t => ‖paperFT f t‖ ^ 2 with ha
  have hia := integrable_normSq_paperFT_mul_rpow hf hfc hθ0.le (by linarith)
  have hib : Integrable fun t : ℝ => ‖paperFT f (-t)‖ ^ 2 * (1 + |t|) ^ θ := by
    have := hia.comp_neg
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [abs_neg, Complex.ofReal_neg]
  have hpw : ∀ t : ℝ, ‖((1 : ℂ) + t * I) ^ (θ : ℂ)‖ ≤ (1 + |t|) ^ θ := fun t => by
    rw [Complex.norm_cpow_real]
    refine Real.rpow_le_rpow (norm_nonneg _) ?_ hθ0.le
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hgc : Continuous fun t : ℝ =>
      ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) * ((1 : ℂ) + t * I) ^ (θ : ℂ) := by
    have h1 : Continuous fun t : ℝ => paperFT f t :=
      (WeilEF.differentiable_paperFT hf.continuous hfc).continuous.comp Complex.continuous_ofReal
    have h2 : Continuous fun t : ℝ => paperFT f (-(t : ℂ)) :=
      (WeilEF.differentiable_paperFT hf.continuous hfc).continuous.comp
        (Complex.continuous_ofReal.neg)
    refine (Complex.continuous_ofReal.comp ((h1.norm.pow 2).add ?_)).mul ?_
    · have : (fun t : ℝ => ‖paperFT f ((-t : ℝ) : ℂ)‖ ^ 2) = fun t : ℝ => ‖paperFT f (-(t : ℂ))‖ ^ 2 := by
        funext t; push_cast; rfl
      simp only [Complex.ofReal_neg] at this ⊢
      exact h2.norm.pow 2
    · refine continuous_iff_continuousAt.mpr fun t => ?_
      exact ContinuousAt.cpow (by fun_prop) continuousAt_const
        (Complex.mem_slitPlane_iff.mpr (Or.inl (by simp)))
  have hgi : Integrable fun t : ℝ =>
      ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) * ((1 : ℂ) + t * I) ^ (θ : ℂ) := by
    refine (hia.add hib).mono' hgc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2) * ‖((1 : ℂ) + t * I) ^ (θ : ℂ)‖ ≤
        (‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2) * (1 + |t|) ^ θ :=
          mul_le_mul_of_nonneg_left (hpw t) (by positivity)
      _ = ‖paperFT f t‖ ^ 2 * (1 + |t|) ^ θ + ‖paperFT f (-t)‖ ^ 2 * (1 + |t|) ^ θ := by ring
  have hreI : (∫ t : ℝ, ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) *
      ((1 : ℂ) + t * I) ^ (θ : ℂ)).re ≤ 2 * ∫ t : ℝ, ‖paperFT f t‖ ^ 2 * (1 + |t|) ^ θ := by
    have h1 := integral_re hgi
    simp only [RCLike.re_to_complex] at h1
    rw [← h1]
    have hmono : ∫ t : ℝ, (((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) *
        ((1 : ℂ) + t * I) ^ (θ : ℂ)).re ≤
        ∫ t : ℝ, (‖paperFT f t‖ ^ 2 * (1 + |t|) ^ θ + ‖paperFT f (-t)‖ ^ 2 * (1 + |t|) ^ θ) := by
      refine integral_mono hgi.re (hia.add hib) fun t => ?_
      simp only
      rw [Complex.re_ofReal_mul]
      have hre := (Complex.re_le_norm (((1 : ℂ) + t * I) ^ (θ : ℂ))).trans (hpw t)
      have h0 : 0 ≤ ‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hre h0]
    refine hmono.trans (le_of_eq ?_)
    rw [integral_add hia hib]
    have hneg : ∫ t : ℝ, ‖paperFT f (-t)‖ ^ 2 * (1 + |t|) ^ θ =
        ∫ t : ℝ, ‖paperFT f t‖ ^ 2 * (1 + |t|) ^ θ := by
      have := integral_neg_eq_self (fun t : ℝ => ‖paperFT f t‖ ^ 2 * (1 + |t|) ^ θ) volume
      simp only [abs_neg] at this
      exact_mod_cast this
    rw [hneg]
    ring
  -- assemble
  rw [hsplit, hshift] at key
  have hkey : 0 ≤ (weilFullFunctional (fun _ => 1) k).re +
      c / (2 * Real.pi) * (∫ t : ℝ, ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) *
        ((1 : ℂ) + t * I) ^ (θ : ℂ)).re := by
    rw [hWeil]
    have e : ((1 / (2 * Real.pi) : ℂ) * ((∫ t : ℝ, F t * W (((5 / 4 : ℝ) : ℂ) + t * I)) +
        c * ∫ t : ℝ, ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) *
          ((1 : ℂ) + t * I) ^ (θ : ℂ))).re =
        ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F t * W (((5 / 4 : ℝ) : ℂ) + t * I)).re +
        c / (2 * Real.pi) * (∫ t : ℝ, ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) *
          ((1 : ℂ) + t * I) ^ (θ : ℂ)).re := by
      rw [mul_add, Complex.add_re]
      congr 1
      rw [show (1 / (2 * Real.pi) : ℂ) * (c * ∫ t : ℝ, ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 :
          ℝ) : ℂ) * ((1 : ℂ) + t * I) ^ (θ : ℂ)) = ((c / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) *
            ((1 : ℂ) + t * I) ^ (θ : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    rw [← e]
    exact key
  have hdens : 1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * c * (1 + |r|) ^ θ) =
      c / (2 * Real.pi) * (2 * ∫ t : ℝ, ‖paperFT f t‖ ^ 2 * (1 + |t|) ^ θ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    congr 1
    funext r
    ring
  rw [hdens]
  have hcpos : 0 ≤ c / (2 * Real.pi) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hreI hcpos]

/-- **The cone-existence ladder.**  For an admissible growth exponent `μ` and `θ > μ`, the trivial
weights lie in the Weil cone with archimedean density `Ω_ζ + C(1 + |t|)^θ`: for every `f ∈ C²_c`
for which the boosted density pairing converges,
`0 ≤ Re W_{λ≡1}(f ⋆ f̃) + (1/2π) ∫ |f̂(r)|² C (1 + |r|)^θ dr`. -/
theorem trivialWeights_boostedWeilCone {μ θ : ℝ} (hμ : ZetaGrowthExponent μ) (hθ : μ < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Integrable (fun r : ℝ => ‖paperFT f r‖ ^ 2 * (1 + |r|) ^ θ) →
      0 ≤ (weilFullFunctional (fun _ => 1) (EF.weilTest f f)).re +
        1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (C * (1 + |r|) ^ θ) := by
  have hμ0 := hμ.nonneg
  -- a producer exponent `θ' ∈ (0, 1)` with `θ' ≤ θ`
  obtain ⟨θ', c, hθ'0, hθ'1, hθ'θ, hc, Φ, hΦd, hΦre, hΦ⟩ : ∃ θ' c : ℝ, 0 < θ' ∧ θ' < 1 ∧ θ' ≤ θ ∧
      0 < c ∧ ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
        (∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) ∧ ∀ s : ℂ, 1 < s.re →
          Φ s = WeilHerglotz.weilFunction (fun _ => 1) s + c * (s + 1 / 2) ^ (θ' : ℂ) := by
    by_cases hθ1 : θ < 1
    · obtain ⟨c, hc, Φ, h⟩ := exists_herglotz_trivialWeights_boosted_of_growth hμ hθ hθ1
      exact ⟨θ, c, by linarith, hθ1, le_rfl, hc, Φ, h⟩
    · push Not at hθ1
      by_cases hμ1 : μ < 1
      · obtain ⟨c, hc, Φ, h⟩ := exists_herglotz_trivialWeights_boosted_of_growth hμ
          (show μ < (μ + 1) / 2 by linarith) (by linarith)
        exact ⟨(μ + 1) / 2, c, by linarith, by linarith, by linarith, hc, Φ, h⟩
      · push Not at hμ1
        obtain ⟨c, hc, Φ, h⟩ := RelaxedHerglotz.exists_herglotz_trivialWeights_boosted
          (θ := 1 / 2) (by norm_num) (by norm_num)
        exact ⟨1 / 2, c, by norm_num, by norm_num, by linarith, hc, Φ, h⟩
  refine ⟨2 * c, by positivity, fun f hf hfc hint => ?_⟩
  have h := weilCone_of_boostedProducer hθ'0 hθ'1 hc hΦd hΦre hΦ hf hfc
  have hi' : Integrable fun r : ℝ => ‖paperFT f r‖ ^ 2 * (2 * c * (1 + |r|) ^ θ') :=
    ((integrable_normSq_paperFT_mul_rpow (θ := θ') hf hfc hθ'0.le (by linarith)).const_mul
      (2 * c)).congr
      (Eventually.of_forall fun r => by simp only; ring)
  have hmono : ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * c * (1 + |r|) ^ θ') ≤
      ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * c * (1 + |r|) ^ θ) := by
    refine integral_mono hi' ((hint.const_mul (2 * c)).congr
      (Eventually.of_forall fun r => by simp only; ring)) fun r => ?_
    have h1 : (1 + |r|) ^ θ' ≤ (1 + |r|) ^ θ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg r]) hθ'θ
    have h2 : 0 ≤ ‖paperFT f r‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 (by positivity : (0 : ℝ) ≤ 2 * c))]
  have hpos : 0 ≤ 1 / (2 * Real.pi) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmono hpos]

/-- **The convexity rung, unconditionally**: for every `θ > ¼` the trivial weights lie in the Weil cone
with archimedean density `Ω_ζ + C(1 + |t|)^θ`. -/
theorem trivialWeights_boostedWeilCone_of_quarter_lt {θ : ℝ} (hθ : 1 / 4 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Integrable (fun r : ℝ => ‖paperFT f r‖ ^ 2 * (1 + |r|) ^ θ) →
      0 ≤ (weilFullFunctional (fun _ => 1) (EF.weilTest f f)).re +
        1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (C * (1 + |r|) ^ θ) := by
  set θ' : ℝ := min θ (1 / 2) with hθ'
  have h1 : 1 / 4 < θ' := lt_min hθ (by norm_num)
  have h2 : θ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨c, hc, Φ, hΦd, hΦre, hΦ⟩ := RelaxedHerglotz.exists_herglotz_trivialWeights_boosted h1 h2
  refine ⟨2 * c, by positivity, fun f hf hfc hint => ?_⟩
  have h := weilCone_of_boostedProducer (by linarith) h2 hc hΦd hΦre hΦ hf hfc
  have hi' : Integrable fun r : ℝ => ‖paperFT f r‖ ^ 2 * (2 * c * (1 + |r|) ^ θ') :=
    ((integrable_normSq_paperFT_mul_rpow (θ := θ') hf hfc (by linarith) (by linarith)).const_mul
      (2 * c)).congr
      (Eventually.of_forall fun r => by simp only; ring)
  have hmono : ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * c * (1 + |r|) ^ θ') ≤
      ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * c * (1 + |r|) ^ θ) := by
    refine integral_mono hi' ((hint.const_mul (2 * c)).congr
      (Eventually.of_forall fun r => by simp only; ring)) fun r => ?_
    have h1 : (1 + |r|) ^ θ' ≤ (1 + |r|) ^ θ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg r]) (min_le_left _ _)
    have h2 : 0 ≤ ‖paperFT f r‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 (by positivity : (0 : ℝ) ≤ 2 * c))]
  have hpos : 0 ≤ 1 / (2 * Real.pi) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmono hpos]

end

end RHTower.TrivialWeightCone
