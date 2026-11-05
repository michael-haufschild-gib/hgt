import GaloisForLFunctions.FiniteFreeProbability.GenusOneStabilityClassification
import GaloisForLFunctions.FiniteFreeProbability.RealJensenHurwitzStability
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiRealReciprocalField

/-!
# The completed zeta function sits on the boundary of finite free stability

On every vertical line the functional equation forces drift zero for `w ↦ ξ(σ + iw)`:
`Re ξ'/ξ(σ) = Σ_ρ Re 1/(σ − ρ)`. By concentration (`HurwitzDeflation`):

* there is no stability margin: for every `σ`, `μ > 0` and all large `d`, the polynomial
  `R_d(ξ(σ + i·))` has a root with `Im x > −μ`, although for `σ ≥ 1` all roots have `Im x < 0`;
* for `σ ≥ 1`, or any `σ` right of all zeros, the proportion of roots with `Im x ≤ −μ` tends to `0`;
* **phase threshold**: `e^{c(s−σ)} ξ(s)` has all Jensen roots in `Im ≤ 0` on `Re s = σ` iff
  `ξ ≠ 0` on `Re s > σ` and `c ≥ 0`.

So `c = 0` is the exact critical phase, on every line: any negative exponential phase destabilizes
`ξ`, and stability of `ξ` cannot be proved with room to spare.
-/

open Polynomial Filter Topology Complex Metric
open GaloisForLFunctions.HTGeometry RHTower
open GaloisForLFunctions.ArithmeticCorrespondencePositivity

namespace FiniteFreeProbability

noncomputable section

/-! ## The normalized coefficients of `ξ` on a vertical line -/

/-- The Taylor coefficients of `w ↦ ξ(σ + iw)/ξ(σ)`. -/
def xiNormCoeff (σ : ℝ) (k : ℕ) : ℂ := xiShiftCoeff σ k / xi (σ : ℂ)

theorem xiNormCoeff_zero (σ : ℝ) : xiNormCoeff σ 0 = 1 := by
  have h := xi_ne_zero_of_real σ
  simp [xiNormCoeff, xiShiftCoeff, h]

theorem mk_xiShiftCoeff_eq (σ : ℝ) :
    PowerSeries.mk (xiShiftCoeff σ) = PowerSeries.C (xi (σ : ℂ)) * PowerSeries.mk (xiNormCoeff σ) := by
  have h := xi_ne_zero_of_real σ
  ext k
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, xiNormCoeff]
  field_simp

theorem roots_jensenRev_xiShift (σ : ℝ) (d : ℕ) :
    (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).roots =
      (jensenRev d (PowerSeries.mk (xiNormCoeff σ))).roots := by
  rw [mk_xiShiftCoeff_eq, jensenRev_C_mul, roots_C_mul _ (xi_ne_zero_of_real σ)]

theorem isRoot_jensenRev_xiShift_iff (σ : ℝ) (d : ℕ) (x : ℂ) :
    (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x ↔
      (jensenRev d (PowerSeries.mk (xiNormCoeff σ))).IsRoot x := by
  rw [mk_xiShiftCoeff_eq, jensenRev_C_mul, IsRoot, eval_mul, eval_C, mul_eq_zero, IsRoot]
  exact or_iff_right (xi_ne_zero_of_real σ)

theorem summable_xiNormCoeff (σ R : ℝ) : Summable fun k => ‖xiNormCoeff σ k‖ * R ^ k := by
  refine ((summable_xiShiftCoeff σ R).mul_left ‖xi (σ : ℂ)‖⁻¹).congr fun k => ?_
  simp only [xiNormCoeff, norm_div]
  ring

theorem tsum_xiNormCoeff (σ : ℝ) (u : ℂ) :
    ∑' k, xiNormCoeff σ k * u ^ k = xi ((σ : ℂ) + I * u) / xi (σ : ℂ) := by
  have h := (hasSum_xiShiftCoeff σ u).div_const (xi (σ : ℂ))
  rw [← h.tsum_eq]
  exact tsum_congr fun k => by simp only [xiNormCoeff]; ring

/-- `Im(ξ(σ + iw)/ξ(σ))'(0) = Re ξ'/ξ(σ)`. -/
theorem xiNormCoeff_one_im (σ : ℝ) : (xiNormCoeff σ 1).im = (logDeriv xi (σ : ℂ)).re := by
  have : xiNormCoeff σ 1 = I * logDeriv xi (σ : ℂ) := by
    rw [xiNormCoeff, xiShiftCoeff_eq, iteratedDeriv_one, logDeriv_apply]
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    ring
  rw [this]
  simp

/-- The zero `w_q = a_q + i(σ − 1/2)` of `w ↦ ξ(σ + iw)`. -/
def xiLineZero (σ : ℝ) (q : XiZeroCopy) : ℂ := xiSpectralPoint q + I * ((σ - 1 / 2 : ℝ) : ℂ)

theorem xiLineZero_ne (σ : ℝ) (q : XiZeroCopy) : xiLineZero σ q ≠ 0 := xiSpectralPoint_add_ne q

theorem xiLineZero_eq (σ : ℝ) (q : XiZeroCopy) : xiLineZero σ q = I * ((σ : ℂ) - (q.1 : ℂ)) := by
  rw [xiLineZero, xiSpectralPoint_eq_support, xiSpectralPointSupport]
  push_cast
  ring

theorem one_div_xiLineZero_im (σ : ℝ) (q : XiZeroCopy) :
    (1 / xiLineZero σ q).im = -xiRealReciprocal (σ : ℂ) 0 q := by
  rw [xiLineZero_eq, one_div, mul_inv, Complex.inv_I]
  simp [xiRealReciprocal]

/-- **Finitely many zeros factor out of `ξ` with multiplicity.** -/
theorem exists_xi_factor (σ : ℝ) (T : Finset XiZeroCopy) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ u : ℂ,
      ∑' k, xiNormCoeff σ k * u ^ k = (∏ q ∈ T, (1 - u / xiLineZero σ q)) * G u := by
  set δ : ℝ := σ - 1 / 2
  set Cc : ℂ → ℂ := canonicalProductE1Indexed
    (fun x : ↑((T : Set XiZeroCopy)ᶜ) => xiSpectralPoint x.1)
  have hCc : Differentiable ℂ Cc := differentiable_canonicalProduct_compl xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable (T : Set XiZeroCopy)
  have hCc' : Differentiable ℂ fun u => Cc (u - I * δ) := hCc.comp (by fun_prop)
  set K : ℂ := (xi (σ : ℂ))⁻¹ * XiC 0 * ∏ q ∈ T, weierstrassE1 (-(I * δ) / xiSpectralPoint q)
  set e : ℂ := ∑ q ∈ T, 1 / xiSpectralPoint q
  have hexp : Differentiable ℂ fun u : ℂ => K * Complex.exp (e * u) := by fun_prop
  refine ⟨fun u => K * Complex.exp (e * u) * Cc (u - I * δ), hexp.mul hCc', fun u => ?_⟩
  have h0 : XiC 0 ≠ 0 := XiC_zero_ne
  have hsplit := canonicalProductE1Indexed_split xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable (T : Set XiZeroCopy) (u - I * δ)
  rw [Finset.tprod_subtype' T fun q => weierstrassE1 ((u - I * δ) / xiSpectralPoint q)] at hsplit
  have hshift := xiCanonicalProduct_shift δ u
  rw [show (1 / 2 + δ : ℝ) = σ by simp only [δ]; ring] at hshift
  have hterm : ∀ q ∈ T, weierstrassE1 ((u - I * δ) / xiSpectralPoint q) =
      weierstrassE1 (-(I * δ) / xiSpectralPoint q) * (1 - u / xiLineZero σ q) *
        Complex.exp ((1 / xiSpectralPoint q) * u) := fun q _ => by
    rw [weierstrassE1_shift δ (xiSpectralPoint_ne_zero q) (xiSpectralPoint_add_ne q)]
    simp only [shiftedFactorPoly, eval_mul, eval_C, eval_sub, eval_one, eval_X, xiLineZero, δ]
    ring
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← Complex.exp_sum, ← Finset.sum_mul] at hsplit
  have hxi : xi ((σ : ℂ) + I * u) = XiC 0 * xiCanonicalProduct (u - I * δ) := by
    rw [hshift]
    field_simp
  have hC : xiCanonicalProduct (u - I * δ) = canonicalProductE1Indexed xiSpectralPoint (u - I * δ) :=
    rfl
  rw [tsum_xiNormCoeff, hxi, hC, ← hsplit, div_eq_mul_inv]
  change _ = _ * (K * Complex.exp (e * u) *
    (∏' x : ↑((T : Set XiZeroCopy)ᶜ), weierstrassE1 ((u - I * δ) / xiSpectralPoint x.1)))
  simp only [K, e]
  ring

/-! ## Concentration on the real axis -/

/-- **Stable lines concentrate.** If every root of every `R_d(ξ(σ + i·))` has `Im ≤ 0`, the proportion
of roots with `Im x ≤ −μ` tends to `0`, for every `μ > 0`. -/
theorem tendsto_card_filter_div_xi {σ : ℝ}
    (hstab : ∀ d x, (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x → x.im ≤ 0)
    {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun d : ℕ => (Multiset.card ((jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).roots.filter
      fun x => x.im ≤ -μ) : ℝ) / d) atTop (𝓝 0) := by
  classical
  simp only [roots_jensenRev_xiShift]
  refine tendsto_card_filter_div (xiNormCoeff_zero σ) (summable_xiNormCoeff σ)
    (fun d x hx => hstab d x ((isRoot_jensenRev_xiShift_iff σ d x).2 hx))
    (xiLineZero σ) (xiLineZero_ne σ) (fun ε hε => ?_) hμ
  have hsum := (xiRealReciprocal_summable (σ : ℂ) (h := 0) (by simp)).hasSum
  rw [← re_logDeriv_xi_eq_realReciprocal_tsum (xi_ne_zero_of_real σ)] at hsum
  obtain ⟨T, hT⟩ := (hsum.eventually (Metric.ball_mem_nhds _ hε)).exists
  obtain ⟨G, hG, hfac⟩ := exists_xi_factor σ T
  refine ⟨T, G, hG, hfac, ?_⟩
  rw [Real.dist_eq] at hT
  rw [xiNormCoeff_one_im]
  simp only [one_div_xiLineZero_im, Finset.sum_neg_distrib]
  have := (abs_lt.1 hT).1
  linarith

/-- **Unconditional concentration at `Re s ≥ 1`.** For `σ ≥ 1` all Jensen roots lie in `Im x < 0`, and
all but a vanishing proportion of them lie in every strip `−μ < Im x < 0`. -/
theorem tendsto_card_filter_div_xi_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun d : ℕ => (Multiset.card ((jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).roots.filter
      fun x => x.im ≤ -μ) : ℝ) / d) atTop (𝓝 0) :=
  tendsto_card_filter_div_xi (fun d _ hx => im_le_zero_of_one_le hσ d hx) hμ

/-- **There is no stability margin, on any line.** For every `σ`, every `μ > 0` and all large `d`, the
polynomial `R_d(ξ(σ + i·))` has a root with `Im x > −μ`. -/
theorem eventually_exists_root_im_gt_xi (σ : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ d : ℕ in atTop, ∃ x, (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x ∧ -μ < x.im := by
  by_cases hzf : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ
  · have h := tendsto_card_filter_div_xi (fun d _ hx => im_le_zero_of_zeroFree hzf d hx) hμ
    simp only [roots_jensenRev_xiShift] at h
    filter_upwards [eventually_exists_root_im_gt (xiNormCoeff_zero σ) h] with d hd
    obtain ⟨x, hx, hxim⟩ := hd
    exact ⟨x, (isRoot_jensenRev_xiShift_iff σ d x).2 hx, hxim⟩
  · push Not at hzf
    obtain ⟨ρ, hρ, hre⟩ := hzf
    obtain ⟨κ, hκ, hev⟩ := exists_linear_im_of_xi_zero hρ hre
    filter_upwards [hev] with d hd
    obtain ⟨x, hx, hxim⟩ := hd
    refine ⟨x, hx, ?_⟩
    have : 0 ≤ κ * d := by positivity
    linarith

/-- **The exact critical phase.** `e^{c(s−σ)} ξ(s)`, expanded on `Re s = σ`, has all reversed Jensen
roots in `Im ≤ 0` iff `ξ ≠ 0` on `Re s > σ` and `c ≥ 0`. -/
theorem jensenRev_phase_xi_stable_iff (σ c : ℝ) :
    (∀ d x, (jensenRev d (expSeries (I * c) * PowerSeries.mk (xiShiftCoeff σ))).IsRoot x → x.im ≤ 0) ↔
      (∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ) ∧ 0 ≤ c := by
  have him : ∀ y : ℂ, (y - I * c + I * c) = y := fun y => by ring
  have himsub : ∀ y : ℂ, (y - I * c).im = y.im - c := fun y => by simp
  constructor
  · intro h
    refine ⟨fun ρ hρ => re_le_of_frequently_im_le (K := c) (Frequently.of_forall fun d y hy => ?_) hρ,
      ?_⟩
    · have := h d (y - I * c) ((isRoot_jensenRev_expSeries_mul_iff d _ _ _).2 (by rwa [him]))
      rw [himsub] at this
      linarith
    · by_contra hc
      push Not at hc
      obtain ⟨d, y, hy, hyim⟩ := (eventually_exists_root_im_gt_xi σ (neg_pos.2 hc)).exists
      have := h d (y - I * c) ((isRoot_jensenRev_expSeries_mul_iff d _ _ _).2 (by rwa [him]))
      rw [himsub] at this
      linarith
  · rintro ⟨hzf, hc⟩ d x hx
    have := im_le_zero_of_zeroFree hzf d ((isRoot_jensenRev_expSeries_mul_iff d _ _ _).1 hx)
    simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add] at this
    linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.tendsto_card_filter_div_xi_of_one_le
#print axioms FiniteFreeProbability.eventually_exists_root_im_gt_xi
#print axioms FiniteFreeProbability.jensenRev_phase_xi_stable_iff
