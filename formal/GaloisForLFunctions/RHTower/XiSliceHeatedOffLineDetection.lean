import GaloisForLFunctions.RHTower.XiSliceBoundedDetectionOrder
import GaloisForLFunctions.RHTower.XiSliceHeatRateOnePlusDelta

/-!
# Heat cannot hide a near-line off-line zero below heat `δ²`

Let `ρ` be a zero of `ξ` off the critical line, `γ = Im ρ`, `δ = |Re ρ − ½|`, with `Ξ(γ) ≠ 0`, at most
`m` zero copies at `γ ± iδ` and inverse-square mass `Σ 1/|z − γ|² ≤ S` of the other copies.

**Theorem** (`exists_re_xiSliceHeatTransfer_neg_of_offLine_mass`).  With
`A = 72^m m! e^{1/8} e^{8δ²S}`, if `0 < λ`, `16 λ S ≤ 1`, `512 A λ ≤ δ²` and `8A < 2^N`, then some heated
slice coefficient `T_n(λ, 0, γ)` with `n < N` has negative real part.

So the slice heat threshold at the ordinate of `ρ` is at least `min(1/(16S), δ²/(512A))`.  For a
near-line zero (`δ²S ≤ 1`) this is `≍ δ²` (for fixed `m`): with the heated cone criterion, which makes
the pair factor heat-positive once `3λ ≥ δ²`, the local heat threshold at an isolated near-line
off-line ordinate is of exact order `δ²`.  Consequently every off-line zero bounds the WD heat
threshold from below (`le_wdHeatThreshold_of_offLine_mass`).

Proof.  Write `g = S(γ, ·)` and `c₀ = g(0) > 0`.  The product formula gives the envelope
`‖g(x)‖ ≤ c₀ (1 + ‖x‖²/δ²)^m e^{‖x‖²S}` (`norm_xiSliceProduct_le_envelope`).  The Gaussian
representation of the heated coefficients sums to the heated function at `δ`:
`√(2π) Σ_n T_n δⁿ = ∫ e^{−w²/2} g(√λ w + δ) dw` (`hasSum_xiSliceHeatTransfer_mul_pow`).  Since
`g(δ) = g′(δ) = 0` (both factors of the slice vanish at `δ`) and `g′(0) = 0`, second-order Taylor
bounds make the right side `O(λ/δ²)` and `T_0 = c₀ + O(λ/δ²)`, while Cauchy's estimate on circles
of radius `2δ` makes the orders `≥ N` contribute `O(2^{−N})`.  If `Re T_n ≥ 0` for `n < N`, then
`Re Σ T_n δⁿ ≥ Re T_0 − O(2^{−N})`, a contradiction.
-/

open Complex MeasureTheory Filter Topology Metric
open scoped ComplexOrder Nat

namespace RHTower.DeBruijn

noncomputable section

/-- The envelope `c₀ (1 + r²/δ²)^m e^{r² S}`. -/
def sliceEnvelope (c₀ δ S : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  c₀ * ((1 + r ^ 2 / δ ^ 2) ^ m * Real.exp (r ^ 2 * S))

theorem sliceEnvelope_mono {c₀ δ S : ℝ} {m : ℕ} (hc₀ : 0 ≤ c₀) (hS : 0 ≤ S) {r r' : ℝ}
    (hr : 0 ≤ r) (hrr : r ≤ r') : sliceEnvelope c₀ δ S m r ≤ sliceEnvelope c₀ δ S m r' := by
  unfold sliceEnvelope
  have hsq : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr hrr 2
  have h1 : (1 + r ^ 2 / δ ^ 2) ^ m ≤ (1 + r' ^ 2 / δ ^ 2) ^ m :=
    pow_le_pow_left₀ (by positivity) (by gcongr) m
  have h2 : Real.exp (r ^ 2 * S) ≤ Real.exp (r' ^ 2 * S) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsq hS)
  gcongr

/-- **The envelope of the slice at an off-line ordinate.** -/
theorem norm_xiSliceProduct_le_envelope {ρ : ℂ} (hne : ρ.re ≠ 1 / 2) (hΞ : XiC ρ.im ≠ 0) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I)) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S) (x : ℂ) :
    ‖xiSliceProduct ρ.im x‖
      ≤ sliceEnvelope (xiSliceCoeff ρ.im 0).re |ρ.re - 1 / 2| S m ‖x‖ := by
  classical
  set t : ℝ := ρ.im with htdef
  set δ : ℝ := |ρ.re - 1 / 2| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hc0 : xiSliceCoeff t 0 = xiSliceProduct t 0 := by simp [xiSliceCoeff]
  have hc0pos : 0 < (xiSliceCoeff t 0).re := xiSliceCoeff_zero_re_pos hΞ
  have hc0im : (xiSliceCoeff t 0).im = 0 := xiSliceCoeff_im_eq_zero t 0
  have hg0norm : ‖xiSliceProduct t 0‖ = (xiSliceCoeff t 0).re := by
    rw [← hc0]
    have hreal : xiSliceCoeff t 0 = (((xiSliceCoeff t 0).re : ℝ) : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hc0im)
    conv_lhs => rw [hreal]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0pos]
  set r := ‖x‖ with hr
  have hfinite : ∀ F : Finset XiZeroCopy,
      ‖∏ q ∈ F, (1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2)‖
        ≤ (1 + r ^ 2 / δ ^ 2) ^ m * Real.exp (r ^ 2 * S) := by
    intro F
    set own : XiZeroCopy → Prop := fun q =>
      xiSpectralPoint q = (t : ℂ) + (δ : ℂ) * I ∨ xiSpectralPoint q = (t : ℂ) - (δ : ℂ) * I
    rw [← Finset.prod_filter_mul_prod_filter_not F own, norm_mul, norm_prod, norm_prod]
    have hx2 : ‖x ^ 2‖ = r ^ 2 := by rw [norm_pow]
    have h1 : ∏ q ∈ F with own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖
        ≤ (1 + r ^ 2 / δ ^ 2) ^ m := by
      calc ∏ q ∈ F with own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖
          ≤ ∏ q ∈ F with own q, (1 + r ^ 2 / δ ^ 2) := by
            refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q hq => ?_
            have hsq : (xiSpectralPoint q - t) ^ 2 = -((δ : ℂ) ^ 2) := by
              rcases (Finset.mem_filter.mp hq).2 with h | h <;> rw [h] <;> ring_nf <;>
                rw [I_sq] <;> ring
            rw [hsq]
            calc ‖1 + x ^ 2 / -((δ : ℂ) ^ 2)‖ ≤ ‖(1 : ℂ)‖ + ‖x ^ 2 / -((δ : ℂ) ^ 2)‖ :=
                  norm_add_le _ _
              _ = 1 + r ^ 2 / δ ^ 2 := by
                  rw [norm_one, norm_div, norm_neg, hx2, norm_pow, Complex.norm_real,
                    Real.norm_eq_abs, abs_of_pos hδ]
        _ = (1 + r ^ 2 / δ ^ 2) ^ (F.filter own).card := by rw [Finset.prod_const]
        _ ≤ (1 + r ^ 2 / δ ^ 2) ^ m := pow_le_pow_right₀ (by
              have : 0 ≤ r ^ 2 / δ ^ 2 := by positivity
              linarith) (hown _ fun q hq => (Finset.mem_filter.mp hq).2)
    have h2 : ∏ q ∈ F with ¬ own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖ ≤
        Real.exp (r ^ 2 * S) := by
      calc ∏ q ∈ F with ¬ own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖
          ≤ ∏ q ∈ F with ¬ own q, Real.exp (r ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)) := by
            refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q _ => ?_
            calc ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖
                ≤ ‖(1 : ℂ)‖ + ‖x ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := norm_add_le _ _
              _ = r ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) + 1 := by
                  rw [norm_one, norm_div, hx2, norm_pow]; ring
              _ ≤ Real.exp (r ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)) :=
                  Real.add_one_le_exp _
        _ = Real.exp (r ^ 2 * ∑ q ∈ F with ¬ own q, 1 / ‖xiSpectralPoint q - t‖ ^ 2) := by
            rw [Finset.mul_sum, Real.exp_sum]
        _ ≤ Real.exp (r ^ 2 * S) := by
            apply Real.exp_le_exp.mpr
            have hsum := hS (F.filter fun q => ¬ own q) (fun q hq => (Finset.mem_filter.mp hq).2)
            exact mul_le_mul_of_nonneg_left hsum (by positivity)
    exact mul_le_mul h1 h2 (Finset.prod_nonneg fun q _ => norm_nonneg _) (by positivity)
  have hlim := (tendsto_prod_one_add_sq_div_xiSliceProduct hΞ x).norm
  have hle := le_of_tendsto hlim (Eventually.of_forall hfinite)
  rw [norm_div, hg0norm, div_le_iff₀ hc0pos] at hle
  unfold sliceEnvelope
  linarith

/-- **Second-order Taylor bound.**  If `‖g(z)‖ ≤ E(‖z‖)` with `E` monotone on `[0, ∞)` and
`g′(a) = 0`, then `‖g(a + u) − g(a)‖ ≤ 8 (‖u‖/r)² E(‖a‖ + r + ‖u‖)` for every `r > 0`. -/
theorem norm_xiSliceProduct_sub_le_of_deriv_eq_zero {t : ℝ} {E : ℝ → ℝ}
    (hEmono : ∀ r r', 0 ≤ r → r ≤ r' → E r ≤ E r') (hE : ∀ z, ‖xiSliceProduct t z‖ ≤ E ‖z‖)
    {a : ℂ} (ha : iteratedDeriv 1 (xiSliceProduct t) a = 0) {r : ℝ} (hr : 0 < r) (u : ℂ) :
    ‖xiSliceProduct t (a + u) - xiSliceProduct t a‖
      ≤ 8 * (‖u‖ / r) ^ 2 * E (‖a‖ + r + ‖u‖) := by
  have hE0 : ∀ s, 0 ≤ s → 0 ≤ E s := by
    intro s hs
    have h := hE (s : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] at h
    exact le_trans (norm_nonneg _) h
  set q := ‖u‖ / r with hq
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hr.le
  have hbig : E (‖a‖ + r) ≤ E (‖a‖ + r + ‖u‖) :=
    hEmono _ _ (by positivity) (by linarith [norm_nonneg u])
  by_cases hsmall : q ≤ 1 / 2
  · -- Taylor series at `a`
    have hT := Complex.hasSum_taylorSeries_of_entire (differentiable_xiSliceProduct t) a (a + u)
    simp only [add_sub_cancel_left, smul_eq_mul] at hT
    have hT2 := (hasSum_nat_add_iff' 2).mpr hT
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
      Nat.cast_one, inv_one, pow_zero, one_mul, iteratedDeriv_zero, Nat.factorial_one, pow_one,
      ha, mul_zero, add_zero] at hT2
    have hcauchy : ∀ k : ℕ, ‖iteratedDeriv k (xiSliceProduct t) a‖
        ≤ k ! * E (‖a‖ + r) / r ^ k := fun k =>
      norm_iteratedDeriv_xiSliceProduct_le t k hr fun z hz => by
        refine le_trans (hE z) (hEmono _ _ (norm_nonneg _) ?_)
        have := norm_sub_norm_le z a
        rw [mem_sphere_iff_norm.mp hz] at this
        linarith
    have hgeom : HasSum (fun k : ℕ => E (‖a‖ + r) * q ^ 2 * q ^ k)
        (E (‖a‖ + r) * q ^ 2 * (1 - q)⁻¹) :=
      (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left _
    have hle := hT2.norm_le_of_bounded hgeom fun k => by
      rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
      have hk := hcauchy (k + 2)
      have hfac : (0 : ℝ) < ((k + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      calc (((k + 2)! : ℝ))⁻¹ * (‖u‖ ^ (k + 2) * ‖iteratedDeriv (k + 2) (xiSliceProduct t) a‖)
          ≤ (((k + 2)! : ℝ))⁻¹ * (‖u‖ ^ (k + 2) * ((k + 2)! * E (‖a‖ + r) / r ^ (k + 2))) := by
            gcongr
        _ = E (‖a‖ + r) * q ^ 2 * q ^ k := by
            rw [hq, div_pow, div_pow]; field_simp; ring
    have h12 : (1 - q)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hEa := hE0 (‖a‖ + r) (by positivity)
    calc ‖xiSliceProduct t (a + u) - xiSliceProduct t a‖
        ≤ E (‖a‖ + r) * q ^ 2 * (1 - q)⁻¹ := hle
      _ ≤ E (‖a‖ + r) * q ^ 2 * 2 := by gcongr
      _ ≤ 8 * q ^ 2 * E (‖a‖ + r + ‖u‖) := by nlinarith [sq_nonneg q]
  · push Not at hsmall
    have h1 : ‖xiSliceProduct t (a + u)‖ ≤ E (‖a‖ + r + ‖u‖) :=
      le_trans (hE _) (hEmono _ _ (norm_nonneg _) (by linarith [norm_add_le a u]))
    have h2 : ‖xiSliceProduct t a‖ ≤ E (‖a‖ + r + ‖u‖) :=
      le_trans (hE _) (hEmono _ _ (norm_nonneg _) (by linarith [norm_nonneg u]))
    have hq4 : 1 ≤ 4 * q ^ 2 := by nlinarith
    have hEb := hE0 (‖a‖ + r + ‖u‖) (by positivity)
    calc ‖xiSliceProduct t (a + u) - xiSliceProduct t a‖
        ≤ ‖xiSliceProduct t (a + u)‖ + ‖xiSliceProduct t a‖ := norm_sub_le _ _
      _ ≤ 2 * E (‖a‖ + r + ‖u‖) := by linarith
      _ ≤ 8 * q ^ 2 * E (‖a‖ + r + ‖u‖) := by nlinarith

/-- Both factors of the slice vanish at the horizontal offset of an off-line zero. -/
theorem xi_zero_at_offset {ρ : ℂ} (hρ : xi ρ = 0) :
    xi (1 / 2 + ((|ρ.re - 1 / 2| : ℝ) : ℂ) + (ρ.im : ℂ) * I) = 0 ∧
      xi (1 / 2 - ((|ρ.re - 1 / 2| : ℝ) : ℂ) + (ρ.im : ℂ) * I) = 0 := by
  have hρ' : xi (1 - (starRingEnd ℂ) ρ) = 0 := by
    rw [xi_one_sub, xi_conj, hρ, map_zero]
  have e1 : ρ = 1 / 2 + (((ρ.re - 1 / 2 : ℝ)) : ℂ) + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have e2 : 1 - (starRingEnd ℂ) ρ = 1 / 2 - (((ρ.re - 1 / 2 : ℝ)) : ℂ) + (ρ.im : ℂ) * I := by
    apply Complex.ext
    · simp; ring
    · simp
  rcases le_total 0 (ρ.re - 1 / 2) with h | h
  · rw [abs_of_nonneg h]
    exact ⟨e1 ▸ hρ, e2 ▸ hρ'⟩
  · rw [abs_of_nonpos h]
    have e3 : (1 / 2 : ℂ) + (((-(ρ.re - 1 / 2)) : ℝ) : ℂ) + (ρ.im : ℂ) * I
        = 1 / 2 - (((ρ.re - 1 / 2 : ℝ)) : ℂ) + (ρ.im : ℂ) * I := by push_cast; ring
    have e4 : (1 / 2 : ℂ) - (((-(ρ.re - 1 / 2)) : ℝ) : ℂ) + (ρ.im : ℂ) * I
        = 1 / 2 + (((ρ.re - 1 / 2 : ℝ)) : ℂ) + (ρ.im : ℂ) * I := by push_cast; ring
    rw [e3, e4]
    exact ⟨e2 ▸ hρ', e1 ▸ hρ⟩

/-- The slice has a double zero at the horizontal offset of an off-line zero. -/
theorem xiSliceProduct_offset_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) :
    xiSliceProduct ρ.im ((|ρ.re - 1 / 2| : ℝ) : ℂ) = 0 ∧
      iteratedDeriv 1 (xiSliceProduct ρ.im) ((|ρ.re - 1 / 2| : ℝ) : ℂ) = 0 := by
  obtain ⟨h1, h2⟩ := xi_zero_at_offset hρ
  set δ : ℂ := ((|ρ.re - 1 / 2| : ℝ) : ℂ)
  refine ⟨by unfold xiSliceProduct; rw [h1, zero_mul], ?_⟩
  rw [iteratedDeriv_one]
  have hf : HasDerivAt (fun x : ℂ => xi (1 / 2 + x + (ρ.im : ℂ) * I))
      (deriv xi (1 / 2 + δ + (ρ.im : ℂ) * I) * 1) δ := by
    have := ((hasDerivAt_id δ).const_add (1 / 2 : ℂ)).add_const ((ρ.im : ℂ) * I)
    exact (xi_differentiable _).hasDerivAt.comp δ (by simpa using this)
  have hg : HasDerivAt (fun x : ℂ => xi (1 / 2 - x + (ρ.im : ℂ) * I))
      (deriv xi (1 / 2 - δ + (ρ.im : ℂ) * I) * (-1)) δ := by
    have := ((hasDerivAt_id δ).const_sub (1 / 2 : ℂ)).add_const ((ρ.im : ℂ) * I)
    exact (xi_differentiable _).hasDerivAt.comp δ (by simpa using this)
  have hfg : HasDerivAt (fun x : ℂ =>
      xi (1 / 2 + x + (ρ.im : ℂ) * I) * xi (1 / 2 - x + (ρ.im : ℂ) * I)) _ δ := hf.mul hg
  have e : xiSliceProduct ρ.im = fun x : ℂ =>
      xi (1 / 2 + x + (ρ.im : ℂ) * I) * xi (1 / 2 - x + (ρ.im : ℂ) * I) := by
    funext x; rfl
  rw [e, hfg.deriv, h1, h2]
  ring

/-- The slice is even, so its first derivative vanishes at `0`. -/
theorem iteratedDeriv_one_xiSliceProduct_zero (t : ℝ) :
    iteratedDeriv 1 (xiSliceProduct t) 0 = 0 := by
  have h := iteratedDeriv_comp_neg 1 (xiSliceProduct t) 0
  have hf : (fun x => xiSliceProduct t (-x)) = xiSliceProduct t := funext (xiSliceProduct_neg t)
  rw [hf, neg_zero, pow_one, neg_one_smul] at h
  have := congrArg (· * (1 / 2 : ℂ)) (show iteratedDeriv 1 (xiSliceProduct t) 0
    + iteratedDeriv 1 (xiSliceProduct t) 0 = 0 by
      nth_rewrite 2 [h]; ring)
  simp only [zero_mul] at this
  linear_combination this

/-- **The heated function at a real point.**  `√(2π) Σ_n T_n(λ, 0, t) δⁿ = ∫ e^{−w²/2} g(√λ w + δ) dw`,
with `‖√(2π) T_n δⁿ‖ ≤ 2^{−n} ∫ e^{−w²/2} E(√λ|w| + 2δ) dw` for any monotone envelope `E` of the slice. -/
theorem hasSum_xiSliceHeatTransfer_mul_pow {t lam δ : ℝ} (hlam : 0 ≤ lam) (hδ : 0 < δ)
    {E : ℝ → ℝ} (hEmono : ∀ r r', 0 ≤ r → r ≤ r' → E r ≤ E r')
    (hE : ∀ z, ‖xiSliceProduct t z‖ ≤ E ‖z‖)
    (hint : Integrable (fun w : ℝ => Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + 2 * δ))) :
    HasSum (fun n : ℕ => ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 t n
        * (δ : ℂ) ^ n)
      (∫ w : ℝ, ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
        * xiSliceProduct t (((Real.sqrt lam * w : ℝ) : ℂ) + δ)) ∧
    ∀ n : ℕ, ‖((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 t n * (δ : ℂ) ^ n‖
      ≤ (1 / 2) ^ n * ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + 2 * δ) := by
  set I₀ := ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + 2 * δ) with hI₀
  set F : ℕ → ℝ → ℂ := fun n w => ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
    * (iteratedDeriv n (xiSliceProduct t) ((Real.sqrt lam * w : ℝ) : ℂ) / n.factorial)
    * (δ : ℂ) ^ n with hF
  have hFint : ∀ n, Integrable (F n) := fun n =>
    (integrable_gauss_mul_iteratedDeriv_xiSliceProduct hlam t n).mul_const _
  have hFeq : ∀ n, ∫ w, F n w = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
      * xiSliceHeatTransfer lam 0 t n * (δ : ℂ) ^ n := by
    intro n
    simp only [hF]
    rw [integral_mul_const, ← xiSliceHeatTransfer_eq_integral_iteratedDeriv hlam t n]
  have hFbound : ∀ n w, ‖F n w‖ ≤ (1 / 2) ^ n
      * (Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + 2 * δ)) := by
    intro n w
    have hx : ‖((Real.sqrt lam * w : ℝ) : ℂ)‖ = Real.sqrt lam * |w| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hc := norm_iteratedDeriv_xiSliceProduct_le t n (x := ((Real.sqrt lam * w : ℝ) : ℂ))
      (r := 2 * δ) (M := E (Real.sqrt lam * |w| + 2 * δ)) (by linarith) fun z hz => by
        refine le_trans (hE z) (hEmono _ _ (norm_nonneg _) ?_)
        have := norm_sub_norm_le z ((Real.sqrt lam * w : ℝ) : ℂ)
        rw [mem_sphere_iff_norm.mp hz, hx] at this
        linarith
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    simp only [hF]
    rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_natCast, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hδ]
    have hδn : (0 : ℝ) < (2 * δ) ^ n := by positivity
    calc Real.exp (-(w ^ 2 / 2)) * (‖iteratedDeriv n (xiSliceProduct t)
          ((Real.sqrt lam * w : ℝ) : ℂ)‖ / n.factorial) * δ ^ n
        ≤ Real.exp (-(w ^ 2 / 2)) * ((n.factorial * E (Real.sqrt lam * |w| + 2 * δ)
            / (2 * δ) ^ n) / n.factorial) * δ ^ n := by gcongr
      _ = (1 / 2) ^ n * (Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + 2 * δ)) := by
          rw [mul_pow, one_div_pow]
          field_simp
  have hFnorm : ∀ n, ∫ w, ‖F n w‖ ≤ (1 / 2) ^ n * I₀ := by
    intro n
    rw [hI₀, ← integral_const_mul]
    exact integral_mono_of_nonneg (Eventually.of_forall fun w => norm_nonneg _)
      (hint.const_mul _) (Eventually.of_forall (hFbound n))
  have hsum : Summable fun n => ∫ w, ‖F n w‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun w => norm_nonneg _) hFnorm
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right I₀)
  have hHS := hasSum_integral_of_summable_integral_norm hFint hsum
  have htsum : ∀ w, ∑' n, F n w = ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
      * xiSliceProduct t (((Real.sqrt lam * w : ℝ) : ℂ) + δ) := by
    intro w
    have hT := Complex.hasSum_taylorSeries_of_entire (differentiable_xiSliceProduct t)
      ((Real.sqrt lam * w : ℝ) : ℂ) (((Real.sqrt lam * w : ℝ) : ℂ) + δ)
    simp only [add_sub_cancel_left, smul_eq_mul] at hT
    refine ((hT.mul_left ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)).congr_fun ?_).tsum_eq
    intro n
    simp only [hF]
    ring
  simp only [htsum, hFeq] at hHS
  refine ⟨hHS, fun n => ?_⟩
  rw [← hFeq]
  exact le_trans (norm_integral_le_integral_norm _) (hFnorm n)

/-- Gaussian control of the envelope along `√λ|w| + 2δ`. -/
theorem gauss_mul_sliceEnvelope_le {c₀ δ S lam : ℝ} (hc₀ : 0 ≤ c₀) (hδ : 0 < δ) (hS : 0 ≤ S)
    (hlam0 : 0 ≤ lam) (hlamδ : lam ≤ δ ^ 2) (hlamS : 16 * lam * S ≤ 1) (m : ℕ) (w : ℝ) :
    Real.exp (-(w ^ 2 / 2)) * sliceEnvelope c₀ δ S m (Real.sqrt lam * |w| + 2 * δ)
      ≤ c₀ * (72 ^ m * m ! * Real.exp (1 / 8) * Real.exp (8 * δ ^ 2 * S))
        * Real.exp (-(1 / 4) * w ^ 2) := by
  unfold sliceEnvelope
  set r := Real.sqrt lam * |w| + 2 * δ with hr
  have hsq : (Real.sqrt lam * |w|) ^ 2 = lam * w ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hlam0, sq_abs]
  have hr2 : r ^ 2 ≤ 2 * (lam * w ^ 2) + 8 * δ ^ 2 := by
    rw [hr]; nlinarith [sq_nonneg (Real.sqrt lam * |w| - 2 * δ)]
  have hδ2 : 0 < δ ^ 2 := by positivity
  -- the polynomial factor
  have hpoly1 : 1 + r ^ 2 / δ ^ 2 ≤ 9 * (1 + w ^ 2) := by
    rw [show 1 + r ^ 2 / δ ^ 2 = (δ ^ 2 + r ^ 2) / δ ^ 2 by field_simp, div_le_iff₀ hδ2]
    nlinarith [hr2, mul_le_mul_of_nonneg_right hlamδ (sq_nonneg w)]
  have hfact : (1 + w ^ 2) ^ m ≤ 8 ^ m * m ! * Real.exp ((1 + w ^ 2) / 8) := by
    have h := Real.pow_div_factorial_le_exp ((1 + w ^ 2) / 8) (by positivity) m
    have hm : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hm, div_pow] at h
    have h8 : (0 : ℝ) < 8 ^ m := by positivity
    rw [div_le_iff₀ h8] at h
    linarith [show Real.exp ((1 + w ^ 2) / 8) * m ! * 8 ^ m
      = 8 ^ m * m ! * Real.exp ((1 + w ^ 2) / 8) by ring]
  have hpoly : (1 + r ^ 2 / δ ^ 2) ^ m ≤ 72 ^ m * m ! * Real.exp ((1 + w ^ 2) / 8) := by
    calc (1 + r ^ 2 / δ ^ 2) ^ m ≤ (9 * (1 + w ^ 2)) ^ m :=
          pow_le_pow_left₀ (by positivity) hpoly1 m
      _ = 9 ^ m * (1 + w ^ 2) ^ m := mul_pow _ _ _
      _ ≤ 9 ^ m * (8 ^ m * m ! * Real.exp ((1 + w ^ 2) / 8)) := by gcongr
      _ = 72 ^ m * m ! * Real.exp ((1 + w ^ 2) / 8) := by
          rw [show (72 : ℝ) ^ m = 9 ^ m * 8 ^ m by rw [← mul_pow]; norm_num]; ring
  -- the exponential factor
  have hexp : Real.exp (r ^ 2 * S) ≤ Real.exp (8 * δ ^ 2 * S) * Real.exp (w ^ 2 / 8) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right hr2 hS
    have h2 : 2 * (lam * w ^ 2) * S ≤ w ^ 2 / 8 := by
      have := mul_le_mul_of_nonneg_right hlamS (sq_nonneg w)
      nlinarith
    nlinarith
  have hE0 : 0 ≤ Real.exp (r ^ 2 * S) := (Real.exp_pos _).le
  have hP0 : 0 ≤ (1 + r ^ 2 / δ ^ 2) ^ m := by positivity
  calc Real.exp (-(w ^ 2 / 2)) * (c₀ * ((1 + r ^ 2 / δ ^ 2) ^ m * Real.exp (r ^ 2 * S)))
      ≤ Real.exp (-(w ^ 2 / 2)) * (c₀ * ((72 ^ m * m ! * Real.exp ((1 + w ^ 2) / 8))
          * (Real.exp (8 * δ ^ 2 * S) * Real.exp (w ^ 2 / 8)))) := by gcongr
    _ = c₀ * (72 ^ m * m ! * Real.exp (1 / 8) * Real.exp (8 * δ ^ 2 * S))
          * Real.exp (-(1 / 4) * w ^ 2) := by
        have e : Real.exp ((1 + w ^ 2) / 8) = Real.exp (1 / 8) * Real.exp (w ^ 2 / 8) := by
          rw [← Real.exp_add]; ring_nf
        rw [e]
        have e2 : Real.exp (-(w ^ 2 / 2)) * Real.exp (w ^ 2 / 8) * Real.exp (w ^ 2 / 8)
            = Real.exp (-(1 / 4) * w ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        calc Real.exp (-(w ^ 2 / 2)) * (c₀ * (72 ^ m * m ! * (Real.exp (1 / 8)
              * Real.exp (w ^ 2 / 8)) * (Real.exp (8 * δ ^ 2 * S) * Real.exp (w ^ 2 / 8))))
            = c₀ * (72 ^ m * m ! * Real.exp (1 / 8) * Real.exp (8 * δ ^ 2 * S))
              * (Real.exp (-(w ^ 2 / 2)) * Real.exp (w ^ 2 / 8) * Real.exp (w ^ 2 / 8)) := by
              ring
          _ = _ := by rw [e2]

theorem sq_mul_exp_neg_quarter_le (w : ℝ) :
    w ^ 2 * Real.exp (-(1 / 4) * w ^ 2) ≤ 8 * Real.exp (-(1 / 8) * w ^ 2) := by
  have h := Real.add_one_le_exp (w ^ 2 / 8)
  have e : Real.exp (-(1 / 4) * w ^ 2) = Real.exp (-(1 / 8) * w ^ 2) * Real.exp (-(w ^ 2 / 8)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have h2 : w ^ 2 * Real.exp (-(w ^ 2 / 8)) ≤ 8 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith [sq_nonneg w]
  have hp := Real.exp_pos (-(1 / 8) * w ^ 2)
  nlinarith

/-- **Heated detection of an off-line zero.**  With `δ = |Re ρ − ½|` and
`A = 72^m m! e^{1/8} e^{8δ²S}`: if `0 < λ`, `16 λ S ≤ 1`, `512 A λ ≤ δ²` and `8A < 2^N`, some heated
slice coefficient `T_n(λ, 0, γ)`, `n < N`, has negative real part. -/
theorem exists_re_xiSliceHeatTransfer_neg_of_offLine_mass {ρ : ℂ} (hρ : xi ρ = 0)
    (hne : ρ.re ≠ 1 / 2) (hΞ : XiC ρ.im ≠ 0) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I)) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S)
    {lam : ℝ} (hlam : 0 < lam) (hlamS : 16 * lam * S ≤ 1)
    (hlamδ : 512 * (72 ^ m * m ! * Real.exp (1 / 8) * Real.exp (8 * |ρ.re - 1 / 2| ^ 2 * S))
      * lam ≤ |ρ.re - 1 / 2| ^ 2)
    {N : ℕ} (hN : 8 * (72 ^ m * m ! * Real.exp (1 / 8) * Real.exp (8 * |ρ.re - 1 / 2| ^ 2 * S))
      < 2 ^ N) :
    ∃ n < N, (xiSliceHeatTransfer lam 0 ρ.im n).re < 0 := by
  classical
  set t : ℝ := ρ.im with htdef
  set δ : ℝ := |ρ.re - 1 / 2| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hS0 : 0 ≤ S := by simpa using hS ∅ (by simp)
  set A := 72 ^ m * m ! * Real.exp (1 / 8) * Real.exp (8 * δ ^ 2 * S) with hA
  have hA1 : 1 ≤ A := by
    have h1 : (1 : ℝ) ≤ 72 ^ m := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ m ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
    have h3 : (1 : ℝ) ≤ Real.exp (1 / 8) := Real.one_le_exp (by norm_num)
    have h4 : (1 : ℝ) ≤ Real.exp (8 * δ ^ 2 * S) := Real.one_le_exp (by positivity)
    calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ A := by rw [hA]; gcongr
  set c₀ := (xiSliceCoeff t 0).re with hc₀def
  have hc₀ : 0 < c₀ := by simpa using xiSliceCoeff_zero_re_pos hΞ
  have hEmono : ∀ r r', 0 ≤ r → r ≤ r' → sliceEnvelope c₀ δ S m r ≤ sliceEnvelope c₀ δ S m r' :=
    fun r r' hr hrr => sliceEnvelope_mono hc₀.le hS0 hr hrr
  have hE : ∀ z, ‖xiSliceProduct t z‖ ≤ sliceEnvelope c₀ δ S m ‖z‖ :=
    norm_xiSliceProduct_le_envelope hne hΞ hown hS
  have hEnn : ∀ r, 0 ≤ sliceEnvelope c₀ δ S m r := fun r => by
    unfold sliceEnvelope; positivity
  have hlamδ' : lam ≤ δ ^ 2 := by nlinarith
  -- Gaussian control
  set B : ℝ → ℝ := fun w => c₀ * A * Real.exp (-(1 / 8) * w ^ 2) with hBdef
  have hBint : Integrable B :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 8)).const_mul _
  have hBval : ∫ w, B w = c₀ * A * Real.sqrt (8 * Real.pi) := by
    simp only [hBdef]
    rw [integral_const_mul, integral_gaussian]
    congr 2; ring
  have hG := gauss_mul_sliceEnvelope_le hc₀.le hδ hS0 hlam.le hlamδ' hlamS m
  have hGB : ∀ w, Real.exp (-(w ^ 2 / 2)) * sliceEnvelope c₀ δ S m (Real.sqrt lam * |w| + 2 * δ)
      ≤ B w := fun w => by
    refine le_trans (hG w) ?_
    simp only [hBdef]
    gcongr
    nlinarith [sq_nonneg w]
  have hG2 : ∀ w, w ^ 2 * (Real.exp (-(w ^ 2 / 2))
      * sliceEnvelope c₀ δ S m (Real.sqrt lam * |w| + 2 * δ)) ≤ 8 * B w := fun w => by
    have h1 := mul_le_mul_of_nonneg_left (hG w) (sq_nonneg w)
    have h2 := sq_mul_exp_neg_quarter_le w
    have hcA : 0 ≤ c₀ * A := by positivity
    simp only [hBdef]
    nlinarith [mul_le_mul_of_nonneg_left h2 hcA]
  have hcont : Continuous fun w : ℝ =>
      Real.exp (-(w ^ 2 / 2)) * sliceEnvelope c₀ δ S m (Real.sqrt lam * |w| + 2 * δ) := by
    unfold sliceEnvelope; fun_prop
  have hint : Integrable fun w : ℝ =>
      Real.exp (-(w ^ 2 / 2)) * sliceEnvelope c₀ δ S m (Real.sqrt lam * |w| + 2 * δ) :=
    hBint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hEnn _))]
      exact hGB w)
  obtain ⟨hHS, hbd⟩ := hasSum_xiSliceHeatTransfer_mul_pow hlam.le hδ hEmono hE hint
  have hI₀ : ∫ w, Real.exp (-(w ^ 2 / 2)) * sliceEnvelope c₀ δ S m (Real.sqrt lam * |w| + 2 * δ)
      ≤ c₀ * A * Real.sqrt (8 * Real.pi) := by
    rw [← hBval]; exact integral_mono hint hBint hGB
  have hsqrt8 : Real.sqrt (8 * Real.pi) = 2 * Real.sqrt (2 * Real.pi) := by
    rw [show (8 : ℝ) * Real.pi = 2 ^ 2 * (2 * Real.pi) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  -- the heated function at `δ` is small
  obtain ⟨hzero, hzero'⟩ := xiSliceProduct_offset_eq_zero hρ
  rw [← htdef, ← hδdef] at hzero hzero'
  have hδn : ‖((δ : ℝ) : ℂ)‖ = δ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have hun : ∀ w : ℝ, ‖((Real.sqrt lam * w : ℝ) : ℂ)‖ = Real.sqrt lam * |w| := fun w => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hq2 : ∀ w : ℝ, (Real.sqrt lam * |w| / δ) ^ 2 = lam * w ^ 2 / δ ^ 2 := fun w => by
    rw [div_pow, mul_pow, Real.sq_sqrt hlam.le, sq_abs]
  have hVpt : ∀ w : ℝ, ‖((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
      * xiSliceProduct t (((Real.sqrt lam * w : ℝ) : ℂ) + δ)‖ ≤ 8 * lam / δ ^ 2 * (8 * B w) := by
    intro w
    have h := norm_xiSliceProduct_sub_le_of_deriv_eq_zero hEmono hE hzero' hδ
      ((Real.sqrt lam * w : ℝ) : ℂ)
    rw [hzero, sub_zero, hδn, hun, hq2, add_comm ((δ : ℝ) : ℂ)] at h
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h' : Real.exp (-(w ^ 2 / 2)) * ‖xiSliceProduct t (((Real.sqrt lam * w : ℝ) : ℂ) + δ)‖
        ≤ 8 * lam / δ ^ 2 * (w ^ 2 * (Real.exp (-(w ^ 2 / 2))
          * sliceEnvelope c₀ δ S m (Real.sqrt lam * |w| + 2 * δ))) := by
      have hx := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(w ^ 2 / 2))).le
      calc _ ≤ Real.exp (-(w ^ 2 / 2)) * (8 * (lam * w ^ 2 / δ ^ 2)
            * sliceEnvelope c₀ δ S m (δ + δ + Real.sqrt lam * |w|)) := hx
        _ = _ := by rw [show δ + δ + Real.sqrt lam * |w| = Real.sqrt lam * |w| + 2 * δ by ring];
                    field_simp
    refine le_trans h' (mul_le_mul_of_nonneg_left (hG2 w) (by positivity))
  set V := ∫ w : ℝ, ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
    * xiSliceProduct t (((Real.sqrt lam * w : ℝ) : ℂ) + δ) with hVdef
  have hV : ‖V‖ ≤ 8 * lam / δ ^ 2 * (8 * (c₀ * A * Real.sqrt (8 * Real.pi))) := by
    rw [← hBval, ← integral_const_mul, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hBint.const_mul 8).const_mul _)
      (Eventually.of_forall fun w => ?_)
    exact hVpt w
  -- the zeroth heated coefficient is close to `c₀`
  have hT0rep := xiSliceHeatTransfer_eq_integral_iteratedDeriv hlam.le t 0
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hT0rep
  have hS0eq : xiSliceProduct t 0 = ((c₀ : ℝ) : ℂ) := by
    have h1 : xiSliceCoeff t 0 = xiSliceProduct t 0 := by simp [xiSliceCoeff]
    rw [← h1]
    exact Complex.ext (by simp [hc₀def]) (by simp [xiSliceCoeff_im_eq_zero])
  have hgaussint : Integrable fun w : ℝ => ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ) * ((c₀ : ℝ) : ℂ) := by
    have h := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))
    refine (h.ofReal.mul_const ((c₀ : ℝ) : ℂ)).congr (Eventually.of_forall fun w => ?_)
    simp only; congr 3; ring
  have hgauss : ∫ w : ℝ, ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ) * ((c₀ : ℝ) : ℂ)
      = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((c₀ : ℝ) : ℂ) := by
    rw [integral_mul_const, integral_complex_ofReal]
    have e : (fun w : ℝ => Real.exp (-(w ^ 2 / 2))) = fun w => Real.exp (-(1 / 2) * w ^ 2) := by
      funext w; congr 1; ring
    rw [e, integral_gaussian]
    congr 3; ring
  have hT0pt : ∀ w : ℝ, ‖((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
      * xiSliceProduct t ((Real.sqrt lam * w : ℝ) : ℂ)
        - ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ) * ((c₀ : ℝ) : ℂ)‖ ≤ 8 * lam / δ ^ 2 * (8 * B w) := by
    intro w
    have h := norm_xiSliceProduct_sub_le_of_deriv_eq_zero hEmono hE
      (iteratedDeriv_one_xiSliceProduct_zero t) hδ ((Real.sqrt lam * w : ℝ) : ℂ)
    rw [zero_add, hS0eq, norm_zero, zero_add, hun, hq2] at h
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hmono := hEmono (δ + Real.sqrt lam * |w|) (Real.sqrt lam * |w| + 2 * δ) (by positivity)
      (by linarith)
    have h' : Real.exp (-(w ^ 2 / 2)) * ‖xiSliceProduct t ((Real.sqrt lam * w : ℝ) : ℂ)
        - ((c₀ : ℝ) : ℂ)‖ ≤ 8 * lam / δ ^ 2 * (w ^ 2 * (Real.exp (-(w ^ 2 / 2))
          * sliceEnvelope c₀ δ S m (Real.sqrt lam * |w| + 2 * δ))) := by
      have hx := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(w ^ 2 / 2))).le
      have hk : 0 ≤ 8 * (lam * w ^ 2 / δ ^ 2) := by positivity
      calc _ ≤ Real.exp (-(w ^ 2 / 2)) * (8 * (lam * w ^ 2 / δ ^ 2)
            * sliceEnvelope c₀ δ S m (δ + Real.sqrt lam * |w|)) := hx
        _ ≤ Real.exp (-(w ^ 2 / 2)) * (8 * (lam * w ^ 2 / δ ^ 2)
            * sliceEnvelope c₀ δ S m (Real.sqrt lam * |w| + 2 * δ)) := by gcongr
        _ = _ := by field_simp
    refine le_trans h' (mul_le_mul_of_nonneg_left (hG2 w) (by positivity))
  have hT0 : ‖((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 t 0
      - ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((c₀ : ℝ) : ℂ)‖
        ≤ 8 * lam / δ ^ 2 * (8 * (c₀ * A * Real.sqrt (8 * Real.pi))) := by
    rw [hT0rep, ← hgauss, ← integral_sub
      ((integrable_gauss_mul_iteratedDeriv_xiSliceProduct hlam.le t 0).congr
        (Eventually.of_forall fun w => by simp)) hgaussint]
    rw [← hBval, ← integral_const_mul, ← integral_const_mul]
    exact norm_integral_le_of_norm_le ((hBint.const_mul 8).const_mul _)
      (Eventually.of_forall hT0pt)
  -- assembly
  by_contra hcon
  push Not at hcon
  have hN1 : 1 ≤ N := by
    by_contra h0
    push Not at h0
    interval_cases N
    simp at hN
    linarith
  set a : ℕ → ℂ := fun n => ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 t n
    * (δ : ℂ) ^ n with hadef
  have hsplit := (hasSum_nat_add_iff' N).mpr hHS
  set C := c₀ * A * Real.sqrt (8 * Real.pi) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hgeo : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + N) * C) ((1 / 2) ^ N * C * 2) := by
    refine (hasSum_geometric_two.mul_left ((1 / 2 : ℝ) ^ N * C)).congr_fun fun k => ?_
    rw [pow_add]; ring
  have htail : ‖V - ∑ i ∈ Finset.range N, a i‖ ≤ (1 / 2) ^ N * C * 2 :=
    hsplit.norm_le_of_bounded hgeo fun k =>
      le_trans (hbd (k + N)) (mul_le_mul_of_nonneg_left hI₀ (by positivity))
  have hare : ∀ i, (a i).re = Real.sqrt (2 * Real.pi) * δ ^ i
      * (xiSliceHeatTransfer lam 0 t i).re := by
    intro i
    have e : a i = ((Real.sqrt (2 * Real.pi) * δ ^ i : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 t i := by
      simp only [hadef]; push_cast; ring
    rw [e, Complex.re_ofReal_mul]
  have hhead : (a 0).re ≤ (∑ i ∈ Finset.range N, a i).re := by
    rw [Complex.re_sum]
    refine Finset.single_le_sum (f := fun i => (a i).re) (fun i hi => ?_)
      (Finset.mem_range.mpr hN1)
    rw [hare]
    exact mul_nonneg (by positivity) (hcon i (Finset.mem_range.mp hi))
  have ha0 : a 0 = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 t 0 := by
    simp [hadef]
  have hlow0 : Real.sqrt (2 * Real.pi) * c₀ - 8 * lam / δ ^ 2 * (8 * C) ≤ (a 0).re := by
    have h := Complex.abs_re_le_norm (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
      * xiSliceHeatTransfer lam 0 t 0 - ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((c₀ : ℝ) : ℂ))
    have hre2 : (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((c₀ : ℝ) : ℂ)).re
        = Real.sqrt (2 * Real.pi) * c₀ := by
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
    rw [Complex.sub_re, Complex.re_ofReal_mul, hre2] at h
    rw [ha0, Complex.re_ofReal_mul]
    have h' := le_trans h hT0
    linarith [neg_abs_le (Real.sqrt (2 * Real.pi) * (xiSliceHeatTransfer lam 0 t 0).re
      - Real.sqrt (2 * Real.pi) * c₀)]
  have hreV : (V).re ≥ Real.sqrt (2 * Real.pi) * c₀ - 8 * lam / δ ^ 2 * (8 * C)
      - (1 / 2) ^ N * C * 2 := by
    have h1 : V.re = (∑ i ∈ Finset.range N, a i).re + (V - ∑ i ∈ Finset.range N, a i).re := by
      rw [Complex.sub_re]; ring
    have h2 := neg_abs_le (V - ∑ i ∈ Finset.range N, a i).re
    have h3 := Complex.abs_re_le_norm (V - ∑ i ∈ Finset.range N, a i)
    linarith
  have hVre : V.re ≤ 8 * lam / δ ^ 2 * (8 * C) := le_trans (Complex.re_le_norm V) hV
  -- the contradiction
  set P := Real.sqrt (2 * Real.pi) with hP
  have hP0 : 0 < P := Real.sqrt_pos.mpr (by positivity)
  have hCP : C = 2 * c₀ * A * P := by rw [hCdef, hsqrt8]; ring
  have hkey : P * c₀ ≤ 2 * (8 * lam / δ ^ 2 * (8 * C)) + (1 / 2) ^ N * C * 2 := by linarith
  rw [hCP] at hkey
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h1 : 256 * A * lam / δ ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ hδ2]; linarith
  have h2 : 4 * A * (1 / 2) ^ N < 1 / 2 := by
    rw [one_div_pow]
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    rw [show 4 * A * (1 / 2 ^ N) = 4 * A / 2 ^ N by ring, div_lt_iff₀ h2N]
    linarith
  have hcP : 0 < c₀ * P := mul_pos hc₀ hP0
  have e : 2 * (8 * lam / δ ^ 2 * (8 * (2 * c₀ * A * P))) + (1 / 2) ^ N * (2 * c₀ * A * P) * 2
      = (c₀ * P) * (256 * A * lam / δ ^ 2 + 4 * A * (1 / 2) ^ N) := by
    field_simp; ring
  rw [e] at hkey
  have : (c₀ * P) * (256 * A * lam / δ ^ 2 + 4 * A * (1 / 2) ^ N) < c₀ * P * 1 :=
    mul_lt_mul_of_pos_left (by linarith) hcP
  linarith

/-- **Every off-line zero bounds the WD heat threshold from below.**  With `δ = |Re ρ − ½|` and
`A = 72^m m! e^{1/8} e^{8δ²S}`, `λ_WD ≥ min(δ²/(512A), 1/(16(S + 1)))`. -/
theorem le_wdHeatThreshold_of_offLine_mass {ρ : ℂ} (hρ : xi ρ = 0)
    (hne : ρ.re ≠ 1 / 2) (hΞ : XiC ρ.im ≠ 0) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I)) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S) :
    min (|ρ.re - 1 / 2| ^ 2 / (512 * (72 ^ m * m ! * Real.exp (1 / 8)
        * Real.exp (8 * |ρ.re - 1 / 2| ^ 2 * S)))) (1 / (16 * (S + 1)))
      ≤ wdHeatThreshold := by
  set δ := |ρ.re - 1 / 2| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hS0 : 0 ≤ S := by simpa using hS ∅ (by simp)
  set A := 72 ^ m * m ! * Real.exp (1 / 8) * Real.exp (8 * δ ^ 2 * S) with hA
  have hA0 : 0 < A := by positivity
  set L₀ := min (δ ^ 2 / (512 * A)) (1 / (16 * (S + 1))) with hL₀
  have hL₀pos : 0 < L₀ := lt_min (by positivity) (by positivity)
  refine le_csInf ⟨1 / 8, eighth_mem_wdHeatAdmissible⟩ fun lam hlam => ?_
  by_contra hlt
  push Not at hlt
  have hadm : ∀ t : ℝ, ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer L₀ 0 t n :=
    xiSliceHeatTransfer_nonneg_of_le hlt.le hlam
  have hS' : 16 * L₀ * S ≤ 1 := by
    have h1 : L₀ ≤ 1 / (16 * (S + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hδ' : 512 * A * L₀ ≤ δ ^ 2 := by
    have h1 : L₀ ≤ δ ^ 2 / (512 * A) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (8 * A) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨n, -, hn⟩ := exists_re_xiSliceHeatTransfer_neg_of_offLine_mass hρ hne hΞ hown hS
    hL₀pos hS' hδ' hN
  exact absurd (Complex.nonneg_iff.mp (hadm ρ.im n)).1 (not_le.mpr hn)

end

end RHTower.DeBruijn
