import GaloisForLFunctions.RHTower.CCMEvenGroundXiStripConvergenceRH
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv
import GaloisForLFunctions.RHTower.DeBruijnShiftContraction

/-!
# Cross-rooted functions vanishing at `±i/2` cannot converge to `Ξ` on the strip

Let `F` be even and entire with the order-one envelope, `F(0) ≠ 0`, and all zeros on the cross
`ℝ ∪ iℝ`, i.e. `(z²).im = 0`. Along the imaginary axis put `Λ_F(y) = i F'(iy) / (2y F(iy))`.
Hadamard's factorization and the reflection `q ↦ -q` of the zero copies give

`Λ_F(y) = Σ_q 1 / (2 (a_q² + y²))`   (`hasSum_imagAxisLogDeriv`).

On the cross every `a_q²` is real, so each term is real and decreases in `y` as long as `a_q² + y²`
keeps its sign. If `F(i/2) = 0`, the two copies `±i/2` alone make `Re Λ_F` drop between
`y₁ ≤ y₂ < 1/2` by at least `1/(1/4 − y₂²) − 1/(1/4 − y₁²)` (`re_imagAxisLogDeriv_sub_le`), and
this is unbounded as `y₂ → 1/2`.

**Theorem** (`not_tendstoLocallyUniformlyOn_XiC`). No sequence `c_n F_n` of such functions
converges to `XiC` locally uniformly on the open strip `|Im z| < 1/2`. The function `XiC` has no
zero on the closed segment `i[1/4, 1/2]`, so `Λ_Ξ` is bounded there, and logarithmic derivatives
pass to the limit at points of the open strip.

**The polar ground states** (`not_evenGround_strip_convergence`). Polar-constrained even ground
transforms vanish at `±i/2`. So the two hypotheses of
`riemannHypothesis_of_evenGround_strip_convergence` cannot hold together. The polar factor has to be
divided out: `riemannHypothesis_of_crossRooted_polarQuotient_strip_convergence` is the receiver
for `c_n F_n(z) / (z² + 1/4) → XiC`, whose hypothesis carries no such obstruction.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Real

namespace RHTower.CCMPolarObstruction

open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.CountableDivisor
open RHTower.OrderOneHadamard
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open RHTower.CCMXiStrip RHTower.CCMRealRootedGround

/-- The imaginary-axis logarithmic derivative `Λ_F(y) = i F'(iy) / (2y F(iy))`. -/
def imagAxisLogDeriv (F : ℂ → ℂ) (y : ℝ) : ℂ := I * logDeriv F (I * y) / (2 * y)

/-! ## The Mittag-Leffler series on the imaginary axis -/

/-- The reflected pair of genus-one log-derivative terms at `iy`. -/
theorem reflected_pair_term (a : ℂ) {y : ℝ} (hy : y ≠ 0) (h1 : I * y - a ≠ 0)
    (h2 : I * y + a ≠ 0) :
    I / (4 * y) * (((I * y - a)⁻¹ + a⁻¹) + ((I * y - -a)⁻¹ + (-a)⁻¹)) =
      1 / (2 * (a ^ 2 + (y : ℂ) ^ 2)) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hprod : (I * y - a) * (I * y + a) = -(a ^ 2 + (y : ℂ) ^ 2) := by
    ring_nf
    rw [I_sq]
    ring
  have h3 : a ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by
    intro h
    rw [h, neg_zero] at hprod
    rcases mul_eq_zero.mp hprod with h' | h'
    · exact h1 h'
    · exact h2 h'
  rw [sub_neg_eq_add, inv_neg]
  have hsum : (I * y - a)⁻¹ + a⁻¹ + ((I * y + a)⁻¹ + -a⁻¹) =
      (I * y - a)⁻¹ + (I * y + a)⁻¹ := by ring
  rw [hsum, inv_add_inv h1 h2]
  have hnum : I * y - a + (I * y + a) = 2 * I * y := by ring
  rw [hnum, hprod]
  field_simp
  ring_nf
  rw [I_sq]
  ring

variable {F : ℂ → ℂ}

/-- Every zero of an entire function with finite orders carries a multiplicity copy. -/
theorem exists_zeroCopy_of_zero (hF : AnalyticOnNhd ℂ F univ)
    (hford : ∀ z, analyticOrderAt F z ≠ ⊤) {w : ℂ} (hw : F w = 0) :
    ∃ q : ZeroCopy F, zeroCopyPoint F q = w := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt F w = (n : ℕ∞) :=
    ⟨(analyticOrderAt F w).toNat, (ENat.coe_toNat (hford w)).symm⟩
  have hdiv : (MeromorphicOn.divisor F univ) w = (n : ℤ) := by
    rw [divisor_univ_eq_analyticOrder hF, hn]
    rfl
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h0 : analyticOrderAt F w = 0 := by rw [hn]; rfl
    exact ((hF w (mem_univ w)).analyticOrderAt_eq_zero.mp h0) hw
  have hsupp : w ∈ (MeromorphicOn.divisor F univ).support := by
    rw [Function.mem_support, hdiv]
    exact_mod_cast hn0
  refine ⟨⟨⟨w, hsupp⟩, ⟨0, ?_⟩⟩, rfl⟩
  show 0 < ((MeromorphicOn.divisor F univ) w).toNat
  rw [hdiv]
  simp only [Int.toNat_natCast]
  omega

/-- **Mittag-Leffler series on the imaginary axis.** For an even order-one entire function with
`F(0) ≠ 0` and `F(iy) ≠ 0`, `Λ_F(y) = Σ_q 1/(2(a_q² + y²))` over the zero copies. -/
theorem hasSum_imagAxisLogDeriv {C : ℝ} (hC : 0 ≤ C) (hF : AnalyticOnNhd ℂ F univ)
    (hF0 : F 0 ≠ 0) (heven : ∀ z, F (-z) = F z)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {y : ℝ} (hy : y ≠ 0) (hFy : F (I * y) ≠ 0) :
    HasSum (fun q : ZeroCopy F => 1 / (2 * (zeroCopyPoint F q ^ 2 + (y : ℂ) ^ 2)))
      (imagAxisLogDeriv F y) := by
  have hford := RHTower.DeBruijn.analyticOrderAt_ne_top_of_ne_zero hF hF0
  have hfac := eq_const_mul_hadamardProduct_of_even hC hF hF0 hford heven hbound
  set a : ZeroCopy F → ℂ := zeroCopyPoint F with ha
  have hane : ∀ q, a q ≠ 0 := zeroCopyPoint_ne_zero hF hF0
  have hsum : Summable (fun q : ZeroCopy F => 1 / ‖a q‖ ^ (2 : ℕ)) :=
    summable_inv_sq_zeroCopyPoint hC hF hF0 hbound
  have hazero : ∀ q, F (a q) = 0 := by
    intro q
    by_contra hne
    have hord : analyticOrderAt F (a q) = 0 :=
      (hF (a q) (mem_univ _)).analyticOrderAt_eq_zero.mpr hne
    have hdiv : (MeromorphicOn.divisor F univ) (a q) ≠ 0 := q.1.2
    apply hdiv
    rw [divisor_univ_eq_analyticOrder hF, hord]
    simp
  have hne1 : ∀ q, I * y ≠ a q := fun q h => hFy (h ▸ hazero q)
  have hne2 : ∀ q, I * y + a q ≠ 0 := by
    intro q h
    have hneg : I * y = -(a q) := eq_neg_of_add_eq_zero_left h
    apply hFy
    rw [hneg, heven]
    exact hazero q
  have hlogF : logDeriv F (I * y) = logDeriv (hadamardProduct F) (I * y) := by
    calc logDeriv F (I * y) = logDeriv (fun z => F 0 * hadamardProduct F z) (I * y) := by
          rw [show (fun z => F 0 * hadamardProduct F z) = F from (funext hfac).symm]
      _ = logDeriv (hadamardProduct F) (I * y) := logDeriv_const_mul _ _ hF0
  have hP : logDeriv (hadamardProduct F) (I * y) = ∑' q, ((I * y - a q)⁻¹ + (a q)⁻¹) :=
    logDeriv_canonicalProductE1Indexed hane hsum hne1
  have hT : Summable (fun q : ZeroCopy F => (I * y - a q)⁻¹ + (a q)⁻¹) := by
    refine (summable_canonicalProductE1LogDerivTerm hane hsum hne1).neg.congr (fun q => ?_)
    have hneg : I * y - a q = -(a q - I * y) := by ring
    rw [hneg, inv_neg]
    ring
  set σ := zeroCopyReflect hF heven with hσ
  have hTσ : HasSum (fun q => (I * y - a (σ q))⁻¹ + (a (σ q))⁻¹)
      (∑' q, ((I * y - a q)⁻¹ + (a q)⁻¹)) :=
    (σ.hasSum_iff (f := fun q => (I * y - a q)⁻¹ + (a q)⁻¹)).mpr hT.hasSum
  have hmul := (hT.hasSum.add hTσ).mul_left (I / (4 * y))
  have hfun : (fun q => I / (4 * y) * (((I * y - a q)⁻¹ + (a q)⁻¹) +
      ((I * y - a (σ q))⁻¹ + (a (σ q))⁻¹))) =
      fun q => 1 / (2 * (a q ^ 2 + (y : ℂ) ^ 2)) := by
    funext q
    have hrefl : a (σ q) = -a q := zeroCopyPoint_reflect hF heven q
    rw [hrefl]
    exact reflected_pair_term (a q) hy (sub_ne_zero.mpr (hne1 q)) (hne2 q)
  have hval : I / (4 * y) * ((∑' q, ((I * y - a q)⁻¹ + (a q)⁻¹)) +
      ∑' q, ((I * y - a q)⁻¹ + (a q)⁻¹)) = imagAxisLogDeriv F y := by
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
    unfold imagAxisLogDeriv
    rw [hlogF, hP]
    field_simp
    ring
  rw [hfun, hval] at hmul
  exact hmul

/-! ## The polar drop -/

theorem sq_eq_ofReal_re_of_im_eq_zero {a : ℂ} (ha : (a ^ 2).im = 0) :
    a ^ 2 = (((a ^ 2).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [ha])

theorem re_one_div_two_mul_sq_add {a : ℂ} (ha : (a ^ 2).im = 0) (y : ℝ) :
    (1 / (2 * (a ^ 2 + (y : ℂ) ^ 2))).re = 1 / (2 * ((a ^ 2).re + y ^ 2)) := by
  rw [sq_eq_ofReal_re_of_im_eq_zero ha]
  have h : (1 : ℂ) / (2 * ((((a ^ 2).re : ℝ) : ℂ) + (y : ℂ) ^ 2)) =
      (((1 / (2 * ((a ^ 2).re + y ^ 2)) : ℝ)) : ℂ) := by push_cast; ring
  rw [h, Complex.ofReal_re]
  simp

/-- A real term `1/(2(r + y²))` decreases in `y ≥ 0` while `r + y²` keeps its sign. -/
theorem one_div_two_mul_add_sq_sub_le {r y₁ y₂ : ℝ} (hy₁ : 0 ≤ y₁) (h12 : y₁ ≤ y₂)
    (hsign : 0 < (r + y₁ ^ 2) * (r + y₂ ^ 2)) :
    1 / (2 * (r + y₂ ^ 2)) - 1 / (2 * (r + y₁ ^ 2)) ≤ 0 := by
  have hA : r + y₂ ^ 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsign
    exact lt_irrefl 0 hsign
  have hB : r + y₁ ^ 2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsign
    exact lt_irrefl 0 hsign
  have key : 1 / (2 * (r + y₂ ^ 2)) - 1 / (2 * (r + y₁ ^ 2)) =
      (y₁ ^ 2 - y₂ ^ 2) / (2 * ((r + y₁ ^ 2) * (r + y₂ ^ 2))) := by
    field_simp
    ring
  rw [key]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith
  · positivity

/-- **The polar drop.** If `F` is cross-rooted, vanishes at `i/2`, and has no zero on
`i[y₁, y₂]` with `0 < y₁ ≤ y₂ < 1/2`, then `Re Λ_F` drops by at least the polar amount. -/
theorem re_imagAxisLogDeriv_sub_le {C : ℝ} (hC : 0 ≤ C) (hF : AnalyticOnNhd ℂ F univ)
    (hF0 : F 0 ≠ 0) (heven : ∀ z, F (-z) = F z)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hcross : ∀ z, F z = 0 → (z ^ 2).im = 0) (hpol : F (I / 2) = 0)
    {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (h12 : y₁ ≤ y₂) (hy₂ : y₂ < 1 / 2)
    (hnz : ∀ y ∈ Icc y₁ y₂, F (I * y) ≠ 0) :
    (imagAxisLogDeriv F y₂).re - (imagAxisLogDeriv F y₁).re ≤
      1 / (1 / 4 - y₁ ^ 2) - 1 / (1 / 4 - y₂ ^ 2) := by
  have hy₂pos : 0 < y₂ := lt_of_lt_of_le hy₁ h12
  have hford := RHTower.DeBruijn.analyticOrderAt_ne_top_of_ne_zero hF hF0
  have h1 := hasSum_imagAxisLogDeriv hC hF hF0 heven hbound hy₁.ne' (hnz y₁ ⟨le_rfl, h12⟩)
  have h2 := hasSum_imagAxisLogDeriv hC hF hF0 heven hbound hy₂pos.ne' (hnz y₂ ⟨h12, le_rfl⟩)
  set a : ZeroCopy F → ℂ := zeroCopyPoint F with ha
  have hre1 := Complex.reCLM.hasSum h1
  have hre2 := Complex.reCLM.hasSum h2
  set d : ZeroCopy F → ℝ := fun q =>
    (1 / (2 * (a q ^ 2 + (y₂ : ℂ) ^ 2))).re - (1 / (2 * (a q ^ 2 + (y₁ : ℂ) ^ 2))).re with hd
  have hdsum : HasSum d ((imagAxisLogDeriv F y₂).re - (imagAxisLogDeriv F y₁).re) := by
    have := hre2.sub hre1
    simpa only [Complex.reCLM_apply] using this
  have hazero : ∀ q, F (a q) = 0 := by
    intro q
    by_contra hne
    have hord : analyticOrderAt F (a q) = 0 :=
      (hF (a q) (mem_univ _)).analyticOrderAt_eq_zero.mpr hne
    have hdiv : (MeromorphicOn.divisor F univ) (a q) ≠ 0 := q.1.2
    apply hdiv
    rw [divisor_univ_eq_analyticOrder hF, hord]
    simp
  have hane : ∀ q, a q ≠ 0 := zeroCopyPoint_ne_zero hF hF0
  -- every term is nonpositive
  have hdnp : ∀ q, d q ≤ 0 := by
    intro q
    have hsq := hcross _ (hazero q)
    simp only [hd]
    rw [re_one_div_two_mul_sq_add hsq, re_one_div_two_mul_sq_add hsq]
    apply one_div_two_mul_add_sq_sub_le hy₁.le h12
    have hreim : (a q).re * (a q).im = 0 := by
      have h : ((a q) ^ 2).im = 2 * ((a q).re * (a q).im) := by
        rw [sq, Complex.mul_im]; ring
      rw [hsq] at h
      linarith
    have hr : ((a q) ^ 2).re = (a q).re ^ 2 - (a q).im ^ 2 := by
      rw [sq, Complex.mul_re]; ring
    rw [hr]
    rcases mul_eq_zero.mp hreim with hre | him
    · -- imaginary zero `a = i t`
      set t := (a q).im with ht
      rw [hre]
      by_contra hneg
      rw [not_lt] at hneg
      have hlo : y₁ ^ 2 ≤ t ^ 2 := by
        by_contra hlt
        rw [not_le] at hlt
        have : 0 < (0 ^ 2 - t ^ 2 + y₁ ^ 2) * (0 ^ 2 - t ^ 2 + y₂ ^ 2) := by
          apply mul_pos <;> nlinarith
        linarith
      have hhi : t ^ 2 ≤ y₂ ^ 2 := by
        by_contra hlt
        rw [not_le] at hlt
        have : 0 < (0 ^ 2 - t ^ 2 + y₁ ^ 2) * (0 ^ 2 - t ^ 2 + y₂ ^ 2) := by
          apply mul_pos_of_neg_of_neg <;> nlinarith
        linarith
      have habs1 : y₁ ≤ |t| := by
        have := sq_le_sq.mp hlo
        rwa [abs_of_pos hy₁] at this
      have habs2 : |t| ≤ y₂ := by
        have := sq_le_sq.mp hhi
        rwa [abs_of_pos hy₂pos] at this
      apply hnz |t| ⟨habs1, habs2⟩
      have haq : a q = I * (t : ℂ) := by
        apply Complex.ext <;> simp [hre, ht]
      rcases le_or_gt 0 t with ht0 | ht0
      · rw [abs_of_nonneg ht0, ← haq]
        exact hazero q
      · rw [abs_of_neg ht0]
        have : I * ((-t : ℝ) : ℂ) = -(a q) := by rw [haq]; push_cast; ring
        rw [this, heven]
        exact hazero q
    · -- real zero
      rw [him]
      have hre0 : (a q).re ≠ 0 := by
        intro h0
        apply hane q
        apply Complex.ext <;> simp [h0, him]
      have hpos : 0 < (a q).re ^ 2 := by positivity
      apply mul_pos <;> nlinarith [sq_nonneg y₁, sq_nonneg y₂]
  -- the two polar copies
  obtain ⟨qp, hqp⟩ := exists_zeroCopy_of_zero hF hford hpol
  have hpol' : F (-(I / 2)) = 0 := by rw [heven]; exact hpol
  obtain ⟨qm, hqm⟩ := exists_zeroCopy_of_zero hF hford hpol'
  have hne : qp ≠ qm := by
    intro h
    rw [h] at hqp
    rw [hqp] at hqm
    have him := congrArg Complex.im hqm
    simp at him
    norm_num at him
  have hle : ∑' q, d q ≤ d qp + d qm := by
    have hsl := (hdsum.summable.neg).sum_le_tsum {qp, qm}
      (fun q _ => neg_nonneg.mpr (hdnp q))
    rw [Finset.sum_pair hne, tsum_neg] at hsl
    linarith
  have hpolsq : ((I / 2) ^ 2 : ℂ) = (((-1 / 4 : ℝ)) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hval : ∀ q, a q = I / 2 ∨ a q = -(I / 2) →
      d q = 1 / (2 * (-1 / 4 + y₂ ^ 2)) - 1 / (2 * (-1 / 4 + y₁ ^ 2)) := by
    intro q hq
    have hsq : a q ^ 2 = (((-1 / 4 : ℝ)) : ℂ) := by
      rcases hq with h | h
      · rw [h, hpolsq]
      · rw [h, neg_sq, hpolsq]
    have him : (a q ^ 2).im = 0 := by rw [hsq, Complex.ofReal_im]
    have hre : (a q ^ 2).re = -1 / 4 := by rw [hsq, Complex.ofReal_re]
    simp only [hd]
    rw [re_one_div_two_mul_sq_add him, re_one_div_two_mul_sq_add him, hre]
  rw [← hdsum.tsum_eq]
  calc ∑' q, d q ≤ d qp + d qm := hle
    _ = 2 * (1 / (2 * (-1 / 4 + y₂ ^ 2)) - 1 / (2 * (-1 / 4 + y₁ ^ 2))) := by
        rw [hval qp (Or.inl hqp), hval qm (Or.inr hqm)]
        ring
    _ = 1 / (1 / 4 - y₁ ^ 2) - 1 / (1 / 4 - y₂ ^ 2) := by
        have e1 : (-1 / 4 : ℝ) + y₁ ^ 2 = -(1 / 4 - y₁ ^ 2) := by ring
        have e2 : (-1 / 4 : ℝ) + y₂ ^ 2 = -(1 / 4 - y₂ ^ 2) := by ring
        have hA : (1 / 4 : ℝ) - y₂ ^ 2 ≠ 0 := by nlinarith
        have hB : (1 / 4 : ℝ) - y₁ ^ 2 ≠ 0 := by nlinarith
        rw [e1, e2, mul_neg, mul_neg, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div]
        field_simp
        ring

/-! ## No convergence to `Ξ` on the strip -/

theorem XiC_imag_ne_zero (y : ℝ) : XiC (I * y) ≠ 0 := by
  intro h
  have hsq : ((I * (y : ℂ)) ^ 2).im = 0 := by
    rw [mul_pow, I_sq]
    simp [← Complex.ofReal_pow]
  have him := XiC_im_eq_zero_of_sq_im_eq_zero h hsq
  have hy : y = 0 := by simpa using him
  rw [hy, Complex.ofReal_zero, mul_zero] at h
  exact XiC_zero_ne h

theorem imag_mem_centeredStrip {y : ℝ} (hy : |y| < 1 / 2) : I * (y : ℂ) ∈ centeredStrip := by
  have him : (I * (y : ℂ)).im = y := by simp
  show |(I * (y : ℂ)).im| < 1 / 2
  rw [him]
  exact hy

/-- **No cross-rooted family vanishing at `±i/2` converges to `Ξ` on the strip.** -/
theorem not_tendstoLocallyUniformlyOn_XiC (F : ℕ → ℂ → ℂ) (c : ℕ → ℂ)
    (hF : ∀ n, AnalyticOnNhd ℂ (F n) univ) (heven : ∀ n z, F n (-z) = F n z)
    (hbound : ∀ n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, ‖F n z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hcross : ∀ n z, F n z = 0 → (z ^ 2).im = 0) (hpol : ∀ n, F n (I / 2) = 0) :
    ¬ TendstoLocallyUniformlyOn (fun n z => c n * F n z) XiC atTop centeredStrip := by
  intro hconv
  set G : ℕ → ℂ → ℂ := fun n z => c n * F n z with hG
  have hlin : Continuous (fun y : ℝ => I * (y : ℂ)) := by fun_prop
  -- `Λ_Ξ` is bounded on `[1/4, 1/2]`
  have hcont : ContinuousOn (fun y : ℝ => logDeriv XiC (I * y)) (Icc (1 / 4) (1 / 2)) := by
    intro y _
    apply ContinuousAt.continuousWithinAt
    have hd : ContinuousAt (deriv XiC) (I * y) :=
      (XiC_analytic.deriv (I * y) (mem_univ _)).continuousAt
    have hv : ContinuousAt XiC (I * y) := (XiC_analytic _ (mem_univ _)).continuousAt
    have hd' : ContinuousAt (fun y : ℝ => deriv XiC (I * y)) y :=
      ContinuousAt.comp (g := deriv XiC) (f := fun y : ℝ => I * (y : ℂ)) hd hlin.continuousAt
    have hv' : ContinuousAt (fun y : ℝ => XiC (I * y)) y :=
      ContinuousAt.comp (g := XiC) (f := fun y : ℝ => I * (y : ℂ)) hv hlin.continuousAt
    have h : ContinuousAt (fun y : ℝ => deriv XiC (I * y) / XiC (I * y)) y :=
      hd'.div hv' (XiC_imag_ne_zero y)
    simpa only [logDeriv_apply] using h
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hbdd : ∀ y ∈ Icc (1 / 4 : ℝ) (1 / 2), |(imagAxisLogDeriv XiC y).re| ≤ 2 * M' := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hnorm : ‖imagAxisLogDeriv XiC y‖ = ‖logDeriv XiC (I * y)‖ / (2 * y) := by
      unfold imagAxisLogDeriv
      rw [norm_div, norm_mul, Complex.norm_I, one_mul]
      congr 1
      rw [show (2 * (y : ℂ)) = ((2 * y : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
    calc |(imagAxisLogDeriv XiC y).re| ≤ ‖imagAxisLogDeriv XiC y‖ := Complex.abs_re_le_norm _
      _ = ‖logDeriv XiC (I * y)‖ / (2 * y) := hnorm
      _ ≤ M' / (2 * (1 / 4)) := by
          apply div_le_div₀ hM'0 ((hM y hy).trans (le_max_left _ _)) (by norm_num)
          linarith [hy.1]
      _ = 2 * M' := by ring
  -- the second aperture point
  set K : ℝ := 16 / 3 + 4 * M' + 1 with hK
  have hK0 : 16 / 3 < K := by linarith
  have hKpos : 0 < K := by linarith
  have hinvK : 1 / K < 3 / 16 := by
    rw [div_lt_div_iff₀ hKpos (by norm_num)]
    linarith
  set y₂ : ℝ := Real.sqrt (1 / 4 - 1 / K) with hy₂def
  have hrad : 0 ≤ 1 / 4 - 1 / K := by linarith
  have hy₂sq : y₂ ^ 2 = 1 / 4 - 1 / K := Real.sq_sqrt hrad
  have hy₂nn : 0 ≤ y₂ := Real.sqrt_nonneg _
  have hy₂lo : 1 / 4 < y₂ := by nlinarith
  have hy₂hi : y₂ < 1 / 2 := by
    have hK' : 0 < 1 / K := by positivity
    nlinarith
  have hy₁₂ : (1 / 4 : ℝ) ≤ y₂ := hy₂lo.le
  have hy₂val : 1 / (1 / 4 - y₂ ^ 2) = K := by
    rw [hy₂sq, show (1 / 4 : ℝ) - (1 / 4 - 1 / K) = 1 / K by ring, one_div_one_div]
  have hy₁val : 1 / (1 / 4 - (1 / 4 : ℝ) ^ 2) = 16 / 3 := by norm_num
  have hy₁abs : |(1 / 4 : ℝ)| < 1 / 2 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hy₂abs : |y₂| < 1 / 2 := by rw [abs_of_nonneg hy₂nn]; exact hy₂hi
  -- eventually `c_n F_n(0) ≠ 0`
  have h0 : (0 : ℂ) ∈ centeredStrip := by simp [centeredStrip]
  have hG0 : ∀ᶠ n in atTop, G n 0 ≠ 0 := (hconv.tendsto_at h0).eventually_ne XiC_zero_ne
  -- eventually no zero on the segment `i[y₁, y₂]`
  have hseg : ∀ᶠ n in atTop, ∀ y ∈ Icc (1 / 4 : ℝ) y₂, G n (I * y) ≠ 0 := by
    set S : Set ℂ := (fun y : ℝ => I * (y : ℂ)) '' Icc (1 / 4 : ℝ) y₂ with hS
    have hScpt : IsCompact S := isCompact_Icc.image hlin
    have hSsub : S ⊆ centeredStrip := by
      rintro _ ⟨y, hy, rfl⟩
      apply imag_mem_centeredStrip
      rw [abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    have hunif : TendstoUniformlyOn G XiC atTop S :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_centeredStrip).mp hconv S hSsub
        hScpt
    have hSne : S.Nonempty := ⟨I * (1 / 4 : ℝ), 1 / 4, ⟨le_rfl, hy₁₂⟩, rfl⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hScpt.exists_isMinOn hSne
      (XiC_analytic.continuousOn.norm.mono (subset_univ _))
    have hm : 0 < ‖XiC z₀‖ := by
      obtain ⟨y, _, rfl⟩ := hz₀
      exact norm_pos_iff.mpr (XiC_imag_ne_zero y)
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hunif) _ hm] with n hn y hy hzero
    have hdist := hn (I * y) ⟨y, hy, rfl⟩
    rw [hzero, dist_zero_right] at hdist
    have hmin' : ‖XiC z₀‖ ≤ ‖XiC (I * y)‖ := hmin ⟨y, hy, rfl⟩
    exact absurd hmin' (not_le.mpr hdist)
  -- logarithmic derivatives converge at points of the strip
  have hdiffG : ∀ᶠ n in atTop, DifferentiableOn ℂ (G n) centeredStrip :=
    Eventually.of_forall fun n =>
      fun z _ => (((hF n) z (mem_univ z)).differentiableAt.const_mul (c n)).differentiableWithinAt
  have hderiv := hconv.deriv hdiffG isOpen_centeredStrip
  have hΛ : ∀ y : ℝ, |y| < 1 / 2 → Tendsto (fun n => (imagAxisLogDeriv (F n) y).re) atTop
      (𝓝 (imagAxisLogDeriv XiC y).re) := by
    intro y hy
    have h1 : Tendsto (fun n => deriv (G n) (I * y)) atTop (𝓝 (deriv XiC (I * y))) :=
      hderiv.tendsto_at (imag_mem_centeredStrip hy)
    have h2 : Tendsto (fun n => G n (I * y)) atTop (𝓝 (XiC (I * y))) :=
      hconv.tendsto_at (imag_mem_centeredStrip hy)
    have h3 : Tendsto (fun n => deriv (G n) (I * y) / G n (I * y)) atTop
        (𝓝 (deriv XiC (I * y) / XiC (I * y))) := h1.div h2 (XiC_imag_ne_zero y)
    have hlog : Tendsto (fun n => I * logDeriv (G n) (I * y) / (2 * y)) atTop
        (𝓝 (imagAxisLogDeriv XiC y)) := by
      have := (h3.const_mul I).div_const (2 * (y : ℂ))
      simpa only [imagAxisLogDeriv, logDeriv_apply] using this
    have hev : ∀ᶠ n in atTop, I * logDeriv (G n) (I * y) / (2 * y) = imagAxisLogDeriv (F n) y := by
      filter_upwards [hG0] with n hn
      have hcn : c n ≠ 0 := left_ne_zero_of_mul hn
      unfold imagAxisLogDeriv
      rw [hG, logDeriv_const_mul _ _ hcn]
    exact (Complex.continuous_re.tendsto _).comp (hlog.congr' hev)
  -- the polar drop at every large index
  have hineq : ∀ᶠ n in atTop,
      (imagAxisLogDeriv (F n) y₂).re - (imagAxisLogDeriv (F n) (1 / 4)).re ≤
        1 / (1 / 4 - (1 / 4 : ℝ) ^ 2) - 1 / (1 / 4 - y₂ ^ 2) := by
    filter_upwards [hG0, hseg] with n hn hs
    obtain ⟨C, hC, hb⟩ := hbound n
    have hF0 : F n 0 ≠ 0 := right_ne_zero_of_mul hn
    refine re_imagAxisLogDeriv_sub_le hC (hF n) hF0 (heven n) hb (hcross n) (hpol n)
      (by norm_num) hy₁₂ hy₂hi (fun y hy h => hs y hy ?_)
    simp only [hG, h, mul_zero]
  have hlim := le_of_tendsto ((hΛ y₂ hy₂abs).sub (hΛ (1 / 4) hy₁abs)) hineq
  rw [hy₁val, hy₂val] at hlim
  have hb1 := hbdd (1 / 4) ⟨le_rfl, by norm_num⟩
  have hb2 := hbdd y₂ ⟨hy₂lo.le, hy₂hi.le⟩
  rw [abs_le] at hb1 hb2
  linarith [hb1.1, hb1.2, hb2.1, hb2.2]

/-! ## The polar ground states of the restricted Weil form -/

theorem polarPoint_re (s : ℝ) : (polarPoint s).re = 0 := by
  rw [polarPoint, show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
    Complex.div_ofReal_re]
  simp

/-- Exponential-type bound for the transform of an integrable function supported in `[-A, A]`. -/
theorem norm_unitaryLaplace_le {A : ℝ} {f : ℝ → ℂ} (hf : Integrable f) (hs : SupportedIn A f)
    (w : ℂ) : ‖unitaryLaplace f w‖ ≤ Real.exp (2 * π * |w.im| * A) * ∫ x, ‖f x‖ := by
  rw [unitaryLaplace, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hf.norm.const_mul _) (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Icc (-A) A
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_cexp_le_of_mem_Icc w hx) (norm_nonneg _)
  · simp [hs x hx]

/-- Exponential type gives the order-one envelope. -/
theorem orderOneEnvelope_of_expType {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) {G : ℂ → ℂ}
    (hG : ∀ z, ‖G z‖ ≤ B * Real.exp (A * ‖z‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖G z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ Real.log (1 + B) := Real.log_nonneg (by linarith)
  refine ⟨(Real.log (1 + B) + A) / Real.log 2, by positivity, fun z => ?_⟩
  have hz := norm_nonneg z
  have hB1 : B ≤ Real.exp (Real.log (1 + B)) := by
    rw [Real.exp_log (by linarith)]
    linarith
  have hl : Real.log 2 ≤ Real.log (2 + ‖z‖) := Real.log_le_log (by norm_num) (by linarith)
  calc ‖G z‖ ≤ B * Real.exp (A * ‖z‖) := hG z
    _ ≤ Real.exp (Real.log (1 + B)) * Real.exp (A * ‖z‖) := by gcongr
    _ = Real.exp (Real.log (1 + B) + A * ‖z‖) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((Real.log (1 + B) + A) / Real.log 2 * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
        apply Real.exp_le_exp.mpr
        have hstep1 : Real.log (1 + B) + A * ‖z‖ ≤ (Real.log (1 + B) + A) * (1 + ‖z‖) := by
          nlinarith
        have hstep2 : (Real.log (1 + B) + A) * (1 + ‖z‖) ≤
            (Real.log (1 + B) + A) / Real.log 2 * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
          have hratio : 1 ≤ Real.log (2 + ‖z‖) / Real.log 2 := by
            rw [le_div_iff₀ hlog2]
            linarith
          have hnn : 0 ≤ (Real.log (1 + B) + A) * (1 + ‖z‖) := by positivity
          calc (Real.log (1 + B) + A) * (1 + ‖z‖)
              ≤ (Real.log (1 + B) + A) * (1 + ‖z‖) * (Real.log (2 + ‖z‖) / Real.log 2) :=
                le_mul_of_one_le_right hnn hratio
            _ = (Real.log (1 + B) + A) / Real.log 2 * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
                field_simp
        linarith

/-- The centred transform `z ↦ f̂_u(z/(2π))` of a form-domain vector has the order-one envelope. -/
theorem orderOneEnvelope_ccmTransform (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖unitaryLaplace (timeRep a u) (z / (2 * π))‖ ≤
      Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  refine orderOneEnvelope_of_expType (B := ∫ x, ‖timeRep a u x‖) (A := a.1)
    (integral_nonneg fun x => norm_nonneg _) a.2.le (fun z => ?_)
  have h := norm_unitaryLaplace_le (integrable_timeRep a u) (supportedIn_timeRep a u) (z / (2 * π))
  have him : |(z / (2 * π)).im| = |z.im| / (2 * π) := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  rw [him] at h
  have hexp : Real.exp (2 * π * (|z.im| / (2 * π)) * a.1) ≤ Real.exp (a.1 * ‖z‖) := by
    apply Real.exp_le_exp.mpr
    have hπ : (2 * π) * (|z.im| / (2 * π)) = |z.im| := by field_simp
    rw [hπ, mul_comm]
    exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) a.2.le
  calc ‖unitaryLaplace (timeRep a u) (z / (2 * π))‖
      ≤ Real.exp (2 * π * (|z.im| / (2 * π)) * a.1) * ∫ x, ‖timeRep a u x‖ := h
    _ ≤ Real.exp (a.1 * ‖z‖) * ∫ x, ‖timeRep a u x‖ :=
        mul_le_mul_of_nonneg_right hexp (integral_nonneg fun x => norm_nonneg _)
    _ = (∫ x, ‖timeRep a u x‖) * Real.exp (a.1 * ‖z‖) := mul_comm _ _

/-- **The polar even ground transforms never converge to `Ξ` on the strip.** Even polar ground
states with cross-rooted transforms vanish at `±i/2`, so no normalization of them converges to
`XiC` locally uniformly on `|Im z| < 1/2`; the hypotheses of
`riemannHypothesis_of_evenGround_strip_convergence` are jointly unsatisfiable. -/
theorem not_evenGround_strip_convergence
    (a : ℕ → SuzukiPositiveAperture) (u : ∀ n, CCMArchimedeanFormDomain (a n)) (c : ℕ → ℂ)
    (hground : ∀ n, RHTower.CCMEvenSector.IsEvenGround (a n) (u n) ∧
      ∀ w : ℂ, unitaryLaplace (timeRep (a n) (u n)) w = 0 →
        w ≠ polarPoint (1 / 2) → w ≠ polarPoint (-1 / 2) → w.re = 0 ∨ w.im = 0) :
    ¬ TendstoLocallyUniformlyOn
      (fun n z => c n * unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π))) XiC atTop
      centeredStrip := by
  have hπ : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  have hπpos : (0 : ℝ) < 2 * π := by positivity
  refine not_tendstoLocallyUniformlyOn_XiC
    (fun n z => unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π))) c ?_ ?_
    (fun n => orderOneEnvelope_ccmTransform (a n) (u n)) ?_ ?_
  · intro n z _
    have hd := differentiable_unitaryLaplace (a n).2.le (integrable_timeRep (a n) (u n))
      (supportedIn_timeRep (a n) (u n))
    exact (hd.comp (differentiable_id.div_const _)).analyticAt z
  · intro n z
    show unitaryLaplace (timeRep (a n) (u n)) (-z / (2 * π)) =
      unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π))
    rw [neg_div]
    exact RHTower.CCMEvenSector.IsEven.transform_neg (a n) (hground n).1.2.1 _
  · intro n z hz
    have hz' : unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π)) = 0 := hz
    have hcr : (z / (2 * π)).re = 0 ∨ (z / (2 * π)).im = 0 := by
      by_cases h1 : z / (2 * π) = polarPoint (1 / 2)
      · left
        rw [h1]
        exact polarPoint_re _
      by_cases h2 : z / (2 * π) = polarPoint (-1 / 2)
      · left
        rw [h2]
        exact polarPoint_re _
      exact (hground n).2 _ hz' h1 h2
    have hre : (z / (2 * π)).re = z.re / (2 * π) := by rw [hπ, Complex.div_ofReal_re]
    have him : (z / (2 * π)).im = z.im / (2 * π) := by rw [hπ, Complex.div_ofReal_im]
    rw [sq, Complex.mul_im]
    rcases hcr with h | h
    · rw [hre, div_eq_zero_iff] at h
      rcases h with h | h
      · rw [h]; ring
      · exact absurd h hπpos.ne'
    · rw [him, div_eq_zero_iff] at h
      rcases h with h | h
      · rw [h]; ring
      · exact absurd h hπpos.ne'
  · intro n
    show unitaryLaplace (timeRep (a n) (u n)) (I / 2 / (2 * π)) = 0
    have hpt : I / 2 / (2 * π) = polarPoint (1 / 2) := by
      rw [polarPoint]
      push_cast
      ring
    rw [hpt, ← inner_polar_eq]
    exact (hground n).1.1.1

/-! ## The corrected receiver: divide out the polar factor -/

theorem sq_add_quarter_ne_zero {z : ℂ} (hz : z ∈ centeredStrip) : z ^ 2 + 1 / 4 ≠ 0 := by
  intro h
  have hre : (z ^ 2 + 1 / 4).re = 0 := by rw [h]; simp
  have hzs : |z.im| < 1 / 2 := hz
  rw [abs_lt] at hzs
  have hre' : z.re ^ 2 - z.im ^ 2 + 1 / 4 = 0 := by
    have : (z ^ 2 + 1 / 4).re = z.re ^ 2 - z.im ^ 2 + 1 / 4 := by
      rw [Complex.add_re, sq, Complex.mul_re]
      norm_num
      ring
    linarith
  nlinarith [sq_nonneg z.re]

/-- **Strip receiver for functions with cross zeros.** If functions holomorphic on the strip, with
all zeros there on `ℝ ∪ iℝ`, converge to `XiC` locally uniformly on the strip, then RH holds. -/
theorem riemannHypothesis_of_strip_convergence_of_cross_zeros (Fn : ℕ → ℂ → ℂ)
    (hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (Fn n) centeredStrip)
    (hzero : ∀ᶠ n in atTop, ∀ w ∈ centeredStrip, Fn n w = 0 → (w ^ 2).im = 0)
    (hconv : TendstoLocallyUniformlyOn Fn XiC atTop centeredStrip) : RiemannHypothesis := by
  set S : Set ℂ := {z | (z ^ 2).im = 0} with hSdef
  have hS : IsClosed S := isClosed_eq (Complex.continuous_im.comp (continuous_pow 2))
    continuous_const
  have h0 : (0 : ℂ) ∈ centeredStrip := by simp [centeredStrip]
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero'
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero']
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  have hρ1 : ρ.re < 1 := by
    by_contra hge
    exact xi_ne_zero_of_one_le_re (not_lt.mp hge) hzero'
  have hρh : 1 / 2 < ρ.re := mem_rightHalf.mp hρ
  have hzU : z ∈ centeredStrip := by
    simp only [centeredStrip, mem_setOf_eq, hzIm]
    rw [abs_lt]
    constructor <;> linarith
  have hzS : z ∈ S := zero_mem_closed_of_tendstoLocallyUniformlyOn isOpen_centeredStrip
    isPreconnected_centeredStrip hconv (fun w _ => XiC_analytic w (Set.mem_univ w))
    hdiff hS hzero h0 XiC_zero_ne hzU hXiC
  have hzreal : z.im = 0 := XiC_im_eq_zero_of_sq_im_eq_zero hXiC hzS
  have hre : ρ.re = 1 / 2 := by linarith [hzreal, hzIm]
  exact (ne_of_gt hρh) hre

/-- **The corrected CCM receiver.** If the cross-rooted transforms, divided by the polar factor
`z² + 1/4`, converge to `XiC` locally uniformly on the strip, then RH holds. -/
theorem riemannHypothesis_of_crossRooted_polarQuotient_strip_convergence
    (a : ℕ → SuzukiPositiveAperture) (u : ∀ n, CCMArchimedeanFormDomain (a n)) (c : ℕ → ℂ)
    (hcross : ∀ n, ∀ w : ℂ, unitaryLaplace (timeRep (a n) (u n)) w = 0 →
      w ≠ polarPoint (1 / 2) → w ≠ polarPoint (-1 / 2) → w.re = 0 ∨ w.im = 0)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π)) / (z ^ 2 + 1 / 4))
      XiC atTop centeredStrip) :
    RiemannHypothesis := by
  set Fn : ℕ → ℂ → ℂ :=
    fun n z => c n * unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π)) / (z ^ 2 + 1 / 4)
    with hFn
  have h0 : (0 : ℂ) ∈ centeredStrip := by simp [centeredStrip]
  have hπ : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  have hπpos : (0 : ℝ) < 2 * π := by positivity
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (Fn n) centeredStrip := by
    refine Eventually.of_forall fun n => ?_
    have hd := differentiable_unitaryLaplace (a n).2.le (integrable_timeRep (a n) (u n))
      (supportedIn_timeRep (a n) (u n))
    have hnum : Differentiable ℂ
        (fun z => c n * unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π))) :=
      (hd.comp (differentiable_id.div_const _)).const_mul (c n)
    exact hnum.differentiableOn.div (by fun_prop) (fun z hz => sq_add_quarter_ne_zero hz)
  have hc : ∀ᶠ n in atTop, c n ≠ 0 := by
    have hpt : Tendsto (fun n => Fn n 0) atTop (𝓝 (XiC 0)) := hconv.tendsto_at h0
    filter_upwards [hpt.eventually_ne XiC_zero_ne] with n hn hc0
    apply hn
    simp only [hFn, hc0, zero_mul, zero_div]
  have hzero : ∀ᶠ n in atTop, ∀ w ∈ centeredStrip, Fn n w = 0 → (w ^ 2).im = 0 := by
    filter_upwards [hc] with n hcn w hw hzero
    have hnum : c n * unitaryLaplace (timeRep (a n) (u n)) (w / (2 * π)) = 0 :=
      (div_eq_zero_iff.mp hzero).resolve_right (sq_add_quarter_ne_zero hw)
    have hT : unitaryLaplace (timeRep (a n) (u n)) (w / (2 * π)) = 0 :=
      (mul_eq_zero.mp hnum).resolve_left hcn
    have hcr : (w / (2 * π)).re = 0 ∨ (w / (2 * π)).im = 0 := by
      by_cases h1 : w / (2 * π) = polarPoint (1 / 2)
      · left
        rw [h1]
        exact polarPoint_re _
      by_cases h2 : w / (2 * π) = polarPoint (-1 / 2)
      · left
        rw [h2]
        exact polarPoint_re _
      exact hcross n _ hT h1 h2
    have hre : (w / (2 * π)).re = w.re / (2 * π) := by rw [hπ, Complex.div_ofReal_re]
    have him : (w / (2 * π)).im = w.im / (2 * π) := by rw [hπ, Complex.div_ofReal_im]
    rw [sq, Complex.mul_im]
    rcases hcr with h | h
    · rw [hre, div_eq_zero_iff] at h
      rcases h with h | h
      · rw [h]; ring
      · exact absurd h hπpos.ne'
    · rw [him, div_eq_zero_iff] at h
      rcases h with h | h
      · rw [h]; ring
      · exact absurd h hπpos.ne'
  exact riemannHypothesis_of_strip_convergence_of_cross_zeros Fn hdiff hzero hconv

/-- **The CCM approximation programme, corrected.** For cross-rooted polar even ground states, RH
follows once their transforms divided by `z² + 1/4` converge to `XiC` on the strip. -/
theorem riemannHypothesis_of_evenGround_polarQuotient_strip_convergence
    (a : ℕ → SuzukiPositiveAperture) (u : ∀ n, CCMArchimedeanFormDomain (a n)) (c : ℕ → ℂ)
    (hground : ∀ n, RHTower.CCMEvenSector.IsEvenGround (a n) (u n) ∧
      ∀ w : ℂ, unitaryLaplace (timeRep (a n) (u n)) w = 0 →
        w ≠ polarPoint (1 / 2) → w ≠ polarPoint (-1 / 2) → w.re = 0 ∨ w.im = 0)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π)) / (z ^ 2 + 1 / 4))
      XiC atTop centeredStrip) :
    RiemannHypothesis :=
  riemannHypothesis_of_crossRooted_polarQuotient_strip_convergence a u c
    (fun n => (hground n).2) hconv

end RHTower.CCMPolarObstruction
