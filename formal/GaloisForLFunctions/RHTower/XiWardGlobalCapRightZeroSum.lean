import GaloisForLFunctions.RHTower.XiWardCapGlobalIntegrability
import GaloisForLFunctions.RHTower.XiWardTriangularSourceRectangle
import GaloisForLFunctions.RHTower.XiCriticalLineThinStripSourceProjector
import GaloisForLFunctions.RHTower.LorentzianZeroMass

/-!
# The global Ward cap is the Stieltjes transform of the zeros to the right of the cap line

The canonical Ward cap at level `θ = θ(s) ∈ (0, ½)` integrates the Schwarz two-pole kernel against
the completed prime–archimedean source trace along the line `Re s = ½ + θ`.  For almost every
level the global cap converges absolutely (`ae_forall_integrable_xiWardSchwarzCapFactor`).  This
file evaluates it.

**Theorem** (`ae_forall_xiWardGlobalCap_eq_rightZeroSum`).  For almost every canonical level and
every `τ`,

  `∫_ℝ K_τ(x) T(x − θ i) dx = −8π τ Σ_{Re ρ > ½ + θ} 1 / ((ρ + 1/100)² + τ²)`,

the sum running over the zeros of `ξ` with multiplicity.  The weights do not depend on the level:
the kernel poles sit at the fixed abscissa `−1/100` of the `s`-plane.

The proof closes the cap line downward in the centred coordinate (to the right in `s`) on
rectangles `[−T, T] × [−T, −θ]`.  On the far edges the kernel is `O(|τ|/T²)` and `|ξ'/ξ|` is
`O(log T)`; on the two horizontal strip edges a height `T ∈ [n, n + 1]` is chosen by averaging, so
that `∫_{½}^{2} |ξ'/ξ(σ ± iT)| dσ = O(log n)` (`exists_good_xiWardHeight`).  The kernel has no
pole below the cap line, so the prime side of the cap is identically zero and only the residues at
zeros right of the line survive.

**Sign** (`ae_forall_xiWardGlobalCap_re_nonneg`).  Zeros off the critical line have
`|Im ρ| ≥ 12.16`, so for `0 < τ ≤ 12` every right zero contributes
`Re 1/((ρ + 1/100)² + τ²) < 0`.  Hence the global cap is nonnegative for every such `τ`, and it
vanishes exactly when no zero lies right of the cap line: the one-sided cap family exists
unconditionally, in the nonnegative orientation.

**Vanishing** (`ae_xiWardGlobalCap_eq_zero_iff`).  The global caps vanish for almost every level
exactly when every zero lies on the critical line.
-/

open Complex MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-! ## The kernel in the centred coordinate -/

/-- The Schwarz-paired Ward cap kernel as an analytic function of the centred coordinate. -/
def xiWardCapKernel (tau : ℝ) (z : ℂ) : ℂ :=
  xiWardCauchySourceWeight (((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)) z -
    xiWardCauchySourceWeight (((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ)) z

theorem xiWardSchwarzCapDifference_eq_xiWardCapKernel (tau s x : ℝ) :
    xiWardSchwarzCapDifference tau s x = xiWardCapKernel tau (xiWardLowerCapPoint s x) := by
  unfold xiWardSchwarzCapDifference xiWardCapKernel xiWardLowerCapPoint xiWardCauchySourceWeight
  congr 1
  rw [map_mul, map_inv₀, map_add, map_mul, map_sub, map_mul, map_add, map_mul]
  simp only [Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  congr 2
  push_cast
  ring

/-- The open half-plane below the kernel poles. -/
def xiWardCapKernelDomain : Set ℂ := {z | z.im < 1 / 2}

theorem isOpen_xiWardCapKernelDomain : IsOpen xiWardCapKernelDomain :=
  isOpen_lt Complex.continuous_im continuous_const

theorem analyticOnNhd_xiWardCapKernel (tau : ℝ) :
    AnalyticOnNhd ℂ (xiWardCapKernel tau) xiWardCapKernelDomain := by
  have hsub : ∀ w : ℂ, w.re = 51 / 100 → xiWardCapKernelDomain ⊆ xiWardCauchySourcePoleFreeDomain w := by
    intro w hw z hz hzw
    have h := congrArg Complex.im hzw
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, hw] at h
    change z.im < 1 / 2 at hz
    linarith
  refine ((analyticOnNhd_xiWardCauchySourceWeight _).mono (hsub _ ?_)).sub
    ((analyticOnNhd_xiWardCauchySourceWeight _).mono (hsub _ ?_)) <;> simp

private theorem norm_add_I_mul_ge_re (w z : ℂ) : |w.re - z.im| ≤ ‖w + I * z‖ := by
  have h := Complex.abs_re_le_norm (w + I * z)
  simpa [Complex.add_re, Complex.mul_re, sub_eq_add_neg] using h

private theorem norm_add_I_mul_ge_im (w z : ℂ) : |w.im + z.re| ≤ ‖w + I * z‖ := by
  have h := Complex.abs_im_le_norm (w + I * z)
  simpa [Complex.add_im, Complex.mul_im] using h

/-- Two-pole form of the kernel. -/
theorem xiWardCapKernel_eq (tau : ℝ) {z : ℂ}
    (h1 : (((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)) + I * z ≠ 0)
    (h2 : (((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ)) + I * z ≠ 0) :
    xiWardCapKernel tau z = -4 * I * (tau : ℂ) *
      ((((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)) + I * z)⁻¹ *
      ((((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ)) + I * z)⁻¹ := by
  unfold xiWardCapKernel xiWardCauchySourceWeight
  field_simp
  ring

theorem norm_xiWardCapKernel_le (tau : ℝ) {z : ℂ} {m : ℝ} (hm : 0 < m)
    (h1 : m ≤ ‖(((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)) + I * z‖)
    (h2 : m ≤ ‖(((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ)) + I * z‖) :
    ‖xiWardCapKernel tau z‖ ≤ 4 * |tau| / m ^ 2 := by
  have h1' : (((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)) + I * z ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have h2' : (((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ)) + I * z ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; linarith
  rw [xiWardCapKernel_eq tau h1' h2', norm_mul, norm_mul, norm_inv, norm_inv, norm_mul, norm_mul,
    norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hp1 : 0 < ‖(((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)) + I * z‖ := norm_pos_iff.mpr h1'
  have hp2 : 0 < ‖(((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ)) + I * z‖ := norm_pos_iff.mpr h2'
  rw [show ‖(4 : ℂ)‖ = 4 by norm_num]
  have hi1 := inv_anti₀ hm h1
  have hi2 := inv_anti₀ hm h2
  have h4 : 0 ≤ 4 * 1 * |tau| := by positivity
  calc 4 * 1 * |tau| * ‖(((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)) + I * z‖⁻¹ *
        ‖(((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ)) + I * z‖⁻¹
      ≤ 4 * 1 * |tau| * m⁻¹ * m⁻¹ := by gcongr
    _ = 4 * |tau| / m ^ 2 := by field_simp

/-- Below the line `Im z = −1`: `‖K_τ(z)‖ ≤ 4|τ| / (Im z)²`. -/
theorem norm_xiWardCapKernel_le_of_im (tau : ℝ) {z : ℂ} (hz : z.im ≤ -1) :
    ‖xiWardCapKernel tau z‖ ≤ 4 * |tau| / z.im ^ 2 := by
  have hm : 0 < -z.im := by linarith
  have key : ∀ w : ℂ, w.re = 51 / 100 → -z.im ≤ ‖w + I * z‖ := fun w hw =>
    le_trans (by rw [hw, abs_of_pos (by linarith)]; linarith) (norm_add_I_mul_ge_re w z)
  have h := norm_xiWardCapKernel_le tau hm (key _ (by simp)) (key _ (by simp))
  rwa [neg_sq] at h

/-- On the vertical edges `|Re z| = T ≥ 2|τ|`: `‖K_τ(z)‖ ≤ 16|τ| / T²`. -/
theorem norm_xiWardCapKernel_le_of_re (tau : ℝ) {z : ℂ} {T : ℝ} (hT : 2 * |tau| ≤ T) (hT0 : 0 < T)
    (hz : |z.re| = T) : ‖xiWardCapKernel tau z‖ ≤ 16 * |tau| / T ^ 2 := by
  have hm : 0 < T / 2 := by linarith
  have key : ∀ w : ℂ, |w.im| = |tau| → T / 2 ≤ ‖w + I * z‖ := by
    intro w hw
    refine le_trans ?_ (norm_add_I_mul_ge_im w z)
    have h1 := abs_sub_abs_le_abs_add z.re w.im
    rw [hz, hw] at h1
    rw [add_comm]
    linarith
  have h := norm_xiWardCapKernel_le tau hm (key _ (by simp)) (key _ (by simp))
  calc ‖xiWardCapKernel tau z‖ ≤ 4 * |tau| / (T / 2) ^ 2 := h
    _ = 16 * |tau| / T ^ 2 := by field_simp; ring

/-! ## The trace off the zeros -/

/-- Off the zeros of `ζ` in `Re s > 0`, `s ≠ 1`, the trace is `i · ξ'/ξ(½ + iz)`. -/
theorem continuedPrimeArchSourceRelativeTrace_eq_I_mul {z : ℂ}
    (hpos : 0 < (1 / 2 + z * I).re) (h1 : 1 / 2 + z * I ≠ 1)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    continuedPrimeArchSourceRelativeTrace z = I * logDeriv xi (1 / 2 + z * I) := by
  have hseam := seamFluxCochain_eq_continuedPrime_add_archimedean hpos h1 hzeta
  rw [seamFluxCochain] at hseam
  unfold continuedPrimeArchSourceRelativeTrace
  rw [← hseam]
  ring

/-- A zero of `ζ` with positive real part is a zero of `ξ`, hence a zero copy. -/
theorem exists_xiZeroCopy_of_riemannZeta_eq_zero {w : ℂ} (h0 : 0 < w.re) (h1 : w ≠ 1)
    (hζ : riemannZeta w = 0) : ∃ q : XiZeroCopy, (q.1 : ℂ) = w := by
  have hw0 : w ≠ 0 := by intro h; rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hxi : xi w = 0 := by
    rw [xi_eq_archFactor_mul_zeta hw0 h1 (Gammaℝ_ne_zero_of_re_pos h0), hζ, mul_zero]
  exact exists_xiZeroCopy_of_xi_eq_zero hxi

/-! ## A good height in every unit interval -/

/-- Window majorant on the strip `½ ≤ Re s ≤ 2`. -/
theorem norm_logDeriv_xi_le_window_strip {t₀ : ℝ} (ht₀ : 8 ≤ t₀) {s : ℂ} (h1 : 1 / 2 ≤ s.re)
    (h2 : s.re ≤ 2) (hs : |s.im - t₀| ≤ 1) (hxi : xi s ≠ 0) :
    ‖logDeriv xi s‖ ≤ windowLogConst * Real.log t₀ +
      ∑ q ∈ windowCopySet t₀, 1 / ‖s - (q.1 : ℂ)‖ := by
  have h := norm_logDeriv_xi_sub_window_le ht₀ h1 h2 hs hxi
  have htri : ‖∑ q ∈ windowCopySet t₀, (s - (q.1 : ℂ))⁻¹‖ ≤
      ∑ q ∈ windowCopySet t₀, 1 / ‖s - (q.1 : ℂ)‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => ?_))
    rw [norm_inv, one_div]
  calc ‖logDeriv xi s‖ ≤ ‖logDeriv xi s - ∑ q ∈ windowCopySet t₀, (s - (q.1 : ℂ))⁻¹‖ +
        ‖∑ q ∈ windowCopySet t₀, (s - (q.1 : ℂ))⁻¹‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add h htri

/-- The heights of zero copies, with both signs. -/
def xiZeroHeightSet : Set ℝ :=
  range (fun q : XiZeroCopy => (q.1 : ℂ).im) ∪ range (fun q : XiZeroCopy => -(q.1 : ℂ).im)

theorem countable_xiZeroHeightSet : xiZeroHeightSet.Countable :=
  (countable_range _).union (countable_range _)

theorem not_mem_xiZeroHeightSet {T : ℝ} (hT : T ∉ xiZeroHeightSet) (q : XiZeroCopy) :
    (q.1 : ℂ).im ≠ T ∧ (q.1 : ℂ).im ≠ -T := by
  refine ⟨fun h => hT (Or.inl ⟨q, h⟩), fun h => hT (Or.inr ⟨q, ?_⟩)⟩
  change -(q.1 : ℂ).im = T
  rw [h, neg_neg]

theorem measurable_ofReal_abs_sub_rpow (c : ℝ) :
    Measurable fun y : ℝ => ENNReal.ofReal (|y - c| ^ (-(1 / 2 : ℝ))) :=
  ((measurable_id.sub_const c).abs.pow_const _).ennreal_ofReal

/-- The good-height bound in the unit interval `[n, n + 1]`. -/
def xiWardGoodHeightBound (n : ℕ) : ℝ :=
  2 * ((3 / 2) * windowLogConst * Real.log ((n : ℝ) + 1 / 2) +
    ((windowCopySet ((n : ℝ) + 1 / 2)).card : ℝ) * (4 * Real.sqrt 2 * (4 * Real.sqrt 3)))

/-- The point `(½ − y) + iT` of the right strip edge. -/
def xiWardStripPoint (T y : ℝ) : ℂ := ((1 / 2 - y : ℝ) : ℂ) + (T : ℂ) * I

/-- **Good heights.**  Every interval `[n, n + 1]`, `n ≥ 8`, contains a height `T` carrying no zero
of `ξ` (at `±T`) along which `∫_{½}^{2} |ξ'/ξ(σ + iT)| dσ` is at most `xiWardGoodHeightBound n`. -/
theorem exists_good_xiWardHeight {n : ℕ} (hn : 8 ≤ n) :
    ∃ T ∈ Icc (n : ℝ) (n + 1), T ∉ xiZeroHeightSet ∧
      ∫⁻ y in Icc (-(3 / 2) : ℝ) 0, ‖logDeriv xi (xiWardStripPoint T y)‖ₑ ≤
        ENNReal.ofReal (xiWardGoodHeightBound n) := by
  set t₀ : ℝ := (n : ℝ) + 1 / 2 with ht₀
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have ht₀8 : 8 ≤ t₀ := by linarith
  set W := windowCopySet t₀ with hW
  set A : ℝ := windowLogConst * Real.log t₀ with hA
  have hA0 : 0 < A := mul_pos (by unfold windowLogConst; positivity)
    (Real.log_pos (by linarith))
  set B₀ : ℝ := (3 / 2) * A + (W.card : ℝ) * (4 * Real.sqrt 2 * (4 * Real.sqrt 3)) with hB₀
  have hB₀pos : 0 < B₀ := by positivity
  have hbound : xiWardGoodHeightBound n = 2 * B₀ := by
    rw [xiWardGoodHeightBound, hB₀, hA]; ring
  set F : ℝ → ENNReal := fun T =>
    ∫⁻ y in Icc (-(3 / 2) : ℝ) 0, ‖logDeriv xi (xiWardStripPoint T y)‖ₑ with hF
  set M : ℝ → ENNReal := fun T => ENNReal.ofReal ((3 / 2) * A) +
    ∑ q ∈ W, ENNReal.ofReal (|T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ))) *
      ENNReal.ofReal (4 * Real.sqrt 2) with hM
  -- pointwise majorant off the zero heights
  have hFM : ∀ T ∈ Icc (n : ℝ) (n + 1), T ∉ xiZeroHeightSet → F T ≤ M T := by
    intro T hT hTgood
    have hTt : |T - t₀| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
    set E : Set ℝ := (W : Set XiZeroCopy).image (fun q => 1 / 2 - (q.1 : ℂ).re) with hE
    have hEnull : volume E = 0 := ((W.finite_toSet.image _).countable).measure_zero _
    have hpt : ∀ᵐ y ∂(volume.restrict (Icc (-(3 / 2) : ℝ) 0)),
        ‖logDeriv xi (xiWardStripPoint T y)‖ₑ ≤ ENNReal.ofReal A +
          ∑ q ∈ W, ENNReal.ofReal (|T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ))) *
            ENNReal.ofReal (|y - (1 / 2 - (q.1 : ℂ).re)| ^ (-(1 / 2 : ℝ))) := by
      have hae : ∀ᵐ y ∂(volume : Measure ℝ), y ∉ E := by
        rw [ae_iff]; simpa using hEnull
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hae] with y hyE hy
      set w : ℂ := xiWardStripPoint T y with hw
      have hre : w.re = 1 / 2 - y := by simp [hw, xiWardStripPoint]
      have him : w.im = T := by simp [hw, xiWardStripPoint]
      have hxi : xi w ≠ 0 := by
        intro h0
        obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h0
        exact (not_mem_xiZeroHeightSet hTgood q).1 (by rw [hq, him])
      have hwin := norm_logDeriv_xi_le_window_strip ht₀8 (by rw [hre]; linarith [hy.2])
        (by rw [hre]; linarith [hy.1]) (by rw [him]; exact hTt) hxi
      have hterm : ∀ q ∈ W, 1 / ‖w - (q.1 : ℂ)‖ ≤
          |T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ)) *
            |y - (1 / 2 - (q.1 : ℂ).re)| ^ (-(1 / 2 : ℝ)) := by
        intro q hq
        have hσ : 1 / 2 - y ≠ (q.1 : ℂ).re := by
          intro h; exact hyE ⟨q, hq, by simp only; linarith⟩
        have hT' : T ≠ (q.1 : ℂ).im := fun h => (not_mem_xiZeroHeightSet hTgood q).1 h.symm
        have h := GaloisForLFunctions.HTGeometry.inv_norm_sub_le_rpow (q.1 : ℂ) hσ hT'
        have hpt : w = ((1 / 2 - y : ℝ) : ℂ) + (T : ℂ) * I := rfl
        rw [hpt]
        refine h.trans (le_of_eq ?_)
        rw [mul_comm, show (1 / 2 - y) - (q.1 : ℂ).re = -(y - (1 / 2 - (q.1 : ℂ).re)) by ring,
          abs_neg]
      have hsum : ∑ q ∈ W, 1 / ‖w - (q.1 : ℂ)‖ ≤ ∑ q ∈ W,
          |T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ)) *
            |y - (1 / 2 - (q.1 : ℂ).re)| ^ (-(1 / 2 : ℝ)) := Finset.sum_le_sum hterm
      have hnn : ∀ q ∈ W, 0 ≤ |T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ)) *
          |y - (1 / 2 - (q.1 : ℂ).re)| ^ (-(1 / 2 : ℝ)) := fun q _ =>
        mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
      calc ‖logDeriv xi w‖ₑ = ENNReal.ofReal ‖logDeriv xi w‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (A + ∑ q ∈ W, |T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ)) *
            |y - (1 / 2 - (q.1 : ℂ).re)| ^ (-(1 / 2 : ℝ))) :=
          ENNReal.ofReal_le_ofReal (hwin.trans (by rw [hA]; linarith))
        _ = _ := by
          rw [ENNReal.ofReal_add hA0.le (Finset.sum_nonneg hnn), ENNReal.ofReal_sum_of_nonneg hnn]
          congr 1
          refine Finset.sum_congr rfl fun q _ => ?_
          exact ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)
    have hmeas : ∀ q ∈ W, Measurable fun y : ℝ =>
        ENNReal.ofReal (|T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (|y - (1 / 2 - (q.1 : ℂ).re)| ^ (-(1 / 2 : ℝ))) := fun q _ =>
      measurable_const.mul (measurable_ofReal_abs_sub_rpow _)
    calc F T ≤ ∫⁻ y in Icc (-(3 / 2) : ℝ) 0, (ENNReal.ofReal A +
          ∑ q ∈ W, ENNReal.ofReal (|T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ))) *
            ENNReal.ofReal (|y - (1 / 2 - (q.1 : ℂ).re)| ^ (-(1 / 2 : ℝ)))) := lintegral_mono_ae hpt
      _ = ENNReal.ofReal A * ENNReal.ofReal (3 / 2) + ∑ q ∈ W,
          ENNReal.ofReal (|T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ))) *
            ∫⁻ y in Icc (-(3 / 2) : ℝ) 0,
              ENNReal.ofReal (|y - (1 / 2 - (q.1 : ℂ).re)| ^ (-(1 / 2 : ℝ))) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, Real.volume_Icc,
            lintegral_finsetSum _ hmeas]
          norm_num
          congr 1
          refine Finset.sum_congr rfl fun q _ => ?_
          exact lintegral_const_mul _ (measurable_ofReal_abs_sub_rpow _)
      _ ≤ M T := by
          rw [← ENNReal.ofReal_mul hA0.le, mul_comm A (3 / 2)]
          simp only [hM]
          gcongr with q hq
          calc ∫⁻ y in Icc (-(3 / 2) : ℝ) 0,
                ENNReal.ofReal (|y - (1 / 2 - (q.1 : ℂ).re)| ^ (-(1 / 2 : ℝ)))
              ≤ ∫⁻ y in Icc ((1 / 2 - (q.1 : ℂ).re) - 2) ((1 / 2 - (q.1 : ℂ).re) + 2),
                ENNReal.ofReal (|y - (1 / 2 - (q.1 : ℂ).re)| ^ (-(1 / 2 : ℝ))) := by
                apply lintegral_mono_set
                intro y hy
                have h0 := xiZeroCopy_re_pos q
                have h1 := xiZeroCopy_re_lt_one q
                constructor <;> linarith [hy.1, hy.2]
            _ ≤ ENNReal.ofReal (4 * Real.sqrt 2) := GaloisForLFunctions.HTGeometry.lintegral_Icc_abs_sub_rpow_neg_half_le _ (by norm_num)
  -- the majorant has small mean
  have hMint : ∫⁻ T in Icc (n : ℝ) (n + 1), M T ≤ ENNReal.ofReal B₀ := by
    have hmeas : ∀ q ∈ W, Measurable fun T : ℝ =>
        ENNReal.ofReal (|T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (4 * Real.sqrt 2) :=
      fun q _ => (measurable_ofReal_abs_sub_rpow _).mul measurable_const
    rw [hM, lintegral_add_left measurable_const, setLIntegral_const, Real.volume_Icc,
      lintegral_finsetSum _ hmeas]
    have hone : ((n : ℝ) + 1 - n) = 1 := by ring
    rw [hone, ENNReal.ofReal_one, mul_one, hB₀,
      ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
    calc ∑ q ∈ W, ∫⁻ T in Icc (n : ℝ) (n + 1),
          ENNReal.ofReal (|T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (4 * Real.sqrt 2)
        ≤ ∑ _q ∈ W, ENNReal.ofReal (4 * Real.sqrt 3) * ENNReal.ofReal (4 * Real.sqrt 2) := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [lintegral_mul_const _ (measurable_ofReal_abs_sub_rpow _)]
          gcongr
          have hq' := mem_windowCopySet.mp hq
          calc ∫⁻ T in Icc (n : ℝ) (n + 1), ENNReal.ofReal (|T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ)))
              ≤ ∫⁻ T in Icc ((q.1 : ℂ).im - 3) ((q.1 : ℂ).im + 3),
                  ENNReal.ofReal (|T - (q.1 : ℂ).im| ^ (-(1 / 2 : ℝ))) := by
                apply lintegral_mono_set
                intro T hT
                rw [abs_lt] at hq'
                constructor <;> linarith [hT.1, hT.2, hq'.1, hq'.2]
            _ ≤ ENNReal.ofReal (4 * Real.sqrt 3) :=
                GaloisForLFunctions.HTGeometry.lintegral_Icc_abs_sub_rpow_neg_half_le _ (by norm_num)
      _ = ENNReal.ofReal (W.card * (4 * Real.sqrt 2 * (4 * Real.sqrt 3))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  -- choose a good height
  by_contra hcon
  push Not at hcon
  have hgoodae : ∀ᵐ T ∂(volume : Measure ℝ), T ∉ xiZeroHeightSet := by
    rw [ae_iff]; simpa using countable_xiZeroHeightSet.measure_zero volume
  have hlow : ENNReal.ofReal (2 * B₀) ≤ ∫⁻ T in Icc (n : ℝ) (n + 1), F T := by
    calc ENNReal.ofReal (2 * B₀) = ∫⁻ _T in Icc (n : ℝ) (n + 1), ENNReal.ofReal (2 * B₀) := by
          rw [setLIntegral_const, Real.volume_Icc, show ((n : ℝ) + 1 - n) = 1 by ring,
            ENNReal.ofReal_one, mul_one]
      _ ≤ ∫⁻ T in Icc (n : ℝ) (n + 1), F T := by
          apply lintegral_mono_ae
          rw [ae_restrict_iff' measurableSet_Icc]
          filter_upwards [hgoodae] with T hT hTI
          have := hcon T hTI hT
          rw [hbound] at this
          exact this.le
  have hup : ∫⁻ T in Icc (n : ℝ) (n + 1), F T ≤ ENNReal.ofReal B₀ := by
    refine le_trans (lintegral_mono_ae ?_) hMint
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hgoodae] with T hT hTI
    exact hFM T hTI hT
  have := (ENNReal.ofReal_le_ofReal_iff hB₀pos.le).mp (hlow.trans hup)
  linarith

/-! ## The rectangle identity at one height -/

/-- Admissibility from the absence of a zero copy at the point. -/
theorem xiExplicitAdmissible_of_forall_ne {z : ℂ} (hpos : 0 < (1 / 2 + z * I).re)
    (h1 : 1 / 2 + z * I ≠ 1) (hq : ∀ q : XiZeroCopy, (q.1 : ℂ) ≠ 1 / 2 + z * I) :
    XiExplicitAdmissible z where
  re_pos := hpos
  ne_one := h1
  zeta_ne := by
    intro hζ
    obtain ⟨q, hq'⟩ := exists_xiZeroCopy_of_riemannZeta_eq_zero hpos h1 hζ
    exact hq q hq'

/-- Lower-left corner of the cap rectangle. -/
def xiWardCapCornerLow (T : ℝ) : ℂ := ((-T : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I

/-- Upper-right corner of the cap rectangle, on the cap line. -/
def xiWardCapCornerHigh (θ T : ℝ) : ℂ := (T : ℂ) + ((-θ : ℝ) : ℂ) * I

@[simp] theorem xiWardCapCornerLow_re (T : ℝ) : (xiWardCapCornerLow T).re = -T := by
  simp [xiWardCapCornerLow]
@[simp] theorem xiWardCapCornerLow_im (T : ℝ) : (xiWardCapCornerLow T).im = -T := by
  simp [xiWardCapCornerLow]
@[simp] theorem xiWardCapCornerHigh_re (θ T : ℝ) : (xiWardCapCornerHigh θ T).re = T := by
  simp [xiWardCapCornerHigh]
@[simp] theorem xiWardCapCornerHigh_im (θ T : ℝ) : (xiWardCapCornerHigh θ T).im = -θ := by
  simp [xiWardCapCornerHigh]

private theorem xiWardCap_re_half_add (z : ℂ) : (1 / 2 + z * I).re = 1 / 2 - z.im := by
  simp [Complex.add_re, Complex.mul_re, sub_eq_add_neg]

private theorem xiWardCap_im_half_add (z : ℂ) : (1 / 2 + z * I).im = z.re := by
  simp [Complex.add_im, Complex.mul_im]

/-- **Rectangle identity.**  If no zero lies on the cap line `Re s = ½ + θ` and no zero has height
`±T`, the Ward cap contour around `[−T, T] × [−T, −θ]` is `2πi` times the kernel summed over the
enclosed zero copies. -/
theorem rectIntegral_xiWardCapKernel_eq {θ T tau : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2)
    (hT : 2 ≤ T) (hTgood : T ∉ xiZeroHeightSet)
    (hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 + θ) :
    rectIntegral (fun z => xiWardCapKernel tau z * continuedPrimeArchSourceRelativeTrace z)
        (xiWardCapCornerLow T) (xiWardCapCornerHigh θ T) =
      2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle (xiWardCapCornerLow T)
        (xiWardCapCornerHigh θ T), xiWardCapKernel tau (xiSpectralPoint q) := by
  set z₁ := xiWardCapCornerLow T
  set z₂ := xiWardCapCornerHigh θ T
  have hre : z₁.re < z₂.re := by simp only [z₁, z₂, xiWardCapCornerLow_re, xiWardCapCornerHigh_re]; linarith
  have him : z₁.im < z₂.im := by simp only [z₁, z₂, xiWardCapCornerLow_im, xiWardCapCornerHigh_im]; linarith
  have hrect : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ xiWardCapKernelDomain := by
    intro z hz
    have hzi := (Complex.mem_reProdIm.mp hz).2
    rw [uIcc_of_le him.le] at hzi
    change z.im < 1 / 2
    simp only [z₂, xiWardCapCornerHigh_im] at hzi
    linarith [hzi.2]
  have hne1 : ∀ z : ℂ, z.re ≠ 0 → 1 / 2 + z * I ≠ 1 := by
    intro z hz h
    have := congrArg Complex.im h
    rw [xiWardCap_im_half_add] at this
    simp at this
    exact hz this
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, XiExplicitAdmissible ((x : ℂ) + z₁.im * I) := by
    intro x _
    apply XiExplicitAdmissible_of_one_lt_re
    rw [xiWardCap_re_half_add]
    simp only [z₁, xiWardCapCornerLow_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im]
    linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, XiExplicitAdmissible ((x : ℂ) + z₂.im * I) := by
    intro x _
    have himz : ((x : ℂ) + z₂.im * I).im = -θ := by
      simp [z₂]
    refine xiExplicitAdmissible_of_forall_ne ?_ ?_ ?_
    · rw [xiWardCap_re_half_add, himz]; linarith
    · intro h
      have := congrArg Complex.re h
      rw [xiWardCap_re_half_add, himz, Complex.one_re] at this
      linarith
    · intro q hq
      apply hline q
      rw [hq, xiWardCap_re_half_add, himz]; ring
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, XiExplicitAdmissible ((z₂.re : ℂ) + y * I) := by
    intro y hy
    rw [uIcc_of_le him.le] at hy
    simp only [z₂, xiWardCapCornerHigh_im, z₁, xiWardCapCornerLow_im] at hy
    have hrez : ((z₂.re : ℂ) + y * I).re = T := by simp [z₂]
    have himz : ((z₂.re : ℂ) + y * I).im = y := by simp
    refine xiExplicitAdmissible_of_forall_ne ?_ (hne1 _ (by rw [hrez]; linarith)) ?_
    · rw [xiWardCap_re_half_add, himz]; linarith [hy.2]
    · intro q hq
      apply (not_mem_xiZeroHeightSet hTgood q).1
      rw [hq, xiWardCap_im_half_add, hrez]
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, XiExplicitAdmissible ((z₁.re : ℂ) + y * I) := by
    intro y hy
    rw [uIcc_of_le him.le] at hy
    simp only [z₂, xiWardCapCornerHigh_im, z₁, xiWardCapCornerLow_im] at hy
    have hrez : ((z₁.re : ℂ) + y * I).re = -T := by simp [z₁]
    have himz : ((z₁.re : ℂ) + y * I).im = y := by simp
    refine xiExplicitAdmissible_of_forall_ne ?_ (hne1 _ (by rw [hrez]; linarith)) ?_
    · rw [xiWardCap_re_half_add, himz]; linarith [hy.2]
    · intro q hq
      apply (not_mem_xiZeroHeightSet hTgood q).2
      rw [hq, xiWardCap_im_half_add, hrez]
  have hres := rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum_local
    isOpen_xiWardCapKernelDomain (analyticOnNhd_xiWardCapKernel tau) hrect hre him hbot htop
    hright hleft
  rw [hres]
  congr 1
  calc ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * xiWardCapKernel tau w =
      ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        (xiSpectralMultiplicity w : ℂ) * xiWardCapKernel tau w := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat (mem_xiCClosedRectangleZeros.mp hw).2]
    _ = _ := (sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum (xiWardCapKernel tau) z₁ z₂).symm

/-! ## The far edges -/

/-- The logarithmic size `|C| + log(T + 4)` of `ξ'/ξ` on the far edges. -/
def xiWardEdgeLog (T : ℝ) : ℝ := |xiLineTwoLogDerivConstant| + Real.log (T + 4)

theorem xiWardEdgeLog_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ xiWardEdgeLog T :=
  add_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith))

theorem norm_logDeriv_xi_le_edgeLog {s : ℂ} {T : ℝ} (hs : 2 ≤ s.re)
    (hnorm : ‖s‖ ≤ 1 / 2 + 2 * T) : ‖logDeriv xi s‖ ≤ xiWardEdgeLog T := by
  refine (norm_logDeriv_xi_le_of_two_le_re hs).trans ?_
  unfold xiWardEdgeLog
  have hlog : Real.log (‖s‖ / 2 + 3) ≤ Real.log (T + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith [le_abs_self xiLineTwoLogDerivConstant]

theorem norm_trace_eq_of_two_le_re {z : ℂ} (hs : 2 ≤ (1 / 2 + z * I).re) :
    ‖continuedPrimeArchSourceRelativeTrace z‖ = ‖logDeriv xi (1 / 2 + z * I)‖ := by
  rw [continuedPrimeArchSourceRelativeTrace_eq_I_mul (by linarith) (by
      intro h; rw [h, Complex.one_re] at hs; linarith)
      (riemannZeta_ne_zero_of_one_le_re (by linarith)), norm_mul, Complex.norm_I, one_mul]

/-- **Bottom edge.**  `‖∫_{−T}^{T} K_τ T(x − iT) dx‖ ≤ 8|τ| L(T)/T`. -/
theorem norm_xiWardCapBottomEdge_le {tau T : ℝ} (hT : 2 ≤ T) :
    ‖∫ x in (-T)..T, xiWardCapKernel tau ((x : ℂ) + ((-T : ℝ) : ℂ) * I) *
        continuedPrimeArchSourceRelativeTrace ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
      4 * |tau| / T ^ 2 * xiWardEdgeLog T * (2 * T) := by
  have hbound : ∀ x ∈ uIoc (-T) T, ‖xiWardCapKernel tau ((x : ℂ) + ((-T : ℝ) : ℂ) * I) *
      continuedPrimeArchSourceRelativeTrace ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
      4 * |tau| / T ^ 2 * xiWardEdgeLog T := by
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    set z : ℂ := (x : ℂ) + ((-T : ℝ) : ℂ) * I with hz
    have hzim : z.im = -T := by simp [hz]
    have hzre : z.re = x := by simp [hz]
    have hsre : (1 / 2 + z * I).re = 1 / 2 + T := by rw [xiWardCap_re_half_add, hzim]; ring
    have hk := norm_xiWardCapKernel_le_of_im tau (z := z) (by rw [hzim]; linarith)
    rw [hzim, neg_sq] at hk
    rw [norm_mul, norm_trace_eq_of_two_le_re (by rw [hsre]; linarith)]
    have hnorm : ‖1 / 2 + z * I‖ ≤ 1 / 2 + 2 * T := by
      have h1 : 1 / 2 + z * I = ((1 / 2 + T : ℝ) : ℂ) + (x : ℂ) * I := by
        apply Complex.ext <;> simp [hzim, hzre, Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
      rw [h1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have := abs_le.mpr ⟨hx.1.le, hx.2⟩
      linarith
    exact mul_le_mul hk (norm_logDeriv_xi_le_edgeLog (by rw [hsre]; linarith) hnorm)
      (norm_nonneg _) (by positivity)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans (le_of_eq ?_)
  rw [show T - -T = 2 * T by ring, abs_of_pos (show (0 : ℝ) < 2 * T by linarith)]

/-- On a vertical edge `Re z = R`, `|R| = T`, the source point is `(½ − y) ± iT`. -/
private theorem half_add_vertical_mul_I (R y : ℝ) :
    1 / 2 + ((R : ℂ) + (y : ℂ) * I) * I = ((1 / 2 - y : ℝ) : ℂ) + (R : ℂ) * I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, sub_eq_add_neg]

theorem norm_logDeriv_xi_vertical_eq {R T : ℝ} (hR : |R| = T) (y : ℝ) :
    ‖logDeriv xi (((1 / 2 - y : ℝ) : ℂ) + (R : ℂ) * I)‖ =
      ‖logDeriv xi (xiWardStripPoint T y)‖ := by
  have hT : 0 ≤ T := hR ▸ abs_nonneg R
  rcases (abs_eq hT).mp hR with h | h
  · rw [h, xiWardStripPoint]
  · have hconj : ((1 / 2 - y : ℝ) : ℂ) + (R : ℂ) * I = starRingEnd ℂ (xiWardStripPoint T y) := by
      rw [h, xiWardStripPoint]
      apply Complex.ext <;> simp
    rw [hconj, logDeriv_xi_starRingEnd, Complex.norm_conj]

theorem measurable_logDeriv_xi_stripPoint (T : ℝ) :
    Measurable fun y : ℝ => logDeriv xi (xiWardStripPoint T y) := by
  have hl : Measurable (logDeriv xi) := by
    have h1 : Measurable (deriv xi) := xi_differentiable.deriv.continuous.measurable
    have h2 : Measurable xi := xi_differentiable.continuous.measurable
    simpa [logDeriv] using h1.div h2
  exact hl.comp (by unfold xiWardStripPoint; fun_prop)

/-- **Vertical edges.**  With a good height `T`, the edge integral at `Re z = ±T` is at most
`(16|τ|/T²)(T L(T) + B)`. -/
theorem norm_xiWardCapVerticalEdge_le {tau T θ B R : ℝ} (hT : 2 ≤ T) (hτ : 2 * |tau| ≤ T)
    (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) (hR : |R| = T) (hTgood : T ∉ xiZeroHeightSet) (hB : 0 ≤ B)
    (hint : ∫⁻ y in Icc (-(3 / 2) : ℝ) 0, ‖logDeriv xi (xiWardStripPoint T y)‖ₑ ≤
      ENNReal.ofReal B) :
    ‖∫ y in (-T)..(-θ), xiWardCapKernel tau ((R : ℂ) + (y : ℂ) * I) *
        continuedPrimeArchSourceRelativeTrace ((R : ℂ) + (y : ℂ) * I)‖ ≤
      16 * |tau| / T ^ 2 * (T * xiWardEdgeLog T + B) := by
  set G : ℝ → ℂ := fun y => xiWardCapKernel tau ((R : ℂ) + (y : ℂ) * I) *
    continuedPrimeArchSourceRelativeTrace ((R : ℂ) + (y : ℂ) * I) with hG
  have hTpos : 0 < T := by linarith
  have hk : ∀ y : ℝ, ‖xiWardCapKernel tau ((R : ℂ) + (y : ℂ) * I)‖ ≤ 16 * |tau| / T ^ 2 :=
    fun y => norm_xiWardCapKernel_le_of_re tau hτ hTpos (by simpa using hR)
  have hRne : R ≠ 0 := by intro h; rw [h, abs_zero] at hR; linarith
  set K : ℝ := 16 * |tau| / T ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hL0 : 0 ≤ xiWardEdgeLog T := xiWardEdgeLog_nonneg hTpos.le
  -- far part of the edge: `Re s ≥ 2`
  have h1 : ∫⁻ y in Icc (-T) (-(3 / 2) : ℝ), ENNReal.ofReal ‖G y‖ ≤
      ENNReal.ofReal (K * xiWardEdgeLog T) * ENNReal.ofReal T := by
    calc ∫⁻ y in Icc (-T) (-(3 / 2) : ℝ), ENNReal.ofReal ‖G y‖
        ≤ ∫⁻ _y in Icc (-T) (-(3 / 2) : ℝ), ENNReal.ofReal (K * xiWardEdgeLog T) := by
          refine setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal ?_
          have hsre : (1 / 2 + ((R : ℂ) + (y : ℂ) * I) * I).re = 1 / 2 - y := by
            rw [half_add_vertical_mul_I]; simp
          rw [hG, norm_mul, norm_trace_eq_of_two_le_re (by rw [hsre]; linarith [hy.2])]
          refine mul_le_mul (hk y) (norm_logDeriv_xi_le_edgeLog (by rw [hsre]; linarith [hy.2]) ?_)
            (norm_nonneg _) hK0
          rw [half_add_vertical_mul_I]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, hR, abs_of_pos (by linarith [hy.2])]
          linarith [hy.1]
      _ ≤ ENNReal.ofReal (K * xiWardEdgeLog T) * ENNReal.ofReal T := by
          rw [setLIntegral_const, Real.volume_Icc]
          gcongr
          linarith
  -- near part of the edge: the good-height integral
  have h2 : ∫⁻ y in Icc (-(3 / 2) : ℝ) 0, ENNReal.ofReal ‖G y‖ ≤
      ENNReal.ofReal K * ENNReal.ofReal B := by
    calc ∫⁻ y in Icc (-(3 / 2) : ℝ) 0, ENNReal.ofReal ‖G y‖
        ≤ ∫⁻ y in Icc (-(3 / 2) : ℝ) 0,
            ENNReal.ofReal K * ‖logDeriv xi (xiWardStripPoint T y)‖ₑ := by
          refine setLIntegral_mono ((measurable_logDeriv_xi_stripPoint T).enorm.const_mul _)
            fun y hy => ?_
          · set s : ℂ := 1 / 2 + ((R : ℂ) + (y : ℂ) * I) * I with hs
            have hs' : s = ((1 / 2 - y : ℝ) : ℂ) + (R : ℂ) * I := half_add_vertical_mul_I R y
            have hsre : s.re = 1 / 2 - y := by rw [hs']; simp
            have hsim : s.im = R := by rw [hs']; simp
            have htr : continuedPrimeArchSourceRelativeTrace ((R : ℂ) + (y : ℂ) * I) =
                I * logDeriv xi s := by
              refine continuedPrimeArchSourceRelativeTrace_eq_I_mul (by rw [← hs, hsre]; linarith [hy.2])
                (fun h => ?_) (fun hζ => ?_)
              · have := congrArg Complex.im h
                rw [← hs, hsim, Complex.one_im] at this
                exact hRne this
              · have hspos : 0 < s.re := by rw [hsre]; linarith [hy.2]
                have hs1 : s ≠ 1 := by
                  intro h; have := congrArg Complex.im h
                  rw [hsim, Complex.one_im] at this; exact hRne this
                obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_riemannZeta_eq_zero hspos hs1 hζ
                have hqim : (q.1 : ℂ).im = R := by rw [hq, hsim]
                rcases (abs_eq hTpos.le).mp hR with hRT | hRT
                · exact (not_mem_xiZeroHeightSet hTgood q).1 (hqim.trans hRT)
                · exact (not_mem_xiZeroHeightSet hTgood q).2 (hqim.trans hRT)
            rw [hG, norm_mul, htr, norm_mul, Complex.norm_I, one_mul, hs',
              norm_logDeriv_xi_vertical_eq hR y, ← ofReal_norm, ← ENNReal.ofReal_mul hK0]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hk y) (norm_nonneg _))
      _ = ENNReal.ofReal K * ∫⁻ y in Icc (-(3 / 2) : ℝ) 0,
            ‖logDeriv xi (xiWardStripPoint T y)‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal B := by gcongr
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ -θ)]
  refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal (by positivity) ?_)
  have hsub : Ioc (-T) (-θ) ⊆ Icc (-T) (-(3 / 2) : ℝ) ∪ Icc (-(3 / 2) : ℝ) 0 := by
    intro y hy
    rcases le_total y (-(3 / 2)) with h | h
    · exact Or.inl ⟨hy.1.le, h⟩
    · exact Or.inr ⟨h, by linarith [hy.2]⟩
  calc ∫⁻ y in Ioc (-T) (-θ), ENNReal.ofReal ‖G y‖
      ≤ ∫⁻ y in Icc (-T) (-(3 / 2) : ℝ) ∪ Icc (-(3 / 2) : ℝ) 0, ENNReal.ofReal ‖G y‖ :=
        lintegral_mono_set hsub
    _ ≤ _ := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (K * xiWardEdgeLog T) * ENNReal.ofReal T +
        ENNReal.ofReal K * ENNReal.ofReal B := add_le_add h1 h2
    _ = ENNReal.ofReal (K * (T * xiWardEdgeLog T + B)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hK0,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-! ## The kernel at the zeros -/

private theorem xiWardCap_spectral_re (q : XiZeroCopy) : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint_eq_support, xiSpectralPointSupport, Complex.mul_re]

private theorem xiWardCap_spectral_im (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
  simp [xiSpectralPoint_eq_support, xiSpectralPointSupport, Complex.mul_im]

/-- The kernel denominators at a zero are `ρ + 1/100 ± iτ`. -/
theorem xiWardCapKernel_denominator_add (tau : ℝ) (q : XiZeroCopy) :
    (((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)) + I * xiSpectralPoint q =
      (q.1 : ℂ) + 1 / 100 + I * (tau : ℂ) := by
  rw [I_mul_xiSpectralPoint]; push_cast; ring

theorem xiWardCapKernel_denominator_sub (tau : ℝ) (q : XiZeroCopy) :
    (((51 / 100 : ℝ) : ℂ) - I * (tau : ℂ)) + I * xiSpectralPoint q =
      (q.1 : ℂ) + 1 / 100 - I * (tau : ℂ) := by
  rw [I_mul_xiSpectralPoint]; push_cast; ring

private theorem norm_sq_zero_shift (tau : ℝ) (q : XiZeroCopy) (e : ℝ) :
    ‖(q.1 : ℂ) + 1 / 100 + I * ((e * tau : ℝ) : ℂ)‖ ^ 2 =
      ((q.1 : ℂ).re + 1 / 100) ^ 2 + ((q.1 : ℂ).im + e * tau) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- **Value at a zero.**  `K_τ(ρ̂) = −4iτ / ((ρ + 1/100)² + τ²)`. -/
theorem xiWardCapKernel_xiSpectralPoint (tau : ℝ) (q : XiZeroCopy) :
    xiWardCapKernel tau (xiSpectralPoint q) =
      -4 * I * (tau : ℂ) * (((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2)⁻¹ := by
  have h1 := xiWardCapKernel_denominator_add tau q
  have h2 := xiWardCapKernel_denominator_sub tau q
  have hpos : 0 < (q.1 : ℂ).re + 1 / 100 := by linarith [xiZeroCopy_re_pos q]
  have hne : ∀ e : ℂ, e.re = 0 → (q.1 : ℂ) + 1 / 100 + e ≠ 0 := by
    intro e he h
    have := congrArg Complex.re h
    simp [he] at this
    linarith
  have hn1 : (q.1 : ℂ) + 1 / 100 + I * (tau : ℂ) ≠ 0 := hne _ (by simp)
  have hn2 : (q.1 : ℂ) + 1 / 100 - I * (tau : ℂ) ≠ 0 := by
    rw [sub_eq_add_neg]; exact hne _ (by simp)
  rw [xiWardCapKernel_eq tau (by rw [h1]; exact hn1) (by rw [h2]; exact hn2), h1, h2]
  have hprod : ((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2 =
      ((q.1 : ℂ) + 1 / 100 + I * (tau : ℂ)) * ((q.1 : ℂ) + 1 / 100 - I * (tau : ℂ)) := by
    ring_nf; rw [I_sq]; ring
  rw [hprod, mul_inv]
  ring

/-- `‖K_τ(ρ̂)‖ ≤ 4|τ| A_τ / (1 + γ²)` with `A_τ = 2 + 10⁴ (1 + 2τ²)`. -/
theorem norm_xiWardCapKernel_xiSpectralPoint_le (tau : ℝ) (q : XiZeroCopy) :
    ‖xiWardCapKernel tau (xiSpectralPoint q)‖ ≤
      4 * |tau| * (2 + 10000 * (1 + 2 * tau ^ 2)) * (1 / (1 + (0 - (q.1 : ℂ).im) ^ 2)) := by
  set A : ℝ := 2 + 10000 * (1 + 2 * tau ^ 2) with hA
  set γ : ℝ := (q.1 : ℂ).im with hγ
  set β : ℝ := (q.1 : ℂ).re with hβ
  have hA0 : 0 < A := by positivity
  have hβ0 : 0 < β := xiZeroCopy_re_pos q
  set m : ℝ := Real.sqrt ((1 + γ ^ 2) / A) with hm
  have hm0 : 0 < m := Real.sqrt_pos.mpr (by positivity)
  have hmsq : m ^ 2 = (1 + γ ^ 2) / A := Real.sq_sqrt (by positivity)
  have key : ∀ e : ℝ, e ^ 2 = 1 → m ≤ ‖(q.1 : ℂ) + 1 / 100 + I * ((e * tau : ℝ) : ℂ)‖ := by
    intro e he2
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    rw [norm_sq_zero_shift, hmsq, div_le_iff₀ hA0]
    have h1 : 1 + γ ^ 2 ≤ 1 + 2 * (γ + e * tau) ^ 2 + 2 * tau ^ 2 := by
      nlinarith [sq_nonneg (γ + 2 * e * tau), he2]
    have h2 : 1 + 2 * tau ^ 2 ≤ 10000 * (1 + 2 * tau ^ 2) * (β + 1 / 100) ^ 2 := by
      have : (1 / 100 : ℝ) ^ 2 ≤ (β + 1 / 100) ^ 2 := by
        apply pow_le_pow_left₀ (by norm_num); linarith
      nlinarith [sq_nonneg tau]
    nlinarith [sq_nonneg (γ + e * tau), sq_nonneg (β + 1 / 100)]
  have k1 := key 1 (by norm_num)
  have k2 := key (-1) (by norm_num)
  rw [show ((1 * tau : ℝ) : ℂ) = (tau : ℂ) by push_cast; ring, ← xiWardCapKernel_denominator_add] at k1
  rw [show (q.1 : ℂ) + 1 / 100 + I * ((-1 * tau : ℝ) : ℂ) = (q.1 : ℂ) + 1 / 100 - I * (tau : ℂ) by
    push_cast; ring, ← xiWardCapKernel_denominator_sub] at k2
  refine (norm_xiWardCapKernel_le tau hm0 k1 k2).trans (le_of_eq ?_)
  rw [hmsq, zero_sub, neg_sq]
  field_simp

theorem summable_norm_xiWardCapKernel_xiSpectralPoint (tau : ℝ) :
    Summable fun q : XiZeroCopy => ‖xiWardCapKernel tau (xiSpectralPoint q)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_xiWardCapKernel_xiSpectralPoint_le tau) ((summable_lorentzMassTerm 0).mul_left _)

/-- The right-zero kernel weights at level `θ`. -/
def xiWardRightZeroWeight (θ tau : ℝ) (q : XiZeroCopy) : ℂ :=
  if 1 / 2 + θ < (q.1 : ℂ).re then xiWardCapKernel tau (xiSpectralPoint q) else 0

theorem summable_xiWardRightZeroWeight (θ tau : ℝ) : Summable (xiWardRightZeroWeight θ tau) := by
  refine Summable.of_norm_bounded (summable_norm_xiWardCapKernel_xiSpectralPoint tau) fun q => ?_
  unfold xiWardRightZeroWeight
  split_ifs <;> simp

/-! ## Exhaustion -/

/-- All zero copies of height at most `T`. -/
def xiZeroCopyHeightBox (T : ℝ) : Finset XiZeroCopy :=
  xiZeroCopyClosedRectangle (((-T : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I) ((T : ℂ) + ((1 : ℝ) : ℂ) * I)

theorem mem_xiZeroCopyHeightBox {T : ℝ} (hT : 0 ≤ T) {q : XiZeroCopy} :
    q ∈ xiZeroCopyHeightBox T ↔ |(q.1 : ℂ).im| ≤ T := by
  have e1 : (((-T : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I).re = -T := by simp
  have e2 : (((-T : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I).im = -1 := by simp
  have e3 : ((T : ℂ) + ((1 : ℝ) : ℂ) * I).re = T := by simp
  have e4 : ((T : ℂ) + ((1 : ℝ) : ℂ) * I).im = 1 := by simp
  rw [xiZeroCopyHeightBox, mem_xiZeroCopyClosedRectangle, Complex.mem_reProdIm,
    xiWardCap_spectral_re, xiWardCap_spectral_im, e1, e2, e3, e4,
    uIcc_of_le (by linarith), uIcc_of_le (by norm_num), mem_Icc, mem_Icc, abs_le]
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  constructor
  · rintro ⟨⟨a, b⟩, -⟩; exact ⟨a, b⟩
  · rintro ⟨a, b⟩; exact ⟨⟨a, b⟩, ⟨by linarith, by linarith⟩⟩

theorem mem_xiZeroCopyClosedRectangle_cap {θ T : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) (hT : 1 ≤ T)
    {q : XiZeroCopy} :
    q ∈ xiZeroCopyClosedRectangle (xiWardCapCornerLow T) (xiWardCapCornerHigh θ T) ↔
      |(q.1 : ℂ).im| ≤ T ∧ 1 / 2 + θ ≤ (q.1 : ℂ).re := by
  rw [mem_xiZeroCopyClosedRectangle, Complex.mem_reProdIm, xiWardCap_spectral_re,
    xiWardCap_spectral_im]
  simp only [xiWardCapCornerLow_re, xiWardCapCornerHigh_re, xiWardCapCornerLow_im,
    xiWardCapCornerHigh_im]
  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith), mem_Icc, mem_Icc, abs_le]
  have h1 := xiZeroCopy_re_lt_one q
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨a, b⟩, by linarith⟩
  · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨a, b⟩, by linarith, by linarith⟩

/-- On a cap rectangle the enclosed kernel sum is the right-zero weight summed over the height box. -/
theorem sum_cap_rectangle_eq_heightBox {θ T tau : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) (hT : 1 ≤ T)
    (hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 + θ) :
    ∑ q ∈ xiZeroCopyClosedRectangle (xiWardCapCornerLow T) (xiWardCapCornerHigh θ T),
        xiWardCapKernel tau (xiSpectralPoint q) =
      ∑ q ∈ xiZeroCopyHeightBox T, xiWardRightZeroWeight θ tau q := by
  classical
  have hset : xiZeroCopyClosedRectangle (xiWardCapCornerLow T) (xiWardCapCornerHigh θ T) =
      (xiZeroCopyHeightBox T).filter (fun q => 1 / 2 + θ < (q.1 : ℂ).re) := by
    ext q
    rw [Finset.mem_filter, mem_xiZeroCopyClosedRectangle_cap hθ0 hθ1 hT,
      mem_xiZeroCopyHeightBox (by linarith)]
    constructor
    · rintro ⟨a, b⟩; exact ⟨a, lt_of_le_of_ne b (fun h => hline q h.symm)⟩
    · rintro ⟨a, b⟩; exact ⟨a, b.le⟩
  rw [hset, Finset.sum_filter]
  rfl

/-! ## The edge errors vanish along the good heights -/

private theorem tendsto_log_add_div_add (a b : ℝ) :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + a) / ((n : ℝ) + b)) atTop (nhds 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (b - a) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop a tendsto_natCast_atTop_atTop)
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, pow_one, one_mul]
  congr 1; ring

private theorem tendsto_affine_log_div (c₁ c₂ : ℝ) :
    Tendsto (fun n : ℕ => (c₁ * Real.log ((n : ℝ) + 13) + c₂) / ((n : ℝ) + 8)) atTop (nhds 0) := by
  have h1 := (tendsto_log_add_div_add 13 8).const_mul c₁
  have h2 : Tendsto (fun n : ℕ => c₂ / ((n : ℝ) + 8)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 8 tendsto_natCast_atTop_atTop)
  rw [show (0 : ℝ) = c₁ * 0 + 0 by ring]
  refine (h1.add h2).congr fun n => ?_
  rw [add_div, mul_div_assoc]

theorem xiWardEdgeLog_div_le {n : ℕ} {T : ℝ} (hge : (n : ℝ) + 8 ≤ T) (hle : T ≤ n + 9) :
    xiWardEdgeLog T / T ≤ (1 * Real.log ((n : ℝ) + 13) + |xiLineTwoLogDerivConstant|) /
      ((n : ℝ) + 8) := by
  have hT0 : 0 < T := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hn0 : (0 : ℝ) < n + 8 := by positivity
  unfold xiWardEdgeLog
  have hlog : Real.log (T + 4) ≤ Real.log ((n : ℝ) + 13) :=
    Real.log_le_log (by linarith) (by linarith)
  have hnum : 0 ≤ |xiLineTwoLogDerivConstant| + Real.log ((n : ℝ) + 13) :=
    add_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  calc (|xiLineTwoLogDerivConstant| + Real.log (T + 4)) / T
      ≤ (|xiLineTwoLogDerivConstant| + Real.log ((n : ℝ) + 13)) / T := by gcongr
    _ ≤ (|xiLineTwoLogDerivConstant| + Real.log ((n : ℝ) + 13)) / ((n : ℝ) + 8) :=
        div_le_div_of_nonneg_left hnum hn0 hge
    _ = _ := by ring

theorem xiWardGoodHeightBound_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ xiWardGoodHeightBound n := by
  unfold xiWardGoodHeightBound
  have : 0 ≤ Real.log ((n : ℝ) + 1 / 2) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  have hwl : 0 ≤ windowLogConst := windowLogConst_nonneg
  positivity

theorem xiWardGoodHeightBound_le (n : ℕ) :
    xiWardGoodHeightBound (n + 8) ≤
      (3 * windowLogConst + 320 * (4 * Real.sqrt 2 * (4 * Real.sqrt 3))) *
          Real.log ((n : ℝ) + 13) +
        4 * (80 * Real.log 180 + smallHeightCount) * (4 * Real.sqrt 2 * (4 * Real.sqrt 3)) := by
  unfold xiWardGoodHeightBound
  set k : ℝ := 4 * Real.sqrt 2 * (4 * Real.sqrt 3) with hk
  have hk0 : 0 ≤ k := by positivity
  have hcast : ((n + 8 : ℕ) : ℝ) = (n : ℝ) + 8 := by push_cast; ring
  rw [hcast]
  have hcard := card_windowCopySet_le (t₀ := (n : ℝ) + 8 + 1 / 2) (by
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl1 : Real.log ((n : ℝ) + 8 + 1 / 2) ≤ Real.log ((n : ℝ) + 13) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl2 : Real.log (180 * ((n : ℝ) + 8 + 1 / 2 + 2)) ≤ Real.log 180 + Real.log ((n : ℝ) + 13) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_le_log (show (0 : ℝ) < (n : ℝ) + 8 + 1 / 2 + 2 by linarith)
      (show (n : ℝ) + 8 + 1 / 2 + 2 ≤ (n : ℝ) + 13 by linarith)]
  have hwl : 0 ≤ windowLogConst := windowLogConst_nonneg
  have hcard' : ((windowCopySet ((n : ℝ) + 8 + 1 / 2)).card : ℝ) ≤
      2 * (80 * (Real.log 180 + Real.log ((n : ℝ) + 13)) + smallHeightCount) := by
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hcard' hk0, mul_le_mul_of_nonneg_left hl1 hwl]

/-! ## The global cap -/

/-- **Evaluation at one level.**  If no zero lies on the cap line and the global cap integrand is
integrable, the global cap is `−2πi` times the kernel summed over the zeros right of the line. -/
theorem xiWardGlobalCap_eq_rightZeroSum_of {s tau : ℝ}
    (hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 + xiWardTransverseLevel s)
    (hint : Integrable fun x : ℝ => xiWardSchwarzCapDifference tau s x *
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)) :
    ∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
        continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) =
      -(2 * Real.pi * I) * ∑' q : XiZeroCopy, xiWardRightZeroWeight (xiWardTransverseLevel s) tau q := by
  set θ := xiWardTransverseLevel s with hθ
  have hθ0 : 0 < θ := (xiWardTransverseLevel_mem_Ioo s).1
  have hθ1 : θ < 1 / 2 := (xiWardTransverseLevel_mem_Ioo s).2
  set G : ℂ := ∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
    continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) with hGdef
  set Sf : ℂ := ∑' q : XiZeroCopy, xiWardRightZeroWeight θ tau q with hSf
  -- good heights
  have hgood : ∀ n : ℕ, ∃ T ∈ Icc ((n + 8 : ℕ) : ℝ) ((n + 8 : ℕ) + 1), T ∉ xiZeroHeightSet ∧
      ∫⁻ y in Icc (-(3 / 2) : ℝ) 0, ‖logDeriv xi (xiWardStripPoint T y)‖ₑ ≤
        ENNReal.ofReal (xiWardGoodHeightBound (n + 8)) := fun n =>
    exists_good_xiWardHeight (by omega)
  choose T hTI hTgood hTint using hgood
  have hTge : ∀ n : ℕ, (n : ℝ) + 8 ≤ T n := fun n => by
    have := (hTI n).1; push_cast at this; linarith
  have hTle : ∀ n : ℕ, T n ≤ (n : ℝ) + 9 := fun n => by
    have := (hTI n).2; push_cast at this; linarith
  have hT2 : ∀ n : ℕ, 2 ≤ T n := fun n => by linarith [hTge n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hTtop : Tendsto T atTop atTop :=
    tendsto_atTop_mono hTge (tendsto_atTop_add_const_right atTop 8 tendsto_natCast_atTop_atTop)
  have hTmono : Monotone T := monotone_nat_of_le_succ fun n => by
    have h1 := hTle n; have h2 := hTge (n + 1); push_cast at h2; linarith
  -- the finite caps converge to the global cap
  have hcap : Tendsto (fun n => xiWardSchwarzCapFactorIntegral tau s (T n)) atTop (nhds G) :=
    intervalIntegral_tendsto_integral hint (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  -- the enclosed zero sums converge to the right-zero sum
  have hboxmono : Monotone fun n => xiZeroCopyHeightBox (T n) := by
    intro a b hab q hq
    rw [mem_xiZeroCopyHeightBox (by linarith [hT2 a])] at hq
    rw [mem_xiZeroCopyHeightBox (by linarith [hT2 b])]
    exact hq.trans (hTmono hab)
  have hboxcover : ∀ q : XiZeroCopy, ∃ n, q ∈ xiZeroCopyHeightBox (T n) := by
    intro q
    refine ⟨⌈|(q.1 : ℂ).im|⌉₊, ?_⟩
    rw [mem_xiZeroCopyHeightBox (by linarith [hT2 ⌈|(q.1 : ℂ).im|⌉₊])]
    linarith [Nat.le_ceil |(q.1 : ℂ).im|, hTge ⌈|(q.1 : ℂ).im|⌉₊]
  have hS : Tendsto (fun n => ∑ q ∈ xiZeroCopyHeightBox (T n), xiWardRightZeroWeight θ tau q)
      atTop (nhds Sf) :=
    (summable_xiWardRightZeroWeight θ tau).hasSum.comp
      (tendsto_atTop_finset_of_monotone hboxmono hboxcover)
  -- the edge error
  set E : ℕ → ℂ := fun n => xiWardSchwarzCapFactorIntegral tau s (T n) +
    2 * Real.pi * I * ∑ q ∈ xiZeroCopyHeightBox (T n), xiWardRightZeroWeight θ tau q with hE
  set ε : ℕ → ℝ := fun n => 40 * |tau| * (xiWardEdgeLog (T n) / T n) +
    32 * |tau| * (xiWardGoodHeightBound (n + 8) / (T n) ^ 2) with hε
  have hEbound : ∀ n : ℕ, 2 * |tau| ≤ T n → ‖E n‖ ≤ ε n := by
    intro n hτn
    set Tn := T n
    have hTn0 : 0 < Tn := by linarith [hT2 n]
    have hrect := rectIntegral_xiWardCapKernel_eq (tau := tau) hθ0 hθ1 (hT2 n) (hTgood n) hline
    rw [sum_cap_rectangle_eq_heightBox hθ0 hθ1 (by linarith [hT2 n]) hline] at hrect
    unfold rectIntegral at hrect
    simp only [xiWardCapCornerLow_re, xiWardCapCornerLow_im, xiWardCapCornerHigh_re,
      xiWardCapCornerHigh_im] at hrect
    have htop : (∫ x in (-Tn)..Tn, xiWardCapKernel tau ((x : ℂ) + ((-θ : ℝ) : ℂ) * I) *
        continuedPrimeArchSourceRelativeTrace ((x : ℂ) + ((-θ : ℝ) : ℂ) * I)) =
        xiWardSchwarzCapFactorIntegral tau s Tn := by
      unfold xiWardSchwarzCapFactorIntegral
      refine intervalIntegral.integral_congr fun x _ => ?_
      have hpt : (x : ℂ) + ((-θ : ℝ) : ℂ) * I = xiWardLowerCapPoint s x := by
        unfold xiWardLowerCapPoint; rw [hθ]; push_cast; ring
      simp only [hpt, xiWardSchwarzCapDifference_eq_xiWardCapKernel]
    have hcasts : ∀ (a : ℝ), ((-a : ℝ) : ℂ) = -(a : ℂ) := fun a => by push_cast; ring
    set bot := ∫ x in (-Tn)..Tn, xiWardCapKernel tau ((x : ℂ) + ((-Tn : ℝ) : ℂ) * I) *
        continuedPrimeArchSourceRelativeTrace ((x : ℂ) + ((-Tn : ℝ) : ℂ) * I) with hbot
    set rgt := ∫ y in (-Tn)..(-θ), xiWardCapKernel tau ((Tn : ℂ) + (y : ℂ) * I) *
        continuedPrimeArchSourceRelativeTrace ((Tn : ℂ) + (y : ℂ) * I) with hrgt
    set lft := ∫ y in (-Tn)..(-θ), xiWardCapKernel tau (((-Tn : ℝ) : ℂ) + (y : ℂ) * I) *
        continuedPrimeArchSourceRelativeTrace (((-Tn : ℝ) : ℂ) + (y : ℂ) * I) with hlft
    have hEeq : E n = bot + I * rgt - I * lft := by
      simp only [hE]
      rw [← htop]
      simp only [smul_eq_mul] at hrect
      rw [← hrect]
      ring
    have hB0 : 0 ≤ xiWardGoodHeightBound (n + 8) := xiWardGoodHeightBound_nonneg (by omega)
    have hb := norm_xiWardCapBottomEdge_le (tau := tau) (hT2 n)
    have hr := norm_xiWardCapVerticalEdge_le (R := Tn) (hT2 n) hτn hθ0 hθ1 (abs_of_pos hTn0)
      (hTgood n) hB0 (hTint n)
    have hl := norm_xiWardCapVerticalEdge_le (R := -Tn) (hT2 n) hτn hθ0 hθ1
      (by rw [abs_neg, abs_of_pos hTn0]) (hTgood n) hB0 (hTint n)
    rw [hEeq]
    have hIr : ‖I * rgt‖ = ‖rgt‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    have hIl : ‖I * lft‖ = ‖lft‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    calc ‖bot + I * rgt - I * lft‖ ≤ ‖bot‖ + ‖rgt‖ + ‖lft‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [hIl]
          linarith [norm_add_le bot (I * rgt)]
      _ ≤ 4 * |tau| / Tn ^ 2 * xiWardEdgeLog Tn * (2 * Tn) +
          16 * |tau| / Tn ^ 2 * (Tn * xiWardEdgeLog Tn + xiWardGoodHeightBound (n + 8)) +
          16 * |tau| / Tn ^ 2 * (Tn * xiWardEdgeLog Tn + xiWardGoodHeightBound (n + 8)) := by
          gcongr
      _ = 40 * |tau| * (xiWardEdgeLog Tn / Tn) +
          32 * |tau| * (xiWardGoodHeightBound (n + 8) / Tn ^ 2) := by
          field_simp
          ring
      _ = ε n := rfl
  have hεlim : Tendsto ε atTop (nhds 0) := by
    have ha : Tendsto (fun n : ℕ => xiWardEdgeLog (T n) / T n) atTop (nhds 0) :=
      squeeze_zero (fun n => div_nonneg (xiWardEdgeLog_nonneg (by linarith [hT2 n]))
        (by linarith [hT2 n])) (fun n => xiWardEdgeLog_div_le (hTge n) (hTle n))
        (tendsto_affine_log_div 1 |xiLineTwoLogDerivConstant|)
    have hb : Tendsto (fun n : ℕ => xiWardGoodHeightBound (n + 8) / (T n) ^ 2) atTop (nhds 0) := by
      refine squeeze_zero (fun n => div_nonneg (xiWardGoodHeightBound_nonneg (by omega))
        (by positivity)) (fun n => ?_)
        (tendsto_affine_log_div (3 * windowLogConst + 320 * (4 * Real.sqrt 2 * (4 * Real.sqrt 3)))
          (4 * (80 * Real.log 180 + smallHeightCount) * (4 * Real.sqrt 2 * (4 * Real.sqrt 3))))
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hB0 : 0 ≤ xiWardGoodHeightBound (n + 8) := xiWardGoodHeightBound_nonneg (by omega)
      have hsq : (n : ℝ) + 8 ≤ (T n) ^ 2 := by nlinarith [hTge n]
      calc xiWardGoodHeightBound (n + 8) / (T n) ^ 2
          ≤ xiWardGoodHeightBound (n + 8) / ((n : ℝ) + 8) :=
            div_le_div_of_nonneg_left hB0 (by positivity) hsq
        _ ≤ _ := div_le_div_of_nonneg_right (xiWardGoodHeightBound_le n) (by positivity)
    have := (ha.const_mul (40 * |tau|)).add (hb.const_mul (32 * |tau|))
    simpa [hε] using this
  have hElim : Tendsto E atTop (nhds 0) := by
    have hev : ∀ᶠ n in atTop, ‖E n‖ ≤ ε n := by
      filter_upwards [hTtop.eventually_ge_atTop (2 * |tau|)] with n hn
      exact hEbound n hn
    exact squeeze_zero_norm' hev hεlim
  have hsum : Tendsto E atTop (nhds (G + 2 * Real.pi * I * Sf)) :=
    hcap.add (hS.const_mul _)
  have huniq := tendsto_nhds_unique hsum hElim
  linear_combination huniq

/-- For almost every level no zero lies on the cap line. -/
theorem ae_forall_re_ne_capLine :
    ∀ᵐ s : ℝ ∂(volume : Measure ℝ), ∀ q : XiZeroCopy,
      (q.1 : ℂ).re ≠ 1 / 2 + xiWardTransverseLevel s := by
  apply ae_comp_xiWardTransverseLevel (P := fun a => ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 + a)
  have hcount : (range fun q : XiZeroCopy => (q.1 : ℂ).re - 1 / 2).Countable := countable_range _
  have hnull := hcount.measure_zero (volume : Measure ℝ)
  have hae : ∀ᵐ a ∂(volume : Measure ℝ), a ∉ range fun q : XiZeroCopy => (q.1 : ℂ).re - 1 / 2 := by
    rw [ae_iff]
    exact measure_mono_null (fun a ha => not_not.mp ha) hnull
  filter_upwards [hae] with a ha _ q hq
  exact ha ⟨q, by simp only; linarith⟩

/-- The level-free zero weight `1 / ((ρ + 1/100)² + τ²)` of a zero right of the line. -/
def xiWardRightZeroStieltjes (θ tau : ℝ) (q : XiZeroCopy) : ℂ :=
  if 1 / 2 + θ < (q.1 : ℂ).re then (((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2)⁻¹ else 0

theorem xiWardRightZeroWeight_eq (θ tau : ℝ) (q : XiZeroCopy) :
    xiWardRightZeroWeight θ tau q = -4 * I * (tau : ℂ) * xiWardRightZeroStieltjes θ tau q := by
  unfold xiWardRightZeroWeight xiWardRightZeroStieltjes
  split_ifs
  · exact xiWardCapKernel_xiSpectralPoint tau q
  · ring

/-- **The global Ward cap is the Stieltjes transform of the zeros right of the cap line.**  For
almost every canonical level and every `τ`,
`∫_ℝ K_τ(x) T(x − θ i) dx = −8π τ Σ_{Re ρ > ½ + θ} 1 / ((ρ + 1/100)² + τ²)`. -/
theorem ae_forall_xiWardGlobalCap_eq_rightZeroSum :
    ∀ᵐ s : ℝ ∂(volume : Measure ℝ), ∀ tau : ℝ,
      ∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) =
        -(8 * Real.pi * tau : ℂ) *
          ∑' q : XiZeroCopy, xiWardRightZeroStieltjes (xiWardTransverseLevel s) tau q := by
  filter_upwards [ae_forall_re_ne_capLine, ae_forall_integrable_xiWardSchwarzCapFactor] with
    s hline hint tau
  rw [xiWardGlobalCap_eq_rightZeroSum_of hline (hint tau)]
  simp only [xiWardRightZeroWeight_eq]
  rw [tsum_mul_left]
  ring_nf
  rw [I_sq]
  ring

/-! ## Sign of the global cap -/

theorem summable_xiWardRightZeroStieltjes (θ : ℝ) {tau : ℝ} (hτ : tau ≠ 0) :
    Summable (xiWardRightZeroStieltjes θ tau) := by
  have h := (summable_xiWardRightZeroWeight θ tau).mul_left (-4 * I * (tau : ℂ))⁻¹
  refine h.congr fun q => ?_
  rw [xiWardRightZeroWeight_eq, ← mul_assoc, inv_mul_cancel₀, one_mul]
  have : (tau : ℂ) ≠ 0 := by exact_mod_cast hτ
  simp [this, Complex.I_ne_zero]

/-- A zero right of a cap line has squared height at least `2365/16`. -/
private theorem im_sq_ge_of_right {θ : ℝ} (hθ : 0 < θ) {q : XiZeroCopy}
    (hq : 1 / 2 + θ < (q.1 : ℂ).re) : 2365 / 16 ≤ (q.1 : ℂ).im ^ 2 := by
  by_contra h
  push Not at h
  have := xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q h
  linarith

/-- For `0 < τ ≤ 12` every right zero contributes a negative real part. -/
theorem re_xiWardRightZeroStieltjes_neg {θ tau : ℝ} (hθ : 0 < θ) (hτ : tau ≤ 12) (hτ0 : 0 ≤ tau)
    {q : XiZeroCopy} (hq : 1 / 2 + θ < (q.1 : ℂ).re) :
    (xiWardRightZeroStieltjes θ tau q).re < 0 := by
  unfold xiWardRightZeroStieltjes
  rw [if_pos hq]
  set z : ℂ := ((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2 with hz
  have hγ := im_sq_ge_of_right hθ hq
  have hβ := xiZeroCopy_re_lt_one q
  have hβ0 := xiZeroCopy_re_pos q
  have hre : z.re = ((q.1 : ℂ).re + 1 / 100) ^ 2 - (q.1 : ℂ).im ^ 2 + tau ^ 2 := by
    simp only [hz, Complex.add_re, sq, Complex.mul_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
  have hzre : z.re < 0 := by
    rw [hre]
    nlinarith
  have hnz : 0 < Complex.normSq z := by
    rw [Complex.normSq_pos]; intro h; rw [h, Complex.zero_re] at hzre; exact lt_irrefl 0 hzre
  rw [Complex.inv_re]
  exact div_neg_of_neg_of_pos hzre hnz

theorem re_xiWardRightZeroStieltjes_nonpos {θ tau : ℝ} (hθ : 0 < θ) (hτ : tau ≤ 12) (hτ0 : 0 ≤ tau)
    (q : XiZeroCopy) : (xiWardRightZeroStieltjes θ tau q).re ≤ 0 := by
  by_cases hq : 1 / 2 + θ < (q.1 : ℂ).re
  · exact (re_xiWardRightZeroStieltjes_neg hθ hτ hτ0 hq).le
  · unfold xiWardRightZeroStieltjes; rw [if_neg hq]; simp

/-- **One-sided global caps.**  For almost every level and every `0 < τ ≤ 12` the global cap is
nonnegative, and it vanishes exactly when no zero lies to the right of the cap line. -/
theorem ae_forall_xiWardGlobalCap_re_nonneg :
    ∀ᵐ s : ℝ ∂(volume : Measure ℝ), ∀ tau ∈ Ioc (0 : ℝ) 12,
      0 ≤ (∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re ∧
      ((∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re = 0 ↔
        ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + xiWardTransverseLevel s) := by
  filter_upwards [ae_forall_xiWardGlobalCap_eq_rightZeroSum] with s hs tau hτ
  set θ := xiWardTransverseLevel s
  have hθ : 0 < θ := (xiWardTransverseLevel_mem_Ioo s).1
  have hsum := summable_xiWardRightZeroStieltjes θ hτ.1.ne'
  have hsumre : Summable fun q => -(xiWardRightZeroStieltjes θ tau q).re :=
    (Complex.reCLM.summable hsum).neg
  have hnn : ∀ q, 0 ≤ -(xiWardRightZeroStieltjes θ tau q).re := fun q =>
    neg_nonneg.mpr (re_xiWardRightZeroStieltjes_nonpos hθ hτ.2 hτ.1.le q)
  have hre : (∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re =
      8 * Real.pi * tau * ∑' q, -(xiWardRightZeroStieltjes θ tau q).re := by
    rw [hs tau, show -(8 * Real.pi * tau : ℂ) = ((-(8 * Real.pi * tau) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.re_tsum hsum, tsum_neg]
    ring
  have hpos : 0 < 8 * Real.pi * tau := by have := hτ.1; positivity
  rw [hre]
  refine ⟨mul_nonneg hpos.le (tsum_nonneg hnn), ⟨fun h0 => ?_, fun hall => ?_⟩⟩
  · intro q
    by_contra hq
    push Not at hq
    have := hsumre.tsum_pos hnn q (neg_pos.mpr (re_xiWardRightZeroStieltjes_neg hθ hτ.2 hτ.1.le hq))
    have : 0 < 8 * Real.pi * tau * ∑' q, -(xiWardRightZeroStieltjes θ tau q).re :=
      mul_pos hpos this
    linarith
  · have hz : ∀ q, -(xiWardRightZeroStieltjes θ tau q).re = 0 := by
      intro q
      unfold xiWardRightZeroStieltjes
      rw [if_neg (not_lt.mpr (hall q))]
      simp
    simp [hz]

theorem xiZeroCopy_re_eq_half_of_forall_le (h : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2)
    (q : XiZeroCopy) :
    (q.1 : ℂ).re = 1 / 2 := by
  have h1 := h q
  have h2 := h (xiZeroCopyReflectEquiv q)
  rw [xiZeroCopyReflectEquiv_coe, Complex.sub_re, Complex.one_re] at h2
  linarith

/-- **Vanishing of the global caps is the Riemann hypothesis.**  The global caps vanish for almost
every level and every `τ` exactly when every zero of `ξ` lies on the critical line.  Already the
single height `τ = 1` decides: a zero right of the line makes the cap strictly positive on a set of
levels of infinite measure. -/
theorem ae_xiWardGlobalCap_eq_zero_iff :
    (∀ᵐ s : ℝ ∂(volume : Measure ℝ), ∀ tau : ℝ,
      ∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) = 0) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    suffices hle : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 from
      xiZeroCopy_re_eq_half_of_forall_le hle
    intro q₀
    by_contra hq₀
    push Not at hq₀
    set a₀ : ℝ := (q₀.1 : ℂ).re - 1 / 2 with ha₀
    have ha₀mem : a₀ ∈ Ioo (0 : ℝ) (1 / 2) :=
      ⟨by linarith, by linarith [xiZeroCopy_re_lt_one q₀]⟩
    set s₀ : ℝ := xiWardTransverseCoordinate a₀ with hs₀
    have hboth := h.and ae_forall_xiWardGlobalCap_re_nonneg
    obtain ⟨s, hs, hzero, hsign⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (s := Iio s₀) (by rw [Real.volume_Iio]; exact ENNReal.top_ne_zero) (ae_restrict_of_ae hboth)
    have hlev : xiWardTransverseLevel s < a₀ := by
      have := xiWardTransverseLevel_strictMono hs
      rwa [hs₀, xiWardTransverseLevel_coordinate ha₀mem] at this
    have h1 := (hsign 1 ⟨one_pos, by norm_num⟩).2.mp (by rw [hzero 1, Complex.zero_re])
    have := h1 q₀
    linarith
  · intro hall
    filter_upwards [ae_forall_xiWardGlobalCap_eq_rightZeroSum] with s hs tau
    rw [hs tau]
    have hθ : 0 < xiWardTransverseLevel s := (xiWardTransverseLevel_mem_Ioo s).1
    have hz : ∀ q : XiZeroCopy, xiWardRightZeroStieltjes (xiWardTransverseLevel s) tau q = 0 := by
      intro q
      unfold xiWardRightZeroStieltjes
      rw [if_neg (by rw [hall q]; linarith)]
    simp [hz]

end

end RHTower
