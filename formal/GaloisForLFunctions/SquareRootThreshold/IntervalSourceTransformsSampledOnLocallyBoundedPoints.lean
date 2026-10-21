import GaloisForLFunctions.RHTower.WindowTransformSamplingParseval
import GaloisForLFunctions.RHTower.CCMParityQuartetEvenFloor

/-!
# Transforms of interval sources sampled on locally bounded point sets

Let `f` be a continuous function vanishing off `[−a, a]` and `Φ(z) = ∫ f(u) e^{izu} du` its entire
transform.  For a family of points `z_q = x_q + i y_q` whose heights `x_q` are uniformly bounded
in number on unit windows (at most `M` in any interval of length one) and whose depths satisfy
`|y_q| ≤ σ`, the sampled energy is controlled by the source energy:

`Σ_q |Φ(z_q)|² ≤ M (2a + 2π) e^{2π} e^{2σa} ∫ |f|²`
(`sum_norm_sq_testTransform_le_of_locallyBounded`).

**Proof.**  Put `L = 2a + 2π` and `h = 2π/L ≤ 1`.  Every point is `z = g + w` with
`g = ⌊x/h⌋ h` on the grid `hℤ` and `|w| ≤ h + σ`.  Expanding `e^{iwu}` in its power series gives
`Φ(z) = Σ_j (iw)^j/j! · Φ_j(g)`, where `Φ_j` is the transform of the moment source `u^j f(u)`
(`testTransform_add_eq_tsum_momentSource`).  Weighted Cauchy–Schwarz with the weights
`((h+σ)a)^j/j!` (`sq_tsum_le_tsum_mul_tsum_div`) bounds `|Φ(z)|²` by
`e^{(h+σ)a} Σ_j (h+σ)^j/(j! a^j) |Φ_j(g)|²`.  Each grid cell carries at most `M` points
(`card_filter_gridIndex_le`), and the grid Parseval identity on the window `[−L/2, L/2]`
(`hasSum_norm_sq_testTransform_grid`) gives `Σ_k |Φ_j(kh)|² = L ∫ |u^j f|² ≤ L a^{2j} ∫ |f|²`.
Summing the factorial series once more yields `e^{2(h+σ)a} M L ∫|f|²`, and `ha ≤ π`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open GaloisForLFunctions.HTGeometry _root_.RHTower _root_.RHTower.CCMParityQuartet

namespace GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-! ### 1. Moment sources and the power series of the transform -/

/-- The `j`-th moment source `u ↦ u^j f(u)`. -/
def momentSource (f : ℝ → ℂ) (j : ℕ) : ℝ → ℂ := fun u => (u : ℂ) ^ j * f u

theorem intervalSource_momentSource {a : ℝ} {f : ℝ → ℂ} (hf : IntervalSource a f) (j : ℕ) :
    IntervalSource a (momentSource f j) where
  continuous := (Complex.continuous_ofReal.pow j).mul hf.continuous
  hasCompactSupport := hf.hasCompactSupport.mul_left
  vanish := fun x hx => by simp [momentSource, hf.vanish x hx]

theorem norm_momentSource_le {a : ℝ} {f : ℝ → ℂ} (hf : IntervalSource a f) (j : ℕ) (u : ℝ) :
    ‖momentSource f j u‖ ≤ a ^ j * ‖f u‖ := by
  by_cases hu : u ∈ Icc (-a) a
  · have hua : |u| ≤ a := abs_le.mpr ⟨hu.1, hu.2⟩
    simp only [momentSource, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hua j) (norm_nonneg _)
  · simp [momentSource, hf.vanish u hu]

/-- The transform of a moment source at a real point is bounded by `a^j ∫ |f|`. -/
theorem norm_testTransform_momentSource_le {a : ℝ} {f : ℝ → ℂ} (hf : IntervalSource a f)
    (j : ℕ) (c : ℝ) :
    ‖testTransform (momentSource f j) c‖ ≤ a ^ j * ∫ u, ‖f u‖ := by
  unfold testTransform
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (Eventually.of_forall fun u => ?_)
  · exact (hf.continuous.norm.integrable_of_hasCompactSupport hf.hasCompactSupport.norm).const_mul _
  · show ‖momentSource f j u * cexp (I * (c : ℂ) * (u : ℂ))‖ ≤ a ^ j * ‖f u‖
    rw [norm_mul, norm_exp_I_mul]
    simp only [Complex.ofReal_im, mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact norm_momentSource_le hf j u

/-- **The power series of the transform.** At `c + w` with `c` real, the transform is the
exponential series of the moment transforms at `c`:
`Φ(c + w) = Σ_j (iw)^j/j! · Φ_j(c)`. -/
theorem testTransform_add_eq_tsum_momentSource {a : ℝ} {f : ℝ → ℂ}
    (hf : IntervalSource a f) (c : ℝ) (w : ℂ) :
    testTransform f ((c : ℂ) + w) =
      ∑' j : ℕ, (I * w) ^ j / (j.factorial : ℂ) * testTransform (momentSource f j) c := by
  set F : ℕ → ℝ → ℂ := fun j u =>
    (I * w) ^ j / (j.factorial : ℂ) * (momentSource f j u * cexp (I * (c : ℂ) * (u : ℂ))) with hF
  have hFint : ∀ j, Integrable (F j) := fun j =>
    (integrable_testTransform_integrand (intervalSource_momentSource hf j).continuous
      (intervalSource_momentSource hf j).hasCompactSupport (c : ℂ)).const_mul _
  have hfint : Integrable fun u => ‖f u‖ :=
    hf.continuous.norm.integrable_of_hasCompactSupport hf.hasCompactSupport.norm
  have hFnorm : ∀ j u, ‖F j u‖ ≤ (‖w‖ * a) ^ j / j.factorial * ‖f u‖ := by
    intro j u
    have h1 : ‖(I * w) ^ j / (j.factorial : ℂ)‖ = ‖w‖ ^ j / j.factorial := by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
    have h2 : ‖cexp (I * (c : ℂ) * (u : ℂ))‖ = 1 := by
      rw [norm_exp_I_mul]; simp
    simp only [hF]
    rw [norm_mul, norm_mul, h1, h2, mul_one, mul_pow]
    calc ‖w‖ ^ j / j.factorial * ‖momentSource f j u‖
        ≤ ‖w‖ ^ j / j.factorial * (a ^ j * ‖f u‖) := by
          gcongr
          exact norm_momentSource_le hf j u
      _ = ‖w‖ ^ j * a ^ j / j.factorial * ‖f u‖ := by ring
  have hFnormInt : ∀ j, ∫ u, ‖F j u‖ ≤ (‖w‖ * a) ^ j / j.factorial * ∫ u, ‖f u‖ := by
    intro j
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (hfint.const_mul _) (Eventually.of_forall fun u => hFnorm j u)
  have hsum : Summable fun j => ∫ u, ‖F j u‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _) hFnormInt
      ((Real.summable_pow_div_factorial (‖w‖ * a)).mul_right _)
  have hexp : ∀ u : ℝ, cexp (I * ((c : ℂ) + w) * (u : ℂ)) =
      cexp (I * (c : ℂ) * (u : ℂ)) * ∑' j : ℕ, (I * w * (u : ℂ)) ^ j / (j.factorial : ℂ) := by
    intro u
    rw [show I * ((c : ℂ) + w) * (u : ℂ) = I * (c : ℂ) * (u : ℂ) + I * w * (u : ℂ) by ring,
      Complex.exp_add]
    congr 1
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  calc testTransform f ((c : ℂ) + w) = ∫ u, ∑' j, F j u := by
        unfold testTransform
        congr 1
        funext u
        rw [hexp u, ← tsum_mul_left, ← tsum_mul_left]
        congr 1
        funext j
        simp only [hF, momentSource]
        rw [mul_pow]
        ring
    _ = ∑' j, ∫ u, F j u := (integral_tsum_of_summable_integral_norm hFint hsum).symm
    _ = _ := by
        congr 1
        funext j
        simp only [hF]
        rw [integral_const_mul]
        rfl

/-- The transform at `c + w` is bounded by the factorial series of the moment transforms. -/
theorem norm_testTransform_le_tsum_momentSource {a : ℝ} {f : ℝ → ℂ}
    (hf : IntervalSource a f) (c : ℝ) {w : ℂ} {r : ℝ} (hw : ‖w‖ ≤ r) :
    ‖testTransform f ((c : ℂ) + w)‖ ≤
      ∑' j : ℕ, r ^ j / j.factorial * ‖testTransform (momentSource f j) c‖ := by
  have hterm : ∀ j, ‖(I * w) ^ j / (j.factorial : ℂ) * testTransform (momentSource f j) c‖ ≤
      r ^ j / j.factorial * ‖testTransform (momentSource f j) c‖ := by
    intro j
    rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
    gcongr
  have hsumm : Summable fun j => r ^ j / j.factorial * ‖testTransform (momentSource f j) c‖ := by
    have hr : 0 ≤ r := (norm_nonneg _).trans hw
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      ((Real.summable_pow_div_factorial (r * a)).mul_right (∫ u, ‖f u‖))
    calc r ^ j / j.factorial * ‖testTransform (momentSource f j) c‖
        ≤ r ^ j / j.factorial * (a ^ j * ∫ u, ‖f u‖) := by
          gcongr
          exact norm_testTransform_momentSource_le hf j c
      _ = (r * a) ^ j / j.factorial * ∫ u, ‖f u‖ := by rw [mul_pow]; ring
  rw [testTransform_add_eq_tsum_momentSource hf c w]
  refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum hterm ?_ hsumm)
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumm
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumm

/-! ### 2. The grid: window length `2a + 2π`, step `2π/(2a + 2π)`, Parseval -/

/-- The window length `L = 2a + 2π`. -/
def windowLength (a : ℝ) : ℝ := 2 * a + 2 * π

/-- The grid step `h = 2π/L`. -/
def gridStep (a : ℝ) : ℝ := 2 * π / windowLength a

theorem windowLength_pos {a : ℝ} (ha : 0 < a) : 0 < windowLength a := by
  unfold windowLength; positivity

theorem gridStep_pos {a : ℝ} (ha : 0 < a) : 0 < gridStep a := by
  unfold gridStep
  exact div_pos (by positivity) (windowLength_pos ha)

theorem gridStep_le_one {a : ℝ} (ha : 0 < a) : gridStep a ≤ 1 := by
  unfold gridStep windowLength
  rw [div_le_one (by positivity)]
  linarith

theorem gridStep_mul_le_pi {a : ℝ} (ha : 0 < a) : gridStep a * a ≤ π := by
  unfold gridStep windowLength
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/-- **Grid Parseval for interval sources.** The samples of the transform of a source vanishing
off `[−a, a]` on the grid `hℤ` have square sum `L ∫_{−L/2}^{L/2} |ψ|²`. -/
theorem hasSum_norm_sq_testTransform_grid {a : ℝ} (ha : 0 < a) {ψ : ℝ → ℂ}
    (hψ : IntervalSource a ψ) :
    HasSum (fun k : ℤ => ‖testTransform ψ ((-(k * gridStep a) : ℝ) : ℂ)‖ ^ 2)
      (windowLength a *
        ∫ u in (-(windowLength a / 2))..(windowLength a / 2), ‖ψ u‖ ^ 2) := by
  have hL := windowLength_pos ha
  have hsupp : ∀ u, windowLength a / 2 ≤ |u| → ψ u = 0 := by
    intro u hu
    apply hψ.vanish
    intro hmem
    have := abs_le.mpr ⟨hmem.1, hmem.2⟩
    unfold windowLength at hu
    linarith [Real.pi_pos]
  have h := hasSum_norm_sq_paperFT_grid hL hψ.continuous hsupp 0 0
  have hfun : (fun k : ℤ => ‖testTransform ψ ((-(k * gridStep a) : ℝ) : ℂ)‖ ^ 2) =
      fun k : ℤ => ‖Zeta23.paperFT ψ ((0 - (0 + k * (2 * π / windowLength a)) : ℝ) : ℂ)‖ ^ 2 := by
    funext k
    have e : ((0 : ℝ) - (0 + k * (2 * π / windowLength a)) : ℝ) = -(k * gridStep a) := by
      unfold gridStep; ring
    rw [e]
    simp only [testTransform, Zeta23.paperFT]
  rw [hfun]
  exact h

/-- The energy of a moment source on any symmetric window is at most `a^{2j}` times the energy
of the source. -/
theorem intervalIntegral_norm_sq_momentSource_le {a : ℝ} {f : ℝ → ℂ}
    (hf : IntervalSource a f) (j : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    ∫ u in (-b)..b, ‖momentSource f j u‖ ^ 2 ≤ (a ^ j) ^ 2 * ∫ u, ‖f u‖ ^ 2 := by
  have hfint : Integrable fun u => ‖f u‖ ^ 2 :=
    (hf.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (hf.hasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
  have hmint : Integrable fun u => ‖momentSource f j u‖ ^ 2 :=
    ((intervalSource_momentSource hf j).continuous.norm.pow 2).integrable_of_hasCompactSupport
      ((intervalSource_momentSource hf j).hasCompactSupport.comp_left
        (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
  calc ∫ u in (-b)..b, ‖momentSource f j u‖ ^ 2
      ≤ ∫ u in (-b)..b, (a ^ j) ^ 2 * ‖f u‖ ^ 2 := by
        refine intervalIntegral.integral_mono_on (by linarith) hmint.intervalIntegrable
          (hfint.const_mul _).intervalIntegrable fun u _ => ?_
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_momentSource_le hf j u) 2
    _ = (a ^ j) ^ 2 * ∫ u in (-b)..b, ‖f u‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ (a ^ j) ^ 2 * ∫ u, ‖f u‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_le_integral hfint (Eventually.of_forall fun _ => by positivity)

/-- Any finite set of grid samples of the `j`-th moment transform has square sum at most
`L a^{2j} ∫ |f|²`. -/
theorem sum_norm_sq_testTransform_grid_le {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : IntervalSource a f) (j : ℕ) (t : Finset ℤ) :
    ∑ k ∈ t, ‖testTransform (momentSource f j) ((-(k * gridStep a) : ℝ) : ℂ)‖ ^ 2 ≤
      windowLength a * ((a ^ j) ^ 2 * ∫ u, ‖f u‖ ^ 2) := by
  have h := hasSum_norm_sq_testTransform_grid ha (intervalSource_momentSource hf j)
  refine (sum_le_hasSum t (fun _ _ => sq_nonneg _) h).trans ?_
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral_norm_sq_momentSource_le hf j (by linarith [windowLength_pos ha]))
    (windowLength_pos ha).le

/-! ### 3. Grid cells and the local count -/

/-- The grid index `−⌊x/h⌋` of a height `x`: the grid point `−k h = ⌊x/h⌋ h` lies within `h` to the
left of `x`. -/
def gridIndex (a x : ℝ) : ℤ := -⌊x / gridStep a⌋

theorem gridPoint_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    -((gridIndex a x : ℝ) * gridStep a) ≤ x := by
  unfold gridIndex
  have hh := gridStep_pos ha
  have := (le_div_iff₀ hh).mp (Int.floor_le (x / gridStep a))
  push_cast
  linarith

theorem lt_gridPoint_add {a : ℝ} (ha : 0 < a) (x : ℝ) :
    x < -((gridIndex a x : ℝ) * gridStep a) + gridStep a := by
  unfold gridIndex
  have hh := gridStep_pos ha
  have h2 : x < ((⌊x / gridStep a⌋ : ℝ) + 1) * gridStep a :=
    (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x / gridStep a))
  rw [add_mul, one_mul] at h2
  push_cast
  linarith

theorem abs_sub_gridPoint_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |x - -((gridIndex a x : ℝ) * gridStep a)| ≤ gridStep a := by
  rw [abs_le]
  constructor
  · linarith [gridPoint_le ha x, gridStep_pos ha]
  · linarith [lt_gridPoint_add ha x]

/-- **Each grid cell carries at most `M` points** when every unit window does. -/
theorem card_filter_gridIndex_le {ι : Type*} {x : ι → ℝ} {M : ℕ} {a : ℝ} (ha : 0 < a)
    (s : Finset ι) (hM : ∀ T : ℝ, ((s : Set ι) ∩ {q | |x q - T| ≤ 1}).encard ≤ M) (k : ℤ) :
    ({q ∈ s | gridIndex a (x q) = k} : Finset ι).card ≤ M := by
  have hsub : (({q ∈ s | gridIndex a (x q) = k} : Finset ι) : Set ι) ⊆
      (s : Set ι) ∩ {q | |x q - -((k : ℝ) * gridStep a)| ≤ 1} := by
    intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    obtain ⟨hqs, hqk⟩ := hq
    refine ⟨hqs, ?_⟩
    show |x q - -((k : ℝ) * gridStep a)| ≤ 1
    rw [← hqk]
    exact (abs_sub_gridPoint_le ha (x q)).trans (gridStep_le_one ha)
  have h := (Set.encard_le_encard hsub).trans (hM _)
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

/-! ### 4. Weighted Cauchy–Schwarz for series -/

/-- `(Σ c_j)² ≤ (Σ p_j)(Σ c_j²/p_j)` for positive weights `p_j` and nonnegative `c_j`. -/
theorem sq_tsum_le_tsum_mul_tsum_div {p c : ℕ → ℝ} (hp : ∀ j, 0 < p j) (hc : ∀ j, 0 ≤ c j)
    (hps : Summable p) (hcs : Summable fun j => c j ^ 2 / p j) :
    (∑' j, c j) ^ 2 ≤ (∑' j, p j) * ∑' j, c j ^ 2 / p j := by
  have hF : ∀ j, 0 ≤ Real.sqrt (p j) := fun j => Real.sqrt_nonneg _
  have hG : ∀ j, 0 ≤ c j / Real.sqrt (p j) := fun j => div_nonneg (hc j) (hF j)
  have hFG : ∀ j, Real.sqrt (p j) * (c j / Real.sqrt (p j)) = c j := fun j => by
    have : Real.sqrt (p j) ≠ 0 := (Real.sqrt_pos.mpr (hp j)).ne'
    field_simp
  have hF2 : ∀ j, Real.sqrt (p j) ^ (2 : ℝ) = p j := fun j => by
    rw [Real.rpow_two, Real.sq_sqrt (hp j).le]
  have hG2 : ∀ j, (c j / Real.sqrt (p j)) ^ (2 : ℝ) = c j ^ 2 / p j := fun j => by
    rw [Real.rpow_two, div_pow, Real.sq_sqrt (hp j).le]
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hF hG
    (by simpa only [hF2] using hps) (by simpa only [hG2] using hcs)
  simp only [hFG, hF2, hG2] at h
  have hA : 0 ≤ ∑' j, p j := tsum_nonneg fun j => (hp j).le
  have hB : 0 ≤ ∑' j, c j ^ 2 / p j := tsum_nonneg fun j => div_nonneg (sq_nonneg _) (hp j).le
  have hc0 : 0 ≤ ∑' j, c j := tsum_nonneg hc
  calc (∑' j, c j) ^ 2
      ≤ ((∑' j, p j) ^ (1 / 2 : ℝ) * (∑' j, c j ^ 2 / p j) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hc0 h 2
    _ = _ := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-! ### 5. Two weight identities -/

theorem momentWeight_mul_sq (ρ₀ a X : ℝ) (j : ℕ) (ha : a ≠ 0) :
    ρ₀ ^ j / (j.factorial * a ^ j) * ((a ^ j) ^ 2 * X) = (ρ₀ * a) ^ j / j.factorial * X := by
  have ha0 : a ^ j ≠ 0 := pow_ne_zero _ ha
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [mul_pow ρ₀ a]
  field_simp

theorem sq_div_momentWeight (ρ₀ a B : ℝ) (j : ℕ) (ha : a ≠ 0) (hρ : ρ₀ ≠ 0) :
    (ρ₀ ^ j / j.factorial * B) ^ 2 / ((ρ₀ * a) ^ j / j.factorial) =
      ρ₀ ^ j / (j.factorial * a ^ j) * B ^ 2 := by
  have ha0 : a ^ j ≠ 0 := pow_ne_zero _ ha
  have hρ0 : ρ₀ ^ j ≠ 0 := pow_ne_zero _ hρ
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [mul_pow ρ₀ a]
  field_simp

/-! ### 6. The sampling inequality -/

/-- **Sampling a transform on a locally bounded point set.** If at most `M` of the heights `x_q`,
`q ∈ s`, fall in any unit window and all depths satisfy `|y_q| ≤ σ`, then
`Σ_{q ∈ s} |Φ(x_q + i y_q)|² ≤ e^{2(h+σ)a} M L ∫|f|²` with `L = 2a + 2π`, `h = 2π/L`. -/
theorem sum_norm_sq_testTransform_le_of_locallyBounded {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : IntervalSource a f) {ι : Type*} (x y : ι → ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hy : ∀ q, |y q| ≤ σ) {M : ℕ} (s : Finset ι)
    (hM : ∀ T : ℝ, ((s : Set ι) ∩ {q | |x q - T| ≤ 1}).encard ≤ M) :
    ∑ q ∈ s, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
      Real.exp (2 * (gridStep a + σ) * a) * (M * (windowLength a * ∫ u, ‖f u‖ ^ 2)) := by
  have hh0 : 0 < gridStep a := gridStep_pos ha
  set ρ₀ := gridStep a + σ with hρ₀
  have hρ₀0 : 0 < ρ₀ := by linarith
  set N := ∫ u, ‖f u‖ ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => by positivity
  set I₁ := ∫ u, ‖f u‖ with hI₁
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun _ => norm_nonneg _
  set L := windowLength a with hL
  have hL0 : 0 < L := windowLength_pos ha
  set g : ι → ℝ := fun q => -((gridIndex a (x q) : ℝ) * gridStep a) with hg
  set B : ℕ → ι → ℝ := fun j q => ‖testTransform (momentSource f j) ((g q : ℝ) : ℂ)‖ with hB
  set D : ℕ → ℝ := fun j => ρ₀ ^ j / (j.factorial * a ^ j) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by positivity
  have hB0 : ∀ j q, 0 ≤ B j q := fun j q => norm_nonneg _
  have hBle : ∀ j q, B j q ≤ a ^ j * I₁ := fun j q => norm_testTransform_momentSource_le hf j (g q)
  have hE : ∑' j : ℕ, (ρ₀ * a) ^ j / j.factorial = Real.exp (ρ₀ * a) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hDB : ∀ j q, D j * B j q ^ 2 ≤ (ρ₀ * a) ^ j / j.factorial * I₁ ^ 2 := by
    intro j q
    calc D j * B j q ^ 2 ≤ D j * (a ^ j * I₁) ^ 2 := by
          gcongr
          exact hBle j q
      _ = (ρ₀ * a) ^ j / j.factorial * I₁ ^ 2 := by
          simp only [hD]
          rw [mul_pow (a ^ j) I₁]
          exact momentWeight_mul_sq ρ₀ a (I₁ ^ 2) j ha.ne'
  have hsummD : ∀ q, Summable fun j => D j * B j q ^ 2 := fun q =>
    Summable.of_nonneg_of_le (fun j => by positivity) (fun j => hDB j q)
      ((Real.summable_pow_div_factorial (ρ₀ * a)).mul_right _)
  -- pointwise bound through the power series and weighted Cauchy–Schwarz
  have hpt : ∀ q, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
      Real.exp (ρ₀ * a) * ∑' j, D j * B j q ^ 2 := by
    intro q
    have hw : ‖((x q : ℂ) + (y q : ℂ) * I) - (g q : ℂ)‖ ≤ ρ₀ := by
      have e : ((x q : ℂ) + (y q : ℂ) * I) - (g q : ℂ) =
          ((x q - g q : ℝ) : ℂ) + (y q : ℂ) * I := by push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have := abs_sub_gridPoint_le ha (x q)
      linarith [hy q]
    have hz : ((x q : ℂ) + (y q : ℂ) * I) =
        (g q : ℂ) + (((x q : ℂ) + (y q : ℂ) * I) - (g q : ℂ)) := by ring
    have h1 := norm_testTransform_le_tsum_momentSource hf (g q) hw
    rw [← hz] at h1
    have hp : ∀ j : ℕ, 0 < (ρ₀ * a) ^ j / j.factorial := fun j => by positivity
    have hps : Summable fun j : ℕ => (ρ₀ * a) ^ j / j.factorial :=
      Real.summable_pow_div_factorial _
    have hconv : ∀ j : ℕ, (ρ₀ ^ j / j.factorial * B j q) ^ 2 / ((ρ₀ * a) ^ j / j.factorial) =
        D j * B j q ^ 2 := by
      intro j
      simp only [hD]
      exact sq_div_momentWeight ρ₀ a (B j q) j ha.ne' hρ₀0.ne'
    have hcs : Summable fun j : ℕ =>
        (ρ₀ ^ j / j.factorial * B j q) ^ 2 / ((ρ₀ * a) ^ j / j.factorial) := by
      simp only [hconv]
      exact hsummD q
    have hCS := sq_tsum_le_tsum_mul_tsum_div hp (fun j => by positivity) hps hcs
    calc ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2
        ≤ (∑' j : ℕ, ρ₀ ^ j / j.factorial * B j q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := hCS
      _ = Real.exp (ρ₀ * a) * ∑' j, D j * B j q ^ 2 := by
          rw [hE]
          congr 1
          exact tsum_congr hconv
  -- each grid cell carries at most `M` points; grid Parseval
  have hcell : ∀ j, ∑ q ∈ s, B j q ^ 2 ≤ M * (L * ((a ^ j) ^ 2 * N)) := by
    intro j
    set G : ℤ → ℝ := fun k =>
      ‖testTransform (momentSource f j) ((-(k * gridStep a) : ℝ) : ℂ)‖ ^ 2 with hG
    have hGq : ∀ q, B j q ^ 2 = G (gridIndex a (x q)) := fun q => rfl
    have hG0 : ∀ k, 0 ≤ G k := fun k => sq_nonneg _
    calc ∑ q ∈ s, B j q ^ 2 = ∑ q ∈ s, G (gridIndex a (x q)) :=
          Finset.sum_congr rfl fun q _ => hGq q
      _ = ∑ k ∈ s.image (fun q => gridIndex a (x q)),
            ({q ∈ s | gridIndex a (x q) = k} : Finset ι).card • G k :=
          Finset.sum_comp G (fun q => gridIndex a (x q))
      _ ≤ ∑ k ∈ s.image (fun q => gridIndex a (x q)), M • G k :=
          Finset.sum_le_sum fun k _ =>
            nsmul_le_nsmul_left (hG0 k) (card_filter_gridIndex_le ha s hM k)
      _ = M • ∑ k ∈ s.image (fun q => gridIndex a (x q)), G k := (Finset.smul_sum).symm
      _ ≤ M • (L * ((a ^ j) ^ 2 * N)) :=
          nsmul_le_nsmul_right (sum_norm_sq_testTransform_grid_le ha hf j _) M
      _ = M * (L * ((a ^ j) ^ 2 * N)) := nsmul_eq_mul _ _
  have hterm : ∀ j : ℕ, D j * (M * (L * ((a ^ j) ^ 2 * N))) =
      (ρ₀ * a) ^ j / j.factorial * (M * (L * N)) := by
    intro j
    simp only [hD]
    rw [show (M : ℝ) * (L * ((a ^ j) ^ 2 * N)) = (a ^ j) ^ 2 * (M * (L * N)) by ring]
    exact momentWeight_mul_sq ρ₀ a (M * (L * N)) j ha.ne'
  -- assemble
  calc ∑ q ∈ s, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2
      ≤ ∑ q ∈ s, Real.exp (ρ₀ * a) * ∑' j, D j * B j q ^ 2 :=
        Finset.sum_le_sum fun q _ => hpt q
    _ = Real.exp (ρ₀ * a) * ∑' j, D j * ∑ q ∈ s, B j q ^ 2 := by
        rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun q _ => hsummD q)]
        congr 1
        refine tsum_congr fun j => ?_
        rw [Finset.mul_sum]
    _ ≤ Real.exp (ρ₀ * a) * ∑' j, D j * (M * (L * ((a ^ j) ^ 2 * N))) := by
        refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun j => ?_) ?_ ?_)
          (Real.exp_pos _).le
        · exact mul_le_mul_of_nonneg_left (hcell j) (hD0 j)
        · refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
            ((Real.summable_pow_div_factorial (ρ₀ * a)).mul_right (M * (L * N)))
          · exact mul_nonneg (hD0 j) (Finset.sum_nonneg fun q _ => sq_nonneg _)
          · calc D j * ∑ q ∈ s, B j q ^ 2 ≤ D j * (M * (L * ((a ^ j) ^ 2 * N))) :=
                  mul_le_mul_of_nonneg_left (hcell j) (hD0 j)
              _ = (ρ₀ * a) ^ j / j.factorial * (M * (L * N)) := hterm j
        · refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
            ((Real.summable_pow_div_factorial (ρ₀ * a)).mul_right (M * (L * N)))
          exact le_of_eq (hterm j)
    _ = Real.exp (ρ₀ * a) * (Real.exp (ρ₀ * a) * (M * (L * N))) := by
        congr 1
        rw [tsum_congr hterm, tsum_mul_right, hE]
    _ = Real.exp (2 * (gridStep a + σ) * a) * (M * (L * N)) := by
        rw [← mul_assoc, ← Real.exp_add, ← hρ₀, show ρ₀ * a + ρ₀ * a = 2 * ρ₀ * a by ring]

/-- **The sampling inequality with the explicit constant** `M (2a + 2π) e^{2π} e^{2σa}`. -/
theorem sum_norm_sq_testTransform_le_of_locallyBounded' {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : IntervalSource a f) {ι : Type*} (x y : ι → ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hy : ∀ q, |y q| ≤ σ) {M : ℕ} (s : Finset ι)
    (hM : ∀ T : ℝ, ((s : Set ι) ∩ {q | |x q - T| ≤ 1}).encard ≤ M) :
    ∑ q ∈ s, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
      M * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * ∫ u, ‖f u‖ ^ 2 := by
  refine (sum_norm_sq_testTransform_le_of_locallyBounded ha hf x y hσ hy s hM).trans ?_
  have hN0 : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hexp : Real.exp (2 * (gridStep a + σ) * a) ≤ Real.exp (2 * π) * Real.exp (2 * σ * a) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := gridStep_mul_le_pi ha
    have h2 : 2 * (gridStep a + σ) * a = 2 * (gridStep a * a) + 2 * σ * a := by ring
    linarith
  unfold windowLength
  calc Real.exp (2 * (gridStep a + σ) * a) * (M * ((2 * a + 2 * π) * ∫ u, ‖f u‖ ^ 2))
      ≤ Real.exp (2 * π) * Real.exp (2 * σ * a) * (M * ((2 * a + 2 * π) * ∫ u, ‖f u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = _ := by ring

/-- **Summability and the series bound** for a globally locally bounded family. -/
theorem summable_tsum_norm_sq_testTransform_le_of_locallyBounded {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : IntervalSource a f) {ι : Type*} (x y : ι → ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hy : ∀ q, |y q| ≤ σ) {M : ℕ} (hM : ∀ T : ℝ, ({q | |x q - T| ≤ 1} : Set ι).encard ≤ M) :
    Summable (fun q => ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2) ∧
      ∑' q, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
        M * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * ∫ u, ‖f u‖ ^ 2 := by
  have hbound : ∀ s : Finset ι, ∑ q ∈ s, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
      M * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * ∫ u, ‖f u‖ ^ 2 :=
    fun s => sum_norm_sq_testTransform_le_of_locallyBounded' ha hf x y hσ hy s fun T =>
      (Set.encard_le_encard Set.inter_subset_right).trans (hM T)
  have hs : Summable fun q => ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 :=
    summable_of_sum_le (fun _ => sq_nonneg _) hbound
  exact ⟨hs, hs.tsum_le_of_sum_le hbound⟩

end

end GaloisForLFunctions.SquareRootThreshold
