import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheLogLatticeSynthesizesWideTests
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion

/-!
# The critical exponent

Weil's form on the atomic families of width `w = N^{−θ}`: at `θ = 1` — a fixed fraction of the spacing —
it is nonnegative up to the pole for every `N` (`TheStabilityLawAtTheSpacingScale`); at every fixed
width it is the Riemann hypothesis (`UnboundedOverlapIsTheRiemannHypothesis`). This file settles
every exponent in between.

**The overlap law** (`riemannHypothesis_iff_atomicFamilies_nonneg_of_growth`): for every `C²` profile
`φ` supported in `[−1, 1]` with `∫ φ = 1`, and every dilation sequence `κ_N → ∞` whose overlap ratio
`N/κ_N` beats `√(log κ_N)` (`OverlapGrowth`), RH holds iff for all large `N` Weil's form is
nonnegative on every atomic test `Σ_{n ≤ N} x_n φ_κ(· − log n)` with the dilate `φ_κ = κ φ(κ·)`.
Special cases: widths `N^{−θ}`, `0 < θ < 1` (`riemannHypothesis_iff_atomicFamilies_nonneg`: the
critical exponent is one), and widths `(log N)^α/N`, `α > 1/2`
(`riemannHypothesis_iff_atomicFamilies_nonneg_log`): positivity is RH as soon as the overlap ratio
exceeds `(log N)^{1/2+ε}`.

The proof synthesizes a fixed test `F` with `Q(F) < 0` from narrow atoms. Near the top scale the
atoms `log n`, `n ≍ N`, have gaps `≍ 1/N`; the cell weights `x_n = ∫_{cell} F` give a synthesis `S`
with

* `‖S − F‖_∞ ≤ M (k/n₀) ‖φ′‖₁ + L ‖φ‖₁ / k` (`abs_cellSum_sub_self_le`) — the cell lemma and one
  convolution step;
* `Lip(S) ≤ M k ‖φ′‖₁ + M (k²/n₀) ‖φ″‖₁` (`abs_cellSum_sub_le_lipschitz`);

so the Lévy energy of `S − F` is `O((k/n₀ + 1/k)² log k)` (`levyEnergy_le_lipschitz` at `δ = 1/k`), and
Weil's form, continuous in the Lévy norm (`weilQuad_add_le`), moves by `o(1)` as soon as
`k → ∞` and `(k/n₀)² log k → 0`.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### Generic synthesis bounds -/

section Synthesis

variable {F ψ ψ1 ψ2 : ℝ → ℝ} {a : ℕ → ℝ} {J : ℕ} {h M L ρ : ℝ}

/-- `|∫ F(t) ψ(r − t) dt| ≤ M ‖ψ‖₁` for `|F| ≤ M`. -/
theorem abs_integral_mul_le_sup_mul (hFM : ∀ t, |F t| ≤ M) (hψi : Integrable ψ) (r : ℝ) :
    |∫ t, F t * ψ (r - t)| ≤ M * ∫ s, |ψ s| := by
  have hint : Integrable fun t => |ψ (r - t)| := (hψi.comp_sub_left r).abs
  calc |∫ t, F t * ψ (r - t)| ≤ ∫ t, |F t * ψ (r - t)| := abs_integral_le_integral_abs
    _ ≤ ∫ t, M * |ψ (r - t)| := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => abs_nonneg _)
          (hint.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
        show |F t * ψ (r - t)| ≤ M * |ψ (r - t)|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hFM t) (abs_nonneg _)
    _ = M * ∫ s, |ψ s| := by
        rw [MeasureTheory.integral_const_mul, integral_sub_left_eq_self (fun s => |ψ s|) volume r]

/-- **The synthesis is close to the test**: `|S(r) − F(r)| ≤ M h ‖ψ′‖₁ + L ρ ‖ψ‖₁`. -/
theorem abs_cellSum_sub_self_le (ha : Monotone a) (hh : 0 ≤ h)
    (hgap : ∀ j < J, a (j + 1) - a j ≤ h) (hF : Continuous F) (hFM : ∀ t, |F t| ≤ M)
    (hFsupp : ∀ t, t ∉ Icc (a 0) (a J) → F t = 0) (hL : ∀ u v, |F u - F v| ≤ L * |u - v|)
    (hψd : ∀ s, HasDerivAt ψ (ψ1 s) s) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψ1c : Continuous ψ1) (hψ1i : Integrable ψ1) (hψint : ∫ s, ψ s = 1)
    (hψρ : ∀ s, ρ < |s| → ψ s = 0) (r : ℝ) :
    |cellSum F ψ a J r - F r| ≤ M * h * (∫ s, |ψ1 s|) + L * ρ * ∫ s, |ψ s| := by
  have h1 := abs_cellSum_sub_le ha hh hgap hF hFM hFsupp hψd hψ hψ1c hψ1i r
  have h2 := abs_integral_mul_sub_le hF hψ hψc hψint hψρ hL r
  calc |cellSum F ψ a J r - F r|
      = |(cellSum F ψ a J r - ∫ t, F t * ψ (r - t)) + ((∫ t, F t * ψ (r - t)) - F r)| := by
        ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **The synthesis is Lipschitz**: `|S(u) − S(v)| ≤ (M‖ψ′‖₁ + M h ‖ψ″‖₁)|u − v|`. -/
theorem abs_cellSum_sub_le_lipschitz (ha : Monotone a) (hh : 0 ≤ h)
    (hgap : ∀ j < J, a (j + 1) - a j ≤ h) (hF : Continuous F) (hFM : ∀ t, |F t| ≤ M)
    (hFsupp : ∀ t, t ∉ Icc (a 0) (a J) → F t = 0)
    (hψd : ∀ s, HasDerivAt ψ (ψ1 s) s) (hψ1d : ∀ s, HasDerivAt ψ1 (ψ2 s) s)
    (hψ1c : Continuous ψ1) (hψ1i : Integrable ψ1) (hψ2c : Continuous ψ2) (hψ2i : Integrable ψ2)
    (u v : ℝ) :
    |cellSum F ψ a J u - cellSum F ψ a J v| ≤
      (M * (∫ s, |ψ1 s|) + M * h * ∫ s, |ψ2 s|) * |u - v| := by
  refine abs_sub_le_of_hasDerivAt (hasDerivAt_cellSum hψd) (fun r => ?_) u v
  have h1 := abs_cellSum_sub_le ha hh hgap hF hFM hFsupp hψ1d hψ1c hψ2c hψ2i r
  have h2 := abs_integral_mul_le_sup_mul hFM hψ1i r
  calc |cellSum F ψ1 a J r| = |(cellSum F ψ1 a J r - ∫ t, F t * ψ1 (r - t)) +
        ∫ t, F t * ψ1 (r - t)| := by ring_nf
    _ ≤ M * h * (∫ s, |ψ2 s|) + M * ∫ s, |ψ1 s| := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = _ := by ring

end Synthesis

/-! ### Norms of a small perturbation -/

section Norms

variable {d : ℝ → ℝ} {e R : ℝ}

/-- `∫ |d| ≤ 2R e` for `|d| ≤ e` supported in `[−R, R]`. -/
theorem integral_abs_le_of_bound (hd : Continuous d) (hdc : HasCompactSupport d)
    (hde : ∀ u, |d u| ≤ e) (hdR : SupportedIn R d) (hR : 0 ≤ R) :
    ∫ u, |d u| ≤ 2 * R * e := by
  have he : 0 ≤ e := (abs_nonneg _).trans (hde 0)
  have hint : Integrable fun u => |d u| := (hd.integrable_of_hasCompactSupport hdc).abs
  calc ∫ u, |d u| ≤ ∫ u, (Icc (-R) R).indicator (fun _ => e) u := by
        refine integral_mono hint ((integrableOn_const (by simp)).integrable_indicator
          measurableSet_Icc) fun u => ?_
        by_cases hu : u ∈ Icc (-R) R
        · rw [indicator_of_mem hu]; exact hde u
        · rw [indicator_of_notMem hu, hdR u (by
            simp only [mem_Icc, not_and_or, not_le] at hu
            rcases hu with hu | hu
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith), abs_zero]
    _ = 2 * R * e := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
          smul_eq_mul]
        ring

/-- `∫ d² ≤ e ∫ |d|` for `|d| ≤ e`. -/
theorem integral_sq_le_of_bound (hd : Continuous d) (hdc : HasCompactSupport d)
    (hde : ∀ u, |d u| ≤ e) : ∫ u, d u ^ 2 ≤ e * ∫ u, |d u| := by
  have hint : Integrable fun u => |d u| := (hd.integrable_of_hasCompactSupport hdc).abs
  rw [← MeasureTheory.integral_const_mul]
  refine integral_mono (integrable_sq_of_continuous hd hdc) (hint.const_mul _) fun u => ?_
  calc d u ^ 2 = |d u| * |d u| := by rw [← sq, sq_abs]
    _ ≤ e * |d u| := mul_le_mul_of_nonneg_right (hde u) (abs_nonneg _)

end Norms

/-! ### Profiles and their dilates -/

section Profile

variable {φ : ℝ → ℝ}

/-- A function vanishing off `[−1, 1]`. -/
def VanishesOff (f : ℝ → ℝ) : Prop := ∀ s, 1 < |s| → f s = 0

theorem vanishesOff_deriv {f : ℝ → ℝ} (hf : VanishesOff f) : VanishesOff (deriv f) := by
  intro s hs
  have hopen : IsOpen {t : ℝ | 1 < |t|} := isOpen_lt continuous_const continuous_abs
  have hev : f =ᶠ[𝓝 s] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hopen.mem_nhds hs) fun t ht => hf t ht
  rw [hev.deriv_eq, deriv_const]

theorem hasCompactSupport_of_vanishes {f : ℝ → ℝ} {B : ℝ} (hf : ∀ s, B < |s| → f s = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_Icc (a := -B) (b := B)) fun s hs => hf s (by
    simp only [mem_Icc, not_and_or, not_le] at hs
    rcases hs with hs | hs
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs s)
    · exact lt_of_lt_of_le hs (le_abs_self s))

theorem dilate_vanishes {f : ℝ → ℝ} (hf : VanishesOff f) {k : ℝ} (hk : 0 < k) {s : ℝ}
    (hs : 1 / k < |s|) : dilate k f s = 0 :=
  dilate_eq_zero hk hf hs

theorem contDiff_dilate {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (k : ℝ) :
    ContDiff ℝ n (dilate k f) :=
  contDiff_const.mul (hf.comp (contDiff_const.mul contDiff_id))

theorem integral_abs_dilate_mul {k : ℝ} (hk : 0 < k) (f : ℝ → ℝ) :
    ∫ s, |dilate k (fun s => k * f s) s| = k * ∫ s, |f s| := by
  rw [integral_abs_dilate hk]
  simp_rw [abs_mul, abs_of_pos hk]
  exact MeasureTheory.integral_const_mul _ _

/-- The derivatives of a `C²` profile. -/
theorem profile_derivs (hφ : ContDiff ℝ 2 φ) :
    (∀ s, HasDerivAt φ (deriv φ s) s) ∧ (∀ s, HasDerivAt (deriv φ) (deriv (deriv φ) s) s) ∧
      Continuous (deriv φ) ∧ Continuous (deriv (deriv φ)) := by
  have h1 : ContDiff ℝ 1 (deriv φ) := hφ.iterate_deriv' 1 1
  refine ⟨fun s => (hφ.differentiable (by norm_num) s).hasDerivAt,
    fun s => (h1.differentiable (by norm_num) s).hasDerivAt, h1.continuous, ?_⟩
  exact h1.continuous_deriv le_rfl

end Profile

/-! ### Constants of the synthesis -/

/-- The supremum error `e₀ = M (k/n₀) ‖φ′‖₁ + L ‖φ‖₁/k` of the synthesis. -/
def synthErr (A0 A1 M L k : ℝ) (n₀ : ℕ) : ℝ := M * (1 / n₀) * (k * A1) + L * (1 / k) * A0

/-- The Lipschitz constant `M k ‖φ′‖₁ + M (k²/n₀) ‖φ″‖₁ + L` of the error. -/
def synthLip (A1 A2 M L k : ℝ) (n₀ : ℕ) : ℝ := M * (k * A1) + M * (1 / n₀) * (k * (k * A2)) + L

/-- The Lévy bound of the error at `δ = 1/k`. -/
def synthLevy (R e LD k : ℝ) : ℝ :=
  Real.exp (1 / 2) * LD * (1 / k) * (2 * R * e) + (2 * Real.log k + levyLipConstant) * (2 * R * e ^ 2)

/-- The resulting bound on the motion of Weil's form. -/
def weilErr (F : ℝ → ℝ) (R e V : ℝ) : ℝ :=
  2 * |gammaHardyPhaseRate 0| * (2 * (Real.sqrt (∫ u, F u ^ 2) * (Real.sqrt (2 * R) * e)) +
      2 * R * e ^ 2) +
    (2 * (Real.sqrt (levyEnergy F) * Real.sqrt V) + V) +
    2 * primeMass R * (2 * (Real.sqrt (∫ u, F u ^ 2) * (Real.sqrt (2 * R) * e)) + 2 * R * e ^ 2) +
    4 * Real.cosh (R / 2) * (|coshHalfMoment F| + |sinhHalfMoment F|) * (2 * R * e) +
    4 * Real.cosh (R / 2) ^ 2 * (2 * R * e) ^ 2

/-! ### The synthesis of a fixed test -/

/-- The block size `B = ⌈1 + e^{2R}⌉`: the atoms `n₀ ≤ n ≤ n₀ B` synthesize a test supported in
`[−R, R]`. -/
def blockSize (R : ℝ) : ℕ := ⌈1 + Real.exp (2 * R)⌉₊

/-- The cell weights placed on the atoms `n₀ ≤ n < n₀ + J`. -/
def synthWeights (F : ℝ → ℝ) (a : ℕ → ℝ) (n₀ J : ℕ) (n : ℕ) : ℝ :=
  if n₀ ≤ n ∧ n < n₀ + J then cellWeight F a (n - n₀) else 0

/-- The atomic test with the synthesis weights is the synthesis, translated to the atoms. -/
theorem atomicTest_synthWeights {F ψ : ℝ → ℝ} {n₀ J N : ℕ} (hn₀ : 1 ≤ n₀) (hJN : n₀ + J ≤ N + 1)
    (c : ℝ) (u : ℝ) :
    atomicTest N (synthWeights F (logNode n₀ c) n₀ J) ψ u = cellSum F ψ (logNode n₀ c) J (u - c) := by
  unfold atomicTest cellSum
  have hterm : ∀ n ∈ Finset.Icc 1 N, synthWeights F (logNode n₀ c) n₀ J n * ψ (u - Real.log n) =
      if n ∈ Finset.Ico n₀ (n₀ + J) then
        cellWeight F (logNode n₀ c) (n - n₀) * ψ (u - Real.log n) else 0 := by
    intro n _
    unfold synthWeights
    by_cases h : n₀ ≤ n ∧ n < n₀ + J
    · rw [if_pos h, if_pos (Finset.mem_Ico.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (Finset.mem_Ico.mp h')), zero_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter,
    show (Finset.Icc 1 N).filter (· ∈ Finset.Ico n₀ (n₀ + J)) = Finset.Ico n₀ (n₀ + J) by
      ext n; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.add_sub_cancel_left]
  unfold logNode
  congr 2
  ring

/-! ### The dilated profile -/

section DilatedProfile

variable {φ : ℝ → ℝ} {k : ℝ}

theorem hasDerivAt_dilate_profile (hφ : ContDiff ℝ 2 φ) (s : ℝ) :
    HasDerivAt (dilate k φ) (dilate k (fun s => k * deriv φ s) s) s :=
  hasDerivAt_dilate (profile_derivs hφ).1 s

theorem hasDerivAt_dilate_profile' (hφ : ContDiff ℝ 2 φ) (s : ℝ) :
    HasDerivAt (dilate k (fun s => k * deriv φ s))
      (dilate k (fun s => k * (k * deriv (deriv φ) s)) s) s :=
  hasDerivAt_dilate (fun s => ((profile_derivs hφ).2.1 s).const_mul k) s

theorem continuous_dilate_of {f : ℝ → ℝ} (hf : Continuous f) : Continuous (dilate k f) :=
  continuous_const.mul (hf.comp (continuous_const.mul continuous_id))

theorem vanishesOff_const_mul {f : ℝ → ℝ} (hf : VanishesOff f) (c : ℝ) :
    VanishesOff fun s => c * f s := fun s hs => by simp [hf s hs]

theorem integrable_dilate_of {f : ℝ → ℝ} (hf : Continuous f) (hv : VanishesOff f) (hk : 0 < k) :
    Integrable (dilate k f) :=
  (continuous_dilate_of hf).integrable_of_hasCompactSupport
    (hasCompactSupport_of_vanishes fun _ hs => dilate_vanishes hv hk hs)

theorem integral_abs_dilate_mul_mul (hk : 0 < k) (f : ℝ → ℝ) :
    ∫ s, |dilate k (fun s => k * (k * f s)) s| = k * (k * ∫ s, |f s|) := by
  rw [integral_abs_dilate_mul hk (fun s => k * f s)]
  simp_rw [abs_mul, abs_of_pos hk]
  rw [MeasureTheory.integral_const_mul]

end DilatedProfile

/-! ### The log-lattice nodes of a window -/

section Nodes

variable {n₀ : ℕ} {R : ℝ}

/-- The number of cells `J = ⌈n₀ e^{2R}⌉` covering `[−R, R]`. -/
def cellCount (n₀ : ℕ) (R : ℝ) : ℕ := ⌈(n₀ : ℝ) * Real.exp (2 * R)⌉₊

theorem logNode_log_add_zero (n₀ : ℕ) (R : ℝ) : logNode n₀ (Real.log n₀ + R) 0 = -R := by
  simp only [logNode, add_zero]
  ring

theorem logNode_eq (hn₀ : 1 ≤ n₀) (R : ℝ) (j : ℕ) :
    logNode n₀ (Real.log n₀ + R) j = Real.log (((n₀ + j : ℕ) : ℝ) / n₀) - R := by
  have hn : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  rw [logNode, Real.log_div (by positivity) hn.ne']
  ring

theorem le_logNode_cellCount (hn₀ : 1 ≤ n₀) :
    R ≤ logNode n₀ (Real.log n₀ + R) (cellCount n₀ R) := by
  have hn : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  rw [logNode_eq hn₀]
  have hJ : (n₀ : ℝ) * Real.exp (2 * R) ≤ cellCount n₀ R := Nat.le_ceil _
  have h1 : Real.exp (2 * R) ≤ ((n₀ + cellCount n₀ R : ℕ) : ℝ) / n₀ := by
    rw [le_div_iff₀ hn]; push_cast; nlinarith
  have h2 := Real.log_le_log (Real.exp_pos _) h1
  rw [Real.log_exp] at h2
  linarith

theorem logNode_le (hn₀ : 1 ≤ n₀) (hR : 0 ≤ R) {j : ℕ} (hj : j ≤ cellCount n₀ R) :
    logNode n₀ (Real.log n₀ + R) j ≤ R + 2 := by
  have hn : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  rw [logNode_eq hn₀]
  have hJ : (cellCount n₀ R : ℝ) < n₀ * Real.exp (2 * R) + 1 := Nat.ceil_lt_add_one (by positivity)
  have he : 1 ≤ Real.exp (2 * R) := Real.one_le_exp (by linarith)
  have h1 : ((n₀ + j : ℕ) : ℝ) / n₀ ≤ 3 * Real.exp (2 * R) := by
    rw [div_le_iff₀ hn]
    have : ((n₀ + j : ℕ) : ℝ) ≤ n₀ + cellCount n₀ R := by
      push_cast; exact_mod_cast (show n₀ + j ≤ n₀ + cellCount n₀ R by omega)
    have hn1 : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    nlinarith
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h2
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  linarith

theorem cellCount_le_block : n₀ + cellCount n₀ R ≤ n₀ * blockSize R + 1 := by
  have hJ : (cellCount n₀ R : ℝ) < n₀ * Real.exp (2 * R) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hB : 1 + Real.exp (2 * R) ≤ blockSize R := Nat.le_ceil _
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  have : ((n₀ + cellCount n₀ R : ℕ) : ℝ) < ((n₀ * blockSize R + 1 + 1 : ℕ) : ℝ) := by
    push_cast; nlinarith
  have := (Nat.cast_lt (α := ℝ)).mp this
  omega

end Nodes

/-! ### The algebra of the final bound -/

/-- Monotonicity of the perturbation bound in the norms of the perturbation. -/
theorem weilErr_mono {F : ℝ → ℝ} {R' s2 q2 lv n1 e V : ℝ}
    (hs2 : s2 ≤ Real.sqrt (2 * R') * e) (hq2 : q2 ≤ 2 * R' * e ^ 2) (hlv : lv ≤ V)
    (hn10 : 0 ≤ n1) (hn1 : n1 ≤ 2 * R' * e) :
    2 * |gammaHardyPhaseRate 0| * (2 * (Real.sqrt (∫ u, F u ^ 2) * s2) + q2) +
        (2 * (Real.sqrt (levyEnergy F) * Real.sqrt lv) + lv) +
        2 * primeMass R' * (2 * (Real.sqrt (∫ u, F u ^ 2) * s2) + q2) +
        4 * Real.cosh (R' / 2) * (|coshHalfMoment F| + |sinhHalfMoment F|) * n1 +
        4 * Real.cosh (R' / 2) ^ 2 * n1 ^ 2 ≤
      weilErr F R' e V := by
  unfold weilErr
  have hF2 : 0 ≤ Real.sqrt (∫ u, F u ^ 2) := Real.sqrt_nonneg _
  have hLF : 0 ≤ Real.sqrt (levyEnergy F) := Real.sqrt_nonneg _
  have hP : 0 ≤ primeMass R' := primeMass_nonneg _
  have hch : 0 ≤ Real.cosh (R' / 2) := (Real.cosh_pos _).le
  have hmom : 0 ≤ |coshHalfMoment F| + |sinhHalfMoment F| := by positivity
  have hsl : Real.sqrt lv ≤ Real.sqrt V := Real.sqrt_le_sqrt hlv
  have hn1sq : n1 ^ 2 ≤ (2 * R' * e) ^ 2 := pow_le_pow_left₀ hn10 hn1 2
  have t1 : 2 * |gammaHardyPhaseRate 0| * (2 * (Real.sqrt (∫ u, F u ^ 2) * s2) + q2) ≤
      2 * |gammaHardyPhaseRate 0| *
        (2 * (Real.sqrt (∫ u, F u ^ 2) * (Real.sqrt (2 * R') * e)) + 2 * R' * e ^ 2) := by
    gcongr
  have t2 : 2 * (Real.sqrt (levyEnergy F) * Real.sqrt lv) + lv ≤
      2 * (Real.sqrt (levyEnergy F) * Real.sqrt V) + V := by gcongr
  have t3 : 2 * primeMass R' * (2 * (Real.sqrt (∫ u, F u ^ 2) * s2) + q2) ≤
      2 * primeMass R' *
        (2 * (Real.sqrt (∫ u, F u ^ 2) * (Real.sqrt (2 * R') * e)) + 2 * R' * e ^ 2) := by gcongr
  have t4 : 4 * Real.cosh (R' / 2) * (|coshHalfMoment F| + |sinhHalfMoment F|) * n1 ≤
      4 * Real.cosh (R' / 2) * (|coshHalfMoment F| + |sinhHalfMoment F|) * (2 * R' * e) := by
    gcongr
  have t5 : 4 * Real.cosh (R' / 2) ^ 2 * n1 ^ 2 ≤ 4 * Real.cosh (R' / 2) ^ 2 * (2 * R' * e) ^ 2 := by
    gcongr
  linarith

/-! ### The synthesis of a fixed test -/

section Synthesis2

variable {φ F : ℝ → ℝ} {R M L k : ℝ} {n₀ : ℕ}

/-- **Error bounds of the log-lattice synthesis** `S = Σ_j x_j φ_k(· − a_j)` of `F`: the supremum
error, the Lipschitz constant of `S − F`, and the support. -/
theorem synthesis_error_bounds (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    (hF : ContDiff ℝ 2 F) (hR : 0 ≤ R) (hFR : SupportedIn R F) (hFM : ∀ t, |F t| ≤ M)
    (hL : ∀ u v, |F u - F v| ≤ L * |u - v|) (hn₀ : 1 ≤ n₀) (hk : 1 ≤ k) :
    (∀ r, |cellSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R) r - F r| ≤
        synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L k n₀) ∧
      (∀ u v, |cellSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R) u -
          cellSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R) v| ≤
        (M * (k * ∫ s, |deriv φ s|) + M * (1 / n₀) * (k * (k * ∫ s, |deriv (deriv φ) s|))) *
          |u - v|) ∧
      SupportedIn (R + 3) (cellSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R)) ∧
      ContDiff ℝ 2 (cellSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R)) := by
  obtain ⟨-, -, hc1, hc2⟩ := profile_derivs hφ
  have hk0 : 0 < k := by linarith
  have hv1 := vanishesOff_deriv hφ1
  have hv2 := vanishesOff_deriv hv1
  have hψv : ∀ s, 1 / k < |s| → dilate k φ s = 0 := fun s hs => dilate_vanishes hφ1 hk0 hs
  have hψc : HasCompactSupport (dilate k φ) := hasCompactSupport_of_vanishes hψv
  have hψ : Continuous (dilate k φ) := continuous_dilate_of hφ.continuous
  have hc1' : Continuous fun s => k * deriv φ s := continuous_const.mul hc1
  have hc2' : Continuous fun s => k * (k * deriv (deriv φ) s) :=
    continuous_const.mul (continuous_const.mul hc2)
  have hψ1c : Continuous (dilate k fun s => k * deriv φ s) := continuous_dilate_of hc1'
  have hψ2c : Continuous (dilate k fun s => k * (k * deriv (deriv φ) s)) := continuous_dilate_of hc2'
  have hψ1i : Integrable (dilate k fun s => k * deriv φ s) :=
    integrable_dilate_of hc1' (vanishesOff_const_mul hv1 k) hk0
  have hψ2i : Integrable (dilate k fun s => k * (k * deriv (deriv φ) s)) :=
    integrable_dilate_of hc2' (vanishesOff_const_mul (vanishesOff_const_mul hv2 k) k) hk0
  have hψint : ∫ s, dilate k φ s = 1 := by rw [integral_dilate hk0, hφint]
  have hψabs : ∫ s, |dilate k φ s| = ∫ s, |φ s| := integral_abs_dilate hk0 φ
  have hψ1abs := integral_abs_dilate_mul hk0 (deriv φ)
  have hψ2abs := integral_abs_dilate_mul_mul hk0 (deriv (deriv φ))
  have ha := logNode_monotone hn₀ (Real.log n₀ + R)
  have hgap : ∀ j < cellCount n₀ R, logNode n₀ (Real.log n₀ + R) (j + 1) -
      logNode n₀ (Real.log n₀ + R) j ≤ 1 / n₀ := fun j _ => logNode_gap_le hn₀ _ j
  have hh : (0 : ℝ) ≤ 1 / n₀ := by positivity
  have ha0 := logNode_log_add_zero n₀ R
  have haJ := le_logNode_cellCount (R := R) hn₀
  have halb : ∀ j, -R ≤ logNode n₀ (Real.log n₀ + R) j := fun j => ha0 ▸ ha (Nat.zero_le j)
  have hFsupp : ∀ t, t ∉ Icc (logNode n₀ (Real.log n₀ + R) 0)
      (logNode n₀ (Real.log n₀ + R) (cellCount n₀ R)) → F t = 0 := by
    intro t ht
    refine hFR t ?_
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · rw [ha0] at ht
      exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
    · exact lt_of_lt_of_le (lt_of_le_of_lt haJ ht) (le_abs_self t)
  refine ⟨fun r => ?_, fun u v => ?_, fun r hr => ?_, ?_⟩
  · have := abs_cellSum_sub_self_le ha hh hgap hF.continuous hFM hFsupp hL
      (hasDerivAt_dilate_profile hφ) hψ hψc hψ1c hψ1i hψint hψv r
    rw [hψ1abs, hψabs] at this
    exact this
  · have := abs_cellSum_sub_le_lipschitz ha hh hgap hF.continuous hFM hFsupp
      (hasDerivAt_dilate_profile hφ) (hasDerivAt_dilate_profile' hφ) hψ1c hψ1i hψ2c hψ2i u v
    rw [hψ1abs, hψ2abs] at this
    exact this
  · unfold cellSum
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjJ : j ≤ cellCount n₀ R := (Finset.mem_range.mp hj).le
    have hab : |logNode n₀ (Real.log n₀ + R) j| ≤ R + 2 :=
      abs_le.mpr ⟨by linarith [halb j], logNode_le hn₀ hR hjJ⟩
    have hk1 : 1 / k ≤ 1 := by rw [div_le_one hk0]; exact hk
    rw [hψv _ (by
      have := abs_sub_abs_le_abs_sub r (logNode n₀ (Real.log n₀ + R) j)
      linarith), mul_zero]
  · unfold cellSum
    exact ContDiff.sum fun j _ =>
      contDiff_const.mul ((contDiff_dilate hφ k).comp (contDiff_id.sub contDiff_const))

/-- **The synthesis as a perturbation**: the atomic test of level `n₀ B` with the synthesis weights
is the translate of `F + D` by `log n₀ + R`, where the error `D` is a `C²` test supported in
`[−(R+3), R+3]` with
`‖D‖₂ ≤ √(2(R+3)) e₀`, `‖D‖₂² ≤ 2(R+3) e₀²`, `levyEnergy D ≤ V`, `‖D‖₁ ≤ 2(R+3) e₀`. -/
theorem exists_synthesis (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hF : ContDiff ℝ 2 F) (hR : 0 ≤ R)
    (hFR : SupportedIn R F) (hFM : ∀ t, |F t| ≤ M) (hL : ∀ u v, |F u - F v| ≤ L * |u - v|)
    (hn₀ : 1 ≤ n₀) (hk : 1 ≤ k) :
    ∃ (x : ℕ → ℝ) (D : ℝ → ℝ),
      atomicTest (n₀ * blockSize R) x (dilate k φ) =
        (fun u => F (u - (Real.log n₀ + R)) + D (u - (Real.log n₀ + R))) ∧
      ContDiff ℝ 2 D ∧ HasCompactSupport D ∧ SupportedIn (R + 3) D ∧
      Real.sqrt (∫ u, D u ^ 2) ≤ Real.sqrt (2 * (R + 3)) *
        synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L k n₀ ∧
      ∫ u, D u ^ 2 ≤ 2 * (R + 3) * synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L k n₀ ^ 2 ∧
      levyEnergy D ≤ synthLevy (R + 3) (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L k n₀)
          (synthLip (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L k n₀) k ∧
      ∫ u, |D u| ≤ 2 * (R + 3) * synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L k n₀ := by
  obtain ⟨hsup, hlip, hSsupp, hS2⟩ :=
    synthesis_error_bounds hφ hφ1 hφint hF hR hFR hFM hL hn₀ hk (M := M)
  set S := cellSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R)
  set e0 := synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L k n₀
  set LD := synthLip (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L k n₀
  have hk0 : 0 < k := by linarith
  set D : ℝ → ℝ := fun u => S u - F u
  have hD2 : ContDiff ℝ 2 D := hS2.sub hF
  have hFR3 : SupportedIn (R + 3) F := fun u hu => hFR u (by linarith)
  have hDsupp : SupportedIn (R + 3) D := fun u hu => by
    simp only [D, hSsupp u hu, hFR3 u hu, sub_zero]
  have hDc : HasCompactSupport D := hasCompactSupport_of_vanishes hDsupp
  have he0 : ∀ r, |D r| ≤ e0 := hsup
  have he00 : 0 ≤ e0 := (abs_nonneg _).trans (he0 0)
  have hLD : ∀ u v, |D u - D v| ≤ LD * |u - v| := fun u v => by
    have h1 := hlip u v
    have h2 := hL u v
    have e : D u - D v = (S u - S v) - (F u - F v) := by simp only [D]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have : LD * |u - v| = (M * (k * ∫ s, |deriv φ s|) +
        M * (1 / n₀) * (k * (k * ∫ s, |deriv (deriv φ) s|))) * |u - v| + L * |u - v| := by
      simp only [LD, synthLip]; ring
    rw [this]
    exact add_le_add h1 h2
  have hR3 : 0 ≤ R + 3 := by linarith
  have hN1 := integral_abs_le_of_bound hD2.continuous hDc he0 hDsupp hR3
  have hN2 : ∫ u, D u ^ 2 ≤ 2 * (R + 3) * e0 ^ 2 := by
    have := integral_sq_le_of_bound hD2.continuous hDc he0
    nlinarith
  have hLD0 : 0 ≤ LD := by
    have := hLD 1 0
    simp only [sub_zero, abs_one, mul_one] at this
    linarith [abs_nonneg (D 1 - D 0)]
  have hLev : levyEnergy D ≤ synthLevy (R + 3) e0 LD k := by
    have h := levyEnergy_le_lipschitz hD2 hDc hLD (δ := 1 / k) (one_div_pos.mpr hk0)
      (by rw [div_le_one hk0]; exact hk)
    rw [one_div_one_div] at h
    have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk
    have hC1 : 0 ≤ levyLipConstant := by
      have h2 : 0 < 1 - Real.exp (-2) := by
        have := Real.exp_lt_one_iff.mpr (show (-2 : ℝ) < 0 by norm_num); linarith
      unfold levyLipConstant
      have := div_pos (mul_pos (by norm_num : (0 : ℝ) < 8) (Real.exp_pos (-(1 / 2)))) h2
      linarith [Real.exp_pos (1 / 2)]
    have hb1 : Real.exp (1 / 2) * LD * (1 / k) * (∫ u, |D u|) ≤
        Real.exp (1 / 2) * LD * (1 / k) * (2 * (R + 3) * e0) :=
      mul_le_mul_of_nonneg_left hN1
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le hLD0) (one_div_pos.mpr hk0).le)
    have hb2 : (2 * Real.log k + levyLipConstant) * (∫ u, D u ^ 2) ≤
        (2 * Real.log k + levyLipConstant) * (2 * (R + 3) * e0 ^ 2) :=
      mul_le_mul_of_nonneg_left hN2 (by linarith)
    unfold synthLevy
    linarith
  have hsqD : Real.sqrt (∫ u, D u ^ 2) ≤ Real.sqrt (2 * (R + 3)) * e0 := by
    rw [← Real.sqrt_sq he00, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  refine ⟨synthWeights F (logNode n₀ (Real.log n₀ + R)) n₀ (cellCount n₀ R), D,
    ?_, hD2, hDc, hDsupp, hsqD, hN2, hLev, hN1⟩
  funext u
  rw [atomicTest_synthWeights hn₀ cellCount_le_block]
  simp only [D]
  ring

/-- **The synthesis bound**: the atoms of level `n₀ B` synthesize a fixed test `F` supported in
`[−R, R]` up to an explicit motion of Weil's form. -/
theorem exists_atomicTest_weilQuad_le (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hR : 0 ≤ R)
    (hFR : SupportedIn R F) (hFM : ∀ t, |F t| ≤ M) (hL : ∀ u v, |F u - F v| ≤ L * |u - v|)
    (hn₀ : 1 ≤ n₀) (hk : 1 ≤ k) :
    ∃ x : ℕ → ℝ, weilQuad (atomicTest (n₀ * blockSize R) x (dilate k φ)) ≤ weilQuad F +
      weilErr F (R + 3) (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L k n₀)
        (synthLevy (R + 3) (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L k n₀)
          (synthLip (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L k n₀) k) := by
  obtain ⟨x, D, hx, hD2, hDc, hDsupp, hsqD, hN2, hLev, hN1⟩ :=
    exists_synthesis hφ hφ1 hφint hF hR hFR hFM hL hn₀ hk
  refine ⟨x, ?_⟩
  have hFR3 : SupportedIn (R + 3) F := fun u hu => hFR u (by linarith)
  rw [hx, weilQuad_comp_sub (fun u => F u + D u)]
  exact (weilQuad_add_le hF hFc hD2 hDc hFR3 hDsupp).trans (add_le_add le_rfl
    (weilErr_mono (F := F) hsqD hN2 hLev (integral_nonneg fun u => abs_nonneg _) hN1))

end Synthesis2

/-! ### Asymptotics -/

section Asymptotics

theorem tendsto_log_mul_rpow_neg {α : ℝ} (hα : 0 < α) :
    Tendsto (fun y : ℝ => Real.log y * y ^ (-α)) atTop (𝓝 0) := by
  refine ((isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [Real.rpow_neg hy.le, div_eq_mul_inv]

/-- **Overlap growth**: dilations `κ_N → ∞` (widths `1/κ_N → 0`) whose overlap ratio `N/κ_N` beats
`√(log κ_N)`, i.e. `(κ_N/N)² log κ_N → 0`. -/
def OverlapGrowth (κ : ℕ → ℝ) : Prop :=
  Tendsto κ atTop atTop ∧ Tendsto (fun N : ℕ => (κ N / N) ^ 2 * Real.log (κ N)) atTop (𝓝 0)

/-- **The synthesis errors vanish** under overlap growth: along the levels `n₀ B`, with `k = κ_{n₀B}`,
the supremum error and the Lévy bound tend to `0`. -/
theorem tendsto_synth {κ : ℕ → ℝ} (hκ : OverlapGrowth κ) {B : ℕ} (hB : 1 ≤ B)
    (A0 A1 A2 M L R' : ℝ) :
    Tendsto (fun n : ℕ => synthErr A0 A1 M L (κ (n * B)) n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => synthLevy R' (synthErr A0 A1 M L (κ (n * B)) n)
        (synthLip A1 A2 M L (κ (n * B)) n) (κ (n * B))) atTop (𝓝 0) := by
  obtain ⟨hk, hkl⟩ := hκ
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  set K : ℕ → ℝ := fun n => κ (n * B)
  set r : ℕ → ℝ := fun n => κ (n * B) / ((n * B : ℕ) : ℝ)
  have hK : Tendsto K atTop atTop := hk.comp hNB
  have hrl : Tendsto (fun n => r n ^ 2 * Real.log (K n)) atTop (𝓝 0) := hkl.comp hNB
  have hlogK : Tendsto (fun n => Real.log (K n)) atTop atTop := Real.tendsto_log_atTop.comp hK
  have hinv : Tendsto (fun n => 1 / K n) atTop (𝓝 0) := by
    simp only [one_div]
    exact hK.inv_tendsto_atTop
  have hlinv : Tendsto (fun n => (1 / K n) ^ 2 * Real.log (K n)) atTop (𝓝 0) := by
    refine ((tendsto_log_mul_rpow_neg two_pos).comp hK).congr' ?_
    filter_upwards [hK.eventually_gt_atTop 0] with n hn
    simp only [Function.comp]
    rw [Real.rpow_neg hn.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  -- eventually `K ≥ 1`, `n ≥ 1`
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ K n ∧ 1 ≤ n := (hK.eventually_ge_atTop 1).and
    (eventually_ge_atTop 1)
  have hr0 : ∀ᶠ n : ℕ in atTop, 0 ≤ r n := by
    filter_upwards [hev] with n ⟨h1, _⟩
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  -- `r → 0`, from `r² log K → 0` and `log K → ∞`
  have hr2 : Tendsto (fun n => r n ^ 2) atTop (𝓝 0) := by
    refine (hrl.div_atTop hlogK).congr' ?_
    filter_upwards [hlogK.eventually_gt_atTop 0] with n hn
    field_simp
  have hr : Tendsto r atTop (𝓝 0) := by
    have := hr2.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr' ?_
    filter_upwards [hr0] with n hn
    exact Real.sqrt_sq hn
  set E : ℕ → ℝ := fun n => M * A1 * B * r n + L * A0 * (1 / K n)
  have hE : Tendsto E atTop (𝓝 0) := by
    have := (hr.const_mul (M * A1 * B)).add (hinv.const_mul (L * A0))
    simpa [E] using this
  have he0 : ∀ᶠ n : ℕ in atTop, synthErr A0 A1 M L (K n) n = E n := by
    filter_upwards [hev] with n ⟨_, hn⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    simp only [synthErr, E, r, K]
    push_cast
    field_simp
  refine ⟨hE.congr' (he0.mono fun n h => h.symm), ?_⟩
  -- the Lévy bound
  have hLE : Tendsto (fun n => Real.log (K n) * E n ^ 2) atTop (𝓝 0) := by
    have hup := ((hrl.const_mul (2 * (M * A1 * B) ^ 2)).add
      (hlinv.const_mul (2 * (L * A0) ^ 2)))
    simp only [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hev] with n ⟨h1, _⟩
      exact mul_nonneg (Real.log_nonneg h1) (sq_nonneg _)
    · filter_upwards [hev] with n ⟨h1, _⟩
      have hl := Real.log_nonneg h1
      have : E n ^ 2 ≤ 2 * (M * A1 * B) ^ 2 * r n ^ 2 + 2 * (L * A0) ^ 2 * (1 / K n) ^ 2 := by
        simp only [E]
        nlinarith [sq_nonneg (M * A1 * B * r n - L * A0 * (1 / K n))]
      nlinarith
  set G : ℕ → ℝ := fun n => M * A1 + M * A2 * B * r n + L * (1 / K n)
  have hG : Tendsto G atTop (𝓝 (M * A1 + M * A2 * B * 0 + L * 0)) :=
    (tendsto_const_nhds.add (hr.const_mul (M * A2 * B))).add (hinv.const_mul L)
  set V : ℕ → ℝ := fun n => Real.exp (1 / 2) * G n * (2 * R' * E n) +
    (2 * (Real.log (K n) * E n ^ 2) * (2 * R') + levyLipConstant * (2 * R' * E n ^ 2))
  have hV : Tendsto V atTop (𝓝 0) := by
    have h1 := (hG.const_mul (Real.exp (1 / 2))).mul (hE.const_mul (2 * R'))
    have h2 := ((hLE.const_mul 2).mul_const (2 * R')).add
      (((hE.pow 2).const_mul (2 * R')).const_mul levyLipConstant)
    have := h1.add h2
    simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    exact this
  refine hV.congr' ?_
  filter_upwards [hev, he0] with n ⟨h1, hn⟩ he
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hK0 : (0 : ℝ) < K n := by linarith
  have hκ0 : κ (n * B) ≠ 0 := hK0.ne'
  have hLD : synthLip A1 A2 M L (K n) n * (1 / K n) = G n := by
    simp only [synthLip, G, r, K]
    push_cast
    field_simp
  simp only [synthLevy, V]
  rw [he, show Real.exp (1 / 2) * synthLip A1 A2 M L (K n) n * (1 / K n) * (2 * R' * E n) =
    Real.exp (1 / 2) * (synthLip A1 A2 M L (K n) n * (1 / K n)) * (2 * R' * E n) by ring, hLD]
  ring

/-- Polynomial widths `N^{−θ}`, `0 < θ < 1`, have overlap growth. -/
theorem overlapGrowth_rpow {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    OverlapGrowth fun N : ℕ => (N : ℝ) ^ θ := by
  refine ⟨(tendsto_rpow_atTop hθ0).comp tendsto_natCast_atTop_atTop, ?_⟩
  have h := ((tendsto_log_mul_rpow_neg (α := 2 * (1 - θ)) (by linarith)).comp
    tendsto_natCast_atTop_atTop).const_mul θ
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp]
  rw [Real.log_rpow hN0, ← Real.rpow_sub_one hN0.ne', ← Real.rpow_natCast,
    ← Real.rpow_mul hN0.le]
  push_cast
  rw [show (θ - 1) * 2 = -(2 * (1 - θ)) by ring]
  ring

/-- Widths `(log N)^α/N`, `α > 1/2` — overlap ratio `(log N)^α` — have overlap growth. -/
theorem overlapGrowth_log {α : ℝ} (hα : 1 / 2 < α) :
    OverlapGrowth fun N : ℕ => (N : ℝ) / Real.log N ^ α := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hα0 : 0 < α := by linarith
  -- `κ_N = N/(log N)^α → ∞`
  have hκ : Tendsto (fun N : ℕ => (N : ℝ) / Real.log N ^ α) atTop atTop := by
    have ho := (isLittleO_log_rpow_rpow_atTop α one_pos).tendsto_div_nhds_zero
    have hpos : ∀ᶠ y : ℝ in atTop, 0 < Real.log y ^ α / y ^ (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop 1] with y hy
      exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hy) α) (by positivity)
    have hinv := (tendsto_nhdsWithin_iff.mpr ⟨ho, hpos⟩).inv_tendsto_nhdsGT_zero
    refine (hinv.comp tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp, Real.rpow_one, Pi.inv_apply, inv_div]
  refine ⟨hκ, ?_⟩
  have hup : Tendsto (fun N : ℕ => Real.log N ^ (-(2 * α - 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hκ.eventually_ge_atTop 1] with N h1
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg h1)
  · filter_upwards [hκ.eventually_ge_atTop 1, hlog.eventually_ge_atTop 1,
      eventually_ge_atTop 1] with N h1 hl hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hl0 : 0 < Real.log N := by linarith
    have hpow : 1 ≤ Real.log N ^ α := Real.one_le_rpow hl hα0.le
    have hpow0 : 0 < Real.log N ^ α := by linarith
    have hκN : (N : ℝ) / Real.log N ^ α ≤ N := div_le_self hN0.le hpow
    have hlk : Real.log ((N : ℝ) / Real.log N ^ α) ≤ Real.log N :=
      Real.log_le_log (by linarith) hκN
    have hsq : ((N : ℝ) / Real.log N ^ α / N) ^ 2 = Real.log N ^ (-(2 * α)) := by
      rw [div_div_cancel_left' hN0.ne', Real.rpow_neg hl0.le, inv_pow,
        ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
      push_cast
      rw [mul_comm α 2]
    rw [hsq, show -(2 * α - 1) = -(2 * α) + 1 by ring, Real.rpow_add hl0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hlk (Real.rpow_nonneg hl0.le _)

/-- `weilErr` vanishes with its arguments. -/
theorem tendsto_weilErr (F : ℝ → ℝ) (R' : ℝ) {e V : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hV : Tendsto V atTop (𝓝 0)) : Tendsto (fun n => weilErr F R' (e n) (V n)) atTop (𝓝 0) := by
  unfold weilErr
  have hsV : Tendsto (fun n => Real.sqrt (V n)) atTop (𝓝 0) := by
    simpa using hV.sqrt
  have := (((((((((tendsto_const_nhds (x := Real.sqrt (∫ u, F u ^ 2))).mul (he.const_mul (Real.sqrt (2 * R')))).const_mul 2).add
    ((he.pow 2).const_mul (2 * R'))).const_mul (2 * |gammaHardyPhaseRate 0|)).add
    (((hsV.const_mul (Real.sqrt (levyEnergy F))).const_mul 2).add hV)).add
    (((((tendsto_const_nhds (x := Real.sqrt (∫ u, F u ^ 2))).mul (he.const_mul (Real.sqrt (2 * R')))).const_mul 2).add
    ((he.pow 2).const_mul (2 * R'))).const_mul (2 * primeMass R'))).add
    ((he.const_mul (2 * R')).const_mul
      (4 * Real.cosh (R' / 2) * (|coshHalfMoment F| + |sinhHalfMoment F|)))).add
    (((he.const_mul (2 * R')).pow 2).const_mul (4 * Real.cosh (R' / 2) ^ 2)))
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at this
  refine this.congr' (Eventually.of_forall fun n => ?_)
  ring

end Asymptotics

/-! ### The critical exponent -/

section CriticalExponent

variable {φ : ℝ → ℝ} {θ : ℝ}

/-- An atomic test with a dilated profile is a test. -/
theorem atomicTest_dilate_mem (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ) {k : ℝ} (hk : 0 < k)
    (N : ℕ) (x : ℕ → ℝ) :
    ContDiff ℝ 2 (atomicTest N x (dilate k φ)) ∧ HasCompactSupport (atomicTest N x (dilate k φ)) := by
  refine ⟨contDiff_atomicTest (contDiff_dilate hφ k) N x,
    hasCompactSupport_of_vanishes (B := Real.log N + 1 / k) fun u hu => ?_⟩
  unfold atomicTest
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn1 := (Finset.mem_Icc.mp hn)
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hn1.2)
  rw [dilate_vanishes hφ1 hk (by
    have := abs_sub_abs_le_abs_sub u (Real.log n)
    rw [abs_of_nonneg hl0] at this
    linarith), mul_zero]

/-- **The overlap law**: for every `C²` profile `φ` supported in `[−1, 1]` with `∫ φ = 1` and every
dilation sequence `κ` of overlap growth, RH holds iff for all large `N` Weil's form is nonnegative on
every atomic test `Σ_{n ≤ N} x_n φ_κ(· − log n)` of width `1/κ_N`. -/
theorem riemannHypothesis_iff_atomicFamilies_nonneg_of_growth {κ : ℕ → ℝ} (hκ : OverlapGrowth κ)
    (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate (κ N) φ)) := by
  constructor
  · intro hRH
    filter_upwards [hκ.1.eventually_gt_atTop 0] with N hk x
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ hφ1 hk N x
    exact RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH _ h2 hc
  · intro H
    by_contra hRH
    rw [RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive] at hRH
    push Not at hRH
    obtain ⟨g, hg, hgc, hneg⟩ := hRH
    change weilQuad g < 0 at hneg
    -- a radius, a bound and a Lipschitz constant for `g`
    obtain ⟨R0, hR0⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    set R := max R0 0
    have hR : 0 ≤ R := le_max_right _ _
    have hgR : SupportedIn R g := fun u hu => by
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hR0 hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith [le_max_left R0 0]
    obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
    have hM' : ∀ t, |g t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
    obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
    have hL : ∀ u v, |g u - g v| ≤ C * |u - v| := fun u v => by
      simpa [Real.dist_eq] using hC.dist_le_mul u v
    -- the synthesis errors vanish
    set B := blockSize R
    have hB : 1 ≤ B := by
      have h := Nat.le_ceil (1 + Real.exp (2 * R))
      have : (1 : ℝ) ≤ B := by
        have := Real.exp_pos (2 * R)
        simp only [B, blockSize] at h ⊢
        linarith
      exact_mod_cast this
    obtain ⟨he, hV⟩ := tendsto_synth hκ hB (∫ s, |φ s|) (∫ s, |deriv φ s|)
      (∫ s, |deriv (deriv φ) s|) M C (R + 3)
    have hErr := tendsto_weilErr g (R + 3) he hV
    have h1 := hErr.eventually (gt_mem_nhds (show (0 : ℝ) < -weilQuad g by linarith))
    have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
    have h2 := hNB.eventually H
    have h3 := hNB.eventually (hκ.1.eventually_ge_atTop 1)
    obtain ⟨n, hn1, hn2, hk, hn3⟩ := (h1.and (h2.and (h3.and (eventually_ge_atTop 1)))).exists
    obtain ⟨x, hx⟩ := exists_atomicTest_weilQuad_le hφ hφ1 hφint hg hgc hR hgR hM' hL hn3 hk
    have := hn2 x
    linarith

/-- **The critical exponent law**: for every `0 < θ < 1`, RH holds iff for all large `N` Weil's
form is nonnegative on the atomic families of width `N^{−θ}`. -/
theorem riemannHypothesis_iff_atomicFamilies_nonneg (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) ^ θ) φ)) :=
  riemannHypothesis_iff_atomicFamilies_nonneg_of_growth (overlapGrowth_rpow hθ0 hθ1) hφ hφ1 hφint

/-- **The logarithmic overlap law**: for every `α > 1/2`, RH holds iff for all large `N` Weil's form
is nonnegative on the atomic families of width `(log N)^α/N`, overlap ratio `≍ (log N)^α`. -/
theorem riemannHypothesis_iff_atomicFamilies_nonneg_log {α : ℝ} (hα : 1 / 2 < α)
    (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / Real.log N ^ α) φ)) :=
  riemannHypothesis_iff_atomicFamilies_nonneg_of_growth (overlapGrowth_log hα) hφ hφ1 hφint

end CriticalExponent

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
