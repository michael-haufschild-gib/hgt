import GaloisForLFunctions.RHTower.OddSectorPoleWeightAtMostOne
import GaloisForLFunctions.RHTower.WeilPolarConeFirstVariation
import GaloisForLFunctions.RHTower.EvenSectorStripPositivity
import GaloisForLFunctions.RHTower.WeilPositivityConductorObstruction

/-!
# Pole-free far-bump corrections of even tests

Let `φ` be the even bump of the far-bump construction, `k = φ ⋆ φ̃`, `J = ∫ φ(x) e^{−x/2} dx`, and
`e_a = φ(· − a) + φ(· + a)` the even far bump.  For a real even `C²` test `g` supported in
`[−R, R]` put `P = ∫ g(x) e^{−x/2} dx` and `c_a = P / ((e^{−a/2} + e^{a/2}) J)`.  Then
`G_a = g − c_a e_a` is even and pole-free (`∫ G_a e^{−x/2} = 0`), so Weil positivity on even
pole-free tests (`WeilPositiveEvenPolar`, implied by even positivity at any pole weight) gives
`W(G_a) ≥ 0`.

**Theorem** (`realWeil_ge_of_weilPositiveEvenPolar`).  There is `M ≥ 0` such that for every
`a ≥ R + 1`

`W(g) ≥ 2P² − 4 c_a T(a) + 2 c_a² S(a) − M (|c_a| + c_a²)`,

where `S(a) = Σ_{n ≥ 2} lam(n) n^{−1/2} k(log n − 2a)` is the far-bump window sum and
`T(a) = Σ_{n ≥ 2} lam(n) n^{−1/2} h(log n − a)` the cross window sum, `h = g ⋆ φ̃`.

Proof.  Expand the quadratic form along `g − c_a e_a`: the prime pairing by bilinearity of the
cross-correlation (the reflected cross term equals the direct one), the archimedean energy by
polarization, `A(g − c e) = (1 + c) A(g) − c A(g + e) + (c + c²) A(e)`.  The atoms of `g ⋆ ẽ_a`
are `2T(a)` once `a ≥ R + 1`, those of `e_a ⋆ ẽ_a` are `2S(a)`, and `A(e_a)`, `A(g + e_a)` are
bounded uniformly in `a` because `|ê_a| ≤ 2|φ̂|`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open OddSector WeilOneSided WeilPoleWeight

/-! ## The even far bump -/

/-- The even far bump `φ(x − a) + φ(x + a)`. -/
def evenFarBump (a x : ℝ) : ℝ := farBump (x - a) + farBump (x + a)

theorem evenFarBump_neg (a x : ℝ) : evenFarBump a (-x) = evenFarBump a x := by
  unfold evenFarBump
  rw [show -x - a = -(x + a) by ring, show -x + a = -(x - a) by ring, farBump_neg, farBump_neg]
  ring

theorem contDiff_evenFarBump (a : ℝ) : ContDiff ℝ 2 (evenFarBump a) := by
  unfold evenFarBump
  exact ((contDiff_farBump 2).comp (contDiff_id.sub contDiff_const)).add
    ((contDiff_farBump 2).comp (contDiff_id.add contDiff_const))

theorem continuous_evenFarBump (a : ℝ) : Continuous (evenFarBump a) :=
  (contDiff_evenFarBump a).continuous

theorem hasCompactSupport_evenFarBump (a : ℝ) : HasCompactSupport (evenFarBump a) := by
  unfold evenFarBump
  exact (hasCompactSupport_farBump.comp_homeomorph (Homeomorph.subRight a)).add
    (hasCompactSupport_farBump.comp_homeomorph (Homeomorph.addRight a))

theorem evenFarBump_eq_zero {a x : ℝ} (ha : 0 ≤ a) (hx : a + 1 < |x|) : evenFarBump a x = 0 := by
  have hr := nodeBump_rOut_le 2
  have h1 := abs_sub_abs_le_abs_sub x a
  have h2 := abs_sub_abs_le_abs_sub x (-a)
  rw [abs_of_nonneg ha] at h1
  rw [abs_neg, abs_of_nonneg ha, sub_neg_eq_add] at h2
  unfold evenFarBump
  rw [farBump_eq_zero (by linarith), farBump_eq_zero (by linarith), add_zero]

/-- The exponential moment of the even far bump: `(e^{−a/2} + e^{a/2}) J`. -/
theorem integral_evenFarBump_mul_exp (a : ℝ) :
    ∫ x, evenFarBump a x * Real.exp (-x / 2) =
      (Real.exp (-a / 2) + Real.exp (a / 2)) * farJ := by
  have hi : ∀ c : ℝ, Integrable fun x => farBump (x - c) * Real.exp (-x / 2) := fun c =>
    ((continuous_farBump.comp (continuous_id.sub continuous_const)).mul (by fun_prop)
      ).integrable_of_hasCompactSupport
      (hasCompactSupport_farBump.comp_homeomorph (Homeomorph.subRight c)).mul_right
  have h1 : ∫ x, farBump (x - a) * Real.exp (-x / 2) = Real.exp (-a / 2) * farJ := by
    have key := integral_sub_right_eq_self (μ := volume)
      (fun x => farBump x * Real.exp (-(x + a) / 2)) a
    simp only [sub_add_cancel] at key
    rw [key]
    unfold farJ
    rw [← integral_const_mul]
    congr 1; funext x
    rw [show -(x + a) / 2 = -a / 2 + -x / 2 by ring, Real.exp_add]
    ring
  have h2 : ∫ x, farBump (x + a) * Real.exp (-x / 2) = Real.exp (a / 2) * farJ := by
    have key := integral_add_right_eq_self (μ := volume)
      (fun x => farBump x * Real.exp (-(x - a) / 2)) a
    simp only [add_sub_cancel_right] at key
    rw [key]
    unfold farJ
    rw [← integral_const_mul]
    congr 1; funext x
    rw [show -(x - a) / 2 = a / 2 + -x / 2 by ring, Real.exp_add]
    ring
  unfold evenFarBump
  have e : (fun x => (farBump (x - a) + farBump (x + a)) * Real.exp (-x / 2)) =
      fun x => farBump (x - a) * Real.exp (-x / 2) + farBump (x + a) * Real.exp (-x / 2) := by
    funext x; ring
  have hi2 : Integrable fun x => farBump (x + a) * Real.exp (-x / 2) := by
    refine (hi (-a)).congr (Eventually.of_forall fun x => ?_)
    simp only [sub_neg_eq_add]
  rw [e, integral_add (hi a) hi2, h1, h2]
  ring

theorem evenFarBumpC_eq (a : ℝ) :
    (fun u => ((evenFarBump a u : ℝ) : ℂ)) = fun u => ∑ k : Fin 2, (![1, 1] k : ℂ) *
      (fun v => ((farBump v : ℝ) : ℂ)) (u - ![a, -a] k) := by
  funext u
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, evenFarBump]
  push_cast
  rw [sub_neg_eq_add]
  ring

theorem norm_paperFT_evenFarBump_le (a r : ℝ) :
    ‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ≤
      4 * ‖paperFT (fun u => (nodeBump 2 u : ℂ)) r‖ := by
  rw [evenFarBumpC_eq]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _
    (Complex.continuous_ofReal.comp continuous_farBump)
    (hasCompactSupport_farBump.comp_left Complex.ofReal_zero) r).trans ?_
  have hs : (∑ k : Fin 2, ‖(![1, 1] k : ℂ)‖) = 2 := by simp [Fin.sum_univ_two]; norm_num
  rw [hs]
  have : ‖paperFT (Complex.ofReal ∘ farBump) r‖ = ‖paperFT (fun u => (nodeBump 2 u : ℂ)) r‖ :=
    rfl
  rw [this]
  nlinarith [norm_nonneg (paperFT (fun u => (nodeBump 2 u : ℂ)) r)]

/-- The autocorrelation of the even far bump. -/
theorem crossCorr_evenFarBump (a y : ℝ) :
    crossCorr (evenFarBump a) (evenFarBump a) y =
      2 * farKernel y + farKernel (y - 2 * a) + farKernel (y + 2 * a) := by
  unfold crossCorr evenFarBump farKernel crossCorr
  have i1 : Integrable fun t => farBump (t - a) * farBump (t - y - a) := by
    have := (integrable_farBump_mul y).comp_sub_right a
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t - a) * farBump (t - a - y) = _
    rw [show t - a - y = t - y - a by ring]
  have i2 : Integrable fun t => farBump (t - a) * farBump (t - y + a) := by
    have := (integrable_farBump_mul (y - 2 * a)).comp_sub_right a
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t - a) * farBump (t - a - (y - 2 * a)) = _
    rw [show t - a - (y - 2 * a) = t - y + a by ring]
  have i3 : Integrable fun t => farBump (t + a) * farBump (t - y - a) := by
    have := (integrable_farBump_mul (y + 2 * a)).comp_add_right a
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t + a) * farBump (t + a - (y + 2 * a)) = _
    rw [show t + a - (y + 2 * a) = t - y - a by ring]
  have i4 : Integrable fun t => farBump (t + a) * farBump (t - y + a) := by
    have := (integrable_farBump_mul y).comp_add_right a
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t + a) * farBump (t + a - y) = _
    rw [show t + a - y = t - y + a by ring]
  have e : (fun t => (farBump (t - a) + farBump (t + a)) *
      (farBump (t - y - a) + farBump (t - y + a))) =
      fun t => farBump (t - a) * farBump (t - y - a) + farBump (t - a) * farBump (t - y + a) +
        farBump (t + a) * farBump (t - y - a) + farBump (t + a) * farBump (t - y + a) := by
    funext t; ring
  rw [e, integral_add (f := fun t => farBump (t - a) * farBump (t - y - a) +
      farBump (t - a) * farBump (t - y + a) + farBump (t + a) * farBump (t - y - a))
      (g := fun t => farBump (t + a) * farBump (t - y + a)) ((i1.add i2).add i3) i4,
    integral_add (f := fun t => farBump (t - a) * farBump (t - y - a) +
      farBump (t - a) * farBump (t - y + a))
      (g := fun t => farBump (t + a) * farBump (t - y - a)) (i1.add i2) i3,
    integral_add i1 i2]
  have j1 : ∫ t, farBump (t - a) * farBump (t - y - a) = ∫ s, farBump s * farBump (s - y) := by
    rw [← integral_sub_right_eq_self (fun s => farBump s * farBump (s - y)) a]
    congr 1; funext t; congr 2; ring
  have j2 : ∫ t, farBump (t - a) * farBump (t - y + a) =
      ∫ s, farBump s * farBump (s - (y - 2 * a)) := by
    rw [← integral_sub_right_eq_self (fun s => farBump s * farBump (s - (y - 2 * a))) a]
    congr 1; funext t; congr 2; ring
  have j3 : ∫ t, farBump (t + a) * farBump (t - y - a) =
      ∫ s, farBump s * farBump (s - (y + 2 * a)) := by
    rw [← integral_add_right_eq_self (fun s => farBump s * farBump (s - (y + 2 * a))) a]
    congr 1; funext t; congr 2; ring
  have j4 : ∫ t, farBump (t + a) * farBump (t - y + a) = ∫ s, farBump s * farBump (s - y) := by
    rw [← integral_add_right_eq_self (fun s => farBump s * farBump (s - y)) a]
    congr 1; funext t; congr 2; ring
  rw [j1, j2, j3, j4]
  ring

/-- At the atoms only the cross terms survive: `2 k(log n − 2a)`. -/
theorem crossCorr_evenFarBump_log_add {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 2 ≤ n) :
    crossCorr (evenFarBump a) (evenFarBump a) (Real.log n) +
      crossCorr (evenFarBump a) (evenFarBump a) (-Real.log n) =
      2 * farKernel (Real.log n - 2 * a) := by
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hr := two_mul_rOut_lt_log_two
  have hr0 := (nodeBump 2).rOut_pos
  rw [crossCorr_evenFarBump, crossCorr_evenFarBump]
  have z1 : farKernel (Real.log n) = 0 :=
    farKernel_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith)
  have z2 : farKernel (Real.log n + 2 * a) = 0 :=
    farKernel_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith)
  have z3 : farKernel (-Real.log n) = 0 := by rw [farKernel_neg, z1]
  have z4 : farKernel (-Real.log n - 2 * a) = 0 := by
    rw [show -Real.log n - 2 * a = -(Real.log n + 2 * a) by ring, farKernel_neg, z2]
  have e5 : farKernel (-Real.log n + 2 * a) = farKernel (Real.log n - 2 * a) := by
    rw [show -Real.log n + 2 * a = -(Real.log n - 2 * a) by ring, farKernel_neg]
  rw [z1, z2, z3, z4, e5]
  ring

theorem atomPairing_evenFarBump (lam : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    atomPairing lam (crossCorr (evenFarBump a) (evenFarBump a)) = 2 * farSum lam a := by
  unfold atomPairing farSum
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  split_ifs with hn
  · rw [crossCorr_evenFarBump_log_add ha hn]; ring
  · ring

/-! ## The cross kernel `h = g ⋆ φ̃` -/

/-- `h(y) = ∫ g(t) φ(t − y) dt`. -/
def farCrossKernel (g : ℝ → ℝ) (y : ℝ) : ℝ := crossCorr g farBump y

/-- `T(a) = Σ_{n ≥ 2} lam(n) n^{−1/2} h(log n − a)`. -/
def farCrossSum (lam : ℕ → ℝ) (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) * farCrossKernel g (Real.log n - a)

theorem farCrossKernel_neg {g : ℝ → ℝ} (hge : ∀ x, g (-x) = g x) (y : ℝ) :
    farCrossKernel g (-y) = farCrossKernel g y := by
  unfold farCrossKernel crossCorr
  rw [← integral_neg_eq_self (fun t => g t * farBump (t - -y))]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show g (-t) * farBump (-t - -y) = g t * farBump (t - y)
  rw [hge, show -t - -y = -(t - y) by ring, farBump_neg]

theorem farCrossKernel_eq_zero {g : ℝ → ℝ} {R : ℝ} (hgs : ∀ x, R < |x| → g x = 0) {y : ℝ}
    (hy : R + 1 < |y|) : farCrossKernel g y = 0 := by
  have hr := nodeBump_rOut_le 2
  exact crossCorr_eq_zero (R₂ := 1 / 12) hgs (fun t ht => farBump_eq_zero (by linarith))
    (by linarith)

theorem crossCorr_evenFarBump_right {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (a y : ℝ) :
    crossCorr g (evenFarBump a) y = farCrossKernel g (y + a) + farCrossKernel g (y - a) := by
  unfold crossCorr evenFarBump farCrossKernel crossCorr
  have i1 : Integrable fun t => g t * farBump (t - y - a) := by
    refine (integrable_translate_prod hg hgc continuous_farBump (y + a)).congr
      (Eventually.of_forall fun t => ?_)
    show g t * farBump (t - (y + a)) = g t * farBump (t - y - a)
    rw [show t - (y + a) = t - y - a by ring]
  have i2 : Integrable fun t => g t * farBump (t - y + a) := by
    refine (integrable_translate_prod hg hgc continuous_farBump (y - a)).congr
      (Eventually.of_forall fun t => ?_)
    show g t * farBump (t - (y - a)) = g t * farBump (t - y + a)
    rw [show t - (y - a) = t - y + a by ring]
  have e : (fun t => g t * (farBump (t - y - a) + farBump (t - y + a))) =
      fun t => g t * farBump (t - y - a) + g t * farBump (t - y + a) := by
    funext t; ring
  rw [e, integral_add i1 i2]
  congr 1
  · congr 1; funext t; congr 2; ring
  · congr 1; funext t; congr 2; ring

/-- The atoms of `g ⋆ ẽ_a` are `2T(a)` once the far bump has left the support of `g`. -/
theorem atomPairing_crossCorr_evenFarBump (lam : ℕ → ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hge : ∀ x, g (-x) = g x) {R : ℝ} (hR : 0 ≤ R)
    (hgs : ∀ x, R < |x| → g x = 0) {a : ℝ} (ha : R + 1 ≤ a) :
    atomPairing lam (crossCorr g (evenFarBump a)) = 2 * farCrossSum lam g a := by
  unfold atomPairing farCrossSum
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  split_ifs with hn
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    rw [crossCorr_evenFarBump_right hg hgc, crossCorr_evenFarBump_right hg hgc]
    have z1 : farCrossKernel g (Real.log n + a) = 0 :=
      farCrossKernel_eq_zero hgs (by rw [abs_of_pos (by linarith)]; linarith)
    have z2 : farCrossKernel g (-Real.log n - a) = 0 := by
      rw [show -Real.log n - a = -(Real.log n + a) by ring, farCrossKernel_neg hge, z1]
    have e3 : farCrossKernel g (-Real.log n + a) = farCrossKernel g (Real.log n - a) := by
      rw [show -Real.log n + a = -(Real.log n - a) by ring, farCrossKernel_neg hge]
    rw [z1, z2, e3]
    ring
  · ring

/-! ## The archimedean energy -/

/-- The archimedean energy `(1/2π) ∫ |F̂(r)|² G(r) dr` of a real test. -/
def farArch (F : ℝ → ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 * EF.gammaBracket r

theorem tsupport_ofReal_subset_Icc_of_abs_gt {F : ℝ → ℝ} {R : ℝ} (hF : ∀ x, R < |x| → F x = 0) :
    tsupport (fun u => (F u : ℂ)) ⊆ Icc (-R) R := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  rw [Function.mem_support] at hx
  by_contra hc
  rw [mem_Icc, not_and_or, not_le, not_le] at hc
  apply hx
  have hR : R < |x| := lt_abs.mpr (by rcases hc with h | h <;> [right; left] <;> linarith)
  rw [hF x hR, Complex.ofReal_zero]

theorem hasCompactSupport_of_abs_gt_eq_zero {F : ℝ → ℝ} {R : ℝ} (hF : ∀ x, R < |x| → F x = 0) :
    HasCompactSupport F :=
  HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun x hx => by
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    exact hF x (lt_abs.mpr (by rcases hx with h | h <;> [right; left] <;> linarith))

theorem integrable_normSq_paperFT_ofReal_mul_gammaBracket {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {R : ℝ}
    (hFs : ∀ x, R < |x| → F x = 0) :
    Integrable fun r : ℝ => ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 * EF.gammaBracket r := by
  have h := integrable_normSq_paperFT_mul_arch (contDiff_ofReal_comp hF)
    (tsupport_ofReal_subset_Icc_of_abs_gt hFs)
  refine h.congr (Eventually.of_forall fun r => ?_)
  show ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 * archimedeanWeilSymbol (r / (2 * π)) =
    ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 * EF.gammaBracket r
  rw [gammaBracket_eq_archimedeanWeilSymbol]

theorem norm_sub_ofReal_mul_sq (u v : ℂ) (c : ℝ) :
    ‖u - (c : ℂ) * v‖ ^ 2 = (1 + c) * ‖u‖ ^ 2 - c * ‖u + v‖ ^ 2 + (c + c ^ 2) * ‖v‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem paperFT_ofReal_add_smul {F₁ F₂ : ℝ → ℝ} (h₁ : Continuous F₁) (hc₁ : HasCompactSupport F₁)
    (h₂ : Continuous F₂) (hc₂ : HasCompactSupport F₂) (a b r : ℝ) :
    paperFT (fun u => ((a * F₁ u + b * F₂ u : ℝ) : ℂ)) r =
      a * paperFT (fun u => (F₁ u : ℂ)) r + b * paperFT (fun u => (F₂ u : ℂ)) r := by
  have := paperFT_smul_add_smul (a : ℂ) (b : ℂ) (r : ℂ)
    (integrable_ofReal_mul_cexp_of_hasCompactSupport h₁ hc₁ r)
    (integrable_ofReal_mul_cexp_of_hasCompactSupport h₂ hc₂ r)
  rw [← this]
  congr 1; funext u; push_cast; ring

/-- **Polarization of the archimedean energy.** -/
theorem farArch_sub_smul {F₁ F₂ : ℝ → ℝ} (h₁ : ContDiff ℝ 2 F₁) (h₂ : ContDiff ℝ 2 F₂) {R : ℝ}
    (hs₁ : ∀ x, R < |x| → F₁ x = 0) (hs₂ : ∀ x, R < |x| → F₂ x = 0) (c : ℝ) :
    farArch (fun x => F₁ x - c * F₂ x) =
      (1 + c) * farArch F₁ - c * farArch (fun x => F₁ x + F₂ x) + (c + c ^ 2) * farArch F₂ := by
  have hc₁ := hasCompactSupport_of_abs_gt_eq_zero hs₁
  have hc₂ := hasCompactSupport_of_abs_gt_eq_zero hs₂
  have hs₃ : ∀ x, R < |x| → F₁ x + F₂ x = 0 := fun x hx => by rw [hs₁ x hx, hs₂ x hx, add_zero]
  have hI₁ := integrable_normSq_paperFT_ofReal_mul_gammaBracket h₁ hs₁
  have hI₂ := integrable_normSq_paperFT_ofReal_mul_gammaBracket h₂ hs₂
  have hI₃ := integrable_normSq_paperFT_ofReal_mul_gammaBracket (h₁.add h₂) hs₃
  have hpt : ∀ r : ℝ, ‖paperFT (fun u => ((F₁ u - c * F₂ u : ℝ) : ℂ)) r‖ ^ 2 =
      (1 + c) * ‖paperFT (fun u => (F₁ u : ℂ)) r‖ ^ 2 -
        c * ‖paperFT (fun u => ((F₁ u + F₂ u : ℝ) : ℂ)) r‖ ^ 2 +
        (c + c ^ 2) * ‖paperFT (fun u => (F₂ u : ℂ)) r‖ ^ 2 := by
    intro r
    have e1 : paperFT (fun u => ((F₁ u - c * F₂ u : ℝ) : ℂ)) r =
        paperFT (fun u => (F₁ u : ℂ)) r - (c : ℂ) * paperFT (fun u => (F₂ u : ℂ)) r := by
      have := paperFT_ofReal_add_smul h₁.continuous hc₁ h₂.continuous hc₂ 1 (-c) r
      rw [show (fun u => ((F₁ u - c * F₂ u : ℝ) : ℂ)) =
        fun u => ((1 * F₁ u + -c * F₂ u : ℝ) : ℂ) by funext u; push_cast; ring, this]
      push_cast; ring
    have e2 : paperFT (fun u => ((F₁ u + F₂ u : ℝ) : ℂ)) r =
        paperFT (fun u => (F₁ u : ℂ)) r + paperFT (fun u => (F₂ u : ℂ)) r := by
      have := paperFT_ofReal_add_smul h₁.continuous hc₁ h₂.continuous hc₂ 1 1 r
      rw [show (fun u => ((F₁ u + F₂ u : ℝ) : ℂ)) =
        fun u => ((1 * F₁ u + 1 * F₂ u : ℝ) : ℂ) by funext u; push_cast; ring, this]
      push_cast; ring
    rw [e1, e2, norm_sub_ofReal_mul_sq]
  unfold farArch
  have e : (fun r : ℝ => ‖paperFT (fun u => ((F₁ u - c * F₂ u : ℝ) : ℂ)) r‖ ^ 2 *
      EF.gammaBracket r) = fun r : ℝ =>
      (1 + c) * (‖paperFT (fun u => (F₁ u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) -
        c * (‖paperFT (fun u => ((F₁ u + F₂ u : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r) +
        (c + c ^ 2) * (‖paperFT (fun u => (F₂ u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) := by
    funext r; rw [hpt r]; ring
  have i12 : Integrable fun r : ℝ =>
      (1 + c) * (‖paperFT (fun u => (F₁ u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) -
        c * (‖paperFT (fun u => ((F₁ u + F₂ u : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r) :=
    (hI₁.const_mul _).sub (hI₃.const_mul _)
  rw [e, integral_add i12 (hI₂.const_mul _), integral_sub (hI₁.const_mul _) (hI₃.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
  ring

theorem abs_farArch_le (F : ℝ → ℝ) :
    |farArch F| ≤ 1 / (2 * Real.pi) *
      ∫ r : ℝ, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r| := by
  unfold farArch
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans (le_of_eq ?_))
    (by positivity)
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [abs_mul, abs_of_nonneg (sq_nonneg ‖paperFT (fun u => (F u : ℂ)) r‖)]

/-- The constant bounding `∫ |ê_a|² |G|`, uniform in `a`. -/
def farBumpArchMass : ℝ :=
  16 / nodeScale 2 * ((gammaLogConst + Real.log (nodeScale 2)) * bumpMassConst + bumpLogConst)

theorem integral_evenFarBump_arch_le (a : ℝ) :
    ∫ r : ℝ, ‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r| ≤
      farBumpArchMass :=
  integral_normSq_mul_abs_gammaBracket_le 2 (norm_paperFT_evenFarBump_le a)

theorem abs_farArch_evenFarBump_le (a : ℝ) :
    |farArch (evenFarBump a)| ≤ 1 / (2 * Real.pi) * farBumpArchMass :=
  (abs_farArch_le (evenFarBump a)).trans
    (mul_le_mul_of_nonneg_left (integral_evenFarBump_arch_le a) (by positivity))

theorem integrable_normSq_paperFT_mul_abs_gammaBracket {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {R : ℝ} (hFs : ∀ x, R < |x| → F x = 0) :
    Integrable fun r : ℝ => ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r| := by
  refine (integrable_normSq_paperFT_ofReal_mul_gammaBracket hF hFs).norm.congr
    (Eventually.of_forall fun r => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖paperFT (fun u => (F u : ℂ)) r‖)]

theorem abs_farArch_add_evenFarBump_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R)
    (hgs : ∀ x, R < |x| → g x = 0) {a : ℝ} (ha : R ≤ a) :
    |farArch (fun x => g x + evenFarBump a x)| ≤ 1 / (2 * Real.pi) *
      (2 * (∫ r : ℝ, ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
        2 * farBumpArchMass) := by
  have ha0 : 0 ≤ a := hR.trans ha
  have hes : ∀ x, a + 1 < |x| → evenFarBump a x = 0 := fun x hx => evenFarBump_eq_zero ha0 hx
  have hgs' : ∀ x, a + 1 < |x| → g x = 0 := fun x hx => hgs x (by linarith)
  have hs : ∀ x, a + 1 < |x| → g x + evenFarBump a x = 0 := fun x hx => by
    rw [hgs' x hx, hes x hx, add_zero]
  have hgc := hasCompactSupport_of_abs_gt_eq_zero hgs
  have hec := hasCompactSupport_evenFarBump a
  refine (abs_farArch_le (fun x => g x + evenFarBump a x)).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hIg := integrable_normSq_paperFT_mul_abs_gammaBracket hg hgs
  have hIe := integrable_normSq_paperFT_mul_abs_gammaBracket (contDiff_evenFarBump a) hes
  have hIs := integrable_normSq_paperFT_mul_abs_gammaBracket (hg.add (contDiff_evenFarBump a)) hs
  have hpt : ∀ r : ℝ, ‖paperFT (fun u => ((g u + evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
      |EF.gammaBracket r| ≤
      2 * (‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
        2 * (‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) := by
    intro r
    have e : paperFT (fun u => ((g u + evenFarBump a u : ℝ) : ℂ)) r =
        paperFT (fun u => (g u : ℂ)) r + paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r := by
      have := paperFT_ofReal_add_smul hg.continuous hgc (continuous_evenFarBump a) hec 1 1 r
      rw [show (fun u => ((g u + evenFarBump a u : ℝ) : ℂ)) =
        fun u => ((1 * g u + 1 * evenFarBump a u : ℝ) : ℂ) by funext u; push_cast; ring, this]
      push_cast; ring
    rw [e]
    have hsq : ‖paperFT (fun u => (g u : ℂ)) r +
        paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2
        ≤ 2 * ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 +
          2 * ‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (paperFT (fun u => (g u : ℂ)) r)
        (paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r)) 2
      nlinarith [sq_nonneg (‖paperFT (fun u => (g u : ℂ)) r‖ -
        ‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖)]
    have hG := abs_nonneg (EF.gammaBracket r)
    nlinarith
  calc ∫ r : ℝ, ‖paperFT (fun u => ((g u + evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
        |EF.gammaBracket r|
      ≤ ∫ r : ℝ, (2 * (‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
        2 * (‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|)) :=
        integral_mono hIs ((hIg.const_mul 2).add (hIe.const_mul 2)) hpt
    _ = 2 * (∫ r : ℝ, ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
        2 * ∫ r : ℝ, ‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
          |EF.gammaBracket r| := by
        rw [integral_add (hIg.const_mul 2) (hIe.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by linarith [integral_evenFarBump_arch_le a]

/-! ## The Weil functional of a real even test -/

theorem re_weilPoleTerm_ofReal_even {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hFe : ∀ x, F (-x) = F x) :
    (weilPoleTerm (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re =
      2 * (∫ u, F u * Real.exp (-u / 2)) ^ 2 := by
  have hc : Continuous fun u => (F u : ℂ) := Complex.continuous_ofReal.comp hF
  have hcs : HasCompactSupport fun u => (F u : ℂ) := hFc.comp_left Complex.ofReal_zero
  have hJ : ∫ u, F u * Real.exp (u / 2) = ∫ u, F u * Real.exp (-u / 2) := by
    rw [← integral_neg_eq_self (fun u => F u * Real.exp (u / 2))]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show F (-u) * Real.exp (-u / 2) = F u * Real.exp (-u / 2)
    rw [hFe]
  rw [weilPoleTerm_weilTest_eq hc hcs, paperFT_ofRealFun_I_div_two,
    paperFT_ofRealFun_neg_I_div_two, hJ, Complex.conj_ofReal]
  simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem re_weilFullFunctional_ofReal_eq (lam : ℕ → ℝ) {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    (weilFullFunctional lam (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re =
      (weilPoleTerm (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re + farArch F -
        atomPairing lam (crossCorr F F) := by
  rw [re_weilFullFunctional_ofReal, weilArchRe_weilTest_eq (f := fun u => (F u : ℂ))
    (Complex.continuous_ofReal.comp hF) (hFc.comp_left Complex.ofReal_zero)]
  unfold farArch
  ring

/-! ## The pole-free correction -/

/-- `c_a = P / ((e^{−a/2} + e^{a/2}) J)`, `P = ∫ g(x) e^{−x/2} dx`. -/
def farCoeff (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  (∫ x, g x * Real.exp (-x / 2)) / ((Real.exp (-a / 2) + Real.exp (a / 2)) * farJ)

theorem integral_sub_farCoeff_mul_exp {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (a : ℝ) : ∫ x, (g x - farCoeff g a * evenFarBump a x) * Real.exp (-x / 2) = 0 := by
  have hJ := farJ_pos
  have hE : 0 < Real.exp (-a / 2) + Real.exp (a / 2) := by positivity
  have hig : Integrable fun x => g x * Real.exp (-x / 2) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hie : Integrable fun x => evenFarBump a x * Real.exp (-x / 2) :=
    ((continuous_evenFarBump a).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_evenFarBump a).mul_right
  have e : (fun x => (g x - farCoeff g a * evenFarBump a x) * Real.exp (-x / 2)) =
      fun x => g x * Real.exp (-x / 2) - farCoeff g a * (evenFarBump a x * Real.exp (-x / 2)) := by
    funext x; ring
  rw [e, integral_sub hig (hie.const_mul _), integral_const_mul, integral_evenFarBump_mul_exp]
  unfold farCoeff
  field_simp
  ring

/-- Weil positivity on even tests whose transform vanishes at `i/2`; the pole term is absent. -/
def WeilPositiveEvenPolar (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → (∀ x, f (-x) = f x) →
    paperFT f (I / 2) = 0 → 0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re

theorem weilPositiveEvenPolar_of_weilPositiveEvenAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) : WeilPositiveEvenPolar lam := by
  intro f hf hfc hfe h0
  have hpos := h f hf hfc hfe
  rw [re_weilPoleWeightFunctional_eq_add] at hpos
  have h1 : paperFT f (-I / 2) = 0 := by
    rw [show (-I / 2 : ℂ) = -(I / 2) by ring, paperFT_neg_of_even hfe]; exact h0
  have hpole : (weilPoleTerm (EF.weilTest f f)).re = 0 := by
    rw [weilPoleTerm_weilTest_eq hf.continuous hfc, h0, h1]; simp
  rw [hpole, mul_zero, add_zero] at hpos
  exact hpos

/-- **The far-bump inequality for even tests.**  Weil positivity on even pole-free tests bounds the
Weil functional of a real even test `g` (supported in `[−R, R]`) from below by the window sums: for
`a ≥ R + 1`, `W(g) ≥ 2P² − 4c_a T(a) + 2c_a² S(a) − M(|c_a| + c_a²)`. -/
theorem realWeil_ge_of_weilPositiveEvenPolar {lam : ℕ → ℝ} (hpf : WeilPositiveEvenPolar lam)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R) (hgs : ∀ x, R < |x| → g x = 0)
    (hge : ∀ x, g (-x) = g x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℝ, R + 1 ≤ a →
      2 * (∫ x, g x * Real.exp (-x / 2)) ^ 2 - 4 * farCoeff g a * farCrossSum lam g a +
          2 * farCoeff g a ^ 2 * farSum lam a - M * (|farCoeff g a| + farCoeff g a ^ 2) ≤
        (weilFullFunctional lam (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re := by
  have hgc := hasCompactSupport_of_abs_gt_eq_zero hgs
  set Bg : ℝ := 1 / (2 * Real.pi) *
      (2 * (∫ r : ℝ, ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
        2 * farBumpArchMass) with hBg
  set Be : ℝ := 1 / (2 * Real.pi) * farBumpArchMass with hBe
  refine ⟨|farArch g| + |Bg| + 2 * |Be|, by positivity, fun a ha => ?_⟩
  have ha0 : 0 ≤ a := by linarith
  set c := farCoeff g a with hc
  set e := evenFarBump a with he
  have hes : ∀ x, a + 1 < |x| → e x = 0 := fun x hx => evenFarBump_eq_zero ha0 hx
  have hgs' : ∀ x, a + 1 < |x| → g x = 0 := fun x hx => hgs x (by linarith)
  set G : ℝ → ℝ := fun x => g x - c * e x with hG
  have hGd : ContDiff ℝ 2 G := hg.sub (contDiff_const.mul (contDiff_evenFarBump a))
  have hGs : ∀ x, a + 1 < |x| → G x = 0 := fun x hx => by
    simp only [hG, hgs' x hx, hes x hx, mul_zero, sub_zero]
  have hGc := hasCompactSupport_of_abs_gt_eq_zero hGs
  have hGe : ∀ x, G (-x) = G x := fun x => by simp only [hG, he, hge, evenFarBump_neg]
  -- positivity on the pole-free combination
  have hP0 : ∫ u, G u * Real.exp (-u / 2) = 0 := integral_sub_farCoeff_mul_exp hg.continuous hgc a
  have hpos := hpf (fun u => (G u : ℂ)) (contDiff_ofReal_comp hGd)
    (hGc.comp_left Complex.ofReal_zero) (fun x => by simp only [hGe])
    (by rw [paperFT_ofRealFun_I_div_two, hP0, Complex.ofReal_zero])
  rw [re_weilFullFunctional_ofReal_eq lam hGd.continuous hGc,
    re_weilPoleTerm_ofReal_even hGd.continuous hGc hGe, hP0] at hpos
  -- archimedean polarization
  have harch : farArch G = (1 + c) * farArch g - c * farArch (fun x => g x + e x) +
      (c + c ^ 2) * farArch e :=
    farArch_sub_smul hg (contDiff_evenFarBump a) hgs' hes c
  -- prime pairing
  have hG' : G = fun u => g u + -c * e u := by funext u; simp only [hG]; ring
  have hatoms : atomPairing lam (crossCorr G G) = atomPairing lam (crossCorr g g) -
      4 * c * farCrossSum lam g a + 2 * c ^ 2 * farSum lam a := by
    rw [hG', atomPairing_add_smul_expand lam hg.continuous hgc (continuous_evenFarBump a)
      (hasCompactSupport_evenFarBump a) (-c),
      atomPairing_crossCorr_evenFarBump lam hg.continuous hgc hge hR hgs ha,
      atomPairing_evenFarBump lam ha0]
    ring
  -- the test itself
  have hg_eq := re_weilFullFunctional_ofReal_eq lam hg.continuous hgc
  rw [re_weilPoleTerm_ofReal_even hg.continuous hgc hge] at hg_eq
  rw [hg_eq]
  -- bounds on the archimedean remainders
  have hAs := abs_farArch_add_evenFarBump_le hg hR hgs (show R ≤ a by linarith)
  have hAe := abs_farArch_evenFarBump_le a
  rw [← hBg] at hAs
  rw [← hBe] at hAe
  have hrem : |(-c) * farArch g + c * farArch (fun x => g x + e x) - (c + c ^ 2) * farArch e| ≤
      (|farArch g| + |Bg| + 2 * |Be|) * (|c| + c ^ 2) := by
    have h1 : |(-c) * farArch g| = |c| * |farArch g| := by rw [abs_mul, abs_neg]
    have h2 : |c * farArch (fun x => g x + e x)| ≤ |c| * |Bg| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hAs.trans (le_abs_self _)) (abs_nonneg _)
    have h3 : |(c + c ^ 2) * farArch e| ≤ (|c| + c ^ 2) * |Be| := by
      rw [abs_mul]
      refine mul_le_mul ((abs_add_le _ _).trans (by rw [abs_of_nonneg (sq_nonneg c)]))
        (hAe.trans (le_abs_self _)) (abs_nonneg _) (by positivity)
    calc |(-c) * farArch g + c * farArch (fun x => g x + e x) - (c + c ^ 2) * farArch e|
        ≤ |(-c) * farArch g| + |c * farArch (fun x => g x + e x)| +
          |(c + c ^ 2) * farArch e| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |c| * |farArch g| + |c| * |Bg| + (|c| + c ^ 2) * |Be| := by linarith
      _ ≤ (|farArch g| + |Bg| + 2 * |Be|) * (|c| + c ^ 2) := by
          have := abs_nonneg c
          have := abs_nonneg (farArch g)
          have := abs_nonneg Bg
          have := abs_nonneg Be
          nlinarith [sq_nonneg c]
  have hlow := neg_abs_le ((-c) * farArch g + c * farArch (fun x => g x + e x) -
    (c + c ^ 2) * farArch e)
  rw [harch, hatoms] at hpos
  nlinarith

theorem realWeil_ge_of_weilPositiveEvenAt {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R) (hgs : ∀ x, R < |x| → g x = 0)
    (hge : ∀ x, g (-x) = g x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℝ, R + 1 ≤ a →
      2 * (∫ x, g x * Real.exp (-x / 2)) ^ 2 - 4 * farCoeff g a * farCrossSum lam g a +
          2 * farCoeff g a ^ 2 * farSum lam a - M * (|farCoeff g a| + farCoeff g a ^ 2) ≤
        (weilFullFunctional lam (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re :=
  realWeil_ge_of_weilPositiveEvenPolar (weilPositiveEvenPolar_of_weilPositiveEvenAt h) hg hR hgs hge

end RHTower.EvenSector

end
