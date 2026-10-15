import GaloisForLFunctions.RHTower.EvenSectorWeilCone
import GaloisForLFunctions.RHTower.WeilWorkDeficitRepairCost
import GaloisForLFunctions.RHTower.ZetaWeilFiniteLevelInertia
import GaloisForLFunctions.RHTower.RiemannKernelEdgeWeilEnergy
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# Growth of weights that are Weil-positive on even tests

**Theorem** (`exists_abs_le_of_weilPositiveEvenAt`).  If real weights `lam` make the Weil functional
(pole weight `1`) nonnegative on every autocorrelation of an even compactly supported `C²` test,
then `|lam(n)| ≤ C √n (1 + log n)` for every `n ≥ 2`.

The bound is two-sided although even positivity is a one-sided condition at every node.  The even
two-bump tests at the node `log n` (`evenPlus`, `evenMinus`) reach it with node value `+` and `−` a
multiple of `‖φ‖²/√n`, where `φ` is the node bump, a dilate of a fixed bump by `m = 2n + 3`.

Proof.  For both tests `f`, `‖f̂(r)‖ ≤ 4‖φ̂(r)‖` on the real line and `φ̂(z) = m⁻¹ φ̂₀(z/m)`.
* *Archimedean part.*  `|γ(r)| ≤ K + log(2 + |r|)`, so after the substitution `r = mt`,
  `∫ ‖f̂‖² |γ| ≤ (16/m) ((K + log m) ∫ ‖φ̂₀‖² + ∫ ‖φ̂₀(t)‖² log(2 + |t|) dt)`.
* *Pole.*  The translates sit within `(log n)/2 + 1/2` of the origin, so
  `‖f̂(σ i)‖ ≤ 4 e^{1/4} n^{1/4} P₀ / m` for `|σ| ≤ 1/2`.
* *Node.*  `‖φ‖² = J₀/m`.  Dividing the Weil inequality by the node value `≍ J₀/(m√n)` gives
  `±lam(n) ≤ C(n/m + √n (1 + log m))`.

Reading.  An imaginary frequency `ia` of the even functional would make the weights grow like
`n^{a − 1/2}`, so only `|a| ≤ 1` can occur.
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided SeparatedBump

/-! ## The node bump is an even dilate of a fixed bump -/

theorem nodeBump_neg (j : ℕ) (v : ℝ) : nodeBump j (-v) = nodeBump j v := (nodeBump j).neg v

theorem evenProfile_eq (j : ℕ) (v : ℝ) : evenProfile j v = 2 * nodeBump j v := by
  unfold evenProfile; rw [nodeBump_neg]; ring

theorem oddProfile_eq (j : ℕ) (v : ℝ) :
    oddProfile j v = nodeBump j (v - 2 * (nodeBump j).rOut) -
      nodeBump j (v + 2 * (nodeBump j).rOut) := by
  unfold oddProfile
  rw [show -v - 2 * (nodeBump j).rOut = -(v + 2 * (nodeBump j).rOut) by ring, nodeBump_neg]

/-- The dilation scale `m = 2j + 3` of the node bump. -/
def nodeScale (j : ℕ) : ℝ := 2 * (j : ℝ) + 3

theorem nodeScale_pos (j : ℕ) : 0 < nodeScale j := by unfold nodeScale; positivity

theorem one_le_nodeScale (j : ℕ) : 1 ≤ nodeScale j := by
  unfold nodeScale; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem paperFT_nodeBump (j : ℕ) (z : ℂ) :
    paperFT (fun u => (nodeBump j u : ℂ)) z =
      ((nodeScale j)⁻¹ : ℝ) * paperFT (narrowBumpC 0) (((nodeScale j)⁻¹ : ℝ) * z) := by
  have h := RHTower.WeilWorkPBAP.paperFT_narrowBump_scale (2 * j + 2) z
  have e : (((2 * j + 2 : ℕ) : ℝ) + 1) = nodeScale j := by unfold nodeScale; push_cast; ring
  rw [e] at h
  exact h

theorem integral_nodeBump_sq (j : ℕ) :
    (∫ u, nodeBump j u ^ 2) = (nodeScale j)⁻¹ * ∫ u, narrowBump 0 u ^ 2 := by
  have h := RHTower.WeilWorkPBAP.integral_narrowBump_sq_scale (2 * j + 2)
  have e : (((2 * j + 2 : ℕ) : ℝ) + 1) = nodeScale j := by unfold nodeScale; push_cast; ring
  rw [e] at h
  exact h

/-! ## Fourier transforms of signed sums of translates -/

theorem paperFT_sum_translate {ι : Type*} (T : Finset ι) (ε : ι → ℂ) (x : ι → ℝ)
    {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (fun u => ∑ k ∈ T, ε k * g (u - x k)) z =
      (∑ k ∈ T, ε k * Complex.exp (I * z * x k)) * paperFT g z := by
  rw [RHTower.paperFT_finset_sum T ε (f := fun k u => g (u - x k))
    (fun _ => hg.comp (continuous_id.sub continuous_const))
    (fun k => hgc.comp_homeomorph (Homeomorph.subRight (x k))), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RHTower.paperFT_translate']
  ring

theorem norm_paperFT_sum_translate_le {ι : Type*} (T : Finset ι) (ε : ι → ℂ) (x : ι → ℝ)
    {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) (r : ℝ) :
    ‖paperFT (fun u => ∑ k ∈ T, ε k * g (u - x k)) r‖ ≤ (∑ k ∈ T, ‖ε k‖) * ‖paperFT g r‖ := by
  rw [paperFT_sum_translate T ε x hg hgc, norm_mul]
  refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (le_of_eq ?_)) (norm_nonneg _)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, WeilSpectral.norm_cexp_I_mul_ofReal, mul_one]

theorem norm_cexp_I_mul_I_div_two (σ x : ℝ) (hσ : |σ| ≤ 1 / 2) :
    ‖Complex.exp (I * ((σ : ℂ) * I) * x)‖ ≤ Real.exp (|x| / 2) := by
  rw [Complex.norm_exp]
  have e : (I * ((σ : ℂ) * I) * (x : ℂ)).re = -(σ * x) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [e, Real.exp_le_exp]
  have := abs_mul σ x
  have h1 : |σ * x| ≤ 1 / 2 * |x| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hσ (abs_nonneg x)
  have h2 := neg_abs_le (σ * x)
  linarith

theorem norm_paperFT_sum_translate_imag_le {ι : Type*} (T : Finset ι) (ε : ι → ℂ) (x : ι → ℝ)
    {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) {σ : ℝ} (hσ : |σ| ≤ 1 / 2)
    {X : ℝ} (hX : ∀ k ∈ T, |x k| ≤ X) :
    ‖paperFT (fun u => ∑ k ∈ T, ε k * g (u - x k)) ((σ : ℂ) * I)‖ ≤
      (∑ k ∈ T, ‖ε k‖) * Real.exp (X / 2) * ‖paperFT g ((σ : ℂ) * I)‖ := by
  rw [paperFT_sum_translate T ε x hg hgc, norm_mul]
  refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans ?_) (norm_nonneg _)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_cexp_I_mul_I_div_two σ (x k) hσ).trans ?_)
    (norm_nonneg _)
  exact Real.exp_le_exp.mpr (by linarith [hX k hk])

/-! ## The two node tests as sums of translates of the node bump -/

theorem evenPlusC_eq (j : ℕ) :
    (fun u => (evenPlusFn j u : ℂ)) = fun u => ∑ k : Fin 2, (![2, 2] k : ℂ) *
      (fun v => (nodeBump j v : ℂ)) (u - ![Real.log j / 2, -(Real.log j / 2)] k) := by
  funext u
  simp only [evenPlusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    evenProfile_eq]
  push_cast
  ring

theorem evenMinusC_eq (j : ℕ) :
    (fun u => (evenMinusFn j u : ℂ)) = fun u => ∑ k : Fin 4, (![1, -1, -1, 1] k : ℂ) *
      (fun v => (nodeBump j v : ℂ)) (u - ![Real.log j / 2 + 2 * (nodeBump j).rOut,
        Real.log j / 2 - 2 * (nodeBump j).rOut, -(Real.log j / 2) + 2 * (nodeBump j).rOut,
        -(Real.log j / 2) - 2 * (nodeBump j).rOut] k) := by
  funext u
  rw [Fin.sum_univ_four]
  simp only [evenMinusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    oddProfile_eq]
  simp
  ring_nf


/-! ## Constants of the fixed bump -/

/-- A bound for `‖φ̂₀(σ i)‖`, `|σ| ≤ 1/2`, where `φ₀` is the fixed bump. -/
def bumpPoleConst : ℝ :=
  Real.exp (1 / 8) * (4 * ((∫ u, ‖narrowBumpC 0 u‖) + ∫ u, ‖deriv (deriv (narrowBumpC 0)) u‖))

theorem narrowBumpC_zero_support (u : ℝ) (hu : narrowBumpC 0 u ≠ 0) : |u| ≤ 1 / 4 := by
  by_contra h
  exact hu (narrowBumpC_eq_zero 0 (by norm_num; linarith))

theorem norm_paperFT_narrowBumpC_zero_imag_le {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ‖paperFT (narrowBumpC 0) ((σ : ℂ) * I)‖ ≤ bumpPoleConst := by
  have h := norm_paperFT_le_decay (((contDiff_narrowBumpC 0).of_le (by norm_cast)))
    narrowBumpC_zero_support ((σ : ℂ) * I)
  have hre : ((σ : ℂ) * I).re = 0 := by simp
  have him : ((σ : ℂ) * I).im = σ := by simp
  rw [hre, him, abs_zero, add_zero, one_pow, div_one] at h
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) ?_)
  · nlinarith [abs_nonneg σ]
  · have h1 : 0 ≤ ∫ u, ‖narrowBumpC 0 u‖ := integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv (narrowBumpC 0)) u‖ := integral_nonneg fun _ => norm_nonneg _
    positivity

theorem bumpPoleConst_nonneg : 0 ≤ bumpPoleConst :=
  (norm_nonneg _).trans (norm_paperFT_narrowBumpC_zero_imag_le (σ := 0) (by norm_num))

theorem tsupport_narrowBumpC_zero : tsupport (narrowBumpC 0) ⊆ Icc (-(1 / 4)) (1 / 4) := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  exact abs_le.mp (narrowBumpC_zero_support u hu)

/-- The archimedean constant `K₀ = K_ψ + log π`. -/
def gammaLogConst : ℝ := digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi

theorem abs_gammaBracket_le_log (r : ℝ) :
    |EF.gammaBracket r| ≤ gammaLogConst + Real.log (2 + |r|) := by
  rw [WeilHerglotz.gammaBracket_eq]
  have h1 := abs_re_digamma_vertical_le (c := 1 / 4) (by norm_num) (r / 2)
  have hr2 : |r / 2| ≤ |r| := by
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]; linarith [abs_nonneg r]
  have hlog : Real.log (2 + |r / 2|) ≤ Real.log (2 + |r|) :=
    Real.log_le_log (by positivity) (by linarith)
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hab := abs_sub (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re
    (Real.log Real.pi)
  rw [abs_of_nonneg hpi] at hab
  unfold gammaLogConst
  push_cast at h1 hab ⊢
  linarith

theorem abs_gammaBracket_mul_le {m : ℝ} (hm : 1 ≤ m) (t : ℝ) :
    |EF.gammaBracket (m * t)| ≤ gammaLogConst + Real.log m + Real.log (2 + |t|) := by
  refine (abs_gammaBracket_le_log (m * t)).trans ?_
  have hm0 : 0 < m := by linarith
  have h : 2 + |m * t| ≤ m * (2 + |t|) := by
    rw [abs_mul, abs_of_pos hm0]; nlinarith [abs_nonneg t]
  have := Real.log_le_log (by positivity) h
  rw [Real.log_mul hm0.ne' (by positivity)] at this
  linarith

theorem continuous_abs_gammaBracket : Continuous fun r => |EF.gammaBracket r| :=
  WeilHerglotz.continuous_gammaBracket.abs

theorem abs_abs_gammaBracket_le_linear (r : ℝ) :
    |(|EF.gammaBracket r|)| ≤ (|gammaLogConst| + 2) * (1 + |r|) := by
  rw [abs_abs]
  refine (abs_gammaBracket_le_log r).trans ?_
  have hlog : Real.log (2 + |r|) ≤ 1 + |r| := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 + |r|)
    linarith
  nlinarith [le_abs_self gammaLogConst, abs_nonneg r, abs_nonneg gammaLogConst]

/-- `I₀ = ∫ ‖φ̂₀‖²`. -/
def bumpMassConst : ℝ := ∫ t : ℝ, ‖paperFT (narrowBumpC 0) t‖ ^ 2 * 1

/-- `I₁ = ∫ ‖φ̂₀(t)‖² log(2 + |t|) dt`. -/
def bumpLogConst : ℝ := ∫ t : ℝ, ‖paperFT (narrowBumpC 0) t‖ ^ 2 * Real.log (2 + |t|)

theorem integrable_bumpMass :
    Integrable fun t : ℝ => ‖paperFT (narrowBumpC 0) t‖ ^ 2 * 1 :=
  integrable_normSq_paperFT_mul_of_linear ((contDiff_narrowBumpC 0).of_le (by norm_cast))
    tsupport_narrowBumpC_zero continuous_const (Mp := 1) fun τ => by
      rw [abs_one]; linarith [abs_nonneg τ]

theorem integrable_bumpLog :
    Integrable fun t : ℝ => ‖paperFT (narrowBumpC 0) t‖ ^ 2 * Real.log (2 + |t|) :=
  integrable_normSq_paperFT_mul_of_linear ((contDiff_narrowBumpC 0).of_le (by norm_cast))
    tsupport_narrowBumpC_zero
    ((continuous_const.add continuous_abs).log fun t =>
      (by positivity : (0 : ℝ) < 2 + |t|).ne') (Mp := 1) fun τ => by
      have h0 : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 + |τ|)
      rw [abs_of_nonneg h0]; linarith

theorem bumpMassConst_nonneg : 0 ≤ bumpMassConst :=
  integral_nonneg fun _ => by positivity

theorem bumpLogConst_nonneg : 0 ≤ bumpLogConst :=
  integral_nonneg fun t => mul_nonneg (sq_nonneg _)
    (Real.log_nonneg (by linarith [abs_nonneg t]))

/-! ## The archimedean and pole parts of the node tests -/

/-- **Archimedean part.**  If `‖f̂‖ ≤ 4 ‖φ̂_j‖` on the real line, then
`∫ ‖f̂‖² |γ| ≤ (16/m) ((K₀ + log m) I₀ + I₁)`. -/
theorem integral_normSq_mul_abs_gammaBracket_le (j : ℕ) {f : ℝ → ℂ}
    (hb : ∀ r : ℝ, ‖paperFT f r‖ ≤ 4 * ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖) :
    ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| ≤
      16 / nodeScale j *
        ((gammaLogConst + Real.log (nodeScale j)) * bumpMassConst + bumpLogConst) := by
  set m := nodeScale j with hm_def
  have hm0 : 0 < m := nodeScale_pos j
  have hm1 : 1 ≤ m := one_le_nodeScale j
  set H : ℝ → ℝ := fun t =>
    16 / m ^ 2 * (‖paperFT (narrowBumpC 0) t‖ ^ 2 * |EF.gammaBracket (m * t)|) with hH
  have hpt : ∀ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| ≤ H (r / m) := fun r => by
    have h1 := hb r
    rw [paperFT_nodeBump j r] at h1
    have e : (((m⁻¹ : ℝ) : ℂ) * (r : ℂ)) = ((r / m : ℝ) : ℂ) := by push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h1
    have h2 : ‖paperFT f r‖ ^ 2 ≤ 16 / m ^ 2 * ‖paperFT (narrowBumpC 0) (r / m : ℝ)‖ ^ 2 := by
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      calc ‖paperFT f r‖ ^ 2 ≤ (4 * (m⁻¹ * ‖paperFT (narrowBumpC 0) (r / m : ℝ)‖)) ^ 2 := h3
        _ = 16 / m ^ 2 * ‖paperFT (narrowBumpC 0) (r / m : ℝ)‖ ^ 2 := by field_simp; ring
    have e2 : m * (r / m) = r := by field_simp
    simp only [hH, e2]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have hHint : Integrable H := by
    have : Integrable fun t : ℝ =>
        ‖paperFT (narrowBumpC 0) t‖ ^ 2 *
          ((gammaLogConst + Real.log m) * 1 + Real.log (2 + |t|)) := by
      have e : (fun t : ℝ => ‖paperFT (narrowBumpC 0) t‖ ^ 2 *
          ((gammaLogConst + Real.log m) * 1 + Real.log (2 + |t|))) = fun t : ℝ =>
          (gammaLogConst + Real.log m) * (‖paperFT (narrowBumpC 0) t‖ ^ 2 * 1) +
            ‖paperFT (narrowBumpC 0) t‖ ^ 2 * Real.log (2 + |t|) := by
        funext t; ring
      rw [e]
      exact (integrable_bumpMass.const_mul _).add integrable_bumpLog
    refine (this.const_mul (16 / m ^ 2)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · have hc : Continuous fun t : ℝ => paperFT (narrowBumpC 0) t :=
        WeilHerglotz.continuous_paperFT_real
          ((contDiff_narrowBumpC 0).continuous.integrable_of_hasCompactSupport
            (hasCompactSupport_narrowBumpC 0))
      exact (continuous_const.mul ((continuous_norm.comp hc).pow 2 |>.mul
        (continuous_abs_gammaBracket.comp
          (continuous_const.mul continuous_id)))).aestronglyMeasurable
    · simp only [hH, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) (by positivity)
      have := abs_gammaBracket_mul_le hm1 t
      linarith
  have hlhs : 0 ≤ᵐ[volume] fun r : ℝ => ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| :=
    Filter.Eventually.of_forall fun r => by positivity
  have hcomp : Integrable fun r : ℝ => H (r / m) := by
    have := hHint.comp_div hm0.ne'
    exact this
  calc ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r|
      ≤ ∫ r : ℝ, H (r / m) := integral_mono_of_nonneg hlhs hcomp
        (Filter.Eventually.of_forall hpt)
    _ = m * ∫ t : ℝ, H t := by
        rw [Measure.integral_comp_div H m, abs_of_pos hm0, smul_eq_mul]
    _ ≤ m * ∫ t : ℝ, 16 / m ^ 2 * (‖paperFT (narrowBumpC 0) t‖ ^ 2 *
          ((gammaLogConst + Real.log m) * 1 + Real.log (2 + |t|))) := by
        refine mul_le_mul_of_nonneg_left (integral_mono hHint ?_ fun t => ?_) hm0.le
        · have e : (fun t : ℝ => 16 / m ^ 2 * (‖paperFT (narrowBumpC 0) t‖ ^ 2 *
              ((gammaLogConst + Real.log m) * 1 + Real.log (2 + |t|)))) = fun t : ℝ =>
              16 / m ^ 2 * ((gammaLogConst + Real.log m) * (‖paperFT (narrowBumpC 0) t‖ ^ 2 * 1) +
                ‖paperFT (narrowBumpC 0) t‖ ^ 2 * Real.log (2 + |t|)) := by
            funext t; ring
          rw [e]
          exact ((integrable_bumpMass.const_mul _).add integrable_bumpLog).const_mul _
        · simp only [hH]
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
            (by positivity)
          have := abs_gammaBracket_mul_le hm1 t
          linarith
    _ = 16 / m * ((gammaLogConst + Real.log m) * bumpMassConst + bumpLogConst) := by
        rw [integral_const_mul]
        have e : (fun t : ℝ => ‖paperFT (narrowBumpC 0) t‖ ^ 2 *
            ((gammaLogConst + Real.log m) * 1 + Real.log (2 + |t|))) = fun t : ℝ =>
            (gammaLogConst + Real.log m) * (‖paperFT (narrowBumpC 0) t‖ ^ 2 * 1) +
              ‖paperFT (narrowBumpC 0) t‖ ^ 2 * Real.log (2 + |t|) := by
          funext t; ring
        rw [e, integral_add (integrable_bumpMass.const_mul _) integrable_bumpLog,
          integral_const_mul]
        unfold bumpMassConst bumpLogConst
        field_simp


/-! ## The pole-and-archimedean part of a test -/

/-- `|W_∞(f ⋆ f̃)| ≤ 2B² + (1/2π) ∫ ‖f̂‖² |γ|` when `‖f̂(σ i)‖ ≤ B` for `|σ| ≤ 1/2`. -/
theorem abs_weilArchRe_le {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {B : ℝ}
    (hB : ∀ σ : ℝ, |σ| ≤ 1 / 2 → ‖paperFT f ((σ : ℂ) * I)‖ ≤ B) :
    |weilArchRe (EF.weilTest f f)| ≤
      2 * B ^ 2 + 1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num))
  have hpole : ∀ σ : ℝ, |σ| ≤ 1 / 2 →
      ‖paperFT (EF.weilTest f f) ((σ : ℂ) * I)‖ ≤ B ^ 2 := fun σ hσ => by
    rw [EF.paperFT_weilTest hf hf hfc hfc, norm_mul, Complex.norm_conj]
    have hc : conj ((σ : ℂ) * I) = ((-σ : ℝ) : ℂ) * I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
    rw [hc, sq]
    exact mul_le_mul (hB σ hσ) (hB (-σ) (by rwa [abs_neg])) (norm_nonneg _) hB0
  have ha : ‖paperFT (EF.weilTest f f) (I / 2)‖ ≤ B ^ 2 := by
    have := hpole (1 / 2) (by norm_num [abs_of_pos])
    rwa [show ((1 / 2 : ℝ) : ℂ) * I = I / 2 by push_cast; ring] at this
  have hb : ‖paperFT (EF.weilTest f f) (-I / 2)‖ ≤ B ^ 2 := by
    have := hpole (-(1 / 2)) (by norm_num [abs_of_pos])
    rwa [show ((-(1 / 2) : ℝ) : ℂ) * I = -I / 2 by push_cast; ring] at this
  have hint : (∫ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)) =
      ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [paperFT_weilTest_self_eq_normSq hf hfc r]
    push_cast; ring
  set X := ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r with hX
  have hXabs : |X| ≤ ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [abs_mul, abs_of_nonneg (sq_nonneg ‖paperFT f r‖)]
  have hc : (1 / (2 * (Real.pi : ℂ)) : ℂ) * (X : ℂ) = ((X / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast; ring
  unfold weilArchRe
  rw [hint, hc, Complex.add_re, Complex.add_re, Complex.ofReal_re]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hXd : |X / (2 * Real.pi)| ≤ 1 / (2 * Real.pi) *
      ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| := by
    rw [abs_div, abs_of_pos hpi, div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left hXabs (by positivity)
  calc |(paperFT (EF.weilTest f f) (I / 2)).re + (paperFT (EF.weilTest f f) (-I / 2)).re +
        X / (2 * Real.pi)|
      ≤ |(paperFT (EF.weilTest f f) (I / 2)).re| + |(paperFT (EF.weilTest f f) (-I / 2)).re| +
          |X / (2 * Real.pi)| := abs_add_three _ _ _
    _ ≤ B ^ 2 + B ^ 2 + 1 / (2 * Real.pi) *
          ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| := by
        gcongr
        · exact (Complex.abs_re_le_norm _).trans ha
        · exact (Complex.abs_re_le_norm _).trans hb
    _ = _ := by ring

/-! ## The node tests -/

theorem continuous_nodeBumpC (j : ℕ) : Continuous fun v => (nodeBump j v : ℂ) :=
  Complex.continuous_ofReal.comp (nodeBump j).continuous

theorem hasCompactSupport_nodeBumpC (j : ℕ) : HasCompactSupport fun v => (nodeBump j v : ℂ) :=
  (nodeBump j).hasCompactSupport.comp_left Complex.ofReal_zero

theorem norm_paperFT_evenPlus_le (j : ℕ) (r : ℝ) :
    ‖paperFT (fun u => (evenPlusFn j u : ℂ)) r‖ ≤
      4 * ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖ := by
  rw [evenPlusC_eq]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) r).trans (le_of_eq ?_)
  simp [Fin.sum_univ_two]
  norm_num

theorem norm_paperFT_evenMinus_le (j : ℕ) (r : ℝ) :
    ‖paperFT (fun u => (evenMinusFn j u : ℂ)) r‖ ≤
      4 * ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖ := by
  rw [evenMinusC_eq]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) r).trans (le_of_eq ?_)
  simp [Fin.sum_univ_four]
  norm_num

theorem norm_paperFT_nodeBump_imag_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ‖paperFT (fun u => (nodeBump j u : ℂ)) ((σ : ℂ) * I)‖ ≤ (nodeScale j)⁻¹ * bumpPoleConst := by
  have hm0 := nodeScale_pos j
  have hm1 := one_le_nodeScale j
  rw [paperFT_nodeBump, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have e : (((nodeScale j)⁻¹ : ℝ) : ℂ) * ((σ : ℂ) * I) = (((σ / nodeScale j) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (norm_paperFT_narrowBumpC_zero_imag_le ?_) (by positivity)
  rw [abs_div, abs_of_pos hm0]
  exact (div_le_self (abs_nonneg _) hm1).trans hσ

theorem nodeBump_rOut_le (j : ℕ) : (nodeBump j).rOut ≤ 1 / 12 := by
  rw [nodeBump_rOut]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])

/-- The pole bound for the node tests: `‖f̂(σ i)‖ ≤ 4 e^{(log j)/4 + 1/4} P₀ / m`. -/
theorem norm_paperFT_evenPlus_imag_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ‖paperFT (fun u => (evenPlusFn j u : ℂ)) ((σ : ℂ) * I)‖ ≤
      4 * Real.exp (Real.log j / 4 + 1 / 4) * ((nodeScale j)⁻¹ * bumpPoleConst) := by
  rw [evenPlusC_eq]
  have hX : ∀ k ∈ (Finset.univ : Finset (Fin 2)),
      |![Real.log j / 2, -(Real.log j / 2)] k| ≤ Real.log j / 2 + 1 / 2 := by
    intro k _
    have hl : 0 ≤ Real.log j := Real.log_natCast_nonneg j
    fin_cases k <;> simp [abs_of_nonneg (by linarith : 0 ≤ Real.log j / 2)]
  refine (norm_paperFT_sum_translate_imag_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) hσ hX).trans ?_
  have hs : (∑ k : Fin 2, ‖(![2, 2] k : ℂ)‖) = 4 := by simp [Fin.sum_univ_two]; norm_num
  rw [hs, show (Real.log j / 2 + 1 / 2) / 2 = Real.log j / 4 + 1 / 4 by ring]
  exact mul_le_mul_of_nonneg_left (norm_paperFT_nodeBump_imag_le j hσ) (by positivity)

theorem norm_paperFT_evenMinus_imag_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ‖paperFT (fun u => (evenMinusFn j u : ℂ)) ((σ : ℂ) * I)‖ ≤
      4 * Real.exp (Real.log j / 4 + 1 / 4) * ((nodeScale j)⁻¹ * bumpPoleConst) := by
  rw [evenMinusC_eq]
  have hρ := nodeBump_rOut_le j
  have hρ0 := (nodeBump j).rOut_pos
  have hl : 0 ≤ Real.log j := Real.log_natCast_nonneg j
  have hX : ∀ k ∈ (Finset.univ : Finset (Fin 4)),
      |![Real.log j / 2 + 2 * (nodeBump j).rOut, Real.log j / 2 - 2 * (nodeBump j).rOut,
        -(Real.log j / 2) + 2 * (nodeBump j).rOut, -(Real.log j / 2) - 2 * (nodeBump j).rOut] k| ≤
        Real.log j / 2 + 1 / 2 := by
    intro k _
    fin_cases k <;> simp <;> rw [abs_le] <;> constructor <;> linarith
  refine (norm_paperFT_sum_translate_imag_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) hσ hX).trans ?_
  have hs : (∑ k : Fin 4, ‖(![1, -1, -1, 1] k : ℂ)‖) = 4 := by simp [Fin.sum_univ_four]; norm_num
  rw [hs, show (Real.log j / 2 + 1 / 2) / 2 = Real.log j / 4 + 1 / 4 by ring]
  exact mul_le_mul_of_nonneg_left (norm_paperFT_nodeBump_imag_le j hσ) (by positivity)


/-! ## The growth bound -/

theorem integral_evenProfile_sq_eq (j : ℕ) :
    (∫ u, evenProfile j u ^ 2) = 4 * ((nodeScale j)⁻¹ * ∫ u, narrowBump 0 u ^ 2) := by
  simp_rw [evenProfile_eq, mul_pow]
  rw [integral_const_mul, integral_nodeBump_sq]
  norm_num

theorem integrable_sq_nodeBump_sub (j : ℕ) (a : ℝ) :
    Integrable fun v => nodeBump j (v - a) ^ 2 := by
  refine (((nodeBump j).continuous.comp (continuous_sub_right a)).pow 2
    ).integrable_of_hasCompactSupport
      (SeparatedBump.hasCompactSupport_of_abs_gt (R := |a| + (nodeBump j).rOut) fun u hu => ?_)
  have h : (nodeBump j).rOut ≤ |u - a| := by
    have := abs_sub_abs_le_abs_sub u a
    linarith
  show nodeBump j (u - a) ^ 2 = 0
  rw [nodeBump_eq_zero j h]
  norm_num

theorem integrable_oddProfile_sq (j : ℕ) : Integrable fun v => oddProfile j v ^ 2 :=
  ((contDiff_oddProfile j).continuous.pow 2).integrable_of_hasCompactSupport
    (SeparatedBump.hasCompactSupport_of_abs_gt (R := 6 * (nodeBump j).rOut / 2) fun u hu => by
      show oddProfile j u ^ 2 = 0
      rw [oddProfile_eq_zero j hu]
      norm_num)

theorem sq_nodeBump_le_sq_oddProfile (j : ℕ) (v : ℝ) :
    nodeBump j (v - 2 * (nodeBump j).rOut) ^ 2 ≤ oddProfile j v ^ 2 := by
  have hρ0 : 0 < (nodeBump j).rOut := (nodeBump j).rOut_pos
  have hprod : nodeBump j (v - 2 * (nodeBump j).rOut) * nodeBump j (v + 2 * (nodeBump j).rOut) =
      0 := by
    by_cases h : (nodeBump j).rOut ≤ |v - 2 * (nodeBump j).rOut|
    · rw [nodeBump_eq_zero j h, zero_mul]
    · push Not at h
      have h1 := (abs_lt.mp h).1
      have h2 : (nodeBump j).rOut ≤ |v + 2 * (nodeBump j).rOut| := by
        rw [abs_of_pos (by linarith)]; linarith
      rw [nodeBump_eq_zero j h2, mul_zero]
  rw [oddProfile_eq]
  nlinarith [sq_nonneg (nodeBump j (v + 2 * (nodeBump j).rOut))]

theorem le_integral_oddProfile_sq (j : ℕ) :
    (nodeScale j)⁻¹ * (∫ u, narrowBump 0 u ^ 2) ≤ ∫ u, oddProfile j u ^ 2 := by
  rw [← integral_nodeBump_sq]
  calc (∫ u, nodeBump j u ^ 2) = ∫ v, nodeBump j (v - 2 * (nodeBump j).rOut) ^ 2 :=
        (integral_sub_right_eq_self (fun u => nodeBump j u ^ 2) (2 * (nodeBump j).rOut)).symm
    _ ≤ ∫ v, oddProfile j v ^ 2 :=
        integral_mono (integrable_sq_nodeBump_sub j _) (integrable_oddProfile_sq j)
          (sq_nodeBump_le_sq_oddProfile j)

/-- The bound `|W_∞| ≤ 32 e^{(log n)/2 + 1/2} P₀²/m² + (8/(πm))((K₀ + log m) I₀ + I₁)` for a node
test. -/
theorem abs_weilArchRe_node_le (n : ℕ) {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hb : ∀ r : ℝ, ‖paperFT f r‖ ≤ 4 * ‖paperFT (fun u => (nodeBump n u : ℂ)) r‖)
    (hi : ∀ σ : ℝ, |σ| ≤ 1 / 2 → ‖paperFT f ((σ : ℂ) * I)‖ ≤
      4 * Real.exp (Real.log n / 4 + 1 / 4) * ((nodeScale n)⁻¹ * bumpPoleConst)) :
    |weilArchRe (EF.weilTest f f)| ≤
      32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 +
        8 / (Real.pi * nodeScale n) *
          ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) := by
  have hm0 := nodeScale_pos n
  refine (abs_weilArchRe_le hf hfc hi).trans ?_
  have h1 := integral_normSq_mul_abs_gammaBracket_le n hb
  have hpi : 0 < Real.pi := Real.pi_pos
  have e1 : 2 * (4 * Real.exp (Real.log n / 4 + 1 / 4) * ((nodeScale n)⁻¹ * bumpPoleConst)) ^ 2 =
      32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]
    field_simp
    ring_nf
  rw [e1]
  have e2 : 1 / (2 * Real.pi) *
      (16 / nodeScale n *
        ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst)) =
      8 / (Real.pi * nodeScale n) *
        ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) := by
    field_simp; ring
  rw [← e2]
  gcongr

theorem le_div_of_node {A c x B : ℝ} (hc : 0 < c) (hW : 0 ≤ A - c * x) (hA : |A| ≤ B) :
    x ≤ B / c := by
  rw [le_div_iff₀ hc]
  linarith [le_abs_self A]

theorem log_nodeScale_le {n : ℝ} (hn : 1 ≤ n) : Real.log (2 * n + 3) ≤ 2 + Real.log n := by
  have hn0 : 0 < n := by linarith
  have h5 : 2 * n + 3 ≤ 5 * n := by linarith
  have := Real.log_le_log (by linarith) h5
  rw [Real.log_mul (by norm_num) hn0.ne'] at this
  have h52 : Real.log 5 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9]
  linarith

/-- The arithmetic of the final bound. -/
theorem node_bound_le {n J₀ P K I₀ I₁ : ℝ} (hn : 2 ≤ n) (hJ : 0 < J₀) (hI₀ : 0 ≤ I₀)
    (hI₁ : 0 ≤ I₁) :
    (32 * Real.exp (Real.log n / 2 + 1 / 2) * P ^ 2 / (2 * n + 3) ^ 2 +
        8 / (Real.pi * (2 * n + 3)) * ((K + Real.log (2 * n + 3)) * I₀ + I₁)) *
        (Real.sqrt n * (2 * n + 3) / (2 * J₀)) ≤
      (16 * Real.exp (1 / 2) * P ^ 2 / J₀ + 4 * ((|K| + 3) * I₀ + I₁) / (Real.pi * J₀)) *
        Real.sqrt n * (1 + Real.log n) := by
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < 2 * n + 3 := by linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hsqrt : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; linarith
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hexp : Real.exp (Real.log n / 2 + 1 / 2) = Real.sqrt n * Real.exp (1 / 2) := by
    rw [Real.exp_add, Real.exp_half, Real.exp_log hn0]
  have hpi : 0 < Real.pi := Real.pi_pos
  set T₁ := 16 * Real.exp (1 / 2) * P ^ 2 / J₀ with hT₁def
  set T₂ := 4 * ((|K| + 3) * I₀ + I₁) / (Real.pi * J₀)
  have hT₁ : 0 ≤ T₁ := by positivity
  have h1 : 32 * Real.exp (Real.log n / 2 + 1 / 2) * P ^ 2 / (2 * n + 3) ^ 2 *
      (Real.sqrt n * (2 * n + 3) / (2 * J₀)) = T₁ * (n / (2 * n + 3)) := by
    have e : 32 * Real.exp (Real.log n / 2 + 1 / 2) * P ^ 2 / (2 * n + 3) ^ 2 *
        (Real.sqrt n * (2 * n + 3) / (2 * J₀)) =
        T₁ * (Real.sqrt n * Real.sqrt n / (2 * n + 3)) := by
      rw [hexp, hT₁def]
      field_simp
      ring
    rw [e, hs]
  have h2 : 8 / (Real.pi * (2 * n + 3)) * ((K + Real.log (2 * n + 3)) * I₀ + I₁) *
      (Real.sqrt n * (2 * n + 3) / (2 * J₀)) =
      4 / (Real.pi * J₀) * ((K + Real.log (2 * n + 3)) * I₀ + I₁) * Real.sqrt n := by
    field_simp
    ring
  have h3 : T₁ * (n / (2 * n + 3)) ≤ T₁ * Real.sqrt n * (1 + Real.log n) := by
    have hq : n / (2 * n + 3) ≤ 1 := (div_le_one hm0).mpr (by linarith)
    calc T₁ * (n / (2 * n + 3)) ≤ T₁ * 1 := mul_le_mul_of_nonneg_left hq hT₁
      _ ≤ T₁ * (Real.sqrt n * (1 + Real.log n)) := by
          refine mul_le_mul_of_nonneg_left ?_ hT₁
          nlinarith
      _ = T₁ * Real.sqrt n * (1 + Real.log n) := by ring
  have hlogm := log_nodeScale_le (n := n) (by linarith)
  have hX : (K + Real.log (2 * n + 3)) * I₀ + I₁ ≤ ((|K| + 3) * I₀ + I₁) * (1 + Real.log n) := by
    have hK : K ≤ |K| := le_abs_self K
    have hKI : K * I₀ ≤ |K| * I₀ := mul_le_mul_of_nonneg_right hK hI₀
    have hLI : Real.log (2 * n + 3) * I₀ ≤ (2 + Real.log n) * I₀ :=
      mul_le_mul_of_nonneg_right hlogm hI₀
    nlinarith [mul_nonneg hI₀ hlogn, mul_nonneg hI₁ hlogn,
      mul_nonneg (mul_nonneg (abs_nonneg K) hI₀) hlogn]
  have h4 : 4 / (Real.pi * J₀) * ((K + Real.log (2 * n + 3)) * I₀ + I₁) * Real.sqrt n ≤
      T₂ * Real.sqrt n * (1 + Real.log n) := by
    have hc : 0 ≤ 4 / (Real.pi * J₀) := by positivity
    calc 4 / (Real.pi * J₀) * ((K + Real.log (2 * n + 3)) * I₀ + I₁) * Real.sqrt n
        ≤ 4 / (Real.pi * J₀) * (((|K| + 3) * I₀ + I₁) * (1 + Real.log n)) * Real.sqrt n := by
          gcongr
      _ = T₂ * Real.sqrt n * (1 + Real.log n) := by ring
  rw [add_mul, h1, h2]
  linarith

/-- **Even-positive weights grow at most like `√n log n`.** -/
theorem exists_abs_le_of_weilPositiveEvenAt {lam : ℕ → ℝ} (h : WeilPositiveEvenAt 1 lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → |lam n| ≤ C * Real.sqrt n * (1 + Real.log n) := by
  have hJ : 0 < ∫ u, narrowBump 0 u ^ 2 := integral_narrowBump_sq_pos 0
  refine ⟨16 * Real.exp (1 / 2) * bumpPoleConst ^ 2 / (∫ u, narrowBump 0 u ^ 2) +
    4 * ((|gammaLogConst| + 3) * bumpMassConst + bumpLogConst) /
      (Real.pi * ∫ u, narrowBump 0 u ^ 2),
    add_nonneg (by positivity)
      (div_nonneg (by have := bumpMassConst_nonneg; have := bumpLogConst_nonneg; positivity)
        (by positivity)), fun n hn => ?_⟩
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hm0 := nodeScale_pos n
  have hmeq : nodeScale n = 2 * (n : ℝ) + 3 := rfl
  set Bd := 32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 +
    8 / (Real.pi * nodeScale n) *
      ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) with hBd
  have hWp := h (evenPlus n).1.1 (evenPlus n).1.2.1 (evenPlus n).1.2.2 (evenPlus n).2
  rw [re_weilPoleWeightFunctional_eq 1 lam (evenPlus n).1,
    logVector_evenPlus ⟨n, hn⟩, Finsupp.linearCombination_single] at hWp
  have hWm := h (evenMinus n).1.1 (evenMinus n).1.2.1 (evenMinus n).1.2.2 (evenMinus n).2
  rw [re_weilPoleWeightFunctional_eq 1 lam (evenMinus n).1,
    logVector_evenMinus ⟨n, hn⟩, Finsupp.linearCombination_single] at hWm
  simp only [poleWeightArchRe, sub_self, zero_mul, add_zero, smul_eq_mul] at hWp hWm
  have hAp : |weilArchRe (EF.weilTest (evenPlus n).1.1 (evenPlus n).1.1)| ≤ Bd :=
    abs_weilArchRe_node_le n (evenPlus n).1.2.1.continuous (evenPlus n).1.2.2
      (norm_paperFT_evenPlus_le n) fun σ hσ => norm_paperFT_evenPlus_imag_le n hσ
  have hAm : |weilArchRe (EF.weilTest (evenMinus n).1.1 (evenMinus n).1.1)| ≤ Bd :=
    abs_weilArchRe_node_le n (evenMinus n).1.2.1.continuous (evenMinus n).1.2.2
      (norm_paperFT_evenMinus_le n) fun σ hσ => norm_paperFT_evenMinus_imag_le n hσ
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans hAp
  set c₀ := 2 * ((nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2) / Real.sqrt n with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  -- the upper bound
  have hcp : c₀ ≤ 2 * (∫ u, evenProfile n u ^ 2) / Real.sqrt n := by
    rw [integral_evenProfile_sq_eq]
    refine div_le_div_of_nonneg_right ?_ hsq.le
    have : 0 ≤ (nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2 := by positivity
    linarith
  have hup : (lam n) ≤ Bd / c₀ :=
    (le_div_of_node (lt_of_lt_of_le hc₀0 hcp) hWp hAp).trans
      (div_le_div_of_nonneg_left hBd0 hc₀0 hcp)
  -- the lower bound
  have hcm : c₀ ≤ 2 * (∫ u, oddProfile n u ^ 2) / Real.sqrt n :=
    div_le_div_of_nonneg_right (by linarith [le_integral_oddProfile_sq n]) hsq.le
  have hWm' : 0 ≤ weilArchRe (EF.weilTest (evenMinus n).1.1 (evenMinus n).1.1) -
      2 * (∫ u, oddProfile n u ^ 2) / Real.sqrt n * (-lam n) := by linarith
  have hlo : -lam n ≤ Bd / c₀ :=
    (le_div_of_node (lt_of_lt_of_le hc₀0 hcm) hWm' hAm).trans
      (div_le_div_of_nonneg_left hBd0 hc₀0 hcm)
  have hfin : Bd / c₀ = Bd * (Real.sqrt n * nodeScale n / (2 * ∫ u, narrowBump 0 u ^ 2)) := by
    rw [hc₀]
    field_simp
  have hkey := node_bound_le (n := n) (J₀ := ∫ u, narrowBump 0 u ^ 2) (P := bumpPoleConst)
    (K := gammaLogConst) (I₀ := bumpMassConst) (I₁ := bumpLogConst) hn1 hJ bumpMassConst_nonneg
    bumpLogConst_nonneg
  rw [← hmeq, ← hBd, ← hfin] at hkey
  rw [abs_le]
  constructor <;> linarith

end RHTower.EvenSector

end
