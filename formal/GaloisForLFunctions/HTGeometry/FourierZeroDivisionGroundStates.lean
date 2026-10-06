import GaloisForLFunctions.HTGeometry.FourierZeroFlipRealZeros

/-!
# Ground states are closed under division by non-real Fourier zeros

For a real measurable symbol `S`, put `Q(f) = ∫ S |f̂|²` and `N(f) = ∫ |f̂|²` over the real line
(`f̂ = paperFT f`).  The comparison class (`InClass`) consists of `Cⁿ` functions supported in
`[-L, L]` whose transforms vanish on a set `E`.  A level `μ` bounds the Rayleigh quotient from
below on the class (`IsGroundLevel`); a *ground state* at level `μ` (`IsGround`) is a member with
`Q`, `N` finite and `Q = μ N`.

**Division** (`isGround_flipAux`).  Let `f₀` be a ground state and `z₀ = x₀ + i y₀ ∉ E`, `y₀ ≠ 0`,
a zero of `f̂₀`.  Then `g = flipAux L f₀ z₀`, with `ĝ = f̂₀/(w − z₀)`, is a ground state.  On the
real line `|f̂₀|² = |(t − x₀)ĝ|² + y₀²|ĝ|²` (`sq_norm_split`), and both pieces are transforms of
class members; `Q ≥ μ N` holds for each piece and with equality for their sum, hence for each.

**Multiplicity bound** (`card_lt_of_isGround`).  Dividing by distinct non-real zeros one at a time
(`divChain`) gives ground states with transforms `f̂₀/∏_{l<j}(w − z_l)`, which are linearly
independent (`linearIndependent_divChain`: a vanishing combination is a polynomial with infinitely
many real roots, evaluated at the last division point).  So if no `d + 1` ground states are
linearly independent, `f̂₀` has fewer than `d` distinct non-real zeros outside `E`.

**Real-rooted ground state** (`exists_isGround_real_zeros`).  Under the same bound, some nonzero
ground state has only real zeros outside `E`: otherwise each ground state of the chain has a
non-real zero to divide by, and the chain produces `d + 1` independent ground states.  No
simplicity of the ground level is assumed; for `d = 1` every ground state is real-rooted outside
`E`, which is the simple-eigenline case `im_eq_zero_of_simple_rayleigh_contDiff`.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Zeta23 Polynomial

namespace GaloisForLFunctions.HTGeometry.FourierZeroFlip

theorem contDiff_flipAux (L : ℝ) {n : ℕ} {f : ℝ → ℂ} (hf : ContDiff ℝ n f) (z₀ : ℂ) :
    ContDiff ℝ n (flipAux L f z₀) := by
  have hp := contDiff_prim L hf z₀
  have he : ContDiff ℝ n fun x : ℝ => cexp (-(I * z₀ * x)) := by
    have : ContDiff ℝ n fun x : ℝ => -(I * z₀ * (x : ℂ)) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
    exact Complex.contDiff_exp.comp this
  exact (contDiff_const.mul he).mul hp

theorem continuous_paperFT_ofReal {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hc : Continuous f)
    (hs : SupportedIn L f) : Continuous fun t : ℝ => paperFT f t := by
  have h : (fun t : ℝ => paperFT f t) = fun t : ℝ => ∫ x in (-L)..L, f x * cexp (I * t * x) :=
    funext fun t => paperFT_eq_intervalIntegral hL hs t
  rw [h]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t x : ℝ => f x * cexp (I * t * x)) (by fun_prop) _ _

theorem integrable_paperFT_integrand {L : ℝ} {f : ℝ → ℂ} (hc : Continuous f)
    (hs : SupportedIn L f) (w : ℂ) : Integrable fun u : ℝ => f u * cexp (I * w * u) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  exact HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun x hx => by simp [hs x hx]

theorem paperFT_add_mul {L : ℝ} {f g : ℝ → ℂ} (hf : Continuous f) (hfs : SupportedIn L f)
    (hg : Continuous g) (hgs : SupportedIn L g) (c w : ℂ) :
    paperFT (fun x => f x + c * g x) w = paperFT f w + c * paperFT g w := by
  unfold paperFT
  rw [← integral_const_mul, ← integral_add (integrable_paperFT_integrand hf hfs w)
    ((integrable_paperFT_integrand hg hgs w).const_mul c)]
  congr 1
  funext u
  ring

/-- On the real line `|F|² = |F + i y₀ F/(t − z₀)|² + |y₀ F/(t − z₀)|²`, `y₀ = Im z₀ ≠ 0`. -/
theorem sq_norm_split (F : ℂ) (t : ℝ) {z₀ : ℂ} (hz : z₀.im ≠ 0) :
    ‖F‖ ^ 2 = ‖F + (I * z₀.im) * (F / ((t : ℂ) - z₀))‖ ^ 2 +
      ‖(z₀.im : ℂ) * (F / ((t : ℂ) - z₀))‖ ^ 2 := by
  have hD : (t : ℂ) - z₀ ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hz this
  have hpos : 0 < (t - z₀.re) ^ 2 + z₀.im ^ 2 := by positivity
  have hnD : Complex.normSq ((t : ℂ) - z₀) = (t - z₀.re) ^ 2 + z₀.im ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have key : (t : ℂ) - z₀ + I * z₀.im = ((t - z₀.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have h1 : F + (I * z₀.im) * (F / ((t : ℂ) - z₀)) =
      F * ((t - z₀.re : ℝ) : ℂ) / ((t : ℂ) - z₀) := by
    rw [← key]
    field_simp
  rw [h1, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_div,
    Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_div, Complex.normSq_ofReal,
    Complex.normSq_ofReal, hnD]
  field_simp

/-- A member of the comparison class: `Cⁿ`, supported in `[-L, L]`, transform vanishing on `E`. -/
def InClass (L : ℝ) (n : ℕ) (E : Set ℂ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ n f ∧ SupportedIn L f ∧ ∀ w ∈ E, paperFT f w = 0

/-- `μ` bounds the Rayleigh quotient `∫ S|f̂|² / ∫ |f̂|²` from below on the class. -/
def IsGroundLevel (L : ℝ) (n : ℕ) (E : Set ℂ) (S : ℝ → ℝ) (μ : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, InClass L n E f → Integrable (fun t : ℝ => S t * ‖paperFT f t‖ ^ 2) →
    Integrable (fun t : ℝ => ‖paperFT f t‖ ^ 2) →
    μ * ∫ t : ℝ, ‖paperFT f t‖ ^ 2 ≤ ∫ t : ℝ, S t * ‖paperFT f t‖ ^ 2

/-- A ground state at level `μ`: a class member with finite energies and Rayleigh value `μ`. -/
def IsGround (L : ℝ) (n : ℕ) (E : Set ℂ) (S : ℝ → ℝ) (μ : ℝ) (f : ℝ → ℂ) : Prop :=
  InClass L n E f ∧ Integrable (fun t : ℝ => S t * ‖paperFT f t‖ ^ 2) ∧
    Integrable (fun t : ℝ => ‖paperFT f t‖ ^ 2) ∧
    ∫ t : ℝ, S t * ‖paperFT f t‖ ^ 2 = μ * ∫ t : ℝ, ‖paperFT f t‖ ^ 2

theorem ne_of_im_ne_zero (t : ℝ) {z₀ : ℂ} (hz : z₀.im ≠ 0) : (t : ℂ) ≠ z₀ := by
  intro h
  apply hz
  rw [← h]
  simp

/-- **Division of a ground state by a non-real Fourier zero.**  `flipAux L f₀ z₀`, with transform
`f̂₀/(w − z₀)`, is again a ground state at the same level. -/
theorem isGround_flipAux {L : ℝ} (hL : 0 ≤ L) {n : ℕ} {E : Set ℂ} {S : ℝ → ℝ}
    (hS : Measurable S) {μ : ℝ} (hlev : IsGroundLevel L n E S μ) {f₀ : ℝ → ℂ}
    (hf₀ : IsGround L n E S μ f₀) {z₀ : ℂ} (hz : paperFT f₀ z₀ = 0) (him : z₀.im ≠ 0)
    (hzE : z₀ ∉ E) : IsGround L n E S μ (flipAux L f₀ z₀) := by
  obtain ⟨⟨hcd, hs, hE⟩, hQi, hNi, hQ⟩ := hf₀
  have hc : Continuous f₀ := hcd.continuous
  set g := flipAux L f₀ z₀ with hg
  have hgc : Continuous g := continuous_flipAux L hc z₀
  have hgs : SupportedIn L g := supportedIn_flipAux hL hc hs hz
  have hgcd : ContDiff ℝ n g := contDiff_flipAux L hcd z₀
  have hgw : ∀ w : ℂ, w ≠ z₀ → paperFT g w = paperFT f₀ w / (w - z₀) :=
    fun w hw => paperFT_flipAux hL hc hs hz hw
  set c : ℂ := I * z₀.im with hcdef
  set h₁ : ℝ → ℂ := fun x => f₀ x + c * g x with hh₁
  set h₂ : ℝ → ℂ := fun x => 0 + (z₀.im : ℂ) * g x with hh₂
  have hz0 : Continuous (fun _ : ℝ => (0 : ℂ)) := continuous_const
  have hzs0 : SupportedIn L (fun _ : ℝ => (0 : ℂ)) := fun _ _ => rfl
  have h₁w : ∀ w : ℂ, paperFT h₁ w = paperFT f₀ w + c * paperFT g w :=
    fun w => paperFT_add_mul hc hs hgc hgs c w
  have hpz : ∀ w : ℂ, paperFT (fun _ : ℝ => (0 : ℂ)) w = 0 := fun w => by simp [paperFT]
  have h₂w : ∀ w : ℂ, paperFT h₂ w = (z₀.im : ℂ) * paperFT g w := fun w => by
    rw [paperFT_add_mul hz0 hzs0 hgc hgs, hpz, zero_add]
  have hsupp : ∀ {u v : ℝ → ℂ} (d : ℂ), SupportedIn L u → SupportedIn L v →
      SupportedIn L (fun x => u x + d * v x) := fun d hu hv x hx => by simp [hu x hx, hv x hx]
  have hgE : ∀ w ∈ E, paperFT g w = 0 := fun w hw => by
    rw [hgw w (fun h => hzE (h ▸ hw)), hE w hw, zero_div]
  have hcl₁ : InClass L n E h₁ :=
    ⟨hcd.add (contDiff_const.mul hgcd), hsupp c hs hgs,
      fun w hw => by rw [h₁w, hE w hw, hgE w hw]; ring⟩
  have hcl₂ : InClass L n E h₂ :=
    ⟨contDiff_const.add (contDiff_const.mul hgcd), hsupp _ hzs0 hgs,
      fun w hw => by rw [h₂w, hgE w hw]; ring⟩
  have hclg : InClass L n E g := ⟨hgcd, hgs, hgE⟩
  -- pointwise splitting on the real line
  have hsplit : ∀ t : ℝ, ‖paperFT f₀ t‖ ^ 2 = ‖paperFT h₁ t‖ ^ 2 + ‖paperFT h₂ t‖ ^ 2 := by
    intro t
    rw [h₁w, h₂w, hgw t (ne_of_im_ne_zero t him)]
    exact sq_norm_split _ t him
  have hle₁ : ∀ t : ℝ, ‖paperFT h₁ t‖ ^ 2 ≤ ‖paperFT f₀ t‖ ^ 2 := fun t => by
    rw [hsplit t]; nlinarith [sq_nonneg ‖paperFT h₂ t‖]
  have hle₂ : ∀ t : ℝ, ‖paperFT h₂ t‖ ^ 2 ≤ ‖paperFT f₀ t‖ ^ 2 := fun t => by
    rw [hsplit t]; nlinarith [sq_nonneg ‖paperFT h₁ t‖]
  have hcont : ∀ {u : ℝ → ℂ}, InClass L n E u → Continuous fun t : ℝ => ‖paperFT u t‖ ^ 2 :=
    fun hu => (continuous_paperFT_ofReal hL hu.1.continuous hu.2.1).norm.pow 2
  have hNint : ∀ {u : ℝ → ℂ}, InClass L n E u → (∀ t : ℝ, ‖paperFT u t‖ ^ 2 ≤ ‖paperFT f₀ t‖ ^ 2) →
      Integrable fun t : ℝ => ‖paperFT u t‖ ^ 2 := fun hu hle =>
    hNi.mono' (hcont hu).aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [norm_pow, norm_norm]; exact hle t)
  have hQint : ∀ {u : ℝ → ℂ}, InClass L n E u → (∀ t : ℝ, ‖paperFT u t‖ ^ 2 ≤ ‖paperFT f₀ t‖ ^ 2) →
      Integrable fun t : ℝ => S t * ‖paperFT u t‖ ^ 2 := fun hu hle =>
    hQi.mono (hS.aestronglyMeasurable.mul (hcont hu).aestronglyMeasurable)
      (Eventually.of_forall fun t => by
        simp only [norm_mul, norm_pow, norm_norm]
        exact mul_le_mul_of_nonneg_left (hle t) (norm_nonneg _))
  have hN₁ := hNint hcl₁ hle₁
  have hN₂ := hNint hcl₂ hle₂
  have hQ₁ := hQint hcl₁ hle₁
  have hQ₂ := hQint hcl₂ hle₂
  have hNsum : (∫ t : ℝ, ‖paperFT f₀ t‖ ^ 2) =
      (∫ t : ℝ, ‖paperFT h₁ t‖ ^ 2) + ∫ t : ℝ, ‖paperFT h₂ t‖ ^ 2 := by
    rw [← integral_add hN₁ hN₂]
    exact integral_congr_ae (Eventually.of_forall hsplit)
  have hQsum : (∫ t : ℝ, S t * ‖paperFT f₀ t‖ ^ 2) =
      (∫ t : ℝ, S t * ‖paperFT h₁ t‖ ^ 2) + ∫ t : ℝ, S t * ‖paperFT h₂ t‖ ^ 2 := by
    rw [← integral_add hQ₁ hQ₂]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only [hsplit t, mul_add])
  have hl₁ := hlev h₁ hcl₁ hQ₁ hN₁
  have hl₂ := hlev h₂ hcl₂ hQ₂ hN₂
  have heq₂ : (∫ t : ℝ, S t * ‖paperFT h₂ t‖ ^ 2) = μ * ∫ t : ℝ, ‖paperFT h₂ t‖ ^ 2 := by
    have h0 := hQ
    rw [hNsum, hQsum, mul_add] at h0
    linarith
  -- rescale from `h₂ = y₀ g` to `g`
  have hy2 : (0 : ℝ) < z₀.im ^ 2 := by positivity
  have hscale : ∀ t : ℝ, ‖paperFT h₂ t‖ ^ 2 = z₀.im ^ 2 * ‖paperFT g t‖ ^ 2 := fun t => by
    rw [h₂w, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hgN : (fun t : ℝ => ‖paperFT g t‖ ^ 2) =
      fun t : ℝ => (z₀.im ^ 2)⁻¹ * ‖paperFT h₂ t‖ ^ 2 := funext fun t => by
    rw [hscale t]; field_simp
  have hgQ : (fun t : ℝ => S t * ‖paperFT g t‖ ^ 2) =
      fun t : ℝ => (z₀.im ^ 2)⁻¹ * (S t * ‖paperFT h₂ t‖ ^ 2) := funext fun t => by
    rw [hscale t]; field_simp
  refine ⟨hclg, ?_, ?_, ?_⟩
  · rw [hgQ]; exact hQ₂.const_mul _
  · rw [hgN]; exact hN₂.const_mul _
  · rw [hgQ, hgN, integral_const_mul, integral_const_mul, heq₂]
    ring

theorem paperFT_zero_fun (w : ℂ) : paperFT (0 : ℝ → ℂ) w = 0 := by simp [paperFT]

theorem infinite_paperFT_ne_zero {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hc : Continuous f)
    (hs : SupportedIn L f) (hne : f ≠ 0) : {t : ℝ | paperFT f t ≠ 0}.Infinite := by
  intro hfin
  apply hne
  have hopen : IsOpen {t : ℝ | paperFT f t ≠ 0} :=
    isOpen_ne_fun (continuous_paperFT_ofReal hL hc hs) continuous_const
  have hempty : ∀ t : ℝ, paperFT f t = 0 := by
    intro t
    by_contra ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t ht
    refine (Set.Ioo_infinite (show t - ε < t + ε by linarith)) (hfin.subset fun x hx => ?_)
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact eq_zero_of_paperFT_eq_zero hc hs 0 fun t _ => hempty t

/-- Successive division of `f₀` by the points `zs 0, zs 1, …`. -/
def divChain (L : ℝ) (f₀ : ℝ → ℂ) (zs : ℕ → ℂ) : ℕ → ℝ → ℂ
  | 0 => f₀
  | j + 1 => flipAux L (divChain L f₀ zs j) (zs j)

/-- The first `j` division points are non-real, avoid `E`, and are zeros at their step. -/
def ChainAdmissible (L : ℝ) (E : Set ℂ) (f₀ : ℝ → ℂ) (zs : ℕ → ℂ) (j : ℕ) : Prop :=
  ∀ i < j, (zs i).im ≠ 0 ∧ zs i ∉ E ∧ paperFT (divChain L f₀ zs i) (zs i) = 0

theorem divChain_spec {L : ℝ} (hL : 0 ≤ L) {n : ℕ} {E : Set ℂ} {S : ℝ → ℝ}
    (hS : Measurable S) {μ : ℝ} (hlev : IsGroundLevel L n E S μ) {f₀ : ℝ → ℂ}
    (hf₀ : IsGround L n E S μ f₀) (zs : ℕ → ℂ) :
    ∀ j : ℕ, ChainAdmissible L E f₀ zs j →
      IsGround L n E S μ (divChain L f₀ zs j) ∧
        ∀ w : ℂ, (∀ i < j, w ≠ zs i) →
          paperFT (divChain L f₀ zs j) w = paperFT f₀ w / ∏ i ∈ Finset.range j, (w - zs i)
  | 0, _ => ⟨hf₀, fun w _ => by simp [divChain]⟩
  | j + 1, hadm => by
    have hadm' : ChainAdmissible L E f₀ zs j := fun i hi => hadm i (Nat.lt_succ_of_lt hi)
    obtain ⟨hg, hft⟩ := divChain_spec hL hS hlev hf₀ zs j hadm'
    obtain ⟨him, hzE, hz⟩ := hadm j (Nat.lt_succ_self j)
    refine ⟨isGround_flipAux hL hS hlev hg hz him hzE, fun w hw => ?_⟩
    have hwj : w ≠ zs j := hw j (Nat.lt_succ_self j)
    show paperFT (flipAux L (divChain L f₀ zs j) (zs j)) w = _
    rw [paperFT_flipAux hL hg.1.1.continuous hg.1.2.1 hz hwj,
      hft w (fun i hi => hw i (Nat.lt_succ_of_lt hi)), Finset.prod_range_succ, div_div]

/-- Coefficients of a vanishing combination `Σ c_i F/P_i`, `P_i = ∏_{l<i}(t − z_l)`, vanish. -/
theorem eq_zero_of_sum_div_prod {F : ℝ → ℂ} (hF : {t : ℝ | F t ≠ 0}.Infinite) (zs : ℕ → ℂ) :
    ∀ (k : ℕ), (∀ i < k, ∀ t : ℝ, (t : ℂ) - zs i ≠ 0) → ∀ (c : ℕ → ℂ),
      (∀ t : ℝ, ∑ i ∈ Finset.range (k + 1),
        c i * (F t / ∏ l ∈ Finset.range i, ((t : ℂ) - zs l)) = 0) → ∀ i ≤ k, c i = 0
  | 0, _, c, h, i, hi => by
    obtain ⟨t, ht⟩ := hF.nonempty
    have h0 := h t
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Finset.range_zero,
      Finset.prod_empty, div_one] at h0
    rw [Nat.le_zero.mp hi]
    exact (mul_eq_zero.mp h0).resolve_right ht
  | k + 1, hreal, c, h, i, hi => by
    have hP : ∀ j ≤ k + 1, ∀ t : ℝ, ∏ l ∈ Finset.range j, ((t : ℂ) - zs l) ≠ 0 :=
      fun j hj t => Finset.prod_ne_zero_iff.mpr fun l hl =>
        hreal l (lt_of_lt_of_le (Finset.mem_range.mp hl) hj) t
    let Q : ℂ[X] := ∑ i ∈ Finset.range (k + 2),
      C (c i) * ∏ l ∈ Finset.Ico i (k + 1), (X - C (zs l))
    have hQeval : ∀ x : ℂ, Q.eval x =
        ∑ i ∈ Finset.range (k + 2), c i * ∏ l ∈ Finset.Ico i (k + 1), (x - zs l) := by
      intro x
      simp [Q, eval_finsetSum, eval_prod]
    have hroot : ∀ t : ℝ, F t ≠ 0 → Q.eval (t : ℂ) = 0 := by
      intro t ht
      rw [hQeval]
      have hterm : ∀ i ∈ Finset.range (k + 2),
          c i * ∏ l ∈ Finset.Ico i (k + 1), ((t : ℂ) - zs l) =
            (∏ l ∈ Finset.range (k + 1), ((t : ℂ) - zs l)) / F t *
              (c i * (F t / ∏ l ∈ Finset.range i, ((t : ℂ) - zs l))) := by
        intro i hi
        have hik : i ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hsplit := Finset.prod_range_mul_prod_Ico (fun l => (t : ℂ) - zs l) hik
        have hPi := hP i hik t
        rw [← hsplit]
        field_simp
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, h t, mul_zero]
    have hQ0 : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono ?_ (hF.image Complex.ofReal_injective.injOn)
      rintro x ⟨t, ht, rfl⟩
      exact hroot t ht
    have hck : c (k + 1) = 0 := by
      have h0 := congrArg (Polynomial.eval (zs k)) hQ0
      rw [hQeval, Polynomial.eval_zero, Finset.sum_range_succ, Finset.Ico_self,
        Finset.prod_empty, mul_one] at h0
      rw [Finset.sum_eq_zero, zero_add] at h0
      · exact h0
      · intro j hj
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [Finset.prod_eq_zero (i := k) (Finset.mem_Ico.mpr ⟨hjk, Nat.lt_succ_self k⟩)
          (sub_self _), mul_zero]
    have h' : ∀ t : ℝ, ∑ i ∈ Finset.range (k + 1),
        c i * (F t / ∏ l ∈ Finset.range i, ((t : ℂ) - zs l)) = 0 := by
      intro t
      have := h t
      rw [Finset.sum_range_succ, hck, zero_mul, add_zero] at this
      exact this
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_iff.mpr hi) with hi' | rfl
    · exact eq_zero_of_sum_div_prod hF zs k (fun j hj => hreal j (Nat.lt_succ_of_lt hj)) c h' i
        (Nat.lt_succ_iff.mp hi')
    · exact hck

theorem paperFT_finset_sum_smul {L : ℝ} {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → ℝ → ℂ)
    (hgc : ∀ i, Continuous (g i)) (hgs : ∀ i, SupportedIn L (g i)) (w : ℂ) :
    paperFT (∑ i ∈ s, c i • g i) w = ∑ i ∈ s, c i * paperFT (g i) w := by
  unfold paperFT
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  have hfun : (fun u : ℝ => ∑ i ∈ s, c i * g i u * cexp (I * w * u)) =
      fun u : ℝ => ∑ i ∈ s, c i * (g i u * cexp (I * w * u)) :=
    funext fun u => Finset.sum_congr rfl fun i _ => by ring
  rw [hfun, integral_finsetSum s fun i _ =>
    (integrable_paperFT_integrand (hgc i) (hgs i) w).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem linearIndependent_divChain {L : ℝ} (hL : 0 ≤ L) {n : ℕ} {E : Set ℂ} {S : ℝ → ℝ}
    (hS : Measurable S) {μ : ℝ} (hlev : IsGroundLevel L n E S μ) {f₀ : ℝ → ℂ}
    (hf₀ : IsGround L n E S μ f₀) (hne : f₀ ≠ 0) (zs : ℕ → ℂ) (k : ℕ)
    (hadm : ChainAdmissible L E f₀ zs k) :
    LinearIndependent ℂ (fun i : Fin (k + 1) => divChain L f₀ zs i) := by
  have hadmj : ∀ j ≤ k, ChainAdmissible L E f₀ zs j :=
    fun j hj i hi => hadm i (lt_of_lt_of_le hi hj)
  have hspec := fun (j : Fin (k + 1)) =>
    divChain_spec hL hS hlev hf₀ zs j (hadmj j (Nat.lt_succ_iff.mp j.isLt))
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let c' : ℕ → ℂ := fun j => if h : j < k + 1 then c ⟨j, h⟩ else 0
  have hreal : ∀ j < k, ∀ t : ℝ, (t : ℂ) - zs j ≠ 0 :=
    fun j hj t => sub_ne_zero.mpr (ne_of_im_ne_zero t (hadm j hj).1)
  have hsum : ∀ t : ℝ, ∑ j ∈ Finset.range (k + 1),
      c' j * (paperFT f₀ t / ∏ l ∈ Finset.range j, ((t : ℂ) - zs l)) = 0 := by
    intro t
    have h0 := congrArg (fun φ : ℝ → ℂ => paperFT φ t) hc
    rw [paperFT_finset_sum_smul (L := L) Finset.univ c _ (fun j => (hspec j).1.1.1.continuous)
      (fun j => (hspec j).1.1.2.1), paperFT_zero_fun] at h0
    rw [← h0, ← Fin.sum_univ_eq_sum_range (fun j => c' j *
      (paperFT f₀ t / ∏ l ∈ Finset.range j, ((t : ℂ) - zs l)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [c', dif_pos j.isLt, Fin.eta]
    rw [(hspec j).2 t fun l hl => ne_of_im_ne_zero t (hadm l (lt_of_lt_of_le hl
      (Nat.lt_succ_iff.mp j.isLt))).1]
  have := eq_zero_of_sum_div_prod (infinite_paperFT_ne_zero hL hf₀.1.1.continuous hf₀.1.2.1 hne)
    zs k hreal c' hsum i (Nat.lt_succ_iff.mp i.isLt)
  simp only [c', dif_pos i.isLt, Fin.eta] at this
  exact this

/-- **Multiplicity bound.** If no `d + 1` ground states are linearly independent, a ground state's
transform has fewer than `d` distinct non-real zeros outside `E`. -/
theorem card_lt_of_isGround {L : ℝ} (hL : 0 ≤ L) {n : ℕ} {E : Set ℂ} {S : ℝ → ℝ}
    (hS : Measurable S) {μ : ℝ} (hlev : IsGroundLevel L n E S μ) {d : ℕ}
    (hdim : ∀ g : Fin (d + 1) → ℝ → ℂ, (∀ i, IsGround L n E S μ (g i)) → ¬ LinearIndependent ℂ g)
    {f₀ : ℝ → ℂ} (hf₀ : IsGround L n E S μ f₀) (hne : f₀ ≠ 0) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, paperFT f₀ z = 0 ∧ z.im ≠ 0 ∧ z ∉ E) : Z.card < d := by
  classical
  by_contra hlt
  push Not at hlt
  let e : Fin Z.card ≃ Z := Z.equivFin.symm
  let zs : ℕ → ℂ := fun i => if h : i < Z.card then (e ⟨i, h⟩ : ℂ) else 0
  have hzsZ : ∀ i < Z.card, zs i ∈ Z := fun i hi => by
    simp only [zs, dif_pos hi]
    exact (e ⟨i, hi⟩).2
  have hinj : ∀ i j, i < Z.card → j < Z.card → zs i = zs j → i = j := by
    intro i j hi hj h
    simp only [zs, dif_pos hi, dif_pos hj] at h
    have := e.injective (Subtype.ext h)
    exact congrArg Fin.val this
  have hadm : ∀ j ≤ d, ChainAdmissible L E f₀ zs j := by
    intro j
    induction j with
    | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact ih (by omega) i hi
      · have hjc : i < Z.card := by omega
        obtain ⟨hz0, him, hzE⟩ := hZ _ (hzsZ i hjc)
        refine ⟨him, hzE, ?_⟩
        rw [(divChain_spec hL hS hlev hf₀ zs i (ih (by omega))).2 (zs i)
          (fun l hl h => absurd (hinj i l hjc (by omega) h) (by omega)), hz0, zero_div]
  exact hdim (fun i => divChain L f₀ zs i)
    (fun i => (divChain_spec hL hS hlev hf₀ zs i (hadm i (Nat.lt_succ_iff.mp i.isLt))).1)
    (linearIndependent_divChain hL hS hlev hf₀ hne zs d (hadm d le_rfl))

/-- **A real-rooted ground state exists.** If no `d + 1` ground states are linearly independent and
a nonzero ground state exists, some nonzero ground state has only real zeros outside `E`. -/
theorem exists_isGround_real_zeros {L : ℝ} (hL : 0 ≤ L) {n : ℕ} {E : Set ℂ} {S : ℝ → ℝ}
    (hS : Measurable S) {μ : ℝ} (hlev : IsGroundLevel L n E S μ) {d : ℕ}
    (hdim : ∀ g : Fin (d + 1) → ℝ → ℂ, (∀ i, IsGround L n E S μ (g i)) → ¬ LinearIndependent ℂ g)
    {f₀ : ℝ → ℂ} (hf₀ : IsGround L n E S μ f₀) (hne : f₀ ≠ 0) :
    ∃ g : ℝ → ℂ, IsGround L n E S μ g ∧ g ≠ 0 ∧
      ∀ z : ℂ, paperFT g z = 0 → z ∉ E → z.im = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  let pick : (ℝ → ℂ) → ℂ := fun g =>
    if h : ∃ z : ℂ, paperFT g z = 0 ∧ z ∉ E ∧ z.im ≠ 0 then h.choose else 0
  let seq : ℕ → ℝ → ℂ := fun j => Nat.rec f₀ (fun _ g => flipAux L g (pick g)) j
  let zs : ℕ → ℂ := fun j => pick (seq j)
  have hseq : ∀ j, divChain L f₀ zs j = seq j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      show flipAux L (divChain L f₀ zs j) (zs j) = flipAux L (seq j) (pick (seq j))
      rw [ih]
  have hadm : ∀ j, ChainAdmissible L E f₀ zs j := by
    intro j
    induction j with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ j ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact ih i hi
      · obtain ⟨hg, hft⟩ := divChain_spec hL hS hlev hf₀ zs i ih
        have hgne : divChain L f₀ zs i ≠ 0 := by
          intro h0
          obtain ⟨t, ht⟩ := (infinite_paperFT_ne_zero hL hf₀.1.1.continuous hf₀.1.2.1 hne).nonempty
          have hval := hft t fun l hl => ne_of_im_ne_zero t (ih l hl).1
          rw [h0] at hval
          have hz : paperFT (0 : ℝ → ℂ) (t : ℂ) = 0 := paperFT_zero_fun _
          rw [hz] at hval
          exact div_ne_zero ht (Finset.prod_ne_zero_iff.mpr fun l hl =>
            sub_ne_zero.mpr (ne_of_im_ne_zero t (ih l (Finset.mem_range.mp hl)).1)) hval.symm
        have hex := hcon _ hg hgne
        have hzi : zs i = hex.choose := by
          show pick (seq i) = _
          rw [← hseq i]
          exact dif_pos hex
        obtain ⟨h1, h2, h3⟩ := hex.choose_spec
        rw [hzi]
        exact ⟨h3, h2, h1⟩
  exact hdim (fun i => divChain L f₀ zs i)
    (fun i => (divChain_spec hL hS hlev hf₀ zs i (hadm i)).1)
    (linearIndependent_divChain hL hS hlev hf₀ hne zs d (hadm d))

end GaloisForLFunctions.HTGeometry.FourierZeroFlip
