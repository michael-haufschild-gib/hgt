import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure

/-!
# Consistency of the Bochner measures of a Weil-positive system

For a full-cone Weil-positive `lam` and `C²` compactly supported tests `f, g`, the Bochner
measures `ν_f, ν_g` of `exists_spectralMeasure` satisfy

`|ĝ|² ν_f = |f̂|² ν_g`  (`spectralMeasure_consistency`),

as they must if `ν_f = |f̂|² μ` for one measure `μ`.  Both sides are finite measures with the same
characteristic function

`y ↦ W_lam(x ↦ ∫ (g ⋆ g̃)(u) (f ⋆ f̃)(x − y − u) du)`,

which is symmetric in `f, g`.  The identification uses that the Weil functional commutes with
averaging against a continuous compactly supported weight (`weilFullFunctional_average`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate NNReal ENNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-! ## Averages -/

/-- The average `x ↦ ∫ φ(u) k(x − y − u) du`. -/
def average (φ k : ℝ → ℂ) (y x : ℝ) : ℂ := ∫ u, φ u * k (x - y - u)

theorem average_eq_zero {φ k : ℝ → ℂ} {A a : ℝ} (hφ : ∀ u, φ u ≠ 0 → |u| ≤ A)
    (hk : ∀ x, k x ≠ 0 → |x| ≤ a) (y : ℝ) {x : ℝ} (hx : a + A + |y| < |x|) :
    average φ k y x = 0 := by
  unfold average
  refine (integral_congr_ae (Eventually.of_forall fun u => ?_)).trans (integral_zero ℝ ℂ)
  by_cases hu : φ u = 0
  · simp [hu]
  · have hu' := hφ u hu
    have hk0 : k (x - y - u) = 0 := by
      by_contra hne
      have h1 := hk _ hne
      have h2 : |x| - |y| - |u| ≤ |x - y - u| := by
        have := abs_sub_abs_le_abs_sub x (y + u)
        have h3 : |y + u| ≤ |y| + |u| := abs_add_le y u
        rw [show x - y - u = x - (y + u) by ring]
        linarith
      linarith
    simp [hk0]

theorem integrable_prod_average {φ k : ℝ → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hk : Continuous k) (hkc : HasCompactSupport k) (y : ℝ) (z : ℂ) :
    Integrable (Function.uncurry fun (x u : ℝ) => φ u * k (x - y - u) * cexp (I * z * x))
      (volume.prod volume) := by
  obtain ⟨A, hA⟩ := exists_abs_bound_of_hasCompactSupport hφc
  obtain ⟨a, ha⟩ := exists_abs_bound_of_hasCompactSupport hkc
  have hcont : Continuous (Function.uncurry fun (x u : ℝ) => φ u * k (x - y - u) * cexp (I * z * x)) := by
    change Continuous fun p : ℝ × ℝ => φ p.2 * k (p.1 - y - p.2) * cexp (I * z * p.1)
    fun_prop
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro
    ((isCompact_Icc (a := -(a + A + |y|)) (b := a + A + |y|)).prod
      (isCompact_Icc (a := -A) (b := A))) fun p hp => ?_)
  show φ p.2 * k (p.1 - y - p.2) * cexp (I * z * p.1) = 0
  rw [Set.mem_prod, not_and_or] at hp
  by_cases hu : φ p.2 = 0
  · simp [hu]
  · have hu' := hA p.2 hu
    rcases hp with hp | hp
    · have hx : a + A + |y| < |p.1| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hp
        rcases hp with h | h
        · have := neg_le_abs p.1
          linarith
        · have := le_abs_self p.1
          linarith
      have hk0 : k (p.1 - y - p.2) = 0 := by
        by_contra hne
        have h1 := ha _ hne
        have h2 : |p.1| - |y| - |p.2| ≤ |p.1 - y - p.2| := by
          have := abs_sub_abs_le_abs_sub p.1 (y + p.2)
          have h3 : |y + p.2| ≤ |y| + |p.2| := abs_add_le y p.2
          rw [show p.1 - y - p.2 = p.1 - (y + p.2) by ring]
          linarith
        linarith
      simp [hk0]
    · exfalso
      exact hp (Set.mem_Icc.mpr (abs_le.mp hu'))

/-- The transform of an average. -/
theorem paperFT_average {φ k : ℝ → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hk : Continuous k) (hkc : HasCompactSupport k) (y : ℝ) (z : ℂ) :
    paperFT (average φ k y) z = (∫ u, φ u * cexp (I * z * (y + u))) * paperFT k z := by
  unfold paperFT average
  have hswap := integral_integral_swap (integrable_prod_average hφ hφc hk hkc y z)
  have hL : (∫ x : ℝ, (∫ u, φ u * k (x - y - u)) * cexp (I * z * x)) =
      ∫ x : ℝ, ∫ u : ℝ, φ u * k (x - y - u) * cexp (I * z * x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← integral_mul_const]
  rw [hL, hswap, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have := paperFT_transl (y + u) k z
  unfold paperFT transl at this
  simp only [sub_sub] at this ⊢
  rw [show (∫ x : ℝ, φ u * k (x - (y + u)) * cexp (I * z * x)) =
      φ u * ∫ x : ℝ, k (x - (y + u)) * cexp (I * z * x) by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring, this]
  push_cast
  ring

/-! ## The three parts of the Weil functional -/

/-- The pole part `k̂(i/2) + k̂(−i/2)`. -/
def polePart (k : ℝ → ℂ) : ℂ := paperFT k (I / 2) + paperFT k (-I / 2)

/-- The prime part. -/
def primePart (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))

/-- The archimedean part. -/
def archPart (k : ℝ → ℂ) : ℂ := (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)

theorem weilFullFunctional_eq_parts (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    weilFullFunctional lam k = polePart k - primePart lam k + archPart k := rfl

theorem continuous_polePart_transl (k : ℝ → ℂ) :
    Continuous fun v : ℝ => polePart (transl v k) := by
  unfold polePart
  simp_rw [paperFT_transl]
  fun_prop

theorem continuous_archPart_transl {k : ℝ → ℂ} (hk : Admissible k) :
    Continuous fun v : ℝ => archPart (transl v k) := by
  unfold archPart
  simp_rw [paperFT_transl]
  refine continuous_const.mul (continuous_of_dominated
    (bound := fun r => ‖paperFT k r * (EF.gammaBracket r : ℂ)‖)
    (fun v => ?_) (fun v => Eventually.of_forall fun r => ?_) hk.arch.norm
    (Eventually.of_forall fun r => by fun_prop))
  · have hc := WeilHerglotz.continuous_paperFT_real hk.integrable
    have hcont : Continuous fun r : ℝ =>
        cexp (I * (r : ℂ) * v) * paperFT k r * (EF.gammaBracket r : ℂ) :=
      ((by fun_prop : Continuous fun r : ℝ => cexp (I * (r : ℂ) * v)).mul hc).mul
        (Complex.continuous_ofReal.comp WeilHerglotz.continuous_gammaBracket)
    exact hcont.aestronglyMeasurable
  · rw [mul_assoc, norm_mul, norm_cexp_I_mul_ofReal, one_mul]

theorem continuous_primePart_transl (lam : ℕ → ℝ) {k : ℝ → ℂ} (hk : Continuous k)
    (hkc : HasCompactSupport k) : Continuous fun v : ℝ => primePart lam (transl v k) :=
  continuous_primeSum_transl lam hk hkc

theorem integrable_mul_of_continuous {φ F : ℝ → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hF : Continuous F) : Integrable fun u => φ u * F u :=
  (hφ.mul hF).integrable_of_hasCompactSupport hφc.mul_right

theorem polePart_average {φ k : ℝ → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hk : Continuous k) (hkc : HasCompactSupport k) (y : ℝ) :
    polePart (average φ k y) = ∫ u, φ u * polePart (transl (y + u) k) := by
  unfold polePart
  rw [paperFT_average hφ hφc hk hkc, paperFT_average hφ hφc hk hkc]
  simp_rw [paperFT_transl]
  rw [← integral_mul_const, ← integral_mul_const,
    ← integral_add (integrable_mul_of_continuous hφ hφc (by fun_prop) |>.mul_const _)
      (integrable_mul_of_continuous hφ hφc (by fun_prop) |>.mul_const _)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  push_cast
  ring

theorem primePart_average (lam : ℕ → ℝ) {φ k : ℝ → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hk : Continuous k) (hkc : HasCompactSupport k) (y : ℝ) :
    primePart lam (average φ k y) = ∫ u, φ u * primePart lam (transl (y + u) k) := by
  obtain ⟨A, hA⟩ := exists_abs_bound_of_hasCompactSupport hφc
  obtain ⟨a, ha⟩ := exists_abs_bound_of_hasCompactSupport hkc
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (|a| + |A| + |y| + 1))
  set c : ℕ → ℂ := fun n => ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) with hc
  have hlarge : ∀ n, N ≤ n → |a| + |A| + |y| + 1 < Real.log n := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by
      have : Real.exp (|a| + |A| + |y| + 1) < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
      exact lt_trans (Real.exp_pos _) this
    rw [Real.lt_log_iff_exp_lt hnpos]
    exact lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hzero : ∀ x : ℝ, |a| < |x| → k x = 0 := by
    intro x hx
    by_contra hne
    have := ha x hne
    linarith [le_abs_self a]
  -- for `n ≥ N` and `|u| ≤ A` both translates vanish at `±log n`
  have hvan : ∀ n, N ≤ n → ∀ u : ℝ, φ u * (transl (y + u) k (Real.log n) +
      transl (y + u) k (-Real.log n)) = 0 := by
    intro n hn u
    by_cases hu : φ u = 0
    · simp [hu]
    · have hu' := hA u hu
      have hl := hlarge n hn
      have hl0 : 0 < Real.log n := by linarith [abs_nonneg a, abs_nonneg A, abs_nonneg y]
      have hyu : |y + u| ≤ |y| + |A| := (abs_add_le y u).trans (by linarith [le_abs_self A])
      have h1 : transl (y + u) k (Real.log n) = 0 := by
        refine hzero _ ?_
        have := abs_sub_abs_le_abs_sub (Real.log n) (y + u)
        rw [abs_of_pos hl0] at this
        linarith
      have h2 : transl (y + u) k (-Real.log n) = 0 := by
        refine hzero _ ?_
        have := abs_sub_abs_le_abs_sub (-Real.log n) (y + u)
        rw [abs_neg, abs_of_pos hl0] at this
        linarith
      rw [h1, h2, add_zero, mul_zero]
  have hLsum : primePart lam (average φ k y) =
      ∑ n ∈ Finset.range N, c n * (average φ k y (Real.log n) + average φ k y (-Real.log n)) := by
    unfold primePart
    refine tsum_eq_sum fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    have hl := hlarge n hn
    have hl0 : 0 < Real.log n := by linarith [abs_nonneg a, abs_nonneg A, abs_nonneg y]
    have h1 : average φ k y (Real.log n) = 0 :=
      average_eq_zero hA ha y (by rw [abs_of_pos hl0]; linarith [le_abs_self a, le_abs_self A])
    have h2 : average φ k y (-Real.log n) = 0 :=
      average_eq_zero hA ha y (by
        rw [abs_neg, abs_of_pos hl0]; linarith [le_abs_self a, le_abs_self A])
    rw [h1, h2, add_zero, mul_zero]
  have hRsum : ∀ u : ℝ, φ u * primePart lam (transl (y + u) k) =
      ∑ n ∈ Finset.range N, c n * (φ u * (transl (y + u) k (Real.log n) +
        transl (y + u) k (-Real.log n))) := by
    intro u
    unfold primePart
    rw [← tsum_mul_left]
    rw [tsum_eq_sum (s := Finset.range N) fun n hn => ?_]
    · refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hc]
      ring
    · rw [Finset.mem_range, not_lt] at hn
      rw [show φ u * (((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
          (transl (y + u) k (Real.log n) + transl (y + u) k (-Real.log n))) =
          ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
            (φ u * (transl (y + u) k (Real.log n) + transl (y + u) k (-Real.log n))) by ring,
        hvan n hn u, mul_zero]
  rw [hLsum, integral_congr_ae (Eventually.of_forall hRsum),
    integral_finsetSum _ fun n _ => (integrable_mul_of_continuous hφ hφc
      (by unfold transl; fun_prop)).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul]
  congr 1
  unfold average transl
  rw [← integral_add (integrable_mul_of_continuous hφ hφc (by fun_prop))
    (integrable_mul_of_continuous hφ hφc (by fun_prop))]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [sub_sub]
  ring

theorem archPart_average {φ k : ℝ → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hk : Admissible k) (y : ℝ) :
    archPart (average φ k y) = ∫ u, φ u * archPart (transl (y + u) k) := by
  unfold archPart
  simp_rw [paperFT_average hφ hφc hk.cont hk.supp, paperFT_transl]
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hint : Integrable (Function.uncurry fun (r u : ℝ) =>
      φ u * cexp (I * (r : ℂ) * (y + u)) * (paperFT k r * (EF.gammaBracket r : ℂ)))
      (volume.prod volume) := by
    have hprod := (hk.arch.norm).mul_prod (hφi.norm)
    refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc := WeilHerglotz.continuous_paperFT_real hk.integrable
      have hcont : Continuous (Function.uncurry fun (r u : ℝ) =>
          φ u * cexp (I * (r : ℂ) * (y + u)) * (paperFT k r * (EF.gammaBracket r : ℂ))) := by
        change Continuous fun p : ℝ × ℝ =>
          φ p.2 * cexp (I * (p.1 : ℂ) * (y + p.2)) * (paperFT k p.1 * (EF.gammaBracket p.1 : ℂ))
        have h1 : Continuous fun p : ℝ × ℝ => paperFT k p.1 * (EF.gammaBracket p.1 : ℂ) :=
          (hc.mul (Complex.continuous_ofReal.comp WeilHerglotz.continuous_gammaBracket)).comp
            continuous_fst
        exact ((hφ.comp continuous_snd).mul (by fun_prop)).mul h1
      exact hcont.aestronglyMeasurable
    · obtain ⟨r, u⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [show I * (r : ℂ) * ((y : ℂ) + (u : ℂ)) = I * (r : ℂ) * ((y + u : ℝ) : ℂ) by
        push_cast; ring, norm_cexp_I_mul_ofReal, mul_one]
      ring_nf
      exact le_rfl
  have hswap := integral_integral_swap hint
  have hL : (∫ r : ℝ, (∫ u, φ u * cexp (I * (r : ℂ) * (y + u))) * paperFT k r *
      (EF.gammaBracket r : ℂ)) =
      ∫ r : ℝ, ∫ u : ℝ, φ u * cexp (I * (r : ℂ) * (y + u)) *
        (paperFT k r * (EF.gammaBracket r : ℂ)) := by
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only
    rw [mul_assoc, ← integral_mul_const]
  have hR : (∫ u, φ u * ((1 / (2 * π) : ℂ) * ∫ r : ℝ, cexp (I * (r : ℂ) * ((y + u : ℝ) : ℂ)) *
      paperFT k r * (EF.gammaBracket r : ℂ))) =
      (1 / (2 * π) : ℂ) * ∫ u : ℝ, ∫ r : ℝ, φ u * cexp (I * (r : ℂ) * (y + u)) *
        (paperFT k r * (EF.gammaBracket r : ℂ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only
    push_cast
    ring
  rw [hL, hswap, hR]

/-- **The Weil functional commutes with averages.** -/
theorem weilFullFunctional_average (lam : ℕ → ℝ) {φ k : ℝ → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hk : Admissible k) (y : ℝ) :
    weilFullFunctional lam (average φ k y) =
      ∫ u, φ u * weilFullFunctional lam (transl (y + u) k) := by
  have hP := continuous_polePart_transl k
  have hQ := continuous_primePart_transl lam hk.cont hk.supp
  have hA := continuous_archPart_transl hk
  have i1 : Integrable fun u => φ u * polePart (transl (y + u) k) :=
    integrable_mul_of_continuous hφ hφc (hP.comp (continuous_const.add continuous_id))
  have i2 : Integrable fun u => φ u * primePart lam (transl (y + u) k) :=
    integrable_mul_of_continuous hφ hφc (hQ.comp (continuous_const.add continuous_id))
  have i3 : Integrable fun u => φ u * archPart (transl (y + u) k) :=
    integrable_mul_of_continuous hφ hφc (hA.comp (continuous_const.add continuous_id))
  have hsplit : (∫ u, φ u * weilFullFunctional lam (transl (y + u) k)) =
      (∫ u, φ u * polePart (transl (y + u) k)) - (∫ u, φ u * primePart lam (transl (y + u) k)) +
        ∫ u, φ u * archPart (transl (y + u) k) := by
    have i12 : Integrable fun u => φ u * polePart (transl (y + u) k) -
        φ u * primePart lam (transl (y + u) k) := i1.sub i2
    rw [← integral_sub i1 i2, ← integral_add i12 i3]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [weilFullFunctional_eq_parts]
    ring
  rw [hsplit, weilFullFunctional_eq_parts, polePart_average hφ hφc hk.cont hk.supp,
    primePart_average lam hφ hφc hk.cont hk.supp, archPart_average hφ hφc hk]

/-! ## Consistency -/

/-- The density `|f̂|²` as an `ℝ≥0`-valued function. -/
def specDensity (f : ℝ → ℂ) (r : ℝ) : ℝ≥0 := ‖paperFT f r‖₊ ^ 2

theorem measurable_specDensity {f : ℝ → ℂ} (hf : Integrable f) : Measurable (specDensity f) :=
  ((WeilHerglotz.continuous_paperFT_real hf).nnnorm.pow 2).measurable

theorem specDensity_eq_paperFT_weilTest {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (r : ℝ) : ((specDensity f r : ℝ) : ℂ) = paperFT (EF.weilTest f f) r := by
  rw [EF.paperFT_weilTest hf hf hfc hfc, Complex.conj_ofReal, Complex.mul_conj, specDensity]
  push_cast
  rw [Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem average_comm (f g : ℝ → ℂ) (y x : ℝ) :
    average (EF.weilTest g g) (EF.weilTest f f) y x =
      average (EF.weilTest f f) (EF.weilTest g g) y x := by
  unfold average
  rw [← integral_add_right_eq_self (μ := volume)
    (fun u => EF.weilTest g g u * EF.weilTest f f (x - y - u)) 0]
  have := integral_sub_left_eq_self (μ := volume)
    (fun u => EF.weilTest f f u * EF.weilTest g g (x - y - u)) (x - y)
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [add_zero, sub_sub_cancel]
  ring

theorem norm_paperFT_real_le (f : ℝ → ℂ) (r : ℝ) : ‖paperFT f r‖ ≤ ∫ u, ‖f u‖ := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [norm_mul, norm_cexp_I_mul_ofReal, mul_one]

theorem isFiniteMeasure_withDensity_specDensity {ν : Measure ℝ} [IsFiniteMeasure ν] (g : ℝ → ℂ) :
    IsFiniteMeasure (ν.withDensity fun r => (specDensity g r : ℝ≥0∞)) := by
  refine isFiniteMeasure_withDensity (ne_of_lt ?_)
  set C : ℝ≥0 := (‖∫ u, ‖g u‖‖₊) ^ 2 with hC
  have hle : ∀ r, (specDensity g r : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
    intro r
    have h1 : ‖paperFT g r‖ ≤ ∫ u, ‖g u‖ := norm_paperFT_real_le g r
    have h0 : 0 ≤ ∫ u, ‖g u‖ := integral_nonneg fun _ => norm_nonneg _
    rw [specDensity, hC, ENNReal.coe_le_coe]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_of_nonneg h0]
    exact h1
  calc ∫⁻ r, (specDensity g r : ℝ≥0∞) ∂ν ≤ ∫⁻ _, (C : ℝ≥0∞) ∂ν := lintegral_mono hle
    _ = C * ν Set.univ := lintegral_const _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top ν _)

/-- The characteristic function of `|ĝ|² ν_f` is the Weil functional of an average. -/
theorem charFun_withDensity_eq {lam : ℕ → ℝ} {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ∀ y, charFun ν y = spectralKernel lam f y) (y : ℝ) :
    charFun (ν.withDensity fun r => (specDensity g r : ℝ≥0∞)) y =
      weilFullFunctional lam (average (EF.weilTest g g) (EF.weilTest f f) y) := by
  have hwg := admissible_weilTest hg hgc
  have hwf := admissible_weilTest hf hfc
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  rw [weilFullFunctional_average lam hwg.cont hwg.supp hwf, charFun_apply_real,
    integral_withDensity_eq_integral_smul (measurable_specDensity hgint)]
  -- expand `|ĝ|²` as a transform and swap the integrals
  have hpt : ∀ r : ℝ, (specDensity g r) • cexp ((y : ℂ) * r * I) =
      ∫ u, EF.weilTest g g u * cexp (((y + u : ℝ) : ℂ) * r * I) := by
    intro r
    rw [NNReal.smul_def, Complex.real_smul,
      specDensity_eq_paperFT_weilTest hg.continuous hgc r, paperFT, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have hint : Integrable (Function.uncurry fun (r u : ℝ) =>
      EF.weilTest g g u * cexp (((y + u : ℝ) : ℂ) * r * I)) (ν.prod volume) := by
    have hprod := (integrable_const (μ := ν) (1 : ℝ)).mul_prod hwg.integrable.norm
    refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hcont : Continuous (Function.uncurry fun (r u : ℝ) =>
          EF.weilTest g g u * cexp (((y + u : ℝ) : ℂ) * r * I)) := by
        change Continuous fun p : ℝ × ℝ => EF.weilTest g g p.2 * cexp (((y + p.2 : ℝ) : ℂ) * p.1 * I)
        exact (hwg.cont.comp continuous_snd).mul (by fun_prop)
      exact hcont.aestronglyMeasurable
    · obtain ⟨r, u⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul, one_mul]
      rw [show ((y + u : ℝ) : ℂ) * (r : ℂ) * I = (((y + u) * r : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [integral_const_mul, ← charFun_apply_real, hν, spectralKernel]

/-- **Consistency of the Bochner measures.** `|ĝ|² ν_f = |f̂|² ν_g`. -/
theorem spectralMeasure_consistency {lam : ℕ → ℝ} {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {νf νg : Measure ℝ} [IsFiniteMeasure νf] [IsFiniteMeasure νg]
    (hνf : ∀ y, charFun νf y = spectralKernel lam f y)
    (hνg : ∀ y, charFun νg y = spectralKernel lam g y) :
    (νf.withDensity fun r => (specDensity g r : ℝ≥0∞)) =
      νg.withDensity fun r => (specDensity f r : ℝ≥0∞) := by
  haveI := isFiniteMeasure_withDensity_specDensity (ν := νf) g
  haveI := isFiniteMeasure_withDensity_specDensity (ν := νg) f
  refine Measure.ext_of_charFun (funext fun y => ?_)
  rw [charFun_withDensity_eq hf hfc hg hgc hνf y, charFun_withDensity_eq hg hgc hf hfc hνg y]
  congr 1
  funext x
  exact average_comm f g y x

end RHTower.WeilSpectral

end
