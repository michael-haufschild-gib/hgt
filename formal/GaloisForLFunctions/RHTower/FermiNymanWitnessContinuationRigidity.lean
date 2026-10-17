import GaloisForLFunctions.RHTower.FermiNymanWitnessExponentZeroRigidity
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionSharp
import GaloisForLFunctions.RHTower.FermiNymanWitnessSelfSimilarityCriterion
import GaloisForLFunctions.RHTower.XiLogDerivVinogradovKorobovPositive

/-!
# Self-similarity of Fermi witnesses from analytic continuation of the Mellin transform

Let `w` be a witness of the alternating Nyman–Beurling system of Mellin exponent `a < 1`
(`IsMellinFermiWitness w a`) with Mellin transform `W(z) = ∫_0^1 t^{z−1} w(t) dt` on `Re z > a`.
Its dyadic defect `(1 − 2^{−z}) W(z)` agrees on `a < Re z < 1` with the left form
`−2^{−z} z (1 − z) Φ₀(1 − z)/Ξ(1 − z)`, whose only possible poles are the points `1 − ρ` with
`Ξ(ρ) = 0`.  The exponent-zero rigidity theorem glues the two forms along `Re z = 0`, which needs
`Ξ ≠ 0` on `Re s ≥ 1`.

Here the two forms are glued along the boundary of an arbitrary open set `Ω ⊇ {Re z > a}` to which
`W` continues analytically.  If `Ω` is closed under moving to the right on horizontal lines, then
`Ω ∩ {Re z < 1}` is connected, and the identity theorem gives

`(1 − 2^{−z}) W(z) Ξ(1 − z) = −2^{−z} z (1 − z) Φ₀(1 − z)` on `Ω ∩ {Re z < 1}`.

If moreover `Ω` contains every pole `1 − ρ`, all poles are removable and the glued defect is entire.
It coincides with the exponent-`a` transform `U` wherever `ζ(1 − z) ≠ 0`, so it inherits the
polynomial growth of `U` (maximum modulus between the heights of Titchmarsh IX.7) and its decay
along the integers, hence vanishes identically, and `w(t/2) = w(t)` follows by Fourier uniqueness.
No majorant rate at the exponent is needed.

Two instances are unconditional.

* If `W` continues analytically to the right half-plane `Re z > 0`, the witness is self-similar
  (`Ξ ≠ 0` on `Re s ≥ 1`).
* If `W` continues analytically merely to the region
  `{Re z > a} ∪ {Re z > 0, |Im z| < 4} ∪ {Re z > 1/(59 log max(|Im z|, 2))}`,
  the witness is self-similar: every zero `ρ` of `ζ` with `|Im ρ| ≥ 4` satisfies
  `Re ρ ≤ 1 − 1/(58 log |Im ρ|)`, so every pole `1 − ρ` lies in that region.

Thus the domain on which the Mellin continuation must exist shrinks from the half-plane to the
known zero-free region, and any zero-free region transports to a rigidity statement through
`IsMellinContinuation.selfSimilar`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin

variable {w : ℝ → ℂ} {a : ℝ} {G : ℂ → ℂ} {Ω : Set ℂ}

/-! ## The strip product identity -/

/-- **Strip product identity.**  On `a < Re z < 1`,
`(1 − 2^{−z}) W(z) Ξ(1 − z) = −2^{−z} z (1 − z) Φ₀(1 − z)`, with no nonvanishing hypothesis. -/
theorem IsMellinFermiWitness.strip_product (hw : IsMellinFermiWitness w a) {z : ℂ}
    (hza : a < z.re) (hz1 : z.re < 1) :
    (1 - (2 : ℂ) ^ (-z)) * witnessMellin w z * zetaEntire (1 - z) =
      -((2 : ℂ) ^ (-z)) * z * (1 - z) * correlationMellin w (1 - z) := by
  have hz0' : 0 < z.re := lt_of_le_of_lt hw.nonneg hza
  have hs0 : 0 < (1 - z).re := by simp; linarith
  have hs1 : (1 - z).re < 1 := by simp; linarith
  have hs1a : (1 - z).re < 1 - a := by simp; linarith
  have hz : z ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hz0'; exact lt_irrefl 0 hz0'
  have hne1 : (1 : ℂ) - z ≠ 1 := by
    intro h; apply hz; linear_combination -h
  have hfub := hw.correlationMellin_eq hs0 hs1a
  rw [show (1 : ℂ) - (1 - z) = z by ring, mellin_fermiNymanGen_one hs0 hs1,
    show (1 : ℂ) - (1 - z) = z by ring] at hfub
  have hζ : riemannZeta (1 - z) = zetaEntire (1 - z) / (1 - z - 1) := by
    rw [zetaEntire_eq hne1]
    have : (1 : ℂ) - z - 1 ≠ 0 := by
      rw [show (1 : ℂ) - z - 1 = -z by ring]; exact neg_ne_zero.2 hz
    field_simp
  rw [hζ] at hfub
  have h2 : (2 : ℂ) ^ z ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]; exact Complex.exp_ne_zero _
  have hinv : (2 : ℂ) ^ (-z) * (2 : ℂ) ^ z = 1 := by
    rw [Complex.cpow_neg, inv_mul_cancel₀ h2]
  have hzz : (1 : ℂ) - z - 1 = -z := by ring
  have h1z : (1 : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  have key : z * (1 - z) * correlationMellin w (1 - z) =
      (1 - (2 : ℂ) ^ z) * zetaEntire (1 - z) * witnessMellin w z := by
    rw [hfub, hzz]
    field_simp
  linear_combination (2 : ℂ) ^ (-z) * key - witnessMellin w z * zetaEntire (1 - z) * hinv

/-! ## Analytic continuations of the witness Mellin transform -/

/-- An analytic continuation `G` of the witness Mellin transform `W` to an open set
`Ω ⊇ {Re z > a}` that is closed under moving to the right along horizontal lines. -/
structure IsMellinContinuation (w : ℝ → ℂ) (a : ℝ) (G : ℂ → ℂ) (Ω : Set ℂ) : Prop where
  isOpen : IsOpen Ω
  right : ∀ z ∈ Ω, ∀ x : ℝ, z.re ≤ x → (⟨x, z.im⟩ : ℂ) ∈ Ω
  strip : ∀ z : ℂ, a < z.re → z ∈ Ω
  diff : DifferentiableOn ℂ G Ω
  eq : ∀ z : ℂ, a < z.re → G z = witnessMellin w z

/-- `Ω ∩ {Re z < 1}` is preconnected: every point joins the vertical line `Re z = (a+1)/2` by a
horizontal segment, and that line lies in the strip. -/
theorem IsMellinContinuation.isPreconnected_inter (h : IsMellinContinuation w a G Ω)
    (ha1 : a < 1) : IsPreconnected (Ω ∩ {z : ℂ | z.re < 1}) := by
  set x₀ : ℝ := (a + 1) / 2 with hx₀
  have hx₀a : a < x₀ := by rw [hx₀]; linarith
  have hx₀1 : x₀ < 1 := by rw [hx₀]; linarith
  refine isPreconnected_of_forall (x₀ : ℂ) (fun y hy => ?_)
  set p : ℂ := ⟨x₀, y.im⟩ with hp
  refine ⟨segment ℝ y p ∪ segment ℝ p (x₀ : ℂ), ?_, Or.inr (right_mem_segment ℝ p _),
    Or.inl (left_mem_segment ℝ y p),
    (convex_segment y p).isPreconnected.union p (right_mem_segment ℝ y p)
      (left_mem_segment ℝ p _) (convex_segment p _).isPreconnected⟩
  have hy1 : y.re < 1 := hy.2
  rintro u (⟨α, β, hα, hβ, hαβ, rfl⟩ | ⟨α, β, hα, hβ, hαβ, rfl⟩)
  · have hre : (α • y + β • p).re = α * y.re + β * x₀ := by
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, hp]
    have him : (α • y + β • p).im = y.im := by
      simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, hp]
      linear_combination y.im * hαβ
    have hlt : α * y.re + β * x₀ < 1 := by
      have h1 : α * y.re ≤ α * max y.re x₀ := mul_le_mul_of_nonneg_left (le_max_left _ _) hα
      have h2 : β * x₀ ≤ β * max y.re x₀ := mul_le_mul_of_nonneg_left (le_max_right _ _) hβ
      have h3 : max y.re x₀ < 1 := max_lt hy1 hx₀1
      calc α * y.re + β * x₀ ≤ (α + β) * max y.re x₀ := by linarith
        _ = max y.re x₀ := by rw [hαβ, one_mul]
        _ < 1 := h3
    refine ⟨?_, by rw [mem_setOf_eq, hre]; exact hlt⟩
    rcases le_or_gt y.re x₀ with hyx | hyx
    · have hge : y.re ≤ (α • y + β • p).re := by
        rw [hre]
        have := mul_le_mul_of_nonneg_left hyx hβ
        calc y.re = (α + β) * y.re := by rw [hαβ, one_mul]
          _ ≤ α * y.re + β * x₀ := by linarith
      have hmem := h.right y hy.1 _ hge
      have heq : (⟨(α • y + β • p).re, y.im⟩ : ℂ) = α • y + β • p := Complex.ext rfl him.symm
      rw [heq] at hmem
      exact hmem
    · refine h.strip _ ?_
      rw [hre]
      have := mul_le_mul_of_nonneg_left hyx.le hα
      calc a < x₀ := hx₀a
        _ = (α + β) * x₀ := by rw [hαβ, one_mul]
        _ ≤ α * y.re + β * x₀ := by linarith
  · have hre : (α • p + β • (x₀ : ℂ)).re = x₀ := by
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.ofReal_re, hp]
      linear_combination x₀ * hαβ
    exact ⟨h.strip _ (by rw [hre]; exact hx₀a), by rw [mem_setOf_eq, hre]; exact hx₀1⟩

/-- **Product identity on the continuation region.**  On `Ω ∩ {Re z < 1}`,
`(1 − 2^{−z}) G(z) Ξ(1 − z) = −2^{−z} z (1 − z) Φ₀(1 − z)`. -/
theorem IsMellinContinuation.product_identity (hw : IsMellinFermiWitness w a)
    (h : IsMellinContinuation w a G Ω) {z : ℂ} (hz : z ∈ Ω) (hz1 : z.re < 1) :
    (1 - (2 : ℂ) ^ (-z)) * G z * zetaEntire (1 - z) =
      -((2 : ℂ) ^ (-z)) * z * (1 - z) * correlationMellin w (1 - z) := by
  have ha1 := hw.lt_one
  set U : Set ℂ := Ω ∩ {u : ℂ | u.re < 1} with hU
  have hUo : IsOpen U := h.isOpen.inter (isOpen_lt Complex.continuous_re continuous_const)
  have hUc : IsPreconnected U := h.isPreconnected_inter ha1
  have hsub : ∀ u : ℂ, DifferentiableAt ℂ (fun v : ℂ => (1 : ℂ) - v) u :=
    fun u => (differentiableAt_const _).sub differentiableAt_id
  have hF₁ : AnalyticOnNhd ℂ (fun u : ℂ => (1 - (2 : ℂ) ^ (-u)) * G u * zetaEntire (1 - u)) U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu => ?_) hUo
    have hG : DifferentiableAt ℂ G u := h.diff.differentiableAt (h.isOpen.mem_nhds hu.1)
    exact ((((differentiableAt_const _).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl two_ne_zero))).mul hG).mul
      ((differentiable_zetaEntire _).comp u (hsub u))).differentiableWithinAt
  have hF₂ : AnalyticOnNhd ℂ
      (fun u : ℂ => -((2 : ℂ) ^ (-u)) * u * (1 - u) * correlationMellin w (1 - u)) U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu => ?_) hUo
    have hu1 : u.re < 1 := hu.2
    have hs0 : 0 < (1 - u).re := by simp; linarith
    have hΦ : DifferentiableAt ℂ (fun v : ℂ => correlationMellin w (1 - v)) u :=
      (hw.differentiableAt_correlationMellin hs0).comp u (hsub u)
    exact (((((differentiableAt_id.neg).const_cpow (Or.inl two_ne_zero)).neg.mul
      differentiableAt_id).mul (hsub u)).mul hΦ).differentiableWithinAt
  have hz₀ : (((a + 1) / 2 : ℝ) : ℂ) ∈ U :=
    ⟨h.strip _ (by simp; linarith), by simp; linarith⟩
  have hev : (fun u : ℂ => (1 - (2 : ℂ) ^ (-u)) * G u * zetaEntire (1 - u)) =ᶠ[𝓝 (((a + 1) / 2 : ℝ) : ℂ)]
      fun u : ℂ => -((2 : ℂ) ^ (-u)) * u * (1 - u) * correlationMellin w (1 - u) := by
    have hopen : IsOpen {u : ℂ | a < u.re ∧ u.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds ⟨by simp; linarith, by simp; linarith⟩] with u hu
    rw [h.eq u hu.1]
    exact hw.strip_product hu.1 hu.2
  exact hF₁.eqOn_of_preconnected_of_eventuallyEq hF₂ hUc hz₀ hev ⟨hz, hz1⟩

/-! ## The glued defect -/

open scoped Classical in
/-- The dyadic defect glued from the continued right form `(1 − 2^{−z}) G(z)` on `Ω` and the left
form off `Ω`. -/
def continuedDefect (w : ℝ → ℂ) (G : ℂ → ℂ) (Ω : Set ℂ) : ℂ → ℂ :=
  Ω.piecewise (fun z => (1 - (2 : ℂ) ^ (-z)) * G z) (dyadicDefectLeft w)

/-- The transform `2^z (V(z) − ∫_{1/2}^1 t^{z−1} w)` of the glued defect. -/
def continuedDefectTransform (w : ℝ → ℂ) (G : ℂ → ℂ) (Ω : Set ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ) ^ z * (continuedDefect w G Ω z - upperWitnessMellin w z)

theorem continuedDefect_of_mem {z : ℂ} (hz : z ∈ Ω) :
    continuedDefect w G Ω z = (1 - (2 : ℂ) ^ (-z)) * G z := by
  simp [continuedDefect, Set.piecewise, hz]

theorem continuedDefect_of_notMem {z : ℂ} (hz : z ∉ Ω) :
    continuedDefect w G Ω z = dyadicDefectLeft w z := by
  simp [continuedDefect, Set.piecewise, hz]

/-- On `Ω ∩ {Re z < 1}` away from the zeros of `Ξ(1 − z)` the glued defect is the left form. -/
theorem IsMellinContinuation.continuedDefect_eq_left (hw : IsMellinFermiWitness w a)
    (h : IsMellinContinuation w a G Ω) {z : ℂ} (hz : z ∈ Ω) (hz1 : z.re < 1)
    (hΞ : zetaEntire (1 - z) ≠ 0) : continuedDefect w G Ω z = dyadicDefectLeft w z := by
  rw [continuedDefect_of_mem hz, dyadicDefectLeft, eq_div_iff hΞ]
  exact h.product_identity hw hz hz1

/-- **The glued defect is entire** when `Ω` contains every pole `1 − ρ`, `Ξ(ρ) = 0`. -/
theorem IsMellinContinuation.differentiable_continuedDefect (hw : IsMellinFermiWitness w a)
    (h : IsMellinContinuation w a G Ω) (hpole : ∀ z : ℂ, zetaEntire (1 - z) = 0 → z ∈ Ω) :
    Differentiable ℂ (continuedDefect w G Ω) := by
  intro z
  by_cases hz : z ∈ Ω
  · have hev : continuedDefect w G Ω =ᶠ[𝓝 z] fun u => (1 - (2 : ℂ) ^ (-u)) * G u := by
      filter_upwards [h.isOpen.mem_nhds hz] with u hu
      exact continuedDefect_of_mem hu
    have hG : DifferentiableAt ℂ G z := h.diff.differentiableAt (h.isOpen.mem_nhds hz)
    exact (((differentiableAt_const _).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl two_ne_zero))).mul hG).congr_of_eventuallyEq hev
  · have hΞ : zetaEntire (1 - z) ≠ 0 := fun h0 => hz (hpole z h0)
    have hz1 : z.re < 1 := by
      by_contra hc
      exact hz (h.strip z (by linarith [hw.lt_one, not_lt.1 hc]))
    have hopen : IsOpen {u : ℂ | zetaEntire (1 - u) ≠ 0 ∧ u.re < 1} := by
      refine IsOpen.inter ?_ (isOpen_lt Complex.continuous_re continuous_const)
      exact isOpen_ne_fun (differentiable_zetaEntire.continuous.comp
        (continuous_const.sub continuous_id)) continuous_const
    have hev : continuedDefect w G Ω =ᶠ[𝓝 z] dyadicDefectLeft w := by
      filter_upwards [hopen.mem_nhds ⟨hΞ, hz1⟩] with u hu
      by_cases huΩ : u ∈ Ω
      · exact h.continuedDefect_eq_left hw huΩ hu.2 hu.1
      · exact continuedDefect_of_notMem huΩ
    have hs0 : 0 < (1 - z).re := by simp; linarith
    exact (hw.differentiableAt_dyadicDefectLeft hs0 hΞ).congr_of_eventuallyEq hev

theorem IsMellinContinuation.differentiable_continuedDefectTransform
    (hw : IsMellinFermiWitness w a) (h : IsMellinContinuation w a G Ω)
    (hpole : ∀ z : ℂ, zetaEntire (1 - z) = 0 → z ∈ Ω) :
    Differentiable ℂ (continuedDefectTransform w G Ω) := fun z =>
  (differentiableAt_id.const_cpow (Or.inl two_ne_zero)).mul
    ((h.differentiable_continuedDefect hw hpole z).sub (hw.differentiable_upperWitnessMellin z))

/-! ## Comparison with the exponent-`a` transform -/

/-- On `Re z > a` the glued transform is the exponent-`a` transform `U`. -/
theorem IsMellinContinuation.continuedDefectTransform_eq_of_lt (h : IsMellinContinuation w a G Ω)
    {z : ℂ} (hz : a < z.re) :
    continuedDefectTransform w G Ω z = dyadicDefectTransform w a z := by
  unfold continuedDefectTransform dyadicDefectTransform dyadicDefect
  rw [if_pos hz, continuedDefect_of_mem (h.strip z hz), h.eq z hz]
  rfl

/-- Wherever `z ≠ 0` and `ζ(1 − z) ≠ 0` the glued transform is the exponent-`a` transform `U`. -/
theorem IsMellinContinuation.continuedDefectTransform_eq_of_ne (hw : IsMellinFermiWitness w a)
    (h : IsMellinContinuation w a G Ω) {z : ℂ} (hz0 : z ≠ 0) (hζ : riemannZeta (1 - z) ≠ 0) :
    continuedDefectTransform w G Ω z = dyadicDefectTransform w a z := by
  rcases lt_or_ge a z.re with hz | hz
  · exact h.continuedDefectTransform_eq_of_lt hz
  · have hne1 : (1 : ℂ) - z ≠ 1 := by intro h'; apply hz0; linear_combination -h'
    have hΞ : zetaEntire (1 - z) ≠ 0 := by
      rw [zetaEntire_eq hne1]; exact mul_ne_zero (sub_ne_zero.2 hne1) hζ
    have hz1 : z.re < 1 := lt_of_le_of_lt hz hw.lt_one
    unfold continuedDefectTransform dyadicDefectTransform dyadicDefect
    rw [if_neg (not_lt.2 hz)]
    congr 2
    by_cases hzΩ : z ∈ Ω
    · exact h.continuedDefect_eq_left hw hzΩ hz1 hΞ
    · exact continuedDefect_of_notMem hzΩ

/-- **Polynomial growth of the glued transform.** -/
theorem IsMellinContinuation.exists_growth (hw : IsMellinFermiWitness w a)
    (h : IsMellinContinuation w a G Ω) (hpole : ∀ z : ℂ, zetaEntire (1 - z) = 0 → z ∈ Ω) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ z : ℂ, ‖continuedDefectTransform w G Ω z‖ ≤ K * (1 + ‖z‖) ^ N := by
  have ha0 := hw.nonneg
  have ha1 := hw.lt_one
  have hm := witnessMajorant_nonneg w 1
  refine exists_polyGrowth_of_zetaInv_bounds (h.differentiable_continuedDefectTransform hw hpole)
    (x₁ := (a + 1) / 2) (KR := rightDefectBound w ((a + 1) / 2)) (KL := upperDefectBound w)
    (c := 6 * witnessMajorant w 1 / (1 - a)) (by linarith) (by linarith)
    (rightDefectBound_nonneg w _) (upperDefectBound_nonneg w)
    (div_nonneg (by linarith) (by linarith)) (fun z hz => ?_) (fun z hz hz0 hζ => ?_)
  · rw [h.continuedDefectTransform_eq_of_lt (by linarith)]
    exact hw.norm_dyadicDefectTransform_le_right (by linarith) (by linarith) hz
  · rw [h.continuedDefectTransform_eq_of_ne hw hz0 hζ]
    have hz1 : z.re < 1 := by linarith
    have hb := hw.norm_dyadicDefectTransform_le_left hz1 hz0 (fun _ => hζ)
    have h3 : 3 * witnessMajorant w 1 / (1 - z.re) ≤ 6 * witnessMajorant w 1 / (1 - a) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [mul_nonneg hm (show (0 : ℝ) ≤ 1 + a - 2 * z.re by linarith)]
    rw [one_div, ← norm_inv] at hb
    refine hb.trans (add_le_add ?_ le_rfl)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) (norm_nonneg _)

/-- **The glued transform vanishes identically.** -/
theorem IsMellinContinuation.continuedDefectTransform_eq_zero (hw : IsMellinFermiWitness w a)
    (h : IsMellinContinuation w a G Ω) (hpole : ∀ z : ℂ, zetaEntire (1 - z) = 0 → z ∈ Ω) (z : ℂ) :
    continuedDefectTransform w G Ω z = 0 := by
  refine eq_zero_of_polyGrowth_of_tendsto_nat (h.differentiable_continuedDefectTransform hw hpole)
    (h.exists_growth hw hpole) ?_ z
  refine hw.tendsto_dyadicDefectTransform_nat.congr (fun n => ?_)
  refine (h.continuedDefectTransform_eq_of_lt ?_).symm
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  simp; linarith [hw.lt_one]

/-! ## Self-similarity -/

/-- **Mellin-continuation rigidity.**  A witness of Mellin exponent `a < 1` whose Mellin transform
continues analytically to an open right-closed set `Ω ⊇ {Re z > a}` containing every pole `1 − ρ`
(`Ξ(ρ) = 0`) is dyadically self-similar: `w(t/2) = w(t)` on `(0,1]`. -/
theorem IsMellinContinuation.selfSimilar (hw : IsMellinFermiWitness w a)
    (h : IsMellinContinuation w a G Ω) (hpole : ∀ z : ℂ, zetaEntire (1 - z) = 0 → z ∈ Ω)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t := by
  refine selfSimilar_of_mellin_lowerDefect hw.cont hw.integrable_lowerDefect (fun z hz => ?_) ht
  have hz' : a < z.re := by rw [hz]; exact hw.lt_one
  have h0 := h.continuedDefectTransform_eq_zero hw hpole z
  rw [h.continuedDefectTransform_eq_of_lt hz', hw.dyadicDefectTransform_eq_of_lt_re hz'] at h0
  have h2 : (2 : ℂ) ^ z ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]; exact Complex.exp_ne_zero _
  unfold lowerDefect
  rw [mellin_indicator_eq_setIntegral le_rfl]
  exact (mul_eq_zero.1 h0).resolve_left h2

/-! ## Instance: continuation to the right half-plane -/

/-- **Continuation to `Re z > 0` forces self-similarity.**  No zero of `Ξ` has real part `≥ 1`, so
every pole `1 − ρ` lies in the right half-plane. -/
theorem IsMellinFermiWitness.selfSimilar_of_continuation_halfPlane (hw : IsMellinFermiWitness w a)
    (hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.re})
    (hGW : ∀ z : ℂ, a < z.re → G z = witnessMellin w z) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    w (t / 2) = w t := by
  have h : IsMellinContinuation w a G {z : ℂ | 0 < z.re} :=
    { isOpen := isOpen_lt continuous_const Complex.continuous_re
      right := fun z hz x hx => show (0 : ℝ) < x from lt_of_lt_of_le hz hx
      strip := fun z hz => show (0 : ℝ) < z.re by linarith [hw.nonneg]
      diff := hG
      eq := hGW }
  refine h.selfSimilar hw (fun z hz => ?_) ht
  show (0 : ℝ) < z.re
  by_contra hc
  exact zetaEntire_ne_zero_of_re_le_zero (not_lt.1 hc) hz

/-! ## Instance: continuation to the known zero-free region -/

/-- The width profile `1/(59 log max(|y|, 2))` of the zero-free region. -/
def zeroFreeWidth (y : ℝ) : ℝ := 1 / (59 * Real.log (max |y| 2))

theorem log_max_abs_two_pos (y : ℝ) : 0 < Real.log (max |y| 2) :=
  Real.log_pos (lt_of_lt_of_le one_lt_two (le_max_right _ _))

theorem continuous_zeroFreeWidth : Continuous zeroFreeWidth := by
  have hmax : Continuous fun y : ℝ => max |y| 2 := continuous_abs.max continuous_const
  have hlog : Continuous fun y : ℝ => Real.log (max |y| 2) :=
    Real.continuousOn_log.comp_continuous hmax (fun y =>
      Set.mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le two_pos (le_max_right _ _))))
  exact continuous_const.div (continuous_const.mul hlog)
    (fun y => mul_ne_zero (by norm_num) (log_max_abs_two_pos y).ne')

/-- The region `{Re z > a} ∪ {Re z > 0, |Im z| < 4} ∪ {Re z > 1/(59 log max(|Im z|, 2))}`: it
contains every pole `1 − ρ`, `Ξ(ρ) = 0`, by the zero-free region of width `1/(58 log |Im ρ|)`
valid from `|Im ρ| ≥ 4`. -/
def zeroFreeContinuationRegion (a : ℝ) : Set ℂ :=
  {z | a < z.re} ∪ {z | 0 < z.re ∧ |z.im| < 4} ∪ {z | zeroFreeWidth z.im < z.re}

theorem isOpen_zeroFreeContinuationRegion (a : ℝ) : IsOpen (zeroFreeContinuationRegion a) :=
  ((isOpen_lt continuous_const Complex.continuous_re).union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))).union
    (isOpen_lt (continuous_zeroFreeWidth.comp Complex.continuous_im) Complex.continuous_re)

theorem zeroFreeContinuationRegion_right (a : ℝ) {z : ℂ} (hz : z ∈ zeroFreeContinuationRegion a)
    {x : ℝ} (hx : z.re ≤ x) : (⟨x, z.im⟩ : ℂ) ∈ zeroFreeContinuationRegion a := by
  rcases hz with (hz | hz) | hz
  · exact Or.inl (Or.inl (show a < x from lt_of_lt_of_le hz hx))
  · exact Or.inl (Or.inr ⟨show (0 : ℝ) < x from lt_of_lt_of_le hz.1 hx, hz.2⟩)
  · exact Or.inr (show zeroFreeWidth z.im < x from lt_of_lt_of_le hz hx)

/-- Every pole `1 − ρ` of the left form lies in the region. -/
theorem mem_zeroFreeContinuationRegion_of_zetaEntire_eq_zero (a : ℝ) {z : ℂ}
    (hz : zetaEntire (1 - z) = 0) : z ∈ zeroFreeContinuationRegion a := by
  have hre : (1 - z).re < 1 := by
    by_contra hc; exact Sieve.zetaEntire_ne_zero_of_one_le_re (not_lt.1 hc) hz
  have hre' : (1 - z).re = 1 - z.re := by simp
  rw [hre'] at hre
  have hz0 : 0 < z.re := by linarith
  rcases lt_or_ge |z.im| 4 with h4 | h4
  · exact Or.inl (Or.inr ⟨hz0, h4⟩)
  · right
    show zeroFreeWidth z.im < z.re
    have hne1 : (1 : ℂ) - z ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this; linarith
    have hζ : riemannZeta (1 - z) = 0 := by
      rw [zetaEntire_eq hne1] at hz
      exact (mul_eq_zero.1 hz).resolve_left (sub_ne_zero.2 hne1)
    have him : |(1 - z).im| = |z.im| := by simp
    have hγ : 4 ≤ |(1 - z).im| := by rw [him]; exact h4
    have hβ := re_le_one_sub_of_riemannZeta_eq_zero hγ
      (by rw [Complex.re_add_im]; exact hζ)
    rw [him, hre'] at hβ
    have hL : 0 < Real.log |z.im| := Real.log_pos (by linarith)
    have hmax : max |z.im| 2 = |z.im| := max_eq_left (by linarith)
    unfold zeroFreeWidth
    rw [hmax]
    calc 1 / (59 * Real.log |z.im|) < 1 / (58 * Real.log |z.im|) :=
          one_div_lt_one_div_of_lt (by positivity) (by linarith)
      _ = 1 / 58 / Real.log |z.im| := by rw [div_div]
      _ ≤ z.re := by linarith

/-- **Continuation to the known zero-free region forces self-similarity.**  A witness of Mellin
exponent `a < 1` whose Mellin transform continues analytically to
`{Re z > a} ∪ {Re z > 0, |Im z| < 4} ∪ {Re z > 1/(59 log max(|Im z|, 2))}` is dyadically
self-similar. -/
theorem IsMellinFermiWitness.selfSimilar_of_continuation_zeroFreeRegion
    (hw : IsMellinFermiWitness w a) (hG : DifferentiableOn ℂ G (zeroFreeContinuationRegion a))
    (hGW : ∀ z : ℂ, a < z.re → G z = witnessMellin w z) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    w (t / 2) = w t := by
  have h : IsMellinContinuation w a G (zeroFreeContinuationRegion a) :=
    { isOpen := isOpen_zeroFreeContinuationRegion a
      right := fun z hz x hx => zeroFreeContinuationRegion_right a hz hx
      strip := fun z hz => Or.inl (Or.inl hz)
      diff := hG
      eq := hGW }
  exact h.selfSimilar hw (fun z hz => mem_zeroFreeContinuationRegion_of_zetaEntire_eq_zero a hz) ht

/-- **Square-integrable witnesses.**  A continuous square-integrable witness whose Mellin transform
(exponent `½`) continues analytically to the zero-free continuation region at `a = ½` is dyadically
self-similar. -/
theorem selfSimilar_of_sq_continuation_zeroFreeRegion (hc : ContinuousOn w (Ioc 0 1))
    (hsq : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1))
    (ho : ∀ b : ℝ, 1 ≤ b → ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen b t * w t = 0)
    (hG : DifferentiableOn ℂ G (zeroFreeContinuationRegion (1 / 2)))
    (hGW : ∀ z : ℂ, 1 / 2 < z.re → G z = witnessMellin w z) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    w (t / 2) = w t :=
  (isMellinFermiWitness_half_of_sq hc hsq ho).selfSimilar_of_continuation_zeroFreeRegion hG hGW ht

/-! ## Instance: continuation to the Vinogradov–Korobov region -/

theorem continuousOn_vkHadamardWidth :
    ContinuousOn vkHadamardWidth (Ici (Real.exp (Real.exp 1))) := by
  have hL : ∀ T ∈ Ici (Real.exp (Real.exp 1)), Real.exp 1 ≤ Real.log T := fun T hT => by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hT
  have hlog : ContinuousOn (fun T : ℝ => Real.log T) (Ici (Real.exp (Real.exp 1))) :=
    Real.continuousOn_log.mono (fun T hT =>
      Set.mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) hT)))
  have hloglog : ContinuousOn (fun T : ℝ => Real.log (Real.log T)) (Ici (Real.exp (Real.exp 1))) :=
    Real.continuousOn_log.comp hlog (fun T hT =>
      Set.mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le (Real.exp_pos 1) (hL T hT))))
  have h1 : ContinuousOn (fun T : ℝ => Real.log T ^ (-(2 : ℝ) / 3)) (Ici (Real.exp (Real.exp 1))) :=
    hlog.rpow_const (fun T hT => Or.inl (ne_of_gt (lt_of_lt_of_le (Real.exp_pos 1) (hL T hT))))
  have h2 : ContinuousOn (fun T : ℝ => Real.log (Real.log T) ^ (-(5 : ℝ) / 3))
      (Ici (Real.exp (Real.exp 1))) := by
    refine hloglog.rpow_const (fun T hT => Or.inl (ne_of_gt ?_))
    have : 1 ≤ Real.log (Real.log T) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos _) (hL T hT)
    linarith
  exact (h1.mul h2).div_const _

/-- The Vinogradov–Korobov continuation region above the threshold `γ₁`:
`{Re z > a} ∪ {Re z > 0, |Im z| < γ₁ + 1} ∪ {Re z > w(max(|Im z|, γ₁))/2}` with
`w(T) = (log T)^{-2/3}(log log T)^{-5/3}/10⁸`. -/
def vkContinuationRegion (a γ₁ : ℝ) : Set ℂ :=
  {z | a < z.re} ∪ {z | 0 < z.re ∧ |z.im| < γ₁ + 1} ∪
    {z | vkHadamardWidth (max |z.im| γ₁) / 2 < z.re}

theorem continuous_vkRegionWidth {γ₁ : ℝ} (hγ₁ : Real.exp (Real.exp 1) ≤ γ₁) :
    Continuous fun z : ℂ => vkHadamardWidth (max |z.im| γ₁) / 2 := by
  have hmax : Continuous fun z : ℂ => max |z.im| γ₁ :=
    (continuous_abs.comp Complex.continuous_im).max continuous_const
  exact (continuousOn_vkHadamardWidth.comp_continuous hmax
    (fun z => mem_Ici.2 (le_trans hγ₁ (le_max_right _ _)))).div_const 2

theorem isOpen_vkContinuationRegion (a : ℝ) {γ₁ : ℝ} (hγ₁ : Real.exp (Real.exp 1) ≤ γ₁) :
    IsOpen (vkContinuationRegion a γ₁) :=
  ((isOpen_lt continuous_const Complex.continuous_re).union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))).union
    (isOpen_lt (continuous_vkRegionWidth hγ₁) Complex.continuous_re)

theorem vkContinuationRegion_right (a γ₁ : ℝ) {z : ℂ} (hz : z ∈ vkContinuationRegion a γ₁)
    {x : ℝ} (hx : z.re ≤ x) : (⟨x, z.im⟩ : ℂ) ∈ vkContinuationRegion a γ₁ := by
  rcases hz with (hz | hz) | hz
  · exact Or.inl (Or.inl (show a < x from lt_of_lt_of_le hz hx))
  · exact Or.inl (Or.inr ⟨show (0 : ℝ) < x from lt_of_lt_of_le hz.1 hx, hz.2⟩)
  · exact Or.inr (show vkHadamardWidth (max |z.im| γ₁) / 2 < x from lt_of_lt_of_le hz hx)

/-- **Continuation to the Vinogradov–Korobov region forces self-similarity.**  There is a height
`γ₁ ≥ e^e` such that every witness of Mellin exponent `a < 1` whose Mellin transform continues
analytically to `vkContinuationRegion a γ₁` is dyadically self-similar. -/
theorem exists_vk_selfSimilar_of_continuation :
    ∃ γ₁ : ℝ, Real.exp (Real.exp 1) ≤ γ₁ ∧
      ∀ (w : ℝ → ℂ) (a : ℝ) (G : ℂ → ℂ), IsMellinFermiWitness w a →
        DifferentiableOn ℂ G (vkContinuationRegion a γ₁) →
        (∀ z : ℂ, a < z.re → G z = witnessMellin w z) →
        ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t := by
  obtain ⟨γ₁, hγ₁, hvk⟩ := abs_re_sub_half_le_vinogradovKorobov
  refine ⟨γ₁, hγ₁, fun w a G hw hG hGW t ht => ?_⟩
  have h : IsMellinContinuation w a G (vkContinuationRegion a γ₁) :=
    { isOpen := isOpen_vkContinuationRegion a hγ₁
      right := fun z hz x hx => vkContinuationRegion_right a γ₁ hz hx
      strip := fun z hz => Or.inl (Or.inl hz)
      diff := hG
      eq := hGW }
  refine h.selfSimilar hw (fun z hz => ?_) ht
  rcases lt_or_ge a z.re with hza | hza
  · exact Or.inl (Or.inl hza)
  have hre : (1 - z).re < 1 := by
    by_contra hc; exact Sieve.zetaEntire_ne_zero_of_one_le_re (not_lt.1 hc) hz
  have hre' : (1 - z).re = 1 - z.re := by simp
  rw [hre'] at hre
  have hz0 : 0 < z.re := by linarith
  rcases lt_or_ge |z.im| (γ₁ + 1) with hsm | hsm
  · exact Or.inl (Or.inr ⟨hz0, hsm⟩)
  right
  show vkHadamardWidth (max |z.im| γ₁) / 2 < z.re
  have hne1 : (1 : ℂ) - z ≠ 1 := by
    intro h'
    have := congrArg Complex.re h'
    simp at this; linarith
  have hζ : riemannZeta (1 - z) = 0 := by
    rw [zetaEntire_eq hne1] at hz
    exact (mul_eq_zero.1 hz).resolve_left (sub_ne_zero.2 hne1)
  have him : |(1 - z).im| = |z.im| := by simp
  have hρ0 : 0 < (1 - z).re := by rw [hre']; linarith [hw.lt_one]
  have hρ1 : (1 - z).re < 1 := by rw [hre']; exact hre
  have hγ : γ₁ ≤ |(1 - z).im| := by rw [him]; linarith
  have hd := hvk (1 - z) hρ0 hρ1 hζ hγ
  rw [him, hre'] at hd
  have hmax : max |z.im| γ₁ = |z.im| := max_eq_left (by linarith)
  have hw0 : 0 < vkHadamardWidth |z.im| := vkHadamardWidth_pos (le_trans hγ₁ (by linarith))
  rw [hmax]
  have := (abs_le.1 hd).2
  linarith

end RHTower
