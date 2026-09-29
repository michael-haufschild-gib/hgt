import GaloisForLFunctions.RHTower.DeckScatteringUnitarity

/-!
# Reflection of the deck Eisenstein series and bounds for the scattering operator

For `Re s > 1` the rows have real heights, so `Ẽ(z, s̄; v̄) = conj Ẽ(z, s; v)`; by the identity theorem
and continuity the continued series satisfies the same reflection on `{Re ≥ 1/2} \ {1/2, 1}`, and so
does its truncation.  Consequently the Maass–Selberg relation at the pair `(s, s̄)` pairs `Λ^Y Ẽ(s; v)`
with its own conjugate:

`(s − s̄)(s + s̄ − 1) ∫_𝒟 ‖Λ^1 Ẽ(s; v)‖² = R(s, s̄)`.

Taking imaginary parts with `s = σ + it`:
`t (2σ−1) ‖Λ^1Ẽ‖² = t (‖v‖² − ‖Φ̃(s)v‖²) + (2σ−1) Im⟪Φ̃(s)v, v⟫`, whence
`‖Φ̃(s)v‖² ≤ ‖v‖² + (2σ−1) ‖Φ̃(s)v‖ ‖v‖ / |t|`, and `‖Φ̃(s)v‖ ≤ 4‖v‖` for `σ ≤ 2`, `|t| ≥ 1`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Metric EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry SelbergEisensteinStarCriticalLine

noncomputable section

variable {N : ℕ}

/-! ## Reflection of the series -/

theorem conj_eisVec_apply {s : ℂ} (hs : 1 < s.re) (v : DeckSpace N) (z : ℍ) (q : Deck N) :
    conj (eisVec s v z q) = eisVec (conj s) (deckConjVec v) z q := by
  have hs' : 1 < (conj s).re := by simpa using hs
  rw [eisVec_apply hs, eisVec_apply hs', map_mul, Complex.conj_tsum]
  congr 1
  · rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
  · refine tsum_congr fun p => ?_
    rw [map_mul, conj_ofReal_nonneg_cpow (RHTower.rowHeight_pos p z).le, deckConjVec_apply]

theorem eisVec_conj {s : ℂ} (hs : 1 < s.re) (v : DeckSpace N) (z : ℍ) :
    eisVec (conj s) (deckConjVec v) z = deckConjVec (eisVec s v z) := by
  ext q
  rw [deckConjVec_apply, conj_eisVec_apply hs]

/-- **Reflection of the continued series** on `{Re ≥ 1/2} \ {1/2, 1}`. -/
theorem eisExt_conj (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) (z : ℍ) {s : ℂ}
    (hs : s ∈ closedHalfDom) : eisExt (conj s) (deckConjVec v) z = deckConjVec (eisExt s v z) := by
  have hvc := isCuspVec_deckConjVec hv
  ext q
  rw [deckConjVec_apply]
  have hd : ∀ s ∈ closedHalfDom, DifferentiableAt ℂ (fun s => eisExt s v z q) s := fun s hs =>
    differentiableAt_eisExt_apply v z q (closedHalfDom_subset (N := N) hs).1 hs.2.2
  have hd' : ∀ s ∈ closedHalfDom, DifferentiableAt ℂ (fun s => eisExt s (deckConjVec v) z q) s :=
    fun s hs => differentiableAt_eisExt_apply _ z q (closedHalfDom_subset (N := N) hs).1 hs.2.2
  have hsub : halfPlaneDom ⊆ closedHalfDom := fun s hs =>
    ⟨hs.1.le, fun h => by rw [h] at hs; norm_num at hs, hs.2⟩
  -- the two holomorphic functions agree on the half-plane
  have hEq : EqOn (fun s => conj (eisExt (conj s) (deckConjVec v) z q)) (fun s => eisExt s v z q)
      halfPlaneDom := by
    have hopen := SelbergEisensteinCuspExpansion.isOpen_punctured
    have hconn := SelbergEisensteinCuspExpansion.isPreconnected_punctured
    have hf : AnalyticOnNhd ℂ (fun s => conj (eisExt (conj s) (deckConjVec v) z q)) halfPlaneDom := by
      refine analyticOnNhd_of_differentiableAt hopen fun s hs => ?_
      have h := (hd' (conj s) (hsub (conj_mem_halfPlaneDom hs))).conj_conj
      simpa [Function.comp_def] using h
    have hg : AnalyticOnNhd ℂ (fun s => eisExt s v z q) halfPlaneDom :=
      analyticOnNhd_of_differentiableAt hopen fun s hs => hd s (hsub hs)
    have h2 : (2 : ℂ) ∈ halfPlaneDom := ⟨by norm_num, by norm_num⟩
    have hev : (fun s => conj (eisExt (conj s) (deckConjVec v) z q)) =ᶠ[𝓝 (2 : ℂ)]
        fun s => eisExt s v z q := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs'
      have hs1 : 1 < (conj s).re := by simpa using hs'
      rw [← eisVec_eq_eisExt hN hs1 hvc, ← eisVec_eq_eisExt hN hs' hv, ← conj_eisVec_apply hs',
        Complex.conj_conj]
    exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 hev
  have key : conj (eisExt (conj s) (deckConjVec v) z q) = eisExt s v z q :=
    eq_of_eqOn_halfPlaneDom (f := fun s => conj (eisExt (conj s) (deckConjVec v) z q))
      (g := fun s => eisExt s v z q) hs
      (Complex.continuous_conj.continuousAt.comp
        ((hd' (conj s) (conj_mem_closedHalfDom hs)).continuousAt.comp Complex.continuous_conj.continuousAt))
      (hd s hs).continuousAt hEq
  rw [← key, Complex.conj_conj]

theorem eisCT_conj {s : ℂ} (hs : s ∈ closedHalfDom) (v : DeckSpace N) {y : ℝ} (hy : 0 < y) :
    eisCT (conj s) (deckConjVec v) y = deckConjVec (eisCT s v y) := by
  unfold eisCT
  rw [← deckConjVec_scatVec hs]
  ext q
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, deckConjVec_apply, map_add, map_mul]
  rw [conj_ofReal_nonneg_cpow hy.le, conj_ofReal_nonneg_cpow hy.le, map_sub, map_one]

theorem eisTrunc_conj (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) {s : ℂ} (hs : s ∈ closedHalfDom)
    (Y : ℝ) (z : ℍ) : eisTrunc Y (conj s) (deckConjVec v) z = deckConjVec (eisTrunc Y s v z) := by
  rw [eisTrunc_def, eisTrunc_def, eisExt_conj hN hv z hs]
  split_ifs
  · rw [eisCT_conj hs v z.im_pos]
    ext q; simp [deckConjVec_apply]
  · ext q; simp [deckConjVec_apply]

/-! ## Positivity -/

theorem bil_self_conj (X : DeckSpace N) : bil X (deckConjVec X) = ((‖X‖ ^ 2 : ℝ) : ℂ) := by
  rw [bil_comm, bil_eq_inner, deckConjVec_deckConjVec, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem truncPairing_conj (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) {s : ℂ}
    (hs : s ∈ closedHalfDom) (Y : ℝ) :
    truncPairing Y s v (conj s) (deckConjVec v) = ((∫ z in fd, ‖eisTrunc Y s v z‖ ^ 2 : ℝ) : ℂ) := by
  unfold truncPairing
  simp_rw [eisTrunc_conj hN hv hs, bil_self_conj]
  exact integral_complex_ofReal

/-- **The Maass–Selberg inequality for the scattering operator**: for `s = σ + it`, `σ > 1/2`,
`t ≠ 0`: `‖Φ̃(s)v‖² ≤ ‖v‖² + (2σ−1) ‖Φ̃(s)v‖ ‖v‖ / |t|`. -/
theorem norm_scatVec_sq_le (hN : 2 ≤ N) {s : ℂ} (hs : s ∈ halfPlaneDom) (ht : s.im ≠ 0)
    {v : DeckSpace N} (hv : IsCuspVec v) :
    ‖scatVec s v‖ ^ 2 ≤ ‖v‖ ^ 2 + (2 * s.re - 1) * ‖scatVec s v‖ * ‖v‖ / |s.im| := by
  have hsc : s ∈ closedHalfDom :=
    ⟨hs.1.le, fun h => by have := hs.1; rw [h] at this; norm_num at this, hs.2⟩
  have hvc := isCuspVec_deckConjVec hv
  have hms := msDefect_eq_zero hN hs (conj_mem_halfPlaneDom hs) hv hvc (le_refl 1)
  unfold msDefect msCleared at hms
  rw [truncPairing_conj hN hv hsc] at hms
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at hms
  rw [← deckConjVec_scatVec hsc, bil_self_conj, bil_self_conj] at hms
  set P : ℝ := ∫ z in fd, ‖eisTrunc 1 s v z‖ ^ 2
  have hP : 0 ≤ P := integral_nonneg fun z => by positivity
  set a : ℂ := bil v (deckConjVec (scatVec s v))
  have ha : bil (scatVec s v) (deckConjVec v) = conj a := by
    simp only [a, bil, deckConjVec_apply, map_sum, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [ha] at hms
  have e1 : s - conj s = ((2 * s.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp; ring
  have e2 : s + conj s - 1 = ((2 * s.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp; ring
  have e3 : a - conj a = ((2 * a.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp; ring
  rw [e1, e2, e3] at hms
  have key : ((2 * s.im * (2 * s.re - 1) * P - 2 * s.im * (‖v‖ ^ 2 - ‖scatVec s v‖ ^ 2) -
      (2 * s.re - 1) * (2 * a.im) : ℝ) : ℂ) * Complex.I = 0 := by
    rw [← hms]; push_cast; ring
  have hreal : 2 * s.im * (2 * s.re - 1) * P - 2 * s.im * (‖v‖ ^ 2 - ‖scatVec s v‖ ^ 2) -
      (2 * s.re - 1) * (2 * a.im) = 0 := by
    exact_mod_cast (mul_eq_zero.1 key).resolve_right Complex.I_ne_zero
  have hIm : |a.im| ≤ ‖scatVec s v‖ * ‖v‖ := by
    refine (Complex.abs_im_le_norm a).trans ?_
    simp only [a]
    refine (norm_bil_le _ _).trans (le_of_eq ?_)
    rw [norm_deckConjVec, mul_comm]
  have hσ : 0 < 2 * s.re - 1 := by linarith [hs.1]
  have ht' : 0 < |s.im| := abs_pos.2 ht
  rw [← sub_le_iff_le_add', le_div_iff₀ ht']
  have hσP := mul_nonneg hσ.le hP
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [abs_of_neg hneg]
    nlinarith [abs_le.1 hIm, mul_nonneg hσP (neg_nonneg.2 hneg.le)]
  · rw [abs_of_pos hpos]
    nlinarith [abs_le.1 hIm, mul_nonneg hσP hpos.le]

/-- **Uniform bound of the scattering operator** away from the real axis:
`‖Φ̃(s)v‖ ≤ 4‖v‖` for `1/2 < Re s ≤ 2`, `|Im s| ≥ 1`. -/
theorem norm_scatVec_le_four (hN : 2 ≤ N) {s : ℂ} (hs : 1 / 2 < s.re) (hs2 : s.re ≤ 2)
    (ht : 1 ≤ |s.im|) {v : DeckSpace N} (hv : IsCuspVec v) : ‖scatVec s v‖ ≤ 4 * ‖v‖ := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at ht; norm_num at ht
  have him : s.im ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  have h := norm_scatVec_sq_le hN ⟨hs, hs1⟩ him hv
  set x := ‖scatVec s v‖
  set y := ‖v‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hq : (2 * s.re - 1) * x * y / |s.im| ≤ 3 * x * y := by
    rw [div_le_iff₀ (by linarith)]
    have h3 : 2 * s.re - 1 ≤ 3 := by linarith
    have hxy : 0 ≤ x * y := mul_nonneg hx hy
    nlinarith [mul_le_mul_of_nonneg_right h3 hxy, mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num :
      (0 : ℝ) ≤ 3) hxy)]
  by_contra hc
  push Not at hc
  nlinarith

end

end GaloisForLFunctions.RHTower.DeckPointPair
