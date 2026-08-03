import GaloisForLFunctions.HTGeometry.ClockSlabExistence
import GaloisForLFunctions.HTGeometry.ClockProbeFullySeparable

/-!
# A null slab block times one-dimensional factors

The slab construction and the fully separable construction are orthogonal to each other and can be
multiplied. On a diagonal chart the gradient pairing is a sum over coordinates, and a slab lift has
no transverse derivative while a product of transverse coordinate factors has no derivative in the
two null directions, so the two factors pair to zero. The Leibniz rule for the d'Alembertian then
turns a product of solutions into a solution for the sum of the potentials.

The result is a determined class in every dimension which is genuinely larger than either
constituent: potentials

`V(x) = v(x⁰ + x¹, x⁰ - x¹) + ∑ⱼ Vⱼ(xʲ)`

with an arbitrary continuously differentiable function of the two null coordinates and arbitrary
continuously differentiable profiles in the transverse ones. The two-dimensional block is solved by
the Goursat construction, each transverse block by Picard–Lindelöf.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {n : ℕ}

/-! ## The two factors are orthogonal -/

variable {u A B : ℝ → ℝ → ℝ} {Ω : Set (ℝ × ℝ)}

theorem gradPair_slabLift_boxProduct (h : IsC1On u A B Ω) {w : Fin (n + 2) → ℝ → ℝ}
    {s : Finset (Fin (n + 2))} (hs0 : (0 : Fin (n + 2)) ∉ s) (hs1 : (1 : Fin (n + 2)) ∉ s)
    {x : Fin (n + 2) → ℝ} (hxΩ : slabCLM n x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.gradPair
      (slabLift u n) (boxProduct w s) x = 0 := by
  rw [ofSignature_gradPair]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h0 : i = 0
  · subst h0
    rw [coordPartial_boxProduct_of_notMem w hs0 x]
    ring
  · by_cases h1 : i = 1
    · subst h1
      rw [coordPartial_boxProduct_of_notMem w hs1 x]
      ring
    · rw [coordPartial_slabLift_transverse h hxΩ h0 h1]
      ring

/-! ## The product solves the sum equation -/

variable {Aa Ab Ba Bb : ℝ → ℝ → ℝ}

/-- **A slab block times transverse coordinate factors solves the sum potential.** -/
theorem slabSeparable_solves (h : IsC1On u A B Ω) (hA : IsC1On A Aa Ab Ω)
    (hB : IsC1On B Ba Bb Ω) {vv : ℝ → ℝ → ℝ}
    (w dw ddw Vt : Fin (n + 2) → ℝ → ℝ) (I : Fin (n + 2) → Set ℝ) (hI : ∀ i, IsOpen (I i))
    (hd1 : ∀ i, ∀ t ∈ I i, HasDerivAt (w i) (dw i t) t)
    (hd2 : ∀ i, ∀ t ∈ I i, HasDerivAt (dw i) (ddw i t) t)
    (heq : ∀ i t, (slabEps n i)⁻¹ * ddw i t + Vt i t * w i t = 0)
    (s : Finset (Fin (n + 2))) (hs0 : (0 : Fin (n + 2)) ∉ s) (hs1 : (1 : Fin (n + 2)) ∉ s)
    {x : Fin (n + 2) → ℝ} (hxI : ∀ i, x i ∈ I i) (hxΩ : slabCLM n x ∈ Ω)
    (hslab : SolvesPotentialWaveAt
      (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      (slabLift vv n) (slabLift u n) x) :
    SolvesPotentialWaveAt
      (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      (fun y => slabLift vv n y + ∑ i ∈ s, Vt i (y i))
      (fun y => slabLift u n y * boxProduct w s y) x := by
  classical
  obtain ⟨hgdiff, hgpartial, hgsolve⟩ :=
    boxProduct_solves (d := n + 1) (slabEps n) (slabEps_ne_zero n) w dw ddw Vt I hI hd1 hd2 heq
      hxI s
  have hIopen : IsOpen {y : Fin (n + 2) → ℝ | ∀ i, y i ∈ I i} := by
    have hEq : {y : Fin (n + 2) → ℝ | ∀ i, y i ∈ I i}
        = ⋂ i, (fun y : Fin (n + 2) → ℝ => y i) ⁻¹' I i := by
      ext y
      simp
    rw [hEq]
    exact isOpen_iInter_of_finite fun i => (hI i).preimage (continuous_apply i)
  have hUopen : IsOpen (slabBox Ω n ∩ {y : Fin (n + 2) → ℝ | ∀ i, y i ∈ I i}) :=
    (isOpen_slabBox h.isOpen n).inter hIopen
  have hxU : x ∈ slabBox Ω n ∩ {y : Fin (n + 2) → ℝ | ∀ i, y i ∈ I i} := ⟨hxΩ, hxI⟩
  have hgp := gradPair_slabLift_boxProduct h hs0 hs1 hxΩ (w := w) (s := s)
  have hmul := dalembert_mul_of_differentiableAt (d := n + 1) (slabEps n) (slabEps_ne_zero n)
    hUopen hxU (fun y hy => differentiableAt_slabLift h hy.1)
    (fun y hy => hgdiff y hy.2)
    (fun i => differentiableAt_coordPartial_slabLift h hA hB hxΩ i) hgpartial
  have h1 : (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      (slabLift u n) x + slabLift vv n x * slabLift u n x = 0 := hslab
  have h2 : (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      (boxProduct w s) x + (∑ i ∈ s, Vt i (x i)) * boxProduct w s x = 0 := hgsolve
  show (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      (fun y => slabLift u n y * boxProduct w s y) x
    + (slabLift vv n x + ∑ i ∈ s, Vt i (x i)) * (slabLift u n x * boxProduct w s x) = 0
  rw [hmul, hgp]
  linear_combination boxProduct w s x * h1 + slabLift u n x * h2

/-! ## Existence -/

/-- **Clock probes for a null-slab block plus transverse one-dimensional profiles**, in every
dimension. -/
theorem exists_clockProbe_on_slabSeparable {vv : ℝ → ℝ → ℝ}
    (hvv : ContDiff ℝ 1 fun p : ℝ × ℝ => vv p.1 p.2) {Vt : Fin (n + 2) → ℝ → ℝ}
    (hVt : ∀ i, ContDiff ℝ 1 (Vt i)) (s : Finset (Fin (n + 2)))
    (hs0 : (0 : Fin (n + 2)) ∉ s) (hs1 : (1 : Fin (n + 2)) ∉ s) (x : Fin (n + 2) → ℝ) :
    ∃ W : Set (Fin (n + 2) → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ U : (Fin (n + 2) → ℝ) → ℝ,
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          (fun y => slabLift vv n y + ∑ i ∈ s, Vt i (y i)) U W ∧
        (∀ y ∈ W, U y ≠ 0) ∧ U x = 1 := by
  classical
  -- the transverse one-dimensional factors
  choose w dw ddw r hr hwb hd1 hd2 hqeq using fun i : Fin (n + 2) =>
    exists_localLinearProbe (p := fun _ => (0 : ℝ)) contDiff_const
      (contDiff_const.mul (hVt i) : ContDiff ℝ 1 fun t => slabEps n i * Vt i t) (x i)
  have heq : ∀ (i : Fin (n + 2)) (t : ℝ),
      (slabEps n i)⁻¹ * ddw i t + Vt i t * w i t = 0 := by
    intro i t
    have hne : slabEps n i ≠ 0 := slabEps_ne_zero n i
    have hq := hqeq i t
    simp only [zero_mul, add_zero] at hq
    have hd : ddw i t = -(slabEps n i * Vt i t * w i t) := by linarith [hq]
    rw [hd, mul_neg, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    ring
  -- the two-dimensional block
  set F : ℝ × ℝ → ℝ := fun p => vv p.1 p.2 / 4 with hF_def
  have hFC : ContDiff ℝ 1 F := hvv.div_const 4
  set ξ₀ : ℝ := x 0 + x 1 with hξ₀
  set η₀ : ℝ := x 0 - x 1 with hη₀
  set c : ℝ := ξ₀ - 1 with hc
  set c' : ℝ := ξ₀ + 1 with hc'
  set b : ℝ := η₀ - 1 with hb
  set b' : ℝ := η₀ + 1 with hb'
  have hcc : c ≤ c' := by rw [hc, hc']; linarith
  have hbb : b ≤ b' := by rw [hb, hb']; linarith
  obtain ⟨M, hMbound⟩ := ((isCompact_Icc (a := c) (b := c')).prod
    (isCompact_Icc (a := b) (b := b'))).exists_bound_of_continuousOn hFC.continuous.continuousOn
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg (F (c, b))) (hMbound (c, b) ⟨⟨le_rfl, hcc⟩, ⟨le_rfl, hbb⟩⟩)
  have hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |F (ξ, t)| ≤ M := by
    intro ξ hξ t ht
    have := hMbound (ξ, t) ⟨hξ, ht⟩
    rwa [Real.norm_eq_abs] at this
  obtain ⟨hgo, hh, u, A, B, Aa, Ab, Ba, Bb, hu0, hujoint, hC1u, hC1A, hC1B, hAbeq, hBaeq⟩ :=
    exists_goursat_C2 (fun ξ η => F (ξ, η)) (planarFst F) (planarSnd F) b b' c c' M
      hFC.continuous (continuous_planarFst hFC) (continuous_planarSnd hFC)
      (hasDerivAt_planarFst hFC) (hasDerivAt_planarSnd hFC) hbb hcc hM0 hM ξ₀
  have hΩopen : IsOpen ((Ioo (ξ₀ - hgo) (ξ₀ + hgo) ∩ Ioo c c') ×ˢ Ioo b b') :=
    (isOpen_Ioo.inter isOpen_Ioo).prod isOpen_Ioo
  have hmemΩ : slabCLM n x ∈ (Ioo (ξ₀ - hgo) (ξ₀ + hgo) ∩ Ioo c c') ×ˢ Ioo b b' := by
    rw [slabCLM_apply, ← hξ₀, ← hη₀]
    exact ⟨⟨⟨by linarith, by linarith⟩, by rw [hc, hc']; constructor <;> linarith⟩,
      by rw [hb, hb']; constructor <;> linarith⟩
  -- the slab factor solves its own equation everywhere on the rectangle
  have hslabSolve : ∀ y : Fin (n + 2) → ℝ,
      slabCLM n y ∈ (Ioo (ξ₀ - hgo) (ξ₀ + hgo) ∩ Ioo c c') ×ˢ Ioo b b' →
      SolvesPotentialWaveAt
        (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
        (slabLift vv n) (slabLift u n) y := by
    intro y hy
    have hab := hAbeq (slabCLM n y) hy
    have hba := hBaeq (slabCLM n y) hy
    simp only [slabCLM_apply] at hab hba
    show (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
        (slabLift u n) y + slabLift vv n y * slabLift u n y = 0
    rw [dalembert_slabLift hC1u hC1A hC1B hy, hab, hba]
    show -2 * (F (y 0 + y 1, y 0 - y 1) * u (y 0 + y 1) (y 0 - y 1)
        + F (y 0 + y 1, y 0 - y 1) * u (y 0 + y 1) (y 0 - y 1))
        + vv (y 0 + y 1) (y 0 - y 1) * u (y 0 + y 1) (y 0 - y 1) = 0
    rw [hF_def]
    ring
  -- the region
  set W₀ : Set (Fin (n + 2) → ℝ) :=
    slabBox ((Ioo (ξ₀ - hgo) (ξ₀ + hgo) ∩ Ioo c c') ×ˢ Ioo b b') n
      ∩ {y | ∀ i, y i ∈ Ioo (x i - r i) (x i + r i)} with hW₀
  have hIopen : IsOpen {y : Fin (n + 2) → ℝ | ∀ i, y i ∈ Ioo (x i - r i) (x i + r i)} := by
    have hEq : {y : Fin (n + 2) → ℝ | ∀ i, y i ∈ Ioo (x i - r i) (x i + r i)}
        = ⋂ i, (fun y : Fin (n + 2) → ℝ => y i) ⁻¹' Ioo (x i - r i) (x i + r i) := by
      ext y
      simp
    rw [hEq]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)
  have hW₀open : IsOpen W₀ := (isOpen_slabBox hΩopen n).inter hIopen
  have hxr : ∀ i, x i ∈ Ioo (x i - r i) (x i + r i) := by
    intro i
    constructor <;> [linarith [hr i]; linarith [hr i]]
  have hxW₀ : x ∈ W₀ := ⟨hmemΩ, hxr⟩
  -- the probe and its continuity on the region
  have hprodcont : ContinuousOn (fun y => slabLift u n y * boxProduct w s y) W₀ := by
    intro y hy
    have h1 : DifferentiableAt ℝ (slabLift u n) y := differentiableAt_slabLift hC1u hy.1
    have h2 : DifferentiableAt ℝ (boxProduct w s) y :=
      (boxProduct_solves (d := n + 1) (slabEps n) (slabEps_ne_zero n) w dw ddw Vt
        (fun i => Ioo (x i - r i) (x i + r i)) (fun _ => isOpen_Ioo) hd1 hd2 heq hxr s).1 y hy.2
    exact ((h1.mul h2).continuousAt).continuousWithinAt
  have hU1 : (fun y => slabLift u n y * boxProduct w s y) x = 1 := by
    show slabLift u n x * boxProduct w s x = 1
    rw [boxProduct_apply]
    have hslab1 : slabLift u n x = 1 := by
      show u (x 0 + x 1) (x 0 - x 1) = 1
      rw [← hξ₀, ← hη₀]
      exact hu0 _
    rw [hslab1, one_mul]
    exact Finset.prod_eq_one fun i _ => hwb i
  refine ⟨W₀ ∩ (fun y => slabLift u n y * boxProduct w s y) ⁻¹' {z : ℝ | z ≠ 0},
    hprodcont.isOpen_inter_preimage hW₀open isOpen_ne,
    ⟨hxW₀, by show (fun y => slabLift u n y * boxProduct w s y) x ≠ 0; rw [hU1]; exact one_ne_zero⟩,
    fun y => slabLift u n y * boxProduct w s y, ?_, fun y hy => hy.2, hU1⟩
  intro y hy
  exact slabSeparable_solves hC1u hC1A hC1B w dw ddw Vt
    (fun i => Ioo (x i - r i) (x i + r i)) (fun _ => isOpen_Ioo) hd1 hd2 heq s hs0 hs1
    hy.1.2 hy.1.1 (hslabSolve y hy.1.1)

end GaloisForLFunctions.HTGeometry
