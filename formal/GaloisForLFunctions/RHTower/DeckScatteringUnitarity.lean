import GaloisForLFunctions.RHTower.DeckMaassSelbergContinuation

/-!
# Reflection and unitarity of the deck scattering operator

The scattering entries have real Dirichlet coefficients: for `Re s > 1`,
`φ_{∞,σ∞}(s) = Σ_c (c²)^{-s} count_σ(c) · ∫_ℝ (1 + t²)^{-s} dt`, so `conj φ(s) = φ(s̄)`; by the identity
theorem on `{Re > 1/2} \ {1}` and by continuity at the points of the critical line, the same holds on
`{Re ≥ 1/2} \ {1/2, 1}`.  Hence `conj(Φ̃(s) v) = Φ̃(s̄)(conj v)`.

On the critical line `s̄ = 1 − s`, so the transposed functional equation
`⟨Φ̃(1/2 + it) v, Φ̃(1/2 − it) w⟩_β = ⟨v, w⟩_β` becomes
`⟪Φ̃(1/2 + it) v, Φ̃(1/2 + it) w⟫ = ⟪v, w⟫` on `V_∞`: **the scattering operator is unitary on the line**.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Metric EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry SelbergEisensteinStarCriticalLine

noncomputable section

variable {N : ℕ}

/-! ## Reflection of the scattering entries -/

theorem conj_ofReal_nonneg_cpow {r : ℝ} (hr : 0 ≤ r) (s : ℂ) : conj ((r : ℂ) ^ s) = (r : ℂ) ^ conj s := by
  rcases hr.lt_or_eq with hr | hr
  · rw [Complex.cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm),
      Complex.conj_ofReal]
  · subst hr
    simp only [Complex.ofReal_zero]
    by_cases hs : s = 0
    · subst hs; simp
    · rw [Complex.zero_cpow hs, Complex.zero_cpow (by simpa using hs), map_zero]

theorem conj_ker01 (s : ℂ) (t : ℝ) :
    conj (SelbergPoincareKernel.ker 0 1 s t) = SelbergPoincareKernel.ker 0 1 (conj s) t := by
  unfold SelbergPoincareKernel.ker
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal]

theorem conj_Dσ (σ : SL(2, ℤ)) {s : ℂ} (hs : 1 < s.re) :
    conj (SelbergEisensteinCuspScattering.Dσ (N + 1) σ s) =
      SelbergEisensteinCuspScattering.Dσ (N + 1) σ (conj s) := by
  rw [← SelbergEisensteinCuspScattering.tsum_weight_eq_Dσ _ σ hs,
    ← SelbergEisensteinCuspScattering.tsum_weight_eq_Dσ _ σ (by simpa using hs), Complex.conj_tsum]
  refine tsum_congr fun c => ?_
  rw [map_mul, Complex.conj_natCast, ← map_neg, conj_ofReal_nonneg_cpow (by positivity)]

theorem conj_phiσ (σ : SL(2, ℤ)) {s : ℂ} (hs : 1 < s.re) :
    conj (SelbergEisensteinScatteringEntry.phiσ (N + 1) σ s) =
      SelbergEisensteinScatteringEntry.phiσ (N + 1) σ (conj s) := by
  unfold SelbergEisensteinScatteringEntry.phiσ
  rw [map_mul, conj_Dσ σ hs, ← integral_conj]
  simp_rw [conj_ker01]

/-- `{Re ≥ 1/2} \ {1/2, 1}`. -/
abbrev closedHalfDom : Set ℂ := {s : ℂ | 1 / 2 ≤ s.re ∧ s ≠ 1 / 2 ∧ s ≠ 1}

theorem closedHalfDom_subset : closedHalfDom ⊆ contDom N := fun _ hs =>
  ⟨mem_Wset_of_half_le (N + 1) hs.1 hs.2.1, hs.2.2⟩

theorem conj_mem_closedHalfDom {s : ℂ} (hs : s ∈ closedHalfDom) : conj s ∈ closedHalfDom := by
  refine ⟨by simpa using hs.1, fun h => hs.2.1 ?_, fun h => hs.2.2 ?_⟩
  · rw [← Complex.conj_conj s, h, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.conj_ofReal]
  · rw [← Complex.conj_conj s, h]; simp

theorem conj_mem_halfPlaneDom {s : ℂ} (hs : s ∈ halfPlaneDom) : conj s ∈ halfPlaneDom := by
  refine ⟨by simpa using hs.1, fun h => hs.2 ?_⟩
  rw [← Complex.conj_conj s, h]; simp

/-- Agreement on `{Re > 1/2} \ {1}` extends to the points of `{Re ≥ 1/2} \ {1/2, 1}` by continuity. -/
theorem eq_of_eqOn_halfPlaneDom {f g : ℂ → ℂ} {s₀ : ℂ} (hs₀ : s₀ ∈ closedHalfDom)
    (hf : ContinuousAt f s₀) (hg : ContinuousAt g s₀) (h : EqOn f g halfPlaneDom) : f s₀ = g s₀ := by
  rcases hs₀.1.lt_or_eq with hlt | heq
  · exact h ⟨hlt, hs₀.2.2⟩
  have hshift : Tendsto (fun ε : ℝ => s₀ + (ε : ℂ)) (𝓝[>] 0) (𝓝 s₀) := by
    have : Tendsto (fun ε : ℝ => s₀ + (ε : ℂ)) (𝓝 0) (𝓝 (s₀ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have him : s₀.im ≠ 0 := by
    intro him
    apply hs₀.2.1
    apply Complex.ext <;> simp [him, ← heq]
  have hev : (fun ε : ℝ => f (s₀ + (ε : ℂ))) =ᶠ[𝓝[>] 0] fun ε => g (s₀ + (ε : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    refine h ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.ofReal_re]; simp only [mem_Ioi] at hε; linarith
    · intro h1; have := congrArg Complex.im h1; simp at this; exact him this
  exact tendsto_nhds_unique ((hf.tendsto.comp hshift).congr' hev) (hg.tendsto.comp hshift)

theorem conj_phiExt_of_halfPlaneDom (σ : SL(2, ℤ)) {s : ℂ} (hs : s ∈ halfPlaneDom) :
    conj (SelbergEisensteinCriticalLine.phiExt (N + 1) σ s) =
      SelbergEisensteinCriticalLine.phiExt (N + 1) σ (conj s) := by
  have hopen := SelbergEisensteinCuspExpansion.isOpen_punctured
  have hconn := SelbergEisensteinCuspExpansion.isPreconnected_punctured
  have hdiff : ∀ s ∈ halfPlaneDom, DifferentiableAt ℂ (SelbergEisensteinCriticalLine.phiExt (N + 1) σ) s :=
    fun s hs => SelbergEisensteinCriticalLine.differentiableAt_phiExt (N + 1) σ
      (halfPlaneDom_subset (N := N) hs).1 hs.2
  have hf : AnalyticOnNhd ℂ (fun s => conj (SelbergEisensteinCriticalLine.phiExt (N + 1) σ (conj s)))
      halfPlaneDom := by
    refine analyticOnNhd_of_differentiableAt hopen fun s hs => ?_
    have h := (hdiff (conj s) (conj_mem_halfPlaneDom hs)).conj_conj
    simpa [Function.comp_def] using h
  have hg : AnalyticOnNhd ℂ (SelbergEisensteinCriticalLine.phiExt (N + 1) σ) halfPlaneDom :=
    analyticOnNhd_of_differentiableAt hopen hdiff
  have h2 : (2 : ℂ) ∈ halfPlaneDom := ⟨by norm_num, by norm_num⟩
  have hev : (fun s => conj (SelbergEisensteinCriticalLine.phiExt (N + 1) σ (conj s))) =ᶠ[𝓝 (2 : ℂ)]
      SelbergEisensteinCriticalLine.phiExt (N + 1) σ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs'
    have hs1 : 1 < (conj s).re := by simpa using hs'
    rw [← SelbergEisensteinCriticalLine.phiσ_eq_phiExt _ _ (by linarith), conj_phiσ σ hs1,
      Complex.conj_conj, SelbergEisensteinCriticalLine.phiσ_eq_phiExt _ _ (by linarith)]
  have key := hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 hev (conj_mem_halfPlaneDom hs)
  simp only [Complex.conj_conj] at key
  exact key

/-- **Reflection of the scattering entries** on `{Re ≥ 1/2} \ {1/2, 1}`. -/
theorem conj_phiExt (σ : SL(2, ℤ)) {s : ℂ} (hs : s ∈ closedHalfDom) :
    conj (SelbergEisensteinCriticalLine.phiExt (N + 1) σ s) =
      SelbergEisensteinCriticalLine.phiExt (N + 1) σ (conj s) := by
  have hd : ∀ s ∈ closedHalfDom, DifferentiableAt ℂ (SelbergEisensteinCriticalLine.phiExt (N + 1) σ) s :=
    fun s hs => SelbergEisensteinCriticalLine.differentiableAt_phiExt (N + 1) σ
      (closedHalfDom_subset (N := N) hs).1 hs.2.2
  refine eq_of_eqOn_halfPlaneDom (f := fun s => conj (SelbergEisensteinCriticalLine.phiExt (N + 1) σ s))
    (g := fun s => SelbergEisensteinCriticalLine.phiExt (N + 1) σ (conj s)) hs
    (Complex.continuous_conj.continuousAt.comp (hd s hs).continuousAt)
    ((hd (conj s) (conj_mem_closedHalfDom hs)).continuousAt.comp Complex.continuous_conj.continuousAt)
    fun s hs => conj_phiExt_of_halfPlaneDom σ hs

/-! ## Reflection and unitarity of `Φ̃` -/

theorem deckConjVec_apply (X : DeckSpace N) (q : Deck N) : deckConjVec X q = conj (X q) := rfl

theorem deckConjVec_deckConjVec (X : DeckSpace N) : deckConjVec (deckConjVec X) = X := by
  ext q; simp [deckConjVec_apply]

theorem deckRho_deckConjVec (A : SL(2, ℤ)) (X : DeckSpace N) :
    deckRho N A (deckConjVec X) = deckConjVec (deckRho N A X) := by
  ext q
  rw [deckRho_apply, deckConjVec_apply, deckConjVec_apply, deckRho_apply]

theorem isCuspVec_deckConjVec {v : DeckSpace N} (hv : IsCuspVec v) : IsCuspVec (deckConjVec v) :=
  ⟨by rw [deckRho_deckConjVec, hv.1], by rw [deckRho_deckConjVec, hv.2]⟩

theorem conj_scatConst : conj ((2 * (N + 1 : ℂ) ^ 2)⁻¹) = (2 * (N + 1 : ℂ) ^ 2)⁻¹ := by
  have e : (2 * (N + 1 : ℂ) ^ 2)⁻¹ = (((2 * ((N : ℝ) + 1) ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.conj_ofReal]

theorem deckConjVec_scatVec {s : ℂ} (hs : s ∈ closedHalfDom) (v : DeckSpace N) :
    deckConjVec (scatVec s v) = scatVec (conj s) (deckConjVec v) := by
  ext q
  rw [deckConjVec_apply, scatVec_apply, scatVec_apply, map_mul, conj_scatConst, map_sum]
  have hsum : ∑ g : Deck N, conj (SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s *
      v (q * g⁻¹)) = ∑ g : Deck N, SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) (conj s) *
      deckConjVec v (q * g⁻¹) :=
    Finset.sum_congr rfl fun g _ => by rw [map_mul, conj_phiExt _ hs, deckConjVec_apply]
  rw [hsum]

theorem inner_eq_bil (X Y : DeckSpace N) : ⟪X, Y⟫_ℂ = bil (deckConjVec X) Y := by
  rw [bil_eq_inner, deckConjVec_deckConjVec]

/-- **Unitarity of the scattering operator on the critical line**:
`⟪Φ̃(1/2 + it) v, Φ̃(1/2 + it) w⟫ = ⟪v, w⟫` for `v, w ∈ V_∞`, `t ≠ 0`. -/
theorem inner_scatVec_line (hN : 2 ≤ N) {t : ℝ} (ht : t ≠ 0) {v w : DeckSpace N} (hv : IsCuspVec v)
    (hw : IsCuspVec w) :
    ⟪scatVec ((1 / 2 : ℝ) + t * Complex.I) v, scatVec ((1 / 2 : ℝ) + t * Complex.I) w⟫_ℂ = ⟪v, w⟫_ℂ := by
  have hs : ((1 / 2 : ℝ) : ℂ) + t * Complex.I ∈ closedHalfDom := by
    refine ⟨by simp, ?_, ?_⟩ <;> intro h <;> have := congrArg Complex.im h <;> simp at this <;> exact ht this
  have hconj : conj (((1 / 2 : ℝ) : ℂ) + t * Complex.I) = ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [inner_eq_bil, inner_eq_bil, deckConjVec_scatVec hs, hconj]
  have h := bil_scatVec_line hN (neg_ne_zero.2 ht) (isCuspVec_deckConjVec hv) hw
  simp only [Complex.ofReal_neg, neg_neg] at h ⊢
  exact h

theorem norm_scatVec_line (hN : 2 ≤ N) {t : ℝ} (ht : t ≠ 0) {v : DeckSpace N} (hv : IsCuspVec v) :
    ‖scatVec ((1 / 2 : ℝ) + t * Complex.I) v‖ = ‖v‖ := by
  have h := inner_scatVec_line hN ht hv hv
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖scatVec ((1 / 2 : ℝ) + t * Complex.I) v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'

end

end GaloisForLFunctions.RHTower.DeckPointPair
