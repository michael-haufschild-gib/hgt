import GaloisForLFunctions.RHTower.CHMDPurePointAboveThreshold

/-!
# The spectral Riemann criterion: RH ⟺ no primitive bound state above 1/2

Let `R` be the bounded arithmetic resolvent on `L²(Θcosh(x/2)dx)` and `1` the constant function
(the ground state, `R 1 = 1`). The primitive hyperplane `1^⊥` is `R`-invariant. Then

`RH ⟺ ⟪Rw, w⟫ ≤ ½‖w‖² for all w ⊥ 1 ⟺ R has no eigenvector w ⊥ 1 with eigenvalue μ > 1/2`.

The first equivalence is the corpus primitive Dirichlet–Poincaré criterion (Doob energy `≥ 0` on
primitive compact tests) extended by density to the primitive hyperplane of the graph, then
converted into the resolvent bound through `E(p) = ‖p‖² − 2‖Sp‖²`, `R = SS*`. The second uses the
pure point structure of the spectrum above `1/2`: if the numerical range of `R` on `1^⊥` exceeds
`1/2`, its supremum `M` carries unit approximate eigenvectors (a variational argument using only the
Cauchy–Schwarz inequality of the positive form), whose weak limit is a primitive eigenvector at `M`.

Together with the discreteness results: RH fails exactly when the arithmetic resolvent has a bound
state in the primitive sector above its essential threshold; such bound states are finitely
degenerate and finitely many above every `1/2 + ε`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## The primitive hyperplane -/

/-- A graph vector is primitive if its source is orthogonal to the constant ground state. -/
def PrimitiveGraph (p : SourceGraph) : Prop := ⟪p.val.fst, oneL⟫_ℝ = 0

theorem inner_compactLift_oneL (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ⟪(compactLift v hv hvc).val.fst, oneL⟫_ℝ = phiDoobCoshMass v := by
  rw [inner_oneL, phiDoobCoshMass_eq_integral_mass]
  exact integral_congr_ae (compactLift_source_ae v hv hvc)

theorem primitiveGraph_compactLift_iff (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) :
    PrimitiveGraph (compactLift v hv hvc) ↔ phiDoobCoshMass v = 0 := by
  unfold PrimitiveGraph
  rw [inner_compactLift_oneL]

/-! ## The corpus criterion on compact tests, in graph form -/

theorem sourceEnergy_compactLift_nonneg_of_rh (hRH : RiemannHypothesis) {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (hp : PrimitiveGraph (compactLift v hv hvc)) :
    0 ≤ sourceEnergy (compactLift v hv hvc) := by
  have h := (riemannHypothesis_iff_forall_phiDoobCoshMass_zero_dirichlet_poincare.mp hRH) v hv hvc
    ((primitiveGraph_compactLift_iff v hv hvc).mp hp)
  have h2 : phiDoobCoshMass (fun x => v x ^ 2) = ∫ x, v x ^ 2 ∂massMeasure :=
    phiDoobCoshMass_eq_integral_mass _
  rw [sourceEnergy_compactLift_eq]
  linarith

theorem riemannHypothesis_of_primitive_energy
    (hE : ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v),
      PrimitiveGraph (compactLift v hv hvc) → 0 ≤ sourceEnergy (compactLift v hv hvc)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_phiDoobCoshMass_zero_dirichlet_poincare]
  intro v hv hvc hmass
  have h := hE v hv hvc ((primitiveGraph_compactLift_iff v hv hvc).mpr hmass)
  have h2 : phiDoobCoshMass (fun x => v x ^ 2) = ∫ x, v x ^ 2 ∂massMeasure :=
    phiDoobCoshMass_eq_integral_mass _
  rw [sourceEnergy_compactLift_eq] at h
  linarith

/-! ## Density: the criterion on the whole primitive hyperplane -/

/-- A compact test of positive mass. -/
theorem exists_compactTest_mass_pos :
    ∃ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v),
      0 < ⟪(compactLift v hv hvc).val.fst, oneL⟫_ℝ := by
  refine ⟨windowBump 0 le_rfl, contDiff_windowBump 0 le_rfl, hasCompactSupport_windowBump 0 le_rfl, ?_⟩
  rw [inner_oneL, integral_congr_ae (compactLift_source_ae _ _ _), integral_mass]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (continuous_massDensity.mul (contDiff_windowBump 0 le_rfl).continuous)
    (hasCompactSupport_windowBump 0 le_rfl).mul_left
    (fun x => mul_nonneg (massDensity_pos x).le (windowBump_nonneg _ _ x)) ?_
  show massDensity 0 * windowBump 0 le_rfl 0 ≠ 0
  rw [windowBump_eq_one le_rfl (by rw [abs_zero]; norm_num), mul_one]
  exact (massDensity_pos 0).ne'

/-- **RH ⇒ nonnegative Doob energy on the primitive hyperplane.** -/
theorem sourceEnergy_nonneg_of_rh (hRH : RiemannHypothesis) (p : SourceGraph)
    (hp : PrimitiveGraph p) : 0 ≤ sourceEnergy p := by
  obtain ⟨v₀, hv₀, hv₀c, hpos⟩ := exists_compactTest_mass_pos
  set q₀ : SourceGraph := compactLift v₀ hv₀ hv₀c with hq₀
  set c₀ : ℝ := ⟪q₀.val.fst, oneL⟫_ℝ with hc₀
  have hc₀ne : c₀ ≠ 0 := hpos.ne'
  set Φ : SourceGraph → SourceGraph := fun q => q - (⟪q.val.fst, oneL⟫_ℝ / c₀) • q₀ with hΦ
  have hℓ : Continuous fun q : SourceGraph => ⟪q.val.fst, oneL⟫_ℝ :=
    sourceMap.continuous.inner continuous_const
  have hΦc : Continuous Φ := continuous_id.sub ((hℓ.div_const c₀).smul continuous_const)
  have hΦprim : ∀ q, PrimitiveGraph (Φ q) := by
    intro q
    unfold PrimitiveGraph
    have hfst : (Φ q).val.fst = q.val.fst - (⟪q.val.fst, oneL⟫_ℝ / c₀) • q₀.val.fst := rfl
    rw [hfst, inner_sub_left, real_inner_smul_left, ← hc₀, div_mul_cancel₀ _ hc₀ne, sub_self]
  have hΦtests : ∀ q ∈ compactTests, Φ q ∈ compactTests := fun q hq =>
    compactTests.sub_mem hq (compactTests.smul_mem _ ⟨v₀, hv₀, hv₀c, rfl⟩)
  have hΦp : Φ p = p := by
    simp only [hΦ]
    rw [show ⟪p.val.fst, oneL⟫_ℝ = 0 from hp, zero_div, zero_smul, sub_zero]
  have hclosed : IsClosed {q : SourceGraph | 0 ≤ sourceEnergy q} :=
    isClosed_le continuous_const continuous_sourceEnergy
  have hsub : Φ '' (compactTests : Set SourceGraph) ⊆ {q | 0 ≤ sourceEnergy q} := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨v, hv, hvc, hqv⟩ := hΦtests q hq
    show 0 ≤ sourceEnergy (Φ q)
    rw [hqv]
    exact sourceEnergy_compactLift_nonneg_of_rh hRH hv hvc (by rw [← hqv]; exact hΦprim q)
  have hp' : p ∈ closure (Φ '' (compactTests : Set SourceGraph)) := by
    rw [← hΦp]
    exact mem_closure_image hΦc.continuousAt (by rw [dense_compactTests.closure_eq]; trivial)
  exact closure_minimal hsub hclosed hp'

/-! ## From energy to the resolvent bound on the primitive hyperplane -/

/-- `R ≤ 1/2` on the primitive hyperplane of the mass space. -/
def ResolventHalfBound : Prop :=
  ∀ w : MassSpace, ⟪w, oneL⟫_ℝ = 0 → ⟪resolvent w, w⟫_ℝ ≤ (1 / 2) * ‖w‖ ^ 2

theorem sq_le_half_sq {a b c : ℝ} (h1 : a ^ 2 ≤ b * c) (h2 : b ^ 2 ≤ (1 / 2) * a ^ 2) :
    a ^ 2 ≤ (1 / 2) * c ^ 2 := by
  by_contra hneg
  rw [not_le] at hneg
  have hpos : 0 < a ^ 2 := by nlinarith [sq_nonneg c]
  have hbc : 0 ≤ b * c := le_trans (sq_nonneg a) h1
  have e1 : a ^ 2 * a ^ 2 ≤ (b * c) * (b * c) := mul_self_le_mul_self (sq_nonneg a) h1
  have e2 : b ^ 2 * c ^ 2 ≤ (1 / 2) * a ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg c)
  have e3 : a ^ 2 * ((1 / 2) * c ^ 2) < a ^ 2 * a ^ 2 := mul_lt_mul_of_pos_left hneg hpos
  nlinarith

theorem primitiveGraph_rieszLift {w : MassSpace} (hw : ⟪w, oneL⟫_ℝ = 0) :
    PrimitiveGraph (rieszLift w) := by
  unfold PrimitiveGraph
  show ⟪resolvent w, oneL⟫_ℝ = 0
  rw [inner_resolvent_oneL, real_inner_comm]
  exact hw

theorem resolventHalfBound_of_energy (hE : ∀ p : SourceGraph, PrimitiveGraph p → 0 ≤ sourceEnergy p) :
    ResolventHalfBound := by
  intro w hw
  have hE' := hE _ (primitiveGraph_rieszLift hw)
  rw [sourceEnergy_rieszLift] at hE'
  have h1 : ⟪resolvent w, w⟫_ℝ = ‖rieszLift w‖ ^ 2 := inner_resolvent_self w
  have h2 : ‖rieszLift w‖ ^ 2 = ⟪w, resolvent w⟫_ℝ := graph_norm_sq_rieszLift w
  have h3 : ‖resolvent w‖ ^ 2 ≤ (1 / 2) * ‖rieszLift w‖ ^ 2 := by linarith
  have h4 : ‖rieszLift w‖ ^ 2 ≤ ‖resolvent w‖ * ‖w‖ := by
    rw [h2]
    exact (real_inner_le_norm _ _).trans_eq (mul_comm _ _)
  rw [h1]
  exact sq_le_half_sq h4 h3

theorem sourceEnergy_eq_graph_sub (p : SourceGraph) :
    sourceEnergy p = ‖p‖ ^ 2 - 2 * ‖p.val.fst‖ ^ 2 := by
  have h := graph_norm_sq p
  show ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2 = _
  linarith

theorem energy_nonneg_of_resolventHalfBound (hR : ResolventHalfBound) (p : SourceGraph)
    (hp : PrimitiveGraph p) : 0 ≤ sourceEnergy p := by
  have h1 := hR p.val.fst hp
  have h2 : ‖p.val.fst‖ ^ 2 ≤ ‖rieszLift p.val.fst‖ * ‖p‖ := by
    rw [← real_inner_self_eq_norm_sq, ← inner_rieszLift]
    exact real_inner_le_norm _ _
  have h3 : ‖rieszLift p.val.fst‖ ^ 2 ≤ (1 / 2) * ‖p.val.fst‖ ^ 2 := by
    rw [← inner_resolvent_self]
    exact h1
  have h4 := sq_le_half_sq h2 h3
  rw [sourceEnergy_eq_graph_sub]
  linarith

/-- **RH ⟺ the arithmetic resolvent is at most `1/2` on the primitive hyperplane.** -/
theorem riemannHypothesis_iff_resolventHalfBound : RiemannHypothesis ↔ ResolventHalfBound :=
  ⟨fun h => resolventHalfBound_of_energy (sourceEnergy_nonneg_of_rh h),
   fun h => riemannHypothesis_of_primitive_energy fun _ _ _ hp =>
    energy_nonneg_of_resolventHalfBound h _ hp⟩

/-! ## From the resolvent bound to bound states -/

theorem eq_zero_of_primitive_eigenvector_of_resolventHalfBound (hR : ResolventHalfBound) {μ : ℝ}
    (hμ : 1 / 2 < μ) {w : MassSpace} (hw : ⟪w, oneL⟫_ℝ = 0) (heig : resolvent w = μ • w) :
    w = 0 := by
  by_contra h0
  have h := hR w hw
  rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
  have hpos : 0 < ‖w‖ ^ 2 := by
    have := norm_pos_iff.mpr h0
    positivity
  nlinarith

/-- Weak limits of primitive unit approximate eigenvectors above `1/2` are primitive eigenvectors. -/
theorem exists_primitive_eigenvector_of_approx_eigen_above_half {μ : ℝ} (hμ : 1 / 2 < μ)
    (w : ℕ → MassSpace) (hw1 : ∀ n, ‖w n‖ = 1)
    (hw : Tendsto (fun n => ‖resolvent (w n) - μ • w n‖) atTop (𝓝 0))
    (hprim : ∀ n, ⟪w n, oneL⟫_ℝ = 0) :
    ∃ x : MassSpace, x ≠ 0 ∧ resolvent x = μ • x ∧ ⟪x, oneL⟫_ℝ = 0 := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology MassSpace := Lp.SecondCountableTopology
  obtain ⟨x, φ, hφ, hweak⟩ := exists_real_weak_subseq w 1 fun n => (hw1 n).le
  have hw' : Tendsto (fun n => ‖resolvent (w (φ n)) - μ • w (φ n)‖) atTop (𝓝 0) :=
    hw.comp hφ.tendsto_atTop
  refine ⟨x, ?_, ?_, ?_⟩
  · intro hx0
    rw [hx0] at hweak
    refine no_weakly_null_weyl_above_half hμ (fun n => w (φ n)) (fun n => hw1 _) ?_ hw'
    intro k
    simpa using hweak k
  · apply ext_inner_right ℝ
    intro k
    have h1 : Tendsto (fun n => ⟪resolvent (w (φ n)) - μ • w (φ n), k⟫_ℝ) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => norm_inner_le_norm _ _) ?_
      simpa using hw'.mul_const ‖k‖
    have ha : Tendsto (fun n => ⟪resolvent (w (φ n)), k⟫_ℝ) atTop (𝓝 ⟪resolvent x, k⟫_ℝ) := by
      have h := hweak (resolvent k)
      rw [← resolvent_symm] at h
      refine Filter.Tendsto.congr (fun n => ?_) h
      exact (resolvent_symm _ _).symm
    have hb : Tendsto (fun n => μ * ⟪w (φ n), k⟫_ℝ) atTop (𝓝 (μ * ⟪x, k⟫_ℝ)) :=
      (hweak k).const_mul μ
    have h2 : Tendsto (fun n => ⟪resolvent (w (φ n)) - μ • w (φ n), k⟫_ℝ) atTop
        (𝓝 (⟪resolvent x, k⟫_ℝ - μ * ⟪x, k⟫_ℝ)) := by
      refine Filter.Tendsto.congr (fun n => ?_) (ha.sub hb)
      rw [inner_sub_left, real_inner_smul_left]
    have h3 := tendsto_nhds_unique h2 h1
    rw [real_inner_smul_left]
    linarith
  · have h := hweak oneL
    have h0 : Tendsto (fun n => ⟪w (φ n), oneL⟫_ℝ) atTop (𝓝 0) := by
      simp only [hprim]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h h0

/-- Cauchy–Schwarz for the positive form `⟪R·,·⟫`. -/
theorem inner_resolvent_sq_le (x y : MassSpace) :
    ⟪resolvent x, y⟫_ℝ ^ 2 ≤ ⟪resolvent x, x⟫_ℝ * ⟪resolvent y, y⟫_ℝ := by
  have hq : ∀ t : ℝ, 0 ≤ ⟪resolvent y, y⟫_ℝ * (t * t) + (-2 * ⟪resolvent x, y⟫_ℝ) * t +
      ⟪resolvent x, x⟫_ℝ := by
    intro t
    have hnn : 0 ≤ ⟪resolvent (x - t • y), x - t • y⟫_ℝ := by
      rw [inner_resolvent_self]
      positivity
    have hyx : ⟪resolvent y, x⟫_ℝ = ⟪resolvent x, y⟫_ℝ := by
      rw [resolvent_symm, real_inner_comm]
    rw [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, hyx] at hnn
    nlinarith [hnn]
  have h := discrim_le_zero hq
  unfold discrim at h
  nlinarith [h]

theorem resolventHalfBound_of_no_primitive_bound_state
    (h : ∀ (μ : ℝ) (w : MassSpace), 1 / 2 < μ → ⟪w, oneL⟫_ℝ = 0 → resolvent w = μ • w → w = 0) :
    ResolventHalfBound := by
  by_contra hno
  unfold ResolventHalfBound at hno
  simp only [not_forall, not_le] at hno
  obtain ⟨w₀, hw₀, hlt⟩ := hno
  have hw₀ne : w₀ ≠ 0 := by
    rintro rfl
    simp at hlt
  set P : Set MassSpace := {w | ⟪w, oneL⟫_ℝ = 0 ∧ ‖w‖ = 1} with hP
  set Sset : Set ℝ := (fun w => ⟪resolvent w, w⟫_ℝ) '' P with hSset
  -- normalized vectors of the primitive hyperplane
  have hnorm_mem : ∀ w : MassSpace, ⟪w, oneL⟫_ℝ = 0 → w ≠ 0 → ‖w‖⁻¹ • w ∈ P := by
    intro w hw hw0
    refine ⟨?_, norm_smul_inv_norm hw0⟩
    rw [real_inner_smul_left, hw, mul_zero]
  have hnorm_val : ∀ w : MassSpace, ⟪resolvent (‖w‖⁻¹ • w), ‖w‖⁻¹ • w⟫_ℝ =
      ‖w‖⁻¹ ^ 2 * ⟪resolvent w, w⟫_ℝ := by
    intro w
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  have hne : Sset.Nonempty := ⟨_, ⟨_, hnorm_mem w₀ hw₀ hw₀ne, rfl⟩⟩
  have hbdd : BddAbove Sset := by
    refine ⟨1, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    calc ⟪resolvent w, w⟫_ℝ ≤ ‖resolvent w‖ * ‖w‖ := real_inner_le_norm _ _
      _ ≤ ‖w‖ * ‖w‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact (resolvent.le_opNorm w).trans (mul_le_of_le_one_left (norm_nonneg _) norm_resolvent_le)
      _ = 1 := by rw [hw.2, mul_one]
  set M : ℝ := sSup Sset with hM
  have hM_half : 1 / 2 < M := by
    have h1 : ⟪resolvent (‖w₀‖⁻¹ • w₀), ‖w₀‖⁻¹ • w₀⟫_ℝ ≤ M :=
      le_csSup hbdd ⟨_, hnorm_mem w₀ hw₀ hw₀ne, rfl⟩
    rw [hnorm_val] at h1
    have hpos : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀ne
    have h2 : (1 / 2 : ℝ) < ‖w₀‖⁻¹ ^ 2 * ⟪resolvent w₀, w₀⟫_ℝ := by
      rw [inv_pow, lt_inv_mul_iff₀ (by positivity)]
      linarith
    linarith
  have hM0 : 0 < M := by linarith
  -- the numerical bound on the primitive hyperplane
  have hMb : ∀ w : MassSpace, ⟪w, oneL⟫_ℝ = 0 → ⟪resolvent w, w⟫_ℝ ≤ M * ‖w‖ ^ 2 := by
    intro w hw
    by_cases h0 : w = 0
    · rw [h0]
      simp
    · have h1 : ⟪resolvent (‖w‖⁻¹ • w), ‖w‖⁻¹ • w⟫_ℝ ≤ M := le_csSup hbdd ⟨_, hnorm_mem w hw h0, rfl⟩
      rw [hnorm_val] at h1
      have hpos : 0 < ‖w‖ ^ 2 := by
        have := norm_pos_iff.mpr h0
        positivity
      rw [inv_pow, inv_mul_le_iff₀ hpos] at h1
      linarith
  -- the key inequality `‖Rw‖² ≤ M ⟪Rw, w⟫` on the primitive hyperplane
  have hkey : ∀ w : MassSpace, ⟪w, oneL⟫_ℝ = 0 →
      ‖resolvent w‖ ^ 2 ≤ M * ⟪resolvent w, w⟫_ℝ := by
    intro w hw
    have hRw : ⟪resolvent w, oneL⟫_ℝ = 0 := by
      rw [inner_resolvent_oneL, real_inner_comm]
      exact hw
    have h1 := inner_resolvent_sq_le w (resolvent w)
    have h2 := hMb (resolvent w) hRw
    rw [real_inner_self_eq_norm_sq] at h1
    have hnn : 0 ≤ ⟪resolvent w, w⟫_ℝ := by
      rw [inner_resolvent_self]
      positivity
    by_cases h0 : ‖resolvent w‖ = 0
    · rw [h0]
      simp
      exact mul_nonneg hM0.le hnn
    · have hpos : 0 < ‖resolvent w‖ ^ 2 := by positivity
      have h3 : ‖resolvent w‖ ^ 2 * ‖resolvent w‖ ^ 2 ≤ (M * ⟪resolvent w, w⟫_ℝ) * ‖resolvent w‖ ^ 2 := by
        calc ‖resolvent w‖ ^ 2 * ‖resolvent w‖ ^ 2 = (‖resolvent w‖ ^ 2) ^ 2 := by ring
          _ ≤ ⟪resolvent w, w⟫_ℝ * ⟪resolvent (resolvent w), resolvent w⟫_ℝ := h1
          _ ≤ ⟪resolvent w, w⟫_ℝ * (M * ‖resolvent w‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hnn
          _ = (M * ⟪resolvent w, w⟫_ℝ) * ‖resolvent w‖ ^ 2 := by ring
      exact le_of_mul_le_mul_right h3 hpos
  -- approximate eigenvectors at the top of the numerical range
  have happrox : ∀ n : ℕ, ∃ w : MassSpace, ⟪w, oneL⟫_ℝ = 0 ∧ ‖w‖ = 1 ∧
      M - 1 / ((n : ℝ) + 1) < ⟪resolvent w, w⟫_ℝ := by
    intro n
    have hlt' : M - 1 / ((n : ℝ) + 1) < M := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hlt'
    exact ⟨w, hw.1, hw.2, hlt⟩
  choose w hw0 hw1 hw2 using happrox
  have hdef : Tendsto (fun n => ‖resolvent (w n) - M • w n‖) atTop (𝓝 0) := by
    have hsq : ∀ n, ‖resolvent (w n) - M • w n‖ ^ 2 ≤ M * (1 / ((n : ℝ) + 1)) := by
      intro n
      have e : ‖resolvent (w n) - M • w n‖ ^ 2 =
          ‖resolvent (w n)‖ ^ 2 - 2 * M * ⟪resolvent (w n), w n⟫_ℝ + M ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
          real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
          real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hw1,
          real_inner_comm (w n) (resolvent (w n))]
        ring
      have k := hkey (w n) (hw0 n)
      have h2 := hw2 n
      rw [e]
      nlinarith
    have h2 : Tendsto (fun n => ‖resolvent (w n) - M • w n‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => sq_nonneg _) hsq ?_
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul M
    have h3 := h2.sqrt
    rw [Real.sqrt_zero] at h3
    exact Filter.Tendsto.congr (fun n => Real.sqrt_sq (norm_nonneg _)) h3
  obtain ⟨x, hx0, hxeig, hxprim⟩ :=
    exists_primitive_eigenvector_of_approx_eigen_above_half hM_half w hw1 hdef hw0
  exact hx0 (h M x hM_half hxprim hxeig)

/-! ## The spectral Riemann criterion -/

/-- **RH ⟺ the arithmetic resolvent has no primitive eigenvector with eigenvalue above `1/2`.** -/
theorem riemannHypothesis_iff_no_primitive_bound_state :
    RiemannHypothesis ↔
      ∀ (μ : ℝ) (w : MassSpace), 1 / 2 < μ → ⟪w, oneL⟫_ℝ = 0 → resolvent w = μ • w → w = 0 := by
  rw [riemannHypothesis_iff_resolventHalfBound]
  exact ⟨fun hR μ w hμ hw heig => eq_zero_of_primitive_eigenvector_of_resolventHalfBound hR hμ hw heig,
    resolventHalfBound_of_no_primitive_bound_state⟩

/-- **RH fails ⟺ a primitive bound state of the arithmetic resolvent exists above `1/2`.** -/
theorem not_riemannHypothesis_iff_exists_primitive_bound_state :
    ¬ RiemannHypothesis ↔
      ∃ (μ : ℝ) (w : MassSpace), 1 / 2 < μ ∧ w ≠ 0 ∧ ⟪w, oneL⟫_ℝ = 0 ∧ resolvent w = μ • w := by
  rw [riemannHypothesis_iff_no_primitive_bound_state]
  constructor
  · intro h
    simp only [not_forall] at h
    obtain ⟨μ, w, hμ, hw, heig, hne⟩ := h
    exact ⟨μ, w, hμ, hne, hw, heig⟩
  · rintro ⟨μ, w, hμ, hne, hw, heig⟩ h
    exact hne (h μ w hμ hw heig)

/-- **Primitive bound states are spectral points above the threshold**, hence subject to the
discreteness laws: finitely many levels in `[1/2+ε, 1]`, finite-dimensional eigenspaces. -/
theorem mem_spectrum_of_primitive_bound_state {μ : ℝ} {w : MassSpace} (hw0 : w ≠ 0)
    (heig : resolvent w = μ • w) : μ ∈ spectrum ℝ resolvent :=
  mem_spectrum_of_eigenvector hw0 heig

end RHTower.CHMDPolar
