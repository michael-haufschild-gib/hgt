import GaloisForLFunctions.RHTower.CHMDReflectionSymmetry

/-!
# The odd sector detects the Riemann hypothesis

The arithmetic resolvent `R` commutes with the reflection `J`, so the odd sector `{w : Jw = −w}` is
a closed `R`-invariant subspace. The corpus odd Dirichlet–Poincaré criterion (RH ⟺ Doob energy `≥ 0`
on odd compact tests) extends by density to all graph vectors with odd source, and the generic
invariant-subspace dictionary (energy `≥ 0` ⟺ `R ≤ 1/2` on the subspace ⟺ no eigenvector above
`1/2` in the subspace) then gives

`RH ⟺ R has no odd eigenvector with eigenvalue above 1/2`.

Every eigenvector of `R` splits into an even and an odd eigenvector, so the failure of RH is always
witnessed in the odd sector: the odd part of a primitive bound state above `1/2` cannot vanish for
all of them.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## The generic invariant-subspace dictionary -/

/-- A subspace of the mass space invariant under the arithmetic resolvent. -/
def ResolventInvariant (V : Submodule ℝ MassSpace) : Prop := ∀ w ∈ V, resolvent w ∈ V

theorem half_bound_on_of_energy {V : Submodule ℝ MassSpace} (hV : ResolventInvariant V)
    (hE : ∀ p : SourceGraph, p.val.fst ∈ V → 0 ≤ sourceEnergy p) :
    ∀ w ∈ V, ⟪resolvent w, w⟫_ℝ ≤ (1 / 2) * ‖w‖ ^ 2 := by
  intro w hw
  have hE' := hE (rieszLift w) (by show resolvent w ∈ V; exact hV w hw)
  rw [sourceEnergy_rieszLift] at hE'
  have h1 : ⟪resolvent w, w⟫_ℝ = ‖rieszLift w‖ ^ 2 := inner_resolvent_self w
  have h2 : ‖rieszLift w‖ ^ 2 = ⟪w, resolvent w⟫_ℝ := graph_norm_sq_rieszLift w
  have h3 : ‖resolvent w‖ ^ 2 ≤ (1 / 2) * ‖rieszLift w‖ ^ 2 := by linarith
  have h4 : ‖rieszLift w‖ ^ 2 ≤ ‖resolvent w‖ * ‖w‖ := by
    rw [h2]
    exact (real_inner_le_norm _ _).trans_eq (mul_comm _ _)
  rw [h1]
  exact sq_le_half_sq h4 h3

theorem energy_nonneg_on_of_half_bound {V : Submodule ℝ MassSpace}
    (h : ∀ w ∈ V, ⟪resolvent w, w⟫_ℝ ≤ (1 / 2) * ‖w‖ ^ 2) (p : SourceGraph) (hp : p.val.fst ∈ V) :
    0 ≤ sourceEnergy p := by
  have h1 := h p.val.fst hp
  have h2 : ‖p.val.fst‖ ^ 2 ≤ ‖rieszLift p.val.fst‖ * ‖p‖ := by
    rw [← real_inner_self_eq_norm_sq, ← inner_rieszLift]
    exact real_inner_le_norm _ _
  have h3 : ‖rieszLift p.val.fst‖ ^ 2 ≤ (1 / 2) * ‖p.val.fst‖ ^ 2 := by
    rw [← inner_resolvent_self]
    exact h1
  have h4 := sq_le_half_sq h2 h3
  rw [sourceEnergy_eq_graph_sub]
  linarith

theorem eq_zero_of_eigenvector_of_half_bound {V : Submodule ℝ MassSpace}
    (h : ∀ w ∈ V, ⟪resolvent w, w⟫_ℝ ≤ (1 / 2) * ‖w‖ ^ 2) {μ : ℝ} (hμ : 1 / 2 < μ) {w : MassSpace}
    (hw : w ∈ V) (heig : resolvent w = μ • w) : w = 0 := by
  by_contra h0
  have h1 := h w hw
  rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq] at h1
  have hpos : 0 < ‖w‖ ^ 2 := by
    have := norm_pos_iff.mpr h0
    positivity
  nlinarith

/-- Weak limits of unit approximate eigenvectors above `1/2` lying in a closed subspace are
eigenvectors in that subspace. -/
theorem exists_eigenvector_mem_of_approx_eigen_above_half {V : Submodule ℝ MassSpace}
    (hclosed : IsClosed (V : Set MassSpace)) {μ : ℝ} (hμ : 1 / 2 < μ) (w : ℕ → MassSpace)
    (hw1 : ∀ n, ‖w n‖ = 1) (hw : Tendsto (fun n => ‖resolvent (w n) - μ • w n‖) atTop (𝓝 0))
    (hmem : ∀ n, w n ∈ V) : ∃ x ∈ V, x ≠ 0 ∧ resolvent x = μ • x := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology MassSpace := Lp.SecondCountableTopology
  haveI : CompleteSpace V := hclosed.completeSpace_coe
  obtain ⟨x, φ, hφ, hweak⟩ := exists_real_weak_subseq w 1 fun n => (hw1 n).le
  have hw' : Tendsto (fun n => ‖resolvent (w (φ n)) - μ • w (φ n)‖) atTop (𝓝 0) :=
    hw.comp hφ.tendsto_atTop
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [← V.orthogonal_orthogonal, Submodule.mem_orthogonal']
    intro k hk
    have h0 : Tendsto (fun n => ⟪w (φ n), k⟫_ℝ) atTop (𝓝 0) := by
      have : ∀ n, ⟪w (φ n), k⟫_ℝ = 0 := fun n => Submodule.inner_right_of_mem_orthogonal (hmem _) hk
      simp only [this]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hweak k) h0
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

/-- On a closed invariant subspace, the absence of eigenvectors above `1/2` forces `R ≤ 1/2`. -/
theorem half_bound_on_of_no_eigenvector {V : Submodule ℝ MassSpace} (hV : ResolventInvariant V)
    (hclosed : IsClosed (V : Set MassSpace))
    (h : ∀ (μ : ℝ) (w : MassSpace), 1 / 2 < μ → w ∈ V → resolvent w = μ • w → w = 0) :
    ∀ w ∈ V, ⟪resolvent w, w⟫_ℝ ≤ (1 / 2) * ‖w‖ ^ 2 := by
  by_contra hno
  simp only [not_forall, not_le] at hno
  obtain ⟨w₀, hw₀, hlt⟩ := hno
  have hw₀ne : w₀ ≠ 0 := by
    rintro rfl
    simp at hlt
  set P : Set MassSpace := {w | w ∈ V ∧ ‖w‖ = 1} with hP
  set Sset : Set ℝ := (fun w => ⟪resolvent w, w⟫_ℝ) '' P with hSset
  have hnorm_mem : ∀ w : MassSpace, w ∈ V → w ≠ 0 → ‖w‖⁻¹ • w ∈ P := by
    intro w hw hw0
    exact ⟨V.smul_mem _ hw, norm_smul_inv_norm hw0⟩
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
  have hMb : ∀ w : MassSpace, w ∈ V → ⟪resolvent w, w⟫_ℝ ≤ M * ‖w‖ ^ 2 := by
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
  have hkey : ∀ w : MassSpace, w ∈ V → ‖resolvent w‖ ^ 2 ≤ M * ⟪resolvent w, w⟫_ℝ := by
    intro w hw
    have h1 := inner_resolvent_sq_le w (resolvent w)
    have h2 := hMb (resolvent w) (hV w hw)
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
  have happrox : ∀ n : ℕ, ∃ w : MassSpace, w ∈ V ∧ ‖w‖ = 1 ∧
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
  obtain ⟨x, hxV, hx0, hxeig⟩ :=
    exists_eigenvector_mem_of_approx_eigen_above_half hclosed hM_half w hw1 hdef hw0
  exact hx0 (h M x hM_half hxV hxeig)

/-! ## The odd sector -/

/-- The operator `J + 1`, whose kernel is the odd sector. -/
def oddOp : MassSpace →L[ℝ] MassSpace :=
  reflectMass.toContinuousLinearMap + ContinuousLinearMap.id ℝ MassSpace

/-- The odd sector `{w : Jw = −w}`. -/
def oddSector : Submodule ℝ MassSpace := LinearMap.ker (oddOp : MassSpace →ₗ[ℝ] MassSpace)

theorem mem_oddSector {w : MassSpace} : w ∈ oddSector ↔ reflectMass w = -w := by
  unfold oddSector
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  change reflectMass w + w = 0 ↔ _
  rw [add_eq_zero_iff_eq_neg]

theorem isClosed_oddSector : IsClosed (oddSector : Set MassSpace) := oddOp.isClosed_ker

theorem resolventInvariant_oddSector : ResolventInvariant oddSector := by
  intro w hw
  rw [mem_oddSector] at hw ⊢
  rw [← resolvent_reflectMass, hw, map_neg]

/-! ## Odd compact tests -/

theorem reflectMass_compactLift_fst (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    reflectMass (compactLift v hv hvc).val.fst =
      (compactLift (fun x => v (-x)) (hv.comp contDiff_neg)
        (hvc.comp_homeomorph (Homeomorph.neg ℝ))).val.fst := by
  rw [← reflectGraph_fst, reflectGraph_compactLift]

theorem compactLift_fst_mem_oddSector {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) : (compactLift v hv hvc).val.fst ∈ oddSector := by
  rw [mem_oddSector, reflectMass_compactLift_fst, Lp.ext_iff]
  have h1 := compactLift_source_ae (fun x => v (-x)) (hv.comp contDiff_neg)
    (hvc.comp_homeomorph (Homeomorph.neg ℝ))
  have h2 := Lp.coeFn_neg (compactLift v hv hvc).val.fst
  have h3 := compactLift_source_ae v hv hvc
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx2, Pi.neg_apply, hx3, hodd]

/-- The odd part of a compact test is an odd compact test. -/
theorem oddPart_compactLift (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    (1 / 2 : ℝ) • (compactLift v hv hvc - reflectGraph (compactLift v hv hvc)) =
      compactLift (fun x => (1 / 2) * (v x - v (-x)))
        (contDiff_const.mul (hv.sub (hv.comp contDiff_neg)))
        ((hvc.sub (hvc.comp_homeomorph (Homeomorph.neg ℝ))).mul_left) := by
  apply source_projection_injective
  show ((1 / 2 : ℝ) • (compactLift v hv hvc - reflectGraph (compactLift v hv hvc))).val.fst =
    (compactLift (fun x => (1 / 2) * (v x - v (-x))) _ _).val.fst
  change (1 / 2 : ℝ) • ((compactLift v hv hvc).val.fst - (reflectGraph (compactLift v hv hvc)).val.fst) = _
  rw [reflectGraph_fst, reflectMass_compactLift_fst, Lp.ext_iff]
  have h1 := Lp.coeFn_smul (1 / 2 : ℝ) ((compactLift v hv hvc).val.fst -
    (compactLift (fun x => v (-x)) (hv.comp contDiff_neg) (hvc.comp_homeomorph (Homeomorph.neg ℝ))).val.fst)
  have h2 := Lp.coeFn_sub (compactLift v hv hvc).val.fst
    (compactLift (fun x => v (-x)) (hv.comp contDiff_neg) (hvc.comp_homeomorph (Homeomorph.neg ℝ))).val.fst
  have h3 := compactLift_source_ae v hv hvc
  have h4 := compactLift_source_ae (fun x => v (-x)) (hv.comp contDiff_neg)
    (hvc.comp_homeomorph (Homeomorph.neg ℝ))
  have h5 := compactLift_source_ae (fun x => (1 / 2) * (v x - v (-x)))
    (contDiff_const.mul (hv.sub (hv.comp contDiff_neg)))
    ((hvc.sub (hvc.comp_homeomorph (Homeomorph.neg ℝ))).mul_left)
  filter_upwards [h1, h2, h3, h4, h5] with x hx1 hx2 hx3 hx4 hx5
  rw [hx1, Pi.smul_apply, hx2, Pi.sub_apply, hx3, hx4, hx5, smul_eq_mul]

/-- A graph vector with odd source is reversed by the graph reflection. -/
theorem reflectGraph_eq_neg_of_odd {p : SourceGraph} (hp : p.val.fst ∈ oddSector) :
    reflectGraph p = -p := by
  apply source_projection_injective
  show (reflectGraph p).val.fst = (-p).val.fst
  rw [reflectGraph_fst, mem_oddSector.mp hp]
  rfl

/-! ## RH on the odd sector -/

theorem sourceEnergy_compactLift_nonneg_of_rh_odd (hRH : RiemannHypothesis) {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) :
    0 ≤ sourceEnergy (compactLift v hv hvc) := by
  have h := (riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare.mp hRH) v hv hvc hodd
  have h2 : phiDoobCoshMass (fun x => v x ^ 2) = ∫ x, v x ^ 2 ∂massMeasure :=
    phiDoobCoshMass_eq_integral_mass _
  rw [sourceEnergy_compactLift_eq]
  linarith

/-- **RH ⇒ nonnegative Doob energy on all graph vectors with odd source.** -/
theorem sourceEnergy_nonneg_of_rh_odd (hRH : RiemannHypothesis) (p : SourceGraph)
    (hp : p.val.fst ∈ oddSector) : 0 ≤ sourceEnergy p := by
  set Φ : SourceGraph → SourceGraph := fun q => (1 / 2 : ℝ) • (q - reflectGraph q) with hΦ
  have hΦc : Continuous Φ := by
    show Continuous fun q : SourceGraph => (1 / 2 : ℝ) • (q - reflectGraph q)
    exact (continuous_id.sub continuous_reflectGraph).const_smul (1 / 2 : ℝ)
  have hΦp : Φ p = p := by
    simp only [hΦ]
    rw [reflectGraph_eq_neg_of_odd hp, sub_neg_eq_add, ← two_smul ℝ p, smul_smul]
    norm_num
  have hclosed : IsClosed {q : SourceGraph | 0 ≤ sourceEnergy q} :=
    isClosed_le continuous_const continuous_sourceEnergy
  have hsub : Φ '' (compactTests : Set SourceGraph) ⊆ {q | 0 ≤ sourceEnergy q} := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨v, hv, hvc, rfl⟩ := hq
    show 0 ≤ sourceEnergy ((1 / 2 : ℝ) • (compactLift v hv hvc - reflectGraph (compactLift v hv hvc)))
    rw [oddPart_compactLift]
    exact sourceEnergy_compactLift_nonneg_of_rh_odd hRH _ _ fun x => by
      simp only [neg_neg]
      ring
  have hp' : p ∈ closure (Φ '' (compactTests : Set SourceGraph)) := by
    rw [← hΦp]
    exact mem_closure_image hΦc.continuousAt (by rw [dense_compactTests.closure_eq]; trivial)
  exact closure_minimal hsub hclosed hp'

theorem riemannHypothesis_of_odd_energy
    (hE : ∀ p : SourceGraph, p.val.fst ∈ oddSector → 0 ≤ sourceEnergy p) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare]
  intro v hv hvc hodd
  have h := hE (compactLift v hv hvc) (compactLift_fst_mem_oddSector hv hvc hodd)
  have h2 : phiDoobCoshMass (fun x => v x ^ 2) = ∫ x, v x ^ 2 ∂massMeasure :=
    phiDoobCoshMass_eq_integral_mass _
  rw [sourceEnergy_compactLift_eq] at h
  linarith

/-- **RH ⟺ the arithmetic resolvent is at most `1/2` on the odd sector.** -/
theorem riemannHypothesis_iff_odd_half_bound :
    RiemannHypothesis ↔ ∀ w ∈ oddSector, ⟪resolvent w, w⟫_ℝ ≤ (1 / 2) * ‖w‖ ^ 2 :=
  ⟨fun h => half_bound_on_of_energy resolventInvariant_oddSector (sourceEnergy_nonneg_of_rh_odd h),
   fun h => riemannHypothesis_of_odd_energy fun p hp => energy_nonneg_on_of_half_bound h p hp⟩

/-- **The odd sector detects RH: RH ⟺ no odd eigenvector of the arithmetic resolvent above `1/2`.** -/
theorem riemannHypothesis_iff_no_odd_bound_state :
    RiemannHypothesis ↔
      ∀ (μ : ℝ) (w : MassSpace), 1 / 2 < μ → reflectMass w = -w → resolvent w = μ • w → w = 0 := by
  rw [riemannHypothesis_iff_odd_half_bound]
  constructor
  · intro h μ w hμ hodd heig
    exact eq_zero_of_eigenvector_of_half_bound h hμ (mem_oddSector.mpr hodd) heig
  · intro h
    exact half_bound_on_of_no_eigenvector resolventInvariant_oddSector isClosed_oddSector
      fun μ w hμ hw heig => h μ w hμ (mem_oddSector.mp hw) heig

/-- **RH fails ⟺ an odd bound state above `1/2` exists.** -/
theorem not_riemannHypothesis_iff_exists_odd_bound_state :
    ¬ RiemannHypothesis ↔
      ∃ (μ : ℝ) (w : MassSpace), 1 / 2 < μ ∧ w ≠ 0 ∧ reflectMass w = -w ∧ resolvent w = μ • w := by
  rw [riemannHypothesis_iff_no_odd_bound_state]
  constructor
  · intro h
    simp only [not_forall] at h
    obtain ⟨μ, w, hμ, hodd, heig, hne⟩ := h
    exact ⟨μ, w, hμ, hne, hodd, heig⟩
  · rintro ⟨μ, w, hμ, hne, hodd, heig⟩ h
    exact hne (h μ w hμ hodd heig)

/-! ## Parity decomposition of eigenvectors -/

/-- The odd part of an eigenvector is an odd eigenvector. -/
theorem oddPart_eigenvector {μ : ℝ} {w : MassSpace} (heig : resolvent w = μ • w) :
    reflectMass ((1 / 2 : ℝ) • (w - reflectMass w)) = -((1 / 2 : ℝ) • (w - reflectMass w)) ∧
      resolvent ((1 / 2 : ℝ) • (w - reflectMass w)) = μ • ((1 / 2 : ℝ) • (w - reflectMass w)) := by
  constructor
  · rw [map_smul, map_sub, reflectMass_reflectMass, ← smul_neg, neg_sub]
  · rw [map_smul, map_sub, resolvent_reflectMass, heig, map_smul, ← smul_sub, smul_comm]

/-- The even part of an eigenvector is an even eigenvector. -/
theorem evenPart_eigenvector {μ : ℝ} {w : MassSpace} (heig : resolvent w = μ • w) :
    reflectMass ((1 / 2 : ℝ) • (w + reflectMass w)) = (1 / 2 : ℝ) • (w + reflectMass w) ∧
      resolvent ((1 / 2 : ℝ) • (w + reflectMass w)) = μ • ((1 / 2 : ℝ) • (w + reflectMass w)) := by
  constructor
  · rw [map_smul, map_add, reflectMass_reflectMass, add_comm]
  · rw [map_smul, map_add, resolvent_reflectMass, heig, map_smul, ← smul_add, smul_comm]

/-- Every primitive bound state forces an odd bound state: the odd sector witnesses every failure
of RH. -/
theorem exists_odd_bound_state_of_primitive_bound_state {μ : ℝ} {w : MassSpace} (hμ : 1 / 2 < μ)
    (hw0 : w ≠ 0) (hprim : ⟪w, oneL⟫_ℝ = 0) (heig : resolvent w = μ • w) :
    ∃ (μ' : ℝ) (w' : MassSpace), 1 / 2 < μ' ∧ w' ≠ 0 ∧ reflectMass w' = -w' ∧ resolvent w' = μ' • w' := by
  rw [← not_riemannHypothesis_iff_exists_odd_bound_state,
    not_riemannHypothesis_iff_exists_primitive_bound_state]
  exact ⟨μ, w, hμ, hw0, hprim, heig⟩

end RHTower.CHMDPolar
