import GaloisForLFunctions.RHTower.DeckConstantCuspidalOrthogonal

/-!
# `C²` profiles and `V_∞` vectors generate the Eisenstein space

* `E(·|ψ, ρ(-1)v) = E(·|ψ, v)` for `T`-fixed `v` (`incEis_deckRho_neg_one`): the rows `±(c, d)` give
  matrices differing by `-1` up to a power of `T`.  Hence `E(·|ψ, v) = E(·|ψ, P v)` with
  `P v = (v + ρ(-1) v)/2 ∈ V_∞` (`incEisL2_cuspProj`).
* On profiles supported in a fixed `[a, b] ⊂ (0, ∞)` the map `ψ ↦ E(·|ψ, v)` is Lipschitz for the
  supremum norm (`exists_norm_incEisL2_sub_le`): on `𝒟` only a fixed finite set of rows contributes.
* Mollification approximates every continuous profile uniformly by `C^∞` profiles with slightly
  larger support (`exists_contDiff_approx`).

So the closed span `eisSpace` of the series `E(·|ψ, v)`, `ψ ∈ C²`, `v ∈ V_∞`, contains every
incomplete Eisenstein series (`incEisL2_mem_eisSpace`), and the cuspidal carrier is its orthogonal
complement in the central space (`mem_cuspidalL2Closure_iff_eisSpace`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Metric EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate Pointwise

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## Reduction to `V_∞` -/

theorem deckRho_neg_one_comm (A : SL(2, ℤ)) (v : DeckSpace N) :
    deckRho N A (deckRho N (-1) v) = deckRho N (-1) (deckRho N A v) := by
  rw [← deckRho_mul, ← deckRho_mul, mul_neg_one, neg_one_mul]

theorem deckRho_neg_one_neg_one (v : DeckSpace N) : deckRho N (-1) (deckRho N (-1) v) = v := by
  rw [← deckRho_mul, neg_one_mul, neg_neg, deckRho_one]

theorem eisTerm_gammaSetNeg (ψ : ℝ → ℂ) {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v)
    (p : gammaSet 1 1 0) (z : ℍ) :
    eisTerm ψ (deckRho N (-1) v) (gammaSetNeg p) z = eisTerm ψ v p z := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix (gammaSetNeg p))
    (-gammaSetMatrix p) (by simp) (by simp)
  unfold eisTerm
  have him : (gammaSetMatrix (gammaSetNeg p) • z).im = (gammaSetMatrix p • z).im := by
    rw [hn, mul_smul, im_T_zpow_smul, SL_neg_smul]
  rw [him]
  congr 1
  refine symm_eq_of_apply_eq ?_
  rw [hn, deckRho_mul, show -gammaSetMatrix p = -1 * gammaSetMatrix p by rw [neg_one_mul],
    deckRho_mul, LinearIsometryEquiv.apply_symm_apply, deckRho_neg_one_comm, deckRho_T_zpow hv]

theorem incEis_deckRho_neg_one (ψ : ℝ → ℂ) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) (z : ℍ) :
    incEis ψ (deckRho N (-1) v) z = incEis ψ v z := by
  unfold incEis
  rw [← (Function.Involutive.toPerm gammaSetNeg gammaSetNeg_gammaSetNeg).tsum_eq
    (fun p => eisTerm ψ (deckRho N (-1) v) p z)]
  exact tsum_congr fun p => eisTerm_gammaSetNeg ψ hv p z

theorem incEis_add_smul (ψ : HeightProfile) (a b : ℂ) (v w : DeckSpace N) (z : ℍ) :
    incEis ψ.toFun (a • v + b • w) z = a • incEis ψ.toFun v z + b • incEis ψ.toFun w z := by
  obtain ⟨S, hS⟩ := exists_finset_profile_eq_zero ψ.lower_pos ψ.eq_zero_of_lt
    (isCompact_singleton (x := z))
  have hS' : ∀ p ∉ S, ψ.toFun (gammaSetMatrix p • z).im = 0 := fun p hp => hS z rfl p hp
  rw [incEis_eq_sum hS', incEis_eq_sum hS', incEis_eq_sum hS', Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [eisTerm]
  rw [map_add, map_smul, map_smul, smul_add, smul_comm (ψ.toFun _) a, smul_comm (ψ.toFun _) b]

/-- The projection `v ↦ (v + ρ(-1) v)/2` onto the `-1`-fixed vectors. -/
def cuspProj (v : DeckSpace N) : DeckSpace N := (1 / 2 : ℂ) • (v + deckRho N (-1) v)

theorem isCuspVec_cuspProj {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) :
    IsCuspVec (cuspProj v) := by
  constructor
  · rw [cuspProj, map_smul, map_add, deckRho_neg_one_comm, hv]
  · rw [cuspProj, map_smul, map_add, deckRho_neg_one_neg_one, add_comm]

theorem incEis_cuspProj (ψ : HeightProfile) {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v)
    (z : ℍ) : incEis ψ.toFun (cuspProj v) z = incEis ψ.toFun v z := by
  rw [cuspProj, smul_add, incEis_add_smul, incEis_deckRho_neg_one _ hv, ← add_smul]
  norm_num

theorem incEisL2_cuspProj (ψ : HeightProfile) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) : incEisL2 ψ (cuspProj v) = incEisL2 ψ v :=
  toDeckL2_congr _ _ (Eventually.of_forall fun z => incEis_cuspProj ψ hv z)

/-! ## Lipschitz dependence on the profile -/

theorem exists_norm_incEisL2_sub_le {a b : ℝ} (ha : 0 < a) :
    ∃ C, 0 ≤ C ∧ ∀ (ψ ψ' : HeightProfile), a ≤ ψ.lower → ψ.upper ≤ b → a ≤ ψ'.lower →
      ψ'.upper ≤ b → ∀ δ, 0 ≤ δ → (∀ y, ‖ψ.toFun y - ψ'.toFun y‖ ≤ δ) → ∀ v : DeckSpace N,
        ‖incEisL2 ψ v - incEisL2 ψ' v‖ ≤ C * (δ * ‖v‖) := by
  set Y : ℝ := max b a⁻¹
  have hK : IsCompact {z : ℍ | z ∈ fd ∧ z.im ≤ Y} :=
    _root_.RHTower.D4BMModularCore.truncated_cell_compact Y
  set S := (finite_rows_im_ge hK ha).toFinset
  refine ⟨(measureUnivNNReal (cellMeasure : Measure ℍ) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * S.card,
    by positivity, fun ψ ψ' h1 h2 h3 h4 δ hδ hψ v => ?_⟩
  have hvan : ∀ χ : HeightProfile, a ≤ χ.lower → ∀ z, z ∈ fd → z.im ≤ Y → ∀ p ∉ S,
      χ.toFun (gammaSetMatrix p • z).im = 0 := fun χ hχ z hz hzY p hp => by
    refine χ.eq_zero_of_lt _ (lt_of_lt_of_le ?_ hχ)
    by_contra h
    exact hp ((finite_rows_im_ge hK ha).mem_toFinset.2 ⟨z, ⟨hz, hzY⟩, not_lt.1 h⟩)
  have hcap : ∀ χ : HeightProfile, a ≤ χ.lower → χ.upper ≤ b → χ.cap ≤ Y := fun χ hχa hχb =>
    max_le_max hχb (inv_anti₀ ha hχa)
  have hpt : ∀ z ∈ fd, ‖incEis ψ.toFun v z - incEis ψ'.toFun v z‖ ≤ S.card * (δ * ‖v‖) := by
    intro z hz
    by_cases hzY : z.im ≤ Y
    · rw [incEis_eq_sum (hvan ψ h1 z hz hzY), incEis_eq_sum (hvan ψ' h3 z hz hzY),
        ← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [eisTerm, eisTerm, ← sub_smul, norm_smul, LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (hψ _) (norm_nonneg _)
    · rw [ψ.incEis_eq_zero_of_im_gt v ((hcap ψ h1 h2).trans_lt (not_le.1 hzY)),
        ψ'.incEis_eq_zero_of_im_gt v ((hcap ψ' h3 h4).trans_lt (not_le.1 hzY)), sub_zero, norm_zero]
      positivity
  rw [mul_assoc]
  refine Lp.norm_le_of_ae_bound (by positivity) ?_
  filter_upwards [Lp.coeFn_sub (incEisL2 ψ v) (incEisL2 ψ' v), incEisL2_coeFn ψ v,
    incEisL2_coeFn ψ' v, (ae_restrict_iff' isClosed_fd.measurableSet).2
      (Eventually.of_forall hpt)] with z h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3]
  exact h4

/-! ## Mollification -/

theorem exists_contDiff_approx (ψ : HeightProfile) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ' : HeightProfile, ContDiff ℝ 2 ψ'.toFun ∧ ψ.lower / 2 ≤ ψ'.lower ∧
      ψ'.upper ≤ ψ.upper + 1 ∧ ∀ y, ‖ψ'.toFun y - ψ.toFun y‖ ≤ ε := by
  have hcs : HasCompactSupport ψ.toFun :=
    HasCompactSupport.intro isCompact_Icc fun y hy => ψ.eq_zero_of_not_mem_Icc hy
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1
    (hcs.uniformContinuous_of_continuous ψ.continuous) ε hε
  set r : ℝ := min δ (min (ψ.lower / 2) 1)
  have hr : 0 < r := lt_min hδ (lt_min (half_pos ψ.lower_pos) one_pos)
  let φ : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set f : ℝ → ℂ := convolution (φ.normed volume) ψ.toFun (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hf : ContDiff ℝ 2 f := by
    have h := (φ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ.contDiff_normed (n := 2)) (μ := volume)
      ψ.continuous.locallyIntegrable
    exact_mod_cast h
  have hsupp : ∀ y, f y ≠ 0 → ψ.lower - r < y ∧ y < ψ.upper + r := fun y hy => by
    have h := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
      (f := φ.normed volume) (g := ψ.toFun) hy
    rw [φ.support_normed_eq] at h
    obtain ⟨u, hu, t, ht, rfl⟩ := h
    have hu' : |u| < r := by simpa using hu
    have ht' : t ∈ Icc ψ.lower ψ.upper := by
      by_contra h'
      exact ht (ψ.eq_zero_of_not_mem_Icc h')
    constructor <;> linarith [abs_lt.1 hu', ht'.1, ht'.2]
  have hr2 : r ≤ ψ.lower / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨⟨f, ψ.lower - r, ψ.upper + r, by linarith [ψ.lower_pos], by linarith [ψ.lower_le_upper],
    hf.continuous, fun y hy => ?_, fun y hy => ?_⟩, hf, by simp; linarith, by simp; linarith,
    fun y => ?_⟩
  · by_contra h; linarith [(hsupp y h).1]
  · by_contra h; linarith [(hsupp y h).2]
  · rw [← dist_eq_norm]
    refine φ.dist_normed_convolution_le ψ.continuous.aestronglyMeasurable fun x hx => ?_
    exact (hδε (lt_of_lt_of_le (mem_ball.1 hx) (min_le_left _ _))).le

/-! ## The Eisenstein space -/

/-- Incomplete Eisenstein series with `C²` profiles and vectors in `V_∞`. -/
def eisGen (N : ℕ) : Set (DeckL2 N) :=
  {f | ∃ ψ : HeightProfile, ContDiff ℝ 2 ψ.toFun ∧ ∃ v, IsCuspVec v ∧ f = incEisL2 ψ v}

/-- **The Eisenstein space**: the closed span of the incomplete Eisenstein series. -/
def eisSpace (N : ℕ) : Submodule ℂ (DeckL2 N) := (Submodule.span ℂ (eisGen N)).topologicalClosure

theorem eisGen_subset_eisSpace : eisGen N ⊆ eisSpace N := fun _ hf =>
  Submodule.le_topologicalClosure _ (Submodule.subset_span hf)

theorem isClosed_eisSpace : IsClosed (eisSpace N : Set (DeckL2 N)) :=
  Submodule.isClosed_topologicalClosure _

/-- Every incomplete Eisenstein series lies in the Eisenstein space. -/
theorem incEisL2_mem_eisSpace (ψ : HeightProfile) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) : incEisL2 ψ v ∈ eisSpace N := by
  rw [← incEisL2_cuspProj ψ hv]
  set w := cuspProj v
  have hw := isCuspVec_cuspProj hv
  obtain ⟨C, hC0, hC⟩ := exists_norm_incEisL2_sub_le (N := N) (a := ψ.lower / 2) (b := ψ.upper + 1)
    (half_pos ψ.lower_pos)
  rw [← SetLike.mem_coe, ← isClosed_eisSpace.closure_eq]
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  set δ : ℝ := ε / (2 * ((C + 1) * (‖w‖ + 1)))
  have hδ : 0 < δ := by positivity
  obtain ⟨ψ', hψ', hl, hu, happ⟩ := exists_contDiff_approx ψ hδ
  refine ⟨incEisL2 ψ' w, eisGen_subset_eisSpace ⟨ψ', hψ', w, hw, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have h := hC ψ ψ' (half_le_self ψ.lower_pos.le) (by linarith) hl hu δ hδ.le
    (fun y => by rw [norm_sub_rev]; exact happ y) w
  calc ‖incEisL2 ψ w - incEisL2 ψ' w‖ ≤ C * (δ * ‖w‖) := h
    _ ≤ (C + 1) * (δ * (‖w‖ + 1)) := by gcongr <;> linarith
    _ = ε / 2 := by simp only [δ]; field_simp
    _ < ε := half_lt_self hε

theorem eisSpace_le_deckCentralFixedL2 : eisSpace N ≤ deckCentralFixedL2 N := by
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨ψ, _, v, hv, rfl⟩
    exact incEisL2_mem_deckCentralFixedL2 ψ hv.1
  · exact ContinuousLinearMap.isClosed_ker _

/-- **The cuspidal carrier is the orthogonal complement of the Eisenstein space** in the central
space. -/
theorem mem_cuspidalL2Closure_iff_eisSpace (f : DeckL2 N) :
    f ∈ cuspidalL2Closure N ↔ f ∈ deckCentralFixedL2 N ∧ ∀ g ∈ eisSpace N, ⟪g, f⟫_ℂ = 0 := by
  constructor
  · intro hf
    refine ⟨cuspidalL2Closure_le_deckCentralFixedL2 hf, fun g hg => ?_⟩
    have hclosed : IsClosed {g : DeckL2 N | ⟪g, f⟫_ℂ = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    set Z : Submodule ℂ (DeckL2 N) :=
      { carrier := {g | ⟪g, f⟫_ℂ = 0}
        add_mem' := fun ha hb => by simp only [mem_setOf_eq, inner_add_left] at *; rw [ha, hb, add_zero]
        zero_mem' := by simp
        smul_mem' := fun c x hx => by simp only [mem_setOf_eq, inner_smul_left] at *; rw [hx, mul_zero] }
    have hle : eisSpace N ≤ Z := by
      refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hclosed
      rintro _ ⟨ψ, _, v, hv, rfl⟩
      exact inner_incEisL2_eq_zero_of_mem ψ hv.1 hf
    exact hle hg
  · rintro ⟨hc, horth⟩
    exact mem_cuspidalL2Closure_of_forall_inner_incEisL2 hc fun ψ v hv =>
      horth _ (incEisL2_mem_eisSpace ψ hv)

end

end GaloisForLFunctions.RHTower.DeckPointPair
