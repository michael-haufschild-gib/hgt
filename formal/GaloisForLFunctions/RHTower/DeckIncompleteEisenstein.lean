import GaloisForLFunctions.RHTower.DeckCuspidalConstantTerm
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral
import GaloisForLFunctions.RHTower.EisensteinHoroballBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompactModularPeriodization

/-!
# Incomplete Eisenstein series on the finite deck

For a continuous height profile `ψ` vanishing outside `[a, b] ⊂ (0, ∞)` and a deck vector `v`
fixed by the translation `T`, the incomplete Eisenstein series is
`E(z | ψ, v) = Σ_{(c, d) coprime} ψ(Im M_{c,d} z) ρ(M_{c,d})⁻¹ v`,
where `M_{c,d} ∈ SL₂(ℤ)` has bottom row `(c, d)`.  Since `Im M_{c,d} z = y / |cz + d|²`, only
finitely many rows reach height `a` from a compact set, so `E` is locally a finite sum; it is
continuous, deck-equivariant, vanishes above height `max(b, 1/a)` and lies in finite-deck `L²`.

Unfolding along the translation strip: for continuous deck-equivariant `G`,
`∫_𝒟 ⟨E(z | ψ, v), G(z)⟩ dμ = 2 ∫_0^∞ y⁻² \bar ψ(y) ∫_0^1 ⟨v, G(x + iy)⟩ dx dy`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## Height profiles and the series -/

/-- A continuous complex profile vanishing outside `[lower, upper]`, with `0 < lower`. -/
structure HeightProfile where
  toFun : ℝ → ℂ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  continuous : Continuous toFun
  eq_zero_of_lt : ∀ y, y < lower → toFun y = 0
  eq_zero_of_gt : ∀ y, upper < y → toFun y = 0

/-- One term `ψ(Im M_{c,d} z) ρ(M_{c,d})⁻¹ v` of the incomplete Eisenstein series. -/
def eisTerm (ψ : ℝ → ℂ) (v : DeckSpace N) (p : gammaSet 1 1 0) (z : ℍ) : DeckSpace N :=
  ψ (gammaSetMatrix p • z).im • (deckRho N (gammaSetMatrix p)).symm v

/-- **The incomplete Eisenstein series** `E(z | ψ, v) = Σ_{(c,d)} ψ(Im M_{c,d} z) ρ(M_{c,d})⁻¹ v`. -/
def incEis (ψ : ℝ → ℂ) (v : DeckSpace N) (z : ℍ) : DeckSpace N :=
  ∑' p : gammaSet 1 1 0, eisTerm ψ v p z

theorem gammaSet_val_ne_zero (p : gammaSet 1 1 0) : p.1 ≠ 0 := by
  intro h
  have hp := (gammaSet_one_mem_iff 1 p.1).1 p.2
  rw [h] at hp
  simp at hp

theorem im_gammaSetMatrix_smul (p : gammaSet 1 1 0) (z : ℍ) :
    (gammaSetMatrix p • z).im =
      z.im / Complex.normSq (((p.1 0 : ℤ) : ℂ) * (z : ℂ) + ((p.1 1 : ℤ) : ℂ)) := by
  rw [ModularGroup.im_smul_eq_div_normSq, _root_.RHTower.denom_SL2Z]
  simp

/-- Rows lifting a point of a compact set to height at least `a > 0` form a finite set. -/
theorem finite_rows_im_ge {K : Set ℍ} (hK : IsCompact K) {a : ℝ} (ha : 0 < a) :
    {p : gammaSet 1 1 0 | ∃ z ∈ K, a ≤ (gammaSetMatrix p • z).im}.Finite := by
  obtain ⟨A, B, hB, hKs⟩ := subset_verticalStrip_of_isCompact hK
  obtain ⟨Y, hY⟩ : ∃ Y, ∀ z ∈ K, z.im ≤ Y := by
    obtain ⟨Y, hY⟩ := (hK.image continuous_im).bddAbove
    exact ⟨Y, fun z hz => hY ⟨z, hz, rfl⟩⟩
  have hr0 : 0 < r ⟨⟨A, B⟩, hB⟩ := r_pos _
  have hsub : (fun p : gammaSet 1 1 0 => p.1) ''
      {p : gammaSet 1 1 0 | ∃ z ∈ K, a ≤ (gammaSetMatrix p • z).im} ⊆
      Metric.closedBall (0 : Fin 2 → ℤ) (Real.sqrt (Y / a) / r ⟨⟨A, B⟩, hB⟩) := by
    rintro _ ⟨p, ⟨z, hz, hle⟩, rfl⟩
    rw [mem_closedBall_zero_iff, le_div_iff₀ hr0]
    have h1 := r_mul_max_le z (gammaSet_val_ne_zero p)
    have h2 := r_lower_bound_on_verticalStrip z hB (hKs hz)
    rw [im_gammaSetMatrix_smul] at hle
    set w : ℂ := ((p.1 0 : ℤ) : ℂ) * (z : ℂ) + ((p.1 1 : ℤ) : ℂ)
    have hw0 : 0 < Complex.normSq w := by
      have : w ≠ 0 := by
        intro h0
        have := r_pos z
        have h3 : r z * ‖p.1‖ ≤ 0 := by rw [h0, norm_zero] at h1; exact h1
        have h4 : 0 < ‖p.1‖ := norm_pos_iff.2 (gammaSet_val_ne_zero p)
        nlinarith
      exact Complex.normSq_pos.2 this
    have hn : Complex.normSq w ≤ Y / a := by
      rw [le_div_iff₀ ha]
      rw [le_div_iff₀ hw0] at hle
      nlinarith [hY z hz]
    have hw : ‖w‖ ≤ Real.sqrt (Y / a) := by
      rw [← Real.sqrt_sq (norm_nonneg w), ← Complex.normSq_eq_norm_sq]
      exact Real.sqrt_le_sqrt hn
    calc ‖p.1‖ * r ⟨⟨A, B⟩, hB⟩ ≤ ‖p.1‖ * r z := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = r z * ‖p.1‖ := mul_comm _ _
      _ ≤ ‖w‖ := h1
      _ ≤ _ := hw
  exact Set.Finite.of_finite_image
    ((isCompact_closedBall _ _).finite_of_discrete.subset hsub) Subtype.val_injective.injOn

variable {ψ : ℝ → ℂ} {a : ℝ}

/-- Outside a finite set of rows, the profile vanishes at every lifted height from a compact set. -/
theorem exists_finset_profile_eq_zero (ha : 0 < a) (hψa : ∀ y, y < a → ψ y = 0) {K : Set ℍ}
    (hK : IsCompact K) :
    ∃ S : Finset (gammaSet 1 1 0), ∀ z ∈ K, ∀ p ∉ S, ψ (gammaSetMatrix p • z).im = 0 := by
  refine ⟨(finite_rows_im_ge hK ha).toFinset, fun z hz p hp => hψa _ ?_⟩
  by_contra h
  exact hp ((finite_rows_im_ge hK ha).mem_toFinset.2 ⟨z, hz, not_lt.1 h⟩)

theorem eisTerm_eq_zero_of_profile {v : DeckSpace N} {p : gammaSet 1 1 0} {z : ℍ}
    (h : ψ (gammaSetMatrix p • z).im = 0) : eisTerm ψ v p z = 0 := by
  rw [eisTerm, h, zero_smul]

theorem incEis_eq_sum {v : DeckSpace N} {z : ℍ} {S : Finset (gammaSet 1 1 0)}
    (hS : ∀ p ∉ S, ψ (gammaSetMatrix p • z).im = 0) :
    incEis ψ v z = ∑ p ∈ S, eisTerm ψ v p z :=
  tsum_eq_sum fun p hp => eisTerm_eq_zero_of_profile (hS p hp)

theorem continuous_eisTerm (hψc : Continuous ψ) (v : DeckSpace N) (p : gammaSet 1 1 0) :
    Continuous (eisTerm ψ v p) :=
  (hψc.comp (continuous_im.comp (continuous_modular_smul _))).smul continuous_const

/-- **Continuity.** Near every point the series is a finite sum of continuous terms. -/
theorem continuous_incEis (hψc : Continuous ψ) (ha : 0 < a) (hψa : ∀ y, y < a → ψ y = 0)
    (v : DeckSpace N) : Continuous (incEis ψ v) := by
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  obtain ⟨S, hS⟩ := exists_finset_profile_eq_zero ha hψa (isCompact_closedBall z₀ 1)
  have heq : (fun z => ∑ p ∈ S, eisTerm ψ v p z) =ᶠ[𝓝 z₀] incEis ψ v := by
    filter_upwards [Metric.closedBall_mem_nhds z₀ one_pos] with z hz
    exact (incEis_eq_sum (hS z hz)).symm
  exact ((continuous_finsetSum S fun p _ => continuous_eisTerm hψc v p).continuousAt).congr heq

/-! ## Equivariance -/

theorem symm_eq_of_apply_eq {e : DeckSpace N ≃ₗᵢ[ℂ] DeckSpace N} {x y : DeckSpace N}
    (h : e y = x) : e.symm x = y := by
  rw [← h, LinearIsometryEquiv.symm_apply_apply]

theorem deckRho_T_zpow {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) (n : ℤ) :
    deckRho N (ModularGroup.T ^ n) v = v := by
  induction n using Int.induction_on with
  | zero => simpa using deckRho_one v
  | succ n ih => rw [zpow_add_one, deckRho_mul, hv, ih]
  | pred n ih =>
      rw [zpow_sub_one, deckRho_mul, deckRho_inv, symm_eq_of_apply_eq hv, ih]

theorem symm_deckRho_T_zpow {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) (n : ℤ) :
    (deckRho N (ModularGroup.T ^ n)).symm v = v :=
  symm_eq_of_apply_eq (deckRho_T_zpow hv n)

theorem im_T_zpow_smul (n : ℤ) (z : ℍ) : (ModularGroup.T ^ n • z).im = z.im := by
  rw [modular_T_zpow_smul, vadd_im]

/-- Reindexing a term along the right action of `A` on coprime rows. -/
theorem eisTerm_smul {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) (A : SL(2, ℤ))
    (p : gammaSet 1 1 0) (z : ℍ) :
    eisTerm ψ v p (A • z) = deckRho N A (eisTerm ψ v (gammaSetSelfEquiv A p) z) := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix p * A)
    (gammaSetMatrix (gammaSetSelfEquiv A p))
    (by rw [gammaSetMatrix_mul_apply_one, gammaSetMatrix_apply_one_zero, gammaSetSelfEquiv_apply_val])
    (by rw [gammaSetMatrix_mul_apply_one, gammaSetMatrix_apply_one_one, gammaSetSelfEquiv_apply_val])
  set M := gammaSetMatrix p
  set M' := gammaSetMatrix (gammaSetSelfEquiv A p)
  have him : (M • A • z).im = (M' • z).im := by
    rw [← mul_smul, hn, mul_smul, im_T_zpow_smul]
  have hvec : (deckRho N M).symm v = deckRho N A ((deckRho N M').symm v) := by
    refine symm_eq_of_apply_eq ?_
    rw [← deckRho_mul, hn, deckRho_mul, LinearIsometryEquiv.apply_symm_apply, deckRho_T_zpow hv]
  rw [eisTerm, eisTerm, him, hvec, map_smul]

/-- **Deck equivariance** `E(Az) = ρ(A) E(z)`. -/
theorem incEis_smul {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) (A : SL(2, ℤ))
    (z : ℍ) : incEis ψ v (A • z) = deckRho N A (incEis ψ v z) := by
  unfold incEis
  simp_rw [eisTerm_smul hv A _ z]
  rw [(gammaSetSelfEquiv A).tsum_eq (fun p => deckRho N A (eisTerm ψ v p z))]
  exact ((deckRho N A).toContinuousLinearEquiv.map_tsum).symm

theorem deckEquivariant_incEis {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) :
    deckEquivariant N (incEis ψ v) :=
  fun A z => incEis_smul hv A z

/-! ## Support and `L²` -/

/-- `Im M_{c,d} z ≤ 1/Im z` for `c ≠ 0`, and `= Im z` for `c = 0`. -/
theorem im_gammaSetMatrix_smul_cases (p : gammaSet 1 1 0) (z : ℍ) :
    (gammaSetMatrix p • z).im = z.im ∨ (gammaSetMatrix p • z).im ≤ z.im⁻¹ := by
  rw [im_gammaSetMatrix_smul, _root_.RHTower.normSq_int_mul_add]
  have hy := z.im_pos
  by_cases hc : p.1 0 = 0
  · left
    have hp := (gammaSet_one_mem_iff 1 p.1).1 p.2
    rw [hc, Int.gcd_zero_left] at hp
    have hd : ((p.1 1 : ℤ) : ℝ) ^ 2 = 1 := by
      have : (p.1 1).natAbs = 1 := hp
      have h2 : (p.1 1) ^ 2 = 1 := by
        rw [← Int.natAbs_sq, this]; norm_num
      exact_mod_cast h2
    rw [hc]
    simp [hd]
  · right
    have hc1 : (1 : ℝ) ≤ ((p.1 0 : ℤ) : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ (p.1 0) ^ 2 := by
        have := sq_pos_of_ne_zero hc
        omega
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((p.1 0 : ℤ) * z.im) ^ 2 +
      ((p.1 0 : ℤ) * z.re + (p.1 1 : ℤ)) ^ 2)]
    rw [inv_mul_eq_div, le_div_iff₀ hy]
    nlinarith [sq_nonneg (((p.1 0 : ℤ) : ℝ) * z.re + (p.1 1 : ℤ)), mul_pos hy hy]

/-- Every term vanishes above height `max(b, 1/a)`. -/
theorem profile_eq_zero_of_im_gt {b : ℝ} (ha : 0 < a) (hψa : ∀ y, y < a → ψ y = 0)
    (hψb : ∀ y, b < y → ψ y = 0) {z : ℍ} (hz : max b a⁻¹ < z.im) (p : gammaSet 1 1 0) :
    ψ (gammaSetMatrix p • z).im = 0 := by
  rcases im_gammaSetMatrix_smul_cases p z with h | h
  · rw [h]
    exact hψb _ (lt_of_le_of_lt (le_max_left _ _) hz)
  · refine hψa _ (lt_of_le_of_lt h ?_)
    have h1 : a⁻¹ < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    rw [inv_lt_comm₀ z.im_pos ha]
    exact h1

namespace HeightProfile

variable (ψ : HeightProfile)

/-- The height above which the series vanishes identically. -/
def cap : ℝ := max ψ.upper ψ.lower⁻¹

theorem incEis_eq_zero_of_im_gt (v : DeckSpace N) {z : ℍ} (hz : ψ.cap < z.im) :
    incEis ψ.toFun v z = 0 := by
  rw [incEis_eq_sum (S := ∅) fun p _ =>
    profile_eq_zero_of_im_gt ψ.lower_pos ψ.eq_zero_of_lt ψ.eq_zero_of_gt hz p]
  simp

theorem continuous_incEis (v : DeckSpace N) : Continuous (incEis ψ.toFun v) :=
  DeckPointPair.continuous_incEis ψ.continuous ψ.lower_pos ψ.eq_zero_of_lt v

/-- On `𝒟` all terms outside one finite set of rows vanish identically. -/
theorem exists_finset_fd :
    ∃ S : Finset (gammaSet 1 1 0), ∀ z ∈ fd, ∀ p ∉ S, ψ.toFun (gammaSetMatrix p • z).im = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_profile_eq_zero ψ.lower_pos ψ.eq_zero_of_lt
    (_root_.RHTower.D4BMModularCore.truncated_cell_compact ψ.cap)
  refine ⟨S, fun z hz p hp => ?_⟩
  by_cases hY : z.im ≤ ψ.cap
  · exact hS z ⟨hz, hY⟩ p hp
  · exact profile_eq_zero_of_im_gt ψ.lower_pos ψ.eq_zero_of_lt ψ.eq_zero_of_gt (not_le.1 hY) p

theorem exists_bound_fd (v : DeckSpace N) : ∃ C, ∀ z ∈ fd, ‖incEis ψ.toFun v z‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((_root_.RHTower.D4BMModularCore.truncated_cell_compact ψ.cap).image
    ((ψ.continuous_incEis v).norm)).bddAbove
  refine ⟨max C 0, fun z hz => ?_⟩
  by_cases hY : z.im ≤ ψ.cap
  · exact (hC ⟨z, ⟨hz, hY⟩, rfl⟩).trans (le_max_left _ _)
  · rw [ψ.incEis_eq_zero_of_im_gt v (not_le.1 hY), norm_zero]
    exact le_max_right _ _

theorem memLp_incEis (v : DeckSpace N) : MemLp (incEis ψ.toFun v) 2 cellMeasure := by
  obtain ⟨C, hC⟩ := ψ.exists_bound_fd v
  exact MemLp.of_bound (ψ.continuous_incEis v).aestronglyMeasurable C
    ((ae_restrict_iff' isClosed_fd.measurableSet).2 (Eventually.of_forall hC))

end HeightProfile

/-- The class of `E(· | ψ, v)` in finite-deck `L²`. -/
def incEisL2 (ψ : HeightProfile) (v : DeckSpace N) : DeckL2 N :=
  toDeckL2 (incEis ψ.toFun v) (ψ.memLp_incEis v)

theorem incEisL2_coeFn (ψ : HeightProfile) (v : DeckSpace N) :
    (incEisL2 ψ v : ℍ → DeckSpace N) =ᵐ[cellMeasure] incEis ψ.toFun v :=
  MemLp.coeFn_toLp (ψ.memLp_incEis v)

/-! ## Unfolding -/

section Unfold

variable {G : ℍ → DeckSpace N}

/-- The unfolded integrand `\bar ψ(Im w) ⟨v, G(w)⟩`. -/
def unfoldIntegrand (ψ : ℝ → ℂ) (v : DeckSpace N) (G : ℍ → DeckSpace N) (w : ℍ) : ℂ :=
  conj (ψ w.im) * ⟪v, G w⟫_ℂ

theorem inner_eisTerm (hGe : deckEquivariant N G) (v : DeckSpace N) (p : gammaSet 1 1 0)
    (z : ℍ) : ⟪eisTerm ψ v p z, G z⟫_ℂ = unfoldIntegrand ψ v G (gammaSetMatrix p • z) := by
  rw [eisTerm, inner_smul_left, unfoldIntegrand, hGe]
  congr 1
  rw [← (deckRho N (gammaSetMatrix p)).inner_map_map ((deckRho N (gammaSetMatrix p)).symm v) (G z),
    LinearIsometryEquiv.apply_symm_apply]

theorem unfoldIntegrand_T_zpow (hGe : deckEquivariant N G) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) (n : ℤ) (w : ℍ) :
    unfoldIntegrand ψ v G (ModularGroup.T ^ n • w) = unfoldIntegrand ψ v G w := by
  rw [unfoldIntegrand, unfoldIntegrand, im_T_zpow_smul, hGe]
  congr 1
  conv_lhs => rw [← deckRho_T_zpow hv n]
  exact (deckRho N (ModularGroup.T ^ n)).inner_map_map v (G w)

theorem continuous_unfoldIntegrand (hψc : Continuous ψ) (hGc : Continuous G) (v : DeckSpace N) :
    Continuous (unfoldIntegrand ψ v G) :=
  (Complex.continuous_conj.comp (hψc.comp continuous_im)).mul (continuous_const.inner hGc)

theorem unfoldIntegrand_eq_zero {v : DeckSpace N} {w : ℍ} (h : ψ w.im = 0) :
    unfoldIntegrand ψ v G w = 0 := by
  rw [unfoldIntegrand, h, map_zero, zero_mul]

/-- The translation strip meets the band `a ≤ Im w ≤ b` in a compact set. -/
theorem isCompact_stripBand {a b : ℝ} (ha : 0 < a) :
    IsCompact (UpperHalfPlane.coe ⁻¹' (Icc (0 : ℝ) 1 ×ℂ Icc a b)) :=
  isCompact_preimage_coe (isCompact_Icc.reProdIm isCompact_Icc) fun _ hw =>
    lt_of_lt_of_le ha hw.2.1

theorem integrableOn_modularStrip_unfoldIntegrand (ψ : HeightProfile) (hGc : Continuous G)
    (v : DeckSpace N) : IntegrableOn (unfoldIntegrand ψ.toFun v G) modularStrip volume := by
  refine IntegrableOn.of_forall_sdiff_eq_zero
    ((continuous_unfoldIntegrand ψ.continuous hGc v).continuousOn.integrableOn_compact
      (isCompact_stripBand (b := ψ.upper) ψ.lower_pos)) measurableSet_modularStrip ?_
  rintro w ⟨hw, hwK⟩
  refine unfoldIntegrand_eq_zero ?_
  by_contra hne
  apply hwK
  refine ⟨⟨hw.1, hw.2.le⟩, ?_, ?_⟩
  · by_contra h
    exact hne (ψ.eq_zero_of_lt _ (not_le.1 h))
  · by_contra h
    exact hne (ψ.eq_zero_of_gt _ (not_le.1 h))

theorem integrableOn_fd_unfoldIntegrand_smul (ψ : HeightProfile) (hGc : Continuous G)
    (v : DeckSpace N) (p : gammaSet 1 1 0) :
    IntegrableOn (fun z => unfoldIntegrand ψ.toFun v G (gammaSetMatrix p • z)) fd volume := by
  refine IntegrableOn.of_forall_sdiff_eq_zero
    (((continuous_unfoldIntegrand ψ.continuous hGc v).comp
      (continuous_modular_smul _)).continuousOn.integrableOn_compact
      (_root_.RHTower.D4BMModularCore.truncated_cell_compact ψ.cap))
    isClosed_fd.measurableSet ?_
  rintro z ⟨hz, hzK⟩
  have hY : ψ.cap < z.im := by
    by_contra h
    exact hzK ⟨hz, not_lt.1 h⟩
  exact unfoldIntegrand_eq_zero
    (profile_eq_zero_of_im_gt ψ.lower_pos ψ.eq_zero_of_lt ψ.eq_zero_of_gt hY p)

/-- **Unfolding.** For continuous deck-equivariant `G`,
`∫_𝒟 ⟨E(z | ψ, v), G(z)⟩ = 2 ∫_{strip} \bar ψ(Im w) ⟨v, G(w)⟩`. -/
theorem integral_inner_incEis (ψ : HeightProfile) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) (hGc : Continuous G) (hGe : deckEquivariant N G) :
    ∫ z in fd, ⟪incEis ψ.toFun v z, G z⟫_ℂ =
      2 * ∫ w in modularStrip, unfoldIntegrand ψ.toFun v G w := by
  obtain ⟨S, hS⟩ := ψ.exists_finset_fd
  have h1 : ∀ z ∈ fd, ⟪incEis ψ.toFun v z, G z⟫_ℂ =
      ∑ p ∈ S, unfoldIntegrand ψ.toFun v G (gammaSetMatrix p • z) := by
    intro z hz
    rw [incEis_eq_sum (hS z hz), sum_inner]
    exact Finset.sum_congr rfl fun p _ => inner_eisTerm hGe v p z
  rw [setIntegral_congr_fun isClosed_fd.measurableSet h1,
    integral_finsetSum S fun p _ => integrableOn_fd_unfoldIntegrand_smul ψ hGc v p,
    ← tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip _
      (unfoldIntegrand_T_zpow hGe hv) (integrableOn_modularStrip_unfoldIntegrand ψ hGc v)]
  refine (tsum_eq_sum fun p hp => ?_).symm
  exact setIntegral_eq_zero_of_forall_eq_zero fun z hz => unfoldIntegrand_eq_zero (hS z hz p hp)

/-- The horocycle average `∫_0^1 ⟨v, G(x + iy)⟩ dx`. -/
def horoAverage (v : DeckSpace N) (G : ℍ → DeckSpace N) (y : ℝ) : ℂ :=
  ∫ x in Ico (0 : ℝ) 1, ⟪v, G (ofComplex ⟨x, y⟩)⟫_ℂ

/-- **Unfolding, iterated form.**
`∫_𝒟 ⟨E(z | ψ, v), G(z)⟩ = 2 ∫_0^∞ y⁻² \bar ψ(y) ∫_0^1 ⟨v, G(x + iy)⟩ dx dy`. -/
theorem integral_inner_incEis_eq (ψ : HeightProfile) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) (hGc : Continuous G) (hGe : deckEquivariant N G) :
    ∫ z in fd, ⟪incEis ψ.toFun v z, G z⟫_ℂ =
      2 * ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ • (conj (ψ.toFun y) * horoAverage v G y) := by
  rw [integral_inner_incEis ψ hv hGc hGe, setIntegral_modularStrip_eq_iterated _
    (integrableOn_modularStrip_unfoldIntegrand ψ hGc v)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  congr 1
  rw [horoAverage, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  have him : 0 < (⟨x, y⟩ : ℂ).im := hy
  simp only [unfoldIntegrand]
  rw [ofComplex_apply_of_im_pos him]
  rfl

end Unfold

/-- The `L²` pairing with the class of a continuous deck-equivariant `G`, unfolded. -/
theorem inner_incEisL2 (ψ : HeightProfile) {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v)
    {g : DeckL2 N} {G : ℍ → DeckSpace N} (hg : (g : ℍ → DeckSpace N) =ᵐ[cellMeasure] G)
    (hGc : Continuous G) (hGe : deckEquivariant N G) :
    ⟪incEisL2 ψ v, g⟫_ℂ =
      2 * ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ • (conj (ψ.toFun y) * horoAverage v G y) := by
  rw [L2.inner_def, ← integral_inner_incEis_eq ψ hv hGc hGe]
  refine integral_congr_ae ?_
  filter_upwards [incEisL2_coeFn ψ v, hg] with z h1 h2
  rw [h1, h2]

/-! ## Point-pair images -/

section PointPair

/-- A point-pair ball controls the height ratio: `u(z, w) ≤ R ⇒ Im w < (2 + 4R) Im z`. -/
theorem im_lt_of_pairU_le {z w : ℍ} {R : ℝ} (h : pairU z w ≤ R) :
    w.im < (2 + 4 * R) * z.im := by
  have hz := z.im_pos
  have hw := w.im_pos
  have h1 : (z.im - w.im) ^ 2 ≤ dist (z : ℂ) w ^ 2 := by
    have : |z.im - w.im| ≤ dist (z : ℂ) w := by
      rw [Complex.dist_eq]
      simpa using Complex.abs_im_le_norm ((z : ℂ) - w)
    nlinarith [abs_nonneg (z.im - w.im), sq_abs (z.im - w.im)]
  have h2 : dist (z : ℂ) w ^ 2 = 4 * pairU z w * z.im * w.im := by
    unfold pairU
    field_simp
  have hd : (z.im - w.im) ^ 2 ≤ 4 * R * z.im * w.im := by
    nlinarith [mul_pos hz hw]
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_left hc hw.le, mul_pos hz hz]

/-- The height transform `ψ̃(t) = ∫_ℍ φ(u(i, w)) ψ(t Im w) dμ(w)`. -/
def heightTransform (φ : ℝ → ℝ) (ψ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ w : ℍ, ((φ (pairU UpperHalfPlane.I w) : ℝ) : ℂ) * ψ (t * w.im)

variable {φ : ℝ → ℝ} {R : ℝ}

theorem pairKernel_mul_eq_zero_of_not_mem (hφR : KernelSupport φ R) {z w : ℍ}
    (hw : w ∉ Metric.closedBall z (1 + 2 * R)) (c : ℂ) : ((φ (pairU z w) : ℝ) : ℂ) * c = 0 := by
  have : R < pairU z w := by
    by_contra h
    exact hw (Metric.mem_closedBall.2 (by rw [dist_comm]; exact dist_le_of_pairU_le (not_lt.1 h)))
  rw [hφR _ this]
  simp

theorem continuous_heightTransform (hφc : Continuous φ) (hφR : KernelSupport φ R)
    (hψc : Continuous ψ) : Continuous (heightTransform φ ψ) := by
  have h : heightTransform φ ψ = fun t => ∫ w in Metric.closedBall UpperHalfPlane.I (1 + 2 * R),
      ((φ (pairU UpperHalfPlane.I w) : ℝ) : ℂ) * ψ (t * w.im) := by
    funext t
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw =>
      pairKernel_mul_eq_zero_of_not_mem hφR hw _).symm
  rw [h]
  refine continuous_parametric_integral_of_continuous ?_ (isCompact_closedBall _ _)
  exact (Complex.continuous_ofReal.comp (hφc.comp ((continuous_pairU_right _).comp
    continuous_snd))).mul (hψc.comp (continuous_fst.mul (continuous_im.comp continuous_snd)))

/-- The height transform of a height profile is a height profile, supported in
`[a/(2+4R), b(2+4R)]`. -/
def HeightProfile.pointPair (ψ : HeightProfile) (hφc : Continuous φ) (hR : 0 ≤ R)
    (hφR : KernelSupport φ R) : HeightProfile where
  toFun := heightTransform φ ψ.toFun
  lower := ψ.lower / (2 + 4 * R)
  upper := ψ.upper * (2 + 4 * R)
  lower_pos := div_pos ψ.lower_pos (by linarith)
  lower_le_upper := by
    have h1 : ψ.lower / (2 + 4 * R) ≤ ψ.lower := div_le_self ψ.lower_pos.le (by linarith)
    have h2 : ψ.upper ≤ ψ.upper * (2 + 4 * R) :=
      le_mul_of_one_le_right (ψ.lower_pos.le.trans ψ.lower_le_upper) (by linarith)
    linarith [ψ.lower_le_upper]
  continuous := continuous_heightTransform hφc hφR ψ.continuous
  eq_zero_of_lt := fun t ht => by
    unfold heightTransform
    refine integral_eq_zero_of_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : pairU UpperHalfPlane.I w ≤ R
    · have h1 := im_lt_of_pairU_le hw
      rw [UpperHalfPlane.I_im, mul_one] at h1
      have hlt : t * w.im < ψ.lower := by
        rcases le_or_gt t 0 with h | h
        · nlinarith [w.im_pos, ψ.lower_pos]
        · have h2 : t * (2 + 4 * R) < ψ.lower := by rwa [lt_div_iff₀ (by linarith)] at ht
          nlinarith
      simp [ψ.eq_zero_of_lt _ hlt]
    · simp [hφR _ (not_le.1 hw)]
  eq_zero_of_gt := fun t ht => by
    unfold heightTransform
    refine integral_eq_zero_of_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : pairU UpperHalfPlane.I w ≤ R
    · have h1 := im_lt_of_pairU_le (show pairU w UpperHalfPlane.I ≤ R by rwa [pairU_comm])
      rw [UpperHalfPlane.I_im] at h1
      have hu : 0 < ψ.upper := ψ.lower_pos.trans_le ψ.lower_le_upper
      have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
      have hgt : ψ.upper < t * w.im := by nlinarith
      simp [ψ.eq_zero_of_gt _ hgt]
    · simp [hφR _ (not_le.1 hw)]

theorem im_toSL2R_smul (ζ w : ℍ) : (ζ.toSL2R • w).im = ζ.im * w.im := by
  have h := UpperHalfPlane.im_smul_eq_div_normSq (ζ.toSL2R : GL (Fin 2) ℝ) w
  change (ζ.toSL2R • w).im = _ at h
  rw [h]
  have hy := ζ.im_pos
  have hd : denom (ζ.toSL2R : GL (Fin 2) ℝ) (w : ℂ) = ((1 / √ζ.im : ℝ) : ℂ) := by
    simp [denom]
  have hdet : |(Matrix.GeneralLinearGroup.det (ζ.toSL2R : GL (Fin 2) ℝ) : ℝ)| = 1 := by
    simp
  rw [hd, Complex.normSq_ofReal, hdet, one_mul]
  have hs : 1 / √ζ.im * (1 / √ζ.im) = ζ.im⁻¹ := by
    rw [one_div_mul_one_div, Real.mul_self_sqrt hy.le, one_div]
  rw [hs]
  field_simp

/-- Radial averages of height functions: `∫_ℍ φ(u(ζ, w)) ψ(Im w) dμ(w) = ψ̃(Im ζ)`. -/
theorem integral_pairKernel_height (ψ : ℝ → ℂ) (ζ : ℍ) :
    ∫ w : ℍ, ((φ (pairU ζ w) : ℝ) : ℂ) * ψ w.im = heightTransform φ ψ ζ.im := by
  have hmp := measurePreserving_smul ((ζ.toSL2R : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have h := hmp.integral_comp (measurableEmbedding_const_smul _)
    (fun w : ℍ => ((φ (pairU ζ w) : ℝ) : ℂ) * ψ w.im)
  rw [← h, heightTransform]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  change ((φ (pairU ζ (ζ.toSL2R • w)) : ℝ) : ℂ) * ψ (ζ.toSL2R • w).im = _
  have hu := pairU_smul ζ.toSL2R UpperHalfPlane.I w
  rw [toSL2R_smul_I] at hu
  rw [hu, im_toSL2R_smul]

theorem integral_pairKernel_height_smul (ψ : ℝ → ℂ) (M : SL(2, ℤ)) (z : ℍ) :
    ∫ w : ℍ, ((φ (pairU z w) : ℝ) : ℂ) * ψ (M • w).im =
      ∫ w : ℍ, ((φ (pairU (M • z) w) : ℝ) : ℂ) * ψ w.im := by
  have h := (measurePreserving_smul M (volume : Measure ℍ)).integral_comp
    (measurableEmbedding_const_smul M) (fun w : ℍ => ((φ (pairU (M • z) w) : ℝ) : ℂ) * ψ w.im)
  simp only [pairU_smul_int] at h
  exact h

/-- **Point-pair images of incomplete Eisenstein series**: `L_φ E(· | ψ, v) = E(· | ψ̃, v)`. -/
theorem ppApply_incEis (hφc : Continuous φ) (hφR : KernelSupport φ R) (ψ : HeightProfile)
    {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) (z : ℍ) :
    ppApply φ (incEis ψ.toFun v) z = incEis (heightTransform φ ψ.toFun) v z := by
  obtain ⟨S, hS⟩ := exists_finset_profile_eq_zero ψ.lower_pos ψ.eq_zero_of_lt
    (isCompact_closedBall z (1 + 2 * R))
  have hterm : ∀ p : gammaSet 1 1 0,
      ∫ w : ℍ, ((φ (pairU z w) : ℝ) : ℂ) * ψ.toFun (gammaSetMatrix p • w).im =
        heightTransform φ ψ.toFun (gammaSetMatrix p • z).im := fun p => by
    rw [integral_pairKernel_height_smul, integral_pairKernel_height]
  have hzero : ∀ p ∉ S, heightTransform φ ψ.toFun (gammaSetMatrix p • z).im = 0 := by
    intro p hp
    rw [← hterm p]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun w => ?_)
    change ((φ (pairU z w) : ℝ) : ℂ) * ψ.toFun (gammaSetMatrix p • w).im = 0
    by_cases hw : w ∈ Metric.closedBall z (1 + 2 * R)
    · rw [hS w hw p hp, mul_zero]
    · exact pairKernel_mul_eq_zero_of_not_mem hφR hw _
  have hpt : ∀ w : ℍ, ((φ (pairU z w) : ℝ) : ℂ) • incEis ψ.toFun v w =
      ∑ p ∈ S, (((φ (pairU z w) : ℝ) : ℂ) * ψ.toFun (gammaSetMatrix p • w).im) •
        (deckRho N (gammaSetMatrix p)).symm v := by
    intro w
    by_cases hw : w ∈ Metric.closedBall z (1 + 2 * R)
    · rw [incEis_eq_sum (hS w hw), Finset.smul_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [eisTerm, smul_smul]
    · have h0 : ((φ (pairU z w) : ℝ) : ℂ) = 0 := by
        simpa using pairKernel_mul_eq_zero_of_not_mem hφR hw 1
      simp [h0]
  have hint : ∀ p : gammaSet 1 1 0, Integrable (fun w : ℍ =>
      ((φ (pairU z w) : ℝ) : ℂ) * ψ.toFun (gammaSetMatrix p • w).im) := fun p =>
    (integrable_pairKernel_smul' hφc hφR (ψ.continuous.comp (continuous_im.comp
      (continuous_modular_smul (gammaSetMatrix p)))) z).congr
      (Eventually.of_forall fun w => by simp [Complex.real_smul])
  rw [ppApply_eq_integral hφc hφR (ψ.continuous_incEis v) (deckEquivariant_incEis hv) z,
    incEis_eq_sum hzero]
  simp_rw [hpt]
  rw [integral_finsetSum S fun p _ => (hint p).smul_const _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_const, hterm p]
  rfl

/-- **Point-pair images in `L²`**: `L_φ` maps `E(· | ψ, v)` to `E(· | ψ̃, v)`. -/
theorem PairProfile.op_incEisL2 (P : PairProfile) (ψ : HeightProfile) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) :
    P.op N (incEisL2 ψ v) =
      incEisL2 (ψ.pointPair P.differentiable.continuous P.radius_nonneg P.support) v := by
  apply Lp.ext
  filter_upwards [P.op_coeFn (incEisL2 ψ v),
    incEisL2_coeFn (ψ.pointPair P.differentiable.continuous P.radius_nonneg P.support) v]
    with z h1 h2
  rw [h1, h2, ppApply_congr_ae _ (incEisL2_coeFn ψ v)]
  exact ppApply_incEis P.differentiable.continuous P.support ψ hv z

end PointPair

end

end GaloisForLFunctions.RHTower.DeckPointPair
