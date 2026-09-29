import GaloisForLFunctions.RHTower.HeightProfileMellin
import GaloisForLFunctions.RHTower.DeckScatteringSingularities

/-!
# Incomplete Eisenstein series as Mellin superpositions

For a `C²` height profile `φ`, `σ > 1` and `w ∈ V_∞`,
`E(z | φ, w) = π⁻¹ ∫ φ̂(σ+it) Ẽ(z, σ+it; w) dt` (`incEis_eq_integral_eisVec`): Mellin inversion
term by term in the row sum, exchanged with the sum by absolute convergence
(`Σ_p Im(M_p z)^σ < ∞`).

Unfolding against `Ẽ(·, s; w)` and the constant term `y^s w + y^{1-s} Φ̃(s) w` give
`∫_𝒟 ⟨E(·|ψ,v), Ẽ(·,s;w)⟩ = 2 (ψ̄̂(1-s)⟨v,w⟩ + ψ̄̂(s)⟨v,Φ̃(s)w⟩)`
(`integral_inner_incEis_eisVec`), and Fubini on `𝒟 × ℝ` combines the two into the inner product of
two incomplete Eisenstein series (`inner_incEisL2_eq_integral_line`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries Complex
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## The real Eisenstein sum `Σ_p Im(M_p z)^σ` -/

theorem onesVec_apply (q : Deck N) : onesVec N q = 1 := rfl

theorem deckRho_onesVec (A : SL(2, ℤ)) : deckRho N A (onesVec N) = onesVec N := by
  ext q; rw [deckRho_apply]; rfl

theorem ofReal_tsum_rowHeight_rpow {σ : ℝ} (hσ : 1 < σ) (z : ℍ) (q : Deck N) :
    ((∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ σ : ℝ) : ℂ) =
      2 * eisVec (σ : ℂ) (onesVec N) z q := by
  rw [eisVec_apply (by simpa using hσ), Complex.ofReal_tsum, ← mul_assoc,
    show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul]
  refine tsum_congr fun p => ?_
  rw [Complex.ofReal_cpow (RHTower.rowHeight_pos p z).le, onesVec_apply, mul_one]

theorem continuous_tsum_rowHeight_rpow {σ : ℝ} (hσ : 1 < σ) :
    Continuous fun z : ℍ => ∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ σ := by
  have hc : Continuous fun z : ℍ => eisVec (σ : ℂ) (onesVec 0) z (1 : Deck 0) :=
    (EuclideanSpace.proj (1 : Deck 0)).continuous.comp
      (continuous_eisVec (by simpa using hσ) (deckRho_onesVec _))
  have he : (fun z : ℍ => ∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ σ) =
      fun z => (2 * eisVec (σ : ℂ) (onesVec 0) z (1 : Deck 0)).re := funext fun z => by
    rw [← ofReal_tsum_rowHeight_rpow hσ z, Complex.ofReal_re]
  rw [he]
  exact Complex.continuous_re.comp (continuous_const.mul hc)

theorem exists_bound_tsum_rowHeight_fd {σ : ℝ} (hσ : 1 < σ) (Y : ℝ) :
    ∃ M, ∀ z ∈ fd, z.im ≤ Y → ∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ σ ≤ M := by
  obtain ⟨M, hM⟩ := (_root_.RHTower.D4BMModularCore.truncated_cell_compact Y).exists_bound_of_continuousOn
    (continuous_tsum_rowHeight_rpow hσ).continuousOn
  exact ⟨M, fun z hz hy => (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hM z ⟨hz, hy⟩)⟩

theorem tsum_rowHeight_rpow_nonneg (σ : ℝ) (z : ℍ) :
    0 ≤ ∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ σ :=
  tsum_nonneg fun p => Real.rpow_nonneg (RHTower.rowHeight_pos p z).le _

/-- The Eisenstein series is continuous along vertical lines `Re s = σ > 1`. -/
theorem continuous_eisVec_line (hN : 2 ≤ N) {w : DeckSpace N} (hw : IsCuspVec w) (z : ℍ) {σ : ℝ}
    (hσ : 1 < σ) : Continuous fun t : ℝ => eisVec ((σ : ℂ) + t * Complex.I) w z := by
  have he : (fun t : ℝ => eisVec ((σ : ℂ) + t * Complex.I) w z) =
      fun t : ℝ => eisExt ((σ : ℂ) + t * Complex.I) w z :=
    funext fun t : ℝ => eisVec_eq_eisExt hN (s := (σ : ℂ) + t * Complex.I) (by simpa using hσ) hw z
  rw [he]
  refine continuous_deck_of_coords fun q => ?_
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hs : 1 / 2 < ((σ : ℂ) + t * Complex.I).re := by simp; linarith
  have hs1 : (σ : ℂ) + t * Complex.I ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  exact ((differentiableAt_eisExt_apply w z q (mem_Wset_of_half_lt hs) hs1).continuousAt).comp
    (f := fun t : ℝ => (σ : ℂ) + t * Complex.I) (by fun_prop)

/-! ## Mellin superposition -/

/-- **Incomplete Eisenstein series as Mellin superpositions of Eisenstein series**:
`E(z | φ, w) = π⁻¹ ∫ φ̂(σ+it) Ẽ(z, σ+it; w) dt` for `σ > 1`. -/
theorem incEis_eq_integral_eisVec (φ : HeightProfile) (hφ : ContDiff ℝ 2 φ.toFun) {σ : ℝ}
    (hσ : 1 < σ) (w : DeckSpace N) (z : ℍ) :
    incEis φ.toFun w z = (Real.pi : ℂ)⁻¹ •
      ∫ t : ℝ, hMellin φ.toFun ((σ : ℂ) + t * Complex.I) • eisVec ((σ : ℂ) + t * Complex.I) w z := by
  set c : gammaSet 1 1 0 → DeckSpace N := fun p => (deckRho N (gammaSetMatrix p)).symm w
  set Y : gammaSet 1 1 0 → ℝ := fun p => (gammaSetMatrix p • z).im
  set h : ℝ → ℂ := fun t => hMellin φ.toFun ((σ : ℂ) + t * Complex.I)
  set F : gammaSet 1 1 0 → ℝ → DeckSpace N := fun p t =>
    ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (Y p : ℂ) ^ ((σ : ℂ) + t * Complex.I) * h t) • c p
  have hY : ∀ p, 0 < Y p := fun p => (gammaSetMatrix p • z).im_pos
  have hh : Integrable h := φ.integrable_hMellin_line hφ σ
  have hcY : ∀ p, Continuous fun t : ℝ => (Y p : ℂ) ^ ((σ : ℂ) + t * Complex.I) := fun p =>
    (by fun_prop : Continuous fun t : ℝ => (σ : ℂ) + t * Complex.I).const_cpow
      (Or.inl (ofReal_ne_zero.2 (hY p).ne'))
  have hnY : ∀ p (t : ℝ), ‖(Y p : ℂ) ^ ((σ : ℂ) + t * Complex.I)‖ = Y p ^ σ := fun p t => by
    rw [norm_cpow_eq_rpow_re_of_pos (hY p)]; simp
  have hnc : ∀ p, ‖c p‖ = ‖w‖ := fun p => LinearIsometryEquiv.norm_map _ _
  have hnF : ∀ p t, ‖F p t‖ = (2 * Real.pi)⁻¹ * Y p ^ σ * ‖w‖ * ‖h t‖ := fun p t => by
    simp only [F, norm_smul, norm_mul, hnY, hnc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (mul_pos two_pos Real.pi_pos))]
    ring
  have hint : ∀ p, Integrable (F p) := fun p => by
    refine Integrable.smul_const ?_ (c p)
    refine hh.bdd_mul (c := (2 * Real.pi)⁻¹ * Y p ^ σ)
      ((continuous_const.mul (hcY p)).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [norm_mul, hnY, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (mul_pos two_pos Real.pi_pos))]
  have hsum : Summable fun p => ∫ t, ‖F p t‖ := by
    have he : (fun p => ∫ t, ‖F p t‖) = fun p =>
        RHTower.rowHeight p z ^ σ * ((2 * Real.pi)⁻¹ * ‖w‖ * ∫ t, ‖h t‖) := funext fun p => by
      simp_rw [hnF]
      rw [integral_const_mul]
      simp only [Y, RHTower.rowHeight]
      ring
    rw [he]
    exact (summable_rowHeight_rpow hσ z).mul_right _
  have hterm : ∀ p, eisTerm φ.toFun w p z = ∫ t, F p t := fun p => by
    rw [integral_smul_const]
    simp only [eisTerm]
    congr 1
    rw [φ.hMellin_inversion hφ σ (hY p), real_smul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [h]
    ring
  have hF : ∀ t, ∑' p, F p t = ((Real.pi : ℂ)⁻¹ * h t) • eisVec ((σ : ℂ) + t * Complex.I) w z := fun t => by
    have hre : ∀ p, F p t = (((2 * Real.pi)⁻¹ : ℝ) * h t : ℂ) •
        eisTerm (fun y : ℝ => (y : ℂ) ^ ((σ : ℂ) + t * Complex.I)) w p z := fun p => by
      simp only [F, eisTerm, smul_smul]
      congr 1
      ring
    simp_rw [hre]
    rw [tsum_const_smul'', ← incEis, eisVec, smul_smul]
    congr 1
    push_cast
    field_simp
  rw [incEis, tsum_congr hterm, integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hF, ← smul_smul]
  rw [integral_smul]

/-! ## Unfolding against the Eisenstein series -/

/-- The constant term of `Ẽ(·, s; w)` read against `v ∈ V_T`. -/
theorem horoAverage_eisVec {s : ℂ} (hs : 1 < s.re) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) {w : DeckSpace N} (hw : IsCuspVec w) {y : ℝ} (hy : 0 < y) :
    horoAverage v (eisVec s w) y =
      (y : ℂ) ^ s * ⟪v, w⟫_ℂ + (y : ℂ) ^ (1 - s) * ⟪v, scatVec s w⟫_ℂ := by
  have hv' : deckRho N ModularGroup.T (deckConjVec v) = deckConjVec v := by
    rw [deckRho_deckConjVec, hv]
  have hconj : ∀ X : DeckSpace N, ⟪v, X⟫_ℂ = bil (deckConjVec v) X := fun X => by
    rw [bil_eq_inner, deckConjVec_deckConjVec]
  rw [horoAverage_eq_intervalIntegral]
  simp_rw [hconj]
  rw [intervalIntegral_bil_eisVec hs hv' hw hy, bil_add_right, bil_smul_right, bil_smul_right]

/-- **Unfolding against `Ẽ(·, s; w)`**:
`∫_𝒟 ⟨E(·|ψ,v), Ẽ(·,s;w)⟩ = 2 (ψ̄̂(1-s)⟨v,w⟩ + ψ̄̂(s)⟨v,Φ̃(s)w⟩)`. -/
theorem integral_inner_incEis_eisVec (ψ : HeightProfile) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) {w : DeckSpace N} (hw : IsCuspVec w) {s : ℂ}
    (hs : 1 < s.re) :
    ∫ z in fd, ⟪incEis ψ.toFun v z, eisVec s w z⟫_ℂ =
      2 * (hMellin ψ.conjProfile.toFun (1 - s) * ⟪v, w⟫_ℂ +
        hMellin ψ.conjProfile.toFun s * ⟪v, scatVec s w⟫_ℂ) := by
  rw [integral_inner_incEis_eq ψ hv (continuous_eisVec hs hw.1) (deckEquivariant_eisVec hw.1)]
  congr 1
  have hcongr : EqOn (fun y : ℝ => (y ^ 2)⁻¹ • (conj (ψ.toFun y) * horoAverage v (eisVec s w) y))
      (fun y : ℝ => (y ^ 2)⁻¹ • (ψ.conjProfile.toFun y * (y : ℂ) ^ s) * ⟪v, w⟫_ℂ +
        (y ^ 2)⁻¹ • (ψ.conjProfile.toFun y * (y : ℂ) ^ (1 - s)) * ⟪v, scatVec s w⟫_ℂ) (Ioi 0) :=
    fun y hy => by
      simp only
      rw [horoAverage_eisVec hs hv hw hy, ψ.conjProfile_apply, real_smul, real_smul, real_smul]
      ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_add ((ψ.conjProfile.integrableOn_inv_sq_smul_mul_cpow s).mul_const _)
      ((ψ.conjProfile.integrableOn_inv_sq_smul_mul_cpow (1 - s)).mul_const _),
    integral_mul_const, integral_mul_const, ψ.conjProfile.integral_inv_sq_smul_mul_cpow,
    ψ.conjProfile.integral_inv_sq_smul_mul_cpow, sub_sub_cancel]

/-! ## The inner product of two incomplete Eisenstein series -/

/-- **Inner product of incomplete Eisenstein series on a line `Re s = σ > 1`**:
`⟨E(·|ψ,v), E(·|φ,w)⟩ = π⁻¹ ∫ φ̂(s) · 2(ψ̄̂(1-s)⟨v,w⟩ + ψ̄̂(s)⟨v,Φ̃(s)w⟩) dt`, `s = σ+it`. -/
theorem inner_incEisL2_eq_integral_line (hN : 2 ≤ N) (ψ φ : HeightProfile)
    (hφ : ContDiff ℝ 2 φ.toFun) {v w : DeckSpace N} (hv : deckRho N ModularGroup.T v = v)
    (hw : IsCuspVec w) {σ : ℝ} (hσ : 1 < σ) :
    ⟪incEisL2 ψ v, incEisL2 φ w⟫_ℂ = (Real.pi : ℂ)⁻¹ * ∫ t : ℝ, hMellin φ.toFun ((σ : ℂ) + t * Complex.I) *
      (2 * (hMellin ψ.conjProfile.toFun (1 - ((σ : ℂ) + t * Complex.I)) * ⟪v, w⟫_ℂ +
        hMellin ψ.conjProfile.toFun ((σ : ℂ) + t * Complex.I) * ⟪v, scatVec ((σ : ℂ) + t * Complex.I) w⟫_ℂ)) := by
  set h : ℝ → ℂ := fun t => hMellin φ.toFun ((σ : ℂ) + t * Complex.I)
  set E : ℝ → ℍ → DeckSpace N := fun t z => eisVec ((σ : ℂ) + t * Complex.I) w z
  set f : ℍ → ℝ → ℂ := fun z t => h t * ⟪incEis ψ.toFun v z, E t z⟫_ℂ
  have hh : Integrable h := φ.integrable_hMellin_line hφ σ
  have hre : ∀ t : ℝ, 1 < ((σ : ℂ) + t * Complex.I).re := fun t => by simpa using hσ
  set R : ℍ → ℝ := fun z => ∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ σ
  have hE : ∀ t z, ‖E t z‖ ≤ 1 / 2 * (R z * ‖w‖) := fun t z => by
    have := norm_eisVec_le (hre t) w z
    simpa using this
  -- integrability in `t` for fixed `z`
  have hEc : ∀ z, Continuous fun t => E t z := fun z => continuous_eisVec_line hN hw z hσ
  have hintz : ∀ z, Integrable fun t => h t • E t z := fun z => by
    refine (hh.norm.mul_const (1 / 2 * (R z * ‖w‖))).mono'
      ((hh.aestronglyMeasurable).smul (hEc z).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hE t z) (norm_nonneg _)
  -- the bound on `𝒟`
  obtain ⟨C, hC⟩ := ψ.exists_bound_fd v
  obtain ⟨M, hM⟩ := exists_bound_tsum_rowHeight_fd hσ ψ.cap
  set B : ℍ → ℝ := fun z => ‖incEis ψ.toFun v z‖ * (1 / 2 * (R z * ‖w‖))
  have hBc : Continuous B :=
    (ψ.continuous_incEis v).norm.mul (continuous_const.mul
      ((continuous_tsum_rowHeight_rpow hσ).mul continuous_const))
  have hB : Integrable B cellMeasure := by
    refine Integrable.of_bound hBc.aestronglyMeasurable (C * (1 / 2 * (|M| * ‖w‖))) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).2 (Eventually.of_forall fun z hz => ?_)
    have hR0 : 0 ≤ R z := tsum_rowHeight_rpow_nonneg σ z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hY : z.im ≤ ψ.cap
    · have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z hz)
      refine mul_le_mul (hC z hz) ?_ (by positivity) hC0
      gcongr
      exact (hM z hz hY).trans (le_abs_self M)
    · simp only [B]
      rw [ψ.incEis_eq_zero_of_im_gt v (not_le.1 hY), norm_zero, zero_mul]
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z hz)
      positivity
  -- joint integrability
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (cellMeasure.prod volume) := by
    have hs : StronglyMeasurable (Function.uncurry fun (t : ℝ) (z : ℍ) => f z t) := by
      refine stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun z => ?_) (fun t => ?_)
      · exact (φ.continuous_hMellin_line σ).mul (continuous_const.inner (hEc z))
      · exact (continuous_const.mul ((ψ.continuous_incEis v).inner
          (continuous_eisVec (hre t) hw.1))).stronglyMeasurable
    exact (hs.comp_measurable measurable_swap).aestronglyMeasurable
  have hint : Integrable (Function.uncurry f) (cellMeasure.prod volume) := by
    refine (hB.mul_prod hh.norm).mono' hmeas (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, f, norm_mul]
    rw [mul_comm (‖h p.2‖)]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hE _ _) (norm_nonneg _))
  -- assemble
  have hinner : ⟪incEisL2 ψ v, incEisL2 φ w⟫_ℂ =
      ∫ z in fd, ⟪incEis ψ.toFun v z, incEis φ.toFun w z⟫_ℂ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [incEisL2_coeFn ψ v, incEisL2_coeFn φ w] with z h1 h2
    rw [h1, h2]
  have hpt : ∀ z, ⟪incEis ψ.toFun v z, incEis φ.toFun w z⟫_ℂ =
      (Real.pi : ℂ)⁻¹ * ∫ t, f z t := fun z => by
    rw [incEis_eq_integral_eisVec φ hφ hσ w z, inner_smul_right, ← integral_inner (hintz z)]
    simp_rw [inner_smul_right]
    rfl
  rw [hinner, integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [f]
  rw [integral_const_mul, integral_inner_incEis_eisVec ψ hv hw (hre t)]
