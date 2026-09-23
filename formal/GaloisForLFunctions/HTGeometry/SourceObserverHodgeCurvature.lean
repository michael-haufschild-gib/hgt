import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Source–observer Hodge curvature and subunit annihilation

Two densely defined Hilbert-complex arrows `d_S : S⁻¹ → S⁰` and `d_H : H⁻¹ → H⁰` are compared by
linear maps `A₋₁ : S⁻¹ → H⁻¹` and `A₀ : S⁰ → H⁰`.  The chain-level Beck–Chevalley defect

`Ω_A a = A₀ d_S a − d_H A₋₁ a`

is the **comparison curvature** on a source antecedent `a`.  With a source residual `r` and the
physical field `y = A₀ (d_S a + r)`, the source–observer Gauss–Hodge identity reads

`⟪y, y⟫ = ⟪A₋₁ a, d_H* y⟫ + ⟪Ω_A a + A₀ r, y⟫`.

Its consequences are the annihilation laws: exact comparison, a subunit curvature gain, or a
strict upper bound on the signed curvature work each force `y = 0`, and the unit gain is sharp.
-/

open scoped InnerProductSpace LinearPMap

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 : Type*} [RCLike 𝕜]
variable {Sm S0 Hm H0 : Type*}
  [NormedAddCommGroup Sm] [InnerProductSpace 𝕜 Sm]
  [NormedAddCommGroup S0] [InnerProductSpace 𝕜 S0]
  [NormedAddCommGroup Hm] [InnerProductSpace 𝕜 Hm] [CompleteSpace Hm]
  [NormedAddCommGroup H0] [InnerProductSpace 𝕜 H0]

/-- The chain-level comparison curvature `Ω_A a = A₀ d_S a − d_H A₋₁ a`.  It vanishes exactly
when the comparison commutes with the two displayed differentials on `a`. -/
noncomputable def comparisonCurvature (dS : Sm →ₗ.[𝕜] S0) (dH : Hm →ₗ.[𝕜] H0)
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain) : H0 :=
  A0 (dS a) - dH ⟨Am (a : Sm), haH⟩

/-- The physical field `y = A₀ (d_S a + r)` produced by a source antecedent `a` and a source
residual `r`. -/
noncomputable def observerField (dS : Sm →ₗ.[𝕜] S0) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (r : S0) : H0 :=
  A0 (dS a + r)

omit [CompleteSpace Hm] in
/-- The observer field splits into a `d_H`-exact part, the comparison curvature and the
transported source residual. -/
theorem observerField_eq_add (dS : Sm →ₗ.[𝕜] S0) (dH : Hm →ₗ.[𝕜] H0)
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain) (r : S0) :
    observerField dS A0 a r
      = dH ⟨Am (a : Sm), haH⟩ + (comparisonCurvature dS dH Am A0 a haH + A0 r) := by
  rw [observerField, comparisonCurvature, map_add]
  abel

/-- The adjoint pairing on a densely defined arrow. -/
theorem inner_apply_eq_inner_adjoint {dH : Hm →ₗ.[𝕜] H0}
    (hdense : Dense (dH.domain : Set Hm)) (u : Hm) (hu : u ∈ dH.domain)
    (y : H0) (hy : y ∈ dH.adjoint.domain) :
    ⟪dH ⟨u, hu⟩, y⟫_𝕜 = ⟪u, dH.adjoint ⟨y, hy⟩⟫_𝕜 := by
  have h := LinearPMap.adjoint_isFormalAdjoint (T := dH) hdense ⟨y, hy⟩ ⟨u, hu⟩
  rw [← inner_conj_symm, ← inner_conj_symm u]
  exact congrArg (starRingEnd 𝕜) h.symm

/-- **The source–observer Gauss–Hodge identity.**  The energy of the physical field is carried
exactly by the source antecedent paired with the Hodge co-differential together with the signed
work of the comparison curvature and the transported source residual. -/
theorem inner_observerField_self_eq {dS : Sm →ₗ.[𝕜] S0} {dH : Hm →ₗ.[𝕜] H0}
    (hdense : Dense (dH.domain : Set Hm))
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain) (r : S0)
    (hy : observerField dS A0 a r ∈ dH.adjoint.domain) :
    ⟪observerField dS A0 a r, observerField dS A0 a r⟫_𝕜
      = ⟪Am (a : Sm), dH.adjoint ⟨observerField dS A0 a r, hy⟩⟫_𝕜
        + ⟪comparisonCurvature dS dH Am A0 a haH + A0 r,
            observerField dS A0 a r⟫_𝕜 := by
  have hsplit := observerField_eq_add dS dH Am A0 a haH r
  calc ⟪observerField dS A0 a r, observerField dS A0 a r⟫_𝕜
      = ⟪dH ⟨Am (a : Sm), haH⟩ + (comparisonCurvature dS dH Am A0 a haH + A0 r),
          observerField dS A0 a r⟫_𝕜 := by rw [← hsplit]
    _ = ⟪dH ⟨Am (a : Sm), haH⟩, observerField dS A0 a r⟫_𝕜
          + ⟪comparisonCurvature dS dH Am A0 a haH + A0 r,
              observerField dS A0 a r⟫_𝕜 := inner_add_left _ _ _
    _ = ⟪Am (a : Sm), dH.adjoint ⟨observerField dS A0 a r, hy⟩⟫_𝕜
          + ⟪comparisonCurvature dS dH Am A0 a haH + A0 r,
              observerField dS A0 a r⟫_𝕜 := by
        rw [inner_apply_eq_inner_adjoint hdense (Am (a : Sm)) haH _ hy]

/-- The Cauchy–Schwarz form of the Gauss–Hodge identity. -/
theorem norm_observerField_sq_le {dS : Sm →ₗ.[𝕜] S0} {dH : Hm →ₗ.[𝕜] H0}
    (hdense : Dense (dH.domain : Set Hm))
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain) (r : S0)
    (hy : observerField dS A0 a r ∈ dH.adjoint.domain) :
    ‖observerField dS A0 a r‖ ^ (2 : ℕ)
      ≤ ‖Am (a : Sm)‖ * ‖dH.adjoint ⟨observerField dS A0 a r, hy⟩‖
        + ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖ * ‖observerField dS A0 a r‖ := by
  have hid := inner_observerField_self_eq hdense Am A0 a haH r hy
  have hre := congrArg RCLike.re hid
  rw [inner_self_eq_norm_sq, map_add] at hre
  rw [hre]
  refine add_le_add ?_ ?_
  · exact le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  · exact le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)

/-- **Exact comparison annihilation.**  A co-closed physical field with no source residual and
vanishing comparison curvature vanishes. -/
theorem observerField_eq_zero_of_exact {dS : Sm →ₗ.[𝕜] S0} {dH : Hm →ₗ.[𝕜] H0}
    (hdense : Dense (dH.domain : Set Hm))
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain)
    (hy : observerField dS A0 a 0 ∈ dH.adjoint.domain)
    (hco : dH.adjoint ⟨observerField dS A0 a 0, hy⟩ = 0)
    (hcurv : comparisonCurvature dS dH Am A0 a haH = 0) :
    observerField dS A0 a 0 = 0 := by
  have hle := norm_observerField_sq_le hdense Am A0 a haH 0 hy
  rw [hco, hcurv] at hle
  simp only [map_zero, add_zero, norm_zero, mul_zero, zero_mul] at hle
  have hzero : ‖observerField dS A0 a 0‖ ≤ 0 := by
    nlinarith [norm_nonneg (observerField dS A0 a 0)]
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

/-- **Subunit curvature annihilation.**  A co-closed physical field whose curvature-plus-residual
gain on the actual source antecedent is strictly below one vanishes. -/
theorem observerField_eq_zero_of_subunit {dS : Sm →ₗ.[𝕜] S0} {dH : Hm →ₗ.[𝕜] H0}
    (hdense : Dense (dH.domain : Set Hm))
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain) (r : S0)
    (hy : observerField dS A0 a r ∈ dH.adjoint.domain)
    (hco : dH.adjoint ⟨observerField dS A0 a r, hy⟩ = 0)
    {κ : ℝ} (hκ : κ < 1)
    (hgain : ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖
      ≤ κ * ‖observerField dS A0 a r‖) :
    observerField dS A0 a r = 0 := by
  have hle := norm_observerField_sq_le hdense Am A0 a haH r hy
  rw [hco, norm_zero, mul_zero, zero_add] at hle
  have hmul : ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖ * ‖observerField dS A0 a r‖
      ≤ κ * ‖observerField dS A0 a r‖ ^ (2 : ℕ) := by
    have := mul_le_mul_of_nonneg_right hgain (norm_nonneg (observerField dS A0 a r))
    calc ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖ * ‖observerField dS A0 a r‖
        ≤ κ * ‖observerField dS A0 a r‖ * ‖observerField dS A0 a r‖ := this
      _ = κ * ‖observerField dS A0 a r‖ ^ (2 : ℕ) := by ring
  have hfinal : ‖observerField dS A0 a r‖ ^ (2 : ℕ) ≤ κ * ‖observerField dS A0 a r‖ ^ (2 : ℕ) :=
    le_trans hle hmul
  have hsq : ‖observerField dS A0 a r‖ ^ (2 : ℕ) ≤ 0 := by nlinarith [sq_nonneg ‖observerField dS A0 a r‖]
  have hzero : ‖observerField dS A0 a r‖ ≤ 0 := by
    nlinarith [norm_nonneg (observerField dS A0 a r)]
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

/-- **Source energy annihilation.**  Only the signed curvature work on the actual source/field
pair needs to be controlled: a co-closed physical field whose curvature work is at most `κ‖y‖²`
with `κ < 1` vanishes.  In particular a dissipative curvature work forces `y = 0`. -/
theorem observerField_eq_zero_of_reWork {dS : Sm →ₗ.[𝕜] S0} {dH : Hm →ₗ.[𝕜] H0}
    (hdense : Dense (dH.domain : Set Hm))
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain) (r : S0)
    (hy : observerField dS A0 a r ∈ dH.adjoint.domain)
    (hco : dH.adjoint ⟨observerField dS A0 a r, hy⟩ = 0)
    {κ : ℝ} (hκ : κ < 1)
    (hwork : RCLike.re (⟪comparisonCurvature dS dH Am A0 a haH + A0 r,
        observerField dS A0 a r⟫_𝕜) ≤ κ * ‖observerField dS A0 a r‖ ^ (2 : ℕ)) :
    observerField dS A0 a r = 0 := by
  have hid := inner_observerField_self_eq hdense Am A0 a haH r hy
  have hre := congrArg RCLike.re hid
  rw [inner_self_eq_norm_sq, map_add, hco, inner_zero_right, map_zero, zero_add] at hre
  have hfinal : ‖observerField dS A0 a r‖ ^ (2 : ℕ) ≤ κ * ‖observerField dS A0 a r‖ ^ (2 : ℕ) := by
    linarith [hwork]
  have hsq : ‖observerField dS A0 a r‖ ^ (2 : ℕ) ≤ 0 := by nlinarith [sq_nonneg ‖observerField dS A0 a r‖]
  have hzero : ‖observerField dS A0 a r‖ ≤ 0 := by
    nlinarith [norm_nonneg (observerField dS A0 a r)]
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

/-- **Approximate co-closure.**  A subunit curvature gain converts quantitative co-closure into
quantitative field control without requiring exact comparison. -/
theorem norm_observerField_sq_le_of_subunit {dS : Sm →ₗ.[𝕜] S0} {dH : Hm →ₗ.[𝕜] H0}
    (hdense : Dense (dH.domain : Set Hm))
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain) (r : S0)
    (hy : observerField dS A0 a r ∈ dH.adjoint.domain)
    {κ : ℝ}
    (hgain : ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖
      ≤ κ * ‖observerField dS A0 a r‖) :
    (1 - κ) * ‖observerField dS A0 a r‖ ^ (2 : ℕ)
      ≤ ‖Am (a : Sm)‖ * ‖dH.adjoint ⟨observerField dS A0 a r, hy⟩‖ := by
  have hle := norm_observerField_sq_le hdense Am A0 a haH r hy
  have hmul : ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖ * ‖observerField dS A0 a r‖
      ≤ κ * ‖observerField dS A0 a r‖ ^ (2 : ℕ) := by
    have hstep := mul_le_mul_of_nonneg_right hgain (norm_nonneg (observerField dS A0 a r))
    calc ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖ * ‖observerField dS A0 a r‖
        ≤ κ * ‖observerField dS A0 a r‖ * ‖observerField dS A0 a r‖ := hstep
      _ = κ * ‖observerField dS A0 a r‖ ^ (2 : ℕ) := by ring
  nlinarith

omit [CompleteSpace Hm] in
/-- Subunit norm gain implies the directional source energy condition, so the latter is a genuine
weakening. -/
theorem reWork_le_of_subunit {dS : Sm →ₗ.[𝕜] S0} {dH : Hm →ₗ.[𝕜] H0}
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain) (r : S0)
    {κ : ℝ}
    (hgain : ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖
      ≤ κ * ‖observerField dS A0 a r‖) :
    RCLike.re (⟪comparisonCurvature dS dH Am A0 a haH + A0 r,
        observerField dS A0 a r⟫_𝕜) ≤ κ * ‖observerField dS A0 a r‖ ^ (2 : ℕ) := by
  have h1 : RCLike.re (⟪comparisonCurvature dS dH Am A0 a haH + A0 r,
      observerField dS A0 a r⟫_𝕜)
      ≤ ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖ * ‖observerField dS A0 a r‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  have h2 := mul_le_mul_of_nonneg_right hgain (norm_nonneg (observerField dS A0 a r))
  calc RCLike.re (⟪comparisonCurvature dS dH Am A0 a haH + A0 r,
        observerField dS A0 a r⟫_𝕜)
      ≤ ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖ * ‖observerField dS A0 a r‖ := h1
    _ ≤ κ * ‖observerField dS A0 a r‖ * ‖observerField dS A0 a r‖ := h2
    _ = κ * ‖observerField dS A0 a r‖ ^ (2 : ℕ) := by ring

/-! ## Gauge covariance -/

omit [CompleteSpace Hm] in
/-- **Unitary frame covariance.**  A unitary change of observer frame transports the comparison
curvature, the physical field and every formal co-differential value covariantly, so the
Gauss–Hodge identity and all its annihilation consequences are frame invariant. -/
theorem comparisonCurvature_gauge {Hm' H0' : Type*}
    [NormedAddCommGroup Hm'] [InnerProductSpace 𝕜 Hm'] [CompleteSpace Hm']
    [NormedAddCommGroup H0'] [InnerProductSpace 𝕜 H0']
    (dS : Sm →ₗ.[𝕜] S0) (dH : Hm →ₗ.[𝕜] H0) (dH' : Hm' →ₗ.[𝕜] H0')
    (Um : Hm ≃ₗᵢ[𝕜] Hm') (U0 : H0 ≃ₗᵢ[𝕜] H0')
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain)
    (haH' : Um (Am (a : Sm)) ∈ dH'.domain)
    (hconj : dH' ⟨Um (Am (a : Sm)), haH'⟩ = U0 (dH ⟨Am (a : Sm), haH⟩)) (r : S0) :
    comparisonCurvature dS dH' ((Um.toLinearIsometry.toLinearMap).comp Am)
        ((U0.toLinearIsometry.toLinearMap).comp A0) a haH'
      = U0 (comparisonCurvature dS dH Am A0 a haH) ∧
      observerField dS ((U0.toLinearIsometry.toLinearMap).comp A0) a r
        = U0 (observerField dS A0 a r) := by
  constructor
  · rw [comparisonCurvature, comparisonCurvature]
    have hAm : ((Um.toLinearIsometry.toLinearMap).comp Am) (a : Sm) = Um (Am (a : Sm)) := rfl
    rw [show (((U0.toLinearIsometry.toLinearMap).comp A0) (dS a) : H0') = U0 (A0 (dS a)) from rfl]
    rw [show dH' ⟨((Um.toLinearIsometry.toLinearMap).comp Am) (a : Sm), haH'⟩
        = dH' ⟨Um (Am (a : Sm)), haH'⟩ from rfl, hconj, ← map_sub]
  · rfl

omit [CompleteSpace Hm] in
/-- A unitary frame change transports formal co-differential values covariantly. -/
theorem isFormalCoDifferential_gauge {Hm' H0' : Type*}
    [NormedAddCommGroup Hm'] [InnerProductSpace 𝕜 Hm'] [CompleteSpace Hm']
    [NormedAddCommGroup H0'] [InnerProductSpace 𝕜 H0']
    (dH : Hm →ₗ.[𝕜] H0) (dH' : Hm' →ₗ.[𝕜] H0')
    (Um : Hm ≃ₗᵢ[𝕜] Hm') (U0 : H0 ≃ₗᵢ[𝕜] H0')
    (hconj : ∀ u : dH.domain, ∃ hu : Um (u : Hm) ∈ dH'.domain,
      dH' ⟨Um (u : Hm), hu⟩ = U0 (dH u))
    (hsurj : ∀ u' : dH'.domain, ∃ u : dH.domain, Um (u : Hm) = (u' : Hm'))
    (y : H0) (w : Hm) (hw : ∀ u : dH.domain, ⟪dH u, y⟫_𝕜 = ⟪(u : Hm), w⟫_𝕜) :
    ∀ u' : dH'.domain, ⟪dH' u', U0 y⟫_𝕜 = ⟪(u' : Hm'), Um w⟫_𝕜 := by
  intro u'
  obtain ⟨u, hu⟩ := hsurj u'
  obtain ⟨hmem, heq⟩ := hconj u
  have hu'eq : (u' : Hm') = Um (u : Hm) := hu.symm
  have hval : dH' u' = U0 (dH u) := by
    rw [show u' = (⟨Um (u : Hm), hmem⟩ : dH'.domain) from Subtype.ext hu'eq, heq]
  rw [hval, hu'eq, U0.inner_map_map, Um.inner_map_map]
  exact hw u

omit [CompleteSpace Hm] in
/-- The subunit gain criterion is observer-frame invariant. -/
theorem subunit_criterion_gauge_iff {Hm' H0' : Type*}
    [NormedAddCommGroup Hm'] [InnerProductSpace 𝕜 Hm'] [CompleteSpace Hm']
    [NormedAddCommGroup H0'] [InnerProductSpace 𝕜 H0']
    (dS : Sm →ₗ.[𝕜] S0) (dH : Hm →ₗ.[𝕜] H0) (dH' : Hm' →ₗ.[𝕜] H0')
    (Um : Hm ≃ₗᵢ[𝕜] Hm') (U0 : H0 ≃ₗᵢ[𝕜] H0')
    (Am : Sm →ₗ[𝕜] Hm) (A0 : S0 →ₗ[𝕜] H0)
    (a : dS.domain) (haH : Am (a : Sm) ∈ dH.domain)
    (haH' : Um (Am (a : Sm)) ∈ dH'.domain)
    (hconj : dH' ⟨Um (Am (a : Sm)), haH'⟩ = U0 (dH ⟨Am (a : Sm), haH⟩)) (r : S0) (κ : ℝ) :
    ‖comparisonCurvature dS dH' ((Um.toLinearIsometry.toLinearMap).comp Am)
          ((U0.toLinearIsometry.toLinearMap).comp A0) a haH'
        + ((U0.toLinearIsometry.toLinearMap).comp A0) r‖
        ≤ κ * ‖observerField dS ((U0.toLinearIsometry.toLinearMap).comp A0) a r‖
      ↔ ‖comparisonCurvature dS dH Am A0 a haH + A0 r‖
          ≤ κ * ‖observerField dS A0 a r‖ := by
  obtain ⟨hcurv, hfield⟩ :=
    comparisonCurvature_gauge dS dH dH' Um U0 Am A0 a haH haH' hconj r
  rw [hcurv, hfield,
    show ((U0.toLinearIsometry.toLinearMap).comp A0) r = U0 (A0 r) from rfl,
    ← map_add, U0.norm_map, U0.norm_map]

/-! ## Sharpness of the unit gain -/

/-- **The unit gain is sharp.**  At gain exactly one no annihilation follows: with the zero
target differential, the identity comparison and a nonzero source antecedent, the physical field
is co-closed and its curvature gain is one, yet it does not vanish. -/
theorem exists_unitGain_observerField_ne_zero :
    ∃ (dS dH : 𝕜 →ₗ.[𝕜] 𝕜) (Am A0 : 𝕜 →ₗ[𝕜] 𝕜) (a : dS.domain)
      (haH : Am (a : 𝕜) ∈ dH.domain) (hy : observerField dS A0 a 0 ∈ dH.adjoint.domain),
      Dense ((dH.domain : Submodule 𝕜 𝕜) : Set 𝕜) ∧
      dH.adjoint ⟨observerField dS A0 a 0, hy⟩ = 0 ∧
      ‖comparisonCurvature dS dH Am A0 a haH + A0 0‖
        = 1 * ‖observerField dS A0 a 0‖ ∧
      observerField dS A0 a 0 ≠ 0 := by
  classical
  set dS : 𝕜 →ₗ.[𝕜] 𝕜 := (LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤ with hdS
  set dH : 𝕜 →ₗ.[𝕜] 𝕜 := (0 : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤ with hdH
  have hdomtop : dH.domain = ⊤ := rfl
  have hdense : Dense ((dH.domain : Submodule 𝕜 𝕜) : Set 𝕜) := by
    rw [hdomtop, Submodule.top_coe]
    exact dense_univ
  have hzeroval : ∀ x : dH.domain, dH x = 0 := fun x => rfl
  have hmem : (0 : 𝕜) ∈ dH.domain := by rw [hdomtop]; trivial
  have hadjdom : ∀ y : 𝕜, y ∈ dH.adjoint.domain := by
    intro y
    refine LinearPMap.mem_adjoint_domain_of_exists (T := dH) y ⟨0, ?_⟩
    intro x
    rw [hzeroval x]
    simp
  set a : dS.domain := ⟨1, by rw [show dS.domain = ⊤ from rfl]; trivial⟩ with ha
  have hdSval : ∀ x : dS.domain, dS x = (x : 𝕜) := fun _ => rfl
  have hfield : observerField dS (LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜) a 0 = 1 := by
    rw [observerField, add_zero, hdSval a]
    simp [ha]
  have haH : (0 : 𝕜 →ₗ[𝕜] 𝕜) (a : 𝕜) ∈ dH.domain := by
    rw [hdomtop]; trivial
  refine ⟨dS, dH, 0, LinearMap.id, a, haH, hadjdom _, hdense, ?_, ?_, ?_⟩
  · refine LinearPMap.adjoint_apply_eq (T := dH) hdense ⟨_, hadjdom _⟩ (x₀ := 0) ?_
    intro x
    rw [hzeroval x]
    simp
  · have hcurv : comparisonCurvature dS dH (0 : 𝕜 →ₗ[𝕜] 𝕜) (LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜) a haH
        = 1 := by
      rw [comparisonCurvature, hzeroval ⟨_, haH⟩, sub_zero, hdSval a]
      simp [ha]
    rw [hcurv, hfield]
    simp
  · rw [hfield]
    exact one_ne_zero

end GaloisForLFunctions.HTGeometry
