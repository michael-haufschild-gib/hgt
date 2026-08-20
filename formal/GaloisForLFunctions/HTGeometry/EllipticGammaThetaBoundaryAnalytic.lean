import GaloisForLFunctions.HTGeometry.EllipticGammaProductSourceEquation
import GaloisForLFunctions.HTGeometry.MeromorphicEllipticGamma

/-!
# Global analytic packaging of the elliptic-gamma source boundary

The two structural boundary products

```text
Θ_τ(z) = ∏_k (1 − q^(k+1)/x(z)) · ∏_k (1 − q^k x(z)),
Θ_(σ|τ)(z) = ∏_j (1 − p^(j+1)/x(z)) · ∏_j (1 − p^j x(z)),
```

are built from the source periods alone, before the elliptic gamma product itself.  This file
proves that each single boundary product converges locally uniformly on the whole plane, hence is
entire, packages the two boundaries as elements of the global analytic germ ring, and restates the
three source equations as unconditional identities in the meromorphic germ field — with no
regular-locus hypothesis.

* **`hasProdLocallyUniformlyOn_ellipticGammaForwardBoundaryFactor`** and its backward and `τ`
  counterparts;
* **`differentiable_ellipticGammaMultiplicativeThetaBoundary(Tau)`** — the boundaries are entire;
* `ellipticGammaThetaBoundaryAnalytic(Tau)`, `ellipticGammaThetaBoundaryMero(Tau)`;
* **`ellipticGammaMero_add_sigma`**, **`ellipticGammaMero_add_tau`**,
  **`ellipticGammaMero_add_one`** — the source equations in `meroField ℂ`.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

open Bottcher

noncomputable section

/-! ## The single boundary products -/

/-- The forward structural boundary product. -/
def ellipticGammaForwardBoundaryProduct (tau z : ℂ) : ℂ :=
  ∏' k : ℕ, ellipticGammaForwardBoundaryFactor tau k z

/-- The backward structural boundary product. -/
def ellipticGammaBackwardBoundaryProduct (tau z : ℂ) : ℂ :=
  ∏' k : ℕ, ellipticGammaBackwardBoundaryFactor tau k z

/-- The forward `τ`-boundary product. -/
def ellipticGammaTauForwardBoundaryProduct (sigma tau z : ℂ) : ℂ :=
  ∏' j : ℕ, ellipticGammaTauForwardBoundaryFactor sigma tau j z

/-- The backward `τ`-boundary product. -/
def ellipticGammaTauBackwardBoundaryProduct (sigma tau z : ℂ) : ℂ :=
  ∏' j : ℕ, ellipticGammaTauBackwardBoundaryFactor sigma tau j z

theorem ellipticGammaMultiplicativeThetaBoundary_eq (tau z : ℂ) :
    ellipticGammaMultiplicativeThetaBoundary tau z =
      ellipticGammaForwardBoundaryProduct tau z *
        ellipticGammaBackwardBoundaryProduct tau z := rfl

theorem ellipticGammaMultiplicativeThetaBoundaryTau_eq (sigma tau z : ℂ) :
    ellipticGammaMultiplicativeThetaBoundaryTau sigma tau z =
      ellipticGammaTauForwardBoundaryProduct sigma tau z *
        ellipticGammaTauBackwardBoundaryProduct sigma tau z := rfl

/-! ## Locally uniform convergence -/

set_option maxHeartbeats 800000 in
theorem hasProdLocallyUniformlyOn_ellipticGammaForwardBoundaryFactor
    {nome tau : ℂ} (hnome : ‖ellipticNome nome‖ < 1) :
    HasProdLocallyUniformlyOn
      (fun k : ℕ => fun z : ℂ =>
        1 - ellipticNome nome ^ (k + 1) / ellipticThetaCoordinate tau z)
      (fun z : ℂ => ∏' k : ℕ,
        (1 - ellipticNome nome ^ (k + 1) / ellipticThetaCoordinate tau z))
      Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  have hInvCont : Continuous (fun z => (ellipticThetaCoordinate tau z)⁻¹) := by
    apply Continuous.inv₀
    · exact continuous_iff_continuousAt.mpr fun z =>
        (analyticAt_ellipticThetaCoordinate tau z).continuousAt
    · exact ellipticThetaCoordinate_ne_zero tau
  obtain ⟨C, hC⟩ := hK.bddAbove_image hInvCont.norm.continuousOn
  let D : ℝ := max C 0
  have hD0 : 0 ≤ D := le_max_right _ _
  have hD : ∀ z ∈ K, ‖(ellipticThetaCoordinate tau z)⁻¹‖ ≤ D := by
    intro z hz
    exact (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hu : Summable (fun k : ℕ => D * ‖ellipticNome nome‖ ^ (k + 1)) := by
    have hg : Summable (fun k : ℕ => ‖ellipticNome nome‖ ^ k) :=
      summable_geometric_of_lt_one (norm_nonneg _) hnome
    have := (hg.mul_left (D * ‖ellipticNome nome‖))
    refine this.congr fun k => ?_
    rw [pow_succ]
    ring
  have hbound : ∀ᶠ k : ℕ in cofinite, ∀ z ∈ K,
      ‖-(ellipticNome nome ^ (k + 1) / ellipticThetaCoordinate tau z)‖ ≤
        D * ‖ellipticNome nome‖ ^ (k + 1) := by
    filter_upwards with k
    intro z hz
    have hInv := hD z hz
    have hw0 : (0 : ℝ) ≤ ‖ellipticNome nome‖ ^ (k + 1) :=
      pow_nonneg (norm_nonneg _) (k + 1)
    simp only [norm_neg, div_eq_mul_inv, norm_mul, norm_pow]
    nlinarith
  convert! Summable.hasProdUniformlyOn_one_add hK hu hbound (fun k => by
    have hcont : Continuous (fun x : ℂ =>
        -(ellipticNome nome ^ (k + 1) * (ellipticThetaCoordinate tau x)⁻¹)) :=
      (continuous_const.mul hInvCont).neg
    simpa [div_eq_mul_inv] using hcont.continuousOn) using 1

set_option maxHeartbeats 800000 in
theorem hasProdLocallyUniformlyOn_ellipticGammaBackwardBoundaryFactor
    {nome tau : ℂ} (hnome : ‖ellipticNome nome‖ < 1) :
    HasProdLocallyUniformlyOn
      (fun k : ℕ => fun z : ℂ =>
        1 - ellipticNome nome ^ k * ellipticThetaCoordinate tau z)
      (fun z : ℂ => ∏' k : ℕ,
        (1 - ellipticNome nome ^ k * ellipticThetaCoordinate tau z))
      Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  have hCoordCont : Continuous (ellipticThetaCoordinate tau) :=
    continuous_iff_continuousAt.mpr fun z =>
      (analyticAt_ellipticThetaCoordinate tau z).continuousAt
  obtain ⟨C, hC⟩ := hK.bddAbove_image hCoordCont.norm.continuousOn
  let D : ℝ := max C 0
  have hD0 : 0 ≤ D := le_max_right _ _
  have hD : ∀ z ∈ K, ‖ellipticThetaCoordinate tau z‖ ≤ D := by
    intro z hz
    exact (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hu : Summable (fun k : ℕ => D * ‖ellipticNome nome‖ ^ k) :=
    (summable_geometric_of_lt_one (norm_nonneg _) hnome).mul_left D
  have hbound : ∀ᶠ k : ℕ in cofinite, ∀ z ∈ K,
      ‖-(ellipticNome nome ^ k * ellipticThetaCoordinate tau z)‖ ≤
        D * ‖ellipticNome nome‖ ^ k := by
    filter_upwards with k
    intro z hz
    have hCoord := hD z hz
    have hw0 : (0 : ℝ) ≤ ‖ellipticNome nome‖ ^ k := pow_nonneg (norm_nonneg _) k
    simp only [norm_neg, norm_mul, norm_pow]
    nlinarith
  convert! Summable.hasProdUniformlyOn_one_add hK hu hbound (fun k => by
    have hcont : Continuous (fun x : ℂ =>
        -(ellipticNome nome ^ k * ellipticThetaCoordinate tau x)) :=
      (continuous_const.mul hCoordCont).neg
    exact hcont.continuousOn) using 1

/-! ## Entirety of the boundary products -/

theorem differentiable_boundaryProductForward {nome tau : ℂ}
    (hnome : ‖ellipticNome nome‖ < 1) :
    Differentiable ℂ (fun z : ℂ => ∏' k : ℕ,
      (1 - ellipticNome nome ^ (k + 1) / ellipticThetaCoordinate tau z)) := by
  have hprod := hasProdLocallyUniformlyOn_ellipticGammaForwardBoundaryFactor
    (nome := nome) (tau := tau) hnome
  have ht := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod)
  have hfac : ∀ k : ℕ, Differentiable ℂ (fun z : ℂ =>
      1 - ellipticNome nome ^ (k + 1) / ellipticThetaCoordinate tau z) := by
    intro k z
    exact (analyticAt_const.sub
      (analyticAt_const.div (analyticAt_ellipticThetaCoordinate tau z)
        (ellipticThetaCoordinate_ne_zero tau z))).differentiableAt
  have hd : ∀ᶠ S : Finset ℕ in atTop,
      DifferentiableOn ℂ (fun z => ∏ k ∈ S, (1 - ellipticNome nome ^ (k + 1) /
        ellipticThetaCoordinate tau z)) Set.univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun k _ => (hfac k).differentiableOn
  intro z
  simpa only [differentiableWithinAt_univ] using
    ht.differentiableOn hd isOpen_univ z (Set.mem_univ z)

theorem differentiable_boundaryProductBackward {nome tau : ℂ}
    (hnome : ‖ellipticNome nome‖ < 1) :
    Differentiable ℂ (fun z : ℂ => ∏' k : ℕ,
      (1 - ellipticNome nome ^ k * ellipticThetaCoordinate tau z)) := by
  have hprod := hasProdLocallyUniformlyOn_ellipticGammaBackwardBoundaryFactor
    (nome := nome) (tau := tau) hnome
  have ht := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod)
  have hfac : ∀ k : ℕ, Differentiable ℂ (fun z : ℂ =>
      1 - ellipticNome nome ^ k * ellipticThetaCoordinate tau z) := by
    intro k z
    exact (analyticAt_const.sub
      (analyticAt_const.mul (analyticAt_ellipticThetaCoordinate tau z))).differentiableAt
  have hd : ∀ᶠ S : Finset ℕ in atTop,
      DifferentiableOn ℂ (fun z => ∏ k ∈ S, (1 - ellipticNome nome ^ k *
        ellipticThetaCoordinate tau z)) Set.univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun k _ => (hfac k).differentiableOn
  intro z
  simpa only [differentiableWithinAt_univ] using
    ht.differentiableOn hd isOpen_univ z (Set.mem_univ z)

theorem differentiable_ellipticGammaForwardBoundaryProduct {tau : ℂ} (htau : 0 < tau.im) :
    Differentiable ℂ (ellipticGammaForwardBoundaryProduct tau) :=
  differentiable_boundaryProductForward (nome := tau) (tau := tau)
    (norm_ellipticNome_lt_one htau)

theorem differentiable_ellipticGammaBackwardBoundaryProduct {tau : ℂ} (htau : 0 < tau.im) :
    Differentiable ℂ (ellipticGammaBackwardBoundaryProduct tau) :=
  differentiable_boundaryProductBackward (nome := tau) (tau := tau)
    (norm_ellipticNome_lt_one htau)

theorem differentiable_ellipticGammaTauForwardBoundaryProduct {sigma tau : ℂ}
    (hsigma : 0 < sigma.im) :
    Differentiable ℂ (ellipticGammaTauForwardBoundaryProduct sigma tau) :=
  differentiable_boundaryProductForward (nome := sigma) (tau := tau)
    (norm_ellipticNome_lt_one hsigma)

theorem differentiable_ellipticGammaTauBackwardBoundaryProduct {sigma tau : ℂ}
    (hsigma : 0 < sigma.im) :
    Differentiable ℂ (ellipticGammaTauBackwardBoundaryProduct sigma tau) :=
  differentiable_boundaryProductBackward (nome := sigma) (tau := tau)
    (norm_ellipticNome_lt_one hsigma)

/-- **The first structural boundary is entire.** -/
theorem differentiable_ellipticGammaMultiplicativeThetaBoundary {tau : ℂ} (htau : 0 < tau.im) :
    Differentiable ℂ (ellipticGammaMultiplicativeThetaBoundary tau) :=
  (differentiable_ellipticGammaForwardBoundaryProduct htau).mul
    (differentiable_ellipticGammaBackwardBoundaryProduct htau)

/-- **The second structural boundary is entire.** -/
theorem differentiable_ellipticGammaMultiplicativeThetaBoundaryTau {sigma tau : ℂ}
    (hsigma : 0 < sigma.im) :
    Differentiable ℂ (ellipticGammaMultiplicativeThetaBoundaryTau sigma tau) :=
  (differentiable_ellipticGammaTauForwardBoundaryProduct hsigma).mul
    (differentiable_ellipticGammaTauBackwardBoundaryProduct hsigma)

/-! ## Analytic-subring packaging -/

local instance ellipticGammaThetaBoundaryUnivDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

/-- The analytic germ of an entire function. -/
def entireAnalyticElem {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    analyticSubring (Set.univ : Set ℂ) :=
  ⟨Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) f,
    ⟨f, by
      rw [Complex.analyticOnNhd_univ_iff_differentiable]
      exact hf, rfl⟩⟩

theorem entireAnalyticElem_coe {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ((entireAnalyticElem hf : analyticSubring (Set.univ : Set ℂ)) :
      Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ)) f := rfl

theorem entireAnalyticElem_congr {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ z, f z = g z) :
    entireAnalyticElem hf = entireAnalyticElem hg := by
  apply Subtype.ext
  rw [entireAnalyticElem_coe, entireAnalyticElem_coe, Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => h z

theorem entireAnalyticElem_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) :
    entireAnalyticElem (hf.mul hg) = entireAnalyticElem hf * entireAnalyticElem hg := by
  apply Subtype.ext
  rw [entireAnalyticElem_coe]
  change Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ)) (f * g) = _
  rw [Germ.coe_mul]
  rfl

theorem addTranslationAnalyticEquiv_entireAnalyticElem (c : ℂ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hshift : Differentiable ℂ (fun z => f (z + c))) :
    addTranslationAnalyticEquiv c (entireAnalyticElem hf) =
      entireAnalyticElem hshift := by
  apply Subtype.ext
  rfl

theorem differentiable_comp_add_const {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (fun z => f (z + c)) :=
  hf.comp (differentiable_id.add_const c)

/-- The first structural boundary as an element of the global analytic germ ring. -/
def ellipticGammaThetaBoundaryAnalytic (tau : ℂ) (htau : 0 < tau.im) :
    analyticSubring (Set.univ : Set ℂ) :=
  entireAnalyticElem (differentiable_ellipticGammaMultiplicativeThetaBoundary htau)

/-- The second structural boundary as an element of the global analytic germ ring. -/
def ellipticGammaThetaBoundaryTauAnalytic (sigma tau : ℂ) (hsigma : 0 < sigma.im) :
    analyticSubring (Set.univ : Set ℂ) :=
  entireAnalyticElem
    (differentiable_ellipticGammaMultiplicativeThetaBoundaryTau (tau := tau) hsigma)

/-- The first structural boundary in the meromorphic germ field. -/
def ellipticGammaThetaBoundaryMero (tau : ℂ) (htau : 0 < tau.im) :
    meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
    (ellipticGammaThetaBoundaryAnalytic tau htau)

/-- The second structural boundary in the meromorphic germ field. -/
def ellipticGammaThetaBoundaryTauMero (sigma tau : ℂ) (hsigma : 0 < sigma.im) :
    meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
    (ellipticGammaThetaBoundaryTauAnalytic sigma tau hsigma)

/-! ## The source equations in the meromorphic germ field -/

theorem ellipticGammaForwardAnalytic_eq (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ellipticGammaForwardAnalytic σ τ hσ hτ =
      entireAnalyticElem (differentiable_ellipticGammaForwardProduct hσ hτ) := Subtype.ext rfl

theorem ellipticGammaBackwardAnalytic_eq (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ellipticGammaBackwardAnalytic σ τ hσ hτ =
      entireAnalyticElem (differentiable_ellipticGammaBackwardProduct hσ hτ) := Subtype.ext rfl

theorem ellipticGammaThetaBoundaryAnalytic_eq_mul (tau : ℂ) (htau : 0 < tau.im) :
    ellipticGammaThetaBoundaryAnalytic tau htau =
      entireAnalyticElem (differentiable_ellipticGammaForwardBoundaryProduct htau) *
        entireAnalyticElem (differentiable_ellipticGammaBackwardBoundaryProduct htau) := by
  rw [ellipticGammaThetaBoundaryAnalytic, ← entireAnalyticElem_mul]
  exact entireAnalyticElem_congr _ _ fun z => rfl

theorem ellipticGammaThetaBoundaryTauAnalytic_eq_mul (sigma tau : ℂ) (hsigma : 0 < sigma.im) :
    ellipticGammaThetaBoundaryTauAnalytic sigma tau hsigma =
      entireAnalyticElem
          (differentiable_ellipticGammaTauForwardBoundaryProduct (tau := tau) hsigma) *
        entireAnalyticElem
          (differentiable_ellipticGammaTauBackwardBoundaryProduct (tau := tau) hsigma) := by
  rw [ellipticGammaThetaBoundaryTauAnalytic, ← entireAnalyticElem_mul]
  exact entireAnalyticElem_congr _ _ fun z => rfl

theorem algebraMap_analyticElem_ne_zero {b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0) :
    algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b ≠ 0 := by
  intro h
  exact hb (IsFractionRing.injective (analyticSubring (Set.univ : Set ℂ))
    (meroField Set.univ) (h.trans (map_zero _).symm))

/-- The field identity behind both source equations. -/
theorem source_div_identity {K : Type*} [Field K] {F B ΘF ΘB TB : K}
    (hΘB : ΘB ≠ 0) (hTB : TB ≠ 0) (hBeq : B = ΘB * TB) :
    (ΘF * F) / TB = (ΘF * ΘB) * (F / B) := by
  rw [hBeq]
  field_simp

set_option maxHeartbeats 800000 in
/-- **The first source equation in the meromorphic germ field**, with no regular-locus
hypothesis. -/
theorem ellipticGammaMero_add_sigma (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    addTranslationMeroEquiv σ (ellipticGammaMero σ τ hσ hτ) =
      ellipticGammaThetaBoundaryMero τ hτ * ellipticGammaMero σ τ hσ hτ := by
  classical
  have hFshift : addTranslationAnalyticEquiv σ (ellipticGammaForwardAnalytic σ τ hσ hτ) =
      entireAnalyticElem (differentiable_ellipticGammaForwardBoundaryProduct hτ) *
        ellipticGammaForwardAnalytic σ τ hσ hτ := by
    rw [ellipticGammaForwardAnalytic_eq,
      addTranslationAnalyticEquiv_entireAnalyticElem σ _
        (differentiable_comp_add_const (differentiable_ellipticGammaForwardProduct hσ hτ) σ),
      ← entireAnalyticElem_mul]
    exact entireAnalyticElem_congr _ _ fun z =>
      ellipticGammaForwardProduct_add_sigma hσ hτ z
  have hBshift : ellipticGammaBackwardAnalytic σ τ hσ hτ =
      entireAnalyticElem (differentiable_ellipticGammaBackwardBoundaryProduct hτ) *
        addTranslationAnalyticEquiv σ (ellipticGammaBackwardAnalytic σ τ hσ hτ) := by
    conv_lhs => rw [ellipticGammaBackwardAnalytic_eq]
    rw [ellipticGammaBackwardAnalytic_eq,
      addTranslationAnalyticEquiv_entireAnalyticElem σ _
        (differentiable_comp_add_const (differentiable_ellipticGammaBackwardProduct hσ hτ) σ),
      ← entireAnalyticElem_mul]
    exact entireAnalyticElem_congr _ _ fun z =>
      ellipticGammaBackwardProduct_eq_boundary_mul_add_sigma hσ hτ z
  have hBne : ellipticGammaBackwardAnalytic σ τ hσ hτ ≠ 0 :=
    ellipticGammaBackwardAnalytic_ne_zero σ τ hσ hτ
  have hΘBne : entireAnalyticElem (differentiable_ellipticGammaBackwardBoundaryProduct hτ) ≠ 0 := by
    intro h
    exact hBne (by rw [hBshift, h, zero_mul])
  have hTBne : addTranslationAnalyticEquiv σ (ellipticGammaBackwardAnalytic σ τ hσ hτ) ≠ 0 := by
    intro h
    exact hBne (by rw [hBshift, h, mul_zero])
  rw [ellipticGammaMero, ellipticGammaThetaBoundaryMero,
    ellipticGammaThetaBoundaryAnalytic_eq_mul, map_div₀,
    addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
    hFshift, map_mul, map_mul]
  refine source_div_identity (algebraMap_analyticElem_ne_zero hΘBne)
    (algebraMap_analyticElem_ne_zero hTBne) ?_
  rw [← map_mul, ← hBshift]

set_option maxHeartbeats 800000 in
/-- **The second source equation in the meromorphic germ field.** -/
theorem ellipticGammaMero_add_tau (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    addTranslationMeroEquiv τ (ellipticGammaMero σ τ hσ hτ) =
      ellipticGammaThetaBoundaryTauMero σ τ hσ * ellipticGammaMero σ τ hσ hτ := by
  classical
  have hFshift : addTranslationAnalyticEquiv τ (ellipticGammaForwardAnalytic σ τ hσ hτ) =
      entireAnalyticElem
          (differentiable_ellipticGammaTauForwardBoundaryProduct (tau := τ) hσ) *
        ellipticGammaForwardAnalytic σ τ hσ hτ := by
    rw [ellipticGammaForwardAnalytic_eq,
      addTranslationAnalyticEquiv_entireAnalyticElem τ _
        (differentiable_comp_add_const (differentiable_ellipticGammaForwardProduct hσ hτ) τ),
      ← entireAnalyticElem_mul]
    exact entireAnalyticElem_congr _ _ fun z =>
      ellipticGammaForwardProduct_add_tau hσ hτ z
  have hBshift : ellipticGammaBackwardAnalytic σ τ hσ hτ =
      entireAnalyticElem
          (differentiable_ellipticGammaTauBackwardBoundaryProduct (tau := τ) hσ) *
        addTranslationAnalyticEquiv τ (ellipticGammaBackwardAnalytic σ τ hσ hτ) := by
    conv_lhs => rw [ellipticGammaBackwardAnalytic_eq]
    rw [ellipticGammaBackwardAnalytic_eq,
      addTranslationAnalyticEquiv_entireAnalyticElem τ _
        (differentiable_comp_add_const (differentiable_ellipticGammaBackwardProduct hσ hτ) τ),
      ← entireAnalyticElem_mul]
    exact entireAnalyticElem_congr _ _ fun z =>
      ellipticGammaBackwardProduct_eq_boundary_mul_add_tau hσ hτ z
  have hBne : ellipticGammaBackwardAnalytic σ τ hσ hτ ≠ 0 :=
    ellipticGammaBackwardAnalytic_ne_zero σ τ hσ hτ
  have hΘBne : entireAnalyticElem
      (differentiable_ellipticGammaTauBackwardBoundaryProduct (tau := τ) hσ) ≠ 0 := by
    intro h
    exact hBne (by rw [hBshift, h, zero_mul])
  have hTBne : addTranslationAnalyticEquiv τ (ellipticGammaBackwardAnalytic σ τ hσ hτ) ≠ 0 := by
    intro h
    exact hBne (by rw [hBshift, h, mul_zero])
  rw [ellipticGammaMero, ellipticGammaThetaBoundaryTauMero,
    ellipticGammaThetaBoundaryTauAnalytic_eq_mul, map_div₀,
    addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
    hFshift, map_mul, map_mul]
  refine source_div_identity (algebraMap_analyticElem_ne_zero hΘBne)
    (algebraMap_analyticElem_ne_zero hTBne) ?_
  rw [← map_mul, ← hBshift]

/-- **The exact period-one law in the meromorphic germ field.** -/
theorem ellipticGammaMero_add_one (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    addTranslationMeroEquiv 1 (ellipticGammaMero σ τ hσ hτ) =
      ellipticGammaMero σ τ hσ hτ := by
  have hF : addTranslationAnalyticEquiv 1 (ellipticGammaForwardAnalytic σ τ hσ hτ) =
      ellipticGammaForwardAnalytic σ τ hσ hτ := by
    conv_rhs => rw [ellipticGammaForwardAnalytic_eq]
    rw [ellipticGammaForwardAnalytic_eq,
      addTranslationAnalyticEquiv_entireAnalyticElem 1 _
        (differentiable_comp_add_const (differentiable_ellipticGammaForwardProduct hσ hτ) 1)]
    exact entireAnalyticElem_congr _ _ fun z => ellipticGammaForwardProduct_add_one σ τ z
  have hB : addTranslationAnalyticEquiv 1 (ellipticGammaBackwardAnalytic σ τ hσ hτ) =
      ellipticGammaBackwardAnalytic σ τ hσ hτ := by
    conv_rhs => rw [ellipticGammaBackwardAnalytic_eq]
    rw [ellipticGammaBackwardAnalytic_eq,
      addTranslationAnalyticEquiv_entireAnalyticElem 1 _
        (differentiable_comp_add_const (differentiable_ellipticGammaBackwardProduct hσ hτ) 1)]
    exact entireAnalyticElem_congr _ _ fun z => ellipticGammaBackwardProduct_add_one σ τ z
  rw [ellipticGammaMero, map_div₀, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap, hF, hB]

end

end GaloisForLFunctions
