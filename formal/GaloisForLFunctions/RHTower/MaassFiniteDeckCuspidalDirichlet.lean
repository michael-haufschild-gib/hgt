import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichletCentral
import GaloisForLFunctions.RHTower.SelbergMaassTraceDirection
import GaloisForLFunctions.HTGeometry.CirclePoincareWirtinger

/-!
# Cuspidal finite-deck Dirichlet carrier

The full finite-deck Dirichlet form contains the constant horocycle mode, so
its cusp embedding cannot be compact.  This module isolates the source-valid
zero-mode condition: every deck coordinate has zero average on each complete
level horocycle.  The resulting completed form carrier is the domain on which
a cusp-tail Poincare estimate can give compactness.
-/

open Complex Filter MeasureTheory ModularGroup Set Topology UpperHalfPlane
open scoped ContDiff MatrixGroups

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceAverage
  SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceDirection
  MaassCongruenceL2

noncomputable section

/-- Every finite-deck coordinate has zero integral on each full level horocycle. -/
def levelCuspZero (N : ℕ) (F : ℍ → DeckSpace N) : Prop :=
  ∀ (q : Deck N) {y : ℝ}, 0 < y → ∀ a : ℝ,
    (∫ x in a..a + (N + 1 : ℕ), F (ofComplex (point x y)) q) = 0

private theorem component_intervalIntegrable (N : ℕ) (F : formPreDomain N)
    (q : Deck N) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => (F : ℍ → DeckSpace N) (ofComplex (point x y)) q)
      volume a (a + (N + 1 : ℕ)) := by
  change IntervalIntegrable
    (fun x : ℝ => component (F : ℍ → DeckSpace N) q
      (ofComplex (point x y)))
    volume a (a + (N + 1 : ℕ))
  exact (slice_continuous (component_c1 F q).continuousOn hy).intervalIntegrable _ _

/-- Every coordinate of a finite-deck form pre-vector closes after the level
period.  Equivariance and `T^(N+1) ∈ Γ(N+1)` make the deck action trivial. -/
theorem component_level_periodic {N : ℕ} (F : formPreDomain N) (q : Deck N)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    component (F : ℍ → DeckSpace N) q (ofComplex (point (x + (N + 1 : ℕ)) y)) =
      component (F : ℍ → DeckSpace N) q (ofComplex (point x y)) := by
  let g : SL2Z := ModularGroup.T ^ ((N + 1 : ℕ) : ℤ)
  have hg : g ∈ CongruenceSubgroup.Gamma (N + 1) := by
    simpa only [Int.natAbs_natCast, g] using
      CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N + 1 : ℕ) (N + 1 : ℕ) (dvd_refl _)
  letI : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
    CongruenceSubgroup.Gamma_normal (N + 1)
  have hdeck : (QuotientGroup.mk g : Deck N) = 1 :=
    (QuotientGroup.eq_one_iff g).mpr hg
  have hp : 0 < (point x y).im := by simpa [point] using hy
  let z : ℍ := ⟨point x y, hp⟩
  have hF := formPreDomain.equivariant F g z
  change (F : ℍ → DeckSpace N) (ModularGroup.T ^ ((N + 1 : ℕ) : ℤ) • z) = _ at hF
  rw [UpperHalfPlane.modular_T_zpow_smul] at hF
  have hF' : (F : ℍ → DeckSpace N) ((N + 1 : ℝ) +ᵥ z) =
      finiteRegularUnitary (QuotientGroup.mk g : Deck N) ((F : ℍ → DeckSpace N) z) := by
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one, Nat.cast_add, Nat.cast_one] using hF
  have hz : ofComplex (point (x + (N + 1 : ℕ)) y) = (N + 1 : ℝ) +ᵥ z := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy)]
    simp [point, z, UpperHalfPlane.coe_vadd]
    ring
  change (F : ℍ → DeckSpace N) (ofComplex (point (x + (N + 1 : ℕ)) y)) q =
    (F : ℍ → DeckSpace N) (ofComplex (point x y)) q
  rw [hz, ofComplex_apply_of_im_pos hp, hF', hdeck]
  simp only [finiteRegularUnitary_apply, mul_one]
  rfl

/-- Although its coordinates close only after the level period, the complete
finite-deck value norm is already one-periodic: `T` only permutes coordinates. -/
theorem form_value_norm_one_periodic {N : ℕ} (F : formPreDomain N)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖(F : ℍ → DeckSpace N) (ofComplex (point (x + 1) y))‖ =
      ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  let z : ℍ := ⟨point x y, hp⟩
  have hF := formPreDomain.equivariant F ModularGroup.T z
  rw [show ModularGroup.T = ModularGroup.T ^ (1 : ℤ) by simp,
    UpperHalfPlane.modular_T_zpow_smul] at hF
  have hF' : (F : ℍ → DeckSpace N) ((1 : ℝ) +ᵥ z) =
      finiteRegularUnitary (QuotientGroup.mk (ModularGroup.T ^ (1 : ℤ)) : Deck N)
        ((F : ℍ → DeckSpace N) z) := by
    simpa only [Int.cast_one] using hF
  have hz : ofComplex (point (x + 1) y) = (1 : ℝ) +ᵥ z := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy)]
    simp [point, z, UpperHalfPlane.coe_vadd]
    ring
  rw [hz, ofComplex_apply_of_im_pos hp, hF']
  exact (finiteRegularUnitary (QuotientGroup.mk (ModularGroup.T ^ (1 : ℤ)) : Deck N)).norm_map _

/-- In the translation chart, deck equivariance is literal unit translation
equivariance.  This is the local identity needed to transport the derivative
energy from a full level period to a unit cusp cell. -/
private theorem chartFun_T_eq_regular {N : ℕ} (F : formPreDomain N)
    (w : ℂ) (hw : 0 < w.im) :
    chartFun (F : ℍ → DeckSpace N) (w + 1) =
      finiteRegularUnitary (QuotientGroup.mk (ModularGroup.T ^ (1 : ℤ)) : Deck N)
        (chartFun (F : ℍ → DeckSpace N) w) := by
  have hw' : 0 < (w + 1).im := by simpa using hw
  have hF := formPreDomain.equivariant F ModularGroup.T (ofComplex w)
  rw [show ModularGroup.T = ModularGroup.T ^ (1 : ℤ) by simp,
    UpperHalfPlane.modular_T_zpow_smul] at hF
  change (F : ℍ → DeckSpace N) (ofComplex (w + 1)) =
    finiteRegularUnitary (QuotientGroup.mk (ModularGroup.T ^ (1 : ℤ)) : Deck N)
      ((F : ℍ → DeckSpace N) (ofComplex w))
  rw [show ofComplex (w + 1) = (1 : ℝ) +ᵥ ofComplex w by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    simp [UpperHalfPlane.coe_vadd]
    ring]
  simpa only [Int.cast_one] using hF

/-- The weighted horizontal derivative has the same finite-deck translation
covariance as the value.  The proof differentiates the actual local chart
equivariance; it does not treat derivative periodicity as an assumption. -/
theorem hypGradX_T_eq_regular {N : ℕ} (F : formPreDomain N)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    hypGradX (F : ℍ → DeckSpace N) (ofComplex (point (x + 1) y)) =
      finiteRegularUnitary (QuotientGroup.mk (ModularGroup.T ^ (1 : ℤ)) : Deck N)
        (hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))) := by
  let U := finiteRegularUnitary (QuotientGroup.mk (ModularGroup.T ^ (1 : ℤ)) : Deck N)
  let L : DeckSpace N →L[ℝ] DeckSpace N :=
    (U.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have hpt : point x y ∈ GaloisForLFunctions.HTGeometry.upperSet := by
    simpa [point, GaloisForLFunctions.HTGeometry.upperSet] using hy
  have hdiff : DifferentiableAt ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) :=
    ((formPreDomain.c1 F).differentiableOn one_ne_zero).differentiableAt
      (GaloisForLFunctions.HTGeometry.isOpen_upperSet.mem_nhds hpt)
  have hlocal : (fun w : ℂ => chartFun (F : ℍ → DeckSpace N) (w + 1)) =ᶠ[𝓝 (point x y)]
      fun w => U (chartFun (F : ℍ → DeckSpace N) w) := by
    filter_upwards [GaloisForLFunctions.HTGeometry.isOpen_upperSet.mem_nhds hpt] with w hw
    exact chartFun_T_eq_regular F w hw
  have hU : HasFDerivAt (fun w : ℂ => L (chartFun (F : ℍ → DeckSpace N) w))
      (L.comp (fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y))) (point x y) :=
    L.hasFDerivAt.comp (point x y) hdiff.hasFDerivAt
  have hshift : HasFDerivAt (fun w : ℂ => chartFun (F : ℍ → DeckSpace N) (w + 1))
      (L.comp (fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y))) (point x y) := by
    apply hU.congr_of_eventuallyEq
    exact hlocal
  have hderiv : fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point (x + 1) y) 1 =
      L (fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) 1) := by
    rw [show point (x + 1) y = point x y + 1 by
      simp [point]
      ring]
    rw [← fderiv_comp_add_right]
    simpa only [ContinuousLinearMap.comp_apply] using congrArg (fun D => D (1 : ℂ)) hshift.fderiv
  unfold hypGradX chartDeriv
  have hp0 : 0 < (point x y).im := by simpa [point] using hy
  have hp1 : 0 < (point (x + 1) y).im := by simpa [point] using hy
  have him0 : (ofComplex (point x y)).im = y := by
    simpa [point] using congrArg UpperHalfPlane.im (ofComplex_apply_of_im_pos hp0)
  have him1 : (ofComplex (point (x + 1) y)).im = y := by
    simpa [point] using congrArg UpperHalfPlane.im (ofComplex_apply_of_im_pos hp1)
  have hcoe0 : ((ofComplex (point x y) : ℍ) : ℂ) = point x y := by
    rw [ofComplex_apply_of_im_pos hp0]
  have hcoe1 : ((ofComplex (point (x + 1) y) : ℍ) : ℂ) = point (x + 1) y := by
    rw [ofComplex_apply_of_im_pos hp1]
  rw [him1, him0, hcoe1, hcoe0]
  change (y : ℂ) • fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point (x + 1) y) 1 =
    U ((y : ℂ) • fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) 1)
  rw [hderiv]
  change (y : ℂ) • U (fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) 1) =
    U ((y : ℂ) • fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) 1)
  exact (U.map_smul _ _).symm

/-- The horizontal hyperbolic-gradient energy is one-periodic despite
coordinate values closing only after the level period. -/
theorem hypGradX_norm_one_periodic {N : ℕ} (F : formPreDomain N)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point (x + 1) y))‖ =
      ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ := by
  rw [hypGradX_T_eq_regular F hy x]
  exact (finiteRegularUnitary
    (QuotientGroup.mk (ModularGroup.T ^ (1 : ℤ)) : Deck N)).norm_map _

theorem hypGradX_normSq_one_periodic {N : ℕ} (F : formPreDomain N)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point (x + 1) y))‖ ^ 2 =
      ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2 := by
  rw [hypGradX_norm_one_periodic F hy x]

/-- The vertical hyperbolic derivative has the same literal unit-translation
covariance as the value and horizontal derivative. -/
theorem hypGradY_T_eq_regular {N : ℕ} (F : formPreDomain N)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    hypGradY (F : ℍ → DeckSpace N) (ofComplex (point (x + 1) y)) =
      finiteRegularUnitary (QuotientGroup.mk (ModularGroup.T ^ (1 : ℤ)) : Deck N)
        (hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))) := by
  let U := finiteRegularUnitary (QuotientGroup.mk (ModularGroup.T ^ (1 : ℤ)) : Deck N)
  let L : DeckSpace N →L[ℝ] DeckSpace N :=
    (U.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have hpt : point x y ∈ GaloisForLFunctions.HTGeometry.upperSet := by
    simpa [point, GaloisForLFunctions.HTGeometry.upperSet] using hy
  have hdiff : DifferentiableAt ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) :=
    ((formPreDomain.c1 F).differentiableOn one_ne_zero).differentiableAt
      (GaloisForLFunctions.HTGeometry.isOpen_upperSet.mem_nhds hpt)
  have hlocal : (fun w : ℂ => chartFun (F : ℍ → DeckSpace N) (w + 1)) =ᶠ[𝓝 (point x y)]
      fun w => U (chartFun (F : ℍ → DeckSpace N) w) := by
    filter_upwards [GaloisForLFunctions.HTGeometry.isOpen_upperSet.mem_nhds hpt] with w hw
    exact chartFun_T_eq_regular F w hw
  have hU : HasFDerivAt (fun w : ℂ => L (chartFun (F : ℍ → DeckSpace N) w))
      (L.comp (fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y))) (point x y) :=
    L.hasFDerivAt.comp (point x y) hdiff.hasFDerivAt
  have hshift : HasFDerivAt (fun w : ℂ => chartFun (F : ℍ → DeckSpace N) (w + 1))
      (L.comp (fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y))) (point x y) := by
    apply hU.congr_of_eventuallyEq
    exact hlocal
  have hderiv : fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point (x + 1) y) Complex.I =
      L (fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) Complex.I) := by
    rw [show point (x + 1) y = point x y + 1 by
      simp [point]
      ring]
    rw [← fderiv_comp_add_right]
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun D => D Complex.I) hshift.fderiv
  unfold hypGradY chartDeriv
  have hp0 : 0 < (point x y).im := by simpa [point] using hy
  have hp1 : 0 < (point (x + 1) y).im := by simpa [point] using hy
  have him0 : (ofComplex (point x y)).im = y := by
    simpa [point] using congrArg UpperHalfPlane.im (ofComplex_apply_of_im_pos hp0)
  have him1 : (ofComplex (point (x + 1) y)).im = y := by
    simpa [point] using congrArg UpperHalfPlane.im (ofComplex_apply_of_im_pos hp1)
  have hcoe0 : ((ofComplex (point x y) : ℍ) : ℂ) = point x y := by
    rw [ofComplex_apply_of_im_pos hp0]
  have hcoe1 : ((ofComplex (point (x + 1) y) : ℍ) : ℂ) = point (x + 1) y := by
    rw [ofComplex_apply_of_im_pos hp1]
  rw [him1, him0, hcoe1, hcoe0]
  change (y : ℂ) • fderiv ℝ (chartFun (F : ℍ → DeckSpace N))
      (point (x + 1) y) Complex.I =
    U ((y : ℂ) • fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) Complex.I)
  rw [hderiv]
  change (y : ℂ) • U (fderiv ℝ (chartFun (F : ℍ → DeckSpace N))
      (point x y) Complex.I) =
    U ((y : ℂ) • fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) Complex.I)
  exact (U.map_smul _ _).symm

/-- The vertical hyperbolic-gradient norm is one-periodic on a finite-deck form. -/
theorem hypGradY_norm_one_periodic {N : ℕ} (F : formPreDomain N)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point (x + 1) y))‖ =
      ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ := by
  rw [hypGradY_T_eq_regular F hy x]
  exact (finiteRegularUnitary
    (QuotientGroup.mk (ModularGroup.T ^ (1 : ℤ)) : Deck N)).norm_map _

theorem hypGradY_normSq_one_periodic {N : ℕ} (F : formPreDomain N)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point (x + 1) y))‖ ^ 2 =
      ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2 := by
  rw [hypGradY_norm_one_periodic F hy x]

/-- The complete finite-deck value energy on a level period is exactly the
level length times its unit-cell energy.  This converts the left side of the
coordinate Poincaré estimate into the physical cusp-cell normalization. -/
theorem value_normSq_interval_level_period {N : ℕ} (F : formPreDomain N)
    {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ),
      ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2)
      = ((N + 1 : ℕ) : ℤ) •
        ∫ x in a..a + 1, ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2 := by
  let G : ℝ → ℝ := fun x => ‖chartFun (F : ℍ → DeckSpace N) (point x y)‖ ^ 2
  have hcont : Continuous G := by
    apply Continuous.pow
    apply Continuous.norm
    apply (formPreDomain.c1 F).continuousOn.comp_continuous
    · change Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I
      fun_prop
    · intro x
      simpa [point, GaloisForLFunctions.HTGeometry.upperSet] using hy
  have hper : Function.Periodic G 1 := by
    intro x
    simpa only [G, chartFun, Function.comp_apply] using
      congrArg (fun r : ℝ => r ^ 2) (form_value_norm_one_periodic F hy x)
  have hint : ∀ s t : ℝ, IntervalIntegrable G volume s t :=
    fun s t => hcont.intervalIntegrable s t
  have h := hper.intervalIntegral_add_zsmul_eq ((N + 1 : ℕ) : ℤ) a hint
  simpa only [G, chartFun, Function.comp_apply, Int.ofNat_eq_natCast,
    Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one,
    zsmul_one, add_assoc] using h

/-- The complete finite-deck horizontal energy has the same exact
level-period/unit-cell identity.  This is obtained from differentiated deck
equivariance, rather than assumed periodicity of the gradient. -/
theorem hypGradX_normSq_interval_level_period {N : ℕ} (F : formPreDomain N)
    {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ),
      ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2)
      = ((N + 1 : ℕ) : ℤ) •
        ∫ x in a..a + 1,
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2 := by
  let G : ℝ → ℝ := fun x => ‖(y : ℂ) •
    fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) 1‖ ^ 2
  have hG : G = fun x =>
      ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2 := by
    funext x
    dsimp [G]
    have hp : 0 < (point x y).im := by simpa [point] using hy
    have him : (ofComplex (point x y)).im = y := by
      simpa [point] using congrArg UpperHalfPlane.im (ofComplex_apply_of_im_pos hp)
    have hcoe : ((ofComplex (point x y) : ℍ) : ℂ) = point x y := by
      rw [ofComplex_apply_of_im_pos hp]
    rw [hypGradX, chartDeriv, him, hcoe]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hderiv : ContinuousOn (fun w : ℂ =>
      fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) w 1)
      GaloisForLFunctions.HTGeometry.upperSet := by
    have h := ContDiffOn.continuousOn_fderiv_of_isOpen (formPreDomain.c1 F)
      GaloisForLFunctions.HTGeometry.isOpen_upperSet le_rfl
    exact h.clm_apply continuousOn_const
  have hcont : Continuous G := by
    apply Continuous.pow
    apply Continuous.norm
    refine (hderiv.comp_continuous ?_ ?_).const_smul (y : ℂ)
    · change Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I
      fun_prop
    · intro x
      simpa [point, GaloisForLFunctions.HTGeometry.upperSet] using hy
  have hper : Function.Periodic G 1 := by
    intro x
    rw [hG]
    exact congrArg (fun r : ℝ => r ^ 2) (hypGradX_norm_one_periodic F hy x)
  have hint : ∀ s t : ℝ, IntervalIntegrable G volume s t :=
    fun s t => hcont.intervalIntegrable s t
  have h := hper.intervalIntegral_add_zsmul_eq ((N + 1 : ℕ) : ℤ) a hint
  simpa only [hG, Int.ofNat_eq_natCast, Int.cast_add, Int.cast_natCast,
    Int.cast_one, Nat.cast_add, Nat.cast_one, zsmul_one, add_assoc] using h

/-- The complete finite-deck vertical energy has the same exact
level-period/unit-cell identity.  It is the vertical counterpart needed for
the mixed cusp current. -/
theorem hypGradY_normSq_interval_level_period {N : ℕ} (F : formPreDomain N)
    {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ),
      ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2)
      = ((N + 1 : ℕ) : ℤ) •
        ∫ x in a..a + 1,
          ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2 := by
  let G : ℝ → ℝ := fun x => ‖(y : ℂ) •
    fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (point x y) Complex.I‖ ^ 2
  have hG : G = fun x =>
      ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2 := by
    funext x
    dsimp [G]
    have hp : 0 < (point x y).im := by simpa [point] using hy
    have him : (ofComplex (point x y)).im = y := by
      simpa [point] using congrArg UpperHalfPlane.im (ofComplex_apply_of_im_pos hp)
    have hcoe : ((ofComplex (point x y) : ℍ) : ℂ) = point x y := by
      rw [ofComplex_apply_of_im_pos hp]
    rw [hypGradY, chartDeriv, him, hcoe]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hderiv : ContinuousOn (fun w : ℂ =>
      fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) w Complex.I)
      GaloisForLFunctions.HTGeometry.upperSet := by
    have h := ContDiffOn.continuousOn_fderiv_of_isOpen (formPreDomain.c1 F)
      GaloisForLFunctions.HTGeometry.isOpen_upperSet le_rfl
    exact h.clm_apply continuousOn_const
  have hcont : Continuous G := by
    apply Continuous.pow
    apply Continuous.norm
    refine (hderiv.comp_continuous ?_ ?_).const_smul (y : ℂ)
    · change Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I
      fun_prop
    · intro x
      simpa [point, GaloisForLFunctions.HTGeometry.upperSet] using hy
  have hper : Function.Periodic G 1 := by
    intro x
    rw [hG]
    exact congrArg (fun r : ℝ => r ^ 2) (hypGradY_norm_one_periodic F hy x)
  have hint : ∀ s t : ℝ, IntervalIntegrable G volume s t :=
    fun s t => hcont.intervalIntegrable s t
  have h := hper.intervalIntegral_add_zsmul_eq ((N + 1 : ℕ) : ℤ) a hint
  simpa only [hG, Int.ofNat_eq_natCast, Int.cast_add, Int.cast_natCast,
    Int.cast_one, Nat.cast_add, Nat.cast_one, zsmul_one, add_assoc] using h

/-- Above height one, the modular cell is exactly its horizontal cusp strip.
This is the geometric entry point for converting period estimates into a
modular-cell tail bound. -/
theorem mem_fd_of_abs_re_le_half_one_le_im {z : ℍ}
    (hre : |z.re| ≤ (1 : ℝ) / 2) (him : 1 ≤ z.im) : z ∈ fd := by
  constructor
  · rw [Complex.normSq_apply]
    change 1 ≤ z.re * z.re + z.im * z.im
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  · exact hre

theorem mem_fd_and_one_le_im_iff {z : ℍ} :
    z ∈ fd ∧ 1 ≤ z.im ↔ |z.re| ≤ (1 : ℝ) / 2 ∧ 1 ≤ z.im := by
  constructor
  · rintro ⟨hz, him⟩
    exact ⟨hz.2, him⟩
  · rintro ⟨hre, him⟩
    exact ⟨mem_fd_of_abs_re_le_half_one_le_im hre him, him⟩

private theorem levelCuspZero_zero (N : ℕ) :
    levelCuspZero N (0 : ℍ → DeckSpace N) := by
  intro q y hy a
  simp

private theorem levelCuspZero_add (N : ℕ) {F G : ℍ → DeckSpace N}
    (hF : F ∈ formPreDomain N) (hG : G ∈ formPreDomain N)
    (hF0 : levelCuspZero N F) (hG0 : levelCuspZero N G) :
    levelCuspZero N (F + G) := by
  intro q y hy a
  have hFi := component_intervalIntegrable N ⟨F, hF⟩ q hy a
  have hGi := component_intervalIntegrable N ⟨G, hG⟩ q hy a
  change (∫ x in a..a + (N + 1 : ℕ),
    F (ofComplex (point x y)) q + G (ofComplex (point x y)) q) = 0
  rw [intervalIntegral.integral_add hFi hGi, hF0 q hy a, hG0 q hy a]
  ring

private theorem levelCuspZero_smul (N : ℕ) (c : ℂ) {F : ℍ → DeckSpace N}
    (hF : levelCuspZero N F) : levelCuspZero N (c • F) := by
  intro q y hy a
  change (∫ x in a..a + (N + 1 : ℕ), c • F (ofComplex (point x y)) q) = 0
  rw [intervalIntegral.integral_smul, hF q hy a, smul_zero]

/-- The finite-deck C¹ Dirichlet pre-domain with its actual cusp-zero Fourier
condition.  It contains the exceptional source and removes precisely the
horocycle zero mode which obstructs cusp compactness. -/
def cuspidalFormPreDomain (N : ℕ) : Submodule ℂ (ℍ → DeckSpace N) where
  carrier := {F | F ∈ formPreDomain N ∧ levelCuspZero N F}
  zero_mem' := ⟨(formPreDomain N).zero_mem, levelCuspZero_zero N⟩
  add_mem' := by
    intro F G hF hG
    exact ⟨add_mem hF.1 hG.1, levelCuspZero_add N hF.1 hG.1 hF.2 hG.2⟩
  smul_mem' := by
    intro c F hF
    exact ⟨(formPreDomain N).smul_mem c hF.1, levelCuspZero_smul N c hF.2⟩

namespace cuspidalFormPreDomain

/-- Forgetting the cusp condition. -/
def toFormPreDomain (N : ℕ) : cuspidalFormPreDomain N →ₗ[ℂ] formPreDomain N :=
  { toFun := fun F => ⟨F.1, F.2.1⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp] theorem coe_toFormPreDomain {N : ℕ} (F : cuspidalFormPreDomain N) :
    ((toFormPreDomain N F : formPreDomain N) : ℍ → DeckSpace N) = F := rfl

theorem c1 {N : ℕ} (F : cuspidalFormPreDomain N) : IsChartC1 (F : ℍ → DeckSpace N) :=
  formPreDomain.c1 (toFormPreDomain N F)

theorem cusp_zero {N : ℕ} (F : cuspidalFormPreDomain N) :
    levelCuspZero N (F : ℍ → DeckSpace N) := F.2.2

theorem memLp {N : ℕ} (F : cuspidalFormPreDomain N) :
    MemLp (F : ℍ → DeckSpace N) 2 cellMeasure :=
  formPreDomain.memLp (toFormPreDomain N F)

theorem memLp_gradX {N : ℕ} (F : cuspidalFormPreDomain N) :
    MemLp (hypGradX (F : ℍ → DeckSpace N)) 2 cellMeasure :=
  formPreDomain.memLp_gradX (toFormPreDomain N F)

theorem memLp_gradY {N : ℕ} (F : cuspidalFormPreDomain N) :
    MemLp (hypGradY (F : ℍ → DeckSpace N)) 2 cellMeasure :=
  formPreDomain.memLp_gradY (toFormPreDomain N F)

end cuspidalFormPreDomain

/-- Sharp horizontal Poincaré estimate on one complete cusp period for a
cuspidal finite-deck pre-vector.  The zero Fourier mode is eliminated by the
literal cusp condition; no spectral assertion is used. -/
theorem component_wirtinger_slice {N : ℕ} (F : cuspidalFormPreDomain N) (q : Deck N)
    {y : ℝ} (hy : 0 < y) (a : ℝ) :
    ((N + 1 : ℝ)⁻¹ * ∫ x in a..a + (N + 1 : ℕ),
      ‖component (F : ℍ → DeckSpace N) q (ofComplex (point x y))‖ ^ 2)
      ≤ (((N + 1 : ℝ) / (2 * Real.pi)) ^ 2) *
        ((N + 1 : ℝ)⁻¹ * ∫ x in a..a + (N + 1 : ℕ),
          ‖directional 1
            (GaloisForLFunctions.HTGeometry.chartFun
              (component (F : ℍ → DeckSpace N) q)) (point x y)‖ ^ 2) := by
  have hLpos : 0 < (N + 1 : ℝ) := by positivity
  have hab : a < a + (N + 1 : ℝ) := by linarith
  have hC1 := component_c1 (cuspidalFormPreDomain.toFormPreDomain N F) q
  change ContDiffOn ℝ 1
    (GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q))
    {z : ℂ | 0 < z.im} at hC1
  have hderiv : ∀ x ∈ Set.uIcc a (a + (N + 1 : ℝ)),
      HasDerivAt
        (fun t => GaloisForLFunctions.HTGeometry.chartFun
          (component (F : ℍ → DeckSpace N) q) (point t y))
        (directional 1
          (GaloisForLFunctions.HTGeometry.chartFun
            (component (F : ℍ → DeckSpace N) q)) (point x y)) x := by
    intro x _
    exact slice_horizontal hC1 hy x
  have hderiv_cont : ContinuousOn
      (fun x => directional 1
        (GaloisForLFunctions.HTGeometry.chartFun
          (component (F : ℍ → DeckSpace N) q)) (point x y))
      (Set.uIcc a (a + (N + 1 : ℝ))) := by
    exact (slice_continuous
      (directional_contDiffOn hC1 (m := 0) (by simp) 1).continuousOn hy).continuousOn
  have hper :
      GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q)
        (point (a + (N + 1 : ℝ)) y) =
      GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q)
        (point a y) := by
    change component (F : ℍ → DeckSpace N) q
      (ofComplex (point (a + (N + 1 : ℝ)) y)) =
      component (F : ℍ → DeckSpace N) q (ofComplex (point a y))
    simpa only [cuspidalFormPreDomain.coe_toFormPreDomain, Nat.cast_add, Nat.cast_one] using
      component_level_periodic (cuspidalFormPreDomain.toFormPreDomain N F) q hy a
  have hmean :
      (∫ x in a..a + (N + 1 : ℝ),
        GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q)
          (point x y)) = 0 := by
    simpa only [GaloisForLFunctions.HTGeometry.chartFun, Function.comp_apply,
      component, Nat.cast_add, Nat.cast_one] using cuspidalFormPreDomain.cusp_zero F q hy a
  have h := GaloisForLFunctions.HTGeometry.wirtinger_intervalIntegral hab hderiv hderiv_cont hper
  rw [hmean] at h
  simpa only [smul_zero, norm_zero, pow_two, mul_zero, sub_zero, add_sub_cancel_left,
    GaloisForLFunctions.HTGeometry.chartFun, Function.comp_apply,
    Nat.cast_add, Nat.cast_one] using h

/-- The slice derivative in `component_wirtinger_slice` is exactly the
horizontal finite-deck form coordinate after multiplication by the height. -/
theorem component_directional_mul_height_eq_hypGradX {N : ℕ}
    (F : cuspidalFormPreDomain N) (q : Deck N) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    (y : ℂ) * directional 1
      (GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q))
        (point x y) = hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  have h := component_hypGradX (cuspidalFormPreDomain.toFormPreDomain N F) q
    (ofComplex (point x y))
  change GaloisForLFunctions.HTGeometry.hypGradX
    (component ((cuspidalFormPreDomain.toFormPreDomain N F : formPreDomain N) :
      ℍ → DeckSpace N) q) (ofComplex (point x y)) = _ at h
  rw [GaloisForLFunctions.HTGeometry.hypGradX] at h
  rw [ofComplex_apply_of_im_pos hp] at h
  rw [ofComplex_apply_of_im_pos hp]
  simpa [cuspidalFormPreDomain.coe_toFormPreDomain,
    GaloisForLFunctions.HTGeometry.chartDeriv, directional, point,
    ofComplex_apply_of_im_pos hp] using h

/-- Pointwise norm form of the horizontal derivative identity. -/
theorem component_directional_normSq_eq_height_invSq_hypGradX {N : ℕ}
    (F : cuspidalFormPreDomain N) (q : Deck N) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖directional 1
      (GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q))
        (point x y)‖ ^ 2 = y⁻¹ ^ 2 *
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ 2 := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have h := component_directional_mul_height_eq_hypGradX F q hy x
  have hnorm : ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ =
      y * ‖directional 1
        (GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q))
          (point x y)‖ := by
    rw [← h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have hsq : ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ 2 =
      y ^ 2 * ‖directional 1
        (GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q))
          (point x y)‖ ^ 2 := by
    rw [hnorm, mul_pow]
  rw [hsq]
  field_simp

/-- Sharp one-period cusp estimate in the finite-deck horizontal form
coordinate.  Its `y⁻²` factor is the mechanism which suppresses cusp escape. -/
theorem component_wirtinger_slice_hypGradX {N : ℕ} (F : cuspidalFormPreDomain N)
    (q : Deck N) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    ((N + 1 : ℝ)⁻¹ * ∫ x in a..a + (N + 1 : ℕ),
      ‖component (F : ℍ → DeckSpace N) q (ofComplex (point x y))‖ ^ 2)
      ≤ (((N + 1 : ℝ) / (2 * Real.pi)) ^ 2) * y⁻¹ ^ 2 *
        ((N + 1 : ℝ)⁻¹ * ∫ x in a..a + (N + 1 : ℕ),
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ 2) := by
  have h := component_wirtinger_slice F q hy a
  have hint :
      (∫ x in a..a + (N + 1 : ℕ),
        ‖directional 1
          (GaloisForLFunctions.HTGeometry.chartFun
            (component (F : ℍ → DeckSpace N) q)) (point x y)‖ ^ 2) =
      y⁻¹ ^ 2 * ∫ x in a..a + (N + 1 : ℕ),
        ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    exact component_directional_normSq_eq_height_invSq_hypGradX F q hy x
  rw [hint] at h
  nlinarith

/-- The cuspidal form embedding into the same value/gradient Hilbert triple. -/
def cuspidalFormEmbeddingMap (N : ℕ) :
    cuspidalFormPreDomain N →ₗ[ℂ] FormTriple N :=
  (formEmbeddingMap N).comp (cuspidalFormPreDomain.toFormPreDomain N)

/-- Completion of the cusp-zero form inside the finite-deck form triple. -/
def cuspidalFormDomainClosure (N : ℕ) : Submodule ℂ (FormTriple N) :=
  (LinearMap.range (cuspidalFormEmbeddingMap N)).topologicalClosure

/-- Completed cusp-zero finite-deck Dirichlet form. -/
abbrev CuspidalFormDomain (N : ℕ) := ↥(cuspidalFormDomainClosure N)

instance (N : ℕ) : CompleteSpace (CuspidalFormDomain N) :=
  inferInstanceAs (CompleteSpace ↥(LinearMap.range (cuspidalFormEmbeddingMap N)).topologicalClosure)

/-- A cuspidal pre-vector in its completed cusp-zero form domain. -/
def toCuspidalFormDomain (N : ℕ) (F : cuspidalFormPreDomain N) : CuspidalFormDomain N :=
  ⟨cuspidalFormEmbeddingMap N F, subset_closure ⟨F, rfl⟩⟩

theorem cuspidalFormDomainClosure_le_formDomainClosure (N : ℕ) :
    cuspidalFormDomainClosure N ≤ formDomainClosure N := by
  refine Submodule.topologicalClosure_mono ?_
  rintro _ ⟨F, rfl⟩
  exact ⟨cuspidalFormPreDomain.toFormPreDomain N F, rfl⟩

/-- The cusp-zero completion embeds into the original completed form. -/
def cuspidalFormDomainToFormDomain (N : ℕ) :
    CuspidalFormDomain N →ₗ[ℂ] FormDomain N where
  toFun v := ⟨v.1, cuspidalFormDomainClosure_le_formDomainClosure N v.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cuspidalFormDomainToFormDomain_injective (N : ℕ) :
    Function.Injective (cuspidalFormDomainToFormDomain N) := by
  intro u v h
  apply Subtype.ext
  exact congrArg (fun w : FormDomain N => (w : FormTriple N)) h

/-- First-coordinate inclusion of the completed cusp-zero form into finite-deck `L²`. -/
def cuspidalFormInclusion (N : ℕ) : CuspidalFormDomain N →L[ℂ] DeckL2 N :=
  (PiLp.proj 2 (fun _ : Fin 3 => DeckL2 N) 0).comp
    (cuspidalFormDomainClosure N).subtypeL

theorem cuspidalFormInclusion_injective (N : ℕ) :
    Function.Injective (cuspidalFormInclusion N) := by
  intro u v h
  apply cuspidalFormDomainToFormDomain_injective N
  apply formInclusion_injective N
  change cuspidalFormInclusion N u = cuspidalFormInclusion N v
  exact h

section Exceptional

variable (N : ℕ) (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)

/-- Every exceptional finite-deck source coordinate satisfies the cusp-zero
condition at every height, so the source enters the cuspidal form carrier. -/
theorem sourceVector_levelCuspZero : levelCuspZero N (sourceVector N f) := by
  intro q y hy a
  change (∫ x in a..a + (N + 1 : ℕ),
    (quotientForm N f q).1.1 (ofComplex (point x y))) = 0
  exact component_mean_zero N lam f q hy a

/-- The actual exceptional source belongs to the cusp-zero pre-domain. -/
def sourceInCuspidalFormPreDomain : cuspidalFormPreDomain N :=
  ⟨sourceVector N f, (sourceInFormPreDomain N lam f).property,
    sourceVector_levelCuspZero N lam f⟩

/-- The actual exceptional source in the completed cusp-zero form domain. -/
def sourceCuspidalFormVector : CuspidalFormDomain N :=
  toCuspidalFormDomain N (sourceInCuspidalFormPreDomain N lam f)

/-- The cuspidal-form inclusion realizes the literal quotient source. -/
theorem cuspidalFormInclusion_sourceCuspidalFormVector :
    cuspidalFormInclusion N (sourceCuspidalFormVector N lam f) = sourceLp N f := by
  change toDeckL2 (sourceVector N f) (formPreDomain.memLp (sourceInFormPreDomain N lam f)) =
    sourceLp N f
  exact formInclusion_sourceFormVector N lam f

end Exceptional

end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
