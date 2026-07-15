import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary

/-!
# Finite clock shadows are exactly descent anomalies

A constrained hypertranscendental source can have a homogeneous tangent that realizes every
finite clock observation.  In that situation no nonzero operator on a finite observation space
can be an exact descent of the source constraint.  More sharply, the whole range of every proposed
finite shadow is exactly the range of its failure to intertwine, restricted to genuine source
solutions.

This upgrades the scalar finite-conormal no-go to arbitrary finite linear shadows and identifies
the positive object left by the no-go: the source-to-clock descent anomaly.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K V O : Type*}
  [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup O] [Module K O]

/-- Failure of a proposed finite shadow to be the exact descent of a source constraint. -/
def clockDescentAnomaly
    (source : V →ₗ[K] V) (observe : V →ₗ[K] O) (shadow : O →ₗ[K] O) :
    V →ₗ[K] O :=
  shadow.comp observe - observe.comp source

@[simp] theorem clockDescentAnomaly_apply
    (source : V →ₗ[K] V) (observe : V →ₗ[K] O) (shadow : O →ₗ[K] O) (v : V) :
    clockDescentAnomaly source observe shadow v =
      shadow (observe v) - observe (source v) :=
  rfl

/-- On a space of genuine homogeneous source variations, the descent anomaly is exactly the
proposed finite shadow of the observed variation. -/
theorem clockDescentAnomaly_on_sourceKernel
    (source : V →ₗ[K] V) (observe : V →ₗ[K] O) (shadow : O →ₗ[K] O)
    (W : Submodule K V) (hW : W ≤ LinearMap.ker source) (w : W) :
    clockDescentAnomaly source observe shadow w.1 = shadow (observe w.1) := by
  have hw : source w.1 = 0 := LinearMap.mem_ker.mp (hW w.2)
  simp [clockDescentAnomaly, hw]

/-- **Exact descent-anomaly range law.**  If genuine source solutions realize every finite
observation, then the whole range of a proposed finite shadow is exactly the range of its descent
anomaly on those solutions.  Thus none of the shadow's nonzero content descends from the source;
all of it is comparison failure. -/
theorem range_clockDescentAnomaly_domRestrict_eq_range_shadow
    (source : V →ₗ[K] V) (observe : V →ₗ[K] O) (shadow : O →ₗ[K] O)
    (W : Submodule K V) (hW : W ≤ LinearMap.ker source)
    (hsurj : Function.Surjective (observe.domRestrict W)) :
    LinearMap.range ((clockDescentAnomaly source observe shadow).domRestrict W) =
      LinearMap.range shadow := by
  apply le_antisymm
  · rintro y ⟨w, rfl⟩
    refine ⟨observe w.1, ?_⟩
    exact (clockDescentAnomaly_on_sourceKernel source observe shadow W hW w).symm
  · rintro y ⟨x, rfl⟩
    obtain ⟨w, hw⟩ := hsurj x
    change observe w.1 = x at hw
    refine ⟨w, ?_⟩
    change clockDescentAnomaly source observe shadow w.1 = shadow x
    rw [clockDescentAnomaly_on_sourceKernel source observe shadow W hW w, hw]

/-- If the comparison anomaly vanishes on finite-observably free source solutions, its finite
shadow is zero. -/
theorem finiteShadow_eq_zero_of_anomaly_eq_zero_on_sourceKernel
    (source : V →ₗ[K] V) (observe : V →ₗ[K] O) (shadow : O →ₗ[K] O)
    (W : Submodule K V) (hW : W ≤ LinearMap.ker source)
    (hsurj : Function.Surjective (observe.domRestrict W))
    (hzero : ∀ w : W, clockDescentAnomaly source observe shadow w.1 = 0) :
    shadow = 0 := by
  ext y
  change shadow y = 0
  obtain ⟨w, hw⟩ := hsurj y
  change observe w.1 = y at hw
  have hz := hzero w
  rw [clockDescentAnomaly_on_sourceKernel source observe shadow W hW w, hw] at hz
  exact hz

/-- **No exact finite descent.**  Exact source-to-clock intertwining forces every finite shadow to
vanish whenever homogeneous source solutions realize all finite observations. -/
theorem finiteShadow_eq_zero_of_intertwines
    (source : V →ₗ[K] V) (observe : V →ₗ[K] O) (shadow : O →ₗ[K] O)
    (W : Submodule K V) (hW : W ≤ LinearMap.ker source)
    (hsurj : Function.Surjective (observe.domRestrict W))
    (hintertwines : observe.comp source = shadow.comp observe) :
    shadow = 0 := by
  apply finiteShadow_eq_zero_of_anomaly_eq_zero_on_sourceKernel
    source observe shadow W hW hsurj
  intro w
  have hi := LinearMap.congr_fun hintertwines w.1
  have hw : source w.1 = 0 := LinearMap.mem_ker.mp (hW w.2)
  simpa [clockDescentAnomaly, hw] using hi.symm

/-- Restriction of the infinite clock packet to a finite coordinate window. -/
def tateClockFiniteObservation (s : Finset ℕ) :
    (ℕ → K) →ₗ[K] (s → K) where
  toFun p i := p i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tateClockFiniteObservation_domRestrict_surjective
    (W : Submodule K (ℕ → K)) (hW : TateClockFiniteObservableSurjective W)
    (s : Finset ℕ) :
    Function.Surjective ((tateClockFiniteObservation s).domRestrict W) :=
  hW s

/-- **HT clock specialization.**  On every finite clock window, the proposed shadow range equals
the range of the descent anomaly carried by admissible source variations. -/
theorem tateClockFiniteShadow_range_eq_descentAnomaly
    (source : (ℕ → K) →ₗ[K] (ℕ → K)) (s : Finset ℕ)
    (shadow : (s → K) →ₗ[K] (s → K))
    (W : Submodule K (ℕ → K)) (hker : W ≤ LinearMap.ker source)
    (hW : TateClockFiniteObservableSurjective W) :
    LinearMap.range
        ((clockDescentAnomaly source (tateClockFiniteObservation s) shadow).domRestrict W) =
      LinearMap.range shadow :=
  range_clockDescentAnomaly_domRestrict_eq_range_shadow
    source (tateClockFiniteObservation s) shadow W hker
      (tateClockFiniteObservation_domRestrict_surjective W hW s)

/-! ### Covariance under faithful clock charts -/

section ChartCovariance

variable {V' O' : Type*}
  [AddCommGroup V'] [Module K V']
  [AddCommGroup O'] [Module K O']

/-- The source constraint written in an invertible source chart. -/
def clockSourceInChart (eV : V ≃ₗ[K] V') (source : V →ₗ[K] V) :
    V' →ₗ[K] V' :=
  eV.toLinearMap.comp (source.comp eV.symm.toLinearMap)

/-- A finite observation written in invertible source and observable charts. -/
def clockObservationInChart
    (eV : V ≃ₗ[K] V') (eO : O ≃ₗ[K] O') (observe : V →ₗ[K] O) :
    V' →ₗ[K] O' :=
  eO.toLinearMap.comp (observe.comp eV.symm.toLinearMap)

/-- A proposed finite shadow written in an invertible observable chart. -/
def clockShadowInChart (eO : O ≃ₗ[K] O') (shadow : O →ₗ[K] O) :
    O' →ₗ[K] O' :=
  eO.toLinearMap.comp (shadow.comp eO.symm.toLinearMap)

/-- **Faithful-chart covariance.**  The clock-descent anomaly is conjugated, rather than changed,
by invertible source and observable charts.  Thus its comparison content is intrinsic at the
finite linear level and cannot be manufactured by a change of representation. -/
theorem clockDescentAnomaly_inChart
    (eV : V ≃ₗ[K] V') (eO : O ≃ₗ[K] O')
    (source : V →ₗ[K] V) (observe : V →ₗ[K] O) (shadow : O →ₗ[K] O) :
    clockDescentAnomaly (clockSourceInChart eV source)
        (clockObservationInChart eV eO observe) (clockShadowInChart eO shadow) =
      eO.toLinearMap.comp
        ((clockDescentAnomaly source observe shadow).comp eV.symm.toLinearMap) := by
  ext v
  simp [clockDescentAnomaly, clockSourceInChart, clockObservationInChart,
    clockShadowInChart]

end ChartCovariance

/-! ### Curvature across observable resolutions -/

section ShadowCurvature

variable {O₀ O₁ : Type*}
  [AddCommGroup O₀] [Module K O₀]
  [AddCommGroup O₁] [Module K O₁]

/-- Failure of proposed clock shadows to commute with truncation of observations.  The clock index
is an observable resolution, not a time parameter. -/
def clockShadowCurvature
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (truncate : O₁ →ₗ[K] O₀) : O₁ →ₗ[K] O₀ :=
  truncate.comp shadow₁ - shadow₀.comp truncate

/-- Failure of source-to-shadow anomalies to commute with truncation. -/
def clockAnomalyCoherenceDefect
    (source : V →ₗ[K] V)
    (observe₀ : V →ₗ[K] O₀) (observe₁ : V →ₗ[K] O₁)
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (truncate : O₁ →ₗ[K] O₀) : V →ₗ[K] O₀ :=
  truncate.comp (clockDescentAnomaly source observe₁ shadow₁) -
    clockDescentAnomaly source observe₀ shadow₀

/-- **Clock-descent Bianchi identity.**  When observations themselves truncate compatibly, the
incoherence of source-to-shadow anomalies is exactly the shadow curvature observed one level
higher:

`p α₁ - α₀ = (p T₁ - T₀ p) q₁`.

Thus failure of anomaly coherence is not an independent error term. -/
theorem clockAnomalyCoherenceDefect_eq_shadowCurvature_comp
    (source : V →ₗ[K] V)
    (observe₀ : V →ₗ[K] O₀) (observe₁ : V →ₗ[K] O₁)
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (truncate : O₁ →ₗ[K] O₀)
    (hobserve : truncate.comp observe₁ = observe₀) :
    clockAnomalyCoherenceDefect source observe₀ observe₁ shadow₀ shadow₁ truncate =
      (clockShadowCurvature shadow₀ shadow₁ truncate).comp observe₁ := by
  ext v
  have ho_v := LinearMap.congr_fun hobserve v
  have ho_sv := LinearMap.congr_fun hobserve (source v)
  simp only [LinearMap.comp_apply] at ho_v ho_sv
  simp [clockAnomalyCoherenceDefect, clockShadowCurvature, clockDescentAnomaly,
    LinearMap.comp_apply, map_sub, ho_v, ho_sv]

/-- **Exact curvature-range law.**  If source variations realize all higher-resolution
observations, the whole shadow-curvature range is exactly the range of anomaly incoherence on
those variations. -/
theorem range_clockAnomalyCoherenceDefect_domRestrict_eq_range_shadowCurvature
    (source : V →ₗ[K] V)
    (observe₀ : V →ₗ[K] O₀) (observe₁ : V →ₗ[K] O₁)
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (truncate : O₁ →ₗ[K] O₀)
    (hobserve : truncate.comp observe₁ = observe₀)
    (W : Submodule K V) (hsurj : Function.Surjective (observe₁.domRestrict W)) :
    LinearMap.range
        ((clockAnomalyCoherenceDefect source observe₀ observe₁ shadow₀ shadow₁ truncate).domRestrict W) =
      LinearMap.range (clockShadowCurvature shadow₀ shadow₁ truncate) := by
  rw [clockAnomalyCoherenceDefect_eq_shadowCurvature_comp
    source observe₀ observe₁ shadow₀ shadow₁ truncate hobserve]
  apply le_antisymm
  · rintro y ⟨w, rfl⟩
    exact ⟨observe₁ w.1, rfl⟩
  · rintro y ⟨x, rfl⟩
    obtain ⟨w, hw⟩ := hsurj x
    change observe₁ w.1 = x at hw
    refine ⟨w, ?_⟩
    change clockShadowCurvature shadow₀ shadow₁ truncate (observe₁ w.1) =
      clockShadowCurvature shadow₀ shadow₁ truncate x
    rw [hw]

/-- **Gauge additivity of clock curvature.**  Changing a finite shadow by a correction changes
its curvature by the curvature of that correction.  This is the exact coboundary law behind any
calibrated gauge quotient; the nontrivial research content must enter through which corrections
the source calibration permits. -/
theorem clockShadowCurvature_add
    (shadow₀ gauge₀ : O₀ →ₗ[K] O₀) (shadow₁ gauge₁ : O₁ →ₗ[K] O₁)
    (truncate : O₁ →ₗ[K] O₀) :
    clockShadowCurvature (shadow₀ + gauge₀) (shadow₁ + gauge₁) truncate =
      clockShadowCurvature shadow₀ shadow₁ truncate +
        clockShadowCurvature gauge₀ gauge₁ truncate := by
  ext v
  simp [clockShadowCurvature, LinearMap.comp_apply, map_add, add_sub_add_comm]

/-- **Constraint-algebra Leibniz law.**  Clock curvature is a derivation under composition of
finite shadows:

`κ(T ∘ U) = κ(T) ∘ U₁ + T₀ ∘ κ(U)`.

Thus the boundary datum belongs to the whole algebra of source operations, not merely to one
chosen operator. -/
theorem clockShadowCurvature_comp_shadow
    (left₀ right₀ : O₀ →ₗ[K] O₀) (left₁ right₁ : O₁ →ₗ[K] O₁)
    (truncate : O₁ →ₗ[K] O₀) :
    clockShadowCurvature (left₀.comp right₀) (left₁.comp right₁) truncate =
      (clockShadowCurvature left₀ left₁ truncate).comp right₁ +
        left₀.comp (clockShadowCurvature right₀ right₁ truncate) := by
  ext v
  simp [clockShadowCurvature, LinearMap.comp_apply, map_sub]

/-- Vanishing clock curvature is exactly compatibility of the two shadows with truncation. -/
theorem clockShadowCurvature_eq_zero_iff
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (truncate : O₁ →ₗ[K] O₀) :
    clockShadowCurvature shadow₀ shadow₁ truncate = 0 ↔
      truncate.comp shadow₁ = shadow₀.comp truncate := by
  simp only [clockShadowCurvature, sub_eq_zero]

section CurvatureCocycle

variable {O₂ : Type*} [AddCommGroup O₂] [Module K O₂]

/-- **Three-resolution curvature cocycle.**  Curvature across a composite truncation is the sum of
the transported curvatures across its two stages.  This is the exact cocycle law needed before a
calibrated curvature class can be defined on the whole clock tower. -/
theorem clockShadowCurvature_comp
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (shadow₂ : O₂ →ₗ[K] O₂)
    (truncate₀₁ : O₁ →ₗ[K] O₀) (truncate₁₂ : O₂ →ₗ[K] O₁) :
    clockShadowCurvature shadow₀ shadow₂ (truncate₀₁.comp truncate₁₂) =
      truncate₀₁.comp (clockShadowCurvature shadow₁ shadow₂ truncate₁₂) +
        (clockShadowCurvature shadow₀ shadow₁ truncate₀₁).comp truncate₁₂ := by
  ext v
  simp [clockShadowCurvature, LinearMap.comp_apply, map_sub]

end CurvatureCocycle

end ShadowCurvature

/-! ### Linear integration fiber of a prescribed curvature -/

section IntegrationFiber

variable {P C : Type*}
  [AddCommGroup P] [Module K P]
  [AddCommGroup C] [Module K C]

/-- The linear model of global primitives realizing one prescribed clock curvature.  In the
nonlinear theory this fiber is replaced by a derived integration stack. -/
def clockIntegrationFiber (integrate : P →ₗ[K] C) (curvature : C) :=
  {primitive : P // integrate primitive = curvature}

/-- A prescribed curvature has a global primitive exactly when it belongs to the range of the
integration map.  This is the linear skeleton of continuation versus integration failure. -/
theorem nonempty_clockIntegrationFiber_iff_mem_range
    (integrate : P →ₗ[K] C) (curvature : C) :
    Nonempty (clockIntegrationFiber integrate curvature) ↔
      curvature ∈ LinearMap.range integrate := by
  constructor
  · rintro ⟨primitive, hprimitive⟩
    exact ⟨primitive, hprimitive⟩
  · rintro ⟨primitive, hprimitive⟩
    exact ⟨⟨primitive, hprimitive⟩⟩

/-- Once one primitive exists, every other primitive differs from it by a unique element of the
kernel.  Thus continuation failure and boundary-condition ambiguity are respectively emptiness
and the kernel torsor of one integration fiber. -/
def clockIntegrationFiberEquivKernel
    (integrate : P →ₗ[K] C) (curvature : C)
    (base : clockIntegrationFiber integrate curvature) :
    clockIntegrationFiber integrate curvature ≃ LinearMap.ker integrate where
  toFun primitive := ⟨primitive.1 - base.1, by
    rw [LinearMap.mem_ker, map_sub, primitive.2, base.2, sub_self]⟩
  invFun gauge := ⟨base.1 + gauge.1, by
    rw [map_add, base.2, LinearMap.mem_ker.mp gauge.2, add_zero]⟩
  left_inv primitive := by
    apply Subtype.ext
    simp
  right_inv gauge := by
    apply Subtype.ext
    simp

end IntegrationFiber

/-! ### Coherence along the finite clock tower -/

section TruncationCoherence

variable {O₀ O₁ : Type*}
  [AddCommGroup O₀] [Module K O₀]
  [AddCommGroup O₁] [Module K O₁]

/-- **Clock-tower coherence.**  Compatible observations and proposed shadows force their descent
anomalies to be compatible under truncation.  Therefore the anomaly family is determined by the
source comparison data; it is not an independently chosen pro-object. -/
theorem clockDescentAnomaly_truncate
    (source : V →ₗ[K] V)
    (observe₀ : V →ₗ[K] O₀) (observe₁ : V →ₗ[K] O₁)
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (truncate : O₁ →ₗ[K] O₀)
    (hobserve : truncate.comp observe₁ = observe₀)
    (hshadow : truncate.comp shadow₁ = shadow₀.comp truncate) :
    truncate.comp (clockDescentAnomaly source observe₁ shadow₁) =
      clockDescentAnomaly source observe₀ shadow₀ := by
  ext v
  have ho_v := LinearMap.congr_fun hobserve v
  have ho_sv := LinearMap.congr_fun hobserve (source v)
  have hs_ov := LinearMap.congr_fun hshadow (observe₁ v)
  simp only [LinearMap.comp_apply] at ho_v ho_sv hs_ov ⊢
  simp [clockDescentAnomaly, map_sub, hs_ov, ho_v, ho_sv]

end TruncationCoherence

/-! ### Detection after quotienting negligible effects -/

section QuotientDetection

variable {Q : Type*} [AddCommGroup Q] [Module K Q]

/-- **Quotient-shadow collapse.**  Suppose a quotient carries a proposed finite shadow, source
solutions realize every quotient observation, and the source-to-clock descent anomaly lands in
the quotient kernel.  Then the quotient shadow is zero.

This is the common linear interface for quotienting compact, finite-support, radical, or other
declared-negligible effects: a nonzero shadow cannot remain after the entire anomaly has been
erased. -/
theorem quotientShadow_eq_zero_of_anomaly_mem_kernel
    (source : V →ₗ[K] V) (observe : V →ₗ[K] O)
    (shadow : O →ₗ[K] O) (quotientShadow : Q →ₗ[K] Q)
    (quotient : O →ₗ[K] Q)
    (hshadow : quotient.comp shadow = quotientShadow.comp quotient)
    (W : Submodule K V) (hW : W ≤ LinearMap.ker source)
    (hsurj : Function.Surjective ((quotient.comp observe).domRestrict W))
    (hvanish : ∀ w : W,
      clockDescentAnomaly source observe shadow w.1 ∈ LinearMap.ker quotient) :
    quotientShadow = 0 := by
  apply finiteShadow_eq_zero_of_anomaly_eq_zero_on_sourceKernel
    source (quotient.comp observe) quotientShadow W hW hsurj
  intro w
  have hcoh := LinearMap.congr_fun
    (clockDescentAnomaly_truncate source (quotient.comp observe) observe
      quotientShadow shadow quotient rfl hshadow) w.1
  change quotient (clockDescentAnomaly source observe shadow w.1) =
    clockDescentAnomaly source (quotient.comp observe) quotientShadow w.1 at hcoh
  rw [← hcoh]
  exact LinearMap.mem_ker.mp (hvanish w)

end QuotientDetection

/-! ### Product-topology blindness -/

section DenseBoundary

variable [TopologicalSpace K]

/-- **Finite freedom forces product density.**  If admissible clock variations realize arbitrary
values on every finite coordinate set, then their inclusion into the full product clock has dense
range for the product topology, independently of the topology chosen on the coefficient field.

Consequently the raw product topology cannot separate a nontrivial quotient boundary carried by
these variations.  A nonzero Hausdorff constraint quotient requires a strictly more
source-sensitive topology. -/
theorem denseRange_subtype_of_tateClockFiniteObservableSurjective
    (W : Submodule K (ℕ → K)) (hW : TateClockFiniteObservableSurjective W) :
    DenseRange W.subtype := by
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨s, u, hsu, hsub⟩ := (isOpen_pi_iff.mp hU) x hx
  let target : s → K := fun i ↦ x i.1
  obtain ⟨w, hw⟩ := hW s target
  have hwcyl : w.1 ∈ (s : Set ℕ).pi u := by
    intro i hi
    have his : i ∈ s := Finset.mem_coe.mp hi
    have hwi := congrFun hw ⟨i, his⟩
    change w.1 i = x i at hwi
    rw [hwi]
    exact (hsu i his).2
  refine ⟨w.1, hsub hwcyl, ?_⟩
  exact ⟨w, rfl⟩

/-- **Hausdorff product-observation no-go.**  A continuous linear map from the raw product clock
to any Hausdorff target which vanishes on a finite-observably free admissible tangent must vanish
everywhere.  Thus no nonzero Hausdorff constraint quotient is continuously visible in the product
clock topology. -/
theorem continuousLinearMap_eq_zero_of_tateClockFiniteObservableSurjective
    {Q : Type*} [AddCommGroup Q] [Module K Q] [TopologicalSpace Q] [T2Space Q]
    (W : Submodule K (ℕ → K)) (hW : TateClockFiniteObservableSurjective W)
    (L : (ℕ → K) →ₗ[K] Q) (hL : Continuous L)
    (hzero : ∀ w : W, L w.1 = 0) :
    L = 0 := by
  have hdense := denseRange_subtype_of_tateClockFiniteObservableSurjective W hW
  have heq : (fun x ↦ L x) = (fun _ ↦ (0 : Q)) :=
    hdense.equalizer hL continuous_const (by
      funext w
      exact hzero w)
  ext x
  exact congrFun heq x

end DenseBoundary

end

end GaloisForLFunctions.HTGeometry
