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

/-- **Constraint-algebra cocycle law.**  The source-specific descent anomaly is a derivation under
composition of source operations and their proposed clock shadows:

`α(S T, A B) = A α(T, B) + α(S, A) T`.

Together with the curvature Leibniz law, this is the exact semidirect-product law underlying the
affine boundary-colligation field. -/
theorem clockDescentAnomaly_comp_constraint
    (leftSource rightSource : V →ₗ[K] V)
    (observe : V →ₗ[K] O)
    (leftShadow rightShadow : O →ₗ[K] O) :
    clockDescentAnomaly (leftSource.comp rightSource) observe
        (leftShadow.comp rightShadow) =
      leftShadow.comp
          (clockDescentAnomaly rightSource observe rightShadow) +
        (clockDescentAnomaly leftSource observe leftShadow).comp rightSource := by
  ext v
  simp [clockDescentAnomaly, LinearMap.comp_apply, map_sub]

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

/-- **Boundary-transfer factorization.**  Suppose observable truncation is split by forward clock
extension and the shadows commute with that forward extension.  Then all backward-observation
curvature factors through the complementary boundary projection:

`κ = p T₁ (1 - i p)`.

Thus curvature vanishes on the assembled lower clock and is carried entirely by the newly exposed
boundary layer. -/
theorem clockShadowCurvature_eq_boundaryTransfer
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id)
    (hforward : shadow₁.comp extend = extend.comp shadow₀) :
    clockShadowCurvature shadow₀ shadow₁ truncate =
      truncate.comp
        (shadow₁.comp (LinearMap.id - extend.comp truncate)) := by
  ext v
  have hforward_v := LinearMap.congr_fun hforward (truncate v)
  have hsplit_v := LinearMap.congr_fun hsplit (shadow₀ (truncate v))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hforward_v hsplit_v
  change truncate (shadow₁ v) - shadow₀ (truncate v) =
    truncate (shadow₁ (v - extend (truncate v)))
  rw [map_sub, map_sub, hforward_v, hsplit_v]

/-- Forward-compatible shadows have zero curvature on every direction already assembled from the
lower clock. -/
theorem clockShadowCurvature_comp_extend_eq_zero
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id)
    (hforward : shadow₁.comp extend = extend.comp shadow₀) :
    (clockShadowCurvature shadow₀ shadow₁ truncate).comp extend = 0 := by
  rw [clockShadowCurvature_eq_boundaryTransfer shadow₀ shadow₁ extend truncate hsplit hforward]
  ext v
  have hsplit_v := LinearMap.congr_fun hsplit v
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsplit_v
  simp [LinearMap.comp_apply, hsplit_v]

/-- Projection onto the boundary directions newly exposed at the higher clock.  It is canonical
relative to a chosen splitting `p i = 1`, and is the linear coordinate form of the quotient by
the previously assembled clock. -/
def clockBoundaryProjector
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀) : O₁ →ₗ[K] O₁ :=
  LinearMap.id - extend.comp truncate

/-- The corner of an operator which acts entirely within the newly exposed boundary layer. -/
def clockBoundaryCompression
    (operator : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀) : O₁ →ₗ[K] O₁ :=
  (clockBoundaryProjector extend truncate).comp
    (operator.comp (clockBoundaryProjector extend truncate))

/-- The boundary projector kills all directions extended from the lower clock. -/
theorem clockBoundaryProjector_comp_extend_eq_zero
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id) :
    (clockBoundaryProjector extend truncate).comp extend = 0 := by
  ext v
  have hsplit_v := LinearMap.congr_fun hsplit v
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsplit_v
  simp [clockBoundaryProjector, LinearMap.comp_apply, hsplit_v]

/-- Truncation is blind to every direction selected by the boundary projector. -/
theorem truncate_comp_clockBoundaryProjector_eq_zero
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id) :
    truncate.comp (clockBoundaryProjector extend truncate) = 0 := by
  ext v
  have hsplit_v := LinearMap.congr_fun hsplit (truncate v)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsplit_v
  simp [clockBoundaryProjector, LinearMap.comp_apply, hsplit_v]

/-- **Boundary-colligation reconstruction.**  A forward-compatible higher clock action is
reconstructed exactly from three pieces: the lower action, its outgoing boundary transfer
`κ = p T₁ - T₀ p`, and the action compressed wholly inside the new boundary layer:

`T₁ = i T₀ p + i κ + (1 - i p) T₁ (1 - i p)`.

Consequently curvature alone is not the unified field: it forgets the boundary self-symbol. -/
theorem clockShadow_eq_boundaryColligation
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id)
    (hforward : shadow₁.comp extend = extend.comp shadow₀) :
    shadow₁ =
      extend.comp (shadow₀.comp truncate) +
        extend.comp (clockShadowCurvature shadow₀ shadow₁ truncate) +
          clockBoundaryCompression shadow₁ extend truncate := by
  ext v
  have hforward_v := LinearMap.congr_fun hforward (truncate v)
  have hsplit_v := LinearMap.congr_fun hsplit (shadow₀ (truncate v))
  simp only [LinearMap.comp_apply] at hforward_v
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsplit_v
  simp [clockShadowCurvature, clockBoundaryCompression, clockBoundaryProjector,
    LinearMap.comp_apply, map_sub, hforward_v, hsplit_v]

/-- Equal curvature does not see a perturbation confined entirely to the boundary corner.  This
is the exact no-go for a curvature-only reconstruction theory. -/
theorem clockShadowCurvature_add_boundaryCompression
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ gauge : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id) :
    clockShadowCurvature shadow₀
        (shadow₁ + clockBoundaryCompression gauge extend truncate) truncate =
      clockShadowCurvature shadow₀ shadow₁ truncate := by
  ext v
  have hzero := LinearMap.congr_fun
    (truncate_comp_clockBoundaryProjector_eq_zero extend truncate hsplit)
    (gauge (clockBoundaryProjector extend truncate v))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hzero
  have hcompression :
      truncate (clockBoundaryCompression gauge extend truncate v) = 0 := by
    simpa only [clockBoundaryCompression, LinearMap.comp_apply] using hzero
  simp [clockShadowCurvature, LinearMap.comp_apply, hcompression]

/-- The boundary perturbations invisible to curvature also preserve the action already assembled
from the lower clock. -/
theorem add_clockBoundaryCompression_comp_extend
    (shadow₁ gauge : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id) :
    (shadow₁ + clockBoundaryCompression gauge extend truncate).comp extend =
      shadow₁.comp extend := by
  ext v
  have hsplit_v := LinearMap.congr_fun hsplit v
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsplit_v
  simp [clockBoundaryCompression, clockBoundaryProjector, LinearMap.comp_apply, hsplit_v]

/-- **Colligation uniqueness.**  Once the boundary self-symbol is supplied, the lower action and
boundary transfer determine a forward-compatible higher action uniquely. -/
theorem clockShadow_eq_of_curvature_eq_of_boundaryCompression_eq
    (shadow₀ : O₀ →ₗ[K] O₀) (left₁ right₁ : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id)
    (hleft : left₁.comp extend = extend.comp shadow₀)
    (hright : right₁.comp extend = extend.comp shadow₀)
    (hcurvature : clockShadowCurvature shadow₀ left₁ truncate =
      clockShadowCurvature shadow₀ right₁ truncate)
    (hboundary : clockBoundaryCompression left₁ extend truncate =
      clockBoundaryCompression right₁ extend truncate) :
    left₁ = right₁ := by
  calc
    left₁ = extend.comp (shadow₀.comp truncate) +
        extend.comp (clockShadowCurvature shadow₀ left₁ truncate) +
          clockBoundaryCompression left₁ extend truncate :=
      clockShadow_eq_boundaryColligation shadow₀ left₁ extend truncate hsplit hleft
    _ = extend.comp (shadow₀.comp truncate) +
        extend.comp (clockShadowCurvature shadow₀ right₁ truncate) +
          clockBoundaryCompression right₁ extend truncate := by
      rw [hcurvature, hboundary]
    _ = right₁ :=
      (clockShadow_eq_boundaryColligation shadow₀ right₁ extend truncate hsplit hright).symm

/-- Failure of an algebraic realization to commute with forward clock extension.  For an
otherwise Pro-compatible realization this is an incoming channel into the new boundary. -/
def clockIncomingDefect
    (operator₀ : O₀ →ₗ[K] O₀) (operator₁ : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) : O₀ →ₗ[K] O₁ :=
  operator₁.comp extend - extend.comp operator₀

/-- Comparison seam between an analytic action, an algebraic action, and the algebraic action
after the source parameter has been shifted. -/
def clockComparisonSeam
    (analytic algebraic shiftedAlgebraic : O₀ →ₗ[K] O₀) : O₀ →ₗ[K] O₀ :=
  analytic.comp algebraic - shiftedAlgebraic.comp analytic

/-- **Opposite-variance seam conservation.**  Let the analytic realization be forward Ind-flat,
while the algebraic realization and its shifted copy are backward Pro-flat.  Then the old-clock
block of the higher comparison seam is exactly

`old seam + outgoing analytic curvature ∘ incoming algebraic defect`.

Thus a comparison defect can leave the retained bulk only through a paired incoming/outgoing
boundary channel. -/
theorem truncate_comp_clockComparisonSeam_comp_extend
    (analytic₀ algebraic₀ shiftedAlgebraic₀ : O₀ →ₗ[K] O₀)
    (analytic₁ algebraic₁ shiftedAlgebraic₁ : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id)
    (hanalytic : analytic₁.comp extend = extend.comp analytic₀)
    (halgebraic : truncate.comp algebraic₁ = algebraic₀.comp truncate)
    (hshifted : truncate.comp shiftedAlgebraic₁ =
      shiftedAlgebraic₀.comp truncate) :
    truncate.comp
        ((clockComparisonSeam analytic₁ algebraic₁ shiftedAlgebraic₁).comp extend) =
      clockComparisonSeam analytic₀ algebraic₀ shiftedAlgebraic₀ +
        (clockShadowCurvature analytic₀ analytic₁ truncate).comp
          (clockIncomingDefect algebraic₀ algebraic₁ extend) := by
  ext v
  have hsplit_v := LinearMap.congr_fun hsplit v
  have hanalytic_v := LinearMap.congr_fun hanalytic v
  have hsplit_algebraic_v := LinearMap.congr_fun hsplit (algebraic₀ v)
  have hanalytic_algebraic_v := LinearMap.congr_fun hanalytic (algebraic₀ v)
  have hsplit_analytic_algebraic_v := LinearMap.congr_fun hsplit
    (analytic₀ (algebraic₀ v))
  have halgebraic_v := LinearMap.congr_fun halgebraic (extend v)
  have hsplit_analytic_v := LinearMap.congr_fun hsplit (analytic₀ v)
  have hshifted_analytic_v := LinearMap.congr_fun hshifted (extend (analytic₀ v))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsplit_v
  simp only [LinearMap.comp_apply] at hanalytic_v
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsplit_algebraic_v
  simp only [LinearMap.comp_apply] at hanalytic_algebraic_v
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsplit_analytic_algebraic_v
  simp only [LinearMap.comp_apply] at halgebraic_v
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsplit_analytic_v
  simp only [LinearMap.comp_apply] at hshifted_analytic_v
  simp [clockComparisonSeam, clockShadowCurvature, clockIncomingDefect,
    LinearMap.comp_apply, map_sub, hsplit_v, hanalytic_v, hsplit_algebraic_v,
    hanalytic_algebraic_v, hsplit_analytic_algebraic_v, halgebraic_v,
    hsplit_analytic_v, hshifted_analytic_v]

/-- The intrinsic boundary-transfer map on the quotient by all previously assembled clock
directions.  A split complement is useful for coordinates but is not part of this definition. -/
def clockBoundaryTransferQuotient
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id)
    (hforward : shadow₁.comp extend = extend.comp shadow₀) :
    (O₁ ⧸ LinearMap.range extend) →ₗ[K] O₀ :=
  (LinearMap.range extend).liftQ
    (clockShadowCurvature shadow₀ shadow₁ truncate) (by
      rintro y ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      have hzero := LinearMap.congr_fun
        (clockShadowCurvature_comp_extend_eq_zero
          shadow₀ shadow₁ extend truncate hsplit hforward) x
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hzero)

/-- Pulling the intrinsic quotient transfer back to the higher clock recovers the whole
curvature. -/
theorem clockBoundaryTransferQuotient_comp_mkQ
    (shadow₀ : O₀ →ₗ[K] O₀) (shadow₁ : O₁ →ₗ[K] O₁)
    (extend : O₀ →ₗ[K] O₁) (truncate : O₁ →ₗ[K] O₀)
    (hsplit : truncate.comp extend = LinearMap.id)
    (hforward : shadow₁.comp extend = extend.comp shadow₀) :
    (clockBoundaryTransferQuotient
        shadow₀ shadow₁ extend truncate hsplit hforward).comp
        (LinearMap.range extend).mkQ =
      clockShadowCurvature shadow₀ shadow₁ truncate := by
  exact Submodule.liftQ_mkQ _ _ _

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

/-- The coarsest refinement of the raw product clock topology which makes a chosen source
conormal continuous.  The infimum is in Lean's reverse-inclusion order on topologies: it retains
all product-clock observations and adds exactly the opens forced by `L`. -/
@[reducible] def sourceConormalRefinedTopology
    {Q : Type*} [AddCommGroup Q] [Module K Q] [TopologicalSpace Q]
    (base : TopologicalSpace (ℕ → K)) (L : (ℕ → K) →ₗ[K] Q) :
    TopologicalSpace (ℕ → K) :=
  base ⊓
    TopologicalSpace.induced L (inferInstance : TopologicalSpace Q)

/-- **A nonzero source conormal forces a genuinely finer clock topology.**  If a conormal
annihilates a finite-observably free source tangent, then it is invisible to the product clock.
Consequently the minimal topology which makes that conormal continuous is strictly finer than the
product topology.

This is the positive topology forced by the product-observation no-go: the source constraint does
not merely inhabit a completion chosen afterwards; it contributes new open sets. -/
theorem sourceConormalRefinedTopology_lt_product
    {Q : Type*} [AddCommGroup Q] [Module K Q] [TopologicalSpace Q] [T2Space Q]
    (W : Submodule K (ℕ → K)) (hW : TateClockFiniteObservableSurjective W)
    (L : (ℕ → K) →ₗ[K] Q) (hL : L ≠ 0) (hzero : ∀ w : W, L w.1 = 0) :
    sourceConormalRefinedTopology (K := K)
        (inferInstance : TopologicalSpace (ℕ → K)) L <
      (inferInstance : TopologicalSpace (ℕ → K)) := by
  rw [sourceConormalRefinedTopology, inf_lt_left]
  intro hcontinuous
  apply hL
  exact continuousLinearMap_eq_zero_of_tateClockFiniteObservableSurjective
    W hW L (continuous_iff_le_induced.mpr hcontinuous) hzero

omit [TopologicalSpace K] in
/-- The source-conormal refinement is minimal: every topology which refines the product clock and
makes `L` continuous is itself finer than `sourceConormalRefinedTopology L`. -/
theorem le_sourceConormalRefinedTopology
    {Q : Type*} [AddCommGroup Q] [Module K Q] [TopologicalSpace Q]
    (L : (ℕ → K) →ₗ[K] Q)
    (base t : TopologicalSpace (ℕ → K))
    (hproduct : t ≤ base)
    (hL : t ≤ TopologicalSpace.induced L (inferInstance : TopologicalSpace Q)) :
    t ≤ sourceConormalRefinedTopology (K := K) base L :=
  le_inf hproduct hL

end DenseBoundary

end

end GaloisForLFunctions.HTGeometry
