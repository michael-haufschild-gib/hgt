import GaloisForLFunctions.RHTower.CCMSoninInverseSemigroup

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

set_option maxHeartbeats 1000000

/-- Canonical live window of a composable scale path with prescribed minimum. -/
def soninPathWindow
    (a p q m : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hm : 1 < m)
    (hmp : m ≤ p) (hmq : m ≤ q) : SoninLiveWindow a where
  ceiling := p * a
  floor := (p * m⁻¹) * a
  scale := p⁻¹ * q
  scale_pos := mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq)
  base_le_floor := by
    have hm0 : 0 < m := zero_lt_one.trans hm
    have hratio : 1 ≤ p * m⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hm0).mpr (by simpa using hmp)
    nlinarith
  floor_lt_ceiling := by
    have hm0 : 0 < m := zero_lt_one.trans hm
    have hp0 : 0 < p := zero_lt_one.trans hp
    have hminv : m⁻¹ < 1 := inv_lt_one_of_one_lt₀ hm
    nlinarith [mul_pos hp0 ha]
  domain_le := by
    have hp0 : 0 < p := zero_lt_one.trans hp
    have hm0 : 0 < m := zero_lt_one.trans hm
    have hratio : 1 ≤ q * m⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hm0).mpr (by simpa using hmq)
    have heq : (p⁻¹ * q) * ((p * m⁻¹) * a) = (q * m⁻¹) * a := by
      field_simp [hp0.ne']
    rw [heq]
    nlinarith

/-- Scaling the second ceiling back through a composable path recovers the first ceiling. -/
theorem soninPath_scaledCeiling
    (p q a : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (p⁻¹ * q)⁻¹ * (q * a) = p * a := by
  field_simp [hp.ne', hq.ne']

/-- Scaling the second path floor back through a composable path preserves its minimum label. -/
theorem soninPath_scaledFloor
    (p q n a : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (p⁻¹ * q)⁻¹ * ((q * n⁻¹) * a) = (p * n⁻¹) * a := by
  field_simp [hp.ne', hq.ne']

/-- Composition multiplies the endpoint displacement ratios. -/
theorem soninPath_composeScale
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (p⁻¹ * q) * (q⁻¹ * r) = p⁻¹ * r := by
  field_simp [hp.ne', hq.ne']

/-- Intersecting two composable path shells replaces their minimum labels by their minimum. -/
theorem soninPath_maxFloors
    (p m n a : ℝ) (hp : 0 < p) (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) :
    max ((p * m⁻¹) * a) ((p * n⁻¹) * a) =
      (p * (min m n)⁻¹) * a := by
  rcases le_total m n with hmn | hnm
  · have hinv : n⁻¹ ≤ m⁻¹ := (inv_le_inv₀ hn hm).2 hmn
    have hscaled : (p * n⁻¹) * a ≤ (p * m⁻¹) * a := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv hp.le) ha.le
    rw [min_eq_left hmn, max_eq_left hscaled]
  · have hinv : m⁻¹ ≤ n⁻¹ := (inv_le_inv₀ hm hn).2 hnm
    have hscaled : (p * m⁻¹) * a ≤ (p * n⁻¹) * a := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv hp.le) ha.le
    rw [min_eq_right hnm, max_eq_right hscaled]

/-- **Tropical concatenation law.**  Concatenating composable path windows preserves the outer
endpoints and replaces the two recorded minima by their minimum. -/
theorem composeSoninPathWindows
    (a p q r m n : ℝ) (ha : 0 < a)
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hm : 1 < m) (hn : 1 < n)
    (hmp : m ≤ p) (hmq : m ≤ q) (hnq : n ≤ q) (hnr : n ≤ r) :
    composeSoninLiveWindows
        (soninPathWindow a p q m ha hp hq hm hmp hmq)
        (soninPathWindow a q r n ha hq hr hn hnq hnr) =
      SoninWindowState.live
        (soninPathWindow a p r (min m n) ha hp hr (lt_min hm hn)
          ((min_le_left m n).trans hmp) ((min_le_right m n).trans hnr)) := by
  let d₁ := soninPathWindow a p q m ha hp hq hm hmp hmq
  let d₂ := soninPathWindow a q r n ha hq hr hn hnq hnr
  let d₃ := soninPathWindow a p r (min m n) ha hp hr (lt_min hm hn)
    ((min_le_left m n).trans hmp) ((min_le_right m n).trans hnr)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hCeiling : soninLiveComposeCeiling d₁ d₂ = d₃.ceiling := by
    dsimp only [soninLiveComposeCeiling, soninWindowComposeCeiling, d₁, d₂, d₃,
      soninPathWindow]
    rw [soninPath_scaledCeiling p q a hp0 hq0, min_self]
  have hRawFloor : soninWindowComposeFloor d₁.ceiling d₁.floor d₁.scale
      d₂.ceiling d₂.floor = d₃.floor := by
    dsimp only [soninWindowComposeFloor, soninWindowComposeCeiling, d₁, d₂, d₃,
      soninPathWindow]
    rw [soninPath_scaledFloor p q n a hp0 hq0,
      soninPath_maxFloors p m n a hp0 (zero_lt_one.trans hm)
        (zero_lt_one.trans hn) ha,
      soninPath_scaledCeiling p q a hp0 hq0, min_self,
      min_eq_left]
    exact (soninPathWindow a p r (min m n) ha hp hr (lt_min hm hn)
      ((min_le_left m n).trans hmp) ((min_le_right m n).trans hnr)).floor_lt_ceiling.le
  have hScale : soninLiveComposeScale d₁ d₂ = d₃.scale := by
    dsimp only [soninLiveComposeScale, d₁, d₂, d₃, soninPathWindow]
    exact soninPath_composeScale p q r hp0 hq0
  have hinvFloor : d₃.scale⁻¹ * a ≤ d₃.floor := by
    have hdiv : a / d₃.scale ≤ d₃.floor :=
      (div_le_iff₀ d₃.scale_pos).mpr (by
        simpa only [mul_comm] using d₃.domain_le)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  have hFloor : soninLiveComposeFloor d₁ d₂ = d₃.floor := by
    have hCeiling' : soninWindowComposeCeiling d₁.ceiling d₁.scale d₂.ceiling =
        d₃.ceiling := hCeiling
    have hScale' : d₁.scale * d₂.scale = d₃.scale := hScale
    dsimp only [soninLiveComposeFloor, soninWindowComposeNormalizedFloor,
      soninWindowNormalizedFloor]
    rw [hRawFloor, hCeiling', hScale', max_eq_left hinvFloor,
      min_eq_left d₃.floor_lt_ceiling.le]
  have hlt : soninLiveComposeFloor d₁ d₂ < soninLiveComposeCeiling d₁ d₂ := by
    rw [hFloor, hCeiling]
    exact d₃.floor_lt_ceiling
  change composeSoninLiveWindows d₁ d₂ = SoninWindowState.live d₃
  rw [composeSoninLiveWindows, dif_pos hlt]
  congr 1
  apply SoninLiveWindow.ext_coordinates
  · exact hCeiling
  · exact hFloor
  · exact hScale

/-- Genuine Gram factor attached to an ordered pair of scales. -/
def soninGramFactorOfScales (p q : ℝ) (hp : 1 < p) (hq : 1 < q) : SoninGramFactor where
  source := p
  target := q
  source_gt_one := hp
  target_gt_one := hq

/-- A one-edge Gram factor is the path window whose recorded minimum is the smaller endpoint. -/
theorem soninGramFactor_liveWindow_eq_pathWindow
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    (soninGramFactorOfScales p q hp hq).liveWindow a ha =
      soninPathWindow a p q (min p q) ha hp hq (lt_min hp hq)
        (min_le_left p q) (min_le_right p q) := by
  apply SoninLiveWindow.ext_coordinates
  · rfl
  · dsimp only [SoninGramFactor.liveWindow, soninGramFactorOfScales, soninPathWindow]
    rcases le_total p q with hpq | hqp
    · rw [min_eq_left hpq]
      have hratio : (p * q⁻¹) * a ≤ a := by
        have hq0 : 0 < q := zero_lt_one.trans hq
        have hpq' : p * q⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv]
          exact (div_le_one hq0).mpr hpq
        nlinarith [mul_pos (zero_lt_one.trans hp) ha]
      rw [max_eq_left hratio]
      field_simp [hp.ne']
    · rw [min_eq_right hqp]
      have hratio : a ≤ (p * q⁻¹) * a := by
        have hq0 : 0 < q := zero_lt_one.trans hq
        have hqp' : 1 ≤ p * q⁻¹ := by
          rw [← div_eq_mul_inv]
          exact (one_le_div hq0).mpr hqp
        nlinarith [mul_pos (zero_lt_one.trans hp) ha]
      rw [max_eq_right hratio]
  · rfl

/-- A nonempty composable path of scales, built by adjoining one endpoint at a time. -/
inductive SoninScalePath where
  | edge (source target : ℝ) (source_gt_one : 1 < source) (target_gt_one : 1 < target)
  | extend (path : SoninScalePath) (target : ℝ) (target_gt_one : 1 < target)

namespace SoninScalePath

/-- Initial scale of a path. -/
def start : SoninScalePath → ℝ
  | .edge p _ _ _ => p
  | .extend P _ _ => P.start

/-- Terminal scale of a path. -/
def endpoint : SoninScalePath → ℝ
  | .edge _ q _ _ => q
  | .extend _ r _ => r

/-- Smallest scale visited by the recursive path. -/
def minimum : SoninScalePath → ℝ
  | .edge p q _ _ => min p q
  | .extend P r _ => min P.minimum r

theorem start_gt_one : ∀ P : SoninScalePath, 1 < P.start
  | .edge _ _ hp _ => hp
  | .extend P _ _ => P.start_gt_one

theorem endpoint_gt_one : ∀ P : SoninScalePath, 1 < P.endpoint
  | .edge _ _ _ hq => hq
  | .extend _ _ hr => hr

theorem minimum_gt_one : ∀ P : SoninScalePath, 1 < P.minimum
  | .edge _ _ hp hq => lt_min hp hq
  | .extend P _ hr => lt_min P.minimum_gt_one hr

theorem minimum_le_start : ∀ P : SoninScalePath, P.minimum ≤ P.start
  | .edge p q _ _ => min_le_left p q
  | .extend P r _ => (min_le_left P.minimum r).trans P.minimum_le_start

theorem minimum_le_endpoint : ∀ P : SoninScalePath, P.minimum ≤ P.endpoint
  | .edge p q _ _ => min_le_right p q
  | .extend P r _ => min_le_right P.minimum r

/-- Canonical live window carried by a finite composable path. -/
def window (a : ℝ) (ha : 0 < a) (P : SoninScalePath) : SoninLiveWindow a :=
  soninPathWindow a P.start P.endpoint P.minimum ha P.start_gt_one P.endpoint_gt_one
    P.minimum_gt_one P.minimum_le_start P.minimum_le_endpoint

/-- Left-associated word of genuine Gram operators along the path. -/
def operator (a : ℝ) : SoninScalePath → (evenSubspace →L[Complex] evenSubspace)
  | .edge p q hp hq => (soninGramFactorOfScales p q hp hq).operator a
  | .extend P r hr =>
      P.operator a *
        (soninGramFactorOfScales P.endpoint r P.endpoint_gt_one hr).operator a

/-- **Finite composable-path normal form.**  The genuine Gram word of a path is compactly equal
to the unique window determined by its first endpoint, last endpoint, and minimum visited scale. -/
theorem operator_compactEq_window (a : ℝ) (ha : 0 < a) :
    ∀ P : SoninScalePath, P.operator a =ₖ (P.window a ha).operator
  | .edge p q hp hq => by
      have h := (soninGramFactorOfScales p q hp hq).operator_compactEq_liveWindow a ha
      rw [soninGramFactor_liveWindow_eq_pathWindow a p q ha hp hq] at h
      simpa [SoninScalePath.operator, SoninScalePath.window, start, endpoint, minimum] using h
  | .extend P r hr => by
      let e := soninPathWindow a P.endpoint r (min P.endpoint r) ha
        P.endpoint_gt_one hr (lt_min P.endpoint_gt_one hr)
        (min_le_left P.endpoint r) (min_le_right P.endpoint r)
      let g := soninGramFactorOfScales P.endpoint r P.endpoint_gt_one hr
      have hedge := soninGramFactor_liveWindow_eq_pathWindow
        a P.endpoint r ha P.endpoint_gt_one hr
      have hnext : g.operator a =ₖ e.operator := by
        have h := g.operator_compactEq_liveWindow a ha
        change g.operator a =ₖ (g.liveWindow a ha).operator at h
        rw [hedge] at h
        exact h
      have hmul : P.operator a * g.operator a =ₖ (P.window a ha).operator * e.operator :=
        CompactOperatorEq.mul (operator_compactEq_window a ha P) hnext
      have hstate := soninWindowState_operator_mul_compactEq ha
        (SoninWindowState.live (P.window a ha)) (SoninWindowState.live e)
      dsimp only [window, e, composeSoninWindowStates] at hstate
      rw [composeSoninPathWindows a P.start P.endpoint r P.minimum
        (min P.endpoint r) ha P.start_gt_one P.endpoint_gt_one hr
        P.minimum_gt_one (lt_min P.endpoint_gt_one hr)
        P.minimum_le_start P.minimum_le_endpoint
        (min_le_left P.endpoint r) (min_le_right P.endpoint r)] at hstate
      have hmin : min P.minimum (min P.endpoint r) = min P.minimum r := by
        rw [← min_assoc, min_eq_left P.minimum_le_endpoint]
      have hwindow :
          soninPathWindow a P.start r (min P.minimum (min P.endpoint r)) ha
              P.start_gt_one hr (lt_min P.minimum_gt_one (lt_min P.endpoint_gt_one hr))
              ((min_le_left P.minimum (min P.endpoint r)).trans P.minimum_le_start)
              ((min_le_right P.minimum (min P.endpoint r)).trans (min_le_right P.endpoint r)) =
            (SoninScalePath.extend P r hr).window a ha := by
        apply SoninLiveWindow.ext_coordinates
        · rfl
        · change (P.start * (min P.minimum (min P.endpoint r))⁻¹) * a =
            (P.start * (min P.minimum r)⁻¹) * a
          rw [hmin]
        · rfl
      rw [hwindow] at hstate
      exact hmul.trans hstate

/-- With fixed endpoints, the path-window datum recovers its minimum scale exactly. -/
theorem pathWindow_eq_iff_minimum_eq
    (a p q m n : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q)
    (hm : 1 < m) (hn : 1 < n)
    (hmp : m ≤ p) (hmq : m ≤ q) (hnp : n ≤ p) (hnq : n ≤ q) :
    soninPathWindow a p q m ha hp hq hm hmp hmq =
        soninPathWindow a p q n ha hp hq hn hnp hnq ↔
      m = n := by
  constructor
  · intro h
    have hfloor := congrArg SoninLiveWindow.floor h
    change (p * m⁻¹) * a = (p * n⁻¹) * a at hfloor
    have hratio : p * m⁻¹ = p * n⁻¹ := mul_right_cancel₀ ha.ne' hfloor
    have hinv : m⁻¹ = n⁻¹ :=
      mul_left_cancel₀ (zero_lt_one.trans hp).ne' hratio
    exact inv_injective hinv
  · rintro rfl
    rfl

/-- Every finite composable Gram path remains noncompact: its minimum scale is strictly larger
than one, so its canonical shell never degenerates. -/
theorem operator_not_isCompactOperator (a : ℝ) (ha : 0 < a) (P : SoninScalePath) :
    ¬ IsCompactOperator (P.operator a) := by
  intro hcompact
  have hwindow : IsCompactOperator (P.window a ha).operator :=
    RHTower.IsCompactOperator.compactEq_right hcompact (P.operator_compactEq_window a ha)
  exact (P.window a ha).not_isCompactOperator ha hwindow

/-- **Endpoint absorption criterion.**  A composable Gram path is compactly equal to the direct
Gram entry between its endpoints exactly when no interior scale lies below both endpoints. -/
theorem operator_compactEq_direct_iff_minimum_eq_endpointMin
    (a : ℝ) (ha : 0 < a) (P : SoninScalePath) :
    P.operator a =ₖ
        (soninGramFactorOfScales P.start P.endpoint P.start_gt_one
          P.endpoint_gt_one).operator a ↔
      P.minimum = min P.start P.endpoint := by
  let g := soninGramFactorOfScales P.start P.endpoint P.start_gt_one P.endpoint_gt_one
  let w := soninPathWindow a P.start P.endpoint (min P.start P.endpoint) ha
    P.start_gt_one P.endpoint_gt_one (lt_min P.start_gt_one P.endpoint_gt_one)
    (min_le_left P.start P.endpoint) (min_le_right P.start P.endpoint)
  have hP : P.operator a =ₖ (P.window a ha).operator := P.operator_compactEq_window a ha
  have hg : g.operator a =ₖ w.operator := by
    have h := g.operator_compactEq_liveWindow a ha
    have hedge := soninGramFactor_liveWindow_eq_pathWindow
      a P.start P.endpoint ha P.start_gt_one P.endpoint_gt_one
    change g.operator a =ₖ (g.liveWindow a ha).operator at h
    rw [hedge] at h
    exact h
  constructor
  · intro h
    have hwop : (P.window a ha).operator =ₖ w.operator :=
      hP.symm.trans (h.trans hg)
    have hw : P.window a ha = w :=
      ((P.window a ha).operator_compactEq_iff ha w).mp hwop
    exact (pathWindow_eq_iff_minimum_eq a P.start P.endpoint P.minimum
      (min P.start P.endpoint) ha P.start_gt_one P.endpoint_gt_one
      P.minimum_gt_one (lt_min P.start_gt_one P.endpoint_gt_one)
      P.minimum_le_start P.minimum_le_endpoint
      (min_le_left P.start P.endpoint) (min_le_right P.start P.endpoint)).mp hw
  · intro hmin
    have hw : P.window a ha = w :=
      (pathWindow_eq_iff_minimum_eq a P.start P.endpoint P.minimum
        (min P.start P.endpoint) ha P.start_gt_one P.endpoint_gt_one
        P.minimum_gt_one (lt_min P.start_gt_one P.endpoint_gt_one)
        P.minimum_le_start P.minimum_le_endpoint
        (min_le_left P.start P.endpoint) (min_le_right P.start P.endpoint)).mpr hmin
    exact hP.trans ((CompactOperatorEq.of_eq (congrArg SoninLiveWindow.operator hw)).trans hg.symm)

end SoninScalePath

end RHTower
