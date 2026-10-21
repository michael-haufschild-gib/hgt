import GaloisForLFunctions.ArithmeticCriticalityTheory.EvenGaugeFoldedConductance

/-!
# The hub energy of the folded jump form and the Schur step

For an even gauge `M` and an even profile `u`, the folded jump energy is
`∫ κ I = 2 ∫_{x>0} ∫_{s>0} (κ(s) + κ(s + 2x)) J_s(x)`, `J_s(x) = M(x) M(x+s)(u(x) − u(x+s))²`.

* **The hub energy** (`hub_energy_ge`). The pairs with one point in a set `Z ⊆ (0, ∞)` carry at least
  `(∫_Z M) ∫_{p>0} M(p)(u(p) − ū)²`, `ū = ∫_Z M u / ∫_Z M`: the upper pairs `(p, z)`, `p < z`, and,
  after Fubini, the lower pairs make up all pairs `(p, z ∈ Z)`, and each point sees the hub through
  Jensen's inequality (`hub_jensen`). This is a Poincaré inequality for the folded jump form with
  constant `k ∫_Z M` whenever the hub conductances are at least `k`.
* **The fold with a hub and a two-point cost** (`integral_kappa_mul_gaugeJumpProfile_ge_hub`). A lower
  bound `κ(s) + κ(s + 2x) ≥ k (1_Z(x) + 1_Z(x + s)) − G(x, x + s)` keeps the hub pairs and pays the
  negative part on `u(x)²` with the inner weight `∫_{s>0} G(x, x+s) M(x+s) ds` and on `u(y)²` with an
  outer majorant of `G`. With `k = 0` it is the fold with a cost depending on both points.
* **The Schur step** (`schur_pointwise`, `integral_schur_piece_ge`).
  `A(t − c)² + B t² ≥ c² AB/(A + B)` for `A + B > 0`: a Poincaré term absorbs a potential that is
  negative in places, as long as its Schur average stays positive.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- **Jensen on a hub.** `∫_Z M (a − u)² ≥ (∫_Z M)(a − ū)²`, `ū = ∫_Z M u / ∫_Z M`: the
difference is the weighted variance `∫_Z M (u − ū)²`. -/
theorem hub_jensen {M u : ℝ → ℝ} {Z : Set ℝ} (hZm : MeasurableSet Z) (hM : IntegrableOn M Z)
    (hMu : IntegrableOn (fun z => M z * u z) Z) (hMu2 : IntegrableOn (fun z => M z * u z ^ 2) Z)
    (hM0 : ∀ z ∈ Z, 0 ≤ M z) (hpos : 0 < ∫ z in Z, M z) (a : ℝ) :
    (∫ z in Z, M z) * (a - (∫ z in Z, M z * u z) / ∫ z in Z, M z) ^ 2 ≤
      ∫ z in Z, M z * (a - u z) ^ 2 := by
  set m0 := ∫ z in Z, M z with hm0
  set m1 := ∫ z in Z, M z * u z with hm1
  set m2 := ∫ z in Z, M z * u z ^ 2 with hm2
  have hquad : ∀ b : ℝ, (∫ z in Z, M z * (b - u z) ^ 2) = b ^ 2 * m0 - 2 * b * m1 + m2 := by
    intro b
    have e : (∫ z in Z, M z * (b - u z) ^ 2) =
        ∫ z in Z, (b ^ 2 * M z - 2 * b * (M z * u z) + M z * u z ^ 2) :=
      setIntegral_congr_fun hZm fun z _ => by ring
    rw [e, integral_add (f := fun z => b ^ 2 * M z - 2 * b * (M z * u z))
      (g := fun z => M z * u z ^ 2) ((hM.const_mul _).sub (hMu.const_mul _)) hMu2,
      integral_sub (f := fun z => b ^ 2 * M z) (g := fun z => 2 * b * (M z * u z))
        (hM.const_mul _) (hMu.const_mul _), integral_const_mul, integral_const_mul]
  have hvar : 0 ≤ ∫ z in Z, M z * (m1 / m0 - u z) ^ 2 :=
    setIntegral_nonneg hZm fun z hz => mul_nonneg (hM0 z hz) (sq_nonneg _)
  rw [hquad] at hvar
  rw [hquad]
  set t := m1 / m0 with htdef
  have ht : m0 * t = m1 := by rw [htdef]; field_simp
  have h2 : m0 * t ^ 2 = t * m1 := by rw [← ht]; ring
  have e : m0 * (a - t) ^ 2 = a ^ 2 * m0 - 2 * a * (m0 * t) + m0 * t ^ 2 := by ring
  rw [e, ht, h2]
  have h3 : t ^ 2 * m0 = t * m1 := by rw [mul_comm, h2]
  linarith

/-! ### The hub energy -/

/-- The pair energy density `g(p, z) = M(p) M(z) (u(p) − u(z))²` on `ℝ²`. -/
def pairEnergy (M u : ℝ → ℝ) (q : ℝ × ℝ) : ℝ := M q.1 * M q.2 * (u q.1 - u q.2) ^ 2

theorem pairEnergy_diag (M u : ℝ → ℝ) (p : ℝ) : pairEnergy M u (p, p) = 0 := by
  simp [pairEnergy]

theorem integrable_pairEnergy {M u : ℝ → ℝ} {B : ℝ} (hMc : Continuous M) (huc : Continuous u)
    (hMB : ∀ x, B ≤ |x| → M x = 0) : Integrable (pairEnergy M u) := by
  have hc : Continuous (pairEnergy M u) := by unfold pairEnergy; fun_prop
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (-B) B ×ˢ Icc (-B) B)) fun q hq => ?_)
  unfold pairEnergy
  rw [mem_prod, not_and_or] at hq
  rcases hq with h | h
  · rw [hMB q.1 (not_lt.mp fun h' => h (abs_le.mp h'.le)), zero_mul, zero_mul]
  · rw [hMB q.2 (not_lt.mp fun h' => h (abs_le.mp h'.le)), mul_zero, zero_mul]

/-- Pairs `(p, z)`, `0 < p < z`, with the outer point in the hub. -/
def hubUpperPairs (Z : Set ℝ) : Set (ℝ × ℝ) := {q | 0 < q.1} ∩ ({q | q.1 < q.2} ∩ Prod.snd ⁻¹' Z)

/-- Pairs `(p, z)`, `0 < z < p`, with the inner point in the hub. -/
def hubLowerPairs (Z : Set ℝ) : Set (ℝ × ℝ) := {q | 0 < q.1} ∩ ({q | q.2 < q.1} ∩ Prod.snd ⁻¹' Z)

/-- All pairs `(p, z)`, `p > 0`, `z` in the hub. -/
def hubPairs (Z : Set ℝ) : Set (ℝ × ℝ) := {q | 0 < q.1} ∩ Prod.snd ⁻¹' Z

theorem measurableSet_hubUpperPairs {Z : Set ℝ} (hZm : MeasurableSet Z) :
    MeasurableSet (hubUpperPairs Z) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_snd).inter (measurable_snd hZm))

theorem measurableSet_hubLowerPairs {Z : Set ℝ} (hZm : MeasurableSet Z) :
    MeasurableSet (hubLowerPairs Z) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_snd measurable_fst).inter (measurable_snd hZm))

theorem measurableSet_hubPairs {Z : Set ℝ} (hZm : MeasurableSet Z) : MeasurableSet (hubPairs Z) :=
  (measurableSet_lt measurable_const measurable_fst).inter (measurable_snd hZm)

/-- Off the diagonal, where the pair energy vanishes, the hub pairs split into upper and lower. -/
theorem indicator_hubUpper_add_hubLower (M u : ℝ → ℝ) (Z : Set ℝ) (q : ℝ × ℝ) :
    (hubUpperPairs Z).indicator (pairEnergy M u) q + (hubLowerPairs Z).indicator (pairEnergy M u) q =
      (hubPairs Z).indicator (pairEnergy M u) q := by
  obtain ⟨p, z⟩ := q
  have hU : (p, z) ∈ hubUpperPairs Z ↔ 0 < p ∧ p < z ∧ z ∈ Z := Iff.rfl
  have hL : (p, z) ∈ hubLowerPairs Z ↔ 0 < p ∧ z < p ∧ z ∈ Z := Iff.rfl
  have hH : (p, z) ∈ hubPairs Z ↔ 0 < p ∧ z ∈ Z := Iff.rfl
  by_cases hc : 0 < p ∧ z ∈ Z
  · rw [Set.indicator_of_mem (hH.mpr hc)]
    rcases lt_trichotomy p z with h | h | h
    · rw [Set.indicator_of_mem (hU.mpr ⟨hc.1, h, hc.2⟩),
        Set.indicator_of_notMem (fun hh => absurd (hL.mp hh).2.1 (not_lt.mpr h.le)), add_zero]
    · subst h
      rw [Set.indicator_of_notMem (fun hh => lt_irrefl _ (hU.mp hh).2.1),
        Set.indicator_of_notMem (fun hh => lt_irrefl _ (hL.mp hh).2.1), pairEnergy_diag, add_zero]
    · rw [Set.indicator_of_notMem (fun hh => absurd (hU.mp hh).2.1 (not_lt.mpr h.le)),
        Set.indicator_of_mem (hL.mpr ⟨hc.1, h, hc.2⟩), zero_add]
  · rw [Set.indicator_of_notMem (fun hh => hc ⟨(hU.mp hh).1, (hU.mp hh).2.2⟩),
      Set.indicator_of_notMem (fun hh => hc ⟨(hL.mp hh).1, (hL.mp hh).2.2⟩),
      Set.indicator_of_notMem (fun hh => hc (hH.mp hh)), add_zero]

section HubSum

variable {M u : ℝ → ℝ} {B : ℝ} (hMc : Continuous M) (huc : Continuous u)
  (hMB : ∀ x, B ≤ |x| → M x = 0) {Z : Set ℝ} (hZm : MeasurableSet Z) (hZ : Z ⊆ Ioi 0)

/-- At a fixed inner point `p > 0` the upper hub pairs are the shift integral over `p + s ∈ Z`. -/
theorem integral_hubUpperPairs_section (M u : ℝ → ℝ) (Z : Set ℝ) (p : ℝ) :
    (∫ z, (hubUpperPairs Z).indicator (pairEnergy M u) (p, z)) =
      (Ioi (0 : ℝ)).indicator (fun x => ∫ s in Ioi (0 : ℝ),
        Z.indicator 1 (x + s) * signedShiftJump M u s x) p := by
  by_cases hp : 0 < p
  · rw [Set.indicator_of_mem (show p ∈ Ioi (0 : ℝ) from hp)]
    have e : (fun z => (hubUpperPairs Z).indicator (pairEnergy M u) (p, z)) =
        (Ioi p).indicator (fun z => Z.indicator 1 z * pairEnergy M u (p, z)) := by
      funext z
      by_cases hz : p < z
      · rw [Set.indicator_of_mem (show z ∈ Ioi p from hz)]
        by_cases hzZ : z ∈ Z
        · rw [Set.indicator_of_mem (show (p, z) ∈ hubUpperPairs Z from ⟨hp, hz, hzZ⟩),
            Set.indicator_of_mem hzZ, Pi.one_apply, one_mul]
        · rw [Set.indicator_of_notMem (fun hh => hzZ hh.2.2), Set.indicator_of_notMem hzZ,
            zero_mul]
      · rw [Set.indicator_of_notMem (show z ∉ Ioi p from hz),
          Set.indicator_of_notMem (fun hh => hz hh.2.1)]
    rw [e, integral_indicator measurableSet_Ioi, setIntegral_Ioi_translate]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [pairEnergy, signedShiftJump]
    rw [add_comm s p]
  · rw [Set.indicator_of_notMem (show p ∉ Ioi (0 : ℝ) from hp)]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
    exact Set.indicator_of_notMem (fun hh => hp hh.1) _

/-- At a fixed hub point `z` the lower hub pairs are the shift integral from `z`. -/
theorem integral_hubLowerPairs_section (M u : ℝ → ℝ) {Z : Set ℝ} (hZ : Z ⊆ Ioi 0) (z : ℝ) :
    (∫ p, (hubLowerPairs Z).indicator (pairEnergy M u) (p, z)) =
      (Ioi (0 : ℝ)).indicator (fun x => ∫ s in Ioi (0 : ℝ),
        Z.indicator 1 x * signedShiftJump M u s x) z := by
  by_cases hzZ : z ∈ Z
  · have hz : 0 < z := hZ hzZ
    rw [Set.indicator_of_mem (show z ∈ Ioi (0 : ℝ) from hz)]
    have e : (fun p => (hubLowerPairs Z).indicator (pairEnergy M u) (p, z)) =
        (Ioi z).indicator (fun p => pairEnergy M u (p, z)) := by
      funext p
      by_cases hp : z < p
      · rw [Set.indicator_of_mem (show p ∈ Ioi z from hp),
          Set.indicator_of_mem (show (p, z) ∈ hubLowerPairs Z from ⟨hz.trans hp, hp, hzZ⟩)]
      · rw [Set.indicator_of_notMem (show p ∉ Ioi z from hp),
          Set.indicator_of_notMem (fun hh => hp hh.2.1)]
    rw [e, integral_indicator measurableSet_Ioi, setIntegral_Ioi_translate]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [pairEnergy, signedShiftJump, Set.indicator_of_mem hzZ, Pi.one_apply, one_mul]
    rw [add_comm s z]
    ring
  · have e : (fun p => (hubLowerPairs Z).indicator (pairEnergy M u) (p, z)) = fun _ => 0 := by
      funext p
      exact Set.indicator_of_notMem (fun hh => hzZ hh.2.2) _
    rw [e, integral_zero]
    by_cases hz : 0 < z
    · rw [Set.indicator_of_mem (show z ∈ Ioi (0 : ℝ) from hz)]
      symm
      refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
      simp [Set.indicator_of_notMem hzZ]
    · rw [Set.indicator_of_notMem (show z ∉ Ioi (0 : ℝ) from hz)]

include hMc huc hMB hZm in
/-- The upper hub pairs as a shift integral: `0 < p`, `z = p + s ∈ Z`. -/
theorem integral_hubUpperPairs_eq :
    (∫ q, (hubUpperPairs Z).indicator (pairEnergy M u) q) =
      ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), Z.indicator 1 (x + s) * signedShiftJump M u s x := by
  have hint := (integrable_pairEnergy hMc huc hMB).indicator (measurableSet_hubUpperPairs hZm)
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint, ← integral_indicator measurableSet_Ioi]
  exact integral_congr_ae (Eventually.of_forall fun p => integral_hubUpperPairs_section M u Z p)

include hMc huc hMB hZm hZ in
/-- The lower hub pairs as a shift integral: the inner point `x ∈ Z`, the outer `x + s`. -/
theorem integral_hubLowerPairs_eq :
    (∫ q, (hubLowerPairs Z).indicator (pairEnergy M u) q) =
      ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), Z.indicator 1 x * signedShiftJump M u s x := by
  have hint := (integrable_pairEnergy hMc huc hMB).indicator (measurableSet_hubLowerPairs hZm)
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint, ← integral_indicator measurableSet_Ioi]
  exact integral_congr_ae (Eventually.of_forall fun z => integral_hubLowerPairs_section M u hZ z)

include hMc huc hMB hZm in
theorem integrableOn_hubUpper_section :
    IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ), Z.indicator 1 (x + s) * signedShiftJump M u s x)
      (Ioi 0) := by
  have hint := (integrable_pairEnergy hMc huc hMB).indicator (measurableSet_hubUpperPairs hZm)
  rw [Measure.volume_eq_prod] at hint
  refine (hint.integral_prod_left.integrableOn (s := Ioi (0 : ℝ))).congr_fun (fun p hp => ?_)
    measurableSet_Ioi
  simp only
  rw [integral_hubUpperPairs_section, Set.indicator_of_mem hp]

include hMc huc hMB hZm hZ in
theorem integrableOn_hubLower_section :
    IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ), Z.indicator 1 x * signedShiftJump M u s x)
      (Ioi 0) := by
  have hint := (integrable_pairEnergy hMc huc hMB).indicator (measurableSet_hubLowerPairs hZm)
  rw [Measure.volume_eq_prod] at hint
  refine (hint.integral_prod_right.integrableOn (s := Ioi (0 : ℝ))).congr_fun (fun z hz => ?_)
    measurableSet_Ioi
  simp only
  rw [integral_hubLowerPairs_section M u hZ, Set.indicator_of_mem hz]

include hMc huc hMB hZm hZ in
/-- **The hub energy.** The pairs with one point in the hub `Z ⊆ (0, ∞)` carry at least
`(∫_Z M) ∫_{p>0} M(p)(u(p) − ū)²`, `ū = ∫_Z M u / ∫_Z M`: the upper and lower hub pairs make up all
pairs `(p, z)`, `z ∈ Z`, and each point `p` sees the hub through Jensen's inequality. -/
theorem hub_energy_ge (hM0 : ∀ x, 0 ≤ M x) (hpos : 0 < ∫ z in Z, M z) :
    (∫ z in Z, M z) *
        ∫ p in Ioi (0 : ℝ), M p * (u p - (∫ z in Z, M z * u z) / ∫ z in Z, M z) ^ 2 ≤
      (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), Z.indicator 1 (x + s) * signedShiftJump M u s x) +
        ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), Z.indicator 1 x * signedShiftJump M u s x := by
  set ū := (∫ z in Z, M z * u z) / ∫ z in Z, M z with hūdef
  rw [← integral_hubUpperPairs_eq hMc huc hMB hZm, ← integral_hubLowerPairs_eq hMc huc hMB hZm hZ]
  have hg : Integrable (pairEnergy M u) := integrable_pairEnergy hMc huc hMB
  rw [← integral_add (hg.indicator (measurableSet_hubUpperPairs hZm))
    (hg.indicator (measurableSet_hubLowerPairs hZm))]
  have e : (fun q => (hubUpperPairs Z).indicator (pairEnergy M u) q +
      (hubLowerPairs Z).indicator (pairEnergy M u) q) = (hubPairs Z).indicator (pairEnergy M u) :=
    funext (indicator_hubUpper_add_hubLower M u Z)
  rw [e]
  have hint := hg.indicator (measurableSet_hubPairs hZm)
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  -- the inner integral is the hub pairing of `p`
  have hMcs : HasCompactSupport M := HasCompactSupport.intro isCompact_Icc fun y hy =>
    hMB y (not_lt.mp fun h' => hy (abs_le.mp h'.le))
  have hMi : Integrable M := hMc.integrable_of_hasCompactSupport hMcs
  have hMui : Integrable fun z => M z * u z :=
    (hMc.mul huc).integrable_of_hasCompactSupport hMcs.mul_right
  have hMu2i : Integrable fun z => M z * u z ^ 2 :=
    (hMc.mul (huc.pow 2)).integrable_of_hasCompactSupport hMcs.mul_right
  have hinner : ∀ p, (∫ z, (hubPairs Z).indicator (pairEnergy M u) (p, z)) =
      (Ioi (0 : ℝ)).indicator (fun p => M p * ∫ z in Z, M z * (u p - u z) ^ 2) p := by
    intro p
    by_cases hp : 0 < p
    · rw [Set.indicator_of_mem (show p ∈ Ioi (0 : ℝ) from hp), ← integral_const_mul,
        ← integral_indicator hZm]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      dsimp only
      by_cases hz : z ∈ Z
      · rw [Set.indicator_of_mem (show (p, z) ∈ hubPairs Z from ⟨hp, hz⟩),
          Set.indicator_of_mem hz]
        simp only [pairEnergy]
        ring
      · have hnot : (p, z) ∉ hubPairs Z := fun hh => hz hh.2
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hz]
    · rw [Set.indicator_of_notMem (show p ∉ Ioi (0 : ℝ) from hp)]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
      exact Set.indicator_of_notMem (fun hh => hp hh.1) _
  simp_rw [hinner]
  rw [integral_indicator measurableSet_Ioi, ← integral_const_mul]
  have hRi : IntegrableOn (fun p => M p * ∫ z in Z, M z * (u p - u z) ^ 2) (Ioi 0) := by
    have h := hint.integral_prod_left
    refine (h.integrableOn (s := Ioi (0 : ℝ))).congr_fun (fun p hp => ?_) measurableSet_Ioi
    simp only
    rw [hinner p, Set.indicator_of_mem hp]
  have hLi : IntegrableOn (fun p => (∫ z in Z, M z) * (M p * (u p - ū) ^ 2)) (Ioi 0) := by
    refine (Integrable.const_mul ?_ _).integrableOn
    exact (hMc.mul ((huc.sub continuous_const).pow 2)).integrable_of_hasCompactSupport
      hMcs.mul_right
  refine setIntegral_mono_on hLi hRi measurableSet_Ioi fun p _ => ?_
  have hJ := hub_jensen hZm hMi.integrableOn hMui.integrableOn hMu2i.integrableOn
    (fun z _ => hM0 z) hpos (u p)
  have := mul_le_mul_of_nonneg_left hJ (hM0 p)
  calc (∫ z in Z, M z) * (M p * (u p - ū) ^ 2) = M p * ((∫ z in Z, M z) * (u p - ū) ^ 2) := by
        ring
    _ ≤ M p * ∫ z in Z, M z * (u p - u z) ^ 2 := this

end HubSum

/-! ### The fold with a hub and a two-point cost -/

/-- **The fold with a hub and a cost.** If the folded conductance satisfies
`κ(s) + κ(s + 2x) ≥ k (1_Z(x) + 1_Z(x + s)) − G(x, x + s)` on `x + s < B`, with `0 ≤ G(x, y) ≤ G_y(y)`,
then `∫ κ I ≥ 2k (hub energy) − 4 ∫_{x>0} C₁ u² M − 4B ∫_{y>0} G_y M u²`, where
`C₁(x) ≥ ∫_{s>0} G(x, x + s) M(x + s) ds` and `G(x, ·) = 0` for `x ≥ X₀`: the hub pairs keep their
conductance, the cost is paid on `u(x)²` with the inner weight `C₁` and on `u(y)²` with the outer
weight `2X₀ G_y`. -/
theorem integral_kappa_mul_gaugeJumpProfile_ge_hub {M u κ : ℝ → ℝ} {B K C : ℝ}
    (hMc : Continuous M) (huc : Continuous u)
    (hMe : ∀ x, M (-x) = M x) (hue : ∀ x, u (-x) = u x) (hM0 : ∀ x, 0 ≤ M x)
    (hM1 : ∀ x, M x ≤ 1) (hMB : ∀ x, B ≤ |x| → M x = 0)
    (huL : ∀ a b, |u a - u b| ≤ K * |a - b|) (hB0 : 0 < B)
    (hκm : Measurable κ) (hC : 0 ≤ C) (hκ : ∀ t, 0 < t → t ≤ 2 * B → |κ t| ≤ C / t)
    {Z : Set ℝ} (hZm : MeasurableSet Z) (hZ : Z ⊆ Ioi 0) (k : ℝ)
    {G : ℝ → ℝ → ℝ} (hGm : ∀ x, Measurable (G x)) {Gy : ℝ → ℝ} (hGym : Measurable Gy)
    {G₁ : ℝ} (hG0 : ∀ x y, 0 ≤ G x y) (hGy : ∀ x y, G x y ≤ Gy y) (hGy1 : ∀ y, Gy y ≤ G₁)
    {C₁ : ℝ → ℝ} (hC₁m : Measurable C₁) (hC₁0 : ∀ x, 0 ≤ C₁ x) (hC₁1 : ∀ x, C₁ x ≤ G₁)
    (hC₁ : ∀ x, 0 < x → x < B → (∫ s in Ioi (0 : ℝ), G x (x + s) * M (x + s)) ≤ C₁ x)
    {X₀ : ℝ} (hX₀ : 0 < X₀) (hGX : ∀ x y, X₀ ≤ x → G x y = 0)
    (hfold : ∀ s x, 0 < s → 0 < x → x + s < B →
      k * (Z.indicator 1 x + Z.indicator 1 (x + s)) - G x (x + s) ≤ κ s + κ (s + 2 * x)) :
    2 * k * ((∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
          Z.indicator 1 (x + s) * signedShiftJump M u s x) +
        ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), Z.indicator 1 x * signedShiftJump M u s x) -
      4 * (∫ x in Ioi (0 : ℝ), C₁ x * (u x ^ 2 * M x)) -
        4 * X₀ * ∫ y in Ioi (0 : ℝ), Gy y * M y * u y ^ 2 ≤
      ∫ t in Ioi (0 : ℝ), κ t * gaugeJumpProfile M u t := by
  rw [integral_kappa_mul_gaugeJumpProfile_eq_fold_sum hMc huc hMe hue hM0 hM1 hMB huL hB0 hκm hC hκ]
  have hG10 : 0 ≤ G₁ := (hC₁0 0).trans (hC₁1 0)
  have hMB' : ∀ y, B ≤ y → M y = 0 := fun y hy => hMB y (by rw [abs_of_pos (by linarith)]; exact hy)
  have hMcs : HasCompactSupport M :=
    HasCompactSupport.intro (isCompact_Icc (a := -B) (b := B)) fun y hy =>
      hMB y (not_le.mp fun h => hy (abs_le.mp h)).le
  have hu2M : Integrable fun x => u x ^ 2 * M x :=
    ((huc.pow 2).mul hMc).integrable_of_hasCompactSupport hMcs.mul_left
  have hGMu : Integrable fun y => Gy y * M y * u y ^ 2 := by
    have h := hu2M.bdd_mul (c := G₁) hGym.aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((hG0 0 y).trans (hGy 0 y))]; exact hGy1 y)
    exact h.congr (ae_of_all _ fun y => by ring)
  have hC₁i : Integrable fun x => C₁ x * (u x ^ 2 * M x) :=
    hu2M.bdd_mul (c := G₁) hC₁m.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hC₁0 x)]; exact hC₁1 x)
  set Γ₂ := ∫ y in Ioi (0 : ℝ), Gy y * M y * u y ^ 2 with hΓ₂def
  -- the folded integrand is integrable in the outer point
  have hIS := integrable_kappa_mul_signedShiftJump_prod hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
  have hID := integrable_foldedKappaCrossing hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
  have hA : IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ), κ s * signedShiftJump M u s x) (Ioi 0) :=
    hIS.integral_prod_right
  have hCr : IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ), κ (s + 2 * x) * signedShiftJump M u s x)
      (Ioi 0) :=
    IntegrableOn.congr_fun hID.integral_prod_right
      (fun x hx => integral_foldedKappaCrossing_eq (mem_Ioi.mp hx)) measurableSet_Ioi
  have hsum : IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ),
      (κ s + κ (s + 2 * x)) * signedShiftJump M u s x) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hA.add hCr) (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := hx
    simp only [Pi.add_apply]
    rw [← integral_add (integrableOn_kappa_mul_signedShiftJump_section hMc huc hM0 hM1 hMB huL
        hB0 hκm hC hκ hx0)
      (integrableOn_kappa_reflect_mul_signedShiftJump_section hMc huc hM0 hM1 hMB huL hB0 hκm hC
        hκ hx0)]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  have hH1 := integrableOn_hubUpper_section hMc huc hMB hZm (u := u)
  have hH2 := integrableOn_hubLower_section hMc huc hMB hZm hZ (u := u)
  -- the jump of a fixed outer point, as an integrable section
  have hJs : ∀ x, IntegrableOn (fun s => signedShiftJump M u s x) (Ioi 0) := fun x => by
    have h : Integrable fun s => signedShiftJump M u s x := by
      have hcs : HasCompactSupport fun s => signedShiftJump M u s x :=
        HasCompactSupport.intro (isCompact_Icc (a := -x - B) (b := B - x)) fun s hs => by
          unfold signedShiftJump
          rw [hMB (x + s) (by
            rcases not_and_or.mp (mem_Icc.not.mp hs) with h | h
            · rw [abs_of_neg (by linarith)]; linarith [not_le.mp h]
            · rw [abs_of_pos (by linarith [not_le.mp h])]; linarith [not_le.mp h]),
            mul_zero, zero_mul]
      exact (by unfold signedShiftJump; fun_prop : Continuous fun s => signedShiftJump M u s x
        ).integrable_of_hasCompactSupport hcs
    exact h.integrableOn
  -- the pointwise lower bound of the inner integral
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      k * (∫ s in Ioi (0 : ℝ), Z.indicator 1 (x + s) * signedShiftJump M u s x) +
          k * (∫ s in Ioi (0 : ℝ), Z.indicator 1 x * signedShiftJump M u s x) -
        2 * (C₁ x * (u x ^ 2 * M x)) - 2 * Γ₂ * (Ioc 0 X₀).indicator 1 x ≤
      ∫ s in Ioi (0 : ℝ), (κ s + κ (s + 2 * x)) * signedShiftJump M u s x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hJx := hJs x
    have hZ1 : IntegrableOn (fun s => Z.indicator 1 (x + s) * signedShiftJump M u s x) (Ioi 0) :=
      hJx.bdd_mul (c := 1) ((measurable_const.indicator hZm).comp (measurable_const_add x)
        ).aestronglyMeasurable (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs]
          by_cases h : x + s ∈ Z <;> simp [h])
    have hZ2 : IntegrableOn (fun s => Z.indicator 1 x * signedShiftJump M u s x) (Ioi 0) :=
      hJx.const_mul _
    have hGJ : IntegrableOn (fun s => G x (x + s) * signedShiftJump M u s x) (Ioi 0) :=
      hJx.bdd_mul (c := G₁) ((hGm x).comp (measurable_const_add x)).aestronglyMeasurable
        (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs]
          rw [abs_of_nonneg (hG0 _ _)]; exact (hGy _ _).trans (hGy1 _))
    have hinner : IntegrableOn (fun s => (κ s + κ (s + 2 * x)) * signedShiftJump M u s x)
        (Ioi 0) := by
      refine IntegrableOn.congr_fun ((integrableOn_kappa_mul_signedShiftJump_section hMc huc hM0
        hM1 hMB huL hB0 hκm hC hκ hx0).add (integrableOn_kappa_reflect_mul_signedShiftJump_section
        hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ hx0)) (fun s _ => ?_) measurableSet_Ioi
      simp only [Pi.add_apply]; ring
    have hlow : IntegrableOn (fun s => k * (Z.indicator 1 (x + s) * signedShiftJump M u s x) +
        k * (Z.indicator 1 x * signedShiftJump M u s x) -
          G x (x + s) * signedShiftJump M u s x) (Ioi 0) :=
      ((hZ1.const_mul k).add (hZ2.const_mul k)).sub hGJ
    have hmono := setIntegral_mono_on hlow hinner measurableSet_Ioi fun s hs => by
      have hs0 : (0 : ℝ) < s := hs
      have hJ0 := signedShiftJump_nonneg' hM0 (F := u) s x
      by_cases hxs : x + s < B
      · have hk := mul_le_mul_of_nonneg_right (hfold s x hs0 hx0 hxs) hJ0
        nlinarith [hk]
      · rw [signedShiftJump_eq_zero_of_le_add hMB hB0 (u := u) (not_lt.mp hxs)]
        simp
    have eL : (∫ s in Ioi (0 : ℝ), (k * (Z.indicator 1 (x + s) * signedShiftJump M u s x) +
        k * (Z.indicator 1 x * signedShiftJump M u s x) -
          G x (x + s) * signedShiftJump M u s x)) =
        k * (∫ s in Ioi (0 : ℝ), Z.indicator 1 (x + s) * signedShiftJump M u s x) +
          k * (∫ s in Ioi (0 : ℝ), Z.indicator 1 x * signedShiftJump M u s x) -
            ∫ s in Ioi (0 : ℝ), G x (x + s) * signedShiftJump M u s x := by
      have i1 : IntegrableOn (fun s => k * (Z.indicator 1 (x + s) * signedShiftJump M u s x))
          (Ioi 0) := hZ1.const_mul k
      have i2 : IntegrableOn (fun s => k * (Z.indicator 1 x * signedShiftJump M u s x)) (Ioi 0) :=
        hZ2.const_mul k
      have i12 : IntegrableOn (fun s => k * (Z.indicator 1 (x + s) * signedShiftJump M u s x) +
          k * (Z.indicator 1 x * signedShiftJump M u s x)) (Ioi 0) := i1.add i2
      rw [integral_sub i12 hGJ, integral_add i1 i2, integral_const_mul, integral_const_mul]
    rw [eL] at hmono
    -- the cost of the inner point and of the outer point
    have hcost : (∫ s in Ioi (0 : ℝ), G x (x + s) * signedShiftJump M u s x) ≤
        2 * (C₁ x * (u x ^ 2 * M x)) + 2 * Γ₂ * (Ioc 0 X₀).indicator 1 x := by
      have hΓ₂0 : 0 ≤ Γ₂ := setIntegral_nonneg measurableSet_Ioi fun y _ =>
        mul_nonneg (mul_nonneg ((hG0 0 y).trans (hGy 0 y)) (hM0 y)) (sq_nonneg _)
      have hind0 : 0 ≤ (Ioc 0 X₀).indicator (1 : ℝ → ℝ) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      have hC0 : 0 ≤ C₁ x * (u x ^ 2 * M x) :=
        mul_nonneg (hC₁0 x) (mul_nonneg (sq_nonneg _) (hM0 x))
      by_cases hxX : X₀ ≤ x
      · have h0 : (∫ s in Ioi (0 : ℝ), G x (x + s) * signedShiftJump M u s x) = 0 := by
          refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
          simp only [Pi.zero_apply, hGX x (x + s) hxX, zero_mul]
        rw [h0]
        nlinarith
      have hxX' : x < X₀ := not_le.mp hxX
      by_cases hxB : x < B
      · rw [Set.indicator_of_mem (show x ∈ Ioc 0 X₀ from ⟨hx0, hxX'.le⟩), Pi.one_apply, mul_one]
        have hGM : IntegrableOn (fun s => G x (x + s) * M (x + s)) (Ioi 0) := by
          have hM' : Integrable fun s => M (x + s) :=
            (hMc.integrable_of_hasCompactSupport hMcs).comp_add_left x
          exact (hM'.bdd_mul (c := G₁) ((hGm x).comp (measurable_const_add x)).aestronglyMeasurable
            (ae_of_all _ fun s => by
              simp only [Function.comp, Real.norm_eq_abs]
              rw [abs_of_nonneg (hG0 _ _)]; exact (hGy _ _).trans (hGy1 _))).integrableOn
        have hGMu' : IntegrableOn (fun s => Gy (x + s) * M (x + s) * u (x + s) ^ 2) (Ioi 0) :=
          (hGMu.comp_add_left x).integrableOn
        have hcomb : IntegrableOn (fun s => 2 * (u x ^ 2 * M x) * (G x (x + s) * M (x + s)) +
            2 * (Gy (x + s) * M (x + s) * u (x + s) ^ 2)) (Ioi 0) :=
          (hGM.const_mul _).add (hGMu'.const_mul 2)
        have hm := setIntegral_mono_on hGJ hcomb measurableSet_Ioi fun s _ => by
          unfold signedShiftJump
          have h1 := hM0 x
          have h2 := hM0 (x + s)
          have h3 := hM1 x
          have hg := hG0 x (x + s)
          have hg' := hGy x (x + s)
          have hsq : (u x - u (x + s)) ^ 2 ≤ 2 * u x ^ 2 + 2 * u (x + s) ^ 2 := by
            nlinarith [sq_nonneg (u x + u (x + s))]
          have hMM := mul_nonneg h1 h2
          have e1 := mul_le_mul_of_nonneg_left hsq (mul_nonneg hg hMM)
          have e2 : G x (x + s) * (M x * M (x + s) * (2 * u (x + s) ^ 2)) ≤
              Gy (x + s) * (1 * M (x + s) * (2 * u (x + s) ^ 2)) := by
            apply mul_le_mul hg' _ (by positivity) (hg.trans hg')
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 h2) (by positivity)
          nlinarith [e1, e2]
        have eR : (∫ s in Ioi (0 : ℝ), (2 * (u x ^ 2 * M x) * (G x (x + s) * M (x + s)) +
            2 * (Gy (x + s) * M (x + s) * u (x + s) ^ 2))) =
            2 * (u x ^ 2 * M x) * (∫ s in Ioi (0 : ℝ), G x (x + s) * M (x + s)) +
              2 * ∫ s in Ioi (0 : ℝ), Gy (x + s) * M (x + s) * u (x + s) ^ 2 := by
          rw [integral_add (hGM.const_mul _) (hGMu'.const_mul 2), integral_const_mul,
            integral_const_mul]
        rw [eR] at hm
        have htr : (∫ s in Ioi (0 : ℝ), Gy (x + s) * M (x + s) * u (x + s) ^ 2) ≤ Γ₂ := by
          have e : (∫ s in Ioi (0 : ℝ), Gy (x + s) * M (x + s) * u (x + s) ^ 2) =
              ∫ y in Ioi x, Gy y * M y * u y ^ 2 := by
            rw [setIntegral_Ioi_translate (fun y => Gy y * M y * u y ^ 2) x]
            refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [add_comm]
          rw [e]
          exact setIntegral_mono_set hGMu.integrableOn (ae_of_all _ fun y =>
            mul_nonneg (mul_nonneg ((hG0 0 y).trans (hGy 0 y)) (hM0 y)) (sq_nonneg _))
            (Eventually.of_forall fun y hy => lt_trans hx0 hy)
        have hc := hC₁ x hx0 hxB
        have hu2 : 0 ≤ u x ^ 2 * M x := mul_nonneg (sq_nonneg _) (hM0 x)
        have := mul_le_mul_of_nonneg_left hc hu2
        nlinarith [hm, htr, this]
      · have hMx : M x = 0 := hMB x (by rw [abs_of_pos hx0]; exact not_lt.mp hxB)
        have h0 : (∫ s in Ioi (0 : ℝ), G x (x + s) * signedShiftJump M u s x) = 0 := by
          refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
          simp only [Pi.zero_apply, signedShiftJump, hMx, zero_mul, mul_zero]
        rw [h0, hMx, mul_zero, mul_zero]
        nlinarith
    linarith [hmono, hcost]
  -- integrate over the outer point
  have hind : IntegrableOn (fun x => (Ioc 0 X₀).indicator (1 : ℝ → ℝ) x) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))).integrableOn
  have hL : IntegrableOn (fun x =>
      k * (∫ s in Ioi (0 : ℝ), Z.indicator 1 (x + s) * signedShiftJump M u s x) +
          k * (∫ s in Ioi (0 : ℝ), Z.indicator 1 x * signedShiftJump M u s x) -
        2 * (C₁ x * (u x ^ 2 * M x)) - 2 * Γ₂ * (Ioc 0 X₀).indicator 1 x) (Ioi 0) :=
    (((hH1.const_mul k).add (hH2.const_mul k)).sub (hC₁i.integrableOn.const_mul 2)).sub
      (hind.const_mul _)
  have hmono := setIntegral_mono_on hL hsum measurableSet_Ioi hpt
  have hB1 : (∫ x in Ioi (0 : ℝ), (Ioc 0 X₀).indicator (1 : ℝ → ℝ) x) = X₀ := by
    rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Ioc_subset_Ioi_self]
    simp [Real.volume_real_Ioc, hX₀.le]
  have eL : (∫ x in Ioi (0 : ℝ),
      (k * (∫ s in Ioi (0 : ℝ), Z.indicator 1 (x + s) * signedShiftJump M u s x) +
          k * (∫ s in Ioi (0 : ℝ), Z.indicator 1 x * signedShiftJump M u s x) -
        2 * (C₁ x * (u x ^ 2 * M x)) - 2 * Γ₂ * (Ioc 0 X₀).indicator 1 x)) =
      k * (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), Z.indicator 1 (x + s) * signedShiftJump M u s x) +
        k * (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), Z.indicator 1 x * signedShiftJump M u s x) -
          2 * (∫ x in Ioi (0 : ℝ), C₁ x * (u x ^ 2 * M x)) - 2 * Γ₂ * X₀ := by
    have i1 : IntegrableOn (fun x => k * ∫ s in Ioi (0 : ℝ),
        Z.indicator 1 (x + s) * signedShiftJump M u s x) (Ioi 0) := hH1.const_mul k
    have i2 : IntegrableOn (fun x => k * ∫ s in Ioi (0 : ℝ),
        Z.indicator 1 x * signedShiftJump M u s x) (Ioi 0) := hH2.const_mul k
    have i12 : IntegrableOn (fun x => (k * ∫ s in Ioi (0 : ℝ),
        Z.indicator 1 (x + s) * signedShiftJump M u s x) + k * ∫ s in Ioi (0 : ℝ),
          Z.indicator 1 x * signedShiftJump M u s x) (Ioi 0) := i1.add i2
    have i3 : IntegrableOn (fun x => 2 * (C₁ x * (u x ^ 2 * M x))) (Ioi 0) :=
      hC₁i.integrableOn.const_mul 2
    have i123 : IntegrableOn (fun x => (k * ∫ s in Ioi (0 : ℝ),
        Z.indicator 1 (x + s) * signedShiftJump M u s x) + (k * ∫ s in Ioi (0 : ℝ),
          Z.indicator 1 x * signedShiftJump M u s x) - 2 * (C₁ x * (u x ^ 2 * M x))) (Ioi 0) :=
      i12.sub i3
    have i4 : IntegrableOn (fun x => 2 * Γ₂ * (Ioc 0 X₀).indicator (1 : ℝ → ℝ) x) (Ioi 0) :=
      hind.const_mul _
    rw [integral_sub i123 i4, integral_sub i12 i3, integral_add i1 i2, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, hB1]
  rw [eL] at hmono
  linarith

/-! ### The Schur step -/

/-- **The pointwise Schur bound.** For `A + B > 0`:
`A (t − c)² + B t² ≥ c² · AB/(A + B)`, the defect being `((A + B)t − Ac)²/(A + B)`. -/
theorem schur_pointwise {A B t c : ℝ} (hAB : 0 < A + B) :
    c ^ 2 * (A * B / (A + B)) ≤ A * (t - c) ^ 2 + B * t ^ 2 := by
  have h : A * (t - c) ^ 2 + B * t ^ 2 - c ^ 2 * (A * B / (A + B)) =
      ((A + B) * t - A * c) ^ 2 / (A + B) := by
    field_simp
    ring
  have : 0 ≤ ((A + B) * t - A * c) ^ 2 / (A + B) := div_nonneg (sq_nonneg _) hAB.le
  linarith

/-- **The Schur bound on a piece.** If `p ≥ m` on `[lo, hi]` and `ŵ + m > 0`, then
`∫_{lo}^{hi} (ŵ M (u − c)² + M p u²) ≥ c² (ŵ m/(ŵ + m)) ∫_{lo}^{hi} M`. -/
theorem integral_schur_piece_ge {M u p : ℝ → ℝ} {lo hi ŵ m c : ℝ} (hlh : lo ≤ hi)
    (hMc : Continuous M) (huc : Continuous u)
    (hpi : IntervalIntegrable (fun x => M x * p x * u x ^ 2) volume lo hi)
    (hM0 : ∀ x, 0 ≤ M x) (hwm : 0 < ŵ + m) (hp : ∀ x ∈ Icc lo hi, m ≤ p x) :
    c ^ 2 * (ŵ * m / (ŵ + m)) * (∫ x in lo..hi, M x) ≤
      ∫ x in lo..hi, (ŵ * M x * (u x - c) ^ 2 + M x * p x * u x ^ 2) := by
  rw [← intervalIntegral.integral_const_mul]
  have hL : IntervalIntegrable (fun x => c ^ 2 * (ŵ * m / (ŵ + m)) * M x) volume lo hi :=
    (hMc.intervalIntegrable lo hi).const_mul _
  have hR : IntervalIntegrable (fun x => ŵ * M x * (u x - c) ^ 2 + M x * p x * u x ^ 2) volume
      lo hi :=
    ((continuous_const.mul hMc).mul ((huc.sub continuous_const).pow 2)).intervalIntegrable
      lo hi |>.add hpi
  refine intervalIntegral.integral_mono_on hlh hL hR fun x hx => ?_
  have hs := schur_pointwise (t := u x) (c := c) hwm
  have hpx := hp x hx
  have h1 : M x * (m * u x ^ 2) ≤ M x * p x * u x ^ 2 := by
    have := mul_le_mul_of_nonneg_right hpx (sq_nonneg (u x))
    nlinarith [mul_le_mul_of_nonneg_left this (hM0 x)]
  have h2 := mul_le_mul_of_nonneg_left hs (hM0 x)
  nlinarith [h1, h2]

end GaloisForLFunctions.ArithmeticCriticalityTheory
