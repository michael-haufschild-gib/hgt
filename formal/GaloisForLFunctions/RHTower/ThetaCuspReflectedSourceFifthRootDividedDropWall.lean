import GaloisForLFunctions.HilbertMetric.FifthRootDividedDropWall
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedPtolemyTransport
import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceOddStationary

/-!
# Fifth-root divided-drop obstruction for the completed theta source

For a reflected source fibre `P_u(t)`, put

`G_u(t²) = (P_u(0) - P_u(t)) / t²`.

The second--sixth source Turán law identifies the fifth root of `G_u` as the first root
transform whose coalesced convexity is forced by known source jets.  This module proves the
exact discrete bridge to the unresolved four-point odd wall.  At every positive displacement,
wall negativity must break either decrease of `G_u^(1/5)` from squared scale `1` to `9`, or its
convex chord inequality at squared scale `4`.  Thus the remaining source problem is a literal
shape failure, not a numerical-bound deficit.
-/

open Set

namespace RHTower

noncomputable section

/-- Divided first drop of a reflected completed-source fibre. -/
def thetaCuspReflectedSourceDividedDrop (u t : ℝ) : ℝ :=
  (thetaCuspReflectedSourceProduct u 0 -
      thetaCuspReflectedSourceProduct u t) / t ^ 2

/-- Fifth root of the divided source drop.  The exponent five is forced by the exact
second--sixth coalesced Turán law. -/
def thetaCuspReflectedSourceDividedDropFifthRoot (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceDividedDrop u t ^ ((5 : ℝ)⁻¹)

/-- Fifth-root divided drop in its natural squared-displacement variable. -/
def thetaCuspReflectedSourceSquaredDividedDropFifthRoot (u x : ℝ) : ℝ :=
  thetaCuspReflectedSourceDividedDropFifthRoot u (Real.sqrt x)

theorem thetaCuspReflectedSourceDividedDrop_pos
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspReflectedSourceDividedDrop u t := by
  unfold thetaCuspReflectedSourceDividedDrop
  exact div_pos (thetaCuspReflectedSourceFirstDrop_pos u ht) (sq_pos_of_pos ht)

theorem thetaCuspReflectedSourceDividedDropFifthRoot_pos
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspReflectedSourceDividedDropFifthRoot u t := by
  unfold thetaCuspReflectedSourceDividedDropFifthRoot
  exact Real.rpow_pos_of_pos (thetaCuspReflectedSourceDividedDrop_pos u ht) _

theorem thetaCuspReflectedSourceDividedDropFifthRoot_pow_five
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceDividedDropFifthRoot u t ^ 5 =
      thetaCuspReflectedSourceDividedDrop u t := by
  unfold thetaCuspReflectedSourceDividedDropFifthRoot
  exact Real.rpow_inv_natCast_pow
    (thetaCuspReflectedSourceDividedDrop_pos u ht).le (by norm_num)

theorem contDiffAt_two_thetaCuspReflectedSourceDividedDrop
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 2 (thetaCuspReflectedSourceDividedDrop u) t := by
  unfold thetaCuspReflectedSourceDividedDrop
  apply ContDiffAt.div
  · exact contDiffAt_const.sub
      ((contDiff_thetaCuspReflectedSourceProduct u).of_le
        (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt
  · exact contDiffAt_id.pow 2
  · exact pow_ne_zero 2 ht.ne'

theorem contDiffAt_two_thetaCuspReflectedSourceDividedDropFifthRoot
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 2 (thetaCuspReflectedSourceDividedDropFifthRoot u) t := by
  have hdrop := contDiffAt_two_thetaCuspReflectedSourceDividedDrop u ht
  have hpow : ContDiffAt ℝ 2
      (fun y : ℝ => y ^ ((5 : ℝ)⁻¹))
      (thetaCuspReflectedSourceDividedDrop u t) :=
    Real.contDiffAt_rpow_const_of_ne
      (thetaCuspReflectedSourceDividedDrop_pos u ht).ne'
  change ContDiffAt ℝ 2
    ((fun y : ℝ => y ^ ((5 : ℝ)⁻¹)) ∘ thetaCuspReflectedSourceDividedDrop u) t
  exact hpow.comp t hdrop

theorem contDiffAt_two_thetaCuspReflectedSourceSquaredDividedDropFifthRoot
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ 2 (thetaCuspReflectedSourceSquaredDividedDropFifthRoot u) x := by
  have hsqrt : ContDiffAt ℝ 2 Real.sqrt x := Real.contDiffAt_sqrt hx.ne'
  have hroot := contDiffAt_two_thetaCuspReflectedSourceDividedDropFifthRoot u
    (Real.sqrt_pos.2 hx)
  change ContDiffAt ℝ 2
    (thetaCuspReflectedSourceDividedDropFifthRoot u ∘ Real.sqrt) x
  exact hroot.comp x hsqrt

theorem thetaCuspReflectedSourceSquaredDividedDropFifthRoot_sq
    (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    thetaCuspReflectedSourceSquaredDividedDropFifthRoot u (t ^ 2) =
      thetaCuspReflectedSourceDividedDropFifthRoot u t := by
  unfold thetaCuspReflectedSourceSquaredDividedDropFifthRoot
  rw [Real.sqrt_sq ht]

/-- **Global divided-drop decrease.**  Concavity of the literal source correlation angle makes
the squared-variable divided drop antitone on the whole positive axis. -/
theorem antitoneOn_thetaCuspReflectedSourceDividedDrop (u : ℝ) :
    AntitoneOn (thetaCuspReflectedSourceDividedDrop u) (Ioi 0) := by
  intro s hs t ht hst
  have hs0 : 0 < s := hs
  have ht0 : 0 < t := ht
  let q : ℝ → ℝ := thetaCuspReflectedLogAction u
  let alpha : ℝ → ℝ := HilbertMetric.riccatiCorrelationAngle q
  let d : ℝ := thetaCuspReflectedSourceProduct u 0
  let p : ℝ → ℝ := thetaCuspReflectedSourceCorrelation u
  have hd : 0 < d := by
    dsimp [d, thetaCuspReflectedSourceProduct]
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hpPos (v : ℝ) : 0 < p v := by
    dsimp [p, thetaCuspReflectedSourceCorrelation]
    exact div_pos
      (mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)) hd
  have halpha (v : ℝ) : alpha v = Real.arccos (p v) := by
    dsimp [alpha, HilbertMetric.riccatiCorrelationAngle, q, p,
      thetaCuspReflectedSourceCorrelation, thetaCuspReflectedSourceProduct]
    rw [exp_neg_thetaCuspReflectedLogAction]
    congr 2
    simp [pow_two]
  have halpha0 : alpha 0 = 0 := by
    rw [halpha]
    have hp0 : p 0 = 1 := by
      dsimp [p, thetaCuspReflectedSourceCorrelation]
      exact div_self hd.ne'
    rw [hp0, Real.arccos_one]
  have hconc : ConcaveOn ℝ (Icc 0 t) alpha := by
    simpa only [alpha, q] using
      concaveOn_thetaCuspReflectedLogCorrelationAngle (u := u) (T := t) ht0.le
  let r : ℝ := s / t
  have hr0 : 0 ≤ r := div_nonneg hs0.le ht0.le
  have hr1 : r ≤ 1 := (div_le_one ht0).2 hst
  have hscaleRaw := hconc.2
    (show (0 : ℝ) ∈ Icc 0 t by exact ⟨le_rfl, ht0.le⟩)
    (show t ∈ Icc 0 t by exact ⟨ht0.le, le_rfl⟩)
    (sub_nonneg.mpr hr1) hr0 (show (1 - r) + r = 1 by ring)
  have hscale : r * alpha t ≤ alpha s := by
    calc
      r * alpha t = (1 - r) * alpha 0 + r * alpha t := by rw [halpha0]; ring
      _ ≤ alpha ((1 - r) * 0 + r * t) := by
        simpa only [smul_eq_mul] using hscaleRaw
      _ = alpha s := by
        congr 1
        dsimp [r]
        field_simp
        ring
  have has0 : 0 ≤ alpha s := by rw [halpha]; exact Real.arccos_nonneg _
  have hat0 : 0 ≤ alpha t := by rw [halpha]; exact Real.arccos_nonneg _
  have hasHalf : alpha s ≤ Real.pi / 2 := by
    rw [halpha]
    exact Real.arccos_le_pi_div_two.mpr (hpPos _).le
  have hatHalf : alpha t ≤ Real.pi / 2 := by
    rw [halpha]
    exact Real.arccos_le_pi_div_two.mpr (hpPos _).le
  have hnorm := HilbertMetric.cosineDividedDrop_antitone_of_angleScaling
    hs0 hst has0 hat0 hasHalf hatHalf hscale
  have hcos (v : ℝ) (hv : 0 ≤ v) : Real.cos (alpha v) = p v := by
    rw [halpha]
    apply Real.cos_arccos
    · linarith [(hpPos v).le]
    · have hraw := (strictAntiOn_thetaCuspFullSource_mul_reflect u).antitoneOn
        (show (0 : ℝ) ∈ Ici 0 by simp) hv hv
      have hraw' : thetaCuspReflectedSourceProduct u v ≤ d := by
        simpa only [thetaCuspReflectedSourceProduct, d] using hraw
      exact (div_le_one hd).mpr hraw'
  rw [hcos s hs0.le, hcos t ht0.le] at hnorm
  have hscaleP (v : ℝ) : d * p v = thetaCuspReflectedSourceProduct u v := by
    dsimp [p, thetaCuspReflectedSourceCorrelation]
    exact mul_div_cancel₀ _ hd.ne'
  unfold thetaCuspReflectedSourceDividedDrop
  calc
    (thetaCuspReflectedSourceProduct u 0 - thetaCuspReflectedSourceProduct u t) /
        t ^ 2 = d * ((1 - p t) / t ^ 2) := by
      rw [show d * ((1 - p t) / t ^ 2) = (d - d * p t) / t ^ 2 by ring,
        hscaleP]
    _ ≤ d * ((1 - p s) / s ^ 2) := mul_le_mul_of_nonneg_left hnorm hd.le
    _ = (thetaCuspReflectedSourceProduct u 0 - thetaCuspReflectedSourceProduct u s) /
        s ^ 2 := by
      rw [show d * ((1 - p s) / s ^ 2) = (d - d * p s) / s ^ 2 by ring,
        hscaleP]

/-- The fifth-root transform preserves the global divided-drop decrease. -/
theorem antitoneOn_thetaCuspReflectedSourceDividedDropFifthRoot (u : ℝ) :
    AntitoneOn (thetaCuspReflectedSourceDividedDropFifthRoot u) (Ioi 0) := by
  intro s hs t ht hst
  unfold thetaCuspReflectedSourceDividedDropFifthRoot
  exact Real.rpow_le_rpow
    (thetaCuspReflectedSourceDividedDrop_pos u ht).le
    (antitoneOn_thetaCuspReflectedSourceDividedDrop u hs ht hst)
    (by positivity)

/-- Ordinary source monotonicity supplies the unnormalized two-step drop condition needed by
the fifth-root wall bridge. -/
theorem thetaCuspReflectedSource_first_to_two_dividedDrop
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceDividedDropFifthRoot u t ^ 5 ≤
      4 * thetaCuspReflectedSourceDividedDropFifthRoot u (2 * t) ^ 5 := by
  rw [thetaCuspReflectedSourceDividedDropFifthRoot_pow_five u ht,
    thetaCuspReflectedSourceDividedDropFifthRoot_pow_five u (by positivity : 0 < 2 * t)]
  unfold thetaCuspReflectedSourceDividedDrop
  have hmono : thetaCuspReflectedSourceProduct u (2 * t) ≤
      thetaCuspReflectedSourceProduct u t := by
    exact (strictAntiOn_thetaCuspFullSource_mul_reflect u).antitoneOn
      ht.le (show 2 * t ∈ Ici (0 : ℝ) by simp only [mem_Ici]; positivity) (by linarith)
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  calc
    (thetaCuspReflectedSourceProduct u 0 - thetaCuspReflectedSourceProduct u t) /
          t ^ 2 ≤
        (thetaCuspReflectedSourceProduct u 0 -
            thetaCuspReflectedSourceProduct u (2 * t)) / t ^ 2 :=
      (div_le_div_iff_of_pos_right ht2).2 (by linarith)
    _ = 4 * ((thetaCuspReflectedSourceProduct u 0 -
            thetaCuspReflectedSourceProduct u (2 * t)) / (2 * t) ^ 2) := by
      field_simp
      ring

/-- Decrease and the `1,4,9` convex chord of the fifth-root divided drop force the exact
reflection-odd four-point wall. -/
theorem thetaCuspReflectedSourceOddParityWall_nonneg_of_fifthRootShape
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hdecr : thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t) ≤
      thetaCuspReflectedSourceDividedDropFifthRoot u t)
    (hconv : 8 * thetaCuspReflectedSourceDividedDropFifthRoot u (2 * t) ≤
      5 * thetaCuspReflectedSourceDividedDropFifthRoot u t +
        3 * thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t)) :
    0 ≤ thetaCuspReflectedSourceOddParityWall u t := by
  let a := thetaCuspReflectedSourceDividedDropFifthRoot u t
  let b := thetaCuspReflectedSourceDividedDropFifthRoot u (2 * t)
  let c := thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t)
  have ha : 0 < a := thetaCuspReflectedSourceDividedDropFifthRoot_pos u ht
  have hb : 0 ≤ b :=
    (thetaCuspReflectedSourceDividedDropFifthRoot_pos u (by positivity : 0 < 2 * t)).le
  have hc : 0 ≤ c :=
    (thetaCuspReflectedSourceDividedDropFifthRoot_pos u (by positivity : 0 < 3 * t)).le
  have hwall := HilbertMetric.fifthRootConvexChord_forces_wall
    ha hb hc hdecr hconv (thetaCuspReflectedSource_first_to_two_dividedDrop u ht)
  have ha5 : a ^ 5 = thetaCuspReflectedSourceDividedDrop u t :=
    thetaCuspReflectedSourceDividedDropFifthRoot_pow_five u ht
  have hb5 : b ^ 5 = thetaCuspReflectedSourceDividedDrop u (2 * t) :=
    thetaCuspReflectedSourceDividedDropFifthRoot_pow_five u (by positivity)
  have hc5 : c ^ 5 = thetaCuspReflectedSourceDividedDrop u (3 * t) :=
    thetaCuspReflectedSourceDividedDropFifthRoot_pow_five u (by positivity)
  rw [ha5, hb5, hc5] at hwall
  unfold thetaCuspReflectedSourceDividedDrop at hwall
  rw [thetaCuspReflectedSourceOddParityWall_eq_dropProduct]
  unfold thetaCuspReflectedSourceFirstDrop thetaCuspReflectedSourceMiddleDrop
    thetaCuspReflectedSourceFullDrop
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  field_simp at hwall
  ring_nf at hwall ⊢
  nlinarith

/-- **Unconditional fifth-root shape obstruction.**  Every real source fibre is either at a
nonpositive displacement, has nonnegative odd wall, or exhibits one of the two exact discrete
failures forbidden by decreasing convexity of the fifth-root divided-drop profile. -/
theorem thetaCuspReflectedSourceOddParityWall_or_fifthRootShapeFailure
    (u t : ℝ) :
    t ≤ 0 ∨
      0 ≤ thetaCuspReflectedSourceOddParityWall u t ∨
      thetaCuspReflectedSourceDividedDropFifthRoot u t <
        thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t) ∨
      5 * thetaCuspReflectedSourceDividedDropFifthRoot u t +
          3 * thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t) <
        8 * thetaCuspReflectedSourceDividedDropFifthRoot u (2 * t) := by
  by_cases ht : 0 < t
  · right
    by_cases hwall : 0 ≤ thetaCuspReflectedSourceOddParityWall u t
    · exact Or.inl hwall
    right
    by_cases hdecr : thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t) ≤
        thetaCuspReflectedSourceDividedDropFifthRoot u t
    · right
      have hnotconv : ¬ 8 * thetaCuspReflectedSourceDividedDropFifthRoot u (2 * t) ≤
          5 * thetaCuspReflectedSourceDividedDropFifthRoot u t +
            3 * thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t) := by
        intro hconv
        exact hwall (thetaCuspReflectedSourceOddParityWall_nonneg_of_fifthRootShape
          u ht hdecr hconv)
      exact lt_of_not_ge hnotconv
    · left
      exact lt_of_not_ge hdecr
  · left
    exact le_of_not_gt ht

/-- **Monotonicity burden eliminated.**  Global source-angle concavity rules out the first shape
failure, so a positive-displacement negative odd wall forces the single strict `1,4,9` convexity
failure of the fifth-root divided drop. -/
theorem thetaCuspReflectedSourceOddParityWall_or_fifthRootConvexityFailure
    (u t : ℝ) :
    t ≤ 0 ∨
      0 ≤ thetaCuspReflectedSourceOddParityWall u t ∨
      5 * thetaCuspReflectedSourceDividedDropFifthRoot u t +
          3 * thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t) <
        8 * thetaCuspReflectedSourceDividedDropFifthRoot u (2 * t) := by
  by_cases ht : 0 < t
  · right
    by_cases hwall : 0 ≤ thetaCuspReflectedSourceOddParityWall u t
    · exact Or.inl hwall
    right
    have hdecr : thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t) ≤
        thetaCuspReflectedSourceDividedDropFifthRoot u t :=
      antitoneOn_thetaCuspReflectedSourceDividedDropFifthRoot u
        (show t ∈ Ioi (0 : ℝ) from ht)
        (show 3 * t ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; positivity)
        (by linarith)
    have hnotconv : ¬ 8 * thetaCuspReflectedSourceDividedDropFifthRoot u (2 * t) ≤
        5 * thetaCuspReflectedSourceDividedDropFifthRoot u t +
          3 * thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t) := by
      intro hconv
      exact hwall (thetaCuspReflectedSourceOddParityWall_nonneg_of_fifthRootShape
        u ht hdecr hconv)
    exact lt_of_not_ge hnotconv
  · left
    exact le_of_not_gt ht

/-- A single rank-two log-convex minor of the ordinary divided-drop profile at squared scales
`1,4,9` forces the literal rank-four odd wall.  Positivity lets the fifth-root transform preserve
the minor, while global source-angle concavity supplies the required decrease. -/
theorem thetaCuspReflectedSourceOddParityWall_nonneg_of_dividedDrop_logConvex
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hlog : thetaCuspReflectedSourceDividedDrop u (2 * t) ^ 2 ≤
      thetaCuspReflectedSourceDividedDrop u t *
        thetaCuspReflectedSourceDividedDrop u (3 * t)) :
    0 ≤ thetaCuspReflectedSourceOddParityWall u t := by
  let a := thetaCuspReflectedSourceDividedDropFifthRoot u t
  let b := thetaCuspReflectedSourceDividedDropFifthRoot u (2 * t)
  let c := thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t)
  have ha : 0 < a := thetaCuspReflectedSourceDividedDropFifthRoot_pos u ht
  have hb : 0 ≤ b :=
    (thetaCuspReflectedSourceDividedDropFifthRoot_pos u (by positivity : 0 < 2 * t)).le
  have hc : 0 ≤ c :=
    (thetaCuspReflectedSourceDividedDropFifthRoot_pos u (by positivity : 0 < 3 * t)).le
  have hca : c ≤ a :=
    antitoneOn_thetaCuspReflectedSourceDividedDropFifthRoot u
      (show t ∈ Ioi (0 : ℝ) from ht)
      (show 3 * t ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; positivity)
      (by linarith)
  have ha5 : a ^ 5 = thetaCuspReflectedSourceDividedDrop u t :=
    thetaCuspReflectedSourceDividedDropFifthRoot_pow_five u ht
  have hb5 : b ^ 5 = thetaCuspReflectedSourceDividedDrop u (2 * t) :=
    thetaCuspReflectedSourceDividedDropFifthRoot_pow_five u (by positivity)
  have hc5 : c ^ 5 = thetaCuspReflectedSourceDividedDrop u (3 * t) :=
    thetaCuspReflectedSourceDividedDropFifthRoot_pow_five u (by positivity)
  have hlogPow : (b ^ 2) ^ 5 ≤ (a * c) ^ 5 := by
    calc
      (b ^ 2) ^ 5 = (b ^ 5) ^ 2 := by ring
      _ ≤ a ^ 5 * c ^ 5 := by simpa only [hb5, ha5, hc5] using hlog
      _ = (a * c) ^ 5 := by ring
  have hlogRoot : b ^ 2 ≤ a * c :=
    le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0)
      (mul_nonneg ha.le hc) hlogPow
  have hconv := HilbertMetric.logConvexTriple_forces_weightedChord
    ha.le hb hc hca hlogRoot
  exact thetaCuspReflectedSourceOddParityWall_nonneg_of_fifthRootShape
    u ht hca hconv

/-- **Rank reduction of every possible source failure.**  A negative rank-four odd wall at
positive displacement forces a reversed rank-two Hankel minor of the ordinary divided drops at
squared scales `1,4,9`. -/
theorem thetaCuspReflectedSourceOddParityWall_or_dividedDropLogConvexityFailure
    (u t : ℝ) :
    t ≤ 0 ∨
      0 ≤ thetaCuspReflectedSourceOddParityWall u t ∨
      thetaCuspReflectedSourceDividedDrop u t *
          thetaCuspReflectedSourceDividedDrop u (3 * t) <
        thetaCuspReflectedSourceDividedDrop u (2 * t) ^ 2 := by
  by_cases ht : 0 < t
  · right
    by_cases hwall : 0 ≤ thetaCuspReflectedSourceOddParityWall u t
    · exact Or.inl hwall
    right
    by_contra hnot
    have hlog : thetaCuspReflectedSourceDividedDrop u (2 * t) ^ 2 ≤
        thetaCuspReflectedSourceDividedDrop u t *
          thetaCuspReflectedSourceDividedDrop u (3 * t) := by
      exact le_of_not_gt hnot
    exact hwall
      (thetaCuspReflectedSourceOddParityWall_nonneg_of_dividedDrop_logConvex u ht hlog)
  · left
    exact le_of_not_gt ht

/-- **Differential localization of every possible rank-four failure.**  A negative source wall
forces genuine negative curvature of the squared-variable fifth-root divided drop at an interior
scale between `t²` and `9t²`; a merely discrete convexity defect cannot remain hidden. -/
theorem thetaCuspReflectedSourceOddParityWall_or_exists_fifthRootCurvatureFailure
    (u t : ℝ) :
    t ≤ 0 ∨
      0 ≤ thetaCuspReflectedSourceOddParityWall u t ∨
      ∃ x ∈ Ioo (t ^ 2) (9 * t ^ 2),
        (deriv^[2] (thetaCuspReflectedSourceSquaredDividedDropFifthRoot u)) x < 0 := by
  by_cases ht : 0 < t
  · right
    by_cases hwall : 0 ≤ thetaCuspReflectedSourceOddParityWall u t
    · exact Or.inl hwall
    right
    have hviol :
        5 * thetaCuspReflectedSourceDividedDropFifthRoot u t +
            3 * thetaCuspReflectedSourceDividedDropFifthRoot u (3 * t) <
          8 * thetaCuspReflectedSourceDividedDropFifthRoot u (2 * t) := by
      rcases thetaCuspReflectedSourceOddParityWall_or_fifthRootConvexityFailure u t with
        hnonpos | hnonneg | hfailure
      · linarith
      · exact False.elim (hwall hnonneg)
      · exact hfailure
    let f : ℝ → ℝ := thetaCuspReflectedSourceSquaredDividedDropFifthRoot u
    let x0 : ℝ := t ^ 2
    have hx0 : 0 < x0 := by dsimp [x0]; positivity
    have hcont : ContinuousOn f (Icc x0 (9 * x0)) := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hx0 hx.1
      exact (contDiffAt_two_thetaCuspReflectedSourceSquaredDividedDropFifthRoot
        u hxpos).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Ioo x0 (9 * x0)) := by
      intro x hx
      have hxpos : 0 < x := hx0.trans hx.1
      dsimp only [f]
      exact (contDiffAt_two_thetaCuspReflectedSourceSquaredDividedDropFifthRoot
        u hxpos).differentiableAt (by norm_num) |>.differentiableWithinAt
    have hdiff' : DifferentiableOn ℝ (deriv f) (Ioo x0 (9 * x0)) := by
      intro x hx
      have hxpos : 0 < x := hx0.trans hx.1
      have hsmooth := contDiffAt_two_thetaCuspReflectedSourceSquaredDividedDropFifthRoot
        u hxpos
      dsimp only [f]
      exact (hsmooth.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
        |>.differentiableWithinAt
    have hviol' : 5 * f x0 + 3 * f (9 * x0) < 8 * f (4 * x0) := by
      dsimp only [f, x0]
      rw [thetaCuspReflectedSourceSquaredDividedDropFifthRoot_sq u ht.le,
        show 9 * t ^ 2 = (3 * t) ^ 2 by ring,
        thetaCuspReflectedSourceSquaredDividedDropFifthRoot_sq u (by positivity),
        show 4 * t ^ 2 = (2 * t) ^ 2 by ring,
        thetaCuspReflectedSourceSquaredDividedDropFifthRoot_sq u (by positivity)]
      exact hviol
    simpa only [f, x0] using
      HilbertMetric.exists_secondDeriv_neg_of_weightedChordViolation
        hx0 hcont hdiff hdiff' hviol'
  · left
    exact le_of_not_gt ht

end

end RHTower
