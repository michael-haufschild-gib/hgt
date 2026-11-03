import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.TheBarnesPeriodIsAHeckeEigenfunctionForEveryPrime
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.LewisHeckeEisensteinEigenvalue
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected

/-!
# The Eisenstein period is a Hecke eigenfunction for every prime

`E_w = period w 1 (−ζ(w)) (state w)` is the global Lewis period of the actual Mayer state
(`eisensteinPeriod`; `eisensteinLewisPeriod s = E_{2s}`). On the regular parameters
`U = {Re w > 0} ∖ {1, 2}` it satisfies the Lewis three-term equation and inversion
(`eisensteinPeriod_three_term`, `eisensteinPeriod_reciprocity`) and equals the Mayer disc value on
`(½, 7/2)`.

* **Propagation** (`positive_line_induction`): the three-term equation `ψ(a + 1) = ψ(a) − (a + 1)^{−w}
  ψ(a/(a + 1))` and inversion reach every `a > 0` from `(½, 7/2)`. Hence `w ↦ E_w(a)` is holomorphic
  on `U` for every `a > 0` (`differentiableAt_eisensteinPeriod`), and for `Re w > 2` the period is the
  Barnes boundary period `E_w(a) = P_w(a, 1)` (`eisensteinPeriod_eq_barnes`).
* **Every prime** (`eisensteinPeriod_lewisHecke`): `T_{p,w/2} E_w = (1 + p^{1−w}) E_w` on the positive
  line at every regular `w`: the Barnes cone identity holds for `Re w > 2`, and the defect is
  holomorphic on the connected set `U`.
* **Strip and resonances** (`eisensteinLewisPeriod_lewisHecke`, `resonantLewisPeriod_lewisHecke`):
  `T_{p,s} ψ_s = (1 + p^{1−2s}) ψ_s` for `0 < Re s < ½`, in particular at every Mayer resonance.
-/

noncomputable section
open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerScatteringState MayerScatteringMellin MayerScatteringPeriod
open MayerParameter MayerGlobalPeriods

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-! ### Regular parameters -/

/-- The regular parameters `Re w > 0`, `w ≠ 1, 2` of the Mayer state equation. -/
def regularParameters : Set ℂ := {w : ℂ | 0 < w.re} \ {1, 2}

theorem mem_regularParameters {w : ℂ} (hw : w ∈ regularParameters) :
    0 < w.re ∧ w ≠ 1 ∧ w ≠ 2 :=
  ⟨hw.1, fun h => hw.2 (Or.inl h), fun h => hw.2 (Or.inr h)⟩

theorem mem_regularParameters_of_re {w : ℂ} (h0 : 0 < w.re) (h1 : w.re ≠ 1) (h2 : w.re ≠ 2) :
    w ∈ regularParameters := by
  refine ⟨h0, fun h => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · exact h1 (by rw [h, Complex.one_re])
  · exact h2 (by rw [h]; norm_num)

theorem isOpen_regularParameters : IsOpen regularParameters :=
  (isOpen_lt continuous_const Complex.continuous_re).sdiff
    ((Set.finite_singleton (2 : ℂ)).insert 1).isClosed

theorem isPreconnected_regularParameters : IsPreconnected regularParameters :=
  isPreconnected_diff_of_countable_of_convex_complex (convex_halfSpace_re_gt 0)
    (isOpen_lt continuous_const Complex.continuous_re)
    ((Set.finite_singleton (2 : ℂ)).insert 1).countable (a := 3)
    (mem_regularParameters_of_re (by norm_num) (by norm_num) (by norm_num))

/-! ### The Eisenstein period at regular parameters -/

/-- The global Eisenstein Lewis period at parameter `w`. -/
def eisensteinPeriod (w a : ℂ) : ℂ := period w 1 (-riemannZeta w) (state w) a

theorem eisensteinLewisPeriod_eq (s a : ℂ) :
    eisensteinLewisPeriod s a = eisensteinPeriod (2 * s) a := rfl

/-- The Mayer state solves the regularized equation with forcing `−ζ(w)`. -/
theorem state_regularized {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hw2 : w ≠ 2) :
    regularized w hw (state w) = (1 : ℂ) • state w + constant (-riemannZeta w) := by
  have hst := state_equation hw hw1 hw2
  have hc : constant (-riemannZeta w) = -(riemannZeta w • constant 1) := by
    apply Subtype.ext
    ext z
    change -riemannZeta w = -(riemannZeta w * 1)
    ring
  rw [← source_eq hw, one_smul, hc, ← hst]
  abel

theorem eisensteinPeriod_three_term {w : ℂ} (hw : w ∈ regularParameters) {a : ℝ} (ha : 0 < a) :
    eisensteinPeriod w (a + 1 : ℝ) =
      eisensteinPeriod w a - ((a + 1 : ℝ) : ℂ) ^ (-w) * eisensteinPeriod w (a / (a + 1) : ℝ) := by
  obtain ⟨hw0, hw1, hw2⟩ := mem_regularParameters hw
  have h := three_term hw0 (by norm_num) (state w) (state_regularized hw0 hw1 hw2)
    (a := (a : ℂ)) (by simpa using ha)
  have e1 : ((a + 1 : ℝ) : ℂ) = (a : ℂ) + 1 := by push_cast; ring
  have e2 : ((a / (a + 1) : ℝ) : ℂ) = (a : ℂ) / ((a : ℂ) + 1) := by push_cast; ring
  simp only [eisensteinPeriod]
  rw [e1, e2]
  linear_combination -h

theorem eisensteinPeriod_reciprocity {w : ℂ} (hw : w ∈ regularParameters) {a : ℝ} (ha : 0 < a) :
    eisensteinPeriod w a = (a : ℂ) ^ (-w) * eisensteinPeriod w (1 / a : ℝ) := by
  obtain ⟨hw0, hw1, hw2⟩ := mem_regularParameters hw
  have h := reciprocity hw0 (by norm_num) (state w) (state_regularized hw0 hw1 hw2)
    (a := (a : ℂ)) (by simpa using ha)
  have e : ((1 / a : ℝ) : ℂ) = (a : ℂ)⁻¹ := by push_cast; ring
  simp only [eisensteinPeriod]
  rw [e, h, one_mul]

/-- On `(½, 7/2)` the period is the value of the Mayer state on its disc. -/
theorem eisensteinPeriod_eq_periodValue {w : ℂ} (hw : w ∈ regularParameters) {a : ℝ}
    (ha : a ∈ Ioo (1 / 2 : ℝ) (7 / 2)) : eisensteinPeriod w a = periodValue w a := by
  obtain ⟨hw0, hw1, hw2⟩ := mem_regularParameters hw
  have hi : (a : ℂ) - 1 ∈ MayerCutoff.inner := by
    rw [MayerCutoff.inner, Metric.mem_ball, dist_eq_norm,
      show ((a : ℂ) - 1) - 1 = ((a - 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith only [ha.1, ha.2]
  change extension w 1 (-riemannZeta w) (state w) ((a : ℂ) - 1) = plane (state w) ((a : ℂ) - 1)
  exact extension_eq_plane hw0 (by norm_num) (state w) (state_regularized hw0 hw1 hw2) hi

/-- The disc value is holomorphic in the parameter away from the pole `w = 2`. -/
theorem differentiableAt_periodValue {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2) {a : ℝ}
    (ha : a ∈ periodSegment) : DifferentiableAt ℂ (fun v => periodValue v a) w := by
  have hmem : (a : ℂ) - 1 ∈ outer := by
    have he : ((a : ℂ) - 1) - 1 = ((a - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [outer, Metric.mem_closedBall, dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs,
      abs_le]
    constructor <;> linarith only [ha.1, ha.2]
  have he : (fun v => periodValue v a) = fun v => evaluation ⟨(a : ℂ) - 1, hmem⟩ (state v) :=
    funext fun v => plane_eq (state v) ⟨(a : ℂ) - 1, hmem⟩
  rw [he]
  exact (evaluation ⟨(a : ℂ) - 1, hmem⟩).differentiableAt.comp w
    (analyticAt_state hw hw2).differentiableAt

/-! ### Propagation along the positive line -/

/-- A property of `(½, 7/2)` that propagates by the three-term step `a ↦ a + 1` (from `a` and
`a/(a + 1)`) and by inversion `a ↦ 1/a` holds on the whole positive line. -/
theorem positive_line_induction {Q : ℝ → Prop} (hbase : ∀ a ∈ Ioo (1 / 2 : ℝ) (7 / 2), Q a)
    (hstep : ∀ a, 2 ≤ a → Q a → Q (a / (a + 1)) → Q (a + 1))
    (hinv : ∀ a, 0 < a → Q (1 / a) → Q a) : ∀ a, 0 < a → Q a := by
  have hn : ∀ n : ℕ, ∀ a, 1 / 2 < a → a ≤ n + 3 → Q a := by
    intro n
    induction n with
    | zero =>
      intro a h1 h2
      push_cast at h2
      exact hbase a ⟨h1, by linarith⟩
    | succ n ih =>
      intro a h1 h2
      push_cast at h2
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      by_cases hle : a ≤ n + 3
      · exact ih a h1 hle
      · push Not at hle
        have hb := ih (a - 1) (by linarith) (by linarith)
        have hpos : 0 < a - 1 + 1 := by linarith
        have hq : Q ((a - 1) / (a - 1 + 1)) := by
          apply hbase
          constructor
          · rw [lt_div_iff₀ hpos]; linarith
          · rw [div_lt_iff₀ hpos]; linarith
        have := hstep (a - 1) (by linarith) hb hq
        rwa [sub_add_cancel] at this
  have hhalf : ∀ a, 1 / 2 < a → Q a := fun a ha =>
    hn ⌈a⌉₊ a ha (by linarith [Nat.le_ceil a])
  intro a ha
  by_cases h : 1 / 2 < a
  · exact hhalf a h
  · push Not at h
    refine hinv a ha (hhalf _ ?_)
    have : 2 ≤ 1 / a := by rw [le_div_iff₀ ha]; linarith
    linarith

/-- **`w ↦ E_w(a)` is holomorphic on the regular parameters, for every `a > 0`.** -/
theorem differentiableAt_eisensteinPeriod :
    ∀ a : ℝ, 0 < a → ∀ w ∈ regularParameters,
      DifferentiableAt ℂ (fun v => eisensteinPeriod v a) w := by
  refine positive_line_induction ?_ ?_ ?_
  · intro b hb w hw
    obtain ⟨hw0, -, hw2⟩ := mem_regularParameters hw
    have he : (fun v => eisensteinPeriod v b) =ᶠ[𝓝 w] fun v => periodValue v b :=
      Filter.eventually_of_mem (isOpen_regularParameters.mem_nhds hw)
        fun v hv => eisensteinPeriod_eq_periodValue hv hb
    exact (differentiableAt_periodValue hw0 hw2 ⟨hb.1.le, hb.2.le⟩).congr_of_eventuallyEq he
  · intro b hb h1 h2 w hw
    have hb0 : 0 < b := by linarith
    have he : (fun v => eisensteinPeriod v (b + 1 : ℝ)) =ᶠ[𝓝 w] fun v =>
        eisensteinPeriod v b - ((b + 1 : ℝ) : ℂ) ^ (-v) * eisensteinPeriod v (b / (b + 1) : ℝ) :=
      Filter.eventually_of_mem (isOpen_regularParameters.mem_nhds hw)
        fun v hv => eisensteinPeriod_three_term hv hb0
    have hpow : DifferentiableAt ℂ (fun v : ℂ => ((b + 1 : ℝ) : ℂ) ^ (-v)) w :=
      differentiableAt_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (by linarith)))
    exact ((h1 w hw).sub (hpow.mul (h2 w hw))).congr_of_eventuallyEq he
  · intro b hb h w hw
    have he : (fun v => eisensteinPeriod v b) =ᶠ[𝓝 w] fun v =>
        (b : ℂ) ^ (-v) * eisensteinPeriod v (1 / b : ℝ) :=
      Filter.eventually_of_mem (isOpen_regularParameters.mem_nhds hw)
        fun v hv => eisensteinPeriod_reciprocity hv hb
    have hpow : DifferentiableAt ℂ (fun v : ℂ => (b : ℂ) ^ (-v)) w :=
      differentiableAt_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne'))
    exact (hpow.mul (h w hw)).congr_of_eventuallyEq he

/-- **In the absolute chamber the Eisenstein period is the Barnes boundary period.** -/
theorem eisensteinPeriod_eq_barnes {w : ℂ} (hw : 2 < w.re) :
    ∀ a : ℝ, 0 < a → eisensteinPeriod w a = barnesBoundaryPeriod w a 1 := by
  have hU : w ∈ regularParameters :=
    mem_regularParameters_of_re (by linarith) (by linarith : (1 : ℝ) < w.re).ne'
      (by linarith : (2 : ℝ) < w.re).ne'
  refine positive_line_induction ?_ ?_ ?_
  · intro a ha
    rw [eisensteinPeriod_eq_periodValue hU ha, periodValue_barnes hw ⟨ha.1.le, ha.2.le⟩,
      barnesBoundaryPeriod]
    simp only [Complex.ofReal_one]
    exact add_comm _ _
  · intro a ha h1 h2
    have ha0 : 0 < a := by linarith
    rw [eisensteinPeriod_three_term hU ha0, h1, h2]
    have := barnesBoundaryPeriod_three_term hw ha0
    linear_combination this
  · intro a ha h
    rw [eisensteinPeriod_reciprocity hU ha, h, ← barnesBoundaryPeriod_reciprocity w ha]

/-! ### The Hecke eigenvalue for every prime -/

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

theorem lewisHeckeOperator_const_mul (s c : ℂ) (f : ℝ → ℂ) (a : ℝ) :
    lewisHeckeOperator p s (fun x => c * f x) a = c * lewisHeckeOperator p s f a := by
  simp only [lewisHeckeOperator, Finset.mul_sum]
  exact Finset.sum_congr rfl fun M _ => by ring

/-- **The Eisenstein period is a `T_p`-eigenfunction at every regular parameter**:
`T_{p,w/2} E_w = (1 + p · p^{−w}) E_w` on the positive line. -/
theorem eisensteinPeriod_lewisHecke {w : ℂ} (hw : w ∈ regularParameters) {a : ℝ} (ha : 0 < a) :
    lewisHeckeOperator p (w / 2) (fun x => eisensteinPeriod w x) a =
      (1 + p * (p : ℂ) ^ (-w)) * eisensteinPeriod w a := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set D : ℂ → ℂ := fun v => lewisHeckeOperator p (v / 2) (fun x => eisensteinPeriod v x) a -
    (1 + p * (p : ℂ) ^ (-v)) * eisensteinPeriod v a with hD
  have hdiff : DifferentiableOn ℂ D regularParameters := by
    intro v hv
    apply DifferentiableAt.differentiableWithinAt
    simp only [hD, lewisHeckeOperator]
    refine DifferentiableAt.sub (DifferentiableAt.fun_sum fun M hM => ?_) ?_
    · obtain ⟨hc, hx⟩ := heckeBranch_pos hM ha
      refine DifferentiableAt.mul ?_ (differentiableAt_eisensteinPeriod _ (div_pos hx hc) v hv)
      exact ((differentiableAt_id.div_const 2).const_mul 2).neg.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))
    · exact ((differentiableAt_const _).add ((differentiableAt_const _).mul
        (differentiableAt_id.neg.const_cpow (Or.inl hp0)))).mul
          (differentiableAt_eisensteinPeriod a ha v hv)
  have hzero : D =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : IsOpen {v : ℂ | 2 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (3 : ℂ) ∈ {v : ℂ | 2 < v.re} by norm_num)] with v hv
    have hE := eisensteinPeriod_eq_barnes hv
    simp only [hD, Pi.zero_apply]
    rw [sub_eq_zero, hE a ha, ← barnesBoundaryPeriod_lewisHecke (p := p) hv ha]
    simp only [lewisHeckeOperator]
    refine Finset.sum_congr rfl fun M hM => ?_
    obtain ⟨hc, hx⟩ := heckeBranch_pos hM ha
    rw [hE _ (div_pos hx hc)]
  have h3 : (3 : ℂ) ∈ regularParameters :=
    mem_regularParameters_of_re (by norm_num) (by norm_num) (by norm_num)
  have hz := (hdiff.analyticOnNhd isOpen_regularParameters).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_regularParameters h3 hzero hw
  simp only [hD, Pi.zero_apply] at hz
  exact sub_eq_zero.mp hz

/-- **Every source Hecke operator has the Eisenstein period as eigenfunction** across the strip:
`T_{p,s} ψ_s = (1 + p^{1−2s}) ψ_s`, `0 < Re s < ½`. -/
theorem eisensteinLewisPeriod_lewisHecke {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) {a : ℝ}
    (ha : 0 < a) :
    lewisHeckeOperator p s (fun x => eisensteinLewisPeriod s x) a =
      (1 + (p : ℂ) ^ (1 - 2 * s)) * eisensteinLewisPeriod s a := by
  have hre : (2 * s).re = 2 * s.re := by simp
  have hw : 2 * s ∈ regularParameters :=
    mem_regularParameters_of_re (by rw [hre]; linarith) (by rw [hre]; linarith : (2 * s).re < 1).ne
      (by rw [hre]; linarith : (2 * s).re < 2).ne
  have h := eisensteinPeriod_lewisHecke (p := p) hw ha
  rw [show 2 * s / 2 = s by ring, natCast_mul_cpow_neg hp.out.ne_zero] at h
  exact h

/-- At every Mayer scattering resonance, `T_{p,s} ψ_s = (1 + p^{1−2s}) ψ_s` for every prime `p`. -/
theorem resonantLewisPeriod_lewisHecke {s : ℂ} (hs : IsMayerScatteringResonance s) {a : ℝ}
    (ha : 0 < a) :
    lewisHeckeOperator p s (fun x => resonantLewisPeriod s x) a =
      (1 + (p : ℂ) ^ (1 - 2 * s)) * resonantLewisPeriod s a := by
  have hz := (isMayerScatteringResonance_iff_zeta_zero hs.1 hs.2.1).mp hs
  have he : eisensteinLewisPeriod s = resonantLewisPeriod s := by
    funext z
    simp only [eisensteinLewisPeriod, resonantLewisPeriod, hz, neg_zero]
  simpa only [he] using eisensteinLewisPeriod_lewisHecke (p := p) hs.1 hs.2.1 ha

end Prime

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
