/-
The sweep-selection principle: any rule assigning boundary root readings
continuously along the anchor sweep is RIGID — it is the half-angle transport of
its initial reading, with no further freedom.  Consequences:

* Over an Euler anchor whose relative sweep holonomy is near a half turn, EVERY
  selection suffers strict reading reversal: the relative reading at full sweep
  lands in the open half-plane opposite its initial position, and prime sets
  beyond any bound force this for all selections simultaneously.
* Over the empty anchor every selection is FROZEN: readings constant in the
  stage, relative displacement identically `1` — the reversal mechanism has
  nothing to act on.
* On the slit-chart annulus, a selection whose readings extend at every stage to
  a global analytic square root of the swept member exists precisely when the
  deck class of the chart roots is trivial: the interface is calibrated exactly
  to the parity obstruction.

The rigidity mechanism: two continuous square-root families of the same
nonvanishing family differ by a continuous `±1`-valued ratio, constant by the
intermediate value theorem.
-/
import GaloisForLFunctions.RHTower.AnnulusRootGluing

noncomputable section

namespace RHTower

open Complex Metric Set

/-! ### §1 The selection interface -/

/-- A sweep selection at a pair of basepoints: one boundary reading per sweep
stage at each basepoint, varying continuously with the stage and squaring at
every stage to the swept member value there.  The interface mentions no charts,
arcs, or chosen roots — only the readings themselves. -/
def SweepSelection (P : Finset ℕ) (pP pM vP vM : ℂ) (F₁ F₂ : ℝ → ℂ) : Prop :=
  Continuous F₁ ∧ Continuous F₂ ∧
    (∀ t, F₁ t ^ 2 = anchorSweep P t pP * vP) ∧
    (∀ t, F₂ t ^ 2 = anchorSweep P t pM * vM)

/-- A family whose square tracks the swept value never vanishes. -/
theorem continuous_root_family_ne_zero {P : Finset ℕ} {z v : ℂ} {g : ℝ → ℂ}
    (hsq : ∀ t, g t ^ 2 = anchorSweep P t z * v) (hv : v ≠ 0) (t : ℝ) :
    g t ≠ 0 := by
  intro h0
  have h : anchorSweep P t z * v = 0 := by rw [← hsq t, h0]; ring
  exact mul_ne_zero (anchorSweep_ne_zero P t z) hv h

/-! ### §2 Rigidity: a continuous root family is the half-angle transport -/

/-- **Sweep rigidity**: a continuous root family along the sweep is the
half-angle transport of its initial value.  The ratio against the explicit
transport is a continuous `±1`-valued function of the stage, hence constant by
the intermediate value theorem: continuity forbids the only other motion, a
sheet jump. -/
theorem continuous_root_family_eq_transport {P : Finset ℕ} {z v : ℂ} {g : ℝ → ℂ}
    (hg : Continuous g) (hsq : ∀ t, g t ^ 2 = anchorSweep P t z * v)
    (hv : v ≠ 0) :
    ∀ t, g t = Complex.exp ((t : ℂ) * anchorLog P z / 2) * g 0 := by
  have hg0 : g 0 ≠ 0 := continuous_root_family_ne_zero hsq hv 0
  set d : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * anchorLog P z / 2) * g 0
  have hd0 : ∀ t, d t ≠ 0 := fun t => mul_ne_zero (Complex.exp_ne_zero _) hg0
  have hd_cont : Continuous d :=
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.mul continuous_const).div_const 2)).mul
      continuous_const
  have hgv : g 0 ^ 2 = v := by
    have := hsq 0
    rwa [anchorSweep_zero, one_mul] at this
  have hdsq : ∀ t, d t ^ 2 = anchorSweep P t z * v := by
    intro t
    show (Complex.exp ((t : ℂ) * anchorLog P z / 2) * g 0) ^ 2
      = anchorSweep P t z * v
    have h2 : Complex.exp ((t : ℂ) * anchorLog P z / 2) ^ 2
        = anchorSweep P t z := by
      rw [← Complex.exp_nat_mul, anchorSweep]
      congr 1
      push_cast
      ring
    rw [mul_pow, h2, hgv]
  set q : ℝ → ℂ := fun t => g t / d t
  have hq_cont : Continuous q := hg.div hd_cont hd0
  have hq_pm : ∀ t, q t = 1 ∨ q t = -1 := by
    intro t
    have hsq1 : q t ^ 2 = 1 := by
      show (g t / d t) ^ 2 = 1
      rw [div_pow, hsq t, hdsq t,
        div_self (mul_ne_zero (anchorSweep_ne_zero P t z) hv)]
    have hfac : (q t - 1) * (q t + 1) = 0 := by linear_combination hsq1
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hd00 : d 0 = g 0 := by
    show Complex.exp (((0 : ℝ) : ℂ) * anchorLog P z / 2) * g 0 = g 0
    rw [Complex.ofReal_zero, zero_mul, zero_div, Complex.exp_zero, one_mul]
  have hq0 : q 0 = 1 := by
    show g 0 / d 0 = 1
    rw [hd00, div_self hg0]
  have hq_one : ∀ t, q t = 1 := by
    intro t
    rcases hq_pm t with h | h
    · exact h
    · exfalso
      have hre_cont : ContinuousOn (fun s => (q s).re) (Set.uIcc 0 t) :=
        (Complex.continuous_re.comp hq_cont).continuousOn
      have hmem : (0 : ℝ) ∈ Set.uIcc (q 0).re (q t).re := by
        rw [hq0, h]
        norm_num [Complex.neg_re, Complex.one_re, Set.mem_uIcc]
      obtain ⟨s, -, hs0⟩ := intermediate_value_uIcc hre_cont hmem
      have hs0' : (q s).re = 0 := hs0
      rcases hq_pm s with h' | h' <;> rw [h'] at hs0' <;> simp at hs0'
  intro t
  exact (div_eq_one_iff_eq (hd0 t)).mp (hq_one t)

/-- Every sweep selection is the half-angle transport of its initial readings:
the initial reading exhausts the rule's freedom. -/
theorem SweepSelection.transport {P : Finset ℕ} {pP pM vP vM : ℂ}
    {F₁ F₂ : ℝ → ℂ} (h : SweepSelection P pP pM vP vM F₁ F₂)
    (hvP : vP ≠ 0) (hvM : vM ≠ 0) (t : ℝ) :
    F₁ t = Complex.exp ((t : ℂ) * anchorLog P pP / 2) * F₁ 0 ∧
      F₂ t = Complex.exp ((t : ℂ) * anchorLog P pM / 2) * F₂ 0 := by
  obtain ⟨hc1, hc2, hsq1, hsq2⟩ := h
  exact ⟨continuous_root_family_eq_transport hc1 hsq1 hvP t,
    continuous_root_family_eq_transport hc2 hsq2 hvM t⟩

/-- The initial readings are square roots of the member values: the fiber of
rules over fixed data is exactly the four sign pairs. -/
theorem SweepSelection.initial_sq {P : Finset ℕ} {pP pM vP vM : ℂ}
    {F₁ F₂ : ℝ → ℂ} (h : SweepSelection P pP pM vP vM F₁ F₂) :
    F₁ 0 ^ 2 = vP ∧ F₂ 0 ^ 2 = vM := by
  obtain ⟨-, -, hsq1, hsq2⟩ := h
  constructor
  · have := hsq1 0
    rwa [anchorSweep_zero, one_mul] at this
  · have := hsq2 0
    rwa [anchorSweep_zero, one_mul] at this

/-- Selection readings never vanish. -/
theorem SweepSelection.ne_zero {P : Finset ℕ} {pP pM vP vM : ℂ}
    {F₁ F₂ : ℝ → ℂ} (h : SweepSelection P pP pM vP vM F₁ F₂)
    (hvP : vP ≠ 0) (hvM : vM ≠ 0) (t : ℝ) :
    F₁ t ≠ 0 ∧ F₂ t ≠ 0 := by
  obtain ⟨-, -, hsq1, hsq2⟩ := h
  exact ⟨continuous_root_family_ne_zero hsq1 hvP t,
    continuous_root_family_ne_zero hsq2 hvM t⟩

/-- Two selections with the same initial readings agree at every stage. -/
theorem SweepSelection.eq_of_initial {P : Finset ℕ} {pP pM vP vM : ℂ}
    {F₁ F₂ F₁' F₂' : ℝ → ℂ}
    (h : SweepSelection P pP pM vP vM F₁ F₂)
    (h' : SweepSelection P pP pM vP vM F₁' F₂')
    (hvP : vP ≠ 0) (hvM : vM ≠ 0)
    (h1 : F₁ 0 = F₁' 0) (h2 : F₂ 0 = F₂' 0) (t : ℝ) :
    F₁ t = F₁' t ∧ F₂ t = F₂' t := by
  obtain ⟨e1, e2⟩ := h.transport hvP hvM t
  obtain ⟨e1', e2'⟩ := h'.transport hvP hvM t
  rw [e1, e1', e2, e2', h1, h2]
  exact ⟨rfl, rfl⟩

/-! ### §3 The displacement identity and reading reversal -/

/-- **The displacement identity**: over the full sweep the relative reading of
any selection is displaced by exactly the exponential of half the
anchor-logarithm difference — the half-angle law leaves the rule no other
motion. -/
theorem SweepSelection.displacement {P : Finset ℕ} {pP pM vP vM : ℂ}
    {F₁ F₂ : ℝ → ℂ} (h : SweepSelection P pP pM vP vM F₁ F₂)
    (hvP : vP ≠ 0) (hvM : vM ≠ 0) :
    F₁ 1 / F₂ 1 / (F₁ 0 / F₂ 0)
      = Complex.exp ((anchorLog P pP - anchorLog P pM) / 2) := by
  obtain ⟨h10, h20⟩ := h.ne_zero hvP hvM 0
  obtain ⟨e1, e2⟩ := h.transport hvP hvM 1
  rw [e1, e2, mul_div_mul_comm, mul_div_cancel_right₀ _ (div_ne_zero h10 h20),
    ← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- The real part of the displacement: a positive scale times the cosine of the
relative sweep holonomy. -/
theorem SweepSelection.displacement_re {P : Finset ℕ} {pP pM vP vM : ℂ}
    {F₁ F₂ : ℝ → ℂ} (h : SweepSelection P pP pM vP vM F₁ F₂)
    (hvP : vP ≠ 0) (hvM : vM ≠ 0) :
    (F₁ 1 / F₂ 1 / (F₁ 0 / F₂ 0)).re
      = Real.exp (((anchorLog P pP).re - (anchorLog P pM).re) / 2)
        * Real.cos ((anchorTilt P pP - anchorTilt P pM) / 2) := by
  have hw0 : anchorLog P pP - anchorLog P pM
      = ((((anchorLog P pP).re - (anchorLog P pM).re : ℝ)) : ℂ)
        + (((anchorTilt P pP - anchorTilt P pM : ℝ)) : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp [← anchorLog_im]
  have hw : (anchorLog P pP - anchorLog P pM) / 2
      = (((((anchorLog P pP).re - (anchorLog P pM).re) / 2 : ℝ)) : ℂ)
        + ((((anchorTilt P pP - anchorTilt P pM) / 2 : ℝ)) : ℂ) * I := by
    rw [hw0]
    push_cast
    ring
  rw [h.displacement hvP hvM, hw, Complex.exp_re]
  simp

/-- **Reading reversal**: when the relative sweep holonomy is within `ε < π/2`
of a half turn, the full sweep drives the relative reading of EVERY selection
strictly into the opposite open half-plane — the only escape, a sheet jump, is
what continuity forbids. -/
theorem SweepSelection.reading_reversal {P : Finset ℕ} {pP pM vP vM : ℂ}
    {F₁ F₂ : ℝ → ℂ} {ε : ℝ}
    (h : SweepSelection P pP pM vP vM F₁ F₂) (hvP : vP ≠ 0) (hvM : vM ≠ 0)
    (hε : ε < Real.pi / 2)
    (hhalf : |(anchorTilt P pP - anchorTilt P pM) / 2 - Real.pi| ≤ ε) :
    (F₁ 1 / F₂ 1 / (F₁ 0 / F₂ 0)).re < 0 := by
  rw [h.displacement_re hvP hvM]
  rw [abs_le] at hhalf
  refine mul_neg_of_pos_of_neg (Real.exp_pos _) ?_
  refine Real.cos_neg_of_pi_div_two_lt_of_lt ?_ ?_
  · linarith [hhalf.1]
  · linarith [hhalf.2]

/-- **The steering defeats every rule at once**: beyond any bound there is a
prime set for which EVERY sweep selection at the conjugate basepoints suffers
strict reading reversal — one anchor refutes all continuous root rules
simultaneously, whatever their member values and initial signs. -/
theorem selection_reversal_steerable {ρ : ℂ} {c : ℝ}
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (hcap : (ρ.im + c) * (4 * Real.log 2) < Real.pi) (Q : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      ∀ vP vM : ℂ, vP ≠ 0 → vM ≠ 0 → ∀ F₁ F₂ : ℝ → ℂ,
        SweepSelection P (ρ + (c : ℂ) * I) (ρ - (c : ℂ) * I) vP vM F₁ F₂ →
          (F₁ 1 / F₂ 1 / (F₁ 0 / F₂ 0)).re < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨P, hP, hhalf⟩ := exists_near_half_turn_relative_holonomy hre0 hre1
    hc hcτ hnarrow hcap (ε := Real.pi / 4) (by linarith) Q
  exact ⟨P, hP, fun vP vM hvP hvM F₁ F₂ hF =>
    hF.reading_reversal hvP hvM (by linarith) hhalf⟩

/-! ### §4 The anchor-free side: every rule is frozen -/

/-- **The anchor-free rule is frozen**: over the empty anchor every sweep
selection is constant in the stage and its relative displacement is identically
`1` — the reversal mechanism has nothing to act on.  A functional equation
without an Euler product supports rules, but only motionless ones. -/
theorem SweepSelection.frozen_of_empty {pP pM vP vM : ℂ} {F₁ F₂ : ℝ → ℂ}
    (h : SweepSelection ∅ pP pM vP vM F₁ F₂) (hvP : vP ≠ 0) (hvM : vM ≠ 0) :
    (∀ t, F₁ t = F₁ 0 ∧ F₂ t = F₂ 0) ∧
      ∀ t u : ℝ, F₁ t / F₂ t / (F₁ u / F₂ u) = 1 := by
  have hconst : ∀ t, F₁ t = F₁ 0 ∧ F₂ t = F₂ 0 := by
    intro t
    obtain ⟨e1, e2⟩ := h.transport hvP hvM t
    rw [e1, e2, anchorLog_empty, anchorLog_empty]
    constructor <;> simp
  obtain ⟨h10, h20⟩ := h.ne_zero hvP hvM 0
  refine ⟨hconst, fun t u => ?_⟩
  rw [(hconst t).1, (hconst t).2, (hconst u).1, (hconst u).2,
    div_self (div_ne_zero h10 h20)]

/-- Sweep selections exist over the empty anchor: constant readings from any
fixed square roots.  With `SweepSelection.frozen_of_empty` this is the
anchor-free side of the discriminator: rules exist, and all of them are
frozen. -/
theorem exists_sweepSelection_empty (pP pM : ℂ) {vP vM : ℂ}
    (hvP : vP ≠ 0) (hvM : vM ≠ 0) :
    ∃ F₁ F₂ : ℝ → ℂ, SweepSelection ∅ pP pM vP vM F₁ F₂ := by
  refine ⟨fun _ => Complex.exp (Complex.log vP / 2),
    fun _ => Complex.exp (Complex.log vM / 2), continuous_const, continuous_const,
    fun t => ?_, fun t => ?_⟩
  · rw [anchorSweep_empty, one_mul, ← Complex.exp_nat_mul,
      show ((2 : ℕ) : ℂ) * (Complex.log vP / 2) = Complex.log vP by
        push_cast; ring]
    exact Complex.exp_log hvP
  · rw [anchorSweep_empty, one_mul, ← Complex.exp_nat_mul,
      show ((2 : ℕ) : ℂ) * (Complex.log vM / 2) = Complex.log vM by
        push_cast; ring]
    exact Complex.exp_log hvM

/-! ### §5 The geometric calibration: selections against the deck class -/

/-- On the symmetric member the endpoint readings of any selection square to the
anchored member: the abstract interface lands on the anchored symmetric member
at full sweep. -/
theorem SweepSelection.endpoint_sq_anchoredSEM {P : Finset ℕ}
    (hP : ∀ p ∈ P, 2 ≤ p) {N : ℕ} {pP pM : ℂ}
    (hreP : 0 < pP.re) (hreM : 0 < pM.re) {F₁ F₂ : ℝ → ℂ}
    (h : SweepSelection P pP pM (completedSEM N pP) (completedSEM N pM) F₁ F₂) :
    F₁ 1 ^ 2 = anchoredSEM P N pP ∧ F₂ 1 ^ 2 = anchoredSEM P N pM := by
  obtain ⟨-, -, hsq1, hsq2⟩ := h
  constructor
  · rw [hsq1 1, anchorSweep_one hP hreP]
    rfl
  · rw [hsq2 1, anchorSweep_one hP hreM]
    rfl

/-- **The calibration**: on the slit-chart annulus, a sweep selection whose
readings extend at every stage to a global analytic square root of the swept
member exists precisely when the deck class of the chart roots is trivial.  The
interface is calibrated exactly to the parity obstruction. -/
theorem exists_extending_sweepSelection_iff_deckClass_one {P : Finset ℕ}
    (hP : ∀ p ∈ P, 2 ≤ p) {f G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hre : ∀ z ∈ ball a R \ closedBall a r₀, 0 < z.re)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 = f z)
    (hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0) :
    (∃ F₁ F₂ : ℝ → ℂ,
      SweepSelection P (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I))
        (f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)) F₁ F₂ ∧
      ∀ t : ℝ, ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball a R \ closedBall a r₀) ∧
        (∀ z ∈ ball a R \ closedBall a r₀, G z ^ 2 = anchorSweep P t z * f z) ∧
        G (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) = F₁ t ∧
        G (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = F₂ t)
      ↔ deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = 1 := by
  constructor
  · rintro ⟨F₁, F₂, -, hExt⟩
    obtain ⟨G, hGan, hGsq, -, -⟩ := hExt 0
    have hGf : ∀ z ∈ ball a R \ closedBall a r₀, G z ^ 2 = f z := fun z hz => by
      rw [hGsq z hz, anchorSweep_zero, one_mul]
    exact deckClass_eq_one_of_global_sqrt h0 hrR hG₁ hG₂ hpG₁ hpG₂ hGan hGf
      hfP hfM
  · intro hdeck
    obtain ⟨G₀, hG₀an, hpG₀⟩ := exists_global_sqrt_of_deckClass_one h0 hrR
      hG₁ hG₂ hpG₁ hpG₂ hfP hfM hdeck
    obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem h0 hrR
    refine ⟨fun t => sweepRoot P t G₀ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I),
      fun t => sweepRoot P t G₀ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I),
      ⟨?_, ?_, fun t => sweepRoot_sq hpG₀ P t _ hPmem.1.2,
        fun t => sweepRoot_sq hpG₀ P t _ hMmem.1.2⟩,
      fun t => ⟨sweepRoot P t G₀,
        sweepRoot_analyticOnNhd hP t hG₀an hre,
        sweepRoot_sq hpG₀ P t, rfl, rfl⟩⟩
    · exact (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.mul continuous_const).div_const 2)).mul
        continuous_const
    · exact (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.mul continuous_const).div_const 2)).mul
        continuous_const

/-- **The selection principle, static form**: a nontrivial deck class refutes
every sweep selection whose readings are realized by a global root at each
stage — the interface plus an odd hole parity is contradictory. -/
theorem no_extending_sweepSelection_of_deckClass_ne_one {P : Finset ℕ}
    (hP : ∀ p ∈ P, 2 ≤ p) {f G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hre : ∀ z ∈ ball a R \ closedBall a r₀, 0 < z.re)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 = f z)
    (hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hdeck : deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 1) :
    ¬(∃ F₁ F₂ : ℝ → ℂ,
      SweepSelection P (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I))
        (f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)) F₁ F₂ ∧
      ∀ t : ℝ, ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball a R \ closedBall a r₀) ∧
        (∀ z ∈ ball a R \ closedBall a r₀, G z ^ 2 = anchorSweep P t z * f z) ∧
        G (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) = F₁ t ∧
        G (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = F₂ t) := fun hsel =>
  hdeck ((exists_extending_sweepSelection_iff_deckClass_one hP h0 hrR hre
    hG₁ hG₂ hpG₁ hpG₂ hfP hfM).mp hsel)

/-! ### §6 The weld: steering and parity refuse the same rule -/

/-- **The weld**: at conjugate basepoints admissible for steering, with chart
roots of nontrivial deck class, one prime set beyond any bound simultaneously
(i) drives every sweep selection into strict reading reversal and (ii) admits
no stage at which any reading is realized by a global root on the annulus.  A
rule tying the steered boundary readings to the branch the geometry selects can
neither hold its readings nor come from the geometry. -/
theorem selection_principle_weld {ρ : ℂ} {r₀ R : ℝ}
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hcτ : (r₀ + R) / 2 < ρ.im)
    (hnarrow : 9 * (2 * ((r₀ + R) / 2)) ≤ ρ.im + (r₀ + R) / 2)
    (hcap : (ρ.im + (r₀ + R) / 2) * (4 * Real.log 2) < Real.pi)
    (hre : ∀ z ∈ ball ρ R \ closedBall ρ r₀, 0 < z.re)
    {f G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA ρ r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA ρ r₀ R))
    (hpG₁ : ∀ z ∈ chartRA ρ r₀ R, G₁ z ^ 2 = f z)
    (hpG₂ : ∀ z ∈ chartLA ρ r₀ R, G₂ z ^ 2 = f z)
    (hfP : f (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hdeck : deckClass G₁ G₂ (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 1) (Q : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      (∀ vP vM : ℂ, vP ≠ 0 → vM ≠ 0 → ∀ F₁ F₂ : ℝ → ℂ,
        SweepSelection P (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) vP vM F₁ F₂ →
          (F₁ 1 / F₂ 1 / (F₁ 0 / F₂ 0)).re < 0) ∧
      ∀ t : ℝ, ¬∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball ρ R \ closedBall ρ r₀) ∧
        ∀ z ∈ ball ρ R \ closedBall ρ r₀,
          G z ^ 2 = anchorSweep P t z * f z := by
  have hc : 0 < (r₀ + R) / 2 := by linarith
  obtain ⟨P, hP, hrev⟩ := selection_reversal_steerable hre0 hre1 hc hcτ
    hnarrow hcap Q
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp => (hP p hp).1.two_le
  exact ⟨P, hP, hrev, fun t =>
    no_global_sqrt_along_sweep_of_deckClass_ne_one hP2 h0 hrR hre hG₁ hG₂
      hpG₁ hpG₂ hfP hfM hdeck t⟩

/-! ### §7 The neutral stage: the tie the rule cannot break -/

/-- The stage-`t` displacement identity: at every stage the relative reading is
displaced from its initial position by the half-angle exponential of that
stage — the whole displacement path of any selection is the same explicit
one-parameter curve. -/
theorem SweepSelection.displacement_at {P : Finset ℕ} {pP pM vP vM : ℂ}
    {F₁ F₂ : ℝ → ℂ} (h : SweepSelection P pP pM vP vM F₁ F₂)
    (hvP : vP ≠ 0) (hvM : vM ≠ 0) (t : ℝ) :
    F₁ t / F₂ t / (F₁ 0 / F₂ 0)
      = Complex.exp ((t : ℂ) * (anchorLog P pP - anchorLog P pM) / 2) := by
  obtain ⟨h10, h20⟩ := h.ne_zero hvP hvM 0
  obtain ⟨e1, e2⟩ := h.transport hvP hvM t
  rw [e1, e2, mul_div_mul_comm, mul_div_cancel_right₀ _ (div_ne_zero h10 h20),
    ← Complex.exp_sub]
  congr 1
  ring

/-- The real part of the stage-`t` displacement: the reading's half-plane
position is an explicit cosine of the stage times the relative tilt. -/
theorem SweepSelection.displacement_re_at {P : Finset ℕ} {pP pM vP vM : ℂ}
    {F₁ F₂ : ℝ → ℂ} (h : SweepSelection P pP pM vP vM F₁ F₂)
    (hvP : vP ≠ 0) (hvM : vM ≠ 0) (t : ℝ) :
    (F₁ t / F₂ t / (F₁ 0 / F₂ 0)).re
      = Real.exp (t * ((anchorLog P pP).re - (anchorLog P pM).re) / 2)
        * Real.cos (t * (anchorTilt P pP - anchorTilt P pM) / 2) := by
  have hw0 : anchorLog P pP - anchorLog P pM
      = ((((anchorLog P pP).re - (anchorLog P pM).re : ℝ)) : ℂ)
        + (((anchorTilt P pP - anchorTilt P pM : ℝ)) : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp [← anchorLog_im]
  have hw : (t : ℂ) * (anchorLog P pP - anchorLog P pM) / 2
      = (((t * ((anchorLog P pP).re - (anchorLog P pM).re) / 2 : ℝ)) : ℂ)
        + (((t * (anchorTilt P pP - anchorTilt P pM) / 2 : ℝ)) : ℂ) * I := by
    rw [hw0]
    push_cast
    ring
  rw [h.displacement_at hvP hvM t, hw, Complex.exp_re]
  simp

/-- **The neutral stage**: under near-half-turn holonomy a selection starts at
displacement `1` and ends reversed, so the intermediate value theorem forces a
stage at which the relative reading is purely imaginary and nonzero — the two
branches are exactly equidistant, and the tie can only be broken by the sheet
jump that continuity forbids. -/
theorem SweepSelection.exists_neutral_stage {P : Finset ℕ} {pP pM vP vM : ℂ}
    {F₁ F₂ : ℝ → ℂ} {ε : ℝ}
    (h : SweepSelection P pP pM vP vM F₁ F₂) (hvP : vP ≠ 0) (hvM : vM ≠ 0)
    (hε : ε < Real.pi / 2)
    (hhalf : |(anchorTilt P pP - anchorTilt P pM) / 2 - Real.pi| ≤ ε) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      (F₁ t / F₂ t / (F₁ 0 / F₂ 0)).re = 0 ∧
        F₁ t / F₂ t / (F₁ 0 / F₂ 0) ≠ 0 := by
  have hrev := h.reading_reversal hvP hvM hε hhalf
  have hne := h.ne_zero hvP hvM
  have hdisp := h.displacement_at hvP hvM
  obtain ⟨hc1, hc2, -, -⟩ := h
  have h2ne : ∀ u, F₂ u ≠ 0 := fun u => (hne u).2
  have hφcont : ContinuousOn (fun u => (F₁ u / F₂ u / (F₁ 0 / F₂ 0)).re)
      (Set.uIcc (0 : ℝ) 1) :=
    (Complex.continuous_re.comp
      ((hc1.div hc2 h2ne).div_const (F₁ 0 / F₂ 0))).continuousOn
  have hφ0 : (F₁ 0 / F₂ 0 / (F₁ 0 / F₂ 0)).re = 1 := by
    rw [div_self (div_ne_zero (hne 0).1 (hne 0).2)]
    exact Complex.one_re
  have hmem : (0 : ℝ) ∈ Set.uIcc ((F₁ 0 / F₂ 0 / (F₁ 0 / F₂ 0)).re)
      ((F₁ 1 / F₂ 1 / (F₁ 0 / F₂ 0)).re) := by
    rw [Set.mem_uIcc]
    right
    refine ⟨le_of_lt hrev, ?_⟩
    rw [hφ0]
    norm_num
  obtain ⟨t, ht, hφt⟩ := intermediate_value_uIcc hφcont hmem
  refine ⟨t, ?_, hφt, ?_⟩
  · rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  · rw [hdisp t]
    exact Complex.exp_ne_zero _

/-! ### §8 Cross-anchor compatibility is free -/

/-- **Endpoint compatibility is free**: given any fixed square roots of two port
values, EVERY finite anchor admits a sweep selection — for the member values
with that anchor's head divided out — whose full-sweep readings are exactly the
chosen roots.  A family of selections over all finite anchors sharing one
endpoint reading pair therefore always exists: the discriminating content of
the selection principle lies in per-anchor geometric realization (the deck
class, unchanged by dividing out any anchor), never in cross-anchor
compatibility of the readings. -/
theorem exists_sweepSelection_with_endpoint {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {pP pM : ℂ} (hreP : 0 < pP.re) (hreM : 0 < pM.re)
    {W₁ W₂ w₁ w₂ : ℂ} (hw₁ : w₁ ^ 2 = W₁) (hw₂ : w₂ ^ 2 = W₂) :
    ∃ F₁ F₂ : ℝ → ℂ,
      SweepSelection P pP pM (W₁ / eulerHeadAnchor P pP)
        (W₂ / eulerHeadAnchor P pM) F₁ F₂ ∧ F₁ 1 = w₁ ∧ F₂ 1 = w₂ := by
  refine ⟨fun t => Complex.exp (((t - 1 : ℝ) : ℂ) * anchorLog P pP / 2) * w₁,
    fun t => Complex.exp (((t - 1 : ℝ) : ℂ) * anchorLog P pM / 2) * w₂,
    ⟨?_, ?_, fun t => ?_, fun t => ?_⟩, ?_, ?_⟩
  · exact (Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).mul
        continuous_const).div_const 2)).mul continuous_const
  · exact (Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).mul
        continuous_const).div_const 2)).mul continuous_const
  · rw [mul_pow, ← Complex.exp_nat_mul, hw₁, anchorSweep,
      ← exp_anchorLog hP hreP,
      show ((2 : ℕ) : ℂ) * (((t - 1 : ℝ) : ℂ) * anchorLog P pP / 2)
        = (t : ℂ) * anchorLog P pP - anchorLog P pP by push_cast; ring,
      Complex.exp_sub, div_mul_eq_mul_div, mul_div_assoc]
  · rw [mul_pow, ← Complex.exp_nat_mul, hw₂, anchorSweep,
      ← exp_anchorLog hP hreM,
      show ((2 : ℕ) : ℂ) * (((t - 1 : ℝ) : ℂ) * anchorLog P pM / 2)
        = (t : ℂ) * anchorLog P pM - anchorLog P pM by push_cast; ring,
      Complex.exp_sub, div_mul_eq_mul_div, mul_div_assoc]
  · simp
  · simp

end RHTower
