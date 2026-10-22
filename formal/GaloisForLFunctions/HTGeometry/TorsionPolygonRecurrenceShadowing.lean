import GaloisForLFunctions.HTGeometry.ProjectiveTorsionPhaseQuotient
import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity
import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleFiniteCoherence
import GaloisForLFunctions.HTGeometry.TemporalDimensionInteractionMultiplicationLaw

/-!
# Every hard torsion polygon is shadowed by arbitrarily late recurrences

An autonomous uniform-phase trajectory whose anchored energy gaps are rationally independent passes
arbitrarily late through every prescribed torsion phase class, and it does so quantitatively: a
Kronecker time places the phase vector near the class, and a Dirichlet return time of arbitrary size
translates that placement forward without losing accuracy.

Because the flow phase at time `j t` is the `j`-th power of the phase at time `t`, one such
placement controls the whole polygon at once: at every one of the `k-1` interior slices the state is
within `j` times the placement error of the corresponding torsion vertex, and at the endpoint `k t`
it is within `k` times that error of the initial state.  Feeding a hard torsion class into this
estimate converts the static avoidance of a target dictionary into a dynamical one, with the strict
inequalities preserved by the margin that finiteness of the dictionary supplies.
-/

open Real RHTower

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Elementary

/-- The pure-state trace distance is bounded by the norm distance. -/
theorem pureStateTraceDistance_le_norm_sub {ι : Type*} [Fintype ι] (u v : EuclideanSpace ℂ ι)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    pureStateTraceDistance u v ≤ ‖u - v‖ := by
  have hns := norm_sub_sq (𝕜 := ℂ) u v
  rw [hu, hv] at hns
  have hre : RCLike.re (inner ℂ u v : ℂ) ≤ ‖(inner ℂ u v : ℂ)‖ := RCLike.re_le_norm _
  have hkey : 1 - ‖(inner ℂ u v : ℂ)‖ ^ (2 : ℕ) ≤ ‖u - v‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (‖(inner ℂ u v : ℂ)‖ - 1)]
  rw [pureStateTraceDistance]
  calc Real.sqrt (1 - ‖(inner ℂ u v : ℂ)‖ ^ (2 : ℕ)) ≤ Real.sqrt (‖u - v‖ ^ (2 : ℕ)) := Real.sqrt_le_sqrt hkey
    _ = ‖u - v‖ := Real.sqrt_sq (norm_nonneg _)

/-- A uniform coordinate bound bounds the distance between the corresponding rays. -/
theorem norm_phaseRay_sub_le {D : ℕ} (q r : Fin D → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a, ‖q a - r a‖ ≤ ε) : ‖phaseRay q - phaseRay r‖ ≤ ε := by
  rw [phaseRay_sub, EuclideanSpace.norm_eq]
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Real.sqrt_zero]
    exact hε
  · have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have hterm : ∀ a : Fin D, ‖(phaseRay (fun a => q a - r a)).ofLp a‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) / (D : ℝ) := by
      intro a
      show ‖((Real.sqrt (D : ℝ))⁻¹ : ℂ) * (q a - r a)‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) / (D : ℝ)
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        mul_pow, inv_pow, Real.sq_sqrt hDR.le, div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [norm_nonneg (q a - r a), h a]
    have hsum : ∑ _a : Fin D, ε ^ (2 : ℕ) / (D : ℝ) = ε ^ (2 : ℕ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    calc Real.sqrt (∑ a, ‖(phaseRay (fun a => q a - r a)).ofLp a‖ ^ (2 : ℕ))
        ≤ Real.sqrt (∑ _a : Fin D, ε ^ (2 : ℕ) / (D : ℝ)) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun a _ => hterm a)
      _ = ε := by rw [hsum, Real.sqrt_sq hε]

/-- Two unimodular phases differ by at most the difference of their arguments. -/
theorem norm_exp_ofReal_mul_I_sub_le (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x - y| := by
  have hsq := norm_expChar_sub_sq x y
  have hcos : 1 - (x - y) ^ (2 : ℕ) / 2 ≤ Real.cos (x - y) := Real.one_sub_sq_div_two_le_cos
  have hn : (0 : ℝ) ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ :=
    norm_nonneg _
  have h2 : ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ^ (2 : ℕ)
      ≤ |x - y| ^ (2 : ℕ) := by
    rw [hsq, sq_abs]
    linarith
  nlinarith [abs_nonneg (x - y)]

/-- Conjugating both arguments does not change the distance between two unimodular phases. -/
theorem norm_exp_neg_ofReal_mul_I_sub (x y : ℝ) :
    ‖Complex.exp (((-x : ℝ) : ℂ) * Complex.I) - Complex.exp (((-y : ℝ) : ℂ) * Complex.I)‖
      = ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ := by
  have hconj : ∀ z : ℝ, Complex.exp (((-z : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) (Complex.exp ((z : ℂ) * Complex.I)) := by
    intro z
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  rw [hconj x, hconj y, ← map_sub, RCLike.norm_conj]

/-- Powers of unimodular numbers separate at most linearly. -/
theorem norm_pow_sub_pow_le_of_unit {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (j : ℕ) :
    ‖z ^ j - w ^ j‖ ≤ (j : ℝ) * ‖z - w‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : z ^ (j + 1) - w ^ (j + 1) = z * (z ^ j - w ^ j) + (z - w) * w ^ j := by ring
      have h1 : ‖z‖ * ‖z ^ j - w ^ j‖ ≤ 1 * ((j : ℝ) * ‖z - w‖) :=
        mul_le_mul hz ih (norm_nonneg _) zero_le_one
      have h2 : ‖z - w‖ * ‖w‖ ^ j ≤ ‖z - w‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hw) (norm_nonneg _)
      calc ‖z ^ (j + 1) - w ^ (j + 1)‖
          ≤ ‖z * (z ^ j - w ^ j)‖ + ‖(z - w) * w ^ j‖ := by rw [hstep]; exact norm_add_le _ _
        _ = ‖z‖ * ‖z ^ j - w ^ j‖ + ‖z - w‖ * ‖w‖ ^ j := by rw [norm_mul, norm_mul, norm_pow]
        _ ≤ 1 * ((j : ℝ) * ‖z - w‖) + ‖z - w‖ * 1 := by linarith
        _ = ((j : ℝ) + 1) * ‖z - w‖ := by ring
        _ = ((j + 1 : ℕ) : ℝ) * ‖z - w‖ := by push_cast; ring

/-- A strict inequality over a finite index set has a uniform margin. -/
theorem exists_margin_of_lt {β : Type*} (s : Finset β) (g : β → ℝ) {δ : ℝ}
    (h : ∀ b ∈ s, δ < g b) : ∃ σ : ℝ, 0 < σ ∧ ∀ b ∈ s, δ + σ ≤ g b := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨b₀, hb₀, hmin⟩ := Finset.exists_min_image s g hs
    refine ⟨g b₀ - δ, by linarith [h b₀ hb₀], fun b hb => ?_⟩
    have := hmin b hb
    linarith

end Elementary

section Flow

variable {d k : ℕ}

/-- The unimodular phase vector of the autonomous trajectory `(17)`. -/
def flowPhaseVec {D : ℕ} (E : Fin D → ℝ) (t : ℝ) : Fin D → ℂ :=
  fun a => Complex.exp (((-(t * E a) : ℝ) : ℂ) * Complex.I)

/-- **`(17)`.**  The autonomous uniform-phase trajectory, as a ray. -/
def flowRay {D : ℕ} (E : Fin D → ℝ) (t : ℝ) : EuclideanSpace ℂ (Fin D) :=
  phaseRay (flowPhaseVec E t)

@[simp] theorem norm_flowPhaseVec {D : ℕ} (E : Fin D → ℝ) (t : ℝ) (a : Fin D) :
    ‖flowPhaseVec E t a‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem norm_flowRay {D : ℕ} (E : Fin D → ℝ) (t : ℝ) (hD : 0 < D) : ‖flowRay E t‖ = 1 :=
  norm_phaseRay (fun a => norm_flowPhaseVec E t a) hD

/-- The trajectory anchored at the first energy. -/
def anchoredFlowVec (E : Fin (d + 1) → ℝ) (t : ℝ) : Fin (d + 1) → ℂ :=
  fun a => Complex.exp (((-(t * (E a - E 0)) : ℝ) : ℂ) * Complex.I)

theorem norm_anchoredFlowVec (E : Fin (d + 1) → ℝ) (t : ℝ) (a : Fin (d + 1)) :
    ‖anchoredFlowVec E t a‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- The global phase of the trajectory is invisible to the trace distance. -/
theorem pureStateTraceDistance_flowRay_eq (E : Fin (d + 1) → ℝ) (t : ℝ)
    (y : EuclideanSpace ℂ (Fin (d + 1))) :
    pureStateTraceDistance (flowRay E t) y
      = pureStateTraceDistance (phaseRay (anchoredFlowVec E t)) y := by
  have hfac : flowPhaseVec E t
      = fun a => Complex.exp (((-(t * E 0) : ℝ) : ℂ) * Complex.I) * anchoredFlowVec E t a := by
    funext a
    show Complex.exp (((-(t * E a) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((-(t * E 0) : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((-(t * (E a - E 0)) : ℝ) : ℂ) * Complex.I)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [flowRay, hfac, phaseRay_const_mul]
  exact _root_.HTGeometry.pureStateTraceDistance_smul_left _
    (Complex.norm_exp_ofReal_mul_I _) _ _

/-- The trajectory starts at the anchored zero class. -/
theorem cons_zero_zero_zmod (k d : ℕ) :
    (Fin.cons (0 : ZMod k) (0 : Fin d → ZMod k) : Fin (d + 1) → ZMod k) = 0 := by
  funext a
  refine Fin.cases ?_ ?_ a
  · rw [Fin.cons_zero]
    rfl
  · intro j
    rw [Fin.cons_succ]
    rfl

theorem flowRay_zero [NeZero k] (E : Fin (d + 1) → ℝ) :
    flowRay E 0 = anchoredRay k (0 : Fin d → ZMod k) := by
  have hvec : flowPhaseVec E 0 = torsionPhaseVec k (0 : Fin (d + 1) → ZMod k) := by
    funext a
    show Complex.exp (((-(0 * E a) : ℝ) : ℂ) * Complex.I)
        = (ZMod.toCircle ((0 : Fin (d + 1) → ZMod k) a) : ℂ)
    rw [show ((0 : Fin (d + 1) → ZMod k) a) = 0 from rfl, AddChar.map_zero_eq_one]
    norm_num
  rw [flowRay, anchoredRay, torsionRay, cons_zero_zero_zmod, hvec]

/-- The flow phase at time `t` sits within `ε` of the torsion class `n`. -/
def ShadowsTorsion (E : Fin (d + 1) → ℝ) (k : ℕ) [NeZero k] (n : Fin d → ZMod k)
    (t ε : ℝ) : Prop :=
  ∀ j : Fin d, ‖Complex.exp (((-(t * projectiveGapPacket E j) : ℝ) : ℂ) * Complex.I)
      - (ZMod.toCircle (n j) : ℂ)‖ ≤ ε

theorem shadowsTorsion_iff [NeZero k] (E : Fin (d + 1) → ℝ) (n : Fin d → ZMod k) (t ε : ℝ) :
    ShadowsTorsion E k n t ε ↔ ∀ j : Fin d,
      ‖Complex.exp (((-(t * projectiveGapPacket E j) : ℝ) : ℂ) * Complex.I)
        - (ZMod.toCircle (n j) : ℂ)‖ ≤ ε := Iff.rfl

/-- **The polygon estimate.**  Shadowing propagates to every power, with a linear loss. -/
theorem shadowsTorsion_nsmul [NeZero k] {E : Fin (d + 1) → ℝ} {n : Fin d → ZMod k} {t ε : ℝ}
    (h : ShadowsTorsion E k n t ε) (j : ℕ) :
    ShadowsTorsion E k (j • n) ((j : ℝ) * t) ((j : ℝ) * ε) := by
  refine (shadowsTorsion_iff _ _ _ _).mpr fun a => ?_
  have hz : Complex.exp (((-(((j : ℝ) * t) * projectiveGapPacket E a) : ℝ) : ℂ) * Complex.I)
      = (Complex.exp (((-(t * projectiveGapPacket E a) : ℝ) : ℂ) * Complex.I)) ^ j := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hw : (ZMod.toCircle ((j • n) a) : ℂ) = ((ZMod.toCircle (n a) : ℂ)) ^ j := by
    show (ZMod.toCircle (j • n a) : ℂ) = _
    rw [AddChar.map_nsmul_eq_pow, Circle.coe_pow]
  rw [hz, hw]
  refine le_trans (norm_pow_sub_pow_le_of_unit (le_of_eq (Complex.norm_exp_ofReal_mul_I _))
    (le_of_eq (Circle.norm_coe _)) j) ?_
  exact mul_le_mul_of_nonneg_left (h a) (Nat.cast_nonneg j)

/-- **The shadowing estimate.**  A shadowed time is trace-close to the anchored torsion ray. -/
theorem pureStateTraceDistance_flowRay_anchoredRay_le [NeZero k] (E : Fin (d + 1) → ℝ)
    (n : Fin d → ZMod k) {t ε : ℝ} (hε : 0 ≤ ε) (h : ShadowsTorsion E k n t ε) :
    pureStateTraceDistance (flowRay E t) (anchoredRay k n) ≤ ε := by
  rw [pureStateTraceDistance_flowRay_eq]
  refine le_trans (pureStateTraceDistance_le_norm_sub _ _
    (norm_phaseRay (fun a => norm_anchoredFlowVec E t a) (Nat.succ_pos d))
    (norm_anchoredRay n)) ?_
  rw [anchoredRay, torsionRay]
  refine norm_phaseRay_sub_le _ _ hε ?_
  intro a
  refine Fin.cases ?_ ?_ a
  · show ‖Complex.exp (((-(t * (E 0 - E 0)) : ℝ) : ℂ) * Complex.I)
        - (ZMod.toCircle ((Fin.cons (0 : ZMod k) n : Fin (d + 1) → ZMod k) 0) : ℂ)‖ ≤ ε
    rw [Fin.cons_zero, AddChar.map_zero_eq_one, sub_self, mul_zero, neg_zero]
    norm_num
    exact hε
  · intro j
    show ‖Complex.exp (((-(t * (E j.succ - E 0)) : ℝ) : ℂ) * Complex.I)
        - (ZMod.toCircle ((Fin.cons (0 : ZMod k) n : Fin (d + 1) → ZMod k) j.succ) : ℂ)‖ ≤ ε
    rw [Fin.cons_succ]
    exact h j

end Flow

section LateShadowing

variable {d k : ℕ}

/-- The angle a torsion class prescribes for the anchored flow. -/
def torsionAngle (k : ℕ) [NeZero k] {d : ℕ} (n : Fin d → ZMod k) : Fin d → ℝ :=
  fun j => -(2 * π * (((n j).val : ℕ) : ℝ) / (k : ℝ))

theorem exp_neg_torsionAngle [NeZero k] (n : Fin d → ZMod k) (j : Fin d) :
    Complex.exp (((-(torsionAngle k n j) : ℝ) : ℂ) * Complex.I) = (ZMod.toCircle (n j) : ℂ) := by
  rw [ZMod.toCircle_apply, torsionAngle]
  congr 1
  push_cast
  ring

/-- **Kronecker plus Dirichlet.**  A rationally independent gap family lets the trajectory shadow
any prescribed torsion class at arbitrarily late times. -/
theorem exists_late_shadowing [NeZero k] (E : Fin (d + 1) → ℝ)
    (hind : LinearIndependent ℚ (projectiveGapPacket E)) (n : Fin d → ZMod k) {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∃ t : ℝ, A < t ∧ ShadowsTorsion E k n t ε := by
  classical
  obtain ⟨t₀, ht₀⟩ := kronecker_approx hind (torsionAngle k n) (half_pos hε)
  set Q : ℕ := max 1 ⌈max (4 * π / ε) (A - t₀ + 1)⌉₊ with hQdef
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
  have hQceil : (max (4 * π / ε) (A - t₀ + 1) : ℝ) ≤ (Q : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast Nat.le_max_right 1 ⌈max (4 * π / ε) (A - t₀ + 1)⌉₊
  have hQ1 : 4 * π / ε ≤ (Q : ℝ) := le_trans (le_max_left _ _) hQceil
  have hQ2 : A - t₀ + 1 ≤ (Q : ℝ) := le_trans (le_max_right _ _) hQceil
  have h4 : 4 * π ≤ (Q : ℝ) * ε := by
    rw [div_le_iff₀ hε] at hQ1
    linarith
  have hQeps : 2 * π / (Q : ℝ) ≤ ε / 2 := by
    rw [div_le_div_iff₀ hQR (by norm_num : (0 : ℝ) < 2)]
    linarith
  obtain ⟨m, hmQ, -, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_annular_quantitative hQpos (projectiveGapPacket E)
  have hmR : (Q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmQ
  refine ⟨t₀ + (m : ℝ), by linarith, ?_⟩
  refine (shadowsTorsion_iff _ _ _ _).mpr fun j => ?_
  -- the approximate return time
  have hunit : Complex.exp (((2 * π * ((r j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((2 * π * ((r j : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I
        = ((r j : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (r j)
  have hshift : Complex.exp ((((m : ℝ) * projectiveGapPacket E j : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((((m : ℝ) * projectiveGapPacket E j - 2 * π * ((r j : ℤ) : ℝ)) : ℝ) : ℂ)
          * Complex.I) := by
    calc Complex.exp ((((m : ℝ) * projectiveGapPacket E j : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((((m : ℝ) * projectiveGapPacket E j - 2 * π * ((r j : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((2 * π * ((r j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
      _ = _ := by rw [hunit, mul_one]
  have hret : ‖Complex.exp ((((m : ℝ) * projectiveGapPacket E j : ℝ) : ℂ) * Complex.I) - 1‖ ≤ ε / 2 := by
    have h1 := norm_exp_ofReal_mul_I_sub_le
      ((m : ℝ) * projectiveGapPacket E j - 2 * π * ((r j : ℤ) : ℝ)) 0
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
    rw [hshift]
    refine le_trans h1 ?_
    rw [sub_zero]
    exact le_trans (hr j) hQeps
  -- the Kronecker placement
  have hkron : ‖Complex.exp (((projectiveGapPacket E j * t₀ : ℝ) : ℂ) * Complex.I)
      - Complex.exp (((torsionAngle k n j : ℝ) : ℂ) * Complex.I)‖ ≤ ε / 2 := le_of_lt (ht₀ j)
  -- the translated placement
  have hfac : Complex.exp ((((t₀ + (m : ℝ)) * projectiveGapPacket E j : ℝ) : ℂ) * Complex.I)
      - Complex.exp (((projectiveGapPacket E j * t₀ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((projectiveGapPacket E j * t₀ : ℝ) : ℂ) * Complex.I)
        * (Complex.exp ((((m : ℝ) * projectiveGapPacket E j : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hsplit : ‖Complex.exp ((((t₀ + (m : ℝ)) * projectiveGapPacket E j : ℝ) : ℂ) * Complex.I)
      - Complex.exp (((torsionAngle k n j : ℝ) : ℂ) * Complex.I)‖ ≤ ε := by
    have hdec : Complex.exp ((((t₀ + (m : ℝ)) * projectiveGapPacket E j : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((torsionAngle k n j : ℝ) : ℂ) * Complex.I)
        = (Complex.exp ((((t₀ + (m : ℝ)) * projectiveGapPacket E j : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((projectiveGapPacket E j * t₀ : ℝ) : ℂ) * Complex.I))
          + (Complex.exp (((projectiveGapPacket E j * t₀ : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((torsionAngle k n j : ℝ) : ℂ) * Complex.I)) := by ring
    rw [hdec]
    refine le_trans (norm_add_le _ _) ?_
    rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    linarith
  -- transport to the flow orientation
  have hconj := norm_exp_neg_ofReal_mul_I_sub ((t₀ + (m : ℝ)) * projectiveGapPacket E j) (torsionAngle k n j)
  rw [exp_neg_torsionAngle] at hconj
  rw [hconj]
  exact hsplit

end LateShadowing

section Capstone

variable {d k : ℕ}

/-- **Theorem B.**  Under the torsion-cap hypothesis `(13)`, an autonomous trajectory of maximal
projective rational rank has arbitrarily late recurrence cycles `(18)` all of whose `k-1` equally
spaced interior slices avoid the whole target dictionary `(19)`. -/
theorem exists_late_recurrence_hard_polygon [NeZero k] (hk : k.Prime) (E : Fin (d + 1) → ℝ)
    (hind : LinearIndependent ℚ (projectiveGapPacket E))
    (Y : Finset (EuclideanSpace ℂ (Fin (d + 1)))) (hY : ∀ y ∈ Y, ‖y‖ = 1) {δ : ℝ}
    (hsmall : (k - 1) * (easyAnchored k Y δ).card < k ^ d)
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∃ τ : ℝ, A < τ ∧
      pureStateTraceDistance (flowRay E ((k : ℝ) * τ)) (flowRay E 0) < ρ ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 → ∀ y ∈ Y,
        δ < pureStateTraceDistance (flowRay E ((j : ℝ) * τ)) y := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : Fin d → ZMod k, ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 →
      (j : ℤ) • q ∉ easyAnchored k Y δ :=
    exists_hard_torsionModel_point (D := d + 1) hk (easyAnchored k Y δ) hsmall
  have hhard : ∀ p ∈ (Finset.Icc 1 (k - 1)) ×ˢ Y,
      δ < pureStateTraceDistance (anchoredRay k ((p.1 : ℤ) • q)) p.2 := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_Icc] at hp
    exact lt_pureStateTraceDistance_of_not_mem_easyAnchored (hq p.1 hp.1.1 hp.1.2) hp.2
  obtain ⟨σ, hσ, hmargin⟩ := exists_margin_of_lt _ _ hhard
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.pos
  set ε : ℝ := min (σ / (2 * (k : ℝ))) (ρ / (2 * (k : ℝ))) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hkσ : (k : ℝ) * ε ≤ σ / 2 := by
    have hle : ε ≤ σ / (2 * (k : ℝ)) := min_le_left _ _
    have : (k : ℝ) * ε ≤ (k : ℝ) * (σ / (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hle hkR.le
    calc (k : ℝ) * ε ≤ (k : ℝ) * (σ / (2 * (k : ℝ))) := this
      _ = σ / 2 := by field_simp
  have hkρ : (k : ℝ) * ε ≤ ρ / 2 := by
    have hle : ε ≤ ρ / (2 * (k : ℝ)) := min_le_right _ _
    have : (k : ℝ) * ε ≤ (k : ℝ) * (ρ / (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hle hkR.le
    calc (k : ℝ) * ε ≤ (k : ℝ) * (ρ / (2 * (k : ℝ))) := this
      _ = ρ / 2 := by field_simp
  obtain ⟨τ, hτA, hτ⟩ := exists_late_shadowing E hind q hε A
  refine ⟨τ, hτA, ?_, ?_⟩
  · -- the recurrence at the endpoint
    have hs : ShadowsTorsion E k ((k : ℕ) • q) ((k : ℝ) * τ) ((k : ℝ) * ε) :=
      shadowsTorsion_nsmul hτ k
    have hzero : ((k : ℕ) • q : Fin d → ZMod k) = 0 := by
      funext a
      show (k : ℕ) • q a = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hzero] at hs
    have hle := pureStateTraceDistance_flowRay_anchoredRay_le E (0 : Fin d → ZMod k)
      (by positivity) hs
    rw [← flowRay_zero (k := k) E] at hle
    linarith
  · -- the hard interior slices
    intro j hj1 hj2 y hy
    have hs : ShadowsTorsion E k ((j : ℕ) • q) ((j : ℝ) * τ) ((j : ℝ) * ε) :=
      shadowsTorsion_nsmul hτ j
    have hjq : ((j : ℕ) • q : Fin d → ZMod k) = ((j : ℤ)) • q := (natCast_zsmul q j).symm
    have hm := hmargin (j, y) (Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hj1, hj2⟩, hy⟩)
    dsimp only at hm
    have hle : pureStateTraceDistance (flowRay E ((j : ℝ) * τ))
        (anchoredRay k ((j : ℕ) • q)) ≤ (j : ℝ) * ε :=
      pureStateTraceDistance_flowRay_anchoredRay_le E ((j : ℕ) • q) (by positivity) hs
    rw [hjq] at hle
    have htri := _root_.HTGeometry.pureStateTraceDistance_triangle
      (anchoredRay k ((j : ℤ) • q)) (flowRay E ((j : ℝ) * τ)) y (norm_anchoredRay _)
      (norm_flowRay E _ (Nat.succ_pos d)) (hY y hy)
    have hcomm := _root_.HTGeometry.pureStateTraceDistance_comm
      (anchoredRay k ((j : ℤ) • q)) (flowRay E ((j : ℝ) * τ))
    have hjk : (j : ℝ) * ε ≤ (k : ℝ) * ε := by
      have hjle : (j : ℝ) ≤ (k : ℝ) := by
        have : j ≤ k := le_trans hj2 (Nat.sub_le k 1)
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hjle hε.le
    linarith

/-- **`(20)`.**  The same statement in recurrence-time parametrization: arbitrarily large recurrence
times `R` whose `k-1` interior rational slices `jR/k` are all target-hard. -/
theorem exists_late_recurrence_rational_slices [NeZero k] (hk : k.Prime) (E : Fin (d + 1) → ℝ)
    (hind : LinearIndependent ℚ (projectiveGapPacket E))
    (Y : Finset (EuclideanSpace ℂ (Fin (d + 1)))) (hY : ∀ y ∈ Y, ‖y‖ = 1) {δ : ℝ}
    (hsmall : (k - 1) * (easyAnchored k Y δ).card < k ^ d)
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∃ R : ℝ, A < R ∧
      pureStateTraceDistance (flowRay E R) (flowRay E 0) < ρ ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 → ∀ y ∈ Y,
        δ < pureStateTraceDistance (flowRay E ((j : ℝ) * R / (k : ℝ))) y := by
  obtain ⟨τ, hτA, hrec, hhard⟩ :=
    exists_late_recurrence_hard_polygon hk E hind Y hY hsmall hρ (max A 0)
  have hτ0 : 0 < τ := lt_of_le_of_lt (le_max_right A 0) hτA
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.one_lt.le
  have hkne : (k : ℝ) ≠ 0 := by linarith
  refine ⟨(k : ℝ) * τ, ?_, hrec, ?_⟩
  · exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left A 0) hτA)
      (le_mul_of_one_le_left hτ0.le hkR)
  · intro j hj1 hj2 y hy
    have hslice : (j : ℝ) * ((k : ℝ) * τ) / (k : ℝ) = (j : ℝ) * τ := by
      field_simp
    rw [hslice]
    exact hhard j hj1 hj2 y hy

end Capstone

end

end GaloisForLFunctions.HTGeometry
