/-
The tilt-sweep discriminator: the Euler anchor couples to the parity sheet at half
rate; an anchor-free member has no sweep at all.

The finite Euler head admits the canonical power family `A^t = exp(t·anchorLog)` —
a homotopy of nonvanishing multipliers from `1` to the anchor that never moves the
member's zeros.  Because the anchor has a global logarithm, every chart square root
transports along the sweep EXPLICITLY: `H ↦ exp(t·anchorLog/2)·H` squares to
`A^t·f`, with no continuation or monodromy bookkeeping.  The transported root's
phase at any point advances at exactly HALF the swept tilt: when the tilt at a
point passes `2π`, the member multiplier returns to the positive-real ray while the
root's sign has flipped — the mod-2 coupling between the prime-indexed steering
walk and the square-root sheet.  The deck class is sweep-invariant (the transport
is one global factor on both charts), and at root resolution the class is the
parity `(−1)^{m_P − m_M}` of the `πℤ`-quantized root-logarithm mismatches — twice
as fine as the member's `2πℤ` dictionary.

The discriminator: the sweep holonomy pair — half the anchor tilts at the two
basepoints.  For a finite Euler head it is DENSE (pair-reachability); for the empty
anchor — the formal shadow of a functional equation without an Euler product — the
sweep is constant and every reading is frozen.  A Davenport–Heilbronn analogue has
only the frozen sweep.
-/
import GaloisForLFunctions.RHTower.ArcWindingDictionary

noncomputable section

namespace RHTower

open Complex Metric Finset

/-! ### §1 The anchor sweep -/

/-- The anchor-phase sweep: the real power `A^t` of the finite Euler head along its
canonical logarithm — a nonvanishing interpolation from `1` to the anchor. -/
noncomputable def anchorSweep (P : Finset ℕ) (t : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((t : ℂ) * anchorLog P s)

theorem anchorSweep_zero (P : Finset ℕ) (s : ℂ) : anchorSweep P 0 s = 1 := by
  rw [anchorSweep]
  norm_num

/-- At `t = 1` the sweep is the anchor itself. -/
theorem anchorSweep_one {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ}
    (hs : 0 < s.re) :
    anchorSweep P 1 s = eulerHeadAnchor P s := by
  rw [anchorSweep, Complex.ofReal_one, one_mul, exp_anchorLog hP hs]

theorem anchorSweep_ne_zero (P : Finset ℕ) (t : ℝ) (s : ℂ) :
    anchorSweep P t s ≠ 0 :=
  Complex.exp_ne_zero _

/-- The sweep is a one-parameter multiplicative family. -/
theorem anchorSweep_add (P : Finset ℕ) (t u : ℝ) (s : ℂ) :
    anchorSweep P (t + u) s = anchorSweep P t s * anchorSweep P u s := by
  rw [anchorSweep, anchorSweep, anchorSweep, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem anchorSweep_analyticAt {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) (t : ℝ)
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (anchorSweep P t) s :=
  (analyticAt_const.mul (anchorLog_analyticAt hP hs)).cexp

/-- The sweep never moves the zeros: multiplication by `A^t` preserves vanishing. -/
theorem anchorSweep_mul_eq_zero_iff (P : Finset ℕ) (t : ℝ) (f : ℂ → ℂ) (z : ℂ) :
    anchorSweep P t z * f z = 0 ↔ f z = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (anchorSweep_ne_zero P t z)
    · exact h'
  · intro h
    rw [h, mul_zero]

/-- The polar form of the sweep: modulus `exp(t·Re anchorLog)`, phase `t` times the
anchor tilt. -/
theorem anchorSweep_polar (P : Finset ℕ) (t : ℝ) (s : ℂ) :
    anchorSweep P t s
      = ((Real.exp (t * (anchorLog P s).re) : ℝ) : ℂ)
        * Complex.exp (((t * anchorTilt P s : ℝ) : ℂ) * I) := by
  have hz : (t : ℂ) * anchorLog P s
      = ((t * (anchorLog P s).re : ℝ) : ℂ)
        + ((t * (anchorLog P s).im : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp
  rw [anchorSweep, hz, Complex.exp_add, ← Complex.ofReal_exp, anchorLog_im]

/-! ### §2 The root transport and the half-angle law -/

/-- The explicit root transport along the sweep: no continuation, no monodromy —
the global anchor logarithm supplies the branch. -/
noncomputable def sweepRoot (P : Finset ℕ) (t : ℝ) (H : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp ((t : ℂ) * anchorLog P z / 2) * H z

theorem sweepRoot_zero (P : Finset ℕ) (H : ℂ → ℂ) (z : ℂ) :
    sweepRoot P 0 H z = H z := by
  rw [sweepRoot]
  norm_num

/-- The transported root squares to the swept member. -/
theorem sweepRoot_sq {f H : ℂ → ℂ} {U : Set ℂ} (hpH : ∀ z ∈ U, H z ^ 2 = f z)
    (P : Finset ℕ) (t : ℝ) :
    ∀ z ∈ U, sweepRoot P t H z ^ 2 = anchorSweep P t z * f z := by
  intro z hz
  rw [sweepRoot, mul_pow, ← Complex.exp_nat_mul, hpH z hz, anchorSweep]
  congr 2
  push_cast
  ring

theorem sweepRoot_analyticOnNhd {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) (t : ℝ)
    {H : ℂ → ℂ} {U : Set ℂ} (hH : AnalyticOnNhd ℂ H U)
    (hre : ∀ z ∈ U, 0 < z.re) :
    AnalyticOnNhd ℂ (sweepRoot P t H) U := fun z hz =>
  (((analyticAt_const.mul (anchorLog_analyticAt hP (hre z hz))).div
    analyticAt_const (by norm_num)).cexp).mul (hH z hz)

/-- **The half-angle law**: the transported root is the original rotated by exactly
half the swept tilt, scaled positively — the square-root sheet turns at half the
anchor's steering rate. -/
theorem sweepRoot_eq_anchorSweep_half (P : Finset ℕ) (t : ℝ) (H : ℂ → ℂ) (z : ℂ) :
    sweepRoot P t H z = anchorSweep P (t / 2) z * H z := by
  rw [sweepRoot, anchorSweep]
  congr 2
  push_cast
  ring

theorem sweepRoot_polar (P : Finset ℕ) (t : ℝ) (H : ℂ → ℂ) (z : ℂ) :
    sweepRoot P t H z
      = ((Real.exp (t * (anchorLog P z).re / 2) : ℝ) : ℂ)
        * (Complex.exp (((t * anchorTilt P z / 2 : ℝ) : ℂ) * I) * H z) := by
  rw [sweepRoot_eq_anchorSweep_half, anchorSweep_polar, mul_assoc,
    show t / 2 * (anchorLog P z).re = t * (anchorLog P z).re / 2 from by ring,
    show t / 2 * anchorTilt P z = t * anchorTilt P z / 2 from by ring]

/-- **The mod-2 coupling**: when the anchor's tilt at a point is `2π`, the full
sweep returns the member multiplier to the positive-real ray … -/
theorem anchorSweep_pos_real_of_tilt_two_pi {P : Finset ℕ} {z : ℂ}
    (htilt : anchorTilt P z = 2 * Real.pi) :
    anchorSweep P 1 z = ((Real.exp ((anchorLog P z).re) : ℝ) : ℂ) := by
  rw [anchorSweep_polar, htilt]
  rw [show ((1 * (2 * Real.pi) : ℝ) : ℂ) * I = ((2 * Real.pi : ℝ) : ℂ) * I from by
    push_cast; ring]
  rw [show ((2 * Real.pi : ℝ) : ℂ) * I = 2 * Real.pi * I from by push_cast; ring,
    Complex.exp_two_pi_mul_I, mul_one, one_mul]

/-- … while the transported root's SIGN has flipped: the root system counts the
anchor's full phase turns mod 2. -/
theorem sweepRoot_sign_flip_of_tilt_two_pi {P : Finset ℕ} {z : ℂ}
    (htilt : anchorTilt P z = 2 * Real.pi) (H : ℂ → ℂ) :
    sweepRoot P 1 H z
      = -(((Real.exp ((anchorLog P z).re / 2) : ℝ) : ℂ) * H z) := by
  rw [sweepRoot_polar, htilt]
  rw [show ((1 * (2 * Real.pi) / 2 : ℝ) : ℂ) * I = ((Real.pi : ℝ) : ℂ) * I from by
    push_cast; ring]
  rw [Complex.exp_pi_mul_I]
  rw [show (1 : ℝ) * (anchorLog P z).re / 2 = (anchorLog P z).re / 2 from by ring]
  ring

/-! ### §3 The deck class is sweep-invariant -/

/-- The sweep transports both chart roots by one global factor, so the deck class
never moves: the prime set cannot reach the parity through the transported root
system's overlap cocycle. -/
theorem deckClass_sweepRoot (P : Finset ℕ) (t : ℝ) (H₁ H₂ : ℂ → ℂ) (pP pM : ℂ) :
    deckClass (sweepRoot P t H₁) (sweepRoot P t H₂) pP pM
      = deckClass H₁ H₂ pP pM := by
  have h1 : sweepRoot P t H₁
      = fun z => H₁ z * Complex.exp ((t : ℂ) * anchorLog P z / 2) :=
    funext fun z => mul_comm _ _
  have h2 : sweepRoot P t H₂
      = fun z => H₂ z * Complex.exp ((t : ℂ) * anchorLog P z / 2) :=
    funext fun z => mul_comm _ _
  rw [h1, h2, deckClass_mul_global
    (r := fun z => Complex.exp ((t : ℂ) * anchorLog P z / 2))
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)]

/-! ### §4 The π-quantized root-level dictionary -/

/-- Chart square roots of the same function have pointwise ratio `±1` on the
overlap. -/
theorem root_ratio_pm_one {f H₁ H₂ : ℂ → ℂ} {p : ℂ}
    (h₁ : H₁ p ^ 2 = f p) (h₂ : H₂ p ^ 2 = f p) (hf : f p ≠ 0) :
    H₁ p / H₂ p = 1 ∨ H₁ p / H₂ p = -1 := by
  have hH₂ : H₂ p ≠ 0 := fun h0 => hf (by rw [← h₂, h0]; ring)
  have hsq : (H₁ p / H₂ p) ^ 2 = 1 := by
    rw [div_pow, h₁, h₂, div_self hf]
  have h2 : (H₁ p / H₂ p - 1) * (H₁ p / H₂ p + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (eq_neg_of_add_eq_zero_left h')

/-- **The root-level winding dictionary**: root-logarithm mismatches are
`πℤ`-quantized — twice as fine as the member's `2πℤ` — and the deck class is
`(−1)^{m_P − m_M}` on the nose: the parity IS the difference of the root-level
winding integers. -/
theorem deckClass_neg_one_zpow_root_log_mismatch {f H₁ H₂ h₁ h₂ : ℂ → ℂ}
    {U₁ U₂ : Set ℂ}
    (hpH₁ : ∀ z ∈ U₁, H₁ z ^ 2 = f z) (hpH₂ : ∀ z ∈ U₂, H₂ z ^ 2 = f z)
    (hexp₁ : ∀ z ∈ U₁, Complex.exp (h₁ z) = H₁ z)
    (hexp₂ : ∀ z ∈ U₂, Complex.exp (h₂ z) = H₂ z)
    {pP pM : ℂ} (hpP₁ : pP ∈ U₁) (hpP₂ : pP ∈ U₂)
    (hpM₁ : pM ∈ U₁) (hpM₂ : pM ∈ U₂)
    (hfP : f pP ≠ 0) (hfM : f pM ≠ 0) :
    ∃ mP mM : ℤ,
      (h₁ pP - h₂ pP).im = mP * Real.pi ∧
      (h₁ pM - h₂ pM).im = mM * Real.pi ∧
      deckClass H₁ H₂ pP pM = (-1 : ℂ) ^ (mP - mM) := by
  have key : ∀ p : ℂ, p ∈ U₁ → p ∈ U₂ → f p ≠ 0 →
      ∃ m : ℤ, (h₁ p - h₂ p).im = m * Real.pi
        ∧ H₁ p / H₂ p = (-1 : ℂ) ^ m := by
    intro p hp₁ hp₂ hf
    have hexp_ratio : Complex.exp (h₁ p - h₂ p) = H₁ p / H₂ p := by
      rw [Complex.exp_sub, hexp₁ p hp₁, hexp₂ p hp₂]
    rcases root_ratio_pm_one (hpH₁ p hp₁) (hpH₂ p hp₂) hf with hρ | hρ
    · obtain ⟨m, hm⟩ := im_eq_int_mul_pi_of_exp_real (r := 1) one_ne_zero
        (by rw [hexp_ratio, hρ]; norm_num)
      refine ⟨m, hm, ?_⟩
      have hre : (h₁ p - h₂ p).re = 0 := by
        have hnorm := congrArg norm hexp_ratio
        rw [Complex.norm_exp, hρ, norm_one] at hnorm
        exact Real.exp_injective (by rw [hnorm, Real.exp_zero])
      have hw : h₁ p - h₂ p = ((m * Real.pi : ℝ) : ℂ) * I := by
        apply Complex.ext
        · simp [hre]
        · simp [hm]
      rw [← hexp_ratio, hw,
        show ((m * Real.pi : ℝ) : ℂ) * I = (m : ℂ) * (Real.pi * I) from by
          push_cast; ring,
        Complex.exp_int_mul, Complex.exp_pi_mul_I]
    · obtain ⟨m, hm⟩ := im_eq_int_mul_pi_of_exp_real (r := -1)
        (by norm_num)
        (by rw [hexp_ratio, hρ]; norm_num)
      refine ⟨m, hm, ?_⟩
      have hre : (h₁ p - h₂ p).re = 0 := by
        have hnorm := congrArg norm hexp_ratio
        rw [Complex.norm_exp, hρ, norm_neg, norm_one] at hnorm
        exact Real.exp_injective (by rw [hnorm, Real.exp_zero])
      have hw : h₁ p - h₂ p = ((m * Real.pi : ℝ) : ℂ) * I := by
        apply Complex.ext
        · simp [hre]
        · simp [hm]
      rw [← hexp_ratio, hw,
        show ((m * Real.pi : ℝ) : ℂ) * I = (m : ℂ) * (Real.pi * I) from by
          push_cast; ring,
        Complex.exp_int_mul, Complex.exp_pi_mul_I]
  obtain ⟨mP, hmP, hρP⟩ := key pP hpP₁ hpP₂ hfP
  obtain ⟨mM, hmM, hρM⟩ := key pM hpM₁ hpM₂ hfM
  refine ⟨mP, mM, hmP, hmM, ?_⟩
  rw [deckClass, hρP, hρM, ← zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)]

/-! ### §5 The discriminator: frozen without the Euler head, dense with it -/

/-- The empty anchor has zero canonical logarithm. -/
theorem anchorLog_empty (s : ℂ) : anchorLog ∅ s = 0 := by
  rw [anchorLog, Finset.sum_empty]

/-- **The anchor-free sweep is constant** — the formal shadow of a functional
equation without an Euler product: nothing to sweep, every boundary reading
frozen.  This is the Davenport–Heilbronn side of the discriminator. -/
theorem anchorSweep_empty (t : ℝ) (s : ℂ) : anchorSweep ∅ t s = 1 := by
  rw [anchorSweep, anchorLog_empty]
  norm_num

/-- The anchor-free root transport is the identity. -/
theorem sweepRoot_empty (t : ℝ) (H : ℂ → ℂ) (z : ℂ) :
    sweepRoot ∅ t H z = H z := by
  rw [sweepRoot, anchorLog_empty]
  norm_num

/-- **The Euler side of the discriminator**: the sweep-holonomy pair — half the
anchor tilts at the two basepoints, the exact angles the two basepoint root
readings turn under the full sweep — reaches every nonnegative target box within
every tolerance, over prime sets beyond any bound.  The Euler walk couples to the
square-root sheet densely; the empty anchor not at all. -/
theorem sweep_holonomy_pair_reachable {ρ : ℂ} {c : ℝ}
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (hcap : (ρ.im + c) * (4 * Real.log 2) < Real.pi)
    {Tp Tm : ℝ} (hTp : 0 ≤ Tp) (hTm : 0 ≤ Tm) {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      |Tp - anchorTilt P (ρ + (c : ℂ) * I) / 2| ≤ ε ∧
      |Tm - anchorTilt P (ρ - (c : ℂ) * I) / 2| ≤ ε := by
  obtain ⟨P, hP, hp, hm⟩ := anchorTilt_pair_reachable_nonneg hre0 hre1 hc hcτ
    hnarrow hcap (Tp := 2 * Tp) (Tm := 2 * Tm) (by linarith) (by linarith)
    (ε := 2 * ε) (by linarith) Q
  refine ⟨P, hP, ?_, ?_⟩
  · rw [abs_le] at hp ⊢
    constructor <;> [linarith [hp.1]; linarith [hp.2]]
  · rw [abs_le] at hm ⊢
    constructor <;> [linarith [hm.1]; linarith [hm.2]]

/-- The sweep preserves the analytic order at every strip point: the homotopy from
the member to the anchored member never moves a zero or changes its multiplicity —
the hole count is a sweep invariant. -/
theorem analyticOrderAt_anchorSweep_mul {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    (t : ℝ) {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hz : 0 < z.re) :
    analyticOrderAt (fun w => anchorSweep P t w * f w) z = analyticOrderAt f z := by
  have hA : AnalyticAt ℂ (anchorSweep P t) z := anchorSweep_analyticAt hP t hz
  have hfun : (fun w => anchorSweep P t w * f w) = anchorSweep P t * f := rfl
  rw [hfun, analyticOrderAt_mul hA hf,
    hA.analyticOrderAt_eq_zero.mpr (anchorSweep_ne_zero P t z), zero_add]

/-- **The discriminator's observable**: the full sweep multiplies the
cross-basepoint root ratio by a positive scalar and the rotation by HALF the
endpoint tilt difference — the relative sweep holonomy.  The scalar is
parity-blind; the rotation is the steerable reading. -/
theorem sweepRoot_cross_ratio (P : Finset ℕ) (H : ℂ → ℂ) (pP pM : ℂ) :
    sweepRoot P 1 H pP / sweepRoot P 1 H pM
      = ((Real.exp (((anchorLog P pP).re - (anchorLog P pM).re) / 2) : ℝ) : ℂ)
        * (Complex.exp ((((anchorTilt P pP - anchorTilt P pM) / 2 : ℝ) : ℂ) * I)
            * (H pP / H pM)) := by
  rw [sweepRoot_polar, sweepRoot_polar]
  have heR : ((Real.exp (((anchorLog P pP).re - (anchorLog P pM).re) / 2) : ℝ) : ℂ)
      = ((Real.exp (1 * (anchorLog P pP).re / 2) : ℝ) : ℂ)
        / ((Real.exp (1 * (anchorLog P pM).re / 2) : ℝ) : ℂ) := by
    have h : ((anchorLog P pP).re - (anchorLog P pM).re) / 2
        = 1 * (anchorLog P pP).re / 2 - 1 * (anchorLog P pM).re / 2 := by ring
    rw [← Complex.ofReal_div, ← Real.exp_sub, h]
  have heC : Complex.exp ((((anchorTilt P pP - anchorTilt P pM) / 2 : ℝ) : ℂ) * I)
      = Complex.exp (((1 * anchorTilt P pP / 2 : ℝ) : ℂ) * I)
        / Complex.exp (((1 * anchorTilt P pM / 2 : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_sub]
    congr 1
    push_cast
    ring
  rw [heR, heC, mul_div_mul_comm, mul_div_mul_comm]

/-- **Near-half-turn steering**: prime sets beyond any bound bring the relative
sweep holonomy `ε`-close to a half turn — the cross-basepoint reading of the
transported root system approaches a sign flip while the deck class stays
pinned.  The gap between this rotation observable and the chart-ratio parity is
the residual selection principle of the weld. -/
theorem exists_near_half_turn_relative_holonomy {ρ : ℂ} {c : ℝ}
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (hcap : (ρ.im + c) * (4 * Real.log 2) < Real.pi)
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      |(anchorTilt P (ρ + (c : ℂ) * I) - anchorTilt P (ρ - (c : ℂ) * I)) / 2
        - Real.pi| ≤ ε := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨P, hP, hp, hm⟩ := sweep_holonomy_pair_reachable hre0 hre1 hc hcτ
    hnarrow hcap (Tp := 3 * Real.pi / 2) (Tm := Real.pi / 2)
    (by linarith) (by linarith) (show (0 : ℝ) < ε / 2 by linarith) Q
  refine ⟨P, hP, ?_⟩
  rw [abs_le] at hp hm ⊢
  constructor
  · linarith [hp.1, hp.2, hm.1, hm.2]
  · linarith [hp.1, hp.2, hm.1, hm.2]

/-- At full sweep the transported member roots are anchored-member roots: the
explicit transport lands exactly on the anchored symmetric member. -/
theorem sweepRoot_one_sq_anchoredSEM {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {N : ℕ}
    {H : ℂ → ℂ} {U : Set ℂ} (hre : ∀ z ∈ U, 0 < z.re)
    (hpH : ∀ z ∈ U, H z ^ 2 = completedSEM N z) :
    ∀ z ∈ U, sweepRoot P 1 H z ^ 2 = anchoredSEM P N z := by
  intro z hz
  rw [sweepRoot_sq hpH P 1 z hz, anchorSweep_one hP (hre z hz)]
  rfl

end RHTower
