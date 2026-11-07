import GaloisForLFunctions.ArithmeticScatteringHolography.TheKreinFluxLaw
import GaloisForLFunctions.ArithmeticScatteringHolography.HeckeAtASecondPlace
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Hasse window and the fake black holes

The trace is a difference of channel counts: `t = q + 1 - h`, and `q + 1 + t` counts the two-torsion points
and twice the dead ends. Writing `h' = q + 1 + t`, we have `h h' = (q+1)² - t²`.

* **The edge theorem.** The counts give `|t| ≤ q` (`abs_traceR_le`). Every resonance has `|a| < q`
  (`norm_resonance_lt`): by the flux law when `Y` is not real, and by the count when `a` is real and
  positive. This is the statement that `ζ` of the black hole has no zero on the edge.
* **The Hasse window.** Universal damping says the number of cusps lies between `(√q - 1)²` and `(√q + 1)²`,
  or equivalently `h h' ≥ (q-1)²` (`universal_iff_window`). So it is a balance of open and trapped channels. With too
  few open channels, energy leaves slowly and a real mode is slower than universal. With too many, necks
  transmit from cusp to cusp, and a mode at `λ` near zero is slow.
* **The fake black holes.** Every odd group order `N ≤ 2q + 1` gives a black hole, with `t = q + 1 - N`
  (`oddChannels`). It has local regularity, the flux law, unitarity, causality and a full commuting family of
  Hecke operators. When `t² > 4q` it has a resonance off the universal circle
  (`exists_slow_resonance`). So **universal damping is not a law of wave dynamics on a tree lattice**: a
  derivation must use arithmetic that the graph does not record.
-/

open Finset ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]

/-- The real trace `t = q + 1 - h`. -/
def Channels.traceR (B : Channels G D) : ℝ := (B.q : ℝ) + 1 - Fintype.card G

theorem Channels.trace_eq_ofReal (B : Channels G D) : B.trace = (B.traceR : ℂ) := by
  unfold Channels.trace Channels.traceR cuspCount
  push_cast
  ring

/-- There is at least one two-torsion point. -/
theorem one_le_card_twoTorsion : 1 ≤ Fintype.card (TwoTorsion G) :=
  Fintype.card_pos_iff.mpr ⟨⟨0, by simp⟩⟩

/-- The count of trapped channels: `q + 1 + t = a + 2c`. -/
theorem Channels.twist_count (B : Channels G D) :
    (B.q : ℝ) + 1 + B.traceR = (Fintype.card (TwoTorsion G) : ℝ) + 2 * Fintype.card D := by
  have := congrArg (Nat.cast : ℕ → ℝ) B.count
  push_cast at this
  unfold Channels.traceR
  linarith

/-- **`h' > 0`**: the two-torsion point `0` is a trapped channel of the twist. -/
theorem Channels.twist_pos (B : Channels G D) : 0 < (B.q : ℝ) + 1 + B.traceR := by
  rw [B.twist_count]
  have h1 : (1 : ℝ) ≤ Fintype.card (TwoTorsion G) := by exact_mod_cast one_le_card_twoTorsion
  have h2 : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  linarith

/-- **`h > 0`**: the point `0` is an open channel. -/
theorem Channels.open_pos (B : Channels G D) : 0 < (B.q : ℝ) + 1 - B.traceR := by
  unfold Channels.traceR
  have h1 : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  linarith

/-- **The edge bound.** `|t| ≤ q`, from the two counts. -/
theorem Channels.abs_traceR_le (B : Channels G D) : |B.traceR| ≤ B.q := by
  rw [abs_le]
  constructor
  · have := B.twist_count
    have h1 : (1 : ℝ) ≤ Fintype.card (TwoTorsion G) := by exact_mod_cast one_le_card_twoTorsion
    have h2 : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
    linarith
  · unfold Channels.traceR
    have h1 : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
    linarith

theorem Channels.q_pos (B : Channels G D) : (2 : ℝ) ≤ B.q := by exact_mod_cast B.two_le

/-! ### The window -/

/-- **The Hasse window.** With `h` cusps and `h' = 2(q+1) - h`, not overdamped means
`(√q-1)² ≤ h ≤ (√q+1)²`, equivalently `h h' ≥ (q-1)²`. -/
theorem universal_iff_window {q h : ℝ} (hq : 0 < q) :
    (q + 1 - h) ^ 2 ≤ 4 * q ↔
      ((Real.sqrt q - 1) ^ 2 ≤ h ∧ h ≤ (Real.sqrt q + 1) ^ 2) := by
  set r := Real.sqrt q with hr
  have hrsq : r ^ 2 = q := Real.sq_sqrt hq.le
  have hrpos : 0 < r := Real.sqrt_pos.mpr hq
  have e1 : (r - 1) ^ 2 = q + 1 - 2 * r := by rw [← hrsq]; ring
  have e2 : (r + 1) ^ 2 = q + 1 + 2 * r := by rw [← hrsq]; ring
  rw [e1, e2]
  have e3 : 4 * q = (2 * r) ^ 2 := by rw [← hrsq]; ring
  rw [e3]
  constructor
  · intro h1
    have h2 := abs_le_of_sq_le_sq' h1 (by positivity)
    constructor <;> linarith [h2.1, h2.2]
  · rintro ⟨h1, h2⟩
    have h3 : q + 1 - h ≤ 2 * r := by linarith
    have h4 : -(2 * r) ≤ q + 1 - h := by linarith
    exact sq_le_sq' h4 h3

/-- The same window as a product of channel counts. -/
theorem universal_iff_product {q t : ℝ} :
    t ^ 2 ≤ 4 * q ↔ (q - 1) ^ 2 ≤ (q + 1 - t) * (q + 1 + t) := by
  constructor <;> intro h <;> nlinarith

/-! ### Resonances from the roots -/

/-- **Every root of the Frobenius polynomial is a resonance of the black hole.** -/
theorem Channels.exists_resonance_of_root (B : Channels G D) {a : ℂ}
    (ha : a ^ 2 - (B.traceR : ℂ) * a + (B.q : ℂ) = 0) :
    ∃ X Y : ℂ, X ^ 2 = a ∧ X * Y = B.q ∧ X ≠ Y ∧ X + Y ≠ 0 ∧
      ∃ (f : Vertex G D → ℂ) (c : G → ℂ), f ≠ 0 ∧ IsOutgoing B.q X Y f c ∧ ∃ P, c P ≠ 0 := by
  have hq : (2 : ℝ) ≤ B.q := B.q_pos
  have hq0' : (B.q : ℂ) ≠ 0 := B.q_ne_zero
  have hne0 : a ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_self,
      zero_add] at ha
    exact hq0' ha
  obtain ⟨X, hX⟩ := IsAlgClosed.exists_pow_nat_eq a (n := 2) (by norm_num)
  have hX0 : X ≠ 0 := by
    rintro rfl
    apply hne0
    rw [← hX]
    simp
  set Y : ℂ := (B.q : ℂ) / X with hY
  have hXY : X * Y = B.q := by
    rw [hY]
    field_simp
  have hX2 : X * X = a := by rw [← hX]; ring
  have hab := B.abs_traceR_le
  have htw := B.twist_pos
  have hop := B.open_pos
  have htcast : ((B.q : ℂ) + 1 + (B.traceR : ℂ)) ≠ 0 := by
    have : (((B.q : ℝ) + 1 + B.traceR : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htw.ne'
    simpa using this
  have htcast' : ((B.q : ℂ) + 1 - (B.traceR : ℂ)) ≠ 0 := by
    have : (((B.q : ℝ) + 1 - B.traceR : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hop.ne'
    simpa using this
  have hneY : X ≠ Y := by
    intro h
    apply htcast'
    have hsq : a = B.q := by rw [← hX2, ← hXY, ← h]
    rw [hsq] at ha
    have : (B.q : ℂ) * ((B.q : ℂ) + 1 - (B.traceR : ℂ)) = 0 := by linear_combination ha
    exact (mul_eq_zero.mp this).resolve_left hq0'
  have hlam : X + Y ≠ 0 := by
    intro h
    apply htcast
    have hsq : a = -(B.q : ℂ) := by
      rw [← hX2, ← hXY]
      have : Y = -X := by linear_combination h
      rw [this]
      ring
    rw [hsq] at ha
    have : (B.q : ℂ) * ((B.q : ℂ) + 1 + (B.traceR : ℂ)) = 0 := by linear_combination ha
    exact (mul_eq_zero.mp this).resolve_left hq0'
  have hj : jost B.trace X Y = 0 := by
    rw [jost_eq_zero_iff hXY hX0, B.trace_eq_ofReal]
    right
    rw [hX]
    exact ha
  obtain ⟨f, c, hf0, hf⟩ := (exists_outgoing_iff B hXY hneY hlam).mpr hj
  refine ⟨X, Y, hX, hXY, hneY, hlam, f, c, hf0, hf, ?_⟩
  by_contra hall
  have hall' : ∀ P, c P = 0 := by
    intro P
    by_contra hP
    exact hall ⟨P, hP⟩
  exact hf0 (hf.eq_zero_of_amplitude B hXY hlam hall')

/-- **The edge theorem from flux.** Every root of the Frobenius polynomial of a black hole has `|a| < q`. If `a`
is not positive real then `Y` is not real and the flux law gives it; if `a` is positive, the count gives it. -/
theorem Channels.norm_resonance_lt (B : Channels G D) {a : ℂ}
    (ha : a ^ 2 - (B.traceR : ℂ) * a + (B.q : ℂ) = 0) : ‖a‖ < B.q := by
  have hq := B.q_pos
  have hq0 : (0 : ℝ) < B.q := by linarith
  obtain ⟨X, Y, hX, hXY, hne, hlam, f, c, hf0, hf, hc⟩ := B.exists_resonance_of_root ha
  have hX0 : X ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hXY
    exact B.q_ne_zero hXY.symm
  by_cases hYim : Y.im = 0
  · -- `Y` real, so `X` real, so `a` is a positive real
    have hYreal : Y = (Y.re : ℂ) := by
      apply Complex.ext <;> simp [hYim]
    have hYne : Y.re ≠ 0 := by
      intro h
      rw [hYreal, h] at hXY
      simp only [Complex.ofReal_zero, mul_zero] at hXY
      exact B.q_ne_zero hXY.symm
    set y := Y.re
    have hXreal : X = ((B.q : ℝ) / y : ℝ) := by
      push_cast
      rw [eq_div_iff (by exact_mod_cast hYne)]
      rw [← hXY, hYreal]
    set x : ℝ := (B.q : ℝ) / y with hx
    have hx0 : x ≠ 0 := div_ne_zero hq0.ne' hYne
    have hapos : a = ((x ^ 2 : ℝ) : ℂ) := by
      rw [← hX, hXreal]
      push_cast
      ring
    have hroot : (x ^ 2) ^ 2 - B.traceR * x ^ 2 + B.q = 0 := by
      rw [hapos] at ha
      exact_mod_cast ha
    have hxpos : 0 < x ^ 2 := by positivity
    have hle := (abs_le.mp B.abs_traceR_le).2
    rw [hapos, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    by_contra hge
    have hge' := not_lt.mp hge
    nlinarith
  · have := normSq_lt_of_outgoing B hXY hYim hf hc
    have hnorm : ‖a‖ = Complex.normSq X := by
      rw [← hX, norm_pow, Complex.normSq_eq_norm_sq]
    rw [hnorm]
    exact this

/-! ### The fakes -/

/-- In a group of odd order, only `0` is two-torsion. -/
theorem card_twoTorsion_zmod {N : ℕ} [NeZero N] (hN : Odd N) :
    Fintype.card (TwoTorsion (ZMod N)) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, by simp⟩, fun ⟨P, hP⟩ => ?_⟩
  have hunit : IsUnit (2 : ZMod N) := by
    have : IsUnit ((2 : ℕ) : ZMod N) :=
      (ZMod.isUnit_iff_coprime 2 N).mpr (Nat.coprime_two_left.mpr hN)
    simpa using this
  have h2 : (2 : ZMod N) * P = 0 := by simpa [two_nsmul, two_mul] using hP
  have : P = 0 := (hunit.mul_right_eq_zero).mp h2
  exact Subtype.ext this

/-- **The black hole of an odd cyclic group.** `G = ℤ/N`, with `q + 1 - (N+1)/2` dead ends. No curve is needed. -/
def oddChannels (q N : ℕ) [NeZero N] (hN : Odd N) (hq : 2 ≤ q) (hle : N ≤ 2 * q + 1) :
    Channels (ZMod N) (Fin (q + 1 - (N + 1) / 2)) where
  q := q
  two_le := hq
  count := by
    rw [card_twoTorsion_zmod hN, ZMod.card, Fintype.card_fin]
    obtain ⟨m, rfl⟩ := hN
    have : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [this]
    omega

theorem traceR_oddChannels (q N : ℕ) [NeZero N] (hN : Odd N) (hq : 2 ≤ q) (hle : N ≤ 2 * q + 1) :
    (oddChannels q N hN hq hle).traceR = (q : ℝ) + 1 - N := by
  simp [Channels.traceR, oddChannels, ZMod.card]

/-- **A black hole with a slow real mode.** Above the critical discriminant a resonance with `|a|² > q`
exists: its rate is below `¼`, and its partner's rate is above `¼`. -/
theorem exists_slow_resonance (B : Channels G D) (hfake : 4 * (B.q : ℝ) < B.traceR ^ 2) :
    ∃ (X Y : ℂ) (f : Vertex G D → ℂ) (c : G → ℂ), f ≠ 0 ∧ IsOutgoing B.q X Y f c ∧
      (B.q : ℝ) < Complex.normSq (X ^ 2) ∧ (∃ P, c P ≠ 0) ∧ dampingRate B.q (X ^ 2) < 1 / 4 := by
  have hq := B.q_pos
  have hq0 : (0 : ℝ) < B.q := by linarith
  have hq1 : (1 : ℝ) < B.q := by linarith
  obtain ⟨x, x', hsum, hprod, hbig, hsmall⟩ := exists_slow_mode hq0 hfake
  have hroot : ((x : ℂ)) ^ 2 - (B.traceR : ℂ) * x + (B.q : ℂ) = 0 := by
    have : x ^ 2 - B.traceR * x + B.q = 0 := by
      rw [← hsum, ← hprod]
      ring
    exact_mod_cast this
  obtain ⟨X, Y, hX, _, _, _, f, c, hf0, hf, hc⟩ := B.exists_resonance_of_root hroot
  refine ⟨X, Y, f, c, hf0, hf, ?_, hc, ?_⟩
  · rw [hX, Complex.normSq_ofReal]
    nlinarith
  · have hx0 : x ≠ 0 := by
      rintro rfl
      nlinarith
    have hn : ‖X ^ 2‖ = |x| := by
      rw [hX, Complex.norm_real, Real.norm_eq_abs]
    unfold dampingRate
    rw [hn]
    have hlog : 0 < Real.log (B.q : ℝ) := Real.log_pos hq1
    have habs : (B.q : ℝ) < |x| ^ 2 := by rw [sq_abs]; exact hbig
    have hlog2 : Real.log (B.q : ℝ) < 2 * Real.log |x| := by
      have := Real.log_lt_log hq0 habs
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have h3 : 1 / 2 < Real.log |x| / Real.log (B.q : ℝ) := by
      rw [lt_div_iff₀ hlog]
      linarith
    linarith

/-- **Universal damping is not a law of wave dynamics.** For every `q ≥ 5` the black hole with one cusp and `q`
dead ends has all the structure of the wave dynamics, and a resonance slower than universal. -/
theorem universal_damping_not_forced_one_cusp {q : ℕ} (hq : 5 ≤ q) :
    let B := oddChannels q 1 odd_one (by omega) (by omega)
    (∀ v : Vertex (ZMod 1) (Fin (q + 1 - (1 + 1) / 2)),
      waveOp B.q (fun _ => (1 : ℂ)) v = (B.q : ℂ) + 1) ∧
      (∀ (Q Q' : ZMod 1) (f : Vertex (ZMod 1) (Fin (q + 1 - (1 + 1) / 2)) → ℂ) (v),
        heckeOp B.q Q (heckeOp B.q Q' f) v = heckeOp B.q Q' (heckeOp B.q Q f) v) ∧
      ∃ (X Y : ℂ) (f : Vertex (ZMod 1) (Fin (q + 1 - (1 + 1) / 2)) → ℂ) (c : ZMod 1 → ℂ),
        f ≠ 0 ∧ IsOutgoing B.q X Y f c ∧ (B.q : ℝ) < Complex.normSq (X ^ 2) := by
  intro B
  refine ⟨B.waveOp_one, heckeOp_comm B, ?_⟩
  have htr : B.traceR = (q : ℝ) := by
    show (oddChannels q 1 odd_one _ _).traceR = _
    rw [traceR_oddChannels]
    push_cast
    ring
  have hq' : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hBq : (B.q : ℝ) = q := rfl
  obtain ⟨X, Y, f, c, hf0, hf, hbig, _⟩ := exists_slow_resonance B (by rw [htr, hBq]; nlinarith)
  exact ⟨X, Y, f, c, hf0, hf, hbig⟩

/-- **The same with a nontrivial cusp group.** For `q ≥ 8`, the group `ℤ/3` has Hecke operators at its
nontrivial classes, moving the cusps, and the black hole still has a slow resonance. -/
theorem universal_damping_not_forced_three_cusps {q : ℕ} (hq : 8 ≤ q) :
    let B := oddChannels q 3 (by decide) (by omega) (by omega)
    (∀ (Q Q' : ZMod 3) (f : Vertex (ZMod 3) (Fin (q + 1 - (3 + 1) / 2)) → ℂ) (v),
        heckeOp B.q Q (heckeOp B.q Q' f) v = heckeOp B.q Q' (heckeOp B.q Q f) v) ∧
      ∃ (X Y : ℂ) (f : Vertex (ZMod 3) (Fin (q + 1 - (3 + 1) / 2)) → ℂ) (c : ZMod 3 → ℂ),
        f ≠ 0 ∧ IsOutgoing B.q X Y f c ∧ (B.q : ℝ) < Complex.normSq (X ^ 2) := by
  intro B
  refine ⟨heckeOp_comm B, ?_⟩
  have htr : B.traceR = (q : ℝ) - 2 := by
    show (oddChannels q 3 _ _ _).traceR = _
    rw [traceR_oddChannels]
    push_cast
    ring
  have hq' : (8 : ℝ) ≤ q := by exact_mod_cast hq
  have hBq : (B.q : ℝ) = q := rfl
  obtain ⟨X, Y, f, c, hf0, hf, hbig, _⟩ := exists_slow_resonance B (by rw [htr, hBq]; nlinarith)
  exact ⟨X, Y, f, c, hf0, hf, hbig⟩

/-- **The fake on the other side.** With `N = 2q + 1` cusps and no dead ends, `t = -q`. For `q ≥ 5` the slow
modes have `a < 0`, so the ring-down oscillates at the frequency of `λ` near zero. -/
theorem universal_damping_not_forced_many_cusps {q : ℕ} (hq : 5 ≤ q) :
    let B := oddChannels q (2 * q + 1) ⟨q, rfl⟩ (by omega) le_rfl
    ∃ (X Y : ℂ) (f : Vertex (ZMod (2 * q + 1)) (Fin (q + 1 - (2 * q + 1 + 1) / 2)) → ℂ)
        (c : ZMod (2 * q + 1) → ℂ),
      f ≠ 0 ∧ IsOutgoing B.q X Y f c ∧ (B.q : ℝ) < Complex.normSq (X ^ 2) := by
  intro B
  have htr : B.traceR = -(q : ℝ) := by
    show (oddChannels q (2 * q + 1) _ _ _).traceR = _
    rw [traceR_oddChannels]
    push_cast
    ring
  have hq' : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hBq : (B.q : ℝ) = q := rfl
  obtain ⟨X, Y, f, c, hf0, hf, hbig, _⟩ := exists_slow_resonance B (by rw [htr, hBq]; nlinarith)
  exact ⟨X, Y, f, c, hf0, hf, hbig⟩

end GaloisForLFunctions.ArithmeticScatteringHolography

end
