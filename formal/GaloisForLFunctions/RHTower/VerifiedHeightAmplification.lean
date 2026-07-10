/-
# Verified-height amplification from equivariant zero censuses

This module isolates the exact integer input that can extend a verified RH height without any
minimum-modulus computation.  `RHVerifiedThrough H` records that every positive-ordinate strip zero
through height `H` is on the critical line.  `stripZeroIncrement H U` is the finite set of strip
zeros in the half-open increment `(H, U]`.

The capstone `rhVerifiedThrough_amplify_of_increment_ncard_le_one` says that a census of at most one
new distinct zero amplifies RH from `H` through `U`.  The reason is quantized and uniform at the
critical line: an off-line zero and its critical-line reflection are two distinct members of the
increment.  Unlike a modulus or logarithmic-derivative margin, this count does not decay when the
off-line pair approaches the line.

The theorems are bridges, not the missing analytic estimate.  The second capstone weakens a census
of the whole increment to an equivariant collar: at most one zero near the critical line and no
zeros in one outer wing.  Reflection supplies the other wing.  This is the right interface when
the verified endpoint itself may be a simple critical-line zero, so a full top-edge nonvanishing
margin is unavailable.
-/
import GaloisForLFunctions.RHTower.WindowLadder

namespace RHTower

open Complex

/-- RH verified through the positive ordinate `T`, restricted to the open critical strip. -/
def RHVerifiedThrough (T : ℝ) : Prop :=
  ∀ ⦃ρ : ℂ⦄, xi ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ T → ρ.re = 1 / 2

/-- **The verified-height interface has an unconditional base.**  At every nonpositive height there
is no positive-ordinate zero to check, so `RHVerifiedThrough T` holds vacuously.  In particular this
discharges the initial-height hypothesis of the amplification theorems at `T = 0`; only their new
zero census remains. -/
theorem rhVerifiedThrough_of_nonpos {T : ℝ} (hT : T ≤ 0) : RHVerifiedThrough T := by
  intro ρ _ _ _ him0 himT
  exfalso
  linarith

theorem rhVerifiedThrough_zero : RHVerifiedThrough 0 :=
  rhVerifiedThrough_of_nonpos le_rfl

/-- Strip zeros in the half-open height increment `(H, U]`. -/
def stripZeroIncrement (H U : ℝ) : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ H < ρ.im ∧ ρ.im ≤ U ∧ xi ρ = 0}

/-- Every bounded height increment contains finitely many strip zeros. -/
theorem stripZeroIncrement_finite (H U : ℝ) : (stripZeroIncrement H U).Finite := by
  refine (stripZeros_finite (U + 1)).subset ?_
  rintro ρ ⟨hre0, hre1, him0, himH, himU, hzero⟩
  exact ⟨⟨hre0, hre1, him0.le, lt_of_le_of_lt himU (lt_add_one U)⟩, hzero⟩

/-- The height increment is closed under critical-line reflection. -/
theorem lineReflect_mem_stripZeroIncrement {H U : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ stripZeroIncrement H U) : lineReflect ρ ∈ stripZeroIncrement H U := by
  obtain ⟨hre0, hre1, him0, himH, himU, hzero⟩ := hρ
  have him : (lineReflect ρ).im = ρ.im := by simp [lineReflect]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lineReflect_re]; linarith
  · rw [lineReflect_re]; linarith
  · rw [him]; exact him0
  · rw [him]; exact himH
  · rw [him]; exact himU
  · simp only [lineReflect]
    rw [xi_one_sub, xi_conj, hzero, map_zero]

/-- **A one-new-zero census amplifies a verified RH height.**  If RH is verified through `H` and
the full strip contains at most one distinct zero in `(H, U]`, then RH is verified through `U`.
An off-line zero cannot be that sole point: its distinct critical-line reflection lies at the same
positive ordinate and belongs to the same increment. -/
theorem rhVerifiedThrough_amplify_of_increment_ncard_le_one {H U : ℝ}
    (hH : RHVerifiedThrough H) (hcount : (stripZeroIncrement H U).ncard ≤ 1) :
    RHVerifiedThrough U := by
  intro ρ hzero hre0 hre1 him0 himU
  by_cases himH : ρ.im ≤ H
  · exact hH hzero hre0 hre1 him0 himH
  · have hρ : ρ ∈ stripZeroIncrement H U :=
      ⟨hre0, hre1, him0, lt_of_not_ge himH, himU, hzero⟩
    have hreflect : lineReflect ρ ∈ stripZeroIncrement H U :=
      lineReflect_mem_stripZeroIncrement hρ
    have heq : ρ = lineReflect ρ :=
      (Set.ncard_le_one_iff (stripZeroIncrement_finite H U)).mp hcount hρ hreflect
    have hre : ρ.re = (lineReflect ρ).re := congrArg Complex.re heq
    rw [lineReflect_re] at hre
    linarith

/-- New strip zeros within horizontal depth `a` of the critical line. -/
def centralStripZeroIncrement (a H U : ℝ) : Set ℂ :=
  {ρ ∈ stripZeroIncrement H U | |ρ.re - 1 / 2| < a}

/-- New strip zeros in the closed right wing of horizontal depth at least `a`. -/
def rightWingZeroIncrement (a H U : ℝ) : Set ℂ :=
  {ρ ∈ stripZeroIncrement H U | 1 / 2 + a ≤ ρ.re}

theorem centralStripZeroIncrement_finite (a H U : ℝ) :
    (centralStripZeroIncrement a H U).Finite :=
  (stripZeroIncrement_finite H U).subset fun _ hρ => hρ.1

/-- **Equivariant-collar height amplification.**  It is enough to certify at most one new zero in
the central band and no new zero in the right wing.  Reflection turns every left-wing zero into a
right-wing zero, while a central off-line zero would give two distinct central points. -/
theorem rhVerifiedThrough_amplify_of_equivariant_collar {a H U : ℝ}
    (hH : RHVerifiedThrough H)
    (hcentral : (centralStripZeroIncrement a H U).ncard ≤ 1)
    (hwing : rightWingZeroIncrement a H U = ∅) :
    RHVerifiedThrough U := by
  intro ρ hzero hre0 hre1 him0 himU
  by_cases himH : ρ.im ≤ H
  · exact hH hzero hre0 hre1 him0 himH
  · have hρinc : ρ ∈ stripZeroIncrement H U :=
      ⟨hre0, hre1, him0, lt_of_not_ge himH, himU, hzero⟩
    have noRight : ∀ {q : ℂ}, q ∈ stripZeroIncrement H U → 1 / 2 < q.re → False := by
      intro q hq hqright
      by_cases hdepth : q.re - 1 / 2 < a
      · have hqcentral : q ∈ centralStripZeroIncrement a H U := by
          refine ⟨hq, ?_⟩
          rw [abs_of_pos (by linarith)]
          exact hdepth
        have hreflectInc : lineReflect q ∈ stripZeroIncrement H U :=
          lineReflect_mem_stripZeroIncrement hq
        have hreflectCentral : lineReflect q ∈ centralStripZeroIncrement a H U := by
          refine ⟨hreflectInc, ?_⟩
          rw [lineReflect_re]
          have heq : 1 - q.re - 1 / 2 = -(q.re - 1 / 2) := by ring
          rw [heq, abs_neg, abs_of_pos (by linarith)]
          exact hdepth
        have hsame : q = lineReflect q :=
          (Set.ncard_le_one_iff (centralStripZeroIncrement_finite a H U)).mp
            hcentral hqcentral hreflectCentral
        have hre : q.re = (lineReflect q).re := congrArg Complex.re hsame
        rw [lineReflect_re] at hre
        linarith
      · have hqwing : q ∈ rightWingZeroIncrement a H U := by
          refine ⟨hq, ?_⟩
          linarith
        rw [hwing] at hqwing
        exact hqwing
    rcases lt_trichotomy ρ.re (1 / 2) with hleft | hon | hright
    · have hreflectInc : lineReflect ρ ∈ stripZeroIncrement H U :=
        lineReflect_mem_stripZeroIncrement hρinc
      exact (noRight hreflectInc (by
        rw [lineReflect_re]
        linarith)).elim
    · exact hon
    · exact (noRight hρinc hright).elim

end RHTower
