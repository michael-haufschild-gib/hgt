/-
The parity obstruction to completing a functional equation.

For a carrier presented in central normal form `F s = (s − 1/2)^m · G s` on the open critical
strip — `G` nonvanishing and symmetric under the reflection `s ↦ 1 − s` — the existence of a
completion, a strip-nonvanishing factor `γ` making `γ·F` reflection-symmetric, is decided by a
single bit, and the bit depends on how much regularity the completion is required to carry.

A bare set-theoretic completion always exists: away from the center the functional identity only
constrains the sign cocycle `γ (1 − s) = (−1)^m · γ s`, and a locally constant sign pattern over
the two half-strips and the two real half-lines realizes it, jumping across the reflection's
fixed axis.

A continuous completion exists exactly when the central order `m` is even.  For even `m` the
constant `1` completes, since the reflected central power `(1 − s − 1/2)^m = (−1)^m (s − 1/2)^m`
loses its sign.  For odd `m` the identity forces `γ (1 − s) = −γ s` off the center; approaching
the reflection's fixed point `1/2` along the real segment inside the strip, continuity gives
`γ (1/2) = −γ (1/2)`, so `γ (1/2) = 0`, contradicting nonvanishing.  The completability of a
divisor-symmetric carrier is thus read off the parity of its central order — the reflection's
fixed-point charge — and off no other data of the carrier.
-/
import Mathlib

noncomputable section

namespace RHTower

open Complex Filter Topology

/-- The open critical strip `0 < Re s < 1`. -/
def openStrip : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The strip is symmetric under the reflection `s ↦ 1 − s`. -/
theorem openStrip_reflect {s : ℂ} (hs : s ∈ openStrip) : (1 - s) ∈ openStrip := by
  obtain ⟨h0, h1⟩ := hs
  have hre : (1 - s).re = 1 - s.re := by simp [Complex.sub_re]
  exact ⟨by rw [hre]; linarith, by rw [hre]; linarith⟩

/-- The center `1/2` lies in the strip. -/
theorem openStrip_half : (1 / 2 : ℂ) ∈ openStrip := by
  have h : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  exact ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩

/-- **A bare completion always exists, whatever the central parity.**  The locally constant sign
pattern that is `1` on the upper half-strip and the right real half-line, and `(−1)^m` on the
lower half-strip and the left real half-line, is nonvanishing and satisfies the reflected sign
cocycle pointwise, so it completes the central normal form with no regularity at the fixed
point.  The functional-equation clause with an unconstrained completion factor therefore carries
no central-parity information. -/
theorem completion_raw_exists (m : ℕ) {G : ℂ → ℂ}
    (hGsym : ∀ s ∈ openStrip, G (1 - s) = G s) :
    ∃ γ : ℂ → ℂ, (∀ s ∈ openStrip, γ s ≠ 0) ∧
      ∀ s ∈ openStrip, γ (1 - s) * ((1 - s - 1/2) ^ m * G (1 - s))
        = γ s * ((s - 1/2) ^ m * G s) := by
  classical
  refine ⟨fun z => if 0 < z.im ∨ (z.im = 0 ∧ 1/2 ≤ z.re) then 1 else (-1) ^ m, ?_, ?_⟩
  all_goals
    have hval : ∀ z : ℂ, (fun z : ℂ =>
        if 0 < z.im ∨ (z.im = 0 ∧ 1/2 ≤ z.re) then (1 : ℂ) else (-1) ^ m) z
        = if 0 < z.im ∨ (z.im = 0 ∧ 1/2 ≤ z.re) then (1 : ℂ) else (-1) ^ m := fun z => rfl
  · intro s _
    rw [hval s]
    by_cases h : 0 < s.im ∨ (s.im = 0 ∧ 1/2 ≤ s.re)
    · rw [if_pos h]; norm_num
    · rw [if_neg h]
      exact pow_ne_zero m (by norm_num)
  · intro s hs
    have hpow : (1 - s - 1/2 : ℂ) ^ m = (-1) ^ m * (s - 1/2) ^ m := by
      rw [show (1 - s - 1/2 : ℂ) = -(s - 1/2) by ring, neg_pow]
    rw [hval s, hval (1 - s), hGsym s hs, hpow]
    have him : (1 - s).im = -s.im := by simp [Complex.sub_im]
    have hre : (1 - s).re = 1 - s.re := by simp [Complex.sub_re]
    rcases lt_trichotomy s.im 0 with hlt | heq | hgt
    · have h1 : ¬(0 < s.im ∨ (s.im = 0 ∧ 1/2 ≤ s.re)) := by
        rintro (h | ⟨h', -⟩)
        · linarith
        · linarith
      have h2 : 0 < (1 - s).im ∨ ((1 - s).im = 0 ∧ 1/2 ≤ (1 - s).re) :=
        Or.inl (by rw [him]; linarith)
      rw [if_neg h1, if_pos h2]
      ring
    · rcases le_or_gt (1/2 : ℝ) s.re with hge | hlt2
      · have h1 : 0 < s.im ∨ (s.im = 0 ∧ 1/2 ≤ s.re) := Or.inr ⟨heq, hge⟩
        rw [if_pos h1]
        rcases eq_or_lt_of_le hge with hcenter | hgt2
        · -- On the fixed point `s = 1/2` the central power kills both sides when `m ≥ 1`,
          -- and for `m = 0` both sign values sit on the closed right half-line and agree.
          have hs12 : s = 1/2 := by
            refine Complex.ext ?_ ?_
            · rw [show (1/2 : ℂ).re = 1/2 by norm_num]
              exact hcenter.symm
            · rw [show (1/2 : ℂ).im = 0 by norm_num]
              exact heq
          subst hs12
          rcases Nat.eq_zero_or_pos m with hm0 | hmpos
          · subst hm0
            have h2 : 0 < ((1 : ℂ) - 1/2).im ∨
                (((1 : ℂ) - 1/2).im = 0 ∧ 1/2 ≤ ((1 : ℂ) - 1/2).re) := by
              right
              refine ⟨by norm_num [Complex.sub_im], by norm_num [Complex.sub_re]⟩
            rw [if_pos h2]
            ring
          · have hz : ((1 : ℂ)/2 - 1/2) ^ m = 0 := by
              rw [show ((1 : ℂ)/2 - 1/2) = 0 by ring]
              exact zero_pow (by omega)
            rw [hz]
            ring
        · have h2 : ¬(0 < (1 - s).im ∨ ((1 - s).im = 0 ∧ 1/2 ≤ (1 - s).re)) := by
            rintro (h | ⟨-, h'⟩)
            · rw [him] at h; linarith
            · rw [hre] at h'; linarith
          rw [if_neg h2]
          have hsq : ((-1 : ℂ)) ^ m * (-1) ^ m = 1 := by
            rw [← pow_add]
            exact Even.neg_one_pow ⟨m, rfl⟩
          linear_combination ((s - 1/2) ^ m * G s) * hsq
      · have h1 : ¬(0 < s.im ∨ (s.im = 0 ∧ 1/2 ≤ s.re)) := by
          rintro (h | ⟨-, h'⟩)
          · linarith
          · linarith
        have h2 : 0 < (1 - s).im ∨ ((1 - s).im = 0 ∧ 1/2 ≤ (1 - s).re) := by
          right
          exact ⟨by rw [him]; linarith, by rw [hre]; linarith⟩
        rw [if_neg h1, if_pos h2]
        ring
    · have h1 : 0 < s.im ∨ (s.im = 0 ∧ 1/2 ≤ s.re) := Or.inl hgt
      have h2 : ¬(0 < (1 - s).im ∨ ((1 - s).im = 0 ∧ 1/2 ≤ (1 - s).re)) := by
        rintro (h | ⟨h', -⟩)
        · rw [him] at h; linarith
        · rw [him] at h'; linarith
      rw [if_pos h1, if_neg h2]
      have hsq : ((-1 : ℂ)) ^ m * (-1) ^ m = 1 := by
        rw [← pow_add]
        exact Even.neg_one_pow ⟨m, rfl⟩
      linear_combination ((s - 1/2) ^ m * G s) * hsq

/-- **A continuous completion exists exactly when the central order is even.**  Even `m`: the
constant `1` completes, since the reflected central power sheds its sign.  Odd `m`: off the
center the identity forces the sign cocycle `γ (1 − s) = −γ s`; approaching the reflection's
fixed point `1/2` along the real segment inside the strip, continuity of `γ` within the strip
gives `γ (1/2) = −γ (1/2)`, so `γ (1/2) = 0`, contradicting nonvanishing.  One bit of
fixed-point data decides completability, independently of the symmetric unit `G`. -/
theorem completion_continuousOn_iff_even_center {G : ℂ → ℂ}
    (hGne : ∀ s ∈ openStrip, G s ≠ 0) (hGsym : ∀ s ∈ openStrip, G (1 - s) = G s) (m : ℕ) :
    (∃ γ : ℂ → ℂ, ContinuousOn γ openStrip ∧ (∀ s ∈ openStrip, γ s ≠ 0) ∧
      ∀ s ∈ openStrip, γ (1 - s) * ((1 - s - 1/2) ^ m * G (1 - s))
        = γ s * ((s - 1/2) ^ m * G s)) ↔ Even m := by
  constructor
  · rintro ⟨γ, hγc, hγne, hγfe⟩
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    -- Off the center the identity forces the odd sign cocycle.
    have hsign : ∀ s ∈ openStrip, s ≠ 1/2 → γ (1 - s) = -γ s := by
      intro s hs hne
      have hfe := hγfe s hs
      have hflip : (1 - s - 1/2 : ℂ) ^ m = -((s - 1/2) ^ m) := by
        rw [show (1 - s - 1/2 : ℂ) = -(s - 1/2) by ring, neg_pow, hodd.neg_one_pow]
        ring
      rw [hGsym s hs, hflip] at hfe
      have hc : (s - 1/2 : ℂ) ^ m * G s ≠ 0 :=
        mul_ne_zero (pow_ne_zero m (sub_ne_zero.mpr hne)) (hGne s hs)
      have hfe' : (-γ (1 - s)) * ((s - 1/2) ^ m * G s) = γ s * ((s - 1/2) ^ m * G s) := by
        linear_combination hfe
      exact neg_eq_iff_eq_neg.mp (mul_right_cancel₀ hc hfe')
    -- The real approach sequence to the reflection's fixed point.
    set σ : ℕ → ℂ := fun n => ((1/2 + 1/(n+3) : ℝ) : ℂ) with hσdef
    have hσre : ∀ n : ℕ, (σ n).re = 1/2 + 1/((n : ℝ)+3) := fun n => Complex.ofReal_re _
    have hσmem : ∀ n : ℕ, σ n ∈ openStrip := by
      intro n
      have hpos : (0 : ℝ) < 1/((n : ℝ)+3) := by positivity
      have hle : (1 : ℝ)/((n : ℝ)+3) ≤ 1/3 :=
        one_div_le_one_div_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg n))
      exact ⟨by rw [hσre]; linarith, by rw [hσre]; linarith⟩
    have hσne : ∀ n, σ n ≠ 1/2 := by
      intro n h
      have hre := congrArg Complex.re h
      rw [hσre, show (1/2 : ℂ).re = 1/2 by norm_num] at hre
      have hpos : (0 : ℝ) < 1/((n : ℝ)+3) := by positivity
      linarith
    have hσtend : Tendsto σ atTop (𝓝 (1/2 : ℂ)) := by
      have h0 : Tendsto (fun n : ℕ => (1/((n : ℝ)+3))) atTop (𝓝 0) := by
        simp only [one_div]
        exact tendsto_inv_atTop_zero.comp
          ((tendsto_atTop_add_const_right _ 3 tendsto_id).comp tendsto_natCast_atTop_atTop)
      have hreal : Tendsto (fun n : ℕ => (1/2 + 1/((n : ℝ)+3))) atTop (𝓝 (1/2 : ℝ)) := by
        simpa using h0.const_add (1/2 : ℝ)
      have hcomp := (Complex.continuous_ofReal.tendsto (1/2 : ℝ)).comp hreal
      rw [show ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) by norm_num] at hcomp
      exact hcomp
    have hσtendW : Tendsto σ atTop (𝓝[openStrip] (1/2 : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within σ hσtend
        (Eventually.of_forall hσmem)
    have hσ'tendW : Tendsto (fun n => 1 - σ n) atTop (𝓝[openStrip] (1/2 : ℂ)) := by
      have htend : Tendsto (fun n => 1 - σ n) atTop (𝓝 (1/2 : ℂ)) := by
        have h := hσtend.const_sub (1 : ℂ)
        rwa [show (1 : ℂ) - 1/2 = 1/2 by norm_num] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend
        (Eventually.of_forall (fun n => openStrip_reflect (hσmem n)))
    have hγhalf : Tendsto γ (𝓝[openStrip] (1/2 : ℂ)) (𝓝 (γ (1/2))) :=
      hγc (1/2) openStrip_half
    have hL1 : Tendsto (fun n => γ (1 - σ n)) atTop (𝓝 (γ (1/2))) := hγhalf.comp hσ'tendW
    have hL2 : Tendsto (fun n => γ (σ n)) atTop (𝓝 (γ (1/2))) := hγhalf.comp hσtendW
    have hL1' : Tendsto (fun n => γ (1 - σ n)) atTop (𝓝 (-γ (1/2))) := by
      have hEq : (fun n => γ (1 - σ n)) = fun n => -γ (σ n) := by
        funext n
        exact hsign (σ n) (hσmem n) (hσne n)
      rw [hEq]
      exact hL2.neg
    have hcontra : γ (1/2 : ℂ) = -γ (1/2 : ℂ) := tendsto_nhds_unique hL1 hL1'
    have hzero : γ (1/2 : ℂ) = 0 := by
      have h2 : (2 : ℂ) * γ (1/2) = 0 := by linear_combination hcontra
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h two_ne_zero
      · exact h
    exact hγne (1/2) openStrip_half hzero
  · intro heven
    refine ⟨fun _ => 1, continuousOn_const, fun s _ => one_ne_zero, fun s hs => ?_⟩
    have hpow : (1 - s - 1/2 : ℂ) ^ m = (s - 1/2) ^ m := by
      rw [show (1 - s - 1/2 : ℂ) = -(s - 1/2) by ring, neg_pow, heven.neg_one_pow, one_mul]
    rw [hGsym s hs, hpow]

end RHTower
