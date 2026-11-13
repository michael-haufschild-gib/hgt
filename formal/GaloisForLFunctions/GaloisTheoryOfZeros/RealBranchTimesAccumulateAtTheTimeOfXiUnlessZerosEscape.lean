import GaloisForLFunctions.GaloisTheoryOfZeros.AZeroContinuesAlongAPathOfTimesUntilItEscapes
import GaloisForLFunctions.GaloisTheoryOfZeros.TheCentreValueIsTheEquationOfTheSignBranchPoints
import GaloisForLFunctions.RHTower.DeBruijnNewmanNonnegative
import GaloisForLFunctions.RHTower.KiKimLeeFiniteness
import GaloisForLFunctions.RHTower.DeBruijnNewmanHalfBound

/-!
# Real branch times accumulate at the time of ξ unless zeros escape

The time `0` of the heat family is the function `Ξ`. At every negative real time the family has
infinitely many nonreal zeros, at every positive real time finitely many. This file turns the two
counts into a statement on the branch locus of the heat cover over the real times.

Let `a < 0 < b` and suppose that the segment `[a, b]` of real times contains no branch time.

* Conjugation maps a lift along the segment to a lift (`IsZeroLift.conj`). A lift that is real at
  one parameter meets its conjugate there, so the two start at the same zero: a nonreal zero stays
  nonreal (`IsZeroLift.im_ne_zero`).
* Transport along the segment is injective. So the nonreal zeros at time `a` that lift to time `b`
  inject into the finitely many nonreal zeros at time `b`, and all the others, infinitely many,
  escape before time `b` (`infinite_escapingNonrealZeros`).

Hence every real neighbourhood of the time `0` contains a branch time, or zeros escape along real
times arbitrarily close to `0` (`zero_mem_closure_real_branchTimes_or_escape`). A real branch time
is a collision away from the centre (`exists_multiple_zero_ne_zero_of_real_mem_branchTimes`).

A nonreal zero at a negative time that neither collides nor escapes before the time `0` arrives
at a zero of `ξ` off the line (`escapesAlong_or_exists_lift_to_nonreal_zero`). So under the Riemann
hypothesis, at every negative time `a`: a branch time lies in `[a, 0]`, or every nonreal zero of
`H_a` escapes before the time `0`
(`not_riemannHypothesis_or_exists_branchTime_or_forall_escapesAlong`,
`not_riemannHypothesis_or_zero_mem_closure_nonpos_branchTimes_or_escape`).
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Segments of real times -/

/-- The segment of real times from `a` to `b`, as a path of complex times. -/
def realSegment (a b : ℝ) (s : ℝ) : ℂ := ((a + s * (b - a) : ℝ) : ℂ)

theorem realSegment_zero (a b : ℝ) : realSegment a b 0 = a := by simp [realSegment]

theorem realSegment_one (a b : ℝ) : realSegment a b 1 = b := by simp [realSegment]

theorem continuous_realSegment (a b : ℝ) : Continuous (realSegment a b) :=
  Complex.continuous_ofReal.comp (continuous_const.add (continuous_id.mul continuous_const))

theorem realSegment_conj (a b s : ℝ) : starRingEnd ℂ (realSegment a b s) = realSegment a b s :=
  Complex.conj_ofReal _

theorem add_mul_sub_mem_Icc {a b s : ℝ} (hab : a ≤ b) (hs : s ∈ Icc (0 : ℝ) 1) :
    a + s * (b - a) ∈ Icc a b :=
  ⟨by linarith [mul_nonneg hs.1 (sub_nonneg.2 hab)],
    by linarith [mul_le_of_le_one_left (sub_nonneg.2 hab) hs.2]⟩

/-! ## Conjugation of lifts -/

/-- Along a path of real times the conjugate of a lift is a lift. -/
theorem IsZeroLift.conj {γ : ℝ → ℂ} {b : ℝ} {z : ℝ → ℂ}
    (hreal : ∀ s, starRingEnd ℂ (γ s) = γ s) (h : IsZeroLift γ b z) :
    IsZeroLift γ b fun s => starRingEnd ℂ (z s) :=
  ⟨Complex.continuous_conj.comp_continuousOn h.continuousOn, fun s hs => by
    have hc := complexHeat_conj (γ s) (z s)
    rw [h.zero s hs, map_zero, hreal] at hc
    exact hc.symm⟩

/-- **A nonreal zero stays nonreal.** Along a path of real times that avoids the branch times, a
lift that starts at a nonreal zero is nonreal at every parameter: where it is real it meets its
conjugate lift, and lifts that meet start at the same zero. -/
theorem IsZeroLift.im_ne_zero {γ : ℝ → ℂ} {z : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hreal : ∀ s, starRingEnd ℂ (γ s) = γ s)
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∉ branchTimes) (h : IsZeroLift γ 1 z)
    (h0 : (z 0).im ≠ 0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : (z s).im ≠ 0 := by
  intro him
  have hmeet : z s = starRingEnd ℂ (z s) := (Complex.conj_eq_iff_im.2 him).symm
  have h00 : z 0 = starRingEnd ℂ (z 0) := h.eq_zero_of_eq hγ hsimple (h.conj hreal) hs hmeet
  exact h0 (Complex.conj_eq_iff_im.1 h00.symm)

/-! ## The nonreal zeros between a negative and a positive time -/

/-- The nonreal zeros at the real time `a` that escape along the segment of real times to `b`. -/
def escapingNonrealZeros (a b : ℝ) : Set ℂ :=
  {z₀ | complexHeat a z₀ = 0 ∧ z₀.im ≠ 0 ∧ EscapesAlong (realSegment a b) z₀}

/-- **Without a real branch time the nonreal zeros escape.** If the segment of real times from
`a < 0` to `b > 0` contains no branch time, then infinitely many nonreal zeros of `H_a` escape along
it: those that lift inject into the finitely many nonreal zeros of `H_b`. -/
theorem infinite_escapingNonrealZeros {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hno : ∀ t ∈ Icc a b, (t : ℂ) ∉ branchTimes) : (escapingNonrealZeros a b).Infinite := by
  intro hfin
  have hγ : ContinuousOn (realSegment a b) (Icc 0 1) := (continuous_realSegment a b).continuousOn
  have hsimple : ∀ s ∈ Icc (0 : ℝ) 1, realSegment a b s ∉ branchTimes := fun s hs =>
    hno _ (add_mul_sub_mem_Icc (ha.trans hb).le hs)
  -- the nonreal zeros at the two ends
  have hN : {z : ℂ | complexHeat a z = 0 ∧ z.im ≠ 0}.Infinite := by
    have h := riemannHeat_neg_nonreal_zeros_infinite (τ := -a) (by linarith)
    rw [neg_neg] at h
    simpa only [complexHeat_ofReal] using h
  have hM : {z : ℂ | complexHeat b z = 0 ∧ z.im ≠ 0}.Finite := by
    simpa only [complexHeat_ofReal] using riemannHeat_nonreal_zeros_finite hb
  -- the nonreal zeros that do not escape lift to the time `b`
  have hrest := hN.sdiff hfin
  have hlift : ∀ z₀ ∈ {z : ℂ | complexHeat a z = 0 ∧ z.im ≠ 0} \ escapingNonrealZeros a b,
      ∃ z, IsZeroLift (realSegment a b) 1 z ∧ z 0 = z₀ := by
    rintro z₀ ⟨⟨hz, him⟩, hne⟩
    rcases exists_isZeroLift_or_escape hγ hsimple (z₀ := z₀)
      (by rw [realSegment_zero]; exact hz) with h | h
    · exact h
    · exact absurd ⟨hz, him, h⟩ hne
  classical
  let f : ℂ → ℂ := fun z₀ =>
    if h : ∃ z, IsZeroLift (realSegment a b) 1 z ∧ z 0 = z₀ then h.choose 1 else 0
  have hf : ∀ z₀ (h : ∃ z, IsZeroLift (realSegment a b) 1 z ∧ z 0 = z₀), f z₀ = h.choose 1 :=
    fun z₀ h => dif_pos h
  have hmaps : MapsTo f ({z : ℂ | complexHeat a z = 0 ∧ z.im ≠ 0} \ escapingNonrealZeros a b)
      {z : ℂ | complexHeat b z = 0 ∧ z.im ≠ 0} := by
    intro z₀ hz₀
    have h := hlift z₀ hz₀
    obtain ⟨hl, hl0⟩ := h.choose_spec
    have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have hzero := hl.zero 1 h1I
    rw [realSegment_one] at hzero
    rw [mem_setOf_eq, hf z₀ h]
    exact ⟨hzero, hl.im_ne_zero hγ (realSegment_conj a b) hsimple
      (by rw [hl0]; exact hz₀.1.2) h1I⟩
  -- two of them arrive at the same zero
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := hrest.exists_ne_map_eq_of_mapsTo hmaps hM
  have h₁ := hlift x hx
  have h₂ := hlift y hy
  rw [hf x h₁, hf y h₂] at hfxy
  have h00 := h₁.choose_spec.1.eq_zero_of_eq_one hγ hsimple h₂.choose_spec.1 hfxy
  rw [h₁.choose_spec.2, h₂.choose_spec.2] at h00
  exact hxy h00

/-- **A real branch time, or escape.** Between a negative and a positive real time there is a
branch time, or infinitely many nonreal zeros of the earlier time escape on the way. -/
theorem exists_real_branchTime_or_infinite_escaping {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    (∃ t ∈ Icc a b, (t : ℂ) ∈ branchTimes) ∨ (escapingNonrealZeros a b).Infinite := by
  by_cases h : ∃ t ∈ Icc a b, (t : ℂ) ∈ branchTimes
  · exact Or.inl h
  · exact Or.inr (infinite_escapingNonrealZeros ha hb fun t ht hbr => h ⟨t, ht, hbr⟩)

/-- A real branch time is a collision away from the centre. -/
theorem exists_multiple_zero_ne_zero_of_real_mem_branchTimes {t : ℝ}
    (h : (t : ℂ) ∈ branchTimes) :
    ∃ z : ℂ, z ≠ 0 ∧ complexHeat t z = 0 ∧ deriv (complexHeat t) z = 0 := by
  obtain ⟨⟨τ, z⟩, ⟨hz, hd⟩, hτ⟩ := h
  have hτ' : τ = (t : ℂ) := hτ
  subst hτ'
  refine ⟨z, ?_, hz, hd⟩
  rintro rfl
  exact im_ne_zero_of_complexHeat_center_eq_zero hz (Complex.ofReal_im t)

/-! ## The time of ξ -/

/-- **The time of ξ is a limit of real branch times, unless zeros escape.** Every real
neighbourhood of the time `0` contains a branch time of the heat cover, or there is `ε > 0` such
that along every segment of real times from `a ∈ (−ε, 0)` to `b ∈ (0, ε)` infinitely many nonreal
zeros escape. -/
theorem zero_mem_closure_real_branchTimes_or_escape :
    (0 : ℝ) ∈ closure {t : ℝ | (t : ℂ) ∈ branchTimes} ∨
      ∃ ε > 0, ∀ a b : ℝ, -ε < a → a < 0 → 0 < b → b < ε →
        (escapingNonrealZeros a b).Infinite := by
  by_cases h : (0 : ℝ) ∈ closure {t : ℝ | (t : ℂ) ∈ branchTimes}
  · exact Or.inl h
  right
  obtain ⟨ε, hε, hfree⟩ : ∃ ε > 0, ∀ t : ℝ, (t : ℂ) ∈ branchTimes → ε ≤ dist 0 t := by
    by_contra hcon
    refine h (Metric.mem_closure_iff.2 fun ε hε => ?_)
    by_contra hno
    exact hcon ⟨ε, hε, fun t ht => not_lt.1 fun hlt => hno ⟨t, ht, hlt⟩⟩
  refine ⟨ε, hε, fun a b ha ha0 hb0 hb =>
    infinite_escapingNonrealZeros ha0 hb0 fun t ht hbr => ?_⟩
  have h1 := hfree t hbr
  rw [Real.dist_eq, zero_sub, abs_neg] at h1
  have h2 : |t| < ε := abs_lt.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  linarith

/-! ## Arrival at the time of ξ -/

/-- **A nonreal zero at a negative time collides, escapes, or arrives at a zero of ξ off the
line.** If the segment of real times from `a < 0` to `0` contains no branch time, a nonreal zero
of `H_a` escapes along it or lifts to a nonreal zero of `H_0 = Ξ`. -/
theorem escapesAlong_or_exists_lift_to_nonreal_zero {a : ℝ} (ha : a < 0)
    (hno : ∀ t ∈ Icc a 0, (t : ℂ) ∉ branchTimes) {z₀ : ℂ} (hz : complexHeat a z₀ = 0)
    (him : z₀.im ≠ 0) :
    EscapesAlong (realSegment a 0) z₀ ∨
      ∃ z, IsZeroLift (realSegment a 0) 1 z ∧ z 0 = z₀ ∧
        riemannHeat 0 (z 1) = 0 ∧ (z 1).im ≠ 0 := by
  have hγ : ContinuousOn (realSegment a 0) (Icc 0 1) := (continuous_realSegment a 0).continuousOn
  have hsimple : ∀ s ∈ Icc (0 : ℝ) 1, realSegment a 0 s ∉ branchTimes := fun s hs =>
    hno _ (add_mul_sub_mem_Icc ha.le hs)
  rcases exists_isZeroLift_or_escape hγ hsimple (z₀ := z₀)
    (by rw [realSegment_zero]; exact hz) with ⟨z, hl, hl0⟩ | h
  · have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have hzero := hl.zero 1 h1I
    rw [realSegment_one, complexHeat_ofReal] at hzero
    exact Or.inr ⟨z, hl, hl0, hzero, hl.im_ne_zero hγ (realSegment_conj a 0) hsimple
      (by rw [hl0]; exact him) h1I⟩
  · exact Or.inl h

/-- **Three cases at every negative time.** The Riemann hypothesis fails; or between the time
`a < 0` and the time `0` there is a branch time; or every nonreal zero of `H_a` escapes before
the time `0`. -/
theorem not_riemannHypothesis_or_exists_branchTime_or_forall_escapesAlong {a : ℝ} (ha : a < 0) :
    ¬ RiemannHypothesis ∨ (∃ t ∈ Icc a 0, (t : ℂ) ∈ branchTimes) ∨
      ∀ z₀ : ℂ, complexHeat a z₀ = 0 → z₀.im ≠ 0 → EscapesAlong (realSegment a 0) z₀ := by
  by_cases hRH : RiemannHypothesis
  · right
    by_cases hbr : ∃ t ∈ Icc a 0, (t : ℂ) ∈ branchTimes
    · exact Or.inl hbr
    · refine Or.inr fun z₀ hz him => ?_
      rcases escapesAlong_or_exists_lift_to_nonreal_zero ha
        (fun t ht hmem => hbr ⟨t, ht, hmem⟩) hz him with h | ⟨z, -, -, hz1, him1⟩
      · exact h
      · exact absurd (riemannHypothesis_iff_riemannHeat_zero_real.1 hRH _ hz1) him1
  · exact Or.inl hRH

/-- **Three cases at the time of ξ.** The Riemann hypothesis fails; or the time `0` is a limit of
nonpositive real branch times (the time `0` itself, where `Ξ` would have a multiple zero, or
negative times); or there is `ε > 0` such that every nonreal zero at every time `a ∈ (−ε, 0)`
escapes before the time `0`. -/
theorem not_riemannHypothesis_or_zero_mem_closure_nonpos_branchTimes_or_escape :
    ¬ RiemannHypothesis ∨ (0 : ℝ) ∈ closure {t : ℝ | t ≤ 0 ∧ (t : ℂ) ∈ branchTimes} ∨
      ∃ ε > 0, ∀ a : ℝ, -ε < a → a < 0 → ∀ z₀ : ℂ, complexHeat a z₀ = 0 → z₀.im ≠ 0 →
        EscapesAlong (realSegment a 0) z₀ := by
  by_cases hRH : RiemannHypothesis
  · right
    by_cases h : (0 : ℝ) ∈ closure {t : ℝ | t ≤ 0 ∧ (t : ℂ) ∈ branchTimes}
    · exact Or.inl h
    right
    obtain ⟨ε, hε, hfree⟩ : ∃ ε > 0, ∀ t : ℝ, t ≤ 0 → (t : ℂ) ∈ branchTimes → ε ≤ dist 0 t := by
      by_contra hcon
      refine h (Metric.mem_closure_iff.2 fun ε hε => ?_)
      by_contra hno
      exact hcon ⟨ε, hε, fun t ht0 ht => not_lt.1 fun hlt => hno ⟨t, ⟨ht0, ht⟩, hlt⟩⟩
    refine ⟨ε, hε, fun a ha ha0 z₀ hz him => ?_⟩
    rcases not_riemannHypothesis_or_exists_branchTime_or_forall_escapesAlong ha0 with
      h1 | ⟨t, ht, hbr⟩ | h3
    · exact absurd hRH h1
    · have h1 := hfree t ht.2 hbr
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonpos ht.2] at h1
      linarith [ht.1]
    · exact h3 z₀ hz him
  · exact Or.inl hRH

end

end GaloisForLFunctions.GaloisTheoryOfZeros
