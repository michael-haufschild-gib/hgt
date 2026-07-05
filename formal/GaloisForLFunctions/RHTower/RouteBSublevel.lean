/-
(L4)-seed: one-phase anti-concentration on the circle (doc 87 §4).

The first analytic small-ball brick of the (SMOOTH-LOW) architecture: the
angular sublevel set of a circle map is covered by two intervals of length
π·r/‖A‖, so its measure is ≤ 2·π·r/‖A‖ — the exponent-one anti-concentration
that the hierarchical Esseen (L3) consumes per phase.

* `norm_exp_I_sub_exp_I` — the chord identity ‖e^{ia} − e^{ib}‖ = 2|sin((a−b)/2)|.
* `chord_lower` — Jordan: (2/π)|a−b| ≤ ‖e^{ia} − e^{ib}‖ for |a−b| ≤ π.
* `sublevel_pair_close` — two sublevel angles within π are within π·r/‖A‖.
* `subset_two_intervals` — a set in [0, 2π] whose π-close pairs are D-close
  is covered by two intervals of length D.
* `arc_sublevel` — volume of the sublevel set ≤ 2·(π r/‖A‖).
-/
import Mathlib

namespace RHTower
namespace Sublevel

open Complex MeasureTheory

/-- `2i·sin z = e^{iz} − e^{−iz}`. -/
theorem two_I_sin (z : ℂ) :
    2 * Complex.I * Complex.sin z
      = Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I)) := by
  rw [Complex.sin]
  have h : (2 : ℂ) * Complex.I *
      ((Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I))
        * Complex.I / 2)
      = Complex.I ^ 2 *
        (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) := by
    ring
  rw [h, Complex.I_sq]
  have hneg : -z * Complex.I = -(z * Complex.I) := by ring
  rw [hneg]
  ring

/-- **The chord identity**: `‖e^{ia} − e^{ib}‖ = 2|sin((a−b)/2)|`. -/
theorem norm_exp_I_sub_exp_I (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖
      = 2 * |Real.sin ((a - b) / 2)| := by
  have hfac : Complex.exp ((a : ℂ) * Complex.I)
        - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((((a + b) / 2 : ℝ) : ℂ) * Complex.I)
        * (Complex.exp ((((a - b) / 2 : ℝ) : ℂ) * Complex.I)
          - Complex.exp (-((((a - b) / 2 : ℝ) : ℂ) * Complex.I))) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    · push_cast
      ring
    · push_cast
      ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← two_I_sin]
  rw [norm_mul, norm_mul, Complex.norm_I]
  have h2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  rw [h2, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- **Jordan lower bound for the chord**: for `|a − b| ≤ π`,
`(2/π)·|a − b| ≤ ‖e^{ia} − e^{ib}‖`. -/
theorem chord_lower {a b : ℝ} (h : |a - b| ≤ Real.pi) :
    2 / Real.pi * |a - b|
      ≤ ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ := by
  rw [norm_exp_I_sub_exp_I]
  have habs : |Real.sin ((a - b) / 2)| = Real.sin (|a - b| / 2) := by
    rcases le_or_gt 0 (a - b) with hpos | hneg
    · rw [abs_of_nonneg hpos, abs_of_nonneg]
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · linarith
      · rw [abs_of_nonneg hpos] at h
        linarith [Real.pi_pos]
    · have hs : (0 : ℝ) ≤ Real.sin (-((a - b) / 2)) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · linarith
        · rw [abs_of_neg hneg] at h
          linarith [Real.pi_pos]
      calc |Real.sin ((a - b) / 2)|
          = |Real.sin (-((a - b) / 2))| := by rw [Real.sin_neg, abs_neg]
        _ = Real.sin (-((a - b) / 2)) := abs_of_nonneg hs
        _ = Real.sin (|a - b| / 2) := by rw [abs_of_neg hneg]; ring_nf
  rw [habs]
  have hj : 2 / Real.pi * (|a - b| / 2) ≤ Real.sin (|a - b| / 2) :=
    Real.mul_le_sin (by positivity) (by linarith [abs_nonneg (a - b)])
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [hj]

/-- Two sublevel angles within `π` of each other are within `π·r/‖A‖`. -/
theorem sublevel_pair_close {A c : ℂ} {r : ℝ} (hA : A ≠ 0)
    {x y : ℝ}
    (hx : ‖c + A * Complex.exp ((x : ℂ) * Complex.I)‖ ≤ r)
    (hy : ‖c + A * Complex.exp ((y : ℂ) * Complex.I)‖ ≤ r)
    (hxy : |x - y| ≤ Real.pi) :
    |x - y| ≤ Real.pi * r / ‖A‖ := by
  have hApos : (0 : ℝ) < ‖A‖ := norm_pos_iff.mpr hA
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hchord : ‖A‖ * ‖Complex.exp ((x : ℂ) * Complex.I)
      - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ 2 * r := by
    rw [← norm_mul, mul_sub]
    have hdiff : A * Complex.exp ((x : ℂ) * Complex.I)
        - A * Complex.exp ((y : ℂ) * Complex.I)
        = (c + A * Complex.exp ((x : ℂ) * Complex.I))
          - (c + A * Complex.exp ((y : ℂ) * Complex.I)) := by ring
    rw [hdiff]
    calc ‖(c + A * Complex.exp ((x : ℂ) * Complex.I))
          - (c + A * Complex.exp ((y : ℂ) * Complex.I))‖
        ≤ ‖c + A * Complex.exp ((x : ℂ) * Complex.I)‖
          + ‖c + A * Complex.exp ((y : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith
  have hlow := chord_lower hxy
  have h1 : 2 / Real.pi * |x - y| * ‖A‖ ≤ 2 * r := by
    calc 2 / Real.pi * |x - y| * ‖A‖
        ≤ ‖Complex.exp ((x : ℂ) * Complex.I)
            - Complex.exp ((y : ℂ) * Complex.I)‖ * ‖A‖ :=
          mul_le_mul_of_nonneg_right hlow (le_of_lt hApos)
      _ = ‖A‖ * ‖Complex.exp ((x : ℂ) * Complex.I)
            - Complex.exp ((y : ℂ) * Complex.I)‖ := by ring
      _ ≤ 2 * r := hchord
  have h2 : 2 * |x - y| * ‖A‖ ≤ 2 * r * Real.pi := by
    have h3 := mul_le_mul_of_nonneg_right h1 (le_of_lt hπ)
    calc 2 * |x - y| * ‖A‖
        = 2 / Real.pi * |x - y| * ‖A‖ * Real.pi := by
          field_simp
      _ ≤ 2 * r * Real.pi := h3
  rw [le_div_iff₀ hApos]
  nlinarith [h2]

/-- A subset of `[0, 2π]` in which every π-close pair is D-close is covered
by two intervals of length `D`. -/
theorem subset_two_intervals {S : Set ℝ} {D : ℝ}
    (hS : S ⊆ Set.Icc 0 (2 * Real.pi))
    (hclose : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ Real.pi → |x - y| ≤ D) :
    ∃ a b : ℝ, S ⊆ Set.Icc a (a + D) ∪ Set.Icc b (b + D) := by
  classical
  rcases Set.eq_empty_or_nonempty S with rfl | hne
  · exact ⟨0, 0, by simp⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => (hS hx).1⟩
  set a := sInf S with ha
  have haS : ∀ x ∈ S, a ≤ x := fun x hx => csInf_le hbdd hx
  have ha0 : 0 ≤ a := le_csInf hne fun x hx => (hS hx).1
  have hnear : ∀ x ∈ S, x ≤ a + Real.pi → x ≤ a + D := by
    intro x hxS hxpi
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hεπ : 0 < min ε Real.pi := lt_min hε Real.pi_pos
    obtain ⟨a', ha'S, ha'lt⟩ := exists_lt_of_csInf_lt hne
      (lt_add_of_pos_right a hεπ)
    have ha'ge : a ≤ a' := haS a' ha'S
    have hd1 : |x - a'| ≤ Real.pi := by
      rw [abs_le]
      constructor
      · have hx0 : a ≤ x := haS x hxS
        have hmin : min ε Real.pi ≤ Real.pi := min_le_right _ _
        linarith
      · linarith
    have hd2 := hclose x hxS a' ha'S hd1
    have hd3 : x - a' ≤ D := le_trans (le_abs_self _) hd2
    have hmin : min ε Real.pi ≤ ε := min_le_left _ _
    linarith
  set T := S ∩ Set.Icc (a + Real.pi) (2 * Real.pi) with hT
  rcases Set.eq_empty_or_nonempty T with hTe | hTne
  · refine ⟨a, a, fun x hxS => Or.inl ?_⟩
    have hxa : a ≤ x := haS x hxS
    have hxpi : x ≤ a + Real.pi := by
      by_contra hgt
      have hmem : x ∈ T := ⟨hxS, ⟨by linarith, (hS hxS).2⟩⟩
      rw [hTe] at hmem
      exact hmem
    exact ⟨hxa, hnear x hxS hxpi⟩
  · have hbddT : BddBelow T := ⟨0, fun x hx => (hS hx.1).1⟩
    set b := sInf T with hb
    have hbT : ∀ y ∈ T, b ≤ y := fun y hy => csInf_le hbddT hy
    have hfar : ∀ y ∈ T, y ≤ b + D := by
      intro y hyT
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨b', hb'T, hb'lt⟩ := exists_lt_of_csInf_lt hTne
        (lt_add_of_pos_right b hε)
      have hb'ge : b ≤ b' := hbT b' hb'T
      have hy1 : a + Real.pi ≤ y := hyT.2.1
      have hy2 : y ≤ 2 * Real.pi := hyT.2.2
      have hb'1 : a + Real.pi ≤ b' := hb'T.2.1
      have hb'2 : b' ≤ 2 * Real.pi := hb'T.2.2
      have hwin : |y - b'| ≤ Real.pi := by
        rw [abs_le]
        constructor
        · linarith
        · linarith
      have hd2 := hclose y hyT.1 b' hb'T.1 hwin
      have hd3 : y - b' ≤ D := le_trans (le_abs_self _) hd2
      linarith
    refine ⟨a, b, fun x hxS => ?_⟩
    rcases le_or_gt x (a + Real.pi) with hle | hgt
    · exact Or.inl ⟨haS x hxS, hnear x hxS hle⟩
    · have hxT : x ∈ T := ⟨hxS, ⟨le_of_lt hgt, (hS hxS).2⟩⟩
      exact Or.inr ⟨hbT x hxT, hfar x hxT⟩

/-- **(L4)-seed: one-phase anti-concentration.**  The angular sublevel set of
a circle map has measure at most `2·(π r/‖A‖)`. -/
theorem arc_sublevel {A c : ℂ} {r : ℝ} (hA : A ≠ 0) (hr : 0 ≤ r) :
    volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖c + A * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ r}
      ≤ ENNReal.ofReal (2 * (Real.pi * r / ‖A‖)) := by
  have hApos : (0 : ℝ) < ‖A‖ := norm_pos_iff.mpr hA
  have hD : (0 : ℝ) ≤ Real.pi * r / ‖A‖ := by positivity
  obtain ⟨a, b, hab⟩ := subset_two_intervals
    (S := {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖c + A * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ r})
    (D := Real.pi * r / ‖A‖)
    (fun θ hθ => by exact hθ.1)
    (fun x hx y hy hxy => by exact sublevel_pair_close hA hx.2 hy.2 hxy)
  calc volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖c + A * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ r}
      ≤ volume (Set.Icc a (a + Real.pi * r / ‖A‖)
          ∪ Set.Icc b (b + Real.pi * r / ‖A‖)) := measure_mono hab
    _ ≤ volume (Set.Icc a (a + Real.pi * r / ‖A‖))
        + volume (Set.Icc b (b + Real.pi * r / ‖A‖)) := measure_union_le _ _
    _ = ENNReal.ofReal (Real.pi * r / ‖A‖)
        + ENNReal.ofReal (Real.pi * r / ‖A‖) := by
        rw [Real.volume_Icc, Real.volume_Icc]
        congr 1 <;> ring_nf
    _ ≤ ENNReal.ofReal (2 * (Real.pi * r / ‖A‖)) := by
        rw [← ENNReal.ofReal_add hD hD]
        apply ENNReal.ofReal_le_ofReal
        ring_nf
        rfl

end Sublevel
end RHTower

namespace RHTower
namespace Sublevel

open Complex MeasureTheory

/-- **Two-phase Fubini composition.**  The 2D sublevel measure of a two-phase
circle sum factors through the per-phase arc bound times the measure of the
CAUSTIC set (angles where the second arm lands within `r` of the first
circle's radius).  This isolates exactly the caustic factor that the
hierarchical Esseen (L3) must average out; away from the caustic the section
is EMPTY (reverse triangle inequality). -/
theorem two_phase_sublevel {A B c : ℂ} {r : ℝ} (hA : A ≠ 0) (hr : 0 ≤ r) :
    (volume.prod volume)
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
        {p : ℝ × ℝ | ‖c + B * Complex.exp ((p.1 : ℂ) * Complex.I)
            + A * Complex.exp ((p.2 : ℂ) * Complex.I)‖ ≤ r})
      ≤ ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))
        * volume {φ : ℝ | φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
            |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ‖A‖| ≤ r} := by
  classical
  set S : Set (ℝ × ℝ) :=
    (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
      {p : ℝ × ℝ | ‖c + B * Complex.exp ((p.1 : ℂ) * Complex.I)
          + A * Complex.exp ((p.2 : ℂ) * Complex.I)‖ ≤ r} with hS
  set K : Set ℝ := {φ : ℝ | φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
      |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ‖A‖| ≤ r} with hK
  have hcont2 : Continuous fun p : ℝ × ℝ =>
      ‖c + B * Complex.exp ((p.1 : ℂ) * Complex.I)
        + A * Complex.exp ((p.2 : ℂ) * Complex.I)‖ := by
    apply Continuous.norm
    apply Continuous.add
    · apply Continuous.add continuous_const
      exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hcont1 : Continuous fun φ : ℝ =>
      |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ‖A‖| := by
    apply Continuous.abs
    apply Continuous.sub _ continuous_const
    apply Continuous.norm
    exact continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal).mul continuous_const)))
  have hSm : MeasurableSet S := by
    apply IsClosed.measurableSet
    exact (isClosed_Icc.prod isClosed_Icc).inter
      (isClosed_le hcont2 continuous_const)
  have hKm : MeasurableSet K := by
    apply IsClosed.measurableSet
    have : K = Set.Icc (0 : ℝ) (2 * Real.pi)
        ∩ {φ : ℝ | |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ‖A‖| ≤ r} := rfl
    rw [this]
    exact isClosed_Icc.inter (isClosed_le hcont1 continuous_const)
  rw [Measure.prod_apply hSm]
  have hsec : ∀ φ : ℝ, volume (Prod.mk φ ⁻¹' S)
      ≤ K.indicator (fun _ => ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))) φ := by
    intro φ
    by_cases hφ : φ ∈ K
    · rw [Set.indicator_of_mem hφ]
      refine le_trans (measure_mono ?_)
        (arc_sublevel (c := c + B * Complex.exp ((φ : ℂ) * Complex.I)) hA hr)
      intro θ hθ
      exact ⟨hθ.1.2, hθ.2⟩
    · rw [Set.indicator_of_notMem hφ]
      have hempty : Prod.mk φ ⁻¹' S = ∅ := by
        ext θ
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨hφI, _⟩, hnorm⟩
        apply hφ
        refine ⟨hφI, ?_⟩
        have htri := abs_norm_sub_norm_le
          (c + B * Complex.exp ((φ : ℂ) * Complex.I))
          (-(A * Complex.exp ((θ : ℂ) * Complex.I)))
        rw [sub_neg_eq_add, norm_neg, norm_mul,
          Complex.norm_exp_ofReal_mul_I, mul_one] at htri
        exact le_trans htri hnorm
      rw [hempty, measure_empty]
  calc ∫⁻ φ, volume (Prod.mk φ ⁻¹' S)
      ≤ ∫⁻ φ, K.indicator
          (fun _ => ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))) φ :=
        lintegral_mono hsec
    _ = ∫⁻ _ in K, ENNReal.ofReal (2 * (Real.pi * r / ‖A‖)) :=
        lintegral_indicator hKm _
    _ = ENNReal.ofReal (2 * (Real.pi * r / ‖A‖)) * volume K :=
        setLIntegral_const K _

end Sublevel
end RHTower

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- **The arccos-gap inequality (double Jordan)**: for `−1 ≤ u₁ ≤ u₂ ≤ 1`,
`(arccos u₁ − arccos u₂)² ≤ (π²/2)(u₂ − u₁)`.  The √-law behind the caustic
band: `u₂ − u₁ = 2 sin(mean)·sin(half-gap)` and BOTH factors admit the
Jordan lower bound `(2/π)·(half-gap)` — the mean is at least the half-gap
away from both endpoints of `[0, π]`. -/
theorem arccos_gap_sq {u₁ u₂ : ℝ} (h1 : -1 ≤ u₁) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ 1) :
    (Real.arccos u₁ - Real.arccos u₂) ^ 2 ≤ Real.pi ^ 2 / 2 * (u₂ - u₁) := by
  set θ₁ := Real.arccos u₂ with hθ₁
  set θ₂ := Real.arccos u₁ with hθ₂
  have hθ₁0 : 0 ≤ θ₁ := Real.arccos_nonneg _
  have hθ₂0 : 0 ≤ θ₂ := Real.arccos_nonneg _
  have hθ₁π : θ₁ ≤ Real.pi := Real.arccos_le_pi _
  have hθ₂π : θ₂ ≤ Real.pi := Real.arccos_le_pi _
  have hcosθ₁ : Real.cos θ₁ = u₂ := Real.cos_arccos (by linarith) h2
  have hcosθ₂ : Real.cos θ₂ = u₁ := Real.cos_arccos h1 (by linarith)
  have hθ₁2 : θ₁ ≤ θ₂ := by
    by_contra hlt
    push Not at hlt
    have := Real.strictAntiOn_cos ⟨hθ₂0, hθ₂π⟩ ⟨hθ₁0, hθ₁π⟩ hlt
    rw [hcosθ₁, hcosθ₂] at this
    linarith
  set L := θ₂ - θ₁ with hLdef
  have hL0 : 0 ≤ L := by simp [hLdef]; linarith
  have hLπ : L ≤ Real.pi := by simp [hLdef]; linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hdiff : u₂ - u₁ = 2 * Real.sin ((θ₁ + θ₂) / 2) * Real.sin (L / 2) := by
    rw [← hcosθ₁, ← hcosθ₂, Real.cos_sub_cos]
    rw [show (θ₁ - θ₂) / 2 = -(L / 2) by rw [hLdef]; ring, Real.sin_neg]
    ring
  have hs1 : 2 / Real.pi * (L / 2) ≤ Real.sin (L / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have hs2 : 2 / Real.pi * (L / 2) ≤ Real.sin ((θ₁ + θ₂) / 2) := by
    rcases le_or_gt ((θ₁ + θ₂) / 2) (Real.pi / 2) with hm | hm
    · calc 2 / Real.pi * (L / 2) ≤ 2 / Real.pi * ((θ₁ + θ₂) / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [hLdef]
            linarith
        _ ≤ Real.sin ((θ₁ + θ₂) / 2) := Real.mul_le_sin (by linarith) hm
    · have hflip : Real.sin ((θ₁ + θ₂) / 2)
          = Real.sin (Real.pi - (θ₁ + θ₂) / 2) := (Real.sin_pi_sub _).symm
      rw [hflip]
      calc 2 / Real.pi * (L / 2)
          ≤ 2 / Real.pi * (Real.pi - (θ₁ + θ₂) / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [hLdef]
            linarith
        _ ≤ Real.sin (Real.pi - (θ₁ + θ₂) / 2) :=
            Real.mul_le_sin (by linarith) (by linarith)
  have hs1n : (0 : ℝ) ≤ 2 / Real.pi * (L / 2) := by positivity
  have hprod : (2 / Real.pi * (L / 2)) * (2 / Real.pi * (L / 2))
      ≤ Real.sin ((θ₁ + θ₂) / 2) * Real.sin (L / 2) :=
    mul_le_mul hs2 hs1 hs1n (by linarith)
  have hprod2 : L ^ 2 ≤ Real.pi ^ 2 *
      (Real.sin ((θ₁ + θ₂) / 2) * Real.sin (L / 2)) := by
    have hstep : L ^ 2 = Real.pi ^ 2 *
        ((2 / Real.pi * (L / 2)) * (2 / Real.pi * (L / 2))) := by
      field_simp
    rw [hstep]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  have hgap : L ^ 2 ≤ Real.pi ^ 2 / 2 * (u₂ - u₁) := by
    rw [hdiff]
    calc L ^ 2
        ≤ Real.pi ^ 2 * (Real.sin ((θ₁ + θ₂) / 2) * Real.sin (L / 2)) := hprod2
      _ = Real.pi ^ 2 / 2 * (2 * Real.sin ((θ₁ + θ₂) / 2) * Real.sin (L / 2)) := by
          ring
  calc (Real.arccos u₁ - Real.arccos u₂) ^ 2 = L ^ 2 := rfl
    _ ≤ Real.pi ^ 2 / 2 * (u₂ - u₁) := hgap

/-- **(CAUSTIC-cos): the cosine-band measure √-law.**  The set of angles in
`[0, 2π]` whose cosine lies in a band of width `δ` has measure at most
`π·√(2δ)` — the unconditional (tangency-worst-case) caustic bound. -/
theorem cos_band_measure {u₁ u₂ : ℝ} (h1 : -1 ≤ u₁) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ 1) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        Real.cos φ ∈ Set.Icc u₁ u₂}
      ≤ ENNReal.ofReal (Real.pi * Real.sqrt (2 * (u₂ - u₁))) := by
  set θ₁ := Real.arccos u₂ with hθ₁
  set θ₂ := Real.arccos u₁ with hθ₂
  have hθ₁0 : 0 ≤ θ₁ := Real.arccos_nonneg _
  have hθ₂0 : 0 ≤ θ₂ := Real.arccos_nonneg _
  have hθ₁π : θ₁ ≤ Real.pi := Real.arccos_le_pi _
  have hθ₂π : θ₂ ≤ Real.pi := Real.arccos_le_pi _
  have hcosθ₁ : Real.cos θ₁ = u₂ := Real.cos_arccos (by linarith) h2
  have hcosθ₂ : Real.cos θ₂ = u₁ := Real.cos_arccos h1 (by linarith)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcover : {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        Real.cos φ ∈ Set.Icc u₁ u₂}
      ⊆ Set.Icc θ₁ θ₂ ∪ Set.Icc (2 * Real.pi - θ₂) (2 * Real.pi - θ₁) := by
    rintro φ ⟨⟨hφ0, hφ2π⟩, hc1, hc2⟩
    rcases le_or_gt φ Real.pi with hle | hgt
    · left
      constructor
      · by_contra hlt
        push Not at hlt
        have := Real.strictAntiOn_cos ⟨hφ0, hle⟩ ⟨hθ₁0, hθ₁π⟩ hlt
        rw [hcosθ₁] at this
        linarith
      · by_contra hlt
        push Not at hlt
        have := Real.strictAntiOn_cos ⟨hθ₂0, hθ₂π⟩ ⟨hφ0, hle⟩ hlt
        rw [hcosθ₂] at this
        linarith
    · right
      have hψ0 : 0 ≤ 2 * Real.pi - φ := by linarith
      have hψπ : 2 * Real.pi - φ ≤ Real.pi := by linarith
      have hψcos : Real.cos (2 * Real.pi - φ) = Real.cos φ :=
        Real.cos_two_pi_sub φ
      have hlow : θ₁ ≤ 2 * Real.pi - φ := by
        by_contra hlt
        push Not at hlt
        have := Real.strictAntiOn_cos ⟨hψ0, hψπ⟩ ⟨hθ₁0, hθ₁π⟩ hlt
        rw [hcosθ₁, hψcos] at this
        linarith
      have hhigh : 2 * Real.pi - φ ≤ θ₂ := by
        by_contra hlt
        push Not at hlt
        have := Real.strictAntiOn_cos ⟨hθ₂0, hθ₂π⟩ ⟨hψ0, hψπ⟩ hlt
        rw [hcosθ₂, hψcos] at this
        linarith
      exact ⟨by linarith, by linarith⟩
  have hgap := arccos_gap_sq h1 h12 h2
  have hL0 : 0 ≤ θ₂ - θ₁ := by
    by_contra hlt
    push Not at hlt
    have := Real.strictAntiOn_cos ⟨hθ₂0, hθ₂π⟩ ⟨hθ₁0, hθ₁π⟩
      (by linarith : θ₂ < θ₁)
    rw [hcosθ₁, hcosθ₂] at this
    linarith
  have h2L : 2 * (θ₂ - θ₁) ≤ Real.pi * Real.sqrt (2 * (u₂ - u₁)) := by
    have hLs : θ₂ - θ₁ ≤ Real.sqrt (Real.pi ^ 2 / 2 * (u₂ - u₁)) := by
      rw [Real.le_sqrt hL0 (by nlinarith)]
      exact hgap
    have hfact : Real.pi ^ 2 / 2 * (u₂ - u₁)
        = (Real.pi / 2) ^ 2 * (2 * (u₂ - u₁)) := by ring
    rw [hfact, Real.sqrt_mul (by positivity) _,
      Real.sqrt_sq (by positivity)] at hLs
    linarith
  calc volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        Real.cos φ ∈ Set.Icc u₁ u₂}
      ≤ volume (Set.Icc θ₁ θ₂
          ∪ Set.Icc (2 * Real.pi - θ₂) (2 * Real.pi - θ₁)) :=
        measure_mono hcover
    _ ≤ volume (Set.Icc θ₁ θ₂)
        + volume (Set.Icc (2 * Real.pi - θ₂) (2 * Real.pi - θ₁)) :=
        measure_union_le _ _
    _ = ENNReal.ofReal (θ₂ - θ₁) + ENNReal.ofReal (θ₂ - θ₁) := by
        rw [Real.volume_Icc, Real.volume_Icc]
        congr 1
        ring_nf
    _ ≤ ENNReal.ofReal (Real.pi * Real.sqrt (2 * (u₂ - u₁))) := by
        rw [← ENNReal.ofReal_add hL0 hL0]
        apply ENNReal.ofReal_le_ofReal
        linarith

end Sublevel
end RHTower
