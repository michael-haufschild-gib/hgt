import Mathlib

/-!
# Fifth-root divided-drop wall

Convexity of the fifth root of a divided drop is not merely a qualitative shape law.  At
the three squared scales `x`, `4x`, and `9x`, it forces the exact rank-four odd/Ptolemy wall.
The exponent five is certified by a positive factorization with a triple endpoint zero.
-/

namespace HilbertMetric

open Set

/-- Concave scaling of a correlation angle forces antitonicity of its squared-variable divided
cosine drop.  This is the continuum form of the `1,4,9` normalization used by the wall. -/
theorem cosineDividedDrop_antitone_of_angleScaling
    {s t x y : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxpi : x ≤ Real.pi / 2) (hypi : y ≤ Real.pi / 2)
    (hscale : (s / t) * y ≤ x) :
    (1 - Real.cos y) / t ^ (2 : ℕ) ≤ (1 - Real.cos x) / s ^ (2 : ℕ) := by
  have ht : 0 < t := hs.trans_le hst
  let r : ℝ := s / t
  have hr0 : 0 ≤ r := div_nonneg hs.le ht.le
  have hr1 : r ≤ 1 := (div_le_one ht).2 hst
  have hyhalf0 : 0 ≤ y / 2 := by linarith
  have hyhalfpi : y / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hconc : r * Real.sin (y / 2) ≤ Real.sin (r * (y / 2)) := by
    have h := strictConcaveOn_sin_Icc.concaveOn.2
      (show (0 : ℝ) ∈ Icc 0 Real.pi by simp [Real.pi_pos.le])
      (show y / 2 ∈ Icc 0 Real.pi from ⟨hyhalf0, hyhalfpi⟩)
      (sub_nonneg.mpr hr1) hr0
      (show (1 - r) + r = 1 by ring)
    norm_num [smul_eq_mul] at h ⊢
    exact h
  have hmono : Real.sin (r * (y / 2)) ≤ Real.sin (x / 2) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · have : 0 ≤ r * (y / 2) := mul_nonneg hr0 hyhalf0
      linarith [Real.pi_pos]
    · linarith
    · nlinarith [hscale]
  have hstsin : s * Real.sin (y / 2) ≤ t * Real.sin (x / 2) := by
    have hsin : r * Real.sin (y / 2) ≤ Real.sin (x / 2) := hconc.trans hmono
    dsimp [r] at hsin
    have h := mul_le_mul_of_nonneg_left hsin ht.le
    field_simp [ht.ne'] at h
    nlinarith
  have hleft0 : 0 ≤ s * Real.sin (y / 2) := by
    exact mul_nonneg hs.le (Real.sin_nonneg_of_nonneg_of_le_pi hyhalf0 hyhalfpi)
  have hsquare := pow_le_pow_left₀ hleft0 hstsin 2
  rw [show 1 - Real.cos y = 2 * Real.sin (y / 2) ^ (2 : ℕ) by
      rw [Real.sin_sq_eq_half_sub]; ring,
    show 1 - Real.cos x = 2 * Real.sin (x / 2) ^ (2 : ℕ) by
      rw [Real.sin_sq_eq_half_sub]; ring,
    div_le_div_iff₀ (sq_pos_of_pos ht) (sq_pos_of_pos hs)]
  nlinarith

/-- Positive factorization behind the fifth-root divided-drop wall. -/
theorem weighted_fifth_power_wall {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (5 + 3 * y ^ (2 : ℕ)) ^ (5 : ℕ) ≤ 8192 * (1 + 3 * y ^ (5 : ℕ)) := by
  have hid :
      8192 * (1 + 3 * y ^ (5 : ℕ)) - (5 + 3 * y ^ (2 : ℕ)) ^ (5 : ℕ) =
        (1 - y) ^ (3 : ℕ) *
          (243 * y ^ (7 : ℕ) + 729 * y ^ (6 : ℕ) + 3483 * y ^ (5 : ℕ) +
            8505 * y ^ (4 : ℕ) + 22545 * y ^ (3 : ℕ) + 21027 * y ^ (2 : ℕ) +
            15201 * y + 5067) := by
    ring
  rw [← sub_nonneg, hid]
  positivity

/-- A decreasing convex chord of nonnegative fifth roots forces the associated odd wall.
Here `a`, `b`, and `c` are values at squared scales `x`, `4x`, and `9x`; the last premise
is monotonicity of the underlying, unnormalized two-step drop. -/
theorem fifthRootConvexChord_forces_wall
    {a b c : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hca : c ≤ a)
    (hconv : 8 * b ≤ 5 * a + 3 * c)
    (hdrop : a ^ (5 : ℕ) ≤ 4 * b ^ (5 : ℕ)) :
    (4 * b ^ (5 : ℕ) - a ^ (5 : ℕ)) ^ (2 : ℕ) ≤ 9 * a ^ (5 : ℕ) * c ^ (5 : ℕ) := by
  let y : ℝ := Real.sqrt (c / a)
  have hquot : 0 ≤ c / a := div_nonneg hc ha.le
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y ^ (2 : ℕ) = c / a := by
    simpa only [y] using Real.sq_sqrt hquot
  have hay : a * y ^ (2 : ℕ) = c := by
    rw [hy2]
    field_simp
  have hy1 : y ≤ 1 := by
    rw [← sq_le_sq₀ hy0 (by norm_num : (0 : ℝ) ≤ 1), hy2]
    simpa using (div_le_one ha).2 hca
  have hconv' : 8 * b ≤ a * (5 + 3 * y ^ (2 : ℕ)) := by
    nlinarith
  have hM : 0 ≤ 5 + 3 * y ^ (2 : ℕ) := by positivity
  have hleft : 0 ≤ 8 * b := by positivity
  have hpow := pow_le_pow_left₀ hleft hconv' 5
  have hscalar := weighted_fifth_power_wall hy0 hy1
  have ha5 : 0 ≤ a ^ (5 : ℕ) := by positivity
  have hscaled : 32768 * b ^ (5 : ℕ) ≤
      8192 * (a ^ (5 : ℕ) * (1 + 3 * y ^ (5 : ℕ))) := by
    calc
      32768 * b ^ (5 : ℕ) = (8 * b) ^ (5 : ℕ) := by ring
      _ ≤ (a * (5 + 3 * y ^ (2 : ℕ))) ^ (5 : ℕ) := hpow
      _ = a ^ (5 : ℕ) * (5 + 3 * y ^ (2 : ℕ)) ^ (5 : ℕ) := by ring
      _ ≤ a ^ (5 : ℕ) * (8192 * (1 + 3 * y ^ (5 : ℕ))) :=
        mul_le_mul_of_nonneg_left hscalar ha5
      _ = 8192 * (a ^ (5 : ℕ) * (1 + 3 * y ^ (5 : ℕ))) := by ring
  have hupper : 4 * b ^ (5 : ℕ) ≤ a ^ (5 : ℕ) * (1 + 3 * y ^ (5 : ℕ)) := by
    nlinarith
  have hgap0 : 0 ≤ 4 * b ^ (5 : ℕ) - a ^ (5 : ℕ) := sub_nonneg.mpr hdrop
  have hgap : 4 * b ^ (5 : ℕ) - a ^ (5 : ℕ) ≤ 3 * a ^ (5 : ℕ) * y ^ (5 : ℕ) := by
    nlinarith
  have hsquare := pow_le_pow_left₀ hgap0 hgap 2
  calc
    (4 * b ^ (5 : ℕ) - a ^ (5 : ℕ)) ^ (2 : ℕ) ≤ 9 * a ^ (10 : ℕ) * y ^ (10 : ℕ) := by
      nlinarith
    _ = 9 * a ^ (5 : ℕ) * c ^ (5 : ℕ) := by rw [← hay]; ring

/-- A decreasing nonnegative log-convex triple lies below the same weighted chord used by the
fifth-root wall.  The exact square remainder is
`(5a + 3c)^(2 : ℕ) - 64ac = (a-c)(25a-9c)`; hence no differentiability is involved. -/
theorem logConvexTriple_forces_weightedChord
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hca : c ≤ a) (hlog : b ^ (2 : ℕ) ≤ a * c) :
    8 * b ≤ 5 * a + 3 * c := by
  have hleft : 0 ≤ 8 * b := by positivity
  have hright : 0 ≤ 5 * a + 3 * c := by positivity
  have hfactor : 0 ≤ (a - c) * (25 * a - 9 * c) := by
    have hfirst : 0 ≤ a - c := sub_nonneg.mpr hca
    have hsecond : 0 ≤ 25 * a - 9 * c := by nlinarith
    exact mul_nonneg hfirst hsecond
  have hsquare : (8 * b) ^ (2 : ℕ) ≤ (5 * a + 3 * c) ^ (2 : ℕ) := by
    calc
      (8 * b) ^ (2 : ℕ) = 64 * b ^ (2 : ℕ) := by ring
      _ ≤ 64 * (a * c) := by nlinarith
      _ ≤ (5 * a + 3 * c) ^ (2 : ℕ) := by
        nlinarith [hfactor]
  exact (sq_le_sq₀ hleft hright).mp hsquare

/-- Log-convexity of the decreasing fifth-root triple is a rank-two sufficient condition for
the rank-four odd wall. -/
theorem fifthRootLogConvex_forces_wall
    {a b c : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hca : c ≤ a)
    (hlog : b ^ (2 : ℕ) ≤ a * c)
    (hdrop : a ^ (5 : ℕ) ≤ 4 * b ^ (5 : ℕ)) :
    (4 * b ^ (5 : ℕ) - a ^ (5 : ℕ)) ^ (2 : ℕ) ≤ 9 * a ^ (5 : ℕ) * c ^ (5 : ℕ) := by
  apply fifthRootConvexChord_forces_wall ha hb hc hca
  · exact logConvexTriple_forces_weightedChord ha.le hb hc hca hlog
  · exact hdrop

/-- A strict violation of the `1,4,9` convex chord for a twice differentiable profile localizes
to a genuinely negative second derivative between the outer scales. -/
theorem exists_secondDeriv_neg_of_weightedChordViolation
    {f : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hcont : ContinuousOn f (Icc x (9 * x)))
    (hdiff : DifferentiableOn ℝ f (Ioo x (9 * x)))
    (hdiff' : DifferentiableOn ℝ (deriv f) (Ioo x (9 * x)))
    (hviol : 5 * f x + 3 * f (9 * x) < 8 * f (4 * x)) :
    ∃ y ∈ Ioo x (9 * x), (deriv^[2] f) y < 0 := by
  have hx9 : x < 9 * x := by nlinarith
  by_contra hnone
  have hsecond : ∀ y ∈ interior (Icc x (9 * x)), 0 ≤ (deriv^[2] f) y := by
    intro y hy
    rw [interior_Icc] at hy
    exact le_of_not_gt fun hneg => hnone ⟨y, hy, hneg⟩
  have hconv : ConvexOn ℝ (Icc x (9 * x)) f := by
    apply convexOn_of_deriv2_nonneg (convex_Icc x (9 * x)) hcont
    · simpa only [interior_Icc] using hdiff
    · simpa only [interior_Icc] using hdiff'
    · exact hsecond
  have hchord := hconv.2
    (show x ∈ Icc x (9 * x) by exact ⟨le_rfl, hx9.le⟩)
    (show 9 * x ∈ Icc x (9 * x) by exact ⟨hx9.le, le_rfl⟩)
    (show 0 ≤ (5 / 8 : ℝ) by norm_num)
    (show 0 ≤ (3 / 8 : ℝ) by norm_num)
    (show (5 / 8 : ℝ) + 3 / 8 = 1 by norm_num)
  have hpoint : (5 / 8 : ℝ) * x + (3 / 8 : ℝ) * (9 * x) = 4 * x := by ring
  simp only [smul_eq_mul] at hchord
  rw [hpoint] at hchord
  nlinarith

end HilbertMetric
