import Mathlib

/-!
# A period-wise lower bound for resonance integrals of arc-sandwiched sets

Let `λ > 0`, `P = 2π/λ`, and let `E ⊆ ℝ` be measurable.  On the period `J = [kP, (k+1)P]` write
`φ = λu − 2πk ∈ [0, 2π]`.  Suppose `E` contains the core arc `{|cos(φ/2)| ≥ 1/√2}` of `J` and is
contained in the outer arc `{|cos(φ/2)| ≥ cos θ}` for some `θ ∈ [π/4, π/2)`.  Then

`∫_J 1_E(u) cos(λu) du ≥ (2/λ) sin 2θ ≥ 0`,

because the negative part of `cos(λu)` on `E ∩ J` is confined to the arcs `[π/2, 2θ]` and
`[2π − 2θ, 3π/2]`, where it is dominated by the positive core.  A set contained in the core arc
has nonnegative integral, and any set has integral at least `−P`.
-/

open Real MeasureTheory Set intervalIntegral

namespace RHTower

noncomputable section

/-- Lower bound function on one period: the cosine on the two outer arcs, zero in between. -/
def arcLower (lam : ℝ) (a c₁ c₂ b : ℝ) (u : ℝ) : ℝ :=
  (Icc a c₁ ∪ Icc c₂ b).indicator (fun u => Real.cos (lam * u)) u

theorem abs_cos_half_of_core {φ : ℝ} (h0 : 0 ≤ φ) (h2 : φ ≤ 2 * π) (hpos : 0 < Real.cos φ) :
    Real.sqrt 2 / 2 ≤ |Real.cos (φ / 2)| := by
  by_cases hφ : φ < π / 2
  · have h1 : Real.cos (π / 4) < Real.cos (φ / 2) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]) (by linarith)
    rw [Real.cos_pi_div_four] at h1
    have : 0 ≤ Real.cos (φ / 2) := by linarith [Real.sqrt_nonneg 2]
    rw [abs_of_nonneg this]; exact h1.le
  · push Not at hφ
    have hφ' : 3 * π / 2 < φ := by
      by_contra hcon
      push Not at hcon
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hφ (by linarith)
      linarith
    have h1 : Real.cos (φ / 2) < Real.cos (3 * π / 4) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith) (by linarith)
    have h34 : Real.cos (3 * π / 4) = -(Real.sqrt 2 / 2) := by
      rw [show 3 * π / 4 = π - π / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
    rw [h34] at h1
    have : Real.cos (φ / 2) < 0 := by linarith [Real.sqrt_nonneg 2]
    rw [abs_of_neg this]; linarith

theorem abs_cos_half_lt_of_middle {φ θ : ℝ} (hθ0 : 0 ≤ θ)
    (h1 : 2 * θ < φ) (h2 : φ < 2 * π - 2 * θ) : |Real.cos (φ / 2)| < Real.cos θ := by
  have ha : Real.cos (φ / 2) < Real.cos θ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hθ0 (by linarith) (by linarith)
  have hb : Real.cos (π - θ) < Real.cos (φ / 2) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]) (by linarith)
  rw [Real.cos_pi_sub] at hb
  rw [abs_lt]; constructor <;> linarith

/-- `cos(λu)` and `|cos(λu/2)|` on the `k`-th period in terms of `φ = λu − 2πk`. -/
theorem cos_lam_mul_eq {lam u : ℝ} (k : ℕ) :
    Real.cos (lam * u) = Real.cos (lam * u - 2 * π * k) := by
  have : lam * u = (lam * u - 2 * π * k) + (k : ℤ) * (2 * π) := by push_cast; ring
  conv_lhs => rw [this]
  rw [Real.cos_add_int_mul_two_pi]

theorem abs_cos_half_lam_mul_eq {lam u : ℝ} (k : ℕ) :
    |Real.cos (lam * u / 2)| = |Real.cos ((lam * u - 2 * π * k) / 2)| := by
  have : lam * u / 2 = (lam * u - 2 * π * k) / 2 + (k : ℕ) * π := by ring
  rw [this, Real.cos_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- **Pointwise sandwich on one period.** -/
theorem arcLower_le_indicator {lam : ℝ} (hlam : 0 < lam) {E : Set ℝ} (k : ℕ) {θ : ℝ}
    (hθ1 : π / 4 ≤ θ) (hθ2 : θ < π / 2)
    (hcore : ∀ u ∈ Icc ((k : ℝ) * (2 * π / lam)) (((k : ℝ) + 1) * (2 * π / lam)),
      Real.sqrt 2 / 2 ≤ |Real.cos (lam * u / 2)| → u ∈ E)
    (houter : ∀ u ∈ Icc ((k : ℝ) * (2 * π / lam)) (((k : ℝ) + 1) * (2 * π / lam)),
      u ∈ E → Real.cos θ ≤ |Real.cos (lam * u / 2)|)
    {u : ℝ} (hu : u ∈ Icc ((k : ℝ) * (2 * π / lam)) (((k : ℝ) + 1) * (2 * π / lam))) :
    arcLower lam ((k : ℝ) * (2 * π / lam)) ((k : ℝ) * (2 * π / lam) + 2 * θ / lam)
        (((k : ℝ) + 1) * (2 * π / lam) - 2 * θ / lam) (((k : ℝ) + 1) * (2 * π / lam)) u ≤
      E.indicator (fun u => Real.cos (lam * u)) u := by
  set φ := lam * u - 2 * π * k with hφ
  have hφ0 : 0 ≤ φ := by
    rw [hφ]
    have := hu.1
    have h : lam * ((k : ℝ) * (2 * π / lam)) = 2 * π * k := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left this hlam.le]
  have hφ2 : φ ≤ 2 * π := by
    rw [hφ]
    have := hu.2
    have h : lam * (((k : ℝ) + 1) * (2 * π / lam)) = 2 * π * k + 2 * π := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left this hlam.le]
  have hcos : Real.cos (lam * u) = Real.cos φ := cos_lam_mul_eq k
  have habs : |Real.cos (lam * u / 2)| = |Real.cos (φ / 2)| := abs_cos_half_lam_mul_eq k
  unfold arcLower
  by_cases hmem : u ∈ Icc ((k : ℝ) * (2 * π / lam)) ((k : ℝ) * (2 * π / lam) + 2 * θ / lam) ∪
      Icc (((k : ℝ) + 1) * (2 * π / lam) - 2 * θ / lam) (((k : ℝ) + 1) * (2 * π / lam))
  · rw [Set.indicator_of_mem hmem]
    by_cases hsign : Real.cos (lam * u) ≤ 0
    · by_cases hE : u ∈ E
      · rw [Set.indicator_of_mem hE]
      · rw [Set.indicator_of_notMem hE]; exact hsign
    · push Not at hsign
      have hE : u ∈ E := by
        apply hcore u hu
        rw [habs]
        exact abs_cos_half_of_core hφ0 hφ2 (by rwa [hcos] at hsign)
      rw [Set.indicator_of_mem hE]
  · rw [Set.indicator_of_notMem hmem]
    -- `u` lies strictly between the arcs, so `|cos(φ/2)| < cos θ` and `u ∉ E`
    have hnot : u ∉ E := by
      intro hE
      have h := houter u hu hE
      rw [habs] at h
      have hlt : |Real.cos (φ / 2)| < Real.cos θ := by
        apply abs_cos_half_lt_of_middle (by linarith [Real.pi_pos])
        · -- `2θ < φ`
          by_contra hcon
          push Not at hcon
          apply hmem; left
          refine ⟨hu.1, ?_⟩
          have : lam * u ≤ 2 * π * k + 2 * θ := by rw [hφ] at hcon; linarith
          have h' : (k : ℝ) * (2 * π / lam) + 2 * θ / lam = (2 * π * k + 2 * θ) / lam := by
            field_simp
          rw [h', le_div_iff₀ hlam]; linarith
        · -- `φ < 2π − 2θ`
          by_contra hcon
          push Not at hcon
          apply hmem; right
          refine ⟨?_, hu.2⟩
          have : 2 * π * k + 2 * π - 2 * θ ≤ lam * u := by rw [hφ] at hcon; linarith
          have h' : ((k : ℝ) + 1) * (2 * π / lam) - 2 * θ / lam =
              (2 * π * k + 2 * π - 2 * θ) / lam := by field_simp
          rw [h', div_le_iff₀ hlam]; linarith
      linarith
    rw [Set.indicator_of_notMem hnot]

/-- The integral of the arc lower function over one period. -/
theorem integral_arcLower {lam : ℝ} (hlam : 0 < lam) (k : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ2 : θ < π / 2) :
    ∫ u in ((k : ℝ) * (2 * π / lam))..(((k : ℝ) + 1) * (2 * π / lam)),
        arcLower lam ((k : ℝ) * (2 * π / lam)) ((k : ℝ) * (2 * π / lam) + 2 * θ / lam)
          (((k : ℝ) + 1) * (2 * π / lam) - 2 * θ / lam) (((k : ℝ) + 1) * (2 * π / lam)) u =
      2 / lam * Real.sin (2 * θ) := by
  set a := (k : ℝ) * (2 * π / lam) with ha
  set b := ((k : ℝ) + 1) * (2 * π / lam) with hb
  set c₁ := a + 2 * θ / lam with hc₁
  set c₂ := b - 2 * θ / lam with hc₂
  have hP : 0 < 2 * π / lam := by positivity
  have hθlam : 0 ≤ 2 * θ / lam := by positivity
  have hθP : 2 * θ / lam < π / lam := by
    rw [div_lt_div_iff_of_pos_right hlam]; linarith
  have hab : a ≤ b := by rw [ha, hb]; nlinarith
  have hac₁ : a ≤ c₁ := by rw [hc₁]; linarith
  have hc₁c₂ : c₁ < c₂ := by
    rw [hc₁, hc₂, hb, ha]
    have : ((k : ℝ) + 1) * (2 * π / lam) = (k : ℝ) * (2 * π / lam) + 2 * (π / lam) := by ring
    rw [this]; linarith
  have hc₂b : c₂ ≤ b := by rw [hc₂]; linarith
  have hcont : Continuous fun u : ℝ => Real.cos (lam * u) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hdisj : Disjoint (Icc a c₁) (Icc c₂ b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    linarith [hx.2, hx'.1]
  -- split the indicator of the union
  have hsplit : ∀ u, arcLower lam a c₁ c₂ b u =
      (Icc a c₁).indicator (fun u => Real.cos (lam * u)) u +
        (Icc c₂ b).indicator (fun u => Real.cos (lam * u)) u := by
    intro u
    unfold arcLower
    rw [Set.indicator_union_of_disjoint hdisj]
  have hc₁b : c₁ ≤ b := le_trans hc₁c₂.le hc₂b
  have hint1 : ∫ u in a..b, (Icc a c₁).indicator (fun u => Real.cos (lam * u)) u =
      ∫ u in a..c₁, Real.cos (lam * u) := by
    have hset : Ioc a b ∩ Icc a c₁ = Ioc a c₁ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, ⟨_, h2⟩⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hc₁b⟩, ⟨h1.le, h2⟩⟩
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hac₁,
      MeasureTheory.setIntegral_indicator measurableSet_Icc, hset]
  have hint2 : ∫ u in a..b, (Icc c₂ b).indicator (fun u => Real.cos (lam * u)) u =
      ∫ u in c₂..b, Real.cos (lam * u) := by
    have hac₂ : a < c₂ := lt_of_le_of_lt hac₁ hc₁c₂
    have hset : Ioc a b ∩ Icc c₂ b = Icc c₂ b := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨_, ⟨h1, h2⟩⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, ⟨h1, h2⟩⟩
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hc₂b,
      MeasureTheory.setIntegral_indicator measurableSet_Icc, hset,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hI1 : IntervalIntegrable (fun u => (Icc a c₁).indicator (fun u => Real.cos (lam * u)) u)
      volume a b :=
    ⟨(hcont.intervalIntegrable a b).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable a b).2.indicator measurableSet_Icc⟩
  have hI2 : IntervalIntegrable (fun u => (Icc c₂ b).indicator (fun u => Real.cos (lam * u)) u)
      volume a b :=
    ⟨(hcont.intervalIntegrable a b).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable a b).2.indicator measurableSet_Icc⟩
  simp_rw [hsplit]
  rw [intervalIntegral.integral_add hI1 hI2, hint1, hint2]
  -- evaluate the two cosine integrals
  have hcos_int : ∀ p q : ℝ, ∫ u in p..q, Real.cos (lam * u) = lam⁻¹ * (Real.sin (lam * q) - Real.sin (lam * p)) := by
    intro p q
    have := intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) (a := p) (b := q) hlam.ne'
    rw [this, integral_cos, smul_eq_mul]
  rw [hcos_int, hcos_int]
  have hla : lam * a = 0 + (k : ℕ) * (2 * π) := by rw [ha]; field_simp; ring
  have hlc₁ : lam * c₁ = 2 * θ + (k : ℕ) * (2 * π) := by rw [hc₁, ha]; field_simp; ring
  have hlc₂ : lam * c₂ = -(2 * θ) + (k + 1 : ℕ) * (2 * π) := by
    rw [hc₂, hb]; field_simp; push_cast; ring
  have hlb : lam * b = 0 + (k + 1 : ℕ) * (2 * π) := by rw [hb]; field_simp; push_cast; ring
  rw [hla, hlc₁, hlc₂, hlb, Real.sin_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi,
    Real.sin_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi, Real.sin_zero, Real.sin_neg]
  field_simp
  ring

/-- **Period lower bound.** -/
theorem integral_indicator_cos_period_ge {lam : ℝ} (hlam : 0 < lam) {E : Set ℝ}
    (hE : MeasurableSet E) (k : ℕ) {θ : ℝ} (hθ1 : π / 4 ≤ θ) (hθ2 : θ < π / 2)
    (hcore : ∀ u ∈ Icc ((k : ℝ) * (2 * π / lam)) (((k : ℝ) + 1) * (2 * π / lam)),
      Real.sqrt 2 / 2 ≤ |Real.cos (lam * u / 2)| → u ∈ E)
    (houter : ∀ u ∈ Icc ((k : ℝ) * (2 * π / lam)) (((k : ℝ) + 1) * (2 * π / lam)),
      u ∈ E → Real.cos θ ≤ |Real.cos (lam * u / 2)|) :
    2 / lam * Real.sin (2 * θ) ≤
      ∫ u in ((k : ℝ) * (2 * π / lam))..(((k : ℝ) + 1) * (2 * π / lam)),
        E.indicator (fun u => Real.cos (lam * u)) u := by
  have hP : 0 < 2 * π / lam := by positivity
  have hab : (k : ℝ) * (2 * π / lam) ≤ ((k : ℝ) + 1) * (2 * π / lam) := by nlinarith
  have hcont : Continuous fun u : ℝ => Real.cos (lam * u) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hIE : IntervalIntegrable (fun u => E.indicator (fun u => Real.cos (lam * u)) u) volume
      ((k : ℝ) * (2 * π / lam)) (((k : ℝ) + 1) * (2 * π / lam)) :=
    ⟨(hcont.intervalIntegrable _ _).1.indicator hE, (hcont.intervalIntegrable _ _).2.indicator hE⟩
  have hIg : IntervalIntegrable (arcLower lam ((k : ℝ) * (2 * π / lam))
      ((k : ℝ) * (2 * π / lam) + 2 * θ / lam) (((k : ℝ) + 1) * (2 * π / lam) - 2 * θ / lam)
      (((k : ℝ) + 1) * (2 * π / lam))) volume
      ((k : ℝ) * (2 * π / lam)) (((k : ℝ) + 1) * (2 * π / lam)) := by
    unfold arcLower
    exact ⟨(hcont.intervalIntegrable _ _).1.indicator (measurableSet_Icc.union measurableSet_Icc),
      (hcont.intervalIntegrable _ _).2.indicator (measurableSet_Icc.union measurableSet_Icc)⟩
  rw [← integral_arcLower hlam k (by linarith [Real.pi_pos]) hθ2]
  exact intervalIntegral.integral_mono_on hab hIg hIE
    (fun u hu => arcLower_le_indicator hlam k hθ1 hθ2 hcore houter hu)

/-- A set inside the core arc has nonnegative resonance integral on the period. -/
theorem integral_indicator_cos_period_nonneg {lam : ℝ} (hlam : 0 < lam) {E : Set ℝ} (k : ℕ)
    (houter : ∀ u ∈ Icc ((k : ℝ) * (2 * π / lam)) (((k : ℝ) + 1) * (2 * π / lam)),
      u ∈ E → Real.sqrt 2 / 2 ≤ |Real.cos (lam * u / 2)|) :
    0 ≤ ∫ u in ((k : ℝ) * (2 * π / lam))..(((k : ℝ) + 1) * (2 * π / lam)),
        E.indicator (fun u => Real.cos (lam * u)) u := by
  have hP : 0 < 2 * π / lam := by positivity
  have hab : (k : ℝ) * (2 * π / lam) ≤ ((k : ℝ) + 1) * (2 * π / lam) := by nlinarith
  apply intervalIntegral.integral_nonneg hab
  intro u hu
  by_cases hEu : u ∈ E
  · rw [Set.indicator_of_mem hEu]
    have h := houter u hu hEu
    -- `cos(λu) = 2cos²(λu/2) − 1 ≥ 0`
    have hsq : (Real.sqrt 2 / 2) ^ 2 ≤ Real.cos (lam * u / 2) ^ 2 := by
      calc (Real.sqrt 2 / 2) ^ 2 ≤ |Real.cos (lam * u / 2)| ^ 2 :=
            pow_le_pow_left₀ (by positivity) h 2
        _ = Real.cos (lam * u / 2) ^ 2 := sq_abs _
    have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hc : Real.cos (lam * u) = 2 * Real.cos (lam * u / 2) ^ 2 - 1 := by
      rw [Real.cos_sq]
      rw [show 2 * (lam * u / 2) = lam * u by ring]; ring
    rw [hc]; linarith
  · rw [Set.indicator_of_notMem hEu]

/-- Any measurable set has resonance integral at least `−P` on a period. -/
theorem integral_indicator_cos_period_ge_neg {lam : ℝ} (hlam : 0 < lam) {E : Set ℝ}
    (hE : MeasurableSet E) (k : ℕ) :
    -(2 * π / lam) ≤ ∫ u in ((k : ℝ) * (2 * π / lam))..(((k : ℝ) + 1) * (2 * π / lam)),
        E.indicator (fun u => Real.cos (lam * u)) u := by
  have hP : 0 < 2 * π / lam := by positivity
  have hab : (k : ℝ) * (2 * π / lam) ≤ ((k : ℝ) + 1) * (2 * π / lam) := by nlinarith
  have hcont : Continuous fun u : ℝ => Real.cos (lam * u) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hIE : IntervalIntegrable (fun u => E.indicator (fun u => Real.cos (lam * u)) u) volume
      ((k : ℝ) * (2 * π / lam)) (((k : ℝ) + 1) * (2 * π / lam)) :=
    ⟨(hcont.intervalIntegrable _ _).1.indicator hE, (hcont.intervalIntegrable _ _).2.indicator hE⟩
  have hconst : ∫ u in ((k : ℝ) * (2 * π / lam))..(((k : ℝ) + 1) * (2 * π / lam)), (-1 : ℝ) =
      -(2 * π / lam) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab (by simp) hIE
  intro u hu
  by_cases hEu : u ∈ E
  · rw [Set.indicator_of_mem hEu]; exact Real.neg_one_le_cos _
  · rw [Set.indicator_of_notMem hEu]; norm_num

end

end RHTower
