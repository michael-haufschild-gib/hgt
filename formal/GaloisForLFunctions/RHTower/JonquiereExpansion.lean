import GaloisForLFunctions.RHTower.HurwitzZetaSmallShift

/-!
# Jonquière's boundary expansion of the polylogarithm

For `0 < Re s < 1` and a small positive phase `θ` the boundary germ of `∑ n^{-s} e^{i n θ}`
splits into a singular power, the value of the Riemann zeta function, and a remainder that is
linear in `θ`:

`Li_s(e^{iθ}) = Γ(1-s) e^{iπ(1-s)/2} θ^{s-1} + ζ(s) + O_s(θ)`.

The identity is Hurwitz's formula (mathlib's `expZeta_one_sub`) combined with the small-shift
expansion of the Hurwitz zeta function and the functional equation of `ζ`.
-/

open Complex HurwitzZeta Filter Topology Set

namespace RHTower

/-- The leading Jonquière coefficient `A₊(s) = Γ(1-s) e^{-iπ(s-1)/2}`. -/
noncomputable def jonquiereLead (s : ℂ) : ℂ :=
  Complex.Gamma (1 - s) * Complex.exp (↑Real.pi * I * (1 - s) / 2)

/-- The Jonquière remainder, as an explicit combination of the two shift-difference series. -/
noncomputable def jonquiereRemainder (s : ℂ) (θ : ℝ) : ℂ :=
  ((2 * ↑Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
    (Complex.exp (↑Real.pi * I * (1 - s) / 2) * shiftDiffSeries (θ / (2 * Real.pi)) (1 - s)
      + Complex.exp (-↑Real.pi * I * (1 - s) / 2)
          * shiftDiffSeries (-(θ / (2 * Real.pi))) (1 - s))

theorem neg_coe_unitAddCircle (a : ℝ) :
    (-((a : ℝ) : UnitAddCircle)) = (((-a : ℝ)) : UnitAddCircle) := rfl

/-- **Jonquière's expansion, exact form.** -/
theorem expZeta_eq_jonquiere {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    expZeta ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle) s
      = jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s + jonquiereRemainder s θ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set a : ℝ := θ / (2 * Real.pi) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ (by positivity)]
    linarith
  set w : ℂ := 1 - s with hw
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  have hwre1 : w.re < 1 := by rw [hw]; simp; linarith
  -- Hurwitz's formula
  have hne : ∀ n : ℕ, w ≠ 1 - (n : ℂ) := by
    intro n hcon
    have : s = (n : ℂ) := by rw [hw] at hcon; linear_combination -hcon
    rw [this] at h0 h1
    simp at h0 h1
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro hn; rw [hn] at h0; simp at h0)
    linarith
  have hform := expZeta_one_sub ((a : ℝ) : UnitAddCircle) (s := w) hne
  rw [show (1 : ℂ) - w = s by rw [hw]; ring] at hform
  -- the two small-shift expansions
  have hpos := hurwitzZeta_sub_riemannZeta_eq ha0 ha1 hwre
  have hneg := hurwitzZeta_neg_sub_riemannZeta_eq ha0 ha1 hwre
  rw [← neg_coe_unitAddCircle a] at hneg
  -- the functional equation of ζ
  have hzne : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hcon
    have : w.re = -(n : ℝ) := by rw [hcon]; simp
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hz1 : w ≠ 1 := by
    intro hcon
    rw [hcon] at hwre1
    simp at hwre1
  have hfe := riemannZeta_one_sub hzne hz1
  rw [show (1 : ℂ) - w = s by rw [hw]; ring] at hfe
  -- assemble
  have hpos' : hurwitzZeta ((a : ℝ) : UnitAddCircle) w
      = riemannZeta w + (((a : ℝ) : ℂ) ^ (-w) + shiftDiffSeries a w) := by
    linear_combination hpos
  have hneg' : hurwitzZeta (-((a : ℝ) : UnitAddCircle)) w
      = riemannZeta w + shiftDiffSeries (-a) w := by
    linear_combination hneg
  have hcos : (2 : ℂ) * Complex.cos (↑Real.pi * w / 2)
      = Complex.exp (↑Real.pi * I * w / 2) + Complex.exp (-↑Real.pi * I * w / 2) := by
    rw [Complex.cos]
    ring_nf
  have hsplit : ((2 * ↑Real.pi : ℂ)) ^ (-w) * ((a : ℝ) : ℂ) ^ (-w) = ((θ : ℝ) : ℂ) ^ (s - 1) := by
    have h2pi : ((2 * ↑Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
    rw [h2pi, ← Complex.mul_cpow_ofReal_nonneg (by positivity) ha0.le]
    rw [← Complex.ofReal_mul, show (2 * Real.pi) * a = θ by rw [ha]; field_simp,
      show -w = s - 1 by rw [hw]; ring]
  have hzeta : riemannZeta s
      = ((2 * ↑Real.pi : ℂ)) ^ (-w) * Complex.Gamma w
        * (Complex.exp (↑Real.pi * I * w / 2) + Complex.exp (-↑Real.pi * I * w / 2))
        * riemannZeta w := by
    rw [hfe, ← hcos]
    ring
  rw [hform, hpos', hneg', jonquiereLead, jonquiereRemainder, ← ha, ← hw, hzeta, ← hsplit]
  ring

/-- The explicit constant in the Jonquière remainder bound. -/
noncomputable def jonquiereConst (s : ℂ) : ℝ :=
  ‖((2 * (Real.pi : ℂ))) ^ (-(1 - s))‖ * ‖Complex.Gamma (1 - s)‖
    * (‖Complex.exp (↑Real.pi * I * (1 - s) / 2)‖
        + ‖Complex.exp (-↑Real.pi * I * (1 - s) / 2)‖)
    * (‖(1 - s)‖ * 2 ^ ((1 - s).re + 1)
        * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 - s).re - 1)))
    / (2 * Real.pi)

theorem jonquiereConst_nonneg (s : ℂ) : 0 ≤ jonquiereConst s := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsum : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 - s).re - 1) :=
    tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ 2 ^ ((1 - s).re + 1) := Real.rpow_nonneg (by norm_num) _
  rw [jonquiereConst]
  positivity

/-- **Jonquière's expansion with a linear remainder bound.** -/
theorem norm_jonquiereRemainder_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    ‖jonquiereRemainder s θ‖ ≤ jonquiereConst s * θ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set a : ℝ := θ / (2 * Real.pi) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : |a| ≤ 1 / 2 := by
    rw [abs_of_pos ha0, ha, div_le_iff₀ (by positivity)]
    linarith
  have ha1' : |(-a)| ≤ 1 / 2 := by rwa [abs_neg]
  set w : ℂ := 1 - s with hw
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  set M : ℝ := ‖w‖ * 2 ^ (w.re + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-w.re - 1)) with hM
  have hMbound : ∀ b : ℝ, |b| ≤ 1 / 2 → ‖shiftDiffSeries b w‖ ≤ M * |b| := by
    intro b hb
    have := norm_shiftDiffSeries_le hb hwre
    rw [hM]
    linarith
  have hD1 : ‖shiftDiffSeries a w‖ ≤ M * a := by
    have := hMbound a ha1
    rwa [abs_of_pos ha0] at this
  have hD2 : ‖shiftDiffSeries (-a) w‖ ≤ M * a := by
    have := hMbound (-a) ha1'
    rwa [abs_neg, abs_of_pos ha0] at this
  set E₁ : ℂ := Complex.exp (↑Real.pi * I * w / 2) with hE₁
  set E₂ : ℂ := Complex.exp (-↑Real.pi * I * w / 2) with hE₂
  have hstep : ‖E₁ * shiftDiffSeries a w + E₂ * shiftDiffSeries (-a) w‖
      ≤ (‖E₁‖ + ‖E₂‖) * (M * a) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hM0 : 0 ≤ M * a := by
      refine le_trans (norm_nonneg _) hD1
    nlinarith [norm_nonneg E₁, norm_nonneg E₂, hD1, hD2]
  rw [jonquiereRemainder, ← hw, ← ha, ← hE₁, ← hE₂, norm_mul, norm_mul]
  have hfin : ‖((2 * (Real.pi : ℂ))) ^ (-w)‖ * ‖Complex.Gamma w‖
      * ‖E₁ * shiftDiffSeries a w + E₂ * shiftDiffSeries (-a) w‖
      ≤ ‖((2 * (Real.pi : ℂ))) ^ (-w)‖ * ‖Complex.Gamma w‖ * ((‖E₁‖ + ‖E₂‖) * (M * a)) := by
    refine mul_le_mul_of_nonneg_left hstep ?_
    positivity
  refine hfin.trans ?_
  rw [jonquiereConst, ← hw, ← hE₁, ← hE₂, ← hM, ha]
  field_simp
  exact le_rfl

/-- **The boundary germ of the polylogarithm, with an explicit linear error.** -/
theorem norm_expZeta_sub_jonquiere_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    ‖expZeta ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle) s
        - (jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s)‖
      ≤ jonquiereConst s * θ := by
  have h := expZeta_eq_jonquiere h0 h1 hθ0 hθ1
  rw [h]
  have : jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s + jonquiereRemainder s θ
      - (jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s)
      = jonquiereRemainder s θ := by ring
  rw [this]
  exact norm_jonquiereRemainder_le h0 h1 hθ0 hθ1

/-! ## The reflected phase -/

/-- The leading Jonquière coefficient on the negative side, `A₋(s) = Γ(1-s) e^{iπ(s-1)/2}`. -/
noncomputable def jonquiereLeadNeg (s : ℂ) : ℂ :=
  Complex.Gamma (1 - s) * Complex.exp (-↑Real.pi * I * (1 - s) / 2)

/-- The Jonquière remainder on the negative side. -/
noncomputable def jonquiereRemainderNeg (s : ℂ) (θ : ℝ) : ℂ :=
  ((2 * ↑Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
    (Complex.exp (↑Real.pi * I * (1 - s) / 2) * shiftDiffSeries (-(θ / (2 * Real.pi))) (1 - s)
      + Complex.exp (-↑Real.pi * I * (1 - s) / 2)
          * shiftDiffSeries (θ / (2 * Real.pi)) (1 - s))

theorem neg_neg_coe_unitAddCircle (a : ℝ) :
    (-(((-a : ℝ)) : UnitAddCircle)) = (((a : ℝ)) : UnitAddCircle) := by
  rw [neg_coe_unitAddCircle, neg_neg]

/-- **Jonquière's expansion at a negative phase, exact form.** -/
theorem expZeta_neg_eq_jonquiere {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    expZeta ((-(θ / (2 * Real.pi)) : ℝ) : UnitAddCircle) s
      = jonquiereLeadNeg s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s
        + jonquiereRemainderNeg s θ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set a : ℝ := θ / (2 * Real.pi) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ (by positivity)]
    linarith
  set w : ℂ := 1 - s with hw
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  have hwre1 : w.re < 1 := by rw [hw]; simp; linarith
  have hne : ∀ n : ℕ, w ≠ 1 - (n : ℂ) := by
    intro n hcon
    have hsn : s = (n : ℂ) := by rw [hw] at hcon; linear_combination -hcon
    rw [hsn] at h0 h1
    simp at h0 h1
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro hn; rw [hn] at h0; simp at h0)
    linarith
  have hform := expZeta_one_sub ((-a : ℝ) : UnitAddCircle) (s := w) hne
  rw [show (1 : ℂ) - w = s by rw [hw]; ring, neg_neg_coe_unitAddCircle] at hform
  have hpos := hurwitzZeta_sub_riemannZeta_eq ha0 ha1 hwre
  have hneg := hurwitzZeta_neg_sub_riemannZeta_eq ha0 ha1 hwre
  have hzne : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hcon
    have hre : w.re = -(n : ℝ) := by rw [hcon]; simp
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hz1 : w ≠ 1 := by
    intro hcon
    rw [hcon] at hwre1
    simp at hwre1
  have hfe := riemannZeta_one_sub hzne hz1
  rw [show (1 : ℂ) - w = s by rw [hw]; ring] at hfe
  have hpos' : hurwitzZeta ((a : ℝ) : UnitAddCircle) w
      = riemannZeta w + (((a : ℝ) : ℂ) ^ (-w) + shiftDiffSeries a w) := by
    linear_combination hpos
  have hneg' : hurwitzZeta ((-a : ℝ) : UnitAddCircle) w
      = riemannZeta w + shiftDiffSeries (-a) w := by
    linear_combination hneg
  have hcos : (2 : ℂ) * Complex.cos (↑Real.pi * w / 2)
      = Complex.exp (↑Real.pi * I * w / 2) + Complex.exp (-↑Real.pi * I * w / 2) := by
    rw [Complex.cos]
    ring_nf
  have hsplit : ((2 * ↑Real.pi : ℂ)) ^ (-w) * ((a : ℝ) : ℂ) ^ (-w) = ((θ : ℝ) : ℂ) ^ (s - 1) := by
    have h2pi : ((2 * ↑Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
    rw [h2pi, ← Complex.mul_cpow_ofReal_nonneg (by positivity) ha0.le]
    rw [← Complex.ofReal_mul, show (2 * Real.pi) * a = θ by rw [ha]; field_simp,
      show -w = s - 1 by rw [hw]; ring]
  have hzeta : riemannZeta s
      = ((2 * ↑Real.pi : ℂ)) ^ (-w) * Complex.Gamma w
        * (Complex.exp (↑Real.pi * I * w / 2) + Complex.exp (-↑Real.pi * I * w / 2))
        * riemannZeta w := by
    rw [hfe, ← hcos]
    ring
  rw [hform, hpos', hneg', jonquiereLeadNeg, jonquiereRemainderNeg, ← ha, ← hw, hzeta, ← hsplit]
  ring

theorem norm_jonquiereRemainderNeg_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    ‖jonquiereRemainderNeg s θ‖ ≤ jonquiereConst s * θ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set a : ℝ := θ / (2 * Real.pi) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : |a| ≤ 1 / 2 := by
    rw [abs_of_pos ha0, ha, div_le_iff₀ (by positivity)]
    linarith
  have ha1' : |(-a)| ≤ 1 / 2 := by rwa [abs_neg]
  set w : ℂ := 1 - s with hw
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  set M : ℝ := ‖w‖ * 2 ^ (w.re + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-w.re - 1)) with hM
  have hMbound : ∀ b : ℝ, |b| ≤ 1 / 2 → ‖shiftDiffSeries b w‖ ≤ M * |b| := by
    intro b hb
    have := norm_shiftDiffSeries_le hb hwre
    rw [hM]
    linarith
  have hD1 : ‖shiftDiffSeries a w‖ ≤ M * a := by
    have := hMbound a ha1
    rwa [abs_of_pos ha0] at this
  have hD2 : ‖shiftDiffSeries (-a) w‖ ≤ M * a := by
    have := hMbound (-a) ha1'
    rwa [abs_neg, abs_of_pos ha0] at this
  set E₁ : ℂ := Complex.exp (↑Real.pi * I * w / 2) with hE₁
  set E₂ : ℂ := Complex.exp (-↑Real.pi * I * w / 2) with hE₂
  have hstep : ‖E₁ * shiftDiffSeries (-a) w + E₂ * shiftDiffSeries a w‖
      ≤ (‖E₁‖ + ‖E₂‖) * (M * a) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hM0 : 0 ≤ M * a := le_trans (norm_nonneg _) hD1
    nlinarith [norm_nonneg E₁, norm_nonneg E₂, hD1, hD2]
  rw [jonquiereRemainderNeg, ← hw, ← ha, ← hE₁, ← hE₂, norm_mul, norm_mul]
  have hfin : ‖((2 * (Real.pi : ℂ))) ^ (-w)‖ * ‖Complex.Gamma w‖
      * ‖E₁ * shiftDiffSeries (-a) w + E₂ * shiftDiffSeries a w‖
      ≤ ‖((2 * (Real.pi : ℂ))) ^ (-w)‖ * ‖Complex.Gamma w‖ * ((‖E₁‖ + ‖E₂‖) * (M * a)) := by
    refine mul_le_mul_of_nonneg_left hstep ?_
    positivity
  refine hfin.trans ?_
  rw [jonquiereConst, ← hw, ← hE₁, ← hE₂, ← hM, ha]
  field_simp
  exact le_rfl

/-- **The boundary germ of the polylogarithm at a negative phase.** -/
theorem norm_expZeta_neg_sub_jonquiere_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    ‖expZeta ((-(θ / (2 * Real.pi)) : ℝ) : UnitAddCircle) s
        - (jonquiereLeadNeg s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s)‖
      ≤ jonquiereConst s * θ := by
  have h := expZeta_neg_eq_jonquiere h0 h1 hθ0 hθ1
  rw [h]
  have hcancel : jonquiereLeadNeg s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s
      + jonquiereRemainderNeg s θ
      - (jonquiereLeadNeg s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s)
      = jonquiereRemainderNeg s θ := by ring
  rw [hcancel]
  exact norm_jonquiereRemainderNeg_le h0 h1 hθ0 hθ1

/-! ## Regularity of the boundary germ -/

/-- **The boundary germ of the polylogarithm is continuous on the punctured phase window.** -/
theorem continuousOn_expZeta_phase {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ContinuousOn (fun θ : ℝ => expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) s)
      (Set.Ioc (0 : ℝ) Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hw : 0 < (1 - s).re := by simp; linarith
  have hmaps : Set.MapsTo (fun θ : ℝ => θ / (2 * Real.pi)) (Set.Ioc (0 : ℝ) Real.pi)
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro θ hθ
    have hθ0 : (0 : ℝ) < θ := hθ.1
    have hpos : (0 : ℝ) < θ / (2 * Real.pi) := by positivity
    refine ⟨by linarith, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    linarith [hθ.2]
  have hmapsneg : Set.MapsTo (fun θ : ℝ => -(θ / (2 * Real.pi))) (Set.Ioc (0 : ℝ) Real.pi)
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro θ hθ
    obtain ⟨h1', h2'⟩ := hmaps hθ
    exact ⟨by linarith, by linarith⟩

  have hdiv : ContinuousOn (fun θ : ℝ => θ / (2 * Real.pi)) (Set.Ioc (0 : ℝ) Real.pi) := by
    fun_prop
  have hdivneg : ContinuousOn (fun θ : ℝ => -(θ / (2 * Real.pi))) (Set.Ioc (0 : ℝ) Real.pi) := by
    fun_prop
  have hrem : ContinuousOn (fun θ : ℝ => jonquiereRemainder s θ) (Set.Ioc (0 : ℝ) Real.pi) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.add ?_ ?_)
    · exact continuousOn_const.mul
        ((continuousOn_shiftDiffSeries hw).comp hdiv hmaps)
    · exact continuousOn_const.mul
        ((continuousOn_shiftDiffSeries hw).comp hdivneg hmapsneg)
  have hpow : ContinuousOn (fun θ : ℝ => ((θ : ℝ) : ℂ) ^ (s - 1)) (Set.Ioc (0 : ℝ) Real.pi) := by
    intro θ hθ
    have hθ0 : (0 : ℝ) < θ := hθ.1
    have hslit : ((θ : ℝ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by simpa using hθ0)
    have h1' : ContinuousAt (fun t : ℝ => ((t : ℝ) : ℂ)) θ := by fun_prop
    exact (ContinuousAt.comp (g := fun z : ℂ => z ^ (s - 1))
      (f := fun t : ℝ => ((t : ℝ) : ℂ)) (x := θ)
      (continuousAt_cpow_const hslit) h1').continuousWithinAt
  refine ContinuousOn.congr ?_ (fun θ hθ => expZeta_eq_jonquiere h0 h1 hθ.1 hθ.2)
  exact ((continuousOn_const.mul hpow).add continuousOn_const).add hrem

/-! ## The tangent of the regularized germ -/

/-- The linear coefficient of the Jonquière remainder. -/
noncomputable def jonquiereTangent (s : ℂ) : ℂ :=
  ((2 * ↑Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s)
    * ((1 - s) * riemannZeta ((1 - s) + 1)
      * (Complex.exp (-↑Real.pi * I * (1 - s) / 2) - Complex.exp (↑Real.pi * I * (1 - s) / 2)))
    / (2 * ↑Real.pi)

/-- The explicit constant in the quadratic remainder bound. -/
noncomputable def jonquiereTangentConst (s : ℂ) : ℝ :=
  ‖((2 * (Real.pi : ℂ))) ^ (-(1 - s))‖ * ‖Complex.Gamma (1 - s)‖
    * (‖Complex.exp (↑Real.pi * I * (1 - s) / 2)‖
        + ‖Complex.exp (-↑Real.pi * I * (1 - s) / 2)‖)
    * (‖(1 - s)‖ * (‖(1 - s) + 1‖ * 2 ^ ((1 - s).re + 2))
        * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 - s).re - 2)))
    / (2 * Real.pi) ^ 2

theorem jonquiereTangentConst_nonneg (s : ℂ) : 0 ≤ jonquiereTangentConst s := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsum : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 - s).re - 2) :=
    tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ 2 ^ ((1 - s).re + 2) := Real.rpow_nonneg (by norm_num) _
  rw [jonquiereTangentConst]
  positivity

/-- **The Jonquière remainder is linear with a quadratic error.** -/
theorem norm_jonquiereRemainder_sub_tangent_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    ‖jonquiereRemainder s θ - jonquiereTangent s * (θ : ℂ)‖
      ≤ jonquiereTangentConst s * θ ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set a : ℝ := θ / (2 * Real.pi) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : |a| ≤ 1 / 2 := by
    rw [abs_of_pos ha0, ha, div_le_iff₀ (by positivity)]
    linarith
  have ha1' : |(-a)| ≤ 1 / 2 := by rwa [abs_neg]
  set w : ℂ := 1 - s with hw
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  set M : ℝ := ‖w‖ * (‖w + 1‖ * 2 ^ (w.re + 2)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-w.re - 2)) with hM
  set E₁ : ℂ := Complex.exp (↑Real.pi * I * w / 2) with hE₁
  set E₂ : ℂ := Complex.exp (-↑Real.pi * I * w / 2) with hE₂
  set Z : ℂ := riemannZeta (w + 1) with hZ
  have hd1 := norm_shiftDiffSeries_add_linear_le ha1 hwre
  have hd2 := norm_shiftDiffSeries_add_linear_le ha1' hwre
  rw [← hM] at hd1 hd2
  rw [← hZ] at hd1 hd2
  set r₁ : ℂ := shiftDiffSeries a w + (w * (a : ℂ)) * Z with hr₁
  set r₂ : ℂ := shiftDiffSeries (-a) w + (w * ((-a : ℝ) : ℂ)) * Z with hr₂
  have hrem : jonquiereRemainder s θ - jonquiereTangent s * (θ : ℂ)
      = ((2 * ↑Real.pi : ℂ)) ^ (-w) * Complex.Gamma w * (E₁ * r₁ + E₂ * r₂) := by
    rw [jonquiereRemainder, jonquiereTangent, ← hw, ← hE₁, ← hE₂, ← hZ, hr₁, hr₂, ← ha]
    have hane : ((2 * ↑Real.pi : ℂ)) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero]
      push Not
      exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr hpi.ne'⟩
    have hθa : ((θ : ℝ) : ℂ) = (2 * ↑Real.pi) * ((a : ℝ) : ℂ) := by
      rw [ha]
      push_cast
      field_simp
    rw [hθa]
    push_cast
    field_simp
    ring
  rw [hrem]
  have hb1 : ‖r₁‖ ≤ M * |a| ^ 2 := hd1
  have hb2 : ‖r₂‖ ≤ M * |a| ^ 2 := by
    have := hd2
    rwa [abs_neg] at this
  have hstep : ‖E₁ * r₁ + E₂ * r₂‖ ≤ (‖E₁‖ + ‖E₂‖) * (M * |a| ^ 2) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hM0 : 0 ≤ M * |a| ^ 2 := le_trans (norm_nonneg _) hb1
    nlinarith [norm_nonneg E₁, norm_nonneg E₂, hb1, hb2]
  rw [norm_mul, norm_mul]
  have hfin : ‖((2 * (Real.pi : ℂ))) ^ (-w)‖ * ‖Complex.Gamma w‖ * ‖E₁ * r₁ + E₂ * r₂‖
      ≤ ‖((2 * (Real.pi : ℂ))) ^ (-w)‖ * ‖Complex.Gamma w‖ * ((‖E₁‖ + ‖E₂‖) * (M * |a| ^ 2)) := by
    refine mul_le_mul_of_nonneg_left hstep ?_
    positivity
  refine hfin.trans ?_
  rw [jonquiereTangentConst, ← hw, ← hE₁, ← hE₂, ← hM, abs_of_pos ha0, ha]
  field_simp
  ring_nf
  exact le_rfl

end RHTower
