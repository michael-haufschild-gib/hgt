import GaloisForLFunctions.HTGeometry.DigammaFieldValuationRational

/-!
# Flat functions on a right half-plane

A function is *flat* to the right of `σ₀` if on every vertical line there it decays faster than every
power of the height.  Flatness is stable under differences, under multiplication and division by a
nonzero polynomial — hence under multiplication by a nonzero rational function, in both directions —
and under the unit translation, which only moves the line further right.  No nonzero rational
function is flat.

These are the closure properties of the space of asymptotically invisible elements: a differential
relation whose value is flat is exactly one that the algebraic-logarithmic residue cannot see.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- A function is flat to the right of `σ₀` when `t^N · ‖A(σ + it)‖ → 0` for every power `N` and
every line `σ ≥ σ₀`. -/
def IsVertFlat (σ₀ : ℝ) (A : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, ∀ σ : ℝ, σ₀ ≤ σ →
    Tendsto (fun t : ℝ => t ^ N * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop (nhds 0)

theorem IsVertFlat.sub {σ₀ : ℝ} {A B : ℂ → ℂ} (hA : IsVertFlat σ₀ A) (hB : IsVertFlat σ₀ B) :
    IsVertFlat σ₀ (fun s => A s - B s) := by
  intro N σ hσ
  have h := (hA N σ hσ).add (hB N σ hσ)
  rw [add_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hnorm : ‖A ((σ : ℂ) + (t : ℂ) * Complex.I) - B ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ + ‖B ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
      norm_sub_le _ _
    have hpow : (0 : ℝ) ≤ t ^ N := pow_nonneg ht N
    calc t ^ N * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I) - B ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ t ^ N * (‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            + ‖B ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := mul_le_mul_of_nonneg_left hnorm hpow
      _ = t ^ N * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            + t ^ N * ‖B ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by ring

/-- The height dominates the modulus on a vertical line. -/
theorem norm_vertical_le {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ᶠ t : ℝ in atTop, ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ (1 + σ) * t := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have h : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
  have h1 : ‖(σ : ℂ)‖ = σ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ]
  have h2 : ‖(t : ℂ) * Complex.I‖ = t := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0]
  rw [h1, h2] at h
  nlinarith

/-- A polynomial grows at most like a power of the height on a vertical line. -/
theorem eventually_norm_eval_le {σ : ℝ} (hσ : 0 ≤ σ) (p : Polynomial ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * t ^ p.natDegree := by
  refine ⟨(‖p.leadingCoeff‖ + 1) * (1 + σ) ^ p.natDegree + 1, by positivity, ?_⟩
  have hlead := tendsto_eval_div_pow_natDegree_vertical σ p
  have hbound : ∀ᶠ t : ℝ in atTop,
      ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖ ≤ ‖p.leadingCoeff‖ + 1 := by
    have := hlead.norm
    have hlt : ∀ᶠ t : ℝ in atTop,
        ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖ < ‖p.leadingCoeff‖ + 1 :=
      this.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [hlt] with t ht using ht.le
  filter_upwards [hbound, norm_vertical_le hσ, eventually_vertical_ne_zero σ,
    eventually_ge_atTop (1 : ℝ)] with t hb hv hne ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hpow : ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖ ≤ ((1 + σ) * t) ^ p.natDegree := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hv _
  have hnum : ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (‖p.leadingCoeff‖ + 1) * ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖ := by
    have hdiv : ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        / ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖ ≤ ‖p.leadingCoeff‖ + 1 := by
      rwa [← norm_div]
    have hp : (0 : ℝ) < ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖ :=
      norm_pos_iff.mpr (pow_ne_zero _ hne)
    exact (div_le_iff₀ hp).mp hdiv
  have hmul : (‖p.leadingCoeff‖ + 1) * ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖
      ≤ (‖p.leadingCoeff‖ + 1) * ((1 + σ) * t) ^ p.natDegree :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hsplit : ((1 + σ) * t) ^ p.natDegree = (1 + σ) ^ p.natDegree * t ^ p.natDegree :=
    mul_pow _ _ _
  have hfinal : (‖p.leadingCoeff‖ + 1) * ((1 + σ) ^ p.natDegree * t ^ p.natDegree)
      ≤ ((‖p.leadingCoeff‖ + 1) * (1 + σ) ^ p.natDegree + 1) * t ^ p.natDegree := by
    have hnn : (0 : ℝ) ≤ t ^ p.natDegree := pow_nonneg ht0 _
    nlinarith
  calc ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (‖p.leadingCoeff‖ + 1) * ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖ := hnum
    _ ≤ (‖p.leadingCoeff‖ + 1) * ((1 + σ) * t) ^ p.natDegree := hmul
    _ = (‖p.leadingCoeff‖ + 1) * ((1 + σ) ^ p.natDegree * t ^ p.natDegree) := by rw [hsplit]
    _ ≤ ((‖p.leadingCoeff‖ + 1) * (1 + σ) ^ p.natDegree + 1) * t ^ p.natDegree := hfinal

/-- A nonzero polynomial is bounded below by a power of the height on a vertical line. -/
theorem eventually_norm_eval_ge {σ : ℝ} {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop,
      c * ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ p.natDegree
        ≤ ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hlead : ‖p.leadingCoeff‖ ≠ 0 := norm_ne_zero_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hpos : 0 < ‖p.leadingCoeff‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hlead)
  refine ⟨‖p.leadingCoeff‖ / 2, by positivity, ?_⟩
  have hconv := (tendsto_eval_div_pow_natDegree_vertical σ p).norm
  have hgt : ∀ᶠ t : ℝ in atTop, ‖p.leadingCoeff‖ / 2
      < ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖ :=
    hconv.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hgt, eventually_vertical_ne_zero σ] with t ht hne
  have hp0 : (0 : ℝ) < ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖ :=
    norm_pos_iff.mpr (pow_ne_zero _ hne)
  have hdiv : ‖p.leadingCoeff‖ / 2 * ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree‖
      ≤ ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rw [norm_div] at ht
    exact le_of_lt ((lt_div_iff₀ hp0).mp ht)
  rwa [norm_pow] at hdiv

/-- Flatness survives multiplication by a polynomial. -/
theorem IsVertFlat.mul_poly {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {A : ℂ → ℂ} (hA : IsVertFlat σ₀ A)
    (p : Polynomial ℂ) : IsVertFlat σ₀ (fun s => p.eval s * A s) := by
  intro N σ hσ
  obtain ⟨C, hC, hbound⟩ := eventually_norm_eval_le (le_trans hσ₀ hσ) p
  have hA' := hA (N + p.natDegree) σ hσ
  have hmul : Tendsto (fun t : ℝ => C * (t ^ (N + p.natDegree)
      * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖)) atTop (nhds 0) := by
    have := hA'.const_mul C
    simpa using this
  refine squeeze_zero' ?_ ?_ hmul
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with t hb ht
  have hpow : (0 : ℝ) ≤ t ^ N := pow_nonneg ht N
  have hnormA : (0 : ℝ) ≤ ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  have hstep : t ^ N * (‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖)
      ≤ t ^ N * (C * t ^ p.natDegree * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
    have := mul_le_mul_of_nonneg_right hb hnormA
    exact mul_le_mul_of_nonneg_left this hpow
  have heq : t ^ N * (C * t ^ p.natDegree * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖)
      = C * (t ^ (N + p.natDegree) * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
    rw [pow_add]
    ring
  calc t ^ N * ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I) * A ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = t ^ N * (‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by rw [norm_mul]
    _ ≤ t ^ N * (C * t ^ p.natDegree * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := hstep
    _ = C * (t ^ (N + p.natDegree) * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := heq

/-- Flatness survives division by a nonzero polynomial. -/
theorem IsVertFlat.div_poly {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {A : ℂ → ℂ} (hA : IsVertFlat σ₀ A)
    {p : Polynomial ℂ} (hp : p ≠ 0) : IsVertFlat σ₀ (fun s => A s / p.eval s) := by
  intro N σ hσ
  obtain ⟨c, hc, hbound⟩ := eventually_norm_eval_ge (σ := σ) hp
  have hA' := hA N σ hσ
  have hmul : Tendsto (fun t : ℝ => c⁻¹ * (t ^ N * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖))
      atTop (nhds 0) := by
    have := hA'.const_mul c⁻¹
    simpa using this
  refine squeeze_zero' ?_ ?_ hmul
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ), norm_vertical_le (le_trans hσ₀ hσ)]
    with t hb ht hv
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hnorm1 : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    have him : ‖((σ : ℂ) + (t : ℂ) * Complex.I).im‖ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      Complex.abs_im_le_norm _
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [hval, Real.norm_eq_abs, abs_of_nonneg ht0] at him
    linarith
  have hge : c ≤ ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have hpow : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ p.natDegree :=
      one_le_pow₀ hnorm1
    nlinarith
  have hppos : (0 : ℝ) < ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := lt_of_lt_of_le hc hge
  have hquot : ‖A ((σ : ℂ) + (t : ℂ) * Complex.I) / p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ c⁻¹ * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rw [norm_div]
    rw [div_le_iff₀ hppos]
    have hstep : c⁻¹ * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * c
        ≤ c⁻¹ * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          * ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have hnn : (0 : ℝ) ≤ c⁻¹ * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by positivity
      exact mul_le_mul_of_nonneg_left hge hnn
    have hcc : c⁻¹ * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * c
        = ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
      field_simp
    linarith [hstep, hcc.symm.le]
  have hpow : (0 : ℝ) ≤ t ^ N := pow_nonneg ht0 N
  calc t ^ N * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)
        / p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ t ^ N * (c⁻¹ * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖) :=
        mul_le_mul_of_nonneg_left hquot hpow
    _ = c⁻¹ * (t ^ N * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by ring

/-- Flatness survives the unit translation: the shifted line lies further right. -/
theorem IsVertFlat.shift {σ₀ : ℝ} {A : ℂ → ℂ} (hA : IsVertFlat σ₀ A) :
    IsVertFlat σ₀ (fun s => A (s + 1)) := by
  intro N σ hσ
  have h := hA N (σ + 1) (by linarith)
  refine h.congr fun t => ?_
  have hcast : (((σ + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I
      = ((σ : ℂ) + (t : ℂ) * Complex.I) + 1 := by
    push_cast
    ring
  rw [hcast]

/-- **A nonzero polynomial is not flat.**  Its modulus on a vertical line is bounded below by a
constant. -/
theorem not_isVertFlat_polynomial {σ₀ : ℝ} {p : Polynomial ℂ} (hp : p ≠ 0) :
    ¬ IsVertFlat σ₀ (fun s => p.eval s) := by
  intro hflat
  obtain ⟨c, hc, hbound⟩ := eventually_norm_eval_ge (σ := max σ₀ 0) hp
  have h := hflat 0 (max σ₀ 0) (le_max_left _ _)
  simp only [pow_zero, one_mul] at h
  have hlim : ∀ᶠ t : ℝ in atTop,
      ‖p.eval ((((max σ₀ 0 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ < c :=
    h.eventually (eventually_lt_nhds hc)
  obtain ⟨t, ⟨hb, hlt⟩, ht⟩ := ((hbound.and hlim).and (eventually_ge_atTop (1 : ℝ))).exists
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hnorm1 : (1 : ℝ) ≤ ‖(((max σ₀ 0 : ℝ)) : ℂ) + (t : ℂ) * Complex.I‖ := by
    have him : ‖((((max σ₀ 0 : ℝ)) : ℂ) + (t : ℂ) * Complex.I).im‖
        ≤ ‖(((max σ₀ 0 : ℝ)) : ℂ) + (t : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _
    have hval : ((((max σ₀ 0 : ℝ)) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [hval, Real.norm_eq_abs, abs_of_nonneg ht0] at him
    linarith
  have hpow : (1 : ℝ) ≤ ‖(((max σ₀ 0 : ℝ)) : ℂ) + (t : ℂ) * Complex.I‖ ^ p.natDegree :=
    one_le_pow₀ hnorm1
  nlinarith

end GaloisForLFunctions
