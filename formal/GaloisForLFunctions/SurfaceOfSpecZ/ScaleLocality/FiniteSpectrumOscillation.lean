import GaloisForLFunctions.RHTower.GaussianCentralGapExtremalSignChanges

/-!
# Growing oscillation of a finite conjugate spectrum

A finite exponential sum with conjugate coefficients is real. If its top
real part is positive and no frequency is zero, its negative excursions
have exponential size and bounded gaps. The proof applies uniform Fourier
coefficient extraction after the lower real parts have decayed.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

private theorem finite_sum_cexp_real (S : Finset ℂ) (c : ℂ → ℂ)
    (hS : ∀ z ∈ S, conj z ∈ S) (hc : ∀ z ∈ S, c (conj z) = conj (c z))
    (b t : ℝ) :
    (((∑ z ∈ S, c z * Complex.exp ((z - b) * t)).re : ℝ) : ℂ) =
      ∑ z ∈ S, c z * Complex.exp ((z - b) * t) := by
  classical
  have he : conj (∑ z ∈ S, c z * Complex.exp ((z - b) * t)) =
      ∑ z ∈ S, c z * Complex.exp ((z - b) * t) := by
    rw [map_sum]
    refine Finset.sum_bij (fun z _ => conj z) hS ?_ ?_ ?_
    · intro z hz w hw hzw
      simpa only [Complex.conj_conj] using congrArg conj hzw
    · intro z hz
      exact ⟨conj z, hS z hz, Complex.conj_conj z⟩
    · intro z hz
      rw [map_mul, ← Complex.exp_conj, map_mul, map_sub, Complex.conj_ofReal,
        Complex.conj_ofReal, hc z hz]
  exact Complex.ext rfl (by simpa using (Complex.conj_eq_iff_im.mp he).symm)

private theorem tendsto_cexp_mul_zero {z : ℂ} (hz : z.re < 0) :
    Tendsto (fun t : ℝ => Complex.exp (z * t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hz)
  simpa only [Function.comp_def, id_eq, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using h

/-- A real shift of the exponents extracts the corresponding exponential scale. -/
theorem finite_sum_cexp_scale (S : Finset ℂ) (c : ℂ → ℂ) (b t : ℝ) :
    (∑ z ∈ S, c z * Complex.exp ((z - (b : ℂ)) * t)).re * Real.exp (b * t) =
      (∑ z ∈ S, c z * Complex.exp (z * t)).re := by
  have he : (∑ z ∈ S, c z * Complex.exp ((z - (b : ℂ)) * t)) *
      (Real.exp (b * t) : ℂ) = ∑ z ∈ S, c z * Complex.exp (z * t) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Complex.ofReal_exp, Complex.ofReal_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using congrArg Complex.re he

/-- A nonzero top coefficient forces negative excursions at the top exponential scale. -/
theorem finite_spectrum_dense_negative (S : Finset ℂ) (c : ℂ → ℂ)
    (hS : ∀ z ∈ S, conj z ∈ S) (hc : ∀ z ∈ S, c (conj z) = conj (c z))
    (hreal : ∀ z ∈ S, z.im ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hc₀ : c z₀ ≠ 0)
    (hmax : ∀ z ∈ S, z.re ≤ z₀.re) :
    ∃ L ε U : ℝ, 0 < L ∧ 0 < ε ∧ ∀ T : ℝ, U ≤ T →
      ∃ t ∈ Icc T (T + L),
        (∑ z ∈ S, c z * Complex.exp (z * t)).re < -ε * Real.exp (z₀.re * t) := by
  classical
  let g : ℝ → ℝ := fun t => (∑ z ∈ S, c z * Complex.exp ((z - z₀.re) * t)).re
  let d : S → ℂ := fun z => if (z : ℂ).re = z₀.re then -c z else 0
  let μ : S → ℝ := fun z => (z : ℂ).im
  have hg : Continuous g := by unfold g; fun_prop
  have hlim : Tendsto (fun t : ℝ => (g t : ℂ) +
      ∑' z : S, d z * Complex.exp ((μ z : ℂ) * I * t)) atTop (𝓝 0) := by
    have he (t : ℝ) : (g t : ℂ) +
        ∑' z : S, d z * Complex.exp ((μ z : ℂ) * I * t) =
        ∑ z ∈ S, if z.re = z₀.re then 0 else c z * Complex.exp ((z - z₀.re) * t) := by
      rw [show (g t : ℂ) = ∑ z ∈ S, c z * Complex.exp ((z - z₀.re) * t) from
        finite_sum_cexp_real S c hS hc z₀.re t, tsum_fintype]
      change (∑ z ∈ S, c z * Complex.exp ((z - z₀.re) * t)) +
        (∑ z : S, (if (z : ℂ).re = z₀.re then -c z else 0) *
          Complex.exp (((z : ℂ).im : ℂ) * I * t)) = _
      have hsum : (∑ z : S, (if (z : ℂ).re = z₀.re then -c z else 0) *
          Complex.exp (((z : ℂ).im : ℂ) * I * t)) =
          ∑ z ∈ S, (if z.re = z₀.re then -c z else 0) *
            Complex.exp ((z.im : ℂ) * I * t) := by
        refine Finset.sum_bij (fun z _ => (z : ℂ)) (fun z _ => z.2) ?_ ?_ (fun _ _ => rfl)
        · intro z hz w hw hzw
          exact Subtype.ext hzw
        · intro z hz
          exact ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩
      rw [hsum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases htop : z.re = z₀.re
      · have hz : z - (z₀.re : ℂ) = (z.im : ℂ) * I := by
          apply Complex.ext <;> simp [htop]
        simp only [htop, if_true, hz, neg_mul, add_neg_cancel]
      · simp only [htop, if_false, zero_mul, add_zero]
    simp_rw [he]
    have ht : ∀ z ∈ S, Tendsto (fun t : ℝ =>
        if z.re = z₀.re then (0 : ℂ) else c z * Complex.exp ((z - z₀.re) * t)) atTop (𝓝 0) := by
      intro z hz
      by_cases htop : z.re = z₀.re
      · simpa only [htop, if_true] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
      · have hn : (z - (z₀.re : ℂ)).re < 0 := by
          simp only [Complex.sub_re, Complex.ofReal_re]
          exact sub_neg.mpr (lt_of_le_of_ne (hmax z hz) htop)
        simpa only [htop, if_false, mul_zero] using (tendsto_cexp_mul_zero hn).const_mul (c z)
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum S ht
  have hzero : (∑' z : S, if μ z = 0 then d z else 0) = 0 := by
    rw [tsum_fintype]
    exact Finset.sum_eq_zero fun z _ => if_neg (hreal z z.2)
  have hfreq : (∑' z : S, if μ z = z₀.im then d z else 0) ≠ 0 := by
    rw [tsum_fintype, Finset.sum_eq_single (⟨z₀, hz₀⟩ : S)]
    · simpa only [μ, d, if_true] using neg_ne_zero.mpr hc₀
    · intro z hz hne
      by_cases hi : μ z = z₀.im
      · rw [if_pos hi]
        change (if (z : ℂ).re = z₀.re then -c z else 0) = 0
        apply if_neg
        intro hr
        exact hne (Subtype.ext (Complex.ext hr hi))
      · exact if_neg hi
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  obtain ⟨L, ε, U, hL, hε, hwin⟩ :=
    _root_.RHTower.exists_dense_sign_changes_of_tendsto_add_tsum hg d (Summable.of_finite)
      μ hlim hzero hfreq
  refine ⟨L, ε, U, hL, hε, fun T hT => ?_⟩
  obtain ⟨t, ht, hneg⟩ := (hwin T hT).2
  refine ⟨t, ht, ?_⟩
  have hscale : g t * Real.exp (z₀.re * t) =
      (∑ z ∈ S, c z * Complex.exp (z * t)).re := by
    exact finite_sum_cexp_scale S c z₀.re t
  rw [← hscale]
  exact mul_lt_mul_of_pos_right hneg (Real.exp_pos _)

#print axioms finite_spectrum_dense_negative

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
