import GaloisForLFunctions.HTGeometry.RatApproximant
import GaloisForLFunctions.HTGeometry.GammaShiftTubeDatumAlgebra

/-!
# From a rational approximant to a boundary datum

A function approximated to every order by rational functions is either negligible or has a boundary
datum.  The mechanism is a single comparison of exponents: if the approximant of order `N` were
smaller than `t^{-N}` the function would be negligible at that order, so its degree difference `ω`
satisfies `ω > -N`; and then the approximation error, being `O(t^{-N})`, is smaller than the
approximant's own leading order.  The datum of the function is therefore the datum of the
approximant, which is the datum of a quotient of polynomials.
-/

open Filter Set Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A tube bound of one fixed order. -/
def IsTubeBigO (M : ℝ) (N : ℕ) (f : ℂ → ℂ) : Prop :=
  ∃ C T : ℝ, ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
    ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / t ^ N

theorem IsTubeBigO.mono_tube {M M' : ℝ} (hMM : M' ≤ M) {N : ℕ} {f : ℂ → ℂ}
    (hf : IsTubeBigO M N f) : IsTubeBigO M' N f := by
  obtain ⟨C, T, hb⟩ := hf
  exact ⟨C, T, fun σ t hσ hσM ht => hb σ t hσ (le_trans hσM hMM) ht⟩

theorem isVerticallyNegligible_of_forall_isTubeBigO {f : ℂ → ℂ}
    (h : ∀ M : ℝ, 0 < M → ∀ N : ℕ, IsTubeBigO M N f) : IsVerticallyNegligible f := by
  intro M hM N
  obtain ⟨C, T, hb⟩ := h M hM N
  refine ⟨max C 0, max T 2, le_max_right _ _, le_max_right _ _, fun σ t hσ hσM ht => ?_⟩
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have htpos : (0 : ℝ) < t ^ N := by positivity
  refine le_trans (hb σ t hσ hσM (le_trans (le_max_left _ _) ht)) ?_
  exact div_le_div_of_nonneg_right (le_max_left _ _) htpos.le

/-- A function that is not negligible fails one tube bound outright. -/
theorem exists_not_isTubeBigO {f : ℂ → ℂ} (h : ¬ IsVerticallyNegligible f) :
    ∃ (M : ℝ) (N : ℕ), 0 < M ∧ ¬ IsTubeBigO M N f := by
  by_contra hcon
  refine h (isVerticallyNegligible_of_forall_isTubeBigO fun M hM N => ?_)
  by_contra hno
  exact hcon ⟨M, N, hM, hno⟩

/-- Tube limits restrict to smaller tubes. -/
theorem TubeLimit.mono_tube {M M' : ℝ} (hMM : M' ≤ M) {f : ℝ → ℝ → ℂ} {c : ℂ}
    (h : TubeLimit M f c) : TubeLimit M' f c := by
  intro ε hε
  obtain ⟨T, hT⟩ := h ε hε
  exact ⟨T, fun σ t hσ hσM ht => hT σ t hσ (le_trans hσM hMM) ht⟩

theorem HasShiftTubeDatum.mono_tube {M M' lam : ℝ} (hMM : M' ≤ M) {φ : ℝ → ℝ → ℂ}
    {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ} (h : HasShiftTubeDatum M lam φ d ω b c) :
    HasShiftTubeDatum M' lam φ d ω b c :=
  ⟨h.1, h.2.mono_tube hMM⟩

/-- The modulus of the boundary shape of a degree difference. -/
theorem norm_shape_natDegree_eq (σ : ℝ) {t : ℝ} (ht : 0 < t) (dp dq : ℕ) :
    ‖gammaShiftShape 0 σ 0 ((dp : ℝ) - (dq : ℝ)) 0 t‖
      = ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ dp / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ dq := by
  have hpos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
    norm_pos_iff.mpr (vertical_ne_zero_of_pos ht)
  rw [gammaShiftShape, zpow_zero, one_mul, zpow_zero, mul_one, norm_cpow_real_vertical,
    Real.rpow_sub hpos, Real.rpow_natCast, Real.rpow_natCast]

/-- **A function with rational approximants is negligible or has a boundary datum.**  The exponent
is the degree difference of an approximant and the residue is its leading coefficient ratio. -/
theorem exists_hasShiftTubeDatum_of_ratApprox {f : ℂ → ℂ} (hf : HasRatApprox f)
    (hnn : ¬ IsVerticallyNegligible f) {M : ℝ} (hM : 0 < M) :
    ∃ (ω : ℝ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0 (fun σ t => f ((σ : ℂ) + (t : ℂ) * Complex.I)) 0 ω 0 c := by
  classical
  obtain ⟨M₀, N, hM₀, hnot⟩ := exists_not_isTubeBigO hnn
  set M' : ℝ := max M M₀ with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le hM (le_max_left _ _)
  have hMM' : M ≤ M' := le_max_left _ _
  have hnot' : ¬ IsTubeBigO M' N f := fun hb => hnot (hb.mono_tube (le_max_right _ _))
  obtain ⟨p, q, C, T, hq, hC, hT, hb⟩ := hf M' hM'pos N
  obtain ⟨cq, Tq, hcq, hTq, hlow⟩ := exists_lower_bound_polyEval hq
  obtain ⟨Cp, hCp, hup⟩ := exists_norm_polynomial_le p
  -- the approximant is nonzero
  have hp : p ≠ 0 := by
    intro h0
    refine hnot' ⟨C, max T 2, fun σ t hσ hσM ht => ?_⟩
    have h := hb σ t hσ hσM (le_trans (le_max_left _ _) ht)
    rw [h0] at h
    simpa using h
  -- its degree difference beats the approximation order
  have hdeg : q.natDegree < p.natDegree + N := by
    by_contra hcon0
    have hcon : p.natDegree + N ≤ q.natDegree := Nat.not_lt.mp hcon0
    refine hnot' ⟨C + Cp * (1 + M') ^ p.natDegree / cq, max (max T Tq) 2,
      fun σ t hσ hσM ht => ?_⟩
    have ht2 : (2 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have htpos : (0 : ℝ) < t := by linarith
    have h1 := hb σ t hσ hσM (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht)
    have h2 := hlow σ t hσ hσM (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht)
    set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
    have hsnorm : ‖s‖ ≤ (1 + M') * t := norm_vertical_le_of_le hσ hσM ht1
    have hsone : (1 : ℝ) ≤ ‖s‖ := le_trans ht1 (norm_vertical_ge_im σ t)
    have hqpos : (0 : ℝ) < ‖Polynomial.eval s q‖ := by
      have : (0 : ℝ) < cq * t ^ q.natDegree := by positivity
      linarith
    -- the approximant itself is already of the failing order
    have hA : ‖Polynomial.eval s p / Polynomial.eval s q‖
        ≤ Cp * (1 + M') ^ p.natDegree / cq / t ^ N := by
      rw [norm_div, div_le_div_iff₀ hqpos (by positivity)]
      have hnum : ‖Polynomial.eval s p‖ ≤ Cp * ((1 + M') * t) ^ p.natDegree := by
        refine le_trans (hup s hsone) ?_
        have := pow_le_pow_left₀ (norm_nonneg s) hsnorm p.natDegree
        nlinarith
      have hpowle : t ^ (p.natDegree + N) ≤ t ^ q.natDegree :=
        pow_le_pow_right₀ ht1 hcon
      have hexp : Cp * ((1 + M') * t) ^ p.natDegree * t ^ N
          = Cp * (1 + M') ^ p.natDegree * t ^ (p.natDegree + N) := by
        rw [mul_pow, pow_add]
        ring
      have hcqpos : (0 : ℝ) < cq := hcq
      have hstep : ‖Polynomial.eval s p‖ * t ^ N
          ≤ Cp * (1 + M') ^ p.natDegree * t ^ q.natDegree := by
        calc ‖Polynomial.eval s p‖ * t ^ N
            ≤ (Cp * ((1 + M') * t) ^ p.natDegree) * t ^ N := by
              have hp0 : (0 : ℝ) ≤ t ^ N := by positivity
              exact mul_le_mul_of_nonneg_right hnum hp0
          _ = Cp * (1 + M') ^ p.natDegree * t ^ (p.natDegree + N) := hexp
          _ ≤ Cp * (1 + M') ^ p.natDegree * t ^ q.natDegree := by
              have hc0 : (0 : ℝ) ≤ Cp * (1 + M') ^ p.natDegree := by positivity
              exact mul_le_mul_of_nonneg_left hpowle hc0
      have hfin : Cp * (1 + M') ^ p.natDegree * t ^ q.natDegree
          ≤ Cp * (1 + M') ^ p.natDegree / cq * ‖Polynomial.eval s q‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hcq]
        have hc0 : (0 : ℝ) ≤ Cp * (1 + M') ^ p.natDegree := by positivity
        nlinarith
      linarith
    have hsplit : ‖f s‖ ≤ ‖f s - Polynomial.eval s p / Polynomial.eval s q‖
        + ‖Polynomial.eval s p / Polynomial.eval s q‖ := by
      have := norm_add_le (f s - Polynomial.eval s p / Polynomial.eval s q)
        (Polynomial.eval s p / Polynomial.eval s q)
      simpa using this
    have hsum : C / t ^ N + Cp * (1 + M') ^ p.natDegree / cq / t ^ N
        = (C + Cp * (1 + M') ^ p.natDegree / cq) / t ^ N := by ring
    linarith
  -- the datum of the approximant
  have hdat := hasShiftTubeDatum_multiMonomial (M := M') hM'pos (r := 0) (fun _ => 0)
    (fun i => i.elim0) (fun _ => 0) (c := 1) one_ne_zero (q := p) (p := q) hp hq 0
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, one_mul, mul_one,
    zpow_zero, zero_add] at hdat
  refine ⟨(p.natDegree : ℝ) - (q.natDegree : ℝ), p.leadingCoeff / q.leadingCoeff, hdat.1, ?_⟩
  refine HasShiftTubeDatum.mono_tube hMM' ⟨hdat.1, ?_⟩
  -- the error is smaller than the approximant's leading order
  have hgtend : Tendsto (fun t : ℝ => C * (1 + M') ^ q.natDegree / t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have herr : TubeLimit M' (fun σ t =>
      (f ((σ : ℂ) + (t : ℂ) * Complex.I)
        - Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) p
          / Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) q)
      / gammaShiftShape 0 σ 0 ((p.natDegree : ℝ) - (q.natDegree : ℝ)) 0 t) 0 := by
    refine tubeLimit_of_squeeze (T₀ := max T 2)
      (g := fun t : ℝ => C * (1 + M') ^ q.natDegree / t) (fun σ t hσ hσM ht => ?_) hgtend
    have ht2 : (2 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have htpos : (0 : ℝ) < t := by linarith
    have h1 := hb σ t hσ hσM (le_trans (le_max_left _ _) ht)
    set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
    have hsnorm : ‖s‖ ≤ (1 + M') * t := norm_vertical_le_of_le hσ hσM ht1
    have hsone : (1 : ℝ) ≤ ‖s‖ := le_trans ht1 (norm_vertical_ge_im σ t)
    have hnumq : ‖s‖ ^ q.natDegree ≤ ((1 + M') * t) ^ q.natDegree :=
      pow_le_pow_left₀ (norm_nonneg s) hsnorm q.natDegree
    have hkey : ‖f s - Polynomial.eval s p / Polynomial.eval s q‖ * ‖s‖ ^ q.natDegree
        ≤ (C / t ^ N) * ((1 + M') * t) ^ q.natDegree :=
      mul_le_mul h1 hnumq (by positivity) (by positivity)
    have hCM : (C / t ^ N) * ((1 + M') * t) ^ q.natDegree
        = C * (1 + M') ^ q.natDegree * (t ^ q.natDegree / t ^ N) := by
      rw [mul_pow]
      field_simp
    have hfrac : t ^ q.natDegree / t ^ N * t ≤ t ^ p.natDegree := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc t ^ q.natDegree * t = t ^ (q.natDegree + 1) := by rw [pow_succ]
        _ ≤ t ^ (p.natDegree + N) := pow_le_pow_right₀ ht1 (by omega)
        _ = t ^ p.natDegree * t ^ N := by rw [pow_add]
    have hpowle : t ^ p.natDegree ≤ ‖s‖ ^ p.natDegree :=
      pow_le_pow_left₀ (by positivity) (norm_vertical_ge_im σ t) p.natDegree
    have hgoal : ‖f s - Polynomial.eval s p / Polynomial.eval s q‖ * ‖s‖ ^ q.natDegree * t
        ≤ C * (1 + M') ^ q.natDegree * ‖s‖ ^ p.natDegree := by
      have hC0 : (0 : ℝ) ≤ C * (1 + M') ^ q.natDegree := by positivity
      calc ‖f s - Polynomial.eval s p / Polynomial.eval s q‖ * ‖s‖ ^ q.natDegree * t
          ≤ (C * (1 + M') ^ q.natDegree * (t ^ q.natDegree / t ^ N)) * t := by
            have := mul_le_mul_of_nonneg_right (le_trans hkey (le_of_eq hCM)) htpos.le
            linarith
        _ = C * (1 + M') ^ q.natDegree * (t ^ q.natDegree / t ^ N * t) := by ring
        _ ≤ C * (1 + M') ^ q.natDegree * ‖s‖ ^ p.natDegree :=
            mul_le_mul_of_nonneg_left (le_trans hfrac hpowle) hC0
    rw [norm_div, norm_shape_natDegree_eq σ htpos p.natDegree q.natDegree,
      div_div_eq_mul_div, div_le_div_iff₀ (by positivity) htpos]
    exact hgoal
  have hsum := hdat.2.add herr
  rw [add_zero] at hsum
  refine hsum.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have htpos : (0 : ℝ) < t := by linarith
  have hshape : gammaShiftShape 0 σ 0 ((p.natDegree : ℝ) - (q.natDegree : ℝ)) 0 t ≠ 0 := by
    have hnorm := norm_shape_natDegree_eq σ htpos p.natDegree q.natDegree
    have hspos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      norm_pos_iff.mpr (vertical_ne_zero_of_pos htpos)
    refine norm_pos_iff.mp ?_
    rw [hnorm]
    positivity
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
