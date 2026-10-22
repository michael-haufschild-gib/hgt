import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorSchwarzMonodromy

/-!
# The defect trace of the Deninger divisor flow detects the Riemann hypothesis

The displacement Ward identity produces, at every divisor copy, the defect factor
`λ_{Rq} - conj λ_q`, whose spectral-coordinate form is `μ - conj μ = 2i·Im μ`
(`xiSpectralPoint_sub_conj`).  This file sums that factor against the third resolvent power and
proves that the resulting **defect trace**

`Δ(z) = Σ' q, (μ_q - conj μ_q) · ((μ_q - z)⁻¹)³`

is an absolutely convergent, everywhere-defined function of `z` which vanishes identically
**iff** the Riemann hypothesis holds:

* `RH ⟹ Δ ≡ 0` is termwise: on the line every spectral point is real.
* `Δ ≡ 0 ⟹ RH` is a pole-extraction argument, carried out in full: a non-real spectral point
  `μ₀` is isolated (the divisor is locally finite), the copies at `μ₀` contribute
  `(Nat.card) · (μ₀ - conj μ₀) · (μ₀ - z)⁻³`, and every other copy is dominated by a summable
  `C/‖μ‖²` majorant uniformly for `z` near `μ₀`; taking `z = μ₀ + t` with `t` small makes the
  leading block larger than the whole tail, so `Δ(z) ≠ 0`.

The third power is the smallest making the twisted terms absolutely summable
(`|μ - conj μ| ≤ 2|μ|` costs one power of the `Σ 1/|μ|²` budget).  The trace is the first object
in this lane whose vanishing is RH while each ingredient — the twist factor from the Ward
identity, the resolvent test family from the Lefschetz trace — is unconditional.

No positivity, zero-location, or RH premise enters except where `RiemannHypothesis` is the
explicit hypothesis or conclusion.
-/

noncomputable section

open Complex

namespace RHTower

/-- The Ward defect factor in spectral coordinates: `μ - conj μ = I · (λ_{Rq} - conj λ_q)`.
The twist weight of the defect trace is exactly the displacement factor of the Ward identity,
rotated by `I`. -/
theorem xiSpectralPoint_sub_conj (q : XiZeroCopy) :
    xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q) =
      Complex.I * (deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) -
        (starRingEnd ℂ) (deningerDivisorThetaEigen q)) := by
  have hR : deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) =
      1 - deningerDivisorThetaEigen q := by
    linear_combination deningerDivisorThetaEigen_add_reflect q
  have hq : deningerDivisorThetaEigen q = (q.1 : ℂ) := rfl
  rw [hR, hq, xiSpectralPoint]
  simp only [map_mul, map_sub, map_neg, Complex.conj_I, map_one, map_ofNat,
    map_div₀]
  ring

/-- Imaginary part of the spectral coordinate: `Im μ = 1/2 - Re ρ`, the critical-line
displacement. -/
theorem xiSpectralPoint_im_divisorDefect (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
  simp [xiSpectralPoint, Complex.mul_im, Complex.sub_re, Complex.sub_im]

/-- Every closed spectral norm ball contains only finitely many divisor copies. -/
theorem finite_setOf_norm_xiSpectralPoint_le (R : ℝ) :
    {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ R}.Finite := by
  have hLF : LocallyFiniteSupport (MeromorphicOn.divisor xi Set.univ).toFun :=
    Function.locallyFinsupp.locallyFiniteSupport _
  have hS : {ρ : XiDivisorSupport | ‖(ρ : ℂ) - 1 / 2‖ ≤ R}.Finite := by
    apply Set.Finite.of_finite_image _ (Subtype.val_injective.injOn)
    apply Set.Finite.subset (hLF.finite_inter_support_of_isCompact
      (isCompact_closedBall (1 / 2 : ℂ) R))
    rintro w ⟨ρ, hρ, rfl⟩
    refine ⟨?_, ρ.2⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hρ
  apply Set.Finite.subset
    (Set.Finite.biUnion hS (fun ρ _ => Set.finite_range (Sigma.mk ρ)))
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  rw [norm_xiSpectralPoint] at hq
  exact Set.mem_biUnion hq ⟨q.2, rfl⟩

/-- The defect term: the Ward twist factor against the third resolvent power. -/
def deningerDivisorDefectTerm (z : ℂ) (q : XiZeroCopy) : ℂ :=
  (xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q)) *
    ((xiSpectralPoint q - z)⁻¹) ^ (3 : ℕ)

/-- The defect trace. -/
def deningerDivisorDefectTrace (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, deningerDivisorDefectTerm z q

/-- The twist factor is bounded by twice the spectral norm. -/
theorem norm_defectTwist_le (q : XiZeroCopy) :
    ‖xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q)‖ ≤
      2 * ‖xiSpectralPoint q‖ := by
  calc ‖xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q)‖
      ≤ ‖xiSpectralPoint q‖ + ‖(starRingEnd ℂ) (xiSpectralPoint q)‖ :=
        norm_sub_le _ _
    _ = 2 * ‖xiSpectralPoint q‖ := by rw [RCLike.norm_conj]; ring

/-- Resolvent lower bound in the far regime: if `‖μ‖ ≥ 2‖z‖ + 2` then `‖μ - z‖ ≥ ‖μ‖/2`. -/
theorem norm_sub_ge_half_of_far {z μ : ℂ} (hfar : 2 * ‖z‖ + 2 ≤ ‖μ‖) :
    ‖μ‖ / 2 ≤ ‖μ - z‖ := by
  have h1 : ‖μ‖ - ‖z‖ ≤ ‖μ - z‖ := norm_sub_norm_le μ z
  have h2 : 0 ≤ ‖z‖ := norm_nonneg z
  linarith

/-- Far-regime bound: outside a compact spectral ball the defect term is dominated by
`16/‖μ‖²`. -/
theorem norm_deningerDivisorDefectTerm_le_of_far (z : ℂ) (q : XiZeroCopy)
    (hfar : 2 * ‖z‖ + 2 ≤ ‖xiSpectralPoint q‖) :
    ‖deningerDivisorDefectTerm z q‖ ≤ 16 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  set μ := xiSpectralPoint q with hμ
  have hμpos : 0 < ‖μ‖ := by
    have : (0 : ℝ) < 2 * ‖z‖ + 2 := by positivity
    linarith
  have hhalf : ‖μ‖ / 2 ≤ ‖μ - z‖ := norm_sub_ge_half_of_far hfar
  have hinv : ‖(μ - z)⁻¹‖ ≤ 2 / ‖μ‖ := by
    rw [norm_inv]
    have hpos2 : (0 : ℝ) < ‖μ‖ / 2 := by positivity
    calc ‖μ - z‖⁻¹ ≤ (‖μ‖ / 2)⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div]
          exact div_le_div_of_nonneg_left (by norm_num) hpos2 hhalf
      _ = 2 / ‖μ‖ := by rw [inv_div]
  have hterm : ‖deningerDivisorDefectTerm z q‖ ≤
      (2 * ‖μ‖) * (2 / ‖μ‖) ^ (3 : ℕ) := by
    rw [deningerDivisorDefectTerm, norm_mul, norm_pow]
    apply mul_le_mul (norm_defectTwist_le q)
      (pow_le_pow_left₀ (norm_nonneg _) hinv 3)
      (by positivity) (by positivity)
  calc ‖deningerDivisorDefectTerm z q‖ ≤ (2 * ‖μ‖) * (2 / ‖μ‖) ^ (3 : ℕ) := hterm
    _ = 16 * (1 / ‖μ‖ ^ (2 : ℕ)) := by
        field_simp
        ring

/-- The defect terms are absolutely summable at every base point. -/
theorem summable_norm_deningerDivisorDefectTerm (z : ℂ) :
    Summable (fun q : XiZeroCopy => ‖deningerDivisorDefectTerm z q‖) := by
  apply Summable.of_norm_bounded_eventually
    (xiSpectralPoint_inv_sq_summable.mul_left 16)
  filter_upwards [(finite_setOf_norm_xiSpectralPoint_le
    (2 * ‖z‖ + 2)).eventually_cofinite_notMem] with q hq
  simp only [not_le] at hq
  rw [norm_norm]
  exact norm_deningerDivisorDefectTerm_le_of_far z q (le_of_lt hq)

theorem summable_deningerDivisorDefectTerm (z : ℂ) :
    Summable (deningerDivisorDefectTerm z) :=
  (summable_norm_deningerDivisorDefectTerm z).of_norm

/-- **RH kills the defect trace, termwise**: on the critical line every spectral point is
real, so every twist factor vanishes. -/
theorem deningerDivisorDefectTrace_eq_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) (z : ℂ) :
    deningerDivisorDefectTrace z = 0 := by
  have hterm : ∀ q : XiZeroCopy, deningerDivisorDefectTerm z q = 0 := by
    intro q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [deningerDivisorDefectTerm, ht]
    simp [Complex.conj_ofReal]
  rw [deningerDivisorDefectTrace]
  rw [tsum_congr hterm]
  exact tsum_zero

/-- Spectral separation: every point of the plane has a punctured neighbourhood free of
spectral values, uniformly over the multiplicity copies. -/
theorem exists_xiSpectralPoint_separation (μ₀ : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ q : XiZeroCopy,
      xiSpectralPoint q ≠ μ₀ → δ ≤ ‖xiSpectralPoint q - μ₀‖ := by
  have hF : {q : XiZeroCopy |
      ‖xiSpectralPoint q - μ₀‖ ≤ 1 ∧ xiSpectralPoint q ≠ μ₀}.Finite := by
    apply (finite_setOf_norm_xiSpectralPoint_le (1 + ‖μ₀‖)).subset
    intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    calc ‖xiSpectralPoint q‖
        = ‖(xiSpectralPoint q - μ₀) + μ₀‖ := by ring_nf
      _ ≤ ‖xiSpectralPoint q - μ₀‖ + ‖μ₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖μ₀‖ := by linarith [hq.1]
  classical
  set T : Finset ℝ :=
    hF.toFinset.image (fun q => ‖xiSpectralPoint q - μ₀‖) with hT
  have hne : (insert (1 : ℝ) T).Nonempty := ⟨1, Finset.mem_insert_self 1 T⟩
  refine ⟨(insert (1 : ℝ) T).min' hne, ?_, ?_, ?_⟩
  · have hmem := Finset.min'_mem (insert (1 : ℝ) T) hne
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h]; norm_num
    · obtain ⟨q, hqmem, hval⟩ := Finset.mem_image.mp h
      have hne0 : xiSpectralPoint q ≠ μ₀ := (hF.mem_toFinset.mp hqmem).2
      rw [← hval]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hne0)
  · exact Finset.min'_le _ 1 (Finset.mem_insert_self 1 T)
  · intro q hq
    by_cases hle : ‖xiSpectralPoint q - μ₀‖ ≤ 1
    · apply Finset.min'_le
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨q, hF.mem_toFinset.mpr ⟨hle, hq⟩, rfl⟩)
    · have h1 : (insert (1 : ℝ) T).min' hne ≤ 1 :=
        Finset.min'_le _ 1 (Finset.mem_insert_self 1 T)
      linarith [lt_of_not_ge hle]

/-- **Pole extraction: a non-real spectral point makes the defect trace nonzero somewhere.**
The copies at `μ₀` contribute a block `card · (μ₀ - conj μ₀) · (μ₀ - z)⁻³`; all other copies
are dominated, uniformly for `z` near `μ₀`, by one summable majorant.  Choosing `z = μ₀ + t`
with `t` small makes the block beat the tail. -/
theorem exists_deningerDivisorDefectTrace_ne_zero_of_offline
    (q₀ : XiZeroCopy) (him : (xiSpectralPoint q₀).im ≠ 0) :
    ∃ z : ℂ, deningerDivisorDefectTrace z ≠ 0 := by
  classical
  set μ₀ := xiSpectralPoint q₀ with hμ₀
  set c : ℂ := μ₀ - (starRingEnd ℂ) μ₀ with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Complex.sub_conj]
    apply mul_ne_zero _ Complex.I_ne_zero
    rw [Complex.ofReal_ne_zero]
    intro h
    apply him
    linarith [h]
  have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_xiSpectralPoint_separation μ₀
  set R₀ : ℝ := 2 * ‖μ₀‖ + 4 with hR₀
  have hR₀pos : 0 < R₀ := by positivity
  set C : ℝ := 16 + 2 * R₀ ^ (3 : ℕ) * (2 / δ) ^ (3 : ℕ) with hC
  have hCpos : 0 < C := by positivity
  have hCsum : Summable (fun q : XiZeroCopy =>
      C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) :=
    xiSpectralPoint_inv_sq_summable.mul_left C
  set M : ℝ := ∑' q : XiZeroCopy, C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) with hM
  have hM0 : 0 ≤ M := tsum_nonneg (fun q => by positivity)
  -- the test point
  set t : ℝ := min (δ / 4) (min (1 / 2) (‖c‖ / (4 * (M + 1)))) with ht
  have ht0 : 0 < t := by
    apply lt_min (by positivity)
    apply lt_min (by norm_num)
    exact div_pos hcnorm (by linarith)
  have htδ : t ≤ δ / 4 := min_le_left _ _
  have ht1 : t ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have htc : t ≤ ‖c‖ / (4 * (M + 1)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  set z : ℂ := μ₀ + (t : ℂ) with hz
  have hzdist : ‖z - μ₀‖ = t := by
    rw [hz]
    simp [Complex.norm_real, abs_of_pos ht0]
  have hμ₀z : μ₀ - z = -(t : ℂ) := by rw [hz]; ring
  set v : ℂ := c * ((μ₀ - z)⁻¹) ^ (3 : ℕ) with hv
  have hv0 : v ≠ 0 := by
    apply mul_ne_zero hc0
    apply pow_ne_zero
    apply inv_ne_zero
    rw [hμ₀z]
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt ht0))
  have hvnorm : ‖v‖ = ‖c‖ / t ^ (3 : ℕ) := by
    rw [hv, norm_mul, norm_pow, norm_inv, hμ₀z, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht0]
    field_simp
  -- the block at μ₀ and its complement
  set A : Set XiZeroCopy := {q | xiSpectralPoint q = μ₀} with hA
  have hq₀A : q₀ ∈ A := by rw [hA]; exact Set.mem_setOf_eq ▸ rfl
  have hsum := summable_deningerDivisorDefectTerm z
  have hsumA : Summable ((deningerDivisorDefectTerm z) ∘
      (Subtype.val : A → XiZeroCopy)) := hsum.subtype A
  have hsumAc : Summable ((deningerDivisorDefectTerm z) ∘
      (Subtype.val : ↥Aᶜ → XiZeroCopy)) := hsum.subtype Aᶜ
  have htermA : ∀ q : A, deningerDivisorDefectTerm z (q : XiZeroCopy) = v := by
    rintro ⟨q, hqA⟩
    have hqval : xiSpectralPoint q = μ₀ := hqA
    simp only [deningerDivisorDefectTerm, hqval, hv, hc]
  have hAconst : Summable (fun _ : A => v) := hsumA.congr (fun q => by
    rw [Function.comp_apply, htermA q])
  have hfinA : Finite A := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact hv0 ((summable_const_iff v).mp hAconst)
  have hcardA : 1 ≤ Nat.card A := by
    haveI := hfinA
    haveI : Nonempty A := ⟨⟨q₀, hq₀A⟩⟩
    exact Nat.card_pos
  have hsumA_eq : (∑' q : A, deningerDivisorDefectTerm z (q : XiZeroCopy)) =
      (Nat.card A) • v :=
    calc (∑' q : A, deningerDivisorDefectTerm z (q : XiZeroCopy))
        = ∑' _ : A, v := tsum_congr htermA
      _ = (Nat.card A) • v := tsum_const v
  have hnormA : ‖c‖ / t ^ (3 : ℕ) ≤
      ‖∑' q : A, deningerDivisorDefectTerm z (q : XiZeroCopy)‖ := by
    rw [hsumA_eq, nsmul_eq_mul, norm_mul, Complex.norm_natCast, hvnorm]
    have hnn : 0 ≤ ‖c‖ / t ^ (3 : ℕ) :=
      div_nonneg (norm_nonneg c) (le_of_lt (pow_pos ht0 3))
    calc ‖c‖ / t ^ (3 : ℕ) = 1 * (‖c‖ / t ^ (3 : ℕ)) := (one_mul _).symm
      _ ≤ (Nat.card A : ℝ) * (‖c‖ / t ^ (3 : ℕ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcardA) hnn
  -- uniform bound on the complement
  have hbound : ∀ q : XiZeroCopy, xiSpectralPoint q ≠ μ₀ →
      ‖deningerDivisorDefectTerm z q‖ ≤
        C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro q hqne
    have hμq0 : 0 < ‖xiSpectralPoint q‖ :=
      norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    by_cases hreg : 2 * ‖z‖ + 2 ≤ ‖xiSpectralPoint q‖
    · calc ‖deningerDivisorDefectTerm z q‖
          ≤ 16 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
            norm_deningerDivisorDefectTerm_le_of_far z q hreg
        _ ≤ C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [hC]
            have h0 : 0 ≤ 2 * R₀ ^ (3 : ℕ) * (2 / δ) ^ (3 : ℕ) := by positivity
            linarith
    · -- near regime: separation gives the resolvent bound, the ball gives the norm bound
      rw [not_le] at hreg
      have hμsmall : ‖xiSpectralPoint q‖ ≤ R₀ := by
        have hzn : ‖z‖ ≤ ‖μ₀‖ + 1 := by
          rw [hz]
          calc ‖μ₀ + (t : ℂ)‖ ≤ ‖μ₀‖ + ‖(t : ℂ)‖ := norm_add_le _ _
            _ ≤ ‖μ₀‖ + 1 := by
                simp only [Complex.norm_real, Real.norm_eq_abs,
                  abs_of_pos ht0]
                linarith
        rw [hR₀]
        linarith
      have hres : δ / 2 ≤ ‖xiSpectralPoint q - z‖ := by
        have hsep := hδ q hqne
        have htri : ‖xiSpectralPoint q - μ₀‖ - ‖z - μ₀‖ ≤
            ‖xiSpectralPoint q - z‖ := by
          have := norm_sub_norm_le (xiSpectralPoint q - μ₀) (z - μ₀)
          calc ‖xiSpectralPoint q - μ₀‖ - ‖z - μ₀‖
              ≤ ‖(xiSpectralPoint q - μ₀) - (z - μ₀)‖ := this
            _ = ‖xiSpectralPoint q - z‖ := by ring_nf
        rw [hzdist] at htri
        linarith
      have hinv : ‖(xiSpectralPoint q - z)⁻¹‖ ≤ 2 / δ := by
        rw [norm_inv]
        have h2 : (0 : ℝ) < δ / 2 := by positivity
        calc ‖xiSpectralPoint q - z‖⁻¹ ≤ (δ / 2)⁻¹ := by
              rw [inv_eq_one_div, inv_eq_one_div]
              exact div_le_div_of_nonneg_left (by norm_num) h2 hres
          _ = 2 / δ := by rw [inv_div]
      calc ‖deningerDivisorDefectTerm z q‖
          = ‖xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q)‖ *
              ‖(xiSpectralPoint q - z)⁻¹‖ ^ (3 : ℕ) := by
            rw [deningerDivisorDefectTerm, norm_mul, norm_pow]
        _ ≤ (2 * R₀) * (2 / δ) ^ (3 : ℕ) := by
            apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hinv 3)
              (by positivity) (by positivity)
            calc ‖xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q)‖
                ≤ 2 * ‖xiSpectralPoint q‖ := norm_defectTwist_le q
              _ ≤ 2 * R₀ := by linarith
        _ ≤ C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
            rw [hC]
            rw [div_eq_mul_inv, one_div]
            have hsq : ‖xiSpectralPoint q‖ ^ (2 : ℕ) ≤ R₀ ^ (2 : ℕ) :=
              pow_le_pow_left₀ (le_of_lt hμq0) hμsmall 2
            have hinvsq : (R₀ ^ (2 : ℕ))⁻¹ ≤ (‖xiSpectralPoint q‖ ^ (2 : ℕ))⁻¹ := by
              rw [inv_eq_one_div, inv_eq_one_div]
              exact div_le_div_of_nonneg_left (by norm_num)
                (by positivity) hsq
            calc (2 * R₀) * (2 / δ) ^ (3 : ℕ)
                = (2 * R₀ ^ (3 : ℕ) * (2 / δ) ^ (3 : ℕ)) * (R₀ ^ (2 : ℕ))⁻¹ := by
                  field_simp
              _ ≤ (2 * R₀ ^ (3 : ℕ) * (2 / δ) ^ (3 : ℕ)) * (‖xiSpectralPoint q‖ ^ (2 : ℕ))⁻¹ := by
                  apply mul_le_mul_of_nonneg_left hinvsq (by positivity)
              _ ≤ (16 + 2 * R₀ ^ (3 : ℕ) * (2 / δ) ^ (3 : ℕ)) *
                    (‖xiSpectralPoint q‖ ^ (2 : ℕ))⁻¹ := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  linarith
  have hcomplnorm : ‖∑' q : ↥Aᶜ,
      deningerDivisorDefectTerm z (q : XiZeroCopy)‖ ≤ M := by
    have hsumnormAc : Summable (fun q : ↥Aᶜ =>
        ‖deningerDivisorDefectTerm z (q : XiZeroCopy)‖) :=
      (summable_norm_deningerDivisorDefectTerm z).subtype Aᶜ
    calc ‖∑' q : ↥Aᶜ, deningerDivisorDefectTerm z (q : XiZeroCopy)‖
        ≤ ∑' q : ↥Aᶜ, ‖deningerDivisorDefectTerm z (q : XiZeroCopy)‖ :=
          norm_tsum_le_tsum_norm hsumnormAc
      _ ≤ ∑' q : ↥Aᶜ, C * (1 / ‖xiSpectralPoint (q : XiZeroCopy)‖ ^ (2 : ℕ)) := by
          apply Summable.tsum_le_tsum _ hsumnormAc (hCsum.subtype Aᶜ)
          rintro ⟨q, hqc⟩
          exact hbound q hqc
      _ = ∑' q : XiZeroCopy, (Aᶜ).indicator
            (fun q => C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) q :=
          tsum_subtype Aᶜ (fun q => C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
      _ ≤ M := by
          rw [hM]
          apply Summable.tsum_le_tsum _ (hCsum.indicator Aᶜ) hCsum
          intro q
          exact Set.indicator_le_self' (fun q _ => by positivity) q
  -- assemble
  refine ⟨z, ?_⟩
  have hsplit := Summable.tsum_add_tsum_compl (s := A) hsumA hsumAc
  have hlow : ‖c‖ / t ^ (3 : ℕ) - M ≤ ‖deningerDivisorDefectTrace z‖ := by
    rw [deningerDivisorDefectTrace, ← hsplit]
    have htri : ‖∑' q : A, deningerDivisorDefectTerm z (q : XiZeroCopy)‖ -
        ‖∑' q : ↥Aᶜ, deningerDivisorDefectTerm z (q : XiZeroCopy)‖ ≤
        ‖(∑' q : A, deningerDivisorDefectTerm z (q : XiZeroCopy)) +
          ∑' q : ↥Aᶜ, deningerDivisorDefectTerm z (q : XiZeroCopy)‖ := by
      have h1 := norm_sub_le
        ((∑' q : A, deningerDivisorDefectTerm z (q : XiZeroCopy)) +
          ∑' q : ↥Aᶜ, deningerDivisorDefectTerm z (q : XiZeroCopy))
        (∑' q : ↥Aᶜ, deningerDivisorDefectTerm z (q : XiZeroCopy))
      have h2 : ((∑' q : A, deningerDivisorDefectTerm z (q : XiZeroCopy)) +
          ∑' q : ↥Aᶜ, deningerDivisorDefectTerm z (q : XiZeroCopy)) -
          (∑' q : ↥Aᶜ, deningerDivisorDefectTerm z (q : XiZeroCopy)) =
          ∑' q : A, deningerDivisorDefectTerm z (q : XiZeroCopy) := by ring
      rw [h2] at h1
      linarith
    linarith [hnormA, hcomplnorm, htri]
  have hbig : 4 * (M + 1) ≤ ‖c‖ / t ^ (3 : ℕ) := by
    have ht3 : t ^ (3 : ℕ) ≤ t := by
      have ht1' : t ≤ 1 := by linarith
      have hsq : t ^ (2 : ℕ) ≤ 1 := by nlinarith
      calc t ^ (3 : ℕ) = t * t ^ (2 : ℕ) := by ring
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left hsq (le_of_lt ht0)
        _ = t := mul_one t
    have hdivmono : ‖c‖ / t ≤ ‖c‖ / t ^ (3 : ℕ) := by
      apply div_le_div_of_nonneg_left (le_of_lt hcnorm) (pow_pos ht0 3) ht3
    have hct : 4 * (M + 1) ≤ ‖c‖ / t := by
      rw [le_div_iff₀ ht0]
      calc 4 * (M + 1) * t ≤ 4 * (M + 1) * (‖c‖ / (4 * (M + 1))) := by
            apply mul_le_mul_of_nonneg_left htc (by linarith)
        _ = ‖c‖ := by field_simp
    linarith
  intro hzero
  rw [hzero, norm_zero] at hlow
  linarith

/-- **Vanishing of the defect trace forces RH.** -/
theorem riemannHypothesis_of_forall_deningerDivisorDefectTrace_eq_zero
    (h : ∀ z : ℂ, deningerDivisorDefectTrace z = 0) :
    RiemannHypothesis := by
  by_contra hRH
  rw [rh_iff_xi_ne_zero_right] at hRH
  push Not at hRH
  obtain ⟨s, hs, hzero⟩ := hRH
  have hmem := mem_xi_divisor_support_of_eq_zero hzero
  have hpos : 0 < (MeromorphicOn.divisor xi Set.univ) s :=
    xi_divisor_pos_on_support ⟨s, hmem⟩
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) s) := by omega
  have him : (xiSpectralPoint (⟨⟨s, hmem⟩, ⟨0, hn⟩⟩ : XiZeroCopy)).im ≠ 0 := by
    rw [xiSpectralPoint_im_divisorDefect]
    have hre := mem_rightHalf.mp hs
    intro heq
    have : (s : ℂ).re = 1 / 2 := by
      have : ((⟨s, hmem⟩ : XiDivisorSupport) : ℂ) = s := rfl
      linarith [heq]
    linarith
  obtain ⟨z, hz⟩ :=
    exists_deningerDivisorDefectTrace_ne_zero_of_offline _ him
  exact hz (h z)

/-- **The defect trace detects the Riemann hypothesis**: the Ward twist factor summed against
the third resolvent power vanishes identically iff RH.  The trivial direction is termwise
reality on the line; the detection direction is unconditional pole extraction. -/
theorem deningerDivisorDefectTrace_eq_zero_iff_riemannHypothesis :
    (∀ z : ℂ, deningerDivisorDefectTrace z = 0) ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_forall_deningerDivisorDefectTrace_eq_zero,
    deningerDivisorDefectTrace_eq_zero_of_riemannHypothesis⟩

end RHTower
