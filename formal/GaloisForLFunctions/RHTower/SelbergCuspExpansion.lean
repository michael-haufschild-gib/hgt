import GaloisForLFunctions.RHTower.SelbergCuspLeftLineDecay

/-!
# The shift-lattice expansion at the cusp

For a class member `F` of positive degree `d`, a base point `s` off the lattice `1 + ℕ/d`, and the
cusp gap `Δ(0) = dist(0, Spec F)`:

```text
Φ_F(s, ζ) − P_F(s, ζ) = Σ_{k ≥ 0} (2πiζ)^k/k! · F(s − k/d)      (ζ ∈ H, |ζ| < Δ(0))
```

(`ExtendedSelbergClass.hasSum_cuspExpansion`), where `Φ_F(s, ζ) = Σ a(n) n^{-s} e(ζ n^{1/d})` is
the theta function and `P_F(s, ζ)` is the singular part: the residue at `u₀ = d(1 − s)` of the
Mellin–Barnes integrand `(−2πiζ)^{-u} Γ(u) F(s + u/d)` (zero when `F` is entire).  The power series
has radius of convergence **exactly** `Δ(0)` (`ExtendedSelbergClass.radius_cuspExpansion`).

Proof.  On the imaginary axis `ζ = iy`, `0 < y < Δ(0)`: the Mellin–Barnes integral on a line
`Re u = c` is `Φ_F(s, iy)`; moving the line to `Re u = −K − 1/2` crosses the Gamma poles `u = −k`,
`k ≤ K`, whose residues are the terms of the series, and the pole `u₀`, whose residue is
`P_F(s, iy)`; the horizontal sides vanish because `Γ` decays and `F` grows polynomially on vertical
strips; and the far-left integrals tend to zero because their `K`-th roots tend to `y/Δ(0) < 1`.
Both sides are analytic on the half-disk `H ∩ {|ζ| < Δ(0)}`, so the identity extends from the
imaginary axis.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SelbergClass

namespace RHTower

noncomputable section

variable (F : ExtendedSelbergClass)

/-! ## The growth functional in extended-real form -/

theorem ExtendedSelbergClass.isBoundedUnder_norm_shift_rpow_inv (hd : 0 < F.gammaData.degree)
    (s₀ : ℂ) :
    IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ =>
      (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ))) := by
  have harch := F.gammaData.tendsto_norm_asymmetricH_shift_rpow_inv hd s₀
  have hrefl := F.tendsto_norm_reflection_shift_rpow_inv hd s₀
  have hA := harch.mul hrefl
  obtain ⟨B, hB, hBle⟩ := F.gammaData.exists_bound_norm_asymmetricS_shift s₀
  have hBb : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ =>
      ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ ^ (1 / (k : ℝ))) :=
    isBoundedUnder_rpow_inv hB (fun k => norm_nonneg _) hBle
  obtain ⟨M, hM⟩ := hBb
  rw [Filter.eventually_map] at hM
  set L := F.gammaData.conductor ^ (1 / F.gammaData.degree) / (2 * Real.pi * F.gammaData.degree) *
    (F.firstIndex : ℝ) ^ (-(1 / F.gammaData.degree))
  refine ⟨(L + 1) * max M 0, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [hM, hA.eventually_lt_const (lt_add_one L), F.eventually_farLeft_shift hd s₀]
    with k hMk hAk ⟨hk0, hkμ⟩
  have hFEk := F.value_eq_asymmetric_of_farLeft hk0 hkμ
  have hnormF : ‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖
      = ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖
        * ‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖
        * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ := by
    rw [hFEk, norm_mul, norm_mul, norm_mul, F.gammaData.norm_invariantRootNumber, one_mul]
  rw [hnormF]
  have hrearr : ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖
        * ‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖
        * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ /
          (k.factorial : ℝ)
      = (‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)
          * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖)
        * ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ := by
    ring
  rw [hrearr, Real.mul_rpow (by positivity) (norm_nonneg _),
    Real.mul_rpow (by positivity) (norm_nonneg _)]
  have hA0 : 0 ≤ (‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ /
      (k.factorial : ℝ)) ^ (1 / (k : ℝ)) *
      ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ ^ (1 / (k : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (norm_nonneg _) _)
  exact mul_le_mul hAk.le (le_trans hMk (le_max_left _ _))
    (Real.rpow_nonneg (norm_nonneg _) _) (by linarith)

/-- **The cusp growth law, extended-real form.** -/
theorem ExtendedSelbergClass.hadamardLimsup_shift (hd : 0 < F.gammaData.degree) (s₀ : ℂ) :
    hadamardLimsup (fun k : ℕ =>
        F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ)) / (k.factorial : ℂ)) =
      ENNReal.ofReal (1 / (2 * Real.pi * Metric.infDist 0 F.shiftSpectrum)) := by
  have hnorm : ∀ k : ℕ, ‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ)) / (k.factorial : ℂ)‖ =
      ‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ) := by
    intro k
    rw [norm_div, Complex.norm_natCast]
  have hbdd := F.isBoundedUnder_norm_shift_rpow_inv hd s₀
  rw [hadamardLimsup_eq_ofReal_limsup (by simp_rw [hnorm]; exact hbdd)]
  simp_rw [hnorm]
  rw [F.cuspGrowthLaw hd s₀]

/-! ## The expansion -/

/-- The cusp gap `Δ(0) = dist(0, Spec F)`. -/
theorem ExtendedSelbergClass.infDist_zero_shiftSpectrum_eq (hd : 0 < F.gammaData.degree) :
    Metric.infDist 0 F.shiftSpectrum = F.gammaData.degree *
      ((F.firstIndex : ℝ) / F.gammaData.conductor) ^ (1 / F.gammaData.degree) := by
  rw [ExtendedSelbergClass.shiftSpectrum, ExtendedSelbergClass.presentationDegree,
    ExtendedSelbergClass.presentationConductor]
  exact infDist_zero_shiftSpectrum_of_first (a := fun n => (F.coeff n : ℂ)) F.firstIndex_pos
    F.coeff_firstIndex_ne_zero (fun n _ hn => F.coeff_eq_zero_of_lt_firstIndex hn) hd
    F.gammaData.conductor_pos

theorem ExtendedSelbergClass.infDist_zero_shiftSpectrum_pos (hd : 0 < F.gammaData.degree) :
    0 < Metric.infDist 0 F.shiftSpectrum := by
  rw [F.infDist_zero_shiftSpectrum_eq hd]
  have : (0 : ℝ) < (F.firstIndex : ℝ) := by exact_mod_cast F.firstIndex_pos
  have := F.gammaData.conductor_pos
  positivity

/-- The coefficients `(2πi)^k F(s − k/d)/k!` of the cusp expansion. -/
def ExtendedSelbergClass.cuspExpansionCoeff (s : ℂ) (k : ℕ) : ℂ :=
  (2 * Real.pi * I) ^ k * (F (s - (k : ℂ) / (F.gammaData.degree : ℂ)) / (k.factorial : ℂ))

/-- **The cusp expansion has radius of convergence exactly the cusp gap.** -/
theorem ExtendedSelbergClass.radius_cuspExpansion (hd : 0 < F.gammaData.degree) (s : ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ (F.cuspExpansionCoeff s)).radius =
      ENNReal.ofReal (Metric.infDist 0 F.shiftSpectrum) := by
  have hΔ := F.infDist_zero_shiftSpectrum_pos hd
  rw [radius_ofScalars_eq_inv_hadamardLimsup]
  unfold ExtendedSelbergClass.cuspExpansionCoeff
  rw [hadamardLimsup_geometric, F.hadamardLimsup_shift hd s]
  have hnorm : ((‖(2 * Real.pi * I : ℂ)‖₊ : ENNReal)) = ENNReal.ofReal (2 * Real.pi) := by
    have h2 : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]; norm_num
    rw [← enorm_eq_nnnorm, ← ofReal_norm, h2]
  rw [hnorm, ← ENNReal.ofReal_mul (by positivity)]
  rw [show 2 * Real.pi * (1 / (2 * Real.pi * Metric.infDist 0 F.shiftSpectrum)) =
      (Metric.infDist 0 F.shiftSpectrum)⁻¹ by field_simp,
    ENNReal.ofReal_inv_of_pos hΔ, inv_inv]

/-- A Mellin line `c` on which the representation holds and which lies right of the pole `u₀`. -/
def ExtendedSelbergClass.cuspMellinLine (s : ℂ) : ℝ :=
  |(F.cuspPole s).re| + F.gammaData.degree * (|s.re| + 2) + 1

theorem ExtendedSelbergClass.cuspMellinLine_pos (hd : 0 < F.gammaData.degree) (s : ℂ) :
    0 < F.cuspMellinLine s := by
  unfold ExtendedSelbergClass.cuspMellinLine; positivity

theorem ExtendedSelbergClass.cuspPole_re_lt_cuspMellinLine (hd : 0 < F.gammaData.degree)
    (s : ℂ) : (F.cuspPole s).re < F.cuspMellinLine s := by
  unfold ExtendedSelbergClass.cuspMellinLine
  have := le_abs_self (F.cuspPole s).re
  have : 0 ≤ F.gammaData.degree * (|s.re| + 2) := by positivity
  linarith

theorem ExtendedSelbergClass.one_lt_re_add_cuspMellinLine (hd : 0 < F.gammaData.degree)
    (s : ℂ) : 1 < s.re + F.cuspMellinLine s / F.gammaData.degree := by
  unfold ExtendedSelbergClass.cuspMellinLine
  have h1 : (|(F.cuspPole s).re| + F.gammaData.degree * (|s.re| + 2) + 1) / F.gammaData.degree
      ≥ |s.re| + 2 := by
    rw [ge_iff_le, le_div_iff₀ hd]
    have := abs_nonneg (F.cuspPole s).re
    nlinarith
  have := neg_abs_le s.re
  linarith

theorem neg_two_pi_I_mul_imag (y : ℝ) :
    -2 * (Real.pi : ℂ) * I * ((y : ℂ) * I) = (((2 * Real.pi * y : ℝ)) : ℂ) := by
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The contour identity on the imaginary axis**, for one far-left line. -/
theorem ExtendedSelbergClass.eventually_contour_identity (hd : 0 < F.gammaData.degree) (s : ℂ)
    (hs : ∀ k : ℕ, F.cuspPole s ≠ -(k : ℂ)) {y : ℝ} (hy : 0 < y) :
    ∀ᶠ K : ℕ in atTop,
      (∫ t : ℝ, F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ)
          (((F.cuspMellinLine s : ℝ) : ℂ) + (t : ℂ) * I)) -
        (∫ t : ℝ, F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ) (leftLine K t)) =
      2 * (Real.pi : ℂ) * (F.cuspPolarPart s ((y : ℂ) * I) +
        ∑ k ∈ Finset.range (K + 1), F.cuspExpansionCoeff s k * ((y : ℂ) * I) ^ k) := by
  classical
  obtain ⟨j₀⟩ := F.exists_distinguished_index hd
  obtain ⟨C, -, hev⟩ := F.eventually_integrable_norm_integral_left_le hd s hy j₀
  set x : ℂ := (((2 * Real.pi * y : ℝ)) : ℂ) with hx
  have hx0 : x ≠ 0 := by rw [hx]; exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi * y).ne'
  set c := F.cuspMellinLine s with hcdef
  have hc := F.cuspMellinLine_pos hd s
  have hpole_c := F.cuspPole_re_lt_cuspMellinLine hd s
  have hright := F.integrable_cuspMellinIntegrand_right hd s hy hc
    (F.one_lt_re_add_cuspMellinLine hd s)
  have hK_pole : ∀ᶠ K : ℕ in atTop, (-(K : ℝ) - 1 / 2) < (F.cuspPole s).re := by
    have : Tendsto (fun K : ℕ => -(K : ℝ) - 1 / 2) atTop atBot :=
      tendsto_atBot_add_const_right _ _ (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    exact this.eventually_lt_atBot _
  filter_upwards [hev, hK_pole] with K hK hKp
  set a : ℝ := -(K : ℝ) - 1 / 2 with ha
  have hac : a < c := by linarith
  set P : Finset ℂ := insert (F.cuspPole s)
    ((Finset.range (K + 1)).image fun k : ℕ => -(k : ℂ)) with hP
  have hnotin : F.cuspPole s ∉ (Finset.range (K + 1)).image fun k : ℕ => -(k : ℂ) := by
    intro h
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 h
    exact hs k hk.symm
  have hPre : ∀ p ∈ P, a < p.re ∧ p.re < c := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact ⟨hKp, hpole_c⟩
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
      have hkK : (k : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      constructor
      · simp; linarith
      · simp; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hmero : ∀ p ∈ P, MeromorphicAt (F.cuspMellinIntegrand s x) p :=
    fun p _ => F.meromorphicAt_cuspMellinIntegrand s hx0 p
  have hoff : ∀ z : ℂ, a ≤ z.re → z.re ≤ c → z ∉ P →
      AnalyticAt ℂ (F.cuspMellinIntegrand s x) z := by
    intro z hza _ hzP
    refine F.analyticAt_cuspMellinIntegrand hd s hx0 (fun k hk => ?_) (fun h => hzP ?_)
    · apply hzP
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨k, Finset.mem_range.2 ?_, hk.symm⟩)
      have hre := congrArg Complex.re hk
      simp at hre
      have : (k : ℝ) < K + 1 := by linarith
      exact_mod_cast this
    · rw [h]; exact Finset.mem_insert_self _ _
  have hT : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨htop, hbot⟩ := F.tendsto_hIntegral_cuspMellinIntegrand hd s hy hac.le
  have hshift := verticalIntegral_sub_eq_sum_laurentCoeff_of_horizontal_tendsto_seq hac hPre hmero
    hoff hK.1 hright hT (htop.comp hT) (hbot.comp hT)
  have hleft_eq : (fun t : ℝ => F.cuspMellinIntegrand s x (((a : ℝ) : ℂ) + (t : ℂ) * I)) =
      fun t => F.cuspMellinIntegrand s x (leftLine K t) := by
    funext t; rfl
  rw [hleft_eq] at hshift
  rw [hshift]
  congr 1
  rw [hP, Finset.sum_insert hnotin, Finset.sum_image (fun k _ k' _ h => by
    have := congrArg Complex.re h; simp at this; exact_mod_cast this)]
  congr 1
  · rw [ExtendedSelbergClass.cuspPolarPart, neg_two_pi_I_mul_imag]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [F.laurentCoeff_cuspMellinIntegrand_neg_nat hd s hx0 k (hs k),
      ExtendedSelbergClass.cuspExpansionCoeff, hx]
    set Fv := F (s - (k : ℂ) / (F.gammaData.degree : ℂ))
    have hI : (I : ℂ) ^ k * I ^ k = (-1) ^ k := by rw [← mul_pow, Complex.I_mul_I]
    push_cast
    rw [mul_pow, mul_pow, mul_pow, mul_pow]
    linear_combination (-((2 : ℂ) ^ k * (Real.pi : ℂ) ^ k * (y : ℂ) ^ k *
      (Fv / (k.factorial : ℂ)))) * hI

/-- **The cusp expansion on the imaginary axis.** -/
theorem ExtendedSelbergClass.hasSum_cuspExpansion_imag (hd : 0 < F.gammaData.degree) (s : ℂ)
    (hs : ∀ k : ℕ, F.cuspPole s ≠ -(k : ℂ)) {y : ℝ} (hy : 0 < y)
    (hyΔ : y < Metric.infDist 0 F.shiftSpectrum) :
    HasSum (fun k : ℕ => F.cuspExpansionCoeff s k * ((y : ℂ) * I) ^ k)
      (F.theta s ((y : ℂ) * I) - F.cuspPolarPart s ((y : ℂ) * I)) := by
  -- absolute convergence from the radius
  have hrad := F.radius_cuspExpansion hd s
  have hmem : ((y : ℂ) * I) ∈ Metric.eball (0 : ℂ)
      (FormalMultilinearSeries.ofScalars ℂ (F.cuspExpansionCoeff s)).radius := by
    rw [hrad, Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    refine (ENNReal.ofReal_lt_ofReal_iff (F.infDist_zero_shiftSpectrum_pos hd)).2 ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
    exact hyΔ
  have hsum : Summable (fun k : ℕ => F.cuspExpansionCoeff s k * ((y : ℂ) * I) ^ k) := by
    have h := (FormalMultilinearSeries.ofScalars ℂ (F.cuspExpansionCoeff s)).summable_norm_apply
      hmem
    refine Summable.of_norm (h.congr fun k => ?_)
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [hsum.hasSum_iff_tendsto_nat, ← Filter.tendsto_add_atTop_iff_nat 1]
  -- the contour identity and the vanishing far-left integrals
  have hleft := F.tendsto_integral_cuspMellinIntegrand_left hd s hy
    (by rwa [← F.infDist_zero_shiftSpectrum_eq hd])
  have hMB := F.theta_imag_eq_mellinBarnes s hy (F.cuspMellinLine_pos hd s)
    (F.one_lt_re_add_cuspMellinLine hd s)
  have hmb_eq : F.theta s ((y : ℂ) * I) = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
      F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ)
        (((F.cuspMellinLine s : ℝ) : ℂ) + (t : ℂ) * I) := by
    rw [ExtendedSelbergClass.theta, ExtendedSelbergClass.presentationDegree, hMB]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ExtendedSelbergClass.cuspMellinIntegrand, mellinLine]
    ring
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
  have hlim : Tendsto (fun K : ℕ =>
      F.theta s ((y : ℂ) * I) - F.cuspPolarPart s ((y : ℂ) * I) -
        (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
          F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ) (leftLine K t))
      atTop (𝓝 (F.theta s ((y : ℂ) * I) - F.cuspPolarPart s ((y : ℂ) * I))) := by
    have := (hleft.const_smul (1 / (2 * Real.pi) : ℝ)).const_sub
      (F.theta s ((y : ℂ) * I) - F.cuspPolarPart s ((y : ℂ) * I))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [F.eventually_contour_identity hd s hs hy] with K hK
  rw [hmb_eq]
  have hK' : (∫ t : ℝ, F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ)
      (((F.cuspMellinLine s : ℝ) : ℂ) + (t : ℂ) * I)) =
      2 * (Real.pi : ℂ) * (F.cuspPolarPart s ((y : ℂ) * I) +
        ∑ k ∈ Finset.range (K + 1), F.cuspExpansionCoeff s k * ((y : ℂ) * I) ^ k) +
      ∫ t : ℝ, F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ) (leftLine K t) := by
    rw [← hK]; ring
  rw [hK', Complex.real_smul, Complex.real_smul]
  push_cast
  field_simp
  ring

/-- **The shift-lattice expansion at the cusp.**  For `ζ` in the upper half plane with
`|ζ| < Δ(0)`, the theta function minus its singular part is the power series
`Σ_k (2πiζ)^k F(s − k/d)/k!`. -/
theorem ExtendedSelbergClass.hasSum_cuspExpansion (hd : 0 < F.gammaData.degree) (s : ℂ)
    (hs : ∀ k : ℕ, F.cuspPole s ≠ -(k : ℂ)) {ζ : ℂ} (hζ : 0 < ζ.im)
    (hζΔ : ‖ζ‖ < Metric.infDist 0 F.shiftSpectrum) :
    HasSum (fun k : ℕ => F.cuspExpansionCoeff s k * ζ ^ k)
      (F.theta s ζ - F.cuspPolarPart s ζ) := by
  set p := FormalMultilinearSeries.ofScalars ℂ (F.cuspExpansionCoeff s) with hp
  set Δ := Metric.infDist 0 F.shiftSpectrum with hΔdef
  have hΔ : 0 < Δ := F.infDist_zero_shiftSpectrum_pos hd
  have hrad : p.radius = ENNReal.ofReal Δ := F.radius_cuspExpansion hd s
  have hradpos : 0 < p.radius := by rw [hrad]; exact ENNReal.ofReal_pos.2 hΔ
  have hps := p.hasFPowerSeriesOnBall hradpos
  have hmemball : ∀ z : ℂ, ‖z‖ < Δ → z ∈ Metric.eball (0 : ℂ) p.radius := by
    intro z hz
    rw [hrad, Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hΔ).2 hz
  have happly : ∀ z : ℂ, (fun n => p n fun _ => z) = fun k => F.cuspExpansionCoeff s k * z ^ k := by
    intro z; funext k
    rw [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  -- the two analytic functions on the half-disk
  set U : Set ℂ := {z : ℂ | 0 < z.im} ∩ Metric.ball 0 Δ with hU
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball
  have hUconv : Convex ℝ U := (convex_halfSpace_im_gt 0).inter (convex_ball 0 Δ)
  have hL : AnalyticOnNhd ℂ (fun z => F.theta s z - F.cuspPolarPart s z) U := by
    intro z hz
    exact (F.analyticAt_theta hd s z hz.1).sub (F.analyticOnNhd_cuspPolarPart s z hz.1)
  have hR : AnalyticOnNhd ℂ p.sum U := by
    intro z hz
    have hzmem : z ∈ Metric.eball (0 : ℂ) p.radius :=
      hmemball z (by simpa [hU, dist_zero_right] using hz.2)
    exact hps.analyticAt_of_mem hzmem
  -- agreement on the imaginary axis
  have hz₀ : ((Δ / 2 : ℝ) : ℂ) * I ∈ U := by
    refine ⟨by simp; linarith, ?_⟩
    rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have heq_axis : ∀ y : ℝ, 0 < y → y < Δ →
      F.theta s ((y : ℂ) * I) - F.cuspPolarPart s ((y : ℂ) * I) = p.sum ((y : ℂ) * I) := by
    intro y hy hyΔ
    have h1 := F.hasSum_cuspExpansion_imag hd s hs hy hyΔ
    have h2 := hps.hasSum (hmemball ((y : ℂ) * I) (by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
      exact hyΔ))
    rw [zero_add, happly] at h2
    exact h1.unique h2
  have hfreq : ∃ᶠ z in 𝓝[≠] (((Δ / 2 : ℝ) : ℂ) * I),
      (fun z => F.theta s z - F.cuspPolarPart s z) z = p.sum z := by
    have hmap : Tendsto (fun r : ℝ => ((r : ℝ) : ℂ) * I) (𝓝[≠] (Δ / 2))
        (𝓝[≠] (((Δ / 2 : ℝ) : ℂ) * I)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact ((Complex.continuous_ofReal.mul continuous_const).tendsto _).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        intro h
        apply hr
        have := congrArg Complex.im h
        simpa using this
    have hev : ∀ᶠ r in 𝓝[≠] (Δ / 2), 0 < r ∧ r < Δ := by
      have : Ioo 0 Δ ∈ 𝓝 (Δ / 2) := Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [nhdsWithin_le_nhds this] with r hr
      exact hr
    refine (hmap.frequently (Filter.Eventually.frequently ?_))
    filter_upwards [hev] with r ⟨hr0, hrΔ⟩
    exact heq_axis r hr0 hrΔ
  have hEq := hL.eqOn_of_preconnected_of_frequently_eq hR hUconv.isPreconnected hz₀ hfreq
  have hζU : ζ ∈ U := ⟨hζ, by simpa [dist_zero_right] using hζΔ⟩
  have hsumζ := hps.hasSum (hmemball ζ hζΔ)
  rw [zero_add, happly] at hsumζ
  have h := hEq hζU
  dsimp only at h
  rw [h]
  exact hsumζ

end

end RHTower
