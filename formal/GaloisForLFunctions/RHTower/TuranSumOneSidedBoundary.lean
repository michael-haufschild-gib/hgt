import GaloisForLFunctions.RHTower.LiouvilleSummatoryPolyaBoundary

/-!
# Turán's problem: one-sided bounds for `Σ λ(k)/k`

Let `T(x) = Σ_{k ≤ x} λ(k)/k`.  In the logarithmic variable
`∫_0^∞ T(e^u) e^{-su} du = ζ(2s+2)/(sζ(s+1))` for `Re s > 0` (partial summation with the harmonic
bound `Σ_{k ≤ n} 1/k = O(n^r)` for every `r > 0`).  With `Z(w) = (w-1)ζ(w)` the kernel is
`Q(z) = Z(2z+2)/((2z+1)Z(z+1))`, holomorphic on `Re z > -½` off the shifted zeros of `ζ`, with a
simple pole at `-½` of residue `-1/ζ(½) > 0`.

Suppose `ηT(x) ≤ ε'/√x` for large `x`, `η = ±1`.  The region of interest contains `z = 0`, so the
finitely many early values are absorbed by `K e^{-u}` (transform `K/(z+1)`) rather than a constant.
For `ε > ε'` the density `ε e^{-u/2} - ηT(e^u) + K e^{-u}` is nonnegative and at least
`(ε - ε')e^{-u/2}`; Landau's theorem puts the abscissa of its Laplace transform at `-½`, and the
identity theorem gives `H(z)(2z+1)Z(z+1) = ηZ(2z+2)` on `Re z > -½`.

* A zero `w` of `ζ` with `Re w > ½` makes the left side vanish at `z = w - 1` while `Z(2w) ≠ 0`:
  **either one-sided bound implies RH** (Turán's problem).
* `r·Q(-½ + r) → -1/ζ(½)`, so `r ∫ e^{-(r-½)u} dν → ε + η/ζ(½)`; with `η = 1` and `ε < -1/ζ(½)`
  this is negative.  Hence **`T(x) > c/√x` infinitely often for every `c < -1/ζ(½)`**: Turán's sum
  has a positive bias of exact size `-1/(ζ(½)√x)`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open scoped LSeries.notation

namespace RHTower

noncomputable section

/-! ## Turán's sum -/

/-- Turán's sum `T(x) = Σ_{1 ≤ k ≤ x} λ(k)/k`. -/
def turanSum (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.liouville k : ℤ) : ℝ) / k

theorem abs_turanSum_le (x : ℝ) : |turanSum x| ≤ 1 + Real.log ⌊x⌋₊ := by
  unfold turanSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |((ArithmeticFunction.liouville k : ℤ) : ℝ) / k|
      ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((k : ℝ))⁻¹ := Finset.sum_le_sum fun k hk => by
        rw [abs_div, abs_of_nonneg (a := (k : ℝ)) (Nat.cast_nonneg k), div_eq_mul_inv]
        exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg k)) (abs_liouville_le_one k)
    _ = (harmonic ⌊x⌋₊ : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ 1 + Real.log ⌊x⌋₊ := harmonic_le_one_add_log _

theorem abs_turanSum_exp_le {u : ℝ} (hu : 0 ≤ u) : |turanSum (Real.exp u)| ≤ 1 + u := by
  refine (abs_turanSum_le _).trans ?_
  rcases Nat.eq_zero_or_pos ⌊Real.exp u⌋₊ with h | h
  · rw [h]; simp; linarith
  have hfl : (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
  have hpos : (0 : ℝ) < ⌊Real.exp u⌋₊ := by exact_mod_cast h
  have := Real.log_le_log hpos hfl
  rw [Real.log_exp] at this
  linarith

theorem measurable_turanSum : Measurable turanSum := by
  have : turanSum = (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      ((ArithmeticFunction.liouville k : ℤ) : ℝ) / k) ∘ Nat.floor := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

/-- The coefficients `λ(k)/k`. -/
def turanCoeff (k : ℕ) : ℂ := liouvilleC k / k

theorem LSeries_turanCoeff (s : ℂ) :
    LSeries (fun k => turanCoeff k) s = LSeries ↗liouvilleC (s + 1) := by
  refine tsum_congr fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp [LSeries.term]
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [LSeries.term_of_ne_zero hk, LSeries.term_of_ne_zero hk, turanCoeff,
    Complex.cpow_add _ _ hkc, Complex.cpow_one]
  field_simp

/-- **The Mellin transform of `T` in the logarithmic variable.**
`∫_0^∞ T(e^u) e^{-su} du = ζ(2s+2)/(sζ(s+1))` for `Re s > 0`. -/
theorem integral_turanSum_exp_mul_cexp {s : ℂ} (hs : 0 < s.re) :
    ∫ u in Ioi (0 : ℝ), (turanSum (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = riemannZeta (2 * s + 2) / (s * riemannZeta (s + 1)) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; linarith
  have hs1 : 1 < (s + 1).re := by simp; linarith
  set r : ℝ := s.re / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hrs : r < s.re := by rw [hr]; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖turanCoeff k‖)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ r := by
    refine Asymptotics.IsBigO.of_bound (1 + 1 / r) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hle : ∑ k ∈ Finset.Icc 1 n, ‖turanCoeff k‖ ≤ 1 + Real.log n := by
      calc ∑ k ∈ Finset.Icc 1 n, ‖turanCoeff k‖ ≤ ∑ k ∈ Finset.Icc 1 n, ((k : ℝ))⁻¹ :=
            Finset.sum_le_sum fun k hk => by
              rw [turanCoeff, norm_div, Complex.norm_natCast, div_eq_mul_inv]
              exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg k))
                (norm_liouvilleC_le_one k)
        _ = (harmonic n : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; rfl
        _ ≤ 1 + Real.log n := harmonic_le_one_add_log _
    have hlog : Real.log n ≤ (n : ℝ) ^ r / r := Real.log_le_rpow_div (Nat.cast_nonneg n) hr0
    have hpow : 1 ≤ (n : ℝ) ^ r := Real.one_le_rpow hn' hr0.le
    have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, ‖turanCoeff k‖ :=
      Finset.sum_nonneg fun k _ => norm_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    calc ∑ k ∈ Finset.Icc 1 n, ‖turanCoeff k‖ ≤ 1 + (n : ℝ) ^ r / r := by linarith
      _ ≤ (1 + 1 / r) * (n : ℝ) ^ r := by
          rw [add_mul, one_mul, div_eq_mul_inv, one_div, mul_comm ((n : ℝ) ^ r)]; linarith
  have hM := LSeries_eq_mul_integral' (fun k : ℕ => turanCoeff k) hr0.le hrs hO
  rw [LSeries_turanCoeff s, LSeries_liouvilleC_eq_div hs1,
    show 2 * (s + 1) = 2 * s + 2 by ring] at hM
  rw [← image_exp_Ioi_zero, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn] at hM
  have hcongr : ∫ u in Ioi (0 : ℝ), |Real.exp u| • ((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊,
        turanCoeff k) * ((Real.exp u : ℝ) : ℂ) ^ (-(s + 1)))
      = ∫ u in Ioi (0 : ℝ), (turanSum (Real.exp u) : ℂ) * Complex.exp (-s * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hcpow : ((Real.exp u : ℝ) : ℂ) ^ (-(s + 1)) = Complex.exp (u * (-(s + 1))) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
        ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    rw [abs_of_pos (Real.exp_pos u), hcpow, Complex.real_smul, Complex.ofReal_exp]
    unfold turanSum
    simp only [turanCoeff, liouvilleC_apply]
    push_cast
    rw [mul_comm (Complex.exp (u : ℂ)), mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hcongr] at hM
  set I := ∫ u in Ioi (0 : ℝ), (turanSum (Real.exp u) : ℂ) * Complex.exp (-s * u)
  calc I = s * I / s := by field_simp
    _ = riemannZeta (2 * s + 2) / riemannZeta (s + 1) / s := by rw [hM]
    _ = riemannZeta (2 * s + 2) / (s * riemannZeta (s + 1)) := by
        rw [div_div, mul_comm (riemannZeta (s + 1))]

/-! ## The continuation kernel -/

/-- `Q(z) = Z(2z+2)/((2z+1)Z(z+1)) = ζ(2z+2)/(zζ(z+1))`, `Z(w) = (w-1)ζ(w)`. -/
def turanKernel (z : ℂ) : ℂ := zetaResidueUnit (2 * z + 2) / ((2 * z + 1) * zetaResidueUnit (z + 1))

theorem turanKernel_eq {s : ℂ} (hs : s ≠ 0) (hs2 : 2 * s + 1 ≠ 0) :
    turanKernel s = riemannZeta (2 * s + 2) / (s * riemannZeta (s + 1)) := by
  unfold turanKernel
  have h1 : s + 1 ≠ 1 := by intro h; apply hs; linear_combination h
  have h2 : 2 * s + 2 ≠ 1 := by intro h; apply hs2; linear_combination h
  rw [zetaResidueUnit, Function.update_of_ne h1, Function.update_of_ne h2]
  rw [show s + 1 - 1 = s by ring, show 2 * s + 2 - 1 = 2 * s + 1 by ring]
  by_cases hz : riemannZeta (s + 1) = 0
  · rw [hz]; simp
  field_simp

theorem analyticAt_turanKernel {z : ℂ} (hzh : z ≠ -(1 / 2)) (hz : zetaResidueUnit (z + 1) ≠ 0) :
    AnalyticAt ℂ turanKernel z := by
  unfold turanKernel
  have h2 : 2 * z + 1 ≠ 0 := by
    intro h; apply hzh; linear_combination h / 2
  exact ((analyticAt_zetaResidueUnit _).comp ((analyticAt_const.mul analyticAt_id).add
    analyticAt_const)).div (((analyticAt_const.mul analyticAt_id).add analyticAt_const).mul
      ((analyticAt_zetaResidueUnit _).comp (analyticAt_id.add analyticAt_const)))
    (mul_ne_zero h2 hz)

/-! ## The one-sided measure -/

/-- The clipped density `ε e^{-u/2} - ηT(e^u) + K e^{-u}`. -/
def turanSumDensity (η ε K : ℝ) (u : ℝ) : NNReal :=
  Real.toNNReal (ε * Real.exp (-(u / 2)) - η * turanSum (Real.exp u) + K * Real.exp (-u))

theorem measurable_turanSumDensity (η ε K : ℝ) : Measurable (turanSumDensity η ε K) := by
  unfold turanSumDensity
  refine Measurable.real_toNNReal ?_
  refine Measurable.add (Measurable.sub ?_ ?_) ?_
  · exact measurable_const.mul (Real.measurable_exp.comp (measurable_id.div_const 2).neg)
  · exact measurable_const.mul (measurable_turanSum.comp Real.measurable_exp)
  · exact measurable_const.mul (Real.measurable_exp.comp measurable_neg)

/-- `ν = (ε e^{-u/2} - ηT(e^u) + K e^{-u}) du` on `(0, ∞)`. -/
def turanMeasure (η ε K : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun u => (turanSumDensity η ε K u : ENNReal))

theorem turanSumDensity_le {η ε K : ℝ} (hη : |η| = 1) (hε : 0 ≤ ε) (hK : 0 ≤ K) {u : ℝ}
    (hu : 0 < u) : ((turanSumDensity η ε K u : ℝ)) ≤ (ε + K + 1) * (1 + u) := by
  unfold turanSumDensity
  rw [Real.coe_toNNReal']
  have h1 : Real.exp (-(u / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h1' : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : -(η * turanSum (Real.exp u)) ≤ 1 + u := by
    have h3 : |η * turanSum (Real.exp u)| ≤ 1 + u := by
      rw [abs_mul, hη, one_mul]; exact abs_turanSum_exp_le hu.le
    linarith [neg_abs_le (η * turanSum (Real.exp u))]
  have hE := Real.exp_pos (-(u / 2))
  have hE' := Real.exp_pos (-u)
  refine max_le ?_ (by positivity)
  nlinarith

theorem turanSumDensity_coe {η ε ε' K : ℝ} (hεε' : ε' ≤ ε)
    (hg : ∀ u, 0 < u → η * turanSum (Real.exp u) ≤ ε' * Real.exp (-(u / 2)) + K * Real.exp (-u))
    {u : ℝ} (hu : 0 < u) :
    ((turanSumDensity η ε K u : ℝ))
      = ε * Real.exp (-(u / 2)) - η * turanSum (Real.exp u) + K * Real.exp (-u) := by
  unfold turanSumDensity
  have h := hg u hu
  have hE := Real.exp_pos (-(u / 2))
  rw [Real.coe_toNNReal _ (by nlinarith)]

theorem integrableOn_one_add_mul_exp_neg_mul {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => (1 + u) * Real.exp (-σ * u)) (Ioi 0) := by
  set τ : ℝ := min (σ / 2) 1 with hτ
  have hτ0 : 0 < τ := lt_min (by linarith) one_pos
  have hτ1 : τ ≤ 1 := min_le_right _ _
  have hτσ : τ ≤ σ / 2 := min_le_left _ _
  have hmaj : IntegrableOn (fun u : ℝ => τ⁻¹ * Real.exp (-(σ - τ) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
  refine hmaj.mono' ?_ ?_
  · exact ((measurable_const.add measurable_id).mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hexp : τ * (1 + u) ≤ Real.exp (τ * u) := by
      have := Real.add_one_le_exp (τ * u)
      nlinarith
    have hsplit : Real.exp (-(σ - τ) * u) = Real.exp (τ * u) * Real.exp (-σ * u) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [le_inv_mul_iff₀ hτ0]
    linarith

theorem laplaceMass_turanMeasure_ne_top {η ε K σ : ℝ} (hη : |η| = 1) (hε : 0 ≤ ε)
    (hK : 0 ≤ K) (hσ : 0 < σ) : laplaceMass (turanMeasure η ε K) σ ≠ ⊤ := by
  unfold laplaceMass turanMeasure
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_turanSumDensity η ε K).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top
    ((integrableOn_one_add_mul_exp_neg_mul hσ).const_mul (ε + K + 1)).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (turanSumDensity_le hη hε hK hu) (Real.exp_pos _).le

theorem laplaceMass_turanMeasure_eq_top {η ε ε' K σ : ℝ} (hεε' : ε' < ε)
    (hg : ∀ u, 0 < u → η * turanSum (Real.exp u) ≤ ε' * Real.exp (-(u / 2)) + K * Real.exp (-u))
    (hσ : σ ≤ -(1 / 2)) : laplaceMass (turanMeasure η ε K) σ = ⊤ := by
  unfold laplaceMass turanMeasure
  have hg' : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_turanSumDensity η ε K).coe_nnreal_ennreal hg', eq_top_iff]
  have hδ : 0 < ε - ε' := by linarith
  calc (⊤ : ENNReal) = ENNReal.ofReal (ε - ε') * volume (Ioi (0 : ℝ)) := by
        rw [Real.volume_Ioi, ENNReal.mul_top (by simpa using hδ)]
    _ = ∫⁻ _ in Ioi (0 : ℝ), ENNReal.ofReal (ε - ε') := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), ((fun u => (turanSumDensity η ε K u : ENNReal))
          * fun u => ENNReal.ofReal (Real.exp (-σ * u))) u := by
        refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [turanSumDensity_coe hεε'.le hg hu0]
        have h1 := hg u hu0
        have h2 : 1 ≤ Real.exp (-(u / 2)) * Real.exp (-σ * u) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have hE := Real.exp_pos (-σ * u)
        have hE2 := Real.exp_pos (-(u / 2))
        have h3 : (ε - ε') * Real.exp (-(u / 2)) ≤ ε * Real.exp (-(u / 2))
            - η * turanSum (Real.exp u) + K * Real.exp (-u) := by linarith
        calc ε - ε' ≤ (ε - ε') * (Real.exp (-(u / 2)) * Real.exp (-σ * u)) :=
              le_mul_of_one_le_right hδ.le h2
          _ = (ε - ε') * Real.exp (-(u / 2)) * Real.exp (-σ * u) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h3 hE.le

theorem isAbscissa_turanMeasure {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε') (hεε' : ε' < ε)
    (hK : 0 ≤ K)
    (hg : ∀ u, 0 < u → η * turanSum (Real.exp u) ≤ ε' * Real.exp (-(u / 2)) + K * Real.exp (-u)) :
    IsAbscissa (turanMeasure η ε K) (sInf {σ : ℝ | laplaceMass (turanMeasure η ε K) σ ≠ ⊤})
      ∧ -(1 / 2) ≤ sInf {σ : ℝ | laplaceMass (turanMeasure η ε K) σ ≠ ⊤}
      ∧ sInf {σ : ℝ | laplaceMass (turanMeasure η ε K) σ ≠ ⊤} ≤ 0 := by
  have hε : 0 ≤ ε := by linarith
  set S := {σ : ℝ | laplaceMass (turanMeasure η ε K) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, -(1 / 2) < σ := by
    intro σ hσ
    by_contra hle
    exact hσ (laplaceMass_turanMeasure_eq_top hεε' hg (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨-(1 / 2), fun σ hσ => (hpos σ hσ).le⟩
  have hmem : ∀ d : ℝ, 0 < d → d ∈ S := fun d hd =>
    laplaceMass_turanMeasure_ne_top hη hε hK hd
  have hne : S.Nonempty := ⟨1, hmem 1 one_pos⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le,
    le_of_forall_pos_le_add fun d hd => by simpa using csInf_le hbdd (hmem d hd)⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The transform and Landau's theorem -/

/-- The continuation `Φ(z) = ε/(z+½) + K/(z+1) - ηQ(z)`. -/
def turanContinuation (η ε K : ℝ) (z : ℂ) : ℂ :=
  ε / (z + 1 / 2) + K / (z + 1) - η * turanKernel z

theorem analyticAt_turanContinuation (η ε K : ℝ) {z : ℂ} (hzh : z ≠ -(1 / 2)) (hz1 : z ≠ -1)
    (hz : zetaResidueUnit (z + 1) ≠ 0) : AnalyticAt ℂ (turanContinuation η ε K) z := by
  unfold turanContinuation
  have h1 : z + 1 / 2 ≠ 0 := by intro h; apply hzh; linear_combination h
  have h2 : z + 1 ≠ 0 := by intro h; apply hz1; linear_combination h
  exact ((analyticAt_const.div (analyticAt_id.add analyticAt_const) h1).add
    (analyticAt_const.div (analyticAt_id.add analyticAt_const) h2)).sub
    (analyticAt_const.mul (analyticAt_turanKernel hzh hz))

/-- On `Re s > 0` the complex transform of `ν` is `Φ(s)`. -/
theorem complexLaplace_turanMeasure_eq {η ε ε' K : ℝ} (hεε' : ε' ≤ ε)
    (hg : ∀ u, 0 < u → η * turanSum (Real.exp u) ≤ ε' * Real.exp (-(u / 2)) + K * Real.exp (-u))
    {s : ℂ} (hs : 0 < s.re) :
    complexLaplace (turanMeasure η ε K) s = turanContinuation η ε K s := by
  have hsh : 0 < (s + 1 / 2).re := by simp; linarith
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have hs2 : 2 * s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hcexp : ∀ w : ℂ, Continuous (fun u : ℝ => Complex.exp (-w * (u : ℂ))) := fun w =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hexpInt : ∀ w : ℂ, 0 < w.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-w * (u : ℂ))) (Ioi 0) := fun w hw =>
    (exp_neg_integrableOn_Ioi 0 hw).mono' (hcexp w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  have hTint : IntegrableOn
      (fun u : ℝ => (turanSum (Real.exp u) : ℂ) * Complex.exp (-s * u)) (Ioi 0) := by
    refine (integrableOn_one_add_mul_exp_neg_mul hs).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.measurable.comp
        (measurable_turanSum.comp Real.measurable_exp)).aestronglyMeasurable.mul
        (hcexp s).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_turanSum_exp_le hu0.le) (Real.exp_pos _).le
  unfold complexLaplace turanMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul (measurable_turanSumDensity η ε K)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), turanSumDensity η ε K u • Complex.exp (-s * (u : ℂ))
      = ((ε : ℂ) * Complex.exp (-(s + 1 / 2) * (u : ℂ)) +
          (K : ℂ) * Complex.exp (-(s + 1) * (u : ℂ)))
        - (η : ℂ) * ((turanSum (Real.exp u) : ℂ) * Complex.exp (-s * u)) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul, turanSumDensity_coe hεε' hg hu]
    push_cast
    rw [show Complex.exp (-(s + 1 / 2) * (u : ℂ))
      = Complex.exp (-((u : ℂ) / 2)) * Complex.exp (-s * (u : ℂ)) by
        rw [← Complex.exp_add]; congr 1; ring,
      show Complex.exp (-(s + 1) * (u : ℂ))
      = Complex.exp (-(u : ℂ)) * Complex.exp (-s * (u : ℂ)) by
        rw [← Complex.exp_add]; congr 1; ring]
    ring
  have i1 : IntegrableOn (fun u : ℝ => (ε : ℂ) * Complex.exp (-(s + 1 / 2) * (u : ℂ))) (Ioi 0) :=
    (hexpInt _ hsh).const_mul _
  have i2 : IntegrableOn (fun u : ℝ => (K : ℂ) * Complex.exp (-(s + 1) * (u : ℂ))) (Ioi 0) :=
    (hexpInt _ hs1).const_mul _
  have i3 : IntegrableOn (fun u : ℝ => (η : ℂ) * ((turanSum (Real.exp u) : ℂ)
      * Complex.exp (-s * u))) (Ioi 0) := hTint.const_mul _
  have i12 : IntegrableOn (fun u : ℝ => (ε : ℂ) * Complex.exp (-(s + 1 / 2) * (u : ℂ))
      + (K : ℂ) * Complex.exp (-(s + 1) * (u : ℂ))) (Ioi 0) := i1.add i2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_cexp_neg_mul_Ioi hsh,
    integral_cexp_neg_mul_Ioi hs1, integral_turanSum_exp_mul_cexp hs]
  unfold turanContinuation
  rw [turanKernel_eq hs0 hs2]
  ring

theorem zetaResidueUnit_ofReal_add_one_ne_zero {t : ℝ} (ht : -1 < t) :
    zetaResidueUnit ((t : ℂ) + 1) ≠ 0 := by
  have := zetaResidueUnit_ofReal_ne_zero (t := t + 1) (by linarith)
  push_cast at this
  exact this

/-- **Landau: the abscissa of `ν` is `-½`.** -/
theorem abscissa_turanMeasure_eq {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε') (hεε' : ε' < ε)
    (hK : 0 ≤ K)
    (hg : ∀ u, 0 < u → η * turanSum (Real.exp u) ≤ ε' * Real.exp (-(u / 2)) + K * Real.exp (-u)) :
    IsAbscissa (turanMeasure η ε K) (-(1 / 2)) := by
  obtain ⟨hc, hac, hc0⟩ := isAbscissa_turanMeasure hη hε' hεε' hK hg
  set c : ℝ := sInf {σ : ℝ | laplaceMass (turanMeasure η ε K) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hch : (c : ℂ) ≠ -(1 / 2) := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hc1 : (c : ℂ) ≠ -1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hZ : zetaResidueUnit ((c : ℂ) + 1) ≠ 0 :=
      zetaResidueUnit_ofReal_add_one_ne_zero (by linarith)
    have hZc : ContinuousAt (fun z : ℂ => zetaResidueUnit (z + 1)) (c : ℂ) :=
      ((analyticAt_zetaResidueUnit _).comp (analyticAt_id.add analyticAt_const)).continuousAt
    have hev : ∀ᶠ z in 𝓝 (c : ℂ), zetaResidueUnit (z + 1) ≠ 0 ∧ z ≠ -(1 / 2) ∧ z ≠ -1 :=
      (hZc.eventually_ne hZ).and ((eventually_ne_nhds hch).and (eventually_ne_nhds hc1))
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine false_of_analyticAt_abscissa hc hd (Φ := turanContinuation η ε K) ?_ ?_
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := hball hz
      exact analyticAt_turanContinuation η ε K h2 h3 h1
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (turanMeasure η ε K))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (turanMeasure η ε K) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (turanMeasure η ε K)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => turanContinuation η ε K (t : ℂ)) (Ioi c) := by
        intro t ht
        have hth : -(1 / 2) < t := lt_trans hpos ht
        have h1 : AnalyticAt ℂ (turanContinuation η ε K) (t : ℂ) := by
          refine analyticAt_turanContinuation η ε K ?_ ?_
            (zetaResidueUnit_ofReal_add_one_ne_zero (by linarith))
          · intro h; have := congrArg Complex.re h; simp at this; linarith
          · intro h; have := congrArg Complex.re h; simp at this; linarith
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h1mem : (1 : ℝ) ∈ Ioi c := by show c < 1; linarith
      have hfg : (fun t : ℝ => complexLaplace (turanMeasure η ε K) (t : ℂ)) =ᶠ[𝓝 (1 : ℝ)]
          (fun t : ℝ => turanContinuation η ε K (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
          fun t ht => ?_
        have ht1 : 0 < (t : ℂ).re := by simp; linarith [ht.1]
        exact complexLaplace_turanMeasure_eq hεε'.le hg ht1
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
      have hσ : complexLaplace (turanMeasure η ε K) (σ : ℂ)
          = turanContinuation η ε K (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **The continuation identity on `Re z > -½`.**
`H(z)·(2z+1)·Z(z+1) = ηZ(2z+2)`, `H(z) = ε/(z+½) + K/(z+1) - ∫ e^{-zu} dν`. -/
theorem turan_continuation_identity {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ u, 0 < u → η * turanSum (Real.exp u) ≤ ε' * Real.exp (-(u / 2)) + K * Real.exp (-u))
    {z : ℂ} (hz : -(1 / 2) < z.re) :
    (ε / (z + 1 / 2) + K / (z + 1) - complexLaplace (turanMeasure η ε K) z)
      * ((2 * z + 1) * zetaResidueUnit (z + 1)) = η * zetaResidueUnit (2 * z + 2) := by
  have hc := abscissa_turanMeasure_eq hη hε' hεε' hK hg
  set U : Set ℂ := {w : ℂ | -(1 / 2) < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hneh : ∀ w ∈ U, w + 1 / 2 ≠ 0 := fun w hw h => by
    have := congrArg Complex.re h; simp [hU] at this hw; linarith
  have hne1 : ∀ w ∈ U, w + 1 ≠ 0 := fun w hw h => by
    have := congrArg Complex.re h; simp [hU] at this hw; linarith
  set F : ℂ → ℂ := fun w => (ε / (w + 1 / 2) + K / (w + 1)
    - complexLaplace (turanMeasure η ε K) w) * ((2 * w + 1) * zetaResidueUnit (w + 1)) with hF
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (ε : ℂ) / (w + 1 / 2)) w :=
      (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _))
        (hneh w hw)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (K : ℂ) / (w + 1)) w :=
      (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _))
        (hne1 w hw)
    have h3 := (hasDerivAt_complexLaplace hc hw).differentiableAt
    have h4 : DifferentiableAt ℂ (fun w => (2 * w + 1) * zetaResidueUnit (w + 1)) w :=
      (((differentiableAt_const _).mul differentiableAt_id).add (differentiableAt_const _)).mul
        ((analyticAt_zetaResidueUnit _).differentiableAt.comp w
          (differentiableAt_id.add (differentiableAt_const _)))
    exact (((h1.add h2).sub h3).mul h4).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hUo
  have hGa : AnalyticOnNhd ℂ (fun w : ℂ => (η : ℂ) * zetaResidueUnit (2 * w + 2)) U :=
    fun w _ => analyticAt_const.mul ((analyticAt_zetaResidueUnit _).comp
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const))
  have h1U : (1 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : F =ᶠ[𝓝 (1 : ℂ)] fun w : ℂ => (η : ℂ) * zetaResidueUnit (2 * w + 2) := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with w hw
    have hw0 : 0 < w.re := hw
    have hw2 : 2 * w + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hwr : 1 < (w + 1).re := by simp; linarith
    have hw1' : w + 1 ≠ 1 := by intro h; rw [h, Complex.one_re] at hwr; linarith
    have hZ : zetaResidueUnit (w + 1) ≠ 0 := by
      rw [zetaResidueUnit, Function.update_of_ne hw1']
      exact mul_ne_zero (sub_ne_zero.mpr hw1') (riemannZeta_ne_zero_of_one_lt_re hwr)
    simp only [hF]
    rw [complexLaplace_turanMeasure_eq hεε'.le hg hw0, turanContinuation]
    have hden : (2 * w + 1) * zetaResidueUnit (w + 1) ≠ 0 := mul_ne_zero hw2 hZ
    have e : turanKernel w * ((2 * w + 1) * zetaResidueUnit (w + 1)) =
        zetaResidueUnit (2 * w + 2) := by
      unfold turanKernel; exact div_mul_cancel₀ _ hden
    linear_combination (η : ℂ) * e
  have hEq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (convex_halfSpace_re_gt _).isPreconnected h1U hev
  exact hEq hz

theorem exists_turan_oneSided_of_eventually {η c : ℝ} (hη : |η| = 1) (hc : 0 ≤ c)
    (h : ∀ᶠ x : ℝ in atTop, η * turanSum x ≤ c * x ^ (-(1 / 2) : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u, 0 < u →
      η * turanSum (Real.exp u) ≤ c * Real.exp (-(u / 2)) + K * Real.exp (-u) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp h
  set u₀ : ℝ := abs (Real.log (abs x₀)) with hu₀
  refine ⟨(1 + u₀) * Real.exp u₀, by positivity, fun u hu => ?_⟩
  have hE := Real.exp_pos (-(u / 2))
  have hE' := Real.exp_pos (-u)
  have hK0 : 0 ≤ (1 + u₀) * Real.exp u₀ * Real.exp (-u) := by positivity
  by_cases hxt : x₀ ≤ Real.exp u
  · have := hx₀ (Real.exp u) hxt
    rw [← Real.exp_mul, show u * (-(1 / 2)) = -(u / 2) by ring] at this
    linarith
  · have hlt : Real.exp u < x₀ := not_le.mp hxt
    have hx0 : 0 < x₀ := (Real.exp_pos u).trans hlt
    have hulog : u < Real.log x₀ := by
      rw [← Real.log_exp u]; exact Real.log_lt_log (Real.exp_pos u) hlt
    have huu₀ : u ≤ u₀ := by
      rw [hu₀, abs_of_pos hx0]; exact hulog.le.trans (le_abs_self _)
    have h1 : |η * turanSum (Real.exp u)| ≤ 1 + u := by
      rw [abs_mul, hη, one_mul]; exact abs_turanSum_exp_le hu.le
    have h2 := le_abs_self (η * turanSum (Real.exp u))
    have h3 : 1 + u ≤ (1 + u₀) * Real.exp u₀ * Real.exp (-u) := by
      have hexp : 1 ≤ Real.exp u₀ * Real.exp (-u) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      have hu0' : 0 ≤ u₀ := abs_nonneg _
      nlinarith
    have h5 : 0 ≤ c * Real.exp (-(u / 2)) := mul_nonneg hc hE.le
    linarith

/-- **Turán's problem: a one-sided bound `±T(x) ≤ c/√x` implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_turan_oneSided {η c : ℝ} (hη : |η| = 1) (hc : 0 ≤ c)
    (h : ∀ᶠ x : ℝ in atTop, η * turanSum x ≤ c * x ^ (-(1 / 2) : ℝ)) : RiemannHypothesis := by
  obtain ⟨K, hK, hg⟩ := exists_turan_oneSided_of_eventually hη hc h
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro w hw hzero
  have hid := turan_continuation_identity hη hc (lt_add_one c) hK hg (z := w - 1)
    (by simp; linarith)
  rw [show w - 1 + 1 = w by ring, hzero, mul_zero, mul_zero,
    show 2 * (w - 1) + 2 = 2 * w by ring] at hid
  have hη0 : (η : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; rw [this] at hη; simp at hη
  have h2w : 1 < (2 * w).re := by simp; linarith
  have h2w1 : 2 * w ≠ 1 := by intro h; rw [h, Complex.one_re] at h2w; linarith
  have hZ2 : zetaResidueUnit (2 * w) ≠ 0 := by
    rw [zetaResidueUnit, Function.update_of_ne h2w1]
    exact mul_ne_zero (sub_ne_zero.mpr h2w1) (riemannZeta_ne_zero_of_one_lt_re h2w)
  exact mul_ne_zero hη0 hZ2 hid.symm

/-! ## The bias at `s = -½` -/

/-- `q(z) = Z(2z+2)/(2Z(z+1))`, so that `(z + ½)Q(z) = q(z)`. -/
def turanResidueFactor (z : ℂ) : ℂ := zetaResidueUnit (2 * z + 2) / (2 * zetaResidueUnit (z + 1))

theorem add_half_mul_turanKernel {z : ℂ} (hz : 2 * z + 1 ≠ 0) :
    (z + 1 / 2) * turanKernel z = turanResidueFactor z := by
  unfold turanKernel turanResidueFactor
  rw [show z + 1 / 2 = (2 * z + 1) / 2 by ring]
  by_cases hZ : zetaResidueUnit (z + 1) = 0
  · rw [hZ]; simp
  field_simp

/-- `q(-½) = -1/ζ(½)`. -/
theorem turanResidueFactor_neg_half :
    turanResidueFactor (-(1 / 2)) = -(riemannZeta (1 / 2))⁻¹ := by
  unfold turanResidueFactor
  have hne : (1 / 2 : ℂ) ≠ 1 := by norm_num
  rw [show 2 * (-(1 / 2) : ℂ) + 2 = 1 by norm_num, show (-(1 / 2) : ℂ) + 1 = 1 / 2 by norm_num,
    zetaResidueUnit_one, zetaResidueUnit, Function.update_of_ne hne]
  have hz := riemannZeta_half_eq_re
  have hz0 : riemannZeta (1 / 2) ≠ 0 := by
    rw [hz.1]; exact_mod_cast hz.2.ne
  field_simp
  ring

theorem continuousAt_turanResidueFactor_neg_half :
    ContinuousAt turanResidueFactor (-(1 / 2)) := by
  have hZ : zetaResidueUnit ((-(1 / 2) : ℂ) + 1) ≠ 0 := by
    have := zetaResidueUnit_ofReal_ne_zero (t := 1 / 2) (by norm_num)
    rw [show ((-(1 / 2) : ℂ) + 1) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact this
  unfold turanResidueFactor
  refine ((analyticAt_zetaResidueUnit _).continuousAt.comp
    ((continuousAt_const.mul continuousAt_id).add continuousAt_const)).div
    (continuousAt_const.mul ((analyticAt_zetaResidueUnit _).continuousAt.comp
      (continuousAt_id.add continuousAt_const))) ?_
  exact mul_ne_zero (by norm_num) hZ

/-- At points of `Re z > -½` where `Z(z+1) ≠ 0` the transform of `ν` equals `Φ(z)`. -/
theorem complexLaplace_turanMeasure_eq_of_ne {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ u, 0 < u → η * turanSum (Real.exp u) ≤ ε' * Real.exp (-(u / 2)) + K * Real.exp (-u))
    {z : ℂ} (hz : -(1 / 2) < z.re) (hZ : zetaResidueUnit (z + 1) ≠ 0) :
    complexLaplace (turanMeasure η ε K) z = turanContinuation η ε K z := by
  have hid := turan_continuation_identity hη hε' hεε' hK hg hz
  have h2 : 2 * z + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hden : (2 * z + 1) * zetaResidueUnit (z + 1) ≠ 0 := mul_ne_zero h2 hZ
  have hH : ε / (z + 1 / 2) + K / (z + 1) - complexLaplace (turanMeasure η ε K) z
      = η * turanKernel z := by
    unfold turanKernel
    rw [mul_div_assoc', eq_div_iff hden, hid]
  unfold turanContinuation
  linear_combination (-1 : ℂ) * hH

/-- **The bias.**  `r ∫ e^{-(r-½)u} dν → ε + η/ζ(½)` as `r ↓ 0`. -/
theorem tendsto_mul_laplaceReal_turanMeasure {η ε ε' K : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε')
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ u, 0 < u → η * turanSum (Real.exp u) ≤ ε' * Real.exp (-(u / 2)) + K * Real.exp (-u)) :
    Tendsto (fun r : ℝ => r * laplaceReal (turanMeasure η ε K) (-(1 / 2) + r)) (𝓝[>] 0)
      (𝓝 (ε + η * ((riemannZeta (1 / 2)).re)⁻¹)) := by
  have hz := riemannZeta_half_eq_re
  set z₀ := (riemannZeta (1 / 2)).re with hz₀
  have hq0 : turanResidueFactor (-(1 / 2)) = ((-z₀⁻¹ : ℝ) : ℂ) := by
    rw [turanResidueFactor_neg_half, hz.1]; push_cast; rfl
  have htq : Tendsto (fun r : ℝ => turanResidueFactor (-(1 / 2) + r)) (𝓝[>] 0)
      (𝓝 (turanResidueFactor (-(1 / 2)))) := by
    have h : Tendsto (fun r : ℝ => (-(1 / 2) : ℂ) + r) (𝓝 (0 : ℝ))
        (𝓝 ((-(1 / 2) : ℂ) + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    have h' : Tendsto (fun r : ℝ => (-(1 / 2) : ℂ) + r) (𝓝[>] (0 : ℝ)) (𝓝 (-(1 / 2) : ℂ)) := by
      simpa using h.mono_left nhdsWithin_le_nhds
    exact continuousAt_turanResidueFactor_neg_half.tendsto.comp h'
  have hK' : Tendsto (fun r : ℝ => (r : ℂ) * ((K : ℂ) / ((-(1 / 2) : ℂ) + r + 1))) (𝓝[>] 0)
      (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => (r : ℂ) * ((K : ℂ) / ((-(1 / 2) : ℂ) + r + 1))) (𝓝 (0 : ℝ))
        (𝓝 (((0 : ℝ) : ℂ) * ((K : ℂ) / ((-(1 / 2) : ℂ) + ((0 : ℝ) : ℂ) + 1)))) := by
      refine (Complex.continuous_ofReal.tendsto 0).mul ?_
      refine tendsto_const_nhds.div (((continuous_const.add Complex.continuous_ofReal).add
        continuous_const).tendsto 0) (by norm_num)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hlimC : Tendsto (fun r : ℝ => (ε : ℂ) + (r : ℂ) * ((K : ℂ) / ((-(1 / 2) : ℂ) + r + 1)) -
      η * turanResidueFactor (-(1 / 2) + r)) (𝓝[>] 0)
      (𝓝 ((ε : ℂ) + 0 - η * turanResidueFactor (-(1 / 2)))) :=
    (tendsto_const_nhds.add hK').sub (htq.const_mul _)
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, (ε : ℂ) + (r : ℂ) * ((K : ℂ) / ((-(1 / 2) : ℂ) + r + 1)) -
      η * turanResidueFactor (-(1 / 2) + r) =
      ((r * laplaceReal (turanMeasure η ε K) (-(1 / 2) + r) : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : 0 < r := hr
    have hwre : -(1 / 2) < (((-(1 / 2) + r : ℝ)) : ℂ).re := by simp; linarith
    have hZ : zetaResidueUnit ((((-(1 / 2) + r : ℝ)) : ℂ) + 1) ≠ 0 :=
      zetaResidueUnit_ofReal_add_one_ne_zero (by linarith)
    have hCL := complexLaplace_turanMeasure_eq_of_ne hη hε' hεε' hK hg hwre hZ
    rw [complexLaplace_ofReal] at hCL
    have hcast : (((-(1 / 2) + r : ℝ)) : ℂ) = -(1 / 2) + (r : ℂ) := by push_cast; ring
    rw [hcast] at hCL
    have h2w : 2 * (-(1 / 2) + (r : ℂ)) + 1 ≠ 0 := by
      rw [show 2 * (-(1 / 2) + (r : ℂ)) + 1 = 2 * (r : ℂ) by ring]
      exact mul_ne_zero two_ne_zero (by exact_mod_cast hr0.ne')
    have hq := add_half_mul_turanKernel h2w
    rw [show (-(1 / 2) + (r : ℂ)) + 1 / 2 = (r : ℂ) by ring] at hq
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    rw [Complex.ofReal_mul, hCL, turanContinuation,
      show (-(1 / 2) + (r : ℂ)) + 1 / 2 = (r : ℂ) by ring, ← hq]
    field_simp
  have hlimR := (hlimC.congr' hev)
  have hre := (Complex.continuous_re.tendsto _).comp hlimR
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  convert hre using 2
  rw [hq0]
  simp

/-- **The Turán bias.**  For every `c < -1/ζ(½)`, `T(x) > c/√x` for arbitrarily large `x`: the pole
of `ζ(2s+2)` at `s = -½` gives `T` the positive mean `-1/(ζ(½)√x)`. -/
theorem turanSum_frequently_gt {c : ℝ} (hc : c < -((riemannZeta (1 / 2)).re)⁻¹) :
    ∃ᶠ x : ℝ in atTop, c * x ^ (-(1 / 2) : ℝ) < turanSum x := by
  have hz := riemannZeta_half_eq_re
  set κ : ℝ := -((riemannZeta (1 / 2)).re)⁻¹ with hκ
  have hκ0 : 0 < κ := by rw [hκ]; simp only [neg_pos, inv_lt_zero]; exact hz.2
  set c₀ : ℝ := max c 0 with hc₀
  have hc₀κ : c₀ < κ := max_lt hc hκ0
  have hc₀0 : 0 ≤ c₀ := le_max_right _ _
  suffices h : ∃ᶠ x : ℝ in atTop, c₀ * x ^ (-(1 / 2) : ℝ) < turanSum x by
    refine (h.and_eventually (eventually_gt_atTop 0)).mono fun x ⟨hx, hx0⟩ =>
      lt_of_le_of_lt ?_ hx
    have := Real.rpow_nonneg hx0.le (-(1 / 2) : ℝ)
    have : c ≤ c₀ := le_max_left _ _
    nlinarith
  by_contra hno
  rw [Filter.not_frequently] at hno
  have h' : ∀ᶠ x : ℝ in atTop, (1 : ℝ) * turanSum x ≤ c₀ * x ^ (-(1 / 2) : ℝ) :=
    hno.mono fun x hx => by rw [one_mul]; exact not_lt.mp hx
  obtain ⟨K, hK, hg⟩ := exists_turan_oneSided_of_eventually (by simp) hc₀0 h'
  set ε : ℝ := (c₀ + κ) / 2 with hε
  have hlim := tendsto_mul_laplaceReal_turanMeasure (η := 1) (ε := ε) (by simp) hc₀0
    (by rw [hε]; linarith) hK hg
  have hval : ε + 1 * ((riemannZeta (1 / 2)).re)⁻¹ = ε - κ := by rw [hκ]; ring
  rw [hval] at hlim
  have hnn : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 ≤ r * laplaceReal (turanMeasure 1 ε K) (-(1 / 2) + r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_nonneg (le_of_lt hr) (integral_nonneg fun u => (Real.exp_pos _).le)
  have := ge_of_tendsto hlim hnn
  rw [hε] at this
  linarith

/-- `T(x)` is `Ω₊(x^{-1/2})`. -/
theorem turanSum_omega_pos :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x : ℝ in atTop, c * x ^ (-(1 / 2) : ℝ) < turanSum x := by
  have hz := riemannZeta_half_eq_re
  have hκ : 0 < -((riemannZeta (1 / 2)).re)⁻¹ := by
    simp only [neg_pos, inv_lt_zero]; exact hz.2
  exact ⟨-((riemannZeta (1 / 2)).re)⁻¹ / 2, by linarith,
    turanSum_frequently_gt (by linarith)⟩

end

end RHTower
