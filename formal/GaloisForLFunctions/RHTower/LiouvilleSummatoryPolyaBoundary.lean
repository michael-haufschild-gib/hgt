import GaloisForLFunctions.RHTower.MertensSquareRootOmega
import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries

/-!
# Pólya's problem: one-sided bounds for the Liouville summatory function

Let `L(x) = Σ_{k ≤ x} λ(k)`.  In the logarithmic variable `∫_0^∞ L(e^u) e^{-su} du = ζ(2s)/(sζ(s))`
for `Re s > 1`; with `Z(w) = (w-1)ζ(w)` the kernel is `Q(z) = (z-1)Z(2z)/((2z-1)zZ(z))`, which is
holomorphic on `Re z > ½` off the zeros of `ζ` and has a simple pole at `½` with residue `1/ζ(½)`.

Suppose `ηL(x) ≤ ε'√x` for large `x`, `η = ±1`.  For `ε > ε'` the density
`ε e^{t/2} - ηL(e^t) + K` is nonnegative and at least `(ε - ε')e^{t/2}`; its transform
`ε/(z-½) + K/z - ηQ(z)` is analytic at every real point of `(½, ∞)`, so Landau's theorem puts the
abscissa at `½`, and the identity theorem gives `H(z)(2z-1)zZ(z) = η(z-1)Z(2z)` on `Re z > ½`.

* A zero of `ζ` with `Re ρ > ½` would make the left side vanish while `Z(2ρ) ≠ 0`: **either
  one-sided bound implies RH** (Pólya's problem; Ingham's theorem).
* At real `½ + r` the transform equals the continuation, and `r·Q(½ + r) → 1/ζ(½)`, so
  `r ∫ e^{-(½+r)t} dν → ε - η/ζ(½)`.  Since `ζ(½) < 0`, a lower bound `L(x) ≥ -c√x` with
  `c < -1/ζ(½)` makes this limit negative: **`L(x) = Ω₋(√x)`, with the explicit bias `1/ζ(½)`**.
* Along `ρ + r` at a critical zero the same bound and the local factorization give **simplicity**
  and the residue bound `|ρ-1||Z(2ρ)|/(|2ρ-1||ρ||G(ρ)|) ≤ ε' - η/ζ(½)`.
* The constant `ε'` may have either sign.  Applied around the bias with a Hardy zero, the residue
  bound gives **`L(x) - √x/ζ(½) = Ω±(√x)`**: `L` oscillates on both sides of its mean.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open scoped LSeries.notation

namespace RHTower

noncomputable section

/-! ## The Liouville summatory function -/

/-- `L(x) = Σ_{1 ≤ k ≤ x} λ(k)`. -/
def liouvilleSummatory (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.liouville k : ℤ) : ℝ)

theorem abs_liouville_le_one (k : ℕ) : |((ArithmeticFunction.liouville k : ℤ) : ℝ)| ≤ 1 := by
  have h := norm_liouvilleC_le_one k
  rw [liouvilleC_apply, show ((ArithmeticFunction.liouville k : ℤ) : ℂ)
    = ((((ArithmeticFunction.liouville k : ℤ) : ℝ)) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem abs_liouvilleSummatory_le (x : ℝ) : |liouvilleSummatory x| ≤ ⌊x⌋₊ := by
  unfold liouvilleSummatory
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |((ArithmeticFunction.liouville k : ℤ) : ℝ)|
      ≤ ∑ _k ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => abs_liouville_le_one k
    _ = ⌊x⌋₊ := by simp

theorem abs_liouvilleSummatory_exp_le (t : ℝ) :
    |liouvilleSummatory (Real.exp t)| ≤ Real.exp t :=
  (abs_liouvilleSummatory_le _).trans (Nat.floor_le (Real.exp_pos t).le)

theorem measurable_liouvilleSummatory : Measurable liouvilleSummatory := by
  have : liouvilleSummatory = (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      ((ArithmeticFunction.liouville k : ℤ) : ℝ)) ∘ Nat.floor := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

/-- `L(λ, s) = ζ(2s)/ζ(s)` on `Re s > 1`. -/
theorem LSeries_liouvilleC_eq_div {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗liouvilleC s = riemannZeta (2 * s) / riemannZeta s := by
  rw [eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)]
  exact LSeries_liouvilleC_mul_riemannZeta hs

/-- **The Mellin transform of `L` in the logarithmic variable.**
`∫_0^∞ L(e^u) e^{-su} du = ζ(2s)/(sζ(s))` for `Re s > 1`. -/
theorem integral_liouvilleSummatory_exp_mul_cexp {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), (liouvilleSummatory (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = riemannZeta (2 * s) / (s * riemannZeta s) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖liouvilleC k‖)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    have hle : ∑ k ∈ Finset.Icc 1 n, ‖liouvilleC k‖ ≤ (n : ℝ) := by
      refine le_trans (Finset.sum_le_sum fun k _ => norm_liouvilleC_le_one k) ?_
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      simp
    have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, ‖liouvilleC k‖ :=
      Finset.sum_nonneg fun k _ => norm_nonneg _
    rw [Real.rpow_one, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hnn, abs_of_nonneg (Nat.cast_nonneg n)]
    exact hle
  have hM := LSeries_eq_mul_integral' (fun n : ℕ => liouvilleC n) (r := 1) zero_le_one hs hO
  rw [LSeries_liouvilleC_eq_div hs] at hM
  rw [← image_exp_Ioi_zero, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn] at hM
  have hcongr : ∫ u in Ioi (0 : ℝ), |Real.exp u| • ((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊,
        liouvilleC k) * ((Real.exp u : ℝ) : ℂ) ^ (-(s + 1)))
      = ∫ u in Ioi (0 : ℝ), (liouvilleSummatory (Real.exp u) : ℂ) * Complex.exp (-s * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hcpow : ((Real.exp u : ℝ) : ℂ) ^ (-(s + 1)) = Complex.exp (u * (-(s + 1))) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
        ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    rw [abs_of_pos (Real.exp_pos u), hcpow, Complex.real_smul, Complex.ofReal_exp]
    unfold liouvilleSummatory
    simp only [liouvilleC_apply]
    push_cast
    rw [mul_comm (Complex.exp (u : ℂ)), mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hcongr] at hM
  set I := ∫ u in Ioi (0 : ℝ), (liouvilleSummatory (Real.exp u) : ℂ) * Complex.exp (-s * u)
  calc I = s * I / s := by field_simp
    _ = riemannZeta (2 * s) / riemannZeta s / s := by rw [hM]
    _ = riemannZeta (2 * s) / (s * riemannZeta s) := by rw [div_div, mul_comm (riemannZeta s)]

/-! ## The continuation kernel -/

/-- `Q(z) = (z-1)Z(2z)/((2z-1)zZ(z)) = ζ(2z)/(zζ(z))`, `Z(w) = (w-1)ζ(w)`. -/
def liouvilleKernel (z : ℂ) : ℂ :=
  (z - 1) * zetaResidueUnit (2 * z) / ((2 * z - 1) * z * zetaResidueUnit z)

theorem liouvilleKernel_eq {s : ℂ} (hs : s ≠ 1) (hs2 : 2 * s ≠ 1) :
    liouvilleKernel s = riemannZeta (2 * s) / (s * riemannZeta s) := by
  unfold liouvilleKernel
  rw [zetaResidueUnit, Function.update_of_ne hs, Function.update_of_ne hs2]
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have h2 : 2 * s - 1 ≠ 0 := sub_ne_zero.mpr hs2
  by_cases hs0 : s = 0
  · rw [hs0]; simp
  by_cases hz : riemannZeta s = 0
  · rw [hz]; simp
  have h2' : s * 2 - 1 ≠ 0 := by rwa [mul_comm] at h2
  field_simp

theorem analyticAt_liouvilleKernel {z : ℂ} (hz0 : z ≠ 0) (hzh : z ≠ 1 / 2)
    (hz : zetaResidueUnit z ≠ 0) : AnalyticAt ℂ liouvilleKernel z := by
  unfold liouvilleKernel
  have h2 : 2 * z - 1 ≠ 0 := by
    intro h; apply hzh; linear_combination h / 2
  exact ((analyticAt_id.sub analyticAt_const).mul ((analyticAt_zetaResidueUnit _).comp
    (analyticAt_const.mul analyticAt_id))).div
    (((analyticAt_const.mul analyticAt_id).sub analyticAt_const).mul analyticAt_id |>.mul
      (analyticAt_zetaResidueUnit z)) (mul_ne_zero (mul_ne_zero h2 hz0) hz)

/-! ## The one-sided measure -/

/-- The clipped density `ε e^{t/2} - ηL(e^t) + K`. -/
def liouvilleDensity (η ε K : ℝ) (t : ℝ) : NNReal :=
  Real.toNNReal (ε * Real.exp (t / 2) - η * liouvilleSummatory (Real.exp t) + K)

theorem measurable_liouvilleDensity (η ε K : ℝ) : Measurable (liouvilleDensity η ε K) := by
  unfold liouvilleDensity
  refine Measurable.real_toNNReal ?_
  refine Measurable.add (Measurable.sub ?_ ?_) measurable_const
  · exact measurable_const.mul (Real.measurable_exp.comp (measurable_id.div_const 2))
  · exact measurable_const.mul (measurable_liouvilleSummatory.comp Real.measurable_exp)

/-- `ν = (ε e^{t/2} - ηL(e^t) + K) dt` on `(0, ∞)`. -/
def liouvilleMeasure (η ε K : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun u => (liouvilleDensity η ε K u : ENNReal))

theorem liouvilleDensity_le {η ε K : ℝ} (hη : |η| = 1) (hK : 0 ≤ K) {t : ℝ}
    (ht : 0 < t) : ((liouvilleDensity η ε K t : ℝ)) ≤ (|ε| + K + 1) * Real.exp t := by
  unfold liouvilleDensity
  rw [Real.coe_toNNReal']
  have h1 : Real.exp (t / 2) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
  have h2 : -(η * liouvilleSummatory (Real.exp t)) ≤ Real.exp t := by
    have h3 : |η * liouvilleSummatory (Real.exp t)| ≤ Real.exp t := by
      rw [abs_mul, hη, one_mul]; exact abs_liouvilleSummatory_exp_le t
    linarith [neg_abs_le (η * liouvilleSummatory (Real.exp t))]
  have h4 : 1 ≤ Real.exp t := Real.one_le_exp ht.le
  have hE := Real.exp_pos t
  have hE2 := Real.exp_pos (t / 2)
  have h5 : ε * Real.exp (t / 2) ≤ |ε| * Real.exp t := by
    calc ε * Real.exp (t / 2) ≤ |ε| * Real.exp (t / 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self ε) hE2.le
      _ ≤ |ε| * Real.exp t := mul_le_mul_of_nonneg_left h1 (abs_nonneg ε)
  refine max_le ?_ (by positivity)
  nlinarith

theorem liouvilleDensity_coe {η ε ε' K : ℝ} (hεε' : ε' ≤ ε)
    (hg : ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {t : ℝ} (ht : 0 < t) :
    ((liouvilleDensity η ε K t : ℝ))
      = ε * Real.exp (t / 2) - η * liouvilleSummatory (Real.exp t) + K := by
  unfold liouvilleDensity
  have h := hg t ht
  have hE := Real.exp_pos (t / 2)
  rw [Real.coe_toNNReal _ (by nlinarith)]

theorem laplaceMass_liouvilleMeasure_ne_top {η ε K σ : ℝ} (hη : |η| = 1)
    (hK : 0 ≤ K) (hσ : 1 < σ) : laplaceMass (liouvilleMeasure η ε K) σ ≠ ⊤ := by
  unfold laplaceMass liouvilleMeasure
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_liouvilleDensity η ε K).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top
    (integrableOn_exp_majorant (C := |ε| + K + 1) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (liouvilleDensity_le hη hK hu) (Real.exp_pos _).le

theorem laplaceMass_liouvilleMeasure_eq_top {η ε ε' K σ : ℝ} (hεε' : ε' < ε)
    (hg : ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    (hσ : σ ≤ 1 / 2) : laplaceMass (liouvilleMeasure η ε K) σ = ⊤ := by
  unfold laplaceMass liouvilleMeasure
  have hg' : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_liouvilleDensity η ε K).coe_nnreal_ennreal hg', eq_top_iff]
  have hdl : 0 < ε - ε' := by linarith
  calc (⊤ : ENNReal) = ENNReal.ofReal (ε - ε') * volume (Ioi (0 : ℝ)) := by
        rw [Real.volume_Ioi, ENNReal.mul_top (by simpa using hdl)]
    _ = ∫⁻ _ in Ioi (0 : ℝ), ENNReal.ofReal (ε - ε') := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), ((fun u => (liouvilleDensity η ε K u : ENNReal))
          * fun u => ENNReal.ofReal (Real.exp (-σ * u))) u := by
        refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [liouvilleDensity_coe hεε'.le hg hu0]
        have h1 := hg u hu0
        have h2 : 1 ≤ Real.exp (u / 2) * Real.exp (-σ * u) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have hE := Real.exp_pos (-σ * u)
        have hE2 := Real.exp_pos (u / 2)
        have h3 : (ε - ε') * Real.exp (u / 2) ≤ ε * Real.exp (u / 2)
            - η * liouvilleSummatory (Real.exp u) + K := by linarith
        calc ε - ε' ≤ (ε - ε') * (Real.exp (u / 2) * Real.exp (-σ * u)) :=
              le_mul_of_one_le_right hdl.le h2
          _ = (ε - ε') * Real.exp (u / 2) * Real.exp (-σ * u) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h3 hE.le

theorem isAbscissa_liouvilleMeasure {η ε ε' K : ℝ} (hη : |η| = 1)
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ ε' * Real.exp (t / 2) + K) :
    IsAbscissa (liouvilleMeasure η ε K)
        (sInf {σ : ℝ | laplaceMass (liouvilleMeasure η ε K) σ ≠ ⊤})
      ∧ 1 / 2 ≤ sInf {σ : ℝ | laplaceMass (liouvilleMeasure η ε K) σ ≠ ⊤}
      ∧ sInf {σ : ℝ | laplaceMass (liouvilleMeasure η ε K) σ ≠ ⊤} ≤ 2 := by
  set S := {σ : ℝ | laplaceMass (liouvilleMeasure η ε K) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, 1 / 2 < σ := by
    intro σ hσ
    by_contra hle
    exact hσ (laplaceMass_liouvilleMeasure_eq_top hεε' hg (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨1 / 2, fun σ hσ => (hpos σ hσ).le⟩
  have h2S : (2 : ℝ) ∈ S := laplaceMass_liouvilleMeasure_ne_top hη hK (by norm_num)
  have hne : S.Nonempty := ⟨2, h2S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le,
    csInf_le hbdd h2S⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The transform and Landau's theorem -/

/-- The continuation `Φ(z) = ε/(z-½) + K/z - ηQ(z)`. -/
def liouvilleContinuation (η ε K : ℝ) (z : ℂ) : ℂ :=
  ε / (z - 1 / 2) + K / z - η * liouvilleKernel z

theorem analyticAt_liouvilleContinuation (η ε K : ℝ) {z : ℂ} (hzh : z ≠ 1 / 2) (hz0 : z ≠ 0)
    (hz : zetaResidueUnit z ≠ 0) : AnalyticAt ℂ (liouvilleContinuation η ε K) z := by
  unfold liouvilleContinuation
  exact ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzh)).add
    (analyticAt_const.div analyticAt_id hz0)).sub
    (analyticAt_const.mul (analyticAt_liouvilleKernel hz0 hzh hz))

/-- On `Re s > 1` the complex transform of `ν` is `Φ(s)`. -/
theorem complexLaplace_liouvilleMeasure_eq {η ε ε' K : ℝ} (hεε' : ε' ≤ ε)
    (hg : ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {s : ℂ} (hs : 1 < s.re) :
    complexLaplace (liouvilleMeasure η ε K) s = liouvilleContinuation η ε K s := by
  have hs0 : 0 < s.re := by linarith
  have hsh : 0 < (s - 1 / 2).re := by simp; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs; linarith
  have hs2 : 2 * s ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hcexp : ∀ w : ℂ, Continuous (fun u : ℝ => Complex.exp (-w * (u : ℂ))) := fun w =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hexpInt : ∀ w : ℂ, 0 < w.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-w * (u : ℂ))) (Ioi 0) := fun w hw =>
    (exp_neg_integrableOn_Ioi 0 hw).mono' (hcexp w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  have hLint : IntegrableOn
      (fun u : ℝ => (liouvilleSummatory (Real.exp u) : ℂ) * Complex.exp (-s * u))
      (Ioi 0) := by
    have hmaj : IntegrableOn (fun u : ℝ => Real.exp (-(s.re - 1) * u)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (by linarith)
    refine hmaj.mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.measurable.comp
        (measurable_liouvilleSummatory.comp Real.measurable_exp)).aestronglyMeasurable.mul
        (hcexp s).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u _
      rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |liouvilleSummatory (Real.exp u)| * Real.exp (-s.re * u)
          ≤ Real.exp u * Real.exp (-s.re * u) :=
            mul_le_mul_of_nonneg_right (abs_liouvilleSummatory_exp_le u) (Real.exp_pos _).le
        _ = Real.exp (-(s.re - 1) * u) := by rw [← Real.exp_add]; ring_nf
  unfold complexLaplace liouvilleMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul (measurable_liouvilleDensity η ε K)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), liouvilleDensity η ε K u • Complex.exp (-s * (u : ℂ))
      = ((ε : ℂ) * Complex.exp (-(s - 1 / 2) * (u : ℂ)) + (K : ℂ) * Complex.exp (-s * (u : ℂ)))
        - (η : ℂ) * ((liouvilleSummatory (Real.exp u) : ℂ) * Complex.exp (-s * u)) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul, liouvilleDensity_coe hεε' hg hu]
    push_cast
    rw [show Complex.exp (-(s - 1 / 2) * (u : ℂ))
      = Complex.exp ((u : ℂ) / 2) * Complex.exp (-s * (u : ℂ)) by
        rw [← Complex.exp_add]; congr 1; ring]
    ring
  have i1 : IntegrableOn (fun u : ℝ => (ε : ℂ) * Complex.exp (-(s - 1 / 2) * (u : ℂ))) (Ioi 0) :=
    (hexpInt _ hsh).const_mul _
  have i2 : IntegrableOn (fun u : ℝ => (K : ℂ) * Complex.exp (-s * (u : ℂ))) (Ioi 0) :=
    (hexpInt _ hs0).const_mul _
  have i3 : IntegrableOn (fun u : ℝ => (η : ℂ) * ((liouvilleSummatory (Real.exp u) : ℂ)
      * Complex.exp (-s * u))) (Ioi 0) := hLint.const_mul _
  have i12 : IntegrableOn (fun u : ℝ => (ε : ℂ) * Complex.exp (-(s - 1 / 2) * (u : ℂ))
      + (K : ℂ) * Complex.exp (-s * (u : ℂ))) (Ioi 0) := i1.add i2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_cexp_neg_mul_Ioi hsh,
    integral_cexp_neg_mul_Ioi hs0, integral_liouvilleSummatory_exp_mul_cexp hs]
  unfold liouvilleContinuation
  rw [liouvilleKernel_eq hs1 hs2]
  ring

/-- **Landau: the abscissa of `ν` is `½`.** -/
theorem abscissa_liouvilleMeasure_eq {η ε ε' K : ℝ} (hη : |η| = 1)
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ ε' * Real.exp (t / 2) + K) :
    IsAbscissa (liouvilleMeasure η ε K) (1 / 2) := by
  obtain ⟨hc, hac, hc2⟩ := isAbscissa_liouvilleMeasure hη hεε' hK hg
  set c : ℝ := sInf {σ : ℝ | laplaceMass (liouvilleMeasure η ε K) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hcpos : 0 < c := by linarith
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hch : (c : ℂ) ≠ 1 / 2 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hZ : zetaResidueUnit (c : ℂ) ≠ 0 := zetaResidueUnit_ofReal_ne_zero hcpos
    have hev : ∀ᶠ z in 𝓝 (c : ℂ), zetaResidueUnit z ≠ 0 ∧ z ≠ 0 ∧ z ≠ 1 / 2 :=
      ((analyticAt_zetaResidueUnit _).continuousAt.eventually_ne hZ).and
        ((eventually_ne_nhds hc0).and (eventually_ne_nhds hch))
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine false_of_analyticAt_abscissa hc hd (Φ := liouvilleContinuation η ε K) ?_ ?_
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := hball hz
      exact analyticAt_liouvilleContinuation η ε K h3 h2 h1
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (liouvilleMeasure η ε K))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (liouvilleMeasure η ε K) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (liouvilleMeasure η ε K)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => liouvilleContinuation η ε K (t : ℂ)) (Ioi c) := by
        intro t ht
        have hth : 1 / 2 < t := lt_trans hpos ht
        have ht0 : 0 < t := by linarith
        have h1 : AnalyticAt ℂ (liouvilleContinuation η ε K) (t : ℂ) := by
          refine analyticAt_liouvilleContinuation η ε K ?_ (by exact_mod_cast ht0.ne')
            (zetaResidueUnit_ofReal_ne_zero ht0)
          intro h
          have := congrArg Complex.re h
          simp at this
          linarith
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h3mem : (3 : ℝ) ∈ Ioi c := by show c < 3; linarith
      have hfg : (fun t : ℝ => complexLaplace (liouvilleMeasure η ε K) (t : ℂ)) =ᶠ[𝓝 (3 : ℝ)]
          (fun t : ℝ => liouvilleContinuation η ε K (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (2 : ℝ) < 3) (by norm_num : (3 : ℝ) < 4)) fun t ht => ?_
        have ht1 : 1 < (t : ℂ).re := by simp; linarith [ht.1]
        exact complexLaplace_liouvilleMeasure_eq hεε'.le hg ht1
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h3mem hfg
      have hσ : complexLaplace (liouvilleMeasure η ε K) (σ : ℂ)
          = liouvilleContinuation η ε K (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **The continuation identity on `Re z > ½`.**
`H(z)·(2z-1)·z·Z(z) = η(z-1)Z(2z)`, `H(z) = ε/(z-½) + K/z - ∫ e^{-zt} dν`. -/
theorem liouville_continuation_identity {η ε ε' K : ℝ} (hη : |η| = 1)
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    (ε / (z - 1 / 2) + K / z - complexLaplace (liouvilleMeasure η ε K) z)
      * ((2 * z - 1) * z * zetaResidueUnit z) = η * ((z - 1) * zetaResidueUnit (2 * z)) := by
  have hc := abscissa_liouvilleMeasure_eq hη hεε' hK hg
  set U : Set ℂ := {w : ℂ | 1 / 2 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hne0 : ∀ w ∈ U, w ≠ 0 := fun w hw h => by
    rw [h] at hw; simp [hU] at hw; linarith
  have hneh : ∀ w ∈ U, w - 1 / 2 ≠ 0 := fun w hw h => by
    have := congrArg Complex.re h; simp [hU] at this hw; linarith
  set F : ℂ → ℂ := fun w => (ε / (w - 1 / 2) + K / w
    - complexLaplace (liouvilleMeasure η ε K) w) * ((2 * w - 1) * w * zetaResidueUnit w) with hF
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (ε : ℂ) / (w - 1 / 2)) w :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
        (hneh w hw)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (K : ℂ) / w) w :=
      (differentiableAt_const _).div differentiableAt_id (hne0 w hw)
    have h3 := (hasDerivAt_complexLaplace hc hw).differentiableAt
    have h4 : DifferentiableAt ℂ (fun w => (2 * w - 1) * w * zetaResidueUnit w) w :=
      (((differentiableAt_const _).mul differentiableAt_id).sub (differentiableAt_const _)).mul
        differentiableAt_id |>.mul (analyticAt_zetaResidueUnit w).differentiableAt
    exact (((h1.add h2).sub h3).mul h4).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hUo
  have hGa : AnalyticOnNhd ℂ (fun w : ℂ => (η : ℂ) * ((w - 1) * zetaResidueUnit (2 * w))) U :=
    fun w _ => analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).mul
      ((analyticAt_zetaResidueUnit _).comp (analyticAt_const.mul analyticAt_id)))
  have h2U : (2 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : F =ᶠ[𝓝 (2 : ℂ)] fun w : ℂ => (η : ℂ) * ((w - 1) * zetaResidueUnit (2 * w)) := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    have hw1 : 1 < w.re := hw
    have hw0 : w ≠ 0 := by intro h; rw [h, Complex.zero_re] at hw1; linarith
    have hw1' : w ≠ 1 := by intro h; rw [h, Complex.one_re] at hw1; linarith
    have hw2 : 2 * w - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hZ : zetaResidueUnit w ≠ 0 := by
      rw [zetaResidueUnit, Function.update_of_ne hw1']
      exact mul_ne_zero (sub_ne_zero.mpr hw1') (riemannZeta_ne_zero_of_one_lt_re hw1)
    simp only [hF]
    rw [complexLaplace_liouvilleMeasure_eq hεε'.le hg hw1, liouvilleContinuation]
    have hden : (2 * w - 1) * w * zetaResidueUnit w ≠ 0 := mul_ne_zero (mul_ne_zero hw2 hw0) hZ
    have e : liouvilleKernel w * ((2 * w - 1) * w * zetaResidueUnit w) =
        (w - 1) * zetaResidueUnit (2 * w) := by
      unfold liouvilleKernel; exact div_mul_cancel₀ _ hden
    linear_combination (η : ℂ) * e
  have hEq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (convex_halfSpace_re_gt _).isPreconnected h2U hev
  exact hEq hz

theorem exists_liouville_oneSided_of_eventually {η c : ℝ} (hη : |η| = 1)
    (h : ∀ᶠ x : ℝ in atTop, η * liouvilleSummatory x ≤ c * Real.sqrt x) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ c * Real.exp (t / 2) + K := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp h
  refine ⟨(1 + |c|) * |x₀|, by positivity, fun t ht => ?_⟩
  have hE := Real.exp_pos (t / 2)
  have hK0 : 0 ≤ (1 + |c|) * |x₀| := by positivity
  by_cases hxt : x₀ ≤ Real.exp t
  · have := hx₀ (Real.exp t) hxt
    rw [sqrt_exp_eq_exp_half_mul, show 1 / 2 * t = t / 2 by ring] at this
    linarith
  · have h1 : |η * liouvilleSummatory (Real.exp t)| ≤ Real.exp t := by
      rw [abs_mul, hη, one_mul]; exact abs_liouvilleSummatory_exp_le t
    have h2 := le_abs_self (η * liouvilleSummatory (Real.exp t))
    have h3 : Real.exp t < x₀ := not_le.mp hxt
    have h4 := le_abs_self x₀
    have h6 : Real.exp (t / 2) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
    have h7 : -(|c| * |x₀|) ≤ c * Real.exp (t / 2) := by
      have : |c * Real.exp (t / 2)| ≤ |c| * |x₀| := by
        rw [abs_mul, abs_of_pos hE]
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
      linarith [neg_abs_le (c * Real.exp (t / 2))]
    nlinarith

/-- **Pólya's problem: a one-sided square-root bound for `L` implies the Riemann hypothesis.**
Either `L(x) ≤ c√x` or `L(x) ≥ -c√x` for all large `x` forces RH. -/
theorem riemannHypothesis_of_liouville_oneSided {η c : ℝ} (hη : |η| = 1)
    (h : ∀ᶠ x : ℝ in atTop, η * liouvilleSummatory x ≤ c * Real.sqrt x) : RiemannHypothesis := by
  obtain ⟨K, hK, hg⟩ := exists_liouville_oneSided_of_eventually hη h
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro z hz hzero
  have hid := liouville_continuation_identity hη (lt_add_one c) hK hg hz
  rw [hzero, mul_zero, mul_zero] at hid
  have hη0 : (η : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; rw [this] at hη; simp at hη
  have hz1 : z ≠ 1 := by
    intro h1; rw [h1, zetaResidueUnit_one] at hzero; exact one_ne_zero hzero
  have h2z : 1 < (2 * z).re := by simp; linarith
  have h2z1 : 2 * z ≠ 1 := by intro h; rw [h, Complex.one_re] at h2z; linarith
  have hZ2 : zetaResidueUnit (2 * z) ≠ 0 := by
    rw [zetaResidueUnit, Function.update_of_ne h2z1]
    exact mul_ne_zero (sub_ne_zero.mpr h2z1) (riemannZeta_ne_zero_of_one_lt_re h2z)
  exact mul_ne_zero hη0 (mul_ne_zero (sub_ne_zero.mpr hz1) hZ2) hid.symm

/-! ## The bias at `s = ½` -/

/-- `q(z) = (z-1)Z(2z)/(2zZ(z))`, so that `(z - ½)Q(z) = q(z)`. -/
def liouvilleResidueFactor (z : ℂ) : ℂ :=
  (z - 1) * zetaResidueUnit (2 * z) / (2 * z * zetaResidueUnit z)

theorem sub_half_mul_liouvilleKernel {z : ℂ} (hz : 2 * z - 1 ≠ 0) :
    (z - 1 / 2) * liouvilleKernel z = liouvilleResidueFactor z := by
  unfold liouvilleKernel liouvilleResidueFactor
  rw [show z - 1 / 2 = (2 * z - 1) / 2 by ring]
  by_cases hz0 : z = 0
  · rw [hz0]; simp
  by_cases hZ : zetaResidueUnit z = 0
  · rw [hZ]; simp
  field_simp

theorem riemannZeta_half_eq_re : riemannZeta (1 / 2) = ((riemannZeta (1 / 2)).re : ℂ) ∧
    (riemannZeta (1 / 2)).re < 0 := by
  obtain ⟨x, hx, hzx⟩ := riemannZeta_real_strip_neg (σ := 1 / 2) (by norm_num) (by norm_num)
  have h : riemannZeta (1 / 2) = (x : ℂ) := by simpa using hzx
  rw [h]
  simp [hx]

/-- `q(½) = 1/ζ(½)`. -/
theorem liouvilleResidueFactor_half : liouvilleResidueFactor (1 / 2) = (riemannZeta (1 / 2))⁻¹ := by
  unfold liouvilleResidueFactor
  have hne : (1 / 2 : ℂ) ≠ 1 := by norm_num
  rw [show 2 * (1 / 2 : ℂ) = 1 by norm_num, zetaResidueUnit_one, zetaResidueUnit,
    Function.update_of_ne hne]
  have hz := riemannZeta_half_eq_re
  have hz0 : riemannZeta (1 / 2) ≠ 0 := by
    rw [hz.1]; exact_mod_cast hz.2.ne
  field_simp

theorem continuousAt_liouvilleResidueFactor_half :
    ContinuousAt liouvilleResidueFactor (1 / 2) := by
  have hZ : zetaResidueUnit (1 / 2 : ℂ) ≠ 0 := by
    have := zetaResidueUnit_ofReal_ne_zero (t := 1 / 2) (by norm_num)
    simpa using this
  unfold liouvilleResidueFactor
  refine ((continuousAt_id.sub continuousAt_const).mul
    ((analyticAt_zetaResidueUnit _).continuousAt.comp
      (continuousAt_const.mul continuousAt_id))).div
    ((continuousAt_const.mul continuousAt_id).mul (analyticAt_zetaResidueUnit _).continuousAt) ?_
  exact mul_ne_zero (by norm_num) hZ

/-- At points of `Re z > ½` where `Z(z) ≠ 0` the transform of `ν` equals `Φ(z)`. -/
theorem complexLaplace_liouvilleMeasure_eq_of_ne {η ε ε' K : ℝ} (hη : |η| = 1)
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {z : ℂ} (hz : 1 / 2 < z.re) (hZ : zetaResidueUnit z ≠ 0) :
    complexLaplace (liouvilleMeasure η ε K) z = liouvilleContinuation η ε K z := by
  have hid := liouville_continuation_identity hη hεε' hK hg hz
  have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz; linarith
  have h2 : 2 * z - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hden : (2 * z - 1) * z * zetaResidueUnit z ≠ 0 := mul_ne_zero (mul_ne_zero h2 hz0) hZ
  have hH : ε / (z - 1 / 2) + K / z - complexLaplace (liouvilleMeasure η ε K) z
      = η * liouvilleKernel z := by
    unfold liouvilleKernel
    rw [mul_div_assoc', eq_div_iff hden, hid]
  unfold liouvilleContinuation
  linear_combination (-1 : ℂ) * hH

/-- **The bias.**  `r ∫ e^{-(½+r)t} dν → ε - η/ζ(½)` as `r ↓ 0`. -/
theorem tendsto_mul_laplaceReal_liouvilleMeasure {η ε ε' K : ℝ} (hη : |η| = 1)
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ ε' * Real.exp (t / 2) + K) :
    Tendsto (fun r : ℝ => r * laplaceReal (liouvilleMeasure η ε K) (1 / 2 + r)) (𝓝[>] 0)
      (𝓝 (ε - η * ((riemannZeta (1 / 2)).re)⁻¹)) := by
  have hz := riemannZeta_half_eq_re
  set z₀ := (riemannZeta (1 / 2)).re with hz₀
  have hq0 : liouvilleResidueFactor (1 / 2) = ((z₀⁻¹ : ℝ) : ℂ) := by
    rw [liouvilleResidueFactor_half, hz.1]; push_cast; rfl
  -- complex form of the limit
  have htq : Tendsto (fun r : ℝ => liouvilleResidueFactor (1 / 2 + r)) (𝓝[>] 0)
      (𝓝 (liouvilleResidueFactor (1 / 2))) := by
    have h : Tendsto (fun r : ℝ => (1 / 2 : ℂ) + r) (𝓝 (0 : ℝ)) (𝓝 ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    have h' : Tendsto (fun r : ℝ => (1 / 2 : ℂ) + r) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by
      simpa using h.mono_left nhdsWithin_le_nhds
    exact continuousAt_liouvilleResidueFactor_half.tendsto.comp h'
  have hK' : Tendsto (fun r : ℝ => (r : ℂ) * ((K : ℂ) / (1 / 2 + r))) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => (r : ℂ) * ((K : ℂ) / (1 / 2 + r))) (𝓝 (0 : ℝ))
        (𝓝 (((0 : ℝ) : ℂ) * ((K : ℂ) / (1 / 2 + ((0 : ℝ) : ℂ))))) := by
      refine (Complex.continuous_ofReal.tendsto 0).mul ?_
      refine tendsto_const_nhds.div ((continuous_const.add Complex.continuous_ofReal).tendsto 0)
        (by norm_num)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hlimC : Tendsto (fun r : ℝ => (ε : ℂ) + (r : ℂ) * ((K : ℂ) / (1 / 2 + r)) -
      η * liouvilleResidueFactor (1 / 2 + r)) (𝓝[>] 0)
      (𝓝 ((ε : ℂ) + 0 - η * liouvilleResidueFactor (1 / 2))) :=
    (tendsto_const_nhds.add hK').sub (htq.const_mul _)
  -- identify with the real transform
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, (ε : ℂ) + (r : ℂ) * ((K : ℂ) / (1 / 2 + r)) -
      η * liouvilleResidueFactor (1 / 2 + r) =
      ((r * laplaceReal (liouvilleMeasure η ε K) (1 / 2 + r) : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : 0 < r := hr
    have hwre : 1 / 2 < (((1 / 2 + r : ℝ)) : ℂ).re := by simp; linarith
    have hZ : zetaResidueUnit (((1 / 2 + r : ℝ)) : ℂ) ≠ 0 :=
      zetaResidueUnit_ofReal_ne_zero (by linarith)
    have hCL := complexLaplace_liouvilleMeasure_eq_of_ne hη hεε' hK hg hwre hZ
    rw [complexLaplace_ofReal] at hCL
    have hcast : (((1 / 2 + r : ℝ)) : ℂ) = 1 / 2 + (r : ℂ) := by push_cast; ring
    rw [hcast] at hCL
    have h2w : 2 * (1 / 2 + (r : ℂ)) - 1 ≠ 0 := by
      rw [show 2 * (1 / 2 + (r : ℂ)) - 1 = 2 * (r : ℂ) by ring]
      exact mul_ne_zero two_ne_zero (by exact_mod_cast hr0.ne')
    have hq := sub_half_mul_liouvilleKernel h2w
    rw [show (1 / 2 + (r : ℂ)) - 1 / 2 = (r : ℂ) by ring] at hq
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    rw [Complex.ofReal_mul, hCL, liouvilleContinuation,
      show (1 / 2 + (r : ℂ)) - 1 / 2 = (r : ℂ) by ring, ← hq]
    field_simp
  have hlimR := (hlimC.congr' hev)
  have hre := (Complex.continuous_re.tendsto _).comp hlimR
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  convert hre using 2
  rw [hq0]
  simp

/-- **The Liouville bias.**  For every `c < -1/ζ(½)`, `L(x) < -c√x` for arbitrarily large `x`:
the pole of `ζ(2s)` at `s = ½` gives `L` a negative mean `√x/ζ(½)` that no lower bound can beat. -/
theorem liouvilleSummatory_frequently_lt_neg {c : ℝ}
    (hc : c < -((riemannZeta (1 / 2)).re)⁻¹) :
    ∃ᶠ x : ℝ in atTop, liouvilleSummatory x < -(c * Real.sqrt x) := by
  set κ : ℝ := -((riemannZeta (1 / 2)).re)⁻¹ with hκ
  by_contra hno
  rw [Filter.not_frequently] at hno
  have h' : ∀ᶠ x : ℝ in atTop, (-1 : ℝ) * liouvilleSummatory x ≤ c * Real.sqrt x :=
    hno.mono fun x hx => by have := not_lt.mp hx; linarith
  obtain ⟨K, hK, hg⟩ := exists_liouville_oneSided_of_eventually (by simp) h'
  set ε : ℝ := (c + κ) / 2 with hε
  have hlim := tendsto_mul_laplaceReal_liouvilleMeasure (η := -1) (ε := ε) (by simp)
    (by rw [hε]; linarith) hK hg
  have hval : ε - (-1) * ((riemannZeta (1 / 2)).re)⁻¹ = ε - κ := by rw [hκ]; ring
  rw [hval] at hlim
  have hnn : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 ≤ r * laplaceReal (liouvilleMeasure (-1) ε K) (1 / 2 + r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_nonneg (le_of_lt hr) (integral_nonneg fun u => (Real.exp_pos _).le)
  have := ge_of_tendsto hlim hnn
  rw [hε] at this
  linarith

/-- `L(x)` is `Ω₋(√x)`. -/
theorem liouvilleSummatory_omega_neg_sqrt :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x : ℝ in atTop, liouvilleSummatory x < -(c * Real.sqrt x) := by
  have hz := riemannZeta_half_eq_re
  refine ⟨-((riemannZeta (1 / 2)).re)⁻¹ / 2, ?_, liouvilleSummatory_frequently_lt_neg ?_⟩
  · have : 0 < -((riemannZeta (1 / 2)).re)⁻¹ := by
      simp only [neg_pos, inv_lt_zero]; exact hz.2
    linarith
  · have : 0 < -((riemannZeta (1 / 2)).re)⁻¹ := by
      simp only [neg_pos, inv_lt_zero]; exact hz.2
    linarith

/-! ## Critical zeros under a one-sided bound -/

/-- **The local inequality at a zero.**  Near a zero `ρ = ½ + iγ` with `Z(z) = (z-ρ)^m G(z)`,
writing `A = ε - η/ζ(½)`: `|z-1||Z(2z)|/(|2z-1||z||G(z)|) ≤ r^{m-1}(A + dl + Cr)` at `z = ρ + r`,
for all small `r > 0`. -/
theorem eventually_liouville_local_le {η ε ε' K : ℝ} (hη : |η| = 1)
    (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) {m : ℕ} (hm : 1 ≤ m) {G : ℂ → ℂ}
    (hfac : ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = (z - ρ) ^ m • G z)
    (hGan : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0) {dl : ℝ} (hdl : 0 < dl) :
    ∃ C : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖ρ + r - 1‖ * ‖zetaResidueUnit (2 * (ρ + r))‖ /
        (‖2 * (ρ + r) - 1‖ * ‖ρ + r‖ * ‖G (ρ + r)‖)
        ≤ r ^ (m - 1) * (ε - η * ((riemannZeta (1 / 2)).re)⁻¹ + dl + r * C) := by
  set A : ℝ := ε - η * ((riemannZeta (1 / 2)).re)⁻¹ with hA
  set γ : ℝ := |ρ.im| with hγ
  have hγ0 : 0 < γ := abs_pos.mpr hρim
  have hlim := tendsto_mul_laplaceReal_liouvilleMeasure hη hεε' hK hg
  have hlapb : ∀ᶠ r : ℝ in 𝓝[>] 0,
      r * laplaceReal (liouvilleMeasure η ε K) (1 / 2 + r) ≤ A + dl :=
    hlim.eventually (ge_mem_nhds (by rw [hA]; linarith))
  have htend : Tendsto (fun r : ℝ => ρ + r) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + r) (𝓝 (0 : ℝ)) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hfac' := htend.eventually hfac
  have hGne : ∀ᶠ r : ℝ in 𝓝[>] 0, G (ρ + r) ≠ 0 :=
    htend.eventually (hGan.continuousAt.eventually_ne hG0)
  refine ⟨(|ε| + K) / γ, ?_⟩
  filter_upwards [hfac', hGne, self_mem_nhdsWithin, hlapb] with r hr hGr hr0 hlr
  have hr0' : 0 < r := hr0
  set z : ℂ := ρ + r with hz
  have hzre : z.re = 1 / 2 + r := by simp [hz, hρre]
  have hzim : z.im = ρ.im := by simp [hz]
  have hzre' : 1 / 2 < z.re := by rw [hzre]; linarith
  have hz0 : z ≠ 0 := by intro h; rw [h] at hzre; simp at hzre; linarith
  have hid := liouville_continuation_identity hη hεε' hK hg hzre'
  set H : ℂ := ε / (z - 1 / 2) + K / z - complexLaplace (liouvilleMeasure η ε K) z with hHdef
  rw [hr] at hid
  have hzr : z - ρ = (r : ℂ) := by rw [hz]; ring
  rw [hzr] at hid
  have hnormid : ‖H‖ * (‖2 * z - 1‖ * ‖z‖ * (r ^ m * ‖G z‖)) =
      ‖z - 1‖ * ‖zetaResidueUnit (2 * z)‖ := by
    have := congrArg norm hid
    rw [norm_mul, norm_mul, norm_mul, smul_eq_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0', norm_mul, Complex.norm_real, Real.norm_eq_abs, hη,
      one_mul, norm_mul] at this
    rw [← this]
  have hGz : 0 < ‖G z‖ := norm_pos_iff.mpr hGr
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h2z : 0 < ‖2 * z - 1‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have := congrArg Complex.re h; simp at this; rw [hzre] at this; linarith
  have hE : ‖z - 1‖ * ‖zetaResidueUnit (2 * z)‖ / (‖2 * z - 1‖ * ‖z‖ * ‖G z‖) = r ^ m * ‖H‖ := by
    rw [← hnormid]; field_simp
  have hγle : γ ≤ ‖z - 1 / 2‖ := by
    have := Complex.abs_im_le_norm (z - 1 / 2)
    rw [Complex.sub_im, hzim] at this
    simpa using this
  have hγle' : γ ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rw [hzim] at this
    exact this
  have hCL : ‖complexLaplace (liouvilleMeasure η ε K) z‖
      ≤ laplaceReal (liouvilleMeasure η ε K) (1 / 2 + r) := by
    have := norm_complexLaplace_le (liouvilleMeasure η ε K) z
    rw [hzre] at this
    exact this
  have h1 : ‖(ε : ℂ) / (z - 1 / 2)‖ ≤ |ε| / γ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (abs_nonneg ε) hγ0 hγle
  have h2 : ‖(K : ℂ) / z‖ ≤ K / γ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
    exact div_le_div_of_nonneg_left hK hγ0 hγle'
  have hHle : ‖H‖ ≤ |ε| / γ + K / γ + laplaceReal (liouvilleMeasure η ε K) (1 / 2 + r) := by
    have hn1 := norm_sub_le ((ε : ℂ) / (z - 1 / 2) + K / z)
      (complexLaplace (liouvilleMeasure η ε K) z)
    have hn2 := norm_add_le ((ε : ℂ) / (z - 1 / 2)) ((K : ℂ) / z)
    rw [hHdef]
    linarith
  have hrH : r * ‖H‖ ≤ A + dl + r * ((|ε| + K) / γ) := by
    have := mul_le_mul_of_nonneg_left hHle hr0'.le
    have e : r * (|ε| / γ + K / γ) = r * ((|ε| + K) / γ) := by ring
    nlinarith
  rw [hE]
  have hpow : r ^ m = r ^ (m - 1) * r := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow, mul_assoc]
  exact mul_le_mul_of_nonneg_left hrH (pow_nonneg hr0'.le _)

/-- **A one-sided bound forces simple critical zeros with a residue bound.**  If
`ηL(e^t) ≤ ε'e^{t/2} + K` and `Z(z) = (z-ρ)^m G(z)` near `ρ = ½ + iγ`, then `m = 1` and
`|ρ-1||Z(2ρ)|/(|2ρ-1||ρ||G(ρ)|) ≤ ε' - η/ζ(½)`. -/
theorem liouville_zero_simple_of_oneSided {η ε' K : ℝ} (hη : |η| = 1)
    (hK : 0 ≤ K)
    (hg : ∀ t, 0 < t → η * liouvilleSummatory (Real.exp t) ≤ ε' * Real.exp (t / 2) + K)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) (hρ0 : zetaResidueUnit ρ = 0) {m : ℕ}
    {G : ℂ → ℂ} (hGan : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0)
    (hfac : ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = (z - ρ) ^ m • G z) :
    m = 1 ∧ ‖ρ - 1‖ * ‖zetaResidueUnit (2 * ρ)‖ / (‖2 * ρ - 1‖ * ‖ρ‖ * ‖G ρ‖)
      ≤ ε' - η * ((riemannZeta (1 / 2)).re)⁻¹ := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have := hfac.self_of_nhds
      rw [h, pow_zero, one_smul, hρ0] at this
      exact hG0 this.symm
    · exact h
  have hρ0' : ρ ≠ 0 := by intro h; rw [h, Complex.zero_re] at hρre; norm_num at hρre
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρre; norm_num at hρre
  have h2ρ : 2 * ρ - 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hρim him
  have hZ2 : zetaResidueUnit (2 * ρ) ≠ 0 := by
    have hre : (2 * ρ).re = 1 := by simp [hρre]
    have h21 : 2 * ρ ≠ 1 := fun h => h2ρ (by rw [h]; ring)
    rw [zetaResidueUnit, Function.update_of_ne h21]
    exact mul_ne_zero (sub_ne_zero.mpr h21) (riemannZeta_ne_zero_of_one_le_re hre.ge)
  set F₀ : ℝ := ‖ρ - 1‖ * ‖zetaResidueUnit (2 * ρ)‖ / (‖2 * ρ - 1‖ * ‖ρ‖ * ‖G ρ‖) with hF₀
  have hF₀pos : 0 < F₀ := by
    rw [hF₀]
    exact div_pos (mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hρ1)) (norm_pos_iff.mpr hZ2))
      (mul_pos (mul_pos (norm_pos_iff.mpr h2ρ) (norm_pos_iff.mpr hρ0'))
        (norm_pos_iff.mpr hG0))
  have htend : Tendsto (fun r : ℝ => ρ + r) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + r) (𝓝 (0 : ℝ)) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hFt : Tendsto (fun r : ℝ => ‖ρ + r - 1‖ * ‖zetaResidueUnit (2 * (ρ + r))‖ /
      (‖2 * (ρ + r) - 1‖ * ‖ρ + r‖ * ‖G (ρ + r)‖)) (𝓝[>] (0 : ℝ)) (𝓝 F₀) := by
    have hZc : ContinuousAt (fun z : ℂ => zetaResidueUnit (2 * z)) ρ :=
      ((analyticAt_zetaResidueUnit _).comp (analyticAt_const.mul analyticAt_id)).continuousAt
    have h1 : Tendsto (fun r : ℝ => ‖ρ + r - 1‖ * ‖zetaResidueUnit (2 * (ρ + r))‖)
        (𝓝[>] (0 : ℝ)) (𝓝 (‖ρ - 1‖ * ‖zetaResidueUnit (2 * ρ)‖)) :=
      (htend.sub_const 1).norm.mul (hZc.tendsto.comp htend).norm
    have h2 : Tendsto (fun r : ℝ => ‖2 * (ρ + r) - 1‖ * ‖ρ + r‖ * ‖G (ρ + r)‖) (𝓝[>] (0 : ℝ))
        (𝓝 (‖2 * ρ - 1‖ * ‖ρ‖ * ‖G ρ‖)) :=
      (((htend.const_mul 2).sub_const 1).norm.mul htend.norm).mul
        ((hGan.continuousAt.tendsto.comp htend).norm)
    exact h1.div h2 (mul_pos (mul_pos (norm_pos_iff.mpr h2ρ) (norm_pos_iff.mpr hρ0'))
      (norm_pos_iff.mpr hG0)).ne'
  set κ' : ℝ := ((riemannZeta (1 / 2)).re)⁻¹ with hκ'
  have hlocal : ∀ ε : ℝ, ε' < ε → ∀ dl : ℝ, 0 < dl → (m = 1 ∧ F₀ ≤ ε - η * κ' + dl) := by
    intro ε hεε' dl hdl
    obtain ⟨C, hC⟩ := eventually_liouville_local_le hη hεε' hK hg hρre hρim hm hfac hGan
      hG0 hdl
    rcases Nat.lt_or_ge 1 m with hm2 | hm1
    · exfalso
      have hR : Tendsto (fun r : ℝ => r ^ (m - 1) * (ε - η * κ' + dl + r * C)) (𝓝[>] (0 : ℝ))
          (𝓝 0) := by
        have h0 : Tendsto (fun r : ℝ => r ^ (m - 1) * (ε - η * κ' + dl + r * C)) (𝓝 (0 : ℝ))
            (𝓝 ((0 : ℝ) ^ (m - 1) * (ε - η * κ' + dl + 0 * C))) :=
          ((continuous_pow _).mul
            (continuous_const.add (continuous_id.mul continuous_const))).tendsto 0
        rw [zero_pow (by omega), zero_mul] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      have := le_of_tendsto_of_tendsto hFt hR hC
      linarith
    · have hm1' : m = 1 := le_antisymm hm1 hm
      refine ⟨hm1', ?_⟩
      have hR : Tendsto (fun r : ℝ => r ^ (m - 1) * (ε - η * κ' + dl + r * C)) (𝓝[>] (0 : ℝ))
          (𝓝 (ε - η * κ' + dl)) := by
        have h0 : Tendsto (fun r : ℝ => r ^ (m - 1) * (ε - η * κ' + dl + r * C)) (𝓝 (0 : ℝ))
            (𝓝 ((0 : ℝ) ^ (m - 1) * (ε - η * κ' + dl + 0 * C))) :=
          ((continuous_pow _).mul
            (continuous_const.add (continuous_id.mul continuous_const))).tendsto 0
        rw [hm1', Nat.sub_self, pow_zero, one_mul, zero_mul, add_zero] at h0
        rw [hm1']
        exact h0.mono_left nhdsWithin_le_nhds
      exact le_of_tendsto_of_tendsto hFt hR hC
  refine ⟨(hlocal (ε' + 1) (by linarith) 1 one_pos).1, ?_⟩
  refine le_of_forall_pos_lt_add fun dl hdl => ?_
  have := (hlocal (ε' + dl / 3) (by linarith) (dl / 3) (by positivity)).2
  linarith

/-- **A one-sided square-root bound for `L` makes every zero on the critical line simple.** -/
theorem deriv_zetaResidueUnit_ne_zero_of_liouville_oneSided {η c : ℝ} (hη : |η| = 1)
    (h : ∀ᶠ x : ℝ in atTop, η * liouvilleSummatory x ≤ c * Real.sqrt x) {ρ : ℂ}
    (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) (hρ0 : zetaResidueUnit ρ = 0) :
    deriv zetaResidueUnit ρ ≠ 0 := by
  obtain ⟨K, hK, hg⟩ := exists_liouville_oneSided_of_eventually hη h
  have hnot : ¬ ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = 0 := by
    intro hzero
    have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => analyticAt_zetaResidueUnit z) isPreconnected_univ (mem_univ ρ) hzero
    have := hall (mem_univ (1 : ℂ))
    simp at this
  obtain ⟨m, G, hGan, hG0, hfac⟩ :=
    ((analyticAt_zetaResidueUnit ρ).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnot
  have hm := (liouville_zero_simple_of_oneSided hη hK hg hρre hρim hρ0 hGan hG0 hfac).1
  rw [hm] at hfac
  have hd : HasDerivAt (fun z => (z - ρ) ^ 1 • G z) (G ρ) ρ := by
    have h1 : HasDerivAt (fun z : ℂ => (z - ρ) ^ 1) 1 ρ := by
      simpa using (hasDerivAt_id ρ).sub_const ρ
    have h2 := h1.mul hGan.differentiableAt.hasDerivAt
    refine h2.congr_deriv ?_
    simp
  rw [(hd.congr_of_eventuallyEq hfac).deriv]
  exact hG0


/-! ## Oscillation around the bias -/

/-- **`L(x)` oscillates on both sides of its bias.**  `L(x) - √x/ζ(½) = Ω±(√x)`: there is `c > 0`
with `L(x) - √x/ζ(½) > c√x` and `< -c√x`, each for arbitrarily large `x`.  A one-sided bound
around the bias with constant `c` forces `F₀(ρ) ≤ c` at a simple critical zero `ρ` (Hardy's theorem
supplies one), where `F₀(ρ) = |ρ-1||Z(2ρ)|/(|2ρ-1||ρ||G(ρ)|) > 0`. -/
theorem liouvilleSummatory_sub_bias_omega_pm :
    ∃ c : ℝ, 0 < c ∧
      (∃ᶠ x : ℝ in atTop,
        c * Real.sqrt x < liouvilleSummatory x - Real.sqrt x / (riemannZeta (1 / 2)).re) ∧
      ∃ᶠ x : ℝ in atTop,
        liouvilleSummatory x - Real.sqrt x / (riemannZeta (1 / 2)).re < -(c * Real.sqrt x) := by
  obtain ⟨t, ht1, ht0⟩ := exists_Xi_zero_gt 1
  set ρ : ℂ := 1 / 2 + (t : ℂ) * I with hρdef
  have hxi : xi ρ = 0 := by
    rw [xi_eq_XiC_comp]
    have e : ((1 / 2 + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
      ring_nf
      simp [Complex.I_sq]
    rw [e, XiC_ofReal, ht0]
    simp
  have hρre : ρ.re = 1 / 2 := by simp [hρdef]
  have hρim : ρ.im ≠ 0 := by simp [hρdef]; linarith
  have hρ0 : zetaResidueUnit ρ = 0 :=
    zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero
      (riemannZeta_eq_zero_iff_xi_or_trivial.mpr (Or.inl hxi))
  have hnot : ¬ ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = 0 := by
    intro hzero
    have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => analyticAt_zetaResidueUnit z) isPreconnected_univ (mem_univ ρ) hzero
    have := hall (mem_univ (1 : ℂ))
    simp at this
  obtain ⟨m, G, hGan, hG0, hfac⟩ :=
    ((analyticAt_zetaResidueUnit ρ).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnot
  have hρ0' : ρ ≠ 0 := by intro h; rw [h, Complex.zero_re] at hρre; norm_num at hρre
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρre; norm_num at hρre
  have h2ρ : 2 * ρ - 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hρim him
  have hZ2 : zetaResidueUnit (2 * ρ) ≠ 0 := by
    have hre : (2 * ρ).re = 1 := by simp [hρre]
    have h21 : 2 * ρ ≠ 1 := fun h => h2ρ (by rw [h]; ring)
    rw [zetaResidueUnit, Function.update_of_ne h21]
    exact mul_ne_zero (sub_ne_zero.mpr h21) (riemannZeta_ne_zero_of_one_le_re hre.ge)
  set F₀ : ℝ := ‖ρ - 1‖ * ‖zetaResidueUnit (2 * ρ)‖ / (‖2 * ρ - 1‖ * ‖ρ‖ * ‖G ρ‖) with hF₀
  have hF₀pos : 0 < F₀ := by
    rw [hF₀]
    exact div_pos (mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hρ1)) (norm_pos_iff.mpr hZ2))
      (mul_pos (mul_pos (norm_pos_iff.mpr h2ρ) (norm_pos_iff.mpr hρ0'))
        (norm_pos_iff.mpr hG0))
  set z₀ : ℝ := (riemannZeta (1 / 2)).re with hz₀
  refine ⟨F₀ / 2, by positivity, ?_, ?_⟩
  · by_contra hno
    rw [Filter.not_frequently] at hno
    have h' : ∀ᶠ x : ℝ in atTop, (1 : ℝ) * liouvilleSummatory x ≤
        (F₀ / 2 + z₀⁻¹) * Real.sqrt x :=
      hno.mono fun x hx => by
        have := not_lt.mp hx
        have e : (F₀ / 2 + z₀⁻¹) * Real.sqrt x = F₀ / 2 * Real.sqrt x + Real.sqrt x / z₀ := by
          ring
        rw [e]
        linarith
    obtain ⟨K, hK, hg⟩ := exists_liouville_oneSided_of_eventually (by simp) h'
    have := (liouville_zero_simple_of_oneSided (by simp) hK hg hρre hρim hρ0 hGan hG0 hfac).2
    rw [← hF₀, ← hz₀] at this
    linarith
  · by_contra hno
    rw [Filter.not_frequently] at hno
    have h' : ∀ᶠ x : ℝ in atTop, (-1 : ℝ) * liouvilleSummatory x ≤
        (F₀ / 2 - z₀⁻¹) * Real.sqrt x :=
      hno.mono fun x hx => by
        have := not_lt.mp hx
        have e : (F₀ / 2 - z₀⁻¹) * Real.sqrt x = F₀ / 2 * Real.sqrt x - Real.sqrt x / z₀ := by
          ring
        rw [e]
        linarith
    obtain ⟨K, hK, hg⟩ := exists_liouville_oneSided_of_eventually (by simp) h'
    have := (liouville_zero_simple_of_oneSided (by simp) hK hg hρre hρim hρ0 hGan hG0 hfac).2
    rw [← hF₀, ← hz₀] at this
    linarith

end

end RHTower
