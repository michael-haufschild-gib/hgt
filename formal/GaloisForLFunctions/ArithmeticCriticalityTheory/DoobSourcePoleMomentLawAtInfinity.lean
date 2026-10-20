import GaloisForLFunctions.ArithmeticCriticalityTheory.PoleFreeWeilOperatorAndProfileInfinityFailure

/-!
# The Doob source at infinity is a pole moment of the profile

For a profile `M ∈ C¹` with `M(0) = 0` and `|M|, |M'| ≤ Ce^{−8|y|}`, and its gauge `ω = M/Φ`:

* **Folded law** (`tendsto_foldedSource_div`). With no sign condition on `M`,

      (𝓛_N ω − Φ cosh(x/2) ω)(x) / (Φ(x) e^{x/2})  →  −2 ∫_0^∞ M(r) cosh(r/2) dr.

* **Two-sided law** (`tendsto_twoSidedSource_div`). For odd `M`,

      (𝓛_D ω − Φ cosh(x/2) ω)(x) / (Φ(x) e^{x/2})  →  2 ∫_0^∞ M(r) sinh(r/2) dr.

By the exact source `−Φ 𝒲` (`PoleFreeWeilOperatorAndProfileInfinityFailure`) both are limits of
`e^{−x/2} 𝒲`. The archimedean term of `𝒲` is bounded (`abs_integral_profileArchTerm_le`) and the
forward prime terms decay, so at infinity only the prime terms reading back into the profile
survive. They split at `log n = x` into the reflected mass `Σ_{log n > x}`, asymptotic to
`e^{x/2} ∫_0^∞ e^{r/2} M` (`tendsto_exp_neg_half_mul_reflectedPrimeMass`), and the **direct mass**
`Σ_{log n ≤ x} Λ(n) n^{−1/2} M(x − log n)`, asymptotic to `e^{x/2} ∫_0^∞ e^{−r/2} M`
(`tendsto_exp_neg_half_mul_directPrimeMass`; Abel summation against `ψ` on `[1, e^x]`, the
substitution `t = e^{x−s}`, and the prime number theorem with domination by `ψ(y) ≤ Ky`). The
two-sided generator reads the reflected points with the sign of `M` on the negative half line, the
folded one with a plus sign: the moments `e^{∓r/2}` combine into `sinh` and `cosh`.

So at infinity the arithmetic generator sees a profile only through its moments at the pole
`e^{±r/2}`: the two-sided source through the odd pole moment, the folded source through the
half-line cosh moment. The sign of `∫_0^∞ M cosh(r/2)` decides the folded supersolution inequality
on a half line, for every profile (`exists_infinity_window_foldedGenerator_lt_potential_of_coshMoment_pos`,
`exists_infinity_window_potential_lt_foldedGenerator_of_coshMoment_neg`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The weight `H(s) = e^{s/2} M(s)` -/

/-- `H(s) = e^s G(s) = e^{s/2} M(s)`. -/
def directWeight (M : ℝ → ℝ) (s : ℝ) : ℝ := Real.exp s * halfWeight M s

/-- `H'(s) = e^s (G'(s) + G(s))`. -/
def directWeightDeriv (M : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp s * (halfWeightDeriv M s + halfWeight M s)

theorem hasDerivAt_directWeight {M : ℝ → ℝ} (hM : ContDiff ℝ 1 M) (s : ℝ) :
    HasDerivAt (directWeight M) (directWeightDeriv M s) s := by
  refine ((Real.hasDerivAt_exp s).mul (hasDerivAt_halfWeight hM s)).congr_deriv ?_
  unfold directWeightDeriv
  ring

theorem continuous_directWeightDeriv {M : ℝ → ℝ} (hM : ContDiff ℝ 1 M) :
    Continuous (directWeightDeriv M) :=
  Real.continuous_exp.mul ((continuous_halfWeightDeriv hM).add (continuous_halfWeight hM))

theorem hasDerivAt_directWeight_sub_log {M : ℝ → ℝ} (hM : ContDiff ℝ 1 M) (x : ℝ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun t => directWeight M (x - Real.log t))
      (-(directWeightDeriv M (x - Real.log t) / t)) t := by
  refine ((hasDerivAt_directWeight hM (x - Real.log t)).comp t
    ((Real.hasDerivAt_log ht.ne').const_sub x)).congr_deriv ?_
  rw [mul_neg, div_eq_mul_inv]

/-! ### The direct prime mass -/

/-- The direct prime mass `Σ_{log n ≤ x} Λ(n) n^{−1/2} M(x − log n)`. -/
def directPrimeMass (M : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * (if Real.log n ≤ x then M (x - Real.log n) else 0)

/-- **Abel summation on `[1, e^x]`.** For `x ≥ 0`,
`Σ_{1 < k ≤ e^x} H(x − log k) Λ(k) = ∫_1^{e^x} H'(x − log t) ψ(t) dt/t`. -/
theorem sum_directWeight_vonMangoldt_eq {M : ℝ → ℝ} (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0) {x : ℝ}
    (hx : 0 ≤ x) :
    ∑ k ∈ Finset.Ioc 1 ⌊Real.exp x⌋₊, directWeight M (x - Real.log k) *
        (ArithmeticFunction.vonMangoldt k : ℝ) =
      ∫ t in Ioc 1 (Real.exp x), directWeightDeriv M (x - Real.log t) / t * psiSum t := by
  have hpos : ∀ t ∈ Icc (1 : ℝ) (Real.exp x), 0 < t := fun t ht => lt_of_lt_of_le one_pos ht.1
  have hcont : ContinuousOn (fun t => -(directWeightDeriv M (x - Real.log t) / t))
      (Icc 1 (Real.exp x)) :=
    (((continuous_directWeightDeriv hM).comp_continuousOn
      (continuousOn_const.sub (Real.continuousOn_log.mono fun t ht => (hpos t ht).ne'))).div
      continuousOn_id fun t ht => (hpos t ht).ne').neg
  have hint : IntegrableOn (deriv fun t => directWeight M (x - Real.log t)) (Icc 1 (Real.exp x)) := by
    refine hcont.integrableOn_Icc.congr_fun (fun t ht => ?_) measurableSet_Icc
    exact ((hasDerivAt_directWeight_sub_log hM x (hpos t ht)).deriv).symm
  have h := sum_mul_eq_sub_sub_integral_mul (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
    (f := fun t => directWeight M (x - Real.log t)) zero_le_one (Real.one_le_exp hx)
    (fun t ht => (hasDerivAt_directWeight_sub_log hM x (hpos t ht)).differentiableAt) hint
  rw [Nat.floor_one] at h
  have hH0 : directWeight M (x - Real.log (Real.exp x)) = 0 := by
    rw [Real.log_exp, sub_self, directWeight, halfWeight, hM0, mul_zero, mul_zero]
  have hψ1 : ∑ k ∈ Finset.Icc 0 1, (ArithmeticFunction.vonMangoldt k : ℝ) = 0 := by
    rw [show Finset.Icc 0 1 = ({0, 1} : Finset ℕ) by decide]
    simp
  have hI : (∫ t in Ioc 1 (Real.exp x), deriv (fun t => directWeight M (x - Real.log t)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ)) =
      -∫ t in Ioc 1 (Real.exp x), directWeightDeriv M (x - Real.log t) / t * psiSum t := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hasDerivAt_directWeight_sub_log hM x (lt_trans one_pos ht.1)).deriv]
    unfold psiSum
    ring
  rw [h, hH0, zero_mul, hψ1, mul_zero, sub_zero, zero_sub, hI, neg_neg]

/-- The substitution `t = e^{x−s}`. -/
theorem integral_Ioc_one_exp_directWeightDeriv_eq (M : ℝ → ℝ) (x : ℝ) :
    (∫ t in Ioc 1 (Real.exp x), directWeightDeriv M (x - Real.log t) / t * psiSum t) =
      ∫ s in Ioo 0 x, directWeightDeriv M s * psiSum (Real.exp (x - s)) := by
  have himage : (fun s => Real.exp (x - s)) '' Ioo 0 x = Ioo 1 (Real.exp x) := by
    rw [show (fun s => Real.exp (x - s)) = Real.exp ∘ fun s => x - s from rfl, Set.image_comp,
      Set.image_const_sub_Ioo, sub_self, sub_zero, Real.image_exp_Ioo, Real.exp_zero]
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioo (0 : ℝ) x)
    (f := fun s => Real.exp (x - s)) (f' := fun s => -Real.exp (x - s)) measurableSet_Ioo
    (fun s _ => by
      have := ((hasDerivAt_id s).const_sub x).exp
      simpa using this.hasDerivWithinAt)
    ((Real.exp_injective.comp sub_right_injective).injOn)
    (fun t => directWeightDeriv M (x - Real.log t) / t * psiSum t)
  rw [himage] at h
  rw [integral_Ioc_eq_integral_Ioo, h]
  refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
  simp only [smul_eq_mul, Real.log_exp, abs_neg, abs_of_pos (Real.exp_pos _)]
  rw [show x - (x - s) = s by ring]
  field_simp

/-- The direct prime mass as a finite sum of the weight `H`. -/
theorem exp_neg_half_mul_directPrimeMass_eq (M : ℝ → ℝ) (x : ℝ) :
    Real.exp (-x / 2) * directPrimeMass M x =
      Real.exp (-x) * ∑ k ∈ Finset.Ioc 1 ⌊Real.exp x⌋₊, directWeight M (x - Real.log k) *
        (ArithmeticFunction.vonMangoldt k : ℝ) := by
  unfold directPrimeMass
  rw [tsum_eq_sum (s := Finset.Ioc 1 ⌊Real.exp x⌋₊) fun n hn => ?_, Finset.mul_sum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkx : Real.log k ≤ x := by
      have := (Nat.le_floor_iff (Real.exp_pos x).le).mp hk2
      rw [← Real.log_exp x]
      exact Real.log_le_log hk0 this
    rw [if_pos hkx]
    unfold vonMangoldtAtom directWeight halfWeight
    rw [if_pos (by omega : 2 ≤ k)]
    have hsq : Real.sqrt k = Real.exp (Real.log k / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hk0]
      ring_nf
    have e1 : Real.exp (-x) * Real.exp (x - Real.log k) * Real.exp (-(x - Real.log k) / 2) =
        Real.exp (-x / 2) * (Real.exp (Real.log k / 2))⁻¹ := by
      rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    rw [hsq]
    linear_combination (-((ArithmeticFunction.vonMangoldt k : ℝ) * M (x - Real.log k))) * e1
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · unfold vonMangoldtAtom
      rw [if_neg (by omega), zero_mul]
    · have hn : ⌊Real.exp x⌋₊ < n := by
        by_contra hle
        exact hn (Finset.mem_Ioc.mpr ⟨by omega, not_lt.mp hle⟩)
      have hlt : x < Real.log n := by
        have := (Nat.floor_lt (Real.exp_pos x).le).mp hn
        rw [← Real.log_exp x]
        exact Real.log_lt_log (Real.exp_pos x) this
      rw [if_neg (not_le.mpr hlt), mul_zero]

/-- `ψ(y) ≤ K y` on `[1, ∞)`. -/
theorem exists_psiSum_le_mul : ∃ K : ℝ, 0 ≤ K ∧ ∀ y, 1 ≤ y → psiSum y ≤ K * y := by
  obtain ⟨Y, hY⟩ : ∃ Y, ∀ y ≥ Y, psiSum y / y ≤ 2 :=
    eventually_atTop.mp (tendsto_psiSum_div.eventually (ge_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  set Y₁ := max Y 1
  refine ⟨max 2 ((Y₁ + 1) ^ 2), by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  rcases le_or_gt Y₁ y with hYy | hYy
  · have h := hY y (le_trans (le_max_left _ _) hYy)
    rw [div_le_iff₀ hy0] at h
    nlinarith [le_max_left 2 ((Y₁ + 1) ^ 2)]
  · have h := psiSum_le hy0.le
    have h1 : (y + 1) ^ 2 ≤ (Y₁ + 1) ^ 2 := by nlinarith
    have h2 : (Y₁ + 1) ^ 2 ≤ (Y₁ + 1) ^ 2 * y := le_mul_of_one_le_right (by positivity) hy
    nlinarith [le_max_right 2 ((Y₁ + 1) ^ 2)]

/-- **The direct prime mass at infinity.** For `M ∈ C¹` with `M(0) = 0` and
`|M|, |M'| ≤ C e^{−2r}` on `[0, ∞)`,
`e^{−x/2} Σ_{log n ≤ x} Λ(n) n^{−1/2} M(x − log n) → ∫_0^∞ e^{−r/2} M(r) dr`. -/
theorem tendsto_exp_neg_half_mul_directPrimeMass {M : ℝ → ℝ} (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hdec : ∀ r, 0 ≤ r → |M r| ≤ C * Real.exp (-(2 * r)))
    (hdec' : ∀ r, 0 ≤ r → |deriv M r| ≤ C * Real.exp (-(2 * r))) :
    Tendsto (fun x => Real.exp (-x / 2) * directPrimeMass M x) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), Real.exp (-s / 2) * M s)) := by
  set g : ℝ → ℝ := fun s => halfWeightDeriv M s + halfWeight M s with hg
  set F : ℝ → ℝ → ℝ := fun x => Set.indicator (Iio x)
    (fun s => g s * (Real.exp (-(x - s)) * psiSum (Real.exp (x - s)))) with hF
  have hrep : ∀ x, 0 ≤ x → Real.exp (-x / 2) * directPrimeMass M x = ∫ s in Ioi 0, F x s := by
    intro x hx
    rw [exp_neg_half_mul_directPrimeMass_eq M x, sum_directWeight_vonMangoldt_eq hM hM0 hx,
      integral_Ioc_one_exp_directWeightDeriv_eq, ← integral_const_mul, hF,
      setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
    refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
    unfold directWeightDeriv
    have e : Real.exp (-x) * Real.exp s = Real.exp (-(x - s)) := by
      rw [← Real.exp_add]
      ring_nf
    simp only [hg]
    linear_combination ((halfWeightDeriv M s + halfWeight M s) * psiSum (Real.exp (x - s))) * e
  obtain ⟨K, hK0, hK⟩ := exists_psiSum_le_mul
  have hgc : Continuous g := (continuous_halfWeightDeriv hM).add (continuous_halfWeight hM)
  have hDCT : Tendsto (fun x => ∫ s in Ioi 0, F x s) atTop (𝓝 (∫ s in Ioi (0 : ℝ), g s)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => 3 * C * K * Real.exp (-(3 / 2) * s)) ?_ ?_
      (integrableOn_exp_neg_three_halves.const_mul _) ?_
    · refine Eventually.of_forall fun x => ?_
      have hm : Measurable fun s => g s * (Real.exp (-(x - s)) * psiSum (Real.exp (x - s))) :=
        hgc.measurable.mul ((Real.measurable_exp.comp (measurable_const.sub measurable_id).neg).mul
          (measurable_psiSum.comp (Real.measurable_exp.comp (measurable_const.sub measurable_id))))
      exact (hm.indicator measurableSet_Iio).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      have hs0 : 0 ≤ s := le_of_lt hs
      have hb : |g s| ≤ 3 * C * Real.exp (-(5 / 2 * s)) := by
        have h1 := abs_halfWeightDeriv_le hC0 hdec hdec' hs0
        have h2 := abs_halfWeight_le hdec hs0
        have := abs_add_le (halfWeightDeriv M s) (halfWeight M s)
        simp only [hg]
        linarith
      have hexp : Real.exp (-(5 / 2 * s)) ≤ Real.exp (-(3 / 2) * s) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hbound0 : 0 ≤ 3 * C * K * Real.exp (-(3 / 2) * s) := by positivity
      simp only [hF, Set.indicator_apply, mem_Iio]
      split_ifs with hsx
      · have hy : 1 ≤ Real.exp (x - s) := Real.one_le_exp (by linarith)
        have hψ := hK _ hy
        have hψ0 := psiSum_nonneg (Real.exp (x - s))
        have hfac : Real.exp (-(x - s)) * psiSum (Real.exp (x - s)) ≤ K := by
          have : Real.exp (-(x - s)) * Real.exp (x - s) = 1 := by
            rw [← Real.exp_add]; simp
          nlinarith [Real.exp_pos (-(x - s))]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hψ0)]
        calc |g s| * (Real.exp (-(x - s)) * psiSum (Real.exp (x - s))) ≤
            (3 * C * Real.exp (-(5 / 2 * s))) * K :=
              mul_le_mul hb hfac (mul_nonneg (Real.exp_pos _).le hψ0) (by positivity)
          _ ≤ 3 * C * K * Real.exp (-(3 / 2) * s) := by
              have := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 3 * C * K)
              linarith
      · rw [norm_zero]
        exact hbound0
    · refine Eventually.of_forall fun s => ?_
      have h1 : Tendsto (fun x => psiSum (Real.exp (x - s)) / Real.exp (x - s)) atTop (𝓝 1) :=
        tendsto_psiSum_div.comp (Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ _
          tendsto_id))
      have h2 : Tendsto (fun x => g s * (psiSum (Real.exp (x - s)) / Real.exp (x - s))) atTop
          (𝓝 (g s * 1)) := h1.const_mul _
      rw [mul_one] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop s] with x hx
      simp only [hF, Set.indicator_apply, mem_Iio, if_pos hx]
      rw [Real.exp_neg, div_eq_mul_inv]
      ring
  -- the value
  have hG0 : Tendsto (halfWeight M) atTop (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => C * Real.exp (-(5 / 2 * r))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 5 / 2))).const_mul C
      simpa [Function.comp_def, neg_mul] using this
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop 0] with r hr
    rw [Real.norm_eq_abs]
    exact abs_halfWeight_le hdec hr
  have hGi : IntegrableOn (halfWeight M) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 5 / 2)).const_mul C).mono'
      (continuous_halfWeight hM).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
    rw [Real.norm_eq_abs, show -(5 / 2) * r = -(5 / 2 * r) by ring]
    exact abs_halfWeight_le hdec (le_of_lt hr)
  have hG'i : IntegrableOn (halfWeightDeriv M) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 5 / 2)).const_mul (2 * C)).mono'
      (continuous_halfWeightDeriv hM).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
    rw [Real.norm_eq_abs, show -(5 / 2) * r = -(5 / 2 * r) by ring]
    exact abs_halfWeightDeriv_le hC0 hdec hdec' (le_of_lt hr)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hasDerivAt_halfWeight hM 0).continuousAt.continuousWithinAt)
    (fun r _ => hasDerivAt_halfWeight hM r) hG'i hG0
  have hval : (∫ s in Ioi (0 : ℝ), g s) = ∫ s in Ioi (0 : ℝ), Real.exp (-s / 2) * M s := by
    simp only [hg]
    rw [integral_add hG'i hGi, hFTC]
    simp [halfWeight, hM0]
  rw [hval] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  exact (hrep x hx).symm

/-! ### The prime sum of a profile at infinity -/

section Profile

variable {M : ℝ → ℝ} {C : ℝ} (hM : ContDiff ℝ 1 M)
  (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
  (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|)))

include hdec in
theorem abs_le_exp_neg_two_of_decay {r : ℝ} (hr : 0 ≤ r) : |M r| ≤ C * Real.exp (-(2 * r)) :=
  (hdec r).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by rw [abs_of_nonneg hr]; linarith))
    (nonneg_of_abs_le_mul_exp hdec))

theorem summable_atom_mul_of_decay (x : ℝ) (G : ℕ → ℝ)
    (hG : ∀ n, |G n| ≤ C * Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) :
    Summable fun n : ℕ => vonMangoldtAtom n * G n :=
  Summable.of_norm_bounded
    (summable_atom_mul_exp_neg_eight_log.mul_left (C * Real.exp (8 * |x|))) fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
      calc vonMangoldtAtom n * |G n| ≤
          vonMangoldtAtom n * (C * Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) :=
            mul_le_mul_of_nonneg_left (hG n) (vonMangoldtAtom_nonneg n)
        _ = _ := by ring

include hdec in
/-- A profile value at distance at least `log n − |x|` from the origin is `O(e^{8|x|} n^{−8})`. -/
theorem abs_le_of_decay_of_le {x y : ℝ} {n : ℕ} (hy : Real.log n - |x| ≤ |y|) :
    |M y| ≤ C * Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)) := by
  refine (hdec y).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
    (nonneg_of_abs_le_mul_exp hdec)

include hdec in
/-- The forward prime terms vanish after normalisation: `e^{−x/2} Σ Λ(n)n^{−1/2} M(x + log n) → 0`. -/
theorem tendsto_exp_neg_half_mul_forwardPrimeMass :
    Tendsto (fun x => Real.exp (-x / 2) * ∑' n : ℕ, vonMangoldtAtom n * M (x + Real.log n))
      atTop (𝓝 0) := by
  have hC0 := nonneg_of_abs_le_mul_exp hdec
  set S := ∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(8 * Real.log n))
  have h0 : Tendsto (fun x : ℝ => C * S * Real.exp (-(8 * x))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 8))).const_mul (C * S)
    simpa [Function.comp_def, neg_mul] using this
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop 0] with x hx
  have hterm : ∀ n : ℕ, ‖vonMangoldtAtom n * M (x + Real.log n)‖ ≤
      C * Real.exp (-(8 * x)) * (vonMangoldtAtom n * Real.exp (-(8 * Real.log n))) := fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
    have hl := Real.log_natCast_nonneg n
    have h := hdec (x + Real.log n)
    rw [abs_of_nonneg (by linarith : 0 ≤ x + Real.log n), mul_add, neg_add, Real.exp_add] at h
    calc vonMangoldtAtom n * |M (x + Real.log n)| ≤
        vonMangoldtAtom n * (C * (Real.exp (-(8 * x)) * Real.exp (-(8 * Real.log n)))) :=
          mul_le_mul_of_nonneg_left h (vonMangoldtAtom_nonneg n)
      _ = _ := by ring
  have hS := (summable_atom_mul_exp_neg_eight_log.hasSum.mul_left (C * Real.exp (-(8 * x))))
  have hbound := tsum_of_norm_bounded hS hterm
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  calc Real.exp (-x / 2) * ‖∑' n : ℕ, vonMangoldtAtom n * M (x + Real.log n)‖ ≤
      1 * (C * Real.exp (-(8 * x)) * S) :=
        mul_le_mul he hbound (norm_nonneg _) zero_le_one
    _ = C * S * Real.exp (-(8 * x)) := by ring

include hM hdec' in
/-- `M` is `C`-Lipschitz when `|M'| ≤ C e^{−8|y|}`. -/
theorem abs_sub_le_of_decay (a b : ℝ) : |M a - M b| ≤ C * |a - b| := by
  have hC0 := nonneg_of_abs_le_mul_exp hdec'
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := M) (s := univ) (C := C)
    (fun y _ => hM.differentiable one_ne_zero y) (fun y _ => by
      rw [Real.norm_eq_abs]
      exact (hdec' y).trans (mul_le_of_le_one_right hC0
        (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y]))))
    convex_univ (mem_univ b) (mem_univ a)
  simpa only [Real.norm_eq_abs] using h

/-- The archimedean integral of a `K`-Lipschitz profile bounded by `C` is at most `(2K + 3C) J`. -/
theorem abs_integral_profileArchTerm_le {f : ℝ → ℝ} {K : ℝ}
    (hf : ∀ a b, |f a - f b| ≤ K * |a - b|) (hfb : ∀ y, |f y| ≤ C) (x : ℝ) :
    |∫ u in Ioi (0 : ℝ), profileArchTerm f x u| ≤
      (2 * K + 3 * C) * ∫ u in Ioi (0 : ℝ), archLevyDensity u * u := by
  calc |∫ u in Ioi (0 : ℝ), profileArchTerm f x u|
      = ‖∫ u in Ioi (0 : ℝ), profileArchTerm f x u‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ u in Ioi (0 : ℝ), (2 * K + 3 * C) * (archLevyDensity u * u) :=
        norm_integral_le_of_norm_le (integrableOn_archLevyDensity_mul_id.const_mul _)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
            rw [Real.norm_eq_abs]
            refine (abs_profileArchTerm_le hf x hu).trans (mul_le_mul_of_nonneg_right ?_
              (mul_nonneg (archLevyDensity_pos hu).le (le_of_lt hu)))
            linarith [hfb x])
    _ = _ := integral_const_mul _ _

include hdec in
/-- The forward, reflected and direct prime sums of a decaying profile converge. -/
theorem summable_primeSplit {x : ℝ} (hx : 0 ≤ x) :
    (Summable fun n : ℕ => vonMangoldtAtom n * M (x + Real.log n)) ∧
    (Summable fun n : ℕ =>
      vonMangoldtAtom n * (if x < Real.log n then M (Real.log n - x) else 0)) ∧
    (Summable fun n : ℕ =>
      vonMangoldtAtom n * (if Real.log n ≤ x then M (x - Real.log n) else 0)) := by
  have hC0 := nonneg_of_abs_le_mul_exp hdec
  have hl : ∀ n : ℕ, Real.log n - |x| ≤ |x + Real.log n| := fun n => by
    have := Real.log_natCast_nonneg n
    rw [abs_of_nonneg hx, abs_of_nonneg (by linarith)]
    linarith
  have hl' : ∀ n : ℕ, Real.log n - |x| ≤ |Real.log n - x| := fun n => by
    have := abs_sub_abs_le_abs_sub (Real.log n) x
    rwa [abs_of_nonneg (Real.log_natCast_nonneg n)] at this
  have hB0 : ∀ n : ℕ, 0 ≤ C * Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)) := fun n => by
    positivity
  have hFw : Summable fun n : ℕ => vonMangoldtAtom n * M (x + Real.log n) :=
    summable_atom_mul_of_decay x _ fun n => abs_le_of_decay_of_le hdec (hl n)
  have hRf : Summable fun n : ℕ =>
      vonMangoldtAtom n * (if x < Real.log n then M (Real.log n - x) else 0) :=
    summable_atom_mul_of_decay x _ fun n => by
      split_ifs
      · exact abs_le_of_decay_of_le hdec (hl' n)
      · rw [abs_zero]; exact hB0 n
  have hDr : Summable fun n : ℕ =>
      vonMangoldtAtom n * (if Real.log n ≤ x then M (x - Real.log n) else 0) :=
    summable_atom_mul_of_decay x _ fun n => by
      split_ifs
      · exact abs_le_of_decay_of_le hdec (by rw [abs_sub_comm]; exact hl' n)
      · rw [abs_zero]; exact hB0 n
  exact ⟨hFw, hRf, hDr⟩

end Profile

/-! ### The laws -/

theorem tendsto_exp_neg_half_atTop : Tendsto (fun x : ℝ => Real.exp (-x / 2)) atTop (𝓝 0) := by
  have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  simpa [Function.comp_def, neg_div] using this

/-- `e^{−x/2} f(x) → 0` for bounded `f`. -/
theorem tendsto_exp_neg_half_mul_of_abs_le {f : ℝ → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    Tendsto (fun x => Real.exp (-x / 2) * f x) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun x => ?_) (by simpa using tendsto_exp_neg_half_atTop.mul_const B)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hf x) (Real.exp_pos _).le

/-- The two pole moments combine into the half-line cosh and sinh moments. -/
theorem integral_exp_half_add_exp_neg_half {M : ℝ → ℝ} {C : ℝ} (hM : Continuous M)
    (hd2 : ∀ r, 0 ≤ r → |M r| ≤ C * Real.exp (-(2 * r))) :
    IntegrableOn (fun r => Real.exp (r / 2) * M r) (Ioi 0) ∧
      IntegrableOn (fun r => Real.exp (-r / 2) * M r) (Ioi 0) ∧
      (∫ r in Ioi (0 : ℝ), Real.exp (r / 2) * M r) + (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * M r) =
        2 * ∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2) ∧
      (∫ r in Ioi (0 : ℝ), Real.exp (r / 2) * M r) - (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * M r) =
        2 * ∫ r in Ioi (0 : ℝ), M r * Real.sinh (r / 2) := by
  have hp : IntegrableOn (fun r => Real.exp (r / 2) * M r) (Ioi 0) := integrableOn_exp_half_mul hd2 hM
  have hm : IntegrableOn (fun r => Real.exp (-r / 2) * M r) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 5 / 2)).const_mul C).mono'
      ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul hM).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
    rw [Real.norm_eq_abs, show -(5 / 2) * r = -(5 / 2 * r) by ring]
    exact abs_halfWeight_le hd2 (le_of_lt hr)
  refine ⟨hp, hm, ?_, ?_⟩
  · rw [← integral_add hp hm, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [Real.cosh_eq, neg_div]
    ring
  · rw [← integral_sub hp hm, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [Real.sinh_eq, neg_div]
    ring

/-- **The folded law.** For `M ∈ C¹` with `M(0) = 0` and `|M|, |M'| ≤ Ce^{−8|y|}`,
`(𝓛_N ω − Φ cosh(x/2) ω)(x)/(Φ(x)e^{x/2}) → −2 ∫_0^∞ M(r) cosh(r/2) dr` for `ω = M/Φ`. -/
theorem tendsto_foldedSource_div {M : ℝ → ℝ} {C : ℝ} (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0)
    (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) :
    Tendsto (fun x => (foldedGenerator (fun y => M y / riemannKernelReal y) x -
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) /
          (riemannKernelReal x * Real.exp (x / 2))) atTop
      (𝓝 (-(2 * ∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2)))) := by
  have hC0 := nonneg_of_abs_le_mul_exp hdec
  have hd2 : ∀ r, 0 ≤ r → |M r| ≤ C * Real.exp (-(2 * r)) := fun r hr =>
    abs_le_exp_neg_two_of_decay hdec hr
  have hd2' : ∀ r, 0 ≤ r → |deriv M r| ≤ C * Real.exp (-(2 * r)) := fun r hr =>
    abs_le_exp_neg_two_of_decay hdec' hr
  have hMb : ∀ y, |M y| ≤ C := fun y => (hdec y).trans
    (mul_le_of_le_one_right hC0 (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y])))
  -- the exact decomposition of `𝓦(M(|·|))(x)` for `x ≥ 0`
  have hsplit : ∀ x, 0 ≤ x → poleFreeWeilOperator (fun y => M (|y|)) x =
      (∑' n : ℕ, vonMangoldtAtom n * M (x + Real.log n)) +
        (∑' n : ℕ, vonMangoldtAtom n * (if x < Real.log n then M (Real.log n - x) else 0)) +
        directPrimeMass M x - (∫ u in Ioi (0 : ℝ), profileArchTerm (fun y => M (|y|)) x u) +
        2 * archConstantReal * M x := by
    intro x hx
    obtain ⟨hFw, hRf, hDr⟩ := summable_primeSplit hdec hx
    have hP : profilePrimeSum (fun y => M (|y|)) x =
        (∑' n : ℕ, vonMangoldtAtom n * M (x + Real.log n)) +
          (∑' n : ℕ, vonMangoldtAtom n * (if x < Real.log n then M (Real.log n - x) else 0)) +
          directPrimeMass M x := by
      unfold profilePrimeSum directPrimeMass
      rw [← hFw.tsum_add hRf, ← (hFw.add hRf).tsum_add hDr]
      refine tsum_congr fun n => ?_
      have hn := Real.log_natCast_nonneg n
      beta_reduce
      rw [abs_of_nonneg (by linarith : 0 ≤ x + Real.log n)]
      by_cases h : x < Real.log n
      · rw [if_pos h, if_neg (not_le.mpr h), abs_of_neg (by linarith : x - Real.log n < 0), neg_sub]
        ring
      · rw [if_neg h, if_pos (not_lt.mp h), abs_of_nonneg (by linarith : 0 ≤ x - Real.log n)]
        ring
    show profilePrimeSum (fun y => M (|y|)) x -
        (∫ u in Ioi (0 : ℝ), profileArchTerm (fun y => M (|y|)) x u) +
        2 * archConstantReal * M (|x|) = _
    rw [hP, abs_of_nonneg hx]
  -- the quotient is `−e^{−x/2} 𝓦(M(|·|))(x)`
  have hq : ∀ x, 0 ≤ x → (foldedGenerator (fun y => M y / riemannKernelReal y) x -
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) /
        (riemannKernelReal x * Real.exp (x / 2)) =
      -(Real.exp (-x / 2) * poleFreeWeilOperator (fun y => M (|y|)) x) := by
    intro x hx
    rw [foldedGenerator_profileGauge_sub_potential_of_decay (hM.differentiable one_ne_zero) hdec
      hdec' hx]
    have hΦ := (riemannKernelReal_pos x).ne'
    rw [show Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ by rw [← Real.exp_neg]; ring_nf]
    field_simp
  -- the limits of the pieces
  have hFwL := tendsto_exp_neg_half_mul_forwardPrimeMass hdec
  have hRfL := tendsto_exp_neg_half_mul_reflectedPrimeMass hM hM0 hC0 hd2 hd2'
  have hDrL := tendsto_exp_neg_half_mul_directPrimeMass hM hM0 hC0 hd2 hd2'
  have hAL := tendsto_exp_neg_half_mul_of_abs_le
    (f := fun x => ∫ u in Ioi (0 : ℝ), profileArchTerm (fun y => M (|y|)) x u)
    (B := (2 * C + 3 * C) * ∫ u in Ioi (0 : ℝ), archLevyDensity u * u) fun x =>
      abs_integral_profileArchTerm_le
        (abs_comp_abs_sub_le (hM.differentiable one_ne_zero) hdec') (fun y => hMb |y|) x
  have hML := (tendsto_exp_neg_half_mul_of_abs_le (f := M) hMb).const_mul (2 * archConstantReal)
  have hsum := (((hFwL.add hRfL).add hDrL).sub hAL).add hML
  obtain ⟨-, -, hcosh, -⟩ := integral_exp_half_add_exp_neg_half hM.continuous hd2
  rw [zero_add, sub_zero, mul_zero, add_zero, hcosh] at hsum
  refine (hsum.neg).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [hq x hx, hsplit x hx]
  ring

/-- **The two-sided law.** For odd `M ∈ C¹` with `|M|, |M'| ≤ Ce^{−8|y|}`,
`(𝓛_D ω − Φ cosh(x/2) ω)(x)/(Φ(x)e^{x/2}) → 2 ∫_0^∞ M(r) sinh(r/2) dr` for `ω = M/Φ`. -/
theorem tendsto_twoSidedSource_div {M : ℝ → ℝ} {C : ℝ} (hM : ContDiff ℝ 1 M)
    (hodd : ∀ y, M (-y) = -M y) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) :
    Tendsto (fun x => (twoSidedGenerator (fun y => M y / riemannKernelReal y) x -
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) /
          (riemannKernelReal x * Real.exp (x / 2))) atTop
      (𝓝 (2 * ∫ r in Ioi (0 : ℝ), M r * Real.sinh (r / 2))) := by
  have hM0 : M 0 = 0 := by
    have := hodd 0
    rw [neg_zero] at this
    linarith
  have hC0 := nonneg_of_abs_le_mul_exp hdec
  have hd2 : ∀ r, 0 ≤ r → |M r| ≤ C * Real.exp (-(2 * r)) := fun r hr =>
    abs_le_exp_neg_two_of_decay hdec hr
  have hd2' : ∀ r, 0 ≤ r → |deriv M r| ≤ C * Real.exp (-(2 * r)) := fun r hr =>
    abs_le_exp_neg_two_of_decay hdec' hr
  have hMb : ∀ y, |M y| ≤ C := fun y => (hdec y).trans
    (mul_le_of_le_one_right hC0 (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y])))
  have hLip := abs_sub_le_of_decay hM hdec'
  have hsplit : ∀ x, 0 ≤ x → poleFreeWeilOperator M x =
      (∑' n : ℕ, vonMangoldtAtom n * M (x + Real.log n)) -
        (∑' n : ℕ, vonMangoldtAtom n * (if x < Real.log n then M (Real.log n - x) else 0)) +
        directPrimeMass M x - (∫ u in Ioi (0 : ℝ), profileArchTerm M x u) +
        2 * archConstantReal * M x := by
    intro x hx
    obtain ⟨hFw, hRf, hDr⟩ := summable_primeSplit hdec hx
    have hP : profilePrimeSum M x =
        (∑' n : ℕ, vonMangoldtAtom n * M (x + Real.log n)) -
          (∑' n : ℕ, vonMangoldtAtom n * (if x < Real.log n then M (Real.log n - x) else 0)) +
          directPrimeMass M x := by
      unfold profilePrimeSum directPrimeMass
      rw [← hFw.tsum_sub hRf, ← (hFw.sub hRf).tsum_add hDr]
      refine tsum_congr fun n => ?_
      by_cases h : x < Real.log n
      · rw [if_pos h, if_neg (not_le.mpr h), show x - Real.log n = -(Real.log n - x) by ring, hodd]
        ring
      · rw [if_neg h, if_pos (not_lt.mp h)]
        ring
    unfold poleFreeWeilOperator
    rw [hP]
  have hq : ∀ x, (twoSidedGenerator (fun y => M y / riemannKernelReal y) x -
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x)) /
        (riemannKernelReal x * Real.exp (x / 2)) =
      -(Real.exp (-x / 2) * poleFreeWeilOperator M x) := by
    intro x
    rw [twoSidedGenerator_profileGauge_sub_potential (summable_atom_mul_profileShift hdec x)
      (integrableOn_profileArchTerm hM.continuous hLip x)]
    have hΦ := (riemannKernelReal_pos x).ne'
    rw [show Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ by rw [← Real.exp_neg]; ring_nf]
    field_simp
  have hFwL := tendsto_exp_neg_half_mul_forwardPrimeMass hdec
  have hRfL := tendsto_exp_neg_half_mul_reflectedPrimeMass hM hM0 hC0 hd2 hd2'
  have hDrL := tendsto_exp_neg_half_mul_directPrimeMass hM hM0 hC0 hd2 hd2'
  have hAL := tendsto_exp_neg_half_mul_of_abs_le
    (f := fun x => ∫ u in Ioi (0 : ℝ), profileArchTerm M x u)
    (B := (2 * C + 3 * C) * ∫ u in Ioi (0 : ℝ), archLevyDensity u * u) fun x =>
      abs_integral_profileArchTerm_le hLip hMb x
  have hML := (tendsto_exp_neg_half_mul_of_abs_le (f := M) hMb).const_mul (2 * archConstantReal)
  have hsum := (((hFwL.sub hRfL).add hDrL).sub hAL).add hML
  obtain ⟨-, -, -, hsinh⟩ := integral_exp_half_add_exp_neg_half hM.continuous hd2
  rw [zero_sub, sub_zero, mul_zero, add_zero, neg_add_eq_sub, ← neg_sub, hsinh] at hsum
  refine (hsum.neg.congr' ?_).trans (by rw [neg_neg])
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [hq x, hsplit x hx]
  ring

/-- **A positive half-line cosh moment forces folded failure at infinity.** -/
theorem exists_infinity_window_foldedGenerator_lt_potential_of_coshMoment_pos {M : ℝ → ℝ} {C : ℝ}
    (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|)))
    (hpos : 0 < ∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2)) :
    ∃ X : ℝ, ∀ x, X ≤ x →
      foldedGenerator (fun y => M y / riemannKernelReal y) x <
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((tendsto_foldedSource_div hM hM0 hdec hdec').eventually
    (gt_mem_nhds (by linarith : -(2 * ∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2)) < 0)))
  refine ⟨X, fun x hx => ?_⟩
  have h := hX x hx
  have hden : 0 < riemannKernelReal x * Real.exp (x / 2) :=
    mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)
  rw [div_lt_iff₀ hden, zero_mul] at h
  linarith

/-- **A negative half-line cosh moment makes the gauge a strict folded supersolution at infinity.** -/
theorem exists_infinity_window_potential_lt_foldedGenerator_of_coshMoment_neg {M : ℝ → ℝ} {C : ℝ}
    (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|)))
    (hneg : (∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2)) < 0) :
    ∃ X : ℝ, ∀ x, X ≤ x →
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) <
        foldedGenerator (fun y => M y / riemannKernelReal y) x := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((tendsto_foldedSource_div hM hM0 hdec hdec').eventually
    (lt_mem_nhds (by linarith : (0 : ℝ) < -(2 * ∫ r in Ioi (0 : ℝ), M r * Real.cosh (r / 2)))))
  refine ⟨X, fun x hx => ?_⟩
  have h := hX x hx
  have hden : 0 < riemannKernelReal x * Real.exp (x / 2) :=
    mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)
  rw [lt_div_iff₀ hden, zero_mul] at h
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
