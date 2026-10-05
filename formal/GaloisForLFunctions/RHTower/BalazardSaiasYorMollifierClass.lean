import GaloisForLFunctions.RHTower.ZetaFractionalPartGramCriterion
import GaloisForLFunctions.RHTower.BaezDuarteCriterionHardDirection
import GaloisForLFunctions.RHTower.BaezDuarteTargetPairing

/-!
# Which mollifiers realise the Balazard–Saias–Yor criterion

For `M` entire, bounded on `Re s ≥ ½`, with `M(1) ≠ 0`, Jensen's inequality gives
`(1/2π)∫|ζM|² dt/(¼ + t²) ≥ |M(1)|²` (plus the off-line zeros), and RH follows if the ratio can be
made arbitrarily close to `1` (`riemannHypothesis_of_forall_mollified_meanSquare_le`).

**Dirichlet polynomials never reach the floor.**  For real `a` on a finite set of positive integers
the ratio is `Σ a_m a_n A(m,n)/(Σ a_n/n)²` with `A(m,n) = ∫_0^∞ {x/m}{x/n} dx/x²`.  Writing the form
as `∫_0^∞ (Σ a_n{x/n})² dx/x²`, the part `x < 1` is exactly `(Σ a_n/n)²` and the part `1 ≤ x < 2` is
`∫_1^2 (cx − a_1)² dx/x² ≥ c²/48`, so the ratio is at least `49/48` (`fractGram_form_ge`).  The
Dirichlet-polynomial (Gram) form of the criterion is therefore vacuous
(`not_forall_fractGram_form_le`).

**The right class.**  For a Báez-Duarte polynomial `P(s) = Σ c_n(n^{−s} − 1/n)` (which vanishes at
`1`) put `M(s) = −sP(s)/(s − 1)` (`bdMollifier`).  On the critical line `|ζM| = |ζP|`, and
`1 − M(1) = ⟪1, T − Σ c_n g_n⟫` with `M(1) = Σ c_n log n/n`, so a Báez-Duarte residual of norm `d`
gives `|M(1)| ≥ 1 − d` and `(1/2π)∫|ζM|² ≤ 1 + 2d + d²/η + η`.  With RH ⇒ `d_N → 0`
(`exists_bdRiesz_norm_lt_of_rh`) the ratio tends to `1`:

`RH ⟺ inf_M (1/2π)∫|ζM|² dt/(¼ + t²) / |M(1)|² = 1`
(`riemannHypothesis_iff_forall_mollified_meanSquare_le`).
-/

open MeasureTheory Set Filter Complex Topology

namespace RHTower

noncomputable section

theorem fract_div_nat_eq_self_div {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x < n) :
    Int.fract (x / n) = x / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Int.fract_eq_self]
  exact ⟨div_nonneg hx0 hn0.le, (div_lt_one hn0).mpr hxn⟩

theorem fract_le_self_of_nonneg {y : ℝ} (hy : 0 ≤ y) : Int.fract y ≤ y := by
  have h := Int.floor_nonneg.mpr hy
  rw [Int.fract]
  have : (0 : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast h
  linarith

theorem integrableOn_fract_mul_fract_div_sq {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    IntegrableOn (fun x : ℝ => Int.fract (x / m) * Int.fract (x / n) / x ^ 2) (Ioi 0) := by
  have hmeasF : Measurable (fun x : ℝ => Int.fract (x / m) * Int.fract (x / n) / x ^ 2) :=
    ((measurable_fract.comp (measurable_id.div_const _)).mul
      (measurable_fract.comp (measurable_id.div_const _))).div (measurable_id.pow_const 2)
  have hnn : ∀ x : ℝ, 0 ≤ Int.fract (x / m) * Int.fract (x / n) / x ^ 2 := fun x =>
    div_nonneg (mul_nonneg (Int.fract_nonneg _) (Int.fract_nonneg _)) (sq_nonneg x)
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 1) (by simp) hmeasF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : Int.fract (x / m) ≤ x := (fract_le_self_of_nonneg (by positivity)).trans
      (div_le_self hx0.le (by exact_mod_cast hm))
    have h2 : Int.fract (x / n) ≤ x := (fract_le_self_of_nonneg (by positivity)).trans
      (div_le_self hx0.le (by exact_mod_cast hn))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x), div_le_one (pow_pos hx0 2)]
    calc Int.fract (x / m) * Int.fract (x / n) ≤ x * x :=
          mul_le_mul h1 h2 (Int.fract_nonneg _) hx0.le
      _ = x ^ 2 := (sq x).symm
  · have hg : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    refine hg.mono' hmeasF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x), Real.rpow_neg hx0.le, Real.rpow_two,
      div_eq_mul_inv]
    have : Int.fract (x / m) * Int.fract (x / n) ≤ 1 :=
      mul_le_one₀ (Int.fract_lt_one _).le (Int.fract_nonneg _) (Int.fract_lt_one _).le
    exact mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg x)) this

/-- `Σ_{m,n} a_m a_n A(m, n) = ∫_0^∞ (Σ_n a_n {x/n})² dx/x²`. -/
theorem sum_fractGram_eq_integral {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    ∑ m ∈ S, ∑ n ∈ S, a m * a n * fractGram m n =
      ∫ x in Ioi (0 : ℝ), (∑ n ∈ S, a n * Int.fract (x / n)) ^ 2 / x ^ 2 := by
  have hpt : ∀ x : ℝ, (∑ n ∈ S, a n * Int.fract (x / n)) ^ 2 / x ^ 2 =
      ∑ m ∈ S, ∑ n ∈ S, a m * a n * (Int.fract (x / m) * Int.fract (x / n) / x ^ 2) := by
    intro x
    rw [sq, Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m hm => integrable_finsetSum _ fun n hn =>
    (integrableOn_fract_mul_fract_div_sq (hS m hm) (hS n hn)).const_mul _]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_finsetSum _ fun n hn =>
    (integrableOn_fract_mul_fract_div_sq (hS m hm) (hS n hn)).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, fractGram]

/-- **The Dirichlet-polynomial Gram form is bounded away from its Jensen floor.**
`Σ_{m,n} a_m a_n A(m, n) ≥ (49/48)(Σ a_n/n)²`: on `(0, 1)` the integrand is `(Σ a_n/n)²`, and on
`[1, 2)` it is `(cx − a_1)²/x²`, whose integral is at least `(Σ a_n/n)²/48`. -/
theorem fractGram_form_ge {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    (49 / 48) * (∑ n ∈ S, a n / n) ^ 2 ≤ ∑ m ∈ S, ∑ n ∈ S, a m * a n * fractGram m n := by
  set c : ℝ := ∑ n ∈ S, a n / n with hc
  set b : ℝ := if 1 ∈ S then a 1 else 0 with hb
  set g : ℝ → ℝ := fun x => (∑ n ∈ S, a n * Int.fract (x / n)) ^ 2 / x ^ 2 with hg
  rw [sum_fractGram_eq_integral hS a]
  have hgint : IntegrableOn g (Ioi 0) := by
    have hpt : ∀ x : ℝ, g x =
        ∑ m ∈ S, ∑ n ∈ S, a m * a n * (Int.fract (x / m) * Int.fract (x / n) / x ^ 2) := by
      intro x
      simp only [hg]
      rw [sq, Finset.sum_mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [show g = fun x : ℝ => ∑ m ∈ S, ∑ n ∈ S, a m * a n *
        (Int.fract (x / m) * Int.fract (x / n) / x ^ 2) from funext hpt]
    exact integrable_finsetSum _ fun m hm => integrable_finsetSum _ fun n hn =>
      (integrableOn_fract_mul_fract_div_sq (hS m hm) (hS n hn)).const_mul _
  have hg0 : ∀ x, 0 ≤ g x := fun x => by simp only [hg]; positivity
  -- the two pieces
  have hsub : Ioo (0 : ℝ) 1 ∪ Ico 1 2 ⊆ Ioi 0 := by
    rintro x (hx | hx)
    · exact hx.1
    · exact lt_of_lt_of_le zero_lt_one hx.1
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ico 1 2) := by
    rw [Set.disjoint_left]; intro x h1 h2; linarith [h1.2, h2.1]
  have hmono : ∫ x in Ioo (0 : ℝ) 1 ∪ Ico 1 2, g x ≤ ∫ x in Ioi (0 : ℝ), g x :=
    setIntegral_mono_set hgint (Eventually.of_forall fun x => hg0 x)
      (Eventually.of_forall hsub)
  rw [setIntegral_union hdisj measurableSet_Ico (hgint.mono_set fun x hx => hsub (Or.inl hx))
    (hgint.mono_set fun x hx => hsub (Or.inr hx))] at hmono
  -- on `(0, 1)`
  have h01 : ∫ x in Ioo (0 : ℝ) 1, g x = c ^ 2 := by
    have : ∀ x ∈ Ioo (0 : ℝ) 1, g x = c ^ 2 := by
      intro x hx
      have hx0 : 0 < x := hx.1
      simp only [hg]
      have hsum : ∑ n ∈ S, a n * Int.fract (x / n) = x * c := by
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn1 := hS n hn
        rw [fract_div_nat_eq_self_div hn1 hx0.le (by
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          linarith [hx.2])]
        ring
      rw [hsum]; field_simp
    rw [setIntegral_congr_fun measurableSet_Ioo this, setIntegral_const]
    simp
  -- on `[1, 2)`
  have h12 : c ^ 2 / 48 ≤ ∫ x in Ico (1 : ℝ) 2, g x := by
    have hlow : ∀ x ∈ Ico (1 : ℝ) 2, (c * x - b) ^ 2 / 4 ≤ g x := by
      intro x hx
      have hx1 : 1 ≤ x := hx.1
      have hx2 : x < 2 := hx.2
      have hx0 : 0 < x := by linarith
      simp only [hg]
      have hsum : ∑ n ∈ S, a n * Int.fract (x / n) = c * x - b := by
        have hterm : ∀ n ∈ S, a n * Int.fract (x / n) =
            a n * (x / n) - (if n = 1 then a 1 else 0) := by
          intro n hn
          have hn1 := hS n hn
          by_cases h1 : n = 1
          · subst h1
            simp only [Nat.cast_one, div_one, if_true]
            rw [Int.fract, show ⌊x⌋ = 1 from by
              rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith]
            push_cast; ring
          · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
            rw [fract_div_nat_eq_self_div hn1 hx0.le (by linarith), if_neg h1, sub_zero]
        rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hc, Finset.sum_mul,
          Finset.sum_ite_eq']
        rw [hb]
        congr 1
        exact Finset.sum_congr rfl fun n _ => by ring
      rw [hsum, div_le_div_iff₀ (by norm_num) (by positivity)]
      have hsq : x ^ 2 ≤ 4 := by nlinarith
      exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    have hint1 : IntegrableOn (fun x : ℝ => (c * x - b) ^ 2 / 4) (Ico 1 2) :=
      (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ico_subset_Icc_self
    have := setIntegral_mono_on hint1 (hgint.mono_set fun x hx => hsub (Or.inr hx))
      measurableSet_Ico hlow
    refine le_trans ?_ this
    rw [integral_Icc_eq_integral_Ico.symm, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
    have hval : ∫ x in (1 : ℝ)..2, (c * x - b) ^ 2 / 4 =
        (7 / 3 * c ^ 2 - 3 * b * c + b ^ 2) / 4 := by
      have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) 2, HasDerivAt
          (fun x : ℝ => c ^ 2 / 12 * x ^ 3 - b * c / 4 * x ^ 2 + b ^ 2 / 4 * x)
          ((c * x - b) ^ 2 / 4) x := by
        intro x _
        have h := (((hasDerivAt_pow 3 x).const_mul (c ^ 2 / 12)).sub
          ((hasDerivAt_pow 2 x).const_mul (b * c / 4))).add
            ((hasDerivAt_id' x).const_mul (b ^ 2 / 4))
        exact h.congr_deriv (by push_cast; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((Continuous.intervalIntegrable (by fun_prop) _ _))]
      ring
    rw [hval]
    nlinarith [sq_nonneg (b - 3 / 2 * c)]
  linarith

/-- **The Dirichlet-polynomial form of the mollified criterion is vacuous.**  No real Dirichlet
polynomial brings the Gram ratio below `49/48`, so the hypothesis of
`riemannHypothesis_of_fractGram_form` never holds. -/
theorem not_forall_fractGram_form_le :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ (S : Finset ℕ) (a : ℕ → ℝ), (∀ n ∈ S, 1 ≤ n) ∧
      ∑ n ∈ S, a n / n ≠ 0 ∧
      ∑ m ∈ S, ∑ n ∈ S, a m * a n * fractGram m n ≤ (1 + ε) * (∑ n ∈ S, a n / n) ^ 2 := by
  intro h
  obtain ⟨S, a, hS, h0, hle⟩ := h (1 / 96) (by norm_num)
  have hge := fractGram_form_ge hS a
  have hpos : 0 < (∑ n ∈ S, a n / n) ^ 2 := by positivity
  nlinarith

/-! ## The corrected mollifiers -/

/-- The mollifier `M(s) = −s · P(s)/(s − 1)` attached to a Báez-Duarte polynomial
`P(s) = Σ c_n (n^{−s} − 1/n)`, which vanishes at `1`. -/
def bdMollifier (S : Finset ℕ) (c : ℕ → ℝ) (s : ℂ) : ℂ :=
  -(s * dslope (bdMollPoly S c) 1 s)

theorem bdMollPoly_one (S : Finset ℕ) (c : ℕ → ℝ) : bdMollPoly S c 1 = 0 := by
  unfold bdMollPoly
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [Complex.cpow_neg_one, sub_self, mul_zero]

theorem hasDerivAt_natCast_cpow_neg {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    HasDerivAt (fun s : ℂ => (n : ℂ) ^ (-s)) (-((n : ℂ) ^ (-s) * Complex.log n)) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h := (hasDerivAt_neg s).const_cpow (c := (n : ℂ)) (Or.inl hn0)
  convert h using 1
  ring

theorem hasDerivAt_bdMollPoly {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) (s : ℂ) :
    HasDerivAt (bdMollPoly S c)
      (∑ n ∈ S, (c n : ℂ) * (-((n : ℂ) ^ (-s) * Complex.log n))) s := by
  have h := HasDerivAt.sum (u := S) (A := fun n s => (c n : ℂ) * ((n : ℂ) ^ (-s) - (n : ℂ)⁻¹))
    (A' := fun n => (c n : ℂ) * (-((n : ℂ) ^ (-s) * Complex.log n))) (x := s)
    (fun n hn => ((hasDerivAt_natCast_cpow_neg (hS n hn) s).sub_const _).const_mul _)
  have heq : bdMollPoly S c =
      ∑ n ∈ S, (fun s : ℂ => (c n : ℂ) * ((n : ℂ) ^ (-s) - (n : ℂ)⁻¹)) := by
    funext z; simp [bdMollPoly, Finset.sum_apply]
  rw [heq]; exact h

theorem differentiable_bdMollPoly {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) :
    Differentiable ℂ (bdMollPoly S c) := fun s => (hasDerivAt_bdMollPoly hS c s).differentiableAt

theorem differentiable_bdMollifier {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) :
    Differentiable ℂ (bdMollifier S c) := by
  have hd : DifferentiableOn ℂ (dslope (bdMollPoly S c) 1) Set.univ :=
    (differentiableOn_dslope Filter.univ_mem).mpr (differentiable_bdMollPoly hS c).differentiableOn
  intro s
  exact ((differentiableAt_id.mul (hd.differentiableAt Filter.univ_mem)).neg)

theorem bdMollifier_one {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) :
    bdMollifier S c 1 = ((∑ n ∈ S, c n * (Real.log n / n) : ℝ) : ℂ) := by
  unfold bdMollifier
  rw [dslope_same, (hasDerivAt_bdMollPoly hS c 1).deriv, one_mul]
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by have := hS n hn; omega : n ≠ 0)
  rw [Complex.cpow_neg_one, ← Complex.natCast_log]
  field_simp

theorem bdMollifier_eq {S : Finset ℕ} (c : ℕ → ℝ) {s : ℂ} (hs : s ≠ 1) :
    bdMollifier S c s = -(s * bdMollPoly S c s / (s - 1)) := by
  unfold bdMollifier
  rw [dslope_of_ne _ hs, slope_def_field, bdMollPoly_one, sub_zero]
  ring

theorem norm_bdMollPoly_le {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : ‖bdMollPoly S c s‖ ≤ ∑ n ∈ S, 2 * |c n| := by
  unfold bdMollPoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 := hS n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1' (by linarith)
  have h2 : ‖((n : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]; exact inv_le_one_of_one_le₀ hn1'
  have := norm_sub_le ((n : ℂ) ^ (-s)) ((n : ℂ)⁻¹)
  nlinarith [abs_nonneg (c n)]

theorem exists_bound_bdMollifier {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) :
    ∃ B : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖bdMollifier S c s‖ ≤ B := by
  have hcont := (differentiable_bdMollifier hS c).continuous
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (1 : ℂ) 1).exists_bound_of_continuousOn
    hcont.continuousOn
  set C : ℝ := ∑ n ∈ S, 2 * |c n| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun n _ => by positivity
  refine ⟨max B₀ (2 * C), fun s hs => ?_⟩
  by_cases h : ‖s - 1‖ ≤ 1
  · exact (hB₀ s (by rwa [Metric.mem_closedBall, dist_eq_norm])).trans (le_max_left _ _)
  · have h : 1 < ‖s - 1‖ := not_le.mp h
    have hs1 : s ≠ 1 := fun h' => by rw [h', sub_self, norm_zero] at h; linarith
    rw [bdMollifier_eq c hs1, norm_neg, norm_div, norm_mul]
    have hP := norm_bdMollPoly_le hS c hs
    have hss : ‖s‖ ≤ ‖s - 1‖ + 1 := by
      calc ‖s‖ = ‖(s - 1) + 1‖ := by ring_nf
        _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖s - 1‖ + 1 := by rw [norm_one]
    have hpos : 0 < ‖s - 1‖ := by linarith
    rw [div_le_iff₀ hpos]
    calc ‖s‖ * ‖bdMollPoly S c s‖ ≤ (‖s - 1‖ + 1) * C :=
          mul_le_mul hss hP (norm_nonneg _) (by linarith)
      _ ≤ 2 * C * ‖s - 1‖ := by nlinarith
      _ ≤ max B₀ (2 * C) * ‖s - 1‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le

theorem norm_riemannZeta_mul_bdMollifier_line (S : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) :
    ‖riemannZeta (1 / 2 + t * I) * bdMollifier S c (1 / 2 + t * I)‖ =
      ‖riemannZeta (1 / 2 + t * I) * bdMollPoly S c (1 / 2 + t * I)‖ := by
  have hs1 : (1 / 2 : ℂ) + t * I ≠ 1 := fun h => by
    have := congrArg Complex.re h; norm_num at this
  rw [bdMollifier_eq c hs1, norm_mul, norm_mul, norm_neg, norm_div, norm_mul,
    norm_half_add_mul_I, norm_half_add_mul_I_sub_one]
  have : 0 < Real.sqrt (1 / 4 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- The pairing of the target with a Báez-Duarte residual is `1 − M(1)`. -/
theorem inner_bdTarget_residual {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) :
    inner ℂ bdTarget (bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)) =
      1 - bdMollifier S c 1 := by
  rw [inner_sub_right, inner_sum, inner_bdTarget_self, bdMollifier_one hS c]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 := hS n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [inner_smul_right]
  have hθ : ((n : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn1)
  rw [← inner_conj_symm, inner_bdGen_bdTarget (inv_pos.mpr hn0) hθ, Complex.conj_ofReal]
  rw [Real.log_inv]
  push_cast
  field_simp

/-- **The mollified Balazard–Saias–Yor criterion is an equivalence.**  Under RH, for every
`ε > 0` the mollifier `M(s) = −sP(s)/(s − 1)` built from a Báez-Duarte approximant `P` satisfies
`(1/2π) ∫ |ζM|² dt/(¼ + t²) ≤ (1 + ε)|M(1)|²`. -/
theorem exists_mollifier_meanSquare_le_of_rh (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℂ → ℂ, Differentiable ℂ M ∧
      (∃ B : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖M s‖ ≤ B) ∧ M 1 ≠ 0 ∧
      Integrable (fun t : ℝ =>
        ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) ∧
      (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)
        ≤ (1 + ε) * ‖M 1‖ ^ 2 := by
  set η : ℝ := min ε 1 / 20 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 20 := by rw [hη]; have := min_le_right ε 1; linarith
  have hηε : 20 * η ≤ ε := by rw [hη]; have := min_le_left ε 1; linarith
  obtain ⟨N, δ, -, -, hlt⟩ := exists_bdRiesz_norm_lt_of_rh hRH hη0
  set S : Finset ℕ := Finset.Icc 1 N with hSdef
  have hS : ∀ n ∈ S, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  set c := bdRieszCoeff N δ with hc
  set R : BDCarrier := bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹) with hR
  set d : ℝ := ‖R‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  obtain ⟨hint, heq⟩ := integrable_and_norm_sq_bdTarget_sub_sum_bdGen hS c
  obtain ⟨hwint, hwval⟩ := integrable_and_integral_criticalLine_weight
  -- `M(1)`
  have hM1 : ‖1 - bdMollifier S c 1‖ ≤ d := by
    rw [← inner_bdTarget_residual hS c]
    refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
    have hT : ‖bdTarget‖ = 1 := norm_bdTarget
    rw [hT, one_mul]
  have hM1low : 1 - d ≤ ‖bdMollifier S c 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (bdMollifier S c 1)
    rw [norm_one] at this
    have h2 : ‖(1 : ℂ) - bdMollifier S c 1‖ = ‖bdMollifier S c 1 - 1‖ := norm_sub_rev _ _
    linarith [norm_sub_rev (1 : ℂ) (bdMollifier S c 1)]
  -- the pointwise bound
  set F : ℝ → ℝ := fun t => ‖1 + riemannZeta (1 / 2 + t * I) * bdMollPoly S c (1 / 2 + t * I)‖
    with hF
  set w : ℝ → ℝ := fun t => 1 / (1 / 4 + t ^ 2) with hw
  have hpt : ∀ t : ℝ, ‖riemannZeta (1 / 2 + t * I) * bdMollifier S c (1 / 2 + t * I)‖ ^ 2 /
      (1 / 4 + t ^ 2) ≤ (1 + η) * w t + (1 / η + 1) * (F t ^ 2 / (1 / 4 + t ^ 2)) := by
    intro t
    rw [norm_riemannZeta_mul_bdMollifier_line]
    set z := riemannZeta (1 / 2 + t * I) * bdMollPoly S c (1 / 2 + t * I)
    have hz : ‖z‖ ≤ 1 + F t := by
      have : z = (1 + z) - 1 := by ring
      calc ‖z‖ = ‖(1 + z) - 1‖ := by rw [← this]
        _ ≤ ‖1 + z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + F t := by rw [norm_one]; simp [hF, z]; ring
    have hF0 : 0 ≤ F t := norm_nonneg _
    have hsq : ‖z‖ ^ 2 ≤ (1 + η) + (1 / η + 1) * F t ^ 2 := by
      have h1 : ‖z‖ ^ 2 ≤ (1 + F t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      have h2 : 2 * F t ≤ F t ^ 2 / η + η := by
        rw [div_add' _ _ _ hη0.ne', le_div_iff₀ hη0]; nlinarith [sq_nonneg (F t - η)]
      have h3 : F t ^ 2 / η = (1 / η) * F t ^ 2 := by ring
      nlinarith
    have hq : 0 < 1 / 4 + t ^ 2 := by positivity
    simp only [hw]
    rw [div_le_iff₀ hq]
    have : ((1 + η) * (1 / (1 / 4 + t ^ 2)) + (1 / η + 1) * (F t ^ 2 / (1 / 4 + t ^ 2))) *
        (1 / 4 + t ^ 2) = (1 + η) + (1 / η + 1) * F t ^ 2 := by field_simp
    rw [this]; exact hsq
  have hdom : Integrable
      (fun t : ℝ => (1 + η) * w t + (1 / η + 1) * (F t ^ 2 / (1 / 4 + t ^ 2))) :=
    (hwint.const_mul _).add (hint.const_mul _)
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      ‖riemannZeta (1 / 2 + t * I) * bdMollifier S c (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2))
      volume := by
    have hcz : Continuous fun t : ℝ => riemannZeta (1 / 2 + t * I) := by
      have := continuous_riemannZeta_vertical (σ := 1 / 2) (by norm_num)
      simpa using this
    have hcm : Continuous fun t : ℝ => bdMollifier S c (1 / 2 + t * I) :=
      (differentiable_bdMollifier hS c).continuous.comp (by fun_prop)
    exact (((hcz.mul hcm).norm.pow 2).div (by fun_prop)
      (fun t => by positivity)).aestronglyMeasurable
  have hintM : Integrable (fun t : ℝ =>
      ‖riemannZeta (1 / 2 + t * I) * bdMollifier S c (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) :=
    hdom.mono' hmeas (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt t)
  refine ⟨bdMollifier S c, differentiable_bdMollifier hS c, exists_bound_bdMollifier hS c,
    fun h0 => by rw [h0, norm_zero] at hM1low; linarith [hlt], hintM, ?_⟩
  -- the mean square
  have hmean : (2 * Real.pi)⁻¹ * ∫ t : ℝ,
      ‖riemannZeta (1 / 2 + t * I) * bdMollifier S c (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)
      ≤ 1 + 3 * η := by
    have hi := integral_mono hintM hdom hpt
    rw [integral_add (hwint.const_mul _) (hint.const_mul _), integral_const_mul,
      integral_const_mul] at hi
    have hw2 : ∫ t : ℝ, w t = 2 * Real.pi := hwval
    rw [hw2] at hi
    set I : ℝ := ∫ t : ℝ, F t ^ 2 / (1 / 4 + t ^ 2) with hI
    have hd2 : (2 * Real.pi)⁻¹ * I = d ^ 2 := by
      rw [hd, heq]
    have hπ : 0 < (2 * Real.pi)⁻¹ := by positivity
    have hdη : d ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hd0 hlt.le 2
    have hc1 : (2 * Real.pi)⁻¹ * ((1 + η) * (2 * Real.pi)) = 1 + η := by
      field_simp
    calc (2 * Real.pi)⁻¹ * ∫ t : ℝ, _ ≤ (2 * Real.pi)⁻¹ * ((1 + η) * (2 * Real.pi) +
          (1 / η + 1) * I) :=
          mul_le_mul_of_nonneg_left hi hπ.le
      _ = (2 * Real.pi)⁻¹ * ((1 + η) * (2 * Real.pi)) +
            (1 / η + 1) * ((2 * Real.pi)⁻¹ * I) := by
          ring
      _ = (1 + η) + (1 / η + 1) * d ^ 2 := by rw [hc1, hd2]
      _ ≤ (1 + η) + (1 / η + 1) * η ^ 2 := by gcongr
      _ = 1 + 2 * η + η ^ 2 := by field_simp; ring
      _ ≤ 1 + 3 * η := by nlinarith
  refine hmean.trans ?_
  have hlow2 : (1 - η) ^ 2 ≤ ‖bdMollifier S c 1‖ ^ 2 :=
    pow_le_pow_left₀ (by linarith) (le_trans (by linarith [hlt.le]) hM1low) 2
  have h1 : (1 + ε) * (1 - η) ^ 2 ≤ (1 + ε) * ‖bdMollifier S c 1‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hlow2 (by linarith)
  have h3 : 5 * η ≤ ε * (1 - 2 * η) := by nlinarith
  have h2 : 1 + 3 * η ≤ (1 + ε) * (1 - η) ^ 2 := by
    nlinarith [sq_nonneg η, mul_nonneg hε.le (sq_nonneg η)]
  linarith

/-- **RH ⟺ the mollified Balazard–Saias–Yor ratio can be made arbitrarily close to `1`.** -/
theorem riemannHypothesis_iff_forall_mollified_meanSquare_le :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ M : ℂ → ℂ, Differentiable ℂ M ∧
      (∃ B : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖M s‖ ≤ B) ∧ M 1 ≠ 0 ∧
      Integrable (fun t : ℝ =>
        ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) ∧
      (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖riemannZeta (1 / 2 + t * I) * M (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)
        ≤ (1 + ε) * ‖M 1‖ ^ 2 :=
  ⟨fun hRH _ hε => exists_mollifier_meanSquare_le_of_rh hRH hε,
    riemannHypothesis_of_forall_mollified_meanSquare_le⟩

end

end RHTower
