import GaloisForLFunctions.RHTower.GaussianFormationUndampedLimit
import GaloisForLFunctions.HTGeometry.LogDerivativeResidue
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic

/-!
# The single-point abscissa law of the Gaussian passage

For `Re s > 0` the logarithmic derivative of the Gaussian Euler–continuum formation is
`Φₓ'/Φₓ(s) = A(s) − G_s(πx)`, where `A = h∞'/h∞` and
`G_s(y) = Σ Λ(n) n^{-s} e^{-yn²} − E(y, 1−s)` is the prime-minus-continuum gap.  This file reads the
whole zero-free half-plane off the behaviour of the passage at a single point.

* **Mellin transform in the damping variable** (`mellin_gaussianPrimeContinuumGap`).  For
  `Re s + 2 Re w > 1`, `∫₀^∞ y^{w-1} G_s(y) dy = Γ(w)(Σ Λ(n) n^{-(s+2w)} − 1/(s+2w−1))`.  The prime
  part is `hasSum_mellin` with frequencies `n²`; the continuum part is Fubini against
  `∫₀^∞ y^{w-1} e^{-yu²} dy = Γ(w) u^{-2w}`.
* **Single-point law** (`xi_ne_zero_of_isBigO_gaussianPassage`).  If `Φₓ'/Φₓ(s) = O(x^{-a})` as
  `x → 0⁺` (`a ≥ 0`), the gap is `O(y^{-a})` at `0` and decays faster than any power at `∞`, so its
  Mellin transform is holomorphic on `Re w > a`.  There it equals `Γ(w)(A(s+2w) − ξ'/ξ(s+2w))`, so
  `ξ' = ξ·K` on the whole half-plane `Re w > a` for a holomorphic `K` (identity theorem).  A zero of
  `ξ` at `z = s + 2w₀` would force `(u − z)ξ'/ξ(u) → 0`, against the residue `ord_z ξ ≥ 1`.  Hence
  `ξ(z) ≠ 0` for `Re z > Re s + 2a`.
* **Abscissa law** (`xi_zero_re_le_iff_gaussianPassage_bounded`,
  `riemannHypothesis_iff_gaussianPassage_bounded`).  All zeros satisfy `Re ρ ≤ θ` iff the passage
  is bounded at every real `σ ∈ (max θ 0, 2)`; RH iff it is bounded at every real `σ ∈ (½, 2)`.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- The Gaussian prime current at `s` as a function of the damping `y`. -/
def gaussianDampedPrimeSum (s : ℂ) (y : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
    (Real.exp (-(y * (n : ℝ) ^ 2)) : ℂ)

theorem ofReal_sq_cpow_eq {u : ℝ} (hu : 0 < u) (w : ℂ) :
    (((u ^ 2 : ℝ)) : ℂ) ^ w = (u : ℂ) ^ (2 * w) := by
  have hu2 : (((u ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hu 2).ne'
  have hu1 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  rw [Complex.cpow_def_of_ne_zero hu2, Complex.cpow_def_of_ne_zero hu1,
    ← Complex.ofReal_log (pow_pos hu 2).le, ← Complex.ofReal_log hu.le, Real.log_pow]
  push_cast
  ring_nf

theorem norm_vonMangoldt_term_le {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ ≤ n := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · exact Nat.cast_nonneg n
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have hpow : 1 ≤ (n : ℝ) ^ s.re := Real.one_le_rpow hn1 hs
    have hΛ : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg n))
    calc ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ / (n : ℝ) ^ s.re ≤
          ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) one_pos hpow
      _ ≤ n := by rw [div_one]; exact hΛ

theorem summable_norm_vonMangoldt_term_mul_gaussian {s : ℂ} (hs : 0 ≤ s.re) {t : ℝ}
    (ht : 0 < t) :
    Summable fun n : ℕ => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ *
      Real.exp (-(t * (n : ℝ) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Real.summable_pow_mul_exp_neg_nat_mul 1 ht).congr fun n => by rw [pow_one])
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp : Real.exp (-(t * (n : ℝ) ^ 2)) ≤ Real.exp (-t * n) := by
    rw [Real.exp_le_exp]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h
      have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq ht.le]
  exact mul_le_mul (norm_vonMangoldt_term_le hs n) hexp (by positivity) hn0

/-- **Mellin transform of the Gaussian prime current.**  For `Re s ≥ 0`, `Re w > 0` and
`Re s + 2 Re w > 1`, `∫₀^∞ y^{w-1} Σ Λ(n) n^{-s} e^{-yn²} dy = Γ(w) Σ Λ(n) n^{-(s+2w)}`. -/
theorem mellin_gaussianDampedPrimeSum {s w : ℂ} (hs : 0 ≤ s.re) (hw : 0 < w.re)
    (hsw : 1 < s.re + 2 * w.re) :
    mellin (gaussianDampedPrimeSum s) w =
      Complex.Gamma w * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + 2 * w) := by
  set a : ℕ → ℂ := fun n => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n
    with ha
  set p : ℕ → ℝ := fun n => (n : ℝ) ^ 2 with hp
  have hpos : ∀ n, a n = 0 ∨ 0 < p n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · left; subst h; simp [ha]
    · right; simp only [hp]; positivity
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun n => a n * (Real.exp (-p n * t) : ℂ))
      (gaussianDampedPrimeSum s t) := by
    intro t ht
    have hfun : (fun n => a n * (Real.exp (-p n * t) : ℂ)) =
        fun n => a n * (Real.exp (-(t * (n : ℝ) ^ 2)) : ℂ) := by
      funext n; simp only [hp]; congr 3; ring
    rw [hfun]
    have hsn : Summable fun n => ‖a n * (Real.exp (-(t * (n : ℝ) ^ 2)) : ℂ)‖ := by
      refine (summable_norm_vonMangoldt_term_mul_gaussian hs ht).congr fun n => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hsn.of_norm.hasSum
  have hweight : Summable fun n => ‖a n‖ / p n ^ w.re := by
    refine (summable_vonMangoldt_rpow_neg (s := s) (c := 2 * w.re) hsw).congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [ha]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast h
      simp only [ha, hp, LSeries.norm_term_eq, if_neg h.ne']
      rw [← Real.rpow_natCast_mul hn0.le, div_div, ← Real.rpow_add hn0, Real.rpow_neg hn0.le,
        div_eq_mul_inv]
      push_cast
      ring_nf
  have h := hasSum_mellin hpos hw hF hweight
  rw [← h.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp [ha]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast h0
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    simp only [ha, hp, LSeries.term_of_ne_zero h0.ne']
    rw [ofReal_sq_cpow_eq hn0, Complex.ofReal_natCast, Complex.cpow_add _ _ hnc]
    field_simp

/-- `(1/u²)^w = u^{-2w}` for `u > 0`. -/
theorem one_div_ofReal_sq_cpow {u : ℝ} (hu : 0 < u) (w : ℂ) :
    (1 / ((u ^ 2 : ℝ) : ℂ)) ^ w = (u : ℂ) ^ (-(2 * w)) := by
  have hinv : (1 / ((u ^ 2 : ℝ) : ℂ)) = (((u⁻¹) ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [hinv, ofReal_sq_cpow_eq (inv_pos.2 hu), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hu.le]; exact Real.pi_pos.ne),
    Complex.cpow_neg]

/-- **Mellin transform of the continuum current.**  For `Re w > 0` and `Re s + 2 Re w > 1`, the
transform converges and `∫₀^∞ y^{w-1} E(y, 1-s) dy = Γ(w)/(s + 2w - 1)`. -/
theorem mellin_gaussianIncompleteMellin_one_sub {s w : ℂ} (hw : 0 < w.re)
    (hsw : 1 < s.re + 2 * w.re) :
    MellinConvergent (fun y : ℝ => gaussianIncompleteMellin y (1 - s)) w ∧
    mellin (fun y : ℝ => gaussianIncompleteMellin y (1 - s)) w =
      Complex.Gamma w / (s + 2 * w - 1) := by
  set F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) ^ (w - 1) *
    ((Real.exp (-(p.1 * p.2 ^ 2)) : ℂ) * (p.2 : ℂ) ^ (-s)) with hF
  have hE : ∀ y : ℝ, gaussianIncompleteMellin y (1 - s) =
      ∫ u in Ioi (1 : ℝ), (Real.exp (-(y * u ^ 2)) : ℂ) * (u : ℂ) ^ (-s) := by
    intro y
    rw [gaussianIncompleteMellin, integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [show 1 - s - 1 = -s by ring, show -y * u ^ 2 = -(y * u ^ 2) by ring]
  have hslice : ∀ y : ℝ, (y : ℂ) ^ (w - 1) • gaussianIncompleteMellin y (1 - s) =
      ∫ u in Ioi (1 : ℝ), F (y, u) := by
    intro y
    rw [hE, smul_eq_mul, ← integral_const_mul]
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)) with hμ
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioi (1 : ℝ)) with hν
  have hprod : μ.prod ν = ((volume : Measure ℝ).prod volume).restrict (Ioi 0 ×ˢ Ioi 1) :=
    Measure.prod_restrict _ _
  have hcont : ContinuousOn F (Ioi 0 ×ˢ Ioi 1) := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    have hp2 : (0 : ℝ) < p.2 := lt_trans one_pos hp.2
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ (ContinuousAt.mul ?_ ?_)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const
        (Complex.ofReal_mem_slitPlane.2 hp1)
    · fun_prop
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const
        (Complex.ofReal_mem_slitPlane.2 hp2)
  have hmeas : AEStronglyMeasurable F (μ.prod ν) := by
    rw [hprod]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  have hnormF : ∀ y u : ℝ, 0 < y → 0 < u → ‖F (y, u)‖ =
      y ^ (w.re - 1) * Real.exp (-(u ^ 2) * y ^ (1 : ℝ)) * u ^ (-s.re) := by
    intro y u hy hu
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_cpow_eq_rpow_re_of_pos hu,
      Complex.sub_re, Complex.one_re, Complex.neg_re, Real.rpow_one]
    ring_nf
  have hpow : ∀ u : ℝ, 0 < u → (1 / u ^ 2) ^ w.re * u ^ (-s.re) = u ^ (-(s.re + 2 * w.re)) := by
    intro u hu
    have h1 : (1 / u ^ 2 : ℝ) = u ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hu.le, one_div]; norm_cast
    rw [h1, ← Real.rpow_mul hu.le, ← Real.rpow_add hu]
    congr 1; ring
  have hinner_norm : ∀ u : ℝ, 0 < u →
      ∫ y, ‖F (y, u)‖ ∂μ = Real.Gamma w.re * u ^ (-(s.re + 2 * w.re)) := by
    intro u hu
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hw (by positivity : 0 < u ^ 2)
    calc ∫ y, ‖F (y, u)‖ ∂μ =
          ∫ y in Ioi (0 : ℝ), (y ^ (w.re - 1) * Real.exp (-(u ^ 2 * y))) * u ^ (-s.re) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
          rw [hnormF y u hy hu, Real.rpow_one]
          ring_nf
      _ = (1 / u ^ 2) ^ w.re * Real.Gamma w.re * u ^ (-s.re) := by rw [integral_mul_const, h]
      _ = _ := by rw [mul_comm ((1 / u ^ 2) ^ w.re), mul_assoc, hpow u hu]
  have hint : Integrable F (μ.prod ν) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · rw [hν, ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
      have hmaj : IntegrableOn (fun y : ℝ => y ^ (w.re - 1) * Real.exp (-(u ^ 2) * y ^ (1 : ℝ)))
          (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) le_rfl (by positivity)
      refine Integrable.mono' (hmaj.mul_const (u ^ (-s.re))) ?_ ?_
      · exact (hcont.comp (Continuous.continuousOn (by fun_prop : Continuous fun y : ℝ => (y, u)))
          (fun y hy => ⟨hy, hu⟩)).aestronglyMeasurable measurableSet_Ioi
      · rw [hμ, ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun y hy => (hnormF y u hy hu0).le
    · have hI : IntegrableOn (fun u : ℝ => Real.Gamma w.re * u ^ (-(s.re + 2 * w.re))) (Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (a := -(s.re + 2 * w.re)) (by linarith) one_pos).const_mul _
      exact hI.congr_fun (fun u hu => (hinner_norm u (lt_trans one_pos hu)).symm) measurableSet_Ioi
  have hconv : MellinConvergent (fun y : ℝ => gaussianIncompleteMellin y (1 - s)) w := by
    have h := hint.integral_prod_left
    refine (h.congr ?_ : Integrable _ μ)
    rw [hμ]
    filter_upwards with y
    exact (hslice y).symm
  refine ⟨hconv, ?_⟩
  have hswap := integral_integral_swap (f := fun y u => F (y, u)) hint
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi (fun y _ => hslice y)]
  change ∫ y, ∫ u, F (y, u) ∂ν ∂μ = _
  rw [hswap]
  have hcol : ∀ u ∈ Ioi (1 : ℝ), ∫ y, F (y, u) ∂μ =
      Complex.Gamma w * (u : ℂ) ^ (-s - 2 * w) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    have hu1 : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hw (by positivity : 0 < u ^ 2)
    calc ∫ y, F (y, u) ∂μ = ∫ y in Ioi (0 : ℝ), ((y : ℂ) ^ (w - 1) *
          Complex.exp (-(((u ^ 2 : ℝ) : ℂ) * (y : ℂ)))) * (u : ℂ) ^ (-s) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
          simp only [hF]
          rw [Complex.ofReal_exp]
          push_cast
          ring_nf
      _ = (1 / ((u ^ 2 : ℝ) : ℂ)) ^ w * Complex.Gamma w * (u : ℂ) ^ (-s) := by
          rw [integral_mul_const, h]
      _ = _ := by
          rw [one_div_ofReal_sq_cpow hu0, mul_comm ((u : ℂ) ^ (-(2 * w))), mul_assoc,
            ← Complex.cpow_add _ _ hu1]
          ring_nf
  rw [hν, setIntegral_congr_fun measurableSet_Ioi hcol, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  have hden : -s - 2 * w + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hden' : s + 2 * w - 1 ≠ 0 := by
    intro h; apply hden; linear_combination -h
  rw [Complex.ofReal_one, Complex.one_cpow]
  field_simp
  ring

/-! ## The prime-minus-continuum gap -/

/-- The Gaussian prime current minus its continuum, `Σ Λ(n) n^{-s} e^{-yn²} − E(y, 1−s)`. -/
def gaussianPrimeContinuumGap (s : ℂ) (y : ℝ) : ℂ :=
  gaussianDampedPrimeSum s y - gaussianIncompleteMellin y (1 - s)

theorem logDeriv_gaussianFormation_eq_sub_gap {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (gaussianEulerContinuumFormation x) s =
      gaussianArchimedeanCurrent s - gaussianPrimeContinuumGap s (Real.pi * x) := by
  rw [logDeriv_gaussianEulerContinuumFormation hx hs,
    logDeriv_gaussianArchimedeanHalfFactor_eq_gammaReal hs, gaussianVonMangoldtCurrent_eq_tsum_term,
    gaussianContinuumCurrent_eq_incompleteMellin, gaussianArchimedeanCurrent,
    gaussianPrimeContinuumGap, gaussianDampedPrimeSum]
  ring

theorem norm_gaussianDampedPrimeSum_le {s : ℂ} (hs : 0 ≤ s.re) {y : ℝ} (hy : 1 ≤ y) :
    ‖gaussianDampedPrimeSum s y‖ ≤ Real.exp (-y) *
      ∑' n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ *
        Real.exp (1 - (n : ℝ) ^ 2) := by
  set a : ℕ → ℝ := fun n => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖
    with ha
  have hsum1 : Summable fun n => a n * Real.exp (1 - (n : ℝ) ^ 2) := by
    have h := (summable_norm_vonMangoldt_term_mul_gaussian hs one_pos).mul_left (Real.exp 1)
    refine h.congr fun n => ?_
    rw [show (1 : ℝ) - (n : ℝ) ^ 2 = 1 + -(1 * (n : ℝ) ^ 2) by ring, Real.exp_add]
    ring
  have hbound : ∀ n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
      (Real.exp (-(y * (n : ℝ) ^ 2)) : ℂ)‖ ≤
        Real.exp (-y) * (a n * Real.exp (1 - (n : ℝ) ^ 2)) := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [ha]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h
      have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have hexp : Real.exp (-(y * (n : ℝ) ^ 2)) ≤ Real.exp (-y) * Real.exp (1 - (n : ℝ) ^ 2) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        nlinarith [mul_nonneg (sub_nonneg.2 hy) (sub_nonneg.2 hn2)]
      calc a n * Real.exp (-(y * (n : ℝ) ^ 2)) ≤
            a n * (Real.exp (-y) * Real.exp (1 - (n : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = _ := by ring
  have hsn : Summable fun n => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
      (Real.exp (-(y * (n : ℝ) ^ 2)) : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound (hsum1.mul_left _)
  calc ‖gaussianDampedPrimeSum s y‖ ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
        (Real.exp (-(y * (n : ℝ) ^ 2)) : ℂ)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n, Real.exp (-y) * (a n * Real.exp (1 - (n : ℝ) ^ 2)) :=
        hsn.tsum_le_tsum hbound (hsum1.mul_left _)
    _ = _ := tsum_mul_left

/-- The gap decays faster than every power at `+∞`. -/
theorem gaussianPrimeContinuumGap_isBigO_atTop {s : ℂ} (hs : 0 < s.re) (A : ℝ) :
    gaussianPrimeContinuumGap s =O[atTop] (fun y : ℝ => y ^ (-A)) := by
  have hprime : gaussianDampedPrimeSum s =O[atTop] (fun y : ℝ => Real.exp (-1 * y)) := by
    refine IsBigO.of_bound (∑' n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      s n‖ * Real.exp (1 - (n : ℝ) ^ 2)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_one_mul, mul_comm]
    exact norm_gaussianDampedPrimeSum_le hs.le hy
  have hE : (fun y : ℝ => gaussianIncompleteMellin y (1 - s)) =O[atTop] (fun y : ℝ => y ^ (-A)) := by
    set B : ℝ := max A 1 with hB
    have hBA : A ≤ B := le_max_left _ _
    have hB1 : 1 ≤ B := le_max_right _ _
    have hr : -1 < 2 * B - 1 := by linarith
    have hG : 0 ≤ Real.Gamma ((2 * B - 1 + 1) / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
    refine IsBigO.of_bound ((1 / 2) * Real.Gamma ((2 * B - 1 + 1) / 2)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy0 : 0 < y := by linarith
    have h := norm_gaussianIncompleteMellin_le hy0 hr (b := 1 - s) (by simp; linarith)
    have hpow : y ^ (-(2 * B - 1 + 1) / 2) ≤ y ^ (-A) := by
      rw [show -(2 * B - 1 + 1) / 2 = -B by ring]
      exact Real.rpow_le_rpow_of_exponent_le hy (by linarith)
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy0 _)]
    calc ‖gaussianIncompleteMellin y (1 - s)‖ ≤
          y ^ (-(2 * B - 1 + 1) / 2) * (1 / 2) * Real.Gamma ((2 * B - 1 + 1) / 2) := h
      _ ≤ y ^ (-A) * (1 / 2) * Real.Gamma ((2 * B - 1 + 1) / 2) := by gcongr
      _ = _ := by ring
  have h := (hprime.trans (isLittleO_exp_neg_mul_rpow_atTop one_pos _).isBigO).sub hE
  exact h

theorem continuousOn_gaussianPrimeContinuumGap {s : ℂ} (hs : 0 < s.re) :
    ContinuousOn (gaussianPrimeContinuumGap s) (Ioi 0) := by
  have hcont : ∀ x₀ : ℝ, 0 < x₀ →
      ContinuousAt (fun x => logDeriv (gaussianEulerContinuumFormation x) s) x₀ := by
    intro x₀ hx₀
    rw [Metric.continuousAt_iff']
    intro ε hε
    filter_upwards [eventually_norm_logDeriv_gaussianFormation_sub_le hx₀ (half_pos hε)] with x hx
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hx.2 s hs) (half_lt_self hε)
  intro y hy
  have hy0 : (0 : ℝ) < y := hy
  have heq : ∀ y' : ℝ, 0 < y' → gaussianPrimeContinuumGap s y' =
      gaussianArchimedeanCurrent s -
        logDeriv (gaussianEulerContinuumFormation (y' / Real.pi)) s := by
    intro y' hy'
    rw [logDeriv_gaussianFormation_eq_sub_gap (div_pos hy' Real.pi_pos) hs,
      mul_div_cancel₀ _ Real.pi_ne_zero]
    ring
  have hca : ContinuousAt (fun y' : ℝ => gaussianArchimedeanCurrent s -
      logDeriv (gaussianEulerContinuumFormation (y' / Real.pi)) s) y :=
    continuousAt_const.sub ((hcont (y / Real.pi) (div_pos hy0 Real.pi_pos)).comp
      (f := fun y' : ℝ => y' / Real.pi) (continuousAt_id.div_const Real.pi))
  refine (hca.congr ?_).continuousWithinAt
  filter_upwards [Ioi_mem_nhds hy0] with y' hy'
  exact (heq y' hy').symm

theorem tendsto_div_pi_nhdsGT_zero :
    Tendsto (fun y : ℝ => y / Real.pi) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun y : ℝ => y / Real.pi) (𝓝 0) (𝓝 (0 / Real.pi)) :=
      (continuous_id.div_const Real.pi).tendsto 0
    rw [zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact div_pos hy Real.pi_pos

/-- A power bound on the passage at `s` transfers to the gap. -/
theorem gaussianPrimeContinuumGap_isBigO_nhdsGT {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 ≤ a)
    (hbd : (fun x : ℝ => logDeriv (gaussianEulerContinuumFormation x) s) =O[𝓝[>] 0]
      (fun x => x ^ (-a))) :
    gaussianPrimeContinuumGap s =O[𝓝[>] 0] (fun y : ℝ => y ^ (-a)) := by
  have h1 := hbd.comp_tendsto tendsto_div_pi_nhdsGT_zero
  have h2 : (fun y : ℝ => (y / Real.pi) ^ (-a)) =O[𝓝[>] 0] (fun y : ℝ => y ^ (-a)) := by
    refine IsBigO.of_bound (Real.pi ^ a) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    rw [Real.div_rpow hy0.le Real.pi_pos.le, Real.rpow_neg Real.pi_pos.le, div_inv_eq_mul,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (mul_pos (Real.rpow_pos_of_pos hy0 _) (Real.rpow_pos_of_pos Real.pi_pos _)),
      abs_of_pos (Real.rpow_pos_of_pos hy0 _), mul_comm]
  have h3 : (fun _ : ℝ => gaussianArchimedeanCurrent s) =O[𝓝[>] 0] (fun y : ℝ => y ^ (-a)) := by
    refine IsBigO.of_bound ‖gaussianArchimedeanCurrent s‖ ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy.1 _)]
    have h1y : 1 ≤ y ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy.1 hy.2.le (by linarith)
    nlinarith [norm_nonneg (gaussianArchimedeanCurrent s)]
  refine (h3.sub (h1.trans h2)).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [Function.comp]
  rw [logDeriv_gaussianFormation_eq_sub_gap (div_pos hy Real.pi_pos) hs,
    mul_div_cancel₀ _ Real.pi_ne_zero]
  ring

/-- Mellin transform of the gap: `Γ(w)(L(Λ, s+2w) − 1/(s+2w−1))`. -/
theorem mellin_gaussianPrimeContinuumGap {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 ≤ a)
    (hbot : gaussianPrimeContinuumGap s =O[𝓝[>] 0] (fun y : ℝ => y ^ (-a)))
    {w : ℂ} (hw : a < w.re) (hsw : 1 < s.re + 2 * w.re) :
    mellin (gaussianPrimeContinuumGap s) w =
      Complex.Gamma w * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + 2 * w) -
        (s + 2 * w - 1)⁻¹) := by
  have hw0 : 0 < w.re := lt_of_le_of_lt ha hw
  have hloc := (continuousOn_gaussianPrimeContinuumGap hs).locallyIntegrableOn (μ := volume)
    measurableSet_Ioi
  have hgap : MellinConvergent (gaussianPrimeContinuumGap s) w :=
    mellinConvergent_of_isBigO_rpow hloc (gaussianPrimeContinuumGap_isBigO_atTop hs (w.re + 1))
      (by linarith) hbot hw
  obtain ⟨hEconv, hEval⟩ := mellin_gaussianIncompleteMellin_one_sub hw0 hsw
  have hprime := mellin_gaussianDampedPrimeSum hs.le hw0 hsw
  have hsplit : mellin (gaussianDampedPrimeSum s) w = mellin (gaussianPrimeContinuumGap s) w +
      mellin (fun y : ℝ => gaussianIncompleteMellin y (1 - s)) w := by
    rw [mellin, mellin, mellin, ← integral_add hgap hEconv]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [gaussianPrimeContinuumGap, smul_eq_mul]
    ring
  rw [hprime, hEval, div_eq_mul_inv] at hsplit
  linear_combination -hsplit

theorem differentiableAt_gaussianArchimedeanCurrent {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ gaussianArchimedeanCurrent z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hG := GaloisForLFunctions.HTGeometry.analyticAt_Gammaℝ hz
  have hlog : DifferentiableAt ℂ (fun w => deriv Complex.Gammaℝ w / Complex.Gammaℝ w) z :=
    hG.deriv.differentiableAt.div hG.differentiableAt (Complex.Gammaℝ_ne_zero_of_re_pos hz)
  have h : gaussianArchimedeanCurrent = fun w => w⁻¹ + deriv Complex.Gammaℝ w / Complex.Gammaℝ w := by
    funext w; rw [gaussianArchimedeanCurrent, logDeriv_apply]
  rw [h]
  exact (differentiableAt_inv hz0).add hlog

private theorem xi_eventually_ne_zero_punctured (ρ : ℂ) : ∀ᶠ s in 𝓝[≠] ρ, xi s ≠ 0 := by
  rcases (xi_differentiable.analyticAt ρ).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hxiA : AnalyticOnNhd ℂ xi univ := fun z _ => xi_differentiable.analyticAt z
    have hEq := hxiA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ ρ) (show xi =ᶠ[𝓝 ρ] 0 from h)
    exact xi_ne_zero_of_one_le_re (show (1 : ℝ) ≤ (2 : ℂ).re by norm_num) (hEq (mem_univ 2))
  · exact h

/-! ## The single-point passage law -/

/-- **Continuation of `ξ'/ξ` forbids zeros.**  If `ξ'(s + 2w) = ξ(s + 2w) K(w)` whenever `Re w > R`,
with `K` holomorphic on the half-plane `Re w > a` (`a ≤ R`), then `ξ` has no zero with
`Re z > Re s + 2a`: the identity extends to the whole half-plane, and at a zero of order `n ≥ 1`
the residue `(u − z)ξ'/ξ(u) → n` would have to vanish. -/
theorem xi_ne_zero_of_deriv_eq_mul_holomorphic {s : ℂ} {a R : ℝ} {K : ℂ → ℂ}
    (hKd : DifferentiableOn ℂ K {w : ℂ | a < w.re}) (haR : a ≤ R)
    (hfar : ∀ w : ℂ, R < w.re → deriv xi (s + 2 * w) = xi (s + 2 * w) * K w)
    {z : ℂ} (hz : s.re + 2 * a < z.re) : xi z ≠ 0 := by
  set U : Set ℂ := {w : ℂ | a < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hanaL : AnalyticOnNhd ℂ (fun w => deriv xi (s + 2 * w)) U := fun w _ =>
    ((xi_differentiable.analyticAt _).deriv).comp
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
  have hanaR : AnalyticOnNhd ℂ (fun w => xi (s + 2 * w) * K w) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    exact ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun w : ℂ => s + 2 * w)).differentiableOn).mul hKd
  set w₁ : ℂ := ((R + 1 : ℝ) : ℂ) with hw₁
  have hw₁U : w₁ ∈ U := by
    show a < w₁.re
    rw [hw₁, Complex.ofReal_re]
    linarith
  have hev : (fun w => deriv xi (s + 2 * w)) =ᶠ[𝓝 w₁] (fun w => xi (s + 2 * w) * K w) := by
    have hopen : IsOpen {w : ℂ | R < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show R < w₁.re by rw [hw₁, Complex.ofReal_re]; linarith)] with w hw
    exact hfar w hw
  have hid := hanaL.eqOn_of_preconnected_of_eventuallyEq hanaR
    (convex_halfSpace_re_gt a).isPreconnected hw₁U hev
  intro hxz
  set w₀ : ℂ := (z - s) / 2 with hw₀def
  have hw₀ : w₀ ∈ U := by
    show a < w₀.re
    rw [hw₀def]; simp; linarith
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (xi_order_ne_top z)
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn
    exact (analyticOrderAt_ne_zero.2 ⟨xi_differentiable.analyticAt z, hxz⟩) (by rw [← hn]; rfl)
  have hres := GaloisForLFunctions.HTGeometry.tendsto_sub_mul_logDeriv_of_analyticOrderAt
    (xi_differentiable.analyticAt z) hn.symm
  have hKc : ContinuousAt (fun u => K ((u - s) / 2)) z := by
    have hKw₀ : ContinuousAt K w₀ := (hKd.differentiableAt (hUo.mem_nhds hw₀)).continuousAt
    exact hKw₀.comp (f := fun u : ℂ => (u - s) / 2) (by fun_prop)
  have hlim0 : Tendsto (fun u => (u - z) * logDeriv xi u) (𝓝[≠] z) (𝓝 0) := by
    have h1 : Tendsto (fun u => (u - z) * K ((u - s) / 2)) (𝓝 z) (𝓝 ((z - z) * K ((z - s) / 2))) :=
      ((continuous_id.sub continuous_const).continuousAt.tendsto).mul hKc.tendsto
    rw [sub_self, zero_mul] at h1
    refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
    have hUz : ∀ᶠ u in 𝓝 z, (u - s) / 2 ∈ U :=
      (by fun_prop : Continuous fun u : ℂ => (u - s) / 2).continuousAt.preimage_mem_nhds
        (hUo.mem_nhds hw₀)
    filter_upwards [xi_eventually_ne_zero_punctured z, nhdsWithin_le_nhds hUz] with u hu hUu
    have h := hid hUu
    simp only at h
    rw [show s + 2 * ((u - s) / 2) = u by ring] at h
    rw [logDeriv_apply, h]
    field_simp
  have heq := tendsto_nhds_unique hres hlim0
  exact hn0 (by exact_mod_cast heq)

/-- **Single-point passage law.**  If the Gaussian passage at one point `s` (`Re s > 0`) grows at
most like `x^{-a}` as `x → 0⁺` (`a ≥ 0`), then `ξ` has no zero with `Re z > Re s + 2a`.

The Mellin transform in the damping variable `y = πx` of the prime-minus-continuum gap is
`Γ(w)(Σ Λ(n) n^{-(s+2w)} − 1/(s+2w−1)) = Γ(w)(A(s+2w) − ξ'/ξ(s+2w))`.  The growth bound makes it
holomorphic on `Re w > a`, so `ξ'/ξ(s + 2w)` continues holomorphically there; a zero of `ξ` would be
a pole of its logarithmic derivative. -/
theorem xi_ne_zero_of_isBigO_gaussianPassage {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 ≤ a)
    (hbd : (fun x : ℝ => logDeriv (gaussianEulerContinuumFormation x) s) =O[𝓝[>] 0]
      (fun x => x ^ (-a))) {z : ℂ} (hz : s.re + 2 * a < z.re) : xi z ≠ 0 := by
  have hbot := gaussianPrimeContinuumGap_isBigO_nhdsGT hs ha hbd
  set M : ℂ → ℂ := mellin (gaussianPrimeContinuumGap s) with hM
  set U : Set ℂ := {w : ℂ | a < w.re} with hU
  have hloc := (continuousOn_gaussianPrimeContinuumGap hs).locallyIntegrableOn (μ := volume)
    measurableSet_Ioi
  have hMd : ∀ w ∈ U, DifferentiableAt ℂ M w := fun w hw =>
    mellin_differentiableAt_of_isBigO_rpow hloc (gaussianPrimeContinuumGap_isBigO_atTop hs (w.re + 1))
      (by linarith) hbot hw
  set K : ℂ → ℂ := fun w => gaussianArchimedeanCurrent (s + 2 * w) - M w * (Complex.Gamma w)⁻¹
    with hK
  have hKd : DifferentiableOn ℂ K U := by
    intro w hw
    have hw' : a < w.re := hw
    have hre : 0 < (s + 2 * w).re := by simp; linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub ?_ ((hMd w hw).mul (Complex.differentiable_one_div_Gamma w))
    exact (differentiableAt_gaussianArchimedeanCurrent hre).comp (f := fun w : ℂ => s + 2 * w) w
      (by fun_prop)
  set R : ℝ := max a ((1 - s.re) / 2) + 1 with hR
  have hfar : ∀ w : ℂ, R < w.re → deriv xi (s + 2 * w) = xi (s + 2 * w) * K w := by
    intro w hw
    have hwa : a < w.re := by have := le_max_left a ((1 - s.re) / 2); linarith
    have hw0 : 0 < w.re := by linarith
    have hsw : 1 < s.re + 2 * w.re := by have := le_max_right a ((1 - s.re) / 2); linarith
    have hz1 : 1 < (s + 2 * w).re := by simp; linarith
    have hxi : xi (s + 2 * w) ≠ 0 := xi_ne_zero_of_one_lt_re hz1
    have hMw : M w = Complex.Gamma w *
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + 2 * w) -
          (s + 2 * w - 1)⁻¹) := mellin_gaussianPrimeContinuumGap hs ha hbot hwa hsw
    have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw0
    have hz1' : s + 2 * w - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hKw : K w = logDeriv xi (s + 2 * w) := by
      simp only [hK]
      rw [hMw, logDeriv_xi_eq_arithmetic hz1, gaussianArchimedeanCurrent]
      field_simp
      ring
    rw [hKw, logDeriv_apply]
    field_simp
  exact xi_ne_zero_of_deriv_eq_mul_holomorphic hKd
    (by have := le_max_left a ((1 - s.re) / 2); linarith) hfar hz

/-- Bounded passage at one point forces the zero-free half-plane to its right. -/
theorem xi_ne_zero_of_gaussianPassage_isBigO_one {s : ℂ} (hs : 0 < s.re)
    (hbd : (fun x : ℝ => logDeriv (gaussianEulerContinuumFormation x) s) =O[𝓝[>] 0]
      (fun _ => (1 : ℝ))) {z : ℂ} (hz : s.re < z.re) : xi z ≠ 0 := by
  have h1 : (fun x : ℝ => x ^ (-(0 : ℝ))) = fun _ => (1 : ℝ) := by
    funext x; simp
  refine xi_ne_zero_of_isBigO_gaussianPassage hs le_rfl (by rw [h1]; exact hbd) (by linarith)

/-- **Abscissa law of the Gaussian passage.**  Every zero of `ξ` has `Re ρ ≤ θ` iff the passage is
bounded as `x → 0⁺` at every real point `σ` with `max θ 0 < σ < 2`. -/
theorem xi_zero_re_le_iff_gaussianPassage_bounded {θ : ℝ} :
    (∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) ↔
      ∀ σ : ℝ, θ < σ → 0 < σ → σ < 2 →
        (fun x : ℝ => logDeriv (gaussianEulerContinuumFormation x) (σ : ℂ)) =O[𝓝[>] 0]
          (fun _ => (1 : ℝ)) := by
  constructor
  · intro hθ σ hσ hσ0 hσ2
    exact (tendsto_logDeriv_gaussianFormation_of_zeroFree hθ (by simpa using hσ0)
      (by simpa using hσ) (by simpa using hσ2)).isBigO_one ℝ
  · intro h ρ hρ
    by_contra hlt
    push Not at hlt
    have hρ0 := xi_zero_re_pos hρ
    have hρ1 : ρ.re < 1 := by
      by_contra h1; push Not at h1; exact xi_ne_zero_of_one_le_re h1 hρ
    set m : ℝ := max θ 0 with hm
    have hmρ : m < ρ.re := max_lt hlt hρ0
    set σ : ℝ := (m + ρ.re) / 2 with hσ
    have hσθ : θ < σ := by have := le_max_left θ 0; linarith
    have hσ0 : 0 < σ := by have := le_max_right θ 0; linarith
    have hσ2 : σ < 2 := by linarith
    exact xi_ne_zero_of_gaussianPassage_isBigO_one (s := (σ : ℂ)) (by simpa using hσ0)
      (h σ hσθ hσ0 hσ2) (by simp; linarith) hρ

/-- **RH as a single-point boundedness law.**  RH holds iff for every real `σ ∈ (½, 2)` the Gaussian
passage `Φₓ'/Φₓ(σ)` stays bounded as `x → 0⁺`. -/
theorem riemannHypothesis_iff_gaussianPassage_bounded :
    RiemannHypothesis ↔
      ∀ σ : ℝ, 1 / 2 < σ → σ < 2 →
        (fun x : ℝ => logDeriv (gaussianEulerContinuumFormation x) (σ : ℂ)) =O[𝓝[>] 0]
          (fun _ => (1 : ℝ)) := by
  rw [rh_iff_xi_ne_zero_right]
  constructor
  · intro h σ hσ hσ2
    have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ 1 / 2 := by
      intro ρ hρ
      by_contra hlt
      push Not at hlt
      exact h ρ (mem_rightHalf.mpr hlt) hρ
    exact xi_zero_re_le_iff_gaussianPassage_bounded.1 hθ σ hσ (by linarith) hσ2
  · intro h s hs
    have hθ := xi_zero_re_le_iff_gaussianPassage_bounded.2
      (fun σ hσ _ hσ2 => h σ hσ hσ2)
    intro hzero
    have := hθ s hzero
    rw [mem_rightHalf] at hs
    linarith

end

end RHTower
