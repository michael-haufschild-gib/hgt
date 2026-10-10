import GaloisForLFunctions.RHTower.FiniteOffLineLandau

/-!
# Finitely many off-line zeros is exactly a finite-wave law for `ψ`

For a finite set `S` of zero copies let `W_S(x) = Σ_{q ∈ S} x^q/q` and `E_S(x) = ψ(x) − x + Re W_S(x)`.

**Converse of the finite off-line von Koch law** (`re_le_half_add_of_chebyshevPsi_sub_add_offLineWave_ge`).
If `E_S(t) ≥ −C t^{½+a}` for `t ≥ x₁`, with `0 < a < ½`, then every zero copy whose pole `ρ − ½` is
not one of the finitely many points `ρ_q − ½`, `conj ρ_q − ½` (`q ∈ S`) has real part at most `½ + a`.

**Corollary** (`finite_offLine_iff_exists_offLineWave`). The off-line zero copies are finite iff
`|ψ(x) − x + Re W_S(x)| ≤ K √x log²x` for some finite `S` and all `x ≥ 16`.

**Proof.** With `w_q = 1/(ρ(1−ρ))` and `p_q = ρ − ½`,
`Φ_S(u) = Φ(u) − Re Σ_S w_q e^{u p_q}` satisfies `Φ_S(log x)√x = −x∫_x^∞ E_S(t) t^{−2} dt − log 2π + S(x)`
since `x∫_x^∞ t^{ρ−2} dt/ρ = w_q x^ρ`. A lower bound on `E_S` gives `Φ_S(u) ≤ M e^{au}`. The Laplace
transform of `Φ_S` is `G − R_S` with `R_S(s) = ½Σ_S (w_q/(s − p_q) + conj w_q/(s − conj p_q))`, which
is analytic at every real `t > 0`. Landau's theorem continues `G − R_S` to `Re s > a`, and the
tilted-ray argument places every pole of `G` off the finite set to the left of `½ + a`.
-/

open Complex Filter Topology MeasureTheory Set ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The subtracted lag function and its Laplace transform -/

/-- The off-line lag wave `Re Σ_{q ∈ S} w_q e^{u(ρ_q − ½)}`. -/
def offLineLagWave (S : Finset XiZeroCopy) (u : ℝ) : ℝ :=
  (∑ q ∈ S, lagWeight q * Complex.exp (u * lagPole q)).re

/-- The subtracted lag function `Φ_S = Φ − Re Σ_{q ∈ S} w_q e^{u(ρ_q − ½)}`. -/
def subtractedLag (S : Finset XiZeroCopy) (u : ℝ) : ℝ :=
  weilLagFunctionReal u - offLineLagWave S u

/-- The subtracted poles `R_S(s) = ½ Σ_{q ∈ S} (w_q/(s − p_q) + conj w_q/(s − conj p_q))`. -/
def offLinePoleSum (S : Finset XiZeroCopy) (s : ℂ) : ℂ :=
  ∑ q ∈ S, (lagWeight q / (s - lagPole q) + conj (lagWeight q) / (s - conj (lagPole q))) / 2

/-- The finite pole set `{p_q, conj p_q : q ∈ S}`. -/
def offLinePoles (S : Finset XiZeroCopy) : Set ℂ :=
  (lagPole '' (S : Set XiZeroCopy)) ∪ ((fun q => conj (lagPole q)) '' (S : Set XiZeroCopy))

theorem offLinePoles_finite (S : Finset XiZeroCopy) : (offLinePoles S).Finite :=
  (S.finite_toSet.image _).union (S.finite_toSet.image _)

theorem continuous_offLineLagWave (S : Finset XiZeroCopy) : Continuous (offLineLagWave S) :=
  Complex.continuous_re.comp (continuous_finset_sum _ fun q _ =>
    continuous_const.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)))

theorem measurable_subtractedLag (S : Finset XiZeroCopy) : Measurable (subtractedLag S) :=
  measurable_weilLagFunctionReal.sub (continuous_offLineLagWave S).measurable

theorem abs_offLineLagWave_le (S : Finset XiZeroCopy) {u : ℝ} (hu : 0 ≤ u) :
    |offLineLagWave S u| ≤ (∑ q ∈ S, ‖lagWeight q‖) * Real.exp (u / 2) := by
  unfold offLineLagWave
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [norm_mul, Complex.norm_exp]
  gcongr
  have : ((u : ℂ) * lagPole q).re = u * (lagPole q).re := by simp [Complex.mul_re]
  rw [this]
  nlinarith [lagPole_re_lt_half q]

theorem abs_subtractedLag_le (S : Finset XiZeroCopy) {u : ℝ} (hu : 0 < u) :
    |subtractedLag S u| ≤ (lagWeightTotal + ∑ q ∈ S, ‖lagWeight q‖) * Real.exp (u / 2) := by
  unfold subtractedLag
  have h1 := abs_weilLagFunctionReal_le u
  rw [abs_of_pos hu] at h1
  have h2 := abs_offLineLagWave_le S hu.le
  calc |weilLagFunctionReal u - offLineLagWave S u|
      ≤ |weilLagFunctionReal u| + |offLineLagWave S u| := abs_sub _ _
    _ ≤ _ := by nlinarith

theorem integrableOn_cexp_neg_mul_ofReal_Ioi {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (Ioi 0) := by
  have hc : Continuous (fun u : ℝ => Complex.exp (-z * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  exact (exp_neg_integrableOn_Ioi 0 hz).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))

theorem ofReal_offLineLagWave_mul_cexp (S : Finset XiZeroCopy) (s : ℂ) (u : ℝ) :
    (offLineLagWave S u : ℂ) * Complex.exp (-s * u) =
      ∑ q ∈ S, (lagWeight q * Complex.exp (-(s - lagPole q) * u) +
        conj (lagWeight q) * Complex.exp (-(s - conj (lagPole q)) * u)) / 2 := by
  unfold offLineLagWave
  rw [Complex.re_eq_add_conj, map_sum, ← Finset.sum_add_distrib, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  have e1 : Complex.exp (-(s - lagPole q) * u) =
      Complex.exp (u * lagPole q) * Complex.exp (-s * u) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (-(s - conj (lagPole q)) * u) =
      Complex.exp (u * conj (lagPole q)) * Complex.exp (-s * u) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2]
  ring

/-- The Laplace transform of the off-line lag wave is `R_S`. -/
theorem integral_offLineLagWave_mul_cexp (S : Finset XiZeroCopy) {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ u in Ioi (0:ℝ), (offLineLagWave S u : ℂ) * Complex.exp (-s * u) = offLinePoleSum S s := by
  have h1 : ∀ q : XiZeroCopy, 0 < (s - lagPole q).re := fun q => by
    simp only [Complex.sub_re]; linarith [lagPole_re_lt_half q]
  have h2 : ∀ q : XiZeroCopy, 0 < (s - conj (lagPole q)).re := fun q => by
    simp only [Complex.sub_re, Complex.conj_re]; linarith [lagPole_re_lt_half q]
  have hint : ∀ q : XiZeroCopy, IntegrableOn (fun u : ℝ =>
      (lagWeight q * Complex.exp (-(s - lagPole q) * u) +
        conj (lagWeight q) * Complex.exp (-(s - conj (lagPole q)) * u)) / 2) (Ioi 0) := fun q =>
    (((integrableOn_cexp_neg_mul_ofReal_Ioi (h1 q)).const_mul _).add
      ((integrableOn_cexp_neg_mul_ofReal_Ioi (h2 q)).const_mul _)).div_const _
  have hfun : (fun u : ℝ => (offLineLagWave S u : ℂ) * Complex.exp (-s * u)) =
      fun u : ℝ => ∑ q ∈ S, (lagWeight q * Complex.exp (-(s - lagPole q) * u) +
        conj (lagWeight q) * Complex.exp (-(s - conj (lagPole q)) * u)) / 2 :=
    funext (ofReal_offLineLagWave_mul_cexp S s)
  rw [hfun, integral_finsetSum (f := fun q (u : ℝ) =>
    (lagWeight q * Complex.exp (-(s - lagPole q) * u) +
      conj (lagWeight q) * Complex.exp (-(s - conj (lagPole q)) * u)) / 2) S fun q _ => hint q]
  unfold offLinePoleSum
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_div, integral_add ((integrableOn_cexp_neg_mul_ofReal_Ioi (h1 q)).const_mul _)
    ((integrableOn_cexp_neg_mul_ofReal_Ioi (h2 q)).const_mul _), integral_const_mul, integral_const_mul,
    integral_cexp_neg_mul_Ioi (h1 q), integral_cexp_neg_mul_Ioi (h2 q)]
  ring

theorem integrableOn_offLineLagWave_mul_cexp (S : Finset XiZeroCopy) {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun u : ℝ => (offLineLagWave S u : ℂ) * Complex.exp (-s * u)) (Ioi 0) :=
  integrable_ofReal_mul_cexp (continuous_offLineLagWave S).measurable
    (fun u hu => abs_offLineLagWave_le S hu.le) hs

/-- The Laplace transform of `Φ_S` on `Re s > ½` is `G − R_S`. -/
theorem integral_subtractedLag_mul_cexp (S : Finset XiZeroCopy) {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ u in Ioi (0:ℝ), (subtractedLag S u : ℂ) * Complex.exp (-s * u) =
      lagPoleSeries s - offLinePoleSum S s := by
  have hΦ : ∫ u in Ioi (0:ℝ), (weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ)) =
      lagPoleSeries s := by
    rw [← integral_weilLagFunction_mul_cexp hs]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      beta_reduce; rw [weilLagFunction_eq_ofReal])
  have hpt : ∀ u : ℝ, (subtractedLag S u : ℂ) * Complex.exp (-s * u) =
      (weilLagFunctionReal u : ℂ) * Complex.exp (-s * u) -
        (offLineLagWave S u : ℂ) * Complex.exp (-s * u) := fun u => by
    unfold subtractedLag; push_cast; ring
  simp_rw [hpt]
  rw [integral_sub (integrable_weilLag_mul_cexp hs) (integrableOn_offLineLagWave_mul_cexp S hs),
    hΦ, integral_offLineLagWave_mul_cexp S hs]

theorem differentiableAt_offLinePoleSum (S : Finset XiZeroCopy) {z : ℂ} (hz : z ∉ offLinePoles S) :
    DifferentiableAt ℂ (offLinePoleSum S) z := by
  have hp : ∀ q ∈ S, z - lagPole q ≠ 0 := fun q hq h =>
    hz (Or.inl ⟨q, hq, (sub_eq_zero.mp h).symm⟩)
  have hc : ∀ q ∈ S, z - conj (lagPole q) ≠ 0 := fun q hq h =>
    hz (Or.inr ⟨q, hq, (sub_eq_zero.mp h).symm⟩)
  have hd : ∀ c p : ℂ, z - p ≠ 0 → DifferentiableAt ℂ (fun s : ℂ => c / (s - p)) z :=
    fun c p h => (differentiableAt_const c).div (differentiableAt_id.sub_const p) h
  unfold offLinePoleSum
  exact DifferentiableAt.fun_sum fun q hq =>
    ((hd _ _ (hp q hq)).add (hd _ _ (hc q hq))).div_const _

/-- No positive real number is a subtracted pole. -/
theorem ofReal_notMem_offLinePoles (S : Finset XiZeroCopy) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ∉ offLinePoles S := by
  have hne : ∀ q : XiZeroCopy, lagPole q ≠ t := fun q h =>
    xi_ofReal_add_half_ne_zero ht (by rw [← h, lagPole_add_half]; exact xi_xiZeroCopy_eq_zero q)
  rintro (⟨q, _, hq⟩ | ⟨q, _, hq⟩)
  · exact hne q hq
  · apply hne q
    have := congrArg conj hq
    rwa [Complex.conj_conj, Complex.conj_ofReal] at this

theorem analyticAt_lagPoleSeries_sub_offLinePoleSum (S : Finset XiZeroCopy) {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℂ (fun s => lagPoleSeries s - offLinePoleSum S s) (t : ℂ) := by
  have hopen : IsOpen (offLinePoles S)ᶜ := (offLinePoles_finite S).isClosed.isOpen_compl
  have hdiff : DifferentiableOn ℂ (offLinePoleSum S) (offLinePoles S)ᶜ := fun z hz =>
    (differentiableAt_offLinePoleSum S hz).differentiableWithinAt
  have hR : AnalyticAt ℂ (offLinePoleSum S) (t : ℂ) :=
    hdiff.analyticAt (hopen.mem_nhds (ofReal_notMem_offLinePoles S ht))
  exact (analyticAt_lagPoleSeries (xi_ofReal_add_half_ne_zero ht)).sub hR

/-! ## Landau with the subtracted poles -/

/-- **A one-sided exponential bound on `Φ_S` bounds the real parts of the zeros off the subtracted
poles.** -/
theorem re_le_half_add_of_subtractedLag_le_exp (S : Finset XiZeroCopy) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1 / 2) (hM : ∀ u, 0 ≤ u → subtractedLag S u ≤ M * Real.exp (a * u))
    (q : XiZeroCopy) (hq : lagPole q ∉ offLinePoles S) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  obtain ⟨F, hFd, hFΛ⟩ := exists_differentiable_extension_of_le_exp (measurable_subtractedLag S)
    (fun u hu => abs_subtractedLag_le S hu) ha0 ha hM
    (fun t ht => analyticAt_lagPoleSeries_sub_offLinePoleSum S (lt_of_le_of_lt ha0 ht))
    (fun s hs => integral_subtractedLag_mul_cexp S hs)
  refine re_le_half_add_of_lagPoleSeries_sub_extension ha0 (offLinePoles_finite S)
    (fun z hz _ => hFd z hz) (fun z hz => differentiableAt_offLinePoleSum S hz)
    (fun s hs _ => ?_) q hq
  rw [hFΛ s hs]
  ring


/-! ## The wave through the Chebyshev tail -/

theorem integral_Ioi_cpow_div_div_sq (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) / ((t : ℂ) ^ 2)) (Ioi x) ∧
      ∫ t in Ioi x, (t : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) / ((t : ℂ) ^ 2) =
        -(x : ℂ) ^ ((q.1 : ℂ) - 1) / (((q.1 : ℂ) - 1) * (q.1 : ℂ)) := by
  set ρ : ℂ := (q.1 : ℂ) with hρ
  have hre : (ρ - 2).re < -1 := by
    simp only [Complex.sub_re]; norm_num; linarith [xiZeroCopy_re_lt_one q]
  have heq : EqOn (fun t : ℝ => (t : ℂ) ^ ρ / ρ / ((t : ℂ) ^ 2))
      (fun t : ℝ => (t : ℂ) ^ (ρ - 2) * ρ⁻¹) (Ioi x) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [mem_Ioi.mp ht])
    simp only
    rw [Complex.cpow_sub _ _ ht0, Complex.cpow_two]
    ring
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (ρ - 2) * ρ⁻¹) (Ioi x) :=
    (integrableOn_Ioi_cpow_of_lt hre hx).mul_const _
  refine ⟨hint.congr_fun heq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_mul_const,
    integral_Ioi_cpow_of_lt hre hx, show ρ - 2 + 1 = ρ - 1 by ring]
  have hρ0 : ρ ≠ 0 := xiZeroCopy_ne_zero q
  have hρ1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr (xiZeroCopy_ne_one q)
  field_simp

/-- `x · (−x^{ρ−1}/((ρ−1)ρ)) = √x · w_q e^{(log x)(ρ − ½)}`. -/
theorem ofReal_mul_neg_cpow_eq (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * (-(x : ℂ) ^ ((q.1 : ℂ) - 1) / (((q.1 : ℂ) - 1) * (q.1 : ℂ))) =
      (Real.sqrt x : ℂ) * (lagWeight q * Complex.exp ((Real.log x : ℂ) * lagPole q)) := by
  set ρ : ℂ := (q.1 : ℂ) with hρ
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hρ0 : ρ ≠ 0 := xiZeroCopy_ne_zero q
  have hρ1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr (xiZeroCopy_ne_one q)
  have hρ1' : 1 - ρ ≠ 0 := xiZeroCopy_one_sub_ne_zero q
  have hpow : (x : ℂ) ^ (ρ - 1) = Complex.exp ((Real.log x : ℂ) * ρ) / x := by
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one, Complex.cpow_def_of_ne_zero hx0,
      ← Complex.ofReal_log hx.le]
  have hsq : Real.sqrt x = Real.exp (Real.log x / 2) := by rw [Real.exp_half, Real.exp_log hx]
  have hsqrt : (Real.sqrt x : ℂ) = Complex.exp ((Real.log x : ℂ) / 2) := by
    rw [hsq, Complex.ofReal_exp]; push_cast; ring_nf
  have hexp : Complex.exp ((Real.log x : ℂ) / 2) * Complex.exp ((Real.log x : ℂ) * lagPole q) =
      Complex.exp ((Real.log x : ℂ) * ρ) := by
    rw [← Complex.exp_add]; congr 1; unfold lagPole; rw [← hρ]; ring
  rw [hpow, hsqrt, mul_left_comm, hexp]
  unfold lagWeight
  rw [← hρ]
  field_simp
  ring

/-- `x ∫_x^∞ Re W_S(t) t^{−2} dt = √x · Re Σ_S w_q e^{(log x)(ρ_q − ½)}`. -/
theorem mul_integral_offLineWave_re_div_sq (S : Finset XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (offLineWave S t).re / t ^ 2) (Ioi x) ∧
      x * ∫ t in Ioi x, (offLineWave S t).re / t ^ 2 =
        Real.sqrt x * offLineLagWave S (Real.log x) := by
  have hpt : ∀ t : ℝ, (offLineWave S t).re / t ^ 2 =
      RCLike.re (∑ q ∈ S, (t : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) / ((t : ℂ) ^ 2)) := by
    intro t
    rw [← Finset.sum_div, RCLike.re_to_complex]
    unfold offLineWave
    rw [show ((t : ℂ) ^ 2) = ((t ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
  have hint : ∀ q ∈ S, Integrable (fun t : ℝ => (t : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) / ((t : ℂ) ^ 2))
      (volume.restrict (Ioi x)) := fun q _ => (integral_Ioi_cpow_div_div_sq q hx).1
  have hsum := integrable_finsetSum S hint
  refine ⟨hsum.re.congr_fun (fun t _ => (hpt t).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t), integral_re hsum,
    integral_finsetSum S hint, RCLike.re_to_complex,
    Finset.sum_congr rfl fun q _ => (integral_Ioi_cpow_div_div_sq q hx).2]
  have hc : (x : ℂ) * ∑ q ∈ S, -(x : ℂ) ^ ((q.1 : ℂ) - 1) / (((q.1 : ℂ) - 1) * (q.1 : ℂ)) =
      (Real.sqrt x : ℂ) * ∑ q ∈ S, lagWeight q * Complex.exp ((Real.log x : ℂ) * lagPole q) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => ofReal_mul_neg_cpow_eq q hx
  have := congrArg Complex.re hc
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul] at this
  unfold offLineLagWave
  exact this

/-- **The subtracted lag function as a Chebyshev tail.**
`Φ_S(log x)√x = −x∫_x^∞ E_S(t) t^{−2} dt − log 2π + S(x)` with `E_S = ψ − t + Re W_S`. -/
theorem subtractedLag_log_mul_sqrt (S : Finset XiZeroCopy) {x : ℝ} (hx : 1 < x) :
    subtractedLag S (Real.log x) * Real.sqrt x =
      -(x * ∫ t in Ioi x, (chebyshevError t + (offLineWave S t).re) / t ^ 2)
        - Real.log (2 * Real.pi) + trivialZeroSeriesReal x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hWint, hW⟩ := mul_integral_offLineWave_re_div_sq S hx0
  have hEint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi x) :=
    integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi hx.le)
  have hsplit : ∫ t in Ioi x, (chebyshevError t + (offLineWave S t).re) / t ^ 2 =
      (∫ t in Ioi x, chebyshevError t / t ^ 2) + ∫ t in Ioi x, (offLineWave S t).re / t ^ 2 := by
    rw [← integral_add hEint hWint]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => add_div _ _ _)
  rw [hsplit, mul_add, hW]
  unfold subtractedLag
  rw [sub_mul, weilLagFunctionReal_log_mul_sqrt hx]
  ring

/-- **A lower power bound on `E_S` bounds `Φ_S` above by `M e^{au}`.** -/
theorem exists_subtractedLag_le_exp_of_ge_rpow (S : Finset XiZeroCopy) {C a x₁ : ℝ} (hC : 0 ≤ C)
    (ha0 : 0 < a) (ha : a < 1 / 2) (hx₁1 : 1 < x₁)
    (hpow : ∀ t, x₁ ≤ t → -(C * t ^ (1 / 2 + a)) ≤ chebyshevError t + (offLineWave S t).re) :
    ∃ M : ℝ, ∀ u, 0 ≤ u → subtractedLag S u ≤ M * Real.exp (a * u) := by
  have htail : ∀ x, x₁ ≤ x → -(C * (x ^ (a - 1 / 2) / (1 / 2 - a))) ≤
      ∫ t in Ioi x, (chebyshevError t + (offLineWave S t).re) / t ^ 2 := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hint : IntegrableOn (fun t : ℝ => (chebyshevError t + (offLineWave S t).re) / t ^ 2)
        (Ioi x) := by
      have h1 : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi x) :=
        integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi (by linarith))
      exact (h1.add (mul_integral_offLineWave_re_div_sq S hx0).1).congr_fun
        (fun t _ => (add_div _ _ _).symm) measurableSet_Ioi
    have hint2 : IntegrableOn (fun t : ℝ => -(C) * t ^ (a - 3 / 2)) (Ioi x) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hx0).const_mul _
    have hmono := setIntegral_mono_on hint2 hint measurableSet_Ioi (fun t ht => by
      have ht0 : 0 < t := lt_trans hx0 ht
      have h1 := hpow t (le_trans hx (le_of_lt ht))
      have h2 : -(C) * t ^ (a - 3 / 2) = -(C * t ^ (1 / 2 + a)) / t ^ 2 := by
        rw [show a - 3 / 2 = (1 / 2 + a) - 2 by ring, Real.rpow_sub ht0, Real.rpow_two]
        ring
      rw [h2]
      exact div_le_div_of_nonneg_right h1 (by positivity))
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx0,
      show a - 3 / 2 + 1 = a - 1 / 2 by ring] at hmono
    have hd : -x ^ (a - 1 / 2) / (a - 1 / 2) = x ^ (a - 1 / 2) / (1 / 2 - a) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    have hneg : -(C) * (-x ^ (a - 1 / 2) / (a - 1 / 2))
        = -(C * (x ^ (a - 1 / 2) / (1 / 2 - a))) := by
      rw [hd]; ring
    linarith
  set K₁ := C / (1 / 2 - a) + 1 with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    have : 0 ≤ C / (1 / 2 - a) := div_nonneg hC (by linarith)
    linarith
  have hlarge : ∀ L, Real.log x₁ ≤ L → subtractedLag S L ≤ K₁ * Real.exp (a * L) := by
    intro L hL
    have hx1L : x₁ ≤ Real.exp L := by
      rw [← Real.exp_log (show 0 < x₁ by linarith)]; exact Real.exp_le_exp.mpr hL
    set x := Real.exp L with hxdef
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    have hlogx : Real.log x = L := by rw [hxdef, Real.log_exp]
    have hid := subtractedLag_log_mul_sqrt S hx1
    rw [hlogx] at hid
    have ht := htail x hx1L
    have hS := trivialZeroSeriesReal_le_one hx1.le
    have hl := one_lt_log_two_pi
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hxa : x ^ a = Real.exp (a * L) := by
      rw [hxdef, ← Real.exp_mul]; ring_nf
    have hxa' : x * x ^ (a - 1 / 2) = Real.sqrt x * x ^ a := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx0.le (by linarith), ← Real.rpow_add hx0]
      ring_nf
    have h1 : subtractedLag S L * Real.sqrt x
        ≤ C * (x * x ^ (a - 1 / 2)) / (1 / 2 - a) + 1 := by
      have hxI := mul_le_mul_of_nonneg_left ht hx0.le
      have : x * (C * (x ^ (a - 1 / 2) / (1 / 2 - a)))
          = C * (x * x ^ (a - 1 / 2)) / (1 / 2 - a) := by ring
      linarith
    rw [hxa'] at h1
    have h2 : subtractedLag S L ≤ C / (1 / 2 - a) * x ^ a + 1 / Real.sqrt x := by
      rw [← mul_le_mul_iff_of_pos_right hsx]
      have : (C / (1 / 2 - a) * x ^ a + 1 / Real.sqrt x) * Real.sqrt x
          = C * (Real.sqrt x * x ^ a) / (1 / 2 - a) + 1 := by
        field_simp
      rw [this]; exact h1
    have h3 : 1 / Real.sqrt x ≤ x ^ a := by
      have hxa1 : 1 ≤ x ^ a := Real.one_le_rpow hx1.le ha0.le
      have hsx1 : 1 ≤ Real.sqrt x := by rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
      have : 1 / Real.sqrt x ≤ 1 := by rw [div_le_one hsx]; exact hsx1
      linarith
    rw [← hxa]
    nlinarith
  set K₀ := lagWeightTotal + ∑ q ∈ S, ‖lagWeight q‖ with hK₀
  have hK₀0 : 0 ≤ K₀ := add_nonneg lagWeightTotal_nonneg (Finset.sum_nonneg fun q _ => norm_nonneg _)
  refine ⟨K₁ + K₀ * Real.exp (Real.log x₁ / 2), fun u hu => ?_⟩
  have hexp1 : 1 ≤ Real.exp (a * u) := Real.one_le_exp (by positivity)
  have hB0 : 0 ≤ K₀ * Real.exp (Real.log x₁ / 2) := by positivity
  rcases le_or_gt (Real.log x₁) u with hbig | hsmall
  · have := hlarge u hbig
    nlinarith
  · have h1 : subtractedLag S u ≤ K₀ * Real.exp (u / 2) := by
      rcases hu.lt_or_eq with hpos | hzero
      · exact (le_abs_self _).trans (abs_subtractedLag_le S hpos)
      · subst hzero
        have h0 := abs_subtractedLag_le S (u := Real.log x₁ / 2) (by
          have := Real.log_pos hx₁1; linarith)
        -- `Φ_S` at the origin is bounded through continuity from the right
        have hc : Continuous (subtractedLag S) :=
          (Complex.continuous_re.comp continuous_weilLagFunction_unconditional).sub
            (continuous_offLineLagWave S)
        have hlim : Tendsto (fun u : ℝ => K₀ * Real.exp (u / 2) - subtractedLag S u)
            (𝓝[>] 0) (𝓝 (K₀ * Real.exp (0 / 2) - subtractedLag S 0)) :=
          (((continuous_const.mul (Real.continuous_exp.comp
            (continuous_id.div_const 2))).sub hc).tendsto 0).mono_left nhdsWithin_le_nhds
        have hev : ∀ᶠ u in 𝓝[>] (0:ℝ), 0 ≤ K₀ * Real.exp (u / 2) - subtractedLag S u :=
          eventually_nhdsWithin_of_forall fun u hu' => by
            have := (le_abs_self _).trans (abs_subtractedLag_le S (u := u) hu')
            linarith
        have := ge_of_tendsto hlim hev
        linarith
    have h2 : Real.exp (u / 2) ≤ Real.exp (Real.log x₁ / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 : K₀ * Real.exp (u / 2) ≤ K₀ * Real.exp (Real.log x₁ / 2) :=
      mul_le_mul_of_nonneg_left h2 hK₀0
    nlinarith

/-! ## The converse of the finite off-line von Koch law -/

/-- **Landau's theorem with a finite off-line wave subtracted.** If
`ψ(t) − t + Re Σ_{q ∈ S} t^q/q ≥ −C t^{½+a}` for `t ≥ x₁`, with `0 < a < ½`, then every zero copy
whose pole `ρ − ½` is none of the points `ρ_q − ½`, `conj ρ_q − ½` (`q ∈ S`) has real part at most
`½ + a`. -/
theorem re_le_half_add_of_chebyshevPsi_sub_add_offLineWave_ge (S : Finset XiZeroCopy)
    {C a x₁ : ℝ} (hC : 0 ≤ C) (ha0 : 0 < a) (ha : a < 1 / 2) (hx₁1 : 1 < x₁)
    (hpow : ∀ t, x₁ ≤ t → -(C * t ^ (1 / 2 + a)) ≤ Chebyshev.psi t - t + (offLineWave S t).re)
    (q : XiZeroCopy) (hq : lagPole q ∉ offLinePoles S) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  obtain ⟨M, hM⟩ := exists_subtractedLag_le_exp_of_ge_rpow S hC ha0 ha hx₁1 (fun t ht => by
    unfold chebyshevError; exact hpow t ht)
  exact re_le_half_add_of_subtractedLag_le_exp S ha0.le ha hM q hq

/-- `√t log²t ≤ (4/a²) t^{½+a}` for `t ≥ 1` and `a > 0`. -/
theorem sqrt_mul_log_sq_le_rpow {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ t) :
    Real.sqrt t * Real.log t ^ 2 ≤ 4 / a ^ 2 * t ^ (1 / 2 + a) := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hl : Real.log t ≤ t ^ (a / 2) / (a / 2) := Real.log_le_rpow_div ht0.le (by positivity)
  have hl2 : Real.log t ^ 2 ≤ 4 / a ^ 2 * t ^ a := by
    have hp : 0 ≤ t ^ (a / 2) / (a / 2) := by positivity
    calc Real.log t ^ 2 ≤ (t ^ (a / 2) / (a / 2)) ^ 2 := pow_le_pow_left₀ hl0 hl 2
      _ = 4 / a ^ 2 * (t ^ (a / 2)) ^ 2 := by field_simp; ring
      _ = 4 / a ^ 2 * t ^ a := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hs : Real.sqrt t * t ^ a = t ^ (1 / 2 + a) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]
  calc Real.sqrt t * Real.log t ^ 2 ≤ Real.sqrt t * (4 / a ^ 2 * t ^ a) :=
        mul_le_mul_of_nonneg_left hl2 (Real.sqrt_nonneg _)
    _ = 4 / a ^ 2 * (Real.sqrt t * t ^ a) := by ring
    _ = 4 / a ^ 2 * t ^ (1 / 2 + a) := by rw [hs]

/-- **The finite-wave law places every zero off the subtracted poles on `Re ≤ ½`.** -/
theorem re_le_half_of_abs_chebyshevPsi_sub_add_offLineWave_le (S : Finset XiZeroCopy) {K : ℝ}
    (hK : ∀ x : ℝ, 16 ≤ x →
      |Chebyshev.psi x - x + (offLineWave S x).re| ≤ K * Real.sqrt x * Real.log x ^ 2)
    (q : XiZeroCopy) (hq : lagPole q ∉ offLinePoles S) :
    (q.1 : ℂ).re ≤ 1 / 2 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases lt_or_ge ε (1 / 2) with hε2 | hε2
  · refine re_le_half_add_of_chebyshevPsi_sub_add_offLineWave_ge S (C := |K| * (4 / ε ^ 2))
      (x₁ := 16) (by positivity) hε hε2 (by norm_num) (fun t ht => ?_) q hq
    have h1 := (abs_le.mp (hK t ht)).1
    have h2 := sqrt_mul_log_sq_le_rpow hε (show (1:ℝ) ≤ t by linarith)
    have h3 : K * Real.sqrt t * Real.log t ^ 2 ≤ |K| * (Real.sqrt t * Real.log t ^ 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    have h4 : |K| * (Real.sqrt t * Real.log t ^ 2) ≤ |K| * (4 / ε ^ 2 * t ^ (1 / 2 + ε)) :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    nlinarith
  · linarith [xiZeroCopy_re_lt_one q]

/-- **A finite-wave law for `ψ` forces finitely many off-line zeros.** -/
theorem finite_offLine_of_abs_chebyshevPsi_sub_add_offLineWave_le (S : Finset XiZeroCopy) {K : ℝ}
    (hK : ∀ x : ℝ, 16 ≤ x →
      |Chebyshev.psi x - x + (offLineWave S x).re| ≤ K * Real.sqrt x * Real.log x ^ 2) :
    {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite := by
  have hle := re_le_half_of_abs_chebyshevPsi_sub_add_offLineWave_le S hK
  refine ((offLinePoles_finite S).biUnion fun p _ =>
    (finite_xiZeroCopy_band p.im le_rfl).union (finite_xiZeroCopy_band (-p.im) le_rfl)).subset ?_
  intro q hq
  simp only [mem_setOf_eq] at hq
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · set r := xiZeroCopyReflectEquiv q with hr
    have hrre : 1 / 2 < (r.1 : ℂ).re := by
      rw [hr, xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re]; linarith
    have hrP : lagPole r ∈ offLinePoles S := by
      by_contra h; linarith [hle r h]
    refine mem_iUnion₂.mpr ⟨lagPole r, hrP, Or.inr ?_⟩
    simp only [mem_setOf_eq]
    unfold lagPole
    rw [hr, xiZeroCopy_reflect_val]
    simp
  · have hqP : lagPole q ∈ offLinePoles S := by
      by_contra h; linarith [hle q h]
    refine mem_iUnion₂.mpr ⟨lagPole q, hqP, Or.inl ?_⟩
    simp only [mem_setOf_eq]
    unfold lagPole
    simp

/-- **Finitely many off-line zeros is exactly a finite-wave law for `ψ`.** The off-line zero copies
form a finite set iff `|ψ(x) − x + Re Σ_{q ∈ S} x^q/q| ≤ K √x log²x` for `x ≥ 16`, for some finite
set `S` of copies and some `K`. -/
theorem finite_offLine_iff_exists_offLineWave :
    {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite ↔
      ∃ S : Finset XiZeroCopy, ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
        |Chebyshev.psi x - x + (offLineWave S x).re| ≤ K * Real.sqrt x * Real.log x ^ 2 := by
  constructor
  · intro hfin
    obtain ⟨K, _, hK⟩ := exists_abs_chebyshevPsi_sub_add_offLineWave_le_of_finite hfin
    exact ⟨hfin.toFinset, K, hK⟩
  · rintro ⟨S, K, hK⟩
    exact finite_offLine_of_abs_chebyshevPsi_sub_add_offLineWave_le S hK

end

end RHTower
