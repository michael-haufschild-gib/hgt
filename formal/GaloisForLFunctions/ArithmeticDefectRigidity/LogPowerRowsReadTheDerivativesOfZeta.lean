import GaloisForLFunctions.ArithmeticDefectRigidity.TheRenormalizedCofactorActsOnPowerRowsByZeta

/-!
# Log-power rows read the derivatives of ζ

The error of the two-pole expansion of `Σ_{j≤n} j^{-ε}⌊n/j⌋^s` is holomorphic in the exponent and
locally uniformly `O(n^{(Re s + r − ε)/2})`. Cauchy's estimate therefore transfers the expansion
to its `s`-derivatives: for `0 < Re s < 1 − ε` and every `k`,
`Σ_{j≤n} j^{-ε}⌊n/j⌋^s log^k⌊n/j⌋ = Σ_{i≤k} C(k,i) ζ^{(i)}(s+ε) n^s log^{k−i} n + 𝓛_{s,k} n^{1−ε}
  + O(n^{θ/2})`, `θ < 1`, where `𝓛_{s,k}` is the pole trace of the log-power row
(`norm_logPowerCofactorSum_sub_le`). On log-power rows the renormalized cofactor is the
triangular Leibniz matrix of the derivatives of `ζ` at `s + ε`.
-/

open Finset Filter Topology Complex Metric
open GaloisForLFunctions.TransHorizonIncidenceMechanics (partialSumRate partialSumRate_nonneg mellinCell)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The critical strip of exponents `0 < Re s < 1 − ε` of the power-row calculus. -/
def powerRegion (ε : ℝ) : Set ℂ := {s | 0 < s.re ∧ s.re < 1 - ε}

theorem isOpen_powerRegion (ε : ℝ) : IsOpen (powerRegion ε) :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

/-! ### Continuity of the symbol rate -/

theorem continuousOn_partialSumRate : ContinuousOn partialSumRate {w : ℂ | 0 < w.re} := by
  have hre : ContinuousOn (fun w : ℂ => w.re) {w : ℂ | 0 < w.re} := continuous_re.continuousOn
  have hinv : ContinuousOn (fun w : ℂ => 1 / w.re) {w : ℂ | 0 < w.re} :=
    continuousOn_const.div hre fun w hw => (Set.mem_setOf_eq ▸ hw).ne'
  have hpow : Continuous (fun w : ℂ => (2 : ℝ) ^ w.re) :=
    continuous_const.rpow continuous_re fun _ => Or.inl two_ne_zero
  unfold partialSumRate
  exact ((continuous_norm.continuousOn.mul (continuousOn_const.add hinv)).add
    continuousOn_const).mul hpow.continuousOn

theorem continuousOn_powerSymbolRate {ε : ℝ} (hε0 : 0 < ε) :
    ContinuousOn (powerSymbolRate ε) (powerRegion ε) := by
  have hre : ContinuousOn (fun s : ℂ => s.re) (powerRegion ε) := continuous_re.continuousOn
  have h2 : Continuous (fun s : ℂ => (2 : ℝ) ^ |s.re - ε|) :=
    continuous_const.rpow (continuous_re.sub continuous_const).abs fun _ => Or.inl two_ne_zero
  have hσ : ContinuousOn (fun s : ℂ => 1 / s.re) (powerRegion ε) :=
    continuousOn_const.div hre fun s hs => hs.1.ne'
  have hν : ContinuousOn (fun s : ℂ => 1 / (1 - ε + 1 - s.re)) (powerRegion ε) :=
    continuousOn_const.div (continuousOn_const.sub hre) fun s hs => by linarith [hs.2]
  have hw : ContinuousOn (fun s : ℂ => partialSumRate (s + ε)) (powerRegion ε) :=
    continuousOn_partialSumRate.comp (continuous_id.add continuous_const).continuousOn
      fun s hs => by simp only [Set.mem_setOf_eq, add_re, ofReal_re]; linarith [hs.1]
  unfold powerSymbolRate
  have hn : ContinuousOn (fun s : ℂ => ‖s‖) (powerRegion ε) := continuous_norm.continuousOn
  exact (((((h2.continuousOn.mul (hn.mul continuousOn_const)).add hw).add
    (continuousOn_const.mul ((continuousOn_const.add (continuousOn_const.mul hn)).mul
      (continuousOn_const.add hσ)))).add (hn.mul (continuousOn_const.add hν))).add
        continuousOn_const |>.add continuousOn_const).add continuousOn_const

/-! ### Holomorphy of the expansion error -/

/-- The error of the two-pole expansion. -/
def powerSymbolError (ε : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  powerRowCofactorSum ε s n - powerPoleTrace ε s * (((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) -
    riemannZeta (s + ε) * (((n : ℝ)) : ℂ) ^ s

/-- A positive real base gives `x^s = exp(log x · s)`. -/
theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x : ℝ) : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]

/-- `∂_s^k x^s = log^k x · x^s` for `x > 0`. -/
theorem iteratedDeriv_ofReal_cpow {x : ℝ} (hx : 0 < x) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ => ((x : ℝ) : ℂ) ^ s) =
      fun s => (Real.log x : ℂ) ^ k * ((x : ℝ) : ℂ) ^ s := by
  have h : (fun s : ℂ => ((x : ℝ) : ℂ) ^ s) = fun s => Complex.exp ((Real.log x : ℂ) * s) :=
    funext (ofReal_cpow_eq_exp hx)
  rw [h, iteratedDeriv_cexp_const_mul]
  funext s
  rw [ofReal_cpow_eq_exp hx]

theorem contDiff_ofReal_cpow {x : ℝ} (hx : 0 < x) (k : ℕ∞) :
    ContDiff ℂ k (fun s : ℂ => ((x : ℝ) : ℂ) ^ s) := by
  have h : (fun s : ℂ => ((x : ℝ) : ℂ) ^ s) = fun s => Complex.exp ((Real.log x : ℂ) * s) :=
    funext (ofReal_cpow_eq_exp hx)
  rw [h]
  exact Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)

/-- Every row value `⌊n/j⌋`, `j ≤ n`, is a positive real. -/
theorem natDiv_pos_real {n j : ℕ} (hj : j ∈ Icc 1 n) : (0 : ℝ) < ((n / j : ℕ) : ℝ) := by
  obtain ⟨hj1, hjn⟩ := mem_Icc.mp hj
  exact_mod_cast Nat.div_pos hjn hj1

theorem contDiff_powerRowCofactorSum (ε : ℝ) (n : ℕ) (k : ℕ∞) :
    ContDiff ℂ k (fun s => powerRowCofactorSum ε s n) := by
  unfold powerRowCofactorSum
  exact ContDiff.sum fun j hj => contDiff_const.mul (contDiff_ofReal_cpow (natDiv_pos_real hj) k)

/-- **Log-power cofactor sums are exponent derivatives of the power-row sum.** -/
theorem iteratedDeriv_powerRowCofactorSum (ε : ℝ) (n k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun s => powerRowCofactorSum ε s n) s =
      ∑ j ∈ Icc 1 n, (((j : ℝ)) : ℂ) ^ (-(ε : ℂ)) *
        ((Real.log ((n / j : ℕ) : ℝ) : ℂ) ^ k * ((((n / j : ℕ) : ℝ)) : ℂ) ^ s) := by
  unfold powerRowCofactorSum
  rw [iteratedDeriv_fun_sum fun j hj =>
    (contDiff_const.mul (contDiff_ofReal_cpow (natDiv_pos_real hj) k)).contDiffAt]
  refine sum_congr rfl fun j hj => ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_ofReal_cpow (natDiv_pos_real hj)]

/-! ### The pole trace is holomorphic and differentiates termwise -/

/-- `log^k m ≤ a^{-k} m^{δ/2}` with `a = δ/(2(k+1))`. -/
theorem log_pow_le_rpow {δ : ℝ} (hδ : 0 < δ) (k : ℕ) {m : ℝ} (hm : 1 ≤ m) :
    Real.log m ^ k ≤ (2 * (k + 1) / δ) ^ k * m ^ (δ / 2) := by
  have ha : 0 < δ / (2 * (k + 1)) := by positivity
  have hm0 : 0 < m := by linarith
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg hm
  have h1 : Real.log m ≤ m ^ (δ / (2 * (k + 1))) / (δ / (2 * (k + 1))) :=
    Real.log_le_rpow_div hm0.le ha
  have h2 : Real.log m ^ k ≤ (m ^ (δ / (2 * (k + 1))) / (δ / (2 * (k + 1)))) ^ k :=
    pow_le_pow_left₀ hlog0 h1 k
  calc Real.log m ^ k ≤ (m ^ (δ / (2 * (k + 1))) / (δ / (2 * (k + 1)))) ^ k := h2
    _ = (2 * (k + 1) / δ) ^ k * m ^ (δ / (2 * (k + 1)) * k) := by
        rw [div_pow, ← Real.rpow_natCast (m ^ _), ← Real.rpow_mul hm0.le,
          show (2 * (k + 1) / δ : ℝ) = (δ / (2 * (k + 1)))⁻¹ by rw [inv_div], inv_pow]
        ring
    _ ≤ (2 * (k + 1) / δ) ^ k * m ^ (δ / 2) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm ?_) (by positivity)
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

/-- The strip `δ < Re s < α − δ`. -/
def innerStrip (α δ : ℝ) : Set ℂ := {s | δ < s.re ∧ s.re < α - δ}

theorem isOpen_innerStrip (α δ : ℝ) : IsOpen (innerStrip α δ) :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

/-- The `k`-th log-weighted pole term `m^s log^k m · cell_m`. -/
def poleTerm (α : ℝ) (k m : ℕ) (s : ℂ) : ℂ :=
  (((m : ℝ)) : ℂ) ^ s * ((Real.log m : ℂ) ^ k * ((mellinCell α m : ℝ) : ℂ))

/-- Uniform bound of the pole terms on the inner strip. -/
theorem norm_poleTerm_le {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (k m : ℕ) {s : ℂ}
    (hs : s ∈ innerStrip α δ) :
    ‖poleTerm α k m s‖ ≤ α * (2 * (k + 1) / δ) ^ k * (m : ℝ) ^ (-(1 + δ / 2)) := by
  have hs0 : 0 < s.re := lt_trans hδ hs.1
  have hsne : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [poleTerm, Nat.cast_zero, Complex.ofReal_zero, Complex.zero_cpow hsne, zero_mul,
      norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [poleTerm, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hm0, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hm1),
    abs_of_nonneg (TransHorizonIncidenceMechanics.mellinCell_nonneg hα hm)]
  have hcell := (TransHorizonIncidenceMechanics.mellinCell_bounds hα hm).2
  have hlog := log_pow_le_rpow hδ k hm1
  have hpow : (m : ℝ) ^ s.re ≤ (m : ℝ) ^ (α - δ) := Real.rpow_le_rpow_of_exponent_le hm1 hs.2.le
  have hexp : (m : ℝ) ^ (α - δ) * (m : ℝ) ^ (δ / 2) * (m : ℝ) ^ (-α - 1) =
      (m : ℝ) ^ (-(1 + δ / 2)) := by
    rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]; ring_nf
  have hcell0 := TransHorizonIncidenceMechanics.mellinCell_nonneg hα hm
  have hlog0 : 0 ≤ Real.log m ^ k := pow_nonneg (Real.log_nonneg hm1) k
  calc (m : ℝ) ^ s.re * (Real.log m ^ k * mellinCell α m)
      ≤ (m : ℝ) ^ (α - δ) * (((2 * (k + 1) / δ) ^ k * (m : ℝ) ^ (δ / 2)) *
          (α * (m : ℝ) ^ (-α - 1))) :=
        mul_le_mul hpow (mul_le_mul hlog hcell hcell0 (by positivity)) (mul_nonneg hlog0 hcell0)
          (by positivity)
    _ = α * (2 * (k + 1) / δ) ^ k * ((m : ℝ) ^ (α - δ) * (m : ℝ) ^ (δ / 2) * (m : ℝ) ^ (-α - 1)) := by
        ring
    _ = _ := by rw [hexp]

theorem summable_poleTerm_bound (α δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    Summable fun m : ℕ => α * (2 * (k + 1) / δ) ^ k * (m : ℝ) ^ (-(1 + δ / 2)) :=
  (Real.summable_nat_rpow.mpr (by linarith)).mul_left _

theorem hasDerivAt_poleTerm (α : ℝ) (k m : ℕ) {s : ℂ} (hs : s ≠ 0) :
    HasDerivAt (poleTerm α k m) (poleTerm α (k + 1) m s) s := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hzero : poleTerm α k 0 =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [isOpen_ne.mem_nhds hs] with z hz
      simp [poleTerm, Complex.zero_cpow hz]
    refine ((hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq hzero).congr_deriv ?_
    simp [poleTerm, Complex.zero_cpow hs]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := ((hasDerivAt_id s).const_cpow (c := (((m : ℝ)) : ℂ))
    (Or.inl (by exact_mod_cast hm0.ne'))).mul_const ((Real.log m : ℂ) ^ k * ((mellinCell α m : ℝ) : ℂ))
  have hlog : Complex.log (((m : ℝ)) : ℂ) = (Real.log m : ℂ) := (Complex.ofReal_log hm0.le).symm
  refine h.congr_deriv ?_
  simp only [poleTerm, id, mul_one, hlog]; ring

/-- On each inner strip the `k`-th derivative of the pole sum is the `k`-log-weighted pole sum. -/
theorem iteratedDeriv_powerPoleSum_eq {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (k : ℕ) {s : ℂ}
    (hs : s ∈ innerStrip α δ) :
    iteratedDeriv k (powerPoleSum α) s = ∑' m, poleTerm α k m s := by
  induction k generalizing s with
  | zero =>
    simp only [iteratedDeriv_zero, powerPoleSum, poleTerm, pow_zero, one_mul]
  | succ k ih =>
    have hev : iteratedDeriv k (powerPoleSum α) =ᶠ[𝓝 s] fun z => ∑' m, poleTerm α k m z := by
      filter_upwards [(isOpen_innerStrip α δ).mem_nhds hs] with z hz using ih hz
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hdiff : ∀ m, DifferentiableOn ℂ (poleTerm α k m) (innerStrip α δ) := fun m z hz =>
      (hasDerivAt_poleTerm α k m (fun h => by
        have := hz.1; rw [h, Complex.zero_re] at this; linarith)).differentiableAt.differentiableWithinAt
    have h := hasSum_deriv_of_summable_norm (summable_poleTerm_bound α δ hδ k) hdiff
      (isOpen_innerStrip α δ) (fun m z hz => norm_poleTerm_le hα hδ k m hz) hs
    rw [← h.tsum_eq]
    refine tsum_congr fun m => (hasDerivAt_poleTerm α k m ?_).deriv
    intro h0; have := hs.1; rw [h0, Complex.zero_re] at this; linarith

theorem differentiableOn_powerPoleSum {α : ℝ} (hα : 0 < α) :
    DifferentiableOn ℂ (powerPoleSum α) {s : ℂ | 0 < s.re ∧ s.re < α} := by
  intro s hs
  set δ := min s.re (α - s.re) / 2 with hδdef
  have hδ : 0 < δ := by have := hs.1; have := hs.2; positivity
  have hsδ : s ∈ innerStrip α δ := by
    constructor
    · have : δ ≤ s.re / 2 := by rw [hδdef]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith [hs.1]
    · have : δ ≤ (α - s.re) / 2 := by
        rw [hδdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith [hs.2]
  have hdiff : ∀ m, DifferentiableOn ℂ (poleTerm α 0 m) (innerStrip α δ) := fun m z hz =>
    (hasDerivAt_poleTerm α 0 m (fun h => by
      have := hz.1; rw [h, Complex.zero_re] at this; linarith)).differentiableAt.differentiableWithinAt
  have h := differentiableOn_tsum_of_summable_norm (summable_poleTerm_bound α δ hδ 0) hdiff
    (isOpen_innerStrip α δ) (fun m z hz => norm_poleTerm_le hα hδ 0 m hz)
  have heq : (fun w => ∑' m, poleTerm α 0 m w) = powerPoleSum α := by
    funext w; simp only [powerPoleSum, poleTerm, pow_zero, one_mul]
  rw [heq] at h
  exact (h.differentiableAt ((isOpen_innerStrip α δ).mem_nhds hsδ)).differentiableWithinAt

/-- **Termwise derivatives of the pole sum on the full strip.** -/
theorem iteratedDeriv_powerPoleSum {α : ℝ} (hα : 0 < α) (k : ℕ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < α) : iteratedDeriv k (powerPoleSum α) s = ∑' m, poleTerm α k m s := by
  set δ := min s.re (α - s.re) / 2 with hδdef
  have hδ : 0 < δ := by positivity
  refine iteratedDeriv_powerPoleSum_eq hα hδ k ⟨?_, ?_⟩
  · have : δ ≤ s.re / 2 := by rw [hδdef]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith
  · have : δ ≤ (α - s.re) / 2 := by
      rw [hδdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith

theorem differentiableOn_powerSymbolError {ε : ℝ} (hε1 : ε < 1) {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableOn ℂ (fun s => powerSymbolError ε s n) (powerRegion ε) := by
  have hα : 0 < 1 - ε := by linarith
  have hP : DifferentiableOn ℂ (powerPoleTrace ε) (powerRegion ε) := by
    unfold powerPoleTrace
    exact (differentiableOn_powerPoleSum hα).div_const _
  have hZ : DifferentiableOn ℂ (fun s => riemannZeta (s + ε)) (powerRegion ε) := fun s hs =>
    ((differentiableAt_riemannZeta (fun h => by
      have := congrArg Complex.re h
      simp only [id_eq, add_re, ofReal_re, one_re] at this; linarith [hs.2])).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hN : Differentiable ℂ (fun s : ℂ => (((n : ℝ)) : ℂ) ^ s) :=
    (contDiff_ofReal_cpow (by exact_mod_cast hn : (0 : ℝ) < n) ⊤).differentiable (by simp)
  have hS : Differentiable ℂ (fun s => powerRowCofactorSum ε s n) :=
    (contDiff_powerRowCofactorSum ε n ⊤).differentiable (by simp)
  unfold powerSymbolError
  exact (hS.differentiableOn.sub (hP.mul_const _)).sub (hZ.mul hN.differentiableOn)

/-! ### Cauchy's estimate for the expansion error -/

/-- The log-power cofactor sum `Σ_{j≤n} j^{-ε} log^k⌊n/j⌋ ⌊n/j⌋^s`. -/
def logPowerCofactorSum (ε : ℝ) (s : ℂ) (k n : ℕ) : ℂ :=
  ∑ j ∈ Icc 1 n, (((j : ℝ)) : ℂ) ^ (-(ε : ℂ)) *
    ((Real.log ((n / j : ℕ) : ℝ) : ℂ) ^ k * ((((n / j : ℕ) : ℝ)) : ℂ) ^ s)

/-- The pole trace `α⁻¹ Σ_m m^s log^k m (m^{-α} − (m+1)^{-α})` of the log-power row. -/
def logPowerPoleTrace (ε : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  (∑' m, poleTerm (1 - ε) k m s) / ((1 - ε : ℝ) : ℂ)

/-- The Leibniz row `Σ_{i≤k} C(k,i) ζ^{(i)}(s+ε) log^{k−i} n · n^s`. -/
def zetaLeibnizRow (ε : ℝ) (s : ℂ) (k n : ℕ) : ℂ :=
  ∑ i ∈ range (k + 1), (k.choose i : ℂ) * iteratedDeriv i riemannZeta (s + ε) *
    ((Real.log n : ℂ) ^ (k - i) * (((n : ℝ)) : ℂ) ^ s)

theorem contDiffAt_riemannZeta_add {ε : ℝ} {s : ℂ} (hs : s + ε ≠ 1) (k : ℕ∞) :
    ContDiffAt ℂ k (fun z => riemannZeta (z + ε)) s := by
  have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hd : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hζ : ContDiffAt ℂ k riemannZeta (s + ε) :=
    (hd.contDiffOn hopen).contDiffAt (hopen.mem_nhds hs)
  exact hζ.comp s (contDiffAt_id.add contDiffAt_const)

theorem contDiffAt_powerPoleTrace {ε : ℝ} (hε1 : ε < 1) {s : ℂ} (hs : s ∈ powerRegion ε)
    (k : ℕ∞) : ContDiffAt ℂ k (powerPoleTrace ε) s := by
  have hα : 0 < 1 - ε := by linarith
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1 - ε} := isOpen_powerRegion ε
  have hd : DifferentiableOn ℂ (powerPoleTrace ε) {z : ℂ | 0 < z.re ∧ z.re < 1 - ε} := by
    unfold powerPoleTrace
    exact (differentiableOn_powerPoleSum hα).div_const _
  exact (hd.contDiffOn hopen).contDiffAt (hopen.mem_nhds hs)

/-- **The `k`-th exponent derivative of the expansion error** is the log-power cofactor sum minus
its pole term and the Leibniz row of the derivatives of `ζ`. -/
theorem iteratedDeriv_powerSymbolError {ε : ℝ} (hε1 : ε < 1) {n : ℕ} (hn : 1 ≤ n) {s : ℂ}
    (hs : s ∈ powerRegion ε) (k : ℕ) :
    iteratedDeriv k (fun s => powerSymbolError ε s n) s =
      logPowerCofactorSum ε s k n -
        logPowerPoleTrace ε s k * (((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) - zetaLeibnizRow ε s k n := by
  have hα : 0 < 1 - ε := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsε : s + ε ≠ 1 := fun h => by
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, one_re] at this; linarith [hs.2]
  have h1 : ContDiffAt ℂ k (fun s => powerRowCofactorSum ε s n) s :=
    (contDiff_powerRowCofactorSum ε n k).contDiffAt
  have h2 : ContDiffAt ℂ k (fun s => powerPoleTrace ε s * (((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ)) s :=
    (contDiffAt_powerPoleTrace hε1 hs k).mul contDiffAt_const
  have hz : ContDiffAt ℂ k (fun z => riemannZeta (z + ε)) s := contDiffAt_riemannZeta_add hsε k
  have hN : ContDiffAt ℂ k (fun s : ℂ => (((n : ℝ)) : ℂ) ^ s) s := (contDiff_ofReal_cpow hn0 k).contDiffAt
  have h3 : ContDiffAt ℂ k (fun s => riemannZeta (s + ε) * (((n : ℝ)) : ℂ) ^ s) s := hz.mul hN
  unfold powerSymbolError
  rw [iteratedDeriv_fun_sub (h1.sub h2) h3, iteratedDeriv_fun_sub h1 h2,
    iteratedDeriv_powerRowCofactorSum, iteratedDeriv_mul_const_field,
    iteratedDeriv_fun_mul hz hN]
  have hP : iteratedDeriv k (powerPoleTrace ε) s = logPowerPoleTrace ε s k := by
    have : powerPoleTrace ε = fun z => powerPoleSum (1 - ε) z / ((1 - ε : ℝ) : ℂ) := rfl
    rw [this, iteratedDeriv_div_const, iteratedDeriv_powerPoleSum hα k hs.1 hs.2, logPowerPoleTrace]
  rw [hP, logPowerCofactorSum, zetaLeibnizRow]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_comp_add_const, iteratedDeriv_ofReal_cpow hn0]

/-- **Cauchy's estimate.** At every `s₀` of the strip there is `θ < 1` such that every
exponent derivative of the expansion error is `O(n^{θ/2})`. -/
theorem exists_norm_iteratedDeriv_powerSymbolError_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {s₀ : ℂ} (hs₀ : s₀ ∈ powerRegion ε) :
    ∃ θ : ℝ, θ < 1 ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖iteratedDeriv k (fun s => powerSymbolError ε s n) s₀‖ ≤ C * Real.sqrt n ^ θ := by
  set r := min s₀.re (1 - ε - s₀.re) / 2 with hr
  have hs0 := hs₀.1
  have hs1 := hs₀.2
  have hr0 : 0 < r := by
    have : 0 < 1 - ε - s₀.re := by linarith
    positivity
  have hr1 : r ≤ s₀.re / 2 := by rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hr2 : r ≤ (1 - ε - s₀.re) / 2 := by
    rw [hr]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hball : closedBall s₀ r ⊆ powerRegion ε := by
    intro s hs
    have hd : |s.re - s₀.re| ≤ r := by
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans (by rwa [mem_closedBall, dist_eq_norm] at hs)
    have := (abs_le.mp hd)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  obtain ⟨M, hM⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn
    ((continuousOn_powerSymbolRate hε0).mono hball)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s₀ (mem_closedBall_self hr0.le))
  refine ⟨s₀.re + r - ε, by linarith, fun k => ⟨k.factorial * M / r ^ k, fun n hn => ?_⟩⟩
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hsphere : ∀ z ∈ sphere s₀ r, ‖powerSymbolError ε z n‖ ≤ M * Real.sqrt n ^ (s₀.re + r - ε) := by
    intro z hz
    have hzb : z ∈ closedBall s₀ r := sphere_subset_closedBall hz
    have hzr := hball hzb
    have hbound := norm_powerRowCofactorSum_sub_le_rate hε0 hε1 hzr.1 hzr.2 hn
    have hre : z.re ≤ s₀.re + r := by
      have h : |(z - s₀).re| ≤ r := (Complex.abs_re_le_norm (z - s₀)).trans
        (by rwa [mem_closedBall, dist_eq_norm] at hzb)
      rw [Complex.sub_re] at h
      linarith [(abs_le.mp h).2]
    have hpow : Real.sqrt n ^ (z.re - ε) ≤ Real.sqrt n ^ (s₀.re + r - ε) :=
      Real.rpow_le_rpow_of_exponent_le hsq1 (by linarith)
    have hrate : powerSymbolRate ε z ≤ M := (le_abs_self _).trans (hM z hzb)
    calc ‖powerSymbolError ε z n‖ ≤ powerSymbolRate ε z * Real.sqrt n ^ (z.re - ε) := hbound
      _ ≤ M * Real.sqrt n ^ (s₀.re + r - ε) := by
          refine (mul_le_mul_of_nonneg_right hrate (by positivity)).trans ?_
          exact mul_le_mul_of_nonneg_left hpow hM0
  have hdiff : DiffContOnCl ℂ (fun s => powerSymbolError ε s n) (ball s₀ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball s₀ hr0.ne']
    exact (differentiableOn_powerSymbolError hε1 hn).mono hball
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr0 hdiff hsphere
  calc _ ≤ k.factorial * (M * Real.sqrt n ^ (s₀.re + r - ε)) / r ^ k := h
    _ = k.factorial * M / r ^ k * Real.sqrt n ^ (s₀.re + r - ε) := by ring

/-- **The log-power symbol law.** For `0 < Re s < 1 − ε` there is `θ < 1` such that for every `k`
some `C` gives, for all `n ≥ 1`,
`‖Σ_{j≤n} j^{-ε} log^k⌊n/j⌋ ⌊n/j⌋^s − 𝓛_{s,k} n^{1−ε} − Σ_{i≤k} C(k,i) ζ^{(i)}(s+ε) log^{k−i}n · n^s‖
  ≤ C (√n)^θ`. -/
theorem norm_logPowerCofactorSum_sub_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {s : ℂ}
    (hs : s ∈ powerRegion ε) :
    ∃ θ : ℝ, θ < 1 ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖logPowerCofactorSum ε s k n -
          logPowerPoleTrace ε s k * (((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) - zetaLeibnizRow ε s k n‖ ≤
        C * Real.sqrt n ^ θ := by
  obtain ⟨θ, hθ, hC⟩ := exists_norm_iteratedDeriv_powerSymbolError_le hε0 hε1 hs
  refine ⟨θ, hθ, fun k => ?_⟩
  obtain ⟨C, hCk⟩ := hC k
  exact ⟨C, fun n hn => by rw [← iteratedDeriv_powerSymbolError hε1 hn hs k]; exact hCk n hn⟩

end GaloisForLFunctions.ArithmeticDefectRigidity
