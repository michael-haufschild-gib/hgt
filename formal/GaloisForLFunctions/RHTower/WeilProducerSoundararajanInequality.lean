import GaloisForLFunctions.RHTower.WeilProducerExplicitFormulaResidues

/-!
# Soundararajan's inequality on the Weil cone

Let `lam` be full-cone Weil-positive, `A_lam = U − Φ_lam` the continuation of `Σ lam(n) n^{−s}` to
`Re s > ½`, and `log F_lam(σ + it) = Σ lam(n) n^{−2−it}/log n + ∫_σ^2 A_lam(u + it) du`
(`producerLogZeta`; it is the Dirichlet series `Σ lam(n) n^{−s}/log n` on `Re s > 1`,
`producerLogZeta_eq_LSeries`).

**Theorem** (`re_producerLogZeta_le`).  For `t ≠ 0`, `L > 0`, `½ < σ ≤ σ₀ ≤ 2` with
`λ = (σ₀ − ½)L` satisfying `e^{−λ} ≤ λ`:

`Re log F_lam(σ + it) ≤ (1/L) Re Σ_n lam(n)(L − log n)⁺/(n^{σ₀+it} log n) + Re U(σ₀ + it)/L`
`    + ∫_σ^{σ₀} Re U(u + it) du + O_lam((1 + e^{(1−σ₀)L}/(L t²))/L)`.

For `ζ` this is Soundararajan's upper bound for `log|ζ|`, which needs RH.  Here it holds for every
point of the Weil cone, with positivity `Re Φ_lam ≥ 0` in the role of RH.  With
`Re U(u + it) = ½ log|t| + O(1)` it reads
`log|F_lam(σ + it)| ≤ Re P_x(σ₀ + it) + ((1 + λ)/2) log|t|/log x + O(1/log x)`, `x = e^L`.

**Proof.**  Integrate the residue form of the explicit formula
`Σ lam(n) n^{−z}(L − log n)⁺ = L·A_lam(z) + A_lam'(z) + E_L(z)` over `z = u + it`,
`u ∈ [σ₀, 2]` (`mul_integral_producerA_eq`).  The boundary-measure part of `E_L` is at most
`e^{(½−u)L} ∫ |σ₀ − ½ + it − ir|⁻² dμ_lam = e^{(½−u)L} Re H(σ₀ − ½ + it)/(σ₀ − ½)` by the Poisson
identity.  After integration it is at most `(e^{−λ}/λ) Re H`, which `−Re H` from
`Re A_lam(σ₀ + it) = Re U − Re H` absorbs.  Left of `σ₀`, `Re A_lam ≤ Re U`, because
`Re H ≥ 0`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz PerronPole

/-! ### The function `A_lam` -/

theorem producerA_eq_LSeries {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {z : ℂ} (hz : 1 < z.re) :
    producerA hW z = LSeries (lamC lam) z := by
  unfold producerA
  rw [weilContinuation_eq hW hz]
  unfold weilFunction zetaArchimedeanDatum
  ring

theorem re_weilConst {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : (weilConst hW).re = 0 := by
  have h := re_herglotzFunction_eq hW (s := 2) (by norm_num)
  unfold weilConst
  rw [Complex.sub_re, h]
  ring

theorem re_producerA {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (z : ℂ) :
    (producerA hW z).re = (zetaArchimedeanDatum z + 1 / (z - 1)).re -
      (herglotzFunction hW (z - 1 / 2)).re := by
  have h := re_weilConst hW
  unfold weilConst at h
  unfold producerA weilContinuation
  simp only [Complex.sub_re, Complex.add_re] at h ⊢
  linarith

/-- The domain `{Re z > ½, z ≠ 1}` of `A_lam`. -/
def producerDomain : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ z ≠ 1}

theorem isOpen_producerDomain : IsOpen producerDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne

theorem continuousOn_producerA {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ContinuousOn (producerA hW) producerDomain := fun _ hz =>
  (hasDerivAt_producerA hW hz.1 hz.2).continuousAt.continuousWithinAt

theorem continuousOn_producerDA {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ContinuousOn (producerDA hW) producerDomain := by
  have hd : DifferentiableOn ℂ (producerA hW) producerDomain := fun z hz =>
    (hasDerivAt_producerA hW hz.1 hz.2).differentiableAt.differentiableWithinAt
  refine (hd.deriv isOpen_producerDomain).continuousOn.congr fun z hz => ?_
  exact ((hasDerivAt_producerA hW hz.1 hz.2).deriv).symm

theorem horizontal_mem_producerDomain {u t : ℝ} (hu : 1 / 2 < u) (ht : t ≠ 0) :
    (u : ℂ) + t * I ∈ producerDomain := by
  refine ⟨by simpa using hu, fun h => ht ?_⟩
  have := congrArg Complex.im h
  simpa using this

theorem continuousOn_horizontal {f : ℂ → ℂ} (hf : ContinuousOn f producerDomain) {a b t : ℝ}
    (ha : 1 / 2 < a) (hb : 1 / 2 < b) (ht : t ≠ 0) :
    ContinuousOn (fun u : ℝ => f (u + t * I)) (uIcc a b) := by
  refine hf.comp (by fun_prop) fun u hu => horizontal_mem_producerDomain ?_ ht
  rcases le_total a b with h | h
  · rw [uIcc_of_le h] at hu; linarith [hu.1]
  · rw [uIcc_of_ge h] at hu; linarith [hu.1]

/-! ### The residues away from `s = 0` -/

theorem sq_le_normSq_of_im {w : ℂ} : w.im ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg w.re]

theorem norm_cexp_div_sq_le {b : ℂ} {L t : ℝ} (ht : t ^ 2 ≤ ‖b‖ ^ 2) (ht0 : t ≠ 0) :
    ‖cexp (b * L) / b ^ 2‖ ≤ Real.exp (b.re * L) / t ^ 2 := by
  have ht2 : 0 < t ^ 2 := by positivity
  rw [norm_div, Complex.norm_exp, norm_pow]
  have : (b * (L : ℂ)).re = b.re * L := by simp
  rw [this]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le ht2 ht

/-- **Pointwise bound for `E_L`.**  For `½ < σ₀ ≤ u`, `t ≠ 0`, `L > 0`, with
`P = ∫ |σ₀ − ½ + it − ir|⁻² dμ_lam`:
`|E_L(u + it)| ≤ (e^{(1−u)L} + e^{−uL}(1 + (1 − e^{−2L})⁻¹))/t² + e^{(½−u)L} P`. -/
theorem norm_producerE_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ₀ u t L : ℝ}
    (hσ₀ : 1 / 2 < σ₀) (hu : σ₀ ≤ u) (ht : t ≠ 0) (hL : 0 < L) :
    ‖producerE hW L (u + t * I)‖ ≤
      (Real.exp ((1 - u) * L) + Real.exp (-u * L) * (1 + (1 - Real.exp (-2 * L))⁻¹)) / t ^ 2 +
        Real.exp ((1 / 2 - u) * L) *
          ∫ r, ‖1 / (((σ₀ - 1 / 2 : ℝ) : ℂ) + t * I - I * r) ^ 2‖ ∂boundaryMeasure hW := by
  set z : ℂ := (u : ℂ) + t * I with hz
  have hzre : z.re = u := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  have ht2 : 0 < t ^ 2 := by positivity
  set w₀ : ℂ := ((σ₀ - 1 / 2 : ℝ) : ℂ) + t * I with hw₀
  have hw₀re : 0 < w₀.re := by simp [hw₀]; linarith
  -- the pole at `1 − z`
  have h1 : ‖cexp ((1 - z) * L) / (1 - z) ^ 2‖ ≤ Real.exp ((1 - u) * L) / t ^ 2 := by
    have h := norm_cexp_div_sq_le (b := 1 - z) (L := L) (t := t)
      (by have := sq_le_normSq_of_im (w := 1 - z); simpa [hzim] using this) ht
    simpa [hzre] using h
  -- the pole at `−z`
  have h2 : ‖cexp (-z * L) / z ^ 2‖ ≤ Real.exp (-u * L) / t ^ 2 := by
    have h := norm_cexp_div_sq_le (b := -z) (L := L) (t := t)
      (by have := sq_le_normSq_of_im (w := -z); simpa [hzim] using this) ht
    simpa [hzre] using h
  -- the trivial points
  set q : ℝ := Real.exp (-2 * L) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hk : ∀ k : ℕ, ‖cexp ((-z - 2 * k) * L) / (-z - 2 * k) ^ 2‖ ≤
      Real.exp (-u * L) / t ^ 2 * q ^ k := by
    intro k
    have h := norm_cexp_div_sq_le (b := -z - 2 * k) (L := L) (t := t)
      (by have := sq_le_normSq_of_im (w := -z - 2 * k); simpa [hzim] using this) ht
    refine h.trans (le_of_eq ?_)
    have hre : (-z - 2 * (k : ℂ)).re = -u - 2 * k := by simp [hzre]
    rw [hre, hq, ← Real.exp_nat_mul, div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  have hgeo : Summable fun k : ℕ => Real.exp (-u * L) / t ^ 2 * q ^ k :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hs : Summable fun k : ℕ => ‖cexp ((-z - 2 * k) * L) / (-z - 2 * k) ^ 2‖ :=
    hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hk
  have h3 : ‖∑' k : ℕ, cexp ((-z - 2 * k) * L) / (-z - 2 * k) ^ 2‖ ≤
      Real.exp (-u * L) / t ^ 2 * (1 - q)⁻¹ := by
    refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hk hgeo).trans (le_of_eq ?_))
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  -- the boundary measure
  have hmaj := (integrable_inv_sub_I_mul_sq hW hw₀re).norm.const_mul (Real.exp ((1 / 2 - u) * L))
  have h4 : ‖∫ r, cexp ((I * r - (z - 1 / 2)) * L) / (I * r - (z - 1 / 2)) ^ 2
      ∂boundaryMeasure hW‖ ≤ Real.exp ((1 / 2 - u) * L) *
        ∫ r, ‖1 / (w₀ - I * r) ^ 2‖ ∂boundaryMeasure hW := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le hmaj (Eventually.of_forall fun r => ?_)
    have hβ : (I * (r : ℂ) - (z - 1 / 2)).re = 1 / 2 - u := by simp [hzre]
    have hn : ‖w₀ - I * r‖ ^ 2 ≤ ‖I * (r : ℂ) - (z - 1 / 2)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
      simp [hw₀, hz]
      nlinarith
    have hpos : 0 < ‖w₀ - I * r‖ := norm_pos_iff.mpr (sub_I_mul_ne_zero hw₀re r)
    rw [norm_div, Complex.norm_exp, norm_pow, norm_div, norm_one, norm_pow]
    have : ((I * (r : ℂ) - (z - 1 / 2)) * (L : ℂ)).re = (1 / 2 - u) * L := by
      rw [show ((I * (r : ℂ) - (z - 1 / 2)) * (L : ℂ)).re =
        (I * (r : ℂ) - (z - 1 / 2)).re * L by simp, hβ]
    rw [this, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hn)
      (Real.exp_pos _).le
  -- assemble
  have htri : ‖producerE hW L z‖ ≤ ‖cexp ((1 - z) * L) / (1 - z) ^ 2‖ + ‖cexp (-z * L) / z ^ 2‖ +
      ‖∑' k : ℕ, cexp ((-z - 2 * k) * L) / (-z - 2 * k) ^ 2‖ +
      ‖∫ r, cexp ((I * r - (z - 1 / 2)) * L) / (I * r - (z - 1 / 2)) ^ 2 ∂boundaryMeasure hW‖ := by
    unfold producerE
    refine (norm_sub_le _ _).trans ?_
    gcongr
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact norm_add_le _ _
  have e : (Real.exp ((1 - u) * L) + Real.exp (-u * L) * (1 + (1 - q)⁻¹)) / t ^ 2 =
      Real.exp ((1 - u) * L) / t ^ 2 + Real.exp (-u * L) / t ^ 2 +
        Real.exp (-u * L) / t ^ 2 * (1 - q)⁻¹ := by ring
  rw [e]
  linarith

theorem integral_exp_sub_mul (c L a b : ℝ) (hL : L ≠ 0) :
    ∫ u in a..b, Real.exp ((c - u) * L) =
      (Real.exp ((c - a) * L) - Real.exp ((c - b) * L)) / L := by
  have hd : ∀ u ∈ uIcc a b, HasDerivAt (fun u : ℝ => -Real.exp ((c - u) * L) / L)
      (Real.exp ((c - u) * L)) u := by
    intro u _
    have h := (((hasDerivAt_id u).const_sub c).mul_const L).exp.neg.div_const L
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u : ℝ => Real.exp ((c - u) * L)).intervalIntegrable a b)]
  ring

theorem integral_exp_sub_mul_le (c L a b : ℝ) (hL : 0 < L) :
    ∫ u in a..b, Real.exp ((c - u) * L) ≤ Real.exp ((c - a) * L) / L := by
  rw [integral_exp_sub_mul c L a b hL.ne']
  have := Real.exp_pos ((c - b) * L)
  exact div_le_div_of_nonneg_right (by linarith) hL.le

/-! ### The Dirichlet polynomial -/

/-- The cutoff `N = ⌈e^L⌉` beyond which `(L − log n)⁺ = 0`. -/
theorem max_sub_log_eq_zero {L : ℝ} {n : ℕ} (hn : ⌈Real.exp L⌉₊ ≤ n) :
    max (L - Real.log n) 0 = 0 := by
  have h1 : Real.exp L ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hpos : (0 : ℝ) < n := (Real.exp_pos L).trans_le h1
  have : L ≤ Real.log n := by
    rw [← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos L) h1
  exact max_eq_right (by linarith)

/-- The weighted Dirichlet polynomial `Σ_n lam(n) n^{−s} (L − log n)⁺/log n`. -/
def producerPoly (lam : ℕ → ℝ) (L : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, LSeries.term (lamC lam) s n * ((max (L - Real.log n) 0 : ℝ) : ℂ) / Real.log n

theorem producerPoly_eq_sum (lam : ℕ → ℝ) (L : ℝ) (s : ℂ) :
    producerPoly lam L s = ∑ n ∈ Finset.range ⌈Real.exp L⌉₊,
      LSeries.term (lamC lam) s n * ((max (L - Real.log n) 0 : ℝ) : ℂ) / Real.log n := by
  unfold producerPoly
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  rw [max_sub_log_eq_zero hn]
  simp

theorem tsum_lamC_mul_max_eq_sum (lam : ℕ → ℝ) (L : ℝ) (s : ℂ) :
    ∑' n : ℕ, LSeries.term (lamC lam) s n * ((max (L - Real.log n) 0 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range ⌈Real.exp L⌉₊,
        LSeries.term (lamC lam) s n * ((max (L - Real.log n) 0 : ℝ) : ℂ) := by
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  rw [max_sub_log_eq_zero hn]
  simp

theorem term_lamC_eq_cexp (lam : ℕ → ℝ) (s : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    LSeries.term (lamC lam) s n = lamC lam n * cexp (-(s * Real.log n)) := by
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [LSeries.term_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hnC, div_eq_mul_inv,
    ← Complex.exp_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_log hnpos.le]
  ring_nf

theorem term_lamC_eq_zero_of_lt (lam : ℕ → ℝ) (s : ℂ) {n : ℕ} (hn : n < 2) :
    LSeries.term (lamC lam) s n = 0 := by
  rcases Nat.lt_succ_iff.mp hn |>.lt_or_eq with h | h
  · have : n = 0 := by omega
    subst this; simp
  · subst h; simp [LSeries.term, lamC]

/-- **The horizontal integral of the weighted sum.**  `∫_a^b S(u + it) du = D(a + it) − D(b + it)`
where `S` is the weighted sum and `D = producerPoly`. -/
theorem integral_weighted_sum_eq (lam : ℕ → ℝ) (L a b t : ℝ) :
    ∫ u in a..b, ∑' n : ℕ, LSeries.term (lamC lam) ((u : ℂ) + t * I) n *
        ((max (L - Real.log n) 0 : ℝ) : ℂ) =
      producerPoly lam L ((a : ℂ) + t * I) - producerPoly lam L ((b : ℂ) + t * I) := by
  simp_rw [tsum_lamC_mul_max_eq_sum]
  rw [producerPoly_eq_sum, producerPoly_eq_sum, ← Finset.sum_sub_distrib]
  have hcont : ∀ n : ℕ, Continuous fun u : ℝ => LSeries.term (lamC lam) ((u : ℂ) + t * I) n *
      ((max (L - Real.log n) 0 : ℝ) : ℂ) := by
    intro n
    rcases lt_or_ge n 2 with hn | hn
    · simp_rw [term_lamC_eq_zero_of_lt lam _ hn, zero_mul]; exact continuous_const
    · simp_rw [term_lamC_eq_cexp lam _ hn]; fun_prop
  rw [intervalIntegral.integral_finsetSum fun n _ => (hcont n).intervalIntegrable a b]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases lt_or_ge n 2 with hn | hn
  · simp [term_lamC_eq_zero_of_lt lam _ hn]
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have hlogC : (Real.log n : ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
    have e2 : ∀ x : ℝ, cexp (-(((x : ℂ) + t * I) * Real.log n)) =
        cexp (-(t * I * Real.log n)) * cexp ((-(Real.log n : ℂ)) * x) := by
      intro x
      rw [← Complex.exp_add]
      ring_nf
    have e : ∀ u : ℝ, LSeries.term (lamC lam) ((u : ℂ) + t * I) n *
        ((max (L - Real.log n) 0 : ℝ) : ℂ) = (lamC lam n * ((max (L - Real.log n) 0 : ℝ) : ℂ) *
          cexp (-(t * I * Real.log n))) * cexp ((-(Real.log n : ℂ)) * u) := by
      intro u
      rw [term_lamC_eq_cexp lam _ hn, e2]
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex (neg_ne_zero.mpr hlogC)]
    field_simp
    ring

theorem continuous_weighted_sum (lam : ℕ → ℝ) (L t : ℝ) :
    Continuous fun u : ℝ => ∑' n : ℕ, LSeries.term (lamC lam) ((u : ℂ) + t * I) n *
      ((max (L - Real.log n) 0 : ℝ) : ℂ) := by
  simp_rw [tsum_lamC_mul_max_eq_sum]
  refine continuous_finsetSum _ fun n _ => ?_
  rcases lt_or_ge n 2 with hn | hn
  · simp_rw [term_lamC_eq_zero_of_lt lam _ hn, zero_mul]; exact continuous_const
  · simp_rw [term_lamC_eq_cexp lam _ hn]; fun_prop

/-! ### Integrating the explicit formula horizontally -/

/-- **The integrated explicit formula.**  For `½ < a ≤ b`, `t ≠ 0`, `L ≥ 0`:
`L ∫_a^b A(u + it) du = D(a + it) − D(b + it) − (A(b + it) − A(a + it)) − ∫_a^b E_L(u + it) du`. -/
theorem mul_integral_producerA_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {a b t L : ℝ}
    (ha : 1 / 2 < a) (hab : a ≤ b) (ht : t ≠ 0) (hL : 0 ≤ L) :
    L * ∫ u in a..b, producerA hW ((u : ℂ) + t * I) =
      producerPoly lam L ((a : ℂ) + t * I) - producerPoly lam L ((b : ℂ) + t * I) -
        (producerA hW ((b : ℂ) + t * I) - producerA hW ((a : ℂ) + t * I)) -
        ∫ u in a..b, producerE hW L ((u : ℂ) + t * I) := by
  have hb : 1 / 2 < b := lt_of_lt_of_le ha hab
  have hmem : ∀ u ∈ uIcc a b, 1 / 2 < u := fun u hu => by
    rw [uIcc_of_le hab] at hu; linarith [hu.1]
  have hAc := continuousOn_horizontal (continuousOn_producerA hW) ha hb ht
  have hDc := continuousOn_horizontal (continuousOn_producerDA hW) ha hb ht
  have hSc := (continuous_weighted_sum lam L t).continuousOn (s := uIcc a b)
  have hAi : IntervalIntegrable (fun u : ℝ => producerA hW ((u : ℂ) + t * I)) volume a b :=
    hAc.intervalIntegrable
  have hDi : IntervalIntegrable (fun u : ℝ => producerDA hW ((u : ℂ) + t * I)) volume a b :=
    hDc.intervalIntegrable
  have hSi := hSc.intervalIntegrable (μ := volume)
  -- the pointwise identity
  have hpt : ∀ u ∈ uIcc a b, producerE hW L ((u : ℂ) + t * I) =
      (∑' n : ℕ, LSeries.term (lamC lam) ((u : ℂ) + t * I) n *
        ((max (L - Real.log n) 0 : ℝ) : ℂ)) - L * producerA hW ((u : ℂ) + t * I) -
        producerDA hW ((u : ℂ) + t * I) := by
    intro u hu
    have hm := horizontal_mem_producerDomain (hmem u hu) ht
    rw [tsum_lamC_mul_max_eq_residue hW hm.1 hm.2 hL]
    ring
  -- FTC for `A`
  have hFTC : ∫ u in a..b, producerDA hW ((u : ℂ) + t * I) =
      producerA hW ((b : ℂ) + t * I) - producerA hW ((a : ℂ) + t * I) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => producerA hW ((u : ℂ) + t * I)) (fun u hu => ?_) hDi
    have hm := horizontal_mem_producerDomain (hmem u hu) ht
    have h := (hasDerivAt_producerA hW hm.1 hm.2).comp_add_const (u : ℂ) (t * I)
    exact (h.comp_ofReal (z := u))
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub (hSi.sub (hAi.const_mul _))
    hDi, intervalIntegral.integral_sub hSi (hAi.const_mul _), intervalIntegral.integral_const_mul,
    integral_weighted_sum_eq, hFTC]
  ring

/-- **The `E_L` integral.**  For `½ < σ₀ ≤ b`, `t ≠ 0`, `L > 0`:
`|∫_{σ₀}^b E_L(u + it) du| ≤ (e^{(1−σ₀)L} + e^{−σ₀L}(1 + (1 − e^{−2L})⁻¹))/(L t²) + e^{(½−σ₀)L} P/L`. -/
theorem norm_integral_producerE_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ₀ b t L : ℝ}
    (hσ₀ : 1 / 2 < σ₀) (hσ₀b : σ₀ ≤ b) (ht : t ≠ 0) (hL : 0 < L) :
    ‖∫ u in σ₀..b, producerE hW L ((u : ℂ) + t * I)‖ ≤
      (Real.exp ((1 - σ₀) * L) + Real.exp (-σ₀ * L) * (1 + (1 - Real.exp (-2 * L))⁻¹)) /
          (L * t ^ 2) +
        Real.exp ((1 / 2 - σ₀) * L) *
          (∫ r, ‖1 / (((σ₀ - 1 / 2 : ℝ) : ℂ) + t * I - I * r) ^ 2‖ ∂boundaryMeasure hW) / L := by
  set P : ℝ := ∫ r, ‖1 / (((σ₀ - 1 / 2 : ℝ) : ℂ) + t * I - I * r) ^ 2‖ ∂boundaryMeasure hW
    with hP
  have hP0 : 0 ≤ P := integral_nonneg fun _ => norm_nonneg _
  set K : ℝ := 1 + (1 - Real.exp (-2 * L))⁻¹ with hK
  have hq1 : Real.exp (-2 * L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - Real.exp (-2 * L) := by linarith
    positivity
  have hb : 1 / 2 < b := lt_of_lt_of_le hσ₀ hσ₀b
  have hmem : ∀ u ∈ uIcc σ₀ b, 1 / 2 < u := fun u hu => by
    rw [uIcc_of_le hσ₀b] at hu; linarith [hu.1]
  -- continuity of `E_L` along the segment
  have hEc : ContinuousOn (fun u : ℝ => producerE hW L ((u : ℂ) + t * I)) (uIcc σ₀ b) := by
    have hAc := continuousOn_horizontal (continuousOn_producerA hW) hσ₀ hb ht
    have hDc := continuousOn_horizontal (continuousOn_producerDA hW) hσ₀ hb ht
    have hSc := (continuous_weighted_sum lam L t).continuousOn (s := uIcc σ₀ b)
    refine ((hSc.sub ((continuousOn_const (c := (L : ℂ))).mul hAc)).sub hDc).congr fun u hu => ?_
    have hm := horizontal_mem_producerDomain (hmem u hu) ht
    show producerE hW L _ = (∑' n : ℕ, LSeries.term (lamC lam) ((u : ℂ) + t * I) n *
      ((max (L - Real.log n) 0 : ℝ) : ℂ)) - (L : ℂ) * producerA hW ((u : ℂ) + t * I) -
        producerDA hW ((u : ℂ) + t * I)
    rw [tsum_lamC_mul_max_eq_residue hW hm.1 hm.2 hL.le]
    ring
  set B : ℝ → ℝ := fun u => (Real.exp ((1 - u) * L) + Real.exp ((0 - u) * L) * K) / t ^ 2 +
    Real.exp ((1 / 2 - u) * L) * P with hB
  have hBc : Continuous B := by simp only [hB]; fun_prop
  have hle : ∀ u ∈ Icc σ₀ b, ‖producerE hW L ((u : ℂ) + t * I)‖ ≤ B u := by
    intro u hu
    have h := norm_producerE_le hW hσ₀ hu.1 ht hL
    simp only [hB, zero_sub]
    exact h
  calc ‖∫ u in σ₀..b, producerE hW L ((u : ℂ) + t * I)‖
      ≤ ∫ u in σ₀..b, ‖producerE hW L ((u : ℂ) + t * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hσ₀b
    _ ≤ ∫ u in σ₀..b, B u :=
        intervalIntegral.integral_mono_on hσ₀b hEc.norm.intervalIntegrable
          (hBc.intervalIntegrable _ _) hle
    _ = (∫ u in σ₀..b, Real.exp ((1 - u) * L)) / t ^ 2 +
          (∫ u in σ₀..b, Real.exp ((0 - u) * L)) * K / t ^ 2 +
          (∫ u in σ₀..b, Real.exp ((1 / 2 - u) * L)) * P := by
        simp only [hB]
        rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_div,
          intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
        ring
    _ ≤ (Real.exp ((1 - σ₀) * L) / L) / t ^ 2 + (Real.exp ((0 - σ₀) * L) / L) * K / t ^ 2 +
          (Real.exp ((1 / 2 - σ₀) * L) / L) * P := by
        have h1 := integral_exp_sub_mul_le 1 L σ₀ b hL
        have h2 := integral_exp_sub_mul_le 0 L σ₀ b hL
        have h3 := integral_exp_sub_mul_le (1 / 2) L σ₀ b hL
        have ht2 : 0 < t ^ 2 := by positivity
        gcongr
    _ = _ := by
        rw [zero_sub]
        field_simp

/-! ### The value at abscissa `2` -/

theorem norm_term_lamC_le (lam : ℕ → ℝ) {s : ℂ} {σ : ℝ} (hs : σ ≤ s.re) (n : ℕ) :
    ‖LSeries.term (lamC lam) s n‖ ≤ |lam n| / (n : ℝ) ^ σ := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hlam : ‖lamC lam n‖ ≤ |lam n| := by
      unfold lamC
      rw [Complex.norm_real, Real.norm_eq_abs]
      split_ifs
      · exact le_rfl
      · simp
    calc ‖lamC lam n‖ / (n : ℝ) ^ s.re ≤ |lam n| / (n : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right hlam (by positivity)
      _ ≤ |lam n| / (n : ℝ) ^ σ :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
            (Real.rpow_le_rpow_of_exponent_le hn1 hs)

theorem summable_norm_term_lamC {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ} {σ : ℝ}
    (hσ : 1 < σ) (hs : σ ≤ s.re) : Summable fun n => ‖LSeries.term (lamC lam) s n‖ :=
  (WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_term_lamC_le lam hs)

theorem tsum_norm_term_lamC_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ} {σ : ℝ}
    (hσ : 1 < σ) (hs : σ ≤ s.re) :
    ∑' n, ‖LSeries.term (lamC lam) s n‖ ≤ ∑' n : ℕ, |lam n| / (n : ℝ) ^ σ :=
  (summable_norm_term_lamC hW hσ hs).tsum_le_tsum (norm_term_lamC_le lam hs)
    (WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ)

/-- The coefficients `lam(n)/log n` of `log F_lam`. -/
def lamLogC (lam : ℕ → ℝ) (n : ℕ) : ℂ := lamC lam n / (Real.log n : ℂ)

theorem term_lamLogC (lam : ℕ → ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (lamLogC lam) s n = LSeries.term (lamC lam) s n / Real.log n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, lamLogC]
    ring

/-- **The base value.**  `|Σ lam(n) n^{−s}/log n − D(s)/L| ≤ Σ |lam(n)| n^{−2}/L` on `Re s = 2`:
the coefficient `1/log n − (L − log n)⁺/(L log n)` lies in `[0, 1/L]`. -/
theorem norm_LSeries_lamLogC_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    ‖LSeries (lamLogC lam) ((2 : ℂ) + t * I) - producerPoly lam L ((2 : ℂ) + t * I) / L‖ ≤
      (∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) / L := by
  set s : ℂ := (2 : ℂ) + t * I with hs
  have hsre : (2 : ℝ) ≤ s.re := by simp [hs]
  set T : ℕ → ℂ := fun n => LSeries.term (lamC lam) s n with hT
  set c : ℕ → ℝ := fun n => 1 / Real.log n - max (L - Real.log n) 0 / (Real.log n * L) with hc
  have hcoef : ∀ n, ‖T n * (c n : ℂ)‖ ≤ ‖T n‖ / L := by
    intro n
    rcases lt_or_ge n 2 with hn | hn
    · simp [hT, term_lamC_eq_zero_of_lt lam _ hn]
    · have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      have hm1 : max (L - Real.log n) 0 ≤ L := max_le (by linarith) hL.le
      have hm2 : L - Real.log n ≤ max (L - Real.log n) 0 := le_max_left _ _
      have hcn : c n = (L - max (L - Real.log n) 0) / (Real.log n * L) := by
        simp only [hc]; field_simp
      have hc0 : 0 ≤ c n := by
        rw [hcn]; exact div_nonneg (by linarith) (by positivity)
      have hc1 : c n ≤ 1 / L := by
        rw [hcn, div_le_div_iff₀ (by positivity) hL]
        nlinarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hc1 (norm_nonneg _)
  have hsT := summable_norm_term_lamC hW (by norm_num : (1 : ℝ) < 2) hsre
  have hsum1 : Summable fun n => T n / Real.log n := by
    refine Summable.of_norm_bounded (hsT.div_const (Real.log 2)) fun n => ?_
    rcases lt_or_ge n 2 with hn | hn
    · simp [hT, term_lamC_eq_zero_of_lt lam _ hn]
    · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl2.trans_le hl)]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hl2 hl
  have hsum2 : Summable fun n => T n * ((max (L - Real.log n) 0 : ℝ) : ℂ) / Real.log n / L := by
    refine summable_of_ne_finset_zero (s := Finset.range ⌈Real.exp L⌉₊) fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    rw [max_sub_log_eq_zero hn]
    simp
  have hdiff : LSeries (lamLogC lam) s - producerPoly lam L s / L = ∑' n, T n * (c n : ℂ) := by
    have h1 : LSeries (lamLogC lam) s = ∑' n, T n / Real.log n := by
      unfold LSeries
      exact tsum_congr fun n => term_lamLogC lam s n
    have h2 : producerPoly lam L s / L =
        ∑' n, T n * ((max (L - Real.log n) 0 : ℝ) : ℂ) / Real.log n / L := by
      unfold producerPoly
      rw [tsum_div_const]
    rw [h1, h2, ← hsum1.tsum_sub hsum2]
    refine tsum_congr fun n => ?_
    simp only [hc]
    rcases lt_or_ge n 2 with hn | hn
    · simp [hT, term_lamC_eq_zero_of_lt lam _ hn]
    · have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      have hlC : (Real.log n : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
      have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      push_cast
      field_simp
  rw [hdiff]
  have hsc : Summable fun n => ‖T n * (c n : ℂ)‖ :=
    (hsT.div_const L).of_nonneg_of_le (fun _ => norm_nonneg _) hcoef
  calc ‖∑' n, T n * (c n : ℂ)‖ ≤ ∑' n, ‖T n * (c n : ℂ)‖ := norm_tsum_le_tsum_norm hsc
    _ ≤ ∑' n, ‖T n‖ / L := hsc.tsum_le_tsum hcoef (hsT.div_const L)
    _ = (∑' n, ‖T n‖) / L := tsum_div_const
    _ ≤ _ := div_le_div_of_nonneg_right
        (tsum_norm_term_lamC_le hW (by norm_num : (1 : ℝ) < 2) hsre) hL.le

theorem norm_producerA_two_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    ‖producerA hW ((2 : ℂ) + t * I)‖ ≤ ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) := by
  have hsre : (2 : ℝ) ≤ ((2 : ℂ) + t * I).re := by simp
  rw [producerA_eq_LSeries hW (by simp)]
  exact (norm_tsum_le_tsum_norm (summable_norm_term_lamC hW (by norm_num) hsre)).trans
    (tsum_norm_term_lamC_le hW (by norm_num) hsre)

theorem integral_norm_inv_sub_I_mul_sq_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {w : ℂ}
    (hw : 0 < w.re) :
    ∫ r, ‖1 / (w - I * r) ^ 2‖ ∂boundaryMeasure hW = (herglotzFunction hW w).re / w.re := by
  simp_rw [norm_inv_sub_I_mul_sq_eq hw]
  rw [integral_div, re_integral_herglotzKernel hW hw]

/-! ### Soundararajan's inequality -/

/-- `log F_lam(σ + it)`: the value `Σ lam(n) n^{−2−it}/log n` at abscissa `2`, continued to the left
along the horizontal line by `∂_σ log F_lam = −A_lam`. -/
def producerLogZeta {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (σ t : ℝ) : ℂ :=
  LSeries (lamLogC lam) ((2 : ℂ) + t * I) + ∫ u in σ..2, producerA hW ((u : ℂ) + t * I)

/-- The archimedean part `U(z) = ½ψ(z/2) − ½ log π + 1/z + 1/(z − 1)`. -/
def archU (z : ℂ) : ℂ := zetaArchimedeanDatum z + 1 / (z - 1)

theorem archU_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (z : ℂ) :
    archU z = producerA hW z + weilContinuation hW z := by
  unfold archU producerA; ring

/-- **Soundararajan's inequality for every Weil-positive system.**  Let `t ≠ 0`, `L > 0`,
`½ < σ ≤ σ₀ ≤ 2`, and `λ = (σ₀ − ½)L` with `e^{−λ} ≤ λ`.  Then

`Re log F_lam(σ + it) ≤ Re D_L(σ₀ + it)/L + Re U(σ₀ + it)/L + ∫_σ^{σ₀} Re U(u + it) du`
`    + (2 Σ |lam(n)|/n² + (e^{(1−σ₀)L} + e^{−σ₀L}(1 + (1 − e^{−2L})⁻¹))/(L t²))/L`,

with `D_L(s) = Σ lam(n) n^{−s} (L − log n)⁺/log n`.  For `lam = Λ` this is Soundararajan's
inequality, which needs RH for `ζ`; on the Weil cone `Re Φ_lam ≥ 0` replaces RH. -/
theorem re_producerLogZeta_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ σ₀ t L : ℝ}
    (hσ : 1 / 2 < σ) (hσσ₀ : σ ≤ σ₀) (hσ₀ : σ₀ ≤ 2) (ht : t ≠ 0) (hL : 0 < L)
    (hlam : Real.exp (-((σ₀ - 1 / 2) * L)) ≤ (σ₀ - 1 / 2) * L) :
    (producerLogZeta hW σ t).re ≤
      (producerPoly lam L ((σ₀ : ℂ) + t * I)).re / L + (archU ((σ₀ : ℂ) + t * I)).re / L +
        (∫ u in σ..σ₀, (archU ((u : ℂ) + t * I)).re) +
        (2 * (∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) +
          (Real.exp ((1 - σ₀) * L) + Real.exp (-σ₀ * L) * (1 + (1 - Real.exp (-2 * L))⁻¹)) /
            (L * t ^ 2)) / L := by
  have hσ₀' : 1 / 2 < σ₀ := lt_of_lt_of_le hσ hσσ₀
  set z : ℝ → ℂ := fun u => (u : ℂ) + t * I with hz
  set M₂ : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) with hM₂
  set Ep : ℝ := (Real.exp ((1 - σ₀) * L) + Real.exp (-σ₀ * L) *
    (1 + (1 - Real.exp (-2 * L))⁻¹)) / (L * t ^ 2) with hEp
  -- continuity along the segment
  have hAc := continuousOn_horizontal (continuousOn_producerA hW) hσ (by norm_num : (1 / 2 : ℝ) < 2) ht
  have hWc : ContinuousOn (fun u : ℝ => weilContinuation hW ((u : ℂ) + t * I)) (uIcc σ 2) := by
    refine (differentiableOn_weilContinuation hW).continuousOn.comp (by fun_prop) fun u hu => ?_
    have : 1 / 2 < u := by
      rw [uIcc_of_le (by linarith)] at hu; linarith [hu.1]
    show 1 / 2 < ((u : ℂ) + t * I).re
    simpa using this
  have hsub : uIcc σ σ₀ ⊆ uIcc σ 2 := uIcc_subset_uIcc left_mem_uIcc
    (by rw [uIcc_of_le (by linarith)]; exact ⟨hσσ₀, hσ₀⟩)
  have hsub2 : uIcc σ₀ 2 ⊆ uIcc σ 2 := uIcc_subset_uIcc
    (by rw [uIcc_of_le (by linarith)]; exact ⟨hσσ₀, hσ₀⟩) right_mem_uIcc
  have hI1 : IntervalIntegrable (fun u => producerA hW (z u)) volume σ σ₀ :=
    (hAc.mono hsub).intervalIntegrable
  have hI2 : IntervalIntegrable (fun u => producerA hW (z u)) volume σ₀ 2 :=
    (hAc.mono hsub2).intervalIntegrable
  have hUc : ContinuousOn (fun u : ℝ => archU (z u)) (uIcc σ σ₀) := by
    refine ((hAc.add hWc).mono hsub).congr fun u _ => ?_
    simp only [hz, Pi.add_apply]
    rw [archU_eq hW]
  -- the integrated explicit formula on `[σ₀, 2]`
  have hEF := mul_integral_producerA_eq hW hσ₀' hσ₀ ht hL.le
  have hA2 : ∫ u in σ₀..2, producerA hW (z u) =
      (producerPoly lam L (z σ₀) - producerPoly lam L (z 2) -
        (producerA hW (z 2) - producerA hW (z σ₀)) -
        ∫ u in σ₀..2, producerE hW L (z u)) / L := by
    rw [eq_div_iff (by exact_mod_cast hL.ne'), mul_comm]
    exact hEF
  -- the `E_L` bound with the Poisson identity
  set w₀ : ℂ := z σ₀ - 1 / 2 with hw₀
  have hw₀re : w₀.re = σ₀ - 1 / 2 := by simp [hw₀, hz]
  have hw₀pos : 0 < w₀.re := by rw [hw₀re]; linarith
  have hw₀' : (((σ₀ - 1 / 2 : ℝ) : ℂ) + t * I) = w₀ := by simp only [hw₀, hz]; push_cast; ring
  have hEb := norm_integral_producerE_le hW hσ₀' hσ₀ ht hL
  simp_rw [hw₀'] at hEb
  rw [integral_norm_inv_sub_I_mul_sq_eq hW hw₀pos, hw₀re] at hEb
  set ReH : ℝ := (herglotzFunction hW w₀).re with hReH
  have hReH0 : 0 ≤ ReH := re_herglotzFunction_nonneg hW hw₀pos
  have hlpos : 0 < (σ₀ - 1 / 2) * L := by have := sub_pos.mpr hσ₀'; positivity
  have hfac : Real.exp ((1 / 2 - σ₀) * L) * (ReH / (σ₀ - 1 / 2)) / L ≤ ReH := by
    have e : Real.exp ((1 / 2 - σ₀) * L) * (ReH / (σ₀ - 1 / 2)) / L =
        ReH * (Real.exp (-((σ₀ - 1 / 2) * L)) / ((σ₀ - 1 / 2) * L)) := by
      rw [show (1 / 2 - σ₀) * L = -((σ₀ - 1 / 2) * L) by ring]
      field_simp
    rw [e]
    exact mul_le_of_le_one_right hReH0 ((div_le_one hlpos).mpr hlam)
  -- real parts
  have hRA : (producerA hW (z σ₀)).re = (archU (z σ₀)).re - ReH := by
    rw [re_producerA, hReH, hw₀]; rfl
  have hEre : -(∫ u in σ₀..2, producerE hW L (z u)).re ≤ Ep + ReH := by
    have h1 := Complex.abs_re_le_norm (∫ u in σ₀..2, producerE hW L (z u))
    have h2 := neg_abs_le (∫ u in σ₀..2, producerE hW L (z u)).re
    have h3 : ‖∫ u in σ₀..2, producerE hW L (z u)‖ ≤ Ep + ReH := hEb.trans (by linarith)
    linarith
  have hbase := norm_LSeries_lamLogC_sub_le hW hL t
  have hbase' : (LSeries (lamLogC lam) ((2 : ℂ) + t * I)).re -
      (producerPoly lam L (z 2)).re / L ≤ M₂ / L := by
    have h := (Complex.re_le_norm _).trans hbase
    simp only [hz] at h ⊢
    rw [Complex.sub_re, Complex.div_ofReal_re] at h
    push_cast at h ⊢
    linarith
  have hA2b : -(producerA hW (z 2)).re ≤ M₂ := by
    have h1 := norm_producerA_two_le hW t
    have h2 := Complex.abs_re_le_norm (producerA hW (z 2))
    have h3 := neg_abs_le (producerA hW (z 2)).re
    simp only [hz] at h2 h3 ⊢
    push_cast at h2 h3 ⊢
    linarith
  -- the left segment
  have hleft : (∫ u in σ..σ₀, producerA hW (z u)).re ≤ ∫ u in σ..σ₀, (archU (z u)).re := by
    have hre : (∫ u in σ..σ₀, producerA hW (z u)).re = ∫ u in σ..σ₀, (producerA hW (z u)).re :=
      (Complex.reCLM.intervalIntegral_comp_comm hI1).symm
    rw [hre]
    refine intervalIntegral.integral_mono_on hσσ₀
      (Complex.continuous_re.comp_continuousOn (hAc.mono hsub)).intervalIntegrable
      (Complex.continuous_re.comp_continuousOn hUc).intervalIntegrable fun u hu => ?_
    have hu : 1 / 2 < u := by linarith [hu.1]
    have hpos : 0 < (z u - 1 / 2).re := by simp [hz]; linarith
    rw [re_producerA]
    have := re_herglotzFunction_nonneg hW hpos
    unfold archU
    linarith
  -- assemble
  have hsplit : ∫ u in σ..2, producerA hW (z u) =
      (∫ u in σ..σ₀, producerA hW (z u)) + ∫ u in σ₀..2, producerA hW (z u) :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  have hdef : producerLogZeta hW σ t = LSeries (lamLogC lam) ((2 : ℂ) + t * I) +
      ∫ u in σ..2, producerA hW (z u) := rfl
  rw [hdef, hsplit, hA2, Complex.add_re, Complex.add_re, Complex.div_ofReal_re]
  simp only [Complex.sub_re]
  have hLinv : 0 < 1 / L := by positivity
  have key : ((producerPoly lam L (z σ₀)).re - (producerPoly lam L (z 2)).re -
      ((producerA hW (z 2)).re - (producerA hW (z σ₀)).re) -
        (∫ u in σ₀..2, producerE hW L (z u)).re) / L ≤
      (producerPoly lam L (z σ₀)).re / L - (producerPoly lam L (z 2)).re / L + M₂ / L +
        (archU (z σ₀)).re / L + Ep / L := by
    rw [div_le_iff₀ hL]
    have e : ((producerPoly lam L (z σ₀)).re / L - (producerPoly lam L (z 2)).re / L + M₂ / L +
        (archU (z σ₀)).re / L + Ep / L) * L = (producerPoly lam L (z σ₀)).re -
          (producerPoly lam L (z 2)).re + M₂ + (archU (z σ₀)).re + Ep := by
      field_simp
    rw [e]
    linarith
  have e2 : (2 * M₂ + Ep) / L = M₂ / L + M₂ / L + Ep / L := by ring
  rw [e2]
  linarith

theorem logMul_lamLogC (lam : ℕ → ℝ) : LSeries.logMul (lamLogC lam) = lamC lam := by
  funext n
  rw [LSeries.logMul, lamLogC]
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp [lamC]
  · have hl : (Real.log n : ℂ) ≠ 0 := by
      exact_mod_cast (Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)).ne'
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
    field_simp

theorem abscissaOfAbsConv_lamLogC_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    LSeries.abscissaOfAbsConv (lamLogC lam) ≤ 1 := by
  have h := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := lamLogC lam)
    (x := 1) fun y hy => by
      have hsT := summable_norm_term_lamC hW (s := (y : ℂ)) hy (by simp)
      refine Summable.of_norm_bounded (hsT.div_const (Real.log 2)) fun n => ?_
      rw [term_lamLogC]
      rcases lt_or_ge n 2 with hn | hn
      · simp [term_lamC_eq_zero_of_lt lam _ hn]
      · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl2.trans_le hl)]
        exact div_le_div_of_nonneg_left (norm_nonneg _) hl2 hl
  exact_mod_cast h

/-- **Consistency.**  To the right of `Re s = 1`, `log F_lam(σ + it)` is the Dirichlet series
`Σ lam(n) n^{−σ−it}/log n`. -/
theorem producerLogZeta_eq_LSeries {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ}
    (hσ : 1 < σ) (t : ℝ) :
    producerLogZeta hW σ t = LSeries (lamLogC lam) ((σ : ℂ) + t * I) := by
  have hgt : ∀ u ∈ uIcc σ 2, 1 < u := fun u hu => by
    rcases Set.mem_uIcc.mp hu with h | h
    · linarith [h.1]
    · linarith [h.1]
  have hdom : ∀ u : ℝ, 1 < u → (u : ℂ) + t * I ∈ producerDomain := fun u hu =>
    ⟨by simp; linarith, fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith⟩
  have hderiv : ∀ u ∈ uIcc σ 2, HasDerivAt (fun u : ℝ => -LSeries (lamLogC lam) ((u : ℂ) + t * I))
      (producerA hW ((u : ℂ) + t * I)) u := by
    intro u hu
    have hu1 := hgt u hu
    have habs : LSeries.abscissaOfAbsConv (lamLogC lam) < (((u : ℂ) + t * I).re : ℝ) := by
      refine (abscissaOfAbsConv_lamLogC_le hW).trans_lt ?_
      have : ((u : ℂ) + t * I).re = u := by simp
      rw [this]
      exact_mod_cast hu1
    have h := ((LSeries_hasDerivAt habs).comp_add_const (u : ℂ) (t * I)).comp_ofReal (z := u)
    rw [logMul_lamLogC] at h
    have h2 := h.neg
    rw [neg_neg, ← producerA_eq_LSeries hW (by simpa using hu1)] at h2
    exact h2
  have hcont : ContinuousOn (fun u : ℝ => producerA hW ((u : ℂ) + t * I)) (uIcc σ 2) :=
    (continuousOn_producerA hW).comp (by fun_prop) fun u hu => hdom u (hgt u hu)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  unfold producerLogZeta
  rw [hFTC, show ((2 : ℝ) : ℂ) = 2 by norm_num]
  ring

end RHTower.WeilSpectral

end
