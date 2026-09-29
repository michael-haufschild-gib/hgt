import GaloisForLFunctions.RHTower.ThetaEndpointMomentFiltration

/-!
# Positive local moduli of the theta source with a fixed real divisor

Let `P` be the off-line divisor polynomial of `F = XiC` (finite configuration, first-quadrant
multiplicity `M`), `P(0) = 1`, of degree `4M`, whose zeros with multiplicity are exactly the
off-line zeros of `F`.

* Every real even polynomial `E(z²)` of degree `≤ 4M` is the quotient `û P / F` of a divisor-keeping
  source `u`, and `lim_{|x|→∞} u/k = lim_{|z|→∞} E(z²)/P(z)`.
* **Positive deformations.**  For `u ∈ W_N` and small `ε`, `k + εu` is positive, its transform is
  `F` times the positive real multiplier `1 + ε E(x²)/P(x)` on the real axis, it has exactly the real
  zeros of `F` with the same multiplicities, and the same even moments of orders `0, …, 2N`.
* **The last direction.**  `û_* P = F z^{4M}`: for small `t > 0`, `k + t u_*` is positive with
  transform `F (P + t z^{4M}) / P`, keeps all real zeros and the first `2M` even moments, and its
  non-real zeros are exactly those of `P + t z^{4M}`; no off-line zero of `F` survives.
* **A hidden direction from one off-line zero.**  A single off-line zero gives a nonzero
  divisor-keeping source with zero mass, unchanged leading theta tail and nonzero second moment.
-/
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## The polynomial quotient at infinity -/

theorem tendsto_inv_cocompact_complex : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
  rw [← Metric.cobounded_eq_cocompact]
  exact tendsto_inv₀_cobounded

theorem eventually_ne_zero_cocompact_complex : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
  (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact

/-- `P_L(z) / z^{2|L|} → ∏ (−β²)⁻¹` as `|z| → ∞`. -/
theorem tendsto_listDivisor_div_pow (L : List ℂ) :
    Tendsto (fun z => listDivisor L z / z ^ (2 * L.length)) (cocompact ℂ)
      (𝓝 ((L.map fun β : ℂ => -β ^ 2).prod)⁻¹) := by
  induction L with
  | nil =>
    simp only [listDivisor_nil, List.length_nil, mul_zero, pow_zero, div_one, List.map_nil,
      List.prod_nil, inv_one]
    exact tendsto_const_nhds
  | cons β L ih =>
    have h1 : Tendsto (fun z : ℂ => (z⁻¹) ^ 2 - (β ^ 2)⁻¹) (cocompact ℂ) (𝓝 (-(β ^ 2)⁻¹)) := by
      simpa using (tendsto_inv_cocompact_complex.pow 2).sub_const (β ^ 2)⁻¹
    have h := h1.mul ih
    rw [neg_inv, ← mul_inv] at h
    rw [List.map_cons, List.prod_cons]
    refine h.congr' ?_
    filter_upwards [eventually_ne_zero_cocompact_complex] with z hz
    rw [listDivisor_cons, List.length_cons]
    field_simp
    ring

/-- `E(z²) / z^{2n} → e_n` as `|z| → ∞` when `deg e ≤ n`. -/
theorem tendsto_eval_sq_div_pow (e : Polynomial ℂ) {n : ℕ} (he : e.natDegree ≤ n) :
    Tendsto (fun z => e.eval (z ^ 2) / z ^ (2 * n)) (cocompact ℂ) (𝓝 (e.coeff n)) := by
  set q : ℂ → ℂ := fun w => ∑ j ∈ Finset.range (n + 1), e.coeff j * w ^ (2 * (n - j))
  have hq : Continuous q := by fun_prop
  have h0 : q 0 = e.coeff n := by
    simp only [q]
    rw [Finset.sum_eq_single n (fun j hj hjn => by
      have := Finset.mem_range.1 hj
      rw [zero_pow (by omega), mul_zero]) (fun h => absurd (Finset.self_mem_range_succ n) h)]
    simp
  have h := (hq.tendsto 0).comp tendsto_inv_cocompact_complex
  rw [h0] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_zero_cocompact_complex] with z hz
  simp only [Function.comp, q]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le he), Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn := Finset.mem_range.1 hj
  have hsplit : z ^ (2 * n) = (z ^ 2) ^ j * z ^ (2 * (n - j)) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [hsplit, inv_pow]
  field_simp

/-- `E(z²) / P_L(z) → e_{|L|} ∏(−β²)` as `|z| → ∞`. -/
theorem tendsto_eval_sq_div_listDivisor (e : Polynomial ℂ) (L : List ℂ)
    (he : e.natDegree ≤ L.length) (hL : (L.map fun β : ℂ => -β ^ 2).prod ≠ 0) :
    Tendsto (fun z => e.eval (z ^ 2) / listDivisor L z) (cocompact ℂ)
      (𝓝 (e.coeff L.length * (L.map fun β : ℂ => -β ^ 2).prod)) := by
  have h := (tendsto_eval_sq_div_pow e he).div (tendsto_listDivisor_div_pow L) (inv_ne_zero hL)
  rw [div_inv_eq_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_zero_cocompact_complex] with z hz
  rw [Pi.div_apply, div_div_div_cancel_right₀ (pow_ne_zero _ hz)]

theorem exists_norm_le_of_continuous_of_tendsto_cocompact {f : ℝ → ℂ} (hf : Continuous f) {a : ℂ}
    (h : Tendsto f (cocompact ℝ) (𝓝 a)) : ∃ B, ∀ x, ‖f x‖ ≤ B := by
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 (h (Metric.ball_mem_nhds a one_pos))
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B (‖a‖ + 1), fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hB x hx).trans (le_max_left _ _)
  · have h1 : f x ∈ Metric.ball a 1 := hKs hx
    rw [Metric.mem_ball, dist_eq_norm] at h1
    refine le_trans ?_ (le_max_right _ _)
    calc ‖f x‖ = ‖(f x - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ ‖f x - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ ‖a‖ + 1 := by linarith

theorem eval_map_ofReal_sq (e : Polynomial ℝ) (x : ℝ) :
    (e.map (algebraMap ℝ ℂ)).eval ((x : ℂ) ^ 2) = ((e.eval (x ^ 2) : ℝ) : ℂ) := by
  rw [Polynomial.eval_map, ← Complex.ofReal_pow, ← Complex.coe_algebraMap,
    Polynomial.eval₂_at_apply]

theorem differentiable_eval_map_sq (e : Polynomial ℝ) :
    Differentiable ℂ fun z : ℂ => (e.map (algebraMap ℝ ℂ)).eval (z ^ 2) :=
  (e.map (algebraMap ℝ ℂ)).differentiable.comp (differentiable_pow 2)

theorem expMomentSource_thetaCuspFullSource : ExpMomentSource fun x => (thetaCuspFullSource x : ℂ) :=
  expMomentSource_ofReal_of_le contDiff_thetaCuspFullSource.continuous (C := 1)
    fun x => by rw [abs_of_pos (thetaCuspFullSource_pos x), one_mul]

/-- The transform of `k + εu` is `F + ε û`. -/
theorem sourceTransform_add_smul {u : ℝ → ℝ} (huc : Continuous u) {Cu : ℝ}
    (huC : ∀ x, |u x| ≤ Cu * thetaCuspFullSource x) (ε : ℝ) (z : ℂ) :
    sourceTransform (fun x => ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) z =
      XiC z + ε * sourceTransform (fun x => (u x : ℂ)) z := by
  have h : (fun x => ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) =
      fun x => (thetaCuspFullSource x : ℂ) + (ε : ℂ) * (u x : ℂ) := by
    funext x; push_cast; ring
  rw [h, sourceTransform_add expMomentSource_thetaCuspFullSource
    ((expMomentSource_ofReal_of_le huc huC).const_mul _), sourceTransform_const_mul]
  exact congrArg (· + _) (sourceTransform_thetaSourceC z)

/-- The same first even moments after adding a direction with vanishing moments. -/
theorem integral_pow_mul_add_smul {u : ℝ → ℝ} (huc : Continuous u) {Cu : ℝ}
    (huC : ∀ x, |u x| ≤ Cu * thetaCuspFullSource x) (ε : ℝ) {n : ℕ}
    (hn : ∫ x, x ^ n * u x = 0) :
    ∫ x, x ^ n * (thetaCuspFullSource x + ε * u x) = ∫ x, x ^ n * thetaCuspFullSource x := by
  have hk := integrable_pow_mul_of_le contDiff_thetaCuspFullSource.continuous (C := 1)
    (fun x => by rw [abs_of_pos (thetaCuspFullSource_pos x), one_mul]) n
  have hu := (integrable_pow_mul_of_le huc huC n).const_mul ε
  simp only [mul_add]
  have h2 : ∫ x, x ^ n * (ε * u x) = ε * ∫ x, x ^ n * u x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [integral_add hk (hu.congr (Eventually.of_forall fun x => by simp only; ring)), h2, hn,
    mul_zero, add_zero]

/-- **Positive deformations along a divisor-keeping direction.**  If `û P_L = F E(z²)` with
`deg E ≤ |L|`, then for small `ε` the source `k + εu` is positive, its transform is `F` times a
positive real multiplier `1 + ε E(x²)/P_L(x)` on the real axis, and it has exactly the real zeros of
`F` with the same multiplicities. -/
theorem positive_deformation_of_mul_eq {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros)
    {u : ℝ → ℝ} (huc : Continuous u) {Cu : ℝ} (huC : ∀ x, |u x| ≤ Cu * thetaCuspFullSource x)
    {e : Polynomial ℝ} (he : e.natDegree ≤ (quadrantListOf l).length)
    (heT : ∀ z, sourceTransform (fun x => (u x : ℂ)) z * listDivisor (quadrantListOf l) z =
      XiC z * (e.map (algebraMap ℝ ℂ)).eval (z ^ 2)) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| < ε₀ →
      (∀ x, 0 < thetaCuspFullSource x + ε * u x) ∧
      (∀ z, sourceTransform (fun x => ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) z *
          listDivisor (quadrantListOf l) z =
        XiC z * (listDivisor (quadrantListOf l) z + ε * (e.map (algebraMap ℝ ℂ)).eval (z ^ 2))) ∧
      (∀ x : ℝ, ∃ m : ℝ, 0 < m ∧
        sourceTransform (fun x => ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) x = m * XiC x) ∧
      ∀ γ : ℝ, analyticOrderAt (sourceTransform fun x =>
        ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) γ = analyticOrderAt XiC γ := by
  obtain ⟨r, hr0, hr⟩ := prod_neg_sq_quadrantListOf hl
  set P := listDivisor (quadrantListOf l)
  set E : ℂ → ℂ := fun z => (e.map (algebraMap ℝ ℂ)).eval (z ^ 2)
  have hPd : Differentiable ℂ P := differentiable_listDivisor _
  have hEd : Differentiable ℂ E := differentiable_eval_map_sq e
  have hg : Continuous fun x : ℝ => E x / P x :=
    (hEd.continuous.comp Complex.continuous_ofReal).div (hPd.continuous.comp Complex.continuous_ofReal)
      fun x => listDivisor_quadrantListOf_ofReal_ne_zero hl x
  have hlim := (tendsto_eval_sq_div_listDivisor (e.map (algebraMap ℝ ℂ)) (quadrantListOf l)
    (Polynomial.natDegree_map_le.trans he) (by rw [hr]; exact_mod_cast hr0.ne')).comp
      (Complex.isometry_ofReal.isClosedEmbedding.tendsto_cocompact)
  obtain ⟨B, hB⟩ := exists_norm_le_of_continuous_of_tendsto_cocompact hg hlim
  refine ⟨1 / (1 + |Cu| + |B|), by positivity, fun ε hε => ?_⟩
  have hε' : |ε| * (1 + |Cu| + |B|) < 1 := by
    rwa [lt_div_iff₀ (by positivity)] at hε
  have hεC : |ε| * |Cu| < 1 := by nlinarith [abs_nonneg ε, abs_nonneg Cu, abs_nonneg B]
  have hεB : |ε| * |B| < 1 := by nlinarith [abs_nonneg ε, abs_nonneg Cu, abs_nonneg B]
  have hT := sourceTransform_add_smul huc huC ε
  have hid : ∀ z, sourceTransform (fun x => ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) z * P z =
      XiC z * (P z + ε * E z) := fun z => by
    rw [hT, add_mul, mul_assoc, heT]; ring
  -- the real multiplier
  have hmult : ∀ x : ℝ, ∃ ρ : ℝ, 0 < ρ ∧ P x = ρ ∧ 0 < 1 + ε * (e.eval (x ^ 2) / ρ) := by
    intro x
    obtain ⟨ρ, hρ, hPx⟩ := listDivisor_quadrantListOf_ofReal hl x
    replace hPx : P x = ρ := hPx
    refine ⟨ρ, hρ, hPx, ?_⟩
    have hbx := hB x
    simp only [E] at hbx
    rw [eval_map_ofReal_sq, hPx, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs] at hbx
    have h1 : |ε * (e.eval (x ^ 2) / ρ)| ≤ |ε| * |B| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbx.trans (le_abs_self B)) (abs_nonneg ε)
    have := neg_abs_le (ε * (e.eval (x ^ 2) / ρ))
    linarith
  refine ⟨fun x => ?_, hid, fun x => ?_, fun γ => ?_⟩
  · have hk := thetaCuspFullSource_pos x
    have h1 : |ε * u x| ≤ |ε| * (|Cu| * thetaCuspFullSource x) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((huC x).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) hk.le)) (abs_nonneg _)
    have h2 := neg_abs_le (ε * u x)
    have h3 : 0 < thetaCuspFullSource x * (1 - |ε| * |Cu|) := mul_pos hk (by linarith)
    nlinarith
  · obtain ⟨ρ, hρ, hPx, hm⟩ := hmult x
    refine ⟨_, hm, mul_right_cancel₀ (show P x ≠ 0 by rw [hPx]; exact_mod_cast hρ.ne') ?_⟩
    rw [hid, hPx]
    simp only [E]
    rw [eval_map_ofReal_sq]
    have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    push_cast
    field_simp
  · obtain ⟨ρ, hρ, hPx, hm⟩ := hmult γ
    have hU := (expMomentSource_ofReal_of_le (u := fun x => thetaCuspFullSource x + ε * u x)
      (contDiff_thetaCuspFullSource.continuous.add (continuous_const.mul huc)) (C := 1 + |ε| * |Cu|)
      (fun x => by
        have hk := thetaCuspFullSource_pos x
        have h1 : |ε * u x| ≤ |ε| * (|Cu| * thetaCuspFullSource x) := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((huC x).trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) hk.le)) (abs_nonneg _)
        calc |thetaCuspFullSource x + ε * u x| ≤ |thetaCuspFullSource x| + |ε * u x| :=
              abs_add_le _ _
          _ ≤ thetaCuspFullSource x + |ε| * (|Cu| * thetaCuspFullSource x) := by
              rw [abs_of_pos hk]; linarith
          _ = (1 + |ε| * |Cu|) * thetaCuspFullSource x := by ring)).differentiable_sourceTransform
    have h1 := congrArg (fun f => analyticOrderAt f (γ : ℂ))
      (show (sourceTransform fun x => ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) * P =
        XiC * fun z => P z + ε * E z from funext hid)
    have hQ : (fun z => P z + ε * E z) (γ : ℂ) ≠ 0 := by
      simp only [E]
      rw [hPx, eval_map_ofReal_sq]
      have : (ρ : ℂ) + (ε : ℂ) * ((e.eval (γ ^ 2) : ℝ) : ℂ) =
          ((ρ * (1 + ε * (e.eval (γ ^ 2) / ρ)) : ℝ) : ℂ) := by
        have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
        push_cast; field_simp
      rw [this]
      exact_mod_cast (mul_pos hρ hm).ne'
    have hQd : Differentiable ℂ fun z => P z + ε * E z := hPd.add (hEd.const_mul _)
    rw [analyticOrderAt_mul (hU.analyticAt _) (hPd.analyticAt _),
      analyticOrderAt_mul (XiC_differentiable.analyticAt _) (hQd.analyticAt _),
      (hPd.analyticAt _).analyticOrderAt_eq_zero.2 (listDivisor_quadrantListOf_ofReal_ne_zero hl γ),
      (hQd.analyticAt _).analyticOrderAt_eq_zero.2 hQ, add_zero, add_zero] at h1
    exact h1

/-- `P_L` is a polynomial of degree `2|L|` in `z`. -/
theorem exists_polynomial_listDivisor (L : List ℂ) (hL : ∀ β ∈ L, β ≠ 0) :
    ∃ Q : Polynomial ℂ, Q ≠ 0 ∧ Q.natDegree = 2 * L.length ∧ ∀ z, Q.eval z = listDivisor L z := by
  induction L with
  | nil => exact ⟨1, one_ne_zero, by simp, fun z => by simp [listDivisor_nil]⟩
  | cons β L ih =>
    obtain ⟨Q, hQ0, hQd, hQe⟩ := ih fun b hb => hL b (List.mem_cons_of_mem _ hb)
    have hβ : (β ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 (hL β List.mem_cons_self))
    set A : Polynomial ℂ := 1 - Polynomial.C (β ^ 2)⁻¹ * Polynomial.X ^ 2
    have hAd : A.natDegree = 2 := by
      rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by
        rw [Polynomial.natDegree_one, Polynomial.natDegree_C_mul_X_pow 2 _ hβ]; norm_num),
        Polynomial.natDegree_C_mul_X_pow 2 _ hβ]
    have hA0 : A ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hAd; exact absurd hAd (by norm_num)
    refine ⟨A * Q, mul_ne_zero hA0 hQ0, by
      rw [Polynomial.natDegree_mul hA0 hQ0, hAd, hQd, List.length_cons]; ring, fun z => ?_⟩
    rw [Polynomial.eval_mul, hQe, listDivisor_cons]
    simp only [A, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring

theorem im_ne_zero_of_mem_quadrantListOf {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros)
    {β : ℂ} (hβ : β ∈ quadrantListOf l) : β.im ≠ 0 := by
  obtain ⟨α, hα, h | h⟩ := mem_quadrantListOf hβ <;> rw [h]
  · exact (hl α hα).2.1.ne'
  · simpa using (hl α hα).2.1.ne'

/-! ## Finite off-line configurations -/

section FiniteDefect

variable (hfin : xiQuadrantZeros.Finite)

/-- **The off-line divisor.**  `P(0) = 1`, `P` is a polynomial of degree `4M`, and its zeros, with
multiplicity, are exactly the off-line zeros of `F`. -/
theorem xiOffLineDivisor_properties :
    xiOffLineDivisor hfin 0 = 1 ∧
      (∃ Q : Polynomial ℂ, Q.natDegree = 4 * xiQuadrantMult hfin ∧
        ∀ z, Q.eval z = xiOffLineDivisor hfin z) ∧
      ∀ z, analyticOrderAt (xiOffLineDivisor hfin) z =
        if XiC z = 0 ∧ z.im ≠ 0 then analyticOrderAt XiC z else 0 := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  have hPd := differentiable_xiOffLineDivisor hfin
  refine ⟨listDivisor_zero _, ?_, fun z => ?_⟩
  · obtain ⟨Q, -, hQd, hQe⟩ := exists_polynomial_listDivisor (quadrantListOf hfin.toFinset.toList)
      fun β hβ h0 => by have := re_pos_of_mem_quadrantListOf hl hβ; rw [h0] at this; simp at this
    have hn : (quadrantListOf hfin.toFinset.toList).length = 2 * xiQuadrantMult hfin :=
      length_xiOffLineList hfin
    exact ⟨Q, by rw [hQd, hn]; ring, hQe⟩
  split_ifs with h
  · obtain ⟨hz, him⟩ := h
    have key : ∀ w : ℂ, XiC w = 0 → w.im ≠ 0 → 0 < w.re →
        analyticOrderAt (xiOffLineDivisor hfin) w = analyticOrderAt XiC w := by
      intro w hw hwim hwre
      show analyticOrderAt (listDivisor (quadrantListOf hfin.toFinset.toList)) w = _
      rw [analyticOrderAt_listDivisor hwre _ (fun β hβ => re_pos_of_mem_quadrantListOf hl hβ),
        count_quadrantListOf hl (nodup_xiOffLine_toList hfin), if_pos, ← xiZeroMult_eq]
      rcases lt_or_gt_of_ne hwim with h | h
      · right
        refine (Finset.mem_toList).2 (hfin.mem_toFinset.2 ⟨by simpa using hwre, by simpa using h, ?_⟩)
        rw [XiC_conj, hw, map_zero]
      · left
        exact (Finset.mem_toList).2 (hfin.mem_toFinset.2 ⟨hwre, h, hw⟩)
    rcases lt_or_gt_of_ne (re_ne_zero_of_XiC_eq_zero hz) with hre | hre
    · have := key (-z) (by rw [XiC_even]; exact hz) (by simpa using him) (by simpa using hre)
      rwa [analyticOrderAt_XiC_neg_eq,
        analyticOrderAt_neg_of_even hPd (xiOffLineDivisor_neg hfin)] at this
    · exact key z hz him hre
  · refine (hPd.analyticAt z).analyticOrderAt_eq_zero.2 fun hP => h ?_
    obtain ⟨β, hβ, hzβ | hzβ⟩ :=
      exists_mem_of_listDivisor_eq_zero (L := quadrantListOf hfin.toFinset.toList) hP
    · rw [hzβ]
      exact ⟨XiC_eq_zero_of_mem_quadrantListOf hl hβ, im_ne_zero_of_mem_quadrantListOf hl hβ⟩
    · rw [hzβ, XiC_even]
      exact ⟨XiC_eq_zero_of_mem_quadrantListOf hl hβ,
        by simpa using im_ne_zero_of_mem_quadrantListOf hl hβ⟩

/-- **Every admissible polynomial occurs.**  For every real polynomial `e` of degree `≤ 2M` there is a
divisor-keeping source `u` with `û P = F e(z²)`. -/
theorem exists_mem_thetaKeepingSources_of_polynomial (e : Polynomial ℝ)
    (he : e.natDegree ≤ 2 * xiQuadrantMult hfin) :
    ∃ u ∈ thetaKeepingSources, ∀ z, sourceTransform (fun x => (u x : ℂ)) z *
      xiOffLineDivisor hfin z = XiC z * (e.map (algebraMap ℝ ℂ)).eval (z ^ 2) := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  obtain ⟨r, -, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨s, hsc, hse, ⟨C, hsC⟩, hsT, -⟩ :=
    exists_basis_sources hl (nodup_xiOffLine_toList hfin) hr
  have hn : (quadrantListOf hfin.toFinset.toList).length = 2 * xiQuadrantMult hfin :=
    length_xiOffLineList hfin
  refine ⟨divisorBasisComb s fun j => e.coeff j,
    divisorBasisComb_mem_thetaKeepingSources hl hsc hse hsC hsT _, fun z => ?_⟩
  rw [show xiOffLineDivisor hfin z = listDivisor (quadrantListOf hfin.toFinset.toList) z from rfl,
    show (sourceTransform fun x => ((divisorBasisComb s fun j => e.coeff j) x : ℂ)) =
      sourceTransform fun x => ((∑ j ∈ Finset.range ((quadrantListOf hfin.toFinset.toList).length
        + 1), e.coeff j * divisorBasis s j x : ℝ) : ℂ) from rfl,
    sourceTransform_sum_divisorBasis_mul hsc hsC hsT,
    Polynomial.eval_eq_sum_range' (n := (quadrantListOf hfin.toFinset.toList).length + 1)
      (Polynomial.natDegree_map_le.trans_lt (by omega))]
  simp only [Polynomial.coeff_map, Complex.coe_algebraMap, ← pow_mul]

include hfin in
/-- **Measurable sources.**  Every measurable real even `k`-dominated source keeping the real zeros of
`F` agrees almost everywhere with an element of `W`, which is therefore the space of such sources
modulo null functions. -/
theorem exists_mem_thetaKeepingSources_ae_eq {u : ℝ → ℝ} (hu : AEStronglyMeasurable u) {C : ℝ}
    (hC : ∀ x, |u x| ≤ C * thetaCuspFullSource x) (heven : ∀ x, u (-x) = u x)
    (hkeep : KeepsRealZeros (sourceTransform fun x => (u x : ℂ))) :
    ∃ w ∈ thetaKeepingSources, u =ᵐ[volume] w := by
  obtain ⟨e, he, heT⟩ := exists_realPolynomial_of_keepsRealZeros hfin hu hC heven hkeep
  obtain ⟨w, hw, hwT⟩ := exists_mem_thetaKeepingSources_of_polynomial hfin e
    (by rw [length_xiOffLineList] at he; exact he)
  refine ⟨w, hw, ?_⟩
  obtain ⟨hwc, -, ⟨Cw, hwC⟩, -⟩ := hw
  set D : ℝ → ℝ := fun x => u x - w x
  have hDms : MeasurableMomentSource fun x => (D x : ℂ) := by
    refine measurableMomentSource_of_le
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (hu.sub hwc.aestronglyMeasurable))
      (C := C + Cw) fun x => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    have h1 := hC x
    have h2 := hwC x
    nlinarith
  have hdisc : ∀ z : ℂ, ‖z‖ ≤ 1 → sourceTransform (fun x => (D x : ℂ)) z = 0 := fun z hz => by
    have hP := listDivisor_quadrantListOf_ne_zero_of_norm_le_one
      (fun α hα => mem_xiOffLineList_toList hfin hα) hz
    refine (mul_eq_zero.1 ?_).resolve_right hP
    rw [sourceTransform_ofReal_sub hu hC hwc.aestronglyMeasurable hwC, sub_mul]
    exact sub_eq_zero.2 ((heT z).trans (hwT z).symm)
  have hall : ∀ z, sourceTransform (fun x => (D x : ℂ)) z = 0 := by
    have hA : AnalyticOnNhd ℂ (sourceTransform fun x => (D x : ℂ)) univ :=
      fun z _ => hDms.differentiable_sourceTransform.analyticAt z
    have hev : (sourceTransform fun x => (D x : ℂ)) =ᶠ[𝓝 0] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
      exact hdisc z (by rw [Metric.mem_ball, dist_zero_right] at hz; exact hz.le)
    intro z
    exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 0) hev
      (mem_univ z)
  have hD0 := ae_eq_zero_of_sourceTransform_eq_zero ((hDms.moment 0).mono'
    hDms.aestronglyMeasurable (Eventually.of_forall fun x => by simp)) hall
  filter_upwards [hD0] with x hx
  simp only [Pi.zero_apply, Complex.ofReal_eq_zero, D, sub_eq_zero] at hx
  exact hx

/-- **The two limits at infinity agree.**  For `u ∈ W` with `û P = F E(z²)`, the first-atom tail
coefficient `lim_{|x|→∞} u(x)/k(x)` and `lim_{|z|→∞} E(z²)/P(z)` exist and are equal. -/
theorem tendsto_div_thetaCuspFullSource_eq_limit_quotient {u : ℝ → ℝ}
    (hu : u ∈ thetaKeepingSources) {e : Polynomial ℝ}
    (he : e.natDegree ≤ (xiOffLineList hfin).length)
    (heT : ∀ z, sourceTransform (fun x => (u x : ℂ)) z * xiOffLineDivisor hfin z =
      XiC z * (e.map (algebraMap ℝ ℂ)).eval (z ^ 2)) :
    ∃ c : ℝ, Tendsto (fun x => u x / thetaCuspFullSource x) (cocompact ℝ) (𝓝 c) ∧
      Tendsto (fun z => (e.map (algebraMap ℝ ℂ)).eval (z ^ 2) / xiOffLineDivisor hfin z)
        (cocompact ℂ) (𝓝 (c : ℂ)) := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  obtain ⟨r, hr0, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨s, hsc, hse, ⟨C, hsC⟩, hsT, hst⟩ :=
    exists_basis_sources hl (nodup_xiOffLine_toList hfin) hr
  obtain ⟨huc, -, ⟨Cu, huC⟩, -⟩ := hu
  have hu_eq := eq_sum_divisorBasis_of_mul_eq hl hsc hsC hsT huc huC he heT
  refine ⟨e.coeff (quadrantListOf hfin.toFinset.toList).length * r, ?_, ?_⟩
  · rw [hu_eq]
    exact tendsto_divisorBasisComb_div hst _
  · have h := tendsto_eval_sq_div_listDivisor (e.map (algebraMap ℝ ℂ))
      (quadrantListOf hfin.toFinset.toList) (Polynomial.natDegree_map_le.trans he)
      (by rw [hr]; exact_mod_cast hr0.ne')
    rw [Polynomial.coeff_map, hr] at h
    push_cast
    exact h

include hfin in
/-- **Positive local moduli.**  Every `u ∈ W_N` is a positive deformation direction of `k`: for
small `ε`, `k + εu` is positive, its transform is `F` times a positive multiplier on the real axis,
it has exactly the real zeros of `F` with the same multiplicities, and it has the same even moments
of orders `0, 2, …, 2N`. -/
theorem positive_deformation_of_mem_thetaKeepingMomentSources {N : ℕ} {u : ℝ → ℝ}
    (hu : u ∈ thetaKeepingMomentSources N) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| < ε₀ →
      (∀ x, 0 < thetaCuspFullSource x + ε * u x) ∧
      (∀ x : ℝ, ∃ m : ℝ, 0 < m ∧
        sourceTransform (fun x => ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) x = m * XiC x) ∧
      (∀ γ : ℝ, analyticOrderAt (sourceTransform fun x =>
        ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) γ = analyticOrderAt XiC γ) ∧
      ∀ i ≤ N, ∫ x, x ^ (2 * i) * (thetaCuspFullSource x + ε * u x) =
        ∫ x, x ^ (2 * i) * thetaCuspFullSource x := by
  obtain ⟨⟨huc, hue, ⟨Cu, huC⟩, huk⟩, hum⟩ := hu
  obtain ⟨e, he, heT⟩ :=
    exists_realPolynomial_of_keepsRealZeros hfin huc.aestronglyMeasurable huC hue huk
  obtain ⟨ε₀, hε₀, h⟩ := positive_deformation_of_mul_eq (l := hfin.toFinset.toList)
    (fun α hα => mem_xiOffLineList_toList hfin hα) huc huC he heT
  refine ⟨ε₀, hε₀, fun ε hε => ?_⟩
  obtain ⟨h1, -, h3, h4⟩ := h ε hε
  exact ⟨h1, h3, h4, fun i hi => integral_pow_mul_add_smul huc huC ε (hum i hi)⟩

/-- Every off-line zero of `F` is a zero of `P` of at least its multiplicity. -/
theorem analyticOrderAt_XiC_le_xiOffLineDivisor_of_im_ne_zero {z : ℂ} (hz : XiC z = 0)
    (him : z.im ≠ 0) : analyticOrderAt XiC z ≤ analyticOrderAt (xiOffLineDivisor hfin) z := by
  rcases lt_or_gt_of_ne (re_ne_zero_of_XiC_eq_zero hz) with h | h
  · have hz' : XiC (-z) = 0 := by rw [XiC_even]; exact hz
    have := analyticOrderAt_xiOffLineDivisor hfin hz' (by simpa using him) (by simpa using h)
    rwa [analyticOrderAt_XiC_neg_eq, analyticOrderAt_neg_of_even
      (differentiable_xiOffLineDivisor hfin) (xiOffLineDivisor_neg hfin)] at this
  · exact analyticOrderAt_xiOffLineDivisor hfin hz him h

/-- If `G P = F Q` with `Q(α) ≠ 0` at an off-line zero `α` of `F`, then `G(α) ≠ 0`. -/
theorem ne_zero_of_mul_eq_xiOffLineDivisor {G Q : ℂ → ℂ} (hGd : Differentiable ℂ G)
    (hQd : Differentiable ℂ Q) (h : ∀ z, G z * xiOffLineDivisor hfin z = XiC z * Q z) {α : ℂ}
    (hα : XiC α = 0) (him : α.im ≠ 0) (hQ : Q α ≠ 0) : G α ≠ 0 := by
  have hPd := differentiable_xiOffLineDivisor hfin
  have h1 := congrArg (fun f => analyticOrderAt f α)
    (show G * xiOffLineDivisor hfin = XiC * Q from funext h)
  rw [analyticOrderAt_mul (hGd.analyticAt α) (hPd.analyticAt α),
    analyticOrderAt_mul (XiC_differentiable.analyticAt α) (hQd.analyticAt α),
    (hQd.analyticAt α).analyticOrderAt_eq_zero.2 hQ, add_zero] at h1
  have hF := analyticOrderAt_XiC_ne_top_of_entire α
  have hle := analyticOrderAt_XiC_le_xiOffLineDivisor_of_im_ne_zero hfin hα him
  have hP : analyticOrderAt (xiOffLineDivisor hfin) α ≠ ⊤ := fun hP =>
    hF (by rw [← h1, hP, add_top])
  have h2 : analyticOrderAt G α + analyticOrderAt (xiOffLineDivisor hfin) α ≤
      0 + analyticOrderAt (xiOffLineDivisor hfin) α := by
    rw [zero_add, h1]; exact hle
  exact (hGd.analyticAt α).analyticOrderAt_eq_zero.1
    (nonpos_iff_eq_zero.1 ((WithTop.add_le_add_iff_right hP).1 h2))

theorem xiOffLineDivisor_eq_zero_of_im_ne_zero {z : ℂ} (hz : XiC z = 0) (him : z.im ≠ 0) :
    xiOffLineDivisor hfin z = 0 := by
  by_contra hP
  have h0 := ((differentiable_xiOffLineDivisor hfin).analyticAt z).analyticOrderAt_eq_zero.2 hP
  have hle := analyticOrderAt_XiC_le_xiOffLineDivisor_of_im_ne_zero hfin hz him
  rw [h0, nonpos_iff_eq_zero, (XiC_differentiable.analyticAt z).analyticOrderAt_eq_zero] at hle
  exact hle hz

/-- **The last surviving direction.**  For `0 < M < ∞` the source `u_*` with
`û_* P = F z^{4M}` keeps every real zero of `F`, has vanishing even moments of orders
`0, 2, …, 4M − 2` and a nonzero moment of order `4M`.  For small `t > 0` the source `k + t u_*` is
positive with transform `F (P + t z^{4M}) / P`; it keeps the real zeros of `F` with their
multiplicities and the first `2M` even moments of `k`, no off-line zero of `F` survives, and its
non-real zeros are exactly the zeros of `P + t z^{4M}`. -/
theorem exists_topMoment_deformation (hM : 0 < xiQuadrantMult hfin) :
    ∃ u ∈ thetaKeepingSources,
      (∀ z, sourceTransform (fun x => (u x : ℂ)) z * xiOffLineDivisor hfin z =
        XiC z * z ^ (4 * xiQuadrantMult hfin)) ∧
      (∀ i < 2 * xiQuadrantMult hfin, ∫ x, x ^ (2 * i) * u x = 0) ∧
      ∫ x, x ^ (4 * xiQuadrantMult hfin) * u x ≠ 0 ∧
      ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ →
        (∀ x, 0 < thetaCuspFullSource x + t * u x) ∧
        (∀ z, sourceTransform (fun x => ((thetaCuspFullSource x + t * u x : ℝ) : ℂ)) z *
            xiOffLineDivisor hfin z =
          XiC z * (xiOffLineDivisor hfin z + t * z ^ (4 * xiQuadrantMult hfin))) ∧
        (∀ γ : ℝ, analyticOrderAt (sourceTransform fun x =>
          ((thetaCuspFullSource x + t * u x : ℝ) : ℂ)) γ = analyticOrderAt XiC γ) ∧
        (∀ i < 2 * xiQuadrantMult hfin, ∫ x, x ^ (2 * i) * (thetaCuspFullSource x + t * u x) =
          ∫ x, x ^ (2 * i) * thetaCuspFullSource x) ∧
        (∀ α, XiC α = 0 → α.im ≠ 0 →
          sourceTransform (fun x => ((thetaCuspFullSource x + t * u x : ℝ) : ℂ)) α ≠ 0) ∧
        ∀ z : ℂ, z.im ≠ 0 →
          (sourceTransform (fun x => ((thetaCuspFullSource x + t * u x : ℝ) : ℂ)) z = 0 ↔
            xiOffLineDivisor hfin z + t * z ^ (4 * xiQuadrantMult hfin) = 0) := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  obtain ⟨r, hr0, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨s, hsc, hse, ⟨C, hsC⟩, hsT, -⟩ :=
    exists_basis_sources hl (nodup_xiOffLine_toList hfin) hr
  have hn : (quadrantListOf hfin.toFinset.toList).length = 2 * xiQuadrantMult hfin := length_xiOffLineList hfin
  have h4 : 4 * xiQuadrantMult hfin = 2 * (quadrantListOf hfin.toFinset.toList).length := by omega
  have hsingle := divisorBasisComb_single (s := s) (Nat.lt_succ_self (quadrantListOf hfin.toFinset.toList).length)
  have hmem := divisorBasisComb_mem_thetaKeepingSources hl hsc hse hsC hsT
    (fun k => if k = (quadrantListOf hfin.toFinset.toList).length then (1 : ℝ) else 0)
  rw [hsingle] at hmem
  have hT : ∀ z, sourceTransform (fun x => (divisorBasis s (quadrantListOf hfin.toFinset.toList).length x : ℂ)) z *
      xiOffLineDivisor hfin z = XiC z * z ^ (4 * xiQuadrantMult hfin) := fun z => by
    rw [h4]; exact sourceTransform_divisorBasis_mul hsT (Nat.lt_succ_self (quadrantListOf hfin.toFinset.toList).length) z
  have hlow : divisorBasis s (quadrantListOf hfin.toFinset.toList).length ∈ thetaKeepingMomentSources ((quadrantListOf hfin.toFinset.toList).length - 1) := by
    rw [← hsingle, divisorBasisComb_mem_moment_iff hl hsc hse hsC hsT]
    exact fun j _ hj => if_neg (by omega)
  have hmom : ∀ i < 2 * xiQuadrantMult hfin, ∫ x, x ^ (2 * i) * divisorBasis s (quadrantListOf hfin.toFinset.toList).length x = 0 :=
    fun i hi => (mem_thetaKeepingMomentSources.1 hlow).2 i (by omega)
  have htop : ∫ x, x ^ (4 * xiQuadrantMult hfin) * divisorBasis s (quadrantListOf hfin.toFinset.toList).length x ≠ 0 := by
    intro h0
    have hW : divisorBasis s (quadrantListOf hfin.toFinset.toList).length ∈ thetaKeepingMomentSources (quadrantListOf hfin.toFinset.toList).length := by
      refine mem_thetaKeepingMomentSources.2 ⟨hmem, fun i hi => ?_⟩
      rcases lt_or_eq_of_le hi with hi | rfl
      · exact hmom i (by omega)
      · rwa [← h4]
    rw [← hsingle, divisorBasisComb_mem_moment_iff hl hsc hse hsC hsT] at hW
    exact one_ne_zero ((if_pos rfl).symm.trans (hW (quadrantListOf hfin.toFinset.toList).length (Nat.lt_succ_self (quadrantListOf hfin.toFinset.toList).length) le_rfl))
  have heT : ∀ z, sourceTransform (fun x => (divisorBasis s (quadrantListOf hfin.toFinset.toList).length x : ℂ)) z *
      listDivisor (quadrantListOf hfin.toFinset.toList) z =
      XiC z * ((Polynomial.X ^ (quadrantListOf hfin.toFinset.toList).length : Polynomial ℝ).map (algebraMap ℝ ℂ)).eval (z ^ 2) := fun z => by
    rw [Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_X, ← pow_mul]
    exact sourceTransform_divisorBasis_mul hsT (Nat.lt_succ_self (quadrantListOf hfin.toFinset.toList).length) z
  obtain ⟨ε₀, hε₀, hdef⟩ := positive_deformation_of_mul_eq hl (continuous_divisorBasis hsc (quadrantListOf hfin.toFinset.toList).length)
    (abs_divisorBasis_le hsC (quadrantListOf hfin.toFinset.toList).length) (Polynomial.natDegree_X_pow_le (quadrantListOf hfin.toFinset.toList).length) heT
  refine ⟨divisorBasis s (quadrantListOf hfin.toFinset.toList).length, hmem, hT, hmom, htop, ε₀, hε₀, fun t ht htε => ?_⟩
  obtain ⟨h1, h2, -, h3⟩ := hdef t (by rw [abs_of_pos ht]; exact htε)
  have hid : ∀ z, sourceTransform (fun x => ((thetaCuspFullSource x + t * divisorBasis s (quadrantListOf hfin.toFinset.toList).length x : ℝ) :
      ℂ)) z * xiOffLineDivisor hfin z =
      XiC z * (xiOffLineDivisor hfin z + t * z ^ (4 * xiQuadrantMult hfin)) := fun z => by
    have := h2 z
    rw [Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_X,
      ← pow_mul, ← h4] at this
    exact this
  have hGd := (expMomentSource_ofReal_of_le (u := fun x => thetaCuspFullSource x +
      t * divisorBasis s (quadrantListOf hfin.toFinset.toList).length x)
    (contDiff_thetaCuspFullSource.continuous.add (continuous_const.mul
      (continuous_divisorBasis hsc (quadrantListOf hfin.toFinset.toList).length))) (C := 1 + |t| * max C 0) (fun x => by
        have hk := thetaCuspFullSource_pos x
        have hb := abs_divisorBasis_le hsC (quadrantListOf hfin.toFinset.toList).length x
        calc |thetaCuspFullSource x + t * divisorBasis s (quadrantListOf hfin.toFinset.toList).length x| ≤
              |thetaCuspFullSource x| + |t * divisorBasis s (quadrantListOf hfin.toFinset.toList).length x| := abs_add_le _ _
          _ ≤ thetaCuspFullSource x + |t| * (max C 0 * thetaCuspFullSource x) := by
              rw [abs_of_pos hk, abs_mul]
              exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (abs_nonneg t))
          _ = (1 + |t| * max C 0) * thetaCuspFullSource x := by ring)).differentiable_sourceTransform
  have hQd : Differentiable ℂ fun z : ℂ =>
      xiOffLineDivisor hfin z + t * z ^ (4 * xiQuadrantMult hfin) :=
    (differentiable_xiOffLineDivisor hfin).add (by fun_prop)
  have hoff : ∀ α, XiC α = 0 → α.im ≠ 0 →
      sourceTransform (fun x => ((thetaCuspFullSource x + t * divisorBasis s (quadrantListOf hfin.toFinset.toList).length x : ℝ) : ℂ)) α ≠ 0 :=
    fun α hα him => ne_zero_of_mul_eq_xiOffLineDivisor hfin hGd hQd hid hα him (by
      rw [xiOffLineDivisor_eq_zero_of_im_ne_zero hfin hα him, zero_add]
      have hα0 : α ≠ 0 := fun h => him (by rw [h, Complex.zero_im])
      exact mul_ne_zero (by exact_mod_cast ht.ne') (pow_ne_zero _ hα0))
  refine ⟨h1, hid, h3, fun i hi => integral_pow_mul_add_smul (continuous_divisorBasis hsc (quadrantListOf hfin.toFinset.toList).length)
    (abs_divisorBasis_le hsC (quadrantListOf hfin.toFinset.toList).length) t (hmom i hi), hoff, fun z hz => ⟨fun h0 => ?_, fun hQ => ?_⟩⟩
  · by_contra hQ
    have := hid z
    rw [h0, zero_mul] at this
    rcases mul_eq_zero.1 this.symm with hF | hF
    · exact hoff z hF hz h0
    · exact hQ hF
  · have hz0 : z ≠ 0 := fun h => hz (by rw [h, Complex.zero_im])
    have hP : xiOffLineDivisor hfin z ≠ 0 := by
      rw [eq_neg_of_add_eq_zero_left hQ]
      exact neg_ne_zero.2 (mul_ne_zero (by exact_mod_cast ht.ne') (pow_ne_zero _ hz0))
    have := hid z
    rw [hQ, mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_right hP

end FiniteDefect

/-- **A hidden direction from one off-line zero.**  If `F` has an off-line zero, there is a real even
source `u` with `|u| ≤ C k` keeping every real zero of `F`, with zero mass, nonzero second moment
and `u / k → 0` at infinity, such that for small `ε` the source `k + εu` is positive, has exactly the
real zeros of `F` with their multiplicities, the same mass and the same leading theta tail. -/
theorem exists_hidden_direction_of_offLine {α : ℂ} (hα : α ∈ xiQuadrantZeros) :
    ∃ u ∈ thetaKeepingSources, ∫ x, u x = 0 ∧ ∫ x, x ^ 2 * u x ≠ 0 ∧
      Tendsto (fun x => u x / thetaCuspFullSource x) (cocompact ℝ) (𝓝 0) ∧
      ∃ ε₀ > 0, ∀ ε : ℝ, |ε| < ε₀ →
        (∀ x, 0 < thetaCuspFullSource x + ε * u x) ∧
        (∀ γ : ℝ, analyticOrderAt (sourceTransform fun x =>
          ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) γ = analyticOrderAt XiC γ) ∧
        ∫ x, (thetaCuspFullSource x + ε * u x) = ∫ x, thetaCuspFullSource x ∧
        Tendsto (fun x => (thetaCuspFullSource x + ε * u x) / thetaCuspFullSource x)
          (cocompact ℝ) (𝓝 1) := by
  have hl : ∀ β ∈ [α], β ∈ xiQuadrantZeros := fun β hβ => by
    rw [List.mem_singleton] at hβ; exact hβ ▸ hα
  obtain ⟨r, hr0, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨s, hsc, hse, ⟨C, hsC⟩, hsT, hst⟩ := exists_basis_sources hl (List.nodup_singleton α) hr
  have hlen : 2 ≤ (quadrantListOf [α]).length := by
    rw [length_quadrantListOf]
    have := one_le_xiZeroMult hα.2.2
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    omega
  have h1n : 1 < (quadrantListOf [α]).length + 1 := by omega
  have hsingle := divisorBasisComb_single (s := s) h1n
  have hmem := divisorBasisComb_mem_thetaKeepingSources hl hsc hse hsC hsT
    (fun k => if k = 1 then (1 : ℝ) else 0)
  rw [hsingle] at hmem
  have hW0 : divisorBasis s 1 ∈ thetaKeepingMomentSources 0 := by
    rw [← hsingle, divisorBasisComb_mem_moment_iff hl hsc hse hsC hsT]
    exact fun j _ hj => if_neg (by omega)
  have hmass : ∫ x, divisorBasis s 1 x = 0 := by
    have := (mem_thetaKeepingMomentSources.1 hW0).2 0 le_rfl
    simpa using this
  have hsecond : ∫ x, x ^ 2 * divisorBasis s 1 x ≠ 0 := by
    intro h0
    have hW : divisorBasis s 1 ∈ thetaKeepingMomentSources 1 := by
      refine mem_thetaKeepingMomentSources.2 ⟨hmem, fun i hi => ?_⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
      · simpa using hmass
      · simpa using h0
    rw [← hsingle, divisorBasisComb_mem_moment_iff hl hsc hse hsC hsT] at hW
    exact one_ne_zero ((if_pos rfl).symm.trans (hW 1 h1n le_rfl))
  have htail : Tendsto (fun x => divisorBasis s 1 x / thetaCuspFullSource x) (cocompact ℝ)
      (𝓝 0) := by
    have := tendsto_divisorBasisComb_div hst (fun k => if k = 1 then (1 : ℝ) else 0)
    rw [if_neg (by omega), zero_mul, hsingle] at this
    exact this
  have heT : ∀ z, sourceTransform (fun x => (divisorBasis s 1 x : ℂ)) z *
      listDivisor (quadrantListOf [α]) z =
      XiC z * ((Polynomial.X : Polynomial ℝ).map (algebraMap ℝ ℂ)).eval (z ^ 2) := fun z => by
    rw [Polynomial.map_X, Polynomial.eval_X]
    exact sourceTransform_divisorBasis_mul hsT h1n z
  obtain ⟨ε₀, hε₀, hdef⟩ := positive_deformation_of_mul_eq hl (continuous_divisorBasis hsc 1)
    (abs_divisorBasis_le hsC 1) (Polynomial.natDegree_X_le.trans (by omega)) heT
  refine ⟨divisorBasis s 1, hmem, hmass, hsecond, htail, ε₀, hε₀, fun ε hε => ?_⟩
  obtain ⟨h1, -, -, h3⟩ := hdef ε hε
  refine ⟨h1, h3, ?_, ?_⟩
  · have := integral_pow_mul_add_smul (continuous_divisorBasis hsc 1) (abs_divisorBasis_le hsC 1)
      ε (n := 0) (by simpa using hmass)
    simpa using this
  · have := (htail.const_mul ε).const_add 1
    rw [mul_zero, add_zero] at this
    refine this.congr fun x => ?_
    have hk := (thetaCuspFullSource_pos x).ne'
    field_simp

end

end RHTower
