import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheTailDecouplesFromTheHead
import GaloisForLFunctions.RHTower.CarlsonZetaMeanSquare

/-!
# The resonator mean of `ζ`

A resonator `R(t) = Σ_{m∈A} r_m m^{it}` weights the heights by `|R(t)|²`; a box resonator on the
primes up to `y` concentrates this weight on the Bohr set where the head phases are aligned. For
`½ < σ < 1` the weighted mean square of `ζ` itself is the diagonal of the product series:

`(1/T) ∫_T^{2T} |R(t)|² |ζ(σ + it)|² dt → Σ_k |c_k|²`, `c_k = Σ_{m∈A, m|k} r_m (k/m)^{−σ}`

(`tendsto_resonatorMean_zeta`). Proof: for a fixed cut `N`, `R · D̄_N` is a Dirichlet polynomial with
coefficients `c_k^N` and the mean value theorem gives its mean (`tendsto_resonatorMean_head`); Carlson's
theorem makes `ζ − D_N` small in mean square, uniformly against the bounded weight `|R|²`
(`abs_dyadicSquareMean_sub_le_split`); and `c^N → c` in `ℓ²` by dominated convergence
(`tendsto_tsum_truncResonatorCoeff`). The resonator is fixed, so the head lies below the Kronecker scale
as `T → ∞`.
-/

open Real Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

open _root_.RHTower

noncomputable section

/-- The weight `n^{−σ}` of `ζ` on the line `Re s = σ`. -/
def lineWeight (σ : ℝ) (n : ℕ) : ℂ := (((n : ℝ) ^ (-σ) : ℝ) : ℂ)

/-- The coefficients of `R · ζ̄` on `Re s = σ`: `c_k = Σ_{m∈A, m|k} r_m (k/m)^{−σ}`. -/
def resonatorCoeff (A : Finset ℕ) (r : ℕ → ℂ) (σ : ℝ) (k : ℕ) : ℂ :=
  ∑ m ∈ A.filter (· ∣ k), r m * lineWeight σ (k / m)

/-- The coefficients of `R · D̄_N`, `D_N = Σ_{n≤N} n^{−σ−it}`. -/
def truncResonatorCoeff (A : Finset ℕ) (r : ℕ → ℂ) (σ : ℝ) (N k : ℕ) : ℂ :=
  ∑ m ∈ A.filter (fun m => m ∣ k ∧ k / m ≤ N), r m * lineWeight σ (k / m)

theorem norm_lineWeight (σ : ℝ) (n : ℕ) : ‖lineWeight σ n‖ = (n : ℝ) ^ (-σ) := by
  rw [lineWeight, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-! ## The head of `ζ` as a resonator -/

/-- `D_N(σ + it)` is the conjugate of the polynomial `Σ_{n≤N} n^{−σ} n^{it}`. -/
theorem zetaDirichletHead_eq_conj (N : ℕ) (σ t : ℝ) :
    zetaDirichletHead N σ t = (starRingEnd ℂ) (headPoly (Finset.Icc 1 N) (lineWeight σ) t) := by
  rw [zetaDirichletHead, edPoly_line _ (fun n hn => (Finset.mem_Icc.mp hn).1), HTGeometry.cdpoly, headPoly,
    map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [HTGeometry.cdterm, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, lineWeight,
    Complex.conj_ofReal, one_mul]
  congr 2
  push_cast
  ring

theorem norm_mul_zetaDirichletHead {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ) (N : ℕ)
    (σ t : ℝ) :
    ‖headPoly A r t * zetaDirichletHead N σ t‖ =
      ‖indexedPoly (A ×ˢ Finset.Icc 1 N) (fun q => q.1 * q.2)
        (fun q => r q.1 * lineWeight σ q.2) t‖ := by
  rw [← headPoly_mul A (Finset.Icc 1 N) r (lineWeight σ) hA
    (fun n hn => by have := (Finset.mem_Icc.mp hn).1; omega), norm_mul, norm_mul,
    zetaDirichletHead_eq_conj, RCLike.norm_conj]

/-- The fibre of `(m, n) ↦ mn` over `k` is the set of divisors `m ∈ A` with `k/m ≤ N`. -/
theorem sum_fiber_eq_truncResonatorCoeff {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ)
    (σ : ℝ) (N k : ℕ) (hk : 1 ≤ k) :
    ∑ q ∈ (A ×ˢ Finset.Icc 1 N).filter (fun q => q.1 * q.2 = k), r q.1 * lineWeight σ q.2 =
      truncResonatorCoeff A r σ N k := by
  unfold truncResonatorCoeff
  refine Finset.sum_nbij' (fun q => q.1) (fun m => (m, k / m)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq ⊢
    obtain ⟨⟨hqA, -, hqN⟩, hqk⟩ := hq
    have hq0 : 0 < q.1 := Nat.pos_of_ne_zero (hA _ hqA)
    refine ⟨hqA, ⟨q.2, hqk.symm⟩, ?_⟩
    rw [← hqk, Nat.mul_div_cancel_left _ hq0]
    exact hqN
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hm ⊢
    obtain ⟨hmA, hmk, hmN⟩ := hm
    have hm0 : 0 < m := Nat.pos_of_ne_zero (hA _ hmA)
    refine ⟨⟨hmA, Nat.div_pos (Nat.le_of_dvd hk hmk) hm0, hmN⟩, Nat.mul_div_cancel' hmk⟩
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    have hq0 : 0 < q.1 := Nat.pos_of_ne_zero (hA _ hq.1.1)
    ext
    · rfl
    · simp only
      rw [← hq.2, Nat.mul_div_cancel_left _ hq0]
  · intro m _
    rfl
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    have hq0 : 0 < q.1 := Nat.pos_of_ne_zero (hA _ hq.1.1)
    rw [← hq.2, Nat.mul_div_cancel_left _ hq0]

/-- The truncated coefficients vanish at `0` and past `N·max A`. -/
theorem truncResonatorCoeff_eq_zero {A : Finset ℕ} (r : ℕ → ℂ) {σ : ℝ}
    (hσ : σ ≠ 0) {N M k : ℕ} (hM : ∀ m ∈ A, m * N ≤ M) (hk : k = 0 ∨ M < k) :
    truncResonatorCoeff A r σ N k = 0 := by
  unfold truncResonatorCoeff
  rcases hk with rfl | hk
  · refine Finset.sum_eq_zero fun m _ => ?_
    rw [Nat.zero_div, lineWeight, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hσ),
      Complex.ofReal_zero, mul_zero]
  · refine Finset.sum_eq_zero fun m hm => ?_
    obtain ⟨hmA, hmk, hmN⟩ := Finset.mem_filter.mp hm
    exfalso
    have h1 : k = m * (k / m) := (Nat.mul_div_cancel' hmk).symm
    have h2 : m * (k / m) ≤ m * N := Nat.mul_le_mul_left m hmN
    have := hM m hmA
    omega

/-- **The resonator mean of a head of `ζ`.** -/
theorem tendsto_resonatorMean_head {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ) {σ : ℝ}
    (hσ : σ ≠ 0) (N : ℕ) :
    Tendsto (dyadicSquareMean (fun t => headPoly A r t * zetaDirichletHead N σ t)) atTop
      (𝓝 (∑' k, ‖truncResonatorCoeff A r σ N k‖ ^ 2)) := by
  classical
  set M := (A.sup id) * N with hMdef
  set E := A ×ˢ Finset.Icc 1 N with hE
  set c : ℕ × ℕ → ℂ := fun q => r q.1 * lineWeight σ q.2 with hc
  have hM : ∀ m ∈ A, m * N ≤ M := fun m hm =>
    Nat.mul_le_mul_right N (Finset.le_sup (f := id) hm)
  have hk : ∀ q ∈ E, 1 ≤ q.1 * q.2 ∧ q.1 * q.2 ≤ M := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    have h2' := Finset.mem_Icc.mp h2
    refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (hA _ h1) (by omega)), ?_⟩
    exact (Nat.mul_le_mul_left _ h2'.2).trans (hM _ h1)
  -- the limit as a finite sum over fibres
  set S := ∑ n : Fin M, ‖fiberCoeff E (fun q => q.1 * q.2) c M n‖ ^ 2 with hS
  have hfib : ∀ n : Fin M, fiberCoeff E (fun q => q.1 * q.2) c M n =
      truncResonatorCoeff A r σ N ((n : ℕ) + 1) := fun n =>
    sum_fiber_eq_truncResonatorCoeff hA r σ N _ (by omega)
  have hSeq : S = ∑' k, ‖truncResonatorCoeff A r σ N k‖ ^ 2 := by
    rw [tsum_eq_sum (s := Finset.range (M + 1)) fun k hk => by
      rw [truncResonatorCoeff_eq_zero r hσ hM (by
        have := Finset.mem_range.not.mp hk
        omega), norm_zero, sq, zero_mul]]
    rw [Finset.sum_range_succ', truncResonatorCoeff_eq_zero r hσ hM (Or.inl rfl), norm_zero,
      sq, zero_mul, add_zero, hS]
    simp_rw [hfib]
    exact Fin.sum_univ_eq_sum_range (fun k => ‖truncResonatorCoeff A r σ N (k + 1)‖ ^ 2) M
  rw [← hSeq]
  -- the mean value theorem
  have hfun : (fun t => ‖headPoly A r t * zetaDirichletHead N σ t‖ ^ 2) =
      fun t => ‖Sieve.dirPoly M (fiberCoeff E (fun q => q.1 * q.2) c M) t‖ ^ 2 := by
    funext t
    rw [norm_mul_zetaDirichletHead hA r N σ t, dirPoly_fiberCoeff c hk t]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound : Tendsto (fun T : ℝ => 8 * M * (1 + Real.log M) * S / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ =>
    norm_nonneg _) ?_ hbound)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have h := Sieve.dirichlet_meanValue_dyadic M (fiberCoeff E (fun q => q.1 * q.2) c M) T
  rw [dyadicSquareMean, hfun, Real.norm_eq_abs, div_sub' hT.ne', abs_div, abs_of_pos hT]
  exact div_le_div_of_nonneg_right h hT.le

/-! ## The cut in `ℓ²` -/

/-- The majorant `g_k = Σ_{m∈A, m|k} |r_m| (k/m)^{−σ}` of every truncation. -/
def resonatorMajorant (A : Finset ℕ) (r : ℕ → ℂ) (σ : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ A.filter (· ∣ k), ‖r m‖ * ((k / m : ℕ) : ℝ) ^ (-σ)

/-- Multiples of `m` carry the summable weight `(k/m)^{−2σ}`. -/
theorem summable_multiple_rpow {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun k : ℕ => if m ∣ k then ((k / m : ℕ) : ℝ) ^ (-2 * σ) else 0 := by
  have hinj : Function.Injective (fun j : ℕ => m * j) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h
  refine (hinj.summable_iff fun k hk => ?_).mp ?_
  · rw [if_neg]
    rintro ⟨j, rfl⟩
    exact hk ⟨j, rfl⟩
  · have hs : Summable fun j : ℕ => (j : ℝ) ^ (-2 * σ) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine hs.congr fun j => ?_
    simp only [Function.comp_apply, dvd_mul_right, if_true,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm)]

theorem summable_resonatorMajorant_sq {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ) {σ : ℝ}
    (hσ : 1 / 2 < σ) : Summable fun k => resonatorMajorant A r σ k ^ 2 := by
  classical
  have hsum : Summable fun k : ℕ => (A.card : ℝ) *
      ∑ m ∈ A, ‖r m‖ ^ 2 * (if m ∣ k then ((k / m : ℕ) : ℝ) ^ (-2 * σ) else 0) :=
    (summable_sum fun m hm => (summable_multiple_rpow (hA m hm) hσ).mul_left _).mul_left _
  refine hsum.of_nonneg_of_le (fun k => sq_nonneg _) fun k => ?_
  unfold resonatorMajorant
  refine (sq_sum_le_card_mul_sum_sq).trans ?_
  have hcard : ((A.filter (· ∣ k)).card : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_filter_le _ _
  have hterm : ∑ m ∈ A.filter (· ∣ k), (‖r m‖ * ((k / m : ℕ) : ℝ) ^ (-σ)) ^ 2 =
      ∑ m ∈ A, ‖r m‖ ^ 2 * (if m ∣ k then ((k / m : ℕ) : ℝ) ^ (-2 * σ) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs
    · have e : (((k / m : ℕ) : ℝ) ^ (-σ)) ^ 2 = ((k / m : ℕ) : ℝ) ^ (-2 * σ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring
      rw [mul_pow, e]
    · simp
  rw [hterm]
  have h0 : 0 ≤ ∑ m ∈ A, ‖r m‖ ^ 2 * (if m ∣ k then ((k / m : ℕ) : ℝ) ^ (-2 * σ) else 0) :=
    Finset.sum_nonneg fun m _ => mul_nonneg (sq_nonneg _) (by split_ifs <;> positivity)
  exact mul_le_mul_of_nonneg_right hcard h0

theorem norm_truncResonatorCoeff_le (A : Finset ℕ) (r : ℕ → ℂ) (σ : ℝ) (N k : ℕ) :
    ‖truncResonatorCoeff A r σ N k‖ ≤ resonatorMajorant A r σ k := by
  unfold truncResonatorCoeff resonatorMajorant
  refine (norm_sum_le _ _).trans ?_
  have hsub : A.filter (fun m => m ∣ k ∧ k / m ≤ N) ⊆ A.filter (· ∣ k) := fun m hm => by
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
  refine (Finset.sum_le_sum fun m _ => by rw [norm_mul, norm_lineWeight]).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity

/-- **The cut disappears in `ℓ²`.** -/
theorem tendsto_tsum_truncResonatorCoeff {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun N => ∑' k, ‖truncResonatorCoeff A r σ N k‖ ^ 2) atTop
      (𝓝 (∑' k, ‖resonatorCoeff A r σ k‖ ^ 2)) := by
  refine tendsto_tsum_of_dominated_convergence (summable_resonatorMajorant_sq hA r hσ) (fun k => ?_)
    (Eventually.of_forall fun N k => ?_)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k] with N hN
    unfold truncResonatorCoeff resonatorCoeff
    rw [Finset.filter_congr (p := fun m => m ∣ k ∧ k / m ≤ N) (q := fun m => m ∣ k)
      (fun m _ => ⟨fun h => h.1, fun h => ⟨h, (Nat.div_le_self k m).trans hN⟩⟩)]
  · rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_truncResonatorCoeff_le A r σ N k) 2

/-! ## Weighted perturbation of dyadic means -/

/-- `|‖f‖² − ‖g‖²|` is at most `δ‖g‖² + (1 + δ⁻¹)‖f − g‖²`. -/
theorem abs_norm_sq_sub_le_split (x y : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ δ * ‖y‖ ^ 2 + (1 + δ⁻¹) * ‖x - y‖ ^ 2 := by
  set a := ‖y‖
  set b := ‖x - y‖
  have hd : |‖x‖ - a| ≤ b := abs_norm_sub_norm_le x y
  have hx : ‖x‖ ≤ a + b := by linarith [(abs_le.mp hd).2]
  have h1 : |‖x‖ ^ 2 - a ^ 2| ≤ b * (2 * a + b) := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖x‖ + a), mul_comm]
    exact mul_le_mul hd (by linarith) (by positivity) (norm_nonneg _)
  have h2 : 2 * a * b ≤ δ * a ^ 2 + δ⁻¹ * b ^ 2 := by
    have hsq := sq_nonneg (δ * a - b)
    have e : δ * a ^ 2 + δ⁻¹ * b ^ 2 - 2 * a * b = δ⁻¹ * (δ * a - b) ^ 2 := by
      field_simp
      ring
    nlinarith [inv_pos.mpr hδ, mul_nonneg (inv_pos.mpr hδ).le hsq]
  nlinarith

/-- **Weighted perturbation.** If `f − g = h`, then `|M(f) − M(g)| ≤ δ M(g) + (1 + δ⁻¹) M(h)` for
dyadic means. -/
theorem abs_dyadicSquareMean_sub_le_split {f g h : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (hfgh : ∀ t, f t - g t = h t) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    |dyadicSquareMean f T - dyadicSquareMean g T| ≤
      δ * dyadicSquareMean g T + (1 + δ⁻¹) * dyadicSquareMean h T := by
  have hab : T ≤ 2 * T := by linarith
  have hf2 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume T (2 * T) :=
    (show Continuous fun t => ‖f t‖ ^ 2 from hf.norm.pow 2).intervalIntegrable _ _
  have hg2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume T (2 * T) :=
    (show Continuous fun t => ‖g t‖ ^ 2 from hg.norm.pow 2).intervalIntegrable _ _
  have hh2 : IntervalIntegrable (fun t => ‖h t‖ ^ 2) volume T (2 * T) :=
    (show Continuous fun t => ‖h t‖ ^ 2 from hh.norm.pow 2).intervalIntegrable _ _
  unfold dyadicSquareMean
  rw [← sub_div, abs_div, abs_of_pos hT, mul_div_assoc', mul_div_assoc', ← add_div]
  apply div_le_div_of_nonneg_right _ hT.le
  rw [← intervalIntegral.integral_sub hf2 hg2, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hg2.const_mul _)
      (hh2.const_mul _)]
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
  refine intervalIntegral.integral_mono_on hab ((hf2.sub hg2).abs) ((hg2.const_mul _).add
    (hh2.const_mul _)) fun t _ => ?_
  have := abs_norm_sq_sub_le_split (f t) (g t) hδ
  rwa [hfgh t] at this

/-- A bounded weight multiplies a dyadic mean by at most the square of its bound. -/
theorem dyadicSquareMean_mul_le {R h : ℝ → ℂ} (hR : Continuous R) (hh : Continuous h) {B T : ℝ}
    (hT : 0 < T) (hB : ∀ t, ‖R t‖ ≤ B) :
    dyadicSquareMean (fun t => R t * h t) T ≤ B ^ 2 * dyadicSquareMean h T := by
  have hab : T ≤ 2 * T := by linarith
  unfold dyadicSquareMean
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right _ hT.le
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab
    (((hR.mul hh).norm.pow 2).intervalIntegrable _ _)
    (((hh.norm.pow 2).intervalIntegrable _ _).const_mul _) fun t _ => ?_
  rw [norm_mul, mul_pow]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB t) 2) (sq_nonneg _)

/-! ## The resonator mean of `ζ` -/

theorem continuous_headPoly (A : Finset ℕ) (r : ℕ → ℂ) : Continuous (headPoly A r) := by
  unfold headPoly
  fun_prop

theorem norm_headPoly_le (A : Finset ℕ) (r : ℕ → ℂ) (t : ℝ) :
    ‖headPoly A r t‖ ≤ ∑ m ∈ A, ‖r m‖ := by
  unfold headPoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The resonator mean of `ζ`.** For `½ < σ < 1` and every finite resonator `R = Σ_{m∈A} r_m m^{it}`,
`(1/T) ∫_T^{2T} |R(t)ζ(σ + it)|² dt → Σ_k |Σ_{m∈A, m|k} r_m (k/m)^{−σ}|²`. -/
theorem tendsto_resonatorMean_zeta {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (dyadicSquareMean fun t => headPoly A r t * riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (𝓝 (∑' k, ‖resonatorCoeff A r σ k‖ ^ 2)) := by
  set L := ∑' k, ‖resonatorCoeff A r σ k‖ ^ 2 with hL
  set B := ∑ m ∈ A, ‖r m‖ with hBdef
  have hσ0 : σ ≠ 0 := by linarith
  have hσ1' : σ ≠ 1 := by linarith
  have hB : ∀ t, ‖headPoly A r t‖ ≤ B := norm_headPoly_le A r
  have hR := continuous_headPoly A r
  have hzeta : ∀ (N : ℕ) (t : ℝ), riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) =
      zetaDirichletHead N σ t + zetaDirichletTail N σ t := fun N t => by
    rw [zetaDirichletTail, add_sub_cancel]
  have hcontζ : Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    have := (continuous_zetaDirichletHead 0 σ).add (continuous_zetaDirichletTail 0 hσ1')
    exact this.congr fun t => (hzeta 0 t).symm
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / (4 * (|L| + 2)) with hδ
  have hδ0 : 0 < δ := by positivity
  set K := (1 + δ⁻¹) * B ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  -- choose the cut
  have hy := tendsto_tsum_truncResonatorCoeff hA r hσ
  have htail := tendsto_zetaCoefficientTailMass hσ
  obtain ⟨N, hN1, hN2⟩ := ((Metric.tendsto_nhds.mp hy (min (ε / 4) 1) (by positivity)).and
    ((htail.const_mul K).eventually (gt_mem_nhds (by
      rw [mul_zero]; positivity : K * 0 < ε / 8)))).exists
  set y := ∑' k, ‖truncResonatorCoeff A r σ N k‖ ^ 2 with hy'
  have hyL : |y - L| < ε / 4 := by
    have := hN1; rw [Real.dist_eq] at this; exact this.trans_le (min_le_left _ _)
  have hyB : y ≤ |L| + 1 := by
    have := hN1; rw [Real.dist_eq] at this
    have h1 := (abs_lt.mp (this.trans_le (min_le_right _ _))).2
    linarith [le_abs_self L]
  set κ := ε / (8 * (K + 1)) with hκ
  have hκ0 : 0 < κ := by positivity
  have hKκ : K * κ < ε / 8 := by
    rw [hκ, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hfin := (Metric.tendsto_nhds.mp (tendsto_resonatorMean_head hA r hσ0 N)) (min (ε / 4) 1)
    (by positivity)
  have hcar := (carlson_zeta_tail_dyadicMeanSquare N hσ hσ1).eventually
    (gt_mem_nhds (show zetaCoefficientTailMass N σ < zetaCoefficientTailMass N σ + κ by linarith))
  filter_upwards [hfin, hcar, eventually_gt_atTop (0 : ℝ)] with T hT1 hT2 hT
  set X := dyadicSquareMean (fun t => headPoly A r t * riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) T
  set Y := dyadicSquareMean (fun t => headPoly A r t * zetaDirichletHead N σ t) T
  have hYy : |Y - y| < ε / 4 := by
    have := hT1; rw [Real.dist_eq] at this; exact this.trans_le (min_le_left _ _)
  have hYb : Y ≤ |L| + 2 := by
    have := hT1; rw [Real.dist_eq] at this
    have h1 := (abs_lt.mp (this.trans_le (min_le_right _ _))).2
    linarith
  have hsplit := abs_dyadicSquareMean_sub_le_split
    (f := fun t => headPoly A r t * riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
    (g := fun t => headPoly A r t * zetaDirichletHead N σ t)
    (h := fun t => headPoly A r t * zetaDirichletTail N σ t) (hR.mul hcontζ)
    (hR.mul (continuous_zetaDirichletHead N σ)) (hR.mul (continuous_zetaDirichletTail N hσ1'))
    (fun t => by rw [hzeta N t]; ring) hT hδ0
  have hw := dyadicSquareMean_mul_le hR (continuous_zetaDirichletTail N hσ1') hT hB
  have hδY : δ * Y ≤ ε / 4 := by
    have : δ * Y ≤ δ * (|L| + 2) := mul_le_mul_of_nonneg_left hYb hδ0.le
    have e : δ * (|L| + 2) = ε / 4 := by rw [hδ]; field_simp
    linarith
  have hKt : K * dyadicSquareMean (zetaDirichletTail N σ) T < ε / 4 := by
    have h1 : K * dyadicSquareMean (zetaDirichletTail N σ) T ≤
        K * (zetaCoefficientTailMass N σ + κ) := mul_le_mul_of_nonneg_left hT2.le hK0
    have h2 : K * zetaCoefficientTailMass N σ < ε / 8 := hN2
    linarith
  have hXY : |X - Y| < ε / 2 := by
    have : (1 + δ⁻¹) * dyadicSquareMean (fun t => headPoly A r t * zetaDirichletTail N σ t) T ≤
        K * dyadicSquareMean (zetaDirichletTail N σ) T := by
      rw [hK, mul_assoc]
      exact mul_le_mul_of_nonneg_left hw (by positivity)
    linarith
  rw [Real.dist_eq]
  calc |X - L| ≤ |X - Y| + |Y - y| + |y - L| := by
        have := abs_sub_le X Y L
        have := abs_sub_le Y y L
        linarith
    _ < ε / 2 + ε / 4 + ε / 4 := by linarith
    _ = ε := by ring

/-! ## The tail decouples from the head -/

/-- The `y`-smooth part of `k`: its prime powers below `y`. -/
def smoothPart (y k : ℕ) : ℕ := ∏ p ∈ k.primeFactors.filter (· < y), p ^ k.factorization p

/-- The `y`-rough part of `k`: its prime powers from `y` on. -/
def roughPart (y k : ℕ) : ℕ := ∏ p ∈ k.primeFactors.filter (fun p => ¬ p < y), p ^ k.factorization p

theorem smoothPart_mul_roughPart (y : ℕ) {k : ℕ} (hk : k ≠ 0) : smoothPart y k * roughPart y k = k := by
  rw [smoothPart, roughPart, Finset.prod_filter_mul_prod_filter_not]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hk]
  rfl

/-- A prime dividing a product of powers of primes from a set lies in the set. -/
private theorem prime_mem_of_dvd_prod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℕ) {q : ℕ}
    (hq : q.Prime) (h : q ∣ ∏ p ∈ S, p ^ e p) : q ∈ S := by
  obtain ⟨p, hpS, hqp⟩ := (Nat.prime_iff.mp hq).dvd_finsetProd_iff _ |>.mp h
  have := (Nat.prime_dvd_prime_iff_eq hq (hS p hpS)).mp (hq.dvd_of_dvd_pow hqp)
  rw [this]
  exact hpS

theorem smoothPart_mem (y k : ℕ) : smoothPart y k ∈ Nat.smoothNumbers y := by
  refine Nat.mem_smoothNumbers'.mpr fun q hq hqd => ?_
  have hS : ∀ p ∈ k.primeFactors.filter (· < y), p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  exact (Finset.mem_filter.mp (prime_mem_of_dvd_prod hS _ hq hqd)).2

theorem isRough_roughPart (y k : ℕ) : IsRough y (roughPart y k) := by
  have hS : ∀ p ∈ k.primeFactors.filter (fun p => ¬ p < y), p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  refine ⟨Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hS p hp).ne_zero, fun q hq hqd => ?_⟩
  exact not_lt.mp (Finset.mem_filter.mp (prime_mem_of_dvd_prod hS _ hq hqd)).2

/-- **The coefficients factor.** For a smooth resonator, `c_{su} = u^{−σ} c_s` when `s` is smooth and
`u` rough. -/
theorem resonatorCoeff_mul {y : ℕ} {A : Finset ℕ} (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (r : ℕ → ℂ) (σ : ℝ) {s u : ℕ} (hs : s ∈ Nat.smoothNumbers y) (hu : IsRough y u) :
    resonatorCoeff A r σ (s * u) = lineWeight σ u * resonatorCoeff A r σ s := by
  unfold resonatorCoeff
  rw [Finset.mul_sum, Finset.filter_congr (p := (· ∣ s * u)) (q := (· ∣ s)) fun m hm =>
    ⟨fun h => (coprime_of_smooth_of_rough (hA m hm) hu).dvd_of_dvd_mul_right h,
      fun h => h.mul_right u⟩]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hms : m ∣ s := (Finset.mem_filter.mp hm).2
  rw [show s * u / m = s / m * u by rw [Nat.mul_comm s u, Nat.mul_div_assoc u hms, Nat.mul_comm],
    lineWeight, lineWeight, lineWeight, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), Complex.ofReal_mul]
  ring

/-- The pairs `(smooth, rough)` multiply injectively onto the positive integers. -/
private def smoothRoughMul (y : ℕ) : Nat.smoothNumbers y × {u // IsRough y u} → ℕ :=
  fun x => (x.1 : ℕ) * x.2

private theorem smoothRoughMul_injective (y : ℕ) : Function.Injective (smoothRoughMul y) := by
  rintro ⟨⟨s, hs⟩, ⟨u, hu⟩⟩ ⟨⟨s', hs'⟩, ⟨u', hu'⟩⟩ h
  obtain ⟨e1, e2⟩ := smooth_mul_rough_injective hs hs' hu hu' h
  subst e1; subst e2
  rfl

/-- **The tail decouples from the head for `ζ` itself.** For a resonator on `y`-smooth integers the
limit factors as the head part times the rough mass `Σ_{u rough} u^{−2σ}`. -/
theorem tsum_resonatorCoeff_eq_mul {y : ℕ} {A : Finset ℕ} (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (r : ℕ → ℂ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∑' k, ‖resonatorCoeff A r σ k‖ ^ 2 =
      (∑' s : Nat.smoothNumbers y, ‖resonatorCoeff A r σ s‖ ^ 2) *
        ∑' u : {u // IsRough y u}, (u : ℝ) ^ (-2 * σ) := by
  have hA0 : ∀ m ∈ A, m ≠ 0 := fun m hm => Nat.ne_zero_of_mem_smoothNumbers (hA m hm)
  have hc : Summable fun k => ‖resonatorCoeff A r σ k‖ ^ 2 := by
    refine (summable_resonatorMajorant_sq hA0 r hσ).of_nonneg_of_le (fun k => sq_nonneg _) fun k => ?_
    have h := norm_truncResonatorCoeff_le A r σ k k
    have e : truncResonatorCoeff A r σ k k = resonatorCoeff A r σ k := by
      unfold truncResonatorCoeff resonatorCoeff
      rw [Finset.filter_congr (p := fun m => m ∣ k ∧ k / m ≤ k) (q := fun m => m ∣ k)
        (fun m _ => ⟨fun h => h.1, fun h => ⟨h, Nat.div_le_self k m⟩⟩)]
    rw [e] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hu : Summable fun n : ℕ => (n : ℝ) ^ (-2 * σ) := Real.summable_nat_rpow.mpr (by linarith)
  have hcs : Summable fun s : Nat.smoothNumbers y => ‖resonatorCoeff A r σ s‖ ^ 2 :=
    hc.subtype _
  have hus : Summable fun u : {u // IsRough y u} => (u : ℝ) ^ (-2 * σ) := hu.subtype _
  rw [tsum_mul_tsum_of_summable_norm (by simpa using hcs)
    (hus.congr fun u => (Real.norm_of_nonneg (by positivity)).symm)]
  rw [← (smoothRoughMul_injective y).tsum_eq (f := fun k => ‖resonatorCoeff A r σ k‖ ^ 2)]
  · refine tsum_congr fun x => ?_
    simp only [smoothRoughMul]
    rw [resonatorCoeff_mul hA r σ x.1.2 x.2.2, norm_mul, mul_pow, norm_lineWeight,
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    push_cast
    ring_nf
  · intro k hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hk
      simp only [resonatorCoeff]
      rw [sq_eq_zero_iff, norm_eq_zero]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [Nat.zero_div, lineWeight, Nat.cast_zero, Real.zero_rpow (by linarith), Complex.ofReal_zero,
        mul_zero]
    exact ⟨(⟨smoothPart y k, smoothPart_mem y k⟩, ⟨roughPart y k, isRough_roughPart y k⟩),
      smoothPart_mul_roughPart y hk0⟩

/-- **The resonator mean of `ζ` on a Bohr set of the head.** For a resonator on `y`-smooth integers,
`(1/T) ∫_T^{2T} |R(t)ζ(σ + it)|² dt → (Σ_{s smooth} |c_s|²) · Σ_{u rough} u^{−2σ}`: conditionally on the
head, the tail of `ζ` has its unconditional second moment. -/
theorem tendsto_resonatorMean_zeta_smooth {y : ℕ} {A : Finset ℕ}
    (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y) (r : ℕ → ℂ) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (dyadicSquareMean fun t => headPoly A r t * riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (𝓝 ((∑' s : Nat.smoothNumbers y, ‖resonatorCoeff A r σ s‖ ^ 2) *
        ∑' u : {u // IsRough y u}, (u : ℝ) ^ (-2 * σ))) := by
  rw [← tsum_resonatorCoeff_eq_mul hA r hσ]
  exact tendsto_resonatorMean_zeta (fun m hm => Nat.ne_zero_of_mem_smoothNumbers (hA m hm)) r hσ hσ1

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
