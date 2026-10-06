import GaloisForLFunctions.RHTower.VerticalProgressionRatioFibers

/-!
# Off-resonant and near-diagonal quadruples

The phase of a ratio `c = a/b` is `u(c) = α log(a/b)/2π`; a quadruple of ratio `c` carries the
lattice sum `Σ_ℓ ψ(ℓ/T) V(2πmn/t_ℓ) e(ℓ u(c))`.

* **Indicator decomposition** (`hasSum_indicator_fiberTerm`): for any set `S` of ratios,
  `Σ_{c ∈ S} Φ_T(c) = Σ_{h,k} Σ_{P : ratio ∈ S} X_q`; hence
  `‖Σ_{c ∈ S} Φ_T(c)‖ ≤ Σ_{h,k} Σ_{P : ratio ∈ S} ‖X_q‖`.
* **Off-resonant ratios** (`sum_offResonant_le`): if `‖u(c)‖ ≥ δ`, `k`-fold summation by parts gives
  `‖X_q‖ ≤ |c_q| C T²/(2πmn T^k δ^k)`, and the total is `≤ C N T²/(T^k δ^k)`.
* **Near-diagonal ratios** (`pairProd_ge_of_near_diagonal`, `sum_nearDiagonal_le`): if
  `0 < |u(c)| < δ` then `mn ≥ (α/2πδ)²/(e N²)` (two distinct integers `x, y` have
  `|log x − log y| ≥ 1/max(x, y)`), and the rapid decay of `V` makes the total small.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower.VerticalAP

noncomputable section

open ZetaNotch (pairAmp pairFreq pairProd)

/-- The phase `u(c) = α (log a − log b)/2π` of a ratio `c = (a, b)`. -/
def ratioPhase (α : ℝ) (c : ℕ × ℕ) : ℝ := α * (Real.log c.1 - Real.log c.2) / (2 * Real.pi)

theorem summable_norm_quadPoint' {ψ : ℝ → ℝ} {α β T : ℝ}
    (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β) (N h k : ℕ) (ℓ : ℤ) :
    Summable (fun P : ℕ × ℕ => |ψ ((ℓ : ℝ) / T)| * ‖quadPoint N P h k (α * ℓ + β)‖) := by
  by_cases h0 : ψ ((ℓ : ℝ) / T) = 0
  · simp only [h0, abs_zero, zero_mul]; exact summable_zero
  · exact (summable_norm_quadPoint (hpos ℓ h0) N h k).mul_left _

theorem quadFreq_eq_ratio (P : ℕ × ℕ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    quadFreq P h k = Real.log (quadRatio P h k).1 - Real.log (quadRatio P h k).2 := by
  set x := (P.2 + 1) * k
  set y := (P.1 + 1) * h
  have hx : 0 < x := Nat.mul_pos (Nat.succ_pos _) hk
  have hy : 0 < y := Nat.mul_pos (Nat.succ_pos _) hh
  set d := Nat.gcd x y
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.gcd_pos_of_pos_left _ hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  unfold quadRatio quadFreq pairFreq
  simp only
  rw [Nat.cast_div (Nat.gcd_dvd_left x y) hd.ne', Nat.cast_div (Nat.gcd_dvd_right x y) hd.ne',
    Real.log_div hxR.ne' hd.ne', Real.log_div hyR.ne' hd.ne']
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have e1 : (x : ℝ) = ((P.2 : ℝ) + 1) * k := by simp [x]
  have e2 : (y : ℝ) = ((P.1 : ℝ) + 1) * h := by simp [y]
  rw [e1, e2, Real.log_mul (by positivity) hkR.ne', Real.log_mul (by positivity) hhR.ne']
  ring

/-! ## Indicator decomposition -/

theorem summable_norm_quadTerm {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {α β : ℝ}
    (N : ℕ) {T : ℝ} (hT : 0 < T) (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β) (h k : ℕ) :
    Summable (fun P : ℕ × ℕ => ‖quadTerm ψ α β N T P h k‖) := by
  have hs := complex_support_subset hsupp
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun P => ?_)
    (summable_sum (s := Finset.Icc ⌈T⌉ ⌊2 * T⌋) fun ℓ _ =>
      (summable_norm_quadPoint' hpos N h k ℓ))
  rw [quadTerm_eq_latticeSum hsupp N hT, latticeSum_eq_sum (support_cutoff_subset hs hT _)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓ _ => ?_)
  rw [norm_mul, norm_unitExp, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem hasSum_indicator_fiberTerm {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2)
    {α β : ℝ} (N : ℕ) {T : ℝ} (hT : 0 < T) (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β)
    (S : Set (ℕ × ℕ)) :
    HasSum (S.indicator (fiberTerm ψ α β N T))
      (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ∑' P : ℕ × ℕ, ((fun P => quadRatio P h k) ⁻¹' S).indicator
          (fun P => quadTerm ψ α β N T P h k) P) := by
  have hfib : ∀ c : ℕ × ℕ, S.indicator (fiberTerm ψ α β N T) c =
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ∑' P : ↥{P : ℕ × ℕ | quadRatio P h k = c},
        ((fun P => quadRatio P h k) ⁻¹' S).indicator (fun P => quadTerm ψ α β N T P h k) P := by
    intro c
    by_cases hc : c ∈ S
    · rw [Set.indicator_of_mem hc]
      unfold fiberTerm
      refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => tsum_congr fun P => ?_
      rw [Set.indicator_of_mem (show (P : ℕ × ℕ) ∈ (fun P => quadRatio P h k) ⁻¹' S by
        simp only [Set.mem_preimage]; rw [P.2]; exact hc)]
    · rw [Set.indicator_of_notMem hc]
      symm
      refine Finset.sum_eq_zero fun h _ => Finset.sum_eq_zero fun k _ => ?_
      refine (tsum_congr fun P => ?_).trans tsum_zero
      rw [Set.indicator_of_notMem (show (P : ℕ × ℕ) ∉ (fun P => quadRatio P h k) ⁻¹' S by
        simp only [Set.mem_preimage]; rw [P.2]; exact hc)]
  rw [show S.indicator (fiberTerm ψ α β N T) = fun c => ∑ h ∈ Finset.Icc 1 N,
      ∑ k ∈ Finset.Icc 1 N, ∑' P : ↥{P : ℕ × ℕ | quadRatio P h k = c},
        ((fun P => quadRatio P h k) ⁻¹' S).indicator (fun P => quadTerm ψ α β N T P h k) P from
    funext hfib]
  refine hasSum_sum fun h _ => hasSum_sum fun k _ => ?_
  exact ((summable_quadTerm hsupp N hT hpos h k).indicator _).hasSum.tsum_fiberwise
    (fun P => quadRatio P h k)

theorem norm_tsum_indicator_fiberTerm_le {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2)
    {α β : ℝ} (N : ℕ) {T : ℝ} (hT : 0 < T) (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β)
    (S : Set (ℕ × ℕ)) :
    ‖∑' c, S.indicator (fiberTerm ψ α β N T) c‖ ≤
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ∑' P : ℕ × ℕ, ((fun P => quadRatio P h k) ⁻¹' S).indicator
          (fun P => ‖quadTerm ψ α β N T P h k‖) P := by
  rw [(hasSum_indicator_fiberTerm hsupp N hT hpos S).tsum_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hs := (summable_quadTerm hsupp N hT hpos h k).indicator ((fun P => quadRatio P h k) ⁻¹' S)
  have hn : Summable (fun P : ℕ × ℕ => ‖((fun P => quadRatio P h k) ⁻¹' S).indicator
      (fun P => quadTerm ψ α β N T P h k) P‖) := by
    simp_rw [norm_indicator_eq_indicator_norm]
    exact (summable_norm_quadTerm hsupp N hT hpos h k).indicator _
  refine (norm_tsum_le_tsum_norm hn).trans (le_of_eq ?_)
  refine tsum_congr fun P => ?_
  rw [norm_indicator_eq_indicator_norm]

/-! ## Masses -/

theorem abs_mollAmp_le {N h : ℕ} (hh : h ∈ Finset.Icc 1 N) :
    |mollAmp N h| ≤ ((h : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
  have hpos : (0 : ℝ) < h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
  unfold mollAmp
  rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hpos), Real.sqrt_eq_rpow, div_eq_mul_inv]
  have := abs_linearMollifierCoeff_le_one hh
  have h2 : 0 < (h : ℝ) ^ (1 / 2 : ℝ) := by positivity
  calc |Sieve.linearMollifierCoeff N h| * ((h : ℝ) ^ (1 / 2 : ℝ))⁻¹
      ≤ 1 * ((h : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by gcongr
    _ = _ := one_mul _

theorem sum_abs_mollAmp_mul_le (N : ℕ) :
    ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, |mollAmp N h| * |mollAmp N k| ≤ 4 * N := by
  have h1 : ∑ h ∈ Finset.Icc 1 N, |mollAmp N h| ≤ 2 * Real.sqrt N :=
    (Finset.sum_le_sum fun h hh => abs_mollAmp_le hh).trans (sum_Icc_inv_sqrt_le N)
  have h0 : 0 ≤ ∑ h ∈ Finset.Icc 1 N, |mollAmp N h| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, |mollAmp N h| * |mollAmp N k|
      = (∑ h ∈ Finset.Icc 1 N, |mollAmp N h|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
    _ ≤ (2 * Real.sqrt N) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 4 * N := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; ring

theorem summable_pairAmp_div : Summable (fun P : ℕ × ℕ => pairAmp P * pairProd P ^ (-(1 : ℝ))) := by
  refine (ZetaNotch.summable_pairProd_rpow (s := 3 / 2) (by norm_num)).congr fun P => ?_
  rw [ZetaNotch.pairAmp_mul_rpow]; norm_num

/-- `Σ_P (mn)^{−3/2}`. -/
def pairSum : ℝ := ∑' P : ℕ × ℕ, pairAmp P * pairProd P ^ (-(1 : ℝ))

theorem pairSum_nonneg : 0 ≤ pairSum :=
  tsum_nonneg fun P => mul_nonneg (ZetaNotch.pairAmp_pos P).le
    (Real.rpow_nonneg (ZetaNotch.pairProd_pos P).le _)

theorem norm_quadTerm_eq (ψ : ℝ → ℝ) (α β : ℝ) (N : ℕ) (T : ℝ) (P : ℕ × ℕ) (h k : ℕ) :
    ‖quadTerm ψ α β N T P h k‖ = |mollAmp N h| * |mollAmp N k| * pairAmp P *
      ‖latticeSum (fun x => (ψ (x / T) : ℂ) *
        smoothAFECutoff (2 * Real.pi * pairProd P / (α * x + β))) (α * quadFreq P h k / (2 * Real.pi))‖ := by
  unfold quadTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one]
  unfold quadCoeff
  rw [abs_mul, abs_mul, abs_of_pos (ZetaNotch.pairAmp_pos P)]
  ring

/-- Summing a per-quadruple bound `|b(h)b(k)|(hk)^{−1/2}(mn)^{−1/2} B (mn)^{−1}` over all quadruples. -/
theorem sum_quadruple_le {N : ℕ} (S : ℕ → ℕ → Set (ℕ × ℕ)) {f : ℕ × ℕ → ℕ → ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hf : ∀ h ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N, ∀ P ∈ S h k,
      f P h k ≤ |mollAmp N h| * |mollAmp N k| * pairAmp P * (B * pairProd P ^ (-(1 : ℝ))))
    (hf0 : ∀ P h k, 0 ≤ f P h k) :
    ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ∑' P : ℕ × ℕ, (S h k).indicator (fun P => f P h k) P ≤
      4 * N * (B * pairSum) := by
  have hterm : ∀ h ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      ∑' P : ℕ × ℕ, (S h k).indicator (fun P => f P h k) P ≤
        |mollAmp N h| * |mollAmp N k| * (B * pairSum) := by
    intro h hh k hk
    have hsum : Summable (fun P : ℕ × ℕ =>
        |mollAmp N h| * |mollAmp N k| * pairAmp P * (B * pairProd P ^ (-(1 : ℝ)))) := by
      refine (summable_pairAmp_div.mul_left (|mollAmp N h| * |mollAmp N k| * B)).congr fun P => ?_
      ring
    have hle : ∀ P : ℕ × ℕ, (S h k).indicator (fun P => f P h k) P ≤
        |mollAmp N h| * |mollAmp N k| * pairAmp P * (B * pairProd P ^ (-(1 : ℝ))) := by
      intro P
      by_cases hP : P ∈ S h k
      · rw [Set.indicator_of_mem hP]; exact hf h hh k hk P hP
      · rw [Set.indicator_of_notMem hP]
        have := (ZetaNotch.pairAmp_pos P).le
        have := Real.rpow_nonneg (ZetaNotch.pairProd_pos P).le (-(1 : ℝ))
        positivity
    have hnn : ∀ P : ℕ × ℕ, 0 ≤ (S h k).indicator (fun P => f P h k) P := fun P =>
      Set.indicator_nonneg (fun P _ => hf0 P h k) P
    refine (Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnn hle hsum) hsum).trans
      (le_of_eq ?_)
    rw [show (fun P : ℕ × ℕ => |mollAmp N h| * |mollAmp N k| * pairAmp P *
        (B * pairProd P ^ (-(1 : ℝ)))) = fun P => (|mollAmp N h| * |mollAmp N k| * B) *
          (pairAmp P * pairProd P ^ (-(1 : ℝ))) from funext fun P => by ring, tsum_mul_left]
    unfold pairSum
    ring
  calc ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ∑' P : ℕ × ℕ,
        (S h k).indicator (fun P => f P h k) P
      ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, |mollAmp N h| * |mollAmp N k| * (B * pairSum) :=
        Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun k hk => hterm h hh k hk
    _ = (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, |mollAmp N h| * |mollAmp N k|) *
          (B * pairSum) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun h _ => ?_; rw [Finset.sum_mul]
    _ ≤ 4 * N * (B * pairSum) :=
        mul_le_mul_of_nonneg_right (sum_abs_mollAmp_mul_le N)
          (mul_nonneg hB pairSum_nonneg)

/-! ## Off-resonant ratios -/

/-- The off-resonant ratios `{c : ‖u(c)‖ ≥ δ}`. -/
def offResonant (α δ : ℝ) : Set (ℕ × ℕ) := {c | ∀ j : ℤ, δ ≤ |ratioPhase α c - j|}

/-- **Off-resonant quadruples** contribute `≤ C N T²/(T^r δ^r)`. -/
theorem sum_offResonant_le {ψ : ℝ → ℝ} (hψ : ∀ r : ℕ, ContDiff ℝ r ψ)
    (hsupp : Function.support ψ ⊆ Icc 1 2) {α β : ℝ} (hα : 0 < α) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) {T : ℝ}, 1 ≤ T → 2 * |β| ≤ α * T → ∀ {δ : ℝ}, 0 < δ →
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ∑' P : ℕ × ℕ,
        ((fun P => quadRatio P h k) ⁻¹' offResonant α δ).indicator
          (fun P => ‖quadTerm ψ α β N T P h k‖) P ≤ C * N * T ^ 2 / (T ^ r * δ ^ r) := by
  have hψC : ∀ r : ℕ, ContDiff ℝ r (fun y : ℝ => (ψ y : ℂ)) := fun r =>
    Complex.ofRealCLM.contDiff.comp (hψ r)
  have hsuppC := complex_support_subset hsupp
  choose Ψ hΨ using fun j => exists_bound_iteratedDeriv hψC hsuppC j
  obtain ⟨C₅, hC₅, hlat⟩ := exists_norm_latticeSum_cutoff_le hψC hsuppC hΨ (β := β) hα r
  refine ⟨4 * (C₅ / (2 * Real.pi)) * pairSum, by have := pairSum_nonneg; positivity,
    fun N {T} hT hβ {δ} hδ => ?_⟩
  have hT0 : 0 < T := by linarith
  have hB : 0 ≤ C₅ / (2 * Real.pi) * T ^ 2 / (T ^ r * δ ^ r) := by positivity
  refine (sum_quadruple_le (S := fun h k => (fun P => quadRatio P h k) ⁻¹' offResonant α δ)
    (f := fun P h k => ‖quadTerm ψ α β N T P h k‖) hB (fun h hh k hk P hP => ?_)
    (fun _ _ _ => norm_nonneg _)).trans (le_of_eq (by ring))
  have hh0 := (Finset.mem_Icc.mp hh).1
  have hk0 := (Finset.mem_Icc.mp hk).1
  have hu : α * quadFreq P h k / (2 * Real.pi) = ratioPhase α (quadRatio P h k) := by
    unfold ratioPhase; rw [quadFreq_eq_ratio P hh0 hk0]
  have hprod := ZetaNotch.pairProd_pos P
  have hl := hlat T hT hβ (2 * Real.pi * pairProd P) (by positivity)
    (α * quadFreq P h k / (2 * Real.pi)) δ hδ (by rw [hu]; exact hP)
  rw [norm_quadTerm_eq]
  have h0 : 0 ≤ |mollAmp N h| * |mollAmp N k| * pairAmp P := by
    have := (ZetaNotch.pairAmp_pos P).le; positivity
  refine mul_le_mul_of_nonneg_left (hl.trans (le_of_eq ?_)) h0
  rw [Real.rpow_neg_one]
  field_simp

/-! ## Near-diagonal ratios -/

theorem one_div_max_le_abs_log_sub {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : 1 ≤ |x - y|) :
    1 / max x y ≤ |Real.log x - Real.log y| := by
  rcases le_total y x with h | h
  · have hy0 : 0 < y := by linarith
    have hx0 : 0 < x := by linarith
    rw [max_eq_left h, abs_of_nonneg (by linarith [Real.log_le_log hy0 h])]
    rw [abs_of_nonneg (by linarith)] at hxy
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne', inv_div] at hl
    have : 1 / x ≤ 1 - y / x := by
      rw [div_le_iff₀ hx0, sub_mul, div_mul_cancel₀ _ hx0.ne']; linarith
    linarith
  · have hy0 : 0 < y := by linarith
    have hx0 : 0 < x := by linarith
    rw [max_eq_right h, abs_of_nonpos (by linarith [Real.log_le_log hx0 h])]
    rw [abs_of_nonpos (by linarith)] at hxy
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne', inv_div] at hl
    have : 1 / y ≤ 1 - x / y := by
      rw [div_le_iff₀ hy0, sub_mul, div_mul_cancel₀ _ hy0.ne']; linarith
    linarith

/-- **Near-diagonal quadruples have large `mn`.** If `nk ≠ mh` and `|log(nk/mh)| < δ' ≤ 1`, then
`mn ≥ 1/(e δ'² N²)`. -/
theorem pairProd_ge_of_near_diagonal {P : ℕ × ℕ} {h k N : ℕ} (hh : h ∈ Finset.Icc 1 N)
    (hk : k ∈ Finset.Icc 1 N) {δ' : ℝ} (hδ' : 0 < δ') (hδ1 : δ' ≤ 1)
    (hne : quadRatio P h k ≠ (1, 1)) (hlog : |quadFreq P h k| < δ') :
    1 / (Real.exp 1 * δ' ^ 2 * (N : ℝ) ^ 2) ≤ pairProd P := by
  obtain ⟨hh1, hhN⟩ := Finset.mem_Icc.mp hh
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
  set x : ℝ := ((P.2 : ℝ) + 1) * k
  set y : ℝ := ((P.1 : ℝ) + 1) * h
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hP2 : (1 : ℝ) ≤ (P.2 : ℝ) + 1 := by linarith [(P.2.cast_nonneg : (0:ℝ) ≤ P.2)]
  have hP1 : (1 : ℝ) ≤ (P.1 : ℝ) + 1 := by linarith [(P.1.cast_nonneg : (0:ℝ) ≤ P.1)]
  have hx1 : 1 ≤ x := by nlinarith
  have hy1 : 1 ≤ y := by nlinarith
  have hfreq : quadFreq P h k = Real.log x - Real.log y := by
    unfold quadFreq pairFreq
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    ring
  -- `x ≠ y` as integers
  have hxy : 1 ≤ |x - y| := by
    have hne' : (P.2 + 1) * k ≠ (P.1 + 1) * h := by
      intro heq
      apply hne
      unfold quadRatio
      rw [heq, Nat.gcd_self, Nat.div_self (Nat.mul_pos (Nat.succ_pos _) hh1)]
    have : (x - y) = (((P.2 + 1) * k : ℕ) : ℝ) - (((P.1 + 1) * h : ℕ) : ℝ) := by
      push_cast; ring
    rw [this]
    have hz : ((((P.2 + 1) * k : ℕ) : ℤ) - (((P.1 + 1) * h : ℕ) : ℤ)) ≠ 0 := by
      intro h0; apply hne'; exact_mod_cast sub_eq_zero.mp h0
    have h1 : (1 : ℤ) ≤ |(((P.2 + 1) * k : ℕ) : ℤ) - (((P.1 + 1) * h : ℕ) : ℤ)| :=
      Int.one_le_abs hz
    exact_mod_cast h1
  have hmax := one_div_max_le_abs_log_sub hx1 hy1 hxy
  rw [← hfreq] at hmax
  have hM : 1 / δ' < max x y := by
    have hm0 : 0 < max x y := lt_of_lt_of_le zero_lt_one (le_max_of_le_left hx1)
    rw [div_lt_iff₀ hδ']
    have := lt_of_le_of_lt hmax hlog
    rw [div_lt_iff₀ hm0] at this
    linarith
  -- `min(x, y) ≥ max(x, y)/e`
  have hratio : max x y ≤ Real.exp 1 * min x y := by
    have hl : |Real.log x - Real.log y| < 1 := by rw [← hfreq]; linarith
    rcases le_total y x with h' | h'
    · rw [max_eq_left h', min_eq_right h']
      have hlt : Real.log x - Real.log y < 1 := (le_abs_self _).trans_lt hl
      have hx0 : 0 < x := by linarith
      have hy0 : 0 < y := by linarith
      rw [← Real.log_div hx0.ne' hy0.ne'] at hlt
      have := (Real.log_lt_iff_lt_exp (div_pos hx0 hy0)).mp hlt
      rw [div_lt_iff₀ hy0] at this
      linarith
    · rw [max_eq_right h', min_eq_left h']
      have hlt : Real.log y - Real.log x < 1 := by
        have := neg_abs_le (Real.log x - Real.log y); linarith
      have hx0 : 0 < x := by linarith
      have hy0 : 0 < y := by linarith
      rw [← Real.log_div hy0.ne' hx0.ne'] at hlt
      have := (Real.log_lt_iff_lt_exp (div_pos hy0 hx0)).mp hlt
      rw [div_lt_iff₀ hx0] at this
      linarith
  have hxyprod : x * y = max x y * min x y := by
    rcases le_total y x with h' | h'
    · rw [max_eq_left h', min_eq_right h']
    · rw [max_eq_right h', min_eq_left h']; ring
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast le_trans hh1 hhN
  have hprod : pairProd P * ((h : ℝ) * k) = x * y := by
    unfold pairProd; simp only [x, y]; ring
  have hhk : (h : ℝ) * k ≤ (N : ℝ) ^ 2 := by
    have : (h : ℝ) ≤ N := by exact_mod_cast hhN
    have : (k : ℝ) ≤ N := by exact_mod_cast hkN
    nlinarith
  have hmin : max x y / Real.exp 1 ≤ min x y := by
    rw [div_le_iff₀ (Real.exp_pos 1)]; linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hM0 : 0 < max x y := lt_of_lt_of_le zero_lt_one (le_max_of_le_left hx1)
  have key : 1 / (Real.exp 1 * δ' ^ 2) ≤ x * y := by
    rw [hxyprod]
    have h1 : (1 / δ') ^ 2 ≤ (max x y) ^ 2 := by
      have := hM.le
      exact pow_le_pow_left₀ (by positivity) this 2
    calc 1 / (Real.exp 1 * δ' ^ 2) = (1 / δ') ^ 2 / Real.exp 1 := by field_simp
      _ ≤ (max x y) ^ 2 / Real.exp 1 := by gcongr
      _ = max x y * (max x y / Real.exp 1) := by ring
      _ ≤ max x y * min x y := by gcongr
  have hhk0 : 0 < (h : ℝ) * k := by positivity
  calc 1 / (Real.exp 1 * δ' ^ 2 * (N : ℝ) ^ 2) = 1 / (Real.exp 1 * δ' ^ 2) / (N : ℝ) ^ 2 := by
        field_simp
    _ ≤ x * y / ((h : ℝ) * k) := by
        apply div_le_div₀ (by positivity) key hhk0 hhk
    _ = pairProd P := by rw [← hprod]; field_simp

/-- The near-diagonal ratios `{c ≠ (1,1) : |u(c)| < δ}`. -/
def nearDiagonal (α δ : ℝ) : Set (ℕ × ℕ) := {c | c ≠ (1, 1) ∧ |ratioPhase α c| < δ}

/-- **Near-diagonal quadruples** contribute
`≤ 4N (T+1) Ψ₀ K (3αT/2π)^A (e δ'² N²)^{A−1} Σ(mn)^{−3/2}`, `δ' = 2πδ/α`. -/
theorem sum_nearDiagonal_le {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {Ψ₀ : ℝ}
    (hΨ : ∀ y, |ψ y| ≤ Ψ₀) {α β : ℝ} (hα : 0 < α) {A : ℝ} (hA : 1 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ}, 0 < T → 2 * |β| ≤ α * T → ∀ {δ : ℝ}, 0 < δ →
      2 * Real.pi * δ / α ≤ 1 →
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ∑' P : ℕ × ℕ,
        ((fun P => quadRatio P h k) ⁻¹' nearDiagonal α δ).indicator
          (fun P => ‖quadTerm ψ α β N T P h k‖) P ≤
        4 * N * (((T + 1) * (Ψ₀ * (K * (3 * α * T / (2 * Real.pi)) ^ A)) *
          (Real.exp 1 * (2 * Real.pi * δ / α) ^ 2 * (N : ℝ) ^ 2) ^ (A - 1)) * pairSum) := by
  obtain ⟨K, hK, hdec⟩ := exists_norm_latticeSum_cutoff_le_decay (by linarith : (0 : ℝ) < A)
  refine ⟨K, hK, fun N {T} hT hβ {δ} hδ hδ1 => ?_⟩
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  have hsuppC := complex_support_subset hsupp
  have hΨC : ∀ y, ‖(ψ y : ℂ)‖ ≤ Ψ₀ := fun y => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hΨ y
  set δ' : ℝ := 2 * Real.pi * δ / α with hδ'
  have hδ'0 : 0 < δ' := by positivity
  set B : ℝ := (T + 1) * (Ψ₀ * (K * (3 * α * T / (2 * Real.pi)) ^ A)) *
    (Real.exp 1 * δ' ^ 2 * (N : ℝ) ^ 2) ^ (A - 1)
  have hB : 0 ≤ B := by positivity
  refine sum_quadruple_le (S := fun h k => (fun P => quadRatio P h k) ⁻¹' nearDiagonal α δ)
    (f := fun P h k => ‖quadTerm ψ α β N T P h k‖) hB (fun h hh k hk P hP => ?_)
    (fun _ _ _ => norm_nonneg _)
  obtain ⟨hne, hu⟩ := hP
  have hh0 := (Finset.mem_Icc.mp hh).1
  have hk0 := (Finset.mem_Icc.mp hk).1
  have hlog : |quadFreq P h k| < δ' := by
    have e : ratioPhase α (quadRatio P h k) = α * quadFreq P h k / (2 * Real.pi) := by
      unfold ratioPhase; rw [quadFreq_eq_ratio P hh0 hk0]
    rw [e, abs_div, abs_mul, abs_of_pos hα, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      div_lt_iff₀ (by positivity)] at hu
    rw [hδ', lt_div_iff₀ hα]
    linarith
  have hX := pairProd_ge_of_near_diagonal hh hk hδ'0 hδ1 hne hlog
  have hprod := ZetaNotch.pairProd_pos P
  have hX0 : 0 < 1 / (Real.exp 1 * δ' ^ 2 * (N : ℝ) ^ 2) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast le_trans hh0 (Finset.mem_Icc.mp hh).2
    positivity
  have hl := hdec hsuppC hΨC hα hT hβ (c := 2 * Real.pi * pairProd P) (by positivity)
    (α * quadFreq P h k / (2 * Real.pi))
  rw [norm_quadTerm_eq]
  have h0 : 0 ≤ |mollAmp N h| * |mollAmp N k| * pairAmp P := by
    have := (ZetaNotch.pairAmp_pos P).le; positivity
  refine mul_le_mul_of_nonneg_left (hl.trans ?_) h0
  -- `(3αT/2πmn)^A ≤ (3αT/2π)^A X^{−(A−1)} (mn)^{−1}`
  have hsplit : (3 * α * T / (2 * Real.pi * pairProd P)) ^ A =
      (3 * α * T / (2 * Real.pi)) ^ A * (pairProd P ^ (-(A - 1)) * pairProd P ^ (-(1 : ℝ))) := by
    rw [← Real.rpow_add hprod, show -(A - 1) + -(1 : ℝ) = -A by ring, Real.rpow_neg hprod.le,
      ← div_eq_mul_inv, ← Real.div_rpow (by positivity) hprod.le, div_div]
  have hpow : pairProd P ^ (-(A - 1)) ≤ (Real.exp 1 * δ' ^ 2 * (N : ℝ) ^ 2) ^ (A - 1) := by
    calc pairProd P ^ (-(A - 1)) ≤ (1 / (Real.exp 1 * δ' ^ 2 * (N : ℝ) ^ 2)) ^ (-(A - 1)) :=
          Real.rpow_le_rpow_of_nonpos hX0 hX (by linarith)
      _ = (Real.exp 1 * δ' ^ 2 * (N : ℝ) ^ 2) ^ (A - 1) := by
          rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  rw [hsplit]
  have hr1 : 0 ≤ pairProd P ^ (-(1 : ℝ)) := Real.rpow_nonneg hprod.le _
  calc (T + 1) * (Ψ₀ * (K * ((3 * α * T / (2 * Real.pi)) ^ A *
        (pairProd P ^ (-(A - 1)) * pairProd P ^ (-(1 : ℝ))))))
      ≤ (T + 1) * (Ψ₀ * (K * ((3 * α * T / (2 * Real.pi)) ^ A *
          ((Real.exp 1 * δ' ^ 2 * (N : ℝ) ^ 2) ^ (A - 1) * pairProd P ^ (-(1 : ℝ)))))) := by
        gcongr
    _ = B * pairProd P ^ (-(1 : ℝ)) := by ring

end

end RHTower.VerticalAP
