import GaloisForLFunctions.RHTower.MontgomeryAveragedForm
import GaloisForLFunctions.RHTower.ZetaCriticalRowBound

/-!
# The averaged pair form split into bulk rows and low pairs

Let `P = P_R(T)` be the averaged Montgomery form, a double sum over zero copies with `0 < γ ≤ T` of
`x^z w(z) K̃_c(z)`, where `z = ρ + ρ̄' − 1`, `x = T^{α₀}` and `c = log T/R`. Fix `Y > 0` and call a
zero *low* if `γ < Y` and *bulk* otherwise.

* `norm_pairTerm_le`: `‖x^z w(z) K̃_c(z)‖ ≤ 8 x e^c /(1 + (γ − γ')²)`. Here `|Re z| < 1`, so
  `|4 − z²| ≥ 3 + (Im z)²` and `‖K̃_c(z)‖ ≤ 2 e^{c|Re z|}`.
* `pairTerm_eq_of_online`: on the critical line, the pair term is the Fejér row term
  `e^{iθΔ} · 4/(4 + Δ²) · K_c(Δ)`, with `θ = α₀ log T` and `Δ = γ − γ'`.
* `norm_averagedMontgomeryForm_sub_bulk_le`: if every bulk zero is on the line, then
  `‖P − Σ_{n ∈ I} Ψ_n‖ ≤ 16 x e^c · #low · 8(C + log(T + 4))`. Here `I` is the set of ordered
  indices with `Y ≤ γ_n ≤ T` and `Ψ_n = critRow θ c I n`.
-/

noncomputable section

open Complex Finset
open GaloisForLFunctions.HTGeometry (triangleFn triangleFn_nonneg triangleFn_le_one fejerKernel)

namespace RHTower

/-- `‖w(z)‖ ≤ 4/(3 + (Im z)²)` for `|Re z| ≤ 1`. -/
theorem norm_montgomeryWeight_le {z : ℂ} (hz : |z.re| ≤ 1) :
    ‖montgomeryWeight z‖ ≤ 4 / (3 + z.im ^ 2) := by
  unfold montgomeryWeight
  have hre2 : z.re ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg z.re]
  have h1 : 3 + z.im ^ 2 ≤ ‖(4 : ℂ) - z ^ (2 : ℕ)‖ := by
    have hre : ((4 : ℂ) - z ^ (2 : ℕ)).re = 4 - z.re ^ 2 + z.im ^ 2 := by
      simp only [sub_re, pow_two, mul_re]; norm_num; ring
    have := Complex.re_le_norm ((4 : ℂ) - z ^ (2 : ℕ))
    linarith
  rw [norm_div, show ‖(4 : ℂ)‖ = 4 by norm_num]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h1

/-- `‖K̃_c(z)‖ ≤ 2 e^{c|Re z|}`. -/
theorem norm_fejerKernelC_le {c : ℝ} (hc : 0 ≤ c) (z : ℂ) :
    ‖fejerKernelC c z‖ ≤ 2 * Real.exp (c * |z.re|) := by
  unfold fejerKernelC
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1) (b := 1)
    (C := Real.exp (c * |z.re|))
    (f := fun β : ℝ => ((triangleFn 1 β : ℝ) : ℂ) * Complex.exp ((β * c : ℝ) * z)) ?_
  · rw [show |(1 : ℝ) - -1| = 2 by norm_num] at h
    linarith
  intro β hβ
  rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at hβ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (triangleFn_nonneg _ _),
    Complex.norm_exp]
  have h1 := triangleFn_le_one one_pos β
  have h2 : (((β * c : ℝ) : ℂ) * z).re ≤ c * |z.re| := by
    rw [Complex.re_ofReal_mul]
    have hb : |β| ≤ 1 := abs_le.mpr ⟨by linarith, hβ.2⟩
    calc β * c * z.re ≤ |β * c * z.re| := le_abs_self _
      _ = |β| * c * |z.re| := by rw [abs_mul, abs_mul, abs_of_nonneg hc]
      _ ≤ 1 * c * |z.re| := by gcongr
      _ = c * |z.re| := by ring
  calc triangleFn 1 β * Real.exp (((β * c : ℝ) : ℂ) * z).re
      ≤ 1 * Real.exp (c * |z.re|) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr h2) (by positivity) zero_le_one
    _ = Real.exp (c * |z.re|) := one_mul _

/-- **The pair term bound.** -/
theorem norm_pairTerm_le {T α₀ R : ℝ} (hT : 1 ≤ T) (hα : 0 ≤ α₀) (hR : 0 < R) (q q' : XiZeroCopy) :
    ‖((T ^ α₀ : ℝ) : ℂ) ^ ((q.1 : ℂ) + (starRingEnd ℂ) (q'.1 : ℂ) - 1) *
        montgomeryWeight ((q.1 : ℂ) + (starRingEnd ℂ) (q'.1 : ℂ) - 1) *
        fejerKernelC (Real.log T / R) ((q.1 : ℂ) + (starRingEnd ℂ) (q'.1 : ℂ) - 1)‖ ≤
      8 * T ^ α₀ * Real.exp (Real.log T / R) * lorentzMassTerm ((q.1 : ℂ).im) q' := by
  set z := (q.1 : ℂ) + (starRingEnd ℂ) (q'.1 : ℂ) - 1 with hz
  have hre : z.re = (q.1 : ℂ).re + (q'.1 : ℂ).re - 1 := by simp [hz]
  have him : z.im = (q.1 : ℂ).im - (q'.1 : ℂ).im := by simp [hz]; ring
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have h0' := xiZeroCopy_re_pos q'
  have h1' := xiZeroCopy_re_lt_one q'
  have hzre : |z.re| ≤ 1 := by rw [hre, abs_le]; constructor <;> linarith
  have hx1 : 1 ≤ T ^ α₀ := Real.one_le_rpow hT hα
  have hc : 0 ≤ Real.log T / R := div_nonneg (Real.log_nonneg hT) hR.le
  have hA : ‖((T ^ α₀ : ℝ) : ℂ) ^ z‖ ≤ T ^ α₀ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    calc (T ^ α₀) ^ z.re ≤ (T ^ α₀) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hre]; linarith)
      _ = T ^ α₀ := Real.rpow_one _
  have hW : ‖montgomeryWeight z‖ ≤ 4 * lorentzMassTerm ((q.1 : ℂ).im) q' := by
    refine (norm_montgomeryWeight_le hzre).trans ?_
    unfold lorentzMassTerm
    rw [him, mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hK : ‖fejerKernelC (Real.log T / R) z‖ ≤ 2 * Real.exp (Real.log T / R) := by
    refine (norm_fejerKernelC_le hc z).trans ?_
    gcongr
    calc Real.log T / R * |z.re| ≤ Real.log T / R * 1 := mul_le_mul_of_nonneg_left hzre hc
      _ = Real.log T / R := mul_one _
  rw [norm_mul, norm_mul]
  have hL := lorentzMassTerm_nonneg ((q.1 : ℂ).im) q'
  calc ‖((T ^ α₀ : ℝ) : ℂ) ^ z‖ * ‖montgomeryWeight z‖ * ‖fejerKernelC (Real.log T / R) z‖
      ≤ T ^ α₀ * (4 * lorentzMassTerm ((q.1 : ℂ).im) q') * (2 * Real.exp (Real.log T / R)) := by
        gcongr
    _ = 8 * T ^ α₀ * Real.exp (Real.log T / R) * lorentzMassTerm ((q.1 : ℂ).im) q' := by ring

/-- The pair term on the critical line is the Fejér row term. -/
theorem pairTerm_eq_of_online {T α₀ c γ γ' : ℝ} (hT : 0 < T) {ρ ρ' : ℂ}
    (hρ : ρ = 1 / 2 + (γ : ℂ) * I) (hρ' : ρ' = 1 / 2 + (γ' : ℂ) * I) :
    ((T ^ α₀ : ℝ) : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1) *
        montgomeryWeight (ρ + (starRingEnd ℂ) ρ' - 1) * fejerKernelC c (ρ + (starRingEnd ℂ) ρ' - 1) =
      Complex.exp ((α₀ * Real.log T * (γ - γ') : ℝ) * I) *
        ((4 / (4 + (γ - γ') ^ 2) : ℝ) : ℂ) * fejerKernel c (γ - γ') := by
  have hz : ρ + (starRingEnd ℂ) ρ' - 1 = ((γ - γ' : ℝ) : ℂ) * I := by
    rw [hρ, hρ']
    apply Complex.ext <;> simp <;> ring
  rw [hz, fejerKernelC_mul_I]
  have hx : ((T ^ α₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hT α₀).ne'
  have hpow : ((T ^ α₀ : ℝ) : ℂ) ^ (((γ - γ' : ℝ) : ℂ) * I) =
      Complex.exp ((α₀ * Real.log T * (γ - γ') : ℝ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hx, ← Complex.ofReal_log (Real.rpow_pos_of_pos hT α₀).le,
      Real.log_rpow hT]
    congr 1
    push_cast; ring
  have hw : montgomeryWeight (((γ - γ' : ℝ) : ℂ) * I) = ((4 / (4 + (γ - γ') ^ 2) : ℝ) : ℂ) := by
    unfold montgomeryWeight
    have hden : (4 : ℂ) - (((γ - γ' : ℝ) : ℂ) * I) ^ (2 : ℕ) = ((4 + (γ - γ') ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [I_sq]; ring
    rw [hden]; push_cast; ring
  rw [hpow, hw]

/-- The ordered indices with `Y ≤ γ_n ≤ T`. -/
def bulkIndices (Y T : ℝ) : Finset ℕ :=
  (xiOrderedPositiveOrdinateCountFinset T).filter (fun n => Y ≤ xiOrderedPositiveOrdinate n)

theorem mem_bulkIndices {Y T : ℝ} {n : ℕ} :
    n ∈ bulkIndices Y T ↔ Y ≤ xiOrderedPositiveOrdinate n ∧ xiOrderedPositiveOrdinate n ≤ T := by
  rw [bulkIndices, Finset.mem_filter, mem_xiOrderedPositiveOrdinateCountFinset_iff, and_comm]

/-- The bulk copies are the ordered copies with indices in `bulkIndices`. -/
theorem filter_zeroWindow_eq_map_bulkIndices (Y T : ℝ) :
    (zeroWindow T).filter (fun q : XiZeroCopy => Y ≤ (q.1 : ℂ).im) =
      (bulkIndices Y T).map ⟨xiOrderedPositiveZeroCopy, xiOrderedPositiveZeroCopy_injective⟩ := by
  ext q
  rw [Finset.mem_filter, mem_zeroWindow, Finset.mem_map]
  constructor
  · rintro ⟨⟨h0, hT⟩, hY'⟩
    obtain ⟨n, rfl⟩ := exists_index_of_im_pos h0
    refine ⟨n, ?_, rfl⟩
    rw [mem_bulkIndices, ← xiOrderedPositiveZeroCopy_im_eq]
    exact ⟨hY', hT⟩
  · rintro ⟨n, hn, rfl⟩
    rw [mem_bulkIndices] at hn
    simp only [Function.Embedding.coeFn_mk, xiOrderedPositiveZeroCopy_im_eq]
    exact ⟨⟨xiOrderedPositiveOrdinate_pos n, hn.2⟩, hn.1⟩


/-- The pair term of two zero copies. -/
def pairTerm (α₀ R T : ℝ) (q q' : XiZeroCopy) : ℂ :=
  ((T ^ α₀ : ℝ) : ℂ) ^ ((q.1 : ℂ) + (starRingEnd ℂ) (q'.1 : ℂ) - 1) *
    montgomeryWeight ((q.1 : ℂ) + (starRingEnd ℂ) (q'.1 : ℂ) - 1) *
    fejerKernelC (Real.log T / R) ((q.1 : ℂ) + (starRingEnd ℂ) (q'.1 : ℂ) - 1)

theorem averagedMontgomeryForm_eq_sum_pairTerm {α₀ R T : ℝ} (hT : 0 < T) :
    averagedMontgomeryForm α₀ R T =
      ∑ q ∈ zeroWindow T, ∑ q' ∈ zeroWindow T, pairTerm α₀ R T q q' :=
  averagedMontgomeryForm_eq hT

/-- **The bulk double sum is the sum of the Fejér rows.** -/
theorem sum_bulk_pairTerm_eq {α₀ R T Y : ℝ} (hT : 0 < T)
    (hRH : ∀ n ∈ bulkIndices Y T, ((xiOrderedPositiveZeroCopy n).1 : ℂ).re = 1 / 2) :
    ∑ q ∈ (zeroWindow T).filter (fun q : XiZeroCopy => Y ≤ (q.1 : ℂ).im),
        ∑ q' ∈ (zeroWindow T).filter (fun q : XiZeroCopy => Y ≤ (q.1 : ℂ).im),
          pairTerm α₀ R T q q' =
      ∑ n ∈ bulkIndices Y T, critRow (α₀ * Real.log T) (Real.log T / R) (bulkIndices Y T) n := by
  rw [filter_zeroWindow_eq_map_bulkIndices, Finset.sum_map]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_map]
  unfold critRow
  refine Finset.sum_congr rfl fun m hm => ?_
  have hline : ∀ k ∈ bulkIndices Y T, ((xiOrderedPositiveZeroCopy k).1 : ℂ) =
      1 / 2 + (xiOrderedPositiveOrdinate k : ℂ) * I := by
    intro k hk
    apply Complex.ext
    · rw [hRH k hk]; simp
    · rw [xiOrderedPositiveZeroCopy_im_eq]; simp
  simp only [Function.Embedding.coeFn_mk, pairTerm]
  exact pairTerm_eq_of_online hT (hline n hn) (hline m hm)

/-- **The low pairs.** -/
theorem norm_sum_sub_bulk_le {α₀ R T Y : ℝ} (hT : 1 ≤ T) (hα : 0 ≤ α₀) (hR : 0 < R) :
    ‖∑ q ∈ zeroWindow T, ∑ q' ∈ zeroWindow T, pairTerm α₀ R T q q' -
        ∑ q ∈ (zeroWindow T).filter (fun q : XiZeroCopy => Y ≤ (q.1 : ℂ).im),
          ∑ q' ∈ (zeroWindow T).filter (fun q : XiZeroCopy => Y ≤ (q.1 : ℂ).im),
            pairTerm α₀ R T q q'‖ ≤
      2 * (((zeroWindow T).filter (fun q : XiZeroCopy => ¬ Y ≤ (q.1 : ℂ).im)).card : ℝ) *
        (8 * T ^ α₀ * Real.exp (Real.log T / R) *
          (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4)))) := by
  classical
  set W := zeroWindow T with hW
  set Bk := W.filter (fun q : XiZeroCopy => Y ≤ (q.1 : ℂ).im) with hBk
  set Lo := W.filter (fun q : XiZeroCopy => ¬ Y ≤ (q.1 : ℂ).im) with hLo
  set f := pairTerm α₀ R T with hf
  set K := 8 * T ^ α₀ * Real.exp (Real.log T / R) with hK
  set Λ := 8 * (xiLineTwoLogDerivConstant + Real.log (T + 4)) with hΛ
  have hsplit : ∑ q ∈ W, ∑ q' ∈ W, f q q' - ∑ q ∈ Bk, ∑ q' ∈ Bk, f q q' =
      ∑ q ∈ Lo, ∑ q' ∈ W, f q q' + ∑ q' ∈ Lo, ∑ q ∈ Bk, f q q' := by
    rw [← Finset.sum_filter_add_sum_filter_not W (fun q : XiZeroCopy => Y ≤ (q.1 : ℂ).im)]
    have h2 : ∑ q ∈ Bk, ∑ q' ∈ W, f q q' = ∑ q ∈ Bk, ∑ q' ∈ Bk, f q q' +
        ∑ q ∈ Bk, ∑ q' ∈ Lo, f q q' := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      exact (Finset.sum_filter_add_sum_filter_not W _ _).symm
    rw [h2, Finset.sum_comm (s := Bk) (t := Lo)]
    ring
  rw [hsplit]
  -- every zero window copy has ordinate in `(0, T]`
  have hrow : ∀ q : XiZeroCopy, q ∈ W → ∀ S ⊆ W,
      ∑ q' ∈ S, lorentzMassTerm ((q.1 : ℂ).im) q' ≤ Λ := by
    intro q hq S _
    have hqT := (mem_zeroWindow.mp hq)
    refine ((summable_lorentzMassTerm _).sum_le_tsum S
      (fun q' _ => lorentzMassTerm_nonneg _ q')).trans ?_
    refine (lorentzMass_le_log _).trans ?_
    rw [hΛ, abs_of_pos hqT.1]
    gcongr
    · linarith [hqT.1]
    · exact hqT.2
  have hK0 : 0 ≤ K := by positivity
  have hsym : ∀ q q' : XiZeroCopy,
      lorentzMassTerm ((q.1 : ℂ).im) q' = lorentzMassTerm ((q'.1 : ℂ).im) q := by
    intro q q'; unfold lorentzMassTerm; ring_nf
  have hA : ‖∑ q ∈ Lo, ∑ q' ∈ W, f q q'‖ ≤ Lo.card * (K * Λ) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (K * Λ) fun q hq => ?_).trans (by rw [nsmul_eq_mul])
    refine (norm_sum_le _ _).trans ?_
    calc ∑ q' ∈ W, ‖f q q'‖ ≤ ∑ q' ∈ W, K * lorentzMassTerm ((q.1 : ℂ).im) q' :=
          Finset.sum_le_sum fun q' _ => norm_pairTerm_le hT hα hR q q'
      _ = K * ∑ q' ∈ W, lorentzMassTerm ((q.1 : ℂ).im) q' := by rw [Finset.mul_sum]
      _ ≤ K * Λ := by
          gcongr; exact hrow q (Finset.mem_filter.mp hq).1 W subset_rfl
  have hB : ‖∑ q' ∈ Lo, ∑ q ∈ Bk, f q q'‖ ≤ Lo.card * (K * Λ) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (K * Λ) fun q' hq' => ?_).trans (by rw [nsmul_eq_mul])
    refine (norm_sum_le _ _).trans ?_
    calc ∑ q ∈ Bk, ‖f q q'‖ ≤ ∑ q ∈ Bk, K * lorentzMassTerm ((q'.1 : ℂ).im) q :=
          Finset.sum_le_sum fun q _ => by rw [← hsym]; exact norm_pairTerm_le hT hα hR q q'
      _ = K * ∑ q ∈ Bk, lorentzMassTerm ((q'.1 : ℂ).im) q := by rw [Finset.mul_sum]
      _ ≤ K * Λ := by
          gcongr
          exact hrow q' (Finset.mem_filter.mp hq').1 Bk (Finset.filter_subset _ _)
  calc ‖∑ q ∈ Lo, ∑ q' ∈ W, f q q' + ∑ q' ∈ Lo, ∑ q ∈ Bk, f q q'‖
      ≤ ‖∑ q ∈ Lo, ∑ q' ∈ W, f q q'‖ + ‖∑ q' ∈ Lo, ∑ q ∈ Bk, f q q'‖ := norm_add_le _ _
    _ ≤ Lo.card * (K * Λ) + Lo.card * (K * Λ) := add_le_add hA hB
    _ = 2 * (Lo.card : ℝ) * (K * Λ) := by ring

end RHTower
