import GaloisForLFunctions.RHTower.EvenSectorAbelRigidity
import GaloisForLFunctions.RHTower.WeilEvenConeOneSidedCriterion
import GaloisForLFunctions.RHTower.WeilParityPoleWeightWindows

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open OddSector ResonatorProfile WeilOneSided WeilMeanSquare WeilSpectral WeilPoleWeight

/-! ## Section 1: The even Weil–Toeplitz bound for nonnegative coefficients and positive-part summability -/

theorem resonator_ofRealCoeff (N : ℕ) (c : ℕ → ℝ) (w : ℝ) :
    resonator N (fun m => (c m : ℂ)) w =
      fun u => ((∑ m ∈ Finset.Icc 1 N, c m * gR w (u - resPt N m) : ℝ) : ℂ) := by
  funext u
  unfold resonator
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.ofReal_mul]
  rfl

/-- Even positivity at any pole weight gives the Toeplitz hypothesis on every even resonator with
nonnegative coefficients. -/
theorem integral_weilAtomSymbol_evenResonator_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) (N : ℕ) (c : ℕ → ℝ) (hc0 : ∀ m, 0 ≤ c m) :
    0 ≤ ∫ τ : ℝ, ‖paperFT (resonator N (fun m => (c m : ℂ)) (1 / ((N : ℝ) + 1))) τ‖ ^ 2 *
      weilAtomSymbol lam ⌊Real.exp (2 * (Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4))⌋₊
        (τ / (2 * π)) := by
  have hw : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨hp1, hp2⟩ := paperFT_resonator_pole (N := N) (c := fun m => (c m : ℂ)) hw
  have ha : 0 ≤ Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4 := by
    have := Real.log_natCast_nonneg N
    positivity
  refine integral_weilAtomSymbol_nonneg_of_polar ha (contDiff_resonator N _ _ 2)
    (tsupport_subset_of_vanish fun u hu => sum_translates_eq_zero
      (fun v hv => gC_eq_zero hw hv) hu) hp1 hp2 ?_
  have hgc : HasCompactSupport (gR (1 / ((N : ℝ) + 1))) :=
    (hasCompactSupport_comp_left (g := Complex.ofReal) fun {_} => Complex.ofReal_eq_zero).mp
      (hasCompactSupport_gC hw)
  rw [resonator_ofRealCoeff]
  exact re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenAt h (Finset.Icc 1 N)
    (fun m _ => hc0 m) (resPt N) (contDiff_gR _ 2) hgc (gR_neg _) (paperFT_gC_pole hw).1

/-- The even Toeplitz constant `C₀ = log 2 + 9/2 + profileRatio/2`. -/
def evenToeplitzConst : ℝ := Real.log 2 + 9 / 2 + profileRatio / 2

/-- **The even Weil–Toeplitz bound for nonnegative coefficients.** -/
theorem even_toeplitz_bound_nonneg {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam) {N : ℕ}
    (hN : 1 ≤ N) (c : ℕ → ℝ) (hc0 : ∀ m, 0 ≤ c m) (hc : ∀ m, N < m → c m = 0) :
    2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m ≤
      (Real.log N + evenToeplitzConst) * ∑ m ∈ Finset.Icc 1 N, c m ^ 2 := by
  have hcC : ∀ m, N < m → (c m : ℂ) = 0 := fun m hm => by rw [hc m hm, Complex.ofReal_zero]
  have hb := weil_multiplicativeToeplitz_bound_of_resonator hN (fun m => (c m : ℂ)) hcC
    (integral_weilAtomSymbol_evenResonator_nonneg h N c hc0)
  have hl : ∀ n, (∑ m ∈ Finset.Icc 1 N, (c (n * m) : ℂ) * conj (c m : ℂ)).re =
      ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m := fun n => by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hr : ∑ m ∈ Finset.Icc 1 N, ‖(c m : ℂ)‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, c m ^ 2 :=
    Finset.sum_congr rfl fun m _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hl, hr] at hb
  exact hb

/-- **Even positivity at any pole weight bounds the weights in mean square on primitive sets where
they are nonnegative.** -/
theorem even_sum_sq_div_le_of_primitive {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam) {N : ℕ}
    (hN : 1 ≤ N) :
    0 ≤ Real.log N + evenToeplitzConst ∧
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S → (∀ n ∈ S, 0 ≤ lam n) →
        ∑ n ∈ S, lam n ^ 2 / n ≤ (Real.log N + evenToeplitzConst) ^ 2 := by
  have key : ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S → (∀ n ∈ S, 0 ≤ lam n) →
      ∀ t : ℝ, 0 ≤ t → 2 * t * ∑ n ∈ S, lam n ^ 2 / n ≤
        (Real.log N + evenToeplitzConst) * (1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n) := by
    intro S hS hprim hpos t ht
    set c : ℕ → ℝ := fun m => if m = 1 then 1 else if m ∈ S then t * lam m / Real.sqrt m else 0
      with hc
    have hc0 : ∀ m, 0 ≤ c m := fun m => by
      simp only [hc]
      split_ifs with h1 h2
      · norm_num
      · exact div_nonneg (mul_nonneg ht (hpos m h2)) (Real.sqrt_nonneg _)
      · exact le_rfl
    have hcN : ∀ m, N < m → c m = 0 := by
      intro m hm
      have h1 : m ≠ 1 := by omega
      have h2 : m ∉ S := fun h' => by have := (Finset.mem_Icc.mp (hS h')).2; omega
      simp [hc, h1, h2]
    have hb := even_toeplitz_bound_nonneg h hN c hc0 hcN
    have hinner : ∀ n ∈ Finset.Icc 2 N,
        ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m = if n ∈ S then t * lam n / Real.sqrt n else 0 := by
      intro n hn
      obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hrest : ∑ m ∈ (Finset.Icc 1 N).erase 1, c (n * m) * c m = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        obtain ⟨hm1, hmI⟩ := Finset.mem_erase.mp hm
        by_cases hmS : m ∈ S
        · have hnm1 : n * m ≠ 1 := by
            have := (Finset.mem_Icc.mp hmI).1; nlinarith
          have hnmS : n * m ∉ S := fun h' => hprim _ h' m hmS n hn2 rfl
          simp [hc, hnm1, hnmS]
        · simp [hc, hm1, hmS]
      rw [hrest, add_zero, mul_one]
      have hn1 : n ≠ 1 := by omega
      by_cases hnS : n ∈ S
      · simp [hc, hn1, hnS]
      · simp [hc, hn1, hnS]
    have hmass : ∑ m ∈ Finset.Icc 1 N, c m ^ 2 = 1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hS' : S ⊆ (Finset.Icc 1 N).erase 1 := fun n hn => by
        have := Finset.mem_Icc.mp (hS hn)
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, this.2⟩⟩
      rw [← Finset.sum_subset hS' (fun m hm hmS => by
        have hm1 := (Finset.mem_erase.mp hm).1
        simp [hc, hm1, hmS]), Finset.mul_sum]
      congr 1
      · simp [hc]
      · refine Finset.sum_congr rfl fun n hn => ?_
        have hn2 := (Finset.mem_Icc.mp (hS hn)).1
        have hn1 : n ≠ 1 := by omega
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        simp only [hc, hn1, hn, if_false, if_true, div_pow, mul_pow, Real.sq_sqrt hn0.le]
        ring
    have hlhs : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m = t * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [Finset.sum_congr rfl fun n hn => by rw [hinner n hn], Finset.mul_sum]
      rw [← Finset.sum_subset hS (fun n _ hnS => by simp [hnS])]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 := (Finset.mem_Icc.mp (hS hn)).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      rw [if_pos hn, show lam n / Real.sqrt n * (t * lam n / Real.sqrt n) =
        t * (lam n ^ 2 / (Real.sqrt n * Real.sqrt n)) by ring, hsq]
    rw [hlhs, hmass] at hb
    linarith
  have hB : 0 ≤ Real.log N + evenToeplitzConst := by
    have := key ∅ (Finset.empty_subset _) (fun m hm => absurd hm (Finset.notMem_empty m))
      (fun n hn => absurd hn (Finset.notMem_empty n)) 0 le_rfl
    simpa using this
  refine ⟨hB, fun S hS hprim hpos => ?_⟩
  set Q := ∑ n ∈ S, lam n ^ 2 / n with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
  set B := Real.log N + evenToeplitzConst with hBdef
  rcases hQ0.lt_or_eq with hQpos | hQzero
  · have h1 := key S hS hprim hpos (B / Q) (div_nonneg hB hQ0)
    rw [← hQ] at h1
    have e : 2 * (B / Q) * Q = 2 * B := by field_simp
    have e2 : B * (1 + (B / Q) ^ 2 * Q) = B + B ^ 3 / Q := by field_simp
    rw [e, e2] at h1
    have h3 : B ≤ B ^ 3 / Q := by linarith
    rcases hB.lt_or_eq with hBpos | hBzero
    · rw [le_div_iff₀ hQpos] at h3
      nlinarith
    · have h4 := key S hS hprim hpos 1 zero_le_one
      rw [← hQ, ← hBzero] at h4
      nlinarith
  · rw [← hQzero]; positivity

/-- **Dyadic mean square of the positive part for even-positive weights.** -/
theorem even_sum_posPart_sq_Ioc_le {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam) {N : ℕ}
    (hN : 1 ≤ N) :
    0 ≤ Real.log (2 * N : ℕ) + evenToeplitzConst ∧
      ∑ n ∈ Finset.Ioc N (2 * N), max (lam n) 0 ^ 2 ≤
        (2 * N : ℕ) * (Real.log (2 * N : ℕ) + evenToeplitzConst) ^ 2 := by
  obtain ⟨hB, hS⟩ := even_sum_sq_div_le_of_primitive h (N := 2 * N) (by omega)
  refine ⟨hB, ?_⟩
  set S := (Finset.Ioc N (2 * N)).filter fun n => 0 ≤ lam n with hSdef
  have hsub : S ⊆ Finset.Icc 2 (2 * N) := fun n hn => by
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
  have hprim : IsPrimitiveSet S := by
    intro m hm m' hm' k hk heq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm hm'
    have : k * m' ≥ 2 * (N + 1) := Nat.mul_le_mul hk (by omega)
    omega
  have hQ := hS S hsub hprim fun n hn => (Finset.mem_filter.mp hn).2
  have h2N : (0 : ℝ) < (2 * N : ℕ) := by exact_mod_cast (show 0 < 2 * N by omega)
  have hsplit : ∑ n ∈ Finset.Ioc N (2 * N), max (lam n) 0 ^ 2 = ∑ n ∈ S, lam n ^ 2 := by
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with hn
    · rw [max_eq_left hn]
    · push Not at hn; rw [max_eq_right hn.le]; ring
  rw [hsplit]
  calc ∑ n ∈ S, lam n ^ 2
      = (2 * N : ℕ) * ∑ n ∈ S, lam n ^ 2 / (2 * N : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by field_simp
    _ ≤ (2 * N : ℕ) * ∑ n ∈ S, lam n ^ 2 / n := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) h2N.le
        rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        exact div_le_div_of_nonneg_left (sq_nonneg _) hn0 (by exact_mod_cast hn.1.2)
    _ ≤ (2 * N : ℕ) * (Real.log (2 * N : ℕ) + evenToeplitzConst) ^ 2 :=
        mul_le_mul_of_nonneg_left hQ h2N.le

/-- **Dyadic `ℓ¹` bound of the positive part for even-positive weights.** -/
theorem even_sum_posPart_Ioc_le {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam) {N : ℕ}
    (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc N (2 * N), max (lam n) 0 ≤
      3 / 2 * N * (Real.log (2 * N : ℕ) + evenToeplitzConst + 1) := by
  obtain ⟨hB, hsq⟩ := even_sum_posPart_sq_Ioc_le h hN
  have h1 := sum_abs_Ioc_le_of_sum_sq (lam := fun n => max (lam n) 0) hB hsq
  have e : ∀ n, |max (lam n) 0| = max (lam n) 0 := fun n => abs_of_nonneg (le_max_right _ _)
  simp only [e] at h1
  exact h1

/-- **The positive part of any even-positive weight system converges absolutely on `Re s > 1`.** -/
theorem summable_posPart_div_rpow_of_weilPositiveEvenAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => max (lam n) 0 / (n : ℝ) ^ σ := by
  refine summable_div_rpow_of_block (fun n => le_max_right (lam n) 0)
    (B := 3 / 2 * (2 + |evenToeplitzConst|)) (j₀ := 1) hσ fun j hj => ?_
  have hpos := even_sum_posPart_Ioc_le h (N := 2 ^ j) Nat.one_le_two_pow
  rw [show 2 * 2 ^ j = 2 ^ (j + 1) by ring] at hpos
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlog : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ≤ (j : ℝ) + 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    nlinarith
  have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
  rw [hcast] at hpos
  have t : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) + evenToeplitzConst + 1 ≤
      (2 + |evenToeplitzConst|) * ((j : ℝ) + 1) := by
    nlinarith [le_abs_self evenToeplitzConst, abs_nonneg evenToeplitzConst]
  have hpos' := hpos.trans (mul_le_mul_of_nonneg_left t (by positivity))
  nlinarith

/-! ## Section 2: One-sided negative-part Abel rigidity -/

/-- Absolute convergence of `lam` on `Re s > 1` reduces to its negative part `max (-lam n) 0`. -/
theorem summable_abs_div_rpow_of_weilPositiveEvenAt_of_negPart {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {σ : ℝ} (hσ : 1 < σ)
    (hneg : Summable fun n : ℕ => max (-lam n) 0 / (n : ℝ) ^ σ) :
    Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  refine ((summable_posPart_div_rpow_of_weilPositiveEvenAt h hσ).add hneg).congr fun n => ?_
  rw [← add_div, abs_eq_max_zero_add_max_neg_zero]

/-- On `s > 0`, `oddDirichlet lam s` is bounded below by `−oddDirichlet (max (-lam ·) 0) s`. -/
theorem neg_oddDirichlet_negPart_le {lam : ℕ → ℝ} {s : ℝ}
    (hs : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ (1 + s)) :
    -oddDirichlet (fun n => max (-lam n) 0) s ≤ oddDirichlet lam s := by
  unfold oddDirichlet
  rw [← tsum_neg]
  have h1 : Summable fun n : ℕ => -((if 2 ≤ n then max (-lam n) 0 else 0) / (n : ℝ) ^ (1 + s)) := by
    refine Summable.neg (Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs)
    · refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      split_ifs <;> [exact le_max_right _ _; exact le_rfl]
    · refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      split_ifs
      · rw [abs_eq_max_zero_add_max_neg_zero]; linarith [le_max_right (lam n) 0]
      · exact abs_nonneg _
  have h2 : Summable fun n : ℕ => (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + s) := by
    refine Summable.of_norm_bounded hs fun n => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    split_ifs
    · exact le_rfl
    · rw [abs_zero]; exact abs_nonneg _
  refine h1.tsum_le_tsum (fun n => ?_) h2
  rw [← neg_div]
  refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  split_ifs
  · linarith [le_max_left (-lam n) 0]
  · norm_num

/-- **Negative-part Abel rigidity of the even cone.**  Because the positive part of an
even-positive weight system always converges on `Re s > 1` and contributes nonnegatively to
`oddDirichlet`, even positivity at pole weight `1` requires only that the negative part
`max (-lam n) 0` converge on `Re s > 1` and have no double pole at `s = 0`. -/
theorem weilPositiveEvenAt_one_of_negPart {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam)
    (hneg : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => max (-lam n) 0 / (n : ℝ) ^ σ)
    (hdp : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ),
      s * (s * oddDirichlet (fun n => max (-lam n) 0) s) ≤ ε) :
    WeilPositiveEvenAt 1 lam := by
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ :=
    fun σ hσ => summable_abs_div_rpow_of_weilPositiveEvenAt_of_negPart h hσ (hneg σ hσ)
  refine weilPositiveEvenAt_one_of_abel h hsl fun ε hε => ?_
  filter_upwards [self_mem_nhdsWithin, hdp ε hε] with s hs hds
  have hs' : 0 < s := hs
  have hle := neg_oddDirichlet_negPart_le (hsl (1 + s) (by linarith))
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hs'.le) hs'.le
  linarith

/-- **RH from even positivity with controlled negative part.** -/
theorem riemannHypothesis_of_weilPositiveEvenAt_of_negPart {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam)
    (hneg : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => max (-lam n) 0 / (n : ℝ) ^ σ)
    (hdp : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ),
      s * (s * oddDirichlet (fun n => max (-lam n) 0) s) ≤ ε) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  weilPositiveEvenAt_one_iff.mp (weilPositiveEvenAt_one_of_negPart h hneg hdp)

/-! ## Section 3: Linear dyadic negative part and bounded-below even rigidity -/

/-- A nonnegative arithmetic function with linear dyadic blocks `Σ_{N < n ≤ 2N} f(n) ≤ B N` has
`oddDirichlet f s ≤ B / (1 − 2^{−s})` for all `s > 0`. -/
theorem oddDirichlet_le_of_sum_Ioc_le {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) {B : ℝ} (hB0 : 0 ≤ B)
    (hb : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Ioc N (2 * N), f n ≤ B * N) {s : ℝ} (hs : 0 < s) :
    oddDirichlet f s ≤ B / (1 - (2 : ℝ) ^ (-s)) := by
  set r : ℝ := (2 : ℝ) ^ (-s) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set g : ℕ → ℝ := fun n => (if 2 ≤ n then f n else 0) / (n : ℝ) ^ (1 + s) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    split_ifs <;> [exact hf0 n; exact le_rfl]
  set b : ℕ → ℝ := fun j => ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), g n with hbdef
  have hbj : ∀ j : ℕ, b j ≤ B * r ^ j := fun j => by
    have hN0 : (0 : ℝ) < 2 ^ j := by positivity
    calc b j ≤ ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n / ((2 : ℝ) ^ j) ^ (1 + s) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Finset.mem_Ioc] at hn
          have hn2 : 2 ≤ n := by
            have := @Nat.one_le_two_pow j; omega
          simp only [hg, if_pos hn2]
          refine div_le_div_of_nonneg_left (hf0 n) (Real.rpow_pos_of_pos hN0 _)
            (Real.rpow_le_rpow hN0.le ?_ (by linarith))
          exact_mod_cast hn.1.le
      _ = (∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n) / ((2 : ℝ) ^ j) ^ (1 + s) := by
          rw [Finset.sum_div]
      _ ≤ B * ((2 ^ j : ℕ) : ℝ) / ((2 : ℝ) ^ j) ^ (1 + s) := by
          rw [show 2 ^ (j + 1) = 2 * 2 ^ j by ring]
          exact div_le_div_of_nonneg_right (hb (2 ^ j) Nat.one_le_two_pow)
            (Real.rpow_nonneg hN0.le _)
      _ = B * r ^ j := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
          have hrj : (2 : ℝ) ^ j / ((2 : ℝ) ^ j) ^ (1 + s) = r ^ j := by
            rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num), ← Real.rpow_sub (by norm_num)]
            congr 1; ring
          rw [mul_div_assoc, hrj]
  have hgeo : Summable fun j : ℕ => B * r ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left B
  have htsum_geo : (∑' j : ℕ, B * r ^ j) = B / (1 - r) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  have hdyad : ∀ J : ℕ, ∑ n ∈ Finset.Ioc 1 (2 ^ J), g n ≤ ∑ j ∈ Finset.range J, b j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← Finset.sum_Ioc_consecutive g Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)), Finset.sum_range_succ]
      exact add_le_add ih le_rfl
  have hrange : ∀ T : ℕ, ∑ n ∈ Finset.range T, g n ≤ B / (1 - r) := fun T => by
    have hT : T ≤ 2 ^ T := Nat.lt_two_pow_self.le
    have hg00 : g 0 = 0 := by simp [hg]
    have hg01 : g 1 = 0 := by simp [hg]
    calc ∑ n ∈ Finset.range T, g n ≤ ∑ n ∈ Finset.range (2 ^ T + 1), g n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun n _ _ => hg0 n)
      _ = g 0 + g 1 + ∑ n ∈ Finset.Ioc 1 (2 ^ T), g n :=
          sum_range_succ_eq_Ioc g (2 ^ T) Nat.one_le_two_pow
      _ ≤ ∑ j ∈ Finset.range T, B * r ^ j := by
          rw [hg00, hg01, zero_add, zero_add]
          exact (hdyad T).trans (Finset.sum_le_sum fun j _ => hbj j)
      _ ≤ B / (1 - r) := by
          rw [← htsum_geo]
          exact hgeo.sum_le_tsum _ fun j _ => mul_nonneg hB0 (pow_nonneg hr0 j)
  have hgs : Summable g := summable_of_sum_range_le hg0 hrange
  exact Real.tsum_le_of_sum_range_le hg0 hrange

/-- Linear dyadic blocks give `s² oddDirichlet f s → 0` as `s → 0⁺`. -/
theorem eventually_mul_mul_oddDirichlet_le_of_sum_Ioc_le {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    {B : ℝ} (hB0 : 0 ≤ B) (hb : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Ioc N (2 * N), f n ≤ B * N) :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), s * (s * oddDirichlet f s) ≤ ε := by
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set δ := min 1 (ε * Real.log 2 / (2 * B + 1)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδpos)] with s hs0 hsδ
  have hs : 0 < s := hs0
  have hs1 : s ≤ 1 := (hsδ.trans_le (min_le_left _ _)).le
  have hsε : s < ε * Real.log 2 / (2 * B + 1) := hsδ.trans_le (min_le_right _ _)
  have hdir := oddDirichlet_le_of_sum_Ioc_le hf0 hB0 hb hs
  have hrpow : (2 : ℝ) ^ (-s) = Real.exp (-(s * Real.log 2)) := by
    rw [Real.rpow_def_of_pos two_pos]; ring_nf
  have hexp_ge : 1 / 2 ≤ Real.exp (-(s * Real.log 2)) := by
    have h1 : Real.exp (-Real.log 2) ≤ Real.exp (-(s * Real.log 2)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [Real.exp_neg, Real.exp_log two_pos] at h1
    linarith
  have hexp_mul : Real.exp (s * Real.log 2) * Real.exp (-(s * Real.log 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h1sub : s * Real.log 2 / 2 ≤ 1 - (2 : ℝ) ^ (-s) := by
    rw [hrpow]
    have h1 := Real.add_one_le_exp (s * Real.log 2)
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(s * Real.log 2))).le
    rw [hexp_mul] at h2
    have h3 : s * Real.log 2 * (1 / 2) ≤ s * Real.log 2 * Real.exp (-(s * Real.log 2)) :=
      mul_le_mul_of_nonneg_left hexp_ge (by positivity)
    linarith
  have hpos_sub : 0 < 1 - (2 : ℝ) ^ (-s) := by
    have : 0 < s * Real.log 2 / 2 := by positivity
    linarith
  have hs_dir : s * oddDirichlet f s ≤ 2 * B / Real.log 2 := by
    have h1 : s * oddDirichlet f s ≤ s * (B / (1 - (2 : ℝ) ^ (-s))) :=
      mul_le_mul_of_nonneg_left hdir hs.le
    rw [le_div_iff₀ hlog2]
    have h2 : s * (B / (1 - (2 : ℝ) ^ (-s))) * Real.log 2 =
        2 * B * ((s * Real.log 2 / 2) / (1 - (2 : ℝ) ^ (-s))) := by ring
    have h3 : (s * Real.log 2 / 2) / (1 - (2 : ℝ) ^ (-s)) ≤ 1 :=
      (div_le_one hpos_sub).mpr h1sub
    nlinarith
  have hss_dir : s * (s * oddDirichlet f s) ≤ s * (2 * B / Real.log 2) :=
    mul_le_mul_of_nonneg_left hs_dir hs.le
  have hfin : s * (2 * B / Real.log 2) ≤ ε := by
    rw [lt_div_iff₀ (by positivity)] at hsε
    rw [mul_div_assoc', div_le_iff₀ hlog2]
    nlinarith
  exact hss_dir.trans hfin

/-- **Even rigidity under linear dyadic negative part.**  If `lam` is Weil-positive on even tests at
some pole weight `β` and `Σ_{N < n ≤ 2N} max (-lam n) 0 ≤ B N`, then RH holds and `lam = Λ` on
`n ≥ 2`. -/
theorem riemannHypothesis_of_weilPositiveEvenAt_of_sum_negPart_Ioc_le {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {B : ℝ} (hB0 : 0 ≤ B)
    (hb : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Ioc N (2 * N), max (-lam n) 0 ≤ B * N) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine riemannHypothesis_of_weilPositiveEvenAt_of_negPart h (fun σ hσ => ?_)
    (eventually_mul_mul_oddDirichlet_le_of_sum_Ioc_le (fun n => le_max_right _ _) hB0 hb)
  refine summable_div_rpow_of_block (fun n => le_max_right _ _) (B := B) (j₀ := 0) hσ fun j _ => ?_
  rw [show 2 ^ (j + 1) = 2 * 2 ^ j by ring]
  have h1 := hb (2 ^ j) Nat.one_le_two_pow
  rw [Nat.cast_pow, Nat.cast_ofNat] at h1
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have : (0 : ℝ) ≤ B * (2 : ℝ) ^ j := by positivity
  nlinarith

/-- **Even rigidity for weights bounded below.**  If `lam` is Weil-positive on even tests at some
pole weight `β` and `lam(n) ≥ −C` for all `n ≥ 2`, then RH holds and `lam = Λ` on `n ≥ 2`. -/
theorem riemannHypothesis_of_weilPositiveEvenAt_of_bddBelow {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {C : ℝ} (hC : ∀ n, 2 ≤ n → -C ≤ lam n) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine riemannHypothesis_of_weilPositiveEvenAt_of_sum_negPart_Ioc_le h (B := max C 0)
    (le_max_right C 0) fun N hN => ?_
  calc ∑ n ∈ Finset.Ioc N (2 * N), max (-lam n) 0
      ≤ ∑ _n ∈ Finset.Ioc N (2 * N), max C 0 := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
        exact max_le (le_trans (neg_le.mp (hC n hn2)) (le_max_left C 0)) (le_max_right C 0)
    _ = max C 0 * N := by
        rw [Finset.sum_const, Nat.card_Ioc, show 2 * N - N = N by omega, nsmul_eq_mul, mul_comm]

/-! ## Section 4: The arbitrary-pole-weight one-sided even cone and the subblind even window -/

/-- Weil positivity of `L` at pole weight `β` on the nonnegative combinations of even tests whose
`ℓ`-values are nonnegative at every `n ≥ 2`. -/
def PositiveOnEvenNonnegConeAt (β : ℝ) (L : ℕ → ℝ) : Prop :=
  ∀ c : EvenWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1.1 n) →
    0 ≤ c.sum fun f t =>
      t * (WeilPoleWeight.weilPoleWeightFunctional β L (EF.weilTest f.1.1 f.1.1)).re

/-- **Prime-subblind positivity at pole weight `β` on even tests:** whenever a nonnegative
combination of autocorrelations of even tests is `≥ 0` at every `±log n`, `n ≥ 2`, its
`β`-archimedean functional is `≥ 0`. -/
def PrimeSubblindPositiveEvenAt (β : ℝ) : Prop :=
  ∀ c : EvenWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1.1 n) →
    0 ≤ c.sum fun f t => t * poleWeightArchRe β f.1

theorem linearCombination_logVector_evenWeil_apply (c : EvenWeilTestFn →₀ ℝ) (j : LogIndex) :
    linearCombination ℝ (fun f : EvenWeilTestFn => logVector f.1) c j =
      c.sum fun f t => t * logValue f.1.1 j := by
  rw [linearCombination_apply, Finsupp.sum_apply]
  simp [logVector_apply]

theorem sum_re_weilPoleWeightFunctional_even (β : ℝ) (U : ℕ → ℝ) (c : EvenWeilTestFn →₀ ℝ) :
    (c.sum fun f t =>
        t * (WeilPoleWeight.weilPoleWeightFunctional β U (EF.weilTest f.1.1 f.1.1)).re) =
      linearCombination ℝ (fun f : EvenWeilTestFn => poleWeightArchRe β f.1) c -
        linearCombination ℝ (fun j : LogIndex => U j)
          (linearCombination ℝ (fun f : EvenWeilTestFn => logVector f.1) c) := by
  simp_rw [fun f : EvenWeilTestFn => re_weilPoleWeightFunctional_eq β U f.1]
  have e1 : linearCombination ℝ (fun f : EvenWeilTestFn => poleWeightArchRe β f.1) c =
      c.sum fun f t => t * poleWeightArchRe β f.1 := by
    rw [linearCombination_apply]; simp only [smul_eq_mul]
  have e2 : linearCombination ℝ (fun j : LogIndex => U j)
      (linearCombination ℝ (fun f : EvenWeilTestFn => logVector f.1) c) =
      c.sum fun f t => t * linearCombination ℝ (fun j : LogIndex => U j) (logVector f.1) := by
    rw [linearCombination_apply ℝ (v := fun f : EvenWeilTestFn => logVector f.1), map_finsuppSum]
    exact Finsupp.sum_congr fun f _ => by rw [map_smul, smul_eq_mul]
  rw [e1, e2, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun f _ => by ring

/-- **M. Riesz equivalence on the even sector at pole weight `β`.**  `PositiveOnEvenNonnegConeAt β L`
holds iff `L` has a majorant on `n ≥ 2` that is Weil-positive on even tests at pole weight `β`. -/
theorem exists_weilPositiveEvenAt_ge_iff (β : ℝ) (L : ℕ → ℝ) :
    (∃ lam : ℕ → ℝ, WeilPositiveEvenAt β lam ∧ ∀ n, 2 ≤ n → L n ≤ lam n) ↔
      PositiveOnEvenNonnegConeAt β L := by
  constructor
  · rintro ⟨lam, hW, hle⟩ c hc hcT
    have h1 : 0 ≤ c.sum fun f t =>
        t * (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f.1.1 f.1.1)).re :=
      Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (hW f.1.1 f.1.2.1 f.1.2.2 f.2)
    rw [sum_re_weilPoleWeightFunctional_even] at h1 ⊢
    set v := linearCombination ℝ (fun f : EvenWeilTestFn => logVector f.1) c
    have hv : ∀ j : LogIndex, 0 ≤ v j := fun j => by
      rw [linearCombination_logVector_evenWeil_apply]; exact hcT j j.2
    have hmono : linearCombination ℝ (fun j : LogIndex => L j) v ≤
        linearCombination ℝ (fun j : LogIndex => lam j) v := by
      rw [linearCombination_apply, linearCombination_apply]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hle j j.2) (hv j)
    linarith
  · intro h
    have hsqrt : ∀ j : LogIndex, 0 < Real.sqrt (j : ℕ) := fun j =>
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le two_pos j.2))
    obtain ⟨lam, hlamL, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_ge_of_nonneg_on_nonneg_cone
      (fun f : EvenWeilTestFn => logVector f.1)
      (fun f : EvenWeilTestFn => poleWeightArchRe β f.1) (fun j : LogIndex => L j)
      (fun j => ⟨evenPlus j, _, div_pos (mul_pos two_pos (integral_evenProfile_sq_pos j))
        (hsqrt j), logVector_evenPlus j⟩)
      (fun c hc hcT => by
        have h1 := h c hc fun n hn => by
          rw [← linearCombination_logVector_evenWeil_apply c ⟨n, hn⟩]; exact hcT ⟨n, hn⟩
        rw [sum_re_weilPoleWeightFunctional_even] at h1
        linarith)
    refine ⟨fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0,
      fun f hf hfc heven => ?_, fun n hn => ?_⟩
    · rw [re_weilPoleWeightFunctional_eq β _ ⟨f, hf, hfc⟩]
      have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
          lam := funext fun j => by simp [j.2]
      rw [e]
      linarith [hlamT ⟨⟨f, hf, hfc⟩, heven⟩]
    · simp only [dif_pos hn]; exact hlamL ⟨n, hn⟩

/-- **Arbitrary-pole-weight one-sided even positivity forces RH and bounds `L ≤ Λ`** whenever the
negative part of `L` has linear dyadic blocks. -/
theorem riemannHypothesis_and_le_vonMangoldt_of_positiveOnEvenNonnegConeAt_of_sum_negPart_Ioc_le
    {β : ℝ} {L : ℕ → ℝ} (h : PositiveOnEvenNonnegConeAt β L) {B : ℝ} (hB0 : 0 ≤ B)
    (hb : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Ioc N (2 * N), max (-L n) 0 ≤ B * N) :
    RiemannHypothesis ∧ 1 ≤ β ∧ ∀ n, 2 ≤ n → L n ≤ ArithmeticFunction.vonMangoldt n := by
  obtain ⟨lam, hW, hge⟩ := (exists_weilPositiveEvenAt_ge_iff β L).mpr h
  have hblam : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Ioc N (2 * N), max (-lam n) 0 ≤ B * N := by
    intro N hN
    refine (Finset.sum_le_sum fun n hn => ?_).trans (hb N hN)
    have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
    exact max_le (le_trans (neg_le_neg (hge n hn2)) (le_max_left _ _)) (le_max_right _ _)
  obtain ⟨hRH, heq⟩ := riemannHypothesis_of_weilPositiveEvenAt_of_sum_negPart_Ioc_le hW hB0 hblam
  have hWΛ : WeilPositiveEvenAt β fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
    intro f hf hfc hev
    have h1 := hW f hf hfc hev
    rw [re_weilPoleWeightFunctional_eq β _ ⟨f, hf, hfc⟩] at h1 ⊢
    have e : (fun j : LogIndex => lam j) =
        fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ) :=
      funext fun j => heq j j.2
    rwa [← e]
  exact ⟨hRH, one_le_of_weilPositiveEvenAt_vonMangoldt hWΛ,
    fun n hn => (hge n hn).trans (heq n hn).le⟩

/-- **Arbitrary-pole-weight one-sided even positivity for weights bounded below.** -/
theorem riemannHypothesis_and_le_vonMangoldt_of_positiveOnEvenNonnegConeAt_of_bddBelow {β : ℝ}
    {L : ℕ → ℝ} (h : PositiveOnEvenNonnegConeAt β L) {C : ℝ} (hC : ∀ n, 2 ≤ n → -C ≤ L n) :
    RiemannHypothesis ∧ 1 ≤ β ∧ ∀ n, 2 ≤ n → L n ≤ ArithmeticFunction.vonMangoldt n := by
  refine riemannHypothesis_and_le_vonMangoldt_of_positiveOnEvenNonnegConeAt_of_sum_negPart_Ioc_le h
    (B := max C 0) (le_max_right C 0) fun N hN => ?_
  calc ∑ n ∈ Finset.Ioc N (2 * N), max (-L n) 0
      ≤ ∑ _n ∈ Finset.Ioc N (2 * N), max C 0 := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
        exact max_le (le_trans (neg_le.mp (hC n hn2)) (le_max_left C 0)) (le_max_right C 0)
    _ = max C 0 * N := by
        rw [Finset.sum_const, Nat.card_Ioc, show 2 * N - N = N by omega, nsmul_eq_mul, mul_comm]

/-- **The one-sided even window of `Λ`.**  `PositiveOnEvenNonnegConeAt β Λ` holds iff RH and
`1 ≤ β`. -/
theorem positiveOnEvenNonnegConeAt_vonMangoldt_iff (β : ℝ) :
    PositiveOnEvenNonnegConeAt β (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ↔
      RiemannHypothesis ∧ 1 ≤ β := by
  constructor
  · intro h
    obtain ⟨hRH, hβ, -⟩ :=
      riemannHypothesis_and_le_vonMangoldt_of_positiveOnEvenNonnegConeAt_of_bddBelow h (C := 0)
        fun n _ => by simp [ArithmeticFunction.vonMangoldt_nonneg]
    exact ⟨hRH, hβ⟩
  · rintro ⟨hRH, hβ⟩
    refine (exists_weilPositiveEvenAt_ge_iff β _).mp ⟨fun n => ArithmeticFunction.vonMangoldt n,
      weilPositiveEvenAt_mono hβ (weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩),
      fun _ _ => le_rfl⟩

/-- **RH is one-sided even positivity of `Λ` at some pole weight.** -/
theorem riemannHypothesis_iff_exists_positiveOnEvenNonnegConeAt_vonMangoldt :
    RiemannHypothesis ↔
      ∃ β : ℝ, PositiveOnEvenNonnegConeAt β fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  ⟨fun hRH => ⟨1, (positiveOnEvenNonnegConeAt_vonMangoldt_iff 1).mpr ⟨hRH, le_rfl⟩⟩,
    fun ⟨β, h⟩ => ((positiveOnEvenNonnegConeAt_vonMangoldt_iff β).mp h).1⟩

theorem positiveOnEvenNonnegConeAt_zero_iff (β : ℝ) :
    PositiveOnEvenNonnegConeAt β (fun _ => 0) ↔ PrimeSubblindPositiveEvenAt β := by
  unfold PositiveOnEvenNonnegConeAt PrimeSubblindPositiveEvenAt
  have e : ∀ c : EvenWeilTestFn →₀ ℝ,
      (c.sum fun f t =>
        t * (WeilPoleWeight.weilPoleWeightFunctional β (fun _ => 0) (EF.weilTest f.1.1 f.1.1)).re) =
        c.sum fun f t => t * poleWeightArchRe β f.1 := fun c => by
    rw [sum_re_weilPoleWeightFunctional_even]
    have h0 : (fun _ : LogIndex => (0 : ℝ)) = 0 := rfl
    rw [h0, linearCombination_zero, LinearMap.zero_apply, sub_zero, linearCombination_apply]
    simp only [smul_eq_mul]
  simp only [e]

/-- **Subblind even Farkas.**  A nonnegative weight system is Weil-positive on even tests at pole
weight `β` iff `PrimeSubblindPositiveEvenAt β` holds. -/
theorem exists_nonneg_weilPositiveEvenAt_iff (β : ℝ) :
    (∃ lam : ℕ → ℝ, (∀ n, 2 ≤ n → 0 ≤ lam n) ∧ WeilPositiveEvenAt β lam) ↔
      PrimeSubblindPositiveEvenAt β := by
  rw [← positiveOnEvenNonnegConeAt_zero_iff, ← exists_weilPositiveEvenAt_ge_iff]
  exact ⟨fun ⟨lam, hnn, hW⟩ => ⟨lam, hW, hnn⟩, fun ⟨lam, hW, hnn⟩ => ⟨lam, hnn, hW⟩⟩

/-- **The subblind even window is `[1, ∞)` under RH and empty otherwise.** -/
theorem primeSubblindPositiveEvenAt_iff (β : ℝ) :
    PrimeSubblindPositiveEvenAt β ↔ RiemannHypothesis ∧ 1 ≤ β := by
  rw [← positiveOnEvenNonnegConeAt_zero_iff]
  constructor
  · intro h
    obtain ⟨hRH, hβ, -⟩ :=
      riemannHypothesis_and_le_vonMangoldt_of_positiveOnEvenNonnegConeAt_of_bddBelow h (C := 0)
        fun _ _ => by norm_num
    exact ⟨hRH, hβ⟩
  · rintro ⟨hRH, hβ⟩
    exact (exists_weilPositiveEvenAt_ge_iff β _).mp
      ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
        weilPositiveEvenAt_mono hβ (weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩),
        fun _ _ => ArithmeticFunction.vonMangoldt_nonneg⟩

/-- **Unconditional subblind even-window characterization of RH.**  RH holds iff
`PrimeSubblindPositiveEvenAt β` holds at some pole weight `β`. -/
theorem riemannHypothesis_iff_exists_primeSubblindPositiveEvenAt :
    RiemannHypothesis ↔ ∃ β : ℝ, PrimeSubblindPositiveEvenAt β :=
  ⟨fun hRH => ⟨1, (primeSubblindPositiveEvenAt_iff 1).mpr ⟨hRH, le_rfl⟩⟩,
    fun ⟨β, h⟩ => ((primeSubblindPositiveEvenAt_iff β).mp h).1⟩

end RHTower.EvenSector

end
