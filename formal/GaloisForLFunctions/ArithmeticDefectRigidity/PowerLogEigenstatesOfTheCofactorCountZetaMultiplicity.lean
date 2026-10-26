import GaloisForLFunctions.ArithmeticDefectRigidity.LogPowerRowsReadTheDerivativesOfZeta
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.XiDeck

/-!
# Power-log eigenstates of the renormalized cofactor count the multiplicity of ζ

For `1/2 ≤ Re s < 1 − ε` let `u_c(n) = Σ_{k≤K} c_k log^k n · n^s`. Its real and imaginary parts
lie in the pole-trace domain, and both satisfy the renormalized inversion law — `v + D̃v` has
bounded pronic energy, the eigenrelation `D̃v ≈ −v` — if and only if `c_k = 0` for every
`k ≥ ord_{s+ε} ζ` (`powerLogRows_renormalizedInversion_iff_order`). The power-log eigenspace of
`D̃` at exponent `s` has complex dimension exactly the multiplicity of the zero of `ζ` at `s + ε`.

Mechanism: on the power-log block `D̃ + I` is the triangular Leibniz matrix
`(T c)_d = Σ_{k≥d} C(k, k−d) ζ^{(k−d)}(s+ε) c_k` modulo admitted rows
(`norm_logPowerCofactorSum_sub_le`); a block row `Σ_d b_d log^d n · n^s` with `Re s ≥ 1/2` is
admitted only when `b = 0`; and `T c = 0` exactly when `c` vanishes from the order on.
-/

open Finset Filter Topology Complex
open GaloisForLFunctions.BezoutValuationIncidence (pronicNorm pronicNorm_nonneg pronicNorm_sq)
open GaloisForLFunctions.TransHorizonIncidenceMechanics (mellinCell)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The complex power-log row `u_c(n) = Σ_{k≤K} c_k log^k n · n^s`. -/
def powerLogRow (s : ℂ) (K : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ range (K + 1), c k * ((Real.log n : ℂ) ^ k * (((n : ℝ)) : ℂ) ^ s)

/-- Its real part, an ADR row. The imaginary part is the real part of `u_{−ic}`. -/
def powerLogReRow (s : ℂ) (K : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℝ := (powerLogRow s K c n).re

theorem powerLogRow_zero {s : ℂ} (hs : s ≠ 0) (K : ℕ) (c : ℕ → ℂ) : powerLogRow s K c 0 = 0 := by
  simp [powerLogRow, Complex.zero_cpow hs]

theorem powerLogReRow_neg_I_mul (s : ℂ) (K : ℕ) (c : ℕ → ℂ) (n : ℕ) :
    powerLogReRow s K (fun k => -I * c k) n = (powerLogRow s K c n).im := by
  simp only [powerLogReRow, powerLogRow, mul_assoc, ← mul_sum, neg_mul, Complex.neg_re,
    Complex.I_mul_re, neg_neg]

/-! ### The trace domain and the pole trace -/

/-- The Mellin trace series of a power-log row. -/
theorem hasSum_powerLogRow_mul_mellinCell {ε : ℝ} (hε1 : ε < 1) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 - ε) (K : ℕ) (c : ℕ → ℂ) :
    HasSum (fun n => powerLogRow s K c n * ((mellinCell (1 - ε) n : ℝ) : ℂ))
      (∑ k ∈ range (K + 1), c k * ∑' m, poleTerm (1 - ε) k m s) := by
  have hα : 0 < 1 - ε := by linarith
  set δ := min s.re (1 - ε - s.re) / 2 with hδdef
  have hδ : 0 < δ := by have : 0 < 1 - ε - s.re := by linarith
                        positivity
  have hsδ : s ∈ innerStrip (1 - ε) δ := by
    constructor
    · have : δ ≤ s.re / 2 := by
        rw [hδdef]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith
    · have : δ ≤ (1 - ε - s.re) / 2 := by
        rw [hδdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith
  have hsum : ∀ k, Summable fun m => poleTerm (1 - ε) k m s := fun k =>
    Summable.of_norm_bounded (summable_poleTerm_bound (1 - ε) δ hδ k)
      fun m => norm_poleTerm_le hα hδ k m hsδ
  have h := hasSum_sum (s := range (K + 1)) fun k _ => ((hsum k).mul_left (c k)).hasSum
  refine (h.congr_fun fun n => ?_)
  rw [powerLogRow, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  simp only [poleTerm]; ring

theorem powerLogReRow_mem_poleTraceDomain (ε : SubcriticalDamping) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 - ε) (K : ℕ) (c : ℕ → ℂ) : powerLogReRow s K c ∈ poleTraceDomain ε := by
  have hs : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  refine ⟨by simp [powerLogReRow, powerLogRow_zero hs], ?_⟩
  have h := Complex.hasSum_re (hasSum_powerLogRow_mul_mellinCell (by linarith [ε.property.2])
    hs0 hs1 K c)
  refine h.summable.congr fun n => ?_
  simp only [powerLogReRow, Complex.re_mul_ofReal]

/-- The real power-log row as a trace-domain vector. -/
def powerLogTraceVector (ε : SubcriticalDamping) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 - ε)
    (K : ℕ) (c : ℕ → ℂ) : poleTraceDomain ε :=
  ⟨powerLogReRow s K c, powerLogReRow_mem_poleTraceDomain ε hs0 hs1 K c⟩

theorem poleTrace_powerLogTraceVector (ε : SubcriticalDamping) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 - ε) (K : ℕ) (c : ℕ → ℂ) :
    poleTrace ε (powerLogTraceVector ε hs0 hs1 K c) =
      (∑ k ∈ range (K + 1), c k * logPowerPoleTrace ε s k).re := by
  have h := Complex.hasSum_re (hasSum_powerLogRow_mul_mellinCell (by linarith [ε.property.2])
    hs0 hs1 K c)
  change (∑' n, powerLogReRow s K c n * mellinCell (1 - (ε : ℝ)) n) / (1 - (ε : ℝ)) = _
  have hcongr : (fun n => powerLogReRow s K c n * mellinCell (1 - (ε : ℝ)) n) =
      fun n => (powerLogRow s K c n * ((mellinCell (1 - (ε : ℝ)) n : ℝ) : ℂ)).re := by
    funext n; simp only [powerLogReRow, Complex.re_mul_ofReal]
  rw [hcongr, h.tsum_eq, ← Complex.div_ofReal_re]
  congr 1
  rw [sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [logPowerPoleTrace, mul_div_assoc]

/-! ### The cofactor on power-log rows -/

theorem powerLogReRow_add_renormalizedCofactorOperator (ε : SubcriticalDamping) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 - ε) (K : ℕ) (c : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    powerLogReRow s K c n + renormalizedCofactorOperator ε (powerLogTraceVector ε hs0 hs1 K c) n =
      (∑ k ∈ range (K + 1), c k * (logPowerCofactorSum ε s k n -
        logPowerPoleTrace ε s k * (((n : ℝ)) : ℂ) ^ ((1 - (ε : ℝ) : ℝ) : ℂ))).re := by
  change powerLogReRow s K c n + ((∑ j ∈ Icc 2 n, (j : ℝ) ^ (-(ε : ℝ)) * powerLogReRow s K c (n / j)) -
    poleTrace ε (powerLogTraceVector ε hs0 hs1 K c) * (n : ℝ) ^ (1 - (ε : ℝ))) = _
  rw [poleTrace_powerLogTraceVector]
  have hpow : (((n : ℝ)) : ℂ) ^ ((1 - (ε : ℝ) : ℝ) : ℂ) = (((n : ℝ) ^ (1 - (ε : ℝ)) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow (Nat.cast_nonneg n) _).symm
  have hterm : ∀ j : ℕ, (j : ℝ) ^ (-(ε : ℝ)) * powerLogReRow s K c (n / j) =
      ((((j : ℝ)) : ℂ) ^ (-((ε : ℝ) : ℂ)) * powerLogRow s K c (n / j)).re := by
    intro j
    rw [show (-((ε : ℝ) : ℂ)) = (((-(ε : ℝ)) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (Nat.cast_nonneg j), Complex.re_ofReal_mul, powerLogReRow]
  have hsplit : ∑ j ∈ Icc 1 n, (((j : ℝ)) : ℂ) ^ (-((ε : ℝ) : ℂ)) * powerLogRow s K c (n / j) =
      ∑ k ∈ range (K + 1), c k * logPowerCofactorSum ε s k n := by
    simp only [powerLogRow, logPowerCofactorSum, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => by ring
  have hIcc : (Icc 1 n : Finset ℕ) = insert 1 (Icc 2 n) := by
    ext j; simp only [mem_insert, mem_Icc]; omega
  have h1 : (1 : ℕ) ∉ Icc 2 n := by simp
  rw [hpow]
  simp only [mul_sub, sum_sub_distrib, Complex.sub_re, ← hsplit, hIcc, sum_insert h1,
    Complex.add_re, hterm]
  simp only [Nat.cast_one, Complex.ofReal_one, Complex.one_cpow, one_mul, Nat.div_one,
    powerLogReRow, ← Complex.re_sum]
  rw [← sum_mul, Complex.re_mul_ofReal]
  ring

/-- **The power-log symbol law in pronic energy.** Modulo a row of bounded energy,
`(I + D̃) Re u_c = Re Σ_k c_k (Leibniz row)_k`. -/
theorem exists_pronicNorm_powerLogRow_symbol_le (ε : SubcriticalDamping) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 - ε) (K : ℕ) (c : ℕ → ℂ) :
    ∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n => powerLogReRow s K c n +
      renormalizedCofactorOperator ε (powerLogTraceVector ε hs0 hs1 K c) n -
        (∑ k ∈ range (K + 1), c k * zetaLeibnizRow ε s k n).re) ≤ B := by
  obtain ⟨θ, hθ, hC⟩ := norm_logPowerCofactorSum_sub_le ε.property.1
    (by linarith [ε.property.2]) ⟨hs0, hs1⟩
  choose C hCk using hC
  set Ctot := ∑ k ∈ range (K + 1), ‖c k‖ * C k with hCtot
  have hθ' : 0 < 1 - θ := by linarith
  refine ⟨Real.sqrt (Ctot ^ 2 * (1 + 1 / (1 - θ))), fun T => ?_⟩
  refine Real.sqrt_le_sqrt (TransHorizonIncidenceMechanics.sum_sq_le_of_abs_le_sqrt_rpow hθ'
    (fun n hn => ?_) T)
  rw [powerLogReRow_add_renormalizedCofactorOperator ε hs0 hs1 K c hn, ← Complex.sub_re,
    ← sum_sub_distrib, show 1 - (1 - θ) = θ by ring]
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  rw [hCtot, sum_mul]
  refine sum_le_sum fun k _ => ?_
  rw [← mul_sub, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hCk k n hn) (norm_nonneg _)

/-! ### The Leibniz matrix -/

/-- The Leibniz coefficients `b_d = Σ_{d≤k≤K} C(k, k−d) ζ^{(k−d)}(s+ε) c_k`. -/
def leibnizCoeff (ε : ℝ) (s : ℂ) (K : ℕ) (c : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ k ∈ Icc d K, c k * ((k.choose (k - d) : ℂ) * iteratedDeriv (k - d) riemannZeta (s + ε))

/-- The Leibniz combination is a single power-log block with the Leibniz coefficients. -/
theorem sum_mul_zetaLeibnizRow (ε : ℝ) (s : ℂ) (K : ℕ) (c : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ range (K + 1), c k * zetaLeibnizRow ε s k n =
      powerLogRow s K (leibnizCoeff ε s K c) n := by
  simp only [zetaLeibnizRow, powerLogRow, leibnizCoeff, mul_sum, sum_mul]
  have hreflect : ∀ k, ∑ i ∈ range (k + 1), c k * ((k.choose i : ℂ) * iteratedDeriv i riemannZeta
      (s + ε) * ((Real.log n : ℂ) ^ (k - i) * (((n : ℝ)) : ℂ) ^ s)) =
      ∑ d ∈ range (k + 1), c k * ((k.choose (k - d) : ℂ) * iteratedDeriv (k - d) riemannZeta
        (s + ε)) * ((Real.log n : ℂ) ^ d * (((n : ℝ)) : ℂ) ^ s) := by
    intro k
    rw [← sum_range_reflect]
    refine sum_congr rfl fun d hd => ?_
    have hdk : d ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hd)
    rw [show k + 1 - 1 - d = k - d by omega, show k - (k - d) = d by omega]
    ring
  simp only [hreflect]
  rw [sum_comm' (t' := range (K + 1)) (s' := fun d => Icc d K)]
  intro k d
  simp only [mem_range, mem_Icc]
  omega

/-- **Triangular inversion.** If `ζ` vanishes to order exactly `m` at `s + ε`, the Leibniz
coefficients vanish iff `c_k = 0` for all `m ≤ k ≤ K`. -/
theorem leibnizCoeff_eq_zero_iff {ε : ℝ} {s : ℂ} {m : ℕ}
    (hm0 : ∀ i < m, iteratedDeriv i riemannZeta (s + ε) = 0)
    (hm1 : iteratedDeriv m riemannZeta (s + ε) ≠ 0) (K : ℕ) (c : ℕ → ℂ) :
    (∀ d ≤ K, leibnizCoeff ε s K c d = 0) ↔ ∀ k ≤ K, m ≤ k → c k = 0 := by
  constructor
  · intro hb
    -- downward induction from `K`
    have key : ∀ t, ∀ k, K - t ≤ k → k ≤ K → m ≤ k → c k = 0 := by
      intro t
      induction t with
      | zero =>
        intro k hk hkK hmk
        have hkeq : k = K := by omega
        subst hkeq
        have h := hb (k - m) (by omega)
        rw [leibnizCoeff] at h
        have hsplit : ∑ k' ∈ Icc (k - m) k, c k' * ((k'.choose (k' - (k - m)) : ℂ) *
            iteratedDeriv (k' - (k - m)) riemannZeta (s + ε)) = c k * ((k.choose m : ℂ) *
              iteratedDeriv m riemannZeta (s + ε)) := by
          rw [sum_eq_single k]
          · rw [show k - (k - m) = m by omega]
          · intro k' hk' hne
            simp only [mem_Icc] at hk'
            omega
          · intro h; exact absurd (mem_Icc.mpr ⟨by omega, le_rfl⟩) h
        rw [hsplit] at h
        have hch : (k.choose m : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmk).ne'
        exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero hch hm1)
      | succ t ih =>
        intro k hk hkK hmk
        by_cases hkt : K - t ≤ k
        · exact ih k hkt hkK hmk
        have hkeq : k = K - (t + 1) := by omega
        have h := hb (k - m) (by omega)
        rw [leibnizCoeff] at h
        have hsplit : ∑ k' ∈ Icc (k - m) K, c k' * ((k'.choose (k' - (k - m)) : ℂ) *
            iteratedDeriv (k' - (k - m)) riemannZeta (s + ε)) = c k * ((k.choose m : ℂ) *
              iteratedDeriv m riemannZeta (s + ε)) := by
          rw [sum_eq_single k]
          · rw [show k - (k - m) = m by omega]
          · intro k' hk' hne
            simp only [mem_Icc] at hk'
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · rw [hm0 (k' - (k - m)) (by omega), mul_zero, mul_zero]
            · rw [ih k' (by omega) hk'.2 (by omega), zero_mul]
          · intro h; exact absurd (mem_Icc.mpr ⟨by omega, hkK⟩) h
        rw [hsplit] at h
        have hch : (k.choose m : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmk).ne'
        exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero hch hm1)
    intro k hkK hmk
    exact key K k (by omega) hkK hmk
  · intro hc d hd
    rw [leibnizCoeff]
    refine sum_eq_zero fun k hk => ?_
    simp only [mem_Icc] at hk
    by_cases hmk : m ≤ k - d
    · by_cases hmk' : m ≤ k
      · rw [hc k hk.2 hmk', zero_mul]
      · omega
    · rw [hm0 (k - d) (by omega), mul_zero, mul_zero]

/-! ### Admitted power-log blocks vanish -/

/-- **A critical power-log block carries unbounded energy.** If `Re s ≥ 1/2` and both the real
and imaginary parts of `Σ_{d≤K} b_d log^d n · n^s` have bounded pronic energy, then `b = 0`. -/
theorem powerLogRow_coeff_eq_zero_of_bounded {s : ℂ} (hs : 1 / 2 ≤ s.re) (K : ℕ) (b : ℕ → ℂ)
    {B : ℝ} (hre : ∀ T : ℕ, pronicNorm T (fun n => (powerLogRow s K b n).re) ≤ B)
    (him : ∀ T : ℕ, pronicNorm T (fun n => (powerLogRow s K b n).im) ≤ B) :
    ∀ d ≤ K, b d = 0 := by
  by_contra hne
  push_neg at hne
  -- the top nonzero coefficient
  classical
  set S := (range (K + 1)).filter (fun d => b d ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨d, hd, hbd⟩ := hne
    exact ⟨d, mem_filter.mpr ⟨mem_range.mpr (by omega), hbd⟩⟩
  set D := S.max' hSne with hD
  have hDS : D ∈ S := S.max'_mem hSne
  have hbD : b D ≠ 0 := (mem_filter.mp hDS).2
  have hDK : D ≤ K := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hDS).1)
  have htop : ∀ d ≤ K, D < d → b d = 0 := by
    intro d hd hDd
    by_contra h
    have : d ∈ S := mem_filter.mpr ⟨mem_range.mpr (by omega), h⟩
    exact absurd (S.le_max' d this) (not_le.mpr hDd)
  set L := ∑ d ∈ range D, ‖b d‖ with hL
  have hbD0 : 0 < ‖b D‖ := norm_pos_iff.mpr hbD
  set L₀ := max 1 (2 * L / ‖b D‖) with hL₀
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp L₀)
  -- lower bound of the block beyond `N₀`
  have hlow : ∀ n : ℕ, N₀ ≤ n → 1 ≤ n →
      ‖b D‖ / 2 * (n : ℝ) ^ s.re ≤ ‖powerLogRow s K b n‖ := by
    intro n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlogL : L₀ ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hn0]
      exact hN₀.le.trans (by exact_mod_cast hn)
    have hlog1 : 1 ≤ Real.log n := (le_max_left _ _).trans hlogL
    have hlog2 : 2 * L / ‖b D‖ ≤ Real.log n := (le_max_right _ _).trans hlogL
    set λ' := Real.log n with hλ
    have hλ0 : 0 ≤ λ' := by linarith
    have hnpow : ‖(((n : ℝ)) : ℂ) ^ s‖ = (n : ℝ) ^ s.re := Complex.norm_cpow_eq_rpow_re_of_pos hn0 s
    have hrow : powerLogRow s K b n = (b D * (λ' : ℂ) ^ D +
        ∑ d ∈ range D, b d * (λ' : ℂ) ^ d) * (((n : ℝ)) : ℂ) ^ s := by
      rw [powerLogRow]
      have hsplitK : range (K + 1) = range (D + 1) ∪ Ico (D + 1) (K + 1) := by
        ext d; simp only [mem_union, mem_range, mem_Ico]; omega
      rw [hsplitK, sum_union (disjoint_left.mpr fun d h1 h2 => by
        simp only [mem_range, mem_Ico] at h1 h2; omega)]
      have hzero : ∑ d ∈ Ico (D + 1) (K + 1), b d * ((λ' : ℂ) ^ d * (((n : ℝ)) : ℂ) ^ s) = 0 :=
        sum_eq_zero fun d hd => by
          simp only [mem_Ico] at hd
          rw [htop d (by omega) (by omega), zero_mul]
      rw [hzero, add_zero, sum_range_succ, add_mul, sum_mul]
      ring_nf
    have hsmall : ‖∑ d ∈ range D, b d * (λ' : ℂ) ^ d‖ ≤ L * λ' ^ D / λ' := by
      refine (norm_sum_le _ _).trans ?_
      rw [hL, sum_mul, sum_div]
      refine sum_le_sum fun d hd => ?_
      have hdD : d + 1 ≤ D := mem_range.mp hd
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hλ0]
      have hpow : λ' ^ d ≤ λ' ^ D / λ' := by
        rw [le_div_iff₀ (by linarith), ← pow_succ]
        exact pow_le_pow_right₀ hlog1 hdD
      calc ‖b d‖ * λ' ^ d ≤ ‖b d‖ * (λ' ^ D / λ') := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = ‖b d‖ * λ' ^ D / λ' := by ring
    have hLλ : L * λ' ^ D / λ' ≤ ‖b D‖ / 2 * λ' ^ D := by
      rw [div_le_iff₀ (by linarith)]
      have h2 : 2 * L ≤ ‖b D‖ * λ' := by
        have := (div_le_iff₀ hbD0).mp hlog2; linarith
      have hD0 : 0 ≤ λ' ^ D := pow_nonneg hλ0 D
      nlinarith
    have htopn : ‖b D * (λ' : ℂ) ^ D‖ = ‖b D‖ * λ' ^ D := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hλ0]
    have hλD : 1 ≤ λ' ^ D := one_le_pow₀ hlog1
    rw [hrow, norm_mul, hnpow]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hn0.le _)
    have := norm_sub_norm_le (b D * (λ' : ℂ) ^ D) (-(∑ d ∈ range D, b d * (λ' : ℂ) ^ d))
    rw [sub_neg_eq_add, norm_neg] at this
    nlinarith
  -- energy lower bound
  obtain ⟨T, hT1, hT⟩ := TransHorizonIncidenceMechanics.not_bddAbove_sum_Icc_one_div
    (8 * (2 * B ^ 2) / ‖b D‖ ^ 2 + ∑ n ∈ Icc 1 N₀, 1 / (n : ℝ))
  have hsumsq : ∑ n ∈ Icc 1 T, ‖powerLogRow s K b n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ 2 * B ^ 2 := by
    have hB0 : 0 ≤ B := (pronicNorm_nonneg 0 _).trans (hre 0)
    have h1 := pronicNorm_sq T (fun n => (powerLogRow s K b n).re)
    have h2 := pronicNorm_sq T (fun n => (powerLogRow s K b n).im)
    have h1' : pronicNorm T (fun n => (powerLogRow s K b n).re) ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (pronicNorm_nonneg _ _) (hre T) 2
    have h2' : pronicNorm T (fun n => (powerLogRow s K b n).im) ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (pronicNorm_nonneg _ _) (him T) 2
    have hsplit : ∑ n ∈ Icc 1 T, ‖powerLogRow s K b n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ n ∈ Icc 1 T, (powerLogRow s K b n).re ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) +
          ∑ n ∈ Icc 1 T, (powerLogRow s K b n).im ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [← add_div, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hsplit, ← h1, ← h2]
    linarith
  have hterm : ∀ n ∈ Icc 1 T, N₀ < n → ‖b D‖ ^ 2 / 8 * (1 / (n : ℝ)) ≤
      ‖powerLogRow s K b n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn hN
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hl := hlow n hN.le hn1
    have hpow : (n : ℝ) ≤ ((n : ℝ) ^ s.re) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ (s.re * ((2 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hnR (by push_cast; linarith)
    have hsq : (‖b D‖ / 2) ^ 2 * (n : ℝ) ≤ ‖powerLogRow s K b n‖ ^ 2 := by
      have h0 : 0 ≤ ‖b D‖ / 2 * (n : ℝ) ^ s.re := by positivity
      calc (‖b D‖ / 2) ^ 2 * (n : ℝ) ≤ (‖b D‖ / 2) ^ 2 * ((n : ℝ) ^ s.re) ^ 2 :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (‖b D‖ / 2 * (n : ℝ) ^ s.re) ^ 2 := by ring
        _ ≤ ‖powerLogRow s K b n‖ ^ 2 := pow_le_pow_left₀ h0 hl 2
    rw [le_div_iff₀ (by positivity)]
    calc ‖b D‖ ^ 2 / 8 * (1 / (n : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ‖b D‖ ^ 2 / 8 * (1 / (n : ℝ)) * ((n : ℝ) * (2 * n)) := by
          gcongr; linarith
      _ = (‖b D‖ / 2) ^ 2 * (n : ℝ) := by field_simp; ring
      _ ≤ _ := hsq
  -- split the harmonic sum at `N₀`
  have hharm : ∑ n ∈ Icc 1 T, 1 / (n : ℝ) ≤ ∑ n ∈ Icc 1 N₀, 1 / (n : ℝ) +
      ∑ n ∈ (Icc 1 T).filter (fun n => N₀ < n), 1 / (n : ℝ) := by
    rw [← sum_filter_add_sum_filter_not (Icc 1 T) (fun n => N₀ < n), add_comm]
    refine add_le_add_right (sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => by
      positivity) _
    simp only [mem_filter, mem_Icc, not_lt] at hn ⊢
    omega
  have hfilt : ‖b D‖ ^ 2 / 8 * ∑ n ∈ (Icc 1 T).filter (fun n => N₀ < n), 1 / (n : ℝ) ≤ 2 * B ^ 2 := by
    rw [mul_sum]
    refine (sum_le_sum fun n hn => hterm n (mem_filter.mp hn).1 (mem_filter.mp hn).2).trans ?_
    refine le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => by positivity)
      hsumsq
  have hb2 : 0 < ‖b D‖ ^ 2 := by positivity
  have : ∑ n ∈ (Icc 1 T).filter (fun n => N₀ < n), 1 / (n : ℝ) ≤ 8 * (2 * B ^ 2) / ‖b D‖ ^ 2 := by
    rw [le_div_iff₀ hb2]; linarith
  linarith

/-! ### The index theorem -/

/-- **Power-log eigenstates of the renormalized cofactor are counted by the zero multiplicity.**
Let `1/2 ≤ Re s < 1 − ε` and let `ζ` vanish to order exactly `m` at `s + ε`. The real and
imaginary parts of `Σ_{k≤K} c_k log^k n · n^s` both satisfy the renormalized inversion law iff
`c_k = 0` for every `m ≤ k ≤ K`. -/
theorem powerLogRows_renormalizedInversion_iff (ε : SubcriticalDamping) {s : ℂ}
    (hs0 : 1 / 2 ≤ s.re) (hs1 : s.re < 1 - ε) {m : ℕ}
    (hm0 : ∀ i < m, iteratedDeriv i riemannZeta (s + (ε : ℝ)) = 0)
    (hm1 : iteratedDeriv m riemannZeta (s + (ε : ℝ)) ≠ 0) (K : ℕ) (c : ℕ → ℂ) :
    ((∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n => powerLogReRow s K c n +
        renormalizedCofactorOperator ε (powerLogTraceVector ε (by linarith) hs1 K c) n) ≤ B) ∧
      (∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n => powerLogReRow s K (fun k => -I * c k) n +
        renormalizedCofactorOperator ε
          (powerLogTraceVector ε (by linarith) hs1 K (fun k => -I * c k)) n) ≤ B)) ↔
      ∀ k ≤ K, m ≤ k → c k = 0 := by
  have hs0' : 0 < s.re := by linarith
  obtain ⟨B₁, hB₁⟩ := exists_pronicNorm_powerLogRow_symbol_le ε hs0' hs1 K c
  obtain ⟨B₂, hB₂⟩ := exists_pronicNorm_powerLogRow_symbol_le ε hs0' hs1 K (fun k => -I * c k)
  have hleib : ∀ n, (∑ k ∈ range (K + 1), (-I * c k) * zetaLeibnizRow ε s k n).re =
      (∑ k ∈ range (K + 1), c k * zetaLeibnizRow ε s k n).im := by
    intro n
    simp only [mul_assoc, ← mul_sum, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]
  -- difference of two bounded rows is bounded
  have hdiff : ∀ (f g : ℕ → ℝ) (Bf Bg : ℝ), (∀ T, pronicNorm T f ≤ Bf) →
      (∀ T, pronicNorm T (fun n => f n - g n) ≤ Bg) → ∀ T, pronicNorm T g ≤ Bf + Bg := by
    intro f g Bf Bg hf hfg T
    have h := BezoutValuationIncidence.pronicNorm_add_le T f (fun n => -(f n - g n))
    have hneg : pronicNorm T (fun n => -(f n - g n)) = pronicNorm T (fun n => f n - g n) := by
      simp only [BezoutValuationIncidence.pronicNorm, neg_sq]
    have heq : (fun n => f n + -(f n - g n)) = g := by funext n; ring
    rw [heq, hneg] at h
    linarith [hf T, hfg T]
  rw [← leibnizCoeff_eq_zero_iff hm0 hm1 K c]
  constructor
  · rintro ⟨⟨B, hB⟩, ⟨B', hB'⟩⟩
    have hre := hdiff _ _ B B₁ hB hB₁
    have him := hdiff _ _ B' B₂ hB' hB₂
    simp only [hleib, sum_mul_zetaLeibnizRow] at hre him
    exact powerLogRow_coeff_eq_zero_of_bounded hs0 K _ (B := max (B + B₁) (B' + B₂))
      (fun T => (hre T).trans (le_max_left _ _)) (fun T => (him T).trans (le_max_right _ _))
  · intro hb
    have hzero : ∀ n, powerLogRow s K (leibnizCoeff ε s K c) n = 0 := by
      intro n
      refine sum_eq_zero fun d hd => ?_
      rw [hb d (Nat.lt_succ_iff.mp (mem_range.mp hd)), zero_mul]
    refine ⟨⟨B₁, fun T => ?_⟩, ⟨B₂, fun T => ?_⟩⟩
    · have h := hB₁ T
      simp only [sum_mul_zetaLeibnizRow, hzero, Complex.zero_re, sub_zero] at h
      exact h
    · have h := hB₂ T
      simp only [hleib, sum_mul_zetaLeibnizRow, hzero, Complex.zero_im, sub_zero] at h
      exact h

/-- The order of `ζ` at a point of the open critical strip is finite. -/
theorem analyticOrderAt_riemannZeta_ne_top_of_strip {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderAt riemannZeta z ≠ ⊤ := by
  rw [← RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩]
  exact RHTower.xi_orderAt_ne_top z

/-- **Index theorem for the renormalized cofactor.** With `m = ord_{s+ε} ζ`, the power-log rows
of exponent `s` satisfying the renormalized inversion law are exactly those supported on
`log^k`, `k < m`: their complex dimension is the multiplicity of the zero at `s + ε`. -/
theorem powerLogRows_renormalizedInversion_iff_order (ε : SubcriticalDamping) {s : ℂ}
    (hs0 : 1 / 2 ≤ s.re) (hs1 : s.re < 1 - ε) (K : ℕ) (c : ℕ → ℂ) :
    ((∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n => powerLogReRow s K c n +
        renormalizedCofactorOperator ε (powerLogTraceVector ε (by linarith) hs1 K c) n) ≤ B) ∧
      (∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n => powerLogReRow s K (fun k => -I * c k) n +
        renormalizedCofactorOperator ε
          (powerLogTraceVector ε (by linarith) hs1 K (fun k => -I * c k)) n) ≤ B)) ↔
      ∀ k ≤ K, (analyticOrderAt riemannZeta (s + (ε : ℝ))).toNat ≤ k → c k = 0 := by
  have hz0 : 0 < (s + (ε : ℝ)).re := by simp; linarith [ε.property.1]
  have hz1 : (s + (ε : ℝ)).re < 1 := by simp; linarith
  have hne1 : s + (ε : ℝ) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hfin := analyticOrderAt_riemannZeta_ne_top_of_strip hz0 hz1
  have han : AnalyticAt ℂ riemannZeta (s + (ε : ℝ)) :=
    (fun z (hz : z ∈ {w : ℂ | w ≠ 1}) =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt : DifferentiableOn ℂ riemannZeta
        {w : ℂ | w ≠ 1}).analyticAt (isOpen_ne.mem_nhds hne1)
  have hord : analyticOrderAt riemannZeta (s + (ε : ℝ)) =
      ((analyticOrderAt riemannZeta (s + (ε : ℝ))).toNat : ℕ∞) := (ENat.coe_toNat hfin).symm
  obtain ⟨hm0, hm1⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).mp hord
  exact powerLogRows_renormalizedInversion_iff ε hs0 hs1 hm0 hm1 K c

end GaloisForLFunctions.ArithmeticDefectRigidity
