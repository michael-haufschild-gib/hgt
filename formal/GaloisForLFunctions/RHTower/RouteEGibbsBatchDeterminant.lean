import GaloisForLFunctions.RHTower.RouteEGibbsRapidity
import GaloisForLFunctions.RHTower.RouteEEulerDeficitTransport

/-!
# The terminal batch determinant

The literal Euler parity determinant of the batch `Y < p ≤ X` on the critical line factors as

```text
∏ |1 + p^{-1/2}e^{iφ_p}|² - ∏ |1 - p^{-1/2}e^{iφ_p}|²
  = 2 (∏ (1 + 1/p)) (∏ √(1 - u_p²)) sinh(R),
```

with `u_p = 2 d_p cos φ_p` and `R` the additive rapidity.  At the terminal frequency the two
product amplitudes only contribute `O(∑_{p ≤ X} 1/p)` to the logarithm, so the logarithmic size of
the determinant is the rapidity itself:

```text
log(1 + |D_X|) = (4√X / log X)(1 + o(1)).
```
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The primes of the batch `Y < p ≤ X`. -/
def batchPrimes (Y X : ℝ) : Finset ℕ := (Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊).filter Nat.Prime

/-- The critical local radius `p^{-1/2}`. -/
def batchRadius (k : ℕ) : ℝ := (k : ℝ) ^ (-(1 : ℝ) / 2)

/-- The terminal local phase `t_X log p`. -/
def batchPhase (X : ℝ) (k : ℕ) : ℝ := terminalFrequency X * Real.log k

/-- The local transverse coordinate `u_p = 2 d_p cos(t_X log p)`. -/
def batchCoordinate (X : ℝ) (k : ℕ) : ℝ :=
  2 * criticalHalfDensity k * Real.cos (batchPhase X k)

/-- The literal signed/unsigned Euler determinant of the batch on the critical line. -/
def batchEulerDeterminant (Y X : ℝ) : ℝ :=
  (∏ k ∈ batchPrimes Y X,
      Complex.normSq (1 + (batchRadius k : ℂ) * Complex.exp ((batchPhase X k : ℂ) * Complex.I)))
    - ∏ k ∈ batchPrimes Y X,
      Complex.normSq (1 - (batchRadius k : ℂ) * Complex.exp ((batchPhase X k : ℂ) * Complex.I))

/-- The baseline mass `∏ (1 + 1/p)` of the batch. -/
def batchMass (Y X : ℝ) : ℝ := ∏ k ∈ batchPrimes Y X, (1 + batchRadius k ^ 2)

/-- The transverse amplitude `∏ √(1 - u_p²)` of the batch. -/
def batchTransverse (Y X : ℝ) : ℝ :=
  ∏ k ∈ batchPrimes Y X, Real.sqrt (1 - batchCoordinate X k ^ 2)

/-! ## Elementary facts about the batch -/

theorem mem_batchPrimes {Y X : ℝ} (hY : 16 ≤ Y) {k : ℕ} (hk : k ∈ batchPrimes Y X) :
    16 ≤ k ∧ k.Prime ∧ k ≤ ⌊X⌋₊ := by
  rw [batchPrimes, Finset.mem_filter, Finset.mem_Ioc] at hk
  have hfloorY : 16 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  exact ⟨by omega, hk.2, hk.1.2⟩

theorem batchRadius_sq (k : ℕ) (hk : 0 < k) : batchRadius k ^ 2 = (k : ℝ)⁻¹ := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [batchRadius, pow_two, ← Real.rpow_add hk0]
  norm_num
  rw [Real.rpow_neg_one]

theorem abs_batchCoordinate_le {Y X : ℝ} (hY : 16 ≤ Y) {k : ℕ} (hk : k ∈ batchPrimes Y X) :
    |batchCoordinate X k| ≤ 1 / 2 :=
  abs_two_mul_criticalHalfDensity_mul_cos_le (mem_batchPrimes hY hk).1 _

theorem batchCoordinate_sq_le {Y X : ℝ} (hY : 16 ≤ Y) {k : ℕ} (hk : k ∈ batchPrimes Y X) :
    batchCoordinate X k ^ 2 ≤ 4 * (k : ℝ)⁻¹ := by
  obtain ⟨hk16, _, _⟩ := mem_batchPrimes hY hk
  have hk0 : 0 < k := by omega
  have hk0R : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hd0 := criticalHalfDensity_pos hk0
  have hdle := criticalHalfDensity_le hk0
  have hrp : (0 : ℝ) < (k : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hk0R _
  have hsq : ((k : ℝ) ^ (-(1 : ℝ) / 2)) * ((k : ℝ) ^ (-(1 : ℝ) / 2)) = (k : ℝ)⁻¹ := by
    rw [← Real.rpow_add hk0R]
    norm_num
    rw [Real.rpow_neg_one]
  have hcos : |Real.cos (batchPhase X k)| ≤ 1 := Real.abs_cos_le_one _
  have habs : |batchCoordinate X k| ≤ 2 * (k : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [batchCoordinate, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * criticalHalfDensity k)]
    nlinarith [hcos, hd0, hdle, abs_nonneg (Real.cos (batchPhase X k))]
  nlinarith [habs, abs_nonneg (batchCoordinate X k), sq_abs (batchCoordinate X k), hsq, hrp]

/-- The batch inverse-prime mass is below the Mertens sum. -/
theorem sum_inv_batchPrimes_le {Y X : ℝ} :
    ∑ k ∈ batchPrimes Y X, ((k : ℝ))⁻¹ ≤ Sieve.mertensS ⌊X⌋₊ := by
  have hsub : batchPrimes Y X ⊆ Nat.primesLE ⌊X⌋₊ := by
    intro k hk
    rw [batchPrimes, Finset.mem_filter, Finset.mem_Ioc] at hk
    exact Nat.mem_primesLE.mpr ⟨hk.1.2, hk.2⟩
  rw [Sieve.mertensS]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (le_of_eq ?_)
  · intro k hk _
    have hprime := Nat.prime_of_mem_primesLE hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hprime.pos
    positivity
  · exact Finset.sum_congr rfl fun p _ => by rw [one_div]

/-! ## The exact factorization -/

theorem criticalEulerTransverseCoordinate_batchRadius {k : ℕ} (hk : 0 < k) (φ : ℝ) :
    GibbsGas.criticalEulerTransverseCoordinate (batchRadius k) φ
      = 2 * criticalHalfDensity k * Real.cos φ := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsq := batchRadius_sq k hk
  have hden : (0 : ℝ) < 1 + (k : ℝ)⁻¹ := by positivity
  rw [GibbsGas.criticalEulerTransverseCoordinate, criticalHalfDensity, hsq, batchRadius]
  field_simp

theorem batchRapidity_eq_sum (Y X : ℝ) :
    batchRapidity Y X = ∑ k ∈ batchPrimes Y X, Real.artanh (batchCoordinate X k) := by
  rw [batchPrimes, Finset.sum_filter, batchRapidity]
  rfl

/-- **The batch determinant is one sinh of the batch rapidity.** -/
theorem batchEulerDeterminant_eq {Y X : ℝ} (hY : 16 ≤ Y) :
    batchEulerDeterminant Y X
      = 2 * batchMass Y X * batchTransverse Y X * Real.sinh (batchRapidity Y X) := by
  have hcoord : ∀ k ∈ batchPrimes Y X,
      GibbsGas.criticalEulerTransverseCoordinate (batchRadius k) (batchPhase X k)
        = batchCoordinate X k := by
    intro k hk
    obtain ⟨hk16, _, _⟩ := mem_batchPrimes hY hk
    exact criticalEulerTransverseCoordinate_batchRadius (by omega) _
  have hu : ∀ k ∈ batchPrimes Y X, batchCoordinate X k ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro k hk
    have h := abs_le.mp (abs_batchCoordinate_le hY hk)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [batchEulerDeterminant, GibbsGas.prod_normSq_plus_sub_prod_normSq_minus_eq]
  have hplus : (∏ k ∈ batchPrimes Y X,
      (1 + GibbsGas.criticalEulerTransverseCoordinate (batchRadius k) (batchPhase X k)))
      = ∏ k ∈ batchPrimes Y X, (1 + batchCoordinate X k) :=
    Finset.prod_congr rfl fun k hk => by rw [hcoord k hk]
  have hminus : (∏ k ∈ batchPrimes Y X,
      (1 - GibbsGas.criticalEulerTransverseCoordinate (batchRadius k) (batchPhase X k)))
      = ∏ k ∈ batchPrimes Y X, (1 - batchCoordinate X k) :=
    Finset.prod_congr rfl fun k hk => by rw [hcoord k hk]
  rw [hplus, hminus, GibbsGas.prod_one_add_sub_prod_one_sub_eq_rapidity _ _ hu,
    ← batchRapidity_eq_sum, ← batchTransverse, ← batchMass]
  ring

/-! ## The two amplitudes are logarithmically negligible -/

theorem one_le_batchMass (Y X : ℝ) : 1 ≤ batchMass Y X := by
  rw [batchMass]
  have h : (∏ _k ∈ batchPrimes Y X, (1 : ℝ)) ≤ ∏ k ∈ batchPrimes Y X, (1 + batchRadius k ^ 2) := by
    refine Finset.prod_le_prod (fun k _ => by norm_num) (fun k _ => ?_)
    nlinarith [sq_nonneg (batchRadius k)]
  rwa [Finset.prod_const_one] at h

theorem log_batchMass_le {Y X : ℝ} (hY : 16 ≤ Y) :
    Real.log (batchMass Y X) ≤ Sieve.mertensS ⌊X⌋₊ := by
  have hpos : ∀ k ∈ batchPrimes Y X, (1 : ℝ) + batchRadius k ^ 2 ≠ 0 := by
    intro k _
    nlinarith [sq_nonneg (batchRadius k)]
  rw [batchMass, Real.log_prod hpos]
  refine le_trans (Finset.sum_le_sum (fun k hk => ?_)) sum_inv_batchPrimes_le
  obtain ⟨hk16, _, _⟩ := mem_batchPrimes hY hk
  have hk0 : 0 < k := by omega
  have hrad : batchRadius k ^ 2 = (k : ℝ)⁻¹ := batchRadius_sq k hk0
  have hlog := Real.log_le_sub_one_of_pos (x := 1 + batchRadius k ^ 2)
    (by nlinarith [sq_nonneg (batchRadius k)])
  rw [hrad] at hlog ⊢
  linarith

theorem batchTransverse_pos {Y X : ℝ} (hY : 16 ≤ Y) : 0 < batchTransverse Y X := by
  rw [batchTransverse]
  refine Finset.prod_pos fun k hk => ?_
  have h := abs_le.mp (abs_batchCoordinate_le hY hk)
  have hsq : batchCoordinate X k ^ 2 ≤ 1 / 4 := by nlinarith [h.1, h.2]
  exact Real.sqrt_pos.mpr (by linarith)

theorem batchTransverse_le_one (Y X : ℝ) : batchTransverse Y X ≤ 1 := by
  rw [batchTransverse]
  have h : (∏ k ∈ batchPrimes Y X, Real.sqrt (1 - batchCoordinate X k ^ 2))
      ≤ ∏ _k ∈ batchPrimes Y X, (1 : ℝ) := by
    refine Finset.prod_le_prod (fun k _ => Real.sqrt_nonneg _) (fun k _ => ?_)
    have h1 : (1 : ℝ) - batchCoordinate X k ^ 2 ≤ 1 := by nlinarith [sq_nonneg (batchCoordinate X k)]
    calc Real.sqrt (1 - batchCoordinate X k ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  rwa [Finset.prod_const_one] at h

theorem neg_log_batchTransverse_le {Y X : ℝ} (hY : 16 ≤ Y) :
    -Real.log (batchTransverse Y X) ≤ 4 * Sieve.mertensS ⌊X⌋₊ := by
  have hpos : ∀ k ∈ batchPrimes Y X, Real.sqrt (1 - batchCoordinate X k ^ 2) ≠ 0 := by
    intro k hk
    have h := abs_le.mp (abs_batchCoordinate_le hY hk)
    have hsq : batchCoordinate X k ^ 2 ≤ 1 / 4 := by nlinarith [h.1, h.2]
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  rw [batchTransverse, Real.log_prod hpos, ← Finset.sum_neg_distrib]
  have hbound : ∀ k ∈ batchPrimes Y X,
      -Real.log (Real.sqrt (1 - batchCoordinate X k ^ 2)) ≤ 4 * ((k : ℝ))⁻¹ := by
    intro k hk
    have h := abs_le.mp (abs_batchCoordinate_le hY hk)
    have hsq0 : (0 : ℝ) ≤ batchCoordinate X k ^ 2 := sq_nonneg _
    have hsq : batchCoordinate X k ^ 2 ≤ 1 / 4 := by nlinarith [h.1, h.2]
    have hkinv := batchCoordinate_sq_le hY hk
    have hlogsqrt : Real.log (Real.sqrt (1 - batchCoordinate X k ^ 2))
        = Real.log (1 - batchCoordinate X k ^ 2) / 2 := Real.log_sqrt (by linarith)
    have hlow := neg_log_one_sub_le (z := batchCoordinate X k ^ 2) hsq0 (by linarith)
    rw [hlogsqrt]
    have hquad : batchCoordinate X k ^ 2 + 2 * (batchCoordinate X k ^ 2) ^ 2
        ≤ 2 * batchCoordinate X k ^ 2 := by nlinarith [hsq, hsq0]
    have : -(Real.log (1 - batchCoordinate X k ^ 2) / 2) ≤ batchCoordinate X k ^ 2 := by
      linarith
    linarith
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [← Finset.mul_sum]
  have := sum_inv_batchPrimes_le (Y := Y) (X := X)
  linarith

/-! ## The logarithmic size of the determinant -/

theorem exp_le_four_mul_sinh {r : ℝ} (hr : 1 ≤ r) : Real.exp r ≤ 4 * Real.sinh r := by
  have hexp : Real.exp r * Real.exp r = Real.exp (2 * r) := by
    rw [← Real.exp_add]
    ring_nf
  have h2r : (2 : ℝ) ≤ Real.exp (2 * r) := by
    have h := Real.add_one_le_exp (2 * r)
    linarith
  have hinv : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add]
    simp
  have hkey : 2 * Real.exp (-r) ≤ Real.exp r := by
    nlinarith [hexp, h2r, hinv, Real.exp_pos r, Real.exp_pos (-r)]
  rw [Real.sinh_eq]
  linarith

theorem two_mul_sinh_le_exp (r : ℝ) : 2 * Real.sinh r ≤ Real.exp r := by
  rw [Real.sinh_eq]
  have := Real.exp_pos (-r)
  linarith

/-- **The logarithmic size of the batch determinant is its rapidity.** -/
theorem abs_log_one_add_abs_batchEulerDeterminant_sub_le {Y X : ℝ} (hY : 16 ≤ Y)
    (hR : batchRapidity Y X ≤ -1) :
    |Real.log (1 + |batchEulerDeterminant Y X|) - (-batchRapidity Y X)|
      ≤ 1 + 5 * Sieve.mertensS ⌊X⌋₊ := by
  set r : ℝ := -batchRapidity Y X with hrdef
  have hr1 : (1 : ℝ) ≤ r := by rw [hrdef]; linarith
  have hA1 := one_le_batchMass Y X
  have hAlog := log_batchMass_le (Y := Y) (X := X) hY
  have hB0 := batchTransverse_pos (Y := Y) (X := X) hY
  have hB1 := batchTransverse_le_one Y X
  have hBlog := neg_log_batchTransverse_le (Y := Y) (X := X) hY
  have hmert : (0 : ℝ) ≤ Sieve.mertensS ⌊X⌋₊ := by
    rw [Sieve.mertensS]
    exact Finset.sum_nonneg fun p _ => by positivity
  have hrpos : (0 : ℝ) < r := by linarith
  have hsinh : (0 : ℝ) < Real.sinh r := by positivity
  have hfact := batchEulerDeterminant_eq (Y := Y) (X := X) hY
  have hsign : batchEulerDeterminant Y X
      = -(2 * batchMass Y X * batchTransverse Y X * Real.sinh r) := by
    rw [hfact, hrdef, Real.sinh_neg]
    ring
  have habsD : |batchEulerDeterminant Y X|
      = 2 * batchMass Y X * batchTransverse Y X * Real.sinh r := by
    rw [hsign, abs_neg, abs_of_nonneg (by positivity)]
  -- upper bound
  have hupper : Real.log (1 + |batchEulerDeterminant Y X|)
      ≤ Real.log 2 + Real.log (batchMass Y X) + r := by
    have hle : 1 + |batchEulerDeterminant Y X| ≤ 2 * batchMass Y X * Real.exp r := by
      rw [habsD]
      have h1 : 2 * batchMass Y X * batchTransverse Y X * Real.sinh r
          ≤ batchMass Y X * Real.exp r := by
        have hsl := two_mul_sinh_le_exp r
        have hAB : (0 : ℝ) ≤ batchMass Y X * batchTransverse Y X := by positivity
        calc 2 * batchMass Y X * batchTransverse Y X * Real.sinh r
            = (batchMass Y X * batchTransverse Y X) * (2 * Real.sinh r) := by ring
          _ ≤ (batchMass Y X * batchTransverse Y X) * Real.exp r :=
              mul_le_mul_of_nonneg_left hsl hAB
          _ ≤ batchMass Y X * Real.exp r := by
              have hE : (0 : ℝ) < Real.exp r := Real.exp_pos r
              have hA0 : (0 : ℝ) ≤ batchMass Y X := by linarith
              calc (batchMass Y X * batchTransverse Y X) * Real.exp r
                  ≤ (batchMass Y X * 1) * Real.exp r :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB1 hA0) hE.le
                _ = batchMass Y X * Real.exp r := by ring
      have h2 : (1 : ℝ) ≤ batchMass Y X * Real.exp r := by
        nlinarith [Real.one_le_exp (by linarith : (0:ℝ) ≤ r), hA1]
      linarith
    have hpos : (0 : ℝ) < 1 + |batchEulerDeterminant Y X| := by
      have := abs_nonneg (batchEulerDeterminant Y X)
      linarith
    have hlog := Real.log_le_log hpos hle
    have hrw : Real.log (2 * batchMass Y X * Real.exp r)
        = Real.log 2 + Real.log (batchMass Y X) + r := by
      rw [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos r)),
        Real.log_mul (by norm_num) (by positivity), Real.log_exp]
    linarith [hlog, hrw.le, hrw.ge]
  -- lower bound
  have hlower : Real.log (batchTransverse Y X) + r - Real.log 2
      ≤ Real.log (1 + |batchEulerDeterminant Y X|) := by
    have hle : batchTransverse Y X * Real.exp r / 2 ≤ 1 + |batchEulerDeterminant Y X| := by
      rw [habsD]
      have hsl := exp_le_four_mul_sinh hr1
      have hstep1 : batchTransverse Y X * Real.exp r / 2
          ≤ batchTransverse Y X * (4 * Real.sinh r) / 2 := by
        have := mul_le_mul_of_nonneg_left hsl hB0.le
        linarith
      have hstep2 : batchTransverse Y X * (4 * Real.sinh r) / 2
          ≤ 2 * batchMass Y X * batchTransverse Y X * Real.sinh r := by
        have hBs : (0 : ℝ) < batchTransverse Y X * Real.sinh r := mul_pos hB0 hsinh
        nlinarith [hBs, hA1]
      linarith
    have hpos : (0 : ℝ) < batchTransverse Y X * Real.exp r / 2 := by positivity
    have hlog := Real.log_le_log hpos hle
    have hrw : Real.log (batchTransverse Y X * Real.exp r / 2)
        = Real.log (batchTransverse Y X) + r - Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity)
        (ne_of_gt (Real.exp_pos r)), Real.log_exp]
    linarith [hlog, hrw.le, hrw.ge]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-! ## The terminal law -/

/-- **The terminal batch determinant law.**  With `Y = (log X)^A` the logarithmic size of the
signed/unsigned Euler determinant of the batch is `4√X/log X` to leading order. -/
theorem tendsto_log_one_add_abs_batchEulerDeterminant {A : ℝ} (hA : 0 < A) :
    Tendsto (fun X : ℝ =>
      Real.log (1 + |batchEulerDeterminant (Real.log X ^ A) X|) * Real.log X / X ^ ((1 : ℝ) / 2))
      atTop (nhds 4) := by
  have hYtop : Tendsto (fun X : ℝ => Real.log X ^ A) atTop atTop :=
    (tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop
  have hrap := tendsto_batchRapidity hA
  -- the rapidity is eventually below `-1`
  have hlogsqrt : Tendsto (fun X : ℝ => Real.log X / X ^ ((1 : ℝ) / 2)) atTop (nhds 0) := by
    have h := HTGeometry.tendsto_logPow_div_rpow (a := (1 : ℝ) / 2) (by norm_num) 1
    exact h.congr fun X => by rw [pow_one]
  have hRneg : ∀ᶠ X : ℝ in atTop, batchRapidity (Real.log X ^ A) X ≤ -1 := by
    have hlt := hrap.eventually (gt_mem_nhds (by norm_num : (-4 : ℝ) < -2))
    have hsmall := hlogsqrt.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hlt, hsmall, eventually_ge_atTop (3 : ℝ)] with X hX hXs hX3
    have hX0 : (0 : ℝ) < X := by linarith
    have hD : (0 : ℝ) < X ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hX0 _
    have hlogpos : (0 : ℝ) < Real.log X := Real.log_pos (by linarith)
    have hfac : (0 : ℝ) < Real.log X / X ^ ((1 : ℝ) / 2) := by positivity
    -- `R · (log X / √X) < -2` and the factor is at most one, so `R ≤ -2`
    by_contra hcon
    rw [not_le] at hcon
    have heq : batchRapidity (Real.log X ^ A) X * Real.log X / X ^ ((1 : ℝ) / 2)
        = batchRapidity (Real.log X ^ A) X * (Real.log X / X ^ ((1 : ℝ) / 2)) := by
      ring
    rw [heq] at hX
    have hgt : batchRapidity (Real.log X ^ A) X * (Real.log X / X ^ ((1 : ℝ) / 2))
        > -(Real.log X / X ^ ((1 : ℝ) / 2)) := by
      nlinarith [mul_pos (show (0 : ℝ) < batchRapidity (Real.log X ^ A) X + 1 by linarith) hfac]
    linarith
  -- the amplitude remainder is negligible
  have hmaj : Tendsto (fun X : ℝ =>
      (1 + 5 * Sieve.mertensS ⌊X⌋₊) * Real.log X / X ^ ((1 : ℝ) / 2)) atTop (nhds 0) := by
    have h1 := hlogsqrt
    have h2 := tendsto_mertensS_floor_mul_log_div_sqrt.const_mul (5 : ℝ)
    have h := h1.add h2
    rw [mul_zero, add_zero] at h
    refine h.congr fun X => ?_
    field_simp
  have hdiff : Tendsto (fun X : ℝ =>
      Real.log (1 + |batchEulerDeterminant (Real.log X ^ A) X|) * Real.log X / X ^ ((1 : ℝ) / 2)
        - (-(batchRapidity (Real.log X ^ A) X)) * Real.log X / X ^ ((1 : ℝ) / 2)) atTop
      (nhds 0) := by
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [hYtop.eventually_ge_atTop (16 : ℝ), hRneg, eventually_ge_atTop (3 : ℝ)]
      with X hY16 hR hX3
    have hX0 : (0 : ℝ) < X := by linarith
    have hD : (0 : ℝ) < X ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hX0 _
    have hlog0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
    have hkey := abs_log_one_add_abs_batchEulerDeterminant_sub_le
      (Y := Real.log X ^ A) (X := X) hY16 hR
    have hrw : Real.log (1 + |batchEulerDeterminant (Real.log X ^ A) X|) * Real.log X /
          X ^ ((1 : ℝ) / 2)
        - (-(batchRapidity (Real.log X ^ A) X)) * Real.log X / X ^ ((1 : ℝ) / 2)
        = (Real.log (1 + |batchEulerDeterminant (Real.log X ^ A) X|)
            - (-(batchRapidity (Real.log X ^ A) X))) * (Real.log X / X ^ ((1 : ℝ) / 2)) := by
      ring
    rw [Real.norm_eq_abs, hrw, abs_mul, abs_of_nonneg (div_nonneg hlog0 hD.le)]
    have hfac : (0 : ℝ) ≤ Real.log X / X ^ ((1 : ℝ) / 2) := div_nonneg hlog0 hD.le
    have hstep := mul_le_mul_of_nonneg_right hkey hfac
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  have hneg : Tendsto (fun X : ℝ =>
      (-(batchRapidity (Real.log X ^ A) X)) * Real.log X / X ^ ((1 : ℝ) / 2)) atTop (nhds 4) := by
    have h := hrap.neg
    rw [neg_neg] at h
    refine h.congr fun X => ?_
    ring
  have hsum := hdiff.add hneg
  rw [zero_add] at hsum
  exact hsum.congr fun X => by ring

end

end RHTower
