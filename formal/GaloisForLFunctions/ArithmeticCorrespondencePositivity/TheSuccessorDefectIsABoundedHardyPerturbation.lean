import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelCofactorGramsSelectTheDominantZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorEnergyPaysTheCriticalZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheSuccessorIsInvisibleAtZeros

/-!
# The successor defect is a bounded Hardy perturbation

`TheSuccessorIsInvisibleAtZeros` (P5) shows that the successor defect
`D_Λ(s) = Σ_n Λ(n+1)((n+1)^{−s} − (n+2)^{−s})` is holomorphic on `Re s > 0`, and
`TheSuccessorDefectInTheStrip` (P32) bounds it pointwise by `(|s| + 1)^{1−σ+η}`. Here its mean square
on vertical lines is computed exactly.

* **`D_Λ` is the Mellin pairing of the von Mangoldt row** (`complexMellinPairing_vonMangoldtRow`),
  so `D_Λ(s)/s` is the line symbol of the log profile `e^{−u/2} Λ(⌊e^u⌋)`, whose pronic energy
  `Σ_n Λ(n)²/(n(n+1))` is finite (`summable_vonMangoldt_pronic`).
* **The Plancherel identity** (`integral_norm_sq_succShiftDefect_eq`). For `c > 0`, with
  `s = ½ + c + iy`, `∫ |D_Λ(s)/s|² dy = 2π Σ_n Λ(n)² w_c(n)`, `w_c` the Abel weight.
* **The Hardy bound** (`integral_norm_sq_succShiftDefect_le`, `tendsto_integral_norm_sq_succShiftDefect`).
  `∫ |D_Λ(s)/s|² dy ≤ 2π Σ_n Λ(n)²/(n(n+1))` on every line `Re s > ½`, with equality in the limit
  `c ↓ 0`: `D_Λ(s)/s` lies in the Hardy space `H²` of `Re s > ½` with norm
  `(2π Σ_n Λ(n)²/(n(n+1)))^{1/2}` — bounded in mean square, although pointwise it grows like
  `|t|^{1/2+η}` on the critical line.
* **Successor invariance of the Cramér bound** (`not_forall_shiftedPrimeError_energy_le_linear`).
  The successor-shifted prime error `ψ(n+1) − n` differs from `ψ(n) − n` by the finite-energy row
  `Λ(n+1)`, so it has the same unconditional log-slope bound `Σ_ρ m_ρ²/|ρ|²` as P41.

So what a positivity can read of the successor is a finite Hardy norm: the successor perturbs every
energy by a bounded amount and changes no slope, no escape atom and no residue mass.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.TransHorizonIncidenceMechanics (complexMellinCell complexMellinPairing)
open GaloisForLFunctions.ArithmeticDefectRigidity (logProfile)
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy (rowDilate)
open ArithmeticFunction (vonMangoldt)

/-! ### The von Mangoldt row -/

/-- The von Mangoldt row `n ↦ Λ(n)`. -/
def vonMangoldtRow (n : ℕ) : ℝ := vonMangoldt n

theorem vonMangoldtRow_zero : vonMangoldtRow 0 = 0 := by simp [vonMangoldtRow]

/-- `Λ(n)² ≤ 16 n^{1/2}`, from `Λ(n) ≤ log n ≤ 4 n^{1/4}`. -/
theorem vonMangoldt_sq_le (n : ℕ) : vonMangoldt n ^ 2 ≤ 16 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have h0 : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : vonMangoldt n ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div (Nat.cast_nonneg n) (show (0 : ℝ) < 1 / 4 by norm_num)
    calc vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) := this
      _ = 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by ring
  calc vonMangoldt n ^ 2 ≤ (4 * (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 16 * (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 4 : ℝ)), ← Real.rpow_mul (Nat.cast_nonneg n)]
        norm_num

/-- The pronic energy of the von Mangoldt row is finite. -/
theorem summable_vonMangoldt_pronic :
    Summable fun n : ℕ => vonMangoldtRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  refine ((Real.summable_nat_rpow.mpr (show (-3 / 2 : ℝ) < -1 by norm_num)).mul_left 16
    ).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [vonMangoldtRow]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ (by positivity)]
  calc vonMangoldtRow n ^ 2 ≤ 16 * (n : ℝ) ^ (1 / 2 : ℝ) := vonMangoldt_sq_le n
    _ = 16 * (n : ℝ) ^ (-3 / 2 : ℝ) * ((n : ℝ) * (n : ℝ)) := by
        have e : (n : ℝ) ^ (-3 / 2 : ℝ) * ((n : ℝ) * (n : ℝ)) = (n : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← sq, ← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
        rw [mul_assoc, e]
    _ ≤ 16 * (n : ℝ) ^ (-3 / 2 : ℝ) * ((n : ℝ) * ((n : ℝ) + 1)) := by gcongr; linarith


/-- The successor energy `Σ_n Λ(n)²/(n(n+1))`. -/
def successorEnergy : ℝ := ∑' n : ℕ, vonMangoldtRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

theorem successorEnergy_nonneg : 0 ≤ successorEnergy := tsum_nonneg fun n => by positivity

theorem vonMangoldt_energy_le (T : ℕ) :
    ∑ n ∈ Finset.Icc 1 T, vonMangoldtRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      successorEnergy * ((T : ℝ) + 1) ^ (0 : ℝ) := by
  rw [Real.rpow_zero, mul_one]
  exact summable_vonMangoldt_pronic.sum_le_tsum _ fun n _ => by positivity

/-- **`D_Λ` is the Mellin pairing of the von Mangoldt row.** -/
theorem complexMellinPairing_vonMangoldtRow {s : ℂ} (hs : 0 < s.re) :
    complexMellinPairing vonMangoldtRow s = succShiftDefect vonMangoldtC s := by
  have hshift : ∀ n : ℕ, (vonMangoldtRow (n + 1) : ℂ) * complexMellinCell s (n + 1) =
      succShiftTerm vonMangoldtC n s := by
    intro n
    simp only [vonMangoldtRow, vonMangoldtC, complexMellinCell, succShiftTerm]
    push_cast
    ring_nf
  have hsum : Summable fun n => succShiftTerm vonMangoldtC n s := by
    refine Summable.of_norm (((summable_vonMangoldt_shift hs).mul_left ‖s‖).of_nonneg_of_le
      (fun n => norm_nonneg _) fun n => ?_)
    calc ‖succShiftTerm vonMangoldtC n s‖
        ≤ ‖vonMangoldtC (n + 1)‖ * (‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) :=
          norm_succShiftTerm_le _ n hs
      _ = ‖s‖ * (‖vonMangoldtC (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) := by ring
  have hsum' : Summable fun n => (vonMangoldtRow n : ℂ) * complexMellinCell s n :=
    (summable_nat_add_iff 1).mp (by simpa only [hshift] using hsum)
  rw [complexMellinPairing, hsum'.tsum_eq_zero_add, succShiftDefect]
  simp only [vonMangoldtRow_zero, Complex.ofReal_zero, zero_mul, zero_add]
  exact tsum_congr hshift

/-- The line symbol of the von Mangoldt profile is `D_Λ(s)/s`, `s = c + ½ + iy`. -/
theorem lineSymbol_vonMangoldt_eq {c : ℝ} (hc : 0 < c) (y : ℝ) :
    lineSymbol (logProfile vonMangoldtRow) c y =
      succShiftDefect vonMangoldtC (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
        (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  rw [lineSymbol_logProfile_eq vonMangoldtRow_zero successorEnergy_nonneg le_rfl
      vonMangoldt_energy_le (by linarith) y,
    complexMellinPairing_vonMangoldtRow (by simp; linarith)]

theorem dampedProfile_vonMangoldt_data {c : ℝ} (hc : 0 < c) :
    Integrable (dampedProfile (logProfile vonMangoldtRow) c) ∧
      MemLp (dampedProfile (logProfile vonMangoldtRow) c) 2 :=
  integrable_and_memLp_dampedProfile_logProfile vonMangoldtRow_zero successorEnergy_nonneg le_rfl
    vonMangoldt_energy_le (by linarith)

/-- **The Plancherel identity for the successor defect.** For `c > 0`, `s = ½ + c + iy`,
`∫ |D_Λ(s)/s|² dy = 2π Σ_n Λ(n)² w_c(n)`. -/
theorem integral_norm_sq_succShiftDefect_eq {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, ‖succShiftDefect vonMangoldtC (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
        (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 =
      2 * Real.pi * abelPairing c vonMangoldtRow vonMangoldtRow := by
  obtain ⟨h1, h2⟩ := dampedProfile_vonMangoldt_data hc
  have hP := integral_norm_sq_lineSymbol h1 h2
  have hA := abelGram_logProfile_eq_abelPairing vonMangoldtRow_zero le_rfl le_rfl
    (show 2 * c + 1 ≠ 0 by linarith) h2
  simp only [Nat.cast_one, Real.log_one, Real.sqrt_one, one_mul] at hA
  have hrow : rowDilate 1 vonMangoldtRow = vonMangoldtRow := by funext n; simp [rowDilate]
  rw [hrow] at hA
  simp_rw [← lineSymbol_vonMangoldt_eq hc]
  rw [hP, hA]

/-- The Abel weight decreases in `c`: `w_c(n) ≤ w_0(n) = 1/(n(n+1))` for `n ≥ 1`, `c ≥ 0`. -/
theorem abelWeight_le_pronic {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) :
    abelWeight c n ≤ 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hrep : ∀ b : ℝ, b ≠ 0 → (((m + 1 : ℕ) : ℝ) ^ (-b) - (((m + 1 : ℕ) : ℝ) + 1) ^ (-b)) / b =
      ∫ u in logCell m, Real.exp (-(b * u)) := fun b hb => by
    rw [integral_logCell_exp hb m]; push_cast; ring_nf
  rw [← abelWeight_zero hn, abelWeight, abelWeight, hrep _ (by linarith), hrep _ (by norm_num)]
  refine setIntegral_mono_on ?_ ?_ (measurableSet_logCell m) fun u hu => ?_
  · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ico_subset_Icc_self
  · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ico_subset_Icc_self
  · have hu0 : 0 ≤ u := le_trans (Real.log_nonneg (by have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith)) hu.1
    exact Real.exp_le_exp.mpr (by nlinarith)

theorem abelWeight_nonneg {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ abelWeight c n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abelWeight]
  refine div_nonneg (sub_nonneg.mpr ?_) (by linarith)
  exact Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by linarith)

/-- The Abel pairing of the von Mangoldt row is at most its pronic energy. -/
theorem abelPairing_vonMangoldt_le {c : ℝ} (hc : 0 ≤ c) :
    abelPairing c vonMangoldtRow vonMangoldtRow ≤ successorEnergy := by
  have hterm : ∀ n : ℕ, vonMangoldtRow n * vonMangoldtRow n * abelWeight c n ≤
      vonMangoldtRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [vonMangoldtRow_zero]
    rw [← sq, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (abelWeight_le_pronic hc hn) (sq_nonneg _)
  have hnn : ∀ n : ℕ, 0 ≤ vonMangoldtRow n * vonMangoldtRow n * abelWeight c n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [vonMangoldtRow_zero]
    exact mul_nonneg (mul_self_nonneg _) (abelWeight_nonneg hc hn)
  exact (summable_vonMangoldt_pronic.of_nonneg_of_le hnn hterm).tsum_le_tsum hterm
    summable_vonMangoldt_pronic

/-- **The Hardy bound.** On every line `Re s = ½ + c`, `c > 0`,
`∫ |D_Λ(s)/s|² dy ≤ 2π Σ_n Λ(n)²/(n(n+1))`. -/
theorem integral_norm_sq_succShiftDefect_le {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, ‖succShiftDefect vonMangoldtC (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
        (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ 2 * Real.pi * successorEnergy := by
  rw [integral_norm_sq_succShiftDefect_eq hc]
  exact mul_le_mul_of_nonneg_left (abelPairing_vonMangoldt_le hc.le) (by positivity)

/-- **The Hardy norm.** As `c ↓ 0`, `∫ |D_Λ(½ + c + iy)/(½ + c + iy)|² dy → 2π Σ_n Λ(n)²/(n(n+1))`. -/
theorem tendsto_integral_norm_sq_succShiftDefect :
    Tendsto (fun c : ℝ => ∫ y : ℝ, ‖succShiftDefect vonMangoldtC
        (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) / (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * successorEnergy)) := by
  have hlim : Tendsto (fun c : ℝ => abelPairing c vonMangoldtRow vonMangoldtRow) (𝓝[>] 0)
      (𝓝 successorEnergy) := by
    unfold abelPairing successorEnergy
    refine tendsto_tsum_of_dominated_convergence summable_vonMangoldt_pronic (fun n => ?_) ?_
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [vonMangoldtRow_zero]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hc : ContinuousAt (fun c : ℝ => vonMangoldtRow n * vonMangoldtRow n * abelWeight c n) 0 := by
        unfold abelWeight
        refine continuousAt_const.mul (ContinuousAt.div ?_ (by fun_prop) (by norm_num))
        refine ContinuousAt.sub ?_ ?_
        · exact (continuousAt_const.rpow (by fun_prop) (Or.inl hn0.ne'))
        · exact (continuousAt_const.rpow (by fun_prop) (Or.inl (by positivity)))
      have := hc.tendsto
      have e : vonMangoldtRow n * vonMangoldtRow n * abelWeight 0 n =
          vonMangoldtRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        rw [abelWeight_zero hn]; ring
      rw [e] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc n
      have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [vonMangoldtRow_zero]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_self_nonneg _)
        (abelWeight_nonneg hc0 hn)), ← sq, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (abelWeight_le_pronic hc0 hn) (sq_nonneg _)
  refine ((hlim.const_mul (2 * Real.pi))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (integral_norm_sq_succShiftDefect_eq hc).symm

/-! ### Successor invariance of the Cramér bound -/

/-- The successor row `n ↦ Λ(n+1)`. -/
def shiftRow (n : ℕ) : ℝ := vonMangoldt (n + 1)

theorem shiftRow_zero : shiftRow 0 = 0 := by simp [shiftRow]

theorem abs_shiftRow_le (n : ℕ) : |shiftRow n| ≤ 1 * (n : ℝ) ^ 2 := by
  have h0 : 0 ≤ vonMangoldt (n + 1) := ArithmeticFunction.vonMangoldt_nonneg
  have hlog : vonMangoldt (n + 1) ≤ n := by
    calc vonMangoldt (n + 1) ≤ Real.log ((n + 1 : ℕ) : ℝ) := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ ((n + 1 : ℕ) : ℝ) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = n := by push_cast; ring
  rw [shiftRow, abs_of_nonneg h0, one_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-- The pronic energy of the successor row is finite. -/
theorem summable_shiftRow_pronic :
    Summable fun n : ℕ => shiftRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  refine ((Real.summable_nat_rpow.mpr (show (-3 / 2 : ℝ) < -1 by norm_num)).mul_left 32
    ).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [shiftRow_zero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    calc ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤ (4 * (n : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by push_cast; linarith) (by norm_num)
      _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hn0.le, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num)]
          norm_num
  have e : (n : ℝ) ^ (-3 / 2 : ℝ) * ((n : ℝ) * (n : ℝ)) = (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← sq, ← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
  rw [div_le_iff₀ (by positivity)]
  calc shiftRow n ^ 2 ≤ 16 * ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := vonMangoldt_sq_le (n + 1)
    _ ≤ 16 * (2 * (n : ℝ) ^ (1 / 2 : ℝ)) := by gcongr
    _ = 32 * (n : ℝ) ^ (-3 / 2 : ℝ) * ((n : ℝ) * (n : ℝ)) := by rw [mul_assoc 32, e]; ring
    _ ≤ 32 * (n : ℝ) ^ (-3 / 2 : ℝ) * ((n : ℝ) * ((n : ℝ) + 1)) := by gcongr; linarith

/-- The successor energy `Σ_n Λ(n+1)²/(n(n+1))`. -/
def shiftEnergy : ℝ := ∑' n : ℕ, shiftRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- The successor-shifted prime-error row `ψ(n+1) − n = Σ_{k ≤ n} (Λ(k+1) − 1)`. -/
def shiftedPrimeErrorRow (n : ℕ) : ℝ := primeErrorRow n + shiftRow n

theorem logProfile_shiftedPrimeErrorRow (u : ℝ) :
    logProfile shiftedPrimeErrorRow u = logProfile primeErrorRow u + logProfile shiftRow u := by
  simp only [logProfile, shiftedPrimeErrorRow]; ring

/-- The successor row has bounded log-scale energy on every horizon. -/
theorem integral_logProfile_shiftRow_sq_le {L : ℝ} (hL : 0 ≤ L) :
    ∫ u in (0 : ℝ)..L, logProfile shiftRow u ^ 2 ≤ shiftEnergy := by
  set T := ⌊Real.exp L⌋₊ with hT
  have hLT : L ≤ Real.log ((T : ℝ) + 1) :=
    ((Real.lt_log_iff_exp_lt (by positivity)).mpr (Nat.lt_floor_add_one _)).le
  calc ∫ u in (0 : ℝ)..L, logProfile shiftRow u ^ 2
      ≤ ∫ u in (0 : ℝ)..Real.log ((T : ℝ) + 1), logProfile shiftRow u ^ 2 := by
        refine intervalIntegral.integral_mono_interval le_rfl hL hLT
          (Eventually.of_forall fun u => sq_nonneg _) ?_
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (Real.log_nonneg (by
          linarith [T.cast_nonneg (α := ℝ)]))).mpr (integrableOn_logProfile_sq zero_le_one
            abs_shiftRow_le _)
    _ = ∑ n ∈ Finset.Icc 1 T, shiftRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
        (pronic_energy_eq_log_integral shiftRow T).symm
    _ ≤ shiftEnergy := summable_shiftRow_pronic.sum_le_tsum _ fun n _ => by positivity

/-- **Successor invariance of the Cramér bound.** For every finite set `Z` of critical zeros and every
`S < Σ_{ρ ∈ Z} ‖m_ρ/ρ‖²`, the log-energy of the successor-shifted prime error `ψ(n+1) − n` is not
bounded by `S L + B`: the finite-energy successor row changes no slope. -/
theorem not_forall_shiftedPrimeError_energy_le_linear (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2) {S B : ℝ}
    (hS : S < ∑ ρ ∈ Z, ‖(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ‖ ^ 2) :
    ¬ ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile shiftedPrimeErrorRow u ^ 2 ≤ S * L + B := by
  intro hlin
  by_cases hS0 : S < 0
  · exact not_forall_logEnergy_le_of_neg shiftedPrimeErrorRow hS0 hlin
  simp only [not_lt] at hS0
  set R := ∑ ρ ∈ Z, ‖(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ‖ ^ 2 with hR
  set t := (R - S) / (2 * (S + 1)) with ht
  have ht0 : 0 < t := div_pos (by linarith) (by linarith)
  have hS' : (1 + t) * S < R := by
    have : t * S < (R - S) / 2 := by
      rw [ht, div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  refine not_forall_primeError_energy_le_linear Z hZ hS'
    (B := (1 + t) * B + (1 + 1 / t) * shiftEnergy) fun L hL => ?_
  have hshifted : ∀ x, |shiftedPrimeErrorRow x| ≤ 2 * (x : ℝ) ^ 2 := fun x => by
    rw [shiftedPrimeErrorRow]
    have := abs_add_le (primeErrorRow x) (shiftRow x)
    linarith [abs_primeErrorRow_le x, abs_shiftRow_le x]
  have hii : ∀ (v : ℕ → ℝ) (K : ℝ), 0 ≤ K → (∀ n, |v n| ≤ K * (n : ℝ) ^ 2) →
      IntervalIntegrable (fun u => logProfile v u ^ 2) volume 0 L := fun v K hK hv =>
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hL).mpr (integrableOn_logProfile_sq hK hv _)
  have h1 := hii primeErrorRow 1 zero_le_one abs_primeErrorRow_le
  have h2 := hii shiftedPrimeErrorRow 2 (by norm_num) hshifted
  have h3 := hii shiftRow 1 zero_le_one abs_shiftRow_le
  calc ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2
      ≤ ∫ u in (0 : ℝ)..L, ((1 + t) * logProfile shiftedPrimeErrorRow u ^ 2 +
          (1 + 1 / t) * logProfile shiftRow u ^ 2) := by
        refine intervalIntegral.integral_mono_on hL h1 ((h2.const_mul _).add (h3.const_mul _))
          fun u _ => ?_
        rw [logProfile_shiftedPrimeErrorRow]
        set a := logProfile primeErrorRow u
        set b := logProfile shiftRow u
        have hab := sq_nonneg (t * a + (t + 1) * b)
        have key : t * (a ^ 2) ≤ t * ((1 + t) * (a + b) ^ 2 + (1 + 1 / t) * b ^ 2) := by
          have : t * ((1 + t) * (a + b) ^ 2 + (1 + 1 / t) * b ^ 2) =
              t * (1 + t) * (a + b) ^ 2 + (t + 1) * b ^ 2 := by field_simp
          rw [this]; nlinarith
        exact le_of_mul_le_mul_left key ht0
    _ = (1 + t) * (∫ u in (0 : ℝ)..L, logProfile shiftedPrimeErrorRow u ^ 2) +
          (1 + 1 / t) * (∫ u in (0 : ℝ)..L, logProfile shiftRow u ^ 2) := by
        rw [intervalIntegral.integral_add (h2.const_mul _) (h3.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ (1 + t) * (S * L + B) + (1 + 1 / t) * shiftEnergy := by
        gcongr
        · exact hlin L hL
        · exact integral_logProfile_shiftRow_sq_le hL
    _ = (1 + t) * S * L + ((1 + t) * B + (1 + 1 / t) * shiftEnergy) := by ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
