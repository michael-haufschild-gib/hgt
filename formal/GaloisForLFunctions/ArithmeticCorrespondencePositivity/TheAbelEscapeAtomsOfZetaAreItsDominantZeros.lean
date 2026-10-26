import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelEscapeStateIsTheBoundaryMeasureOfTheSymbol
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheLaplaceFormOfTheCofactorProfile
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheEscapeAlternative

/-!
# The Abel escape atoms of `ζ` are its dominant zeros

The Abel escape law (`TheAbelEscapeStateIsTheBoundaryMeasureOfTheSymbol`) reads escape states
from the symbol of a profile on vertical lines. Here the profile is the log profile
`g_ε(u) = e^{−u/2} A_ε(⌊e^u⌋)` of the damped Möbius receiver, and the symbol is computed.

* **Cells** (`integral_stepLaplaceIntegrand`). On the log cells `[log n, log(n+1))` the profile is
  constant, so `∫ e^{−su} f(⌊e^u⌋) du = Φ_f(s)/s` with the Mellin pairing
  `Φ_f(s) = Σ_n f(n)(n^{−s} − (n+1)^{−s})`, whenever `Σ |f(n)| n^{−Re s − 1} < ∞`.
* **Energy integrates the profile** (`integrable_and_memLp_dampedProfile_receiver`). Receiver
  energy `O((T+1)^κ)` puts `e^{−cu} g_ε` in `L¹ ∩ L²` for every `c > κ/2`, and then
  `G_ε(c + iy) = Φ_ε(s)/s`, `s = c + ½ + iy` (`lineSymbol_receiver_eq`).
* **Continuation** (`complexMellinPairing_receiver_eq`). On `(1+κ)/2 < Re s < 1`, off
  `s + ε = 1` and the zeros of `ζ(s + ε)`, `Φ_ε(s) = ζ(s)/ζ(s+ε) − m_ε ζ(s)` (identity theorem from
  the segment where both sides are Dirichlet series).
* **Translated simple zeros are simple poles** (`exists_cofactor_pole_bound`). Near `ρ − ε`, for a
  simple zero `ρ`, the symbol is `r/(s − ρ + ε)` plus a bounded function,
  `r = ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))` (difference quotients of `ζ(s + ε)`).
* **The atom law for `ζ`** (`tendsto_receiver_window_atom`). If `ρ` is dominant — the energy is
  `O((T+1)^κ)` for every `κ > 2(Re ρ − ε) − 1`, which by `TheEscapeAlternative` is the least
  possible exponent when `ρ` is uncancelled — then at `θ = Re ρ − ε − ½` the scaled spectral measure
  of the lines `Re s = θ + e` carries the atom `π ‖r‖² δ_{Im ρ}`. An uncancelled dominant zero
  forces Abel escape at rate `1/e` (`tendsto_receiver_abelGram_atTop`).
* **Zero-free segments carry no escape** (`tendsto_receiver_window_share_zero`). If the receiver
  escapes at `θ` and `ζ(s + ε)` has no zero on a segment of the line `Re s = θ + ½`, that segment's
  share of the spectral measure tends to zero.

So the finite-height part of every Abel escape state of `ζ` is exactly the set of dominant
translated zeros, each with the residue mass `‖ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))‖²`, unconditionally and
without an explicit formula; whatever is not carried by them escapes to infinite height.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.TransHorizonIncidenceMechanics (complexMellinCell complexMellinPairing)
open GaloisForLFunctions.ArithmeticDefectRigidity (mem_Ico_log_iff)

/-! ### The cells of a step profile -/

/-- The log cell `[log(n+1), log(n+2))` on which `⌊e^u⌋ = n + 1`. -/
def logCell (n : ℕ) : Set ℝ := Ico (Real.log ((n : ℝ) + 1)) (Real.log ((n : ℝ) + 2))

theorem measurableSet_logCell (n : ℕ) : MeasurableSet (logCell n) := measurableSet_Ico

theorem log_succ_le (n : ℕ) : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
  Real.log_le_log (by positivity) (by linarith)

theorem pairwise_disjoint_logCell : Pairwise (Function.onFun Disjoint logCell) := by
  intro m n hmn
  refine Set.disjoint_left.mpr fun u hm hn => hmn ?_
  have h1 := (mem_Ico_log_iff m).mp hm
  have h2 := (mem_Ico_log_iff n).mp hn
  omega

/-- The log cells tile `[0, ∞)`. -/
theorem iUnion_logCell : ⋃ n, logCell n = Ici 0 := by
  ext u
  simp only [mem_iUnion, mem_Ici]
  constructor
  · rintro ⟨n, hn⟩
    exact le_trans (Real.log_nonneg (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)) hn.1
  · intro hu
    have h1 : 1 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor (by simpa using Real.one_le_exp hu)
    refine ⟨⌊Real.exp u⌋₊ - 1, (mem_Ico_log_iff _).mpr (by omega)⟩

/-- The length of a log cell is at most `1/(n+1)`. -/
theorem log_cell_length_le (n : ℕ) :
    Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) ≤ ((n : ℝ) + 1)⁻¹ := by
  rw [← Real.log_div (by positivity) (by positivity)]
  have h := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 2) / ((n : ℝ) + 1) by positivity)
  have : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = ((n : ℝ) + 1)⁻¹ := by field_simp; ring
  linarith

theorem floor_exp_eq_zero_of_neg {u : ℝ} (hu : u < 0) : ⌊Real.exp u⌋₊ = 0 :=
  Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr hu)

/-- The complex step profile `e^{−su} f(⌊e^u⌋)`. -/
def stepLaplaceIntegrand (f : ℕ → ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-s * u) * (f ⌊Real.exp u⌋₊ : ℂ)

theorem norm_stepLaplaceIntegrand (f : ℕ → ℝ) (s : ℂ) (u : ℝ) :
    ‖stepLaplaceIntegrand f s u‖ = Real.exp (-(s.re * u)) * |f ⌊Real.exp u⌋₊| := by
  rw [stepLaplaceIntegrand, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  congr 2
  simp [Complex.mul_re]

theorem measurable_stepLaplaceIntegrand (f : ℕ → ℝ) (s : ℂ) :
    Measurable (stepLaplaceIntegrand f s) := by
  unfold stepLaplaceIntegrand
  refine (by fun_prop : Measurable fun u : ℝ => Complex.exp (-s * u)).mul ?_
  exact Complex.measurable_ofReal.comp
    ((measurable_from_nat (f := f)).comp Real.measurable_exp.nat_floor)

/-- On a log cell the step integrand is `f(n+1) e^{−su}`. -/
theorem stepLaplaceIntegrand_eqOn (f : ℕ → ℝ) (s : ℂ) (n : ℕ) :
    EqOn (stepLaplaceIntegrand f s) (fun u => (f (n + 1) : ℂ) * Complex.exp (-s * u)) (logCell n) := by
  intro u hu
  simp only [stepLaplaceIntegrand]
  rw [(mem_Ico_log_iff n).mp hu, mul_comm]

/-- The cell mass: `∫_{cell} ‖e^{−su} f(⌊e^u⌋)‖ ≤ |f(n+1)| (n+1)^{−Re s − 1}` for `Re s ≥ 0`. -/
theorem integral_norm_stepLaplaceIntegrand_cell_le (f : ℕ → ℝ) {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ∫ u in logCell n, ‖stepLaplaceIntegrand f s u‖ ≤
      |f (n + 1)| * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have hbound : ∀ u ∈ logCell n, ‖stepLaplaceIntegrand f s u‖ ≤ |f (n + 1)| * ((n : ℝ) + 1) ^ (-s.re) := by
    intro u hu
    rw [norm_stepLaplaceIntegrand, (mem_Ico_log_iff n).mp hu, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [Real.rpow_def_of_pos (by positivity)]
    refine Real.exp_le_exp.mpr ?_
    have := hu.1
    nlinarith
  have hvol : volume.real (logCell n) = Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) := by
    rw [logCell, Real.volume_real_Ico_of_le (log_succ_le n)]
  calc ∫ u in logCell n, ‖stepLaplaceIntegrand f s u‖
      ≤ |f (n + 1)| * ((n : ℝ) + 1) ^ (-s.re) * volume.real (logCell n) := by
        have := norm_setIntegral_le_of_norm_le_const (f := fun u => ‖stepLaplaceIntegrand f s u‖)
          (s := logCell n) (μ := volume) (C := |f (n + 1)| * ((n : ℝ) + 1) ^ (-s.re))
          (by rw [logCell, Real.volume_Ico]; exact ENNReal.ofReal_lt_top)
          (fun u hu => by rw [norm_norm]; exact hbound u hu)
        exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
    _ ≤ |f (n + 1)| * ((n : ℝ) + 1) ^ (-s.re) * ((n : ℝ) + 1)⁻¹ := by
        rw [hvol]; gcongr; exact log_cell_length_le n
    _ = |f (n + 1)| * ((n : ℝ) + 1) ^ (-s.re - 1) := by
        rw [mul_assoc, Real.rpow_sub (by positivity), Real.rpow_one, div_eq_mul_inv]


/-- The step integrand vanishes for `u < 0` when `f 0 = 0`. -/
theorem stepLaplaceIntegrand_of_neg {f : ℕ → ℝ} (hf0 : f 0 = 0) (s : ℂ) {u : ℝ} (hu : u < 0) :
    stepLaplaceIntegrand f s u = 0 := by
  rw [stepLaplaceIntegrand, floor_exp_eq_zero_of_neg hu, hf0, Complex.ofReal_zero, mul_zero]

theorem integrableOn_stepLaplaceIntegrand_cell (f : ℕ → ℝ) (s : ℂ) (n : ℕ) :
    IntegrableOn (stepLaplaceIntegrand f s) (logCell n) := by
  have hc : IntegrableOn (fun u : ℝ => (f (n + 1) : ℂ) * Complex.exp (-s * u)) (logCell n) := by
    refine (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ico_subset_Icc_self
  exact hc.congr_fun (stepLaplaceIntegrand_eqOn f s n).symm (measurableSet_logCell n)

/-- **Integrability of the step profile.** If `f 0 = 0` and `Σ |f(n)| n^{−Re s − 1} < ∞`, the
integrand `e^{−su} f(⌊e^u⌋)` is integrable on `ℝ`. -/
theorem integrable_stepLaplaceIntegrand {f : ℕ → ℝ} (hf0 : f 0 = 0) {s : ℂ} (hs : 0 ≤ s.re)
    (hsum : Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-s.re - 1)) :
    Integrable (stepLaplaceIntegrand f s) := by
  have hsum' : Summable fun n : ℕ => |f (n + 1)| * ((n : ℝ) + 1) ^ (-s.re - 1) := by
    have := (summable_nat_add_iff 1).mpr hsum
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hon : IntegrableOn (stepLaplaceIntegrand f s) (⋃ n, logCell n) := by
    refine integrableOn_iUnion_of_summable_integral_norm
      (integrableOn_stepLaplaceIntegrand_cell f s) ?_
    refine hsum'.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _)
      (integral_norm_stepLaplaceIntegrand_cell_le f hs)
  rw [iUnion_logCell] at hon
  refine hon.integrable_of_forall_notMem_eq_zero fun u hu => ?_
  exact stepLaplaceIntegrand_of_neg hf0 s (not_le.mp hu)

/-- **The Laplace transform of a step profile is its Mellin pairing over `s`.** Under the
summability of `Σ |f(n)| n^{−Re s − 1}`,
`∫ e^{−su} f(⌊e^u⌋) du = Φ_f(s)/s`, `Φ_f(s) = Σ_n f(n)(n^{−s} − (n+1)^{−s})`. -/
theorem integral_stepLaplaceIntegrand {f : ℕ → ℝ} (hf0 : f 0 = 0) {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-s.re - 1)) :
    ∫ u, stepLaplaceIntegrand f s u = complexMellinPairing f s / s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl _ hs
  have hint := integrable_stepLaplaceIntegrand hf0 hs.le hsum
  -- the integral lives on `[0, ∞)`
  have hIci : ∫ u, stepLaplaceIntegrand f s u = ∫ u in Ici 0, stepLaplaceIntegrand f s u := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    exact stepLaplaceIntegrand_of_neg hf0 s (not_le.mp hu)
  rw [hIci, ← iUnion_logCell, integral_iUnion measurableSet_logCell pairwise_disjoint_logCell
    (by rw [iUnion_logCell]; exact hint.integrableOn)]
  -- each cell is a Mellin cell
  have hcell : ∀ n : ℕ, ∫ u in logCell n, stepLaplaceIntegrand f s u =
      (f (n + 1) : ℂ) * complexMellinCell s (n + 1) / s := by
    intro n
    rw [setIntegral_congr_fun (measurableSet_logCell n) (stepLaplaceIntegrand_eqOn f s n), logCell,
      integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (log_succ_le n), intervalIntegral.integral_const_mul,
      integral_cell_cexp hs0, complexMellinCell]
    push_cast
    ring_nf
  simp_rw [hcell]
  rw [complexMellinPairing, tsum_div_const]
  have hsumm : Summable fun n : ℕ => (f n : ℂ) * complexMellinCell s n := by
    refine Summable.of_norm ?_
    refine (hsum.mul_left ‖s‖).of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf0]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |f n| * ‖complexMellinCell s n‖ ≤ |f n| * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) :=
          mul_le_mul_of_nonneg_left
            (TransHorizonIncidenceMechanics.norm_complexMellinCell_le hs hn) (abs_nonneg _)
      _ = ‖s‖ * (|f n| * (n : ℝ) ^ (-s.re - 1)) := by ring
  rw [hsumm.tsum_eq_zero_add]
  simp [hf0]


/-! ### The damped Möbius receiver on the log scale -/

open GaloisForLFunctions.TransHorizonIncidenceMechanics (weightCenteredPrefix weightCenteredPrefix_zero
  weightPronicEnergy_pmPowerDamped dampedDensity)
open GaloisForLFunctions.BezoutValuationIncidence (pmPowerDampedRealWeight)
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy (dampedMobiusEnergy)

/-- The damped Möbius receiver `A_ε(n) = Σ_{j ≤ n} Σ_{d ∣ j} μ(d) d^{−ε} − m_ε n`. -/
abbrev receiver (ε : ℝ) : ℕ → ℝ := weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε)

/-- The log profile `g_ε(u) = e^{−u/2} A_ε(⌊e^u⌋)` of the receiver. -/
def receiverLogProfile (ε u : ℝ) : ℝ := Real.exp (-(u / 2)) * receiver ε ⌊Real.exp u⌋₊

/-- The receiver energy in prefix form. -/
theorem receiver_energy_eq (ε : ℝ) (T : ℕ) :
    ∑ n ∈ Finset.Icc 1 T, receiver ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) = dampedMobiusEnergy ε T := by
  have h := weightPronicEnergy_pmPowerDamped ε T
  unfold TransHorizonIncidenceMechanics.weightPronicEnergy at h
  exact h

/-- The damped log profile is the real step integrand at `s = c + ½`. -/
theorem ofReal_dampedProfile_receiver (ε c u : ℝ) :
    ((dampedProfile (receiverLogProfile ε) c u : ℝ) : ℂ) =
      stepLaplaceIntegrand (receiver ε) (((c + 1 / 2 : ℝ)) : ℂ) u := by
  rw [dampedProfile, receiverLogProfile, stepLaplaceIntegrand, ← mul_assoc, ← Real.exp_add]
  push_cast
  rw [show -((c : ℂ) * (u : ℂ)) + -((u : ℂ) / 2) = -((c : ℂ) + 1 / 2) * (u : ℂ) by ring]

/-- **Energy growth integrates the damped profile.** If the receiver energy is `O((T+1)^κ)`, the
damped log profile `e^{−cu} g_ε(u)` lies in `L¹ ∩ L²` for every `c > κ/2`. -/
theorem integrable_and_memLp_dampedProfile_receiver {ε C κ c : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hE : ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ) (hc : κ / 2 < c) :
    Integrable (dampedProfile (receiverLogProfile ε) c) ∧
      MemLp (dampedProfile (receiverLogProfile ε) c) 2 := by
  have hA0 : receiver ε 0 = 0 := weightCenteredPrefix_zero _ _
  have hEA : ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, receiver ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      C * ((T : ℝ) + 1) ^ κ := fun T => by rw [receiver_energy_eq]; exact hE T
  have hc0 : 0 ≤ c := by linarith
  have hmeas : Measurable (dampedProfile (receiverLogProfile ε) c) := by
    unfold dampedProfile receiverLogProfile
    refine (by fun_prop : Measurable fun u : ℝ => Real.exp (-(c * u))).mul
      ((by fun_prop : Measurable fun u : ℝ => Real.exp (-(u / 2))).mul ?_)
    exact (measurable_from_nat (f := receiver ε)).comp Real.measurable_exp.nat_floor
  -- `L¹`
  have hsum1 : Summable fun n : ℕ => |receiver ε n| * (n : ℝ) ^ (-((c + 1 / 2 : ℝ) : ℂ).re - 1) := by
    simpa using ArithmeticCorrelationGeometry.summable_abs_mul_rpow_of_energy_growth hA0 hC hκ
      (b := c + 1 / 2) (by linarith) hEA
  have hI := integrable_stepLaplaceIntegrand hA0 (s := ((c + 1 / 2 : ℝ) : ℂ)) (by simp; linarith)
    hsum1
  refine ⟨?_, ?_⟩
  · refine hI.norm.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [← ofReal_dampedProfile_receiver, Complex.norm_real]
  -- `L²`: the square is the step integrand of `A²` at `2c + 1`
  · rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
    have hsq0 : (fun n => receiver ε n ^ 2) 0 = 0 := by simp [hA0]
    have hsum2 : Summable fun n : ℕ =>
        |receiver ε n ^ 2| * (n : ℝ) ^ (-((2 * c + 1 : ℝ) : ℂ).re - 1) := by
      have h1 := ArithmeticCorrelationGeometry.summable_mul_rpow_neg_of_partialSum_le
        (e := fun n => receiver ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) (fun n => by positivity)
        (by simp [hA0]) hC hκ (γ := 2 * c) (by linarith) hEA
      refine (h1.mul_left 2).of_nonneg_of_le (fun n => by positivity) fun n => ?_
      simp only [Complex.ofReal_re]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hA0]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_of_nonneg (sq_nonneg _), show -(2 * c + 1) - 1 = -(2 * c) - 2 by ring,
        Real.rpow_sub hn0, Real.rpow_two]
      have hle : (n : ℝ) * ((n : ℝ) + 1) ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have : ((n : ℝ) ^ 2)⁻¹ ≤ 2 * ((n : ℝ) * ((n : ℝ) + 1))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        calc ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ) * ((n : ℝ) + 1)) ≤
            ((n : ℝ) ^ 2)⁻¹ * (2 * (n : ℝ) ^ 2) := by gcongr
          _ = 2 := by field_simp
      calc receiver ε n ^ 2 * ((n : ℝ) ^ (-(2 * c)) * ((n : ℝ) ^ 2)⁻¹)
          ≤ receiver ε n ^ 2 * ((n : ℝ) ^ (-(2 * c)) * (2 * ((n : ℝ) * ((n : ℝ) + 1))⁻¹)) := by
            gcongr
        _ = 2 * (receiver ε n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1))⁻¹ * (n : ℝ) ^ (-(2 * c))) := by ring
    have hI2 := integrable_stepLaplaceIntegrand hsq0 (s := ((2 * c + 1 : ℝ) : ℂ))
      (by simp; linarith) hsum2
    refine hI2.norm.congr (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [norm_stepLaplaceIntegrand, Complex.ofReal_re, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, sq_abs, dampedProfile, receiverLogProfile, mul_pow, mul_pow,
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
    congr 2
    push_cast
    ring

/-- **The line symbol of the receiver is its Mellin pairing.** Under energy growth `O((T+1)^κ)`,
for `c > κ/2` and every height `y`,
`G_ε(c + iy) = Φ_ε(s)/s`, `s = c + ½ + iy`, `Φ_ε(s) = Σ_n A_ε(n)(n^{−s} − (n+1)^{−s})`. -/
theorem lineSymbol_receiver_eq {ε C κ c : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hE : ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ) (hc : κ / 2 < c) (y : ℝ) :
    lineSymbol (receiverLogProfile ε) c y =
      complexMellinPairing (receiver ε) (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
        (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  have hA0 : receiver ε 0 = 0 := weightCenteredPrefix_zero _ _
  have hEA : ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, receiver ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      C * ((T : ℝ) + 1) ^ κ := fun T => by rw [receiver_energy_eq]; exact hE T
  set s : ℂ := ((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hs
  have hsre : s.re = c + 1 / 2 := by simp [hs]
  have hsum : Summable fun n : ℕ => |receiver ε n| * (n : ℝ) ^ (-s.re - 1) := by
    rw [hsre]
    exact ArithmeticCorrelationGeometry.summable_abs_mul_rpow_of_energy_growth hA0 hC hκ
      (by linarith) hEA
  rw [← integral_stepLaplaceIntegrand hA0 (by rw [hsre]; linarith) hsum, lineSymbol,
    _root_.RHTower.laplaceBoundary]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [ofReal_dampedProfile_receiver, stepLaplaceIntegrand, stepLaplaceIntegrand, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  rw [hs]
  ring


/-- **The receiver pairing continues `ζ(s)/ζ(s+ε) − m_ε ζ(s)` into the strip.** If the receiver
energy is `O((T+1)^κ)`, then on `(1+κ)/2 < Re s < 1`, away from `s + ε = 1` and the
zeros of `ζ(s + ε)`, `Φ_ε(s) = ζ(s)/ζ(s+ε) − m_ε ζ(s)` (identity theorem from the real segment
`Re s > 1 − ε`, where both sides are Dirichlet series). -/
theorem complexMellinPairing_receiver_eq {ε C κ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 ≤ C)
    (hκ : 0 ≤ κ) (hE : ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ) {s : ℂ}
    (hs : (1 + κ) / 2 < s.re) (hs1 : s.re < 1) (hζ : riemannZeta (s + ε) ≠ 0)
    (hne : s + ε ≠ 1) :
    complexMellinPairing (receiver ε) s =
      riemannZeta s / riemannZeta (s + ε) - (dampedDensity ε : ℂ) * riemannZeta s := by
  set c := pmPowerDampedRealWeight ε
  set m := ∑' d : ℕ, c d / d with hm_def
  have hm : m = dampedDensity ε := (BezoutValuationIncidence.dampedDensity_eq_tsum hε).symm
  have hrecv : receiver ε = weightCenteredPrefix c m := by rw [hm]
  have hA0 : receiver ε 0 = 0 := weightCenteredPrefix_zero _ _
  have hEA : ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, receiver ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      C * ((T : ℝ) + 1) ^ κ := fun T => by rw [receiver_energy_eq]; exact hE T
  have hΦ := ArithmeticCorrelationGeometry.differentiableOn_complexMellinPairing_of_energy_growth
    hA0 hC hκ hEA
  set U : Set ℂ := {s : ℂ | (1 + κ) / 2 < s.re ∧ s.re < 1} with hU_def
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt ((1 + κ) / 2)).inter (convex_halfSpace_re_lt 1)).isPreconnected
  set H : ℂ → ℂ := fun s => _root_.RHTower.zetaResidueUnit (s + ε) *
    (complexMellinPairing (receiver ε) s + (m : ℂ) * riemannZeta s) -
      (s + ε - 1) * riemannZeta s with hH
  have hζU : DifferentiableOn ℂ riemannZeta U := fun s hs =>
    (differentiableAt_riemannZeta fun h1 => by
      have := hs.2; rw [h1, Complex.one_re] at this; exact lt_irrefl _ this).differentiableWithinAt
  have hRU : DifferentiableOn ℂ (fun s : ℂ => _root_.RHTower.zetaResidueUnit (s + ε)) U :=
    fun s _ => ((_root_.RHTower.analyticAt_zetaResidueUnit (s + ε)).differentiableAt.comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hHd : DifferentiableOn ℂ H U :=
    (hRU.mul ((hΦ.mono fun s hs => hs.1).add (hζU.const_mul _))).sub
      (((differentiableOn_id.add_const _).sub_const _).mul hζU)
  have hHa : AnalyticOnNhd ℂ H U := hHd.analyticOnNhd hUo
  -- `H` vanishes on the real segment `(max((1+κ)/2, 1 − ε), 1)`
  set a₀ := max ((1 + κ) / 2) (1 - ε) with ha₀
  have ha₀1 : a₀ < 1 := max_lt (by linarith) (by linarith)
  have hzero : ∀ σ : ℝ, a₀ < σ → σ < 1 → H σ = 0 := by
    intro σ hσ hσ1
    have hσε : 1 < σ + ε := by linarith [le_max_right ((1 + κ) / 2) (1 - ε)]
    have hσ0 : 0 < σ := by linarith [le_max_left ((1 + κ) / 2) (1 - ε)]
    have hΦσ := TransHorizonIncidenceMechanics.complexMellinPairing_eq_zeta_mul (c := c)
      (θ := (1 - ε + σ) / 2) (by linarith) (by linarith) hσ1
      (ArithmeticCorrelationGeometry.summable_abs_pmPowerDampedRealWeight_mul (by linarith))
    have hCσ := ArithmeticCorrelationGeometry.ofReal_tsum_pmPowerDampedRealWeight (ε := ε) hσε
    have hne1 : ((σ : ℂ) + ε) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hζne : riemannZeta ((σ : ℂ) + ε) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
    rw [← hm_def, ← hrecv] at hΦσ
    simp only [hH]
    rw [ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hne1, hΦσ]
    push_cast at hCσ ⊢
    rw [hCσ]
    field_simp
    ring
  set σ₀ : ℝ := (a₀ + 1) / 2
  have hσ₀U : (σ₀ : ℂ) ∈ U := by
    simp only [hU_def, Set.mem_setOf_eq, Complex.ofReal_re, σ₀]
    constructor <;> linarith [le_max_left ((1 + κ) / 2) (1 - ε)]
  have hfreq : ∃ᶠ z in 𝓝[≠] (σ₀ : ℂ), H z = 0 := by
    have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[≠] σ₀) (𝓝[≠] (σ₀ : ℂ)) :=
      Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
        fun σ hσ => by simpa using hσ
    have hev : ∀ᶠ σ : ℝ in 𝓝[≠] σ₀, H (σ : ℂ) = 0 := by
      have h1 : ∀ᶠ σ in 𝓝 σ₀, a₀ < σ ∧ σ < 1 :=
        (lt_mem_nhds (by simp only [σ₀]; linarith)).and (gt_mem_nhds (by simp only [σ₀]; linarith))
      filter_upwards [nhdsWithin_le_nhds h1] with σ hσ
      exact hzero σ hσ.1 hσ.2
    exact hmap.frequently hev.frequently
  have hEq := hHa.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hσ₀U hfreq
  have hval := hEq (show s ∈ U from ⟨hs, hs1⟩)
  simp only [hH, Pi.zero_apply] at hval
  rw [ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hne, sub_eq_zero] at hval
  have hne' : s + ε - 1 ≠ 0 := sub_ne_zero.mpr hne
  have h' : riemannZeta (s + ε) * (complexMellinPairing (receiver ε) s + (m : ℂ) * riemannZeta s) =
      riemannZeta s := mul_left_cancel₀ hne' (by rw [← mul_assoc]; exact hval)
  rw [← hm, eq_sub_iff_add_eq, eq_div_iff hζ]
  linear_combination h'

/-! ### Translated zeros are simple poles of the symbol -/

/-- **The cofactor symbol has a simple pole at a translated simple zero.** Let `ρ` be a simple zero
of `ζ`, `s₀ = ρ − ε ∉ {0, 1}`, and `G(s) = (ζ(s)/ζ(s+ε) − m ζ(s))/s`. Near `s₀`, `G` is the polar
part `r/(s − s₀)`, `r = ζ(s₀)/(ζ′(ρ) s₀)`, plus a bounded function; on the punctured disc
`ζ(s + ε) ≠ 0`, `s + ε ≠ 1`, `s ∉ {0, 1}`. -/
theorem exists_cofactor_pole_bound {ε : ℂ} {ρ : ℂ} (m : ℂ) (hρ : riemannZeta ρ = 0)
    (hd : deriv riemannZeta ρ ≠ 0) (hρ1 : ρ ≠ 1) (hs0 : ρ - ε ≠ 0) (hs1 : ρ - ε ≠ 1) :
    ∃ η > 0, ∃ M : ℝ, ∀ s : ℂ, ‖s - (ρ - ε)‖ < η → s ≠ ρ - ε →
      riemannZeta (s + ε) ≠ 0 ∧ s + ε ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧
      ‖(riemannZeta s / riemannZeta (s + ε) - m * riemannZeta s) / s -
        riemannZeta (ρ - ε) / (deriv riemannZeta ρ * (ρ - ε)) / (s - (ρ - ε))‖ ≤ M := by
  set s₀ := ρ - ε with hs₀
  set Z : ℂ → ℂ := fun s => riemannZeta (s + ε) with hZ
  have hZs₀ : Z s₀ = 0 := by simp only [hZ, hs₀, sub_add_cancel, hρ]
  have hZdiff : ∀ s, s + ε ≠ 1 → DifferentiableAt ℂ Z s := fun s hs =>
    (differentiableAt_riemannZeta hs).comp s (differentiableAt_id.add_const ε)
  have hZd : DifferentiableAt ℂ Z s₀ := hZdiff s₀ (by simp only [hs₀, sub_add_cancel]; exact hρ1)
  have hderivZ : deriv Z s₀ = deriv riemannZeta ρ := by
    have h1 : HasDerivAt Z (deriv riemannZeta (s₀ + ε) * 1) s₀ :=
      ((differentiableAt_riemannZeta (by simp only [hs₀, sub_add_cancel]; exact hρ1)).hasDerivAt.comp
        s₀ ((hasDerivAt_id s₀).add_const ε))
    rw [h1.deriv, mul_one, hs₀, sub_add_cancel]
  set Z₁ := dslope Z s₀ with hZ₁
  have hZ₁s₀ : Z₁ s₀ = deriv riemannZeta ρ := by rw [hZ₁, dslope_same, hderivZ]
  have hfac : ∀ s, Z s = (s - s₀) * Z₁ s := fun s => by
    have := sub_smul_dslope Z s₀ s
    rw [hZs₀, sub_zero, smul_eq_mul] at this
    exact this.symm
  -- `Z₁` is differentiable at `s₀`
  have hS : {s : ℂ | s + ε ≠ 1} ∈ 𝓝 s₀ :=
    (isOpen_ne_fun (continuous_id.add continuous_const) continuous_const).mem_nhds
      (show (ρ - ε) + ε ≠ 1 by rw [sub_add_cancel]; exact hρ1)
  have hZ₁d : DifferentiableAt ℂ Z₁ s₀ :=
    ((Complex.differentiableOn_dslope hS).mpr fun s hs => (hZdiff s hs).differentiableWithinAt
      ).differentiableAt hS
  -- `F = ζ(s)/(s Z₁(s))` and its difference quotient
  set F : ℂ → ℂ := fun s => riemannZeta s / s / Z₁ s with hF
  have hFd : DifferentiableAt ℂ F s₀ :=
    (((differentiableAt_riemannZeta hs1).div differentiableAt_id hs0).div hZ₁d
      (by rw [hZ₁s₀]; exact hd))
  set K : ℂ → ℂ := fun s => dslope F s₀ s - m * (riemannZeta s / s) with hK
  have hKc : ContinuousAt K s₀ :=
    (continuousAt_dslope_same.mpr hFd).sub
      (continuousAt_const.mul (((differentiableAt_riemannZeta hs1).continuousAt).div
        continuousAt_id hs0))
  -- the open conditions near `s₀`
  have hev : ∀ᶠ s in 𝓝 s₀, dist (K s) (K s₀) < 1 ∧ Z₁ s ≠ 0 ∧ s + ε ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 := by
    refine (Metric.tendsto_nhds.mp hKc 1 one_pos).and ?_
    refine (hZ₁d.continuousAt.eventually_ne (by rw [hZ₁s₀]; exact hd)).and ?_
    exact Filter.Eventually.and hS ((eventually_ne_nhds hs0).and (eventually_ne_nhds hs1))
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨η, hη, ‖K s₀‖ + 1, fun s hs hne => ?_⟩
  obtain ⟨hK1, hZ₁ne, hsε, hsz, hs1'⟩ := hball (by rwa [dist_eq_norm])
  have hss₀ : s - s₀ ≠ 0 := sub_ne_zero.mpr hne
  have hZne : Z s ≠ 0 := by rw [hfac]; exact mul_ne_zero hss₀ hZ₁ne
  refine ⟨hZne, hsε, hsz, hs1', ?_⟩
  have hval : (riemannZeta s / riemannZeta (s + ε) - m * riemannZeta s) / s -
      riemannZeta s₀ / (deriv riemannZeta ρ * s₀) / (s - s₀) = K s := by
    simp only [hK]
    rw [dslope_of_ne _ hne, slope_def_field, hF]
    simp only
    rw [hZ₁s₀]
    have hZs : riemannZeta (s + ε) = (s - s₀) * Z₁ s := hfac s
    rw [hZs]
    field_simp
    ring
  rw [hval]
  have := norm_sub_norm_le (K s) (K s₀)
  rw [dist_eq_norm] at hK1
  linarith


/-! ### The atoms of the Abel escape state of `ζ` -/

/-- **A dominant simple zero is an atom of the Abel escape state.** Let `ρ` be a simple zero of
`ζ` with `½ + ε < Re ρ < 1` that is dominant for the receiver at damping `ε` — the energy is
`O((T+1)^κ)` for every `κ > 2(Re ρ − ε) − 1` — and put `θ = Re ρ − ε − ½`. Then on a window around
`Im ρ` the scaled spectral measure of the lines `Re s = θ + e` converges to the atom
`π ‖r‖² δ_{Im ρ}`, `r = ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))`:
`e ∫ ‖G_ε(θ + e + iy)‖² w(y) dy → π ‖r‖² w(Im ρ)` for every Lipschitz bounded weight. The atom
vanishes exactly when `ρ` is cancelled, `ζ(ρ − ε) = 0`. No explicit formula enters. -/
theorem tendsto_receiver_window_atom {ε : ℝ} (hε : 0 < ε) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hd : deriv riemannZeta ρ ≠ 0) (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1)
    (hdom : ∀ κ : ℝ, 2 * (ρ.re - ε) - 1 < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (w : ℝ → ℝ) (L W : ℝ), 0 ≤ L → Continuous w →
      (∀ y, |w y - w ρ.im| ≤ L * |y - ρ.im|) → (∀ y, |w y| ≤ W) →
      Tendsto (fun e : ℝ => e * ∫ y in (ρ.im - δ)..(ρ.im + δ),
          ‖lineSymbol (receiverLogProfile ε) (ρ.re - ε - 1 / 2 + e) y‖ ^ 2 * w y) (𝓝[>] 0)
        (𝓝 (Real.pi * ‖riemannZeta (ρ - ε) / (deriv riemannZeta ρ * (ρ - ε))‖ ^ 2 *
          w ρ.im)) := by
  set θ := ρ.re - ε - 1 / 2 with hθ
  have hθ0 : 0 < θ := by linarith
  have hε1 : ε < 1 := by linarith
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hre1; exact lt_irrefl _ hre1
  have hs0 : ρ - (ε : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs1 : ρ - (ε : ℂ) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  obtain ⟨η, hη, M, hpole⟩ := exists_cofactor_pole_bound (ε := (ε : ℂ)) (dampedDensity ε : ℂ)
    hρ hd hρ1 hs0 hs1
  set δ₀ := min (η / 2) ((1 - ρ.re) / 2) with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by linarith) (by linarith)
  refine ⟨δ₀, hδ₀0, fun δ hδ0 hδδ₀ w L W hL hw hwL hwW => ?_⟩
  -- the damped profiles at `c = θ + e` are `L¹ ∩ L²` and their symbol is `G_ε`
  have hdata : ∀ e ∈ Ioo (0 : ℝ) δ, Integrable (dampedProfile (receiverLogProfile ε) (θ + e)) ∧
      ∀ y : ℝ, y ∈ Icc (ρ.im - δ) (ρ.im + δ) →
        ‖lineSymbol (receiverLogProfile ε) (θ + e) y -
          riemannZeta (ρ - ε) / (deriv riemannZeta ρ * (ρ - ε)) /
            ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)‖ ≤ M := by
    intro e he
    obtain ⟨C, hC, hE⟩ := hdom (2 * θ + e) (by rw [hθ]; linarith [he.1])
    have hκ : 0 ≤ 2 * θ + e := by linarith [he.1]
    have hc : (2 * θ + e) / 2 < θ + e := by linarith [he.1]
    refine ⟨(integrable_and_memLp_dampedProfile_receiver hC hκ hE hc).1, fun y hy => ?_⟩
    set s : ℂ := ((θ + e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hs
    have hss₀ : s - (ρ - ε) = (e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hs, hθ]; ring
    have hnorm : ‖s - (ρ - ε)‖ < η := by
      rw [hss₀]
      calc ‖(e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I‖ ≤ ‖(e : ℂ)‖ + ‖((y - ρ.im : ℝ) : ℂ) * I‖ :=
            norm_add_le _ _
        _ = |e| + |y - ρ.im| := by
            simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ < η := by
            have h1 : |e| < δ := by rw [abs_of_pos he.1]; exact he.2
            have h2 : |y - ρ.im| ≤ δ := abs_sub_le_iff.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
            linarith [min_le_left (η / 2) ((1 - ρ.re) / 2)]
    have hne : s ≠ ρ - ε := fun h => by
      have := congrArg Complex.re (show s - (ρ - ε) = 0 by rw [h, sub_self])
      rw [hss₀] at this; simp at this; linarith [he.1]
    obtain ⟨hζ, hsε, -, -, hbound⟩ := hpole s hnorm hne
    have hsre : s.re = θ + e + 1 / 2 := by simp [hs]
    have hΦ := complexMellinPairing_receiver_eq hε hε1 hC hκ hE (s := s)
      (by rw [hsre]; linarith [he.1]) (by
        rw [hsre, hθ]; linarith [he.2, min_le_right (η / 2) ((1 - ρ.re) / 2)]) hζ hsε
    rw [lineSymbol_receiver_eq hC hκ hE hc y, show ((θ + e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I = s
      from rfl, hΦ, ← hss₀]
    exact hbound
  exact tendsto_window_atom (S := fun e y => lineSymbol (receiverLogProfile ε) (θ + e) y) hδ0
    (le_trans (norm_nonneg _) (hdata (δ / 2) ⟨by linarith, by linarith⟩ |>.2 ρ.im
      ⟨by linarith, by linarith⟩)) hL
    (fun e he => (continuous_lineSymbol (hdata e he).1).continuousOn)
    (fun e he y hy => (hdata e he).2 y hy) hw hwL hwW


/-- **A dominant uncancelled zero forces Abel escape at rate `1/e`.** Under the hypotheses of the
atom law with `ζ(ρ − ε) ≠ 0`, the Abel energy `A_{θ+e}(0, 0)` of the receiver diverges as `e ↓ 0`:
`e · A_{θ+e}(0, 0)` stays above a positive multiple of the atom. -/
theorem tendsto_receiver_abelGram_atTop {ε : ℝ} (hε : 0 < ε) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hd : deriv riemannZeta ρ ≠ 0) (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1)
    (hcan : riemannZeta (ρ - ε) ≠ 0)
    (hdom : ∀ κ : ℝ, 2 * (ρ.re - ε) - 1 < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ) :
    Tendsto (fun e : ℝ => abelGram (receiverLogProfile ε) (ρ.re - ε - 1 / 2 + e) 0 0) (𝓝[>] 0)
      atTop := by
  set θ := ρ.re - ε - 1 / 2 with hθ
  set r := riemannZeta (ρ - ε) / (deriv riemannZeta ρ * (ρ - ε)) with hr
  have hs0 : ρ - (ε : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hrpos : 0 < ‖r‖ ^ 2 := by
    have : r ≠ 0 := div_ne_zero hcan (mul_ne_zero hd hs0)
    positivity
  obtain ⟨δ, hδ, hatom⟩ := tendsto_receiver_window_atom hε hρ hd hre hre1 hdom
  have h1 := hatom δ hδ le_rfl (fun _ => 1) 0 1 le_rfl continuous_const (fun y => by simp)
    (fun y => by simp)
  simp only [mul_one] at h1
  -- eventually the window mass exceeds half the atom
  have hev := h1.eventually (lt_mem_nhds (show Real.pi * ‖r‖ ^ 2 / 2 < Real.pi * ‖r‖ ^ 2 by
    have := Real.pi_pos; nlinarith))
  -- and the window mass is at most the total mass `2π A(0,0)`
  have hlow : ∀ᶠ e in 𝓝[>] (0 : ℝ), ‖r‖ ^ 2 / 4 / e ≤
      abelGram (receiverLogProfile ε) (θ + e) 0 0 := by
    filter_upwards [hev, self_mem_nhdsWithin] with e he he0
    have he0' : (0 : ℝ) < e := he0
    obtain ⟨C, hC, hE⟩ := hdom (2 * θ + e) (by rw [hθ]; linarith)
    obtain ⟨hI, hL⟩ := integrable_and_memLp_dampedProfile_receiver hC (by linarith) hE
      (show (2 * θ + e) / 2 < θ + e by linarith)
    have htot := integral_norm_sq_lineSymbol hI hL
    have hwin : (∫ y in (ρ.im - δ)..(ρ.im + δ),
        ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) ≤
        ∫ y, ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_le_integral
        (_root_.RHTower.integrable_norm_sq_laplaceBoundary hI.ofReal hL.ofReal)
        (Eventually.of_forall fun y => by positivity)
    rw [htot] at hwin
    rw [div_le_iff₀ he0']
    have hpi := Real.pi_pos
    nlinarith
  have hinv : Tendsto (fun e : ℝ => ‖r‖ ^ 2 / 4 / e) (𝓝[>] 0) atTop := by
    simp only [div_eq_mul_inv]
    exact tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  exact tendsto_atTop_mono' _ hlow hinv

/-- **A zero-free segment of the abscissa line carries no escape.** Let the receiver at damping
`ε` have energy `O((T+1)^κ)` for every `κ > 2θ`, let it escape at `θ` (the Abel energy diverges),
and let `ζ(s + ε)` have no zero on the segment `Re s = θ + ½`, `y₁ ≤ Im s ≤ y₂`. Then the share of
that segment in the spectral measure of the lines `Re s = θ + e` tends to zero: the escape is
carried by translated zeros on the abscissa line or by infinite height. -/
theorem tendsto_receiver_window_share_zero {ε θ y₁ y₂ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ1 : θ + 1 / 2 + ε < 1) (hy : y₁ ≤ y₂)
    (hdom : ∀ κ : ℝ, 2 * θ < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ)
    (hfree : ∀ y ∈ Icc y₁ y₂, riemannZeta (((θ + 1 / 2 + ε : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hesc : Tendsto (fun e : ℝ => abelGram (receiverLogProfile ε) (θ + e) 0 0) (𝓝[>] 0) atTop) :
    Tendsto (fun e : ℝ => (∫ y in y₁..y₂, ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) /
      ∫ y, ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hε1 : ε < 1 := by linarith
  set G : ℂ → ℂ := fun s =>
    (riemannZeta s / riemannZeta (s + ε) - (dampedDensity ε : ℂ) * riemannZeta s) / s with hG
  -- the open set where `G` is continuous
  set O : Set ℂ := {s | s + ε ≠ 1 ∧ s ≠ 1 ∧ s ≠ 0} ∩ (fun s => riemannZeta (s + ε)) ⁻¹' {0}ᶜ
    with hO
  have hOopen : IsOpen O := by
    refine ContinuousOn.isOpen_inter_preimage ?_ ?_ isOpen_compl_singleton
    · intro s hs
      exact ((differentiableAt_riemannZeta hs.1).comp s
        (differentiableAt_id.add_const (ε : ℂ))).continuousAt.continuousWithinAt
    · refine ((isOpen_ne_fun (continuous_id.add continuous_const) continuous_const).inter
        ((isOpen_ne_fun continuous_id continuous_const).inter
          (isOpen_ne_fun continuous_id continuous_const)))
  have hGc : ContinuousOn G O := by
    intro s hs
    have hζ1 := differentiableAt_riemannZeta hs.1.2.1
    have hζε := (differentiableAt_riemannZeta hs.1.1).comp s (differentiableAt_id.add_const (ε : ℂ))
    exact (((hζ1.div hζε hs.2).sub (hζ1.const_mul _)).div differentiableAt_id
      hs.1.2.2).continuousAt.continuousWithinAt
  -- the segment and a box around it
  set seg : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * I with hseg
  have hsegc : Continuous seg := by fun_prop
  set K₀ := seg '' (Icc (θ + 1 / 2) (θ + 1 / 2) ×ˢ Icc y₁ y₂) with hK₀
  have hK₀c : IsCompact K₀ := (isCompact_Icc.prod isCompact_Icc).image hsegc
  have hK₀O : K₀ ⊆ O := by
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy'⟩, rfl⟩
    have hx' : x = θ + 1 / 2 := le_antisymm hx.2 hx.1
    subst hx'
    refine ⟨⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ?_⟩
    · have := congrArg Complex.re h; simp [hseg] at this; linarith
    · have := congrArg Complex.re h; simp [hseg] at this; linarith
    · have := congrArg Complex.re h; simp [hseg] at this; linarith
    · simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, hseg]
      have := hfree y hy'
      push_cast at this ⊢
      rwa [show ((θ : ℂ) + 1 / 2) + (y : ℂ) * I + ε = (θ : ℂ) + 1 / 2 + ε + (y : ℂ) * I by ring]
  obtain ⟨δ₀, hδ₀, hthick⟩ := hK₀c.exists_thickening_subset_open hOopen hK₀O
  set B := seg '' (Icc (θ + 1 / 2) (θ + 1 / 2 + δ₀ / 2) ×ˢ Icc y₁ y₂) with hB
  have hBc : IsCompact B := (isCompact_Icc.prod isCompact_Icc).image hsegc
  have hBO : B ⊆ O := by
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy'⟩, rfl⟩
    refine hthick (Metric.mem_thickening_iff.mpr ⟨seg (θ + 1 / 2, y),
      ⟨(θ + 1 / 2, y), ⟨⟨le_rfl, le_rfl⟩, hy'⟩, rfl⟩, ?_⟩)
    rw [dist_eq_norm]
    have : seg (x, y) - seg (θ + 1 / 2, y) = ((x - (θ + 1 / 2) : ℝ) : ℂ) := by
      simp only [hseg]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2]
  obtain ⟨B₀, hB₀⟩ := hBc.exists_bound_of_continuousOn (hGc.mono hBO)
  -- on the box the line symbol is `G`
  set δ := min (δ₀ / 2) ((1 - (θ + 1 / 2 + ε)) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  refine tendsto_lineSymbol_window_share_zero (B := B₀) hδ0 (fun e he => ?_) (fun e he => ?_)
    (fun e he y hyI => ?_) hesc
  · obtain ⟨C, hC, hE⟩ := hdom (2 * θ + e) (by linarith [he.1])
    exact (integrable_and_memLp_dampedProfile_receiver hC (by linarith [he.1]) hE
      (show (2 * θ + e) / 2 < θ + e by linarith [he.1])).1
  · obtain ⟨C, hC, hE⟩ := hdom (2 * θ + e) (by linarith [he.1])
    exact (integrable_and_memLp_dampedProfile_receiver hC (by linarith [he.1]) hE
      (show (2 * θ + e) / 2 < θ + e by linarith [he.1])).2
  · rw [uIcc_of_le hy] at hyI
    obtain ⟨C, hC, hE⟩ := hdom (2 * θ + e) (by linarith [he.1])
    have hκ : 0 ≤ 2 * θ + e := by linarith [he.1]
    have hc : (2 * θ + e) / 2 < θ + e := by linarith [he.1]
    have hsB : seg (θ + e + 1 / 2, y) ∈ B :=
      ⟨(θ + e + 1 / 2, y), ⟨⟨by linarith [he.1], by
        linarith [he.2, min_le_left (δ₀ / 2) ((1 - (θ + 1 / 2 + ε)) / 2)]⟩, hyI⟩, rfl⟩
    have hsO := hBO hsB
    have hsre : (seg (θ + e + 1 / 2, y)).re = θ + e + 1 / 2 := by simp [hseg]
    have hΦ := complexMellinPairing_receiver_eq hε hε1 hC hκ hE (s := seg (θ + e + 1 / 2, y))
      (by rw [hsre]; linarith [he.1]) (by
        rw [hsre]; linarith [he.2, min_le_right (δ₀ / 2) ((1 - (θ + 1 / 2 + ε)) / 2)])
      hsO.2 hsO.1.1
    rw [lineSymbol_receiver_eq hC hκ hE hc y]
    have hseq : ((θ + e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I = seg (θ + e + 1 / 2, y) := rfl
    rw [hseq, hΦ]
    exact hB₀ _ hsB

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
