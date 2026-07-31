import GaloisForLFunctions.RHTower.SquaredXiChebyshevWindow
import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory
import GaloisForLFunctions.RHTower.BoseZipfCumulants
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# The Chebyshev--Stieltjes measure

Chebyshev's `psi(x) = sum_{m <= x} Lambda m`, read as a real-variable step function, is monotone and
right-continuous, so it carries a Lebesgue--Stieltjes measure.  That measure is exactly the atomic
measure with mass `Lambda m` at each natural `m`:

`d psi = sum_m Lambda m * delta_m`.

Consequently every Chebyshev--Stieltjes integral is the corresponding von Mangoldt series.  This is
the measure-theoretic content of the identity that turns the radial reverse-Bessel kernel into the
sign-aligned von Mangoldt jet.
-/

open MeasureTheory Set ArithmeticFunction

namespace RHTower

noncomputable section

/-! ### The real-variable Chebyshev step function -/

/-- Chebyshev's `psi` as a real-variable step function. -/
def chebyshevPsiReal (x : ℝ) : ℝ := chebyshevPsi ⌊x⌋₊

theorem chebyshevPsi_eq_sum_Ioc (k : ℕ) :
    chebyshevPsi k = ∑ m ∈ Finset.Ioc 0 k, (vonMangoldt m : ℝ) := by
  rw [chebyshevPsi]
  congr 1

theorem chebyshevPsi_sub {a b : ℕ} (hab : a ≤ b) :
    chebyshevPsi b - chebyshevPsi a = ∑ m ∈ Finset.Ioc a b, (vonMangoldt m : ℝ) := by
  rw [chebyshevPsi_eq_sum_Ioc, chebyshevPsi_eq_sum_Ioc,
    ← Finset.sum_Ioc_consecutive (fun m : ℕ => (vonMangoldt m : ℝ)) (Nat.zero_le a) hab]
  ring

theorem chebyshevPsi_mono : Monotone chebyshevPsi := by
  intro a b hab
  have hsub := chebyshevPsi_sub hab
  have hnn : (0:ℝ) ≤ ∑ m ∈ Finset.Ioc a b, (vonMangoldt m : ℝ) :=
    Finset.sum_nonneg (fun m _ => vonMangoldt_nonneg)
  linarith

theorem chebyshevPsiReal_mono : Monotone chebyshevPsiReal :=
  fun _ _ hab => chebyshevPsi_mono (Nat.floor_mono hab)

theorem lt_floor_add_one_real (x : ℝ) : x < (⌊x⌋₊ : ℝ) + 1 := by
  rcases le_or_gt 0 x with hx | hx
  · exact Nat.lt_floor_add_one x
  · rw [Nat.floor_of_nonpos hx.le]
    push_cast
    linarith

theorem chebyshevPsiReal_const_on_Ico (x : ℝ) :
    ∀ y ∈ Ico x ((⌊x⌋₊ : ℝ) + 1), chebyshevPsiReal y = chebyshevPsiReal x := by
  intro y hy
  rw [chebyshevPsiReal, chebyshevPsiReal]
  congr 1
  rcases le_or_gt 0 y with hy0 | hy0
  · have h1 : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hy.1
    have h2 : ⌊y⌋₊ < ⌊x⌋₊ + 1 := by
      refine (Nat.floor_lt hy0).mpr ?_
      push_cast
      exact hy.2
    omega
  · have hx0 : x < 0 := lt_of_le_of_lt hy.1 hy0
    rw [Nat.floor_of_nonpos hx0.le, Nat.floor_of_nonpos hy0.le]

theorem chebyshevPsiReal_rightContinuous (x : ℝ) :
    ContinuousWithinAt chebyshevPsiReal (Ici x) x := by
  have hmem : Ico x ((⌊x⌋₊ : ℝ) + 1) ∈ nhdsWithin x (Ici x) :=
    Ico_mem_nhdsGE (lt_floor_add_one_real x)
  refine ContinuousWithinAt.congr_of_eventuallyEq
    (f := fun _ : ℝ => chebyshevPsiReal x) continuousWithinAt_const ?_ rfl
  filter_upwards [hmem] with y hy using chebyshevPsiReal_const_on_Ico x y hy

/-- Chebyshev's `psi` as a Stieltjes function. -/
def chebyshevPsiStieltjes : StieltjesFunction ℝ where
  toFun := chebyshevPsiReal
  mono' := chebyshevPsiReal_mono
  right_continuous' := chebyshevPsiReal_rightContinuous

@[simp] theorem chebyshevPsiStieltjes_apply (x : ℝ) :
    chebyshevPsiStieltjes x = chebyshevPsiReal x := rfl

/-! ### The atomic von Mangoldt measure -/

/-- The atomic measure with mass `Lambda m` at each natural `m`. -/
def vonMangoldtAtomMeasure : Measure ℝ :=
  Measure.sum (fun m : ℕ => ENNReal.ofReal (vonMangoldt m) • Measure.dirac (m : ℝ))

theorem vonMangoldtAtomMeasure_Ioc {a b : ℝ} (hab : a < b) :
    vonMangoldtAtomMeasure (Ioc a b)
      = ENNReal.ofReal (chebyshevPsiReal b - chebyshevPsiReal a) := by
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab.le
  have hterm : ∀ m : ℕ,
      (ENNReal.ofReal (vonMangoldt m) • Measure.dirac ((m : ℝ))) (Ioc a b)
        = if (m : ℝ) ∈ Ioc a b then ENNReal.ofReal (vonMangoldt m) else 0 := by
    intro m
    rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ioc, smul_eq_mul]
    by_cases hm : (m : ℝ) ∈ Ioc a b <;> simp [hm]
  have hsupp : ∀ m : ℕ, m ∉ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ →
      (if (m : ℝ) ∈ Ioc a b then ENNReal.ofReal (vonMangoldt m) else 0) = 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp
    · by_cases hmem : (m : ℝ) ∈ Ioc a b
      · exfalso
        have hmb : m ≤ ⌊b⌋₊ := Nat.le_floor hmem.2
        have hma : ⌊a⌋₊ < m := by
          rcases le_or_gt 0 a with ha0 | ha0
          · exact (Nat.floor_lt ha0).mpr hmem.1
          · have h0 : ⌊a⌋₊ = 0 := Nat.floor_of_nonpos ha0.le
            omega
        exact hm (Finset.mem_Ioc.mpr ⟨hma, hmb⟩)
      · simp [hmem]
  have hmemIoc : ∀ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (m : ℝ) ∈ Ioc a b := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hm
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) h1
    have hbpos : 0 < ⌊b⌋₊ := lt_of_lt_of_le hmpos h2
    have hb1 : (1:ℝ) ≤ b := Nat.floor_pos.mp hbpos
    refine ⟨?_, ?_⟩
    · rcases le_or_gt 0 a with ha0 | ha0
      · exact (Nat.floor_lt ha0).mp h1
      · exact lt_of_lt_of_le ha0 (Nat.cast_nonneg m)
    · exact le_trans (by exact_mod_cast h2) (Nat.floor_le (by linarith))
  rw [vonMangoldtAtomMeasure, Measure.sum_apply _ measurableSet_Ioc]
  simp only [hterm]
  rw [tsum_eq_sum hsupp,
    Finset.sum_congr rfl (fun m hm => by rw [if_pos (hmemIoc m hm)]),
    ← ENNReal.ofReal_sum_of_nonneg (fun m _ => vonMangoldt_nonneg),
    chebyshevPsiReal, chebyshevPsiReal, chebyshevPsi_sub hfloor]

/-- **The Chebyshev--Stieltjes measure is the von Mangoldt atomic measure.** -/
theorem chebyshevPsiStieltjes_measure_eq :
    chebyshevPsiStieltjes.measure = vonMangoldtAtomMeasure := by
  refine Measure.ext_of_Ioc _ _ (fun a b hab => ?_)
  rw [StieltjesFunction.measure_Ioc, vonMangoldtAtomMeasure_Ioc hab,
    chebyshevPsiStieltjes_apply, chebyshevPsiStieltjes_apply]

/-! ### Chebyshev--Stieltjes integrals are von Mangoldt series -/

/-- **Equation (3), abstract form.**  A Chebyshev--Stieltjes integral is the von Mangoldt series of
the integrand at the naturals. -/
theorem integral_chebyshevPsiStieltjes {f : ℝ → ℝ}
    (hf : Integrable f chebyshevPsiStieltjes.measure) :
    ∫ x, f x ∂chebyshevPsiStieltjes.measure = ∑' m : ℕ, (vonMangoldt m : ℝ) * f m := by
  rw [chebyshevPsiStieltjes_measure_eq] at hf ⊢
  rw [vonMangoldtAtomMeasure] at hf ⊢
  rw [integral_sum_measure hf]
  refine tsum_congr (fun m => ?_)
  rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal vonMangoldt_nonneg]

theorem integrable_chebyshevPsiStieltjes {f : ℝ → ℝ}
    (hsum : Summable (fun m : ℕ => (vonMangoldt m : ℝ) * ‖f (m : ℝ)‖)) :
    Integrable f chebyshevPsiStieltjes.measure := by
  rw [chebyshevPsiStieltjes_measure_eq, vonMangoldtAtomMeasure]
  refine integrable_sum_measure_iff.mpr ⟨fun m => ?_, ?_⟩
  · by_cases hz : ENNReal.ofReal (vonMangoldt m) = 0
    · rw [hz, zero_smul]
      exact integrable_zero_measure
    · refine (integrable_smul_measure hz (by simp)).mpr ?_
      exact integrable_dirac (by simp)
  · refine hsum.congr (fun m => ?_)
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal vonMangoldt_nonneg]

/-- The von Mangoldt weight of the radial kernel is a finite combination of log-weighted von
Mangoldt series, hence summable above the Euler abscissa. -/
theorem vonMangoldt_mul_norm_radialBesselKernel {n : ℕ} {s : ℝ} (hs : 1 < s) (m : ℕ) :
    (vonMangoldt m : ℝ) * ‖radialBesselKernel n s (m : ℝ)‖
      = ∑ j ∈ Finset.range (n + 1),
          ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
            ((vonMangoldt m : ℝ) * Real.log m ^ j * (m : ℝ) ^ (-s)) := by
  have hw : (0:ℝ) < s - 1 / 2 := by linarith
  have hlog : (0:ℝ) ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  have hrpow : (0:ℝ) ≤ ((m : ℝ)) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hsumnn : (0:ℝ) ≤ ∑ j ∈ Finset.range (n + 1),
      (squaredRadialJetWeight n j : ℝ) * ((s - 1 / 2) * Real.log (m : ℝ)) ^ j := by
    refine Finset.sum_nonneg (fun j _ => ?_)
    have hb : (0:ℝ) ≤ (squaredRadialJetWeight n j : ℝ) := Nat.cast_nonneg _
    have : (0:ℝ) ≤ ((s - 1 / 2) * Real.log (m : ℝ)) ^ j := by positivity
    positivity
  rw [radialBesselKernel, Real.norm_eq_abs, abs_of_nonneg (by positivity), Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_pow]
  ring

theorem summable_vonMangoldt_mul_norm_radialBesselKernel {n : ℕ} {s : ℝ} (hs : 1 < s) :
    Summable (fun m : ℕ => (vonMangoldt m : ℝ) * ‖radialBesselKernel n s (m : ℝ)‖) := by
  have hterms : ∀ j ∈ Finset.range (n + 1), Summable (fun m : ℕ =>
      ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
        ((vonMangoldt m : ℝ) * Real.log m ^ j * (m : ℝ) ^ (-s))) :=
    fun j _ => (summable_vonMangoldtLogTerm hs j).mul_left _
  have h := summable_sum hterms
  refine h.congr (fun m => ?_)
  exact (vonMangoldt_mul_norm_radialBesselKernel hs m).symm

/-- **Equation (3).**  The Chebyshev--Stieltjes integral of the radial reverse-Bessel kernel is the
sign-aligned von Mangoldt jet. -/
theorem integral_radialBesselKernel_chebyshev {n : ℕ} {s : ℝ} (hs : 1 < s) :
    ∫ x, radialBesselKernel n s x ∂chebyshevPsiStieltjes.measure
      = ∑' m : ℕ, (vonMangoldt m : ℝ) * radialBesselKernel n s (m : ℝ) :=
  integral_chebyshevPsiStieltjes
    (integrable_chebyshevPsiStieltjes
      (summable_vonMangoldt_mul_norm_radialBesselKernel hs))

/-- **Equation (4).**  The completed radial discrepancy: the Lebesgue jet minus the
Chebyshev--Stieltjes jet, both in closed form. -/
theorem integral_radialBesselKernel_discrepancy {n : ℕ} {s : ℝ} (hs : 1 < s) :
    (∫ x in Set.Ioi (1:ℝ), radialBesselKernel n s x)
        - ∫ x, radialBesselKernel n s x ∂chebyshevPsiStieltjes.measure
      = (∑ j ∈ Finset.range (n + 1),
          (squaredRadialJetWeight n j : ℝ) * (j.factorial : ℝ) *
            (s - 1 / 2) ^ j / (s - 1) ^ (j + 1))
        - ∑' m : ℕ, (vonMangoldt m : ℝ) * radialBesselKernel n s (m : ℝ) := by
  rw [integral_radialBesselKernel hs, integral_radialBesselKernel_chebyshev hs]

end

end RHTower
