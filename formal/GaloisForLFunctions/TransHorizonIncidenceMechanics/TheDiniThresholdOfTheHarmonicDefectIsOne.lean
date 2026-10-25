import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheDiniLawOfCompletelyMonotoneAmplitudeDefects

/-!
# The Dini threshold of the harmonic defect is one

Take the harmonic defect data `w_k = 1/((k+1)(k+2))`, `s_k = e^{-(k+1)}` (`harmonicWeight`,
`harmonicShift`), so that `g(p) = Σ_k w_k p^{-e^{-(k+1)}}` and

`f_c(p) = (1 − c g(p)) cos(t₀ log p)`,  `0 ≤ c ≤ 2`.

* **The profile is doubly logarithmic.** `log log(1/ρ) − 2 ≤ Λ(ρ) ≤ log log(1/ρ) + 3` on
  `(0, e^{-1}]` (`log_log_sub_two_le_defectProfile_harmonic`, `defectProfile_harmonic_le`), so the
  Dini density is `≍ 1/(ρ (log 1/ρ)^c)`.
* **The threshold.** The Dini density is integrable on `(0, 1]` iff `c > 1`
  (`integrableOn_diniDensity_harmonic_iff`), and with the Dini law the half-damped receiver of `f_c`
  is paid iff `c > 1` or `ζ(1/2 + it₀) = 0` (`receiverBounded_harmonicDefect_iff`).
* **The mass diverges.** For every admissible defect with unbounded profile and `c > 0`, the
  critical-line mass `Σ_p |f(p) − cos(t₀ log p)|/p` is infinite
  (`not_summable_criticalLineMass_defect`); in particular for the harmonic defect at every `c > 0`
  (`not_summable_criticalLineMass_harmonic`). The phase boundary `c = 1` lies inside the regime of
  divergent mass: it is decided by the Dini integral of the profile, not by the mass.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The harmonic defect -/

/-- The harmonic weights `w_k = 1/((k+1)(k+2))`. -/
def harmonicWeight (k : ℕ) : ℝ := 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))

/-- The exponential exponents `s_k = e^{-(k+1)}`. -/
def harmonicShift (k : ℕ) : ℝ := Real.exp (-((k : ℝ) + 1))

theorem harmonicWeight_nonneg (k : ℕ) : 0 ≤ harmonicWeight k := by
  unfold harmonicWeight; positivity

/-- The telescoping partial sums `Σ_{k<n} w_{k+N} = 1/(N+1) − 1/(N+n+1)`. -/
theorem sum_range_harmonicWeight_add (N n : ℕ) :
    ∑ k ∈ Finset.range n, harmonicWeight (k + N) =
      1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [harmonicWeight]
    push_cast
    field_simp
    ring

theorem sum_range_harmonicWeight_le (N n : ℕ) :
    ∑ k ∈ Finset.range n, harmonicWeight (k + N) ≤ 1 / ((N : ℝ) + 1) := by
  rw [sum_range_harmonicWeight_add]
  have : 0 ≤ 1 / ((N : ℝ) + n + 1) := by positivity
  linarith

theorem tsum_harmonicWeight_add_le (N : ℕ) :
    ∑' k, harmonicWeight (k + N) ≤ 1 / ((N : ℝ) + 1) :=
  Real.tsum_le_of_sum_range_le (fun _ => harmonicWeight_nonneg _)
    (sum_range_harmonicWeight_le N)

theorem tsum_harmonicWeight_le : ∑' k, harmonicWeight k ≤ 1 := by
  have h := tsum_harmonicWeight_add_le 0
  simp only [add_zero, Nat.cast_zero, zero_add, div_one] at h
  exact h

theorem admissibleDefect_harmonic : AdmissibleDefect harmonicWeight harmonicShift where
  nonneg := harmonicWeight_nonneg
  summable := by
    refine summable_of_sum_range_le harmonicWeight_nonneg (c := 1) fun n => ?_
    have h := sum_range_harmonicWeight_le 0 n
    simp only [add_zero, Nat.cast_zero, zero_add, div_one] at h
    exact h
  pos := fun k => Real.exp_pos _
  le_half k := by
    have h1 : Real.exp (-((k : ℝ) + 1)) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    exact h1.trans Real.exp_neg_one_lt_half.le

/-! ### Two harmonic-logarithm comparisons -/

/-- `log(N + 2) − log 2 ≤ Σ_{k<N} 1/(k+2)`. -/
theorem log_sub_log_two_le_sum_inv (N : ℕ) :
    Real.log ((N : ℝ) + 2) - Real.log 2 ≤ ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hstep : Real.log ((n : ℝ) + 3) - Real.log ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
      field_simp; ring
    push_cast
    rw [show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
    linarith

/-- `Σ_{k<N} 1/(k+2) ≤ log(N + 1)`. -/
theorem sum_inv_le_log (N : ℕ) :
    ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2) ≤ Real.log ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hstep : 1 / ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      refine le_trans (le_of_eq ?_) (Real.one_sub_inv_le_log_of_pos (by positivity))
      field_simp; ring
    push_cast
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    linarith

/-! ### The profile is doubly logarithmic -/

theorem harmonicShift_pos (k : ℕ) : 0 < harmonicShift k := Real.exp_pos _

theorem log_harmonicShift (k : ℕ) : Real.log (harmonicShift k) = -((k : ℝ) + 1) := by
  rw [harmonicShift, Real.log_exp]

theorem log_inv_eq_neg_log {ρ : ℝ} : Real.log ρ⁻¹ = -Real.log ρ := Real.log_inv ρ

theorem one_le_log_inv {ρ : ℝ} (hρ : 0 < ρ) (hρe : ρ ≤ Real.exp (-1)) : 1 ≤ Real.log ρ⁻¹ := by
  have := Real.log_le_log hρ hρe
  rw [Real.log_exp] at this
  rw [Real.log_inv]; linarith

theorem log_inv_harmonicShift_add_nonneg {ρ : ℝ} (hρ : 0 < ρ) (hρe : ρ ≤ Real.exp (-1))
    (k : ℕ) : 0 ≤ Real.log (harmonicShift k + ρ)⁻¹ := by
  have hk := admissibleDefect_harmonic.le_half k
  have he := Real.exp_neg_one_lt_half
  rw [Real.log_inv, neg_nonneg]
  exact Real.log_nonpos (by linarith [harmonicShift_pos k]) (by linarith)

/-- **The lower profile bound.** `log log(1/ρ) − 2 ≤ Λ(ρ)` on `(0, e^{-1}]`. -/
theorem log_log_sub_two_le_defectProfile_harmonic {ρ : ℝ} (hρ : 0 < ρ)
    (hρe : ρ ≤ Real.exp (-1)) :
    Real.log (Real.log ρ⁻¹) - 2 ≤ defectProfile harmonicWeight harmonicShift ρ := by
  set L := Real.log ρ⁻¹
  have hL1 : 1 ≤ L := one_le_log_inv hρ hρe
  set N := ⌊L⌋₊
  have hNL : (N : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hLN : L < N + 1 := Nat.lt_floor_add_one L
  have hd := admissibleDefect_harmonic
  have hsum := (summable_defectProfile hd hρ).sum_le_tsum (Finset.range N) (fun k _ =>
    mul_nonneg (harmonicWeight_nonneg k) (log_inv_harmonicShift_add_nonneg hρ hρe k))
  have hk : ∀ k ∈ Finset.range N, harmonicWeight k * ((k : ℝ) + 1 - Real.log 2) ≤
      harmonicWeight k * Real.log (harmonicShift k + ρ)⁻¹ := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk1 : (k : ℝ) + 1 ≤ L := by
      have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
      push_cast at this; linarith
    have hsρ : ρ ≤ harmonicShift k := by
      have hρL : ρ = Real.exp (-L) := by
        simp only [L]; rw [Real.log_inv, neg_neg, Real.exp_log hρ]
      rw [hρL, harmonicShift]
      exact Real.exp_le_exp.mpr (by linarith)
    refine mul_le_mul_of_nonneg_left ?_ (harmonicWeight_nonneg k)
    rw [Real.log_inv]
    have h2 : Real.log (harmonicShift k + ρ) ≤ Real.log 2 + Real.log (harmonicShift k) := by
      rw [← Real.log_mul two_ne_zero (harmonicShift_pos k).ne']
      exact Real.log_le_log (by linarith [harmonicShift_pos k]) (by linarith)
    rw [log_harmonicShift] at h2
    linarith
  have hfin : ∑ k ∈ Finset.range N, harmonicWeight k * ((k : ℝ) + 1 - Real.log 2) =
      ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2) -
        Real.log 2 * ∑ k ∈ Finset.range N, harmonicWeight k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [harmonicWeight]
    field_simp
  have hW : ∑ k ∈ Finset.range N, harmonicWeight k ≤ 1 := by
    have h := sum_range_harmonicWeight_le 0 N
    simp only [add_zero, Nat.cast_zero, zero_add, div_one] at h
    exact h
  have hharm := log_sub_log_two_le_sum_inv N
  have hlogL : Real.log L ≤ Real.log ((N : ℝ) + 2) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfinle := Finset.sum_le_sum hk
  rw [hfin] at hfinle
  have hW2 := mul_le_mul_of_nonneg_left hW hl20
  simp only [defectProfile]
  linarith

/-- **The upper profile bound.** `Λ(ρ) ≤ log log(1/ρ) + 3` on `(0, e^{-1}]`. -/
theorem defectProfile_harmonic_le {ρ : ℝ} (hρ : 0 < ρ) (hρe : ρ ≤ Real.exp (-1)) :
    defectProfile harmonicWeight harmonicShift ρ ≤ Real.log (Real.log ρ⁻¹) + 3 := by
  set L := Real.log ρ⁻¹
  have hL1 : 1 ≤ L := one_le_log_inv hρ hρe
  set N := ⌊L⌋₊ + 1
  have hLN : L < N := by simp only [N]; push_cast; exact Nat.lt_floor_add_one L
  have hNL : (N : ℝ) ≤ L + 1 := by
    simp only [N]; push_cast; linarith [Nat.floor_le (show 0 ≤ L by linarith)]
  have hd := admissibleDefect_harmonic
  have hs := summable_defectProfile hd hρ
  rw [defectProfile, ← hs.sum_add_tsum_nat_add N]
  have hℓ1 : ∀ k, Real.log (harmonicShift k + ρ)⁻¹ ≤ (k : ℝ) + 1 := fun k => by
    rw [Real.log_inv, neg_le]
    have := Real.log_le_log (harmonicShift_pos k) (show harmonicShift k ≤ harmonicShift k + ρ by
      linarith)
    rw [log_harmonicShift] at this
    linarith
  have hℓ2 : ∀ k, Real.log (harmonicShift k + ρ)⁻¹ ≤ L := fun k => by
    simp only [L]
    rw [Real.log_inv, Real.log_inv, neg_le_neg_iff]
    exact Real.log_le_log hρ (by linarith [harmonicShift_pos k])
  -- the head: `Σ_{k<N} w_k (k + 1) = Σ_{k<N} 1/(k+2) ≤ log(N + 1)`
  have hhead : ∑ k ∈ Finset.range N, harmonicWeight k * Real.log (harmonicShift k + ρ)⁻¹ ≤
      Real.log ((N : ℝ) + 1) := by
    refine le_trans (Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (hℓ1 k) (harmonicWeight_nonneg k)) (le_trans (le_of_eq ?_)
        (sum_inv_le_log N))
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [harmonicWeight]
    field_simp
  -- the tail: `Σ_{k ≥ N} w_k L ≤ L/(N + 1) ≤ 1`
  have htail : ∑' k, harmonicWeight (k + N) * Real.log (harmonicShift (k + N) + ρ)⁻¹ ≤ 1 := by
    have hws : Summable fun k => harmonicWeight (k + N) :=
      hd.summable.comp_injective (add_left_injective N)
    have hst : Summable fun k =>
        harmonicWeight (k + N) * Real.log (harmonicShift (k + N) + ρ)⁻¹ :=
      hs.comp_injective (add_left_injective N)
    calc _ ≤ ∑' k, harmonicWeight (k + N) * L :=
          hst.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hℓ2 _) (harmonicWeight_nonneg _))
            (hws.mul_right L)
      _ = (∑' k, harmonicWeight (k + N)) * L := tsum_mul_right
      _ ≤ 1 / ((N : ℝ) + 1) * L :=
          mul_le_mul_of_nonneg_right (tsum_harmonicWeight_add_le N) (by linarith)
      _ ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hlogN : Real.log ((N : ℝ) + 1) ≤ Real.log L + 2 := by
    have h1 : Real.log ((N : ℝ) + 1) ≤ Real.log (3 * L) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    linarith
  linarith

/-! ### The threshold -/

/-- The model Dini integrand `ρ⁻¹ (log ρ⁻¹)^{-c}` is integrable on `(0, e^{-1})` iff `c > 1`
(substitute `ρ = e^{-v}`). -/
theorem integrableOn_inv_mul_log_rpow_iff {c : ℝ} :
    IntegrableOn (fun ρ : ℝ => ρ⁻¹ * Real.log ρ⁻¹ ^ (-c)) (Ioo 0 (Real.exp (-1))) ↔ 1 < c := by
  have himage : (fun v : ℝ => Real.exp (-v)) '' Ioi 1 = Ioo 0 (Real.exp (-1)) := by
    ext x
    simp only [mem_image, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_exp.mpr (by linarith)⟩
    · rintro ⟨hx0, hx1⟩
      refine ⟨-Real.log x, ?_, by rw [neg_neg, Real.exp_log hx0]⟩
      have := Real.log_lt_log hx0 hx1
      rw [Real.log_exp] at this; linarith
  have hderiv : ∀ v ∈ Ioi (1 : ℝ),
      HasDerivWithinAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-v)) (Ioi 1) v := fun v _ => by
    have := ((hasDerivAt_neg v).exp).hasDerivWithinAt (s := Ioi (1 : ℝ))
    simpa using this
  have hinj : InjOn (fun v : ℝ => Real.exp (-v)) (Ioi 1) := fun a _ b _ h => by
    simpa using Real.exp_injective h
  rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  have heq : EqOn (fun v : ℝ => |-Real.exp (-v)| •
      ((Real.exp (-v))⁻¹ * Real.log (Real.exp (-v))⁻¹ ^ (-c))) (fun v => v ^ (-c)) (Ioi 1) := by
    intro v _
    simp only [smul_eq_mul, abs_neg, abs_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg,
      Real.log_exp]
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [integrableOn_congr_fun heq measurableSet_Ioi, integrableOn_Ioi_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

/-- **The harmonic Dini density is integrable exactly above `c = 1`.** -/
theorem integrableOn_diniDensity_harmonic_iff {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 2) :
    IntegrableOn (diniDensity c harmonicWeight harmonicShift) (Ioc 0 1) ↔ 1 < c := by
  have hd := admissibleDefect_harmonic
  have hcW : c * ∑' k, harmonicWeight k ≤ 2 := by
    have := mul_le_mul_of_nonneg_left tsum_harmonicWeight_le hc; linarith
  set h := diniDensity c harmonicWeight harmonicShift
  set g : ℝ → ℝ := fun ρ => ρ⁻¹ * Real.log ρ⁻¹ ^ (-c)
  have he1 : Real.exp (-1) < 1 := by have := Real.exp_neg_one_lt_half; linarith
  have he0 : 0 < Real.exp (-1) := Real.exp_pos _
  -- `e^{-3c} g ≤ h ≤ e^{2c} g` on `(0, e^{-1})`
  have hcmp : ∀ ρ ∈ Ioo 0 (Real.exp (-1)),
      Real.exp (-(3 * c)) * g ρ ≤ h ρ ∧ h ρ ≤ Real.exp (2 * c) * g ρ := by
    intro ρ hρ
    have hρ0 := hρ.1
    have hL1 := one_le_log_inv hρ0 hρ.2.le
    have hlow := log_log_sub_two_le_defectProfile_harmonic hρ0 hρ.2.le
    have hup := defectProfile_harmonic_le hρ0 hρ.2.le
    have hLpow : Real.log ρ⁻¹ ^ (-c) = Real.exp (-(c * Real.log (Real.log ρ⁻¹))) := by
      rw [Real.rpow_def_of_pos (by linarith)]; ring_nf
    simp only [h, g, diniDensity, hLpow]
    rw [div_eq_mul_inv]
    constructor
    · rw [show Real.exp (-(3 * c)) * (ρ⁻¹ * Real.exp (-(c * Real.log (Real.log ρ⁻¹)))) =
          Real.exp (-(c * (Real.log (Real.log ρ⁻¹) + 3))) * ρ⁻¹ by
        rw [mul_comm ρ⁻¹, ← mul_assoc, ← Real.exp_add]; ring_nf]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (inv_nonneg.mpr hρ0.le)
      have := mul_le_mul_of_nonneg_left hup hc; linarith
    · rw [show Real.exp (2 * c) * (ρ⁻¹ * Real.exp (-(c * Real.log (Real.log ρ⁻¹)))) =
          Real.exp (-(c * (Real.log (Real.log ρ⁻¹) - 2))) * ρ⁻¹ by
        rw [mul_comm ρ⁻¹, ← mul_assoc, ← Real.exp_add]; ring_nf]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (inv_nonneg.mpr hρ0.le)
      have := mul_le_mul_of_nonneg_left hlow hc; linarith
  have hg0 : ∀ ρ ∈ Ioo 0 (Real.exp (-1)), 0 ≤ g ρ := fun ρ hρ =>
    mul_nonneg (inv_nonneg.mpr hρ.1.le) (Real.rpow_nonneg (by linarith [one_le_log_inv hρ.1 hρ.2.le]) _)
  have hgm : Measurable g :=
    measurable_inv.mul ((Real.measurable_log.comp measurable_inv).pow_const (-c))
  have hhm : AEStronglyMeasurable h (volume.restrict (Ioo 0 (Real.exp (-1)))) :=
    ((aemeasurable_diniDensity hd hc).mono_measure (Measure.restrict_mono
      (fun x hx => (show (0 : ℝ) < x from hx.1)) le_rfl)).aestronglyMeasurable
  have hiff : IntegrableOn h (Ioo 0 (Real.exp (-1))) ↔ IntegrableOn g (Ioo 0 (Real.exp (-1))) := by
    constructor
    · intro hh
      refine Integrable.mono' (hh.const_mul (Real.exp (3 * c))) hgm.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun ρ hρ => ?_)
      rw [Real.norm_of_nonneg (hg0 ρ hρ)]
      have h1 := (hcmp ρ hρ).1
      have h2 : Real.exp (3 * c) * Real.exp (-(3 * c)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (3 * c)).le
      rw [← mul_assoc, h2, one_mul] at this
      exact this
    · intro hg
      refine Integrable.mono' (hg.const_mul (Real.exp (2 * c))) hhm ?_
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun ρ hρ => ?_)
      rw [Real.norm_of_nonneg (diniDensity_nonneg c hρ.1.le)]
      exact (hcmp ρ hρ).2
  rw [← integrableOn_inv_mul_log_rpow_iff, ← hiff]
  constructor
  · intro hI
    exact hI.mono_set (fun x hx => ⟨hx.1, hx.2.le.trans he1.le⟩)
  · intro hI
    rw [← Ioc_union_Ioc_eq_Ioc he0.le he1.le]
    exact ((integrableOn_Ioc_iff_integrableOn_Ioo).mpr hI).union
      (integrableOn_diniDensity_Ioc hd hc hcW he0)

/-- **The phase diagram of the harmonic defect.** For `0 ≤ c ≤ 2` and `t₀ > 0`, the half-damped
weight of `f_c(p) = (1 − c Σ_k p^{-e^{-(k+1)}}/((k+1)(k+2))) cos(t₀ log p)` has bounded receiver iff
`c > 1` or `ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_harmonicDefect_iff {c t₀ : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 2) (ht₀ : 0 < t₀) :
    ReceiverBounded (defectWeight c t₀ harmonicWeight harmonicShift) ↔
      1 < c ∨ riemannZeta (1 / 2 + t₀ * I) = 0 := by
  have hcW : c * ∑' k, harmonicWeight k ≤ 2 := by
    have := mul_le_mul_of_nonneg_left tsum_harmonicWeight_le hc; linarith
  rw [receiverBounded_defectWeight_iff admissibleDefect_harmonic hc hcW ht₀,
    integrableOn_diniDensity_harmonic_iff hc hc2]

/-! ### The critical-line mass diverges -/

/-- At real `v > 1`, `Re Σ_p cos(a log p) p^{-v}` is the real prime sum. -/
theorem re_cosPrimeSeries_ofReal (a : ℝ) {v : ℝ} (hv : 1 < v) :
    (cosPrimeSeries a v).re =
      ∑' p : Nat.Primes, Real.cos (a * Real.log (p : ℕ)) * ((p : ℕ) : ℝ) ^ (-v) := by
  rw [cosPrimeSeries, Complex.re_tsum (summable_cos_mul_prime_cpow a (by simpa using hv))]
  refine tsum_congr fun p => ?_
  have hp : (0 : ℝ) ≤ (p : ℕ) := Nat.cast_nonneg _
  rw [show ((p : ℕ) : ℂ) ^ (-(v : ℂ)) = ((((p : ℕ) : ℝ) ^ (-v) : ℝ) : ℂ) by
    rw [Complex.ofReal_cpow hp, Complex.ofReal_natCast, Complex.ofReal_neg]]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- **The squared-cosine prime sum is logarithmic.** For `t₀ > 0` there is `C` with
`Σ_p cos²(t₀ log p) p^{-(1+σ')} ≥ (log(1/σ') − C)/2` on `0 < σ' ≤ 1`: the mean `1/2` of `cos²`
sees the pole of `ζ`, the oscillating half sees `ζ(1 + σ' ± 2it₀)`, which is bounded. -/
theorem exists_sum_cos_sq_ge {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, ∀ σ' : ℝ, 0 < σ' → σ' ≤ 1 →
      (Real.log σ'⁻¹ - C) / 2 ≤ ∑' p : Nat.Primes,
        Real.cos (t₀ * Real.log (p : ℕ)) ^ 2 * ((p : ℕ) : ℝ) ^ (-(1 + σ')) := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_log_norm_zeta_add_log_le (2 * t₀)
  set L₂ : ℝ := L + (|Real.log (2 * t₀)| + |Real.log (1 + 2 * t₀)|)
  refine ⟨L + L₂ + 2 * primeSquareMass, fun σ' hσ hσ1 => ?_⟩
  set v : ℝ := 1 + σ'
  have hv : 1 < v := by simp only [v]; linarith
  have hs1 : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-v) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hs2 : Summable fun p : Nat.Primes =>
      Real.cos (2 * t₀ * Real.log (p : ℕ)) * ((p : ℕ) : ℝ) ^ (-v) :=
    hs1.of_norm_bounded fun p => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.abs_cos_le_one _)
  have hsplit : ∑' p : Nat.Primes, Real.cos (t₀ * Real.log (p : ℕ)) ^ 2 * ((p : ℕ) : ℝ) ^ (-v) =
      (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-v)) / 2 +
        (∑' p : Nat.Primes, Real.cos (2 * t₀ * Real.log (p : ℕ)) * ((p : ℕ) : ℝ) ^ (-v)) / 2 := by
    rw [← tsum_div_const, ← tsum_div_const, ← (hs1.div_const 2).tsum_add (hs2.div_const 2)]
    refine tsum_congr fun p => ?_
    rw [Real.cos_sq, show 2 * (t₀ * Real.log (p : ℕ)) = 2 * t₀ * Real.log (p : ℕ) by ring]
    ring
  have hP : ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-v) = (cosPrimeSeries 0 v).re := by
    rw [re_cosPrimeSeries_ofReal 0 hv]
    simp
  have hQ : ∑' p : Nat.Primes, Real.cos (2 * t₀ * Real.log (p : ℕ)) * ((p : ℕ) : ℝ) ^ (-v) =
      (cosPrimeSeries (2 * t₀) v).re := (re_cosPrimeSeries_ofReal (2 * t₀) hv).symm
  have hvre : 1 < (v : ℂ).re := by simpa using hv
  have h0 := abs_re_cosPrimeSeries_sub_le 0 hvre
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero] at h0
  have h2 := abs_re_cosPrimeSeries_sub_le (2 * t₀) hvre
  -- `log|ζ(v)| ≥ log(1/σ') − L`
  have hZv : Real.log σ'⁻¹ - L ≤ Real.log ‖riemannZeta (v : ℂ)‖ := by
    have h := hL (v : ℂ) hvre (by simp [v]; linarith) (by simp; linarith)
    have hn : ‖(v : ℂ) - 1‖ = σ' := by
      rw [show (v : ℂ) - 1 = ((σ' : ℝ) : ℂ) by simp only [v]; push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hσ]
    rw [hn] at h
    rw [Real.log_inv]
    rw [abs_le] at h; linarith [h.1]
  -- `log|ζ(v ± 2it₀)| ≥ −L₂`
  have hZpm : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      -L₂ ≤ Real.log ‖riemannZeta ((v : ℂ) + ((ε * (2 * t₀) : ℝ) : ℂ) * I)‖ := by
    intro ε hε
    have hε1 : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
    set z : ℂ := (v : ℂ) + ((ε * (2 * t₀) : ℝ) : ℂ) * I
    have hzre : z.re = v := by simp [z]
    have hzim : z.im = ε * (2 * t₀) := by simp [z]
    have hzim' : |z.im| = 2 * t₀ := by rw [hzim, abs_mul, hε1, one_mul, abs_of_pos (by linarith)]
    have hb := abs_log_norm_zeta_le_of_mem hL (v := z) (by rw [hzre]; exact hv)
      (by rw [hzre]; simp only [v]; linarith) (le_of_eq hzim') (a := 2 * t₀) (b := 1 + 2 * t₀)
      (by linarith)
      (by
        have := Complex.abs_im_le_norm (z - 1)
        rw [Complex.sub_im, Complex.one_im, sub_zero, hzim'] at this; exact this)
      (by
        have := Complex.norm_le_abs_re_add_abs_im (z - 1)
        rw [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, hzre,
          hzim', abs_of_pos (by simp only [v]; linarith)] at this
        simp only [v] at this; linarith)
    rw [abs_le] at hb; linarith [hb.1]
  have hm := hZpm (-1) (Or.inr rfl)
  have hp := hZpm 1 (Or.inl rfl)
  have e1 : (v : ℂ) - ((2 * t₀ : ℝ) : ℂ) * I = (v : ℂ) + (((-1) * (2 * t₀) : ℝ) : ℂ) * I := by
    push_cast; ring
  have e2 : (v : ℂ) + ((2 * t₀ : ℝ) : ℂ) * I = (v : ℂ) + ((1 * (2 * t₀) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e1, e2] at h2
  rw [hsplit, hP, hQ]
  rw [abs_le] at h0 h2
  linarith [h0.1, h2.1]

variable {w s : ℕ → ℝ}

/-- **Unbounded profiles have divergent critical-line mass.** For admissible defect data whose
profile `Λ` is unbounded on `(0, 1/2]`, and `c > 0`, `t₀ > 0`, the critical-line mass
`Σ_p |f(p) − cos(t₀ log p)|/p` of the defect pattern is infinite: the summable-perturbation
invariance of the receiver does not apply. -/
theorem not_summable_criticalLineMass_defect (hd : AdmissibleDefect w s) {c t₀ : ℝ} (hc : 0 < c)
    (ht₀ : 0 < t₀) (hΛ : ∀ M : ℝ, ∃ u : ℝ, 0 < u ∧ u ≤ 1 / 2 ∧ M ≤ defectProfile w s u) :
    ¬ Summable fun p : Nat.Primes =>
      |defectPattern c t₀ w s p - oscPattern 1 t₀ p| / ((p : ℕ) : ℝ) := by
  intro hsum
  obtain ⟨C, hC⟩ := exists_sum_cos_sq_ge ht₀
  set W := ∑' k, w k
  set Sm := ∑' p : Nat.Primes, |defectPattern c t₀ w s p - oscPattern 1 t₀ p| / ((p : ℕ) : ℝ)
  obtain ⟨u, hu, hu2, hM⟩ := hΛ (2 * Sm / c + C * W + 1)
  set q : Nat.Primes → ℕ → ℝ := fun p k =>
    w k * (Real.cos (t₀ * Real.log (p : ℕ)) ^ 2 * ((p : ℕ) : ℝ) ^ (-(1 + (u + s k))))
  have hp1 : ∀ p : Nat.Primes, (1 : ℝ) ≤ (p : ℕ) := fun p => by exact_mod_cast p.2.one_lt.le
  have hq0 : ∀ p k, 0 ≤ q p k := fun p k =>
    mul_nonneg (hd.nonneg k) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hqb : ∀ p k, q p k ≤ ((p : ℕ) : ℝ) ^ (-(1 + u)) * w k := fun p k => by
    simp only [q]
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (hd.nonneg k)
    have hc2 : Real.cos (t₀ * Real.log (p : ℕ)) ^ 2 ≤ 1 := by
      rw [sq]; nlinarith [Real.abs_cos_le_one (t₀ * Real.log (p : ℕ)),
        abs_mul_abs_self (Real.cos (t₀ * Real.log (p : ℕ))), abs_nonneg (Real.cos (t₀ * Real.log (p : ℕ)))]
    have hr : ((p : ℕ) : ℝ) ^ (-(1 + (u + s k))) ≤ ((p : ℕ) : ℝ) ^ (-(1 + u)) :=
      Real.rpow_le_rpow_of_exponent_le (hp1 p) (by linarith [hd.pos k])
    calc _ ≤ 1 * ((p : ℕ) : ℝ) ^ (-(1 + (u + s k))) :=
          mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ _ := by rw [one_mul]; exact hr
  have hsu : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 + u)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hqs : Summable (Function.uncurry q) :=
    (hsu.mul_of_nonneg hd.summable (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      hd.nonneg).of_nonneg_of_le (fun x => hq0 x.1 x.2) fun x => hqb x.1 x.2
  -- the rows: `Σ_k q(p, k) = g(p) cos² p^{-(1+u)}`
  have hrow : ∀ p : Nat.Primes, ∑' k, q p k = cmDefect w s (p : ℕ) *
      (Real.cos (t₀ * Real.log (p : ℕ)) ^ 2 * ((p : ℕ) : ℝ) ^ (-(1 + u))) := by
    intro p
    rw [cmDefect, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    simp only [q]
    rw [show -(1 + (u + s k)) = -s k + -(1 + u) by ring,
      Real.rpow_add (by exact_mod_cast p.2.pos)]
    ring
  -- `c X ≤ Sm`
  have hdiff : ∀ p : Nat.Primes, |defectPattern c t₀ w s p - oscPattern 1 t₀ p| =
      c * cmDefect w s (p : ℕ) * |Real.cos (t₀ * Real.log (p : ℕ))| := fun p => by
    rw [defectPattern_prime c t₀ p.2, oscPattern_prime 1 t₀ p.2,
      show (1 - c * cmDefect w s (p : ℕ)) * Real.cos (t₀ * Real.log (p : ℕ)) -
          1 * Real.cos (t₀ * Real.log (p : ℕ)) =
        -(c * cmDefect w s (p : ℕ) * Real.cos (t₀ * Real.log (p : ℕ))) by ring,
      abs_neg, abs_mul, abs_of_nonneg (mul_nonneg hc.le (cmDefect_nonneg hd (hp1 p)))]
  have hX1 : c * ∑' p : Nat.Primes, ∑' k, q p k ≤ Sm := by
    rw [← tsum_mul_left]
    refine (hqs.prod.mul_left c).tsum_le_tsum (fun p => ?_) hsum
    rw [hrow p, hdiff p]
    have hg := cmDefect_nonneg hd (hp1 p)
    have hcos : Real.cos (t₀ * Real.log (p : ℕ)) ^ 2 ≤ |Real.cos (t₀ * Real.log (p : ℕ))| := by
      rw [← sq_abs, sq]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
    have hr : ((p : ℕ) : ℝ) ^ (-(1 + u)) ≤ 1 / ((p : ℕ) : ℝ) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (hp1 p) (by linarith)
    rw [div_eq_mul_one_div _ ((p : ℕ) : ℝ)]
    have hcg : 0 ≤ c * cmDefect w s (p : ℕ) := mul_nonneg hc.le hg
    calc c * (cmDefect w s (p : ℕ) *
          (Real.cos (t₀ * Real.log (p : ℕ)) ^ 2 * ((p : ℕ) : ℝ) ^ (-(1 + u))))
        = (c * cmDefect w s (p : ℕ)) *
            (Real.cos (t₀ * Real.log (p : ℕ)) ^ 2 * ((p : ℕ) : ℝ) ^ (-(1 + u))) := by ring
      _ ≤ (c * cmDefect w s (p : ℕ)) * (|Real.cos (t₀ * Real.log (p : ℕ))| * (1 / ((p : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hcos hr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            (abs_nonneg _)) hcg
      _ = _ := by ring
  -- the columns: `Σ_p q(p, k) = w_k Y(u + s_k)`, and `Y(σ') ≥ (log(1/σ') − C)/2`
  have hswap : ∑' p : Nat.Primes, ∑' k, q p k = ∑' k, ∑' p : Nat.Primes, q p k :=
    hqs.tsum_comm.symm
  have hcol : ∀ k, (w k * Real.log (s k + u)⁻¹) / 2 - C / 2 * w k ≤ ∑' p : Nat.Primes, q p k := by
    intro k
    simp only [q]
    rw [tsum_mul_left]
    have hY := hC (u + s k) (by linarith [hd.pos k]) (by linarith [hd.le_half k])
    rw [show s k + u = u + s k by ring]
    have := mul_le_mul_of_nonneg_left hY (hd.nonneg k)
    have e : w k * ((Real.log (u + s k)⁻¹ - C) / 2) =
        w k * Real.log (u + s k)⁻¹ / 2 - C / 2 * w k := by ring
    linarith
  have hPu : ∀ k, ∑' p : Nat.Primes, q p k ≤ (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + u))) * w k :=
    fun k => ((hqs.prod_symm.prod_factor k)).tsum_le_tsum (fun p => hqb p k) (hsu.mul_right _)
      |>.trans (le_of_eq tsum_mul_right)
  have hcs : Summable fun k => ∑' p : Nat.Primes, q p k :=
    (hd.summable.mul_left (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + u)))).of_nonneg_of_le
      (fun k => tsum_nonneg fun p => hq0 p k) hPu
  have hlows : Summable fun k => (w k * Real.log (s k + u)⁻¹) / 2 - C / 2 * w k :=
    ((summable_defectProfile hd hu).div_const 2).sub (hd.summable.mul_left (C / 2))
  have hX2 : (defectProfile w s u) / 2 - C / 2 * W ≤ ∑' p : Nat.Primes, ∑' k, q p k := by
    rw [hswap]
    refine le_trans (le_of_eq ?_) (hlows.tsum_le_tsum hcol hcs)
    rw [Summable.tsum_sub ((summable_defectProfile hd hu).div_const 2)
      (hd.summable.mul_left (C / 2)), tsum_div_const, tsum_mul_left]
    rfl
  have hcc : c * (Sm / c + 1 / 2) = Sm + c / 2 := by field_simp
  have hge : Sm / c + 1 / 2 ≤ ∑' p : Nat.Primes, ∑' k, q p k := by
    have : (2 * Sm / c + C * W + 1) / 2 - C / 2 * W = Sm / c + 1 / 2 := by ring
    linarith
  have := mul_le_mul_of_nonneg_left hge hc.le
  linarith

/-- **The harmonic defect has divergent critical-line mass** at every `0 < c ≤ 2`. -/
theorem not_summable_criticalLineMass_harmonic {c t₀ : ℝ} (hc : 0 < c) (ht₀ : 0 < t₀) :
    ¬ Summable fun p : Nat.Primes =>
      |defectPattern c t₀ harmonicWeight harmonicShift p - oscPattern 1 t₀ p| / ((p : ℕ) : ℝ) := by
  refine not_summable_criticalLineMass_defect admissibleDefect_harmonic hc ht₀ fun M => ?_
  set X : ℝ := |M| + 2
  have hX1 : 1 ≤ Real.exp X := Real.one_le_exp (by positivity)
  have hρe : Real.exp (-Real.exp X) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  refine ⟨Real.exp (-Real.exp X), Real.exp_pos _, hρe.trans Real.exp_neg_one_lt_half.le, ?_⟩
  have h := log_log_sub_two_le_defectProfile_harmonic (Real.exp_pos _) hρe
  rw [Real.log_inv, Real.log_exp, neg_neg, Real.log_exp] at h
  simp only [X] at h
  linarith [le_abs_self M]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
