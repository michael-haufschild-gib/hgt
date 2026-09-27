import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import GaloisForLFunctions.HTGeometry.BernsteinWidder
import GaloisForLFunctions.HTGeometry.RepairedFrequencyDensityLaplace

/-!
# The critical theta flux and its Bernstein measure

For a source `f`, the normalized critical flux is
`b_f(t) = t^{-3/2} ∫_{[log t / 2, ∞)} e^{x/2} f(x) dx`.

* Every literal theta atom has exact flux potential `2π n² e^{3x} exp(-π n² e^{2x})`; for any set `A`
  of labels the atom sum `∑_{n∈A} a_n` has flux `2π ∑_{n∈A} n² e^{-π n² t}`.  In particular
  `b_k(t) = 2π ∑_{n≥1} n² e^{-π n² t}`.
* Translation law `b_{f(·+s)}(t) = e^{5s/2} b_f(e^{2s} t)`; the flux determines a continuous source.
* Positive countable exponential sums are completely monotone; conversely, if an absolutely
  convergent signed exponential sum is completely monotone, its total coefficient at every rate is
  nonnegative (Bernstein--Widder and Laplace uniqueness of finite measures).
* A completely monotone summand of a positive exponential sum with injective rates is an
  exponential sum on the same rates with dominated weights; such coefficients are unique.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Iterated forward differences of a countable exponential sum. -/
private theorem fwdDiff_iter_tsum_exp {ι : Type*} (c lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hsum : ∀ t, 0 < t → Summable fun i => |c i| * Real.exp (-lam i * t)) {δ : ℝ} (hδ : 0 < δ)
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    (fwdDiff δ)^[k] (fun s => ∑' i, c i * Real.exp (-lam i * s)) t =
      ∑' i, c i * Real.exp (-lam i * t) * (Real.exp (-lam i * δ) - 1) ^ k := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', fwdDiff, ih ht, ih (by linarith)]
    have hb : ∀ i, |(Real.exp (-lam i * δ) - 1) ^ k| ≤ 1 := by
      intro i
      rw [abs_pow]
      apply pow_le_one₀ (abs_nonneg _)
      have h1 : Real.exp (-lam i * δ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hlam i])
      have h2 : 0 < Real.exp (-lam i * δ) := Real.exp_pos _
      rw [abs_le]
      constructor <;> linarith
    have hs : ∀ s, 0 < s → Summable fun i =>
        c i * Real.exp (-lam i * s) * (Real.exp (-lam i * δ) - 1) ^ k := by
      intro s hs
      refine Summable.of_norm_bounded (hsum s hs) (fun i => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have := hb i
      calc |c i| * Real.exp (-lam i * s) * |(Real.exp (-lam i * δ) - 1) ^ k| ≤
          |c i| * Real.exp (-lam i * s) * 1 := by gcongr
        _ = |c i| * Real.exp (-lam i * s) := mul_one _
    rw [← (hs (t + δ) (by linarith)).tsum_sub (hs t ht)]
    apply tsum_congr
    intro i
    rw [show -lam i * (t + δ) = -lam i * t + -lam i * δ by ring, Real.exp_add, pow_succ]
    ring

/-- A positive countable exponential sum is completely monotone on `(0,∞)`. -/
theorem completelyMonotoneOn_tsum_exp {ι : Type*} (c lam : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hlam : ∀ i, 0 ≤ lam i) (hsum : ∀ t, 0 < t → Summable fun i => c i * Real.exp (-lam i * t)) :
    CompletelyMonotoneOn (fun t => ∑' i, c i * Real.exp (-lam i * t)) := by
  have hsum' : ∀ t, 0 < t → Summable fun i => |c i| * Real.exp (-lam i * t) := by
    intro t ht
    simpa [abs_of_nonneg (hc _)] using hsum t ht
  constructor
  · intro k δ hδ t ht
    rw [fwdDiff_iter_tsum_exp c lam hlam hsum' hδ k ht, ← tsum_mul_left]
    apply tsum_nonneg
    intro i
    rw [show (-1 : ℝ) ^ k * (c i * Real.exp (-lam i * t) * (Real.exp (-lam i * δ) - 1) ^ k) =
      c i * Real.exp (-lam i * t) * (1 - Real.exp (-lam i * δ)) ^ k by
        rw [show (1 - Real.exp (-lam i * δ)) = (-1) * (Real.exp (-lam i * δ) - 1) by ring,
          mul_pow]
        ring]
    have h1 : Real.exp (-lam i * δ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hlam i])
    have : 0 ≤ 1 - Real.exp (-lam i * δ) := by linarith
    exact mul_nonneg (mul_nonneg (hc i) (Real.exp_pos _).le) (pow_nonneg this k)
  · intro t ht
    have hopen : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith [show (0 : ℝ) < t from ht])
    have hcont : ContinuousOn (fun s => ∑' i, c i * Real.exp (-lam i * s)) (Ioi (t / 2)) := by
      apply continuousOn_tsum (u := fun i => c i * Real.exp (-lam i * (t / 2)))
      · intro i
        fun_prop
      · exact hsum (t / 2) (by linarith [show (0 : ℝ) < t from ht])
      · intro i s hs
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc i), abs_of_pos (Real.exp_pos _)]
        have : t / 2 ≤ s := le_of_lt hs
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hlam i])) (hc i)
    exact (hcont.continuousAt hopen).continuousWithinAt


/-- Shifting a completely monotone profile to the right keeps it completely monotone. -/
theorem completelyMonotoneOn_comp_add_left {H : ℝ → ℝ} (hH : CompletelyMonotoneOn H) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) : CompletelyMonotoneOn (fun s => H (t₀ + s)) := by
  constructor
  · intro k δ hδ s hs
    have h := hH.1 k δ hδ (t₀ + s) (by linarith)
    rw [fwdDiff_iter_eq_sum_shift] at h ⊢
    simpa only [add_assoc] using h
  · exact hH.2.comp (continuous_const.add continuous_id).continuousOn
      (fun s hs => by simp only [mem_Ioi] at hs ⊢; linarith)

/-- The finite atomic measure `∑ w_i δ_{λ_i}`. -/
noncomputable def atomicMeasure {ι : Type*} (w lam : ι → ℝ) : Measure ℝ :=
  Measure.sum fun i => ENNReal.ofReal (w i) • Measure.dirac (lam i)

theorem atomicMeasure_apply {ι : Type*} (w lam : ι → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    atomicMeasure w lam s = ∑' i, ENNReal.ofReal (w i) * s.indicator 1 (lam i) := by
  rw [atomicMeasure, Measure.sum_apply _ hs]
  apply tsum_congr
  intro i
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]

theorem atomicMeasure_singleton {ι : Type*} (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (μ : ℝ) :
    atomicMeasure w lam {μ} = ENNReal.ofReal (∑' i, if lam i = μ then w i else 0) := by
  rw [atomicMeasure_apply _ _ (measurableSet_singleton μ),
    ENNReal.ofReal_tsum_of_nonneg (fun i => by split_ifs <;> simp [hw i])
      (hs.indicator {i | lam i = μ} |>.congr fun i => by
        simp [Set.indicator_apply])]
  apply tsum_congr
  intro i
  by_cases h : lam i = μ <;> simp [h]

theorem atomicMeasure_univ {ι : Type*} (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) :
    atomicMeasure w lam Set.univ = ENNReal.ofReal (∑' i, w i) := by
  rw [atomicMeasure_apply _ _ MeasurableSet.univ, ENNReal.ofReal_tsum_of_nonneg hw hs]
  simp

theorem isFiniteMeasure_atomicMeasure {ι : Type*} (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) : IsFiniteMeasure (atomicMeasure w lam) :=
  ⟨by rw [atomicMeasure_univ w lam hw hs]; exact ENNReal.ofReal_lt_top⟩

theorem atomicMeasure_compl_Ici {ι : Type*} (w lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    atomicMeasure w lam (Ici 0)ᶜ = 0 := by
  rw [atomicMeasure_apply _ _ measurableSet_Ici.compl]
  apply ENNReal.tsum_eq_zero.mpr
  intro i
  rw [Set.indicator_of_notMem (by simpa using hlam i), mul_zero]

/-- Laplace transform of an atomic measure. -/
theorem integral_exp_atomicMeasure {ι : Type*} (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hlam : ∀ i, 0 ≤ lam i) (hs : Summable w) {t : ℝ} (ht : 0 ≤ t) :
    (∫ r, Real.exp (-t * r) ∂atomicMeasure w lam) = ∑' i, w i * Real.exp (-t * lam i) := by
  have hsum : Summable fun i => w i * Real.exp (-t * lam i) := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (Real.exp_pos _).le)
      (fun i => ?_) hs
    have : Real.exp (-t * lam i) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hlam i])
    nlinarith [hw i]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun r => (Real.exp_pos _).le)
    (by fun_prop : Continuous fun r : ℝ => Real.exp (-t * r)).aestronglyMeasurable,
    atomicMeasure, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, ← ENNReal.ofReal_mul (hw _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hw i) (Real.exp_pos _).le) hsum,
    ENNReal.toReal_ofReal (tsum_nonneg fun i => mul_nonneg (hw i) (Real.exp_pos _).le)]

/-- **Atomic sign extraction.**  If a countable exponential sum with absolutely convergent
coefficients is completely monotone on `(0,∞)`, then its total coefficient at every rate is
nonnegative. -/
theorem tsum_coeff_nonneg_of_completelyMonotoneOn {ι : Type*} [Countable ι] (c lam : ι → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hsum : ∀ t, 0 < t → Summable fun i => |c i| * Real.exp (-lam i * t))
    (hCM : CompletelyMonotoneOn (fun t => ∑' i, c i * Real.exp (-lam i * t))) (μ : ℝ) :
    0 ≤ ∑' i, if lam i = μ then c i else 0 := by
  set H : ℝ → ℝ := fun t => ∑' i, c i * Real.exp (-lam i * t)
  have hG := completelyMonotoneOn_comp_add_left hCM (t₀ := 1) zero_le_one
  have hcont : ContinuousAt H 1 := hCM.2.continuousAt (Ioi_mem_nhds one_pos)
  have hlim : Tendsto (fun s => H (1 + s)) (𝓝[>] 0) (𝓝 (H 1)) := by
    have hl : Tendsto (fun s : ℝ => 1 + s) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous fun s : ℝ => 1 + s := by fun_prop
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    exact hcont.tendsto.comp hl
  obtain ⟨τ, hτfin, hτsupp, hτ⟩ := exists_finiteLaplaceMeasure_of_completelyMonotoneOn hG hlim
  set wp : ι → ℝ := fun i => max (c i) 0 * Real.exp (-lam i * 1)
  set wn : ι → ℝ := fun i => max (-c i) 0 * Real.exp (-lam i * 1)
  have hwp : ∀ i, 0 ≤ wp i := fun i => mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
  have hwn : ∀ i, 0 ≤ wn i := fun i => mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
  have hs1 := hsum 1 one_pos
  have hwps : Summable wp := Summable.of_nonneg_of_le hwp (fun i => by
    simp only [wp]
    exact mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _))
      (Real.exp_pos _).le) hs1
  have hwns : Summable wn := Summable.of_nonneg_of_le hwn (fun i => by
    simp only [wn]
    exact mul_le_mul_of_nonneg_right (max_le (neg_le_abs _) (abs_nonneg _))
      (Real.exp_pos _).le) hs1
  haveI := isFiniteMeasure_atomicMeasure wp lam hwp hwps
  haveI := isFiniteMeasure_atomicMeasure wn lam hwn hwns
  have hsplit : ∀ s, 0 < s → H (1 + s) =
      (∫ r, Real.exp (-s * r) ∂atomicMeasure wp lam) -
        ∫ r, Real.exp (-s * r) ∂atomicMeasure wn lam := by
    intro s hs
    rw [integral_exp_atomicMeasure wp lam hwp hlam hwps hs.le,
      integral_exp_atomicMeasure wn lam hwn hlam hwns hs.le]
    have hsp : Summable fun i => wp i * Real.exp (-s * lam i) :=
      Summable.of_nonneg_of_le (fun i => mul_nonneg (hwp i) (Real.exp_pos _).le)
        (fun i => mul_le_of_le_one_right (hwp i)
          (Real.exp_le_one_iff.mpr (by nlinarith [hlam i]))) hwps
    have hsn : Summable fun i => wn i * Real.exp (-s * lam i) :=
      Summable.of_nonneg_of_le (fun i => mul_nonneg (hwn i) (Real.exp_pos _).le)
        (fun i => mul_le_of_le_one_right (hwn i)
          (Real.exp_le_one_iff.mpr (by nlinarith [hlam i]))) hwns
    rw [← hsp.tsum_sub hsn]
    apply tsum_congr
    intro i
    simp only [wp, wn]
    rw [show -lam i * (1 + s) = -lam i * 1 + -s * lam i by ring, Real.exp_add]
    rcases le_total 0 (c i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
  have hmeas : τ + atomicMeasure wn lam = atomicMeasure wp lam := by
    apply measure_eq_of_laplace_eq
    · rw [Measure.add_apply, hτsupp, atomicMeasure_compl_Ici wn lam hlam, add_zero]
    · exact atomicMeasure_compl_Ici wp lam hlam
    · intro s hs
      have hint : ∀ ν : Measure ℝ, IsFiniteMeasure ν → ν (Ici 0)ᶜ = 0 →
          Integrable (fun r => Real.exp (-s * r)) ν := by
        intro ν _ hν
        refine Integrable.mono' (integrable_const 1)
          (by fun_prop : Continuous fun r : ℝ => Real.exp (-s * r)).aestronglyMeasurable ?_
        have hae : ∀ᵐ r ∂ν, r ∈ Ici (0 : ℝ) := by
          rw [ae_iff]
          exact hν
        filter_upwards [hae] with r hr
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by nlinarith [show (0 : ℝ) ≤ r from hr])
      rw [integral_add_measure (hint τ hτfin hτsupp)
        (hint _ inferInstance (atomicMeasure_compl_Ici wn lam hlam)), ← hτ s hs, hsplit s hs]
      ring
  have hμ := congrArg (fun ν : Measure ℝ => ν {μ}) hmeas
  simp only [Measure.add_apply] at hμ
  rw [atomicMeasure_singleton wn lam hwn hwns, atomicMeasure_singleton wp lam hwp hwps] at hμ
  have hle : ENNReal.ofReal (∑' i, if lam i = μ then wn i else 0) ≤
      ENNReal.ofReal (∑' i, if lam i = μ then wp i else 0) := by
    rw [← hμ]
    exact le_add_self
  have hsn' : Summable fun i => if lam i = μ then wn i else 0 :=
    (hwns.indicator {i | lam i = μ}).congr fun i => by simp [Set.indicator_apply]
  have hsp' : Summable fun i => if lam i = μ then wp i else 0 :=
    (hwps.indicator {i | lam i = μ}).congr fun i => by simp [Set.indicator_apply]
  rw [ENNReal.ofReal_le_ofReal_iff (tsum_nonneg fun i => by split_ifs <;> simp [hwp i])] at hle
  have hdiff : (∑' i, if lam i = μ then wp i else 0) - (∑' i, if lam i = μ then wn i else 0) =
      Real.exp (-μ * 1) * ∑' i, if lam i = μ then c i else 0 := by
    rw [← hsp'.tsum_sub hsn', ← tsum_mul_left]
    apply tsum_congr
    intro i
    by_cases h : lam i = μ
    · simp only [h, if_true, wp, wn]
      rcases le_total 0 (c i) with hc | hc
      · rw [max_eq_left hc, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right hc, max_eq_left (by linarith)]
        ring
    · simp [h]
  have hpos : 0 ≤ Real.exp (-μ * 1) * ∑' i, if lam i = μ then c i else 0 := by linarith
  exact nonneg_of_mul_nonneg_right (by linarith [hpos]) (Real.exp_pos _) |> fun h => by
    nlinarith [Real.exp_pos (-μ * 1), hpos]


/-- Normalized critical flux `b_f(t) = t^{-3/2} ∫_{[log t / 2, ∞)} e^{x/2} f(x) dx`. -/
noncomputable def thetaNormalizedFlux (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  t ^ (-(3 / 2 : ℝ)) * ∫ x in Ici (Real.log t / 2), Real.exp (x / 2) * f x

/-- The flux potential of one atom: `2π n² e^{3x} exp(-π n² e^{2x})`. -/
noncomputable def thetaAtomFluxPotential (n : ℕ) (x : ℝ) : ℝ :=
  2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (3 * x) * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x))

theorem exp_half_mul_thetaCuspSourceTerm (n : ℕ) (x : ℝ) :
    Real.exp (x / 2) * thetaCuspSourceTerm x n =
      2 * Real.pi * (n : ℝ) ^ 2 * (2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) - 3) *
        Real.exp (3 * x) * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) := by
  unfold thetaCuspSourceTerm thetaCuspSeed
  have h2 : Real.exp (2 * x) = Real.exp x ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have h3 : Real.exp (3 * x) = Real.exp x ^ 3 := by rw [← Real.exp_nat_mul]; ring_nf
  have hh : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by rw [← Real.exp_add]; ring_nf
  rw [h2, h3, show -Real.pi * ((n : ℝ) * Real.exp x) ^ 2 = -Real.pi * (n : ℝ) ^ 2 * Real.exp x ^ 2
    by ring]
  calc Real.exp (x / 2) * (Real.exp (x / 2) * (2 * Real.pi * (2 * Real.pi * ((n : ℝ) * Real.exp x) ^ 4 -
        3 * ((n : ℝ) * Real.exp x) ^ 2) * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp x ^ 2))) =
      (Real.exp (x / 2) * Real.exp (x / 2)) * (2 * Real.pi * (2 * Real.pi * ((n : ℝ) * Real.exp x) ^ 4 -
        3 * ((n : ℝ) * Real.exp x) ^ 2) * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp x ^ 2)) := by ring
    _ = _ := by rw [hh]; ring

theorem hasDerivAt_thetaAtomFluxPotential (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaAtomFluxPotential n)
      (-(Real.exp (x / 2) * thetaCuspSourceTerm x n)) x := by
  rw [exp_half_mul_thetaCuspSourceTerm]
  have hform : thetaAtomFluxPotential n = fun y : ℝ =>
      2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (3 * y - Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * y)) := by
    funext y
    unfold thetaAtomFluxPotential
    rw [sub_eq_add_neg, Real.exp_add]
    ring_nf
  have e2 : HasDerivAt (fun y : ℝ => Real.exp (2 * y)) (Real.exp (2 * x) * 2) x := by
    have := ((hasDerivAt_id x).const_mul (2 : ℝ)).exp
    simp only [id, mul_one] at this
    exact this
  have hg : HasDerivAt (fun y : ℝ => 3 * y - Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * y))
      (3 * 1 - Real.pi * (n : ℝ) ^ 2 * (Real.exp (2 * x) * 2)) x :=
    ((hasDerivAt_id x).const_mul (3 : ℝ)).sub (e2.const_mul _)
  have h := (hg.exp).const_mul (2 * Real.pi * (n : ℝ) ^ 2)
  rw [hform]
  refine h.congr_deriv ?_
  rw [show 3 * x - Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) =
    3 * x + -Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) by ring, Real.exp_add]
  ring

theorem tendsto_thetaAtomFluxPotential_atTop {n : ℕ} (hn : 0 < n) :
    Tendsto (thetaAtomFluxPotential n) atTop (𝓝 0) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hexp : Tendsto (fun x : ℝ => 3 * x - Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) atTop atBot := by
    apply tendsto_atBot_mono (f := fun x : ℝ => (3 - 2 * Real.pi) * x - Real.pi)
    · intro x
      have := Real.add_one_le_exp (2 * x)
      have hmono : Real.pi * Real.exp (2 * x) * 1 ≤ Real.pi * Real.exp (2 * x) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hn1 (mul_pos Real.pi_pos (Real.exp_pos _)).le
      nlinarith [Real.pi_pos]
    · apply tendsto_atBot_add_const_right
      exact tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_gt_three])
  have h := (Real.tendsto_exp_atBot.comp hexp).const_mul (2 * Real.pi * (n : ℝ) ^ 2)
  rw [mul_zero] at h
  refine h.congr (fun x => ?_)
  unfold thetaAtomFluxPotential
  simp only [Function.comp_apply]
  rw [show 3 * x - Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) =
    3 * x + -Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) by ring, Real.exp_add]
  ring

theorem integrable_exp_half_mul_thetaCuspSourceTerm {n : ℕ} (hn : 0 < n) :
    Integrable (fun x : ℝ => Real.exp (x / 2) * thetaCuspSourceTerm x n) := by
  have h := integrable_exp_mul_of_integrable_cexp_mul (1 / 2)
    (integrable_cexp_mul_thetaCuspSourceTerm ((1 / 2 : ℝ) : ℂ) (by norm_num) n hn)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only
  ring_nf

/-- Exact tail integral of one atom against the critical weight. -/
theorem setIntegral_Ici_exp_half_mul_thetaCuspSourceTerm (n : ℕ) (X : ℝ) :
    (∫ x in Ici X, Real.exp (x / 2) * thetaCuspSourceTerm x n) = thetaAtomFluxPotential n X := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [thetaCuspSourceTerm, thetaCuspSeed, thetaAtomFluxPotential]
  rw [integral_Ici_eq_integral_Ioi]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := X)
    (f := thetaAtomFluxPotential n)
    (fun x _ => hasDerivAt_thetaAtomFluxPotential n x)
    (integrable_exp_half_mul_thetaCuspSourceTerm hn).neg.integrableOn
    (tendsto_thetaAtomFluxPotential_atTop hn)
  rw [integral_neg] at h
  linarith


/-- The atom sum over a set `A` of labels: `∑_{n ∈ A} a_n`. -/
noncomputable def thetaAtomSum (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, A.indicator (fun m => thetaCuspSourceTerm x m) n

theorem thetaAtomSum_univ : thetaAtomSum Set.univ = thetaCuspFullSource := by
  funext x
  simp [thetaAtomSum, thetaCuspFullSource]

theorem thetaCuspSourceTerm_nonneg_of_one_le {n : ℕ} {x : ℝ} (h : 1 ≤ (n : ℝ) * Real.exp x) :
    0 ≤ thetaCuspSourceTerm x n := by
  unfold thetaCuspSourceTerm
  apply mul_nonneg (Real.exp_pos _).le
  apply (thetaCuspSeed_pos _).le
  nlinarith [Real.pi_gt_three]

theorem integrable_exp_half_mul_thetaCuspSourceTerm' (n : ℕ) :
    Integrable (fun x : ℝ => Real.exp (x / 2) * thetaCuspSourceTerm x n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [thetaCuspSourceTerm, thetaCuspSeed]
  · exact integrable_exp_half_mul_thetaCuspSourceTerm hn

theorem summable_thetaAtomFluxPotential (X : ℝ) : Summable fun n : ℕ => thetaAtomFluxPotential n X := by
  have h := (summable_pow_mul_exp_neg_nat_sq 2 (mul_pos Real.pi_pos (Real.exp_pos (2 * X)))).mul_left
    (2 * Real.pi * Real.exp (3 * X))
  refine h.congr fun n => ?_
  unfold thetaAtomFluxPotential
  ring_nf

theorem thetaAtomFluxPotential_nonneg (n : ℕ) (X : ℝ) : 0 ≤ thetaAtomFluxPotential n X := by
  unfold thetaAtomFluxPotential
  positivity

/-- **Tail integral of any atom sum.** -/
theorem setIntegral_Ici_exp_half_mul_thetaAtomSum (A : Set ℕ) (X : ℝ) :
    IntegrableOn (fun x => Real.exp (x / 2) * thetaAtomSum A x) (Ici X) ∧
      (∫ x in Ici X, Real.exp (x / 2) * thetaAtomSum A x) =
        ∑' n : ℕ, A.indicator (fun m => thetaAtomFluxPotential m X) n := by
  set F : ℕ → ℝ → ℝ := fun n x => Real.exp (x / 2) *
    A.indicator (fun m => thetaCuspSourceTerm x m) n
  have hF : ∀ n, Integrable (F n) (volume.restrict (Ici X)) := by
    intro n
    by_cases hn : n ∈ A
    · have h := (integrable_exp_half_mul_thetaCuspSourceTerm' n).integrableOn (s := Ici X)
      refine Integrable.congr h (Eventually.of_forall fun x => ?_)
      simp [F, Set.indicator_of_mem hn]
    · have : F n = fun _ => 0 := by
        funext x
        simp [F, Set.indicator_of_notMem hn]
      rw [this]
      exact integrable_zero _ _ _
  have hIF : ∀ n, (∫ x in Ici X, F n x) = A.indicator (fun m => thetaAtomFluxPotential m X) n := by
    intro n
    by_cases hn : n ∈ A
    · simp only [F, Set.indicator_of_mem hn]
      exact setIntegral_Ici_exp_half_mul_thetaCuspSourceTerm n X
    · simp [F, Set.indicator_of_notMem hn]
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, Real.exp (-X) ≤ N0 := exists_nat_ge _
  have hnorm : ∀ᶠ n : ℕ in cofinite, ‖∫ x in Ici X, ‖F n x‖‖ ≤ thetaAtomFluxPotential n X := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N0] with n hn
    have hpos : ∀ x ∈ Ici X, 0 ≤ F n x := by
      intro x hx
      apply mul_nonneg (Real.exp_pos _).le
      by_cases hnA : n ∈ A
      · rw [Set.indicator_of_mem hnA]
        apply thetaCuspSourceTerm_nonneg_of_one_le
        have hn' : Real.exp (-X) ≤ n := hN0.trans (by exact_mod_cast hn)
        have hex : Real.exp X ≤ Real.exp x := Real.exp_le_exp.mpr hx
        have h1 : Real.exp (-X) * Real.exp X = 1 := by rw [← Real.exp_add]; simp
        calc (1 : ℝ) = Real.exp (-X) * Real.exp X := h1.symm
          _ ≤ n * Real.exp x := mul_le_mul hn' hex (Real.exp_pos _).le (Nat.cast_nonneg n)
      · rw [Set.indicator_of_notMem hnA]
    have heq : (∫ x in Ici X, ‖F n x‖) = ∫ x in Ici X, F n x :=
      setIntegral_congr_fun measurableSet_Ici fun x hx => Real.norm_of_nonneg (hpos x hx)
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _), heq, hIF]
    by_cases hnA : n ∈ A
    · rw [Set.indicator_of_mem hnA]
    · rw [Set.indicator_of_notMem hnA]
      exact thetaAtomFluxPotential_nonneg n X
  have hsum : Summable fun n => ∫ x in Ici X, ‖F n x‖ :=
    Summable.of_norm_bounded_eventually (summable_thetaAtomFluxPotential X) hnorm
  have htsum : ∀ x, (∑' n, F n x) = Real.exp (x / 2) * thetaAtomSum A x := by
    intro x
    simp only [F, thetaAtomSum]
    rw [tsum_mul_left]
  constructor
  · have h := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hF hsum
    exact h.congr (Eventually.of_forall fun x => htsum x)
  · have h := integral_tsum_of_summable_integral_norm hF hsum
    rw [← tsum_congr hIF, h]
    exact integral_congr_ae (Eventually.of_forall fun x => (htsum x).symm)

/-- **Flux of any atom sum.**  `b(t) = 2π ∑_{n ∈ A} n² e^{-π n² t}`. -/
theorem thetaNormalizedFlux_thetaAtomSum (A : Set ℕ) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaAtomSum A) t =
      ∑' n : ℕ, A.indicator (fun m => 2 * Real.pi * (m : ℝ) ^ 2 * Real.exp (-Real.pi * (m : ℝ) ^ 2 * t)) n := by
  rw [thetaNormalizedFlux, (setIntegral_Ici_exp_half_mul_thetaAtomSum A _).2, ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n ∈ A
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn, thetaAtomFluxPotential]
    have h3 : Real.exp (3 * (Real.log t / 2)) = t ^ (3 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos ht]; ring_nf
    have h2 : Real.exp (2 * (Real.log t / 2)) = t := by
      rw [show 2 * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]
    rw [h3, h2]
    have ht32 : t ^ (-(3 / 2 : ℝ)) * t ^ (3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add ht]; simp
    calc t ^ (-(3 / 2 : ℝ)) * (2 * Real.pi * (n : ℝ) ^ 2 * t ^ (3 / 2 : ℝ) *
          Real.exp (-Real.pi * (n : ℝ) ^ 2 * t)) =
        (t ^ (-(3 / 2 : ℝ)) * t ^ (3 / 2 : ℝ)) *
          (2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (-Real.pi * (n : ℝ) ^ 2 * t)) := by ring
      _ = _ := by rw [ht32, one_mul]
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, mul_zero]

/-- **The completed theta flux.**  `b_k(t) = 2π ∑_{n ≥ 1} n² e^{-π n² t}`. -/
theorem thetaNormalizedFlux_thetaCuspFullSource {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux thetaCuspFullSource t =
      ∑' n : ℕ, 2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) := by
  rw [← thetaAtomSum_univ, thetaNormalizedFlux_thetaAtomSum _ ht]
  simp


/-- **Translation law of the flux.**  `b_{f(·+s)}(t) = e^{5s/2} b_f(e^{2s} t)`. -/
theorem thetaNormalizedFlux_comp_add (f : ℝ → ℝ) (s : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (fun x => f (x + s)) t =
      Real.exp (5 * s / 2) * thetaNormalizedFlux f (Real.exp (2 * s) * t) := by
  unfold thetaNormalizedFlux
  set a := Real.log t / 2
  have hlog : Real.log (Real.exp (2 * s) * t) / 2 = a + s := by
    rw [Real.log_mul (Real.exp_pos _).ne' ht.ne', Real.log_exp]
    simp only [a]
    ring
  rw [hlog]
  have hint : (∫ x in Ici a, Real.exp (x / 2) * f (x + s)) =
      Real.exp (-s / 2) * ∫ y in Ici (a + s), Real.exp (y / 2) * f y := by
    rw [← integral_indicator measurableSet_Ici, ← integral_const_mul,
      ← integral_indicator measurableSet_Ici]
    set G : ℝ → ℝ := fun y => (Ici (a + s)).indicator
      (fun y => Real.exp (-s / 2) * (Real.exp (y / 2) * f y)) y
    have h := integral_add_right_eq_self (μ := volume) G s
    rw [← h]
    apply integral_congr_ae
    filter_upwards with x
    simp only [G, Set.indicator_apply, mem_Ici, add_le_add_iff_right]
    split_ifs
    · rw [← mul_assoc, ← Real.exp_add]
      ring_nf
    · rfl
  rw [hint]
  have hts : (Real.exp (2 * s) * t) ^ (-(3 / 2 : ℝ)) =
      Real.exp (-3 * s) * t ^ (-(3 / 2 : ℝ)) := by
    rw [Real.mul_rpow (Real.exp_pos _).le ht.le, ← Real.exp_mul]
    ring_nf
  rw [hts]
  have hexp : Real.exp (-s / 2) = Real.exp (5 * s / 2) * Real.exp (-3 * s) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  ring

/-- The flux at `e^{2X}` is the tail integral from `X`, rescaled by `e^{-3X}`. -/
theorem thetaNormalizedFlux_exp (f : ℝ → ℝ) (X : ℝ) :
    thetaNormalizedFlux f (Real.exp (2 * X)) =
      Real.exp (-3 * X) * ∫ x in Ioi X, Real.exp (x / 2) * f x := by
  unfold thetaNormalizedFlux
  rw [Real.log_exp, show 2 * X / 2 = X by ring, integral_Ici_eq_integral_Ioi, ← Real.exp_mul]
  ring_nf

/-- **The flux determines its continuous source.**  `f(x) = -e^{-x/2} d/dx[e^{3x} b_f(e^{2x})]`. -/
theorem eq_of_thetaNormalizedFlux_eq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfi : ∀ X, IntegrableOn (fun x => Real.exp (x / 2) * f x) (Ioi X))
    (hgi : ∀ X, IntegrableOn (fun x => Real.exp (x / 2) * g x) (Ioi X))
    (h : ∀ t, 0 < t → thetaNormalizedFlux f t = thetaNormalizedFlux g t) : f = g := by
  have htail : ∀ (φ : ℝ → ℝ), Continuous φ → (∀ X, IntegrableOn φ (Ioi X)) → ∀ X,
      HasDerivAt (fun Y => ∫ x in Ioi Y, φ x) (-φ X) X := by
    intro φ hφ hφi X
    have heq : (fun Y => ∫ x in Ioi Y, φ x) = fun Y => (∫ x in Ioi 0, φ x) - ∫ x in (0 : ℝ)..Y, φ x := by
      funext Y
      rw [← intervalIntegral.integral_interval_add_Ioi (hφi 0) (hφi Y)]
      ring
    rw [heq]
    exact (intervalIntegral.integral_hasDerivAt_right (hφ.intervalIntegrable _ _)
      (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt).const_sub _
  have hT : (fun Y => ∫ x in Ioi Y, Real.exp (x / 2) * f x) =
      fun Y => ∫ x in Ioi Y, Real.exp (x / 2) * g x := by
    funext Y
    have h1 := thetaNormalizedFlux_exp f Y
    have h2 := thetaNormalizedFlux_exp g Y
    rw [h (Real.exp (2 * Y)) (Real.exp_pos _), h2] at h1
    have hne : Real.exp (-3 * Y) ≠ 0 := (Real.exp_pos _).ne'
    exact (mul_left_cancel₀ hne h1).symm
  funext X
  have hdf := htail (fun x => Real.exp (x / 2) * f x) (by fun_prop) hfi X
  have hdg := htail (fun x => Real.exp (x / 2) * g x) (by fun_prop) hgi X
  rw [hT] at hdf
  have := neg_injective (hdf.unique hdg)
  exact mul_left_cancel₀ (Real.exp_pos _).ne' this


theorem completelyMonotoneOn_zero : CompletelyMonotoneOn (fun _ : ℝ => (0 : ℝ)) := by
  refine ⟨fun k δ _ t _ => ?_, continuousOn_const⟩
  rw [fwdDiff_iter_eq_sum_shift]
  simp

/-- With injective rates, the singleton mass of an atomic measure is the weight itself. -/
theorem atomicMeasure_singleton_of_injective {ι : Type*} (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (hinj : Function.Injective lam) (j : ι) :
    atomicMeasure w lam {lam j} = ENNReal.ofReal (w j) := by
  rw [atomicMeasure_singleton w lam hw hs]
  congr 1
  rw [tsum_eq_single j]
  · simp
  · intro i hi
    rw [if_neg (fun h => hi (hinj h))]

/-- A finite measure dominated by an injective atomic measure is atomic with its singleton masses as
weights. -/
theorem eq_atomicMeasure_of_le {ι : Type*} [Countable ι] (w lam : ι → ℝ)
    (hinj : Function.Injective lam) {τ : Measure ℝ} [IsFiniteMeasure τ]
    (hle : τ ≤ atomicMeasure w lam) :
    τ = atomicMeasure (fun i => τ.real {lam i}) lam := by
  have hmeasR : MeasurableSet (range lam) := (Set.countable_range lam).measurableSet
  have hcompl : τ (range lam)ᶜ = 0 := by
    apply le_antisymm _ bot_le
    refine (hle _).trans (le_of_eq ?_)
    rw [atomicMeasure_apply _ _ hmeasR.compl]
    apply ENNReal.tsum_eq_zero.mpr
    intro i
    rw [Set.indicator_of_notMem (by simp), mul_zero]
  ext s hs
  rw [atomicMeasure_apply _ _ hs]
  have h1 : τ s = τ (s ∩ range lam) := by
    have hdiff : τ (s \ range lam) = 0 :=
      measure_mono_null (fun x hx => hx.2) hcompl
    rw [← measure_inter_add_sdiff s hmeasR, hdiff, add_zero]
  have hcount : (s ∩ range lam).Countable := (Set.countable_range lam).mono inter_subset_right
  have h2 : τ (s ∩ range lam) = ∑' b : ↥(s ∩ range lam), τ {(b : ℝ)} := by
    have := tsum_measure_preimage_singleton (μ := τ) hcount (f := id)
      (fun y _ => measurableSet_singleton y)
    simpa using this.symm
  rw [h1, h2, tsum_subtype (s ∩ range lam) (fun b => τ {b})]
  have hsupp : Function.support ((s ∩ range lam).indicator fun b => τ {b}) ⊆ range lam :=
    fun b hb => (Set.mem_of_indicator_ne_zero hb).2
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro i
  by_cases hi : lam i ∈ s
  · rw [Set.indicator_of_mem (show lam i ∈ s ∩ range lam from ⟨hi, mem_range_self i⟩),
      Set.indicator_of_mem hi, Pi.one_apply,
      mul_one, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top τ _)]
  · rw [Set.indicator_of_notMem (show lam i ∉ s ∩ range lam from fun h => hi h.1),
      Set.indicator_of_notMem hi, mul_zero]

/-- Total coefficient at an injective rate is the coefficient itself. -/
theorem tsum_ite_lam_eq {ι : Type*} (c lam : ι → ℝ) (hinj : Function.Injective lam) (j : ι) :
    (∑' i, if lam i = lam j then c i else 0) = c j := by
  rw [tsum_eq_single j]
  · simp
  · intro i hi
    rw [if_neg (fun h => hi (hinj h))]

/-- **Coefficient uniqueness** for absolutely convergent exponential sums with injective rates. -/
theorem exp_coeff_unique {ι : Type*} [Countable ι] (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hinj : Function.Injective lam) {v v' : ι → ℝ} {T : ℝ}
    (hv : ∀ t, T < t → Summable fun i => |v i| * Real.exp (-lam i * t))
    (hv' : ∀ t, T < t → Summable fun i => |v' i| * Real.exp (-lam i * t))
    (heq : ∀ t, T < t → (∑' i, v i * Real.exp (-lam i * t)) = ∑' i, v' i * Real.exp (-lam i * t)) :
    v = v' := by
  have key : ∀ (a b : ι → ℝ),
      (∀ t, T < t → Summable fun i => |a i| * Real.exp (-lam i * t)) →
      (∀ t, T < t → Summable fun i => |b i| * Real.exp (-lam i * t)) →
      (∀ t, T < t → (∑' i, a i * Real.exp (-lam i * t)) = ∑' i, b i * Real.exp (-lam i * t)) →
      ∀ j, b j ≤ a j := by
    intro a b ha hb hab j
    set c : ι → ℝ := fun i => (a i - b i) * Real.exp (-lam i * T)
    have hcs : ∀ s, 0 < s → Summable fun i => |c i| * Real.exp (-lam i * s) := by
      intro s hs
      refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
        ((ha (T + s) (by linarith)).add (hb (T + s) (by linarith)))
      simp only [c, abs_mul, abs_of_pos (Real.exp_pos _)]
      rw [mul_assoc, ← Real.exp_add, show -lam i * T + -lam i * s = -lam i * (T + s) by ring]
      nlinarith [abs_sub (a i) (b i), Real.exp_pos (-lam i * (T + s))]
    have hsumm : ∀ (d : ι → ℝ) (t : ℝ), Summable (fun i => |d i| * Real.exp (-lam i * t)) →
        Summable (fun i => d i * Real.exp (-lam i * t)) := fun d t h =>
      Summable.of_norm (h.congr fun i => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])
    have hzero : EqOn (fun _ : ℝ => (0 : ℝ)) (fun s => ∑' i, c i * Real.exp (-lam i * s))
        (Ioi 0) := by
      intro s hs
      have hs' : (0 : ℝ) < s := hs
      have hTs : T < T + s := by linarith
      have e : ∀ i, c i * Real.exp (-lam i * s) =
          a i * Real.exp (-lam i * (T + s)) - b i * Real.exp (-lam i * (T + s)) := by
        intro i
        simp only [c]
        rw [show -lam i * (T + s) = -lam i * T + -lam i * s by ring, Real.exp_add]
        ring
      simp only
      rw [tsum_congr e, (hsumm a _ (ha _ hTs)).tsum_sub (hsumm b _ (hb _ hTs)), hab _ hTs, sub_self]
    have hCM := completelyMonotoneOn_zero.congr_Ioi hzero
    have h := tsum_coeff_nonneg_of_completelyMonotoneOn c lam hlam hcs hCM (lam j)
    rw [tsum_ite_lam_eq c lam hinj j] at h
    simp only [c] at h
    have := nonneg_of_mul_nonneg_left h (Real.exp_pos _)
    linarith
  funext j
  exact le_antisymm (key v' v hv' hv (fun t ht => (heq t ht).symm) j) (key v v' hv hv' heq j)

private theorem integrable_exp_of_carried {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ν (Ici 0)ᶜ = 0) {s : ℝ} (hs : 0 ≤ s) : Integrable (fun r => Real.exp (-s * r)) ν := by
  refine Integrable.mono' (integrable_const 1)
    (by fun_prop : Continuous fun r : ℝ => Real.exp (-s * r)).aestronglyMeasurable ?_
  have hae : ∀ᵐ r ∂ν, r ∈ Ici (0 : ℝ) := by
    rw [ae_iff]
    exact hν
  filter_upwards [hae] with r hr
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [show (0 : ℝ) ≤ r from hr])

/-- Local form of the representation on `(t₀, ∞)`. -/
private theorem exists_dominated_exp_representation_local {ι : Type*} [Countable ι]
    (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hlam : ∀ i, 0 ≤ lam i) (hinj : Function.Injective lam)
    (hsum : ∀ t, 0 < t → Summable fun i => w i * Real.exp (-lam i * t)) {H₁ H₂ : ℝ → ℝ}
    (h₁ : CompletelyMonotoneOn H₁) (h₂ : CompletelyMonotoneOn H₂)
    (hadd : ∀ t, 0 < t → H₁ t + H₂ t = ∑' i, w i * Real.exp (-lam i * t)) {t₀ : ℝ}
    (ht₀ : 0 < t₀) :
    ∃ v : ι → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ w i) ∧
      ∀ t, t₀ < t → H₁ t = ∑' i, v i * Real.exp (-lam i * t) := by
  have hlimit : ∀ H : ℝ → ℝ, CompletelyMonotoneOn H →
      Tendsto (fun s => H (t₀ + s)) (𝓝[>] 0) (𝓝 (H t₀)) := by
    intro H hH
    have hcont : ContinuousAt H t₀ := hH.2.continuousAt (Ioi_mem_nhds ht₀)
    have hl : Tendsto (fun s : ℝ => t₀ + s) (𝓝[>] 0) (𝓝 t₀) := by
      have hc : Continuous fun s : ℝ => t₀ + s := by fun_prop
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    exact hcont.tendsto.comp hl
  obtain ⟨τ₁, hτ₁, hτ₁s, hτ₁L⟩ := exists_finiteLaplaceMeasure_of_completelyMonotoneOn
    (completelyMonotoneOn_comp_add_left h₁ ht₀.le) (hlimit H₁ h₁)
  obtain ⟨τ₂, hτ₂, hτ₂s, hτ₂L⟩ := exists_finiteLaplaceMeasure_of_completelyMonotoneOn
    (completelyMonotoneOn_comp_add_left h₂ ht₀.le) (hlimit H₂ h₂)
  set u : ι → ℝ := fun i => w i * Real.exp (-lam i * t₀)
  have hu : ∀ i, 0 ≤ u i := fun i => mul_nonneg (hw i) (Real.exp_pos _).le
  have hus : Summable u := hsum t₀ ht₀
  haveI := isFiniteMeasure_atomicMeasure u lam hu hus
  have hν := atomicMeasure_compl_Ici u lam hlam
  have hmeas : τ₁ + τ₂ = atomicMeasure u lam := by
    apply measure_eq_of_laplace_eq
    · rw [Measure.add_apply, hτ₁s, hτ₂s, add_zero]
    · exact hν
    · intro s hs
      rw [integral_add_measure (integrable_exp_of_carried hτ₁s hs.le)
        (integrable_exp_of_carried hτ₂s hs.le), ← hτ₁L s hs, ← hτ₂L s hs, hadd _ (by linarith),
        integral_exp_atomicMeasure u lam hu hlam hus hs.le]
      apply tsum_congr
      intro i
      simp only [u]
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
  have hle : τ₁ ≤ atomicMeasure u lam := hmeas ▸ Measure.le_add_right le_rfl
  have hτ₁eq := eq_atomicMeasure_of_le u lam hinj hle
  set α : ι → ℝ := fun i => τ₁.real {lam i}
  have hα0 : ∀ i, 0 ≤ α i := fun i => measureReal_nonneg
  have hαu : ∀ i, α i ≤ u i := by
    intro i
    have h := hle {lam i}
    rw [atomicMeasure_singleton_of_injective u lam hu hus hinj i] at h
    simp only [α, measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (hu i) h
  have hαs : Summable α := Summable.of_nonneg_of_le hα0 hαu hus
  refine ⟨fun i => α i * Real.exp (lam i * t₀), fun i => ⟨?_, ?_⟩, fun t ht => ?_⟩
  · exact mul_nonneg (hα0 i) (Real.exp_pos _).le
  · have := mul_le_mul_of_nonneg_right (hαu i) (Real.exp_pos (lam i * t₀)).le
    calc α i * Real.exp (lam i * t₀) ≤ u i * Real.exp (lam i * t₀) := this
      _ = w i := by
        simp only [u]
        rw [mul_assoc, ← Real.exp_add, show -lam i * t₀ + lam i * t₀ = 0 by ring, Real.exp_zero,
          mul_one]
  · have hts : 0 < t - t₀ := by linarith
    have h := hτ₁L (t - t₀) hts
    simp only [add_sub_cancel] at h
    rw [h, hτ₁eq, integral_exp_atomicMeasure α lam hα0 hlam hαs hts.le]
    apply tsum_congr
    intro i
    rw [mul_assoc, ← Real.exp_add]
    ring_nf

/-- **Dominated representation.**  If two completely monotone profiles add up to a positive
exponential sum with injective rates, each of them is an exponential sum on the same rates with
weights between `0` and the original weights. -/
theorem exists_dominated_exp_representation {ι : Type*} [Countable ι] (w lam : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlam : ∀ i, 0 ≤ lam i) (hinj : Function.Injective lam)
    (hsum : ∀ t, 0 < t → Summable fun i => w i * Real.exp (-lam i * t)) {H₁ H₂ : ℝ → ℝ}
    (h₁ : CompletelyMonotoneOn H₁) (h₂ : CompletelyMonotoneOn H₂)
    (hadd : ∀ t, 0 < t → H₁ t + H₂ t = ∑' i, w i * Real.exp (-lam i * t)) :
    ∃ v : ι → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ w i) ∧
      ∀ t, 0 < t → H₁ t = ∑' i, v i * Real.exp (-lam i * t) := by
  have habs : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ w i) → ∀ t, 0 < t →
      Summable fun i => |v i| * Real.exp (-lam i * t) := by
    intro v hv t ht
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hsum t ht)
    rw [abs_of_nonneg (hv i).1]
    exact mul_le_mul_of_nonneg_right (hv i).2 (Real.exp_pos _).le
  obtain ⟨v, hv, hrep⟩ := exists_dominated_exp_representation_local w lam hw hlam hinj hsum
    h₁ h₂ hadd one_pos
  refine ⟨v, hv, fun t ht => ?_⟩
  set t₀ := min 1 (t / 2)
  have ht₀ : 0 < t₀ := lt_min one_pos (by linarith)
  obtain ⟨v', hv', hrep'⟩ := exists_dominated_exp_representation_local w lam hw hlam hinj hsum
    h₁ h₂ hadd ht₀
  have heq : v' = v := by
    apply exp_coeff_unique lam hlam hinj (T := 1)
    · exact fun s hs => habs v' hv' s (by linarith)
    · exact fun s hs => habs v hv s (by linarith)
    · intro s hs
      rw [← hrep' s (lt_of_le_of_lt (min_le_left _ _) hs), ← hrep s hs]
  rw [← heq]
  exact hrep' t (lt_of_le_of_lt (min_le_right _ _) (by linarith))

end RHTower
