import GaloisForLFunctions.HTGeometry.ChronologicalTensor.ArcsineMixturePotential
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicChebyshevOptimizer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# The upper bound `t_m ≤ 2^K 4^{⌊m/K⌋+1} ρ^m` by block Chebyshev products

In the coordinate `r = (1-t²)/4`, `t ∈ [0,1]`, the weight is `W(r) = 1 - t`, and the monic
degree-`d` Chebyshev polynomial of the `r`-interval `[(1-a²)/4, 1/4]` satisfies
`|B(r)| ≤ 2 (g(a,t)²/4)^d` with the arcsine gauge `g`.  Split `[0, b]` into `K` blocks of
`h`-mass `d_i/m`, `d_i = ⌊(i+1)m/K⌋ - ⌊im/K⌋`, and take the product of the block polynomials at the
left endpoints `α_i`.  Since `a ↦ log g(a,t)` decreases on `[0,t]` and increases after `t`, the
left-endpoint sums exceed `m ∫_0^b log g(a,t) h(a) da` by at most `max d_i · log 2`, and the
equilibrium inequality `∫_0^b log g(a,t) h(a) da ≤ log C - ½ log(1-t)` with `C²/4 = ρ` gives the
bound.
-/

open MeasureTheory Set Filter intervalIntegral Polynomial
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-! ### Chebyshev growth -/

theorem chebyshevT_le_pow {y : ℝ} (hy : 1 ≤ y) (d : ℕ) :
    (Chebyshev.T ℝ d).eval y ≤ (y + Real.sqrt (y ^ 2 - 1)) ^ d := by
  have h := Chebyshev.T_real_cosh (Real.arcosh y) d
  rw [Real.cosh_arcosh hy, Int.cast_natCast] at h
  rw [h, Real.cosh_eq, ← Real.exp_arcosh hy, ← Real.exp_nat_mul]
  have h0 : 0 ≤ (d : ℝ) * Real.arcosh y := mul_nonneg (Nat.cast_nonneg d) (Real.arcosh_nonneg hy)
  have : Real.exp (-((d : ℝ) * Real.arcosh y)) ≤ Real.exp ((d : ℝ) * Real.arcosh y) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

theorem abs_chebyshevT_le {x : ℝ} (hx : 1 ≤ |x|) (d : ℕ) :
    |(Chebyshev.T ℝ d).eval x| ≤ (|x| + Real.sqrt (x ^ 2 - 1)) ^ d := by
  have key : |(Chebyshev.T ℝ d).eval x| = (Chebyshev.T ℝ d).eval |x| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hx ⊢
      exact abs_of_nonneg (by linarith [Chebyshev.one_le_eval_T_real (d : ℤ) hx])
    · have hx' : x = -|x| := by rw [abs_of_neg h]; ring
      rw [hx', Chebyshev.T_eval_neg, abs_mul, abs_neg, abs_abs]
      simp only [abs_of_nonneg (by linarith [Chebyshev.one_le_eval_T_real (d : ℤ) hx] :
        0 ≤ (Chebyshev.T ℝ d).eval |x|)]
      simp
  rw [key, ← sq_abs x]
  exact chebyshevT_le_pow hx d

/-! ### The block polynomials -/

/-- The affine map `r ↦ 8(r - (1-a²)/4)/a² - 1`, sending `[(1-a²)/4, 1/4]` onto `[-1, 1]`. -/
def blockAffine (a : ℝ) : Polynomial ℝ := C (8 / a ^ 2) * X - C (2 * (1 - a ^ 2) / a ^ 2 + 1)

theorem eval_blockAffine {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    (blockAffine a).eval ((1 - t ^ 2) / 4) = 1 - 2 * t ^ 2 / a ^ 2 := by
  simp only [blockAffine, eval_sub, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem natDegree_blockAffine {a : ℝ} (ha : a ≠ 0) : (blockAffine a).natDegree = 1 := by
  rw [blockAffine, natDegree_sub_C, natDegree_C_mul_X _ (by positivity)]

theorem leadingCoeff_blockAffine {a : ℝ} (ha : a ≠ 0) :
    (blockAffine a).leadingCoeff = 8 / a ^ 2 := by
  rw [leadingCoeff, natDegree_blockAffine ha]
  simp [blockAffine, coeff_one]

/-- The monic degree-`d` Chebyshev polynomial of the `r`-interval `[(1-a²)/4, 1/4]`, and
`(r - 1/4)^d` when `a = 0` or `d = 0`. -/
def chebyshevBlock (a : ℝ) (d : ℕ) : Polynomial ℝ :=
  if a = 0 ∨ d = 0 then (X - C (1 / 4)) ^ d
  else C (2 * (a ^ 2 / 16) ^ d) * (Chebyshev.T ℝ d).comp (blockAffine a)

theorem chebyshevBlock_monic_natDegree (a : ℝ) (d : ℕ) :
    (chebyshevBlock a d).Monic ∧ (chebyshevBlock a d).natDegree = d := by
  unfold chebyshevBlock
  split_ifs with h
  · exact ⟨(monic_X_sub_C _).pow d, by rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C,
      mul_one]⟩
  push Not at h
  obtain ⟨ha, hd⟩ := h
  have hc : (2 * (a ^ 2 / 16) ^ d : ℝ) ≠ 0 := by positivity
  have hdeg : ((Chebyshev.T ℝ d).comp (blockAffine a)).natDegree = d := by
    rw [natDegree_comp, natDegree_blockAffine ha, Chebyshev.natDegree_T]; simp
  refine ⟨?_, by rw [natDegree_C_mul hc, hdeg]⟩
  have hq1 : (blockAffine a).natDegree ≠ 0 := by rw [natDegree_blockAffine ha]; exact one_ne_zero
  rw [Monic, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp hq1, leadingCoeff_blockAffine ha,
    Chebyshev.leadingCoeff_T, Chebyshev.natDegree_T]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  simp only [Int.natAbs_natCast, Nat.succ_sub_one]
  have hq : a ^ 2 / 16 * (8 / a ^ 2) = 1 / 2 := by field_simp; norm_num
  calc 2 * (a ^ 2 / 16) ^ (e + 1) * (2 ^ e * (8 / a ^ 2) ^ (e + 1))
      = 2 ^ (e + 1) * (a ^ 2 / 16 * (8 / a ^ 2)) ^ (e + 1) := by rw [mul_pow]; ring
    _ = 1 := by rw [hq, ← mul_pow]; norm_num

/-- **The block bound** `|B(r)| ≤ 2 (g(a,t)²/4)^d` at `r = (1-t²)/4`. -/
theorem abs_eval_chebyshevBlock_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (d : ℕ) :
    |(chebyshevBlock a d).eval ((1 - t ^ 2) / 4)| ≤ 2 * (arcsineGauge a t ^ 2 / 4) ^ d := by
  unfold chebyshevBlock
  split_ifs with h
  · rw [eval_pow, eval_sub, eval_X, eval_C, show (1 - t ^ 2) / 4 - 1 / 4 = -(t ^ 2 / 4) by ring,
      abs_pow, abs_neg, abs_of_nonneg (by positivity)]
    rcases h with rfl | rfl
    · rw [arcsineGauge_zero_left ht]
      linarith [pow_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2 / 4) d]
    · norm_num
  push Not at h
  obtain ⟨ha0, hd⟩ := h
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  rw [eval_mul, eval_C, eval_comp, eval_blockAffine ha0, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (a ^ 2 / 16) ^ d), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rcases le_or_gt t a with hta | hat
  · have hx : |1 - 2 * t ^ 2 / a ^ 2| ≤ 1 := by
      rw [abs_le]
      have h1 : 0 ≤ 2 * t ^ 2 / a ^ 2 := by positivity
      have h2 : 2 * t ^ 2 / a ^ 2 ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      constructor <;> linarith
    rw [arcsineGauge_of_le hta ht, show (a / 2) ^ 2 / 4 = a ^ 2 / 16 by ring]
    calc (a ^ 2 / 16) ^ d * |(Chebyshev.T ℝ d).eval (1 - 2 * t ^ 2 / a ^ 2)|
        ≤ (a ^ 2 / 16) ^ d * 1 :=
          mul_le_mul_of_nonneg_left (Chebyshev.abs_eval_T_real_le_one _ hx) (by positivity)
      _ = (a ^ 2 / 16) ^ d := mul_one _
  · set σ := Real.sqrt (t ^ 2 - a ^ 2) with hσ
    have hσ2 : σ ^ 2 = t ^ 2 - a ^ 2 := Real.sq_sqrt (by nlinarith)
    have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
    have hx : |1 - 2 * t ^ 2 / a ^ 2| = 2 * t ^ 2 / a ^ 2 - 1 := by
      rw [abs_of_neg, neg_sub]
      rw [sub_neg, lt_div_iff₀ (by positivity)]; nlinarith
    have hx1 : 1 ≤ |1 - 2 * t ^ 2 / a ^ 2| := by
      rw [hx, le_sub_iff_add_le, le_div_iff₀ (by positivity)]; nlinarith
    have hsq : Real.sqrt ((1 - 2 * t ^ 2 / a ^ 2) ^ 2 - 1) = 2 * t * σ / a ^ 2 := by
      rw [show (1 - 2 * t ^ 2 / a ^ 2) ^ 2 - 1 = (2 * t * σ / a ^ 2) ^ 2 by
        field_simp; linear_combination (-(4 * t ^ 2)) * hσ2]
      exact Real.sqrt_sq (by positivity)
    have hsum : |1 - 2 * t ^ 2 / a ^ 2| + Real.sqrt ((1 - 2 * t ^ 2 / a ^ 2) ^ 2 - 1) =
        (t + σ) ^ 2 / a ^ 2 := by
      rw [hx, hsq]; field_simp; linear_combination (-1 : ℝ) * hσ2
    have hg : arcsineGauge a t = (t + σ) / 2 := by
      rw [arcsineGauge, max_eq_right hat.le]
    calc (a ^ 2 / 16) ^ d * |(Chebyshev.T ℝ d).eval (1 - 2 * t ^ 2 / a ^ 2)|
        ≤ (a ^ 2 / 16) ^ d * ((t + σ) ^ 2 / a ^ 2) ^ d := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← hsum]; exact abs_chebyshevT_le hx1 d
      _ = (arcsineGauge a t ^ 2 / 4) ^ d := by
          rw [← mul_pow, hg]; congr 1; field_simp; ring

/-! ### Mass nodes -/

/-- The mass function `M(x) = ∫_0^x h`. -/
def recoveryMass (x : ℝ) : ℝ := ∫ a in (0 : ℝ)..x, recoveryDensity a

theorem intervalIntegrable_recoveryDensity {c d : ℝ} (hc : c ∈ Icc 0 recoveryEdge)
    (hd : d ∈ Icc 0 recoveryEdge) : IntervalIntegrable recoveryDensity volume c d := by
  refine ContinuousOn.intervalIntegrable ((continuousOn_recoveryDensity recoveryEdge_mem.1.le
    recoveryEdge_mem.2).mono ?_)
  intro x hx
  rw [mem_uIcc] at hx
  constructor <;> rcases hx with hx | hx <;> linarith [hc.1, hc.2, hd.1, hd.2, hx.1, hx.2,
    recoveryEdge_mem.1]

theorem integral_recoveryDensity_eq_mass_sub {c d : ℝ} (hc : c ∈ Icc 0 recoveryEdge)
    (hd : d ∈ Icc 0 recoveryEdge) :
    ∫ a in c..d, recoveryDensity a = recoveryMass d - recoveryMass c :=
  (integral_interval_sub_left
    (intervalIntegrable_recoveryDensity ⟨le_rfl, recoveryEdge_mem.1.le⟩ hd)
    (intervalIntegrable_recoveryDensity ⟨le_rfl, recoveryEdge_mem.1.le⟩ hc)).symm

theorem recoveryMass_zero : recoveryMass 0 = 0 := by simp [recoveryMass]

theorem recoveryMass_edge : recoveryMass recoveryEdge = 1 := integral_recoveryDensity_edge

theorem continuousOn_recoveryMass : ContinuousOn recoveryMass (Icc 0 recoveryEdge) := by
  have hi : IntegrableOn recoveryDensity (uIcc 0 recoveryEdge) volume := by
    rw [uIcc_of_le recoveryEdge_mem.1.le]
    exact ((continuousOn_recoveryDensity recoveryEdge_mem.1.le recoveryEdge_mem.2).mono
      (Icc_subset_Icc (by linarith [recoveryEdge_mem.1]) le_rfl)).integrableOn_Icc
  have h := continuousOn_primitive_interval hi
  rw [uIcc_of_le recoveryEdge_mem.1.le] at h
  exact h

theorem strictMonoOn_recoveryMass : StrictMonoOn recoveryMass (Icc 0 recoveryEdge) := by
  intro x hx y hy hxy
  rw [← sub_pos, ← integral_recoveryDensity_eq_mass_sub hx hy]
  exact intervalIntegral_pos_of_pos_on (intervalIntegrable_recoveryDensity hx hy)
    (fun a ha => recoveryDensity_pos (hx.1.trans ha.1.le) (ha.2.trans_le hy.2 |>.trans
      recoveryEdge_mem.2)) hxy

theorem exists_recoveryMass_eq {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc 0 recoveryEdge, recoveryMass x = y := by
  have h := intermediate_value_Icc recoveryEdge_mem.1.le continuousOn_recoveryMass
  rw [recoveryMass_zero, recoveryMass_edge] at h
  exact h hy

/-- The node of mass `y ∈ [0,1]`: `M(node y) = y`. -/
def recoveryNode (y : ℝ) : ℝ :=
  if hy : y ∈ Icc (0 : ℝ) 1 then Classical.choose (exists_recoveryMass_eq hy) else 0

theorem recoveryNode_spec {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    recoveryNode y ∈ Icc 0 recoveryEdge ∧ recoveryMass (recoveryNode y) = y := by
  rw [recoveryNode, dif_pos hy]
  exact Classical.choose_spec (exists_recoveryMass_eq hy)

theorem recoveryNode_mono {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1)
    (hyz : y ≤ z) : recoveryNode y ≤ recoveryNode z := by
  rw [← strictMonoOn_recoveryMass.le_iff_le (recoveryNode_spec hy).1 (recoveryNode_spec hz).1,
    (recoveryNode_spec hy).2, (recoveryNode_spec hz).2]
  exact hyz

theorem recoveryNode_zero : recoveryNode 0 = 0 :=
  strictMonoOn_recoveryMass.injOn (recoveryNode_spec ⟨le_rfl, zero_le_one⟩).1
    ⟨le_rfl, recoveryEdge_mem.1.le⟩ (by rw [(recoveryNode_spec ⟨le_rfl, zero_le_one⟩).2,
      recoveryMass_zero])

theorem recoveryNode_one : recoveryNode 1 = recoveryEdge :=
  strictMonoOn_recoveryMass.injOn (recoveryNode_spec ⟨zero_le_one, le_rfl⟩).1
    ⟨recoveryEdge_mem.1.le, le_rfl⟩ (by rw [(recoveryNode_spec ⟨zero_le_one, le_rfl⟩).2,
      recoveryMass_edge])

theorem integral_recoveryDensity_nodes {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    ∫ a in recoveryNode y..recoveryNode z, recoveryDensity a = z - y := by
  rw [integral_recoveryDensity_eq_mass_sub (recoveryNode_spec hy).1 (recoveryNode_spec hz).1,
    (recoveryNode_spec hy).2, (recoveryNode_spec hz).2]

/-! ### The block sum inequality -/

/-- For `f` decreasing on `[0,t]`, increasing after `t`, and `φ = f ∘ min(·,t)`:
`f(α) - f(a) ≤ φ(α) - φ(β)` whenever `0 ≤ α ≤ a ≤ β`. -/
theorem valley_increment_le {f : ℝ → ℝ} {t α a β : ℝ} (hf1 : AntitoneOn f (Icc 0 t))
    (hf2 : MonotoneOn f (Ici t)) (ht : 0 ≤ t) (hα : 0 ≤ α) (hαa : α ≤ a) (haβ : a ≤ β) :
    f α - f a ≤ f (min α t) - f (min β t) := by
  rcases le_or_gt a t with hat | hta
  · rw [min_eq_left (hαa.trans hat)]
    have h1 : f (min β t) ≤ f a :=
      hf1 ⟨hα.trans hαa, hat⟩ ⟨le_min (hα.trans (hαa.trans haβ)) ht, min_le_right _ _⟩
        (le_min haβ hat)
    linarith
  · rw [min_eq_right (hta.le.trans haβ)]
    rcases le_or_gt α t with hαt | htα
    · rw [min_eq_left hαt]
      have := hf2 (mem_Ici.mpr le_rfl) (mem_Ici.mpr hta.le) hta.le
      linarith
    · rw [min_eq_right htα.le]
      have := hf2 (mem_Ici.mpr htα.le) (mem_Ici.mpr hta.le) hαa
      linarith

theorem log_arcsineGauge_antitoneOn {t : ℝ} (ht : 0 < t) :
    AntitoneOn (fun a => Real.log (arcsineGauge a t)) (Icc 0 t) :=
  fun _ hx _ hy hxy => Real.log_le_log (arcsineGauge_pos ht) (arcsineGauge_antitoneOn hx hy hxy)

theorem log_arcsineGauge_monotoneOn {t : ℝ} (ht : 0 < t) :
    MonotoneOn (fun a => Real.log (arcsineGauge a t)) (Ici t) :=
  fun _ hx _ hy hxy => Real.log_le_log (arcsineGauge_pos ht)
    (arcsineGauge_monotoneOn ht.le hx hy hxy)

/-- **The block sum inequality.**  For masses `0 = y_0 ≤ … ≤ y_K = 1` with increments at most `D`
and nodes `α_i = node(y_i)`,
`Σ (y_{i+1} - y_i) log g(α_i, t) ≤ ∫_0^b log g(a,t) h(a) da + D log 2`. -/
theorem sum_log_arcsineGauge_le {t : ℝ} (ht0 : 0 < t) {K : ℕ} {y : ℕ → ℝ}
    (hy : ∀ i ≤ K, y i ∈ Icc (0 : ℝ) 1) (hmono : ∀ i < K, y i ≤ y (i + 1)) (hy0 : y 0 = 0)
    (hyK : y K = 1) {D : ℝ} (hD : ∀ i < K, y (i + 1) - y i ≤ D) :
    ∑ i ∈ Finset.range K, (y (i + 1) - y i) * Real.log (arcsineGauge (recoveryNode (y i)) t) ≤
      (∫ a in (0 : ℝ)..recoveryEdge, Real.log (arcsineGauge a t) * recoveryDensity a) +
        D * Real.log 2 := by
  set f : ℝ → ℝ := fun a => Real.log (arcsineGauge a t) with hf
  set α : ℕ → ℝ := fun i => recoveryNode (y i) with hα
  set φ : ℝ → ℝ := fun a => f (min a t) with hφ
  have hαmem : ∀ i ≤ K, α i ∈ Icc 0 recoveryEdge := fun i hi => (recoveryNode_spec (hy i hi)).1
  have hαmono : ∀ i < K, α i ≤ α (i + 1) := fun i hi =>
    recoveryNode_mono (hy i hi.le) (hy (i + 1) hi) (hmono i hi)
  have hint : ∀ i < K, IntervalIntegrable (fun a => f a * recoveryDensity a) volume (α i)
      (α (i + 1)) := fun i hi =>
    ((intervalIntegrable_log_arcsineGauge_mul_recoveryDensity ht0 recoveryEdge_mem.1.le
      recoveryEdge_mem.2).mono_set (by
        rw [uIcc_of_le recoveryEdge_mem.1.le]
        exact uIcc_subset_Icc (hαmem i hi.le) (hαmem (i + 1) hi)))
  have hintd : ∀ i < K, IntervalIntegrable recoveryDensity volume (α i) (α (i + 1)) :=
    fun i hi => intervalIntegrable_recoveryDensity (hαmem i hi.le) (hαmem (i + 1) hi)
  have hmass : ∀ i < K, ∫ a in α i..α (i + 1), recoveryDensity a = y (i + 1) - y i :=
    fun i hi => integral_recoveryDensity_nodes (hy i hi.le) (hy (i + 1) hi)
  -- the whole integral splits along the nodes
  have hsplit : ∑ i ∈ Finset.range K, ∫ a in α i..α (i + 1), f a * recoveryDensity a =
      ∫ a in (0 : ℝ)..recoveryEdge, f a * recoveryDensity a := by
    rw [sum_integral_adjacent_intervals hint]
    simp only [hα, hy0, hyK, recoveryNode_zero, recoveryNode_one]
  -- each block
  have hblock : ∀ i < K, (y (i + 1) - y i) * f (α i) ≤
      (∫ a in α i..α (i + 1), f a * recoveryDensity a) +
        (φ (α i) - φ (α (i + 1))) * (y (i + 1) - y i) := fun i hi => by
    have h1 : (y (i + 1) - y i) * f (α i) = ∫ a in α i..α (i + 1), f (α i) * recoveryDensity a := by
      rw [intervalIntegral.integral_const_mul, hmass i hi]; ring
    have h2 : (φ (α i) - φ (α (i + 1))) * (y (i + 1) - y i) =
        ∫ a in α i..α (i + 1), (φ (α i) - φ (α (i + 1))) * recoveryDensity a := by
      rw [intervalIntegral.integral_const_mul, hmass i hi]
    rw [h1, h2, ← integral_add (hint i hi) ((hintd i hi).const_mul _)]
    refine intervalIntegral.integral_mono_on (hαmono i hi) ((hintd i hi).const_mul _)
      ((hint i hi).add ((hintd i hi).const_mul _)) fun a ha => ?_
    have hh : 0 ≤ recoveryDensity a := (recoveryDensity_pos ((hαmem i hi.le).1.trans ha.1)
      (ha.2.trans (hαmem (i + 1) hi).2 |>.trans_lt recoveryEdge_mem.2)).le
    have hv := valley_increment_le (log_arcsineGauge_antitoneOn ht0)
      (log_arcsineGauge_monotoneOn ht0) ht0.le (hαmem i hi.le).1 ha.1 ha.2
    have : (f (α i) - f a) * recoveryDensity a ≤
        (φ (α i) - φ (α (i + 1))) * recoveryDensity a :=
      mul_le_mul_of_nonneg_right hv hh
    linarith
  -- the telescoping remainder
  have hφanti : ∀ x y, 0 ≤ x → x ≤ y → φ y ≤ φ x := fun x y hx hxy =>
    log_arcsineGauge_antitoneOn ht0 ⟨le_min hx ht0.le, min_le_right _ _⟩
      ⟨le_min (hx.trans hxy) ht0.le, min_le_right _ _⟩ (min_le_min_right _ hxy)
  have hrem : ∑ i ∈ Finset.range K, (φ (α i) - φ (α (i + 1))) * (y (i + 1) - y i) ≤
      D * Real.log 2 := by
    calc ∑ i ∈ Finset.range K, (φ (α i) - φ (α (i + 1))) * (y (i + 1) - y i)
        ≤ ∑ i ∈ Finset.range K, (φ (α i) - φ (α (i + 1))) * D := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.mp hi
          exact mul_le_mul_of_nonneg_left (hD i hi')
            (sub_nonneg.mpr (hφanti _ _ (hαmem i hi'.le).1 (hαmono i hi')))
      _ = (φ (α 0) - φ (α K)) * D := by rw [← Finset.sum_mul, Finset.sum_range_sub']
      _ ≤ Real.log 2 * D := by
          refine mul_le_mul_of_nonneg_right ?_ ((sub_nonneg.mpr (hmono 0 ?_)).trans (hD 0 ?_))
          · simp only [hφ, hα, hy0, hyK, recoveryNode_zero, recoveryNode_one, hf]
            rw [min_eq_left ht0.le, arcsineGauge_zero_left ht0.le]
            have hlow : Real.log (t / 2) ≤ Real.log (arcsineGauge (min recoveryEdge t) t) :=
              Real.log_le_log (by positivity) (half_le_arcsineGauge _ _)
            rw [Real.log_div ht0.ne' two_ne_zero] at hlow
            linarith
          all_goals
            by_contra hK
            push Not at hK
            rw [Nat.lt_one_iff.mp (by omega : K < 1)] at hyK
            rw [hy0] at hyK
            exact zero_ne_one hyK
      _ = D * Real.log 2 := mul_comm _ _
  calc ∑ i ∈ Finset.range K, (y (i + 1) - y i) * Real.log (arcsineGauge (recoveryNode (y i)) t)
      ≤ ∑ i ∈ Finset.range K, ((∫ a in α i..α (i + 1), f a * recoveryDensity a) +
          (φ (α i) - φ (α (i + 1))) * (y (i + 1) - y i)) :=
        Finset.sum_le_sum fun i hi => hblock i (Finset.mem_range.mp hi)
    _ = (∫ a in (0 : ℝ)..recoveryEdge, f a * recoveryDensity a) +
          ∑ i ∈ Finset.range K, (φ (α i) - φ (α (i + 1))) * (y (i + 1) - y i) := by
        rw [Finset.sum_add_distrib, hsplit]
    _ ≤ _ := by linarith

/-! ### The block product -/

/-- The partition indices `s_i = ⌊i m / K⌋`. -/
def blockIndex (m K i : ℕ) : ℕ := i * m / K

theorem blockIndex_mono (m K : ℕ) : Monotone (blockIndex m K) := fun _ _ hij =>
  Nat.div_le_div_right (Nat.mul_le_mul_right m hij)

theorem blockIndex_zero (m K : ℕ) : blockIndex m K 0 = 0 := by simp [blockIndex]

theorem blockIndex_self (m : ℕ) {K : ℕ} (hK : 0 < K) : blockIndex m K K = m :=
  Nat.mul_div_cancel_left m hK

theorem blockIndex_le {m K i : ℕ} (hK : 0 < K) (hi : i ≤ K) : blockIndex m K i ≤ m :=
  calc i * m / K ≤ K * m / K := Nat.div_le_div_right (Nat.mul_le_mul_right m hi)
    _ = m := Nat.mul_div_cancel_left m hK

theorem blockIndex_succ_sub_le (m K i : ℕ) (hK : 0 < K) :
    blockIndex m K (i + 1) - blockIndex m K i ≤ m / K + 1 := by
  unfold blockIndex
  rw [show (i + 1) * m = i * m + m by ring, Nat.add_div hK, Nat.add_assoc,
    Nat.add_sub_cancel_left]
  split_ifs <;> simp

theorem one_le_blockIndex_one {m K : ℕ} (hK : 0 < K) (hKm : K ≤ m) :
    1 ≤ blockIndex m K 1 - blockIndex m K 0 := by
  simp only [blockIndex, one_mul, zero_mul, Nat.zero_div, tsub_zero]
  exact (Nat.one_le_div_iff hK).mpr hKm

/-- The block product `∏_{i<K} B(α_i, d_i)`, `α_i = node(s_i/m)`, `d_i = s_{i+1} - s_i`. -/
def chebyshevBlockProduct (m K : ℕ) : Polynomial ℝ :=
  ∏ i ∈ Finset.range K, chebyshevBlock (recoveryNode ((blockIndex m K i : ℝ) / m))
    (blockIndex m K (i + 1) - blockIndex m K i)

theorem chebyshevBlockProduct_monic_natDegree (m : ℕ) {K : ℕ} (hK : 0 < K) :
    (chebyshevBlockProduct m K).Monic ∧ (chebyshevBlockProduct m K).natDegree = m := by
  unfold chebyshevBlockProduct
  refine ⟨monic_prod_of_monic _ _ fun i _ => (chebyshevBlock_monic_natDegree _ _).1, ?_⟩
  rw [natDegree_prod_of_monic _ _ fun i _ => (chebyshevBlock_monic_natDegree _ _).1]
  simp only [(chebyshevBlock_monic_natDegree _ _).2]
  rw [Finset.sum_range_tsub (blockIndex_mono m K), blockIndex_self m hK, blockIndex_zero,
    tsub_zero]

/-- **The weighted pointwise bound**
`(1-t)^m |P((1-t²)/4)| ≤ 2^K 4^{⌊m/K⌋+1} ρ^m` for `t ∈ [0,1]`. -/
theorem weighted_eval_chebyshevBlockProduct_le {m K : ℕ} (hK : 1 ≤ K) (hKm : K ≤ m) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) ^ m * |(chebyshevBlockProduct m K).eval ((1 - t ^ 2) / 4)| ≤
      2 ^ K * 4 ^ (m / K + 1) * recoveryRate ^ m := by
  have hK0 : 0 < K := hK
  have hm0 : 0 < m := lt_of_lt_of_le hK0 hKm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  set y : ℕ → ℝ := fun i => (blockIndex m K i : ℝ) / m with hy
  set d : ℕ → ℕ := fun i => blockIndex m K (i + 1) - blockIndex m K i with hd
  set g : ℕ → ℝ := fun i => arcsineGauge (recoveryNode (y i)) t with hg
  have hρ := recoveryRate_bounds
  have hymem : ∀ i ≤ K, y i ∈ Icc (0 : ℝ) 1 := fun i hi =>
    ⟨by positivity, by rw [hy, div_le_one hmR]; exact_mod_cast blockIndex_le hK0 hi⟩
  have hnode0 : ∀ i ≤ K, 0 ≤ recoveryNode (y i) := fun i hi => (recoveryNode_spec (hymem i hi)).1.1
  -- the product bound
  have hprod : |(chebyshevBlockProduct m K).eval ((1 - t ^ 2) / 4)| ≤
      2 ^ K * ∏ i ∈ Finset.range K, (g i ^ 2 / 4) ^ d i := by
    have h2 : (2 : ℝ) ^ K * ∏ i ∈ Finset.range K, (g i ^ 2 / 4) ^ d i =
        ∏ i ∈ Finset.range K, 2 * (g i ^ 2 / 4) ^ d i := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [h2, chebyshevBlockProduct, eval_prod, Finset.abs_prod]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi => ?_
    exact abs_eval_chebyshevBlock_le (hnode0 i (Finset.mem_range.mp hi).le) ht.1 _
  have hQ : (1 - t) ^ m * ∏ i ∈ Finset.range K, (g i ^ 2 / 4) ^ d i ≤
      4 ^ (m / K + 1) * recoveryRate ^ m := by
    have hR : 0 < (4 : ℝ) ^ (m / K + 1) * recoveryRate ^ m := by
      have := hρ.1; positivity
    rcases eq_or_lt_of_le ht.2 with ht1 | ht1
    · rw [ht1, sub_self, zero_pow hm0.ne', zero_mul]; exact hR.le
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · subst ht0
      have hd0 : d 0 ≠ 0 := by
        have := one_le_blockIndex_one hK0 hKm
        show blockIndex m K 1 - blockIndex m K 0 ≠ 0
        omega
      have hz : ∏ i ∈ Finset.range K, (g i ^ 2 / 4) ^ d i = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_range.mpr hK0) ?_
        have h0 : y 0 = 0 := by simp [hy, blockIndex_zero]
        have hg0 : g 0 = 0 := by
          simp only [hg]; rw [h0, recoveryNode_zero, arcsineGauge_zero_left le_rfl]
        rw [hg0]
        simp [hd0]
      rw [hz, mul_zero]; exact hR.le
    -- the logarithmic estimate for `0 < t < 1`
    have hgpos : ∀ i, 0 < g i := fun i => arcsineGauge_pos ht0
    have hLpos : 0 < (1 - t) ^ m * ∏ i ∈ Finset.range K, (g i ^ 2 / 4) ^ d i :=
      mul_pos (pow_pos (by linarith) m) (Finset.prod_pos fun i _ => by have := hgpos i; positivity)
    rw [← Real.log_le_log_iff hLpos hR]
    have hymono : ∀ i < K, y i ≤ y (i + 1) := fun i _ => by
      have : (blockIndex m K i : ℝ) ≤ blockIndex m K (i + 1) := by
        exact_mod_cast blockIndex_mono m K (Nat.le_succ i)
      exact div_le_div_of_nonneg_right this hmR.le
    have hblock : ∑ i ∈ Finset.range K, (y (i + 1) - y i) * Real.log (g i) ≤
        (∫ a in (0 : ℝ)..recoveryEdge, Real.log (arcsineGauge a t) * recoveryDensity a) +
          ((m / K + 1 : ℕ) : ℝ) / m * Real.log 2 :=
      sum_log_arcsineGauge_le ht0 (K := K) (y := y) hymem hymono
      (by simp [hy, blockIndex_zero]) (by rw [hy]; simp only [blockIndex_self m hK0]; field_simp)
      (D := ((m / K + 1 : ℕ) : ℝ) / m) (fun i _ => by
        rw [hy, ← sub_div]
        refine div_le_div_of_nonneg_right ?_ hmR.le
        rw [← Nat.cast_sub (blockIndex_mono m K (Nat.le_succ i))]
        exact_mod_cast blockIndex_succ_sub_le m K i hK0)
    have hpot := recoveryMixturePotential_le ht0 ht1
    have hC := recoveryCapacity_pos recoveryEdge_mem.1
    have hρC : Real.log recoveryRate = 2 * Real.log (recoveryCapacity recoveryEdge) -
        Real.log 4 := by
      rw [recoveryRate, ← recoveryCapacity_sq_div_four, Real.log_div (by positivity)
        (by norm_num), Real.log_pow]; push_cast; ring
    have hsumd : ∑ i ∈ Finset.range K, (d i : ℝ) = m := by
      have := (chebyshevBlockProduct_monic_natDegree m hK0).2
      rw [← Nat.cast_sum]
      congr 1
      simp only [hd]
      rw [Finset.sum_range_tsub (blockIndex_mono m K), blockIndex_self m hK0, blockIndex_zero,
        tsub_zero]
    have hdy : ∀ i ∈ Finset.range K, (d i : ℝ) = m * (y (i + 1) - y i) := fun i _ => by
      simp only [hd, hy]
      rw [Nat.cast_sub (blockIndex_mono m K (Nat.le_succ i))]
      field_simp
    have hlogQ : Real.log ((1 - t) ^ m * ∏ i ∈ Finset.range K, (g i ^ 2 / 4) ^ d i) =
        m * Real.log (1 - t) + 2 * m * ∑ i ∈ Finset.range K,
          (y (i + 1) - y i) * Real.log (g i) - m * Real.log 4 := by
      rw [Real.log_mul (pow_pos (by linarith) m).ne' (Finset.prod_pos fun i _ => by
        have := hgpos i; positivity).ne', Real.log_pow,
        Real.log_prod fun i _ => by have := hgpos i; positivity]
      have e0 : ∀ i ∈ Finset.range K, Real.log ((g i ^ 2 / 4) ^ d i) =
          (d i : ℝ) * (2 * Real.log (g i) - Real.log 4) := fun i _ => by
        rw [Real.log_pow, Real.log_div (pow_pos (hgpos i) 2).ne' (by norm_num), Real.log_pow]
        push_cast; ring
      have e1 : ∑ i ∈ Finset.range K, (d i : ℝ) * (2 * Real.log (g i) - Real.log 4) =
          2 * ∑ i ∈ Finset.range K, (d i : ℝ) * Real.log (g i) -
            (∑ i ∈ Finset.range K, (d i : ℝ)) * Real.log 4 := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ i ∈ Finset.range K, (d i : ℝ) * Real.log (g i) =
          m * ∑ i ∈ Finset.range K, (y (i + 1) - y i) * Real.log (g i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => by rw [hdy i hi]; ring
      rw [Finset.sum_congr rfl e0, e1, e2, hsumd]
      ring
    rw [hlogQ, Real.log_mul (by positivity) (pow_pos hρ.1 m).ne', Real.log_pow, Real.log_pow, hρC]
    have hD : (m : ℝ) * (((m / K + 1 : ℕ) : ℝ) / m) = ((m / K + 1 : ℕ) : ℝ) := by
      field_simp
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hblock' : (m : ℝ) * ∑ i ∈ Finset.range K, (y (i + 1) - y i) * Real.log (g i) ≤
        m * (∫ a in (0 : ℝ)..recoveryEdge, Real.log (arcsineGauge a t) * recoveryDensity a) +
          ((m / K + 1 : ℕ) : ℝ) * Real.log 2 := by
      have := mul_le_mul_of_nonneg_left hblock hmR.le
      rw [mul_add, ← mul_assoc, hD] at this
      exact this
    have hpot' := mul_le_mul_of_nonneg_left hpot hmR.le
    push_cast at hblock' ⊢
    nlinarith [hblock', hpot', h4]
  calc (1 - t) ^ m * |(chebyshevBlockProduct m K).eval ((1 - t ^ 2) / 4)|
      ≤ (1 - t) ^ m * (2 ^ K * ∏ i ∈ Finset.range K, (g i ^ 2 / 4) ^ d i) :=
        mul_le_mul_of_nonneg_left hprod (pow_nonneg (by linarith [ht.2]) m)
    _ = 2 ^ K * ((1 - t) ^ m * ∏ i ∈ Finset.range K, (g i ^ 2 / 4) ^ d i) := by ring
    _ ≤ 2 ^ K * (4 ^ (m / K + 1) * recoveryRate ^ m) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = 2 ^ K * 4 ^ (m / K + 1) * recoveryRate ^ m := by ring

/-- **The block-product norm bound** `‖P‖_m ≤ 2^K 4^{⌊m/K⌋+1} ρ^m`. -/
theorem cubicWeightedIntervalNorm_chebyshevBlockProduct_le {m K : ℕ} (hK : 1 ≤ K)
    (hKm : K ≤ m) :
    cubicWeightedIntervalNorm m (chebyshevBlockProduct m K) ≤
      2 ^ K * 4 ^ (m / K + 1) * recoveryRate ^ m := by
  refine csSup_le ((nonempty_Icc.mpr (by norm_num)).image _) ?_
  rintro v ⟨r, hr, rfl⟩
  set t := Real.sqrt (1 - 4 * r) with htdef
  have h14 : 0 ≤ 1 - 4 * r := by linarith [hr.2]
  have ht2 : t ^ 2 = 1 - 4 * r := Real.sq_sqrt h14
  have htmem : t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (by linarith [hr.1])⟩
  have hr' : r = (1 - t ^ 2) / 4 := by rw [ht2]; ring
  have hW : cubicRadialWeight r = 1 - t := rfl
  simp only
  rw [hW, hr']
  exact weighted_eval_chebyshevBlockProduct_le hK hKm htmem

/-- **The upper bound** `t_m ≤ 2^K 4^{⌊m/K⌋+1} ρ^m` for the optimizer, `1 ≤ K ≤ m`. -/
theorem cubicChebyshev_norm_le {m : ℕ} {T : Polynomial ℝ} (hT : IsCubicChebyshev m T) {K : ℕ}
    (hK : 1 ≤ K) (hKm : K ≤ m) :
    cubicWeightedIntervalNorm m T ≤ 2 ^ K * 4 ^ (m / K + 1) * recoveryRate ^ m := by
  obtain ⟨hmon, hdeg⟩ := chebyshevBlockProduct_monic_natDegree m (K := K) hK
  refine (hT.2.2 _ hdeg.le ?_).trans (cubicWeightedIntervalNorm_chebyshevBlockProduct_le hK hKm)
  have := hmon.coeff_natDegree
  rwa [hdeg] at this

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
