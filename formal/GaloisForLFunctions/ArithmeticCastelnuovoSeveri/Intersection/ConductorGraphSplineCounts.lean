import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.ConductorGraphPrimeLimit
import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UnrestrictedAtomicGardingFailsAndCollarGardingHolds

/-!
# Vertical restriction orders on the integer spline lattice

Both graph families and their mesh are determined by the integer coefficient
vector. Thickness is its total absolute multiplicity. Along a ray the
normalized spline is fixed while the mesh tends to zero. The two oriented
orders give the signed prime contribution through their logarithms.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open LogCells GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

/-- The real spline used in the integer Weil probes. -/
def conductorSpline {n : ℕ} (a : Fin n → ℤ) (x : ℝ) : ℝ :=
  ∑ j, (a j : ℝ) * cubicSpline (x - Real.log ((j : ℝ) + 1))

/-- Total absolute multiplicity fixes the mesh without a separate dilation argument. -/
def conductorThickness {n : ℕ} (a : Fin n → ℤ) : ℕ := ∑ j, (a j).natAbs

private def splineHorizon (n : ℕ) : ℕ := (n+1) * ⌈Real.exp 10⌉₊

private theorem horizon_lower (n : ℕ) : 10 + Real.log (n+1 : ℝ) ≤ Real.log (splineHorizon n) := by
  have he := Nat.le_ceil (Real.exp 10)
  have hp := (Real.exp_pos (10:ℝ)).trans_le he
  have hn : 0 < (n:ℝ)+1 := by positivity
  rw [splineHorizon, Nat.cast_mul, Nat.cast_succ, Real.log_mul hn.ne' hp.ne', add_comm]
  exact add_le_add_right (by simpa using Real.log_le_log (Real.exp_pos _) he) _

private theorem spline_support {n : ℕ} (a : Fin n → ℤ) (x : ℝ)
    (hx : x ≤ -5 ∨ Real.log (splineHorizon n) - 5 ≤ x) : conductorSpline a x = 0 := by
  apply sum_eq_zero
  intro j _
  have hj : 1 ≤ (j : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hjn : (j : ℝ)+1 ≤ n+1 := by exact_mod_cast Nat.add_le_add_right j.isLt.le 1
  have hjl := Real.log_nonneg hj
  have hup := Real.log_le_log (by positivity : 0 < (j:ℝ)+1) hjn
  rw [cubicSpline_eq_zero, mul_zero]
  rcases hx with hl | hr
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
  · exact lt_of_lt_of_le (by linarith [horizon_lower n]) (le_abs_self _)

private theorem spline_regular {n : ℕ} (a : Fin n → ℤ) :
    ContDiff ℝ 2 (conductorSpline a) ∧ HasCompactSupport (conductorSpline a) := by
  constructor
  · exact ContDiff.sum fun i _ =>
      contDiff_const.mul (contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const))
  · refine HasCompactSupport.intro (show IsCompact (Set.Icc (-5) (Real.log (splineHorizon n) - 5)) from
      isCompact_Icc) fun x hx => spline_support a x ?_
    rcases not_and_or.mp hx with hl | hr
    · exact Or.inl (lt_of_not_ge hl).le
    · exact Or.inr (lt_of_not_ge hr).le

private theorem thickness_smul {n : ℕ} (a : Fin n → ℤ) (m : ℕ) :
    conductorThickness (m • a) = m * conductorThickness a := by
  simp [conductorThickness, Pi.smul_apply, Int.natAbs_mul, mul_sum]

private theorem spline_smul {n : ℕ} (a : Fin n → ℤ) (m : ℕ) (x : ℝ) :
    conductorSpline (m • a) x = (m:ℝ)*conductorSpline a x := by
  simp [conductorSpline, Pi.smul_apply, mul_sum, mul_assoc]

private def normalizedSpline {n : ℕ} (a : Fin n → ℤ) (x : ℝ) : ℝ :=
  conductorSpline a x / conductorThickness a

private theorem normalizedSpline_smul {n m : ℕ} (a : Fin n → ℤ) (hm : 0 < m) :
    normalizedSpline (m • a) = normalizedSpline a := by
  funext x
  rw [normalizedSpline, normalizedSpline, thickness_smul, spline_smul, Nat.cast_mul]
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hm.ne')

/-- The two oriented graph orders are evaluated on the coefficient vector itself. -/
def conductorSplineHeight {n : ℕ} (a : Fin n → ℤ) : ℝ :=
  if conductorThickness a = 0 then 0 else
    sampledGraphHeight (conductorThickness a) (splineHorizon n) 5 (normalizedSpline a) (normalizedSpline a)

private theorem normalizedSpline_height_limit {n : ℕ} (a : Fin n → ℤ) :
    Tendsto (fun m : ℕ => sampledGraphHeight m (splineHorizon n) 5
      (normalizedSpline a) (normalizedSpline a) / (m:ℝ)^2)
      atTop (𝓝 (_root_.RHTower.primeSum (normalizedSpline a))) := by
  obtain ⟨hr,hc⟩ := spline_regular a
  have hf : ContDiff ℝ 2 (normalizedSpline a) := hr.div_const _
  have hfc : HasCompactSupport (normalizedSpline a) := by
    simpa only [normalizedSpline, div_eq_mul_inv, Pi.mul_def] using
      (hc.mul_right (f' := fun _ : ℝ => (conductorThickness a : ℝ)⁻¹))
  have hB : 1 ≤ splineHorizon n :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_ceil_iff.mpr (Real.exp_pos _))
  rw [← smoothPrimePair_self_eq_primeSum]
  apply tendsto_sampledGraphHeight_of_support hf hf hfc hfc hB
  intro u hu
  have hz : normalizedSpline a u = 0 := by rw [normalizedSpline, spline_support a u hu, zero_div]
  exact ⟨hz,hz⟩

private theorem unscale_prime {n : ℕ} (a : Fin n → ℤ) (hh : conductorThickness a ≠ 0) :
    (conductorThickness a : ℝ)^2 * _root_.RHTower.primeSum (normalizedSpline a) =
      _root_.RHTower.primeSum (conductorSpline a) := by
  rw [← CriticalArithmeticCorrelationTheory.primeSum_const_mul]
  congr 1
  funext u
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hh)

private theorem rescale_degree (z s d : ℝ) (hs : s ≠ 0) :
    s^2 * (z / (d*s)^2) = z / d^2 := by
  rw [mul_pow, ← div_div, mul_div_cancel₀ _ (pow_ne_zero 2 hs)]

private theorem thickness_pos {n : ℕ} {a : Fin n → ℤ} (h : a ≠ 0) : 0 < conductorThickness a := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by simpa [funext_iff] using h
  exact (Int.natAbs_pos.mpr hi).trans_le (single_le_sum
    (fun j _ => Nat.zero_le (a j).natAbs) (mem_univ i))

/-- On every signed integer ray, the vertical graph height has the full prime sum
of the original cubic spline as its quadratic coefficient. -/
theorem conductorSplineHeight_tate (n : ℕ) (a : Fin n → ℤ) :
    Tendsto (fun m : ℕ => conductorSplineHeight (m • a) / (m:ℝ)^2)
      atTop (𝓝 (_root_.RHTower.primeSum (conductorSpline a))) := by
  by_cases ha : a = 0
  · subst a
    have h0 := tendsto_const_nhds (x := (0:ℝ)) (f := (atTop : Filter ℕ))
    simpa [conductorSplineHeight, conductorThickness, conductorSpline, _root_.RHTower.primeSum] using h0
  have hh := thickness_pos ha
  have ht : Tendsto (fun m : ℕ => m * conductorThickness a) atTop atTop :=
    tendsto_atTop_mono (f := id) (fun m => Nat.le_mul_of_pos_right m hh) tendsto_id
  rw [← unscale_prime a hh.ne']
  apply (((normalizedSpline_height_limit a).comp ht).const_mul ((conductorThickness a : ℝ)^2)).congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmh := Nat.mul_ne_zero hm.ne' hh.ne'
  change (conductorThickness a : ℝ)^2 *
    (sampledGraphHeight (m * conductorThickness a) _ _ (normalizedSpline a) (normalizedSpline a) /
      ((m * conductorThickness a : ℕ) : ℝ)^2) = conductorSplineHeight (m • a) / (m:ℝ)^2
  rw [conductorSplineHeight, thickness_smul, if_neg hmh, normalizedSpline_smul a hm, Nat.cast_mul]
  exact rescale_degree _ _ _ (Nat.cast_ne_zero.mpr hh.ne')

#print axioms conductorSplineHeight_tate

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
