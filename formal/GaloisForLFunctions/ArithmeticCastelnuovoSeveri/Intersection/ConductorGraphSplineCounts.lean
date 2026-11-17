import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.ConductorGraphPrimeLimit
import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe

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
  exact add_le_add_left (by simpa using Real.log_le_log (Real.exp_pos _) he) _

private theorem spline_support {n : ℕ} (a : Fin n → ℤ) (x : ℝ)
    (hx : x ≤ -5 ∨ Real.log (splineHorizon n) - 5 ≤ x) : conductorSpline a x = 0 := by
  apply sum_eq_zero
  intro j _
  have hj : 1 ≤ (j : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hjn : (j : ℝ)+1 ≤ n+1 := add_le_add_right (by exact_mod_cast j.isLt.le) 1
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
  simp [conductorThickness, Pi.smul_apply, nsmul_eq_mul, Int.natAbs_mul, mul_sum]

private theorem spline_smul {n : ℕ} (a : Fin n → ℤ) (m : ℕ) (x : ℝ) :
    conductorSpline (m • a) x = (m:ℝ)*conductorSpline a x := by
  simp [conductorSpline, Pi.smul_apply, nsmul_eq_mul, mul_sum, mul_assoc]

/-- The two oriented graph orders are evaluated on the coefficient vector itself. -/
def conductorSplineHeight {n : ℕ} (a : Fin n → ℤ) : ℝ :=
  let h := conductorThickness a
  let f := fun x => conductorSpline a x / h
  if h = 0 then 0 else sampledGraphHeight h (splineHorizon n) 5 f f

/-- On every signed integer ray, the vertical graph height has the full prime sum
of the original cubic spline as its quadratic coefficient. -/
theorem conductorSplineHeight_tate (n : ℕ) (a : Fin n → ℤ) :
    Tendsto (fun m : ℕ => conductorSplineHeight (m • a) / (m:ℝ)^2)
      atTop (𝓝 (_root_.RHTower.primeSum (conductorSpline a))) := by
  let h := conductorThickness a
  let f := fun x => conductorSpline a x / h
  have h1 : 1 ≤ splineHorizon n := by
    apply Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_ceil_iff.mpr (Real.exp_pos _))
  obtain ⟨hr,hc⟩ := spline_regular a
  have hf : ContDiff ℝ 2 f := hr.div_const _
  have hfc : HasCompactSupport f := by simpa only [f, div_eq_mul_inv, Pi.mul_def] using
    (hc.mul_right (f' := fun _ : ℝ => (h:ℝ)⁻¹))
  have hs := tendsto_sampledGraphHeight_of_support hf hf hfc hfc (R := 5) h1
    (fun u hu => by dsimp [f]; rw [spline_support a u hu, zero_div]; exact ⟨rfl,rfl⟩)
  by_cases hz : h = 0
  · have ha : a = 0 := by
      funext j
      have hj := single_le_sum (f := fun j => (a j).natAbs) (fun i _ => Nat.zero_le _) (mem_univ j)
      change (a j).natAbs ≤ h at hj
      simpa [hz] using hj
    subst a
    simp [conductorSplineHeight, conductorThickness, conductorSpline, _root_.RHTower.primeSum]
  have hh : (h:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz
  have ht : Tendsto (fun m : ℕ => m*h) atTop atTop := by
    apply tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hz)) tendsto_id
  have hp : (h:ℝ)^2 * smoothPrimePair f f = _root_.RHTower.primeSum (conductorSpline a) := by
    rw [← smoothPrimePair_self_eq_primeSum]
    unfold smoothPrimePair
    rw [← tsum_mul_left]
    apply tsum_congr
    intro t
    rw [show ∀ z w : ℝ, (h:ℝ)^2 * (z*w) = z*((h:ℝ)^2*w) by intros; ring, ← MeasureTheory.integral_const_mul]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    dsimp [f]
    field_simp
  rw [← hp]
  apply ((hs.comp ht).const_mul ((h:ℝ)^2)).congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : (fun x => conductorSpline (m • a) x / (conductorThickness (m • a) : ℝ)) = f := by
    funext x
    rw [thickness_smul, spline_smul, Nat.cast_mul]
    change (m:ℝ)*conductorSpline a x / ((m:ℝ)*h) = conductorSpline a x / h
    field_simp
  have hmh := Nat.mul_ne_zero (Nat.ne_of_gt hm) hz
  simp only [Function.comp_apply, conductorSplineHeight, he, thickness_smul, if_neg hmh, Nat.cast_mul, h]
  change (h:ℝ)^2 * (sampledGraphHeight (m*h) _ _ f f / ((m:ℝ)*h)^2) =
    sampledGraphHeight (m*h) _ _ f f / (m:ℝ)^2
  field_simp

#print axioms conductorSplineHeight_tate

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
