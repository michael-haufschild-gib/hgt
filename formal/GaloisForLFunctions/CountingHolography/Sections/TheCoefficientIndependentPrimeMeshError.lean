import GaloisForLFunctions.CountingHolography.Sections.SecondOrderQuadratureOnTheDegreeMesh
import GaloisForLFunctions.CountingHolography.Sections.OneMultiplicityPerSquareConductor
import GaloisForLFunctions.CountingHolography.Sections.EffectiveSectionsAtSeparatedConductors

/-!
# Prime contact quadrature on the original resolution

Two derivatives of a signed packet cost its coefficient mass. In the
product the squared mass cancels the square of the original mesh
resolution. Adding back the exact floor loss leaves an error depending
only on the horizon.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticFunction AbsoluteGeometryOfSpecZ BiScaleUncertainty.ChebyshevGauge

private def withSpline {N : ℕ} (a : Fin N → ℤ) (s : ℝ → ℝ) (u : ℝ) :=
  ∑ i, (a i:ℝ)*s (u-(Real.log 3+5)-Real.log ((i:ℝ)+1))

private theorem withSpline_derivative {N : ℕ} (a : Fin N → ℤ) {s t : ℝ → ℝ}
    (hs : ∀ u, HasDerivAt s (t u) u) (u : ℝ) :
    HasDerivAt (withSpline a s) (withSpline a t u) u := by
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.const_mul
  exact ((hs _).comp u (((hasDerivAt_id' u).sub_const _).sub_const _)).congr_deriv (mul_one _)

private theorem withSpline_bound {N : ℕ} (a : Fin N → ℤ) {s : ℝ → ℝ} {K : ℝ}
    (h : ∀ u, |s u| ≤ K) (u : ℝ) : |withSpline a s u| ≤ (resolution a:ℝ)*K := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← coefficientVariation_eq_resolution, sum_mul]
  exact sum_le_sum fun i _ => (abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left (h _) (abs_nonneg _))

private theorem spline_two_derivative_bounds : ∃ K : ℝ, 0 ≤ K ∧ ∀ u,
    |cubicSpline u| ≤ K ∧ |deriv cubicSpline u| ≤ K ∧ |deriv (deriv cubicSpline) u| ≤ K := by
  have h₁ : ContDiff ℝ 1 (deriv cubicSpline) := ContDiff.deriv' (n := 1) contDiff_cubicSpline
  have hc₂ : Continuous (deriv (deriv cubicSpline)) :=
    (show ContDiff ℝ 0 (deriv (deriv cubicSpline)) from ContDiff.deriv' (n := 0) h₁).continuous
  obtain ⟨A,hA⟩ := hasCompactSupport_cubicSpline.deriv.exists_bound_of_continuous h₁.continuous
  obtain ⟨B,hB⟩ := hasCompactSupport_cubicSpline.deriv.deriv.exists_bound_of_continuous hc₂
  let K := 1+|A|+|B|
  refine ⟨K,by dsimp only [K]; positivity,fun u => ?_⟩
  have hu := cubicSpline_le_half u
  have ha := hA u
  have hb := hB u
  rw [Real.norm_eq_abs] at ha hb
  rw [abs_of_nonneg (cubicSpline_nonneg _)]
  dsimp only [K]
  exact ⟨by linarith only [hu,abs_nonneg A,abs_nonneg B],
    by linarith only [ha,le_abs_self A,abs_nonneg B],by linarith only [hb,le_abs_self B,abs_nonneg A]⟩

/-- Every prime-power lag on the actual mesh has an absolute quadrature
error of order 1/√k, uniformly over signed integer coefficients. -/
theorem original_contact_quadrature : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ) {k : ℕ}, 0 < k →
    |contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k-integratedContact a k| ≤ C/Real.sqrt k := by
  obtain ⟨K,hK,hb⟩ := spline_two_derivative_bounds
  have hS : ContDiff ℝ 1 (deriv cubicSpline) := ContDiff.deriv' (n := 1) contDiff_cubicSpline
  refine ⟨64*K^2,by positivity,fun N a {k} hk => ?_⟩
  by_cases ha : a = 0
  · subst a
    have hz (u : ℝ) : packet (0 : Fin N → ℤ) u = 0 := by simp [packet,splineSource]
    simp only [contactMultiplicity,degreeSample,integratedContact,hz,zero_div,sum_const_zero,
      mul_zero,intervalIntegral.integral_zero,sub_self,abs_zero]
    positivity
  let r := resolution a
  let L := 3*windowEnd N
  let f := packet a
  let f₁ := withSpline a (deriv cubicSpline)
  let f₂ := withSpline a (deriv (deriv cubicSpline))
  let l := Real.log k
  let G := fun u : ℝ => f u*f (u+l)
  let G₁ := fun u : ℝ => f₁ u*f (u+l)+f u*f₁ (u+l)
  let G₂ := fun u : ℝ => f₂ u*f (u+l)+f₁ u*f₁ (u+l)+(f₁ u*f₁ (u+l)+f u*f₂ (u+l))
  have hr : 0 < r := resolution_pos ha
  have hf (u) : HasDerivAt f (f₁ u) u := withSpline_derivative a
    (fun x => (contDiff_cubicSpline.differentiable (by decide) x).hasDerivAt) u
  have hf₁ (u) : HasDerivAt f₁ (f₂ u) u := withSpline_derivative a
    (fun x => (hS.differentiable (by decide) x).hasDerivAt) u
  have hs {g g' : ℝ → ℝ} (h : ∀ u, HasDerivAt g (g' u) u) (u : ℝ) :
      HasDerivAt (fun v => g (v+l)) (g' (u+l)) u :=
    ((h _).comp u ((hasDerivAt_id' u).add_const l)).congr_deriv (mul_one _)
  have hG (u) : HasDerivAt G (G₁ u) u := (hf u).mul (hs hf u)
  have hG₁ (u) : HasDerivAt G₁ (G₂ u) u := ((hf₁ u).mul (hs hf u)).add ((hf u).mul (hs hf₁ u))
  have hc₂ : Continuous f₂ := by
    have hcont : Continuous (deriv (deriv cubicSpline)) :=
      (show ContDiff ℝ 0 (deriv (deriv cubicSpline)) from ContDiff.deriv' (n := 0) hS).continuous
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      (hcont.comp ((continuous_id.sub continuous_const).sub continuous_const))
  have hc₀ : Continuous f := (packet_contDiff a).continuous
  have hc₁ : Continuous f₁ := continuous_iff_continuousAt.mpr fun x => (hf₁ x).continuousAt
  have hshift := continuous_id.add (continuous_const (y := l))
  have hcG₂ : Continuous G₂ := ((hc₂.mul (hc₀.comp hshift)).add (hc₁.mul (hc₁.comp hshift))).add
    ((hc₁.mul (hc₁.comp hshift)).add (hc₀.mul (hc₂.comp hshift)))
  let H := (r:ℝ)*K
  have hH := mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hK
  have h₀ (u) : |f u| ≤ H := withSpline_bound a (fun x => (hb x).1) u
  have h₁ (u) : |f₁ u| ≤ H := withSpline_bound a (fun x => (hb x).2.1) u
  have h₂ (u) : |f₂ u| ≤ H := withSpline_bound a (fun x => (hb x).2.2) u
  have prod {x y : ℝ} (hx : |x| ≤ H) (hy : |y| ≤ H) : |x*y| ≤ H^2 := by
    rw [abs_mul,sq]; exact mul_le_mul hx hy (abs_nonneg _) hH
  have bounds (u) : |G u| ≤ 4*H^2 ∧ |G₁ u| ≤ 4*H^2 ∧ |G₂ u| ≤ 4*H^2 := by
    refine ⟨by linarith only [prod (h₀ u) (h₀ (u+l)),sq_nonneg H],?_,?_⟩
    · exact (abs_add_le _ _).trans (by linarith only [prod (h₁ u) (h₀ (u+l)),prod (h₀ u) (h₁ (u+l)),sq_nonneg H])
    · exact (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) (abs_add_le _ _)).trans
        (by linarith only [prod (h₂ u) (h₀ (u+l)),prod (h₁ u) (h₁ (u+l)),prod (h₀ u) (h₂ (u+l))]))
  have hw := packet_window a
  have hz (u : ℝ) (hu : u < Real.log 2) : G u=0 := by
    change packet a u*_ = 0
    rw [hw.2 _ (Or.inl (hu.le.trans (Real.log_le_log (by norm_num) (by norm_num)))),zero_mul]
  have he : G (Real.log (1+(L:ℝ)))=0 := by
    change packet a _*_ = 0
    rw [hw.2 _ (Or.inr ?_),zero_mul]
    apply Real.log_le_log (Nat.cast_pos.mpr hw.1)
    dsimp only [L]; push_cast; linarith only [Nat.cast_nonneg (α := ℝ) (windowEnd N)]
  have h := degreeSum_second_order hG hG₁ hcG₂ (by positivity : 0 ≤ 4*H^2) bounds hz L hr he
  have hrow : (∑ j ∈ Ioc r (r+L*r), G (Real.log ((j:ℝ)/r))/j) =
      ∑ j ∈ Ioc r (r+L*r), degreeSample f r j*degreeSample f r (j*k)/j := by
    refine sum_congr rfl fun j hj => ?_
    have hj' : 0 < j := hr.trans (mem_Ioc.mp hj).1
    unfold degreeSample G l
    rw [Nat.cast_mul,mul_div_right_comm (j:ℝ) k r,Real.log_mul (div_pos (Nat.cast_pos.mpr hj') (Nat.cast_pos.mpr hr)).ne'
      (Nat.cast_pos.mpr hk : 0 < (k:ℝ)).ne']
  rw [hrow] at h
  change |(2/Real.sqrt k)*_ - (2/Real.sqrt k)*_| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2/Real.sqrt k)]
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans (le_of_eq ?_)
  dsimp only [H]
  field_simp [(Nat.cast_pos.mpr hr : 0 < (r:ℝ)).ne',(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk) : 0 < Real.sqrt k).ne']
  ring

/-- After adding the exact floor loss, the discrepancy of the ordinary
prime product is independent of all coefficients on the given horizon. -/
theorem ordinaryPrimeGenerator_coefficient_independent_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    |Real.log (ordinaryPrimeGenerator a : ℝ)+ordinaryFloorLoss a-ordinaryPrimeContact a| ≤
      C*Real.sqrt (3*windowEnd N : ℕ) := by
  obtain ⟨B,hB,h⟩ := original_contact_quadrature
  refine ⟨34*B,by positivity,fun N a => ?_⟩
  let L := 3*windowEnd N
  let X := fun k => contactMultiplicity (packet a) L (resolution a) k
  rw [log_ordinaryPrimeGenerator]
  change |(∑ k ∈ ordinaryPrimeLags L, (⌊X k⌋:ℝ)*vonMangoldt k)+
    (∑ k ∈ ordinaryPrimeLags L, Int.fract (X k)*vonMangoldt k)-
    (∑ k ∈ ordinaryPrimeLags L, integratedContact a k*vonMangoldt k)| ≤ _
  rw [← sum_add_distrib,← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ k ∈ ordinaryPrimeLags L, B*(vonMangoldt k/Real.sqrt k) := by
          refine sum_le_sum fun k hk => ?_
          rw [← add_mul,Int.floor_add_fract,← sub_mul,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
          exact (mul_le_mul_of_nonneg_right (h N a (mem_filter.mp hk).2.pos) vonMangoldt_nonneg).trans_eq (by ring)
    _ ≤ _ := by rw [← mul_sum,mul_comm (34:ℝ),mul_assoc]; exact mul_le_mul_of_nonneg_left (ordinaryPrimeLagSums L).2 hB

/-- Continuous prime contact is homogeneous of degree two on every integer ray. -/
theorem integratedContact_nsmul {N : ℕ} (a : Fin N → ℤ) (m k : ℕ) :
    integratedContact (m • a) k = (m:ℝ)^2*integratedContact a k := by
  simp only [integratedContact,packet_smul]
  simp_rw [show ∀ x y : ℝ, (m:ℝ)*x*((m:ℝ)*y)=(m:ℝ)^2*(x*y) by intro x y; ring,intervalIntegral.integral_const_mul]
  ring

/-- The signed quadrature discrepancy of the square conductors costs O(n)
uniformly over every multiplicity, including the diagonal. -/
theorem successorSquare_floor_corrected_mesh_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → ∀ m : ℕ,
    let a := m • successorSquareTriple n
    |Real.log (ordinaryPrimeGenerator a : ℝ)+ordinaryFloorLoss a-
      (m:ℝ)^2*ordinaryPrimeContact (successorSquareTriple n)| ≤ C*n := by
  obtain ⟨B,hB,h⟩ := ordinaryPrimeGenerator_coefficient_independent_error
  obtain ⟨A,hA,hwin⟩ := successorSquare_window_bound
  refine ⟨B*A,mul_nonneg hB (zero_le_one.trans hA),fun {n} hn m => ?_⟩
  have hh := h _ (m • successorSquareTriple n)
  have hroot := Real.sqrt_le_sqrt (hwin hn)
  rw [Real.sqrt_sq (mul_nonneg (zero_le_one.trans hA) (Nat.cast_nonneg (α := ℝ) n))] at hroot
  simp only [ordinaryPrimeContact,integratedContact_nsmul,mul_assoc,← mul_sum] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hroot hB).trans_eq (mul_assoc ..).symm)

/-- At quadratic conductor scale the complete discrepancy between the
continuous and ordinary prime contacts is the exact loss to floors,
for every sequence of prescribed multiplicities. -/
theorem square_sampling_negligible_at_diagonal_scale (μ : ℕ → ℕ) :
    Tendsto (fun n : ℕ =>
      let a := μ n • successorSquareTriple n
      (Real.log (ordinaryPrimeGenerator a : ℝ)+ordinaryFloorLoss a-
        (μ n:ℝ)^2*ordinaryPrimeContact (successorSquareTriple n))/(n:ℝ)^2) atTop (𝓝 0) := by
  obtain ⟨C,_,h⟩ := successorSquare_floor_corrected_mesh_error
  apply squeeze_zero_norm' (a := fun n : ℕ => C/(n:ℝ)) _
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  dsimp only
  rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (sq_nonneg (n:ℝ))]
  exact (div_le_div_of_nonneg_right (h hn (μ n)) (sq_nonneg _)).trans_eq (by field_simp)

#print axioms original_contact_quadrature
#print axioms ordinaryPrimeGenerator_coefficient_independent_error
#print axioms successorSquare_floor_corrected_mesh_error
#print axioms square_sampling_negligible_at_diagonal_scale

end GaloisForLFunctions.CountingHolography.Sections
