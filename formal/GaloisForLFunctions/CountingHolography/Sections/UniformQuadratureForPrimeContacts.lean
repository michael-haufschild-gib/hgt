import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds
import GaloisForLFunctions.HTGeometry.MonotoneRiemannSum
import GaloisForLFunctions.CountingHolography.Sections.SignedSplineSmallSections

/-!
# Uniform quadrature for prime contacts

For a bounded Lipschitz profile on the log axis, the variation of
`G(log x)/x` on any interval starting at one is bounded independently
of the far endpoint. This gives the same mesh error at every conductor.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset AbsoluteGeometryOfSpecZ BiScaleUncertainty.ChebyshevGauge

private def logDensity (G : ℝ → ℝ) (x : ℝ) := G (Real.log (max x 1))/max x 1

private theorem logDensity_increment {G : ℝ → ℝ} {B K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ u, |G u| ≤ B)
    (hl : ∀ u v, |G v-G u| ≤ K*|v-u|) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    |logDensity G y-logDensity G x| ≤ (K+B)*(1/x-1/y) := by
  have hx' := one_pos.trans_le hx
  have hy' := hx'.trans_le hxy
  have hd := sub_nonneg.mpr (one_div_le_one_div_of_le hx' hxy)
  have ht := Real.log_le_sub_one_of_pos (div_pos hy' hx')
  rw [Real.log_div hy'.ne' hx'.ne'] at ht
  have hs := hl (Real.log x) (Real.log y)
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx' hxy))] at hs
  have he : (y/x-1)/y = 1/x-1/y := by field_simp
  have hi : |G (Real.log y)-G (Real.log x)|/y ≤ K*(1/x-1/y) := calc
    _ ≤ (K*(y/x-1))/y := div_le_div_of_nonneg_right
      (hs.trans (mul_le_mul_of_nonneg_left ht hK)) hy'.le
    _ = _ := by rw [mul_div_assoc,he]
  unfold logDensity
  rw [max_eq_left (hx.trans hxy),max_eq_left hx,
    show G (Real.log y)/y-G (Real.log x)/x =
      (G (Real.log y)-G (Real.log x))/y - G (Real.log x)*(1/x-1/y) by ring]
  refine (abs_sub _ _).trans ?_
  rw [abs_div,abs_of_pos hy',abs_mul,abs_of_nonneg hd,add_mul]
  exact add_le_add hi (mul_le_mul_of_nonneg_right (hb _) hd)

/-- The harmonic sum over the degree points has error at most twice
the sum of the uniform and Lipschitz bounds, divided by the resolution. -/
theorem degreeSum_uniform_error {G : ℝ → ℝ} (hc : Continuous G) {B K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ u, |G u| ≤ B) (hl : ∀ u v, |G v-G u| ≤ K*|v-u|)
    (L : ℕ) {r : ℕ} (hr : 0 < r) (h₀ : G 0 = 0) (h₁ : G (Real.log (1+(L : ℝ))) = 0) :
    |(∑ j ∈ Ioc r (r+L*r), G (Real.log ((j : ℝ)/r))/j) -
      ∫ u in (0:ℝ)..Real.log (1+(L : ℝ)), G u| ≤ 2*(K+B)/r := by
  let A := K+B
  let F := logDensity G
  let Q := fun x : ℝ => -(A/x)
  let P := fun x : ℝ => F x+Q x
  have hA : 0 ≤ A := add_nonneg hK ((abs_nonneg _).trans (hb 0))
  have hr' : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hlen : ((L*r : ℕ) : ℝ)/r = L := by rw [Nat.cast_mul,mul_div_cancel_right₀ _ hr'.ne']
  have hEnd : (1:ℝ) ≤ 1+L := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hQ : MonotoneOn Q (Set.Icc 1 (1+((L*r : ℕ):ℝ)/r)) := by
    intro x hx y _ hxy
    exact neg_le_neg (div_le_div_of_nonneg_left hA (one_pos.trans_le hx.1) hxy)
  have hP : MonotoneOn P (Set.Icc 1 (1+((L*r : ℕ):ℝ)/r)) := by
    intro x hx y _ hxy
    have he := (abs_le.mp (logDensity_increment hK hb hl hx.1 hxy)).1
    change F x + -(A/x) ≤ F y + -(A/y)
    change -(A*(1/x-1/y)) ≤ F y-F x at he
    rw [mul_sub,← mul_div_assoc,← mul_div_assoc,mul_one] at he
    linarith only [he]
  have h := HTGeometry.abs_sum_sub_integral_le_of_bv_scaled hr' hP hQ
  have hPQ (x : ℝ) : P x-Q x = F x := add_sub_cancel_right _ _
  simp only [hPQ,hlen] at h
  have hF₀ : F 1 = 0 := by simp [F,logDensity,h₀]
  have hF₁ : F (1+L) = 0 := by simp [F,logDensity,h₁]
  have hend : P (1+L)-P 1+(Q (1+L)-Q 1) ≤ 2*A := by
    dsimp only [P,Q]
    rw [hF₀,hF₁,div_one]
    linarith only [div_nonneg hA (one_pos.trans_le hEnd).le]
  have hbound := h.trans (mul_le_mul_of_nonneg_left hend (by positivity))
  have htel := sum_range_sub (fun i : ℕ => F (1+(i:ℝ)/r)) (L*r)
  simp only [sum_sub_distrib,hlen,Nat.cast_zero,zero_div,add_zero,hF₀,hF₁,sub_zero,
    sub_eq_zero] at htel
  have hi : (∫ x in (1:ℝ)..1+L, F x) = ∫ u in (0:ℝ)..Real.log (1+(L:ℝ)), G u :=
    integral_comp_log_div hc hEnd
  rw [← htel,hi] at hbound
  have hmesh : (∑ j ∈ Ioc r (r+L*r), G (Real.log ((j : ℝ)/r))/j) =
      (1/(r:ℝ))*∑ i ∈ range (L*r), F (1+((i+1:ℕ):ℝ)/r) := by
    rw [sum_Ioc_add_eq_sum_range,mul_sum]
    refine sum_congr rfl fun j _ => ?_
    unfold F logDensity
    rw [cast_add_succ_div hr j,cast_add_succ_eq hr j,Nat.cast_succ,max_eq_left (one_le_one_add_div r j)]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hmesh]
  exact hbound.trans_eq (by ring)

private theorem packet_bounds_four : ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    (∑ i, |(a i : ℝ)|) ≤ 4 → (∀ u, |packet a u| ≤ 4) ∧
      ∀ u v, |packet a v-packet a u| ≤ K*|v-u| := by
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    hasCompactSupport_cubicSpline contDiff_cubicSpline (by norm_num)
  refine ⟨4*(K : ℝ),by positivity,fun N a ha => ⟨fun u => ?_,fun u v => ?_⟩⟩
  · unfold packet splineSource
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun i _ => ?_).trans ha)
    rw [abs_mul,abs_of_nonneg (cubicSpline_nonneg _)]
    exact mul_le_of_le_one_right (abs_nonneg _) ((cubicSpline_le_half _).trans (by norm_num))
  · unfold packet splineSource
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ i, |(a i : ℝ)| *((K : ℝ)*|v-u|) := by
        refine sum_le_sum fun i _ => ?_
        rw [← mul_sub,abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have h := hK.dist_le_mul
          (v-(Real.log 3+5)-Real.log ((i : ℝ)+1)) (u-(Real.log 3+5)-Real.log ((i : ℝ)+1))
        simp only [Real.dist_eq,sub_sub_sub_cancel_right] at h
        exact h
      _ = (∑ i, |(a i : ℝ)|)*((K : ℝ)*|v-u|) := (sum_mul ..).symm
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right ha (by positivity)

/-- Integrating a single unrounded prime contact on the log window. -/
def integratedContact {N : ℕ} (a : Fin N → ℤ) (k : ℕ) : ℝ :=
  2/Real.sqrt k * ∫ u in (0:ℝ)..Real.log (1+((3*windowEnd N : ℕ) : ℝ)),
    packet a u*packet a (u+Real.log k)

/-- Every prime row of every divisor of total variation at most four has
the same quadrature constant, including when the horizon and lag vary. -/
theorem contactMultiplicity_uniform_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    (∑ i, |(a i : ℝ)|) ≤ 4 → ∀ {r k : ℕ}, 0 < r → 0 < k →
    |contactMultiplicity (packet a) (3*windowEnd N) r k-integratedContact a k| ≤
      (2/Real.sqrt k)*(C/r) := by
  obtain ⟨K,hK,h⟩ := packet_bounds_four
  refine ⟨2*(8*K+16),by positivity,fun N a ha {r k} hr hk => ?_⟩
  let L := 3*windowEnd N
  let f := packet a
  let G := fun u : ℝ => f u*f (u+Real.log k)
  obtain ⟨hf,hl⟩ := h N a ha
  have hfb (u) : |f u| ≤ 4 := hf u
  have hfl (u v) : |f v-f u| ≤ K*|v-u| := hl u v
  have hg (u) : |G u| ≤ 16 := by
    unfold G
    rw [abs_mul]
    exact (mul_le_mul (hfb _) (hfb _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hgl (u v) : |G v-G u| ≤ (8*K)*|v-u| := by
    have ht := hfl (u+Real.log k) (v+Real.log k)
    rw [add_sub_add_right_eq_sub] at ht
    have he : G v-G u = (f v-f u)*f (v+Real.log k) +
        f u*(f (v+Real.log k)-f (u+Real.log k)) := by unfold G; ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul,abs_mul]
    have h₁ := mul_le_mul (hfl u v) (hfb (v+Real.log k)) (abs_nonneg _) (by positivity)
    have h₂ := mul_le_mul (hfb u) ht (abs_nonneg _) (by norm_num)
    linarith only [h₁,h₂]
  have hwin := packet_window a
  have h₀ : G 0 = 0 := by
    unfold G f
    rw [hwin.2 0 (Or.inl (Real.log_nonneg (by norm_num))),zero_mul]
  have h₁ : G (Real.log (1+(L:ℝ))) = 0 := by
    unfold G f
    rw [hwin.2 _ (Or.inr ?_),zero_mul]
    apply Real.log_le_log (Nat.cast_pos.mpr hwin.1)
    unfold L
    push_cast
    linarith only [Nat.cast_nonneg (α := ℝ) (windowEnd N)]
  have hc : Continuous f := (packet_contDiff a).continuous
  have he := degreeSum_uniform_error (G := G) (hc.mul (hc.comp (continuous_id.add continuous_const)))
    (mul_nonneg (by norm_num) hK) hg hgl L hr h₀ h₁
  have heq : (∑ j ∈ Ioc r (r+L*r), G (Real.log ((j:ℝ)/r))/j) =
      ∑ j ∈ Ioc r (r+L*r), degreeSample f r j*degreeSample f r (j*k)/j := by
    apply sum_congr rfl
    intro j hj
    have hj' : (0:ℝ) < j := Nat.cast_pos.mpr (hr.trans (mem_Ioc.mp hj).1)
    have hr' : (0:ℝ) < r := Nat.cast_pos.mpr hr
    have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
    unfold G degreeSample
    rw [Nat.cast_mul,mul_div_right_comm (j:ℝ) k r,Real.log_mul (div_pos hj' hr').ne' hk'.ne']
  rw [heq] at he
  unfold contactMultiplicity integratedContact
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2/Real.sqrt k)]
  exact mul_le_mul_of_nonneg_left he (by positivity)

#print axioms contactMultiplicity_uniform_error

end GaloisForLFunctions.CountingHolography.Sections
