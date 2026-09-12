import GaloisForLFunctions.HTGeometry.ComplexMetricCovariantCurvature

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.CurvatureContraction
noncomputable section
variable {d : ℕ}

/-- Trace of the upper curvature index against the first curvature-form index. -/
def ricciTrace (T : Fin d → Fin d → Fin d → Matrix (Fin d) (Fin d) ℂ)
    (k b j : Fin d) : ℂ := ∑ a, T k a j a b

/-- The full inverse-metric contraction of the Ricci trace. -/
def scalarTrace (H : Matrix (Fin d) (Fin d) ℂ)
    (T : Fin d → Fin d → Fin d → Matrix (Fin d) (Fin d) ℂ) (j : Fin d) : ℂ :=
  ∑ b, ∑ k, H b k*ricciTrace T j b k

/-- The full inverse-metric contraction in the derivative and Ricci slots. -/
def divergenceTrace (H : Matrix (Fin d) (Fin d) ℂ)
    (T : Fin d → Fin d → Fin d → Matrix (Fin d) (Fin d) ℂ) (j : Fin d) : ℂ :=
  ∑ k, ∑ b, H b k*ricciTrace T k b j

/-- The middle Bianchi term gives a second copy of the Ricci divergence.
Both skew identities and every contraction index are explicit. -/
theorem middle_contraction (H : Matrix (Fin d) (Fin d) ℂ)
    (T : Fin d → Fin d → Fin d → Matrix (Fin d) (Fin d) ℂ)
    (hH : ∀ a b, H a b = H b a)
    (hform : ∀ k i j, T k i j = -T k j i)
    (hsk : ∀ k i j, T k i j*H+H*(T k i j).transpose = 0) (j : Fin d) :
    (∑ k, ∑ b, ∑ u, H b k*T u j k u b) = divergenceTrace H T j := by
  have hm (u k : Fin d) : (∑ b, H b k*T u j k u b) =
      ∑ b, H u b*T u k j k b := by
    have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M u k) (hsk u j k)
    simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.zero_apply] at he
    have hc : (∑ b, H b k*T u j k u b) = ∑ b, T u j k u b*H b k := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    calc
      _ = -(∑ b, H u b*T u j k k b) := by rw [hc]; linear_combination he
      _ = _ := by
        rw [hform u j k]
        simp only [Matrix.neg_apply,mul_neg,Finset.sum_neg_distrib,neg_neg]
  calc
    _ = ∑ k, ∑ u, ∑ b, H b k*T u j k u b := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = ∑ u, ∑ k, ∑ b, H b k*T u j k u b := by rw [Finset.sum_comm]
    _ = ∑ u, ∑ k, ∑ b, H u b*T u k j k b := by simp_rw [hm]
    _ = ∑ u, ∑ b, ∑ k, H u b*T u k j k b := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = divergenceTrace H T j := by
      unfold divergenceTrace ricciTrace
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro b _
      rw [hH u b]

/-- The final Bianchi term is minus the scalar-curvature derivative trace. -/
theorem final_contraction (H : Matrix (Fin d) (Fin d) ℂ)
    (T : Fin d → Fin d → Fin d → Matrix (Fin d) (Fin d) ℂ)
    (hform : ∀ k i j, T k i j = -T k j i) (j : Fin d) :
    (∑ k, ∑ b, ∑ u, H b k*T j k u u b) = -scalarTrace H T j := by
  have he (k b u : Fin d) : H b k*T j k u u b = -(H b k*T j u k u b) := by
    rw [hform j k u]
    simp only [Matrix.neg_apply,mul_neg]
  simp_rw [he,Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  unfold scalarTrace ricciTrace
  simp_rw [Finset.mul_sum]

/-- Exact double contraction of differential Bianchi. No Einstein divergence
or scalar-derivative identity is assumed in this finite algebraic step. -/
theorem double_contraction (H : Matrix (Fin d) (Fin d) ℂ)
    (T : Fin d → Fin d → Fin d → Matrix (Fin d) (Fin d) ℂ)
    (hH : ∀ a b, H a b = H b a)
    (hform : ∀ k i j, T k i j = -T k j i)
    (hsk : ∀ k i j, T k i j*H+H*(T k i j).transpose = 0)
    (hB : ∀ k i j, T k i j+T i j k+T j k i = 0) (j : Fin d) :
    2*divergenceTrace H T j = scalarTrace H T j := by
  have hb : (∑ k, ∑ b, ∑ u, H b k*(T k u j u b+T u j k u b+T j k u u b)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro u _
    have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M u b) (hB k u j)
    simp only [Matrix.add_apply,Matrix.zero_apply] at he
    rw [he,mul_zero]
  simp only [mul_add,Finset.sum_add_distrib] at hb
  have hfirst : (∑ k, ∑ b, ∑ u, H b k*T k u j u b) = divergenceTrace H T j := by
    unfold divergenceTrace ricciTrace
    simp_rw [Finset.mul_sum]
  rw [hfirst,middle_contraction H T hH hform hsk j,final_contraction H T hform j] at hb
  linear_combination hb

end
end GaloisForLFunctions.HTGeometry.CurvatureContraction

namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ComplexCoordinateConnection CurvatureContraction
noncomputable section
variable {d : ℕ}

/-- Raising the metric-skew identity gives the exact inverse-metric identity
needed by the original Bianchi contraction. -/
theorem tensorPartial_raised_skew (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y u v, g y u v = g y v u) (k i j : Fin d) :
    let R : Matrix (Fin d) (Fin d) ℂ := tensorPartial (connection g) x k i j
    R*(g x)⁻¹ + (g x)⁻¹*R.transpose = 0 := by
  let R : Matrix (Fin d) (Fin d) ℂ := tensorPartial (connection g) x k i j
  have hR := tensorPartial_metric_skew g x hg hdet hs k i j
  change R.transpose*g x+g x*R = 0 at hR
  have hl := Matrix.nonsing_inv_mul (g x) (isUnit_iff_ne_zero.mpr hdet)
  have hr := Matrix.mul_nonsing_inv (g x) (isUnit_iff_ne_zero.mpr hdet)
  have he : (g x)⁻¹*(R.transpose*g x+g x*R)*(g x)⁻¹ =
      (g x)⁻¹*R.transpose+R*(g x)⁻¹ := by
    calc
      _ = ((g x)⁻¹*R.transpose)*(g x*(g x)⁻¹)+
          ((g x)⁻¹*g x)*(R*(g x)⁻¹) := by noncomm_ring
      _ = _ := by rw [hl,hr,Matrix.mul_one,Matrix.one_mul]
  have hz : (g x)⁻¹*R.transpose+R*(g x)⁻¹ = 0 := by rw [← he,hR]; simp
  simpa only [add_comm] using hz

/-- Double-contracted differential Bianchi for the actual metric-derived
curvature, with both required skew properties produced from that metric. -/
theorem bianchi_double_contracted (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y u v, g y u v = g y v u) (j : Fin d) :
    2*divergenceTrace (g x)⁻¹ (tensorPartial (connection g) x) j =
      scalarTrace (g x)⁻¹ (tensorPartial (connection g) x) j := by
  have hsym : (g x).transpose = g x := by ext u v; exact hs x v u
  have hi : ((g x)⁻¹).transpose = (g x)⁻¹ := by rw [Matrix.transpose_nonsing_inv,hsym]
  apply double_contraction
  · intro a b
    exact (congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M b a) hi)
  · intro k i j
    exact eq_neg_of_add_eq_zero_left
      (tensorPartial_form_skew (connection g) x (connection_contDiffAt g x hg hdet) k i j)
  · exact tensorPartial_raised_skew g x hg hdet hs
  · intro k i j
    ext u v
    exact bianchi g x hg hdet hs k i j u v

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
