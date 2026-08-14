import GaloisForLFunctions.HTGeometry.LowFrequencyAsymptotic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The half-log asymptotic for a Hilbert-valued amplitude

The scalar low-frequency asymptotic transfers to a Hilbert-valued amplitude by duality: testing
against a unit vector turns the vector integral into a scalar one with the same Lipschitz data, and
the norm of a vector is attained by testing against its own direction.  Hence

`∫₀^A f(η) η^{-1/2} e^{iηL} dη = f(0) √π e^{iπ/4} L^{-1/2} + O(L^{-1})`

for an `X`-valued amplitude, which is the form the half-log scattering map uses on the two frequency
channels.
-/

open Complex intervalIntegral MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- Testing the vector asymptotic against a fixed direction. -/
theorem inner_integral_comm {f : ℝ → X} {a b : ℝ} (v : X)
    (hf : IntervalIntegrable f volume a b) :
    (inner ℂ v (∫ t in a..b, f t) : ℂ) = ∫ t in a..b, (inner ℂ v (f t) : ℂ) := by
  have h := (innerSL ℂ v).intervalIntegral_comp_comm hf
  exact h.symm

/-- **The Hilbert-valued low-frequency asymptotic.** -/
theorem norm_vector_lowFrequency_asymptotic {f f' : ℝ → X} {K A L : ℝ}
    (hA : 0 < A) (hL : 0 < L) (hK : 0 ≤ K)
    (hderiv : ∀ η : ℝ, 0 < η → η ≤ A → HasDerivAt f (f' η) η)
    (hcont : ∀ v : X, ContinuousOn (fun η : ℝ => (inner ℂ v (f' η) : ℂ)) (Set.Ioc 0 A))
    (hlip : ∀ η : ℝ, 0 ≤ η → η ≤ A → ‖f η - f 0‖ ≤ K * η)
    (hbound : ∀ η : ℝ, 0 < η → η ≤ A → ‖f' η‖ ≤ K)
    (hint : IntervalIntegrable (fun η : ℝ => scaledFresnel L η • f η) volume 0 A) :
    ‖(∫ η in (0:ℝ)..A, scaledFresnel L η • f η)
        - (((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
            * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I))) • f 0‖
      ≤ ‖f 0‖ * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)))
        + (4 * K * A ^ ((1:ℝ)/2)) / L := by
  set W : ℂ := ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
    * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I)) with hW
  set D : X := (∫ η in (0:ℝ)..A, scaledFresnel L η • f η) - W • f 0 with hD
  set M : ℝ := ‖f 0‖ * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)))
    + (4 * K * A ^ ((1:ℝ)/2)) / L with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have h1 : (0:ℝ) ≤ ‖f 0‖ * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ))) := by positivity
    have h2 : (0:ℝ) ≤ (4 * K * A ^ ((1:ℝ)/2)) / L := by positivity
    linarith
  have hkey : ∀ v : X, ‖v‖ = 1 → ‖(inner ℂ v D : ℂ)‖ ≤ M := by
    intro v hv
    set g : ℝ → ℂ := fun η => (inner ℂ v (f η) : ℂ) with hg
    set g' : ℝ → ℂ := fun η => (inner ℂ v (f' η) : ℂ) with hg'
    have hgderiv : ∀ η : ℝ, 0 < η → η ≤ A → HasDerivAt g (g' η) η := by
      intro η hη hηA
      have hconst : HasDerivAt (fun _ : ℝ => v) (0 : X) η := hasDerivAt_const η v
      have hbase := HasDerivAt.inner ℂ hconst (hderiv η hη hηA)
      simpa [hg, hg'] using hbase
    have hglip : ∀ η : ℝ, 0 ≤ η → η ≤ A → ‖g η - g 0‖ ≤ K * η := by
      intro η hη hηA
      have hsub : g η - g 0 = (inner ℂ v (f η - f 0) : ℂ) := by
        rw [hg, inner_sub_right]
      rw [hsub]
      calc ‖(inner ℂ v (f η - f 0) : ℂ)‖ ≤ ‖v‖ * ‖f η - f 0‖ :=
            norm_inner_le_norm (𝕜 := ℂ) v (f η - f 0)
        _ = ‖f η - f 0‖ := by rw [hv, one_mul]
        _ ≤ K * η := hlip η hη hηA
    have hgbound : ∀ η : ℝ, 0 < η → η ≤ A → ‖g' η‖ ≤ K := by
      intro η hη hηA
      calc ‖(inner ℂ v (f' η) : ℂ)‖ ≤ ‖v‖ * ‖f' η‖ := norm_inner_le_norm (𝕜 := ℂ) v (f' η)
        _ = ‖f' η‖ := by rw [hv, one_mul]
        _ ≤ K := hbound η hη hηA
    have hscalar := norm_lowFrequency_asymptotic (f := g) (f' := g') hA hL hK hgderiv
      (hcont v) hglip hgbound
    have hcomm : (inner ℂ v D : ℂ)
        = (∫ η in (0:ℝ)..A, g η * scaledFresnel L η) - g 0 * W := by
      rw [hD, inner_sub_right, inner_smul_right, inner_integral_comm v hint]
      congr 1
      · refine intervalIntegral.integral_congr fun η _ => ?_
        show (inner ℂ v (scaledFresnel L η • f η) : ℂ) = g η * scaledFresnel L η
        rw [inner_smul_right, hg]
        ring
      · rw [hg]
        ring
    rw [hcomm, hW]
    have hshape : (∫ η in (0:ℝ)..A, g η * scaledFresnel L η)
        - g 0 * (((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
          * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I)))
        = (∫ η in (0:ℝ)..A, g η * scaledFresnel L η)
          - g 0 * (((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
            * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I))) := rfl
    have hg0 : ‖g 0‖ ≤ ‖f 0‖ := by
      calc ‖(inner ℂ v (f 0) : ℂ)‖ ≤ ‖v‖ * ‖f 0‖ := norm_inner_le_norm (𝕜 := ℂ) v (f 0)
        _ = ‖f 0‖ := by rw [hv, one_mul]
    refine le_trans hscalar ?_
    rw [hM]
    have hpos : (0:ℝ) ≤ 2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)) := by positivity
    nlinarith [hg0, hpos]
  rcases eq_or_ne D 0 with hzero | hne
  · rw [hzero, norm_zero]
    exact hM0
  · have hnorm : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    set v : X := ((((‖D‖ : ℝ)⁻¹ : ℝ) : ℂ)) • D with hv
    have hvnorm : ‖v‖ = 1 := by
      rw [hv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
    have hinner : (inner ℂ v D : ℂ) = ((‖D‖ : ℝ) : ℂ) := by
      have hDne : ((‖D‖ : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact hnorm
      have hsq : (inner ℂ D D : ℂ) = ((‖D‖ : ℝ) : ℂ) * ((‖D‖ : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, sq]
        norm_cast
      rw [hv, inner_smul_left, hsq, Complex.conj_ofReal]
      push_cast
      field_simp
    have := hkey v hvnorm
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg D)] at this
    exact this

end

end GaloisForLFunctions.HTGeometry
