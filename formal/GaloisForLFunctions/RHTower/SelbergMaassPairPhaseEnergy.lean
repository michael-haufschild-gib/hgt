import GaloisForLFunctions.RHTower.SelbergMaassSourceCurrents

/-!
# Pair and phase currents in the actual Maass energy

The exact finite complex Gram identity retains both pair-current squares and the
square of the total phase current. Instantiation on the original congruence family
resolves its actual radial residual and Fisher identity, including common zeros.
The original real eigen-potential gives actual phase-current conservation without
choosing a phase. The regulated identity retains the constant-coordinate energy.
No global quarter comparison or vanishing of quotient periods is asserted.
-/

open Complex Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassPairPhaseEnergy
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassTraceBoundary
  SelbergMaassTraceRadial SelbergMaassSourceCurrents
noncomputable section

private theorem sum_tensor {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ i, ∑ j, a i * b j) = (∑ i, a i) * (∑ j, b j) := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- Finite complex pair squares and total phase square recover the full real radial defect. -/
theorem finite_pair_phase_identity {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    (∑ i, normSq (a i)) * (∑ i, normSq (b i)) -
        (∑ i, (b i * (starRingEnd ℂ) (a i)).re) ^ (2 : ℕ) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, normSq (a i * b j - a j * b i) +
        (∑ i, (b i * (starRingEnd ℂ) (a i)).im) ^ (2 : ℕ) := by
  have hp (i j : ι) : normSq (a i * b j - a j * b i) =
      normSq (a i) * normSq (b j) + normSq (a j) * normSq (b i) -
      2 * (b i * (starRingEnd ℂ) (a i)).re * (b j * (starRingEnd ℂ) (a j)).re -
        2 * (b i * (starRingEnd ℂ) (a i)).im * (b j * (starRingEnd ℂ) (a j)).im := by
    simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im]
    ring
  have hr : (∑ i, ∑ j, normSq (a j) * normSq (b i)) =
      (∑ i, normSq (a i)) * (∑ i, normSq (b i)) := by
    simp_rw [← Finset.sum_mul]
    rw [← Finset.mul_sum]
  simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_tensor, hr, sum_tensor, sum_tensor]
  simp_rw [← Finset.mul_sum]
  ring

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Total phase current of the actual complex congruence component family. -/
def phaseCurrent (v : ℂ) (z : ℂ) : ℝ :=
  ∑ q : Deck N, (dir v (field N f q) z * (starRingEnd ℂ) (field N f q z)).im

/-- Half the ordered sum of actual squared complex pair currents. -/
def pairEnergy (v : ℂ) (z : ℂ) : ℝ :=
  (1 / 2 : ℝ) * ∑ q : Deck N, ∑ r : Deck N,
    normSq (bracket (field N f q) (field N f r) v z)

/-- Pair-current energy is nonnegative at every original chart point. -/
theorem pairEnergy_nonneg (v z : ℂ) : 0 ≤ pairEnergy N f v z :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => normSq_nonneg _)))

/-- Exact source Gram identity with the scalar trace current and full phase square retained. -/
theorem source_pair_phase_identity (v : ℂ) (z : ℍ) :
    density N f z * directionalEnergy N f v z - current N f v z ^ (2 : ℕ) / 4 =
      pairEnergy N f v (z : ℂ) + phaseCurrent N f v (z : ℂ) ^ (2 : ℕ) := by
  have h := finite_pair_phase_identity
    (fun q : Deck N => field N f q (z : ℂ))
    (fun q : Deck N => dir v (field N f q) (z : ℂ))
  have hv (q : Deck N) : field N f q (z : ℂ) = (quotientForm N f q).1.1 z := by
    simp only [field, Function.comp_apply, ofComplex_apply]
  have hd : (∑ q : Deck N, normSq (field N f q (z : ℂ))) = density N f z := by
    simp only [hv, density]
  have hr : (∑ q : Deck N,
      (dir v (field N f q) (z : ℂ) * (starRingEnd ℂ) (field N f q (z : ℂ))).re) =
        realPairing N f v z := by
    simp only [field, realPairing, Function.comp_apply, ofComplex_apply]
  change (∑ q : Deck N, normSq (field N f q (z : ℂ))) * directionalEnergy N f v z - _ =
    pairEnergy N f v (z : ℂ) + phaseCurrent N f v (z : ℂ) ^ (2 : ℕ) at h
  rw [hd, hr] at h
  rw [current_eq_realPairing]
  nlinarith [h]

/-- Actual radial residual is exactly the pair-plus-phase energy after multiplication by density, including common zeros. -/
theorem density_mul_radialResidual (v : ℂ) (z : ℍ) :
    density N f z * radialResidual N f v (radialSlope N f v z) z =
      pairEnergy N f v (z : ℂ) + phaseCurrent N f v (z : ℂ) ^ (2 : ℕ) := by
  have h := source_pair_phase_identity N f v z
  rw [density_mul_directionalEnergy] at h
  linarith

/-- Both actual angular directions retain their pair and phase energies at every source point. -/
theorem density_mul_angularEnergy (z : ℍ) :
    density N f z * angularEnergy N f z =
      pairEnergy N f 1 (z : ℂ) + pairEnergy N f Complex.I (z : ℂ) +
        phaseCurrent N f 1 (z : ℂ) ^ (2 : ℕ) + phaseCurrent N f Complex.I (z : ℂ) ^ (2 : ℕ) := by
  rw [angularEnergy, mul_add, density_mul_radialResidual, density_mul_radialResidual]
  ring

/-- The actual Fisher identity resolves its full angular contribution into conserved-current candidates. -/
theorem trace_fisher_pair_phase_identity (z : ℍ) :
    density N f z * realLaplacian (density N f ∘ ofComplex) (z : ℂ) =
      (current N f 1 z ^ (2 : ℕ) + current N f Complex.I z ^ (2 : ℕ)) / 2 +
        2 * (pairEnergy N f 1 (z : ℂ) + pairEnergy N f Complex.I (z : ℂ) +
          phaseCurrent N f 1 (z : ℂ) ^ (2 : ℕ) + phaseCurrent N f Complex.I (z : ℂ) ^ (2 : ℕ)) -
        2 * lam * density N f z ^ (2 : ℕ) / z.im ^ (2 : ℕ) := by
  rw [trace_fisher_identity, mul_assoc 2, density_mul_angularEnergy]

/-- The full regularized residual retains the pair and phase squares and the exact regulator derivative energy. -/
theorem regularized_pair_phase_identity (e : Ioi (0 : ℝ)) (v : ℂ) (z : ℍ) :
    (density N f z + (e : ℝ) ^ (2 : ℕ)) *
        SelbergMaassTraceRegularized.directionalRemainder N f e v z =
      pairEnergy N f v (z : ℂ) + phaseCurrent N f v (z : ℂ) ^ (2 : ℕ) +
        (e : ℝ) ^ (2 : ℕ) * directionalEnergy N f v z := by
  have hd : density N f z + (e : ℝ) ^ (2 : ℕ) ≠ 0 := by
    simpa only [ofComplex_apply] using
      (SelbergMaassTraceRegularized.denominator_pos N f e (z : ℂ)).ne'
  rw [SelbergMaassTraceRegularized.directionalRemainder_eq]
  calc
    _ = density N f z * directionalEnergy N f v z - current N f v z ^ (2 : ℕ) / 4 +
        (e : ℝ) ^ (2 : ℕ) * directionalEnergy N f v z := by
      field_simp
      ring
    _ = _ := by rw [source_pair_phase_identity]

private theorem phase_differentiable {F : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 F z) (v : ℂ) :
    DifferentiableAt ℝ (fun w => (dir v F w * (starRingEnd ℂ) (F w)).im) z := by
  have hd := (dir_contDiffAt hf v).differentiableAt (by norm_num)
  exact Complex.imCLM.differentiableAt.comp z (hd.mul
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z (hf.differentiableAt (by norm_num))))

/-- Differentiating an actual phase current cancels the real derivative-square contribution. -/
theorem component_phase_dir {F : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 F z) (v : ℂ) :
    dir v (fun w => (dir v F w * (starRingEnd ℂ) (F w)).im) z =
      (dir v (dir v F) z * (starRingEnd ℂ) (F z)).im := by
  have hd := (dir_contDiffAt hf v).differentiableAt (by norm_num)
  have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z
    (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hp := Complex.imCLM.hasFDerivAt.comp z (hd.hasFDerivAt.mul hc)
  have h := congrArg (fun L => L v) hp.fderiv
  change dir v (fun w => (dir v F w * (starRingEnd ℂ) (F w)).im) z =
    (dir v F z * (starRingEnd ℂ) (dir v F z) +
      (starRingEnd ℂ) (F z) * dir v (dir v F) z).im at h
  rw [Complex.mul_conj, Complex.add_im, Complex.ofReal_im, zero_add] at h
  rw [h, mul_comm]

/-- Each actual Maass component has zero planar phase-current divergence, including its zeros. -/
theorem component_phase_conservation (q : Deck N) (z : ℍ) :
    dir 1 (fun w => (dir 1 (field N f q) w * (starRingEnd ℂ) (field N f q w)).im) (z : ℂ) +
      dir Complex.I (fun w => (dir Complex.I (field N f q) w *
        (starRingEnd ℂ) (field N f q w)).im) (z : ℂ) = 0 := by
  rw [component_phase_dir (field_smooth N f q z),
    component_phase_dir (field_smooth N f q z), ← Complex.add_im, ← add_mul, field_laplacian,
    mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_im]

/-- The total original phase current is divergence-free; no phase choice or division is required. -/
theorem phase_current_conservation (z : ℍ) :
    dir 1 (phaseCurrent N f 1) (z : ℂ) +
      dir Complex.I (phaseCurrent N f Complex.I) (z : ℂ) = 0 := by
  unfold phaseCurrent
  rw [dir_sum Finset.univ (fun q _ => phase_differentiable (field_smooth N f q z) 1),
    dir_sum Finset.univ (fun q _ => phase_differentiable (field_smooth N f q z) Complex.I),
    ← Finset.sum_add_distrib]
  simp only [component_phase_conservation, Finset.sum_const_zero]

end
end GaloisForLFunctions.RHTower.SelbergMaassPairPhaseEnergy
