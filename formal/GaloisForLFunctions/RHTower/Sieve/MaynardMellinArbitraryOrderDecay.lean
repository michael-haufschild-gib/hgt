import GaloisForLFunctions.RHTower.Sieve.MaynardNormalizedReferenceTargetPerron
import GaloisForLFunctions.HTGeometry.SmoothWeightSharpMellin

/-!
# Arbitrary-order decay of normalized adjacent Mellin kernels

Every derivative order available for the corpus smooth cutoff transfers to its normalized adjacent
window.  The resulting vertical decay has exactly the natural-frequency cost `(N/H)^(j+1)` and a
constant depending only on `j`; no fixed quadratic ceiling remains.
-/

noncomputable section
namespace RHTower.Sieve

open Complex Finset MeasureTheory Set
open GaloisForLFunctions.HTGeometry

theorem exists_routeTNormalizedSmoothWindowMellin_natOrder_bound (j : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ N H : ℝ, 0 < N → 0 < H → ∀ s : ℂ, 0 < s.re →
      |s.im| ^ (j + 1) * ‖routeTNormalizedSmoothWindowMellin N H s‖ ≤
        Cj / H ^ (j + 1) *
          ((N + 2 * H) ^ (s.re + (j : ℝ)) +
            (N + H) ^ (s.re + (j : ℝ))) := by
  obtain ⟨Cj, hCj, hbound⟩ := exists_bound_mellin_smoothWeight_uniform_support j
  refine ⟨Cj, hCj, ?_⟩
  intro N H hN hH s hs
  let Mp : ℂ := mellin (fun x : ℝ =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ)) s
  let Mb : ℂ := mellin (fun x : ℝ =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s
  have hplus := hbound (N + H) H (by linarith) hH s hs
  have hbase := hbound N H hN hH s hs
  have himshift : ∀ i : ℕ, |s.im| ≤ ‖s + 1 + (i : ℂ)‖ := by
    intro i
    calc
      |s.im| = |(s + 1 + (i : ℂ)).im| := by simp
      _ ≤ ‖s + 1 + (i : ℂ)‖ := Complex.abs_im_le_norm _
  have himProd : |s.im| ^ j ≤ ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖ := by
    simpa using (Finset.prod_le_prod (s := Finset.range j)
      (fun _ _ => abs_nonneg s.im) (fun i _ => himshift i))
  have himAll : |s.im| ^ (j + 1) ≤
      ‖s‖ * (∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) := by
    calc
      |s.im| ^ (j + 1) = |s.im| * |s.im| ^ j := by
        rw [pow_succ]
        ring
      _ ≤ ‖s‖ * (∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) :=
        mul_le_mul (Complex.abs_im_le_norm s) himProd (by positivity) (norm_nonneg _)
  have hplus' : |s.im| ^ (j + 1) * ‖Mp‖ ≤
      Cj / H ^ (j + 1) * (N + 2 * H) ^ (s.re + (j : ℝ)) * H := by
    calc
      |s.im| ^ (j + 1) * ‖Mp‖ ≤
          (‖s‖ * (∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖)) * ‖Mp‖ :=
        mul_le_mul_of_nonneg_right himAll (norm_nonneg _)
      _ ≤ Cj / H ^ (j + 1) * (N + 2 * H) ^ (s.re + (j : ℝ)) * H := by
        simpa only [Mp, two_mul, add_assoc] using hplus
  have hbase' : |s.im| ^ (j + 1) * ‖Mb‖ ≤
      Cj / H ^ (j + 1) * (N + H) ^ (s.re + (j : ℝ)) * H := by
    calc
      |s.im| ^ (j + 1) * ‖Mb‖ ≤
          (‖s‖ * (∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖)) * ‖Mb‖ :=
        mul_le_mul_of_nonneg_right himAll (norm_nonneg _)
      _ ≤ Cj / H ^ (j + 1) * (N + H) ^ (s.re + (j : ℝ)) * H := by
        simpa only [Mb] using hbase
  have hnorm : ‖routeTNormalizedSmoothWindowMellin N H s‖ = H⁻¹ * ‖Mp - Mb‖ := by
    rw [routeTNormalizedSmoothWindowMellin,
      mellin_routeTSmoothWindowWeight_eq_sub hN.le hH hs,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  rw [hnorm]
  calc
    |s.im| ^ (j + 1) * (H⁻¹ * ‖Mp - Mb‖) =
        H⁻¹ * (|s.im| ^ (j + 1) * ‖Mp - Mb‖) := by ring
    _ ≤ H⁻¹ * (|s.im| ^ (j + 1) * (‖Mp‖ + ‖Mb‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_sub_le Mp Mb) (by positivity))
        (inv_nonneg.mpr hH.le)
    _ = H⁻¹ *
        (|s.im| ^ (j + 1) * ‖Mp‖ + |s.im| ^ (j + 1) * ‖Mb‖) := by ring
    _ ≤ H⁻¹ *
        (Cj / H ^ (j + 1) * (N + 2 * H) ^ (s.re + (j : ℝ)) * H +
          Cj / H ^ (j + 1) * (N + H) ^ (s.re + (j : ℝ)) * H) :=
      mul_le_mul_of_nonneg_left (add_le_add hplus' hbase') (inv_nonneg.mpr hH.le)
    _ = Cj / H ^ (j + 1) *
        ((N + 2 * H) ^ (s.re + (j : ℝ)) +
          (N + H) ^ (s.re + (j : ℝ))) := by
      field_simp [hH.ne']

/-- Narrow-window form: every integration-by-parts order costs exactly its natural frequency
`N/H`, up to a constant depending only on the order. -/
theorem exists_routeTNormalizedSmoothWindowMellin_natOrder_narrow_bound (j : ℕ) :
    ∃ Dj : ℝ, 0 ≤ Dj ∧ ∀ N H : ℝ, 1 ≤ N → 0 < H → H ≤ N →
      ∀ s : ℂ, 0 < s.re → s.re ≤ 1 →
        |s.im| ^ (j + 1) * ‖routeTNormalizedSmoothWindowMellin N H s‖ ≤
          Dj / H ^ (j + 1) * N ^ (s.re + (j : ℝ)) := by
  obtain ⟨Cj, hCj, hraw⟩ :=
    exists_routeTNormalizedSmoothWindowMellin_natOrder_bound j
  let Dj : ℝ := 2 * Cj * (3 : ℝ) ^ (j + 1)
  have hDj : 0 ≤ Dj := by dsimp only [Dj]; positivity
  refine ⟨Dj, hDj, ?_⟩
  intro N H hN hH hHN s hs0 hs1
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have he0 : 0 ≤ s.re + (j : ℝ) := by positivity
  have he1 : s.re + (j : ℝ) ≤ (j + 1 : ℕ) := by
    norm_num
    linarith
  have hplusBase : N + 2 * H ≤ 3 * N := by linarith
  have hbaseBase : N + H ≤ 3 * N := by linarith
  have hplusPow : (N + 2 * H) ^ (s.re + (j : ℝ)) ≤
      (3 * N) ^ (s.re + (j : ℝ)) := by
    exact Real.rpow_le_rpow (by positivity) hplusBase he0
  have hbasePow : (N + H) ^ (s.re + (j : ℝ)) ≤
      (3 * N) ^ (s.re + (j : ℝ)) := by
    exact Real.rpow_le_rpow (by positivity) hbaseBase he0
  have hthreeExp : (3 : ℝ) ^ (s.re + (j : ℝ)) ≤ (3 : ℝ) ^ (j + 1) := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) he1)
  have hthree : (3 * N) ^ (s.re + (j : ℝ)) ≤
      (3 : ℝ) ^ (j + 1) * N ^ (s.re + (j : ℝ)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hN0.le]
    exact mul_le_mul_of_nonneg_right hthreeExp (Real.rpow_nonneg hN0.le _)
  have hkernel := hraw N H hN0 hH s hs0
  have hscale0 : 0 ≤ Cj / H ^ (j + 1) := by positivity
  calc
    |s.im| ^ (j + 1) * ‖routeTNormalizedSmoothWindowMellin N H s‖ ≤
        Cj / H ^ (j + 1) *
          ((N + 2 * H) ^ (s.re + (j : ℝ)) +
            (N + H) ^ (s.re + (j : ℝ))) := hkernel
    _ ≤ Cj / H ^ (j + 1) *
        (2 * ((3 : ℝ) ^ (j + 1) * N ^ (s.re + (j : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ hscale0
      calc
        (N + 2 * H) ^ (s.re + (j : ℝ)) +
            (N + H) ^ (s.re + (j : ℝ)) ≤
          (3 * N) ^ (s.re + (j : ℝ)) +
            (3 * N) ^ (s.re + (j : ℝ)) := add_le_add hplusPow hbasePow
        _ ≤ 2 * ((3 : ℝ) ^ (j + 1) * N ^ (s.re + (j : ℝ))) := by
          linarith
    _ = Dj / H ^ (j + 1) * N ^ (s.re + (j : ℝ)) := by
      dsimp only [Dj]
      ring

end RHTower.Sieve
