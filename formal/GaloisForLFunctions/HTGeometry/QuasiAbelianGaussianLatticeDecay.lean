import GaloisForLFunctions.HTGeometry.QuasiAbelianGaussianFlatSeed
import GaloisForLFunctions.HTGeometry.QuasiAbelianIntegerLatticeSeparator

/-!
# Gaussian decay of the flat seed along a real lattice

The centred complex Gaussian has modulus `exp(-∑ σ_i (u_i² - v_i²))` where `u` and `v` are the real
and imaginary parts of `x - centre`.  Along the **real** integer lattice the imaginary parts never
move, so on a compact set they contribute a bounded factor, while the real parts are shifted by the
lattice index: `u_i = Re(x_i) + k_i - Re(centre_i)`.  Since `(k + t)² ≥ k²/2 - t²`, the modulus is
at most a compact-uniform constant times `exp(-∑ σ_i k_i²/2)`.

This is the decay half of Abe's growth stability lemma: it is the *only* source of decay in the
Poincaré majorant, and it is quantitatively Gaussian in the lattice index.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The modulus of the centred Gaussian -/

theorem norm_centeredComplexGaussian_apply {d : ℕ} (σ : Fin d → ℝ)
    (center x : Fin d → ℂ) :
    ‖(centeredComplexGaussian σ center).1 x‖
      = Real.exp (-∑ i, σ i * (((x i - center i).re) ^ 2 - ((x i - center i).im) ^ 2)) := by
  rw [centeredComplexGaussian_apply, Complex.norm_exp]
  congr 1
  rw [Complex.neg_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_ofReal_mul, sq, Complex.mul_re]
  ring

/-! ## Compact sets have uniformly bounded coordinates -/

theorem exists_coordinate_bound_of_isCompact {d : ℕ} {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ K, ∀ i, |(x i).re| ≤ R ∧ |(x i).im| ≤ R := by
  obtain ⟨R, hR⟩ := (hK.isBounded).subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx i => ?_⟩
  have hxR : ‖x‖ ≤ max R 0 := by
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact le_trans this (le_max_left _ _)
  have hxi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  refine ⟨le_trans ?_ (le_trans hxi hxR), le_trans ?_ (le_trans hxi hxR)⟩
  · exact Complex.abs_re_le_norm (x i)
  · exact Complex.abs_im_le_norm (x i)

/-! ## The lattice decay bound -/

set_option maxHeartbeats 1000000 in
theorem exists_norm_centeredComplexGaussian_lattice_le {d : ℕ} (σ : Fin d → ℝ)
    (hσ : ∀ i, 0 < σ i) (center : Fin d → ℂ) {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin d → ℤ) (x : Fin d → ℂ), x ∈ K →
      ‖(centeredComplexGaussian σ center).1 (x + integerCastVector k)‖
        ≤ C * Real.exp (-∑ i, σ i / 2 * ((k i : ℝ)) ^ 2) := by
  obtain ⟨R, hR0, hR⟩ := exists_coordinate_bound_of_isCompact hK
  set S : ℝ := ∑ i, σ i with hSdef
  set Rc : ℝ := R + ∑ i, |(center i).re| with hRcdef
  set Ri : ℝ := R + ∑ i, |(center i).im| with hRidef
  have hRc0 : 0 ≤ Rc := by
    refine add_nonneg hR0 (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hRi0 : 0 ≤ Ri := by
    refine add_nonneg hR0 (Finset.sum_nonneg fun i _ => abs_nonneg _)
  refine ⟨Real.exp (S * (Rc ^ 2 + Ri ^ 2)), (Real.exp_pos _).le, fun k x hx => ?_⟩
  rw [norm_centeredComplexGaussian_apply, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hterm : ∀ i : Fin d,
      -(σ i * ((((x + integerCastVector k) i - center i).re) ^ 2
          - (((x + integerCastVector k) i - center i).im) ^ 2))
        ≤ σ i * (Rc ^ 2 + Ri ^ 2) + (-(σ i / 2 * ((k i : ℝ)) ^ 2)) := by
    intro i
    have hxi := hR x hx i
    have hre : (((x + integerCastVector k) i - center i)).re
        = (x i).re + (k i : ℝ) - (center i).re := by
      simp [integerCastVector, Complex.add_re, Complex.sub_re]
    have him : (((x + integerCastVector k) i - center i)).im
        = (x i).im - (center i).im := by
      simp [integerCastVector, Complex.add_im, Complex.sub_im]
    rw [hre, him]
    set t : ℝ := (x i).re - (center i).re with htdef
    set u : ℝ := (x i).im - (center i).im with hudef
    have hsum : (x i).re + (k i : ℝ) - (center i).re = (k i : ℝ) + t := by
      rw [htdef]; ring
    rw [hsum]
    have hcenter_re : |(center i).re| ≤ ∑ j, |(center j).re| :=
      Finset.single_le_sum (f := fun j => |(center j).re|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hcenter_im : |(center i).im| ≤ ∑ j, |(center j).im| :=
      Finset.single_le_sum (f := fun j => |(center j).im|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have ht : |t| ≤ Rc := by
      rw [htdef, hRcdef]
      have h1 : |(x i).re - (center i).re| ≤ |(x i).re| + |(center i).re| := abs_sub _ _
      linarith [hxi.1, hcenter_re]
    have hu : |u| ≤ Ri := by
      rw [hudef, hRidef]
      have h1 : |(x i).im - (center i).im| ≤ |(x i).im| + |(center i).im| := abs_sub _ _
      linarith [hxi.2, hcenter_im]
    have ht2 : t ^ 2 ≤ Rc ^ 2 := by
      have := abs_nonneg t
      nlinarith [ht, sq_abs t, hRc0]
    have hu2 : u ^ 2 ≤ Ri ^ 2 := by
      have := abs_nonneg u
      nlinarith [hu, sq_abs u, hRi0]
    have hkey : ((k i : ℝ) + t) ^ 2 ≥ ((k i : ℝ)) ^ 2 / 2 - t ^ 2 := by
      nlinarith [sq_nonneg ((k i : ℝ) / 2 + t), sq_nonneg ((k i : ℝ) + 2 * t)]
    have hσi := (hσ i).le
    nlinarith [hkey, ht2, hu2, hσi]
  calc -∑ i, σ i * ((((x + integerCastVector k) i - center i)).re ^ 2
        - (((x + integerCastVector k) i - center i)).im ^ 2)
      = ∑ i, -(σ i * ((((x + integerCastVector k) i - center i)).re ^ 2
        - (((x + integerCastVector k) i - center i)).im ^ 2)) := by
        rw [← Finset.sum_neg_distrib]
    _ ≤ ∑ i, (σ i * (Rc ^ 2 + Ri ^ 2) + (-(σ i / 2 * ((k i : ℝ)) ^ 2))) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = S * (Rc ^ 2 + Ri ^ 2) + -∑ i, σ i / 2 * ((k i : ℝ)) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_neg_distrib, hSdef]

end

end GaloisForLFunctions.HTGeometry
