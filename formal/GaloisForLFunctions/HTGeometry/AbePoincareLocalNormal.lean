import GaloisForLFunctions.HTGeometry.AbePositiveGaussianMajorant

/-!
# Local normal convergence of the complement Poincaré series

The damping datum asks for the complement Poincaré series to converge locally normally.  With the
Gaussian lattice majorant this is the Weierstrass M-test: on a compact set the difference form and
the seed are bounded, and the lattice dependence is the Gaussian weight, which is summable.

Both bounds are free.  A Hermitian form on `ℂ^d` expands in the standard basis, so `y ↦ Re D(y,y)`
is continuous; and the seed is continuous by construction.

* `hermitian_self_eq_sum`, `continuous_hermitian_self_re`;
* `summableLocallyUniformlyOn_poincareTerm_appellHumbert` — **the `normal` field of the damping
  datum**, for a seed of bounded normalised modulus.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {d c : ℕ}

/-- A Hermitian form expands in the standard basis. -/
theorem hermitian_self_eq_sum {D : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} (hD : IsHermitianForm D)
    (y : Fin d → ℂ) :
    D y y = ∑ i, ∑ j, y i * star (y j) * D (Pi.single i 1) (Pi.single j 1) := by
  have hy : y = ∑ i, (y i) • (Pi.single i 1 : Fin d → ℂ) := by
    funext t
    rw [Finset.sum_apply]
    have hterm : ∀ i : Fin d, ((y i) • (Pi.single i 1 : Fin d → ℂ)) t
        = if t = i then y t else 0 := by
      intro i
      rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases hti : t = i
      · subst hti
        rw [if_pos rfl, if_pos rfl, mul_one]
      · rw [if_neg hti, if_neg hti, mul_zero]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp
  conv_lhs => rw [hy]
  rw [hermitian_sum_left hD]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermitian_sum_right hD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem continuous_hermitian_self_re {D : (Fin d → ℂ) → (Fin d → ℂ) → ℂ}
    (hD : IsHermitianForm D) : Continuous fun y : Fin d → ℂ => (D y y).re := by
  have hfun : (fun y : Fin d → ℂ => (D y y).re)
      = fun y : Fin d → ℂ =>
        (∑ i, ∑ j, y i * star (y j) * D (Pi.single i 1) (Pi.single j 1)).re := by
    funext y
    rw [hermitian_self_eq_sum hD]
  rw [hfun]
  fun_prop

/-- **The complement Poincaré series of a seed of bounded normalised modulus converges locally
normally.** -/
theorem summableLocallyUniformlyOn_poincareTerm_appellHumbert
    {Hu Hl : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} {χu : (Fin d → ℂ) → ℂ}
    (hHu : IsHermitianForm Hu) (hHl : IsHermitianForm Hl)
    (hχu : ∀ γ, ‖χu γ‖ = 1)
    (hpos : ∀ w : Fin d → ℂ, 0 ≤ (Hu w w - Hl w w).re)
    {Γ : AddSubgroup (Fin d → ℂ)}
    (hsemiu : IsSemicharacterOn Hu χu Γ)
    (seed : MultivariateEntire d) {M : ℝ}
    (hseednorm : ∀ y : Fin d → ℂ, ‖seed.1 y‖ ≤ M * Real.exp (Real.pi / 2 * (Hl y y).re))
    (v : Fin c → (Fin d → ℂ))
    (hgram : (abeGram (fun x y => Hu x y - Hl x y) v).PosDef)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (comp_mem : ∀ z, comp z ∈ Γ)
    (hcomp : ∀ z : Fin c → ℤ, comp z = ∑ i, ((z i : ℂ)) • v i) :
    SummableLocallyUniformlyOn
      (fun (z : Fin c → ℤ) (x : Fin d → ℂ) =>
        poincareTerm (appellHumbertAutomorphicFactor hHu hχu hsemiu) seed
          (complementEmbedding comp comp_mem z) x) Set.univ := by
  have hD : IsHermitianForm fun x y => Hu x y - Hl x y := hHu.sub hHl
  have hM : 0 ≤ M := by
    have h := hseednorm 0
    have h0 : (0 : ℝ) ≤ ‖seed.1 0‖ := norm_nonneg _
    nlinarith [Real.exp_pos (Real.pi / 2 * (Hl 0 0).re), h, h0]
  obtain ⟨sigma, hsigma, hgauss⟩ :=
    exists_gaussian_of_posDef hD v hgram (t := Real.pi / 4) (by positivity)
  refine summableLocallyUniformlyOn_of_polynomialGaussianLattice_bound _ _ isOpen_univ
    (fun _ => 0) (fun _ => sigma) (fun _ => hsigma) ?_
  intro K _ hK
  obtain ⟨CD, hCD⟩ := hK.exists_bound_of_continuousOn
    (f := fun y : Fin d → ℂ => (Hu y y - Hl y y).re)
    ((continuous_hermitian_self_re hD).continuousOn)
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn
    (f := fun y : Fin d → ℂ => (Hl y y).re)
    ((continuous_hermitian_self_re hHl).continuousOn)
  set C₀ : ℝ := Real.sqrt (max CD 0) with hC₀def
  have hC₀ : 0 ≤ C₀ := Real.sqrt_nonneg _
  have hC₀sq : CD ≤ C₀ ^ 2 := by
    rw [hC₀def, Real.sq_sqrt (le_max_right CD 0)]
    exact le_max_left CD 0
  refine ⟨M * Real.exp (Real.pi / 2 * L) * Real.exp (Real.pi * C₀ ^ 2), by positivity,
    fun z x hx => ?_⟩
  have hzsup : (Hu x x - Hl x x).re ≤ C₀ ^ 2 := by
    refine le_trans (le_trans (le_abs_self _) ?_) hC₀sq
    simpa using hCD x hx
  have hLsup : (Hl x x).re ≤ L := by
    refine le_trans (le_abs_self _) ?_
    simpa using hL x hx
  have hbase := norm_poincareTerm_appellHumbert_le hHu hHl hχu hpos hC₀ hzsup hsemiu
    seed hseednorm (complementEmbedding comp comp_mem z)
  have hexp : Real.exp (-(Real.pi / 4)
      * (Hu (complementEmbedding comp comp_mem z).1 (complementEmbedding comp comp_mem z).1
          - Hl (complementEmbedding comp comp_mem z).1
              (complementEmbedding comp comp_mem z).1).re)
      ≤ polynomialGaussianLatticeWeight (Fin c) (fun _ => 0) (fun _ => sigma) z := by
    rw [polynomialGaussianLatticeWeight_zero_exponent]
    have h := hgauss z
    rw [show (∑ i, ((z i : ℂ)) • v i) = (complementEmbedding comp comp_mem z).1 from
      (hcomp z).symm] at h
    exact h
  have hmono : M * Real.exp (Real.pi / 2 * (Hl x x).re)
      ≤ M * Real.exp (Real.pi / 2 * L) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
    nlinarith [Real.pi_pos, hLsup]
  refine le_trans hbase ?_
  calc M * Real.exp (Real.pi / 2 * (Hl x x).re) * Real.exp (Real.pi * C₀ ^ 2)
        * Real.exp (-(Real.pi / 4)
          * (Hu (complementEmbedding comp comp_mem z).1 (complementEmbedding comp comp_mem z).1
            - Hl (complementEmbedding comp comp_mem z).1
                (complementEmbedding comp comp_mem z).1).re)
      ≤ M * Real.exp (Real.pi / 2 * L) * Real.exp (Real.pi * C₀ ^ 2)
        * polynomialGaussianLatticeWeight (Fin c) (fun _ => 0) (fun _ => sigma) z := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hmono (Real.exp_nonneg _)) hexp
          (Real.exp_nonneg _) (by positivity)
    _ = M * Real.exp (Real.pi / 2 * L) * Real.exp (Real.pi * C₀ ^ 2)
        * polynomialGaussianLatticeWeight (Fin c) (fun _ => 0) (fun _ => sigma) z := rfl

end

end GaloisForLFunctions.HTGeometry
