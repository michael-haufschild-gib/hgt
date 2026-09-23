import GaloisForLFunctions.HTGeometry.QuasiAbelianPolynomialLatticeGrowth

/-!
# The Gaussian-flat interpolation seed obeys the polynomial-Gaussian lattice weight

Abe's seed is `bump · damping · P`.  Along the real integer lattice each factor is now controlled:

* `bump` is strip bounded, hence *uniformly* bounded (`QuasiAbelianIntegerLatticeSeparator`);
* `damping = 1 - (1 - G)^m = G · ∑_{r<m}(1-G)^r` inherits the Gaussian decay of `G`
  (`QuasiAbelianGaussianLatticeDecay`), the geometric cofactor being bounded because `G` is;
* `P` grows like `∏_i (1+|k_i|)^{deg_i P}` (`QuasiAbelianPolynomialLatticeGrowth`).

Multiplying the three gives exactly `polynomialGaussianLatticeWeight` at exponents
`A_i = deg_i P` and `decay_i = σ_i / 2`.  No hypothesis on the automorphic factor enters.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The weight splits into its two factors -/

theorem polynomialGaussianLatticeWeight_eq {d : ℕ} (A : Fin d → ℕ) (sigma : Fin d → ℝ)
    (k : Fin d → ℤ) :
    polynomialGaussianLatticeWeight (Fin d) A sigma k
      = (∏ i, (1 + ((k i).natAbs : ℝ)) ^ A i)
        * Real.exp (-∑ i, sigma i * ((k i : ℝ)) ^ (2 : ℕ)) := by
  rw [polynomialGaussianLatticeWeight, Finset.prod_mul_distrib]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  simp only [neg_mul]
  rw [← Finset.sum_neg_distrib]

/-! ## The damping factor -/

theorem damping_apply_eq {d m : ℕ} (σ : Fin d → ℝ) (center : Fin d → ℂ) (hm : 0 < m)
    (z : Fin d → ℂ) :
    (gaussianFlatSeedData σ center hm).damping.1 z
      = 1 - (1 - (centeredComplexGaussian σ center).1 z) ^ m := by
  rw [(gaussianFlatSeedData σ center hm).damping_eq]
  have hsub : ∀ (f g : MultivariateEntire d) (y : Fin d → ℂ), (f - g).1 y = f.1 y - g.1 y :=
    fun _ _ _ => rfl
  have hone : (mvPolynomialMultivariateEntire (1 : MvPolynomial (Fin d) ℂ)).1 z = 1 := by
    simp [mvPolynomialMultivariateEntire]
  rw [hsub, multivariateEntirePow_apply, hsub, hone]
  rfl

theorem norm_damping_le {d m : ℕ} (σ : Fin d → ℝ) (center : Fin d → ℂ) (hm : 0 < m)
    (z : Fin d → ℂ) :
    ‖(gaussianFlatSeedData σ center hm).damping.1 z‖
      ≤ ‖(centeredComplexGaussian σ center).1 z‖ *
        ∑ r ∈ Finset.range m, (1 + ‖(centeredComplexGaussian σ center).1 z‖) ^ r := by
  set g : ℂ := (centeredComplexGaussian σ center).1 z with hgdef
  have hid : (1 : ℂ) - (1 - g) ^ m = (∑ r ∈ Finset.range m, (1 - g) ^ r) * g := by
    have h := geom_sum_mul_neg (1 - g) m
    simpa using h.symm
  rw [damping_apply_eq, hid, norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg g)
  refine le_trans (norm_sum_le (Finset.range m) (fun r => (1 - g) ^ r)) ?_
  refine Finset.sum_le_sum fun r _ => ?_
  rw [norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg ((1 : ℂ) - g)) ?_ r
  have h1 : ‖(1 : ℂ) - g‖ ≤ ‖(1 : ℂ)‖ + ‖g‖ := norm_sub_le _ _
  simpa using h1

set_option maxHeartbeats 1000000 in
theorem exists_norm_damping_lattice_le {d m : ℕ} (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    (center : Fin d → ℂ) (hm : 0 < m) {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin d → ℤ) (x : Fin d → ℂ), x ∈ K →
      ‖(gaussianFlatSeedData σ center hm).damping.1 (x + integerCastVector k)‖
        ≤ C * Real.exp (-∑ i, σ i / 2 * ((k i : ℝ)) ^ (2 : ℕ)) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_norm_centeredComplexGaussian_lattice_le σ hσ center hK
  refine ⟨C₀ * ∑ r ∈ Finset.range m, (1 + C₀) ^ r,
    mul_nonneg hC₀ (Finset.sum_nonneg fun r _ => pow_nonneg (by linarith) r),
    fun k x hx => ?_⟩
  set g : ℂ := (centeredComplexGaussian σ center).1 (x + integerCastVector k) with hgdef
  have hdecay : ‖g‖ ≤ C₀ * Real.exp (-∑ i, σ i / 2 * ((k i : ℝ)) ^ (2 : ℕ)) := hC k x hx
  have hexple : Real.exp (-∑ i, σ i / 2 * ((k i : ℝ)) ^ (2 : ℕ)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : (0 : ℝ) ≤ ∑ i, σ i / 2 * ((k i : ℝ)) ^ (2 : ℕ) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [hσ i]) (sq_nonneg _)
    linarith
  have hbound : ‖g‖ ≤ C₀ := by
    refine le_trans hdecay ?_
    nlinarith [hexple, hC₀]
  have hgeom : ∑ r ∈ Finset.range m, (1 + ‖g‖) ^ r ≤ ∑ r ∈ Finset.range m, (1 + C₀) ^ r := by
    refine Finset.sum_le_sum fun r _ => ?_
    refine pow_le_pow_left₀ (by positivity) ?_ r
    linarith
  have hgeom0 : (0 : ℝ) ≤ ∑ r ∈ Finset.range m, (1 + ‖g‖) ^ r :=
    Finset.sum_nonneg fun r _ => by positivity
  calc ‖(gaussianFlatSeedData σ center hm).damping.1 (x + integerCastVector k)‖
      ≤ ‖g‖ * ∑ r ∈ Finset.range m, (1 + ‖g‖) ^ r := norm_damping_le σ center hm _
    _ ≤ (C₀ * Real.exp (-∑ i, σ i / 2 * ((k i : ℝ)) ^ (2 : ℕ)))
        * ∑ r ∈ Finset.range m, (1 + C₀) ^ r := by
        refine mul_le_mul hdecay hgeom hgeom0 ?_
        exact mul_nonneg hC₀ (Real.exp_pos _).le
    _ = C₀ * (∑ r ∈ Finset.range m, (1 + C₀) ^ r)
        * Real.exp (-∑ i, σ i / 2 * ((k i : ℝ)) ^ (2 : ℕ)) := by ring

/-! ## The full seed -/

set_option maxHeartbeats 1000000 in
/-- **The Gaussian-flat interpolation seed obeys the polynomial-Gaussian lattice weight.**  No
hypothesis on the automorphic factor enters: this is the seed half of Abe's growth stability
lemma, in the exact shape the Poincaré majorant consumes. -/
theorem exists_norm_flatGaussianSeed_lattice_le {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ) (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (target : I) {m : ℕ} (hm : 0 < m) (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    (P : MvPolynomial (Fin d) ℂ) {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin d → ℤ) (x : Fin d → ℂ), x ∈ K →
      ‖(multivariateEntireMul (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
          (multivariateEntireMul (gaussianFlatSeedData σ (w target) hm).damping
            (mvPolynomialMultivariateEntire P))).1 (x + integerCastVector k)‖
        ≤ C * polynomialGaussianLatticeWeight (Fin d) (fun i => P.degreeOf i)
            (fun i => σ i / 2) k := by
  classical
  obtain ⟨R, hR0, hR⟩ := exists_coordinate_bound_of_isCompact hK
  obtain ⟨Cb, hCb0, hCb⟩ :=
    (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump_stripBounded R
  obtain ⟨Cd, hCd0, hCd⟩ := exists_norm_damping_lattice_le σ hσ (w target) hm hK
  obtain ⟨Cp, hCp0, hCp⟩ := exists_norm_mvPolynomial_lattice_le P hK
  refine ⟨Cb * (Cd * Cp), by positivity, fun k x hx => ?_⟩
  have hstrip : ∀ c : Fin d, |((x + integerCastVector k) c).im| ≤ R := by
    intro c
    have him : ((x + integerCastVector k) c).im = (x c).im := by
      simp [integerCastVector, Complex.add_im]
    rw [him]
    exact (hR x hx c).2
  have h1 := hCb (x + integerCastVector k) hstrip
  have h2 := hCd k x hx
  have h3 := hCp k x hx
  have hval : (multivariateEntireMul
      (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
        (multivariateEntireMul (gaussianFlatSeedData σ (w target) hm).damping
          (mvPolynomialMultivariateEntire P))).1 (x + integerCastVector k)
      = (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump.1
          (x + integerCastVector k)
        * ((gaussianFlatSeedData σ (w target) hm).damping.1 (x + integerCastVector k)
          * MvPolynomial.eval (x + integerCastVector k) P) := rfl
  rw [hval, norm_mul, norm_mul, polynomialGaussianLatticeWeight_eq]
  have hd0 : (0 : ℝ) ≤ ‖(gaussianFlatSeedData σ (w target) hm).damping.1
      (x + integerCastVector k)‖ := norm_nonneg _
  have hp0 : (0 : ℝ) ≤ ‖MvPolynomial.eval (x + integerCastVector k) P‖ := norm_nonneg _
  have hb0 : (0 : ℝ) ≤ ‖(flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump.1
      (x + integerCastVector k)‖ := norm_nonneg _
  have hstep : ‖(gaussianFlatSeedData σ (w target) hm).damping.1 (x + integerCastVector k)‖
      * ‖MvPolynomial.eval (x + integerCastVector k) P‖
      ≤ (Cd * Real.exp (-∑ i, σ i / 2 * ((k i : ℝ)) ^ (2 : ℕ)))
        * (Cp * ∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i)) := by
    refine mul_le_mul h2 h3 hp0 ?_
    exact mul_nonneg hCd0 (Real.exp_pos _).le
  calc ‖(flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump.1
        (x + integerCastVector k)‖
      * (‖(gaussianFlatSeedData σ (w target) hm).damping.1 (x + integerCastVector k)‖
        * ‖MvPolynomial.eval (x + integerCastVector k) P‖)
      ≤ Cb * ((Cd * Real.exp (-∑ i, σ i / 2 * ((k i : ℝ)) ^ (2 : ℕ)))
        * (Cp * ∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i))) := by
        refine mul_le_mul h1 hstep (mul_nonneg hd0 hp0) hCb0
    _ = Cb * (Cd * Cp) * ((∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i))
        * Real.exp (-∑ i, σ i / 2 * ((k i : ℝ)) ^ (2 : ℕ))) := by ring

end

end GaloisForLFunctions.HTGeometry
