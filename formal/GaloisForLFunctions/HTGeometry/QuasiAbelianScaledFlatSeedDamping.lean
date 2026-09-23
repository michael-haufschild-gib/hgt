import GaloisForLFunctions.HTGeometry.QuasiAbelianScaledGaussianDamping
import GaloisForLFunctions.HTGeometry.QuasiAbelianFlatSeedLatticeBound

/-!
# The damped flat seed

Of the three factors of the interpolation seed — the packet separator, the Gaussian damping and the
polynomial column — only the damping carries the scale.  Rescaling it therefore transports the
exponential damping of the Gaussian straight to the seed, while the separator's strip bound and the
polynomial's lattice growth stay untouched.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The rescaled flat seed is exponentially damped in the scale on every nonzero lattice
translate**, in the exact shape the Poincaré majorant consumes. -/
theorem exists_norm_scaledFlatSeed_lattice_damped {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ) (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (target : I) {m : ℕ} (hm : 0 < m) (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    {ρ σ₀ : ℝ} (hσ₀le : ∀ i, σ₀ ≤ σ i)
    (hpos : 0 ≤ σ₀ / 4 - (∑ i, σ i) * (2 * ρ ^ (2 : ℕ)))
    (P : MvPolynomial (Fin d) ℂ) {K : Set (Fin d → ℂ)} (hK : IsCompact K)
    (hKb : ∀ x ∈ K, ∀ i, |(x i).re - (w target i).re| ≤ ρ ∧ |(x i).im - (w target i).im| ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 1 ≤ B → ∀ k : Fin d → ℤ, k ≠ 0 → ∀ x ∈ K,
      ‖(multivariateEntireMul (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
          (multivariateEntireMul (gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping
            (mvPolynomialMultivariateEntire P))).1 (x + integerCastVector k)‖
        ≤ C * Real.exp (-((σ₀ / 4 - (∑ i, σ i) * (2 * ρ ^ (2 : ℕ))) * B))
          * polynomialGaussianLatticeWeight (Fin d) (fun i => P.degreeOf i)
              (fun i => σ i / 4) k := by
  classical
  obtain ⟨R, hR0, hR⟩ := exists_coordinate_bound_of_isCompact hK
  obtain ⟨Cb, hCb0, hCb⟩ :=
    (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump_stripBounded R
  obtain ⟨Cp, hCp0, hCp⟩ := exists_norm_mvPolynomial_lattice_le P hK
  refine ⟨Cb * ((2 : ℝ) ^ m * Cp), by positivity, fun B hB k hk x hx => ?_⟩
  set rate : ℝ := σ₀ / 4 - (∑ i, σ i) * (2 * ρ ^ (2 : ℕ)) with hrate
  set G : ℂ := (centeredComplexGaussian (fun i => B * σ i) (w target)).1
    (x + integerCastVector k) with hGdef
  have hB0 : (0 : ℝ) < B := by linarith
  have hGbound : ‖G‖ ≤ Real.exp (-(rate * B))
      * Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ)) :=
    norm_scaledGaussian_lattice_damped σ hσ (w target) hσ₀le hKb hB hk hx
  have hexp1 : Real.exp (-(rate * B)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ rate * B := mul_nonneg hpos hB0.le
    linarith
  have hexp2 : Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : (0 : ℝ) ≤ ∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [hσ i]) (sq_nonneg _)
    linarith
  have hGle1 : ‖G‖ ≤ 1 := by
    refine le_trans hGbound ?_
    nlinarith [hexp1, hexp2, (Real.exp_pos (-(rate * B))).le,
      (Real.exp_pos (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ))).le]
  -- the geometric factor of the damping is uniformly bounded
  have hgeom : ∑ r ∈ Finset.range m, (1 + ‖G‖) ^ r ≤ (2 : ℝ) ^ m := by
    have hle : ∀ r ∈ Finset.range m, (1 + ‖G‖) ^ r ≤ (2 : ℝ) ^ r := fun r _ =>
      pow_le_pow_left₀ (by positivity) (by linarith) r
    refine le_trans (Finset.sum_le_sum hle) ?_
    have hgs : ∑ r ∈ Finset.range m, (2 : ℝ) ^ r = 2 ^ m - 1 := by
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      ring
    rw [hgs]
    linarith
  have hdamp : ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1
      (x + integerCastVector k)‖ ≤ ‖G‖ * (2 : ℝ) ^ m := by
    refine le_trans (norm_damping_le (fun i => B * σ i) (w target) hm _) ?_
    exact mul_le_mul_of_nonneg_left hgeom (norm_nonneg _)
  -- the separator's strip bound
  have hstrip : ∀ c : Fin d, |((x + integerCastVector k) c).im| ≤ R := by
    intro c
    have him : ((x + integerCastVector k) c).im = (x c).im := by
      simp [integerCastVector, Complex.add_im]
    rw [him]
    exact (hR x hx c).2
  have h1 := hCb (x + integerCastVector k) hstrip
  have h3 := hCp k x hx
  have hval : (multivariateEntireMul
      (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
        (multivariateEntireMul (gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping
          (mvPolynomialMultivariateEntire P))).1 (x + integerCastVector k)
      = (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump.1
          (x + integerCastVector k)
        * ((gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1
            (x + integerCastVector k)
          * MvPolynomial.eval (x + integerCastVector k) P) := rfl
  rw [hval, norm_mul, norm_mul, polynomialGaussianLatticeWeight_eq]
  have hprod0 : (0 : ℝ) ≤ ∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i) :=
    Finset.prod_nonneg fun i _ => by positivity
  have hstep : ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1
        (x + integerCastVector k)‖ * ‖MvPolynomial.eval (x + integerCastVector k) P‖
      ≤ ((2 : ℝ) ^ m * Cp) * (Real.exp (-(rate * B))
          * ((∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i))
            * Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ)))) := by
    have hd1 : ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1
        (x + integerCastVector k)‖
        ≤ (2 : ℝ) ^ m * (Real.exp (-(rate * B))
          * Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ))) := by
      refine le_trans hdamp ?_
      nlinarith [hGbound, norm_nonneg G, pow_pos (by norm_num : (0:ℝ) < 2) m]
    have hd0 : (0 : ℝ) ≤ (2 : ℝ) ^ m * (Real.exp (-(rate * B))
        * Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ))) := by positivity
    calc ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1
            (x + integerCastVector k)‖ * ‖MvPolynomial.eval (x + integerCastVector k) P‖
        ≤ ((2 : ℝ) ^ m * (Real.exp (-(rate * B))
            * Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ))))
          * (Cp * ∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i)) :=
          mul_le_mul hd1 h3 (norm_nonneg _) hd0
      _ = ((2 : ℝ) ^ m * Cp) * (Real.exp (-(rate * B))
          * ((∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i))
            * Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ)))) := by ring
  have hrhs : (0 : ℝ) ≤ ((2 : ℝ) ^ m * Cp) * (Real.exp (-(rate * B))
      * ((∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i))
        * Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ)))) := by positivity
  calc ‖(flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump.1
          (x + integerCastVector k)‖
        * (‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1
            (x + integerCastVector k)‖
          * ‖MvPolynomial.eval (x + integerCastVector k) P‖)
      ≤ Cb * (((2 : ℝ) ^ m * Cp) * (Real.exp (-(rate * B))
          * ((∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i))
            * Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ))))) :=
        mul_le_mul h1 hstep (by positivity) hCb0
    _ = Cb * ((2 : ℝ) ^ m * Cp) * Real.exp (-(rate * B))
        * ((∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i))
          * Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ (2 : ℕ))) := by ring

/-- **The rescaled flat seed is exponentially damped on every real translate carrying enough
Gaussian mass.**  This is the form the general complement of a quasi-Abelian lattice needs, where
the translates are real but not integral. -/
theorem exists_norm_scaledFlatSeed_realTranslate_damped {d : ℕ} {I : Type*} [Fintype I]
    [DecidableEq I] (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (target : I) {m : ℕ} (hm : 0 < m) (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    {ρ σ₀ : ℝ} (hpos : 0 ≤ σ₀ / 4 - (∑ i, σ i) * (2 * ρ ^ (2 : ℕ)))
    (P : MvPolynomial (Fin d) ℂ) {K : Set (Fin d → ℂ)} (hK : IsCompact K)
    (hKb : ∀ x ∈ K, ∀ i, |(x i).re - (w target i).re| ≤ ρ ∧ |(x i).im - (w target i).im| ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 1 ≤ B → ∀ v : Fin d → ℝ, σ₀ ≤ ∑ i, σ i * (v i) ^ (2 : ℕ) → ∀ x ∈ K,
      ‖(multivariateEntireMul (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
          (multivariateEntireMul (gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping
            (mvPolynomialMultivariateEntire P))).1 (x + fun i => ((v i : ℝ) : ℂ))‖
        ≤ C * Real.exp (-((σ₀ / 4 - (∑ i, σ i) * (2 * ρ ^ (2 : ℕ))) * B))
          * ((∏ i, (1 + |v i|) ^ (P.degreeOf i))
            * Real.exp (-∑ i, σ i / 4 * (v i) ^ (2 : ℕ))) := by
  classical
  obtain ⟨R, hR0, hR⟩ := exists_coordinate_bound_of_isCompact hK
  obtain ⟨Cb, hCb0, hCb⟩ :=
    (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump_stripBounded R
  obtain ⟨Cp, hCp0, hCp⟩ := exists_norm_mvPolynomial_eval_le P
  refine ⟨Cb * ((2 : ℝ) ^ m * (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i))), by positivity,
    fun B hB v hv x hx => ?_⟩
  set rate : ℝ := σ₀ / 4 - (∑ i, σ i) * (2 * ρ ^ (2 : ℕ)) with hrate
  set y : Fin d → ℂ := x + fun i => ((v i : ℝ) : ℂ) with hy
  set G : ℂ := (centeredComplexGaussian (fun i => B * σ i) (w target)).1 y with hGdef
  have hB0 : (0 : ℝ) < B := by linarith
  have hGbound : ‖G‖ ≤ Real.exp (-(rate * B)) * Real.exp (-∑ i, σ i / 4 * (v i) ^ (2 : ℕ)) :=
    norm_scaledGaussian_realTranslate_damped σ hσ (w target) hKb hB hv hx
  have hexp1 : Real.exp (-(rate * B)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hpos hB0.le])
  have hexp2 : Real.exp (-∑ i, σ i / 4 * (v i) ^ (2 : ℕ)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : (0 : ℝ) ≤ ∑ i, σ i / 4 * (v i) ^ (2 : ℕ) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [hσ i]) (sq_nonneg _)
    linarith
  have hGle1 : ‖G‖ ≤ 1 := by
    refine le_trans hGbound ?_
    nlinarith [hexp1, hexp2, (Real.exp_pos (-(rate * B))).le,
      (Real.exp_pos (-∑ i, σ i / 4 * (v i) ^ (2 : ℕ))).le]
  have hgeom : ∑ r ∈ Finset.range m, (1 + ‖G‖) ^ r ≤ (2 : ℝ) ^ m := by
    have hle : ∀ r ∈ Finset.range m, (1 + ‖G‖) ^ r ≤ (2 : ℝ) ^ r := fun r _ =>
      pow_le_pow_left₀ (by positivity) (by linarith) r
    refine le_trans (Finset.sum_le_sum hle) ?_
    have hgs : ∑ r ∈ Finset.range m, (2 : ℝ) ^ r = 2 ^ m - 1 := by
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      ring
    rw [hgs]
    linarith
  have hdamp : ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y‖
      ≤ ‖G‖ * (2 : ℝ) ^ m :=
    le_trans (norm_damping_le (fun i => B * σ i) (w target) hm _)
      (mul_le_mul_of_nonneg_left hgeom (norm_nonneg _))
  -- the separator stays in the strip: a real translate does not move imaginary parts
  have hstrip : ∀ c : Fin d, |(y c).im| ≤ R := by
    intro c
    have him : (y c).im = (x c).im := by simp [hy, Complex.add_im]
    rw [him]
    exact (hR x hx c).2
  have h1 := hCb y hstrip
  -- the polynomial factor
  have hcoord : ∀ i : Fin d, 1 + ‖y i‖ ≤ (1 + 2 * R) * (1 + |v i|) := by
    intro i
    have hxi := hR x hx i
    have hxnorm : ‖x i‖ ≤ 2 * R := by
      have := Complex.norm_le_abs_re_add_abs_im (x i)
      linarith [hxi.1, hxi.2]
    have hyi : ‖y i‖ ≤ ‖x i‖ + |v i| := by
      have hval : y i = x i + ((v i : ℝ) : ℂ) := by simp [hy]
      rw [hval]
      refine le_trans (norm_add_le _ _) ?_
      simp
    nlinarith [abs_nonneg (v i), norm_nonneg (x i), hR0]
  have h3 : ‖MvPolynomial.eval y P‖
      ≤ (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)) * ∏ i, (1 + |v i|) ^ (P.degreeOf i) := by
    refine le_trans (hCp y) ?_
    have hprod : ∏ i, (1 + ‖y i‖) ^ (P.degreeOf i)
        ≤ ∏ i, ((1 + 2 * R) * (1 + |v i|)) ^ (P.degreeOf i) :=
      Finset.prod_le_prod (fun i _ => by positivity)
        (fun i _ => pow_le_pow_left₀ (by positivity) (hcoord i) _)
    have hsplit : ∏ i, ((1 + 2 * R) * (1 + |v i|)) ^ (P.degreeOf i)
        = (∏ i, (1 + 2 * R) ^ (P.degreeOf i)) * ∏ i, (1 + |v i|) ^ (P.degreeOf i) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [mul_pow]
    calc Cp * ∏ i, (1 + ‖y i‖) ^ (P.degreeOf i)
        ≤ Cp * ∏ i, ((1 + 2 * R) * (1 + |v i|)) ^ (P.degreeOf i) :=
          mul_le_mul_of_nonneg_left hprod hCp0
      _ = (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)) * ∏ i, (1 + |v i|) ^ (P.degreeOf i) := by
          rw [hsplit]; ring
  have hval : (multivariateEntireMul
      (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
        (multivariateEntireMul (gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping
          (mvPolynomialMultivariateEntire P))).1 y
      = (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump.1 y
        * ((gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y
          * MvPolynomial.eval y P) := rfl
  rw [hval, norm_mul, norm_mul]
  have hdampbound : ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y‖
      ≤ (2 : ℝ) ^ m * (Real.exp (-(rate * B)) * Real.exp (-∑ i, σ i / 4 * (v i) ^ (2 : ℕ))) := by
    refine le_trans hdamp ?_
    nlinarith [hGbound, norm_nonneg G, pow_pos (by norm_num : (0:ℝ) < 2) m]
  have hprodv0 : (0 : ℝ) ≤ ∏ i, (1 + |v i|) ^ (P.degreeOf i) :=
    Finset.prod_nonneg fun i _ => by positivity
  have hstep : ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y‖
        * ‖MvPolynomial.eval y P‖
      ≤ ((2 : ℝ) ^ m * (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)))
        * (Real.exp (-(rate * B))
          * ((∏ i, (1 + |v i|) ^ (P.degreeOf i))
            * Real.exp (-∑ i, σ i / 4 * (v i) ^ (2 : ℕ)))) := by
    calc ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y‖
          * ‖MvPolynomial.eval y P‖
        ≤ ((2 : ℝ) ^ m * (Real.exp (-(rate * B)) * Real.exp (-∑ i, σ i / 4 * (v i) ^ (2 : ℕ))))
          * ((Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)) * ∏ i, (1 + |v i|) ^ (P.degreeOf i)) :=
          mul_le_mul hdampbound h3 (norm_nonneg _) (by positivity)
      _ = ((2 : ℝ) ^ m * (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)))
          * (Real.exp (-(rate * B))
            * ((∏ i, (1 + |v i|) ^ (P.degreeOf i))
              * Real.exp (-∑ i, σ i / 4 * (v i) ^ (2 : ℕ)))) := by ring
  calc ‖(flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump.1 y‖
        * (‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y‖
          * ‖MvPolynomial.eval y P‖)
      ≤ Cb * (((2 : ℝ) ^ m * (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)))
          * (Real.exp (-(rate * B))
            * ((∏ i, (1 + |v i|) ^ (P.degreeOf i))
              * Real.exp (-∑ i, σ i / 4 * (v i) ^ (2 : ℕ))))) :=
        mul_le_mul h1 hstep (by positivity) hCb0
    _ = Cb * ((2 : ℝ) ^ m * (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)))
        * Real.exp (-(rate * B))
        * ((∏ i, (1 + |v i|) ^ (P.degreeOf i))
          * Real.exp (-∑ i, σ i / 4 * (v i) ^ (2 : ℕ))) := by ring

end

end GaloisForLFunctions.HTGeometry
