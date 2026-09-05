import GaloisForLFunctions.HTGeometry.QuasiAbelianFlatSeedLatticeBound
import GaloisForLFunctions.HTGeometry.QuasiAbelianPositiveFactorJetAmple

/-!
# Abe's positivity condition produces the Poincaré majorant

`AbePositiveFactorPresentation` carries the polynomial-Gaussian majorant as an *unverified analytic
field*.  This module reduces that field to a single primitive growth condition on the factor:

```text
‖ψ(γ)(x)⁻¹‖ ≤ C_K · exp(a ‖γ‖₁)      uniformly on compacta,
```

which is exactly Abe's positivity of the presentation.  The seed side is unconditional
(`exists_norm_flatGaussianSeed_lattice_le`), and the exponential factor is absorbed by half of the
Gaussian: `a t - t²/4 ≤ a²` coordinatewise.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

noncomputable section

/-- **Abe's positivity growth condition.**  On every compact set the reciprocal automorphic factor
grows at most exponentially in the `ℓ¹` size of the lattice index. -/
def AutomorphicFactor.HasLatticeExponentialGrowth {d : ℕ}
    (ψ : AutomorphicFactor d (standardIntegerLattice d)) : Prop :=
  ∀ K : Set (Fin d → ℂ), IsCompact K → ∃ C a : ℝ, 0 ≤ C ∧ 0 ≤ a ∧
    ∀ (k : Fin d → ℤ) (x : Fin d → ℂ), x ∈ K →
      ‖((ψ.factor (standardIntegerLatticeEquiv d k)).1 x)⁻¹‖
        ≤ C * Real.exp (a * ∑ i, ((k i).natAbs : ℝ))

/-! ## Half a Gaussian absorbs any exponential -/

theorem exp_mul_sum_natAbs_le {d : ℕ} (a : ℝ) (k : Fin d → ℤ) :
    Real.exp (a * ∑ i, ((k i).natAbs : ℝ)) * Real.exp (-∑ i, (1 / 2 : ℝ) * ((k i : ℝ)) ^ 2)
      ≤ Real.exp ((d : ℝ) * a ^ 2) * Real.exp (-∑ i, (1 / 4 : ℝ) * ((k i : ℝ)) ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hsq : ∀ i : Fin d, ((k i).natAbs : ℝ) ^ 2 = ((k i : ℝ)) ^ 2 := by
    intro i
    have h : ((k i).natAbs : ℝ) = |(k i : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    rw [h, sq_abs]
  have hterm : ∀ i : Fin d,
      a * ((k i).natAbs : ℝ) - (1 / 4 : ℝ) * ((k i : ℝ)) ^ 2 ≤ a ^ 2 := by
    intro i
    have h := hsq i
    nlinarith [sq_nonneg (a - ((k i).natAbs : ℝ) / 2), h]
  have hsum : a * ∑ i, ((k i).natAbs : ℝ) - ∑ i, (1 / 4 : ℝ) * ((k i : ℝ)) ^ 2
      ≤ ∑ _i : Fin d, a ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => hterm i
  have hcard : ∑ _i : Fin d, a ^ 2 = (d : ℝ) * a ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hcard] at hsum
  have hhalf : ∑ i, (1 / 2 : ℝ) * ((k i : ℝ)) ^ 2
      = ∑ i, (1 / 4 : ℝ) * ((k i : ℝ)) ^ 2 + ∑ i, (1 / 4 : ℝ) * ((k i : ℝ)) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hhalf]
  linarith [hsum]

/-! ## The reduction -/

/-- **Abe's positivity growth condition supplies the polynomial-Gaussian majorant.**  The seed side
is unconditional; the factor side is exactly the exponential growth bound, and half of the Gaussian
absorbs it. -/
theorem gaussianMajorant_of_hasLatticeExponentialGrowth {d : ℕ}
    (ψ : AutomorphicFactor d (standardIntegerLattice d))
    (hψ : ψ.HasLatticeExponentialGrowth) :
    ∀ (I : Type u) [Fintype I] [DecidableEq I]
      (w : I → Fin d → ℂ)
      (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
      (m : ℕ) (hm : 0 < m),
      ∃ σ : Fin d → ℝ, (∀ c, 0 < σ c) ∧
        ∀ (target : I) (P : MvPolynomial (Fin d) ℂ),
          let S := flatIntegerLatticePacketSeparatorData w hdistinct target m hm
          let D := gaussianFlatSeedData σ (w target) hm
          let seed := multivariateEntireMul S.bump
            (multivariateEntireMul D.damping (mvPolynomialMultivariateEntire P))
          ∃ (A : Fin d → ℕ) (decay : Fin d → ℝ),
            (∀ c, 0 < decay c) ∧
            ∀ K : Set (Fin d → ℂ), IsCompact K →
              ∃ C : ℝ, 0 ≤ C ∧ ∀ k x, x ∈ K →
                ‖poincareTerm ψ seed (standardIntegerLatticeEquiv d k) x‖ ≤
                  C * polynomialGaussianLatticeWeight (Fin d) A decay k := by
  intro I _ _ w hdistinct m hm
  refine ⟨fun _ => 1, fun _ => one_pos, fun target P => ?_⟩
  refine ⟨fun i => P.degreeOf i, fun _ => 1 / 4, fun _ => by norm_num, fun K hK => ?_⟩
  obtain ⟨Cf, a, hCf0, ha0, hCf⟩ := hψ K hK
  obtain ⟨Cs, hCs0, hCs⟩ := exists_norm_flatGaussianSeed_lattice_le w hdistinct target hm
    (fun _ => (1 : ℝ)) (fun _ => one_pos) P hK
  refine ⟨Cf * Cs * Real.exp ((d : ℝ) * a ^ 2), by positivity, fun k x hx => ?_⟩
  have hfac := hCf k x hx
  have hseed := hCs k x hx
  have hval : ‖poincareTerm ψ
      (multivariateEntireMul (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
        (multivariateEntireMul (gaussianFlatSeedData (fun _ => (1 : ℝ)) (w target) hm).damping
          (mvPolynomialMultivariateEntire P)))
      (standardIntegerLatticeEquiv d k) x‖
      = ‖((ψ.factor (standardIntegerLatticeEquiv d k)).1 x)⁻¹‖
        * ‖(multivariateEntireMul
            (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
            (multivariateEntireMul
              (gaussianFlatSeedData (fun _ => (1 : ℝ)) (w target) hm).damping
              (mvPolynomialMultivariateEntire P))).1 (x + integerCastVector k)‖ := by
    rw [poincareTerm, norm_mul, standardIntegerLatticeEquiv_apply]
  rw [hval]
  have hweight2 := polynomialGaussianLatticeWeight_eq (fun i => P.degreeOf i)
    (fun _ : Fin d => (1 : ℝ) / 2) k
  have hweight4 := polynomialGaussianLatticeWeight_eq (fun i => P.degreeOf i)
    (fun _ : Fin d => (1 : ℝ) / 4) k
  have hseed' : ‖(multivariateEntireMul
      (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
      (multivariateEntireMul (gaussianFlatSeedData (fun _ => (1 : ℝ)) (w target) hm).damping
        (mvPolynomialMultivariateEntire P))).1 (x + integerCastVector k)‖
      ≤ Cs * ((∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i))
        * Real.exp (-∑ i, (1 / 2 : ℝ) * ((k i : ℝ)) ^ 2)) := by
    refine le_trans hseed (le_of_eq ?_)
    rw [hweight2]
  have habs := exp_mul_sum_natAbs_le (d := d) a k
  set Pk : ℝ := ∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i) with hPk
  have hPk0 : (0 : ℝ) ≤ Pk := Finset.prod_nonneg fun i _ => by positivity
  have hnorm0 : (0 : ℝ) ≤ ‖(multivariateEntireMul
      (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
      (multivariateEntireMul (gaussianFlatSeedData (fun _ => (1 : ℝ)) (w target) hm).damping
        (mvPolynomialMultivariateEntire P))).1 (x + integerCastVector k)‖ := norm_nonneg _
  rw [hweight4]
  calc ‖((ψ.factor (standardIntegerLatticeEquiv d k)).1 x)⁻¹‖
        * ‖(multivariateEntireMul
            (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
            (multivariateEntireMul
              (gaussianFlatSeedData (fun _ => (1 : ℝ)) (w target) hm).damping
              (mvPolynomialMultivariateEntire P))).1 (x + integerCastVector k)‖
      ≤ (Cf * Real.exp (a * ∑ i, ((k i).natAbs : ℝ)))
        * (Cs * (Pk * Real.exp (-∑ i, (1 / 2 : ℝ) * ((k i : ℝ)) ^ 2))) := by
        refine mul_le_mul hfac hseed' hnorm0 ?_
        exact mul_nonneg hCf0 (Real.exp_pos _).le
    _ = Cf * Cs * Pk * (Real.exp (a * ∑ i, ((k i).natAbs : ℝ))
        * Real.exp (-∑ i, (1 / 2 : ℝ) * ((k i : ℝ)) ^ 2)) := by ring
    _ ≤ Cf * Cs * Pk * (Real.exp ((d : ℝ) * a ^ 2)
        * Real.exp (-∑ i, (1 / 4 : ℝ) * ((k i : ℝ)) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left habs ?_
        positivity
    _ = Cf * Cs * Real.exp ((d : ℝ) * a ^ 2)
        * (Pk * Real.exp (-∑ i, (1 / 4 : ℝ) * ((k i : ℝ)) ^ 2)) := by ring

/-! ## The base case from a checkable condition -/

/-- Abe's positivity growth condition makes the factor a positive presentation. -/
def abePositiveFactorPresentationOfGrowth {d : ℕ}
    (ψ : AutomorphicFactor d (standardIntegerLattice d))
    (hψ : ψ.HasLatticeExponentialGrowth) : AbePositiveFactorPresentation.{u} d :=
  ⟨ψ, gaussianMajorant_of_hasLatticeExponentialGrowth.{u} ψ hψ⟩

/-- **The card's statement at the rank-zero base, from a checkable growth condition.**  A fixed
automorphic factor on the standard integer lattice whose reciprocal grows at most exponentially in
the lattice index interpolates every finite packet of arbitrary mixed jets at every finite order. -/
theorem AutomorphicFactor.jetAmpleEveryFiniteOrder_of_hasLatticeExponentialGrowth {d : ℕ}
    (ψ : AutomorphicFactor d (standardIntegerLattice d))
    (hψ : ψ.HasLatticeExponentialGrowth) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} ψ :=
  (abePositiveFactorPresentationOfGrowth.{u} ψ hψ).jetAmpleEveryFiniteOrder

end

end GaloisForLFunctions.HTGeometry
