import GaloisForLFunctions.HTGeometry.LatticeGaussianSummability

/-!
# The periodized Gaussian does not vanish at its centre

At the centre every lattice copy of the Gaussian contributes a **positive real** number — the
translate is real, so the quadratic form in the exponent is real — and the copy at the origin
contributes exactly `1`.  So the periodization is at least `1` there, and in particular nonzero,
which is what allows it to be normalized into a multiplier that is the identity on the jet packet.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A real translate of the centre gives a positive real value. -/
theorem centeredComplexGaussian_real_translate {d : ℕ} (σ : Fin d → ℝ) (center : Fin d → ℂ)
    (v : Fin d → ℝ) :
    (centeredComplexGaussian σ center).1 (center + fun i => ((v i : ℝ) : ℂ))
      = ((Real.exp (-∑ i, σ i * (v i) ^ (2 : ℕ)) : ℝ) : ℂ) := by
  rw [centeredComplexGaussian_apply]
  rw [Complex.ofReal_exp]
  congr 1
  rw [Complex.ofReal_neg, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hval : (center + fun j => ((v j : ℝ) : ℂ)) i - center i = ((v i : ℝ) : ℂ) := by
    simp
  rw [hval]
  push_cast
  ring

/-- **The periodized Gaussian is at least one at its centre.** -/
theorem one_le_latticePeriodization_center {d k : ℕ}
    (vec : (Fin k → ℤ) → Fin d → ℝ)
    (hvec0 : ∀ i, vec 0 i = 0) (σ : Fin d → ℝ)
    (hsum : Summable fun n : Fin k → ℤ => Real.exp (-∑ i, σ i * (vec n i) ^ (2 : ℕ))) :
    (1 : ℝ) ≤ ∑' n : Fin k → ℤ, Real.exp (-∑ i, σ i * (vec n i) ^ (2 : ℕ)) := by
  have hzero : Real.exp (-∑ i, σ i * (vec 0 i) ^ (2 : ℕ)) = 1 := by
    have : ∑ i, σ i * (vec 0 i) ^ (2 : ℕ) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hvec0 i]
      ring
    rw [this, neg_zero, Real.exp_zero]
  calc (1 : ℝ) = Real.exp (-∑ i, σ i * (vec 0 i) ^ (2 : ℕ)) := hzero.symm
    _ ≤ ∑' n : Fin k → ℤ, Real.exp (-∑ i, σ i * (vec n i) ^ (2 : ℕ)) :=
        hsum.le_tsum 0 (fun n _ => (Real.exp_pos _).le)

/-- **The periodization at the centre is a positive real**, hence nonzero. -/
theorem latticePeriodizationFun_center_ne_zero {d k : ℕ} (emb : (Fin k → ℤ) →+ (Fin d → ℂ))
    (vec : (Fin k → ℤ) → Fin d → ℝ) (hvec : ∀ n i, emb n i = ((vec n i : ℝ) : ℂ))
    (hvec0 : ∀ i, vec 0 i = 0) (σ : Fin d → ℝ) (center : Fin d → ℂ)
    (hsum : Summable fun n : Fin k → ℤ => Real.exp (-∑ i, σ i * (vec n i) ^ (2 : ℕ))) :
    latticePeriodizationFun emb (centeredComplexGaussian σ center) center ≠ 0 := by
  have hterm : ∀ n : Fin k → ℤ,
      (centeredComplexGaussian σ center).1 (center + emb n)
        = ((Real.exp (-∑ i, σ i * (vec n i) ^ (2 : ℕ)) : ℝ) : ℂ) := by
    intro n
    have hpt : center + emb n = center + fun i => ((vec n i : ℝ) : ℂ) := by
      funext i
      rw [Pi.add_apply, Pi.add_apply, hvec n i]
    rw [hpt, centeredComplexGaussian_real_translate]
  have hval : latticePeriodizationFun emb (centeredComplexGaussian σ center) center
      = ((∑' n : Fin k → ℤ, Real.exp (-∑ i, σ i * (vec n i) ^ (2 : ℕ)) : ℝ) : ℂ) := by
    rw [latticePeriodizationFun]
    rw [show (fun n : Fin k → ℤ => (centeredComplexGaussian σ center).1 (center + emb n))
        = fun n : Fin k → ℤ => ((Real.exp (-∑ i, σ i * (vec n i) ^ (2 : ℕ)) : ℝ) : ℂ) from
      funext hterm]
    exact (Complex.ofRealCLM.map_tsum hsum).symm
  rw [hval]
  have hone := one_le_latticePeriodization_center vec hvec0 σ hsum
  simp only [ne_eq, Complex.ofReal_eq_zero]
  linarith

end

end GaloisForLFunctions.HTGeometry
