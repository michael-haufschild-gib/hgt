import GaloisForLFunctions.HTGeometry.InfiniteOccupationLaw
import GaloisForLFunctions.HTGeometry.GeneralPrimaryFactor

/-!
# Infinite-order multiple elliptic gamma products

An arbitrary nome family `p : ι → ℂ` generates the bosonic occupation spectrum indexed by
finitely supported functions `ν : ι →₀ ℕ`, with occupation monomial `p^ν`.  This file proves that
the `(g+1)`-summability threshold of that whole spectrum is exactly the threshold of the original
nome family.  It then constructs the corresponding infinite-order genus-`g` canonical product.
-/

namespace HTGeometry

open scoped BigOperators ENNReal

noncomputable def nomeMonomial {ι : Type*}
    (p : ι → ℂ) (ν : ι →₀ ℕ) : ℂ :=
  ν.prod fun a n => p a ^ n

@[simp] theorem nnnorm_nomeMonomial {ι : Type*}
    (p : ι → ℂ) (ν : ι →₀ ℕ) :
    ‖nomeMonomial p ν‖₊ = ν.prod fun a n => ‖p a‖₊ ^ n := by
  classical
  rw [nomeMonomial, Finsupp.prod, nnnorm_prod]
  rw [Finsupp.prod]
  apply Finset.prod_congr rfl
  intro a _
  exact nnnorm_pow _ _

theorem nomeMonomial_ne_zero {ι : Type*}
    (p : ι → ℂ) (hp : ∀ a, p a ≠ 0) (ν : ι →₀ ℕ) :
    nomeMonomial p ν ≠ 0 := by
  classical
  rw [nomeMonomial, Finsupp.prod_ne_zero_iff]
  intro a _
  exact pow_ne_zero _ (hp a)

theorem occupationWeight_nomePower {ι : Type*}
    (g : ℕ) (p : ι → ℂ) (ν : ι →₀ ℕ) :
    occupationWeight
        (fun a => ((‖p a‖₊ ^ (g + 1) : NNReal) : ℝ≥0∞)) ν =
      ((‖nomeMonomial p ν‖₊ ^ (g + 1) : NNReal) : ℝ≥0∞) := by
  classical
  rw [occupationWeight, Finsupp.prod]
  simp_rw [← ENNReal.coe_pow]
  rw [← ENNReal.coe_finsetProd]
  congr 1
  rw [nnnorm_nomeMonomial, Finsupp.prod]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro a _
  simp only [← pow_mul]
  congr 1
  exact Nat.mul_comm _ _

theorem summable_nomeMonomial_pow_iff {ι : Type*}
    (g : ℕ) (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) :
    Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ (g + 1)) ↔
      Summable (fun a => ‖p a‖ ^ (g + 1)) := by
  let u : ι → NNReal := fun a => ‖p a‖₊ ^ (g + 1)
  have hu_lt : ∀ a, u a < 1 := by
    intro a
    simp only [u]
    exact pow_lt_one₀ bot_le (by exact_mod_cast hp_lt a) (by omega)
  simpa only [NNReal.coe_pow, coe_nnnorm, u] using
    (show
      Summable (fun ν : ι →₀ ℕ => ((‖nomeMonomial p ν‖₊ ^ (g + 1) : NNReal) : ℝ)) ↔
        Summable (fun a => ((u a : NNReal) : ℝ)) by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
      rw [show
          (∑' ν : ι →₀ ℕ,
              ((‖nomeMonomial p ν‖₊ ^ (g + 1) : NNReal) : ℝ≥0∞)) =
            ∑' ν : ι →₀ ℕ,
              occupationWeight (fun a => (u a : ℝ≥0∞)) ν by
        apply tsum_congr
        intro ν
        rw [occupationWeight_nomePower]]
      exact occupationMass_ne_top_iff u hu_lt)

/-- The infinite-order genus-`g` multiple elliptic gamma product. -/
noncomputable def infiniteMultipleEllipticGamma {ι : Type*}
    (g : ℕ) (p : ι → ℂ) : ℂ → ℂ :=
  canonicalWeightProduct g (nomeMonomial p)

/-- Exact mass formula for the nome-generated occupation spectrum. -/
theorem nomeOccupationMass_eq_iSup_finset {ι : Type*}
    (g : ℕ) (p : ι → ℂ) :
    (∑' ν : ι →₀ ℕ,
        ((‖nomeMonomial p ν‖₊ ^ (g + 1) : NNReal) : ℝ≥0∞)) =
      ⨆ S : Finset ι,
        ∏ a ∈ S,
          (1 - ((‖p a‖₊ ^ (g + 1) : NNReal) : ℝ≥0∞))⁻¹ := by
  let u : ι → NNReal := fun a => ‖p a‖₊ ^ (g + 1)
  rw [show
      (∑' ν : ι →₀ ℕ,
          ((‖nomeMonomial p ν‖₊ ^ (g + 1) : NNReal) : ℝ≥0∞)) =
        ∑' ν : ι →₀ ℕ,
          occupationWeight (fun a => (u a : ℝ≥0∞)) ν by
    apply tsum_congr
    intro ν
    rw [occupationWeight_nomePower]]
  exact occupationMass_eq_iSup_finset (fun a => (u a : ℝ≥0∞))

/-- The infinite-order product converges locally uniformly on the whole complex plane. -/
theorem infiniteMultipleEllipticGamma_hasProdLocallyUniformlyOn {ι : Type*}
    (g : ℕ) (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0)
    (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    HasProdLocallyUniformlyOn
      (fun ν x => primaryFactor g (x * nomeMonomial p ν))
      (infiniteMultipleEllipticGamma g p) Set.univ := by
  apply canonicalWeightProduct_hasProdLocallyUniformlyOn
  · exact nomeMonomial_ne_zero p hp_ne
  · exact (summable_nomeMonomial_pow_iff g p hp_lt).2 hsum

/-- The infinite-order product is entire at every finite genus. -/
theorem infiniteMultipleEllipticGamma_analytic {ι : Type*}
    (g : ℕ) (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0)
    (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    AnalyticOnNhd ℂ (infiniteMultipleEllipticGamma g p) Set.univ :=
  canonicalWeightProduct_analytic g (nomeMonomial p)
    (nomeMonomial_ne_zero p hp_ne)
    ((summable_nomeMonomial_pow_iff g p hp_lt).2 hsum)

end HTGeometry
