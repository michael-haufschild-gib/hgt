import GaloisForLFunctions.HTGeometry.TwoDeformedFibrePoints
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# The universal deformation of a critical observation

The critical observation of a horizon has `n` raw coordinates and `m` reciprocal ones.  Deform them
by the `m + n` variables of a multivariate power series ring: the raw critical coefficients become
`1 + s_0, s_1, …, s_(n-1)` and the reciprocal ones `1 + s_n, …, s_(L-1)`.  That is an affine change
of the variables, so the deformed observation is as generic as an observation can be.

The power series ring is adically complete for the ideal of its variables, so the lift applies: two
distinct factorisations of `1 + t^L` over the coefficient field deform, along this one deformation,
into two distinct factorisations sharing the deformed observation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable (K : Type*) [Field K] (m n : ℕ)

/-- The base of the universal deformation: power series in one variable per critical coordinate. -/
abbrev deformBase : Type _ := MvPowerSeries (Fin n ⊕ Fin m ⊕ Unit) K

/-- The ideal of the deformation parameters. -/
noncomputable abbrev deformIdeal : Ideal (deformBase K m n) :=
  Ideal.span (Set.range (MvPowerSeries.X : Fin n ⊕ Fin m ⊕ Unit → deformBase K m n))

/-- The deformation of the raw critical coefficients. -/
noncomputable def rawDeformation : (deformBase K m n)[X] :=
  ∑ i : Fin n, Polynomial.C (MvPowerSeries.X (Sum.inl i) : deformBase K m n) * X ^ (m + (i : ℕ))

/-- The deformation of the reciprocal critical coefficients. -/
noncomputable def reciprocalDeformation : (deformBase K m n)[X] :=
  ∑ j : Fin m, Polynomial.C (MvPowerSeries.X (Sum.inr (Sum.inl j)) : deformBase K m n) * X ^ (n + (j : ℕ))

theorem coeffMem_rawDeformation : CoeffMem (deformIdeal K m n) (rawDeformation K m n) := by
  intro k
  rw [rawDeformation, Polynomial.finsetSum_coeff]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with h
  · rw [mul_one]
    exact Ideal.subset_span ⟨Sum.inl i, rfl⟩
  · rw [mul_zero]
    exact Submodule.zero_mem _

theorem coeffMem_reciprocalDeformation :
    CoeffMem (deformIdeal K m n) (reciprocalDeformation K m n) := by
  intro k
  rw [reciprocalDeformation, Polynomial.finsetSum_coeff]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with h
  · rw [mul_one]
    exact Ideal.subset_span ⟨Sum.inr (Sum.inl j), rfl⟩
  · rw [mul_zero]
    exact Submodule.zero_mem _

theorem natDegree_rawDeformation_lt (hn : 0 < n) :
    (rawDeformation K m n).natDegree < m + n := by
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_))
    (by omega : m + n - 1 < m + n)
  exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (by have := i.2; omega)

theorem natDegree_reciprocalDeformation_lt (hm : 0 < m) :
    (reciprocalDeformation K m n).natDegree < m + n := by
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_))
    (by omega : m + n - 1 < m + n)
  exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (by have := j.2; omega)

/-- The deformation of the new raw coefficient beyond the horizon. -/
noncomputable def deformParam : deformBase K m n :=
  MvPowerSeries.X (Sum.inr (Sum.inr ()))

theorem deformParam_mem : deformParam K m n ∈ deformIdeal K m n :=
  Ideal.subset_span ⟨Sum.inr (Sum.inr ()), rfl⟩

/-- **A nonzero constant is not a deformation parameter.** -/
theorem notMem_deformIdeal_of_ne_zero {c : K} (hc : c ≠ 0) :
    (algebraMap K (deformBase K m n)) c ∉ deformIdeal K m n := by
  intro hcon
  have hker : deformIdeal K m n
      ≤ RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  have hmem := hker hcon
  rw [RingHom.mem_ker] at hmem
  have hconst : MvPowerSeries.constantCoeff (algebraMap K (deformBase K m n) c) = c := by
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C]
    simp
  rw [hconst] at hmem
  exact hc hmem

/-- **Two points of the fibre over the universal deformed observation.**  Two distinct
factorisations of `1 + t^L` over the coefficient field deform, along the universal deformation of
the critical observation, into two factorisations over the horizon that share every coefficient from
the critical orders on and whose constant terms still differ. -/
theorem exists_two_deformed_pure_factorisations {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A₀ B₀ A₁ B₁ : K[X]}
    (hA₀ : A₀.Monic) (hA₀deg : A₀.natDegree = m) (hB₀ : B₀.Monic) (hB₀deg : B₀.natDegree = n)
    (hA₁ : A₁.Monic) (hA₁deg : A₁.natDegree = m) (hB₁ : B₁.Monic) (hB₁deg : B₁.natDegree = n)
    (hcop₀ : IsCoprime A₀ B₀) (hcop₁ : IsCoprime A₁ B₁)
    (hfac₀ : A₀ * B₀ = 1 + X ^ (m + n)) (hfac₁ : A₁ * B₁ = 1 + X ^ (m + n))
    (hsep : A₀.coeff 0 ≠ A₁.coeff 0) :
    ∃ Z₀ W₀ Z₁ W₁ : (deformBase K m n)[X],
      (X : (deformBase K m n)[X]) ^ (m + n) ∣ inversionError Z₀ W₀ ∧
      (X : (deformBase K m n)[X]) ^ (m + n) ∣ inversionError Z₁ W₁ ∧
      (∀ i, m ≤ i → Z₀.coeff i = Z₁.coeff i) ∧
      (∀ j, n ≤ j → W₀.coeff j = W₁.coeff j) ∧
      Z₀.coeff 0 - Z₁.coeff 0 ∉ deformIdeal K m n ∧
      CoeffMem (deformIdeal K m n) (Z₀ - A₀.map (algebraMap K (deformBase K m n))) ∧
      CoeffMem (deformIdeal K m n) (W₀ - B₀.map (algebraMap K (deformBase K m n))) ∧
      CoeffMem (deformIdeal K m n) (Z₁ - A₁.map (algebraMap K (deformBase K m n))) ∧
      CoeffMem (deformIdeal K m n) (W₁ - B₁.map (algebraMap K (deformBase K m n))) ∧
      W₀.natDegree < m + n ∧ W₁.natDegree < m + n ∧
      Z₀.natDegree < m + n ∧ Z₁.natDegree < m + n ∧
      (∀ i, m ≤ i → Z₀.coeff i
        = (A₀.map (algebraMap K (deformBase K m n))).coeff i + (rawDeformation K m n).coeff i) ∧
      (∀ j, n ≤ j → W₀.coeff j
        = (B₀.map (algebraMap K (deformBase K m n))).coeff j
          + (reciprocalDeformation K m n).coeff j) := by
  haveI : IsAdicComplete (deformIdeal K m n) (deformBase K m n) := inferInstanceAs
    (IsAdicComplete (Ideal.span (Set.range (MvPowerSeries.X :
      Fin n ⊕ Fin m ⊕ Unit → MvPowerSeries (Fin n ⊕ Fin m ⊕ Unit) K)))
      (MvPowerSeries (Fin n ⊕ Fin m ⊕ Unit) K))
  set φ : K →+* deformBase K m n := algebraMap K (deformBase K m n) with hφ
  have hmapfac : ∀ {A B : K[X]}, A * B = 1 + X ^ (m + n) →
      (X : (deformBase K m n)[X]) ^ (m + n)
        ∣ inversionError (A.map φ) (B.map φ) := by
    intro A B h
    have : inversionError (A.map φ) (B.map φ) = (X : (deformBase K m n)[X]) ^ (m + n) := by
      rw [inversionError, ← Polynomial.map_mul, h, Polynomial.map_add, Polynomial.map_one,
        Polynomial.map_pow, Polynomial.map_X, add_sub_cancel_left]
    rw [this]
  refine exists_two_deformed_factorisations (deformIdeal K m n) hm hn
    (hA₀.map φ) (by rw [hA₀.natDegree_map φ, hA₀deg]) (hB₀.map φ)
    (by rw [hB₀.natDegree_map φ, hB₀deg]) (hA₁.map φ) (by rw [hA₁.natDegree_map φ, hA₁deg])
    (hB₁.map φ) (by rw [hB₁.natDegree_map φ, hB₁deg])
    (hcop₀.map (Polynomial.mapRingHom φ)) (hcop₁.map (Polynomial.mapRingHom φ))
    (hmapfac hfac₀) (hmapfac hfac₁) ?_
    (coeffMem_rawDeformation K m n) (coeffMem_reciprocalDeformation K m n)
    (natDegree_rawDeformation_lt K m n hn) (natDegree_reciprocalDeformation_lt K m n hm)
  rw [Polynomial.coeff_map, Polynomial.coeff_map, ← map_sub]
  exact notMem_deformIdeal_of_ne_zero K m n (sub_ne_zero.2 hsep)

end GaloisForLFunctions.HTGeometry
