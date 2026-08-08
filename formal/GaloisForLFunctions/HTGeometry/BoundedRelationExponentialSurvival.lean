import GaloisForLFunctions.HTGeometry.BoundedRelationConfinement
import GaloisForLFunctions.HTGeometry.MagnitudeBalancedAtomExistence
import GaloisForLFunctions.HTGeometry.MagnitudeAtomBounds
import GaloisForLFunctions.HTGeometry.FiniteAlgebraicCoefficientLindemannWeierstrass

/-!
# Bounded-relation exponential survival

An algebraic exponential coefficient germ with bounded integer-relation confinement defeats every
integer differential polynomial having positive jet degree.  A balanced full-degree atom supplies a
nonzero grouped weight.  Confinement makes its valuation fiber a singleton, while the finite
Lindemann--Weierstrass theorem prevents cancellation between the remaining distinct valuation
fibers.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

/-- Multiplicative algebraic phase of an atom. -/
def atomPhase (u : ℕ → ℂ) (ν : ℕ →₀ ℕ) : ℂ :=
  ν.prod fun i k => u i ^ k

/-- Exact phase/exponential factorization of a finite coefficient atom. -/
theorem atom_product_eq_phase_mul_exp
    {b : ℕ → ℝ} {u : ℕ → ℂ} {F : PowerSeries ℂ}
    (hF : ∀ i, PowerSeries.coeff i F =
      u i * Complex.exp (-(b i : ℂ)))
    (ν : ℕ →₀ ℕ) :
    ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) =
      atomPhase u ν * Complex.exp (-((boundedAtomValuation b ν : ℝ) : ℂ)) := by
  classical
  simp_rw [hF, mul_pow]
  rw [Finsupp.prod_mul]
  congr 1
  change (∏ i ∈ ν.support, Complex.exp (-(b i : ℂ)) ^ ν i) = _
  simp_rw [← Complex.exp_nsmul]
  rw [← Complex.exp_sum]
  congr 1
  rw [boundedAtomValuation, Finsupp.sum]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A finite phase atom is nonzero when every underlying phase is nonzero. -/
theorem atomPhase_ne_zero {u : ℕ → ℂ} (hu0 : ∀ i, u i ≠ 0)
    (ν : ℕ →₀ ℕ) : atomPhase u ν ≠ 0 := by
  rw [atomPhase, Finsupp.prod_ne_zero_iff]
  intro i hi
  exact pow_ne_zero _ (hu0 i)

/-- A finite phase atom is algebraic when every underlying phase is algebraic. -/
theorem atomPhase_isAlgebraic {u : ℕ → ℂ}
    (huAlg : ∀ i, IsAlgebraic ℚ (u i)) (ν : ℕ →₀ ℕ) :
    IsAlgebraic ℚ (atomPhase u ν) := by
  rw [← Subalgebra.mem_algebraicClosure]
  rw [atomPhase, Finsupp.prod]
  apply Subalgebra.prod_mem
  intro i hi
  rw [Subalgebra.mem_algebraicClosure]
  exact (huAlg i).pow (ν i)

/-- A finite bounded-atom valuation of algebraic reals remains algebraic after embedding in
`ℂ`. -/
theorem boundedAtomValuation_coe_isAlgebraic {b : ℕ → ℝ}
    (hbAlg : ∀ i, IsAlgebraic ℚ (b i)) (ν : ℕ →₀ ℕ) :
    IsAlgebraic ℚ ((boundedAtomValuation b ν : ℝ) : ℂ) := by
  have hreal : IsAlgebraic ℚ (boundedAtomValuation b ν) := by
    rw [← Subalgebra.mem_algebraicClosure]
    rw [boundedAtomValuation, Finsupp.sum]
    apply Subalgebra.sum_mem
    intro i hi
    exact Subalgebra.nsmul_mem _
      ((Subalgebra.mem_algebraicClosure ℚ ℝ).mpr (hbAlg i)) (ν i)
  simpa using hreal.algHom (IsScalarTower.toAlgHom ℚ ℝ ℂ)

private theorem intCast_complex_isAlgebraic (z : ℤ) :
    IsAlgebraic ℚ (z : ℂ) := by
  simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (z : ℚ))

/-- Regroup a finite atom sum by its additive valuations. -/
theorem sum_atom_products_regrouped_by_valuation
    {b : ℕ → ℝ} {u : ℕ → ℂ} {F : PowerSeries ℂ}
    (hF : ∀ i, PowerSeries.coeff i F =
      u i * Complex.exp (-(b i : ℂ)))
    (A : Finset (ℕ →₀ ℕ)) (w : (ℕ →₀ ℕ) → ℂ) :
    ∑ ν ∈ A,
        ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) * w ν =
      ∑ v ∈ A.image (boundedAtomValuation b),
        (∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v),
          atomPhase u ν * w ν) * Complex.exp (-((v : ℝ) : ℂ)) := by
  classical
  calc
    ∑ ν ∈ A,
        ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) * w ν =
        ∑ ν ∈ A,
          (atomPhase u ν * Complex.exp (-((boundedAtomValuation b ν : ℝ) : ℂ))) * w ν := by
            apply Finset.sum_congr rfl
            intro ν hν
            rw [atom_product_eq_phase_mul_exp hF]
    _ = ∑ v ∈ A.image (boundedAtomValuation b),
          ∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v),
            (atomPhase u ν * Complex.exp (-((boundedAtomValuation b ν : ℝ) : ℂ))) * w ν := by
          rw [Finset.sum_fiberwise_of_maps_to
            (fun ν hν => Finset.mem_image_of_mem _ hν)]
    _ = ∑ v ∈ A.image (boundedAtomValuation b),
          (∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v),
            atomPhase u ν * w ν) * Complex.exp (-((v : ℝ) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro ν hν
          have hval := (Finset.mem_filter.mp hν).2
          rw [hval]
          ring

/-- A bounded-relation exponential coefficient germ defeats every positive-jet-degree
integer differential polynomial at some coefficient level. -/
theorem exists_coeff_ne_zero_of_boundedRelation_exponential
    {b : ℕ → ℝ} {u : ℕ → ℂ} {F : PowerSeries ℂ}
    (hF : ∀ i, PowerSeries.coeff i F =
      u i * Complex.exp (-(b i : ℂ)))
    (hbAlg : ∀ i, IsAlgebraic ℚ (b i))
    (hconf : BoundedRelationConfinement b)
    (huAlg : ∀ i, IsAlgebraic ℚ (u i))
    (hu0 : ∀ i, u i ≠ 0)
    {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ N, PowerSeries.coeff N
      (MvPolynomial.aeval (formalJets n F) Q) ≠ 0 := by
  classical
  let D := magnitudeMaxJetDegree n Q
  have hD : 0 < D := by simpa [D] using hDpos
  have hsupport : Q.support.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hDz : D = 0 := by simp [D, magnitudeMaxJetDegree, hempty]
    omega
  obtain ⟨anchor, ha, haSup⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupport (fun m => jetMonomialDegree n m)
  have haD : jetMonomialDegree n anchor = D := by
    dsimp [D]
    rw [magnitudeMaxJetDegree, jetMonomialDegree]
    exact haSup.symm
  have haPos : 0 < jetMonomialDegree n anchor := by omega
  obtain ⟨δ, _hδ, Q₀, hbalanced⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight ha haPos
  obtain ⟨M, hM⟩ := hconf D
  let q := max Q₀ M
  have hqQ₀ : Q₀ ≤ q := le_max_left _ _
  have hqM : M ≤ q := le_max_right _ _
  let s : Fin (jetMonomialDegree n anchor) → ℕ := fun i => q + δ i
  let N := (∑ i, s i) + anchor 0 - jetMonomialOrder n anchor
  have hbalancedq := hbalanced q hqQ₀
  have hstarMem : key s ∈ (sigmaIdx n N Q).image (atomKeyOf n) := by
    simpa [s, N] using hbalancedq.1
  have hstarWeight : aevalWeight n N Q (key s) ≠ 0 := by
    simpa [s, N] using hbalancedq.2.1
  have hstarCount : (key s).sum (fun _ k => k) = D := by
    rw [key_total_count, haD]
  have hstarTail : ∀ i, key s i ≠ 0 → M ≤ i := by
    intro i hi
    have hex : ∃ j, s j = i := by
      by_contra hno
      push Not at hno
      apply hi
      simp [key, hno]
    obtain ⟨j, rfl⟩ := hex
    dsimp [s]
    omega
  let A := (sigmaIdx n N Q).image (atomKeyOf n)
  have hstarUnique : ∀ μ ∈ A,
      boundedAtomValuation b μ = boundedAtomValuation b (key s) → μ = key s := by
    intro μ hμ hval
    exact atom_eq_of_valuation_eq_of_full_tail hM hstarCount
      (appearing_atom_count_le Q hμ) hstarTail hval
  refine ⟨N, ?_⟩
  intro hcoeff
  have hsumzero :
      ∑ ν ∈ A,
          ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) *
            aevalWeight n N Q ν = 0 := by
    rw [← coeff_aeval_regrouped_weight n N F Q]
    exact hcoeff
  have hgroupzero :
      ∑ v ∈ A.image (boundedAtomValuation b),
          (∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v),
            atomPhase u ν * aevalWeight n N Q ν) *
              Complex.exp (-((v : ℝ) : ℂ)) = 0 := by
    rw [← sum_atom_products_regrouped_by_valuation hF A
      (aevalWeight n N Q)]
    exact hsumzero
  let V := A.image (boundedAtomValuation b)
  let I := {v : ℝ // v ∈ V}
  let E : I → ℂ := fun v => -((v.1 : ℝ) : ℂ)
  let C : I → ℂ := fun v =>
    ∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v.1),
      atomPhase u ν * aevalWeight n N Q ν
  have hEalg : ∀ v, IsAlgebraic ℚ (E v) := by
    intro v
    obtain ⟨ν, hν, hval⟩ := Finset.mem_image.mp v.2
    simpa [E, hval] using (boundedAtomValuation_coe_isAlgebraic hbAlg ν).neg
  have hEinj : Function.Injective E := by
    intro v w hvw
    apply Subtype.ext
    dsimp [E] at hvw
    exact Complex.ofReal_injective (neg_injective hvw)
  have hCAlg : ∀ v, IsAlgebraic ℚ (C v) := by
    intro v
    rw [← Subalgebra.mem_algebraicClosure]
    dsimp [C]
    apply Subalgebra.sum_mem
    intro ν hν
    rw [Subalgebra.mem_algebraicClosure]
    apply (atomPhase_isAlgebraic huAlg ν).mul
    obtain ⟨z, hz⟩ := aevalWeight_isInt n N Q ν hQint
    rw [hz]
    exact intCast_complex_isAlgebraic z
  have hrel : ∑ v : I, C v * Complex.exp (E v) = 0 := by
    change (∑ v ∈ V.attach, C v * Complex.exp (E v)) = 0
    simp only [C, E]
    rw [Finset.sum_attach V (fun v : ℝ =>
      (∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v),
        atomPhase u ν * aevalWeight n N Q ν) *
          Complex.exp (-((v : ℝ) : ℂ)))]
    simpa [V] using hgroupzero
  have hallzero := GaloisForLFunctions.RHTower.exp_algebraic_relation_eq_zero
    E C hEalg hEinj hCAlg hrel
  have hvstar : boundedAtomValuation b (key s) ∈ V := by
    apply Finset.mem_image.mpr
    exact ⟨key s, hstarMem, rfl⟩
  let vstar : I := ⟨boundedAtomValuation b (key s), hvstar⟩
  have hfiber :
      A.filter (fun μ => boundedAtomValuation b μ = boundedAtomValuation b (key s)) =
        {key s} := by
    ext μ
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hμ, hval⟩
      exact hstarUnique μ hμ hval
    · rintro rfl
      exact ⟨hstarMem, rfl⟩
  have hCstar : C vstar ≠ 0 := by
    dsimp [C, vstar]
    rw [hfiber, Finset.sum_singleton]
    exact mul_ne_zero (atomPhase_ne_zero hu0 (key s)) hstarWeight
  exact hCstar (hallzero vstar)

end

end GaloisForLFunctions
