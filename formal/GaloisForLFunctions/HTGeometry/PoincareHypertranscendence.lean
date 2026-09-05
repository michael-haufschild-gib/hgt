import GaloisForLFunctions.HTGeometry.CompositionDecompositionLaw
import GaloisForLFunctions.HTGeometry.ExponentialPoincareRecession

/-!
# Bergweiler's hypertranscendence for a Poincaré function

Precomposition by a dilation `z ↦ c z` is an automorphism of the meromorphic field of the plane
fixing the constants, and the jets of a dilated function are constant multiples of the images of the
original jets.  So a dilate has an algebraic-witness family of the *same size* as the original.

Feeding that into the composition-decomposition law gives a bound on the differential order of every
`g` with `g ∘ φ = φ(c ·)` that depends only on `φ` — uniform in `c`.  A `φ` conjugating maps of
unbounded differential order into dilations therefore satisfies no algebraic differential equation.

For the exponential the iterates have differential order exactly `n`
(`ExponentialTowerUnitCost.exactDifferentialOrder_expTower`), so every nonconstant entire solution of
`exp ∘ φ = φ(λ ·)` with nonvanishing realized derivative is hypertranscendental.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Bottcher Set
open scoped UnivMeroFieldInstances Differential

theorem analyticOnNhd_dilation (c : ℂ) :
    AnalyticOnNhd ℂ (fun z => c * z) (Set.univ : Set ℂ) :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_id.const_mul c)

theorem mapsTo_dilation (c : ℂ) :
    Set.MapsTo (fun z => c * z) (Set.univ : Set ℂ) (Set.univ : Set ℂ) :=
  fun _ _ => Set.mem_univ _

/-- Precomposition by the dilation `z ↦ c z` as an automorphism of the meromorphic field. -/
def dilationMeroEquiv {c : ℂ} (hc : c ≠ 0) :
    meroField (Set.univ : Set ℂ) ≃+* meroField (Set.univ : Set ℂ) :=
  precompMeroEquiv (analyticOnNhd_dilation c) (analyticOnNhd_dilation c⁻¹)
    (mapsTo_dilation c) (mapsTo_dilation c⁻¹)
    (by intro z _; show c * (c⁻¹ * z) = z; field_simp)
    (by intro z _; show c⁻¹ * (c * z) = z; field_simp)
    isOpen_univ isPreconnected_univ Set.univ_nonempty

theorem dilationMeroEquiv_analyticMeroElement {c : ℂ} (hc : c ≠ 0) (u : ℂ → ℂ)
    (hu : AnalyticOnNhd ℂ u (Set.univ : Set ℂ)) (hcomp : AnalyticOnNhd ℂ (fun z => u (c * z))
      (Set.univ : Set ℂ)) :
    dilationMeroEquiv hc (analyticMeroElement u hu)
      = analyticMeroElement (fun z => u (c * z)) hcomp := by
  rw [analyticMeroElement, dilationMeroEquiv, precompMeroEquiv_algebraMap]
  congr 1

theorem analyticOnNhd_const_univ (a : ℂ) :
    AnalyticOnNhd ℂ (fun _ : ℂ => a) (Set.univ : Set ℂ) :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_const a)

theorem algebraMap_complex_meroField_eq (a : ℂ) :
    (algebraMap ℂ (meroField (Set.univ : Set ℂ))) a
      = analyticMeroElement (fun _ : ℂ => a) (analyticOnNhd_const_univ a) :=
  (analyticMeroElement_const (Set.univ : Set ℂ) a).symm

theorem dilationMeroEquiv_algebraMap {c : ℂ} (hc : c ≠ 0) (a : ℂ) :
    dilationMeroEquiv hc ((algebraMap ℂ (meroField (Set.univ : Set ℂ))) a)
      = (algebraMap ℂ (meroField (Set.univ : Set ℂ))) a := by
  rw [algebraMap_complex_meroField_eq a,
    dilationMeroEquiv_analyticMeroElement hc _ (analyticOnNhd_const_univ a)
      (analyticOnNhd_const_univ a)]

/-- The dilation automorphism as a `ℂ`-algebra map. -/
def dilationMeroAlgHom {c : ℂ} (hc : c ≠ 0) :
    meroField (Set.univ : Set ℂ) →ₐ[ℂ] meroField (Set.univ : Set ℂ) :=
  { (dilationMeroEquiv hc : meroField (Set.univ : Set ℂ) →+* meroField (Set.univ : Set ℂ)) with
    commutes' := dilationMeroEquiv_algebraMap hc }

@[simp] theorem dilationMeroAlgHom_apply {c : ℂ} (hc : c ≠ 0)
    (x : meroField (Set.univ : Set ℂ)) : dilationMeroAlgHom hc x = dilationMeroEquiv hc x := rfl

theorem dilationMeroAlgHom_injective {c : ℂ} (hc : c ≠ 0) :
    Function.Injective (dilationMeroAlgHom hc) := (dilationMeroEquiv hc).injective

/-- A nonzero constant multiple of a witnessed element is witnessed over the same family. -/
theorem AlgebraicWitness.const_mul {L K : Type*} [Field L] [Field K] [Algebra K L]
    {σ : Type*} {b : σ → L} {y : L} {a : K} (ha : a ≠ 0) (h : AlgebraicWitness K b y) :
    AlgebraicWitness K b (algebraMap K L a * y) := by
  obtain ⟨m, P, hlead, hrel⟩ := h
  refine ⟨m, fun i => MvPolynomial.C (a⁻¹ ^ i) * P i, ?_, ?_⟩
  · rw [map_mul, MvPolynomial.aeval_C]
    refine mul_ne_zero ?_ hlead
    have hne : (a⁻¹ ^ m) ≠ 0 := pow_ne_zero m (inv_ne_zero ha)
    exact (map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective).mpr hne
  · refine Eq.trans ?_ hrel
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.aeval_C, mul_pow]
    have hinv : (algebraMap K L (a⁻¹ ^ i)) * (algebraMap K L a) ^ i = 1 := by
      rw [← map_pow, ← map_mul, ← mul_pow, inv_mul_cancel₀ ha, one_pow, map_one]
    calc (algebraMap K L) (a⁻¹ ^ i) * MvPolynomial.aeval b (P i)
          * ((algebraMap K L) a ^ i * y ^ i)
        = ((algebraMap K L) (a⁻¹ ^ i) * (algebraMap K L) a ^ i)
          * (MvPolynomial.aeval b (P i) * y ^ i) := by ring
      _ = MvPolynomial.aeval b (P i) * y ^ i := by rw [hinv, one_mul]


theorem contDiff_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) : ContDiff ℂ n f := by
  have hana : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  exact (hana z (Set.mem_univ z)).contDiffAt.of_le le_top

/-- **A dilated function has a witness family of the same size.**  Precomposition by `z ↦ c z` is an
automorphism of the meromorphic field fixing the constants, and the jets of the dilate are constant
multiples of the images of the jets. -/
theorem exists_dilate_jet_algebraicWitness {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    {c : ℂ} (hc : c ≠ 0) {p : ℕ} {b : Fin p → meroField (Set.univ : Set ℂ)}
    (hb : ∀ j : ℕ, AlgebraicWitness ℂ b (analyticMeroElement (iteratedDeriv j φ)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (differentiable_iteratedDeriv_of_entire hφ j))))
    (j : ℕ) :
    AlgebraicWitness ℂ (fun i => dilationMeroEquiv hc (b i))
      (analyticMeroElement (iteratedDeriv j (fun z => φ (c * z)))
        (Complex.analyticOnNhd_univ_iff_differentiable.mpr
          (differentiable_iteratedDeriv_of_entire (hφ.comp (differentiable_id.const_mul c)) j))) := by
  have hjetfun : iteratedDeriv j (fun z => φ (c * z))
      = fun z => c ^ j * iteratedDeriv j φ (c * z) :=
    iteratedDeriv_comp_const_mul (contDiff_of_entire hφ j) c
  have hshift : AnalyticOnNhd ℂ (fun z => iteratedDeriv j φ (c * z)) (Set.univ : Set ℂ) :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((differentiable_iteratedDeriv_of_entire hφ j).comp (differentiable_id.const_mul c))
  have hconstfun : AnalyticOnNhd ℂ (fun _ : ℂ => c ^ j) (Set.univ : Set ℂ) :=
    analyticOnNhd_const_univ _
  have hprod : analyticMeroElement (iteratedDeriv j (fun z => φ (c * z)))
        (Complex.analyticOnNhd_univ_iff_differentiable.mpr
          (differentiable_iteratedDeriv_of_entire (hφ.comp (differentiable_id.const_mul c)) j))
      = (algebraMap ℂ (meroField (Set.univ : Set ℂ))) (c ^ j)
        * analyticMeroElement (fun z => iteratedDeriv j φ (c * z)) hshift := by
    rw [algebraMap_complex_meroField_eq, ← analyticMeroElement_mul hconstfun hshift]
    exact analyticMeroElement_congr _ _ hjetfun
  rw [hprod, ← dilationMeroEquiv_analyticMeroElement hc _
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_iteratedDeriv_of_entire hφ j)) hshift]
  refine AlgebraicWitness.const_mul (pow_ne_zero j hc) ?_
  exact AlgebraicWitness.map (dilationMeroAlgHom hc) (dilationMeroAlgHom_injective hc) (hb j)


set_option synthInstance.maxHeartbeats 800000 in
/-- The witness family of a differentially algebraic entire function, in the global instance
stack. -/
theorem exists_univ_witness_family {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ))
    (hfDA : DifferentiallyAlgebraicOn f (Set.univ : Set ℂ)) :
    ∃ (p : ℕ) (b : Fin p → meroField (Set.univ : Set ℂ)), ∀ j : ℕ,
      AlgebraicWitness ℂ b (analyticMeroElement (iteratedDeriv j f)
        (analyticOnNhd_iteratedDeriv hf j)) := by
  obtain ⟨p, b, hb⟩ := exists_jet_algebraicWitness_family isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ hf hfDA
  refine ⟨p, b, fun j => ?_⟩
  convert hb j using 2
  all_goals first
    | rfl
    | exact Algebra.algebra_ext _ _ fun r => (ratfuncToMero_C_eq_constToMero r).symm


set_option synthInstance.maxHeartbeats 800000 in
/-- **Uniform order bound along a Schröder conjugacy.**  If `φ` is a differentially algebraic
nonconstant entire function with nonvanishing realized derivative, then every entire `g` with
`g ∘ φ = φ(c ·)` for some nonzero `c` satisfies an algebraic differential equation of one and the
same order — a bound depending only on `φ`. -/
theorem exists_uniform_order_of_conjugacy {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    (hnc : ∀ a : ℂ, ∃ z, φ z ≠ a)
    (hφ' : analyticMeroElement (deriv φ)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hφ).deriv ≠ 0)
    (hφDA : DifferentiallyAlgebraicOn φ (Set.univ : Set ℂ)) :
    ∃ M : ℕ, ∀ (c : ℂ), c ≠ 0 → ∀ g : ℂ → ℂ, Differentiable ℂ g →
      (∀ z, g (φ z) = φ (c * z)) → DifferentiallyAlgebraicOfOrder g M := by
  classical
  have hφa : AnalyticOnNhd ℂ φ (Set.univ : Set ℂ) :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hφ
  obtain ⟨p, b, hb⟩ := exists_univ_witness_family hφa hφDA
  refine ⟨p + p, fun c hc g hg hconj => ?_⟩
  have hca : AnalyticOnNhd ℂ (fun z => g (φ z)) (Set.univ : Set ℂ) :=
    analyticOnNhd_iteratedDeriv_comp hg hφ 0
  have hfun : (fun z => g (φ z)) = fun z => φ (c * z) := funext hconj
  refine differentiallyAlgebraicOfOrder_of_comp_witness hg hφ hnc hφ'
    (I := Fin p ⊕ Fin p) (M := p + p)
    (Sum.elim b fun i => dilationMeroEquiv hc (b i)) (by simp) ?_
  intro x hx j
  rcases hx with hx | hx
  · subst hx
    have hjet : differentialJet j (analyticMeroElement φ hφa)
        = analyticMeroElement (iteratedDeriv j φ) (analyticOnNhd_iteratedDeriv hφa j) :=
      differentialJet_analyticMeroElement isOpen_univ isPreconnected_univ Set.univ_nonempty
        φ hφa j
    rw [hjet]
    exact AlgebraicWitness.extend Sum.inl _ (by funext i; rfl) (hb j)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have hjet : differentialJet j
          (analyticMeroElement (fun z => iteratedDeriv 0 g (φ z)) hca)
        = analyticMeroElement (iteratedDeriv j fun z => g (φ z))
            (analyticOnNhd_iteratedDeriv hca j) :=
      differentialJet_analyticMeroElement isOpen_univ isPreconnected_univ Set.univ_nonempty
        (fun z => g (φ z)) hca j
    rw [hjet]
    have hdil := exists_dilate_jet_algebraicWitness hφ hc hb j
    have hcongr : analyticMeroElement (iteratedDeriv j fun z => g (φ z))
          (analyticOnNhd_iteratedDeriv hca j)
        = analyticMeroElement (iteratedDeriv j (fun z => φ (c * z)))
            (Complex.analyticOnNhd_univ_iff_differentiable.mpr
              (differentiable_iteratedDeriv_of_entire
                (hφ.comp (differentiable_id.const_mul c)) j)) :=
      analyticMeroElement_congr _ _ (by rw [hfun])
    rw [hcongr]
    exact AlgebraicWitness.extend Sum.inr _ (by funext i; rfl) hdil


/-- **Hypertranscendence from unbounded conjugates.**  A nonconstant entire `φ` with nonvanishing
realized derivative that conjugates entire maps of unbounded differential order into dilations
satisfies no algebraic differential equation. -/
theorem not_differentiallyAlgebraicOn_of_unbounded_conjugates {φ : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hnc : ∀ a : ℂ, ∃ z, φ z ≠ a)
    (hφ' : analyticMeroElement (deriv φ)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hφ).deriv ≠ 0)
    (hfam : ∀ M : ℕ, ∃ (c : ℂ) (g : ℂ → ℂ), c ≠ 0 ∧ Differentiable ℂ g ∧
      (∀ z, g (φ z) = φ (c * z)) ∧ ¬ DifferentiallyAlgebraicOfOrder g M) :
    ¬ DifferentiallyAlgebraicOn φ (Set.univ : Set ℂ) := by
  intro hDA
  obtain ⟨M, hM⟩ := exists_uniform_order_of_conjugacy hφ hnc hφ' hDA
  obtain ⟨c, g, hc, hg, hconj, hnot⟩ := hfam M
  exact hnot (hM c hc g hg hconj)

theorem differentiable_exp_iterate (k : ℕ) : Differentiable ℂ (Complex.exp^[k]) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ']
      exact Complex.differentiable_exp.comp ih

theorem exp_iterate_conj {φ : ℂ → ℂ} {lam : ℂ}
    (hconj : ∀ z, Complex.exp (φ z) = φ (lam * z)) (k : ℕ) (z : ℂ) :
    Complex.exp^[k] (φ z) = φ (lam ^ k * z) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, hconj z, ih (lam * z)]
      congr 1
      ring

/-- **Bergweiler's theorem for the exponential Poincaré function.**  A nonconstant entire solution
of `exp ∘ φ = φ(λ ·)` with nonvanishing realized derivative is hypertranscendental: the iterates of
the exponential have unbounded differential order, so no uniform bound can hold. -/
theorem not_differentiallyAlgebraicOn_poincare_exp {φ : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hnc : ∀ a : ℂ, ∃ z, φ z ≠ a)
    (hφ' : analyticMeroElement (deriv φ)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hφ).deriv ≠ 0)
    {lam : ℂ} (hlam : lam ≠ 0)
    (hconj : ∀ z, Complex.exp (φ z) = φ (lam * z)) :
    ¬ DifferentiallyAlgebraicOn φ (Set.univ : Set ℂ) := by
  refine not_differentiallyAlgebraicOn_of_unbounded_conjugates hφ hnc hφ' fun M => ?_
  refine ⟨lam ^ (M + 1), Complex.exp^[M + 1], pow_ne_zero _ hlam,
    differentiable_exp_iterate (M + 1), fun z => exp_iterate_conj hconj (M + 1) z, ?_⟩
  exact (exactDifferentialOrder_exp_iterate M).2 M (Nat.lt_succ_self M)


end GaloisForLFunctions.HTGeometry
