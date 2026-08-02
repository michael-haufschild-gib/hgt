import GaloisForLFunctions.HTGeometry.CountableMultivariateAffineJetPattern
import GaloisForLFunctions.HTGeometry.QuasiAbelianAutomorphicForms
import Mathlib.Analysis.Complex.Cardinality

/-!
# Full-rank decorated packets on a discrete quotient

The coefficient-uniform Baire argument needs more than an abstract polynomial witness: all source
jets used by one determinant must sit at distinct points of the lattice quotient.  Starting from a
full-rank decorated-monomial packet, this file perturbs its sample rows along one complex parameter.
The determinant excludes finitely many parameters, while every forbidden lattice collision
excludes only a countable set because the lattice is discrete in a second-countable vector space.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Sample base points, together with arbitrary decorated-jet targets, can be chosen so that the
decorated evaluation matrix is invertible and every translated sample point is distinct modulo a
discrete lattice. -/
theorem exists_fullRank_multivariateTranslatedMonomial_packet_distinctModulo
    {d frameCount monomialCount : ℕ} (hd : 0 < d)
    (Gamma : AddSubgroup (Fin d → ℂ)) [DiscreteTopology Gamma]
    (shift : Fin frameCount → Fin d → ℂ)
    (hshift : PairwiseDistinctModulo Gamma shift)
    (orders : Fin frameCount → ℕ)
    (coordinateExponent : Fin monomialCount → Fin d →₀ ℕ)
    (jetExponent : Fin monomialCount →
      ((Σ i, MultiIndexBelow d (orders i)) →₀ ℕ))
    (hdecorated : Function.Injective (fun b ↦
      (coordinateExponent b, jetExponent b))) :
    ∃ (base : Fin monomialCount → Fin d → ℂ)
      (target : Fin monomialCount →
        (Σ i, MultiIndexBelow d (orders i)) → ℂ),
      IsUnit (Matrix.of fun a b ↦
        multivariateCoordinateMonomial (coordinateExponent b) (base a) *
          (jetExponent b).prod (fun i e ↦ target a i ^ e) :
        Matrix (Fin monomialCount) (Fin monomialCount) ℂ) ∧
      PairwiseDistinctModulo Gamma
        (fun q : Fin monomialCount × Fin frameCount ↦ base q.1 + shift q.2) := by
  classical
  let c0 : Fin d := ⟨0, hd⟩
  let e0 : Fin d → ℂ := Pi.single c0 1
  obtain ⟨base0, target0, hfull0⟩ :=
    exists_fullRank_multivariateExpandedMonomial_packet
      coordinateExponent jetExponent hdecorated
  let lineBase (t : ℂ) (a : Fin monomialCount) : Fin d → ℂ :=
    base0 a + t • (((a : ℕ) : ℂ) • e0)
  let coordinatePolynomial (a : Fin monomialCount) (i : Fin d) : Polynomial ℂ :=
    Polynomial.C (base0 a i) +
      Polynomial.C (((a : ℕ) : ℂ) * e0 i) * Polynomial.X
  let determinantPolynomial : Polynomial ℂ :=
    (Matrix.of fun a b ↦
      (coordinateExponent b).prod
          (fun i e ↦ coordinatePolynomial a i ^ e) *
        Polynomial.C ((jetExponent b).prod (fun i e ↦ target0 a i ^ e)) :
      Matrix (Fin monomialCount) (Fin monomialCount) (Polynomial ℂ)).det
  have hdeterminant_eval (t : ℂ) :
      determinantPolynomial.eval t =
        (Matrix.of fun a b ↦
          multivariateCoordinateMonomial (coordinateExponent b) (lineBase t a) *
            (jetExponent b).prod (fun i e ↦ target0 a i ^ e) :
          Matrix (Fin monomialCount) (Fin monomialCount) ℂ).det := by
    change Polynomial.evalRingHom t determinantPolynomial = _
    simp only [determinantPolynomial]
    rw [RingHom.map_det]
    congr 1
    ext a b
    change Polynomial.evalRingHom t
        ((coordinateExponent b).prod
            (fun i e ↦ coordinatePolynomial a i ^ e) *
          Polynomial.C ((jetExponent b).prod (fun i e ↦ target0 a i ^ e))) = _
    simp only [multivariateCoordinateMonomial, map_mul]
    congr 1
    · rw [map_finsuppProd]
      apply Finsupp.prod_congr
      intro i hi
      rw [map_pow]
      congr 1
      simp only [coordinatePolynomial, map_add, map_mul]
      simp [lineBase, Pi.smul_apply, mul_comm]
    · simp
  have hdet0 :
      (Matrix.of fun a b ↦
        multivariateCoordinateMonomial (coordinateExponent b) (base0 a) *
          (jetExponent b).prod (fun i e ↦ target0 a i ^ e) :
        Matrix (Fin monomialCount) (Fin monomialCount) ℂ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hfull0).ne_zero
  have hdeterminant_ne : determinantPolynomial ≠ 0 := by
    intro hzero
    have hzeroEval : determinantPolynomial.eval 0 = 0 := by simp [hzero]
    rw [hdeterminant_eval] at hzeroEval
    apply hdet0
    simpa [lineBase] using hzeroEval
  have hGamma : (Gamma : Set (Fin d → ℂ)).Countable :=
    (HereditarilyLindelofSpace.isLindelof (Gamma : Set (Fin d → ℂ))).countable
      (inferInstance : DiscreteTopology Gamma)
  let node (t : ℂ) (q : Fin monomialCount × Fin frameCount) : Fin d → ℂ :=
    lineBase t q.1 + shift q.2
  let badPair (a b : Fin monomialCount) (i j : Fin frameCount) : Set ℂ :=
    if a = b then ∅ else
      {t | node t (a, i) - node t (b, j) ∈ Gamma}
  have hbadPair : ∀ a b i j, (badPair a b i j).Countable := by
    intro a b i j
    by_cases hab : a = b
    · simp [badPair, hab]
    · simp only [badPair, if_neg hab]
      let g : ℂ → Fin d → ℂ := fun t ↦ node t (a, i) - node t (b, j)
      have habNat : (a : ℕ) ≠ (b : ℕ) := fun h ↦ hab (Fin.ext h)
      have habComplex : (((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)) ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast habNat
      have hg : Function.Injective g := by
        intro t u htu
        have hc := congrFun htu c0
        have he0 : e0 c0 = 1 := by simp [e0, c0]
        have hmul :
            ((((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)) * t) =
              ((((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)) * u) := by
          dsimp only [g, node, lineBase] at hc
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, he0] at hc
          linear_combination hc
        exact mul_left_cancel₀ habComplex hmul
      change (g ⁻¹' (Gamma : Set (Fin d → ℂ))).Countable
      exact hGamma.preimage hg
  let bad : Set ℂ := ⋃ a, ⋃ b, ⋃ i, ⋃ j, badPair a b i j
  have hbad : bad.Countable := by
    apply Set.countable_iUnion
    intro a
    apply Set.countable_iUnion
    intro b
    apply Set.countable_iUnion
    intro i
    apply Set.countable_iUnion
    intro j
    exact hbadPair a b i j
  let roots : Set ℂ := {t | determinantPolynomial.eval t = 0}
  have hroots : roots.Countable := by
    apply (determinantPolynomial.roots.toFinset.finite_toSet.countable).mono
    intro t ht
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hdeterminant_ne).mpr ht)
  have hexists : ∃ t : ℂ, t ∉ bad ∪ roots := by
    by_contra h
    push Not at h
    have huniv : bad ∪ roots = Set.univ := Set.eq_univ_of_forall h
    apply not_countable_complex
    simpa only [huniv] using hbad.union hroots
  obtain ⟨t, ht⟩ := hexists
  have htbad : t ∉ bad := fun hbadMem ↦ ht (Or.inl hbadMem)
  have htroots : t ∉ roots := fun hrootMem ↦ ht (Or.inr hrootMem)
  refine ⟨lineBase t, target0, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (by
      rw [← hdeterminant_eval]
      exact htroots)
  · intro q r hqr hmem
    rcases q with ⟨a, i⟩
    rcases r with ⟨b, j⟩
    by_cases hab : a = b
    · subst b
      have hij : i ≠ j := by
        intro hij
        exact hqr (Prod.ext rfl hij)
      apply hshift hij
      simpa [node, lineBase] using hmem
    · apply htbad
      simp only [bad, Set.mem_iUnion]
      refine ⟨a, b, i, j, ?_⟩
      simpa [badPair, hab, node] using hmem

end

end GaloisForLFunctions.HTGeometry
