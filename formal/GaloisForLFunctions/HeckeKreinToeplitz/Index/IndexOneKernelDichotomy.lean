import GaloisForLFunctions.HeckeKreinToeplitz.Index.CompletedColumnRepresentation
import GaloisForLFunctions.HeckeKreinToeplitz.Index.CommutingIndexOneIsometries
import GaloisForLFunctions.HeckeKreinToeplitz.Index.CommutingReflectedEigenline
import GaloisForLFunctions.HeckeKreinToeplitz.Index.HyperbolicEigenlineSplitting

/-!
# The unitary-or-hyperbolic dichotomy at index one

An abelian index-one kernel either has a positive unitary-character mass
hyperplane, or is a positive-definite kernel plus one nonzero nonunitary
hyperbolic pair. The common eigenline theorem produces the first character;
the reflected companion splits the nonunitary case. Cyclic density ensures
that neither hyperbolic coefficient vanishes.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Module
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [CommGroup G] {k : G → ℂ}

/-- Every index-one abelian kernel has either a unitary positive hyperplane or a single
nonzero hyperbolic pair with positive-definite remainder. -/
theorem index_one_unitary_or_hyperbolic (hk : IsHermKernel k) (hi : negIndex k ≤ 1) :
    (∃ χ : G →* ℂ, IsUnitaryChar χ ∧ ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      charEval χ x c = 0 → 0 ≤ hermQuad (gram k x) c) ∨
    ∃ (p : G → ℂ) (χ : G →* ℂ) (ω : ℂ),
      IsPosDefKernel p ∧ ¬ IsUnitaryChar χ ∧ ω ≠ 0 ∧
        k = fun g => p g + pairKernel χ ω g := by
  classical
  by_cases hp : IsPosDefKernel k
  · exact Or.inl ⟨1, (by intro g; simp), fun n x c _ => hp.2 n x c⟩
  obtain ⟨e, he⟩ := exists_negative_unit_column hk hp
  let H := NegativeColumn.Hilbert hk hi e he
  let T : G → (H × ℂ) ≃L[ℂ] (H × ℂ) := NegativeColumn.action hk hi e he
  let E : kernelColumnSpan k →ₗ[ℂ] (H × ℂ) := NegativeColumn.embedding hk hi e he
  have hT : ∀ g u v, IndexOne.pairing (T g u) (T g v) = IndexOne.pairing u v :=
    NegativeColumn.action_pairing hk hi e he
  have hmul (g h : G) (u : H × ℂ) : T (g * h) u = T g (T h u) :=
    NegativeColumn.action_mul hk hi e he g h u
  have hone (u : H × ℂ) : T 1 u = u := NegativeColumn.action_one hk hi e he u
  have hcomm (g h : G) (u : H × ℂ) : T g (T h u) = T h (T g u) := by
    rw [← hmul, ← hmul, mul_comm g h]
  let ρ : G →* End ℂ (H × ℂ) :=
    { toFun := fun g => (T g).toContinuousLinearMap.toLinearMap
      map_one' := by
        apply LinearMap.ext
        intro u
        exact hone u
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro u
        exact hmul g h u }
  have hρ : ∀ g u v, IndexOne.pairing (ρ g u) (ρ g v) = IndexOne.pairing u v := hT
  obtain ⟨z, hz, hzT⟩ :=
    IndexOne.exists_common_normalized_nonpositive_eigenvector T hT hcomm
  let w : H × ℂ := (z, 1)
  have heigen (g : G) : T g w = (T g w).2 • w := by
    obtain ⟨a, _, ha⟩ := hzT g
    have hs : (T g w).2 = a := by
      simpa only [Prod.smul_snd, smul_eq_mul, mul_one] using congrArg Prod.snd ha
    rw [hs]
    exact ha
  let α : G →* ℂ :=
    { toFun := fun g => (T g w).2
      map_one' := by rw [hone]
      map_mul' := by
        intro g h
        conv_lhs => rw [hmul, heigen h, map_smul]
        change (T h w).2 * (T g w).2 = (T g w).2 * (T h w).2
        exact mul_comm _ _ }
  have hw : ∀ g, ρ g w = α g • w := heigen
  let e₀ : H × ℂ := E (kernelColumnPoint k 1)
  have hpoint (q : H × ℂ) (χ : G →* ℂ) (hq : ∀ g, ρ g q = χ g • q) (g : G) :
      IndexOne.pairing q (E (kernelColumnPoint k g)) =
        reflectChar χ g * IndexOne.pairing q e₀ := by
    have h := IndexOne.pairing_action_right ρ hρ χ hq g e₀
    change IndexOne.pairing q (NegativeColumn.action hk hi e he g
      (NegativeColumn.embedding hk hi e he (kernelColumnPoint k 1))) = _ at h
    rw [NegativeColumn.action_point, mul_one] at h
    exact h
  by_cases hunit : IsUnitaryChar α
  · left
    refine ⟨reflectChar α, ?_, fun n x c hc => ?_⟩
    · intro g
      rw [norm_reflectChar, hunit g, inv_one]
    · let L := IndexOne.pairingLinear w
      let u : kernelColumnSpan k := ∑ i, c i • kernelColumnPoint k (x i)
      have horth : IndexOne.pairing w (E u) = 0 := by
        change L (E u) = 0
        simp only [u, map_sum, map_smul, smul_eq_mul]
        calc
          ∑ i, c i * L (E (kernelColumnPoint k (x i))) =
              ∑ i, c i * (reflectChar α (x i) * L e₀) := by
            apply Finset.sum_congr rfl
            intro i _
            exact congrArg (fun a : ℂ => c i * a) (hpoint w α hw (x i))
          _ = charEval (reflectChar α) x c * L e₀ := by
            rw [charEval_apply, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            exact (mul_assoc _ _ _).symm
          _ = 0 := by rw [hc, zero_mul]
      have hw0 : w ≠ 0 := fun h => one_ne_zero (congrArg Prod.snd h)
      have hwq : (IndexOne.pairing w w).re ≤ 0 := by
        rw [IndexOne.pairing_self_nonpos_iff]
        simpa only [w, norm_one] using hz
      have hpos := IndexOne.nonneg_of_orthogonal_nonpositive hw0 hwq horth
      change 0 ≤ (IndexOne.pairing (NegativeColumn.embedding hk hi e he u)
        (NegativeColumn.embedding hk hi e he u)).re at hpos
      rw [NegativeColumn.embedding_pairing, kernelColumnPoint_sum_self_re hk] at hpos
      exact hpos
  · right
    obtain ⟨hwq, v, hwv, hvq, hvT⟩ :=
      IndexOne.exists_common_reflected_null_eigenvector T hT hcomm α hunit heigen
    change IndexOne.pairing w w = 0 at hwq
    change IndexOne.pairing w v = 1 at hwv
    have hv : ∀ g, ρ g v = reflectChar α g • v := hvT
    have hvw : IndexOne.pairing v w = 1 := by
      rw [← IndexOne.pairing_conj_symm, hwv, map_one]
    -- A nonzero eigenfunctional cannot vanish on a cyclic vector.
    have hcyclic (q : H × ℂ) (χ : G →* ℂ) (hq : ∀ g, ρ g q = χ g • q)
        (r : H × ℂ) (hqr : IndexOne.pairing q r ≠ 0) :
        IndexOne.pairing q e₀ ≠ 0 := by
      intro hzero
      let L := IndexOne.pairingLinear q
      have hpnt (g : G) : L (E (kernelColumnPoint k g)) = 0 := by
        change IndexOne.pairing q (E (kernelColumnPoint k g)) = 0
        rw [hpoint q χ hq, hzero, mul_zero]
      have hcol (u : kernelColumnSpan k) : L (E u) = 0 := by
        obtain ⟨n, x, c, rfl⟩ := exists_kernelColumnPoint_fin_sum k u
        simp only [map_sum, map_smul, hpnt, smul_zero, Finset.sum_const_zero]
      have hall (u : H × ℂ) : IndexOne.pairing q u = 0 := by
        refine (NegativeColumn.embedding_dense hk hi e he).induction_on u
          (isClosed_eq (IndexOne.continuous_pairing.comp
            (continuous_const.prodMk continuous_id)) continuous_const) ?_
        exact hcol
      exact hqr (hall r)
    have ha : IndexOne.pairing v e₀ ≠ 0 := hcyclic v (reflectChar α) hv w (by rw [hvw]; exact one_ne_zero)
    have hb : IndexOne.pairing w e₀ ≠ 0 := hcyclic w α hw v (by rw [hwv]; exact one_ne_zero)
    obtain ⟨p, hp, hdec⟩ := IndexOne.exists_positive_hyperbolic_remainder
      ρ hρ α hw hv hwq hvq hwv e₀
    refine ⟨p, α, conj (IndexOne.pairing w e₀) * IndexOne.pairing v e₀,
      hp, hunit, mul_ne_zero (star_ne_zero.mpr hb) ha, ?_⟩
    funext g
    have hkernel : IndexOne.pairing e₀ (ρ g e₀) = k g := by
      change IndexOne.pairing (NegativeColumn.embedding hk hi e he (kernelColumnPoint k 1))
        (NegativeColumn.action hk hi e he g
          (NegativeColumn.embedding hk hi e he (kernelColumnPoint k 1))) = k g
      rw [NegativeColumn.action_point, mul_one, NegativeColumn.embedding_pairing,
        kernelColumnPairing_point_left hk]
      simp only [kernelColumnPoint, kernelColumn, inv_one, one_mul]
    exact hkernel.symm.trans (hdec g)

#print axioms index_one_unitary_or_hyperbolic

end GaloisForLFunctions.HeckeKreinToeplitz
