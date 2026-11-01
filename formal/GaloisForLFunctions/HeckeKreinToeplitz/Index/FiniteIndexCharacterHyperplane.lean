import GaloisForLFunctions.HeckeKreinToeplitz.Index.CommutingFiniteIndexIsometries
import GaloisForLFunctions.HeckeKreinToeplitz.Index.CompletedFrameRepresentation
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeCoefficients
import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula

/-!
# Character hyperplanes lower every finite negative index

Commuting completed translations have a common nonpositive eigenline. Its
reflected character makes every zero-mass synthesis orthogonal to that line,
so every strictly negative subspace in the character hyperplane loses one
possible dimension. No growth assumption is imposed on the kernel.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Module
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [CommGroup G] {k : G → ℂ}

/-- A finite-index abelian kernel has a character hyperplane with one fewer possible
negative square, uniformly over every finite Gram restriction. -/
theorem exists_index_lowering_character_hyperplane {r : ℕ}
    (hk : IsHermKernel k) (hi : negIndex k ≤ r + 1) :
    ∃ χ : G →* ℂ, ∀ (n : ℕ) (x : Fin n → G) (U : Submodule ℂ (Fin n → ℂ)),
      (∀ c ∈ U, charEval χ x c = 0) →
      (∀ c ∈ U, c ≠ 0 → hermQuad (gram k x) c < 0) → finrank ℂ U ≤ r := by
  classical
  obtain ⟨m, hm, e, he, hp⟩ := exists_maximal_negative_column_frame hk (r := r + 1) (by
    simpa only [Nat.cast_add, Nat.cast_one] using hi)
  by_cases hm0 : m = 0
  · subst m
    refine ⟨1, ?_⟩
    intro n x U _ hneg
    have hU : U = ⊥ := by
      apply le_antisymm
      · intro c hc
        apply (Submodule.mem_bot ℂ).mpr
        by_contra hc0
        have hpos := hp (∑ i, c i • kernelColumnPoint k (x i)) (fun i => Fin.elim0 i)
        rw [kernelColumnPoint_sum_self_re hk] at hpos
        exact (not_lt_of_ge hpos) (hneg c hc hc0)
      · exact bot_le
    rw [hU, finrank_bot]
    exact Nat.zero_le r
  · letI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm0⟩⟩
    let H := NegativeFrame.Hilbert hk e he hp
    let T : G → (H × EuclideanSpace ℂ (Fin m)) ≃L[ℂ]
        (H × EuclideanSpace ℂ (Fin m)) := NegativeFrame.action hk e he hp
    let E : kernelColumnSpan k →ₗ[ℂ] (H × EuclideanSpace ℂ (Fin m)) :=
      NegativeFrame.embedding hk e he hp
    have hT : ∀ g v w, FiniteNegative.pairing (T g v) (T g w) = FiniteNegative.pairing v w :=
      NegativeFrame.action_pairing hk e he hp
    have hmul (a b : G) (v : H × EuclideanSpace ℂ (Fin m)) : T (a * b) v = T a (T b v) :=
      NegativeFrame.action_mul hk e he hp a b v
    have hone (v : H × EuclideanSpace ℂ (Fin m)) : T 1 v = v :=
      NegativeFrame.action_one hk e he hp v
    have hcomm (a b : G) (v : H × EuclideanSpace ℂ (Fin m)) : T a (T b v) = T b (T a v) := by
      rw [← hmul, ← hmul, mul_comm a b]
    obtain ⟨w, a, hw, hwq, ha⟩ := FiniteNegative.exists_common_nonpositive_eigenvector T hT hcomm
    have heigen (g : G) : T g w = a g • w := (ha g).2
    let α : G →* ℂ :=
      { toFun := a
        map_one' := by
          apply smul_left_injective ℂ hw
          change a 1 • w = (1 : ℂ) • w
          rw [one_smul]
          exact (heigen 1).symm.trans (hone w)
        map_mul' := by
          intro g h
          apply smul_left_injective ℂ hw
          calc
            a (g * h) • w = T (g * h) w := (heigen (g * h)).symm
            _ = T g (T h w) := hmul g h w
            _ = a h • (a g • w) := by rw [heigen h, map_smul, heigen g]
            _ = (a g * a h) • w := by rw [smul_smul, mul_comm] }
    let L := FiniteNegative.pairingLinear w
    have htransform (g : G) (v : H × EuclideanSpace ℂ (Fin m)) :
        L (T g v) = reflectChar α g * L v := by
      have h := hT g (T g⁻¹ w) v
      have hcancel : T g (T g⁻¹ w) = w := by rw [← hmul, mul_inv_cancel, hone]
      rw [hcancel] at h
      change FiniteNegative.pairing w (T g v) = conj (a g⁻¹) * FiniteNegative.pairing w v
      rw [h]
      conv_lhs => rw [heigen g⁻¹]
      exact FiniteNegative.pairing_smul_left _ _ _
    have hpoint (g : G) : L (E (kernelColumnPoint k g)) =
        reflectChar α g * L (E (kernelColumnPoint k 1)) := by
      have h := htransform g (E (kernelColumnPoint k 1))
      change L (NegativeFrame.action hk e he hp g
        (NegativeFrame.embedding hk e he hp (kernelColumnPoint k 1))) = _ at h
      rw [NegativeFrame.action_point, mul_one] at h
      exact h
    refine ⟨reflectChar α, ?_⟩
    intro n x U hmass hneg
    let F : U →ₗ[ℂ] (H × EuclideanSpace ℂ (Fin m)) :=
      E.comp ((kernelColumnSynthesis (fun i => kernelColumnPoint k (x i))).comp U.subtype)
    have hFpair (c : U) : (FiniteNegative.pairing (F c) (F c)).re = hermQuad (gram k x) c := by
      change (FiniteNegative.pairing (E (∑ i, c.1 i • kernelColumnPoint k (x i)))
        (E (∑ i, c.1 i • kernelColumnPoint k (x i)))).re = _
      rw [NegativeFrame.embedding_pairing, kernelColumnPoint_sum_self_re hk]
    have hFneg (c : U) (hc : c ≠ 0) : (FiniteNegative.pairing (F c) (F c)).re < 0 := by
      rw [hFpair]
      exact hneg c c.property (fun h => hc (Subtype.ext h))
    have horth (c : U) : FiniteNegative.pairing w (F c) = 0 := by
      change L (E (∑ i, c.1 i • kernelColumnPoint k (x i))) = 0
      simp only [map_sum, map_smul, smul_eq_mul]
      calc
        ∑ i, c.1 i * L (E (kernelColumnPoint k (x i))) =
            ∑ i, c.1 i * (reflectChar α (x i) * L (E (kernelColumnPoint k 1))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hpoint]
        _ = charEval (reflectChar α) x c * L (E (kernelColumnPoint k 1)) := by
          rw [charEval_apply, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          exact (mul_assoc _ _ _).symm
        _ = 0 := by rw [hmass c c.property, zero_mul]
    have hd := FiniteNegative.finrank_add_one_le_of_negative_orthogonal F w horth hFneg hw hwq
    have hdim : finrank ℂ (EuclideanSpace ℂ (Fin m)) = m := by simp
    rw [hdim] at hd
    omega

#print axioms exists_index_lowering_character_hyperplane

end GaloisForLFunctions.HeckeKreinToeplitz
