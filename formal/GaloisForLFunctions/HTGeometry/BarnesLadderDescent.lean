import GaloisForLFunctions.HTGeometry.BarnesSubframeLadderStep
import GaloisForLFunctions.HTGeometry.LadderProductPeeling

/-!
# The descent to a single direction

Peeling one direction off the ladder product and replacing the defect it produces by the
deleted-frame source costs only a differentially algebraic term, so the induction on the number of
directions runs:

```text
(∏_{k ∈ S.erase j} (T_k - 1)) Ψ_S  =  (-1)^{|S|-1} Ψ_{j}   modulo the DA sector.
```

At `S = univ` this is the ladder hypothesis of the annihilator theorem, with the sign that theorem
now tolerates.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

theorem differentialAlgebraicOver_zero_mero :
    DifferentialAlgebraicOver (RatFunc ℂ) (0 : meroField (Set.univ : Set ℂ)) := by
  have h := differentialAlgebraicOver_algebraMap (F := RatFunc ℂ)
    (E := meroField (Set.univ : Set ℂ)) 0
  rwa [map_zero] at h

theorem differentialAlgebraicOver_neg_mero {x : meroField (Set.univ : Set ℂ)}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) (-x) := by
  have h := differentialAlgebraicOver_sub differentialAlgebraicOver_zero_mero hx
  rwa [zero_sub] at h

/-- **The descent to a single direction.**  Applying the ladder product over all directions of `S`
but `j` to the subframe source reaches, modulo the differentially algebraic sector, the source of
the single direction `j`, up to the sign the peeling accumulates. -/
theorem differentialAlgebraicOver_ladderProd_descent {N : ℕ} (ω : Fin N → ℂ)
    (hω : ∀ i, 0 < (ω i).im) (j : Fin N) :
    ∀ (m : ℕ) (S : Finset (Fin N)) [Nonempty {i : Fin N // i ∈ S}], S.card = m → j ∈ S →
      letI : Nonempty {i : Fin N // i ∈ ({j} : Finset (Fin N))} :=
        ⟨⟨j, Finset.mem_singleton_self j⟩⟩
      DifferentialAlgebraicOver (RatFunc ℂ)
        (diffTranslateApply ω (ladderProd (S.erase j))
            (barnesSourceLogDerivMero (subframe ω S) (subframe_im_pos hω S))
          - (-1 : meroField (Set.univ : Set ℂ)) ^ (m - 1) *
            barnesSourceLogDerivMero (subframe ω ({j} : Finset (Fin N)))
              (subframe_im_pos hω ({j} : Finset (Fin N)))) := by
  classical
  intro m
  induction m with
  | zero =>
      intro S _ hcard hj
      exact absurd (Finset.card_eq_zero.mp hcard ▸ hj) (Finset.notMem_empty j)
  | succ m ih =>
      intro S hS hcard hj
      letI : Nonempty {i : Fin N // i ∈ ({j} : Finset (Fin N))} :=
        ⟨⟨j, Finset.mem_singleton_self j⟩⟩
      rcases Nat.eq_zero_or_pos m with hm | hm
      · -- one direction: the operator is the identity and the two sources agree
        subst hm
        have hSj : S = {j} := by
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
          rw [ha] at hj ⊢
          rw [Finset.mem_singleton.mp hj]
        subst hSj
        rw [Finset.erase_singleton, diffTranslateApply_ladderProd_empty, pow_zero, one_mul,
          sub_self]
        exact differentialAlgebraicOver_zero_mero
      · -- at least two directions: peel one and use the inductive hypothesis
        obtain ⟨k, hk⟩ : (S.erase j).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hj, hcard]
          omega
        have hkS : k ∈ S := Finset.mem_of_mem_erase hk
        have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
        have hcard' : (S.erase k).card = m := by
          rw [Finset.card_erase_of_mem hkS, hcard]
          omega
        have hjk : j ∈ S.erase k := Finset.mem_erase.mpr ⟨fun hc => hkj hc.symm, hj⟩
        haveI : Nonempty {i : Fin N // i ∈ S.erase k} := ⟨⟨j, hjk⟩⟩
        have h2 : 2 ≤ S.card := by omega
        have hstep := differentialAlgebraicOver_subframe_ladder_step ω hω S k hkS h2
        have hIH := ih (S.erase k) hcard' hjk
        -- peel the direction `k`
        rw [diffTranslateApply_ladderProd_erase ω hk, Finset.erase_right_comm]
        set Op : meroField (Set.univ : Set ℂ) → meroField (Set.univ : Set ℂ) :=
          fun y => diffTranslateApply ω (ladderProd ((S.erase k).erase j)) y with hOp
        set Ψ : meroField (Set.univ : Set ℂ) :=
          barnesSourceLogDerivMero (subframe ω S) (subframe_im_pos hω S) with hΨ
        set Ψ' : meroField (Set.univ : Set ℂ) :=
          barnesSourceLogDerivMero (subframe ω (S.erase k)) (subframe_im_pos hω (S.erase k))
          with hΨ'
        set Ψj : meroField (Set.univ : Set ℂ) :=
          barnesSourceLogDerivMero (subframe ω ({j} : Finset (Fin N)))
            (subframe_im_pos hω ({j} : Finset (Fin N))) with hΨj
        have hdefect : addTranslationMeroEquiv (ω k) Ψ - Ψ
            = -Ψ' + (addTranslationMeroEquiv (ω k) Ψ - Ψ + Ψ') := by ring
        rw [hdefect, diffTranslateApply_add_input, diffTranslateApply_neg_input]
        have hsign : (-1 : meroField (Set.univ : Set ℂ)) ^ (m + 1 - 1)
            = -((-1 : meroField (Set.univ : Set ℂ)) ^ (m - 1)) := by
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          rw [show m' + 1 + 1 - 1 = (m' + 1 - 1) + 1 by omega, pow_succ]
          ring
        rw [hsign]
        have hrewrite : -Op Ψ' + Op (addTranslationMeroEquiv (ω k) Ψ - Ψ + Ψ')
              - -((-1 : meroField (Set.univ : Set ℂ)) ^ (m - 1)) * Ψj
            = -(Op Ψ' - (-1 : meroField (Set.univ : Set ℂ)) ^ (m - 1) * Ψj)
              + Op (addTranslationMeroEquiv (ω k) Ψ - Ψ + Ψ') := by ring
        rw [hrewrite]
        exact differentialAlgebraicOver_add (differentialAlgebraicOver_neg_mero hIH)
          (differentialAlgebraicOver_diffTranslateApply ω _ hstep)

end

end GaloisForLFunctions.HTGeometry
