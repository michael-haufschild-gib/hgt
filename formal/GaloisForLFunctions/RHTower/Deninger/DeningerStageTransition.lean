import GaloisForLFunctions.RHTower.Deninger.DeningerFormPullback

/-!
# The transition maps between finite character stages

A finite-index inclusion of lattices induces a power isogeny of character tori and an inclusion of
finite-dimensional subspaces induces a coordinate projection; both are monomial maps, given by an
integer matrix of exponents.  These maps are holomorphic on the stage, preserve it, and compose
according to matrix multiplication, so the finite stages form a cofiltered system of complex tori.
Pulling back differential forms along them transports the holomorphic de Rham complexes.

* `deningerMonomialMap` : the monomial transition map of an integer matrix.
* `deningerMonomialMap_mapsTo`, `deningerMonomialMap_analyticOnNhd` : it preserves the stage and is
  holomorphic there.
* `deningerMonomialMap_comp` : composition is matrix multiplication.
* `deningerMonomialPullback_holomorphic`, `deningerMonomialPullback_extDeriv` : the induced maps of
  holomorphic de Rham complexes.
-/

namespace RHTower

section Monomial

variable {r s t : ℕ}

/-- **The transition map between finite character stages** attached to an integer matrix of
exponents: the monomial map covering both the power isogenies of finite-index lattice inclusions and
the coordinate projections of inclusions of finite-dimensional subspaces. -/
noncomputable def deningerMonomialMap (m : Fin r → Fin s → ℤ) :
    (Fin s → ℂ) → (Fin r → ℂ) := fun z i => ∏ j, (z j) ^ (m i j)

theorem deningerMonomialMap_apply (m : Fin r → Fin s → ℤ) (z : Fin s → ℂ) (i : Fin r) :
    deningerMonomialMap m z i = ∏ j, (z j) ^ (m i j) := rfl

/-- **The transition maps preserve the stage.** -/
theorem deningerMonomialMap_mapsTo (m : Fin r → Fin s → ℤ) :
    Set.MapsTo (deningerMonomialMap m) (deningerStageTorus s) (deningerStageTorus r) := by
  intro z hz i
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ (hz j)

/-- **The transition maps are holomorphic on the stage.** -/
theorem deningerMonomialMap_analyticOnNhd (m : Fin r → Fin s → ℤ) :
    AnalyticOnNhd ℂ (deningerMonomialMap m) (deningerStageTorus s) := by
  intro z hz
  refine AnalyticAt.pi fun i => ?_
  have h : AnalyticAt ℂ (∏ j : Fin s, fun w : Fin s → ℂ => (w j) ^ (m i j)) z := by
    refine Finset.analyticAt_prod _ fun j _ => ?_
    have hproj : AnalyticAt ℂ (fun w : Fin s → ℂ => w j) z :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j).analyticAt z
    exact hproj.zpow (hz j)
  have hfun : (∏ j : Fin s, fun w : Fin s → ℂ => (w j) ^ (m i j)) =
      fun w : Fin s → ℂ => ∏ j : Fin s, (w j) ^ (m i j) := by
    funext w
    simp [Finset.prod_apply]
  rwa [hfun] at h

/-- A power of a fixed invertible scalar over a finite index set is the power at the summed
exponent. -/
theorem deningerProd_zpow_eq_zpow_sum {ι : Type*} (S : Finset ι) {a : ℂ} (ha : a ≠ 0)
    (c : ι → ℤ) : ∏ j ∈ S, a ^ (c j) = a ^ (∑ j ∈ S, c j) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | @insert j S hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, zpow_add₀ ha, ih]

/-- **Composing transition maps multiplies the exponent matrices**, so the finite character stages
form a cofiltered system. -/
theorem deningerMonomialMap_comp (m : Fin r → Fin s → ℤ) (n : Fin s → Fin t → ℤ) :
    Set.EqOn (deningerMonomialMap m ∘ deningerMonomialMap n)
      (deningerMonomialMap fun i k => ∑ j, m i j * n j k) (deningerStageTorus t) := by
  intro z hz
  funext i
  show ∏ j, (∏ k, (z k) ^ (n j k)) ^ (m i j) = ∏ k, (z k) ^ (∑ j, m i j * n j k)
  calc ∏ j, (∏ k, (z k) ^ (n j k)) ^ (m i j)
      = ∏ j, ∏ k, ((z k) ^ (n j k)) ^ (m i j) := by
        exact Finset.prod_congr rfl fun j _ => (Finset.prod_zpow _ _ _).symm
    _ = ∏ j, ∏ k, (z k) ^ (m i j * n j k) := by
        refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun k _ => ?_
        rw [← zpow_mul, mul_comm (n j k) (m i j)]
    _ = ∏ k, ∏ j, (z k) ^ (m i j * n j k) := Finset.prod_comm
    _ = ∏ k, (z k) ^ (∑ j, m i j * n j k) := by
        exact Finset.prod_congr rfl fun k _ =>
          deningerProd_zpow_eq_zpow_sum _ (hz k) fun j => m i j * n j k

/-- **The identity transition map.** -/
theorem deningerMonomialMap_id :
    Set.EqOn (deningerMonomialMap fun i j : Fin r => if i = j then (1 : ℤ) else 0) id
      (deningerStageTorus r) := by
  intro z _
  funext i
  show (∏ j, (z j) ^ (if i = j then (1 : ℤ) else 0)) = z i
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg (fun h => hj h.symm), zpow_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Monomial

section MonomialPullback

variable {r s n : ℕ}

/-- **The pullback of a holomorphic stage form along a transition map is holomorphic.** -/
theorem deningerMonomialPullback_holomorphic (m : Fin r → Fin s → ℤ)
    {ω : DeningerStageForm r n} (hω : DeningerIsHolomorphicForm ω) :
    DeningerIsHolomorphicForm (deningerStagePullback (deningerMonomialMap m) ω) :=
  deningerStagePullback_holomorphic (deningerMonomialMap_analyticOnNhd m)
    (deningerMonomialMap_mapsTo m) hω

/-- **The transition maps are maps of holomorphic de Rham complexes**: pulling back commutes with
the exterior derivative.  This is what makes the cylinder de Rham complex a colimit of complexes. -/
theorem deningerMonomialPullback_extDeriv (m : Fin r → Fin s → ℤ)
    {ω : DeningerStageForm r n} (hω : DeningerIsHolomorphicForm ω) {z : Fin s → ℂ}
    (hz : z ∈ deningerStageTorus s) :
    extDeriv (deningerStagePullback (deningerMonomialMap m) ω) z =
      deningerStagePullback (deningerMonomialMap m) (extDeriv ω) z :=
  deningerStagePullback_extDeriv (deningerMonomialMap_analyticOnNhd m)
    (deningerMonomialMap_mapsTo m) hω hz

end MonomialPullback

end RHTower
