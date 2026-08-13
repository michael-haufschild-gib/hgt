import GaloisForLFunctions.HTGeometry.GaussApexCenteredSourceLogDerivative
import GaloisForLFunctions.HTGeometry.FiniteConfluentDarboux
import GaloisForLFunctions.HTGeometry.ExtremeNode

/-!
# Finite-block outer-node and super-apex persistence

Outer interlacing only needs one finite positive moment block.  The largest current Gauss node has
positive cofactor; finite confluent Christoffel--Darboux transfers this sign to the preceding
admission, and the finite three-term recurrence makes the next admission negative there.  Monic
eventual positivity then produces a strictly larger next node.

Consequently a positive source-first moving-apex null flag cannot disappear when degree increases
at fixed mass, provided current nodes are positive.
-/

open scoped BigOperators
open Polynomial Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Finite-block outer interlacing.**  Some next Gauss node lies strictly above every current
Gauss node. -/
theorem exists_gaussNode_above_all_below {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N) :
    ∃ z ∈ gaussNodes s (m + 1), ∀ x ∈ gaussNodes s m, x < z := by
  classical
  let nodes := gaussNodes s m
  have hcard : nodes.card = m + 1 := by
    simpa only [nodes] using gaussNodes_card_below h m (by omega)
  have hnonempty : nodes.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty] at hcard
    omega
  let xi := nodes.max' hnonempty
  have hximem : xi ∈ nodes := Finset.max'_mem nodes hnonempty
  let G : Polynomial ℝ := ∏ y ∈ nodes.erase xi, (X - C y)
  have hG : monicOrtho s (m + 1) = (X - C xi) * G := by
    rw [monicOrtho_eq_prod_gaussNodes_below h (m := m) (by omega)]
    change (∏ y ∈ nodes, (X - C y)) = (X - C xi) * G
    exact (Finset.mul_prod_erase nodes (fun y => X - C y) hximem).symm
  have hGpos : 0 < G.eval xi := by
    change 0 < Polynomial.eval xi (∏ y ∈ nodes.erase xi, (X - C y))
    rw [Polynomial.eval_prod]
    apply Finset.prod_pos
    intro y hy
    have hydata := Finset.mem_erase.mp hy
    have hyle : y ≤ xi := Finset.le_max' nodes y hydata.2
    have hylt : y < xi := lt_of_le_of_ne hyle hydata.1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    linarith
  have hcd := cdKernel_diag_mul_eq_below h m (by omega) hG
  have hcofactorPrev :
      0 < G.eval xi * (monicOrtho s m).eval xi := by
    rw [← hcd]
    exact mul_pos (cdKernel_eval_self_pos_below h m (by omega) xi)
      (monicOrtho_inner_self_pos_below h (by omega))
  have hprev : 0 < (monicOrtho s m).eval xi := by
    nlinarith
  have hxroot : (monicOrtho s (m + 1)).eval xi = 0 := by
    exact (mem_gaussNodes_iff m xi).mp (by simpa only [nodes] using hximem)
  have hrec := monicOrtho_three_term_eval_below h (n := m) (by omega) xi
  have hratio : 0 <
      momentInner s (monicOrtho s (m + 1)) (monicOrtho s (m + 1)) /
        momentInner s (monicOrtho s m) (monicOrtho s m) :=
    div_pos (monicOrtho_inner_self_pos_below h (by omega))
      (monicOrtho_inner_self_pos_below h (by omega))
  have hnextNeg : (monicOrtho s (m + 2)).eval xi < 0 := by
    rw [hxroot] at hrec
    simp only [mul_zero, add_zero] at hrec
    nlinarith
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp
    (monic_eventually_pos (monicOrtho_monic s (m + 2)))
  let R := max R0 (xi + 1)
  have hxiR : xi < R := lt_of_lt_of_le (lt_add_one xi) (le_max_right _ _)
  have hnextR : 0 < (monicOrtho s (m + 2)).eval R :=
    hR0 R (le_max_left _ _)
  obtain ⟨z, hz, hzroot⟩ := intermediate_value_Ioo hxiR.le
    (continuousOn_eval (monicOrtho s (m + 2)) _) ⟨hnextNeg, hnextR⟩
  refine ⟨z, (mem_gaussNodes_iff (m + 1) z).mpr hzroot, ?_⟩
  intro x hxmem
  exact lt_of_le_of_lt (Finset.le_max' nodes x (by simpa only [nodes] using hxmem)) hz.1

/-- Every threshold exceeded by a current node is exceeded by a next-degree node. -/
theorem exists_gaussNode_above_threshold_succ_below {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N) {a : ℝ}
    (hcurrent : ∃ x ∈ gaussNodes s m, a < x) :
    ∃ z ∈ gaussNodes s (m + 1), a < z := by
  obtain ⟨z, hzmem, hzall⟩ := exists_gaussNode_above_all_below h hmN
  obtain ⟨x, hxmem, hax⟩ := hcurrent
  exact ⟨z, hzmem, hax.trans (hzall x hxmem)⟩

/-- **Fixed-mass null-flag persistence.**  On a positive current node set, positive super-apex
source cannot disappear under one degree renewal.  Positive shear is nodewise before aggregation. -/
theorem gaussSuperApexNullFlagPoissonSource_succ_pos_of_pos
    {N m : ℕ} (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N)
    {y : ℝ} (hy : 0 < y)
    (hnodes : ∀ x ∈ gaussNodes s m, 0 < x)
    (a : ℝ) {eta : ℝ} (heta : 0 < eta)
    (hsource : 0 < gaussSuperApexNullFlagPoissonSource s m y a eta) :
    0 < gaussSuperApexNullFlagPoissonSource s (m + 1) y a eta := by
  rw [gaussSuperApexNullFlagPoissonSource_pos_iff s m y a heta] at hsource
  obtain ⟨x, hxmem, hxresidue⟩ := hsource
  have hxapex : 1 < y * x :=
    (gaussApexCenteredResidue_pos_iff hy (hnodes x hxmem)).mp hxresidue
  obtain ⟨z, hzmem, hxz⟩ := exists_gaussNode_above_all_below h hmN
  have hxz' : x < z := hxz x hxmem
  have hzpos : 0 < z := (hnodes x hxmem).trans hxz'
  have hzapex : 1 < y * z := by nlinarith
  rw [gaussSuperApexNullFlagPoissonSource_pos_iff s (m + 1) y a heta]
  exact ⟨z, hzmem, (gaussApexCenteredResidue_pos_iff hy hzpos).mpr hzapex⟩

end HTGeometry
