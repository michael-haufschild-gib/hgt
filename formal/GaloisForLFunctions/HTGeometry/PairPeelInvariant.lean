import GaloisForLFunctions.HTGeometry.PairPeelStep

/-!
# The peel restores the shape and the limit

After one peel the new starting vector is

`E(H) + H·c`,   `c = (∏_(i<m) p_i)·α(X_m)·(1 + deg g)`,

where `H` is the border entry one level down and `E` the scalar operator there.  Dividing by `c` —
free, by the orbit rescaling law — leaves `H + E(H)/c`, and `E(H)` already has degree `−2` while
`1/c` does not raise it.  So the rescaled vector is shaped again.

Its own value at infinity is the border row one level further down, because the shifted operator
keeps degree zero on a border row while `1/c` drops one.  Both conditions are therefore
self-sustaining, which is what lets the peel be iterated down the flag.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ} {α γ δ : Polynomial ℂ} {n : ℕ}

/-! ## Degrees on a border row -/

theorem topDegLE_pairLogBorder_zero (hγ : γ ≠ 0) (hpn : p n = affinePair γ δ) {k : ℕ}
    (hk : k ≤ n) : TopDegLE (n + 1) 0 (pairLogBorder p (n + 1) k) :=
  TopLim.topDegLE_zero
    (topFree_of_mem_coordField (by omega) (headBorder_mem_coordField γ n k))
    (topLim_pairLogBorder hγ hpn hk)

theorem topDegLE_pairJet_succ (hpn : p n = affinePair γ δ) :
    TopDegLE (n + 1) 1 (pairJet p (n + 1)) := by
  rw [pairJet_succ]
  have h1 : TopDegLE (n + 1) 0 (pairJet p n) := topFree_pairJet_top.topDegLE
  have h2 : TopDegLE (n + 1) ((MvPolynomial.degreeOf 1 (p n) : ℤ)) (pairFactor (p n) n) :=
    topDegLE_pairFactor_top n (p n)
  have hle : ((MvPolynomial.degreeOf 1 (p n) : ℕ) : ℤ) ≤ 1 := by
    have : MvPolynomial.degreeOf 1 (p n) ≤ 1 := by
      rw [hpn]
      exact degreeOf_one_affinePair γ δ
    exact_mod_cast this
  have hmul := TopDegLE.mul h1 h2
  refine TopDegLE.mono ?_ hmul
  omega

/-- **The shifted operator keeps degree zero away from the newest coordinate.** -/
theorem topDegLE_pairGradShift_zero (hγ : γ ≠ 0) (hpn : p n = affinePair γ δ)
    (hne : ∀ j, pairFactor (p j) j ≠ 0) {k : ℕ} (hk : k < n + 1)
    {u : ℕ → CascadeField}
    (hmem : ∀ l, u l ∈ coordField (n + 1))
    (hlow : ∀ l, l < n + 1 → TopDegLE (n + 1) 0 (u l))
    (htop : TopDegLE (n + 1) (-1) (u (n + 1))) :
    TopDegLE (n + 1) 0 (pairGradShift p (n + 1) u k) := by
  rw [pairGradShift]
  refine TopDegLE.add (topDegLE_pairDerivation_coordField ?_ (hmem k) (hlow k hk)) ?_
  · rw [hpn]
    exact degreeOf_one_affinePair γ δ
  refine topDegLE_sum _ _ fun l hl => ?_
  have hlm : l ≤ n + 1 := by
    have := Finset.mem_range.mp hl
    omega
  rcases eq_or_lt_of_le hlm with rfl | hlt
  · rw [pairResponse_eq_pairLogBorder hne k (n + 1), mul_assoc]
    have hmul := TopDegLE.mul (topDegLE_pairLogBorder_zero hγ hpn (by omega : k ≤ n))
      (TopDegLE.mul (topDegLE_pairJet_succ hpn) htop)
    refine TopDegLE.mono ?_ hmul
    omega
  · have hfree : TopFree (n + 1) (pairResponse p k l) := topFree_pairResponse hlt
    have hmul := TopDegLE.mul hfree.topDegLE (hlow l hlt)
    refine TopDegLE.mono ?_ hmul
    omega

/-! ## The rescaling factor -/

/-- The factor that restores the shape of the peeled vector. -/
noncomputable def pairPeelScale (p : ℕ → MvPolynomial (Fin 2) ℂ) (α g : Polynomial ℂ) (m' : ℕ) :
    CascadeField :=
  pairJet p m' * fact α m' * pairPeelRes g 0

theorem pairPeelRes_zero_ne_zero (g : Polynomial ℂ) : pairPeelRes g 0 ≠ 0 := by
  show algebraMap ℂ CascadeField (1 + (g.natDegree : ℂ)) ≠ 0
  refine (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr ?_
  intro hc
  have hre : (1 : ℝ) + (g.natDegree : ℝ) = 0 := by
    have := congrArg Complex.re hc
    simpa using this
  have : (0 : ℝ) ≤ (g.natDegree : ℝ) := Nat.cast_nonneg _
  linarith

theorem pairPeelScale_ne_zero (hα : α ≠ 0) (g : Polynomial ℂ)
    (hne : ∀ j, pairFactor (p j) j ≠ 0) (m' : ℕ) : pairPeelScale p α g m' ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pairJet_ne_zero hne m') (fact_ne_zero hα m'))
    (pairPeelRes_zero_ne_zero g)

theorem inv_pairPeelScale_mem_coordField (α g : Polynomial ℂ) (m : ℕ) {m' : ℕ} (h : m' ≤ m) :
    (pairPeelScale p α g m')⁻¹ ∈ coordField m := by
  rw [pairPeelScale]
  refine inv_mem (mul_mem (mul_mem (pairJet_mem_coordField h) (fact_mem_coordField h α)) ?_)
  exact pairPeelRes_mem_coordField g m 0

/-- **The rescaling factor's inverse drops a degree.** -/
theorem topDegLE_inv_pairPeelScale (hα : α ≠ 0) (g : Polynomial ℂ)
    (hpn : p n = affinePair γ δ) (hγ : γ ≠ 0) :
    TopDegLE (n + 1) (-1) ((pairPeelScale p α g (n + 1))⁻¹) := by
  rw [pairPeelScale, mul_inv, mul_inv, pairJet_succ, mul_inv]
  have h1 : TopFree (n + 1) ((pairJet p n)⁻¹) := TopFree.inv topFree_pairJet_top
  have h2 : TopDegLE (n + 1) (-1) ((pairFactor (p n) n)⁻¹) := by
    rw [hpn]
    exact topDegLE_inv_pairFactor_affine hγ δ n
  have h3 : TopDegLE (n + 1) (-(α.natDegree : ℤ)) ((fact α (n + 1))⁻¹) :=
    topDegLE_inv_fact (n + 1) hα
  have h4 : TopFree (n + 1) ((pairPeelRes g 0)⁻¹) := by
    show TopFree (n + 1) ((algebraMap ℂ CascadeField (1 + (g.natDegree : ℂ)))⁻¹)
    rw [← map_inv₀]
    exact topFree_algebraMap_complex (n + 1) _
  have hmul := TopDegLE.mul (TopDegLE.mul (TopDegLE.mul h1.topDegLE h2) h3) h4.topDegLE
  refine TopDegLE.mono ?_ hmul
  omega

/-! ## The rescaled vector -/

theorem pairLimVec_one_rescaled (α g : Polynomial ℂ) {L : ℕ → CascadeField} {l : ℕ}
    (hl : l ≤ n + 1) (hc : pairPeelScale p α g (n + 1) ≠ 0) :
    (pairPeelScale p α g (n + 1))⁻¹ * pairLimVec p α (n + 1) L (pairPeelRes g) 1 l
      = (pairPeelScale p α g (n + 1))⁻¹ * pairGradShift p (n + 1) L l
        + headBorder p α (n + 1) l := by
  rw [pairLimVec_succ_of_le p α (n + 1) L (pairPeelRes g) 0 l hl, pairLimVec_zero, mul_add]
  congr 1
  rw [show pairJet p (n + 1) * fact α (n + 1) * pairPeelRes g 0
      = pairPeelScale p α g (n + 1) from rfl, ← mul_assoc,
    mul_comm ((pairPeelScale p α g (n + 1))⁻¹) (headBorder p α (n + 1) l), mul_assoc,
    inv_mul_cancel₀ hc, mul_one]

/-- **The peel restores the shape.** -/
theorem pairBorderShape_rescaled (hα : α ≠ 0) (hγ : γ ≠ 0) (hpn : p n = affinePair γ δ)
    (g : Polynomial ℂ) (hne : ∀ j, pairFactor (p j) j ≠ 0) :
    PairBorderShape p α (n + 1)
      (fun l => (pairPeelScale p α g (n + 1))⁻¹
        * pairLimVec p α (n + 1) (headBorder p α (n + 1)) (pairPeelRes g) 1 l) := by
  have hc : pairPeelScale p α g (n + 1) ≠ 0 := pairPeelScale_ne_zero hα g hne (n + 1)
  rw [PairBorderShape,
    pairLimVec_one_rescaled α g (le_refl (n + 1)) hc, add_sub_cancel_right,
    pairGradShift_top]
  have h1 : TopDegLE (n + 1) (-2)
      (pairTopShift p (n + 1) (headBorder p α (n + 1) (n + 1))) :=
    topDegLE_pairTopShift_headBorder hγ hα hpn
  have h2 : TopDegLE (n + 1) 0 ((pairPeelScale p α g (n + 1))⁻¹) :=
    TopDegLE.mono (by norm_num) (topDegLE_inv_pairPeelScale hα g hpn hγ)
  have hmul := TopDegLE.mul h2 h1
  refine TopDegLE.mono ?_ hmul
  omega

/-! ## The border row's own limit -/

/-- **The border row converges to the border row one level down.** -/
theorem topLim_headBorder (hγ : γ ≠ 0) (hpn : p n = affinePair γ δ) (g : Polynomial ℂ) (l : ℕ) :
    TopLim (n + 1) (headBorder p g (n + 1) l) (headBorder p γ n l) := by
  by_cases hl : l ≤ n
  · rw [headBorder_of_ne (by omega : l ≠ n + 1)]
    exact topLim_pairLogBorder hγ hpn hl
  · by_cases hl2 : l = n + 1
    · subst hl2
      rw [headBorder_of_ne (by omega : n + 1 ≠ n), pairLogBorder_eq_zero_of_gt (by omega),
        TopLim, sub_zero]
      exact topDegLE_headBorder_top hγ g hpn
    · rw [headBorder_eq_zero_of_gt (by omega : n < l),
        headBorder_eq_zero_of_gt (by omega : n + 1 < l)]
      exact topLim_const

/-- **The rescaled peeled vector converges to the border row one level down.** -/
theorem topLim_rescaled_pairLimVec (hα : α ≠ 0) (hγ : γ ≠ 0) (hpn : p n = affinePair γ δ)
    (g : Polynomial ℂ) (hne : ∀ j, pairFactor (p j) j ≠ 0) (l : ℕ) :
    TopLim (n + 1)
      ((pairPeelScale p α g (n + 1))⁻¹
        * pairLimVec p α (n + 1) (headBorder p α (n + 1)) (pairPeelRes g) 1 l)
      (headBorder p γ n l) := by
  have hc : pairPeelScale p α g (n + 1) ≠ 0 := pairPeelScale_ne_zero hα g hne (n + 1)
  by_cases hl : l ≤ n
  · rw [pairLimVec_one_rescaled α g (by omega : l ≤ n + 1) hc]
    have hgs : TopDegLE (n + 1) 0
        (pairGradShift p (n + 1) (headBorder p α (n + 1)) l) := by
      refine topDegLE_pairGradShift_zero hγ hpn hne (by omega)
        (fun l' => headBorder_mem_coordField α (n + 1) l') (fun l' hl' => ?_) ?_
      · rw [headBorder_of_ne (by omega : l' ≠ n + 1)]
        exact topDegLE_pairLogBorder_zero hγ hpn (by omega)
      · exact topDegLE_headBorder_top hγ α hpn
    have hdrop : TopLim (n + 1)
        ((pairPeelScale p α g (n + 1))⁻¹
          * pairGradShift p (n + 1) (headBorder p α (n + 1)) l) 0 := by
      rw [TopLim, sub_zero]
      have := TopDegLE.mul (topDegLE_inv_pairPeelScale hα g hpn hγ) hgs
      simpa using this
    have hborder : TopLim (n + 1) (headBorder p α (n + 1) l) (headBorder p γ n l) :=
      topLim_headBorder hγ hpn α l
    have hsum := TopLim.add hdrop hborder
    rw [zero_add] at hsum
    exact hsum
  · by_cases hl2 : l = n + 1
    · subst hl2
      rw [headBorder_of_ne (by omega : n + 1 ≠ n), pairLogBorder_eq_zero_of_gt (by omega),
        TopLim, sub_zero]
      have hshape := pairBorderShape_rescaled hα hγ hpn g hne
      rw [PairBorderShape] at hshape
      have hsplit : (pairPeelScale p α g (n + 1))⁻¹
            * pairLimVec p α (n + 1) (headBorder p α (n + 1)) (pairPeelRes g) 1 (n + 1)
          = ((pairPeelScale p α g (n + 1))⁻¹
              * pairLimVec p α (n + 1) (headBorder p α (n + 1)) (pairPeelRes g) 1 (n + 1)
              - headBorder p α (n + 1) (n + 1)) + headBorder p α (n + 1) (n + 1) := by
        ring
      rw [hsplit]
      exact TopDegLE.add (TopDegLE.mono (by norm_num) hshape)
        (topDegLE_headBorder_top hγ α hpn)
    · rw [pairLimVec_succ_of_gt p α (n + 1) (headBorder p α (n + 1)) (pairPeelRes g) 0 l
        (by omega), mul_zero, headBorder_eq_zero_of_gt (by omega : n < l)]
      exact topLim_const

end GaloisForLFunctions.HTGeometry
