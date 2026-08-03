import GaloisForLFunctions.HTGeometry.ExponentialJetInverseSmoothness

/-!
# The local inverse of the Cayley outer jet chart

The chart is the composite of two affine jet maps, the reciprocal jet map and the exponential jet
map.  The affine maps are invertible outright, the reciprocal map is an involution, and the
exponential map has the logarithmic branch inverse, so the composite has an explicit local inverse.

Both the chart and its inverse are smooth, which is what makes the chart a local diffeomorphism
rather than merely an open map.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Locality of the inverse -/

theorem expJetTail_congr (a : ℂ) {w w' : ℕ → ℂ} :
    ∀ k, (∀ j, j ≤ k + 1 → w j = w' j) → expJetTail a w k = expJetTail a w' k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h
    have h0 : w 0 = w' 0 := h 0 (by omega)
    have hb : logBranch a (w 0) = logBranch a (w' 0) := by rw [h0]
    have hlow : ∀ j, j < k → expJetTail a w j = expJetTail a w' j := by
      intro j hj
      exact ih j hj fun i hi => h i (by omega)
    have hext : ∀ j, j ≤ k + 1 →
        expJetExtend (logBranch a (w 0))
          (fun j => if _ : j < k then expJetTail a w j else 0) j
        = expJetExtend (logBranch a (w' 0))
          (fun j => if _ : j < k then expJetTail a w' j else 0) j := by
      intro j _
      cases j with
      | zero => simpa only [expJetExtend_zero] using hb
      | succ l =>
          simp only [expJetExtend_succ]
          by_cases hl : l < k
          · simp only [dif_pos hl, hlow l hl]
          · simp only [dif_neg hl]
    have hsc : expJetScalar (expJetExtend (logBranch a (w 0))
          (fun j => if _ : j < k then expJetTail a w j else 0)) (k + 1)
        = expJetScalar (expJetExtend (logBranch a (w' 0))
          (fun j => if _ : j < k then expJetTail a w' j else 0)) (k + 1) :=
      expJetScalar_congr _ _ (k + 1) hext
    rw [expJetTail_eq, expJetTail_eq, hsc, hb, h (k + 1) (by omega)]

theorem expJetInv_congr (a : ℂ) {w w' : ℕ → ℂ} {k : ℕ} (h : ∀ j, j ≤ k → w j = w' j) :
    expJetInv a w k = expJetInv a w' k := by
  cases k with
  | zero =>
      rw [expJetInv_zero, expJetInv_zero, h 0 (le_refl 0)]
  | succ l =>
      rw [expJetInv_succ, expJetInv_succ]
      exact expJetTail_congr a l h

/-! ## The chart inverse -/

theorem neg_two_I_ne_zero : (-(2 * Complex.I)) ≠ 0 := by
  simp [Complex.I_ne_zero]

/-- The local inverse of the Cayley outer jet chart, through the logarithmic branch at `a`: undo
the exponential, undo the outer affine map, invert, undo the inner affine map. -/
def chiJetInv (a : ℂ) (w : ℕ → ℂ) : ℕ → ℂ :=
  fun k => affJetScalar (1 : ℂ)⁻¹ (-(Complex.I / 1))
    (fun l => invJetScalar (fun m => affJetScalar (-(2 * Complex.I))⁻¹
      (-(1 / (-(2 * Complex.I)))) (expJetInv a w) m) l) k

/-- The pivot of the inverse chart: the zeroth entry after undoing the exponential and the outer
affine map.  It is nonzero exactly when the branch avoids the Möbius pole. -/
theorem chiJetPivot_ne_zero {a : ℂ} {w : ℕ → ℂ} (hbranch : logBranch a (w 0) ≠ 1) :
    affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I)))) (expJetInv a w) 0 ≠ 0 := by
  rw [affJetScalar_apply_zero]
  have hval : (-(2 * Complex.I))⁻¹ * expJetInv a w 0 + -(1 / (-(2 * Complex.I)))
      = (-(2 * Complex.I))⁻¹ * (expJetInv a w 0 - 1) := by
    field_simp
    ring
  rw [hval]
  refine mul_ne_zero (inv_ne_zero neg_two_I_ne_zero) (sub_ne_zero.mpr ?_)
  rw [expJetInv_zero]
  exact hbranch

theorem chiJetInv_congr (a : ℂ) {w w' : ℕ → ℂ} {k : ℕ} (h : ∀ j, j ≤ k → w j = w' j) :
    chiJetInv a w k = chiJetInv a w' k := by
  have hbase : ∀ j, j ≤ k →
      affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I)))) (expJetInv a w) j
      = affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I)))) (expJetInv a w') j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [affJetScalar_apply_zero, affJetScalar_apply_zero,
        expJetInv_congr a (k := 0) fun i hi => h i (by omega)]
    · rw [affJetScalar_apply_of_ne _ _ _ hj0, affJetScalar_apply_of_ne _ _ _ hj0,
        expJetInv_congr a (k := j) fun i hi => h i (by omega)]
  have hinv : ∀ j, j ≤ k →
      invJetScalar (affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I))))
        (expJetInv a w)) j
      = invJetScalar (affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I))))
        (expJetInv a w')) j := by
    intro j hj
    exact invJetScalar_congr (K := j) (fun i hi => hbase i (by omega)) j (le_refl j)
  by_cases hk : k = 0
  · subst hk
    rw [chiJetInv, chiJetInv, affJetScalar_apply_zero, affJetScalar_apply_zero,
      hinv 0 (le_refl 0)]
  · rw [chiJetInv, chiJetInv, affJetScalar_apply_of_ne _ _ _ hk,
      affJetScalar_apply_of_ne _ _ _ hk, hinv k (le_refl k)]

/-- **The chart inverse really inverts.**  Every packet whose zeroth entry is nonzero and whose
branch avoids the Möbius pole is the Cayley outer jet packet of its inverse. -/
theorem chiJetScalar_chiJetInv {a : ℂ} {w : ℕ → ℂ} (hw : w 0 ≠ 0)
    (hbranch : logBranch a (w 0) ≠ 1) (k : ℕ) :
    chiJetScalar (chiJetInv a w) k = w k := by
  have hA : (fun m => affJetScalar 1 Complex.I (chiJetInv a w) m)
      = invJetScalar (affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I))))
        (expJetInv a w)) := by
    funext m
    exact affJetScalar_affJetScalar (a := (1 : ℂ)) (b := Complex.I) one_ne_zero _ m
  have hB : (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I (chiJetInv a w) m) l)
      = affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I)))) (expJetInv a w) := by
    rw [hA]
    funext l
    exact invJetScalar_invJetScalar (chiJetPivot_ne_zero hbranch) l
  have hC : (fun j => affJetScalar (-(2 * Complex.I)) 1
      (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I (chiJetInv a w) m) l) j)
      = expJetInv a w := by
    rw [hB]
    funext j
    exact affJetScalar_affJetScalar neg_two_I_ne_zero _ j
  have hchi : chiJetScalar (chiJetInv a w) k
      = expJetScalar (fun j => affJetScalar (-(2 * Complex.I)) 1
        (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I (chiJetInv a w) m) l) j) k := rfl
  rw [hchi, hC]
  exact expJetScalar_expJetInv hw k

/-! ## Smoothness of the chart inverse -/

theorem contDiffOn_chiJetInv_comp {V : Set X} {W : X → ℕ → ℂ} (a : ℂ)
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => W x j) V)
    (hslit : ∀ x ∈ V, W x 0 / Complex.exp a ∈ Complex.slitPlane)
    (hpole : ∀ x ∈ V, logBranch a (W x 0) ≠ 1) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => chiJetInv a (W x) k) V := by
  have h1 : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => expJetInv a (W x) j) V :=
    fun j => contDiffOn_expJetInv_comp a hW hslit j
  have h2 : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I))))
        (expJetInv a (W x)) j) V :=
    fun j => contDiffOn_affJetScalar_comp (A := fun x j => expJetInv a (W x) j) h1 _ _ j
  have h2ne : ∀ x ∈ V,
      affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I)))) (expJetInv a (W x)) 0 ≠ 0 :=
    fun x hx => chiJetPivot_ne_zero (hpole x hx)
  have h3 : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => invJetScalar (affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I))))
        (expJetInv a (W x))) j) V :=
    fun j => contDiffOn_invJetScalar_comp
      (A := fun x j => affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I))))
        (expJetInv a (W x)) j) h2 h2ne j
  exact contDiffOn_affJetScalar_comp
    (A := fun x j => invJetScalar (affJetScalar (-(2 * Complex.I))⁻¹
      (-(1 / (-(2 * Complex.I)))) (expJetInv a (W x))) j) h3 _ _ k

end

end GaloisForLFunctions.HTGeometry
