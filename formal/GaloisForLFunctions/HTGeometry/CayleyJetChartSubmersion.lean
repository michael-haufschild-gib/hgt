import GaloisForLFunctions.HTGeometry.ExponentialJetInverseSmoothness

/-!
# The Cayley outer jet chart is a submersion

The chart is the composite of two affine jet maps, the reciprocal jet map and the exponential jet
map.  The affine maps are invertible outright, the reciprocal map is an involution, and the
exponential map has the logarithmic branch inverse, so the composite has an explicit local inverse.

Both the chart and its inverse are smooth, so the chart's derivative is surjective at every packet
whose zeroth entry avoids `-i`.  This is the submersion input a parametric transversality argument
needs, and it is strictly stronger than openness.
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

/-- The Cayley coefficient: the inverse of the Möbius scale `-(2i)`. -/
def cayleyScaleInv : ℂ := (-(2 * Complex.I))⁻¹

theorem neg_two_I_ne_zero : (-(2 * Complex.I)) ≠ 0 := by
  simp [Complex.I_ne_zero]

theorem cayleyScaleInv_ne_zero : cayleyScaleInv ≠ 0 :=
  inv_ne_zero neg_two_I_ne_zero

theorem neg_two_I_mul_cayleyScaleInv : (-(2 * Complex.I)) * cayleyScaleInv = 1 :=
  mul_inv_cancel₀ neg_two_I_ne_zero

/-- The local inverse of the Cayley outer jet chart, through the logarithmic branch at `a`. -/
def chiJetInv (a : ℂ) (w : ℕ → ℂ) : ℕ → ℂ :=
  affJetScalar 1 (-Complex.I)
    (invJetScalar (affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a w)))

theorem chiJetInv_congr (a : ℂ) {w w' : ℕ → ℂ} {k : ℕ} (h : ∀ j, j ≤ k → w j = w' j) :
    chiJetInv a w k = chiJetInv a w' k := by
  have hbase : ∀ j, j ≤ k →
      affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a w) j
      = affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a w') j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp only [affJetScalar, expJetInv_congr a (k := 0) fun i hi => h i (by omega)]
    · simp only [affJetScalar, if_neg hj0, expJetInv_congr a (k := j) fun i hi => h i (by omega)]
  have hinv : ∀ j, j ≤ k →
      invJetScalar (affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a w)) j
      = invJetScalar (affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a w')) j := by
    intro j hj
    exact invJetScalar_congr (K := j) (fun i hi => hbase i (by omega)) j (le_refl j)
  by_cases hk : k = 0
  · subst hk
    simp only [chiJetInv, affJetScalar, hinv 0 (le_refl 0)]
  · simp only [chiJetInv, affJetScalar, if_neg hk, hinv k (le_refl k)]

theorem affJetScalar_apply_zero (a b : ℂ) (y : ℕ → ℂ) : affJetScalar a b y 0 = a * y 0 + b := by
  rw [affJetScalar, if_pos rfl]

theorem affJetScalar_apply_ne_zero (a b : ℂ) (y : ℕ → ℂ) {k : ℕ} (hk : k ≠ 0) :
    affJetScalar a b y k = a * y k := by
  rw [affJetScalar, if_neg hk]

/-- **The chart inverse really inverts.**  Every packet whose zeroth entry is nonzero and whose
branch avoids the Möbius pole is the Cayley outer jet packet of its inverse. -/
theorem chiJetScalar_chiJetInv {a : ℂ} {w : ℕ → ℂ} (hw : w 0 ≠ 0)
    (hbranch : logBranch a (w 0) ≠ 1) (k : ℕ) :
    chiJetScalar (chiJetInv a w) k = w k := by
  have hp0 : affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a w) 0 ≠ 0 := by
    rw [affJetScalar_apply_zero]
    have hval : cayleyScaleInv * expJetInv a w 0 + -cayleyScaleInv
        = cayleyScaleInv * (expJetInv a w 0 - 1) := by ring
    rw [hval]
    refine mul_ne_zero cayleyScaleInv_ne_zero (sub_ne_zero.mpr ?_)
    rw [expJetInv_zero]
    exact hbranch
  have hA : (fun m => affJetScalar 1 Complex.I (chiJetInv a w) m)
      = invJetScalar (affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a w)) := by
    funext m
    by_cases hm : m = 0
    · subst hm
      rw [affJetScalar_apply_zero, chiJetInv, affJetScalar_apply_zero]
      ring
    · rw [affJetScalar_apply_ne_zero _ _ _ hm, chiJetInv, affJetScalar_apply_ne_zero _ _ _ hm]
      ring
  have hB : (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I (chiJetInv a w) m) l)
      = affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a w) := by
    rw [hA]
    funext l
    exact invJetScalar_invJetScalar hp0 l
  have hC : (fun j => affJetScalar (-(2 * Complex.I)) 1
      (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I (chiJetInv a w) m) l) j)
      = expJetInv a w := by
    rw [hB]
    funext j
    by_cases hj : j = 0
    · subst hj
      rw [affJetScalar_apply_zero, affJetScalar_apply_zero]
      linear_combination (expJetInv a w 0 - 1) * neg_two_I_mul_cayleyScaleInv
    · rw [affJetScalar_apply_ne_zero _ _ _ hj, affJetScalar_apply_ne_zero _ _ _ hj]
      linear_combination (expJetInv a w j) * neg_two_I_mul_cayleyScaleInv
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
      (fun x => affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a (W x)) j) V :=
    fun j => contDiffOn_affJetScalar_comp
      (A := fun x j => expJetInv a (W x) j) h1 cayleyScaleInv (-cayleyScaleInv) j
  have h2ne : ∀ x ∈ V,
      affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a (W x)) 0 ≠ 0 := by
    intro x hx
    have hval : affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a (W x)) 0
        = cayleyScaleInv * (expJetInv a (W x) 0 - 1) := by
      rw [affJetScalar, if_pos rfl]
      ring
    rw [hval]
    refine mul_ne_zero cayleyScaleInv_ne_zero (sub_ne_zero.mpr ?_)
    rw [expJetInv_zero]
    exact hpole x hx
  have h3 : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => invJetScalar
        (affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a (W x))) j) V :=
    fun j => contDiffOn_invJetScalar_comp
      (A := fun x j => affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a (W x)) j)
      h2 h2ne j
  exact contDiffOn_affJetScalar_comp
    (A := fun x j => invJetScalar
      (affJetScalar cayleyScaleInv (-cayleyScaleInv) (expJetInv a (W x))) j) h3 1 (-Complex.I) k

end

end GaloisForLFunctions.HTGeometry
