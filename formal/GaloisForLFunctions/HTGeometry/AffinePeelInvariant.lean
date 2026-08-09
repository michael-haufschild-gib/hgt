import GaloisForLFunctions.HTGeometry.AffinePeelStep

/-!
# The rational affine family, and the peel's invariant

A first-order linear equation with rational coefficients gives an affine factor family whose
coefficients are ratios of univariate factors.  The head the peel creates one level down is then the
leading coefficient of the factor there, which is again such a ratio — so the class is closed.

Two degree conditions appear, and for rational coefficients they are the same one.  The residue at
the border is `1 + deg ln − deg ld`, which must not vanish; and the rescaling factor's inverse must
not raise a degree, which needs `deg ln ≥ deg ld`.  The second implies the first, and it is
automatic for polynomial coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- An affine factor family with rational coefficients. -/
structure RatAffineFam where
  /-- Numerator of the leading coefficient at level `j`. -/
  ln : ℕ → Polynomial ℂ
  /-- Denominator of the leading coefficient at level `j`. -/
  ld : ℕ → Polynomial ℂ
  /-- Numerator of the constant term at level `j`. -/
  cn : ℕ → Polynomial ℂ
  /-- Denominator of the constant term at level `j`. -/
  cd : ℕ → Polynomial ℂ
  ln_ne_zero : ∀ j, ln j ≠ 0
  ld_ne_zero : ∀ j, ld j ≠ 0
  cd_ne_zero : ∀ j, cd j ≠ 0

namespace RatAffineFam

variable (R : RatAffineFam)

/-- The affine factor family it determines. -/
noncomputable def toAffineFam : AffineFam where
  lead j := ratFact (R.ln j) (R.ld j) j
  cnst j := ratFact (R.cn j) (R.cd j) j
  lead_ne_zero j := ratFact_ne_zero (R.ln_ne_zero j) (R.ld_ne_zero j) j
  fpderiv_lead h := fpderiv_ratFact_of_ne (Ne.symm h)
  fpderiv_cnst h := fpderiv_ratFact_of_ne (Ne.symm h)

@[simp] theorem lead_eq (j : ℕ) : R.toAffineFam.lead j = ratFact (R.ln j) (R.ld j) j := rfl

@[simp] theorem cnst_eq (j : ℕ) : R.toAffineFam.cnst j = ratFact (R.cn j) (R.cd j) j := rfl

/-! ## The rescaling factor -/

/-- The factor that restores the shape of the peeled vector. -/
noncomputable def peelScale (g₁ g₂ : Polynomial ℂ) (m : ℕ) : CascadeField :=
  R.toAffineFam.toPairFam.jet m * R.toAffineFam.lead m * AffineFam.peelRes g₁ g₂ 0

theorem peelRes_zero_ne_zero {g₁ g₂ : Polynomial ℂ}
    (hres : ((g₁.natDegree : ℤ) - (g₂.natDegree : ℤ)) ≠ -1) :
    AffineFam.peelRes g₁ g₂ 0 ≠ 0 := by
  show algebraMap ℂ CascadeField (1 + (g₁.natDegree : ℂ) - (g₂.natDegree : ℂ)) ≠ 0
  exact (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr
    (AffineFam.residue_ne_zero hres)

theorem peelScale_ne_zero {g₁ g₂ : Polynomial ℂ}
    (hres : ((g₁.natDegree : ℤ) - (g₂.natDegree : ℤ)) ≠ -1) (m : ℕ) :
    R.peelScale g₁ g₂ m ≠ 0 :=
  mul_ne_zero (mul_ne_zero (R.toAffineFam.toPairFam.jet_ne_zero m)
    (R.toAffineFam.lead_ne_zero m)) (peelRes_zero_ne_zero hres)

theorem inv_peelScale_mem_coordField (g₁ g₂ : Polynomial ℂ) {m m' : ℕ} (h : m' ≤ m) :
    (R.peelScale g₁ g₂ m')⁻¹ ∈ coordField m := by
  rw [peelScale]
  refine inv_mem (mul_mem (mul_mem (R.toAffineFam.toPairFam.jet_mem_coordField h) ?_) ?_)
  · exact R.toAffineFam.lead_mem_coordField h
  · exact AffineFam.peelRes_mem_coordField g₁ g₂ m 0

/-- **The rescaling factor's inverse drops a degree**, given `deg ln ≥ deg ld`. -/
theorem topDegLE_inv_peelScale (g₁ g₂ : Polynomial ℂ) (n : ℕ)
    (hdeg : (R.ld (n + 1)).natDegree ≤ (R.ln (n + 1)).natDegree) :
    TopDegLE (n + 1) (-1) ((R.peelScale g₁ g₂ (n + 1))⁻¹) := by
  rw [peelScale, mul_inv, mul_inv, R.toAffineFam.jet_succ_eq n, mul_inv]
  have h1 : TopFree (n + 1) ((R.toAffineFam.toPairFam.jet n)⁻¹) :=
    TopFree.inv (R.toAffineFam.topFree_jet_top (by omega))
  have h2 : TopDegLE (n + 1) (-1) ((R.toAffineFam.fac n)⁻¹) := R.toAffineFam.topDegLE_inv_fac n
  have h3 : TopDegLE (n + 1) (((R.ld (n + 1)).natDegree : ℤ) - (R.ln (n + 1)).natDegree)
      ((R.toAffineFam.lead (n + 1))⁻¹) := by
    rw [lead_eq]
    exact topDegLE_inv_ratFact (n + 1) (R.ln_ne_zero (n + 1))
  have h4 : TopFree (n + 1) ((AffineFam.peelRes g₁ g₂ 0)⁻¹) := by
    show TopFree (n + 1)
      ((algebraMap ℂ CascadeField (1 + (g₁.natDegree : ℂ) - (g₂.natDegree : ℂ)))⁻¹)
    rw [← map_inv₀]
    exact topFree_algebraMap_complex (n + 1) _
  have hmul := TopDegLE.mul (TopDegLE.mul (TopDegLE.mul h1.topDegLE h2) h3) h4.topDegLE
  refine TopDegLE.mono ?_ hmul
  have : ((R.ld (n + 1)).natDegree : ℤ) ≤ ((R.ln (n + 1)).natDegree : ℤ) := by exact_mod_cast hdeg
  omega

/-! ## Degrees on a border row -/

theorem topDegLE_logBorder_zero (n : ℕ) {k : ℕ} (hk : k ≤ n) :
    TopDegLE (n + 1) 0 (R.toAffineFam.toPairFam.logBorder (n + 1) k) :=
  TopLim.topDegLE_zero
    (topFree_of_mem_coordField (by omega)
      (R.toAffineFam.toPairFam.headBorder_mem_coordField
        (R.toAffineFam.lead_mem_coordField (le_refl n)) k))
    (R.toAffineFam.topLim_logBorder hk)

/-- **The shifted operator keeps degree zero away from the newest coordinate.** -/
theorem topDegLE_gradShift_zero (n : ℕ) {k : ℕ} (hk : k < n + 1) {u : ℕ → CascadeField}
    (hmem : ∀ l, u l ∈ coordField (n + 1))
    (hlow : ∀ l, l < n + 1 → TopDegLE (n + 1) 0 (u l))
    (htop : TopDegLE (n + 1) (-1) (u (n + 1))) :
    TopDegLE (n + 1) 0 (R.toAffineFam.toPairFam.gradShift (n + 1) u k) := by
  rw [PairFam.gradShift]
  refine TopDegLE.add (R.toAffineFam.topDegLE_law (hmem k) (hlow k hk)) ?_
  refine topDegLE_sum _ _ fun l hl => ?_
  have hlm : l ≤ n + 1 := by
    have := Finset.mem_range.mp hl
    omega
  rcases eq_or_lt_of_le hlm with rfl | hlt
  · rw [R.toAffineFam.toPairFam.response_eq_logBorder k (n + 1), mul_assoc]
    have hmul := TopDegLE.mul (R.topDegLE_logBorder_zero n (by omega : k ≤ n))
      (TopDegLE.mul (R.toAffineFam.topDegLE_jet_top n) htop)
    refine TopDegLE.mono ?_ hmul
    omega
  · have hfree : TopFree (n + 1) (R.toAffineFam.toPairFam.response k l) :=
      topFree_of_mem_coordField hlt
        (R.toAffineFam.toPairFam.response_mem_coordField (le_refl l))
    have hmul := TopDegLE.mul hfree.topDegLE (hlow l hlt)
    refine TopDegLE.mono ?_ hmul
    omega

/-! ## The rescaled vector -/

theorem limVec_one_rescaled (g₁ g₂ : Polynomial ℂ) (n : ℕ) {L : ℕ → CascadeField} {l : ℕ}
    (hl : l ≤ n + 1) (hc : R.peelScale g₁ g₂ (n + 1) ≠ 0) :
    (R.peelScale g₁ g₂ (n + 1))⁻¹
        * R.toAffineFam.limVec (n + 1) L (AffineFam.peelRes g₁ g₂) 1 l
      = (R.peelScale g₁ g₂ (n + 1))⁻¹
          * R.toAffineFam.toPairFam.gradShift (n + 1) L l
        + R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1) l := by
  rw [R.toAffineFam.limVec_succ_of_le (n + 1) L (AffineFam.peelRes g₁ g₂) 0 l hl,
    R.toAffineFam.limVec_zero, mul_add]
  congr 1
  rw [show R.toAffineFam.toPairFam.jet (n + 1) * R.toAffineFam.lead (n + 1)
      * AffineFam.peelRes g₁ g₂ 0 = R.peelScale g₁ g₂ (n + 1) from rfl, ← mul_assoc,
    mul_comm ((R.peelScale g₁ g₂ (n + 1))⁻¹)
      (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1) l),
    mul_assoc, inv_mul_cancel₀ hc, mul_one]

/-- **The peel restores the shape.** -/
theorem borderShape_rescaled (g₁ g₂ : Polynomial ℂ) (n : ℕ)
    (hres : ((g₁.natDegree : ℤ) - (g₂.natDegree : ℤ)) ≠ -1)
    (hdeg : (R.ld (n + 1)).natDegree ≤ (R.ln (n + 1)).natDegree) :
    R.toAffineFam.BorderShape (R.ln (n + 1)) (R.ld (n + 1)) (n + 1)
      (fun l => (R.peelScale g₁ g₂ (n + 1))⁻¹
        * R.toAffineFam.limVec (n + 1)
            (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1))
            (AffineFam.peelRes g₁ g₂) 1 l) := by
  have hc : R.peelScale g₁ g₂ (n + 1) ≠ 0 := R.peelScale_ne_zero hres (n + 1)
  rw [AffineFam.BorderShape, R.limVec_one_rescaled g₁ g₂ n (le_refl (n + 1)) hc,
    ← R.lead_eq (n + 1), add_sub_cancel_right, R.toAffineFam.toPairFam.gradShift_top]
  have h1 : TopDegLE (n + 1) (-2)
      (R.toAffineFam.toPairFam.topShift (n + 1)
        (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1) (n + 1))) := by
    rw [R.lead_eq (n + 1)]
    exact R.toAffineFam.topDegLE_topShift_headBorder (R.ln_ne_zero (n + 1))
      (R.ld_ne_zero (n + 1)) n
  have h2 : TopDegLE (n + 1) 0 ((R.peelScale g₁ g₂ (n + 1))⁻¹) :=
    TopDegLE.mono (by norm_num) (R.topDegLE_inv_peelScale g₁ g₂ n hdeg)
  have hmul := TopDegLE.mul h2 h1
  refine TopDegLE.mono ?_ hmul
  omega

/-! ## The border row's own limit -/

/-- **The border row converges to the border row one level down.** -/
theorem topLim_headBorder (n l : ℕ) :
    TopLim (n + 1)
      (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1) l)
      (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead n) n l) := by
  by_cases hl : l ≤ n
  · rw [PairFam.headBorder, R.toAffineFam.fpderiv_lead (by omega : l ≠ n + 1), zero_div,
      add_zero]
    exact R.toAffineFam.topLim_logBorder hl
  · by_cases hl2 : l = n + 1
    · subst hl2
      rw [R.toAffineFam.toPairFam.headBorder_of_ne
          (R.toAffineFam.lead_mem_coordField (le_refl n)) (by omega : n < n + 1),
        TopLim, sub_zero, R.lead_eq (n + 1)]
      exact R.toAffineFam.topDegLE_headBorder_top (R.ln_ne_zero (n + 1)) (R.ld_ne_zero (n + 1)) n
    · rw [R.toAffineFam.toPairFam.headBorder_of_ne
          (R.toAffineFam.lead_mem_coordField (le_refl (n + 1))) (by omega : n + 1 < l),
        R.toAffineFam.toPairFam.headBorder_of_ne
          (R.toAffineFam.lead_mem_coordField (le_refl n)) (by omega : n < l)]
      exact topLim_const

/-- **The rescaled peeled vector converges to the border row one level down.** -/
theorem topLim_rescaled_limVec (g₁ g₂ : Polynomial ℂ) (n : ℕ)
    (hres : ((g₁.natDegree : ℤ) - (g₂.natDegree : ℤ)) ≠ -1)
    (hdeg : (R.ld (n + 1)).natDegree ≤ (R.ln (n + 1)).natDegree) (l : ℕ) :
    TopLim (n + 1)
      ((R.peelScale g₁ g₂ (n + 1))⁻¹
        * R.toAffineFam.limVec (n + 1)
            (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1))
            (AffineFam.peelRes g₁ g₂) 1 l)
      (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead n) n l) := by
  have hc : R.peelScale g₁ g₂ (n + 1) ≠ 0 := R.peelScale_ne_zero hres (n + 1)
  by_cases hl : l ≤ n
  · rw [R.limVec_one_rescaled g₁ g₂ n (by omega : l ≤ n + 1) hc]
    have hgs : TopDegLE (n + 1) 0
        (R.toAffineFam.toPairFam.gradShift (n + 1)
          (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1)) l) := by
      refine R.topDegLE_gradShift_zero n (by omega)
        (fun l' => R.toAffineFam.toPairFam.headBorder_mem_coordField
          (R.toAffineFam.lead_mem_coordField (le_refl (n + 1))) l')
        (fun l' hl' => ?_) ?_
      · rw [PairFam.headBorder, R.toAffineFam.fpderiv_lead (by omega : l' ≠ n + 1), zero_div,
          add_zero]
        exact R.topDegLE_logBorder_zero n (by omega)
      · rw [R.lead_eq (n + 1)]
        exact R.toAffineFam.topDegLE_headBorder_top (R.ln_ne_zero (n + 1))
          (R.ld_ne_zero (n + 1)) n
    have hdrop : TopLim (n + 1)
        ((R.peelScale g₁ g₂ (n + 1))⁻¹
          * R.toAffineFam.toPairFam.gradShift (n + 1)
              (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1)) l) 0 := by
      rw [TopLim, sub_zero]
      have := TopDegLE.mul (R.topDegLE_inv_peelScale g₁ g₂ n hdeg) hgs
      simpa using this
    have hsum := TopLim.add hdrop (R.topLim_headBorder n l)
    rw [zero_add] at hsum
    exact hsum
  · by_cases hl2 : l = n + 1
    · subst hl2
      rw [R.toAffineFam.toPairFam.headBorder_of_ne
          (R.toAffineFam.lead_mem_coordField (le_refl n)) (by omega : n < n + 1),
        TopLim, sub_zero]
      have hshape := R.borderShape_rescaled g₁ g₂ n hres hdeg
      rw [AffineFam.BorderShape] at hshape
      have hsplit : (R.peelScale g₁ g₂ (n + 1))⁻¹
            * R.toAffineFam.limVec (n + 1)
                (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1))
                (AffineFam.peelRes g₁ g₂) 1 (n + 1)
          = ((R.peelScale g₁ g₂ (n + 1))⁻¹
              * R.toAffineFam.limVec (n + 1)
                  (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1))
                  (AffineFam.peelRes g₁ g₂) 1 (n + 1)
              - R.toAffineFam.toPairFam.headBorder
                  (ratFact (R.ln (n + 1)) (R.ld (n + 1)) (n + 1)) (n + 1) (n + 1))
            + R.toAffineFam.toPairFam.headBorder
                (ratFact (R.ln (n + 1)) (R.ld (n + 1)) (n + 1)) (n + 1) (n + 1) := by
        ring
      rw [hsplit]
      exact TopDegLE.add (TopDegLE.mono (by norm_num) hshape)
        (R.toAffineFam.topDegLE_headBorder_top (R.ln_ne_zero (n + 1)) (R.ld_ne_zero (n + 1)) n)
    · rw [R.toAffineFam.limVec_succ_of_gt (n + 1)
        (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1))
        (AffineFam.peelRes g₁ g₂) 0 l (by omega), mul_zero,
        R.toAffineFam.toPairFam.headBorder_of_ne
          (R.toAffineFam.lead_mem_coordField (le_refl n)) (by omega : n < l)]
      exact topLim_const

end RatAffineFam

end GaloisForLFunctions.HTGeometry
