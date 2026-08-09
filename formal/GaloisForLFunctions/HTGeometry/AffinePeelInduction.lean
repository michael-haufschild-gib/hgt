import GaloisForLFunctions.HTGeometry.AffinePeelInvariant

/-!
# The affine peel, iterated down the flag

Every hypothesis of the peel step is reproduced by the peel step, so the step can be chained.  The
induction bottoms out at a `1×1` determinant, whose single entry is the border entry up to a
degree-`−2` correction and is therefore nonzero.

Hence the orbit determinant of the border row of a rational affine family is nonzero at every
height, provided the leading coefficient of each equation has nonnegative degree at infinity.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace RatAffineFam

variable (R : RatAffineFam)

/-- **A rational head border row converges to the border row one level down.** -/
theorem topLim_headBorder_rat {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (n l : ℕ) :
    TopLim (n + 1)
      (R.toAffineFam.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) l)
      (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead n) n l) := by
  by_cases hl : l ≤ n
  · rw [R.toAffineFam.headBorder_ratFact_of_ne g₁ g₂ (by omega : l ≠ n + 1)]
    exact R.toAffineFam.topLim_logBorder hl
  · by_cases hl2 : l = n + 1
    · subst hl2
      rw [R.toAffineFam.toPairFam.headBorder_of_ne
          (R.toAffineFam.lead_mem_coordField (le_refl n)) (by omega : n < n + 1),
        TopLim, sub_zero]
      exact R.toAffineFam.topDegLE_headBorder_top hg₁ hg₂ n
    · rw [R.toAffineFam.toPairFam.headBorder_of_ne
          (ratFact_mem_coordField (le_refl (n + 1)) g₁ g₂) (by omega : n + 1 < l),
        R.toAffineFam.toPairFam.headBorder_of_ne
          (R.toAffineFam.lead_mem_coordField (le_refl n)) (by omega : n < l)]
      exact topLim_const

/-! ## The induction's hypothesis package -/

/-- The data the peel consumes and reproduces. -/
structure PeelHyp (R : RatAffineFam) (m' : ℕ) (g₁ g₂ : Polynomial ℂ) (u : ℕ → CascadeField) :
    Prop where
  mem : ∀ l, u l ∈ coordField (m' + 1)
  vanish : ∀ l, m' + 1 < l → u l = 0
  shape : R.toAffineFam.BorderShape g₁ g₂ (m' + 1) u
  lim : ∀ l, TopLim (m' + 1) (u l)
    (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead m') m' l)

/-- A rational head border row satisfies the package. -/
theorem peelHyp_headBorder {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (m' : ℕ) :
    R.PeelHyp m' g₁ g₂
      (R.toAffineFam.toPairFam.headBorder (ratFact g₁ g₂ (m' + 1)) (m' + 1)) :=
  ⟨fun l => R.toAffineFam.toPairFam.headBorder_mem_coordField
      (ratFact_mem_coordField (le_refl (m' + 1)) g₁ g₂) l,
    fun _ hl => R.toAffineFam.toPairFam.headBorder_of_ne
      (ratFact_mem_coordField (le_refl (m' + 1)) g₁ g₂) hl,
    R.toAffineFam.borderShape_headBorder g₁ g₂ (m' + 1),
    fun l => R.topLim_headBorder_rat hg₁ hg₂ m' l⟩

/-! ## The induction -/

/-- **The orbit determinant of a peel-shaped vector is nonzero, at every level.** -/
theorem det_orbitMatrix_ne_zero_of_peelHyp
    (hdeg : ∀ j, (R.ld j).natDegree ≤ (R.ln j).natDegree) :
    ∀ (m' : ℕ) (g₁ g₂ : Polynomial ℂ), g₁ ≠ 0 → g₂ ≠ 0 →
      ((g₁.natDegree : ℤ) - (g₂.natDegree : ℤ)) ≠ -1 →
      ∀ u : ℕ → CascadeField, R.PeelHyp m' g₁ g₂ u →
        (R.toAffineFam.toPairFam.orbitMatrix (m' + 1) (m' + 1) u).det ≠ 0 := by
  have hresj : ∀ j, ((R.ln j).natDegree : ℤ) - ((R.ld j).natDegree : ℤ) ≠ -1 := by
    intro j
    have := hdeg j
    omega
  intro m'
  induction m' with
  | zero =>
      intro g₁ g₂ hg₁ hg₂ hres u hu
      rw [PairFam.orbitMatrix, Matrix.det_fin_one]
      simpa using R.toAffineFam.ne_zero_of_borderShape hg₁ hg₂ hres hu.shape
  | succ n ih =>
      intro g₁ g₂ hg₁ hg₂ hres u hu
      refine R.toAffineFam.det_orbitMatrix_ne_zero_of_peel hg₁ hg₂ hres hu.mem hu.vanish
        (fun l => R.toAffineFam.toPairFam.headBorder_mem_coordField
          (R.toAffineFam.lead_mem_coordField (le_refl (n + 1))) l) hu.lim hu.shape ?_
      have hcne : R.peelScale g₁ g₂ (n + 1) ≠ 0 := R.peelScale_ne_zero hres (n + 1)
      have hhyp : R.PeelHyp n (R.ln (n + 1)) (R.ld (n + 1))
          (fun l => (R.peelScale g₁ g₂ (n + 1))⁻¹
            * R.toAffineFam.limVec (n + 1)
                (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1))
                (AffineFam.peelRes g₁ g₂) 1 l) :=
        ⟨fun l => mul_mem (R.inv_peelScale_mem_coordField g₁ g₂ (le_refl (n + 1)))
            (R.toAffineFam.limVec_mem_coordField
              (fun l' => R.toAffineFam.toPairFam.headBorder_mem_coordField
                (R.toAffineFam.lead_mem_coordField (le_refl (n + 1))) l')
              (fun i => AffineFam.peelRes_mem_coordField g₁ g₂ (n + 1) i) 1 l),
          fun l hl => by
            rw [R.toAffineFam.limVec_succ_of_gt (n + 1)
              (R.toAffineFam.toPairFam.headBorder (R.toAffineFam.lead (n + 1)) (n + 1))
              (AffineFam.peelRes g₁ g₂) 0 l (by omega), mul_zero],
          R.borderShape_rescaled g₁ g₂ n hres (hdeg (n + 1)),
          fun l => R.topLim_rescaled_limVec g₁ g₂ n hres (hdeg (n + 1)) l⟩
      have hscaled := ih (R.ln (n + 1)) (R.ld (n + 1)) (R.ln_ne_zero (n + 1))
        (R.ld_ne_zero (n + 1)) (hresj (n + 1)) _ hhyp
      rw [R.toAffineFam.toPairFam.det_orbitMatrix_smul (n + 1) (n + 1)
        (R.peelScale g₁ g₂ (n + 1))⁻¹ _] at hscaled
      exact fun h0 => hscaled (by rw [h0, mul_zero])

/-- **The border row's orbit determinant is nonzero at every height.** -/
theorem det_orbitMatrix_logBorder_ne_zero
    (hdeg : ∀ j, (R.ld j).natDegree ≤ (R.ln j).natDegree) (n : ℕ) :
    (R.toAffineFam.toPairFam.orbitMatrix (n + 1) (n + 1)
      (R.toAffineFam.toPairFam.logBorder (n + 1))).det ≠ 0 := by
  have hone : ratFact (1 : Polynomial ℂ) (1 : Polynomial ℂ) (n + 1) = 1 := by
    rw [ratFact, fact, univFactor, map_one, map_one, div_one]
  have hb : R.toAffineFam.toPairFam.headBorder
      (ratFact (1 : Polynomial ℂ) (1 : Polynomial ℂ) (n + 1)) (n + 1)
      = R.toAffineFam.toPairFam.logBorder (n + 1) := by
    funext l
    rw [PairFam.headBorder, hone, (fpderiv l).map_one_eq_zero, zero_div, add_zero]
  rw [← hb]
  refine R.det_orbitMatrix_ne_zero_of_peelHyp hdeg n 1 1 one_ne_zero one_ne_zero ?_ _
    (R.peelHyp_headBorder one_ne_zero one_ne_zero n)
  rw [Polynomial.natDegree_one]
  omega

end RatAffineFam

end GaloisForLFunctions.HTGeometry
