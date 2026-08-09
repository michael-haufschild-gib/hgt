import GaloisForLFunctions.HTGeometry.PairPeelInvariant

/-!
# The peel, iterated down the flag

Every hypothesis of the peel step is reproduced by the peel step, so the step can be chained.  The
induction bottoms out at a `1×1` determinant, whose single entry is the border entry up to a
degree-`−2` correction and is therefore nonzero: its scaled value at infinity is `1 + deg g`, a
positive integer.

Hence the logarithmic Jacobian of a linear first-order cascade is nonsingular at every height.  This
is the two-coordinate law's unit-cost statement: the states of a cascade built from
`h' = a(z)·h + b(z)` with `a ≠ 0` have algebraically independent jets at every length.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ}

/-! ## The induction's hypothesis package -/

/-- The data the peel consumes and reproduces. -/
structure PairPeelHyp (p : ℕ → MvPolynomial (Fin 2) ℂ) (a : ℕ → Polynomial ℂ) (m' : ℕ)
    (g : Polynomial ℂ) (u : ℕ → CascadeField) : Prop where
  mem : ∀ l, u l ∈ coordField (m' + 1)
  vanish : ∀ l, m' + 1 < l → u l = 0
  shape : PairBorderShape p g (m' + 1) u
  lim : ∀ l, TopLim (m' + 1) (u l) (headBorder p (a m') m' l)

/-- A border row with any head satisfies the package. -/
theorem pairPeelHyp_headBorder (a b : ℕ → Polynomial ℂ)
    (hp : ∀ j, p j = affinePair (a j) (b j)) (ha : ∀ j, a j ≠ 0) (m' : ℕ) (g : Polynomial ℂ) :
    PairPeelHyp p a m' g (headBorder p g (m' + 1)) where
  mem := fun l => headBorder_mem_coordField g (m' + 1) l
  vanish := fun l hl => headBorder_eq_zero_of_gt (by omega)
  shape := pairBorderShape_headBorder p g (m' + 1)
  lim := fun l => topLim_headBorder (ha m') (hp m') g l

/-! ## The induction -/

/-- **The orbit determinant of a peel-shaped vector is nonzero, at every level.** -/
theorem det_pairOrbitMatrix_ne_zero_of_peelHyp (a b : ℕ → Polynomial ℂ)
    (hp : ∀ j, p j = affinePair (a j) (b j)) (ha : ∀ j, a j ≠ 0) :
    ∀ (m' : ℕ) (g : Polynomial ℂ), g ≠ 0 → ∀ u : ℕ → CascadeField, PairPeelHyp p a m' g u →
      (pairOrbitMatrix p (m' + 1) (m' + 1) u).det ≠ 0 := by
  have hne : ∀ j, pairFactor (p j) j ≠ 0 := by
    intro j
    rw [hp j]
    exact pairFactor_affinePair_ne_zero (ha j) (b j) j
  intro m'
  induction m' with
  | zero =>
      intro g _ u hu
      rw [pairOrbitMatrix, Matrix.det_fin_one]
      simpa using ne_zero_of_pairBorderShape (ha 0) g (hp 0) hu.shape
  | succ n ih =>
      intro g hg u hu
      refine det_pairOrbitMatrix_ne_zero_of_peel (ha (n + 1)) hg (hp (n + 1)) hne hu.mem
        hu.vanish (fun l => headBorder_mem_coordField (a (n + 1)) (n + 1) l) hu.lim hu.shape ?_
      have hcne : pairPeelScale p (a (n + 1)) g (n + 1) ≠ 0 :=
        pairPeelScale_ne_zero (ha (n + 1)) g hne (n + 1)
      have hhyp : PairPeelHyp p a n (a (n + 1))
          (fun l => (pairPeelScale p (a (n + 1)) g (n + 1))⁻¹
            * pairLimVec p (a (n + 1)) (n + 1) (headBorder p (a (n + 1)) (n + 1))
                (pairPeelRes g) 1 l) :=
        ⟨fun l => mul_mem
            (inv_pairPeelScale_mem_coordField (a (n + 1)) g (n + 1) (le_refl (n + 1)))
            (pairLimVec_mem_coordField
              (fun l' => headBorder_mem_coordField (a (n + 1)) (n + 1) l')
              (fun i => pairPeelRes_mem_coordField g (n + 1) i) 1 l),
          fun l hl => by
            rw [pairLimVec_succ_of_gt p (a (n + 1)) (n + 1) (headBorder p (a (n + 1)) (n + 1))
              (pairPeelRes g) 0 l (by omega), mul_zero],
          pairBorderShape_rescaled (ha (n + 1)) (ha n) (hp n) g hne,
          fun l => topLim_rescaled_pairLimVec (ha (n + 1)) (ha n) (hp n) g hne l⟩
      have hscaled := ih (a (n + 1)) (ha (n + 1)) _ hhyp
      rw [det_pairOrbitMatrix_smul p (n + 1) (n + 1)
        (pairPeelScale p (a (n + 1)) g (n + 1))⁻¹ _] at hscaled
      exact fun h0 => hscaled (by rw [h0, mul_zero])

/-! ## The Jacobian of the jets of the logarithm -/

/-- The Jacobian of the jets of `∑_(j ≤ n) log p_j`: border row `∂_(j+1) L`, remaining rows
`∂_(j+1) δ^r (δL)`. -/
noncomputable def pairLogJetJacobian (p : ℕ → MvPolynomial (Fin 2) ℂ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) CascadeField :=
  Matrix.of fun i j =>
    Fin.cases (pairLogBorder p (n + 1) ((j : ℕ) + 1))
      (fun r : Fin n => fpderiv ((j : ℕ) + 1)
        (((pairDerivation p : CascadeField → CascadeField)^[(r : ℕ)])
          (pairLogSum p (n + 1)))) i

theorem headBorder_one_eq (p : ℕ → MvPolynomial (Fin 2) ℂ) (m : ℕ) :
    headBorder p 1 m = pairLogBorder p m := by
  funext l
  exact headBorder_one m l

theorem headSum_one_eq (p : ℕ → MvPolynomial (Fin 2) ℂ) (m : ℕ) :
    headSum p 1 m = pairLogSum p m := by
  rw [headSum, pairLogSum]
  exact Finset.sum_congr rfl fun l _ => by rw [headBorder_one]

/-- **The Jacobian is the orbit matrix of the border row.** -/
theorem pairLogJetJacobian_eq_orbit (p : ℕ → MvPolynomial (Fin 2) ℂ) (n : ℕ) :
    pairLogJetJacobian p n = pairOrbitMatrix p (n + 1) (n + 1) (pairLogBorder p (n + 1)) := by
  funext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · simp only [pairLogJetJacobian, Matrix.of_apply, Fin.cases_zero, pairOrbitMatrix,
      Fin.val_zero, Function.iterate_zero, id_eq]
  · have hgrad := gradient_iterate_headSum (p := p) 1 (n + 1) (r : ℕ)
    rw [headSum_one_eq, headBorder_one_eq] at hgrad
    have hval := congrArg (fun F : ℕ → CascadeField => F ((j : ℕ) + 1)) hgrad
    simp only [pairLogJetJacobian, Matrix.of_apply, Fin.cases_succ, pairOrbitMatrix,
      Fin.val_succ]
    exact hval

/-! ## The capstone -/

/-- **The logarithmic Jacobian of a linear first-order cascade is nonsingular at every height.** -/
theorem pairLogJetJacobian_det_ne_zero (a b : ℕ → Polynomial ℂ)
    (hp : ∀ j, p j = affinePair (a j) (b j)) (ha : ∀ j, a j ≠ 0) (n : ℕ) :
    (pairLogJetJacobian p n).det ≠ 0 := by
  rw [pairLogJetJacobian_eq_orbit, ← headBorder_one_eq]
  exact det_pairOrbitMatrix_ne_zero_of_peelHyp a b hp ha n 1 one_ne_zero _
    (pairPeelHyp_headBorder a b hp ha n 1)

end GaloisForLFunctions.HTGeometry
