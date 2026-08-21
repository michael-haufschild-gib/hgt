import GaloisForLFunctions.HTGeometry.BorelWeil.CellCoordinates

/-!
# The Weyl group acting on the flag localization

Left translation by a permutation matrix permutes the Bruhat cells: it carries the cell equation of
`σ` to that of `w⁻¹σ`, hence fixes the product of all of them.  So it extends to a ring
automorphism of the flag localization which commutes with the right Borel translation, preserves
each weight space, and permutes the denominator bounds.  This transports every statement about the
identity cell — in particular the chart description of its sections — to an arbitrary Bruhat cell.

## Main definitions

* `permMat`, `weylSubst`

## Main results

* `substLeft_minorPolyAt` — the cell minors are permuted.
* `weylSubst_mem_cellSections` — the cells are permuted.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- The permutation matrix of `w`. -/
noncomputable def permMat (w : Equiv.Perm (Fin N)) (k : Type*) [Field k] :
    Matrix (Fin N) (Fin N) k :=
  permWitness w k

theorem permMat_mul (w : Equiv.Perm (Fin N)) (g : Matrix (Fin N) (Fin N) k) :
    permMat w k * g = g.submatrix (⇑w⁻¹) id := by
  ext r c
  rw [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, permMat, permWitness]
  rw [Finset.sum_eq_single (w⁻¹ r)]
  · simp only [Matrix.of_apply]
    rw [if_pos (by simp), one_mul]
  · intro l _ hl
    simp only [Matrix.of_apply]
    rw [if_neg (fun hc => hl (by rw [hc]; simp)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (w⁻¹ r)) h

theorem substLeft_minorPolyAt (w σ : Equiv.Perm (Fin N)) (j : ℕ) :
    substLeft (permMat w k) (minorPolyAt N k σ j) = minorPolyAt N k (w⁻¹ * σ) j := by
  refine matEval_injective fun g => ?_
  rw [matEval_substLeft, matEval_minorPolyAt, matEval_minorPolyAt, permMat_mul]
  congr 1

theorem substLeft_cellDenomPoly (w σ : Equiv.Perm (Fin N)) :
    substLeft (permMat w k) (cellDenomPoly N k σ) = cellDenomPoly N k (w⁻¹ * σ) := by
  rw [cellDenomPoly, cellDenomPoly, map_prod]
  exact Finset.prod_congr rfl fun j _ => substLeft_minorPolyAt w σ ((j : ℕ) + 1)

theorem substLeft_totalDenom (w : Equiv.Perm (Fin N)) :
    substLeft (permMat w k) (totalDenom N k) = totalDenom N k := by
  have h1 : substLeft (permMat w k) (totalDenom N k)
      = ∏ σ : Equiv.Perm (Fin N), cellDenomPoly N k (w⁻¹ * σ) := by
    rw [totalDenom, map_prod]
    exact Finset.prod_congr rfl fun σ _ => substLeft_cellDenomPoly w σ
  rw [h1, totalDenom]
  exact Equiv.prod_comp (Equiv.mulLeft w⁻¹) fun σ => cellDenomPoly N k σ

theorem substLeft_denomOf (w : Equiv.Perm (Fin N)) (I : Finset (Equiv.Perm (Fin N))) :
    substLeft (permMat w k) (denomOf N k I) = denomOf N k (I.image fun σ => w⁻¹ * σ) := by
  classical
  rw [denomOf, denomOf, map_prod,
    Finset.prod_image (fun a _ b _ hab => by
      have := congrArg (fun τ : Equiv.Perm (Fin N) => w * τ) hab
      simpa [← mul_assoc] using this)]
  exact Finset.prod_congr rfl fun σ _ => substLeft_cellDenomPoly w σ

/-- **The Weyl group acting on the flag localization.** -/
noncomputable def weylSubst (w : Equiv.Perm (Fin N)) : FlagLoc N k →+* FlagLoc N k :=
  IsLocalization.Away.lift (S := FlagLoc N k) (totalDenom N k)
    (g := (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)).comp
      (substLeft (permMat w k)).toRingHom)
    (by
      have hmap : ((algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)).comp
          (substLeft (permMat w k)).toRingHom) (totalDenom N k)
          = algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (totalDenom N k) := by
        rw [RingHom.comp_apply]
        show algebraMap _ _ (substLeft (permMat w k) (totalDenom N k)) = _
        rw [substLeft_totalDenom]
      rw [hmap]
      exact isUnit_algebraMap_totalDenom)

theorem weylSubst_algebraMap (w : Equiv.Perm (Fin N)) (p : MvPolynomial (Fin N × Fin N) k) :
    weylSubst w (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) p)
      = algebraMap _ _ (substLeft (permMat w k) p) := by
  rw [weylSubst, IsLocalization.Away.lift_eq]
  rfl

theorem substLeft_substRight (x B : Matrix (Fin N) (Fin N) k) (p : MvPolynomial (Fin N × Fin N) k) :
    substLeft x (substRight B p) = substRight B (substLeft x p) := by
  refine matEval_injective fun g => ?_
  rw [matEval_substLeft, matEval_substRight, matEval_substRight, matEval_substLeft,
    Matrix.mul_assoc]

theorem weylSubst_substRightAway (w : Equiv.Perm (Fin N)) {B : Matrix (Fin N) (Fin N) k}
    (hB : IsBorelMat B) (x : FlagLoc N k) :
    weylSubst w (substRightAway hB x) = substRightAway hB (weylSubst w x) := by
  have hext : (weylSubst (k := k) w).comp (substRightAway hB)
      = (substRightAway hB).comp (weylSubst (k := k) w) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (totalDenom N k)) (RingHom.ext fun p => ?_)
    show weylSubst w (substRightAway hB (algebraMap _ _ p))
      = substRightAway hB (weylSubst w (algebraMap _ _ p))
    rw [substRightAway_algebraMap, weylSubst_algebraMap, weylSubst_algebraMap,
      substRightAway_algebraMap, substLeft_substRight]
  exact congrFun (congrArg (fun f : FlagLoc N k →+* FlagLoc N k => (f : FlagLoc N k → FlagLoc N k))
    hext) x

theorem weylSubst_smul (w : Equiv.Perm (Fin N)) (c : k) (x : FlagLoc N k) :
    weylSubst w (c • x) = c • weylSubst w x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k),
    weylSubst_algebraMap, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)]

theorem weylSubst_mem_flagSemiInv (w : Equiv.Perm (Fin N)) {lam : Fin N → ℤ} {x : FlagLoc N k}
    (hx : x ∈ flagSemiInv N k lam) : weylSubst w x ∈ flagSemiInv N k lam := by
  intro B hB
  rw [← weylSubst_substRightAway, hx B hB, weylSubst_smul]

theorem weylSubst_mem_denomBounded (w : Equiv.Perm (Fin N)) {I : Finset (Equiv.Perm (Fin N))}
    {x : FlagLoc N k} (hx : x ∈ denomBounded N k I) :
    weylSubst w x ∈ denomBounded N k (I.image fun σ => w⁻¹ * σ) := by
  classical
  obtain ⟨m, p, hp⟩ := hx
  refine ⟨m, substLeft (permMat w k) p, ?_⟩
  rw [← substLeft_denomOf, ← weylSubst_algebraMap, ← map_pow, ← map_mul, hp, weylSubst_algebraMap]

/-- **The Weyl group permutes the cells.** -/
theorem weylSubst_mem_cellSections (w : Equiv.Perm (Fin N)) {I : Finset (Equiv.Perm (Fin N))}
    {lam : Fin N → ℤ} {x : FlagLoc N k} (hx : x ∈ cellSections N k I lam) :
    weylSubst w x ∈ cellSections N k (I.image fun σ => w⁻¹ * σ) lam :=
  ⟨weylSubst_mem_flagSemiInv w hx.1, weylSubst_mem_denomBounded w hx.2⟩

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem permMat_mul_permMat (v w : Equiv.Perm (Fin N)) :
    permMat v k * permMat w k = permMat (v * w) k := by
  rw [permMat_mul]
  ext r c
  rw [Matrix.submatrix_apply, id_eq, permMat, permMat, permWitness, permWitness]
  simp only [Matrix.of_apply]
  by_cases h : r = (v * w) c
  · rw [if_pos h, if_pos (by rw [h]; simp)]
  · rw [if_neg h, if_neg (fun hc => h (by rw [Equiv.Perm.mul_apply, ← hc]; simp))]

@[simp] theorem permMat_one : permMat (1 : Equiv.Perm (Fin N)) k = 1 := by
  ext r c
  rw [permMat, permWitness, Matrix.of_apply, Matrix.one_apply]
  simp

theorem weylSubst_weylSubst (v w : Equiv.Perm (Fin N)) (x : FlagLoc N k) :
    weylSubst w (weylSubst v x) = weylSubst (v * w) x := by
  have hext : (weylSubst (k := k) w).comp (weylSubst v) = weylSubst (v * w) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (totalDenom N k)) (RingHom.ext fun p => ?_)
    show weylSubst w (weylSubst v (algebraMap _ _ p)) = weylSubst (v * w) (algebraMap _ _ p)
    rw [weylSubst_algebraMap, weylSubst_algebraMap, weylSubst_algebraMap, substLeft_substLeft,
      permMat_mul_permMat]
  exact congrFun (congrArg (fun f : FlagLoc N k →+* FlagLoc N k => (f : FlagLoc N k → FlagLoc N k))
    hext) x

@[simp] theorem weylSubst_one (x : FlagLoc N k) : weylSubst (1 : Equiv.Perm (Fin N)) x = x := by
  have hext : weylSubst (k := k) (1 : Equiv.Perm (Fin N)) = RingHom.id (FlagLoc N k) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (totalDenom N k)) (RingHom.ext fun p => ?_)
    show weylSubst (1 : Equiv.Perm (Fin N)) (algebraMap _ _ p) = _
    rw [weylSubst_algebraMap, permMat_one, substLeft_one]
    rfl
  exact congrFun (congrArg (fun f : FlagLoc N k →+* FlagLoc N k => (f : FlagLoc N k → FlagLoc N k))
    hext) x

theorem weylSubst_leftInverse (w : Equiv.Perm (Fin N)) (x : FlagLoc N k) :
    weylSubst w⁻¹ (weylSubst w x) = x := by
  rw [weylSubst_weylSubst, mul_inv_cancel, weylSubst_one]

/-- **The chart description of the sections on an arbitrary cell.** -/
theorem exists_weylSubst_cellCoordAlg_eq {σ : Equiv.Perm (Fin N)} {x : FlagLoc N k}
    (hx : x ∈ cellSections N k {σ} (fun _ => 0)) :
    ∃ p : MvPolynomial (Fin N × Fin N) k, x = weylSubst σ⁻¹ (cellCoordAlg p) := by
  classical
  have himg : ({σ} : Finset (Equiv.Perm (Fin N))).image (fun τ => σ⁻¹ * τ)
      = {(1 : Equiv.Perm (Fin N))} := by
    rw [Finset.image_singleton, inv_mul_cancel]
  have hx' : weylSubst σ x ∈ cellSections N k {(1 : Equiv.Perm (Fin N))} (fun _ => 0) := by
    have h := weylSubst_mem_cellSections σ hx
    rwa [himg] at h
  obtain ⟨p, hp⟩ := exists_cellCoordAlg_eq hx'
  refine ⟨p, ?_⟩
  rw [← hp, weylSubst_weylSubst, mul_inv_cancel, weylSubst_one]

theorem weylSubst_cellCoordAlg_mem_cellSections (σ : Equiv.Perm (Fin N))
    (p : MvPolynomial (Fin N × Fin N) k) :
    weylSubst σ⁻¹ (cellCoordAlg p) ∈ cellSections N k {σ} (fun _ => 0) := by
  classical
  have h := weylSubst_mem_cellSections (k := k) σ⁻¹ (cellCoordAlg_mem_cellSections p)
  have himg : ({(1 : Equiv.Perm (Fin N))} : Finset (Equiv.Perm (Fin N))).image
      (fun τ => (σ⁻¹)⁻¹ * τ) = {σ} := by
    rw [Finset.image_singleton, mul_one, inv_inv]
  rwa [himg] at h

end GaloisForLFunctions.HTGeometry.BorelWeil
