import GaloisForLFunctions.HTGeometry.ExponentialTowerBell
import GaloisForLFunctions.HTGeometry.ColumnPencilDeterminant
import GaloisForLFunctions.HTGeometry.DerivationTerminalLinearJacobian

/-!
# The partial-sum Jacobian of the tower is nonzero at every height

The jets of the tower's `m`-th partial sum have a nonvanishing Jacobian against the first `m`
coordinate derivations.  The induction is on the height: passing from `m` to `m+1` the newest variable
enters only through the newest monomial and only linearly, so the Jacobian is a column pencil whose
top coefficient is, after dropping multiples of the constant column and expanding along the unit row,
the Bell Jacobian of the previous partial sum — which the Bell substitution identifies with the
previous Jacobian.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The Jacobian of the first `m` jets of the `m`-th partial sum against the first `m` coordinates. -/
noncomputable def sumJacobian (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial ℕ ℂ) :=
  Matrix.of fun i j => (MvPolynomial.pderiv ((j : ℕ) + 1))
    (((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(i : ℕ)]) (towerSum m))

theorem towerMonomial_ne_zero (k : ℕ) : (towerMonomial k : MvPolynomial ℕ ℂ) ≠ 0 := by
  rw [towerMonomial]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  exact MvPolynomial.X_ne_zero i

/-! ## The pencil data at one height -/

/-- The affine part of the pencil: the previous partial sum's Jacobian columns. -/
noncomputable def towerA (m : ℕ) : Fin m → Fin (m + 1) → MvPolynomial ℕ ℂ :=
  fun j i => (MvPolynomial.pderiv ((j : ℕ) + 1))
    (((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(i : ℕ)]) (towerSum m))

/-- The Bell iterates of the previous partial sum. -/
noncomputable def towerU (m : ℕ) : Fin (m + 1) → MvPolynomial ℕ ℂ :=
  fun i => towerBell (towerSum m) (i : ℕ)

/-- The Jacobian columns of those Bell iterates. -/
noncomputable def towerV (m : ℕ) : Fin m → Fin (m + 1) → MvPolynomial ℕ ℂ :=
  fun j i => (MvPolynomial.pderiv ((j : ℕ) + 1)) (towerU m i)

/-- The Jacobian columns of the newest monomial's cofactor. -/
noncomputable def towerC (m : ℕ) : Fin m → MvPolynomial ℕ ℂ :=
  fun j => (MvPolynomial.pderiv ((j : ℕ) + 1)) (towerMonomial m)

/-- The linear part of the pencil. -/
noncomputable def towerBcol (m : ℕ) : Fin m → Fin (m + 1) → MvPolynomial ℕ ℂ :=
  fun j i => towerC m j * towerU m i + towerMonomial m * towerV m j i

/-- The constant column of the pencil. -/
noncomputable def towerW (m : ℕ) : Fin (m + 1) → MvPolynomial ℕ ℂ :=
  fun i => towerMonomial m * towerU m i

theorem sumJacobian_top (m : ℕ) (i : Fin (m + 1)) :
    sumJacobian (m + 1) i (Fin.last m) = towerW m i := by
  simp only [sumJacobian, Matrix.of_apply, towerW, towerU]
  rw [show ((Fin.last m : Fin (m + 1)) : ℕ) = m from rfl]
  exact pderiv_iterate_towerSum_succ_top m (i : ℕ)

theorem sumJacobian_low (m : ℕ) (i : Fin (m + 1)) (j : Fin m) :
    sumJacobian (m + 1) i j.castSucc
      = towerA m j i + MvPolynomial.X (m + 1) * towerBcol m j i := by
  simp only [sumJacobian, Matrix.of_apply, towerA, towerBcol, towerC, towerU, towerV]
  rw [show ((j.castSucc : Fin (m + 1)) : ℕ) = (j : ℕ) from rfl]
  rw [pderiv_iterate_towerSum_succ_low (by omega : (j : ℕ) + 1 ≤ m)]
  congr 2
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-! ## Membership of the pencil data in the low subalgebra -/

theorem towerU_mem (m : ℕ) (i : Fin (m + 1)) : towerU m i ∈ lowAlg m :=
  towerBell_mem_lowAlg (towerSum_mem_lowAlg (le_refl m)) _

theorem towerA_mem (m : ℕ) (j : Fin m) (i : Fin (m + 1)) : towerA m j i ∈ lowAlg m :=
  pderiv_mem_lowAlg (iterate_towerDerivation_mem_lowAlg (towerSum_mem_lowAlg (le_refl m)) _)

theorem towerBcol_mem (m : ℕ) (j : Fin m) (i : Fin (m + 1)) : towerBcol m j i ∈ lowAlg m := by
  refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ ?_ (towerU_mem m i))
    (Subalgebra.mul_mem _ (towerMonomial_mem_lowAlg (le_refl m)) ?_)
  · exact pderiv_mem_lowAlg (towerMonomial_mem_lowAlg (le_refl m))
  · exact pderiv_mem_lowAlg (towerU_mem m i)

theorem towerW_mem (m : ℕ) (i : Fin (m + 1)) : towerW m i ∈ lowAlg m :=
  Subalgebra.mul_mem _ (towerMonomial_mem_lowAlg (le_refl m)) (towerU_mem m i)

/-! ## The Jacobian is a column pencil -/

theorem topSub_sumJacobian (m : ℕ) :
    (topSub m).toRingHom.mapMatrix (sumJacobian (m + 1))
      = columnPencil (towerA m) (towerBcol m) (towerW m) := by
  funext i j
  refine Fin.lastCases ?_ ?_ j
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply, sumJacobian_top m i,
      show (topSub m).toRingHom (towerW m i) = topSub m (towerW m i) from rfl,
      topSub_eq_C (towerW_mem m i)]
    simp only [columnPencil, Matrix.of_apply, Fin.lastCases_last]
  · intro j'
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, sumJacobian_low m i j',
      show (topSub m).toRingHom (towerA m j' i + MvPolynomial.X (m + 1) * towerBcol m j' i)
        = topSub m (towerA m j' i + MvPolynomial.X (m + 1) * towerBcol m j' i) from rfl,
      map_add, map_mul, topSub_eq_C (towerA_mem m j' i), topSub_eq_C (towerBcol_mem m j' i),
      topSub_X_top]
    simp only [columnPencil, Matrix.of_apply, Fin.lastCases_castSucc]

/-! ## The Bell identification -/

theorem towerBell_eq_derivationBellValue (m n : ℕ) (i : Fin (n + 1)) :
    towerBell (towerSum m) ((i : ℕ) + 1)
      = derivationBellValue towerDerivation (towerSum m) n i := by
  have hlog : towerDerivation (towerMonomial (m + 1))
      = towerSum m * towerMonomial (m + 1) := by
    rw [towerDerivation_towerMonomial]; ring
  have h1 := derivation_iterate_terminalLinear_eq_derivationBellValue towerDerivation
      (towerMonomial (m + 1)) (towerSum m) hlog n i
  have h2 := iterate_towerDerivation_of_logLinear hlog ((i : ℕ) + 1)
  rw [h1] at h2
  exact (mul_left_cancel₀ (towerMonomial_ne_zero (m + 1)) h2).symm

theorem det_bell_pderiv_eq_sumJacobian (k : ℕ) :
    (Matrix.of fun i j : Fin (k + 1) =>
        (MvPolynomial.pderiv ((j : ℕ) + 1))
          (towerBell (towerSum (k + 1)) ((i : ℕ) + 1))).det
      = (sumJacobian (k + 1)).det := by
  have h := derivationBellValueJacobian_det (R := MvPolynomial ℕ ℂ) towerDerivation k
    (fun l : Fin (k + 2) => MvPolynomial.pderiv ((l : ℕ) + 1)) (towerSum (k + 1))
  have hL : (Matrix.of fun i j : Fin (k + 1) =>
      (MvPolynomial.pderiv ((j : ℕ) + 1))
        (towerBell (towerSum (k + 1)) ((i : ℕ) + 1)))
      = derivationBellValueJacobian towerDerivation k
        (fun l : Fin (k + 2) => MvPolynomial.pderiv ((l : ℕ) + 1)) (towerSum (k + 1)) := by
    funext i j
    show (MvPolynomial.pderiv ((j : ℕ) + 1))
        (towerBell (towerSum (k + 1)) ((i : ℕ) + 1))
      = (MvPolynomial.pderiv (((j.castSucc : Fin (k + 2)) : ℕ) + 1))
          (derivationBellValue towerDerivation (towerSum (k + 1)) k i)
    rw [towerBell_eq_derivationBellValue (k + 1) k i, Fin.val_castSucc]
  have hR : derivationLowerJetJacobian towerDerivation k
      (fun l : Fin (k + 2) => MvPolynomial.pderiv ((l : ℕ) + 1)) (towerSum (k + 1))
      = sumJacobian (k + 1) := by
    funext i j
    rfl
  rw [hL, h, hR]

/-! ## The induction -/

/-- **The partial-sum Jacobian is nonzero at every height.** -/
theorem sumJacobian_det_ne_zero : ∀ k : ℕ, (sumJacobian (k + 1)).det ≠ 0 := by
  intro k
  induction k with
  | zero =>
      rw [Matrix.det_fin_one]
      have hval : sumJacobian 1 0 0 = 1 := by
        simp only [sumJacobian, Matrix.of_apply]
        rw [show (0 : Fin 1).val = 0 from rfl, Function.iterate_zero_apply,
          show (1 : ℕ) = 0 + 1 from rfl, towerSum_succ, towerSum_zero, map_add]
        have h1 : (MvPolynomial.pderiv (0 + 1)) (1 : MvPolynomial ℕ ℂ) = 0 := by simp
        have h2 : towerMonomial (0 + 1) = MvPolynomial.X (0 + 1) := by
          rw [towerMonomial_succ, towerMonomial_zero, one_mul]
        rw [h1, h2, MvPolynomial.pderiv_X_self, zero_add]
      rw [hval]
      exact one_ne_zero
  | succ k ih =>
      intro hzero
      have hdet0 : (columnPencil (towerA (k + 1)) (towerBcol (k + 1)) (towerW (k + 1))).det = 0 := by
        rw [← topSub_sumJacobian (k + 1), ← RingHom.map_det, hzero, map_zero]
      have hlead : (columnLeading (towerBcol (k + 1)) (towerW (k + 1))).det = 0 := by
        rw [← coeff_det_columnPencil (towerA (k + 1)) (towerBcol (k + 1)) (towerW (k + 1)),
          hdet0, Polynomial.coeff_zero]
      have hsplit : (columnLeading (towerBcol (k + 1)) (towerW (k + 1))).det
          = (towerMonomial (k + 1)) ^ (k + 2)
            * (columnLeading (towerV (k + 1)) (towerU (k + 1))).det := by
        exact det_columnLeading_smul_add (towerV (k + 1)) (towerU (k + 1))
          (towerC (k + 1)) (towerMonomial (k + 1))
      have hpow : (towerMonomial (k + 1) : MvPolynomial ℕ ℂ) ^ (k + 2) ≠ 0 :=
        pow_ne_zero _ (towerMonomial_ne_zero (k + 1))
      have hlead2 : (columnLeading (towerV (k + 1)) (towerU (k + 1))).det = 0 := by
        rw [hsplit] at hlead
        rcases mul_eq_zero.mp hlead with h | h
        · exact absurd h hpow
        · exact h
      have hu0 : towerU (k + 1) 0 = 1 := by
        simp [towerU]
      have hv0 : ∀ j : Fin (k + 1), towerV (k + 1) j 0 = 0 := by
        intro j
        simp [towerV, towerU]
      have hexp : (columnLeading (towerV (k + 1)) (towerU (k + 1))).det
          = (-1) ^ (k + 1)
            * (Matrix.of fun i j : Fin (k + 1) => towerV (k + 1) j i.succ).det :=
        det_columnLeading_of_row_zero (towerV (k + 1)) (towerU (k + 1)) hu0 hv0
      have hminor : (Matrix.of fun i j : Fin (k + 1) => towerV (k + 1) j i.succ).det = 0 := by
        rw [hexp] at hlead2
        rcases mul_eq_zero.mp hlead2 with h | h
        · exact absurd h (pow_ne_zero _ (by norm_num : (-1 : MvPolynomial ℕ ℂ) ≠ 0))
        · exact h
      have hmatch : (Matrix.of fun i j : Fin (k + 1) => towerV (k + 1) j i.succ)
          = Matrix.of fun i j : Fin (k + 1) =>
              (MvPolynomial.pderiv ((j : ℕ) + 1))
                (towerBell (towerSum (k + 1)) ((i : ℕ) + 1)) := by
        funext i j
        simp only [Matrix.of_apply, towerV, towerU]
        rw [show ((i.succ : Fin (k + 2)) : ℕ) = (i : ℕ) + 1 from rfl]
      rw [hmatch, det_bell_pderiv_eq_sumJacobian k] at hminor
      exact ih hminor

end GaloisForLFunctions.HTGeometry
