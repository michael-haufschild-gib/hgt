import Mathlib
import GaloisForLFunctions.Core
import GaloisForLFunctions.HTGeometry.SmithNormalFormDVR
import GaloisForLFunctions.HTGeometry.VandermondeSign
import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity

/-!
# Common-contact sheets, their observer staircase, and the contact scaling

Sheets `f_i = c u_i` with unit residues pairwise distinct modulo the maximal ideal have a
sheet-evaluation matrix that factors as the residue Vandermonde — invertible over the base — times
the contact scaling `diag(1, c, …, c^{N−1})`.  The observer barcode is therefore the exact
staircase `R/(c), R/(c²), …, R/(c^{N−1})`, and every determinantal ideal of the observer is a
power of `c` with triangular exponent.

The same factorisation transports any operator intertwined with multiplication by sheet values:
its matrix is the residue matrix conjugated by the contact scaling, so its minors acquire the exact
exponent `k(N−1) + ∑J − ∑I`, minimised uniquely on the southwest rows and the first columns.
-/

namespace HTGeometry.ConstraintRelativity

open GaloisForLFunctions.HTGeometry IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-! ## The contact factorisation -/

/-- **Card `(3)`.**  The common-contact sheets `f_i = c u_i`. -/
def contactSheets {N : ℕ} (c : R) (u : Fin N → R) : Fin N → R := fun i => c * u i

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The sheet-evaluation matrix factors as the residue Vandermonde times the contact scaling. -/
theorem vandermonde_contactSheets {N : ℕ} (c : R) (u : Fin N → R) :
    Matrix.vandermonde (contactSheets c u)
      = Matrix.vandermonde u * Matrix.diagonal fun j : Fin N => c ^ (j : ℕ) := by
  ext i j
  rw [Matrix.vandermonde_apply, Matrix.mul_diagonal, Matrix.vandermonde_apply]
  show (c * u i) ^ (j : ℕ) = u i ^ (j : ℕ) * c ^ (j : ℕ)
  rw [mul_pow, mul_comm]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(2)`.**  Pairwise distinct residues make the residue Vandermonde invertible over the
base ring. -/
theorem isUnit_det_vandermonde_of_separated {N : ℕ} (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) :
    IsUnit (Matrix.vandermonde u).det := by
  rw [det_vandermonde_eq_vandermondeProd, vandermondeProd]
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => ?_
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j hj => ?_
  exact hu i j (ne_of_lt (Finset.mem_Ioi.mp hj))

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The contact scaling is a divisibility chain. -/
theorem contactScaling_chain {N : ℕ} (c : R) :
    ∀ i j : Fin N, i ≤ j → c ^ (i : ℕ) ∣ c ^ (j : ℕ) := fun _ _ h => pow_dvd_pow c h

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(8)`, boxed.**  The observer barcode of a common-contact configuration is the exact
staircase `R/(c^j)`. -/
theorem contact_cokernel_equiv {N : ℕ} (c : R) (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) :
    Nonempty (((Fin N → R) ⧸ LinearMap.range (Matrix.vandermonde (contactSheets c u)).mulVecLin)
      ≃ₗ[R] ∀ j : Fin N, R ⧸ (Ideal.span {c ^ (j : ℕ)} : Submodule R R)) := by
  classical
  have hV := isUnit_det_vandermonde_of_separated u hu
  refine cokernel_equiv_pi_of_diagonal (U := (Matrix.vandermonde u)⁻¹) (V := 1) ?_ ?_ ?_
  · exact Matrix.isUnit_nonsing_inv_det _ hV
  · rw [Matrix.det_one]
    exact isUnit_one
  · rw [Matrix.mul_one, vandermonde_contactSheets, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hV, Matrix.one_mul]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(8)`.**  Every determinantal ideal of the common-contact observer is the triangular
power of the contact parameter. -/
theorem detIdeal_contact {N : ℕ} (c : R) (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) {k : ℕ} (hk : k ≤ N) :
    detIdeal (Matrix.vandermonde (contactSheets c u)) k
      = Ideal.span {c ^ (∑ α : Fin k, (α : ℕ))} := by
  classical
  have hV := isUnit_det_vandermonde_of_separated u hu
  have hfac : Matrix.vandermonde (contactSheets c u)
      = Matrix.vandermonde u * Matrix.diagonal fun j : Fin N => c ^ (j : ℕ) :=
    vandermonde_contactSheets c u
  have hprod : (∏ α : Fin k, c ^ ((Fin.castLE hk α : Fin N) : ℕ))
      = c ^ (∑ α : Fin k, (α : ℕ)) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hfac, detIdeal_unit_mul hV, detIdeal_diagonal_chain _ (contactScaling_chain c) hk, hprod]

/-! ## The contact scaling of an intertwined operator -/

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(16)`.**  Conjugating a residue operator by the contact scaling multiplies its `(i, j)`
entry by `c^{N−1+j−i}`. -/
theorem contactScale_apply {N : ℕ} (c : R) (B : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    ((Matrix.diagonal fun i : Fin N => c ^ (N - 1 - (i : ℕ))) * B
        * Matrix.diagonal fun j : Fin N => c ^ (j : ℕ)) i j
      = c ^ (N - 1 - (i : ℕ) + (j : ℕ)) * B i j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, pow_add]
  ring

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(17)`.**  Every minor of the contact-scaled operator carries the exact exponent
`∑_α (N−1−I α) + ∑_β J β`. -/
theorem det_submatrix_contactScale {N : ℕ} (c : R) (B : Matrix (Fin N) (Fin N) R) {k : ℕ}
    (I J : Fin k → Fin N) :
    (((Matrix.diagonal fun i : Fin N => c ^ (N - 1 - (i : ℕ))) * B
        * Matrix.diagonal fun j : Fin N => c ^ (j : ℕ)).submatrix I J).det
      = c ^ ((∑ α : Fin k, (N - 1 - (I α : ℕ))) + ∑ β : Fin k, (J β : ℕ))
        * (B.submatrix I J).det := by
  classical
  have hsub : ((Matrix.diagonal fun i : Fin N => c ^ (N - 1 - (i : ℕ))) * B
        * Matrix.diagonal fun j : Fin N => c ^ (j : ℕ)).submatrix I J
      = (Matrix.diagonal fun α : Fin k => c ^ (N - 1 - (I α : ℕ))) * (B.submatrix I J)
        * Matrix.diagonal fun β : Fin k => c ^ (J β : ℕ) := by
    ext α β
    rw [Matrix.submatrix_apply, contactScale_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.submatrix_apply, pow_add]
    ring
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add]
  ring


/-! ## The residue polynomial, its cofactors, and the moment matrix -/

section Residue

variable {N : ℕ}

/-- The residue polynomial `Q = ∏ (X − u_i)`. -/
noncomputable def residuePoly (u : Fin N → R) : Polynomial R :=
  ∏ i : Fin N, (Polynomial.X - Polynomial.C (u i))

/-- The cofactor polynomial `Q / (X − u_i) = ∏_{k ≠ i} (X − u_k)`. -/
noncomputable def cofactorPoly (u : Fin N → R) (i : Fin N) : Polynomial R :=
  ∏ k ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (u k))

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem residuePoly_monic (u : Fin N → R) : (residuePoly u).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (u i)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem cofactorPoly_monic (u : Fin N → R) (i : Fin N) : (cofactorPoly u i).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C (u k)

omit [IsDiscreteValuationRing R] in
theorem natDegree_residuePoly (u : Fin N → R) : (residuePoly u).natDegree = N := by
  rw [residuePoly,
    Polynomial.natDegree_prod _ _ fun i _ => (Polynomial.monic_X_sub_C (u i)).ne_zero]
  simp

omit [IsDiscreteValuationRing R] in
theorem natDegree_cofactorPoly (u : Fin N → R) (i : Fin N) :
    (cofactorPoly u i).natDegree = N - 1 := by
  classical
  rw [cofactorPoly,
    Polynomial.natDegree_prod _ _ fun k _ => (Polynomial.monic_X_sub_C (u k)).ne_zero]
  simp [Finset.card_erase_of_mem (Finset.mem_univ i)]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The factorisation `(X − u_i) · Q/(X − u_i) = Q`. -/
theorem linear_mul_cofactorPoly (u : Fin N → R) (i : Fin N) :
    (Polynomial.X - Polynomial.C (u i)) * cofactorPoly u i = residuePoly u := by
  classical
  rw [cofactorPoly, residuePoly]
  exact Finset.mul_prod_erase Finset.univ (fun k => Polynomial.X - Polynomial.C (u k))
    (Finset.mem_univ i)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The synthetic-division recursion for the cofactor coefficients. -/
theorem coeff_cofactorPoly_succ (u : Fin N → R) (i : Fin N) (n : ℕ) :
    (cofactorPoly u i).coeff n
      = (residuePoly u).coeff (n + 1) + u i * (cofactorPoly u i).coeff (n + 1) := by
  have h := congrArg (fun p : Polynomial R => p.coeff (n + 1)) (linear_mul_cofactorPoly u i)
  simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul] at h
  linear_combination h

omit [IsDiscreteValuationRing R] in
/-- **Card, proof of Lemma 2.**  The cofactor coefficients are the truncated tails of the residue
polynomial evaluated along the sheet. -/
theorem coeff_cofactorPoly (u : Fin N → R) (i : Fin N) :
    ∀ d : ℕ, d < N →
      (cofactorPoly u i).coeff (N - 1 - d)
        = ∑ s ∈ Finset.range (d + 1), (residuePoly u).coeff (N - d + s) * u i ^ s := by
  intro d
  induction d with
  | zero =>
    intro _
    have h1 : (cofactorPoly u i).coeff (N - 1) = 1 := by
      have h := (cofactorPoly_monic u i).coeff_natDegree
      rwa [natDegree_cofactorPoly] at h
    have h2 : (residuePoly u).coeff N = 1 := by
      have h := (residuePoly_monic u).coeff_natDegree
      rwa [natDegree_residuePoly] at h
    simp [h1, h2]
  | succ d ih =>
    intro hd
    have hdN : d < N := Nat.lt_of_succ_lt hd
    have hstep : N - 1 - d = (N - 1 - (d + 1)) + 1 := by omega
    have hrec := coeff_cofactorPoly_succ u i (N - 1 - (d + 1))
    rw [← hstep] at hrec
    have hidx : N - 1 - d = N - (d + 1) := by omega
    have hL : (residuePoly u).coeff (N - (d + 1))
          + u i * ∑ t ∈ Finset.range (d + 1), (residuePoly u).coeff (N - d + t) * u i ^ t
        = (residuePoly u).coeff (N - (d + 1))
          + ∑ t ∈ Finset.range (d + 1),
              (residuePoly u).coeff (N - (d + 1) + (t + 1)) * u i ^ (t + 1) := by
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht' : t < d + 1 := Finset.mem_range.mp ht
      have hre : N - (d + 1) + (t + 1) = N - d + t := by omega
      rw [hre]
      ring
    rw [hrec, ih hdN, hidx, hL,
      Finset.sum_range_succ' (fun s => (residuePoly u).coeff (N - (d + 1) + s) * u i ^ s) (d + 1)]
    simp [add_comm]

/-- The matrix of cofactor coefficients. -/
noncomputable def cofactorMatrix (u : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun j i => (cofactorPoly u i).coeff (j : ℕ)

omit [IsDiscreteValuationRing R] in
/-- The residue Vandermonde times the cofactor matrix is the diagonal of cofactor values. -/
theorem vandermonde_mul_cofactorMatrix (u : Fin N → R) :
    Matrix.vandermonde u * cofactorMatrix u
      = Matrix.diagonal fun i => (cofactorPoly u i).eval (u i) := by
  classical
  ext i i'
  have hN : 0 < N := Fin.pos_iff_nonempty.mpr ⟨i⟩
  have hdeg : (cofactorPoly u i').natDegree < N := by
    rw [natDegree_cofactorPoly]
    omega
  have hval : ∑ j : Fin N, Matrix.vandermonde u i j * cofactorMatrix u j i'
      = (cofactorPoly u i').eval (u i) := by
    have hrange : ∑ j : Fin N, ((cofactorPoly u i').coeff (j : ℕ) * u i ^ (j : ℕ))
        = ∑ j ∈ Finset.range N, (cofactorPoly u i').coeff j * u i ^ j :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => (cofactorPoly u i').coeff j * u i ^ j) N
    rw [Polynomial.eval_eq_sum_range' hdeg (u i), ← hrange]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.vandermonde_apply]
    exact mul_comm _ _
  rw [Matrix.mul_apply, hval]
  by_cases hii : i = i'
  · subst hii
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hii, cofactorPoly, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hii, Finset.mem_univ i⟩) (by simp)

end Residue


/-! ## The phase subdiscriminant and the southwest block -/

section Moment

variable {N : ℕ}

/-- **Card `(6)`.**  The power sums of the residues. -/
noncomputable def moment (u : Fin N → R) (l : ℕ) : R := ∑ i : Fin N, u i ^ l

/-- **Card `(6)`.**  The Hankel moment matrix. -/
noncomputable def momentMatrix (u : Fin N → R) (k : ℕ) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun p q => moment u ((p : ℕ) + (q : ℕ))

/-- **Card `(6)`, `(7)`.**  The phase subdiscriminant `H_k`. -/
noncomputable def phaseSubdiscriminant (u : Fin N → R) (k : ℕ) : R := (momentMatrix u k).det

/-- The matrix of multiplication by the residue different in the monomial basis. -/
noncomputable def residueMult (u : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  cofactorMatrix u * Matrix.vandermonde u

omit [IsDiscreteValuationRing R] in
/-- It intertwines the residue observer with multiplication by the cofactor values. -/
theorem vandermonde_mul_residueMult (u : Fin N → R) :
    Matrix.vandermonde u * residueMult u
      = (Matrix.diagonal fun i => (cofactorPoly u i).eval (u i)) * Matrix.vandermonde u := by
  rw [residueMult, ← Matrix.mul_assoc, vandermonde_mul_cofactorMatrix]

/-- The southwest row selection. -/
def southwestRows (hN : 0 < N) (k : ℕ) : Fin k → Fin N :=
  fun p => ⟨N - 1 - (p : ℕ), by omega⟩

/-- The unit lower-triangular transition between the southwest rows and the moment rows. -/
noncomputable def coeffTriangle (u : Fin N → R) (k : ℕ) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun p s =>
    if (s : ℕ) ≤ (p : ℕ) then (residuePoly u).coeff (N - (p : ℕ) + (s : ℕ)) else 0

omit [IsDiscreteValuationRing R] in
theorem det_coeffTriangle (u : Fin N → R) {k : ℕ} (hk : k ≤ N) :
    (coeffTriangle u k).det = 1 := by
  classical
  have h2 : (residuePoly u).coeff N = 1 := by
    have h := (residuePoly_monic u).coeff_natDegree
    rwa [natDegree_residuePoly] at h
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun p _ => ?_
    have hp : (p : ℕ) < k := p.isLt
    show (if ((p : ℕ)) ≤ (p : ℕ) then (residuePoly u).coeff (N - (p : ℕ) + (p : ℕ)) else 0) = 1
    rw [if_pos le_rfl]
    have : N - (p : ℕ) + (p : ℕ) = N := by omega
    rw [this, h2]
  · intro p s hps
    show (if ((s : ℕ)) ≤ (p : ℕ) then (residuePoly u).coeff (N - (p : ℕ) + (s : ℕ)) else 0) = 0
    refine if_neg ?_
    exact Nat.not_le.mpr (by exact_mod_cast hps)

omit [IsDiscreteValuationRing R] in
/-- **Card `(13)`.**  The southwest block of the multiplication matrix is the moment matrix, up to
a unit lower-triangular change of rows. -/
theorem submatrix_residueMult_southwest (u : Fin N → R) (hN : 0 < N) {k : ℕ} (hk : k ≤ N) :
    (residueMult u).submatrix (southwestRows hN k) (Fin.castLE hk)
      = coeffTriangle u k * momentMatrix u k := by
  classical
  ext p q
  have hpk : (p : ℕ) < k := p.isLt
  have hpN : (p : ℕ) < N := lt_of_lt_of_le hpk hk
  have hlhs : (residueMult u).submatrix (southwestRows hN k) (Fin.castLE hk) p q
      = ∑ i : Fin N, (cofactorPoly u i).coeff (N - 1 - (p : ℕ)) * u i ^ (q : ℕ) := by
    rw [Matrix.submatrix_apply, residueMult, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.vandermonde_apply]
    rfl
  have hswap : ∑ i : Fin N, (cofactorPoly u i).coeff (N - 1 - (p : ℕ)) * u i ^ (q : ℕ)
      = ∑ s ∈ Finset.range ((p : ℕ) + 1),
          (residuePoly u).coeff (N - (p : ℕ) + s) * moment u (s + (q : ℕ)) := by
    have hstep : ∀ i : Fin N, (cofactorPoly u i).coeff (N - 1 - (p : ℕ)) * u i ^ (q : ℕ)
        = ∑ s ∈ Finset.range ((p : ℕ) + 1),
            (residuePoly u).coeff (N - (p : ℕ) + s) * u i ^ (s + (q : ℕ)) := by
      intro i
      rw [coeff_cofactorPoly u i (p : ℕ) hpN, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [pow_add]
      ring
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [moment, Finset.mul_sum]
  have hrhs : (coeffTriangle u k * momentMatrix u k) p q
      = ∑ s ∈ Finset.range ((p : ℕ) + 1),
          (residuePoly u).coeff (N - (p : ℕ) + s) * moment u (s + (q : ℕ)) := by
    have hG : ∀ s : Fin k, coeffTriangle u k p s * momentMatrix u k s q
        = (if (s : ℕ) ≤ (p : ℕ) then (residuePoly u).coeff (N - (p : ℕ) + (s : ℕ)) else 0)
          * moment u ((s : ℕ) + (q : ℕ)) := fun _ => rfl
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun s _ => hG s,
      Fin.sum_univ_eq_sum_range (fun s => (if s ≤ (p : ℕ)
        then (residuePoly u).coeff (N - (p : ℕ) + s) else 0) * moment u (s + (q : ℕ))) k,
      ← Finset.sum_subset (show Finset.range ((p : ℕ) + 1) ⊆ Finset.range k by
        intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega)]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))]
    · intro s _ hs
      rw [Finset.mem_range, Nat.lt_succ_iff] at hs
      rw [if_neg (Nat.not_le.mpr (Nat.lt_of_not_le hs)), zero_mul]
  rw [hlhs, hswap, hrhs]

omit [IsDiscreteValuationRing R] in
/-- **Card `(11)`, boxed.**  The southwest `k × k` minor of the multiplication matrix is exactly
the phase subdiscriminant `H_k`. -/
theorem det_submatrix_residueMult_southwest (u : Fin N → R) (hN : 0 < N) {k : ℕ} (hk : k ≤ N) :
    ((residueMult u).submatrix (southwestRows hN k) (Fin.castLE hk)).det
      = phaseSubdiscriminant u k := by
  rw [submatrix_residueMult_southwest u hN hk, Matrix.det_mul, det_coeffTriangle u hk, one_mul,
    phaseSubdiscriminant]

end Moment


/-! ## The exact minor exponent and the real-chamber square law -/

section Chamber

variable {N : ℕ}

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- An injective selection has index sum at least the triangular number. -/
theorem sum_le_sum_of_injective {k : ℕ} {f : Fin k → Fin N} (hf : Function.Injective f) :
    ∑ α : Fin k, (α : ℕ) ≤ ∑ α : Fin k, (f α : ℕ) := by
  classical
  have hJ : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Equiv.injective _))
  have hperm : ∑ α : Fin k, ((f ∘ Tuple.sort f) α : ℕ) = ∑ α : Fin k, (f α : ℕ) :=
    Equiv.sum_comp (Tuple.sort f) fun α => ((f α : Fin N) : ℕ)
  rw [← hperm]
  exact Finset.sum_le_sum fun α _ => val_le_val_of_strictMono hJ α

/-- The contact-scaled operator. -/
noncomputable def contactScale (c : R) (B : Matrix (Fin N) (Fin N) R) :
    Matrix (Fin N) (Fin N) R :=
  (Matrix.diagonal fun i : Fin N => c ^ (N - 1 - (i : ℕ))) * B
    * Matrix.diagonal fun j : Fin N => c ^ (j : ℕ)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(18)`.**  Every `k`-minor of the contact-scaled operator is divisible by
`c^{k(k−1)}`. -/
theorem pow_dvd_det_submatrix_contactScale (c : R) (B : Matrix (Fin N) (Fin N) R) {k : ℕ}
    (I J : Fin k → Fin N) :
    c ^ (2 * ∑ α : Fin k, (α : ℕ)) ∣ ((contactScale c B).submatrix I J).det := by
  classical
  by_cases hI : Function.Injective I
  · by_cases hJ : Function.Injective J
    · rw [contactScale, det_submatrix_contactScale]
      refine Dvd.dvd.mul_right (pow_dvd_pow c ?_) _
      have hIrev : Function.Injective fun α : Fin k => (⟨N - 1 - (I α : ℕ), by omega⟩ : Fin N) := by
        intro a b hab
        have hval : N - 1 - (I a : ℕ) = N - 1 - (I b : ℕ) := congrArg Fin.val hab
        have ha := (I a).isLt
        have hb := (I b).isLt
        exact hI (Fin.ext (by omega))
      have h1 := sum_le_sum_of_injective hIrev
      have h2 := sum_le_sum_of_injective hJ
      simp only at h1
      omega
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, J a = J b ∧ a ≠ b := by
        by_contra hcon
        push Not at hcon
        exact hJ fun x y h => hcon x y h
      rw [Matrix.det_zero_of_column_eq hne fun γ => by
        rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hab]]
      exact dvd_zero _
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, I a = I b ∧ a ≠ b := by
      by_contra hcon
      push Not at hcon
      exact hI fun x y h => hcon x y h
    rw [Matrix.det_zero_of_row_eq hne (by
      funext γ
      rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hab])]
    exact dvd_zero _

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The southwest minor of the contact-scaled operator realises the lower bound exactly. -/
theorem det_southwest_contactScale (c : R) (B : Matrix (Fin N) (Fin N) R) (hN : 0 < N) {k : ℕ}
    (hk : k ≤ N) :
    ((contactScale c B).submatrix (southwestRows hN k) (Fin.castLE hk)).det
      = c ^ (2 * ∑ α : Fin k, (α : ℕ))
        * (B.submatrix (southwestRows hN k) (Fin.castLE hk)).det := by
  rw [contactScale, det_submatrix_contactScale]
  congr 2
  have hrow : ∀ α : Fin k, N - 1 - ((southwestRows hN k α : Fin N) : ℕ) = (α : ℕ) := by
    intro α
    have := α.isLt
    show N - 1 - (N - 1 - (α : ℕ)) = (α : ℕ)
    omega
  have hcol : ∀ α : Fin k, ((Fin.castLE hk α : Fin N) : ℕ) = (α : ℕ) := fun _ => rfl
  rw [Finset.sum_congr rfl fun α _ => hrow α, Finset.sum_congr rfl fun α _ => hcol α]
  ring

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(18)`, boxed.**  If the southwest residue minor is a unit then the `k`-th determinantal
ideal of the contact-scaled operator is exactly `(c^{k(k−1)})`. -/
theorem detIdeal_contactScale (c : R) (B : Matrix (Fin N) (Fin N) R) (hN : 0 < N) {k : ℕ}
    (hk : k ≤ N)
    (hsw : IsUnit ((B.submatrix (southwestRows hN k) (Fin.castLE hk)).det)) :
    detIdeal (contactScale c B) k = Ideal.span {c ^ (2 * ∑ α : Fin k, (α : ℕ))} := by
  classical
  refine le_antisymm (detIdeal_le fun I J => ?_) ?_
  · exact Ideal.mem_span_singleton.mpr (pow_dvd_det_submatrix_contactScale c B I J)
  · rw [Ideal.span_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨v, hv⟩ := hsw
    have hmem := minor_mem_detIdeal (contactScale c B) (southwestRows hN k) (Fin.castLE hk)
    rw [det_southwest_contactScale c B hN hk, ← hv] at hmem
    have := Ideal.mul_mem_left (detIdeal (contactScale c B) k) ((v⁻¹ : Rˣ) : R) hmem
    rwa [← mul_assoc, mul_comm ((v⁻¹ : Rˣ) : R), mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, mul_one] at this

end Chamber


/-! ## The all-Fitting square law -/

section Square

variable {N : ℕ}

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- A scalar diagonal commutes with every matrix. -/
theorem mul_diagonal_const (M : Matrix (Fin N) (Fin N) R) (a : R) :
    M * Matrix.diagonal (fun _ : Fin N => a) = Matrix.diagonal (fun _ : Fin N => a) * M := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

omit [IsDiscreteValuationRing R] in
/-- **Card `(16)`.**  The contact-scaled residue multiplication matrix is intertwined with
multiplication by the sheet values of the sheet different `P' = c^{N−1} Q'`. -/
theorem vandermonde_contactSheets_mul_contactScale (c : R) (u : Fin N → R) :
    Matrix.vandermonde (contactSheets c u) * contactScale c (residueMult u)
      = (Matrix.diagonal fun i => c ^ (N - 1) * (cofactorPoly u i).eval (u i))
        * Matrix.vandermonde (contactSheets c u) := by
  classical
  have hdiag : (Matrix.diagonal fun j : Fin N => c ^ (j : ℕ))
      * Matrix.diagonal (fun i : Fin N => c ^ (N - 1 - (i : ℕ)))
      = Matrix.diagonal fun _ : Fin N => c ^ (N - 1) := by
    rw [Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    have := i.isLt
    rw [← pow_add]
    congr 1
    omega
  calc Matrix.vandermonde (contactSheets c u) * contactScale c (residueMult u)
      = Matrix.vandermonde u * ((Matrix.diagonal fun j : Fin N => c ^ (j : ℕ))
          * Matrix.diagonal fun i : Fin N => c ^ (N - 1 - (i : ℕ)))
          * (residueMult u * Matrix.diagonal fun j : Fin N => c ^ (j : ℕ)) := by
        rw [vandermonde_contactSheets, contactScale]
        simp only [Matrix.mul_assoc]
    _ = (Matrix.diagonal fun _ : Fin N => c ^ (N - 1))
          * (Matrix.vandermonde u * residueMult u
            * Matrix.diagonal fun j : Fin N => c ^ (j : ℕ)) := by
        rw [hdiag, ← Matrix.mul_assoc, mul_diagonal_const]
        simp only [Matrix.mul_assoc]
    _ = (Matrix.diagonal fun i => c ^ (N - 1) * (cofactorPoly u i).eval (u i))
          * Matrix.vandermonde (contactSheets c u) := by
        rw [vandermonde_mul_residueMult, vandermonde_contactSheets]
        simp only [Matrix.mul_assoc, ← Matrix.diagonal_mul_diagonal]

omit [IsDiscreteValuationRing R] in
/-- **Card `(15)`, boxed.**  In the chamber where every phase subdiscriminant is a unit, the
determinantal ideal of the cotangent presentation is the square of the determinantal ideal of the
observer, at every height. -/
theorem detIdeal_contactScale_eq_sq (c : R) (u : Fin N → R) (hN : 0 < N)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) {k : ℕ} (hk : k ≤ N)
    (hsw : IsUnit (phaseSubdiscriminant u k)) :
    detIdeal (contactScale c (residueMult u)) k
      = detIdeal (Matrix.vandermonde (contactSheets c u)) k ^ 2 := by
  have hswdet : IsUnit
      (((residueMult u).submatrix (southwestRows hN k) (Fin.castLE hk)).det) := by
    rwa [det_submatrix_residueMult_southwest u hN hk]
  have hcomm : 2 * (∑ α : Fin k, (α : ℕ)) = (∑ α : Fin k, (α : ℕ)) * 2 := Nat.mul_comm _ _
  rw [detIdeal_contactScale c (residueMult u) hN hk hswdet, detIdeal_contact c u hu hk,
    Ideal.span_singleton_pow, ← pow_mul, hcomm]

end Square


/-! ## The real chamber -/

section RealChamber

variable {N : ℕ}

/-- The evaluation of a coefficient vector at a point. -/
def coeffEval {S : Type*} [CommRing S] {k : ℕ} (x : Fin k → S) (t : S) : S :=
  ∑ p : Fin k, x p * t ^ (p : ℕ)

/-- The polynomial with the given coefficient vector. -/
noncomputable def coeffPoly {S : Type*} [CommRing S] {k : ℕ} (x : Fin k → S) : Polynomial S :=
  ∑ p : Fin k, Polynomial.C (x p) * Polynomial.X ^ (p : ℕ)

theorem eval_coeffPoly {S : Type*} [CommRing S] {k : ℕ} (x : Fin k → S) (t : S) :
    (coeffPoly x).eval t = coeffEval x t := by
  rw [coeffPoly, coeffEval, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

theorem natDegree_coeffPoly_lt {S : Type*} [CommRing S] [Nontrivial S] {k : ℕ} (hk : 0 < k)
    (x : Fin k → S) :
    (coeffPoly x).natDegree < k := by
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun p _ => ?_)
    (Nat.sub_lt hk Nat.one_pos)
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_X_pow]
  have := p.isLt
  omega

theorem coeff_coeffPoly {S : Type*} [CommRing S] {k : ℕ} (x : Fin k → S) (p : Fin k) :
    (coeffPoly x).coeff (p : ℕ) = x p := by
  classical
  rw [coeffPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hq (Fin.ext h.symm)),
      mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- **Card, proof of Theorem 3.**  A nonzero coefficient vector of length at most `N` cannot
vanish at `N` distinct points. -/
theorem exists_coeffEval_ne_zero {S : Type*} [CommRing S] [IsDomain S] {n : ℕ} {lam : Fin n → S}
    (hlam : Function.Injective lam) {k : ℕ} (hk : k ≤ n) {x : Fin k → S} (hx : x ≠ 0) :
    ∃ i : Fin n, coeffEval x (lam i) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (funext fun p => Fin.elim0 p) hx
    · exact h
  have hzero : coeffPoly x = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (coeffPoly x) hlam
      (fun i => by rw [eval_coeffPoly]; exact hcon i) ?_
    rw [Fintype.card_fin]
    exact lt_of_lt_of_le (natDegree_coeffPoly_lt hkpos x) hk
  exact hx (funext fun p => by rw [← coeff_coeffPoly x p, hzero, Polynomial.coeff_zero]; rfl)

/-- **Card, proof of Theorem 3.**  Over the reals the moment matrix of distinct residues is
positive definite. -/
theorem posDef_momentMatrix {lam : Fin N → ℝ} (hlam : Function.Injective lam) {k : ℕ}
    (hk : k ≤ N) : (momentMatrix lam k).PosDef := by
  classical
  constructor
  · ext p q
    show momentMatrix lam k q p = momentMatrix lam k p q
    show moment lam ((q : ℕ) + (p : ℕ)) = moment lam ((p : ℕ) + (q : ℕ))
    rw [Nat.add_comm]
  · intro x hx
    set y : Fin k → ℝ := fun i => x i with hy
    have hyne : y ≠ 0 := by
      intro h
      refine hx (Finsupp.ext fun i => ?_)
      have := congrFun h i
      simpa [hy] using this
    have hsum : (x.sum fun i xi => x.sum fun j xj =>
          star xi * momentMatrix lam k i j * xj)
        = ∑ i : Fin k, ∑ j : Fin k, y i * momentMatrix lam k i j * y j := by
      rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
      rfl
    have hL : ∀ i : Fin k, (∑ j : Fin k, y i * momentMatrix lam k i j * y j)
        = ∑ j : Fin k, ∑ l : Fin N, y i * y j * lam l ^ ((i : ℕ) + (j : ℕ)) := by
      intro i
      refine Finset.sum_congr rfl fun j _ => ?_
      show y i * moment lam ((i : ℕ) + (j : ℕ)) * y j = _
      rw [moment, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    have hswap : ∑ i : Fin k, ∑ j : Fin k, ∑ l : Fin N,
          y i * y j * lam l ^ ((i : ℕ) + (j : ℕ))
        = ∑ l : Fin N, ∑ i : Fin k, ∑ j : Fin k,
          y i * y j * lam l ^ ((i : ℕ) + (j : ℕ)) := by
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_comm]
      exact Finset.sum_comm
    have hl : ∀ l : Fin N, (∑ i : Fin k, ∑ j : Fin k,
          y i * y j * lam l ^ ((i : ℕ) + (j : ℕ)))
        = coeffEval y (lam l) * coeffEval y (lam l) := by
      intro l
      rw [coeffEval, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add]
      ring
    rw [hsum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hL i, hswap,
      Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hl l]
    obtain ⟨l₀, hl₀⟩ := exists_coeffEval_ne_zero hlam hk hyne
    exact Finset.sum_pos' (fun l _ => mul_self_nonneg _)
      ⟨l₀, Finset.mem_univ l₀, mul_self_pos.mpr hl₀⟩

/-- **Card `(14)`, real chamber.**  Distinct real residues make every phase subdiscriminant
strictly positive, hence nonzero. -/
theorem phaseSubdiscriminant_pos {lam : Fin N → ℝ} (hlam : Function.Injective lam) {k : ℕ}
    (hk : k ≤ N) : 0 < phaseSubdiscriminant lam k :=
  (posDef_momentMatrix hlam hk).det_pos

end RealChamber


/-! ## Total length is conserved -/

section Total

variable {N : ℕ}

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The moment matrix at full size is the Gram matrix of the residue Vandermonde. -/
theorem momentMatrix_top (u : Fin N → R) :
    momentMatrix u N = (Matrix.vandermonde u).transpose * Matrix.vandermonde u := by
  ext p q
  rw [Matrix.mul_apply]
  show moment u ((p : ℕ) + (q : ℕ)) = _
  rw [moment]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_apply, Matrix.vandermonde_apply, Matrix.vandermonde_apply, ← pow_add]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(20)`.**  The top phase subdiscriminant is the residue discriminant. -/
theorem phaseSubdiscriminant_top (u : Fin N → R) :
    phaseSubdiscriminant u N = (vandermondeProd u) ^ 2 := by
  rw [phaseSubdiscriminant, momentMatrix_top, Matrix.det_mul, Matrix.det_transpose,
    det_vandermonde_eq_vandermondeProd, sq]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Separated residues make the top phase subdiscriminant a unit. -/
theorem isUnit_phaseSubdiscriminant_top (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) :
    IsUnit (phaseSubdiscriminant u N) := by
  rw [phaseSubdiscriminant_top]
  refine IsUnit.pow 2 ?_
  rw [← det_vandermonde_eq_vandermondeProd]
  exact isUnit_det_vandermonde_of_separated u hu

omit [IsDiscreteValuationRing R] in
/-- **Card `(20)`, boxed.**  Total cotangent length is conserved: the top determinantal ideal of
the cotangent presentation is `(c^{N(N−1)})`, whatever the phase. -/
theorem detIdeal_contactScale_top (c : R) (u : Fin N → R) (hN : 0 < N)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) :
    detIdeal (contactScale c (residueMult u)) N
      = Ideal.span {c ^ (2 * ∑ α : Fin N, (α : ℕ))} := by
  have hswdet : IsUnit
      (((residueMult u).submatrix (southwestRows hN N) (Fin.castLE le_rfl)).det) := by
    rw [det_submatrix_residueMult_southwest u hN le_rfl]
    exact isUnit_phaseSubdiscriminant_top u hu
  exact detIdeal_contactScale c (residueMult u) hN le_rfl hswdet

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The triangular exponent in closed form. -/
theorem sum_val_fin (n : ℕ) : 2 * ∑ α : Fin n, (α : ℕ) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have hcast : ∑ α : Fin m, ((α.castSucc : Fin (m + 1)) : ℕ) = ∑ α : Fin m, (α : ℕ) :=
      Finset.sum_congr rfl fun _ _ => rfl
    rw [hcast, Nat.mul_add, ih]
    have : ((Fin.last m : Fin (m + 1)) : ℕ) = m := rfl
    rw [this]
    cases m with
    | zero => simp
    | succ t =>
      simp only [Nat.succ_sub_one]
      ring

end Total


/-! ## Phase walls: the equianharmonic and square configurations -/

section Walls

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The second phase subdiscriminant in closed form. -/
theorem phaseSubdiscriminant_two {N : ℕ} (u : Fin N → R) :
    phaseSubdiscriminant u 2 = moment u 0 * moment u 2 - moment u 1 * moment u 1 := by
  rw [phaseSubdiscriminant, Matrix.det_fin_two]
  rfl

/-- **Card `(21)`.**  The equianharmonic triple of cube roots of unity. -/
def cubeRootTriple (w : R) : Fin 3 → R := ![1, w, w ^ 2]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(22)`.**  The equianharmonic triple lies on the second phase wall. -/
theorem phaseSubdiscriminant_cubeRootTriple {w : R} (hw : w ^ 2 + w + 1 = 0) :
    phaseSubdiscriminant (cubeRootTriple w) 2 = 0 := by
  have hm0 : moment (cubeRootTriple w) 0 = 3 := by
    rw [moment, Fin.sum_univ_three]
    simp [cubeRootTriple]
    ring
  have hm1 : moment (cubeRootTriple w) 1 = 0 := by
    rw [moment, Fin.sum_univ_three]
    simp only [cubeRootTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, pow_one]
    linear_combination hw
  have hm2 : moment (cubeRootTriple w) 2 = 0 := by
    rw [moment, Fin.sum_univ_three]
    simp only [cubeRootTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination (w ^ 2 - w + 1) * hw
  rw [phaseSubdiscriminant_two, hm0, hm1, hm2]
  ring

/-- **Card `(22a)`.**  The square configuration of fourth roots of unity. -/
def squareQuadruple (w : R) : Fin 4 → R := ![1, w, -1, -w]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(22a)`.**  The square configuration lies on the second phase wall. -/
theorem phaseSubdiscriminant_squareQuadruple {w : R} (hw : w ^ 2 + 1 = 0) :
    phaseSubdiscriminant (squareQuadruple w) 2 = 0 := by
  have hm0 : moment (squareQuadruple w) 0 = 4 := by
    rw [moment, Fin.sum_univ_four]
    simp [squareQuadruple]
    ring
  have hm1 : moment (squareQuadruple w) 1 = 0 := by
    rw [moment, Fin.sum_univ_four]
    simp only [squareQuadruple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, pow_one]
    ring
  have hm2 : moment (squareQuadruple w) 2 = 0 := by
    rw [moment, Fin.sum_univ_four]
    simp only [squareQuadruple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    linear_combination 2 * hw
  rw [phaseSubdiscriminant_two, hm0, hm1, hm2]
  ring

end Walls


/-! ## The phase jump -/

section Jump

variable {N : ℕ}

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Equality in the index-sum bound forces the extreme selection. -/
theorem exists_perm_of_sum_eq {k : ℕ} (hk : k ≤ N) {f : Fin k → Fin N}
    (hf : Function.Injective f)
    (hsum : ∑ α : Fin k, (f α : ℕ) = ∑ α : Fin k, (α : ℕ)) :
    ∃ σ : Equiv.Perm (Fin k), ∀ α, f α = Fin.castLE hk (σ α) := by
  classical
  have hg : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Equiv.injective _))
  have hperm : ∑ α : Fin k, ((f ∘ Tuple.sort f) α : ℕ) = ∑ α : Fin k, (f α : ℕ) :=
    Equiv.sum_comp (Tuple.sort f) fun α => ((f α : Fin N) : ℕ)
  have hle : ∀ α ∈ (Finset.univ : Finset (Fin k)), (α : ℕ) ≤ ((f ∘ Tuple.sort f) α : ℕ) :=
    fun α _ => val_le_val_of_strictMono hg α
  have heq : ∀ α ∈ (Finset.univ : Finset (Fin k)), (α : ℕ) = ((f ∘ Tuple.sort f) α : ℕ) :=
    (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [hperm, hsum])
  refine ⟨(Tuple.sort f)⁻¹, fun β => ?_⟩
  have h1 := heq ((Tuple.sort f)⁻¹ β) (Finset.mem_univ _)
  refine Fin.ext ?_
  show (f β : ℕ) = (((Tuple.sort f)⁻¹ β : Fin k) : ℕ)
  have h2 : (f ∘ Tuple.sort f) ((Tuple.sort f)⁻¹ β) = f β := by
    show f (Tuple.sort f ((Tuple.sort f)⁻¹ β)) = f β
    simp
  rw [← h2, ← h1]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(19)`.**  Every minor of the contact-scaled operator either is the southwest one up to
sign and the exact power `c^{k(k−1)}`, or carries one more power of `c`. -/
theorem detIdeal_contactScale_le (c : R) (B : Matrix (Fin N) (Fin N) R) (hN : 0 < N) {k : ℕ}
    (hk : k ≤ N) :
    detIdeal (contactScale c B) k
      ≤ Ideal.span {c ^ (2 * ∑ α : Fin k, (α : ℕ))
            * (B.submatrix (southwestRows hN k) (Fin.castLE hk)).det,
          c ^ (2 * ∑ α : Fin k, (α : ℕ) + 1)} := by
  classical
  set T : ℕ := ∑ α : Fin k, (α : ℕ) with hT
  refine detIdeal_le fun I J => ?_
  by_cases hI : Function.Injective I
  · by_cases hJ : Function.Injective J
    · have hIrev : Function.Injective fun α : Fin k => (⟨N - 1 - (I α : ℕ), by omega⟩ : Fin N) := by
        intro a b hab
        have hval : N - 1 - (I a : ℕ) = N - 1 - (I b : ℕ) := congrArg Fin.val hab
        have ha := (I a).isLt
        have hb := (I b).isLt
        exact hI (Fin.ext (by omega))
      have h1 := sum_le_sum_of_injective hIrev
      have h2 := sum_le_sum_of_injective hJ
      simp only at h1
      rcases Nat.lt_or_ge ((∑ α : Fin k, (N - 1 - (I α : ℕ))) + ∑ β : Fin k, (J β : ℕ)) (2 * T + 1)
        with hlt | hge
      · -- the exponent is minimal: both selections are extreme
        have hIeq : (∑ α : Fin k, (N - 1 - (I α : ℕ))) = T := by omega
        have hJeq : (∑ β : Fin k, (J β : ℕ)) = T := by omega
        obtain ⟨σ, hσ⟩ := exists_perm_of_sum_eq hk hIrev (by rw [hIeq, hT])
        obtain ⟨τ, hτ⟩ := exists_perm_of_sum_eq hk hJ (by rw [hJeq, hT])
        have hIform : ∀ α, I α = southwestRows hN k (σ α) := by
          intro α
          have hv : N - 1 - (I α : ℕ) = (σ α : ℕ) := congrArg Fin.val (hσ α)
          have := (I α).isLt
          exact Fin.ext (by show (I α : ℕ) = N - 1 - (σ α : ℕ); omega)
        have hsub : B.submatrix I J
            = (B.submatrix (southwestRows hN k) (Fin.castLE hk)).submatrix σ τ := by
          ext α β
          rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.submatrix_apply, hIform α,
            hτ β]
        have hdet : (B.submatrix I J).det
            = ((Equiv.Perm.sign τ : ℤ) : R) * (((Equiv.Perm.sign σ : ℤ) : R)
              * (B.submatrix (southwestRows hN k) (Fin.castLE hk)).det) := by
          have hsplit : (B.submatrix (southwestRows hN k) (Fin.castLE hk)).submatrix σ τ
              = (((B.submatrix (southwestRows hN k) (Fin.castLE hk)).submatrix σ id)).submatrix
                id τ := rfl
          rw [hsub, hsplit, Matrix.det_permute', Matrix.det_permute]
        rw [contactScale, det_submatrix_contactScale, hIeq, hJeq, hdet]
        refine Ideal.mem_span_pair.mpr
          ⟨((Equiv.Perm.sign τ : ℤ) : R) * ((Equiv.Perm.sign σ : ℤ) : R), 0, ?_⟩
        have : T + T = 2 * T := by omega
        rw [this]
        ring
      · rw [contactScale, det_submatrix_contactScale]
        refine Ideal.mul_mem_right _ _ ?_
        refine Ideal.mem_span_pair.mpr ⟨0, c ^ ((∑ α : Fin k, (N - 1 - (I α : ℕ)))
          + (∑ β : Fin k, (J β : ℕ)) - (2 * T + 1)), ?_⟩
        rw [zero_mul, zero_add, ← pow_add]
        congr 1
        omega
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, J a = J b ∧ a ≠ b := by
        by_contra hcon
        push Not at hcon
        exact hJ fun x y h => hcon x y h
      have hdet0 : ((contactScale c B).submatrix I J).det = 0 :=
        Matrix.det_zero_of_column_eq hne fun γ => by
          rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hab]
      rw [hdet0]
      exact Ideal.zero_mem _
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, I a = I b ∧ a ≠ b := by
      by_contra hcon
      push Not at hcon
      exact hI fun x y h => hcon x y h
    have hdet0 : ((contactScale c B).submatrix I J).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by
        funext γ
        rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hab])
    rw [hdet0]
    exact Ideal.zero_mem _


omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The generic value of the determinantal ideal bounds it from above. -/
theorem detIdeal_contactScale_le_generic (c : R) (u : Fin N → R) (hN : 0 < N) {k : ℕ}
    (hk : k ≤ N) :
    detIdeal (contactScale c (residueMult u)) k
      ≤ Ideal.span {c ^ (2 * ∑ α : Fin k, (α : ℕ))} := by
  refine le_trans (detIdeal_contactScale_le c (residueMult u) hN hk) ?_
  rw [Ideal.span_le]
  rintro y hy
  rcases hy with hy | hy
  · rw [hy]
    exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Ideal.mem_span_singleton.mpr ⟨c, by rw [pow_succ]⟩

/-- **Card `(19)`, boxed.**  On a phase wall the determinantal ideal drops strictly below its
generic value: the Kähler Smith type jumps although the observer barcode and the total length do
not. -/
theorem detIdeal_contactScale_lt_of_wall (c : R) (u : Fin N → R) (hN : 0 < N) {k : ℕ}
    (hk : k ≤ N) (hc0 : c ≠ 0) (hc : ¬ IsUnit c)
    (hH : ¬ IsUnit (phaseSubdiscriminant u k)) :
    detIdeal (contactScale c (residueMult u)) k
      < Ideal.span {c ^ (2 * ∑ α : Fin k, (α : ℕ))} := by
  refine lt_of_le_of_ne (detIdeal_contactScale_le_generic c u hN hk) fun hEq => ?_
  have hmem : c ^ (2 * ∑ α : Fin k, (α : ℕ))
      ∈ detIdeal (contactScale c (residueMult u)) k := by
    rw [hEq]
    exact Ideal.mem_span_singleton.mpr dvd_rfl
  have hle := detIdeal_contactScale_le c (residueMult u) hN hk hmem
  rw [det_submatrix_residueMult_southwest u hN hk] at hle
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hle
  rw [pow_succ] at hab
  have hcancel : a * phaseSubdiscriminant u k + b * c = 1 := by
    refine mul_left_cancel₀ (pow_ne_zero (2 * ∑ α : Fin k, (α : ℕ)) hc0) ?_
    rw [mul_one]
    linear_combination hab
  have hnu : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hcancel]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · exact (IsLocalRing.mem_maximalIdeal _).mpr hH
    · exact (IsLocalRing.mem_maximalIdeal _).mpr hc
  exact ((IsLocalRing.mem_maximalIdeal (1 : R)).mp hnu) isUnit_one

end Jump


/-! ## The successor exact sequence -/

section Successor

variable {N : ℕ}

/-- The polynomial of the first `N` sheets. -/
noncomputable def belowPoly (x : Fin (N + 1) → R) : Polynomial R :=
  residuePoly (x ∘ Fin.castSucc)

/-- **Card `(24)`.**  The successor gap `P_N(x_q)`. -/
noncomputable def successorGap (x : Fin (N + 1) → R) : R :=
  (belowPoly x).eval (x (Fin.last N))

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem eval_belowPoly_castSucc (x : Fin (N + 1) → R) (i : Fin N) :
    (belowPoly x).eval (x (Fin.castSucc i)) = 0 := by
  classical
  rw [belowPoly, residuePoly, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp

omit [IsDiscreteValuationRing R] in
/-- The monic expansion of the below-polynomial at a sheet. -/
theorem eval_belowPoly_eq (x : Fin (N + 1) → R) (t : R) :
    (belowPoly x).eval t
      = t ^ N + ∑ j ∈ Finset.range N, (belowPoly x).coeff j * t ^ j := by
  have hdeg : (belowPoly x).natDegree = N := natDegree_residuePoly (x ∘ Fin.castSucc)
  have hmonic : (belowPoly x).coeff N = 1 := by
    have h := (residuePoly_monic (x ∘ Fin.castSucc)).coeff_natDegree
    rw [natDegree_residuePoly] at h
    exact h
  rw [Polynomial.eval_eq_sum_range' (n := N + 1) (by rw [hdeg]; omega) t,
    Finset.sum_range_succ, hmonic, one_mul]
  ring

omit [IsDiscreteValuationRing R] in
/-- **Card `(24)`.**  The evaluation of a degree-`N` coefficient vector at the first `N` sheets is
the evaluation of a degree-`N−1` one. -/
theorem exists_shift_mulVec (x : Fin (N + 1) → R) (v : Fin (N + 1) → R) :
    ∃ w : Fin N → R, ∀ i : Fin N,
      (Matrix.vandermonde x).mulVec v (Fin.castSucc i)
        = (Matrix.vandermonde (x ∘ Fin.castSucc)).mulVec w i := by
  classical
  refine ⟨fun j => v (Fin.castSucc j) - v (Fin.last N) * (belowPoly x).coeff (j : ℕ), fun i => ?_⟩
  have hzero := eval_belowPoly_castSucc x i
  rw [eval_belowPoly_eq] at hzero
  have hpow : x (Fin.castSucc i) ^ N
      = -∑ j ∈ Finset.range N, (belowPoly x).coeff j * x (Fin.castSucc i) ^ j := by
    linear_combination hzero
  show ∑ j : Fin (N + 1), Matrix.vandermonde x (Fin.castSucc i) j * v j
      = ∑ j : Fin N, Matrix.vandermonde (x ∘ Fin.castSucc) i j
        * (v (Fin.castSucc j) - v (Fin.last N) * (belowPoly x).coeff (j : ℕ))
  have hL : ∑ j : Fin (N + 1), Matrix.vandermonde x (Fin.castSucc i) j * v j
      = (∑ j : Fin N, x (Fin.castSucc i) ^ (j : ℕ) * v (Fin.castSucc j))
        + x (Fin.castSucc i) ^ N * v (Fin.last N) := by
    rw [Fin.sum_univ_castSucc]
    rfl
  have hR : ∑ j : Fin N, Matrix.vandermonde (x ∘ Fin.castSucc) i j
        * (v (Fin.castSucc j) - v (Fin.last N) * (belowPoly x).coeff (j : ℕ))
      = (∑ j : Fin N, x (Fin.castSucc i) ^ (j : ℕ) * v (Fin.castSucc j))
        - v (Fin.last N)
          * ∑ j : Fin N, (belowPoly x).coeff (j : ℕ) * x (Fin.castSucc i) ^ (j : ℕ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.vandermonde_apply]
    show x (Fin.castSucc i) ^ (j : ℕ) * (v (Fin.castSucc j)
      - v (Fin.last N) * (belowPoly x).coeff (j : ℕ)) = _
    ring
  have hrange : ∑ j : Fin N, (belowPoly x).coeff (j : ℕ) * x (Fin.castSucc i) ^ (j : ℕ)
      = ∑ j ∈ Finset.range N, (belowPoly x).coeff j * x (Fin.castSucc i) ^ j :=
    Fin.sum_univ_eq_sum_range
      (fun j => (belowPoly x).coeff j * x (Fin.castSucc i) ^ j) N
  rw [hL, hR, hrange, hpow]
  ring


/-- The projection forgetting the last sheet coordinate. -/
noncomputable def succProj : (Fin (N + 1) → R) →ₗ[R] (Fin N → R) :=
  LinearMap.funLeft R R Fin.castSucc

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem succProj_apply (w : Fin (N + 1) → R) (i : Fin N) :
    succProj w i = w (Fin.castSucc i) := rfl

omit [IsDiscreteValuationRing R] in
/-- The projection carries the big observer range into the small one. -/
theorem succProj_range_le (x : Fin (N + 1) → R) :
    Submodule.map succProj (LinearMap.range (Matrix.vandermonde x).mulVecLin)
      ≤ LinearMap.range (Matrix.vandermonde (x ∘ Fin.castSucc)).mulVecLin := by
  rintro y ⟨z, ⟨v, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := exists_shift_mulVec x v
  exact ⟨w, funext fun i => (hw i).symm⟩

/-- **Card `(24)`.**  The successor observer map, forgetting the last sheet. -/
noncomputable def successorMap (x : Fin (N + 1) → R) :
    ((Fin (N + 1) → R) ⧸ LinearMap.range (Matrix.vandermonde x).mulVecLin)
      →ₗ[R] ((Fin N → R) ⧸
        LinearMap.range (Matrix.vandermonde (x ∘ Fin.castSucc)).mulVecLin) :=
  Submodule.mapQ _ _ succProj (Submodule.map_le_iff_le_comap.mp (succProj_range_le x))

omit [IsDiscreteValuationRing R] in
/-- **Card `(24)`, right exactness.** -/
theorem successorMap_surjective (x : Fin (N + 1) → R) :
    Function.Surjective (successorMap x) := by
  intro z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine ⟨Submodule.Quotient.mk ((Fin.snoc y (0 : R) : Fin (N + 1) → R)), ?_⟩
  show Submodule.Quotient.mk (succProj ((Fin.snoc y (0 : R) : Fin (N + 1) → R)))
    = Submodule.Quotient.mk y
  congr 1
  funext i
  show (Fin.snoc y (0 : R) : Fin (N + 1) → R) (Fin.castSucc i) = y i
  rw [Fin.snoc_castSucc]

/-- The last-coordinate line inside the big cokernel. -/
noncomputable def lastLine (x : Fin (N + 1) → R) :
    R →ₗ[R] ((Fin (N + 1) → R) ⧸ LinearMap.range (Matrix.vandermonde x).mulVecLin) :=
  (Submodule.mkQ _).comp (LinearMap.toSpanSingleton R _ (Pi.single (Fin.last N) (1 : R)))

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem lastLine_apply (x : Fin (N + 1) → R) (z : R) :
    lastLine x z = Submodule.Quotient.mk (Pi.single (Fin.last N) z) := by
  show Submodule.Quotient.mk (z • Pi.single (Fin.last N) (1 : R)) = _
  congr 1
  funext i
  rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : i = Fin.last N
  · rw [if_pos h, if_pos h, smul_eq_mul, mul_one]
  · rw [if_neg h, if_neg h, smul_zero]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- A vector vanishing off the last coordinate is a multiple of the last basis vector. -/
theorem eq_single_last {w : Fin (N + 1) → R} (hw : ∀ i : Fin N, w (Fin.castSucc i) = 0) :
    w = Pi.single (Fin.last N) (w (Fin.last N)) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [Pi.single_eq_same]
  · intro i
    rw [hw i, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The observer is evaluation of the coefficient polynomial. -/
theorem mulVec_eq_coeffEval {n : ℕ} (x : Fin n → R) (v : Fin n → R) (i : Fin n) :
    (Matrix.vandermonde x).mulVec v i = coeffEval v (x i) := by
  show ∑ j : Fin n, Matrix.vandermonde x i j * v j = ∑ j : Fin n, v j * x i ^ (j : ℕ)
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.vandermonde_apply]; exact mul_comm _ _

omit [IsDiscreteValuationRing R] in
/-- **Card `(24)`, exactness in the middle.** -/
theorem range_lastLine_eq_ker (x : Fin (N + 1) → R) :
    LinearMap.range (lastLine x) = LinearMap.ker (successorMap x) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨z, rfl⟩
    rw [LinearMap.mem_ker, lastLine_apply]
    have h0 : succProj ((Pi.single (Fin.last N) z : Fin (N + 1) → R)) = 0 := by
      funext i
      show (Pi.single (Fin.last N) z : Fin (N + 1) → R) (Fin.castSucc i) = 0
      rw [Pi.single_apply, if_neg (Fin.castSucc_lt_last i).ne]
    show Submodule.Quotient.mk (succProj ((Pi.single (Fin.last N) z : Fin (N + 1) → R))) = 0
    rw [h0]
    exact Submodule.Quotient.mk_zero _
  · intro y hy
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [LinearMap.mem_ker] at hy
    have hy' : succProj w
        ∈ LinearMap.range (Matrix.vandermonde (x ∘ Fin.castSucc)).mulVecLin := by
      have hq : Submodule.Quotient.mk (succProj w)
          = (0 : (Fin N → R) ⧸
            LinearMap.range (Matrix.vandermonde (x ∘ Fin.castSucc)).mulVecLin) := hy
      rwa [Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨u, hu⟩ := hy'
    have hproj : ∀ i : Fin N,
        (Matrix.vandermonde x).mulVec ((Fin.snoc u 0 : Fin (N + 1) → R)) (Fin.castSucc i)
          = succProj w i := by
      intro i
      rw [← hu]
      show ∑ j : Fin (N + 1), Matrix.vandermonde x (Fin.castSucc i) j
          * (Fin.snoc u (0 : R) : Fin (N + 1) → R) j
        = ∑ j : Fin N, Matrix.vandermonde (x ∘ Fin.castSucc) i j * u j
      rw [Fin.sum_univ_castSucc]
      have hlast : Matrix.vandermonde x (Fin.castSucc i) (Fin.last N)
          * (Fin.snoc u (0 : R) : Fin (N + 1) → R) (Fin.last N) = 0 := by
        rw [Fin.snoc_last, mul_zero]
      rw [hlast, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.snoc_castSucc]
      rfl
    set d : Fin (N + 1) → R :=
      w - (Matrix.vandermonde x).mulVec ((Fin.snoc u 0 : Fin (N + 1) → R)) with hd
    have hdz : ∀ i : Fin N, d (Fin.castSucc i) = 0 := by
      intro i
      show w (Fin.castSucc i)
        - (Matrix.vandermonde x).mulVec ((Fin.snoc u 0 : Fin (N + 1) → R)) (Fin.castSucc i) = 0
      rw [hproj i]
      show w (Fin.castSucc i) - w (Fin.castSucc i) = 0
      exact sub_self _
    refine ⟨d (Fin.last N), ?_⟩
    rw [lastLine_apply, ← eq_single_last hdz]
    refine (Submodule.Quotient.eq _).2 ?_
    show d - w ∈ LinearMap.range (Matrix.vandermonde x).mulVecLin
    refine ⟨-(Fin.snoc u 0 : Fin (N + 1) → R), ?_⟩
    show (Matrix.vandermonde x).mulVec (-(Fin.snoc u 0 : Fin (N + 1) → R)) = d - w
    rw [Matrix.mulVec_neg, hd]
    abel

omit [IsDiscreteValuationRing R] in
/-- The evaluation of the below-polynomial as a coefficient vector. -/
theorem coeffEval_belowPoly (x : Fin (N + 1) → R) (lam : R) (t : R) :
    coeffEval (fun j : Fin (N + 1) => lam * (belowPoly x).coeff (j : ℕ)) t
      = lam * (belowPoly x).eval t := by
  have hdeg : (belowPoly x).natDegree = N := natDegree_residuePoly (x ∘ Fin.castSucc)
  rw [coeffEval, Polynomial.eval_eq_sum_range' (n := N + 1) (by rw [hdeg]; omega) t,
    Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
      (fun j => lam * ((belowPoly x).coeff j * t ^ j)) (N + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [IsDiscreteValuationRing R] in
/-- **Card `(24)`, left exactness.**  The kernel of the last-coordinate line is exactly the ideal
generated by the successor gap `P_N(x_q)`. -/
theorem ker_lastLine (x : Fin (N + 1) → R) (hx : Function.Injective x) :
    LinearMap.ker (lastLine x) = Ideal.span {successorGap x} := by
  classical
  have hQdeg : (belowPoly x).natDegree = N := natDegree_residuePoly (x ∘ Fin.castSucc)
  have hQmonic : (belowPoly x).Monic := residuePoly_monic (x ∘ Fin.castSucc)
  ext z
  rw [LinearMap.mem_ker, lastLine_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨v, hv⟩
    have hval : ∀ i : Fin (N + 1),
        (coeffPoly v).eval (x i) = (Pi.single (Fin.last N) z : Fin (N + 1) → R) i := by
      intro i
      rw [eval_coeffPoly, ← mulVec_eq_coeffEval]
      exact congrFun hv i
    have hroot : ∀ i : Fin N, ((coeffPoly v) %ₘ belowPoly x).eval (x (Fin.castSucc i)) = 0 := by
      intro i
      have hdiv := Polynomial.modByMonic_add_div (coeffPoly v) (belowPoly x)
      have h1 : (coeffPoly v).eval (x (Fin.castSucc i)) = 0 := by
        rw [hval (Fin.castSucc i), Pi.single_apply, if_neg (Fin.castSucc_lt_last i).ne]
      have h2 := congrArg (Polynomial.eval (x (Fin.castSucc i))) hdiv
      rw [Polynomial.eval_add, Polynomial.eval_mul, eval_belowPoly_castSucc, zero_mul, add_zero,
        h1] at h2
      exact h2
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0
      exact ⟨z, by rw [successorGap, belowPoly, residuePoly]; simp⟩
    · have hzero : (coeffPoly v) %ₘ belowPoly x = 0 := by
        refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
          (hx.comp (Fin.castSucc_injective N)) hroot ?_
        rw [Fintype.card_fin]
        rcases eq_or_ne ((coeffPoly v) %ₘ belowPoly x) 0 with h0 | h0
        · rw [h0, Polynomial.natDegree_zero]
          exact hNpos
        · have hlt := Polynomial.degree_modByMonic_lt (coeffPoly v) hQmonic
          have hdq : (belowPoly x).degree = (N : ℕ) := by
            rw [Polynomial.degree_eq_natDegree hQmonic.ne_zero, hQdeg]
          rw [hdq] at hlt
          exact Polynomial.natDegree_lt_iff_degree_lt h0 |>.mpr hlt
      have hfac : coeffPoly v = belowPoly x * ((coeffPoly v) /ₘ belowPoly x) := by
        have hdiv := Polynomial.modByMonic_add_div (coeffPoly v) (belowPoly x)
        rw [hzero, zero_add] at hdiv
        exact hdiv.symm
      rcases eq_or_ne ((coeffPoly v) /ₘ belowPoly x) 0 with hq0 | hq0
      · refine ⟨0, ?_⟩
        have hz : z = (coeffPoly v).eval (x (Fin.last N)) := by
          rw [hval (Fin.last N), Pi.single_eq_same]
        rw [hz, hfac, hq0, mul_zero, Polynomial.eval_zero, mul_zero]
      · have hdegf : (coeffPoly v).natDegree ≤ N := by
          have := natDegree_coeffPoly_lt (Nat.succ_pos N) v
          omega
        have hqdeg : ((coeffPoly v) /ₘ belowPoly x).natDegree = 0 := by
          have hmul : (coeffPoly v).natDegree
              = (belowPoly x).natDegree + ((coeffPoly v) /ₘ belowPoly x).natDegree := by
            conv_lhs => rw [hfac]
            rw [Polynomial.natDegree_mul hQmonic.ne_zero hq0]
          omega
        have hlam := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
        refine ⟨((coeffPoly v) /ₘ belowPoly x).coeff 0, ?_⟩
        have hz : z = (coeffPoly v).eval (x (Fin.last N)) := by
          rw [hval (Fin.last N), Pi.single_eq_same]
        have heval : (coeffPoly v).eval (x (Fin.last N))
            = successorGap x * ((coeffPoly v) /ₘ belowPoly x).coeff 0 := by
          conv_lhs => rw [hfac]
          rw [Polynomial.eval_mul, successorGap]
          congr 1
          conv_lhs => rw [hlam]
          rw [Polynomial.eval_C]
        rw [hz, heval]
  · rintro ⟨lam, rfl⟩
    refine ⟨fun j : Fin (N + 1) => lam * (belowPoly x).coeff (j : ℕ), ?_⟩
    funext i
    refine Fin.lastCases ?_ ?_ i
    · show (Matrix.vandermonde x).mulVec
          (fun j : Fin (N + 1) => lam * (belowPoly x).coeff (j : ℕ)) (Fin.last N) = _
      rw [mulVec_eq_coeffEval, coeffEval_belowPoly, Pi.single_eq_same, successorGap]
      ring
    · intro j
      show (Matrix.vandermonde x).mulVec
          (fun j : Fin (N + 1) => lam * (belowPoly x).coeff (j : ℕ)) (Fin.castSucc j) = _
      rw [mulVec_eq_coeffEval, coeffEval_belowPoly, eval_belowPoly_castSucc, mul_zero,
        Pi.single_apply, if_neg (Fin.castSucc_lt_last j).ne]

end Successor


/-! ## The three-node wall is the equianharmonic locus -/

section Triple

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(22d)`, algebraic form.**  For three nodes the second phase subdiscriminant is
`3∑z² − (∑z)²`. -/
theorem phaseSubdiscriminant_two_triple (z : Fin 3 → R) :
    phaseSubdiscriminant z 2
      = 3 * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) - (z 0 + z 1 + z 2) ^ 2 := by
  rw [phaseSubdiscriminant_two, moment, moment, moment, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three]
  ring

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(22d)`.**  Centred at the barycentre, the wall is the vanishing of the sum of squares
of the centred nodes. -/
theorem phaseSubdiscriminant_two_centered (z : Fin 3 → R) (m : R)
    (hm : z 0 + z 1 + z 2 = 3 * m) :
    phaseSubdiscriminant z 2
      = 3 * ((z 0 - m) ^ 2 + (z 1 - m) ^ 2 + (z 2 - m) ^ 2) := by
  rw [phaseSubdiscriminant_two_triple]
  linear_combination (-(z 0) - z 1 - z 2 + 3 * m) * hm

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- On the wall the second elementary symmetric function of the centred nodes vanishes. -/
theorem esymm_two_centered_eq_zero {z : Fin 3 → R} (m : R)
    (hnzd : ∀ a : R, 6 * a = 0 → a = 0)
    (hm : z 0 + z 1 + z 2 = 3 * m) (hH : phaseSubdiscriminant z 2 = 0) :
    (z 0 - m) * (z 1 - m) + (z 0 - m) * (z 2 - m) + (z 1 - m) * (z 2 - m) = 0 := by
  refine hnzd _ ?_
  have hcent : (z 0 - m) + (z 1 - m) + (z 2 - m) = 0 := by linear_combination hm
  have hsq := phaseSubdiscriminant_two_centered z m hm
  rw [hH] at hsq
  linear_combination (3 * ((z 0 - m) + (z 1 - m) + (z 2 - m))) * hcent + hsq

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- A zero-sum triple with vanishing second symmetric function has all cubes equal to the
product. -/
theorem cube_eq_of_centered {a b c : R} (h1 : a + b + c = 0)
    (h2 : a * b + a * c + b * c = 0) : a ^ 3 = a * b * c := by
  linear_combination a ^ 2 * h1 - a * h2

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(22d)`, boxed geometric core.**  On the three-node wall all centred nodes have the same
cube: the configuration is an affine equilateral triple. -/
theorem cube_centered_eq_of_wall {z : Fin 3 → R} (m : R)
    (hnzd : ∀ a : R, 6 * a = 0 → a = 0)
    (hm : z 0 + z 1 + z 2 = 3 * m) (hH : phaseSubdiscriminant z 2 = 0) :
    (z 0 - m) ^ 3 = (z 0 - m) * (z 1 - m) * (z 2 - m)
      ∧ (z 1 - m) ^ 3 = (z 0 - m) * (z 1 - m) * (z 2 - m)
      ∧ (z 2 - m) ^ 3 = (z 0 - m) * (z 1 - m) * (z 2 - m) := by
  have hcent : (z 0 - m) + (z 1 - m) + (z 2 - m) = 0 := by linear_combination hm
  have he2 := esymm_two_centered_eq_zero m hnzd hm hH
  refine ⟨cube_eq_of_centered hcent he2, ?_, ?_⟩
  · have h1 : (z 1 - m) + (z 0 - m) + (z 2 - m) = 0 := by linear_combination hcent
    have h2 : (z 1 - m) * (z 0 - m) + (z 1 - m) * (z 2 - m) + (z 0 - m) * (z 2 - m) = 0 := by
      linear_combination he2
    have := cube_eq_of_centered h1 h2
    linear_combination this
  · have h1 : (z 2 - m) + (z 0 - m) + (z 1 - m) = 0 := by linear_combination hcent
    have h2 : (z 2 - m) * (z 0 - m) + (z 2 - m) * (z 1 - m) + (z 0 - m) * (z 1 - m) = 0 := by
      linear_combination he2
    have := cube_eq_of_centered h1 h2
    linear_combination this


omit [IsDiscreteValuationRing R] in
/-- **Card `(22c)`.**  At a three-node wall the second determinantal ideal of the cotangent
presentation lies in `(c³)`, one power deeper than the generic `(c²)` of card `(18)`. -/
theorem detIdeal_two_le_of_triple_wall (c : R) (u : Fin 3 → R)
    (hH : phaseSubdiscriminant u 2 = 0) :
    detIdeal (contactScale c (residueMult u)) 2 ≤ Ideal.span {c ^ 3} := by
  have hsum : (∑ α : Fin 2, (α : ℕ)) = 1 := by decide
  refine le_trans (detIdeal_contactScale_le c (residueMult u) (by norm_num) (by norm_num)) ?_
  rw [det_submatrix_residueMult_southwest u (by norm_num) (by norm_num), hH, hsum]
  rw [Ideal.span_le]
  rintro y hy
  rcases hy with hy | hy
  · rw [hy, mul_zero]
    exact Ideal.zero_mem _
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Ideal.mem_span_singleton.mpr dvd_rfl

end Triple


/-! ## The equianharmonic three-node model -/

section Equianharmonic

omit [IsDiscreteValuationRing R] in
/-- The multiplication matrix is determined by its intertwining law. -/
theorem residueMult_eq_of_intertwine {N : ℕ} (u : Fin N → R)
    (hu : IsUnit (Matrix.vandermonde u).det) (M : Matrix (Fin N) (Fin N) R)
    (h : Matrix.vandermonde u * M
      = (Matrix.diagonal fun i => (cofactorPoly u i).eval (u i)) * Matrix.vandermonde u) :
    M = residueMult u := by
  have h2 : Matrix.vandermonde u * M = Matrix.vandermonde u * residueMult u := by
    rw [h, vandermonde_mul_residueMult]
  have h3 := congrArg (fun X => (Matrix.vandermonde u)⁻¹ * X) h2
  simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu] using h3

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem cubeRootTriple_pow_three {w : R} (hw : w ^ 2 + w + 1 = 0) (i : Fin 3) :
    cubeRootTriple w i ^ 3 = 1 := by
  have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  fin_cases i
  · show (1 : R) ^ 3 = 1
    ring
  · show w ^ 3 = 1
    exact hw3
  · show (w ^ 2) ^ 3 = 1
    linear_combination (w ^ 3 + 1) * hw3

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The equianharmonic cofactor values are `3u_i²`. -/
theorem cofactorPoly_eval_cubeRootTriple {w : R} (hw : w ^ 2 + w + 1 = 0) (i : Fin 3) :
    (cofactorPoly (cubeRootTriple w) i).eval (cubeRootTriple w i)
      = 3 * cubeRootTriple w i ^ 2 := by
  classical
  have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  fin_cases i
  · show (cofactorPoly (cubeRootTriple w) 0).eval (cubeRootTriple w 0)
      = 3 * cubeRootTriple w 0 ^ 2
    rw [cofactorPoly, Polynomial.eval_prod]
    have hset : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
    rw [hset, Finset.prod_insert (by decide), Finset.prod_singleton]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, cubeRootTriple,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    linear_combination (w - 2) * hw
  · show (cofactorPoly (cubeRootTriple w) 1).eval (cubeRootTriple w 1)
      = 3 * cubeRootTriple w 1 ^ 2
    rw [cofactorPoly, Polynomial.eval_prod]
    have hset : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
    rw [hset, Finset.prod_insert (by decide), Finset.prod_singleton]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, cubeRootTriple,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    linear_combination -hw - hw3
  · show (cofactorPoly (cubeRootTriple w) 2).eval (cubeRootTriple w 2)
      = 3 * cubeRootTriple w 2 ^ 2
    rw [cofactorPoly, Polynomial.eval_prod]
    have hset : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
    rw [hset, Finset.prod_insert (by decide), Finset.prod_singleton]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, cubeRootTriple,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    linear_combination -hw + (-2 * w - 1) * hw3


omit [IsDiscreteValuationRing R] in
/-- **Card `(22)`.**  The equianharmonic multiplication matrix is the cyclic shift scaled by
three. -/
theorem residueMult_cubeRootTriple {w : R} (hw : w ^ 2 + w + 1 = 0)
    (hV : IsUnit (Matrix.vandermonde (cubeRootTriple w)).det) :
    residueMult (cubeRootTriple w)
      = Matrix.of ![![0, 3, 0], ![0, 0, 3], ![3, 0, 0]] := by
  refine (residueMult_eq_of_intertwine _ hV _ ?_).symm
  ext i q
  have hu3 : cubeRootTriple w i ^ 3 = 1 := cubeRootTriple_pow_three hw i
  rw [Matrix.mul_apply, Matrix.diagonal_mul, cofactorPoly_eval_cubeRootTriple hw,
    Fin.sum_univ_three]
  fin_cases q
  · simp [Matrix.vandermonde_apply]
    ring
  · simp [Matrix.vandermonde_apply]
    linear_combination -3 * hu3
  · simp [Matrix.vandermonde_apply]
    linear_combination -3 * cubeRootTriple w i * hu3


omit [IsDiscreteValuationRing R] in
/-- **Card `(22c)`, boxed.**  At the equianharmonic wall the second determinantal ideal of the
cotangent presentation is exactly `(c³)`, so the Kähler Smith type is the balanced
`R/(c³) ⊕ R/(c³)` rather than the generic `R/(c²) ⊕ R/(c⁴)`. -/
theorem detIdeal_two_cubeRootTriple (c : R) {w : R} (hw : w ^ 2 + w + 1 = 0)
    (hV : IsUnit (Matrix.vandermonde (cubeRootTriple w)).det) (h3 : IsUnit (3 : R)) :
    detIdeal (contactScale c (residueMult (cubeRootTriple w))) 2 = Ideal.span {c ^ 3} := by
  classical
  refine le_antisymm
    (detIdeal_two_le_of_triple_wall c _ (phaseSubdiscriminant_cubeRootTriple hw)) ?_
  have hmem := minor_mem_detIdeal (contactScale c (residueMult (cubeRootTriple w)))
    (![(0 : Fin 3), 2]) (![(0 : Fin 3), 1])
  rw [contactScale, det_submatrix_contactScale] at hmem
  have hexp : (∑ α : Fin 2, (3 - 1 - ((![(0 : Fin 3), 2] α : Fin 3) : ℕ)))
      + ∑ β : Fin 2, ((![(0 : Fin 3), 1] β : Fin 3) : ℕ) = 3 := by
    simp [Fin.sum_univ_two]
  have hminor : ((residueMult (cubeRootTriple w)).submatrix
      (![(0 : Fin 3), 2]) (![(0 : Fin 3), 1])).det = -9 := by
    rw [residueMult_cubeRootTriple hw hV, Matrix.det_fin_two]
    simp
    ring
  rw [hexp, hminor] at hmem
  have hunit : IsUnit ((-9 : R)) := by
    have h9 : IsUnit ((9 : R)) := by
      have : (9 : R) = 3 * 3 := by norm_num
      rw [this]
      exact h3.mul h3
    exact h9.neg
  obtain ⟨v, hv⟩ := hunit
  rw [Ideal.span_le]
  rintro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have := Ideal.mul_mem_left (detIdeal (contactScale c (residueMult (cubeRootTriple w))) 2)
    ((v⁻¹ : Rˣ) : R) hmem
  rwa [← hv, ← mul_assoc, mul_comm ((v⁻¹ : Rˣ) : R), mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, mul_one] at this


omit [IsDiscreteValuationRing R] in
/-- **Card `(22b)`, boxed.**  Off the wall the second determinantal ideal of the cotangent
presentation is `(c²)`, so the Kähler Smith type is the generic `R/(c²) ⊕ R/(c⁴)`. -/
theorem detIdeal_two_generic (c : R) (u : Fin 3 → R)
    (hH : IsUnit (phaseSubdiscriminant u 2)) :
    detIdeal (contactScale c (residueMult u)) 2 = Ideal.span {c ^ 2} := by
  have hswdet : IsUnit (((residueMult u).submatrix (southwestRows (by norm_num) 2)
      (Fin.castLE (by norm_num : (2 : ℕ) ≤ 3))).det) := by
    rwa [det_submatrix_residueMult_southwest u (by norm_num) (by norm_num)]
  have hsum : (∑ α : Fin 2, (α : ℕ)) = 1 := by simp [Fin.sum_univ_two]
  rw [detIdeal_contactScale c (residueMult u) (by norm_num) (by norm_num : (2 : ℕ) ≤ 3) hswdet,
    hsum]

end Equianharmonic


/-! ## The self-dual observer–cotangent sandwich -/

section Sandwich

variable {N : ℕ}

/-- The observer lattice `A = J(A) ⊆ R^N`. -/
noncomputable def observerLattice (x : Fin N → R) : Submodule R (Fin N → R) :=
  LinearMap.range (Matrix.vandermonde x).mulVecLin

/-- Multiplication by the sheet different. -/
noncomputable def differentDiag (x : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.diagonal fun i => (cofactorPoly x i).eval (x i)

omit [IsDiscreteValuationRing R] in
/-- **Card `(11a)`.**  The different carries the whole coordinate lattice into the observer
lattice: this is the inclusion `R^N ⊆ A^♯ = (P')⁻¹A`. -/
theorem range_differentDiag_le (x : Fin N → R) :
    LinearMap.range (differentDiag x).mulVecLin ≤ observerLattice x := by
  have h : differentDiag x = Matrix.vandermonde x * cofactorMatrix x := by
    rw [differentDiag, vandermonde_mul_cofactorMatrix]
  rw [h, Matrix.mulVecLin_mul, observerLattice]
  exact LinearMap.range_comp_le_range _ _

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The different image of the observer lattice sits inside the different image of the coordinate
lattice. -/
theorem map_differentDiag_mono (x : Fin N → R) :
    Submodule.map (differentDiag x).mulVecLin (observerLattice x)
      ≤ LinearMap.range (differentDiag x).mulVecLin := by
  rw [← Submodule.map_top]
  exact Submodule.map_mono le_top

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The induced map between quotients by nested submodules is surjective. -/
theorem mapQ_id_surjective {M : Type*} [AddCommGroup M] [Module R M] (S T : Submodule R M)
    (h : S ≤ T) :
    Function.Surjective (Submodule.mapQ S T LinearMap.id (by simpa using h)) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk z, rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Its kernel is the intermediate quotient. -/
theorem ker_mapQ_id {M : Type*} [AddCommGroup M] [Module R M] (S T : Submodule R M)
    (h : S ≤ T) :
    LinearMap.ker (Submodule.mapQ S T LinearMap.id (by simpa using h)) = T.map S.mkQ := by
  ext y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  constructor
  · intro hz
    have hz' : Submodule.Quotient.mk (p := T) z = 0 := hz
    rw [Submodule.Quotient.mk_eq_zero] at hz'
    exact ⟨z, hz', rfl⟩
  · rintro ⟨u, hu, huz⟩
    have hzu : z - u ∈ S := (Submodule.Quotient.eq S).1 huz.symm
    show Submodule.Quotient.mk (p := T) z = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have : z = u + (z - u) := by abel
    rw [this]
    exact T.add_mem hu (h hzu)


omit [IsDiscreteValuationRing R] in
/-- The different is injective when the sheets are distinct. -/
theorem differentDiag_injective (x : Fin N → R) (hx : Function.Injective x) :
    Function.Injective (differentDiag x).mulVecLin := by
  classical
  have hdet : (differentDiag x).det ≠ 0 := by
    rw [differentDiag, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [cofactorPoly, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
    have hij : j ≠ i := (Finset.mem_erase.mp hj).1
    have : Polynomial.eval (x i) (Polynomial.X - Polynomial.C (x j)) = x i - x j := by simp
    rw [this]
    exact sub_ne_zero.mpr fun h => hij (hx h).symm
  intro a b hab
  have h0 : (differentDiag x).mulVec (a - b) = 0 := by
    rw [Matrix.mulVec_sub]
    show (differentDiag x).mulVecLin a - (differentDiag x).mulVecLin b = 0
    rw [hab, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hdet h0)

omit [IsDiscreteValuationRing R] in
/-- **Card `(11b)`, the sub.**  Multiplication by the different identifies the observer defect
`C = R^N/A` with the sub `D·R^N / D·A` of the cotangent defect. -/
theorem ker_differentComp (x : Fin N → R) (hx : Function.Injective x) :
    LinearMap.ker ((Submodule.mkQ
        (Submodule.map (differentDiag x).mulVecLin (observerLattice x))).comp
      (differentDiag x).mulVecLin) = observerLattice x := by
  ext y
  constructor
  · intro hy
    have hy' : (differentDiag x).mulVecLin y
        ∈ Submodule.map (differentDiag x).mulVecLin (observerLattice x) := by
      have := hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at this
      exact this
    obtain ⟨a, ha, hae⟩ := hy'
    have : y = a := differentDiag_injective x hx hae.symm
    rw [this]
    exact ha
  · intro hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨y, hy, rfl⟩

/-- The different image of the observer lattice, inside the observer lattice. -/
noncomputable def differentSub (x : Fin N → R) : Submodule R ↥(observerLattice x) :=
  (Submodule.map (differentDiag x).mulVecLin (observerLattice x)).comap
    (observerLattice x).subtype

/-- The different image of the coordinate lattice, inside the observer lattice. -/
noncomputable def differentMid (x : Fin N → R) : Submodule R ↥(observerLattice x) :=
  (LinearMap.range (differentDiag x).mulVecLin).comap (observerLattice x).subtype

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem differentSub_le (x : Fin N → R) : differentSub x ≤ differentMid x :=
  Submodule.comap_mono (map_differentDiag_mono x)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(11b)`, boxed.**  The sandwich `D·A ⊆ D·R^N ⊆ A` yields the exact sequence
`0 → C → Ω → C† → 0`: the middle term `A/D·A` is the cotangent defect `Ω_{A/R} ≅ A/(P')A`, the sub
is the observer defect (identified by `ker_differentComp`) and the quotient is its trace dual. -/
theorem sandwich_exact (x : Fin N → R) :
    Function.Surjective (Submodule.mapQ (differentSub x) (differentMid x) LinearMap.id
        (by simpa using differentSub_le x))
      ∧ LinearMap.ker (Submodule.mapQ (differentSub x) (differentMid x) LinearMap.id
        (by simpa using differentSub_le x))
        = (differentMid x).map (differentSub x).mkQ :=
  ⟨mapQ_id_surjective _ _ (differentSub_le x), ker_mapQ_id _ _ (differentSub_le x)⟩

end Sandwich


/-! ## The fixed-radius wall criterion -/

section Radii

/-- **Card `(22d)`, the solvability step.**  Two nonnegative reals with prescribed sum of squares
and prescribed product exist exactly when the sum of squares is at least twice the product. -/
theorem exists_sq_add_sq_and_mul {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∃ x t : ℝ, 0 ≤ x ∧ 0 ≤ t ∧ x ^ 2 + t ^ 2 = A ∧ x * t = B) ↔ 2 * B ≤ A := by
  constructor
  · rintro ⟨x, t, hx, ht, hsum, hprod⟩
    nlinarith [sq_nonneg (x - t)]
  · intro hle
    have hAB : 4 * B ^ 2 ≤ A ^ 2 := by nlinarith
    set D : ℝ := Real.sqrt (A ^ 2 - 4 * B ^ 2) with hD
    have hDnn : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq : D ^ 2 = A ^ 2 - 4 * B ^ 2 := by
      rw [hD, Real.sq_sqrt (by linarith)]
    have hDA : D ≤ A := by nlinarith
    have hu1 : 0 ≤ (A + D) / 2 := by linarith
    have hu2 : 0 ≤ (A - D) / 2 := by linarith
    refine ⟨Real.sqrt ((A + D) / 2), Real.sqrt ((A - D) / 2), Real.sqrt_nonneg _,
      Real.sqrt_nonneg _, ?_, ?_⟩
    · rw [Real.sq_sqrt hu1, Real.sq_sqrt hu2]
      ring
    · rw [← Real.sqrt_mul hu1]
      have hprod : (A + D) / 2 * ((A - D) / 2) = B ^ 2 := by
        have : (A + D) * (A - D) = A ^ 2 - D ^ 2 := by ring
        rw [hDsq] at this
        nlinarith [this]
      rw [hprod, Real.sqrt_sq hB]


/-- **Card `(21)`.**  Primitive cube roots of unity exist. -/
theorem exists_primitiveCubeRoot : ∃ w : ℂ, w ^ 2 + w + 1 = 0 := by
  have hw := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / 3), ?_⟩
  have h3 : Complex.exp (2 * Real.pi * Complex.I / 3) ^ 3 = 1 := hw.pow_eq_one
  have hne : Complex.exp (2 * Real.pi * Complex.I / 3) ≠ 1 := hw.ne_one (by norm_num)
  have hfac : (Complex.exp (2 * Real.pi * Complex.I / 3) - 1)
      * (Complex.exp (2 * Real.pi * Complex.I / 3) ^ 2
        + Complex.exp (2 * Real.pi * Complex.I / 3) + 1) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- **Card `(21)`.**  A primitive cube root of unity has real part `−1/2` and imaginary part of
square `3/4`. -/
theorem cubeRoot_re_im {w : ℂ} (hw : w ^ 2 + w + 1 = 0) :
    w.re = -1 / 2 ∧ w.im ^ 2 = 3 / 4 := by
  have hre : w.re ^ 2 - w.im ^ 2 + w.re + 1 = 0 := by
    have h := congrArg Complex.re hw
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, pow_two, Complex.zero_re] at h
    linear_combination h
  have him : 2 * (w.re * w.im) + w.im = 0 := by
    have h := congrArg Complex.im hw
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, pow_two, Complex.zero_im] at h
    linear_combination h
  have hfac : w.im * (2 * w.re + 1) = 0 := by linear_combination him
  rcases mul_eq_zero.mp hfac with h | h
  · exfalso
    rw [h] at hre
    nlinarith [sq_nonneg (w.re + 1 / 2)]
  · constructor
    · linarith
    · have hr : w.re = -1 / 2 := by linarith
      rw [hr] at hre
      nlinarith [hre]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Card `(22d)`.**  Every affine equilateral triple lies on the wall. -/
theorem phaseSubdiscriminant_equilateral {w : R} (hw : w ^ 2 + w + 1 = 0) (m s : R) :
    phaseSubdiscriminant ![m + s, m + s * w, m + s * w ^ 2] 2 = 0 := by
  rw [phaseSubdiscriminant_two_triple]
  show 3 * ((m + s) ^ 2 + (m + s * w) ^ 2 + (m + s * w ^ 2) ^ 2)
    - ((m + s) + (m + s * w) + (m + s * w ^ 2)) ^ 2 = 0
  linear_combination (s ^ 2 * (2 * w ^ 2 - 4 * w + 2)) * hw


/-- A primitive cube root of unity has modulus one. -/
theorem normSq_cubeRoot {w : ℂ} (hw : w ^ 2 + w + 1 = 0) : Complex.normSq w = 1 := by
  obtain ⟨hre, him⟩ := cubeRoot_re_im hw
  rw [Complex.normSq_apply, hre]
  nlinarith [him]

/-- **Card `(22d)`.**  The three centred real parts of a rotated complex number have sum of squares
`3/2` times its norm square. -/
theorem sum_re_sq_cubeRoot {w : ℂ} (hw : w ^ 2 + w + 1 = 0) (q : ℂ) :
    q.re ^ 2 + (q * (starRingEnd ℂ) w).re ^ 2
        + (q * (starRingEnd ℂ) (w ^ 2)).re ^ 2
      = 3 / 2 * Complex.normSq q := by
  obtain ⟨hre, him⟩ := cubeRoot_re_im hw
  have hw2re : (w ^ 2).re = -1 / 2 := by
    have h : w ^ 2 = -w - 1 := by linear_combination hw
    rw [h]
    simp [hre]
    linarith
  have hw2im : (w ^ 2).im = -w.im := by
    have h : w ^ 2 = -w - 1 := by linear_combination hw
    rw [h]
    simp
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hre, hw2re, hw2im,
    Complex.normSq_apply]
  nlinarith [him]


/-- The modulus expansion of an equilateral vertex. -/
theorem normSq_equilateral {w : ℂ} (hw : w ^ 2 + w + 1 = 0) (m s : ℂ) (n : ℕ) :
    Complex.normSq (m + s * w ^ n)
      = Complex.normSq m + Complex.normSq s
        + 2 * ((m * (starRingEnd ℂ) s) * (starRingEnd ℂ) (w ^ n)).re := by
  rw [Complex.normSq_add, Complex.normSq_mul, map_pow, normSq_cubeRoot hw, one_pow, mul_one,
    map_mul, ← mul_assoc]

/-- The three rotated real parts sum to zero. -/
theorem sum_re_cubeRoot_eq_zero {w : ℂ} (hw : w ^ 2 + w + 1 = 0) (q : ℂ) :
    (q * (starRingEnd ℂ) (w ^ (0 : ℕ))).re + (q * (starRingEnd ℂ) (w ^ (1 : ℕ))).re
      + (q * (starRingEnd ℂ) (w ^ (2 : ℕ))).re = 0 := by
  have h : q * (starRingEnd ℂ) (w ^ (0 : ℕ)) + q * (starRingEnd ℂ) (w ^ (1 : ℕ))
      + q * (starRingEnd ℂ) (w ^ (2 : ℕ)) = q * (starRingEnd ℂ) (w ^ 2 + w + 1) := by
    rw [map_add, map_add]
    ring
  rw [hw, map_zero, mul_zero] at h
  have h2 := congrArg Complex.re h
  simpa using h2

/-- **Card `(22d)`, forward.**  Any equilateral triple of positive radii satisfies the
criterion. -/
theorem wall_radii_forward {w : ℂ} (hw : w ^ 2 + w + 1 = 0) {y : Fin 3 → ℝ}
    (m s : ℂ) (hms : ∀ i : Fin 3, Complex.normSq (m + s * w ^ (i : ℕ)) = y i) :
    2 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) ≤ (y 0 + y 1 + y 2) ^ 2 := by
  set X := Complex.normSq m with hX
  set T := Complex.normSq s with hT
  set q := m * (starRingEnd ℂ) s with hq
  have hy : ∀ n : ℕ, Complex.normSq (m + s * w ^ n)
      = X + T + 2 * (q * (starRingEnd ℂ) (w ^ n)).re := fun n => normSq_equilateral hw m s n
  have h0 : y 0 = X + T + 2 * (q * (starRingEnd ℂ) (w ^ (0 : ℕ))).re := by
    rw [← hms 0]; exact hy 0
  have h1 : y 1 = X + T + 2 * (q * (starRingEnd ℂ) (w ^ (1 : ℕ))).re := by
    rw [← hms 1]; exact hy 1
  have h2 : y 2 = X + T + 2 * (q * (starRingEnd ℂ) (w ^ (2 : ℕ))).re := by
    rw [← hms 2]; exact hy 2
  have hsum := sum_re_cubeRoot_eq_zero hw q
  have hsq := sum_re_sq_cubeRoot hw q
  have hqnorm : Complex.normSq q = X * T := by
    rw [hq, Complex.normSq_mul, Complex.normSq_conj]
  have hr0 : (q * (starRingEnd ℂ) (w ^ (0 : ℕ))).re = q.re := by
    rw [pow_zero, map_one, mul_one]
  have hsq' : q.re ^ 2 + (q * (starRingEnd ℂ) (w ^ (1 : ℕ))).re ^ 2
      + (q * (starRingEnd ℂ) (w ^ (2 : ℕ))).re ^ 2 = 3 / 2 * (X * T) := by
    rw [← hqnorm, pow_one]
    exact hsq
  rw [hr0] at hsum h0
  set a := q.re with ha
  set b := (q * (starRingEnd ℂ) (w ^ (1 : ℕ))).re with hb
  set c := (q * (starRingEnd ℂ) (w ^ (2 : ℕ))).re with hc
  have hgoal : (y 0 + y 1 + y 2) ^ 2 - 2 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) = 3 * (X - T) ^ 2 := by
    rw [h0, h1, h2]
    linear_combination (-8 : ℝ) * hsq' + (4 * (X + T) + 4 * (a + b + c)) * hsum
  linarith [sq_nonneg (X - T), hgoal]


/-- The conjugate of a primitive cube root is its square. -/
theorem conj_cubeRoot {w : ℂ} (hw : w ^ 2 + w + 1 = 0) : (starRingEnd ℂ) w = w ^ 2 := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have h1 : w * (starRingEnd ℂ) w = (Complex.normSq w : ℂ) := Complex.mul_conj w
  rw [normSq_cubeRoot hw] at h1
  have hw3 : w * w ^ 2 = 1 := by linear_combination (w - 1) * hw
  refine mul_left_cancel₀ hwne ?_
  rw [h1, hw3]
  norm_num

/-- The interpolating rotation of a zero-sum real triple. -/
noncomputable def rotationOfDefect (w : ℂ) (d : Fin 3 → ℝ) : ℂ :=
  ((1 / 3 : ℝ) : ℂ) * ((d 0 : ℂ) + (d 1 : ℂ) * w + (d 2 : ℂ) * w ^ 2)

/-- **Card `(22d)`.**  The interpolating rotation reproduces the prescribed centred radii. -/
theorem two_re_rotationOfDefect {w : ℂ} (hw : w ^ 2 + w + 1 = 0) {d : Fin 3 → ℝ}
    (hd : d 0 + d 1 + d 2 = 0) (n : Fin 3) :
    2 * ((rotationOfDefect w d) * (starRingEnd ℂ) (w ^ (n : ℕ))).re = d n := by
  obtain ⟨hre, him⟩ := cubeRoot_re_im hw
  have hconj : (starRingEnd ℂ) w = w ^ 2 := conj_cubeRoot hw
  have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  have hw2re : (w ^ 2).re = -1 / 2 := by
    have h : w ^ 2 = -w - 1 := by linear_combination hw
    rw [h]
    simp [hre]
    linarith
  have hw2im : (w ^ 2).im = -w.im := by
    have h : w ^ 2 = -w - 1 := by linear_combination hw
    rw [h]
    simp
  have hsimp : ∀ e0 e1 e2 : ℝ,
      2 * (((1 / 3 : ℝ) : ℂ) * ((e0 : ℂ) + (e1 : ℂ) * w + (e2 : ℂ) * w ^ 2)).re
        = 2 * ((1 / 3 : ℝ) * (e0 + e1 * (-1 / 2) + e2 * (-1 / 2))) := by
    intro e0 e1 e2
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, hre, hw2re, hw2im]
    ring
  fin_cases n
  · show 2 * ((rotationOfDefect w d) * (starRingEnd ℂ) (w ^ (0 : ℕ))).re = d 0
    rw [pow_zero, map_one, mul_one, rotationOfDefect, hsimp]
    linarith
  · show 2 * ((rotationOfDefect w d) * (starRingEnd ℂ) (w ^ (1 : ℕ))).re = d 1
    rw [pow_one, hconj, rotationOfDefect]
    have hexp : ((1 / 3 : ℝ) : ℂ) * ((d 0 : ℂ) + (d 1 : ℂ) * w + (d 2 : ℂ) * w ^ 2) * w ^ 2
        = ((1 / 3 : ℝ) : ℂ) * ((d 1 : ℂ) + (d 2 : ℂ) * w + (d 0 : ℂ) * w ^ 2) := by
      push_cast
      linear_combination ((1 / 3 : ℂ) * ((d 1 : ℂ) + (d 2 : ℂ) * w)) * hw3
    rw [hexp, hsimp]
    linarith
  · show 2 * ((rotationOfDefect w d) * (starRingEnd ℂ) (w ^ (2 : ℕ))).re = d 2
    rw [map_pow, hconj, rotationOfDefect]
    have hexp : ((1 / 3 : ℝ) : ℂ) * ((d 0 : ℂ) + (d 1 : ℂ) * w + (d 2 : ℂ) * w ^ 2) * (w ^ 2) ^ 2
        = ((1 / 3 : ℝ) : ℂ) * ((d 2 : ℂ) + (d 0 : ℂ) * w + (d 1 : ℂ) * w ^ 2) := by
      push_cast
      linear_combination ((1 / 3 : ℂ) * ((d 0 : ℂ) * w + (d 1 : ℂ) * w ^ 2
        + (d 2 : ℂ) * (w ^ 3 + 1))) * hw3
    rw [hexp, hsimp]
    linarith


/-- **Card `(22d)`, boxed.**  Positive radii admit an equilateral realisation — that is, phases
putting the three nodes on the wall — exactly when `(∑ρ²)² ≥ 2∑ρ⁴`. -/
theorem wall_radii_criterion {w : ℂ} (hw : w ^ 2 + w + 1 = 0) {y : Fin 3 → ℝ}
    (hy : ∀ i, 0 < y i) :
    (∃ m s : ℂ, s ≠ 0 ∧ ∀ i : Fin 3, Complex.normSq (m + s * w ^ (i : ℕ)) = y i)
      ↔ 2 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) ≤ (y 0 + y 1 + y 2) ^ 2 := by
  constructor
  · rintro ⟨m, s, -, hms⟩
    exact wall_radii_forward hw m s hms
  · intro hcrit
    set A : ℝ := (y 0 + y 1 + y 2) / 3 with hAdef
    have hA : 0 < A := by
      have := hy 0; have := hy 1; have := hy 2
      simp only [hAdef]
      linarith [hy 0, hy 1, hy 2]
    set d : Fin 3 → ℝ := fun i => y i - A with hddef
    have hd : d 0 + d 1 + d 2 = 0 := by
      simp only [hddef, hAdef]
      ring
    set q : ℂ := rotationOfDefect w d with hqdef
    have hq2 : ∀ n : Fin 3, 2 * (q * (starRingEnd ℂ) (w ^ (n : ℕ))).re = d n :=
      two_re_rotationOfDefect hw hd
    have hr0 : (q * (starRingEnd ℂ) (w ^ (0 : ℕ))).re = q.re := by
      rw [pow_zero, map_one, mul_one]
    have hqnorm : Complex.normSq q = (d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2) / 6 := by
      have hsq := sum_re_sq_cubeRoot hw q
      have e0 := hq2 0
      have e1 := hq2 1
      have e2 := hq2 2
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
      rw [hr0] at e0
      rw [pow_one] at e1
      have h0 : q.re = d 0 / 2 := by linarith
      have h1 : (q * (starRingEnd ℂ) w).re = d 1 / 2 := by linarith
      have h2 : (q * (starRingEnd ℂ) (w ^ 2)).re = d 2 / 2 := by linarith
      rw [h0, h1, h2] at hsq
      linarith
    have hsumd : d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 ≤ 3 / 2 * A ^ 2 := by
      simp only [hddef, hAdef] at *
      nlinarith [hcrit]
    set B : ℝ := Real.sqrt (Complex.normSq q) with hBdef
    have hBnn : 0 ≤ B := Real.sqrt_nonneg _
    have hB2 : B ^ 2 = Complex.normSq q := Real.sq_sqrt (Complex.normSq_nonneg q)
    have hAB : 2 * B ≤ A := by
      nlinarith [hB2, hqnorm, hsumd, hBnn, hA]
    obtain ⟨x, t, hx, ht, hxt, hxtB⟩ :=
      (exists_sq_add_sq_and_mul hA.le hBnn).2 hAB
    by_cases hq0 : q = 0
    · have hdzero : ∀ n : Fin 3, d n = 0 := by
        intro n
        rw [← hq2 n, hq0]
        simp
      refine ⟨0, ((Real.sqrt A : ℝ) : ℂ), ?_, ?_⟩
      · simp only [ne_eq, Complex.ofReal_eq_zero]
        exact (Real.sqrt_pos.mpr hA).ne'
      · intro i
        have hyi : y i = A := by
          have := hdzero i
          simp only [hddef] at this
          linarith
        rw [zero_add, Complex.normSq_mul, map_pow, normSq_cubeRoot hw, one_pow, mul_one,
          Complex.normSq_ofReal, hyi]
        exact Real.mul_self_sqrt hA.le
    · have hBpos : 0 < B := by
        rw [hBdef]
        refine Real.sqrt_pos.mpr ?_
        exact (Complex.normSq_pos).mpr hq0
      have htpos : 0 < t := by
        rcases lt_or_eq_of_le ht with h | h
        · exact h
        · exfalso
          rw [← h, mul_zero] at hxtB
          exact absurd hxtB.symm hBpos.ne'
      refine ⟨((x / B : ℝ) : ℂ) * q, ((t : ℝ) : ℂ), ?_, ?_⟩
      · simp only [ne_eq, Complex.ofReal_eq_zero]
        exact htpos.ne'
      · intro i
        have hmconj : (((x / B : ℝ) : ℂ) * q) * (starRingEnd ℂ) ((t : ℝ) : ℂ) = q := by
          rw [Complex.conj_ofReal]
          have : ((x / B : ℝ) : ℂ) * ((t : ℝ) : ℂ) = 1 := by
            rw [← Complex.ofReal_mul, div_mul_eq_mul_div, hxtB, div_self hBpos.ne']
            simp
          calc ((x / B : ℝ) : ℂ) * q * ((t : ℝ) : ℂ)
              = (((x / B : ℝ) : ℂ) * ((t : ℝ) : ℂ)) * q := by ring
            _ = q := by rw [this, one_mul]
        have hnormm : Complex.normSq (((x / B : ℝ) : ℂ) * q) = x ^ 2 := by
          rw [Complex.normSq_mul, Complex.normSq_ofReal, ← hB2]
          field_simp
        rw [normSq_equilateral hw, hnormm, Complex.normSq_ofReal, hmconj]
        have hqi := hq2 i
        simp only [hddef] at hqi
        linarith [hxt, hqi]

end Radii


/-! ## The literal prime-phase wall -/

section PrimePhase

/-- An ordered triple with the largest term below the sum of the other two satisfies the
criterion. -/
theorem criterion_of_ordered {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hca : c < 2 * a) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (a + b + c) ^ 2 := by
  have h1 : 0 < a + b - c := by linarith
  have h2 : a + b - c ≤ a := by linarith
  have h3 : (a + b - c) ^ 2 ≤ a ^ 2 := by nlinarith
  have h4 : a ^ 2 ≤ 4 * (a * b) := by nlinarith
  nlinarith [h3, h4]

/-- **Card `(22g)`.**  The prime triple `(101, 103, 107)` satisfies the fixed-radius criterion:
its log-radii admit an equilateral realisation. -/
theorem primeTriple_criterion :
    2 * (((Real.log 101) ^ 2) ^ 2 + ((Real.log 103) ^ 2) ^ 2 + ((Real.log 107) ^ 2) ^ 2)
      ≤ ((Real.log 101) ^ 2 + (Real.log 103) ^ 2 + (Real.log 107) ^ 2) ^ 2 := by
  have h101 : (0 : ℝ) < Real.log 101 := Real.log_pos (by norm_num)
  have h103 : Real.log 101 ≤ Real.log 103 := Real.log_le_log (by norm_num) (by norm_num)
  have h107 : Real.log 103 ≤ Real.log 107 := Real.log_le_log (by norm_num) (by norm_num)
  have hlog : 3 * Real.log 107 < 4 * Real.log 101 := by
    have h1 : Real.log ((107 : ℝ) ^ (3 : ℕ)) < Real.log ((101 : ℝ) ^ (4 : ℕ)) :=
      Real.log_lt_log (by positivity) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  refine criterion_of_ordered (by positivity) ?_ ?_ ?_
  · nlinarith [h101, h103]
  · nlinarith [h101, h103, h107]
  · nlinarith [h101, hlog]


/-- The second phase subdiscriminant is Lipschitz on a polydisc. -/
theorem norm_phaseSubdiscriminant_sub_le {z z' : Fin 3 → ℂ} {M d : ℝ}
    (hM : ∀ i, ‖z i‖ ≤ M) (hM' : ∀ i, ‖z' i‖ ≤ M) (hd : ∀ i, ‖z i - z' i‖ ≤ d)
    (hMnn : 0 ≤ M) :
    ‖phaseSubdiscriminant z 2 - phaseSubdiscriminant z' 2‖ ≤ 36 * M * d := by
  rw [phaseSubdiscriminant_two_triple, phaseSubdiscriminant_two_triple]
  have key : 3 * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) - (z 0 + z 1 + z 2) ^ 2
      - (3 * (z' 0 ^ 2 + z' 1 ^ 2 + z' 2 ^ 2) - (z' 0 + z' 1 + z' 2) ^ 2)
      = 3 * ((z 0 + z' 0) * (z 0 - z' 0) + (z 1 + z' 1) * (z 1 - z' 1)
          + (z 2 + z' 2) * (z 2 - z' 2))
        - (z 0 + z 1 + z 2 + (z' 0 + z' 1 + z' 2))
          * (z 0 - z' 0 + (z 1 - z' 1) + (z 2 - z' 2)) := by
    ring
  rw [key]
  have hpair : ∀ i, ‖(z i + z' i) * (z i - z' i)‖ ≤ 2 * M * d := by
    intro i
    rw [norm_mul]
    refine mul_le_mul (le_trans (norm_add_le _ _) (by linarith [hM i, hM' i])) (hd i)
      (norm_nonneg _) (by linarith)
  have hA : ‖(z 0 + z' 0) * (z 0 - z' 0) + (z 1 + z' 1) * (z 1 - z' 1)
      + (z 2 + z' 2) * (z 2 - z' 2)‖ ≤ 6 * M * d := by
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    linarith [hpair 0, hpair 1, hpair 2]
  have hB : ‖z 0 + z 1 + z 2 + (z' 0 + z' 1 + z' 2)‖ ≤ 6 * M := by
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖z 0 + z 1 + z 2‖ ≤ 3 * M := by
      refine le_trans (norm_add_le _ _) ?_
      refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
      linarith [hM 0, hM 1, hM 2]
    have h2 : ‖z' 0 + z' 1 + z' 2‖ ≤ 3 * M := by
      refine le_trans (norm_add_le _ _) ?_
      refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
      linarith [hM' 0, hM' 1, hM' 2]
    linarith
  have hC : ‖z 0 - z' 0 + (z 1 - z' 1) + (z 2 - z' 2)‖ ≤ 3 * d := by
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    linarith [hd 0, hd 1, hd 2]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul, norm_mul]
  have h3 : ‖(3 : ℂ)‖ = 3 := by simp
  rw [h3]
  have hBC : ‖z 0 + z 1 + z 2 + (z' 0 + z' 1 + z' 2)‖
      * ‖z 0 - z' 0 + (z 1 - z' 1) + (z 2 - z' 2)‖ ≤ (6 * M) * (3 * d) :=
    mul_le_mul hB hC (norm_nonneg _) (by linarith)
  nlinarith [hA, hBC, hMnn]


/-- The literal prime triple of the card. -/
def primeTripleIdx : Fin 3 → Nat.Primes :=
  ![⟨101, by norm_num⟩, ⟨103, by norm_num⟩, ⟨107, by norm_num⟩]

theorem primeTripleIdx_injective : Function.Injective primeTripleIdx := by
  intro a b hab
  have h : ((primeTripleIdx a : Nat.Primes) : ℕ) = ((primeTripleIdx b : Nat.Primes) : ℕ) := by
    rw [hab]
  clear hab
  fin_cases a <;> fin_cases b <;> simp_all [primeTripleIdx]

/-- The literal prime log radii. -/
noncomputable def primeLogRadius (i : Fin 3) : ℝ := Real.log ((primeTripleIdx i : ℕ) : ℝ)

theorem primeLogRadius_zero : primeLogRadius 0 = Real.log 101 := by
  rw [primeLogRadius]
  norm_num [primeTripleIdx, Matrix.cons_val_zero]

theorem primeLogRadius_one : primeLogRadius 1 = Real.log 103 := by
  rw [primeLogRadius]
  norm_num [primeTripleIdx, Matrix.cons_val_one, Matrix.head_cons]

theorem primeLogRadius_two : primeLogRadius 2 = Real.log 107 := by
  rw [primeLogRadius]
  norm_num [primeTripleIdx, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

theorem primeLogRadius_pos (i : Fin 3) : 0 < primeLogRadius i := by
  fin_cases i
  · rw [show ((⟨0, by norm_num⟩ : Fin 3)) = (0 : Fin 3) from rfl, primeLogRadius_zero]
    exact Real.log_pos (by norm_num)
  · rw [show ((⟨1, by norm_num⟩ : Fin 3)) = (1 : Fin 3) from rfl, primeLogRadius_one]
    exact Real.log_pos (by norm_num)
  · rw [show ((⟨2, by norm_num⟩ : Fin 3)) = (2 : Fin 3) from rfl, primeLogRadius_two]
    exact Real.log_pos (by norm_num)

theorem primeLogRadius_le (i : Fin 3) : primeLogRadius i ≤ Real.log 107 := by
  fin_cases i
  · rw [show ((⟨0, by norm_num⟩ : Fin 3)) = (0 : Fin 3) from rfl, primeLogRadius_zero]
    exact Real.log_le_log (by norm_num) (by norm_num)
  · rw [show ((⟨1, by norm_num⟩ : Fin 3)) = (1 : Fin 3) from rfl, primeLogRadius_one]
    exact Real.log_le_log (by norm_num) (by norm_num)
  · rw [show ((⟨2, by norm_num⟩ : Fin 3)) = (2 : Fin 3) from rfl, primeLogRadius_two]

/-- **Card `(22f)`.**  The prime log frequencies are rationally independent, so the one-clock orbit
is dense in the torus. -/
theorem linearIndependent_primeLogRadius : LinearIndependent ℚ primeLogRadius :=
  (GaloisForLFunctions.linearIndependent_log_primes).comp primeTripleIdx primeTripleIdx_injective

/-- **Card `(22g)`.**  The prime log radii are realised by a wall configuration. -/
theorem exists_primeWall :
    ∃ z : Fin 3 → ℂ, (∀ i, ‖z i‖ = primeLogRadius i) ∧ phaseSubdiscriminant z 2 = 0 := by
  obtain ⟨w, hw⟩ := exists_primitiveCubeRoot
  have hy : ∀ i : Fin 3, 0 < (primeLogRadius i) ^ 2 := fun i => by
    have := primeLogRadius_pos i
    positivity
  have hcrit : 2 * (((primeLogRadius 0) ^ 2) ^ 2 + ((primeLogRadius 1) ^ 2) ^ 2
      + ((primeLogRadius 2) ^ 2) ^ 2)
      ≤ ((primeLogRadius 0) ^ 2 + (primeLogRadius 1) ^ 2 + (primeLogRadius 2) ^ 2) ^ 2 := by
    rw [primeLogRadius_zero, primeLogRadius_one, primeLogRadius_two]
    exact primeTriple_criterion
  obtain ⟨m, s, -, hms⟩ := (wall_radii_criterion hw hy).2 hcrit
  refine ⟨fun i => m + s * w ^ (i : ℕ), fun i => ?_, ?_⟩
  · have h := hms i
    rw [Complex.norm_def, h, Real.sqrt_sq (primeLogRadius_pos i).le]
  · have hz : (fun i : Fin 3 => m + s * w ^ (i : ℕ))
        = ![m + s, m + s * w, m + s * w ^ 2] := by
      funext i
      fin_cases i <;> simp
    rw [hz]
    exact phaseSubdiscriminant_equilateral hw m s

/-- **Cards `(22g)`, `(22h)`, boxed.**  The one-clock prime orbit approaches the balanced phase
wall arbitrarily closely: the infimum over time of the second phase subdiscriminant is zero. -/
theorem primeOrbit_approaches_wall (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, ‖phaseSubdiscriminant
      (fun i => (primeLogRadius i : ℂ) * GaloisForLFunctions.expChar (primeLogRadius i) t) 2‖
        < ε := by
  obtain ⟨z, hznorm, hzwall⟩ := exists_primeWall
  set M : ℝ := Real.log 107 with hMdef
  have hMpos : 0 < M := Real.log_pos (by norm_num)
  set e : ℝ := ε / (36 * M * M + 1) with hedef
  have hepos : 0 < e := by
    refine div_pos hε ?_
    positivity
  obtain ⟨t, ht⟩ :=
    GaloisForLFunctions.kronecker_approx linearIndependent_primeLogRadius
      (fun i => (z i).arg) hepos
  refine ⟨t, ?_⟩
  have hzform : ∀ i, z i = (primeLogRadius i : ℂ) * Complex.exp (((z i).arg : ℝ) * Complex.I) := by
    intro i
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (z i)]
    rw [hznorm i]
  have hM1 : ∀ i, ‖(primeLogRadius i : ℂ)
      * GaloisForLFunctions.expChar (primeLogRadius i) t‖ ≤ M := by
    intro i
    rw [norm_mul, GaloisForLFunctions.expChar, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (primeLogRadius_pos i)]
    exact primeLogRadius_le i
  have hM2 : ∀ i, ‖z i‖ ≤ M := fun i => by rw [hznorm i]; exact primeLogRadius_le i
  have hdiff : ∀ i, ‖(primeLogRadius i : ℂ)
      * GaloisForLFunctions.expChar (primeLogRadius i) t - z i‖ ≤ M * e := by
    intro i
    rw [hzform i, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (primeLogRadius_pos i)]
    exact mul_le_mul (primeLogRadius_le i) (le_of_lt (ht i)) (norm_nonneg _) hMpos.le
  have hlip := norm_phaseSubdiscriminant_sub_le hM1 hM2 hdiff hMpos.le
  rw [hzwall, sub_zero] at hlip
  refine lt_of_le_of_lt hlip ?_
  rw [hedef]
  rw [show 36 * M * (M * (ε / (36 * M * M + 1))) = (36 * M * M) * ε / (36 * M * M + 1) by ring]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [hε, hMpos]

end PrimePhase





end HTGeometry.ConstraintRelativity
