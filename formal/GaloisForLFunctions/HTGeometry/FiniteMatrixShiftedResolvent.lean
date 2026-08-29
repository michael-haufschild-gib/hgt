import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-!
# Finite Hermitian shifted resolvents

Spectral formulas and positivity facts for regularized inverses of finite Hermitian matrices.
These lemmas isolate the finite-dimensional cutoff calculus used in matrix-valued Ward limits.
-/

open scoped Matrix ComplexOrder
open Filter Matrix Set
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real trace pairing of two positive-semidefinite matrices on any finite index type is
nonnegative. -/
theorem fintypeMatrix_re_trace_mul_nonneg_of_posSemidef
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ((A * B).trace).re := by
  let U : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let D : Matrix n n ℂ :=
    diagonal (fun i => (hB.isHermitian.eigenvalues i : ℂ))
  let C : Matrix n n ℂ := Uᴴ * A * U
  have hspec : B = U * D * Uᴴ := by
    simpa [U, D, Matrix.star_eq_conjTranspose] using
      isHermitian_eq_conj_diagonal hB.isHermitian
  have hC : C.PosSemidef := by
    simpa [C, Matrix.conjTranspose_conjTranspose] using
      hA.mul_mul_conjTranspose_same Uᴴ
  have htraceEq : (A * B).trace = (C * D).trace := by
    rw [hspec]
    calc
      (A * (U * D * Uᴴ)).trace = ((D * Uᴴ) * A * U).trace := by
        rw [show A * (U * D * Uᴴ) = (A * U) * (D * Uᴴ) by noncomm_ring,
          Matrix.trace_mul_comm]
        congr 1; noncomm_ring
      _ = (D * C).trace := by congr 1; simp [C, Matrix.mul_assoc]
      _ = (C * D).trace := Matrix.trace_mul_comm D C
  rw [htraceEq]
  have htrace : 0 ≤ (C * D).trace := by
    rw [Matrix.trace]
    apply Finset.sum_nonneg
    intro i _hi
    simp only [Matrix.diag_apply, Matrix.mul_apply, D, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp only [if_pos]
      exact mul_nonneg hC.diag_nonneg (by
        exact_mod_cast hB.eigenvalues_nonneg i)
    · intro j _hj hji
      simp [hji]
    · intro hi
      simp at hi
  exact (RCLike.nonneg_iff.mp htrace).1

/-- Spectral formula for a real scalar shift of a finite Hermitian matrix. -/
theorem shiftedHermitian_inv_eq_spectral {H : Matrix n n ℂ} (hH : H.IsHermitian) (c : ℝ)
    (hc : ∀ i, hH.eigenvalues i + c ≠ 0) :
    (H + (c : ℂ) • (1 : Matrix n n ℂ))⁻¹ =
      (hH.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => (((hH.eigenvalues i + c)⁻¹ : ℝ) : ℂ)) *
        (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  change (H + (c : ℂ) • (1 : Matrix n n ℂ))⁻¹ =
    U * diagonal (fun i => (((hH.eigenvalues i + c)⁻¹ : ℝ) : ℂ)) * Uᴴ
  apply Matrix.inv_eq_right_inv
  have hspec : H =
      U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ := by
    simpa [U, Matrix.star_eq_conjTranspose] using isHermitian_eq_conj_diagonal hH
  have hUU : Uᴴ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.mem_iff.mp hH.eigenvectorUnitary.property).1
  have hUU' : U * Uᴴ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.mem_iff.mp hH.eigenvectorUnitary.property).2
  have hshift :
      U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ +
          (c : ℂ) • (1 : Matrix n n ℂ) =
        U * diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ)) * Uᴴ := by
    calc
      U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ +
          (c : ℂ) • (1 : Matrix n n ℂ) =
        U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ +
          (c : ℂ) • (U * Uᴴ) := by rw [hUU']
      _ = U * (diagonal (fun i => (hH.eigenvalues i : ℂ)) +
          (c : ℂ) • (1 : Matrix n n ℂ)) * Uᴴ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul]
      _ = U * diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ)) * Uᴴ := by
        congr 2
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
  have hshiftH : H + (c : ℂ) • (1 : Matrix n n ℂ) =
      U * diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ)) * Uᴴ :=
    (congrArg (fun Z => Z + (c : ℂ) • (1 : Matrix n n ℂ)) hspec).trans hshift
  rw [hshiftH]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc
      (U * diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ))) Uᴴ U,
    show Uᴴ * U = 1 from hUU, Matrix.mul_one,
    Matrix.mul_assoc U
      (diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ)))
      (diagonal (fun i => (((hH.eigenvalues i + c)⁻¹ : ℝ) : ℂ))),
    Matrix.diagonal_mul_diagonal]
  have hdiag :
      diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ) *
        (((hH.eigenvalues i + c)⁻¹ : ℝ) : ℂ)) = (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq, one_apply_eq, Complex.ofReal_inv,
        Complex.ofReal_add]
      exact mul_inv_cancel₀ (by exact_mod_cast hc i)
    · simp [hij]
  rw [hdiag, Matrix.mul_one, hUU']

/-- A positive shift of a positive-semidefinite Hermitian matrix has positive-semidefinite inverse. -/
theorem shiftedPosSemidef_inv_posSemidef {H : Matrix n n ℂ} (hH : H.PosSemidef) {c : ℝ}
    (hc : 0 < c) :
    (H + (c : ℂ) • (1 : Matrix n n ℂ))⁻¹ |>.PosSemidef := by
  rw [shiftedHermitian_inv_eq_spectral hH.isHermitian c fun i =>
    ne_of_gt (add_pos_of_nonneg_of_pos (hH.eigenvalues_nonneg i) hc)]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (((hH.isHermitian.eigenvalues i + c)⁻¹ : ℝ) : ℂ)
  exact_mod_cast inv_nonneg.mpr
    (add_nonneg (hH.eigenvalues_nonneg i) hc.le)

/-- Shifted inverses are antitone in the positive scalar regularization. -/
theorem shiftedPosSemidef_inv_sub_posSemidef {H : Matrix n n ℂ} (hH : H.PosSemidef)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ((H + (a : ℂ) • (1 : Matrix n n ℂ))⁻¹ -
      (H + (b : ℂ) • (1 : Matrix n n ℂ))⁻¹).PosSemidef := by
  let U : Matrix n n ℂ := hH.isHermitian.eigenvectorUnitary
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [shiftedHermitian_inv_eq_spectral hH.isHermitian a fun i =>
      ne_of_gt (add_pos_of_nonneg_of_pos (hH.eigenvalues_nonneg i) ha),
    shiftedHermitian_inv_eq_spectral hH.isHermitian b fun i =>
      ne_of_gt (add_pos_of_nonneg_of_pos (hH.eigenvalues_nonneg i) hb)]
  change (U * diagonal (fun i => (((hH.isHermitian.eigenvalues i + a)⁻¹ : ℝ) : ℂ)) * Uᴴ -
    U * diagonal (fun i => (((hH.isHermitian.eigenvalues i + b)⁻¹ : ℝ) : ℂ)) * Uᴴ).PosSemidef
  have hfactor :
      U * diagonal (fun i => (((hH.isHermitian.eigenvalues i + a)⁻¹ : ℝ) : ℂ)) * Uᴴ -
          U * diagonal (fun i => (((hH.isHermitian.eigenvalues i + b)⁻¹ : ℝ) : ℂ)) * Uᴴ =
        U * diagonal (fun i =>
          ((((hH.isHermitian.eigenvalues i + a)⁻¹ -
            (hH.isHermitian.eigenvalues i + b)⁻¹) : ℝ) : ℂ)) * Uᴴ := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hfactor]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ ((((hH.isHermitian.eigenvalues i + a)⁻¹ -
    (hH.isHermitian.eigenvalues i + b)⁻¹) : ℝ) : ℂ)
  exact_mod_cast sub_nonneg.mpr ((inv_le_inv₀
    (add_pos_of_nonneg_of_pos (hH.eigenvalues_nonneg i) hb)
    (add_pos_of_nonneg_of_pos (hH.eigenvalues_nonneg i) ha)).2
      (by simpa [add_comm] using
        add_le_add_left hab (hH.isHermitian.eigenvalues i)))

/-- Positive trace pairings inherit antitonicity of shifted inverses. -/
theorem re_trace_mul_shiftedPosSemidef_inv_le
    {H P : Matrix n n ℂ} (hH : H.PosSemidef) (hP : P.PosSemidef)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ((P * (H + (b : ℂ) • (1 : Matrix n n ℂ))⁻¹).trace).re ≤
      ((P * (H + (a : ℂ) • (1 : Matrix n n ℂ))⁻¹).trace).re := by
  have hdiff := shiftedPosSemidef_inv_sub_posSemidef hH ha hab
  have hnonneg := fintypeMatrix_re_trace_mul_nonneg_of_posSemidef hP hdiff
  rw [Matrix.mul_sub, Matrix.trace_sub] at hnonneg
  change 0 ≤
    ((P * (H + (a : ℂ) • (1 : Matrix n n ℂ))⁻¹).trace).re -
      ((P * (H + (b : ℂ) • (1 : Matrix n n ℂ))⁻¹).trace).re at hnonneg
  linarith

/-- Spectral cutoff `H(H + εI)⁻¹` for a finite matrix. -/
def finiteMatrixResolventCutoff (H : Matrix n n ℂ) (ε : ℝ) : Matrix n n ℂ :=
  H * (H + (ε : ℂ) • (1 : Matrix n n ℂ))⁻¹

/-- A positive-semidefinite cutoff is the unitary conjugate of `λ / (λ + ε)`. -/
theorem finiteMatrixResolventCutoff_eq_spectral {H : Matrix n n ℂ} (hH : H.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    finiteMatrixResolventCutoff H ε =
      (hH.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i =>
          (((hH.isHermitian.eigenvalues i *
            (hH.isHermitian.eigenvalues i + ε)⁻¹) : ℝ) : ℂ)) *
        (hH.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  let U : Matrix n n ℂ := hH.isHermitian.eigenvectorUnitary
  have hUU : Uᴴ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.mem_iff.mp hH.isHermitian.eigenvectorUnitary.property).1
  have hconj (A B : Matrix n n ℂ) :
      (U * A * Uᴴ) * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
    calc
      (U * A * Uᴴ) * (U * B * Uᴴ) =
          U * A * (Uᴴ * U) * B * Uᴴ := by noncomm_ring
      _ = U * (A * B) * Uᴴ := by rw [hUU]; simp [Matrix.mul_assoc]
  have hspec : H = U * diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) * Uᴴ := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      isHermitian_eq_conj_diagonal hH.isHermitian
  have hinv : (H + (ε : ℂ) • (1 : Matrix n n ℂ))⁻¹ =
      U * diagonal (fun i =>
        (((hH.isHermitian.eigenvalues i + ε)⁻¹ : ℝ) : ℂ)) * Uᴴ := by
    simpa [U] using shiftedHermitian_inv_eq_spectral hH.isHermitian ε fun i =>
      ne_of_gt (add_pos_of_nonneg_of_pos (hH.eigenvalues_nonneg i) hε)
  unfold finiteMatrixResolventCutoff
  calc
    H * (H + (ε : ℂ) • (1 : Matrix n n ℂ))⁻¹ =
      (U * diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) * Uᴴ) *
        (U * diagonal (fun i =>
          (((hH.isHermitian.eigenvalues i + ε)⁻¹ : ℝ) : ℂ)) * Uᴴ) :=
      congrArg₂ (fun X Y : Matrix n n ℂ => X * Y) hspec hinv
    _ =
      U * (diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) *
        diagonal (fun i => (((hH.isHermitian.eigenvalues i + ε)⁻¹ : ℝ) : ℂ))) * Uᴴ := by
      exact hconj _ _
    _ = U * diagonal (fun i =>
        (((hH.isHermitian.eigenvalues i *
          (hH.isHermitian.eigenvalues i + ε)⁻¹) : ℝ) : ℂ)) * Uᴴ := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 2
      funext i
      push_cast
      rfl

/-- Every positive regularized spectral cutoff is positive semidefinite. -/
theorem finiteMatrixResolventCutoff_posSemidef {H : Matrix n n ℂ} (hH : H.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    (finiteMatrixResolventCutoff H ε).PosSemidef := by
  rw [finiteMatrixResolventCutoff_eq_spectral hH hε]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (((hH.isHermitian.eigenvalues i *
    (hH.isHermitian.eigenvalues i + ε)⁻¹) : ℝ) : ℂ)
  exact_mod_cast mul_nonneg (hH.eigenvalues_nonneg i)
    (inv_nonneg.mpr (add_nonneg (hH.eigenvalues_nonneg i) hε.le))

/-- Multiplying a positive regularized cutoff by its source remains positive semidefinite. -/
theorem finiteMatrixResolventCutoff_mul_posSemidef {H : Matrix n n ℂ} (hH : H.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    (finiteMatrixResolventCutoff H ε * H).PosSemidef := by
  let U : Matrix n n ℂ := hH.isHermitian.eigenvectorUnitary
  have hUU : Uᴴ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.mem_iff.mp hH.isHermitian.eigenvectorUnitary.property).1
  have hconj (A B : Matrix n n ℂ) :
      (U * A * Uᴴ) * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
    calc
      (U * A * Uᴴ) * (U * B * Uᴴ) =
          U * A * (Uᴴ * U) * B * Uᴴ := by noncomm_ring
      _ = U * (A * B) * Uᴴ := by rw [hUU]; simp [Matrix.mul_assoc]
  have hcut : finiteMatrixResolventCutoff H ε =
      U * diagonal (fun i =>
        (((hH.isHermitian.eigenvalues i *
          (hH.isHermitian.eigenvalues i + ε)⁻¹) : ℝ) : ℂ)) * Uᴴ := by
    simpa [U] using finiteMatrixResolventCutoff_eq_spectral hH hε
  have hspec : H = U * diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) * Uᴴ := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      isHermitian_eq_conj_diagonal hH.isHermitian
  have heq : finiteMatrixResolventCutoff H ε * H =
      U * diagonal (fun i =>
        (((hH.isHermitian.eigenvalues i *
          (hH.isHermitian.eigenvalues i + ε)⁻¹ *
          hH.isHermitian.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := by
    calc
      finiteMatrixResolventCutoff H ε * H =
          (U * diagonal (fun i =>
            (((hH.isHermitian.eigenvalues i *
              (hH.isHermitian.eigenvalues i + ε)⁻¹) : ℝ) : ℂ)) * Uᴴ) *
          (U * diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) * Uᴴ) :=
        congrArg₂ (fun X Y : Matrix n n ℂ => X * Y) hcut hspec
      _ = U * (diagonal (fun i =>
          (((hH.isHermitian.eigenvalues i *
            (hH.isHermitian.eigenvalues i + ε)⁻¹) : ℝ) : ℂ)) *
        diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ))) * Uᴴ := by
        exact hconj _ _
      _ = U * diagonal (fun i =>
          (((hH.isHermitian.eigenvalues i *
            (hH.isHermitian.eigenvalues i + ε)⁻¹ *
            hH.isHermitian.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 2
        funext i
        push_cast
        rfl
  rw [heq]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (((hH.isHermitian.eigenvalues i *
      (hH.isHermitian.eigenvalues i + ε)⁻¹ *
      hH.isHermitian.eigenvalues i) : ℝ) : ℂ)
  exact_mod_cast mul_nonneg
    (mul_nonneg (hH.eigenvalues_nonneg i)
      (inv_nonneg.mpr (add_nonneg (hH.eigenvalues_nonneg i) hε.le)))
    (hH.eigenvalues_nonneg i)

/-- Trace of a positive regularized cutoff in spectral coordinates. -/
theorem finiteMatrixResolventCutoff_trace_re {H : Matrix n n ℂ} (hH : H.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    (finiteMatrixResolventCutoff H ε).trace.re =
      ∑ i, hH.isHermitian.eigenvalues i *
        (hH.isHermitian.eigenvalues i + ε)⁻¹ := by
  let U : Matrix n n ℂ := hH.isHermitian.eigenvectorUnitary
  have hUU : Uᴴ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.mem_iff.mp hH.isHermitian.eigenvectorUnitary.property).1
  rw [finiteMatrixResolventCutoff_eq_spectral hH hε]
  change (U * diagonal (fun i =>
      (((hH.isHermitian.eigenvalues i *
        (hH.isHermitian.eigenvalues i + ε)⁻¹) : ℝ) : ℂ)) * Uᴴ).trace.re = _
  rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_diagonal]
  norm_cast

/-- As regularization decreases to zero, cutoff trace converges to matrix rank. -/
theorem tendsto_finiteMatrixResolventCutoff_trace_re_rank
    {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    Tendsto (fun ε : ℝ => (finiteMatrixResolventCutoff H ε).trace.re)
      (𝓝[Ioi 0] 0) (𝓝 (H.rank : ℝ)) := by
  let eig : n → ℝ := hH.isHermitian.eigenvalues
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[Ioi 0] 0) (𝓝 0) := by
    exact tendsto_id.mono_right inf_le_left
  have hterm (i : n) :
      Tendsto (fun ε : ℝ => eig i * (eig i + ε)⁻¹) (𝓝[Ioi 0] 0)
        (𝓝 (if eig i = 0 then (0 : ℝ) else 1)) := by
    by_cases heig : eig i = 0
    · simp [heig]
    · have hconst : Tendsto (fun _ : ℝ => eig i) (𝓝[Ioi 0] 0) (𝓝 (eig i)) :=
        tendsto_const_nhds
      have hden : Tendsto (fun ε : ℝ => eig i + ε) (𝓝[Ioi 0] 0) (𝓝 (eig i)) := by
        simpa using hconst.add hid
      simpa [heig] using hconst.mul (hden.inv₀ heig)
  have hsum :
      Tendsto (fun ε : ℝ => ∑ i, eig i * (eig i + ε)⁻¹) (𝓝[Ioi 0] 0)
        (𝓝 (∑ i, if eig i = 0 then (0 : ℝ) else 1)) := by
    simpa using tendsto_finsetSum Finset.univ fun i _ => hterm i
  have heq :
      (fun ε : ℝ => (finiteMatrixResolventCutoff H ε).trace.re) =ᶠ[𝓝[Ioi 0] 0]
        (fun ε : ℝ => ∑ i, eig i * (eig i + ε)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [eig] using finiteMatrixResolventCutoff_trace_re hH hε
  have hrank :
      (∑ i, if eig i = 0 then (0 : ℝ) else 1) = (H.rank : ℝ) := by
    rw [hH.isHermitian.rank_eq_card_non_zero_eigs]
    change (∑ i, if eig i = 0 then (0 : ℝ) else 1) =
      (Fintype.card {i // eig i ≠ 0} : ℝ)
    calc
      (∑ i, if eig i = 0 then (0 : ℝ) else 1) =
          ∑ i, if eig i ≠ 0 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : eig i = 0 <;> simp [hi]
      _ = ((Finset.univ.filter fun i => eig i ≠ 0).card : ℝ) := by
        simpa using Finset.sum_boole (fun i => eig i ≠ 0) Finset.univ
      _ = (Fintype.card {i // eig i ≠ 0} : ℝ) := by
        norm_cast
        let e : {i // eig i ≠ 0} ≃
            ↥(Finset.univ.filter fun i => eig i ≠ 0) :=
          { toFun := fun i =>
              ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩⟩
            invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        calc
          (Finset.univ.filter fun i => eig i ≠ 0).card =
              Fintype.card ↥(Finset.univ.filter fun i => eig i ≠ 0) :=
            (Fintype.card_coe _).symm
          _ = Fintype.card {i // eig i ≠ 0} := (Fintype.card_congr e).symm
  rw [← hrank]
  exact Filter.Tendsto.congr' heq.symm hsum

end

end GaloisForLFunctions.HTGeometry
