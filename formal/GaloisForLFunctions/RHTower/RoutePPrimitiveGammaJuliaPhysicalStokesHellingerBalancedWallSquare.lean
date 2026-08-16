import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryDeterminantCofinalUniform

/-!
# Route P primitive Gamma--Julia balanced-wall square law

The forced physical ratio tends to the balanced value `r = 1` at the aperture wall. At that
value the Hellinger channel is not collapsing: it satisfies `A₁² = 64 I`, has trace zero, and
has eigenvalues `+8` and `-8`. Consequently its tensor determinant is a square-coordinate
determinant of the literal child matrix:

```text
det(I + z (A₁ tensor H)) = det(I - 64 z² H²).
```

This file proves the identity for every finite Hermitian child carrier, not merely for diagonal
models. It then constructs the channel-complete cofinal truncations of the actual prime Stokes
kernel and proves their literal finite ordinary determinants equal the squared-child determinants.
Although arbitrary channel-prime truncations need not preserve the pairing, channel-complete
truncations are cofinal. Their pointwise limit proves the full balanced ordinary determinant is
even, while the previous self-adjoint determinant theorem keeps all its zeros real.

Thus the aperture wall is the operator source of a squared compact spectral coordinate. It does
not identify that child-square spectrum with the separate reciprocal-gap Markov candidate; that
arithmetic spectral bridge and wall convergence remain open.
-/

open Complex Matrix Filter Topology Set
open ContinuousLinearMap
open scoped Kronecker ComplexOrder BigOperators InnerProductSpace Matrix

namespace RHTower

noncomputable section

/-- The balanced physical Hellinger channel is an exact square root of `64 I`. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_balanced_sq :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 *
        routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 =
      (64 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hdefect : (routeEPCubicFourthDepthJuliaDefect : ℂ) ^ 2 =
      ((63 / 64 : ℝ) : ℂ) := by
    exact_mod_cast routeEPCubicFourthDepthJuliaDefect_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> rw [hdefect] <;> norm_num

/-- Physical Hellinger pencil over an arbitrary finite child index type. -/
def routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (r : ℝ) (u : ℂ) :
    Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
  1 + u • (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ⊗ₖ H)

/-- Spectral factorization of the physical pencil for arbitrary finite child types. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil_det_eq_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    {r : ℝ} (hr : 0 ≤ r) (u : ℂ) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H r u).det =
      ∏ i, routePPrimitiveGammaJuliaSignedBivariateFactor
        (hH.eigenvalues i) (64 * u) (r * u) := by
  let U : Matrix ι ι ℂ := hH.eigenvectorUnitary
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    u • routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r
  let Q : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U
  have hU : Uᴴ * U = 1 := by
    change (hH.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
        (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hQ : Qᴴ * Q = 1 := by
    dsimp only [Q]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, hU,
      Matrix.one_kronecker_one]
  have hUH : Uᴴ * H * U =
      Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    exact GaloisForLFunctions.HTGeometry.conjTranspose_mul_mul_eigenvectorUnitary hH
  have hconj :
      Qᴴ * routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H r u * Q =
        1 + A ⊗ₖ Matrix.diagonal
          (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil,
      Matrix.mul_add, Matrix.add_mul]
    rw [Matrix.mul_one, hQ]
    congr 1
    rw [← Matrix.smul_kronecker]
    change Qᴴ * (A ⊗ₖ H) * Q = _
    dsimp only [Q]
    rw [Matrix.conjTranspose_kronecker]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hUH]
  have hdet_conj :
      (Qᴴ * routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H r u * Q).det =
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H r u).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    have hdetQ : Qᴴ.det * Q.det = 1 := by
      rw [← Matrix.det_mul, hQ, Matrix.det_one]
    calc
      Qᴴ.det *
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H r u).det *
          Q.det =
          (Qᴴ.det * Q.det) *
            (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H r u).det := by
              ring
      _ = (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H r u).det := by
        rw [hdetQ, one_mul]
  have hblock :
      1 + A ⊗ₖ Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) =
        Matrix.blockDiagonal (fun i : ι =>
          1 + ((hH.eigenvalues i : ℝ) : ℂ) • A) := by
    rw [Matrix.kronecker_diagonal]
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases hij : i = j
    · subst j
      simp [Matrix.blockDiagonal_apply_eq, Matrix.one_apply]
    · simp [Matrix.blockDiagonal_apply_ne _ _ _ hij, hij]
  rw [← hdet_conj, hconj, hblock, Matrix.det_blockDiagonal]
  apply Finset.prod_congr rfl
  intro i _hi
  simpa [A, smul_smul, mul_comm] using
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_factor
      (lam := hH.eigenvalues i) hr u

/-- At balance, the physical eigenfactor loses its linear term and becomes a square factor. -/
theorem routePPrimitiveGammaJuliaSignedBivariateFactor_balanced
    (lam : ℝ) (u : ℂ) :
    routePPrimitiveGammaJuliaSignedBivariateFactor lam (64 * u) (1 * u) =
      1 - 64 * (lam : ℂ) ^ 2 * u ^ 2 := by
  simp [routePPrimitiveGammaJuliaSignedBivariateFactor]
  ring

/-- Exact balanced physical determinant as product over squared child eigenvalues. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil_balanced_det_eq_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (u : ℂ) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H 1 u).det =
      ∏ i, (1 - 64 * ((hH.eigenvalues i : ℝ) : ℂ) ^ 2 * u ^ 2) := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil_det_eq_prod
    H hH (r := 1) (by norm_num)]
  apply Finset.prod_congr rfl
  intro i _hi
  exact routePPrimitiveGammaJuliaSignedBivariateFactor_balanced
    (hH.eigenvalues i) u

/-- Balanced physical finite determinant is even before any cofinal limit. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil_balanced_even
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    Function.Even (fun u : ℂ =>
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H 1 u).det) := by
  intro u
  change (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H 1 (-u)).det =
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H 1 u).det
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil_balanced_det_eq_prod
      H hH,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil_balanced_det_eq_prod
      H hH]
  apply Finset.prod_congr rfl
  intro i _hi
  ring

/-- Literal square-coordinate pencil of a finite child matrix. -/
def routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (u : ℂ) : Matrix ι ι ℂ :=
  1 - (64 * u ^ 2) • (H * H)

/-- Squared-child determinant has the same squared-eigenvalue product. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil_det_eq_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (u : ℂ) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u).det =
      ∏ i, (1 - 64 * ((hH.eigenvalues i : ℝ) : ℂ) ^ 2 * u ^ 2) := by
  let U : Matrix ι ι ℂ := hH.eigenvectorUnitary
  let D : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))
  have hstarU : Uᴴ * U = 1 := by
    change (hH.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
        (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hUstar : U * Uᴴ = 1 := by
    change (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
        (hH.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ = 1
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self _
  have hUH : Uᴴ * H * U = D := by
    exact GaloisForLFunctions.HTGeometry.conjTranspose_mul_mul_eigenvectorUnitary hH
  have hHsq : Uᴴ * (H * H) * U = D * D := by
    calc
      Uᴴ * (H * H) * U = (Uᴴ * H) * (H * U) := by simp [mul_assoc]
      _ = (Uᴴ * H) * (1 * (H * U)) := by rw [Matrix.one_mul]
      _ = (Uᴴ * H) * ((U * Uᴴ) * (H * U)) := by rw [hUstar]
      _ = (Uᴴ * H * U) * (Uᴴ * H * U) := by simp [mul_assoc]
      _ = D * D := by rw [hUH]
  have hconj :
      Uᴴ * routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u * U =
        Matrix.diagonal
          (fun i => 1 - 64 * ((hH.eigenvalues i : ℝ) : ℂ) ^ 2 * u ^ 2) := by
    calc
      Uᴴ * routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u * U =
          1 - (64 * u ^ 2) • (Uᴴ * (H * H) * U) := by
            simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil,
              Matrix.mul_sub, Matrix.sub_mul, hstarU, mul_assoc]
      _ = 1 - (64 * u ^ 2) • (D * D) := by rw [hHsq]
      _ = Matrix.diagonal
          (fun i => 1 - 64 * ((hH.eigenvalues i : ℝ) : ℂ) ^ 2 * u ^ 2) := by
            ext i j
            by_cases hij : i = j
            · subst j
              simp [D]
              ring
            · simp [D, hij]
  have hdet_conj :
      (Uᴴ * routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u * U).det =
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    have hdetU : Uᴴ.det * U.det = 1 := by
      rw [← Matrix.det_mul, hstarU, Matrix.det_one]
    calc
      Uᴴ.det *
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u).det *
          U.det =
          (Uᴴ.det * U.det) *
            (routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u).det := by
              ring
      _ = (routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u).det := by
        rw [hdetU, one_mul]
  rw [← hdet_conj, hconj, Matrix.det_diagonal]

/-- Universal balanced-wall square law for every finite Hermitian child matrix. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil_balanced_det_eq_squaredChild
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (u : ℂ) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil H 1 u).det =
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u).det := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil_balanced_det_eq_prod
      H hH,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil_det_eq_prod H hH]

/-- Finite prime sets completed across both physical Hellinger channels. -/
def routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete
    (t : Finset Nat.Primes) : Finset (Fin 2 × Nat.Primes) :=
  Finset.univ ×ˢ t

/-- Canonical equivalence between channel-complete indices and channel times finite primes. -/
def routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteEquiv
    (t : Finset Nat.Primes) :
    (Fin 2 × ↥t) ≃
      ↥(routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) where
  toFun x := ⟨(x.1, x.2.1), by
    simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete, x.2.2]⟩
  invFun x := (x.1.1, ⟨x.1.2, (Finset.mem_product.mp x.2).2⟩)
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- A channel-complete block is exactly the channel tensor the child block after reindexing. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteBlock_reindex
    (d r : ℝ) (t : Finset Nat.Primes) (u : ℂ) :
    Matrix.reindex
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteEquiv t).symm
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteEquiv t).symm
        (1 + u • HilbertSchmidt.blockMatrix
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r)
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t)) =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil
        (HilbertSchmidt.blockMatrix
          (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t) r u := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp [Matrix.reindex_apply,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteEquiv,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil,
    HilbertSchmidt.blockMatrix,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel,
    Matrix.one_apply]

/-- Every literal channel-complete finite physical determinant is a squared-child determinant. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet_eq_squaredChild
    (d : ℝ) (t : Finset Nat.Primes) (u : ℂ) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) u =
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil
        (HilbertSchmidt.blockMatrix
          (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t) u).det := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet_eq_det]
  let e := routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteEquiv t
  let M := 1 + u • HilbertSchmidt.blockMatrix
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d 1)
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t)
  calc
    M.det = (Matrix.reindex e.symm e.symm M).det := by
      exact (Matrix.det_reindex_self e.symm M).symm
    _ = (routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil
        (HilbertSchmidt.blockMatrix
          (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t) 1 u).det := by
      rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteBlock_reindex]
    _ = _ :=
      routePPrimitiveGammaJuliaPhysicalStokesHellingerFintypePencil_balanced_det_eq_squaredChild
        _ (routePPrimitiveGammaJuliaStokesCofinalChildBlockMatrix_posSemidef d t).isHermitian u

/-- Channel-complete literal finite ordinary determinants are even. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet_even
    (d : ℝ) (t : Finset Nat.Primes) :
    Function.Even (fun u : ℂ =>
      routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) u) := by
  intro u
  change routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) (-u) =
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) u
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet_eq_squaredChild,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet_eq_squaredChild]
  congr 1
  simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil]

/-- Channel-complete finite prime truncations are cofinal among all channel-prime truncations. -/
theorem tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete :
    Tendsto routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete atTop atTop := by
  apply tendsto_atTop.2
  intro s
  filter_upwards [eventually_ge_atTop (s.image Prod.snd)] with t ht
  intro x hx
  have hxsnd : x.2 ∈ t := ht (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete, hxsnd]

/-- Channel-complete determinants converge to the full balanced ordinary determinant. -/
theorem tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet
    {d : ℝ} (hd : 0 < d) (u : ℂ) :
    Tendsto (fun t : Finset Nat.Primes =>
      routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) u) atTop
      (nhds (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d 1 u)) := by
  simpa [Function.comp_def] using
    (tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet
      hd (r := 1) (by norm_num) u).comp
        tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete

/-- The full balanced ordinary determinant is even: its spectral variable descends through `z²`. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet_balanced_even
    {d : ℝ} (hd : 0 < d) :
    Function.Even
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d 1) := by
  intro u
  have hneg :=
    tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet hd (-u)
  have hpos :=
    tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet hd u
  have hstage :
      (fun t : Finset Nat.Primes =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) (-u)) =
      (fun t : Finset Nat.Primes =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) u) := by
    funext t
    exact routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet_even d t u
  rw [hstage] at hneg
  exact tendsto_nhds_unique hneg hpos

/-- At balance the trace restoration factor is exactly one. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet_balanced_eq_det2
    (d : ℝ) (u : ℂ) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d 1 u =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d 1 (-u) := by
  simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet]

/-- **P-G105P capstone.** Balanced aperture-wall channel is a square root of `64 I`; every
channel-complete finite determinant is the literal squared-child determinant; these truncations
are cofinal; and the resulting full entire determinant is even with only real zeros. -/
theorem routePPrimitive_GammaJulia_physicalStokesHellingerBalancedWallSquare
    (d : ℝ) (hd : 0 < d) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 *
        routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 =
      (64 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    (∀ (t : Finset Nat.Primes) (u : ℂ),
      routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) u =
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil
          (HilbertSchmidt.blockMatrix
            (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t) u).det) ∧
    Tendsto routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete atTop atTop ∧
    Function.Even
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d 1) ∧
    (∀ u : ℂ,
      routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d 1 u = 0 →
        u.im = 0) := by
  refine ⟨routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_balanced_sq,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet_eq_squaredChild d,
    tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet_balanced_even hd, ?_⟩
  intro u hu
  exact routePPrimitive_GammaJulia_physicalStokesHellingerOrdinaryDeterminant
    d hd 1 (by norm_num) |>.2.2.2.1 u hu

end

end RHTower
