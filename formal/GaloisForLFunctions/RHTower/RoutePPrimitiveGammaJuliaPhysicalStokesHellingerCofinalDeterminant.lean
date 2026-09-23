import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCofinalChildKernel
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantEigenvalueLimit
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Route P primitive Gamma--Julia physical Hellinger cofinal determinant

P-G105J's forced physical generator is row-weighted and therefore nonnormal.  Its hidden
Hellinger representative is the real-symmetric channel

```text
A_r = [[1, 8 sqrt(r) delta], [8 sqrt(r) delta, -r]].
```

For `r >= 0`, `A_r` has trace `1-r`, determinant `-64r`, and exactly the same characteristic
factor as the original physical channel on every eigenvalue of every actual finite P-G186 source
Gram.  Tensoring `A_r` with P-G105K's full cofinal child kernel retains every cross-prime entry.
The resulting kernel is Hilbert--Schmidt and Hermitian, so its represented operator is
self-adjoint.  Its regularized determinant is entire, its finite sections converge uniformly on
every closed disc, and every cofinal zero is real.  At the forced ratio `r(d)`, its summable
diagonal is exactly the completed prime--Gamma current.

This closes the cofinal stable-det2 gate without target fitting.  Trace class, ordinary
trace-restoration, aperture-wall determinant convergence, and Xi-divisor identification remain.
-/

open Complex Matrix Filter Topology Set
open scoped Kronecker ComplexOrder BigOperators

namespace RHTower

noncomputable section

/-- Symmetric Hellinger representative of the forced physical Julia--polar channel. -/
def routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel (r : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 : ℝ) : ℂ),
      ((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ);
    ((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ),
      ((-r : ℝ) : ℂ)]

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_conjTranspose
    (r : ℝ) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r)ᴴ =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    change star ((_ : ℝ) : ℂ) = ((_ : ℝ) : ℂ) <;>
    exact Complex.conj_ofReal _

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_trace
    (r : ℝ) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r).trace =
      ((1 - r : ℝ) : ℂ) := by
  simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel, Matrix.trace]
  ring

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_det
    {r : ℝ} (hr : 0 ≤ r) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r).det =
      ((-64 * r : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  have hsqrt : (Real.sqrt r) ^ (2 : ℕ) = r := Real.sq_sqrt hr
  have hdefect : routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) = (63 / 64 : ℝ) :=
    routeEPCubicFourthDepthJuliaDefect_sq
  simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel]
  have hmul : (Real.sqrt r * routeEPCubicFourthDepthJuliaDefect) ^ (2 : ℕ) =
      r * (63 / 64 : ℝ) := by rw [mul_pow, hsqrt, hdefect]
  have hreal :
      -r - (8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect) *
        (8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect) = -64 * r := by
    nlinarith [hmul]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hreal
  calc
    (-(r : ℂ) - 8 * (Real.sqrt r : ℂ) *
        (routeEPCubicFourthDepthJuliaDefect : ℂ) *
        (8 * (Real.sqrt r : ℂ) *
          (routeEPCubicFourthDepthJuliaDefect : ℂ))) =
        (((-r - (8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect) *
          (8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect)) : ℝ) : ℂ) := by
            push_cast
            ring
    _ = (((-64 * r : ℝ)) : ℂ) := hc
    _ = -(64 * (r : ℂ)) := by push_cast; ring

/-- Symmetric and row-weighted physical channels have the same characteristic factor. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_factor
    {r lam : ℝ} (hr : 0 ≤ r) (u : ℂ) :
    (1 + ((lam : ℂ) * u) •
      routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r).det =
      routePPrimitiveGammaJuliaSignedBivariateFactor lam (64 * u) (r * u) := by
  rw [Matrix.det_fin_two]
  have hsqrt : (Real.sqrt r) ^ (2 : ℕ) = r := Real.sq_sqrt hr
  have hdefect : routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) = (63 / 64 : ℝ) :=
    routeEPCubicFourthDepthJuliaDefect_sq
  simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel,
    routePPrimitiveGammaJuliaSignedBivariateFactor]
  have hsqrtC : (Real.sqrt r : ℂ) ^ (2 : ℕ) = (r : ℂ) := by exact_mod_cast hsqrt
  have hdefectC : (routeEPCubicFourthDepthJuliaDefect : ℂ) ^ (2 : ℕ) =
      ((63 / 64 : ℝ) : ℂ) := by exact_mod_cast hdefect
  ring_nf
  rw [hsqrtC, hdefectC]
  norm_num
  ring

/-- Finite physical pencil in the symmetric Hellinger channel. -/
def routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (r : ℝ) (u : ℂ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  1 + u •
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ⊗ₖ H)

/-- Spectral factorization of the symmetric physical pencil. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil_det_eq_prod
    {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {r : ℝ} (hr : 0 ≤ r) (u : ℂ) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil H r u).det =
      ∏ i, routePPrimitiveGammaJuliaSignedBivariateFactor
        (hH.eigenvalues i) (64 * u) (r * u) := by
  let U : Matrix (Fin N) (Fin N) ℂ := hH.eigenvectorUnitary
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    u • routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r
  let Q : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U
  have hU : Uᴴ * U = 1 := by
    change (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)ᴴ *
        (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1
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
      Qᴴ * routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil H r u * Q =
        1 + A ⊗ₖ Matrix.diagonal
          (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil,
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
      (Qᴴ * routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil H r u * Q).det =
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil H r u).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    have hdetQ : Qᴴ.det * Q.det = 1 := by
      rw [← Matrix.det_mul, hQ, Matrix.det_one]
    calc
      Qᴴ.det *
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil H r u).det *
          Q.det =
          (Qᴴ.det * Q.det) *
            (routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil H r u).det := by ring
      _ = (routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil H r u).det := by
        rw [hdetQ, one_mul]
  have hblock :
      1 + A ⊗ₖ Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) =
        Matrix.blockDiagonal (fun i : Fin N =>
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

/-- Exact finite source equivalence: Hellinger symmetrization changes no physical determinant. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil_det_eq_completed
    {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {r : ℝ} (hr : 0 ≤ r) (u : ℂ) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil H r u).det =
      (routePPrimitiveGammaJuliaSignedBivariatePencil H (64 * u) (r * u)).det := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil_det_eq_prod H hH hr,
    routePPrimitiveGammaJuliaSignedBivariatePencil_det_eq_prod_eigenfactors H hH]

/-- Every actual finite P-G186 physical determinant is retained by Hellinger symmetrization. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil_det_eq_actual
    {N : ℕ} (d : ℝ) (p : Fin N → Nat.Primes) (kappa : Fin N → ℝ)
    (hr : 0 ≤ routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) (u : ℂ) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil
      (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram d p kappa)
      (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) u).det =
      (routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil d p kappa u).det := by
  have hH :=
    (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_posSemidef
      d p kappa).isHermitian
  simpa [routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil] using
    routePPrimitiveGammaJuliaPhysicalStokesHellingerPencil_det_eq_completed
      (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram d p kappa)
      hH hr u

/-- Reindexing which separates finite channel pair from cofinal prime pair. -/
def routePPrimitiveGammaJuliaPhysicalStokesHellingerPairEquiv :
    ((Fin 2 × Nat.Primes) × (Fin 2 × Nat.Primes)) ≃
      ((Fin 2 × Fin 2) × (Nat.Primes × Nat.Primes)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv x := by rcases x with ⟨⟨i,p⟩,⟨j,q⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨i,j⟩,⟨p,q⟩⟩; rfl

/-- Full physical Hellinger channel tensored with literal cofinal Stokes child kernel. -/
def routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
    (d r : ℝ)
    (xy : (Fin 2 × Nat.Primes) × (Fin 2 × Nat.Primes)) : ℂ :=
  routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r xy.1.1 xy.2.1 *
    routePPrimitiveGammaJuliaStokesCofinalChildKernel d (xy.1.2, xy.2.2)

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS
    {d : ℝ} (hd : 0 < d) (r : ℝ) :
    HilbertSchmidt.IsHS
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) := by
  let g : Fin 2 × Fin 2 → ℝ := fun ij =>
    ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ij.1 ij.2‖ ^ (2 : ℕ)
  let h : Nat.Primes × Nat.Primes → ℝ := fun pq =>
    ‖routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq‖ ^ (2 : ℕ)
  have hg : Summable g := Summable.of_finite
  have hh : Summable h :=
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd
  have hgh : Summable (fun x : (Fin 2 × Fin 2) ×
      (Nat.Primes × Nat.Primes) => g x.1 * h x.2) :=
    summable_mul_of_summable_norm hg.norm hh.norm
  rw [← routePPrimitiveGammaJuliaPhysicalStokesHellingerPairEquiv.summable_iff]
    at hgh
  simpa [HilbertSchmidt.IsHS, Function.comp_def,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerPairEquiv,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel,
    g, h, norm_mul, mul_pow] using hgh

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_star_apply
    (r : ℝ) (i j : Fin 2) :
    star (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r j i) =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r i j := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A i j)
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_conjTranspose r)
  simpa only [Matrix.conjTranspose_apply] using h

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_hsAdjoint
    (d r : ℝ) :
    HilbertSchmidt.hsAdjoint
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) =
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r := by
  funext xy
  rw [HilbertSchmidt.hsAdjoint]
  change star
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r xy.2.1 xy.1.1 *
        routePPrimitiveGammaJuliaStokesCofinalChildKernel d (xy.2.2, xy.1.2)) = _
  rw [star_mul,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_star_apply,
    show star (routePPrimitiveGammaJuliaStokesCofinalChildKernel
      d (xy.2.2, xy.1.2)) =
      routePPrimitiveGammaJuliaStokesCofinalChildKernel
        d (xy.1.2, xy.2.2) by
      have h := congrFun
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_hsAdjoint d)
        (xy.1.2, xy.2.2)
      simpa [HilbertSchmidt.hsAdjoint] using h]
  simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel,
    mul_comm]

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_isSelfAdjoint
    {d : ℝ} (hd : 0 < d) (r : ℝ) :
    IsSelfAdjoint (HilbertSchmidt.toOperator
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)) := by
  rw [IsSelfAdjoint]
  change ContinuousLinearMap.adjoint
      (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)) = _
  rw [HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_hsAdjoint d r)

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_diagonal
    {d : ℝ} (hd : 0 < d) (r : ℝ) (ip : Fin 2 × Nat.Primes) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r (ip, ip) =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ip.1 ip.1 *
        (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d ip.2 : ℂ) := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd]

theorem summable_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_diagonal
    {d : ℝ} (hd : 0 < d) (r : ℝ) :
    Summable (fun ip : Fin 2 × Nat.Primes =>
      routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r (ip, ip)) := by
  let f : Fin 2 × Nat.Primes → ℂ := fun ip =>
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ip.1 ip.1 *
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d (ip.2, ip.2)
  have hdiag := summable_routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd
  have hf : Summable f := by
    exact summable_mul_of_summable_norm
      (f := fun i : Fin 2 =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r i i)
      (g := fun p : Nat.Primes =>
        routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, p))
      Summable.of_finite hdiag.norm
  simpa [f, routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel] using hf

theorem tsum_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_diagonal
    {d : ℝ} (hd : 0 < d) (r : ℝ) :
    (∑' ip : Fin 2 × Nat.Primes,
      routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r (ip, ip)) =
      ((1 - r : ℝ) : ℂ) *
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ) := by
  have hs := summable_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_diagonal hd r
  rw [hs.tsum_prod, tsum_fintype]
  simp only [routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel,
    tsum_mul_left]
  rw [tsum_routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd]
  simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel]
  ring

/-- Cofinal physical regularized determinant. -/
def routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2
    (d r : ℝ) : ℂ → ℂ :=
  GaloisForLFunctions.HTGeometry.entireDet2
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r)

theorem differentiable_routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2
    {d : ℝ} (hd : 0 < d) (r : ℝ) :
    Differentiable ℂ
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d r) :=
  GaloisForLFunctions.HTGeometry.differentiable_entireDet2
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)

theorem tendstoUniformlyOn_routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteDet2
    {d : ℝ} (hd : 0 < d) (r : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    TendstoUniformlyOn
      (fun s z => GaloisForLFunctions.HTGeometry.finiteDet2
        (-(HilbertSchmidt.blockMatrix
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) s)) z)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d r)
      atTop (Metric.closedBall 0 rho) :=
  GaloisForLFunctions.HTGeometry.tendstoUniformlyOn_finiteDet2_entireDet2
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r) hrho

/-- Self-adjoint cofinalization converts every regularized-determinant zero into a real zero. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2_zero_im
    {d : ℝ} (hd : 0 < d) (r : ℝ) {z : ℂ}
    (hz : routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d r z = 0) :
    z.im = 0 := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    have hone :=
      (GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)).eq_one_at_zero
    exact one_ne_zero (hone.symm.trans hz)
  obtain ⟨w, hw0, hw⟩ :=
    GaloisForLFunctions.HTGeometry.exists_eigenvector_of_entireDet2_eq_zero
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)
      hz0 hz
  let T := HilbertSchmidt.toOperator
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)
  have heig : Module.End.HasEigenvalue (T : Module.End ℂ
      (lp (fun _ : Fin 2 × Nat.Primes => ℂ) 2)) z⁻¹ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := w) ⟨?_, hw0⟩
    rw [Module.End.mem_eigenspace_iff]
    exact hw
  have hrealInv : star z⁻¹ = z⁻¹ :=
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_isSelfAdjoint
      hd r).isSymmetric.conj_eigenvalue_eq_self heig
  have himInv : z⁻¹.im = 0 := Complex.conj_eq_iff_im.mp hrealInv
  rw [Complex.inv_im] at himInv
  have hnorm : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz0).ne'
  exact neg_eq_zero.mp (div_eq_zero_iff.mp himInv |>.resolve_right hnorm)

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2_ne_zero_of_im_ne
    {d : ℝ} (hd : 0 < d) (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d r z ≠ 0 := by
  intro hzero
  exact hz
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2_zero_im hd r hzero)

theorem routePPrimitiveGammaJuliaPhysicalStokesHellinger_diagonalTrace_eq_completed
    {d : ℝ} (hd : 0 < d) :
    (∑' ip : Fin 2 × Nat.Primes,
      routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d
        (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) (ip, ip)) =
      (gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent d : ℂ) := by
  rw [tsum_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_diagonal hd]
  exact_mod_cast routePPrimitiveGammaJuliaPhysicalStokesLinearTrace_eq_completed hd

/-- **P-G105L capstone.**  The complete cofinal Hellinger kernel keeps actual finite physical
determinants, has the exact completed first trace, converges to an entire det2, and has no nonreal
zeros. -/
theorem routePPrimitive_GammaJulia_physicalStokesHellingerCofinalDeterminant :
    ∀ (d : ℝ) (hd : 0 < d),
      HilbertSchmidt.IsHS
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d)) ∧
      IsSelfAdjoint (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d))) ∧
      Differentiable ℂ
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d)) ∧
      (∀ z : ℂ,
        routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) z = 0 → z.im = 0) ∧
      (∑' ip : Fin 2 × Nat.Primes,
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) (ip, ip)) =
        (gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent d : ℂ) := by
  intro d hd
  exact ⟨routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd _,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_isSelfAdjoint hd _,
    differentiable_routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 hd _,
    fun _ hzero =>
      routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2_zero_im hd _ hzero,
    routePPrimitiveGammaJuliaPhysicalStokesHellinger_diagonalTrace_eq_completed hd⟩

end

end RHTower
