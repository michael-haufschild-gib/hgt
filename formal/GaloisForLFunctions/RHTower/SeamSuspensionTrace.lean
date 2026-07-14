/-
The seam-suspension trace: the compression mechanism and the two equivalent forms of the bridge.

The seam-suspension construction assembles the completed flux cochain `−ξ'/ξ` as a flat supertrace of a
resolvent `(s − Θ_Δ)⁻¹` over a three-degree seam complex — finite-prime closed returns (`ζ'/ζ`), the
Gaussian archimedean oscillator (`Γ_ℝ'/Γ_ℝ`), and two boundary states (`1/s + 1/(s−1)`) — summing to
`ξ'/ξ` because `ξ = ½s(s−1)Γ_ℝ ζ`.  Three formalizable cores of that construction:

* **§4 sector split** (`logDeriv_completed_split`): the completed log-derivative decomposes into the
  archimedean sector and the finite sector, `logDeriv(archFactor · ζ) = logDeriv archFactor +
  logDeriv ζ`.  With `ξ = archFactor · ζ` (`ZetaCarrier.xi_eq_archFactor_mul_zeta`) and
  `archFactor = s(s−1)/2 · Gammaℝ` this is the flat supertrace identity `Str^♭ = ξ'/ξ` at the
  log-derivative level: the three seam sectors sum to `ξ'/ξ`.

* **§7 compression mechanism**: the legacy declarations
  `supertrace_supercommutator_zero` and `flat_eq_cohomology_trace` record ordinary trace cyclicity
  for an ordinary commutator.  The grading-aware declarations `gradedMatrixTrace`,
  `gradedMatrixTrace_oddAnticommutator_zero`, and `gradedMatrixTrace_hodgeCompression` encode the
  actual BRST/supersymmetric statement: for `Str_Γ(A)=Tr(ΓA)` and an odd `d`, the supertrace of
  `dX+Xd` vanishes, so the Hodge relation `I − P = dh + hd` compresses the full graded trace to the
  harmonic sector.

* **§10 Herglotz positivity** (`herglotz_rank_one_psd`): the equivalent spectral form of the bridge.
  A Nevanlinna/Herglotz function `G(z) = ∫ dν(λ)/(z − iλ)` with `ν ≥ 0` has a positive-semidefinite
  kernel `K(z,w) = (G(z) + conj G(w))/(z + conj w)`, because it is an integral of the rank-one PSD
  kernels `v(z)·conj(v(w))`, `v(z) = 1/(z − iλ)`.  The rank-one PSD core is proved here: the Gram-type
  sum `Σ_{i,j} v_i·conj(v_j)·c_i·conj(c_j) = |Σ_i c_i v_i|² ≥ 0`.

Both the Hodge relation `I − P = dG + Gd` (with renormalized cyclicity) and the Herglotz positivity
`K_Δ ≥ 0` are the two faces of the single remaining bridge; each would give
`Str((s − Θ_Δ)⁻¹ | H_Δ) = ξ'/ξ` on the positive `H_Δ^1`.
-/
import GaloisForLFunctions.RHTower.ZetaCarrier

noncomputable section

namespace RHTower

open Complex Matrix

/-! ### §4 The sector split of the completed log-derivative -/

/-- **The completed flux cochain splits into archimedean and finite sectors.**
`logDeriv(archFactor · ζ) = logDeriv archFactor + logDeriv ζ`.  With `ξ = archFactor · ζ` and
`archFactor = s(s−1)/2 · Gammaℝ`, this is the seam-suspension flat supertrace `Str^♭ = ξ'/ξ` at the
log-derivative level: the boundary sector `1/s + 1/(s−1)` (from `s(s−1)`), the archimedean sector
`Γ_ℝ'/Γ_ℝ` (from `Gammaℝ`), and the finite sector `ζ'/ζ` sum to `ξ'/ξ`. -/
theorem logDeriv_completed_split {s : ℂ} (haf : archFactor s ≠ 0) (hz : riemannZeta s ≠ 0)
    (hda : DifferentiableAt ℂ archFactor s) (hdz : DifferentiableAt ℂ riemannZeta s) :
    logDeriv (fun z => archFactor z * riemannZeta z) s
      = logDeriv archFactor s + logDeriv riemannZeta s :=
  logDeriv_mul s haf hz hda hdz

/-! ### §7 The compression mechanism: flat supertrace = cohomology supertrace -/

/-- **Legacy ordinary-commutator trace identity.**  `tr(dX − Xd) = 0`, by trace cyclicity.  The
historical declaration name is retained for compatibility; the grading-aware supertrace and odd
anticommutator appear below. -/
theorem supertrace_supercommutator_zero {n : Type*} [Fintype n] [DecidableEq n]
    (d X : Matrix n n ℂ) : (d * X - X * d).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- **Legacy ordinary-trace compression.**  If the off-cohomology part `(I − P)·R` is separately
given as an ordinary commutator `dY − Yd`, then ordinary trace cyclicity yields
`tr R = tr(P·R)`.  A Hodge relation naturally gives the odd anticommutator `dY+Yd`; its valid
graded-trace consumer is `gradedMatrixTrace_hodgeCompression` below. -/
theorem flat_eq_cohomology_trace {n : Type*} [Fintype n] [DecidableEq n]
    (P Res d Y : Matrix n n ℂ) (h : (1 - P) * Res = d * Y - Y * d) :
    Res.trace = (P * Res).trace := by
  have hc : ((1 - P) * Res).trace = 0 := by
    rw [h, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub] at hc
  exact sub_eq_zero.mp hc

/-! ### Grading-aware BRST/Hodge compression -/

/-- The finite graded trace `Str_Γ(A)=Tr(ΓA)`.  In a boson/fermion decomposition, `Γ` is the
parity operator with eigenvalues `+1` and `-1`. -/
def gradedMatrixTrace {n : Type*} [Fintype n] [DecidableEq n]
    (Γ A : Matrix n n ℂ) : ℂ :=
  (Γ * A).trace

/-- **The genuine odd-supercommutator cancellation.**  If `d` is odd for the grading `Γ`, then
the graded trace of the anticommutator `dX+Xd` vanishes.  No parity premise on `X` is needed for
this trace identity. -/
theorem gradedMatrixTrace_oddAnticommutator_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (Γ d X : Matrix n n ℂ) (hodd : Γ * d = -(d * Γ)) :
    gradedMatrixTrace Γ (d * X + X * d) = 0 := by
  have hcancel : (Γ * (d * X)).trace = -(Γ * (X * d)).trace := by
    calc
      (Γ * (d * X)).trace = ((Γ * d) * X).trace := by rw [mul_assoc]
      _ = ((-(d * Γ)) * X).trace := by rw [hodd]
      _ = -((d * Γ) * X).trace := by simp
      _ = -(d * (Γ * X)).trace := by rw [mul_assoc]
      _ = -((Γ * X) * d).trace := by rw [Matrix.trace_mul_comm]
      _ = -(Γ * (X * d)).trace := by rw [mul_assoc]
  rw [gradedMatrixTrace, Matrix.mul_add, Matrix.trace_add, hcancel]
  simp

/-- **Finite graded Hodge compression.**  If `d` is odd, the Hodge complement is
`1-P=dh+hd`, and `Res` commutes with `d`, then the full graded trace equals the harmonic compressed
graded trace.  This is the finite, non-renormalized seam-compression identity. -/
theorem gradedMatrixTrace_hodgeCompression
    {n : Type*} [Fintype n] [DecidableEq n]
    (Γ P Res d h : Matrix n n ℂ)
    (hodd : Γ * d = -(d * Γ))
    (hHodge : 1 - P = d * h + h * d)
    (hcomm : d * Res = Res * d) :
    gradedMatrixTrace Γ Res = gradedMatrixTrace Γ (P * Res) := by
  have hres : (1 - P) * Res =
      d * (h * Res) + (h * Res) * d := by
    rw [hHodge, Matrix.add_mul]
    calc
      (d * h) * Res + (h * d) * Res =
          d * (h * Res) + h * (d * Res) := by simp only [mul_assoc]
      _ = d * (h * Res) + h * (Res * d) := by rw [hcomm]
      _ = d * (h * Res) + (h * Res) * d := by simp only [mul_assoc]
  have hzero : gradedMatrixTrace Γ ((1 - P) * Res) = 0 := by
    rw [hres]
    exact gradedMatrixTrace_oddAnticommutator_zero Γ d (h * Res) hodd
  rw [gradedMatrixTrace, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_sub, Matrix.trace_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- A two-sided inverse inherits every commutation relation of the inverted matrix.  Applied to
`A=s-Θ`, this discharges resolvent/differential commutation from generator/differential
commutation. -/
theorem matrixTwoSidedInverse_commutes
    {n : Type*} [Fintype n] [DecidableEq n]
    (A Res d : Matrix n n ℂ)
    (hRA : Res * A = 1) (hAR : A * Res = 1)
    (hAd : A * d = d * A) :
    d * Res = Res * d := by
  calc
    d * Res = (Res * A) * (d * Res) := by rw [hRA, Matrix.one_mul]
    _ = Res * (A * d) * Res := by simp only [mul_assoc]
    _ = Res * (d * A) * Res := by rw [hAd]
    _ = (Res * d) * (A * Res) := by simp only [mul_assoc]
    _ = Res * d := by rw [hAR, Matrix.mul_one]

/-- For self-adjoint matrices, one inverse equation supplies the other by adjunction.  This is the
finite resolvent form of `HTGeometry.rightGreen_eq_of_leftGreen_of_selfAdjoint`. -/
theorem matrixLeftInverse_of_rightInverse_of_selfAdjoint
    {n : Type*} [Fintype n] [DecidableEq n]
    (A Res : Matrix n n ℂ)
    (hA : IsSelfAdjoint A) (hRes : IsSelfAdjoint Res)
    (hRA : Res * A = 1) :
    A * Res = 1 := by
  have hstar := congrArg star hRA
  simpa only [star_mul, star_one, hA.star_eq, hRes.star_eq] using hstar

/-- A self-adjoint inverse inherits commutation from the inverted self-adjoint matrix from a
single inverse equation. -/
theorem matrixSelfAdjointInverse_commutes
    {n : Type*} [Fintype n] [DecidableEq n]
    (A Res d : Matrix n n ℂ)
    (hA : IsSelfAdjoint A) (hRes : IsSelfAdjoint Res)
    (hRA : Res * A = 1)
    (hAd : A * d = d * A) :
    d * Res = Res * d := by
  exact matrixTwoSidedInverse_commutes A Res d hRA
    (matrixLeftInverse_of_rightInverse_of_selfAdjoint A Res hA hRes hRA) hAd

/-- **Resolvent form of finite graded Hodge compression.**  The explicit resolvent-commutation
premise is removed: two-sided inverse equations and commutation of the inverted generator with
the differential imply it automatically. -/
theorem gradedMatrixTrace_hodgeCompression_of_twoSidedInverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (Γ P A Res d h : Matrix n n ℂ)
    (hodd : Γ * d = -(d * Γ))
    (hHodge : 1 - P = d * h + h * d)
    (hRA : Res * A = 1) (hAR : A * Res = 1)
    (hAd : A * d = d * A) :
    gradedMatrixTrace Γ Res = gradedMatrixTrace Γ (P * Res) := by
  exact gradedMatrixTrace_hodgeCompression Γ P Res d h hodd hHodge
    (matrixTwoSidedInverse_commutes A Res d hRA hAR hAd)

/-- **Self-adjoint one-inverse resolvent compression.**  When the inverted generator and its
resolvent are self-adjoint, `Res A = 1` implies `A Res = 1` by adjunction.  The finite graded Hodge
compression theorem therefore needs only one inverse equation. -/
theorem gradedMatrixTrace_hodgeCompression_of_selfAdjointInverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (Γ P A Res d h : Matrix n n ℂ)
    (hodd : Γ * d = -(d * Γ))
    (hHodge : 1 - P = d * h + h * d)
    (hA : IsSelfAdjoint A) (hRes : IsSelfAdjoint Res)
    (hRA : Res * A = 1)
    (hAd : A * d = d * A) :
    gradedMatrixTrace Γ Res = gradedMatrixTrace Γ (P * Res) := by
  exact gradedMatrixTrace_hodgeCompression_of_twoSidedInverse
    Γ P A Res d h hodd hHodge hRA
    (matrixLeftInverse_of_rightInverse_of_selfAdjoint A Res hA hRes hRA) hAd

/-! ### §10 The Herglotz kernel positivity (the equivalent spectral form of the bridge) -/

/-- **The Herglotz/Nevanlinna rank-one kernel is positive semidefinite.**  For any nodes and
coefficients, `Σ_{i,j} v_i·conj(v_j)·c_i·conj(c_j) = |Σ_i c_i v_i|² ≥ 0`.  Taking
`v_i = 1/(z_i − iλ)` this is the positivity of the single-pole Herglotz kernel
`1/((z − iλ)(conj w + iλ))`; integrating against `ν ≥ 0` gives the positivity of the seam Herglotz
kernel `K_Δ(z,w) = (G_Δ(z) + conj G_Δ(w))/(z + conj w)`, whose positivity is equivalent (Nevanlinna
realization) to the existence of the self-adjoint seam generator `T_Δ` with
`Str_ren((s − Θ_Δ)⁻¹) = ξ'/ξ`.  This is the spectral face of the remaining bridge. -/
theorem herglotz_rank_one_psd {N : Type*} [Fintype N] (v c : N → ℂ) :
    0 ≤ (∑ i, ∑ j, (v i * (starRingEnd ℂ) (v j)) * (c i * (starRingEnd ℂ) (c j))).re := by
  have hsq : (∑ i, ∑ j, (v i * (starRingEnd ℂ) (v j)) * (c i * (starRingEnd ℂ) (c j)))
      = (∑ i, c i * v i) * (starRingEnd ℂ) (∑ i, c i * v i) := by
    rw [map_sum, Finset.sum_mul_sum]
    congr 1; ext i; congr 1; ext j; simp [map_mul]; ring
  rw [hsq, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end RHTower
