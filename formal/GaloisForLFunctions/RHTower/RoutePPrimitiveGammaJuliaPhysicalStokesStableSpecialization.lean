import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesApertureResidueTransport
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaSignedBivariateStability

/-!
# Route P primitive Gamma--Julia physical Stokes stable specialization

P-G105I identifies the positive child trace with the literal oriented Stokes current and the
negative completion trace with the polar/Gamma countercurrent.  This file determines their forced
relative channel coordinate:

```text
r(d) = - polarCountercurrent(d) / firstTraceCurrent(d).
```

Both one-sided residues have magnitude four, so `r(d) -> 1` from the right and `r(d)>0` eventually.
The physical one-variable specialization of P-G105G is therefore

```text
z = 64 u,   w = r(d) u.
```

The factor `64` removes the child coefficient `1/64`; the positive ratio turns every upper-half
plane `u` into upper-half-plane child and pivot variables.  Hence every actual finite aperture-
transported P-G186 matrix inherits P-G105G stability near the wall.  Its generator trace is
`(1-r(d))` times the finite transported child trace, while the all-prime value is exactly the
completed prime--Gamma current.  At the wall `r(d)->1`: polar cancellation is balanced channel
geometry, not scalar subtraction.

This constructs the physical stable specialization and exact first coefficient.  It does not yet
construct the cofinal determinant or identify its full divisor with Xi.
-/

open Complex Matrix Filter Topology Set
open scoped Kronecker ComplexOrder

namespace RHTower

noncomputable section

/-- Literal oriented first-trace current is positive on the physical right ray. -/
theorem gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos
    {d : ℝ} (hd : 0 < d) :
    0 < gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := by
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent]
  have hsum := summable_gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm d
  refine hsum.tsum_pos (fun p => ?_) (⟨2, Nat.prime_two⟩ : Nat.Primes) ?_
  · rw [gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
      xiMassPrimeSquareEulerWeight_eq, abs_of_pos hd]
    positivity
  · rw [gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
      xiMassPrimeSquareEulerWeight_eq, abs_of_pos hd]
    positivity

/-- Forced polar-to-child channel ratio. -/
def routePPrimitiveGammaJuliaPhysicalStokesPivotRatio (d : ℝ) : ℝ :=
  -gammaSewnMobiusApertureStokesOrientedPolarCountercurrent d /
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d

/-- Four-unit prime and polar residues force balanced child/pivot ratio at the wall. -/
theorem tendsto_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio :
    Tendsto routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hnum :=
    tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsGT_zero.neg
  have hden :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero
  have hquot := hnum.div hden (by norm_num : (4 : ℝ) ≠ 0)
  convert hquot using 1
  · funext d
    rfl
  · norm_num

/-- Physical pivot ratio is positive throughout some punctured right neighborhood of the wall. -/
theorem eventually_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio_pos :
    ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      0 < routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d := by
  exact tendsto_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio.eventually
    (isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Ioi 0))

/-- Total physical linear trace is exactly the completed prime--Gamma current. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesLinearTrace_eq_completed
    {d : ℝ} (hd : 0 < d) :
    (1 - routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d =
      gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent d := by
  have hcur : gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ≠ 0 :=
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'
  rw [routePPrimitiveGammaJuliaPhysicalStokesPivotRatio]
  have hdecomp :=
    gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_eq_firstTrace_add_counter
      d hd.ne'
  rw [hdecomp]
  field_simp [hcur]
  ring

/-- Finite aperture scale diagonal is Hermitian. -/
theorem routePPrimitiveGammaJuliaStokesApertureDiagonal_conjTranspose {N : ℕ}
    (d : ℝ) (p : Fin N → Nat.Primes) :
    (routePPrimitiveGammaJuliaStokesApertureDiagonal d p)ᴴ =
      routePPrimitiveGammaJuliaStokesApertureDiagonal d p := by
  rw [routePPrimitiveGammaJuliaStokesApertureDiagonal, diagonal_conjTranspose]
  congr 1
  funext i
  change star ((Real.sqrt
    (routePPrimitiveGammaJuliaStokesApertureScaleSq d (p i)) : ℝ) : ℂ) = _
  rw [← starRingEnd_apply, Complex.conj_ofReal]

/-- Actual twice-conjugated depth-zero P-G186 source Gram remains positive semidefinite. -/
theorem routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_posSemidef
    {N : ℕ} (d : ℝ) (p : Fin N → Nat.Primes) (kappa : Fin N → ℝ) :
    (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
      d p kappa).PosSemidef := by
  let pe : Fin N → Nat.Primes × ℕ := fun i => (p i, 0)
  have h :=
    (routePPrimitiveBurnolPrimeLogConjugate_posSemidef pe kappa).conjTranspose_mul_mul_same
      (routePPrimitiveGammaJuliaStokesApertureDiagonal d p)
  rw [routePPrimitiveGammaJuliaStokesApertureDiagonal_conjTranspose] at h
  exact h

/-- Physical one-variable specialization of the full signed bivariate pencil. -/
def routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil {N : ℕ}
    (d : ℝ) (p : Fin N → Nat.Primes) (kappa : Fin N → ℝ) (u : ℂ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  routePPrimitiveGammaJuliaSignedBivariatePencil
    (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram d p kappa)
    (64 * u) (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d * u)

/-- Linear generator of the physical one-variable pencil. -/
def routePPrimitiveGammaJuliaPhysicalStokesCompletedGenerator {N : ℕ}
    (d : ℝ) (p : Fin N → Nat.Primes) (kappa : Fin N → ℝ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  (routePPrimitiveGammaJuliaSignedChannelDiagonal 64
      (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
        routePPrimitiveBurnolJuliaKreinBlock) ⊗ₖ
    routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram d p kappa

/-- Physical pencil is exactly identity plus scalar times its completed generator. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil_eq_generator
    {N : ℕ} (d : ℝ) (p : Fin N → Nat.Primes)
    (kappa : Fin N → ℝ) (u : ℂ) :
    routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil d p kappa u =
      1 + u • routePPrimitiveGammaJuliaPhysicalStokesCompletedGenerator d p kappa := by
  have hchannel :
      routePPrimitiveGammaJuliaSignedChannelDiagonal (64 * u)
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d * u) *
            routePPrimitiveBurnolJuliaKreinBlock =
        u • (routePPrimitiveGammaJuliaSignedChannelDiagonal 64
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
            routePPrimitiveBurnolJuliaKreinBlock) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [routePPrimitiveGammaJuliaSignedChannelDiagonal,
        routePPrimitiveBurnolJuliaKreinBlock] <;> ring
  rw [routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil,
    routePPrimitiveGammaJuliaSignedBivariatePencil,
    routePPrimitiveGammaJuliaPhysicalStokesCompletedGenerator,
    hchannel, Matrix.smul_kronecker]

/-- Actual finite generator trace is the physical channel imbalance times finite child current. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesCompletedGenerator_trace
    {N : ℕ} {d : ℝ} (hd : 0 < d) (p : Fin N → Nat.Primes)
    (kappa : Fin N → ℝ) :
    (routePPrimitiveGammaJuliaPhysicalStokesCompletedGenerator
      d p kappa).trace.re =
      (1 - routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
        ∑ i, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d (p i) := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesCompletedGenerator,
    Matrix.trace_kronecker]
  have hchannel :
      (routePPrimitiveGammaJuliaSignedChannelDiagonal 64
        (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
          routePPrimitiveBurnolJuliaKreinBlock).trace =
        ((1 - routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d : ℝ) : ℂ) := by
    simp [routePPrimitiveGammaJuliaSignedChannelDiagonal,
      routePPrimitiveBurnolJuliaKreinBlock, Matrix.trace]
    ring
  rw [hchannel]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_trace hd]

/-- Positive pivot ratio makes physical specialization upper-half-plane stable. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil_stable
    {N : ℕ} {d : ℝ}
    (hratio : 0 < routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d)
    (p : Fin N → Nat.Primes) (kappa : Fin N → ℝ) {u : ℂ}
    (hu : 0 < u.im) :
    (routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil
      d p kappa u).det ≠ 0 := by
  let H := routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram d p kappa
  have hH : H.PosSemidef :=
    routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_posSemidef d p kappa
  rw [routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil,
    routePPrimitiveGammaJuliaSignedBivariatePencil_det_eq_prod_eigenfactors
      H hH.isHermitian]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  apply routePPrimitiveGammaJuliaSignedBivariateFactor_stable _
    (hH.eigenvalues_nonneg i)
  · simpa [Complex.mul_im] using
      mul_pos (by norm_num : (0 : ℝ) < 64) hu
  · simpa [Complex.mul_im] using mul_pos hratio hu

/-- Every actual finite physical pencil is stable throughout a punctured right wall neighborhood. -/
theorem eventually_routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil_stable
    {N : ℕ} (p : Fin N → Nat.Primes) (kappa : Fin N → ℝ) :
    ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      ∀ u : ℂ, 0 < u.im →
        (routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil
          d p kappa u).det ≠ 0 := by
  filter_upwards
    [eventually_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio_pos] with d hd
  intro u hu
  exact routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil_stable hd p kappa hu

/-- **P-G105J capstone.** Forced physical pivot ratio tends one and is eventually positive; every
actual finite source pencil is then stable, and its all-prime linear trace is exactly completed
prime--Gamma current. -/
theorem routePPrimitive_GammaJulia_physicalStokesStableSpecialization :
    Tendsto routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
      (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    (∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      0 < routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) ∧
    (∀ (d : ℝ), 0 < d →
      (1 - routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d =
        gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent d) ∧
    (∀ (N : ℕ) (p : Fin N → Nat.Primes) (kappa : Fin N → ℝ),
      ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
        ∀ u : ℂ, 0 < u.im →
          (routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil
            d p kappa u).det ≠ 0) := by
  exact ⟨tendsto_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio,
    eventually_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio_pos,
    fun _ hd => routePPrimitiveGammaJuliaPhysicalStokesLinearTrace_eq_completed hd,
    fun _ => eventually_routePPrimitiveGammaJuliaPhysicalStokesCompletedPencil_stable⟩

end

end RHTower
