# The Xi logarithmic derivative has a canonical positive real-boundary divisor measure

- **ID:** `xi-logderivative-real-boundary-divisor-measure`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper); Route-A boundary construction
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** the theta-source entire function `XiC` and the distributional boundary value of a
  meromorphic logarithmic derivative
- **Statement:** The upper boundary value of `-Im(XiC'/XiC)/pi` converges locally as a distribution
  to the positive atomic measure on the real Xi zeros, with each atom weighted by its analytic
  multiplicity.  Nonreal conjugate zero pairs contribute no boundary atom.

## General boundary identity

Let `F` be a nonzero entire function satisfying

```text
F(conj(z))=conj(F(z)).                                  (1)
```

Its zeros are locally finite and stable under conjugation.  Near a real zero `gamma` of
multiplicity `m_gamma`,

```text
F'(z)/F(z)=m_gamma/(z-gamma)+h_gamma(z),                (2)
```

where `h_gamma` is holomorphic and real on the real axis near `gamma`.

For `epsilon>0`, define locally away from horizontal zero hits

```text
d nu_epsilon(t)
  =-(1/pi) Im(F'(t+i epsilon)/F(t+i epsilon)) dt.        (3)
```

The singular term in (2) gives

```text
-(1/pi) Im(m_gamma/(t-gamma+i epsilon))
  =(m_gamma/pi)
    epsilon/((t-gamma)^2+epsilon^2).                    (4)
```

The right side is the Poisson approximation to `m_gamma delta_gamma`.  The holomorphic remainder
has imaginary part tending locally uniformly to zero on the real axis.

A nonreal pair `rho,conj(rho)` contributes

```text
1/(t-rho)+1/(t-conj(rho))
```

in the boundary limit.  This is real for real `t`, so its contribution to (3) tends to zero.
Applying this on each compact set, which meets only finitely many zeros, proves the local
distributional convergence

```text
nu_epsilon
  -> sum_(gamma in R, F(gamma)=0)
       m_gamma delta_gamma.                             (5)
```

Equivalently, (5) is the jump of `F'/F` across the real axis.

## Xi specialization

Take

```text
F=XiC,
XiC(z)=xi(1/2+i z).
```

`XiC` is entire and real on the real axis, so (1) holds.  Equation (5) gives the canonical positive
real-boundary divisor measure

```text
nu_Xi
  =sum_(gamma in R, XiC(gamma)=0)
      ord_gamma(XiC) delta_gamma.                       (6)
```

Definition (3) uses only the theta-source function and its logarithmic derivative; it does not list
or assume the locations of the zeros.  Formula (6) is the resulting boundary theorem.

## Positive semisimple Hilbert space

On finitely supported real-zero data define

```text
||c||_Xi^2
  =integral |c(t)|^2 d nu_Xi(t)
  =sum_gamma m_gamma |c_gamma|^2.                       (7)
```

Its completion is positive.  Real translation acts on the atom at `gamma` by
`exp(-i a gamma)`, so it is unitary.  Multiplicity is retained as the positive atom weight while
nilpotent local jets are not inserted into the Hilbert space.

Thus (6)--(7) construct, unconditionally, the positive semisimple defect carried by the real part of
the Xi divisor.

## Exact limitation

The analytic divisor current contains every complex zero, whereas (6) contains only real zeros.
A nonreal conjugate pair is visible in the meromorphic function `XiC'/XiC` but has no jump across
the real axis.  Therefore the assertion

```text
analytic Xi defect is exhausted by nu_Xi                           (8)
```

is equivalent to all Xi zeros being real, namely RH.

The theorem constructs the target positive boundary object but does not prove (8).

## Gates

- [x] multiplicity-safe Poisson boundary identity proved
- [x] nonreal conjugate-pair cancellation proved
- [x] Xi positive real-boundary measure constructed without zero input
- [x] positive semisimple Hilbert completion and unitary action constructed
- [x] analytic-to-real exhaustion isolated as the RH-bearing theorem (formalised as an
  equivalence with RH, not proved)


## Lean formalization (stage 3)

Unconditional and axiom-clean (`propext, Classical.choice, Quot.sound` only) in

- `formal/GaloisForLFunctions/HTGeometry/BoundaryCauchyKernel.lean`
- `formal/GaloisForLFunctions/HTGeometry/WeightedAtomHilbert.lean`
- `formal/GaloisForLFunctions/RHTower/RealBoundaryDivisorLimit.lean`
- `formal/GaloisForLFunctions/RHTower/XiRealBoundaryDivisorMeasure.lean`

### Gate 1 — multiplicity-safe Poisson boundary identity

`boundaryDensity F ε t = -(1/π) · Im (F'/F)(t + iε)` is the definition `(3)`.  At any height that
misses every local zero the identity `(2)` is

```text
RHTower.RealBoundaryDivisor.logDeriv_split_eventually :
  (∀ᶠ w in 𝓝 z, F w = (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * g w) → DifferentiableAt ℂ g z → g z ≠ 0 →
    (∀ ρ ∈ Z, z ≠ ρ) →
    logDeriv F z = (∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) + logDeriv g z
```

and the exponents are the analytic orders,
`RHTower.RealBoundaryDivisor.analyticOrderAt_eq_mult : analyticOrderAt F ρ = (m ρ : ℕ∞)`, so the
whole construction is multiplicity-safe.  Equation `(4)` — the singular term is the Poisson/Cauchy
kernel — is

```text
GaloisForLFunctions.HTGeometry.neg_im_inv_eq_cauchyPDFReal :
  -(((t : ℂ) - (γ : ℂ) + (ε : ℂ) * I)⁻¹).im = π * cauchyPDFReal γ s t
```

together with the approximate-identity theorem
`GaloisForLFunctions.HTGeometry.tendsto_integral_cauchyPDFReal_mul`.

### Gate 2 — nonreal conjugate-pair cancellation

`GaloisForLFunctions.HTGeometry.conjPairKernel ρ ε t = ((t + iε - ρ)⁻¹ + (t + iε - conj ρ)⁻¹).im`,
with `conjPairKernel_zero`, `norm_conjPairKernel_le` and

```text
GaloisForLFunctions.HTGeometry.tendsto_integral_conjPairKernel :
  ρ.im ≠ 0 → Integrable φ → Tendsto (fun ε => ∫ t, φ t * conjPairKernel ρ ε t) (𝓝 0) (𝓝 0)
```

The reindexing that turns the nonreal part of the pole sum into a sum of pair kernels (using
conjugation-stability of the zero set and conjugation-invariance of the multiplicities) is
`RHTower.RealBoundaryDivisor.boundaryDensity_decomp`.

The zero-free remainder is handled by
`RHTower.RealBoundaryDivisor.tendsto_integral_logDeriv_remainder`: the factor `g` agrees with
`F / ∏(z - ρ)^{m ρ}` off the (finite) zero set, that quotient is Schwarz-real, hence
`Im (g'/g) = 0` a.e. on the real slice (`im_logDeriv_eq_zero_of_schwarz`), and dominated
convergence on the compact base interval finishes.

Assembled:

```text
RHTower.RealBoundaryDivisor.tendsto_boundaryDensity_setIntegral :
  Differentiable ℂ F → (∀ z, F (conj z) = conj (F z)) → 0 ≤ r → r < R →
  z₀ ∈ ball (c : ℂ) R → F z₀ ≠ 0 → Continuous φ →
  (∀ t ∉ Ioo (c - r) (c + r), φ t = 0) →
  ∃ Γ : Finset ℝ,
    (∀ γ, γ ∈ Γ ↔ ((γ : ℂ) ∈ ball (c : ℂ) R ∧ F γ = 0)) ∧
    Tendsto (fun ε => ∫ t in Icc (c - r) (c + r), φ t * boundaryDensity F ε t)
      (𝓝[>] 0) (𝓝 (∑ γ ∈ Γ, ((analyticOrderAt F (γ : ℂ)).toNat : ℝ) * φ γ))
```

which is `(5)`.

### Gate 3 — the Xi measure, built without zero input

`XiC` is entire (`RHTower.XiC_differentiable`) and Schwarz-real (`RHTower.XiC_conj`), and
`RHTower.XiRealBoundary.exists_XiC_ne_zero_in_ball` supplies the nondegeneracy point in every disc
(from `XiC (-i) ≠ 0` and the identity theorem).  Hence `(6)`:

```text
RHTower.XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral :
  0 ≤ r → r < R → Continuous φ → (∀ t ∉ Ioo (c - r) (c + r), φ t = 0) →
  ∃ Γ : Finset ℝ,
    (∀ γ, γ ∈ Γ ↔ ((γ : ℂ) ∈ ball (c : ℂ) R ∧ XiC γ = 0)) ∧
    Tendsto (fun ε => ∫ t in Icc (c - r) (c + r), φ t * boundaryDensity XiC ε t)
      (𝓝[>] 0) (𝓝 (∑ γ ∈ Γ, ((analyticOrderAt XiC (γ : ℂ)).toNat : ℝ) * φ γ))
```

`boundaryDensity XiC` mentions only the theta-source function and its logarithmic derivative; the
zero list `Γ` is an output of the theorem, never an input.

### Gate 4 — the positive semisimple Hilbert space

The atom weights are positive integers,
`RHTower.XiRealBoundary.one_le_xiRealMult : 1 ≤ xiRealMult γ`, so the weighted form `(7)` is
realised by splitting each real zero into `m_γ` atoms:

```text
XiBoundaryAtom    := Σ γ : XiRealZero, Fin (xiRealMult γ)
XiBoundaryHilbert := lp (fun _ : XiBoundaryAtom => ℂ) 2
```

which is a complete positive inner-product space by construction, and

```text
RHTower.XiRealBoundary.norm_xiOfFinsupp_sq (c : XiRealZero →₀ ℂ) :
  ‖xiOfFinsupp c‖ ^ 2 = ∑ γ ∈ c.support, (xiRealMult γ : ℝ) * ‖c γ‖ ^ 2
```

is exactly `(7)`.  Real translation acts by the character `exp (-i a γ)` on the atom at `γ`:

```text
RHTower.XiRealBoundary.xiBoundaryTranslation (a : ℝ) :
  XiBoundaryHilbert ≃ₗᵢ[ℂ] XiBoundaryHilbert
RHTower.XiRealBoundary.xiBoundaryTranslation_zero
RHTower.XiRealBoundary.xiBoundaryTranslation_add
```

a unitary one-parameter group (`GaloisForLFunctions.HTGeometry.lpPhaseUnitary` and its group law).
Multiplicity enters only as an atom count, so the nilpotent local jets are never inserted.

### Gate 5 — the exact limitation

Two theorems isolate what the construction does *not* give.

```text
RHTower.RealBoundaryDivisor.exists_nonreal_pair_with_vanishing_boundary_measure :
  ∃ F, Differentiable ℂ F ∧ (∀ z, F (conj z) = conj (F z)) ∧ F I = 0 ∧ F (-I) = 0 ∧
    (∀ γ : ℝ, F γ ≠ 0) ∧ (the boundary limit is 0 against every test function)
```

(witness `z ↦ z² + 1`): a Schwarz-real entire function can carry a whole conjugate pair of zeros
and still have identically vanishing real-boundary measure.  And at the source,

```text
RHTower.XiRealBoundary.xiBoundaryExhaustsDivisor_iff_riemannHypothesis :
  XiBoundaryExhaustsDivisor ↔ RiemannHypothesis
```

so assertion `(8)` is exactly RH.  It is stated as an equivalence and deliberately not proved.

### Reused corpus infrastructure

`HTGeometry.exists_finset_zeroFree_factorization`, `HTGeometry.logDeriv_finset_prod_pow`
(`AnalyticBallFinsetFactorization`), `RHTower.analyticOrderAt_conj_of_conjEquivariant`
(`Reflection`), `RHTower.XiC_conj` / `XiC_differentiable` (`XiEntireReal`),
`RHTower.xi_ne_zero_of_one_le_re` (`RHLadderTheory`),
`RHTower.SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero`, and mathlib's
`cauchyPDFReal`, `tendsto_integral_comp_smul_smul_of_integrable`, `logDeriv_prod`,
`deriv_conj_conj`, `AnalyticAt.analyticOrderAt_eq_natCast`, `lp`/`Memℓp`.

**Stage:** 3-formalized.
