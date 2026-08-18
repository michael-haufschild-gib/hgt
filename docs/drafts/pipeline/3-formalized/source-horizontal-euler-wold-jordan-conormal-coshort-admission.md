# Source-horizontal Euler--Wold Jordan conormal co-short admission

- **ID:** P-G208-JCA
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · Route P first open core
- **Statement:** On every retained Xi copy, the unrecompressed Euler/Wold Hahn--Jordan pair admits componentwise into the literal four-orientation conormal Schur short, and the physical endpoint response is exactly the source Green--Stokes co-short complement of the admitted Wold leg.

## Goal

Close Route P's physical-admission interface without assuming Loewner order, equivariance,
post-divisor passivity, scalar contractivity, or RH.  Required theorem must use the actual
multiplicity-split completed-Xi conormal coordinate and preserve the negative Euler and positive
Wold legs separately.

## Gates

- [x] 0 → 1 in-progress: exact finite statement frozen below; source-pure attack; hostile tests and
  Door passport recorded
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, exact leaf build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone theorem/proof/Lean certificate and external Door-2 audit

## Frozen conjecture

For `c` equal to the actual multiplicity-split completed-Xi forward conormal coordinate, put

```text
S(c) = Schur_0(routePJuliaSharedOrientationOrbitBlock c) = 4 |c|^2.
```

Let `M_-(N)` and `M_+(N)` be the intrinsic Hahn--Jordan negative Euler and positive Wold masses.
The componentwise physical admission is

```text
A_-(c,N) = -M_-(N) S(c),
A_+(c,N) =  M_+(N) S(c).
```

It must equal the literal Schur short of the already transported Euler and Wold selected matrices,
not merely an abstract scalar proxy.  Moreover, with `R(c,q,N)` the existing literal regularized
Xi-conormal endpoint response,

```text
A_+(c,N) + R(c,q,N) = 2 S(c)                                  (JCA)
```

at every finite clock.  No divisor-fitted scalar is permitted.  Actual Burnol top-conormal
tomography must identify `c`, and summing over the support fibre must multiply the admitted pair by
the analytic multiplicity.

## Conjecture loop

### C0 — orthogonal primitive/Xi Gram innovation

**Conjecture.** Identify the Jordan masses with father/detail energies of the mixed primitive
Burnol/Xi Cauchy Gram.

**Verdict:** `[FALSIFIED]`.  The Schur innovation ratio depends on the Xi horizontal rate and
ordinate, whereas `M_±(N)` depend only on the intrinsic prime clock.  Equality requires a fitted
divisor-dependent normalization and is not source-natural.

**Strongest positive survivor.** Keep the Xi coordinate itself, but apply Hahn--Jordan weights only
after the canonical four-orientation short.  Search for a scale-free conservation law rather than
matching Gram energies.

### C1 — Green--Stokes co-short complement

**Conjecture.** `(JCA)` holds exactly.

**Attack.** Corpus gives

```text
M_+(N) = 2 I_N,
I_N + E_N = 1,
R(c,q,N) = 2 S(c) E_N.
```

Therefore `A_+ + R = 2 S(c)(I_N+E_N)=2S(c)`.  Euler admission is independent and
componentwise, so no grade-forgetting occurs.  Remaining work is Lean verification of literal
matrix shorts, actual Burnol coordinate provenance, and support-fibre multiplicity.

## Paper proof

**Theorem `[PROVED HERE]`.** Frozen conjecture holds at every finite source clock.

**Proof.** Let `B(c)` be the four-orientation orbit block.  Corpus's exact diagonalization gives

```text
B(c) = diag(4|c|^2,4),       Schur_0(B(c)) = S(c)=4|c|^2.
```

The off-diagonal entries vanish, so for every real scalar `a`, including either sign,

```text
Schur_0(a B(c)) = a S(c).
```

The selected Euler and Wold residual matrices are respectively `-M_-(N)B(c)` and
`M_+(N)B(c)`.  Their literal shorts are therefore `A_-(c,N)` and `A_+(c,N)`, proving
componentwise admission before any addition or grade-forgetting.

Write `I_N` and `E_N` for source-horizontal BV interior and endpoint third jets.  By expansion of
the finite Wold moment,

```text
M_+(N)=2 I_N.
```

Finite Green--Stokes conservation gives `I_N+E_N=1`.  Existing coefficient-exact Xi landing gives
`R(c,q,N)=8|c|^2 E_N=2S(c)E_N`.  Consequently

```text
A_+(c,N)+R(c,q,N)
 = 2 I_N S(c)+2 E_N S(c)
 = 2 S(c).
```

For actual fibre admission, take `c` to be the completed Gamma--Julia forward residue after the
canonical multiplicity split.  Existing equal-split residue law reduces it to the source coupling
times the base Xi conormal feature.  Actual Burnol nested-window tomography identifies that feature
with the multiplicity-exact top-conormal jet at every positive aperture.  The reduced coordinate is
independent of copy index; summing the admitted pair over the support fibre therefore multiplies it
by the fibre cardinality, which equals analytic multiplicity.  Every assertion is unconditional.
∎

### Cofinal-character classification `[PROVED HERE]`

For real coefficients `(a,b,d)`, define the reporter on admitted Euler, Wold, and endpoint
channels by

```text
L_(a,b,d)(N) = a A_-(c,N) + b A_+(c,N) + d R(c,q,N).
```

The known source limits `M_-(N),M_+(N) -> 2/3` and `R(c,q,N) -> 16|c|^2/3` give

```text
L_(a,b,d)(N) -> (8/3)|c|^2(-a+b+2d).                    (CHAR)
```

If `c != 0`, the cofinal reporter vanishes exactly on the coefficient plane
`-a+b+2d=0`.  Direct finite expansion shows the existing compensated primitive-budget energy is
literally `L_(1,-1,1)(N)`.  Its coefficient vector lies in that plane, explaining—without a
soft asymptotic argument—how compensated budget tends to zero while the endpoint response remains
nonzero.  Thus a new useful source reporter must be transverse to this plane.  Repeating the
existing compensated budget cannot control the endpoint.

## Door passport

- **Source:** finite prime-labelled Euler `k^2` jet, Wold counterterm, BV Green--Stokes endpoint,
  and actual nested Burnol top-conormal ratio.
- **Bridge:** completed Gamma/polar two-residue transport followed by multiplicity equal split and
  four-orientation Julia orbit.
- **Endpoint:** existing finite regularized Xi-conormal response; no RH endpoint theorem is used in
  proof of `(JCA)`.
- **Non-circularity:** all identities are finite-clock algebra or unconditional residue limits.
  No statement asserts endpoint nonnegativity for all Xi fibres or primitive-budget domination.

## External frontier audit

Classical and current shorted-operator theory studies variational/complementability properties of
Schur complements and conservative realizations.  Cattaneo--Mnev's 2026 BV pushforward theorem
constructs a strong deformation retract and quasi-inverse for observables.  Paugam constructs the
functional-equation symplectic pairing on the zeta zero space.  None of these sources supplies the
arithmetic finite-clock identity `(JCA)`, a multiplicity-exact Burnol/Xi conormal coordinate, or an
Euler/Wold Green--Stokes complement on one selected Xi fibre.  Novelty remains bounded-audit only
until independent expert review.

## No-go closure

- **Exact killing mechanism for C0:** mixed Cauchy coherence is divisor-dependent; intrinsic Jordan
  masses are divisor-independent.
- **Strongest positive survivor:** exact Green--Stokes co-short complement C1.
- **New insight:** endpoint is not a fitted projection of the Jordan pair.  It is the canonical
  complement of the positive Wold short inside two copies of the literal conormal short, while the
  negative Euler short remains an independent action leg.  Existing primitive-budget reporter is
  exactly the blind character `(1,-1,1)`; next producer must have `-a+b+2d != 0` while retaining a
  source budget.
- **Status:** C1 dependency-closed paper proof and Lean formalization complete. Exact source check and
  exact leaf build pass; capstone, fibre, limit, and reporter-classification declarations use only
  `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-18 — C0 falsified; C1 frozen in 1-in-progress after corpus and primary-literature audit.
- 2026-08-18 — C1 proved on paper and in scratch Lean; promoted to 2-fully-proven.
- 2026-08-18 — classified every cofinal linear reporter and proved existing compensated budget is
  exactly the blind `(1,-1,1)` character.
- 2026-08-18 — formalized in
  `SourceHorizontalEulerWoldJordanConormalCoShortAdmission.lean`, wired into `RHTower.lean`, and
  passed exact leaf build plus axiom audit; promoted to 3-formalized.
