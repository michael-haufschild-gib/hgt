# Xi completed-aperture reflection-sector odd-detector law

- **ID:** `xi-completed-aperture-reflection-sector-odd-detector-law`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM / NO-GO WITH POSITIVE SURVIVOR (paper + Lean)
- **Lean:** `GaloisForLFunctions.RHTower.XiCompletedApertureReflectionKernel`
- **Inputs:** `SeamFluxCompletion.lean`, `CompletedFluxGradedReality.lean`, the true-aperture
  transport phase, and `XiAperturePoissonResponseSignature.lean`
- **Scientific status:** `[PROVED HERE ON PAPER AND IN LEAN] [CORPUS-NEW]`
  `[CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`

## Exact theorem

Let `S(s)=-xi'(s)/xi(s)` be the completed prime--Gamma seam flux and define the transverse
off-diagonal aperture kernel

```text
K_u(x,y)=S(1/2+u+i(x-y)),                    u,x,y real.               (1)
```

Schwarz reality and the Xi functional equation give the exact two-axis reflection laws

```text
K_u(y,x)=conj(K_u(x,y)),                                             (2)
K_(-u)(x,y)=-K_u(y,x).                                               (3)
```

At the critical aperture `u=0`, `(3)` becomes

```text
K_0(y,x)=-K_0(x,y),       K_0(x,x)=0.                                (4)
```

Consequently every odd-cardinality packet

```text
[K_0(x_i,x_j)]_(i,j=1)^n,       n odd,                              (5)
```

has determinant zero.  In particular the completed critical seam cannot carry the strictly
negative three-node determinant required to select one off-line squared-Xi orbit.

More strongly, split the reflected aperture pair into

```text
E_u=K_u+K_(-u),       O_u=K_u-K_(-u).                                (6)
```

Then

```text
E_u(x,y)=K_u(x,y)-K_u(y,x),       E_u^T=-E_u,                         (7)
O_u(x,y)=K_u(x,y)+K_u(y,x)=2 Re K_u(x,y),       O_u^T=O_u.           (8)
```

Every odd packet of the aperture-even sector `E_u` is singular, at every `u`.  The aperture-odd
sector `O_u` is real symmetric and is therefore the unique reflection sector in this completed
kernel capable of carrying a nonzero odd detector.

## Paper proof

For real `u,x,y`, complex conjugation sends the argument in `(1)` to the argument with `x,y`
exchanged.  Schwarz equivariance of `S` gives `(2)`.  Also

```text
1-(1/2+u+i(y-x))=1/2-u+i(x-y),
```

so the odd functional-equation law `S(1-s)=-S(s)` gives `(3)`.  Equations `(4)`, `(7)`, and `(8)`
follow immediately.

If `A^T=-A` is an `n` by `n` complex matrix and `n` is odd, then

```text
det A=det A^T=det(-A)=(-1)^n det A=-det A,
```

hence `det A=0`.  Applying this first to `K_0` and then to `E_u` proves `(5)` and the all-aperture
even-sector statement.

## No-go and strongest positive survivor

The route “put the completed response directly on the critical seam and use its first sharp
three-node determinant” is terminal.  Functional-equation symmetry annihilates not only that
cubic but every odd detector at the center.  Adding the two reflected aperture sides does not
repair it: the aperture-even sector remains skew and all its odd determinants vanish.

The strongest positive survivor is the exact sector selection `(8)`: a nonzero transverse
aperture pair is mandatory, and only its aperture-odd real-symmetric difference can support the
needed three-node sign.  The live target is therefore no longer an unspecified off-diagonal
completion.  It is the sign and source realization of finite packets of

```text
2 Re S(1/2+u+i(x-y)),       u != 0,                                  (9)
```

joined to the fine-minus-coarse Poisson refinement and then to the global response saturation
inequality `(AC25)`.

## Why HTGeometry changes the reading

Finite fusion forces the full countably free source tower, while the minimal HT completion needs
both the source groupoid and a signed polarization; one cofinal ray is nonconservative.  The
reflection-sector law makes that abstract architecture concrete for the RH carrier.  Compressing
to the critical ray or to the reflection-even sum destroys every odd detector.  The surviving
object must retain two-sided transverse aperture data until after the completed prime--Gamma
coupling is formed, and only then take the reflection-odd real-symmetric sector.

Combined with the true-aperture compactness phase, this says the required carrier must join the
unique noncompact unit boundary to compact deeper apertures without collapsing their signed
cross-aperture relation into a positive Gram or a centered seam.

## Hostile audit

1. Matrix skew-symmetry and `det(-A)=(-1)^n det A` are classical parent facts.  Candidate novelty
   is the exact completed Xi aperture-sector classification and the resulting exclusion/selection
   of the RH detector carrier.
2. The theorem constructs the canonical completed off-diagonal kernel and classifies its
   reflection sectors, but does not prove that `(9)` has negative three-node determinant.
3. No zero-location assumption enters the proof; only the already unconditional functional
   equation and Schwarz reality are used.
4. External specialist novelty review remains open.

## Gates

- [x] 0 -> 1: exact completed source kernel and obstruction identified
- [x] 1 -> 2: dependency-closed all-odd-detector proof
- [x] 2 -> 3: Lean reflection laws, center no-go, all-odd determinant law, sector classification
- [ ] external novelty audit
- [ ] determine the sign of the first three-node packet of the real-symmetric sector `(9)`
- [ ] identify `(9)` with the source-defined Poisson refinement joining used by `(AC25)`
- [ ] prove `(AC25)` / RH

## Log

- 2026-07-19 — the centered completed-kernel route was hostile-tested against the known sharp
  three-node orbit obstruction.  Lean strengthened the initial cubic cancellation to an
  all-odd-cardinality singularity theorem and exposed the exact positive survivor: the transverse
  aperture-odd real-symmetric sector `2 Re K_u`.
- 2026-07-19 — targeted module build passed.  `#print axioms` for the kernel swap/reflection laws,
  center and all-aperture even-sector odd-determinant theorems, and the real-symmetric survivor
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
