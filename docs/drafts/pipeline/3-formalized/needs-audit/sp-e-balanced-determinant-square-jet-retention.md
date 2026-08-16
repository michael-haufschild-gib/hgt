# SP-E balanced determinant square-jet retention

- **ID:** SP-E-BALANCED-SQUARE-JET
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM
- **Source:** P-G105P balanced square law + P-G105Q wall Hilbert--Schmidt floor

## Goal

Turn diffuse child energy retained at the aperture wall into an exact, uniformly
nonzero jet of literal channel-complete physical determinants.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and attack identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: closed Lean theorem, target Olean, kernel audit
- [ ] 3 → 4 publication-ready: standalone theorem/proof/certificate

## Corpus audit

Queries run before conjecturing:

- `Fredholm determinant second derivative trace square Hilbert Schmidt child kernel finite section balanced square`
- `determinant I minus u squared H squared quadratic coefficient trace`
- `finite determinant second jet trace square child matrix`
- `Matrix determinant polynomial coefficient trace A`
- `HilbertSchmidt blockMatrix norm tendsto atTop Finset`
- `tsum finite product finset monotone convergence nonnegative`
- `finite block matrix trace square equals sum normSq kernel`

Corpus has exact balanced finite square law, block Hilbert--Schmidt identities,
and general real determinant jets. Search found no theorem identifying the
balanced physical square-coordinate jet with full child energy or retaining it
uniformly at the wall.

## Conjecturing loop

### C4 — cofinal balanced square jet is retained

For finite child block `H_t(d)`, set

```text
Q_{d,t}(v) = det(I - 64 v H_t(d)^2).
```

P-G105P gives physical determinant `F_{d,t}(u)=Q_{d,t}(u^2)`. Hermitianity gives

```text
Q'_{d,t}(0) = -64 tr(H_t(d)^2) = -64 ||H_t(d)||_HS^2.
```

Square blocks exhaust all prime pairs, so

```text
Q'_{d,t}(0) → -64 E(d).
```

P-G105Q gives eventually `E(d) ≥ 4/11025`; hence the cofinal square jet is
eventually at most `-256/11025`, and sufficiently large literal finite blocks
have jet at most `-128/11025`.

Equivalent physical second-order statement:

```text
(F_{d,t}(u)-1)/u^2 → -64 ||H_t(d)||_HS^2  as u → 0, u ≠ 0.
```

This is a determinant-level wall noncollapse certificate. It does not yet
identify the cofinal determinant with Xi.

## Formal theorem

Module:

`GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaPhysicalStokesHellingerBalancedSquareJetRetention`

Main declarations:

- `hasDerivAt_complexDet_one_add_smul`
- `hasDerivAt_squareCoordinatePencil_det_zero`
- `tendsto_squaredChildPencil_det_sub_one_div_sq_zero`
- `tendsto_channelCompleteFiniteDet_sub_one_div_sq_zero`
- `tendsto_childBlockEnergy_atTop`
- `tendsto_finiteSquareJet_atTop`
- `eventually_cofinalSquareJet_le`
- `eventually_eventually_finiteSquareJet_le`

Direct source elaboration and target Olean emission passed. Kernel audit for
physical quotient, cofinal jet, wall floor, and finite-block retention reports
only Lean's standard logical dependencies: `propext`, `Classical.choice`, and
`Quot.sound`.

## Falsification conditions

C4 fails if complex determinant differentiation at the identity, Hermitian
trace/energy identification, punctured square-map transport, or square-block
cofinality fails for the literal physical determinant. If the complex derivative
interface fails, retain the exact polynomial coefficient statement and pivot to
formal power-series coefficients.

## Log

- 2026-08-16 — created after corpus-first audit; C4 selected as direct determinant consequence of P-G105Q.
- 2026-08-16 — C4 proved on paper and in Lean; literal determinant quadratic quotient, cofinal coefficient, and uniform wall/finite-block bounds closed. Umbrella wired; route map left unchanged.
