# Möbius--Liouville square dilation preserves the Mellin continuation wall

- **ID:** `mobius-liouville-square-dilation-wall-preservation`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** Möbius--Laplace continuation wall; square-dilation carrier
- **Statement:** Multiplication by the Liouville square-dilation factor `zeta(2s)` is an analytic
  unit on `Re s > 1/2`, so the Liouville-twisted Mellin wall is equivalent to the original
  Möbius wall and hence to RH.

## Goal

Audit the last plausible conditional square-dilation escape from the critical Lambert equation.
The Möbius and Liouville coefficients obey the classical square-divisor relations

```text
lambda = 1_square * mu,       mu = mu_square * lambda,
```

so their Dirichlet/Mellin channels differ by `zeta(2s)`.  Determine whether conditional
cancellation in the inverse square kernel can continue the Möbius transform across its wall.

## Gates

- [x] 0 -> 1: exact square-dilation multiplier and target half-plane identified
- [x] 1 -> 2: dependency-closed paper proof and hostile classification
- [x] 2 -> 3: Lean unit-twist theorem and Liouville specialization
- [ ] 3 -> 4: ineligible; classical analytic-unit mechanism

## Exact theorem

Let

```text
W_mu := exists G analytic on H,
          G(s) zetaResidueUnit(s) = Gamma(s)(s-1),

W_U  := exists H analytic on H,
          H(s) zetaResidueUnit(s) = Gamma(s)(s-1)U(s),

H := {s : C | Re(s) > 1/2}.
```

If `U` is analytic and nowhere zero on `H`, then

```text
W_U <-> W_mu.                                                (SD1)
```

Indeed, a witness `G` for `W_mu` gives `G*U` for `W_U`.  Conversely a witness `H` for
`W_U` gives `H/U` for `W_mu`; division is analytic because `U` is nowhere zero, and the defining
identity cancels `U` pointwise.

Take `U(s)=zeta(2s)`.  If `Re(s)>1/2`, then `Re(2s)>1`, so `zeta(2s)` is analytic and nonzero.
Therefore

```text
W_lambda <-> W_mu <-> RH.                                   (SD2)
```

The same conclusion holds for every square-dilation convolution whose Mellin multiplier is an
analytic unit on `H`.

## Boundary audit

At `Re(s)=1/2`, the forward square kernel has harmonic weight `sum d^(-1)` and is not absolutely
summable.  The inverse kernel has weight `sum mu(d)/d`, whose conditional cancellation is a
prime-number-theorem boundary phenomenon.  Neither fact changes (SD1): on the open continuation
domain the multiplier is already invertible, so it cannot remove or move any right-half pole.

## No-go closure

- **Exact killing theorem/mechanism:** analytic-unit invariance (SD1); `zeta(2s)` is a unit on the
  entire target half-plane.
- **Strongest positive survivor:** a generic classification for every analytic nowhere-zero
  multiplier, specialized to the exact Möbius--Liouville square-dilation channel.
- **New insight:** conditional square-kernel cancellation can affect boundary representations but
  cannot improve open-half-plane continuation.  Any surviving transform must introduce a factor
  with a genuine zero/pole divisor inside `Re(s)>1/2`, or add information not obtainable by
  invertible dilation.
- **Status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [PROVED HERE]`.  Classical Dirichlet
  convolution and elementary complex analysis absorb the mechanism.  Exact wall classification
  is new to this corpus, not claimed new to literature.

## Literature boundary

- The identities `sum lambda(n)n^(-s)=zeta(2s)/zeta(s)` and
  `sum mu(n)n^(-s)=1/zeta(s)` are classical Euler-product consequences.
- Liflandsky's 2026 discrete-Laplace criterion isolates the same Möbius continuation wall but does
  not supply an unconditional half-power source.
- Existing corpus modules `SquarefreeMoebiusNormalization.lean`, `MFreeLadder.lean`, and
  `MFreeTwinNoGo.lean` already formalize square-dilated Möbius carriers and right-half divisor
  localization; none states (SD1)--(SD2) for the Mellin-wall interface.

## Open core

`[OPEN CORE]` Prove a source estimate before applying any invertible Mellin multiplier.  Neither
Liouville square dilation nor any holomorphic-unit twist reduces the RH-level continuation task.

## Formal verification

Module:

```text
formal/GaloisForLFunctions/RHTower/MobiusLiouvilleSquareDilationWall.lean
```

Principal declarations:

- `MobiusLaplaceUnitTwistedMellinContinuationWall`;
- `mobiusLaplaceUnitTwistedMellinContinuationWall_iff`;
- `mobiusLiouvilleSquareDilationUnit_analyticOnNhd`;
- `mobiusLiouvilleSquareDilationUnit_ne_zero`;
- `mobiusLiouvilleSquareDilationMellinContinuationWall_iff_mobius`;
- `mobiusLiouvilleSquareDilationMellinContinuationWall_iff_riemannHypothesis`.

Direct source verification passes with `lake env lean`.  `#print axioms` for the generic unit
classification and RH equivalence reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-22 -- derived exact unit-twist classification after hostile audit of conditional
  square-dilation inversion.
