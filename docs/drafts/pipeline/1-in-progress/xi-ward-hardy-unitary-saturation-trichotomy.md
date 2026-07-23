# Xi Ward--Hardy unitary-saturation trichotomy

- **ID:** `xi-ward-hardy-unitary-saturation-trichotomy`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Source:** `GammaSewnMobiusXiWardHardyTransport.lean`,
  `GammaSewnMobiusXiWardHardyContraction.lean`,
  `GammaSewnMobiusXiTrueWienerHopfFactorization.lean`
- **Statement:** The complete Schwarz-paired strict-right Xi Ward phase is contractive
  unconditionally, strictly contractive at every positive node/aperture exactly when RH is false,
  and unitary-saturated exactly when RH holds.

## Goal

Decide whether the new infinite non-diagonal Ward--Hardy contraction can itself supply an RH
proof. The proposed theorem is source-pure and contains no finite-section or diagonal
approximation: it classifies the norm of the actual cofinal canonical-product transport.

If proved, ordinary contractivity is a failed RH mechanism. The exact surviving endpoint is
unitary saturation, not positivity or boundedness:

```text
RH
  <-> ||Xi strict-right normalized Ward phase(w,a)||=1
  <-> Xi anti-causal Ward transport V(w,a)=0
```

for every fixed `Re w>0` and real `a>0`.

## Gates

- [x] 0 → 1 in-progress: exact source object, conjecture, hostile controls, corpus search
- [ ] 1 → 2 fully-proven: dependency-closed paper proof, no RH premise
- [ ] 2 → 3 formalized: direct Lean check, targeted final build, axiom audit
- [ ] 3 → 4 publication-ready: specialist novelty review and standalone theorem

## Conjecture

For `Re w>0` and real `a>0`, put

```text
Phi(w,a)
 = xiRightWardBoundarySourcePhaseCrossRatio (i*w) a
 = product_[strict-right Schwarz pairs q]
     ((w+lambda_q-a)/(w+lambda_q+a))
     ((w+conj(lambda_q)-a)/(w+conj(lambda_q)+a)).
```

Then:

1. `||Phi(w,a)||<=1` unconditionally.
2. `not RH -> ||Phi(w,a)||<1`.
3. `RH -> Phi(w,a)=1`.
4. Hence `RH <-> ||Phi(w,a)||=1`.
5. Since `V(w,a)=1-Phi(w,a)`, `RH <-> V(w,a)=0`.

The quantifiers are pointwise but the object is the complete infinite product; no truncation is
part of the statement.

## Approach

Each right-half-plane Cayley factor has norm strictly below one when `a>0`. Pairing with its
Schwarz conjugate preserves strictness. Under `not RH`, the strict-right divisor is nonempty; the
existing Schwarz-pair equivalence supplies one actual pair. Every cofinal finite product
containing that pair is bounded by its strict norm, so the infinite product is strict. Under RH,
the strict-right divisor is empty and the product is one.

## Hostile controls

- **Infinite-product collapse:** proof must use the existing `HasProd` of the actual canonical
  product and pass a strict bound through the cofinal `Finset` filter.
- **Empty-index cheat:** the forward implication may use emptiness only after deriving it from RH;
  the converse must obtain an actual upper Schwarz pair from `not RH`.
- **Boundary aperture:** strictness requires `a>0`; at `a=0` the phase is always one.
- **Wrong orientation:** contractivity must hold under `not RH`; therefore it cannot be presented
  as RH evidence.
- **Totalized-complement defect:** theorem uses the strict-right factor itself and does not use the
  old nonright quotient.
- **Finite/diagonal retreat:** no finite packet, determinant, diagonal minor, or computation may
  appear in the theorem.

## Predicted frontier change

If theorem survives, `XI-WARD-HARDY-CONTRACTION` is a failed proof class:

```text
contractive  -- unconditional and strictly stronger under not RH
unitary      -- exactly RH
```

Any valid continuation of this lane must prove a source identity forcing unitary saturation.
Another norm bound, positive kernel, or strict contraction moves in the wrong logical direction.

## Novelty status

Generic strictness of a Cayley factor and rigidity of a product of contractions are parent
theory. Internal corpus search found no theorem applying them to the actual infinite
Schwarz-paired strict-right Xi Ward phase or classifying its saturation as RH. External priority
is unverified.

## Log

- 2026-07-23 — Green--Lorentz successor-current idea rejected after collision with existing
  `TransportMomentKreinWeld` and `VonMangoldtSuccessorDiracKreinEdge`.
- 2026-07-23 — strongest new infinite non-diagonal object identified: complete strict-right Xi
  Ward phase already has unconditional contractivity; conjectured exact strict/saturated
  classification above.
