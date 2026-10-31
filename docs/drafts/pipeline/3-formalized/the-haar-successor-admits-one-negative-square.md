# The Haar successor admits one negative square

- **ID:** HAAR-ONE-NEGATIVE-SQUARE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Finite-index Mautner rigidity](../1-in-progress/finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** On `Aff(ℚ)`, `Φ(g) = haarState(g) − 4(log |affSlope g| / log 2)²` is Hermitian, has the exact integer successor, and has negative index exactly one.

## Proof [PROVED HERE]

Write `L(g)=log |affSlope g| / log 2`. Then `L(x⁻¹y)=L(y)−L(x)` and

`−4(L(y)−L(x))² + 4(1+L(x)²)(1+L(y)²) = 4 + 8L(x)L(y) + 4L(x)²L(y)²`.

The right side is the sum of the outer products of `2`, `2L`, `2L`, and `2L²`. The Haar kernel is positive definite, so adding the outer product of `2(1+L²)` makes every Gram form of `Φ` positive. The finite-rank index theorem gives index at most one. At dilation by two, `L=1` and `Re Φ≤−3`, since the normalized Haar state has absolute value at most one. But `Φ(1)=1`, and every normalized positive-definite function has absolute value at most one. Thus the index is nonzero, hence exactly one.

The logarithmic term vanishes on translations. Thus the successor remains Haar, although the state cannot be Hecke-supported by the proved zero-or-infinity law. Its dilation reading is discontinuous at one: adding back the continuous logarithmic square would otherwise make the positive Haar state's dilation reading continuous, contrary to the proved Mautner theorem.

## Scope and audit

Corpus searches found the Hecke-supported zero-or-infinity law, finite-rank index bounds, and positive Mautner rigidity, but no such affine state. The rank-one completion is elementary; the consequence is that Haar translation data alone permit a finite nonzero index. The continuity hypothesis in the parent conjecture remains essential to investigate. This construction does not have Weil's dilation reading and does not resolve O5.

## Lean certificate

[Module](../../../../formal/GaloisForLFunctions/AdelicKreinGeometry/Haar/OneNegativeSquare.lean), namespace `GaloisForLFunctions.AdelicKreinGeometry`:

- `haarOneNegativeSquare_hasIntegerSuccessor`: exact Haar translation reading.
- `haarOneNegativeSquare_completion`: explicit rank-one completion.
- `negIndex_haarOneNegativeSquare`: negative index exactly one.
- `not_isHeckeSupported_haarOneNegativeSquare`: failure of Hecke support.
- `haarOneNegativeSquare_dilation_discontinuous`: no continuous interpolation of the dilation reading at one.

Final audit: `lake --old env lean GaloisForLFunctions/AdelicKreinGeometry/Haar/OneNegativeSquare.lean` passed. All five axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.
