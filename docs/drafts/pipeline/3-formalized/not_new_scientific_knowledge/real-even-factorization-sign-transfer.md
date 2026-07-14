# Real even-factorization sign transfer

- **ID:** `real-even-factorization-sign-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/RealEvenFactorizationSignTransfer.lean`

## Statement

Suppose a real function on \([a,b]\) has a finite factorization

\[
 f(x)=\prod_{z\in Z}(x-z)^{m_z}u(x),
\]

where (Z\subset[a,b)), every (m_z) is even, and (u) is continuous and nowhere zero.
If (f(b)>0), then (f(a)\ge0).  The left endpoint may itself be a root.

## Formal declarations

- `HTGeometry.RealEvenFactorizationOn`;
- `HTGeometry.continuousOn_nonzero_endpoint_product_pos`;
- `HTGeometry.nonneg_left_of_realEvenFactorizationOn_of_right_pos`.

## Role

The theorem separates a generic sign-transport fact from source mathematics.  Its first RHTower
consumer is the moving completed prime--Gamma polynomial parity route, where allowing a zero at
the center removes the former independent central-nonvanishing hypothesis.

## Gates

- [x] imported by the HTGeometry umbrella
- [x] no placeholders or project axioms
