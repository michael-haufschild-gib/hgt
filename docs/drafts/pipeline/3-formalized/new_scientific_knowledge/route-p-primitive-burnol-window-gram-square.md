# Route P primitive Burnol window Gram square

- **ID:** `route-p-primitive-burnol-window-gram-square`
- **Stage:** 3-formalized
- **Label:** `P-G186`
- **Source:** P-G181, P-G184, Burnol nested-window conormal tomography
- **Statement:** The complete P-G181 primitive base Cauchy matrix is exactly the aperture Gram of
  coefficient-weighted inverse Burnol window features placed at canonical Euler spectral nodes.
  This holds entrywise for arbitrary finite primitive packets and arbitrary ordinate clocks, not
  only on the diagonal.

## Conjecture, proof, and surviving seam

P-G184 identified only the trace diagonal with the cubically regularized balanced Euler
source/co-source codiagonal. Burnol tomography independently identified the same radial feature at
actual completed-Xi divisor support. The live question was whether these were merely two scalar
charge formulas or faces of one source-defined Hilbert-space square.

For a primitive cell `pe=(p,e)`, put

```text
lambda_pe = (e+1) log p,
z_pe(kappa) = 1/2 + lambda_pe + i kappa,
A_pe = sqrt(Lambda(p^(e+1)) / p^(e+1)).
```

Let `W_L(z)` be the inverse centered Burnol window after one conormal clock. Define

```text
F_(pe,kappa)(L) = A_pe W_L(z_pe(kappa)),   L>0.             (1)
```

Burnol incidence gives `W_L(z)=L exp(-(z-1/2)L)`. Therefore the off-diagonal aperture pairing is

```text
integral_0^infinity conjugate(F_(pe,kappa)(L)) F_(qf,nu)(L) dL
 = A_pe * 2/[lambda_pe+lambda_qf+i(nu-kappa)]^3 * conjugate(A_qf).  (2)
```

The right side of `(2)` is entrywise the primitive base Cauchy cube. Hence the complete matrices
agree. Existing source theorems then yield, without a zero expansion:

- positive semidefiniteness for arbitrary packets and ordinate clocks;
- exact equality of its trace with every balanced-reflection Euler codiagonal;
- the same uniform global trace budget `<2` for injective packets.

This closes construction of the source-to-window square. It does **not** identify its canonical
Euler nodes with Xi divisor nodes and does not imply the RH-equivalent target capacity law. The
remaining theorem is a completed boundary-value restriction/closed-graph comparison transporting
this universal Burnol Gram from the Euler spectral nodes to actual completed-Xi divisor support.

## New route knowledge

P-G181's base cube is a universal Burnol aperture reproducing kernel, not an arithmetic matrix
that must later be embedded into an unrelated target Hilbert space. Prime-depth arithmetic enters
only through canonical node positions and positive von Mangoldt amplitudes. Target residues use
the same feature functor at different nodes.

This changes the obstruction's type. No new Hilbert space, positivity proof, trace estimate, or
source window is missing. What remains is exclusively a restriction theorem between two node
sets at the sharp P-G185 boundary. Any proposed bridge must therefore expose an actual completed
Gamma--Euler boundary-value map; a bare kernel equality or abstract contraction would repeat an
already closed layer or assume the RH-equivalent capacity law.

## Novelty and theatre audit

Internal search found the generic completed-Xi residue Gram and the scalar Burnol self-charge, but
no theorem placing resolved von Mangoldt amplitudes at canonical primitive Euler nodes and proving
the full off-diagonal Burnol Gram equals the P-G181 source matrix. P-G186 is stronger than the
P-G184 trace identity because it retains every ordinate interaction.

Primary-source audit found Burnol's co-Poisson/Sonine realization of zeta zeros and
Connes--Consani's operator-theoretic analysis of the scaling Hamiltonian and Weil-positivity
obstruction, but not `(1)`--`(2)` with primitive Euler nodes and resolved von Mangoldt amplitudes:
[Burnol](https://arxiv.org/abs/math/0203120) and
[Connes--Consani](https://arxiv.org/abs/1910.14368). No external priority claim is made beyond the
exact Route P identity proved here.

No RH conclusion is claimed. P-G186 closes one previously named producer and explicitly leaves
the boundary restriction open; it does not turn a target capacity assumption into a source
theorem.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolWindowGramSquare.lean
```

Capstones:

- `integral_star_routePPrimitiveBurnolWindowFeature_mul`;
- `routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy`;
- `routePPrimitiveBurnolWindowGramMatrix_posSemidef`;
- `trace_routePPrimitiveBurnolWindowGramMatrix_eq_balanced_source`;
- `re_trace_routePPrimitiveBurnolWindowGramMatrix_le_budget`.

Verification:

- `/tmp/pg186.lean`: `lake env lean /tmp/pg186.lean` passed;
- exact leaf build passed;
- `/tmp/pg186_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan: clean;
- umbrella import wired; umbrella not built.

## Gates

- [x] paper proof dependency-closed
- [x] exact unconditional Lean formalization
- [x] full off-diagonal identity, not only trace/diagonal
- [x] scratch verification
- [x] exact leaf build
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] completed boundary-value restriction from Euler nodes to Xi divisor nodes
- [ ] raw conormal trace landing and RH
