# Source-frame modular holonomy law

- **ID:** ULF-SFMH-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor nonabelian formation law
- **Parents:** ULF-MCPT-001, ULF-PBFMS-001, ULF-FBG-002
- **Status:** [PAPER-PROVED] [LEAN-PROVED] [NOT RH]
- **Lean:** formal/GaloisForLFunctions/HTGeometry/SourceFrameModularHolonomy.lean;
  formal/GaloisForLFunctions/RHTower/PrimeBurnolSourceFrameCubicHolonomy.lean

## 1. Big-picture meaning

Completion does not merely compress source data. It changes source coordinates by a moving frame.
If `C` is literal source density and `U` is completion frame, their mismatch is the multiplicative
commutator

~~~text
H_C(U)=C^(-1) U C U^(-1).                                      (SFMH.1)
~~~

This object is formed before any divisor. It is neither a regularized operator, quadratic
cross-prime functional, positivity certificate, nor phase choice. It is the exact obstruction to
naturality of source modular transport under completion framing. Its cubic projection
transgression is therefore a deformation of the completion extension class, rather than another
representative inside a fixed tracial class.

The corpus interpretation becomes precise: source density supplies modular time; theta supplies
moving coordinates; horizontal anomaly can only be a cofinal boundary of their noncommutation.

## 2. Exact nonabelian laws

Let `A` be any ring, `C,U,V` units of `A`, and

~~~text
sigma_C(x)=C^(-1)xC,      Ad_U(x)=UxU^(-1).
~~~

Then direct multiplication gives the cocycle law

~~~text
H_C(UV)=H_C(U) U H_C(V) U^(-1).                         (SFMH.2)
~~~

Frame reversal gives

~~~text
H_C(U^(-1))=U^(-1) H_C(U)^(-1) U.                       (SFMH.3)
~~~

The holonomy is trivial exactly in the source centralizer:

~~~text
H_C(U)=1  iff  CU=UC.                                    (SFMH.4)
~~~

Most importantly, modular transport and completion framing obey exact equivariance

~~~text
sigma_C(Ad_U(x))
  =Ad_(H_C(U))(Ad_U(sigma_C(x))).                         (SFMH.5)
~~~

No invariant-subspace or centralizer premise is needed for (SFMH.5). Thus `H_C(U)` is the complete
failure-of-naturality datum, not an analogy.

## 3. Cubic deformation

For an idempotent neutral polarization `P`, define

~~~text
Q=Ad_U(P),
R=sigma_C(Q),
D3(C,U;P)=(R-P)^3-(R-Q)^3-(Q-P)^3.                      (SFMH.6)
~~~

The three entries remain idempotent. For every `sigma_C`-trace `tau`, ULF-MCPT-001 applies to the
same triple and gives

~~~text
tau(D3(C,U;P))=tau(M3_(sigma_C)(R,Q,P)),                 (SFMH.7)
~~~

where `M3` is the exact five-channel modular anomaly from MCPT. If `C` commutes with `U` and fixes
`P`, then (SFMH.4)--(SFMH.5) give `R=Q`, hence

~~~text
D3(C,U;P)=0.                                             (SFMH.8)
~~~

Therefore a central, diagonal, or prime-separable completion frame cannot be the producer. The
first surviving datum is the odd cubic transgression of noncentral source-frame holonomy.

## 4. Literal Euler specialization

For every injectively labelled finite primitive packet `F`, ULF-PBFMS-001 proves that its complete
Burnol Gram `C_F` is invertible. The Lean specialization defines its canonical unit directly from
that theorem and then forms

~~~text
H_F(U)=C_F^(-1) U C_F U^(-1).                            (SFMH.9)
~~~

The unit coerces definitionally back to the complete literal Gram. No diagonalization,
pseudoinverse, normalization, zero, or Xi datum enters. All laws (SFMH.2)--(SFMH.7) specialize to
`H_F`, retaining every off-diagonal prime/depth coefficient.

## 5. Finite blindness and forced cofinality

For finite matrices over any commutative ring,

~~~text
det H_C(U)=1.                                            (SFMH.10)
~~~

Thus finite determinant, scalar phase, and ordinary finite `K1` cannot detect the mismatch. This
is a theorem, not a warning. Any integer produced by this mechanism must arise as a relative
boundary of the cofinal family `H_F(U_F)`, where failure of ordinary compact convergence can
survive finite commutator triviality.

This matches existing corpus constraints: raw nested projections are diamond-flat, exact Schur
elimination is transitive, ordinary cubic trace vanishes, and the unframed positive nuclear loop
is null-homotopic. The source-framed cofinal boundary is the remaining category not killed by
those results.

## 6. What remains open and how it would close RH

Construct the actual theta/Poisson frames `U_F(a)` on the same literal Burnol packets and prove
that the cofinal holonomy has a relative cubic boundary satisfying one same-representative law

~~~text
boundary_3([H_F(U_F)])=[T_D],
Tr(T_D)=tau_src(Ch3(H_F(U_F))),
|tau_src(Ch3(H_F(U_F)))| <= B_base < 1.                 (SFMH.11)
~~~

The first equality produces the integral Xi escape multiplicity; the second prevents comparing
unrelated objects; the third supplies the literal Euler sub-unit bound. Then the escape integer is
zero on every strict-right rectangle, reflection removes strict-left escape, and existing Xi
support gives RH.

ULF-SFMH-001 proves formation, cocycle, reversal, centralizer exclusion, source specialization,
and finite determinant blindness. It does not prove cofinal existence or (SFMH.11).
