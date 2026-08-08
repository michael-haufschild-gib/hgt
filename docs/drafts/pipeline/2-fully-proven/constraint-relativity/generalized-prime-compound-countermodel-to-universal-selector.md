# Generalized-prime compound countermodel to universal selector

- **ID:** `generalized-prime-compound-countermodel-to-universal-selector`
- **Stage:** 2-fully-proven
- **Type:** COUNTERMODEL / INDEPENDENCE THEOREM (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [META-NO-GO]`
  `[NO RH CLAIM] [NO LEAN WRITTEN]`
- **Role:** proves displayed cyclic, Kummer, reflection, scalar-port, Tor, and controlled-horizon
  identities coexist with nonzero radial drift; their bare conjunction does not select zero.

## Construction

Let index set `I`, free abelian group

\[
 G=\mathbb Z^{(I)},
 \qquad
 A=\mathbb C[G],
 \tag{1}
\]

and choose generalized prime norms `P_i>1`. For `g=(g_i)`, set

\[
 |g|=\prod_iP_i^{g_i},
 \qquad
 \Gamma_c(U_g)=|g|^cU_g,
 \qquad
 U_g^\dagger=U_{-g},
 \tag{2}
\]

with dagger extended conjugate-linearly.

Let `tau` read identity coefficient. For valuation `v_j(g)=g_j`, define

\[
 \partial_j(U_g)=v_j(g)U_g,
 \qquad
 \phi_j(a,b)=\tau(a\partial_jb).
 \tag{3}
\]

For prime/inverse-prime tensor

\[
 u_i=U_{e_i}\otimes U_{-e_i},
 \tag{4}
\]

one has

\[
 \tau^{(1)}(u_i)=1,
 \qquad
 \phi_j(u_i)=-\delta_{ij},
 \qquad
 \Gamma_c^{\otimes2}u_i=u_i.
 \tag{5}
\]

On reciprocal two-leg space define

\[
 T_{i,c}=\begin{pmatrix}P_i^c&0\\0&P_i^{-c}\end{pmatrix},
 \qquad
 J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
 \tag{6}
\]

Then

\[
 T_{i,c}^*JT_{i,c}=J
 \tag{7}
\]

for every real `c`, while scalar physical radial defect

\[
 d_i(c)=1-P_i^{2c}
 \tag{8}
\]

is nonzero for `c!=0`.

On finite-support prime span `W=span{u_i}`, define scalar-port defect

\[
 R_c\!\left(\sum_i a_iu_i\right)
 =\sum_i a_i(1-P_i^{2c}).
 \tag{8a}
\]

For nonempty `I` and `c!=0`, `R_c:W->C` is nonzero and hence has rank one. By contrast, vector
coframe defect `u_i mapsto (1-P_i^(2c))e_i` is diagonal and injective, not rank one.

Finally tensor source system with quadratic observer algebra

\[
 B=\mathbb C[h],
 \qquad
 Q=B[\eta]/(\eta(\eta-h)).
 \tag{9}
\]

## Theorem: organ conjunction does not select zero drift

For every `c!=0`, compound system satisfies simultaneously:

1. graded algebra and total-grade-zero cyclicity;
2. trace-one prime/inverse-prime atoms;
3. complete valuation/Kummer coframe `(5)`;
4. reciprocal reflection and nondegenerate indefinite Stokes form `(7)`;
5. nonzero scalar-port defect of rank one `(8a)`;
6. exact punctured quadratic observer descent;
7. Tor/Bockstein recovery at quadratic collision;
8. controlled inverse-square-root discriminant conditioning.

Therefore no theorem using only bare conjunction of these identities can force `c=0`.

### Proof

Group algebra grading makes `(2)` algebra automorphism and dagger reverses grade. Additivity of
valuations proves `(3)` derivations; coefficient trace proof gives cyclic cocycles. Equations
`(4)`--`(5)` follow from `e_i+(-e_i)=0` and `v_j(-e_i)=-delta_ij`. Direct matrix multiplication
proves `(7)`. Since `P_i>1`, every coefficient in `(8a)` is nonzero for `c!=0`, so `R_c` is
nonzero with one-dimensional codomain and has rank one. Tensoring with independent quadratic
factor preserves all identities. Quadratic
exactness, Tor class, and conditioning are proved in parent law-horizon theorem. QED.

## Independence conclusion

Any successful RH theorem must use literal arithmetic datum absent from countermodel, such as:

- rational-adelic Gaussian/source incidence;
- coefficient-faithful relation-kernel calibrator;
- nonprincipal prime--infinity boundary anomaly;
- source-fixed individual-leg dagger frame;
- literal boundary annihilation before divisor selection.

Abstract positivity, exactness, Tor, scalar-port rank, reflection, valuation coframe, and controlled
singularity cannot replace that datum when asserted only as independent identities. A theorem using
additional coupling among these organs is not addressed by this tensor-product countermodel.

## Nomogenic/SEG consequence

Nonzero obstruction may legitimately execute as successor law; anomaly conservation does not
forbid it. Initiality only selects after execution category is specified and inherits radial
symmetry if category is equivariant. Thus Source Execution Geometry is explanatory unless it
constructs literal source seed and proves boundary identity. Adding axioms to exclude this model
without source provenance risks restating RH.

## Hostile audit

1. This is generalized-prime/model-theoretic countermodel, not counterexample to theorem using
   full rational adeles.
2. Tensor-product independence is deliberate: it proves organ conjunction logically insufficient,
   not that actual source factors.
3. Positive Hilbert unitarity would exclude `c!=0`, but sourcing that positive same-fibre landing
   is missing RH-bearing premise.
4. Complete vector-valued defect is diagonal/injective; only explicitly contracted map `(8a)` is
   rank one.

## Literature boundary

Generalized-prime systems with prescribed analytic behavior provide external falsification class;
compare arXiv:2507.13780. Internal positive Euler-quartet realization supplies off-line symmetric
entire completion within corpus.

## Lean-return note

No Lean work authorized. If later requested, formalize finite-index group-algebra countermodel and
2-by-2 matrix calculation; tensor with existing quadratic law-horizon lemmas only after audit.

## Log

- 2026-08-08 — nine-loop Nomogenesis independence attack; countermodel promoted.
