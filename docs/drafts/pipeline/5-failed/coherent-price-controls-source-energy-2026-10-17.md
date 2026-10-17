# Coherent price cannot control original odd source energy

- **ID:** coherent-price-controls-source-energy
- **Stage:** 5-failed
- **Type:** FALSIFIED (Lean); exact positive survivor and full capstone formalized
- **Source:** ../1-in-progress/hyperbolic-multiplier-lifting-2026-10-17.md
- **Statement tested:** There exists a real scalar c such that
  h_F(0)<=c*C_exact(F) for every actual compact continuous odd source F.

## Exact obstruction

Let d=log2 and A be the actual unit constant-fold source from contribution21.
For B(u)=A(u/2), set W=B-R(B), where R is the annular representative from
contribution22. Its fold is zero. At u=4d the representative is zero, while
B(4d)=A(2d)=1/(2*sinh d) is nonzero. Thus W is a nonzero actual odd source,
C_exact(W)=0 and h_W(0)>0. It contradicts every proposed scalar c.

## Strongest positive survivor

For every actual input f, K(f)=oddCompactSource(f)-R(f) is an actual compact
odd zero-fold source. It is an idempotent projection fixing exactly the odd
zero-fold domain, complementary to R. The exact source coordinates satisfy
odd(f)=R(g)+K(h) iff R(f)=R(g) and K(f)=K(h).

The kernel has zero signed hyperbolic moment, coherent price and cell defect.
For every cutoff N its full plastic functional satisfies
I_opt(K(f),N)+R_plastic(K(f))<=P_plastic(K(f)), hence P_plastic(K(f))>=0.
The explicit family W_a=K(a*B)=a*W has energy a²h_W(0), is nonzero exactly
when a is nonzero, and retains this zero-penalty full functional bound.

## New insight and boundary

The coherent price measures folded data and has a nontrivial kernel among
actual odd sources. The invisible component has constructive plastic
nonnegativity, so it can be isolated without adding an unproved positivity
premise. Original-energy orthogonality, plastic additivity and strict plastic
positivity are not asserted. This obstruction does not rule out energy
control for the annular representative or control after adding a kernel cost.

## Proof status

- [x] Well-posed source-pure scalar-control question.
- [x] Dependency-closed paper obstruction and strongest positive survivor.
- [x] Exact source construction, decomposition and full capstone Lean audit.
- [x] All public theorem axiom audits.

Exact module:
`formal/GaloisForLFunctions/BiScaleUncertainty/CoherentKernelSplitting.lean`.
Key declarations in namespace `CoherentKernelSplitting`: `kernelPart`,
`kernelPart_eq_oddSource_iff`, `decomposition_eq_iff`, `plastic_kernelPart_eq`,
`plastic_kernelPart_bound`, `plastic_kernelPart_nonneg`, `invisibleSource`,
`energy_invisibleSource`, `not_energy_le_coherentPrice`.

Actual-source audit99254 and all25 public theorem axiom audits14114 exited0
without warnings; only `propext`, `Classical.choice`, `Quot.sound`.
Source SHA256 `a66ab901bde6e45677acc2e0e8ab35f1a4e4402fca415863936d64a08c7e0dcf`.
Umbrella wired; all27 public declarations indexed. No full build or numerical
experiment. Global lint reports unrelated modules and concurrent generated
drift; exact snapshot on master card. No global clean-gate or external novelty claim.
