# Common theta forcing in the native graph

The reflected causal source conjecture and its native graph realization are proved.
Normalized full-Xi occurrence and RH remain unproved.

For an actual Xi divisor copy q, put z=xiSpectralPoint(q), with reflected copy q*
whose spectral point is -z. Write u and v for their original causal modes, and Phi
for the complete theta source. The source-defined pair is

    p_q(x)=-(u(x)-v(x))/(2z),
    p_q''+z^2 p_q=Phi.

Its literal height seed and full modular periodization are

    f_q(y)=exp(log(y)/2) p_q(log(y)/2),
    W_q=-(modeSource(q)-modeSource(q*))/(2z).

The actual native Hilbert vector W_q is nonzero, belongs to the original closed
operator domain, and satisfies

    (A-e_q) W_q=-P/4,             e_q=(5+z^2)/4,

where P is the complete positive theta periodization, independent of q. The exact
entire target identity is F(e_q-1)=xiEntireTarget(q), with no replacement of the
zero's real part. The native mean is sourceMass/(1+z^2).

True orthogonal centering against the native constant vector gives an admitted
graph vector U_q=centered(W_q) with

    integral U_q=0,
    (A-e_q) U_q=-(1/4) centered(P).

Nonvanishing here is proved for W_q. Nonvanishing of U_q and a vanishing normalized
full residual are not inferred from this equation.

## Graph proof

The source supplies fixed constants C_q,D_q with

    |f_q(y)| <= C_q positiveProfile(y),
    |y f_q'(y)| <= D_q positiveProfile(y).

For H_n=n+3, subtract the shrinking smooth cutoff at 1/H_n from the expanding
cutoff at H_n. The resulting chi_n is bounded by one and supported in
[1/H_n,2H_n]. At every fixed positive height it is eventually locally one.
Every Euler derivative y^j chi_n^(j) has a bound independent of n.

The compact planar seed cuspWindow(x) chi_n(y) f_q(y) supplies an actual native
domain vector. The entire integer translation row cancels cuspWindow'' at every
horizontal coordinate. Every primitive height row remains, without a restriction
to the high cusp. Its exact height residual is

    -chi_n positiveProfile/4
    -2 (y chi_n') (y f_q') - (y^2 chi_n'') f_q.

All compact values and complete operator images have a single positive theta
majorant. Row dominated convergence and then native L2 dominated convergence give
two independently proved graph limits. Applying the continuous native covariance
to the operator-image limit identifies W_q in the original closed domain.
Centering uses the actual constant-domain vector A1=1 and the exact source mean.

## Lean files and audit

- SelbergThetaCommonForcing.lean: literal reflected pair, height equation,
  native admission and mean, nonvanishing, source majorants, unchanged Xi target.
- ThetaCuspHawkingBMPositiveHeightOperator.lean: constructed compact positive-height
  graph vectors and their complete primitive-row differential image.
- SelbergThetaCommonForcingGraph.lean: both-ended compact approximants, both native
  norm limits, original closed operator equation, nonzero native source, and exact
  true-centering equation.

All three source checks passed with no output. All three named leaf builds passed,
rebuilding only the named new leaf each time. All three are wired once into
RHTower.lean; no full or umbrella build was run.

All 73 public declarations passed the scratch axiom audit, depending only on
propext, Classical.choice, and Quot.sound. The corpus index was regenerated.
`scripts/formal_tools.py lint` passed with existing repository warnings.

Audit logs use the prefix /tmp/sqb36_: source_check.log, leaf_build.log,
positive_source_check.log, positive_build.log, graph_source_check.log,
graph_build.log, axioms.log, index.log, and lint.log.

No numerical computation, computational certificate, exclusion module, added
axiom, commit, or push was used. The frontier map and universal STATUS ledger
were left untouched. The remaining objective is a concrete source-derived family
with nonzero native norm and vanishing normalized residual at the full Xi target.
