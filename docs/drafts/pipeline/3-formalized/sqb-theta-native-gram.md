# Complete native theta Gram kernel

The pointwise Gram conjecture is proved for the literal theta dilation family in
`SelbergThetaDilationRows` and `SelbergThetaDilationGram`. Normalized full-Xi
occurrence and RH remain unproved.

For the existing dyadic theta profile g, define

    f_L(y) = exp(log(y)/2) g(log(y)+L),
    Q(L) = complete modular periodization of f_L,
    K(u) = integral conj(g(t)) g(t+u) dt,
    J(v) = integral conj(g(t)) g(v-t) dt,
    H(v) = sum_{c>=1} phi(c)/c * integral
             J(v-2 log(c)-log(1+x^2))/sqrt(1+x^2) dx.

The actual native Hilbert vectors satisfy

    inner(Q(L), Q(M)) = K(M-L) + H(L+M),
    norm(Q(L))^2 = Re(K(0) + H(2L)).

These identities hold for every complex rho and real L, M; no Xi-zero,
occurrence, spectral-location, or convergence premise is added. Every source,
correlation, and reflected row is the literal object, with integrability proved.

## Absolute proof

All real exponential bounds for g give all real power bounds and all weighted
absolute moments for f_L. The existing positive Eisenstein mean bounds then
admit the complete source product in the native measure and its strip unfolding.
Every source belongs to native L2.

Primitive rows are reindexed exactly as one parabolic row plus positive
primitive pairs. For each c, reduced residues and integer translates give

    integral_0^1 Q(M)(x+iy) dx
      = f_M(y) + sum_c phi(c) * integral f_M(y/(c^2(y^2+t^2))) dt.

The complete native pairing is the integral of this mean against
`y^(-2) conj(f_L(y))`. Rescaling the horizontal coordinate by y and setting
y=exp(t) identifies each reflected row with

    exp(-a_c(x)/2) conj(g(t+L)) g(M-t-a_c(x)),
    a_c(x) = 2 log(c)+log(1+x^2).

Its absolute value is bounded by

    C c^(-4) [norm(g(t+L)) exp(-3(t+L)/2)] (1+x^2)^(-2).

Both real factors are integrable. Totient multiplicity leaves a summable
c^(-3) bound. This proves Fubini and the infinite denominator interchange;
the parabolic row gives K and the reflected rows give H. Almost-everywhere
identification with the actual Lp representatives proves the Hilbert formulas.

## Audit

Both source files passed `lake env lean <file>` without output. Named leaf
builds passed; only the two new leaves and the needed
`ThetaCuspHawkingBMHalfRowIntegralInterchange` dependency were built.
Both leaves are wired once into `RHTower.lean`; no umbrella build was run.

All 21 public declarations passed the scratch axiom audit and depend only on
`propext`, `Classical.choice`, and `Quot.sound`. There are no added axioms,
holes, or computational certificates. The corpus index was regenerated and
`scripts/formal_tools.py lint` passed, with existing repository warnings.

Audit logs: `/tmp/sqb35_source_check.log`, `/tmp/sqb35_leaf_build.log`,
`/tmp/sqb35_gram_source_check.log`, `/tmp/sqb35_gram_leaf_build.log`,
`/tmp/sqb35_axioms.log`, `/tmp/sqb35_index.log`, `/tmp/sqb35_lint.log`.

## Remaining mathematical target

The integrated packet formula and its differential residual are still paper
statements. The required positive construction is a source-derived family w_R
with G(w_R)>0 and G(w_R''-kappa^2 w_R)/G(w_R) tending to zero at the unchanged
full Xi target. The pointwise Gram theorem supplies the complete norm kernel;
it does not supply that family or its residual estimate. Gaussian leading-term
cancellation, the transform's continued mean value, and a separate nonzero
source are not substituted for this estimate.

The frontier map and route-independent STATUS ledger were left unchanged.
No numerical computations, exclusion modules, commits, or pushes were made.
