# Exact kinetic rank cancellation and the displacement-coefficient obstruction

- **ID:** TT-C78-KINETIC-LEADING
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Route TT; `ThetaCuspRatioIntegerJets`, `ThetaCuspRatioIntegerReflections`, `ThetaCuspRatioSquareSlope`, `ThetaCuspRatioSquareSlopeFactor`; working card `../1-in-progress/tt-third-slope-nonlinear-cone.md`.
- **Statement:** The complete reduced third slope has kinetic degree 17 with a positive leading coefficient for positive squared drift and physical clock. Every expansion in downward kinetic displacement consequently has a negative degree-17 coefficient.

## Goal

Test the proposed all-nonnegative displacement power-coefficient certificate for C78 using the complete source recurrence. This is a certificate obstruction, not a counterexample to positivity on the finite physical interval, not a point on the actual modular orbit, and not an RH falsification.

## Gates

- [x] 0 → 1: source recurrence and exact reflection/determinant definitions inspected.
- [x] 1 → 2: dependency-closed paper proof below, [PROVED HERE].
- [ ] 2 → 3: exact source coefficient theorems, obstruction, and strongest positive survivor pass direct `lake --old env lean` audits; standard foundational axioms only; production and umbrella integration complete.
- [ ] 3 → 4: standalone publication audit.

Lean proof preparation has started in sixteen scratch modules, in audit order: `/tmp/TTC78KineticCommutator.lean`, `/tmp/TTC78KineticJetHeads.lean`, `/tmp/TTC78KineticPolynomial.lean`, `/tmp/TTC78KineticReverse.lean`, `/tmp/TTC78KineticBinomialHeads.lean`, `/tmp/TTC78KineticReflectionHeads.lean`, `/tmp/TTC78KineticNormalizedReflections.lean`, `/tmp/TTC78KineticMinorDecomposition.lean`, `/tmp/TTC78KineticMinorLeading.lean`, `/tmp/TTC78KineticSourceDerivatives.lean`, `/tmp/TTC78KineticSlopeCommutator.lean`, `/tmp/TTC78KineticSlopeLeading.lean`, `/tmp/TTC78KineticSquareTransfer.lean`, `/tmp/TTC78KineticDisplacement.lean`, `/tmp/TTC78KineticDisplacementSign.lean`, and `/tmp/TTC78KineticResidualSignature.lean`. None has been compiled. The sole live C77 pipeline retains priority. Do not retire this no-go before the exact survivor is formalized. No degree bound by itself is counted as the intended frontier result: the target is the sign obstruction and exact source rank structure.

## Exact source definitions

Use original integer source coordinates `(u,k,j)`, and put `y=3k+1`, `lambda=12`. Let `P_n` be `integerJet n`. The audited recurrence is

    P_0 = 6k-1 = 2y-3,
    P_(n+1) = D_source P_n + u*(1-12k)*P_n,

    D_source = 6k*(9-u^2)*partial_u
      + (12k+4)*j*partial_k
      + [6k^2*(9-u^2)-36k-24+(12k+8)*u*j]*partial_j.

Let `R_n=integerReflection n`, so

    R_n = sum_(i=0)^n choose(n,i)*(-1)^(n-i)*P_i*P_(n-i).

The actual integer third minor is minus the determinant of the matrix
`[R_(2i+2ell+2)]_(0<=i,ell<=2)`, since every determinant term has total signed-moment index nine. All source derivatives below are taken before shearing or substituting a boundary.

## Paper proof [PROVED HERE]

### 1. All-order top two jet coefficients

The recurrence raises degree in `j` by at most one, so `deg_j P_n<=n`. Write `a_n=[j^n]P_n` and, for n>=1, `b_n=[j^(n-1)]P_n`. The only degree-raising part of D_source is

    L = (12k+4)*partial_k = 12y*partial_y.

Thus `a_0=2y-3` and `a_(n+1)=L a_n`. It follows that

    a_n=2*12^n*y             (n>=1).

Because a_n is independent of u, the next coefficient satisfies, for n>=1,

    b_(n+1) = L b_n + u*[4n*(y+1)+5-4y]*a_n,
    b_1 = u*(-8y^2+22y-15).

Consequently

    b_n = u*12^(n-1)*[-8n*y^2+(4n^2+6n+12)*y-15*delta_(n,1)]
                                                        (n>=1).

For completeness, substitution reduces the induction to the coefficient recurrences

    B_(n+1)=2B_n+8(n-1),   B_n=-8n,
    C_(n+1)=C_n+8n+10,     C_n=4n^2+6n+12.

The exceptional constant in b_1 is killed by L at the next step. The non-j term of D_source(j) lowers kinetic degree and cannot contribute to b_(n+1); it remains in the full polynomial and is not discarded from any later sign claim.

### 2. All-order reflected coefficients and the exceptional first moment

For every even n>=2,

    [j^n]R_n = -12^(n+1)*y.

Indeed, replace a_i temporarily by `2*12^i*y` also at i=0. The alternating binomial sum of the resulting constant coefficient is zero. Restoring `a_0=2y-3` changes each endpoint by `-3*(2*12^n*y)`, giving the formula.

For even n>=4,

    [j^(n-1)]R_n
      = u*12^(n-1)*[48(n-1)*y^2-24(n^2-n+3)*y].

At n=2 this coefficient is instead

    [j]R_2 = u*(960*y^2-1440*y).

Here is the full binomial accounting. By symmetry the next coefficient is twice the sum of `choose(n,j)*(-1)^j*b_j*a_(n-j)`. Factor out `u*12^(n-1)` and use the quadratic expression

    p(j)=-8j*y^2+(4j^2+6j+12)*y.

The unrestricted sum of `2y*p(j)` is zero for n>=4. The missing j=0 term contributes `-24y^2`; the exceptional b_1 contributes `30n*y`; restoring a_0 at j=n contributes `24n*y^2-(12n^2+18n+36)*y`. Multiply their sum by two. For n=2 the unrestricted quadratic binomial sum contributes an additional `16y^2` before multiplication by two. These formulas therefore retain both exceptional endpoints.

### 3. Exact rank cancellation in the third minor

First, the normalized description makes the rank structure transparent. Write epsilon=1/j as a formal Laurent variable. Every entry of the reflection matrix has its leading factors

    R_(2i+2ell+2) = -12*y*(12*j)^(2i+2ell+2)
                     *[1+epsilon*B_(i,ell)+O(epsilon^2)].

Here i,ell are matrix indices and j remains the kinetic variable. The normalized next coefficient is

    B_(i,ell) = (u/6)*[n^2-n+3-2(n-1)y]
                  -(2/9)*u*y*delta_(i,0)*delta_(ell,0),
    n=2i+2ell+2.

The leading matrix is all ones, of rank one. Hence determinant coefficients of kinetic degrees 18 and 17 vanish. At the next order, subtract row zero from rows one and two, then column zero from columns one and two. The remaining 2 by 2 matrix is

    E_(a,b)=B_(a,b)-B_(a,0)-B_(0,b)+B_(0,0)
           =u*[(4/3)*a*b-(2/9)*y],        a,b in {1,2}.

Its determinant is exactly

    det E = -(8/27)*u^2*y.

Terms hidden in `O(epsilon^2)` cannot affect this coefficient: the two differenced rows already contribute one epsilon each. Thus the first nonzero determinant coefficient is determined by the complete top two source coefficients, with no unproved remainder assumption.

Restoring the factored row/column scalars gives the determinant prefactor `-12^21*y^3*j^18`. Reversing the determinant sign for `integerThirdMinor` yields

    deg_j integerThirdMinor <= 16,
    [j^16]integerThirdMinor = -D*u^2*y^4,
    D=(8/27)*12^21 > 0.

The following polynomial argument proves the same identity without dividing by y. For every n, reverse the complete kinetic polynomial about its proved degree bound n and divide only by the nonzero constant `12^n`:

    Q_n(epsilon)=12^(-n)*epsilon^n*R_n(1/epsilon).

For the five even indices in the actual third minor, its constant coefficient is `c=-12y`, and its linear coefficient is

    F_n=u*[4(n-1)y^2-2(n^2-n+3)y]+(8/3)*u*y^2*delta_(n,2).

In the matrix `Q_(2i+2ell+2)`, subtract row zero from rows one and two, then column zero from columns one and two. The two differenced rows have zero constant coefficients; both entries of row zero in the differenced columns also have zero constant coefficients. Thus, in the determinant's epsilon-squared coefficient, only the constant at position (0,0) and the linear coefficients of the bottom-right two by two block can contribute. The latter are

    F'_(a,b)=-16*u*y*a*b+(8/3)*u*y^2,       a,b in {1,2}.

Their determinant is `-(128/3)*u^2*y^3`, so the epsilon-squared coefficient of the reversed determinant is

    (-12y)*[-(128/3)*u^2*y^3]=512*u^2*y^4.

The residual entry identity holds for every positive pair of row indices a,b, not only a,b in {1,2}. This yields a stronger exact survivor [PROVED HERE]. For arbitrary finite index sets and arbitrary scalar weights A and B, put `m0(A)=sum_a A_a` and `m1(A)=sum_a a*A_a`. Then

    sum_(a,b) A_a*B_b*F'_(a,b)
      =(8/3)*u*y^2*m0(A)*m0(B)-16*u*y*m1(A)*m1(B).

Proof: substitute the displayed literal source entry `F'_(a,b)` and distribute both finite sums. There are no other channels in this coefficient. In particular every weight vector with both index moments zero is in its radical. On the first two indices its quadratic form is exactly

    Q(x,z)=(8/3)*u*y^2*(x+z)^2-16*u*y*(x+2z)^2.

The directions `(1,-1)` and `(2,-1)` give `-16*u*y` and `(8/3)*u*y^2`, respectively. For real u!=0 and y>0 they have opposite strict signs, with their roles exchanged when u<0. This proves indefiniteness directly on the actual source residual, while retaining the two-moment formula at every finite size. It does not claim that the complete source matrices or their finite-interval remainders have this signature. The new source theorem and explicit directions have prepared, unaudited Lean proofs.

Every determinant term has the same sum of source indices, eighteen. Undoing the reversal and the constant factors, and retaining the actual minus sign in `integerThirdMinor`, gives

    [j^16]integerThirdMinor=-512*12^18*u^2*y^4,
    512*12^18=(8/27)*12^21=D.

No division by u or y, fraction-field embedding, asymptotic remainder assumption, or nonzero specialization premise is needed. The identities hold also at u=0 or y=0. When u and y are nonzero the displayed coefficient is nonzero and the degree is exactly sixteen. For real u!=0 and y>0, E is indefinite, since its determinant is strictly negative. The exceptional first reflection is essential to this two-direction structure.

The same argument retains an exact remainder, useful for subsequent full-source sign work. Define the symmetric Hankel cubic and its rank-one residual by

    H(a,b,c,d,e)=a*c*e-a*d^2-b^2*e+2*b*c*d-c^3,
    M(a,b,c,d,e)=(c-2*b+a)*(e-2*c+a)-(d-b-c+a)^2.

For arbitrary elements of a commutative ring, determinant multilinearity gives

    H(q+x*a,q+x*b,q+x*c,q+x*d,q+x*e)
      =x^2*q*M(a,b,c,d,e)+x^3*H(a,b,c,d,e).

The constant and linear terms vanish because their determinant expansions contain at least two equal constant rows. The quadratic term is the displayed row/column-difference minor, and the cubic term is H itself. This proves the identity without a remainder estimate. In the actual reversed source, each `Q_(2r)-(-12y)` is divisible by epsilon. Its quotient is a complete polynomial, so this identity separates the full reversed source determinant into an exact quadratic residual and an exact cubic remainder. Their signs on the physical interval remain open; the decomposition does not discard the latter term or assert its sign.

### 4. Full source slope and downward displacement

The audited source slope is

    integerThirdSlope = (2y-3)*D_source(integerThirdMinor)
                         -6*integerThirdMinor*D_source(2y-3).

An exact all-order identity avoids transporting the k and u derivatives coefficient by coefficient. Put `partial=partial_j` and

    C(P)=(12k+4)*partial_k P+(12k+8)*u*partial_j P,
    S(P)=(2y-3)*D_source P-144y*j*P.

The literal field gives `[partial,D_source]=C` and `[partial,C]=0`. Both y and the seed are independent of j, while `D_source(2y-3)=24y*j`. Hence, for every n>=0 and every complete source polynomial P,

    partial^(n+1) S(P)
      =(2y-3)*[D_source(partial^(n+1)P)+(n+1)*C(partial^n P)]
        -144y*[j*partial^(n+1)P+(n+1)*partial^n P].

This follows by induction from the two commutators and the Leibniz identity for multiplication by j. It retains the entire source operator. Applying it at n=16 and n=17 to the exact minor, whose degree-sixteen coefficient was obtained above, gives both the leading slope derivative and the vanishing derivative above degree seventeen. This bridge now has prepared, unaudited Lean source; it adds no unknown coefficient or sign hypothesis.

Only L followed by multiplication by kinetic j can raise degree to seventeen. For `C=-D*u^2*y^4`, one has `L C=48C` and `D_source(2y-3)=24y*j`. Therefore

    [j^17]integerThirdSlope = [(2y-3)*48-144y]*C
                            =48D*u^2*y^4*(y+3).

Its kinetic degree is at most seventeen. The already-proved shear/square identity is

    u*integerThirdSlope(u,k,u*z)=slope(u^2,k,z).

Writing v=u^2 and using the exact polynomial factor `slope=v*reducedSlope` gives

    deg_z reducedSlope <= 17,
    [z^17]reducedSlope(v,k,z)
       =48D*v^9*(3k+1)^4*(3k+4).

Coefficient comparison and cancellation take place in the generic polynomial ring; the result holds also at v=0, where the displayed coefficient vanishes. For v>0 and k>5/4 it is strictly positive, so the degree is exactly seventeen.

The prepared Lean transfer uses the existing stronger factorization `shear integerThirdSlope = u*square reducedSlope`. The maps obey `partial_j(shear P)=u*shear(partial_j P)` and `partial_j(square P)=square(partial_j P)`. Thus the n-th native derivative transfers with the exact factor u^n. The square homomorphism is injective: evaluate at an arbitrary complex assignment after choosing a square root of its u-coordinate. Cancellation of the nonzero polynomial X_U, rather than a nonzero evaluated coordinate, transfers the seventeenth derivative and the vanishing eighteenth derivative. This introduces no specialization premise and retains the seam v=0.

For every real center z0, replacing z by z0-d consequently gives

    [d^17]reducedSlope(v,k,z0-d)
       =-48D*v^9*(3k+1)^4*(3k+4) < 0.

Uniqueness of polynomial coefficients excludes any representation of this same polynomial with all nonnegative coefficients in nonnegative powers of d. Dividing its difference from the boundary value by d leaves a degree-sixteen polynomial with that same negative leading coefficient. This does not assert negativity at any physically admissible d.

## No-go closure

- **Exact killing mechanism:** the full reduced source has positive odd highest kinetic degree, forcing a negative highest coefficient under downward displacement. All-nonnegative displacement power coefficients are impossible even though physical interval positivity may hold.
- **Strongest positive survivor:** the all-order top-two integer jet and reflected-moment coefficients; the exceptional first-moment correction; the exact rank-one leading matrix; the all-order two-index-moment decomposition of its residual and explicit opposite-sign directions; the exact quadratic-plus-cubic determinant decomposition with the entire remainder retained; complete degree-sixteen minor and degree-seventeen slope identities with their factored leading coefficients.
- **New insight:** the first reflected moment prevents an additional rank cancellation. C78 must exploit its finite physical interval through a suitable interval basis or a signed decomposition. Neither the global boundary Bernstein certificate nor the combined divided-difference sign on the admissible interval is refuted.
- **Status:** dependency-closed paper proof; sixteen unaudited Lean proof sources prepared. No Lean certificate yet. Exact formalization and integration are required before retirement.

## Log

- 2026-10-05 — Derived during C77 row44 audit from the literal integer source field and reflection sum. Corpus queries `/tmp/tt_c78_kinetic_degree_rank_search.json` (partial, generation1241120, inventory65797) and `/tmp/tt_c78_kinetic_leading_frontier.json` (partial, generation1241154, coverage pending) supplied no matching coefficient theorem; both reported deadline/refresh limitations. Candidate/source/idea/ingredient sections inspected. No exhaustive novelty claim, numerical sampling, external coefficient arithmetic, source truncation sign inference, or second Lean build.
- 2026-10-05 — During row45, prepared the exact operator identity `partial_j integerStep = integerStep partial_j + kineticCommutator78`, where `kineticCommutator78 P = (12k+4) partial_k P + (12k+8)u partial_j P`. Its coefficients are independent of j, so its commutator with `partial_j` vanishes. Iteration gives the full-source derivative recurrence with multiplier n; the second scratch module uses this recurrence to prove the factorial-weighted top-two jet identities by induction. No high-order jet truncation or source-field replacement. Both files pass a static forbidden-declaration scan, but compilation and axiom audits remain pending. Search `/tmp/tt_c78_kinetic_coefficient_api.json` was partial with generation1241354 and pending coverage. The additional `/tmp/tt_c78_reflection_binomial_api.json` search was partial (index1241443, coverage snapshot1241450, inventory65810, compiler mostly pending/stale, background refresh incomplete). It located the existing `MicroSpectrumMomentCollapse.alternating_binomial_sum_pow_eq_zero` and factorial identity, whose source proofs were inspected for reuse in the reflection cancellation. No exhaustive novelty claim.
- 2026-10-05 — Prepared the third module, `TTC78KineticPolynomial`, to reinterpret the entire source polynomial as a polynomial in J with multivariate coefficients. Its exact partial-derivative intertwining transfers the induction to the literal degree and top-two coefficient statements, using this toolchain's `Polynomial.coeff_iterate_derivative`, `Nat.descFactorial_self`, and factorial cancellation. These API sources were inspected; `/tmp` elaboration checks are included and remain pending. No coefficient sampling or external arithmetic. Static forbidden-declaration scan empty. The reflection endpoint sums, exceptional rank form, complete minor/slope identities, and displacement obstruction still require formalization; none is claimed as Lean-proved.
- 2026-10-05 — During row46, replaced the fraction-field step in Section 3 with a polynomial reversal argument: normalize only by powers of 12, retain constant coefficient `-12y`, take row/column differences, and obtain the determinant coefficient `512u^2y^4` without dividing by u or y. Prepared `TTC78KineticReverse` for exact reversal multiplicativity of the complete jets, `TTC78KineticBinomialHeads` for the all-order endpoint-corrected sums, and `TTC78KineticReflectionHeads` for the literal source reflection coefficients. The prepared constant/linear head identities retain both the zero-index correction and the first-jet correction, with a separate exact n=2 identity. All three pass static forbidden-declaration scans but have no compiler or axiom audit. No full-source reflection coefficient theorem is claimed as Lean-proved. Search `/tmp/tt_c78_top_two_product_api.json` terminated exit0, partial index1241560, coverage snapshot1241561/inventory65812, compiler mostly pending/stale, background refresh incomplete. Candidate/source/idea/ingredient sections inspected; polynomial reversal APIs were then read directly from this toolchain. No exhaustive novelty claim, extra Lean process, coefficient sampling or external arithmetic. The complete minor, full-source slope and displacement obstruction still need Lean proofs and integration.
- 2026-10-05 — The exact rank-one shift also yields the full quadratic-plus-cubic determinant decomposition in Section 3; it retains the complete source quotient and adds no sign premise. This strengthens the positive survivor beyond the leading coefficient. No Lean source for this additional identity yet. Follow-up `/tmp/tt_c78_rank_remainder_api.json` terminated exit0, partial generation1241773, coverage pending, refresh/deadline incomplete; all result categories inspected. The related private four-by-four repair and Jacobi identities in `ThetaCuspCoupledOddSeamDirection:16-45` were read and distinguished from the whole-matrix cubic shift. No exhaustive novelty claim. Current-toolchain `Polynomial.divX`, `coeff_divX`, and `X_mul_divX_add` supply the complete quotient operation; these source APIs remain to be checked in the queued direct Lean audit.
- 2026-10-05 — During row47, prepared three further modules. `TTC78KineticNormalizedReflections` proves source reflection degree bounds, normalizes only by powers of 12, and uses `divX` to retain each complete remainder. `TTC78KineticMinorDecomposition` connects the exact shift identity to the literal signed `integerThirdMinor` via degree-justified weighted reversal, giving the full quadratic-plus-cubic decomposition. `TTC78KineticMinorLeading` extracts the vanishing degree-18/17 coefficients and exact degree-16 coefficient `-512*12^18*u^2*y^4`, retaining the exceptional first reflection. All remain UNCOMPILED; static forbidden-declaration scans empty. Full source slope, square/shear transfer, strict physical leading sign and displacement obstruction remain to formalize. Search `/tmp/tt_c78_actual_minor_reversal_api.json` terminated exit0, partial index1241834, coverage snapshot1241835/inventory65822, compiler mostly pending/stale, background refresh and deadline incomplete; all categories inspected. The related `PolynomialODEEvenCompactGapReversedDet` source proves a different corrected fourth determinant reversal; it was read and not imported. Current toolchain reflection, degree, coefficient and complete-quotient APIs were inspected. No source truncation, extra Lean build, numerical sampling, external coefficient arithmetic, production promotion or no-go retirement.
- 2026-10-05 — Prepared `TTC78KineticSourceDerivatives` (injective kinetic reinterpretation, derivative transport, native minor derivatives 16/17/18), `TTC78KineticSlopeCommutator` (the exact all-order response of the complete `integerThirdSlope`), and `TTC78KineticSlopeLeading` (native derivative seventeen, vanishing derivative eighteen, and literal coefficient `48*512*12^18*u^2*y^4*(y+3)`). Added a public derivative-to-degree wrapper over the existing private proof in `TTC78KineticPolynomial`. The first commutation wrapper now reuses the inspected corpus theorem `GaloisForLFunctions.pderiv_comm` from `CoordinateDerivationCommute`. All twelve sources remain UNCOMPILED; static scans empty. Shear/square transfer, strict physical leading sign, displacement obstruction, exact residual indefiniteness and production integration remain pending. Search `/tmp/tt_c78_source_slope_coefficient_api.json` terminated exit0, partial generation1241912, coverage pending and refresh/deadline incomplete; all result categories inspected. The actual source operator is differentiated before any substitution. No numerical sampling, external coefficient arithmetic, second Lean process or no-go retirement.
- 2026-10-05 — During C77 row49, prepared four further sources: `TTC78KineticSquareTransfer` uses the existing `integerSlope_shear_factor`, proves square-chart injectivity and exact J-derivative transport, and transfers the full reduced-slope head without a coordinate nonzero premise. `TTC78KineticDisplacement` retains the whole shifted polynomial and its exact `divX` quotient. `TTC78KineticDisplacementSign` specializes to the actual reduced source, proves the physical leading sign and coefficient-uniqueness obstruction for both full displacement and quotient. `TTC78KineticResidualSignature` identifies the literal all-order residual pairing with its zeroth/first index moments and gives two opposite-sign source directions. The latter strengthens the paper survivor above; no complete-matrix signature is inferred. Added a general coefficient-extraction helper to `TTC78KineticSourceDerivatives`. All sixteen files remain UNCOMPILED with no axiom audits; static forbidden/raised-limit scans empty. Searches `square_transfer_api` (partial index1242048, complete inventory65824, compiler mostly pending/stale), `displacement_source_api` (partial1242116, coverage pending), and `residual_signature_api` (partial1242139, coverage pending) all terminated exit0; all result categories inspected and background refresh/deadline limitations retained. The existing univariate `GomesPolynomialReflectionSymmetry` anticommutator was inspected; the prepared multivariate source transport needs no field structure on its coefficient polynomial ring. This toolchain's complex root, evaluation and divX APIs were read; queued scratch elaboration checks remain pending. No numerical sampling, external coefficient arithmetic, concurrent Lean, production promotion, or no-go retirement. Finite physical-interval C78 positivity is still open.
