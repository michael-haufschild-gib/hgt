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

Lean formalization has not started. The sole live C77 pipeline retains priority. Do not retire this no-go before the exact survivor is formalized. No degree bound by itself is counted as the intended frontier result: the target is the sign obstruction and exact source rank structure.

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

Work first in the fraction field of the generic u,k polynomial ring and use epsilon=1/j as a formal Laurent variable. Every entry of the reflection matrix has its leading factors

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

This is a polynomial identity. Clearing the temporary fraction-field factors extends it to all specializations, including u=0 or y=0. When u and y are nonzero the displayed coefficient is nonzero and the degree is exactly sixteen. For real u!=0 and y>0, E is indefinite, since its determinant is strictly negative. The exceptional first reflection is essential to this two-direction structure.

### 4. Full source slope and downward displacement

The audited source slope is

    integerThirdSlope = (2y-3)*D_source(integerThirdMinor)
                         -6*integerThirdMinor*D_source(2y-3).

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

For every real center z0, replacing z by z0-d consequently gives

    [d^17]reducedSlope(v,k,z0-d)
       =-48D*v^9*(3k+1)^4*(3k+4) < 0.

Uniqueness of polynomial coefficients excludes any representation of this same polynomial with all nonnegative coefficients in nonnegative powers of d. Dividing its difference from the boundary value by d leaves a degree-sixteen polynomial with that same negative leading coefficient. This does not assert negativity at any physically admissible d.

## No-go closure

- **Exact killing mechanism:** the full reduced source has positive odd highest kinetic degree, forcing a negative highest coefficient under downward displacement. All-nonnegative displacement power coefficients are impossible even though physical interval positivity may hold.
- **Strongest positive survivor:** the all-order top-two integer jet and reflected-moment coefficients; the exceptional first-moment correction; the exact rank-one leading matrix and indefinite next 2 by 2 form; complete degree-sixteen minor and degree-seventeen slope identities with their factored leading coefficients.
- **New insight:** the first reflected moment prevents an additional rank cancellation. C78 must exploit its finite physical interval through a suitable interval basis or a signed decomposition. Neither the global boundary Bernstein certificate nor the combined divided-difference sign on the admissible interval is refuted.
- **Status:** dependency-closed paper proof only. No Lean source or certificate yet. Exact formalization and integration are required before retirement.

## Log

- 2026-10-05 — Derived during C77 row44 audit from the literal integer source field and reflection sum. Corpus queries `/tmp/tt_c78_kinetic_degree_rank_search.json` (partial, generation1241120, inventory65797) and `/tmp/tt_c78_kinetic_leading_frontier.json` (partial, generation1241154, coverage pending) supplied no matching coefficient theorem; both reported deadline/refresh limitations. Candidate/source/idea/ingredient sections inspected. No exhaustive novelty claim, numerical sampling, external coefficient arithmetic, source truncation sign inference, or second Lean build.
