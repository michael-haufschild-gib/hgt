# BAG uniform damping-height square law

- ID: C28.56af.2b; completes the literal-window case of C28.56af.2.
- Route: BAG physical contraction matching, followed by the full signed cubic.
- Status: all five production leaves and all15 public axiom audits passed;
  index refreshed. Global lint reports unrelated unreachable modules.
- Paper: ../2-fully-proven/bag-uniform-damping-height-square-law.md.
- Active: ../1-in-progress/bag-physical-contraction-moving-poles.md.

## Exact frontier theorem

For the ACTUAL W=bagPhysicalHeightWindow and D_e(n)=pmPowerDampedDivisorCoeff,
for every C>0, uniformly over 0<e<=C/log X as X tends to infinity,

    sum_n D_e(n)^2 W(n/X)/(X e^2 log X)
      - Psi(e log X) integral W -> 0,
    Psi(c)=(1-exp(-2c))/(2c).

The final declaration is dampedSquare_physical_window_joint_limit in
ChiRamanujanDampedSquareJointLimit. It includes arbitrarily small positive
e log X. All integers and prime powers remain in the complete weighted sum.
No fixed-damping limit, source-growth assumption, contour assumption,
interchange assumption, or RH premise is used.

The intermediate TendstoUniformlyOn declaration uses c in (0,C] and e=c/log X.
The final theorem states uniformity directly on the shrinking damping interval.
The literal Mellin value M(1) is proved equal to the full real window integral.

## Source proof

1. ChiRamanujanDampedSquareResidues constructs the signed two-pole packet.
   Actual Q(1+e,-e)-1 and Q(1-e,-e)-1 are O(e^2). Entire dslope(M,1) has an
   actual compact bound, so M(1-2e)-M(1)=O(e). With X^(-2e)<=1, the error
   numerator is O(e) BEFORE dividing by 2e log X. The resulting C/log X
   bound holds uniformly on a fixed interval 0<e<=eta, and is promoted to
   TendstoUniformlyOn. No lower bound on e log X is required.
2. ChiRamanujanDampedSquareTails applies the corpus two-sided power-tail
   integral theorem to the actual absolutely integrable original line.
   Arbitrary Mellin strip decay and the actual 24/b^3 normalized Dirichlet
   bound control BOTH infinite tails, independently of e.
3. ChiRamanujanDampedSquareEdges derives the source-disk and Mellin-strip
   conditions throughout the actual rectangle. Real and imaginary parts
   give both pole-distance bounds. The integrated left edge is at most
   C X^(1-delta)(1+T)^55(1+2/delta^2), and each horizontal edge is at most
   A_j X^(1+b)(1+T)^54/(1+T)^j. All constants come from the actual source.
4. ChiRamanujanDampedSquareTransfer proves the exact identity

       R-2*pi*P = (R-R_T)+L+i*(B-U),

   where R is the complete original line, R_T its truncation, P both signed
   residues, and L/B/U the other three edges. Summed inversion then identifies
   the COMPLETE weighted energy error with these four contributions. A single
   actual bound retains the left edge, both horizontal edges and both tails.
5. ChiRamanujanDampedSquareJointLimit takes T=u, X=exp(u^18), b=u^(-18) and
   delta=d/(1+u)^9. One fixed Mellin order60 suffices. All required moving
   geometry holds eventually, uniformly in c in (0,C]. The normalized tails
   tend to zero as a constant times u^(-23); the horizontal error tends to
   zero; the left error is bounded by a polynomial times exp(-a*u), a>0.
   Their uniform sum and residue error tend to zero. The exact substitution
   u=(log X)^(1/18) recovers EVERY sufficiently large real X.

These exponents are incidental choices in a joint-limit proof, not optimized
bounds. A scalar normalization lemma avoids expanding high powers; compiler
heartbeat and recursion limits were not increased.

## Audit record

Five leaves,15 public declarations. Production commands used lake --old env
lean on each leaf with an explicit olean output. Residues20834, Tails94324,
Edges42770, Transfer50009 and JointLimit72335 all exited0 without diagnostics.
The final joint-limit scratch20250 also exited0, including the literal window
mass identity. All five leaves are wired once into RHTower. No umbrella/full
build, numerical experiment, added axiom or subagent was used.

Final axiom17545 exited0: every public declaration depends only on propext,
Classical.choice and Quot.sound. The same /tmp probe checked the used concrete
mathlib/corpus names. Index28644 exited0; all15 API entries and allfive umbrella
imports were verified, each import exactly once. Lint22251 exited1 solely on
40 unrelated modules unreachable from their umbrellas; no proof debt or finding
for these five leaves. Global lint is not claimed clean. All owned jobs exited.

## Remaining hard BAG frontier

This solves the actual uniform quadratic normalization. It does not prove the
full signed Gaussian cubic or justify quadratic-to-cubic promotion. The
complete prime cubic retains both contraction families, their overlap and
the signed noncontracting term. Its exact prime-only Vaughan source is already
formalized, but does not estimate the full shared-modulus sum. The incomplete
weighted determinant correlations, near-resonant terms and growing physical
profiles remain open. Growing moments, moving cofactors and positive
common-height self-return remain open. RH remains unproved.
