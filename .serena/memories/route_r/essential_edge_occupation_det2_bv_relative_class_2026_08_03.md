# Route R essential-edge occupation det2 / BV relative class

Exact new source map: for `a_p = primeFirstTraceEssentialSourceDeviation p` and `r_p = farPrime p`,
`a_p(1)=-p/r_p`, `a_p(2)=1/p-p/r_p^2`, hence source-fixed contraction
`a_p(2)-a_p(1)/r_p=1/p` exactly.

Occupation condensation produces `q(nu)=1/primeProduct(nu)`, enumerating reciprocal positive integers.
Diagonal kernel is HS and not trace class. Quadratic Hilbert-Carleman cocycle is `t^2*zeta(2)/2`;
local det2 is `exp(gamma*t)/Gamma(1-t)` and polarized quotient is Wold-Gamma phase.

Prime relative class `Z_p(s)=(1-p^(-s))*zeta(s)`: regular defect trace at k>1;
quadratic trace `Z_p(2)`; residue at 1 is `1-p^-1`, exactly Wold first-cell mass and adjacent BV residue coefficient.

Formal module: `formal/GaloisForLFunctions/RHTower/PrimeEssentialEdgeOccupationDet2BVRelativeClass.lean`.
Wired into `formal/GaloisForLFunctions/RHTower.lean`. Direct Lean, formal lint, targeted module build, and axiom audit passed.
Axioms only `propext`, `Classical.choice`, `Quot.sound`.

Hard boundary: `primeFirstTraceEssentialEdgeOccupationFredholmDet_ne_zero` proves scalar det2 is nowhere zero.
Therefore it cannot yield arithmetic Xi annihilation. Route R still needs sign-indefinite, nonseparable, off-diagonal
pre-scalar source differential/null-homotopy preserving prime/depth/divisor provenance.
Open card: `docs/drafts/pipeline/1-in-progress/route-r-essential-edge-occupation-det2-bv-relative-class.md`.
Formalized card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-r-essential-edge-occupation-det2-bv-relative-class.md`.