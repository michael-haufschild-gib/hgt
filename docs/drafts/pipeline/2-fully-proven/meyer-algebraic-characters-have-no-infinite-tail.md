# Meyer algebraic characters have no infinite tail

- **ID:** meyer-algebraic-characters-have-no-infinite-tail
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Q-II; positive degree classification and source-class inversion.
- **Statement:** Every nonzero complex-linear multiplicative functional on genuine Meyer cohomology is evaluation at one Xi divisor point, without any continuity assumption. It respects arithmetic sharp exactly at critical points.

## Corpus lead

`DeningerMeyerOriginalConvolutionInverse` supplies an actual source-class
inverse for each finite-resonance repaired convolution. Its underlying input
`exists_deningerMeyerSourceQuasiInverse` proves that absence of common Xi zeros
is the sole obstruction to quasi-inversion inside the original source class.
`MeyerFiniteJetAlgebra` supplies exact finite causal Hasse expansions and the
truncated local product; its formal verification is still pending.

## Dependency-closed paper proof

Normalize a source g so that a nonzero character chi has chi(g)=-1. Write the
repaired convolution as R=Id+C_g(Id-P), with P its finite resonant projector.
Multiplicativity gives chi(Rv)=chi(Pv). The actual source inverse makes R
surjective, so chi cannot vanish on every finite jet class. Within a finite
block, nilpotent positive-order jets have character zero; its value idempotent
has character zero or one. Thus some point idempotent e has chi(e)=1.

For every class u, chi(u)=chi(ue). The finite local expansion of ue has only
one surviving character coefficient, its zeroth Mellin value. Therefore chi
is the point evaluation. Distinct points are separated by actual point
sources. Sharp reflects the evaluation point across the critical line, so
sharp compatibility is precisely criticality. Critical evaluations are
positive on every arithmetic sharp square; an off-line point is not Hermitian.

## Scope and status

This classifies multiplicative degrees only. It does not imply that a general
positive linear degree has zero infinite residual energy or is continuous.
No algebraic character at infinity can be inferred merely from that residual.
The exact original repair/inverse and finite causal expansion statements were
read. Internal searches found finite-packet surjections and original-source
inversion, but no full algebraic character classification. External novelty
unverified. No Lean certificate is claimed.

## Explicit local and global steps

Let e_(rho,j) denote the Hasse-normalized actual class. The multiplication law
is e_(rho,j)e_(rho,k)=e_(rho,j+k) below multiplicity and zero at or above it;
distinct point blocks multiply to zero.

1. Every positive-order class has character zero. Descend on m(rho)-j: its
   square is either zero or the strictly higher-order class e_(rho,2j), already
   killed. In either case chi(e_(rho,j))²=0 in C.
2. Choose u with chi(u) nonzero and an actual representative a. Set
   g=-a/chi(u), so chi([g])=-1. The original repaired operator is exactly
   R_g(v)=v+[g](v-P_gv), with P_g a finite complete causal projector. The
   proved actual inverse supplies v with R_g(v)=u. Hence
   chi(u)=chi(v)-chi(v-P_gv)=chi(P_gv), which is nonzero.
3. Expand P_gv as the exact finite sum of Hasse classes. At least one class
   has nonzero character. Step 1 makes it a zeroth class e_rho. Idempotence
   e_rho²=e_rho forces chi(e_rho)=1.
4. Every different point block has character zero, because its product with
   e_rho is zero. Thus on every finite Hasse sum chi agrees with Mellin value
   at rho, including its exact factorial-normalized expansion.
5. The local idempotent multiplies an arbitrary u into its complete singleton
   causal projection P_{rho}u. One can check this on all jets directly; or
   use centrality of causal projectors and expand P_{rho}u into its finite
   block, on which e_rho is an identity. Therefore
   chi(u)=chi(ue_rho)=chi(P_{rho}u)=M_u(rho).
6. If two points represented the same character, evaluating their zeroth
   point idempotents would give 1=0. The representing point is unique.
7. Sharp sends value at rho to conjugate value at r(rho)=1-conjugate(rho).
   Distinct point separation makes Hermitian compatibility equivalent to
   r(rho)=rho, or Re rho=1/2. At a critical point sharp-square values are
   exactly |M_u(rho)|². At an off-line point put u=e_rho-e_{r(rho)}. Its
   sharp square is -e_rho-e_{r(rho)}, whose rho character is -1. Thus
   nonnegativity on all sharp squares is also exactly criticality.

The finite resonance repair is essential: finite-jet classification alone
would not rule out a multiplicative degree annihilating every finite packet.
It is precisely the surjective original-source inverse that excludes that
possibility, with no assumption of continuity or exchange of infinite sums.

## Lean work

`/tmp/QIIMeyerFiniteProjectorAlgebraDraft.lean` isolates the reused finite
projector algebra, including the local idempotent identity. The finite critical
energy draft now imports that proposed module instead of duplicating its
central-multiplier proof. Both drafts remain unverified.

`ArithmeticCastelnuovoSeveri/MeyerAlgebraicCharacters.lean` now contains unverified proofs of
finite detection by the actual repaired inverse, zero higher character jets,
selection of a value idempotent, unique global Xi evaluation, and exact
Hermitian/positive critical-point classification. The planned actual module
is `ArithmeticCastelnuovoSeveri/MeyerAlgebraicCharacters.lean`.

Actual candidate file exists with endpoint axiom prints; its actual-file
verification is pending. It is not wired into the umbrella.

## Separation corollaries [PROVED HERE, paper]

The intersection of all complex algebraic character kernels is exactly the
ordinary trace radical: both mean vanishing of every Xi value. Characters
therefore separate genuine Poisson classes exactly when every Xi zero is
simple, with no RH condition. No identification with an abstract Jacobson
radical over arbitrary residue fields is asserted.

The intersection of all positive character kernels instead means vanishing
of critical Xi values. Positive characters separate genuine classes exactly
under RH and simplicity. For necessity, a principal sharp square has zero
value under every positive character, hence its source does too; separation
makes that source principal. The proved sharp-square-root criterion gives
RH and simplicity. Conversely these two conditions make every Xi value a
positive character and make values detect all required jets.

All common-kernel and separation endpoints are present in the unverified
actual character candidate. This distinguishes algebraic character separation
from positive character separation without assuming either.
