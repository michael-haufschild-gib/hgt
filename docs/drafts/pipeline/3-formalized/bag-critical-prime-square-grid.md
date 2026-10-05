# BAG exact critical prime-square grid source

- Route: signed physical BAG cubic.
- Stage: paper proof, production and all25 public-declaration axiom audits pass.
- Corpus basis: ChiRamanujanCriticalDistinguishedPrime,
  ChiRamanujanFiniteRationalAtoms, ChiRamanujanWeightedDistinguishedCubic.
- No cubic saving or RH proof is asserted.

Let S be the retained finite prime set, R=product(S), Q=R^2. Retain every
literal divisor/square-divisor critical atom. Send an atom with node
a/d+b/e^2 to a*(Q/d)+b*(Q/e^2) modulo Q. Both denominators divide Q.

For each p in S and 0<=j<p^2 define

    d_p(j)=1_(j=0)-1_(p divides j)/p,
    t_p(j)=1_(p divides j)/p-1/p^2.

On the full product of these prime-square residue sets define

    W(x)=sum_p log(p)*t_p(x_p)*product_(q!=p)d_q(x_q),
    N(x)=sum_p x_p*(Q/p^2) modulo Q.

## Exact source identity [PROVED HERE]

For each integer n, summing exp(2*pi*i*n*j/p^2) over j divisible by p
is the complete p-torsion sum. Therefore the Fourier coefficients of d_p
and t_p are respectively 1-I_(p divides n) and
I_(p divides n)-I_(p^2 divides n). The phase at sum_p x_p/p^2 is the
product of the local phases. Finite product summation gives the Fourier
coefficient of W as the established distinguished-prime multiplier.
This equals the Fourier coefficient of the actual critical atom source
at EVERY integer, including zero and uncovered frequencies.

The phase of each actual atom is the standard character of its grid index;
the same holds for N(x). Group each finite source by grid index. The finite
DFT on ZMod Q is injective, so their grouped masses agree at every node.
No analytic limit, infinite rearrangement or selected frequency is used.

For fixed p, Q/p^2 is the product of q^2 for q!=p, hence coprime to p^2.
Reducing N(x) modulo p^2 kills every other coordinate and gives
x_p*(Q/p^2). Its coefficient is a unit. Thus N is injective. Source and
target both have Q elements, so N is bijective. Consequently the actual
grouped critical mass at N(x) is exactly W(x), with no repeated coordinate
or omitted grid point.

Multiplication by the cofactor unit preserves divisibility by p and by p^2.
Thus the same mass can be expressed directly at k in ZMod Q by

    sum_p log(p)*(I_(p divides k)/p-1/p^2)
      *product_(q!=p)(I_(q^2 divides k)-I_(q divides k)/q).

This includes the zero node and all primitive and nonprimitive residues.

## Exact shifted-coefficient normalization [PROVED HERE]

Put z=1/p and i(j)=0 if j=0, -1 if j!=0 and p divides j, and -2 otherwise.
The existing coefficient c_z is 1 on nonnegative integers, -z/(1-z) at -1,
and zero below -1. Direct symbolic case analysis gives

    d_p(j)=(1-z)*c_z(i(j)),
    t_p(j)=(1-z)*z*c_z(i(j)+1).

Every denominator is nonzero because p is prime. Hence the source really
has the distinguished shift used by the already proved weighted local
traces. Untagged coefficients vanish in the primitive p^2 stratum, while
tagged coefficients there equal -1/p^2. Two distinct primitive prime-square
strata therefore kill every distinguished summand. This classification is
also proved in the production Lean leaf.

## Remaining hard problem

These identities identify the actual rational source and its local signed
coefficients. They give no bound on the complete growing transverse action.
Still prove signed cancellation with the full physical window, Mellin line,
integer lifts, near-cone region and tails, retaining both literal contraction
projectors. Growing moments, moving cofactors, common-height self-return and
RH remain open. No prime-net/Mellin interchange follows from the finite identity.

## Lean audit log

ChiRamanujanCriticalGridSource, 489 lines and25 public declarations, passes
production audit97363 with an empty log under lake --old env lean and leaf
output. All local Fourier formulas, the finite product source, the actual
grouped-source identity, cofactor bijection, direct weight formula, shifted
normalization and two-primitive vanishing are proved. One umbrella import is
wired. Axiom73382 passes for all25 public declarations, with only propext,
Classical.choice and Quot.sound. Index61870 passes; all25 exact module/name
API rows and the single umbrella import are verified. Lint37187 has36
unrelated unreachable-module errors, no new-leaf/proof-debt finding. Global
lint is not clean. No full or umbrella build was run.

Both searches20154 and91212 are nonpartial, with complete inventories65744
and65751 respectively. Their background refresh is incomplete; compiler
metadata is mostly pending/source-only. All20 candidates and20 source
arguments plus proposed ingredients in each were inspected. The second
search and direct current-source reading expose the numerator-cofactor
distinction recorded in the active card. No search absence is used as proof.

Completed scratch sources are removed; logs/search JSON are retained.
No numerical experiments, subagents, added axioms, resource-limit changes,
full/umbrella builds or commits. RH goal remains active.
