# CCM-FU: exact transverse reserve commutation

- Stage: 3-formalized.
- Type: [BRIDGE], exact source decomposition.
- Full chain: actual divisor source → renewable signed reserve → exhaustive selection → uniform O(M) signed Abel bound → RH.
- RH remains open. This isolates the cost that head balancing leaves unchanged.

## Statement

For the literal retained divisor source, let Q(M,P) be complete energy
and F_R(M,P) its signed fibre at the unprocessed prime label R. Define

    T(M,P)=Q(M,P)−F_empty(M,P)^2−F_{2}(M,P)^2.

For M>2 this is the nonnegative sum of all squared fibres at labels
other than empty and {2}. No sign assumption on any fibre is used.

Let L be a block of fresh primes p<M, p≠2. Suppose P contains every
prime below floor(M/p)+1 except two for each p in L, and distinct p,q in L
satisfy floor(M/p)+1≤q. These are the literal two-coordinate child-support
and mutual child-inactivity conditions. Put

    R(M,P,L)=sum_{p in L} p*(I_0(M,p,P)^2+I_2(M,p,P)^2),

where I_0,I_2 are the adjacent-cutoff interpolated source fibres.
Then

    T(M,P union L)=T(M,P)−R(M,P,L).

This equality holds for every such block, regardless of its signed
receiving displacement. Exact balance, a small head, a quadratic budget,
and availability of further helpers are not required.

For any finite set A of primes excluding two and disjoint from L,

    T(M,(P union L) union A)−T(M,P union L)
      =T(M,P union A)−T(M,P).

In particular every other available prime q≠2 has exactly the same
transverse insertion cost before and after consuming L. Its quotient
M/q can be arbitrarily large. Further processed primes already in P
are allowed in A and contribute no change.

The exact cost of inserting a fresh prime q<M, q≠2 is

    Delta_q T = 2 sum_{R != empty,{2}; q not in R} F_R F_{R union {q}}
                −F_{q}²−F_{2,q}².

The sum retains every actual complementary label. Thus only an independent
bound on the complete signed pair sum can control this cost; smallness of
the two receiving coordinates does not appear in its formula.

## Proof

Remove the empty and {2} terms from the complete finite energy sum to
identify T and prove its nonnegativity.

Write X=sum_{p in L}sqrt(p)I_0 and Y=sum_{p in L}sqrt(p)I_2. The existing
exact source batch identities give

    Q(P union L)=Q(P)−2F_empty X−2F_{2}Y+X²+Y²−R,
    F_empty(P union L)=F_empty(P)−X,
    F_{2}(P union L)=F_{2}(P)−Y.

Subtracting the two updated receiving squares cancels all four receiving
terms and leaves T(P union L)=T(P)−R.

For an available prime q≠2 outside L, the child-support condition forces
q≥floor(M/p)+1 for every p in L: otherwise q would belong to P. Therefore
inserting q leaves both interpolated helper coordinates unchanged.
Apply the same reserve identity at P and at P union {q}. Their reserves
are identical, so subtraction proves exact equality of the q gains.
Induct on A, omitting already processed primes, to obtain the finite-core
identity. At every induction step the original P still supplies the
child-support condition and L remains fresh by disjointness.

Finally start from the exact nonempty-energy insertion formula and remove
the {2} term of its paired sum. The new {2} receiving square is
(F_{2}+F_{2,q})². Its cross term cancels the removed paired term,
leaving the displayed full transverse cost formula.

## Lean surface

File: `formal/GaloisForLFunctions/RHTower/MobiusDivisorTwoTransverseEnergy.lean`.

- `mobiusDivisorTwoTransverseEnergy_eq_sum`
- `mobiusDivisorTwoTransverseEnergy_nonneg`
- `mobiusDivisorTwoTransverseEnergy_union_two_child_inactive`
- `mobiusDivisorTwoTransverseEnergy_insert_gain_union`
- `mobiusDivisorTwoTransverseEnergy_union_gain_union`
- `mobiusDivisorTwoTransverseEnergy_insert_cross`

The proof uses the literal existing source identities and finite algebra.
No computation output, numerical sign, additional axiom or RH hypothesis
is used.

## Consequence for the open proof

The previous prescribed-stream construction controls the receiving
displacement and spends copied-square reserve. This theorem separates
that operation from the change caused by advancing the remaining prime
core. Spending helpers translates the transverse energy by a fixed
amount and leaves the entire additional-core energy landscape otherwise
unchanged. It can pay a positive increment from accumulated reserve;
it cannot change the increment's sign.

The independent candidate that the smallest remaining prime always
has nonpositive transverse cost was [numerically falsified](../5-failed/ccm-fu-transverse-front-renewal.md).
That finite negative assertion is not a Lean theorem. The exact identities
above are the dependency-closed positive survivor. The full RH objective
still needs a uniform bound on cumulative actual transverse costs and a
compatible receiving-coordinate bound through exhaustive selection.

## Validation

All six theorems passed scratch checking and exact foreground leaf emission
with `lake env lean`. One temporary-file axiom audit covered only these
six new theorems. Each depends solely on `propext`, `Classical.choice` and
`Quot.sound`. The leaf is wired into RHTower; no full or umbrella build ran.
A scoped Lake package audit remains pending because previous package
planning expanded prohibited broad dependencies; that planning was not
repeated. No computed certificate was used.

Indexes were refreshed. The single `scripts/formal_tools.py lint
--check-generated` run reported unrelated concurrent umbrella gaps in
`HTGeometry.FokasLenellsLaxCompatibility`,
`HTGeometry.FokasLenellsPlaneWaves` and
`HTGeometry.FokasLenellsUniformization`, plus stale generated
`formal/LEAN_API.md` and `formal/LEAN_OVERVIEW.md` after concurrent work.
No changed-proof or proof-debt error was reported. Scoped whitespace
checks passed. The two owned Lean scratch files and temporary lint log
were removed; every owned Lean process exited.

RunPod numerical work is documented separately. Its four owned remote
files and directory were removed after matching downloaded hashes; a
final process working-directory inspection found no owned workers.
The frontier map was read only.
