# EDQ actual coprime head: unconditional subpower remainder

Stage: 3-formalized. Arithmetic estimate; RH remains open.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.

## Closed estimate

Let

`W(N)=sum_(d,e<=N, gcd(d,e)=1)mu(d)mu(e)/(de)`

and let the actual signed coprime residue quadratic at coordinate t be

`B_N(t)=sum_(d,e<=N, gcd(d,e)=1)mu(d)mu(e)*{t/d}*{t/e}`.

For integer t the fractional parts are exactly `(t mod d)/d`; this is the
coprime portion of the corpus's discrete modular Gram, with its normalized
residues retained. It is a signed portion, not a separately positive energy.

For every epsilon>0, Lean proves one constant C_epsilon>0 such that, for
every natural cutoff N,

`|sum_(t=1..N) B_N(t)/[t(t+1)]
  - W(N)*sum_(t=1..N)t/(t+1)| <= C_epsilon*N^epsilon`.

There is no RH premise, sign assumption on W, numerical input, or omitted
term inside this initial range. The theorem also covers N=0.

## Mechanism

The preceding [complete-column estimate](edq-coprime-column-cancellation.md)
identifies `sum_(e<=t, gcd(d,e)=1)mu(e)*floor(t/e)` with S(d,t), the count of
integers through t supported on primes dividing d. Its uniform bound is
`S(d,t)<=C_delta*t^delta*d^delta`.

Define `L_N(t)=sum_(d<=N)mu(d)*S(d,t)/d`. For t<=N, floor columns indexed
beyond t vanish exactly. Symmetry and finite polarization therefore give

`B_N(t)=t^2*W(N)-2t*L_N(t)+F_[1,N](t)`.

Here F is the previously formalized complete-inner-column floor correlation;
its outer selection automatically intersects `[1,t]`. The mixed column has
`|L_N(t)|<=C_delta*N^(2delta)*(1+log N)`. The complete floor term has
`|F_[1,N](t)|<=C'_delta*t^(1+delta)`. Summing against the actual weight
`1/[t(t+1)]` costs only harmonic factors. Set delta=epsilon/4 and absorb
those factors to obtain the displayed subpower estimate.

## Exact proof boundary

The explicit W(N) term remains. Its nonpositivity cannot be assumed: the
[working card](../1-in-progress/edq-full-covariance-core-attack.md) contains a
rational paper derivation of `W(22)>3/800`. That finite counterexample has
not been audited in Lean and is not used in the theorem above.

The positive statement exposed by that failed sign shortcut is now closed:
the actual initial coprime quadratic equals its exact arithmetic leading
term up to a subpower remainder. The remaining task is to control its joint
combination with the complete later tail. General gcd groups also retain
their exact coprimality masks and affine within-block offsets. This theorem
does not assert a bound on the full EDQ energy. The stronger
[all-gcd aggregate remainder](edq-gcd-head-subpower.md) is now closed too;
the retained harmonic coefficients and complete later tail remain open.

## Validation

Module: `GaloisForLFunctions.RHTower.EulerDeletionCoprimeHeadSubpower`.
Namespace: `RHTower.DeletionCoprimeHead`.
Five public definitions, two public theorems, seven private helpers.
Main statements: `residueQuadratic_eq` and
`exists_initialEnergy_remainder_subpower`.

The complete scratch passed `LEAN_NUM_THREADS=1 lake env lean` with no
diagnostics. Final `lake build --old` of this leaf passed in 7.1 seconds;
only this leaf was built and dependencies were reused. Its umbrella import
is wired; no umbrella or full build ran. A separate temporary audit of only
the seven new public declarations found exactly `propext`, `Classical.choice`,
and `Quot.sound`. Corpus indexes were refreshed once and repository lint
passed. The RunPod experiment informed the choice of attack but supplies no
fact or premise to any Lean proof.
