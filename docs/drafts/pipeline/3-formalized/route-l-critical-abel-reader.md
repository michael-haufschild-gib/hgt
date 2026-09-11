# Route L: full integral Abel limit and retained physical first variation

Date: 2026-09-11.
Status: formalized; all 39 theorems and final audits passed. RH unproved.
Module: `GaloisForLFunctions.RHTower.DeningerGammaSixCriticalAbelReader`.

## Question and positive result

C24 derives the actual complete integral operator before divisor
specialization. Write its diagonal as `c/k+r_k`, with `sum_k |r_k|<infinity`
and `c=XiC^(a)(w)*XiC^(b)(z)`. The scalar remainder includes the omitted
finite head. The every-depth source domain remains
`|Im(w)|,|Im(z)|<1`, `Re(s(w)),Re(s(z))>1/3`, where `s(w)=1/2+i*w`.

The next comparison is the normalized *actual* Gibbs reader at
`tau=(1+epsilon)/2`, approached through `epsilon>0`. It is not a value
assigned to a divergent endpoint series. Every positive parameter is
admitted by the preceding source theorem. Let

`Z_epsilon = sum_(k>=1) k^(-1-epsilon)`,
`A_epsilon(T) = Z_epsilon^(-1)*sum_(k>=1) k^(-epsilon)*T_kk`.

Let `S_n` be the existing ordinary-integer Wold dilation, `P_n` its range
projection, and

`D_epsilon(n,T) = A_epsilon(S_n^* T S_n) - A_epsilon(T P_n)`.

The proved full-source limits are:

- `epsilon*Z_epsilon -> 1`, `Z_epsilon -> infinity`, `Z_epsilon^(-1) -> 0`;
- `A_epsilon(T) -> c`;
- both compressed and projected readers tend to `c/n`;
- `D_epsilon(n,T) -> 0` for every fixed positive ordinary integer `n`;
- `D_epsilon(n,T)/epsilon -> log(n)*c/n`.

The final limit retains the complete source's Xi coefficient. At every
admissible divisor with multiplicity-top internal orders, `c` is a square
of a nonzero Xi derivative. For each `n>1` the slope is nonzero; the actual
defect is therefore nonzero throughout some sufficiently small positive
Abel interval, despite tending to zero. The interval may depend on the
source and on `n`; no uniform assertion over all labels is made.

The positive comparison goes further than retaining a residue. Let
`B_n(s)` be the already fixed physical BV boundary reader. Its actual
formula on the same Abel path is

`B_n((1+epsilon)/2) = (1/n)*(1-n^(-epsilon))`.

The proved full-source comparison is

`[D_epsilon(n,T)-c*B_n((1+epsilon)/2)]/epsilon -> 0`.

Thus the complete integral source agrees with that physical boundary to
first order at the critical endpoint. No physical reader equality or
cyclicity premise supplies this statement.

## Dependency-closed paper proof

1. Reindex the literal Gibbs partition on positive integers as the
   natural-number power series; its zero-index term is zero in the open
   region. Apply the corpus's real power-series residue theorem along
   `1+epsilon`. This gives `epsilon*Z_epsilon -> 1`. Multiplying by
   `epsilon^(-1)` gives divergence; dividing `epsilon` by the residue
   expression gives the inverse limit.
2. For `epsilon>=0`, each full correction weight has magnitude at most
   one. Hence `|A_epsilon(R)| <= Z_epsilon^(-1)*sum_k |r_k|` for positive
   `epsilon`. Every correction is admitted in that domain. The bound
   tends to zero without exchanging an unbounded limit and a series.
3. The normalized reader is linear on its proved domain, and reads the
   actual reciprocal Green operator as one. Thus
   `A_epsilon(T)=c+A_epsilon(R)` and its limit is `c`.
4. Compression by `n` has diagonal `T_(nk,nk)`. Its reciprocal coefficient
   is `c/n`, and its correction is a subsequence of the same summable
   correction. Step 3 therefore gives the compressed limit `c/n`.
5. The existing full operator exchange law is exactly
   `A_epsilon(S_n^* T S_n)=n^epsilon*A_epsilon(T P_n)`.
   Its inverse gives the projected limit. Their difference tends to
   zero, but it also equals `(n^epsilon-1)*A_epsilon(T P_n)`.
6. The actual derivative of `n^epsilon` at zero is `log(n)`. Dividing the
   preceding exact defect by `epsilon` and taking limits gives the retained
   slope. No derivative of the possibly singular correction is needed.
7. Differentiate the existing physical formula
   `(1/n)*(1-n^(-epsilon))` at zero. Its slope is `log(n)/n`. Subtracting
   its `c` multiple from step 6 gives the first-order physical comparison.
8. Only now specialize the full integral operator to each admissible Xi
   divisor. The multiplicity theorem proves its top derivative nonzero;
   `log(n)>0` for `n>1`. A nonzero normalized limit implies eventual
   nonzero actual defect, and excludes a zero slope limit.

## What this does and does not settle

This constructs a critical Abel limit for the complete integral class,
including all arithmetic tails and each fixed ordinary dilation. It also
retains internal Xi jets and proves first-order agreement with the
existing physical boundary on the critical Abel path. The earlier
`DeningerGammaSixGreenGibbsPhysicalReader` already has a principal
six-shell continuation; that principal calculation is not claimed as new.

The regulator `epsilon` is independent of the spectral source parameters.
The comparison uses the ordinary-integer operator obtained from the
literal column map; it does not construct a map into the Sonin carrier
or prove that every source arithmetic action intertwines these dilations.
Its first variation is a physical horizontal variation at the critical
endpoint, not the actual displacement `2*Re(rho)-1` of an arbitrary
source divisor. Endpoint cyclicity consequently does not identify the
reader at `tau=Re(rho)`. Even critical divisors have a nonzero regulator
slope at top order, so demanding that slope vanish would be an invalid
replacement condition. RH still requires the source-forced comparison
preserving the original horizontal anchor.

## Searches and method audit

Two new deep/method searches concerned normalized summation, dilation,
pole residues and slope limits. Both reported partial coverage, with
706108 ready and 779 stale method records. Retrieved finite normalized
traces assume cyclicity, and generic dominated-convergence results still
require domination and actual measure data. They do not produce the
needed physical comparison. The applied ingredients were read directly
in the current corpus and checked in the scratch: the actual Gibbs
exchange, source-derived summable integral correction, real power-series
residue, and derivative/slope limit APIs.

Broad arXiv searches used `resonance`, `boundary`, and `renormalization`,
with June--September 2026 preference. The [August scale-consistency paper](https://arxiv.org/html/2608.01489v1)
derives restrictions on independent renormalization scales from operator
sum rules and Ward identities (Sections II and VI). This suggests testing
which physical identities survive a regulator change, but supplies no
arithmetic Ward identity here. The [August stochastic RG paper](https://arxiv.org/html/2608.11106v1)
represents partition functions as conditional expectations and obtains a
martingale from an established probability model (Sections 2 and 5).
Imposing that coupling would not construct this source's missing physical
measure or reader agreement. Neither paper is an RH premise.

## Verification

All 39 scratch theorems passed without warnings using
`lake env lean /tmp/route_l_critical_abel.lean`.
`lake build GaloisForLFunctions.RHTower.DeningerGammaSixCriticalAbelReader`
passed. All 39 theorem axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. `scripts/formal_tools.py lint`
passed; existing repository warnings remain. Umbrella import wired.
All owned Lean processes completed. No numerical experiment, full build
or umbrella build was used.
