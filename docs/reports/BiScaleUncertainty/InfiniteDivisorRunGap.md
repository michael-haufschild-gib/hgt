# Arbitrary divisor families: exact run-gap classification

Status: dependency-closed paper proof; Lean certification pending. One proposed
connected contribution, currently uncounted.

## Actual objects and statement

Fix d∈ℕ and an arbitrary set D⊆ℕ. Index k denotes physical node k+1.
Put A(k) iff some e∈{d}∪D has e+2 dividing k+1. Let H_A be the closed
coordinate-mask fixed subspace of real ℓ²(ℕ), counting every union node once.
Masking any ambient vector gives an actual member. Define E_A v=S(v−Rv),
where S is the certified isometry synthesizing the physical unit-cell indicators
and R is the certified right shift. No periodicity or finite-family assumption
is used. All integer traces, logarithmic traces, exact adjacent energy and
competitor mismatch follow from the existing integer extension:

    F_(E_A v)(k+1)=v_k,
    ‖E_A v‖²=2‖v‖²−2Σ_k v_k v_(k+1).

In particular E_A is injective for every family, including families with no gap.
The data space is a closed kernel of a bounded operator, hence complete.

The following three properties are equivalent, unconditionally on d,D:

1. E_A has closed range in physical L².
2. Some c>0 satisfies c‖v‖²≤‖E_A v‖² for every v∈H_A.
3. Some r∈ℕ satisfies: every k has a missing node among k,…,k+r.

## Bounded-run case and exact sharp constants

Take the least such r. Since A(d+1), r≥1. Failure of the exclusion property
at r−1 gives a run a,…,a+r−1 consisting entirely of active nodes. Thus r is
exactly the maximum run length, even though the family need not be periodic.

On complex ℓ² let P be the actual mask and T=P R* P. It is contractive.
Each coefficient of T^r follows r successive edges; a missing node among its
r+1 visited nodes annihilates that coefficient. Hence T^r=0. The already
certified nilpotent contraction numerical-radius theorem gives

    |Σ v_k v_(k+1)| ≤ cos(π/(r+1))‖v‖².

Combining with the exact energy proves both sharp factors
2−2cos(π/(r+1)) and 2+2cos(π/(r+1)). The lower one is strictly positive.
The sine packet sin(π(j+1)/(r+1)), 0≤j<r, on the attained run, and its
alternating-sign companion attain the two factors with positive norm.
This uses the certified finite sine recurrence, not an assumed spectral gap.
The positive lower bound gives an antilipschitz continuous map from a complete
space and therefore a closed range.

## Unbounded-run producer and the reverse implications

If no finite exclusion length exists, for every n≥1 choose the least start
a_n of an active run of length n. Put s_n=Σ_(j<n) sin²(π(j+1)/(n+1))>0.
The actual data

    v_n(a_n+j)=sin(π(j+1)/(n+1))/√s_n  (0≤j<n),
    v_n(k)=0 otherwise

have norm one and exact energy

    ‖E_A v_n‖²=2−2cos(π/(n+1)) → 0.

Convergence follows from π/(n+1)→0 and continuity of cosine. This proves
that no positive c works. Zero energy remains unattained on unit data because
the integer trace identity proves injectivity. Hence zero is the infimum of
the unit-data energy set, witnessed by actual finite packets.

If the range were closed, the injective bounded map between complete spaces
would have a bounded inverse on its range, by the Banach open mapping theorem.
There would be K≥0 with ‖v‖≤K‖E_A v‖. Squaring and substituting v_n gives
1≤K²‖E_A v_n‖², contradicting the limit zero. This establishes the reverse
closed-range implication without assuming an inverse or a coercivity premise.

For the concrete family D=ℕ every k≥1 is active (take e=k−1), while k=0
is inactive. Thus it has arbitrary long runs and nonclosed range, with the
same explicit near-null producer construction. Positive individual energy
does not imply a positive uniform energy coefficient.

The usual all-integer-trace minimum-energy identity remains valid in both
regimes: matching all integer traces gives
‖q‖²=‖E_A v‖²+‖q−E_A v‖². It does not assert stability of reconstruction
from ℓ² data when runs are unbounded.

## Sources and scope

The finite path sine bound is classical; see Izmestiev,
[discrete Wirtinger inequality, §1.3](https://arxiv.org/html/1502.03186v1).
The closed-range step is the classical open mapping theorem; the precise
implementation is documented in
[mathlib's Banach operator theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Operator/Banach.html).
No external novelty claim is made for those parent results. The contribution
is the complete arithmetic-family classifier for the actual continuum trace
producer, with sharp bounded constants and explicit unbounded-case witnesses.

The original hybrid corpus query returned no candidates and reported interrupted
text/source retrieval, pending coverage generation1445895. A focused lexical
query and exhaustive scoped text search supplement it. No absence/novelty claim
follows from partial corpus coverage. README remains read-only. No RH work,
unweighted logarithmic H1 identification or full affine unitary claim is made.
