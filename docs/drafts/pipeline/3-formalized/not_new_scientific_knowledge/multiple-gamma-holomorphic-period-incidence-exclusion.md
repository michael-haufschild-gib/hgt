# Holomorphic physical-character germs exclude the ambient period-incidence defects

- **ID:** `multiple-gamma-holomorphic-period-incidence-exclusion`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4) / PROGRAMME-4 BENCHMARK NO-GO / POSITIVE SOURCE-IMAGE CLASSIFICATION
- **Source:** `docs/reports/rh-status-1707.md`, research programme 4;
  `../3-formalized/not_new_scientific_knowledge/multiple-gamma-da-meromorphic-physical-character-comparison.md`;
  `hypertranscendental-bornological-krull-radical.md`
- **Scientific status:** `[LEAN-FORMALIZED] [PAPER-PROVED] [REDISCOVERED] [BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Statement:** For any subset `S` of the punctured unit disk accumulating at zero, bounded
  holomorphic evaluation `ev : H^infinity(D) -> ell^infinity(S)` meets the closure of the first
  period-incidence range exactly in that range, and meets the intersection of all powered ranges
  only in zero. Consequently the ambient nonclosed-range quotient and nonzero flat intersection
  cannot be produced by a bounded holomorphic physical-character germ.

## Exact Lean capstone

Let `L` be a nondiscrete integer submodule of `C`, let

```text
w(q)=q/(1+|q|),
T(a)(q)=w(q)a(q),
T_r(a)(q)=w(q)^r a(q),
ev_L(f)(q)=f(w(q)),
```

and suppose `f` is analytic and bounded on the unit disk. Then

```text
ev_L(f) in closure(range(T)) <-> ev_L(f) in range(T),             (F1)

(forall r : N, ev_L(f) in range(T_r)) -> ev_L(f)=0.               (F2)
```

Both statements are unconditional. The proof also formalizes the sharper intermediate facts

```text
ev_L(f) in closure(range(T)) <-> f(0)=0 <-> ev_L(f) in range(T),

ev_L(f) in range(T_r) -> r <= analyticOrderAt(f,0).
```

The exact theorem is `holomorphic_period_incidence_exclusion` in
`formal/GaloisForLFunctions/HTGeometry/HolomorphicPeriodIncidenceExclusion.lean`.

## Stronger paper claim

Let

```text
S subset {z in C : |z|<1 and z!=0},       0 in closure(S),
A=ell^infinity(S),
w(s)=s,
(M_w a)(s)=s a(s),
ev(f)(s)=f(s),                            f in H^infinity(D).
```

Then:

```text
ev(f) in closure(range(M_w))
  <-> f(0)=0
  <-> ev(f) in range(M_w);                                      (1)

ev(f) in range(M_w^k)
  <-> ord_0(f)>=k                       for every k>=1;           (2)

q(ev(H^infinity(D)) intersect closure(range(M_w)))={0},          (3)

ev(H^infinity(D)) intersect intersection_(k>=1) range(M_w^k)
  ={0}.                                                         (4)
```

where `q:closure(range(M_w))->closure(range(M_w))/range(M_w)` is the algebraic quotient map.
It does not assert that the non-Hausdorff quotient is a separated Banach space.

## Programme-4 role

The multiple-Gamma ambient receiver already has:

```text
strictly decreasing powered ranges;
identical positive-order norm closures;
a nonzero all-power flat section;
finite-order exact source comparison.
```

The open `BCDef_F` proposal asks for a source-natural completion/base-change comparison. Equations
`(1)`--`(4)` test whether the existing ambient strictness and flat classes can be that source
defect. If the claim is true, the answer is no for every completion whose physical-character
image factors through bounded holomorphic functional calculus.

## Paper proof

For `(1)`, exact range implies closed-range membership. Suppose `ev(f)` is a uniform limit of
`M_w a_n`. Given `epsilon>0`, choose `n` with `||ev(f)-M_w a_n||<epsilon`. Along a sequence
`s_j in S` with `s_j->0`, boundedness of the fixed element `a_n` gives
`s_j a_n(s_j)->0`, while continuity gives `f(s_j)->f(0)`. Hence `|f(0)|<=epsilon`; because
`epsilon` was arbitrary, `f(0)=0`. Conversely, if `f(0)=0`, Schwarz's lemma applied to
`f/||f||_infinity` (with the zero function handled separately) gives `f(z)=z g(z)` with
`g in H^infinity(D)`. Therefore `ev(f)=M_w(ev(g))`.

For `(2)`, vanishing to order at least `k` and the iterated Schwarz lemma give
`f(z)=z^k g(z)` with `g in H^infinity(D)`, proving exact range membership. Conversely, suppose
`ev(f)=M_w^k a` with `a in A`. If `f` had first nonzero Taylor coefficient `c_m` with `m<k`, then
`f(z)/z^m -> c_m` as `z->0`. Along `s_j->0`, this would make
`|f(s_j)/s_j^k|=|s_j|^(m-k)|f(s_j)/s_j^m|` diverge, contradicting boundedness of `a`.
Thus `ord_0(f)>=k`. Equation `(4)` follows because a holomorphic function with arbitrarily high
vanishing order is zero. Equation `(3)` is the quotient form of `(1)`. `QED`

## Hostile review and exact boundary

- `[PASS]` The actual bounded period symbol `q/(1+|q|)` is used only through its value set `S` in
  the disk; no holomorphic dependence on `q` is claimed.
- `[BOUNDARY]` The genuine multiple-Gamma completion has not been proved to factor through
  `H^infinity(D)`. The theorem is an unconditional classification of every bounded holomorphic
  source image, not a claim that the missing source completion already exists.
- `[REDISCOVERED]` Schwarz division, the identity theorem, and diagonal multiplier ranges are
  standard parent complex/functional analysis. The abstract theorem carries no novelty claim.
- `[SURVIVES]` A source-natural non-holomorphic bornological completion can evade the theorem, but
  must be constructed from the actual source. Selecting it only because it contains the ambient
  flat class is circular and fails the source-naturality gate.
- `[FORMAL BOUNDARY]` Lean formalizes the actual nondiscrete period receiver and the capstones
  `(F1)`--`(F2)`, together with the forward finite-order implication. The reverse finite-order
  implication in `(2)` and the arbitrary-subset packaging remain paper-level strengthening; they
  are not needed for the programme-4 exclusion.

## Relentless-interrogation successor

If the ambient flat/strictness class is excluded from the holomorphic source image, the stronger
replacement conjecture is:

> **[CONJECTURE]** A nonzero multiple-Gamma `BCDef_F`, if it exists, is a transgression measuring
> failure of the genuine source completion to remain inside bounded holomorphic physical-character
> calculus. It is not the bare `ell^infinity` flat radical or strictness quotient. Its first proof
> obligation is an explicit source element whose two completed realizations differ.

This successor survives the exclusion because it predicts a class in the comparison between two
source realizations, not a class already present in the target multiplier algebra.

## Open core

`[OPEN CORE]` Construct the genuine multiple-Gamma source completion and exhibit one explicit
source element on which completion before physical-character base change differs from base change
before completion. Without that element, `BCDef_F` is only a formal cone and programme 4 has no
source-produced multiple-Gamma defect.

## Gates

- [x] inherited programme-4 benchmark isolated from the broader unified-field conjectures
- [x] exact source-image exclusion stated
- [x] dependency-closed paper proof completed
- [x] external parent-theory and rediscovery audit completed
- [x] hostile review of the exact hypotheses completed
- [x] moved through Stage 2 as `[PAPER-PROVED] [BRIDGE]`
- [x] exact unconditional capstone formalized in Lean 4
- [x] touched module checked against the repository toolchain
- [x] moved to Stage 3 as `[LEAN-FORMALIZED] [BRIDGE]`
