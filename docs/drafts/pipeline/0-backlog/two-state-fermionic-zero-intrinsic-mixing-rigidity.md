# [CONJECTURE] A two-state fermionic-zero classification slice may be diagonal

- **ID:** `two-state-fermionic-zero-intrinsic-mixing-rigidity`
- **Stage:** 0-backlog
- **Type:** CONJECTURE / CONVENTION AUDIT / POSSIBLE QFT NO-GO
- **Scientific status:** `[CONJECTURE] [CONVENTION MAP OPEN] [O(N) BENCHMARK BLOCKS PROMOTION]`
- **Scope:** analytic two-state factorizing scattering with positive-metric unitarity and
  `S(0)=-P`; no RH or special-function input
- **Parents:** `../2-fully-proven/needs-audit/projective-wigner-smith-nonabelian-ht-separation.md`
  and `../2-fully-proven/not_new_scientific_knowledge/diagonal-projective-ht-local-qft.md`
- **Candidate statement:** Let `V=C^2` and let `S(theta)` be an analytic positive-unitary
  factorizing-scattering family on `V tensor V` with `S(0)=-P`.  A proposed consequence of the
  published analytic `4 x 4` quantum Yang--Baxter classification is that one constant
  one-particle basis makes `S` diagonal scattering behind the tensor flip.  This is not a theorem:
  the required map between the operator-algebraic scattering convention and the spin-chain
  quantum-`R` convention has not been derived, and the `O(N)` benchmark disproves the corresponding
  dimension-independent inference.

## Promotion blocker: the `O(N)` convention benchmark

The Alazzawi--Lechner `O(N)` factorizing S-matrix is positive-unitary, satisfies `S_N(0)=-F`, and
has intrinsic channel mixing through the invariant tensor structures `K`, `I`, and `P`.  It is not
constant-product-basis diagonal scattering.  Therefore any convention map that sends the physical
problem to an identity-anchored quantum classification and then derives diagonality must either:

1. reproduce the `O(N)` family on the quantum-`R` side; or
2. prove and state an exact restriction that excludes it.

The provisional argument does neither.  Since the standard `O(N)` benchmark has at least three
internal states, it does not by itself refute the dimension-two candidate.  It does refute the
dimension-independent pointwise argument that motivated the candidate and shows that the current
placement of tensor flips, rapidity signs, and leg order is not established.  No classification
corollary may be promoted before this benchmark is passed.

## Proposed convention reduction to the nonregular quantum classification

The provisional map was

```text
R(theta)=-P S(theta).                                           (1)
```

and would send the fermionic zero condition to

```text
R(0)=I.                                                         (2)
```

Pointwise positive-metric unitarity would be preserved by this formula:

```text
R(theta)^*R(theta)
  =S(theta)^*P P S(theta)=I.                                   (3)
```

Those pointwise identities are not the missing step.  The open step is proving that `(1)` sends the
specific adjacent-leg, rapidity-difference Yang--Baxter equation used in operator-algebraic
scattering to the exact quantum Yang--Baxter equation and spectral convention classified by
de Leeuw--Posch.  A valid derivation must track every leg permutation and rapidity sign and must
reproduce the `O(N)` benchmark.  Until then, the phrases “regular”, “nonregular”, and
“identity-anchored” cannot be transported between the two literatures as though their conventions
were identical.

## Provisional exhaustion of the identity-anchored classification slice

Assuming the proposed convention map is correct, de Leeuw--Posch's claimed complete list of
analytic nonregular `4 x 4` quantum Yang--Baxter families can be filtered at a nonzero
scalar-identity base point.  The following table records that useful but conditional audit.

The full-rank list reduces as follows.

| Classification branch | Identity anchor | Positive-unitary consequence |
|---|---|---|
| `R^A` | Four arbitrary diagonal functions can all equal `1` at zero. | Already diagonal; projective HT is allowed only in relative diagonal phases. |
| `R^G` | `R=f_1 I+N` with `N` strictly upper triangular and `N(0)=0`. | If `N(theta) != 0`, the only eigenvalue is `f_1(theta)` and the matrix has a Jordan block.  A unitary matrix is diagonalizable, so `N=0`. |
| `R^H` | The identity anchor forces its constants `p=q=0`, leaving `R=I+c(f(u)-f(v))E_14`. | Every nonconstant member is nontrivial unipotent and non-diagonalizable, hence not unitary. |
| `R^{E'}` | Equal eigenvalues force `p=q=k` and kill its sole off-diagonal entry identically. | The branch collapses to a scalar identity family. |
| `R^E,R^F,R^I,R^J` | Their displayed equal-parameter eigenvalue ratios are not all `1`; `R^E` would require simultaneously `p=q=k` and `-pq=k^2`. | They cannot meet an invertible scalar-identity anchor. |
| `R^B,R^C,R^D` | Their constant spectra or trace exclude a nonzero scalar identity. | They do not enter the physical slice. |

All rank-one, rank-two, and rank-three branches are excluded by `(3)`.  The earlier referee
omission consisting of an identity-diagonal upper-triangular arbitrary-function family is covered
by `R^G`; the Jordan argument above is precisely why that omitted algebraic family does not reopen
the positive-unitary slice.

Constant similarity preserves eigenvalues, diagonalizability, and Jordan blocks, so within this
provisional quantum-`R` slice the nontrivial `R^G` and `R^H` representatives cannot be positive
unitary and only `R^A` survives.  This would prove the candidate if the physical-to-quantum
convention map and classification completeness were both established.  It does not presently
prove a statement about operator-algebraic factorizing S-matrices.

## Conditional conclusion: projective HT would survive, intrinsic mixing would not

The candidate is not a no-go for HT itself.  In the provisionally surviving diagonal branch,

```text
R(theta)=diag(r_11(theta),r_12(theta),r_21(theta),r_22(theta)), (4)
S(theta)=-P R(theta),                                          (5)
```

and arbitrary projective ratios can be HT subject to the physical analytic, crossing, and
unitarity constraints.  The proved two-species compact-local control is exactly of this type.

The conjectured impossible conjunction is

```text
dim V=2,
positive-metric unitarity,
Yang--Baxter,
S(0)=-P,
no constant U tensor U diagonal reduction.                     (6)
```

No such obstruction has yet been proved.

## Conditional physical consequence

The known Alazzawi--Lechner modular-nuclearity theorem uses a fermionic zero to obtain the analytic
intertwiner and effective Pauli principle.  If the two-state candidate were proved, a physically
mixing projective-HT model using that compact-local route would require more than two one-particle
internal states.  The `O(N)` countercheck shows that no general dimension jump follows from the
current argument.

There is one logically distinct escape.  A two-state positive-unitary intrinsically mixing family
may live in another zero-rapidity sector, but then the existing fermionic intertwiner theorem does
not apply and compact locality requires a new intertwiner or a different reconstruction theorem.
The candidate does not treat `S(0)=-P` as a universal physical axiom.

Only after the convention lemma and two-state classification audit pass would the construction
program split as follows:

```text
Route I:  dim V >= 3, retain S(0)=-P and the known locality machinery;
Route II: dim V = 2, change the zero sector and build new locality machinery.  (7)
```

## Anti-theatre attacks

1. **A spin-chain convention imported by notation.**  This is the live failure.  The operator-level
   map has not been derived and fails the `O(N)` benchmark in its presently inferred form.
2. **The arbitrary-function triangular classes advertised as physical HT mixing.**  Their
   nontrivial members have Jordan blocks and cannot be unitary in any positive metric.
3. **A diagonal conclusion advertised as absence of HT.**  False.  The diagonal class supports
   projective HT and already has a compact-local realization.
4. **`S(0)=-P` advertised as mandatory physics.**  False.  It is the load-bearing hypothesis of
   the current compact-local intertwiner route; another zero sector is a valid but different lane.
5. **A classification corollary advertised as established.**  False.  Both the convention map and
   completeness audit are open.
6. **A dimension-independent commutative-Schmidt argument.**  False in the physical scattering
   convention: applying it to `O(N)` would contradict a standard positive-unitary mixing model.

## Novelty gate

De Leeuw--Posch list the nonregular families and explicitly leave their physical properties for
future study.  Their paper does not state the positive-unitary scalar-identity corollary above.
Focused searches for `S(0)=-P 4 x 4 unitary diagonal`, `two species factorizing S-matrix diagonal
no-go`, and `nonregular Yang--Baxter positive unitary scattering` found no explicit theorem.

However, Sogo--Uchinami--Akutsu--Wadati already classified two-component factorization equations in
1982.  That parent must be checked formula by formula before any novelty claim.  The current status
is therefore negative search evidence only, not a novelty certificate.

Significance is conditional.  A valid theorem would remove an entire two-state construction lane;
the present conjecture does not.  Novelty and significance gates are both therefore open.

## Exact open core

1. Derive the operator-level map from the Alazzawi--Lechner factorizing-scattering equation to the
   de Leeuw quantum Yang--Baxter convention, including rapidity signs, leg order, and every
   placement of `P`.
2. Reproduce the `O(N)` family under that map and identify exactly why the provisional
   identity-anchored diagonal inference does not apply to it.
3. Only then audit every identity-anchored full-rank class in the final de Leeuw--Posch version,
   including the repaired referee omissions, for the exact two-state physical slice.
4. Check the 1982 two-component factorization classification for an equivalent corollary.
5. Seek a classification-free dimension-two theorem only after its convention is benchmarked.
6. Independently continue the physical intrinsically mixing projective-HT construction without
   assuming a state-dimension lower bound.

## Lean boundary

No Lean edit is justified.  The load-bearing convention map is open.  Formalizing a pointwise
matrix lemma before that map passes `O(N)` would certify the wrong theorem surface.

## Primary literature

- M. de Leeuw and V. Posch, *All `4 x 4` solutions of the quantum Yang--Baxter equation*,
  <https://arxiv.org/abs/2411.18685>.
- L. Corcoran and M. de Leeuw, *All regular `4 x 4` solutions of the Yang--Baxter equation*,
  <https://arxiv.org/abs/2306.10423>.
- K. Sogo, M. Uchinami, Y. Akutsu, and M. Wadati, *Classification of Exactly Solvable
  Two-Component Models*, <https://doi.org/10.1143/PTP.68.508>.
- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>.

## Gates

- [ ] operator-algebraic scattering / quantum-`R` convention aligned
- [ ] `O(N)` benchmark reproduced under the convention map
- [ ] physical zero condition validly converted to the classified quantum anchor
- [x] pointwise positive unitarity preserved by the proposed multiplication by `-P`
- [x] all displayed full-rank nonregular classes filtered at the identity anchor
- [x] triangular arbitrary-function branches killed by Jordan structure
- [x] provisional diagonal projective-HT survival stated explicitly
- [ ] two-state positive-unitary intrinsic-mixing no-go
- [ ] state-dimension bifurcation
- [ ] independent audit of final classification completeness
- [ ] 1982 parent-theory novelty audit
- [ ] classification-free proof
- [ ] three-state physical intrinsically mixing projective-HT construction
- [ ] compact-local reconstruction
