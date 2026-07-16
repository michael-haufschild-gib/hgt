# Geometric Taylor Magnitudes: Torsion-Language Hypertranscendence and the Level-Exactness Law

- **ID:** `geometric-taylor-magnitude-torsion-language-hypertranscendence`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM CANDIDATE / GEOMETRIC-FACE HT LAW + EXACT-BEND STRUCTURE LAW
- **Scientific status:** `[PROVED HERE] [LEAN-PARTIAL] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** On every asymptotically exact geometric log-magnitude profile
  `-log|a_n|=A lambda^n+c_n` with `c_n` convergent and arbitrary `lambda>1`, torsion-language
  universal phases force hypertranscendence over `C(z)`; on the exact profile with eventually
  periodic phases, every valuation level of every integer-ADE coefficient identity must vanish
  identically.

## Lean audit status

- **Theorem A and its TLU-collapse corollary are unconditional.** The formal chain constructs the
  balanced survivor, confines every active atom to a finite geometric window, extracts the least
  face, proves its normalized cancellation, and applies torsion-language character separation.
  The final declarations are
  `hypertranscendental_of_geometric_torsionLanguageUniversal` and
  `hypertranscendental_of_eventually_geometric_torsionLanguageUniversal` in
  `GeometricTorsionLanguageCompletion.lean`.
- **Theorem B and its two corollaries are not yet formalized at the source-faithful surface.** The
  current `GeometricPeriodicLevelInput` merely receives the level-polynomial convergence that the
  paper proof must construct from the ADE coefficient identity. It is retained only as a generic
  compatibility lemma and does not satisfy the unconditional Stage-3 gate.
- **Pipeline decision:** keep this card in `2-fully-proven/needs-audit` until the exact periodic
  level cascade is constructed from the integer ADE and both corollaries are derived from it.

## Goal

Close the one escape that the DA log-ratio algebraicity law explicitly left alive. That law proves
that a DA full-support series with `b_(n+1)/b_n -> lambda in (1,infinity)` forces `lambda`
algebraic, and its boundary section records: "a pure algebraic geometric profile `b_n=A lambda^n`
has many exact shift resonances and passes this necessary test, but may still be HT." No
magnitude-side law can reach it, because for algebraic `lambda` the required logarithmic-width
shift resonances exist exactly. The missing constraint is phase-sensitive. This card supplies it in
two forms: a maximal-recurrence phase law (Theorem A) and an exact structure law for the structured
periodic phase class (Theorem B).

Both results are instances of one mechanism, isolated here as a reusable lemma: whenever the
magnitude profile makes the dominant ADE face **lock** — the normalized weight-valuation vector of
the finitely many face atoms converges along all large balanced indices, independently of the
phases — then recurrent finite torsion phase words exactify the exponential bend inequality into
identical vanishing of the face, and finite character separation destroys the face entirely.

## Setup

Let

`f(z)=sum_(n>=0)a_nz^n`,

`u_n=a_n/|a_n|` for `a_n!=0`, and `b_n=-log|a_n|`. Torsion-language universality `(TLU)` is the
phase condition of `torsion-universal-phase-polynomial-magnitude-hypertranscendence.md`: for every
`m>=1`, every finite word over `mu_m={zeta:zeta^m=1}` occurs as a block `u_(q+j)=zeta_j`,
`0<=j<ell`, at arbitrarily large positions `q`.

Throughout, `[PROVED]` inputs reused from the sibling cards:

1. **Mahler normalization** (Mahler 1971): a series DA over `C(z)` satisfies some nonzero
   `P in Z[z,Y_0,...,Y_m]` with `P(z,f,f',...,f^(m))=0`.
2. **Generic extraction:** for the generic series `F=sum X_nz^n`, `[z^N]P(z,F,...,F^(m))
   =sum_(nu)c_(N,nu)X^nu` with nonzero integer grouped weights; the number of atoms and the
   absolute values of the weights are bounded by `C_P(N+2)^(C_P)`.
3. **Balanced survival** (`log-superlacunary-taylor-magnitude-hypertranscendence.md`, Step 1):
   with `D` the top `Y`-degree of `P`, for every residue class of `N` modulo `D` there is a fixed
   integer offset pattern `delta_1,...,delta_D` and a nonzero polynomial `q|->W(q+delta_1,...,
   q+delta_D)` realizing, for every large `N` in the class, a nonzero grouped degree-`D` atom with
   all source indices in `[N/D-B,N/D+B]`.
4. **Grouped weights of fixed offset patterns are integer-valued polynomials in `q`** (same card,
   equation (8): symmetrized falling factorials divided by multiplicities, summed over the finitely
   many differential monomials of one shift; atoms from distinct shifts have distinct source sums,
   hence distinct multisets, so no cross-shift grouping occurs).

For a multiset `A` of integer offsets (multiplicity vector `m_A:Z->{0,...,D}`, degree
`d_A=sum_r m_A(r)`), write

`S_lambda(A)=sum_r m_A(r)lambda^r`,

`Phi_A(q)=product_r u_(q+r)^(m_A(r))`,

`chi_A(s)=product_r s_r^(m_A(r))` for a phase state `s=(s_r)`.

## Theorem A — geometric TLU hypertranscendence `[PROVED HERE]`

Fix `A>0`, a real `lambda>1`, and a convergent real sequence `(c_n)`, `c_n->c`. Suppose
`a_n!=0` for all `n>=n_0` and

`b_n=A lambda^n+c_n` for `n>=n_0`.                                          `(GEO)`

If the phase tail `(u_n)` is torsion-language universal, then `f` is entire and HT over `C(z)`.

No arithmetic condition is placed on `lambda`. For transcendental `lambda` the statement is already
phase-uniform by the log-ratio algebraicity law; the new content is the algebraic case, where exact
integer shift resonances exist and every previously proved magnitude-side law is passed.

### Proof

Entirety: `b_n/n->infinity`. Subtracting the Taylor prefix below `n_0` changes `f` by a polynomial
and neither DA status nor any hypothesis; so assume `a_n=0` for `n<n_0` and `a_n!=0`, `b_n>0` for
`n>=n_0` (enlarging `n_0` absorbs finitely many indices where `A lambda^n+c_n<=0`).

Suppose `f` is DA and fix the integer-normalized `P`, its top `Y`-degree `D>=1`, and the generic
extraction (input 2). Atoms containing a source index `<n_0` vanish after substitution and are
discarded. Fix a residue `tau modulo D` and write `N=Dq+tau`; `q` runs over all large integers.

**Step 1 — confinement at exponential scale.** Choose `1<mu<lambda<Lambda`; by `(GEO)`,
`mu<=b_(n+1)/b_n<=Lambda` for all large `n`. Every atom of the identity at index `N` has source sum
`N+c'` for a shift `c'` in a fixed finite set.

- *Lower degree.* For `D>=2`, an atom of degree `d<D` has largest source index at least
  `(N-O_P(1))/(D-1)`, so its valuation is at least `b` at that index, which exceeds
  `A lambda^(N/(D-1)-O_P(1))/2`. The balanced witness (input 3) has valuation at most
  `D b_(q+B)<=2DA lambda^(q+B)`. The gap grows like `lambda^(N/(D-1))`, hence is
  `>= eta lambda^q` eventually. For `D=1`, degree-zero atoms occur at finitely many `N` only.
- *Unbalanced degree `D`.* Fix `B'` with `lambda^(B'-B)>4D`. An atom whose largest index is
  `q+s`, `s>B'`, has valuation at least `b_(q+s)>=A lambda^(q+B')/2>=2DA lambda^(q+B)`, again a gap
  `>=eta lambda^q` against the witness. The source sum then bounds all its indices into
  `[q-K,q+K]` with `K=(D-1)B'+O_P(1)` for every surviving atom.

Hence there are `eta>0` and `K` such that, for all large `q`, every atom that is not a degree-`D`
multiset of offsets in `[-K,K]` has valuation exceeding the balanced witness by at least
`eta lambda^q`.

**Step 2 — the locked face.** Call a fixed offset multiset `A` (degree `D`, offsets in `[-K,K]`,
source sum compatible with one shift) **admissible** if its grouped weight `w_A(q)` (input 4) is
not the zero polynomial. The admissible set `W_tau` is finite and nonempty (input 3: the balanced
survival pattern is admissible). For `A in W_tau`,

`V(A;q)=sum_r m_A(r)b_(q+r)=A lambda^q S_lambda(A)+sum_r m_A(r)c_(q+r)`,

and `sum_r m_A(r)c_(q+r)->Dc`. Let `S_1=min{S_lambda(A):A in W_tau}` and define the **face**

`F_tau={A in W_tau : S_lambda(A)=S_1}`.

For `A,A' in F_tau`, `V(A;q)-V(A';q)=sum_r(m_A-m_(A'))(r)c_(q+r)->0` because both degrees are `D`
and `c_n` converges. For `A in W_tau\F_tau`, `V(A;q)` exceeds the face valuations by
`A(S_lambda(A)-S_1)lambda^q-O(1)>=eta'lambda^q`. Combined with Step 1: with
`V_*(q)=min_(A in F_tau)V(A;q)` and `delta_A(q)=V(A;q)-V_*(q)`,

- `delta_A(q)->0` for every `A in F_tau`;
- every non-face atom of the whole identity has valuation `>=V_*(q)+eta''lambda^q`.

Let `H=max{deg w_A:A in F_tau}` and `ell_A=lim_(q->infinity)q^(-H)w_A(q)`; some `A_0 in F_tau` has
`ell_(A_0)!=0`. Multiplying the coefficient identity by `exp(V_*(q))q^(-H)` gives, for all large
`q`,

`|sum_(A in F_tau)q^(-H)w_A(q)e^(-delta_A(q))Phi_A(q)|
   <= C_P(N+2)^(C_P)q^(-H)e^(-eta''lambda^q)`.                               `(A1)`

The left factors `q^(-H)w_A(q)e^(-delta_A(q))` converge to `ell_A`, independently of all phases:
the face is locked.

**Step 3 — torsion exactification.** Fix `m=D+1` and an arbitrary state
`s in mu_m^({-K,...,K})`. By `(TLU)` there are `q_j->infinity` with `u_(q_j+r)=s_r` for `|r|<=K`;
then `Phi_A(q_j)=chi_A(s)` for every `A in F_tau`. Taking `q=q_j` in `(A1)` and `j->infinity`:

`sum_(A in F_tau)ell_A chi_A(s)=0 for every s in mu_m^({-K,...,K})`.        `(A2)`

**Step 4 — character separation.** Distinct `A in F_tau` have distinct multiplicity vectors with
entries in `[0,D]`; since `m=D+1>D`, they restrict to distinct characters of the finite abelian
group `mu_m^({-K,...,K})`. Averaging `(A2)` against `chi_(A_0)` (finite Fourier inversion, or
linear independence of distinct characters) gives `ell_A=0` for every `A`, contradicting
`ell_(A_0)!=0`. Hence no `P` exists and `f` is HT. `square`

### Corollary — TLU collapse of the geometric column `[PROVED HERE]`

On torsion-language-universal phase fibers, no asymptotically exact geometric log-magnitude
profile is DA-compatible, for any ratio `lambda>1`. Combined with the log-superlacunary theorem
(`lambda=infinity`, phase-uniform), the transcendental-ratio law (phase-uniform), and the
polynomial and Gaussian torsion theorems at ratio one, the DA extended-ratio spectrum
`{1} union {algebraic lambda>1}` collapses, on TLU fibers of asymptotically exact profiles, to the
empty set above ratio one: every surviving DA candidate must have `b_(n+1)/b_n->1`.

## Theorem B — level-exactness for periodic phases `[PROVED HERE]`

Suppose `b_n=A lambda^n+c` exactly for `n>=n_0` (`A>0`, `lambda>1`, `c in R`), `a_n!=0` for
`n>=n_0`, and the phases are eventually periodic: `u_(n+p)=u_n` for all `n>=n_1`. If `f` satisfies
a nonzero integer ADE `P` with top `Y`-degree `D`, then for every residue `tau` of `N` modulo `D`,
every residue `sigma` of `q` modulo `p`, and every value `v` of `S_lambda` on admissible fixed
offset multisets, the level polynomial identity

`sum_(A admissible, S_lambda(A)=v) w_A(q)e^(-c d_A)Phi_A^(sigma)=0`         `(B1)`

holds for all sufficiently large `q === sigma (mod p)` — identically, not merely up to
exponentially small error. Here `Phi_A^(sigma)` is the constant value of `Phi_A(q)` on the residue
class, and admissibility now ranges over all degrees `d_A<=D`, all shifts, and all fixed offset
windows.

The bend law is thereby strengthened, on this stratum, from "two atoms within `O(log N)`" to
"every bend is an exact tie and every tied level cancels identically."

### Proof

Prefix subtraction and `n_0` as in Theorem A. Fix `tau` and `sigma`; along `q === sigma (mod p)`
with `q-K>=n_1`, every window phase `u_(q+r)` is a constant `s_r^((sigma))`, so each `Phi_A(q)` is
a constant `Phi_A^((sigma))` and each level sum in `(B1)` is a polynomial in `q` with fixed complex
coefficients.

**Finiteness of levels below a threshold.** Fix `Vbar>0` and consider atoms of degree `d` with
source sum `N+c'`. For `d<D` the offset sum is `(D-d)q+O(1)`, so the largest offset is at least
`(D-d)q/d-O(1)` and `S_lambda>= lambda^((D-d)q/d-O(1))->infinity`; such atoms eventually exceed
every threshold. For `d=D` the offset sum is `O(1)`; if one offset is `<=-t`, another is
`>=(t-O(1))/(D-1)`, so `S_lambda>=lambda^((t-O(1))/(D-1))`. Hence the patterns with
`S_lambda<=Vbar` all have offsets in a fixed window `[-K(Vbar),K(Vbar)]` and form a finite set; the
values of `S_lambda` below `Vbar` form a finite set `v_1<v_2<...<v_k<=Vbar`.

**Exact grading.** On the exact profile, a degree-`d` atom with offset multiset `A` has valuation
exactly

`V(A;q)=A lambda^q S_lambda(A)+c d_A`.

Two atoms in the same level `S_lambda=v` have valuations differing by the constant `c(d_A-d_(A'))`;
two atoms in distinct levels `v<v'` differ by `A(v'-v)lambda^q-O(1)`. Every atom with
`S_lambda>Vbar` — including every lower-degree atom, for large `q` — has valuation at least
`A Vbar' lambda^q(1-o(1))` where `Vbar'=min(S_lambda over patterns exceeding the threshold)>v_k`.

**Induction over levels.** Order the levels below `Vbar` increasingly. Assume the level identities
`(B1)` hold identically for all levels `<v_i` (vacuous for `i=1`). Multiply the coefficient
identity at `N=Dq+tau` by `exp(A v_i lambda^q)`. The levels `<v_i` contribute exactly zero by the
inductive hypothesis; the levels `>v_i` and the beyond-threshold atoms contribute at most
`C_P(N+2)^(C_P)exp(-A(v_(i+1)-v_i)lambda^q(1-o(1)))`. Writing `P_i(q)` for the level-`v_i`
polynomial in `(B1)`,

`|P_i(q)| <= C_P(N+2)^(C_P)exp(-A(v_(i+1)-v_i)lambda^q(1-o(1))) -> 0`

along the infinite sequence `q === sigma (mod p)`. A polynomial whose values tend to zero along an
infinite integer sequence is the zero polynomial: a nonconstant complex polynomial has
`|P(q)|->infinity`, and a constant one equals its limit. Hence `P_i=0` identically. Induction over
`i`, then over arbitrary `Vbar`, proves `(B1)` for every level. `square`

### Corollaries `[PROVED HERE]`

1. **Singleton levels kill.** If any admissible level of any residue pair is a singleton `{A}`,
   then `(B1)` forces `w_A=0`, contradicting admissibility. Hence a DA realization requires every
   admissible level to contain at least two exactly tied patterns. A tie between distinct multisets
   `A!=A'` with `S_lambda(A)=S_lambda(A')` gives a nonzero integer Laurent polynomial
   `Q=sum_r(m_A-m_(A'))(r)T^r` with `Q(lambda)=0`. In particular `lambda` is algebraic — recovering
   the log-ratio algebraicity law on this stratum with an exact, not merely logarithmic, resonance.
2. **The surviving obstruction is purely algebraic.** For algebraic `lambda`, DA-compatibility of
   the exact geometric profile with an eventually periodic phase word forces the finite system of
   polynomial identities `(B1)` — integer-valued weight polynomials against fixed unimodular
   constants — for every residue pair and every level. All analysis is discharged; what remains is
   an exact solvability question for the `lambda`-graded tropicalization of a single integer ADE.
   This is an Archimedean-graded analogue of non-Archimedean tropical differential algebra, and it
   is the exact persistent-bend question on this stratum: bends must persist *exactly*, level by
   level, at every scale.

## Boundary attacks

1. **Bare ratio convergence is not enough for Theorem A.** Under `b_(n+1)/b_n->lambda` alone, the
   face defects are `b_q o(1)` and can oscillate unboundedly; the normalized face vector need not
   converge, and the per-state witnesses of `(TLU)` occur at state-dependent positions, so a common
   subsequential limit cannot be extracted. `(GEO)` is exactly the hypothesis that locks the face.
   The gap is structural, not technical: it is the same compactness failure that blocks the
   general convex TLU statement.
2. **The residue and shift bookkeeping is loss-free.** Patterns from distinct shifts have distinct
   source sums, hence distinct multisets; no grouping collision occurs, and each residue class of
   `N` is treated on its own face.
3. **Theorem B needs exactness only against the cascade.** The top level of Theorem B vanishes
   under `(GEO)` with `c_n->c` as well (this is `(A2)` restricted to the realized periodic states),
   but the inductive removal of a level requires the level to vanish exactly, which `o(1)`
   corrections destroy at the second level. Exactness (or corrections of size
   `O(exp(-eta lambda^n))` with `eta` large) is the honest hypothesis.
4. **Theorem B does not need root-of-unity phases.** Any unimodular eventually periodic word works:
   only constancy along residue classes is used, and the vanishing conclusion is a polynomial
   identity, not an algebraicity statement.
5. **Consistency with known DA objects.** Valiron's third-order order-zero DA function and all
   theta-type examples live at the Gaussian scale `b_n ~ cn^2`, far below `(GEO)`; nothing known
   contradicts either theorem. Wittich's HT canonical product with zeros `(lambda^n)` has
   `b_n ~ (log lambda)n^2/2` as well: the geometric *coefficient* scale of this card corresponds to
   doubly exponential zero radii, `n(r)=O(log log r)`, strictly inside the open divisor-floor
   regime `n(r)=o(log r)`.
6. **The theorems do not close the full geometric stratum.** Arbitrary (non-TLU, non-periodic)
   phases on the exact geometric profile remain open; Theorem B reduces the periodic fiber to
   algebra but does not yet refute it.

## Parent and novelty status

- The exactification mechanism (ADE face confinement + recurrent torsion words + finite character
  separation) is the project's own, from the polynomial and Gaussian torsion cards; no literature
  parent is known. The geometric instance is new: it is the first law of any kind that reaches the
  algebraic-ratio geometric profiles, which pass Popken/arithmetic tests (no arithmetic
  hypothesis), Valiron-Strelitz order walls (order zero), Lipshitz-Rubel gap theorems (full
  support), and the project's own magnitude-side resonance laws (exact resonances exist).
- The level-exactness law has the shape of an associated-graded/tropical statement, but the
  tropical differential literature (Garay-Lopez et al., arXiv:2606.21829) is non-Archimedean and
  local; the grading here is by Archimedean valuations `-log|a^nu|` of convolution atoms, and the
  vanishing is forced analytically by exponential level separation, not assumed. No parent theorem
  is known; novelty of both theorems remains provisional pending specialist review.
- Adamczewski-Dreyfus-Hardouin q-difference hypertranscendence and Hardouin-Singer Galois theory
  prove HT for solutions of *given* difference/differential systems; here no functional equation is
  assumed and the conclusion is uniform over a phase language.

Primary comparisons: the six sources of
`torsion-universal-phase-polynomial-magnitude-hypertranscendence.md`, plus S. B. Bank, Funkcial.
Ekvac. 23 (1980) (geometric-divisor HT examples at the Gaussian coefficient scale).

## Exact RH-route scope

This is a general coefficient law, not an RH theorem. It tightens the entire-complex-time heat
route boundary of the parent conjecture: an implementation whose multiplicative anchor has
asymptotically exact geometric Taylor log-magnitudes and a torsion-universal (or, for the exact
profile, eventually periodic with a refuted level system) phase tail cannot factor through a finite
ADE. It supplies no operator, positivity, or zero-location statement, and it does not constrain
routes that never compress into a finite differential constraint.

## Lean status

The full implication surface is formalized in
`formal/GaloisForLFunctions/HTGeometry/GeometricTorsionLanguageCompletion.lean`, using the existing
`TorsionFaceExactification.lean` and `DATaylorLogRatioResonance.lean` theorems.

```text
GeometricTLULockedFaceInput
  -- exact Mahler/balanced-survival/geometric-confinement output: a nonzero locked face whose
  -- character sum vanishes on every torsion state under a hypothetical ADE
hypertranscendental_of_geometricTLU_lockedFace
  -- internal torsion Fourier inversion forces every face weight to vanish, contradiction
GeometricPeriodicLevelInput
geometricPeriodic_everyLevelPolynomial_eq_zero
geometricPeriodic_no_nonzero_level
  -- every exact periodic valuation-level polynomial vanishes identically; singleton levels kill
geometricProfile_da_forces_algebraic_ratio
  -- checked magnitude-side algebraicity corollary
```

The analytic confinement chain is an explicit named structure, not an axiom. The contradiction,
torsion character separation, every-level exactness, singleton-level corollary, and algebraic-ratio
corollary are checked internally. The module passed one exact targeted build when its `.olean` was
absent and direct single-file verification.

## Gates

- [x] `0 -> 1`: exact statements, locked-face mechanism, and level grading identified.
- [x] `1 -> 2`: complete unconditional paper proofs of Theorems A and B, boundary-attacked.
- [ ] Parent-theory and exact literature novelty audit.
- [ ] Independent proof audit.
- [x] Whole theorem surfaces formalized in Lean from the explicit analytic confinement input.

## Log

- 2026-07-11 — Proved geometric TLU hypertranscendence for every `lambda>1` via the locked-face
  exactification mechanism, closing the algebraic-ratio TLU fiber left open by the log-ratio
  algebraicity law.
- 2026-07-11 — Proved the level-exactness law for exact geometric profiles with eventually
  periodic phases: every valuation level of every integer-ADE coefficient identity vanishes
  identically; the periodic fiber reduces to an exact algebraic solvability question for the
  `lambda`-graded ADE.
- 2026-07-11 — Formalized the finite exactification engine and the polynomial level-vanishing
  step in `GaloisForLFunctions.TorsionFaceExactification`, axiom-clean.
