# Source-localization modular-defect conservation law

- **ID:** `source-localization-modular-defect-conservation-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / UNIVERSAL CONJECTURE / RH REDUCTION
- **Source:** `prime-deleted-ht-divisor-frame-phase-tomography.md`;
  `source-effective-polar-kummer-conormal-purity.md`;
  `cofinal-conormal-picard-purity-law.md`;
  `adjoint-duality-cauchy-nerve-purity-law.md`
- **Scientific status:** `[ALL-PRIME DEFECT DICTIONARY PAPER-PROVED]`
  `[PRIME-INFINITY FLUX CARRIER PAPER-PROVED]`
  `[PRIME-FILTRATION MARTINGALE DEFECT PAPER-PROVED]`
  `[CHAINWISE WOLD-KUMMER TRANSMUTATION PAPER-PROVED]`
  `[FULL PRIME-NERVE STRICT-LINEARIZATION RIGIDITY PAPER-PROVED]`
  `[FIRST-DEFECT MARKOV LIOUVILLE LAW PAPER-PROVED]`
  `[XI MARKOV HARMONICITY RH REDUCTION]`
  `[UNIVERSAL CONSERVATION LAW CORPUS-KNOWN]` `[NOT RH]`
- **Statement:** Prime-resolved HT-shell likelihood, Kummer degree, Kakutani sector change,
  BV dilation orientation, and cofinal source leakage are coordinates of one real modular defect.
  Universally, this conormal defect should equal source-degree flux lost at the completion
  boundary.  RH follows from the Xi-specific theorem that the ordinary-integer source has zero
  such flux.

## Goal

Replace the collection of critical-line selectors by one invariant and one producer problem.
The invariant must be computed before choosing a topology fitted to a zero.  The producer must be
one global source map constructed before divisor specialization; fibrewise boundedness,
positivity, or a zero-indexed norm does not count.

The proposed change of interpretation is:

```text
critical line
  is not primarily a positivity locus;
  it is the zero-anomaly locus for completion versus conormal localization.
```

Finite stages commute.  At the all-prime boundary they can fail to commute because source degree
escapes to prime infinity.  The horizontal displacement of a divisor point is the complete
modular class of that failure.

## 1. Prime-resolved shell theorem

For a rational prime \(p\), let
\[
 \zeta_p(s)=\prod_{\ell\geq p}(1-\ell^{-s})^{-1},
 \qquad
 H_{p,m}(s)
 =
 {1\over\zeta_p((m+1)s)}-{1\over\zeta_p(ms)}.
 \tag{1}
\]
The prime-deleted HT-frame theorem proves, normally on compact subsets of
\(\operatorname{Re}s>0\),
\[
 H_{p,m}(s)
 =
 p^{-ms}(1-p^{-s})
 +O_{p,s}\!\left((p^+)^{-m\operatorname{Re}s}\right),
 \tag{2}
\]
where \(p^+\) is the next prime.  At the positive source point put
\[
 h_{p,m}=H_{p,m}(1)>0.
 \tag{3}
\]
Specializing `(2)` at \(s=1\) gives
\[
 h_{p,m}
 =
 p^{-m}(1-p^{-1})+O_p((p^+)^{-m}).
 \tag{4}
\]

`[PROVED HERE] [PRIME_RESOLVED_SHELL_KUMMER_RADIAL_IDENTITY]`

For every \(p\) and every fixed \(s\) with \(\operatorname{Re}s>0\),
\[
 \boxed{\quad
 \lim_{m\to\infty}{1\over m}
 \log {\,|H_{p,m}(s)|\over\sqrt{h_{p,m}}}
 =
 \left({1\over2}-\operatorname{Re}s\right)\log p.
 \quad}
 \tag{5}
\]
Equivalently,
\[
 \lim_{m\to\infty}{1\over m\log p}
 \log {|H_{p,m}(s)|^2\over h_{p,m}}
 =
 1-2\operatorname{Re}s.
 \tag{6}
\]

### Proof

Because \(\operatorname{Re}s>0\), one has \(|p^{-s}|<1\), so
\(1-p^{-s}\neq0\).  The ratio of the error in `(2)` to its leading term tends
to zero exponentially.  The same holds in `(4)`.  Therefore
\[
 {H_{p,m}(s)\over\sqrt{h_{p,m}}}
 =
 {1-p^{-s}\over\sqrt{1-p^{-1}}}\,
 p^{-m(s-1/2)}(1+o(1)).
 \tag{7}
\]
Taking absolute values, logarithms, and dividing by \(m\) proves `(5)`;
doubling and dividing by \(\log p\) proves `(6)`.

The theorem is not a new zero selector.  Its content is that the previously dyadic shell
likelihood rate is an all-prime coherent character, with exactly the Kummer normalization at every
prime.

## 2. One modular defect

Define
\[
 c(s)={1\over2}-\operatorname{Re}s
 \tag{8}
\]
and the real character
\[
 \mathfrak d_s:\mathbb Q_{>0}^{\times}\longrightarrow\mathbb R,
 \qquad
 \mathfrak d_s(q)=c(s)\log q.
 \tag{9}
\]
Then \(\mathfrak d_s\) is a group homomorphism, and `(5)` says that its prime
coordinates are the source-normal HT-shell slopes:
\[
 \mathfrak d_s(p)
 =
 \lim_{m\to\infty}{1\over m}
 \log {|H_{p,m}(s)|\over\sqrt{H_{p,m}(1)}}.
 \tag{10}
\]
Reflection \(s^\#=1-\overline s\) gives
\[
 \mathfrak d_{s^\#}=-\mathfrak d_s.
 \tag{11}
\]

The existing corpus theorems give the following exact dictionary.

| Realization | Value or zero law |
|---|---|
| prime-resolved positive HT shell | slope \(\mathfrak d_s(p)\) by `(10)` |
| ordinary maximum-exponent shell | squared likelihood rate \(2c(s)\) |
| Kummer place contrast | \(\langle h,f_p\rangle=c(s)\log p\) |
| prime-valuation Kakutani sector | source-internal exactly when \(c(s)=0\) |
| BV forward/inverse residue orientation | \(-2\sinh(2c(s)\log r)\) times positive residue mass |
| irregular/Stokes radial type | real part \(-2c(s)\) |
| cofinal finite Kummer regulator | nonzero \(L^1\) source-memory defect exactly when \(c(s)\neq0\) |
| source-normal Picard line | internally invertible in critical sector exactly when \(c(s)=0\) |

Thus these are not independent criteria.  They are nonlinear or completed readings of
\(\mathfrak d_s\).  Functional-equation reflection changes its sign, while reflected products,
determinants, and two-chiral scalar completions add the two signs and erase it.

## 3. The defect is a literal boundary measure

The phrase “flux at prime infinity” has a canonical model on the proved coherent finite Kummer
regulators; it need not be introduced as an analogy.

Let \(\mathcal P\) be the discrete set of rational primes, let
\(\mathcal P^\dagger=\mathcal P\sqcup\{\infty_{\mathcal P}\}\) be its one-point compactification,
and let
\[
 K=\{\infty_{\rm ar}\}\sqcup\mathcal P^\dagger.
 \tag{11a}
\]
For a finite prime set \(P\), \(n=|P|\), define the signed place-average measure
\[
 \nu_{P,c}
 =
 {nc\over n+1}\delta_{\infty_{\rm ar}}
 -
 {c\over n+1}\sum_{p\in P}\delta_p.
 \tag{11b}
\]
This is exactly the component-average record of the regulator \(h_{P,c}\).  In particular,
\[
 \nu_{P,c}(K)=0,
 \qquad
 \|\nu_{P,c}\|_{\rm TV}={2n\over n+1}|c|.
 \tag{11c}
\]

`[PROVED HERE] [CANONICAL_PRIME_INFINITY_FLUX_MEASURE]`

For every increasing exhaustion \(P_1\subset P_2\subset\cdots\) of the rational primes with
\(|P_n|=n\),
\[
 \boxed{\quad
 \nu_{P_n,c}
 \overset{*}{\rightharpoonup}
 c\delta_{\infty_{\rm ar}}
 -
 c\delta_{\infty_{\mathcal P}}
 \quad\text{in }M(K).
 \quad}
 \tag{11d}
\]
The limit is independent of the order of the prime exhaustion, has total mass zero, and has total
variation \(2|c|\).

### Proof

Let \(F\in C(K)\).  If the new prime in the exhaustion is denoted \(p_j\), continuity at the
one-point compactification means
\[
 F(p_j)\longrightarrow F(\infty_{\mathcal P}).
\]
Cesàro convergence gives
\[
 {1\over n+1}\sum_{j=1}^nF(p_j)
 \longrightarrow F(\infty_{\mathcal P}).
\]
Since \(n/(n+1)\to1\), pairing `(11b)` with \(F\) gives
\[
 \int_KF\,d\nu_{P_n,c}
 \longrightarrow
 cF(\infty_{\rm ar})-cF(\infty_{\mathcal P}),
 \tag{11e}
\]
which is `(11d)`.  The two limiting atoms are distinct, so their total variation is \(2|c|\).

`[PROVED HERE] [PRIME_INFINITY_COMPLETION_TRICHOTOMY]`

Let
\[
 \nu_{\infty,c}
 =
 c\delta_{\infty_{\rm ar}}
 -
 c\delta_{\infty_{\mathcal P}}.
\]
Then
\[
 \boxed{\quad
 \|\nu_{P_n,c}-\nu_{\infty,c}\|_{\rm TV}=2|c|
 \quad\text{for every }n.
 \quad}
 \tag{11f}
\]
Indeed, the difference has masses
\[
 -{c\over n+1}\text{ at }\infty_{\rm ar},\qquad
 -{c\over n+1}\text{ at each }p\in P_n,\qquad
 c\text{ at }\infty_{\mathcal P},
\]
whose absolute values sum to \(2|c|\).  Hence weak-* boundary convergence upgrades to strict
total-variation convergence exactly when \(c=0\).

Define
\[
 M_0(K)=\{\mu\in M(K):\mu(\{\infty_{\mathcal P}\})=0\}.
 \tag{11g}
\]
This is a closed subspace in total variation, and boundary mass induces an isometric
one-dimensional quotient
\[
 M(K)/M_0(K)\simeq\mathbb C,
 \qquad
 [\mu]\longmapsto\mu(\{\infty_{\mathcal P}\}).
 \tag{11h}
\]
The coherent conormal family has quotient class \(-c\).  Thus “diffusion of dualizable charge” has
one exact coordinate, rather than only a qualitative failure of compactness.

This theorem explains the all-\(L^q\) wall exactly:

```text
bare L^q, q>1:
  shrinking finite-place densities converge strongly to zero;
  only the archimedean atom remains, so degree is not closed;

bare L^1 on the uncompactified place set:
  the escaping mass stays a fixed distance away, so no limit exists;

boundary-measure completion:
  both atoms survive and degree remains exactly zero.
```

Thus a Hausdorff completion can retain every off-line conormal without forcing RH.  It records the
failure as the coefficient of \(\delta_{\infty_{\mathcal P}}\).  The Xi theorem must prove that
the actual ordinary-source conormal has no such boundary atom; choosing a completion which merely
deletes the atom is not conservation.

For a divisor point \(s\), the shell theorem identifies
\[
 \operatorname{Flux}^{\rm shell}_\infty(s)
 =
 -c(s)\delta_{\infty_{\mathcal P}},
 \tag{11i}
\]
with prime coordinates recovered by `(10)`.  This is the first concrete realization of the
completion--localization modular class.

## 4. Abstract conservation theorem

### Corpus collision boundary

Section 25 of `adjoint-duality-cauchy-nerve-purity-law.md` already proves the parent categorical
consumer and formulates `XI_SOURCE_FROBENIUS_CARTIER_REALIZATION` under the headline
“dualizable arithmetic charge cannot diffuse.”  The abstract theorem below and the Xi
Frobenius/Beck--Chevalley conjecture are therefore **corpus-known**, not a new universal jump.

The new candidate contribution of this card is only:

1. all-prime, rather than dyadic, HT-shell identification `(5)`--`(10)`;
2. the canonical boundary dipole `(11d)`;
3. the exact weak/strict/collapsed completion trichotomy `(11f)`--`(11h)`;
4. identification of the prior qualitative “diffusion” with the one-dimensional
   prime-infinity boundary quotient.

Let \(\mathcal S_{\mathrm{fin}}\) be a finite-source symmetric monoidal category, let
\(\mathcal N\) be a principal conormal line with its evaluation--coevaluation triangle, and let
\[
 \operatorname{Loc}:\mathcal S_{\mathrm{fin}}\to\mathcal D_{\mathrm{fin}}
 \tag{12}
\]
be conormal localization.  Let \(\widehat{\mathcal S}_{\rm src}\) and
\(\widehat{\mathcal D}_{\rm src}\) be source completions whose internal radial lines are classified
by the mixed Kummer/Kakutani theorem.

`[ABSTRACT THEOREM] [DEPENDENCY-CLOSED GIVEN THE FUNCTORIAL HYPOTHESES]`

Assume:

1. source completion is strict and degree-continuous;
2. the completion--localization Beck--Chevalley map
   \[
    \widehat{\operatorname{Loc}}(\widehat{\mathcal N})
    \longrightarrow
    \widehat{\operatorname{Loc}(\mathcal N)}
    \tag{13}
   \]
   is an isomorphism;
3. `(13)` is strong monoidal on \(\mathcal N,\mathcal N^\vee\), so it preserves the literal
   evaluation--coevaluation triangle;
4. `(13)` is conservative on the top principal-conormal jet.

Then the completed conormal is an internal invertible line in the fixed source sector.  The
Kakutani/Picard classification forces its radial class to vanish:
\[
 \mathfrak d_{\mathcal N}=0.
 \tag{14}
\]

### Proof

The finite principal conormal and its dual satisfy the two triangle identities.  Strong
monoidality and `(13)` preserve those identities after source completion, while conservativity
prevents the line or its top jet from becoming zero.  Hence the image remains an internal
invertible object of the fixed completed source sector.  The proved cofinal Picard-purity theorem
classifies a coherent radial line with prime modulus \(p^c\) as internal in that sector exactly
when \(c=0\).  Therefore its character `(9)` is zero.

This theorem is formal category theory plus the existing Kummer/Kakutani classification.  It does
not establish any of the four hypotheses for the Xi source.

## 5. Defect--flux form of the corpus-known universal law

The first formulation of the law as automatic vanishing for every source-minimal HT object is
false.  Positive generalized-prime and Gamma--Gaussian property-\(S\) systems can carry arbitrary
off-line reflection packets through a source-built completion.  A universal law must retain their
nonzero anomaly rather than declare it zero.

`[REFORMULATION OF CORPUS CONJECTURE] [SOURCE_LOCALIZATION_MODULAR_DEFECT_FLUX_LAW]`

> For a source-minimal constrained hypertranscendental object, the modular character of a
> principal conormal after completion is exactly the source-degree flux through the cofinal
> boundary in the completion--localization square.  Equivalently, the failure of the
> Beck--Chevalley map `(13)` to preserve the source evaluation--coevaluation triangle is measured
> by one class
> \[
>  \operatorname{Flux}^{\rm src}_\infty
>  \in\operatorname{Hom}(\mathbb Q_{>0}^{\times},\mathbb R),
>  \qquad
>  \mathfrak d_{\mathcal N}
>  =
>  \operatorname{Flux}^{\rm src}_\infty.
>  \tag{15}
> \]
> Strict conservative same-sector base change is equivalent to zero flux.

This law permits generalized-prime countermodels: their off-line divisor is accompanied by
nonzero source flux.  What their functional equation erases is only the total reflected class
\(\mathfrak d+\mathfrak d^\#=0\), not either oriented flux.

For Xi the required arithmetic specialization is separate.

`[BOLD CONJECTURE] [XI_ORDINARY_SOURCE_MODULAR_FLUX_CLOSURE]`

> The ordinary-integer Poisson/co-Poisson--Wold--BV source has no modular degree flux at prime
> infinity in its source-normal Rees/nearby-cycle completion.  Its completion--principal-conormal
> Beck--Chevalley map is therefore strict, conservative, and same-sector monoidal on every
> multiplicity jet.

For Xi the source is fixed before a zero is read:

```text
ordinary-integer Poisson/co-Poisson incidence
  + nested coprime Wold sieve
  + BV first-trace principal normal
  + Gamma/Barnes regular boundary
  + Tate/Kummer integral interval
  + positive HT prime-deleted shell cofinal record.
```

The exact open theorem is to construct the flux class and `(13)` for this one pre-divisor object,
then prove its flux vanishes.  It must be strict under every finite-prime enlargement and every
positive HT-shell enlargement, retain all multiplicity jets, and land in the source
\(L^1\)/Kakutani sector without selecting or deleting fibres.

## 6. Conditional RH theorem

Assume `SOURCE_LOCALIZATION_MODULAR_DEFECT_FLUX_LAW` and
`XI_ORDINARY_SOURCE_MODULAR_FLUX_CLOSURE`.  Let \(\rho\) be a nontrivial zero.  The
BV/co-Poisson normal connection makes its top principal-conormal jet nonzero, including for
multiple zeros.  Its prime-deleted HT record has modular character \(\mathfrak d_\rho\) by `(10)`.
The defect--flux law and Xi flux closure give \(\mathfrak d_\rho=0\), hence
\[
 {1\over2}-\operatorname{Re}\rho=0.
\tag{16}
\]
Therefore every nontrivial zero lies on the critical line.

The implication is dependency-closed once the source law is proved.  At present the source law is
the complete RH-bearing open core.

## 7. New consequences of the interpretation

1. **Third completion is a square, not a space.**  Wold/Szegő, distributional, and Kummer
   receivers already supply kinematic critical completions.  Missing object is a conservative
   completion--localization comparison.  Inventing another ambient norm without `(13)` cannot
   address RH.
   The boundary-measure space `(11a)` is useful because it retains and displays the defect rather
   than silently imposing its vanishing.
2. **All \(L^q,\ q>1\), routes forget the invariant.**  The exact cofinal regulator theorem shows
   that every such completion absorbs nonzero \(c\) into the archimedean component.  Only a
   complete \(L^1\) place record, or an equivalent irregular/Kakutani invariant, can make `(13)`
   degree-continuous.
3. **Finite identities cannot decide RH.**  Every finite prime packet realizes every \(c\).
   The defect is the obstruction to uniform cofinal base change.
4. **Reflection explains pairing, not location.**  It sends \(\mathfrak d\) to
   \(-\mathfrak d\).  Any construction that multiplies, traces, or pushes the two orientations
   together before source completion annihilates the only horizontal invariant.
5. **Hypertranscendence is a noncensorship condition.**  It prevents the positive shell record
   from being compressed to finitely many differential-algebraic coordinates.  It does not
   supply the vanishing of \(\mathfrak d\).
6. **An off-line zero is an explicit anomaly certificate.**  It would produce the source flux
   \(q\mapsto(\tfrac12-\operatorname{Re}\rho)\log q\), a non-uniformly-integrable prime-deletion
   likelihood, a non-internal Kummer line, and a failure of `(13)` at the same conormal jet.
7. **Generalized-prime countermodels carry rather than refute the invariant.**  Their inserted
   off-line packets must carry the corresponding nonzero flux.  They show that positivity,
   functional equation, entire completion, property \(S\), and hypertranscendence do not imply
   flux closure.  Literal ordinary-integer incidence is load-bearing in the Xi specialization.

## 8. Hostile audit

1. The shell theorem `(5)` is an elementary consequence of an existing prime-deleted asymptotic.
   It is a new corpus weld, not claimed as standalone major novelty.
2. Calling \(\mathfrak d\) a modular defect does not prove the defect--flux identity or zero Xi
   flux.
3. The abstract theorem is useless without construction of `(13)` before zero specialization.
4. Fibrewise membership, boundedness, uniform integrability, or internality is RH-equivalent and
   is forbidden as a hypothesis replacing `(13)`.
5. A functor defined only on the divisor, a norm summed over zeros, or deletion of non-moderate
   fibres is circular.
6. A large enhanced target retaining all exponential characters makes `(13)` automatic but
   destroys `(14)`.
7. A small Hilbert target loses critical-line point fibres and violates conservativity.
8. A paired Chu/Krein completion can retain \(c\) and \(-c\) in different sectors; abstract
   duality alone is insufficient.  Same-source-sector monoidality is load-bearing.
9. The finite Wold occupation triangle is already proved.  Reproving it, or another local
   \(2\times2\) identity, does not advance `(13)`.
10. Generalized-prime packet surgery kills automatic-vanishing formulations of the universal law.
    Only defect--flux matching can be universal; zero flux is an arithmetic Xi theorem.
11. The Frobenius-monoidal/dualizable-charge law is already in the corpus.  Claiming it as the new
    jump would be rediscovery.  Only the boundary-flux carrier and its exact trichotomy are new
    within this card.

## 9. Next theorem target

Construct a source-normal Rees/nearby-cycle comparison
\[
 \mathrm{BC}^{\rm src}_{\Xi}:
 \widehat{\operatorname{Loc}}_{\rm Kum}
   (N^{\rm src}_{\Xi})
 \longrightarrow
 \operatorname{Loc}_{\rm Kum}
   (\widehat{N^{\rm src}_{\Xi}})
 \tag{17}
\]
on the whole pre-divisor principal-normal sheaf, not on selected fibres, and prove:

1. finite restriction of `(17)` is the already-proved Tate--Kummer--Wold--Gamma interval
   comparison and BV occupation triangle;
2. all-prime transition retains the cofinal Bockstein/top-boundary class rather than normalizing
   it away;
3. `(17)` and its dual use one source \(L^1\) place record;
4. `(17)` is strict and conservative on every multiplicity jet;
5. prime-resolved HT shell synthesis intertwines `(17)` and reads its character by `(10)`;
6. the boundary flux of `(17)` is zero for the literal ordinary-integer source.

No ordinary normalized-state Cauchy estimate can prove item 2: the normalization-amplification
no-go already rules that out.  The candidate must be a relative/Rees comparison retaining the
vanishing scale and its transition maps.

## Literature boundary

Kakutani product-measure equivalence, Kummer/Arakelov degree, conormal localization,
Beck--Chevalley maps, determinant lines, irregular Riemann--Hilbert theory, and uniform
integrability are parent mathematics.  Targeted arXiv searches did not locate the conjunction of
prime-deleted positive HT shells, the exact all-prime slope `(5)`, the Xi BV principal normal, and
the source-completion/localization modular class.  External novelty remains provisional; no
priority claim is made.

## Gates

- [x] 0 → 1: source-pure invariant, exact theorem, producer, and falsifiers stated
- [x] prime-resolved shell/Kummer identity paper-proved
- [x] canonical prime-infinity boundary-flux measure paper-proved
- [x] weak-star / total-variation / \(L^q\) completion trichotomy paper-proved
- [x] collision audit against existing dualizable-charge/Frobenius law
- [x] all-prime modular-defect dictionary assembled from proved corpus theorems
- [x] conditional RH chain dependency-closed
- [ ] construct pre-divisor source Beck--Chevalley map `(17)`
- [ ] define and prove universal defect--flux equality
- [ ] prove ordinary-integer modular flux closure
- [ ] prove strict same-sector monoidality and conormal conservativity
- [ ] audit generalized-prime and Gamma/property-S countermodels against exact hypotheses
- [ ] complete external novelty audit
- [ ] dependency-closed unconditional RH proof
- [ ] unconditional Lean formalization

## Log

- 2026-07-30 — Derived the prime-resolved shell/Kummer radial identity.  Identified shell
  likelihood, Kummer leakage, Kakutani sector, BV orientation, and irregular type as readings of
  one character \(\mathfrak d_s\).  Replaced “find a third completion” by the stricter
  source-completion/principal-localization Beck--Chevalley problem and recorded its exact RH
  consumer and hostile falsifiers.
- 2026-07-30 — Generalized-prime/property-\(S\) hostile audit killed automatic defect vanishing as
  a universal law.  Replaced it by universal defect--flux matching plus the Xi-specific
  ordinary-source zero-flux theorem.
- 2026-07-30 — Constructed the canonical prime-infinity flux carrier.  Coherent finite Kummer
  regulators converge weak-* on the one-point compactification of the prime set to the
  degree-zero dipole
  \(c\delta_{\infty_{\rm ar}}-c\delta_{\infty_{\mathcal P}}\).  This makes the horizontal defect
  literal boundary mass and explains simultaneously why bare \(L^q,\ q>1\), loses it and bare
  \(L^1\) refuses the limit.
- 2026-07-30 — Corpus collision audit found the abstract Frobenius-monoidal
  “dualizable arithmetic charge cannot diffuse” law already present in
  `adjoint-duality-cauchy-nerve-purity-law.md`.  Demoted the universal-law priority claim and
  sharpened the new survivor to the prime-infinity boundary quotient and exact completion
  trichotomy.

## 10. Prime-filtration martingale normal form

The boundary dipole has an exact probabilistic source model.  It is not merely analogous to loss
of mass.

Fix an enumeration \(p_1,p_2,\ldots\) of the rational primes.  On the source valuation space
\[
 \Omega=\prod_p\mathbb N_0,\qquad
 \mu_0=\bigotimes_p\mu_p,\qquad
 \mu_p(k)=(1-p^{-1})p^{-k},
 \tag{18}
\]
put
\[
 \mathcal F_n=\sigma(k_{p_1},\ldots,k_{p_n}),\qquad
 A_n=\{k_{p_1}=\cdots=k_{p_n}=0\},
 \qquad
 a_n=\mu_0(A_n)=\prod_{j\leq n}(1-p_j^{-1}),
 \tag{19}
\]
and define the source-normal density
\[
 Z_n={\mathbf 1_{A_n}\over a_n}.
 \tag{20}
\]

`[PROVED HERE] [PRIME_SOURCE_NORMALIZATION_MARTINGALE_DEFECT]`

The following statements hold.

1. \((Z_n,\mathcal F_n)\) is a nonnegative mean-one martingale:
   \[
    \mathbb E_{\mu_0}(Z_{n+1}\mid\mathcal F_n)=Z_n,
    \qquad
    \mathbb E_{\mu_0}Z_n=1.
    \tag{21}
   \]
2. \(Z_n\to0\) almost surely, but not in \(L^1\).
3. The failure of uniform integrability is maximal:
   \[
    \lim_{R\to\infty}\sup_n
    \mathbb E_{\mu_0}\!\left[
      Z_n\mathbf 1_{\{Z_n>R\}}
    \right]
    =1.
    \tag{22}
   \]
4. The finite measures
   \[
    Q_n(B)=\int_B Z_n\,d\mu_0,\qquad B\in\mathcal F_n,
    \tag{23}
   \]
   are compatible.  Their unique product-space extension is
   \(\delta_{\mathbf0}\).  It is absolutely continuous with respect to \(\mu_0\) on every
   \(\mathcal F_n\), but singular on
   \(\mathcal F_\infty=\sigma(\bigcup_n\mathcal F_n)\).

### Proof

Independence of the new valuation coordinate gives
\[
 \mathbb E_{\mu_0}(Z_{n+1}\mid\mathcal F_n)
 =
 {\mathbf1_{A_n}\over a_{n+1}}
 \mu_{p_{n+1}}(\{0\})
 =
 {\mathbf1_{A_n}\over a_n}.
\]
Euler's divergence of \(\sum_p p^{-1}\) gives \(a_n\to0\), and continuity from above gives
\(\mu_0(\bigcap_nA_n)=0\).  Outside that null intersection, some valuation coordinate is nonzero,
so \(Z_n\) is eventually zero.  This proves almost-sure convergence to zero, while
\(\|Z_n\|_1=1\) rules out \(L^1\) convergence.

For any \(R>0\), choose \(n\) with \(a_n^{-1}>R\).  Since \(Z_n=a_n^{-1}\) on \(A_n\) and is zero
elsewhere,
\[
 \mathbb E_{\mu_0}\!\left[
   Z_n\mathbf1_{\{Z_n>R\}}
 \right]
 =a_n\,a_n^{-1}=1,
\]
which proves `(22)`.  Martingale compatibility proves consistency of `(23)`.  Every \(Q_n\)
assigns probability one to the first \(n\) coordinates being zero, so the extension is
\(\delta_{\mathbf0}\).  Since \(\mu_0(\{\mathbf0\})=0\), the terminal extension is singular.

### The defect coefficient and the two-infinity dipole

For \(c\in\mathbb R\), let \(M_n^{(c)}=cZ_n\).  Its signed expectation defect is
\[
 \operatorname{Def}_{\rm UI}(M^{(c)})
 :=
 \lim_n\mathbb E M_n^{(c)}
 -
 \mathbb E\!\left[\lim_nM_n^{(c)}\right]
 =c.
 \tag{24}
\]
Its absolute tail defect is \(|c|\), and
\[
 (M_n^{(c)})_n\text{ is uniformly integrable}
 \quad\Longleftrightarrow\quad c=0.
 \tag{25}
\]
Consequently the boundary dipole `(11d)` is exactly
\[
 \boxed{\quad
 \nu_{\infty,c}
 =
 \operatorname{Def}_{\rm UI}(M^{(c)})
 \bigl(\delta_{\infty_{\rm ar}}-\delta_{\infty_{\mathcal P}}\bigr).
 \quad}
 \tag{26}
\]
Thus its coefficient has three identical descriptions:
\[
 \text{horizontal modular character}
 =
 \text{lost martingale expectation}
 =
 \text{singular terminal boundary mass}.
 \tag{27}
\]

This is the rank-one probabilistic normal form of completion--localization curvature.  Finite
prime stages see only local absolute continuity.  Infinite completion asks whether that locally
absolutely continuous change of measure remains globally absolutely continuous.  Uniform
integrability is exactly the missing proper-base-change condition.

### Every superlinear source action detects the same wall

Let \(\Phi:[0,\infty)\to[0,\infty)\) satisfy \(\Phi(0)=0\) and
\(\Phi(t)/t\to\infty\).  If \(c\neq0\), then
\[
 \mathbb E_{\mu_0}\Phi(|c|Z_n)
 =
 a_n\Phi(|c|/a_n)
 =
 |c|\,{\Phi(|c|/a_n)\over |c|/a_n}
 \longrightarrow\infty.
 \tag{28}
\]
Hence
\[
 \sup_n\mathbb E_{\mu_0}\Phi(|c|Z_n)<\infty
 \quad\Longleftrightarrow\quad c=0.
 \tag{29}
\]
Special cases are
\[
 \mathbb E Z_n^q=a_n^{1-q}\longrightarrow\infty
 \quad(q>1),
 \qquad
 \mathbb E(Z_n\log Z_n)=\log(a_n^{-1})\longrightarrow\infty.
 \tag{30}
\]
The significance of `(29)` is not another target selector.  It classifies a whole family of
possible source producers.  Any pre-divisor construction which gives the source-normal principal
conormal a cofinal, divisor-independent, uniformly bounded superlinear action automatically makes
its density martingale uniformly integrable and forces \(c=0\).

This unifies the roles previously assigned separately to Kähler energy, Green coercivity,
relative entropy, \(L^q\) control, weak compactness, and nuclear compactness: each would be a
sufficient producer only after its bound is proved on the actual source-normal conormal before
zero specialization.

### Why existing nuclearity does not supply the producer

The canonical Kummer test space
\[
 \mathcal D(Y)=\underset m{\operatorname{ind\,lim}}\mathcal D_m
 \]
is a strict LF limit of finite-dimensional place stages.  Every bounded subset is contained in
one finite stage.  For \(c\neq0\), the regulator \(h_{P_n,c}\) has nonzero support on every prime
component indexed by \(P_n\).  Therefore
\[
 \{h_{P_n,c}:n\geq1\}
 \text{ is unbounded in }\mathcal D(Y).
 \tag{31}
\]
Nuclearity of \(\mathcal D(Y)\), or continuity of finite-stage Kummer maps, consequently gives no
compactness or uniform-integrability conclusion for this cofinal family.  This closes the naive
argument “nuclear source implies compact conormal image.”

The three existing topologies now form an exact trilemma:

```text
strict nuclear LF:
  retains every finite residue, but the cofinal normalized family is unbounded;

mixed L1/L2:
  keeps the family norm-bounded, but it is not uniformly integrable or strongly Cauchy;

weak boundary compactification:
  gives a limit, but the limit carries the singular prime-infinity atom.
```

The third completion must therefore retain the martingale together with its terminal singular
measure and distinguish the class-\(D\) subcategory.  It cannot be another ordinary Banach or
Hilbert completion.

### Sharpened Xi producer and conditional RH theorem

`[BOLD CONJECTURE] [XI_SOURCE_CONORMAL_FOLLMER_ABSOLUTE_CONTINUITY]`

> The pre-divisor ordinary-integer Euler--Gamma/co-Poisson principal-normal object admits a
> source-defined regulator over the complete prime filtration such that:
>
> 1. its finite restrictions agree with the proved Wold/BV source-normal densities and
>    Tate--Kummer interval regulators;
> 2. it is defined on the Rees deformation before principal-divisor specialization;
> 3. its Föllmer terminal measure is globally absolutely continuous in the strict source
>    \(L^1\) boundary channel;
> 4. the terminal density is compatible with reflection and remains conservative on every top
>    multiplicity jet.

Clause 3 is not to be assumed fibrewise.  It must be proved for the one pre-divisor source
morphism.  On localization at a zero \(\rho\) of multiplicity \(m_\rho\), equations
`(5)`--`(10)` and the BV normal law identify
\[
 c_\rho=m_\rho(1/2-\operatorname{Re}\rho).
 \tag{32}
\]
The conjecture makes the localized density martingale class \(D\).  Equation `(25)` forces
\(c_\rho=0\), hence \(\operatorname{Re}\rho=1/2\).  Applied to every top jet, this proves RH with
multiplicity.

This is analytically equivalent, on the coherent rank-one sector, to the nearby-cycle
Beck--Chevalley conjecture `(17)`.  Its advantage is diagnostic precision: the missing morphism
must prevent a locally absolutely continuous source-normal charge from acquiring singular mass
at the terminal prime boundary.

### Universal interpretation and hostile audit

The proposed universal law is now sharper:

> **A horizontal divisor displacement is the singular mass created when a source-normal
> conormal change of measure passes from every finite source filtration to the infinite source.
> Completion--localization curvature is the failure of uniform integrability.**

For arbitrary source-minimal HT objects the singular mass need not vanish; generalized-prime
off-line systems realize nonzero defects.  The universal assertion is defect matching `(27)`.
Zero defect is the additional ordinary-Riemann source theorem.

1. Martingale convergence, class \(D\), Föllmer measures, and the de la Vallée--Poussin criterion
   are parent probability theory.  Novelty is claimed only provisionally for their exact
   ordinary-prime Wold/BV--Kummer--HT conormal identification.
2. The literature on strict local martingales already relates lost mass to singular
   measure-extension phenomena.  It does not supply
   `XI_SOURCE_CONORMAL_FOLLMER_ABSOLUTE_CONTINUITY`.
3. Equation `(29)` does not prove that Xi has a bounded source action.  Postulating such a bound
   on zero fibres is RH-equivalent and circular.
4. Existing finite KMS/entropy-production, Green-energy, and nuclear-source theorems do not give
   the required cofinal bound after normalization amplification.
5. No Lean formalization of `(21)`--`(30)` is prioritized: those are standard consumers.  The
   frontier is construction of the pre-divisor terminal density or a genuine source estimate
   proving its uniform integrability.

Parent literature boundary:

- Martin Larsson, *Filtration shrinkage, strict local martingales and the Föllmer measure*,
  https://arxiv.org/abs/1111.7218.
- Classical martingale convergence and de la Vallée--Poussin uniform-integrability criteria.

## 11. Revised next theorem target

Construct the finite-prime density morphisms of
`XI_SOURCE_CONORMAL_FOLLMER_ABSOLUTE_CONTINUITY` as one compatible pre-divisor martingale, then
prove one of the following source-side statements without evaluating any zero:

1. identify an \(L^1\) terminal density whose conditional expectations are the finite regulator
   morphisms;
2. prove a cofinal bound `(29)` for one source-defined superlinear \(\Phi\);
3. prove relative weak compactness of the complete regulator image on the source-normal Rees
   disk.

These are equivalent producer formats once the finite Wold/BV--Kummer comparison is established.
The first serious obstruction is not martingale theory.  It is constructing the regulator
martingale before divisor specialization and showing that Gamma/co-Poisson sewing cancels, rather
than hides, its prime-boundary singular part.

## 12. Exact chainwise Wold--Kummer transmutation

The first-defect probability law itself is corpus-known.  What was missing was an exact comparison
between its conditioned tails and the coherent Kummer head averages.  The archimedean component is
essential: omitting it changes \(n+1\) to \(n\), loses the first prime coordinate, and produces a
spurious kernel.

Keep the increasing prime order \(p_1<p_2<\cdots\), and write
\[
 \omega=\sum_{j\geq1}w_j\delta_{p_j}.
 \tag{33}
\]
For \(n\geq0\), define the conditioned first-defect tail
\[
 \theta_n
 =
 {1\over a_n}\sum_{j>n}w_j\delta_{p_j},
 \qquad
 F_n(f)=\int f\,d\theta_n,
 \tag{34}
\]
where \(a_0=1\).  On the Kummer place compactification
\[
 K=\{\infty_{\rm ar}\}\sqcup\mathcal P^\dagger
\]
put
\[
 \kappa_n
 =
 {1\over n+1}
 \left(
   \delta_{\infty_{\rm ar}}+\sum_{j=1}^n\delta_{p_j}
 \right).
 \tag{35}
\]

`[PROVED HERE] [PRIME_HAZARD_CESARO_TRANSMUTATION]`

There is a unique linear map
\[
 T:C(\mathcal P^\dagger)\longrightarrow C(K)
 \tag{36}
\]
such that
\[
 T^*\kappa_n=\theta_n
 \qquad(n\geq0).
 \tag{37}
\]
It is given by
\[
 \begin{aligned}
 (Tf)(\infty_{\rm ar})&=F_0(f),\\
 (Tf)(p_n)&=(n+1)F_n(f)-nF_{n-1}(f),\\
 (Tf)(\infty_{\mathcal P})&=f(\infty_{\mathcal P}).
 \end{aligned}
 \tag{38}
\]
Moreover:

1. \(T\) is bounded, with \(\|T\|\leq3\);
2. \(T\) preserves the prime-infinity boundary value and maps \(c_0(\mathcal P)\) into
   \(c_0(K\setminus\{\infty_{\rm ar}\})\);
3. \(T\) is injective;
4. its range is not closed, and \(T^{-1}:\operatorname{Ran}T\to C(\mathcal P^\dagger)\) is
   unbounded;
5. if
   \[
    \nu_{n,c}=c(\delta_{\infty_{\rm ar}}-\kappa_n),
   \]
   then
   \[
    \boxed{\quad
    T^*\nu_{n,c}=c(\omega-\theta_n).
    \quad}
    \tag{39}
   \]
   At the boundary,
   \[
    T^*\nu_{\infty,c}=c(\omega-\delta_{\infty_{\mathcal P}}).
    \tag{40}
   \]

### Proof

The tail probabilities telescope:
\[
 \sum_{j>n}w_j=a_n.
 \]
Hence every \(\theta_n\) is a probability measure.  Removing its first remaining atom gives
\[
 F_{n-1}(f)
 =
 {1\over p_n}f(p_n)
 +
 \left(1-{1\over p_n}\right)F_n(f),
 \tag{41}
\]
and therefore
\[
 (Tf)(p_n)
 =
 F_n(f)+{n\over p_n}\bigl(F_n(f)-f(p_n)\bigr).
 \tag{42}
\]
Since \(n/p_n\leq1\), equation `(42)` proves \(\|T\|\leq3\).  If \(f(p_n)\to f_\infty\), then
\(F_n(f)\to f_\infty\), and `(42)` proves continuity at prime infinity.

The defining differences telescope:
\[
 {1\over n+1}
 \left(
  (Tf)(\infty_{\rm ar})+\sum_{k=1}^n(Tf)(p_k)
 \right)
 =
 F_n(f),
 \tag{43}
\]
which is `(37)`.  Conversely, `(37)` determines every displayed coordinate in `(38)`, proving
uniqueness.  The tail means recover the original sequence by
\[
 f(p_n)=p_nF_{n-1}(f)-(p_n-1)F_n(f),
 \tag{44}
\]
so \(T\) is injective.

Let \(e_N\) be the prime-coordinate unit vector at \(p_N\).  For \(n<N\),
\[
 F_n(e_N)={w_N\over a_n}\leq{1\over p_N},
\]
while \(F_n(e_N)=0\) for \(n\geq N\).  Thus
\[
 \|Te_N\|_\infty\leq
 \max\left\{{2\over p_N},{N\over p_N}\right\}
 ={N\over p_N}
 \longrightarrow0.
 \tag{45}
\]
Here the displayed equality is for \(N\geq2\), and the last limit is the prime number theorem.
Since \(\|e_N\|_\infty=1\), \(T\) is not bounded
below.  A bounded injective operator between Banach spaces with closed range is bounded below, so
the range is not closed and its inverse is unbounded.  Finally, `(39)` follows from
\[
 T^*\delta_{\infty_{\rm ar}}=\omega,\qquad
 T^*\kappa_n=\theta_n,
\]
and `(40)` follows from boundary preservation.

### Rate-distortion meaning

Equation `(42)` is the unique head--tail comparison law.  Its coefficient
\[
 r_n={n\over p_n}\sim{1\over\log p_n}
 \tag{46}
\]
is the exact loss in reconstructing one prime coordinate from its conditioned tail.  The
off-diagonal prefix of \(Te_n\) is \(O(p_n^{-1})\), while its largest coordinate is
\(n/p_n\).  Thus one operator contains both scales already isolated by the actual-prime
first-trace graph fracture:
\[
 \text{individual prime response }p^{-1},
 \qquad
 \text{source reconstruction size }(\log p)^{-1}.
 \tag{47}
\]

The graph space
\[
 \mathcal G_T
 =
 \operatorname{Ran}T,\qquad
 \|g\|_{\mathcal G_T}
 =
 \|g\|_\infty+\|T^{-1}g\|_\infty,
 \tag{48}
\]
is a Hausdorff Banach candidate for the chainwise third completion.  It retains the
prime-infinity boundary and the singular reconstruction scale.  It does **not** prove RH:
membership of both reflected conormal characters in this graph is the existing source-landing
problem in a more explicit coordinate.

## 13. A single exhaustion is insufficient: prime-nerve curvature

The exact chain map exposes a stronger issue.  It works on one nested exhaustion.  The arithmetic
source is indexed by the full directed set of finite prime subsets, whose incomparable
prime-enlargement directions form squares and higher cubes.

For an arbitrary finite prime set \(P\), put
\[
 A_P=\{k_p=0:p\in P\},\qquad
 \theta_P=\tau_\#\bigl(\mu_0(\,\cdot\,\mid A_P)\bigr),
 \tag{49}
\]
where \(\tau\) is the least occupied prime in the increasing norm order, with value
\(\infty_{\mathcal P}\) at the zero valuation.  Also put
\[
 \kappa_P
 =
 {1\over |P|+1}
 \left(
   \delta_{\infty_{\rm ar}}+\sum_{p\in P}\delta_p
 \right),
 \quad
 \nu_{P,c}=c(\delta_{\infty_{\rm ar}}-\kappa_P),
 \quad
 j_{P,c}=c(\omega-\theta_P).
 \tag{50}
\]

`[PROVED HERE] [FULL_PRIME_NERVE_STRICT_LINEARIZATION_RIGIDITY]`

Let \(c\in\mathbb R\).  Suppose one continuous linear map
\[
 L:C(\mathcal P^\dagger)\longrightarrow C(K)
 \tag{51}
\]
simultaneously intertwines every nonempty finite Kummer regulator and Wold conditioning current:
\[
 L^*\nu_{P,c}=j_{P,c}
 \qquad
 \text{for every nonempty finite }P.
 \tag{52}
\]
Then
\[
 \boxed{c=0.}
 \tag{53}
\]
Conversely, \(c=0\) makes `(52)` tautological.

### Two-prime proof

Assume \(c\neq0\), and take two primes \(p<q\).  Write
\[
 \lambda=L^*\delta_{\infty_{\rm ar}},
 \qquad
 \lambda_p=L^*\delta_p,
 \qquad
 \lambda_q=L^*\delta_q.
\]
The singleton cases of `(52)` give
\[
 \lambda_p=\lambda-2\omega+2\theta_{\{p\}},
 \qquad
 \lambda_q=\lambda-2\omega+2\theta_{\{q\}}.
 \tag{54}
\]
The pair case then forces
\[
 3\theta_{\{p,q\}}
 -
 2\theta_{\{p\}}
 -
 2\theta_{\{q\}}
 +
 \omega
 =0.
 \tag{55}
\]
Evaluate this signed measure at the atom \(p\).  Conditioning \(p\) to have zero valuation removes
that atom, while conditioning only the later prime \(q\) does not change the event that \(p\) is
the first occupied prime:
\[
 \theta_{\{p\}}(\{p\})=0,\qquad
 \theta_{\{p,q\}}(\{p\})=0,\qquad
 \theta_{\{q\}}(\{p\})=\omega(\{p\})=w_p>0.
 \]
The left side of `(55)` at \(\{p\}\) is therefore \(-w_p\), a contradiction.

### What the theorem says

```text
one nested chain:
  exact bounded comparison exists for every radial defect c;

full prime-subset nerve:
  no stage-independent strict linear comparison exists for c != 0.
```

This separates two notions previously conflated as “all-prime compatibility.”  Cofinal convergence
along one enumeration is only one-dimensional.  Source-natural completion must also descend across
every interchange square.  The obstruction is the nonzero conditioning curvature
\[
 \mathcal C_{p,q}
 =
 3\theta_{\{p,q\}}
 -
 2\theta_{\{p\}}
 -
 2\theta_{\{q\}}
 +
 \omega.
 \tag{56}
\]
The horizontal conormal displacement is its scalar coupling \(c\mathcal C_{p,q}\).

This gives a sharper universal interpretation:

> **Criticality is strictifiability of the curved prime-conditioning nerve.**
> Finite Wold conditioning is multiplicative, while finite Kummer place averaging is barycentric.
> Their chainwise comparison is bounded but irreversibly rate-distorted.  Their full cubical
> comparison has nonzero \(2\)-curvature.  A horizontal conormal character can descend through one
> stage-independent strict linear source-localization map only at \(c=0\).

The corpus facts become shadows of this one mismatch:

1. normalized Wold states fail to be total-variation Cauchy because multiplicative conditioning
   is not affine place averaging;
2. Kummer mass escapes to prime infinity because a barycentric head cannot retain the
   multiplicative tail in a strong scalar limit;
3. chainwise reconstruction is unbounded at the rate \(n/p_n\);
4. finite prime commutativity requires all square and higher cells because a vertex-level strict
   linearization is impossible off the zero-curvature locus;
5. scalar generalized-prime and off-line Euler systems can realize the oriented defect by
   carrying nonzero higher conditioning curvature rather than a strict linear descent.

### Strictification hunch and immediate correction

`[OVERSTRONG AS STATED] [NOT THE CURRENT PRODUCER]`

> The ordinary-integer Euler--Gamma/co-Poisson principal-normal object has one pre-divisor,
> stage-independent continuous linear comparison on the source-normal nearby-cycle conormal.
> Its restriction to every finite prime packet sends the exact Kummer regulator current
> \(\nu_{P,c}\) to the Wold/BV first-defect conditioning current \(j_{P,c}\), commutes strictly
> with every prime-enlargement square, preserves reflection, and is conservative on every top
> multiplicity jet.

If this conjecture holds, localize at a zero \(\rho\) of multiplicity \(m_\rho\).  The proved
shell/BV/Kummer dictionary gives
\[
 c=m_\rho(1/2-\operatorname{Re}\rho).
\]
The theorem `(53)` gives \(c=0\); since \(m_\rho>0\),
\(\operatorname{Re}\rho=1/2\).  This proves RH.

The implication is correct, but hostile audit makes the premise implausibly strict as a raw
description of source conditioning.  Division by \(a_P\) changes the barycentric weights by
Bayes' formula.  A July 2026 cubical formalization of Bayesian conditioning proves, in a general
probability setting, that ordinary convex interchange is too weak for this operation and must be
replaced by a generalized interchange with distinct inner weights:

- Karen Sargsyan, *A cubical formalisation of conditional independence, Bayesian conditioning,
  and Pearl's d-separation soundness*, https://arxiv.org/abs/2606.20351.

The project's own cubical bar/Koszul comparison had already predicted the same correction.
Therefore `(53)` is retained as a sharp no-go and a conditional consumer, but raw
stage-independent linearization is not promoted as the likely Xi theorem.  The positive survivor
is a weaker scalar fixed-point law on the Hermitian conormal norm.

### Hostile audit

1. The theorem `(53)` is unconditional, finite, and non-circular.  The conjecture that Xi supplies
   the single strict linearization is unproved and contains all remaining RH strength.
2. Existing cubical bar/Koszul constructions predict higher homotopies.  If the true comparison is
   merely \(A_\infty\)-natural, its \(2\)-cell can carry `(56)` and no criticality follows.
   **Strictification on the principal conormal**, not generic derived naturality, is load-bearing.
3. A family of packet-dependent maps \(L_P\) evades `(53)`.  Presentation independence must be
   proved from one pre-divisor source morphism; it cannot be declared after fibre specialization.
4. The first-defect probability, conditioning law, Cesàro and Copson operators, and non-affinity of
   conditioning are parent mathematics.  Candidate-new content is the exact Wold--Kummer adjoint
   identity `(39)`, the rate-distortion law `(45)`--`(47)`, and the strict prime-nerve rigidity
   conjunction `(52)`--`(56)`.  External novelty remains provisional.
5. This result corrects the previous next target.  Proving uniform integrability along one chain
   would still miss incomparable prime squares.  First determine whether the Xi principal
   conormal comparison strictifies the full prime nerve or necessarily retains higher curvature.
6. No Lean formalization is prioritized yet.  Formalizing `(53)` before proving that the Xi
   source furnishes `(52)` would certify a small conditional consumer while leaving the frontier
   untouched.

## Revised gates and log

- [x] exact chainwise Wold--Kummer adjoint transmutation paper-proved
- [x] archimedean \(n+1\) coordinate and injectivity correction proved
- [x] actual-prime inverse instability \(n/p_n\to0\) proved
- [x] full prime-nerve strict-linearization rigidity paper-proved
- [x] single-exhaustion source proofs ruled insufficient
- [ ] identify actual finite Wold/BV current with \(j_{P,c}\) on every prime packet
- [ ] construct one pre-divisor comparison over the full finite-prime nerve
- [ ] prove strictification rather than only cubical/\(A_\infty\) naturality on the principal
  conormal
- [ ] audit generalized-prime off-line systems against strictification hypothesis
- [ ] dependency-close unconditional RH proof
- [ ] unconditional Lean formalization

- 2026-07-30 — Added the missing archimedean coordinate to the head--tail comparison and proved the
  unique bounded transmutation \(T\).  Its adjoint sends the coherent finite Kummer regulator
  exactly to the Wold first-defect conditioning current.  Its inverse is unbounded at the
  actual-prime rate \(n/p_n\sim1/\log p_n\).
- 2026-07-30 — Tested the chain construction against the full finite-prime subset nerve.  A single
  stage-independent linear comparison for all packets forces a false two-prime affine identity
  unless the horizontal conormal coefficient is zero.  This yields the strict prime-nerve
  linearization rigidity theorem and moves the RH-bearing producer from chainwise compactness to
  strictification across every prime interchange square.

## 14. The positive survivor: first-defect Markov--Liouville law

Define the tail-renewal operator
\[
 B:C(\mathcal P^\dagger)\longrightarrow C(\mathcal P^\dagger)
 \tag{57}
\]
by
\[
 (Bf)(p_n)=F_n(f)
 ={1\over a_n}\sum_{j>n}w_jf(p_j),
 \qquad
 (Bf)(\infty_{\mathcal P})=f(\infty_{\mathcal P}).
 \tag{58}
\]
Thus, from prime \(p_n\), the Markov chain jumps to the first occupied prime conditioned to lie
strictly after \(p_n\).  It never returns to a finite prime; all recurrence is carried by the
prime-infinity boundary.

`[PROVED HERE] [FIRST_DEFECT_MARKOV_LIOUVILLE_RIGIDITY]`

The operator \(B\) is positive, unital, and contractive.  Its continuous harmonic functions are
exactly the constants:
\[
 \boxed{\quad
  Bf=f
  \quad\Longleftrightarrow\quad
  f\text{ is constant}.
 \quad}
 \tag{59}
\]

### Proof

Positivity, preservation of constants, and contractivity follow because every \(\theta_n\) is a
probability measure.  If \(Bf=f\), then \(F_n(f)=f(p_n)\).  Equation `(41)` gives
\[
 f(p_{n-1})
 =
 {1\over p_n}f(p_n)
 +
 \left(1-{1\over p_n}\right)f(p_n)
 =
 f(p_n)
 \qquad(n\geq2).
 \tag{60}
\]
Hence all finite-prime values are equal, and continuity gives the same value at prime infinity.
The converse is immediate.

For a real radial exponent \(c\), put
\[
 r_c(p)=p^c.
 \tag{61}
\]
Then:

1. if \(c<0\), \(r_c\in C(\mathcal P^\dagger)\) and
   \[
    Br_c(p_n)<r_c(p_n)
    \qquad\text{for every }n;
    \tag{62}
   \]
2. if \(c=0\), \(r_c=1\) and \(Br_c=r_c\);
3. if \(c>0\), every tail expectation in `(58)` is infinite by the proved first-defect
   exponential-moment theorem.

Therefore, in the extended positive cone,
\[
 \boxed{\quad
  Br_c=r_c
  \quad\Longleftrightarrow\quad
  c=0.
 \quad}
 \tag{63}
\]
The theorem acts on modulus only.  A unitary phase \(p^{it}\) is not required to be constant, so
`(63)` selects the critical **line**, not the central point.

### The first square already sees the Liouville boundary

For \(p=2\) and \(q=3\), the conditioning curvature `(56)` simplifies exactly to
\[
 \mathcal C_{2,3}
 =
 \theta_{\{2,3\}}
 -
 {1\over2}\delta_2
 -
 {1\over2}\delta_3.
 \tag{64}
\]
Indeed, its negative mass is \(1/2\) at each of \(2\) and \(3\), while its positive part is the
probability law of the first occupied prime conditioned to be at least \(5\).
Consequently,
\[
 \int r_c\,d\mathcal C_{2,3}
 \begin{cases}
 <0,&c<0,\\
 =0,&c=0,\\
 =+\infty,&c>0.
 \end{cases}
 \tag{65}
\]
For \(c<0\), every point in the positive tail has \(r_c(p)<r_c(3)\), while the negative head is
the average of \(r_c(2)\) and \(r_c(3)\).  For \(c>0\), the first-defect moment diverges.
Thus the full infinite tail is already distinguished from its first two source coordinates by one
strict modulus-curvature law.

### New universal hunch

`[BOLD CONJECTURE] [XI_CONORMAL_FIRST_DEFECT_MARKOV_HARMONICITY]`

> The ordinary-integer Euler--Gamma/co-Poisson source carries one pre-divisor positive Hermitian
> metric on its principal-normal line.  Under the exact Wold first-defect renewal, the metric's
> semisimple prime modulus is \(B\)-harmonic.  This harmonicity is constructed before divisor
> specialization, is compatible with Gamma reflection, and remains faithful on every top
> multiplicity jet.

This is deliberately a conjecture in the user's strong sense: the corpus makes it plausible, but
no proof method is presently asserted.  It says what source recurrence must mean numerically,
rather than postulating that a chosen zero lies in a critical receiver.

At a zero \(\rho\) of multiplicity \(m_\rho\), the proved local shell/Kummer/BV dictionary
specializes the Hermitian modulus to
\[
 r_\rho(p)
 =
 p^{\,m_\rho(1/2-\operatorname{Re}\rho)}.
 \tag{66}
\]
The conjecture and `(63)` force
\[
 m_\rho(1/2-\operatorname{Re}\rho)=0.
\]
Since \(m_\rho>0\), every nontrivial zero lies on the critical line.

### Why this is a better mechanism

```text
source recurrence:
  conormal norm is stationary under least-prime renewal;

Markov Liouville law:
  stationary continuous norms are constants;

constant radial norm:
  prime dilation acts unitarily;

unitary prime dilation:
  Re(rho)=1/2.
```

This joins the corpus without identifying recurrence with finite return:

1. finite truncations recur because every finite tail has a terminal state, but they do not see
   the Liouville boundary;
2. ambient adelic \(L^2\) retains the Markov chain but loses the singular conormal metric;
3. Kummer prime-infinity leakage is the failure of a nonconstant radial norm to be harmonic;
4. Wold normalization amplification is the strict drift \(Br_c-r_c\);
5. the chainwise transmutation \(T\) compares head averages with renewed tails, while \(B\)
   extracts the fixed-point law that comparison was missing;
6. the abstract corpus conjecture “source principal conormals are recurrent” becomes one
   falsifiable renewal identity `(58)`, not a slogan.

### Hostile audit and exact open core

1. Markov contractions and the Liouville theorem `(59)` are parent probability theory.  Novelty is
   restricted to this exact first-defect Wold--Kummer conormal realization.
2. The conjecture is not proved by positivity, functional equation, hypertranscendence,
   prime-dilation covariance, or finite Wold identities separately.  Generalized-prime off-line
   systems are expected to fail precisely this harmonicity.
3. Stating \(Br_\rho=r_\rho\) after choosing \(\rho\) is equivalent to the desired criticality.
   Required theorem is one metric-renewal identity on the complete pre-divisor conormal sheaf.
4. Phase recurrence alone is insufficient.  The renewal must act on the positive Hermitian norm,
   leaving \(p^{it}\) free while killing radial drift.
5. The two-prime curvature test `(65)` is a finite reporter with an infinite tail.  It does not
   prove that the Xi metric annihilates that curvature.
6. Hypertranscendence supplies non-finite-collapse: all prime-tail restrictions must remain
   visible.  It does not itself supply harmonicity.

The next non-immediate mathematical obstacle is now exact:

> Construct the source Hermitian conormal metric before localization and prove that least-prime
> factorization of the ordinary-integer Wold/Gamma/co-Poisson source induces the fixed-point
> identity \(Br=B\!^0r=r\) on its semisimple modulus.

Any proposed proof must compute the boundary correction.  If Gamma/co-Poisson sewing gives
\[
 Br-r=\varepsilon
 \]
instead, \(\varepsilon\) is the new source curvature and must be classified rather than discarded.

## Final gate update

- [x] first-defect tail Markov operator constructed
- [x] exact continuous Liouville theorem proved
- [x] radial harmonicity locus proved to be \(c=0\)
- [x] \(2,3\)-prime modulus-curvature law proved
- [x] raw strict convex linearization demoted after cubical/Bayesian audit
- [ ] construct pre-divisor positive conormal metric
- [ ] derive Markov renewal from least-prime Wold/Gamma/co-Poisson factorization
- [ ] compute and classify the Gamma/archimedean boundary correction
- [ ] prove multiplicity-faithful source localization
- [ ] dependency-close unconditional RH proof
- [ ] unconditional Lean formalization

- 2026-07-30 — Replaced the overstrong raw strictification producer by its positive survivor.
  The first-defect tail kernel is a canonical Markov contraction whose continuous harmonic
  functions are exactly constants.  The localized radial modulus \(p^c\) is harmonic exactly at
  \(c=0\), yielding a concrete source-recurrence mechanism for critical-line selection and an
  exact pre-divisor metric-renewal theorem target.

## 15. Markov--Schur fusion: the universal law behind the receivers

The Markov formulation is not separate from the positive-shell fusion law already present in the
corpus.  They are two exact forms of one operator statement.

Let
\[
 {\cal H}_{\rm fd}=\ell^2(\mathbb N_{>0},w),\qquad
 \Omega=(1,1,\ldots)\in{\cal H}_{\rm fd},
 \tag{67}
\]
so \(\|\Omega\|^2=\sum_jw_j=1\).  Equivalently, in unweighted coordinates the vector is
\((\sqrt{w_j})_j\).  Let
\[
 P_\Omega=|\Omega\rangle\langle\Omega|
 \tag{68}
\]
be the rank-one fusion projection.  For \(n\geq0\), define the normalized tail vector
\[
 \Omega_n
 =
 {1\over\sqrt{a_n}}\mathbf1_{\{j>n\}}\Omega.
 \tag{69}
\]
For a bounded prime observable \(f=(f_j)\), let \(D_f\) be diagonal multiplication by \(f_j\).

`[PROVED HERE] [FIRST_DEFECT_MARKOV_SCHUR_FUSION_EQUIVALENCE]`

\[
 \boxed{
 \begin{aligned}
  (Bf)(p_n)
   &=\langle\Omega_n,D_f\Omega_n\rangle,\\
  \ker(I-B)
   &=\{f:[D_f,P_\Omega]=0\}\\
   &=\mathbb C1.
 \end{aligned}}
 \tag{70}
\]

### Proof

The first identity is just
\[
 \langle\Omega_n,D_f\Omega_n\rangle
 =
 {1\over a_n}\sum_{j>n}w_jf_j
 =
 F_n(f).
 \tag{71}
\]
The fixed-space equality with \(\mathbb C1\) is `(59)`.  If
\([D_f,P_\Omega]=0\), the one-dimensional range of \(P_\Omega\) is invariant under \(D_f\), so
\[
 D_f\Omega=\lambda\Omega
\]
for some \(\lambda\).  Every \(w_j\) is positive, hence every coordinate of \(\Omega\) is nonzero
and \(f_j=\lambda\) for all \(j\).  Constants commute with \(P_\Omega\), proving `(70)`.

Let \(C\) be the Kummer head-average operator on functions \(g\in C(K)\):
\[
 (Cg)_n=\int_Kg\,d\kappa_n.
 \tag{72}
\]
The transmutation identity `(43)` is exactly
\[
 \boxed{\quad CT=B.\quad}
 \tag{73}
\]
Thus the three constructions have one factorization:

```text
Wold tail renewal B
  = Kummer barycentric observation C
      after the singular head--tail transmutation T.
```

The inverse instability of \(T\) says that the same fixed metric is easy to observe from the
source tail but unstable to reconstruct from scalar place averages.  The Markov fixed-point law
and fusion-commutant law say that, if the complete positive observation is nevertheless preserved,
its Hermitian metric has no nonconstant radial degree of freedom.

### Universal interpretation

> **Complete-observation Hermitian Liouville law.**
> A source-minimal hypertranscendental object supplies a full-support positive fusion frame and a
> recurrent source boundary.  A principal-conormal metric produced by that source is a harmonic
> observable of the frame's tail Berezin transform.  Complete observation makes the positive
> Poisson boundary trivial, so the metric is scalar.  Scalar conormal metric is unitary radial
> holonomy, hence criticality.

This is the common statement behind:

1. the existing finite-shell theorem that a diagonal polar defect commuting with the shell label
   and full-support fusion projector is scalar;
2. the Wold claim that a recurrent principal conormal has no unilateral storage component;
3. the Kummer claim that its strict place degree cannot leak to prime infinity;
4. the first-defect claim that both reflected exponential moments can coexist only at radial
   exponent zero;
5. the complete-clock principle that no polarization can disappear from a left-invertible full
   observation.

The theorem explains the exact roles of prior hypotheses.

```text
positivity without fusion:
  diagonal off-line metrics survive;

fusion without source recurrence:
  scalarity theorem has no reason to apply to the Xi conormal;

recurrence in ambient L2:
  divisor fibres disappear before their metric is observed;

hypertranscendence:
  prevents finite collapse of the labelled observation, but does not prove harmonicity;

functional equation:
  inverts radial metric, but does not place it in the positive fusion commutant;

source fusion + Hermitian recurrence:
  leaves only a scalar metric.
```

This also clarifies the required “third completion.”  It is not merely the graph space `(48)`.
It must retain simultaneously:

1. the singular principal-conormal metric \(D\);
2. the full-support source fusion vector \(\Omega\);
3. every tail coherent state \(\Omega_n\);
4. the Kummer observation factorization \(CT=B\);
5. the Gamma/reflection dagger;
6. enough source topology to state \(D\Omega=\lambda\Omega\) without deleting \(D\) or
   \(\Omega\).

### Exact Xi theorem target

`[BOLD CONJECTURE] [XI_COMPLETE_OBSERVATION_HERMITIAN_LIOUVILLE]`

> In one source-defined relative completion of the ordinary-integer
> Euler--Gamma/co-Poisson/positive-HT object, the complete principal Xi conormal carries a positive
> polar metric \(D_\Xi\).  The source fusion line is invariant under \(D_\Xi\), equivalently the
> localized semisimple modulus is fixed by the first-defect tail Berezin transform.  This
> invariance is proved before choosing a zero, is compatible with all prime and HT-shell labels,
> and is conservative on each top multiplicity jet.

The first-defect Markov conjecture and positive-shell star-covariance conjecture are therefore not
two independent RH assumptions.  They are prime and shell charts of this one proposed source
invariance.  The next proof attempt must construct the common fusion line and dagger across both
charts; proving either chart only after localization remains theatre.

### Post-weld hostile audit

1. The equality of the fixed space and diagonal fusion commutant is elementary Schur/Liouville
   mathematics.  Frontier content is entirely the Xi source-invariance theorem.
2. Prime and exponent-shell weights are different positive frames.  A common source fusion has
   not been constructed merely by observing that both frames have full support.
3. Tensoring the two frames by hand would force irreducibility but would be target-fed.  The common
   fusion vector must be induced by the actual Euler--Gamma/co-Poisson incidence and agree with
   both proved normal-jet systems.
4. Generalized-prime off-line systems falsify any claim that scalar entire
   functional-equation data automatically preserve the source fusion line.
5. The exact shell reconstruction proves that \(H_m(\rho)\) are genuine normal coordinates of a
   zeta zero.  It does not prove that their polar metric preserves fusion.  This is the present
   gap, not a hidden completed proof.

## Frontier after the universal weld

- [x] Wold tail kernel represented as nested coherent-state Berezin transform
- [x] harmonic fixed space identified with diagonal fusion commutant
- [x] Kummer--transmutation--Wold factorization \(CT=B\)
- [x] Markov and shell-fusion RH mechanisms identified as one law
- [ ] construct common prime/shell fusion line from actual source incidence
- [ ] construct positive conormal polar metric in same relative completion
- [ ] prove source continuation preserves fusion line and Gamma dagger
- [ ] show localized metric coordinates equal the proved \(p^c\) and shell likelihood rates
- [ ] prove conormal/multiplicity conservativity
- [ ] unconditional RH proof and Lean formalization

- 2026-07-30 — Identified first-defect renewal as the tail Berezin transform of the
  full-support source fusion vector.  Its harmonic functions, the diagonal fusion commutant, and
  constants coincide.  The Kummer head observation factors it as \(CT=B\).  This turns the
  previously separate Wold recurrence, Kummer leakage, and positive-shell Schur mechanisms into
  one complete-observation Hermitian Liouville law, while isolating the still-unproved Xi
  source-invariance theorem.

## 16. The common prime/shell fusion is a literal source probability

The post-weld audit left a serious gap: prime first-defect weights and exponent-shell weights are
different positive frames, and tensoring them by hand would be target-fed.  The valuation source
itself supplies their canonical joint law.

On \((\Omega,\mu_0)\), define
\[
 \tau(\mathbf k)=\min\{p:k_p>0\},
 \qquad
 M(\mathbf k)=\sup_p k_p,
 \tag{74}
\]
with \(\tau(\mathbf0)=\infty_{\mathcal P}\).  Also put
\[
 M_{\geq p}(\mathbf k)=\sup_{q\geq p}k_q.
 \tag{75}
\]
The previous first-defect theorem proves \(\tau<\infty\) almost surely.  The random variable \(M\)
is finite almost surely because
\[
 \mu_0(M\leq m)
 =
 \prod_p(1-p^{-(m+1)})
 =
 {1\over\zeta(m+1)}
 \longrightarrow1.
 \tag{76}
\]

The ambient product law is the critical projective valuation source, not a uniform probability
measure on finite integers.  In fact \(\sum_p\mu_0(k_p>0)=\sum_p1/p=\infty\), so Borel--Cantelli
makes infinitely many primes occupied almost surely.  Its samples are naturally supernatural
valuation vectors.  Nevertheless the finite-coordinate laws, and the events used below, are the
Euler-product natural densities of the corresponding ordinary-integer conditions.  Thus
\(\pi_{p,m}\) is an ordinary-integer density realized on the projective boundary; it must not be
described as a random finite integer.

`[PROVED HERE] [PRIME_FIRST_DEFECT_MAXIMUM_EXPONENT_JOINT_SOURCE_LAW]`

For \(m\geq1\), define
\[
 \pi_{p,m}
 =
 \mu_0(\tau=p,\ M=m).
 \tag{77}
\]
Then \(\pi\) is a full-support probability distribution on
\(\mathcal P\times\mathbb N_{>0}\), with marginals
\[
 \boxed{
 \begin{aligned}
  \sum_{m\geq1}\pi_{p,m}
   &=w_p,\\
  \sum_p\pi_{p,m}
   &={1\over\zeta(m+1)}-{1\over\zeta(m)}
    =H_{2,m}(1),\\
  \mu_0(M_{\geq p}=m)
   &={1\over\zeta_p(m+1)}-{1\over\zeta_p(m)}
    =H_{p,m}(1).
 \end{aligned}}
 \tag{78}
\]
Thus:

```text
Wold first occupied prime
and
positive HT maximum-exponent shell
are two marginals of one ordinary-integer valuation incidence.
```

### Exact joint formula

Let \(p=p_j\), and write
\[
 a_{<p}=\prod_{q<p}(1-q^{-1}).
 \]
For \(m\geq1\),
\[
 \begin{aligned}
 G_{p,m}
 &:=
 \mu_0(\tau=p,\ M\leq m)\\
 &=
 {a_{<p}\over p}
 (1-p^{-m})
 \prod_{q>p}(1-q^{-(m+1)})\\
 &=
 {a_{<p}\over p}
 {1-p^{-m}\over\zeta_{p^+}(m+1)},
 \end{aligned}
 \tag{79}
\]
where \(p^+\) is the next prime and \(G_{p,0}=0\).  Hence
\[
 \boxed{\quad
 \pi_{p,m}=G_{p,m}-G_{p,m-1}.
 \quad}
 \tag{80}
\]

Indeed, all primes below \(p\) must have valuation zero; the \(p\)-valuation must lie in
\(\{1,\ldots,m\}\), an event of probability \(p^{-1}(1-p^{-m})\); and every later valuation must
be at most \(m\).  Independence gives `(79)`.  The event
\[
 k_q=0\ (q<p),\qquad k_p=m,\qquad k_q\leq m\ (q>p)
\]
has positive probability, so every \(\pi_{p,m}>0\).  The marginal identities follow directly
from `(74)`--`(76)`.

For fixed \(p\), the joint shell has the sharp rate
\[
 \boxed{\quad
  \pi_{p,m}
  \sim
  a_{<p}(1-p^{-1})p^{-m}.
 \quad}
 \tag{81}
\]
The lower bound is the positive event displayed above.  The upper bound is
\[
 \pi_{p,m}
 \leq
 a_{<p}\mu_0(M_{\geq p}=m)
 =
 a_{<p}H_{p,m}(1).
 \]
Both bounds have the same asymptotic by the prime-resolved shell theorem and
\(\prod_{q>p}(1-q^{-(m+1)})\to1\), proving `(81)`.  In particular,
\[
 {\pi_{p,m}\over H_{p,m}(1)}
 \longrightarrow a_{<p}.
 \tag{82}
\]

### Canonical joint Dirichlet shell: no fitted rescaling

Let
\[
 {\mathscr S}_{p,m}(s)=\zeta_p(s)H_{p,m}(s)
\]
be the existing Dirichlet series of \(p\)-rough integers whose maximum valuation exponent is
exactly \(m\).  Partitioning that shell according to whether \(p\) is occupied gives the literal
joint cell
\[
\begin{aligned}
 {\mathscr J}_{p,m}(s)
 &:=
 \sum_{\substack{n\geq2\\ \tau(n)=p,\ M(n)=m}}n^{-s}\\
 &=
 {\mathscr S}_{p,m}(s)-{\mathscr S}_{p^+,m}(s)
 =
 \zeta(s)B_{p,m}(s),
\end{aligned}
\tag{83}
\]
initially for \(\operatorname{Re}s>1\), where
\[
 \boxed{\quad
 B_{p,m}(s)
 =
 E_p(s)H_{p,m}(s)-E_{p^+}(s)H_{p^+,m}(s),
 \qquad
 E_p(s)=\prod_{q<p}(1-q^{-s}).
 \quad}
\tag{84}
\]
This is coefficient partition, not a rescaling of a pre-existing analytic frame.

There is also a closed cumulative formula.  Put
\[
 A_{p,m}(s)
 =
 {p^{-s}(1-p^{-ms})\over\zeta_{p^+}((m+1)s)},
 \qquad A_{p,0}=0.
\]
Then
\[
 \sum_{\substack{n\geq2\\ \tau(n)=p,\ M(n)\leq m}}n^{-s}
 =
 \zeta(s)E_p(s)A_{p,m}(s),
 \qquad
 B_{p,m}=E_p(A_{p,m}-A_{p,m-1}).
 \tag{85}
\]
Indeed, primes below \(p\) have exponent zero, the \(p\)-exponent contributes
\[
 p^{-s}+p^{-2s}+\cdots+p^{-ms}
 =
 {p^{-s}(1-p^{-ms})\over1-p^{-s}},
 \]
and every later prime has exponent at most \(m\).  Multiplication of the local factors gives
`(85)`.

At the positive source point,
\[
 \boxed{\quad
 B_{p,m}(1)=\pi_{p,m}.
 \quad}
 \tag{86}
\]
This follows either by substituting `(79)` into `(85)` or by taking the residue at \(s=1\) of
the ordinary-integer Dirichlet series `(83)`.  Moreover,
\[
 \sum_{p,m}{\mathscr J}_{p,m}(s)=\zeta(s)-1
 \tag{87}
\]
in the half-plane of absolute convergence.

For fixed \(p\), normally on compact subsets of \(\operatorname{Re}s>0\),
\[
 B_{p,m}(s)
 =
 E_p(s)p^{-ms}(1-p^{-s})
 +
 O_{p,s}\bigl((p^+)^{-m\operatorname{Re}s}\bigr).
 \tag{88}
\]
Thus, for sufficiently large \(m\), \(B_{p,m}\) is holomorphic and zero-free in a neighborhood
of every point of the strict right half-plane.  Equation `(83)` then gives an actual
common-\(\zeta\)-divisor joint cell, including the top principal multiplicity jet, rather than a
source-normalized copy of one.

The complete analytic incidence frame retains the existing HT data.  Finite telescoping gives
\[
 E_p(s)H_{p,m}(s)
 =
 H_{2,m}(s)-\sum_{2\leq q<p}B_{q,m}(s).
 \tag{89}
\]
Consequently the global maximum-exponent marginal \(H_{2,m}\), together with the joint cells
\(B_{q,m}\), reconstructs every prime-deleted HT shell by a finite triangular transformation.
The known relative-HT frame is therefore not discarded when one passes to the joint incidence.

### One marginal is exact; the other carries prime-infinity curvature

Summing over shell depth at one fixed first prime is already compatible with continuation.  The
asymptotic `(88)` makes the series normally convergent on compact subsets of
\(\operatorname{Re}s>0\), and telescoping the two prime-deleted shells in `(84)` gives
\[
 \boxed{\quad
  \sum_{m\geq1}B_{p,m}(s)
  =
  E_p(s)p^{-s}.
 \quad}
 \tag{89a}
\]
Equivalently,
\[
 \sum_{m\geq1}{\mathscr J}_{p,m}(s)
 =
 \sum_{\tau(n)=p}n^{-s}
 =
 \zeta(s)E_p(s)p^{-s}
 \tag{89b}
\]
where the first equality begins in the absolute half-plane and the last expression supplies its
continuation.

The other marginal has an exact finite-cutoff defect.  If \(P^+\) is the prime following a
finite prime cutoff \(P\), then `(84)` telescopes to
\[
 \boxed{\quad
  \sum_{2\leq p\leq P}B_{p,m}(s)
  =
  H_{2,m}(s)-E_{P^+}(s)H_{P^+,m}(s).
 \quad}
 \tag{89c}
\]
At \(s=1\), the remainder tends to zero and `(89c)` becomes the probability marginal
\(\sum_p\pi_{p,m}=H_{2,m}(1)\).  Away from the positive source, the whole all-prime
completion problem is concentrated in the explicit boundary term
\[
 {\mathcal R}_{P,m}(s)
 =
 E_{P^+}(s)H_{P^+,m}(s).
 \tag{89d}
\]
Thus forgetting maximum depth is already source-flat, while forgetting first occupied prime
acquires a prime-infinity curvature.  Any joint Bayes/Beck--Chevalley theorem must control
`(89d)` in the source-normal topology; treating the two marginal squares as equally unconstructed
would miss this exact asymmetry.

Define the joint half-density continuation and its coordinate intensity by
\[
 c_{p,m}(s)
 =
 {B_{p,m}(s)\over\sqrt{\pi_{p,m}}},
 \qquad
 d_{p,m}(s)
 =
 |c_{p,m}(s)|^2
 =
 {|B_{p,m}(s)|^2\over\pi_{p,m}}.
 \tag{90}
\]
Equation `(86)` gives
\[
 c_{p,m}(1)=\sqrt{\pi_{p,m}}.
 \tag{91}
\]
Here \(c(s)\) is a half-density coordinate in the unweighted counting model
\(\ell^2(\mathcal P\times\mathbb N_{>0})\), whose source fusion vector has coordinates
\(\sqrt{\pi_{p,m}}\).  Under the unitary identification with
\(\ell^2(\mathcal P\times\mathbb N_{>0},\pi)\), the corresponding function is
\[
 {c_{p,m}(s)\over\sqrt{\pi_{p,m}}}
 =
 {B_{p,m}(s)\over\pi_{p,m}}.
\]
Thus \(d_{p,m}=|c_{p,m}|^2\) is the counting-coordinate intensity of the continued
half-density.  It is not asserted to be a Radon--Nikodym density or a normal
\(L^2(\pi)\) state.  The factor \(\pi_{p,m}\) is exactly the source half-density shift which makes
the zero-degree boundary occur at \(\operatorname{Re}s=1/2\), rather than at the positive source
abscissa \(1\).

Equations `(81)` and `(88)` give
\[
 \boxed{\quad
 \lim_{m\to\infty}{1\over m}
 \log d_{p,m}(s)
 =
 (1-2\operatorname{Re}s)\log p.
 \quad}
 \tag{92}
\]
Indeed,
\[
 {1\over m}\log\pi_{p,m}\to-\log p,\quad
 {1\over m}\log|B_{p,m}(s)|\to-\operatorname{Re}s\log p.
\]

### Exact joint source gauge

The raw metric in `(90)` is not expected to be scalar on the critical line.  It retains a
bounded, generally nonconstant transverse shell gauge.  To separate that gauge from the modular
degree, put
\[
 G^{\rm joint}_{p,m}(s)
 =
 {p^{ms}B_{p,m}(s)\over E_p(s)(1-p^{-s})}.
 \tag{93}
\]
For fixed \(p\), normally on compact subsets of \(\operatorname{Re}s>0\),
\[
 G^{\rm joint}_{p,m}(s)\longrightarrow1.
 \tag{94}
\]
In particular it is eventually nonzero, while
\[
 \pi_{p,m}
 =
 \beta_pp^{-m}G^{\rm joint}_{p,m}(1),
 \qquad
 \beta_p=a_{<p}(1-p^{-1}).
 \tag{95}
\]
Write
\[
 C_p(s)={E_p(s)(1-p^{-s})\over\sqrt{\beta_p}},
\]
and define the eventual transverse gauge
\[
 Q_{p,m}(s)
 =
 {G^{\rm joint}_{p,m}(s)\over
  \sqrt{G^{\rm joint}_{p,m}(1)}}.
 \tag{96}
\]
Equation `(94)` gives
\[
 Q_{p,m}(s)\longrightarrow1
 \tag{97}
\]
for every fixed \(p\) and \(s\) in the strict right half-plane.  Direct substitution, with no
asymptotic equality, yields
\[
 \boxed{\quad
 c_{p,m}(s)
 =
 C_p(s)Q_{p,m}(s)p^{-m(s-1/2)}.
 \quad}
 \tag{98}
\]
Therefore
\[
 d_{p,m}(s)
 =
 R_{p,m}(s)\widetilde d_{p,m}(s),
 \qquad
 R_{p,m}(s)=|C_p(s)Q_{p,m}(s)|^2,
 \qquad
 \widetilde d_{p,m}(s)=p^{m(1-2\operatorname{Re}s)}.
 \tag{99}
\]
For fixed \(p,s\), \(R_{p,m}(s)\) is eventually bounded and bounded away from zero and has zero
exponential \(m\)-rate.  The gauge-invariant modular polar degree is exactly
\[
 \widetilde d_{p,m}(s)=p^{m(1-2\operatorname{Re}s)}.
 \]

### Common fusion line and gauge-reduced criticality theorem

Let
\[
 {\cal H}_{\rm joint}
 =
 \ell^2(\mathcal P\times\mathbb N_{>0},\pi),
 \qquad
 \Omega_{\rm joint}=1,
 \qquad
 P_{\rm joint}
 =
 |\Omega_{\rm joint}\rangle\langle\Omega_{\rm joint}|.
 \tag{100}
\]
Its two coordinate marginals are exactly the Wold prime fusion and positive HT shell fusion in
`(78)`.  No tensor-product choice was made.

For a finite joint packet \(E\), let
\[
 \widetilde D_{s,E}
 =
 \operatorname{diag}\bigl(p^{m(1-2\operatorname{Re}s)}\bigr)_{(p,m)\in E},
 \qquad
 P_E
 =
 {|\Omega_E\rangle\langle\Omega_E|
  \over\langle\Omega_E,\Omega_E\rangle},
 \tag{101}
\]
where, in the standard unweighted coordinate realization, every coordinate of \(\Omega_E\) is
\(\sqrt{\pi_{p,m}}>0\).  Thus \(P_E\) is the orthogonal projection onto the restricted fusion
line, not merely an unnormalized rank-one operator.

`[PROVED HERE] [JOINT_PRIME_SHELL_GRADED_FUSION_CRITICALITY]`

\[
 \boxed{\quad
 [\widetilde D_{s,E},P_E]=0
 \text{ compatibly for every finite joint packet }E
 \quad\Longleftrightarrow\quad
 \operatorname{Re}s=\frac12.
 \quad}
 \tag{102}
\]

Indeed, full support makes commutation force the diagonal entries to be constant on every finite
packet.  For one fixed prime and two distinct shell depths this gives
\[
 p^{m(1-2\operatorname{Re}s)}
 =
 p^{n(1-2\operatorname{Re}s)},
\]
so \(\operatorname{Re}s=1/2\).  Conversely every entry equals \(1\) on the critical line.
The theorem retains imaginary phase.  It applies separately to the top principal normal of a
zero of any multiplicity; compatibility with all lower multiplicity jets remains part of the
source theorem, not a consequence of this scalar selector.

`[WITHDRAWN OVERSTRONG FORMULATION]` The earlier raw condition
\([D_{s,E},P_E]=0\), with \(D_{s,E}=\operatorname{diag}(d_{p,m}(s))\), is generally too rigid:
even at \(\operatorname{Re}s=1/2\), the zero-rate factor \(R_{p,m}(s)\) need not be constant.
This is the joint version of the raw-fusion correction already proved for the prime-\(2\) shell
shift.  Only the gauge-reduced degree `(99)` has critical line as its exact unitary locus.

### Frontier movement and remaining theorem

The common prime/shell fusion line required in Section 15 is now constructed unconditionally from
the ordinary-integer source.  The RH-bearing problem narrows from “find a common observation” to:

`[BOLD CONJECTURE] [XI_JOINT_INCIDENCE_GRADED_STAR_COVARIANCE]`

> The Euler--Gamma/co-Poisson continuation of the complete Xi principal-normal sheaf has, on the
> joint source frame `(77)`--`(100)`, the diagonal coordinates `(90)`, descends functorially
> through the zero-rate gauge quotient `(99)`, and preserves the source fusion projection in the
> positive multiplicative domain of that quotient.  Equivalently, the induced modular polar
> defect satisfies `(102)` on every finite joint packet before zero specialization, compatibly
> with Gamma reflection and every multiplicity jet.

Combined with `(102)`, this proves RH.

This is stronger than observing the prime and shell marginals separately, but it is not an
invented tensor coupling: the same valuation vector \(\mathbf k\) simultaneously determines
\(\tau\) and \(M\).  Hypertranscendence remains present because the marginal-plus-joint frame
`(89)` reconstructs every prime-deleted HT shell by a finite triangular transformation.

### Hostile audit

1. Least-prime and maximum-exponent distributions are classical-type arithmetic probabilities.
   Candidate-new content is their exact joint use as the fusion marginal for the prime-deleted HT
   conormal frame, not either marginal alone.
2. The joint analytic cell is no longer a fitted rescaling: `(83)`--`(86)` identify the literal
   coefficient class and its common zeta divisor.  What remains conjectural is descent of its
   positive half-density through the zero-rate gauge quotient.
3. Raw full-support Schur rigidity is a one-way selector and is false as a characterization of
   critical fibres.  Equation `(99)` is essential: the source theorem must prove functorial
   descent through its zero-rate gauge class before applying Schur rigidity.
4. Generalized-prime systems may possess analogues of \(\tau\) and \(M\).  The conjecture is
   falsified if an explicit off-line system also carries the literal joint law, analytic common
   divisor, Gamma dagger, and **graded** fusion star-covariance.
5. No Lean formalization is prioritized until the star-covariance producer is advanced.  The
   joint law and rate theorem are unconditional, but formalizing them alone would not close the
   remaining source arrow.

## Updated frontier gates

- [x] common prime/shell fusion probability constructed without tensoring
- [x] exact joint formula and both marginals proved
- [x] full support and joint shell asymptotic proved
- [x] literal joint Dirichlet shell and common-divisor lift constructed
- [x] marginal-plus-joint frame proved to retain prime-deleted HT data
- [x] joint polar likelihood rate proved
- [x] raw fusion formulation hostile-tested and withdrawn
- [x] exact zero-rate joint gauge separated from modular degree
- [x] finite-packet gauge-reduced fusion criticality equivalence proved
- [x] prove joint normalization is the literal joint coefficient continuation
- [ ] transport the joint half-density through Euler--Gamma/co-Poisson completion
- [ ] construct the zero-rate gauge quotient as a source object
- [ ] prove graded positive multiplicative-domain/star covariance
- [ ] prove Gamma/reflection and multiplicity compatibility
- [ ] audit explicit generalized-prime off-line systems against the joint hypothesis
- [ ] unconditional RH proof and Lean formalization

- 2026-07-30 — Constructed the missing common fusion line.  On the source valuation space, least
  occupied prime and maximum valuation exponent have a full-support joint law \(\pi_{p,m}\).
  Its marginals are exactly the Wold first-defect weights and positive HT exponent-shell weights.
  The literal difference of adjacent prime-deleted shells gives the joint Dirichlet cell
  \({\mathscr J}_{p,m}=\zeta B_{p,m}\), with \(B_{p,m}(1)=\pi_{p,m}\) and polar rate
  \((1-2\Re s)\log p\).  Hostile audit then refuted raw fusion scalarity as a critical-line
  characterization and isolated the exact bounded gauge `(96)`.  Graded fusion star-covariance
  on the resulting modular degree would force every Xi zero onto the critical line.

## 17. The fusion line is generated by alternating source coarse-grainings

The rank-one fusion line in `(100)` need not be inserted as an additional source observable.  It
is the meet of two canonical conditional-expectation ranges generated by the two arithmetic
marginals in `(78)`.

Put
\[
 h_m=\sum_p\pi_{p,m}=H_{2,m}(1).
\]
On \({\cal H}_{\rm joint}\), define
\[
\begin{aligned}
 (E_\tau f)(p,m)
  &=
  {1\over w_p}\sum_{n\geq1}\pi_{p,n}f(p,n),\\
 (E_M f)(p,m)
  &=
  {1\over h_m}\sum_q\pi_{q,m}f(q,m).
\end{aligned}
\tag{103}
\]
These are the orthogonal conditional-expectation projections onto functions of \(\tau\) and
functions of \(M\), respectively.

`[PROVED HERE] [JOINT_INCIDENCE_ALTERNATING_EXPECTATION_LIOUVILLE_LAW]`

\[
 \operatorname{Ran}E_\tau\cap\operatorname{Ran}E_M
 =
 \mathbb C1.
 \tag{104}
\]
Indeed, an element of the intersection has the form \(u(p)=v(m)\) for
\(\pi_{p,m}\)-almost every pair.  Full support of \(\pi\) makes this equality hold for every
\((p,m)\), so all values of \(u\) and \(v\) are equal.

The alternating-projection theorem now gives
\[
 \boxed{\quad
  (E_\tau E_M)^n
  \ \xrightarrow[n\to\infty]{\rm strong}\
  P_{\rm joint}.
 \quad}
 \tag{105}
\]
Thus complete fusion is generated by repeatedly forgetting shell depth and first occupied prime
in alternating order.  It is not a tensor coupling or an independently chosen rank-one state.

There is an equivalent reversible Markov form.  Let
\[
\begin{aligned}
 {\cal H}_\tau&=\ell^2(\mathcal P,w),&
 {\cal H}_M&=\ell^2(\mathbb N_{>0},h),\\
 (Ku)(m)&={1\over h_m}\sum_p\pi_{p,m}u(p),&
 (K^\ast v)(p)&={1\over w_p}\sum_m\pi_{p,m}v(m).
\end{aligned}
\tag{106}
\]
Then \(K\) and \(K^\ast\) are the two Bayes conditional-expectation contractions,
\[
 K1=1,\qquad K^\ast1=1,
 \tag{107}
\]
and
\[
 \boxed{\quad
  \ker(I-K^\ast K)=\mathbb C1,
  \qquad
  \ker(I-KK^\ast)=\mathbb C1.
 \quad}
 \tag{108}
\]
For example, if \(K^\ast Ku=u\), then
\[
 \|Ku\|^2
 =
 \langle u,K^\ast Ku\rangle
 =
 \|u\|^2.
\]
Equality in the conditional-expectation contraction says that \(u(\tau)\) is also
\(M\)-measurable.  Equation `(104)` makes it constant.  The other identity is symmetric.

### The joint Bayes operator has a strict spectral gap

The arithmetic joint law makes \(K\) compact, not merely contractive.

`[PROVED HERE] [PRIME_SHELL_BAYES_HILBERT_SCHMIDT_GAP]`

\[
 \boxed{\quad
 \|K\|_{\rm HS}^2
 =
 \sum_{p,m}{\pi_{p,m}^2\over w_ph_m}
 \leq 6\zeta(2).
 \quad}
 \tag{109}
\]

To prove the bound, first note that the event
\[
 k_2=m,\qquad k_q\leq m\quad(q>2)
\]
gives, for every \(m\geq1\),
\[
 h_m
 \geq
 2^{-m-1}\prod_{q>2}(1-q^{-2})
 =
 {2^{1-m}\over3\zeta(2)}
 =
 {2\over3\zeta(2)}\,2^{-m}.
 \tag{110}
\]
Conditioned on \(\tau=p\), the \(p\)-valuation is geometric conditioned to be positive and all
later valuations keep their original laws.  For \(m\geq2\),
\[
\begin{aligned}
 \mathbb P(M=m\mid\tau=p)
 &\leq
 \mathbb P(M\geq m\mid\tau=p)\\
 &\leq
 p^{-(m-1)}+\sum_{q>p}q^{-m}\\
 &\leq
 2^{1-m}+\sum_{n\geq3}n^{-m}\\
 &\leq
 2\cdot2^{-m}+4\cdot3^{-m}
 <4\cdot2^{-m}.
\end{aligned}
\tag{111}
\]
For \(m=1\), the same conditional probability is at most \(1\), while
\(h_1=1/\zeta(2)\).  Equations `(110)`--`(111)` therefore give the uniform likelihood bound
\[
 {\pi_{p,m}\over w_ph_m}
 =
 {\mathbb P(M=m\mid\tau=p)\over h_m}
 \leq6\zeta(2).
 \tag{112}
\]
Multiplying `(112)` by \(\pi_{p,m}\) and summing proves `(109)`.

Since \(K1=1\), \(\|K\|=1\).  Equation `(108)` makes the singular value \(1\) simple.  Compactness
then supplies a number \(0\leq\vartheta<1\) such that
\[
 \left\|(K^\ast K)^n-P_\tau\right\|
 \leq\vartheta^n,
 \qquad
 \left\|(KK^\ast)^n-P_M\right\|
 \leq\vartheta^n,
 \tag{113}
\]
where \(P_\tau,P_M\) are the constant projections on the two marginal spaces.  Equivalently,
\[
 \left\|(E_\tau E_ME_\tau)^n-P_{\rm joint}\right\|
 \leq\vartheta^n
 \quad\text{on }\operatorname{Ran}E_\tau,
 \tag{114}
\]
and symmetrically with \(\tau,M\) reversed.

Consequently the Liouville law is stable:
\[
 \|u-\mathbb E_wu\|_2
 \leq
 {1\over1-\vartheta}
 \|u-K^\ast Ku\|_2,
 \tag{115}
\]
with the analogous inequality on the shell marginal.  Thus any proposed source comparison which
commutes with the two Bayes coarse-grainings only approximately must pay a quantitatively
nonzero prime/shell discrepancy unless its marginal polar degree is close to constant.

### Complete-incidence Bayes curvature

For \(f\in{\cal H}_{\rm joint}\), define
\[
 {\mathfrak B}(f)
 =
 \|(I-E_\tau)f\|_2^2+\|(I-E_M)f\|_2^2.
 \tag{115a}
\]
The Friedrichs cosine of the two conditional-expectation ranges is
\[
 \|E_\tau E_M-P_{\rm joint}\|
 =
 \sqrt{\vartheta}<1.
\]
The standard two-projection decomposition, together with `(104)`, therefore gives the coercive
Poincaré law
\[
 \boxed{\quad
 {\mathfrak B}(f)
 \geq
 (1-\sqrt{\vartheta})
 \|f-\mathbb E_\pi(f)1\|_2^2.
 \quad}
 \tag{115b}
\]
In particular,
\[
 {\mathfrak B}(f)=0
 \quad\Longleftrightarrow\quad
 f\in\operatorname{Ran}E_\tau\cap\operatorname{Ran}E_M
 \quad\Longleftrightarrow\quad
 f\text{ is constant}.
 \tag{115c}
\]

For a bounded diagonal observable \(M_f\), this curvature is exactly its two vacuum
Beck--Chevalley defects:
\[
 {\mathfrak B}(f)
 =
 \|[M_f,E_\tau]1\|_2^2
 +
 \|[M_f,E_M]1\|_2^2.
 \tag{115d}
\]
Thus full operator commutation is sufficient but not necessary.  Vanishing only on the source
fusion vector already forces scalarity.

Applied to the gauge-reduced polar intensity `(117)`,
\[
 \boxed{\quad
 {\mathfrak B}(r_s)=0
 \quad\Longleftrightarrow\quad
 \operatorname{Re}s=\frac12.
 \quad}
 \tag{115e}
\]
This turns the missing “opposite sign” into a zero-curvature problem.  The explicit off-line
positive Euler/orientation systems may have positive scalar Ward currents, but a source carrying
the complete ordinary-prime joint incidence must additionally account for the nonnegative
Bayes curvature `(115a)`.

### Complete-incidence commutant theorem

Let \(r\in L^\infty(\pi)\) and let \(M_r\) be multiplication by \(r\) on
\({\cal H}_{\rm joint}\).  Equations `(104)`--`(105)` give
\[
 [M_r,E_\tau]=[M_r,E_M]=0
 \quad\Longrightarrow\quad
 [M_r,P_{\rm joint}]=0
 \quad\Longrightarrow\quad
 r\text{ is constant }\pi\text{-almost everywhere}.
 \tag{116}
\]
The last implication follows by applying the commutator to \(1\):
\[
 r=M_rP_{\rm joint}1=P_{\rm joint}M_r1=\mathbb E_\pi(r)\,1.
\]

For the gauge-reduced right-chart polar multiplier in `(99)`,
\[
 r_s(p,m)=p^{m(1-2\operatorname{Re}s)},
 \qquad \operatorname{Re}s\geq\frac12,
 \tag{117}
\]
boundedness is automatic.  Hence
\[
 \boxed{\quad
 [M_{r_s},E_\tau]=[M_{r_s},E_M]=0
 \quad\Longleftrightarrow\quad
 \operatorname{Re}s=\frac12.
 \quad}
 \tag{118}
\]
The reverse implication is immediate from \(r_s=1\).  For the forward implication, `(116)` makes
\(r_s\) constant, and comparison of two distinct depths at one prime forces
\(1-2\operatorname{Re}s=0\).

This replaces the unexplained fusion-projection hypothesis by two concrete source squares:

```text
forget maximum depth after continuation
  = continue after forgetting maximum depth;

forget first occupied prime after continuation
  = continue after forgetting first occupied prime.
```

If both squares hold for the positive gauge-reduced principal normal, their alternating strong
limit supplies fusion covariance automatically.

### Universal interpretation

The corpus's apparently different fractures are failures of one complete-incidence law:

```text
finite truncation leakage:
  one conditional expectation is cut off before the other;

chainwise Wold--Kummer transmutation:
  one ordered path through the two Bayes coarse-grainings;

full-prime-nerve conditioning curvature:
  ordinary linear interchange forgets the Bayes weights;

ambient adelic L2:
  both conditional expectations exist, but divisor conormals are not normal multipliers;

off-line Rees/Kakutani sector:
  one reflected polar multiplier is bounded and the other leaves the normal sector;

full-support Schur rigidity:
  the rank-one shadow of the alternating strong limit;

hypertranscendence:
  no finite differential observer contains the complete alternating incidence record.
```

What all of these results are saying is:

> **Criticality is triviality of the complete arithmetic observation boundary.**
>
> A source-normal polar displacement that is natural for both complementary ordinary-integer
> coarse-grainings is forced into their common Liouville boundary.  That boundary consists only
> of constants, so its modular degree is zero.

This is a universal law for any full-support bipartite source incidence, not only zeta.  The
Riemann-specific content is that the two sides are the literal first-prime and maximum-exponent
marginals of ordinary integers, and that the Xi principal normal must descend as one normal
positive observable natural for both.

### Sharpened RH-bearing conjecture

`[BOLD CONJECTURE] [XI_COMPLETE_INCIDENCE_WARD_FLATNESS]`

> Before divisor specialization, the Euler--Gamma/co-Poisson continuation of the Xi
> principal-normal sheaf extends to the source-normal/Rees completion of the joint valuation
> incidence `(77)`.  In the right chart, its positive polar part is the bounded gauge-reduced
> intensity \(r_\rho\) in `(117)`.  The completed factorized Ward identity makes that intensity
> flat for the two complementary source observations:
> \[
>  {\mathfrak B}(r_\rho)=0,
> \]
> compatibly with every finite multiplicity jet.

Equation `(115e)` then forces every right-half member of a nontrivial zero orbit onto the
critical line, and functional-equation/Schwarz reflection gives RH.

The two full Bayes/Beck--Chevalley operator squares displayed above are one stronger provider of
Ward flatness, but they are not required.  It is enough to prove their two vacuum defects vanish,
or directly identify the completed Ward energy with `(115a)` and prove its source value is zero.
This is strictly weaker than graded multiplicative-domain membership.

This is still an RH-bearing source conjecture.  The advance is a smaller, source-generated open
core:

1. construct the source-normal joint-incidence completion on which \(E_\tau,E_M\) remain
   continuous;
2. identify the completed joint Dirichlet principal normal with the multiplier class `(99)`;
3. identify its completed Euler--Gamma Ward energy with the Bayes curvature `(115a)`;
4. prove source Ward flatness before divisor localization;
5. prove reflected conormal conservativity and multiplicity-jet strictness.

The conjecture is killed by an explicit off-line completed Euler system satisfying all of these
items.  Scalar positivity, functional equation, hypertranscendence, raw orientation, or separate
prime/shell marginal naturality do not imply zero joint Bayes curvature.

### Collision boundary

Alternating orthogonal projections, Gibbs/Bayes conditional expectations, and the fixed-point
description in `(104)`--`(108)` are parent mathematics.  The corpus already predicted a
pair-face/triple-coherence comparison and already warned that raw fusion covariance is too rigid.
The content added here is narrower:

1. the exact arithmetic joint law `(77)` makes the two conditional expectations literal source
   maps rather than abstract fibres;
2. full support proves their common boundary is exactly the fusion line;
3. alternating projection constructs that line from the two marginals;
4. the arbitrary graded-fusion premise is replaced by one coercive sum-of-squares Ward curvature;
5. full operator base change is demoted to an optional stronger provider.

No external priority claim is made for the abstract theorem.  The candidate-new mathematical
object is the Xi source-normal joint-incidence comparison in the boxed conjecture.

- 2026-07-30 — Proved that the common prime/shell fusion line is the alternating strong limit of
  the two literal source conditional expectations.  Reframed the RH-bearing producer as two
  weighted Bayes/Beck--Chevalley defects and then as one coercive Ward curvature.  This supplies
  a source origin for the fusion projection and identifies criticality with triviality of the
  complete-incidence observation boundary.

## 18. Jump: the pole is a sector budget, not merely a singularity

The local flatness conjecture above is still too close to the desired conclusion.  It asks every
zero conormal to have zero Bayes curvature and then invokes a theorem saying that zero curvature
is criticality.  The corpus points to a more global producer.

Three independently obtained discontinuous invariants have the same support:

1. Kakutani equivalence changes from equality of sectors to mutual singularity at every nonzero
   modular displacement, however small;
2. a generic off-line quartet contributes exactly two negative directions to its isolated Weil
   block;
3. positive Euler quartet surgery pays exactly two extra pole orders at the Euler point.

The first is a cofinal sector-change index, the second is its divisor index, and the third is its
source budget.  The joint incidence theorem adds the missing zeroth term: the ordinary-integer
source has exactly one common Bayes vacuum,
\[
 b_\zeta
 :=
 \dim\bigl(
   \operatorname{Ran}E_\tau\cap\operatorname{Ran}E_M
 \bigr)
 =1.
 \tag{119}
\]
This suggests that the simple pole is already fully occupied by the source vacuum.  There is no
remaining source index in which an off-line sector can live.

### Complete-source sector-budget index law

Let \(F\) be a factorization-complete positive discrete Euler source with reflected entire
completion.  Write
\[
 r_F=-\operatorname{ord}_{s=1}F
 \tag{120}
\]
for its Euler-pole order, \(b_F\) for the dimension of its complete-incidence source boundary,
defined before divisor localization, and \(\mathcal W_F\) for its completed Weil form.  The
integer \(b_F\) is not the number of zeros, a fitted correction, or a declared pole baseline; it
is the dimension of the common fixed space of the source conditional expectations, as in
`(119)`.

`[BOLD CONJECTURE] [COMPLETE_SOURCE_SECTOR_BUDGET_INDEX_LAW]`

> If the polarized HT conormal reporter extends conservatively through the strict cofinal
> source completion, then
> \[
>  \boxed{\qquad
>   \operatorname{ind}_{-}(\mathcal W_F)
>   \leq r_F-b_F.
>  \qquad}
>  \tag{121}
> \]
> Equivalently, every nonunitary cofinal sector change consumes source pole excess.  Critical
> divisor fibres consume no excess; a generic off-line quartet of multiplicity \(d\) consumes
> \(2d\) units.

The first intended operator statement was stronger:
\[
 \mathcal W_F=A_F^\ast A_F-B_F^\ast B_F,
 \qquad
 \dim\overline{\operatorname{Ran}B_F}\leq r_F-b_F.
 \tag{122}
\]
Here \(A_F\) was to be generated by the complete prime/depth Bayes gradient and the positive
Euler--Gamma current, while the negative port \(B_F\) was to be the raw cofinal
prime-infinity remainder
\[
 {\mathcal R}_{P,m}
 =
 E_{P^+}H_{P^+,m}
 \tag{123}
\]
and the excess Euler-pole jets.  The next subsection refutes this raw finite-rank interpretation.
Only a cohomological/transgressed version of `(122)` survives.

### Why this would prove RH without assuming local Ward flatness

For the Riemann source,
\[
 r_\zeta=1,\qquad b_\zeta=1.
 \tag{124}
\]
Hence `(121)` gives
\[
 \operatorname{ind}_{-}(\mathcal W_\zeta)=0.
 \tag{125}
\]
Weil positivity then gives RH.  More concretely, if only finitely many zero orbits were off the
line, Bombieri's index theorem and the packet calculation in
`euler-ward-weil-index-law/main.tex` give
\[
 \operatorname{ind}_{-}(\mathcal W_\zeta)
 =
 2\sum_{\substack{\mathcal O\ {\rm off\ line}\\
                   \operatorname{Re}\rho_{\mathcal O}>1/2}}
 d_{\mathcal O}.
 \tag{126}
\]
One quartet already contradicts `(125)`.  If there are infinitely many off-line orbits, finite
packet restrictions give arbitrarily large negative index and contradict the finite right side
of `(121)`.

Thus `[XI_COMPLETE_INCIDENCE_WARD_FLATNESS]` becomes a corollary rather than the producer:
zero negative budget gives RH, RH gives \(r_\rho=1\), and `(115e)` gives
\(\mathfrak B(r_\rho)=0\).

### Calibration against the explicit off-line Euler systems

The finite positive quartet surgeries do not falsify `(121)`.  They calibrate its sharp
constant.  For a packet \(J\),
\[
 \Delta r_F=2|J|,
 \qquad
 \Delta\operatorname{ind}_{-}(\mathcal W_F)=2|J|,
 \qquad
 {Q_{\rm Julia}(J)\over4\pi}=2|J|.
 \tag{127}
\]
They manufacture exactly the pole capacity needed by their off-line sectors.  This explains why
positive source, reflection, entire completion, hypertranscendence, and positive unsquared
orientation all survive: the deformation enlarges the negative boundary port rather than
violating source index conservation.

A hypothetical off-line zero intrinsic to \(\zeta\) is different.  It would demand two negative
sector units without changing either side of `(124)`.  The missing theorem is therefore not an
opposite pointwise Julia sign.  It is strict global conservation of the finite pole-boundary
port.

### Universal reinterpretation of the corpus

```text
finite Euler truncations:
  every sector change is internal; the cofinal index is invisible;

Kakutani/Hellinger fracture:
  every nonzero radial degree becomes a genuine sector-change class;

Wold and Kummer leakage:
  two boundary charts of the same escaping negative port;

Gamma first-trace anomaly:
  norm growth of its evaluation map;

joint Bayes spectral gap:
  the source vacuum has multiplicity one and no hidden zero-energy component;

Weil negative squares:
  divisor-side realization of the sector-change index;

Julia--Ward quantization:
  boundary-current realization of the same integer;

Euler pole excess:
  source capacity available to carry that integer;

hypertranscendence:
  conservativity of the conormal reporter, preventing the index from being killed by a finite
  differential quotient;

continuous generalized-prime surgery:
  an operation which adds a negative port and pays exactly for it;

ambient adelic Hilbert space:
  keeps the positive source but deletes the singular index-bearing conormal;

large irregular/Krein completion:
  keeps every conormal but does not impose the source pole budget.
```

The resulting universal statement is:

> **A completed positive source cannot contain more nonunitary divisor sectors than it has
> source-boundary ports.**
>
> Critical-line localization is the zero-excess case of this sector-capacity law.

This is stronger conceptually than “zeros should be eigenvalues of a self-adjoint operator.”
Self-adjointness is the special case \(r_F-b_F=0\).  The general object is source-rigged
Pontryagin/Fredholm geometry with a computable negative-index budget.

### New conditional corollaries

1. **One-pole principle.**  Any connected source satisfying the hypotheses with one simple Euler
   pole has no off-line divisor orbit.
2. **Finite-exception exclusion.**  No separate density or simplicity theorem is needed:
   one generic quartet already costs two units.
3. **Infinite-exception exclusion.**  Arbitrarily large finite Weil blocks contradict the fixed
   source budget.
4. **Multiplicity safety.**  An orbit of multiplicity \(d\) costs \(2d\); no simple-zero
   hypothesis enters.
5. **Surgery sharpness.**  Positive quartet surgery saturates the budget increment rather than
   evading it.
6. **GRH extension target.**  A connected positive discrete ideal source with simple pole and the
   same strict incidence factorization would satisfy its corresponding critical-line theorem.
7. **Third-completion specification.**  The required completion must retain the principal
   conormal and turn the infinite raw boundary into a strict complex whose *cohomological*
   negative index is at most \(r_F-b_F\).  “Retain all fibres” and “be Hausdorff” are no longer
   the whole specification.

### Raw pole-port rank is false at infinity

`[PROVED HERE] [PRIME_INFINITY_BOUNDARY_INFINITE_RANK]`

Fix \(s\) with \(\operatorname{Re}s>1/2\).  For each prime \(q\), let \(P=q^-\) be its predecessor
cutoff and view
\[
 R_q(s)=\bigl({\mathcal R}_{q^-,m}(s)\bigr)_{m\geq1}
 =\bigl(E_q(s)H_{q,m}(s)\bigr)_{m\geq1}
 \tag{128}
\]
as a depth sequence.  Then the family \(\{R_q(s):q\ {\rm prime}\}\) is linearly independent.

Indeed, the prime-resolved shell asymptotic gives
\[
 {\mathcal R}_{q^-,m}(s)
 =
 E_q(s)(1-q^{-s})q^{-ms}
 +O\!\left((q^+)^{-m\operatorname{Re}s}\right).
 \tag{129}
\]
The leading coefficient is nonzero because \(\operatorname{Re}s>0\).  Suppose a finite relation
\[
 \sum_{j=1}^N c_jR_{q_j}(s)=0,
 \qquad q_1<\cdots<q_N.
 \tag{130}
\]
Multiply its \(m\)-th coordinate by \(q_1^{ms}\) and let \(m\to\infty\).  Every term with
\(j>1\) tends to zero in modulus, while `(129)` makes the first term tend to
\[
 c_1E_{q_1}(s)(1-q_1^{-s}).
 \]
Hence \(c_1=0\).  Induction proves every \(c_j=0\).

Consequently the raw cofinal remainder cannot be the finite pole port in `(122)`.  One column at
each finite cutoff becomes an infinite-rank family after all cutoffs are retained.  This is the
same finite-to-infinite trap seen in the Wold, Kummer, Gamma, and completed-window-index no-gos.

The strongest surviving operator target is therefore
\[
 \boxed{\quad
 \mathcal W_F
 =
 A_F^\ast A_F
 -
 (\Theta_F{\mathcal R}_F)^\ast(\Theta_F{\mathcal R}_F),
 \qquad
 \dim\overline{\operatorname{Ran}(\Theta_F{\mathcal R}_F)}
 \leq r_F-b_F.
 \quad}
 \tag{131}
\]
Here \({\mathcal R}_F\) is the infinite-rank raw boundary complex and
\(\Theta_F\) must be a source-defined strict transgression to its finite pole-jet cohomology.
It cannot be a scalar residue reader, ordinary all-place multiplier, divisor monodromy, or a
post-hoc projection onto the desired negative space: the corpus has already proved those
realizations split, collapse, become nonclosable off RH, or read the divisor itself.

Equation `(131)`, unlike raw `(122)`, is compatible with infinite boundary data and a finite
index.  It implies `(121)` by the min--max principle.  Constructing \(\Theta_F\) before divisor
localization is now the exact missing mechanism.

### Canonical mixed modular transgression on the coherent conormal orbit

The joint prime--depth frame gives one explicit part of the previously unnamed
\(\Theta_F\).  For the gauge-reduced polar intensity in `(99)`, put
\[
 \ell_s(p,m)
 :=
 \log \widetilde d_{p,m}(s)
 =
 (1-2\operatorname{Re}s)m\log p.
 \tag{132}
\]
For distinct primes \(p,q\) and distinct depths \(m,n\), define the normalized rectangular
curvature
\[
 {\mathfrak T}_{p,q;m,n}(\ell)
 :=
 {\ell(p,m)-\ell(p,n)-\ell(q,m)+\ell(q,n)
  \over
  (\log p-\log q)(m-n)}.
 \tag{133}
\]

`[PROVED HERE] [JOINT_MIXED_MODULAR_CURVATURE]`

\[
 \boxed{\qquad
 {\mathfrak T}_{p,q;m,n}(\ell_s)
 =
 1-2\operatorname{Re}s
 \qquad}
 \tag{134}
\]
for every such rectangle.  This is immediate from `(132)`: the numerator is
\[
 (1-2\operatorname{Re}s)(m-n)(\log p-\log q).
 \]
For a top conormal of multiplicity \(d\), tensor-power functoriality multiplies `(134)` by \(d\).
Reflection \(s\mapsto1-\overline s\) negates it.  Hence
\[
 {\mathfrak T}(\ell_s)=0
 \quad\Longleftrightarrow\quad
 \operatorname{Re}s=\frac12.
 \tag{135}
\]

The rectangular form is strictly more gauge-resistant than a one-axis slope.  It kills every
separated change
\[
 \ell(p,m)\longmapsto\ell(p,m)+u(p)+v(m)
 \tag{136}
\]
exactly.  If a residual two-variable gauge \(b(p,m)\) has mixed rectangular increment
\[
 \Delta_{p,q}\Delta_{m,n}b
 =
 o\!\left(
   |\log p-\log q|\,|m-n|
 \right)
 \tag{137}
\]
cofinally, then its contribution to `(133)` tends to zero.  In particular this holds for a
uniformly bounded residual along rectangles whose two side lengths tend to infinity.

Equation `(134)` is the first concrete candidate for the strict transgression in `(131)`: the raw
prime-infinity boundary is infinite-rank by `(128)`--`(130)`, but its coherent radial conormal
orbit has a one-dimensional mixed modular curvature after separated source gauges are removed.
This is not a finite-rank assertion about the raw boundary and not a post-hoc projection onto a
Weil negative space.

Two gaps must remain explicit.

1. The exact zero-rate gauge \(R_{p,m}(s)\) in `(99)` is only controlled depthwise at each fixed
   prime.  It has not been proved to satisfy the uniform mixed condition `(137)`.  Thus `(134)` is
   unconditional on the already-defined gauge-reduced degree, while construction of that quotient
   as a source object remains open.
2. A scalar mixed curvature does not imply the Weil factorization `(131)`.  The corpus already
   contains the one-axis modular character
   \((\operatorname{Re}s-\tfrac12)\log p\); `(134)` is its exact joint prime--depth,
   separated-gauge realization.  It is a new bridge in this card, not a claim of new general
   mathematics and not an RH proof.

### Revised universal law: curvature length, not boundary rank

The infinity audit changes the type of the sector-budget conjecture.  The proposed finite object
cannot be a raw boundary port.  It must be the source-relative length of nonzero mixed modular
curvature classes in a controlled cohomology of the infinite boundary complex.

Write provisionally
\[
 H^2_{\mathrm{mod}}(F)
 \tag{138}
\]
for the source-constructed controlled curvature module, formed before divisor localization, and
\(\operatorname{len}_{\ne0}H^2_{\mathrm{mod}}(F)\) for the multiplicity length of its nonzero
reflection-oriented conormal classes.  The sharpened conjectural chain is
\[
 \boxed{\quad
 \operatorname{ind}_{-}(\mathcal W_F)
 =
 \operatorname{len}_{\ne0}H^2_{\mathrm{mod}}(F)
 \le r_F-b_F.
 \quad}
 \tag{139}
\]
The first equality is an anomaly-matching realization theorem; the second is the source
pole--vacuum Euler-characteristic bound.  Formula `(134)` fixes what an individual radial class
must be:
\[
 [N_\rho]\longmapsto
 d_\rho(1-2\operatorname{Re}\rho)\,[\eta_{\mathrm{prime}}\smile\eta_{\mathrm{depth}}].
 \tag{140}
\]
The class is nonzero exactly off the critical line, while the Weil realization counts its
multiplicity rather than the size of the real coefficient.

For the target-defined zeta divisor, the first equality in `(139)` already has an exact corpus
realization.  Define
\[
 K^{\mathrm{curv}}_+
 :=
 \bigoplus_{\substack{\Xi(\rho)=0\\ \operatorname{Re}\rho>1/2}}
 \mathbb C^{d_\rho},
 \tag{141}
\]
where \(d_\rho\) is zero multiplicity.  The CCM aperture--Morse/Hardy-model exhaustion theorem,
together with `(135)`, gives
\[
 \dim K^{\mathrm{curv}}_+
 =
 \sum_{\substack{\Xi(\rho)=0\\ \operatorname{Re}\rho>1/2}}d_\rho
 =
 \operatorname{ind}_{-}(\mathcal G_\Xi)
 =
 \sup_{a>0}\kappa(a),
 \tag{142}
\]
with \(+\infty\) allowed.  For a finite rational quartet packet this reduces to the Ward
calibration `(127)`.  Thus the target-side anomaly matching and multiplicity accounting are
already closed: nonzero mixed modular curvature and Weil negative directions carry exactly the
same off-line divisor multiplicity.

This is not yet a source proof.  Definition `(141)` reads the zero divisor and is therefore
circular as a producer.  The remaining bridge is the pre-divisor source identification
\[
 H^2_{\mathrm{mod}}(\zeta)
 \longrightarrow K^{\mathrm{curv}}_+
 \tag{143}
\]
which must be conservative and multiplicity-faithful, together with the source bound
\(\operatorname{len}_{\ne0}H^2_{\mathrm{mod}}(\zeta)\le r_\zeta-b_\zeta=0\).
The first equality of `(139)` is proved only after divisor localization through `(142)`; its
source-relative realization and the second inequality remain open.

For zeta, \(r_\zeta-b_\zeta=0\), so `(139)` would force every class `(140)` to vanish and hence
prove RH.  A positive quartet surgery adds two oriented curvature classes and two pole units, so
the calibration `(127)` remains exact.  The missing theorem is now precise:

1. construct \(H^2_{\mathrm{mod}}(F)\) from the literal infinite prime--depth boundary and its
   source bornology;
2. prove that the gauge-reduced Xi conormal maps to `(140)` without reading its zero location into
   the construction;
3. prove HT shell conservativity and multiplicity faithfulness for this map;
4. prove the source length bound in `(139)` from the full Euler--Gamma/Poisson comparison;
5. identify its source realization with the target index transport `(142)`, without using the
   target divisor to define the source module.

This formulation is compatible with the CCM infinite-boundary Schur law: a finite effective index
may be computed only after the exact infinite boundary resolvent is retained.  Merely naming
\(H^2_{\mathrm{mod}}(F)\), a derived limit, a Tate object, or a Fredholm complex does not establish
any item above.

### Exact proof core

The next theorem is not `(121)` as an axiom.  Raw factorization `(122)` is false by `(128)`--`(130)`.
The target is the transgressed source factorization `(131)`.  Required construction:

1. at finite prime cutoff \(P\), build the Euler--Gamma/Weil Gram identity using the literal
   joint cells \(\mathscr J_{p,m}\);
2. separate its positive term through the two conditional-expectation gradients;
3. assemble the independent columns \(\mathcal R_{P,m}\) into their full strict boundary complex;
4. construct a source-defined transgression \(\Theta_F\) to pole-jet cohomology and prove the
   rank bound \(r_F-b_F\) there, without asserting a rank bound for the raw boundary;
5. prove that every negative term factors through \(\Theta_F\mathcal R_F\);
6. pass to a closed strict graph while preserving the HT principal conormal and every
   multiplicity jet;
7. identify the limiting Hermitian form with the full Weil form, not merely its isolated packet
   blocks.

This replaces the unexplained local assertion “the Xi polar degree is Bayes-flat” by one global
finite-to-infinite factorization problem with an independently fixed rank budget.

### Hostile audit

1. `(121)` is unproved and load-bearing.  At \(F=\zeta\) it implies RH; it must not be described
   as a consequence of pole order alone.
2. Euler product plus a simple pole is insufficient.  Beurling systems can have a simple pole and
   critical-strip zeros, while Helson Euler products can realize nearly arbitrary zeros and
   poles.  The discrete ordinary-factorization incidence, positive polarization, reflected
   completion, and strict conormal factorization in `(131)` are essential.
3. Functional equation alone is insufficient.  It pairs sector changes but does not bound their
   number.
4. The finite surgery identity `(127)` proves calibration only for inserted rational packets.  It
   does not prove the global rank bound for the undeformed zeta source.
5. Generalized Nevanlinna/Pontryagin negative-square theory, Bombieri's finite-exception index
   theorem, and the general demand for a source-built negative-index bound are parent mathematics
   and already appear in the corpus.  The content added here is the literal joint boundary
   `(123)`, its infinite-rank theorem `(128)`--`(130)`, and the resulting specification of a
   nontrivial strict transgression `(131)`.
6. The number \(b_F\) must be computed from the source before divisor localization.  Defining it
   by subtracting the desired negative index would make `(121)` circular.
7. A large Krein target can always retain off-line packets.  Without the cohomological
   length/rank estimate in `(131)` and `(139)` it is not the third completion.
8. A proof only for each finite cutoff is insufficient: all finite source sectors are equivalent,
   so the decisive index appears only in the strict cofinal graph.
9. The retired `completed-source-window-index-amplifier.md` already proves that ordinary
   all-place multipliers collapse, Banach and \(K\)-theory unit-tail extensions split, and the
   canonical residue graph is nonclosable off RH.  Calling \(\Theta_F\) any of those objects would
   be rediscovery, not a new route.

Literature boundary used in this audit:

- Enrico Bombieri, *Remarks on Weil's quadratic functional in the theory of prime numbers, I*,
  https://eudml.org/doc/252338;
- Krein--Langer generalized Nevanlinna theory, where negative squares count generalized
  nonpositive-type poles and zeros;
- T. W. Hilberdink and M. L. Lapidus, *Beurling Zeta Functions, Generalised Primes, and Fractal
  Membranes*, https://arxiv.org/abs/math/0410270;
- I. Bochkov and R. Romanov, *On zeroes and poles of Helson zeta functions*,
  https://arxiv.org/abs/2106.15949.

- 2026-07-30 — Replaced local Ward-flatness as the apex producer by the
  complete-source sector-budget conjecture.  The new mechanism identifies the Kakutani sector
  jump, Weil negative index, Julia charge, and Euler pole excess as four realizations of one
  cofinal integer.  This first version proposed a finite raw pole-boundary port and the
  factorization/rank theorem `(122)`; the subsequent infinity audit refuted that realization.
- 2026-07-30 — Hostile infinity audit refuted the raw finite pole-port model: the cutoff
  remainders have distinct prime-exponential depth rates and are linearly independent.  Replaced
  `(122)` by the strict-transgression target `(131)`.  The source must collapse infinite raw
  boundary *cohomologically*, not by a finite-rank assertion on the boundary itself.
- 2026-07-30 — Constructed the exact mixed modular transgression `(133)`--`(135)` on the
  gauge-reduced joint conormal orbit.  It recovers \(1-2\operatorname{Re}s\), kills separated
  prime/depth gauges, and changes sign under reflection.  Replaced finite-port language by the
  curvature-length anomaly-matching target `(139)`.  This identifies the correct type of the
  missing source theorem but does not prove its source construction, length bound, Weil
  realization, or RH.

## 19. Correction and jump: off-line displacement is a secondary boundary anomaly

The word *curvature* in `(133)` must not be confused with the exterior or Spencer curvature in the
HT constraint-curvature integration stack.  Put
\[
 a_s:=1-2\operatorname{Re}s,\qquad x_p:=\log p.
\]
Then the gauge-reduced logarithmic degree is the globally defined bilinear potential
\[
 \ell_s(p,m)=a_s x_p m.                                  \tag{144}
\]
Its mixed Hessian is nonzero when \(a_s\ne0\), but the potential itself exists at every finite
prime--depth stage.  In particular, exactness of an HT total one-form, or the formal identity
\(d_{\rm tot}^2=0\), does **not** force `(134)` to vanish.  Identifying these two notions of
curvature would be a false RH proof.

What `(133)` detects is instead failure of the exact potential `(144)` to remain negligible at
the cofinal boundary.  Fix a base prime \(p_0\).  On every finite rectangle,
\[
\begin{aligned}
 &\ell_s(P,M)-\ell_s(P,0)-\ell_s(p_0,M)+\ell_s(p_0,0)\\
 &\hspace{35mm}
 =a_s(\log P-\log p_0)M.                                \tag{145}
\end{aligned}
\]
Therefore the normalized mixed Stokes boundary density
\[
 \partial_{\infty}^{\rm mix}\ell
 :=
 \lim_{\substack{P\to\infty\\M\to\infty}}
 {\ell(P,M)-\ell(P,0)-\ell(p_0,M)+\ell(p_0,0)
  \over(\log P-\log p_0)M}                              \tag{146}
\]
exists for `(144)` and satisfies
\[
 \boxed{\quad
 \partial_{\infty}^{\rm mix}\ell_s
 =1-2\operatorname{Re}s.
 \quad}                                                  \tag{147}
\]
It is unchanged by separated gauges \(u(p)+v(m)\) and by every residual gauge satisfying `(137)`.
Thus `(147)` is a secondary boundary invariant of a locally exact bulk potential, not a local
curvature obstruction.

This distinction explains the corpus more accurately.

```text
all finite truncations are invertible/exact
  -> the bulk potential (144) exists on every finite rectangle;

prime-dilation covariance leaks at infinity
  -> the rectangle boundary term (145) survives cofinally;

ambient adelic L2 loses point conormals
  -> scalar completion quotients out the secondary boundary record;

flat HT faces retain maximal information
  -> exact bulk data may survive only as an asymptotic boundary class;

orthogonality catastrophe and nonclosed graphs
  -> the primitive exits the critical bornology without ceasing to exist;

Weil/Hardy/CCM negative index
  -> target realization counts nonzero boundary classes with multiplicity;

functional-equation reflection
  -> it sends the boundary density in (147) to its negative;

positive quartet surgery
  -> it inserts two oriented nonzero boundary records and two negative squares.
```

The third completion is consequently not a space on which local curvature vanishes.  It must be a
Hausdorff **relative completion** which retains simultaneously:

1. the exact finite-stage primitive;
2. its complementary prime--depth boundary record `(146)`;
3. the source pointing, polarization, integral multiplicity, and HT shell reporters;
4. the closed comparison map to the additive Poisson/Weil realization.

The provisional notation \(H^2_{\rm mod}(F)\) in `(138)` is legitimate only if it denotes this
controlled *relative boundary* theory.  In ordinary unconstrained cohomology the potential `(144)`
already trivializes the class, so ordinary \(H^2\), a bare derived limit, or the formal equation
\(d^2=0\) cannot prove `(139)`.

### Frozen truth-hunch: source-effective Stokes anomaly matching

`[CONJECTURE] [SOURCE_EFFECTIVE_STOKES_ANOMALY_MATCHING]`

> For a source-minimal self-dual constrained HT object, completion and principal-conormal
> localization carry every source-exact calibrated primitive to a conservative
> continuation--record correspondence.  The only failure of proper base change is its controlled
> mixed boundary record.  The multiplicity length of the nonzero reflection-oriented record equals
> the negative index of the completed Hermitian realization and is bounded by a
> presentation-independent source anomaly capacity:
> \[
>  \operatorname{ind}_{-}(\mathcal W_F)
>  =
>  \operatorname{len}_{\ne0}
>    \partial_{\infty}^{\rm mix}\operatorname{Loc}(N_F)
>  \le \mathfrak a_{\rm src}(F).                          \tag{148}
> \]
> The capacity is constructed before divisor localization from the complete polarized
> Euler--Gamma/Poisson source colligation; it is not defined by the target index.  For the
> pointed ordinary-integer comb,
> \[
>  \mathfrak a_{\rm src}(\zeta)=0.                        \tag{149}
> \]

The conjecture is a truth hunch in the requested sense: current evidence suggests it, but no proof
method for `(148)`--`(149)` is known.  The earlier quantity \(r_F-b_F\) is only one candidate
realization of \(\mathfrak a_{\rm src}(F)\); the infinite-rank theorem `(128)`--`(130)` forbids
treating it as the dimension of a raw pole port.

For zeta, `(147)`, multiplicity faithfulness, `(142)`, and `(149)` would give
\[
 0
 \le
 \sum_{\substack{\Xi(\rho)=0\\\operatorname{Re}\rho>1/2}}d_\rho
 =
 \operatorname{ind}_{-}(\mathcal G_\Xi)
 \le 0,
 \tag{150}
\]
hence no right-half off-line zero; reflection then gives RH.

### New deductions and exact open core

1. **Finite-stage exactness is expected, not evidence for RH.**  Any proof whose decisive identity
   lives on one finite prime--depth rectangle cannot see `(146)`.
2. **Separate prime and depth estimates are structurally insufficient.**  The invariant kills
   \(u(p)+v(m)\); the producer must control the joint incidence primitive at mixed area scale.
3. **Local HT integrability is insufficient.**  The missing statement is a properness theorem for
   a source-effective primitive in the critical bornology.
4. **Target index theory is complete as detector.**  Equation `(142)` counts every nonzero record,
   with \(+\infty\) allowed.  It does not prove source capacity zero.
5. **The exact RH-bearing core is `(149)`.**  It must be obtained by constructing the
   ordinary-integer Euler/Poisson continuation--record colligation and proving a source Stokes
   theorem whose only archimedean/polar contribution is cancelled by the distinguished vacuum.
   Neither functional equation, positivity, hypertranscendence, nor ordinary-prime incidence alone
   implies this cancellation.
6. **Falsifier.**  If an explicit off-line generalized-prime system realizes the literal
   ordinary-integer prime-square Fourier clock, the same pointed integral incidence colligation,
   and zero source anomaly capacity, then `(148)` is false.

This replaces the misleading instruction “prove local mixed curvature is zero” by one
finite-to-infinite theorem: prove that the exact ordinary-integer source primitive has no
uncancelled controlled Stokes record after the producer and reporter polarizations are glued.

- 2026-07-30 — Hostile comparison with the HT Spencer--Helmholtz integration stack showed that
  `(133)` is a mixed Hessian of the globally defined bilinear potential `(144)`, not an exterior
  curvature.  Reinterpreted off-line displacement as the secondary cofinal Stokes density `(146)`.
  This explains why every finite stage can be exact while the infinite completion carries a
  nonzero sector/index anomaly, and isolates zero ordinary-source anomaly capacity `(149)` as the
  RH-bearing theorem.

### Reciprocity is not yet source-anomaly cancellation

The corpus's metaplectic--Steinberg descent supplies an important hostile test for `(149)`.
Adelic theta splitting cancels local Maslov/Hilbert-symbol cocycles by Poisson summation and the
global product formula.  This cannot by itself kill `(147)`:

1. the metaplectic defect is unitary, ultimately \(\mu_2\)- or circle-valued, whereas `(147)` is
   the real logarithmic modulus of a radial character;
2. for every \(a\in\mathbb C\) and \(q\in\mathbb Q^\times\), the adelic product formula gives
   \[
    \prod_v |q|_v^a=1,                                  \tag{151}
   \]
   not only when \(\operatorname{Re}a=0\);
3. the Gamma--Gaussian property-\(S\) envelope already constructs Fourier-self-dual tempered
   distributions retaining arbitrary reflection-symmetric off-line divisors.

Thus rational splitting, Poisson self-duality, and ordinary temperedness all permit nonzero
mixed Stokes density.  The missing source assertion is stronger:

`[OPEN CORE] [XI_BILATERAL_DAGGER_RECORD]`

> The source-landed principal Xi conormal and its reflected dual are positive/finite-order
> functionals for one source-fixed bilateral prime-dilation dagger correspondence, before either
> fibre is evaluated.

On one prime-depth character this has the exact algebraic consequence
\[
 \alpha_\rho(U_p)=p^{\rho-1/2},\qquad
 \alpha_\rho(U_p^\ast)=\overline{\alpha_\rho(U_p)},\qquad
 U_p^\ast U_p=U_pU_p^\ast=1,
 \tag{152}
\]
so
\[
 |p^{\rho-1/2}|=1
 \quad\Longrightarrow\quad
 \operatorname{Re}\rho=\frac12.                         \tag{153}
\]
Equation `(153)` is only the consumer.  The frontier theorem is construction of the single
source-fixed dagger correspondence and conservative landing of all Xi multiplicity conormals.
Giving the reflected pair two different Toeplitz sectors, fitting the dagger after choosing
\(\rho\), or invoking the universal property-\(S\) envelope does not prove it.

This locates the role of the source-effective Stokes law: `(148)` is the index-valued global form
of bilateral dagger landing, while `(152)` is its one-character shadow.  The prime-square Fourier
clock and projective cross-Gram construct the finite local dagger; the unproved step is its strict
all-prime Poisson/Tate identification on Meyer's pre-divisor quotient.

- 2026-07-30 — Tested zero source anomaly against adelic metaplectic reciprocity.  The test fails
  because product-formula cancellation holds for every radial modulus and the universal
  property-\(S\) envelope retains off-line divisors.  Sharpened `(149)` to the bilateral
  source-dagger landing theorem `(152)`, matching the corpus's existing relative-hyperrigidity
  open core rather than pretending Poisson descent alone forces RH.

## 20. Exact local meaning: off-line conormals are mixed Poisson states

The bilateral-dagger statement has a sharper local formulation.  Let
\(\rho\) lie in the strict right half of the critical strip and put
\[
 w_{p,\rho}:=p^{1/2-\rho},
 \qquad |w_{p,\rho}|^2=p^{1-2\operatorname{Re}\rho}<1.
 \tag{154}
\]
On the unramified prime-angle algebra
\[
 C^\ast(\mathbb Z)\cong C(\mathbb T),
 \]
let \(U_p\) be the canonical unitary generator.  The Poisson measure at \(w=w_{p,\rho}\),
\[
 d\mu_w(e^{i\theta})
 =
 {1-|w|^2\over|e^{i\theta}-w|^2}\,{d\theta\over2\pi},
 \tag{155}
\]
defines a state \(\varphi_{p,\rho}\) with
\[
 \varphi_{p,\rho}(U_p^m)=w^m,\qquad
 \varphi_{p,\rho}(U_p^{-m})=\overline w^{\,m}
 \qquad(m\ge0).
 \tag{156}
\]
Thus reflection can glue the two one-sided Hardy characters into a positive bilateral state for
every strict-right point.  Positivity and finite-order distributionality do not select the
critical line.

The state is multiplicative exactly on the boundary of the disk.  Its Kadison defect at depth
\(m\) is
\[
\begin{aligned}
 \delta_{p,m}(\rho)
 &:=
 \varphi_{p,\rho}(U_p^{-m}U_p^m)
 -
 \varphi_{p,\rho}(U_p^{-m})
 \varphi_{p,\rho}(U_p^m)\\
 &=1-|w_{p,\rho}|^{2m}
 =1-p^{m(1-2\operatorname{Re}\rho)}.
                                                               \tag{157}
\end{aligned}
\]
Consequently:

`[PROVED HERE] [PRIME_POISSON_STATE_STOKES_DEFECT_IDENTITY]`
\[
 \boxed{\quad
 {\,\log(1-\delta_{p,m}(\rho))\over m\log p}
 =
 1-2\operatorname{Re}\rho
 =
 \partial_\infty^{\rm mix}\ell_\rho.
 \quad}                                                       \tag{158}
\]

The first equality follows immediately from `(157)`; the second is `(147)`.  Hence the following
conditions are equivalent:
\[
\begin{aligned}
 \operatorname{Re}\rho=\tfrac12
 &\Longleftrightarrow
 \delta_{p,m}(\rho)=0\text{ for one/every }p,m\\
 &\Longleftrightarrow
 \varphi_{p,\rho}\text{ is multiplicative}\\
 &\Longleftrightarrow
 \varphi_{p,\rho}\text{ is a pure state of }C(\mathbb T)\\
 &\Longleftrightarrow
 \mu_{w_{p,\rho}}\text{ is a point mass on }\mathbb T.
                                                               \tag{159}
\end{aligned}
\]
At \(|w|<1\), `(155)` is an absolutely continuous mixed state.  At \(|w|=1\), its weak boundary
value is the Dirac character at \(w\).  The reflected parameter \(1/\overline w\) lies outside the
disk; `(156)` retains it through the negative Fourier modes without making the two-sided moment
sequence a group character.  The seam defect `(157)` is exactly the obstruction.

This corrects another possible overstatement in the source polarization--record conjecture:
finite-order bilateral record alone does not force the critical line.  Poisson states `(155)` are
smooth bilateral records for every \(|w|<1\).  What forces the line is **purity**, equivalently
membership of the prime-angle generator in the multiplicative domain of the continuation state.

### Universal law, sharpened

The common statement behind the channel, Stokes, dagger, and index descriptions is now:

> **Source-effective conormal purity conservation.**  Principal localization of a
> source-invertible conormal line through the complete continuation--record correspondence
> preserves its purity on the source-selected unramified prime-angle algebra.  Failure of purity is
> carried faithfully by the complementary record; its logarithmic density is `(158)`, and its
> nonzero multiplicity length is the Weil/Hardy/CCM negative index `(142)`.

This is not a theorem yet.  It says more than positivity and less vaguely than “source duality is
strict.”  The exact zeta producer is:

`[OPEN CORE] [XI_SOURCE_CONORMAL_PRIME_ANGLE_MULTIPLICATIVE_DOMAIN]`

Construct, before zero specialization, a unital completely positive prime-angle realization
\[
 \Phi_\zeta:
 \mathcal S_{\rm Euler/Poisson}
 \longrightarrow
 \mathcal B(\mathcal H_{\rm cont}\oplus\mathcal H_{\rm rec})
 \tag{160}
\]
of the full ordinary-integer source operator system such that:

1. the local prime-square Fourier clocks and the projective Weyl comparisons are its finite
   restrictions;
2. the cross-Gram \(\mu(n)/n\), Gamma first-trace face, regular dyadic tower, and additive
   Poisson reporter are retained in one strict all-prime graph;
3. Meyer's pre-divisor principal conormal and every multiplicity jet land conservatively;
4. every unramified unitary \(U_p\) lies in the multiplicative domain of the landed conormal
   functional, uniformly under aperture enlargement;
5. the complementary record is not discarded; its vanishing on the conormal is proved from the
   source colligation rather than assumed.

Clause 4 gives `(159)` and RH.  Clause 5 is the source content: a pure global Stinespring vector
can have mixed marginals, so global purity or a unitary dilation alone is insufficient.

This mechanism explains the strongest countermodels.  Positive generalized-prime systems,
Fourier-self-dual property-\(S\) envelopes, and off-line Euler quartet surgeries all realize the
mixed Poisson phase `(155)`; they show that the record can be positive and perfectly regular while
the multiplicative-domain defect is strictly positive.  The literal ordinary-integer
prime-square clock is relevant only if its all-prime Poisson gluing proves Clause 5.

- 2026-07-30 — Identified every strict-right radial conormal with a prime-angle Poisson state.
  Proved the exact identity `(158)` equating its Kadison multiplicative-domain defect rate, the
  prime--depth mixed Stokes density, and horizontal zero displacement.  This replaces the false
  “finite-order record implies RH” idea by the precise source-purity problem `(160)`.

### Infinite energy, finite support length

For every fixed strict-right \(\rho\), `(157)` gives
\[
 \delta_{p,1}(\rho)=1-p^{1-2\operatorname{Re}\rho}
 \longrightarrow1
 \qquad(p\to\infty).                                    \tag{161}
\]
Moreover,
\[
 -\log\!\left(1-\delta_{p,m}(\rho)\right)
 =
 (2\operatorname{Re}\rho-1)m\log p.                    \tag{162}
\]
Thus one off-line conormal has unbounded accumulated prime-record energy and lies in a sector
disjoint from the critical vacuum, exactly as the Kakutani, Hellinger, Wold, and orthogonality
catastrophe theorems predict.  Nevertheless `(142)` counts that same conormal by the finite
integer \(d_\rho\).

There is no contradiction.  The raw boundary and its metric defect measure the **magnitude** of
sector separation; the Weil/Hardy index measures the **multiplicity length of its nonzero
support**.  The source transgression sought in `(148)` must pass from the former to the latter
without claiming that the former has finite rank or finite energy.

This also refutes a stronger reading of the pole-budget idea.  A finite pole count cannot bound
the raw sum of `(162)`: it is already infinite for one off-line zero.  Any valid
pole--vacuum statement must bound only the controlled support length after strict
continuation--record transgression.  That transgression, not a trace or energy estimate, is the
load-bearing source theorem.

### Duality--adjunction fracture is exactly the record

The Poisson countermodel and the Hodge target are not competing descriptions.  They are the two
sides of one elementary but load-bearing identity.

Let \(A\) be an invertible contraction on a Hilbert space.  Algebraic duality transports an
invertible source unit by \(A\mapsto A^{-1}\), whereas positive Hilbert adjunction transports it
by \(A\mapsto A^*\).  Define their fracture
\[
 \Sigma(A):=A^{-1}-A^*.
 \tag{163}
\]
Direct multiplication gives
\[
 \boxed{\qquad
 \Sigma(A)A=I-A^*A,\qquad
 A\Sigma(A)=I-AA^*.
 \qquad}
 \tag{164}
\]
Therefore the two normalized faces of the duality--adjunction fracture are exactly the two
Kadison--Schwarz records.  In particular,
\[
 \Sigma(A)=0
 \Longleftrightarrow
 A\text{ is unitary}
 \Longleftrightarrow
 I-A^*A=I-AA^*=0.
 \tag{165}
\]
If \(A=\Phi(u)\) is the image of a unitary source generator under a UCP continuation channel,
the two operators in `(164)` are precisely the defects testing whether \(u\) belongs to the
multiplicative domain of \(\Phi\).

For the scalar prime character \(w=w_{p,\rho}\) and depth \(m\), the two candidate negative
moments are
\[
 \underbrace{w^{-m}}_{\text{functional-equation duality}},
 \qquad
 \underbrace{\overline w^{\,m}}_{\text{positive adjunction}}.
 \tag{166}
\]
Their seam
\[
 \varepsilon_{p,m}(\rho)
 :=
 w^{-m}-\overline w^{\,m}
 \tag{167}
\]
obeys the exact normalized fracture law
\[
 \boxed{\qquad
 w^m\varepsilon_{p,m}(\rho)
 =
 1-|w|^{2m}
 =
 \delta_{p,m}(\rho).
 \qquad}
 \tag{168}
\]
Combining `(158)` and `(168)` gives
\[
 {\,\log\!\left(1-w^m\varepsilon_{p,m}(\rho)\right)\over m\log p}
 =
 1-2\operatorname{Re}\rho.
 \tag{169}
\]

`[PROVED HERE] [DUALITY_ADJUNCTION_KADISON_FRACTURE_IDENTITY]`

Equations `(163)`--`(169)` require no zeta value or zero information.  The operator identities are
immediate from invertibility, and the scalar specialization is direct substitution.

This changes the universal interpretation:

1. functional equation supplies the inverse face;
2. positivity supplies the adjoint face;
3. a mixed Poisson state retains the adjoint face while its complementary Stinespring record
   stores the missing inverse face;
4. bilateral moderation tests whether inverse transport is also adjoint transport;
5. Wold--Higgs and Kakutani energies accumulate the logarithmic magnitude of the same fracture;
6. the secondary mixed Stokes density is its normalized local logarithm;
7. the Weil/Hardy/CCM index counts the multiplicity length of its nonzero conormal support.

Thus all current selectors are shadows of one law:

> **Adjoint--duality fracture conservation.**  Positive completion of an invertible source action
> cannot erase the failure of duality to equal adjunction.  The failure appears exactly as the
> two-sided multiplicative-domain record `(164)`; under strict localization it may move into an
> ideal, Stokes, sector, or index channel, but it cannot become zero without the source action
> becoming unitary on the localized class.

This abstract statement is an identity, not RH.  The Riemann theorem must prove that the actual
source-generated Xi conormal is a class on which source duality and positive adjunction are the
same transport, rather than two separately existing transports.

### Sharper arithmetic open core

`[OPEN CORE] [XI_POLARIZED_BOCKSTEIN_DUALITY_ADJUNCTION_NATURALITY]`

Construct the source/ambient/corona exact sequence for the ordinary-prime
Euler--Gamma/Tate--Milnor/Calderón object and its common escaping unit primitive before divisor
specialization.  Prove:

1. its connecting Bockstein class is the principal Xi conormal in Meyer's quotient, with every
   multiplicity grade retained;
2. functional-equation duality and Green/Hodge adjunction are defined on the same strict relative
   completion and commute with the connecting morphism;
3. on the common corona primitive these two transports coincide by a source Green formula;
4. no completion kernel appears when the resulting identity descends to the Xi conormal.

Then `(164)` makes both complementary records vanish on every prime generator.  Equation `(159)`
forces every nontrivial zero onto the critical line.

Clause 3 is now the first formula-bearing source obstacle.  It is stronger than having a
functional equation and a positive completion separately, yet weaker and more concrete than
postulating a positive metric directly on the zero space.  An off-line Euler/property-\(S\)
countermodel must fail it by a nonzero seam `(167)`; its positive Poisson completion demonstrates
exactly where that seam goes.

- 2026-07-30 — Proved the duality--adjunction fracture identities `(163)`--`(169)`.  They identify
  inverse-versus-adjoint mismatch, two-sided Kadison record, prime Poisson impurity, mixed Stokes
  density, and the accumulated sector defects as realizations of one conserved fracture.  The
  RH-bearing source theorem is now the polarized Bockstein naturality statement above.

### The local and ambient seam is already zero

The unit Calderón primitive does not itself create the fracture.  Let
\((U_t)_{t\in\mathbb R}\) be a strongly continuous unitary group and let \(J\) be an antiunitary
involution satisfying
\[
 JU_tJ^{-1}=U_{-t}.
\]
For \(\alpha>0\), define the forward and backward resolvents and their finite cells by
\[
\begin{aligned}
 R_{\alpha,+}&=\int_0^\infty e^{-\alpha t}U_t\,dt,
 &R_{\alpha,-}&=\int_0^\infty e^{-\alpha t}U_{-t}\,dt,\\
 B_{\alpha,L,+}&=\int_0^L e^{-\alpha t}U_t\,dt,
 &B_{\alpha,L,-}&=\int_0^L e^{-\alpha t}U_{-t}\,dt.
\end{aligned}
\tag{170}
\]
Bochner integration and unitarity give
\[
\boxed{
 JR_{\alpha,+}J^{-1}
 =R_{\alpha,-}
 =R_{\alpha,+}^*,
\qquad
 JB_{\alpha,L,+}J^{-1}
 =B_{\alpha,L,-}
 =B_{\alpha,L,+}^*.
}
\tag{171}
\]

`[PROVED HERE] [UNIT_CALDERON_PRIMITIVE_DUALITY_ADJUNCTION_COINCIDENCE]`

This is the centered-unitary form of the unit-exponential Wold--Calderón primitive.  Its proof
uses only that the scalar kernel \(e^{-\alpha t}\) is real and integrable.  Hence every finite
cell and the ambient resolvent already identify reflection duality with Hilbert adjunction.

There is also no abstract Bockstein obstruction.  For a short exact sequence of cochain complexes
\[
 0\longrightarrow C^\bullet
 \longrightarrow A^\bullet
 \longrightarrow K^\bullet
 \longrightarrow0
\tag{172}
\]
let \(\partial:H^j(K^\bullet)\to H^{j+1}(C^\bullet)\) be its connecting map.  If
\(\mathfrak d\) and \(\mathfrak a\) are two possibly semilinear natural chain transports of the
whole exact sequence, naturality gives
\[
 \partial\,\mathfrak d_K=\mathfrak d_C\,\partial,
 \qquad
 \partial\,\mathfrak a_K=\mathfrak a_C\,\partial.
\tag{173}
\]
Therefore
\[
 (\mathfrak d_K-\mathfrak a_K)[R]=0
 \quad\Longrightarrow\quad
 (\mathfrak d_C-\mathfrak a_C)\partial[R]=0.
\tag{174}
\]

`[PROVED HERE] [POLARIZED_BOCKSTEIN_NO_FRACTURE]`

Equation `(174)` is ordinary naturality of the long exact cohomology sequence.  It shows that a
connecting morphism cannot manufacture a duality--adjunction fracture when both transports are
defined naturally on one exact sequence.

The bare resolvent in `(170)` cannot itself be the Riemann primitive: its Mellin symbol is
rational and carries no zeta divisor.  The source-decorated primitive must also retain the full
prime cube.  The corpus has already constructed its decisive operator coordinate:
\[
 {\cal A}e_n={\mu(n)\over n}e_n,\qquad
 \operatorname{Dom}{\cal A}^{-1}
 =
 \left\{y:\sum_{\mu^2(n)=1}n^2|y_n|^2<\infty\right\}.
\tag{175a}
\]
It is the producer--reporter cross-Gram, its inverse graph is closed and self-adjoint, and its
signed spectral family satisfies
\[
 \operatorname{Tr}\!\left(\operatorname{sgn}{\cal A}\,|{\cal A}|^s\right)
 ={1\over\zeta(s)}
 \qquad(\operatorname{Re}s>1).
\tag{175b}
\]
Moreover the exact finite prime-square Fourier-fixed currents converge pointwise to the inverse
graph symbol \(\mu(n)n\).  Thus the actual candidate is the **Euler-decorated Calderón
primitive**
\(\mathfrak R_{\rm ar}\): the common cell primitive `(170)` together with its full cubical
prime-interval object, the closed inverse cross-Gram graph `(175a)`, and the Gamma/Poisson
transgression.  The notation denotes a construction target; merely taking the scalar product of
Euler factors is forbidden.

The RH-bearing gap has consequently narrowed to the following source identification:

\[
\boxed{
\begin{gathered}
\text{construct one strict dagger-stable source/ambient/corona sequence `(172)`,}\\
\text{and prove }
\partial[\mathfrak R_{\rm ar}]
=N_\Xi^{\rm src}
\text{ faithfully in }M_\zeta.
\end{gathered}}
\tag{175}
\]

Here dagger equality on \(\mathfrak R_{\rm ar}\) must be proved from the finite Fourier-fixed
currents, self-adjoint inverse graph, and Gamma/Poisson reflection; it does not follow from
`(171)` alone.  If `(175)` and that graph compatibility hold, `(171)` and `(174)` force duality
to equal adjunction on
\(N_\Xi^{\rm src}\).  The conormal covariance then specializes this equality to
\(\Sigma(w_{p,\rho})=0\), and `(165)`--`(169)` give RH.

This is materially narrower than the former producer `(160)`.  One need not prove a new
multiplicative-domain theorem after constructing `(175)`; multiplicative-domain membership is
the normalized image of the already-zero seam.  It is not only an identification theorem:
constructing \(\mathfrak R_{\rm ar}\) as one strict dagger graph is part of `(175)`.
Nor can a local calculation settle `(175)`:
every finite packet has an honest primitive and zero cohomology.  The nonzero class exists only
because the Euler-decorated primitive escapes the strict arithmetic completion, so equality with
the Meyer conormal is an all-prime completion--specialization theorem.

The exact failure alternatives are now exhaustive:

1. the arithmetic source/ambient/corona sequence is not strict or not dagger-stable;
2. reflection and adjunction do not define natural transports of the same sequence;
3. the finite Fourier-fixed currents, inverse cross-Gram graph, and Gamma/Poisson faces do not
   assemble into one \(\mathfrak R_{\rm ar}\);
4. \(\mathfrak R_{\rm ar}\) is not the corona class producing arithmetic middle cohomology;
5. its Bockstein is not the Xi principal conormal;
6. the comparison to \(M_\zeta\) kills a conormal or multiplicity grade.

An off-line zero would force at least one of these six failures.  Its Poisson state then realizes
the resulting nonzero seam through `(168)`.

The literature contains duality of \(C^*\)-extension exact triangles and Toeplitz
\(K\)-theory boundary maps, as well as canonical unitary dilations of contraction tuples.  Those
parent theories support `(173)` but do not identify the ordinary-prime Wold--Calderón Bockstein
with Meyer's principal conormal or prove strict dagger faithfulness of the arithmetic completion.
Targeted arXiv audit found no such source-specific theorem; this is a noncollision statement, not
a priority claim.

- 2026-07-30 — Proved ambient resolvent equality `(171)` and the polarized Bockstein
  no-fracture lemma `(174)`.  The only place a Riemann seam can arise is now the strict
  source-to-Meyer identification `(175)`, not finite-cell reflection, positivity, dilation, or
  abstract connecting-map naturality.
- 2026-07-30 — Corrected `(175)`: the bare rational Calderón resolvent cannot carry the zeta
  divisor.  The Bockstein primitive must be the Euler-decorated object
  \(\mathfrak R_{\rm ar}\), retaining the finite Fourier-fixed prime cube, self-adjoint Möbius
  inverse graph, and Gamma/Poisson transgression before strict source-to-Meyer comparison.

### Representation-type and depth laws forced by the fracture

The local positive representation undergoes a sharp type change.  For \(|w|<1\), the Poisson
measure `(155)` has a strictly positive smooth density with respect to Haar measure.  Its GNS
space is therefore the diffuse infinite-dimensional space \(L^2(\mathbb T,\mu_w)\).  At
\(|w|=1\), the boundary state is a Dirac character and its GNS space is one-dimensional:
\[
 \dim\mathcal H_{\varphi_{p,\rho}}
 =
 \begin{cases}
  1,&\operatorname{Re}\rho=\tfrac12,\\
  \infty,&\operatorname{Re}\rho>\tfrac12.
 \end{cases}
\tag{176}
\]
Thus an off-line conormal does not merely change one scalar.  Positive completion forces an
infinite diffuse environmental record at every prime, whereas a critical conormal is already a
closed one-dimensional unitary sector.

The records also obey an exact crossed-cocycle law:
\[
 \delta_{p,m+n}
 =
 \delta_{p,m}
 +(1-\delta_{p,m})\delta_{p,n}.
\tag{177}
\]
Indeed \(1-\delta_{p,m}=|w|^{2m}\).  More generally, for
\(N=\prod_pp^{m_p}\),
\[
\begin{aligned}
 1-\delta_N(\rho)
 &:=
 \prod_p(1-\delta_{p,m_p}(\rho))
 =N^{\,1-2\operatorname{Re}\rho},\\
 -\log(1-\delta_N(\rho))
 &=(2\operatorname{Re}\rho-1)\log N.
\end{aligned}
\tag{178}
\]
Hence the mixed Stokes density is the unique additive logarithmic rate of the complete
multiplicative-domain record.  The Wold crossed-cocycle formulas, Kakutani product fracture, and
prime--depth Bayes rate are instances of `(177)`--`(178)` in different source coordinates.

### Frozen universal law: effective dagger base change

The preceding results suggest one law of which the completion, Stokes, Hodge, Wold, Kakutani,
hyperrigidity, and index descriptions are shadows.

`[CONJECTURE] [SOURCE_EFFECTIVE_DAGGER_BECK_CHEVALLEY_LAW]`

> Let an integral source-minimal hypertranscendental object carry an invertible source action,
> source duality, a distinguished effective section, and a complete continuation--record
> object.  Form its relative completion before spectral specialization.  On every effective
> principal conormal, completion and specialization satisfy dagger Beck--Chevalley: the
> comparison identifies categorical inverse duality with positive adjunction.  The cone of this
> comparison is the complete complementary record.  Its two normalized boundary maps are the
> Kadison defects `(164)`, its logarithmic local density is `(169)`, and its target support length
> is the negative index `(142)`.

For the ordinary-prime source, the comparison object is not arbitrary.  It must be constructed
from \(\mathfrak R_{\rm ar}\): the finite prime-square Fourier fixed points, projective Möbius
cross-Gram and closed inverse graph, cubical interval/Bockstein cells, Gamma determinant and BV
first trace, additive Poisson comparison, and both real boundary faces.  The law asserts that the
resulting strict comparison is dagger-exact and faithful on the Meyer principal conormal.

The conjecture makes several exact predictions.

1. **No local origin for off-line displacement.**  Equation `(171)` kills the fracture on every
   unitary Calderón cell.  A nonzero seam can only be a strict completion--specialization anomaly.
2. **No scalar cure.**  A scalar Hilbert completion may restore adjunction but erase the
   conormal; a raw Ind-limit may retain the conormal but fail dagger Beck--Chevalley.  Both are
   nonconservative base changes.
3. **Positive countermodels are mixed phases.**  Generalized-prime and property-\(S\) off-line
   systems realize the adjoint chart by a diffuse Poisson GNS space `(176)` while their inverse
   chart survives in the complementary record `(168)`.
4. **Hypertranscendence fixes the height of the comparison, not its sign.**  No finite
   differential observer can exhaust the comparison cone; the complete Rees/Stokes tower is
   required.  Dagger exactness is an independent source theorem.
5. **Critical zeros are anomaly-free effective fibres.**  On them inverse and adjoint transport
   coincide, the GNS environment collapses, every \(\delta_{p,m}\) vanishes, and the target
   negative-index contribution is zero.

For \(\Xi\), the theorem required to instantiate the law is precisely:
\[
 \operatorname{BC}^{\dagger}_{\mathfrak R_{\rm ar}}:
 \operatorname{Comp}_{\rm ar}\operatorname{Sp}_{\Xi}
 \Longrightarrow
 \operatorname{Sp}_{\Xi}\operatorname{Comp}_{\rm ar}
\tag{179}
\]
constructed before a zero is selected, strict and conservative on every principal conormal jet,
with duality equal to adjunction.  At a fibre \(\rho\), the scalar symbol of the failure cone of
`(179)` is \(\varepsilon_{p,m}(\rho)\).  Dagger Beck--Chevalley makes it zero; `(168)` then makes
\(\delta_{p,m}(\rho)=0\), and `(159)` proves
\(\operatorname{Re}\rho=\tfrac12\).

This is a genuine truth-hunch, not a theorem renamed for convenience.  No proof of `(179)` is
known.  Its first non-parent mathematical task is to construct the closed all-prime comparison
from \(\mathfrak R_{\rm ar}\) and compute its comparison cone without scalarizing or choosing a
unitary target.  If the cone has a nonzero source-invisible class, that class is the exact missing
channel and the conjecture is false as stated.

- 2026-07-30 — Froze the source-effective dagger Beck--Chevalley law `(179)`.  Derived the local
  GNS type transition `(176)` and the complete depth/multiplicative defect cocycles
  `(177)`--`(178)`.  The proposed universal interpretation is now falsifiable: all unexplained
  obstruction mass must be the cone of one explicit completion--specialization comparison.

### The formal Sonin--Calkin seam is exactly the duality--adjunction fracture

The recent Calkin corpus already contains a faithful essential reporter for `(167)`, but its
relation to the dagger formulation was not made explicit.  Write
\[
 c_p(\rho)
 :=
 \log p\left(p^{-\overline\rho}-p^{-(1-\rho)}\right)
\tag{180}
\]
for the formalized FE--Schwarz prime-seam charge.  Since
\[
 p^{-\overline\rho}=p^{-1/2}\overline{w_{p,\rho}},
 \qquad
 p^{-(1-\rho)}=p^{-1/2}w_{p,\rho}^{-1},
\]
equation `(167)` gives the exact identity
\[
 \boxed{\qquad
 c_p(\rho)
 =
 -{\log p\over\sqrt p}\,
 \varepsilon_{p,1}(\rho).
 \qquad}
\tag{181}
\]

`[PROVED HERE] [PRIME_SEAM_IS_RENORMALIZED_DUALITY_ADJUNCTION_FRACTURE]`

Let \(C_{p,q}(a)\) be the literal two-prime Sonin quadratic Gram corner at positive aperture
\(a\), and put
\[
 K_{p,q}(a,\rho)
 :=
 \bigl(c_p(\rho)-c_q(\rho)\bigr)C_{p,q}(a).
\tag{182}
\]
The formal Calkin theorem gives
\[
 \|K_{p,q}(a,\rho)\|_{\rm ess}
 =
 {|c_p(\rho)-c_q(\rho)|\over\sqrt{pq}}.
\]
Substitution of `(181)` yields
\[
 \boxed{
 \|K_{p,q}(a,\rho)\|_{\rm ess}
 =
 {1\over\sqrt{pq}}
 \left|
 {\log q\over\sqrt q}\varepsilon_{q,1}(\rho)
 -
 {\log p\over\sqrt p}\varepsilon_{p,1}(\rho)
 \right|.
 }
\tag{183}
\]
Thus the prime-pair Calkin Gram is the essential discrete curvature of the renormalized
duality--adjunction fracture.  It is compact exactly when the two renormalized local fractures
agree.  Compactness for every pair makes \(c_p(\rho)\) prime-independent; the proved open-strip
cofinal decay \(c_p(\rho)\to0\) then kills the common value.  Equations `(181)` and `(168)` force
every local Kadison defect to vanish.

This is not another RH equivalent chosen after the fact.  The operator \(C_{p,q}(a)\) is the
literal source Sonin Gram corner, its noncompactness is unconditional, and finite and
absolutely-summable all-prime Calkin injectivity are already proved in Lean.  What remains
target-fed in the existing aggregate is its fibre-dependent damping.  A proof must instead
produce compactness of the undamped principal curvature from the completed source.

### Finite self-duality cannot supply that compactness

Every finite prime-square current \(g_P\) is exactly Fourier fixed, its crystalline theta
distribution is Fourier self-dual, and its entire completion \(\Xi_P\) satisfies the Riemann
reflection law.  Nevertheless \(\Xi_P\) retains every nontrivial zeta zero, on or off the
critical line, because its extra finite Euler factors are nonzero in the open strip.  Similarly,
finite Green--Poisson sewing is strict exact and conjugate to Meyer's sequence, while its
prime-enlargement maps retain every strip conormal.

Therefore the following implications are false:

```text
finite Fourier self-duality -> critical-line purity;
finite dagger exactness -> critical-line purity;
coarse all-prime reflection -> critical-line purity.
```

The missing datum is the dagger behavior of the **moving comparison between finite self-dual
frames** after source-normal cofinal specialization.  The scale
\(\sqrt{M_P}\), the Hilbert sector, the common indicial order, and the observation condition
number all move with \(P\).  Exact symmetry inside each fibre says nothing about the adjoint of
the transport between fibres.

### Universal jump: essential curvature of a singular source correspondence

The corpus now points to a more precise universal law than a scalar third norm.

`[BOLD CONJECTURE] [COFINAL_FOURIER_DAGGER_ESSENTIAL_CURVATURE_LAW]`

> A source-minimal integral Euler object has a complete continuation--record correspondence
> \(\mathscr E_{\rm src}\) joining the inequivalent infinite tensor-product sectors selected by
> its finite local clocks.  Its finite Fourier/Weyl identifications, prime-enlargement maps,
> Gamma face, and source-normal Rees section define one adjointable cofinal connection before
> divisor localization.  For a source-effective intermediate-extension projection
> \(\Pi_{\rm src}\), the connection is parallel modulo the intrinsic compact endomorphisms
> \(\mathcal K(\mathscr E_{\rm src})\).  After principal-conormal localization, the essential
> curvature of \(\Pi_{\rm src}\) is exactly the renormalized duality--adjunction fracture
> reported by `(182)`--`(183)`.

The natural target is therefore the Hausdorff \(C^*\)-corona
\[
 \mathcal Q_{\rm src}
 :=
 \mathcal L(\mathscr E_{\rm src})/
 \mathcal K(\mathscr E_{\rm src}),
\tag{184}
\]
not scalar adelic \(L^2\) and not the raw strict Ind-limit.  It is singular enough to retain
noncompact tail-sector records, while adjointable prime actions remain contractive.  The compact
ideal records locally repairable continuation errors; the corona retains the cofinal obstruction.

For the ordinary-prime source, the proposed \(\mathscr E_{\rm ar}\) must be generated before a
zero is selected by:

1. the full three-channel prime-square Fourier/projective Weyl unitary, not its lossy
   two-dimensional compression;
2. both inequivalent continuation and Möbius-record incomplete tensor-product sectors;
3. the Euler-decorated Calderón inverse graph \(\mathfrak R_{\rm ar}\);
4. the Gamma/Poisson real face and source-normal BV/Rees section;
5. Meyer's quotient and the Sonin projection as one relative, rather than scalar, boundary
   projection.

Its localized essential curvature is predicted to satisfy
\[
 \pi_{\rm Calkin}\!\left(
 \Omega^{\rm src}_{p,q}\big|_{N_{\Xi,\rho}}
 \right)
 =
 \pi_{\rm Calkin}\!\left(K_{p,q}(a,\rho)\right).
\tag{185}
\]
Source-effectivity says the left side is zero.  The already-formalized Calkin faithfulness then
forces \(c_p(\rho)=c_q(\rho)\) for all \(p,q\), cofinal decay forces their common value to zero,
and `(181)`--`(169)` prove RH.

This formulation unifies the obstructions without pretending to solve the remaining theorem:

```text
finite clocks and finite Green sewing:
  flat inside each moving fibre, no cofinal dagger control;

scalar adelic L2:
  adjunction restored after quotienting away every point conormal;

raw strict Ind-limit:
  conormals retained, but essential curvature is uncontrolled;

prime-square/Möbius sector fracture:
  continuation and record live in inequivalent incomplete tensor sectors;

Green observability collapse:
  every scalar sector becomes approximately blind beyond every finite Rees order;

Poisson off-line states:
  the same essential curvature appears as a diffuse Stinespring environment;

Stokes, Wold, and Kakutani laws:
  logarithmic magnitude of the essential curvature;

Weil/Hardy/CCM index:
  multiplicity length of its nonzero support;

hypertranscendence:
  forces the complete all-order correspondence, but does not make its curvature vanish.
```

The exact analytic open core is now the one already approached by the semilocal projection
corpus, but with its missing meaning exposed:

`[OPEN CORE] [XI_SOURCE_NORMAL_ESSENTIAL_CURVATURE_COMPACTNESS]`

Construct the completed prime--Gamma two-parameter projection family on
\(\mathscr E_{\rm ar}\), before divisor specialization, and prove that its phase-polarized
base-compressed mixed derivative is compact on the source-normal nearby cycle.  Then prove the
principal-symbol identity `(185)`.  The existing Lean corpus already supplies the
phase-rotation algebra, principal--residual compact replacement, and Calkin coefficient
injectivity.

### Hostile audit

1. The Calkin corona is a **reporter**, not yet a selector.  Off-line fibres give nonzero Calkin
   classes by `(183)` and are retained rather than excluded.
2. Coarse Fourier self-duality is insufficient: every finite \(\Xi_P\) already has it while
   retaining all strip zeros.
3. One-sided quasi-innerness is insufficient.  Connes--Consani compactness of one Hardy
   off-diagonal block does not imply source-normal compactness of the phase-polarized mixed
   curvature.
4. Ambient flatness is insufficient.  Projection of a flat connection has the
   Gauss--Codazzi second-fundamental curvature; that term is precisely the Sonin Gram reporter.
5. An arbitrary rapidly damped all-prime aggregate is target-fed.  The source must produce
   \(\Omega^{\rm src}\) and its compact ideal before \(\rho\) is known.
6. Property-\(S\) and positive generalized-prime countermodels may be coarsely Fourier symmetric.
   They must fail either the literal integral prime-square correspondence, source-normal
   adjointability, or compact essential curvature.  If one satisfies all three with an off-line
   zero, the conjecture is false.
7. The recent local-moment criterion for Möbius Fourier polynomials confirms that moving
   archimedean aperture is load-bearing, but it is an RH equivalent, not a proof of `(185)`.

Literature on quasi-inner local factors proves finite one-sided Hardy compactness, and semilocal
prolate theory constructs stable finite-place Sonin spaces.  A targeted arXiv search found no
identification of their cofinal phase-polarized Calkin curvature with the
inverse-versus-adjoint fracture `(181)` or with the prime-square Möbius sector correspondence.
This is noncollision evidence only.

- 2026-07-30 — Proved the exact bridge `(181)` from the local
  duality--adjunction fracture to the formal prime-seam charge and derived its faithful
  Sonin--Calkin essential-curvature formula `(183)`.  Replaced the vague “third completion” by a
  concrete singular-correspondence/Calkin-corona architecture `(184)`, while isolating
  source-normal essential-curvature compactness `(185)` as the unproved RH-bearing theorem.
  The bridge itself is formalized unconditionally as
  `primeCpowDualityAdjunctionFracture` and
  `orbitwiseNatPrimeSeamCharge_eq_cpow_fracture` in
  `XiPrimeSeamCoherenceCollapse.lean`; direct `lake env lean` verification passed and its axiom
  audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

### Correction: essential curvature is a reporter, not a source theorem

The conjectural implication used after `(185)` was unsupported:

```text
source-effectivity -> vanishing Calkin curvature.
```

Effectivity can select a continuation class without making a compressed connection flat modulo
compacts.  Its Gauss--Codazzi term is precisely the already-proved noncompact Sonin reporter.
Consequently `COFINAL_FOURIER_DAGGER_ESSENTIAL_CURVATURE_LAW` and
`XI_SOURCE_NORMAL_ESSENTIAL_CURVATURE_COMPACTNESS` are withdrawn as producers.  Equations
`(181)`--`(183)` survive unchanged as exact reporter identities.  No claim below uses `(185)`.

### Universal law: the positive radical is the reduced reflection-fixed locus

Let \(D\) be a finite reflection-stable zero-dimensional complex scheme, with commutative local
divisor algebra
\[
 A_D=\bigoplus_{\rho\in |D|}A_\rho,\qquad
 1_\rho 1_\sigma=0\quad(\rho\ne\sigma),                  \tag{186}
\]
and an antilinear star induced by an involution \(\tau\):
\[
 1_\rho^*=1_{\tau\rho}.
\tag{187}
\]
Define the positive radical to be the intersection of the kernels of all star representations
into \(C^*\)-algebras,
\[
 J_+(A_D):=\bigcap_{\pi:A_D\to B_\pi}\ker\pi.             \tag{188}
\]

`[PROVED HERE] [POSITIVE_REFLECTION_RADICAL_LAW]`

\[
 \boxed{\qquad
 J_+(A_D)
 =
 \operatorname{Nil}(A_D)
 \oplus
 \bigoplus_{\rho:\tau\rho\ne\rho}A_\rho .
 \qquad}                                                  \tag{189}
\]

Indeed, if \(\tau\rho\ne\rho\), then
\[
 \pi(1_\rho)^*\pi(1_\rho)
 =\pi(1_{\tau\rho}1_\rho)=0.
\]
The \(C^*\)-identity forces \(\pi(1_\rho)=0\), hence \(\pi(A_\rho)=0\).  Every nilpotent in the
commutative algebra has normal image, and a normal nilpotent in a \(C^*\)-algebra is zero.
Conversely, at a fixed reduced point the residue character
\(A_\rho\to\mathbb C\) is a star representation and detects its scalar residue.  This proves
`(189)`.

The orbit-annihilation core is now formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/XiPositiveReflectionRadical.lean`:

```text
cstar_eq_zero_of_star_eq_orthogonal
starAlgHom_kills_star_isotropic
starAlgHom_kills_swapped_orthogonal
no_injective_starAlgHom_of_swapped_orthogonal
```

The parent operator-algebra fact is standard.  In Bursztyn--Waldmann's terminology, `(188)` is
the minimal closed star ideal detected by positive/GNS representations.  The candidate-new content
is not that parent theorem, but its exact application to the functional-equation divisor and the
resulting completion classification.

### Xi consequence: RH is positive real-radicality, not spectral construction

For the completed Xi divisor use
\[
 \tau(\rho)=1-\overline\rho .
\]
Its fixed locus is exactly \(\operatorname{Re}\rho=1/2\).  Applying `(189)` to every finite
reflection-stable divisor packet gives
\[
 \operatorname{Supp}\bigl(A_\Xi/J_+(A_\Xi)\bigr)
 =
 D_\Xi\cap\{\operatorname{Re}s=1/2\}.                    \tag{190}
\]
Therefore
\[
\boxed{
\mathrm{RH}
\iff
J_+(A_\Xi^{\mathrm{red}})=0
\iff
J_+(A_\Xi)=\operatorname{Nil}(A_\Xi).
}
\tag{191}
\]
The stronger equality \(J_+(A_\Xi)=0\) is RH plus simplicity of every Xi zero.  Thus a single
faithful positive Hilbert completion retaining full local jets would accidentally attempt to
prove both RH and simplicity.  An RH-only architecture must separate two channels:

```text
algebraic/HT divisor channel:
  retains every local algebra and every nilpotent multiplicity jet;

positive spectral channel:
  retains exactly the reduced reflection-fixed support;

comparison anomaly:
  positive radical = nilpotent jets + non-fixed reflection orbits.
```

This is the sought correction to the “third completion” requirement.  No positive completion can
retain every conormal fibre if an off-line fibre exists, and no commutative positive completion can
retain a nontrivial multiplicity jet.  The third object must be a bipolar relative comparison,
not one scalar normed space.

The formal RH reduction is:

```text
riemannHypothesis_of_positive_reflected_divisor_atoms
```

It assumes atoms are defined before zero specialization, reflection swaps them, distinct
reflection partners are orthogonal, and the positive realization retains the atom at every Xi
zero.  The last premise is explicitly load-bearing; the theorem does not hide it.

### What the HT frame contributes, and why it does not yet close the comparison

The positive high-exponent shell frame supplies algebraic conservativity on the right-half
divisor: \(S_m^\#=\zeta H_m\), with \(H_m\) zero-free for \(m\ge12\), so every local reduced
conormal survives in every shell channel.  Pairwise-disjoint \(0/1\) coefficient support supplies
an unconditional positive source Hilbert space.  Relative hypertranscendence prevents finite
differential collapse of the transverse shell labels.

Those are exactly the two ends needed by `(191)`, but the connecting arrow is absent.  The
coefficient Hilbert pairing does not descend conservatively through analytic continuation to the
Xi divisor.  The formal operator-norm wall and Burnol cross-aperture cancellation show why:
off-line evaluation is nonclosable, and ambient Fourier reality is repaired by an orthogonal
defect.  Declaring descent would insert the missing theorem.

`[BOLD CONJECTURE] [ARITHMETIC_HT_POSITIVE_REAL_RADICAL_DESCENT]`

> The ordinary-prime/Gamma source defines, before support decomposition, a bipolar realization of
> the global supported Xi class
> \(\mathcal O_{D_\Xi}=\mathcal O_{\mathbb C}/\Xi\mathcal O_{\mathbb C}\):
> its algebraic leg is conservative on the full supported \(K_1\)/HT divisor record, its positive
> leg is the maximal positive quotient, and strict source descent makes the comparison
> conservative after reduced base change.  Equivalently, its comparison kernel on
> \(\mathcal O_{D_\Xi}^{\mathrm{red}}\) is zero.

By `(191)`, this conjecture implies RH.  It is a truth-hunch, not a proved theorem and not merely a
request for an inequality.  Its first falsifiable construction task is precise:

`[OPEN CORE] [XI_SOURCE_REDUCED_DIVISOR_POSITIVE_DESCENT]`

Construct a star-compatible positive realization from the literal prime-square
Fourier/Möbius/Gamma source and the global supported class `(283)`, then prove that its kernel
contains no nonzero reduced stalk unit.  The construction may retain nilpotent jets only in the
algebraic leg.  A generalized-prime off-line model necessarily fails this reduced conservativity,
even when it retains positive Euler density, functional equation, entire completion, and
hypertranscendence.

This formulation explains, simultaneously:

```text
finite truncations:
  algebraic atoms survive, but positive descent is not cofinally conservative;

ambient adelic L2:
  positivity survives, but every point atom lies in the completion kernel;

raw distribution/Ind completion:
  atoms and jets survive, but reflection duality is not positive adjunction;

Hedenmalm divisor measures:
  positive states are automatically supported on the fixed reduced divisor;

shell operator-norm wall:
  algebraic local faithfulness does not imply positive descent;

Calkin, Ward, Wold, Kakutani, and Stokes defects:
  reporters of membership in the positive radical, not producers of its vanishing;

HT differential rank:
  protects the algebraic leg from finite collapse, but cannot by itself shrink the positive
  radical.
```

The universal missing mathematics is therefore an arithmetic hypertranscendental real
Nullstellensatz: prove that strict positive localization of the ordinary-prime source has no
reduced kernel.  Unlike the withdrawn curvature law, this statement says exactly which ideal must
vanish and why its vanishing locates every zero on the critical line.

- 2026-07-30 — Withdrew source-normal Calkin compactness as an unsupported producer.  Proved the
  positive reflection-radical law `(189)`, derived the Xi real-radicality equivalence `(191)`,
  formalized its unconditional orbit-annihilation and RH-reduction core, and isolated
  `XI_SOURCE_REDUCED_DIVISOR_POSITIVE_DESCENT` as the sole arithmetic producer still missing.

## Positive radical is the base-change Tor of arithmetic attainment

The source-face corpus already proves the parent transmutation law
\[
 0\longrightarrow K/\Xi K
 \longrightarrow
 \ker(T_\Xi)
 \longrightarrow
 \operatorname{Tor}_1^A(\operatorname{coker}T,A/(\Xi))
 \longrightarrow0,                                      \tag{192}
\]
for a two-term observation \(T:M\to N\) over a source ring \(A\), where
\(K=\ker T\) and \(T_\Xi\) is restriction to the Cartier face
\(B_\Xi=A/(\Xi)\).  Here multiplication by \(\Xi\) is required to be injective on \(M\) and
\(N\), as in the proved source-face theorem; flat source modules are a sufficient realization.
The Hilbert realization of the same law identifies
\(\ker(T_\Xi)\) with the boundary Gram radical.  These facts are parent homological algebra and
were already recorded in
`source-face-observation-cohomology-transmutation.md` and
`hypertranscendental-source-face-vanishing-cycle-conservation.md`.

The new conjunction is with the positive reflection-radical law `(189)`.  Suppose:

1. \(T_{\rm ar}:M_{\rm alg}\to M_+\) is constructed before divisor specialization from the
   ordinary-prime Euler-decorated Calderón/Poisson comparison;
2. the source modules are \(\Xi\)-torsion-free and \(T_{\rm ar}\) is generically injective;
3. its Xi-face is the maximal positive star realization of the divisor algebra, not an arbitrary
   positive quotient.

Then `(192)` and `(189)` give, on every finite reflection-stable divisor packet and stalkwise on
the global divisor,
\[
 \boxed{\quad
 \operatorname{Tor}_1^A(\operatorname{coker}T_{\rm ar},B_\Xi)
 \cong
 J_+(B_\Xi)
 =
 \operatorname{Nil}(B_\Xi)
 \oplus
 \bigoplus_{\rho:\,1-\overline\rho\ne\rho}(B_\Xi)_\rho .
 \quad}                                                   \tag{193}
\]
Thus positivity failure, loss of conormal conservativity under completion, and failure of
ordinary base change are not three obstructions.  They are three realizations of one attainment
class.

Equation `(193)` corrects an important possible overstatement.  Vanishing of the complete Tor
class would force
\[
 J_+(B_\Xi)=0,
\]
which is RH plus simplicity of every Xi zero.  RH alone is the reduced statement
\[
 \boxed{\quad
 \mathrm{RH}
 \iff
 \left(
 \operatorname{Tor}_1^A(\operatorname{coker}T_{\rm ar},B_\Xi)
 \right)_{\rm red}=0
 \iff
 T_{\rm ar}\otimes_A B_\Xi^{\rm red}
 \text{ is injective}.
 \quad}                                                   \tag{194}
\]
Here `(194)` is conditional on Clauses 1--3, especially the construction and maximal-positive
identification of the Xi-face.  It is not a proof of RH.

### Which map occupies the comparison slot

The multiplier
\[
 A\xrightarrow{\ \Xi\ }A
\]
is not \(T_{\rm ar}\).  Its cokernel is \(B_\Xi\), so it creates the divisor and has maximal
Xi-torsion by design.  The positive shell immersion
\[
 A\longrightarrow A^{I_N},\qquad
 1\longmapsto(H_m)_{m\in I_N},
\]
is split on \(\Re s>1/2\) because every \(H_m\) is a unit there, but it is only the algebraic
conormal leg.  It has no star-positive target and therefore does not instantiate `(193)`.

The only corpus object with the correct type is the strict arithmetic boundary comparison already
denoted by
\[
 {\mathfrak B}_\Xi
 \quad\text{or}\quad
 \operatorname{BC}^{\dagger}_{\mathfrak R_{\rm ar}}:
 \operatorname{Comp}_{\rm ar}\operatorname{Sp}_\Xi
 \Longrightarrow
 \operatorname{Sp}_\Xi\operatorname{Comp}_{\rm ar}.       \tag{195}
\]
Its finite prime-square Fourier/projective-Weyl restrictions, cross-Gram
\(\mu(n)/n\), closed inverse graph, Wold/Green sector, and Gamma/Poisson faces are constructed
separately.  Their strict all-prime assembly into one pre-divisor morphism remains absent.

### New exact open core

`[BOLD CONJECTURE] [ARITHMETIC_DAGGER_REDUCED_TOR_INDEPENDENCE]`

> The ordinary-prime Euler-decorated Calderón comparison `(195)` exists as a strict
> star-compatible pre-divisor morphism, is generically faithful, has maximal-positive Xi-face, and
> its attainment cokernel is Tor-independent of the reduced Xi Cartier face:
> \[
> \operatorname{Tor}_1^A(
>   \operatorname{coker}\operatorname{BC}^{\dagger}_{\mathfrak R_{\rm ar}},
>   B_\Xi^{\rm red})=0.                                  \tag{196}
> \]

This is the source-side form of the hunch.  Its provability is not part of the conjecture.
Together with `(193)` it implies RH.

`[OPEN CORE] [XI_DAGGER_COMPARISON_REDUCED_TOR_INDEPENDENCE]`

1. Construct the single strict morphism `(195)` from the already compatible finite
   Fourier--Weyl, inverse-cross-Gram, Wold/Green, and Gamma/Poisson data.
2. Prove generic injectivity without completing away the Meyer conormal.
3. Identify its Xi-face with the maximal positive quotient by an actual universal property.
4. Prove \(\Xi_{\rm red}\)-regularity of its attainment cokernel from the integral
   ordinary-prime source complex.

Clause 4 is weaker than surjectivity, closed range, flatness of the full cokernel, or a faithful
positive realization of nilpotent jets.  It asks only that no reduced Xi-supported class be born
from generic nonattainment.

### Consequences for the obstruction census

```text
finite exact packets:
  Tor vanishes packetwise, but strict all-prime assembly can create attainment cohomology;

ordinary adelic L2:
  the comparison kills all point conormals, so it is maximally non-Tor-independent at the
  divisor face;

raw analytic/Ind completion:
  the conormals survive, but the target is not the maximal positive star quotient, so `(193)`
  does not apply;

positive HT shells:
  split the algebraic leg and retain every reduced stalk, but do not construct the horizontal
  arithmetic-positive comparison;

Wold, Kakutani, Stokes, Ward, Calkin, and Weil defects:
  scalar, metric, or index images of the same Tor-supported positive radical;

nontrivial multiplicity:
  nilpotent Tor which must remain in the algebraic leg and is irrelevant to RH after reduced
  base change;

off-line zero:
  a reduced Tor class forced into the attainment cokernel of every putative maximal-positive
  arithmetic comparison.
```

This also gives a falsifier.  If a constructed `(195)` has a nonzero reduced
\(\Xi\)-torsion class, that class is not a technical completion error: under `(193)` it is the
exact off-line divisor sector which the source comparison cannot attain positively.

### Hostile audit of the shell-fusion shortcut

The raw shell-fusion star-covariance proposed elsewhere cannot supply Clause 4.  At the positive
source point \(s=1\),
\[
 C_N(1)=\operatorname{diag}(\sqrt{h_m}),\qquad
 P_N=(\sqrt{h_mh_n})_{m,n}.
\]
Therefore
\[
 (C_NP_NC_N^{-1})_{m,n}=h_m,
 \qquad
 (C_NP_NC_N^{-1})^\ast_{m,n}=h_n.                       \tag{197}
\]
The shell masses are not constant: the proved law \(2^mh_m\to1/2\) gives \(h_m\to0\), while every
\(h_m>0\).  Hence raw star-covariance already fails on some finite source aperture.  Gauge
reduction leaves the Toeplitz character selector, but proving it unitary after choosing a Xi
fibre is RH-equivalent.  It is not the pre-divisor comparison `(195)`.

The parent base-change mechanism in `(192)` is standard Tor-independence; the parent positive
radical mechanism in `(189)` is standard positive/GNS representation theory.  The exact
arithmetic conjunction `(193)`--`(196)` was not found in the corpus or targeted literature
searches.  Candidate novelty lies only in constructing `(195)` and proving its source-specific
reduced Tor-independence, not in either parent theorem.

- 2026-07-30 — Combined source-face Tor transmutation with the positive reflection-radical law.
  Identified the off-line reduced divisor as the reduced base-change Tor of the unique correctly
  typed arithmetic positive comparison, separated it from the divisor-producing Xi multiplier
  and algebraic shell immersion, isolated reduced rather than full Tor vanishing as the RH target,
  and found the source-point obstruction `(197)` to raw shell-fusion star covariance.

## Conservation is not purity: the missing law is source saturation

The continuation--record interpretation needs one further correction.  Retaining every
complementary record does not make that record vanish.  For every strict disk point \(w\), the
scalar contraction \(w\) has a conservative unitary dilation, and compression produces the
Poisson state with exact Kadison defect
\[
 1-|w|^{2m}.
\tag{198}
\]
The full dilation is lossless for every \(w\), including every off-circle \(w\).  Thus a universal
law of the form
\[
 \text{continuation}+\text{complete record}=\text{conservation}
\]
is compatible with off-line zeros.  It explains where their information goes; it does not force
the information-loss channel to be trivial.  The source must prove a stronger statement:
specialization is **saturated** in the positive reporter topology.

### Local Shilov base change

Let \(\mathcal S_{\rm ar}\) denote the still-to-be-constructed local operator space generated by
all finite ordinary-prime Fourier--Weyl, Gamma--Poisson, BV/Wold, HT boundary, and flat-grade
reporter matrices.  "Local" is essential: one norm erases either the dense nonclosed Gamma class,
the Calkin separated class, or the all-orders-flat HT class.  Let
\[
 q_{\Xi,\mathrm{red}}:
 \mathcal S_{\rm ar}\longrightarrow
 \mathcal S_{\Xi,\mathrm{red}}
\tag{199}
\]
be reduced Xi specialization, defined on the source complex before a zero is selected.

Recent parent theory constructs an \(\mathcal R\)-\(C^*\)-envelope and an
\(\mathcal R\)-Shilov ideal for unital local operator spaces.  If `(199)` is a legitimate complete
quotient, envelope universality gives a base-change comparison of the form
\[
 \beta_{\Xi,\mathrm{red}}:
 \mathcal E_{\mathcal R}(\mathcal S_{\rm ar})/
 I_{\Xi,\mathrm{red}}
 \twoheadrightarrow
 \mathcal E_{\mathcal R}(\mathcal S_{\Xi,\mathrm{red}}).
\tag{200}
\]
Its kernel is the local Shilov defect of specializing after positive completion.

For a finite reflection-stable divisor algebra, the already-proved law `(189)` identifies the
null ideal of its universal positive \(C^*\)-seminorm:
\[
 \ker\!\left(A_D\longrightarrow C_u^*(A_D)\right)
 =
 J_+(A_D)
 =
 \operatorname{Nil}(A_D)
 \oplus
 \bigoplus_{\rho:\tau\rho\ne\rho}A_\rho ,
\tag{201}
\]
and hence
\[
 C_u^*(A_D)
 \cong
 \bigoplus_{\rho:\tau\rho=\rho}\mathbb C .
\tag{202}
\]
Thus, once `(199)`--`(200)` are constructed and their Xi-face is identified with the universal
positive divisor realization, the reduced Shilov base-change defect and the reduced Tor class in
`(193)` are the same support:
\[
 \left.\ker\beta_{\Xi,\mathrm{red}}\right|_{D_\Xi}
 \cong
 \left(
 \operatorname{Tor}_1^A(
   \operatorname{coker}\operatorname{BC}^{\dagger}_{\mathfrak R_{\rm ar}},
   B_\Xi)
 \right)_{\mathrm{red}}
 \cong
 \bigoplus_{\rho:\,1-\bar\rho\ne\rho}(B_\Xi)_\rho .
\tag{203}
\]
Equation `(203)` is conditional on construction of the comparison and both universal-property
identifications.  It is not inferred from generic operator-system theory.

### Hypertranscendence becomes saturation, not merely rank

The source-logarithmic-boundary theorem proves that every finite nonlinear differential circuit
of a multiplicative HT family is represented by a linear class over \(\mathbb C[D]\).  This gives
generic algebraic freeness.  The finite-reporter collapse theorem proves that no fixed
finite-dimensional reporter detects the full HT source.  The all-orders-flat theorems prove that
even all finite jets do not give a separated completion.

These results point to the missing general HT theorem:

`[BOLD CONJECTURE] [ENHANCED_HT_REDUCED_ENTIRE_SATURATION]`

> After retaining the simultaneous logarithmic source-boundary module, all Stokes/flat grades,
> the integral source action, and every matrix reporter level, the reduced attainment module of a
> source-minimal constrained HT comparison is torsion-free over the ring of entire spectral
> functions.  Equivalently, every reduced analytic divisor specialization is pure on the complete
> source reporter module.

The ring of entire functions is a Bezout, hence Prüfer, domain; for an honest module over it,
torsion-free implies flat.  Therefore the conjecture would give
\[
 \operatorname{Tor}_1^A(C_{\rm ar}^{\mathrm{red}},A/(f))=0
 \qquad
 \text{for every nonzero entire }f,
\tag{204}
\]
and in particular for \(f=\Xi_{\mathrm{red}}\).  With `(193)`, this proves RH.

The qualification "honest module" is load-bearing.  The corpus already excludes replacing the
singular completion by an ordinary derived limit of acyclic finite fibres.  Polynomial
differential freeness over \(\mathbb C[D]\) does not imply entire, bornological, or matricial
saturation.  Equation `(204)` is new mathematical content only if the source comparison module
is constructed and its torsion-freeness is proved from the HT boundary calculus.

The positive/operator version is the sharper arithmetic specialization:

`[BOLD CONJECTURE] [ARITHMETIC_HT_LOCAL_SHILOV_SATURATION]`

> The literal ordinary-prime Euler--Gamma--Poisson source defines `(199)` as a Hausdorff complete
> quotient on the full local matricial HT reporter space; `(200)` is injective after reduced Xi
> base change; and its algebraic Xi-face retains every reduced principal conormal atom before the
> universal positive envelope is taken.

Under `(201)`--`(203)`, this conjecture is equivalent to RH.  Its provability is not part of the
conjecture.

### Quantitative finite falsifier

The local formulation exposes a finite-stage test that the previous category language hid.  For
finite prime/Gamma aperture \((P,N)\), matrix level \(k\), and reduced source quotient
\(q_{P,N}\), let
\[
 \lambda_{P,N,k}(y)
 :=
 \inf\{\|x\|:\ q_{P,N}(x)=y\}.
\tag{205}
\]
Local complete-quotient saturation requires compatible lifts whose constants stay controlled in
every fixed source seminorm as \(P,N,k\) become cofinal.  If an off-line reduced Xi atom exists,
then under the source-face identification in `(203)` some such lifting profile must escape every
admissible control family.  Conversely, a source-derived cofinal complete-quotient estimate,
including the flat grade and not only scalar or finite-jet norms, would kill the reduced Tor
class and prove RH.

This is the first non-tautological producer target left by the synthesis:

`[OPEN CORE] [XI_COFINAL_MATRICIAL_SOURCE_SATURATION]`

1. construct \(\mathcal S_{\rm ar}\) from the explicit finite clock and HT reporter matrices;
2. prove the finite quotient maps and their Gamma--Poisson compatibility before Xi
   specialization;
3. prove cofinal controlled lifting at every matrix level, retaining the all-orders-flat grade;
4. identify the resulting local Shilov defect with the Tor/positive radical in `(203)`.

Plain record conservation, a unitary dilation, algebraic \(\mathbb C[D]\)-freeness, a normed
\(C^*\)-envelope, or finite-stage complete positivity proves none of these four items.

Parent boundaries are operator-system quotients and exactness
(`arXiv:1008.2811`), tensorial \(C^*\)-envelopes and Shilov ideals
(`arXiv:2202.12144`), product-system covariance envelopes
(`arXiv:2012.12435`), and the 2026 local \(\mathcal R\)-Shilov envelope
(`arXiv:2602.03628`).  Those sources provide the ambient language and existence theorems; they do
not construct `(199)` for the Riemann source or prove `(203)`--`(205)`.

- 2026-07-30 — Corrected the record-conservation hunch: conservative Stinespring dilation exists
  for every off-line Poisson state and cannot be the selector.  Reinterpreted the missing
  hypertranscendental theorem as reduced entire/matricial source saturation, identified its
  positive face with local Shilov base change, and extracted cofinal matrix lifting as a concrete
  finite falsifier and proof target.
