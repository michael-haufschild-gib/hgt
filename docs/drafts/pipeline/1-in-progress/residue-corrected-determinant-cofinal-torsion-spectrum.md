# Residue-corrected determinant cofinal torsion spectrum

**Status:** 1-in-progress  
**Claim ID:** `ROUTE_R_RESIDUE_CORRECTED_COFINAL_TORSION_SPECTRUM`  
**Opened:** 2026-08-03  
**Route:** R / Program 4 (`ROUTE_R_ARAKELOV_RESIDUE_DETERMINANT_CHARACTER`)  
**Primary carrier:** nested prime-sieve Wold operator  
**Formalization status:** finite algebra, cleared excision, residue-jet character, torsion cocycle,
all-order spectral-suspension cancellation, factorial moment-matrix nonsingularity, and exact
forward/converse compact-open convergence criterion compile unconditionally in Lean; construction
and continuity of Schatten/Fredholm/zeta determinants and arithmetic Mertens layers remain  
**Novelty status:** Hartmann--Lesch fixed-operator zeta--Fredholm factorization is
`[REDISCOVERED]`; no collision found for cofinal residue-jet completeness, all-order graded
spectral-suspension sharpness, cofinal classification, Mertens-system universality, number-field
lift, determinant excision, or Baire-generic maximal spectrum

## Rational special case

Let \(\mathbb P\) be the set of rational primes. For a finite set
\(P\subset\mathbb P\), put

\[
 a(P):=\prod_{p\in P}\left(1-\frac1p\right),\qquad
 b(P):=\gamma+\sum_{p\in P}\frac{\log p}{p-1},\qquad
 \kappa(P):=a(P)b(P).
\]

For a permutation \(\sigma=(q_1,q_2,\ldots)\) of the primes, let
\(P_n^\sigma=\{q_1,\ldots,q_n\}\), and let
\(C(\sigma)\) be the cluster set of \(\kappa(P_n^\sigma)\) in the extended
half-line \([0,\infty]\).

> **[PROVED ON PAPER] Cofinal torsion-spectrum theorem.**
> The sets \(C(\sigma)\), as \(\sigma\) ranges over all permutations of the
> primes, are exactly the nonempty closed intervals
> \[
> [\alpha,\beta]\subset [e^{-\gamma},\infty],
> \qquad e^{-\gamma}\le \alpha\le\beta\le\infty.
> \]

This is rational special case. Determinant, residue, and relative-torsion
statements below are proved consequences and intrinsic interpretation.

## Strengthened exact claim

For every number field \(K\), with Dedekind-zeta residue \(\rho_K\), Euler--Kronecker
constant \(\gamma_K\), and finite prime-ideal set \(P\), put

\[
 \kappa_K(P)=\rho_K\prod_{\mathfrak p\in P}
 \left(1-\frac1{N\mathfrak p}\right)
 \left(\gamma_K+\sum_{\mathfrak p\in P}
 \frac{\log N\mathfrak p}{N\mathfrak p-1}\right).
\]

> **[PROVED ON PAPER] Number-field cofinal universality.** Along arbitrary
> orderings of all nonzero prime ideals, cluster sets of \(\kappa_K(P_n)\) are
> exactly nonempty closed intervals in \([e^{-\gamma},\infty]\). Every interval
> occurs. Endpoint is independent of \(K\).

This is instance of abstract Mertens-system theorem: same classification holds
for every proper Euler-atom system with

\[
 \rho a(\mathcal A(x))\log x\to c_*>0,
 \qquad
 \sum_{q(v)\le x}\frac{\log q(v)}{q(v)-1}-\log x\to C.
\]

Every interval fibre is dense in ordering space, full spectrum is comeagre,
all proper fibres are dense meagre, and cluster-spectrum map is nowhere
continuous. Number-field determinant lift uses ideal-norm operator and has
exact prime-ideal excision.

## Universal residue-jet law

> **[PROVED ON PAPER] Cofinal Schatten law.** For admissible positive operators
> \(L_n\) with \(L_n^{-1}\to A\) in \(\mathcal S_p\), corrected jet
> 
> \[
> b_j(L_n)=-\frac1j\left(\operatorname*{FP}_{s=j}\zeta_{L_n}(s)
> +H_{j-1}\operatorname*{Res}_{s=j}\zeta_{L_n}(s)\right)
> \]
> is complete invariant of compact-open zeta-determinant clustering. Cluster
> map is topological embedding
> 
> \[
> b\mapsto e^{\sum_{j=1}^{p-1}b_jz^j}\det_p(I-zA),
> \]
> and divisor-cancelled relative torsion is exponential polynomial of jet
> difference.

Fixed-operator factorization is due to Hartmann--Lesch and is not claimed.
New statement is converse cofinal completeness and exact transport of cluster
topology/torsion.

> **[PROVED ON PAPER] Full-jet sharpness.** For every \(p\ge2\), graded spectral
> suspensions with weights
> 
> \[
> w_{j,r}=(-1)^{j-r}\binom jr
> \]
> cancel every lower moment and retain \(V_j(j)=j!\). Along Baire-generic
> colored-prime orderings, corrected virtual-jet cluster set has nonempty
> interior in \(\mathbb R^{p-1}\), while constituent \(\mathcal S_p\) limits,
> integer zeta residues, and virtual divisor converge. Relative torsions
> generate every character \(\exp(\sum_{j=1}^{p-1}v_jz^j)\).

## Exact determinant package

On \(H=\ell^2(\mathbb N_{>0})\), let \(Qe_m=m^{-1}e_m\), and let \(Q_P\)
be its compression to the basis vectors with \((m,M_P)=1\), where
\(M_P=\prod_{p\in P}p\). Then

\[
 Z_P(s):=\operatorname{Tr}(Q_P^s)
 =\zeta(s)\prod_{p\in P}(1-p^{-s}),
 \]

with

\[
 \operatorname*{Res}_{s=1}Z_P(s)=a(P),\qquad
 \operatorname*{FP}_{s=1}Z_P(s)=\kappa(P).
\]

Define the residue-corrected determinant

\[
 \Delta_P(z)
 :=\lim_{N\to\infty}N^{a(P)z}
 \prod_{\substack{1\le m\le N\\(m,M_P)=1}}
 \left(1-\frac zm\right).
\]

The target paper must prove all equalities

\[
 \Delta_P(z)
 =e^{-\kappa(P)z}\det{}_2(I-zQ_P)
 =M_P^{a(P)z}
 \prod_{\substack{1\le r\le M_P\\(r,M_P)=1}}
 \frac{\Gamma(r/M_P)}{\Gamma((r-z)/M_P)}.
\]

If \(p\notin P\), prime excision must be proved in the exact form

\[
 \Delta_{P\cup\{p\}}(z)
 =p^{-a(P)z/p}\frac{\Delta_P(z)}{\Delta_P(z/p)}.
\]

For every prime permutation, \(Q_{P_n^\sigma}\to |e_1\rangle\langle e_1|\)
in Hilbert--Schmidt norm. Hence every finite \(c\in C(\sigma)\) must give the
compact-open determinant cluster value

\[
 \Delta_c(z)=e^{(1-c)z}(1-z).
\]

All \(\Delta_c\) have the same divisor \([z=1]\), while

\[
 \mathcal T_{c,d}(z):=\frac{\Delta_c(z)}{\Delta_d(z)}=e^{(d-c)z}
\]

is nontrivial relative determinant torsion and satisfies
\(\mathcal T_{c,d}\mathcal T_{d,e}=\mathcal T_{c,e}\). Thus divisor or
determinant-line triviality forgets the entire real torsion coordinate.

## Why this is the Fields-level conjecture at this frontier

The scalar divisor is rigid and uninformative. The hard object is the set of
all cofinal secondary residues under arbitrary prime orderings. Exact interval
classification would reverse ontology:

- not one canonical all-prime determinant, but a torsor of determinant germs;
- not primary residue alone, but finite-part/secondary-residue transport;
- not absolute flat countertransport, but relative torsion between cofinal
  lifts;
- not arbitrary finite-set density, but nested exhaustive realizability.

It compresses four existing obstructions into one exact theorem: det2 loses
first trace, primary BV residue vanishes cofinally, determinant divisors agree,
and analytic torsion still retains a continuous real modulus.

## Conjecture--attack ledger

### Attack 0: plain determinant-line triviality

`[KNOWN]` A line over a contractible base is trivial, but a chosen section may
have any divisor. This cannot control nonvanishing or the critical locus.

**Disposition:** `[DEAD END]`; retained only as motivation.

### Attack 1: add a Wodzicki correction to Quillen/Bismut--Freed curvature

Paycha--Rosenberg already identify the Bismut--Freed curvature defect with
Wodzicki-residue terms. Kontsevich--Vishik and Scott already separate local
multiplicative residue determinants from nonlocal, nonmultiplicative zeta
determinants.

**Disposition:** `[REDISCOVERED] [BRIDGE]`; not new scientific knowledge.

### Attack 2: scalar \(\kappa(P)\) has a continuum of finite-set values

Diamond--Ford define exactly \(\kappa(P)\) as a generalized Euler constant,
prove that its finite-set values are dense in \([\Gamma,\infty)\), reduce the
global infimum to initial prime segments, and relate the inequality against
\(e^{-\gamma}\) to RH.

**Disposition:** `[REDISCOVERED]`; finite-set density cannot be paper claim.

### Attack 3: arbitrary finite-set density implies cofinal density

False inference. Diamond--Ford's approximating sets need not be nested and
need not exhaust the primes. Cofinality imposes persistent inclusion of every
initial prime segment.

**Disposition:** `[DEAD END]`; exact missing theorem is permutation/cluster-set
classification.

### Attack 4: cofinal limit can lie below \(e^{-\gamma}\)

Expected obstruction: a relative form of Diamond--Ford's extremal descent.
If \(P\) contains the first \(k\) primes, descent operations should preserve
them and yield

\[
 \kappa(P)\ge \inf_{r\ge k}\kappa(P_r^{\mathrm{nat}}).
\]

Since the right side tends to \(e^{-\gamma}\), every cofinal cluster point is
at least \(e^{-\gamma}\), even if RH is false and the unrestricted finite-set
infimum \(\Gamma\) is smaller.

**Status:** proved on paper, including repeated prime-ideal norm ties via
strictly decreasing reference-index potential.

### Attack 5: cluster sets may be disconnected

For one-prime extension,

\[
 \kappa(P\cup\{p\})-\kappa(P)
 =\frac{a(P)}p\bigl(\log p-b(P)\bigr).
\]

Along a permutation, the inserted primes tend to infinity. On any bounded
\(\kappa\)-window, the one-step jumps should therefore tend to zero. Any path
visiting two finite cluster values must accumulate at every intermediate
value.

**Status:** proved on paper with bounded local crossing argument, including
infinite endpoint.

### Attack 6: every interval is realizable

Two controls are available:

1. **Downward control:** fill all omitted primes up to a growing cutoff. From
   any fixed finite source set this drives \(\kappa\) toward
   \(e^{-\gamma}\).
2. **Upward control:** after a finite set \(P\), add a far prime block
   \((y,e^u y]\). Prime number theorem and Mertens estimates give negligible
   primary-residue and Hilbert--Schmidt changes but a prescribed positive
   finite-part shift.

Alternating increasingly accurate downward and upward controls should realize
every \([\alpha,\beta]\), while forcing inclusion of the least omitted prime at
each stage.

**Status:** proved on paper. Finite, infinite, singleton, and \(\{\infty\}\)
cases separated; every downward stage consumes a least missing atom.

## Novelty audit

### Closest established results

1. H. G. Diamond and K. Ford, *Generalized Euler constants*, Math. Proc.
   Cambridge Philos. Soc. 145 (2008), 27--41,
   DOI `10.1017/S0305004108001187`.
   Exact scalar formula, finite-set density, extremal initial segments, and RH
   equivalence. No prime-permutation cluster-set classification found.
2. S. Paycha and S. Rosenberg, *Curvature on determinant bundles and first
   Chern forms*, arXiv:`math/0009172`. Bismut--Freed curvature correction by
   Wodzicki residues.
3. M. Kontsevich and S. Vishik, *Determinants of elliptic
   pseudo-differential operators*, arXiv:`hep-th/9404046`. Canonical trace,
   determinant central extension, and multiplicative anomaly.
4. S. Scott, *The residue determinant*, arXiv:`math/0406268`. Local
   multiplicative Wodzicki determinant versus nonlocal zeta determinant.
5. S. Scott, relative zeta determinants and Quillen metrics,
   arXiv:`math/9910148`; W. Müller, relative zeta functions and determinants,
   Comm. Math. Phys. 192 (1998), 309--347.
6. J.-M. Bismut--H. Gillet--C. Soulé/Bismut--Freed determinant-line theory;
   X. Dai--D. Freed eta/determinant-line gluing; U. Bunke determinant classes
   in Deligne cohomology. These make a broad differential-character claim
   non-novel unless source-specific cofinal content is proved.

### Search verdict

`[NO COLLISION FOUND]` for classification of cluster sets of \(\kappa(P_n)\)
along permutations/exhaustive nested finite sets of primes. This is not proof
of priority. Repeat search after theorem wording stabilizes and inspect citing
literature around Diamond--Ford.

## Paper-proof dependency graph

1. [done] Finite-part trace formula for \(Z_P\).
2. [done] Existence, det2 identity, and Gamma product for \(\Delta_P\).
3. [done] Exact one-prime excision and cubical coherence.
4. [done] Hilbert--Schmidt cofinal convergence of \(Q_P\).
5. [done] Relative extremal lemma for supersets of initial prime segments.
6. [done] Vanishing local jump lemma on bounded windows.
7. [done] Localized upward block lemma with quantitative error.
8. [done] Downward cutoff lemma from arbitrary finite source.
9. [done] Interval realization construction, finite upper endpoint.
10. [done] Infinite upper endpoint and singleton cases.
11. [done] Necessity/classification theorem.
12. [done] Compact-open determinant cluster theorem.
13. [done] Relative torsion cocycle and no-descent theorem.
14. [done] Quillen/Bismut--Freed/Wodzicki comparison with claims sharply separated
    into established general theory and new arithmetic spectral theorem.

## Lean plan

No Lean implementation before items 1--13 have dependency-closed paper proofs.
Formal target must be unconditional. It will separate:

- finite-set algebra: \(a,b,\kappa\), one-prime update, excision cocycle;
- abstract cluster-set topology: vanishing mesh implies interval cluster set;
- abstract two-control realization theorem, with PNT/Mertens facts supplied as
  explicit hypotheses only if mathlib lacks analytic-number-theory theorems;
- unconditional instantiated theorems may not assume unproved PNT/Mertens
  placeholders. Missing analytic infrastructure must be proved or imported
  from verified mathlib declarations;
- determinant analytic identities only after checking available complex Gamma
  and Fredholm determinant infrastructure. No fake finite-dimensional proxy
  may be presented as formalization of the analytic theorem.

Before reusable Lean work, run

```text
scripts/formal_tools.py research "generalized Euler constant cluster interval determinant"
```

and verify every mathlib name in `/tmp` with `lake env lean`.

## Hostile-review gates

- Reject if main theorem reduces to Diamond--Ford Proposition 2 by deleting
  nested/exhaustive constraint.
- Reject if Wodzicki terminology is used without an exact residue theorem.
- Reject if relative torsion is only a renamed ratio and no cofinal
  classification/no-descent result is proved.
- Reject if determinant-line discussion overclaims RH or nonvanishing.
- Reject if any result depends on RH.
- Reject if formalization proves only finite algebra while paper advertises
  analytic determinants or cofinal classification as Lean-verified.
- Reject if novelty audit omits citing literature after 2008.

## Progress log

### 2026-08-03

- Internal audit killed plain determinant-line triviality, scalar det2
  annihilation, absolute inverse-gain countertransport, and second-order
  Koplienko regularization.
- External audit classified broad residue-corrected Quillen determinant claim
  as `[REDISCOVERED] [BRIDGE]`.
- Exact scalar \(\kappa(P)\) identified with Diamond--Ford generalized Euler
  constant; earlier continuum conjecture retired as `[REDISCOVERED]`.
- Fields-level replacement frozen: cofinal prime-permutation cluster-set
  classification plus determinant-torsion interpretation.
- Open core: relative extremal lemma and interval realization with nested
  exhaustive blocks.
- Rational open core closed. Strengthened theorem covers every number field;
  Dedekind residue cancels number-field Mertens constant at universal endpoint
  \(e^{-\gamma}\).
- Abstract Mertens-system theorem isolated two sufficient asymptotics.
- Baire audit proves full torsion spectrum is generic, every prescribed
  interval fibre dense, and spectrum map nowhere continuous.
- Paper draft compiles and rendered PDF passed full-page visual inspection.
- Remaining open core: unconditional Lean formalization plus hostile review at
  renowned-general-journal bar.
- Universal-law pivot: Hartmann--Lesch collision removed fixed-operator
  factorization from novelty claim. Proved cofinal residue-jet completeness.
- Proved all-order graded spectral-suspension realization. Finite-difference
  weights cancel lower residue coordinates exactly and preserve factorial
  diagonal; Baire-generic joint spectrum is full-dimensional.
- Added unconditional Lean modules
  `ResidueCorrectedDeterminantCofinalTorsion.lean` and
  `ResidueJetSpectralSuspension.lean`; both pass `lake env lean`, and umbrellas
  import both modules.
- Formal polynomial coefficient recovery proves full corrected jet is a complete
  invariant of its counterterm polynomial; affected module passes Lean compilation.
- Lean proves suspension moment matrix is upper triangular with exact factorial
  determinant, hence nonsingular in every order; it also proves supported polynomial
  surjectivity and realization of every jet character as relative torsion.
- Added wired ResidueJetCompactOpen module.  Lean bundles determinant characters in
  compact-open continuous-map topology and proves convergence iff full corrected jet
  converges after eventual zero-free cancellation of convergent common core.
