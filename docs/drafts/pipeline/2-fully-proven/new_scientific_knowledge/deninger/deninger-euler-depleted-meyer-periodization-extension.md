# Euler-depleted Meyer periodization extension

- **ID:** `deninger-euler-depleted-meyer-periodization-extension`
- **Stage:** 2-fully-proven
- **Type:** SOURCE ADMISSION / STRICT EXACT-SEQUENCE THEOREM
- **Label:** `DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** for every prime $p$, deleting the $p$-Euler orbit from Meyer's Poisson
  differential produces a strict nuclear extension whose canonical zero-periodization sector is
  exactly the full Meyer quotient $M_\zeta$.  Thus one prime already gives a conservative closed
  admission of every middle class, while every form factoring only through the compact
  prime-circle trace vanishes on that entire admitted sector.

## 1. The actual source operator

Write $t=\log x$, $L=\log p$, and identify Meyer's target $H_-$ with the nuclear Fr\'echet
space
\[
 \mathscr S_{\exp}(\mathbb R)
 =\{h\in C^\infty(\mathbb R):e^{kt}h(t)\in\mathcal S(\mathbb R)
      \text{ for every }k\in\mathbb Z\}.
\tag{1}
\]
Equivalently, all derivatives decay faster than every exponential at both ends.  Put
\[
 (\tau_Lh)(t)=h(t+L),\qquad \Delta_p=1-\tau_L.
\tag{2}
\]
We use the equivalent countable Fr\'echet seminorm family
\[
 q_{a,m,n}(h)
 =\sup_{t\in\mathbb R}e^{a|t|}(1+|t|)^m|h^{(n)}(t)|,
 \qquad a,m,n\in\mathbb N.
 \tag{2a}
\]
This is Meyer's projective-limit topology: multiplication by every integral exponential weight
lands in the ordinary Schwartz space.  It is nuclear because the diagonal realization in the
countable product of those weighted Schwartz spaces is closed.
For the literal Poisson operator
\[
 (Zf)(e^t)=\sum_{n\ge1}f(ne^t),
\]
absolute convergence in the Meyer topology gives the Euler-depletion identity
\[
 \Delta_pZf(t)
 =\sum_{\substack{n\ge1\\p\nmid n}}f(ne^t)
 =:Z^{(p)}f(t).
\tag{3}
\]
No Euler product continuation is used: the second sum in
$Zf(t)-Zf(t+L)$ is exactly the subseries indexed by multiples of $p$.

## 2. Multiplicative periodization

Define
\[
 \operatorname{Per}_p(h)(\bar t)
 =\sum_{j\in\mathbb Z}h(t+jL),
 \qquad \bar t\in\mathbb R/L\mathbb Z.
\tag{4}
\]
The series and every differentiated series converge absolutely and uniformly on a fundamental
interval.  Hence `(4)` is a continuous linear map
\[
 \operatorname{Per}_p:\mathscr S_{\exp}(\mathbb R)
 \longrightarrow C^\infty(\mathbb R/L\mathbb Z).
\]

`[PROVED HERE] [DAC_DENINGER_MULTIPLICATIVE_PERIODIZATION_EXACT_SEQUENCE]`

There is a split strict exact sequence of nuclear Fr\'echet spaces
\[
 0\longrightarrow \mathscr S_{\exp}(\mathbb R)
 \xrightarrow{\ \Delta_p\ }
 \mathscr S_{\exp}(\mathbb R)
 \xrightarrow{\ \operatorname{Per}_p\ }
 C^\infty(\mathbb R/L\mathbb Z)
 \longrightarrow0.
\tag{5}
\]
More precisely,
\[
 \operatorname{im}\Delta_p=\ker\operatorname{Per}_p,
\tag{6}
\]
and the inverse of \(\Delta_p\) on this closed kernel is the two-sided Green sum
\[
 G_p h(t)
 =\sum_{j\ge0}h(t+jL)
 =-\sum_{j<0}h(t+jL)
 \qquad(h\in\ker\operatorname{Per}_p).
\tag{7}
\]

### Proof

Telescoping gives
\[
 \operatorname{Per}_p(\Delta_ph)
 =\sum_{j\in\mathbb Z}
   \bigl(h(t+jL)-h(t+(j+1)L)\bigr)=0.
\]
If \(\Delta_ph=0\), then $h(t)=h(t+nL)$ for every $n\ge0$.  Letting $n\to\infty$ and using
the positive-end decay in `(1)` gives $h(t)=0$, so \(\Delta_p\) is injective.

If \(\operatorname{Per}_p(h)=0\), the two series in `(7)` agree because their difference is
`(4)`.  The positive series gives rapid exponential decay as $t\to+\infty$, and the negative
series gives it as $t\to-\infty$.  The same argument applies after every derivative.  Quantitatively,
for every defining seminorm $q_{a,m,n}$ of `(1)` there is a constant $C=C(a,m,n,L)$ such that
\[
 q_{a,m,n}(G_ph)\le Cq_{a+1,m+1,n}(h).
\tag{8}
\]
Indeed, for $t\ge0$ use the first series in `(7)`, and for $t\le0$ use the second.  After
multiplication by $e^{a|t|}(1+|t|)^m$, the summands are bounded by a geometric series using the
$a+1$ exponential weight; the extra polynomial power absorbs the fixed fundamental interval.
Thus $G_p:\ker\operatorname{Per}_p\to\mathscr S_{\exp}$ is continuous.  Direct telescoping gives
$\Delta_pG_ph=h$, proving `(6)` and strictness of the first arrow.

Choose a compactly supported smooth partition function \(\chi\) satisfying
\[
 \sum_{j\in\mathbb Z}\chi(t+jL)=1.
\]
For a smooth $L$-periodic function $F$, the compactly supported lift
\[
 s_\chi(F)(t)=\chi(t)F(\bar t)
\]
belongs to `(1)`, depends continuously on $F$, and satisfies
\(\operatorname{Per}_p s_\chi(F)=F\).  This proves surjectivity and a continuous linear splitting.
The kernel in `(6)` is closed, so `(5)` is split strict.  Nuclearity is inherited from Meyer's
nuclear target and the standard nuclearity of $C^\infty$ on a compact circle.

## 3. The depleted Meyer quotient

Let $H_\cap$ be Meyer's endpoint-zero Schwartz source and use his proved strict closed embedding
\[
 Z:H_\cap\hookrightarrow H_-.
\]
By `(3)` and `(5)`,
\[
 Z^{(p)}=\Delta_pZ:H_\cap\hookrightarrow H_-
\tag{9}
\]
is again a strict closed embedding: \(\Delta_p\) is a topological isomorphism from $H_-$ onto
the closed space \(\ker\operatorname{Per}_p\), and it carries the closed subspace $Z(H_\cap)$
onto $Z^{(p)}(H_\cap)$.  Define the source-only depleted quotient
\[
 M_\zeta^{(p)}=H_-/Z^{(p)}(H_\cap).
\tag{10}
\]
It is a Hausdorff nuclear Fr\'echet representation, constructed without a zero divisor.

`[PROVED HERE] [DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION]`

The formulas
\[
 \iota_p([g])=[\Delta_pg],\qquad
 \overline{\operatorname{Per}}_p([h])=\operatorname{Per}_p(h)
\tag{11}
\]
give a split strict exact sequence
\[
 0\longrightarrow M_\zeta
 \xrightarrow{\ \iota_p\ }
 M_\zeta^{(p)}
 \xrightarrow{\ \overline{\operatorname{Per}}_p\ }
 C^\infty(\mathbb R/\log p\,\mathbb Z)
 \longrightarrow0.
\tag{12}
\]
Its admitted middle sector is canonical:
\[
 \iota_p(M_\zeta)
 =\ker\overline{\operatorname{Per}}_p.
\tag{13}
\]

### Proof

Equation `(3)` makes \(\iota_p\) well-defined, and

\[
 \Delta_pg\in Z^{(p)}(H_\cap)
 \Longleftrightarrow
 \Delta_pg=\Delta_pZf\text{ for some }f
 \Longleftrightarrow
 g=Zf,
\tag{14}
\]
where the last equivalence is injectivity of \(\Delta_p\).  This proves injectivity and the exact
one-prime conservative boundary law.

Because $Z^{(p)}(H_\cap)\subset\ker\operatorname{Per}_p$, periodization descends to `(10)`.
Using `(6)`,
\[
 \ker\overline{\operatorname{Per}}_p
 =\ker\operatorname{Per}_p/Z^{(p)}(H_\cap)
 =\Delta_pH_-/\Delta_pZ(H_\cap)
 =\iota_p(M_\zeta).
\]
Surjectivity and a continuous splitting descend from $s_\chi$.  The homeomorphism
\(\Delta_p:H_-\to\ker\operatorname{Per}_p\), followed by passage to closed quotients, proves that
\(\iota_p\) is a strict closed embedding.  This proves `(12)`--`(13)`.

Translations on the logarithmic line commute with \(\Delta_p\) and descend to rotations on the
prime circle, so `(12)` is flow-equivariant.  The auxiliary partition-of-unity splitting need not
be flow-equivariant; only the kernel sector `(13)` is canonical.

## 4. Finite Euler-depletion tower

For a finite set $S$ of primes, put
\[
 \Delta_S=\prod_{p\in S}\Delta_p,\qquad
 Z^{(S)}=\Delta_SZ,qquad
 M_\zeta^{(S)}=H_-/Z^{(S)}(H_\cap).
\tag{15}
\]
The commuting difference operators make `(15)` independent of an ordering of $S$.

`[PROVED HERE] [DAC_DENINGER_FINITE_EULER_DEPLETION_TOWER]`

If $q\notin S$, there is a split strict exact sequence
\[
 0\longrightarrow M_\zeta^{(S)}
 \xrightarrow{[g]\mapsto[\Delta_qg]}
 M_\zeta^{(S\cup\{q\})}
 \xrightarrow{\overline{\operatorname{Per}}_q}
 C^\infty(\mathbb R/\log q\,\mathbb Z)
 \longrightarrow0.
\tag{16}
\]
Indeed, $Z^{(S\cup\{q\})}=\Delta_qZ^{(S)}$, and the proof of `(12)` applies verbatim to the
closed translation-invariant subspace $Z^{(S)}(H_\cap)\subset H_-$.  Induction proves that every
$Z^{(S)}$ is a strict closed embedding and that the composite
\[
 \iota_S:M_\zeta\hookrightarrow M_\zeta^{(S)},qquad
 [g]\longmapsto[\Delta_Sg]
\tag{17}
\]
is a strict closed embedding.  For $S\subset T$, these embeddings commute with the transition
map defined by \(\Delta_{T\setminus S}\).

Choosing an ordering $S=\{p_1,\dots,p_r\}$ gives a strict filtration of $M_\zeta^{(S)}$ whose
bottom term is the canonical copy `(17)` of $M_\zeta$ and whose successive quotients are
\[
 C^\infty(\mathbb R/\log p_j\,\mathbb Z),\qquad 1\le j\le r.
\tag{18}
\]
The filtration is source-canonical up to ordering; its partition-of-unity direct-sum splittings
are not.

## 5. Exact Green/Hodge consequence

`[PROVED HERE] [DAC_DENINGER_PRIME_TRACE_HODGE_NO_GO]`

Let $Q$ be any quadratic or sesquilinear form on $M_\zeta^{(p)}$ which factors through the
compact prime-circle trace:
\[
 Q(u,v)=q\bigl(
   \overline{\operatorname{Per}}_p u,
   \overline{\operatorname{Per}}_p v
 \bigr).
\tag{19}
\]
Then
\[
 Q(\iota_px,\iota_py)=0
 \qquad(x,y\in M_\zeta).
\tag{20}
\]
In particular, Dirichlet energy of the compact prime-circle trace, all of its Fourier-mode
energies, and any full norm of that trace have radical containing the entire Meyer middle sector.

This is immediate from `(13)`, but it changes the Route-L frontier.  More generally, applying all
successive compact-orbit traces in `(18)` still annihilates the bottom sector `(17)`. Thus no
finite collection of complete compact prime-orbit traces can polarize $M_\zeta$.

The prime orbit does admit
all of $M_\zeta$, strictly and without spectral specialization; it admits it as the **relative
zero-periodization sector**, not as visible compact Cauchy trace.  Therefore the missing Hodge form
must be a relative Green form on \(\ker\overline{\operatorname{Per}}_p\), annihilating
\(\Delta_pZ(H_\cap)\) before quotient and faithful afterward.  No construction that first applies
\(\overline{\operatorname{Per}}_p\) can supply it.

The naive use of the Green inverse `(7)` also does not finish the form: for a boundary
\(h=\Delta_pZf\), one has $G_ph=Zf$, generally nonzero.  Hence a bulk norm of $G_ph$ is not
boundary-blind.  Harmonic/relative projection against the Poisson boundary remains load-bearing.

## 6. Frontier movement

The theorem removes two former Route-L uncertainties.

1. **Admission/conservativity:** no cofinal all-prime syzygy theorem is needed merely to prove that
   prime source data retain the actual Meyer quotient.  Every finite prime tower supplies the
   canonical strict admission `(17)`, and `(14)` is already the exact one-prime boundary
   classification.
2. **Location of positivity:** compact prime-orbit Cauchy energy cannot be the middle Hodge form,
   even when every Fourier mode is retained.  Positivity must live on the relative
   zero-periodization kernel and use the Poisson-boundary harmonic projection.

Thus the first hard Route-L theorem is no longer another carrier, bar, Sullivan, or packet
completion.  It is construction of the source-relative Green form on the canonical sector `(13)`,
with radical exactly \(\iota_p(0)\), followed by compatibility across the real Fourier seam and
centered flow.  That is the Deninger-specific source producer needed before polar sign and Paugam
comparison.

## 7. Hostile audit

- **No RH-equivalent premise.** Only two-ended rapid decay, source Poisson summation over ordinary
  integers, and Meyer's already-proved strict embedding are used.
- **No divisor-fed carrier.** Both quotients in `(12)` are cokernels of explicit source operators.
- **Not scalar packet averaging.** The target of periodization is the complete smooth prime-circle
  packet.  The no-go `(20)` therefore rules out every trace-only packet form at once.
- **Not a proof of positivity.** The theorem constructs the admitted sector and proves where a
  faithful form cannot live.  It does not assert the still-missing relative Green form.
- **No hidden completion collapse.** All images are closed by the explicit Green inverse `(7)` and
  Meyer's strictness; every quotient in `(12)` is Hausdorff.
- **No Lean claim.** Lean corpus was inspected read-only during an active refactor.  No Lean file or
  build is part of this result.

## 8. Novelty audit

Repository search found Meyer's strict Poisson quotient, the Euler factorization, local
prime-circle Hodge packets, scalar/full-packet Bessel maps, and several packet-average no-go
theorems.  It found no Euler-depleted quotient `(10)`, no strict periodization extension `(12)`, no
identification `(13)` of the full Meyer quotient with the zero-periodization sector of one prime,
no finite Euler tower `(16)`--`(18)`, and no trace-Hodge obstruction `(20)`.

Targeted primary-source search found Meyer's nuclear Fr\'echet spectral quotient and Deninger's
prime-orbit/Frobenius framework, but no source stating the quotient and tower `(12)`--`(18)`.
The elementary translation
difference sequence underlying `(5)` is standard analysis; the new content is its arithmetic
composition with Meyer's strict Poisson embedding and the resulting exact location/no-go for the
Route-L Hodge form.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  arXiv:math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*, arXiv:1807.06400.
- `DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY`.
- `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_AMALGAMATION`.
- `DAC_GLOBAL_GREEN_ENERGY_RADICAL`.

## Gates

- [x] 0 → 1 in-progress: source formula and falsifiers fixed
- [x] 1 → 2 fully-proven: dependency-closed strict exact-sequence proof
- [ ] 2 → 3 formalized: intentionally paused during Lean corpus refactor
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-08 — Conjectured one-prime Euler-depleted conservativity; upgraded algebraic
  cancellation to the strict periodization sequence, proved the canonical closed admission of
  $M_\zeta$, and extracted the full prime-trace Hodge no-go.
