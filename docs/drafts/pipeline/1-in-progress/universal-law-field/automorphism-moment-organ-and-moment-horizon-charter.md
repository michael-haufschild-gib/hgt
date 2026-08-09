# Automorphism/moment organ and the moment horizon of the zeta gas

- **ID:** ULF-GAS-5
- **Stage:** 1-in-progress
- **Type:** ORGAN CHARTER + FROZEN CONJECTURE
- **Source:** PRD-E "fourth, non-classical organ" demand after ULF-GAS-4
- **Status:** [CHARTER] [HORIZON CALIBRATION PROVED] [COLLISION AUDIT MANDATORY]
  [OPEN CORE NAMED] [NOT RH] [NO LEAN]

## 1. The demand and the occupied boundary

The PRD-E gate's spirit asks for a fourth observer organ of the abelian zeta gas that is not one
of probability/KMS/meromorphic-divisor. The modern random-group organ is the **moment observer**:
test functionals \(A\mapsto\#\mathrm{Sur}(A,H)\) and \(A\mapsto\#\mathrm{Hom}(H,A)\) against
finite test groups \(H\), and the automorphism-weighted ensembles they determine.

Occupied territory (read before promoting anything from this charter):

- Fulman; Fulman–Kaplan, *Random partitions and Cohen–Lenstra heuristics* (arXiv:1803.03722) —
  Hall–Littlewood measure families on partitions containing the per-prime tilted ensembles.
- Fulman, *Hall–Littlewood polynomials and Cohen–Lenstra heuristics for Jacobians of random
  graphs* (arXiv:1403.0473); *CL heuristics and random matrix theory over finite fields*
  (arXiv:1307.0879).
- Sawin–Wood moment problem and universality (arXiv:2210.04278 and the diamond-category moment
  theorem); *Symmetric functions and the explicit moment problem* (arXiv:2402.16625); Van Peski's
  p-adic random matrix theory (thesis, 2023).

Any per-prime statement about \(|{\rm Aut}|\)-tilts or Hall–Littlewood specializations of the
zeta measure is presumptively theirs. The residual claim-space is the **global, zeta-normalized,
heavy-tailed regime** below.

## 2. Horizon calibration (proved; dependency-closed)

Under \(\mathbb P_\sigma\) (\(\sigma>1\)), with \(q=p^{-\sigma}\) and \(r_p=\mathrm{rank}_p(A)=N_p\):

\[
\mathbb E_\sigma\bigl[x^{\,r_p}\bigr]
=\frac{(q;q)_\infty}{(xq;q)_\infty}
\quad\text{for }|x|<p^{\sigma},
\qquad
\mathbb E_\sigma\bigl[x^{\,r_p}\bigr]=\infty
\quad\text{for }x\ge p^{\sigma},
\tag{GAS5.1}
\]

by the Euler PGF of ULF-GAS-1 Theorem 3.1 (the series \(\sum_nw_{q,n}x^n\) has radius exactly
\(q^{-1}=p^\sigma\), since \(w_{q,n}\sim(q;q)_\infty q^n/(q;q)_\infty\cdot\)const). Consequently,
for the elementary test groups \(H=(\mathbb Z/p)^r\):

\[
\boxed{\ \mathbb E_\sigma\bigl[\#\mathrm{Sur}\bigl(A,(\mathbb Z/p)^r\bigr)\bigr]<\infty
\iff r<\sigma.\ }
\tag{GAS5.2}
\]

Proof: \(\#\mathrm{Sur}((\mathbb Z/p)^{n},(\mathbb Z/p)^r)=\prod_{i=0}^{r-1}(p^{n}-p^{i})\asymp
p^{nr}\) for \(n\ge r\), and \(\#\mathrm{Sur}(A,(\mathbb Z/p)^r)\) depends only on \(r_p=n\);
compare with (GAS5.1) at \(x=p^{r}\). QED.

**The zeta gas has a sharp moment horizon at \(\sigma\):** all Sur-moments of test rank
\(r<\sigma\) are finite and explicit; all of test rank \(r\ge\sigma\) are infinite. In
particular for \(\sigma\in(1,2]\) only rank-one moments exist. The ensemble is therefore outside
the moment-determined (Cohen–Lenstra/Sawin–Wood) universality regime, whose measures have all
moments finite and small. Heavy tails are not a defect: they are forced by the zeta weighting
\(|A|^{-\sigma}\) and are the group-theoretic face of the divisor calculus's pole ladder.

## 3. Frozen hunch

> The zeta-Gibbs measures \(\{\mathbb P_\sigma\}\) form a natural **moment-indeterminate** family:
> for \(\sigma\) in a nonempty range there exist random finite abelian groups, not equal in law to
> \(\mathbb P_\sigma\), with the same finite (sub-horizon) Sur-moment data. Equivalently, the
> Sawin–Wood determinacy mechanism fails exactly past the moment horizon, and the horizon is the
> group-theoretic shadow of the abscissa.

`[OPEN CORE]` Construct a second measure matching all sub-horizon moments, or prove sub-horizon
determinacy for some \(\sigma\). First unprovable point: whether the finitely many finite moment
values, which no longer form the full CL-type moment family, still pin the law within a
reasonable class (the classical one-dimensional analogue — Stieltjes indeterminacy for
heavy-tailed moment problems — suggests indeterminacy, but the group-valued setting has extra
rigidity through the multiplicative mode structure).

## 4. Falsifiers and exits

1. Sub-horizon determinacy holds for all \(\sigma>1\) — hunch dies; survivor: a determinacy
   theorem strictly extending the Sawin–Wood growth condition; check against their hypotheses
   first (their theorem may already cover or exclude this regime — that check is step one of the
   next cycle, BEFORE any construction).
2. Indeterminacy holds trivially by known one-dimensional examples lifted to rank-one data —
   hunch survives but significance collapses to an exercise; verdict INSIGNIFICANT; record and
   close.
3. The horizon (GAS5.2) is already in the literature (heavy-tailed random groups) — calibration
   loses novelty; the charter then reduces to a citation node.

## 5. Anti-theatre gate for this charter

Reject unless the outcome couples the moment organ to at least one existing gas organ with an
exact law (e.g., horizon = abscissa is (GAS5.2); demanded next: a statement linking moment
(in)determinacy to the condensation fan or to the divisor calculus, not a free-standing
probability curiosity).

## Log

- 2026-08-09 — charter opened; horizon calibration proved; collision boundary recorded;
  hunch frozen with the mandatory read-first list of §1.

## 6. RESOLUTION — 2026-08-09 (same session): hunch true but insignificant as stated; closed

### 6.1 Rank-horizon strengthening (proved; supersedes the elementary-target calibration)

For every finite abelian p-group H and sigma > 1:

    E_sigma[#Sur(A, H)] < infinity  <=>  rank(H) < sigma.

Proof. #Hom(A,H) = prod_i p^{ s_i * G_i } with s_i = sum_j min(i, mu_j) over H's partition mu;
mode-wise finiteness needs s_i < i*sigma for all i. At i = 1, s_1 = rank(H), giving the
necessity threshold at rank(H) (the depth-1 modes carry it, via the PGF radius p^sigma). For
finiteness when rank(H) < sigma: s_i <= i*rank(H) < i*sigma for all i, and #Sur <= #Hom. For
infinity when r := rank(H) >= sigma: on the event {A contains H + (Z/p)^n} (probability
>= c_H * w_{q_p,n} >= c * p^{-sigma n}: realize H on the deeper modes, n particles in mode
(p,1)), the maps (id_H + psi) with psi in Hom((Z/p)^n, H) are pairwise distinct surjections, so
#Sur(A,H) >= p^{n r}; hence E[#Sur] >= c * sum_n p^{-sigma n} p^{r n} = infinity since
p^r >= p^sigma. QED. The horizon is exactly the RANK of the test group, at every depth.

### 6.2 Sub-horizon indeterminacy (proved; but by collapse, hence insignificant)

For sigma in (1,2) the finite test family is {H : rank H = 1} = cyclic targets. On laws
supported on depths <= 2 (configurations (G_1, G_2)), the entire cyclic test family collapses to
TWO functionals: E[p^{G_1+G_2}] (from H = Z/p) and E[p^{G_1+2G_2}] (from H = Z/p^j, any j >= 2 —
all coincide since min(i,j) saturates at depth 2). Two linear constraints on the
infinite-dimensional simplex of laws on N^2 leave explicit distinct positive laws matching the
zeta gas's values (three-point signed perturbation with small epsilon). Hence the zeta measure
at sigma in (1,2) is NOT determined by its finite Sur-moments.

### 6.3 Verdict

Per this card's own falsifier 2: the frozen hunch is TRUE but by an elementary collapse —
verdict INSIGNIFICANT as a standalone discovery. Survivors kept: the rank-horizon theorem
(§6.1, exact and clean) and the saturation-collapse mechanism (§6.2, the reason bare Sur-counts
lose depth information above the horizon). The moment-organ direction is CLOSED unless a
determinacy-restoring richer test family (Hall-algebra / Hecke-operator tests instead of bare
Sur-counts) is proposed through a fresh hunch-formation pass with the Fulman/Sawin-Wood
collision audit actually executed. Do not reopen with bare moments.
