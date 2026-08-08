# Polarized incidence--Stokes and Route-E/Mass capacity-phase law

- **ID:** `polarized-incidence-stokes-and-e-mass-capacity-phase-law`
- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [CROSS-ROUTE BRIDGE]`
  `[PATH-LOCAL MASS CAPACITY IDENTIFICATION FALSIFIED] [CORPUS PRIORITY UNVERIFIED]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT RH] [NO LEAN WRITTEN]`
- **Scope:** Finite labeled bipartite incidence, the finite symmetric opposite-sign Route-E
  conductance sector, and finite ordered-prime paths. No limiting source estimate, prime-gap
  hypothesis, PNT, or RH premise.
- **Formal parents:**
  `../../3-formalized/mass-xi-full-adjacent-prime-graph-flux.md`,
  `../../3-formalized/mass-xi-balanced-adjacent-prime-difference-summability.md`, and the existing
  `MobiusBoundaryOppositeSignTransport.lean` results cited by
  `../route-e-forward-interval-hall-reduction.md`.

## 1. Result

Route E and the Mass-shift route have one exact common algebraic shadow: after Möbius
polarization, Route E's signless endpoint-incidence is ordinary oriented boundary, and both its
unused-capacity survivor and the Mass route's terminal Abel term are degree-zero boundary
remainders. This common shadow does **not** identify their capacity geometries. On the ordered-prime
path, the primitive of the constant mass class is asymptotically unbounded relative to the natural
local edge capacity, and its log-gap work diverges.

The source-specific conclusion is therefore a phase separation:

```text
same polarized H_0 boundary type
          does not imply
same capacity-filtered boundary phase.
```

## 2. Polarized signless incidence

Let `G=(V,E)` be a finite bipartite multigraph. Fix a sign

\[
 \epsilon:V\longrightarrow\{+1,-1\}
\]

such that every edge joins opposite signs. Orient every edge from its positive endpoint `s(e)` to
its negative endpoint `t(e)`. Let `C_1=\mathbb C^E` and `C_0=\mathbb C^V`, with the given labels
retained as basis labels. Define

\[
 B^+e=v_{s(e)}+v_{t(e)},\qquad
 \partial e=v_{s(e)}-v_{t(e)},\qquad
 S_\epsilon v=\epsilon(v)v.
 \tag{1}
\]

### Theorem A — Möbius polarization is a chain identification

\[
 \boxed{S_\epsilon B^+=\partial.}
 \tag{2}
\]

It preserves edge and vertex labels, support, marked coordinate ports, every absolute `ell^p`
norm, every edge capacity, and every absolute edge-work functional

\[
 W_c(q)=\sum_{e\in E}c(e)|q(e)|.
 \tag{3}
\]

Here `c:E->R_{>=0}` is any fixed edge-cost function.

It sends the positive vertex cone to the polarized cone
`S_epsilon(R_{>=0}^V)`; it does not identify that cone with the original positive cone.

### Proof

For a basis edge from a positive vertex to a negative vertex,

\[
 S_\epsilon B^+e
 =S_\epsilon(v_{s(e)}+v_{t(e)})
 =v_{s(e)}-v_{t(e)}
 =\partial e.
\]

Linearity gives `(2)`. The map is diagonal with entries of modulus one, so it preserves absolute
coordinate norms and does not alter edge coordinates, labels, support, capacities, or `(3)`.
For every marked vertex set `A`, the exact port identity is

\[
 \pi_A S_\epsilon=S_{\epsilon|A}\pi_A.
\]

The final cone statement is its definition. `[PROVED HERE]`

## 3. Exact capacity--flux balance

Let `w in C_0` be endpoint capacity, let `q in C_1` be a source-predeclared edge current, and put

\[
 r=w-B^+q.
 \tag{4}
\]

The vector `r` is always an algebraic residual. It is unused or unmatched endpoint capacity only
under the additional capacity hypotheses

\[
 w\ge0,\qquad q\ge0,\qquad B^+q\le w.
 \tag{4a}
\]

### Theorem B — polarized discrete Stokes law

\[
 \boxed{S_\epsilon w=\partial q+S_\epsilon r.}
 \tag{5}
\]

Hence

\[
 [S_\epsilon w]=[S_\epsilon r]\quad\text{in }H_0(G),
 \qquad
 \sum_{v\in V}\epsilon(v)w(v)
 =\sum_{v\in V}\epsilon(v)r(v).
 \tag{6}
\]

For every marked cut or port cochain `chi in C^0`,

\[
 \boxed{
 \langle S_\epsilon w,\chi\rangle
 =\sum_{e\in E}q(e)
   \bigl(\chi(s(e))-\chi(t(e))\bigr)
  +\langle S_\epsilon r,\chi\rangle .}
 \tag{7}
\]

### Proof

Apply `S_epsilon` to `(4)` and use `(2)`, obtaining `(5)`. Passing to the cokernel of `partial`
gives the first part of `(6)`. Pairing with the constant cochain gives the second part because
augmentation kills every oriented boundary. Pairing `(5)` with arbitrary `chi` and using
`<partial q,chi>=<q,d chi>` gives `(7)`. `[PROVED HERE]`

### Connected quotient

If `G` is connected, ordinary graph homology gives

\[
 C_0/\operatorname{im}\partial\cong\mathbb C
\]

by augmentation. Conjugating with `S_epsilon` gives

\[
 C_0/\operatorname{im}B^+\cong\mathbb C,
 \qquad
 [w]\longmapsto\sum_v\epsilon(v)w(v).
 \tag{8}
\]

Thus the Route-E Möbius-sign observer is literally the constant degree-zero cohomology class after
polarization.

## 4. Finite symmetric Route-E conductance realization

For the finite symmetric opposite-sign Route-E conductance sector take:

1. vertices to be all source and target endpoints in the finite extended physical set;
2. `epsilon(v)=mu(v)`;
3. one unordered edge `{i,j}` for each source-declared parity-flipping support pair with symmetric
   conductance `c(i,j)=c(j,i)`;
4. `w(v)` to be finite Gibbs capacity;
5. `q_{\{i,j\}}=c(i,j)>=0`, with row-capacity condition `B^+q<=w`;
6. `r=w-B^+q` to be unused capacity;
7. `chi` to be a marked physical cut, including the zero/one-large-prime port.

If allocation provenance is retained as multiedges, a pre-existing nonnegative decomposition into
parallel currents whose sum is `c(i,j)` is required; the theorem does not invent one. Every
admitted edge joins opposite Möbius signs, so Theorems A--B apply without changing the symmetric
source relation. Equation `(7)` becomes a **signed polarized cut flux**:

```text
polarized source charge = signed cut flux + unmatched residual.
```

Under `(4a)`, the elementary estimate strengthens to

\[
 \left|\sum_v\mu(v)w(v)\right|
 =\left|\sum_v\mu(v)r(v)\right|
 \le \sum_v r(v)=\|r\|_1
 \tag{9}
\]

This is the oriented-homology form of the corpus unused-capacity bound. Hall-cut inequalities control
which `q` are admitted; `(5)` records exactly what remains after any such current is chosen.

This signed flux is not automatically the directed normalized physical `1->0` seam. Möbius
orientation may oppose that physical direction. Recovering the directed harmonic-row seam charge
requires a separate source-to-target orientation or a two-orientation incidence object; it is not
proved here.

## 5. Mass-shift realization

Let `p_0<p_1<...` be the primes and set

\[
 \lambda_n=\log p_n,qquad
 t_n={\log p_n\over\sqrt{p_n}},qquad
 T_m=\sum_{k<m}t_k.
 \tag{10}
\]

For `N>=1`, on the finite path with oriented edges `e_n:v_n->v_{n+1}`, define

\[
 z_N=\sum_{n<N}t_nv_n,qquad
 q_N=\sum_{n<N-1}T_{n+1}e_n,qquad
 b_N=T_Nv_{N-1}.
 \tag{11}
\]

Here `t_n` is the actual positive real value of the prime von-Mangoldt coefficient at `s=1/2`,
viewed inside `C` in the formal Mass route.

### Theorem C — exact finite Abel boundary decomposition

\[
 \boxed{z_N=\partial q_N+b_N.}
 \tag{12}
\]

For any vertex profile `F_n`, pairing gives

\[
 \boxed{
 \sum_{n<N}t_nF_n
 =T_NF_{N-1}
 +\sum_{n<N-1}T_{n+1}(F_n-F_{n+1}).}
 \tag{13}
\]

For the actual Mass-shift Fourier profile this is exactly the formalized C39 finite Abel identity.

### Proof

Since `partial e_n=v_n-v_{n+1}`, the coefficient of `v_0` in `partial q_N` is `T_1=t_0`.
For `0<n<N-1`, it is

\[
 T_{n+1}-T_n=t_n.
\]

The coefficient of `v_{N-1}` is `-T_{N-1}`. Adding `b_N` changes this to
`T_N-T_{N-1}=t_{N-1}`, proving `(12)`. Pairing with `F` proves `(13)`. `[PROVED HERE]`

The vector `b_N` is the terminal remainder in C39's finite Abel decomposition. It is not by itself
the Mass outgoing Chebyshev current or the full constant-mask evaluation: the bulk term
`sum T_{n+1}(F_n-F_{n+1})` is generally nonzero and is not known bounded. For example, with `N=2`,
`F_0=1`, and `F_1=0`, the terminal pairing vanishes while the bulk is `t_0`.

The exact common statement is narrower: Route-E residual and Mass terminal Abel remainder occupy
the same chain degree. The full Mass outgoing class is represented by the entire left side of
`(13)`, modulo separately proved bounded coboundaries.

## 6. Capacity-phase separation

The natural local Mass edge capacity is

\[
 \kappa_n=t_{n+1}.
 \tag{14}
\]

The C39 Lipschitz/telescoping theorem proves finite total local log-gap work,

\[
 \sum_{n\ge0}t_{n+1}(\lambda_{n+1}-\lambda_n)
 \le 16e^{-\lambda_0/4}.
 \tag{15}
\]

The primitive in `(11)` instead has coefficient `T_{n+1}`.

### Theorem D — no bounded local capacity identification

\[
 \boxed{{T_{n+1}\over t_{n+1}}\longrightarrow+\infty}
 \tag{16}
\]

and

\[
 \boxed{
 \sum_{n<N-1}T_{n+1}(\lambda_{n+1}-\lambda_n)
 \longrightarrow+\infty.}
 \tag{17}
\]

Equivalently, the C39 prefix primitive lies in no fixed local-capacity ball

\[
 K_M(M)=\{q:|q_n|\le M\kappa_n\text{ for every }n\}.
 \tag{17a}
\]

Consequently no edgewise path identification with uniformly bounded inverse and uniformly
comparable capacity weights can regularize this primitive. Comparison with a nonlocal Route-E
graph remains open.

### Proof

The sequence `t_n=(log p_n)/sqrt(p_n)` tends to zero, while
`T_{n+1}>=t_0>0`. This proves `(16)`. Also

\[
 \sum_{n<N-1}T_{n+1}(\lambda_{n+1}-\lambda_n)
 \ge t_0\sum_{n<N-1}(\lambda_{n+1}-\lambda_n)
 =t_0(\lambda_{N-1}-\lambda_0),
\]

which diverges because the primes are unbounded. Membership in `K_M(M)` would require
`T_{n+1}/t_{n+1}<=M` for every `n`, contradicting `(16)`. A uniformly invertible edgewise
identification with comparable weights would preserve bounded congestion in both directions, so it
cannot regularize this primitive. `[PROVED HERE]`

## 7. Strongest positive survivor

For an oriented finite graph, a capacity cone `K subset C_1`, work `W`, and marked boundary-port
set `P subset V`, define the relative capacity-filtered filling profile of `z in C_0` by

\[
 \mathfrak F_{z,P}(\alpha)
 =\inf_{q\in K}\left\{W(q):
 \inf_{b\in C_0(P)}\|z-\partial q-b\|_1\le\alpha\right\},
 \tag{18}
\]

with `inf emptyset=+infinity`. For Mass take `P={v_{N-1}}`; for Route E take the chosen boundary or
seam ports, or `P=emptyset` for total unmatched capacity. Theorem D says no fixed `M` admits the
Mass prefix primitive cofinally in `K_M(M)`.

Ordinary `H_0` forgets capacity and work data, so it cannot determine capacity phase from the
boundary class alone; it can still distinguish numerical augmentation values. The profile `(18)`
also remembers which primitives are admitted and their cost. Theorems A--D prove:

1. incidence, capacity, and boundary propagation coexist in one exact finite object;
2. polarization transports Route-E signless incidence to the same boundary type as Mass;
3. ordinary `H_0` cannot determine the capacity phase from a boundary class;
4. the Mass prefix primitive has singular path-local capacity behavior at cofinal scale.

This is a candidate finite NGD interface; corpus-wide and external priority remain unaudited. It
remains a classical bridge unless a future theory derives `(18)` from one source-generated
joint-realizability law.

## 8. No-go closure and significance boundary

1. **Direct carrier equivalence.** `NOT DEFINED / NOT CLAIMED`.
2. **Common finite polarized incidence schema.** `PROVED` by A--C.
3. **Ordinary homology determines capacity.** `FALSE` by D.
4. **Uniformly bounded path-local Mass filling.** `FALSE` by D.
5. **Directed Route-E/Mass capacity equivalence.** `OPEN`.
6. **RH consequence.** `NONE`: the open object is the full observed Mass outgoing current,
   including the `T dF` bulk, not the explicit prefix primitive.

Generic parents are signed-graph switching, discrete Stokes/Abel summation, flow/cut duality, and
capacitated filling profiles. No novelty is claimed for those ingredients. Corpus-wide and
external priority for this precise interface remain unverified.

## Lean-return note

- No Lean code was written or built.
- Likely later reuse:
  `formal/GaloisForLFunctions/RHTower/MobiusBoundaryOppositeSignTransport.lean`,
  `formal/GaloisForLFunctions/RHTower/XiMassFullAdjacentPrimeGraph.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiMassCriticalOutgoingCurrent.lean`.
- Formalization should separate generic graph theorem from the two arithmetic instantiations.

## Gates

- [x] dependency-closed generic paper proof
- [x] label and marked-port preservation
- [x] Route-E finite realization typed
- [x] Mass finite Abel realization typed
- [x] path-local Mass capacity no-go proved
- [x] strongest positive survivor extracted
- [x] independent hostile audit repaired
- [ ] external priority verification

## Log

- 2026-08-08 — common polarized boundary law proved; local capacity equivalence falsified by exact
  prime-path primitive blow-up and divergent log-gap work.
