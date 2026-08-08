# Euler prime-orbit prolongation, recurrence, polar loss, and cofinal wall

- **ID:** `clg-euler-prime-orbit-four-organ-law`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / HIGHER-LEVEL SOURCE-ORBIT CALIBRATION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [ARITHMETIC/SPECTRAL/POSITIVE/TOPOLOGICAL]`
  `[RECURRENCE/PROLONGATION] [NOT HT BY ITSELF] [NOT RH] [NO LEAN WRITTEN OR BUILT]`
- **Parents:** `critical-euler-mass-weil-stokes-shadow-law.md`;
  `../constraint-relativity/finite-prime-gibbs-modular-phase-realization.md`;
  `../../3-formalized/not_new_scientific_knowledge/prime-coherent-scale-factor-clock-duality.md`.
- **Statement:** One source-derived prime-log orbit has finite-cutoff full prolongation rank, compact
  recurrent spectral projection, maximally phase-blind positive energy, and a singular cofinal
  half-density limit.

## Goal

Produce a theorem above individual RH routes. The object must be fixed before Xi-zero
specialization and must generate arithmetic, spectral, positive, recurrence, prolongation, and
cofinal-topological shadows from one compatible finite-cutoff family rather than by product
packaging.

## 0. Unitary-invariant finite spectral normal form

Let `H` be an `N`-dimensional complex Hilbert space, let `D` be self-adjoint with distinct real
eigenvalues `lambda_1,...,lambda_N`, and let `v` have nonzero projection to every eigenspace.

### Theorem 0.1 — cyclic history, polar loss, and recurrent projection

1. `v,Dv,...,D^(N-1)v` is a basis of `H`.
2. If the eigenvalues have no nonzero integral relation, the orbit `e^(-itD)v` is dense in the
   torus obtained by independently rotating the nonzero spectral components of `v`.
3. The positive observer `x mapsto ||x||^2` is constant on that torus.
4. The logarithmic phase lift `t mapsto (-t lambda_j)_j in R^N` is unbounded when `D!=0`.

### Proof

Choose the orthonormal eigenbasis. The coordinate matrix of the first list is the Vandermonde
matrix `(lambda_j^k)` multiplied by the nonzero spectral coordinates of `v`, so it is invertible.
The second assertion is Kronecker--Weyl applied to the frequency vector `(lambda_j)`. Unitarity
proves the third. The Euclidean norm of the lift is
`|t| sqrt(sum_j lambda_j^2)`, proving the fourth. QED.

Theorem 0.1 is the unitary-invariant spectral normal form behind the later prime chart. The
displayed logarithmic lift uses an eigenvalue ordering, while its Euclidean norm is spectral. It says one
spectral generator can be simultaneously cyclic for prolongation, recurrent after phase quotient,
invisible to a scalar positive observer, and open in the universal phase cover. None of these
properties alone determines the others without the shared pair `(D,v)`.

### Corollary 0.2 — finite compactness / cofinal noncompactness split

Let the directed set be the finite subsets `F` of a countable index set, put `H_F=C^F`, and use
coordinate restriction maps `H_G->H_F` for `F subset G`. Let `D_F` and `v_F` be restrictions of a
single real diagonal sequence and amplitude sequence, with integral independence at every finite
stage. If `|F|` is unbounded and the compatible amplitude sequence is not in `ell^2`, then every
finite phase observer is compact recurrent, the exact span inequality below holds at every fixed
order, and the compatible algebraic source sequence defines no vector in the standard `ell^2`
completion. No general pro-object theorem is asserted.

### Proof

Apply Theorem 0.1 at each stage. For fixed `r`, whenever `|F|>r+1`,
`span{v_F,D_Fv_F,...,D_F^rv_F}` has dimension at most `r+1` and is not `H_F`. Membership of the
compatible vector in the Hilbert completion is exactly square summability of its spectral
coordinates, which fails by hypothesis. QED.

## 1. Source orbit

Let `P` be the ordinary primes. The Euler--Möbius logarithmic current has primitive-prime
coefficient

\[
 \Theta(p)=\Lambda(p)=\log p.
\tag{1}
\]

At half density define

\[
 v(p)=\frac{\log p}{\sqrt p}.
\tag{2}
\]

For a finite nonempty prime set `F`, put `H_F=C^F`, let

\[
 (D_Fx)(p)=(\log p)x(p),
 \qquad U_F(t)=e^{-itD_F},
\tag{3}
\]

and write

\[
 v_F(t)=U_F(t)v_F,
 \qquad v_F(t;p)=\frac{\log p}{\sqrt p}e^{-it\log p}.
\tag{4}
\]

This is the same primitive-prime coefficient as the Mass boundary source; `-D_Fv_F` is the
positive-frequency coefficient of the reflection-odd Weil torque; and `U_F` is the finite prime
Mellin/Fourier clock.

## 2. Full finite prolongation rank

### Theorem 2.1

If `|F|=N`, then

\[
 v_F,D_Fv_F,\ldots,D_F^{N-1}v_F
\tag{5}
\]

is a basis of `H_F`.

### Proof

In the prime-coordinate basis the matrix of `(5)` is

\[
 M_{p,k}=\frac{(\log p)^{k+1}}{\sqrt p},
 \qquad p\in F,\quad 0\le k<N.
\tag{6}
\]

Factor the nonzero row scalar `(log p)/sqrt(p)`. The remaining matrix is the Vandermonde matrix
`((log p)^k)`. Its nodes are distinct because the primes are distinct, so its determinant is
nonzero. Hence `(5)` is a basis. QED.

### Consequence 2.2

For every fixed `r`,

\[
 |F|>r+1\quad\Longrightarrow\quad
 \operatorname{span}\{v_F,D_Fv_F,\ldots,D_F^rv_F\}\ne H_F.
\tag{6a}
\]

Thus no fixed linear prolongation order spans all finite prime cutoffs. This is an exact
unbounded linear-prolongation law.

It is not, by itself, differential
hypertranscendence of a named analytic function; that requires a realization theorem controlling
all polynomial jet relations.

## 3. Compact recurrent observer and open logarithmic lift

### Theorem 3.1

For every finite `F`, the orbit `(4)` is dense in the radius torus

\[
 \mathbb T_F(v)=
 \prod_{p\in F}\left\{z\in\mathbb C:|z|=\frac{\log p}{\sqrt p}\right\}.
\tag{7}
\]

In particular it returns arbitrarily close to its initial point at arbitrarily large positive
times. Its logarithmic lift

\[
 \widetilde\gamma_F(t)=(-t\log p)_{p\in F}\in\mathbb R^F
\tag{8}
\]

is unbounded whenever `F` is nonempty.

### Proof

If integers `m_p` satisfy `sum_(p in F)m_p log p=0`, exponentiation gives
`prod_(p in F)p^(m_p)=1`. Unique factorization forces every `m_p=0`. Thus the frequency vector
`(log p)` has no nonzero integral annihilator. Kronecker--Weyl density gives `(7)` and recurrence.
Equation `(8)` has Euclidean norm
`t(sqrt(sum_(p in F)(log p)^2))`, so it is unbounded. QED.

This is the exact finite model of closed/recurrent observation with open lifted history. The
observer closes only approximately for `|F|>=2`; no exact common period is asserted.

## 4. Positive polar observer is maximally phase-blind

### Theorem 4.1

The Hilbert energy

\[
 E_F(t)=\|v_F(t)\|^2
 =\sum_{p\in F}\frac{(\log p)^2}{p}
\tag{9}
\]

is independent of `t` and is constant on the entire torus `(7)`. Therefore this positive scalar
does not determine orbit time, phase, winding, recurrence quality, or logarithmic lift.

### Proof

Every coordinate multiplier in `(4)` has modulus one. Summing squared coordinate norms gives
`(9)`. The same argument applies to every point of `(7)`. QED.

The full autocorrelation function

\[
 C_F(t)=\langle v_F,U_F(t)v_F\rangle
 =\sum_{p\in F}\frac{(\log p)^2}{p}e^{-it\log p}
\tag{10}
\]

retains the discrete prime-frequency measure, while its value at `t=0` is only `(9)`. Positivity is
therefore a polar observer, not a complete phase geometry.

## 5. Cofinal half-density wall

### Theorem 5.1

For real `sigma`, define

\[
 v_\sigma(p)=(\log p)p^{-\sigma},
\tag{11}
\]

one has

\[
 v_\sigma\in\ell^2(\mathcal P)
 \quad\Longleftrightarrow\quad \sigma>\frac12.
\tag{12}
\]

In particular the compatible algebraic finite-cutoff family has no global orbit vector in the
standard prime Hilbert space at half density, even though every finite observer orbit is compact
and recurrent. This distinguishes a compatible finite family from a single global Hilbert orbit.

### Proof

The squared norm is `sum_p (log p)^2p^(-2sigma)`. For `sigma<=1/2`, its terms dominate
`(log 2)^2/p`, and Euler's divergence of `sum_p 1/p` applies. For `sigma>1/2`, choose
`epsilon>0` with `2sigma-2epsilon>1` and use `log p<=p^epsilon/epsilon`; comparison with the
convergent integer `p`-series proves summability. QED.

For `0<sigma<1`, both reflected vectors `v_sigma` and `v_(1-sigma)` fail to lie in `ell^2`
exactly when `sigma=1/2`. This is a source metric wall, not a proof that Xi zeros lie there.

## 6. One compatible source family, six computed shadows

The compatible marked finite-cutoff family `(Theta,D_F,U_F(t),v_F)` yields:

1. **arithmetic:** `Theta(p)=log p`;
2. **spectral/Fourier:** the prime-log generator `D` and autocorrelation `(10)`;
3. **positive:** the polar energy `(9)`;
4. **recurrence:** compact Kronecker phase projection `(7)`;
5. **history:** unbounded logarithmic lift `(8)`;
6. **unbounded linear-prolongation geometry:** rank `(5)` plus the cofinal Hilbert wall
   `(12)`.

These are not mutually derivable scalar invariants. They are different computed shadows of one
compatible source family. Actual comparison functors have not been constructed. The theorem
therefore supports the higher field primitive:

> a law chart is a source history orbit together with its prolongation module, phase observer,
> polarization, lift, and completion; geometry begins with comparison among these shadows, not
> with any one route endpoint.

## 7. Hostile boundaries

1. Compact recurrence does not imply bounded lifted history: `(7)` and `(8)` coexist.
2. Positive energy does not encode phase: `(9)` is constant on `(7)`.
3. Unbounded prolongation rank does not prove analytic HT without a polynomial-relation
   realization theorem.
4. Finite compactness does not produce a cofinal Hilbert vector: `(12)` fails at half density.
5. The theorem contains no Xi divisor, no zero-line premise, no source-nullhomology, and no RH
   selection.
6. The theorem does not derive Route-E capacity, Gamma normalization, or a physical wormhole
   length. These require additional constitutive fields.

## 8. Route-independent predictions

1. Any positive scalar depending only on coordinate moduli is blind to prime-log recurrence phase
   and cannot bound the logarithmic lift without an independent action.
2. Any fixed-order **linear prolongation** observer fails to span sufficiently large prime
   cutoffs, by `(6a)`.
3. The unrenormalized critical half-density coefficient is absent from standard
   `ell^2(P)`. Renormalization, a changed topology, or an external-time interpretation are possible
   responses, not an exhaustive classification.
4. Any Brown--Susskind-type interpretation of this chart would need an independently sourced
   proper history/complexity operator; the
   phase torus and its energy alone contain no such length.
5. A field theory claiming HT, recurrence, positivity, and completion are one scalar phenomenon is
   falsified by the independent formulas `(5)`, `(7)`, `(9)`, and `(12)`.

## Literature and corpus boundary

Kronecker--Weyl density, Vandermonde rank, polar energy, and prime-harmonic divergence are classical.
The corpus already proves several components separately. This card intentionally makes no novelty
claim; its role is a dependency-closed constitutive synthesis around one source-derived orbit.
Current infinite-prime-torus context: Baroni, *The infinite prime torus and arithmetic Kronecker
flows*, <https://arxiv.org/abs/2604.02213>.

## Gates

- [x] source fixed before target/divisor specialization
- [x] finite prolongation-rank theorem
- [x] compact recurrence/open-lift theorem
- [x] polar phase-erasure theorem
- [x] cofinal half-density wall
- [x] six shadows arise from one orbit
- [x] hostile non-implication audit
- [ ] identify a common source-normalized action beyond finite Euclidean lift
- [ ] construct observer functors from this chart to a non-prime HT family and physical horizon
- [ ] formalize only after field-level target stabilizes

## Lean-return note

No Lean code was written or built. Existing formal parents include prime-log frequency
independence, finite-prime Kronecker density, and the half-density summability wall; reuse them
rather than duplicating proofs.

## Log

- 2026-08-09 — higher-level pivot from source-selector search to one-orbit six-shadow geometry.
