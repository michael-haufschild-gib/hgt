# Nested inverse-power static-local ramp--return law

- **ID:** inverse-power-nested-static-local-ramp-return
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Source:** `inverse-square-static-local-exact-return-reflection-law.md`

## Exact claim

For `L : ℕ`, on `2L` qubits grouped into pairs, let

\[
 H_L^{\mathrm{nest}}
 =\sum_{j=1}^{L}j^{-2}P_{2j-1,2j}
 +\sum_{j=1}^{L-1}(j+1)^{-4}P_{2j,2j+1},
 \qquad U_L(t)=e^{-itH_L^{\mathrm{nest}}}.
\]

Every coefficient belongs to one fixed infinite sequence: increasing `L` never changes an old
interaction.  Put

\[
 Q_L=(L!)^4,\qquad R_L=2\pi Q_L.
\]

Let `C^{op}_{L,ε}(t)` be the infimum in `ℕ∞` of counted arbitrary two-qubit gates among
support-certified one/two-qubit circuits within global `L2` operator norm `ε` of `U_L(t)`;
one-qubit gates are free.  Prove:

1. **Bounded thermodynamic completion.**  The infinite diagonal energy
   \[
   E_\infty(x)=\sum_{j\ge1}j^{-2}p_j(x)
   +\sum_{j\ge1}(j+1)^{-4}b_j(x)
   \]
   exists for every infinite configuration, is bounded by `3`, and its `L`-pair truncations are
   exactly the finite energies of `H_L^{nest}`.  For `L≥1`, convergence is uniform with tail at
   most `L^{-1}+L^{-3}`.
2. **Exact return.**  For every `L`, `U_L(R_L)=I`.
3. **Exact reflection.**  For every real `t,ε`,
   \[
   C^{op}_{L,ε}(R_L-t)=C^{op}_{L,ε}(t).
   \]
4. **Laboratory ramp.**  If
   \[
   0<ε\le1/100,\qquad 1024\pi ε\le t\le εL/2,
   \]
   then
   \[
   \left\lfloor\frac{t}{128\pi ε}\right\rfloor
   \le C^{op}_{L,ε}(t)
   \le 2\left\lceil\frac{2t}{ε}\right\rceil,
   \]
   and identical bounds hold at `R_L-t`.

The upper constant is deliberately unoptimized.  No literal monotonicity, plateau, minimal return,
translation invariance, or infinite-volume orbit recurrence is claimed.

## Internal frontier

- `[CORPUS]` `inverseSquareChain_floor_ceil_growth` proves a robust linear envelope for a connected
  finite path whose bridge coefficient is the volume-dependent `L^{-3}`.
- `[CORPUS]` `inverseSquareChain_growth_exactReturn_reflection` adds exact factorial-cube return and
  exact operator-complexity reflection for that same family.
- `[OPEN CORE]` Replace the disappearing volume-dependent bridges by a fixed summable bond sequence
  while preserving both lower and upper circuit bounds and proving a genuine bounded thermodynamic
  completion.
- No matching failed-route card was found.

## External frontier

- `[LITERATURE]` Haah--Hastings--Kothari--Low, arXiv:1801.03922, prove near-optimal simulation and
  a worst-case lower bound for piecewise bounded 1D local Hamiltonians; this does not give one
  explicit fixed nested static Hamiltonian or its recurrence history.
- `[LITERATURE]` Low--Su--Tong--Tran, arXiv:2211.09133 / PRX Quantum 4, 020323 (2023), prove an
  `Ω(n²)` lower bound for generic commuting two-local Hamiltonians at short time; the family is not
  this explicit bounded-degree path and no exact ramp--return composition is given.
- `[LITERATURE]` Oszmaniec--Kotowski--Horodecki--Hunter-Jones, arXiv:2205.09734 / PRX 14, 041068
  (2024), prove saturation and recurrence for random circuits and stochastic local Hamiltonians and
  explicitly separate the unresolved time-independent-Hamiltonian problem.

Preliminary hostile verdict: `SURVIVES PRELIMINARY ATTACK`; scientific priority remains
`[NOVELTY UNVERIFIED]` pending independent exact-object search and referee review.

## Complete paper proof

Write `p_j(x)` for the indicator that both qubits of pair `j` are one, and `b_j(x)` for
the indicator that the right qubit of pair `j` and left qubit of pair `j+1` are one.  Thus

\[
 E_L(x)=\sum_{j=1}^{L}\frac{p_j(x)}{j^2}
       +\sum_{j=1}^{L-1}\frac{b_j(x)}{(j+1)^4}.
\]

### Thermodynamic completion

For `n≥2`,

\[
 \frac1{n^2}\le \frac1{n-1}-\frac1n,
 \qquad
 \frac1{n^4}\le \frac1{(n-1)^3}-\frac1{n^3}.
\]

Both follow after multiplication by their positive common denominators.  Telescoping gives, for
every `L≥1`,

\[
 \sum_{n>L}\frac1{n^2}\le\frac1L,
 \qquad
 \sum_{n>L}\frac1{n^4}\le\frac1{L^3}.
\]

Consequently the two infinite energy series converge absolutely and uniformly in the infinite
configuration `x`.  Their sum is nonnegative, bounded by `2+1=3`, and the uniform error after the
`L`-pair truncation is at most `L^{-1}+L^{-3}`.  Each term is a bounded self-adjoint local diagonal
observable.  The uniform limit is therefore a bounded self-adjoint element of the diagonal
quasi-local completion.  Its first `L` matching terms and first `L-1` bridge terms are exactly
`H_L^{nest}`.  In particular old coefficients never change when volume increases.

### Integer-window lower bound

Fix an integer `K≥8` with `8K≤L` and suppose

\[
 128\pi εK\le t<128\pi ε(K+1).
\]

Assume a support-certified circuit `c` with fewer than `K` counted two-qubit gates is within
operator norm `ε` of `U_L(t)`.  A two-qubit gate touches at most two pair blocks, so fewer than
`2K` pairs are touched.  Among the `4K` pairs whose one-based indices lie in `(4K,8K]`, more than
`2K` remain untouched.  Each matching phase weight on this block is at most `2πε`; their total on
the untouched set is greater than `4πε`.  The elementary greedy subset-sum lemma for nonnegative
weights therefore supplies an untouched subset `S` whose matching phase `θ` satisfies

\[
 3\pi ε\le θ\le5\pi ε.
\]

Cut the qubits between the first and second endpoints of pairs in `S`.  Every circuit gate lies on
one side of this cut, so its diagonal entries on the four Boolean corner configurations satisfy the
rank-one identity

\[
 W_{00}W_{11}=W_{01}W_{10}.
\]

The three configurations `00,01,10` have zero Hamiltonian energy.  The `11` configuration has phase

\[
 \phi=θ+tB_S,
\]

where `B_S≥0` is its bridge energy.  Any active bridge has its right pair in `S`, hence has right
pair index greater than `4K`.  The inverse-fourth tail bound gives

\[
 B_S\le(4K)^{-3}.
\]

Using the strict upper time bound, `K≥8`, and `π<4`,

\[
 tB_S<\frac{128\pi ε(K+1)}{64K^3}
      =2\pi ε\frac{K+1}{K^3}<\frac ε4.
\]

Thus `3πε≤φ≤5πε+ε/4<π` when `ε≤1/100`.  The chord estimate on `[0,π]` yields

\[
 \lVert e^{-i\phi}-1\rVert\ge\frac{2\phi}{\pi}\ge6ε.
\]

On the other hand, operator-norm `ε` approximation bounds each of the four diagonal-entry errors by
`ε`; the rank-one identity and unitary entry bounds give
`\lVert e^{-i\phi}-1\rVert≤4ε`, a contradiction.  Hence every approximating circuit has at least
`K` two-qubit gates.

### Constructive upper bound

Let

\[
 K=\left\lceil\frac{2t}{ε}\right\rceil.
\]

The laboratory upper bound implies `K≤L`.  Apply one exact diagonal two-qubit phase gate to each of
the first `K` matching pairs and to each bridge whose right pair index lies in `2,…,K`.  These gates
exactly implement the truncation through pair `K` and use `K+(K-1)=2K-1≤2K` counted gates.

The omitted matching and bridge energies are nonnegative and, uniformly in the configuration,
bounded by

\[
 K^{-1}+K^{-3}.
\]

Put `x=t/ε`.  Here `x≥1024π>1` and `K≥2x`; hence

\[
 t(K^{-1}+K^{-3})
 \le \frac ε2+\frac{ε}{8x^2}<ε.
\]

Since `|e^{-ia}-e^{-ib}|≤|a-b|`, the diagonal operator-norm error is strictly below `ε`.  This gives
the asserted upper bound `2⌈2t/ε⌉`.

Taking `K=floor(t/(128πε))` in the integer-window lower bound gives `K≥8` and `8K≤L` under the
stated hypotheses, exactly as follows from
`1024πε≤t≤εL/2`.  This proves the laboratory ramp.

### Exact return and reflection

Let `Q_L=(L!)^4`.  If `1≤j≤L` and `L!=ja`, then

\[
 \frac{Q_L}{j^2}=j^2a^4\in\N,
 \qquad
 \frac{Q_L}{j^4}=a^4\in\N.
\]

Every computational-basis energy is therefore `N_x/Q_L` for some natural number `N_x`.  At
`R_L=2πQ_L`, every diagonal phase is one, so `U_L(R_L)=I`.

Autonomy gives `U_L(R_L-t)=U_L(t)^*`.  Adjoint every local gate and reverse circuit order.  This
preserves support, arity, unitarity and counted two-qubit cost, changes circuit matrix to its adjoint,
and preserves global operator norm.  It is a cost-preserving bijection between circuits admitted at
`t` and at `R_L-t`; their `ℕ∞` cost infima are equal.  Reflection transfers both ramp inequalities to
`R_L-t`.  This proves all four clauses. ∎

## Hostile audit

- Family is nested and has a bounded quasi-local diagonal completion, but is not translation
  invariant and has no uniform positive lower bound on distant bond strengths.
- Every finite interaction graph is a connected nearest-neighbour path because every bridge
  coefficient is positive.  Connectivity is graph-theoretic, not a uniform-transport claim.
- Complexity allows arbitrary support-certified two-qubit gates, so lower bound does not rely on
  forcing approximating circuit to respect path geometry.
- Ramp means matching linear lower/upper envelopes.  Literal monotonicity between arbitrary times is
  not proved.
- `R_L` is a valid exact period, not minimal.  No plateau, maximal complexity, chaoticity, Haar
  randomization, infinite-volume return, or interchange of time and volume limits is inferred.
- Thermodynamic completion concerns bounded static energy observable and uniform finite-volume
  convergence.  Infinite-system circuit complexity is not defined.
- Exact-return arithmetic and adjoint reflection are `[BRIDGE]`; priority of complete nested
  ramp--return composition remains `[NOVELTY UNVERIFIED]`.

## Planned proof architecture

1. Dominate inverse-fourth bridge tails by inverse-square tails to obtain absolute summability,
   uniform bound `3`, and uniform truncation error `L^{-1}+L^{-3}`.
2. Reuse untouched-pair four-point obstruction.  On witness block `(4K,8K]`, active bridge phase is
   at most the inverse-fourth tail after `4K`, hence at most `(4K)^{-3}` and at laboratory time at
   most `ε/4`.
3. Construct a circuit containing first `K` matching phases and first `K-1` bridge phases.  With
   `K=ceil(2t/ε)`, omitted matching and bridge energy is at most `K^{-1}+K^{-3}`, giving strict
   operator error below `ε`; cost is `2K-1`.
4. `Q_L=(L!)^4` integerizes every inverse-square and inverse-fourth coefficient, giving exact return.
5. Reuse adjoint circuit reversal for exact complexity reflection and transport both ramp bounds.

## Gates

- [x] 0 → 1: exact claim frozen; internal and external frontier recorded.
- [x] 1 → 2: complete dependency-closed proof and hostile audit; `[PAPER-PROVED]`.
- [ ] 2 → 3: exact Lean theorem, targeted builds, formal lint and axiom audit.
- [ ] 3 → 4: integrate into standalone recurrence manuscript after priority audit.

## Log

- 2026-08-17 — `[PAPER-PROVED] [NOVELTY UNVERIFIED]`; fixed inverse-fourth bridges survive lower,
  upper, exact-return and thermodynamic-limit attacks.  Ready for exact Lean formalization.
