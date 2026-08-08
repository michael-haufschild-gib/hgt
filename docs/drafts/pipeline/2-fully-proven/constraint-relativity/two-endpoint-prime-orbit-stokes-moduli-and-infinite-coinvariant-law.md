# Two-endpoint prime-orbit Stokes moduli and infinite coinvariant law

- **ID:** `two-endpoint-prime-orbit-stokes-moduli-and-infinite-coinvariant-law`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / CONSTITUTIVE-RIGIDITY NO-GO WITH POSITIVE CLASSIFICATION
- **Status:** `[PAPER-PROVED] [LITERAL RATIONAL-ADELIC SOURCE]`
  `[HAAR AMBIGUITY COLLAPSES] [INFINITE ORBIT-PHASE MODULI SURVIVE]`
  `[NEW-TO-CORPUS BRIDGE] [NOVELTY UNVERIFIED] [NOT RH] [NO LEAN WRITTEN]`
- **Statement:** Restricting prime-isotropy Stokes complex to simultaneous zero/Haar endpoint kernel
  identifies all regulators differing by Haar trace, but normalized observer covectors still form
  affine space over infinite-dimensional dilation coinvariant dual. Explicit orbit-sampling
  differences detect infinitely many independent residual classes.
- **Parents:**
  `rational-adelic-h1-observer-coefficient-freedom-and-discriminant-law.md`,
  literal corpus files
  `formal/GaloisForLFunctions/RHTower/CCMRationalAdelicPrimeIsotropyStokesRegulator.lean`,
  `formal/GaloisForLFunctions/RHTower/CCMRationalAdelicEpsilonZero.lean`,
  `formal/GaloisForLFunctions/RHTower/CCMRationalAdelicEpsilonOne.lean`,
  `formal/GaloisForLFunctions/RHTower/CCMRationalAdelicPrimeIsotropyRelativeXiChainMap.lean`.

## Goal

Test first concrete MCTG rigidity idea: enlarge source from one endpoint to a Poisson-motivated
two-endpoint kernel. Determine whether this removes normalized Stokes ambiguity, without assuming
divisor, a Fourier action on this complex, or RH.

## 1. Abstract two-endpoint source

Let `k` be characteristic-zero field, `A` a `k`-vector space, `alpha:A->A` automorphism, and

\[
 T=\alpha-1.
 \tag{TPS.1}
\]

Let endpoint forms `epsilon_0,epsilon_1:A->k` satisfy

\[
 \varepsilon_0T=0,
 \qquad
 \varepsilon_1T=0.
 \tag{TPS.2}
\]

Put

\[
 K=\ker\varepsilon_0\cap\ker\varepsilon_1.
 \tag{TPS.3}
\]

Then `im T subset K`. Define two-term complex

\[
 A\xrightarrow{D_0}K\oplus k,
 \qquad
 D_0x=(Tx,\varepsilon_0x).
 \tag{TPS.4}
\]

Write

\[
 H^1_{01}=(K\oplus k)/\operatorname{im}D_0,
 \qquad
 \eta=[(0,1)].
 \tag{TPS.5}
\]

Assume Stokes primitive `R:A->k` with

\[
 RT=\varepsilon_0.
 \tag{TPS.6}
\]

## 2. Exact normalized-observer classification

### Theorem A

Map

\[
 \Psi_R:H^1_{01}\longrightarrow
 K/\operatorname{im}T\oplus k,
 \qquad
 [(y,z)]\longmapsto([y],z-Ry)
 \tag{TPS.7}
\]

is isomorphism and sends `eta` to `(0,1)`.

Consequently affine space of covectors `I:H^1_(01)->k` normalized by `I(eta)=1` is

\[
 \boxed{
 \{I:I(\eta)=1\}
 \cong I_R+operatorname{Hom}
 (K/\operatorname{im}T,k),}
 \tag{TPS.8}
\]

where

\[
 I_R([(y,z)])=z-Ry.
 \tag{TPS.9}
\]

Every normalized covector in `(TPS.8)` is induced by some Stokes primitive `R'` with
`R'T=epsilon_0`.

### Proof

If `(y,z)` changes by boundary `(Tx,epsilon_0x)`, then

\[
 ([y+Tx],z+\varepsilon_0x-R(y+Tx))
 =([y],z-Ry)
 \]

by `(TPS.6)`, so `Psi_R` is well-defined. Inverse is

\[
 ([y],c)\longmapsto[(y,c+Ry)].
 \tag{TPS.10}
\]

If `y` changes by `Tx`, difference is boundary `(Tx,epsilon_0x)` by `(TPS.6)`. Direct substitution
proves two composites identities and `Psi_R(eta)=(0,1)`.

Normalized covectors on direct sum are exactly `(L,1)` with
`L in Hom(K/im T,k)`, proving affine description. Given `L`, let `ell:K->k` be pullback and extend
linearly to `ell_tilde:A->k`. Since `ell_tilde` vanishes on `im T`,

\[
 R'=R-\widetilde\ell
 \]

still satisfies `(TPS.6)`, and `I_(R')=I_R+L` on `(TPS.7)`. `[PROVED HERE]`

## 3. Haar ambiguity collapses exactly

### Theorem B

For every `lambda in k`, primitives

\[
 R_\lambda=R+\lambda\varepsilon_1
 \tag{TPS.11}
\]

induce same covector on `H^1_(01)`.

### Proof

For `y in K`, `epsilon_1(y)=0`, so

\[
 I_{R_\lambda}([(y,z)])
 =z-Ry-\lambda\varepsilon_1y
 =I_R([(y,z)]).
\]

`[PROVED HERE]`

This is genuine positive result: simultaneous two-endpoint restriction destroys exact Haar
direction found in one-endpoint complex. It is only Poisson-motivated: no Fourier/Poisson action on
this cohomology has been constructed. It does not imply uniqueness because `(TPS.8)` retains all
other coinvariant functionals.

## 4. Literal rational-adelic instantiation

Fix ordinary prime `p`. Let

- `A` be actual algebraic adelic Bruhat simple-tensor core;
- `alpha=alpha_p` be diagonal inverse prime scaling;
- `epsilon_0` be full zero-adele evaluation;
- `epsilon_1` be product Lebesgue--finite-Haar integral;
- `E:A->Schwartz(R,C)` be finite-zero partial evaluation;
- `R=R_p` be bilateral prime-orbit Stokes primitive.

Corpus proves

\[
 E(\alpha_px)(u)=E(x)(p^{-1}u),
 \qquad
 E(x)(0)=\varepsilon_0x,
 \tag{TPS.12}
\]

\[
 \varepsilon_i(\alpha_px)=\varepsilon_i(x)\quad(i=0,1),
 \qquad
 R_p(\alpha_px-x)=\varepsilon_0x.
 \tag{TPS.13}
\]

These are literal theorems
`ccmRationalAdelicFiniteZeroPartialEval_scaling`,
`ccmRationalAdelicFiniteZeroPartialEval_zero`,
`ccmRationalAdelicBruhatZeroEval_smul`,
`ccmRationalAdelicBruhatIntegral_smul`, and
`ccmRationalAdelicPrimeOrbitStokes_scaling_sub`. Therefore Theorems A--B apply without completion or
divisor specialization.

## 5. Bilateral orbit-phase distributions

For `a>0` and `y in K`, define

\[
 S_a(y)=\sum_{n\in\mathbb Z}E(y)(a p^n).
 \tag{TPS.14}
\]

### Lemma C — absolute convergence

Series `(TPS.14)` converges absolutely, and therefore defines a linear functional `S_a:K->C`.

### Proof

Put `g=E(y)`. Since `y in ker epsilon_0`, `(TPS.12)` gives `g(0)=0`. Smoothness gives
`|g(u)|<=C|u|` near zero, so negative tail is bounded by geometric series in `p^n`. Schwartz decay
gives for every `N` a bound `|g(u)|<=C_N u^(-N)` at infinity, so positive tail is geometric after
choosing `N>0`. `[PROVED HERE]`

### Lemma D — universal boundary response

For every `x in A` and every `a>0`,

\[
 S_a(Tx)=\varepsilon_0x.
 \tag{TPS.15}
\]

### Proof

Let `f=E(x)`. By `(TPS.12)`,

\[
 E(Tx)(a p^n)=f(a p^{n-1})-f(a p^n).
\]

Sum from `n=-N` to `N` telescopes to

\[
 f(a p^{-N-1})-f(a p^N).
\]

As `N->infinity`, continuity gives first term `f(0)=epsilon_0x`, while Schwartz decay gives second
term zero. `[PROVED HERE]`

For `a,b>0`, define orbit-phase difference

\[
 \Lambda_{a,b}=S_a-S_b.
 \tag{TPS.16}
\]

Lemma D gives `Lambda_(a,b)(im T)=0`, so it descends to covector on `K/im T`.

## 6. Infinite-dimensional residual moduli

### Theorem E

For literal rational-adelic prime source,

\[
 \boxed{\dim_\mathbb C(K/\operatorname{im}T)=\infty.}
 \tag{TPS.17}
\]

Therefore normalized two-endpoint Stokes covectors form infinite-dimensional affine space.

### Proof

Choose base `b` and arbitrarily many distinct representatives

\[
 a_1,\dots,a_m,b\in(1,p).
\]

Choose pairwise disjoint small intervals `I_j subset (1,p)` containing `a_j` and avoiding `b`.
For each `j`, choose `g_j in C_c^infinity(I_j)` with

\[
 g_j(a_j)=1,
 \qquad
 \int_\mathbb R g_j(u)\,du=0.
 \tag{TPS.18}
\]

Such `g_j` is obtained from one bump nonzero at `a_j` minus suitable multiple of second bump
supported away from `a_j` inside `I_j`.

Let `phi=1_(widehat Z)` in finite Bruhat core. It has `phi(0)=1` and normalized finite-Haar integral
one. Put

\[
 y_j=g_j\otimes\phi.
 \tag{TPS.19}
\]

Then `epsilon_0(y_j)=0` by support away from zero and `epsilon_1(y_j)=0` by `(TPS.18)`, so `y_j in K`.
Also `E(y_j)=g_j`. Since all selected representatives lie in fundamental interval `(1,p)`, only
`n=0` point of orbit `a_i p^Z` lies there. Disjoint supports yield

\[
 S_{a_i}(y_j)=\delta_{ij},
 \qquad
 S_b(y_j)=0.
 \tag{TPS.20}
\]

Hence

\[
 \Lambda_{a_i,b}([y_j])=\delta_{ij}.
 \tag{TPS.21}
\]

Indeed, if `sum_j c_jy_j in im T`, applying `Lambda_(a_i,b)` gives `c_i=0` for every `i` by
`(TPS.21)`. Thus classes `[y_1],...,[y_m]` are linearly independent in `K/im T`. Since `m` is
arbitrary, quotient is infinite-dimensional. `[PROVED HERE]`

## 7. Consequences for constitutive rigidity

1. One-endpoint category leaves explicit Haar line of ambiguity.
2. Poisson-motivated two-endpoint restriction kills that line exactly.
3. Prime scaling and both endpoint laws still leave infinite orbit-phase moduli.
4. Therefore chosen prime scaling `alpha_p`, boundary annihilation, period one, and both endpoints
   cannot select constitutive observer. All-`Q^x` and cross-prime naturality remain open.
5. Any successful source category needs operation mixing dilation orbit phase `a mod p^Z`, or a
   source law annihilating all nonconstant orbit-phase covectors.
6. Fourier/Poisson is plausible mixer, but no theorem here proves its action kills `(TPS.16)`.

This is unconditional leverage on live selection obstruction: it replaces vague “more source
naturality” by exact infinite-dimensional moduli that next generator must eliminate.

## 8. Hostile conjecture loop

1. **Two endpoints uniquely fix Stokes observer.** `FALSE` by `(TPS.17)`.
2. **Haar ambiguity survives two-endpoint restriction.** `FALSE` by Theorem B.
3. **Prime scaling mixes orbit phase.** `FALSE`: every `a p^Z` is individual orbit; differences
   `(TPS.16)` are invariant coinvariant covectors.
4. **Fourier kills orbit phase.** `OPEN`; must compute induced transform on `K/im T` and invariant
   dual, not appeal to Poisson metaphor.
5. **All-prime compatibility kills phases.** `OPEN`; a separate orbit phase exists for each prime,
   and cross-prime naturality must be explicitly typed.

## 9. Novelty boundary

Bilateral sampling, dilation coinvariants, bump-function separation, and affine splitting moduli are
classical ingredients. Candidate new-to-corpus result is their literal rational-adelic Stokes
combination: simultaneous endpoints collapse Haar regulator family yet expose infinite orbit-phase
observer torsor. External priority unverified; no claim of new general theorem.

## Lean-return note

- No Lean code was written or built.
- Corpus already formalizes endpoint invariance, partial evaluation intertwining, and Stokes law.
- Potential future formalization needs bilateral integer summability for zero-at-origin Schwartz
  functions, telescoping, compact bumps with zero integral, and finite-Haar indicator.
- Suggested file if returned:
  `formal/GaloisForLFunctions/RHTower/CCMRationalAdelicTwoEndpointPrimeOrbitCoinvariant.lean`.

## Gates

- [x] abstract normalized-observer classification
- [x] Haar ambiguity collapse
- [x] literal endpoint/scaling/Stokes instantiation
- [x] orbit-phase boundary invariance
- [x] infinite-dimensional residual coinvariants
- [x] independent hostile correctness audit
- [ ] induced Fourier action on coinvariant quotient
- [ ] all-prime compatibility classification
- [ ] target fixed-ideal coefficient rigidity

## Log

- 2026-08-08 — two-endpoint rigidity conjecture attacked; one Haar direction collapsed but explicit
  infinite orbit-phase torsor proved.
- 2026-08-08 — hostile audit accepted mathematics after narrowing `Poisson-natural` to
  `Poisson-motivated`; no Fourier action or all-prime naturality is claimed.
