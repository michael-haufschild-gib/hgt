# Krylov causal replica sieve law

- **ID:** `krylov-causal-replica-sieve-law`
- **Stage:** 3 — formalized
- **Type:** THEOREM / REPLACEMENT MECHANISM
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [AXIOM-AUDITED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/scalar-recurrence-traceless-replica-decoupling-law.md`
- **Date:** 2026-08-06

## Public sentence

An observer blind to the first `K+1` energy moments cannot detect bounded
Hamiltonian time evolution before the corresponding Krylov horizon; replica
order amplifies this causal exclusion exponentially.

## Exact theorem

Let `I` be finite, let `c_i` be complex coefficients, let `E_i` be real,
and put

\[
 F(t)=\sum_{i\in I}c_i e^{\mathrm i tE_i}.
\]

Fix `K,r in N`, `r>=1`, `T>0`, and numbers `A,B>=0`. Assume

\[
 \sum_i|c_i|\le A,
 \qquad |E_i|\le B,
 \qquad \sum_i c_iE_i^k=0\quad(0\le k\le K).       \tag{1}
\]

Then

\[
 \boxed{
 |F(t)|\le
 A\,{(B|t|)^{K+1}\over(K+1)!}
 \quad(t\in\mathbb R),}                              \tag{2}
\]

and

\[
 \boxed{
 {1\over2T}\int_{-T}^{T}|F(t)|^{2r}\,dt
 \le {A^{2r}\over2r(K+1)+1}
 \left({(BT)^{K+1}\over(K+1)!}\right)^{2r}.}        \tag{3}
\]

Consequently, for every `theta>0`,

\[
 \boxed{
 {\left|\{t\in[-T,T]:|F(t)|\ge\theta\}\right|\over2T}
 \le {A^{2r}\theta^{-2r}\over2r(K+1)+1}
 \left({(BT)^{K+1}\over(K+1)!}\right)^{2r}.}        \tag{4}
\]

For a finite dictionary `D` whose every target amplitude obeys `(1)` with
the same `A,B,K`, subadditivity gives the right side of `(4)` multiplied by
`|D|`.  Since `(K+1)! >= ((K+1)/e)^(K+1)`, the circuit-union factor is beaten
whenever

\[
 2r(K+1)\log{K+1\over eBT}
 > \log|D|+2r\log(A/\theta).                         \tag{5}
\]

This is a growing-replica estimate for the signed physical reporter itself,
not for the positive near-action relaxation `Z_r`.

## Proof

Write `L=K+1`. Taylor's theorem with integral remainder on the real segment
from `0` to `t` gives, for real `x`,

\[
 e^{\mathrm ix}
 =\sum_{k=0}^{L-1}{(\mathrm ix)^k\over k!}+R_L(x),
 \qquad |R_L(x)|\le {|x|^L\over L!}.                 \tag{6}
\]

The sharp bound follows because every real derivative of
`s -> exp(i s)` has modulus one. Substitute `x=tE_i`, multiply by `c_i`,
and sum. Every polynomial term vanishes by `(1)`, while the remainder obeys

\[
 |F(t)|
 \le\sum_i|c_i|{|tE_i|^L\over L!}
 \le A{(B|t|)^L\over L!},                            \tag{7}
\]

proving `(2)`. Raise `(7)` to the power `2r` and use

\[
 {1\over2T}\int_{-T}^{T}|t|^{2rL}\,dt
 ={T^{2rL}\over2rL+1}                                \tag{8}

to obtain `(3)`. Markov's integral inequality proves `(4)`, finite
subadditivity proves the dictionary form, and the standard factorial lower
bound proves `(5)`.

## Static-Choi specialization

Let `H` have eigenvalues `E_i` in `[-B,B]`, and let `phi` be a normalized
Choi target. Its diagonal spectral coefficients are

\[
 c_i=d^{-1/2}\langle i,i|\phi\rangle,
 \qquad \sum_i|c_i|\le1.                              \tag{9}
\]

Orthogonality of `phi` to the Choi Krylov vectors corresponding to
`I,H,...,H^K` is exactly the moment-null condition in `(1)`. Therefore
`A=1` in `(2)`--`(5)`. The statement holds for each fixed Hamiltonian, so no
annealed-to-quenched conversion and no exceptional ensemble event is needed.

## Hostile audit

1. This theorem does not bound the positive near-action mass `Z_r`; that
   object has the central-limit floor proved on the companion route-killer
   card.
2. Moment nullity alone does not control near-action spectral mass. It
   controls the observed finite-time kernel directly, through cancellation.
3. Arbitrary circuit targets are not Krylov-null. Every target must first be
   decomposed into its projection onto `span{I,H,...,H^K}` and its orthogonal
   residual. Equations `(2)`--`(5)` close only the residual channel.
4. The remaining carrier channel is not a harmless finite-dimensional error:
   it contains the actual early-time orbit. Bounding its intersection with
   shallow circuits is the surviving no-fast-forwarding problem.
5. The theorem gives an early-time exclusion law, not plateau occupation or
   recurrence time by itself.

**Verdict:** `PAPER-PROVED` as a universal residual theorem. It does not close
the master Brown--Susskind card.

## Representation lesson and exact open core

Positive spectral crowding was the wrong variable, and signed near-window
mass remains too crude. The physical finite-time kernel itself is the correct
object: Krylov cancellation converts directly into factorial time delay.

After the canonical orthogonal split

\[
 U=P_K(H)U+(I-P_K(H))U,                              \tag{10}
\]

the residual is controlled by `(3)` without any spectral-spacing input. The
exact `[OPEN CORE]` is therefore:

> Prove a quenched growing-`K` transversality bound between the fixed shallow-
> circuit family and the random Krylov carrier `span{I,H,...,H^K}` for the
> normalized fixed-`q` Gaussian Pauli ensemble, strong enough that the carrier
> channel plus `(4)` survives the circuit union.

This is strictly more precise than a bound on `Z_r`: it identifies which
part of every target remains uncontrolled and proves the complement.

## Gates

- [x] 0 -> 1: exact statement and hostile falsifiers
- [x] 1 -> 2: dependency-closed proof
- [x] 2 -> 3: exact Lean theorem and axiom audit
- [ ] 3 -> 4: external priority audit and manuscript use only after carrier closure

## Log

- 2026-08-06 — Replaced impossible positive near-action control by a direct
  factorial finite-time bound on every Krylov-null target channel.

## Formal trace

Module:
`formal/GaloisForLFunctions/HTGeometry/KrylovCausalReplicaSieveLaw.lean`.

The exact pointwise and symmetric-window conclusions are
`norm_finiteRealTimeComplexAmplitude_le_of_moment_null_abs` and
`uniformMoment_finiteRealTimeComplexAmplitude_le_of_moment_null`.
The owning file passes `lake env lean`. `#print axioms` for the derivative,
sharp Taylor, pointwise, power-integral, unnormalized-moment, and normalized-
moment capstones reports only `propext`, `Classical.choice`, and `Quot.sound`.
