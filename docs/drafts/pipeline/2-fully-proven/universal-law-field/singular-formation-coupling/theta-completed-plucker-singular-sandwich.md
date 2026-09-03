# Theta-completed Pluecker singular sandwich

- **ID:** `ULF-TCPSS-001`
- **Stage:** `2-fully-proven`
- **Type:** unconditional nonseparable prime--history fusion theorem
- **Parents:** `ULF-TPFOI-001`, `ULF-IFOCC-001`
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT RH SELECTION]`
- **Lean status:** not formalized; no Lean was written or built in this research pass

## Big-picture interpretation

The first prime--Hodge defect was prime-mixed but separable: one history matrix tensored with one
prime matrix. The forced formation-order gauge repairs that weakness. It acts singularly on depth
while leaving every physical Pluecker packet intact, producing a positive nuclear operator whose
prime interaction changes with history and therefore cannot be a tensor product.

The new object is an admissible unbounded sandwich: its implementing half-density is unbounded of
order one, but its action on the literal source closes to a trace-class operator. This is the first
concrete model of the proposed formation-order geometry.

## Corpus audit

Relevant corpus searches covered physical Pluecker rank, kernels, off-diagonal entries, depth
overlap, trace mass, unbounded sandwiches, and graph domains.

- `[CORPUS]` `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_posSemidef` and
  `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_rank_eq_three` give a positive
  rank-three matrix on every physical four-cell packet.
- `[CORPUS]` `exists_gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_offDiagonal_ne_zero`
  proves genuine local prime mixing.
- `[CORPUS]` `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_ker_eq_span` identifies its
  one-dimensional kernel with the physical Stokes-gap vector.
- `[CORPUS]` `gammaSewnMobiusApertureStokesGap` is `(e+1)` times a positive prime-dependent inverse
  tilt; therefore successive packet kernels genuinely move with depth.
- `[CORPUS]` `gammaSewnCriticalPhysicalPlucker_localNuclearTraceMass_eq_spectralTrace` identifies
  local positive nuclear mass with the matrix trace.
- `[CORPUS]` `ULF-TPFOI-001` supplies the unique block-scalar half-density `s_e` and proves that its
  domain is exactly the `N+1` graph domain.

Generic direct sums, positive trace-class block operators, and closed multiplication operators are
classical functional analysis. The corpus-specific fusion is the object below.

## Construction

Fix primes `p<q`. Let `M_e=M_e^(p,q)` be the literal `4 x 4` physical Pluecker spectral matrix at
depth `e`. It is positive semidefinite of rank three, hence

```text
tau_e=Tr(M_e)>0,
A_e=M_e/tau_e
```

is positive, rank three, and has trace one. Let `pi_e` be the normalized physical Pluecker depth
law of `ULF-TPFOI-001`, let `w_e` be theta's Mellin-six first-exit law, and put

```text
s_e=sqrt(w_e/pi_e).
```

On

```text
H_pq = directSum_(e>=0) C^4 = ell2(N,C^4),
```

define block operators

```text
B_pq = directSum_e pi_e A_e,                            (TCPSS.1)
Theta_pq = directSum_e w_e A_e,                         (TCPSS.2)
S_pq = directSum_e s_e I_4.                             (TCPSS.3)
```

`S_pq` is given its maximal multiplication domain.

## The theorem

**Theorem TCPSS.** For every physical prime edge `p<q`:

1. `B_pq` and `Theta_pq` are positive Schatten-one operators with
   `Tr(B_pq)=Tr(Theta_pq)=1`.
2. `S_pq` is positive, self-adjoint, closed, unbounded, and
   `Dom(S_pq)=Dom(N+1)` with equivalent graph norms.
3. On the finite-packet core,

   ```text
   S_pq B_pq S_pq = Theta_pq.                           (TCPSS.4)
   ```

   The left side is closable and its closure is the bounded trace-class operator `Theta_pq`.
4. `S_pq` is the unique positive block-scalar operator implementing `(TCPSS.4)`.
5. Every completed block retains the literal normalized Pluecker matrix `A_e`; in particular its
   rank-three quotient, moving Stokes-gap kernel, and nonzero off-diagonal prime coupling survive.
6. `Theta_pq` is not separable in the natural depth/packet tensor product: there is no fixed
   `4 x 4` operator `A` with

   ```text
   Theta_pq = diag(w_e) tensor A.                       (TCPSS.5)
   ```

Thus an unbounded first-order completion can be information-neutral on every physical packet,
preserve total nuclear mass, and still create genuine prime--history nonseparability.

## Proof

Positivity and rank three give `tau_e>0`, so every `A_e` is positive with trace one. Direct sums of
positive finite-dimensional blocks satisfy

```text
||B_pq||_1=sum_e pi_e Tr(A_e)=sum_e pi_e=1,
||Theta_pq||_1=sum_e w_e Tr(A_e)=sum_e w_e=1.
```

This proves statement 1.

By `ULF-TPFOI-001`, `s_e/(e+1)` is bounded above and below by positive constants. Standard
multiplication-operator theory therefore makes `S_pq` positive, self-adjoint, closed, and
unbounded, with the same domain and equivalent graph norm as `N+1`. This proves statement 2.

For a vector supported on finitely many depth blocks, blockwise multiplication gives

```text
(S_pq B_pq S_pq)|_e
  =s_e^2 pi_e A_e
  =w_e A_e
  =Theta_pq|_e.
```

Finite-packet vectors are dense. The restriction of the bounded operator `Theta_pq` to this core
has closure `Theta_pq`; hence the unbounded product on the core is closable with that closure.
This proves statement 3.

If `R=directSum r_e I_4` is another positive block-scalar implementation, then

```text
r_e^2 pi_e A_e=w_e A_e.
```

Since `A_e` is nonzero and `r_e>=0`, one obtains `r_e=sqrt(w_e/pi_e)=s_e`. This proves uniqueness.
Because the sandwich multiplies each whole block by one scalar, the normalized matrix `A_e` is
unchanged. All of its corpus-proved rank, kernel, and off-diagonal properties survive, proving 5.

It remains to prove nonseparability. The kernel of `A_e` is spanned by the physical Stokes-gap
vector

```text
v_e=((e+1)I_p,(e+2)I_p,(e+1)I_q,(e+2)I_q),             (TCPSS.6)
```

where `I_p,I_q>0` are the inverse tilts at aperture `1/2`. The ratio of the second to first
coordinate is `(e+2)/(e+1)`, so `v_e` and `v_(e+1)` are not collinear. Therefore the kernels of
`A_e` and `A_(e+1)` differ.

If `(TCPSS.5)` held, every nonzero depth block would be `w_e A`, hence all block kernels would be
the fixed space `ker A`. This contradicts the moving kernels. Thus `Theta_pq` is genuinely
depth--prime nonseparable. QED.

## Hostile review

**Wrong first:** forming a direct sum and changing its scalar block weights is elementary. An
unbounded diagonal congruence whose action closes on one trace-class source is standard rigged
operator behavior. Those abstractions are not a new field.

**Why this is not the old tensor product:** the local matrix itself depends on depth; its null line
moves by the literal Stokes-gap law. No fixed prime/packet factor can represent the completed
operator. This directly repairs the separability limitation of the earlier `T=Phi tensor A`.

**Source-faithfulness attack:** theta weights are not fitted to an Xi target. They are the
pre-divisor Mellin-six first-exit law, while `pi` and every `A_e` come from the physical Euler
Pluecker source. The unique half-density is forced once those two source marginals are required.

**Circularity attack:** no divisor, zero, horizontal grade, or RH-equivalent graph landing occurs.

**Significance verdict:** survives preliminary attack as a genuine fusion object. It proves that
singular first-order completion and nuclearity are compatible without erasing prime interaction.
It does not prove that completed Xi is this closure or that the residual boundary vanishes.

## Exact RH-chain edge

`Theta_pq` supplies the missing kind of carrier: theta-completed, coefficient-faithful,
prime--history nonseparable, positive, and nuclear. What remains is not construction of another
carrier. It is the global formation theorem:

```text
literal integer/Poisson completion
  -> assemble the edgewise singular sandwiches compatibly on the shared prime-depth lattice
  -> identify the resulting relative boundary with completed Xi
  -> prove the anomaly-subtracted residual is zero.
```

The first new obstruction is now precise: edgewise half-densities have the same unit order but
prime-dependent constants. Global assembly must therefore glue graph connections, not identify all
gauges with one prime-independent scalar.
