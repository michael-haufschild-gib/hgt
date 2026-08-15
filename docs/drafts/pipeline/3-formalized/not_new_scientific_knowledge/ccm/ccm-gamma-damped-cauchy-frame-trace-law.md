# The Gamma-damped Cauchy carrier is a channel-resolved Hilbert--Schmidt frame

- **ID:** `ccm-gamma-damped-cauchy-frame-trace-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Hilbert--Schmidt synthesis operators, trace-class Gram operators, the archimedean
  Gamma cyclic representation, and
  `gamma-damped-prime-log-cauchy-domain.md`

## 1. Pointed Gamma cyclic source

Let `mu_infinity` be the normalized archimedean cyclic measure with characteristic function

```text
phi(t)=int exp(i t s) dmu_infinity(s)=(cosh t)^(-1/2).
```

Write `H_infinity=L^2(mu_infinity)`, let `U_t` be multiplication by `exp(i t s)`, let `xi=1`, and
let `P_xi` be the rank-one projection onto `C xi`. Then

```text
P_xi U_(2t) P_xi=phi(2t)P_xi.                            (1)
```

Since `phi(2t)>0`, functional calculus gives

```text
||(P_xi U_(2t) P_xi)^(1/2)xi||=sqrt(phi(2t)).             (2)
```

Thus the damping

```text
d(t)=sqrt(phi(2t))                                       (3)
```

is the half-density of the pointed reflected-mode overlap. It is selected canonically by the
pointed Gamma cyclic system `(H_infinity,U,xi)`, rather than chosen as an arbitrary scalar gauge.

## 2. Channel-resolved Cauchy synthesis

For a finite Cauchy packet

```text
a_p=sum_j c_j/(z_j-log p),
t_p=log p,
```

define on the prime basis of `ell^2(P)`

```text
T_(z,c)e_p=a_p d(t_p) U_(t_p)xi.                         (4)
```

The formal theorem `summable_gammaDampedPrimeLogCauchyPacketEnergy` is exactly

```text
sum_p ||T_(z,c)e_p||^2
 =sum_p phi(2log p)|a_p|^2<infinity.                     (5)
```

Therefore `(4)` extends uniquely to a Hilbert--Schmidt operator

```text
T_(z,c):ell^2(P)->H_infinity.                             (6)
```

## 3. Positive Gram with additive trace

The operator

```text
G_(z,c)=T_(z,c)^*T_(z,c)                                 (7)
```

is positive and trace class. Its matrix entries retain the complete Gamma covariance:

```text
<e_p,G_(z,c)e_q>
 =conj(a_p)a_q d(t_p)d(t_q)phi(t_q-t_p).                 (8)
```

In particular, all off-diagonal prime interactions survive in `(8)`. Nevertheless the trace is
automatically additive over prime channels:

```text
Tr G_(z,c)
 =sum_p <e_p,G_(z,c)e_p>
 =sum_p phi(2log p)|a_p|^2.                              (9)
```

There are no cross-prime terms in `(9)`. The apparent conflict between positive Gamma covariance
and additive Euler trace arose only after collapsing the prime input to the coherent all-ones
direction before taking the norm. Channel resolution keeps the covariance in the operator and lets
the trace read its diagonal.

### Proof

Equation `(1)` follows from

```text
<xi,U_(2t)xi>=phi(2t).
```

Because the compression has rank one and positive scalar eigenvalue, `(2)` follows from the
positive square root. Equation `(5)` is the Gamma-damped Cauchy-domain theorem. The standard
Hilbert--Schmidt synthesis theorem yields `(6)`. Equations `(7)`--`(9)` are the Gram-entry formula
and the trace identity for a Hilbert--Schmidt operator. `QED`

## 4. Positive CCM consequence

A successful CCM construction is forced to preserve prime-channel resolution until after the
positive Gram operator has been formed. It may then take a trace, relative trace, determinant, or
Sonin compression. Scalar coherent summation before the Gram is the wrong operation because it
turns the off-diagonal covariance into unwanted scalar cross terms.

The open theorem is correspondingly sharper. The channel-resolved construction must be realized
inside the actual Gauss-paired Hardy--Titchmarsh/Sonin operator and its diagonal must be identified
with the completed prime--archimedean Weil/Pick source. The present diagonal is

```text
phi(2log p)=sqrt(2)p/sqrt(p^4+1),                         (10)
```

which has the correct inverse-prime order but is not literally the von-Mangoldt/Euler coefficient.
The exact prime-power correction is now computed in
`ccm-euler-gamma-radon-nikodym-frame-law.md`: multiplication of the `(p,k)` channel by the positive
contraction

```text
r_(p,k)^(1/2),
r_(p,k)=sqrt(1+p^(-4k))/(sqrt(2)k),
```

makes its squared norm exactly `1/(k p^k)`. Thus `(9)` solves covariance bookkeeping and
Hilbert-domain existence in the Euler-log region. It does not solve the centered von-Mangoldt
source: the exact critical correction grows as
`((log p)/sqrt(2))p^(k/2)sqrt(1+p^(-4k))`. The actual Sonin realization must carry this unbounded
recession together with the archimedean/boundary divided-difference channel.

## 5. Scope and classification

Rank-one compression, Hilbert--Schmidt synthesis, and `Tr(T^*T)=||T||_HS^2` are standard operator
theory. The theorem is a route bridge, not new scientific knowledge. Its value is to remove a false
requirement: the off-diagonal covariance need not be canceled before trace. It must be retained in
a channel-resolved positive operator whose diagonal is proved to be the arithmetic source.

## Gates

- [x] canonical pointed Gamma half-density identified
- [x] complete finite-Cauchy Hilbert--Schmidt synthesis proved
- [x] positive covariance and additive trace coexistence proved
- [x] exact Euler-region prime-power diagonal obtained by a canonical positive contraction
- [x] critical von-Mangoldt diagonal shown to require an unbounded correction
- [ ] realize the synthesis inside the Gauss-paired Hardy--Titchmarsh/Sonin carrier
- [ ] add the exact archimedean/boundary relative channel
- [ ] transport Pick inertia cofinally
- [ ] RH

## Lean status

`[FORMALIZED]` — module `formal/GaloisForLFunctions/RHTower/CCMGammaDampedCauchyFrame.lean`
(10 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired
into `formal/GaloisForLFunctions/RHTower.lean`).

The operator statements are proved over the data of a pointed unitary system — a complex inner
product space, a one-parameter family of norm-preserving operators with the group law, and a unit
vector — which is exactly the structure the cited archimedean cyclic representation supplies.

What is proved in Lean:

- `rankOneProj`, `rankOneProj_idem` — the rank-one projection onto the pointed line.
- `rankOneProj_compression` — **equation (1)**: `P_ξ U P_ξ = ⟪ξ, U ξ⟫ · P_ξ`; the scalar overlap is
  the entire compression, for *any* operator `U`.
- `gammaDampingProfile_pos`, `halfDensity`, `halfDensity_sq`, `halfDensity_pos` — **equations
  (2)–(3)**: the canonical half-density `d(t) = √(φ(2t))` is positive and squares back to `φ(2t)`.
- `norm_sq_synthesis_column` — **equations (4)–(5), one channel**: the synthesis column
  `a · d · U_t ξ` has squared norm exactly `|a|² d²`.
- `sum_norm_sq_synthesis`, `sum_channel_energy` — **equations (5), (9)**: the frame energy is the
  diagonal sum `∑ |a_i|² φ(2 t_i)`; **no cross-channel terms appear**, which is the card's point
  about channel resolution.
- `gram_entry_synthesis` — **equation (8)**: the Gram entry is
  `conj(a_p) a_q d_p d_q ⟪ξ, U_{t_q - t_p} ξ⟫`, so the complete off-diagonal Gamma covariance
  survives in the operator even though the trace reads only the diagonal.
- `gammaDiagSq_prime` — **equation (10)**: `φ(2 log p) = √2 p/√(p⁴+1)`, obtained from
  `gammaDiagSq_eq` at `k = 1`.

Reused, not rebuilt: `gammaDampingProfile`, `gammaDiagSq`, `gammaDiagSq_eq`,
`gammaDampingProfile_eq_inv_sqrt`, and the Euler/critical corrections
(`ccm-euler-gamma-radon-nikodym-frame-law`, module `CCMEulerGammaRadonNikodym`), which already
carry `r_{p,k}` and the unbounded critical correction quoted in section 4 of this card.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the existence of the archimedean cyclic measure `μ_∞` with characteristic function
  `(cosh t)^{-1/2}` and the concrete realization `H_∞ = L²(μ_∞)`;
- the Hilbert–Schmidt synthesis theorem extending `(4)` from the finite basis, and the trace-class
  statement for `G = T^*T`;
- the summability theorem `summable_gammaDampedPrimeLogCauchyPacketEnergy` quoted as `(5)`.
