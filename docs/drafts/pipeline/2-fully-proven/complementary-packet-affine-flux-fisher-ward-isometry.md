# Complementary-packet affine flux is the critical Fisher--Ward isometry

- **ID:** `complementary-packet-affine-flux-fisher-ward-isometry`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / ANTI-CAUSAL WARD SOURCE MAP
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Parents:**
  - `complementary-packet-critical-gini-isometry.md`
  - `mobius-critical-fisher-tangent-hilbert-lift.md`
  - `mobius-fixed-current-von-mangoldt-critical-transport-weld.md`
- **Statement:** The unbounded affine flux of the complementary-packet translation cocycle has an
  exact source domain.  Conditional edge flux sends the two-point packet incidence field to the
  centered squarefree logarithmic score.  On the escaping critical state this map is an
  asymptotic isometry: both sides have exactly four units of energy.

## Affine translation model

Fix `omega>0` and write `c_omega=1/(1+omega)`.  Extend the boundary complementary profile to the
full line by

```text
b_omega(t)=k_omega(t)  for t>=0,
b_omega(t)=-c_omega   for t<0.                           (1)
```

For every divisor clock `h>=0`, the packet on the physical half-line is exactly

```text
B_h(t)=b_omega(t-h),  t>=0.                              (2)
```

Individual packets have a common nonintegrable affine mode, but every difference belongs to
`L1 cap L2`.  Define its affine flux by

```text
Phi_omega(B_k-B_h)=integral_0^infinity(B_k(t)-B_h(t))dt. (3)
```

## Exact flux theorem `[PROVED HERE]`

For all `h,k>=0`,

```text
Phi_omega(B_k-B_h)=-c_omega(k-h).                        (4)
```

### Proof

The power-sum remainder bound makes `k_omega` integrable, so the difference in `(3)` is
integrable.  Let

```text
I(k,h)=integral_0^infinity
  [b_omega(t-k)-b_omega(t-h)]dt.
```

For `k>=h`, translation and truncation reduce the difference to the interval `[-k,-h]` plus a
tail tending to zero at positive infinity.  The interval lies in the negative half-line, where
`b_omega=-c_omega`, and therefore contributes `-c_omega(k-h)`.  The positive tail vanishes because
`k_omega` is integrable.  Antisymmetry gives the same formula when `h>k`.  This proves `(4)`.
`QED`

The flux is not a bounded functional on ambient `L2(R_+)`.  Equation `(4)` identifies its exact
affine-cocycle graph domain and value; no extension to arbitrary `L2` vectors is asserted.

## Edge-to-score Ward identity `[PROVED HERE]`

Let `H_sigma=log d` under the squarefree probability `P_sigma`, let `H_sigma'` be independent, and
put `epsilon=sigma-1`, `omega=epsilon/2`.  Define the packet edge field

```text
G_sigma(H,H')=2(B_(H')-B_H).                             (5)
```

Condition on the first endpoint and apply the affine flux:

```text
W_sigma(H)
 =-(epsilon/c_omega)
   E_(H')[Phi_omega(G_sigma(H,H'))|H].                   (6)
```

Equation `(4)` gives, exactly,

```text
W_sigma(H)=-2epsilon(H-E H).                             (7)
```

This is the scalar coefficient of the completed squarefree Fisher tangent

```text
chi_sigma(d)=W_sigma(log d)psi_sigma(d).                 (8)
```

Thus the centered score is not obtained by choosing an isometry between two equal-norm vectors.
It is the conditional affine flux of the same packet incidence cocycle whose connection produces
the Euler source.

## Critical Ward isometry `[PROVED HERE]`

The packet theorem and the Fisher theorem give

```text
epsilon E||G_sigma||_2^2 ->4,                            (9)
E|W_sigma(H_sigma)|^2
 =4epsilon^2 Var(H_sigma)->4.                            (10)
```

Hence the source-domain flux map `(6)` is asymptotically norm preserving on the distinguished
escaping edge field:

```text
E|W_sigma|^2 /
 [epsilon E||G_sigma||_2^2] ->1.                         (11)
```

The result is source-specific and cofinal.  It does not claim that affine flux is a contraction
on an ambient packet Hilbert space.

By the proved `W_2` coupling of the squarefree and von Mangoldt clocks, the same construction on
the coupled Euler edge field differs from `(7)` by `o_(L2)(1)`.  Therefore `(9)`--`(11)` transfer
to the actual Euler fixed-current Fisher score.

## Contact channel

At criticality, `epsilon H` converges to `Y~Exp(1)` and `(7)` converges to the completed score
`2(1-Y)`.  In `L2(e^(-y)dy)`, the constant `1` and the first Laguerre polynomial `1-y` are
orthonormal.  The canonical Laguerre backward shift therefore sends the score `2(1-y)` to the
Euler-pole ground state `2` isometrically.  After the half-density identification, that ground
state is

```text
ell_pole(t)=2e^(-t/2),
||ell_pole||_2^2=4.                                      (12)
```

This is the Hilbert form of the already formalized Fisher--Stein contact identity.  Equations
`(4)`--`(11)` add the missing incidence interpretation: packet curvature, Fisher score, and pole
contact are successive canonical Ward coordinates of one source vector.

## Direct anti-causal Ward attack

Let

```text
Theta_alpha(z)=Xi(1/2-alpha-iz)/Xi(1/2+alpha-iz).
```

Boundary multiplication by `Theta_alpha` is unitary wherever defined, and `Theta_0=1`.  Relative
to the causal/anti-causal Hardy splitting, write its block column on a source vector as

```text
U_alpha v=(A_alpha v,C_alpha v).
```

For any differentiable normalized source curve with `C_0v_0=0`, twice differentiating boundary
unitarity gives the exact Ward decomposition

```text
||C'_0 v_0||^2
 =-Re <A''_0 v_0,v_0>-||A'_0 v_0||^2.                  (13)
```

Derivatives of the source curve are included in `A'`, `A''`, and `C'`; a horizontal gauge removes
the scalar phase.  The second term on the right is nonnegative.  Thus the RH estimate follows if
the source curvature in `(13)` is the four-unit packet/Fisher curvature `(9)`--`(11)` and

```text
C'_0v_0=ell_E.                                          (14)
```

The packet connection identity and fixed-current theorem prove `(14)` at the pre-divisor source
level: the normal derivative is the von Mangoldt--Gamma current `-2Xi'/Xi`.  What remains is the
closed-graph statement that the affine-flux/Fisher Ward map commutes with Gamma/Sonin completion
and anti-causal Hardy compression on the cofinal source core.  If it does, `(13)` gives

```text
||ell_E||_2^2<=4
```

and therefore RH.

## No-go and positive HT consequences

### 1. Ambient bounded-flux no-go

The integral in `(3)` is unbounded on `L2`.

**Positive theorem:** it is exact and asymptotically isometric on the source-selected affine
cocycle graph.

**HT consequence:** a finite fixed current may be carried by an unbounded observable whose graph
norm is nevertheless canonically calibrated on the escaping HT state.

### 2. Local-density no-go

The Gini edge field has local density `4(1-e^(-u))^2`, not the pole density
`4(1-e^(-u))`.

**Positive theorem:** affine flux, not a reparameterization of local energy, converts the complete
edge cocycle to the Fisher score and then to the pole contact.

**HT consequence:** equal global charges can be related by a Ward boundary functional even when
their filtrations are inequivalent.

### 3. Abstract equal-norm no-go

An arbitrary unitary could send the critical score to the pole vector.

**Positive theorem:** `(4)`--`(8)` select the score by packet translation flux, and the Laguerre
backward shift is fixed by the source exponential law.

**HT consequence:** a meaningful integration of HT curvature is fixed by its affine cocycle and
orthogonal-polynomial clock, not by norm matching.

## Novelty and anti-theatre gate

Affine translation cocycles, conditional expectation, Fisher scores, Laguerre polynomials, and
the block-unitary Ward identity are established parents.  Targeted external searches have not
located the exact complementary-packet flux identity `(4)`, its source Fisher isometry
`(6)`--`(11)`, or their use as the finite side of `(13)`.

The external novelty status remains open.  The card does not claim RH: the cofinal
Gamma/Sonin--Hardy graph commutation in `(13)`--`(14)` is not proved.

## Gates

- [x] affine full-line packet representative identified
- [x] exact packet-difference flux proved
- [x] conditional edge flux computed
- [x] edge flux identified with the squarefree Fisher score
- [x] critical four-unit Ward isometry proved
- [x] `W_2` transport to the Euler fixed-current score proved
- [x] Fisher score-to-pole Laguerre contact identified
- [x] abstract anti-causal block-unitary Ward decomposition written
- [ ] prove affine flux is closed on the completed Gamma/Sonin graph core
- [ ] prove the completed Ward source curvature is at most four
- [ ] prove the anti-causal derivative is `ell_E` on that core
- [ ] independent specialist literature audit
- [ ] RH

## Affine flux is unbounded even on the packet-edge Hilbert span

Let `X_omega` be the linear span of packet differences in the affine packet Hilbert quotient.  For

```text
v_a=B_(h+a)-B_h,
a>0,
```

the exact flux theorem and cofinal packet metric give

```text
|Phi_omega(v_a)|^2=c_omega^2 a^2,
||v_a||_2^2=D_omega(a)=c_omega^2 a+O(1).                 (15)
```

Therefore

```text
|Phi_omega(v_a)|/||v_a||_2 -> infinity                  (16)
```

at rate `sqrt(a)`.  The affine flux has no bounded extension even to the closed Hilbert span of
its natural packet-edge domain.  This is stronger than ambient `L2` unboundedness.

**Positive statement:** after source conditioning and critical multiplication by `epsilon`, the
same unbounded graph functional is asymptotically isometric on the distinguished escaping Mobius
edge state, as proved in `(9)`--`(11)`.

**Ward consequence:** an operator-valued KMS or Sonin packet response cannot be turned into a
positive scalar response by a bounded state whose value is affine flux.  The proof-relevant
scalarization must remain a closed graph quotient and use the source probability before the
critical limit; it cannot be a bounded row on packet space.
