# The coupled Möbius source is an exact signed-channel projection

- **ID:** `mobius-signed-channel-coisometry-incidence-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Source:** `coupled-floor-mobius-complementary-shift-incidence-law.md`;
  `mobius-critical-exponential-boundary-layer-law.md`;
  `da-gauge-ht-divisor-blindness.md`
- **Statement:** The exact coupled floor--Möbius error is the image of a canonical channel feature
  under a signed coisometry.  Equivalently, its entire arithmetic cancellation is the orthogonal
  projection of that feature onto one distinguished source line in the divisor-channel index.
  This constructs the pointed source projection unconditionally and isolates the RH-bearing step
  as a quantitative angle theorem after archimedean boundary renormalization.

## 1. Squarefree channel probability

Fix `omega>0` and put

```text
sigma=1+2omega,
Z_omega=sum_(d>=1)mu(d)^2d^(-sigma)
       =zeta(sigma)/zeta(2sigma),                         (1)

P_omega(d)=mu(d)^2d^(-sigma)/Z_omega.                    (2)
```

Then `P_omega` is a probability measure supported on squarefree positive integers.  Define the
sign character

```text
epsilon(d)=mu(d) when mu(d)!=0, and 0 otherwise.          (3)
```

On the support of `P_omega`, `|epsilon(d)|=1`.

Let `H=L2(R_(>=0),dt)` and

```text
K_omega=direct_sum_(d>=1) H.                              (4)
```

## 2. Signed source coisometry

Define

```text
R_omega:K_omega->H,
R_omega((f_d))
 =sum_d epsilon(d)sqrt(P_omega(d)) f_d.                  (5)
```

The series converges in `H` and

```text
||R_omega||=1,
R_omega R_omega^*=I_H.                                   (6)
```

### Proof

For every channel vector, Cauchy--Schwarz and `sum_d P_omega(d)=1` give

```text
||R_omega((f_d))||
 <=(sum_d P_omega(d))^(1/2)
   (sum_d||f_d||^2)^(1/2)
 =||(f_d)||.                                              (7)
```

The adjoint is

```text
(R_omega^*h)_d
 =epsilon(d)sqrt(P_omega(d))h.                            (8)
```

Consequently

```text
R_omega R_omega^*h
 =sum_d epsilon(d)^2P_omega(d)h=h,                       (9)
```

proving `(6)`.  Thus `R_omega^*` is an isometry and `R_omega` is a coisometry.

Put

```text
Pi_omega=R_omega^*R_omega.                               (10)
```

Then `Pi_omega` is the orthogonal projection onto `range(R_omega^*)`.  It is rank one in the
channel index, tensored with the identity on `H`.

## 3. Coupled floor--tail feature

Let `V_(log d)` be the right shift on `H`, let `P_d=V_(log d)V_(log d)^*`, and put

```text
k_omega(t)=e^(-(1+omega)t)R_omega_floor(e^t),
c_omega=1/(1+omega),                                     (11)
```

where

```text
R_omega_floor(Y)
 =sum_(m<=Y)m^omega-Y^(1+omega)/(1+omega).               (12)
```

To avoid collision with the coisometry notation, `R_omega_floor` denotes the scalar power-sum
remainder from `(12)`.

For every `d`, the truncated constant `(I-P_d)1` belongs to `H`, even though the common boundary
mode `1` does not.  Define

```text
B_(omega,d)
 =V_(log d)k_omega-c_omega(I-P_d)1,                      (13)

(Y_omega)_d=sqrt(P_omega(d))B_(omega,d).                 (14)
```

Then `Y_omega` belongs to `K_omega`.

Indeed, the two terms in `(13)` have disjoint supports, so

```text
||B_(omega,d)||^2
 =||k_omega||^2+c_omega^2 log d.                         (15)
```

The logarithmic moment is finite and equals

```text
E_(P_omega)[log d]
 =-zeta'/zeta(sigma)+2zeta'/zeta(2sigma).                (16)
```

Therefore

```text
||Y_omega||^2
 =||k_omega||^2
  +c_omega^2(
      -zeta'/zeta(sigma)+2zeta'/zeta(2sigma)
    ).                                                    (17)
```

## 4. Exact projection identity

Let

```text
F_omega(t)=e^(-(1+omega)t)E_omega(e^t).                  (18)
```

The complementary-incidence theorem gives

```text
F_omega
 =sum_d mu(d)d^(-sigma)B_(omega,d).                      (19)
```

Using `(2)`--`(5)` and `(14)`,

```text
R_omega Y_omega
 =sum_d epsilon(d)P_omega(d)B_(omega,d)
 =F_omega/Z_omega.                                       (20)
```

Hence

```text
F_omega=Z_omega R_omega Y_omega.                         (21)
```

Because `R_omega` is a coisometry and `Pi_omega=R_omega^*R_omega`,

```text
||R_omega Y_omega||=||Pi_omega Y_omega||.                (22)
```

Combining `(21)`--`(22)` yields the exact cancellation law

```text
||F_omega||
 =Z_omega||Pi_omega Y_omega||.                           (23)
```

Thus cancellation between the floor discrepancy and Möbius tail is neither a triangle-inequality
estimate nor an unspecified correlation.  It is exactly the angle of the pointed feature
`Y_omega` to the distinguished signed source subspace `range(R_omega^*)`.

## 5. What the diagonal boundary layer does and does not prove

The diagonal law `(17)` and the prime-aperture profile determine the size and location of the full
feature.  They do not control `(23)`.  As `omega` decreases to zero,

```text
Z_omega~1/(2omega zeta(2)),
E_(P_omega)[log d]~1/(2omega).                            (24)
```

Therefore a useful boundary estimate requires `Y_omega` to approach the kernel of `R_omega` at a
quantified rate.  Replacing the signed coisometry by its diagonal norm measure destroys precisely
this angle information.

The rational-gauge countermodel makes the distinction compulsory.  A symmetric orbit insertion
adds an exact logarithmic-source correction and a nonzero contour-jump residue vector while leaving
FE, reality, growth, HT, and aperture unchanged.  A successful continuation map must therefore
augment `(20)` by the corresponding rational residue channel; it cannot factor only through
`P_omega(d)` or a DA source quotient.

## 6. Closed-operator amplification `[PROVED HERE; BRIDGE]`

Let `G:D(G) subset H -> H` be any closed linear operator. Define its channelwise amplification by

```text
D(G^(direct sum))
 ={(f_d):f_d in D(G),
          sum_d(||f_d||^2+||Gf_d||^2)<infinity},          (25)

G^(direct sum)((f_d))=(Gf_d).                            (26)
```

Then the signed coisometry preserves the graph domain and commutes with `G`:

```text
R_omega(D(G^(direct sum))) subset D(G),

G R_omega f=R_omega G^(direct sum)f.                     (27)
```

### Proof

For a finite channel set `F`, linearity gives

```text
G sum_(d in F)epsilon(d)sqrt(P_omega(d))f_d
 =sum_(d in F)epsilon(d)sqrt(P_omega(d))Gf_d.             (28)
```

As `F` increases cofinally, the left inputs converge to `R_omega f` by boundedness of `R_omega`.
The right sides converge to `R_omega G^(direct sum)f` by the graph-norm summability in `(25)` and
the same Cauchy--Schwarz estimate as `(7)`. Closedness of `G` now proves that `R_omega f` belongs to
`D(G)` and yields `(27)`.

This applies to the signed archimedean Stieltjes/Mellin boundary operator as soon as that operator
is identified on a closed graph domain independent of the divisor channel.

`[OPEN CORE]` Construct that concrete closed operator `G_omega`, prove that the coupled feature
`Y_omega` belongs to `D(G_omega^(direct sum))`, and show that the renormalized critical feature
satisfies the pointed projection bound which becomes

```text
||ell_E||<=||ell_pole||=2.                               (29)
```

The arithmetic projection `Pi_omega` and its compatibility with every channel-independent closed
operator are now explicit and unconditional. The missing theorem is the concrete archimedean
domain/renormalization theorem and the quantitative decay of the projected component at the
critical boundary.

## 7. Positive Hilbert--Pólya interpretation

The range of `R_omega^*` is the unique channel direction carrying coherent signed Möbius source
information.  Its orthogonal complement contains channel fluctuations invisible to the scalar
Euler error.  A Hilbert--Pólya realization must transport the distinguished projected component,
not merely the ambient channel norm, into the divisor/trace carrier.

At finite prime cutoff this channel direction has exact scalar differential aperture `pi(N)` when
read out rationally and first-order faithfully.  At the critical prime aperture its required order
obeys the exponential price curve already proved in the corpus.  Thus `(23)` couples the two
positive obligations:

```text
cofinally growing prime state
  + signed pointed source projection
  + orbit-sensitive archimedean continuation
  -> candidate divisor energy bound.                            (27)
```

## 8. Scope and classification

- `[PROVED]` Exact signed coisometry and source projection.
- `[PROVED]` Exact coupled feature norm `(17)`.
- `[PROVED]` Exact cancellation/projection identity `(23)`.
- `[PROVED]` Diagonal channel data alone cannot supply the missing angle estimate.
- `[PROVED]` Every channel-independent closed operator commutes with the signed synthesis on its
  graph-norm direct-sum domain.
- `[NOT PROVED]` The concrete archimedean boundary operator and feature satisfy that domain theorem.
- `[NOT PROVED]` The projected critical feature satisfies `(29)`.
- `[NOT PROVED]` RH is not proved.

The theorem is elementary Hilbert direct-sum algebra applied to the exact Möbius divisor switch.
It is a route bridge, not new scientific knowledge.

## 9. Lean decision

The formal tree does not yet contain the squarefree Gibbs channel, countable Hilbert direct sum,
or the shifted summatory-error feature needed to state `(20)`.  Formalizing an abstract coisometry
without these arithmetic objects would not certify the theorem.  The exact source-marking side is
instead formalized concretely in `XiRationalQuartetGauge.lean`.

## Gates

- [x] signed channel coisometry constructed
- [x] pointed source projection constructed
- [x] coupled feature belongs to the channel Hilbert space
- [x] exact feature norm computed
- [x] exact projection identity proved
- [x] closed-operator channel commutation proved
- [x] rational-gauge marking obligation attached
- [ ] concrete archimedean graph-domain membership
- [ ] critical projected-component estimate
- [ ] four-unit boundary norm
- [ ] RH

## Lean formalization (this sweep, complete and unconditional)

`formal/GaloisForLFunctions/RHTower/VectorSignedChannelCoisometry.lean`,
`.../MobiusCoupledFeatureIncidence.lean` and the certificate
`.../MobiusSignedChannelIncidencePaperCertificate.lean` certify equations `(1)`, `(2)`, `(5)`,
`(6)`, `(8)`, `(9)`, `(10)`, `(15)`, `(16)`, `(17)`, `(21)`, `(23)`, `(24)` and `(25)`--`(27)`:
the signed synthesis is a coisometry, its channel projection is idempotent and self-adjoint, the
coupled feature has the exact norm `‖k‖² + c² log d`, the cancellation law holds, both diagonal
data blow up at the rate `1/(2ω)`, and every closed operator commutes with the signed synthesis on
the graph-norm domain of its channelwise amplification.
