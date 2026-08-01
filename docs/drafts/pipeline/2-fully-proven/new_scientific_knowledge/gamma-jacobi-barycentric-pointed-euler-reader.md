# Gamma--Jacobi barycentric pointed Euler reader

- **ID:** `gamma-jacobi-barycentric-pointed-euler-reader`
- **Stage:** 2 — fully proved on paper
- **Type:** CONSTRUCTION / CLASSIFICATION / EXACT RH CONNECTOR
- **Scientific status:** `[PAPER-PROVED] [NOVELTY PROVISIONAL] [NOT RH]`
- **Parent:** Route M in `rh-current-frontier-map.md`
- **RH used:** no
- **Computation used:** no

## Claim

Route M's surviving class is nonempty.  On every finite prime packet there is an explicit
edge/fibre-marked, noncyclic pointed reader which:

1. reads the exact Gamma--Jacobi tail loss before scalar contraction;
2. is covariant for completed Euler multiplication;
3. is compatible with restriction to a smaller labelled packet;
4. aggregates accumulated source moments by the proved barycentric law;
5. is odd under centered FE--Schwarz reflection;
6. has a cofinal anchored flatness condition equivalent to RH.

The same proof classifies the nonlinear content: after multiplication by its positive third-moment
mass, every such barycentric packet reader is an additive marked edge current.  Barycentric
normalization preserves zero loci and real signs; it cannot create the missing RH sign.  Thus the
reader construction is genuine, but its terminal flatness premise is exactly RH-bearing.

## 1. Source objects

Let `I` be a finite labelled packet, `p_i` its positive integer scale, `K` a Jacobi aperture, and

```text
b_i = gammaOddJacobiTailBoundaryReadout(K, log p_i),
R_K(i,j) = b_i b_j.
```

For a complex fibre `w`, put

```text
u_i(w) = log(p_i)
  * (p_i^(-conj(w)) - p_i^(-(1-w))),
U_w = diag(u_i(w)).
```

This is functional calculus of the completed Euler clock `D=diag(log p_i)`: on a finite packet,
`U_w` is obtained by applying

```text
x |-> x (exp(-conj(w)x) - exp(-(1-w)x))
```

to `D`.  No zero or divisor is used in the definition.  Define the marked tail orientation

```text
C_(K,w) = U_w R_K - R_K U_w.                            (1)
```

Diagonal multiplication gives the exact edge value

```text
C_(K,w)(i,j) = (u_i(w)-u_j(w)) b_i b_j.                 (2)
```

For prime labels every `b_i` is nonzero.  Hence `(2)` vanishes at a marked ordered edge `i,j`
exactly when the two fibre seam values agree.

## 2. Barycentric pointed reader

For a moment source `m : N -> R` with `m_3 != 0`, let

```text
c(m) = -m_4/m_3.
```

For a marked ordered edge `(i,j)`, define

```text
Phi_(m;i,j)(A) = c(m) A(i,j).                            (3)
```

This is a linear matrix coefficient, not a trace.  If `i != j` and `c(m) != 0`, take
`A=E_ii` and `B=E_ij`.  Then

```text
Phi(AB)=c(m),     Phi(BA)=0,                             (4)
```

so `Phi` is noncyclic.

For a finite marked source packet `F` with isolated moment sequences `m_e`, write
`m_F=sum_e m_e`.  The already proved coefficient law gives

```text
Phi_(m_F;i,j)(A)
 = sum_e [m_e(3)/m_F(3)] Phi_(m_e;i,j)(A).              (5)
```

Thus the actual reader, not only its stored coefficient, obeys exact third-moment barycentric
aggregation.

## 3. Inclusion and completed-Euler compatibility

If `f : I -> J` is an injective relabelling and `A` is a matrix on `J`, restriction is the
submatrix `A[f,f]`.  Directly from `(3)`,

```text
Phi_(m;i,j)(A[f,f]) = Phi_(m;f(i),f(j))(A).              (6)
```

This is the required inclusion compatibility: no trace, partial trace, or fitted extension is
used.

For `D=diag(lambda_i)`, matrix multiplication gives

```text
Phi_(m;i,j)(D A-A D)
  = (lambda_i-lambda_j) Phi_(m;i,j)(A).                 (7)
```

At `lambda_i=log p_i`, `(7)` says the marked reader represents the completed Euler derivation
before any Xi fibre is selected.  Applying it to `(1)` yields

```text
Phi_(m;i,j)(C_(K,w))
 = c(m)(u_i(w)-u_j(w))b_i b_j.                          (8)
```

## 4. Reflection orientation

Centered FE--Schwarz reflection is `w#=1-conj(w)`.  The exact prime-seam law is

```text
u_i(w#)=-u_i(w).
```

Therefore

```text
C_(K,w#)=-C_(K,w),
Phi_(m;i,j)(C_(K,w#))=-Phi_(m;i,j)(C_(K,w)).             (9)
```

This is a same-marked-edge, fibre-pointed orientation law.  Reflection changes the fibre value;
it does not average the two fibres or impose a globally invariant scalar reader.

## 5. Dehomogenization classification

Equation `(5)` has no hidden nonlinear sign mechanism.  Multiply it by `m_F(3)`:

```text
m_F(3) Phi_(m_F;i,j)(A)
 = sum_e m_e(3) Phi_(m_e;i,j)(A)
 = -m_F(4) A(i,j).                                      (10)
```

More generally, for edge masses `mu_e`, values `v_e` in any real vector space, and nonzero
`mu_F=sum_e mu_e`, the barycentric packet reader

```text
B_F = [sum_e mu_e v_e]/mu_F                              (11)
```

satisfies

```text
mu_F B_F = sum_e mu_e v_e.                              (12)
```

Conversely `(12)` forces `(11)`.  Therefore exact weighted-barycentric packet laws are precisely
projectivizations of additive marked currents.  If `mu_F>0`, then for every real linear output
channel `L`,

```text
L(B_F)=0  iff  L(sum_e mu_e v_e)=0,
sign L(B_F)=sign L(sum_e mu_e v_e).                     (13)
```

The normalization can retain orientation already present edgewise, but cannot generate it.

## 6. Exact cofinal connector

Fix any nonempty actual von-Mangoldt aperture `M>0` and any Jacobi aperture `K`.  Then
`c(m_M)<0`, where `m_M(q)` is the finite successor-relative moment.  For the anchored packet
`{2,q}`, with marked edge `(2,q)`, `(8)` and nonvanishing of the two tail coordinates give

```text
Phi(C_(K,w))=0
  iff u_2(w)=u_q(w).                                    (14)
```

Define cofinal pointed flatness to mean: for every Xi-divisor fibre `rho` and every `N`, some
prime `q>max(N,2)` satisfies the left side of `(14)`.  Then

```text
cofinal pointed flatness  iff  RH.                       (15)
```

Proof of the forward direction: `(14)` makes `u_2(rho)` equal to `u_q(rho)` along an unbounded
prime subnet.  In the open critical strip `u_q(rho)->0`, so `u_2(rho)=0`.  The exact first-prime
seam law gives `Re(rho)=1/2`.  This holds for every Xi-divisor fibre.

Proof of the reverse direction: RH gives `Re(rho)=1/2`, hence every seam `u_p(rho)` is zero and
every marked reader value in `(14)` vanishes.

No computation, zero enumeration, estimate, or RH premise enters the equivalence proof.  It is
not an RH proof because no source theorem proves cofinal pointed flatness.

## 7. Hostile conjecture audit

### C1 — pointed noncyclic survivor is empty

**FALSIFIED.**  Equations `(1)`--`(9)` construct it on every finite packet.

### C2 — reader is only an abstract Ward functional

**FALSIFIED.**  Its value `(8)` is on literal Gamma--Jacobi tail loss and literal Euler-clock
functional calculus.  It is not obtained by choosing an arbitrary state or tangent.

### C3 — barycentric aggregation supplies new positivity

**FALSIFIED CLASS-COMPLETELY.**  Equations `(10)`--`(13)` dehomogenize the entire exact
weighted-barycentric class to additive marked currents.  Positive normalization preserves sign.

### C4 — reflection oddness proves the required sign

**FALSIFIED.**  Oddness only relates two reflected fibres.  It does not order either one.

### C5 — cofinal reader flatness is a lower-cost RH theorem

**FALSIFIED.**  Equation `(15)` is an exact target equivalence.  It is a connector and interface
closure, not a source proof.

### C6 — positive Markov mixing can prove flatness

**FALSIFIED by existing corpus.**  Source-faithful positive barycentric transport exists exactly
when the target scalar sign already holds.  A future producer must act on the additive marked
current in `(12)`, not hide it in positive normalization.

## 8. Novelty and literature boundary

Burnol's extended Sonine/co-Poisson theorem supplies continuous evaluation fibres and identifies
the annihilator system, but does not contain `(1)`--`(15)`:
<https://arxiv.org/abs/math/0203120>.  Suzuki's screw-line work gives other necessary and sufficient
RH conditions, not this Gamma--Jacobi/barycentric pointed construction:
<https://arxiv.org/abs/2209.04658>.  Romik's Meixner--Pollaczek expansions concern partial sums of
one fixed Xi target, whereas `(5)` concerns a changing accumulated source:
<https://arxiv.org/abs/1902.06330>.

The generic algebra in `(2)`, `(7)`, and `(11)`--`(13)` is elementary and is not claimed as a new
general theorem.  Provisional project-level novelty is their exact composition with the actual
Gamma--Jacobi tail, von-Mangoldt counterreader normalization, FE--Schwarz seam, and cofinal RH
connector.

## 9. Formalization target

Lean must formalize unconditionally:

- packet restriction compatibility `(6)`;
- completed-Euler covariance `(7)`;
- exact tail orientation entry `(2)` and reflection law `(9)`;
- actual barycentric reader law `(5)` and dehomogenization `(10)`;
- explicit noncyclicity `(4)`;
- seam-difference detection `(14)`;
- cofinal connector `(15)`.

Umbrellas, direct elaboration, axiom audit, lint, and one targeted module build are required.

