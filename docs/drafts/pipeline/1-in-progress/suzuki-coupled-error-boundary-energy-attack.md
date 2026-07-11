# Suzuki coupled-error boundary-energy attack

- **ID:** `suzuki-coupled-error-boundary-energy-attack`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE; RH-BEARING DIRECT HILBERT--POLYA ATTACK]`
- **Source:** `../2-fully-proven/not_new_scientific_knowledge/infinitesimal-euler-leakage-cauchy-energy-threshold.md`;
  `../2-fully-proven/not_new_scientific_knowledge/suzuki-tail-is-exact-summatory-error-transform.md`;
  `../2-fully-proven/not_new_scientific_knowledge/shifted-euler-error-floor-mobius-tail-coupling.md`
- **Target:** Prove directly from the completed Euler--Gamma source that the first-order
  anti-causal profile `ell_E` satisfies

  ```text
  integral_0^infinity |ell_E(t)|^2 dt <= 4.                 (1)
  ```

  The existing positive Cauchy-energy theorem then proves RH.

## 1. Exact coupled arithmetic source

For `omega>0`, put

```text
c_omega(n)
 =n^omega product_(p|n)(1-p^(-2omega)),

A_omega(X)=sum_(n<=X)c_omega(n),

M_omega(X)
 =X^(1+omega)/((1+omega)zeta(1+2omega)),

E_omega(X)=A_omega(X)-M_omega(X).                         (2)
```

The source identity already proved in the corpus is

```text
h_omega^(1)(x)
 =x^(-1) integral_((0,x])
    g_omega^(1)(t/x)dE_omega(t).                          (3)
```

The two terms of the exact arithmetic decomposition are

```text
E_omega(X)
 =sum_(d<=X)mu(d)d^(-omega)R_omega(X/d)
  -X^(1+omega)/(1+omega)
    sum_(d>X)mu(d)d^(-1-2omega),                         (4)

R_omega(Y)
 =sum_(m<=Y)m^omega-Y^(1+omega)/(1+omega).
```

They are not to be estimated separately.  Their coupling is the source constraint.

## 2. Critical derivative law `[PROVED HERE; BRIDGE]`

Let

```text
psi(X)=sum_(n<=X)Lambda(n).
```

At every fixed `X>=1`, the right derivative at `omega=0` is

```text
partial_omega E_omega(X)|_(0+)
 =2(psi(X)-X).                                            (5)
```

### Proof

For fixed `X`, the sum defining `A_omega(X)` is finite.  The coefficient theorem gives

```text
partial_omega c_omega(n)|_0=2Lambda(n),
```

including the value zero at `n=1`.  Hence

```text
partial_omega A_omega(X)|_0=2psi(X).                      (6)
```

The Laurent expansion of zeta at one gives

```text
1/zeta(1+2omega)=2omega+O(omega^2).                       (7)
```

Since

```text
X^(1+omega)/(1+omega)=X+O_X(omega),                       (8)
```

equations `(7)`--`(8)` imply

```text
partial_omega M_omega(X)|_(0+)=2X.                        (9)
```

Subtracting `(9)` from `(6)` proves `(5)`.

This is a coordinate bridge, not an RH advance by itself: pointwise or mean-square control of
`psi(X)-X` at the critical exponent is classically RH-bearing.

## 3. Candidate mechanisms

### Candidate A: pointed Nyman projection

`[CONJECTURE]` After logarithmic change of variables and distributional differentiation of `(3)`
at `omega=0`, there are a fixed vector `v_arch` of squared norm `4`, a Hilbert space `H_src`, and
a source-defined orthogonal projection `P_src` such that

```text
ell_E=P_src v_arch.                                       (10)
```

Then `(1)` follows from projection contractivity.  The projection must preserve the marked
Möbius/floor coupling in `(4)`; an abstract unitary image or an unpointed Nyman closure is
insufficient.

### Candidate B: completed Hardy sum rule

`[CONJECTURE]` The second-order Toeplitz curvature has a boundary sum rule

```text
C_E(0,0)+B_causal=B_arch,                                 (11)
```

where `B_causal>=0` and `B_arch=4` are constructed before a divisor expansion.  Equation `(11)`
would give `(1)`.  The generic self-dual-quartet counterexample proves that `(11)` must use the
exact Euler coefficients, not only FE symmetry and boundary unimodularity.

### Candidate C: completed renewal contraction

`[CONJECTURE]` The two summands in `(4)`, after applying the signed archimedean Stieltjes kernel,
are the input and boundary counterterm of one contractive renewal operator.  Its defect vector is
`ell_E`, and the renewal input has squared norm `4`.

## 4. Mandatory attacks

1. **Distributional seam.** At `omega=0`, the Mellin kernel contains the identity mass at `x=1`.
   Differentiating `(3)` termwise is invalid until the delta contribution and the derivative of
   `g_omega^(1)` are combined.
2. **Nyman circularity.** If `(10)` is merely the classical Nyman--Beurling projection onto the
   full zeta-generated closure, proving that the target lies in the range is RH.  The projection
   must follow from an unconditional source orthogonality or a smaller closed range.
3. **Boundary evaluation.** Toeplitz contractivity controls operator norm but not the corner
   `C_E(0,0)`; the one-layer model makes the corner unbounded.  Any proof of `(11)` needs a genuine
   trace or reproducing-kernel domain theorem.
4. **Separate estimates.** Absolute values in `(4)` stop at `X^(1-omega)` and destroy the required
   cancellation.
5. **Divisor reconstruction.** Expanding `ell_E` into Xi-zero residue modes proves the implication
   from `(1)` to RH but cannot prove `(1)`.

## 5. Open core

`[OPEN CORE]` Construct the critical distributional limit of `(3)` as one closed Hilbert-space
operator on the coupled pair `(4)`.  Prove either the pointed projection identity `(10)` or the
source sum rule `(11)` without using a zero-free half-plane beyond `Re s>1`, an RH-equivalent
Nyman closure statement, or a divisor expansion.

Only after this operator is constructed is there a legitimate Lean target.  Formalizing
`(1) -> RH` with `(1)` as a hypothesis would be a wrapper around the existing energy criterion.

## Gates

- [x] exact RH-bearing norm target fixed
- [x] coupled floor/Mobius source fixed
- [x] critical derivative law `(5)` proved
- [ ] distributional critical limit of the completed transform
- [ ] pointed projection, sum rule, or renewal contraction
- [ ] unconditional boundary norm `(1)`
- [ ] end-to-end Lean proof of RH
