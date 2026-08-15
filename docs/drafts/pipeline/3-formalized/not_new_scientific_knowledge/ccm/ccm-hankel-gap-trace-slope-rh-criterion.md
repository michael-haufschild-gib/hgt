# The CCM residue energy is an initial Hankel gap-trace slope

- **ID:** `ccm-hankel-gap-trace-slope-rh-criterion`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-EQUIVALENT TARGET]`
- **Parent results:** Hilbert--Schmidt norm formula for Hankel kernels and the positive Cauchy-energy
  threshold for off-line Xi zeros
- **Statement:** The unweighted anti-causal residue energy is exactly the negative initial
  derivative of a positive trace-class Hankel gap profile. The Euler pole has profile `4e^(-u)`.
  Consequently RH is equivalent to the completed divisor gap trace having right slope at least
  `-4` at zero.

## 1. Shifted Hankel leakage

Let `ell:(0,infinity)->C` satisfy

```text
integral_0^infinity (1+t)|ell(t)|^2 dt<infinity.          (1)
```

For `u>=0`, define the shifted Hankel operator on `L2(0,infinity)` by

```text
(H_u f)(x)
 =integral_0^infinity ell(u+x+y)f(y)dy.                  (2)
```

Put

```text
F_ell(u)=Tr(H_u^* H_u)=||H_u||_(S_2)^2.                 (3)
```

Then

```text
F_ell(u)
 =integral_0^infinity r |ell(u+r)|^2 dr
 =integral_u^infinity (t-u)|ell(t)|^2 dt,                (4)
```

and `F_ell` is decreasing and convex, with

```text
F_ell'(u+)=-integral_u^infinity |ell(t)|^2 dt.            (5)
```

In particular,

```text
-F_ell'(0+)=||ell||_2^2.                                 (6)
```

### Proof

The Hilbert--Schmidt kernel of `(2)` is `ell(u+x+y)`. Tonelli's theorem and the change of
variables `r=x+y` give

```text
||H_u||_(S_2)^2
 =integral_0^infinity integral_0^infinity
    |ell(u+x+y)|^2 dx dy
 =integral_0^infinity r|ell(u+r)|^2 dr,
```

which is `(4)`. For `h>0`, subtract the two tail integrals:

```text
(F_ell(u+h)-F_ell(u))/h
 =-integral_(u+h)^infinity |ell(t)|^2dt
  -1/h integral_u^(u+h)(t-u)|ell(t)|^2dt.                (7)
```

The second term tends to zero by absolute continuity of the integral, and the first tends to the
right side of `(5)`. The tail integral decreases with `u`, so `F_ell'` increases; hence `F_ell` is
convex. Equation `(6)` is `(5)` at zero.

No boundary value `ell(0)` and no derivative of `ell` is used. The trace slope is therefore a
strictly weaker analytic demand than point evaluation of the Hankel kernel at the corner.

## 2. Finite divisor formula

For a finite right-half divisor

```text
rho_j=1/2+a_j+i gamma_j,       a_j>0,
```

with multiplicities `m_j`, let

```text
ell_E(t)=2 sum_j m_j exp(-(a_j+i gamma_j)t).              (8)
```

Then

```text
F_E(u)
 =4 Re sum_(j,k) m_j m_k
    exp(-(a_j+a_k+i(gamma_j-gamma_k))u)
    /(a_j+a_k+i(gamma_j-gamma_k))^2,                     (9)
```

and

```text
-F_E'(0+)
 =4 sum_(j,k)m_jm_k
   (a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2)
 =||ell_E||_2^2.                                         (10)
```

Every summand in the middle expression of `(10)` is positive, and the diagonal gives

```text
-F_E'(0+)>=2 sum_j m_j^2/a_j.                            (11)
```

### Proof

Insert `(8)` into `(4)`. For

```text
lambda_(j,k)=a_j+a_k+i(gamma_j-gamma_k),
```

the elementary integral

```text
integral_0^infinity r exp(-lambda_(j,k)(u+r))dr
 =exp(-lambda_(j,k)u)/lambda_(j,k)^2                     (12)
```

gives `(9)` after conjugate pairs are combined. Differentiating `(9)`, or applying `(6)`, gives
`(10)`. Retaining the diagonal terms gives `(11)`.

## 3. The incoming Euler-pole trace

The finite-prime completed source has the unique anti-causal pole profile

```text
ell_pole(t)=2 exp(-t/2).                                  (13)
```

Its shifted Hankel operator is rank one, and `(4)` gives

```text
F_pole(u)=4 exp(-u),
F_pole'(0+)=-4.                                          (14)
```

Thus the constant `4` is both the pole energy and the magnitude of the initial decay rate of its
semilocal gap trace.

## 4. Exact RH criterion

For every nontrivial right-half Xi zero,

```text
0<a_j<1/2.                                               (15)
```

If the divisor is nonempty, `(11)` therefore gives

```text
-F_E'(0+)>4.                                             (16)
```

Under RH, `ell_E=0` and `F_E=0`. With the value `+infinity` assigned when the infinite divisor
profile is not in `L2`, one obtains the exact equivalences

```text
RH
 <-> -F_E'(0+)<=4
 <-> F_E'(0+)>=F_pole'(0+)=-4.                           (17)
```

The forward implication is immediate. Conversely, any right-half zero violates the middle and
right inequalities by `(16)`.

## 5. Positive semilocal transport law

The CCM/Connes route can now state the four-unit obligation without evaluating a kernel at a
boundary corner. It must construct the completed gap trace `F_E` from the Euler--Gamma source and
prove the one-sided slope order

```text
F_E'(0+)>=F_pole'(0+).                                   (18)
```

Equivalently, for sufficiently small `u>0`, it is enough to prove the first-order trace inequality

```text
F_E(0)-F_E(u)<=4u+o(u).                                  (19)
```

The carrier in `(18)` is positive and orbit-sensitive:

```text
aperture u
  -> trace-class shifted leakage H_u^*H_u
  -> initial trace loss -F_E'(0+)
  -> full Cauchy residue charge.                         (20)
```

The exact source-side candidate is available from the shifted completed source. Formally let

```text
L_omega=P_- M_(Theta_omega)|H2_+,
D=lim_(omega->0+)omega^(-1)L_omega                      (20a)
```

on a meromorphic graph domain, and let `V_b` be the right-shift isometry on the reflected half-line.
Whenever this limit defines a closed operator and the displayed compressions are Hilbert--Schmidt,
the Paley--Wiener identification makes `D` the Hankel operator with kernel `ell_E(x+y)`, so

```text
D_u=V_(u/2)^* D V_(u/2)                                 (20b)
```

has kernel `ell_E(u+x+y)`. Therefore

```text
F_E(u)=Tr(D_u^*D_u)                                     (20c)
```

as a positive trace, without expanding the Xi divisor. On the Euler half-plane the
infinitesimal symbol defining `D` is the explicit completed source

```text
-2 Xi'/Xi
 =-2/s-2/(s-1)+log(pi)-psi(s/2)
   +2 sum_n Lambda(n)n^(-s).                            (20d)
```

Thus the source formula for the desired trace family is explicit. What remains open for Xi is
load-bearing: close the meromorphic graph of `(20d)`, prove that its shifted compressions define
the trace `(20c)`, establish trace differentiability at zero, and prove the slope order `(18)`.

A symmetric off-line orbit changes `(20)` by an inverse-horizontal amount, so the trace slope
cannot factor through FE, Schwarz symmetry, hypertranscendence, differential aperture, or the
Euler-side Schur multiplier alone.

This is the native positive target for a semilocal Connes construction: transport the incoming
rank-one pole trace through completion while preventing an increase of its initial aperture-loss
rate. It is not enough to bound `F_E(u)` at one positive aperture, because the RH information is
the right derivative at the singular endpoint.

## 6. Relation to the charged continuation graph

The horizontal-charge norm law proves that the meromorphic continuation graph must explicitly
carry `||ell_E||_2^2`. Equation `(6)` identifies the same charge intrinsically as the boundary
trace slope of the shifted leakage family. Hence the two surviving descriptions agree:

```text
residue Cauchy Gram norm
 =inverse-horizontal graph charge
 =negative initial Hankel gap-trace slope.               (21)
```

This makes the required extension more specific. A viable CCM graph must be trace differentiable
at zero aperture on the distinguished Xi vector, and its renormalization must preserve the slope
order `(18)`. Ordinary bounded graph continuity does not imply this endpoint derivative control.

## 7. Scientific classification and Lean decision

The Hilbert--Schmidt identity `(4)` and differentiation formula `(5)` are standard Hankel-operator
calculus. Combined with the already proved Cauchy threshold they give a useful route bridge, not
new scientific knowledge. The new scientific content would be an unconditional arithmetic proof
of `(18)`.

The current Lean tree has neither trace-class Hankel integral operators nor the analytic Xi
residue profile. Formalizing a finite-sum shadow would not certify `(18)`, so no Lean file is
added.

## Gates

- [x] shifted Hankel trace identity
- [x] initial trace-slope/energy identity
- [x] exact Euler-pole trace profile
- [x] RH-equivalent semilocal slope criterion
- [x] compatibility with the inverse-horizontal charged graph
- [ ] close the source-defined infinitesimal leakage graph and construct its shifted traces
- [ ] prove the slope order `(18)`
- [ ] RH

## Lean status

**Formalized unconditionally, 2026-08-15**, in
`formal/GaloisForLFunctions/RHTower/CCMHankelGapTraceSlope.lean`, on the divisor/pole profiles of
`RHTower/CCMShiftCovariantPoleDivisorCapacity.lean` and the Cauchy energy form of
`RHTower/CCMTransverseIndexTraceSlopeCoercivity.lean`.

- `leakDensity`, `tailLeakEnergy`, `hankelGapProfile`, `LeakProfile` — the leakage density, the tail
  energy, the gap profile `F_ell(u) = int_u^infinity (t-u)|ell|^2`, and hypothesis `(1)`.
- **`hankelGapProfile_eq_shift`** — the two forms of `(4)`, related by the measure-preserving
  translation of the half-line.
- **`hankelGapProfile_sub`** — the exact splitting `F(u) - F(k) = (k-u) T(k) + int_(u,k] (t-u)|ell|^2`,
  which is `(7)` in exact form.
- `tailLeakEnergy_sub`, `remainder_nonneg`, **`remainder_le`** — the two bounds on the remainder.
- **`tailLeakEnergy_le_diff_quotient`** — the sandwich `T(k) <= (F(u)-F(k))/(k-u) <= T(u)`.  This
  replaces the card's two-term limit argument by an exact two-sided inequality.
- **`tendsto_tailLeakEnergy_right`** — right continuity of the tail energy, from absolute continuity
  of the integral.
- **`tendsto_diff_quotient_hankelGapProfile`**, **`tendsto_initial_slope`** — equations `(5)`--`(6)`:
  the one-sided derivative of the gap profile is minus the tail energy, and at the origin
  `-F'(0+) = ||ell||_2^2`.  No boundary value `ell(0)` and no derivative of `ell` is used.
- **`hankelGapProfile_antitone`** — the monotonicity assertion of `(4)`.
- `exists_uniform_re_bound`, `integrableOn_one_add_mul_exp_neg`, `norm_divisorPacketProfile_le`,
  **`leakProfile_divisorPacket`**, **`leakProfile_polePacket`** — the two concrete profiles satisfy
  hypothesis `(1)`.
- **`ofReal_leakDensity_divisorPacket`**, `integrableOn_sub_mul_cexp_neg_mul`,
  `tendsto_linear_mul_exp_neg`, **`integral_Ioi_sub_mul_cexp_neg_mul`**,
  **`hankelGapProfile_divisorPacket`** — equations `(8)`, `(12)`, `(9)`: the exact first-moment
  Laplace integral `int_u^infinity (t-u)exp(-b t)dt = exp(-b u)/b^2` for `Re b > 0` (proved by the
  fundamental theorem of calculus with the antiderivative `((u-s)/b - 1/b^2)exp(-b s)`), and the
  closed form of the gap profile of a finite divisor packet.
- **`tendsto_initial_slope_divisorPacket`** — equation `(10)`: the initial trace slope of a finite
  divisor packet is its residue energy, whose Cauchy form and diagonal bound `(11)` are
  `divisorPacketEnergy_eq` and `diagonal_le_divisorPacketEnergy`.
- `tailLeakEnergy_polePacket_zero`, **`tendsto_initial_slope_polePacket`** — equation `(14)`: the
  incoming pole has initial trace slope exactly `-4`.
- **`divisorPacketEnergy_le_four_iff`** — equations `(16)`--`(17)` at the packet level: a right-half
  packet has initial trace loss at most the pole value exactly when it is empty.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized, and imported: the Hilbert--Schmidt norm formula identifying `Tr(H_u^* H_u)` of the
shifted Hankel operator `(2)` with the first-moment tail `(4)` — the card's parent result — and the
identification of the Xi divisor with the packet data, which is what turns the packet criterion
`(16)`--`(17)` into the RH equivalence.  The source-side obligation `(18)`--`(20b)` is the card's own
open gate.
