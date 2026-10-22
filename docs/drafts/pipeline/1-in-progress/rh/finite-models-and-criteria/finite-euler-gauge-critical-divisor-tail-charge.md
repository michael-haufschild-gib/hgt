# Finite-Euler-gauge critical-divisor tail-charge law

- **ID:** `finite-euler-gauge-critical-divisor-tail-charge`
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE / GENERAL HT LAW / RH ROUTE CONSTRAINT
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY UNVERIFIED] [SIGNIFICANCE UNDER ATTACK]`

## Constraint

Let

```text
Omega = product_(p prime) S^1
```

be the compact prime-phase torus.  A phase `chi` determines the Helson Euler product

```text
Z_chi(s) = product_p (1-chi(p)p^(-s))^(-1),   Re(s)>1.
```

For a globally meromorphic phase, write `Delta(chi)` for the signed divisor of `Z_chi` in the
open critical strip

```text
S = {s : 0 < Re(s) < 1}.
```

The question is whether finite-prime product data can constrain `Delta(chi)`.

## Theorem

### Finite-gauge invariance

If `chi` and `psi` differ on a finite prime set `P`, then

```text
Z_psi(s) / Z_chi(s)
  = product_(p in P) (1-chi(p)p^(-s))/(1-psi(p)p^(-s)).
```

For `Re(s)>0`, every numerator and denominator is nonzero because

```text
abs(chi(p)p^(-s)) = abs(psi(p)p^(-s)) = p^(-Re(s)) < 1.
```

The finite factor is therefore a holomorphic unit on `Re(s)>0`.  Global meromorphic
continuability is invariant under finite prime modification, and

```text
Delta(chi) = Delta(psi).
```

The possible divisor introduced by a finite Euler gauge is confined exactly to the barrier line
`Re(s)=0`.

### Dense divisor fibers

`[CLASSICAL INPUT]` Andersson's Helson Mittag--Leffler theorem with `U=C` realizes every locally
finite signed divisor in `S`.  Fix such a divisor `D` and choose one phase `chi_D` with
`Delta(chi_D)=D`.  Every finite modification of `chi_D` has the same critical-strip divisor.
Finite modifications of any point are dense in the product topology.  Hence

```text
M_D = {chi : Z_chi is globally meromorphic and Delta(chi)=D}
```

is dense in `Omega`.  Since the globally meromorphic stratum is Haar-null, every `M_D` is
Haar-null.  Each `M_D` contains a countable dense orbit obtained by multiplying finitely many
prime phases by roots of unity.

Let `bottom` denote noncontinuability and define the extended critical-divisor charge

```text
Delta_bar : Omega -> Div(S) disjoint_union {bottom}.
```

The `bottom` fiber is dense and conull; every divisor fiber is dense and null.

### Indiscrete charge quotient

Give the range of `Delta_bar` the quotient topology.  Every fiber is dense.  If a nonempty proper
subset of the range had open inverse image, choose a charge outside it.  The dense fiber of that
charge would have to meet the nonempty open inverse image, contradicting disjointness.  Therefore

```text
quotient topology of Delta_bar = indiscrete topology.
```

Equivalently, every continuous finite-prime readout into a `T0` space that depends only on the
critical divisor is constant.  The charge map is nowhere continuous for every separated topology
that distinguishes two charges.

## General HT law

The preceding argument does not depend on special identities of zeta.  Let a product carrier
`product_i X_i` have dense finite-modification orbits, and let an analytic invariant be unchanged
by finite local gauges because their divisors are confined to a barrier disjoint from the region
being read.  Then every nonempty invariant fiber is dense and its quotient topology is
indiscrete.  If every invariant value is realizable, the carrier decomposes into a surjective
family of mutually dense tail-charge strata.

> **Finite-gauge tail-charge law.**  A continuation invariant protected from every finite local
> gauge is necessarily a singular tail charge: it cannot be continuously extracted from the
> product inverse limit of finite chambers.

This is a constraint, not a flow.  The invariant is fixed along dense gauge orbits and becomes
visible only after adding a non-product gluing or boundary datum.

## Positive RH necessity

The critical-strip divisor of a Helson Euler product is completely unconstrained in every finite
prime cylinder.  Therefore an RH-capable carrier must do all of the following:

1. retain the critical divisor as a singular tail-germ charge rather than a continuous product
   observable;
2. distinguish the positive Euler phase from the other dense realizations of every divisor;
3. couple that pointing to the scale-one functional equation and the archimedean factor.

Thus the missing structure is not more finite-prime resolution.  It is a polarized continuation
seam that links the Euler tail charge to reflection.

## Proof attacks

1. **Parent-topology attack.**  Dense finite-modification orbits and indiscrete orbit quotients are
   standard.  They are bridges, not new scientific knowledge by themselves.
2. **Finite-factor attack.**  The unit calculation fails on `Re(s)=0`; this is the sharp barrier.
   The theorem deliberately concerns the open strip `0<Re(s)<1`.
3. **Continuation attack.**  Finite modification preserves global meromorphic continuation in both
   directions because the ratio is globally meromorphic and invertible as a meromorphic function.
4. **Divisor attack.**  Andersson is used only for nonemptiness of each fiber.  Density follows
   from exact finite-gauge invariance and does not require prescribing initial prime phases in his
   construction.
5. **Novelty attack.**  The proof is short once the ingredients are juxtaposed.  Scientific novelty
   can lie only in the exact critical-divisor tail-charge geometry and the resulting route
   constraint, not in any individual topological or analytic lemma.
6. **RH boundary.**  The theorem does not constrain the divisor at the positive phase without the
   functional equation.  It proves that such a constraint cannot come from continuous finite-prime
   product data alone.

## Gates

- [x] exact finite-Euler ratio and barrier line identified
- [x] complete paper proof of critical-strip divisor invariance
- [x] complete paper proof that every realizable divisor fiber is dense
- [x] Andersson gives surjectivity onto all locally finite signed critical-strip divisors
- [x] complete paper proof of the indiscrete charge quotient
- [ ] general dense-fiber and indiscrete-quotient bridge formalized unconditionally
- [ ] finite Euler unit calculation formalized on `Re(s)>0`
- [ ] parent-theory and literature audit
- [ ] dual novelty/significance gate

## Primary literature

- J. Andersson, *Mittag-Leffler type theorems for Helson zeta-functions*, arXiv:2408.15713,
  Theorem 5.
- K. Seip, *Universality and distribution of zeros and poles of some zeta functions*,
  J. Anal. Math. 141 (2020).

