# Drifting periodic primitives have no totally ramified values

- **ID:** `drifting-periodic-primitive-ramification-exclusion`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; primitive ramification
- **Statement:** A primitive of a periodic entire function with nonzero additive period drift has no totally ramified finite value.

## Theorem

Let `W` be a nonconstant entire function. Suppose there are nonzero constants `T,C` such that

`W(z+T)=W(z)+C.`

Then `W` has no totally ramified finite value.

## Proof

Differentiation gives

`W'(z+T)=W'(z)`.

Assume that `a` is a totally ramified value of `W`. For every integer `n`, the value

`a+nC`

is also totally ramified. Indeed, if `W(z)=a+nC`, then

`W(z-nT)=a`,

so `W'(z-nT)=0`; periodicity of `W'` gives `W'(z)=0`.

The values `a+nC` are pairwise distinct. This produces infinitely many totally ramified finite values, contradicting the Nevanlinna ramification theorem, according to which a nonconstant entire function has at most two totally ramified finite values. Therefore no such `a` exists.

## Autonomous first-order corollary

Let `w` be a transcendental entire autonomous first-order DA function and let `W'=w`. The Briot--Bouquet classification gives

`w(z)=L(exp(az))`

for a nonconstant Laurent polynomial `L` and `a!=0`. With `T=2 pi i/a`, integration gives

`W(z)=c_0 z+M(exp(az))`,

where `c_0` is the constant Laurent coefficient of `L`. Hence

`W(z+T)-W(z)=c_0 T.`

If `c_0=0`, then `W` is algebraic over `C(exp(az))`, and `exp(az)` is algebraic over `C(w)`; thus `W` is algebraic over the derivative field and its primitive defect is zero.

If the primitive defect is one, necessarily `c_0!=0`. The theorem applies and shows that `W` has no totally ramified finite value.

Consequently an autonomous first-order entire derivative cannot realize the quadratic matching residue

`W=a+g^2`

with an entire function `g` and primitive defect one.

## Parent-theory verdict

The proof is a direct application of quasi-periodic drift and the classical Nevanlinna ramification bound. It is useful boundary closure, not new scientific knowledge.

## Gates

- [x] Complete proof.
- [x] Autonomous first-order primitive-defect dichotomy.
- [x] Quadratic matching consequence.
- [x] Anti-theatre gate; bridge verdict.

## Primary references

1. Classical Nevanlinna second main theorem with ramification.
2. Classical Briot--Bouquet classification, as recorded in A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95.

