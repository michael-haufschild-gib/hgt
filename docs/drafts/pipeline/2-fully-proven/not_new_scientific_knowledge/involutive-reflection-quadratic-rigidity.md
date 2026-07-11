# Involutive-reflection quadratic rigidity

- **ID:** `involutive-reflection-quadratic-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; primitive ramification
- **Statement:** An affine reflection constraint on a finite-order entire function forces every quadratic entire inner factor to be first-order DA.

## Theorem

Let `sigma(z)=b-z` be an affine involution and let `W` be an entire function of finite order satisfying

`W(sigma(z))=C-W(z)`

for a constant `C`. If

`W(z)=a+g(z)^2`

with `g` entire, then `g` has differential order at most one.

## Proof

The function `g` has finite order. The reflection relation gives

`g(sigma(z))^2+g(z)^2=C-2a.`

If `C-2a=0`, factorization over `C` shows that one of

`g o sigma-i g`,

`g o sigma+i g`

vanishes identically. Thus `g o sigma=+- i g`. Applying the involution twice gives `g=-g`, contradicting nonconstancy.

Hence `D=C-2a!=0`. Put

`A=g o sigma-i g`,

`B=g o sigma+i g`.

Then `AB=D`. Both factors are zero-free entire functions of finite order. Hadamard factorization gives a polynomial `S` and nonzero constants `c,d` such that

`A=c exp(S)`,

`B=d exp(-S)`.

Solving for `g` expresses it as a Laurent polynomial in the hyperexponential generator `E=exp(S)`. Since `E'=S'E`, the function `g` satisfies a first-order ADE.

Therefore no genuinely order-two quadratic inner factor is compatible with the reflection constraint.

## Nonautonomous example

The first-order entire DA function

`w(z)=z sin z`

has the primitive

`W(z)=sin z-z cos z`,

which is odd. Taking `sigma(z)=-z` and `C=0` proves that no factorization

`W=a+g^2`

can have an order-two entire inner `g`.

## Parent-theory verdict

The proof is a difference-of-squares application of Hadamard factorization. It is useful symmetry-side boundary closure, not new scientific knowledge.

## Gates

- [x] Complete proof.
- [x] Zero and nonzero reflection constants classified.
- [x] `z sin z` derivative example excluded.
- [x] Anti-theatre gate; bridge verdict.

## Primary reference

1. Classical Hadamard factorization theorem for finite-order entire functions.

