# Bounded sixth source for Euler aperture capacity

- **ID:** ULF-ESAC-FAIL-001
- **Stage:** 5-failed
- **Type:** FALSIFIED completion model
- **Parent:** ULF-ESAC-001

## Claim tested

The complete primitive Euler collision capacity might be the sixth Lyapunov/Sylvester response of
one bounded rank-one source vector on `ell2(Primes x Nat)`.

## Exact killing theorem

ULF-ESAC-001 computes the only possible source coefficients:

```text
c_(p,e)=sqrt(log p)[(e+1)log p]^(3/2)/p^((e+1)/2).
```

Their valuation-one square sum contains `sum_p (log p)^4/p`, hence diverges by Euler's prime
harmonic theorem.  The source vector is not in `ell2`; the sixth boundary is an unbounded
finite-core form.  Any bounded replacement changes the literal Euler diagonal and no longer
recovers the primitive collision weights.

## Strongest positive survivor

The inverse sixth Sylvester regularization exists uniquely and is positive trace class.  Its
matrix is the order-six Gamma Gram `C`, and its trace is exactly the complete primitive collision
budget.  Noncompact source charge and nuclear observed capacity are therefore an exact pair.

## New insight

Completion cannot be modeled by bounded-generator transport.  It must act on singular boundary
forms and compare their nuclear inverse regularizations.  Together with ULF-PHFI-001, this removes
both bounded-source and bounded-multiplicative completion classes.

## Status

Dependency-closed paper proof in ULF-ESAC-001.  Lean formalization deferred because current pass is
Lean-read-only.
