# Böttcher Prüfer Xi multiplicity character

- **ID:** `bottcher-pruefer-xi-multiplicity-character`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]`, `[FORMALIZATION]`, not new scientific knowledge
- **Lean:** `formal/GaloisForLFunctions/RHTower/BottcherPrueferXiCharge.lean`
- **Route:** `../../1-in-progress/bottcher-pruefer-sem-monodromy-rh.md`

## Statement

Let `zeta_n=exp(2*pi*i/2^n)` be the named Böttcher Prüfer multiplier, whose exact order `2^n` is
already formalized.  For every natural number `m`,

```text
(forall n, zeta_n^m=1) <-> m=0.
```

Consequently, if `m` is the local Xi order at `rho`, the full character is trivial exactly when
that order is zero.  Lean proves the endpoint

```text
RH <->
  forall rho in rightHalf, xi rho=0 ->
    forall n, xiBottcherPrueferCharge rho n=1.
```

## Scope

This is a mechanically exact pairing of two existing objects.  It does not prove that the
completed SEM source canonically couples to Böttcher monodromy or that the resulting character is
trivial.  It is not new scientific knowledge.
