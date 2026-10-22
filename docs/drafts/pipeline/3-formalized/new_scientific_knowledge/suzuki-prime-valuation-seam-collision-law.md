# Suzuki prime-valuation seam collision law

- **ID:** `suzuki-prime-valuation-seam-collision-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPrimeValuationSeam.lean`
- **Parent:** `primeLog_linearIndependent` in `RHTower/WeldRateLattice.lean`

## Statement

For a finite-support signed prime-valuation vector `nu`, define logarithmic seam displacement

```text
sigma(nu)=sum_p nu_p log p.
```

Then

```text
sigma(nu)=sigma(mu) iff nu=mu.                            (1)
```

At aperture `a`, right and left descendant locations

```text
x_+(a,nu)=a-sigma(nu),
x_-(a,nu)=-a+sigma(nu)                                   (2)
```

therefore satisfy

```text
x_+(a,nu)=x_+(a,mu) iff nu=mu,
x_-(a,nu)=x_-(a,mu) iff nu=mu,                           (3)

x_+(a,nu)=x_-(a,mu) iff 2a=sigma(nu)+sigma(mu).          (4)
```

Thus every same-end iterated prime-seam collision is equality of complete valuation labels, while
every opposite-end collision lies on one exact affine resonance hyperplane.

## Proof

Existing theorem `primeLog_linearIndependent` proves `Z`-linear independence of the full family
`p -> log p` from unique factorization. Apply its `Finsupp.linearCombination` map to `nu-mu`.
Vanishing of `sigma(nu)-sigma(mu)` forces `nu-mu=0`, proving `(1)`. Equations `(3)` and `(4)` are
then cancellation and linear rearrangement in `R`. `QED`

## RH-route consequence

For positive Laurent transport polynomial

```text
T_a(z)=sum_(p^j<=exp(2a)) (log p)/p^(j/2)(z_p^j+z_p^(-j)),
```

the grade-`k` mass arriving at `nu` is coefficient `[z^nu]T_a^k`, a sum of strictly positive word
weights. The theorem proves that spatial collision does not identify distinct valuation vectors.
After support pruning, any surviving first-arrival coefficient remains a positive subsum. Analytic
existence and convergence of Suzuki's half-log seam expansion remain open and are tracked in
`suzuki-completed-zero-mode-corona-seam-law.md`.

## Formal audit

Lean proves:

- `primeSeamCoordinate_apply`
- `primeSeamCoordinate_injective`
- `primeSeamCoordinate_eq_iff`
- `rightPrimeSeamLocation_eq_iff`
- `leftPrimeSeamLocation_eq_iff`
- `right_eq_leftPrimeSeamLocation_iff`

No `sorry`, `admit`, new axiom, opaque declaration, unsafe declaration, or numerical computation is
used.
