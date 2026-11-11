# Discriminants before and after folding the zero symmetry

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/fable.md`, §§10.3(F), 10.5(7).
- **Question:** Which information about conjugation survives the discriminant of
  the full, symmetry-paired Jensen equation, uniformly in degree?

## Target

For the centered Jensen sections `R_d(Ξ)`, prove that the non-real root count
is divisible by four. Identify the discriminant sign lost by retaining both
members of each `z ↦ −z` pair, and recover the sharper invariant on the folded
equation. Connect the resulting counts to the entire off-line divisor through
the existing monotone Jensen exhaustion. No assumption of RH or simplicity.

## Mechanism

Parity gives `R_d(−z) = (−1)^d R_d(z)`. The theta-integral coefficients exclude
nonzero purely imaginary roots. Conjugation and negation therefore partition
non-real roots, with multiplicity, into free four-point orbits.

For monic `Q` of degree `n`,
`disc(Q(X²)) = 4^n (−1)^n Q(0) disc(Q)²` and
`disc(X Q(X²)) = 4^n (−1)^n Q(0)³ disc(Q)²`.
These formulas include degree zero and repeated roots.

Write `μ_k = ∫ Φ(x)x^k dx` and normalize `P_d=R_d/μ₀`. Evenness of `Φ`
gives `μ_(2k+1)=0`. The two quotient equations have coefficients

```
E_n(T) = Σ_(k=0)^n (−1)^k choose(2n,2k) μ_(2k)/μ₀ · T^(n−k),
O_n(T) = Σ_(k=0)^n (−1)^k choose(2n+1,2k) μ_(2k)/μ₀ · T^(n−k).
```

Thus `P_(2n)=E_n(X²)` and `P_(2n+1)=X O_n(X²)`. Strict positivity of
the even moments gives

```
disc(P_(2n))   = 4^n (μ_(2n)/μ₀) · disc(E_n)²,
disc(P_(2n+1)) = 4^n ((2n+1)μ_(2n)/μ₀)³ · disc(O_n)².
```

The full discriminants are nonnegative; their vanishing is exactly a collision
in the quotient. Their sign does not record conjugation parity in the quotient.
These specializations remain proof obligations until checked in Lean.

## Proof obligations

- Exact arbitrary-degree discriminant identities, including degree zero.
- Imaginary-axis exclusion for every centered Jensen degree.
- Multiplicity-preserving orbit decomposition and folded count.
- Passage to the infinite ξ divisor, reusing `JensenCountsOffLineZeros`.
- Final Lean checks and transitive axiom audit.

## Scope

The centered sections are not all shifted Jensen families. A theorem here
must state that boundary explicitly. It does not decide RH; its positive
content is the precise folded invariant retained after the symmetry quotient.
