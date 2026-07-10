# Euler horizontal-charge separator

- **ID:** euler-horizontal-charge-separator
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE; NOVELTY UNVERIFIED]`
- **Source:** exact charge decomposition in
  `../2-fully-proven/not_new_scientific_knowledge/horizontal-entry-charge-transfer.md`

## Target

Let `E_zeta` denote the complete von-Mangoldt Euler source together with the archimedean factor and
functional equation. Construct directly from `E_zeta` a locally finite even integer-valued measure
`Omega_E` on the ordinate axis such that, for every bounded interval `I` avoiding zero ordinates at
its endpoints,

```text
Omega_E(I)
  = sum_gamma in I
      (H_gamma^2 - sum_(Im rho=gamma) m_rho^2).           (1)
```

The right side is the off-line cross-charge `O_I`. The construction on the left may not use the
unknown zero divisor, values or derivatives of `xi` at proposed zeros, or a finite Euler head.

The significant theorem sought is not merely (1). Analytic continuation already makes the full
Euler source divisor-faithful. The source construction must also prove a one-sided law, for example

```text
Omega_E(I)=0                                               (2)
```

for a nonempty new class of windows, or an effective bound `Omega_E(I)<2`. Since `Omega_E(I)` is an
even nonnegative integer, the latter also gives (2).

## Why this is the entry constraint

The horizontal-multiplicity excess splits as

```text
horizontal excess = off-line cross-charge + multiplicity excess.
```

A reflected simple pair entering the critical line transfers two units from the first term to the
second. Pair-correlation statistics that see only the sum cannot prevent entry. A source theorem
for `Omega_E` separates the two channels and is therefore the minimal integer obstruction.

This formulation uses neither a height coordinate as the primary object nor a local jet. It is an
all-divisor correlation measure whose proposed left side is built from the complete Euler data.
A bounded interval is only a localization of the measure.

## Candidate construction

On `Re s>1`, the logarithmic Euler source has the pure frequency expansion

```text
-zeta'(s)/zeta(s) = sum_n Lambda(n)n^(-s).
```

The long mean of its two-point product is prime-diagonal because distinct logarithmic frequencies
do not coincide. On the divisor side, a corresponding two-point trace contains:

1. point-diagonal terms, giving `sum m_rho^2`;
2. reflected same-ordinate terms, giving `O_I`;
3. distinct-ordinate terms, killed by the proposed mean.

`[CONJECTURE]` There is an all-place renormalized Plancherel identity across the critical seam whose
prime-diagonal side separates terms 1 and 2 rather than only their sum. Its off-diagonal remainder
is `Omega_E`.

## Fake proof and exact failure

The naive proof says that uniqueness of the frequencies `log n` makes the prime two-point mean
diagonal and therefore forces `Omega_E=0`. This is false. Moving the identity from `Re s>1` to the
critical boundary crosses the zero poles; the individual pole transforms are causal exponential
modes, not orthogonal pure frequencies. Critical-line poles also create a divergent diagonal
mass. Interchanging analytic continuation, boundary limit, and the long mean discards precisely
the residue that could equal `Omega_E`.

Thus the open theorem is a renormalization statement, not prime-log independence by itself.

## Literature and parent-theory audit

- `[SEARCH]` Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh identify reflected
  symmetric-diagonal terms in unconditional Montgomery pair correlation and use them to bound the
  proportion of critical zeros under a thin-box hypothesis.
- `[SEARCH]` Goldston--Lee--Schettler--Suriajaya introduce horizontal multiplicity and show that the
  pair-correlation conjecture implies asymptotically 100 percent simple critical zeros.
- `[SEARCH]` Standard Montgomery pair correlation and long-mean orthogonality determine only
  asymptotic horizontal multiplicity; finite exceptional off-line orbits are invisible at relative
  precision.
- `[BRIDGE]` Krein--Langer negative index and generalized Schur theory already count off-line poles
  when the divisor supplies the carrier.
- `[BRIDGE]` `ChargeMotion.lean` already formalizes homotopy conservation and boundary jumps for
  divisor-fed winding charge; it does not construct the required charge from the Euler source.

No novelty is claimed for horizontal multiplicity, symmetric diagonal terms, the charge algebra,
or source uniqueness. Scientific novelty would begin only with a proved source-side separator and
a noncircular one-sided estimate.

## Falsifiers

1. A construction that first reconstructs the zero divisor and then evaluates (1) is faithful but
   conclusion-fed.
2. A relative/asymptotic formula with error `o(N(I))` cannot exclude one off-line orbit; the
   required absolute error is strictly less than `2`.
3. Any statistic factoring through `C_I-N_I` is collision-blind because that sum is conserved.
4. A bounded-support one-point Weil test cannot isolate the unknown infinite critical-line tail.
5. A finite Euler head cannot work by the formal finite-Euler no-amplification theorem.
6. Bare tempered local factors are insufficient: Helson zeta functions admit essentially
   prescribed zeros without the global zeta functional-equation constraint.

## Gates

- [x] 0 -> 1: exact integer target, collision law, fake proof, literature overlap, and falsifiers
  stated.
- [ ] 1 -> 2: construct `Omega_E` without the divisor and prove an absolute `<2` source bound on a
  nonempty new window or prove a global vanishing theorem.
- [ ] 2 -> 3: formalize the charge measure, source trace, and integer conclusion.
- [ ] 3 -> 4: independent proof and broad scientific-novelty audit.

## Relation to verified-height amplification

For an interval immediately above the Platt--Trudgian prefix, an explicit source estimate

```text
Omega_E(I)<2
```

would exclude every reflected off-line pair in that interval without resolving its horizontal
distance from the line. It would therefore amplify the verified range once the interval endpoints
and source trace are made effective. No such estimate has been proved here.
