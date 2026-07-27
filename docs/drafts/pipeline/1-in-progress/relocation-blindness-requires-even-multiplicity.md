# Transverse divisor relocation preserving the ordinate counting measure requires even multiplicity

- **ID:** `relocation-blindness-requires-even-multiplicity`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, elementary) + SCOPE CORRECTION
- **Scientific status:** `[PAPER-PROVED]` `[SCOPE CORRECTION TO AN EXISTING NO-GO]` `[NOT AN RH PROOF]`
- **Corrects the scope of:**
  `2-fully-proven/not_new_scientific_knowledge/positive-density-transverse-divisor-relocation-law.md`
- **Statement:** Any relocation of a functional-equation- and Schwarz-symmetric divisor from the
  critical line to a transverse position, preserving the ordinate counting measure exactly, must
  move zeros of **even** multiplicity. Consequently the blindness demonstrated by the relocation
  law is a statement about divisors with repeated on-line zeros, and says nothing about the
  simple-zero class.

## The elementary reason

Let `D` be a divisor in the `s`-plane invariant under the functional-equation involution
`s |-> 1-s` and under Schwarz conjugation `s |-> conj s`, and let

```text
mu(gamma) = total multiplicity of D at ordinate Im s = gamma.
```

Fix an ordinate `gamma != 0`.

* If every point of `D` at that ordinate lies **on** the critical line, the group orbit of a point
  `1/2 + i gamma` under the two involutions is `{1/2 + i gamma, 1/2 - i gamma}` — one point per
  ordinate. So an on-line zero of multiplicity `m` contributes `mu(gamma) = m`.
* If a point `1/2 + delta + i gamma` with `delta != 0` lies in `D`, its orbit is
  `{1/2 + delta + i gamma, 1/2 - delta + i gamma, 1/2 + delta - i gamma, 1/2 - delta - i gamma}`
  — **two** points at ordinate `gamma`. So an off-line zero of multiplicity `m` contributes
  `2m` to `mu(gamma)`.

Hence, at each ordinate, the contribution of the off-line part of a symmetric divisor is even.
If a relocation carries an entirely on-line divisor to one with an off-line part while preserving
`mu` pointwise, the multiplicity it moves at each affected ordinate must have been even. `∎`

## Verification against the existing construction

The relocation law's own example is exactly this mechanism, made visible by one identity. Its
envelopes are

```text
A_0(w) = cosh(w)^2,
A_a(w) = cosh(w-a) cosh(w+a),
```

and

```text
cosh(w-a) cosh(w+a) = (cosh 2w + cosh 2a)/2,
cosh(w)^2           = (cosh 2w + 1)/2,
```

so that

```text
A_a = A_0 + (cosh(2a) - 1)/2,        F_a = F_0 + ((cosh 2a - 1)/2) * C_beta.     (*)
```

`A_0` has a **double** zero at each `w = i pi (k + 1/2)`; `A_a` splits each of them into the
transverse simple pair `w = ±a + i pi (k + 1/2)`. Ordinates and total multiplicities agree at every
level, which is precisely why the ordinate counting measure is preserved. The construction is
therefore not merely compatible with even multiplicity — it *is* the splitting of a double on-line
zero, and by the theorem above it could not have been anything else.

Identity `(*)` also exhibits the whole relocation as the addition of a positive constant multiple
of the clean carrier `C_beta`, which is a sharper description than "two envelopes".

## What this changes

The relocation law is quoted (correctly, within its scope) as showing that the package

```text
{ functional equation, Schwarz symmetry, exact order one, hypertranscendence,
  ordinate counting measure, differential-translation field class mod DA }
```

is blind to on-line versus off-line placement. The theorem above shows the demonstrated blindness
lives on divisors with repeated on-line zeros. **Adjoining simplicity of the on-line divisor to
that package is not covered by the existing counterexample.**

This is a scope correction, not a refutation: the relocation law's conclusion stands exactly as
stated. What is removed is the tempting over-reading that no invariant in that package can ever
separate the two cases.

## Open question created

> **Q'.** Does a transverse relocation exist inside the class of functional-equation- and
> Schwarz-symmetric entire functions of exact order one with **simple** zeros, preserving the
> ordinate counting measure and the differential-translation field class?

Three honest remarks on `Q'` before anyone invests in it.

1. **It is not a route to RH by itself.** Simplicity of the zeros of `xi` is unproven, so a
   positive answer to "simplicity blocks relocation" cannot be applied to `xi` without first
   proving simple zeros — which is harder than RH is believed to be, not easier.
2. **It may well be answerable negatively and cheaply.** Relaxing "preserve `mu` pointwise" to
   "preserve the asymptotic counting function `N(T)`" restores enough freedom that a simple-zero
   relocation is plausible: one may trade multiplicities between distinct ordinates. Anyone
   attacking `Q'` should first settle which invariant is intended, because the theorem above is
   sharp only for the pointwise version.
3. **Its real value is diagnostic.** If simplicity *does* obstruct relocation, then the pair
   (counting measure, simplicity) is a non-blind invariant, and the corpus's blindness ledger
   acquires its first positive entry. That is worth knowing even though it does not prove RH.

## Gates

- [x] elementary orbit-parity proof
- [x] verified against the existing construction, including the identity `(*)`
- [ ] settle `Q'` for the pointwise counting measure
- [ ] settle `Q'` for the asymptotic counting function
- [x] Lean: the orbit-parity statement for a symmetric finite divisor —
      `formal/GaloisForLFunctions/RHTower/OrbitParityOffLine.lean`, registered in the
      `GaloisForLFunctions.RHTower` umbrella, lint passes, axiom-clean
      (`propext, Classical.choice, Quot.sound`).  Contents: `feSchwarz s = 1 - conj s`, its
      involutivity, `feSchwarz_eq_self_iff : feSchwarz s = s ↔ s.re = 1/2`, and
      `even_sum_of_offCritical` — a `feSchwarz`-stable finite family avoiding the critical line,
      carrying a `feSchwarz`-invariant multiplicity, has **even** total multiplicity.  Proof is the
      explicit two-sided bijection between the `re < 1/2` and `re > 1/2` halves.

## Log

- 2026-07-27 (Claude): derived while auditing the relocation law as a proposed global blindness
  result. The identity `(*)` and the orbit-parity argument were obtained from the card's own
  construction, not recalled.
