# Mass–Xi valuation-one prime quotient

## Status

- Lane: `3-formalized`
- Conjecture: `C33` — proved
- Parent: C32 prime-square boundary residue
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- Lean: `formal/GaloisForLFunctions/RHTower/XiMassValuationOnePrimeQuotient.lean`

## Exact theorem

Define the valuation-one centered prime layer

```text
S₁(a,τ) = ∑' p : Nat.Primes, xiMassCenteredPrimeAtom a τ p.
```

For every legal `1/2<c<a` and every `σ>0`, Lean proves

```text
XiMassBottomPrimeLineBound a c σ
  ↔ (∃ C : ℝ, ∀ u : ℝ, ‖S₁(a,σ+iu)‖ ≤ C)
```

and therefore

```text
RiemannHypothesis
  ↔ (∃ C : ℝ, ∀ u : ℝ, ‖S₁(a,σ+iu)‖ ≤ C).
```

## Proof

C31 gives the exact source identity

```text
full bottom von-Mangoldt integral = S₁ + S₂ + H≥3.
```

C32 supplies a vertical-time-independent norm bound for `S₂`; C31 supplies one for `H≥3`.
Hence `S₂+H≥3` is one uniformly bounded remainder. Triangle inequalities transfer fixed-line
boundedness between the full literal source and `S₁` in both directions. Composition with
`riemannHypothesis_iff_xiMassBottomPrimeLineBound` gives the capstone.

No rearrangement is added in C33: the exact decomposition was already justified by absolute
summability in C31, and both remainder bounds are unconditional Lean theorems.

## New scientific knowledge

The §9.3 obstruction is primitive in Euler valuation. Every non-primitive prime power has now been
removed from the RH-strength quotient: depths at least three form an absolutely summable ideal,
and squares form a bounded boundary-residue layer. Prime squares cannot be used as a hidden
cancellation partner in a future proof.

This replaces the ambiguous phrase “prime source”, previously meaning the full von-Mangoldt source,
by an exact valuation-one object. Any proposed source theorem must now transfer to `S₁`; if it
only controls square or higher-power interactions, it cannot cross the formal frontier.

## Lean declarations

- `RHTower.xiMassValuationOnePrimeLayer`
- `RHTower.XiMassValuationOnePrimeLineBound`
- `RHTower.xiMassBottomPrimeIntegral_eq_valuationOne_add_square_add_high`
- `RHTower.exists_norm_xiMassNonPrimeRemainder_vertical_bound`
- `RHTower.xiMassBottomPrimeLineBound_iff_valuationOnePrimeLineBound`
- `RHTower.riemannHypothesis_iff_xiMassValuationOnePrimeLineBound`

## Verification

- `lake env lean GaloisForLFunctions/RHTower/XiMassValuationOnePrimeQuotient.lean`: PASS
- `lake build GaloisForLFunctions.RHTower.XiMassValuationOnePrimeQuotient`: PASS (`9475/9475`)
- Axiom audit of three capstones: only `propext`, `Classical.choice`, `Quot.sound`
- No `sorry`, `admit`, local axiom, `opaque`, `unsafe`, computation proof, or RH hypothesis
- Wired into `GaloisForLFunctions.RHTower`

## Novelty audit

`[LOCAL-RESEARCH] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

Removing bounded summands from a boundedness proposition is elementary. Novel content is the
dependency-closed application to the exact mass–Xi Euler-valuation filtration, yielding a literal
valuation-one RH equivalence. This exact reduction was not found in the audited route corpus;
external priority remains unverified.
