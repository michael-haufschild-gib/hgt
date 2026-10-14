# JAS window chain exclusion cannot run on a shrinking zero-free region

## Conjecture (cycle 211)

Level-one window positivity (`JasWindowPositivity 1 N₀`, log-weight Bernoulli tests on the prime
windows `(n, n²]`) excludes off-line chains unconditionally. The Vinogradov–Korobov zero-free region
(`exists_xiZero_re_le_vinogradovKorobov`) would replace the quasi-RH input of
`one_add_sSup_le_of_jasWindowPositivity_of_chain`.

If true, RH would follow from level-one positivity on two sparse families (windows on
`(2^{2^k}, 2^{2^{k+1}}]` and constant vectors at dyadic scales). No separate half-plane producer
would be needed.

## Verdict: FALSE for the window mechanism (open as a bare statement)

The negative-test lemma `re_tsum_jasLogWeightValue_neg` has no zero-free hypothesis. The half-plane
enters only through the bulk condition `hbulk`. This condition requires `‖S(ξ − q̂)‖ ≤ 99` for every
zero `q` with `1 < |Im q − γ| ≤ T₀`, where `S` is the log-weight window prime sum. That bound comes
from the uniform shifted Chebyshev estimate, whose error is
`A^{σ₁ − (1 − Re z)} log²(A + |Im z| + 9)`.

**Obstruction (bulk resonance).** Write `ε_eff = δS − δt` for the gap between the supremal off-line
offset and the target's offset, and `η(T)` for the width of a zero-free region at height `T`.

- The window sum at `z = ξ − q̂` contains the Perron terms of the zeros `ρ''` at the difference height
  `Im q − γ`.
- Their size relative to the main term is `A^{ε_eff − (1 − Re ρ'')}`.
- Bounding them needs `ε_eff < η(T₀)`, up to a `log² T₀ / log A` loss.

The weight tail above `T₀` forces `log T₀ ≳ τ B^{ε_eff} M`, with `M ≍ log n`. The target must beat the
weights, so `τ M ≳ log γ`. Hence `T₀ ≥ γ` and `η(T₀) ≤ η(γ)`.

Now suppose `sup Re ρ = 1`, which is exactly the case quasi-RH excludes. Then the target lies at
distance at least `η(γ)` from the supremum, so `ε_eff ≥ η(γ) ≥ η(T₀)`. The bulk condition therefore
fails for every zero-free region with `η → 0`. It fails for de la Vallée Poussin, for
Vinogradov–Korobov and for `η = c / log log t` alike.

The Dirichlet alignment of the ~`log γ` zeros within height one of the target is a secondary cost. It
needs a polynomial range of amplification scales, which a VK-limited exponent budget
`E ≲ (log B)^{3/2}` cannot supply.

## Positive survivor

The window mechanism reaches exactly the chains with `sup Re ρ < 1`. In that case
`XiZeroHalfPlaneBound (sup − ½)` holds with `sup − ½ < ½`, and the existing theorem applies. So:

- the half-plane input of the sparse capstone is irreducible for window tests;
- a chain that survives level-one window positivity must reach the line `Re s = 1`.

This follows from `one_add_sSup_le_of_jasWindowPositivity_of_chain` together with
`exists_xiZeroHalfPlaneBound_lt_half_of_not_jasOffLineChain`. No new Lean is needed: the statement is
the existing capstone read with `α = sup − ½`.

**Contrast.** The interval/diagonal-Bochner receiver (`abs_re_sub_half_le_of_jasIntervalProductPositive`)
needs no zero-free input. It bounds the lag function two-sidedly at every scale through coherence on
Huxley windows rather than through Perron. The price is that it needs all scales, with at most
exponentially thin exceptions (MUST-1390).

## Paper status / Lean status

The obstruction is a parameter analysis of the existing proof, not a theorem about `ζ`.
NO POSITIVE SALVAGE beyond the reach statement above, which is already in Lean.
