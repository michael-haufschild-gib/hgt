# Mixed-valuation quintic Fourier coupling

- **ID:** biscale-mixed-valuation-quintic-1810
- **Stage:** 3-formalized
- **Type:** THEOREM (BRIDGE; no external novelty claim)
- **Parent:** [full field programme](../1-in-progress/biscale-field-development-1810.md), items 3–5
- **Statement:** At an actual factorial period, an explicit fifth translated-moment Fourier coefficient equals `P^5 Y_d^3 Y_e^2` when `d=2^k p`, `e=2^(k+s+1)q`, and `p,q` are odd positive integers.

## Exact formulation

Take natural `k,s,p₀,q₀,n`, put `p=2p₀+1`, `q=2q₀+1`, `d=2^k p`, `e=2^(k+s+1)q`, `N=max(d,e)+n`, and `P=N!`. The weights `c : ℕ → ℝ` are arbitrary actual divisor-sieve weights; `Y_j=selbergMultiplesCoord N c j`.

Let `u=(u₁,u₂,u₃)` be the already-proved `valuationTriple N k p`. Let `r=P/e` as an element of `ℤ/Pℤ`, and `a=2^(s+1)q-1`. The five frequencies are `(u₁,u₂,u₃,-r,-ar)`. The real part of the unnormalized Fourier transform in all five lag variables of the literal period-averaged translated fifth moment is exactly `P^5 Y_d^3 Y_e^2`.

## Dependency-closed proof

Both `d,e` lie in `[1,N]`, hence divide `P`. The existing primitive-triple theorem gives `ord(u_i)=d` and `u₁+u₂+u₃=P/2^k`.

Write `A=2^(s+1)q`. It is positive and even. Thus `a=A-1` is odd. Also any common divisor of `q` and `a` divides both `A` and `A-1`, hence is one. Consequently `gcd(a,2^(k+s+1)q)=1`. Since `ord(r)=e`, multiplication by `a` preserves this exact order: `ord(ar)=e`.

Write `P=e t`. Because `e=2^k A`, we have `P/2^k=A t`. The pair sum is `r+ar=(1+a)t=A t=P/2^k`. Therefore the five frequencies sum to zero. Negation preserves order, so their coordinate product is exactly `Y_d^3 Y_e^2`.

`momentDFT_sieve` applies to the actual cyclic signal and yields the factor `P^5`. `translatedMoment_complex_eq` identifies that cyclic average with the literal real divisor-sieve observation. Taking real parts gives the stated equality without any remaining assumption.

If two signals additionally have the same higher-coordinate square, then equality of this readout is equivalent to equality of their lower-coordinate cubes unless the common higher coordinate is zero. Real cubes are injective. This algebraic alternative will be expressed as an unconditional equivalence, including the zero case.

## Attack and novelty audit

- Zero higher coordinate is a genuine obstruction: the readout then vanishes independently of the lower coordinate. Retain this branch in the exact equivalence.
- Primitive order is essential: merely writing a five-term zero sum would not isolate the asserted two coordinates. The coprimality argument above supplies it.
- The entire fifth Fourier transform is a readout, not one raw lag measurement. No measurement-complexity claim follows.
- **BRIDGE:** moment Fourier factorization and general six-deck reconstruction have classical antecedents. This component supplies an explicit cross-valuation product needed for the requested actual-sieve classification; no external originality claim is made.
- Corpus query `mixed valuation quintic moment recover lower sign` returned the existing within-block sixth result, but no exact mixed-quintic candidate among its inventories. Snapshot coverage and unmeasured semantic coverage prohibit a global absence claim.

## Gates

- [x] Exact concrete statement and proof with no open mathematical dependency.
- [x] Named-source Lean audit: `lake --old env lean -j 1 GaloisForLFunctions/BiScaleUncertainty/MixedValuationQuintic.lean`, exit 0, no diagnostics; artifact-producing source audit also exit 0.
- [x] All four public theorems have no mathematical premise binders. `#print axioms` in `/tmp/biscale-component-api-audit.lean` reports only `propext`, `Classical.choice`, and `Quot.sound`; no added axiom or proof placeholder.
- [x] Leaf wired into `GaloisForLFunctions.BiScaleUncertainty` without compiling the umbrella.
- [ ] Corpus index and formal lint checked for the completed component batch.

No publication task is part of this card.
