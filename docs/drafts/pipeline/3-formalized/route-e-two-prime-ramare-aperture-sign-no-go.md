# Two-prime Ramaré aperture sign no-go

- **ID:** E-IMC-TWO-PRIME-SIGN-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Label:** `[LEAN-PROVED]`
- **Source:** Route E nested-aperture residual after `E-IMC-SCALAR-LOCALIZATION`
- **Statement:** If `p<q<2p` are primes, then the literal Ramaré off-diagonal for designated set
  `{p,q}`, integer cutoff `q`, and Gallagher aperture `W` is an explicit nonzero-frequency sine
  kernel.  Consequently it takes both signs and has linear-in-`W` size at canonical quarter-period
  windows.

## RH chain and route kill
Nested Ramaré residual → hoped-for source-faithful sign/monotone inter-modulus telescope →
half-power Möbius cancellation → Littlewood/RH.  This theorem kills the middle implication:
even the literal Möbius source on the smallest nontrivial prime aperture oscillates with full
linear window scale.  Any surviving Route E proof must use collective many-prime cancellation or a
nonlocal aperture coupling, not aperture nesting plus sign.

## Corpus frontier
- `[CORPUS]` `ramarePrimeOffDiagonal_eq_integerIncidence` retains the exact Möbius signs and Mellin
  pair kernel.
- `[CORPUS]` `ramarePrimeOffDiagonal_nestedAperture` cancels old scalar mass but does not control the
  residual sign.
- `[CORPUS]` `ramareMellinPairKernel_self` evaluates only the diagonal; no distinct two-prime sine
  evaluation or sign classification was found.

## External audit
No matching two-prime aperture law or monotonicity classification was found through August 2026 in
Matomäki–Teräväinen, *On the Möbius function in all short intervals* (arXiv:1911.09076),
Ramaré–Zuniga Alterman, *Möbius function and primes: an identity factory with applications*
(arXiv:2312.05138v3), or *On a Möbius double sum* (arXiv:2603.25961v3).

## Paper proof
Let `δ=log q-log p>0`.  If `1≤n≤q` has a designated divisor, then either `q∣n`, hence
`n=q`, or `p∣n`; writing `n=pk`, the inequalities `0<n≤q<2p` force `k=1`, hence `n=p`.
Thus the Ramaré active set is exactly `{p,q}`.  Each point has one designated prime factor, so both
self-complement coefficients vanish.  Distinct primes are coprime, so each cross-complement
coefficient is one; also `μ(p)μ(q)=1`.  The exact integer-incidence formula therefore leaves the
two ordered kernels `K_W(p,q)+K_W(q,p)`.

The phase product is
`Re(exp(2πiw log p) exp(-2πiw log q)) = cos(2πwδ)`.  For `W≥0`, the fundamental theorem of
calculus on `[-W,W]` gives
`K_W(p,q)=sin(2πWδ)/(πδ)`; symmetry gives the same value for `K_W(q,p)`.  Hence

`ramarePrimeOffDiagonal {p,q} q W = 2 sin(2πWδ)/(πδ)`.

At `W₊=1/(4δ)` the value is `2/(πδ)>0`; at `W₋=3/(4δ)` it is
`-2/(πδ)<0`.  Moreover the normalized values are `8/π` and `-8/(3π)`, so the failure is
linear-scale rather than a negligible boundary effect.  Every dependency is elementary and
unconditional.

## Hostile audit
Verdict: `SURVIVES HOSTILE ATTACK`.  The statement is not an RH consequence or a coefficient-
chosen counterexample: it classifies the literal Möbius/Ramaré observable.  Existing corpus sine
steering and self-kernel results do not imply this two-prime active-set collapse and physical
off-diagonal law.  External audit above found no exact collision.  Its significance is negative but
material: universal sign, monotonicity, and sublinear-window damping of nested-aperture increments
are impossible.

## Lean certificate
- Module: `GaloisForLFunctions.RHTower.Sieve.RouteERamareTwoPrimeApertureSignNoGo`.
- Proved: active-set collapse, exact phase/kernel laws, exact two-prime off-diagonal, exact
  quarter/three-quarter values, and opposite strict signs.
- Audit: direct `lake env lean` passed; module-only `lake build` passed; all public theorems use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Wired into `GaloisForLFunctions.RHTower`; no umbrella build run.

## Gates
- [x] 0 → 1: exact corpus-derived claim and RH-chain effect recorded
- [x] 1 → 2: dependency-closed paper proof and hostile audit
- [x] 2 → 3: exact Lean theorem, target build, axiom audit
- [ ] 3 → 4: publication-ready
