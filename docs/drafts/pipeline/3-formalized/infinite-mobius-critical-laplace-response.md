# Critical Laplace response of the all-prime Möbius channel

- **ID:** `infinite-mobius-critical-laplace-response`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / RH source-chain bridge
- **Statement:** The exact all-prime signed Möbius Laplace multiplier has the residue-normalized
  critical limit
  \[
  \frac{\tau_\sigma(x)}{\sigma-1}\longrightarrow
  \frac{\zeta(2)}{\zeta(1+\pi x)},\qquad x>0,
  \]
  and the same limit holds in every positive causal Laplace coordinate of every causal
  \(L^2\) input.

## Goal

Close the arithmetic critical-distributional-limit part of the four-unit pole-to-divisor route.
The theorem must use only the explicit all-prime Möbius channel and the residue of zeta at one; it
must not use Xi divisor data, zero locations, Weil positivity, or an RH-equivalent source sign.

## Theorem

For `sigma > 1` and `x > 0`, the existing exact multiplier law is

\[
\tau_\sigma(x)
=\frac{\zeta(2\sigma)}{\zeta(\sigma)\zeta(\sigma+\pi x)}.
\]

Since

\[
(\sigma-1)\zeta(\sigma)\to1,
\quad
\zeta(2\sigma)\to\zeta(2),
\quad
\zeta(\sigma+\pi x)\to\zeta(1+\pi x)\ne0,
\]

division gives

\[
\frac{\tau_\sigma(x)}{\sigma-1}
\longrightarrow
\frac{\zeta(2)}{\zeta(1+\pi x)}
\qquad(\sigma\to1+).
\]

If `f` is causally supported, the exact identity

\[
\langle w_x,T_\sigma f\rangle
=\tau_\sigma(x)\langle w_x,f\rangle
\]

therefore yields the unconditional weak boundary response

\[
\frac{\langle w_x,T_\sigma f\rangle}{\sigma-1}
\longrightarrow
\frac{\zeta(2)}{\zeta(1+\pi x)}\langle w_x,f\rangle.
\]

## Proof-chain contribution

The source side of the four-unit route now factors as

```text
exact signed all-prime causal shift
  -> exact reciprocal-zeta Laplace multiplier
  -> explicit critical weak response in every causal Laplace coordinate
  -> [OPEN] charged archimedean graph continuation and nonexpansive pole-to-divisor transfer
  -> four-unit divisor-energy bound
  -> RH.
```

Thus the arithmetic critical limit is no longer part of the open core. The remaining theorem is
operator-valued and archimedean: promote the coordinatewise causal response to the common doubled
charged graph and prove the source-specific nonexpansive continuation retaining contour-jump
residues.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/InfiniteMobiusCriticalLaplaceResponse.lean`

Declarations:

- `tendsto_infiniteMobiusLaplaceMultiplier_div_sub_one`;
- `tendsto_causalLaplacePairing_infiniteMobiusShiftAverage_div_sub_one`.

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

Direct target build passes. Both declarations have only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1 in-progress: source-pure target and proof route identified
- [x] 1 → 2 fully-proven: residue calculation and weak-response proof complete
- [x] 2 → 3 formalized: both Lean theorems compile and are umbrella-wired
- [ ] 3 → 4 publication-ready: integrate into the charged-continuation paper after the operator
  continuation theorem is settled

## Log

- 2026-07-13 — exact multiplier residue and causal-coordinate response formalized and wired into
  the RHTower umbrella.
