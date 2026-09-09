# HB: original physical response equation

Goal: theta cusp → Xi occurrence → complete source → original outgoing
response and physical adjoint residue → Hawking-clock extinction → RH.
RH is open; frontier map is read-only.

Weighted admission of the original causal response is now proved for
`3/2 < Re w < 2`, `Im w != 0`, including its literal physical angular
pairing. The next obligation is to connect that response to the original
radial Green continuation, rather than assume an outgoing joint inverse.

## Proposed bridge

1. Prove the original joint distribution equation against every separated
   smooth compact radial/modular test. Move both radial derivatives and
   the complete modular Laplacian onto the test. Use the existing
   `CoreField.planarTest`, full modular Green identity, and exact native
   core-operator action; modular seams and elliptic charts remain included.
2. Approximate the physical angular test by smooth modular cusp cutoffs
   at scale N. Prove convergence of both test/height and its
   Laplacian/height in the original angular L2 norm. The cutoff transition
   must scale with N, so its hyperbolic first and second derivatives stay
   bounded; a fixed-width transition has growing derivatives.
3. Pass the compact-test equation to the actual physical pairing using
   the proved height norm of the response and complete source. The result
   must retain the original angular eigenvalue and radial coefficient
   `sech(t)^2`, and identify the complete projected forcing.
4. Derive the projected response's actual radial endpoint conditions,
   then identify it with the original radial Green response on the
   positive-frequency overlap and continue that same observable to QNMs.

For the physical angular field E satisfying Delta_H E=lambda E, the
intended distribution equation for R=P(yU) is

```text
<f'',R> + lambda <sech(t)^2 f,R> - w^2 <f,R> = -<f,P(yF)>.
```

The exact Lean statement will use the existing Hilbert convention,
`<test,response>`, with every coefficient conjugation made explicit.
No noncompact-test, domain, endpoint, or continuation premise may be
inserted at the actual-source capstone. None of steps 1–4 is recorded as
closed here yet. Physical residue, complete-source pole survival,
spin-two/AIME reconstruction, and independent extinction remain open.
