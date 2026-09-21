# EGC rational Cauchy inner-landing facts

- The rational EGC kernel has prescribed poles at `z = w ± eps`; it cannot be used as an entire inner test without accounting for those residues.
- `XiMeromorphicCauchyPairSourceLanding.lean` proves the pole-free alternative: if both prescribed poles lie outside an admissible inner rectangle, the normalized continued prime--archimedean inner contour equals the exact finite Xi multiplicity-copy Cauchy row.
- This landing is source-first and does not select, enumerate, or fit poles to Xi zeros. It uses the prescribed `eps` and observation `w` only.
- The exact three-pole decomposition fixes the residue orientation for the complementary crossing regime: in `K(z,w)/(z-rho)`, the pole at `w + eps` has coefficient `-eps/(2*(rho-w-eps))`, while the pole at `w-eps` has coefficient `+eps/(2*(rho-w+eps))`. The initially guessed opposite orientation is false.
- The theorem does **not** prove a nested covariance or a cofinal limit. The outer phase necessarily encounters the shifted poles of the finite Cauchy row; its residue correction and a source-side cofinal-decay law remain the EGC hard gates.
