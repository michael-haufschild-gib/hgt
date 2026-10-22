# EGC rational Cauchy inner-landing facts

- The rational EGC kernel has prescribed poles at `z = w ± eps`; it cannot be used as an entire inner test without accounting for those residues.
- `XiMeromorphicCauchyPairSourceLanding.lean` proves the pole-free alternative: if both prescribed poles lie outside an admissible inner rectangle, the normalized continued prime--archimedean inner contour equals the exact finite Xi multiplicity-copy Cauchy row.
- This landing is source-first and does not select, enumerate, or fit poles to Xi zeros. It uses the prescribed `eps` and observation `w` only.
- The exact three-pole decomposition fixes the residue orientation for the complementary crossing regime: in `K(z,w)/(z-rho)`, the pole at `w + eps` has coefficient `-eps/(2*(rho-w-eps))`, while the pole at `w-eps` has coefficient `+eps/(2*(rho-w+eps))`. The initially guessed opposite orientation is false.
- The theorem does **not** prove a nested covariance or a cofinal limit. The outer phase necessarily encounters the shifted poles of the finite Cauchy row; its residue correction and a source-side cofinal-decay law remain the EGC hard gates.
- **EGC-R1 (new, formal):** Functional-equation reflection by itself cannot cancel the two shifted-pole corrections. The closed counterexample `not_forall_meromorphicCauchyPair_reflectionCorrection_zero` in `XiMeromorphicCauchyPairReflectionCorrectionNoGo.lean` uses a pole-safe reflected pair and has only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). Its consequence is exact: reflection pairing can at most realify the outer correction; any EGC covariance proof requires an additional source-side real-part cancellation or decay law.
- **EGC-R2 (new, formal):** The two shifted residues are exactly
  `-eps^2 / ((rho-w)^2-eps^2)`.  Coordinate audit matters: EGC's
  `xiSpectralPoint = (rho-1/2)(-i)` sends a critical Xi copy to a *real*
  ordinate, so the tempting unrotated `rho=1/2+i*t, w=1/2` Poisson formula
  is not an EGC spectral assertion and was discarded before route use.  At
  the actual centered spectral observation `w=0`, the corpus bound
  `|xiCriticalOrdinate|>4` gives, for every `0<eps<=1`, the exact strictly
  negative correction
  `-eps^2/(xiCriticalOrdinate^2-eps^2)`.  Hence every nonempty finite cluster
  of critical Xi copies has strictly negative real correction and cannot
  internally cancel at this observation and scale.  The public theorems are
  in `XiMeromorphicCauchyPairCenteredCorrection.lean`.  This does not control
  a noncentered outer observation, off-line copies, or source/cofactor terms;
  it sharpens the remaining EGC gate to a genuinely source-derived balance or
  renormalization that survives beyond this centered critical channel.
