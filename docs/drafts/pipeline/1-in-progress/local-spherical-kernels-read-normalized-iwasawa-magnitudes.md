# Local spherical kernels read normalized Iwasawa magnitudes

- **Stage:** 1-in-progress
- **Parent:** [Arithmetic unfolding](finite-field-eisenstein-unfolding.md).
- **Target:** Identify the actual rank-one Iwasawa kernel with the audited
  valuation-shell kernel, using normalized local magnitudes. For `Re(s)>0`,
  its normalized Haar integral is `(1-Q^(-s-1))/(1-Q^(-s))`.

## Mechanism

An actual uniformizer has valuation `exp(-1)`. Its inverse-power integer
ball of radius `n` is exactly `{x : v(x) ≤ exp(n)}`. Integer discreteness
then gives `max(1,v(x))=exp(n)` on shell `n`, including the full integer
ball as shell zero. The residue-normalized magnitude therefore has
`max(1,|x|)=Q^n` on that shell.

Substitute `z=exp(-s log Q)` in the audited spherical kernel. Its shell
value `(z/Q)^n` is `exp(-(s+1)log(max(1,|x|)))`. Since `Q>1` and
`Re(s)>0`, the existing absolute-integrability and exact-integral theorems
apply. Actual finite and infinity residue equivalences discharge the
normalization parameters.

The [general shell and spectral-kernel bridge](../3-formalized/local-spherical-integrals-read-normalized-valuations.md)
passed direct Lean and transitive axiom audits. The
[actual finite-place and infinity specialization](../3-formalized/actual-elliptic-local-spectral-characters-have-exact-integrals.md)
passed the same audits. The finite simple root has torus valuations `(1,M)`;
the [affine simple root](../3-formalized/affine-simple-loop-iwasawa-values-are-column-norms.md)
has `(M,M⁻¹)`, where `M=max(1,v(x))`. Both passed direct Lean and axiom
audits. Both [actual adelic simple-root factorizations](../3-formalized/actual-elliptic-simple-roots-have-exact-iwasawa-values.md)
also passed direct Lean and axiom audits. Substitution into the normalized
Iwasawa character remains.
