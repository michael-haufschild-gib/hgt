# SQB literal native scattering as approximate modular spectrum

- **Scope retired:** Identifying every actual Xi scattering energy with an approximate eigenvalue of the original modular Friedrichs operator, keeping its native parameter and Hilbert domain.
- **Scope retained:** The full SQB candidate, Maass-specific quarter domination, the entire transform, and independently reconstructed occurrence remain open.
- **Status:** Narrow obstruction and sharp positive survivor formalized and audited.

For `rho=beta+i gamma`, use native Eisenstein exponent `s=rho/2` and the actual
operator `A=1−Delta_H`. The source-pure Xi height and strip laws put the real part
of `1+s(1−s)` above the constructed cusp ray, while its imaginary part is
`gamma(1−beta)/2`.

**Exact killing theorem:**
`RHTower.SelbergScatteringNativeResidual.xi_scattering_no_approximate_eigenvectors`
excludes every unit original-domain sequence whose residual at that energy tends
to zero. At critical zeros the obstruction is still positive, so this is not an
RH disproof or an off-critical zero exclusion.

**Strongest nontrivial positive survivor:**
`xi_residual_isGLB` proves the exact infimum over all original-domain unit residuals:
`|gamma|(1−beta)/2`. The source `xiNativePacket` is an explicit normalized cusp
sequence approaching that bound. The finite-scale identity
`cuspUnitPacket_complex_residual_sq` retains the imaginary square and both cutoff
derivative costs. Thus the obstruction includes a sharp constructive approximation
law, rather than only nonexistence.

**Paper and Lean status:** Complete dependency-closed paper argument and one
audited module with 23 public declarations. Targeted final build and all-export
axiom audit passed; only standard Lean axioms occur. Necessary dependencies were
rebuilt serially, with no umbrella or full build. Repository lint results and
remaining mathematical scope are recorded in the [proof and audit](../3-formalized/sqb-native-domain-residual.md).

The new insight is an exact cost for literal native-domain occurrence. No choice
of unit vector removes that cost. A different source/parameter/operator relation
must be proved independently; merely improving cutoff estimates cannot supply it.
