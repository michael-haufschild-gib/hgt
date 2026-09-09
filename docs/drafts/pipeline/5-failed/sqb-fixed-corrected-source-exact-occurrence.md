# SQB fixed corrected source and convergent cutoffs

Status: exact occurrence from this fixed corrected source and approximate
occurrence from its constructed cutoff family are excluded in Lean.
Its strongest positive survivor is fully proved on paper and formalized.
SQB remains an open candidate interface; RH remains unproved.

## Exact mechanism and obstruction

Start with the complete original modular source, perform the audited original
cusp subtraction, and call its native L² vector V. The actual entire covariance
C produces a nonzero domain vector CV and its unit normalization U. The proposed
exact occurrence would require `(T−mu)U=0` at each full Xi target mu.

The theorem `RHTower.SelbergScatteringSourceNonvanishing.sourceUnitVector_residual_pos`
proves instead `||(T−mu)U||>0` for every actual Xi copy, including critical copies.
The complete original forcing H is nonzero and cannot be any scalar multiple
of V: the original corrected field has a nonzero closed-cell value below the
cutoff transition, where H vanishes. Hence the exact native equation
`(A−e)V=H` prevents V from being a native eigenvector at any complex parameter.
The entire symbol's singleton-fibre theorem then prevents zero entire residual.

The actual compact modular approximants also fail to produce approximate
occurrence. The new `SelbergScatteringApproximateSourceResidual` module proves
every approximant nonzero, constructs its actual normalized entire-domain
vector U_n, and proves ||U_n||=1. Both U_n→U and T U_n→T U in native norm.
Consequently its full residual converges to the fixed source's strictly
positive residual; `sourceApproxEntireUnit_not_approximate` excludes a zero
limit for every Xi copy. Every original Fourier family and modular cutoff is
retained in these actual source vectors.

## Strongest positive survivor

The theorem `RHTower.SelbergScatteringEntireEigenvectors.entireForcingTransport_zero_iff`
classifies the exact transport kernel for every native forcing f:

`(I−(2+mu)C)(A−e)^(-1)f=0`

`iff f=0 or (Re rho=1/2 and Bf=(5/4+(Im rho)^2/4)^(-1)f)`.

Here B=A^(-1) is the original native covariance. On the original A-domain,
the displayed covariance eigen-equation is exactly `Af=(5/4+(Im rho)^2/4)f`.
This classification is a positive theorem about all forcings; it is not a
restatement of failure of the particular source H. The general companion
`cfc_apply_eq_zero_of_zero_set_subset` proves vector-kernel inclusion from
continuous spectral zero-set inclusion without any spectral gap or quotient bound.

The actual cutoff-family theorem supplies another positive survivor: exact
normalized graph convergence and the exact limiting residual, including its
strict positivity. This identifies what the full compact exhaustion converges
to; it is stronger than merely negating approximate occurrence.

The new insight is that this entire transform changes the relevant spectral
values while its singleton fibre still demands the original native eigenspace.
The original corrected source and forcing lie outside that required space.
Exact domain admission, nonzero normalization and a closed transport identity
cannot supply that missing membership.

## Scope and status

[Complete paper proof and Lean audit](../3-formalized/sqb-entire-forcing-kernel.md):
29 public declarations in four individually built, axiom-audited modules.
The negative theorem and exact positive kernel survivor are both closed in
Lean, with only standard logical axioms. The linked audit records the current
repository-wide lint result and verifies all four new umbrella imports.

The obstruction covers the fixed corrected vector and its constructed
normalized compact cutoff family. Other sources and different approximate
families remain open within SQB. The original source graph and forcing-transport
identities remain valid. Full-Xi spectral occurrence remains unproved.
