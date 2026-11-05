# Five sub-RH breakthrough questions

- **ID:** R0411-BQ
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.5
- **Statement:** Unconditionally solve and formalize all five questions and their consequences.

| Question | Exact target | Status |
|---|---|---|
| 2.5.1 | Literal continuum Krein system, prime-power singularities, first singular length `2a*(ζ)` | Open |
| 2.5.2 | Lewis–Hecke defect bound excluding resonances in a de la Vallée Poussin region | Open |
| 2.5.3 | Log-free occupancy `D_win` at depth `A/log V`, with density tending to zero as `A→∞` | Open |
| 2.5.4 | Complete-family arithmetic proof of `R₁(A)=⊤` beyond `2·enlargedWeilFloorAperture`, using growing receiving fibres and literal prime bands | Scalar conclusion formalized; prescribed mechanism open |
| 2.5.5 | Polynomial-floor isolation on ζ's actual configuration, resolving every polynomial-scale near-coincidence to second order | Open |

No numerical experiments, added analytic assumptions, placeholders, or kernel bypasses.
Equivalent criteria and model results do not discharge these targets.

## 2.5.1: established local construction

For every precontact aperture, the exact unshifted Weil norm is complete, with the original
smooth core and isometric aperture inclusions. Its literal Fourier realization is entire and
injective, with bounded surjective evaluations. Compact zero-moving extends unitarily to each
evaluation kernel; source conjugate-reflection extends antiunitarily.

For evaluation vectors `v_z`, put `k=‖v_i‖²` and `E_a(z)=(z+i)F(v_i)(z)`.
The polarized zero-moving identity gives

`E(z)conj(E(w))-E♯(z)conj(E♯(w))=2ik(conj(w)-z)K_a(w,z)`.

Thus `E_a` is Hermite–Biehler and has no real zeros. At finite contact, some fixed diagonal
kernel tends monotonically to infinity: a uniform earlier bound would extend to a nonzero
null ground vector and force its nonzero Fourier value to vanish.

These results are formalized in
[the local kernel and contact theorem](../3-formalized/the-local-weil-kernel-and-its-contact-singularity.md),
using [the unshifted completion](../3-formalized/the-unshifted-weil-space-before-contact.md) and
[compact zero-moving](../3-formalized/moving-a-transform-zero-preserves-the-weil-form.md).
Every actual evaluation Riesz vector also has a bounded measurable physical representative
with exact aperture support and solves the literal restricted operator equation with compact
exponential forcing; see
[the boundedness theorem](../3-formalized/the-completed-weil-riesz-vectors-are-bounded.md).
The same source solves the literal positive logarithmic Dirichlet equation
with bounded forcing retaining every prime and polar term; see
[the exact reference equation](../3-formalized/the-weil-riesz-equation-is-a-logarithmic-dirichlet-equation.md).

**Remaining:** [normalized endpoint traces](normalized-boundary-traces-of-weil-riesz-vectors.md),
their aperture variation, original-length canonical normalization, and prime-entry law.
The reference trace input is
[the half-line logarithmic Green kernel](the-half-line-logarithmic-green-kernel.md).
The ordinary integrable-accelerant theorem does not apply to the unbounded literal Weil form
(`WeilPaperUnboundedSpectralEnergy`). The RH-dependent `suzuki_deBranges_subspace` cannot supply
this unconditional construction.

**Endpoint distinction:** `windowPositiveAt_iff_le_onsetAperture` retains nonnegative window
positivity at finite contact, where the ground energy is zero. Inverse-kernel divergence occurs
on approach. A closed-endpoint equivalence between positivity and regular invertibility must
account for this zero mode.

## 2.5.4: established scalar enlargement

Write `s=weilFloorApertureStep`, `a₁=(181/500)(1+s)`, and `a₂=a₁(1+s)`.
The actual prime-two dilation modulus gives `a₁<a₂<1/2` and
`Q(f)≥(1/20000)∫f²` at aperture `a₂`. Hence `R₁(2a₂)=⊤`, with positive scalar and
finite-family critical pencils at every positive ratio and onset strictly beyond `a₁`.
[The enlargement theorem](../3-formalized/a-second-explicit-positive-weil-aperture.md) contains
the proof and Lean declarations. It does not derive the sign from growing receiving complements.

## Other exact gaps

- **2.5.2:** `MayerBoundaryZeroFree.xiZero_re_le` proves `β≤1−1/(1000 log γ)` for `γ≥4`
  from boundary-slope coefficients `(1−1/n)Λ(n)n^(−s)`. It supplies no bound for
  `lewisCoIsometryDefect` relative to the specified cross mass.
- **2.5.3:** `logFreeNearLineZeroDensity_iff_windowOccupancy_and_clusterTail` separates occupancy
  from multiplicity tails. Existing Selberg counts retain `log V` at fixed depth `A/log V`;
  the squared-depth moment does not remove it.
- **2.5.5:** `zeta_isolated_zero_multiplicity_readout_at_squareRoot_rpow` reads an individually
  polynomially isolated zero. It supplies neither uniform polynomial-floor isolation on ζ's
  configuration nor the required second-order readout for every polynomial-scale cluster.
