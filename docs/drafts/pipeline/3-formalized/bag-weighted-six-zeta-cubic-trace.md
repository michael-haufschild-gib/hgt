# BAG complete weighted six-zeta cubic trace

- **ID:** BAG-C28.56y, arithmetic factorization and critical correction.
- **Stage:** 3-formalized for the exact statements below.
- **Continuation:** `../1-in-progress/bag-weighted-cubic-critical-trace.md`.
- **Lean namespace:** `RHTower.BAGTrace`.
- **Leaves:** `ChiRamanujanWeightedCubicLocal`,
  `ChiRamanujanWeightedCubicTrace`, `ChiRamanujanWeightedCubicContractions`.

## Exact new result

Let Re(sigma)>1, Re(alpha)=Re(beta)=0. At every prime p set z=p^(-sigma),
U=p^(-alpha), V=p^(-beta). The coefficient c_z(i) is 1 for i>=0,
-z/(1-z) for i=-1, and 0 below -1. For each finite prime set P, sum

    prod_(p in P) c_z(i_p)c_z(j_p)c_z(i_p+j_p)
                          (z*U)^i_p (z*V)^j_p

over ALL integer valuation pairs. The directed limit through ALL finite
prime sets is

    Z = H(sigma,alpha,beta)
        * zeta(sigma+alpha)*zeta(sigma-alpha)
        * zeta(sigma+beta)*zeta(sigma-beta)
        / (zeta(sigma+beta-alpha)*zeta(sigma+alpha-beta)).

The finite sum has no omitted signed sector. Its balanced specialization
is the earlier real trace, proved by `weightedLocal_balanced`.

The Euler product H is locally uniformly convergent and jointly holomorphic
on the complex tube

    Re(sigma)>7/8, |Re(alpha)|<1/16, |Re(beta)|<1/16.

Thus it extends across the critical plane. Both exact axis identities hold:
H(sigma,0,beta)=H(sigma,alpha,0)=1. This is full joint holomorphy, obtained
using the corpus multivariable Weierstrass theorem.

The complete single-axis transform is

    D(sigma,alpha) = K(sigma,alpha)*zeta(sigma+alpha)*zeta(sigma-alpha),
    K = prod_p [1-z^2*(1-U^(-1))^2/(1-z)^2].

K converges locally uniformly across the critical plane, has K(sigma,0)=1,
and its complex frequency derivative at zero is zero for Re(sigma)>7/8.
The derivative statement is proved after the full infinite product, using
locally uniform convergence of derivatives, not at a fixed prime cutoff.

`weightedOffAxesTrace` literally masks either zero valuation vector. Its
complete limit is Z-D(sigma,beta)-D(sigma,alpha)+1, with the intersection
restored once. It is not a definition merely naming that subtraction.

## Why cancellation survives the full sum

Geometric HasSum identities sum the positive quadrant, both positive corners
and both negative strips. The exact six-factor local correction satisfies

    H_p-1 = z^2*(1-U^(-1))*(1-V^(-1))*N
               / ((1-z)^2*(1-z*V/U)*(1-z*U/V)),
    N = U+V-1-z^2-U/V-V/U+z/U+z/V.

Both vanishing factors are explicit. On the displayed complex tube a uniform
summable prime majorant follows. The constants only establish normal
convergence; this work does not optimize numerical bounds. Finite-product
HasSum, the ordinary convergent zeta Euler products, and nonvanishing in
Re(s)>1 identify the complete weighted trace. Each contraction is evaluated
independently and subtracted by literal inclusion-exclusion.

## Capstones and scope

- `complete_weighted_trace_six_zeta`
- `hasProdLocallyUniformlyOn_cubicPrimeFactor`
- `analyticOnNhd_cubicEulerCorrection`
- `complete_weighted_axis_two_zeta`
- `hasDerivAt_axisEulerCorrection_zero`
- `weightedOffAxesTrace_eq`, `complete_weighted_offAxes_trace`

The domain restrictions above are ordinary variables of the proved theorem,
not unproved arithmetic inputs. No conjectural hypothesis is introduced.
This is the directed prime-coordinate trace. A single unordered positive-
rational double-tsum reindexing and its fixed-dilation orthogonality transfer
are not provided by these leaves.

The critical DISTRIBUTIONAL boundary is still open: retain both the product
principal value and the intersection point mass, then justify its action
on the actual profiles. The arithmetic axes have not been identified with
literal physical prime diagonals. Damping-dependent contraction scales,
finite-height near-resonances, coupled damping/band limits, growing moments,
moving cofactors and positive common-height self-return remain open. RH is
not proved or refuted.

## Verification

All three production leaves pass direct `lake --old env lean ... -o ...`
audits without diagnostics; no full or umbrella build. Logs:
`/tmp/bag-weighted-local-production-01a0.log`,
`/tmp/bag-weighted-trace-production-01a0.log`,
`/tmp/bag-weighted-contractions-production-01a0.log`.
Umbrella imports are wired. All-public axiom and repository lint outcomes
are recorded below after their terminal results.

All46 public theorem axiom queries pass, each using only propext,
Classical.choice and Quot.sound. Axiom log: `/tmp/bag-weighted-axioms-01a0.log`.
Index regeneration passes and every public theorem is present in LEAN_API.
Repository lint exits1 solely on14 unrelated unreachable modules. It reports
no new-leaf, proof-debt or generated-file error. Lint log:
`/tmp/bag-weighted-lint-01a0.log`. Scoped whitespace check passes.
Owned temporary Lean probes removed; audit and search evidence retained.
