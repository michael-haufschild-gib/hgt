# Critical windows survive removal of the low conductors

- **ID:** critical-windows-survive-low-conductor-removal
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [critical-ratio continuation](../1-in-progress/critical-ratio-continuation.md)

## Exact target

Let L=log N, Q=floor(L^(13/32)), c_N≥1 and c_N⁸/L→R>0.
Write B_N for the actual complete Weil matrix of the tilted spline,
x_N(n)=h(log n−log N)/sqrt(n), and P_N for orthogonal projection onto
the actual conductor subspace through Q. For every bounded real profile
h supported in a fixed interval [-A,0], the checked theorem gives

    ||B_N P_N x_N|| → 0,
    ⟨B_N(x_N−P_Nx_N),x_N−P_Nx_N⟩ − ⟨B_Nx_N,x_N⟩ → 0.

For compact C² h the critical window limit consequently holds unchanged
on the orthogonal complement of this entire growing packet. Every
strictly negative compensated window survives there.
No existence of such a window is asserted.

## Paper argument

The normalized Ramanujan mode has complete-period absolute mass at most
its period m (`sum_range_abs_normalizedRamanujanMode_le`). Splitting a
prefix into whole periods and a remainder gives absolute mass at most
N+m. On the support of x_N, n≥N exp(-A). Hence for 1≤m≤Q≤N,

    |⟨x_N,v_m⟩| ≤ 2 ||h||∞ exp(A)/sqrt(L).

Also ||x_N||²≤||h||∞² exp(A). The actual conductor frame has Riesz
bounds 1/2 and 3/2 eventually at this Q. Its projection estimate gives

    ||P_Nx_N||² ≤ 2 Σ_(m≤Q)|⟨x_N,v_m⟩|² = O_h(Q/L).

Represent P_Nx_N=Σ b_m v_m. The lower frame bound then gives
Σb_m²=O_h(Q/L), with no assumed orthogonality of the individual modes.

The existing variable-rate inverse-energy residual estimate gives

    Ψ_N := Σ_(m≤Q) ||B_Nv_m−E_m v_m||²/E_m ≤ L^(1/4)

eventually at every fixed R. To specialize it without a small-R premise,
use c_N≤L^(2/15), k=128 and Q≤L^(13/32). The main term is at most
O(L^(133/640)(1+log L)^5), which is o(L^(1/4)); the horizon-error
term is O(L^(-46/15)(1+log L)^2) using L⁸≤N. This specializes
`exists_tiltedUnitSpline_quadratic_inv_energy_residual_sum_le`.

Monotonicity in overlap gives E_m≤C(1+log Q), uniformly in c≥1.
Finite weighted Cauchy–Schwarz and the upper frame bound yield

    ||B_N Σ b_m v_m||²
      ≤ [3 C²(1+log Q)² + 2 C(1+log Q) Ψ_N] Σ b_m²
      = O_h((1+log L)² L^(-11/32)) → 0.

Finally symmetry of B_N gives the exact energy difference

    -2⟨B_NP_Nx_N,x_N⟩ + ⟨B_NP_Nx_N,P_Nx_N⟩.

Its absolute value tends to zero by the preceding bound, boundedness of
x_N and contractivity of P_N. Division by c_N≥1 preserves convergence
to zero. The existing horizon limit therefore supplies the stated
compensated limit on the complement.

## Attack and significance

Verdict: `BRIDGE`. This is a localization boundary,
not an estimate of the sign on the complement. It shows that
all-R positivity on the polylogarithmic low packet leaves every window
obstruction intact. It does not cover the subexponential conductor cutoff
of the far-reserve argument, nor polynomial conductor charge families.

Orthogonal removal is not minimization of complete energy over low-packet
correctors. Coefficients of an optimal corrector may grow while its
conductor energy shrinks. The theorem therefore does not bound the
energy improvement from such correctors; that requires the signed
window–conductor mixed form in the inverse-energy metric.

The projection estimate is already present as
`primeCharge_conductor_projection_sq_le`; its statement applies to every
vector, despite its file's application-specific name. Its proof and the
variable-rate residual statement have been inspected. The all-R residual
budget in `TheCriticalLowPacketHasAUniformResidualBudget.lean` and the
actual coordinate, norm and projection bounds in
`WindowConductorCoordinatesVanishUniformly.lean` check with
`[propext, Classical.choice, Quot.sound]`, including their final actual-path
no-olean audits. `CriticalWindowsSurviveLowConductorRemoval.lean` passes
its final actual-path no-olean check with those same three axioms for
the operator bound, norm limit, unnormalized energy difference and
compensated window limit. All three modules are wired into their
umbrellas. Local-corpus audit only; no external novelty claim.

## Gates

- [x] Exact source objects, quantifiers and paper mechanism.
- [x] Formalize the all-R residual budget and actual window bounds.
- [x] Formalize the energy-preserving projection and window limit.
- [x] Final actual-path checks and transitive-axiom audit.
