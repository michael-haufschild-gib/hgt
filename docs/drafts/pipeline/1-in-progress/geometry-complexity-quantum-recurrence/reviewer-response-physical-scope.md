# Response to physical-scope review

Date: 28 August 2026

We accept three substantive criticisms. They require theorem and scope
changes, not cosmetic wording.

## 1. Engineered infinite-chain scope — accepted

The same-field construction uses an absolutely summable,
position-dependent nearest-neighbour coupling profile. It proves existence
and finite-to-infinite compatibility for one deliberately engineered field.
It does not establish a translation-invariant, finite-density, typical, or
material thermodynamic law.

Changes:

- Renamed result “Engineered same-field finite-to-infinite witness.”
- Demoted it in abstract, synthesis, literature comparison, lay summary, and
  experiment section.
- Separated finite-volume generic nearest-neighbour theorems from this
  infinite-chain existence construction.
- Stated exact order of limits in finite-volume occupation extinction:
  completed time first at fixed volume, volume second.
- Added that occupation extinction does not alone imply weak convergence of
  full return laws to a point mass.

## 2. Lack of finite-window rates — accepted with an exact repair

No model-free uniform finite-window rate is claimed for arbitrary-spectrum
weak convergence or support-edge recovery. We added a finite-spectrum theorem
for every fixed survival moment. If `delta_m > 0` is a certified lower bound
on every nonzero order-`m` replica detuning, then

```text
|M_m(T) - C_m| <= min(1, 1/(T delta_m)).
```

Here `C_m` is exact replica-collision mass. Bound has unit constant independent
of Hilbert-space dimension and moment order. If spectroscopy cannot separate
a detuning from zero, certificate fails explicitly; unresolved actions are
not classified by assumption.

Changes:

- Added theorem, derivation, and proof.
- Added finite-window experimental protocol with falsification criterion.
- Kept support-edge claim asymptotic and explicitly non-certifiable by a
  finite record without extra assumptions.

## 3. Physics grounding — accepted with a bounded claim

Central stationary law is a theorem for closed self-adjoint dynamics. It is
not an open-system recurrence law. We added density matrices, quantum effects,
Born probabilities, operational distance, normalized Kraus evolution, and
exact Schrödinger--Heisenberg duality.

For an explicit reset-mixture channel

```text
Phi_r(rho) = r U rho U* + (1-r) rho_reset,
```

we prove exact affine Born response, one-step operational error at most
`1-r`, and `N`-step device-to-ideal error at most `N(1-r)`. This supplies a
falsifiable finite-horizon calibration bridge. It does not claim to model
arbitrary decoherence or preserve recurrence asymptotically.

Changes:

- Added theorem-level operational bridge and appendix proof.
- Added open-system calibration protocol.
- Added foundational Gorini--Kossakowski--Sudarshan and Lindblad references.
- Removed language that could make finite data appear to establish an
  infinite-time or infinite-volume conclusion.

## Resulting scope

Paper's universal theorem remains mathematical: stationary survival law of a
closed time-independent quantum system is carried exactly by pure-point
spectrum. Physical claims are now limited to finite-system predictions with
explicit spectral-resolution and device-error budgets. Infinite-chain result
is retained only as engineered existence evidence.

## Bibliographic correction found during response

Existing Gupta--Short entry attached DOI `10.1103/kkz3-fthm` and *Phys. Rev.
A* 114, 012208 to recurrence preprint. APS record shows that DOI and journal
slot belong to “Fermion doubling in Dirac quantum walks.” False journal
metadata was removed; recurrence work is cited only as arXiv:2604.14995.
