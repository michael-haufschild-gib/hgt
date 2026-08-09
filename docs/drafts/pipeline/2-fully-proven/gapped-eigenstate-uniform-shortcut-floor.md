# Gapped-eigenstate uniform shortcut floor

- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [OBSTRUCTION] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/observer-spectral-shortcut-action-law.md`
- **Killed branch:** `../1-in-progress/observer-rank-autonomous-no-shortcut-law.md`
- **Lean:** `(1)`--`(2)` closed — `HTGeometry/GappedEigenlineStability.lean`,
  `HTGeometry.exists_hasEigenvector_of_gap`, unconditional and axiom-clean.
  `(3)` closed at the physical propagator —
  `HTGeometry/GappedEigenlineTimeUniformFloor.lean`, `HTGeometry/SelfAdjointPropagator.lean`,
  `HTGeometry/GappedEigenlinePropagatorFloor.lean`.
  The Pauli instantiation `(6)`--`(10)`, the Gaussian box bound `(11)`, and the
  asymptotic falsification `(12)` remain
- **Date:** 2026-08-05

## Exact abstract theorem

Let `H0` and `H=H0+V` be Hermitian operators on a nonzero finite-dimensional
complex Hilbert space. Let `Phi` be a unit vector and suppose

\[
 H_0\Phi=\lambda_0\Phi,
 \qquad
 \langle x,H_0x\rangle
 \le \lambda_0\|x\|^2
      -\Delta\bigl(\|x\|^2-|\langle\Phi,x\rangle|^2\bigr)
 \tag{1}
\]

for every `x`, where `Delta>0`. If `||V||<=delta`, then `H` has a unit
eigenvector `psi` satisfying

\[
 d_{\rm tr}([\psi],[\Phi])
 =\sqrt{1-|\langle\psi,\Phi\rangle|^2}
 \le \sqrt{2\delta/\Delta}.                         \tag{2}
\]

Consequently, for every real time `t`,

\[
 \boxed{
 d_{\rm tr}([e^{-itH}\Phi],[\Phi])
 \le 2\sqrt{2\delta/\Delta}.}
 \tag{3}
\]

The bound is uniform in time. It is not the Duhamel bound
`|t| ||V||`: a small perturbation of a gapped eigenstate changes the
eigenline once, and the perturbed eigenline is then preserved forever.

## Dependency-closed proof

Choose an orthonormal eigenbasis `(psi_j)` of `H`, with real eigenvalues
`mu_j`, and write `Phi=sum_j c_j psi_j`. Since

\[
 \langle\Phi,H\Phi\rangle
 =\lambda_0+\langle\Phi,V\Phi\rangle
 \ge\lambda_0-\delta,
\]

at least one index `j` satisfies `mu_j>=lambda_0-delta`; otherwise their
convex combination with weights `|c_j|^2` would be smaller. For the
corresponding unit eigenvector `psi`,

\[
 \langle\psi,H_0\psi\rangle
 =\mu_j-\langle\psi,V\psi\rangle
 \ge\lambda_0-2\delta.                              \tag{4}
\]

Applying `(1)` to `psi` and comparing with `(4)` gives

\[
 \Delta(1-|\langle\Phi,\psi\rangle|^2)\le2\delta,
\]

which is `(2)`. Since `psi` is an eigenvector of `H`, its projective ray is
fixed by `e^{-itH}`. Unitary invariance and the triangle inequality give

\[
\begin{aligned}
 d_{\rm tr}([e^{-itH}\Phi],[\Phi])
 &\le d_{\rm tr}([e^{-itH}\Phi],[e^{-itH}\psi])
      +d_{\rm tr}([e^{-itH}\psi],[\Phi])\\
 &=2d_{\rm tr}([\psi],[\Phi]),
\end{aligned}
\]

proving `(3)`.

## Full fixed-`q` Pauli Gaussian instantiation

Fix `q>=1`, `n>=q`, and

\[
 m=m_{n,q}=\sum_{k=1}^q3^k{n\choose k},
 \qquad
 H_n(J)=m^{-1/2}\sum_{P:\,1\le\operatorname{wt}P\le q}J_PP.
 \tag{5}
\]

Let `Phi=|0>^{\otimes n}`. Define the diagonal centre `J0` by
`(J0)_(Z_S)=1` for every nonempty `S` of size at most `q`, and zero on all
other Pauli words. Thus

\[
 H_0=m^{-1/2}\sum_{\varnothing\ne S,\ |S|\le q}Z_S. \tag{6}
\]

Every computational basis vector `|T>` is an eigenvector. The top vector is
`|emptyset>=Phi`. If `T` is nonempty, choose `i in T`; the singleton term
`Z_{\{i\}}` lowers its energy by `2/sqrt(m)`, while every other term lowers
the top energy by either zero or the same positive amount. Hence `(1)`
holds with

\[
 \Delta=2/\sqrt m.                                  \tag{7}
\]

Fix `0<epsilon<=1` and put

\[
 w={\epsilon^2\over16m},\qquad
 B_{n,q,\epsilon}=\{J:|J_P-(J_0)_P|\le w\text{ for every }P\}. \tag{8}
\]

For `J` in this box, Pauli operator norms and the triangle inequality give

\[
 \|H_n(J)-H_0\|\le m^{-1/2}\sum_P|J_P-(J_0)_P|
 \le {\epsilon^2\over16\sqrt m}.                    \tag{9}
\]

Equations `(3)`, `(7)`, and `(9)` yield the stronger bound

\[
 \boxed{
 \sup_{t\in\mathbb R}
 d_{\rm tr}([e^{-itH_n(J)}\Phi],[\Phi])\le\epsilon/2.}
 \tag{10}
\]

Therefore every Hamiltonian in `B_(n,q,epsilon)` has zero-gate state
complexity at error `epsilon` for every time.

## Explicit Gaussian probability floor

Let the coefficients be independent standard Gaussians. Since `w<=1/16`,
every coordinate in `(8)` lies in `[-2,2]`. The standard Gaussian density
on that interval is at least

\[
 c_0=(2\pi)^{-1/2}e^{-2}.
\]

Every coordinate interval has length `2w`; independence therefore gives

\[
 \boxed{
 \Pr\{J\in B_{n,q,\epsilon}\}
 \ge\left({c_0\epsilon^2\over8m_{n,q}}\right)^{m_{n,q}}.}
 \tag{11}
\]

This lower bound is independent of time and survives conditioning on a
nonzero local interaction scale, since all diagonal centre coefficients are
positive and `w<1`.

## Exact falsification

The observer-rank branch conjectured, for some `c>0` and every small fixed
`eta>0`,

\[
 \Pr\{C_\epsilon(e^{-itH_n(J)}\Phi)\le at\Lambda_n(J)/n^b\}
 \le t^{-(1-\eta)v_{n,q}},
 \quad
 v_{n,q}=2\sum_{k=1}^q{n\choose k},                 \tag{12}
\]

through `t<=2^(cn)`. The identity circuit is admissible throughout the box,
so `(11)` lower-bounds the event in `(12)`. At `t=2^(cn)`, the proposed
right side has negative logarithm `Theta_q(n^(q+1))`, whereas `(11)` has
negative logarithm `O_q(n^q log n)`. The former is eventually larger for
every fixed `c>0` and `eta<1`. Thus `(12)` is false for every proposed
exponential-time window, regardless of its polynomial lower threshold.

## Positive survivor and master-law correction

The killing mechanism is a third local geometry missed by the Duhamel tube:
a polynomial-width neighborhood of a gapped easy eigenline is easy for all
time. It is not a recurrence tube of width `1/t` and not measured by the
projective differential rank at the input.

The completed-orbit action card already has a place for this mechanism. For
every `J` in `(8)`, the whole spectral orbit lies in the circuit-easy target,
so its completed-orbit target mass equals one. Hence the annealed completed
mass satisfies

\[
 \sigma_{n,q,\epsilon}(R)
 \ge\left({c_0\epsilon^2\over8m_{n,q}}\right)^{m_{n,q}},
 \qquad
 I^{\rm comp}_{n,q,\epsilon}(R)=O_q(n^q\log n).      \tag{13}
\]

Thus the minimum in the observer--spectral action necessarily leaves the
observer branch by polynomial time under unconditioned Gaussian sampling.
Any law claiming an exponential-time observer-rank ramp must instead be
quenched or quantile-resolved and must charge the rarity of gapped easy
Hamiltonians separately from their unit orbit mass. Merely renaming the
annealed completed mass as a typical plateau is invalid.

## Hostile audit

- The box is full-dimensional; no measure-zero exact eigenstate locus is used.
- The perturbation width is independent of time. Duhamel's `1/|t|` tube is
  inapplicable because the proof follows the perturbed eigenline.
- The diagonal centre is literally fixed-`q` local and uses only terms already
  present in the flagship Gaussian ensemble.
- The result disproves the observer-only upper law, not the repaired
  observer--spectral minimum: the latter's annealed spectral branch absorbs
  the box through `(13)`.
- The theorem does not prove the adaptive circuit-shortcut upper law. It
  changes its required primitive from an annealed average to a resolved
  rarity--orbit action if typical Brown--Susskind growth is the target.

## Formalization ledger

`(1)`--`(2)` are closed as `HTGeometry.exists_hasEigenvector_of_gap` in
`HTGeometry/GappedEigenlineStability.lean`: for self-adjoint `H₀` and `V` on a finite-dimensional
complex inner product space, a unit eigenvector `Φ` of `H₀` whose eigenvalue dominates the quadratic
form with gap `Δ`, and `‖V‖ ≤ δ`, the operator `H₀ + V` has a unit eigenvector `ψ` with
`1 - |⟪Φ,ψ⟫|² ≤ 2δ/Δ`.

The Lean proof takes the top Rayleigh vector of `H₀ + V` rather than the card's eigenbasis
argument.  On a finite-dimensional space the unit sphere is compact, so the quadratic form attains a
maximum there, and mathlib's Rayleigh theory makes that maximizer an eigenvector.  Comparing its
Rayleigh value against the value at `Φ` — the maximizer wins, and `Φ`'s value is at least
`λ₀ - δ` — and then feeding the gap hypothesis into the maximizer's value gives the bound directly.
No eigenbasis, no convex-combination argument, no resolvent.

`(3)` is closed as `HTGeometry.pureStateTraceDistance_apply_le_of_gap`.  The corpus already owned
the pure-state trace distance and its identification with the density distance up to `√2`, so the
triangle inequality is inherited rather than proved: the distance is a rescaled metric.  It is blind
to phases and preserved by isometries, so a unitary fixing a line moves every state by at most twice
its distance to that line.  The statement is for an arbitrary linear isometry with an invariant
line, which is what makes the bound uniform in time — nothing about `exp(-itH)` beyond fixing the
eigenline is used, and the time never appears.

`HTGeometry/SelfAdjointPropagator.lean` supplies the two facts that specialize `(3)` to the
physical propagator: `exp_apply_of_eigen` — the exponential acts on an eigenvector by the
exponential of the eigenvalue, proved by evaluating the series term by term — and
`neg_I_smul_mem_skewAdjoint` — a real multiple of `-i` times a self-adjoint operator is
skew-adjoint.

The unitarity of `exp(-itH)` needed a mathlib instance that does not exist:
`NormedSpace.exp_mem_unitary_of_mem_skewAdjoint` requires `NormedAlgebra ℚ 𝔸`, and that is not
derivable for `E →L[ℂ] E`.  It is supplied here rather than worked around.  The operator algebra of
a complex normed space carries no rational structure at all by default — not even a `SMul ℚ` — so
there is no diamond to avoid, and the rational algebra can be defined outright through the complex
scalars, with the norm inequality inherited from the complex one.  The instances are scoped, so
they are opted into rather than imposed on the rest of the corpus.

With that, `selfAdjointPropagator` is the propagator as a genuine linear isometry, and
`selfAdjointPropagator_apply_eigen` says it fixes every eigenline of its generator.

`HTGeometry/GappedEigenlinePropagatorFloor.lean` assembles the three pieces into the card's boxed
`(3)` at `exp(-itH)` itself: `pureStateTraceDistance_propagator_le_of_gap`.  The eigenvalue returned
by the Rayleigh construction is real, so the phase it contributes has modulus one and the eigenline
is genuinely fixed rather than merely invariant.  The time appears only inside the propagator; the
right-hand side is `2√(2δ/Δ)` with no `t` in it.

Remaining: `(6)`--`(10)` instantiate in the existing finite-qubit Pauli basis; `(11)` is a Gaussian
product-box estimate; `(12)` is the asymptotic comparison.

## Formal target

Formalize `(1)--(3)` as a finite-Hermitian gapped-eigenline stability theorem,
then instantiate `(6)--(10)` in the existing finite-qubit Pauli basis. The
Gaussian product-box bound `(11)` and the asymptotic contradiction in `(12)`
must also be formalized before this obstruction is used as a public claim.
