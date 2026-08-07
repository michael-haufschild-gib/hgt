# Observer critical-carrier confinement law

**Status:** EXACT LAW FORMALIZED — quantitative approximate-carrier successor open  
**Route:** autonomous-local-Hamiltonian complexity / quenched growing replicas  
**Novelty:** UNVERIFIED; generic analytic ingredients are classical, proposed autonomous observer application requires external priority audit

## Frontier problem

The current recurrence/complexity route has already removed exact spectral resonances almost surely, continuum lag ambiguity, fixed-target circuit-word ambiguity, and common-recurrence mass. The remaining qualitative loophole is nonlinear: an adaptive shortcut carrier might follow a low-dimensional exceptional family of Hamiltonian coefficients even though every fixed affine constraint is null.

Bounding the minimum replica spectral gap attacks the wrong object. It asks for anti-concentration of every integer relation, including relations unrelated to any shortcut, and its discriminant degree grows with the Hilbert-space dimension and replica order. This over-strong reduction is retired.

## Proposed replacement invariant

For an analytic observer endpoint map

\[
F:V\longrightarrow W,
\qquad v=\dim W>0,
\]

use the observer Jacobian, not the minimum spectral gap. Let

\[
\mathcal C_F=\{x\in V:\operatorname{rank} DF(x)<v\}.
\]

The central claim is that one full-rank jet confines *all* lower-codimension exact target carriers to the same target-independent critical set.

## Conjecture OCCC

Let \(V\) and \(W\) be finite-dimensional real inner-product spaces, let \(F:V\to W\) be real analytic, and suppose \(DF(x_0)\) is surjective at one point. Then:

1. \(\mathcal C_F\) has Lebesgue measure zero, hence zero measure for every nondegenerate Gaussian law on \(V\).
2. Every regular fibre \(F^{-1}(y)\setminus\mathcal C_F\) is a smooth embedded submanifold of codimension \(v\).
3. If a \(C^1\) embedded carrier \(M\subseteq V\) has codimension strictly smaller than \(v\) and \(F\) is constant on \(M\), then \(M\subseteq\mathcal C_F\).

Consequently, no positive-Gaussian-measure family of exact adaptive targets can be supported on carriers that beat observer codimension. All such carriers, for every target simultaneously, are confined to one universal null set.

## Dependency-closed paper proof

Choose orthonormal coordinates and a \(v\times v\) minor \(g\) of \(DF\) which is nonzero at \(x_0\). The function \(g\) is real analytic. Its zero set has Lebesgue measure zero: translate \(x_0\) to the origin; on every radial line \(r\mapsto r\omega\), the restricted analytic function is not identically zero because its value at \(r=0\) is nonzero. Its zeros are therefore countable. Polar Fubini gives nullity away from the origin, and the origin itself is null. Since rank deficiency forces every maximal minor, in particular \(g\), to vanish, \(\mathcal C_F\subseteq g^{-1}(0)\), proving (1). Absolute continuity of every nondegenerate Gaussian law gives Gaussian nullity.

At a point outside \(\mathcal C_F\), \(DF\) is surjective. The regular-level-set theorem gives (2). For (3), if \(F\) is constant on \(M\), then \(T_xM\subseteq\ker DF(x)\). Were \(x\notin\mathcal C_F\), rank-nullity would give \(\dim\ker DF(x)=\dim V-v\). But codimension \(M<v\) implies \(\dim T_xM>\dim V-v\), a contradiction. Thus every point of \(M\) is critical.

## Autonomous quantum specialization to prove

For a finite local-generator family \(A_1,\ldots,A_m\), fixed nonzero time \(t\), state \(\Phi\), and a fixed real-linear observer reporter \(P\), define

\[
F_t(J)=P\!\left(e^{-it\sum_j J_jA_j}\Phi\right).
\]

This map is analytic. At \(J=0\),

\[
DF_t(0)[K]=-it\,P\!\left((\sum_jK_jA_j)\Phi\right).
\]

If the reported generator action has rank \(v\), Conjecture OCCC applies. This would close the exact nonlinear-carrier loophole for ordinary time-independent local Hamiltonians at every fixed nonzero time. It does **not** yet give the approximate tube estimate needed for the full Brown--Susskind plateau law.

## Conjecturing loop

1. **Minimum replica-gap anti-concentration.** Falsified as a representation of the shortcut event: relation degree and union size encode worst-spectrum data unrelated to the observer.
2. **Target-by-target transversality.** Incomplete: uncountably many adaptive targets can defeat a naive union of null fibres.
3. **Universal critical-carrier confinement.** Survives paper attack: one nonzero Jacobian minor controls every target and every lower-codimension exact carrier at once.
4. **Quantitative successor.** Seek a quenched lower-tail law for the observer Jacobian pseudodeterminant, strong enough that coarea tube bounds survive circuit and replica unions. This is the remaining quantitative frontier.

## Hostile review

- The generic analytic-null and regular-value ingredients are classical; publication novelty cannot rest on them.
- The exact-carrier theorem is qualitative and does not establish a complexity plateau, recurrence time, or approximate circuit lower bound.
- A fixed-time result needs a separate treatment of a continuum of times; existing configuration-dimension subtraction suggests one additional Jacobian direction is necessary.
- The autonomous quantum application must be formalized, including analyticity and the derivative at zero, before it may appear as a proved claim.
- Priority must be audited specifically against static-Hamiltonian endpoint maps and adaptive circuit carriers, not merely against generic quantum-control transversality.

## Completion gate

- [ ] Lean theorem: radial analytic zero set is volume-null.
- [ ] Lean theorem: one full-rank analytic jet makes critical set Gaussian-null.
- [ ] Lean theorem: lower-codimension constant carriers lie in critical set.
- [ ] Lean theorem: autonomous endpoint derivative at zero.
- [ ] External priority audit for exact application.
- [ ] Quantitative observer-Jacobian lower tail or explicit proof that current assumptions cannot supply it.

## Formal result — 2026-08-07

The exact law is now formalized, including its autonomous exponential
specialization.

- `volume_zero_zeroSet_of_radial_analytic`: radial analytic certificate
  nullity in every finite dimension, including dimension zero.
- `analytic_observer_criticalSet_volume_zero` and
  `analytic_observer_criticalSet_stdGaussian_zero`: one nonzero observer minor
  makes the entire critical locus null.
- `observer_exactCarrier_dimH_le`: every exact carrier in a regular target
  fibre has Hausdorff dimension at most `m - v`.
- `analytic_observer_universal_exactCarrierLaw`: one common Gaussian-null
  critical set and the carrier bound for every target and every carrier.
- `autonomousExponentialEndpoint_fderiv_zero`: for `x ↦ R(exp(L x))`, the
  derivative at zero is exactly `R ∘ L`.
- `autonomousExponential_universal_exactCarrierLaw`: the universal law for
  autonomous exponential evolution in every real Banach algebra.

All three modules compile with `lake env lean`.  `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

### Updated completion gate

- [x] Radial analytic zero set is volume-null.
- [x] One full-rank analytic jet makes critical set Gaussian-null.
- [x] Every exact regular carrier obeys the observer-codimension dimension cap.
- [x] Autonomous exponential endpoint is analytic and has derivative `R ∘ L`
  at zero.
- [x] Targeted external audit against quantum-control endpoint singularity and
  transversality literature.
- [ ] Quantitative observer-Jacobian lower tail strong enough for approximate
  circuit and replica unions.

### Priority audit verdict

The radial analytic-null argument, regular-level-set geometry, and generic
transversality ingredients are classical.  Quantum-control literature studies
singular time-dependent controls and generic trap-free landscapes.  The audit
found no theorem at the precise interface of one autonomous static generator
ensemble, one target-independent critical locus, every exact adaptive target
carrier, and the sharp `m - v` Hausdorff-dimension ceiling.  Priority for that
assembled application remains **plausible but unverified**, not established.

### Hostile significance verdict

This is a real frontier advance because it eliminates the exact nonlinear
carrier loophole globally and replaces the over-strong minimum-gap program by
the correct observer-Jacobian invariant.  It is not a Brown--Susskind plateau
theorem and is not a Nature-level standalone result.  Approximate tube volume,
growing-replica scaling, and the circuit union remain open.
