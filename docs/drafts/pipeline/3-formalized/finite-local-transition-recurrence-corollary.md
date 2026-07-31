# Finite local-transition recurrence corollary

- **Status:** formalized; hostile priority audit restricts it to supporting use
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteAndersonLocalTransitionRecurrenceLaw`
- **Claim class:** `[LEAN-PROVED] [TECHNICAL COROLLARY] [NOT HEADLINE NOVELTY]`

## Result

For the distinct energy sectors \(K\) of a finite single-particle
Hamiltonian, source \(x\), detector \(y\), and spectral projectors \(P_K\),
put
\[
  v_K=\langle y,P_Kx\rangle,\qquad
  P_{x\to y}(t)=\left|\sum_K v_K e^{-itE_K}\right|^2.
\]
For any nonempty retained mode set \(S\), define
\[
  L=\sum_K|v_K|,\qquad
  \alpha_S=\sum_{K\notin S}|v_K|.
\]
For normalized source and detector rows, \(L\le1\). For every phase
resolution \(Q\), a positive sampled return obeys
\[
 n\le(Q+1)^{|S|-1}
\]
and
\[
 |P_{x\to y}(n)-P_{x\to y}(0)|
 \le 4L\alpha_S+\frac{4\pi}{Q+1}L^2.
\]
The prescribed-exit theorem takes any nonnegative exit time at which this
budget is exceeded and any guard time \(g>0\), and returns at a time
\(n(t_{\rm ex}+g)>t_{\rm ex}\) with the same budget and sampled exponent.

## Deterministic localization specialization

If the already aggregated sector amplitudes satisfy
\[
 |v_K|\le C e^{-2\mu r_K}
\]
and the sector centres obey the formalized geometric shell-count bound,
then modes outside radius \(R\) contribute the corresponding geometric
tail while the exponent is the number of retained sectors minus one.

No claim is made that this hypothesis has been derived here for a named
Anderson ensemble.

## Paper proof

The spectral expansion has ordered-pair coefficients
\(v_K\overline{v_L}\), whose absolute mass factorizes as
\(|v_K||v_L|\). The omitted ordered-pair mass is at most
\(2L\alpha_S\), selected mass is at most \(L^2\), and the clique on \(S\)
has projective rank \(|S|-1\). The general expectation-history
capacity--distortion theorem gives the deadline and distortion. Cauchy--
Schwarz gives \(L\le1\) in the simple-spectrum eigenvector specialization.
The general theorem itself takes basis-independent sector amplitudes.

## Hostile priority result

This cannot carry a universal-law or Nature-level novelty claim:

- Kotowski--Oszmaniec already prove the effective-support exponent
  \(M-1\), tail tolerance, and recurrence strictly after exit.
- Gupta--Short give stronger global continuous-time exponents.
- Fishman--Grempel--Prange already connect Anderson localization to
  temporal almost-periodicity.
- Aizenman--Warzel prove genuine Anderson-ensemble, uniform-in-time
  off-diagonal propagator decay.
- For \(x\ne y\), orthogonal source and detector give \(P_{x\to y}(0)=0\);
  this corollary certifies later detector darkening, not recurrence of a
  transported excitation at \(y\).

It is retained only as a formally verified local-observable specialization
and possible experimental protocol component.

## Formal declarations

- `finiteSpectralTransition_history_eq_probability`
- `finiteEigenvectorTransitionMass_le_one`
- `exists_finiteSpectralTransition_recurrence`
- `exists_finiteSpectralTransition_postExit_recurrence`
- `finiteSpectralTransition_neverExits_or_postExit_return`
- `exists_finiteAndersonLocalTransition_recurrence`
- `finiteAndersonLocalTransition_neverExits_or_postExit_return`

## Verification

Foreground source compilation passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

Closed finite-dimensional unitary dynamics only. The deadline is a sampled
upper bound, not the first actual return time or a uniform waiting time
after exit. Uniform-in-volume claims need uniform localization and shell
constants. No open-system or device-feasibility claim follows.
