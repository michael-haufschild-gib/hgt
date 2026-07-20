# Quasi-free rank--variance discriminant law

- **ID:** `quasi-free-rank-variance-discriminant-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / UNIVERSAL HILBERT-SPACE LAW / NOVELTY GATE
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED]`
- **Novelty:** `[SURVIVES PRELIMINARY ATTACK] [NOVELTY UNVERIFIED]`; no priority or
  general-journal claim
- **Source:** scale-covariance attack on `quasi-free-filling-bandwidth-fano-law`
- **Statement:** The scale-free variance deficit of a band-limited quasi-free additive
  observable is exactly endpoint leakage plus Hilbert--Schmidt anisotropy, giving a sharp
  rank-refined Bhatia--Davis law.

## Goal

Remove the dimensionally arbitrary coefficient `1` from the Fano margin and identify the strongest
homogeneous statement forced by the quasi-free moment formula.  The result must be invariant under
changes of energy units, have an exact equality geometry, give a sharp variance envelope, and expose
an operational consequence not already contained in the scalar Bhatia--Davis inequality.

## Gates

- [x] 0 -> 1 in-progress: well-posed, internal corpus searched, parent formulas separated,
  hostile scale attack complete
- [x] 1 -> 2 fully-proven: dependency-closed paper proof below, `[PROVED HERE]`
- [x] 2 -> 3 formalized: exact decomposition, nonnegativity, equality, sharp witness, and
  connector to the fixed-scale law compile unconditionally
- [ ] 3 -> 4 publication-ready: independent expert novelty audit and a demonstrated external
  scientific use case

## Universal law `[PROVED HERE]`

Let `H` be a finite-dimensional real or complex Hilbert space, let `0 <= Gamma <= I` have support
projection `P`, support rank `r`, and particle number

\[
 N=\operatorname{tr}\Gamma.
\]

Let `A=A*` have spectrum in `[a,b]`.  In the gauge-invariant quasi-free state with one-body
density `Gamma`, put

\[
 E=\mathbb E\,d\Gamma(A),\qquad V=\operatorname{Var}(d\Gamma(A)).
\]

Define the endpoint-leakage operator and the occupied compression

\[
 L=\operatorname{tr}\!\left[\Gamma(A-aI)(bI-A)\right],\qquad
 B=\Gamma^{1/2}A\Gamma^{1/2}\big|_{P H}.
\]

Then

\[
\boxed{
 r\big((a+b)E-abN-V\big)-E^2
 =rL+\big(r\|B\|_{\rm HS}^2-(\operatorname{tr}B)^2\big).
}                                                               \tag{RVD}
\]

Since `tr B=E`, the second defect is the Hilbert--Schmidt anisotropy of `B`.  If `r>0`,

\[
 r\|B\|_{\rm HS}^2-(\operatorname{tr}B)^2
 =r\left\|B-\frac{E}{r}P\right\|_{\rm HS}^2.                  \tag{HSA}
\]

Both defects in (RVD) are nonnegative.  Consequently

\[
\boxed{
 V\le (a+b)E-abN-\frac{E^2}{r}
}                                                               \tag{QBD}
\]

for `r>0`.  Equivalently, in division-free form,

\[
\boxed{
 E^2+rV\le r\big((a+b)E-abN\big).
}                                                               \tag{QBD0}
\]

The law is homogeneous of degree two: replacing `(A,a,b)` by `(cA,ca,cb)` multiplies every
term by `c^2`.  It therefore has no distinguished energy unit.

## Coordinate form

Choose an orthonormal eigenbasis `u_i` of `Gamma` on its support, with eigenvalues
`lambda_i>0`, and put

\[
 \mu_i=\langle u_i,Au_i\rangle,\quad
 \nu_i=\langle u_i,A^2u_i\rangle,\quad
 C_{ij}=\langle u_i,Au_j\rangle,
\]

\[
 \epsilon_i=(a+b)\mu_i-ab-\nu_i\ge0,\qquad
 x_i=\lambda_i\mu_i.
\]

Then (RVD) has the fully positive coordinate expansion

\[
\boxed{\begin{aligned}
 r\big((a+b)E-abN-V\big)-E^2
 &=r\sum_i\lambda_i\epsilon_i
   +\frac12\sum_{i,j}(x_i-x_j)^2\\
 &\quad+r\sum_{i\ne j}\lambda_i\lambda_j|C_{ij}|^2.
\end{aligned}}                                                  \tag{RVD3}
\]

Thus equality holds, for `r>0`, exactly when all occupied spectral mass lies on the two endpoints
and the occupation-compressed observable is isotropic:

\[
 \Gamma^{1/2}A\Gamma^{1/2}=\frac Er P
 \quad\text{on }PH.
\]

No commutation of `A` and `Gamma` is assumed.

## Dependency-closed proof `[PROVED HERE]`

The standard quasi-free first-two-cumulant formula is

\[
 E=\operatorname{tr}(\Gamma A),\qquad
 V=\operatorname{tr}(\Gamma A^2)-
   \operatorname{tr}(\Gamma A\Gamma A).
\]

The two terms introduced above satisfy

\[
 L=(a+b)E-abN-\operatorname{tr}(\Gamma A^2),
 \qquad
 \|B\|_{\rm HS}^2=\operatorname{tr}(\Gamma A\Gamma A).
\]

Hence

\[
 (a+b)E-abN-V=L+\|B\|_{\rm HS}^2.                             \tag{5}
\]

Multiplying (5) by `r` and subtracting `E^2=(tr B)^2` proves (RVD).  The spectral theorem gives
`L>=0`.  Hilbert--Schmidt Cauchy--Schwarz gives

\[
 (\operatorname{tr}B)^2=\langle B,P\rangle_{\rm HS}^2
 \le \|B\|_{\rm HS}^2\|P\|_{\rm HS}^2
 =r\|B\|_{\rm HS}^2,
\]

and square expansion gives (HSA).  Dropping the two defects proves (QBD0), hence (QBD).

In the eigenbasis of `Gamma`, separate diagonal and off-diagonal entries of `B`.  The elementary
identity

\[
 r\sum_i x_i^2-\left(\sum_i x_i\right)^2
 =\frac12\sum_{i,j}(x_i-x_j)^2
\]

then gives (RVD3).

## Sharpness `[PROVED HERE]`

Fix `r>=1`, `0<N<=r`, and a target `E` with `E/N in [a,b]`.  On the orthogonal sum of `r`
two-dimensional endpoint blocks, let `A` have eigenvalues `a,b`.  In every block choose the same
unit vector whose endpoint mixture has mean `E/N`; let `P` project onto the span of these `r`
vectors and set `Gamma=(N/r)P`.

Every occupied vector has endpoint support, so `L=0`.  Different blocks are orthogonal and

\[
 PAP=\frac EN P,
 \qquad
 B=\Gamma^{1/2}A\Gamma^{1/2}=\frac Er P.
\]

The Hilbert--Schmidt anisotropy also vanishes.  Equality therefore holds in (QBD) for every
feasible triple `(r,N,E)` once `2r` ambient endpoint dimensions are available.  The variance
envelope is globally sharp, not only asymptotically sharp.

## Operational corollaries `[PROVED HERE]`

Whenever the denominator is positive, the first two cumulants certify the support rank:

\[
\boxed{
 r\ge \frac{E^2}{(a+b)E-abN-V}.
}                                                               \tag{RC}
\]

For nonnegative weights in `[0,b]`, particle number drops out:

\[
 r\ge \frac{E^2}{bE-V}.                                       \tag{RC0}
\]

For an unweighted determinantal count (`b=1`), this becomes

\[
 r\ge \frac{(\mathbb EX)^2}{\mathbb EX-\operatorname{Var}X}.
\]

The right side is the Renyi-2 participation rank of the compressed determinantal kernel.  Thus
mean and noise alone provide a tomography-free lower certificate for the number of active
fermionic or determinantal modes.

## Anti-theatre and hostile audit

1. **Scalar-parent attack.**  The secant inequality behind `L>=0` is the classical
   Bhatia--Davis mechanism.  It is parent theory, not novelty.
2. **Trace-Cauchy attack.**  The nonnegativity of the anisotropy defect is the standard
   Hilbert--Schmidt trace/rank inequality.  It is parent theory, not novelty.
3. **Moment-formula attack.**  The quasi-free cumulant formula and determinantal Fredholm
   determinant are standard.  They are parent theory, not novelty.
4. **Combination attack.**  Targeted searches found the three parents separately, but did not
   locate (RVD), (QBD), its equality classification, or the sharp all-feasible-moments witness in
   quasi-free/DPP literature.  This supports only `[SURVIVES PRELIMINARY ATTACK]`, never a global
   absence claim.
5. **Special-case attack.**  For a one-particle probability law, (QBD) reduces to classical
   Bhatia--Davis.  For unweighted DPP counts, (RC0) reduces to the elementary participation-rank
   inequality for the eigenvalues of the restricted kernel.  Those faces are not new.  The
   candidate contribution is the noncommuting, partially occupied, weighted operator law with
   exact two-defect geometry and global sharpness.
6. **Scale-parameter attack.**  The intermediate family
   `tau E - V` is only a moving square completion.  It is not promoted as a discovery.  Optimizing
   it yields the homogeneous discriminant (RVD), which is the surviving statement.
7. **General-journal gate.**  Mathematical correctness and preliminary non-collision are not
   enough.  The theorem still needs an independent expert audit and a compelling application in
   fermionic mode certification, DPP complexity inference, or fluctuation metrology.

## External parent-theory audit

- Bhatia and Davis, *A Better Bound on the Variance*, American Mathematical Monthly 107 (2000),
  353--357, DOI `10.1080/00029890.2000.12005203`.
- Klich, *Full Counting Statistics: An elementary derivation of Levitov's formula*,
  arXiv:`cond-mat/0209642`.
- Hough--Krishnapur--Peres--Virag, *Determinantal Processes and Independence*, Probability
  Surveys 3 (2006), arXiv:`math/0503110`.
- Bufetov, *Rigidity of determinantal point processes with the Airy, the Bessel and the Gamma
  kernel*, Bulletin of Mathematical Sciences 6 (2016), for the standard projection-DPP additive
  variance formula.

Searches on 2026-07-20 checked exact combinations of `fermionic Bhatia--Davis`, `quasi-free
variance rank`, `determinantal Bhatia--Davis`, `support rank full counting statistics`, and
`effective rank determinantal linear statistics`.  No exact collision was found.  Search-engine
non-detection is not proof of novelty.

## Lean formalization

`GaloisForLFunctions.HilbertMetric.QuasiFreeRankVarianceDiscriminant` contains:

- `quasiFreeSpectralBandBudget_eq_secant_add_compressed` for (5);
- `quasiFreeSpectralRankVarianceDiscriminant_two_defect` and
  `quasiFreeSpectralRankVarianceDiscriminant_hilbertSchmidt_two_defect` for (RVD)--(HSA);
- `quasiFreeSpectralRankVarianceDiscriminant_three_defect` for (RVD3);
- `quasiFreeSpectralVariance_rank_bhatiaDavis` for (QBD0);
- `quasiFreeSpectralRankVarianceDiscriminant_eq_zero_iff` for equality classification;
- `quasiFreeEndpointPairRankVarianceDiscriminant_zero` for the sharp rank-one endpoint face;
- `quasiFreeSpectral_support_rank_lower_bound` for (RC);
- `quasiFreeSpectralRankVarianceDiscriminant_scale` for energy-unit covariance;
- `quasiFreeSpectralFanoMargin_lower_bound_of_rankVariance` connecting the stronger theorem to
  the earlier fixed-scale filling--bandwidth law.

Direct checks of the new source and the `HilbertMetric` umbrella pass.  Exact `#print axioms`
checks of every headline theorem report only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-20 -- Created after the arbitrary-unit attack killed the raw fixed-coefficient Fano
  formulation as a universal headline.  Paper proof and sharpness construction closed; exact Lean
  implementation remained open.
- 2026-07-20 -- Formalized the homogeneous two- and three-defect laws, literal Hilbert--Schmidt
  geometry, equality classification, endpoint witness, rank certificate, scale covariance, and
  connector to the fixed-unit theorem.  Direct module and umbrella checks passed; axiom audit is
  unconditional.  Scientific novelty and the general-journal gate remain open.
