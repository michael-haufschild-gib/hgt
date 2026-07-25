# Connes / Hedenmalm RH route — complete research handover

> **Current compact frontier:** [`connes-frontier-ledger.md`](connes-frontier-ledger.md).
> This long handover is historical; use the ledger to avoid repeating closed attacks.

**Last updated:** 2026-07-22
**Repository:** `/Users/Spare/Documents/code/riemann/publications/hgt`  
**Active research card:**
`docs/drafts/pipeline/1-in-progress/ccm-aperture-resolvent-riesz-sector.md`

## 1. Status at a glance

The Riemann hypothesis has **not** been proved in this lane.

The present route has reached an exact source-side formulation of the remaining RH theorem:

\[
J_a(b):=\partial_a\left|\Xi\!\left(\tfrac12+a+ib\right)\right|^2\ge 0
\qquad
(0<a<\tfrac12,\ b\in\mathbb R).
\]

For every fixed positive Gaussian temperature, this global sign is equivalent to positivity of
the complete Gaussian Hankel tower. It is also equivalent to RH. The equivalence is formalized;
the sign is not.

The strongest unconditional progress currently available in this lane is:

1. the complete tower is positive at every exterior aperture
   \(\tfrac12\le a<1\), including the sharp boundary \(a=\tfrac12\);
2. the complete tower is positive on the full central frequency band
   \(|b|\le 218/25\) at every interior aperture;
3. finite two-node and substantial three-node positivity chambers are closed;
4. the exact threshold law identifies the aperture of complete positivity with the horizontal
   width of the Xi divisor;
5. the critical Poisson response has an unconditional two-ended causal-resolvent norm-square
   factorization;
6. the first theta atom has the **wrong** eventual orientation sign, while the higher theta tail
   supplies the opposite leading term. Consequently the RH-bearing current is carried by the
   nonperturbative modular-seam remainder after cancellation of every algebraic endpoint order.

Items 1–4 are present in Lean. Item 5 is proved on paper but is not yet formalized. Item 6 is
proved on paper in the active card but is not yet formalized. Neither item 5 nor item 6 proves RH.

The exact open core is therefore:

> Prove a theta-specific, nonperturbative sign law for the completed modular-seam remainder,
> equivalently prove the phase-current domination inequality (40) in the active card, and hence
> prove \(J_a(b)\ge0\) for all interior apertures and frequencies.

Do not describe any existing criterion, carrier theorem, finite section, or exterior theorem as
an RH proof.

## 2. Mandatory restart procedure

A new agent should begin in this order:

1. Read `AGENTS.md` and then read `docs/meta/scientific-method.md` completely.
2. Read `formal/README.md`, `formal/AGENTS.md`, and `formal/LEAN_OVERVIEW.md`.
3. Read the active card
   `docs/drafts/pipeline/1-in-progress/hedenmalm-center-mixed-double-positivity-law.md`
   completely, especially equations (29)–(44).
4. Read `docs/drafts/pipeline/1-in-progress/rh-sota-literature-lean-wall-2026.md` for the live
   literature and formal frontier.
5. Search the live corpus before introducing any theorem or definition:

   ```text
   scripts/formal_tools.py research "Hedenmalm current theta seam"
   scripts/formal_tools.py research "Gaussian Hankel RH"
   scripts/formal_tools.py research "Connes spectral triple prolate"
   ```

6. Inspect the current worktree before editing. It is shared by multiple agents and is dirty.
   Preserve all unrelated changes.

The user requires unconditional mathematics, no placeholders, no numerical evidence, and no
claims whose proof is only heuristic. Use one foreground Lean process at a time. Batch substantial
edits and use `lake env lean <file>` for targeted verification. Use `lake build <module>` only for
the final exact-module audit. Do not run a full build.

## 3. Scope of this lane

This is the Connes/Hedenmalm source-and-orientation lane. Its purpose is to construct an actual
producer of the sign needed by a spectral or Hankel realization of Xi, not merely another
equivalent formulation of RH.

The following neighboring research may inform the route but must not be merged into its main
theorem without a proved intertwiner:

- generic hypertranscendence and Stanley–Reisner geometry;
- theta-tail likelihood moments in their nonlinear coordinate;
- Walsh, quantum-replica, or conditional Sonin statements;
- finite-prime spectral agreement without divisor-preserving convergence;
- Hilbert–Pólya constructions which only reproduce zero ordinates;
- the separate Abel-selection manuscript.

The anti-theatre test is strict: a theorem is progress toward RH only if it supplies a new
**producer** of the missing sign or discharges a nontrivial part of its domain. Criteria,
equivalences, repackagings, and positive spaces constructed under an RH-equivalent premise are
consumers.

## 4. How the research arrived here

### 4.1 Connes state-of-the-art audit

The project first audited the modern Connes route rather than treating “Connes” as a generic
operator label. The live literature map is
`docs/drafts/pipeline/1-in-progress/rh-sota-literature-lean-wall-2026.md`.

The key conclusions are:

- Connes–Consani–Moscovici's 2025 *Zeta Spectral Triples* supplies finite-prime self-adjoint
  rank-one perturbations and reported numerical spectral/determinant agreement. The missing
  theorem is rigorous convergence of the actual normalized operator determinant or ground-state
  transform to Xi with its divisor.
- The 2025/2026 quadratic-form and ground-state line proves a powerful real-zero consumer: a
  suitable lower-bounded self-adjoint convolution operator with an isolated simple even ground
  state has a Fourier transform with only real zeros. For RH, one still has to construct the actual
  Weil ground state and prove locally uniform convergence of its transforms to Xi.
- The Connes–Consani prolate/near-radical mechanism is not an incidental technicality. It is the
  correct noncompact escape from compact strict-margin Weil tests. The remaining missing link is
  source/divisor transport, not finite self-adjointness.
- Recent scaling-site, compactified-`Spec Z`, and absolute-geometry programs supply geometric
  foundations but currently do not supply the purity/sign theorem needed for RH.

### 4.2 Positive laws extracted from previous no-go results

Earlier work established that a viable finite-prime or semilocal Connes construction is forced to
carry all of the following:

1. **Cofinal divisor transport.** Finite determinants with real zeros prove nothing about Xi until
   normalized determinants converge locally uniformly and carry every Xi zero.
2. **Logarithmic-boundary control.** Finite-prime reflected sectors cross over at horizontal scale
   \(1/\log N\). A viable approximation must control the zero fibers through this boundary, not
   only prove a finite positivity or symmetry statement.
3. **Noncompact Weil detection.** A compact fixed-aperture test family with a strict positive Weil
   margin cannot detect every remote off-line quartet. A complete detector must grow in support or
   oscillation, or approach the radical of the all-line Weil form.
4. **An infinite arithmetic phase carrier.** Finite Gamma completion supplies only finite
   archimedean phase capacity. Prime directions must be carried by growing state, growing
   differential syntax, coefficient-side frequency, a divisor/determinant, or a genuinely
   infinite-dimensional space.
5. **Orbit-sensitive source–divisor incidence.** Functional equation, Schwarz symmetry,
   hypertranscendence, order-one growth, and any finite divisor prefix remain compatible with
   transverse divisor relocation. A successful carrier must expose an additional global marking.

These laws constrain a Connes construction, but they do not themselves provide the RH sign. The
research therefore pivoted from architecture-only theorems to the concrete Hedenmalm current.

### 4.3 Reviewer-driven correction

An earlier manuscript emphasized Abel selection and carrier geometry. Review correctly objected
that elegant reformulations of Xi zero geometry do not advance the missing RH estimate. The route
was therefore redirected toward proving an actual complete Gaussian Hankel tower positive.

The separate manuscript remains at:

`docs/drafts/pipeline/4-publication-ready/prime-arch-abel-susceptibility-selection/main.tex`

Its single main theorem is the Abel selection theorem, with the Gibbs radical/free-energy split as
a conceptual corollary and the Connes literature updated through the 2025 spectral-triple paper.
It is not an RH proof and should not absorb the theta-tail, Walsh, replica, or conditional Sonin
material merely to look broader. If revised for publication, the requested author list is:

> Michael Haufschild, GPT 5.6 Sol, Fable 5, Grok 4.5

The current Hedenmalm sign research is a distinct proof program.

## 5. The exact mathematical object

Let the normalized even theta source be

\[
k(x)=2\,\mathrm{VarTheta}_{00}(i e^{2x}),
\qquad
X(w)=\int_{\mathbb R}k(x)e^{wx}\,dx
=\Xi\!\left(\tfrac12+w\right).
\]

For \(0<a<1/2\), define

\[
M_a(t)=\int_0^\infty
r\sinh(ar)\,k(r/2+t)k(r/2-t)\,dr.
\]

Unconditionally, \(M_a\) is strictly positive, even, continuous, and integrable. Its Fourier
transform is the Hedenmalm radial Wigner current, with the precise factor determined by the
project's Fourier normalization. For the actual theta source the following are equivalent:

\[
\mathrm{RH}
\iff
J_a(b)\ge0\quad\forall,0<a<1/2,\ b\in\mathbb R
\iff
M_a\text{ is positive definite for every }0<a<1/2.
\]

At any fixed positive Gaussian temperature \(\tau\), the pointwise sign is also equivalent to
positivity of every finite section of the associated infinite Gaussian moment/Hankel tower.

The normalization between `Fourier(M_a)` and `J_a` must be checked against
`fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm` before fixing constants in
new Lean code. Depending on the chosen Fourier phase, a harmless factor of two appears. The sign
and RH equivalence do not depend on that convention.

## 6. What was already proved and formalized

The declarations below are the primary formal foundation. They were not rebuilt during this
handover; consult the source and pipeline cards for their last exact verification status.

### 6.1 Source and current

- `RHTower/ThetaWignerCenterMix.lean`
  - constructs the actual center-mixed density;
  - proves absolute integrability, continuity, evenness, and strict positivity;
  - proves the center-mixing/Fourier identity.
- `RHTower/HedenmalmAutocorrelationPath.lean`
  - identifies the density as the aperture derivative of an autocorrelation path.
- `RHTower/HedenmalmCenterMixedOrientationBoundary.lean`
  - identifies the Fourier current with the theta-orbit Krein current;
  - proves the global interior sign is equivalent to RH.
- `RHTower/HedenmalmRankTwoTangentInertia.lean`
  - proves the ambient pure-state tangent has exact inertia `(1,1)`;
  - shows ambient operator positivity cannot be the intended theorem.

### 6.2 Complete Hankel tower

- `RHTower/HedenmalmGaussianHankelRH.lean`
  - `HedenmalmGaussianHankelCone`;
  - complete tower at one positive temperature iff pointwise Hedenmalm sign iff RH;
  - existence of one successful temperature is already equivalent to RH.
- `RHTower/HedenmalmExteriorGaussianHankel.lean`
  - complete tower for every \(1/2\le a<1\);
  - canonical boundary tower at \(a=1/2\).
- `RHTower/HedenmalmCentralBandGaussianHankel.lean`
  - global-in-aperture, complete all-order tower on the central frequency band;
  - concrete formal endpoint \(|b|\le218/25\).
- `RHTower/HedenmalmGaussianHankelApertureWidthSpectrum.lean`
  - exact aperture-width spectrum;
  - positivity at every aperture strictly above \(\alpha\) iff the Xi divisor's horizontal
    support width is at most \(\alpha\);
  - the \(\alpha=0\) endpoint is RH.

### 6.3 Finite rungs and their limit

The corpus contains unconditional two-node positivity, radial monotonicity, several three-node
chambers, coalesced-square laws, and compact-core reductions. Important modules include:

- `HedenmalmCenterMixedThreePoint.lean`
- `HedenmalmCenterMixedLocalThreePoint.lean`
- `HedenmalmCenterMixedUniformCoalescedSquare.lean`
- `HedenmalmCenterMixedRaywiseCoalescedCone.lean`
- `HedenmalmCenterMixedFourthJetCusp.lean`
- `HedenmalmCenterMixedFourthJetCuspClosure.lean`

These are useful local structure. They must never be extrapolated to the complete tower. The
one-temperature theorem proves that closing **all** orders is already RH.

### 6.4 Consumer and obstruction modules

- `HTGeometry/ReflectionPositiveHankel.lean` turns an independently given positive Gram orbit into
  all-order Hankel positivity. It is a consumer, not a source producer.
- `RHTower/HedenmalmUniversalPositiveFormClassification.lean` classifies positive forms after
  positivity has been supplied.
- `RHTower/HedenmalmLocalFrameObstruction.lean` proves no finite constant-coefficient differential
  autocorrelation frame, and no entire spectral density of the tested form, can orient the
  Hedenmalm tangent. A successful factorization must be non-entire, divisor-sensitive, or cofinal.
- `RHTower/HedenmalmCanonicalOrientationMultiplier.lean`,
  `HedenmalmInfiniteOrientationSingularities.lean`, `HedenmalmOrientationResidues.lean`, and
  `HedenmalmOrientationUpperSingularityCeilingRH.lean` show that the canonical orientation
  multiplier has infinitely many divisor-indexed singularities with exact residues and that an
  upper singularity ceiling is RH-equivalent. These describe the carrier; they do not prove its
  sign.
- `RHTower/PrimeArchHighFrequencyAccretivity.lean` reduces the source-side open region to high
  positive frequency after discharging central-band, reflection, and density issues. Its final
  high-frequency assertion is equivalent to RH, not an unconditional proof.

## 7. New theorem added at the stopping point: two-ended causal resolvent

This is in the active card under **“Two-ended causal resolvent factorization”**. It is
`[PAPER-PROVED; UNCONDITIONAL; NOT RH]` and has no Lean module yet.

For \(f_a(b)=|X(a+ib)|^2\), let

\[
P_r(x)=\frac{r}{\pi(x^2+r^2)},
\qquad R=2a+r,
\]

and define

\[
\mathcal R_{r,c}(a)
=(P_r*f_a)(c)-\frac rR(P_R*f_a)(c).
\]

For

\[
g_{a,c}(x)=e^{(a+ic)x}k(x),
\]

and the causal/anti-causal resolvents

\[
(T_sg)(u)=\int_u^\infty e^{-s(x-u)}g(x)\,dx,
\qquad
(S_sg)(u)=\int_{-\infty}^u e^{-s(u-x)}g(x)\,dx,
\]

Plancherel gives

\[
(P_s*f_a)(c)=2s\|T_sg_{a,c}\|_2^2
\]

and hence

\[
\mathcal R_{r,c}(a)
=2r\bigl(\|T_rg\|_2^2-\|T_Rg\|_2^2\bigr).
\]

If \(D\) is the real Fourier multiplier, then

\[
\mathcal R_{r,c}(a)
=2r(R^2-r^2)
\left\|(r^2+D^2)^{-1/2}(R^2+D^2)^{-1/2}g_{a,c}\right\|_2^2.
\]

Thus the response itself is an exact positive source Hilbert norm. Evenness and reality join its
two ends:

\[
T_Rg_{a,c}(u)=e^{2au}\overline{S_rg_{a,c}(-u)}.
\]

With the one-sided Hedenmalm primitive

\[
B(w,x)=e^{iwx}\int_{-\infty}^x e^{-iwy}k(y)\,dy,
\]

the same identity becomes a weighted vertical contraction law:

\[
\mathcal R_{r,c}(a)
=2r\int_{\mathbb R}e^{-2ax}
\left(|B(c+i(r-a),x)|^2-|B(c+i(r+a),x)|^2\right)dx.
\]

The crucial derivative is

\[
\partial_a\mathcal R_{r,c}(a)
=4r\operatorname{Re}\langle xg,(A_r-A_R)g\rangle
+8rR\langle g,A_R^2g\rangle,
\qquad A_s=(s^2+D^2)^{-1}.
\]

The second term is positive. The first is the unique unresolved phase-current channel:

\[
\operatorname{Re}\langle xg,(A_r-A_R)g\rangle
=\frac1{2\pi}\int_{\mathbb R}
\left(\frac1{r^2+\xi^2}-\frac1{R^2+\xi^2}\right)
\operatorname{Im}(\overline{\partial_\xi\widehat g}\,\widehat g)\,d\xi.
\]

A sufficient source theorem is

\[
\operatorname{Re}\langle xg,(A_r-A_R)g\rangle
\ge -2R\langle g,A_R^2g\rangle
\tag{open phase-current domination}
\]

for every \(r>0\), \(0<a<1/2\), and \(c\in\mathbb R\). Cofinality as \(r\downarrow0\) then
gives \(J_a(c)\ge0\).

This inequality is not generic. The explicit log-concave counterfamily in the active card violates
the desired orientation. Any proof must use exact theta modular/arithmetic structure.

## 8. New theorem added at the stopping point: modular-seam dominance

This is in the active card under **“Modular seam dominance over the first theta atom”**. It is
`[PAPER-PROVED; LEAN OPEN; NOT RH]`.

Let

\[
h(x)=\mathrm{thetaCuspSourceTerm}(x,1),\quad x\ge0,
\qquad k_1(x)=h(|x|),
\]

and let \(X_1\) and \(J_{1,a}\) denote its bilateral transform and aperture current. Existing Lean
proves the exact endpoint slope

\[
h'(0)=\ell_1h(0)>0,
\qquad
\ell_1=\frac92-2\pi+\frac6{2\pi-3}.
\]

Repeated half-line integration by parts gives

\[
X_1(w)=\frac{2h'(0)}{w^2}+\frac{2h'''(0)}{w^4}
+\frac{2h^{(5)}(0)}{w^6}+o(|w|^{-6}),
\]

\[
X_1'(w)=-\frac{4h'(0)}{w^3}-\frac{8h'''(0)}{w^5}
-\frac{12h^{(5)}(0)}{w^7}+o(|w|^{-7}).
\]

For fixed \(a>0\), \(w=a+ib\), this yields the exact limit

\[
\lim_{|b|\to\infty}
\frac{(a^2+b^2)^3}{a}J_{1,a}(b)
=-16h'(0)^2<0.
\]

Therefore the reflected first atom has the wrong eventual sign and cannot supply even one
interior complete tower.

The full completed theta source has Schwartz exponential tilts, so its current decays faster than
every inverse power. If \(J_{\mathrm{corr},a}=J_a-J_{1,a}\), then

\[
\lim_{|b|\to\infty}
\frac{(a^2+b^2)^3}{a}J_{\mathrm{corr},a}(b)
=+16h'(0)^2.
\]

This is a sharp conceptual correction to the earlier first-atom domination idea:

> The first atom dominates positive half-line mass but not oscillatory orientation. The higher
> theta tail is small in mass yet leading-order decisive in the orientation topology. It cancels
> every algebraic cusp contribution. The full RH current is a beyond-all-orders modular-seam
> remainder.

The theorem still does not determine the sign of that remainder.

## 9. The exact unresolved RH-bearing theorem

There are now three equivalent ways to state the target. A successful proof may enter through any
of them, but it must not assume another one implicitly.

### Target A — current sign

\[
\forall,0<a<1/2\ \forall,b\in\mathbb R,
\qquad J_a(b)\ge0.
\]

### Target B — complete Gaussian Hankel tower

For one fixed \(\tau>0\), every finite Hankel section built from the Gaussian-weighted Hedenmalm
current is positive semidefinite at every interior aperture.

### Target C — source resolvent domination

Prove the open phase-current domination inequality from Section 7 for the actual completed theta
source, uniformly or cofinally as \(r\downarrow0\).

Target C is presently the best source-side attack because it isolates a positive square and one
orientation term. Target A remains the simplest final statement. Target B is the clean all-order
moment form. Any one of them, proved unconditionally for the actual source, completes RH.

## 10. Routes already tested and why they do not solve the target

### 10.1 Generic shape theory

The active card constructs

\[
k_{\varepsilon,\beta}(x)=e^{-x^2}(1+\varepsilon\cosh(\beta x))
\]

which is even, positive, Schwartz, and strictly log-concave for an explicit symbolic parameter
range, while its transform has off-axis zero lattices. Its Hedenmalm current is negative somewhere.
Thus positivity, evenness, rapid decay, strict log-concavity, radial decrease, and any fixed finite
collection of derivative signs cannot prove the theta-source theorem.

### 10.2 Finite Hankel sections

Two-node positivity and large parts of order three are already unconditional. No finite order can
prove the complete tower. The one-temperature criterion makes the all-order wall exact.

### 10.3 Abstract reflection positivity

`ReflectionPositiveHankel.lean` proves that a supplied Gram orbit gives positive Hankel sections.
The canonical prime–archimedean orbit currently exists exactly under an RH-equivalent premise.
Using it would be circular.

### 10.4 Likelihood spectral measure

`ThetaCuspLikelihoodSpectralMeasure.lean` gives a fixed positive spectral measure and a strict
Hankel hierarchy for the higher-to-first likelihood coordinate

\[
B(x)=\pi e^{2x}-\tfrac32.
\]

That is not the translation coordinate of \(M_a(t)\). Without a proved intertwiner, transferring
its positivity to the Hedenmalm tower is category substitution. Complete monotonicity in \(B\)
does not by itself imply the required translation positive definiteness.

### 10.5 First-atom domination

This is now decisively retired as a sign producer: the first atom has the wrong high-frequency
current. The entire higher tail is necessary despite being small in positive mass.

### 10.6 Theta-tail Haar, Jacobi, and finite-translation packets

The `XiCTaylorThetaTail*` modules contain exact cancellations, finite-translation decompositions,
primitive-ray squares, and favorable local packets. The capstone conservation law transfers a
decaying top-row current into a surviving translation current and reconstructs the original raw
orientation. Dropping the survivor is circular. A favorable Jacobi fourth-power packet does not
control the sign after global seam reassembly.

Read especially:

- `XiCTaylorThetaTailCoreCurrentCapstone.lean`
- `XiCTaylorThetaTailCompletedDensityDeBrangesNoGo.lean`
- `XiCTaylorThetaTailProductFiberCenteredSeamNoGo.lean`
- `XiCTaylorThetaTailPrimitiveRayGlobalReassembly.lean`

### 10.7 Divisor and singularity criteria

The orientation multiplier's divisor-indexed poles and residue laws are exact. An upper
singularity ceiling is equivalent to RH. This is a valuable carrier classification, not a method
for proving the ceiling.

### 10.8 Finite-prime or semilocal self-adjointness

Self-adjoint finite models, finite real spectra, numerical agreement, or finite determinant zeros
do not transport the Xi divisor. The missing cofinal convergence theorem cannot be replaced by a
finite positivity statement.

## 11. Lean work that is still missing

### 11.1 Highest-priority new module

Create:

`formal/GaloisForLFunctions/RHTower/HedenmalmFirstAtomSeamDominance.lean`

The recommended theorem batch is:

1. Define the half-line complex exponential moments of the derivative family of the first atom.
2. Prove the recurrence

   \[
   zI_n(z)=-h_n(0)-I_{n+1}(z)
   \]

   using `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`.
3. Perform four integrations by parts to obtain

   \[
   X_1(w)=2h'(0)w^{-2}+O(|w|^{-4}).
   \]

4. Apply the same infrastructure to \(x h(x)\) to obtain

   \[
   X_1'(w)=-4h'(0)w^{-3}+O(|w|^{-5}).
   \]

5. Prove a reusable algebraic perturbation lemma. If

   \[
   F=2h_1w^{-2}+e_F,\quad |e_F|\le C|w|^{-4},
   \]

   \[
   G=-4h_1w^{-3}+e_G,\quad |e_G|\le D|w|^{-5},
   \]

   then for \(|w|\ge1\),

   \[
   \left|2\Re(G\bar F)+16h_1^2a|w|^{-6}\right|
   \le K|w|^{-7},
   \]

   with a simple explicit nonnegative \(K\), for example
   \(4h_1D+8h_1C+2CD\) after checking the exact hypotheses.
6. Deduce eventual negativity and the scaled limit for the first atom.
7. Use the tilted-Schwartz/Fourier infrastructure to prove rapid decay of the completed current.
8. Deduce the complementary higher-tail limit.

Existing infrastructure to reuse:

- `XiCTaylorThetaTailFiniteTranslationBounds.lean`
  - `integral_Ioi_secondDerivative_mul_eq_boundary_add`;
- mathlib / existing consumers
  - `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`;
- `PrimeArchThetaWardLaplaceHalfDensity.lean`
  - `integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one` and endpoint decay;
- `ThetaCuspFinitePrimeDerivatives.lean`
  - explicit derivative atoms;
- `PrimeArchThetaGaussianApertureBalance.lean`
  - `thetaCuspFirstAtomBoundaryLogSlope`, its positivity, and the endpoint derivative identity;
- `ThetaCuspTiltedSchwartz.lean`, `ThetaCuspSchwartzFourierXi.lean`, and
  `XiCTaylorThetaTailRapidDecay.lean`
  - completed-source rapid decay.

The limit does not require a separate Riemann–Lebesgue theorem. Bounded remainders after four and
five integrations by parts suffice for eventual sign and the normalized limit.

### 11.2 Second module after the seam theorem

Formalize the two-ended causal resolvent factorization, preferably in:

`formal/GaloisForLFunctions/RHTower/HedenmalmTwoEndedCausalResolvent.lean`

Do not begin by building a large abstract semigroup library. First inspect existing Poisson,
Fourier, resolvent, and one-sided primitive declarations. The desired capstone should state the
norm-square identity, reflection identity, derivative split, and cofinal implication to the
Hedenmalm current.

### 11.3 Verification discipline

After writing a substantial dependency-closed batch, verify from `formal/` with exactly one
foreground process:

```text
lake env lean GaloisForLFunctions/RHTower/HedenmalmFirstAtomSeamDominance.lean
```

Only after the source file succeeds and the module is wired should the final audit use:

```text
lake build GaloisForLFunctions.RHTower.HedenmalmFirstAtomSeamDominance
```

Repeat the same discipline for the causal-resolvent module. Run `#print axioms` from a temporary
file, never by modifying production modules. The finished declarations must contain no `sorry`,
`admit`, new axiom, opaque proof escape, or unsafe declaration.

## 12. Next mathematical research program

Formalizing the seam theorem is foundation work, not the final producer. After it is formalized,
continue in this order.

### Step 1 — exact modular-seam moment hierarchy

Start from
`thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral` in
`ThetaCuspLikelihoodSpectralMeasure.lean`.

The completed source is even and smooth, while the reflected first atom has a cusp. Therefore the
higher tail must cancel every odd right endpoint jet. Derive the exact infinite family of moment
identities on the positive likelihood measure which expresses this cancellation.

This hierarchy is likely the correct algebraic fingerprint of modular completion. It is not enough
to observe that cancellation occurs; the goal is to identify a total-positivity, Pick, Stieltjes,
or variation-diminishing structure strong enough to orient the residual. Hostile-test every such
claim: complete monotonicity alone is insufficient, and a generic PF-infinity conclusion must not
be assumed.

### Step 2 — isolate the nonperturbative remainder

Subtract the full boundary expansion, not a finite truncation. Seek an exact contour,
steepest-descent, scattering, or Borel-type representation of the remainder in which its
contribution to \(J_a(b)\) is a positive integral or norm square.

The required result is not another estimate of the first few terms. Every algebraic endpoint order
cancels. The sign lives after that cancellation.

### Step 3 — join the seam remainder to the causal resolvent

Express the phase current

\[
\operatorname{Im}(\overline{\partial_\xi\widehat g}\,\widehat g)
\]

in terms of the exact modular-seam spectral measure or its scattering phase. The ideal theorem
would transform the open phase-current domination into positivity of a measure, a square, or a
monotone scattering phase forced by the theta modular identity.

The generic log-concave counterfamily must fail a visible hypothesis of this theorem. If it would
satisfy all hypotheses, the proposed proof is impossible.

### Step 4 — cofinal limit

Once the resolvent derivative is nonnegative for all sufficiently small \(r\), use the already
available Poisson approximation and theta-source dominated convergence to pass to
\(J_a(c)\ge0\). Then invoke the formalized equivalence to RH.

### Step 5 — only then state an RH proof

The final proof chain must have no RH-equivalent assumption hidden in a “positive orbit,”
“ground-state,” “upper singularity ceiling,” “high-frequency accretivity,” or “source
factorization” hypothesis. Each such property must be derived unconditionally for the actual theta
source.

## 13. New theorem: fixed-measure modular likelihood scattering

The former promising identity is now a dependency-closed paper theorem with a substantial Lean
surface. See

`docs/drafts/pipeline/2-fully-proven/needs-audit/theta-likelihood-modular-seam-transport.md`

and

`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodModularSeam.lean`.

Let \(h\) be the first theta atom,

\[
B(x)=\pi e^{2x}-\tfrac32,
\qquad
Z(B)=1+\int e^{-Bt}\,d\nu(t),
\]

where the fixed positive higher-tail measure is

\[
d\nu(t)=\sum_{n\ge2}e^{-3(n^2-1)/2}
\left[n^4\delta_{n^2-1}
+\tfrac32n^2(n^2-1)\mathbf1_{(n^2-1,\infty)}(t)\,dt\right].
\]

The factorization \(k(x)=h(x)Z(B(x))\) now holds on the full intrinsic domain \(B(x)>0\), not only
for \(x>0\). In the two-ended seam window, modular reflection becomes the exact Möbius scattering
law

\[
\iota(B)=\frac{\pi^2}{B+3/2}-\frac32,
\qquad B(-x)=\iota(B(x)),
\qquad \iota^2=1,
\]

\[
Z(B(x))=S(x)Z(B(-x)),
\qquad S(x)=\frac{h(-x)}{h(x)},
\qquad 0<S(x)<1,
\qquad S(x)S(-x)=1.
\]

The normalized reflected channel laws have an exact decreasing likelihood ratio and one crossing.
Its location is the nonperturbative log-partition scattering phase

\[
\tau(x)=\frac{\log Z(B(-x))-\log Z(B(x))}{B(x)-B(-x)}.
\]

Writing \(m(B)=-(\log Z)'(B)\), strict Laplace log-convexity yields

\[
m(B(x))<\tau(x)<m(B(-x)).
\]

The two gaps are exactly directed relative entropies divided by \(B(x)-B(-x)\); their sum is the
Jeffreys flux. At the seam, all odd integrated channel jets vanish and the first identity fixes

\[
m(\pi-3/2)
=\frac1{2\pi}\left(\frac92-2\pi+\frac6{2\pi-3}\right).
\]

Lean proves the extended factorization, reflection balance, Möbius involution, reciprocal strict
scattering contraction, one-crossing law, log-partition secant, log-partition derivative, all odd
integrated jets, and the first barycenter. The explicit score-polynomial expansion and strict
convexity/relative-entropy corollaries remain paper-only.

This is a genuine nonperturbative source law, not another endpoint estimate. It still does not
prove the Hedenmalm current sign: passivity and monotone likelihood ratio in latent temperature do
not automatically orient Fourier phase. Next producer must express the phase-current term in
Section 7 as a monotone observable or a conditionally positive two-parameter kernel in this same
latent coordinate.

## 14. Connes interpretation of the surviving target

The two-ended resolvent theorem gives the current route a precise Connes-compatible meaning.
The positive response is a passive two-ended scattering norm. Critical reflection forces the two
damping radii \(r\) and \(r+2a\), and the RH datum is not passivity alone but the orientation of its
aperture derivative.

Therefore a successful Connes realization must retain simultaneously:

\[
\text{cofinal divisor transport}
+\text{two-ended reflection}
+\text{noncompact/near-radical resolution}
+\text{theta-specific phase orientation}.
\]

Finite self-adjointness supplies passivity but not the derivative sign. Finite spectra supply
ordinates but not horizontal divisor transport. The prolate near-radical mechanism supplies the
necessary noncompact resolution but still needs the actual Xi source incidence. The modular-seam
remainder is the current source-side candidate for that incidence.

This is the correct positive replacement for a “no-go” statement:

> A viable Connes construction must be a cofinal, divisor-preserving, two-ended scattering system
> whose modular source phase dominates its positive resolvent correction at every interior
> aperture.

That obligation is precise. Its final sign theorem remains open.

## 15. Dirty worktree and file ownership

At handover time the worktree contains concurrent modifications and new files in both
`HTGeometry` and `RHTower`, including Suzuki and Gamma-pole work belonging to other agents. Do not
reset, revert, reformat, or delete them.

The Connes/Hedenmalm work before this continuation modified:

- `docs/drafts/pipeline/1-in-progress/hedenmalm-center-mixed-double-positivity-law.md`
  - added the two-ended causal-resolvent theorem;
  - added the modular-seam/first-atom theorem.

This continuation adds:

- `docs/drafts/pipeline/2-fully-proven/needs-audit/theta-likelihood-modular-seam-transport.md`;
- `formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodModularSeam.lean`;
- one import in `formal/GaloisForLFunctions/RHTower.lean`;
- this updated handover.

The first-atom wrong-sign asymptotic and two-ended causal-resolvent factorization remain paper-only.
Check the live tree before editing because unrelated concurrent files remain present.

## 16. Integrity and novelty rules

Keep these labels separate:

- **Lean-formalized:** exact declaration exists and has passed the targeted project toolchain.
- **Paper-proved:** a dependency-closed analytic proof is written, but Lean may still be open.
- **Criterion / bridge:** mathematically correct equivalence or transport theorem, not a sign
  producer.
- **Novelty unverified:** no priority claim should be made before a current literature audit.
- **Not RH:** the theorem does not discharge the global interior sign.

Specific warnings:

1. The center-mixed RH equivalence is closely related to the Sondow–Dumitrescu horizontal modulus
   monotonicity criterion. Its equivalence is not itself new RH progress.
2. The broad fact that finite endpoint expansions cancel in a completed smooth source was already
   anticipated elsewhere in the theta-tail pipeline. Do not claim that observation alone as a
   universal new law.
3. The source-specific wrong-sign first-atom asymptotic may be new, but novelty has not been
   verified.
4. The two-ended resolvent factorization may be publishable as an exact source identity, but its
   significance depends on whether it helps prove the phase-current sign.
5. A proof that “no single channel carries the missing datum” is not a proof of RH. Impossibility
   of one proof architecture does not establish the proposition it was intended to prove.
6. No finite Hankel section, finite prime cutoff, finite spectrum, or compact strict-margin Weil
   family suffices.
7. Do not call a theorem unconditional if it assumes any predicate already formalized as
   equivalent to RH.

## 17. Definition of completion

This lane is complete only when all of the following hold:

1. A paper proof derives \(J_a(b)\ge0\) for every \(0<a<1/2\) and every real \(b\) from the actual
   theta source without RH-equivalent premises.
2. The source-side analytic statements, limit passages, and sign theorem are fully formalized in
   Lean with no proof escape.
3. The formal capstone invokes the existing equivalence and derives `RiemannHypothesis`.
4. The exact source normalization and Fourier factors are audited.
5. A hostile review confirms that no consumer theorem has been presented as a producer.
6. Only then is a manuscript allowed to state a proof of RH.

## 18. Exact stopping point

Work stopped after deriving and formalizing the fixed-measure modular likelihood scattering law.
The exact open core is now narrower:

> Rewrite
> \(\operatorname{Re}\langle xg,(A_r-A_R)g\rangle\) using the fixed latent measure and prove that
> its two-parameter channel kernel is conditionally positive on the modular-scattering orbit, or
> identify a monotone latent observable whose stochastic order supplies inequality (40).

Do not return to finite endpoint estimates, finite Hankel sections, or generic log-concavity. The
Möbius scattering law and exact relative-entropy flux are the source-specific hypotheses the
generic counterfamily lacks or must visibly fail. A successful next theorem must connect one of
them to Fourier phase orientation. RH and global interior current positivity remain open.

Verification at this stopping point:

- direct `lake env lean GaloisForLFunctions/RHTower/ThetaCuspLikelihoodModularSeam.lean` passed;
- targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspLikelihoodModularSeam` passed;
- temporary `#print axioms` checks report only `propext`, `Classical.choice`, and `Quot.sound`;
- `scripts/formal_tools.py lint --check-generated` passed after one index regeneration;
- no `lake` or `lean` process remained running.

## 19. New obstruction and survivor: square-gap nondivisibility

The direct Lévy/Thorin continuation of Section 13 is now closed. See

`docs/drafts/pipeline/2-fully-proven/needs-audit/theta-likelihood-square-gap-nondivisibility.md`

and

`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodAtomicNondivisibility.lean`.

For every intrinsic coordinate \(B>0\), normalize the fixed tilted seam carrier to

\[
dP_B(t)=Z(B)^{-1}\bigl(\delta_0(dt)+e^{-Bt}d\nu(t)\bigr).
\]

Its atomic sector has the exact arithmetic signature

\[
P_B\{0\}>0,\qquad P_B\{3\}>0,\qquad P_B\{6\}=0.
\]

An infinitely divisible law on \([0,\infty)\) with an atom at zero is compound Poisson.
Compound-Poisson atom support is additively closed: concatenate jump-atom tuples producing
two atoms to produce their sum. Thus \(P_B\{3\}>0\) would force \(P_B\{6\}>0\), a
contradiction. Every \(P_B\) is therefore non-infinitely-divisible and, in particular, is not a
GGC or Thorin-subordinator marginal. This holds throughout \(B>0\), not only at the seam.

This does not conflict with Polson's incomplete-gamma or zero-based Thorin objects: those are
different probability laws. It rules out exponentiating this fixed likelihood carrier into
independent increments.

The positive survivor is stronger than the negation. Pairing creates a new latent atom:

\[
6\notin A(P_B),\qquad 6\in A(P_B*P_B),
\qquad (P_B*P_B)\{6\}\ge P_B\{3\}^2>0.
\]

Lean formalizes the exact one-particle atoms, failure of additive atom closure under every
nonzero normalization, and nonzero self-convolution mass at \(6\). The general classification
from infinite divisibility to compound Poisson remains paper-only.

Interpretation: missing Xi orientation cannot live in another one-particle monotone-likelihood,
Lévy-exponent, or passive-subordinator observable. It first appears in an irreducible
two-particle sector created by the square-gap incidence. This is source-specific structure the
generic log-concave counterfamily does not automatically possess.

## 20. Revised exact stopping point

The next frontier is no longer “find a one-particle latent observable.” That route is impossible
for the actual fixed carrier. Retain the full two-parameter channel kernel

\[
D_a(s;t,u)=\int_0^\infty r\sinh(ar)
q_t(r/2+s)q_u(r/2-s)\,dr,
\qquad q_t(x)=h(|x|)e^{-B(|x|)t},
\]

and isolate the phase contribution supported on pair sectors absent from the one-particle atomic
law, beginning with the exact birth \((3,3)\mapsto6\). Required theorem must show that modular
reflection or square-gap/ray coherence orients this two-particle defect contribution after the
full \(\nu\otimes\nu\) reassembly. Diagonal channel positivity, MLR, infinite divisibility, and
Thorin exponentiation cannot supply it.

RH and global Hedenmalm current positivity remain open. Novelty of the square-gap application is
unverified; no priority claim is made.

## 21. Offensive connector: likelihood gaps are Eisenstein mass shells

The pair-sector search in Section 20 now has an exact arithmetic solution. See

`docs/drafts/pipeline/3-formalized/needs-audit/theta-likelihood-eisenstein-mass-shell-orientation.md`

and

`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodEisensteinMassShell.lean`.

For the atomic likelihood gaps \(t_n=n^2-1\), every ordered pair satisfies

\[
(t_n+1)(t_m+1)=(nm)^2,
\]

or, in energy--displacement coordinates,

\[
(t_n+t_m+2)^2-(t_n-t_m)^2=4(nm)^2.
\]

Conversely, because all indices are nonnegative, equality with \(k^2\) detects \(nm=k\)
exactly. Thus the product fibres that carry the divisor coefficients in the
Wigner--Bessel--Eisenstein expansion are not merely analogous to pair sectors of the latent
likelihood law: they are its integral shifted-gap mass shells.

The phase coordinate also agrees exactly:

\[
\frac{\log n-\log m}{2}
=\frac{\log(t_n+1)-\log(t_m+1)}4.
\]

Hence the complete likelihood-shell phase

\[
\Phi_k(z)=\sum_{nm=k}
 \exp\!\left(\frac{i z}{4}
 [\log(t_n+1)-\log(t_m+1)]\right)
\]

is literally the already formalized centered product-fibre/divisor phase. Unique factorization
therefore gives, unconditionally, for every \(k>1\) and \(\operatorname{Im}z>0\),

\[
\Im\bigl(\Phi'_k(z)\overline{\Phi_k(z)}\bigr)<0,
\qquad \Phi_k(z)\ne0.
\]

This is genuine sign progress: arithmetic phase orientation is complete inside every atomic
product shell. It is not a global RH proof. The Wigner divisor character is the real-boundary
specialization

\[
\tau_b(k)=\sum_{nm=k}(m/n)^{ib}=\Phi_k(-2b),
\]

while strict current holds in the open analytic half-plane. The full source also contains
Hermitian conjugate polarization, index-dependent positive-half-line windows, and the continuous
likelihood rays. Existing absolute convergence groups every ordered atom pair by its unique
product mode, so no additional cross-mode current is created by this regrouping.

The connector corrects the tempting interpretation of the first new convolution atom. The pair
\((3,3)=(t_2,t_2)\) is the central divisor point \((2,2)\) on mode \(k=4\), but its rapidity is zero.
It is current-neutral alone. Orientation belongs to the completed mode-four shell, including its
reflected off-diagonal pairs, not to the isolated atom at total gap \(6\). Lean formalizes this
correction together with the mass-shell law, phase equality, strict current, and zero-freeness.

## 22. New exact stopping point: intra-shell Hermitian/seam domination

The open frontier has moved. Do not keep attacking individual atom pairs, individual divisor
fibres, or one-particle stochastic order. Exact atomic-shell phase is already oriented, and full
theta current is already an absolutely convergent sum of actual product-fibre currents. Each
ordered pair has one unique product, so “cross-shell interference” is not the missing term. The
remaining producer theorem is:

> In the exact decomposition
> \[
> C_k(z)=|F_c(z)|^2
> \operatorname{Im}\bigl(\Phi'_k(z)\overline{\Phi_k(z)}\bigr)+S_k(c,z),
> \]
> prove after cofinal summation that the complete corrected seams \(S_k\)—Hermitian-polarization
> defect plus all oriented endpoint windows—are dominated by the favorable likelihood-shell
> bases on the target strip.

Concretely, start from the Wigner--Eisenstein expansion in
`theta-wigner-eisenstein-orientation-current.md`. Rewrite its divisor character as
\(\Phi_k(-2b)\) via Section 21, then use
`thetaProductFiberActualPhaseCurrent_eq_likelihoodMassShellBase_add_correctedSeam` to retain the
whole positive-half-line correction. Do not replace the index-dependent windows by one scalar
Bessel/radial weight: that erases the actual seam.

The first nontrivial shell already shows why this is hard. At the explicit point

\[
z_*=\frac{\pi}{\log 2}+\frac{i}{4},
\]

Lean proves the coherent likelihood-shell current for \(k=2\) is strictly negative while the
seam-free Hermitian common-unit-tail current is strictly positive. Thus conjugate polarization
can reverse the arithmetic phase sign even before endpoint windows appear. This is exposed in
likelihood coordinates by `thetaCuspLikelihoodMassShell_two_hermitian_sign_reversal`.

Promising theorem shapes are sharply constrained:

1. an exact completed-square identity for the **joint** polarization-plus-window seam;
2. a conditionally positive kernel coupling reflected factor pairs to their nested swept windows;
3. a cofinal cancellation law for the signed series \(\sum_k S_k(c,z)\) strong enough to dominate
   the summed favorable bases.

Any proof must control polarization and windows together, not merely reprove per-mode phase sign
or estimate seam pieces separately. The mode-two reversal already retires naïve radial
sign-preservation.

RH and global Hedenmalm current positivity remain open. This continuation has overcome one real
frontier problem—the missing arithmetic identification and orientation of the atomic pair
sectors—and connected that orientation to the actual fibre current. Unsolved core is now exact
joint-seam domination, with sign reversal localized on the first nontrivial shell.

## 23. Verification of the mass-shell/current connector

- direct `lake env lean GaloisForLFunctions/RHTower/ThetaCuspLikelihoodEisensteinMassShell.lean`
  passed;
- final targeted
  `lake build GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEisensteinMassShell` passed;
- temporary `#print axioms` checks for mass-shell algebra, phase orientation, actual-current
  bridge, sign reversal, and zero-freeness report only `propext`, `Classical.choice`, and
  `Quot.sound`;
- generated formal API was regenerated and `scripts/formal_tools.py lint --check-generated`
  passed;
- no stale `lake`, `lean`, or formal-tool process remained.

## 24. Frontier advance: modular endpoint is carried by an infinite likelihood ray

The modular seam now has an exact source-level boundary law. See

`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/theta-likelihood-ray-boundary-residue.md`

and

`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodRayBoundaryResidue.lean`.

Write

\[
g_n=n^2-1,
\quad A_n=e^{-3g_n/2}n^4,
\quad R_n=e^{-3g_n/2}\frac32n^2g_n,
\]

and let $L(B)$ be the already formalized higher-likelihood Laplace response. Its atom-plus-ray
decomposition gives

\[
L(B)=\sum_{n\ge2}e^{-Bg_n}\left(A_n+\frac{R_n}{B}\right).
\]

The new theorem identifies the exact positive residue

\[
R_*=\sum_{n\ge2}R_n>0,
\qquad \lim_{B\downarrow0}B L(B)=R_*.
\]

This is not an estimate. The first term vanishes under boundary scaling and the continuous ray
sector alone survives. Consequently the positive higher-likelihood measure has infinite total
mass, and the unscaled response has no finite right-boundary limit. Any finite positive carrier
necessarily loses the nonzero modular endpoint and therefore cannot replace the ray sector.

More importantly, the residue is forced atom by atom by the theta source itself. If $x_*$ is any
point with $B(x_*)=\pi e^{2x_*}-3/2=0$, and

\[
C(x)=4\pi e^{x/2}e^{2x}e^{-\pi e^{2x}}>0,
\]

then for every natural $n$,

\[
\operatorname{thetaCuspSourceTerm}(x_*,n)=C(x_*)R_n.
\]

Hence

\[
\operatorname{thetaCuspFullSource}(x_*)=C(x_*)R_*>0.
\]

This explains exactly how modular completion crosses the apparent first-atom zero: the zero is
cancelled by a positive simple pole supplied by infinite Lebesgue rays. Internal and accessible
external searches found no prior statement of this nonlinear likelihood-coordinate atomwise law;
it remains labelled candidate source-specific novelty, with no priority claim.

## 25. Frontier advance: prime shells return in the first boundary layer

Zeroth-order boundary scaling initially exposes a sharp no-go. Since $R_1=0$, every prime
product shell contains a ground leg and its pure ray-residue phase vanishes identically, together
with its derivative. Thus the modular endpoint kills every prime shell at order zero.

The positive survivor is stronger and resolves the next transition exactly. Define

\[
S_n(B)=e^{-Bg_n}(B A_n+R_n).
\]

The ground coefficient is $S_1(B)=B$. If $p$ is prime, unique factorization leaves only
$(1,p)$ and $(p,1)$, so the complete scaled shell factors as

\[
\Phi_p^{\mathrm{scaled}}(B,z)=B S_p(B)\Phi_p(z),
\qquad
(\Phi_p^{\mathrm{scaled}})'(B,z)=B S_p(B)\Phi_p'(z).
\]

For every $B>0$, $S_p(B)>0$; therefore the strict upper-half-plane current from Section 21
survives throughout the approach to the endpoint. More sharply,

\[
B^{-1}\Phi_p^{\mathrm{scaled}}(B,z)\longrightarrow R_p\Phi_p(z),
\qquad
B^{-1}(\Phi_p^{\mathrm{scaled}})'(B,z)\longrightarrow R_p\Phi_p'(z).
\]

The limiting first-layer current is $R_p^2$ times the atomic prime current and is strictly
negative for $\operatorname{Im}z>0$. Prime annihilation is therefore exactly first order, not a
loss of arithmetic orientation. The carrier is now explicit: ground-atom/higher-ray cross term.

This overcomes the carrier-identification part of the previous open frontier. It does **not** by
itself authorize insertion into the Fourier window: the two Wigner legs have different intrinsic
temperatures. Section 27 gives the corrected two-temperature transport. Remaining core is a
trace-to-bulk theorem from those actual boundary faces into the complete Wigner interior.

Do not return to raw atomic shells, pure ray residue, finite positive carriers, or channelwise
total positivity. Those routes now have exact closure theorems. RH and global Hedenmalm current
positivity remain open.

## 26. Verification of the ray-residue and first-layer connector

- direct
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspLikelihoodRayBoundaryResidue.lean` passed;
- final targeted
  `lake build GaloisForLFunctions.RHTower.ThetaCuspLikelihoodRayBoundaryResidue` passed;
- temporary `#print axioms` checks for atomwise boundary law, infinite mass, simple-pole limit,
  prime-shell annihilation, normalized first-layer limits, and strict first-layer current report
  only `propext`, `Classical.choice`, and `Quot.sound`;
- generated formal indexes were regenerated and
  `scripts/formal_tools.py lint --check-generated` passed;
- no numerical computation enters any statement or proof.

## 27. Hostile correction: common likelihood temperature is not a Wigner coordinate

The proposed next move in Section 25 fails as originally phrased. In a Wigner pair

\[
k(y+t)k(y-t),
\]

the two source legs carry independent intrinsic temperatures

\[
B_+=B(y+t),\qquad B_-=B(y-t).
\]

There is no identity $B_+=B_-$ away from the diagonal. Therefore the common-temperature prime
first-layer theorem cannot be inserted directly into the Fourier/Bezoutian integral. Doing so
would repeat the category-substitution errors already retired for likelihood moments and
translation Gram kernels.

The failure points to a stronger representation. Treat $(B_+,B_-)$ as normal-crossing
coordinates and study the union of the two genuine boundary faces $B_-=0$ and $B_+=0$, rather
than only the artificial common corner $B_+=B_-=0$.

## 28. New source theorem: prime conormal is rigid along both boundary faces

See

`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/theta-likelihood-normal-crossing-prime-face.md`

and

`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodNormalCrossingPrimeFace.lean`.

First, the scaled likelihood channel is globally the exact theta-atom coefficient. For every real
$x$ and every natural $n$, with no positivity assumption on $B(x)$,

\[
\operatorname{thetaCuspSourceTerm}(x,n)
 =C(x)S_n(B(x)),
\]

where

\[
S_n(B)=e^{-B(n^2-1)}(B A_n+R_n).
\]

This removes all division by $B$: the likelihood ray pole is a feature of splitting the
coefficient into atom and ray pieces, while their scaled sum is the literal original theta atom.

For independent temperatures define

\[
\Pi_k(B,D;z)=\sum_{nm=k}S_n(B)S_m(D)
 e^{\frac{i}{2}(\log n-\log m)z}.
\]

On the two boundary faces put

\[
F_k(B;z)=\Pi_k(B,0;z)+\Pi_k(0,B;z).
\]

If $p$ is prime, its only ordered factor pairs are $(1,p)$ and $(p,1)$. Since
$S_1(B)=B$, $S_1(0)=0$, and $S_p(0)=R_p$, Lean now proves the exact rigidity law

\[
F_p(B;z)=B R_p\Phi_p(z),
\qquad
F_p'(B;z)=B R_p\Phi_p'(z).
\]

Thus, for every nonzero face coordinate $B$,

\[
B^{-1}F_p(B;z)=R_p\Phi_p(z).
\]

The normalized conormal is independent of position along the face and equals the corner
first-boundary-layer limit from Section 25. This is the exact transport missing from the invalid
common-temperature substitution.

The result also holds for literal theta-source traces. At the zero-likelihood point $x_*$, define

\[
G_k(x;z)=\sum_{nm=k}
 [\theta_n(x)\theta_m(x_*)+\theta_n(x_*)\theta_m(x)]
 e^{\frac{i}{2}(\log n-\log m)z}.
\]

For every prime $p$,

\[
G_p(x;z)
 =C(x)C(x_*)B(x)R_p\Phi_p(z).
\]

All scalar factors are positive when $B(x)>0$. Hence for every
$\operatorname{Im}z>0$,

\[
\Im(G_p'(x;z)\overline{G_p(x;z)})<0.
\]

This is real frontier progress: a prime-oriented phase has been transported from an auxiliary
equal-temperature corner to actual two-ended theta-source boundary traces. It remains weaker than
RH. Boundary orientation does not yet control the two-temperature bulk or composite endpoint
windows, and restricting to prime faces cannot be allowed to factor the completed source through
a disconnected prime-axis quotient.

The new open core is:

> Prove a source-specific trace-to-bulk identity or positivity law carrying the rigid paired-face
> current through the complete two-temperature Wigner interior and corrected product-fibre
> windows while retaining composite coupling.

## 29. Verification of normal-crossing prime-face rigidity

- direct
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspLikelihoodNormalCrossingPrimeFace.lean`
  passed;
- final targeted
  `lake build GaloisForLFunctions.RHTower.ThetaCuspLikelihoodNormalCrossingPrimeFace` passed;
- temporary `#print axioms` checks for exact source desingularization, prime two-face
  factorization, normalized conormal rigidity, and both strict-current capstones report only
  `propext`, `Classical.choice`, and `Quot.sound`;
- generated formal indexes were regenerated and
  `scripts/formal_tools.py lint --check-generated` passed;
- no numerical computation enters any statement or proof, and no Lean or lake process remains.

## 30. Frontier advance: arithmetic normal crossing now reaches the two-temperature bulk

See

`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/theta-likelihood-swap-bulk-arithmetic-stratification.md`

and

`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodSwapBulkStratification.lean`.

Section 28 left a precise representation problem: a boundary-face current cannot be transported
by setting the two Wigner temperatures equal. The correct operation is leg exchange. Define

\[
\Sigma_k(B,D;z)=\Pi_k(B,D;z)+\Pi_k(D,B;z).
\]

This retains the independent temperatures and every ordered factor pair. Lean proves, for every
shell $k$,

\[
\Sigma_k(B,0;z)=F_k(B;z),
\qquad
\Sigma_k(0,0;z)=2\Psi_k(z),
\]

where $F_k$ is the paired boundary face and $\Psi_k$ is the complete ray--ray corner shell. Thus
$\Sigma_k$ is an exact two-temperature bulk extension of the earlier boundary object, not a new
unrelated carrier.

The corner now has a sharp arithmetic interpretation. Put

\[
M_k=\sum_{nm=k}R_nR_m.
\]

For every $k>1$, Lean proves the exhaustive classification

\[
M_k=0\iff k\text{ is prime},
\qquad
M_k>0\iff k\text{ is composite}.
\]

Prime shells vanish at zeroth normal-crossing order because every factorization has a ground leg.
Every composite shell contains a factorization with both indices at least two, producing one
strictly positive ray--ray term. This prevents the bulk construction from secretly factoring
through a disconnected prime-axis quotient: composite coupling is exactly the positive corner
mass.

For a prime $p$, leg exchange produces a stronger rigidity law throughout the closed nonnegative
temperature quadrant:

\[
\Sigma_p(B,D;z)
 =[B S_p(D)+D S_p(B)]\Phi_p(z).
\]

If $B,D\ge0$ and $B+D>0$, the scalar is strictly positive. Hence for every
$\operatorname{Im}z>0$,

\[
\Im\!\left(
 \Sigma_p'(B,D;z)\overline{\Sigma_p(B,D;z)}
\right)<0.
\]

One theorem now covers both boundary faces and every positive interior point. This is the first
exact trace-to-bulk transport in the intrinsic two-temperature likelihood coordinates.

The same transport is literal at source level. For the leg-exchange theta trace

\[
\mathcal S_k(x,y;z)=\sum_{nm=k}
 [\theta_n(x)\theta_m(y)+\theta_n(y)\theta_m(x)]
 e^{\frac{i}{2}(\log n-\log m)z},
\]

the global atomwise source law gives

\[
\mathcal S_k(x,y;z)
 =C(x)C(y)\Sigma_k(B(x),B(y);z)
\]

for every shell, including composites. Prime source traces therefore have strict negative current
whenever $B(x),B(y)\ge0$, $B(x)+B(y)>0$, and $\operatorname{Im}z>0$.

This advances the frontier but does not prove RH. The swap-invariant algebraic source bulk is now
under control; the remaining producer is the analytic current of the nonzero composite residual
together with its exact corrected positive-half-line endpoint windows. Do not return to
equal-temperature substitution or prime-only quotients.

## 31. Verification of swap-bulk arithmetic stratification

- direct
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspLikelihoodSwapBulkStratification.lean`
  passed without diagnostics;
- final targeted
  `lake build GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSwapBulkStratification` passed;
- temporary `#print axioms` checks for boundary restriction, both corner classifiers, prime bulk
  factorization/current, exact source transport, and literal source current report only `propext`,
  `Classical.choice`, and `Quot.sound`;
- generated formal indexes were regenerated and
  `scripts/formal_tools.py lint --check-generated` passed;
- no numerical computation enters any statement or proof.

## 32. Frontier correction: prime-square diagonal is exact orientation defect

See

`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/theta-likelihood-prime-square-conormal-sign-wall.md`

and

`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodPrimeSquareSignWall.lean`.

Section 30 established strict negative current for prime shells and left composite residual current
as open core. The proposed universal nonpositive extension to all composite shells is now ruled
out exactly, already on every prime square.

For prime $p$, set $\lambda=\log p$ and

\[
E_p(B,D)=B S_{p^2}(D)+D S_{p^2}(B),
\qquad
C_p(B,D)=2S_p(B)S_p(D).
\]

The full $p^2$ factor packet is

\[
(1,p^2),\quad(p,p),\quad(p^2,1),
\]

with rapidities $-\lambda,0,+\lambda$. Therefore the swap shell and its derivative are exactly

\[
\Sigma_{p^2}=E_p(e^{-i\lambda z}+e^{i\lambda z})+C_p,
\qquad
\Sigma'_{p^2}=i\lambda E_p(e^{i\lambda z}-e^{-i\lambda z}).
\]

On the reflection wall $z=\pi/\lambda+iy$, $y>0$, Lean proves

\[
J_{p^2}
=2\lambda E_p\sinh(\lambda y)
  \bigl[C_p-2E_p\cosh(\lambda y)\bigr].
\]

Thus current has a sharp diagonal-versus-endpoint sign wall. More decisively, on $D=0$,

\[
\lim_{B\to0^+}\frac{J_{p^2}(B,0)}{B}
=4\lambda R_{p^2}\sinh(\lambda y)R_p^2>0.
\]

For every prime and every positive wall height, raw composite current is positive for all
sufficiently small positive $B$. No estimate, zero table, or RH assumption enters this
counterexample. Raw swap-bulk orientation is not an RH route.

The obstruction also supplies an exact correction. Remove only the stationary diagonal amplitude
$C_p$ from the phase, leaving its derivative unchanged. The renormalized current is

\[
\widehat J_{p^2}
=-4\lambda E_p^2\sinh(\lambda y)\cosh(\lambda y)<0
\]

throughout $B,D\ge0$, $B+D>0$, $y>0$. Hence square-diagonal subtraction is no longer a heuristic:
it exactly restores prime orientation on every prime-square reflection wall.

This is the representation-level advance. Composite corner mass must remain present in the source,
but its zero-rapidity diagonal component cannot remain unprojected inside the orientation current.
The next open core is:

> Construct a source-intrinsic diagonal projection for every squareful product fibre, prove
> compatibility with the completed theta trace and corrected positive-half-line endpoint windows,
> and determine whether the projected composite current has a global upper-half-plane sign.

Do not spend effort estimating raw composite current: its desired sign is now formally false.

## 33. Verification of prime-square sign wall and diagonal correction

- direct
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspLikelihoodPrimeSquareSignWall.lean`
  passed without diagnostics;
- final targeted
  `lake build GaloisForLFunctions.RHTower.ThetaCuspLikelihoodPrimeSquareSignWall` passed;
- temporary `#print axioms` checks for factor-packet classification, raw wall identity and sign
  classifier, diagonal-renormalized strict sign, conormal limit, residue positivity, and positive
  witnesses report only `propext`, `Classical.choice`, and `Quot.sound`;
- generated formal indexes were regenerated and
  `scripts/formal_tools.py lint --check-generated` passed;
- no numerical computation enters any statement or proof.

## 34. Corpus frontier correction: prime-cube Lee--Yang cone

See

`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/theta-likelihood-prime-cube-lee-yang-cone.md`,

`docs/drafts/pipeline/5-failed/theta-likelihood-zero-rapidity-diagonal-projection.md`,

and

`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodPrimeCubeLeeYangCone.lean`.

The actual corpus stopping point must be kept explicit.  It is not local divisor-phase
orientation: `thetaProductFiberCenteredPhase_current_lt_zero` already settles every complete
unweighted product fibre.  It is not a favorable replacement carrier either.  The exact corpus
identities are

\[
C_k(z)=B_k(c,z)+S_k(c,z),
\]

where \(C_k\) is actual Hermitian positive-half-line fibre current, \(B_k\) is coherent oriented
divisor base, and \(S_k\) is complete polarization-plus-window seam.  Moreover the centered-seam
no-go proves \(C_k\le S_k\) in upper half-plane, and finite-arithmetic/Haar conservation returns
raw current as surviving remainder.  Thus replacing \(C_k\) by \(B_k\), even canonically, solves
a surrogate.  Unconditional raw theta-tail current control remains RH-bearing frontier; corpus
formalizes its scaled anisotropic form as equivalent to RH.

Scientific-method test was applied to Section 32 proposal.

**Conjecture H0.** Zero-rapidity diagonal modes are complete composite orientation defect.

**Falsifiable prediction.** First odd prime power, which has no diagonal, should retain strict
negative upper-half-plane current without correction.

**Test.** For prime \(p\), let \(L=\log p\).  Complete \(p^3\) likelihood boundary packet is

\[
F_{a,b,L}(z)
=a(e^{-3iLz/2}+e^{3iLz/2})
 +b(e^{-iLz/2}+e^{iLz/2}).
\]

Its coefficient polynomial is

\[
P_r(X)=1+rX+rX^2+X^3
      =(X+1)(X^2+(r-1)X+1),
\qquad r=b/a.
\]

Lean proves exact global classifier

\[
\bigl[\forall\,\operatorname{Im}z>0,
  \operatorname{Im}(F'\overline F)<0\bigr]
\iff b\le3a.                                             \tag{34.1}
\]

Sufficiency is existing corpus unit-circle-root orientation.  Necessity is explicit.  On
\(z=\pi/L+iy\),

\[
J=-L\sinh(Ly)
 [b-a(2\cosh(Ly)+1)]
 [b-a(6\cosh(Ly)-3)].                                   \tag{34.2}
\]

If \(b>3a\), choose \(Ly=\operatorname{arcosh}(b/(3a))\); factors in (34.2) have opposite signs,
so \(J>0\).

For actual source face \(D=0\), coefficients are

\[
a_p(B)=B R_{p^3},
\qquad
b_p(B)=S_p(B)R_{p^2}+R_pS_{p^2}(B).
\]

At \(B=0\), \(a_p(0)=0\) while \(b_p(0)=2R_pR_{p^2}>0\).  Continuity gives

\[
b_p(B)>3a_p(B)
\]

for every sufficiently small \(B>0\).  Lean then supplies an upper-half-plane point with positive
actual shell current.  Separately, Lean classifies all four factor pairs and proves every
rapidity is nonzero.  Diagonal projection acts identically and fails.

**Verdict.** H0 is false.  Positive survivor is sharp Lee--Yang coefficient cone (34.1): composite
orientation is root-confinement problem for full palindromic coefficient packet, not stationary
mode deletion.

This is frontier progress, not RH proof.  It prevents another local correction from being mistaken
for raw-source theorem and gives exact hostile gate any source-compatible seam mechanism must pass.

### Next corpus-native conjecture

`[CONJECTURE]` Apply Schur/Lee--Yang defect factorization only after forming finite **completed
cofinal source packet**, before product-fibre/Haar separation.  Reciprocal root defects of this
global packet should equal complete modular Hermitian/window seam plus one remote boundary term;
remote term should vanish under source cofinal limit.  This ordering is essential: per-fibre
projection is refuted by \(p^3\), while post-Haar endpoint tuning is refuted by conserved survivor.

Required first experiment is exact and symbolic, not estimative:

1. construct smallest completed cofinal packet containing \(p^2\) and \(p^3\) strata;
2. prove reciprocal polynomial symmetry and exact Schur defect identity;
3. identify defect with existing complete seam by equality, not domination;
4. test whether remainder is sole modular remote row.  If any extra local term survives, retire
   conjecture before asymptotic work.

## 35. Verification of prime-cube frontier test

- direct
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspLikelihoodPrimeCubeLeeYangCone.lean`
  passed;
- final targeted
  `lake build GaloisForLFunctions.RHTower.ThetaCuspLikelihoodPrimeCubeLeeYangCone` passed;
- temporary `#print axioms` checks for unit-root classification, sharp global iff, no-zero-rapidity
  packet, exact source identity, eventual anti-cone exit, and eventual positive-current witnesses
  report only `propext`, `Classical.choice`, and `Quot.sound`;
- `scripts/formal_tools.py lint` passed;
- no numerical computation enters any statement or proof.

## 36. Frontier correction: continuous full-density contraction, not scalar prime polynomial

See

`docs/drafts/pipeline/5-failed/cofinal-completed-lee-yang-seam-defect.md`,

`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/full-theta-density-monotone-completion-current.md`,

`docs/drafts/pipeline/5-failed/xi-taylor-full-density-transfer-wronskian.md`,

`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/xi-full-density-source-exchange-obstruction.md`,

`docs/drafts/pipeline/1-in-progress/xi-completed-density-projective-heteroclinic-barrier.md`,

and

`formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailFullDensityMonotoneCurrent.lean`.

Section 34 conjectured a scalar cofinal self-reciprocal phase polynomial.  Corpus hostile test kills
that carrier before root analysis.  A one-variable phase polynomial requires frequencies in one
affine lattice, while corpus proves prime-log linear independence, aperture character rank
`pi(N)`, and no fixed finite carrier.  A prime polydisk does not restore actual completion:
`SeamArchimedeanSamplingQuotient.lean` proves continuous archimedean seam does not factor through
prime-power samples, or even all positive integer-log samples.  Scalar/discrete-only cofinal
Lee--Yang route is retired.

Positive survivor retains continuous archimedean density.  Put

\[
\rho(t)=4T''(t),\qquad
F(z)=\int_0^\infty \rho(t)e^{itz}\,dt,\qquad
D(z)=\int_0^\infty it\rho(t)e^{itz}\,dt,
\]

and $h(t)=-\rho'(t)$.  Corpus strict monotonicity gives $h(t)>0$ for $t\ge0$.  Exact
integrations by parts give

\[
G_h(z)=\int_0^\infty h(t)(1-e^{itz})\,dt=-izF(z),
\]

\[
G_h'(z)=-i(F(z)+zD(z)).                                  \tag{36.1}
\]

For $\operatorname{Im}z>0$ every completion integrand has positive real part because
$|e^{itz}|=e^{-t\operatorname{Im}z}<1$.  Hence $F(z)\ne0$.  Pointwise inequality

\[
t e^{-ty}\le \frac{1-e^{-ty}}{y},\qquad y>0,
\]

then yields

\[
|D(z)|\le\frac2{\operatorname{Im}z}|F(z)|,
\quad
\left|\frac{D(z)}{F(z)}\right|\le\frac2{\operatorname{Im}z},
\]

\[
|\operatorname{Im}(D(z)\overline{F(z)})|
 \le\frac2{\operatorname{Im}z}|F(z)|^2.                 \tag{36.2}
\]

Global product-fibre bridge converts left side of (36.2) into absolutely convergent sum of every
actual Hermitian product-fibre current.  This is exact answer to prime-cube obstruction: bad local
faces do occur, but full continuous source forces aggregate cancellation.  No individual fibre is
estimated or assigned false sign.

This is frontier progress, not RH proof.  Full transform $F$ is untruncated one-sided channel;
RH-bearing object is finite odd Xi Taylor section.

## 37. Exact RH-equivalent transfer bridge

Zero-freeness of $F$ makes following factor canonical throughout upper half-plane:

\[
T_d(z)=\frac{P_{2d+3}(z)}{F(z)}.
\]

Lean formalizes quotient-rule derivative and division-free product-current identity

\[
J(P_{2d+3})=|T_d|^2J(F)+|F|^2J(T_d).                    \tag{37.1}
\]

Combining (36.2) and (37.1) preserves final Taylor denominator exactly:

\[
J(P_{2d+3})(z)
 \le \frac2{\operatorname{Im}z}|P_{2d+3}(z)|^2
     +|F(z)|^2J(T_d)(z).                                \tag{37.2}
\]

On every left-strip anisotropic mesh, $2/\operatorname{Im}z_n=O(1)=o(n)$.  Forward and reverse
transport through (37.1), using existing anisotropic coefficient-current equivalence, proves

\[
\texttt{XiCTaylorFullDensityTransferCurrentSublinearUpper D}
\iff \mathrm{RH}.                                       \tag{37.3}
\]

Equation (37.3) is a correct RH-equivalent gauge bridge.  What has been removed unconditionally is
entire untruncated density/arithmetic current, including all polarization/window seams after full
recombination.  It was initially interpreted as concentrating remaining RH content in finite
truncation transfer.  Section 38 corrects that interpretation by exact hostile test.

Verification of source theorem and bridge:

- direct
  `lake env lean GaloisForLFunctions/RHTower/XiCTaylorThetaTailFullDensityMonotoneCurrent.lean`
  passed;
- final targeted
  `lake build GaloisForLFunctions.RHTower.XiCTaylorThetaTailFullDensityMonotoneCurrent` passed;
- axiom audit of completion identities, strict right-half-plane theorem, zero-freeness,
  logarithmic-derivative disk, aggregate fibre-current bound, transfer factorization, and RH
  equivalence reports only `propext`, `Classical.choice`, and `Quot.sound`;
- `scripts/formal_tools.py lint` passed;
- no numerical computation enters any statement or proof.

## 38. Frontier correction: transfer retains full Xi divisor

First symbolic experiment on proposed source Wronskian is decisive.  For two positive full phases,

\[
(ixe^{ixz})e^{itz}-e^{ixz}(ite^{itz})
 =i(x-t)e^{i(x+t)z}.                                  \tag{38.1}
\]

This vanishes exactly when $x=t$, not identically.  Antisymmetric integration cancels only for
the same source measure.  Here $P_d$ carries completed source \(\Phi\) and even cosine phase,
while $F$ carries \(\rho=T+4\Phi\) and one-sided exponential phase.  Proposed full-channel
cancellation is false before estimates.

Put

\[
W_d=P_{2d+3}'F-P_{2d+3}F',\quad
\Omega_F=\Xi_C'F-\Xi_CF',\quad
R_d=\Xi_C-P_{2d+3}.
\]

Exact algebra gives

\[
W_d=\Omega_F-(R_d'F-R_dF').                            \tag{38.2}
\]

Local-uniform Taylor convergence, including derivatives, yields

\[
W_d(z)\longrightarrow\Omega_F(z).                     \tag{38.3}
\]

Background is unconditionally nonzero.  Xi parity gives \(\Xi_C'(0)=0\), while positivity of
\(\rho\) gives

\[
F'(0)=i\int_0^\infty t\rho(t)\,dt\ne0,
\quad
\Omega_F(0)=-\Xi_C(0)F'(0)\ne0.                       \tag{38.4}
\]

Therefore $W_d$ is not a vanishing Taylor-remainder object.  More strongly, if

\[
Q=\Xi_C/F,
\]

then pointwise

\[
T_d\to Q,\qquad T_d'\to Q',\qquad J(T_d)\to J(Q),      \tag{38.5}
\]

and $Q(z)=0\iff\Xi_C(z)=0$ for \(\operatorname{Im}z>0\).  Thus transfer current retains full Xi
divisor.  Description “finite-truncation transfer” is retired; (37.3) is gauge reformulation, not
new source producer.

Completed reflection exposes exact survivor.  With $F_-=F(-z)$, $D=F'(z)$,
$D_-=F'(-z)$, and $q=z^2+1/4$, define

\[
\mathcal C_F
 =2z(F+F_-)F-q(D_-F+F_-D)+\tfrac12D.
\]

Then

\[
\mathcal C_F=8z\Xi_CF+4z^2\Omega_F.                   \tag{38.6}
\]

At simple upper-strip Xi zero, \(\mathcal C_F=4z^2\Xi_C'F\ne0\).  Full survivor is reflected
growing channel plus central seam—the zero signal proposed cancellation would erase.

### Actual unsolved frontier

Let

\[
E=(z^2+1/4)F(z)-1/4,\qquad
E^\#=(z^2+1/4)F(-z)-1/4.
\]

Corpus proves

\[
E+E^\#=4z^2\Xi_C.                                     \tag{38.7}
\]

Away from $z=0$, off-axis Xi zero is exact antipodal collision $E^\#=-E$.  Corpus also proves
global completed-density de Branges gap \(|E|>|E^\#|\) is false in open critical half-strip.
Section 39 corrects first collision-only conjecture after differentiating actual projective ratio.

Formal module:
`formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailFullDensityWronskianNoGo.lean`.

Verification:

- direct
  `lake env lean GaloisForLFunctions/RHTower/XiCTaylorThetaTailFullDensityWronskianNoGo.lean`
  passed;
- final targeted
  `lake build GaloisForLFunctions.RHTower.XiCTaylorThetaTailFullDensityWronskianNoGo` passed;
- axiom audit of kernel classification, exact remainder decomposition, reflected connection,
  simple-zero survivor, central noncancellation, pointwise Wronskian limit, quotient zero set, and
  transfer-current limit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- `scripts/formal_tools.py lint` passed;
- no numerical computation enters any statement or proof.

## 39. Projective correction: frontier is unanchored heteroclinic, not no-return

Hostile derivative audit of section 38 changes active conjecture materially.  Put

\[
R=\frac{E^\#}{E},\qquad
\mathcal W_E=(E^\#)'E-E^\#E'.
\]

Then on regular chart

\[
R'=\frac{\mathcal W_E}{E^2}.                          \tag{39.1}
\]

Previous full-density connection \(\mathcal C_F\) differentiates \(\Xi_C/F\), not
\(E^\#/E\).  Exact completed reflection gives

\[
\mathcal W_E
 =8z\Xi_CE+4z^2(\Xi_C'E-\Xi_CE'),                    \tag{39.2}
\]

and at every Xi zero

\[
\mathcal W_E=4z^2\Xi_C'E,\qquad
\mathcal W_E-(z^2+\tfrac14)\mathcal C_F=-z^2\Xi_C'.  \tag{39.3}
\]

Thus two connections are unequal at every noncentral simple collision.  Nonvanishing of
\(\mathcal C_F\) cannot control projective ratio flow.

Define division-free tangent vector

\[
V_E=E^2\overline{\mathcal W_E}.
\]

Formal algebra proves exact flow law

\[
dR(V_E)=|\mathcal W_E|^2.                             \tag{39.4}
\]

Therefore on every regular component of
\(R^{-1}(( -\infty,0))\), ratio is already strictly monotone.  “No return while connection is
nonzero” is generic and cannot prove RH: off-axis zero may occur once on an unanchored regular
component without any return or critical point.

Real boundary geometry is now exact.  For positive real Xi zero \(t\), source sine positivity
gives \(E(t)=i\,\operatorname{Im}E(t)\), with \(\operatorname{Im}E(t)>0\), so \(R(t)=-1\).  Inward
normal derivative is

\[
\left.\frac d{dy}R(t+iy)\right|_{y=0}
 =\frac{4t^2\operatorname{Re}\Xi_C'(t)}{\operatorname{Im}E(t)}. \tag{39.5}
\]

It is nonzero at every simple real zero; sign may vary.

### Actual corpus frontier after correction

An off-axis Xi zero is exactly a maximal projective trajectory whose real image contains \(-1\)
but which has no real boundary anchor.  Current conjecture is **no unanchored
source-to-reflection heteroclinic**: every negative-ray trajectory bracketing \(-1\) must have a
unique finite real endpoint.  Required source proof splits into negative-ray Wronskian regularity,
top-edge exclusion, horizontal theta-Schwartz escape, and projective zero/pole endpoint separation.
Global gap, innerness, Pick/Herglotz positivity, divisor assumptions, and recurrence are disallowed.

This is frontier progress, not RH proof.  It removes wrong connection and a vacuous dynamical
condition, and names exact global source trajectory corpus still cannot control.

Formal module:
`formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedDensityProjectiveCollision.lean`.

Pipeline:

- failed interface:
  `docs/drafts/pipeline/5-failed/xi-completed-density-antipodal-crossing-barrier.md`;
- formalized survivor:
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/xi-completed-density-projective-collision-geometry.md`;
- active conjecture:
  `docs/drafts/pipeline/1-in-progress/xi-completed-density-projective-heteroclinic-barrier.md`.

Verification of projective collision geometry:

- direct
  `lake env lean GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedDensityProjectiveCollision.lean`
  passed;
- targeted
  `lake build GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityProjectiveCollision`
  passed;
- temporary `#print axioms` checks for ten capstones report only `propext`, `Classical.choice`, and
  `Quot.sound`;
- `scripts/formal_tools.py lint` passed;
- no owned Lean process remained after audit.

## 40. Transverse Pick breakthrough: damped channel is zero-free; RH frontier is one top edge

Section 39 still overstates global difficulty.  Completed density supplies a rank-two inequality
strictly stronger than positive real part of its derivative completion.

Let

\[
\rho(t)=4T''(t),\qquad
F(z)=\int_0^\infty \rho(t)e^{itz}\,dt,\qquad
E(z)=(z^2+\tfrac14)F(z)-\tfrac14.
\]

Corpus already proves

\[
\rho>0,\qquad \int_0^\infty\rho=1,\qquad \rho'<0,
\]

and, with (h=-\rho'>0),

\[
G(z)=\int_0^\infty h(t)(1-e^{itz})\,dt=-izF(z).
\]

For (z=x+iy), (y>0), put

\[
e^{itz}=a(c+is),\quad a=e^{-ty},\quad c=\cos(tx),\quad s=\sin(tx),
\quad d=1-ac.
\]

Convexity of exponential and (|\sin u|\le |u|) give

\[
aty\le d,\qquad y|as|\le |x|d.
\]

After squaring and using

\[
|1-e^{itz}|^2=d^2+a^2s^2,qquad |z|^2=x^2+y^2,
\]

one obtains the pointwise transverse cone

\[
\left|\frac{i}{z}(1-e^{itz})\right|
 \le \frac{1-\operatorname{Re}e^{itz}}{y}.
\]

Integration against (h) proves the new source theorem

\[
\boxed{\;y|F(z)|\le \operatorname{Im}(zF(z))\;}      \tag{40.1}
\]

throughout upper half-plane.

### Zero-free endpoint

If (E(z)=0), then

\[
(z^2+\tfrac14)F(z)=\tfrac14.                         \tag{40.2}
\]

For (x\ne0), substitution in (40.1) forces

\[
|z^2+\tfrac14|\le \tfrac14-|z|^2.
\]

But exact identity

\[
|z^2+\tfrac14|^2-(\tfrac14-|z|^2)^2=x^2             \tag{40.3}
\]

contradicts it.  On (z=iy), positivity and unit mass give

\[
0\le F(iy)\le1.
\]

For (0<y<1/2), (40.2) would require (F(iy)>1); for (y\ge1/2), its left side is nonpositive.
Therefore

\[
\boxed{\;E(z)\ne0\quad(\operatorname{Im}z>0).\;}     \tag{40.4}
\]

This is unconditional and machine-checked.  It eliminates every upper-half-plane pole of

\[
R=E^\#/E.
\]

Hence section 39's projective zero/pole endpoint separation is not frontier.

### Direct RH deformation and failed shortcut

Define affine pencil

\[
H_\tau(z)=\frac{1+\tau}{2}E(z)+\frac{1-\tau}{2}E^\#(z),
\qquad0\le\tau\le1.
\]

Then

\[
H_1=E,\qquad H_0=2z^2\Xi_C.                           \tag{40.5}
\]

The first direct attempt was to copy (40.1) to (F(-z)), then add two cones.  This is invalid:
one-sided Fourier transform satisfies

\[
\overline{F(\bar z)}=F(-z),
\]

so reflected channel in upper half-strip is growing, not damped conjugate.  Bilateral cone would
already contain RH-grade phase information and is not inferred from density monotonicity.

Interior multiple-root collisions are also not independent extinction events.  For holomorphic
pencil (H_\tau), argument principle preserves total zero multiplicity until boundary crossing or
escape to infinity.  Thus previous demand for negative-ray Wronskian regularity was unnecessary.

### Actual frontier after corpus audit

For (\tau>0), positive real bottom edge is safe because

\[
\operatorname{Im}H_\tau(x)=\tau\operatorname{Im}E(x)>0\qquad(x>0).
\]

Positive imaginary edge (z=iy), (0<y<1/2), is safe because

\[
H_\tau=\tau E+(1-\tau)H_0,qquad E(iy)<0,\qquad H_0(iy)<0.
\]

Theta-Schwartz decay reduces horizontal infinity to uniform nonvanishing near (-1/4).  Only top
edge remains.  New source conjecture is

\[
\boxed{\;
\operatorname{Re}\!\left(
 E(x+i/2)\overline{,2(x+i/2)^2\Xi_C(x+i/2),}
\right)>0\quad(x>0).
\;}                                                     \tag{40.6}
\]

This **top-edge acute-angle conjecture** implies (H_\tau(x+i/2)\ne0) for every
(0<\tau\le1).  Indeed

\[
\operatorname{Re}(H_\tau\overline{H_0})
=\tau\operatorname{Re}(E\overline{H_0})+(1-\tau)|H_0|^2>0,
\]

and (H_0) is nonzero on top edge by classical zero-free line (\operatorname{Re}s=1).

Argument principle on truncated positive half-strip would then transfer zero count from zero-free
(H_1) to every (H_\tau), (\tau>0); Hurwitz limit (\tau\downarrow0) makes (H_0) zero-free
inside.  Symmetry gives RH.  No simplicity assumption is needed.

Therefore actual research-corpus frontier is now exact:

> prove top-edge acute-angle law (40.6), or sharp nonintersection
> (H_\tau(x+i/2)\ne0), from joint half-density Ward source; do not seek more bulk estimates,
> projective recurrence, or interior collision regularity.

Formal module:
`formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedDensityTransversePick.lean`.

Pipeline:

- formalized survivor:
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/xi-completed-density-transverse-pick-zero-free.md`;
- retired overbroad frontier:
  `docs/drafts/pipeline/5-failed/xi-completed-density-projective-heteroclinic-barrier.md`;
- actual active conjecture:
  `docs/drafts/pipeline/1-in-progress/xi-completed-density-affine-pencil-top-edge-barrier.md`.

Novelty status is `[NOVELTY UNVERIFIED]`.  Current primary-literature audit found adjacent Xi
Wronskian and deformation results, not exact theta-tail cone (40.1), zero-free endpoint (40.4), or
acute top-edge reduction (40.6).

Verification:

- scratch and direct `lake env lean` checks passed;
- final targeted `lake build
  GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityTransversePick` passed;
- seven `#print axioms` capstones report only `propext`, `Classical.choice`, and `Quot.sound`;
- new source contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration;
- whole-tree `scripts/formal_tools.py lint` passed (large-file warnings only);
- no owned Lean or Lake process remained.

## 41. Affine-homotopy ejection: top-edge route is false; frontier returns to source-real transport

Section 40 is superseded.  Its affine pencil is algebraically correct, but its proposed
zero-free transport is not.

Write

\[
H_0(z)=2z^2\Xi_C(z),\qquad
H_\tau(z)=\tau E(z)+(1-\tau)H_0(z),
\qquad \tau=\frac c{1+c}.
\]

The correct incidence is

\[
\iota(z)=-\frac{H_0(z)}{E(z)}.
\]

A full signed phase advance of \(2\pi\), not merely an unsigned real-axis collision, forces
\(\iota=c>0\) and therefore an actual pencil zero at \(\tau=c/(1+c)\in(0,1)\).  This signed
winding connector is now formalized.

### Exact critical-zero motion

For a general analytic deformation

\[
H(g(c))+cK(g(c))=0,qquad H(z_0)=0,\quad H'(z_0)\ne0,
\]

the analytic implicit-function theorem gives

\[
g(0)=z_0,\qquad g'(0)=-\frac{K(z_0)}{H'(z_0)}.          \tag{41.1}
\]

This has been extracted as the reusable formal theorem
`HTGeometry.exists_affineSimpleZero_branch`.  Its positive survivor is exact: if both
\(H'(z_0)\) and \(K(z_0)\) are real, then \(\operatorname{Im}g'(0)=0\).  Divisor vanishing is
unnecessarily strong; **real tangency** is the first-order condition a viable deformation must
satisfy.

At a positive real Xi zero \(t\), the completed-density source gives

\[
E(t)=i\,\operatorname{Im}E(t),\qquad \operatorname{Im}E(t)>0,
\]

while \(H_0'(t)=2t^2\Xi_C'(t)\).  Hence

\[
g'(0)=-\frac{E(t)}{2t^2\Xi_C'(t)}.                      \tag{41.2}
\]

If \(\operatorname{Re}\Xi_C'(t)<0\), then
\(\operatorname{Im}g'(0)>0\).  Lean proves more than this infinitesimal sign: for every
sufficiently small \(c>0\), the actual point \(g(c)\) lies in the open upper strip and satisfies

\[
H_{c/(1+c)}(g(c))=0.                                    \tag{41.3}
\]

Thus no top-edge estimate can make this asymmetric homotopy upper-zero-free; it already ejects a
bottom-edge target zero into the forbidden region.

### Simplicity is not needed on paper

Let \(t>0\) be a downward sign-changing Xi zero of odd order \(m\).  Locally

\[
H_0(t+\delta)=A\delta^m+O(\delta^{m+1}),\qquad A<0,
\]

and write \(E(t)=ib\), \(b>0\).  With \(\delta=c^{1/m}w\), the normalized pencil converges
uniformly on compact \(w\)-sets to

\[
Aw^m+ib.                                                 \tag{41.4}
\]

It has an upper root of argument \(\pi/(2m)\).  Rouche transfer gives an upper pencil zero for
every sufficiently small positive \(c\).  Classical Hardy sign change supplies a downward odd
critical-line crossing without any numerical zero certificate: \(\Xi_C(0)>0\), and the first
transition to a negative sign interval is downward.  Therefore the affine zero-free homotopy is
unconditionally false on paper.  The current Lean theorem is the complete simple-zero case; the
odd-order Rouche upgrade remains a formalization task.

### Actual corpus frontier

The failed affine path does not alter the exact RH wall already identified by the corpus.  It
removes a false shortcut to that wall.

In the Hedenmalm coordinate, the unresolved producer remains

\[
J_a(b)=\partial_a\left|\Xi\!\left(\tfrac12+a+ib\right)\right|^2\ge0
\quad(0<a<\tfrac12,\ b\in\mathbb R),                    \tag{41.5}
\]

equivalently the theta-specific two-ended phase-current domination inequality (40) in
`hedenmalm-center-mixed-double-positivity-law.md`.  The corpus proves exterior apertures, a full
central frequency band, finite positive-matrix chambers, and exact resolvent factorizations; it
does not produce the nonperturbative modular-seam sign in (41.5).

In the Connes coordinate, the unresolved producer is exactly
`ConnesXiGroundStateLimitWall`: construct a source-defined cofinal sequence of entire functions
with only real zeros which converges locally uniformly to \(\Xi_C\).  Finite self-adjointness and
finite real-zero characteristic functions are already available; source/divisor-preserving
convergence is not.

### Replacement conjecture and scientific test

**[CONJECTURE 41-A: anchored Donoghue--Carleman identification].**  Normalize the actual
finite-aperture Suzuki ground-state characteristic functions at one nonzero real anchor.  Their
canonical Donoghue functions form a normal Herglotz family.  After the already proved
compactified-phase tightness and residual-overcrowding elimination, every subsequential limit is
the same source-defined one-sided even Carleman quotient
\(m_{\rm ext}=-C_R/W_1\).  On the unconditional Euler half-plane, the actual right-triangle
source identity identifies this quotient before any divisor expansion.  Herglotz normality then
continues it holomorphically through the upper half-plane.  The corpus already proves that every
hypothetical nonreal Xi zero gives this quotient a universal nonzero pole germ, while the
finite-interval clock has only real zeros.  Holomorphy therefore excludes every upper off-real Xi
zero and proves RH.  This is the one-sided source-identification route; proving actual normalized
characteristic convergence to \(\Xi_C\) remains the separate `ConnesXiGroundStateLimitWall`.

This conjecture is not a new equivalent criterion.  It specifies the missing source theorem and
how to test it:

1. prove fixed-label Donoghue atom weights converge from the actual finite source, not from an Xi
   divisor expansion;
2. prove the one-sided even Carleman limit is independent of the chosen cofinal aperture sequence;
3. identify it with the actual Euler--Gamma right-triangle quotient on their common unconditional
   half-plane;
4. use Herglotz normality for holomorphic continuation and the already formalized universal Xi
   pole germ for the contradiction;
5. falsify the conjecture if any nonzero compactified escape residual survives, if two cofinal
   sequences yield different carriers, or if the high-half-plane source identity has an
   uncancelled interval term.

The real-tangent theorem is a mandatory design filter for this conjecture.  Actual finite
self-adjoint characteristic functions are Schwarz-real and move their simple zeros horizontally;
the completed-density channel \(E\) is not Schwarz-real on the boundary and fails this test.

Formal modules:

- `formal/GaloisForLFunctions/HTGeometry/AffineSimpleZeroMotion.lean`;
- `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedDensityAffinePencilEjection.lean`.

Pipeline:

- retired route:
  `docs/drafts/pipeline/5-failed/xi-completed-density-affine-pencil-top-edge-barrier.md`;
- formalized survivor:
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/xi-completed-density-affine-pencil-ejection-law.md`;
- actual Hedenmalm producer:
  `docs/drafts/pipeline/1-in-progress/hedenmalm-center-mixed-double-positivity-law.md`;
- actual Connes producer:
  `docs/drafts/pipeline/1-in-progress/xi-approximant-prime-energy-source-close.md`.

Status: substantial frontier correction and new formal motion law, **not an RH proof**.

## 42. Euler-defect germ weld: fixed Donoghue equality is false; one source germ would prove RH

Section 41's Conjecture 41-A is superseded in its literal form.  Current corpus proves that the
actual admissible affine-sewn Carleman quotient

\[
m_{\rm ext}(z)=-\frac{C_{\rm odd}(z)}{P(z)}
              =-\frac{E_R(z)-E_L(z)}{2P(z)}             \tag{42.1}
\]

and Suzuki's fixed finite-aperture Donoghue quotient have different pole divisors.  They cannot
be the same meromorphic function.  Direct convergence of the functions also retains a possible
linear Nevanlinna escape mode.  Therefore neither fixed-function identification nor an anchor by
itself is the correct frontier theorem.

Use instead the degree-one Euler defect

\[
\mathcal E[f](z)=z f'(z)-f(z).                          \tag{42.2}
\]

It kills every linear mode \(cz\), exactly removing compactified endpoint escape.  New theorem
shows that this loss of information is harmless for the RH divisor.

### Exact meromorphic pole law

If \(f\) is meromorphic at \(z_0\ne0\) and

\[
\operatorname{ord}_{z_0}f=n<0,
\]

write \(f(w)=(w-z_0)^n g(w)\), where \(g\) is analytic and \(g(z_0)\ne0\).  Then

\[
\mathcal E[f](w)=(w-z_0)^{n-1}G(w),                    \tag{42.3}
\]

with

\[
G(w)=w\{n g(w)+(w-z_0)g'(w)\}-(w-z_0)g(w),
\qquad G(z_0)=z_0n g(z_0)\ne0.                         \tag{42.4}
\]

Consequently

\[
\boxed{\operatorname{ord}_{z_0}\mathcal E[f]
       =\operatorname{ord}_{z_0}f-1.}                  \tag{42.5}
\]

The exclusion of the origin is sharp because the Euler vector field vanishes there.  It causes
no RH loss: every nonreal point is nonzero.

For actual two-shift Suzuki data, \(P\) has only real zeros.  Existing exterior tomography and
the new order theorem give, at every hypothetical nonreal Xi zero \(\rho\),

\[
\operatorname{ord}_{\rho}m_{\rm ext}=-1,
\qquad
\operatorname{ord}_{\rho}\mathcal E[m_{\rm ext}]=-2.  \tag{42.6}
\]

Thus Euler defect does not conceal an Xi pole; it upgrades it from simple to double while
annihilating the unwanted linear endpoint mode.

### One pointed source germ is enough

There is a second new theorem.  Let \(U\) be preconnected, \(f\) meromorphic on \(U\), and
\(D\) analytic on \(U\).  If at one point \(u\in U\)

\[
f=D\quad\text{as pointed germs at }u,                  \tag{42.7}
\]

then \(f-D\) has infinite meromorphic order at \(u\).  Infinite-order locus of a meromorphic
function is clopen in its domain.  Hence it is all of \(U\), and

\[
\operatorname{ord}_z f\ge0\qquad(z\in U).              \tag{42.8}
\]

Apply this on upper half-plane with \(f=\mathcal E[m_{\rm ext}]\).  If source theory constructs
one analytic function \(D_{\rm src}\) and proves only one high-half-plane pointed-germ identity

\[
\mathcal E[m_{\rm ext}]=D_{\rm src},                   \tag{42.9}
\]

then (42.8) contradicts exact double pole (42.6) at every hypothetical upper Xi zero.  Xi evenness
excludes lower zeros.  Therefore (42.9) proves RH.  No global equality of finite and exterior
quotients, no uniqueness of subsequential limits, no anchor reconstruction, and no assumed Pick
positivity are needed.

### Actual research-corpus frontier

Finite Donoghue Euler kernels vanish at both compactified spectral endpoints.  Their probability
measures therefore have natural subsequential analytic defect limits on compact upper-half-plane
sets, with linear escape already erased.  Exact unresolved producer is now:

> Construct one such \(D_{\rm src}\) from actual finite Suzuki deficiency measures and the
> prime--Gamma screw source, then prove on one unconditional high-half-plane neighborhood that
> its homogeneous common-gauge Euler--Wronskian equals the Euler defect of affine-sewn Carleman
> sheet jump (42.1).

This is not a positivity restatement.  Analyticity of \(D_{\rm src}\) comes before Xi
identification from finite positive spectral measures; arithmetic work is local germ
identification.  Falsifiers are concrete: nonlinear compactified residual, failure of the
common-gauge Wronskian limit, or an uncancelled one-sided triangle term on initial half-plane.

Formal module:

- `formal/GaloisForLFunctions/RHTower/SuzukiCarlemanJumpEulerDefectWeld.lean`.

Formal capstones:

- `meromorphicOrderAt_suzukiEulerDefect_eq_sub_one`;
- `meromorphicOrderAt_suzukiEulerDefect_affineSewnExteriorWeylQuotient_eq_neg_two`;
- `meromorphicOrderAt_nonneg_of_analytic_source_germ_weld`;
- `riemannHypothesis_of_suzukiAffineSewnExteriorWeylEulerDefect_source_germ_weld`.

Pipeline:

- formalized theorem:
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-carleman-jump-euler-defect-pole-rigidity.md`;
- active source theorem:
  `docs/drafts/pipeline/1-in-progress/suzuki-carleman-jump-euler-defect-weld.md`.

Status: exact pole-amplification and one-germ RH discharge are unconditional and formalized.
RH itself remains open precisely at source construction and high-half-plane Wronskian germ
identity (42.9).

## 43. Coordinate retraction: scalar positivity is open; centered Euler remains parallel

Previous Section 43 mixed Suzuki's physical right triangle with centered Xi-real multiplier.
Suzuki 2023 one-sided identity gives physical multiplier `iG_0`, not `G_0`.  Positive half-line of
`r_0(t)=-|t|/2` has transform `1/(2z^2)`, so exact shifted coordinate is

\[
\eta(\lambda)=-i\lambda/2.                               \tag{43.1}
\]

Physical and canonically normalized sheets are

\[
E_{\rm phys}=iG_\eta W-T_{\rm phys},\qquad
(-i)E_{\rm phys}=G_\eta W-(-iT_{\rm phys}).              \tag{43.2}
\]

Thus centered interval input is `-iT_phys`.  Source quadrature still proves
`W_lambda'(0) in R` and `T_phys,lambda(0) in iR`, but normalized triangle value is real.  For
physical and normalized affine central fluxes,

\[
\Phi_{\rm norm}=-i\Phi_{\rm phys},\qquad
\operatorname{Re}\Phi_{\rm norm}
=\operatorname{Im}\Phi_{\rm phys}.                      \tag{43.3}
\]

Therefore prior `Re Phi=0` argument applies only to mixed expression `G_eta W-T_phys`; it does not
falsify actual scalar jump quotient.  Herglotz threshold is restored as

\[
\operatorname{Im}\Phi_{\rm phys}
\le \Xi_C''(0)/\Xi_C(0)<0.                               \tag{43.4}
\]

Direct Neumann term remains linear and cancels under affine sewing.  In exact one-sided coordinate
its normalized slope is `ia`, twice legacy full-symbol slope.

Actual frontier now has two live, nonexclusive source attacks:

1. construct positive prime--Gamma colligation whose normalized Weyl function is scalar sheet
   jump and prove `(43.4)` plus full jump Pick kernel;
2. construct analytic prime--Gamma source germ for centered Euler observable
   `J[f]=z(zf'-f)`, whose existing pole theorem already discharges RH.

Both must be built before Xi-divisor identification and fail on orbit-inserted countermodels.
Neither theorem exists in corpus; RH is not claimed.

Formal modules:

- `formal/GaloisForLFunctions/RHTower/SuzukiCarlemanCoordinatePhase.lean`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCarlemanJumpPhaseObstruction.lean`.

Pipeline:

- coordinate theorem:
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-one-sided-coordinate-phase-normalization.md`;
- retracted no-go:
  `docs/drafts/pipeline/5-failed/suzuki-scalar-jump-herglotz-phase-no-go.md`;
- live centered-Euler source theorem:
  `docs/drafts/pipeline/1-in-progress/suzuki-carleman-jump-euler-defect-weld.md`.

## 44. Neumann-dominated shift cone: scalar positivity requires source-selected shifts

Correct coordinate reopens scalar positivity, but hostile testing rules out arbitrary admissible
shifts.  Fix aperture `a>0` and Suzuki deficiency vectors

\[
v_{\lambda,+}=(A_a-\lambda)^{-1}e^x,
\qquad v_{\lambda,-}=(A_a-\lambda)^{-1}e^{-x}.
\]

Because `A_a` is self-adjoint and bounded below, spectral calculus gives

\[
(-\lambda)(A_a-\lambda)^{-1}\longrightarrow I
\quad\text{strongly as }\lambda\to-\infty.             \tag{44.1}
\]

For phase one, including zero-extension endpoint atoms, effective compact source is

\[
\nu_\lambda=i(v'_{\lambda,+}-v_{\lambda,+}
                   +v'_{\lambda,-}+v_{\lambda,-}).     \tag{44.2}
\]

Interior terms cancel in limiting exponentials.  Distributionally,

\[
(-\lambda)\nu_\lambda\longrightarrow
i\,2\cosh(a)(\delta_{-a}-\delta_a).                    \tag{44.3}
\]

Direct characteristic calculation independently gives

\[
(-\lambda)W_\lambda(z)\to4\cosh(a)\sin(az),
\qquad (-\lambda)W'_\lambda(0)\to4a\cosh(a).          \tag{44.4}
\]

Let `H_g(s)=integral_0^s g(t)dt`.  Pairing `(44.3)` with physical right-triangle test
`H_g(a-y)`, dividing by `(44.4)`, and applying exact normalization
`q_norm=-i q_phys` yields

\[
q^{EG}_{\mathrm{norm},\lambda}\longrightarrow
\frac{H_g(2a)}{2a}.                                    \tag{44.5}
\]

Direct Neumann term `(a/2)lambda` cancels identically under affine sewing.  For admissible dyadic
shifts `alpha_L=-2L`, `beta_L=-L`, zero-intercept is exactly

\[
\Phi_L=2q^{EG}_{\mathrm{norm},-L}
          -q^{EG}_{\mathrm{norm},-2L}
\longrightarrow\frac{H_g(2a)}{2a}.                    \tag{44.6}
\]

Suzuki screw kernel is continuous with `g(0)=0`, so right side tends to zero as `a` tends to zero.
Corpus already proves fixed curvature

\[
c_\Xi=\operatorname{Re}\frac{\Xi_C''(0)}{\Xi_C(0)}<0. \tag{44.7}
\]

Choose `a` small enough that screw average exceeds `c_Xi`.  Then every sufficiently large `L`
has `Phi_L>c_Xi`, opposite necessary Herglotz central-residue inequality.  Therefore normalized
scalar jump quotient is **not** Herglotz uniformly over admissible shift pairs even in correct
one-sided coordinate.

This is new constraint, not RH proof.  Exact frontier is disjunctive:

1. construct intrinsic source-selected nonescaping shift pair, plausibly tied to finite-aperture
   spectral floor, then prove central threshold and full normalized jump Pick kernel; or
2. construct analytic prime--Gamma germ `D_src=J[m_ext]` on one unconditional high-half-plane
   neighborhood, where `J[f]=z(zf'-f)`; existing pole theorem then forces RH.

Any shift law entering large-negative dyadic cone is falsified.  Any proposed positivity proof
using only admissibility, direct Neumann channel, or gauge normalization cannot solve frontier.

Paper proof:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-neumann-dominated-shift-cone-obstruction.md`.

Lean algebraic consumer:

- `formal/GaloisForLFunctions/RHTower/SuzukiLargeNegativeShiftCentralFlux.lean`.

Lean proves dyadic affine identity, limit transfer, and eventual Xi-curvature violation from
source-edge limit.  Concrete restricted-resolvent and distributional triangle instantiation
remain paper-level.  RH remains open at source-selected nonescaping colligation or centered-Euler
prime--Gamma germ identity.

## 45. Monotone spectral ratio produces shift-Stieltjes law

Section 44 forces source selection; chord-mass analysis reduces it to negative-Stieltjes structure
of normalized Euler--Gamma shift jet.  Corpus source formula is ratio, not generic Weyl function:

\[
q(\lambda)=\frac{N(\lambda)}{D(\lambda)},\qquad
N=\langle(A_a-\lambda)^{-1}e^x,h_a\rangle,
\quad D=\langle(A_a-\lambda)^{-1}e^x,2(1+x)\rangle.     \tag{45.1}
\]

New theorem gives exact sufficient source law.  For nodes `t_j`, positive weights `w_j`, and
responses `r_j` nondecreasing in `t_j`, put

\[
D(z)=\sum_j\frac{w_j}{t_j-z},\qquad
N(z)=\sum_j\frac{w_jr_j}{t_j-z},\qquad q=N/D.           \tag{45.2}
\]

Direct symmetrization proves

\[
\frac{\operatorname{Im}q(z)}{\operatorname{Im}z}
=-\frac{1}{2|D(z)|^2}
\sum_{j,k}\frac{w_jw_k(r_j-r_k)(t_j-t_k)}
 {|t_j-z|^2|t_k-z|^2}\le0.                             \tag{45.3}
\]

Thus `q` is anti-Herglotz in shift variable.  Rational partial fractions give exact negative
Stieltjes representation

\[
q(z)=\ell-\sum_k\frac{\nu_k}{\sigma_k-z},
\qquad \nu_k\ge0,                                     \tag{45.4}
\]

where `sigma_k` are uncancelled real zeros of `D`.  Measure version follows from same two-sample
identity.  On real resolvent half-line it makes quotient-rule numerator nonpositive:

\[
N'D-ND'\le0.                                           \tag{45.5}
\]

This replaces all alternating shift-derivative checks by one monotone-likelihood condition.

For actual restricted-Weil eigenpairs `A_a phi_j=t_j phi_j`, exact coefficients are

\[
w_j=\langle e^x,\phi_j\rangle\langle2(1+x),\phi_j\rangle,
\qquad
r_j=\frac{\langle h_a,\phi_j\rangle}
          {\langle2(1+x),\phi_j\rangle}.               \tag{45.6}
\]

Therefore shift-Stieltjes conjecture is reduced to source-pure laws

\[
w_j\ge0,
\qquad (r_j-r_k)(t_j-t_k)\ge0.                         \tag{45.7}
\]

One violating eigenpair kills route.  Ground-state positivity alone cannot prove `(45.7)`, and
corpus already forbids assuming positivity-preserving resolvent at all apertures.

Actual unresolved RH chain is now:

1. prove `(45.7)` for one intrinsic aperture, or falsify monotone-ratio mechanism;
2. prove resulting Stieltjes atoms fill exact chord gap `ell_a-c_Xi` for one nonescaping shift
   pair;
3. lift central inequality to full normalized jump Pick kernel;
4. use existing pole tomography to force RH.

Parallel centered-Euler germ route remains open.  RH is not proved.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-shift-spectral-monotone-likelihood-transfer.md`.

Lean core:

- `formal/GaloisForLFunctions/RHTower/SuzukiShiftSpectralMonotoneRatio.lean`.

Lean proves exact squared-resolvent two-sample identity, integrated cross-Wronskian inequality,
and quotient-rule nonpositivity using existing monotone-likelihood integration theorem.

## 46. Ground-edge small-aperture exclusion and Robin boundary compression

Section 45's all-mode monotone-likelihood law is optional for central selection because asymmetric
shift escape retains one fixed value.  At a simple even floor this value tends to

\[
r_a=\frac{\langle\phi_a,g(a-x)\rangle}{\langle\phi_a,1\rangle}.
\tag{46.1}
\]

Hostile audit now closes the only published positive-ground chamber.  Since Suzuki's explicit
profile is continuous, `g(0)=0`, and corpus proves `c_Xi<0`, there is `a_0>0` such that

\[
g(a-x)>\frac{c_{\Xi}}2>c_{\Xi}
\quad(0<a\le a_0,\ -a\le x\le a).                    \tag{46.2}
\]

Every nonzero nonnegative weight therefore has average strictly above `c_Xi`.  In particular,
Suzuki's sufficiently-small positive simple even ground cannot produce required central sign.
This strengthens Section 44: both far-negative dyadic edge and ground edge fail at small aperture.

Positive survivor is exact and signed.  For any even eigenmode define

\[
U_a(x)=\int_{-a}^{a}g(x-y)\phi_a(y)\,dy,
\qquad M_a=\int_{-a}^{a}\phi_a(y)\,dy.                 \tag{46.3}
\]

Restricted convolution eigen-equation is `-U_a''=lambda_a phi_a`.  Evenness gives

\[
-2U_a'(a)=\lambda_aM_a,
\qquad
r_a=\frac{U_a(a)}{M_a}
=-\frac{\lambda_aU_a(a)}{2U_a'(a)}.                   \tag{46.4}
\]

After orienting `M_a>0`, ground-edge selector is equivalent to one boundary inequality

\[
U_a(a)<c_{\Xi}M_a.                                    \tag{46.5}
\]

This is new `SUZUKI-ROBIN-CROSSING` conjecture.  It must occur at non-small aperture, where corpus
already rules out positivity-preserving semigroup.  Viable proof must use parity-separated
spectral flow, square Evans determinant, or signed boundary transversality.  If `M_a=0`, ground
pole cancels and next noncancelled even mode must be used.

Actual unresolved RH chain:

1. prove non-small-aperture Robin crossing `(46.5)` from explicit prime--Gamma operator;
2. use asymmetric selector to obtain central-valid pair;
3. prove full normalized jump Pick kernel, not merely its central residue;
4. apply existing Euler-defect pole tomography to exclude nonreal Xi zeros.

Paper theorem and conjecture:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-ground-edge-aperture-robin-obstruction.md`.

Lean certificate:

- `formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeApertureObstruction.lean`.

Lean proves uniform small-aperture exclusion, positive-mass average transfer, exact Robin-ratio
algebra, and deficit/excess threshold equivalence.  Concrete distributional convolution producer
remains paper-level.  RH is not proved.

## 47. Central selector closed; full jump is exact Loewner growth gap

Section 46's Robin route is superseded for central selection by new unconditional screw-Cesaro
recurrence.  Curvature-centered primitive

\[
h(A)=\int_0^A(g(t)-c_\Xi)\,dt
=\sum_\gamma\frac{\sin(\gamma A)}{\gamma^3}             \tag{47.1}
\]

changes sign cofinally in both directions by a Landau boundary theorem applied to its exact
Laplace transform.  Hence arbitrarily large apertures satisfy

\[
\frac1{2a}\int_0^{2a}g(t)\,dt<c_\Xi.                  \tag{47.2}
\]

At each such aperture, sufficiently negative finite dyadic pairs meet mandatory central residue
sign.  Central aperture and shift selection are no longer open.

The remaining full-frequency frontier now has exact Loewner form.  For actual reflection-odd
normalized right triangles

\[
q_\lambda(z)=\operatorname{Odd}_z\frac{R_\lambda(z)}{W_\lambda(z)},
\]

new theorem proves sewn exterior Weyl quotient is

\[
m_{\alpha,\beta}(z)
=-M_0(z)+\frac{\beta q_\alpha(z)-\alpha q_\beta(z)}{\beta-\alpha}.
\tag{47.3}
\]

Writing `H_lambda=K[q_lambda]` and `K_0=K[M_0]` for Pick kernels gives exact matrix identity

\[
K_{\rm jump}
=-K_0+\frac{\beta H_\alpha-\alpha H_\beta}{\beta-\alpha}. \tag{47.4}
\]

For `alpha<beta<0`, positivity on every finite test vector is equivalent to

\[
(-\alpha)(H_\beta-H_\alpha)
\succeq(\beta-\alpha)(K_0-H_\alpha).                  \tag{47.5}
\]

Left side is prime--Gamma source Loewner growth; right side is exact Xi-multiplier deficit.  This
is full matrix analogue of scalar chord-mass gap.  Dyadic pair `(-2L,-L)` reduces it to

\[
2(H_{-L}-H_{-2L})\succeq K_0-H_{-2L}.                 \tag{47.6}
\]

Actual open conjecture is `SUZUKI-LOEWNER-GROWTH`: prove `(47.5)` for one recurrence-selected
pair.  Strong square producer asks for exact resolvent factorization of left-minus-right in
`(47.5)` as `B^*B`, before Xi-divisor identification.  One negative finite test vector falsifies
producer.

This is present RH chain:

1. prove prime--Gamma Loewner growth `(47.5)` using restricted resolvent identity;
2. conclude full jump Pick positivity by `(47.4)`;
3. existing pole tomography excludes every nonreal Xi zero;
4. RH.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-jump-kernel-loewner-growth-gap.md`.

Active RH core:

- `docs/drafts/pipeline/1-in-progress/suzuki-jump-kernel-loewner-growth.md`.

Lean certificate:

- `formal/GaloisForLFunctions/RHTower/SuzukiJumpKernelLoewnerGap.lean`.

RH is not yet proved: inequality `(47.5)` remains source conjecture.

## 48. Bare resolvent square fails: exact Krein defect and global/local weld debt (2026-07-22)

Hostile test of Section 47's proposed resolvent square gives exact opposite conclusion.  Put

\[
R_\lambda(t)=\frac1{t-\lambda},\qquad
E_{\alpha,\beta}(t)=
\frac{\beta R_\alpha(t)-\alpha R_\beta(t)}{\beta-\alpha}.
\]

New unconditional theorem is

\[
D_{\alpha,\beta}(t):=R_0(t)-E_{\alpha,\beta}(t)
=\frac{\alpha\beta}{t(t-\alpha)(t-\beta)}.             \tag{48.1}
\]

For source-relevant order `alpha<beta<0`, `beta<t`, `t!=0`, factors other than `t` are positive:

\[
D_{\alpha,\beta}(t)=\operatorname{sgn}(t)
\frac{\alpha\beta}{|t|(t-\alpha)(t-\beta)}.           \tag{48.2}
\]

Ordinary resolvent affine gap is `-D`; negative-Stieltjes/anti-resolvent affine gap is `D`.
Therefore correct source orientation is positive on positive restricted-Weil coordinates but
strictly negative on negative coordinates.  Second resolvent identity gives a Krein square, not
a Hilbert square.  In a minimal finite spectral realization, its negative index is exactly number
of negative nodes.

This does not kill Suzuki route.  It identifies missing contribution sharply.  Against arbitrary
global target `g`, define local/global correction `C_g(t)=-R_0(t)-g(t)`.  Exact anti-resolvent gap
is

\[
G_g(t)=D_{\alpha,\beta}(t)+C_g(t),\qquad
G_g(t)\ge0\iff C_g(t)\ge-D_{\alpha,\beta}(t).          \tag{48.3}
\]

Every negative node creates strictly positive debt

\[
-D_{\alpha,\beta}(t)
=\frac{\alpha\beta}{|t|(t-\alpha)(t-\beta)}>0.        \tag{48.4}
\]

Thus actual frontier corpus cannot solve is no longer generic `Loewner growth` or abstract
`resolvent Bianchi square`.  It is source-specific:

> **`SUZUKI-GLOBAL-LOCAL-KREIN-WELD`** — in one characteristic gauge, prove explicit coupled
> reflected prime--Gamma exterior term and full-frequency Neumann projective holonomy cancel exact
> negative piece `(48.4)`, leaving a source-built positive square while retaining global Xi
> divisor.

This conjecture is decisive and falsifiable on finite node sets.  One vector for which completion
is smaller than negative spectral debt refutes it.  Proving it gives full jump Pick positivity,
then existing pole tomography gives RH.  Replacing global `K_0` by local `R_0` would erase
`(48.3)` and assume missing RH-bearing weld.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-affine-resolvent-krein-defect.md`.

Formal certificate:

- `formal/GaloisForLFunctions/RHTower/SuzukiAffineResolventKreinDefect.lean`.

RH is not proved.  New progress is exact signed factorization, exact negative-index bridge, and
sharp completion threshold which any successful source proof must meet.

## 49. Full-frequency holonomy imposes an exact Schur tax (2026-07-22)

Section 48's diagonal debt is necessary but not sufficient once projective Neumann holonomy mixes
positive and negative channels.  For one positive channel of weight `a>0`, one negative debt
`n>0`, direct completion `c`, and coupling `b`, exact quadratic form is

\[
Q(x,y)=a x^2+2bxy+(c-n)y^2
=a\left(x+\frac ba y\right)^2
+\left(c-n-\frac{b^2}{a}\right)y^2.                    \tag{49.1}
\]

Hence

\[
Q\succeq0\iff c\ge n+\frac{b^2}{a}.                    \tag{49.2}
\]

Nonzero holonomy adds strict positive cost `b^2/a`.  A diagonal completion paying exactly `n`
still has determinant `-b^2` and fails.  This corrects overly weak intuition that holonomy itself
automatically compensates signed resolvent defect.

At fixed aperture restricted-Weil operator has finite-dimensional negative spectral subspace.
Write local signed block `diag(P,-N)` and actual source completion blocks `C`.  Since positive block
`P+C_++` is invertible, block Gaussian congruence gives exact frontier

\[
C_{--}-N-C_{-+}(P+C_{++})^{-1}C_{+-}\succeq0.          \tag{49.3}
\]

Thus infinite Pick problem compresses to one finite negative-block Schur complement.  Direct term
must pay both affine-resolvent debt `N` and projective cross-channel tax.  This is revised
`SUZUKI-FINITE-NEGATIVE-BLOCK-WELD`.  Proving `(49.3)` from reflected prime--Gamma triangles and
exact Neumann projective tangent gives jump Pick positivity and then RH.  One negative principal
minor kills conjecture.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-krein-schur-holonomy-tax.md`.

Lean scalar certificate remains in:

- `formal/GaloisForLFunctions/RHTower/SuzukiAffineResolventKreinDefect.lean`.

RH remains open at source inequality `(49.3)`.

## 50. Unique coherent completion kernel: weighted negative spectral projector (2026-07-22)

Local Xi-real/FE bipolarization fixes minimal negative-light square, but did not fix cross-node
assembly.  Spectral calculus now does.  For restricted-Weil operator `A`, two negative shifts below
spectrum, and `0` outside spectrum, affine defect operator is

\[
D_{\alpha,\beta}
=\operatorname{sgn}(A)W_{\alpha,\beta},\qquad
W_{\alpha,\beta}
=\alpha\beta|A|^{-1}(A-\alpha)^{-1}(A-\beta)^{-1}\succeq0. \tag{50.1}
\]

Writing `P_-` for negative spectral projection,

\[
D=D_+-D_-,\qquad D_-=P_-W.                             \tag{50.2}
\]

`D_-` is unique Loewner-minimal positive correction among operators in functional calculus of
`A`: `D+C>=0` iff `C` dominates `D_-` on negative spectrum.  For source evaluation vectors
`Gamma(z)`, coherent finite-node completion is no longer arbitrary:

\[
K_-(z,w)
=\langle W^{1/2}P_-\Gamma(w),W^{1/2}P_-\Gamma(z)\rangle. \tag{50.3}
\]

It is positive semidefinite on every node set and finite rank at every aperture.  Also
`K_D+K_-=K_{D_+}>=0`.  This converts “coherent assembly” into one explicit source operator target.

Strongest current conjecture is **`SUZUKI-NEGATIVE-PROJECTOR-TRIANGLE-IDENTITY`**: common-gauge
reflected Euler--Gamma triangle plus exact Neumann projective holonomy, in fixed Xi-real/FE
negative-light channel, equals `(50.3)` plus positive kernel.  If holonomy has positive/negative
cross block, it must additionally pay Section 49 Schur tax.

Proving this division-free triangle identity yields jump Pick positivity and RH.  Corpus cannot
currently identify analytic triangle operator with weighted negative projector; this is actual
remaining scientific frontier.

Paper theorem/conjecture:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-negative-projector-coherent-completion.md`.

RH is not yet proved.

## 51. Actual triangle operator is Volterra phase, not admissible energy (2026-07-22)

The projective correction identifies the right representation but still leaves its concrete
source boundary map unnamed.  The physical triangle names it exactly.  For an even kernel `k` on
`(-2a,2a)`, define

\[
(V_k u)(x)=\int_{-a}^x k(x-y)u(y)\,dy,
\qquad H_k=-i(V_k-V_k^*),\qquad C_k=V_k+V_k^* .       \tag{51.1}
\]

Fubini gives the actual right triangle, not a model:

\[
T_{k,R}[u](z)=\widehat{V_k u}(z),\qquad
-iT_{k,R}=\frac12\widehat{H_k u}-\frac i2\widehat{C_k u}. \tag{51.2}
\]

For Suzuki's odd phase-one source, reflection exchanges `V_k` and `V_k^*`.  Therefore

\[
\operatorname{Even}_z[-iT_{k,R}]=\frac12\widehat{H_k u},
\qquad
\operatorname{Odd}_z[-iT_{k,R}]=-\frac i2\widehat{C_k u}. \tag{51.3}
\]

This is decisive.  Admissibility `lambda<lambda_a` proves positivity of compressed symmetric
pencil `C_lambda`, but `(51.3)` places it in already known sine-clock parity.  Entire RH-bearing
even carrier is independent self-adjoint phase

\[
H_\lambda=H_g-\lambda H_{r_0},\qquad r_0(t)=-|t|/2.    \tag{51.4}
\]

Neumann phase is exactly rank one.  If `mu_j=integral y^j u(y)dy`, then

\[
(V_{r_0}-V_{r_0}^*)u(x)=-x\mu_0/2+\mu_1/2.
\]

On odd sources `mu_0=0`, so `H_(r_0)u=-i mu_1/2` is constant and

\[
\operatorname{Even}[-iT_{r_0,R}](z)
=-\frac{W'(0)\sin(az)}{2z}.                            \tag{51.5}
\]

This recovers full-frequency projective holonomy exactly; there is no hidden Neumann positive
completion left to extract.

On a form-resolvent orbit `Au_lambda-lambda u_lambda=e`, phase pencil homogenizes as

\[
(H_g-\lambda H_{r_0})u_\lambda
=(H_g-H_{r_0}A)u_\lambda+H_{r_0}e.                    \tag{51.6}
\]

Thus concrete operator acting on the homogeneous resolvent blade is relative causal phase defect

\[
\Omega=H_g-H_{r_0}A,                                  \tag{51.7}
\]

plus one rank-one homogeneous moment coordinate.  For product-resolvent state `v`, its exact
division-free chord is

\[
\frac{\beta-\alpha}{2}
\{D_z(\Omega v)D_z(Av)-D_z(\Omega Av)D_z(v)
-D_z(H_{r_0}e)D_z(v)\}.                               \tag{51.8}
\]

Chord `(51.8)` is not complete affine-sewn carrier.  Put

\[
B_z=\tfrac12D_z\Omega,\quad c_z=\tfrac12D_z(H_{r_0}e),
\quad x=B_zv,\ X=B_zAv,\ y=D_zv,\ Y=D_zAv.
\]

Actual weighted intercept has marked numerator

\[
Q_{\alpha,\beta}=(X+c_z)Y-(\alpha+\beta)xY+\alpha\beta xy, \tag{51.9}
\]

and denominator `(Y-beta y)(Y-alpha y)`.  Gauge `B_z -> B_z+delta D_z` fixes every
Plucker minor but changes `(51.9)` by `delta` times denominator.  Thus phase operator is correct
source input, while marked affine secant—not blade alone—is complete jump carrier.

The Euler--Gamma phase is itself explicit source commutator.  Off diagonal, writing
`q_g(t)=g(t)/|t|` and letting `Q_g` have kernel `q_g(x-y)`,

\[
H_g=-i[X,Q_g].                                         \tag{51.10}
\]

Actual frontier corpus cannot solve is now
**`SUZUKI-MARKED-SECANT-CD-WELD`**: derive prime--Gamma Christoffel--Darboux/Green identity whose
left side is Pick polarization of `(51.9)` coupled to global Xi multiplier and whose right side
is positive source Gram.  One negative principal minor refutes it.  Proving it gives existing
Loewner growth, jump Pick positivity, pole exclusion, and RH.

This supersedes negative-projector and finite-Morse identities as canonical source producers.
Those remain valid external majorants only if actual phase response independently dominates them.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-volterra-cartesian-phase-defect.md`;
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-projective-affine-secant-tensor-lift.md`.

Lean certificate:

- `formal/GaloisForLFunctions/RHTower/SuzukiVolterraCartesianPhaseDefect.lean`;
- `formal/GaloisForLFunctions/RHTower/SuzukiProjectiveAffineSecantTensor.lean`.

RH remains open at exact source Green identity for causal commutator `(51.10)` in marked tensor
`(51.9)`.

## 52. Compound weld has one exact rooted halfgap debt (2026-07-22)

Section 51's phrase “marked tensor plus Xi deficit” is now division-free and quantitative.  Form
canonical local/global pair

\[
N=QT-SP,\qquad D=PT,
\]

where `(Q,P)` is marked Volterra secant pair and `(S,T)=(XiC',z^2XiC)`.  Existing compound theorem
gives

\[
[N,D]_{z,w}=T_z\overline{T_w}[Q,P]_{z,w}
-P_z\overline{P_w}[S,T]_{z,w}.                       \tag{52.1}
\]

Thus exact RH kernel is fixed across denominator zeros and common affine gauge cancels.

New theorem resolves inertia.  Write

\[
\alpha=m-d,\quad\beta=m+d,\quad B_0=X+c,
\quad U=B_0-mx,\quad V=Y-my,
\quad F=B_0y-xY.
\]

Then unconditionally

\[
Q=UV-d^2xy+mF,\qquad P=V^2-d^2y^2,                  \tag{52.2}
\]

and compound numerator is exactly

\[
N=V(UT-SV)+d^2y(Sy-xT)+mFT.                          \tag{52.3}
\]

Symmetric coefficient form has diagonal

\[
\mathcal S(r,s)=(r-ms)^2-d^2s^2.                     \tag{52.4}
\]

Adding rooted rate `kappa*s^2` makes it nonnegative for every `(r,s)` iff
`kappa>=d^2`; minimal completion is unique and equals one square.  For Suzuki dyadic pair
`(-2L,-L)`, exact missing rate is

\[
d^2=L^2/4,                                            \tag{52.5}
\]

while pre-existing rooted coefficient is `alpha beta=2L^2`; completion raises it to
`m^2=9L^2/4`.

This is not abstract matrix bookkeeping.  On actual two-resolvent orbit,

\[
e=(A-m)^2v-d^2v,
\]

and relative causal phase obeys

\[
(H_g-H_{r_0}A)u_m+H_{r_0}e
=H_gu_m-mH_{r_0}u_m-d^2H_{r_0}v.                     \tag{52.6}
\]

Exact debt lives in rooted Neumann phase of midpoint product-resolvent state.

Hostile corpus audit rules out direct balanced-boundary producer: orthogonal, affine, every
positive jet, growing jet, and cofinal von-Mangoldt--Gamma Grams all vanish on canonical packet
`(+1/2,-1/2)`, while marked rank-one affine intercept remains arbitrary.  Root must remain before
compression.

Actual frontier corpus cannot solve is therefore
**`SUZUKI-ROOTED-MIDPOINT-COMPOUND-GRAM`**:

> derive atom-by-atom from explicit prime--Gamma source and pointed Ward identity that signed
> global Xi term in `(52.1)` supplies exactly `d^2` times raw rooted Gamma--Bianchi Gram plus a
> positive archimedean remainder, with common-prime Julia--Bianchi mixed block fixed by source.

If identity holds, `(52.4)` completes to perfect joint square, `(52.1)` is positive Gram, existing
Loewner/pole-tomography connector proves RH.  One prime-power coefficient mismatch or negative
finite principal minor refutes conjecture.  No Herglotz premise, Xi-zero data, or fitted feature is
allowed.

Paper theorem/conjecture:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-marked-secant-midpoint-lorentz-completion.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-rooted-midpoint-compound-gram.md`.

Lean certificate:

- `formal/GaloisForLFunctions/RHTower/SuzukiMarkedSecantMidpointLorentzCompletion.lean`.

RH is not yet proved.  Missing statement is now one source coefficient identity with exact amount,
source coordinate, mixed block, and finite falsifiers.

## 53. Atomwise rooted Gram is impossible; exact causal aperture-entry law (2026-07-22)

Section 52's exact half-gap debt survives, but its proposed atomwise producer does not.  Suzuki's
positive-half-line contribution of one prime power is delayed hinge

\[
g_n(t)=a_n(t-\ell_n)_+,
\qquad a_n=\frac{\Lambda(n)}{\sqrt n},\quad \ell_n=\log n.       \tag{53.1}
\]

For source `v` on `[-a,a]`, define `W`, right triangle `T_(ell,a)`, and exterior
`R_(ell,a)=M_ell W-T_(ell,a)`.  Direct Laplace integration gives

\[
M_\ell(z)=-\frac{e^{iz\ell}}{z^2}.                           \tag{53.2}
\]

For `0<=ell<=2a`, put `c=a-ell`,

\[
B_c=\int_{-a}^cv(y)dy,\qquad
A_c=\int_{-a}^c(c-y)v(y)dy,\qquad
W_{[c,a]}(z)=\int_c^av(y)e^{izy}dy.
\]

New exact cancellation-before-limit theorem is

\[
R_{\ell,a}(z)
=-\frac{e^{iz\ell}}{z^2}W_{[c,a]}(z)
-e^{iza}\left(\frac{A_c}{iz}+\frac{B_c}{z^2}\right).         \tag{53.3}
\]

At entry wall `ell=2a`, all boundary terms vanish and `(53.3)` joins continuously to pure global
multiplier.  For every `ell>=2a`, local Volterra triangle is identically zero:

\[
T_{\ell,a}=0,\qquad R_{\ell,a}(z)=-e^{iz\ell}W(z)/z^2.        \tag{53.4}
\]

Thus every prime `n>e^(2a)` is invisible to finite local phase but remains in global Xi channel.
Fixed finite common-prime carrier cannot equal complete compound source.

Xi-real far-prime contribution to jump quotient is

\[
m_{n,a}(z)=-i\,a_n\frac{e^{iz\ell_n}}{z^2}.                   \tag{53.5}
\]

Its Pick diagonal changes sign inside upper half-plane.  At `z=i*pi/ell`, it is positive.  At
phase-aligned point

\[
z=\frac{2\pi}{\ell}+i\frac{\pi}{\ell},
\]

one has `exp(iz ell)=exp(-pi)` and

\[
\operatorname{Im}m_{n,a}(z)
=-a_ne^{-\pi}\frac{x^2-y^2}{(x^2+y^2)^2}<0.                 \tag{53.6}
\]

Since diagonal compound congruence multiplies by `|D(z)|^2`, every nonzero compound denominator
preserves this strict negative sign.  Therefore no direct sum of positive prime-power atoms, and
no atomwise Julia--Bianchi Gram plus separate positive archimedean remainder, can factor actual
compound Bezoutian.

Completed distribution confirms why separation is wrong.  With `lambda_k=2k+1/2`,

\[
-g''=e^{t/2}+e^{-t/2}-\sum_{k\ge0}e^{-\lambda_kt}
-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}.      \tag{53.7}
\]

Prime atoms and polar--Gamma source have opposite distributional signs before any positivity.
Together with cofinal critical Bianchi divergence, `(53.6)` conclusively falsifies
`SUZUKI-ROOTED-MIDPOINT-COMPOUND-GRAM` in atomwise/direct-sum form.  Exact `d^2` Lorentz debt is
unchanged.

Actual frontier corpus cannot solve is now
**`SUZUKI-CAUSAL-APERTURE-ENTRY-COMPOUND-WELD`**:

> Insert actual resolvent-dependent deficiency source into every finite-delay boundary law
> `(53.3)`, retain complete far-prime tail `(53.4)` joined to exact polar--Gamma channel `(53.7)`,
> assemble inside canonical compound Bezoutian before any Gram or cofinal limit, and prove
> assembled kernel pays exact rooted half-gap debt `d^2` and is positive.

This is collective, source-nonlinear Ward/CD identity.  Atomwise positivity is now a formal
falsifier, not a permitted ansatz.  Proving collective weld yields compound Pick positivity and
existing pole tomography gives RH.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-causal-hinge-boundary-tail-green-law.md`.

Lean certificate:

- `formal/GaloisForLFunctions/RHTower/SuzukiCausalHingeBoundaryTailGreenLaw.lean`.

Lean proves exact closed-form boundary cancellation, entry wall, both Pick signs, and compound
denominator sign preservation.  Module build passed `9015/9015`; axiom audit is standard
`propext`, `Classical.choice`, `Quot.sound`.  RH is not yet proved.

## 54. Compound denominator converts screw exterior to Weil exterior plus Robin current

Section 53 forced collective prime--Gamma assembly but left its canonical source coordinate
unnamed.  New exact Green identity identifies it.

Let `g` be Suzuki screw kernel, `K=-g''` completed Weil distribution, `v` compactly supported on
`[-a,a]`,

\[
U(x)=\int_{-a}^a g(x-y)v(y)dy,
\qquad W(z)=\int_{-a}^a v(y)e^{izy}dy,
\]

and let `R_g=M_gW-T_(g,R)` be physical right screw exterior.  Define causal Weil exterior

\[
E_K[v](z)=\int_{-a}^a v(y)e^{izy}
 \int_{a-y}^{\infty}K(t)e^{izt}dt\,dy
=\int_a^\infty(K*v)(x)e^{izx}dx.                     \tag{54.1}
\]

Two integrations by parts in source-native half-plane give unconditional identity

\[
\boxed{
z^2R_g[v](z)
=e^{iaz}\bigl(izU(a)-U'(a)\bigr)+E_K[v](z).}
                                                                  \tag{54.2}
\]

Proof uses tail primitive

\[
\int_b^\infty g(t)e^{izt}dt
=-\frac{e^{izb}g(b)}{iz}
+\frac{e^{izb}g'(b)}{(iz)^2}
-\frac1{(iz)^2}\int_b^\infty K(t)e^{izt}dt.          \tag{54.3}
\]

Set `b=a-y`; boundary phases collapse to `e^(iaz)` and source integrals become `U(a),U'(a)`.
Multiplying by `z^2` proves `(54.2)`.

This is exactly matched to global projective denominator `T=z^2XiC`:

\[
(z^2\Xi_C)R_g
=\Xi_C\left[e^{iaz}(izU(a)-U'(a))+E_K\right].         \tag{54.4}
\]

No division by Xi or characteristic is used.  Compound denominator `P*T` adds only factor `P`.

Delayed hinge `g(t)=(t-ell)_+` has `K=-delta_ell`.  With Section 53 moments,

\[
U(a)=A_c,\quad U'(a)=B_c,\quad
E_K=-e^{iz\ell}W_{[c,a]},                             \tag{54.5}
\]

so `(54.2)` reproduces boundary--tail law exactly:

\[
z^2R_{\ell,a}=e^{iaz}(izA_c-B_c)-e^{iz\ell}W_{[c,a]}.\tag{54.6}
\]

For form shift `k_lambda=g-lambda*r_0`, `-r_0''=delta_0`, hence

\[
-k_\lambda''=K-\lambda\delta_0.                      \tag{54.7}
\]

Outside compact source interval, `(delta_0*v)(x)=0`; direct shift delta contributes nothing to
causal Weil exterior.  All shift dependence lives in resolvent state `v_lambda` and Robin current.
Therefore exact midpoint `d^2` Neumann debt is a boundary current, not critical raw Bianchi bulk.

Actual frontier corpus cannot solve is sharpened to
**`SUZUKI-MARKED-WEIL-ROBIN-CD`**:

> At one recurrence-selected aperture and admissible midpoint pair, insert actual two-resolvent
> source into `(54.2)`, affine-sew marked Robin currents retaining exact `d^2` term, polarize causal
> exterior of already-completed signed Weil distribution, and prove resulting compound
> Bezoutian is positive Green Gram.

Prime atoms may not be split (Section 53); Robin current may not be dropped (it contains `d^2`);
signed Weil exterior may not be replaced by positive part (that is RH-equivalent).  Proving this
single marked CD identity gives compound Pick positivity and existing pole tomography proves RH.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-causal-weil-robin-green-identity.md`.

Lean module:

- `formal/GaloisForLFunctions/RHTower/SuzukiCausalWeilRobinGreenIdentity.lean`.

RH is not yet proved; missing sign is now localized to polarization of exact two-channel right
side of `(54.2)`, not an unspecified prime--Gamma Gram.

Formal audit: targeted SOTA build passed `9448/9448`; axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; new module has no forbidden declarations.  Global lint is
blocked only by unrelated concurrently added unreachable module
`GaloisForLFunctions.RHTower.MobiusLaplaceCriticalDilationPrimeEscapeLaw`.

## 55. Affine sewing cannot remove the universal far-prime channel

Section 54 localized exact source to Robin boundary current plus completed Weil exterior, but one
possible escape remained: perhaps two admissible shifts cancel far primes when affine-sewn.  Exact
algebra rules this out.

For deficiency characteristics `W_alpha,W_beta`, target `gamma`, define

\[
P(z)=(\beta-\alpha)W_\alpha(z)W_\beta(z),
\]

and affine sewn channel

\[
S_\gamma(C_\alpha,C_\beta)
=(\beta-\gamma)W_\beta C_\alpha
 -(\alpha-\gamma)W_\alpha C_\beta .                 \tag{55.1}
\]

Every common normalized channel obeys division-free identity

\[
\boxed{S_\gamma(mW_\alpha,mW_\beta)=mP.}             \tag{55.2}
\]

For a far prime-power delay `ell=log n>=2a`, its Weil exterior is

\[
E_\lambda(\ell,z)=-c_\ell e^{iz\ell}W_\lambda(z),
\qquad c_\ell=\frac{\Lambda(n)}{\sqrt n}.
\]

Thus

\[
S_\gamma(E_\alpha(\ell),E_\beta(\ell))
=-c_\ell e^{iz\ell}P(z),                             \tag{55.3}
\]

and, in the source-native convergence half-plane,

\[
S_\gamma(E_\alpha^{\rm far},E_\beta^{\rm far})
=-P(z)\sum_{\log n\ge2a}\frac{\Lambda(n)}{\sqrt n}e^{iz\log n}. \tag{55.4}
\]

Normalized far von-Mangoldt tail is therefore universal: independent of shifts, deficiency
states, and affine target.  This is not only noncancellation.  Common-factor Hermitian Bezoutian
obeys

\[
[Pm,P]_{z,w}=P(z)\overline{P(w)}
              \bigl(m(z)-\overline{m(w)}\bigr).       \tag{55.5}
\]

Affine sewing acts only by congruence.  For Xi-real atom
`m_ell=-i c_ell e^(iz ell)/z^2`, its Pick diagonal is strictly negative at
`z=2pi/ell+i*pi/ell`; `(55.5)` preserves that sign whenever `P(z) != 0`.  Hence two-shift sewing
cannot turn far atoms into an atomwise/direct-sum Gram.

Actual frontier corpus cannot solve is now **`SUZUKI-CAUSAL-ENTRY-SCHUR-WARD`**:

> At one recurrence-selected aperture and admissible midpoint pair, form the complete
> division-free channel from marked Robin current, near-prime aperture-entry terms, universal far
> von-Mangoldt tail, and polar--Gamma exterior.  Construct a source operator `B_a` such that the
> full compound kernel—not its prime summands—equals `B_a^*B_a`, paying exact midpoint `d^2` plus
> holonomy Schur tax.

Any successful `B_a` must mix prime delays with polar--Gamma channel; phase-aligned sign theorem
falsifies diagonal prime coordinates.  One negative finite-node principal minor after complete
assembly falsifies conjecture.  Proving identity gives compound Pick positivity, and existing pole
tomography then gives RH.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-affine-sewn-weil-robin-far-tail-factorization.md`.

Lean module:

- `formal/GaloisForLFunctions/RHTower/SuzukiAffineSewnWeilRobinFarTailFactorization.lean`.

Formal audit: direct source check and targeted SOTA build `9450/9450` pass.  Axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`; forbidden declaration scan is clean.  RH is
not yet proved.

## 56. Exact Suzuki isometry is overkill: semibounded Ward defect suffices

Section 55 left exact positive Green-Gram identity as open core.  Corpus rectangular completeness
allows a strictly weaker target.

Fix `L>0` and put

\[
Q_L(n)=\Re\,\mathrm{xiScrewWindowCurvature}(L,\log n).
\tag{56.1}
\]

Lean corpus already proves RH equivalent to eventual lower boundedness of `Q_L(n)` on admissible
nodes `L<=log(n)/2`; under false RH, `Q_L` is cofinally unbounded below.

Let `R_L(n)` be any explicit source vector, in particular the rectangular combination to be made
from Suzuki's unconditional pole-cancelled `L^2` screw vectors and exact affine-sewn Weil--Robin
channel.  Normalize source energy and defect by

\[
E_L(n)=\|R_L(n)\|^2\ge0,
\qquad \Delta_L(n)=Q_L(n)-E_L(n).                         \tag{56.2}
\]

If constants `B,N0` satisfy

\[
B\le\Delta_L(n)
\quad(n\ge N_0,\;L\le\log(n)/2),                         \tag{56.3}
\]

then

\[
B\le\Delta_L(n)\le\Delta_L(n)+E_L(n)=Q_L(n).            \tag{56.4}
\]

Thus `Q_L` is eventually bounded below and existing formal rectangular theorem proves RH.  Exact
isometry `Delta_L=0`, orthogonality of zero fibers, and exact CD/Green Gram are unnecessary.

Hostile converse is equally sharp.  If RH is false, then for every nonnegative energy `E` and
every `B,N0`, some admissible `n>=N0` has `Q_L(n)<B`, hence

\[
Q_L(n)-E(n)\le Q_L(n)<B.                                 \tag{56.5}
\]

False RH forces Ward defect of every positive source square cofinally to `-infinity`; positive
energy cannot conceal divisor obstruction inside semibounded error.

Actual frontier corpus cannot solve is now
**`SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED`**:

> For one fixed width, construct rectangular source vector from marked Robin current, near-entry
> terms, universal far von-Mangoldt tail, and polar--Gamma exterior using Suzuki's unconditional
> pole-cancelled source realization.  Prove only uniform lower bound `(56.3)` on logarithmic
> aperture mesh.

This admits nonzero completion error when its quadratic values on the logarithmic orbit are
uniformly lower bounded; trace-class or finite-rank membership alone does not imply that bound.
Target remains materially weaker than previous exact factorization.  Far atoms still cannot be
diagonalized; source vector must mix them with Gamma channel.  One sequence with
`Delta_L(n)->-infinity` falsifies conjecture and, by `(56.5)`, is exact signature of off-critical
divisor.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-rectangular-ward-defect-semiboundedness.md`.

Lean module:

- `formal/GaloisForLFunctions/RHTower/SuzukiRectangularWardDefectBoundedness.lean`.

Direct source check and targeted SOTA build `9451/9451` pass.  Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`; forbidden declaration scan is clean.  RH is not
yet proved: missing theorem is now one explicit uniform lower bound, not exact source isometry.

## 57. Corpus correction: RH-bearing screw kernel lives on Suzuki completion

Sections 48--56 derived valid algebraic consequences of proposed source identities, but none
constructs the required source or proves an RH-bearing sign.  In particular, Section 56's
semibounded-defect statement is a criterion: its missing lower bound is already strong enough to
exclude the off-critical divisor.  It must not be reported as resolution of the frontier.

A source audit of Suzuki's 2026 paper exposes a more immediate correctness issue in the older CCM
kernel route.  Fix aperture `a` and `mu<lambda_a=inf spec(A_a)`.  Suzuki forms

\[
S_{a,\mu}=G_a-\mu(-\Delta_N)^{-1}
\]

and completes the smooth zero-mean derivative core in its positive norm.  The resulting space
`H(S_(a,mu))` satisfies

\[
\overline D:H(A_a-\mu I)\overset{\sim}{\longrightarrow}H(S_{a,\mu}),
\qquad
A_a=\overline D^{*}\widetilde G_a\overline D,            \tag{57.1}
\]

where `Gtilde_a` is the bounded extension of the raw continuous-kernel screw operator.  Suzuki
states explicitly

\[
H(S_{a,\mu})\not\subset L^2(-a,a).                       \tag{57.2}
\]

Therefore the generalized zero fiber is

\[
\ker A_a\cong\ker\bigl(\widetilde G_a:H(S_{a,\mu})
                  \to H(S_{a,\mu})\bigr),                \tag{57.3}
\]

not automatically `ker(G_a:L2_0->L2_0)`.  Earlier handover statements that promoted raw screw
injectivity to an RH equivalence are wrong without an additional regularity theorem.  The
eigenfunction-variable square Evans determinant remains completion-safe because it starts with
the original `L2` eigenfunction of `A_a`.

### Exact completion-corona theorem

Let

\[
j_a:L^2_0(-a,a)\hookrightarrow H(S_{a,\mu})
\]

be the canonical injection.  Strict positivity of `S_(a,mu)` makes it injective, and extension
from the common core gives

\[
\widetilde G_a j_a=j_aG_a.                               \tag{57.4}
\]

Hence

\[
\boxed{
j_a(\ker G_a)=\ker\widetilde G_a\cap j_a(L^2_0).}         \tag{57.5}
\]

Proof is two lines: `(57.4)` gives forward inclusion; reverse inclusion follows from injectivity
of `j_a`. Combining `(57.5)` with `(57.1)` produces exact set partition of zero modes

\[
\ker A_a=Z_a^{\rm regular}\ \dot\cup\ Z_a^{\rm corona}, \tag{57.6}
\]

where regular means `Dbar v` lies in `j_a(L2_0)` and corona means it does not.  If RH is false,
continuity of lowest aperture eigenvalue supplies a first `a_*` with nonzero completed kernel.  If
raw `G_(a_*)` is injective, `(57.5)` forces every nonzero vector in that first zero fiber into
corona. Thus raw unique continuation can succeed and RH can still fail; completion regularity is
not optional.

### New boundary indicial law

The corona has a concrete analytic origin.  Put `r=dist(x,partial I)`, `L=-log r`, and
`phi_tau(r)=L^(-tau)` near one endpoint.  For the principal one-dimensional logarithmic jump
operator, exterior killing and interior tail have leading terms

\[
L^{1-\tau},
\qquad
-\frac{\tau}{1-\tau}L^{1-\tau},                          \tag{57.7}
\]

respectively.  Therefore

\[
L_{\log}\phi_\tau(r)
=C_{\log}\frac{1-2\tau}{1-\tau}L^{1-\tau}
 +o(L^{1-\tau}),\qquad C_{\log}>0.                       \tag{57.8}
\]

The unique leading indicial cancellation is

\[
\boxed{\tau=\tfrac12.}                                   \tag{57.9}
\]

This explains exact threshold in Chen--Weth barriers: their proved estimate gives
`O(log^(-tau))` for every `tau<1/2`, and its leading barrier coefficient vanishes at `1/2`.
Hernandez-Santamaria--Lopez Rios--Saldana subsequently proved the optimal `tau=1/2` upper rate and
a matching Hopf lower bound for nonnegative supersolutions. Equation `(57.8)` identifies the same
critical scale for Suzuki's signed perturbation and predicts eigenmode layer

\[
v(a-r)=c_+L^{-1/2}+\cdots,
\qquad
v'(a-r)\sim\frac{c_+}{2rL^{3/2}},                        \tag{57.10}
\]

whose derivative is not in `L2`.  This is exactly the missing completion-corona channel, not a
technical artifact.

### Exact Volterra boundary normal form

The half-log root comes from an exact identity. Let `u` vanish outside `(0,1)`, put

\[
(Ju)(r)=\int_{r-1}^{r+1}\frac{u(r)-u(y)}{|r-y|}\,dy,
\qquad r=e^{-L},\qquad F(L)=u(e^{-L}).                   \tag{57.10a}
\]

Changing variables `y=r e^(-s)` below `r` and `y=r e^s` above `r` gives

\[
(Ju)(e^{-L})
=2LF(L)-\int_0^L F(t)\,dt+(RF)(L)
 -\log(1-e^{-L})F(L),                                    \tag{57.10b}
\]

where

\[
\begin{aligned}
(RF)(L)
={}&\int_0^\infty\frac{F(L)-F(L+s)}{e^s-1}\,ds\\
 &+\int_0^L\frac{F(L)-F(L-s)}{e^s-1}\,ds .              \tag{57.10c}
\end{aligned}
\]

This is an equality, not an estimate. For a cut-off `F(L)=L^(-tau)`, two integrals in
`(57.10c)` combine into an exponentially weighted second difference, so

\[
(RF)(L)=O(L^{-\tau-2})+O(e^{-L/2}).                      \tag{57.10d}
\]

It therefore proves indicial law `(57.8)` directly. More importantly, with

\[
H(L)=\sqrt L\,F(L),
\]

the leading block obeys

\[
\frac d{dL}\left(2LF(L)-\int_0^L F(t)dt\right)
=F(L)+2LF'(L)=2\sqrt L\,H'(L).                           \tag{57.10e}
\]

Thus an equation `(Ju)(e^-L)=Phi(L)` has exact trace equation

\[
2\sqrt L\,H'(L)
=\Phi'(L)-(RF)'(L)
 +\frac d{dL}\left[\log(1-e^{-L})F(L)\right].           \tag{57.10f}
\]

Whenever right side divided by `sqrt(L)` is integrable, canonical boundary trace

\[
\beta_+(u)=\lim_{L\to\infty}\sqrt L\,u(e^{-L})           \tag{57.10g}
\]

exists; reflection gives `beta_-`.  Exact Suzuki lower-order terms have favorable structure:
zeroth-order multiplication loses one inverse-log order, the finite translation **alphabet**
generates a countable graded seam orbit, and regular polar--Gamma convolution is endpoint-smooth.
Remaining boundary theorem is therefore a simultaneous log-Dini bootstrap on a countable graded
carrier, not a finite seam system and not discovery of boundary exponent or trace variable.

### New source-specific conjecture

Suzuki zero equation contains visible translations

\[
-\sum_{n\le e^{2a}}\frac{\Lambda(n)}{\sqrt n}
  \bigl(v(x-\log n)+v(x+\log n)\bigr).                   \tag{57.11}
\]

Endpoint layer `(57.10)` is transported to interior seam `x=a-log n`.  Division by principal log
symbol raises one-sided logarithmic exponent by one, predicting

\[
v(x)=C_a\frac{\Lambda(n)}{\sqrt n}c_+
 \bigl(-\log|x-(a-\log n)|\bigr)^{-3/2}+\cdots .          \tag{57.12}
\]

The exponent shift in `(57.12)` is not merely heuristic. A one-sided log-conormal germ with

\[
\widehat h(\xi)
=\frac{A e^{-ix_0\xi}}{i\xi}(\log|\xi|)^{-\alpha}
 +o\!\left(|\xi|^{-1}(\log|\xi|)^{-\alpha}\right)
\]

divided by `c(xi)=kappa log|xi|+O(1)`, `kappa>0`, has leading transform

\[
\frac{A e^{-ix_0\xi}}{\kappa i\xi}
(\log|\xi|)^{-(\alpha+1)}.
\]

The one-sided slowly varying Fourier Abelian law returns a spatial germ of exponent
`alpha+1`. Thus inverse logarithmic ellipticity raises seam order by exactly one and direct
coefficient is nonzero whenever `Lambda(n)c_+` is nonzero. Bounded oscillatory prime--Gamma terms
enter only at later inverse-log orders.

One resonance must be retained. Same-end seams are separated because `log n` is injective in
`n`, but opposite-end direct seams collide precisely when

\[
a-\log n=-a+\log m
\iff e^{2a}=mn.                                           \tag{57.12a}
\]

These discrete apertures do not create direct cancellation. The right-end layer transported by
`v(x+log n)` occupies the left punctured side of collision point; left-end layer transported by
`v(x-log m)` occupies right punctured side. Restricting to two half-neighborhoods recovers two
coefficients separately, so parity cannot erase either oriented germ. Later iterated collisions
are no longer an unclassified cancellation problem.  Let `P_a` be visible primes and form positive
Laurent polynomial on prime-valuation lattice

\[
T_a(z)=\sum_{p^j\le e^{2a}}\frac{\log p}{p^{j/2}}
       (z_p^j+z_p^{-j}).                                 \tag{57.12b}
\]

Grade-`k` coefficient at valuation vector `nu` is exactly `[z^nu]T_a^k`, positive iff at least one
length-`k` word reaches `nu`. Unique factorization gives

\[
\sum_p\nu_p\log p=\sum_p\mu_p\log p\iff\nu=\mu,        \tag{57.12c}
\]

so it classifies all same-end spatial collisions. Support pruning merely removes inadmissible
positive summands. Every prime propagation has one common nonzero real principal factor (with sign
fixed by operator convention); smooth polar--Gamma terms create no new interior one-sided singular
support. Hence first-arrival
coefficient at every admissibly reachable seam is nonzero **within any valid polyhomogeneous
expansion**. Translations preserve orientation, so
collisions between descendants of opposite endpoints remain separated on two punctured sides at
every grade.

Support pruning also retains density cofinally. Put `alpha=log 2`, `beta=log 3`, and
`Gamma=Z alpha+Z beta`. For every `a>beta`, admissible descendants of either endpoint are dense in

\[
C_a=(-a+\beta,a-\beta).                                  \tag{57.12d}
\]

Proof: `Gamma` is dense because `alpha/beta` is irrational. Choose
`d in Gamma intersect (beta,2a-beta)`. Order a reduced word for `-d` greedily around terminal value
`-d`; its partial sums stay in `(-d-beta,0)`, so starting at `a` it reaches
`b=a-d in C_a` without leaving aperture. For any `gamma` with `b+gamma in C_a`, greedily alternate
positive and negative letters in a reduced word for `gamma`; all partial sums lie between
`min(0,gamma)-beta` and `max(0,gamma)+beta`. Thus every point of
`(b+Gamma) intersect C_a` is admissibly reachable, and this set is dense. This proves

\[
a>\log3,\ \beta_+(v)\ne0
\Longrightarrow
\text{dense nonzero first-arrival seam germs in }C_a.   \tag{57.12e}
\]

Dense germs of increasing inverse-log grade can still converge in logarithmic form domain, so
`(57.12e)` is not itself contradiction. It closes geometry and collision gates and exposes two
genuinely analytic gates: trace separation for nonzero characteristic packets, and convergence plus
two-ended no-return for resulting graded state.

This yields **`SUZUKI-COMPLETED-LOG-SEAM-NO-RETURN`**:

> For actual polar--Gamma symbol and exact von-Mangoldt coefficients, logarithmic Dirichlet
> reconstruction of every finite characteristic packet has full two-ended half-log expansion.
> If square Evans residual vanishes, endpoint and propagated prime-seam coefficients satisfy a
> convergent countable transport system graded by inverse-log order, and that system has only zero
> solution.

The decisive chain is

\[
\det N_{a,0}=0
\Rightarrow\text{nonzero characteristic packet}
\Rightarrow\text{half-log endpoint/seam state}
\Rightarrow\text{two-ended transport contradiction}.    \tag{57.13}
\]

Generic logarithmic ellipticity cannot prove this: tuned log-order Dirichlet symbols can have
special-aperture zero modes.  Proof must retain exact `Lambda(n)/sqrt(n)` shifts and polar--Gamma
remainder.  Falsifiers are explicit: a flat boundary datum invisible to all half-log coefficients,
vanishing direct seam coefficient, or a nonzero packet satisfying exact two-ended system.

Research card:

- `docs/drafts/pipeline/1-in-progress/suzuki-completed-zero-mode-corona-seam-law.md`.

Arithmetic collision law `(57.12c)` and opposite-end resonance are formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/SuzukiPrimeValuationSeam.lean`, reusing existing full
prime-log linear independence. Formal tree still lacks Suzuki completed form and logarithmic
boundary calculus, so Lean does not yet certify analytic transport `(57.12)`. RH is not proved.
Actual corpus frontier is now exact: prove full
half-logarithmic expansion and trace separation, construct convergent valuation-graded transport,
and prove its two-ended no-return, equivalently `det N_(a,0)!=0` for every aperture.  Collision
classification and cofinal support-pruned density are no longer open.

## 58. Critical log-translation flux collapses infinite seam hierarchy to finite grade (2026-07-22)

Section 57 left two analytic tasks entangled: observation of half-log coefficients and convergence
of countable dense-seam transport.  The first now has an exact positive Hilbert metric, and the
second is not necessary for kernel exclusion.

For `alpha>0`, let a zero-extended one-sided germ be

\[
 f_{\alpha,c}(x)=c\,\chi(x)(\log(1/x))^{-\alpha},\qquad x>0,
\]

where `chi=1` near zero.  If `tau_h f(x)=f(x-h)` and `L_h=log(1/h)`, then

\[
 \boxed{\displaystyle
 \lim_{h\downarrow0}\frac{L_h^{2\alpha}}h
       \|\tau_hf_{\alpha,c}-f_{\alpha,c}\|_2^2=|c|^2.} \tag{58.1}
\]

The proof separates the exposed strip `(0,h)` from overlap.  After `x=ht`, the exposed term is

\[
 |c|^2\int_0^1
 \left(1+\frac{\log(1/t)}{L_h}\right)^{-2\alpha}dt\to |c|^2.
\]

On `(h,2h)` both normalized profiles converge to one, so their difference is `o(1)` by dominated
convergence.  On `(2h,epsilon)`, mean value gives

\[
 |f(x-h)-f(x)|\le
 C_\alpha\frac{h}{x(\log(1/x))^{\alpha+1}},
\]

whose squared integral is `O(hL_h^(-2alpha-2))+O(h^(3/2))`; smooth cutoff terms are `O(h^2)`.
This proves `(58.1)` without a boundary regularity import.

For two interval endpoints with coefficients `beta_+`,`beta_-`, the exposed strips are disjoint:

\[
 \lim_{h\downarrow0}\frac{L_h^{2\alpha}}h\|\tau_hu-u\|_2^2
 =|\beta_+|^2+|\beta_-|^2.                              \tag{58.2}
\]

At critical corona order `alpha=1/2`, normalization is `L_h/h`.  At seam grade `k`, where
`alpha=k+1/2`, normalization is `L_h^(2k+1)/h`.  A two-sided collision is seen unlocalized as
`|c_+-c_-|^2`; smooth one-sided localization recovers `|c_+|^2` and `|c_-|^2` separately.  Thus
every finite endpoint/seam coefficient is metrically observable, including resonant opposite
orientations.

The more important correction uses the completion-safe square-Evans carrier.  Let `F_a` be its
finite-dimensional characteristic packet and let `ell_i in F_a^*` be all scalar endpoint/seam
residual coordinates, indexed by arbitrary grade, valuation, and orientation.  Linear algebra gives

\[
 \bigcap_i\ker\ell_i=\{0\}
 \Longrightarrow
 \exists i_1,\ldots,i_m,\quad
 m\le\dim F_a,\quad
 \bigcap_{j=1}^m\ker\ell_{i_j}=\{0\}.                  \tag{58.3}
\]

For a natural grade hierarchy there is therefore one finite `N_a` such that vanishing through
grade `N_a` forces the packet to vanish.  Consequently a convergent infinite dense-seam state is
**not required** to exclude `ker A_a`.  It is enough to prove exact Suzuki expansion to every
prescribed finite order and the joint separation statement that an infinitely log-flat
characteristic packet is zero.  Equation `(58.3)` then selects a finite certificate automatically.

This changes the frontier from

```text
construct and sum an infinite dense transport state
```

to the sharper pair

```text
arbitrary finite-order source-faithful transport;
log-quasianalytic separation on the finite square-Evans packet.             (58.4)
```

The finite detector is formalized unconditionally as
`exists_finite_trace_detector` and `exists_finite_grade_trace_cutoff` in
`formal/GaloisForLFunctions/RHTower/SuzukiFiniteGradeTraceDetector.lean`.

There is also a concrete route to the missing first-crossing calculus.  Split Suzuki's fixed
whole-line form on compact support as

\[
 A=L_0+B,\qquad \widehat{L_0f}(\xi)=\log|\xi|\widehat f(\xi),
\]

with `B` the exact polar--prime--Gamma remainder, and regularize only the principal block by

\[
 L_s=\frac{(-\Delta)^s-I}{2s}.                          \tag{58.5}
\]

Fractional Hadamard theory detects `(u_s/delta^s)^2`.  Matching `delta^s=e^{-sL}` to the outer
half-log layer at `L` of order `1/s` predicts

\[
 \frac{u_s/\delta^s}{\sqrt s}\longrightarrow C_{\log}\beta,
\]

and hence the logarithmic crossing form conjecture

\[
 \dot\lambda_a(v,w)=
 -\frac{C_{\log}^2}{2}
 \bigl(\beta_+(v)\overline{\beta_+(w)}
      +\beta_-(v)\overline{\beta_-(w)}\bigr).          \tag{58.6}
\]

Primary audit found fractional eigenvalue and pointwise Green Hadamard formulas, but no proved
logarithmic-Laplacian version.  The only arXiv paper found advertising a logarithmic Pohozaev
identity is withdrawn for a crucial error in that proof.  Thus `(58.6)` is a genuine boundary-layer
problem, not an import.

Hostile sign audit is decisive: `(58.6)` alone does not prove RH.  Its negative sign is compatible
with a false-RH first crossing.  Its proof would establish trace transversality and reduce any
remaining invisible zero mode to infinite log-flatness.  The RH-bearing step is then `(58.4)` plus
exact finite-grade two-ended prime--Gamma no-return, equivalently `det N_(a,0)!=0` for every
aperture.

Research card:

- `docs/drafts/pipeline/1-in-progress/suzuki-log-translation-flux-finite-grade-detector.md`.

## 59. Whole-packet log separation is false; zero modes have corona and regular channels (2026-07-22)

Section 58's finite-dimensional theorem is correct, but its proposed separation premise is not.
Inverse-log traces do not see the whole square-Evans reconstruction.  A hostile exact model test
produces both a regular invisible channel and a more dangerous intermediate invisible channel.

First correct the literature boundary.  Chen--Weth proved decay `log^(-tau)` for every
`tau<1/2`, and Feulefack--Jarohs--Weth left the endpoint open.  Hernandez-Santamaria--Lopez
Rios--Saldana, arXiv:2401.18033v2, subsequently proved the optimal `log^(-1/2)` upper bound,
two-sided bounds for the torsion solution, and a half-log Hopf lower bound for nonnegative
supersolutions.  This validates the critical scale.  It does **not** prove a signed trace limit,
trace-zero `H1` regularity, or a boundary expansion for Suzuki's signed prime--polar perturbation.

The principal Volterra block already gives the exact classification needed to audit the proposed
trace hierarchy.  Put

\[
 (PF)(L)=2LF(L)-\int_0^L F(t)\,dt,qquad
 H(L)=\sqrt L F(L),qquad \Phi=PF.                       \tag{59.1}
\]

Then

\[
 \Phi'(L)=2\sqrt L\,H'(L).                               \tag{59.2}
\]

If `Phi'(L)/sqrt(L)` is integrable at infinity, the trace
`beta=lim sqrt(L)F(L)` exists and

\[
 \boxed{F(L)=\frac{\beta}{\sqrt L}
 -\frac1{2\sqrt L}\int_L^\infty\frac{\Phi'(t)}{\sqrt t}\,dt.} \tag{59.3}
\]

This is an identity.  If

\[
 |\Phi'(L)|\le C e^{-\sigma L}(1+L)^m,qquad \sigma>\tfrac12, \tag{59.4}
\]

then `(59.3)` has exactly two channels:

\[
\begin{array}{ll}
 \beta\ne0:&F(L)=\beta L^{-1/2}+O(e^{-\sigma L}L^{m-1}),
             \quad u(r)=F(\log(1/r))\notin H^1;\\
 \beta=0:&F,F'=O(e^{-\sigma L}L^{m-1}),
             \quad u\in H^1.
\end{array}                                               \tag{59.5}
\]

Indeed `F'=Phi'/(2L)-F/(2L)`.  In the second case the derivative energy has tail
`integral exp(-(2sigma-1)L)L^(2m-2)dL`; in the first it has tail
`integral exp(L)L^(-3)dL`.

The first counterexample is source-shaped:

\[
 F_{\rm reg}(L)=e^{-L}-2e^{-2L},\qquad
 PF_{\rm reg}=(2L+1)e^{-L}-(4L+1)e^{-2L}.                \tag{59.6}
\]

Every inverse-log coefficient of this nonzero solution vanishes, while in physical coordinates
`u_reg(r)=r-2r^2` lies in `H1`.  Thus all log grades cannot separate a finite characteristic
packet even when its forcing is exponential-polynomial.

There is a sharper generic obstruction.  Choose smooth `F_flat` equal to `e^(-sqrt(L))` for large
`L` and alter it on a bounded interval so that its total integral is zero.  Then on the tail

\[
 PF_{\rm flat}(L)=(2L+2\sqrt L+2)e^{-\sqrt L},           \tag{59.7}
\]

so solution and forcing are flat at every inverse-log order, but
`u_flat(r)=e^(-sqrt(log(1/r)))` is not in `H1`; its derivative energy contains
`integral L^(-1)e^(L-2sqrt(L))dL`.  Finite-dimensional compression cannot exclude this mode:
it only compresses a family **after** joint separation is established.

The countermodel is forced, however; it does not solve a homogeneous zero-mode system.  There is
an exact rigidity theorem for that missing case.  Let `F(L)` take values in a Banach seam carrier,
put `f(L)=||F(L)||` and `g(L)=integral_L^infinity f`, and suppose

\[
 2LF(L)-\int_{L_0}^L F(t)dt+T(L)F(L)+E(L)=0,            \tag{59.7a}
\]

with `sup ||T(L)||<=C`, `Lf(L)->0`, and

\[
 \|E(L)\|\le\tfrac12\{Lf(L)+g(L)\}.                    \tag{59.7b}
\]

If `g(L)=o(L^(-3/2))`, then `F` vanishes on a terminal half-line.  Indeed, passage to infinity in
`(59.7a)` first forces `integral F=0`.  Replacing the initial integral by the negative tail and
taking norms gives

\[
 (3L/2-C)f(L)\le3g(L)/2.
\]

For `L>=2C`, `g'=-f>=-3g/(2L)`, so `L^(3/2)g(L)` is nondecreasing.  A nonzero tail therefore has
a polynomial lower bound, contradicting inverse-log flatness.

This applies to the proposed intermediate sector once the exact remainder is relatively small.
At fixed aperture the prime translation alphabet is finite, hence bounded on a uniform seam
carrier.  Symmetrizing the exact Volterra remainder gives an exponentially weighted second
difference, bounded on a controlled tail by a local `F''` envelope plus `O(e^(-L/2))`; every
intermediate conormal scale `e^(-L^theta)`, `0<theta<1`, makes it `o(LF)`.  Thus the entire
intermediate transseries obstruction is reduced to one concrete source theorem: construct a
uniform oriented-seam carrier satisfying `(59.7b)` after regular power jets are subtracted.

The strongest survivor is a new two-scale architecture.  Inverse-log flux is a detector on the
completion-corona quotient, not on the whole packet.  For a regular zero mode Suzuki's exact
operator relation supplies the complementary connector

\[
 v\in\ker A_a\cap H^1_0(-a,a)
 \quad\Longleftrightarrow\quad
 Dv\in\ker(G_a:L^2_0(-a,a)\to L^2_0(-a,a)).             \tag{59.8}
\]

For the forward direction, `A_a` agrees on `H1_0` with `D^*G_aD`; hence `G_aDv` is constant, and
its zero mean makes it zero.  The reverse implication is immediate.  Therefore a zero-trace
regularity theorem would pass every invisible regular square-Evans mode to the already constructed
raw Evans Gram.

The new source-specific conjecture is **`SUZUKI-NO-INTERMEDIATE-BOUNDARY-SCALE`**:

> Every exact Suzuki zero mode has two endpoint half-log traces.  Nonzero traces generate the
> valuation-graded corona seams.  If both traces vanish, there is no inverse-log-flat non-`H1`
> homogeneous seam cycle; the mode lies in `H1_0`, with power remainder
> `O(r^sigma log(1/r)^m)` for some `sigma>1/2`.

This cannot follow from generic logarithmic ellipticity because `(59.7)` is an exact generic
countermodel.  It must retain Suzuki's finite von-Mangoldt translation alphabet and exact
polar--Gamma remainder.  If proved, every nonzero zero mode falls into exactly one live branch:

\[
\begin{array}{c}
 \text{nonzero corona state}\quad\xrightarrow{\text{prime--Gamma no-return}}\quad\bot,\\
 \text{zero corona state}\quad\xrightarrow{(59.8)}\quad
 \text{raw screw kernel}\quad\xrightarrow{\det(M_a^*M_a)>0}\quad\bot.
\end{array}                                               \tag{59.9}
\]

This is the actual frontier the corpus cannot solve: prove the no-intermediate-scale theorem,
prove corona no-return, and prove raw Evans Gram positivity for every aperture.  Section 58's
Lean finite detector remains useful only after restricting to the corona quotient.  No Lean
wrapper was added for `(59.3)`--`(59.9)`: current formal tree has no logarithmic boundary calculus,
and an abstract restatement would not certify the source theorem.

Research card:

- `docs/drafts/pipeline/1-in-progress/suzuki-corona-regular-two-scale-boundary-law.md`.

## 60. Dense Suzuki seams collapse to a two-root valuation Wiener problem

Section 59 left a uniform-carrier problem: iterated prime translations are dense in physical
space, so no simultaneous system of disjoint seam neighborhoods exists.  The correct carrier is
not spatial.  At fixed aperture let `P_a` be the finite visible-prime set and put

\[
 \Gamma_a=\mathbb Z^{P_a},\qquad
 \lambda(\nu)=\sum_{p\in P_a}\nu_p\log p,
 \qquad \mathcal W_a=\ell^1(\Gamma_a).                 \tag{60.1}
\]

Unique factorization makes `lambda` injective.  Every phase character

\[
 \operatorname{Ev}_\xi(c)
 =\sum_{\nu\in\Gamma_a}c_\nu e^{-i\xi\lambda(\nu)}
\]

is contractive on `W_a`, so an `ell^1` coefficient state can be evaluated even when its physical
phase set is dense.

After splitting the principal polar--Gamma logarithm, the exact finite-aperture high-frequency
symbol has source form

\[
 p_a(\xi)=\kappa L(\xi)+q_a(\xi)+\operatorname{Ev}_\xi(t_a),
 \qquad L(\xi)=\log\langle\xi\rangle,                  \tag{60.2}
\]

where `kappa>0`, `q_a` is bounded after the digamma logarithm is removed, and

\[
 t_a=-\sum_{p^j\le e^{2a}}\frac{\log p}{p^{j/2}}
       (\delta_{je_p}+\delta_{-je_p}),qquad
 M_a=\|t_a\|_1
 =2\sum_{p^j\le e^{2a}}\frac{\log p}{p^{j/2}}<\infty. \tag{60.3}
\]

The normalization in `(60.2)` must still be copied directly from Suzuki when the completed
analytic realization is built; no guessed value of `kappa` is used below.

There is now an exact convergence theorem.  For any discrete abelian group, `t in ell^1`, scalar
`|q(L)|<=C`, and

\[
 h_L=\kappa L\delta_0+q(L)\delta_0+t,
\]

if `kappa L>C+||t||_1`, then

\[
 h_L^{-1}=\frac1{\kappa L}\sum_{k\ge0}
 \left[-\frac{q(L)\delta_0+t}{\kappa L}\right]^{*k},
 \qquad
 \|h_L^{-1}\|_1\le
 \frac1{\kappa L-C-\|t\|_1}.                          \tag{60.4}
\]

Writing `rho_L=(C+||t||_1)/(kappa L)`, the tail after grade `N` is at most

\[
 \frac1{\kappa L}\frac{\rho_L^{N+1}}{1-\rho_L}.        \tag{60.5}
\]

This is the Banach-algebra geometric series, but its Suzuki consequence is new in the corpus: the
entire dense valuation seam state converges absolutely, not merely grade by grade.

It also closes first-arrival cancellation.  If `d(nu)` is shortest translation-word length
reaching `nu`, the common sign of Suzuki prime coefficients gives

\[
 (h_L^{-1})_\nu
 =\frac{(-1)^{d(\nu)}(t^{*d(\nu)})_\nu}
        {\kappa^{d(\nu)+1}L^{d(\nu)+1}}
   +O(L^{-d(\nu)-2}).                                  \tag{60.6}
\]

No lower Neumann grade reaches `nu`; at first grade no bounded zero-step factor can occur.  The
leading coefficient is therefore the nonzero common-sign sum of all shortest prime words.
Arithmetic collisions and infinite-grade convergence are both settled in one coefficient norm.

There is a second reduction.  Extend a putative zero mode `v` by zero outside `(-a,a)` and choose
the translation-invariant truncated Weil distribution `P_a` representing the same compression.
The interior equation says

\[
 b=P_a\widetilde v,qquad
 \operatorname{supp}b\subset(-\infty,-a]\cup[a,\infty). \tag{60.7}
\]

Splitting the two exterior half-lines and translating them to zero gives, exactly,

\[
 p_a(\xi)V(\xi)
 =e^{ia\xi}B_-(\xi)+e^{-ia\xi}B_+(\xi),qquad
 V=\widehat{\widetilde v}.                              \tag{60.8}
\]

The two `B` terms belong to opposite distributional Hardy classes once Suzuki's logarithmic form
domain is installed.  Applying `(60.4)` on the high-frequency tail in the root module

\[
 \mathcal W_a e_-\oplus\mathcal W_a e_+                \tag{60.9}
\]

shows that every dense seam coefficient is slaved to these two endpoint amplitudes.  Resonant
apertures may identify their evaluated physical phases, but not the two root labels or their
opposite one-sided orientations.

Crucially, `(60.8)` must **not** be divided globally by `p_a`: finite-frequency zeros are part of
the RH-bearing problem.  The exact remaining matching problem is

\[
 \boxed{
 V\in PW_a,\quad B_-\in H_+,\quad B_+\in H_-,\quad
 p_aV=e^{ia\xi}B_-+e^{-ia\xi}B_+.}                     \tag{60.10}
\]

Here all three spaces mean their completed logarithmic distribution versions.  At a real zero of
`p_a`, `(60.10)` imposes divisibility; on the high-frequency tail `(60.4)` supplies the unique
absolutely convergent valuation expansion.

The new source-specific conjecture is **`SUZUKI-TWO-PORT-RETURN-INJECTIVITY`**:

> For every aperture, the completed Suzuki classes contain no nonzero triple
> `(V,B_-,B_+)` satisfying `(60.10)`.

This conjecture is equivalent to `ker A_a=0` for every aperture and hence to RH; it is not a proof.
The scientific reduction is that the former countable dense-seam frontier is now a two-amplitude
Hardy divisibility problem with an explicitly inverted high-frequency tail.  The first genuinely
non-circular target is trace-zero endpoint classification: if both half-log components of
`B_-` and `B_+` vanish, prove `V` is `H1`.  Then `(59.8)` sends the mode to the raw screw kernel.
The only remaining branches are

\[
 \text{nonzero endpoint pair}\xrightarrow{\text{two-port no-return}}\bot,
 \qquad
 \text{trace-zero pair}\xrightarrow{H^1\text{ lift}}
 \ker G_a\xrightarrow{\det(M_a^*M_a)>0}\bot.           \tag{60.11}
\]

Thus actual corpus frontier is now narrower than Section 59: construct endpoint Hardy classes for
Suzuki's completion, exclude inverse-log-flat elements of matching kernel `(60.10)`, and prove raw
Evans Gram positivity.  Generic Wiener inversion cannot decide the finite-frequency matching
kernel, and assuming its contractivity or positivity would simply assume RH.

Research card:

- `docs/drafts/pipeline/1-in-progress/suzuki-two-root-valuation-wiener-lift.md`.

The standard parent theory is the Wiener convolution algebra and almost-periodic
pseudodifferential calculus of Shubin/Wahlberg.  Corpus already formalizes prime-log independence,
finite Laurent collision laws, and finite exponential-pencil coefficient extraction.  No Lean was
added: the concrete Suzuki multiplier, completion, exterior support split, and Hardy boundary
classes are absent, while formalizing only geometric series `(60.4)` would be non-RH bridge work.

## 61. Coherent causal fusion creates the missing cofinal cross-prime carrier

Section 60 was based on an incomplete frontier audit.  Its two-root Wiener matching problem remains
a valid secondary zero-mode reduction, but the formal corpus already proceeds much further through
entry-wall Green transport, FE light completion, all-prime cubic innovation, rectangular Ward
completeness, and S63's causal-depth Frostman law.  Actual unresolved RH-bearing statement before
this section was:

```text
SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY:
identify actual division-free Robin--Gamma--holonomy trace on completed wall carrier,
pay marked-halfgap and holonomy Schur debts,
and prove fixed-width rectangular Ward residual uniformly lower bounded.
```

S63 left its cross-prime correction unspecified.  Cubic innovation in fact gives enough damping to
construct it.  Fix `h,a>0`, put `alpha=ha/2`, and define

\[
 d_p=p^{-\alpha},\qquad
 r_p=p^{-(1/4+2\alpha)},\qquad
 z_p(t)=e^{it\log p/2}.
\]

The exact causal ray is

\[
 R_p(t)=\sum_{e\ge0}\psi_t(p,e)
       =\frac{A_pz_p(t)}{1-r_pz_p(t)},                   \tag{61.1}
\]

where

\[
 A_p=(h\sqrt h)^{-1}\sqrt{\log p}\,p^{-1/4}(p+1)^{-1}(1-d_p)^2.
                                                                  \tag{61.2}
\]

Since `r_p<=2^(-1/4)<1`, reverse triangle inequality and
`sqrt(x)<=(1+x)/2` give a height-uniform bound

\[
 |R_p(t)|\le C_h\sqrt{\log p}\,p^{-5/4}
       \le \frac{C_h}{2}(1+\log p)p^{-5/4}.              \tag{61.3}
\]

Both Dirichlet majorants converge.  Therefore a new legal source operation exists:

\[
 R(t)=\sum_pR_p(t)                                      \tag{61.4}
\]

converges absolutely over every prime and uniformly in height **before** any Gram square, FE light
split, or projective division.  Its energy is the absolutely convergent double-prime Gram

\[
 |R(t)|^2=\sum_{p,q}R_p(t)\overline{R_q(t)}.             \tag{61.5}
\]

Thus `p!=q` terms required by Gamma conductor capacity are actual source terms, not fitted
covariance.  Reflection is exact: `R(-t)=conjugate(R(t))`.

There is also a rigidity theorem.  Put `C=sum_p |R_p(0)|`.  Individual Frostman caps and triangle
inequality give

\[
 C^2-|R(t-u)|^2\ge0.                                   \tag{61.6}
\]

If equality holds, the nonnegative summable deficits
`|R_p(0)|-|R_p(t-u)|` all vanish.  Prime `2` and prime `3` then simultaneously attain their S63
caps; incommensurate prime-log clocks force `t=u`.  Hence

\[
 C^2-|R(t-u)|^2=0\quad\Longleftrightarrow\quad t=u.     \tag{61.7}
\]

Equations `(61.3)--(61.7)` are fully formalized, unconditionally, in
`SuzukiCoherentCausalDepthFusion.lean`.  They close cofinal cross-prime carrier existence and global
height observability.

The remaining frontier is now exact and smaller:

> **`SUZUKI-COHERENT-FUSION-GAMMA-WELD`.** Prove that centered projection of coherent field
> `(61.4)` against existing Gamma conductor coordinate is the concrete division-free
> Weil--Robin/polar--Gamma rectangular trace; incorporate marked-halfgap and holonomy graph debts;
> prove residual Xi Ward defect uniformly lower bounded on `a=log(n)/2`.

The Gamma projection itself has no sign mystery.  In `L2(mu_Gamma)`, if `f_p` is centered `R_p` and
`c` is centered conductor, then

\[
 f_p^\perp=f_p-\frac{\langle c,f_p\rangle}{\|c\|^2}c,
 \qquad K_{pq}=\langle f_p^\perp,f_q^\perp\rangle       \tag{61.8}
\]

is automatically PSD and exactly pays scalar conductor Schur tax.  Open issue is occurrence:
prove `(61.8)` is Suzuki's actual Robin--Gamma trace, not merely an available covariance.  Once
that trace identity and bounded residual are proved, existing Lean theorem
`riemannHypothesis_of_suzukiRectangularHilbertWardDefect_eventually_bddBelow` yields RH.

RH is not yet proved.  No further estimate or generic positivity lemma is missing; one concrete
source trace identity plus its graph-domain residual bound is.

Research and formalization:

- `docs/drafts/pipeline/1-in-progress/suzuki-coherent-fusion-gamma-weld.md`;
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-coherent-causal-depth-fusion.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-coherent-causal-depth-fusion.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCoherentCausalDepthFusion.lean`.

## 62. Connes/CCM aperture averaging collapses the phase wall to one Riesz-sector theorem

Section 61 is Suzuki-lane work and does not answer the Connes frontier.  The actual CCM open scalar
remains the adjacent-block value of the completed critical-Mellin error.  On a positive-growth mode
`exp(w x)`, its already formalized fixed-width multiplier is

\[
 M_L(w)=-\frac{(2w+1)(1-e^{-Lw})^2}{2w^2}.              \tag{62.1}
\]

It is nonzero for `Re(w)>0`, but its phase varies with `L`.  This filter-phase obstruction is now
closed by averaging over the **actual rectangular aperture**.  For every `a>0`, direct integration
gives

\[
 \boxed{\int_0^\infty e^{-aL}M_L(w)\,dL
 =-\frac{2w+1}{a(a+w)(a+2w)}}.                          \tag{62.2}
\]

The unit rate is canonical because the Volterra numerator cancels exactly:

\[
 \boxed{\int_0^\infty e^{-L}M_L(w)\,dL=-\frac1{w+1}},
 \qquad
 \Re\!\left(-\frac1{w+1}\right)<0\quad(\Re w>0).       \tag{62.3}
\]

There is a stronger pre-modal identity.  Width averaging produces causal kernel

\[
 K(t)=2e^{-t}-e^{-t/2},qquad
 \int_0^tK(s)ds=2(e^{-t/2}-e^{-t}),                     \tag{62.4}
\]

so

\[
 \boxed{K(t)+\frac12\int_0^tK(s)ds=e^{-t}.}             \tag{62.5}
\]

Thus aperture averaging cancels the entire Volterra memory in the completed Chebyshev potential.
For

\[
 e(x)=(\psi(e^x)-e^x)e^{-x/2},
\]

the averaged response is `-J(x)`, where

\[
 \boxed{
 J(\log X)=\frac1X\int_0^X\frac{\psi(y)-y}{\sqrt y}\,dy.}       \tag{62.6}
\]

This is the new source scalar.  It is not a generic smoothing: it is forced by exact cancellation
between CCM's Haar aperture factor and its critical Volterra factor.

The legal-width restriction `0<L<=x/2` does not reintroduce censorship.  For a hypothetical mode
`0<Re(w)<1/2`, the omitted tail is

\[
 -\frac{2w+1}{2w^2}\left[
 e^{(w-1/2)x}-\frac{2e^{(w/2-1/2)x}}{1+w}
 +\frac{e^{-x/2}}{1+2w}\right],                         \tag{62.7}
\]

which tends to zero.  Hence every possible off-critical zeta mode survives the admissible average
with limiting transfer `-1/(w+1)`.

### Exact remaining frontier

The detector now has fixed half-plane orientation, but a negative-real multiplier does not orient
an arbitrary complex source residue.  The genuine unresolved Connes theorem is
**`CCM-APERTURE-RESOLVENT-RIESZ-SECTOR`**:

> For every `epsilon>0`, the actual von-Mangoldt source satisfies
> \[
> \frac1n\int_0^n\frac{\psi(y)-y}{\sqrt y}\,dy
> \le C_\epsilon n^\epsilon
> \]
> eventually, proved without zero locations or Weil positivity.

The matching connector must apply the power-corrected one-sided Landau theorem to Mellin transform

\[
 \frac1{s+1}\left[
 -\frac{\zeta'(s+1/2)}{(s+1/2)\zeta(s+1/2)}
 -\frac1{s-1/2}\right]                                 \tag{62.8}
\]

and show this source bound excludes every pole with `Re(s)>0`.  This connector is open; so is the
source bound.  They are now the two honest steps to RH.  Fixed-width phase, Volterra memory, and
aperture-tail loss are no longer frontier problems.

Equations `(62.2)--(62.5)` are formalized unconditionally in
`CCMCriticalMellinApertureResolvent.lean`.  RH is not proved.

Research:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/ccm-critical-mellin-aperture-resolvent-law.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-critical-mellin-aperture-resolvent-law.md`;
- `docs/drafts/pipeline/1-in-progress/ccm-aperture-resolvent-riesz-sector.md`;
- `formal/GaloisForLFunctions/RHTower/CCMCriticalMellinApertureResolvent.lean`.

Internal corpus and targeted primary-paper searches found no prior occurrence of `(62.2)--(62.6)`.
External priority remains `[NOVELTY UNVERIFIED]`; elementary Laplace algebra alone is not a novelty
claim.

## 63. Unit-Riesz corpus closure: known-derived algebra formalized; one RH core remains

### Classification correction

The unit-aperture Riesz, Möbius-renewal, Markov-density, and causal-virial identities below are
now classified as **known-derived corpus infrastructure**, not new scientific knowledge.  Their
purpose is to prevent another research pass from rediscovering elementary Laplace/Möbius algebra
and presenting it as frontier progress.

### Formalized exact layer

Unit aperture gives

\[
 \frac{2(e^{-x/2}-e^{-x})}{\sqrt n}
 \bigg|_{x=\log(X/n)}
 =\frac2{\sqrt X}\left(1-\sqrt{n/X}\right).             \tag{63.1}
\]

The complete Möbius--log divisor dressing collapses exactly to the negative von-Mangoldt renewal,
whose physical atoms are nonnegative.  This is formalized in
`CCMCriticalMellinRieszMobiusRenewal.lean`.

For

\[
 W(t)=\frac3t\sum_{1\le r\le t}(1-\sqrt{r/t}),\qquad
 w(v)=W(e^v),                                             \tag{63.2}
\]

the cell `log m <= v < log(m+1)` is

\[
 w(v)=3me^{-v}-3\left(\sum_{r=1}^m\sqrt r\right)e^{-3v/2}. \tag{63.3}
\]

Lean proves

\[
 2m\sqrt{m+1}\le3\sum_{r=1}^m\sqrt r,                   \tag{63.4}
\]

the exact derivative of `(63.3)`, its nonnegativity throughout the cell, exact adjacent-cell
gluing, `w(0)=0`, and reduction of the global `floor(exp v)` profile to every cell.  These are in
`CCMUnitRieszMarkovDensity.lean`.

For the finite critical Möbius boundary, Lean also proves the exact virial cancellation

\[
 V_K(T)=1-(1+T)e^{-T}
       +\sum_{n\le K}\frac{\mu(n)\log n}{n}
 =1-(1+T)e^{-T}-Q_K.                                    \tag{63.5}
\]

This is `finiteCriticalMobiusCausalVirial_eq_logMoment` and
`finiteCriticalMobiusCausalVirial_eq_one_sub_logDefect` in
`CCMUnitRieszMobiusCausalVirial.lean`.

### Paper-level connector, not a novelty claim

Let `d=w'` almost everywhere.  Cell positivity and gluing give `d>=0` and `integral d=1`.  For the
critical causal complement

\[
 h_0(t)=e^{-t}-\sum_{n\le e^t}\frac{\mu(n)}n,
\]

the moving unit-Riesz coefficient factors as

\[
 I(T)=\int_0^T h_0(u)K_T(u)\,du=(d*V_{h_0})(T).          \tag{63.6}
\]

Its elementary Laplace calculation is

\[
 \mathcal Ld(z)=\frac{3z\zeta(1+z)}{2(z+1)(z+3/2)},     \tag{63.7}
\]

and

\[
 \mathcal LI(z)=\frac3{2(z+1)(z+3/2)}
 \left(\frac{\zeta(1+z)}{(1+z)^2}
       +\frac{\zeta'(1+z)}{\zeta(1+z)}\right).          \tag{63.8}
\]

Every zero `rho` contributes a genuine pole at `z=rho-1`.  Classical one-sided Landau therefore
shows that

\[
 \forall\epsilon>0,\qquad
 I(T)\ge-C_\epsilon e^{(-1/2+\epsilon)T}                \tag{63.9}
\]

implies RH.  Equations `(63.6)--(63.9)` are recorded as a paper proof and are **not** claimed fully
formalized in Lean.

### Actual frontier

All filter phase, Volterra memory, Riesz normalization, future Möbius dressing, cell positivity,
cell gluing, finite virial algebra, and Landau noncensorship are downstream infrastructure.  Sole
unproved RH-bearing Connes/CCM statement is `(63.9)`, equivalently the one-sided half-unit bound on
the positive Markov average of exact logarithmic Möbius defect `(63.5)`.

Generic Schur/coisometry contractivity cannot supply it: critical causal recombination gives
`e^{-t}`, Markov kernel is fixed in `T`, and `(63.8)` retains every off-line pole.  Required new
science must prove a source-specific signed first-crossing law for `Q_K` before scalar norm
estimation.  No such law is known or proved here.  **RH remains unproved.**

Corpus:

- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/ccm-unit-riesz-mobius-wavelet-reduction.md`;
- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/ccm-unit-riesz-markov-virial-landau-law.md`;
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm-unit-riesz-mobius-renewal-law.md`;
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm-unit-riesz-markov-density.md`;
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm-unit-riesz-mobius-causal-virial.md`;
- `docs/drafts/pipeline/1-in-progress/ccm-unit-riesz-causal-complement-wavelet.md`.

## 64. Boundary-channel completion law: finite algebraic obstruction closed

The CCM finite-clock correction no longer needs a simple-even radical premise at the level of
metric-adjoint completion. For finite real symmetric `T,D,Gamma` with

\[
T\Gamma=\Gamma T,\qquad \Gamma\eta=\eta,\qquad \Gamma\beta=-\beta,
\qquad DT-TD=|\beta\rangle\langle\eta|-|\eta\rangle\langle\beta|,
\]

Lean proves the radical transport law

\[
TDk=-\langle\eta,k\rangle\beta+\langle\beta,k\rangle\eta,
\qquad k\in\ker T.
\]

This yields an exhaustive three-channel completion:

1. if `eta` sees the radical, normalize `e` and use
   `A_E=D-|De><eta|`;
2. if `eta` vanishes but `beta` sees the radical, normalize `o` and use
   `A_O=D-|Do><beta|`;
3. if both vanish, Lean proves existence of `y` with `Ty=beta` and uses
   `A_N=D+|y><eta|`.

Every branch satisfies

\[
TA=A^{\mathsf T}T,\qquad A(\ker T)\subseteq\ker T,
\]

and the active channels are incompatible. Neutral source existence is derived from the
finite-dimensional dual-annihilator theorem, not assumed.

The concrete connector is also formalized. For every injective divided-difference matrix

\[
Q_{ii}=a_i,\qquad Q_{ij}=\frac{b_i-b_j}{c_i-c_j},
\]

with an involution satisfying `c_(rho i)=-c_i`, `b_(rho i)=-b_i`, and
`a_(rho i)=a_i`, Lean proves symmetry, exact rank-two displacement, reflection commutation, source
parity, preservation under every scalar shift, and existence of a completed clock. No positivity,
kernel dimension, or kernel parity premise occurs.

Formalization:

- `formal/GaloisForLFunctions/RHTower/CCMBoundaryChannelCompletion.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMDividedDifferenceInstantiation.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-boundary-channel-completion-trichotomy.md`;
- `docs/drafts/manuscripts/ccm-boundary-channel-completion/main.tex`.

Manuscript claim gate is strict: quotient spectra, real-root determinants, actual special-function
`Q_lambda^N`, simple-even ground states, normalized determinant transfer, and RH are not claimed.
Earlier draft language asserting those consequences was removed because no matching Lean
declarations exist.

Exact frontier remains source-specific. Corpus has no formal definition-to-theorem connector for
actual CCM `Q_lambda^N`, no proof of its cofinal branch selection, and no divisor-preserving
normalized determinant convergence to `Xi`. The new theorem closes finite metric-adjoint
completion only; it does not prove finite-Weil transfer or RH.

## 65. Correction: CCM endpoint is infinite, and finite rank two is only a boundary chart

Section 64 is not paper headline and not claimed as universal CCM law. It solves one finite
algebraic correction problem. Every finite matrix has closed range, so it cannot see decisive
cofinal obstruction: singular values accumulating at zero and inverse becoming unbounded.

The replacement theorem is formalized on an arbitrary complete real Hilbert space, with no
finite-dimensional, finite-rank, matrix-size, compactness, or trace-class parameter. For every
bounded operator `T`, Lean constructs the algebraic equivalence

```text
(ker T)^perp  ~=  range T,
```

whose inverse chooses unique preimage orthogonal to `ker T`; this needs no closed-range premise.
For bounded self-adjoint `T`, Lean proves sharp phase law

```text
IsClosed (range T)  <->  Nonempty (SymmetricSupportInverse T).
```

When equivalent conditions hold, support projection `P` and generalized inverse `G` are unique,
and for every bounded clock `D`

```text
S_T(D) = (1/2) (P D P + G D* T)
```

is supported on both sides, annihilates all of `ker T`, satisfies
`T S_T(D) = S_T(D)* T`, is idempotent, and has exactly supported `T`-self-adjoint operators as
fixed points. If range is nonclosed, Lean proves no bounded symmetric support inverse can exist.

Formal source:

- `formal/GaloisForLFunctions/RHTower/InfiniteSemimetricSymmetrization.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/infinite-semimetric-symmetrization-closed-range-law.md`;
- `docs/drafts/manuscripts/ccm-boundary-channel-completion/main.tex`.

This infinite theorem exposes rather than closes actual CCM/RH frontier. Corpus theorem
`ccm-exterior-inverse-symbol-graph-norm-law.md` proves at paper level that natural exterior
inverse-symbol block is positive and injective with dense nonclosed range. Therefore actual CCM
construction lies in nonclosed branch: it must prove exact finite-to-infinite range incidence and
construct controlled logarithmic graph-domain inverse or closed linear relation before forming
Feshbach/Evans reduction. No such source-defined graph relation, divisor-preserving cofinal
transfer, or RH proof is present. Finite rank-two corrections cannot decide this topological
branch.

## 66. Infinite nonclosed branch constructed: graph inverse and exact incidence law

Section 65's closed-range theorem was diagnosis, not final infinite carrier. Nonclosed branch now
has unconditional Lean construction on arbitrary real Hilbert space.

For every bounded `T`, define partial operator `G_T` by restricting `T` to `(ker T)^perp` and
inverting onto its algebraic range. Lean proves

```text
domain G_T = range T,
T (G_T y) = y,
graph G_T is closed,
G_T y = unique preimage orthogonal to ker T.
```

No self-adjointness or closed-range assumption is used for these statements. If range is nonclosed,
domain of `G_T` is nonclosed. If `T` is self-adjoint, `G_T` is formally symmetric on its domain.

For bounded self-adjoint `T` and arbitrary bounded `D`, Lean defines exact incidence domain

```text
I(T,D) = {x | D* (T x) in range T}
```

and closed-graph inverse symmetrizer

```text
GraphSymm(T,D)x = (1/2) (P D P x + G_T (D* T x)).
```

Lean proves its domain equals `I(T,D)`, entire radical belongs to domain and is annihilated, and

```text
<T GraphSymm(T,D)x, y> = <T x, GraphSymm(T,D)y>
```

for all domain vectors `x,y`. Dimension, defect rank, and radical rank are unrestricted.

Formal source:

- `formal/GaloisForLFunctions/RHTower/InfiniteSemimetricGraphInverse.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/infinite-semimetric-graph-inverse-incidence-law.md`;
- `docs/drafts/manuscripts/ccm-boundary-channel-completion/main.tex`.

This closes abstract graph-domain construction, but not source-specific CCM bridge. Exact remaining
frontier is to identify actual CCM boundary weight/clock with `T,D`, prove actual boundary source
satisfies incidence `D*Tx in range T` on required core, prove resulting Evans/Feshbach relation
has divisor-preserving cofinal transfer to `Xi`, then RH. None is assumed or claimed.

## 67. Correction: finite incidence is closed; live CCM obstruction is infinite/cofinal

The last paragraph of Section 66 overstates the remaining range-incidence gate.  The paper theorem
`ccm-log-symbol-dirichlet-exterior-reconstruction-law.md` already proves, for every aperture and
every interior characteristic forcing `f`, that

```text
u_f=C_(a,I)^(-1)f
```

exists uniquely in the global logarithmic multiplier domain.  Hence every finite characteristic
trace satisfies the exact exterior range-incidence condition.  The abstract graph inverse in
Section 66 is a faithful infinite-dimensional carrier theorem, but applying it again to prove
finite characteristic incidence would duplicate a closed paper-level CCM step.

The finite square Evans map

```text
N_(a,lambda):F_(a,lambda) -> R_(a,lambda)
```

is only an exact Grushin coordinate chart for the infinite restricted-Weil/Fredholm family.  Its
entries retain the full infinite logarithmic Dirichlet inverse.  Finite matrix size therefore does
not make the CCM problem finite, and no finite-rank theorem is a universal RH endpoint.

The actual unresolved CCM theorem is infinite and cofinal.  In either equivalent source-defined
form it is

```text
source-normalized Evans nonvanishing:
  E_a(lambda) != 0 for every a>0 and lambda<=0,

or, on the closed anti-causal logarithmic-source graph
  D_Xi=closure(P_- M_(-2 Xi'/Xi)),

four-unit boundary relative-trace contraction:
  limsup_(u->0+)
    ||Q_u D_Xi||_(S_2,ext)^2 / (4(1-exp(-u))) <= 1.
```

The corpus proves that either statement implies RH and that every off-critical divisor unit costs
strictly more than four units of boundary trace, whereas the incoming Euler pole carries exactly
four.  It does **not** prove the displayed nonvanishing or trace contraction.  This is the true
frontier: construct an infinite, orbit-sensitive prime--Gamma transport on the Xi graph and prove
it is nonexpansive at the singular boundary.  Finite Evans coordinates may diagnose its zeros but
cannot supply that transport.

Relevant corpus:

- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/ccm-log-symbol-dirichlet-exterior-reconstruction-law.md`;
- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/ccm-restricted-weil-square-evans-determinant-law.md`;
- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/ccm-weierstrass-stabilized-square-evans-line-law.md`;
- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/ccm-logderivative-closed-two-channel-graph-law.md`;
- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/ccm-hankel-boundary-relative-trace-four-unit-law.md`;
- `docs/drafts/pipeline/1-in-progress/ccm-direct-cofinal-weil-floor.md`.

## 68. Infinite off-diagonal Gamma-marginal repair is impossible in common-aperture Pick geometry

The scalar obstruction in Section 67 did not decide whether an infinite prime-mixing operator
could restore passivity. That escape is now closed under the exact unchanged-marginal interface.

On an arbitrary real Hilbert space with arbitrary Hilbert basis `(e_i)`, define

```text
D_x(u)=(||u||^2-||T_xu||^2)/(1-exp(-2x)),
K_(x,y)(u,v)
 =( <u,v>-<T_xu,T_yv> )/(1-exp(-(x+y))).
```

Lean proves the dimension-free boundary-charge law: if `T_y e_i -> e_i` for every basis vector,
`D_y(e_i)->0`, and the operator Pick inequalities

```text
K_(x,y)(u,v)^2<=D_x(u)D_y(v)
```

hold near the boundary, then every fixed interior `T_x` is the identity. The proof tests the Pick
inequality with `h=e_i-T_x^*e_i`; its cross term tends to
`||h||^2/(1-exp(-x))`, while its moving diagonal bound tends to zero. Hence `T_x^*e_i=e_i` for
every basis vector and totality gives `T_x=I`.

For every actual prime `p`, Lean also proves

```text
(1-c_p(y)^2)/(1-exp(-2y))->0,
```

where `c_p` is the Gamma-sewn Möbius contraction multiplier. Therefore no operator family, in any
Hilbert dimension, can simultaneously converge strongly to the identity on every prime basis
vector, preserve `||T_xe_p||=c_p(x)`, and satisfy common-aperture operator Pick positivity. The
forced identity contradicts the already formalized strict inequality `c_p(x)<1` for `x>0`.

Formal sources:

- `formal/GaloisForLFunctions/HTGeometry/BasiswiseBoundaryPickRigidity.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaSewnBasiswisePickMixingNoGo.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/gamma-sewn-basiswise-pick-mixing-no-go.md`.

This does not prove RH. It sharply changes the surviving CCM construction: off-diagonal mixing is
not enough if scalar Gamma marginals and strong boundary topology are retained. A viable
four-unit transport must alter first-order marginal charge, be genuinely singular/cofinal before
strong prime-basis closure, leave common-aperture Pick geometry, or change the marginals before
scalar trace. The exact RH frontier remains source-normalized Evans nonvanishing/equivalent
four-unit Xi graph contraction from Section 67; the admissible construction class is now smaller.

## 69. Radical-free CCM source-pencil Evans coefficient law

A selected ground/radical vector is no longer needed inside the finite polynomial whose cofinal
limit must be controlled. Lean proves the following universal law. For a split quotient
`B R=I`, an ambient operator `A` preserving `ker B`, `C=B A R`, and a factorization `T=L B` with
`m<=n`,

```text
[X^(n-m)] charpoly(T(A-zI))
  = det(C-zI) [X^(n-m)] charpoly(T).                       (69.1)
```

If `T A=T D+S`, the left side is

```text
[X^(n-m)] charpoly(T(D-zI)+S).                            (69.2)
```

For an active CCM boundary channel, displacement gives `T(Dc)=-beta`; hence the completed clock
`A=D-|Dc><alpha|` obeys

```text
T A=T D+|beta><alpha|.                                    (69.3)
```

If `T=B^*B`, metric adjointness proves preservation of the whole radical and the denominator in
`(69.1)` is nonzero. Therefore

```text
det(C-zI)
 = [X^(n-m)] charpoly(T(D-zI)+|beta><alpha|)
   / [X^(n-m)] charpoly(T).                               (69.4)
```

Reflection removes active-channel choice. Exactly one of the two explicit numerators

```text
[X^(n-m)] charpoly(T(D-zI)+|beta><eta|),
[X^(n-m)] charpoly(T(D-zI)-|eta><beta|)                   (69.5)
```

is the quotient determinant after normalization. Neither contains `c` or `R`. The theorem is
connected in Lean to actual scalar-shifted CCM divided-difference matrices, so `(69.5)` is not an
abstract finite-rank surrogate: it is the exact finite-section invariant of the cofinal CCM
family.

This corrects the determinant work program. Ground-vector approximation is not an intrinsic input
to the source polynomial. Exact unresolved theorem is now divisor-tight cofinal locally-uniform
convergence/nonvanishing of the coefficient ratio `(69.5)`, derived directly from Euler/Gamma
source data, or a category-wide proof that no such convergence can hold. Existing corpus shows
that quotient-determinant convergence remains RH-complete. Thus Section 69 is significant frontier
reduction, not RH and not CCM death.

Formal sources:

- `formal/GaloisForLFunctions/HTGeometry/RadicalQuotientEvansCoefficient.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMSourcePencilRadicalEvans.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-source-pencil-radical-evans-coefficient-law.md`.

Priority boundary: rectangular `AB/BA` characteristic identities and pseudodeterminants are
classical. Candidate new content is their CCM displacement/reflection assembly eliminating the
radical vector from the source/response numerator. External literature priority remains open.

## 70. Singular-Loewner central-slab source-order law

The first post-C28 rational-Pick formulation was too strong. From quotient columns

```text
(C-x_i)v_i=-u
```

one cannot infer that `u` is cyclic for arbitrary radical dimension, and one cannot assume clock
nodes avoid the quotient spectrum. Both failures occur when selected radical coordinates vanish.
The corresponding cyclic-denominator and regular-interpolation claims are withdrawn.

The correct theorem is stronger at singular nodes and needs no inverse. For any real symmetric
matrix `C`, common source `u`, and

```text
C v=xv-u,   C w=yw-u,   x<y,
```

Lean proves

```text
v dot w<0  ->  exists lambda in spec(C) intersect [x,y].       (70.1)
```

If the interval avoided the spectrum, simultaneous eigenbasis expansion would make every cross
coordinate nonnegative; Parseval contradicts the negative cross Gram product.

For the actual active-even CCM divided-difference matrix, arbitrary split Gram frame and arbitrary
radical dimension, the quotient columns satisfy

```text
C v_i=x_i v_i-u,
v_i dot v_j=(b_i-b_j)/(x_i-x_j).                              (70.2)
```

Thus a strict source descent `x_i<x_j`, `b_j<b_i` forces a zero of the actual complexified quotient
characteristic polynomial in `[x_i,x_j]`. Centered Xi is unconditionally nonzero on the closed
complex disk of radius four. Local-uniform convergence to Xi therefore implies the universal
moving-node law

```text
for every cofinal pair x_i<x_j in [-4,4], eventually b_i<=b_j. (70.3)
```

No dimension bound, corank bound, normalization nonvanishing, simple-evenness, quantitative rate,
or RH premise occurs.

This is the first direct source-only falsifier for C28's surviving active-even determinant branch.
It does not yet decide the branch. Exact source frontier is no longer vague pole tightness:
determine whether the published finite von-Mangoldt--Gamma sine coefficients have a persistent
descent in the central physical clock slab. One such cofinal descent kills divisor-faithful CCM
determinant convergence; eventual order is a necessary new arithmetic theorem but is not itself
divisor convergence.

Formal sources:

- `formal/GaloisForLFunctions/HTGeometry/PositiveResiduePoleForcing.lean`;
- `formal/GaloisForLFunctions/HTGeometry/HermitianLoewnerPoleForcing.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMPositiveResidueCentralSlab.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMSingularLoewnerPoleForcing.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-singular-loewner-central-slab-order-law.md`.

## 71. Published CCM coefficient is one explicit Chebyshev cosine test

Section 70 left the arithmetic input written as a sine transform of the distribution `D`. That
interface is now eliminated. Let `L=2a`, `t_n=pi*n/a`, and

```text
E_crit(h)=4*sinh(h/2)-sum_(2<=m<=exp(h)) Lambda(m)m^(-1/2),
rho_infinity(h)=exp(h/2)/(exp(h)-exp(-h)).
```

The polar--prime part is one Stieltjes pairing. Since `sin(t_n L)=0`, exact Stieltjes integration
by parts gives the complete published source coordinate

```text
b_n
 = (1/pi) integral_(0,L] sin(t_n h) rho_infinity(h) dh
   +(1/pi) integral_(0,L] E_crit(h)t_n cos(t_n h) dh.       (71.1)
```

Lean also replaces `E_crit` pointwise by the normalized Chebyshev Volterra potential. Hence the
active-even determinant lane has a source-only, computation-free falsifier:

```text
b_n<0 and 0<t_n<=4
  -> actual quotient charpoly has a real zero in [0,t_n],  (71.2)

quotient determinants -> Xi locally uniformly
  -> b_n>=0 eventually for every moving 0<t_n<=4.          (71.3)
```

This is not RH and not CCM death. Exact unsolved frontier is now one named arithmetic law: decide
cofinal nonnegativity versus persistent negativity of `(71.1)`. Do not return to cyclic response,
simple-evenness, radical-vector approximation, or unnamed `D`-transform analysis; those interfaces
have been eliminated from this branch.

Audit: all five new source files pass direct Lean; targeted cached build of
`GaloisForLFunctions.RHTower.CCMSingularLoewnerPoleForcing` passes `8971/8971`. Capstone axiom
checks report only `propext`, `Classical.choice`, and `Quot.sound`. Global lint has no attributable
failure; it currently fails on unrelated shared-tree modules not imported by their umbrellas.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMPublishedSourceSineCoefficient.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMSingularLoewnerPoleForcing.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-singular-loewner-central-slab-order-law.md`.

## 72. Exact character tomography closes the endpoint-energy geometry loophole

The physical prime-log endpoint carrier is an actual centered vector in complex `L2(0,A)`.  Its
nonzero aperture characters form a complete orthogonal family, and the zero character vanishes
by centering.  For every finite prime packet `P`, positive aperture `A`, and physical interval
parameters `(m,k)`, Lean proves

```text
sum_(n in Z, n!=0) normSq(characterAmplitude(P,A,n;m,k))
 = A * fusionEnergy(P,A;m,k).                              (72.1)
```

When `P=B union E` is split into bulk and clipped-edge primes, each character amplitude is exactly

```text
exp(k*r_n) * rectangularWindowAmplitude(k-m,r_n)
  * twistedPrimeSum(B,A,n) + characterAmplitude(E,A,n;m,k),
```

and the sum of its squared norms is still precisely the right side of `(72.1)`.  There is no
unseen Hilbert remainder and no loss from passing to all nonzero characters.

This formalizes the strongest exact positive statement exposed by the endpoint-energy route.  It
does not prove the required cofinal decay `fusionEnergy=O(M^(-1) polylog M)`, does not decide the
published source sign in `(71.1)`, and is not RH.  Its research use is a no-repeat boundary:
future work must produce arithmetic control of the complete character family or decide C30's
source descent; another Hilbert embedding, finite-channel Bessel bound, or bulk/edge repartition
cannot cross the frontier.

Formal source:

- `formal/GaloisForLFunctions/RHTower/CCMPhysicalPrimeApertureCharacterTomography.lean`.

## 73. Fixed spectral shifts desingularize the CCM source but preserve its entire tail spectrum

The published source admits one exact spectral-shift operation not previously connected to its
finite physical aperture. For `q=2`, multiplication by `1-exp(-2h)` is the physical coboundary of
`s -> s+2`, and Lean proves

```text
(1-exp(-2h))*rho_infinity(h)=exp(-h/2),  h>0.             (73.1)
```

At physical frequency `xi=pi*n/a`, the filtered Gamma term is

```text
(1/pi) xi*(1-exp(-kappa*2a))/(kappa^2+xi^2),             (73.2)
```

strictly positive for `a,kappa,n>0`. The complete filtered source is `(73.2)` plus one exact
completed-critical-Mellin-error derivative moment. Lean proves negativity occurs iff that moment
is smaller than the negative of the displayed Gamma budget.

The operation does not cross the RH frontier. The new universal multiplier theorem says that for
every eventually nonnegative carrier `eta`, every weight eventually satisfying
`0<c<=w(h)<=C`, and every real `epsilon`,

```text
w(h)eta(h)=O(exp(epsilon*h))
  iff eta(h)=O(exp(epsilon*h)).                            (73.3)
```

Hence zero exponential type is invariant. Every fixed positive shift coboundary tends to one, so
Lean specializes `(73.3)` to

```text
|(1-exp(-2h))*E_crit(h)|=O(exp(epsilon*h))
  iff |E_crit(h)|=O(exp(epsilon*h))                       (73.4)
```

for every rate `epsilon`. Fixed-shift Euler positivity and Gamma desingularization are therefore
provably inert at the completed-error abscissa; they cannot supply the missing half-unit of
continuation. Do not retry this class as an RH-closing mechanism.

The theorem classifies the whole finite fixed-shift algebra. A polynomial `P` in a positive shift
has multiplier `|P(exp(-q h))|`. If `P(0) != 0`, every exponential rate is invariant. If a filter
creates any rate absent from the original carrier, Lean forces `P(0)=0`. More sharply,
`P=X^m Q`, `Q(0)!=0`, translates the rate spectrum by exactly `q*m`. Thus every effective finite
filter lies in the augmentation ideal and is asymptotically noninvertible; stable finite shift
algebra cannot cross the CCM/RH seam. For arbitrary nonzero `P`, Lean performs the canonical
factorization and proves that the exact rate translation is
`q*rootMultiplicity(0,P)`; every other coefficient is invisible to the tail exponent.

This is a universal fixed-shift no-go, not RH and not death of the whole CCM lane. Any surviving
transport must be asymptotically singular/noninvertible or genuinely operator-valued and
orbit-sensitive before scalarization. Exact open endpoint remains source-normalized Evans
nonvanishing / four-unit Xi graph relative-trace contraction.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMPublishedSourceEvenShiftSieve.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMEvenShiftExponentialTypeRigidity.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-even-shift-exponential-spectrum-rigidity.md`.

## 74. Holomorphic fixed-shift calculus has a quantized aperture spectrum

The finite-polynomial classification in §73 is now extended to every norm-analytic germ of one
fixed positive shift, valued in an arbitrary complex normed space. Put `z(h)=exp(-q h)`, `q>0`,
and let `F` be analytic at the augmentation point `z=0`. Lean proves a complete dichotomy.

If `F` vanishes locally, `|F(z(h))|` is eventually zero. Otherwise `F` has finite vanishing order
`m`, and for every eventually nonnegative carrier `eta` and every real `epsilon`,

```text
|F(exp(-q h))| eta(h)=O(exp(epsilon h))
  iff eta(h)=O(exp((epsilon+q m)h)).                       (74.1)
```

Equivalently, the filtered carrier has zero exponential type exactly when the original carrier
has every rate strictly above `q m`. Holomorphic units have `m=0` and preserve the complete rate
spectrum. All Taylor coefficients beyond the first nonzero coefficient are invisible to aperture
exponents.

The theorem remains exact after replacing `|F|` by the norm of a vector-, bounded-operator-, or
Schatten-valued family. It assumes no dimension, rank, compactness, or scalarization. For the
actual CCM completed critical-Mellin error, Lean proves `(74.1)` with
`eta(h)=|E_crit(h)|`. Hence passing from finite shift polynomials to an infinite norm-convergent
operator power series creates no new route across the RH frontier. This is a complete no-go for
norm-holomorphic functions of one fixed shift, not for singular, cofinal, multiorbit, or closed
graph CCM constructions.

The exact survivor is sharper: any successful fixed-shift boundary transport must be nonanalytic
at `z=0`, have order growing with aperture, retain joint orbit coordinates, or live in a singular
graph topology not controlled by operator/Schatten norm. Source-normalized Evans nonvanishing /
four-unit Xi graph relative-trace contraction remains open; RH is not proved.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMAnalyticShiftSpectrumRigidity.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-holomorphic-fixed-shift-spectrum-quantization.md`.

## 75. Four-unit boundary charge is necessarily square-root singular

The exact boundary relative trace already forces a precise regularity class. For any curve `F`
into a normed target, put

```text
delta_F(u)=||F(u)||^2/(1-exp(-u)),
a_F(u)=||F(u)||/sqrt(1-exp(-u)).
```

Lean proves

```text
delta_F(u)->ell  ->  a_F(u)->sqrt(ell).                  (75.1)
```

If `F(0)=0` and `F` is norm-differentiable at zero, then `delta_F(u)->0`. Thus an exact four-unit
boundary curve has `a_F(u)->2` and cannot be norm-differentiable at zero. This applies to arbitrary
Hilbert, Hilbert--Schmidt, bounded-operator, and other normed targets; no dimension or rank enters.

This is a Lean closure theorem, not new scientific knowledge. The paper-level CCM boundary-trace
law already implies square-root Hilbert--Schmidt scaling, and the attack ledger already requires a
singular graph. Do not present `(75.1)` as RH progress or retry smooth/norm-holomorphic boundary
curves. Live theorem remains source-defined nonexpansive transport of the four-unit contact into
`Q_u D_Xi`, equivalently source-normalized Evans/model-space defect vanishing.

Formal sources:

- `formal/GaloisForLFunctions/HTGeometry/BoundaryTraceRamification.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMBoundaryTraceRamification.lean`;
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm-four-unit-boundary-square-root-ramification.md`.

## 76. Holomorphic-orbit spectrum quantization is dimension-free

The one-coordinate law of §74 is not a finite-dimensional artifact. Let `A,E` be arbitrary
complex normed spaces, let `gamma:C->A` be analytic at zero with `gamma(0)=0`, and let `F:A->E` be
analytic at zero. Along the physical arc define

```text
M(h)=||F(gamma(exp(-q h)))||,   q>0.
```

Lean proves a complete dichotomy. If `F circle gamma` vanishes locally, `M` is eventually zero.
Otherwise `m=ord_0(F circle gamma)` is finite and

```text
M(h)eta(h)=O(exp(epsilon h))
  iff eta(h)=O(exp((epsilon+q m)h))                      (76.1)
```

for every eventually nonnegative carrier and every real `epsilon`. No dimension, coordinate
cardinality, operator rank, compactness, or scalarization enters. Infinite-coordinate Banach
orbits and operator-ideal orbits are covered whenever their orbit and readout are norm-holomorphic.

For any finite family of commensurate positive shifts `k_i q`, the monomial orbit
`gamma(z)=(z^(k_i))_i` gives an explicit joint-calculus law. All cross-shift cancellations enter
only through the one composite order `ord_0(z |-> F((z^(k_i))_i))`; if that restriction is locally
zero, the physical multiplier is eventually zero. Lean also specializes `(76.1)` to the actual
completed critical-Mellin error.

This removes the finite/joint norm-holomorphic escape left in §74. It does not prove RH or kill
singular/cofinal CCM. A viable source-to-Xi transport must now leave fixed norm-holomorphic Banach
orbit geometry: ramified/nonanalytic boundary behavior, aperture-dependent cofinal order, or
closed-graph information invisible to ambient norm. Analytic core is classical; external novelty
of this complete CCM classification is still under audit.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMAnalyticOrbitSpectrumRigidity.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMCommensurateJointShiftSpectrumRigidity.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-dimension-free-holomorphic-orbit-spectrum-law.md`.

## 77. Ramification density selects analytic charge and monodromy

The ramified survivor left in §76 has an exact universal classification. For any complex normed
target, any `q>0`, and any germ `F:C->E` analytic at zero, put

```text
Delta_(q,F)(h)=||F(exp(-qh))||^2/(1-exp(-exp(-h))).
```

Lean proves, without assuming `F` nonzero or finite order, that

```text
Delta_(q,F)(h)->ell>0
  ==> m=ord_0(F)>0 and 2 q m=1.                         (77.1)
```

If `F` descends locally under any scalar deck generator `zeta`, then its leading analytic charge
satisfies

```text
zeta^m=1.                                              (77.2)
```

Equations `(77.1)`--`(77.2)` are the density--charge--monodromy law. They immediately exclude every
nontorsion scalar deck generator. For a primitive finite `r`th root with `q=1/r`, they force
`2m=r`: sheet number is even and the branch-selected leading character is `zeta^m=-1`. A descended
branch would require `zeta^m=1`, so no finite primitive deck-invariant norm-holomorphic branch can
carry positive finite density. Both no-gos specialize directly to the CCM value `ell=4`.

This closes fixed norm-holomorphic scalar ramification, not CCM. Infinite-order scalar rotations are
covered, but logarithmic universal covers, non-scalar deck representations, nonanalytic/cofinal
families, and graph-topological transports remain. Therefore exact frontier is no longer “try a
ramified analytic filter”; it is to construct or exclude a genuinely logarithmic/nonanalytic
source-to-Xi graph transport proving

```text
D_Xi=closure(P_- M_(-2 Xi'/Xi)),
limsup_(u->0+) ||Q_u D_Xi||_(S2,ext)^2 /
                (4(1-exp(-u))) <= 1,                   (77.3)
```

equivalently source-normalized Evans nonvanishing. C36 is unconditional Lean and internally novel
as a CCM classification; its analytic ingredients are classical and external novelty remains open.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMFiniteRamifiedBoundaryNoGo.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-ramification-density-monodromy-selection-law.md`.

## 78. Bounded holomorphic logarithmic descent has a quantized period

The logarithmic universal-cover survivor in §77 has now been decided for bounded norm-holomorphic
descent. Let `E` be any complete complex normed space, `h>0`, and let `f:C->E` be `h`-periodic,
eventually holomorphic, and bounded as `Im(z)->+infinity`. Define

```text
Lambda_f(t)=||f(it)||^2/(1-exp(-exp(-t))).
```

Periodicity descends `f` through the exact cusp coordinate

```text
q_h(z)=exp(2π i z/h),   q_h(it)=exp(-(2π/h)t).
```

Lean proves, for arbitrary complete normed targets, that the descended cusp function `F_h` has a
removable singularity and is analytic at zero. Combining this with §77 gives

```text
Lambda_f(t)->ell>0  ==>  h=4π ord_0(F_h).              (78.1)
```

Equation `(78.1)` is the logarithmic period--density charge law. For the ordinary deck period
`h=2π`, it requires `1=2 ord_0(F_h)`, impossible. Hence no bounded holomorphic `2π`-periodic
logarithmic branch carries any positive finite thermal density; in particular it cannot realize
the CCM four-unit boundary normalization. The same vector-valued cusp construction proves the
universal first-Fourier-mode gap

```text
f(z)=O(exp(-2π Im(z)/h))
```

whenever `f` tends to zero at the cusp.

This is unconditional Lean and closes bounded holomorphic logarithmic descent, including
infinite-dimensional Hilbert/operator targets. It does not prove RH or kill CCM. Unbounded or
nonanalytic cusp maps, aperture-dependent/cofinal families without one fixed periodic function,
non-scalar monodromy, and closed graph topology remain outside `(78.1)`. The exact frontier is now
the construction or exclusion of that genuinely graph-singular source-to-Xi transport proving

```text
D_Xi=closure(P_- M_(-2 Xi'/Xi)),
limsup_(u->0+) ||Q_u D_Xi||_(S2,ext)^2 /
                (4(1-exp(-u))) <= 1,                   (78.2)
```

equivalently source-normalized Evans nonvanishing. Analytic `q`-expansion ingredients are
classical; corpus search found no prior target-universal CCM period--density theorem, while
external literature novelty remains open.

Formal sources:

- `formal/GaloisForLFunctions/HTGeometry/PeriodicCuspBoundaryGap.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMLogarithmicCuspBoundaryNoGo.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-logarithmic-cusp-period-density-quantization-law.md`.

## 79. Meromorphic logarithmic cusps obey an integral Laurent charge law

The unbounded finite-order cusp survivor left by §78 is now closed without boundedness,
completeness, finite-dimensionality, or eventual-holomorphy assumptions. Let `E` be any complex
normed space, `q>0`, and `F:C->E` meromorphic at zero. Define

```text
Delta_(q,F)(t)=||F(exp(-q t))||^2/(1-exp(-exp(-t))).
```

Lean proves the universal meromorphic charge-rate law

```text
Delta_(q,F)(t)->ell>0
  ==> exists n in Z: ord_0^mero(F)=n, n>0, 2 q n=1.      (79.1)
```

Finiteness of order and nontriviality are conclusions. If the order is `top`, the germ is zero on
a punctured neighborhood and the density is eventually zero. Otherwise vector-valued Laurent
normal form gives

```text
F(z)=z^n G(z),  G analytic at 0,  G(0)!=0,
Delta_(q,F)(t)=exp((1-2 q n)t) U(t),
U(t)->||G(0)||^2>0,
```

so a finite positive limit forces `(79.1)`. In particular poles and nonzero constant germs are
excluded automatically.

For an `h`-periodic map `f`, assume only that its descended cusp germ under
`q_h(z)=exp(2π i z/h)` is meromorphic at zero. The exact central-ray identity
`q_h(it)=exp(-(2π/h)t)` turns `(79.1)` into

```text
ord_0^mero(F_h)=n>0,   h=4π n.                          (79.2)
```

Thus no `2π`-periodic meromorphic logarithmic cusp in any complex normed target carries any
positive finite thermal density, including the exact CCM four-unit normalization. This strictly
extends §78 from bounded holomorphic cusps to every unbounded finite Laurent singularity.

This is unconditional Lean but not RH and not death of whole CCM. The surviving category is now
sharp: a viable one-loop cusp must be essential/nonmeromorphic at zero, cofinal with no fixed germ,
non-scalar-monodromic, or a closed graph relation invisible to ambient norm. The exact CCM frontier
remains

```text
D_Xi=closure(P_- M_(-2 Xi'/Xi)),
limsup_(u->0+) ||Q_u D_Xi||_(S2,ext)^2 /
                (4(1-exp(-u))) <= 1,                    (79.3)
```

equivalently source-normalized Evans nonvanishing. Next work must derive `(79.3)` from the exact
source-rigged Plücker/Tate capacity geometry or exclude every essential/graph-singular transport;
another meromorphic cusp is closed by `(79.2)`.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMMeromorphicCuspBoundaryNoGo.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-meromorphic-cusp-laurent-charge-law.md`.

## 80. Essential one-loop Hilbert cusps realize the four-unit boundary law

The essential survivor left by §79 is genuinely nonempty.  Let

```text
H=L2((0,1),dt),
f(z)(t)=2 sqrt(2) exp(-t exp(-i z)).
```

Lean proves that `f:C->H` is entire and exactly `2π`-periodic.  Along the central ray, with
`u=exp(-y)`,

```text
||f(iy)||^2
 = integral_(0,1] 8 exp(-2t/u) dt
 = 4u(1-exp(-2/u)).                                     (80.1)
```

Therefore

```text
||f(iy)||^2/(1-exp(-exp(-y))) -> 4.                     (80.2)
```

The four units are carried by a genuine endpoint boundary layer.  For every fixed
`0<δ<=1`,

```text
integral_(δ,1] 8 exp(-2t/u) dt
 =4u(exp(-2δ/u)-exp(-2/u)),
```

and division by `1-exp(-u)` tends to zero.  Hence every region separated from `t=0` loses all
normalized energy even though the total normalized energy tends to four.

Combining `(80.2)` with §79 proves that the descended cusp under `q=exp(iz)` is not meromorphic at
zero.  This is formalized directly, not inferred from a scalar point-evaluation argument.  The
packaged theorem

```text
exists_entire_twoPi_periodic_fourUnit_essential_Hilbert_cusp
```

returns an entire one-loop map, exact four-unit density, and nonmeromorphic descent in one
unconditional statement.

This settles the sharpness question raised by §79: norm-holomorphy on the logarithmic cover,
ordinary deck periodicity, infinite-dimensional Hilbert geometry, and exact four-unit density do
not exclude essential cusp descent.  A category-wide CCM death proof cannot be obtained from
those properties alone.

This is not the published CCM arithmetic source and proves neither RH nor CCM death.  Exact
frontier is now source-specific:

```text
D_Xi=closure(P_- M_(-2 Xi'/Xi)),
limsup_(u->0+) ||Q_u D_Xi||_(S2,ext)^2 /
                (4(1-exp(-u))) <= 1,                    (80.3)
```

or an obstruction that uses an actual von-Mangoldt--Gamma/source-rigged invariant to exclude
essential, cofinal, non-scalar-monodromic, and graph-topological transports.  C29--C30's published
active-even coefficient sign remains another exact source-only decision point.  Do not repeat
local meromorphic or log-holomorphic exclusion attempts against the essential category.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMEssentialCuspBoundaryLayer.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-essential-cusp-boundary-layer-sharpness.md`.

## 81. First published CCM clock is an exact RH-complete source coordinate

The unresolved first-clock sign from §§70--73 is now proved to be sufficient for RH.  Put

```text
B_1(L)=ccmPublishedSourceSineCoefficient(L/2,2*pi/L),
Q(L)=ccmFirstClockXiRationalDivisor(L).
```

The literal source dictionary gives

```text
B_1(L)=(2/L)Q(L),                    L>=pi/2.             (81.1)
```

The complete first-clock divisor and Xi screw satisfy the fixed dilation law

```text
Q(L)=S(L)+integral_0^1
  2*pi*sin(2*pi*x) S(Lx) dx.                              (81.2)
```

Assume only `B_1(L)>=0` for every `L>=pi/2`.  A positive-tail continuous Landau argument,
using the branch-free cubic continuation inside the source-defined Xi cone, propagates every
positive exponential moment of `Q`.  The dilation kernel has the strict Mellin-tail contraction

```text
integral_(15/16)^1 |2*pi*sin(2*pi*x)|/x dx
  <=2/15<1.                                               (81.3)
```

Truncated weighted `L1` absorption and exhaustion in `(81.2)` therefore propagate the
unconditional screw seed above abscissa `1/2` down to every positive abscissa.  The exact screw
Laplace/logarithmic-derivative identity then excludes every off-critical Xi zero.  Lean proves

```text
CCMFirstClockPublishedSourceNonnegative
  <-> RiemannHypothesis.                                  (81.4)
```

No finite-rank, simple-evenness, determinant convergence, rightmost zero, numerical zero
verification, or auxiliary analytic hypothesis occurs.  This closes the analytic transfer that
had separated the published source from the RH endpoint.

This is not an RH proof: `(81.4)` identifies the remaining source arithmetic exactly.  Frontier
is no longer a CCM transfer problem.  It is the unconditional sign of the explicit
von-Mangoldt--Gamma functional

```text
B_1(L)
 =1/pi * integral_(0,L] sin(2*pi*h/L) rho_infinity(h) dh
  +1/pi * integral_(0,L] E_crit(h) (2*pi/L)
      cos(2*pi*h/L) dh.                                   (81.5)
```

Proving `(81.5)>=0` for all `L>=pi/2` proves RH; one negative value disproves RH.  Generic theta
positivity cannot orient this clock: its compact Fourier density is proportional to
`-sin(2*pi*|u|)` and changes sign at half aperture.  Any next proof must supply a genuinely
arithmetic inner/outer half-wave transport or a source-specific positive factorization.  Do not
return to Volterra estimates, normal convergence, finite clocks, or simple-evenness; those
interfaces are closed.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMFirstClockLandauTransform.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockLandauHead.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockLandauDivisor.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockLandauCarrier.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockLandauDescent.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockLandauHalving.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockLandauDyadic.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockVolterraReflection.lean`;
- `docs/drafts/pipeline/1-in-progress/ccm-first-clock-landau-completeness-law.md`.

## 82. First-clock midpoint reflection isolates the RH-complete prime transport

The literal source in `(81.5)` now has an unconditional positive-mass normal form.  For
`xi*L=2*pi`, define

```text
g(h)=rho_infinity(h)-2*cosh(h/2),
Delta_L g(h)=g(h)-g(h+L/2),

C(L,xi)=integral_0^(L/2) sin(xi*h) Delta_L g(h) dh.
```

The sine cancels the removable Gamma pole at zero.  Midpoint translation negates one complete
sine period, while `rho_infinity` is strictly decreasing and `cosh` strictly increasing on the
positive axis.  Lean therefore proves

```text
C(L,xi)>0.                                                (82.1)
```

For the finite prime-power sine mass, let

```text
P_plus =sum Lambda(k)/sqrt(k) max(sin(xi log k),0),
P_minus=sum Lambda(k)/sqrt(k) max(-sin(xi log k),0).
```

Both are nonnegative, and the complete literal source law is

```text
pi*ccmPublishedSourceSineCoefficient(L/2,xi)
  =C(L,xi)+P_plus(L,xi)-P_minus(L,xi).                    (82.2)
```

At `xi=2*pi/L`, `P_plus` and `P_minus` are respectively the inner and outer logarithmic
half-wave masses.  Combining `(82.2)` with `(81.4)` gives

```text
RiemannHypothesis
  <->
for every L>=pi/2,
  P_minus(L)<=C(L)+P_plus(L).                             (82.3)
```

This is a source-only positive-mass criterion, not an RH proof.  It closes Gamma orientation:
the continuous term is strictly favorable at every aperture, so every possible sign failure is
exactly an outer prime-power excess.  Do not re-open Gamma monotonicity, removable-singularity
integrability, or signed-prime decomposition.

The remaining frontier is concrete: build an unconditional source-preserving transport from the
reflected outer prime-power measure to the inner prime-power measure plus the Gamma--polar
continuous budget, at sine cost, uniformly in `L`; or prove a CCM-native obstruction to every
such transport.  Atomwise reflection cannot do this because `log k -> L-log k` does not preserve
prime-power logarithms, and summing powers of one prime cannot repair an outer prime whose higher
powers lie beyond the aperture.

Formal source:

- `formal/GaloisForLFunctions/RHTower/CCMFirstClockHalfWaveReflection.lean`;
- `docs/drafts/pipeline/1-in-progress/ccm-first-clock-landau-completeness-law.md`.

## 83. Actual Euler current selects the essential cusp; Abel phase is positive

Essential cusp from §80 is now identified with actual CCM source at full critical clock response.
For normalized boundary-layer energy, canonical coordinate `x=2t/u` has exact finite-scale CDF

```text
Prob_u(X<=x)
 =(1-exp(-x))/(1-exp(-2/u)),       0<=x<=2/u.             (83.1)
```

Hence it is `Exp(1)` conditioned on `x<=2/u`. Its full complex response is

```text
H_u(t)
 =[1-exp(-(1-it)2/u)]/[(1-it)(1-exp(-2/u))]
 ->(1-it)^(-1).                                          (83.2)
```

This profile is selected directly by actual positive von Mangoldt fixed current. Put

```text
A(s)=-zeta'(s)/zeta(s),
s_(sigma,t)=sigma-i t(sigma-1).
```

In `sigma>1`, Lean proves literal Euler identity

```text
A(s_(sigma,t))/A(sigma)
 =[sum Lambda(n)n^(-s_(sigma,t))]/
   [sum Lambda(n)n^(-sigma)].                             (83.3)
```

Residue `1` of `A` at `s=1` gives

```text
A(s_(sigma,t))/A(sigma)->(1-it)^(-1),                    (83.4)

A(s_(sigma,t))/A(sigma)-H_u(t)->0                        (83.5)
```

under independent `sigma->1+`, `u->0+`. Its sine orientation is therefore unconditional:

```text
Im A(s_(sigma,t))/A(sigma)->t/(1+t^2)>0,   t>0,          (83.6)
```

including first CCM phase `t=2*pi`.

This is not RH. It closes a frontier ambiguity: essential Hilbert cusp is source-selected at
clock/Fisher/complex-response level, and positive phase already holds in safe Euler/Abel region.
Remaining RH-complete operation is singular half-weight hard de-Abelization from
`Lambda(n)n^(-sigma)` to literal `Lambda(n)/sqrt(n)` first aperture, retaining Gamma--polar
midpoint-reflection budget. C32--C39 exclude bounded scalar, fixed holomorphic, meromorphic, and
regular cusp transports; `(82.3)` proves successful source-preserving hard transport is exactly RH.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMEulerEssentialBoundaryLayerCorrespondence.lean`;
- `formal/GaloisForLFunctions/RHTower/EulerSquarefreeAffineFisherCutoffWard.lean`;
- `docs/drafts/pipeline/1-in-progress/ccm-euler-essential-boundary-layer-correspondence.md`.

## 84. Half-weight de-Abelization increases the bad first-clock odds

The remaining half-weight seam has an unconditional direction.  For `sigma>=1/2`, define the
first-aperture prime half-wave masses using literal weights `Lambda(n)n^(-sigma)`:

```text
P_plus(sigma,L)
 =sum_(2<=n<=exp L) Lambda(n)n^(-sigma)
    max(sin(2*pi*log(n)/L),0),

P_minus(sigma,L)
 =sum_(2<=n<=exp L) Lambda(n)n^(-sigma)
    max(-sin(2*pi*log(n)/L),0).
```

Lean proves the source-specific total-positivity law

```text
P_minus(1/2,L) P_plus(sigma,L)
 >= P_minus(sigma,L) P_plus(1/2,L).                      (84.1)
```

More generally, for any finite positive source separated by one cut, increasing exponential tilt
in the support coordinate increases the division-free outer/inner odds.  Expanding both sides as
a double sum reduces each term to

```text
theta_2*x+theta_1*y >= theta_1*x+theta_2*y
```

for outer `x` and inner `y`, so `(84.1)` is exact and uses no prime estimate.

This directly answers why §83's positive safe Euler phase does not de-Abelize to RH: the critical
half-weight tilt is directionally hostile.  It shifts relative mass toward the counter-phased
outer half-wave.  Positive diagonal reweighting of the same atoms therefore cannot be the missing
CCM transport.

Exact remaining frontier is narrower:

> construct a genuinely non-diagonal, Gamma-sewn source operation whose continuous
> midpoint-reflection budget absorbs the explicit odds inflation in `(84.1)`, uniformly for every
> `L>=pi/2`; or prove no source-faithful CCM operation can do so.

By `(82.3)`, successful absorption proves RH.  Equation `(84.1)` does not prove RH and does not
kill every CCM transport; it kills the direct positive diagonal bridge from the actual Abel
current.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMFirstClockExponentialTiltOdds.lean`;
- `docs/drafts/pipeline/1-in-progress/ccm-first-clock-exponential-tilt-odds-law.md`.

## 85. Infinite convolution nonlinearities are scalar on the irreducible prime face

The first exact non-diagonal candidate after §84 was Möbius/Dirichlet convolution: a composite
outer atom can split into factor pairs, and every product below the aperture has at least one
factor in the inner half. The mechanism fails universally at irreducible primes.

For arithmetic functions with values in any semiring, Lean proves

```text
(f*g)(p)=f(1)g(p)+f(p)g(1)                              (85.1)
```

at every prime `p`. Consequently the `n`th convolution power obeys the full noncommutative
prime-face chain rule

```text
(f^n)(p)
 =sum_(i=0)^(n-1) f(1)^i f(p) f(1)^(n-1-i).             (85.2)
```

This is not finite-rank or scalar. For every complete real normed algebra, including
infinite-dimensional noncommutative operator algebras, an arbitrary coefficientwise infinite
convolution series

```text
Phi_c(f)=sum_(n>=0)c_n f^n
```

satisfies

```text
Phi_c(f)(p)
 =sum_(n>=0)c_n sum_(i=0)^(n-1)
    f(1)^i f(p) f(1)^(n-1-i).                           (85.3)
```

The same derivative map acts at every prime and no term contains another prime coefficient
`f(q)`. Hence no scalar- or operator-valued infinite Dirichlet-convolution functional can mix
distinct irreducible prime faces.

For scalar Gamma/unit sewing

```text
f_a=a*delta_1+Lambda,
```

equation `(85.3)` becomes

```text
Phi_c(f_a)(p)=Phi_c'(a) log p.                           (85.4)
```

At the literal physical first clock this gives the atomwise and summed laws

```text
transformedPrimeAtom(p,L)
 =Phi_c'(a) criticalMellinAtomWeight(p)
    sin(2*pi*log(p)/L),                                  (85.5)

transformed irreducible-prime mass
 =Phi_c'(a) original irreducible-prime mass.             (85.6)
```

The scalar is independent of prime and aperture. Thus Möbius inversion, Selberg/Dirichlet
convolution, Euler-product powers, convolution-generated Fock lifts, arbitrary scalar Gamma
shifts, and their coefficientwise infinite operator-valued power series cannot implement the
outer-prime-to-inner-plus-Gamma transport required by `(82.3)`. They may change composites and
higher prime powers, but irreducible outer primes are only rescaled or erased.

This is unconditional Lean and a candidate new universal package. Prime divisor
indecomposability and convolution Leibniz rules are classical; novelty is restricted to the
noncommutative infinite-series law plus the exact RH-complete CCM prime-face connector. External
priority remains provisional. It is not RH and not death of whole CCM.

Exact survivor is now sharper: a successful CCM operation must be genuinely cross-prime, not
generated endogenously by Dirichlet convolution, and must sew the continuous Gamma budget while
preserving the literal source. By `(82.3)`, constructing that operation proves RH; excluding every
CCM-admissible cross-prime operation kills the lane.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMInfiniteConvolutionPrimeFaceRigidity.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-infinite-convolution-prime-face-rigidity.md`.

## 86. Ax+b subdivision and infinite block--Gamma defect carrier

The surviving non-diagonal first-clock attack now has one exact source carrier.  On successor-edge
sequences define

```text
(A_q u)(n)=q^(-1/2) sum_(0<=a<q)u(qn+a).
```

For every multiplicative `F`, exact block telescoping gives

```text
A_q d_F=q^(-1/2)F(q)d_F,
d_F(n)=F(n+1)-F(n).
```

For `F_t(n)=n^(it)`, the first coordinate of
`sum_(q<=exp L)Lambda(q)A_q d_(F_t)` has imaginary part equal to the literal hard-cutoff CCM
prime sine mass.  This preserves physical scale and avoids the fixed-fibre error that killed
future-product dressing.

More importantly, the same block algebra contains the exact infinite Gamma carrier.  Initial
normalized block seeds satisfy

```text
<V_m e_0,V_n e_0>=exp(-|log m-log n|/2),  V_q=A_q^*.
```

The complete tensor degrees `1 mod 4` obey

```text
sum_(j>=0)<V_m e_0,V_n e_0>^(4j+1)
 =ccmPublishedArchimedeanDensity(|log(m/n)|).
```

Polar completion cancels the degree-one decaying sector exactly:

```text
ccmFirstClockContinuousSourceDensity(h)
 =sum_(j>=1)exp(-(2j+1/2)h)-exp(h/2).
```

Hence continuous reflection is the higher `5,9,13,...` block-Fock tail plus the reflected polar
boundary.  Meanwhile the critical prime radial weight is the universal shift defect

```text
r/(1-r^4)-r^5/(1-r^4)=r,  r=q^(-1/2).
```

The published prime clock is therefore exactly the phase-weighted von Mangoldt relative-defect
trace of the same infinite block-Fock ladder.  These laws are unconditional and Lean-formalized
in:

- `formal/GaloisForLFunctions/RHTower/CCMFirstClockBlockSubdivisionTransfer.lean`;
- `docs/drafts/pipeline/1-in-progress/ccm-first-clock-direct-positive-factorization-attack.md`.

This is not RH.  It removes the former representational ambiguity—Gamma and hard prime clock now
live in one source-defined infinite algebra—and identifies the actual endpoint:

> Prove that the singular, cross-prime four-grade codiagonal makes the phase-weighted relative
> defect trace plus the reflected polar boundary nonnegative at `t=2*pi/L` for every
> `L>=pi/2`; or prove every source-admissible closure retains a negative vertical innovation.

A grade-preserving Fock lift cannot work because the degree-one Gamma sector cancels.  Ordinary
contraction proves only the unphased defect positive and does not control the counter-half-wave
sine.  Bounded/scalar completions are already excluded by the codiagonal saturation corpus.

The finite cross-prime geometry is also exact:

```text
BlockConst(lcm(m,n)) <-> BlockConst(m) and BlockConst(n).
```

Thus finite noncommuting block meets recover the physical causal LCM ridge without scalar
convolution.  But the cofinal unrenormalized meet over all `q>=2` contains only constant
sequences, hence is zero in `ell^2(N)`.  Lean proves both the LCM law and the universal constant
collapse.  Any live block transport must therefore be a critically renormalized relative defect
taken before the zero strong limit; an ordinary alternating-projection exhaustion is dead.

## 87. Complete Xi Ward transport is a non-diagonal four-unit Hardy contraction

The constructed Schwarz-paired Xi Ward phase now has unconditional operator-level, not merely
pointwise, contractivity. For every finite right-half-plane packet `w`, real `alpha>=0`, and

```text
G_ij=1/(w_i+conj(w_j)),
Phi_i=xiRightWardBoundarySourcePhaseCrossRatio(i*w_i,alpha),
V_i=mobiusGammaXiAntiCausalWardTransportV(w_i,alpha)=1-Phi_i,
```

Lean proves

```text
[(1-Phi_i conj(Phi_j))/(w_i+conj(w_j))]_ij >= 0,
G-diag(V/2)Gdiag(V/2)^* >= 0,
4G-diag(V)Gdiag(V)^* >= 0.                              (87.1)
```

For one Cayley divisor factor the Pick defect is exactly a positive rank-one Gram plus a positive
diagonal congruence of `G`. Pick defects close under products, and entrywise matrix limits preserve
positive semidefiniteness, so the proof reaches the actual unconditional infinite Xi product.
Affine Schur closure `f |-> (1-f)/2` gives the two `V` inequalities.

This closes finite-aperture Hardy nonexpansiveness of the requested `V`. It does not close the
RH-bearing tangent step: `(87.1)` contains `diag(V)Gdiag(V)^*`, while the Ward consumer contains
the outer product `r_P r_P^*` of the aperture derivative at zero. Existing boundary-ramification
theorems already show that a nonzero four-unit relative-trace density must be square-root singular,
so differentiating the smooth finite-aperture contraction cannot produce that outer product.

Do not repeat pointwise phase bounds, finite products, smooth Schur contraction, or entrywise Pick
positivity as the missing step. Exact survivor is a source-defined singular/cofinal Julia boundary
lift with column `r_P` and boundary diagonal `4`, or a proof that no CCM-admissible lift can have
those data.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardHardyContraction.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardHardyNonexpansive.lean`;
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/xi-ward-hardy-nondiagonal-nonexpansiveness.md`.

## 88. Zero-adapted sampling classifies the four-unit Julia boundary lift

The exact augmented object requested after Section 87 is now defined:

```text
W_P=[[G_P,r_P],[r_P^*,4]],
S_P=4G_P-r_Pr_P^*.
```

A new zero-adapted mechanism removes the possible cancellation from the complete infinite Xi
divisor. Let `q` be any upper representative of a strict-right Schwarz pair, write
`lambda=xiRightCenteredZero(q)` and `a=Re(lambda)`, and sample at `w_q=conj(lambda)`. Every
Schwarz-pair response has positive real part on the right half-plane. The selected pair contributes

```text
Re(2/(w_q+lambda))=1/a
```

and its conjugate term is strictly positive. Absolute summability therefore gives

```text
Re r_P(w_q)>1/a,
|r_P(w_q)|^2>2/a=4G_P(w_q,w_q).                         (88.1)
```

The strict strip bound `0<a<1/2` is exactly what makes the four-unit threshold fail. Thus one
strict-right Xi pair produces a one-node negative diagonal of `S_P`; no tail cancellation or
finite truncation can repair it.

Lean proves the block Schur equivalence and the exact endpoint law

```text
RH
<->
for every finite right-half-plane packet P, S_P is PSD
<->
for every finite right-half-plane packet P, W_P is PSD. (88.2)
```

This is not RH: the forward construction arm of `(88.2)` remains open. It does close the exact
target classification and supplies a canonical falsifier for every possible strict-right zero.
Any source proof of the requested lift now has no remaining target-side analytic gap: positivity
of the displayed source-defined block is itself the RH-complete operation.

Do not return to generic Schur realization, diagonal multiplier contractivity, or cancellation
estimates for `r_P`. The live source-side problem is to derive positivity of `W_P` from the
singular/cofinal Möbius--Gamma source without inserting a target Gram factorization or assuming a
bounded/norm-holomorphic boundary map.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardCofinalBoundaryLift.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/xi-ward-zero-adapted-four-unit-boundary-charge-law.md`.

## 89. Cofinal factorial/Beta reflection has two negative directions

The remaining canonical “reflect the positive raw source, then attach one boundary channel”
candidate is now decisively excluded. On Borel orders `0,1,2,3`, let

```text
A_x(i,j)=m_(i+j+1)(x)/(i+j+1)!.
```

After scaling by `2^(x+1)`, first-prime dominance gives

```text
A_x(i,j) -> (log 2)^(i+j+2)/(i+j+1)!.
```

With `ell=log 2`, the explicit columns

```text
u=(-1/2, 1/ell, 0, 0),
v=(-1/120, 1/(10 ell), -1/(2 ell^2), 1/ell^3)
```

compress this limit exactly to

```text
ell^2 diag(-1/12,-1/100800).                            (89.1)
```

Hence the actual cofinal factorial/Beta-reflected source is negative definite on the fixed
complex plane `span_C{u,v}` for every sufficiently large displacement. Its negative index is at
least two. The complex Krein--Langer rank bound then yields the universal law

```text
for every b, A_x+b b* is not PSD eventually.            (89.2)
```

So one positive boundary channel, including any scalar four-unit channel after rescaling, cannot
repair this reflected source. This is stronger than the earlier `2 x 2` determinant fracture,
which exposed only one negative direction and did not settle rank-one repair.

Do not retry factorial/Beta reflection plus one boundary vector. The surviving CCM construction
must change the reflected source kernel itself or use a genuinely multi-channel non-diagonal
Julia completion before taking the singular cofinal boundary. This does not prove RH or kill all
CCM transports.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaBetaReflectionRankOneRepairNoGo.lean`;
- `docs/drafts/pipeline/3-formalized/von-mangoldt-gamma-beta-reflection-rank-one-repair-no-go.md`.

## 90. Half-order repair-rank law closes every fixed finite-channel Beta completion

The four-order plane in Section 89 is the first slice of an all-order flag law. For

```text
H_n(i,j)=1/(i+j+1)!,
```

let column `j` of `Q_n` be the last inverse column of the leading `(j+1) x (j+1)` block, extended
by zero. Lean proves `Q_n` invertible and the exact congruence

```text
Q_n^T H_n Q_n = diag(d_0,...,d_(n-1)),
d_j=(H_(j+1)^(-1))_(j,j),
j odd -> d_j<0.                                        (90.1)
```

Therefore the order-`2m` block has an explicit injective `m`-column negative frame. Negative
inertia is unbounded along the reciprocal-factorial tower.

The actual first-prime limit is

```text
L_n=(log 2)^2 D_n H_n D_n,  D_n(i,i)=(log 2)^i.
```

Undoing `D_n` and selecting the odd flag columns compresses `L_(2m)` to

```text
(log 2)^2 diag(d_1,d_3,...,d_(2m-1)) < 0.              (90.2)
```

Entrywise first-prime convergence transfers this fixed negative `m`-plane to the actual cofinal
von Mangoldt--Gamma factorial/Beta source. Krein--Langer then yields the quantitative law

```text
k < m
->
eventually, for every v_0,...,v_(k-1),
A_x + sum_(a<k) v_a v_a^* is not PSD on order 2m.       (90.3)
```

Thus repair rank must be at least half the Borel order. Every fixed finite number of positive
boundary channels fails cofinally. Do not retry factorial/Beta reflection with any fixed finite
multi-channel completion.

This still does not kill a singular completion whose internal channel rank grows without bound,
and it does not identify every imaginable CCM source transport with the canonical Beta reflection.
Exact surviving frontier is now the unbounded-rank singular lift: either prove every
CCM-admissible lift is cofinally finite-rank approximable (then `(90.3)` kills it), or derive a
direct contradiction for the genuinely infinite-rank lift. No weaker finite-order repair question
remains.

Formal sources:

- `formal/GaloisForLFunctions/HTGeometry/ReciprocalFactorialHankelInertia.lean`;
- `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaBetaReflectionFiniteRankRepairNoGo.lean`;
- `docs/drafts/pipeline/3-formalized/von-mangoldt-gamma-beta-reflection-half-order-rank-law.md`.

## 91. Doubled Möbius parity supplies the missing transverse four-unit source channel

The exact CCM endpoint remains

```text
W_P=[[G_P,r_P],[r_P^*,4]].
```

A new infinite source construction now separates the Hardy father space from the four-unit Fisher
detail.  For the damped signed likelihood `d_(sigma,u)`, its Möbius-parity transform
`p_(sigma,u)`, the Fisher tangent `chi_sigma`, and its parity transform `p chi_sigma`, define

```text
F_(sigma,u)=2^(-1/2)(d_(sigma,u),p_(sigma,u)),
D_sigma     =2^(-1/2)(chi_sigma,-p chi_sigma).
```

Lean proves unconditionally

```text
<F_(sigma,u),F_(sigma,v)>
  =squarefreeMobiusBoundaryLayerLaplace sigma (u+v),
<D_sigma,F_(sigma,u)>=0,
||D_sigma||^2=||chi_sigma||^2 -> 4.                    (91.1)
```

Thus every finite augmented source packet has an actual PSD Gram and converges entrywise to

```text
[[G_P,0],[0,4]].                                       (91.2)
```

This is real progress over the one-carrier likelihood: exponentials are total there, forcing the
soft Fisher column; the doubled clock-odd sector is an independent transverse channel with exactly
the required four-unit capacity.

Do not mistake `(91.2)` for source-side positivity of fixed `W_P`.  The sole live map is now the
singular squarefree-overlap graph division, Gamma completion, and strict-right anti-causal
projection acting on `D_sigma`.  It must turn the zero transverse column into `r_P` while
preserving cofinal Gram positivity.  Ordinary phase/Hardy contractivity cannot do this: existing
Lean proves strict phase contraction under false RH and unitary saturation exactly under RH.
Source-rigged nonexpansiveness on the doubled detail is the exact open core.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/MobiusParityLikelihoodHardyGram.lean`;
- `formal/GaloisForLFunctions/RHTower/MobiusDoubledParityHardyTransverseGram.lean`.

## 92. Fixed Ward graph is expansive in source norm

Do not reuse target Hardy multiplier contractivity as source-side nonexpansiveness.  The complete
fixed graph transport depends affinely on a source score, and at base aperture Lean proves

```text
V_(sigma,epsilon)(x)-V_(sigma,epsilon)(y)
 =i/(2 epsilon)
  [<x,psi_sigma>-<y,psi_sigma>].                       (92.1)
```

Because `||psi_sigma||=1`, the explicit pair `x=psi_sigma`, `y=0` on the physical critical ray
`epsilon=sigma-1` has gain

```text
1/[2(sigma-1)]>1,  1<sigma<3/2.                       (92.2)
```

Thus existing `squarefreeMobiusGammaXiWardTransportV` is not nonexpansive on ambient source
Hilbert space.  Its target phase remains contractive; no contradiction exists because graph
division and target multiplier act in different variables and norms.

Combined with §91, exact surviving task is a source-conditioned closed graph on doubled clock-odd
detail.  Its graph norm must absorb overlap division without changing asymptotic detail energy
four.  Merely weighting graph norm by `1/(sigma-1)` destroys four-unit normalization and cannot
prove `W_P`.  This is now the sole norm-compatible transport question; do not retry ambient
source contractivity.

Formal source:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardSourceNonexpansiveNoGo.lean`.

## 93. Cofinal saturation rigidity forces the Ward column into a connection term

The graph-norm escape left by §92 is now sharply classified. For every contraction between
arbitrary complex Hilbert spaces, Lean proves

\[
\|T^*Td-d\|^2\le \|d\|^2-\|Td\|^2,
\]

and therefore

\[
|\langle Tx,Td\rangle-\langle x,d\rangle|
\le \|x\|\sqrt{\|d\|^2-\|Td\|^2}.                     \tag{93.1}
\]

Exact saturation of one detail vector freezes every inner product against it. The cofinal theorem
does not assume finite dimension or finite rank:

\[
\begin{aligned}
\langle x_n,d_n\rangle&=0,\\
\sup_n\|x_n\|&<\infty,\\
\|d_n\|^2-\|T_nd_n\|^2&\to0
\end{aligned}
\quad\Longrightarrow\quad
\langle T_nx_n,T_nd_n\rangle\to0.                     \tag{93.2}
\]

The C41 source satisfies the first condition exactly, its father vectors at fixed aperture are
bounded, and both source and desired target detail diagonals tend to four. Hence no bounded
cofinal contraction can create \(r_P\) by directly transporting \(D_{\sigma_n}\). This closes the
infinite/cofinal bounded-operator version of §92, not merely finite-rank repairs.

A moving target detail can still have a connection term

\[
e_n=T_nd_n+c_n.
\]

But `(93.2)` then gives an exact conservation law:

\[
\langle T_nx_n,e_n\rangle\to r
\quad\Longrightarrow\quad
\langle T_nx_n,c_n\rangle\to r.                       \tag{93.3}
\]

Thus all of the nonzero continued Xi Ward column must come from differentiating the
Gamma/Wiener--Hopf operator itself. It cannot come from the transported four-unit Möbius detail.

Lean proves the complete classification of the now-retired proposal:

\[
\mathrm{RH}
\Longleftrightarrow
\text{cofinal four-unit contraction realization of \(r_P\) from the doubled Möbius source}.
\tag{93.4}
\]

Under RH the column vanishes and the identity contraction realizes it along
\(\sigma_n=1+1/(n+1)\). Conversely, cofinal saturation forces the column to vanish, and the
zero-adapted one-node theorem yields RH.

This is not an RH proof. It prevents another return to “put the division in a graph norm.” Exact
remaining construction is the covariant derivative

\[
c_\sigma=(\partial_\sigma T_\sigma)F_{\sigma,u}
\]

for the source-defined Gamma/true-Wiener--Hopf family, together with the unconditional estimate

\[
\|T_\sigma D_\sigma+c_\sigma\|^2\longrightarrow\le4
\]

and its packet codiagonal limit \(r_P\). The existing non-diagonal Julia derivative identifies the
required output column, but no corpus theorem supplies this connection-augmented four-unit norm.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/MobiusDoubledParityContractionSaturationRigidity.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-four-unit-cofinal-contraction-saturation-rigidity.md`.

## 94. Singular/cofinal connection escape is impossible at an adapted zero

Section 93 identified a moving-operator connection as the only term that
could carry the nonzero Ward codiagonal. That bookkeeping statement is
correct, but the proposed connection escape is now closed once the complete
target detail is tested.

For a strict-right Xi pair with centered zero `lambda`, put
`a=Re(lambda)>0` and sample at `w=conj(lambda)`. The adapted response obeys

\[
2/a<|r(w)|^2.
\]

In every complex Hilbert space, Cauchy--Schwarz now gives

\[
\|f\|^2\le\frac1{2a},\qquad \langle f,e\rangle=r(w)
\quad\Longrightarrow\quad
4<\|e\|^2.                                             \tag{94.1}
\]

If `e=Td+c`, the direct detail remains father-orthogonal, and the connection
carries `r(w)`, then the total `e` has the same codiagonal. Interference
between `Td` and `c` is irrelevant to `(94.1)`: no connection-augmented
four-unit lift exists at that node.

Lean also proves the singular/cofinal version. There are no sequences
`f_n,e_n` satisfying

\[
\|f_n\|^2\to\frac1{2a},\qquad
\langle f_n,e_n\rangle\to r(w),\qquad
\|e_n\|^2\le4\quad\text{for every }n.                  \tag{94.2}
\]

No boundedness of a transport or connection, finite-rank approximation,
vector convergence, or common decomposition is assumed. Only the three Gram
entries of the requested Julia lift occur.

This corrects the final paragraph of Section 93: differentiating the
Gamma/true-Wiener--Hopf operator is not a separate norm-compatible escape.
Any source theorem producing its claimed Hardy father limit, Ward
codiagonal, and four-unit total diagonal already excludes every strict-right
zero and therefore proves RH. The remaining task is exactly unconditional
source positivity of fixed `W_P`; it cannot be replaced by connection
bookkeeping.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardConnectionOverspend.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-cofinal-connection-escape-closure.md`.

## 95. Fixed Euler-edge scalar completeness removes packet geometry

The four-unit endpoint can now be tested on one fixed vertical line. Let
`lambda=a+ib` be any strict-right centered Xi zero, with `0<a<1/2`, and use

```text
w=1/2-ib.
```

The selected Schwarz-pair term has real part `2/(a+1/2)`. Every other
absolutely summable Schwarz-pair term has positive real part. Therefore

\[
\Re r(w)>\frac{2}{a+1/2}>2,\qquad |r(w)|^2>4.          \tag{95.1}
\]

At this node `G(w,w)=1`, so `(95.1)` is exactly a negative diagonal of
`4G-r r^*`. Lean proves both exact laws

```text
RH <-> for every t in R, |r(1/2+i t)|^2 <= 4,

RH <-> W_P is PSD for every finite packet P contained in Re(w)=1/2.
```

Thus the remaining CCM source theorem no longer needs positivity on all
right-half-plane packets, a cofinal packet exhaustion, or an interior-node
estimate. It must prove the scalar two-unit bound on the Euler edge directly
from the completed squarefree overlap graph. This is still RH-complete and
is not yet proved.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardEulerEdgeCompleteness.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/xi-ward-euler-edge-scalar-completeness-law.md`.

## 96. Synchronized recovery is all-support contractive and first-jet invisible

For

\[
f(t)=\frac{1-e^{-t}}t,\qquad f(0)=1,
\]

Lean proves the universal law

\[
f(a)f(b)\le f(a+b)\qquad(a,b\ge0).
\]

After exact Rees-factor cancellation, every finite squarefree support \(P\)
therefore has recovered/physical ratio

\[
R_P(x)=
\frac{\prod_{p\in P}c_x(p)f(x\log p)}
     {f(x\sum_{p\in P}\log p)}
\in(0,1],
\]

strictly below one for \(x>0\) and \(P\ne\varnothing\). The signed amplitude
\[
A_P(x)=(-1)^{|P|}\sqrt{R_P(x)}
\]
defines a contraction on the full infinite squarefree-support \(\ell^2\)
space. More sharply, local Gamma sewing has zero linear defect and the chord
jets cancel across every support:

\[
\frac{R_P(x)-1}{x}\to0,\qquad
\frac{A_P(x)-(-1)^{|P|}}x\to0.
\]

Consequently multiplying the genuine non-diagonal anti-causal Julia transport
by \(A_P(x)\) preserves its fixed Ward-column tangent:

\[
\frac{A_P(x)V_w(x)}x
\longrightarrow
(-1)^{|P|}r(w).
\]

At every positive aperture this recovered transport still obeys the scalar
two-unit bound and the full finite-packet Hardy Pick defect remains PSD.
These are unconditional all-support theorems, not singleton estimates.

Mechanism verdict: synchronized recovery solves signed source-holonomy
nonexpansiveness and exact Ward first-jet compatibility, but its first-jet
invisibility means it does **not** supply the missing order-\(x\) damping
needed to make \(V_w(x)/x\) contractive. Thus it does not by itself imply
fixed \(W_P\succeq0\). Exact live endpoint remains Section 95's
source-side Euler-edge bound \(|r(1/2+it)|\le2\).

Formal source:

- `formal/GaloisForLFunctions/RHTower/GammaSewnSynchronizedRecoveryContraction.lean`.
