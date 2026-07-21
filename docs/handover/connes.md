# Connes / Hedenmalm RH route — complete research handover

**Last updated:** 2026-07-21  
**Repository:** `/Users/Spare/Documents/code/riemann/publications/hgt`  
**Active research card:**
`docs/drafts/pipeline/1-in-progress/hedenmalm-center-mixed-double-positivity-law.md`

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

`docs/drafts/pipeline/1-in-progress/xi-completed-density-antipodal-crossing-barrier.md`,

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
Actual frontier is therefore collision-only: allow norm-gap/unit-circle crossings at other phases,
but exclude projective ratio $E^\#/E=-1$.  Active conjecture is negative-ray no-return for this
ratio, with first nonzero projective jets handling simultaneous zeros.  It is strictly weaker than
refuted global Hermite--Biehler orientation.

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
