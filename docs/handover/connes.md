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

## 13. A promising but unproved source identity

For \(x>0\), the corpus gives a positive likelihood factorization of the form

\[
k(x)=h(x)\left(1+\int e^{-B(x)t}\,d\mu(t)\right),
\qquad
B(x)=\pi e^{2x}-\tfrac32,
\]

with \(h\) the first atom and \(\mu\) positive. This is the most plausible bridge from modular seam
cancellation to an exact positive carrier.

What is known:

- the measure is positive;
- it gives exact higher-tail likelihood response;
- all tilted moment Hankel matrices in the \(B\)-coordinate are strictly positive;
- the first atom endpoint slope is positive;
- the completed source is smooth and even, forcing cancellation of the cusp hierarchy.

What is **not** known:

- a translation-positive-definite representation for \(M_a(t)\);
- a proof that the likelihood measure is PF-infinity or variation diminishing in the required
  coordinate;
- a sign theorem for the beyond-all-orders residual;
- the phase-current domination inequality.

This identity should be developed, but only through exact transformations. Do not infer the
Hedenmalm sign merely from positivity of \(\mu\).

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

The Connes/Hedenmalm work from this stopping point modified:

- `docs/drafts/pipeline/1-in-progress/hedenmalm-center-mixed-double-positivity-law.md`
  - added the two-ended causal-resolvent theorem;
  - added the modular-seam/first-atom theorem.

This handover adds:

- `docs/handover/connes.md`.

No Lean file for either new theorem had been created at the stopping point. Check the live tree
again because another agent may have added one after this handover was written.

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

Work stopped immediately after deriving and recording the modular-seam dominance theorem. The
next concrete task is **not** to search for another criterion and **not** to add another finite
Hankel estimate. It is:

> Formalize the first-atom wrong-sign and higher-tail compensation theorem in
> `HedenmalmFirstAtomSeamDominance.lean`, then derive the exact all-order seam moment hierarchy and
> use it to seek a positive representation of the nonperturbative residual or to prove the
> phase-current domination inequality.

No compiler process was left running by the handover task, and no build was run for this document.
