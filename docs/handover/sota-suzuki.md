# Suzuki screw-function RH route — complete research handover

**Last updated:** 2026-07-21  
**Repository:** `/Users/Spare/Documents/code/riemann/publications/hgt`  
**Resolved repository path:** `/Volumes/Intenso/code/hgt`  
**Persistent goal:** active; do **not** mark complete or blocked  
**Primary formal area:** `formal/GaloisForLFunctions/RHTower`  
**Primary literature source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
[arXiv:2606.09096](https://arxiv.org/abs/2606.09096)

## 1. Executive status

The Riemann hypothesis has **not** been proved in this route.

This work has nevertheless moved the Suzuki route to a materially sharper frontier.  The
finite-aperture real-zero family has been converted into a normalized Hermite--Biehler/Livšic
carrier, and both extreme ends of Suzuki's admissible shift parameter have now been classified:

```text
far below the restricted-Weil floor
  -> the resolvent forgets the arithmetic operator
  -> an explicit free carrier
  -> zero locally uniformly as the aperture grows;

too close to a simple parity ground state
  -> one parity resolvent pole dominates
  -> Schwarz equality
  -> the universal plus/minus Cayley carrier.
```

Both ends preserve finite-aperture real-zero structure while erasing the arithmetic data needed
to recover Xi.  The strongest positive statement exposed by the second no-go is the exact
dimensionless leakage parameter

\[
  \rho_a(\tau)
   =\frac{\tau\,\|\sinh\|^2}
          {\Delta_a\,|\langle\phi_{0,a},\cosh\rangle|^2}.
\]

For a simple even ground pole, if `rho_a(tau)` tends to zero along a locally uniformly convergent
carrier sequence, the limit is forced to be

\[
  \frac{z-i}{z+i}.
\]

The contrapositive is formalized: a non-Cayley limit forces the leakage **not** to tend to zero.
This is an unconditional and useful scale-selection law.  It is not sufficient for an
arithmetic limit, and it is not an RH proof.

The exact remaining scientific wall is now:

> Construct a source-derived cofinal intermediate shift schedule which avoids the far-negative
> free boundary and retains nonvanishing excited-state leakage, prove locally uniform convergence
> of its concrete Suzuki Livšic carriers, and identify the resulting non-universal meromorphic
> carrier with the global Xi/de Branges object without assuming RH.

The concrete Suzuki screw Hilbert space, Friedrichs operator, spectral projections, resolvents,
deficiency vectors, and characteristic functions are not yet represented end-to-end in Lean.
The new Lean theorems formalize the complete analytic implication once their exact source-side
data are supplied.

## 2. Mandatory restart procedure

A fresh agent should do the following in order.  Do not begin by re-searching or re-proving the
results summarized below.

1. Read `AGENTS.md` and `docs/meta/scientific-method.md` completely, line by line.
2. Read `/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md` completely and use that
   research posture.  Do not use `lean-consolidate` for this task.
3. Read `formal/README.md`, `formal/AGENTS.md` if present, and `formal/LEAN_OVERVIEW.md`.
4. Read these four Suzuki cards completely:

   ```text
   docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
     suzuki-finite-aperture-hermite-biehler-normal-family.md
   docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/
     suzuki-negative-shift-defect-escape.md
   docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
     suzuki-projective-defect-free-boundary.md
   docs/drafts/pipeline/3-formalized/needs-audit/
     suzuki-ground-edge-cayley-universality.md
   ```

5. Read the Suzuki row and checklist in
   `docs/drafts/pipeline/1-in-progress/rh-sota-literature-lean-wall-2026.md`.
6. Read these Lean modules in dependency order:

   ```text
   formal/GaloisForLFunctions/RHTower/SuzukiFiniteApertureHermiteBiehler.lean
   formal/GaloisForLFunctions/RHTower/SuzukiProjectiveDefectBoundary.lean
   formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeCayleyUniversality.lean
   formal/GaloisForLFunctions/RHTower/RiemannHypothesisSOTA2026.lean
   ```

7. Search the live corpus before adding any source construction or reusable lemma:

   ```sh
   scripts/formal_tools.py research "Suzuki screw resolvent"
   scripts/formal_tools.py research "Friedrichs restricted Weil parity"
   scripts/formal_tools.py research "Livsic defect angle ground gap"
   scripts/formal_tools.py research "locally uniform Xi de Branges"
   ```

8. Inspect `git status --short`.  This is a shared, dirty worktree.  Preserve every unrelated
   change and re-check ownership rather than trusting the snapshot in this handover blindly.

The user's rules override any generic workflow suggestion to do numerical pre-certification:
there must be **no computations or numerical evidence** in this task.  All mathematics and Lean
proofs must be unconditional.  Do not add `sorry`, `admit`, axioms, opaque escape hatches, unsafe
declarations, or conditional RH premises disguised as interfaces.

Work independently; do not spawn subagents.  Use one owned foreground Lean process at a time.
Batch meaningful edits before checking them.

Before every Lean command, separately run:

```sh
ps -axo pid=,ppid=,etime=,command= | rg '([/]lean|lake (env lean|build))' || true
```

Do not chain the process check and the Lean command.  If another Lean process appears, wait.  Do
not kill or interfere with another agent's process.

Development verification must use:

```sh
cd formal
lake env lean GaloisForLFunctions/RHTower/<File>.lean
```

Use only one exact module build as the final audit:

```sh
cd formal
lake build GaloisForLFunctions.RHTower.<Module>
```

Do not run a full or broad umbrella build.

## 3. Source literature and the exact 2026 frontier

### 3.1 What Suzuki proves

Suzuki's June 2026 paper constructs the following finite-aperture source machinery
unconditionally:

- a lower-semibounded restricted Weil quadratic form on an interval;
- its Friedrichs self-adjoint realization `A_a`;
- a discrete spectrum with lowest eigenvalue `lambda_a`;
- parity invariance under `Jf(x)=f(-x)`;
- continuity information for the lowest eigenvalue;
- for sufficiently small aperture, a simple ground state which is positive almost everywhere
  and therefore even;
- for every admissible shift `lambda < lambda_a`, two deficiency vectors sourced by `e^x` and
  `e^{-x}`;
- a deficiency-`(1,1)` derivative operator and a full circle of self-adjoint extensions;
- entire extension characteristic functions `W(a,theta;z)` having only real zeros for every
  extension angle.

Suzuki does **not** prove a cofinal choice of shifts, a nondegenerate cofinal carrier limit, or an
identification of a carrier limit with Xi sufficient to prove RH.  Control of the shift is part of
the actual open problem.

### 3.2 Correction of the originally displayed limit wall

Suzuki's displayed target is proportional to

\[
  z^2\frac{\Xi_C(z)}{\Xi_C'(z)}.
\]

It has unconditional real poles.  Therefore it cannot be the ordinary locally uniform limit on
all of `C` of entire functions.  The old proposition `SuzukiXiCharacteristicLimitWall` is retained
in `RiemannHypothesisSOTA2026.lean` only as a legacy impossible-premise zero-transfer connector.
Do not revive it as the live route.

The pole-compatible replacement is the normalized finite-aperture Livšic quotient, or
equivalently a quotient of two distinct extension characteristic functions.  A common entire
gauge cancels from the two-angle quotient exactly.

### 3.3 Literature checked for the new theorem

The following sources were checked through 2026-07-21:

- [Suzuki, arXiv:2606.09096](https://arxiv.org/abs/2606.09096), the primary source;
- [Aleman--Martin--Ross, *On a theorem of Livsic*, arXiv:1209.4497](https://arxiv.org/abs/1209.4497),
  for the general characteristic-function framework;
- [Livšic characteristic-function survey, arXiv:2104.12694](https://arxiv.org/abs/2104.12694),
  for the classical operator-theoretic background;
- [Schwarz equality literature, arXiv:2109.07870](https://arxiv.org/abs/2109.07870), for the
  classical rigidity mechanism.

Targeted searches found no Suzuki follow-up or citing mathematical paper stating the exact
ground-pole leakage bound, the Cayley-universality limit, or the two-universal-boundary
classification.  That is evidence only.  The new theorem remains
`[EXTERNAL NOVELTY UNVERIFIED]`; no priority claim has been certified by a specialist.

## 4. Work completed before the latest tranche

The new ground-edge result depends on three earlier pieces of Suzuki-route work.  They should be
reused, not repackaged.

### 4.1 Finite-aperture Hermite--Biehler/Livšic carrier

`SuzukiFiniteApertureHermiteBiehler.lean` extracts the full-angle consequence of Suzuki's
real-zero theorem.  Abstractly, if `A(i)=0` and every `A+uE`, `|u|=1`, has no nonreal zero, then

\[
  |A(z)|<|E(z)|\qquad (\Im z>0).
\]

Hence

\[
  \Theta(z)=A(z)/E(z)
\]

is holomorphic and Schur on the upper half-plane, with the common anchor `Theta(i)=0`.  Its Cayley
transform is Herglotz and normalized by `m(i)=i`.  Schwarz gives the aperture- and shift-independent
bound

\[
  |\Theta(z)|\le\left|\frac{z-i}{z+i}\right|.
\]

This gives local Montel subsequences without RH.  It supplies compactness, not arithmetic
identification or uniqueness.

Principal declarations include:

```text
norm_lt_of_suzukiAllAngleRealZeros
suzukiLivsic_denominator_ne_zero
norm_suzukiLivsicQuotient_lt_one
suzukiLivsicQuotient_I_eq_zero
suzukiHerglotz_I_eq_I
suzukiHerglotz_im_nonneg
suzukiHermiteBiehler_of_allAngleRealZeros
differentiableOn_suzukiLivsicQuotient_upperHalfPlane
norm_suzukiLivsicQuotient_le_lineCayley
exists_suzukiLivsic_montel_subseq
suzuki_twoAngle_quotient_eq_mobius
suzuki_twoAngle_reconstruct_livsic
suzuki_twoAngle_common_gauge_cancels
```

### 4.2 Far-negative shift no-go

At fixed aperture, write an admissible shift as `lambda=-r` with `r` large.  The classical
resolvent law

\[
  r(A_a+rI)^{-1}f\longrightarrow f
\]

makes the common scale cancel from the projective Livšic quotient.  The carrier approaches the
explicit free-interval carrier

\[
  \Theta_a^{\mathrm{free}}(z)
  =\frac{e^{-2a}-e^{2iaz}}
         {1-e^{-2a}e^{2iaz}}.
\]

For every upper strip `Im z >= eta > 0`, this converges uniformly to zero as `a -> infinity`, and
hence locally uniformly on the upper half-plane.  Therefore arbitrary admissible shifts cannot
all be noncollapsing or have a common arithmetic limit.

The complete concrete resolvent escape theorem is paper-proved in
`suzuki-negative-shift-defect-escape.md`.  Its dependency-closed analytic/projective survivor is
formalized in `SuzukiProjectiveDefectBoundary.lean`.

### 4.3 Projective Gram and parity survivor

For a deficiency pair with common norm `N` and cross term `C`, the normalized two-state defect
Gram matrix has even and odd weights

\[
  p_{\mathrm{even}}=\frac{N+C}{2N},\qquad
  p_{\mathrm{odd}}=\frac{N-C}{2N},
\]

and polarization

\[
  p_{\mathrm{even}}-p_{\mathrm{odd}}=C/N.
\]

Common source scale cancels.  Exact parity also selects the extension phases: `u=1` is the odd
member and `u=-1` is the even member, subject to the recorded nondegeneracy conditions.

The natural unconditional chart is the ground-centered family

\[
  \lambda_a^{(\tau)}=\lambda_a-\tau,\qquad \tau>0,
\]

whose shifted operator has exact bottom `tau`.  This chart avoids pretending that the RH-bearing
unshifted value `lambda=0` is known to be admissible.

Principal declarations in `SuzukiProjectiveDefectBoundary.lean` include:

```text
suzukiLivsicQuotient_common_scale
suzukiCharacteristicPencil_common_scale
suzukiFourier_parityPair
suzukiCharacteristicPencil_neg_of_parity
suzuki_odd_phase_eq_one
suzuki_even_phase_eq_neg_one
suzukiNormalizedDefectGram_common_scale
suzukiDefectGram_weight_and_polarization
suzukiDefectGram_weights_mem_unitInterval
norm_suzukiFreeLivsic_le
suzukiFreeLivsic_tendstoUniformlyOn_upperStrip
suzukiFreeLivsic_tendstoLocallyUniformlyOn
suzukiGroundCenteredShift_lt
suzukiGroundCenteredShift_gap
```

## 5. Latest result: ground-edge Cayley universality

This is the point where the work stopped.  The paper proof and its analytic Lean core are complete.

### 5.1 Exact fixed-aperture setup

Fix aperture `a>0`.  Let `lambda_a` be the lowest eigenvalue of Suzuki's `A_a`, and put

\[
  B_a=A_a-\lambda_a I\ge0,\qquad
  R_\tau=(B_a+\tau I)^{-1},\qquad \tau>0.
\]

Use the reflected sources

\[
  f_+(x)=e^x,\qquad f_-(x)=e^{-x},
\]

and their parity components

\[
  f_e=\cosh x,\qquad f_o=\sinh x.
\]

Because `R_tau` commutes with parity, define

\[
  E_e(\tau)=\langle f_e,R_\tau f_e\rangle,
  \qquad
  E_o(\tau)=\langle f_o,R_\tau f_o\rangle.
\]

The reflected deficiency-pair Gram entries are

\[
  N_\tau=E_e(\tau)+E_o(\tau),\qquad
  C_\tau=E_e(\tau)-E_o(\tau).
\]

The projective defect angle is therefore

\[
  \kappa_\tau
   =\frac{C_\tau}{N_\tau}
   =\frac{E_e(\tau)-E_o(\tau)}
          {E_e(\tau)+E_o(\tau)}.
\]

### 5.2 Ground-pole estimate

Assume the ground eigenvalue is simple and even, with normalized eigenvector `phi_0`.  Define

\[
  \alpha=|\langle\phi_0,\cosh\rangle|^2>0,
  \qquad
  \beta=\|\sinh\|^2,
\]

and suppose the odd subspace has spectral gap `Delta>0` above the shifted ground.  The ground
spectral projection gives

\[
  E_e(\tau)\ge\frac{\alpha}{\tau}.
\]

On the odd subspace,

\[
  0\le E_o(\tau)\le\frac{\beta}{\Delta+\tau}
  \le\frac{\beta}{\Delta}.
\]

Consequently

\[
  0\le1-\kappa_\tau
   =\frac{2E_o(\tau)}{E_e(\tau)+E_o(\tau)}
   \le\frac{2\tau\beta}{\Delta\alpha}
   =2\rho_a(\tau).
\]

This estimate retains all aperture-dependent quantities.  It does not hide a collapsing parity
gap or a vanishing source overlap.

For Suzuki's sufficiently small apertures, the source theorem gives a simple positive even ground
state.  Since `cosh x>0`, its overlap with `cosh` is nonzero, and discrete spectrum supplies a
positive odd gap.  The fixed-small-aperture ground-edge result is therefore unconditional at the
paper level.  This does **not** give a cofinal `a -> infinity` estimate.

### 5.3 Exact Fourier endpoint derivative

Let

\[
  v_\tau=R_\tau f_+,
  \qquad
  F_\tau(z)=\int_{-a}^{a}v_\tau(x)e^{izx}\,dx,
\]

and define the anchored Suzuki carrier

\[
  \Theta_\tau(z)
  =\frac{(z-i)F_\tau(z)}{(z+i)F_\tau(-z)}.
\]

The endpoint values are

\[
  F_\tau(i)=C_\tau,
  \qquad
  F_\tau(-i)=N_\tau.
\]

Direct differentiation gives

\[
  2i\,\Theta_\tau'(i)=\frac{F_\tau(i)}{F_\tau(-i)}
  =\kappa_\tau.
\]

After conjugating the upper half-plane to the disk by

\[
  z(w)=i\frac{1+w}{1-w},
  \qquad
  h_\tau(w)=\Theta_\tau(z(w)),
\]

one has

\[
  h_\tau(0)=0,\qquad h_\tau'(0)=\kappa_\tau.
\]

### 5.4 Locally uniform Cayley limit

Suppose the aperture and spectral data may all vary along a nontrivial filter.  If the carriers
converge locally uniformly to a Schur function `Theta`, retain the anchor at `i`, and satisfy

\[
  \rho_{a_j}(\tau_j)\longrightarrow0,
\]

then `kappa_j -> 1`.  The Mathlib locally-uniform Weierstrass theorem transfers convergence to the
disk derivatives.  The limit disk map therefore fixes zero and has derivative one.  The equality
case of Schwarz's lemma forces it to be the identity, so

\[
  \Theta(z)=\frac{z-i}{z+i}
  \qquad (\Im z>0).
\]

The paper proof also gives the odd-ground analog: a simple odd ground with nonzero `sinh` overlap
forces the negative Cayley map.  That odd case is **not yet formalized in Lean**.

### 5.5 No-go and positive survivor

The attractive strategy “move the shift as close as possible to the restricted-Weil floor so the
carrier cannot collapse” fails.  The carrier survives, but a simple parity ground pole forces a
degree-one universal model and erases the excited arithmetic spectrum.

The exact positive survivor is:

> Under the stated energy and derivative laws, if a locally uniform limit is not the Cayley map,
> then `rho_a(tau)` does not tend to zero.

Lean formalizes this exact negation of convergence.  It does **not** formalize the stronger claim
`liminf rho > 0`; do not silently upgrade it.

## 6. Lean realization of the latest theorem

The new module is:

```text
formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeCayleyUniversality.lean
```

It imports:

```text
GaloisForLFunctions.RHTower.SuzukiProjectiveDefectBoundary
Mathlib.Analysis.Complex.LocallyUniformLimit
```

The declarations and their exact roles are:

- `upperHalfPlane_cayley_rigidity`: an upper-half-plane Schur function anchored at `i` whose
  disk-conjugate derivative is `1` is the line Cayley map on the upper half-plane.
- `suzukiDefectAngle`: `(evenEnergy - oddEnergy)/(evenEnergy + oddEnergy)`.
- `suzukiGroundLeakage`: `tau * oddBudget/(gap * groundMass)`.
- `deriv_suzukiFourierLivsic_disk_zero`: for the reflected Fourier Livšic quotient, the derivative
  at the disk origin is exactly `F(i)/F(-i)`.
- `deriv_suzukiFourierLivsic_disk_zero_eq_defectAngle`: substitutes the parity endpoint identities
  and identifies the derivative with the real defect angle.
- `suzukiDefectAngle_ground_leakage_bound`: proves
  `0 <= 1-kappa <= 2*rho` from positivity, the ground lower bound, and the odd upper bound.
- `suzukiDefectAngle_tendsto_one`: proves the varying-parameter filter limit `kappa -> 1`.
- `suzukiGroundEdge_cayley_limit`: transfers locally uniform convergence to derivatives and applies
  Schwarz equality.
- `suzukiGroundEdge_cayley_universality`: combines the energy law, derivative law, and locally
  uniform limit into the Cayley capstone.
- `suzukiGroundEdge_nonCayley_forces_leakage_not_tendsto_zero`: the positive contrapositive
  scale-selection theorem.

The capstone deliberately allows the aperture, shift distance, ground mass, parity gap, odd
budget, even energy, and odd energy to vary along an arbitrary nontrivial filter.  This is the
correct theorem shape for a cofinal Suzuki schedule.

The module does not postulate the restricted-Weil operator.  Its hypotheses are the exact
dependency-closed analytic surfaces needed from that operator.  This makes the theorem
unconditional, but the source instantiation remains future work.

## 7. Exact verification state

The following checks were completed on 2026-07-21:

1. Mathlib names and the proof shape were checked in `/tmp/SuzukiGroundEdgeScratch.lean`.
2. The exact source check passed cleanly with exit code zero:

   ```sh
   cd formal
   lake env lean GaloisForLFunctions/RHTower/SuzukiGroundEdgeCayleyUniversality.lean
   ```

3. `scripts/formal_tools.py index` succeeded and regenerated:

   ```text
   formal/LEAN_API.md
   formal/LEAN_GAPS.md
   formal/LEAN_OVERVIEW.md
   ```

4. `scripts/formal_tools.py lint --check-generated` passed.  Only repository-wide large-file
   warnings remained.
5. The final exact SOTA audit command was:

   ```sh
   cd formal
   lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026
   ```

   It compiled the new leaf and the SOTA module.  The desktop command wrapper detached while
   replaying a very large warning stream and did not preserve a final numeric exit code, but both
   fresh compiled objects were produced and no Lean process remained:

   ```text
   SuzukiGroundEdgeCayleyUniversality.olean  2026-07-21 11:44:58
   RiemannHypothesisSOTA2026.olean            2026-07-21 11:45:37
   ```

   Do not rerun a broad build for reassurance.  If a future session requires a strictly captured
   final exit code after making new relevant changes, run one cached exact-module audit only.
6. `/tmp/SuzukiGroundEdgeAxioms.lean` imports the new module and audits the seven capstone
   declarations.  `lake env lean /tmp/SuzukiGroundEdgeAxioms.lean` exited successfully on
   2026-07-21.  The app capture emitted no diagnostic lines.  If an explicit textual axiom list is
   needed for publication bookkeeping, rerun this one scratch audit when the Lean process slot is
   free; the expected Mathlib-only footprint is `propext`, `Classical.choice`, and `Quot.sound`.

No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in the new module.

One process-discipline mistake occurred during development: the first leaf check was started when
another agent's Lean process was present because the process check and Lean command had been
chained.  The owned process was terminated immediately.  All later checks were serialized.  This
is why the restart instructions require a separate process check.

## 8. Files changed by the Suzuki work

These are the Suzuki-lane files created or intentionally changed in this research chain:

```text
docs/drafts/pipeline/1-in-progress/rh-sota-literature-lean-wall-2026.md
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/
  suzuki-negative-shift-defect-escape.md
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  suzuki-finite-aperture-hermite-biehler-normal-family.md
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  suzuki-projective-defect-free-boundary.md
docs/drafts/pipeline/3-formalized/needs-audit/
  suzuki-ground-edge-cayley-universality.md
docs/handover/sota-suzuki.md
formal/GaloisForLFunctions/RHTower.lean
formal/GaloisForLFunctions/RHTower/RiemannHypothesisSOTA2026.lean
formal/GaloisForLFunctions/RHTower/SuzukiFiniteApertureHermiteBiehler.lean
formal/GaloisForLFunctions/RHTower/SuzukiProjectiveDefectBoundary.lean
formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeCayleyUniversality.lean
formal/LEAN_API.md
formal/LEAN_OVERVIEW.md
```

The generated API/overview files are shared artifacts.  Regenerate them with the official script;
do not hand-edit them.

At the stopping point, these visible worktree changes belong to other research lanes and must not
be edited, reverted, staged, cleaned, or built through without renewed scope:

```text
docs/drafts/pipeline/1-in-progress/hedenmalm-center-mixed-double-positivity-law.md
docs/drafts/pipeline/1-in-progress/simple-pole-jet-lattice-holographic-selection-law.md
formal/GaloisForLFunctions/HTGeometry.lean
formal/GaloisForLFunctions/HTGeometry/GammaPoleCovariantJetRealization.lean
formal/GaloisForLFunctions/HTGeometry/MeromorphicSimplePoleDifferentialOperator.lean
formal/GaloisForLFunctions/HTGeometry/GammaPoleBinomialSubprincipalDescent.lean
formal/GaloisForLFunctions/HTGeometry/GammaPolePrincipalRemainderFreeness.lean
formal/GaloisForLFunctions/HTGeometry/SimplePoleWeightedFirstSubprincipal.lean
docs/handover/connect-theorems.md
docs/handover/connes.md
docs/handover/htzeta.md
docs/handover/rhultra.md
```

Always refresh `git status --short`; concurrent ownership may have changed after this snapshot.

## 9. What the route is now working toward

The route is no longer searching for generic normality, generic real-zero extension families, or
an arbitrary shift.  Those questions are settled sharply enough to expose the real source wall.

The desired cofinal diagram is:

```text
concrete restricted-Weil forms A_a
  -> ground-centered resolvents (A_a-lambda_a I+tau_a I)^(-1)
  -> source Fourier pair from exp(+x), exp(-x)
  -> anchored meromorphic Livsic carriers Theta_(a,tau_a)
  -> exclude free-boundary collapse
  -> retain excited-state parity leakage
  -> prove locally uniform convergence and uniqueness
  -> identify the limit, including its divisor, with the Xi/de Branges carrier
  -> only then use real boundary spectra to infer a statement relevant to RH.
```

There are two distinct kinds of next work.  Keep them separate.

### 9.1 Mechanical/source formalization work

Audit the corpus again before starting; some operator or form pieces may have appeared in another
lane.  If absent, construct the actual source objects rather than another abstract wrapper:

1. the screw-function Hilbert space on the finite interval;
2. Suzuki's restricted Weil sesquilinear/quadratic form;
3. closability, lower semiboundedness, and the Friedrichs extension `A_a`;
4. parity commutation;
5. compact resolvent or the exact discrete-spectral interface used by Suzuki;
6. the lowest spectral value and its projection;
7. the shifted inverse `(A_a-lambda_a I+tau I)^{-1}`;
8. concrete sources `e^x`, `e^{-x}`, `cosh`, and `sinh` in the correct Hilbert space;
9. the deficiency vectors and their Fourier transforms;
10. the endpoint identities `F(i)=C` and `F(-i)=N`;
11. the complete all-angle `W(a,theta;z)` theorem surface, only to the extent it follows
    unconditionally from Suzuki's source theorem.

The immediate connector target is not a new criterion.  It is an instantiation of the existing
variables

```text
evenEnergy
oddEnergy
groundMass
gap
oddBudget
hderivAngle
```

in `suzukiGroundEdge_cayley_universality` with actual Suzuki objects.

Do not claim the source operator has been formalized merely by introducing a structure carrying
the desired properties.  A conditional interface is useful only when it is explicitly labelled
as an interface and connected to concrete, proved construction layers.

### 9.2 Actual mathematical research work

The next genuinely source-specific research target is a cofinal intermediate-window theorem.  For
a schedule `(a_j,tau_j)`, study

\[
  \alpha_a=|\langle\phi_{0,a},\cosh\rangle|^2,
  \qquad
  \Delta_a=\text{first odd spectral gap},
  \qquad
  \beta_a=\|\sinh\|^2,
\]

and prove at least that

\[
  \rho_{a_j}(\tau_j)
  =\frac{\tau_j\beta_{a_j}}
         {\Delta_{a_j}\alpha_{a_j}}
\]

does not tend to zero, while the same schedule avoids the far-negative free boundary.  A stronger
usable bound such as `liminf rho > 0` would be valuable, but it is not currently proved.

Merely choosing `tau_a` algebraically so that `rho_a` is nonzero is not enough.  A successful
theorem must be source-derived and must control the actual excited spectral contribution.  It must
then prove compact convergence and identify a non-universal limit.  Nonvanishing leakage is only a
necessary condition.

The highest-value estimates to seek are:

- aperture-uniform or asymptotically sharp lower bounds for the ground overlap `alpha_a`;
- upper/lower control of the parity gap `Delta_a`;
- exact aperture growth of `beta_a=||sinh||^2` in the correct source norm;
- a shift rule `tau_a` forced by the operator or characteristic data, not inserted to make a ratio
  convenient;
- a lower bound for excited-state spectral weight after projective normalization;
- a compact-open convergence theorem for the actual Fourier/resolvent quotient;
- divisor-preserving identification with a global Xi/de Branges characteristic object.

The fixed-small-aperture simple-even theorem and the cofinal `a -> infinity` problem must not be
conflated.  Simplicity, parity gap, and overlap may degenerate with aperture and require new proof.

## 10. Live escape routes and hostile tests

Every proposed advance should be attacked by the following tests before it enters Lean.

### 10.1 Mixed or multiple ground space

The Cayley no-go assumes a simple parity ground pole.  If the ground eigenspace becomes multiple
and carries both parity channels, its limiting derivative can lie strictly inside the disk, so
Schwarz equality does not force plus/minus Cayley.  This is a genuinely live possible escape.

Do not assume multiplicity merely to evade the theorem.  Derive it, or derive an asymptotic
near-degeneracy, from the concrete restricted-Weil source.  Determine the ground projection's
two-channel Gram state and whether it retains infinitely rich arithmetic data rather than only a
finite Blaschke factor.

### 10.2 Higher anchored jets

The first defect angle is a sufficient noncollapse certificate when bounded away from zero, but it
is not complete.  A nonzero Schur limit can have derivative zero at the anchor and a higher-order
zero there.  For full noncollapse, survival of some fixed anchored derivative order is necessary
and sufficient.

If the first-jet window closes, inspect higher projective resolvent moments.  Any proposed higher
jet should be tied to concrete parity-resolved spectral data and not added as a bare analytic
criterion.

### 10.3 Local uniformity

Pointwise convergence is insufficient for derivative passage and zero/divisor transport.  The
finite-aperture Schur bound gives normality and subsequences, but uniqueness and source
identification remain separate theorems.  Always state the topology exactly.

### 10.4 Gauge and divisor transport

Common nonvanishing entire gauges disappear from the Livšic or two-angle quotient.  This is useful,
but it also means a quotient can lose information.  Any claimed Xi identification must prove the
correct meromorphic divisor and normalization, not just local shape near the anchor.

### 10.5 RH circularity

The ground-centered shift `lambda_a-tau` is admissible for every `tau>0` without knowing the sign
of `lambda_a`.  The unshifted value `lambda=0` is RH-bearing and cannot be inserted unless its
admissibility is proved unconditionally.  Never assume positivity of the full restricted Weil
operator under another name.

### 10.6 Universal finite-degree collapse

Avoid treating a nonzero degree-one or finite Blaschke limit as arithmetic success.  The Cayley
classification shows that survival alone is too weak.  The target must retain the infinite Xi
divisor or an equivalent infinite spectral invariant.

## 11. Dead ends that must not be retried

The following formulations have already failed or been superseded:

- **All admissible shifts have a common nonzero limit.** False: sufficiently negative shifts hit
  the free boundary and collapse to zero cofinally.
- **Choose the shift arbitrarily close to the floor.** False as an arithmetic strategy under a
  simple parity ground pole: the limit is universal plus/minus Cayley.
- **Ordinary entire compact convergence to `z^2 Xi/Xi'`.** Impossible because the target has
  unconditional real poles.
- **A fixed finite-aperture real-zero characteristic function proves RH.** It does not transport
  the Xi divisor.
- **Montel compactness is the missing theorem.** It is already supplied by the uniform Schur
  bound; identification and nondegeneration are the wall.
- **The first anchored derivative alone is a complete noncollapse invariant.** False; higher-order
  anchored zeros exist.
- **A nonzero leakage ratio is sufficient for Xi.** False; it only avoids one universal boundary.
- **A generic abstract operator carrying all desired Suzuki properties is source formalization.**
  False; it merely restates premises.
- **The small-aperture simple positive ground theorem controls the cofinal aperture limit.** Not
  without uniform source estimates.
- **A criterion equivalent to RH is progress on the missing producer.** Not unless a new
  unconditional source theorem discharges a substantive part of it.

Each new no-go must still follow the project rule: extract its strongest nontrivial positive
survivor, prove it on paper, and formalize that exact dependency-closed theorem when possible.

## 12. Recommended next attack

The best next research move is a parity-resolved spectral-measure analysis of the concrete
ground-centered resolvent.

1. Write the even and odd source spectral measures

   \[
     d\mu_{e,a}(t)=d\langle f_e,P_{B_a}(t)f_e\rangle,
     \qquad
     d\mu_{o,a}(t)=d\langle f_o,P_{B_a}(t)f_o\rangle.
   \]

2. Express

   \[
     E_e(a,\tau)=\int\frac{d\mu_{e,a}(t)}{t+\tau},
     \qquad
     E_o(a,\tau)=\int\frac{d\mu_{o,a}(t)}{t+\tau}.
   \]

3. Separate the ground atom from the even excited spectrum and compare it with the first odd
   mass.  Search for an aperture-dependent balance point where neither the ground atom nor the
   free resolvent dominates projectively.
4. Derive a source-selected `tau_a` from an intrinsic balance equation or normalized Gram target,
   not from an arbitrary desire to keep `rho` constant.
5. Prove that the resulting spectral measures do not collapse to a one-atom or free measure and
   that at least one fixed anchored jet survives.
6. Only after the paper proof is dependency-closed, formalize the spectral-measure balance law and
   connect it to `suzukiGroundEdge_nonCayley_forces_leakage_not_tendsto_zero`.
7. Then attack locally uniform uniqueness and global divisor identification.

This attack is valuable even if it fails.  A failure may classify all ground-centered limits as
finite Blaschke models; the required positive survivor would then be the exact spectral measure or
moment condition needed to escape that classification.

## 13. Concrete first-session task list

A fresh agent can resume efficiently with this bounded sequence:

1. Perform the mandatory reads and live corpus searches from Section 2.
2. Confirm whether `A_a`, its quadratic form, compact resolvent, or parity spectral projections
   have appeared elsewhere since this handover.
3. Read Suzuki's source definitions directly and build a dependency table from each source object
   to the exact existing Lean connector.  Do not write Lean yet.
4. On paper, formulate the parity spectral measures and the weakest source estimate that rules out
   both universal ends on one cofinal schedule.
5. Hostile-audit the estimate for vanishing overlap, closing parity gap, multiple ground space,
   pointwise-only convergence, and hidden RH positivity.
6. Add or update an in-progress pipeline card before undertaking a hard proof so the state survives
   compaction.
7. Formalize one dependency-closed theorem batch only after the paper statement stabilizes.
8. Run one targeted source check, the formal lint/generator checks if the API changes, one scratch
   axiom audit, and one exact final module build.

## 14. Completion criteria for the next meaningful milestone

The next milestone is complete only if it achieves one of the following, unconditionally:

- a concrete Lean construction of a substantive Suzuki source layer and an actual instantiation
  of an existing carrier theorem; or
- a new source-derived cofinal spectral estimate that excludes at least one remaining degeneration
  and has a dependency-closed paper proof; or
- a rigorous classification/no-go for a proposed intermediate schedule together with a new
  positive invariant or replacement hypothesis, formalized in Lean where its dependencies exist.

It is not complete merely because a new proposition has been named, a generic implication has
compiled, a finite-aperture real-zero theorem has been restated, or a numerical experiment looks
favorable.

## 15. One-paragraph restart summary

Suzuki supplies unconditional finite-aperture all-angle real-zero characteristic functions.  The
project has turned them into anchored Schur/Livšic carriers with normal-family compactness,
classified far-negative shifts as a free zero boundary, and now classified sufficiently rapid
approach to a simple parity ground state as a universal plus/minus Cayley boundary.  The latest
Lean theorem proves the exact leakage bound, Fourier endpoint derivative, locally uniform
derivative transfer, Schwarz rigidity, and the contrapositive scale-selection law.  Do not redo
those results.  Resume by constructing or estimating the concrete parity-resolved Suzuki
resolvent on a source-selected intermediate schedule, with the aim of retaining excited spectral
mass and proving a non-universal, divisor-preserving Xi/de Branges limit.  RH remains open.

## 16. 2026-07-21 update: exact Herglotz boundary-state classification

This section supersedes Sections 12--15 as restart guidance.  Scalar leakage estimates are no
longer the right frontier object.

### 16.1 New theorem

For the universal far-negative Suzuki carrier

```text
Theta_a^free(z)=(exp(-2a)-exp(2iaz))/(1-exp(-2a)exp(2iaz)),
m_a^free(z)=i(1+Theta_a^free(z))/(1-Theta_a^free(z)),
```

direct Cayley algebra gives the exact identity

```text
m_a^free(z)=coth(a) tan(a z),                 a>0, Im z>0.       (S16.1)
```

Its Nevanlinna measure is therefore the half-integer clock

```text
mu_a=(coth(a)/a) sum_(k in Z) delta_((k+1/2)pi/a).              (S16.2)
```

Midpoint Riemann sums give

```text
mu_a -> dx/pi vaguely,
m_a^free -> i locally uniformly on Im z>0.                      (S16.3)
```

The opposite universal ground edge has

```text
Theta_edge(z)=(z-i)/(z+i),
i(1+Theta_edge)/(1-Theta_edge)=z.                               (S16.4)
```

In normalized Nevanlinna data, `(S16.3)` is homogenization of discrete clock atoms to Lebesgue
measure, whereas `(S16.4)` is zero finite-plane measure with unit linear coefficient: spectral
mass at the projective point at infinity.  Suzuki's two shift extremes erase arithmetic by two
different exact mechanisms.

Full dependency-closed proof, hostile audit, and literature caveat:

- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-free-clock-homogenization.md`

Generic tangent/Herglotz theory is classical.  Candidate source-specific novelty is the exact
identification of Suzuki's free projective boundary with this clock law and its comparison with
ground-edge mass escape.  Priority remains unverified.  This is not an RH proof.

### 16.2 Lean status

New module:

- `formal/GaloisForLFunctions/RHTower/SuzukiHerglotzBoundaryStates.lean`

It proves, without project axioms or RH assumptions:

- `suzukiFreeHerglotz_eq_rcoth_mul_tan`;
- `suzukiFreeClock_cos_eq_zero_iff`;
- `suzukiFreeHerglotz_I_eq_I`;
- `suzukiFreeHerglotz_tendstoLocallyUniformlyOn`.

The opposite boundary identity reuses `suzukiUpperCayleyInv_lineCayley`.  The new module is wired
into `RiemannHypothesisSOTA2026.lean` and the `RHTower.lean` import ledger.  Verification completed:

```text
lake env lean GaloisForLFunctions/RHTower/SuzukiHerglotzBoundaryStates.lean
lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026
lake env lean /tmp/SuzukiBoundaryAxiomAudit.lean
python3 scripts/formal_tools.py lint
```

The axiom audit reports only Lean/mathlib foundations `propext`, `Classical.choice`, and
`Quot.sound`.

### 16.3 Correct frontier invariant

The leakage scalar from the ground-edge no-go is only a first-moment shadow.  A nonzero scalar can
still converge to finite support, continuous spectrum, a wrong clock, or a finite Blaschke model.
The actual intermediate-window state is the complete normalized Nevanlinna triple

```text
(linear coefficient at infinity, affine constant, finite-plane spectral measure),
```

together with spectral type and infinite atomic support.  A divisor-bearing Suzuki schedule must
prove simultaneously:

```text
linear coefficient -> 0,                    excluding ground escape;
mu_a does not approach dx/pi,                excluding free-clock homogenization;
a tight infinite atomic component survives, excluding finite/continuous collapse;
its atoms and weights converge to the Xi/de Branges divisor.                    (S16.5)
```

Avoid another round of leakage, gap, or overlap estimates unless it closes one item of `(S16.5)`
for the concrete Suzuki source measure.

### 16.4 Next frontier attack

Construct the actual normalized Nevanlinna data of Suzuki's parity-resolved resolvent, not another
abstract carrier:

1. Derive the Clark/Nevanlinna measure of the finite-aperture characteristic quotient directly
   from Suzuki's two source vectors and Friedrichs resolvent.
2. Identify its linear coefficient and atomic weights as explicit parity-resolved spectral
   projection data.
3. Choose the cofinal shift intrinsically by a measure normalization or quantile condition that is
   invariant under common defect scaling.
4. Prove measure tightness plus vanishing linear coefficient on that schedule.
5. Prove a source-level obstruction to the clock law `dx/pi`, preferably a persistent arithmetic
   statistic that sees infinitely many atoms rather than finitely many moments.
6. Weld the surviving atomic divisor to the global Xi/de Branges divisor.  This remains the open
   producer theorem and must not assume admissibility of the RH-bearing shift `lambda=0`.

Do not spend a session formalizing generic Clark theory, generalized Schur algorithms, or a finite
moment hierarchy already present in `HTGeometry`.  First derive one concrete source identity that
forces the finite-aperture Suzuki Nevanlinna measure into the framework above.

## 17. 2026-07-21 update: cofinal prime-tangent tomography

This section supersedes the claim in Section 16.4 that a persistent arithmetic statistic still
had to be found. Such a statistic now exists and is complete at first order.

### 17.1 Exact source theorem

Let

```text
w_a(x)=e^(-x)(A_a e^x)(x),
H_a(z)=integral_(-a)^a (A_a e^x)(x)e^(izx) dx,
k_(a,n)=pi n/a,
z_(a,n)=k_(a,n)+i.
```

Suzuki's distribution formula (2.11), the exact endpoint logarithm, and integration by parts give

```text
(-1)^n k_(a,n) Re H_a(z_(a,n))
 = Si(2 pi n)
   + sum_(2<=m<=e^(2a))
       Lambda(m)(sqrt(m)+m^(-3/2)) sin(pi n log(m)/a)
   + o_(n->infinity)(1).                                 (S17.1)
```

The remainder proof is source-level: after removing logarithm and finite prime steps, the weighted
kernel action is `C^1`; its clock endpoint term is purely imaginary and Riemann--Lebesgue kills the
real derivative term. No estimate, computation, or RH input is used.

Consequences:

```text
Cesaro mean of left side -> pi/2 for every a>0;             (S17.2)

nonresonant Bohr coefficient at exp(i pi log(m)/a)
 -> Lambda(m)(sqrt(m)+m^(-3/2))/(2i).                       (S17.3)
```

After division by the explicit positive reflected-step scale, `(S17.3)` recovers `Lambda(m)`
exactly. Resonant apertures lie in the countable set generated by

```text
a=(log j-log m)/(2 ell),
a=log(jm)/(2 ell).
```

Its complement is dense and cofinal. Along a cofinal nonresonant schedule, every fixed
von-Mangoldt coefficient is eventually present and exactly recoverable. Thus Suzuki's first
projective tangent is an unconditional cofinally complete prime-power carrier.

Full proof and hostile audit:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-high-clock-prime-tangent-tomography.md`

### 17.2 Lean status

New module:

- `formal/GaloisForLFunctions/RHTower/SuzukiPrimeTangentTomography.lean`

It proves finite exponential and sine Bohr recovery, Suzuki's unit phase law, positivity and exact
reflected decomposition of the source scale, prime-power support classification, and normalized
convergence to `ArithmeticFunction.vonMangoldt m`. The final capstone is

```text
tendsto_suzukiPrimeTangentCarrier_normalized_bohrCoefficient_of_nonresonant.
```

Exact source check and module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. The module is imported by both `RHTower.lean` and
`RiemannHypothesisSOTA2026.lean`.

### 17.3 Revised open core

Arithmetic loss at the far-negative tangent is no longer a viable explanation of failure: all
prime-power weights survive. The obstruction is continuity of the recovery topology. Bohr
inversion uses arbitrarily long clock averages, hence expanding real spectral windows; ordinary
locally uniform convergence of Livšic carriers does not preserve these observables.

Next frontier theorem must build an explicit transference map

```text
source tangent Bohr coefficient field
  -> intermediate-shift Clark/Donoghue atom weights
```

which is uniform on one intrinsic cofinal shift schedule and simultaneously proves tight infinite
atomic survival. Only then can the recovered prime packet constrain the limiting Xi/de Branges
divisor. Do not return to proving mere nonzero tangents, finite leakage moments, or generic
compactness: those levels are now strictly weaker than `(S17.3)`.

This is significant movement toward the open producer, not an RH proof. The missing theorem is
exactly the nonuniform-high-mode-to-tight-measure transfer and subsequent divisor identification.

## 18. 2026-07-21 update: prime steps move the Donoghue divisor exactly

This section supersedes Section 17.3's statement that the first-order source-to-measure transfer
map was missing. That map is now explicit and primewise faithful.

### 18.1 Exact clock-atom velocity law

Let

```text
x_(a,k)=((k+1/2)pi)/a
```

be the `k`th pole of the far-negative free Donoghue clock. For
`epsilon=(-lambda)^(-1)`, the already proved pole response is

```text
dot x_(a,k)=-Delta_a(x_(a,k))/(2 i a tanh(a)).             (S18.1)
```

Insert one `m`th prime-power step from Suzuki's equation (2.11). Exact endpoint integration gives,
at `z=x_(a,k)`,

```text
Delta_(a,m)(z)
 =-2i Lambda(m)/sqrt(m) tanh(a) sin(z log(m)).             (S18.2)
```

The hyperbolic factor in `(S18.2)` cancels the pole geometry in `(S18.1)`:

```text
dot x_(a,k)^(m)
 =Lambda(m)/(a sqrt(m)) sin(x_(a,k) log(m)).               (S18.3)
```

Therefore the complete arithmetic support velocity is

```text
V_a^prime(k)
 =sum_(2<=m<=e^(2a)) Lambda(m)/(a sqrt(m))
   sin((k+1/2)pi log(m)/a).                                (S18.4)
```

In physical spectral coordinate,

```text
a V_a^prime(k)=P_a(x_(a,k)),
P_a(t)=sum_(2<=m<=e^(2a)) Lambda(m)/sqrt(m) sin(t log(m)). (S18.5)
```

This is the truncated critical von-Mangoldt sine transform, not the growing
`sqrt(m)+m^(-3/2)` source-sampling weight from Section 17. Projective reflection and atom
normalization convert the source packet to the natural critical explicit-formula weight.

At every nonresonant aperture, half-shifted Bohr demodulation of `(S18.4)` recovers each
`Lambda(m)` exactly. Hence the first-order motion of the concrete Donoghue support is a complete
prime-power carrier.

Full proof and hostile audit:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-prime-clock-atom-velocity-transference.md`

### 18.2 Lean status

New axiom-clean module:

- `formal/GaloisForLFunctions/RHTower/SuzukiPrimeClockAtomVelocity.lean`

Its source-specific capstone

```text
suzukiPrimeClockReflectedRatio_velocity
```

proves exact cancellation between the reflected prime-step quotient and free-pole geometry. The
normalized tomography capstone

```text
tendsto_suzukiPrimeClockAtomVelocity_normalized_bohrCoefficient_of_nonresonant
```

recovers `ArithmeticFunction.vonMangoldt m` from the divisor-velocity packet. Critical amplitudes
are nonzero exactly on prime powers. Source check, exact module build, global lint, and axiom audit
all pass; the audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

### 18.3 Revised open core

The following arrows are now closed unconditionally at first order:

```text
restricted-Weil prime step
  -> projective source tangent
  -> concrete Donoghue pole velocity
  -> exact von-Mangoldt reconstruction.                   (S18.6)
```

What remains is genuinely nonlinear. The next theorem must integrate `(S18.3)` away from the
far-negative boundary along one intrinsic admissible finite-shift path while retaining critical
prime modes, prove tight infinite atomic spectral probability on a cofinal aperture schedule, and
then identify its support with the Xi/de Branges divisor.

Do not return to source nonvanishing, high-clock faithfulness, or a generic tangent-to-measure
interface; all are now strictly subsumed by `(S18.3)--(S18.6)`. Also do not mistake the growing
critical sine polynomials `(S18.5)` for an ordinary cofinal limit. Their nonlinear compensation by
the full restricted-Weil resolvent is the exact live producer problem.

RH remains open.

## 19. Finite-shift nonlinear integration is a flat projective resolvent holonomy

Section 18 left one explicit question: can the arithmetic-complete free-boundary velocity be
integrated through a finite Suzuki shift without perturbative remainders or arbitrary pole
labeling?  The answer is yes at the full meromorphic-carrier level.

### 19.1 A stronger global-flow conjecture was rejected

At fixed aperture every Suzuki extension eigenvalue is real and simple, and the resolvent source
depends analytically on an admissible shift.  This gives local real-analytic pole curves by the
implicit-function theorem.  It does **not** give globally labeled curves over the full shift
interval: simplicity prevents collisions but does not prevent a labeled zero escaping to infinity
at a finite parameter.  No available theorem supplies the needed properness or uniform zero count.

The result below avoids that missing premise and integrates the entire carrier directly.

### 19.2 Exact endpoint transport

Fix `a>0`, put

```text
R_r=(A_a+rI)^(-1),
u_r=R_r e^x,
F_r(z)=integral_[-a,a] u_r(x) exp(i z x) dx,

Theta_r(z)=((z-i)F_r(z))/((z+i)F_r(-z)).                 (S19.1)
```

For admissible `r,s`, define

```text
J_(s,r)(z)=Fourier[R_s R_r e^x](z),
D_(s,r)(z)=J_(s,r)(z)F_r(-z)-F_r(z)J_(s,r)(-z).          (S19.2)
```

The second resolvent identity gives

```text
F_s=F_r+(r-s)J_(s,r).                                    (S19.3)
```

Subtraction of the two projective carriers now yields the exact finite law

```text
Theta_s(z)-Theta_r(z)
 =((z-i)/(z+i))
   *(r-s)D_(s,r)(z)/(F_s(-z)F_r(-z)).                    (S19.4)
```

There is no asymptotic sign, Taylor remainder, or small-shift condition in `(S19.4)`.

Define the endpoint transport

```text
H_(s<-r)(z)
 =F_s(z)F_r(-z)/(F_s(-z)F_r(z)).                         (S19.5)
```

Then

```text
Theta_s=H_(s<-r)Theta_r,

H_(s<-r)-1
 =(r-s)D_(s,r)/(F_s(-z)F_r(z)).                          (S19.6)
```

### 19.3 Nonlinear source evolution becomes flat after projectivization

For any three admissible shifts,

```text
H_(t<-r)=H_(t<-s)H_(s<-r).                               (S19.7)
```

Every intermediate transform cancels from the cross ratios.  Consequently two different finite
paths with the same endpoints have identical projective holonomy.  This applies equally to a
multi-parameter activation of Suzuki's finitely many prime-step operators at fixed aperture:
operator resolvent dressings are nonlinear, but their scalar reflected carrier transport is
endpoint-only.  Prime-activation order and path subdivision introduce no new obstruction.

### 19.4 Exact local pole equation is the diagonal of the finite law

Let

```text
G_r(z)=Fourier[R_r^2 e^x](z),
Xi_r(z)=G_r(-z)/F_r(-z)-G_r(z)/F_r(z).                   (S19.8)
```

Since `partial_r R_r=-R_r^2`,

```text
partial_r Theta_r=Theta_r Xi_r,

Xi_r(z)
 =-[G_r(z)F_r(-z)-F_r(z)G_r(-z)]/[F_r(z)F_r(-z)].        (S19.9)
```

At a local simple real pole `Theta_r(x(r))=1`, write

```text
partial_z Theta_r(x)=i q_r(x),
mu_r({x})=2/q_r(x).
```

The exact nonlinear support equation is

```text
x'(r)=i mu_r({x})Xi_r(x)/2.                              (S19.10)
```

Real source reflection makes `Xi_r(x)` purely imaginary, so `(S19.10)` is real.  At the free
prime-step endpoint, `(S19.10)` specializes to the explicit velocity `(S18.3)`.

Full proof and hostile audit:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-finite-shift-flat-projective-resolvent-holonomy.md`

### 19.5 Lean status

New source-specific module:

- `formal/GaloisForLFunctions/RHTower/SuzukiFiniteShiftProjectiveHolonomy.lean`

Formal capstones:

```text
suzukiProjectiveSourceTransport_comp
suzukiProjectiveSourceTransport_path_independent
suzukiProjectiveSourceTransport_finiteShift_sub_one
suzukiFourierLivsic_eq_transport_mul
suzukiFourierLivsic_finiteShift_sub
suzukiFourierLivsic_finiteShift_dividedDifference
suzukiLogarithmicSourceGenerator_eq_neg_reflectionTangent
suzukiImplicitPoleVelocity_eq_clarkTransport
```

The formal layer proves the exact projective algebra and its connectors.  The unbounded-operator
second-resolvent identity remains paper-level until Suzuki's concrete Friedrichs operator is in
Lean.

### 19.6 Revised open core

The following chain is now closed unconditionally at fixed aperture:

```text
prime-power source atom
  -> exact free-pole velocity
  -> finite two-resolvent carrier response
  -> flat endpoint projective holonomy.                  (S19.11)
```

Do not return to local perturbation series or attempt to order prime activations; `(S19.7)` removes
both issues.  The remaining frontier is one cofinal endpoint theorem:

```text
choose intrinsic admissible endpoints (r_a,s_a)
  -> prove compact-open tightness and divisor control for H_(s_a<-r_a)
  -> identify its limiting poles and Clark weights with the Xi/de Branges divisor.
                                                                    (S19.12)
```

Equivalently, control the normalized dressed determinants in `(S19.4)` or `(S19.6)`.  This is a
global cofinal compactness/divisor problem, no longer a finite-shift integration problem.

RH remains open.

## 20. Global phase conjugacy closes the finite-shift pole-escape wall

Section 19 deliberately stopped short of globally labeled pole curves: simplicity alone does not
prevent a local implicit branch from escaping to infinity at a finite shift.  That warning was
correct but incomplete.  The Donoghue spectral law from Section 16 supplies a different
properness mechanism that does not use zero estimates.

### 20.1 Cyclic pure-point support forces a global phase chart

For each admissible fixed-aperture shift `r`, write

```text
m_r=i(1+Theta_r)/(1-Theta_r).
```

The finite-aperture Donoghue measure is pure point and is the spectral probability of a cyclic
deficiency vector.  Suzuki's Hilbert space is infinite dimensional, so this probability cannot
have finite support.  It is even, has no atom at zero, and its meromorphic support has no finite
accumulation.  Hence it has infinitely many atoms in both real directions.

The unimodular real boundary carrier has the uniquely normalized lift

```text
Theta_r(x)=exp(i phi_r(x)),
phi_r(0)=pi.                                             (S20.1)
```

Away from Clark poles,

```text
phi_r'(x)=2m_r'(x)/(1+m_r(x)^2)>0,                       (S20.2)
```

while at a pole of mass `mu_r({x})`,

```text
phi_r'(x)=2/mu_r({x})>0.                                 (S20.3)
```

Because the phase assumes infinitely many distinct values in `2 pi Z` in both directions,

```text
phi_r : R -> R
```

is a strictly increasing real-analytic bijection.  This is the properness missing from the local
argument in Section 19.

### 20.2 One diffeomorphism transports every extension divisor

For two admissible shifts define

```text
T_(s<-r)=phi_s^(-1) o phi_r.                             (S20.4)
```

Then `T_(s<-r)` is an orientation-preserving real-analytic diffeomorphism and

```text
T_(r<-r)=id,
T_(t<-r)=T_(t<-s) o T_(s<-r).                           (S20.5)
```

Suzuki's angle-`theta` spectrum has the global labels

```text
x_(theta,k)(r)=phi_r^(-1)(theta+pi+2 pi k),   k in Z.    (S20.6)
```

Therefore

```text
T_(s<-r)(x_(theta,k)(r))=x_(theta,k)(s)                 (S20.7)
```

for every extension angle and every label simultaneously.  Every curve is real analytic on the
whole admissible shift interval; distinct labels never collide, and no fixed label can escape at
an interior shift.  Escape remains possible only at an admissible endpoint, at infinite shift, or
in the changing-aperture limit.

### 20.3 Phase density, Clark masses, and source norms move together

Differentiating the defining phase identity gives

```text
phi_s'(T(x))T'(x)=phi_r'(x).                             (S20.8)
```

Thus the complete phase-speed density is transported, and each consecutive phase cell has exact
mass `2 pi`.  At an even-extension pole, `(S20.3)` turns `(S20.8)` into

```text
mu_s({T(x)})=T'(x)mu_r({x}).                             (S20.9)
```

The normalized Donoghue spectral probabilities obey

```text
nu_s({T(x)})
 =T'(x)(1+x^2)/(1+T(x)^2) nu_r({x}).                    (S20.10)
```

Substitution of the restricted-Weil source formula gives the exact new norm transference law

```text
(1+T(x)^2)|F_s(-T(x))|^2/(N_s||v_(s,T(x))||_(T_s)^2)
 =T'(x)(1+x^2)|F_r(-x)|^2/(N_r||v_(r,x)||_(T_r)^2).     (S20.11)
```

So the global flow carries support, order, atom mass, Fourier deficiency amplitude, and extension
eigenvector norm as one object.

Finally, comparison of

```text
partial_r Theta_r=Theta_r Xi_r
```

with `(S20.1)` gives `partial_r phi_r=-i Xi_r`.  Each globally labeled even pole therefore solves

```text
x_k'(r)=i mu_r({x_k(r)})Xi_r(x_k(r))/2,                 (S20.12)
```

which proves that Section 19's local Clark velocity is the infinitesimal generator of this global
divisor-measure flow.

Full proof and hostile audit:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-global-phase-conjugacy-divisor-flow.md`

### 20.4 Lean status

New source-specific module:

- `formal/GaloisForLFunctions/RHTower/SuzukiGlobalPhaseConjugacy.lean`

Formal capstones:

```text
suzukiPhaseTransport_comp
suzukiPhaseTransport_pole
suzukiPhasePole_lt_phasePole
suzukiPhaseTransport_phaseSpeed
suzukiPhaseTransport_atomMass
suzukiPhaseTransport_probabilityMass
suzukiPhaseTransport_sourceNormWeight
suzukiGlobalPoleVelocity_eq_sourceGenerator
```

Exact source check, exact module build, SOTA import check, and axiom audit pass.  The exported
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

### 20.5 Revised open core

The finite-aperture chain is now closed through the complete weighted divisor:

```text
prime-power source atom
  -> exact free-pole velocity
  -> finite projective holonomy
  -> global all-extension phase conjugacy
  -> exact Clark/source-weight Jacobian.                 (S20.13)
```

The remaining frontier is no longer global pole existence or separate residue control.  It is one
cofinal compactness-and-identification theorem:

```text
choose intrinsic admissible r_a
  -> normalize the inverse-phase maps phi_(a,r_a)^(-1)
  -> prove compactness together with first derivatives at the phase lattice
  -> identify the limiting weighted lattice with the Xi/de Branges divisor. (S20.14)
```

That single inverse-phase object contains the pole support and all Clark weights.  Ground escape
and free clock homogenization are precisely degenerations of this object at the cofinal boundary.

RH remains open.

## 21. Compactified inverse-phase holography solves the cofinal topology wall

Section 20 left compactness of inverse phases and their lattice derivatives as separate tasks.
They are not separate.  Cayley compactification turns both into one fixed-label jet object and
exposes the exact defect that can still obstruct an Xi limit.

### 21.1 The forced Cayley zero gives a sharp global speed cap

For any normalized proper Suzuki phase, set

```text
X(y)=phi^(-1)(pi+y),
U(y)=arctan X(y).                                       (S21.1)
```

The normalization `Theta(i)=0` factors

```text
Theta(z)=((z-i)/(z+i))S(z),                             (S21.2)
```

with residual meromorphic inner factor `S`.  Its boundary phase speed is nonnegative, so

```text
q(x)=phi'(x)>=2/(1+x^2).                                (S21.3)
```

Inverse differentiation now gives the sharp law

```text
U'(y)=1/[q(X(y))(1+X(y)^2)],
0<U'(y)<=1/2.                                           (S21.4)
```

Hence every `U` is odd, increasing, valued in `(-pi/2,pi/2)`, and globally `1/2`-Lipschitz.
Every aperture/shift sequence therefore has a locally uniformly convergent subsequence on the
whole phase line.  This is unconditional and uses no zero estimate.

### 21.2 One fixed lattice jet reconstructs the moving probability

Use the fixed odd-`pi` lattice

```text
y_k=(2k-1)pi,             k in Z.                       (S21.5)
```

Then `pi+y_k=2pi k`, so the even Clark pole and its normalized Donoghue mass are exactly

```text
x_k=tan U(y_k),
nu({x_k})=2U'(y_k),
sum_(k in Z) 2U'(y_k)=1.                                (S21.6)
```

Thus

```text
nu=sum_(k in Z) 2U'(y_k) delta_(tan U(y_k)).             (S21.7)
```

Pole positions and weights are not two convergence problems: values and derivative samples of
one compactified inverse phase recover the full spectral probability.

### 21.3 Every cofinal limit has a canonical residual decomposition

For an arbitrary cofinal sequence define

```text
p_(n,k)=2U_n'(y_k),
sigma_n=(arctan)_*nu_n
       =sum_k p_(n,k) delta_(U_n(y_k)).                  (S21.8)
```

After one diagonal subsequence,

```text
U_n -> U_infinity locally uniformly,
p_(n,k) -> p_k for every k,
sigma_n -> sigma weakly.                                (S21.9)
```

Writing `u_k=U_infinity(y_k)`, positivity and finite-label convergence imply

```text
sigma_lab=sum_k p_k delta_(u_k),
sigma>=sigma_lab,
sigma_res:=sigma-sigma_lab>=0,
sigma_res(total)=1-sum_k p_k.                           (S21.10)
```

This is the exact cofinal classification: a fixed-label atomic survivor plus a unique positive
phase-label-escape residual.  No derivative convergence of `U_infinity` is assumed; the bounded
lattice derivatives are extracted as independent coordinates.

If `sum_k p_k=1` and every `|u_k|<pi/2`, then `sigma_res=0`, the physical measures are tight, and

```text
nu_n -> sum_k p_k delta_(tan u_k).                       (S21.11)
```

Positivity of every `p_k` and strict increase of `u_k` preserve an infinite simple two-sided
divisor.  Conversely, `(S21.10)` separates label escape, endpoint escape, and label coalescence.

### 21.4 The two universal boundary states occupy different strata

For the free clock, every fixed label collapses to zero and its mass vanishes, while the full
compactified probability tends to normalized Lebesgue measure:

```text
U_infinity=0,
sigma_lab=0,
sigma_res=du/pi.                                        (S21.12)
```

For the ground Cayley carrier, the generalized compactified inverse is the clipped ramp

```text
U_ground(y)=clip(y/2,-pi/2,pi/2),                        (S21.13)
```

and escape appears at the projective endpoints.  Free-clock homogenization is therefore phase-
label escape; ground degeneration is physical escape to infinity.  Compactification distinguishes
them exactly.

Full proof and hostile audit:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-compactified-inverse-phase-lattice-holography.md`

Lean structural core:

- `formal/GaloisForLFunctions/RHTower/SuzukiCompactifiedPhaseProfile.lean`

Formal capstones include `suzukiAnchoredPhaseSpeed_floor`,
`hasDerivAt_suzukiCompactifiedInversePhase`,
`suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv`,
`hasSum_two_mul_suzukiCompactifiedDeriv_one`, and
`suzukiCompactifiedInversePhase_lipschitz`.

### 21.5 Revised open core

Generic cofinal compactness is no longer open.  The remaining source theorem is exact:

```text
choose an intrinsic admissible schedule
  -> prove sum_k p_k=1 and |u_k|<pi/2
  -> eliminate sigma_res
  -> identify (u_k,p_k) with the Xi/de Branges divisor jets. (S21.14)
```

Prime tangent tomography and finite-shift holonomy now have a fixed target: control
`U_n(y_k),U_n'(y_k)` rather than moving poles and residues separately.  RH remains open.
