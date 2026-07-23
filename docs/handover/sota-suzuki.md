# Suzuki screw-function RH route — complete research handover

**Last updated:** 2026-07-22
**Repository:** `/Users/michael/Documents/code/hgt`
**Resolved repository path:** `/Users/michael/Documents/code/hgt`
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

The exact remaining scientific wall is now narrower, but it has two object types that must not be
conflated. Suzuki's canonical Donoghue function is an anchored ratio of two parity phases. His
conjectural reciprocal-logarithmic target is one characteristic phase. The auxiliary boundary-free
targets form `D_eta=XiC'-eta*XiC`, and every finite fibre has the same Xi divisor, but reflection
exchanges `eta` and `-eta`; the zero fibre is the unique odd member. Therefore a nonzero one-fibre
cluster cannot itself be reconstructed as the canonical odd Donoghue carrier.

The strongest exact replacement is distinct-channel opposite-shift cross-sewing. Actual `+eta`
and `-eta` resolvents need not produce the same characteristic function, interval term, or gauge.
Cross-multiplying each exterior remainder by the opposite characteristic factor produces exactly
one zero-shift remainder with product characteristic. Dividing by that product yields a projective
observable invariant under two independent zero-free gauges; its hypothetical nonreal Xi-pole
coefficient is universally `ord_z(XiC)/z^2`. Remaining frontier is:

> Construct actual opposite-shift exterior source channels and prove cofinal off-real analytic
> continuation of their projectively normalized cross-sewn observable. No equality or common
> gauge between shift channels is required.

At an Xi zero of arbitrary multiplicity `m`, every shifted target zero is simple with exact first
coefficient `z^2/m`.  Shift normalization and Xi-zero simplicity are therefore no longer premises.

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
4. Read these five Suzuki cards completely:

   ```text
   docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
     suzuki-finite-aperture-hermite-biehler-normal-family.md
   docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/
     suzuki-negative-shift-defect-escape.md
   docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
     suzuki-projective-defect-free-boundary.md
   docs/drafts/pipeline/3-formalized/needs-audit/
     suzuki-ground-edge-cayley-universality.md
   docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
     suzuki-shifted-xi-target-flat-pencil.md
   ```

5. Read the Suzuki row and checklist in
   `docs/drafts/pipeline/1-in-progress/rh-sota-literature-lean-wall-2026.md`.
6. Read these Lean modules in dependency order:

   ```text
   formal/GaloisForLFunctions/RHTower/SuzukiFiniteApertureHermiteBiehler.lean
   formal/GaloisForLFunctions/RHTower/SuzukiProjectiveDefectBoundary.lean
   formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeCayleyUniversality.lean
   formal/GaloisForLFunctions/RHTower/SuzukiShiftedXiTargetFlatPencil.lean
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

## 22. Residual mass is exactly overcrowding plus linear escape

The residual in `(S21.10)` has two disjoint analytic producers.  For every nonnegative continuous
test `f` on the compactified interval,

```text
int f d sigma_res
 =lim_(K->infinity) lim_(n->infinity)
    sum_(|k|>K) p_(n,k) f(U_n(y_k)).                     (S22.1)
```

Thus interior residual is probability whose phase label escapes while its physical position stays
bounded.  If

```text
sup_n #{k: |U_n(y_k)|<=r}<infinity       for every r<pi/2, (S22.2)
```

then `sigma_res` has no mass in `(-pi/2,pi/2)`.  Strict phase order is essential: a large label in
a fixed physical window forces every intervening central label into a slightly larger fixed
window, contradicting `(S22.2)`.

This turns interior residual elimination into a complex-analytic normality problem.  If zero-free
entire gauges `g_n` make the even characteristic functions converge locally uniformly,

```text
g_n W_(n,-1) -> W_(-1) != 0,                            (S22.3)
```

Rouche's theorem bounds their zero counts on every real compact, so `(S22.2)` holds.  Common-gauge
convergence of the parity pair additionally gives

```text
-i W_(n,1)/W_(n,-1) -> -i W_1/W_(-1)                   (S22.4)
```

meromorphically away from the limiting pole set.  This is pair normality before quotienting, not
the impossible ordinary entire convergence to Suzuki's meromorphic target.

The remaining endpoint defect is exact.  The Donoghue probability kernel obeys

```text
K_z(t)=(tz+1)/(t-z)=z+(z^2+1)/(t-z),
K_z(+infinity)=K_z(-infinity)=z.                         (S22.5)
```

If `alpha` is total endpoint mass of the compactified weak limit, then

```text
m_infinity(z)=alpha z+int_R K_z(t)dnu_int(t).            (S22.6)
```

Hence `alpha` is exactly the linear Nevanlinna coefficient; evenness splits it equally between
the two endpoints.  The two-condition closure theorem is therefore

```text
common-gauge entire-pair normality
  + zero linear Nevanlinna coefficient
  => sigma_res=0 and sum_k p_k=1.                        (S22.7)
```

The conditions are independent.  Free clocks violate local zero-count boundedness and produce
uniform interior residual; the Cayley ground edge has no interior overcrowding but produces linear
endpoint mass.

There is also a rigidity gain.  Equality of `U(y_k)` and `U'(y_k)` for all fixed labels makes the
Donoghue probabilities equal, hence their Herglotz transforms, Livsic carriers, normalized phases,
and every extension divisor are equal.  The lattice first jet is a complete carrier invariant.

Full paper proof and hostile audit:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-residual-overcrowding-entire-pair-closure.md`

The projective endpoint limits `(S22.5)` are formalized as
`tendsto_suzukiDonoghueKernel_atTop` and `tendsto_suzukiDonoghueKernel_atBot` in
`formal/GaloisForLFunctions/RHTower/SuzukiCompactifiedPhaseProfile.lean`.

The remaining frontier is no longer an unspecified compactness/tightness estimate.  It is the
source construction of one common entire gauge for the parity pair, proof that the limiting
Donoghue function has no linear term, and identification of its meromorphic ratio with the global
Xi/de Branges carrier.  RH remains open.

## 23. The continuous-kernel shift is a flat Xi pencil, not a distinguished target

Section 8 contains a stronger consequence than the displayed `lambda=0` heuristic.  Suzuki's
continuous kernel is

```text
S_a=G_a-lambda(-Delta_N)^(-1),
hat(g)(z)=z^(-2)xi'(1/2-iz)/xi(1/2-iz).                 (S23.1)
```

After the still-open finite-interval Neumann boundary passage, the inverse-Laplacian symbol shifts
the logarithmic derivative by a constant.  In centered even coordinates the complete
boundary-free target pencil is, up to Suzuki's fixed nonzero scalar,

```text
D_eta(z)=XiC'(z)-eta XiC(z),
R_eta(z)=z^2 XiC(z)/D_eta(z),
eta=-i lambda.                                          (S23.2)
```

This is not asserted at finite aperture: the Neumann inverse there is not a whole-line convolution
operator.  The boundary term remains part of the operator frontier.

The pencil is exactly affine:

```text
D_alpha-D_beta=(beta-alpha)XiC,
XiC=(D_alpha-D_beta)/(beta-alpha)       (alpha!=beta).  (S23.3)
```

Hence two normalized finite shift fibres recover Xi directly.  Its target transport is flat:

```text
T_(alpha,beta)=D_alpha/D_beta,
T_(alpha,beta)R_alpha=R_beta,
T_(alpha,beta)T_(beta,gamma)=T_(alpha,gamma),           (S23.4)

[z^2-(beta-alpha)R_alpha]R_beta=z^2R_alpha,
z^2/R_beta-z^2/R_alpha=alpha-beta.                      (S23.5)
```

The decisive local theorem is unconditional and allows arbitrary Xi multiplicity.  If `z_0` is an
Xi zero of order `m>=1`, then for every finite `eta`,

```text
ord_(z_0)(D_eta)=m-1,
ord_(z_0)(R_eta)=1,
TC_(z_0)(R_eta)=z_0^2/m.                                (S23.6)
```

Thus every finite shifted target has exactly the same Xi zero set.  Every Xi multiplicity is
collapsed to a simple target zero, but is not lost: it is the reciprocal factor in the exact first
coefficient.  For a simple Xi zero,

```text
R_eta'(z_0)=z_0^2,                                      (S23.7)
```

independent of the shift.  This removes the apparent conflict between simple self-adjoint
extension spectra and potentially multiple Xi zeros without assuming simplicity.

At fixed nonzero `z`, shift variation is the exact Riccati flow

```text
dR_eta(z)/deta=R_eta(z)^2/z^2.                          (S23.8)
```

The old source demand

```text
choose lambda_a -> 0 and identify R_0
```

was unnecessarily strong.  Divisor recovery now needs only a non-erasing intrinsic schedule with
a finite shift cluster and identification of any cluster target `R_eta`.  Uniqueness of the cluster
and convergence to zero are unnecessary.  Alternatively, prove common-gauge normality for two
distinct finite fibres and use the affine secant `(S23.3)`.

Full proof and hostile audit:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-shifted-xi-target-flat-pencil.md`

Exact Lean formalization:

- `formal/GaloisForLFunctions/RHTower/SuzukiShiftedXiTargetFlatPencil.lean`

Formal capstones include
`XiC_eq_suzukiShiftedXiDenominator_secant`,
`suzukiXiShiftTransport_cocycle`,
`meromorphicOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero`,
`meromorphicTrailingCoeffAt_suzukiShiftedXiTarget_of_XiC_zero`, and
`hasDerivAt_suzukiShiftedXiTarget_parameter_riccati`.

### 23.1 Revised open core

The remaining frontier is narrower:

```text
intrinsic schedule avoiding both erasing boundaries
  -> finite shift cluster (not necessarily zero)
  -> common-gauge parity-pair normality and zero linear mass
  -> finite-Neumann-boundary control identifying (z^2 XiC,D_eta)
  -> Xi divisor recovery via any fibre, or Xi recovery via two-fibre secant. (S23.9)
```

Shift normalization and Xi-zero simplicity are no longer open premises.  Finite-aperture boundary
control and common-gauge operator convergence remain; RH remains open.

Later semantic correction: this conclusion concerns one-phase divisor recovery only. It does not
make `R_eta` the canonical odd Donoghue carrier. Section 26 proves that only `R_0` is odd and gives
the required opposite-shift projection for a parity-compatible finite-cluster route.

## 24. Exact finite-Neumann clock annihilation

The finite Neumann passage in `(S23.9)` does not require endpoint decay.  Twice integrating by
parts shows that its complete boundary defect belongs to the rank-two clock module

```text
C_(a,A,B)(z)=z[A cos(az)+B sin(az)].                    (S24.1)
```

The polynomial differential operator

```text
L_a H=z^2 H''-2z H'+(2+a^2z^2)H                        (S24.2)
```

kills this module identically for arbitrary coefficients:

```text
L_a C_(a,A,B)=0.                                        (S24.3)
```

If `U-z^2F` is Suzuki's finite-Neumann Fourier defect, then

```text
L_a U=L_a(z^2F),                                        (S24.4)
L_a(z^2F)=a^2z^2[z^2F+a^(-2)(2zF'+z^2F'')].            (S24.5)
```

Along `a->infinity`, compact-open holomorphic convergence makes the correction in `(S24.5)` tend
to zero by derivative convergence.  No endpoint coefficient estimate occurs.  The operator must
be applied to the ungauged source identity; it is not commuted through a varying common gauge.

Paper proof and exact Lean formalization:

- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-neumann-clock-annihilator.md`
- `formal/GaloisForLFunctions/RHTower/SuzukiExteriorPoleTomography.lean`

Finite-Neumann boundary control is therefore deleted from the open premise list.

## 25. Anchored Euler--Wronskian elimination of cofinal linear escape

Common-gauge normality removes interior label overcrowding, but compactified probability may still
escape to the two projective ends and add `alpha*z` to the limiting Donoghue function.  Proving
`alpha=0` separately is unnecessary after changing observable to the degree-one Euler defect

```text
E[m](z)=z m'(z)-m(z).                                   (S25.1)
```

It has exact linear kernel

```text
E[m+alpha*z]=E[m].                                      (S25.2)
```

For a common-gauge pair `m=-iA/B`, define

```text
P[A,B]=z(A'B-AB')-AB.                                   (S25.3)
```

Then

```text
E[-iA/B]=-i P[A,B]/B^2,
P[gA,gB]=g^2P[A,B].                                     (S25.4)
```

Thus `(S25.4)` is exactly invariant under the zero-free entire gauges needed by the parity-pair
topology.  More decisively, its Donoghue probability kernel is

```text
K^E_z(t)
 =z partial_z[(tz+1)/(t-z)]-(tz+1)/(t-z)
 =[t(z^2-1)+2z]/(t-z)^2,                                (S25.5)

K^E_z(+infinity)=K^E_z(-infinity)=0.                    (S25.6)
```

Therefore compactified weak convergence passes the Euler transform locally uniformly even with
positive endpoint escape.  No tightness or zero-linear-mass hypothesis is needed for this passage.
The transform loses only `c*z`: if two holomorphic carriers on the upper half-plane have equal
Euler defect, their difference divided by `z` has derivative zero.  Suzuki's canonical anchor
`m(i)=i` kills the constant, so

```text
E[m]=E[n] on H and m(i)=n(i)  =>  m=n on H.             (S25.7)
```

The shifted-Xi one-phase target has a named algebraic covariant:

```text
P_eta=P[z^2XiC,D_eta],
E[R_eta]=P_eta/D_eta^2.                                 (S25.8)
```

Exact Lean formalization is in
`formal/GaloisForLFunctions/RHTower/SuzukiAnchoredEulerWronskian.lean`.

Semantic correction: `(S25.7)` reconstructs one anchored Donoghue ratio from another. It does not
identify that ratio with `R_eta`. Suzuki's `W(a,theta;z)` target and the two-phase Donoghue quotient
are different objects. Formula `(S25.8)` remains correct as an algebraic identity only.

### 25.1 Current exact frontier

The earlier producer chain

```text
intrinsic schedule avoiding both erasing boundaries
  -> finite shift cluster
  -> apply L_a before gauge formation
  -> common-gauge parity-pair normality eliminating interior overcrowding
  -> identify the limiting Euler--Wronskian defect with P_eta/D_eta^2
  -> anchor m(i)=i reconstructs R_eta
  -> recover the Xi divisor.                            (S25.9)
```

is false at its anchor step. Nonzero `R_eta` is not odd; no canonical parity-normalized Donoghue
carrier can equal it. The Euler transform still removes linear endpoint escape from the canonical
ratio, but one-phase Xi target identification must proceed through the exterior channel described
below. RH remains open.

## 26. Opposite-shift parity exchange and exact zero-fibre projection

The source/corpus audit exposes an object-type error in the previous frontier. Suzuki's
Corollary 1.6 asks for the one-phase zero-shift target

```text
R_0(z)=z^2 XiC(z)/XiC'(z),                              (S26.1)
```

whereas the anchored Donoghue function is a ratio of two parity phases. Suzuki explicitly says
his conjectural limit is formulated with `lambda=0` in mind; finite `lambda<lambda_a` is an
auxiliary form shift. The paper does not identify arbitrary shifted fibres with the Donoghue
ratio.

Put

```text
D_eta=XiC'-eta XiC,
R_eta=z^2 XiC/D_eta,
G_eta=R_eta^(-1).
```

Evenness of `XiC` and oddness of `XiC'` give the exact exchange law

```text
D_eta(-z)=-D_(-eta)(z),
R_eta(-z)=-R_(-eta)(z).                                 (S26.2)
```

Combining `(S26.2)` with reciprocal shift translation proves the parity classifier

```text
R_eta is odd  <=>  eta=0.                               (S26.3)
```

Thus arbitrary one-fibre parity reconstruction is impossible. The strongest positive survivor is
not `eta -> 0`, however. Opposite finite fibres recover the distinguished zero fibre exactly:

```text
z^2/R_eta+z^2/R_(-eta)=2z^2/R_0,                        (S26.4)

(R_eta+R_(-eta))R_0=2R_eta R_(-eta)                     (S26.5)
```

away from the displayed divisors. Equation `(S26.5)` says `R_0` is the harmonic mean of the two
opposite fibres.

For the actual corrected exterior multiplier, harmonic recovery linearizes:

```text
G_eta+G_(-eta)=2G_0.                                    (S26.6)
```

If one common-gauge characteristic factor `W` and interval part `I` define
`E_eta=G_eta W-I`, then

```text
E_eta+E_(-eta)=2E_0,                                    (S26.7)

z^2(E_(-eta)-E_eta)=2eta W                              (S26.8)
```

off `z=0` and the Xi divisor for the last identity. Symmetric projection is exactly the
zero-shift exterior channel carrying the complete Xi pole obstruction. Antisymmetric projection
cancels both `I` and Xi, leaving an explicit shift-gauge term. Finite shift cannot cancel or move
the RH-bearing exterior poles. Combined with exterior pole tomography, this gives the exact
capstone

```text
RH <=> E_eta+E_(-eta) is analytic at every nonreal point, (S26.9)
```

for a common all-real characteristic member and common entire interval part.

This produces the corrected frontier:

```text
intrinsic schedule avoiding both erasing boundaries
  -> construct zero-shift fibre, or a common-gauge opposite pair (+eta,-eta)
  -> finite-Neumann annihilation before gauge formation
  -> common-gauge normality eliminating interior label overcrowding
  -> corrected exterior continuation for both paired channels
  -> symmetric projection E_eta+E_(-eta)=2E_0
  -> prove E_0 has no nonreal poles
  -> RH by exterior pole tomography.                    (S26.10)
```

The last producer statement is exactly what corpus cannot solve. It is equivalent to excluding
nonreal Xi zeros after source identification; it is not disguised progress bookkeeping. New
knowledge is the unique-odd classifier and exact paired projection, which delete the false
one-fibre anchored route and make a finite nonzero shift schedule compatible with Suzuki's actual
zero-shift target.

Paper proof and hostile audit:

- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-opposite-shift-parity-harmonic-recovery.md`

Exact Lean formalization:

- `formal/GaloisForLFunctions/RHTower/SuzukiOppositeShiftParityHarmonicRecovery.lean`

Key declarations are `suzukiShiftedXiTarget_neg`, `suzukiShiftedXiTarget_odd_iff`,
`suzukiShiftedXiTarget_opposite_harmonic_cross`,
`suzukiExteriorRemainder_opposite_average`, and
`riemannHypothesis_iff_suzukiExteriorRemainder_opposite_average_analytic_offReal`.

## 27. Distinct-channel cross-sewing and universal projective Xi-pole invariant

Section 26's common-characteristic exterior average is exact algebra but not yet Suzuki's actual
opposite source pair. Finite shifts are constructed from different resolvents and source
transforms. Neither source nor corpus identifies

```text
W_+=W_-,   I_+=I_-,   or   g_+=g_-.                    (S27.1)
```

Suzuki only expects shift-independence of characteristic zeros from a Hilbert-space isomorphism;
he explicitly leaves shift control to new arithmetic analysis. Treating `(S27.1)` as available
would therefore hide producer problem.

For genuinely distinct channels put

```text
E_eta(W,I)=G_eta W-I,

C_eta
 =W_-E_eta(W_+,I_+)+W_+E_(-eta)(W_-,I_-),              (S27.2)

P=2W_+W_-,
J=W_-I_+ + W_+I_-.                                     (S27.3)
```

Opposite multiplier law `G_eta+G_(-eta)=2G_0` gives pointwise, with no divisor exclusions,

```text
C_eta=E_0(P,J).                                         (S27.4)
```

This is cross-sewn replacement for common-channel average. If `W_+` and `W_-` are entire with
only real zeros, then `P` is entire with only real zeros; if interval terms are entire, so is `J`.
Thus existing exterior tomography applies directly to `(P,J)`.

Two unrelated pointwise gauges act by

```text
(W_+,I_+)->g_+(W_+,I_+),
(W_-,I_-)->g_-(W_-,I_-).
```

Exact covariance is

```text
C_eta -> g_+g_- C_eta,
P     -> g_+g_- P,
J     -> g_+g_- J.                                     (S27.5)
```

Therefore normalized channel

```text
N_eta=C_eta/P                                           (S27.6)
```

is invariant under two independent nonzero gauges. Away from characteristic divisors it obeys
stronger projective descent law

```text
N_eta
 =G_0-(1/2)(I_+/W_+ + I_-/W_-).                        (S27.7)
```

Explicit opposite shift has disappeared. Gauge matching and shift matching are both absent before
any cofinal limit.

The new analytic capstones are

```text
RH <=> C_eta is analytic at every nonreal point,         (S27.8)

RH <=> N_eta is analytic at every nonreal point.        (S27.9)
```

Second criterion is projectively intrinsic. More strongly, if `z` is hypothetical nonreal Xi
zero of arbitrary multiplicity `m`, then

```text
ord_z(C_eta)=-1,
TC_z(C_eta)=mP(z)/z^2,                                  (S27.10)

ord_z(N_eta)=-1,
TC_z(N_eta)=m/z^2.                                      (S27.11)
```

Equation `(S27.11)` is universal: independent of `eta`, both characteristic functions, both
interval terms, and both gauges. Opposite-channel cancellation cannot move, cancel, or renormalize
a nonreal Xi pole.

Subsequent source audit corrects proposed opposite-channel schedule. Suzuki requires real shift
`lambda<lambda_a`; simultaneous admissibility of `lambda,-lambda` is equivalent to
`|lambda|<lambda_a`, and existence of a nonzero pair is equivalent to `lambda_a>0`. Thus actual
opposite-channel availability can already import localized Weil/RH positivity. Cross-sewn algebra
and pole invariant remain correct, but `(S27.12)` is not an unconditional source schedule.
Section 28 replaces it with arbitrary two-shift affine sewing below every spectral floor.

Paper proof and hostile audit:

- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-opposite-shift-cross-sewn-exterior-product.md`

Exact Lean formalization:

- `formal/GaloisForLFunctions/RHTower/SuzukiOppositeShiftCrossSewnExterior.lean`

Key declarations are `suzukiCrossSewnExterior_eq_zeroShift`,
`suzukiCrossSewnNormalizedExterior_independentGauge`,
`suzukiCrossSewnNormalizedExterior_eq_zeroShift`,
`riemannHypothesis_iff_suzukiCrossSewnNormalizedExterior_analytic_offReal`, and
`meromorphicTrailingCoeffAt_suzukiCrossSewnNormalizedExterior`.

## 28. Arbitrary admissible two-shift sewing and canonical nonreal germ

The actual source constraint is

```text
lambda<lambda_a.                                       (S28.1)
```

The opposite schedule from Section 27 fails unconditionally:

```text
lambda<lambda_a and -lambda<lambda_a
  <=> |lambda|<lambda_a,

exists nonzero opposite pair <=> 0<lambda_a.           (S28.2)
```

In contrast, every real floor has two distinct admissible shifts, for example
`lambda_a-1` and `lambda_a-2`. Centering by `eta(lambda)=-i lambda` preserves distinctness. This
supplies two positive Suzuki source Hilbert spaces regardless of sign of restricted-Weil floor.

Let `alpha!=beta` be corresponding centered source parameters and let `gamma` be arbitrary; target
shift need not be source-admissible. For unrelated channels define

```text
E_eta(W,I)=G_eta W-I,

C_(alpha,beta->gamma)
 =(beta-gamma)W_beta E_alpha(W_alpha,I_alpha)
  -(alpha-gamma)W_alpha E_beta(W_beta,I_beta),          (S28.3)

P_(alpha,beta)=(beta-alpha)W_alpha W_beta,              (S28.4)

J_(alpha,beta->gamma)
 =(beta-gamma)W_beta I_alpha
  -(alpha-gamma)W_alpha I_beta.                         (S28.5)
```

Affine multiplier pencil obeys totalized Lagrange identity

```text
(beta-gamma)G_alpha-(alpha-gamma)G_beta
 =(beta-alpha)G_gamma.                                  (S28.6)
```

Hence pointwise, including `z=0` and Xi divisor,

```text
C_(alpha,beta->gamma)=E_gamma(P_(alpha,beta),
                              J_(alpha,beta->gamma)).   (S28.7)
```

In particular `gamma=0` reconstructs Suzuki's distinguished zero-shift exterior from two
same-side admissible sources even when zero shift itself is inadmissible. No positive floor,
opposite pair, common characteristic, common interval term, common gauge, or shift limit occurs.

Normalize by `P`:

```text
N_(alpha,beta->gamma)=C_(alpha,beta->gamma)/P_(alpha,beta).
```

Independent gauges on source lines cancel. Away from characteristic divisors,

```text
N_(alpha,beta->gamma)
 =G_gamma-Q_(alpha,beta->gamma),                        (S28.8)

Q_(alpha,beta->gamma)
 =[(beta-gamma)I_alpha/W_alpha
   -(alpha-gamma)I_beta/W_beta]/(beta-alpha).            (S28.9)
```

Strong new schedule-independence follows. For another distinct pair `(delta,epsilon)`,

```text
N_(alpha,beta->gamma)-N_(delta,epsilon->gamma)
 =Q_(delta,epsilon->gamma)-Q_(alpha,beta->gamma).       (S28.10)
```

If source characteristic functions are entire with only real zeros and interval terms are entire,
right side is analytic at every nonreal point. Therefore

```text
N_(alpha,beta->gamma) analytic at z
  <=> N_(delta,epsilon->gamma) analytic at z,
  Im z != 0.                                            (S28.11)
```

All arbitrary admissible source pairs define one canonical nonreal meromorphic germ modulo
holomorphic correction. In particular, shifts may move far negative with unknown `lambda_a`;
pair selection cannot change RH-bearing singularities. Suzuki's open shift-floor control and a
cofinal schedule `lambda->0` are removed from divisor detection.

Analytic and pole capstones are

```text
RH <=> C_(alpha,beta->gamma) analytic at every nonreal point,
                                                               (S28.12)
RH <=> N_(alpha,beta->gamma) analytic at every nonreal point.  (S28.13)
```

At hypothetical nonreal Xi zero `z` of arbitrary multiplicity `m`,

```text
ord_z C=-1,  TC_z C=mP(z)/z^2,
ord_z N=-1,  TC_z N=m/z^2.                              (S28.14)
```

Normalized pole is independent of source pair, target shift, both characteristics, interval
terms, and gauges. Opposite cross-sewing is recovered as specialization
`beta=-alpha`, `gamma=0`; for nonzero `alpha`, both raw exterior and characteristic acquire same
scalar `-alpha`, so normalized observables agree.

Actual frontier corpus cannot solve is now source-exact and shift-independent:

```text
choose any two actual shifts below each finite-aperture floor
  -> identify their corrected exterior channels independently of Xi quotient
  -> apply finite-Neumann clock annihilator before each gauge
  -> form affine-sewn projective observable N_(alpha,beta->0)
  -> prove its exterior continuation analytic at every nonreal point
  -> RH by (S28.13).                                    (S28.15)
```

This does not prove final continuation; by `(S28.13)` it is RH-equivalent after source
identification. Scientific progress is deletion of circular positive-floor/opposite-shift premise
and proof that all admissible pair choices share exactly same nonreal singular germ. Remaining
difficulty is genuine exterior continuation, not shift control or normalization.

Paper proof, hostile audit, and novelty boundary:

- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-admissible-two-shift-affine-sewing.md`

Exact Lean formalization:

- `formal/GaloisForLFunctions/RHTower/SuzukiAdmissibleTwoShiftAffineSewing.lean`

Key declarations are `exists_nonzero_opposite_suzuki_shifts_below_iff`,
`exists_distinct_centered_suzuki_shifts_below`,
`suzukiShiftedXiMultiplier_affine_interpolation`,
`suzukiAffineSewnExterior_eq_targetShift`,
`analyticAt_suzukiAffineSewnNormalizedExterior_pair_iff`,
`riemannHypothesis_iff_suzukiAffineSewnNormalizedExterior_analytic_offReal`, and
`meromorphicTrailingCoeffAt_suzukiAffineSewnNormalizedExterior`.

## 29. One-sided Carleman seam correction and actual exterior frontier

The multiplier used in Sections 24--28 requires a transform-category correction.  Suzuki's cited
2023 theorem states explicitly

```text
integral_0^infinity g(t)e^(izt)dt
 =z^(-2)xi'(1/2-iz)/xi(1/2-iz),       Im z>1/2,         (S29.1)
```

for the positive half-line after `g=-Psi`.  It is not a bilateral Fourier transform.  This is
also forced by parity: `g` is real and even, while the meromorphic function in `(S29.1)` is odd.
The 2026 Section 8.3 passage from the global convolution to `ghat*vhat` conflates these objects.

For compact source `v` on `[-a,a]`, put `h=g*v` and let `V` be its entire transform.  Exact Fubini
decomposition gives two entire convolution triangles `T_R,T_L` and

```text
M_+V=R+T_R,
M_-V=L+T_L,
T_R+T_L=I,                                              (S29.2)
```

where `R,L` are the physical right and left exterior transforms in their disjoint convergence
half-planes and `I` is the compact interval transform.  Evenness and the Xi functional equation
give the continuation law `M_-(z)=M_+(-z)=-M_+(z)`.  Hence

```text
R^c= MV-T_R,
L^c=-MV-T_L,                                           (S29.3)

R^c+L^c=-I,
R^c-L^c=2MV-(T_R-T_L).                                 (S29.4)
```

Equation `(S29.4)` is the decisive new source law.  Every Xi pole cancels automatically in the
bilateral exterior sum.  Therefore “prove the bilateral exterior continuation is holomorphic” is
not RH; it targets an identically pole-free combination.  Nonreal Xi poles live with opposite
residues on individual Carleman sheets.

The projected phase-one result gives `I_1=2A sin(az)`.  It cannot be the global multiplier channel:
the zero-shift multiplier and `W_1` are both odd, so their product is even, whereas a nonzero sine
clock is odd.  Lean proves this parity no-go unconditionally.

The corrected RH criterion is one-sided.  For one all-real Suzuki characteristic `W` and its
entire right triangle `T_R`, define

```text
E_R(z)=M_eta(z)W(z)-T_R(z).                             (S29.5)
```

Then centered Xi evenness and pole tomography give

```text
RH
 iff E_R is holomorphic for every Im z>0.               (S29.6)
```

Sections 27--28 survive after replacing every “global exterior remainder” by a selected right
Carleman sheet and every interval term by its right triangle.  Their affine sewing and projective
pole invariants are sheetwise algebra.  What does not survive is bilateral semantics.

Actual source frontier is therefore

```text
actual admissible compact deficiency source
 -> exact right convolution triangle T_R
 -> right sheet identity in Im z>1/2
 -> source-marked continuation through 0<Im z<=1/2
 -> RH by (S29.6).                                      (S29.7)
```

Abstract finite-aperture positivity cannot supply last continuation: rational FE--Schwarz orbit
insertion preserves that local shell while inserting a Carleman pole.  A proof must use the
distinguished Euler--Gamma marking and fail on the orbit-inserted countermodel.

Paper proof and hostile audit:

- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-one-sided-carleman-exterior-seam.md`

Exact Lean formalization:

- `formal/GaloisForLFunctions/RHTower/SuzukiOneSidedCarlemanSeam.lean`

Key declarations are `suzukiCarlemanSheet_sum`, `suzukiCarlemanSheet_difference`,
`suzukiShiftedXiMultiplier_neg`,
`suzukiZeroShiftBilateralMultiplierChannel_ne_projectedSineClock`, and
`riemannHypothesis_iff_suzukiRightCarlemanExterior_analytic_upper`.

## 30. Exact even-pole carrier of the phase-one right sheet

The one-sided frontier admits one further exact source reduction.  For the phase-one source,
Suzuki's interval-reflection involution exchanges the normalized deficiency lines.  After the
first-order spectral bracket, the effective compact source is odd.  Since the screw kernel is
even, its two physical convolution triangles obey

```text
T_L(z)=-T_R(-z).                                        (S30.1)
```

Together with `T_R+T_L=I_1` and the projected law `I_1(z)=2A sin(az)`, this gives

```text
(T_R)_odd(z)=(T_R(z)-T_R(-z))/2=A sin(az).              (S30.2)
```

At zero shift, both the one-sided Xi multiplier `M` and phase-one characteristic `W_1` are odd,
so `MW_1` is even.  Define the even Volterra carrier

```text
C_R(z)=M(z)W_1(z)-(T_R(z)+T_R(-z))/2.                   (S30.3)
```

The selected physical right sheet then has the exact decomposition

```text
E_R(z)=C_R(z)-A sin(az),                                (S30.4)
C_R(-z)=C_R(z).                                         (S30.5)
```

Thus the projected clock is not part of the unresolved Xi channel.  It is exactly the entire odd
half of the right sheet, with the opposite sign.  Every possible Xi pole lies in `C_R`, and

```text
RH
 iff C_R is holomorphic for every Im z>0.               (S30.6)
```

This reduces the unknown half of `T_R` from an arbitrary entire correction to its reflection-even
Volterra component.  It also closes two false continuations of Section 29:

1. Suzuki 2023 Section 10 proves unconditional mean-periodicity and a global Fourier--Carleman
   quotient, but that quotient is the same meromorphic `z^(-2) xi'/xi`; its Xi poles remain.
2. The projected sine clock controls only `(T_R)_odd`; it supplies no information about the even
   pole carrier `(S30.3)`.

The first Weyl producer fails a decisive parity test.  Since both `C_R` and `W_(-1)` are even and
Schwarz-real, `C_R/W_(-1)` is even and cannot be a nonconstant Herglotz function: positivity at
`z` and `-conjugate(z)` forces its imaginary part to vanish.  In particular it cannot have the
Donoghue normalization `m(i)=i`.

This no-go uniquely selects the odd phase-one denominator.  Define

```text
m_ext(z)=-C_R(z)/W_1(z)
        =-M(z)+(T_R)_even(z)/W_1(z).                    (S30.7)
```

Now `m_ext` is odd, as required for an even-measure Weyl function.  The exact live producer is the
source Gram identity

```text
K_ext(z,w)
 =(W_1(z) conjugate(C_R(w))-C_R(z) conjugate(W_1(w)))
   /(z-conjugate(w)) >= 0.                              (S30.8)
```

The nonvanishing `W_1` gauge turns `(S30.8)` exactly into the Pick kernel of `m_ext`.  Its Xi-pole
orientation is already correct: at every real Xi zero `gamma!=0` not shared by `W_1`,

```text
Res_gamma m_ext=-ord_gamma(XiC)/gamma^2<0.              (S30.9)
```

At a simple real zero `x` of `W_1` away from the Xi divisor, the remaining source residue is
`(T_R)_even(x)/W_1'(x)`.  Therefore exact next boundary theorem is the flux sign
`(T_R)_even(x)/W_1'(x)<=0` for every odd-extension eigenvalue, followed by full Gram identity
`(S30.8)`.  These statements are not assumed.  If proved from the restricted Euler--Gamma
operator, they make `m_ext` Herglotz, exclude nonreal poles of `C_R`, and prove RH by `(S30.6)`.
A rational FE--Schwarz orbit insertion preserves the local characteristic pair and sine clock but
inserts a pole into `C_R`, so any successful proof must visibly use Euler prime atoms and
Gamma/theta completion.

Paper proof, hostile audit, competing conjectures, and falsifiers:

- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-even-carleman-pole-carrier.md`

Exact Lean formalization:

- `formal/GaloisForLFunctions/RHTower/SuzukiCarlemanEvenPoleCarrier.lean`

Key declarations are `suzukiRightTriangle_oddPart_eq_half_interior`,
`suzukiEvenCarlemanPoleCarrier_even`,
`suzukiCarlemanRightSheet_eq_evenPoleCarrier_sub_halfInterior`,
`suzukiZeroShiftPhaseOneRightSheet_eq_evenPoleCarrier_sub_sine`, and
`riemannHypothesis_iff_suzukiEvenCarlemanPoleCarrier_analytic_upper`.  The Weyl-phase audit is
formalized by `even_schwarz_value_I_ne_I`, `suzukiPhaseOneExteriorWeylQuotient_odd`,
`suzukiExteriorWeylGram_eq_gauged_pick`, and
`meromorphicTrailingCoeffAt_suzukiPhaseOneExteriorWeylQuotient_of_XiC_zero`.

## 31. Admissible two-shift parity transfer and Carleman jump carrier

Section 30's zero-shift phase-one carrier is algebraically correct but is not automatically an
actual finite-aperture source: Suzuki requires every form shift to lie below the aperture spectral
floor, and zero need not do so.  The unconditional producer uses the existing arbitrary admissible
pair theorem.  Choose distinct `alpha,beta` below the floor and use their phase-one channels.  Each
characteristic and effective compact source is odd:

```text
W_eta(-z)=-W_eta(z),
L_eta(z)=-R_eta(-z).                                    (S31.1)
```

Sew to target zero:

```text
P=(beta-alpha)W_alpha W_beta,
J_R=beta W_beta R_alpha-alpha W_alpha R_beta,
J_L=beta W_beta L_alpha-alpha W_alpha L_beta.           (S31.2)
```

The two odd signs cancel inside each sewn term.  Consequently

```text
P(-z)=P(z),
J_L(z)=J_R(-z).                                         (S31.3)
```

The effective sewn characteristic/source is even.  Sewing also commutes exactly with the physical
triangle sum.  If the individual projected clocks are
`R_eta+L_eta=2A_eta sin(az)`, then

```text
J_R+J_L
 =2sin(az)[beta W_beta A_alpha-alpha W_alpha A_beta]
 =2(J_R)_even.                                          (S31.4)
```

Since the zero-shift multiplier `M_0` is odd and `P` is even, every Xi pole belongs to the odd
carrier

```text
C_odd=M_0P-(J_R)_odd.                                   (S31.5)
```

The actual admissible right sheet decomposes as

```text
E_R=M_0P-J_R=C_odd-(J_R+J_L)/2,                         (S31.6)
```

and the second term is entire.  Combining `(S31.6)` with the existing admissible affine-sewing
criterion gives the unconditional exact frontier

```text
RH iff C_odd is analytic at every nonreal point.         (S31.7)
```

There is one parity-independent physical invariant.  For any right/left triangle pair put

```text
C_jump=MW-(R-L)/2.                                      (S31.8)
```

Then

```text
2C_jump=E_R-E_L.                                        (S31.9)
```

Odd one-source reflection makes `C_jump` the even carrier of Section 30; even sewn reflection
makes it `C_odd`.  Thus the actual Weyl candidate is the normalized Carleman sheet jump

```text
m_ext=-C_odd/P=-(E_R-E_L)/(2P).                         (S31.10)
```

Away from the real characteristic divisor, `(S31.10)` is exactly minus the reflection-odd part of
the projectively normalized affine exterior observable already constructed in Section 28.  It is
odd.  At every Xi zero not shared by `P`, exact pole tomography gives

```text
TC_z(m_ext)=-ord_z(XiC)/z^2,                            (S31.11)
```

independently of both shifts, gauges, and triangles.  Real Xi poles therefore have the correct
negative Herglotz orientation.

Actual frontier corpus cannot solve is no longer source-shift selection, zero admissibility,
projected clock identification, carrier parity, or pole orientation.  It is the source Gram law

```text
K_jump(z,w)
 =(P(z)conj(C_odd(w))-C_odd(z)conj(P(w)))
   /(z-conj(w)) >= 0.                                   (S31.12)
```

Proving `(S31.12)` is not to be avoided: a proof from an independently positive Euler--Gamma
source colligation would prove RH by `(S31.7)`.  Its nonreal-pole exclusion closes the
RH-equivalent analyticity problem; full positivity may additionally impose real source-divisor
flux signs.  What would be circular is declaring `(S31.12)` positive after identifying it with
`XiC'/XiC`.

Canonical finite Donoghue positivity does not discharge `(S31.12)`.  Its poles lie on one finite
self-adjoint-extension divisor, whereas `(S31.10)` additionally carries the Xi divisor by
`(S31.11)`.  They are different fixed-aperture meromorphic functions.  Required new object is a
positive prime--Gamma dilation whose Weyl compression is the physical sheet jump.  Abstract
finite-aperture Hermite--Biehler data cannot produce it: functional-equation--Schwarz orbit
insertion preserves that local shell while inserting a nonreal jump pole.

**Active conjecture:** construct directly from Suzuki's prime-power and Gamma full-line screw
kernel a manifestly positive self-adjoint boundary colligation with scalar Weyl function
`m_ext`.  Its resolvent Gram identity would be `(S31.12)` and would finish RH.  Construction must
fail for orbit-inserted countermodels and establish positivity before using the Xi divisor.

Paper proof, hostile tests, and updated frontier:

- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-even-carleman-pole-carrier.md`

Exact Lean formalization remains in:

- `formal/GaloisForLFunctions/RHTower/SuzukiCarlemanEvenPoleCarrier.lean`

New capstones include `suzukiAffineSewnTriangle_reflection_of_odd`,
`suzukiAffineSewnRightTriangle_evenPart_eq_half_projectedSineClock`,
`riemannHypothesis_iff_suzukiAffineSewnOddCarlemanPoleCarrier_analytic_offReal`,
`two_mul_suzukiCarlemanJumpPoleCarrier_eq_sheet_difference`,
`suzukiAffineSewnExteriorWeylQuotient_eq_neg_oddPart_normalizedExterior`, and
`meromorphicTrailingCoeffAt_suzukiAffineSewnExteriorWeylQuotient_of_XiC_zero`.

## 32. Mandatory central pole and exact source-flux threshold

The jump-Pick conjecture has a decisive source-divisor test at the functional-equation fixed
point.  It is stronger than the nonzero-Xi pole-orientation test in Section 31 and uses no
estimate.  Assume the two actual odd source characteristics have simple central zeros.  Put

```text
a_alpha=W_alpha'(0),  a_beta=W_beta'(0),
r_alpha=R_alpha(0),   r_beta=R_beta(0).                 (S32.1)
```

The sewn characteristic and odd right-triangle component then have exact central jets

```text
P(z)/z^2
 -> (beta-alpha)a_alpha a_beta,                         (S32.2)

(J_R)_odd(z)/z
 -> beta a_beta r_alpha-alpha a_alpha r_beta.           (S32.3)
```

Define the source boundary flux

```text
Phi_(alpha,beta)
 =(beta a_beta r_alpha-alpha a_alpha r_beta)
   /((beta-alpha)a_alpha a_beta)
 =1/(beta-alpha)
   [beta r_alpha/a_alpha-alpha r_beta/a_beta].          (S32.4)
```

Since `XiC` is even and nonzero at zero,

```text
z M_0(z) -> XiC''(0)/XiC(0).                            (S32.5)
```

Substitution into the exact sheet-jump quotient gives the new residue split

```text
Res_0 m_ext
 =-XiC''(0)/XiC(0)+Phi_(alpha,beta).                    (S32.6)
```

The theta-cusp source already proves unconditionally

```text
XiC''(0)/XiC(0)<0.                                     (S32.7)
```

Every Herglotz function has nonpositive real residue at a real pole.  Indeed, along
`z=x+iy`, `Re[(z-x)m(z)]=-y Im m(z)<=0`, and the punctured residue limit preserves this closed
inequality.  Therefore any positive realization of the actual jump quotient must satisfy

```text
Re Phi_(alpha,beta)
 <= XiC''(0)/XiC(0) < 0.                               (S32.8)
```

This is the first exact source-flux threshold, not an RH-equivalent positivity declaration.  Its
left side contains only finite-aperture source derivatives and physical right-triangle values.
It says source flux must be strictly negative and must overcompensate the fixed positive term
`-XiC''(0)/XiC(0)`.  A colligation candidate with zero, nonnegative, or insufficiently negative
central flux is now killed locally before any global Gram argument.

Corpus cannot currently prove `(S32.8)`.  Projected sine clock fixes the even part of `J_R`; its
central first jet vanishes and says nothing about `(S32.3)`.  Canonical finite Donoghue positivity
also does not discharge it: `-i W_1/W_(-1)` uses the opposite divisor and is not the jump quotient.
Thus actual frontier has two ordered source tasks:

```text
prime-power/Gamma right-triangle construction
 -> prove central flux threshold (S32.8)
 -> prove full jump Gram kernel (S31.12)
 -> RH through (S31.7).                                 (S32.9)
```

Exact Lean formalization:

- `formal/GaloisForLFunctions/RHTower/SuzukiCarlemanCentralFlux.lean`

Key declarations are `residue_re_nonpos_of_upperHalfPlane_im_nonneg`,
`tendsto_z_mul_suzukiZeroShiftMultiplier`,
`tendsto_suzukiAffineSewnExteriorWeylQuotient`,
`suzukiAffineSewnCentralSourceFlux_re_le_XiC_curvature_of_herglotz`,
`XiC_secondDeriv_div_center_re_neg`, and
`suzukiAffineSewnCentralSourceFlux_re_neg_of_herglotz`.

## 33. Exact Neumann-channel cancellation: central frontier is purely Euler--Gamma

Section 32 still left open whether positivity of Suzuki's finite Neumann comparison channel could
force the source-flux threshold.  Exact triangle algebra now rules this out and removes that
channel from the frontier.

Let `nu_lambda` be the compact odd effective phase-one source with Fourier transform `W_lambda`,
and put `mu_j(lambda)=<nu_lambda,y^j>`.  The argument is valid for an integrable source or for the
compact distribution produced by the first-order spectral bracket.  Oddness and Fourier
differentiation give

```text
mu_0(lambda)=mu_2(lambda)=0,
W_lambda'(0)=i mu_1(lambda).                            (S33.1)
```

For the global Neumann representative `r_0(t)=-|t|/2`, the positive-half primitive is
`H_0(s)=-s^2/4`.  Hence its right triangle at the center is exactly

```text
T_(r0,R,lambda)(0)
 =-1/4 <nu_lambda,(a-y)^2>
 =(a/2)mu_1(lambda).                                   (S33.2)
```

Write the physical shifted kernel as `k_lambda=g-lambda r_0` and normalize central right-triangle
values by the characteristic jet:

```text
q_lambda=R_lambda(0)/W_lambda'(0),
q_lambda^EG=R_(g,lambda)(0)/W_lambda'(0).
```

Equations `(S33.1)--(S33.2)` give, without a limit or estimate,

```text
q_lambda=q_lambda^EG+i(a/2)lambda.                     (S33.3)
```

The central sewn flux is the affine chord intercept at target shift zero,

```text
Phi_(alpha,beta)
 =[beta q_alpha-alpha q_beta]/(beta-alpha).             (S33.4)
```

Affine interpolation annihilates every common linear-in-shift channel.  In particular the two
explicit Neumann terms in `(S33.3)` cancel:

```text
Phi_(alpha,beta)
 =[beta q_alpha^EG-alpha q_beta^EG]/(beta-alpha).       (S33.5)
```

This is a strict frontier advance.  Neumann positivity makes the two finite sources admissible,
but contributes zero to the mandatory Herglotz residue correction.  The source vectors still
depend on their shifts through the full restricted resolvent; only the direct comparison-kernel
boundary channel disappears.  Therefore actual unresolved theorem is now

```text
prove Re [beta q_alpha^EG-alpha q_beta^EG]/(beta-alpha)
        <= XiC''(0)/XiC(0)
from prime-power/Gamma source structure
 -> construct full Euler--Gamma jump Gram kernel (S31.12)
 -> RH.                                                 (S33.6)
```

Abstract finite-aperture positivity cannot prove first arrow: its only explicit positive
comparison channel is killed by `(S33.5)`.  A successful argument must expose a sign or Gram law
inside the unshifted Euler--Gamma edge triangles themselves and must fail for the corpus's
functional-equation--Schwarz orbit-inserted countermodels.

Lean formalization in
`formal/GaloisForLFunctions/RHTower/SuzukiCarlemanCentralFlux.lean` adds
`suzukiNeumannRightTriangleCentralMoment_of_odd`,
`suzukiNeumannRightTriangleCentralMoment_div_fourierFirstJet`,
`suzukiAffineSewnCentralSourceFlux_eq_normalized_intercept`, and
`suzukiAffineSewnCentralSourceFlux_linear_shift_channel_cancels`, with concrete specialization
`suzukiAffineSewnCentralSourceFlux_neumann_channel_cancels`.

## 34. One-sided coordinate phase reopens scalar jump positivity

Section 33 and the first phase audit mixed two different normalizations.  Suzuki 2023 proves for
`g=-Psi`

```text
int_0^infinity g(t)e^(izt)dt
 =z^(-2) xi'(1/2-iz)/xi(1/2-iz).                       (S34.1)
```

Since `XiC(z)=xi(1/2+iz)` is even, chain rule and functional equation give

```text
xi'(1/2-iz)=i XiC'(z),
M_phys,0(z)=i XiC'(z)/(z^2 XiC(z))=i G_0(z).           (S34.2)
```

This fixed `i` cannot be discarded while retaining physical triangle unchanged.  Real form shift
adds a second correction.  For `r_0(t)=-|t|/2`, its positive-half-line branch is `-t/2` and

```text
int_0^infinity r_0(t)e^(izt)dt=1/(2z^2).               (S34.3)
```

Therefore shifted physical multiplier and exact one-sided centered parameter are

```text
M_phys,lambda=iG_0-lambda/(2z^2)=iG_eta,
eta(lambda)=-i lambda/2.                               (S34.4)
```

Old `eta=-i lambda` is the full/bilateral projective symbol.  It is twice the right-sheet
coordinate.  Divisor algebra survives this rescaling, but source identification and central
phase do not.

Let `T_phys,lambda` be actual right Volterra triangle.  Exact physical and Xi-real normalized
sheets are

```text
E_phys,lambda=iG_eta W_lambda-T_phys,lambda,
E_norm,lambda=(-i)E_phys,lambda
             =G_eta W_lambda-I_norm,lambda,
I_norm,lambda=-iT_phys,lambda.                         (S34.5)
```

Thus every existing theorem written as `G_eta W-I` consumes `I_norm`, not physical triangle.
Source gauges scale `W` and `T_phys` together and cannot absorb relative phase in `(S34.5)`.

This repairs decisive source hostile test.  For real reflected deficiency vectors,

```text
W_lambda'(0) in R,
T_phys,lambda(0) in iR.                                (S34.6)
```

Physical normalized jet `q_phys=T_phys(0)/W'(0)` and its two-shift affine chord `Phi_phys` are
purely imaginary.  But flux in Xi-real Weyl quotient is

```text
q_norm=-i q_phys in R,
Phi_norm=-i Phi_phys,
Re Phi_norm=Im Phi_phys.                               (S34.7)
```

Hence quadrature does **not** force `Re Phi_norm=0`; prior scalar Herglotz no-go is retracted.  It
proved only that mixed expression `G_eta W-T_phys` is not Herglotz.  Correct Herglotz threshold is
the non-vacuous physical condition

```text
Im Phi_phys
 <= XiC''(0)/XiC(0)<0.                                (S34.8)
```

Neumann cancellation remains exact.  Section 33 physical law is still

```text
q_phys,lambda=q_phys,lambda^EG+i(a/2)lambda.           (S34.9)
```

After normalization,

```text
q_norm,lambda=q_norm,lambda^EG+(a/2)lambda.            (S34.10)
```

Affine chord annihilates this real linear term.  Expressed in exact one-sided coordinate
`eta=-i lambda/2`, normalized Neumann slope is `i a`, not `i a/2`.

Actual corpus frontier is reopened scalar source theorem:

```text
construct I_norm=-iT_phys directly from prime-power/Gamma half-line source
 -> prove Im Phi_phys<=XiC''(0)/XiC(0)
 -> prove normalized jump Pick kernel
 -> exclude every nonreal Xi pole
 -> RH.                                                (S34.11)
```

Positivity in `(S34.11)` is RH-bearing and is not to be avoided.  Circular move would be to infer
it after identifying quotient with Xi logarithmic derivative.  Required proof must construct a
positive prime--Gamma boundary colligation before divisor identification and must fail for
functional-equation--Schwarz orbit-inserted countermodels.

Centered Euler observable remains a parallel, unconditional RH detector:

```text
J[f](z)=z(zf'(z)-f(z)).                                (S34.12)
```

It removes central simple pole, preserves linear-escape invariance, and amplifies every nonzero
Xi pole.  One analytic source germ for `J[m_ext]` still proves RH, but no phase no-go forces this
route over restored scalar positivity.

Paper proof, retraction, and active conjectures:

- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-one-sided-coordinate-phase-normalization.md`
- `docs/drafts/pipeline/5-failed/suzuki-scalar-jump-herglotz-phase-no-go.md`
- `docs/drafts/pipeline/1-in-progress/suzuki-carleman-jump-euler-defect-weld.md`

Exact Lean formalization:

- `formal/GaloisForLFunctions/RHTower/SuzukiCarlemanCoordinatePhase.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiCarlemanJumpPhaseObstruction.lean`

Key new declarations are `suzukiOneSidedCenteredShiftParameter`,
`suzukiPhysicalRightCarlemanMultiplier_eq`,
`neg_I_mul_suzukiPhysicalRightCarlemanExterior`,
`suzukiWeylNormalizedCentralSourceFlux_eq_neg_I_mul_physical`,
`suzukiWeylNormalizedCentralSourceFlux_re_eq_physical_im`,
`suzukiWeylNormalizedCentralSourceFlux_im_eq_zero_of_source_quadrature`, and
`suzukiPhysicalCentralSourceFlux_im_le_XiC_curvature_of_normalized_herglotz`.

## 35. Correct-coordinate large-negative-shift cone obstruction

Coordinate repair does not rescue uniform scalar positivity.  Fix aperture `a>0`.  Suzuki's
deficiency vectors obey universal bounded-below resolvent limit

```text
(-lambda)(A_a-lambda)^(-1) -> I strongly,
lambda -> -infinity.                                  (S35.1)
```

For phase one, scaled effective source therefore tends distributionally to endpoint dipole

```text
(-lambda)nu_lambda
 -> i*2*cosh(a)*(delta_(-a)-delta_a).                 (S35.2)
```

Direct characteristic calculation cross-checks this:

```text
(-lambda)W_lambda(z) -> 4*cosh(a)*sin(a z),
(-lambda)W_lambda'(0) -> 4*a*cosh(a).                 (S35.3)
```

Writing `H_g(s)=integral_0^s g(t)dt`, physical triangle pairing and exact normalization
`q_norm=-i q_phys` give

```text
q_norm,lambda^EG -> H_g(2a)/(2a).                    (S35.4)
```

Affine sewing kills direct Neumann term.  On dyadic admissible pair `(-2L,-L)`, normalized
intercept is

```text
Phi_L=2*q_norm,-L^EG-q_norm,-2L^EG
     -> H_g(2a)/(2a).                                 (S35.5)
```

Since Suzuki kernel is continuous with `g(0)=0`, limit in `(S35.5)` approaches zero at small
aperture.  Corpus theorem gives `c_Xi=Re(XiC''(0)/XiC(0))<0`.  Thus sufficiently small `a` and
sufficiently large `L` force `Phi_L>c_Xi`, contradicting necessary Herglotz central-residue sign.

New theorem is correct-coordinate obstruction:

```text
uniform scalar jump positivity over all admissible shifts is false.
```

It does not kill source-selected scalar route.  It proves auxiliary shifts carry nonlinear source
information after Neumann cancellation.  Exact scalar frontier is construction of intrinsic pair
outside negative escape cone—likely in bounded window near spectral floor—followed by source-first
central threshold and full Pick kernel.  Parallel frontier remains one analytic prime--Gamma germ
for `J[m_ext]=z(z*m_ext'-m_ext)`, which existing exact pole law turns into RH.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-neumann-dominated-shift-cone-obstruction.md`.

Lean module:

- `formal/GaloisForLFunctions/RHTower/SuzukiLargeNegativeShiftCentralFlux.lean`.

Lean proves exact dyadic affine identity, convergence inheritance, and eventual Xi-curvature
violation from edge-jet limit.  Actual restricted-resolvent/triangle limit remains paper-level.
RH is not proved.

## 36. Shift-spectral chord mass: exact nonescaping selector

Section 35 kills uniform shift positivity but leaves an exact constructive question: what source
quantity distinguishes a viable bounded pair from the far-negative escape cone?  Corrected
one-sided phase makes normalized Euler--Gamma triangle jet real.  A candidate shift-variable
Weyl law is

```text
q_norm,lambda^EG
 =ell_a-integral 1/(t-lambda)dmu_a(t),
ell_a=H_g(2a)/(2a),      mu_a>=0.                      (S36.1)
```

Constant `ell_a` is forced by `(S35.4)`.  Earlier trial with constant `c_Xi` is false and is not
used.  For distinct shifts define

```text
K(t;alpha,beta)
 =(t-alpha-beta)/((t-alpha)(t-beta)).                  (S36.2)
```

Exact common-denominator identity is

```text
[beta/(t-alpha)-alpha/(t-beta)]/(beta-alpha)
 =K(t;alpha,beta).                                    (S36.3)
```

If `beta<0` and both shifts lie below `t`, then `K>0`, since
`t-alpha-beta=(t-alpha)+(-beta)>0`.  Affine sewing annihilates every common linear term, including
direct Neumann channel.  Thus finite positive shift-spectral colligation satisfies exactly

```text
Phi_norm(alpha,beta)
 =ell_a-sum_j w_j K(t_j;alpha,beta),                  (S36.4)

Phi_norm(alpha,beta)<=c_Xi
 iff
ell_a-c_Xi<=sum_j w_j K(t_j;alpha,beta).              (S36.5)
```

This is stronger than another necessary sign estimate: `(S36.5)` identifies complete missing
source currency and exact amount needed.  It also reproduces Section 35.  For dyadic pair
`(-2L,-L)`,

```text
K(t;-2L,-L)=(t+3L)/((t+2L)(t+L)) -> 0,               (S36.6)
```

so fixed spectral mass disappears and intercept returns to `ell_a>c_Xi`.  Viable selector must
retain chord mass at least `ell_a-c_Xi`; admissibility alone cannot.

Source conjecture `(S36.1)` is not imported from generic Donoghue theory.  Donoghue measure in
corpus lives in spectral variable `z` for `-iW_1/W_(-1)` and has wrong divisor.  Shift-variable
jet is ratio of cross resolvent matrix elements.  Put `R_lambda=(A_a-lambda)^(-1)` and

```text
h_a(x)=g(a-x)-H_g(a-x)+g(a+x)+H_g(a+x).               (S36.7)
```

Distributional integration by parts in actual compact phase-one source gives

```text
q_norm,lambda^EG=N_a(lambda)/D_a(lambda),
N_a(lambda)=<R_lambda e^x,h_a>,
D_a(lambda)=2<R_lambda e^x,1+x>.                      (S36.8)
```

Resolvent differentiation yields first exact falsifier for negative-Stieltjes conjecture:

```text
d q_norm,lambda^EG/dlambda
 = [<R_lambda^2 e^x,h_a>D_a(lambda)
    -N_a(lambda)2<R_lambda^2 e^x,1+x>]/D_a(lambda)^2. (S36.9)
```

Conjecture `(S36.1)` requires cross-Wronskian numerator in `(S36.9)` nonpositive and higher shift
derivatives to alternate.  This is actual corpus frontier now:

```text
prove shift-resolvent cross-Wronskian sign from prime--Gamma operator
 -> construct mu_a and source-selected pair satisfying chord-mass gap (S36.5)
 -> prove full normalized jump Pick kernel
 -> exclude nonreal Xi poles
 -> RH.                                                (S36.10)
```

If `(S36.9)` has wrong sign, retire Stieltjes realization immediately; exact chord theorem remains
the positive survivor and points to required signed/Krein replacement.  No zero-side positivity
or Xi divisor data may enter source proof.

Paper conjecture, derivation, and hostile audit:

- `docs/drafts/pipeline/1-in-progress/suzuki-negative-stieltjes-central-flux-colligation.md`.

Exact Lean formalization:

- `formal/GaloisForLFunctions/RHTower/SuzukiCarlemanStieltjesFlux.lean`.

Key declarations are `suzukiStieltjesChordKernel_eq_resolvent_affine_intercept`,
`suzukiStieltjesChordKernel_pos`,
`suzukiFiniteNegativeStieltjesJet_affine_intercept`,
`suzukiWeylNormalizedCentralSourceFlux_finiteNegativeStieltjes_eq`, and
`suzukiWeylNormalizedCentralSourceFlux_re_le_XiC_curvature_iff_spectralMass_gap`.

## 37. Spectral monotone-likelihood law produces negative-Stieltjes shift jet

Section 36 left cross-Wronskian sign `(S36.9)` as infinite derivative-style test.  It can be
replaced by one source-spectral order.  Let

```text
D(z)=sum_j w_j/(t_j-z),
N(z)=sum_j w_j*r_j/(t_j-z),
q(z)=N(z)/D(z),
w_j>0,
(r_j-r_k)*(t_j-t_k)>=0.                               (S37.1)
```

Because `D` is Herglotz, it has no upper-half-plane zero.  Exact symmetrization gives

```text
Im q(z)/Im z
 =-[1/(2*|D(z)|^2)]
   sum_(j,k) w_j*w_k*(r_j-r_k)*(t_j-t_k)
   /(|t_j-z|^2*|t_k-z|^2)
 <=0.                                                 (S37.2)
```

Hence `q` is anti-Pick in form-shift variable.  Its rational partial fractions are automatically

```text
q(z)=ell-sum_k nu_k/(sigma_k-z),
nu_k>=0,                                              (S37.3)
```

which is precise negative-Stieltjes law `(S36.1)`.  Measure version uses existing corpus
monotone-likelihood integration and exact identity

```text
K_lambda(x)^2*K_lambda(y)-K_lambda(y)^2*K_lambda(x)
 =(t_y-t_x)/[(t_x-lambda)^2*(t_y-lambda)^2].          (S37.4)
```

For actual source quotient `(S36.8)`, real eigenbasis `A_a phi_j=t_j phi_j` gives

```text
w_j=<e^x,phi_j><2*(1+x),phi_j>,
r_j=<h_a,phi_j>/<2*(1+x),phi_j>.                      (S37.5)
```

Thus entire shift-Weyl conjecture reduces to two concrete source laws

```text
w_j>=0,
(r_j-r_k)*(t_j-t_k)>=0.                               (S37.6)
```

This is forward progress: `(S37.6)` implies all real cross-Wronskian signs and complex anti-Pick
property at once.  It remains falsifiable mode by mode.  Ground-state positivity does not control
excited coefficients, and positivity-preserving restricted-Weil resolvent cannot be assumed.

Exact frontier:

```text
prove (S37.6) from prime--Gamma restricted operator
 -> obtain negative-Stieltjes source measure
 -> prove chord mass >=ell_a-c_Xi for selected pair
 -> prove full normalized jump Pick kernel in spectral variable
 -> RH.                                               (S37.7)
```

Failure of one coefficient sign retires monotone-ratio producer but leaves centered-Euler source
germ route.  RH is not proved.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-shift-spectral-monotone-likelihood-transfer.md`.

Lean module:

- `formal/GaloisForLFunctions/RHTower/SuzukiShiftSpectralMonotoneRatio.lean`.

Formal declarations:
`suzukiShiftResolventKernel_sq_cross_eq`,
`suzukiShiftSpectralMonotoneRatio_crossWronskian_nonpos`, and
`suzukiShiftSpectralMonotoneRatio_derivativeNumerator_nonpos`.

## 38. Asymmetric shift selection reduces central sign to one ground-edge average

Sections 35--37 still formulate central selection through a two-shift spectral mass gap.  Exact
affine algebra yields a strictly smaller representation-free target.  Fix one admissible shift
`beta` and send only other shift to `-L`.  For normalized Euler--Gamma jet `q`,

```text
Phi(-L,beta)
 =[beta q(-L)+L q(beta)]/(beta+L)
 =q(beta)+beta[q(-L)-q(beta)]/(beta+L).                (S38.1)
```

The source theorem `(S35.4)` gives finite limit `q(-L)->ell_a`, so

```text
Phi(-L,beta)->q(beta).                                (S38.2)
```

This is opposite of dyadic escape: pair `(-2L,-L)` loses source and tends to `ell_a`, while one
fixed/one-escaping pair retains exactly fixed source value.  Therefore single strict inequality

```text
q(beta)<c_Xi,
c_Xi=(XiC''(0)/XiC(0)).re,                            (S38.3)
```

implies `Phi(-L,beta)<c_Xi` for every sufficiently large `L`.  Central shift-selection problem is
now one-source, not two-source.  Negative-Stieltjes/chord-mass program remains useful sufficient
structure and likely relevant to full Pick kernel, but is no longer necessary to cross central
residue gate.

There is an exact source formula for fixed value.  With

```text
R_lambda=(A_a-lambda)^(-1),
h_a(x)=g(a-x)-H_g(a-x)+g(a+x)+H_g(a+x),               (S38.4)

q(lambda)
 =<R_lambda e^x,h_a> / (2<R_lambda e^x,1+x>).         (S38.5)
```

Suppose `A_a` has simple even ground state `phi_0` at floor `lambda_a`, with nonzero source
overlaps.  Resolvent pole dominance as `beta` approaches `lambda_a` from below gives

```text
q(beta)-><phi_0,h_a>/(2<phi_0,1+x>).                  (S38.6)
```

Parity removes both odd contributions: `<phi_0,x>=0`, and
`-H_g(a-x)+H_g(a+x)` is odd.  Reflection equates two remaining `g` terms.  Hence

```text
q(beta)->r_a
 :=<phi_0,g(a-x)>/<phi_0,1>.                          (S38.7)
```

For positive ground state, `r_a` is literal ground-state-weighted average of screw profile over
`[0,2a]`.  New source theorem sufficient for central Herglotz sign is therefore

```text
exists aperture a with simple positive even ground state and
<phi_0,g(a-x)>/<phi_0,1> < c_Xi.                      (S38.8)
```

Choose `beta` close enough to floor, then use `(S38.2)`.  At sufficiently small apertures,
Section 35 rules out far-negative dyadic schedule, but does not decide ground-edge average.
Every aperture remains testable through actual ground vector.  This is strictly more concrete
than “find a good pair”: it is one ground-vector prime--Gamma integral.

Result does not prove full jump Pick kernel or RH.  It removes Stieltjes representation from
central gate and isolates next source attack:

```text
prove ground screw-average inequality (S38.8)
 -> obtain central-valid asymmetric pairs by (S38.2)
 -> prove full normalized jump Pick kernel
 -> exclude every nonreal Xi pole
 -> RH.                                                (S38.9)
```

Lean formalization in `SuzukiCarlemanStieltjesFlux.lean` proves `(S38.1)--(S38.3)` as
`tendsto_suzukiRealAffineZeroIntercept_neg_atTop_fixed`,
`eventually_suzukiRealAffineZeroIntercept_lt_of_fixed_lt`, and
`eventually_suzukiRealAffineZeroIntercept_lt_XiC_curvature_of_fixed_lt`.
Ground-edge instantiation `(S38.6)--(S38.8)` remains paper-level until concrete restricted-Weil
operator and eigenvectors enter Lean.

## 39. Small aperture cannot satisfy ground selector; source collapses to Robin boundary data

Section 38 left every aperture nominally testable.  That is now corrected.  Suzuki's exact `g` is
continuous with `g(0)=0`, while corpus theorem gives

```text
c_Xi=(XiC''(0)/XiC(0)).re<0.                           (S39.1)
```

Continuity gives `delta>0` with `g(t)>c_Xi/2` for `|t|<delta`.  If `0<a<=delta/4` and
`x in [-a,a]`, then `0<=a-x<=2a<delta`; hence

```text
g(a-x)>c_Xi/2>c_Xi.                                   (S39.2)
```

Every nonzero nonnegative ground weight therefore satisfies

```text
<phi_0,g(a-x)>/<phi_0,1> > c_Xi.                      (S39.3)
```

Thus Section 38 target is impossible throughout all sufficiently small apertures, including only
range where Suzuki 2026 proves a positive simple even ground.  Earlier claim that small-aperture
ground edge remained open is superseded by `(S39.2)--(S39.3)`.

For an even positive weight, define symmetric profile

```text
s_a(x)=[g(a-x)+g(a+x)]/2,       0<=x<=a.              (S39.4)
```

Exact feasibility boundary is

```text
min s_a<c_Xi.                                          (S39.5)
```

If `(S39.5)` fails, no positive-even weight can cross.  If it holds, continuous positive-even test
weights can cross by localization, though actual ground mode still requires deficit-mass dominance.

More important, positivity is unnecessary for pole selector.  Let an even eigenmode satisfy

```text
-U_a''=lambda_a phi_a,
U_a(x)=integral_(-a)^a g(x-y)phi_a(y)dy,
M_a=integral_(-a)^a phi_a(y)dy.                        (S39.6)
```

Integration and evenness give

```text
-2U_a'(a)=lambda_a M_a,
r_a=U_a(a)/M_a=-lambda_a U_a(a)/(2U_a'(a)).            (S39.7)
```

After orientation `M_a>0`, required source theorem becomes one Robin crossing

```text
U_a(a)<c_Xi M_a.                                       (S39.8)
```

`[CONJECTURE: SUZUKI-ROBIN-CROSSING]` There exists a non-small aperture with simple even lowest
mode, `lambda_a M_a!=0`, satisfying `(S39.8)`.  This is compatible with known large-aperture
sign-indefinite geometry; it does not assume positivity-preserving resolvent.  Falsifiers are
`M_a=0`, odd/multiple ground, no symmetric-profile crossing, or a Robin flow that stays above
`c_Xi`.

Current exact frontier:

```text
prime--Gamma parity spectral flow -> (S39.8)
 -> asymmetric central-valid shift pair
 -> full normalized jump Pick kernel
 -> Euler-defect pole exclusion
 -> RH.                                                (S39.9)
```

Paper proof:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-ground-edge-aperture-robin-obstruction.md`.

Lean module:

- `formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeApertureObstruction.lean`.

Formal declarations include `exists_smallAperture_XiC_curvature_half_lt_suzukiGroundEdgeProfile`,
`suzukiGroundEdgeAverage_gt_XiC_curvature_of_half_lowerMoment`,
`suzukiGroundEdgeBoundaryRatio_eq_average_of_flux`, and
`suzukiGroundEdgeBoundaryRatio_lt_iff_boundaryMoment_lt`.

## 40. Unconditional screw-Cesaro curvature recurrence solves central shift selection

Section 39 made a non-small-aperture Robin crossing the apparent central frontier.  That ground
route is unnecessary.  Return to the far-negative dyadic selector, but choose aperture rather than
holding it in the small forbidden chamber.

Let `Psi` be Suzuki's unconditional screw profile, `g=-Psi`, and

```text
c_Xi=(XiC''(0)/XiC(0)).re.
```

Suzuki's multiplicity-exact zero expansion and centered Hadamard identity give

```text
Psi(t)=sum_gamma (1-cos(gamma t))/gamma^2,
c_Xi=-sum_gamma 1/gamma^2.                              (S40.1)
```

Thus the curvature-centered primitive is exactly

```text
h(A):=integral_0^A(g(t)-c_Xi)dt
     =sum_gamma sin(gamma A)/gamma^3.                   (S40.2)
```

`[PROVED HERE — LANDAU BOUNDARY OSCILLATION]` The function `h` changes sign in both directions
cofinally:

```text
for every A0, exists A-,A+>A0 with h(A-)<0<h(A+).       (S40.3)
```

Proof is unconditional and does not assume RH, simplicity, or rational independence.  Put
`F(s)=xi(1/2+s)` and `delta=sup_gamma |Im gamma|`.  Suzuki's one-sided transform gives

```text
Lh(s)
 =-F'(s)/(s^3 F(s))-c_Xi/s^2
 =sum_gamma 1/(gamma^2(s^2+gamma^2)).                   (S40.4)
```

The apparent singularity at zero is removable: `F` is even, the central Xi curvature ratio is
real, and
`(F'/F)'(0)=F''(0)/F(0)=-c_Xi`, so `F'/F+c_Xi s` vanishes to order at least three.  Reciprocal-cube
summability bounds `h(A)` by `C exp(delta A)`.  If `h` were eventually nonnegative, its translated
nonnegative tail would have Laplace convergence abscissa exactly `delta`: the upper bound follows
from exponential type, while every smaller abscissa would put one genuine pole `s=+-i gamma`
inside its holomorphy half-plane.  Yet `(S40.4)` is holomorphic at real `s=delta`, because
`xi(1/2+delta)!=0` for `0<=delta<=1/2`; at `delta=0` use the removable singularity.  This
contradicts Landau's nonnegative-Laplace boundary theorem.  Applying the same argument to `-h`
proves `(S40.3)`.  Supremum attainment is never used.

Dividing `(S40.3)` by positive aperture yields the new exact source theorem

```text
for arbitrarily large A,
 (1/A)integral_0^A g(t)dt<c_Xi,
and for arbitrarily large A,
 c_Xi<(1/A)integral_0^A g(t)dt.                         (S40.5)
```

Choose one negative crossing with `A=2a`.  Section 35 source asymptotic then gives

```text
q_a(lambda)->ell_a:=(1/(2a))integral_0^(2a)g(t)dt<c_Xi,
2q_a(-L)-q_a(-2L)->ell_a.                              (S40.6)
```

Consequently every sufficiently large finite `L` supplies two actual admissible shifts whose
affine-sewn central source flux has the strict required Herglotz residue sign.  These shifts remain
far from the spectral floor, so Section 37 Cayley-universality obstruction does not apply.  This
is why a condition “whose positivity is RH itself” is not avoided: once a source identity proves
that condition it is a valid RH proof.  What is avoided is assuming it.  Here central positivity
is derived from independent divisor/Laplace structure.

Central residue sign, aperture existence, and shift existence are therefore closed.  Actual
frontier corpus cannot solve is now narrower and full-frequency:

```text
fix one aperture and finite dyadic pair supplied by (S40.6)
 -> prove actual normalized Euler--Gamma jump quotient is Herglotz/Pick on C_+
 -> its nonreal Xi poles are impossible by existing pole theorem
 -> RH.                                                (S40.7)
```

Corpus has neither the required prime--Gamma Gram factorization nor a source counterexample for
this selected pair.  More central estimates, ground-state inequalities, or shift searches are no
longer frontier work.  Next experiment must attack the full Pick matrix, beginning with exact
two-frequency determinant of the actual selected Euler--Gamma triangles and testing whether its
defect factors through an already-positive restricted-Weil form.

Paper proof and audit:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-screw-cesaro-curvature-recurrence.md`.

Lean module:

- `formal/GaloisForLFunctions/RHTower/SuzukiScrewCesaroCurvatureRecurrence.lean`.

Formal declarations include `suzukiCurvatureCenteredPrimitive_eq`,
`suzukiScrewCesaroMean_lt_iff_centeredPrimitive_neg`,
`cofinallyCrosses_suzukiScrewCesaroMean_iff_centeredPrimitive`,
`eventually_suzukiDyadicNegativeShiftIntercept_lt`,
`xiSuzukiScrewCesaroCrossing_selects_dyadicCentralFlux`, and
`not_ae_nonneg_of_landau_complexMGF_nonintegrable`.

Primary-source boundary: Suzuki 2023 supplies `(S40.1)` and one-sided transform but only discusses
pointwise `liminf Psi` under RH plus simplicity and rational independence; Suzuki 2026 supplies the
finite-aperture setting.  Targeted searches found no screw-Cesaro curvature recurrence parent.
Priority remains unverified rather than claimed.

## 41. Full jump Pick problem is an exact Loewner growth-versus-deficit law

Section 40 closes central shift selection.  Full jump kernel can now be decomposed without further
asymptotics.  For real `alpha<beta<0`, define actual reflection-odd source response

```text
q_lambda(z)=Odd_z[R_lambda(z)/W_lambda(z)].             (S41.1)
```

Direct expansion of sewn characteristic, triangle, and odd carrier proves

```text
m_ext(z)
 =-M_0(z)+[beta q_alpha(z)-alpha q_beta(z)]/(beta-alpha). (S41.2)
```

For scalar Pick kernel `K_f(z,w)=[f(z)-conj(f(w))]/[z-conj(w)]`, real affinity gives

```text
K_jump
 =-K_0+[beta H_alpha-alpha H_beta]/(beta-alpha),        (S41.3)
H_lambda=K_(q_lambda),  K_0=K_(M_0).                   (S41.4)
```

Evaluate on arbitrary finite node/coefficient vector `v`.  Exact algebra yields

```text
v* K_jump v>=0
iff
(-alpha)[H_beta(v)-H_alpha(v)]
 >=(beta-alpha)[K_0(v)-H_alpha(v)].                    (S41.5)
```

Therefore full Pick positivity is equivalent to Loewner inequality

```text
(-alpha)(H_beta-H_alpha)
 >=_L (beta-alpha)(K_0-H_alpha).                       (S41.6)
```

This is not another estimate or sufficient abstraction.  It is exact matrix form of actual
Carleman jump Gram law.  Negative shifts have extrapolation factor
`-alpha/(beta-alpha)>1`; source growth must pay entire Xi-multiplier deficit.  At selected dyadic
pair `alpha=-2L,beta=-L`, condition becomes

```text
2(H_(-L)-H_(-2L)) >=_L K_0-H_(-2L).                   (S41.7)
```

`[CONJECTURE: SUZUKI-LOEWNER-GROWTH]` One aperture/pair from Section 40 satisfies `(S41.6)` on
all finite upper-half-plane node sets.  Proposed producer is source-before-divisor square

```text
(-alpha)(H_beta-H_alpha)-(beta-alpha)(K_0-H_alpha)
 =B_(alpha,beta)^*B_(alpha,beta),                      (S41.8)
```

derived from restricted resolvent identity
`R_beta-R_alpha=(beta-alpha)R_beta R_alpha` plus reflected prime-power/Gamma triangle.  Any
negative two-frequency determinant kills square producer.  Finite Donoghue positivity cannot
replace it because divisor is wrong; central sign tests only one asymptotic vector.

Actual frontier corpus cannot solve is now exactly `(S41.6)`, not shift selection:

```text
prime--Gamma resolvent square -> SUZUKI-LOEWNER-GROWTH
 -> full jump Pick kernel
 -> nonreal Xi poles excluded
 -> RH.                                                (S41.9)
```

Paper proof:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-jump-kernel-loewner-growth-gap.md`.

Active conjecture:

- `docs/drafts/pipeline/1-in-progress/suzuki-jump-kernel-loewner-growth.md`.

Lean module:

- `formal/GaloisForLFunctions/RHTower/SuzukiJumpKernelLoewnerGap.lean`.

Formal declarations include `suzukiAffineSewnExteriorWeylQuotient_eq_jumpWeylCandidate`,
`suzukiScalarPickKernel_affineSewnExteriorWeylQuotient`, and
`suzukiAffineKernelGap_nonneg_iff_loewnerGrowth`.

## 42. Full-frequency Neumann cancellation is false; exact holonomy survives

The first square producer after `(S41.8)` proposed discarding the direct Neumann comparison
channel because Section 33 proves it cancels from central affine flux.  That extrapolation from one
Laurent coefficient to the whole spectral function is false.

Fix aperture `a` and an odd compact source distribution `nu`, with characteristic

```text
W(z)=<nu,e^(iz·)>.
```

For `r_0(t)=-|t|/2`, let `T_R,T_L` be the right/left compact triangles and put `I=-iT_R` in the
canonical Xi-real coordinate.  Oddness gives zero source mass.  More importantly,

```text
sgn(x-y)r_0(x-y)=-(x-y)/2,                              (S42.1)
```

so the right-minus-left spatial response is the constant half first moment of `nu`.  Fourier
transformation and `W'(0)=i<nu,y>` give the exact normalized reflection-odd response

```text
n_(a,W)(z):=Odd_z[I(z)/W(z)]
 =-W'(0)sin(az)/(2zW(z)).                               (S42.2)
```

For each form shift split the full response into Euler--Gamma and explicit Neumann pieces,

```text
q_lambda=q_lambda^EG-lambda n_(a,W_lambda).             (S42.3)
```

Substitution into affine sewing proves

```text
[beta q_alpha-alpha q_beta]/(beta-alpha)
 =[beta q_alpha^EG-alpha q_beta^EG]/(beta-alpha)
  +N_(alpha,beta),                                      (S42.4)

N_(alpha,beta)(z)
 =alpha beta sin(az)/(2z(beta-alpha))
   [W_alpha'(0)/W_alpha(z)-W_beta'(0)/W_beta(z)].       (S42.5)
```

Thus full cancellation would require equality of projectively normalized characteristics
`W_alpha/W_alpha'(0)=W_beta/W_beta'(0)`.  Actual finite resolvent shift is projectively non-flat;
the corpus already has its reflected-tangent certificate.

There is no contradiction with the central theorem.  Every simple odd characteristic satisfies

```text
n_(a,W)(z)=-a/(2z)+O(z).                                (S42.6)
```

The universal pole cancels from `n_beta-n_alpha`, but its centered higher-frequency part does not.
Writing `W(z)=dz+ez^3+O(z^5)`, the first survivor is

```text
N_(alpha,beta)(z)
 =alpha beta a/[2(beta-alpha)]
   [e_beta/d_beta-e_alpha/d_alpha]z+O(z^3).             (S42.7)
```

Normalized cubic characteristic curvature is therefore the first comparison-channel observable
missed by central residue.

The second resolvent identity makes the correction constructive rather than merely obstructive.
In common gauge

```text
W_beta=W_alpha+(beta-alpha)J,
W_beta'(0)=d_alpha+(beta-alpha)J'(0),                   (S42.8)
```

one has

```text
N_(alpha,beta)(z)
 =alpha beta sin(az)/(2z)
  [d_alpha J(z)-J'(0)W_alpha(z)]
  /[W_alpha(z)W_beta(z)].                               (S42.9)
```

Bracket in `(S42.9)` is exact centered projective tangent.  It is the positive survivor of the
failed prime--Gamma-only square.

There is a second, stronger conclusion.  Put `epsilon=1/L` and normalize the far-negative
phase-one characteristic by its central jet.  Strong source expansion gives

```text
What_epsilon=What_0+epsilon dotWhat_0+o(epsilon),
What_0(z)=sin(az)/a.                                    (S42.9a)
```

The dyadic correction therefore has locally uniform meromorphic limit

```text
N_L(z)
 =L sin(az)/z[1/What_(1/(2L))(z)-1/What_(1/L)(z)]

 ->N_infty(z)
 =a^2 dotWhat_0(z)/[2z sin(az)].                        (S42.9b)
```

This limit is not identically zero.  If the centered phase-one tangent vanished, then for a real
constant `c`, the effective characteristic of `f=A_a e^x-c e^x` would vanish.  Inverse Fourier
transformation forces `f_odd=(f_even)'`.  But Suzuki's exact finite-part endpoint law gives

```text
f_odd=-(1/2)sinh(x)log(a^2-x^2)+O(1),
(f_even)'=f_odd+x cosh(x)/(a^2-x^2)+O(1),               (S42.9c)
```

which is impossible at `a-`.  Thus the large-negative lever arm converts an `O(1/L)` projective
shift into a genuinely nonzero order-one full-frequency response.  Far-negative escape destroys
only central Neumann information; it preserves the arithmetic projective tangent.

Consequently current RH frontier is corrected to

```text
K_jump=K_(m_EG)+K_(N_(alpha,beta)),                    (S42.10)

prove K_(m_EG)+K_(N_(alpha,beta))=B^*B
 -> full jump Pick positivity
 -> no nonreal Xi pole
 -> RH.                                                (S42.11)
```

No sign is claimed for `K_(N)` separately.  New mechanism is compensation: Euler--Gamma
resolvent curvature and Neumann projective holonomy must close together.  Any future derivation
that drops `(S42.5)` is falsified even if its central residue is correct.

Paper theorem and hostile audit:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-full-frequency-neumann-holonomy-survivor.md`.
- `docs/drafts/pipeline/5-failed/suzuki-prime-gamma-only-jump-square.md`.

Corrected active conjecture:

- `docs/drafts/pipeline/1-in-progress/suzuki-jump-kernel-loewner-growth.md`.

Lean module:

- `formal/GaloisForLFunctions/RHTower/SuzukiFullFrequencyNeumannHolonomy.lean`.

Formal declarations include `sign_mul_suzukiNeumannKernel`,
`suzukiRealAffineSourceFunction_shiftedNeumann`,
`suzukiNeumannHolonomyCorrection_eq_projectiveCross`,
`suzukiNeumannHolonomyCorrection_finiteUpdate`, and
`suzukiScalarPickKernel_jumpWeylCandidate_shiftedNeumann`.  It also proves
`tendsto_suzukiDyadicReciprocalSecant`, the exact derivative limit that amplifies dyadic reciprocal
motion with factor `1/2`.  Lean closes exact algebraic and Pick
layers; compact-distribution triangle-to-response passage `(S42.1)--(S42.2)` remains paper-proved.

## S43. Affine resolvent sewing has exact Krein sign, not positive-square sign (2026-07-22)

The remaining claim that second resolvent identity itself produces compensated `B^*B` fails a
direct finite spectral hostile test.  For

```text
R_lambda(t)=1/(t-lambda),
E_(alpha,beta)(t)=[beta R_alpha(t)-alpha R_beta(t)]/(beta-alpha),
```

exact identity is

```text
R_0(t)-E_(alpha,beta)(t)
=alpha beta/[t(t-alpha)(t-beta)].                       (S43.1)
```

When `alpha<beta<0<` spectral-shift denominators and `t!=0`, right side has sign `t`.  Hence
negative-Stieltjes orientation yields signed diagonal form

```text
Q(c)=sum_(t_j>0)|c_j|^2 omega_j
     -sum_(t_j<0)|c_j|^2 omega_j,   omega_j>0.          (S43.2)
```

Negative index is exact count of negative restricted-Weil spectral coordinates in minimal model.
Bare resolvent algebra cannot yield universal Hilbert square when one negative node exists.

Against global target `g`, local/global correction `C_g=-R_0-g` satisfies sharp identity

```text
G_g(t)=D_(alpha,beta)(t)+C_g(t),
G_g(t)>=0 iff C_g(t)>=-D_(alpha,beta)(t).               (S43.3)
```

Thus every negative node imposes explicit positive completion debt `omega_j`.  Correct active
conjecture is `SUZUKI-GLOBAL-LOCAL-KREIN-WELD`: coupled reflected Euler--Gamma triangles and exact
Neumann projective holonomy must pay this negative part, source-before-divisor, while global Xi
multiplier remains intact.  This is now exact frontier toward RH; it is not proved.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-affine-resolvent-krein-defect.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiAffineResolventKreinDefect.lean`.

## S44. Xi-real/FE bipolarization fixes unique minimal Krein completion (2026-07-22)

S43 left completion direction and amount unspecified.  Corpus already has two fixed operations on
real weld-generator plane: Xi-real quarter-turn `J` and FE coefficient reflection `R`.  For weld
area `Omega_theta`, define

```text
P_theta(x,y)=Omega_theta(x,Jy),
K_theta(x,y)=Omega_theta(x,Ry),
Q+_theta=(P_theta+K_theta)/2,
Q-_theta=(P_theta-K_theta)/2.                          (S44.1)
```

Direct algebra gives

```text
Q+_theta(x,y)=theta/2 (x1+x2)(y1+y2),
Q-_theta(x,y)=theta/2 (x1-x2)(y1-y2),
K_theta=Q+_theta-Q-_theta,
K_theta+Q-_theta=Q+_theta>=0.                          (S44.2)
```

Variable completion rate `kappa` has sharp law

```text
K_theta(x,x)+Q-_kappa(x,x)
=theta/2 (x1+x2)^2+(kappa-theta)/2 (x1-x2)^2,

[nonnegative for every x] iff theta>=0 and kappa>=theta. (S44.3)
```

Necessity follows by testing `(1,1)` and `(1,-1)`; sufficiency is literal square positivity.  At
negative S43 node, unique minimal rate is

```text
theta(t)=-D_(alpha,beta)(t)>0.                         (S44.4)
```

No arbitrary `B_a` remains locally.  Completion amount is exact debt, direction is negative FE
light line, and completed residual is positive light square.  Moreover

```text
J R=-R J,
((J+R)/2)^2=0,
((J-R)/2)^2=0.                                        (S44.5)
```

Thus both light squares are area twists by fixed rank-one square-zero operators, matching required
algebraic shape of one-sided Carleman triangles.

Actual unresolved RH-bearing statement is now
`SUZUKI-XIREAL-FE-BIPOLARIZATION-WELD`: prove common-gauge reflected Euler--Gamma triangles plus
full-frequency Neumann holonomy realize `(J-R)/2` completion channel with coefficient at least
`-D(t)` coherently on every finite node set, without Xi-divisor insertion.  This source identity is
strictly stronger and more falsifiable than saying whose positivity is RH: operators, direction,
and exact threshold are fixed before any Xi zero is inspected.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-xireal-fe-bipolarization-completion.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiXiRealFEBipolarizationCompletion.lean`.

## S44. Negative-block Schur reduction and holonomy tax (2026-07-22)

Diagonal cancellation in S43 is insufficient when Neumann projective holonomy couples spectral
sign sectors.  Exact two-channel completion law is

```text
a x^2+2bxy+(c-n)y^2>=0 for all x,y
iff c>=n+b^2/a,                    a>0.                  (S44.1)
```

Here `n` is explicit negative affine-resolvent debt and `b^2/a` is strict Schur holonomy tax.
Full block version at fixed aperture is

```text
C_---N-C_-+(P+C_++)^(-1)C_+- >=0.                       (S44.2)
```

Restricted-Weil negative subspace is finite-dimensional at every aperture, so full-frequency
source problem reduces to finite Schur complement `(S44.2)`.  Correct conjecture is
`SUZUKI-FINITE-NEGATIVE-BLOCK-WELD`: reflected Euler--Gamma diagonal completion must dominate both
negative debt and projective cross tax.  Presence of holonomy alone does not help; purely
off-diagonal holonomy worsens required completion.

Paper theorem:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-krein-schur-holonomy-tax.md`.

Scalar exact law is formalized in `SuzukiAffineResolventKreinDefect.lean`.  Source block inequality
`(S44.2)` remains unproved and RH-bearing.

## S45. Unique coherent negative-projector completion (2026-07-22)

Cross-node assembly of local Xi-real/FE completion has canonical source-spectral solution.  For
restricted-Weil operator `A` and two admissible negative shifts,

```text
D=sgn(A)W,
W=alpha beta |A|^(-1)(A-alpha)^(-1)(A-beta)^(-1)>=0.    (S45.1)
```

Unique minimal commuting correction is `D_-=P_-W`.  For evaluation vectors `Gamma(z)` its complete
finite-node kernel is

```text
K_-(z,w)=<W^(1/2)P_-Gamma(w),W^(1/2)P_-Gamma(z)>.       (S45.2)
```

This Gram kernel is positive and finite rank at fixed aperture; `K_D+K_-=K_(P_+W)>=0`.  Correct
source conjecture is now `SUZUKI-NEGATIVE-PROJECTOR-TRIANGLE-IDENTITY`: actual reflected
Euler--Gamma plus Neumann correction equals `(S45.2)` plus a positive kernel in fixed
Xi-real/FE negative-light direction.  Any cross-sector holonomy must instead satisfy S44 Schur-tax
inequality.

Paper:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-negative-projector-coherent-completion.md`.

Unproved step is analytic identification of concrete source triangle map with `(S45.2)`; proving
it closes jump positivity and RH.

## S46. Finite-Morse resolvent-jet completion replaces discontinuous projector (2026-07-22)

S45 fixed minimal completion but left source representation as weighted spectral projector.  At
fixed aperture `A_a` has finitely many distinct negative eigenvalues
`lambda_1,...,lambda_k`.  Fix `rho<inf spec(A_a)` and set

```text
r_j=1/(lambda_j-rho),
w_j=-D_(alpha,beta)(lambda_j)>0,
ell_j(x)=(x/r_j) product_(m!=j)(x-r_m)/(r_j-r_m),
p_a(x)=sum_j sqrt(w_j) ell_j(x).                       (S46.1)
```

Exact finite-Morse theorem gives

```text
p_a(0)=0,                  p_a(r_j)^2=w_j,
D+p_a((A_a-rho I)^(-1))^2 >=0,
p_a(R_rho)^2=D_-+P_+p_a(R_rho)^2 >=D_-.               (S46.2)
```

Completion is compact and source-native because it is finite jet of one admissible resolvent:

```text
p_a(R_rho)=sum_(n=1)^k c_n R_rho^n
           =sum_(n=1)^k c_n/(n-1)! partial_rho^(n-1)R_rho. (S46.3)
```

This representation cannot be made exactly minimal by finite polynomial.  Positive eigenvalues
give infinitely many distinct resolvent nodes accumulating at zero.  If polynomial square
vanished on all of them, polynomial would be zero and could not pay any `w_j>0`.  Thus positive
tail in `(S46.2)` is forced, not artifact.

Actual frontier corpus still cannot solve is now the concrete source inequality
`SUZUKI-FINITE-MORSE-RESOLVENT-JET-DOMINATION`:

```text
K_completion^src(z,w)
-<p_a(R_rho)Gamma(w),p_a(R_rho)Gamma(z)> >=0           (S46.4)
```

for one recurrence-selected aperture and admissible negative shift pair, on every finite
upper-half-plane node set in common characteristic gauge.  This is stronger than negative-block
diagonal matching: full Loewner remainder in `(S46.4)` must absorb Neumann cross-sector Schur tax.
It is source-before-divisor; coefficients use only explicit `A_a` spectrum, never Xi zeros.
Rational FE--Schwarz orbit insertion preserves local spectral data but inserts global pole, so it
must violate `(S46.4)` and prevents deriving it from abstract spectral calculus alone.

If `(S46.4)` is proved, `(S46.2)` makes full sewn jump Pick kernel positive; existing pole
tomography then excludes every nonreal Xi zero and proves RH.  RH is not proved here: missing step
is actual reflected Euler--Gamma/Neumann mixed-node domination `(S46.4)`.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-finite-morse-resolvent-jet-completion.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiFiniteMorseResolventJetCompletion.lean`.

## S47. Actual quotient is homogeneous Plücker blade; linear projector producer fails (2026-07-22)

S45--S46 solve a linear affine-resolvent completion problem, but actual Suzuki response is ratio
of two boundary observations of same shifted source:

```text
q_lambda(z)=N_z(u_lambda)/D_z(u_lambda),
u_lambda=(A-lambda)^(-1)e.
```

Rank-one hostile test is decisive.  On invariant spectral line, numerator and denominator acquire
same factor `(t-lambda)^(-1)`, so Euler--Gamma quotient is shift-flat even when `t<0`.  Linear
negative projector debt is nonzero there.  Hence weighted projector and finite-Morse square cannot
be canonical correction of actual projective motion.

For `v=(A-alpha)^(-1)(A-beta)^(-1)e`, exact replacement is

```text
U_beta wedge U_alpha
=(beta-alpha)(v,0) wedge (Av,1).                       (S47.1)
```

`V wedge V` component is Euler--Gamma spectral-pair curvature; `V wedge 1` component is affine
Neumann/projective holonomy.  On two spectral modes,

```text
[B,D](v,Av)
=(t_j-t_i)v_i v_j(b_i d_j-b_j d_i).                   (S47.2)
```

Source sign lives on spectral-pair Plücker orientation, not sign of individual eigenvalue.
Current representation is therefore homogeneous exterior square, not negative projector plus
Schur tax.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-homogeneous-projective-resolvent-plucker-lift.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiProjectiveResolventPluckerLift.lean`.

## S48. One-resolvent jets tomographically generate complete homogeneous blade space (2026-07-22)

Let finite simple block have `Ae_i=t_i e_i` and cyclic source `e=sum_i a_i e_i`, `a_i!=0`.  Fix
`rho` below spectrum and `R=(A-rho)^(-1)`.  Zero-constant cardinal polynomials

```text
q_i(x)=x/(a_i r_i) product_(m!=i)(x-r_m)/(r_i-r_m),
r_i=(t_i-rho)^(-1),                                   (S48.1)
```

satisfy `q_i(R)e=e_i`.  Thus all filters are finite positive powers of one admissible resolvent,
equivalently finite shift jets.

For actual homogeneous carrier `H(v)=(v,0) wedge (Av,1)`, exact laws are

```text
H(e_i)=e_i wedge infinity,
H(e_i+e_j)-H(e_i)-H(e_j)
  =(t_j-t_i)e_i wedge e_j.                            (S48.2)
```

These `n+n(n-1)/2` source-generated blades form a basis of
`wedge^2(V direct_sum R)`.  Rank one retains only Neumann homogeneous coordinate; every
Euler--Gamma direction first occurs on spectral pair with exact gap.  Repeated eigenvalues and
zero source coordinates are sharp tomography failures.

Actual frontier research corpus cannot solve is now
`SUZUKI-PLUCKER-CD-MATRIX-GRAM`: for one recurrence-selected aperture/shifts, derive division-free
prime--Gamma Christoffel--Darboux/Green identity factoring full polarized boundary matrix on basis
`(S48.2)` as positive Gram kernel.  Spanning alone does not prove positivity; it makes every bad
direction observable.  One negative principal minor refutes universal producer.  Positive Gram
factorization yields exact Loewner growth, jump Pick positivity, pole exclusion, and RH.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-resolvent-jet-homogeneous-plucker-tomography.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiResolventJetHomogeneousPluckerTomography.lean`.

RH is not proved.  Exact unsolved scientific step is source boundary matrix factorization, not
more affine-resolvent estimates or one-mode completion.

## S49. Weighted affine sewing requires marked secant tensor, not Plücker chord alone (2026-07-22)

S47 controls projective chord `q_beta-q_alpha`.  Actual jump response uses weighted affine
intercept

```text
I_(alpha,beta)q=[beta q_alpha-alpha q_beta]/(beta-alpha). (S49.1)
```

Plücker-only producer fails exact gauge test.  Replace numerator boundary observation by
`B_delta=B+delta D`.  Every minor `B wedge D` is unchanged, while each `q_lambda` and `(S49.1)`
increase by `delta`.  Exterior blade forgets affine chart which jump sewing retains.

Let

```text
u_alpha=Av-beta v,       u_beta=Av-alpha v,
x=B(v), X=B(Av), y=D(v), Y=D(Av),
n_lambda=B(u_lambda)+c.
```

Exact division-free theorem is

```text
beta n_alpha D(u_beta)-alpha n_beta D(u_alpha)
=(beta-alpha)Q_(alpha,beta)(v),                        (S49.2)

Q_(alpha,beta)(v)
=(X+c)Y-(alpha+beta)xY+alpha beta xy.                 (S49.3)
```

Therefore, away from endpoint characteristic divisors,

```text
I_(alpha,beta)q
=Q_(alpha,beta)(v)/[(Y-beta y)(Y-alpha y)].            (S49.4)
```

Spectral expansion of `Q` contains four sectors:

1. diagonal terms `(t_i-alpha)(t_i-beta)b_i d_i v_i^2`;
2. symmetric pair products `b_i d_j+b_j d_i`;
3. alternating Plücker products `b_i d_j-b_j d_i`;
4. homogeneous Neumann term `c sum_i t_i d_i v_i`.

For opposite shifts `alpha=-beta`, alternating sector vanishes while diagonal and symmetric
sectors survive.  Rank one recovers physical affine intercept `L(v)/D(v)` exactly; Plücker chord
only knows slope.  Thus S47--S48 remain correct chord/tomography theorems but do not by themselves
carry affine-sewn jump.

Specializing to actual Volterra source uses

```text
B_z=(1/2)D_z Omega,      Omega=H_g-H_(r0)A,
c_z=(1/2)D_z(H_(r0)e).                                 (S49.5)
```

Actual frontier corpus cannot solve is now `SUZUKI-MARKED-SECANT-CD-WELD`: derive division-free
prime--Gamma Christoffel--Darboux/Green identity whose left side is Pick polarization of marked
tensor `(S49.3)` plus exact global Xi deficit, and whose right side is positive source Gram.
Finite jet filters can tomographically expose all four sectors.  One negative principal minor
falsifies producer.  Proving identity gives exact Loewner gap, jump Pick positivity, pole
tomography, and RH.

Paper, failed route, and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-projective-affine-secant-tensor-lift.md`;
- `docs/drafts/pipeline/5-failed/suzuki-plucker-only-affine-sewing-producer.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiProjectiveAffineSecantTensor.lean`.

RH is not proved.  Open step is positive Gram factorization of actual marked Volterra tensor plus
Xi deficit.  This is positivity whose proof would be RH; that is valid target, but no positivity
has been assumed or renamed as proof.

## S50. Volterra Cartesian split isolates actual RH-bearing source operator (2026-07-22)

S47--S48 identify homogeneous Plucker geometry but not concrete triangle operator.  Exact Fubini
now supplies it.  If

```text
(V_k u)(x)=integral_(-a)^x k(x-y)u(y)dy,
C_k=V_k+V_k^*,        H_k=-i(V_k-V_k^*),               (S50.1)
```

then physical right triangle and Xi-real normalization are

```text
T_(k,R)[u]=Fourier[V_k u],
-iT_(k,R)=1/2 Fourier[H_k u]-i/2 Fourier[C_k u].       (S50.2)
```

For odd phase-one source, `C_k u` is odd and `H_k u` is even.  Hence

```text
Even[-iT_(lambda,R)]=1/2 Fourier[H_lambda nu_lambda],
Odd [-iT_(lambda,R)]=-i/2 Fourier[C_lambda nu_lambda]. (S50.3)
```

Compressed `C_lambda` is precisely positive admissible pencil
`G_a-lambda(-Delta_N)^(-1)`.  Its positivity therefore controls known odd clock, not unresolved
even pole carrier.  This falsifies direct inference from Volterra accretivity to jump Pick
positivity.

For `r_0=-|t|/2`, antisymmetric half has exact moment law

```text
(V_r0-V_r0^*)u=-x*mu_0/2+mu_1/2.                      (S50.4)
```

Odd source has `mu_0=0`, so `H_r0` is rank-one moment-to-constant map and `(S50.3)` gives

```text
Even[-iT_(r0,R)]=-W'(0)sin(az)/(2z).                  (S50.5)
```

This is exactly S42 Neumann projective holonomy.  All infinite-dimensional unresolved source
content lies in `H_g`.

On resolvent orbit `Au_lambda-lambda u_lambda=e`, phase homogenization is

```text
(H_g-lambda H_r0)u_lambda
 =(H_g-H_r0*A)u_lambda+H_r0*e.                        (S50.6)
```

Thus source operator entering S49 marked secant is relative phase defect
`Omega=H_g-H_r0*A`, plus one rank-one coordinate.  Explicitly

```text
(H_g u)(x)=-i integral sgn(x-y)g(x-y)u(y)dy,
H_g=-i[X,Q_g],       Q_g kernel g(x-y)/|x-y|.          (S50.7)
```

This is precise source input, not estimate: positivity of symmetric pencil, negative projectors,
and complete jet tomography do not determine independent causal phase.  Combined with S49, live
frontier is `SUZUKI-MARKED-SECANT-CD-WELD`: prove positive prime--Gamma Green identity for marked
tensor built from `Omega`, rank-one holonomy, and global Xi deficit.  Proving it gives jump Pick
kernel and RH.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-volterra-cartesian-phase-defect.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiVolterraCartesianPhaseDefect.lean`.

## S51. Canonical global-local compound Bezoutian weld (2026-07-22)

S49--S50 identify actual marked Volterra numerator but leave "plus global Xi deficit" informal.
Putting local marked pair `(Q,P)` and centered global pair

```text
S=XiC',              T=z^2 XiC
```

into one compound pair removes this ambiguity:

```text
N=Q*T-S*P,           D=P*T.                          (S51.1)
```

Away from explicit divisors,

```text
N/D=Q/P-S/T,                                           (S51.2)
```

exactly full jump response.  Core result is division-free.  Arbitrary common pointwise affine
gauge cancels:

```text
Q -> Q+delta P,      S -> S+delta T  ==> N unchanged. (S51.3)
```

This weld is unique up to scale among bilinear forms: if
`W=aQS+bQT+cPS+dPT` is common-gauge invariant and vanishes when `QT=SP`, then
`a=d=0`, `c=-b`, hence `W=b(QT-SP)`.

Define Hermitian cross-Bezoutian

```text
[F,G]_(z,w)=F(z)conj(G(w))-G(z)conj(F(w)).
```

Exact compound product rule is

```text
[N,D]=T(z)conj(T(w))[Q,P]-P(z)conj(P(w))[S,T].        (S51.4)
```

Equation `(S51.4)` is precise division-free meaning of "marked tensor plus Xi deficit".  It also
sharpens S49 affine obstruction.  Independent gauges produce `N -> N+rD` and

```text
[N+rD,D]=[N,D]+D(z)conj(D(w))(r(z)-conj(r(w))).       (S51.5)
```

Common pointwise gauge has `r=0`; real constant relative gauge is Pick-invisible.  Actual chart
obstruction is relative nonconstant/non-real curvature, not arbitrary affine normalization.

Hostile audit survives:

- opposite shifts retain diagonal/symmetric sectors through `Q`;
- rank one need not vanish because determinant is between local and global pairs;
- fake functional-equation orbit changes `(S,T)` and hence `N`, except genuine projective/gauge
  degeneracy;
- no division, zero-free region, Herglotz realization, positivity, or RH premise enters
  `(S51.3)--(S51.5)`.

Actual corpus frontier is now `SUZUKI-COMPOUND-BEZOUTIAN-GRAM`: specialize `Q` to marked Volterra
tensor built from

```text
Omega=H_g-H_r0*A
```

and rank-one holonomy, then derive directly from prime--Gamma screw source a positive Green/Gram
factorization of signed compound kernel `(S51.4)` on one nontrivial aperture.  Positivity is not
avoided because it is RH-bearing; representation ambiguity has been removed so this is now one
falsifiable source identity.  A negative principal minor refutes it.  A positive source
factorization yields full jump Pick positivity and RH.

Paper, certificate, and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-global-local-compound-bezoutian-weld.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-global-local-compound-bezoutian-weld.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiGlobalLocalCompoundBezoutianWeld.lean`.

RH is not proved.  Exact remaining open statement is source Gram factorization of `(S51.4)`, not
generic "positivity" or another estimate.

## S52. Midpoint Lorentz completion fixes exact rooted debt (2026-07-22)

Write marked shifts as `alpha=m-d`, `beta=m+d`, and centered boundary data

```text
U=B0-mx,      V=Y-my,      F=B0*y-x*Y.
```

Exact marked secant pair is

```text
Q=U*V-d^2*x*y+m*F,
P=V^2-d^2*y^2.                                      (S52.1)
```

Symmetric coefficient form has Lorentz diagonal

```text
(r-m*s)^2-d^2*s^2.                                  (S52.2)
```

Adding rooted diagonal `kappa*s^2` is nonnegative for every `(r,s)` iff `d^2<=kappa`.
At sharp value it is exactly square `(r-m*s)^2`.  Thus missing rooted mass is not free parameter:

```text
kappa_min=d^2=(beta-alpha)^2/4.                      (S52.3)
```

For dyadic Suzuki pair `(-2L,-L)`, debt is `L^2/4`.  Same `d^2` occurs in actual product-resolvent
equation and relative Volterra phase as `-d^2*phaseNeumann(v)`.  Compound numerator splits into
midpoint determinant, rooted debt, and centered Pluecker flux.  These are unconditional exact
identities, now paper-proved and Lean-formalized.

Paper, certificate, and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-marked-secant-midpoint-lorentz-completion.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-marked-secant-midpoint-lorentz-completion.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiMarkedSecantMidpointLorentzCompletion.lean`.

This sharpened S51 frontier to exact rooted completion problem, but did not yet justify critical
cofinal Hilbert limit.

## S53. Critical rooted Bianchi cofinal no-go and scalar rigidity (2026-07-22)

Corpus raw Gamma--Bianchi diagonal at prime `p` and displacement `x` is

```text
b_x(p)=Lambda(p)/p * exp(-x log p).                  (S53.1)
```

Suzuki critical screw weight forces `x=-1/2`, exactly

```text
b_(-1/2)(p)=Lambda(p)/sqrt(p).                       (S53.2)
```

This is not proxy normalization.  Existing unique complete Gamma-conormal renormalization has
boundary coordinate `sqrt(b_x(p))`; new Lean connector identifies its `x=-1/2` specialization with
critical rooted amplitude.

For every prime,

```text
log(2)/p <= Lambda(p)/sqrt(p).                       (S53.3)
```

Euler prime-harmonic divergence therefore proves critical mass is not summable.  No PNT,
asymptotic estimate, computation, RH premise, or zero data enters.  Consequently standalone raw
rooted feature is not `ell^2` and cannot be passed cofinally as ordinary positive Hilbert Gram.

Stronger scalar-renormalization rigidity is exact:

```text
Summable_p (c*sqrt(b_(-1/2)(p)))^2  <=>  c=0.         (S53.4)
```

Thus global scalar rescaling, finite border, or nonzero constant residual cannot repair route.
Leading critical coordinate must cancel exactly prime-by-prime before square and limit.

This falsifies original unrenormalized cofinal reading of
`SUZUKI-ROOTED-MIDPOINT-COMPOUND-GRAM`, while preserving every finite-cutoff Gram.  Corrected RH
frontier is

```text
SUZUKI-FINITE-APERTURE-RENORMALIZED-MIDPOINT-GRAM:

R_M(p;z)=J_M(p;z)-m B_M(p)+L_M(p;z),
[N_M,D_M](z,w)
 = sum_(p^k in M) R_M(p^k;z)conj(R_M(p^k;w))
   + <A_M(z),A_M(w)>.                                (S53.5)
```

Here `L_M` must be actual prime-dependent Volterra boundary leakage and `A_M` exact completed
Gamma/polar feature.  No fitted remainder allowed.  Prove `(S53.5)` at finite aperture, establish
exact leading cancellation forced by `(S53.4)`, then pass only combined residual cofinally.  This
is actual corpus frontier: exact source intertwiner from Suzuki Volterra boundary atom to completed
prime--Gamma--polar residual.  Corpus has no theorem determining `L_M` or proving `(S53.5)`.

Paper, failed route, certificate, and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-critical-rooted-bianchi-cofinal-no-go.md`;
- `docs/drafts/pipeline/5-failed/suzuki-unrenormalized-cofinal-rooted-bianchi-gram.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-critical-rooted-bianchi-cofinal-no-go.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCriticalRootedBianchiCofinalNoGo.lean`.

RH is not proved.  Progress is structural and falsifiable: one previously proposed RH-producing
limit is impossible, exact reason is formalized on actual source coordinate, and surviving route
now has forced order of operations plus exact scalar cancellation law.

Verification: direct new-module check and SOTA umbrella check passed; axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`; forbidden-token scan and repository formal lint
passed; final targeted build
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passed (9443 jobs).  No Lean or
Lake process from this work remains running.

## S54. Causal Weil--Robin identity localizes actual collective frontier (2026-07-22)

Delayed-hinge sign theorem forbids atomwise positive prime factorization.  Corpus now has stronger
collective source identity.  For screw primitive `g`, `K=-g''`, compact aperture source `v`, and
right screw exterior `R_g[v]`, two source integrations by parts give

```text
z^2 R_g[v](z)
 = exp(i*a*z)(i*z*U(a)-U'(a)) + E_K[v](z).             (S54.1)
```

Thus canonical compound denominator removes universal `z^-2` primitive and leaves exactly Robin
boundary current plus causal exterior of already-completed signed Weil distribution.  Delayed
hinge specialization recovers prior boundary--tail law.  Direct form shift changes
`K` by compact delta whose exterior vanishes, so exact midpoint debt `d^2` is localized in Robin
current, not raw Bianchi bulk.

Actual RH frontier is therefore

```text
SUZUKI-MARKED-WEIL-ROBIN-CD:
affine-sew marked Robin currents + polarize complete causal Weil exterior
 = positive Green Gram.                               (S54.2)
```

No positive part of signed Weil exterior may be assumed: that would import RH-equivalent content.
One negative principal minor of full sewn kernel falsifies `(S54.2)`; success gives compound Pick
positivity and RH through existing pole tomography.

## S55. Triple-log repair fails; critical aperture has exact quarter-shift resolvent (2026-07-22)

Midpoint polynomial `(w-alpha)(w-beta)=(w-m)^2-d^2` is also numerator of corpus's unique affine
two-boundary Cauchy residual.  Canonical critical specialization is

```text
C(p)=-1/[4 log(p)(log(p)+1/2)(log(p)-1/2)].            (S55.1)
```

Weighting by actual critical mass gives

```text
M_aff(p)=Lambda(p)/sqrt(p)*C(p)^2,
1/(6400000*p) <= M_aff(p).                            (S55.2)
```

Euler prime-harmonic divergence proves `M_aff` nonsummable.  Hence strongest existing
two-boundary log-resolvent repair is impossible.  This is formalized with exact connector to
existing affine residual; no PNT, computation, zero data, or RH premise occurs.

Positive survivor comes from a corpus object not previously completed at critical displacement:
finite Gamma--Euler aperture boundary current.  Pair uniquely renormalized critical boundary with
cubically normalized true-aperture innovation before squaring.  For prime `p`, valuation depth
`e`, positive aperture `h,a`, its actual atom satisfies

```text
T_(e+1)(h,a,t;p)=rho(h,a,t;p) T_e(h,a,t;p),
rho=exp(-log(p)/4)*exp(i*t*log(p)/2)
      *exp(-h*a*log(p)),
|rho|<1,                                               (S55.3)
sum_(e>=0) T_e = T_0/(1-rho).                         (S55.4)
```

Lean proves `(S55.3)--(S55.4)` on actual source definitions.  Transverse factor
`q/(1+q)=1/(p+1)` moves prime current to `sqrt(log p)/p^(5/4)` scale, giving dependency-closed
paper proof of absolute prime completion.  Critical boundary still has no standalone Hilbert
vector; correct topology is distributional boundary paired with trace-class aperture innovation.

This does not supersede `(S54.2)` or resurrect atomwise positivity.  It fixes Gamma/aperture
component of Robin channel and removes former unspecified leakage `L_M`.  Exact unsolved frontier
is now narrower: prove full marked Robin plus completed signed Weil exterior has positive Green
Gram, with quarter-shift current forced as its critical Gamma/aperture subchannel.

Paper, failed route, and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-critical-affine-cauchy-residual-divergence.md`;
- `docs/drafts/pipeline/5-failed/suzuki-critical-affine-cauchy-repair.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCriticalAffineCauchyResidualDivergence.lean`;
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-critical-aperture-quarter-shift-current.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCriticalApertureQuarterShiftCurrent.lean`.

RH is not proved.  Frontier progress is representation-level: canonical logarithmic repair is
closed, first source-native power-scale critical pairing is exact, and remaining RH theorem has no
free leakage coordinate.

Verification: both new modules pass direct `lake env lean`; axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden declaration scan is clean.  Required targeted build
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passed `9450/9450`.  Repository
formal lint reaches both modules but remains red on six unrelated concurrent unreachable modules.

## S56. Prime entry is an endpoint-trace third-jet event (2026-07-22)

Rectangular Ward frontier still contained unspecified “near-entry channel.”  Exact moving-boundary
transport removes that freedom.  For delay `ell`, cut `c=a-ell`, truncated moments `A,B`, high
Fourier window `H`, and completed near channel

```text
F_near=exp(i*a*z)(i*z*A-B)-exp(i*z*ell)H,
```

Leibniz transport gives

```text
F_near'  =-i*z[exp(i*a*z)B+exp(i*z*ell)H],
F_near'' =z^2*exp(i*z*ell)H,
F_near'''=i*z^3*exp(i*z*ell)H+z^2*exp(i*a*z)v(a-ell). (S56.1)
```

Point evaluations cancel twice because `ell+c=a`.  At prime-entry wall `ell=2a`, near and far
channels agree through delay order two.  First defect is

```text
F_near'''(2a-)-F_far'''(2a+)
 =z^2*exp(i*a*z)v(-a).                                (S56.2)
```

Thus no prime produces instantaneous positive value, slope, or curvature update.  Discrete entry
reporter is endpoint trace of zero-extended deficiency source.  Under affine sewing it is

```text
z^2*exp(i*a*z)
 *((beta-gamma)W_beta*tau_alpha
   -(alpha-gamma)W_alpha*tau_beta),                   (S56.3)
```

a marked barycentric trace.  Common normalized trace survives rather than cancelling.

Actual open problem remains `SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED`: identify `(S56.3)` with
critical quarter-shift Gamma/aperture current, reconstruct near-entry contribution by triple
integration, and prove assembled rectangular Ward defect uniformly lower bounded.  Existing
connector then proves RH; exact Green--Gram equality is unnecessary.  Corpus currently proves
neither source identification nor lower bound, so RH is not proved.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-causal-entry-third-jet-boundary-law.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-causal-entry-third-jet-boundary-law.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCausalEntryThirdJetBoundaryLaw.lean`.

Verification: direct new-module check is diagnostic-free; axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; final targeted build
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passes `9452/9452`.  Repository
formal lint reaches new module but remains red on unrelated concurrent unreachable HTGeometry
module `CrossingConeSharpCommutativityPhaseLaw`.

## S57. Entry Green transport forces critical quarter-shift phase (2026-07-22)

The near-entry triple-integration problem has an exact source solution.  For completed near/far
gap `G=F_near-F_far`, subtraction of known second and third jets gives throughout near region

```text
(d/dell-I*z)G''(ell,z)=z^2*exp(I*a*z)*tau(ell).         (S57.1)
```

At wall `ell=2a`, `G=G'=G''=0`; hence `(S57.1)` uniquely reconstructs full gap.  With entry depth
`s=2a-ell` and `u(s)=v(-a+s)`, Green kernel is

```text
G(2a-s,z)=exp(I*a*z) integral_0^s
  [exp(-I*z*(s-r))-1+I*z*(s-r)]u(r)dr.                (S57.2)
```

For prime `p`, valuation depth `e`, and `n=p^(e+1)`, wall aperture is

```text
a_(p,e)=log(n)/2,
exp(I*t*a_(p,e))=exp(I*t*log(n)/2).                   (S57.3)
```

This is exactly conjugated critical Gamma-height phase; successive walls differ by
`log(p)/2`, explaining half-log depth phase geometrically.  Keeping observer aperture `b`
distinct from wall aperture, define source amplitude

```text
A_e(h,b;p)=sqrt(log(p)/n*exp(log(n)/2))*I_cubic(h,b;p,e).
```

Existing critical atom then factors exactly as

```text
T_e(h,b,t;p)=A_e(h,b;p)*exp(I*t*a_(p,e)),
Delta_3(p,e;t)=t^2*T_e(h,b,t;p).                      (S57.4)
```

Therefore actual entry forcings inherit quarter-shift recursion and completion

```text
Delta_3(p,e+1;t)=rho(h,b,t;p)*Delta_3(p,e;t),
sum_(e>=0) Delta_3(p,e;t)=t^2*T_0/(1-rho).            (S57.5)
```

Off `t=0`, coefficient `t^2*exp(I*t*a_(p,e))` is nonzero, so matching uniquely forces endpoint
trace `A_e`.  Phase, normalization, and causal reconstruction are no longer free coordinates.

Actual unresolved source statement is narrower: prove Suzuki's concrete restricted-Weil
deficiency endpoint trace equals this calibrated amplitude after already fixed affine
normalization, or prove mismatch residual contributes uniformly lower-bounded fixed-width
rectangular form.  Then `SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED` still requires assembled Ward
defect lower bound.  Neither endpoint realization nor lower bound is in corpus; RH is not proved.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-critical-entry-wall-quarter-shift-green-law.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-critical-entry-wall-quarter-shift-green-law.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCriticalEntryWallQuarterShiftGreenLaw.lean`.

Verification: direct new-module check is diagnostic-free; axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; final targeted build
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passes `9453/9453`.  Repository
formal lint reaches new module but remains red on eight unrelated concurrent unreachable modules.

## S58. One wall field is linear entry and quadratic far source (2026-07-22)

Hostile source audit falsifies one semantic identification in S57.  Quantity

```text
A_e(h,b;p)=sqrt((log p/n)*exp(log n/2))*I_cubic(h,b;p,e)
```

depends on independently chosen observer aperture `b`; Suzuki deficiency endpoint
`v_(a,lambda)(-a)` is fixed by restricted-Weil resolvent, shift, and wall aperture.  At depth zero,
Lean proves `b -> A_0(h,b;p)` injective for `h,b>0`.  Hence it cannot be one observer-independent
endpoint trace at two distinct observers.

Positive survivor is stronger source compression.  For `n=p^(e+1)`, set

```text
b_e=sqrt((log p/n)*exp(log n/2)),
omega_e(t)=conj(xiGammaEulerHeightBoundaryFeature(-1/2,t;(p,e))).
```

Exact algebra gives

```text
omega_e(t)=b_e*exp(I*t*log(n)/2),
b_e^2=Lambda(n)/sqrt(n),
omega_e(t)^2=(Lambda(n)/sqrt(n))*exp(I*t*log n).       (S58.1)
```

Thus Xi-real far delayed-hinge atom and entry jets are

```text
J_e(t)=-I*omega_e(t)^2/t^2,
t^2*J_e(t)=-I*omega_e(t)^2                 (t != 0),
DeltaBare_3=t^2*omega_e(t),
DeltaObs_3=t^2*omega_e(t)*I_cubic(h,b;p,e).            (S58.2)
```

Square in `(S58.1)` is complex bilinear, not norm square; it retains delay phase and creates no
atomwise positivity claim.  This is why existing negative far Pick diagonal remains valid.

Scientific advance: universal far tail, bare entry reporter, and observed quarter-shift current
are quadratic, linear, and observer-paired linear degrees of one wall field.  Separate far-channel
matching is removed from RH frontier.  Correct producer is joint symmetric-square/observer block,
not direct-sum positive prime Gram.

Actual unresolved frontier is now exact and source-local:

```text
actual normalized restricted-Weil deficiency wall trace = b_e,
```

was next conjecture, but subsequent S59 resolvent audit rejects literal equality: `b_e` is source
input, while deficiency endpoint depends on restricted-Weil resolvent and boundary observation.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-critical-wall-field-square-root-weld.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-critical-wall-field-square-root-weld.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCriticalWallFieldSquareRootWeld.lean`.

Direct source check passes diagnostic-free; axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; final targeted build
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passes `9454/9454`.
Repository formal lint reaches new module but remains red on eleven unrelated concurrent
unreachable modules.  RH is not proved.

## S59. Restricted-Weil resolvent dresses wall field and exposes exact negative-mode debt (2026-07-22)

S58 bare wall amplitude is source coordinate, not deficiency endpoint response.  At one spectral
level `s`, Suzuki state equation forces shifted resolvent dressing

```text
r_lambda(s)=1/(s-lambda),
D_lambda(s;t)=r_lambda(s)omega_e(t).                    (S59.1)
```

For two distinct source shifts `alpha,beta`, affine zero-shift extrapolation obeys

```text
D_0-D_aff=K_(alpha,beta)(s)omega_e(t),
K_(alpha,beta)(s)=alpha*beta/[s(s-alpha)(s-beta)].      (S59.2)
```

Self-pairing with same source field and applying S58 gives new closed residual law

```text
omega_e(t)(D_0-D_aff)
 =K_(alpha,beta)(s)omega_e(t)^2
 =K_(alpha,beta)(s)*Lambda(n)/sqrt(n)*exp(I*t*log n).  (S59.3)
```

For `alpha<beta<0`, `beta<s`, and `s!=0`, sign of `K` is sign of `s`.  At `t=0`, prime-power
weight is strictly positive; therefore `(S59.3)` is strictly negative on every negative spectral
level and strictly positive on every positive level.

Scientific advance: endpoint residual is no longer free scalar and raw equality `endpoint=b_e`
is falsified.  Source-symmetric affine mismatch is exact von-Mangoldt-weighted Krein debt.
Two-shift entry block cannot be positive on negative restricted-Weil modes; marked Robin,
polar--Gamma, or holonomy block must compensate exact term before any rectangular lower bound.

Actual frontier is now `SUZUKI-RESOLVENT-DRESSED-WALL-WARD`:

```text
construct actual restricted-Weil spectral measure and boundary endpoint observation
on D_lambda(s;t), then prove mixed compensation pays (S59.3) on every negative mode
with uniformly lower-bounded fixed-width rectangular residual.
```

This is not positivity itself and does not prove RH.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-critical-wall-field-resolvent-dressing-law.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-critical-wall-field-resolvent-dressing-law.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCriticalWallFieldResolventDressingLaw.lean`.

Direct source check passes diagnostic-free; axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; final targeted build
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passes `9455/9455`.
Repository formal lint reaches new module but remains red on thirteen unrelated concurrent
unreachable modules.  RH is not proved.

## S60. Projective density and FE-reflected wall Gram (2026-07-22)

S59 one-mode resolvent law is exact but corpus projective audit prevents using it as canonical
Suzuki producer: multiplying one source state by common scalar cancels from normalized
characteristic response.  Correct pre-division carrier is marked affine-secant tensor and
denominator.  Both obey exact degree-two scaling

```text
T(omega*x,omega*X,omega*y,omega*Y,omega*c)=omega^2*T,
D(omega*y,omega*Y)=omega^2*D.                          (S60.1)
```

For critical wall field, `omega=omega_e(t)` and `omega_e(t)^2=H_e(t)`, exact far-hinge numerator.
Thus both division-free terms retain `H_e`, while quotient cancels it.  Far source is common
determinant-line density, not independent normalized-response atom.

Prior obstruction “complex square is not norm square” is resolved without discarding phase.
Define independent-height Hermitian kernel

```text
K_e(t,u)=omega_e(t)*conj(omega_e(u))
        =Lambda(n)/sqrt(n)*exp(I*(t-u)*log(n)/2).       (S60.2)
```

Lean proves every finite height section is literal rank-one Gram and hence PSD.  Two distinct
restrictions carry two required source types:

```text
K_e(t,t) =Lambda(n)/sqrt(n)>0,                         (S60.3)
K_e(t,-t)=Lambda(n)/sqrt(n)*exp(I*t*log n).             (S60.4)
```

Equation `(S60.4)` is exact far-hinge numerator because FE reflection gives
`conj(omega_e(-t))=omega_e(t)`.  Equation `(S60.3)` is exact local rooted currency:

```text
S_(m,d)(b_e(r,s),b_e(r,s))+d^2*(b_e*s)^2
 =Lambda(n)/sqrt(n)*(r-m*s)^2 >= 0.                    (S60.5)
```

Scientific advance: same genuine Hermitian block carries positive diagonal needed for sharp
marked halfgap completion and reflected anti-diagonal needed for complete far phase.  It neither
claims anti-diagonal nonnegative nor constructs nonsummable all-prime vector.

Actual corpus frontier is now `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`:

```text
assemble local K_e blocks with actual division-free marked Robin/polar--Gamma/holonomy carrier;
compensate divergent all-prime diagonal before cofinal limit;
prove exact d^2 and holonomy Schur debts are paid;
prove resulting rectangular Ward defect uniformly lower semibounded.
```

That global assembly and lower bound remain unproved; RH is not proved.

Paper and Lean:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-wall-field-projective-density-separation-law.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-wall-field-projective-density-separation-law.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiWallFieldProjectiveDensitySeparationLaw.lean`;
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-wall-field-antidiagonal-gram-lift.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-wall-field-antidiagonal-gram-lift.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiWallFieldAntidiagonalGramLift.lean`.

Direct source checks are diagnostic-free.  Final targeted build
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passes `9457/9457`.  Axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`; forbidden declaration scan is clean.
Formal lint reaches both new modules but remains red on 22 unrelated concurrent unreachable
modules.  No stale Lean/lake process remains.

## S61. Wall field realizes forced FE/Xi-real light completion (2026-07-22)

S60 exposed positive diagonal and phase-bearing anti-diagonal in one Hermitian wall Gram, but did
not realize abstract negative light completion from actual source.  Common wall scaling cannot do
this because corpus proves it only acts by projective congruence.

For wall field `omega_e`, define non-common reflected amplitudes

```text
ellPlus(t) =(omega_e(t)+I*omega_e(-t))/2,
ellMinus(t)=(omega_e(t)-I*omega_e(-t))/2.
```

Their two-variable Gram kernels and reflected current satisfy exact unconditional laws

```text
LPlus-LMinus=F_reflected,
LPlus+LMinus=(K_e(t,u)+K_e(-t,-u))/2,
F_reflected+LMinus=LPlus.                               (S61.1)
```

The two light legs are unique under first two equations.  This is literal source realization,
not abstract coordinate analogy.  For `v_e(t)=(Re omega_e(t),Im omega_e(t))`,

```text
R v_e(t)=-v_e(-t),
LPlus(t,u) =QPlus_1(v_e(t),v_e(u)),
LMinus(t,u)=QMinus_1(v_e(t),v_e(u)),
F(t,u)     =QFE_1(v_e(t),v_e(u)).                       (S61.2)
```

Every finite prime-power/height packet of `LPlus` and `LMinus` is literal Gram matrix in finite
source-coordinate Euclidean space, hence PSD, and `(S61.1)` survives source summation.  On
diagonal, `F(t,t)=Im(omega_e(t)^2)`.  Existing square-root weld therefore gives, off center,

```text
t^2*Re J_e(t)+|ellMinus(t)|^2=|ellPlus(t)|^2>=0.        (S61.3)
```

Scientific advance: actual critical wall source supplies unique local negative-light leg; no
external fitted completion is needed.  Abstract source-realization gap is closed at every finite
aperture.

Hostile cofinal audit exposes next obstruction.  Unsplit light mass contains divergent
`sum Lambda(n)/sqrt(n)`.  Subtracting one common PSD counterterm after light splitting cannot
generically remove it: on multi-height packets positive and negative rank-one light ranges are
transverse, so common positive lower bound is generically zero.  Positive survivor is therefore
pre-split fixed-width renormalization: assemble causal Robin/Gamma/holonomy carrier and cancel
cofinal mass before FE/Xi-real projection.  Actual RH-bearing frontier is
`SUZUKI-PRESPLIT-RECTANGULAR-LIGHT-RENORMALIZATION`: prove concrete boundary trace supplies or
dominates forced `LMinus`, pays holonomy Schur and marked halfgap debts, and leaves rectangular Ward
defect uniformly lower semibounded.  Existing connector then proves RH.  This remains unproved;
RH is not proved.

Paper, Lean, and next conjecture:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-wall-field-light-cone-kernel-completion.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-wall-field-light-cone-kernel-completion.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiWallFieldLightConeKernelCompletion.lean`;
- `docs/drafts/pipeline/1-in-progress/suzuki-presplit-rectangular-light-renormalization.md`.

Direct source check passes.  Final targeted build
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passes `9458/9458`.  Axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`; forbidden declaration and whitespace
scans are clean.  Formal lint reaches new module but remains red on 21 unrelated concurrent
unreachable modules.

## S62. Aperture innovation gives all-prime pre-split light completion—and exact height-flat no-go (2026-07-22)

S61's cofinal obstruction can be attacked using actual source operation already present before
light projection.  Let real cubic dyadic innovation be `iota_(h,a)(p,e)` and define observer-dressed
wall field

```text
psi_t(p,e)=suzukiCriticalApertureBoundaryAtom(h,a,t,p,e)
           =omega_e(t)*iota_(h,a)(p,e).                 (S62.1)
```

For `h,a>0`, exact dyadic Gram identity and prime-square bound give

```text
sum_e iota_(h,a)(p,e)^2
 =|(h*sqrt(h))^-1|^2 I_p(h;a,a),
0<=I_p(h;a,a)<=2/p^2.                                  (S62.2)
```

Critical Gamma density is at most `log p`, hence

```text
sum_e |psi_t(p,e)|^2
 <=2 |(h*sqrt(h))^-1|^2 log(p)/p^2.                    (S62.3)
```

Prime summability proves `psi_t in ell^2(Nat.Primes x N)` unconditionally.  Since innovation is
real, FE reflection survives: `psi_(-t)=conj(psi_t)`.  Therefore completed light vectors

```text
PsiPlus_t =(psi_t+I psi_(-t))/2,
PsiMinus_t=(psi_t-I psi_(-t))/2                        (S62.4)
```

are genuine all-prime Hilbert vectors.  Coordinatewise they are exactly old wall light legs times
innovation, so no fitted completion is introduced.  Their global Grams obey

```text
P-N=F_reflected,       F_reflected+N=P,                (S62.5)
```

and both legs are PSD on every finite height packet.  This is first concrete pre-split completion:
cofinal wall divergence and negative-leg realization are closed for actual observer-dyadic source.

Scientific method also kills tempting overclaim.  Phase is unimodular, so Lean proves exact global
law

```text
<psi_t,psi_t>=<psi_u,psi_u>   for all t,u.              (S62.6)
```

Thus dressed norm alone cannot prove rectangular Ward semiboundedness; subtracting it shifts Xi
curvature by one constant and leaves RH-equivalent lower-bound problem unchanged.  This is not a
reason to avoid an RH-equivalent positivity statement: it identifies what must still be proved
unconditionally.  Actual frontier is now `SUZUKI-RESOLVENT-RECTANGULAR-LIGHT-INTERTWINER`:
construct actual restricted-Weil resolvent/marked Robin/polar--Gamma/holonomy transfer of completed
carrier, prove negative light channel uniformly contractive, and prove remaining rectangular trace
uniformly lower bounded.  That structural identity plus bound feeds existing connector and proves
RH.  Corpus does not yet prove transfer or bound; RH remains open.

Paper, Lean, and active conjecture:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-aperture-dressed-wall-light-completion.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-aperture-dressed-wall-light-completion.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiApertureDressedWallLightCompletion.lean`;
- `docs/drafts/pipeline/1-in-progress/suzuki-presplit-rectangular-light-renormalization.md`.

Internal collision search and targeted arXiv audit found source parents but no matching theorem;
external priority remains unverified.  Direct Lean check passes.  Final build, axiom, and lint
audits pass for owned module: axiom surface is only `propext`, `Classical.choice`, and `Quot.sound`;
forbidden declaration and whitespace scans are clean; targeted build
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passes `9461/9461`.  Repository
lint reaches new module but remains red on 21 unrelated concurrently unreachable modules.  No
stale owned Lean/lake process remains.

## S63. Causal valuation fusion breaks height flatness by an exact Frostman law (2026-07-22)

S62 squares dressed wall coordinates before summing valuation depths and therefore has flat
diagonal energy.  Corpus audit found a different operation already forced by Suzuki source: the
critical entry-wall atoms obey an exact geometric causal recursion.  For `h,a>0`, set

```text
r_p=exp(-log(p)/4)
      xiMobiusContinuousApertureDiskNode((h/2)a,p)^2,
z_p(t)=exp(i t log(p)/2),
R_p(t)=sum_(e>=0) psi_t(p,e).
```

Then `0<r_p<1`, and existing entry-wall calibration and depth recursion give the exact source law

```text
R_p(t)=A_p z_p(t)/(1-r_p z_p(t)).                       (S63.1)
```

Consequently its normalized diagonal is not flat:

```text
|R_p(t)|^2/|R_p(0)|^2
 =(1-r_p)^2/(1-2r_p cos(t log(p)/2)+r_p^2)
 =ccmFrostmanPoissonProfile(r_p^(-1),t log(p)/2).        (S63.2)
```

This is exact Suzuki--CCM source identification, not analogy.  It proves that causal valuation
fusion **before** square is concrete non-flat transfer missing from S62.  One prime remains
periodic.  For distinct primes `p!=q`, however, each profile is at most one and simultaneous
equality recovers both half-prime-log phases.  Incommensurability of `log(q)/log(p)` gives

```text
P_p(t)+P_q(t)=2  <->  t=0.                              (S63.3)
```

Thus

```text
D_(p,q)(t,u)=2-P_p(t-u)-P_q(t-u)                        (S63.4)
```

is nonnegative and vanishes exactly when `t=u`.  This is first source-derived faithful scalar
height separator in completed wall branch.  No Xi zero, RH premise, computation, fitted matrix, or
target positivity was used.

Scientific boundary is also sharper.  Primewise Frostman diagonal has positive profile floor; it
cannot itself supply signed cross-prime cancellation in Xi trace.  Remaining frontier is no longer
“find some height dependence.”  It is to prove concrete restricted-Weil rectangular trace contains
`(S63.2)` plus source-derived cross-prime/archimedean Robin--Gamma--holonomy correction, then prove
resulting Ward remainder uniformly lower bounded.  That unconditional theorem feeds existing RH
connector.

Paper, Lean, and active conjecture:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-causal-depth-frostman-transfer.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-causal-depth-frostman-transfer.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCausalDepthFrostmanTransfer.lean`;
- `docs/drafts/pipeline/1-in-progress/suzuki-presplit-rectangular-light-renormalization.md`.

Internal collision search found separate quarter-shift resolvent, entry-wall Green law, CCM
Frostman profile, and incommensurate prime clock, but no identification `(S63.2)` or separator
`(S63.4)`.  Targeted primary-source/arXiv search found no matching theorem; external priority
remains unverified.  Direct Lean source check passes.  Final targeted build
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passes `9477/9477`.  Axiom
surface of six capstones is only `propext`, `Classical.choice`, and `Quot.sound`; forbidden
declaration and whitespace scans are clean.  Repository lint reaches the new module and remains red
only on 21 unrelated unreachable modules.  No stale owned Lean/lake process remains.

## S64. Gamma-boundary pairing gives strict causal rectangular orientation (2026-07-22)

S63 supplied height dependence but not fixed-width aperture sign.  Direct hostile test kills
undemodulated conjecture: at prime phase `z=-1`, causal ray is negative real and its aperture
increment points left.  Correct operation is forced by source, not selected from target.

For `0<c<1`, `s<=1`, and `0<x<1`, define

```text
H_(c,s)(x)=(1-x)^2(1-cx^2s)/(1-2cx^2s+c^2x^4).       (S64.1)
```

Exact derivative comparison proves `H_(c,s)` strictly decreasing on `(0,1)`.  Lean exposed
stronger half-line range `s<=1`; lower phase bound is unnecessary.  With

```text
c=exp(-log(p)/4),
x(a)=exp(-(ha/2)log(p)),
z_p(t)=exp(i t log(p)/2),
R_p(a,t)=suzukiCriticalApertureDepthFusedAtom(h,a,t,p),
```

actual source recursion gives

```text
conj(z_p(t))R_p(a,t)
 =B_p(h)(1-x(a))^2/(1-cx(a)^2z_p(t)),                 (S64.2)
```

where `B_p(h)>0`.  Since `x(a)` strictly decreases, for `h,a,L>0`, every real `t`, and every prime,

```text
0 < Re[conj(z_p(t))(R_p(a+L,t)-R_p(a,t))].            (S64.3)
```

Corpus tracing then removes remaining arbitrariness.  Actual unstarred depth-zero Gamma--Euler
boundary coordinate satisfies

```text
xiGammaEulerHeightBoundaryFeature(-1/2,t,(p,0))
 =G_p conj(z_p(t)),   G_p>0.                            (S64.4)
```

Therefore literal source-boundary pairing obeys

```text
0 < Re[xiGammaEulerHeightBoundaryFeature(-1/2,t,(p,0))
       (R_p(a+L,t)-R_p(a,t))].                         (S64.5)
```

This is first exact causal fixed-width rectangular sign linked to actual Gamma--Euler boundary
coordinate before FE light splitting or Gram square.  It is unconditional and uses no Xi zero,
RH premise, computation, fitted phase, or target positivity.

Frontier moves materially.  Phase discovery and primewise observer-response sign are solved.
Subsequent exact sharp-support audit in S65 proves that `(S64.5)` cannot itself be the literal sharp
prime trace cell: it remains strictly positive beyond the wall where sharp cell is exactly zero,
and it has wrong linear source degree.  S64 is therefore transfer/response layer.  Arithmetic
source is S65 compactly gated observer-free wall Gram.  Remaining open core is to prove concrete
restricted-Weil/Robin boundary operator transports that source into observer response, derive exact
Gamma/marked-halfgap/holonomy Schur remainder, and prove resulting Ward defect uniformly lower
bounded.  Fixed-prime increments decay toward finite aperture ceiling, so `(S64.5)` alone is not
uniform Ward bound and does not prove RH.

Paper, Lean, formalization certificate, and active frontier:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-causal-depth-rectangular-caratheodory-growth.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCausalDepthRectangularCaratheodoryGrowth.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-causal-depth-rectangular-caratheodory-growth.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-presplit-rectangular-light-renormalization.md`.

Targeted internal collision audit found no radial half-line law `(S64.1)`, causal rectangle
`(S64.3)`, or boundary identification `(S64.4)--(S64.5)`; external priority remains unverified.
Direct Lean check passes without module-local warnings.  Final targeted build passes `9479/9479`.
Six capstone axiom surfaces are only `propext`, `Classical.choice`, and `Quot.sound`; forbidden
declaration scan is clean.  Repository lint remains red on 21 unrelated unreachable modules.

## S65. Sharp prime cell is gated wall-Gram diagonal, not fused observer ray (2026-07-22)

S64 ended with wrong candidate trace identification.  Exact corpus comparison gives immediate
hostile falsifier.  Sharp rectangular prime term is finite:

```text
P_(L,a)=sum_(2<=n<=exp(2a))
          Lambda(n)/sqrt(n) R_(L,a)(log n),             (S65.1)
```

and exact support theorem gives `R_(L,a)(log n)=0` whenever `0<=L<=a` and `2a<log n`.
S64 Gamma-boundary fused observer rectangle instead has strictly positive real part for every
prime.  It therefore cannot literally be `(S65.1)`.  Source degree independently kills same
conjecture: fused response is linear in observer-dressed wall field; von Mangoldt cell is square of
bare observer-free wall field.

Competing conjectures were attacked explicitly:

1. direct S64 rectangle = sharp trace cell — **falsified** by positive tail versus exact zero;
2. sharp gate times fused observer ray — **falsified as source identification** by wrong degree and
   mixed valuation-depth response;
3. sharp gate times observer-free Hermitian wall Gram — survives and is now paper/Lean proved.

For `n=p^(e+1)`, let

```text
K_e(t,u)=omega_e(t) conjugate(omega_e(u)),
A_(L,a,e)=R_(L,a)(log n),
G_(L,a,e)(t,u)=A_(L,a,e) K_e(t,u).                     (S65.2)
```

Four-tent formula proves `A_(L,a,e)>=0` without any parameter restrictions.  Exact wall-Gram laws
then give

```text
conjugate(G(u,t))=G(t,u),
G(t,u)=A Lambda(n)/sqrt(n) exp(i(t-u)log(n)/2),
G(t,t)=A Lambda(n)/sqrt(n),                             (S65.3)
G(t,-t)=A Lambda(n)/sqrt(n) exp(i t log n).             (S65.4)
```

Every finite height section is PSD because it is nonnegative scalar multiple of rank-one wall
Gram.  Thus one local object now carries exact sharp prime cell as positive diagonal and full
delayed Weil phase as FE anti-diagonal.  Exact causal support gives `G=0` beyond `log n=2a`.

Positive no-go survivor is formal.  Under `h,a,L>0`, `L<=a`, and `2a<log p`, Lean proves

```text
GammaBoundary_p(t)
 [FusedObserver_p(h,a+L,t)-FusedObserver_p(h,a,t)]
 != G_(L,a,0)(t,t),                                    (S65.5)
```

because left real part is strictly positive and right side is exactly zero.  This corrects
architecture rather than merely retiring route: compact gated wall Gram is arithmetic source;
S64 coherent/fused field is downstream transfer/response.

This is material but not RH.  Full sharp Weil formula carries `-2 P_(L,a)` plus polar--Gamma
block.  Local PSD identifies source type; it does not prove total sign.  Actual unresolved
frontier is now exact `SUZUKI-GATED-WALL-GLOBAL-COMPENSATION`: construct restricted-Weil resolvent
and Robin boundary observation taking gated bare wall blocks as input, prove source-to-observer
intertwining without duplicate prime count, add polar--Gamma/marked-halfgap/holonomy Schur terms,
and establish cofinal fixed-width Ward residual uniformly lower bounded.  Existing connector then
proves RH.  Corpus has no unconditional theorem supplying that global compensated operator.

Paper, Lean, and active frontier:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-rectangular-wall-gram-gate.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-rectangular-wall-gram-gate.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiRectangularWallGramGate.lean`;
- `docs/drafts/pipeline/1-in-progress/suzuki-presplit-rectangular-light-renormalization.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-coherent-fusion-gamma-weld.md`.

Internal collision audit found wall Gram, sharp autocorrelation, sharp prime--Gamma formula, and
resolvent dressing separately, but no gated synthesis or exact S64 mismatch theorem.  Current
primary audit of Suzuki arXiv:2606.09096 and Groskin arXiv:2607.02828 found no matching local
source theorem; external priority remains unverified.  Direct new-module Lean check passes.  Final
targeted build `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passes
`9480/9480`.  Six capstone axiom surfaces are only `propext`, `Classical.choice`, and `Quot.sound`;
forbidden declaration scan is clean.  Repository lint reaches new module and is red only on 22
unrelated shared-tree unreachable modules.  No stale owned Lean/lake process remains.

## S66. Polar--Gamma completion is positive; prime wall is its exact Mangoldt quadrature (2026-07-22)

S65 left a mixed global compensation problem: full sharp Weil value subtracts finite positive prime
wall and adds polar--Gamma archimedean block whose pointwise sign had not been identified.  Corpus
already proved Gamma kernel integrability/bounded correction and separate polar-square identity, but
not common-lag sign.  Exact tent geometry closes that sub-frontier.

Write

```text
C(h)=R_(L,a)(h),  C(0)=2L,
G(t)=[exp(-t)C(0)-exp(-t/4)C(t/2)]/[1-exp(-t)].
```

Existing moving-tent bound `M(h)<=min(L,h)` now gives new sharp contraction

```text
0 <= C(h) <= C(0)=2L                             (S66.1)
```

for `0<=L<=a`, `h>=0`.  Define completed common-lag kernel

```text
K_(L,a)(t)=2 cosh(t/4) C(t/2)+G(t).
```

Exact algebra, not estimate, yields

```text
K(t)=exp(t/4)C(t/2)
 +exp(-t)/[1-exp(-t)] [C(0)-exp(-t/4)C(t/2)].     (S66.2)
```

Both channels on right are nonnegative for `t>0`; second is strictly positive when `L>0`.
Therefore `K(t)>=0`, and `K(t)>0` for every positive lag at positive width.  Gamma kernel need not
be positive separately: pointwise positivity is exact polar--Gamma completion.

Half-tilted autocorrelation rescaling proves exact mass identity

```text
integral_0^infinity K_(L,a)(t)dt
 =normalizedArch(L,a)+(gamma+log pi)2L.            (S66.3)
```

Hence full sharp formula becomes

```text
Weil(L,a)+(gamma+log pi)2L
 =integral_0^infinity K_(L,a)(t)dt-2 PrimeWall(L,a). (S66.4)
```

Stronger source connector emerged after hostile test.  First positive channel

```text
A_(L,a)(t)=exp(t/4)C(t/2)
```

is sampled by every sharp von-Mangoldt cell exactly:

```text
Lambda(n)/sqrt(n) C(log n)
 =Lambda(n)/n A_(L,a)(2 log n).                    (S66.5)
```

Thus entire finite prime wall is not merely analogous to a positive quadrature; it is literally

```text
PrimeWall(L,a)
 =sum_(2<=n<=exp(2a)) Lambda(n)/n A_(L,a)(2 log n). (S66.6)
```

Also `0<=A(t)<=K(t)`, so same-node completed-kernel Mangoldt quadrature dominates prime wall.
Combining `(S66.4)--(S66.6)`, Lean proves for every admissible logarithmic tail:

```text
RH <-> for every tail aperture a,
  2 sum Lambda(n)/n A_(L,a)(2 log n)+(gamma+log pi)2L
    <= integral_0^infinity K_(L,a)(t)dt.           (S66.7)
```

This is material frontier progress but not RH proof.  Two former unknowns are closed: Gamma sign
ambiguity and aggregate prime/arch source interface.  Actual remaining RH-bearing theorem is now
one explicit positive atomic-versus-continuous discrepancy `(S66.7)`.  Corpus sampling no-go proves
general archimedean seam cannot factor through integer-log samples on arbitrary continuous tests,
so universal quadrature reconstruction is dead.  Surviving attack must exploit special sharp
rectangular family through actual restricted-Weil resolvent and Robin boundary transport, producing
a source-derived positive Ward/Schur residual.  Defining residual from target difference would be
circular and is explicitly forbidden.

Scientific artifacts:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-rectangular-positive-arch-lag-completion.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-rectangular-positive-arch-lag-completion.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-positive-arch-mangoldt-quadrature-deficit.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiRectangularPositiveArchLagCompletion.lean`.

Internal collision audit found separate Gamma/polar laws, dyadic Mellin quadrature estimates, and
sampling no-go, but no common-lag positive split `(S66.2)` or exact sharp-wall sample weld
`(S66.5)--(S66.6)`.  Current Suzuki/Groskin primary audit found no matching theorem; external
priority remains unverified, so status is candidate new scientific knowledge.  Direct Lean check
passes.  Final targeted SOTA build passes `9512/9512`.  Eight capstone axiom surfaces are only
`propext`, `Classical.choice`, and `Quot.sound`; forbidden declaration scan is clean.  Repository
lint reaches new module and remains red on 21 unrelated shared-tree unreachable modules.  No stale
owned Lean/lake process remains.

## S67. Exact Mangoldt log-Haar transport localizes all debt to turning seam (2026-07-22)

S66 exposed exact atomic-versus-continuous deficit, but gave no legitimate way to pay atom
`2 Lambda(n)/n` at lag `tau_n=2 log n` from Lebesgue mass.  Universal sampling is impossible and
fitting a residual to target inequality would be circular.  S67 constructs source-derived cells.

Set

```text
F_n=2 sum_(d<=n) Lambda(d)/d,   tau_n=2 log n,
w_n=F_n-F_(n-1)=2 Lambda(n)/n.
```

Endpoint-retaining factorial estimate and divisor swap prove unconditionally

```text
n log n-n+1 <= sum_(m<=n) log m,
tau_n-2+2/n <= F_n,
tau_n-2 <= F_(n-1).                                      (S67.1)
```

The upper capacity law `F_n<=tau_n` is not new: it is Ramaré--Zuniga Alterman's theorem
`sum_(d<=X) Lambda(d)/d<=log X`.  Combining known upper law with new predecessor lower law gives
two canonical exact-mass systems

```text
P_n=(F_(n-1),F_n]       subset (tau_n-2,tau_n],
Q_n=(F_(n-1)+2,F_n+2]   subset (tau_n,tau_n+2],
length(P_n)=length(Q_n)=w_n.                              (S67.2)
```

Each family is pairwise disjoint.  Therefore decreasing profiles pay atom from `P_n`, increasing
profiles from `Q_n`, with Lebesgue multiplicity at most one.  Exact Suzuki normalization welds
transported atom to actual prime wall:

```text
w_n A_(L,a)(tau_n)
 =2 Lambda(n)/sqrt(n) R_(L,a)(log n).                     (S67.3)
```

No external premise is needed for transport architecture in Lean.  Existing formal Mertens bound
gives radius `R=2(log 4+4)`, width `W=2+2R`, and unconditional exact cells

```text
(F_(n-1)-R,F_n-R]             subset (tau_n-W,tau_n],
(F_(n-1)+R+2,F_n+R+2]         subset (tau_n,tau_n+W].     (S67.4)
```

They retain exact mass, pairwise disjointness, monotone integral consumers, and Suzuki weld.
For a unimodal channel, formal seam trichotomy localizes every atom not handled by one monotone
branch to `|tau_n-c|<W`; sharp paper interface reduces this to `|tau_n-c|<2` once known capacity
premise is supplied.

This is frontier progress, not RH.  Exact remaining core is
`SUZUKI-TURNING-SEAM-BICAUSAL-SPLICE`: choose future cells on rising side and past cells on falling
side across moving seam, including seam atoms, without using overlapping Lebesgue mass twice; then
use genuinely unused completed-kernel mass to pay fixed Gamma boundary charge.  This blocks a full
RH proof.  Returning to global prime estimates or naming target defect as residual does not solve
it.

Scientific artifacts:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-mangoldt-log-haar-bicausal-transport.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-mangoldt-log-haar-bicausal-transport.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiMangoldtLogHaarTransport.lean`;
- `docs/drafts/pipeline/1-in-progress/suzuki-positive-arch-mangoldt-quadrature-deficit.md`.

Corpus collision audit found no existing cell transport or endpoint predecessor theorem.  External
novelty is not certified; known capacity theorem is explicitly separated from claims proved here.
Direct new-module Lean check passes.  Final targeted SOTA build passes `9513/9513`.  Nine capstone
axiom surfaces are only `propext`, `Classical.choice`, and `Quot.sound`; forbidden declaration scan
is clean.  Repository lint reaches new module and remains red on 22 unrelated shared-tree
unreachable modules.  Other agents' Lean process was left untouched; no stale owned process remains.

## S68. Mangoldt atoms lock cofinally to unique Suzuki apices; pointwise seam cells fail (2026-07-22)

S67 isolated turning seam and proposed paying each remaining atom from positive-volume part of its
pointwise value-dominating superlevel.  Hostile test now proves this representation impossible on
an unbounded actual-source family.

Set

```text
L_2=log 2,
a_n=(1/2)log(2n),
tau_n=2log n,
A_n(t)=exp(t/4)R_(L_2,a_n)(t/2).
```

Split channel into fixed and moving terms

```text
F_L(t)=2exp(t/4)max(0,L-t/2),
M_(L,a)(t)=exp(t/4)max(0,L-|t/2-(2a-L)|).               (S68.1)
```

For `0<L<2`, exponential tilt leaves moving term with unique maximum at
`c=4a-2L`.  If `t>c`, writing `x=(t-c)/4>0` gives exact strict comparison

```text
L-2x < L(1-x) < L exp(-x),                              (S68.2)
```

while left branch is strict from exponential monotonicity.  Same argument proves
`F_L(t)<2L` for every `t>0`.  At `a_n`, logarithm law gives

```text
c=4a_n-2L_2=2log n=tau_n.                               (S68.3)
```

For `n>=4`, fixed and moving positive supports are disjoint and moving apex is at least `2L_2`.
Therefore Lean proves exact rigidity

```text
t>0 and A_n(tau_n)<=A_n(t)  iff  t=tau_n.               (S68.4)
```

Every pointwise-dominating target set is contained in singleton `{tau_n}`, hence is Lebesgue null.
But at a prime power

```text
w_n=2Lambda(n)/n>0.                                     (S68.5)
```

Thus no same-mass target cell exists.  Formal corollary takes `n=2^k`, `k>=2`, so obstruction is
cofinal and cannot be removed by starting RH criterion farther out.

Verdict: `SUZUKI-TURNING-SEAM-BICAUSAL-SPLICE` is **falsified in per-atom pointwise form**.  This is
not merely past/future interval overlap: arbitrary non-interval adaptive cells still live in a null
superlevel.  Positive survivor is source-aligned unique-apex rigidity `(S68.3)--(S68.5)`.

The stronger live conjecture is `SUZUKI-APEX-BLOCK-TRANSPORT`: group apex and flank atoms before
comparison, derive nonnegative aggregate block surplus, enforce capacity one only after grouping,
and retain unused completed-kernel mass for fixed Gamma boundary charge.  Individual same-channel
payment is now forbidden architecture.  If block surplus cannot be derived directly, restricted-
Weil/Robin boundary current must produce it; defining surplus from target RH deficit is circular.

Scientific artifacts:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-mangoldt-apex-lock-rigidity.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-mangoldt-apex-lock-rigidity.md`;
- `docs/drafts/pipeline/5-failed/suzuki-pointwise-turning-seam-cell-transport.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiMangoldtApexLock.lean`;
- `docs/drafts/pipeline/1-in-progress/suzuki-positive-arch-mangoldt-quadrature-deficit.md`.

Generic strict-max/null-superlevel mechanism is standard and not claimed new.  Corpus audit and
primary-source audit of Suzuki arXiv:2606.09096 and Groskin arXiv:2607.02828 found no matching
Mangoldt aperture-lock theorem; external priority remains unverified.  Direct source check passes.
Final targeted SOTA build passes `9514/9514`.  Nine capstone axiom surfaces are only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden declaration scan is clean.  Repository lint reaches
new module and remains red on 23 unrelated shared-tree unreachable modules.  No stale owned
Lean/lake process remains.

## S69. Sharp width-five source blocks have unbounded seam-scale surplus (2026-07-22)

S68 forced blocks but left a genuine scale objection: the sharp width-`log 2` dyadic flank surplus
is only `Omega(n^(-1/2))`, while a fixed-width moving-apex seam has `sqrt(n)` height.  Optimizing a
single atom cannot close that gap.

New universal law: for

```text
R_(beta,L)(d)=exp(beta d)(1-d/L),  0<=d<=L,
```

if `beta L<1`, then `R_(beta,L)` is strictly decreasing.  More sharply, for every tail `[r,L]`,

```text
(∀ d in [r,L], R_(beta,L)(d)<=C) iff R_(beta,L)(r)<=C.          (S69.1)
```

Thus the left endpoint is the exact least tail ceiling.

Set

```text
L5=log 5,  a5(n)=log(5n)/2,
P_n={p prime:2n<p<=5n},
q5=sqrt(2)(1-log(2)/log(5)).                                  (S69.2)
```

Exact aligned sampling plus `(S69.1)` gives `0<q5<1`, sharpness on the full continuous tail, and

```text
A_n(2log p)<=q5 A_n(2log n)  for every p in P_n.               (S69.3)
```

Formalized Chebyshev bounds yield symbolically, for every natural `n>=exp(20)`,

```text
sum_(p in P_n) 2log(p)/p >= 1/10.                              (S69.4)
```

Therefore the actual-prime source surplus satisfies

```text
S5(n)>=((1-q5)/10)sqrt(n)log(5)>0.                             (S69.5)
```

Lean also proves `S5` unbounded.  This closes source scaling: the new block is on the `sqrt(n)`
seam scale, not the vanishing single-flank scale.  It does not prove RH.  Exact remaining open core
is target-capacity domination of `(S69.5)` by disjoint completed-kernel blocks while reserving Gamma
boundary mass.  Sharpness of `q5` rules out improving the coefficient on the same continuous tail;
next attack must change target/block geometry or exploit additional completed-kernel structure.

Scientific artifacts:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-mangoldt-macroscopic-prime-block-surplus.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-mangoldt-macroscopic-prime-block-surplus.md`;
- `formal/GaloisForLFunctions/HTGeometry/TiltedTentRightFlank.lean`;
- `formal/GaloisForLFunctions/RHTower/SuzukiMangoldtMacroscopicPrimeBlock.lean`;
- `docs/drafts/manuscripts/suzuki-mangoldt-uniform-dyadic-block-surplus/main.tex`.

Internal and primary-source novelty audit found no matching Suzuki-aligned macroscopic block
theorem; external priority remains unverified.  Direct source checks pass.  Six audited capstone
axiom surfaces are only `propext`, `Classical.choice`, and `Quot.sound`.  Final targeted build
passes `9414/9414`.  Lint no longer reports any module in this four-module theorem chain as
unreachable; global lint remains red on 21 unrelated concurrent modules.  Rendered 10-page paper
is `output/pdf/suzuki-mangoldt-macroscopic-prime-block-surplus.pdf`.  No stale owned Lean/lake
process remains.

## S87. Bivariate marginal trace lock excludes ordinary prime--jet partial trace at every index (2026-07-23)

S86 constructs the signed `SR-40` principal-relative jet current. `SR-42` then proves its negative
index is unbounded, excluding Hilbert and every fixed-index Pontryagin realization. That still
left a seemingly standard infinite-index construction: place one kernel on a product
prime--jet carrier and recover the `SR-40` and `SR-38` blocks as its two coordinate partial
traces. This entire class is impossible.

For a finite kernel `C` on `P × J`, define

```text
Jet(C)(i,j) = sum_p C((p,i),(p,j)),
Src(C)(p,q) = sum_i C((p,i),(q,i)).
```

Finite-sum commutation gives the universal trace-lock law

```text
tr Jet(C)
 = sum_i sum_p C((p,i),(p,i))
 = sum_p sum_i C((p,i),(p,i))
 = tr Src(C).                                          (S87.1)
```

No positivity, Hermitian symmetry, nondegeneracy, inclusion law, or finite-index assumption is
used. Arbitrary mixed entries cannot alter `(S87.1)`.

For the actual aperture-`M` principal-relative current

```text
rho_M(q)
 = sum_(n=2)^(M+1) Lambda(n)/n
     (log(n+1)^q-log(n)^q),
R_(M,N)(i,j)=rho_M(i+j+2).
```

Lean proves, for every `M>0` and `q>0`,

```text
rho_M(q)>0.                                            (S87.2)
```

All summands are nonnegative; source atom `n=2` is strict because
`Lambda(2)/2>0` and `log(2)^q<log(3)^q`. Splitting the diagonal trace at its final jet coordinate
then gives exact flux law

```text
tr R_(M,N+1)=tr R_(M,N)+rho_M(2N+2)
             >tr R_(M,N).                              (S87.3)
```

Suppose two product kernels at jet sizes `N` and `N+1` had these jet marginals and same source
marginal `B`. Equation `(S87.1)` would force

```text
tr R_(M,N)=tr B=tr R_(M,N+1),
```

contradicting `(S87.3)`. Since `B` is arbitrary, Lean specializes directly to every finite
pullback of actual coherent odd Gamma--Jacobi residual
`gammaOddJacobiPrimeCoherentResidualKernel`. Thus ordinary partial trace cannot realize
`SR-40` and `SR-38` simultaneously even with arbitrary real kernels, arbitrary mixed block, and
arbitrary negative index.

This is not RH and does not kill every infinite-index Krein connector. It changes exact survivor:
`SR-41` must use a singular, weighted/renormalized, non-trace-preserving cyclic reader or vary its
source marginal with jet cutoff. Such reader must expose positive opening flux
`rho_M(2N+2)` as a boundary channel. It cannot hide flux in mixed block. Ordinary normal partial
trace is now class-completely dead.

Universal law `(S87.1)` is elementary finite-dimensional partial-trace algebra and is not claimed
as externally novel. Corpus search found no prior composition with source flux `(S87.3)`. Exact
von Mangoldt flux, its `SR-38` specialization, and resulting all-index Suzuki completion no-go are
provisional scientific advance pending external specialist novelty audit.

Artifacts:

- `formal/GaloisForLFunctions/HTGeometry/BivariateMarginalTraceLock.lean`;
- `formal/GaloisForLFunctions/RHTower/VonMangoldtBivariateMarginalTraceLock.lean`;
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/von-mangoldt-bivariate-marginal-trace-lock-no-go.md`;
- `docs/drafts/pipeline/3-formalized/von-mangoldt-bivariate-marginal-trace-lock-no-go.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-source-realization-knowledge-ledger.md`.

Formal audit: direct `lake env lean` checks pass for both new leaves. Targeted cached final build
`lake build GaloisForLFunctions.RHTower.VonMangoldtBivariateMarginalTraceLock` passes
`8868/8868`; output contains only pre-existing replayed linter warnings. Repository formal lint
passes with large-file warnings only. Six capstone axiom surfaces use only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden-declaration scan is clean. No stale Lean/lake
process remains.

## S70--S72. Scalar positive transport closes as a no-go; operator source remains (2026-07-22)

S69 proved an unbounded apex-relative prime-block surplus but did not prove that this surplus was
unused target capacity.  The proposed continuum argument tried to pay a width-two future/past seam
from the total two-flank deficit.  Hostile capacity accounting falsifies that interpretation.

For `a<=s`, `h>=0`, `s+h<=b`, and any interval-integrable profile `Phi`, mixed future/past targets
satisfy the universal inclusion--exclusion law

```text
M(Phi)=integral_a^(s+h)Phi+integral_s^b Phi
      =integral_a^b Phi+integral_s^(s+h)Phi.               (S70.1)
```

Hence for every source quadrature `Q`,

```text
M(Phi)-Q-seam(Phi)=capacityOne(Phi)-Q,                     (S70.2)

M(Phi)-Q>=seam(Phi) iff capacityOne(Phi)>=Q.               (S70.3)
```

In the continuum model the one-sided slack equals seam mass exactly.  The proved tilted-tent
identity `D(1/2,2)=16-8cosh(1)>2` remains correct, but `D` is apex-relative deficit, not free
transport slack.  The manuscript promoting it as seam payment is retracted; the exact survivor is
the no-free-splice classification.

The common-shift result still left a broader objection: perhaps arbitrary block transport could
combine the sharp S67 band with S69's unbounded flank surplus.  S72 supplies an explicit
information-class countermodel.  For a moving apex `c`, define the atomless measure

```text
dmu_c/dt=1 outside (c-2,c),
          0 on (c-2,c-1/4),
          8 on (c-1/4,c).                                  (S72.1)
```

Its cumulative mass is monotone and satisfies exactly

```text
t-2<=mu_c((0,t])<=t                                        (S72.2)
```

for every `t>=0`.  It agrees with Lebesgue measure on the whole decreasing flank.  At Suzuki width
two, with

```text
c_a=4a-4,   H_a=2exp(a-1),
A_a(c_a+2x)=H_a exp(x/2)(1-|x|/2),
```

elementary interval bounds give

```text
integral A_a dmu_(c_a)-integral_0^infinity A_a(t)dt
 >=H_a/128.                                                (S72.3)
```

This excess is unbounded.  The completed reserve does not scale with the apex.  Writing

```text
R_a=integral_0^infinity (K_a-A_a)dt-(gamma+log pi)4,
```

the exact common-lag decomposition gives

```text
R_a=integral_0^infinity exp(-t/4)C_(2,a)(t/2)dt
    +rectangularGammaPolarCorrection(2,a).                 (S72.4)
```

Autocorrelation contraction `C_(2,a)(t/2)<=C_(2,a)(0)=4` and the formal Gamma bound imply

```text
R_a<=16+rectangularGammaPolarUniformBound(2).               (S72.5)
```

Choosing the symbolic aperture

```text
a=64(16+rectangularGammaPolarUniformBound(2))+3
```

and using `1+x<=exp(x)` yields the strict completed-lag violation

```text
integral_0^infinity K_a(t)dt
 <integral A_a dmu_(c_a)+(gamma+log pi)4.                  (S72.6)
```

Thus cumulative width-two capacity, atom-size control or atomlessness, and an unbounded untouched
right-flank apex deficit do **not** imply Suzuki's RH-bearing quadrature inequality.  This is a
class-level no-go for the scalar log-Haar/apex-block transport sublane.  It also corrects S69:
that prime-block surplus is a true source theorem, but it is not free capacity without an
independent actual-source identity.

This is not RH, a disproof of RH, or a no-go for Suzuki's complete screw/operator program.
Suzuki's 2026 paper itself conjectures an operator limit rather than a scalar capacity theorem.
The proposed label `SUZUKI-SOURCE-COMMUTATOR-GRAM` is itself retired after a complete-corpus audit.
The corpus already proves the logarithmic-position/Euler commutator Gram, exact valuation Gamma
Schur translation, compact-support Sonin cyclic descent, and coherent cross-prime covariance.  It
would be another rediscovery, not a frontier.

## S73. Coherent causal response has vanishing gain on exact sharp source (2026-07-22)

The surviving coherent-weld conjecture takes exact gated sharp wall Grams as arithmetic source and
the causal depth-fused field as boundary response.  The exact source formulas expose a previously
unrecorded cofinal scale obstruction.  Let `B_p` be observer-free depth-zero wall amplitude.  For
fixed `h>0`, every aperture `a>0`, height `t`, and prime `p`, Lean proves

```text
|R_(a,t,p)| <= C_h B_p/(p+1),
C_h=(h sqrt(h))^(-1)(1-exp(-(log 2)/4))^(-1).              (S73.1)
```

This is not an asymptotic estimate.  Endpoint factorization has exact observer innovation

```text
EndpointAmplitude(h,a,p,0)
 =B_p (h sqrt(h))^(-1) [p^(-1)/(1+p^(-1))]
   (1-p^(-ha/2))^2,                                      (S73.2)
```

and middle factor is exactly `1/(p+1)`.  Exact causal Möbius resolvent has radius at most
`exp(-(log 2)/4)<1`, giving `(S73.1)` by reverse triangle inequality.

At prime moving-wall aperture

```text
a_p=(log p+1)/2,
```

four-tent autocorrelation gives, for `log p>=1`,

```text
suzukiRectangularWallGramGate(1,a_p,p,0)=1,               (S73.3)
sharp wall diagonal=B_p^2.                                (S73.4)
```

Thus response loses a reciprocal-prime order while exact sharp source loses none.  The formal
cofinal theorem is

```text
for every M>=0 and height t,
there exists prime p with M |R_(a_p,t,p)| < B_p.           (S73.5)
```

Therefore coherent causal fusion is not a uniformly frame-equivalent image of sharp wall source.
Bounded/frame-preserving interpretations of `SUZUKI-COHERENT-FUSION-GAMMA-WELD` are false.  Any
surviving Robin--Gamma identification must use a closed unbounded, cutoff-dependent relative
observation with at least linear prime gain; at energy level required amplification is at least
quadratic in `p`.

The exact live frontier is now

```text
SUZUKI-COFINAL-UNBOUNDED-GRAPH-FLOOR:
construct and prove closability of forced unbounded sharp-source recovery on actual
Sonin/Robin--Burnol graph; prove Connes finite part survives this graph and has one
cutoff-uniform lower floor; then invoke the formal completed-flux endpoint to prove RH. (S73.6)
```

Failure of closability, trivial common finite-part domain, or unavoidable trace defect unbounded
below would instead give a source-complete no-go for current coherent Suzuki weld.  Any construction
factoring only through `(S72.2)`, apex surplus, a fixed Hilbert--Schmidt probe, bounded causal
recovery, or another abstract Gram is formally ruled out or already present in corpus.

Scientific artifacts:

- `formal/GaloisForLFunctions/HTGeometry/BicausalDisplacementOverlap.lean`;
- `formal/GaloisForLFunctions/RHTower/SuzukiBicausalNoFreeSplice.lean`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCriticalApexVacuumCapacityNoGo.lean`;
- `formal/GaloisForLFunctions/RHTower/SuzukiCoherentResponseGainNoGo.lean`;
- `docs/drafts/pipeline/1-in-progress/suzuki-terminal-frontier-ledger.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-coherent-response-gain-no-go.md`;
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-coherent-response-gain-no-go.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-coherent-response-gain-no-go.md`;
- `docs/drafts/pipeline/5-failed/suzuki-continuum-two-flank-surplus-pays-bicausal-seam.md`;
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-critical-apex-vacuum-capacity-no-go.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-critical-apex-vacuum-capacity-no-go.md`.

Direct source checks pass.  S72 and S73 capstone axiom surfaces use only `propext`,
`Classical.choice`, and `Quot.sound`.  Final cached build
`lake build GaloisForLFunctions.RHTower.SuzukiCoherentResponseGainNoGo` passes. Repository lint
reaches S73 but remains globally red on 22 unrelated shared-tree modules missing theorem-area
umbrella imports. No paper is promoted: terminal RH/disproof/full-Suzuki-no-go outcome is still
absent.

## S74. Faithful Sonin normal states carry canonical cyclic prime trace (2026-07-22)

The cyclic/source side of `(S73.6)` was narrower than recorded. Corpus audit found exact
principal-relative shell descent, multiplication closure, and faithful zero/live finite-word
normal forms already formalized in `SoninPrincipalRelativeIdeal.lean` and
`CCMSoninFiniteWordFaithfulness.lean`. Those gates are closed and must not be reopened.

For a live canonical normal window `d=(C,F,x)` at aperture `a>0`, define

```text
tau_a(d)=log(C)-log(F) if x=1, and 0 otherwise; tau_a(0)=0. (S74.1)
```

The new universal Sonin law is

```text
tau_a(s*t)=tau_a(t*s)                                    (S74.2)
```

for the exact tropical state product. If product displacement is not one, both sides vanish. If
first and second displacements satisfy `xy=1`, the reverse overlap is exactly the `x`-dilate of
the forward overlap:

```text
C_(t*s)=x C_(s*t),       F_(t*s)=x F_(s*t).              (S74.3)
```

Thus both products are simultaneously live or zero and logarithmic width is invariant. Faithful
normal-form classification makes `tau_a` invariant under compact congruence. Its finite-support
bilinear extension is cyclic.

On genuine CCM Gram factors this trace diagonalizes exactly:

```text
tau_a(Gram(r,q)) = if r=q then log r else 0.              (S74.4)
```

Therefore a diagonal prime-power scale `r=p^m` returns `m log p`, independently of aperture.
Multiplying by the unsquared Euler coefficient `p^(-m/2)/m` gives

```text
log(p) p^(-m/2),                                         (S74.5)
```

the exact nonarchimedean Connes/Weil orbital coefficient. This is not the old bounded
projection-correction response: orbital growth lives intrinsically in principal logarithmic shell
trace.

The first unresolved connector is now exact:

```text
SUZUKI-PRINCIPAL-RELATIVE-FINITE-PART-WELD:
extend tau_a through the retained Sonin principal-relative ideal, with ordinary trace on its
trace-class part; prove aperture-restriction compatibility; attach the Burnol archimedean finite
part; then prove one cutoff-uniform completed lower floor.                  (S74.6)
```

This advances the source construction but does not prove RH, disprove RH, or finish a full Suzuki
no-go. Targeted inspection of the primary semilocal prolate paper found the Hilbertian Sonin
isomorphism and operator program, not `(S74.1)`--`(S74.4)`; external novelty remains provisional.

Scientific artifacts:

- `formal/GaloisForLFunctions/RHTower/SoninPrincipalShellCyclicTrace.lean`;
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/sonin-principal-shell-cyclic-trace.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/sonin-principal-shell-cyclic-trace.md`;
- `docs/drafts/pipeline/1-in-progress/sonin-log-shell-cyclic-finite-part-descent.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-terminal-frontier-ledger.md`.

## S75. Exact sharp-source domain no-go (2026-07-22)

Novelty is not a terminal criterion. The required outcome remains RH, not-RH, or a
class-complete Suzuki impossibility theorem.

The unbounded-graph escape left by S73 has an additional exact obstruction. The depth-zero
observer-free sharp-wall amplitude is definitionally tied, via equality of its exact square, to
the earlier critical rooted-Bianchi amplitude:

```text
suzukiCriticalEntryWallBareAmplitude(p,0)
  =suzukiCriticalRootedBianchiPrimeAmplitude(p).
```

The corpus had already proved that the right side has nonsummable squared prime norm. The new
connector therefore gives

```text
not Summable_p |BareAmplitude(p,0)|^2,
Summable_p |c BareAmplitude(p,0)|^2  iff  c=0.
```

Hence exact all-prime sharp-source recovery cannot land in an ordinary `ell^2` Hilbert carrier,
even through a closed unbounded graph. This kills the global Hilbert-target reading of the
coherent weld, not merely its bounded/frame-preserving reading. It also prevents a constant
rescaling or finite scalar border from repairing the domain.

This is not a full Suzuki no-go. The surviving mechanism is narrower: finite-cutoff recovery with
a genuinely joint renormalized/semifinite prime--Burnol finite part. Its cutoff-uniform completed
lower floor remains the RH-bearing frontier.

Lean: `formal/GaloisForLFunctions/RHTower/SuzukiCoherentSharpSourceDomainNoGo.lean`.

## S76. Positive cofinal finite parts are impossible (2026-07-22)

S75 left a possible finite-cutoff/semifinite escape. The first hostile question is whether finite
Suzuki Gram positivity can pass to a finite-valued cofinal linear trace. It cannot.

Let `w_i >= 0` be any nonsummable coordinate weight. Suppose a real linear functional `Phi` on
the full coordinate product preserves every finite cutoff:

```text
Phi(1_F) = sum_(i in F) w_i                              (S76.1)
```

for every finite `F`. If `Phi` were positive, then `0 <= 1-1_F` would give

```text
sum_(i in F) w_i = Phi(1_F) <= Phi(1),                   (S76.2)
```

uniformly in `F`. The nonnegative finite-sum criterion would make `w` summable, contradiction.
No continuity or boundedness premise is involved.

There is a stronger lower-floor law. Any linear functional bounded below on its whole
nonnegative cone is automatically positive: a negative value can be multiplied by an arbitrary
positive scalar and driven below the proposed floor. Therefore every exact extension satisfying
`(S76.1)` obeys

```text
for every L, there exists f >= 0 with Phi(f) < L.         (S76.3)
```

The result remains true on an arbitrary linear subdomain `D` provided `D` contains the order unit
`1` and every finite indicator `1_F`. Thus choosing a proper domain does not repair positivity
unless the cofinal unit is excluded or assigned infinite trace.

For Suzuki take

```text
w_p = suzukiCriticalEntryWallBareAmplitude(p,0)^2.        (S76.4)
```

S75 proves that this nonnegative weight is nonsummable. Hence no finite-valued positive linear
functional can preserve all finite critical sharp-source traces, and every unital exact linear
extension is unbounded below on positive prime observables.

This closes a whole interpretation of the surviving weld: finite-level Gram positivity cannot
descend through a positive or globally lower-bounded cofinal finite part. Any remaining Suzuki
mechanism must use a genuinely nonunital semifinite domain and a signed finite part whose lower
floor is asserted only on the source-fixed completed Burnol-resolvent family. That restricted
floor is still RH-equivalent, so no terminal verdict is claimed.

Next exact falsifier: prove that the completed Gaussian-rational/Burnol resolvent test family
forces the cofinal unit into its finite linear domain. S76 would then make its uniform lower floor
impossible and kill the last explicit Suzuki weld. Otherwise construct the proper nonunital domain
and prove the completed floor, which yields RH.

Lean: `formal/GaloisForLFunctions/RHTower/SuzukiCofinalPositiveFinitePartNoGo.lean`.

## S77. No positive finite domain contains a completed Mellin profile (2026-07-22)

The proposed S76 falsifier was too weak: forcing the cofinal unit into the domain is unnecessary.
Positivity at a single nonnegative profile already supplies the required upper bound.

Let `w_i>=0`, let `f_i>=0`, and let a linear domain `D` contain `f` and every finite truncation
`f|_F`. Suppose a finite-valued linear functional preserves the exact finite weighted values

```text
Phi(f|_F)=sum_(i in F) w_i f_i.                          (S77.1)
```

If `Phi` is positive, then `f-f|_F>=0` gives

```text
sum_(i in F) w_i f_i <= Phi(f)                          (S77.2)
```

for every finite `F`. Hence the nonnegative series `sum_i w_i f_i` is summable. This theorem uses
neither an order unit nor continuity, normality, topology, or a regulator. As in S76, a finite
lower bound on the whole positive cone forces positivity by scalar dilation. Therefore whenever
the weighted profile mass is nonsummable, every exact linear extension satisfying `(S77.1)` is
unbounded below on the positive cone of `D`.

The Suzuki specialization lands exactly on the completed Euler source. Transport the critical
sharp mass from exponent `1/2` to actual Mellin abscissa `sigma` by

```text
f_sigma(p)=exp(-(sigma-1/2) log p).                      (S77.3)
```

The corpus source connectors and Gamma--Bianchi displacement law now give, prime by prime,

```text
suzukiCriticalSharpPrimeMass(p) f_sigma(p)
  =suzukiRootedBianchiPrimeMassAt(sigma-1,p)
  =Lambda(p) exp(-sigma log p).                          (S77.4)
```

The already formalized sharp displacement threshold then yields the exact abscissa law

```text
Summable_p [suzukiCriticalSharpPrimeMass(p) f_sigma(p)]
  iff 1<sigma.                                           (S77.5)
```

Every Gaussian-rational profile in the RH-bearing left half-strip has `sigma<1/2`, hence violates
`(S77.5)`. Consequently no positive finite-valued linear functional on any domain—unital or
nonunital—can contain even one such profile, preserve all of its finite Suzuki cutoff values, and
remain positive. Every exact extension containing it is globally unbounded below on positive
observables.

This is stronger than S76 and closes the positive-semifinite interpretation of the completed
Suzuki weld class-completely. Removing the unit, choosing a proper trace ideal, or invoking
semifiniteness does not help: the completed profile itself has infinite positive mass.

This is not yet a proof of RH, not-RH, or a no-go for every signed renormalization. The sole
survivor is now sharply isolated: a **signed, canonically fixed Burnol finite-part anomaly** whose
lower floor is asserted only on the normalized completed profile family, not on its positive conic
or linear closure. Such a floor cannot descend from finite Suzuki Gram positivity. It must come
from an additional source-specific coercivity theorem; without one, it is exactly the existing
RH-bearing endpoint.

Next terminal attack: extend the principal Sonin cyclic functional through the concrete
trace-class relative ideal and Burnol conductor, then determine whether cyclicity and aperture
compatibility uniquely fix the signed anomaly. If they force a lower floor, the formal completed
flux endpoint proves RH. If they force a trace anomaly unbounded below already on the normalized
profile family, the last explicit Suzuki weld is dead.

Lean:
`formal/GaloisForLFunctions/RHTower/SuzukiCompletedMellinPositiveDomainNoGo.lean`.

## S78. Fixed-aperture finite part closes; cofinal relative compatibility is impossible (2026-07-22)

S77 left one explicit signed survivor: extend the Sonin principal shell trace through its exact
trace-class relative ideal, then impose aperture compatibility and attach Burnol's conductor.
The first step now closes, but the second is false in that source class.

For an injective finite prime system, every presentation

```text
T=S_A+K,             K in I_a                              (S78.1)
```

is unique.  Here `S_A` is the canonical principal shell and `I_a` is the exact Sonin
principal-relative ideal.  Every `K in I_a` is Schatten-1, so the unique signed finite part is

```text
FP_a(T)=sum_i A_ii log(p_i)+Tr(K).                        (S78.2)
```

For the actual finite Gram combination `O_A`,

```text
FP_a(O_A)=sum_i A_ii log(p_i)+Tr(O_A-S_A).                (S78.3)
```

Thus representative ambiguity and fixed-aperture trace construction are no longer open.

The aperture parameter is not a unitary gauge.  For the exact ambient Sonin projection
correction `C_a`, the corpus identity and unitary invariance give

```text
||C_a||_HS^2=8a^2,
(exists unitary U, U C_a U*=C_b)  iff  a=b,   a,b>0.      (S78.4)
```

Canonical comparison is nested restriction.  If `a<=b`, then `Q_bQ_a=Q_aQ_b=Q_b`, and the exact
quadratic prime-corner defect is

```text
G_b(p,q)-Q_bG_a(p,q)Q_b
  =Q_bD_p(Q_a-Q_b)D_qQ_b.                                (S78.5)
```

On the diagonal, with `X_(a,b,p)=(Q_a-Q_b)D_pQ_b`,

```text
G_b(p,p)-Q_bG_a(p,p)Q_b=X_(a,b,p)* X_(a,b,p)>=0.         (S78.6)
```

This is not a new trace-class residual.  In every crossing chamber

```text
0<a<b<p a,
```

an explicit orthonormal inverse-dilated shell sequence gives

```text
1<=||X_(a,b,p)-K||       for every compact K.             (S78.7)
```

Hence both `X_(a,b,p)` and its positive Gram square `(S78.6)` are noncompact.  Finally, for every
strict pair `0<a<b`, choose `n>b/a` and a prime `p>=n`.  Then `b<p a`, so `(S78.7)` applies at a
genuine prime.  Therefore

```text
for every 0<a<b, there exists prime p such that
G_b(p,p)-Q_bG_a(p,p)Q_b is not in I_b.                   (S78.8)
```

This gives a definitive negative verdict on the previously sole principal-relative cofinal
class: **no strict aperture enlargement preserves all prime corners modulo the exact Schatten-1
relative ideal**.  Neither unitary conjugacy nor ordinary relative trace can implement the needed
compatibility.

The positive survivor forced by the obstruction is also exact.  At the S78 stopping point, a
remaining Suzuki proof had to place the noncompact lost-aperture layers in a principal algebra and
extend the logarithmic reader. S79 below closes that gate: the layers are existing live shells and
their mass is conserved. The remaining RH-bearing assertion is the signed completed lower floor
after the trace-class curvature/Burnol weld. S78 does not itself prove RH, not-RH, or a
class-complete no-go for every possible enlarged principal algebra.

Lean:

- `formal/GaloisForLFunctions/RHTower/TraceClassCyclicity.lean`;
- `formal/GaloisForLFunctions/RHTower/SoninPrincipalRelativeTraceSplitting.lean`;
- `formal/GaloisForLFunctions/RHTower/SoninApertureRestrictionDefect.lean`;
- `formal/GaloisForLFunctions/RHTower/SoninApertureAreaRigidity.lean`;
- `formal/GaloisForLFunctions/RHTower/SoninPrincipalRelativeApertureNoGo.lean`.

Research records:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/sonin-principal-relative-trace-splitting.md`;
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/sonin-aperture-area-rigidity-and-restriction-defect.md`;
- `docs/drafts/pipeline/1-in-progress/sonin-log-shell-cyclic-finite-part-descent.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-terminal-frontier-ledger.md`.

## S79. Aperture restriction conserves principal orbital mass (2026-07-22)

S78 proved that strict aperture restriction exits the trace-class relative ideal.  The resulting
noncompact layer does not, however, require a new principal trace or a compensating archimedean
mass.  Exact normal-state reduction closes that possible obstruction positively.

For `0<a<b<r*a`, let

```text
S(s,t)=(A_t-A_s)+(R_t-R_s)
```

be the two-polarization shell.  At aperture `b`, the retained, lost, and total scale-one live
windows have exact operators

```text
W_keep  =S(b,r*a),
W_lost  =S(r*a,r*b),
W_total =S(b,r*b).                                      (S79.1)
```

Shell telescoping is an exact operator identity:

```text
W_total=W_keep+W_lost.                                  (S79.2)
```

The faithful Sonin cyclic reader gives logarithmic width on each scale-one live window.  Hence

```text
tau(W_lost)=log(b)-log(a),                               (S79.3)

tau(W_keep)+tau(W_lost)
  =[log(r*a)-log(b)]+[log(b)-log(a)]
  =log(r)
  =tau(W_total).                                        (S79.4)
```

Thus aperture enlargement transfers principal mass from the retained shell to a noncompact lost
shell but creates no net source anomaly.  The transferred mass is independent of `r` and is the
exact additive cocycle

```text
c(a,c)=c(a,b)+c(b,c),     c(a,b)=log(b)-log(a).          (S79.5)
```

The operator restriction defects themselves satisfy the stronger exact compressed law

```text
Delta(a,c;r)=Delta(b,c;r)+Q_c Delta(a,b;r) Q_c.          (S79.6)
```

In one common strict crossing chamber they are ordinarily additive modulo the concrete
principal-relative ideal.  Therefore

```text
Kappa(a,b,c;r)
 =Delta(a,c;r)-Delta(a,b;r)-Delta(b,c;r)                 (S79.7)
```

is Schatten-1.  The principal aperture quotient is flat and conserves exact prime orbital mass;
all remaining path dependence is the ordinary scalar `Tr Kappa`.

This materially narrows the terminal Suzuki problem.  Do not reconstruct an enlarged aperture
algebra or ask Burnol's conductor to cancel `(S79.3)`: both are wrong targets.  The exact live edge
is now

```text
compute Tr Kappa on actual semilocal source packets
  -> compare with the cutoff-dependent Burnol conductor counterterm
    -> either exact signed completed finite part and uniform lower floor (hence RH),
       or an explicit normalized source sequence unbounded below (terminal weld no-go). (S79.8)
```

S79 is significant progress but not a terminal verdict.  It falsifies the enlarged-reader
obstruction and removes all noncompact principal aperture ambiguity; it does not compute
`Tr Kappa`, prove the completed floor, disprove it, prove RH, or retire every Suzuki mechanism.

Lean:

- `formal/GaloisForLFunctions/RHTower/SoninApertureRestrictionDefect.lean`;
- `formal/GaloisForLFunctions/RHTower/SoninApertureCyclicMassConservation.lean`.

Research records:

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/sonin-aperture-principal-cyclic-mass-conservation.md`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/sonin-aperture-principal-cyclic-mass-conservation.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-terminal-frontier-ledger.md`.

## S80. Aperture curvature is a faithful negative square with exact Ward transgression (2026-07-22)

S79 left `Tr Kappa` as an unknown scalar.  It is now computed exactly and carries no independent
sign freedom.

For `0<a<b<c<r*a`, put

```text
L_(a,b)=Q_a-Q_b,
Z_(a,b,c;r)=L_(a,b)D_rL_(b,c),
D_r=U_r+U_r^*.
```

Successive layers are orthogonal.  The exact compressed defect cocycle and positive Gram
factorization give

```text
Kappa=Q_c Delta_(a,b;r)Q_c-Delta_(a,b;r),
Delta_(a,b;r)=Y^*Y,
Y(1-Q_c)=Z_(a,b,c;r).                                  (S80.1)
```

Although `Y` is noncompact, the curvature is Schatten-1.  Compression-trace cyclicity therefore
forces `Z^*Z` to be Schatten-1 and `Z` to be Hilbert--Schmidt.  The scalar curvature is

```text
Re Tr Kappa=-||Z_(a,b,c;r)||_HS^2<=0.                  (S80.2)
```

The trace is faithful on this special curvature:

```text
Re Tr Kappa=0
 iff Kappa=0
 iff Z_(a,b,c;r)=0.                                    (S80.3)
```

Thus zero scalar curvature is not a cancellation among hidden trace-class blocks; it is literal
aperture functoriality.

There is also a canonical positive transgression.  Symmetrize the successive transition,

```text
X=Z+Z^*.
```

Its lower boundary across the first layer is exactly `Z^*`.  The two-corner Ward identity yields

```text
||[X,L_(a,b)]||_HS^2=2||Z||_HS^2,
2 Re Tr Kappa+||[X,L_(a,b)]||_HS^2=0.                  (S80.4)
```

Equation `(S80.4)` is the exact universal aperture Ward-curvature law.  It resolves the first
arrow of `(S79.8)`: there is one forced positive counterterm, equal to half the canonical Ward
energy.

This does **not** yet identify Suzuki's concrete Burnol counterterm.  Corpus audit shows the raw
Burnol conductor edge is bounded but generally noncompact, while `Z` is the Hilbert--Schmidt
relative remainder after principal mass subtraction.  Literal operator equality is therefore the
wrong target.  The exact remaining connector is

```text
relative finite part of the concrete Burnol conductor
 = (1/2)||[Z+Z^*,L_(a,b)]||_HS^2                       (S80.5)
```

on the common semilocal source graph, followed by the cutoff-uniform completed co-Poisson lower
floor.  Failure of `(S80.5)` kills the current coherent Burnol weld; success removes aperture
curvature but still leaves the RH-bearing source floor.

S80 is not RH, not a disproof of RH, and not a full Suzuki impossibility theorem.  It prevents
another loop: do not recompute `Tr Kappa`, search for its sign, or invent a second aperture
counterterm.

Lean:

- `formal/GaloisForLFunctions/RHTower/TraceClassCompressionCurvature.lean`;
- `formal/GaloisForLFunctions/RHTower/SoninApertureCurvatureTrace.lean`;
- `formal/GaloisForLFunctions/RHTower/SoninApertureWardCurvature.lean`.

Research records:

- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/sonin-aperture-ward-curvature-transgression.md`;
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/sonin-aperture-ward-curvature-transgression.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-terminal-frontier-ledger.md`.

## S81. Ward curvature is globally exact; invariant-trace Suzuki weld is impossible (2026-07-22)

S80 left open whether a canonical invariant relative finite part of Burnol's edge could return the
positive Ward energy. Two exact universal laws settle that proposal negatively and remove scalar
aperture curvature from RH-bearing frontier.

First, aperture curvature obeys operator Bianchi. For `0<o<a<b<c<r*o`,

```text
Kappa(o,b,c)+Kappa(o,a,b)=Kappa(o,a,c)+Kappa(a,b,c).    (S81.1)
```

Combining `(S81.1)` with `Re Tr Kappa=-||Z||_HS^2` gives exact quadrilateral conservation:

```text
||Z(o,b,c)||_HS^2+||Z(o,a,b)||_HS^2
 =||Z(o,a,c)||_HS^2+||Z(a,b,c)||_HS^2.                 (S81.2)
```

Hence base-aperture potential

```text
B_o(a,b)=||Z(o,a,b)||_HS^2                              (S81.3)
```

integrates scalar curvature:

```text
Re Tr Kappa(a,b,c)+B_o(a,b)+B_o(b,c)-B_o(a,c)=0.        (S81.4)
```

Changing base from `o` to `p` is exact vertex gauge,

```text
B_o(a,b)-B_p(a,b)=V_(o,p)(b)-V_(o,p)(a),
V_(o,p)(x)=||Z(o,p,x)||_HS^2.                           (S81.5)
```

Thus scalar aperture curvature has zero cohomology class on every ordered chamber. It is not an
independent global obstruction.

Second, exact Fourier parity separates cancellation from RH orientation. Let `J` be cosine
Fourier involution. Sonin projection, symmetric dilation sum, successive transition, and Ward
channel are Fourier-even:

```text
JQ_a=Q_aJ,  JD_r=D_rJ,  JZ=ZJ,  J(Z+Z^*)=(Z+Z^*)J.     (S81.6)
```

The forward-minus-inverse bilateral holonomy used by Burnol/co-Poisson orientation is

```text
H_(a,r)=U_rQ_aU_r^*-U_r^*Q_aU_r,
JH_(a,r)J=-H_(a,r).                                     (S81.7)
```

Therefore every complex-linear reader `Phi` invariant under Fourier conjugation satisfies

```text
Phi(JTJ)=Phi(T)  for all T  ->  Phi(H_(a,r))=0.          (S81.8)
```

Together with exact Ward energy

```text
||[Z+Z^*,L_(a,b)]||_HS^2=2||Z||_HS^2,                  (S81.9)
```

Lean proves sharp no-go equivalence

```text
Phi(H_(a,r))=||[Z+Z^*,L_(a,b)]||_HS^2
 iff Z=0
 iff Kappa=0.                                           (S81.10)
```

This is a terminal verdict for one precise surviving class: **no Fourier-invariant complex-linear
relative trace can turn bilateral Suzuki holonomy into the positive Ward counterterm except when
there is no curvature to cancel.** The proposed `(S80.5)` invariant relative-trace weld is dead.

This is not RH, not a disproof of RH, and not a whole-Suzuki impossibility theorem. It identifies
the only remaining kind of reader: fibre-pointed, with Fourier reflection exchanging distinct
character fibres `w` and `1-conj(w)` rather than averaging them. Corpus realization is Burnol's
co-Poisson Berezin diagonal. Its right-half annihilator sign is now the single live Suzuki edge;
proving it from explicit source sums proves RH, while an unavoidable opposite-sign source square
would kill that final co-Poisson contraction.

Lean:

- `formal/GaloisForLFunctions/RHTower/SoninApertureWardPotential.lean`;
- `formal/GaloisForLFunctions/RHTower/SoninApertureFourierParityNoGo.lean`;
- supporting exact energy equality in
  `formal/GaloisForLFunctions/RHTower/SoninApertureWardCurvature.lean`.

Research records:

- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/sonin-aperture-ward-cohomology-fourier-parity-no-go.md`;
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/sonin-aperture-ward-cohomology-fourier-parity-no-go.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-terminal-frontier-ledger.md`.
- `docs/drafts/pipeline/1-in-progress/suzuki-source-realization-knowledge-ledger.md`.
- `docs/drafts/pipeline/1-in-progress/critical-half-weight-copoisson-cocycle-unitarization.md`.

## S82. Resolved Euler Ward--Schur capacity law kills bounded channel mixing (2026-07-22)

The prime--Gamma source programme ended at a request for infinite-rank off-diagonal incidence
which converts inverse-log balanced Cauchy packets to positive-log Mellin jets while preserving
Euler source law. Two ambiguous escape routes remained: call incidence “channel-resolved” while
mixing channels, or let one fixed Gamma conductor pay all off-diagonal energy. Both are now closed.

Let `P_i` be coordinate projection on arbitrary complex channel space `I -> C`. For any complex
linear map `T`, Lean proves exact commutant classification

```text
T P_i=P_i T for every i
 iff
(T x)(i)=x(i)(T e_i)(i) for every x,i.                 (S82.1)
```

Thus literal preservation of every resolved Euler channel is exactly diagonal action, without
finite-dimensional or continuity assumptions. In particular `i!=j` implies `(T e_j)(i)=0`.

For finite channel matrix `A`, set

```text
Omega_i(A)=A P_i-P_i A,
E_comm(A)=sum_i ||Omega_i(A)||_F^2,
E_off(A)=sum_(i!=j)|A_ij|^2.
```

Direct commutator expansion gives incoming and outgoing corners. Summing them proves exact
resolved Ward law

```text
E_comm(A)=2 E_off(A),                                  (S82.2)

E_comm(A)=0
 iff every Omega_i(A)=0
 iff A is diagonal.                                    (S82.3)
```

This composes with already formalized positive-log obstruction. If a prime-channel incidence
commutes with every resolved prime projection and its forced diagonal realizes `r`th positive-log
Mellin jet, its weighted output energy is nonsummable. Lean packages unconditional nonexistence:

```text
no fully resolved channel-preserving incidence
  + positive-log Mellin-jet realization
  + summable weighted output energy.                   (S82.4)
```

The stronger advance uses actual Gamma cyclic coupling. For finite normalized prime covariance
`K`, coupling vector `u`, fixed scalar conductor capacity `B>0`, and

```text
S=sum_i u_i^2=sum_i R_(p_i),
C_off=sum_(i!=j)K_ij u_i u_j,
W=sum_(i!=j)(u_i u_j)^2,
```

off-diagonal Cauchy--Schwarz and `(S82.2)` prove universal Ward--Schur law

```text
C_off^2<=E_off(K)W,
W<=S^2,

0<=L<=C_off
 -> 2L^2<=E_comm(K)W<=E_comm(K)S^2.                   (S82.5)
```

Existing Gamma Schur-capacity theorem supplies exact positive-block bound

```text
C_off>=S^2/B-S.                                        (S82.6)
```

Therefore, once `S>=B`, Lean proves

```text
E_comm(K)>=2(S/B-1)^2.                                 (S82.7)
```

One-prime Gamma Schur costs are nonsummable. New cofinal Lean corollary states: for every fixed
`B>0` and every `M>=0`, some finite prime packet forces `E_comm(K)>M` for every normalized positive
prime--conductor block. Required channel mixing is not merely nonzero; its resolved Ward energy is
cofinally unbounded.

This changes Suzuki source architecture materially before any zeta zero or co-Poisson annihilator
is read. Three classes are now forbidden:

1. exact commutation with every resolved Euler channel;
2. uniformly Ward-bounded finite-packet off-diagonal incidence;
3. fixed finite scalar Gamma conductor paying completed Schur boundary.

Survivor is narrower: singular or locally finite connection with growing archimedean channel
capacity, or source-fixed principal-relative subtraction of divergent carré-du-champ before target
moments. General containing problem is source-renormalized covariant Dirichlet form relative to
resolved Euler algebra:

```text
FP_F[(1/2)sum_(i in F)||T_F P_i-P_i T_F||_F^2
       -boundaryEnergy(B_F)]
 = completed Euler trace defect,                       (S82.8)
```

with cutoff cocycle and finite part fixed from source data. Any finite part defined from desired
moment difference is circular. Fixed boundary capacity is falsified by `(S82.7)`.

This is genuine source-side frontier progress but not RH, not not-RH, and not whole-lane
impossibility. Exact remaining source question is construction or class-complete refutation of
`(S82.8)` using actual prime--Gamma/co-Poisson principal algebra. Success must retain meromorphic
principal part and yield completed Green--Schur Euler identity; failure for every source-canonical
growing-capacity/principal-relative connection would retire this Suzuki branch.

Artifacts:

- `formal/GaloisForLFunctions/HTGeometry/ResolvedChannelWardLaw.lean`;
- `formal/GaloisForLFunctions/RHTower/PrimeMellinJetResolvedChannelNoGo.lean`;
- `docs/drafts/pipeline/1-in-progress/resolved-euler-channel-ward-mixing-no-go.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-source-realization-knowledge-ledger.md`.

Internal collision audit found generic two-corner Ward identities and Gamma Schur-capacity law,
but no multi-channel factor-two commutator classification composed into cofinal Gamma Ward blow-up.
Universal algebra ingredients are not claimed new to literature; source-specific synthesis and
priority remain externally unaudited.

Formal audit: direct universal-module Lean check passes; targeted cached build
`lake build GaloisForLFunctions.RHTower.PrimeMellinJetResolvedChannelNoGo` passes `8570/8570`.
Formal lint passes with large-file warnings only. Six capstone axiom surfaces use only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden declaration scan is clean. No stale Lean/lake
process remains.

## S86. Source principal subtraction preserves full mixed block cofinally (2026-07-22)

S84 left exact decision problem, not estimate problem. Coupled successor--Bianchi head Gram and
pointed tail Gram each diverge, so ordinary Hilbert limit fails. Question was whether canonical
source principal subtraction loses forced cross term or retains it. Define, for every order `q`,

```text
rho_q=sum_(n>=2) Lambda(n)/n
  *((log(n+1))^q-(log n)^q).                           (S86.1)
```

Lean proves source majorant

```text
|term_q(n)|
 <=4*q*|log(n+1)|^q*(n+1)^(-2),                       (S86.2)
```

hence `(S86.1)` is absolutely summable at every order. This is enough to form canonical relative
current but is not novelty by itself.

Let `W_M`, `B_M`, `S_M`, and `X_M` be finite coupled weld, actual pointed Bianchi tail, successor
Gram, and forced symmetrized cross block. Exact source algebra gives universal finite law

```text
R_M:=W_M-B_M=S_M+X_M,                                  (S86.3)
(R_M)_(i,j)=sum_(n=2)^(M+1) Lambda(n)/n
  *((log(n+1))^(i+j+2)-(log n)^(i+j+2)).               (S86.4)
```

Therefore, for every fixed jet size, whole matrix converges—not merely individual selected
entries—to

```text
R_(i,j)=rho_(i+j+2).                                   (S86.5)
```

This is universal all-order Hankel current:

```text
R(r+1,s)=R(r,s+1).                                     (S86.6)
```

More strongly, cancellation happens before limit at every aperture and admissible depth:

```text
X_M(i+1,j)-X_M(i,j+1)
 =-(S_M(i+1,j)-S_M(i,j+1)).                            (S86.7)
```

Thus hostile possibility “principal subtraction discards mixed block” is false. Raw diagonal
Grams may diverge while their source-fixed relative current is canonical, inclusion-compatible in
aperture, convergent, and exactly Hankel. This closes matrix-entry/cofinal-renormalization part of
`SR-40`.

Sharper frontier is object-level and recorded as `SR-41`. S83 residual is prime kernel after
Jacobi-mode contraction; `(S86.5)` is jet kernel after prime contraction. Adding them is ill-typed
and separate direct sum recreates missing-connector problem. Required new object is one
source-fixed bivariate prime--jet completion whose two marginals are these proved kernels and whose
cyclic reader yields completed Euler multiplication/trace before Xi character or target moment is
read. Generic finite matrix completion or generic Krein decomposition does not count.

This is not RH and not whole-lane no-go. It is source advance: one previously open cofinal
obstruction is resolved exactly and replaced by narrower typed connector. Corpus collision search
across `HTGeometry`, `RHTower`, `HilbertMetric`, proven/formalized/failed cards, and support log
found generic summability and moment-Hankel closure but no von Mangoldt successor relative current
or preservation laws `(S86.3)--(S86.7)`. External priority remains provisional.

Artifacts:

- `formal/GaloisForLFunctions/RHTower/VonMangoldtSuccessorPrincipalRelativeHankel.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/von-mangoldt-successor-principal-relative-hankel-current.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-source-realization-knowledge-ledger.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-terminal-frontier-ledger.md`.

Direct `lake env lean` check passes. Final targeted build, formal lint, and axiom/forbidden scan are
pending together with S83--S84 audit.

## S83. Actual odd Gamma--Jacobi capacity exhausts growing odd-sector floor coherently (2026-07-22)

S82 left growing Gamma boundary capacity as an escape. Its odd/parity-mixing sector now exists
source-canonically.
For actual odd Jacobi coefficient

```text
a_k(t)=(-1)^k c_(2k+1) phi(t) tanh(t)^(2k+1),
```

Lean proves literal integral formula and exact Mercer expansion

```text
int J_(2k+1)(s) sin(ts) dmu_Gamma(s)=a_k(t),
O(t,u)=sum_(k>=0) a_k(t)a_k(u).                        (S83.1)
```

Deleting first `K` modes leaves exactly positive series tail, tending to zero on every source
frequency. For each prime `p`, choose least source rank `K(p)` with

```text
R_p * tail_(K(p))(log p,log p)<=p^(-2).                (S83.2)
```

Then weighted all-prime residual is summable. Prime-dependent ranks do not break coherence:
zero-padding in common absolute odd-Jacobi index gives one cross-prime positive kernel on every
finite packet whose diagonal is exactly `(S83.2)`.

This closes parity capacity and cutoff inclusion. Generic adaptive Mercer/Gram lemma is formal
closure; source advance is exact Gamma coefficient law composed with least primewise schedule and
common-coordinate kernel. It does not place kernel inside completed Green--Schur incidence.

Artifacts:

- `formal/GaloisForLFunctions/HTGeometry/AdaptiveMercerCapacity.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaOddJacobiCapacity.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaOddJacobiCoherentCapacity.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/gamma-odd-jacobi-capacity-saturation-law.md`.

Direct Lean checks pass. Final targeted build/axiom audit is grouped with S84.

## S84. All-order successor curvature and exact finite successor--Bianchi Hankel weld (2026-07-22)

S83 left operator placement. Corpus had successor Dirichlet Gram and pointed Bianchi raw Gram, and
warned their direct sum loses mixed terms. Exact obstruction and positive weld are now proved.

Universal conservative--Hankel rigidity says a shift-balanced kernel with zero zeroth row is zero.
For actual successor source put

```text
v_r(n)=sqrt(Lambda(n)/n)*((log(n+1))^r-(log n)^r),
K(r,s)=sum_n v_r(n)v_s(n),
C_s(n)=Lambda(n)/n*(log(n+1)-log n)^2
       *(log(n+1)log n)^s.                             (S84.1)
```

Lean proves at every order

```text
C_s(n)>=0,
C_s(2)>0,
sum_n C_s(n)<infinity,
K(s+2,s)-K(s+1,s+1)=-sum_n C_s(n)<0.                  (S84.2)
```

Thus no additive ordinary Hankel boundary can repair successor carrier. This is class-complete
for additive Hankel corrections, stronger than prior zero-row mismatch.

Positive survivor uses common source coordinate. On finite aperture and positive jet depth,

```text
d_r(n)=sqrt(c_n)(x_(n+1)^r-x_n^r),
b_r(n)=sqrt(c_n)x_n^r,
h_r(n)=sqrt(c_n)x_(n+1)^r,
d_r+b_r=h_r.                                           (S84.3)
```

`b_r` is exactly actual `x=0` pointed Gamma--Bianchi raw feature. If `X` is forced symmetrized
cross block, Lean proves simultaneously for every finite aperture and jet size

```text
Gram(d+b)=Gram(d)+Gram(b)+X,
Gram(d+b)_(i,j)=sum_n c_n*(log(n+1))^(i+j+2),          (S84.4)
X(2,0)-X(1,1)=-(Gram(d)(2,0)-Gram(d)(1,1))>0.          (S84.5)
```

So finite coupled object is exactly positive moment-Hankel Gram, and mixed block cancels strict
successor curvature. Finite cross-term placement is solved rather than renamed.

Not RH: raw pointed boundary has no ordinary cofinal Hilbert limit. S86 subsequently solves signed
principal-relative matrix completion preserving forced mixed block. Remaining frontier `SR-41` is
joint prime--jet source realization with coherent odd Gamma--Jacobi marginal and completed Euler
trace. Direct-sum or diagonal-only limits are formally excluded.

Artifacts:

- `formal/GaloisForLFunctions/HTGeometry/ConservativeHankelRigidity.lean`;
- `formal/GaloisForLFunctions/RHTower/VonMangoldtAdditiveLogJetHankelCurvature.lean`;
- `formal/GaloisForLFunctions/RHTower/VonMangoldtSuccessorBianchiHankelWeld.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/von-mangoldt-successor-bianchi-hankel-curvature-weld.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-source-realization-knowledge-ledger.md`.

Three-tree/pipeline audit found no prior all-order source curvature law or successor--Bianchi
endpoint weld. Generic algebra is not novelty; source composition is `ADVANCE`, with external
priority provisional. Direct Lean checks pass. Final targeted build, lint, and axiom audit remain
pending.

## S85. Parity-protected Schur floor kills growing even Gamma/Jacobi capacity (2026-07-22)

S82 proved that fixed scalar Gamma capacity cannot pay cofinally divergent resolved Ward cost, but
left growing Gamma/polar boundary capacity as one escape. Corpus audit found two pieces already
known separately: odd Gamma sine kernel and all-even semilocal Jacobi residue tower. Missing
statement was whether arbitrarily many even boundary modes could jointly erase odd source cost.
They cannot.

Let `J` be self-adjoint parity on arbitrary real or complex Hilbert space. For finite packet,
assume

```text
J e_i=e_i,       J o_i=-o_i,       J b_i=b_i,
```

where `b_i` is any correction family in even sector. No common finite-dimensional boundary space,
projection, optimality, or rank bound is assumed. Lean proves exact universal law

```text
||sum_i z_i ((e_i+o_i)-b_i)||^2
 =||sum_i z_i (e_i-b_i)||^2+||sum_i z_i o_i||^2.       (S85.1)
```

Hence every even correction has same capacity-independent odd floor:

```text
||sum_i z_i o_i||^2
 <=||sum_i z_i ((e_i+o_i)-b_i)||^2.                    (S85.2)
```

Proof is forced by parity. Self-adjointness gives
`<e_i-b_i,o_j>=<J(e_i-b_i),o_j>=<e_i-b_i,J o_j>=-<e_i-b_i,o_j>`, so even residual and odd packet
are orthogonal; Pythagoras gives `(S85.1)`.

For actual normalized archimedean Gamma measure, Lean proves literal sine Gram identity

```text
O(t,u):=int sin(ts)sin(us)dmu_Gamma(s)
       =(phi(t-u)-phi(t+u))/2,
phi(t)=(cosh t)^(-1/2).                                (S85.3)
```

For `t,u>0`, this is strictly positive. On prime-log diagonal,

```text
O(log p,log p)=(1-phi(2 log p))/2
 >=c_Gamma:=(1-sqrt(2)/2)/2>0.                        (S85.4)
```

Let `R_p` be actual one-prime Gamma conductor Schur cost from S82. Since `R_p` is nonsummable,
protected residual

```text
E_p=R_p O(log p,log p)
```

satisfies

```text
E_p>=c_Gamma R_p,
not Summable_p E_p,
for every M exists finite prime packet F with
  M<sum_(p in F)E_p.                                   (S85.5)
```

This closes growing reflection-even Gamma/Jacobi boundary capacity as source class, regardless of
dimension. It materially narrows S82 before any zeta zero, Xi character, or desired completed
moment is read.

This is not full Suzuki no-go and not RH. S83 constructs source-derived odd/parity-mixing survivor,
S84 places pointed finite boundary with forced mixed block, and S86 constructs signed cofinal
principal-relative matrix current. Remaining escape is joint prime--jet realization feeding
completed Euler trace; ordinary positive even-sector correction is closed.

General topic exposed is symmetry-protected residual energy in renormalized Schur complements:
counterterms confined to one isotypic sector cannot affect opposite sector, so arithmetic
summability of protected sector becomes decisive source test. Here actual Gamma Schur weights fail
that test.

Collision control is explicit. `(S85.3)` alone and all-even Jacobi tower were corpus-known; only
arbitrary-capacity law `(S85.1)` composed with actual prime divergence `(S85.5)` counts as advance.
Current primary-source audit of Connes--Consani--Moscovici's Gamma/Jacobi framework and Suzuki's
parity-split localized Weil framework found no such composed theorem; novelty remains provisional
pending specialist review.

Artifacts:

- `formal/GaloisForLFunctions/HTGeometry/ParityProtectedSchurFloor.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaEvenBoundaryParityNoGo.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/gamma-even-boundary-parity-floor-no-go.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-source-realization-knowledge-ledger.md`.

Formal audit: direct `lake env lean` checks pass for both new leaves; targeted cached build
`lake build GaloisForLFunctions.RHTower.GammaEvenBoundaryParityNoGo` passes `3588/3588`, compiling
only two new leaves and replaying one cached dependency with pre-existing linter warnings. Formal
lint passes with large-file warnings only. Six capstone axiom surfaces use only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden declaration scan is clean. No stale Lean/lake
process remains.

## S88. True infinite Xi Wiener--Hopf split and RH-equivalent removability law (2026-07-23)

Audit of recent non-diagonal Hardy transport found an exact analytic defect at divisor. Its
“complementary factor” was defined by totalized division

```text
P_nonright(z)=P_Xi(z)/P_right(z).                       (S88.1)
```

At every strict-right Xi zero, numerator and denominator both vanish and Lean assigns `(S88.1)`
value zero. Genuine removable complement is generally nonzero there. Existing pointwise identity
`P_Xi=P_right P_nonright` therefore reduces to `0=0*0` on divisor and does not provide analytic
continuation, differentiation, or global Julia/Schur transport.

Universal infinite repair is now proved. For any nonzero reciprocal-square-summable indexed
genus-one divisor `a_i` and any predicate `p` on multiplicity indices,

```text
P_a(z)=P_(a|p)(z) P_(a|not p)(z),                       (S88.2)
```

with both factors entire and nonzero away from selected divisors. Proof uses independent
multipliability and exact `sumCompl` partition; no enumeration, cutoff, numerical evaluation, or
quotient cancellation occurs.

Specializing `p` to strict-right Xi copies gives genuine entire complement `P_comp` and source
factor

```text
G_comp=Q_Hadamard P_comp,
XiC=P_right G_comp,                                    (S88.3)
G_comp(lambda_q) != 0  for every strict-right q.
```

Hence strict-right factor retains exact Xi analytic multiplicity at every such zero. Lean also
proves old quotient and old source vanish there and differ strictly from genuine factors.

Sharp frontier theorem:

```text
RH ↔ P_nonright is entire
   ↔ old nonright source factor is entire.              (S88.4)
```

Old and genuine factors agree near zero. If old factor were entire, identity continuation would
force global equality, contradicting their divisor values under false RH. Under RH strict-right
divisor is empty and old source equals `XiC`.

This is significant correction, not RH proof. It proves claimed old global Wiener--Hopf
continuation is RH-equivalent, and supplies unconditional analytic replacement. Strongest live
Suzuki obstacle remains source-derived positive Green/Gram factorization of full compound
Xi Bezoutian on recurrence-selected aperture (`SUZUKI-COMPOUND-BEZOUTIAN-GRAM`). That positivity,
not divisor factor analyticity, must now be attacked; using old factor analyticity would assume
endpoint.

Artifacts:

- `formal/GaloisForLFunctions/RHTower/CanonicalProductPredicateSplit.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiTrueWienerHopfFactorization.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/xi-true-wiener-hopf-complement-factorization.md`;
- `docs/drafts/pipeline/1-in-progress/suzuki-source-realization-knowledge-ledger.md`.

Internal corpus novelty: no prior arbitrary-predicate exact canonical split or RH-equivalent
totalized-removability law found. External priority remains provisional. Direct Lean checks and
targeted cached build pass `8850/8850`. Six capstone axiom surfaces use only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden-declaration scan is clean. Global lint is blocked
only by unrelated concurrent umbrella omission: `HTGeometry.LagrangeRemainder` is unreachable from
`HTGeometry`.
