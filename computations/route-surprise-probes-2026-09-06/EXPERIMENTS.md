# Short source-intervention experiments

Purpose: discriminate mechanisms at open source gates after surveying all 25 live labels and 35 candidate labels in the frontier, its six primitive gates, and the universal-law constraints. The focused central Hankel proof attempt is paused. No experiment is a proof of RH.

Method: follow `docs/meta/scientific-method.md`. Freeze each experimental hypothesis before evaluation, seek hostile counterexamples, compare with matched controls, and keep any surviving claim distinct from a proved bridge. These are mechanism probes; no new universal primitive or universal law is claimed before the observations justify one. A later primary conjecture must pass the guide's shadow and distance gates.

## E: how an added integer block changes Möbius energy

Corpus inputs: exact Gamma--Hankel/Laplace identity (`MobiusLaplaceGammaHankelWall`), divisibility-supported source births, and confinement of possible escape to a moving cusp (`MobiusIntegerCuspConfinement`). Positivity of energy supplies no upper ceiling. A bounded-return subsequence could feed the existing Mellin/Plancherel endpoint.

**Frozen H1:** For every dyadic `N≥256` and `1.01≤r≤1.5`, the cross energy between the literal Möbius prefix `[1,N]` and its next block `(N,2N]` is nonpositive:

`C_r(N)=Γ(r) Σ_(m≤N<n≤2N) μ(m)μ(n)/(m+n)^r ≤ 0`.

Meaning: new arithmetic coefficients oppose rather than reinforce the old energy. It is suggested by the need for cancellation at source births, not implied by any existing energy or cusp theorem. A positive cross value falsifies this strong local mechanism. It does not disprove a recurrent or collective mechanism, nor RH.

Probe dyadic cutoffs through `2^17`, several fixed `r`, signs and magnitudes of `C`, and the exact balance `E_(2N)=E_N+E_block+2C`. Controls preserve squarefree support: independent sign shuffles within dyadic shells and random multiplicative prime signs. They distinguish literal Möbius structure from sparsity and multiplicativity alone. Use FFT convolution for all additive correlations; independently verify selected integrals in the logarithmic Laplace coordinate. Target <120 seconds per batch.

## O/P: pairwise versus collective prime interference

Corpus inputs: individual outer-prime norm saturation despite pole constraints; strict two-prime norm subadditivity (`CCMRestrictedWeilPrimeInterference`); and full ground positivity still open. Prior ground-energy scans are not repeated.

**Frozen H2:** Pairwise coalitions recover at least half the collective norm saving of the positive weighted outer-prime transport, over apertures `1≤a≤3`. In each finite Legendre compression, define the full saving as `Σ||T_p||-||ΣT_p||`; compare it with the best saving achievable by a partition into pairs and singletons.

Meaning: two-prime incompatibility is the dominant mechanism. A verified finite compression where even the optimal pairing recovers less than half falsifies the compression version. Positive outcomes do not establish the operator statement. Compare basis sizes and actual prime locations with a mass-preserving evenly spaced location control. The quantity being probed is collective structure, not the expected sign of a Weil ground energy. Target <120 seconds.

## CLG/TTF: does tail mass determine the surviving compensation sign?

Corpus inputs: full theta likelihood has an atomic-plus-ray positive spectral measure; the four-face positive cone is formally false; the combined third homotopy compensation survives earlier literal-source tests. Remaining compact source sign still needs a mechanism.

**Frozen H3:** On the structural tail, nonnegativity of the third compensation derivative survives replacing the higher theta likelihood measure by a positive one- or two-atom measure on `[3,∞)` with exactly the same Laplace mass at the left evaluation point `u-t`.

Meaning: total tail mass and its spectral gap, rather than the detailed arithmetic distribution, suffice for this sign. Controls leave the first-atom background fixed and change only the higher-tail measure. This is a risky hypothesis: mass preservation does not preserve higher likelihood moments. Record the first violating configuration and its jets; verify it at increased precision. If false, inspect which coupled moment becomes decisive instead of adding assumptions to rescue H3. This is a probe of a CLG source subproblem, not the paused central Hankel problem. Target <120 seconds.

## Admission and stopping rules

All arithmetic runs on the authorized Runpod. Up to eight independent Python workers, one native linear-algebra thread each. Each batch has a short external timeout; no hour-long job. Record formulas, intervention semantics, basis/cutoff/precision limitations, and reproducible witnesses. Reuse prior solver code only after reading it and checking its source normalization. Do not feed any numerical result into Lean. Do not declare a whole route dead from failure of one mechanism.

Results determine the next conjecture. Do not repeatedly enlarge a grid that yields no discriminating evidence. Reject computations of formal identities, guaranteed positivity, zero-table censuses, and another literal-source C5 sign scan as discovery experiments.

## Adaptive experiments frozen after the first observations

H1 fails numerically already at `N=256`. H2 fails in several finite compressions; at `a=1.4`, basis 40, literal shifts have pairing/full saving ratio about .390, while the evenly spaced control has about .689. H3 survives the tested mass-matched one- and two-atom interventions. These observations motivate changes of representation, not larger repetitions of the original grids.

**H4, frozen before polarization:** the leading small-tail cubic coefficient of the C5 third homotopy derivative has a nonnegative polarized kernel for every triple of spectral nodes in `[3,∞)` on the structural tail. Here the perturbation of `log Z(x)` is the linear Laplace transform of a positive measure normalized at `u-t`. Polarizing the cubic separates mixed contributions that one- and two-atom interventions do not isolate. A negative tensor entry falsifies H4, even if the diagonal cubic remains positive. A surviving kernel would suggest a positive-measure integral mechanism; it would still need an exact proof and control of nonlinear finite-mass corrections. No universal law is yet asserted.

**Prime coalition dissection:** at the anomalous `a=1.4` aperture, examine every subset of the four outer primes, optimal partitions with coalition sizes 1 through 4, and the dominant eigenvector along a mass-preserving deformation of prime shifts to evenly spaced shifts. Compare unconstrained, even-constrained, and odd-constrained modes. This is an exploratory causal decomposition, not a frozen sign claim. Test whether the observed effect is a mode crossing, a discrete resonance, or a smooth many-prime effect. Repeat selected calculations at higher basis size and doubled overlap quadrature. Record the smallest coalition where new norm saving appears. This does not test the complete Weil form.

**Möbius interaction map:** retain H1 as false and inspect the Gram cross energies between separate dyadic source blocks. Measure where a large block's later compensating interaction arrives, with the same squarefree and shell-charge controls. This is exploratory: no cancellation or finite repayment horizon is assumed. Independently validate the H1 witness by direct summation and Laplace quadrature.

**Adversarial follow-up from H4:** polarization has negative `(3,3,g)` entries near the displacement seam, while diagonal values differ by many orders of magnitude. Solve the two-node cubic in its mixture weight, including weights far below .01, then evaluate the original nonlinear mass-matched H3 model at those candidates. Verify with independently differentiated likelihood and compensation at 80 and 120 decimal digits. This attacks the unchanged H3; it does not alter its assumptions. Search for the first boundary crossing and distinguish negativity of one tensor coefficient from negativity of the complete cubic or finite-mass compensation.

**Moment-preserving dissection, frozen after H3 failure:** H3 is now numerically false, independently verified at 80/120 digits. Keep that verdict. Redistribute the tail while preserving successively its first one, two, and three normalized moments in addition to mass; solve the finite moment equations exactly at working precision instead of accepting optimizer constraint residuals. Compute the complete compensation, its three signed channels, the source invariant `F₂F₅−2F₃F₄`, and curvature energy `3F₃²−2F₂F₄`. This exploratory ablation asks which source facts the contaminant destroys. It is not a replacement conjecture or a claim that finitely many moments suffice. A persistent sign failure with matched moments would identify information those moments omit; survival would only motivate a later proof attempt.

**Grouping experiment requested by the user:** test whether primes divide into useful interaction classes at `a=2.2`, where the outer-prime packet has 18 atoms. Compare optimal partitions into groups of size at most 2, 3, or 4 against contiguous-log, interleaved-log, and residue-modulo-6 partitions. Repeat at basis 64/96 and under the evenly spaced shift intervention while retaining the literal weights and prime labels. A useful class must produce a stable, explainable gain; numerical clustering alone is not a classification theorem. This experiment concerns source contributions, not an assignment of zeta zeros to prime classes.

**[BRIDGE] candidate after moment dissection:** every observed negative compensation also has negative lower-transport curvature `H''`, which the literal source excludes by an existing Lean theorem. Examine whether the combined first two channels `-W'''H-3W''H'` remain nonnegative and `W'≤0` under positive Laplace-tail interventions. Those two inequalities, if proved for the actual source, would combine with the existing `H''>0` producer. This is a derived bridge candidate, not a new primary conjecture and not a revision of false H3. Attack it with multi-atom tails, extreme weights, displacements, and homotopy positions.
