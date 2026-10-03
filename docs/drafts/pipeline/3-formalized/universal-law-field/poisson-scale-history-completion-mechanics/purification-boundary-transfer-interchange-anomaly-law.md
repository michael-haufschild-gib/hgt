# Purification--boundary-transfer interchange anomaly law

- **ID:** `ULF-PBTIA-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-POINH-001`, `ULF-INBSG-001`, P-G98, `DirectSubunitEscapeCapacityFusion`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN INPUTS PROVED] [LEAN CAPSTONE OPEN] [NOT RH]`
- **Lean status:** discovered under read-only Lean audit; capstone not yet formalized

## What was wrong first

`ULF-INBSG-001` proves that singular completion remembers multiplicative scale in its open norm
germ.  That is an exact classifier, but its formula is independent of the spectrum of `T`.
Universality is therefore also a warning: germ equality cannot be declared source-forced merely
because the operator was built arithmetically.

The proposed phrase “subtract the universal metric anomaly and make the residual boundary
vanish” is still ambiguous enough to hide RH.  If the subtraction is allowed to move with the
polarization, there is a canonical choice that makes every scale have the same residual.  Such a
rule proves nothing.

The correct question is an operation-order question:

> Does singular completion commute, up to one counterterm fixed before specialization, with
> closing the source-record observer of the canonical purification?

This card computes the interchange defect exactly and proves both the surviving rigidity and the
moving-counterterm no-go.

## Big-picture law

The one pre-divisor defect `T` has a canonical marked purification `P`.  There are two legal paths:

```text
marked pure source P  --singular completion-->  completed marked source
       |                                         |
       | close source record                     | close source record
       v                                         v
mixed nuclear source T --singular completion-->  completed mixed source.
```

Nonlinear functional calculus and observer closure do not commute.  Their positive square defect
is the completion anomaly.  Every polarization has the same **strong** closed anomaly, but
different polarizations have different **open norm germs**.  Thus:

```text
closed observer  = information-neutral;
open history     = scale-faithful;
interchange defect = location of all transverse information.
```

This makes “universal anomaly” precise: it must be chosen on the pre-divisor square before a
horizontal polarization is supplied.  A counterterm recomputed after specialization is a moving
receiver.

## Corpus audit before construction

`scripts/formal_tools.py research` was run for purification, partial trace/Kraus closure, positive
boundary transfer, Jensen defects, completion anomaly subtraction, and same-boundary transport.
The exact relevant facts are:

- `ULF-POINH-001` supplies `T`, its marked unit purification `Psi`, and
  `Tr_record |Psi><Psi|=T`;
- `positiveBoundaryTransfer` is the actual singular completion
  `F_eps(X)=X(eps I+X)^(-1)`;
- `positiveBoundaryTransfer_tendsto_id` and `norm_positiveBoundaryTransfer_sub_id` prove the
  strong/norm boundary split;
- `positiveBoundaryTransfer_add_smul_inverse_eq_id` gives the exact resolvent defect;
- `gammaSewnCriticalPhysicalPluckerBoundaryPacketTrace_add_smul_inverse_eq_four` is the existing
  packetwise trace shadow of this split;
- `xiWardCubicFormationMetricAnomalyTraceWeight_sub_companion_eq_source` proves independently that
  Route P anomaly subtraction leaves the literal unsquared primitive source charge, not zero;
- `CANNOT-248` already forbids a norm-continuous homotopy that creates the integral wall jump;
- no searched theorem computes the purification/closure interchange square below.

Operator Jensen inequalities and quantum partial-trace monotonicity are known abstractly.  The
argument here needs neither as an input because the rank-one functional calculus is explicit.

## 1. Canonical square

Let `H` be infinite dimensional and let `T` be positive, injective, trace class, and normalized by

\[
 \operatorname{Tr}T=1.                                  \tag{PBTIA.1}
\]

Then `0<=T<=I`.  Let `R` be the source-record Hilbert space and choose the canonical purification
from `ULF-POINH-001`,

\[
 \Psi=\sum_i\delta_i\otimes\alpha_i,
 \qquad P=|\Psi\rangle\langle\Psi|,
 \qquad \operatorname{Cl}(P)=T,                         \tag{PBTIA.2}
\]

where `Cl=Tr_R` closes the source record.  Since `||Psi||=1`, `P` is a rank-one projection.

For `eps,c>0`, put

\[
 F_\varepsilon(X)=X(\varepsilon I+X)^{-1}.              \tag{PBTIA.3}
\]

Here \`cP\` and \`cT\` are algebraic shorthand for aperture dilation only:

\[
 F_\varepsilon(cX)=F_{\varepsilon/c}(X).                \tag{PBTIA.3a}
\]

The literal source objects remain the fixed normalized \`P\` and \`T\`; no source mass, trace, or
coefficient is rescaled.  This distinction is essential: a selectable law cannot be manufactured
by changing the normalization of the source it is meant to test.

The two paths around the square are

\[
 F_\varepsilon(\operatorname{Cl}(cP))=F_\varepsilon(cT)
                                                               \tag{PBTIA.4}
\]

and, because `P^2=P`,

\[
 \operatorname{Cl}(F_\varepsilon(cP))
 =\operatorname{Cl}\!\left(\frac{c}{\varepsilon+c}P\right)
 =\frac{c}{\varepsilon+c}T.                            \tag{PBTIA.5}
\]

Define their interchange anomaly

\[
 \mathcal A_{\varepsilon,c}(T)
 =F_\varepsilon(cT)-\frac{c}{\varepsilon+c}T.           \tag{PBTIA.6}
\]

This is defined from the one pre-divisor purification; no zero, divisor, or target horizon enters.

## 2. Positivity and exact residual

**Theorem PBTIA-A.** For every `eps,c>0`,

\[
 \mathcal A_{\varepsilon,c}(T)\ge0,                    \tag{PBTIA.7}
\]

and the exact subtraction identity is

\[
 F_\varepsilon(cT)-\mathcal A_{\varepsilon,c}(T)
 =\frac{c}{\varepsilon+c}T.                            \tag{PBTIA.8}
\]

Consequently the residual retains every unsquared Kraus/source coefficient and

\[
 \frac{c}{\varepsilon+c}T\longrightarrow T
 \quad\text{in trace norm}.                            \tag{PBTIA.9}
\]

**Proof.**  On a spectral value `0<=lambda<=1`, `(PBTIA.6)` is

\[
 \frac{c\lambda}{\varepsilon+c\lambda}
 -\frac{c\lambda}{\varepsilon+c}
 =\frac{c^2\lambda(1-\lambda)}
        {(\varepsilon+c\lambda)(\varepsilon+c)}\ge0.   \tag{PBTIA.10}
\]

Continuous functional calculus proves `(PBTIA.7)`.  Equation `(PBTIA.8)` is the definition.
Finally

\[
 \left\|\frac{c}{\varepsilon+c}T-T\right\|_1
 =\frac{\varepsilon}{\varepsilon+c}\|T\|_1
 \longrightarrow0.                                    \tag{PBTIA.11}
\]

QED.

This is the operator-level counterpart of the corpus theorem that metric-anomaly subtraction
leaves the unsquared primitive Euler source rather than zero.

## 3. Closed neutrality and open anomaly rigidity

**Theorem PBTIA-B.**  For every `c>0`,

\[
 \mathcal A_{\varepsilon,c}(T)\longrightarrow I-T
 \quad\text{strongly as }\varepsilon\downarrow0.        \tag{PBTIA.12}
\]

Thus the closed anomaly is independent of polarization.  Nevertheless, in the norm-history
corona `Q` of `ULF-INBSG-001`,

\[
 \boxed{
 \|[\mathcal A_{\bullet,c}(T)]-[\mathcal A_{\bullet,d}(T)]\|_{\mathcal Q}
 =\frac{|\sqrt c-\sqrt d|}{\sqrt c+\sqrt d}.}           \tag{PBTIA.13}
\]

In particular,

\[
 [\mathcal A_{\bullet,c}(T)]=[\mathcal A_{\bullet,d}(T)]
 \quad\Longleftrightarrow\quad c=d.                    \tag{PBTIA.14}
\]

**Proof.**  Injectivity gives `F_eps(cT)->I` strongly, while the second term of `(PBTIA.6)` tends
to `T` in norm, proving `(PBTIA.12)`.  Moreover

\[
 \begin{aligned}
 \mathcal A_{\varepsilon,c}(T)-\mathcal A_{\varepsilon,d}(T)
 &=F_\varepsilon(cT)-F_\varepsilon(dT)\\
 &\quad-\left(\frac{c}{\varepsilon+c}
              -\frac{d}{\varepsilon+d}\right)T.
 \end{aligned}                                          \tag{PBTIA.15}
\]

The coefficient on the second line tends to zero, so that history lies in `C_0` and disappears in
`Q`.  Equation `(PBTIA.13)` is therefore `ULF-INBSG-001`, and `(PBTIA.14)` follows. QED.

The anomaly is not an error term around the mechanism.  It carries **all** scale information lost
by the closed observer.

## 4. Exact Poisson complement

Let `psi_t` be the literal Poisson scale histories.  Taking `c=t^2,d=u^2` in `(PBTIA.13)` and
using `ULF-PSH-001` gives

\[
 \boxed{
 \|[\mathcal A_{\bullet,t^2}]-[\mathcal A_{\bullet,u^2}]\|_{\mathcal Q}^2
 +\langle\psi_t,\psi_u\rangle=1.}                       \tag{PBTIA.16}
\]

Thus additive Poisson visibility is exactly the complement of the noncommutation between
purification closure and multiplicatively translated singular completion.  This is now an
operation-order theorem, not merely a coincidence between hyperbolic formulas.

For direct/reflected Euler scales `c=p^a`, `d=p^{-a}`, the oriented anomaly distance is

\[
 C_p(a)=\frac{p^a-1}{p^a+1}
       =\tanh\!\left(\frac{a\log p}{2}\right).           \tag{PBTIA.17}
\]

Hence Burnol holonomy, Gamma paired curvature, likelihood contrast, and Poisson visibility are
four scalar shadows of one interchange square.

## 5. Moving-counterterm no-go

**Theorem PBTIA-C.**  If each polarization is allowed to subtract its own anomaly
`A_(eps,c)`, then every `c>0` has the same trace-norm boundary residual `T`.  Therefore

```text
“anomaly-subtracted residuals have the same boundary”
```

is nonselective unless the anomaly is fixed independently of `c` before specialization.

**Proof.**  Equation `(PBTIA.8)` gives the residual.  For `c,d>0`,

\[
 \left\|\frac{c}{\varepsilon+c}T
       -\frac{d}{\varepsilon+d}T\right\|_1
 \longrightarrow0.                                    \tag{PBTIA.18}
\]

This holds for every pair `c,d`. QED.

This is the exact reason “subtract the universal anomaly” was previously vulnerable to theatre.
Universality cannot mean a formula recomputed from the target polarization.  It must mean one
open germ selected on the theta/source square before the horizontal parameter exists.

## 6. Surviving RH mechanism

Let the pre-divisor theta completion fix the anomaly germ

\[
 \mathfrak A_\Theta=[\mathcal A_{\bullet,1}(T)].          \tag{PBTIA.19}
\]

Call a multiplicative polarization `c` admissible only if its actual completion/observer square
has this same open anomaly germ.  Theorem PBTIA-B then proves

\[
 [\mathcal A_{\bullet,c}(T)]=\mathfrak A_\Theta
 \quad\Longleftrightarrow\quad c=1.                    \tag{PBTIA.20}
\]

Equivalently, functional-equation invariance of the anomaly,

\[
 [\mathcal A_{\bullet,p^a}(T)]
   =[\mathcal A_{\bullet,p^{-a}}(T)],                   \tag{PBTIA.21}
\]

forces `a=0`.  At an actual Xi copy this is `2 Re(rho)-1=0`.

The missing producer is now exact:

> Prove from literal integer/Poisson self-duality that completed Euler formation uses the
> pre-divisor theta anomaly germ `(PBTIA.19)`, rather than the moving polarization anomaly allowed
> by Theorem PBTIA-C.

This is narrower than a source-to-horizon landing: both paths, the purification, the observer, the
singular completion, and the anomaly are explicit on the source side.  It remains unproved.  At
divisor specialization `(PBTIA.20)` is only a classifier.

## Hostile review

- `[ABSTRACTLY STANDARD]` Rank-one functional calculus, partial trace, operator concavity, and
  corona quotients are standard.
- `[NEW EXACT LAW]` The source-specific square `(PBTIA.4)--(PBTIA.6)`, positive formula
  `(PBTIA.10)`, and norm-germ rigidity `(PBTIA.13)` were not found in the corpus or checked
  literature.
- `[REAL ADVANCE]` “Universal anomaly” is no longer verbal: fixed-before-specialization and
  recomputed-after-specialization are mathematically distinct, and the latter is proved
  nonselective.
- `[CORPUS FUSION]` The same theorem explains why Route P anomaly subtraction retains unsquared
  source charge and why strong boundary recovery is blind while norm recovery fails maximally.
- `[LIMIT]` Nothing here proves actual Euler completion uses `A_Theta`.  Calling functoriality or
  functional equation enough to obtain `(PBTIA.21)` would assume the remaining theorem.
- `[FALSIFIER]` If the actual completion is not `F_eps`, if source-record closure is not the
  partial trace of the canonical purification, or if its counterterm may depend on horizontal
  polarization, this selection mechanism fails.

## Literature boundary

Hansen--Pedersen prove general Jensen operator inequalities
(<https://arxiv.org/abs/math/0204049>), and Hiai--Petz place related resolvent functions inside
quantum quasi-entropy monotonicity (<https://arxiv.org/abs/1209.0546>).  Asymptotic morphisms into
operator corona algebras are also established mathematics
(Manuilov, <https://arxiv.org/abs/math/0002142>).  No checked source gives the exact
purification--singular-completion square or its source-specific norm-corona law above.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.PurificationTransferInterchangeAnomaly`, `GaloisForLFunctions.RHTower.PhysicalPluckerInterchangeAnomaly`, `GaloisForLFunctions.HTGeometry.BoundaryHistoryCorona`, `GaloisForLFunctions.HTGeometry.FramePurificationPartialTrace`, `GaloisForLFunctions.RHTower.PhysicalPluckerIntegralNuclearDensity`, `GaloisForLFunctions.RHTower.IntegralNuclearScaleGermOrgans`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.PurificationTransferInterchangeAnomaly` and
`GaloisForLFunctions.RHTower.PhysicalPluckerInterchangeAnomaly` (new), on
`GaloisForLFunctions.HTGeometry.BoundaryHistoryCorona`,
`GaloisForLFunctions.HTGeometry.FramePurificationPartialTrace`,
`GaloisForLFunctions.RHTower.PhysicalPluckerIntegralNuclearDensity` and
`GaloisForLFunctions.RHTower.IntegralNuclearScaleGermOrgans`; all `lake env lean` clean, built,
axiom audit `[propext, Classical.choice, Quot.sound]` only.  `T = normalizedPhysicalPluckerOperator`,
`Ψ = pluckerPurification`, `Cl = IsPartialTrace`, `F_ε = positiveBoundaryTransfer`,
`𝒜_{ε,c} = interchangeAnomaly T c ε`.

| Claim | Lean declaration |
|-|-|
| (PBTIA.1) `Tr T = 1`, `0 ≤ T ≤ I` | `opTrace_normalizedPhysicalPluckerOperator`, `isPositive_one_sub_of_norm_le_one`, `physicalPlucker_canonicalSquare` |
| (PBTIA.2) `P = |Ψ⟩⟨Ψ|` rank-one projection, `Cl(P) = T` | `rankOne_comp_rankOne_self_of_norm_eq_one`, `norm_pluckerPurification`, `pluckerPurification_isPartialTrace`, `physicalPlucker_canonicalSquare` |
| (PBTIA.3)–(PBTIA.3a) `F_ε(cX) = F_{ε/c}(X)` | `positiveBoundaryTransfer`, `positiveBoundaryTransfer_smul` |
| (PBTIA.4)–(PBTIA.5) `Cl(cP) = cT`; `F_ε(cP) = c/(ε+c) P`, `Cl(F_ε(cP)) = c/(ε+c) T` | `IsPartialTrace.real_smul`, `positiveBoundaryTransfer_smul_of_idempotent`, `positiveBoundaryTransfer_smul_rankOne_self`, `isPartialTrace_completion_square`, `physicalInterchangeAnomaly_square` |
| (PBTIA.6) anomaly = defect of the square | `interchangeAnomaly`, `interchangeAnomaly_eq_square` |
| Theorem PBTIA-A, (PBTIA.7), (PBTIA.10) positivity, symbol `c²λ(1-λ)/((ε+cλ)(ε+c))` | `anomalySymbol_eq`, `anomalySymbol_nonneg`, `interchangeAnomaly_eq_cfc`, `interchangeAnomaly_isPositive`, `physicalInterchangeAnomaly_isPositive` |
| (PBTIA.8) residual identity | `positiveBoundaryTransfer_sub_interchangeAnomaly` |
| (PBTIA.9), (PBTIA.11) `‖c/(ε+c) T - T‖₁ = ε/(ε+c)‖T‖₁ → 0` | `traceNorm_residual_sub`, `tendsto_traceNorm_residual_sub`, `tendsto_traceNorm_physicalResidual_sub` |
| Theorem PBTIA-B, (PBTIA.12) `𝒜_{ε,c} → I - T` strongly | `tendsto_interchangeAnomaly_apply`, `tendsto_physicalInterchangeAnomaly_apply` |
| (PBTIA.13), (PBTIA.15) corona distance `|√c-√d|/(√c+√d)`; the residual difference lies in `C_0` | `residualHistory`, `anomalyHistory`, `anomalyHistory_apply`, `residualHistory_sub_mem`, `anomalyGerm_sub_eq_scaleGerm_sub`, `norm_anomalyGerm_sub`, `physicalAnomalyGerm`, `norm_physicalAnomalyGerm_sub` |
| (PBTIA.14) `[𝒜_{•,c}] = [𝒜_{•,d}] ⟺ c = d` | `anomalyGerm_eq_iff`, `physicalAnomalyGerm_eq_iff` |
| (PBTIA.16) Poisson complement | `norm_sq_physicalAnomalyGerm_add_poisson` |
| (PBTIA.17) `κ(pᵃ,p⁻ᵃ) = (pᵃ-1)/(pᵃ+1) = tanh(a log p/2)` | `germContrast_rpow_reflection`, `physicalAnomalyGerm_prime_reflection` |
| Theorem PBTIA-C, (PBTIA.18) residuals of all scales merge in trace norm | `tendsto_traceNorm_residual_sub_residual`, `tendsto_traceNorm_residual_sub` |
| (PBTIA.19)–(PBTIA.21) theta germ selects `c = 1`; reflection invariance forces `a = 0` | `anomalyGerm_eq_theta_iff`, `anomalyGerm_rpow_reflection_iff`, `physicalAnomalyGerm_prime_reflection` |

§6's producer (that completed Euler formation uses the fixed theta anomaly germ) is stated in the
card as unproved; it is not claimed.

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
