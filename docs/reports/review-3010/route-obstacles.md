# Research routes and their mathematical obstacles

Status: 30 October 2026, corpus `00540e1855` plus working tree. **RH remains open.** The inventory is the 32 live routes and 17 candidates of the frontier map, the PW-B branch of PM, and eleven theory programmes that act as routes without a map entry (§4.6).

**The frontier in seven sentences.**

- **The corpus already proves, unconditionally and in Lean, results past the published literature:** the Guth–Maynard large-values theorem, at least \(0.6725\) of zeros simple and critical, at least \(4/5\) of zero ordinates carrying a critical zero, \(0\le\Lambda_{\rm dBN}<1/8\), and complete Weil positivity on atomic families at every fixed overlap.
- **Every route ends at an exact RH receiver, and the receiver space is saturated.** About 2,400 declarations are named as RH equivalences, about 860 modules are named no-gos, and whole-corpus universality laws show that broad classes of certificates collapse onto the same few targets.
- **The decisive quantities are known exactly.** The Weil-kernel index equals the number of zeros right of the line; the Hodge defect of the scaling surface equals the same number; the Hecke state \((nd)^{-s}\) on \(\mathrm{Aff}(\mathbb Q)\) is positive definite iff \(s\ge 1/2\).
- **RH is a critical statement.** The margin of the complete Weil matrix is a positive Fourier tail \(E(c)\asymp c^{-7}\to0\), the restricted ground energy tends to \(0\), the odd form is never subcritical, and no monotone minorant of the truncated Weil spectrum can be nonnegative anywhere without being RH.
- **RH is a square-root statement.** Every criterion implying the count must separate \(a\) from \(a+\varepsilon n^{-\eta}\) for every \(\eta<1/2\), while every producer law the corpus has (PNT, short intervals past \(17/30\)) holds for both.
- **RH is a gauge-specific statement.** Gauge-invariant data certify nothing below \(3/4\) at the trivial point, locality is twin-blind, and uniform positivity over all weights \(|\lambda|\le\Lambda\) is impossible.
- **No route has an input that is critical, square-root precise and gauge-selective at once.** Over \(\mathbb F_q\) one object supplies all three (Frobenius on \(C\times C\)). Over \(\mathbb Z\) the corpus proves why the obvious substitutes fail: infinite genus, Adams jets costing \(2^{qr}\), and a trivial gauge point never better than typical.

Companions: [summary and next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md). Research record: [working log](../../../logs/review-3010-rev3-deep-research-2026-10-30.md).

## How to read this report

Evidence: module docstrings of all theory programmes and RHTower subfolders, `formal_tools.py research` queries, and Lean statements. No builds, axiom audits or compilation checks were run.

| Label | Meaning |
|---|---|
| **[Lean]** | Lean declaration read in this review via the corpus search; integration not assessed. |
| **[map]** | Taken from the frontier map; not re-derived here. |
| **(inference)** | A conclusion of this review, not a Lean theorem. |

**Obstacle classes.**

- **A, just work.** The mechanism exists in the corpus and has already succeeded on a smaller instance: a further certificate, an extension of a proved range below a proved barrier, a composition of proved theorems, or a quantification of a qualitative proof. An A item never promises that a desired sign holds.
- **B, open mathematics.** No mechanism in the corpus or the literature is known to produce the statement. Each B item carries its strength:

| Tag | Meaning |
|---|---|
| **[QRH]** | Implies a zero-free strip \(\operatorname{Re}s>\Theta\), \(\Theta<1\). |
| **[LH]** | Implies the Lindelöf hypothesis. |
| **[FS]** | Implies finitely many off-line zeros, hence LH. |
| **[RH]** | Equivalent to RH. |

**The three properties.** A crossing input must be **C** (critical: valid at zero margin), **P** (precise: square-root precision), and **S** (selective: specific to \(\zeta\) at the trivial gauge point). Each route below names the property it lacks. The unification ledger proves why these three are forced.

## 1. What the corpus proves unconditionally

These are the results every route stands on. All are [Lean].

| Area | Theorem | Content |
|---|---|---|
| Zero density | `Sieve.guthMaynardLargeValuesBound_holds` | The Guth–Maynard large-values theorem; consequences on \(7/10\le\sigma\le8/10\) (`exists_zeroHeightBox_ncard_le_gm_unconditional`). |
| Zero-free region | `Sieve.riemannZeta_ne_zero_vinogradovKorobov` | Vinogradov–Korobov with explicit constant \(10^{-8}\). |
| Critical line | `IncommensurableGaborPinching.simple_critical_proportion_ge_67250071` | At least \(0.67250071-\varepsilon\) of zeros are simple and critical. |
| Ordinates | `Zeta23CriticalOrdinateCensus.four_fifths_critical_ordinates` | At least \(4/5-\varepsilon\) of zero ordinates in \((T,2T]\) carry a critical zero. |
| Heat flow | `DeBruijn.newmanConstant_nonneg`, `newmanConstant_lt_eighth` | \(0\le\Lambda<1/8\). An off-line zero at height \(\gamma\) forces \(\Lambda\gtrsim1/\log\gamma\) (`le_newmanConstant_of_offLine_zero`). |
| Small support | `ArithmeticLorentzianGeometry.eventually_weilQuad_nonneg_of_support` | The Weil form is nonnegative on tests supported within a fixed fraction of the atom spacing. The full Weil floor holds through radius \(181/500\) [map]. |
| Complete matrix | `eventually_tiltedUnitSpline_completeWeilMatrix_posDef`, `..._uniform_boundedOverlap` | The complete atomic Weil matrix is positive definite at every fixed overlap \(c\), uniformly on \(0<c\le K\). |
| Spectrum bottom | `RAPT.tiltedUnitSpline_spectrum_bottom`, `tendsto_tiltedUnitSpline_completedShellEnergy_atTop` | The bottom is the completed shell energy \(E(c)\), attained, and \(E(c)\to0\). |
| Conductor floor | `tiltedConductorEnergy_two_sided`, `ConductorScaleControlsTheCompletedEnergy` | \(c^{-7}\lesssim E_m(c)\lesssim1\) for \(m\le c\); a constant floor for every conductor above the overlap scale. |
| Growing overlap | `eventually_tiltedWeil_growing_packet_pos`; `..._finite_packet_energy_pos_growing_overlap` | Every fixed finite conductor family is positive along \(c_N=(\log N)^\alpha\), \(\alpha<1/40\), and uniformly on \(1\le c\le(\log N)^A\), \(A<1/48\). |
| Reserve | `tendsto_gammaReserve_growing`, `tiltedUnitSpline_complete_defect_reserve_explicit` | The Gamma reserve survives while \(c^8=o(\log N)\); the complete defect reserve has explicit polynomial overlap cost. |
| Selection | `liouvilleSelector_selective_of_signGauge`, `..._of_cofiniteFlip` | At one bounded overlap the selector is strictly positive for \(\zeta\) and rejects every pole-free \(\pm1\) gauge with bounded harmonic sums. |
| Selection | `StripBochnerWeilForcing.completedPositiveSystem_one_one_eq_zeta` | Every completed positive system of pole budget \(1\) and degree \(1\) is a multiple of \(\zeta\). |
| Index | `HeckeKreinToeplitz.negIndex_zetaKernel` | \(\kappa(K_\zeta)=\#\{\rho:\operatorname{Re}\rho>1/2\}\), on any two-prime lattice. |
| Hodge defect | `ArithmeticCastelnuovoSeveri.zeta_hodgeDefect_iff` | The Hodge defect of the scaling surface counts the right zeros. |
| Thresholds | `ArithmeticPositiveDuality.isPosDefOnGroup_heckeState_iff` | The Hecke state is positive definite on \(\mathrm{Aff}(\mathbb Q)\) iff \(s\ge1/2\). |
| Moments | `ThetaCuspOddFourRankEight.thetaCuspCenterMixedSignedHankel_eight_posSemidef` | The size-eight signed theta Hankel section is PSD for every \(0<a<1/2\). |
| \(\mathbb F_q\) calibration | `Stepanov.stepanov_bound`, `EventualHasseWeilIsHasseWeil` | Stepanov's method; a Hasse–Weil bound with any constant is RH for curves. |

## 2. The receiver dictionary is saturated

The corpus proves RH equivalent to positivity, index, count, approximation, convergence and recurrence statements in every studied coordinate system. Examples [Lean]:

- **Index:** `riemannHypothesis_tfae_zetaKernel`; `negIndex_zetaKernel_eq_zero_iff_count` (index zero iff \(\psi(x)-x\le C\sqrt x\log^2x\)).
- **Overlap:** `riemannHypothesis_iff_atomicFamilies_nonneg_of_growth/Two/Pow/Gevrey`; `tiltedUnitSpline_overlap_window` (RH iff positivity at \(c_N=2(\log N)^\alpha\), any \(\alpha>1/4\)).
- **Polarization:** `riemannHypothesis_iff_collided_hecke_invariant`; `hecke_similitude_iff`; `riemannHypothesis_iff_W_eq_collided`.
- **Approximation:** `riemannHypothesis_iff_tendsto_bdDistDiscrete` (Báez-Duarte); one off-line zero \(\rho\) forces distance \(\ge\sqrt{2\operatorname{Re}\rho-1}/|\rho|\) (`bdTarget_dist_floor`).
- **Moments:** `xiCentralMomentHankelDeterminantsPositive_iff_riemannHypothesis`; `riemannHypothesis_iff_heatHankel_nonneg`; `thetaCuspIntegratedNativeSignedCone_iff_riemannHypothesis`.
- **Sieve:** BVI proves every short-window Möbius or prime saving, balanced statistic and uniform Vaughan bound equivalent to a zero-free strip.

Three laws show that adding receivers does not move the frontier:

- **Extension no-go** (`RHTower.extension_forces_positivity`; `ExtensionProgrammeNoGo`). A nondecreasing minorant of \(\lambda(L)=\inf\operatorname{spec}Q_L\) that is nonnegative at one length forces \(\lambda\ge0\) everywhere. Soft tools transport positivity only downward in \(L\).
- **Whole-corpus collapse** (`XiWholeCorpusPositiveSoninApertureCollapseUniversalityLaw`; `GammaDigammaZetaXiSynchronizedReporterBlindnessUniversalityLaw`). The positive and failure phases of whole classes of certificates descend to one intrinsic aperture domain. A single coefficient packet is invisible to every finite-dimensional reporter for \(\Gamma\), digamma, \(\zeta\) and \(\Xi\) simultaneously.
- **Cross-route bridges** (`CrossRouteReceiverBridges`). Lag, spline, bound-state and factorial-grid receivers are identified with one another. The module states that these identifications supply none of the required bounds.

(inference) A receiver is progress only if it changes which of C, P, S the input must carry. No receiver in the corpus does.

## 3. Routes by family

Format: **Mechanism**, **Proved**, **A** (just work), **B** (open mathematics), **Lacks** (which of C, P, S).

### 3.1 The complete Weil matrix and arithmetic Hodge theory

These routes share one object: the complete atomic Weil matrix \(W(\varphi,c,N)\) on \(x\in\mathbb R^N\), atoms \(\varphi((u-\log n)/w)\), \(w=c/N\). Its shared state:

| Regime | Status [Lean] |
|---|---|
| Fixed \(c\) | Positive definite; spectrum bottom \(E(c)\), attained at the pole conductor. |
| Fixed finite conductor packets | Positive for \(c\le(\log N)^{1/48}\) uniformly, along \((\log N)^\alpha\), \(\alpha<1/40\). |
| Mass reserve | Survives while \(c^8=o(\log N)\). |
| RH receiver | \(c_N=2(\log N)^\alpha\), \(\alpha>1/4\). |
| Critical curve | \(E(c_N)\log N\asymp1\); for the tilted spline \(c_N\asymp(\log N)^{1/7}\) (inference). |

The degeneracy sits in the \(\approx c\) conductors \(m\le c\), where \(E_m(c)\) falls to \(c^{-7}\). Above the overlap scale the floor is constant (`ConductorScaleControlsTheCompletedEnergy`).

#### HF — Positive Hodge form on arithmetic cohomology
- **Mechanism:** Full-source sign, zero Hecke defect or subquantum arithmetic work → Hodge index → RH.
- **Proved:** The complete-matrix state above. Hecke invariance of the collided polarization is RH (`riemannHypothesis_iff_collided_hecke_invariant`). The scaling-surface defect is a Hecke similitude, \(\mathrm{defect}(H_ax,H_ay)=a\,\mathrm{defect}(x,y)\) (`defect_heckeCorrespondence`). Tilted single-prime threshold \(\gtrsim(p/\log p)^{1/7}\) [map].
- **A:** Extend complete positivity, including the growing conductors \(m\le c\) and the full complement, from fixed \(c\) to the reserve range \(c\le(\log N)^{1/8-\varepsilon}\). Below the critical curve this needs loss-free bookkeeping of the ratio-prime identity, not a new sign.
- **B [RH]:** Positivity on or past the critical curve. The margin is \(E(c_N)\to0\), and every fixed-relative-loss estimate fails exactly there.
- **Lacks:** C.

#### SRT — Prime-side one-parameter lag localization
- **Mechanism:** Late-lag bound, atomic-family sign, all-generator one-prime sign, or consecutive-ratio tower sign → RH.
- **Proved:** The complete-matrix state; full-index exhaustion by towers; exact flip thresholds [map]. Visibility theory [Lean]: aperture-gain certificates certify width exactly down to \(\beta=1/2\) (`certifies_width_apertureGain_iff`). Fixed-aperture positivity cannot force width zero for abstract configurations (`not_forall_configWidth_eq_zero_of_weil_nonneg_on_aperture`).
- **A:** Push packet positivity from \(A<1/48\) to the reserve exponent. Formalize the Steklov full-index exhaustion [map].
- **B [RH]:** Sign on an RH-complete family. Tower branch [FS]: an arithmetic index ceiling.
- **Lacks:** C, and P for the tower branch.

#### AIP — Arithmetic incidence positivity
- **Mechanism:** Prime incidence plus plateau gauge → all-aperture global incidence allocation → odd positivity ⇔ RH.
- **Proved:** As SRT. Signed-incidence theory (SAEI): frustration is the local–global gap; Kron reduction never creates frustration; the odd Weil ledger is frustrated only by primes; on-line companions pay off-line depth; Paley–Wiener sources pay at Nyquist density [Lean docstrings].
- **A:** Mixed Schur payment from tail energy on fixed blocks; Haar-branch bookkeeping of first-prime, coarse and polar costs.
- **B [RH]:** All-aperture allocation. The frustration of the odd ledger is exactly the prime part, so paying it globally is the signed prime problem.
- **Lacks:** C.

#### ACS — Arithmetic Castelnuovo–Severi effectivity
- **Mechanism:** Full-source effectivity, bounded-error Rosati heights or chirality → Hodge → RH.
- **Proved:** The scaling surface of \(\mathbb Z\) is a polar surface whose defect is the Weil form; Hodge defect \(=\#\)right zeros (`zeta_hodgeDefect_iff`). One generic test with dense shifts sees every right zero (`zeta_cyclic_hodgeDefect_iff`). The defect is finite at every degree. **Infinite-genus law:** no compact test vanishes at every zero, so Weil's form has no radical over \(\mathbb Q\), whereas over \(\mathbb F_q\) the genus is the aperture of the radical. Theta Riemann–Roch \(h^0(d)-h^0(-d)=d\) (`arithH0_riemannRoch`). Adams support threshold \(2^{qr}\), sharp.
- **A:** Census and displacement Gram estimates at fixed degree. The automorphic branch's unfolding and quotient-measure formalization [map].
- **B [RH]:** Quadratic effectivity, i.e. subquadratic \(h^0\) growth on degree-zero classes, or Rosati heights. Over \(\mathbb F_q\) the Castelnuovo constant is \(2g\); over \(\mathbb Z\) there is no finite genus to supply it.
- **Lacks:** P, from infinite genus.

#### RW — Restricted Weil ground energy
- **Mechanism:** Ground minimum \(\mu(A)\ge0\) at every aperture → RH.
- **Proved:** \(\mu\) strictly decreasing; RH iff \(\mu(A)>0\) for all \(A\). Restricted ground energy \(\to0\) at infinite aperture, i.e. Gaussian criticality (ACT). \(\mu(A)\le K\exp((11/2)A-\pi e^{2(A-2)})\), so any aperture floor must decay doubly exponentially (ArithmeticCompensationTheory). \(\neg\)RH forces the restricted floor envelope below the transverse supremum (`restrictedWeilFloor_not_eventually_zero_of_not_rh`).
- **A:** Small-aperture floors at further apertures.
- **B [RH]:** Every aperture. The extension no-go forbids reaching it by monotone continuation.
- **Lacks:** C.

#### EWU and OWU — Even and odd weight uniqueness
- **Mechanism:** Even (odd) blind minimum \(\ge0\) at every aperture → \(\lambda=\Lambda\) → RH.
- **Proved:** Weight rigidity; attained blind minima; odd witnesses separating \(\Lambda\) from Liouville and prime flips at radii \(181/500\) and \(23/40\) (`exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg`). The conductor–forcing gap (`TheConductorForcingGap`): companion forcing and the conductor horizon are incompatible.
- **A:** Further fixed-radius witnesses.
- **B [RH]:** All-aperture sign with reflected-prime and polar payment.
- **Lacks:** C.

#### ACT — Arithmetic criticality / single-shift variation
- **Mechanism:** One fixed theta shift with \(D_a\le2S_a+V_a\) for every even compact profile → odd positivity → RH.
- **Proved:** The Markov form of Riemann's kernel in Doob coordinates (Allegretto–Piepenbrink, Pinchover). The odd form is **never subcritical**. An odd nonnegative supersolution of the folded generator would give RH (`riemannHypothesis_of_foldedSupersolution`). No positive profile is a folded supersolution: it fails at the origin through prime \(2\) and at infinity through the theta harmonic identity.
- **A:** Larger-shift absorption of fixed-support collars.
- **B [RH]:** A positive (super)solution of the full nonlocal generator, not of the folded one.
- **Lacks:** C. The route is the clearest statement of the criticality face.

### 3.2 Prime error, cancellation and counts

These routes read the signed prime or Möbius source. Their shared state:

- **Global law [Lean]:** Index zero iff the one-sided count \(\psi(x)-x\le C\sqrt x\log^2x\) (`negIndex_zetaKernel_eq_zero_iff_count`).
- **Deciding input [Lean]:** Any criterion implying the count must reject Liouville, must separate \(a\) from \(a+\varepsilon n^{-\eta}\) for every \(\eta<1/2\), and cannot be decided on a finite window (`deciding_input_necessary_properties`, `not_of_finite_window`).
- **Producer blindness [Lean]:** \(\Lambda+\varepsilon n^{-\eta}\) satisfies PNT and every short-interval law with \(\alpha>17/30\) (`producers_are_precision_blind`).

#### WL — Weil lag function
- **Mechanism:** Prime lag or deficit → one-sided bound or subexponential critical energy → RH.
- **Proved:** Critical-energy, linear-error and count criteria. Balanced factorial ratios cost \(\log A_n\ge(2\log2-\varepsilon)mn\). Order-\(r\) jet vanishing on the Adams fixed locus forces support \(\ge2^{qr}\), sharply attained. Integer approximate vanishing is exact divisibility [map].
- **A:** Further parity-selective auxiliaries inside the factorial-ratio class.
- **B [RH]:** A signed prime-error bound at square-root precision. The Adams and factorial costs show integrality alone gives Chebyshev precision.
- **Lacks:** P.

#### MC — Möbius cancellation at half power
- **Mechanism:** \(\mu\) or Liouville cancellation at half power, or an odd-parity upper count → RH.
- **Proved [Lean, AGT]:** The Möbius gauge exponent satisfies \(\Theta=\theta_\mu(0)\ge1/2\). The typical exponent is exactly \(1/2\), and RH iff the trivial point is typical. Gauge-invariant majorants are \(\ge3/4\) at \(0\) (`threeQuarters_le_of_gaugeInvariant_bound`). The exponent is not constant on the gauge torus. Uniform Dirichlet zero-free region [map].
- **A:** Level-averaged and conductor-averaged savings (large sieve over the special locus).
- **B [RH]:** The exponent at the one specified point \(0\). Almost-sure and averaged typicality do not control a specified point.
- **Lacks:** S at the trivial point, and P.

#### PBM, RB — Regularized abscissa; Robin/Nicolas
- **Proved:** Convergence of the pole-regularized prime or log-\(\zeta\) series at every \(\sigma>1/2\) is RH. Robin at \(\mathrm{lcm}(1,\dots,n)\) is RH (`RobinLcmRiemannCriterion`). Counterexamples need growing prime cores (`RobinMovingValuationDefect`).
- **A:** Necessary-condition refinements on colossally abundant extremizers.
- **B [RH]:** Square-root-scale remainders on growing extremizers.
- **Lacks:** P.

#### LI — Paired Li and prime–Gamma balances
- **Proved:** RH implies paired Li positivity. Unconditionally the paired Li coefficients are not eventually negative (`not_eventually_re_xiLiPaired_neg`). Guarded zero set finite; RH iff empty [map]. RH is reflection positivity of the Cayley ladder (ArithmeticLorentzianGeometry).
- **A:** Budget computations at finitely many guarded zeros.
- **B [RH]:** The primitive ladder sign.
- **Lacks:** C.

#### JAS, CTF, PM (with PW-B), FU, CFC, RP, PA
- **JAS** (joint ancestry). Proved: positivity at growing logarithmic prime budget [map]. B [RH]: reach the square-root power budget. Lacks P.
- **CTF** (chronological tail, Báez-Duarte). Proved [Lean]: RH iff the discrete Báez-Duarte distance tends to \(0\), plus the Burnol lower bound. Vasyunin reciprocity is a residue-difference energy (BVI). B [RH]: covariance cancellation along compatible cutoffs. Exact dual completion gives only lower bounds. Lacks P.
- **PM / PW-B** (physical model, cusp forcing). Proved: complete-energy and gauge-mass receivers; the escape alternative; compact effective pole orders. Escape completeness: RH iff every escape state is visible. A: remove `XiZeroCopy` indexing from the native two-response action. B [RH]: positive gauge mass for every subcritical limit. Lacks S.
- **FU, CFC, RP** (CCM-indexed prime histories). Proved: exact receivers. CFC: RH iff the published first-clock sine coefficient is bounded below on a tail, and under \(\neg\)RH it is unbounded below. RP: no sublinear history floor exists. The CCM subfolder has 48 no-go modules (gauges, Fock positivity, metric transport, parity selection under an off-line quartet). B [RH]: one complete-history linear floor. Lacks C.
- **PA** (prime–archimedean passivity). Proved: each fixed Hausdorff order is positive at large shift [map]. Several "cofinal Hausdorff diagonal/quadrant forces RH" receivers [Lean]. B [RH]: all orders and all shifts. Lacks C.

#### BAG — Deterministic zeta self-return
- **Proved:** Strong and local recurrence receivers; weak ladders collapse to RH; Voronin universality on small discs (`ZetaVoroninUniversalityOnSmallDiscs`).
- **B [RH]:** Returns near possible zeros. Zero-free-target universality is insufficient.
- **Lacks:** S.

### 3.3 Theta, heat and moments

#### TH — Theta moment positivity
- **Mechanism:** Signed center-mixed theta jets → complete Hankel cone → RH.
- **Proved [Lean]:**
  - Rank seven strict for \(0<a<1/2\) [map]. **Rank eight is PSD for every \(0<a<1/2\)** (`thetaCuspCenterMixedSignedHankel_eight_posSemidef`). The seam is split at \(r_c=\log(5/\pi)\), paid by 15 seam and 8 bulk piece certificates and an exact \(LDL^\top\).
  - The native fibre form is a square plus a null Lagrangian, \(\sum v_iv_jh_{i+j}=|G_v|^2+B_v'\), so the tail form is \(2\int_{y>x}|G_v|^2-2B_v(x)\) (`thetaCuspNativeTailHankelForm_eq_square_sub_flux`).
  - The relaxed fourth-moment concentration holds (`thetaCuspRelaxedFourthMomentConcentration_holds`). The strict low block discharges Hankel sizes \(0,1,2\) (`PrimeArchThetaHankelDegreeTail`).
- **A:** Rank nine, ten, … by the same seam-split piece certificates; each finite rank is a finite certificate.
- **B [RH]:** All ranks at once. The square-plus-flux identity converts this into domination of the center flux \(B_v(x)\) by the bulk \(L^2\) mass of \(G_v\), uniformly in rank.
- **Lacks:** C (rank uniformity).

#### TT, LA, WD — Theta tails, line anchor, Ward collisions
- **Proved:**
  - TT: theta tail and Wold receivers; the windowed aperture modes are Weil box tests. Mixed-horizon modulus \(N^{\kappa-\operatorname{Re}z}M^{\kappa+\operatorname{Re}z}\) [map].
  - LA: \(\xi\) coefficients are Turán [map]. The heat zeros are real and simple beyond \(2\pi\exp((2/3+\varepsilon)/t)\) [map]. Every local heat-zero cluster becomes simple immediately forward in time (`HeatForwardSimpleZeros`).
  - WD: \(\Lambda\le t\) iff no collision mass after \(t\) (`newmanConstant_le_iff_forall_collisionMass_eq_zero`); collisions count the index (HKT).
- **A:** LA/WD: absorb the \(C\log X\) outer vertical energy in localized dissipation, and sum the local estimates for fixed \(t>0\).
- **B [RH]:** Uniform control of \(N(t)\) as \(t\downarrow0\), i.e. \(\Lambda=0\); all-height finite-head signs.
- **Lacks:** C (the heat route is critical at \(t=0\)).

#### HCF, GTA, RN, XN, CHMD
- **HCF** (Gaussian heat trace). Proved: one vertical line of the complex-time heat trace decides RH (`XiGaussianHeatVerticalLineReceiver`); positivity on both \(\log2\) and \(\log3\) grids iff RH; uniform-grid alias no-go. A: finite-degree grid signs. B [RH]: all degrees and heights. Lacks C.
- **GTA** (transverse Schur charge). Proved: exact transverse-charge decay criterion. B [RH]: rank-uniform arithmetic decay. Lacks C.
- **RN** (theta renewal). Proved: compact cone-positive renewal operator with exact regularized determinant. Cone positivity does not imply real spectrum. B [RH]: a directed boundary-work sign. Lacks C.
- **XN** (Newton discs). Proved: coverage criterion, nonnegative Laplacian of the margin. B [RH]: cover every zero. Lacks S.
- **CHMD** (causal hyperbolic–modular duality). Proved: the Weil form on Doob tests is edge energy minus polar energy (`CHMDPolar.W_re_eq_edge_sub_polar`). Finite odd bound-state space iff finitely many off-line zeros (`CrossRouteReceiverBridges`). One cutoff controls complete even-power error for finite cell sources [map]. A: further Gamma graph payments. B [RH]: full wave or odd sign. Lacks C.

### 3.4 Operator and boundary routes

#### SZ — Suzuki screw and shifted kernels
- **Proved:** Ward-defect lower-bound receiver; \(\neg\)RH forces cofinal unboundedness below. Every finite prime-power packet satisfies reflected current \(+\) negative-light Gram \(=\) positive-light Gram, with both Grams PSD [map]. The Suzuki subfolder has 44 no-go modules, e.g. Robin observers cannot extract the CCM-FU correction, and the ordinary entire characteristic limit is impossible.
- **A:** Uniform-in-packet assembly of the two-Gram identity.
- **B [RH]:** Uniform lower bound after complete assembly.
- **Lacks:** C.

#### CCM, Hedenmalm, Deninger (operator programmes)
- **CCM.** The Weil distribution is an actual operator trace (`opTrace_ccmIntegratedScaling_mul_geometricScatteringLogDifferential_eq_weilDistribution`). The archimedean Weil distribution equals Sonin part \(+\) square \(-\) anticommutator (`neg_ccmArchimedeanWeilDistribution_eq_sonin_add_square_sub_anticommutator`). Real-rooted nonnegative ground states force RH (`CCMNonnegativeGroundStateRH`). Parity selection of the restricted ground state fails under an isolated off-line quartet (`CCMParitySelectionNoGo`). **B [RH]:** a sign for the anticommutator term. Lacks C.
- **Hedenmalm.** One-aperture singularity ceilings and a one-temperature Hankel criterion force RH. Covariant aggregation cannot select the critical line (`HedenmalmThetaAnomalyBurnolCovariantAggregationNoGo`). **B [RH]**. Lacks S.
- **Deninger.** The Hodge–Schwartz resolvent core is RH (`DeningerResolventCoreIsRiemannHypothesis`). On a complete carrier the polarized generator is bounded, so its spectrum cannot be the zeros (`DeningerCompleteCarrierSpectrumBounded`). A single root adjunction destroys unique roots. **B:** a foliated space whose flow has the right unbounded generator. Lacks a realization (C).

#### TG — Topological sub-unit gate
- **Proved:** Winding and transgression identities; central-gap receivers [map].
- **B [RH]:** Nonnegative residual plus integer trace \(<1\) on every disc. Integrality is present here, but only after the sign.
- **Lacks:** C.

### 3.5 Candidates

All seventeen candidates have proved receivers and lack a zero-independent source mechanism [map]. The table records the property each lacks.

| Candidate | Missing mechanism | Lacks |
|---|---|---|
| APF, EWJ, FEL, WBF | Zero-independent exhaustion, admission or predeclared balance | P |
| BSH, CDC, HJ, IRK, SEC | Pre-divisor forcing at actual zeros | S |
| DR | Global monodromy of strict-right roots | C |
| EGC | Outer contour sign beating the Gamma floor | C |
| MSC | Source-faithful bridge from squarefree Hilbert data to the Sonin sign | C |
| PCS, RFHM | Source-natural symmetry-breaking wall law | S |
| PTR, W1C | Prime-faithful lossless port or ferromagnetic couplings landing on \(\Xi\) | Realization (C) |
| SC | Arithmetic cross-fibre index ceiling | P |
| PW-B | Removing `XiZeroCopy` indexing | S |

### 3.6 Theory programmes that act as routes

These programmes carry their own receivers and boundaries and are not separate map entries.

| Programme | Decisive theorems [Lean] | Status | Lacks |
|---|---|---|---|
| **HKT/AKLT** Krein index | \(\kappa(K_\zeta)=\#\)right zeros; Krein–Langer iff \(\kappa<\infty\); finite index ⇒ Lindelöf (`lindelof_of_negIndex_zetaKernel_lt_top`). All but finitely many primes see the whole index; locality and pointwise-closed statements are twin-blind. | **B [FS]:** \(\kappa<\infty\), a weaker-than-RH target that implies LH. | P (index ceiling) |
| **APD** \(\mathrm{Aff}(\mathbb Q)\) positivity | Hecke state PD iff \(s\ge1/2\); Bost–Connes temperature is the Hecke exponent; Weil's correlation carries no successor. A positive measure satisfying the bare functional equation is Riemann's prime measure (`eq_riemannPrimeMeasure_of_beurling_functional_equation`). | **B [RH]:** a PD function on \(\mathrm{Aff}(\mathbb Q)\) restricting to Weil's correlation. | C (it sits at the threshold) |
| **APol** polarization | The collided form is a coercive polarization at every aperture; RH iff Hecke invariant iff Weil form = collided form. Weil's form has finitely many negative directions at each aperture. | **B [RH]**. | C |
| **ALG** Lorentzian | Euler products of Lorentzian local factors are Lorentzian; the prime ladder is not; Ramanujan and Lorentzian meet only at the Weil bound; trickle-down inequality = square-root count. | **B [RH]**. | P |
| **MPG/SB** multiplicative positivity | Exact Fejér barrier \(a_1\le2\cos(\pi/(K+2))a_0\); multi-frequency certificates buy at most two; Siegel's exception is two-torsion; the simple-pole class is \(\zeta\). | Boundary; selection survivor. | C |
| **AES/RBG** electrostatics, renormalized geometry | Transverse equilibrium is the critical line; an off-line zero carries a full energy quantum; the Hecke defect is the moment of inertia. Prime-place counterterm survives nothing; the archimedean germ survives on the polar hyperplane. | **B [RH]:** the stability (sign) of the equilibrium. | C |
| **BGG** gauge geometry | Positive prime-mass deformations of \(\zeta(s)^2\zeta(s+i\gamma)\zeta(s-i\gamma)\) are rigid off the line; central excess forces a square-root prime deficit. | Rigidity for deformations, not for \(\zeta\) itself. | S |
| **AOG/SSIC** orientation, visibility | Orientation rate = depth of deepest seen zero; eventual Hasse–Weil is Hasse–Weil over \(\mathbb F_q\); hiding needs a crystal; refutation is finite, confirmation is not; the depth is the complete dilation invariant. | Visibility boundary. | P |
| **BSU** blind cones | Packet persistence; growth exponent of a compact packet = depth of seen zeros; prime-power node deletion price \(=\Lambda(m)/\sqrt m\) exactly, additive over primes (the blind cone reads the Euler product); a sharp window ceiling forces RH. | **B [RH]**. | C |
| **THIM/BVI** receiver calculus | The oscillating smooth power is paid exactly at the zeros of \(\zeta\); sign-blind dampings stop at \(1/2\). Coherent prime blocks admit no Type-II dispersion below the quadratic horizon; sharp cutoffs stop Type-I at \(\theta=4/3\). | Exact Type-II/parity boundary. | P |
| **ALDG/CDG** local divisors, collided metric | Heat repairs roots in a disc after time \(32r/\deg\); every finite head of \(\xi\) is heat-repaired at large height. Finite integer theta prefixes recover the full collided metric. | Local tools; no global sign. | C |

## 4. Cross-route verdict

| Missing property | Routes |
|---|---|
| **C** — critical sign at zero margin | HF, SRT, AIP, RW, EWU, OWU, ACT, LI, FU, CFC, RP, PA, TH, TT, LA, WD, HCF, GTA, RN, CHMD, SZ, TG, CCM, APD, APol, AES/RBG, BSU, ALDG/CDG, DR, EGC, MSC, PTR, W1C |
| **P** — square-root precision | ACS, WL, MC, PBM, RB, JAS, CTF, HKT/AKLT, ALG, AOG/SSIC, THIM/BVI, SRT (towers), APF, EWJ, FEL, WBF, SC |
| **S** — selection at the trivial point | MC, PM/PW-B, BAG, XN, Hedenmalm, BGG, BSH, CDC, HJ, IRK, SEC, PCS, RFHM |

(inference) The list is lopsided: about two thirds of the routes lack C. These routes already have selection, from the pole, Gamma and Ramanujan packets, and work at a fixed resolution; they fail because their margin vanishes. The P-routes have the right counting form but no producer stronger than Chebyshev precision. The S-routes carry an analytic object that cannot tell \(\zeta\) from a twin. No route lacks nothing.
