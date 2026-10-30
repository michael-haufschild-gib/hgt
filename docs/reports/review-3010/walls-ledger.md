# Walls ledger

Status: 30 October 2026, corpus `00540e1855` plus working tree. **No core wall is crossed.**

**Three core families of walls**, one for each property a crossing must supply:

- **Σ — the critical sign.** A positivity statement that must hold with zero margin.
- **Π — square-root precision.** A count or cancellation that must be exact at \(x^{1/2}\).
- **Γ — selection.** The statement must hold for \(\zeta\) and fail for its gauge twins, at the trivial gauge point.

Each family is forced by theorems (§1).

**Solved faces** (§3): the rank-eight theta Hankel section; twin resolution at bounded overlap; complete Weil positivity at every fixed overlap and on fixed conductor packets up to \((\log N)^{1/40}\).

**Sharpest open face:** the critical curve of the complete Weil matrix. The degeneracy sits in the \(\approx c\) conductors \(m\le c\). The complete defect reserve has explicit polynomial overlap cost and survives while \(c^8=o(\log N)\); RH needs \((\log N)^{1/4+}\).

Links: [route report](route-obstacles.md) · [summary and next questions](obstacles-summary.md) · [route unification](route-unification-ledger.md) · [scoped no-go catalogue](../rh-killed-routes.md). [Working log](../../../logs/review-3010-rev3-deep-research-2026-10-30.md). No builds were run.

| Label | Meaning |
|---|---|
| **[Lean]** | Declaration read via the corpus search. |
| **[map]** | From the frontier map. |
| **(inference)** | This review's interpretation. |
| **[QRH] [LH] [FS] [RH]** | Strength of the open statement: zero-free strip; Lindelöf; finitely many off-line zeros; RH. |

## 1. Why there are exactly three families

Each family is the content of a theorem that any RH-strength input must satisfy.

| Family | Forcing theorem [Lean] | What it says about any crossing input |
|---|---|---|
| **Σ** | `extension_forces_positivity`; ACT: odd form never subcritical; `isPosDefOnGroup_heckeState_iff` (\(s\ge1/2\)); `tendsto_tiltedUnitSpline_completedShellEnergy_atTop` (\(E(c)\to0\)) | RH sits at the boundary of a positivity cone. There is no spectral gap to spend, and monotone continuation from a positive range is impossible. |
| **Π** | `deciding_input_necessary_properties`; `producers_are_precision_blind`; `negIndex_zetaKernel_eq_zero_iff_count` | The input must distinguish perturbations of size \(n^{-\eta}\), \(\eta<1/2\), which every known producer law ignores. |
| **Γ** | `threeQuarters_le_of_gaugeInvariant_bound`; `SMAP.not_forall_atomicPositiveAt`; AKLT: locality and pointwise-closed statements are twin-blind | The input must break the gauge symmetry at the trivial point. Uniform positivity over all weights \(|\lambda|\le\Lambda\) is false. |

(inference) The three are independent. Bounded-overlap complete positivity is selective and fixed-resolution, but not critical. The Krein index is critical and precise by construction, but has no producer. Integrality producers (Bézout, Adams, factorial ratios) are selective through \(\Lambda*1=\log\), but give only Chebyshev precision.

## 2. The walls

### Family Σ — the critical sign

| Wall | Current content | Strength of open part |
|---|---|---|
| **Σ1 Critical curve of the complete Weil matrix** | See below. | [RH] on or past the curve |
| **Σ2 Extension** | A nondecreasing minorant of \(\lambda(L)\) nonnegative once forces \(\lambda\ge0\) everywhere (`extension_forces_positivity`). Soft tools move positivity only downward in \(L\). Linear \(\Lambda\)-positivity caps at PNT strength; the quadratic Weil index gives lower bounds on \(\operatorname{ind}_-\) only (`ExtensionProgrammeNoGo`). | Exact no-go |
| **Σ3 Criticality of the arithmetic Markov form** | See below. | [RH] |
| **Σ4 Rank and order uniformity** | Rank-seven strict and rank-eight PSD theta Hankel sections for \(0<a<1/2\) (`thetaCuspCenterMixedSignedHankel_eight_posSemidef`). Heated orthant signs at all ranks. Square-plus-null-Lagrangian identity for the native fibre form (`thetaCuspNativeTailHankelForm_eq_square_sub_flux`). All-rank sign iff RH. | Each finite rank: A. All ranks: [RH] |
| **Σ5 Infinite genus** | See below. | [FS] for finite index; [RH] for zero |
| **Σ6 Realization** | See below. | [RH] |

**Σ1 Critical curve of the complete Weil matrix.**

- Fixed \(c\): positive definite, bottom \(E(c)\).
- \(c^{-7}\lesssim E_m(c)\) for \(m\le c\), constant floor above (`ConductorScaleControlsTheCompletedEnergy`).
- Fixed packets: positive for \(c\le(\log N)^{1/48}\) and along \((\log N)^{\alpha}\), \(\alpha<1/40\).
- Gamma reserve: survives while \(c^8=o(\log N)\); explicit complete defect reserve with polynomial cost.
- Receiver: RH iff positivity at \(2(\log N)^\alpha\), \(\alpha>1/4\).
- (inference) Margin, reserve and synthesis error are one Fourier tail separated by the weight \(\log N\), so the transition is the curve \(E(c_N)\log N\asymp1\); for the tilted spline, exponent \(1/7\).

**Σ3 Criticality of the arithmetic Markov form.**

- Odd form never subcritical.
- Restricted Weil ground energy \(\to0\); \(\mu(A)\le K\exp((11/2)A-\pi e^{2(A-2)})\).
- No positive profile is a folded supersolution.
- Hecke state threshold \(s=1/2\) equals the Bost–Connes temperature \(\beta=1\).
- RAPT: the pole is the ground state; the multiplicative random-walk Dirichlet form has gap \(2\log2\) below it.

**Σ5 Infinite genus.**

- \(\kappa(K_\zeta)=\) Hodge defect \(=\#\)right zeros; finite at each degree.
- No compact test vanishes at every zero: no radical, hence infinite genus.
- Finite index iff finitely many off-line zeros, which implies Lindelöf (`lindelof_of_negIndex_zetaKernel_lt_top`).
- Weil's form has finitely many negative directions at each aperture (APol).
- Over \(\mathbb F_q\): index \(\le\) genus (AKLT).

**Σ6 Realization.**

- The Weil distribution is a CCM operator trace.
- The archimedean part equals Sonin \(+\) square \(-\) anticommutator.
- Deninger: a complete carrier gives a bounded generator, which cannot have the zeros as spectrum.
- Lossless media, Ising limits and theta-cusp black-hole quasinormal modes realize \(\Xi\) only when indexed by its zeros (`XiZeroCopy`) or with a unit gap [map].

### Family Π — square-root precision

| Wall | Current content | Strength of open part |
|---|---|---|
| **Π1 Global law** | Index zero iff \(\psi(x)-x\le C\sqrt x\log^2x\), which is also the odd Liouville upper count [Lean, HKT/AKLT]. The trickle-down inequality of the Lorentzian route is the same count (ALG). | [RH] |
| **Π2 Deciding input and precision blindness** | A criterion implying the count must reject Liouville, separate \(a\) from \(a+\varepsilon n^{-\eta}\) for all \(\eta<1/2\), and not be finite-window. \(\Lambda+\varepsilon n^{-\eta}\) satisfies PNT and every short-interval law past \(17/30\). Count holds iff \(a-1\in\mathcal Q\) [map]. | Exact boundary |
| **Π3 Producer cost** | See below. | [RH] for a square-root producer |
| **Π4 Dispersion horizon** | Coherent prime blocks admit no Type-II dispersion below the quadratic horizon (`exists_primeBlock_typeII_window_loss`). Sharp cutoffs stop Type-I at \(\theta=4/3\). Every short-window, balanced or uniform-Vaughan saving is equivalent to a zero-free strip (BVI). Degree-\(m\) transfer horizon \(N^m\). | [QRH] and up |
| **Π5 Depth visibility** | See below. | [FS] and up |
| **Π6 Classical density layer** | Formalized past the literature: Guth–Maynard large values; Vinogradov–Korobov; \(\ge0.6725\) simple critical; \(\ge4/5\) critical ordinates; \(\Lambda<1/8\). Lindelöf follows only from finite index. | [LH], [QRH] |

**Π3 Producer cost.**

- Order-\(r\) jet vanishing on the Adams fixed locus costs support \(2^{qr}\), sharp.
- Balanced factorial ratios cost \((2\log2-\varepsilon)mn\).
- Bézout and Riemann–Roch on \(\mathbb G_m(\mathbb Q)\) are linear.
- Integer approximate vanishing is divisibility.
- Bounded-defect ring endomorphisms of \(\mathbb N\) are trivial [map].
- Over \(\mathbb F_q\) Stepanov reaches \(\sqrt q\) (`stepanov_bound`).

**Π5 Depth visibility.**

- Single-horizon charges are depth-blind; depth enters only as \((N/M)^{|\operatorname{Re}z|}\).
- Hiding needs a crystal.
- A bounded aperture range certifies no rate; refutation is finite, confirmation is not.
- Orientation rate = depth of the deepest seen zero.
- Growth exponent of a compact packet = depth of the zeros it sees (BSU).

### Family Γ — selection

| Wall | Current content | Strength of open part |
|---|---|---|
| **Γ1 The trivial gauge point** | The typical gauge exponent is exactly \(1/2\); \(\theta_\mu(0)=\Theta\); RH iff \(0\) is typical. Gauge-invariant majorants are \(\ge3/4\) at \(0\). The trivial point is the additively invariant point, and divisor collapse \(\Lambda*1=\log\) happens only there (AGT). | [RH] |
| **Γ2 Twin resolution** | See below. | Bounded: solved. Uniform: [RH] |
| **Γ3 Twin-blindness of soft structure** | See below. | Exact boundary |
| **Γ4 Hecke invariance** | RH iff the collided polarization is Hecke invariant, iff it is a Hecke similitude, iff Weil form = collided form. The scaling defect is a Hecke similitude (`defect_heckeCorrespondence`). \(\zeta\)-specific deformations of \(\zeta^2\zeta(s\pm i\gamma)\) are rigid off the line (BGG). | [RH] |

**Γ2 Twin resolution.**

- At fixed overlap a twisted form is decided by a finite Ramanujan packet.
- Pole-free \(\pm1\) gauges with bounded harmonic sums and all cofinite flips are rejected at one bounded overlap (`liouvilleSelector_selective_of_signGauge`).
- Pole-keeping flips need \(c_0\asymp p^{1/7}\) [map].
- The simple-pole class is \(\zeta\) (`completedPositiveSystem_one_one_eq_zeta`).
- A positive measure satisfying the functional equation is Riemann's prime measure.

**Γ3 Twin-blindness of soft structure.**

- Locality and pointwise-closed statements are twin-blind: a twin is a limit of vertical shifts (AKLT).
- The gauge is invisible at atomic resolution (AES).
- \(\zeta\) is the worst twin on nonnegative tests (`weilPositive_nonneg_transfers`).
- Uniform atomic positivity over \(|\lambda|\le\Lambda\) is impossible (`not_forall_atomicPositiveAt`).

## 3. Status by face

"Solved" means the stated face is answered; it never means a route is closed.

| Face | Wall | Status | Content |
|---|---|---|---|
| Rank-eight theta Hankel section | Σ4 | **Solved [Lean]** | PSD for every \(0<a<1/2\); seam at \(\log(5/\pi)\), 15 seam and 8 bulk piece certificates, exact \(LDL^\top\). Rank nine is the next finite certificate. |
| Theta tail form | Σ4 | **Identity [Lean]** | Square plus null Lagrangian; tail form = bulk \(L^2\) mass \(-\) center flux; flux \(0\) at the seam. All-rank positivity is flux domination. |
| Complete positivity at fixed overlap | Σ1 | **Solved [Lean]** | Every fixed \(c\), uniformly on \(0<c\le K\); bottom \(E(c)\), attained at the pole conductor. |
| Fixed conductor packets at growing overlap | Σ1 | **Solved to \((\log N)^{1/40}\) [Lean]** | Along \((\log N)^\alpha\), \(\alpha<1/40\); uniformly on \(1\le c\le(\log N)^A\), \(A<1/48\). |
| Conductor floor | Σ1 | **Exact [Lean]** | \(c^{-7}\) floor only for \(m\le c\); constant floor above the overlap scale. |
| Complete defect reserve | Σ1 | **Explicit [Lean]** | Cutoff \(\sim c^8\), polynomial cost; Gamma reserve survives while \(c^8=o(\log N)\). |
| Growing conductors and full complement below the curve | Σ1 | **Open; A** | Loss-free control of the \(\approx c\) conductors \(m\le c\) up to \((\log N)^{1/8-\varepsilon}\). |
| Positivity on the critical curve | Σ1 | **Open [RH]** | \(E(c_N)\log N\asymp1\). |
| Extension of positivity ranges | Σ2 | **Exact no-go [Lean]** | Every positivity-range argument must prove RH outright. |
| Ground state of the full nonlocal generator | Σ3 | **Open [RH]** | Folded supersolutions are excluded. |
| Finite Krein index | Σ5 | **Open [FS]** | Implies Lindelöf. |
| Realization without zero indexing | Σ6 | **Open [RH]** | The CCM anticommutator term and the Deninger bounded-generator law locate the missing sign. |
| Producer precision | Π2, Π3 | **Exact boundary [Lean]** | Producers are precision-blind; integrality gives Chebyshev precision; Adams jets cost \(2^{qr}\). |
| Type-II horizon | Π4 | **Exact boundary [Lean]** | No dispersion below the quadratic horizon for coherent prime blocks. |
| Classical density layer | Π6 | **Formalized [Lean]** | Guth–Maynard, \(0.6725\), \(4/5\) ordinates, \(\Lambda<1/8\). Lindelöf and density hypothesis open. |
| Bounded-overlap twin resolution | Γ2 | **Solved [Lean]** | Pole-free gauges and cofinite flips rejected at one bounded overlap; the simple-pole class is \(\zeta\). |
| Uniform selection at growing resolution | Γ2 | **Open [RH]** | Pole-keeping flips need \(c_0\asymp p^{1/7}\). |
| Exponent at the trivial gauge point | Γ1 | **Open [RH]** | Gauge-invariant data stop at \(3/4\). |
| Hecke invariance of the collided polarization | Γ4 | **Open [RH]** | The scaling defect is a Hecke similitude. |

## 4. How the walls interlock

The corpus proves bridges between the families. A crossing of one family therefore transfers to the others only along these bridges.

| Bridge [Lean] | Connects | Consequence (inference) |
|---|---|---|
| \(\kappa(K_\zeta)=\#\)right zeros; \(\kappa=0\iff\) one-sided count | Σ5 = Π1 | Index zero is the count: a critical sign and a precise count are one statement at the endpoint. |
| Finite \(\kappa\) ⇒ Lindelöf; finite \(\kappa\iff\) finitely many off-line zeros | Σ5 → Π6 | A weaker-than-RH target with a structural (dimension) form. |
| RH iff collided polarization is Hecke invariant | Γ4 = Σ | Selection by Hecke symmetry is the sign. |
| Gauge-invariant data \(\ge3/4\); typical \(1/2\) | Γ1 → Π | Precision must be spent at one point of the gauge torus, not on average. |
| Hecke state PD iff \(s\ge1/2\) | Σ3 = Γ | The critical line is the positivity threshold of the integer successor. |
| Adams cost \(2^{qr}\); \(\mathbb F_q\) Stepanov | Π3 ↔ \(\mathbb F_q\) | The char-\(p\) mechanism (a Frobenius with vanishing derivative) has no char-\(0\) analogue at polynomial cost. |
| Margin = reserve = synthesis error (one tail) | Σ1 internal | No fixed-relative-loss estimate crosses the critical curve. |

**Organizing identities.**

- The complete form and the pole defect: \(\operatorname{Re}W(f,f)=D(f,f)-\mathfrak d(f)\); \(P_N+D_N=\sum(A(\lfloor N/n\rfloor)+\log n)x_n^2\) (RAPT ground-state identity).
- The collided form under translation: \(\mathrm{collided}(T_Lf)=\sum_\rho m_\rho e^{2(\operatorname{Re}\rho-1/2)L}|\hat f(\rho)|^2\) (`collidedForm_translate`).
- Shell repayment: \(E_m(c)=\frac2{M\varphi(m)}\sum_{(a,m)=1}\frac ma\int_{ac/m}^\infty|\hat\varphi(2\pi t)|^2dt\).
- Theta tail: \(\sum v_iv_jU_{i+j}(r)=2\int_{y>r/2}|G_v|^2-2B_v(r/2)\).
