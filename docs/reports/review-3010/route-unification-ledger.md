# Route-unification ledger

Status: 30 October 2026, corpus `00540e1855` plus working tree.

**The 32 live routes, 17 candidates, PW-B and the route-like theory programmes are faces of three core problems:**

- **U-Σ, critical positivity:** a positivity statement with zero margin.
- **U-Π, the square-root count:** a one-sided count exact at \(x^{1/2}\).
- **U-Γ, selection at the trivial gauge point:** a statement true for \(\zeta\) and false for its twins.

The corpus proves exact identifications between the three at their endpoints (§2). RH is the single statement in which all three coincide (inference). Every route supplies at most two of the three properties; most supply one.

Links: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [summary and next questions](obstacles-summary.md) · [frontier map](../rh-current-frontier-map.md). [Working log](../../../logs/review-3010-rev3-deep-research-2026-10-30.md). Labels as in the route report: [Lean], [map], (inference).

## 1. The three core problems

### U-Σ — Critical positivity

**Canonical forms** [Lean]:

- The complete atomic Weil matrix is positive on the critical curve \(E(c_N)\log N\asymp1\), and past it at \(c_N=2(\log N)^\alpha\), \(\alpha>1/4\) (`tiltedUnitSpline_overlap_window`).
- The restricted ground minimum satisfies \(\mu(A)\ge0\) at every aperture.
- The odd Markov form of Riemann's kernel has a positive ground state (`riemannHypothesis_of_foldedSupersolution` is the folded special case).

**Why it is critical** [Lean]:

- \(E(c)\to0\), with floor \(c^{-7}\) on the conductors \(m\le c\).
- \(\mu(A)\to0\) doubly exponentially.
- The odd form is never subcritical.
- The Hecke state is PD exactly from \(s=1/2\); the Bost–Connes temperature is the Hecke exponent.
- Monotone minorants cannot extend positivity (`extension_forces_positivity`).

**Faces:** HF, SRT, AIP, ACS (atomic branch), RW, EWU, OWU, ACT, TH, TT, LA, WD, HCF, GTA, RN, CHMD, SZ, CCM (FU, CFC, RP), PA, LI, TG, APD, APol, AES/RBG, BSU, DR, EGC, MSC, PTR, W1C.

### U-Π — The square-root count

**Canonical form** [Lean]: \(\kappa(K_\zeta)=0\iff\exists C,\ \psi(x)-x\le C\sqrt x\log^2x\) eventually (`negIndex_zetaKernel_eq_zero_iff_count`). The same count is the upper count of the odd Liouville class [map].

**Why it is a precision problem** [Lean]:

- Any criterion implying the count separates \(a\) from \(a+\varepsilon n^{-\eta}\), \(\eta<1/2\) (`deciding_input_necessary_properties`).
- Every producer law in the corpus holds for both (`producers_are_precision_blind`).
- Integrality over \(\mathbb Z\) produces Chebyshev precision: Adams jets cost \(2^{qr}\), factorial ratios \(2\log2\).

**Faces:** WL, MC, PBM, RB, JAS, CTF, PM, ACS (effectivity branch), HKT/AKLT, ALG, AOG/SSIC, THIM/BVI, SRT (tower branch), APF, EWJ, FEL, WBF, SC.

### U-Γ — Selection at the trivial gauge point

**Canonical forms** [Lean]:

- The Möbius gauge exponent at \(0\) equals the typical value \(1/2\).
- The collided polarization is Hecke invariant (`riemannHypothesis_iff_collided_hecke_invariant`).

**Why it is a selection problem** [Lean]:

- Gauge-invariant majorants are \(\ge3/4\) at \(0\).
- The trivial point is never better than typical.
- Locality and pointwise-closed statements are twin-blind.
- Uniform atomic positivity over all \(|\lambda|\le\Lambda\) is impossible (`not_forall_atomicPositiveAt`).
- \(\zeta\) is the worst twin on nonnegative tests (`weilPositive_nonneg_transfers`), so nonnegative tests cannot select.

**Faces:** MC, PM/PW-B, BAG, XN, Hedenmalm, BGG, BSH, CDC, HJ, IRK, SEC, PCS, RFHM.

**Solved part:** at bounded overlap, selection is a theorem [Lean]. Pole-free gauges and cofinite flips are rejected at one bounded overlap; the simple-pole class is \(\zeta\); a positive measure satisfying the functional equation is Riemann's prime measure. The open part is uniformity: pole-keeping flips need overlap \(\asymp p^{1/7}\) [map], and the trivial point is one point of a torus on which averages say nothing.

## 2. Proved identifications between the core problems

| Identity [Lean] | Joins | Content |
|---|---|---|
| `negIndex_zetaKernel`, `negIndex_zetaKernel_eq_zero_iff_count` | U-Σ = U-Π | The index of the Weil kernel is the number of right zeros; index zero is the square-root count. |
| `zeta_hodgeDefect_iff` | U-Σ = U-Π | The Hodge defect of the scaling surface is the same count of right zeros. |
| `riemannHypothesis_iff_collided_hecke_invariant`, `riemannHypothesis_iff_W_eq_collided` | U-Γ = U-Σ | Hecke invariance, a symmetry, is the sign: Weil form equals collided form. |
| `isPosDefOnGroup_heckeState_iff` | U-Γ = U-Σ | The positivity threshold of the integer successor is \(s=1/2\). |
| `threeQuarters_le_of_gaugeInvariant_bound`; typical exponent \(1/2\) | U-Γ = U-Π | The square-root exponent must be certified at one specified gauge point. |
| `lindelof_of_negIndex_zetaKernel_lt_top` | U-Σ → classical | Finite index, a weakened U-Σ/U-Π target, implies Lindelöf. |
| `collidedForm_translate` | U-Σ ↔ visibility | Hecke translation multiplies each zero's weight by \(e^{2(\operatorname{Re}\rho-1/2)L}\); depth is a growth rate. |

(inference) These are endpoint identities. Away from the endpoint the problems separate: a route can be selective without being critical, critical without being precise, and so on. The identities do not transfer partial progress from one face to another.

## 3. Each route as a face

**Supplies** lists what the route has; **Lacks** what it must produce. "Selective (bounded)" means selection at bounded resolution only.

| Route | Core object | Supplies | Lacks | Endpoint identity |
|---|---|---|---|---|
| HF, SRT, AIP, ACS-atomic | Complete Weil matrix | Selective (bounded); precise at fixed resolution | Critical | Overlap receiver \(\alpha>1/4\) |
| RW, EWU, OWU | Restricted ground minimum | Selective (odd witnesses) | Critical | \(\mu(A)>0\ \forall A\) |
| ACT, CHMD | Markov/Doob form | Exact ground-state structure | Critical | Positive ground state |
| TH, LA, HCF, GTA | Theta/heat Hankel and Jensen data | Critical structure (moment problem) | Critical uniformity in rank/degree | Hankel/Jensen positivity at all ranks |
| WD, heat | De Bruijn–Newman flow | Precise local dynamics | Critical at \(t=0\) | \(\Lambda=0\) |
| SZ, CCM (FU, CFC, RP), PA, LI, TG | Boundary/operator currents | Exact receivers | Critical | One-sided current bound |
| APD, APol, ALG | Group positivity, polarization, Lorentzian | Exact threshold at \(s=1/2\) | Critical (at threshold), precise | PD extension; Hecke invariance; trickle-down |
| WL, PBM, RB, JAS, CTF | Prime/Möbius error | Selective (divisor collapse at \(0\)) | Precise | One-sided count |
| MC | Möbius gauge exponent | Precise form of the target | Selective at \(0\); precise | \(\theta_\mu(0)=1/2\) |
| ACS-effectivity, HKT/AKLT, SC | Scaling surface, Krein index | Critical and precise by construction | A producer (index ceiling) | \(\kappa=0\) |
| AOG/SSIC, BSU, THIM/BVI | Visibility, blind cones, receivers | Exact boundaries | Precise (depth) | Rate = depth |
| PM/PW-B, BAG, XN, Hedenmalm, BGG | Escape states, recurrence, Newton, theta sources | Analytic objects | Selective | Visibility of every escape state |
| Candidates | Mixed | Receivers | See route report §3.5 | — |

## 4. How one object supplies all three over \(\mathbb F_q\)

| Property | Over \(\mathbb F_q\) | Over \(\mathbb Z\), per the corpus |
|---|---|---|
| **Critical** | The Rosati/Hodge index on \(C\times C\) is exact. Purity \(|\alpha|=\sqrt q\) is the boundary case, so no margin is needed. | The scaling surface has a Hodge index iff RH; its defect is the right-zero count. No Hodge-index theorem is available without the sign. |
| **Precise** | Finite genus gives \(|N_m-q^m-1|\le2gq^{m/2}\). Any constant suffices: eventual Hasse–Weil is Hasse–Weil (`EventualHasseWeilIsHasseWeil`). Stepanov reaches \(\sqrt q\) (`stepanov_bound`). | Infinite genus: no radical, no finite constant. The amplifier exists (rate readings are cofinal invariants; orientation rate = depth), but there is no constant to amplify. Integrality gives Chebyshev precision; Adams jets cost \(2^{qr}\). |
| **Selective** | Frobenius is a specific endomorphism, and the trivial point is better than typical over \(\mathbb F_q[T]\) [map]. | No Frobenius substitute among self-maps of \(\mathbb N\); the trivial point is never better than typical; gauge-invariant data stop at \(3/4\). |

(inference) The \(\mathbb F_q\) proof is not three arguments but one object: the Frobenius graph \(\Gamma_F\subset C\times C\). Its intersection numbers carry the sign (Hodge index), the count (\(\Gamma_F\cdot\Delta=N_1\)) and the selection (\(F\) is the Frobenius of this curve). Over \(\mathbb Z\) the corpus has the surface (scaling surface), the intersection form (Weil form), the Hecke correspondences (similitudes of the defect) and the count (index = right zeros), but no correspondence playing \(\Gamma_F\): one whose self-intersection is bounded by an independent geometric invariant.

## 5. What a unified input must look like

(inference, constrained by the theorems above)

1. **A positivity theorem without a gap.** It must be of Hodge-index or reflection-positivity type, an identity-level positivity, not a coercivity estimate with margin. Σ1 and the extension wall exclude everything that spends a margin.
2. **An amplifier with a finite seed.** The rate-reading machinery converts a bound with any constant into the exact sign once a uniform constant exists. The missing piece is a renormalized, height-local replacement for the genus, a constant per window that does not grow exponentially.
3. **Euler-product specificity.** The object must not exist for twins. The proved selectors are the pole (simple-pole class), the finite part \(-L'/L(1)\) and the conductor spectrum. The input must keep them at growing resolution, where pole-keeping twins need overlap \(\asymp p^{1/7}\).

**Partial matches in the corpus:**

| Object | Has | Lacks |
|---|---|---|
| Krein index | 1 and 2 | 3, and a producer |
| Complete Weil matrix | 3 | 1 |
| Hecke-similitude scaling surface | 1 in form, 3 | 2 |
| Integrality producers | 3 | 1, and 2 at square-root precision |
