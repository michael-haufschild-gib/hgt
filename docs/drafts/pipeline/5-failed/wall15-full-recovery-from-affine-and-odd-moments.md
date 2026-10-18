# All-odd moment completion fails in an even sieve sector

- **ID:** wall15-full-recovery-from-affine-and-odd-moments
- **Stage:** 5-failed
- **Type:** FALSIFIED; exact positive survivor formalized
- **Wall:** 15, support versus positivity/orientation; field research only.
- **Source:** [cubic recovery and parity certificate](../3-formalized/wall15-cubic-odd-mode-recovery-and-parity-obstruction.md).
- **Statement falsified:** Adding every odd-order translated moment to all affine quadratic sieve data recovers an arbitrary finite real divisor response up to translated global sign, or even recovers its absolute origin amplitude.

## Exact killing mechanism

At every cutoff `N+10`, use the actual weights
`w_t(1)=1+t`, `w_t(2)=-2(1+t)`, `w_t(3)=-3`, `w_t(5)=-5t`, `w_t(6)=6`, `w_t(10)=10t`, zero elsewhere. Their Selberg coordinates are supported at 6 and 10, with values `(1,t)`. At `t=1` and `t=-1`, every comparable product agrees, hence every affine quadratic observation agrees.

The literal response is
`g_t(n)=(2·1_(2∣n)-1)[(3·1_(3∣n)-1)+t(5·1_(5∣n)-1)]`.
It changes sign under `n↦n+15`. Translation by 15 permutes the complete factorial period and reverses every odd-length translated product, so every such moment vanishes for every parameter `t`, every odd length and every lag vector.

Nevertheless `g_1(0)=6` and `|g_-1(n)|≤5` everywhere. No translation followed by a global sign identifies the responses. No decoder from the joint full affine-data function and the dependent family of all odd translated moments can recover absolute origin amplitude.

Exact actual-object certificates, in namespace `GaloisForLFunctions.BiScaleUncertainty.SieveMoments`: `translatedMoment_parityReal_zero`, `exists_same_affine_odd_data_distinct_absolute_origin`, and `no_absolute_origin_decoder_from_affine_and_odd`, in [CubicSievePhaseRecovery.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/CubicSievePhaseRecovery.lean). The affine-data and amplitude-bound statements use the existing `AffineSieve.affineMoment` and `sieveSeq` definitions.

## Strongest positive survivor

For an arbitrary finite real divisor sieve, the double Fourier transform of its literal triple observations is exactly
`P²Y(ord r)Y(ord s)Y(ord(r+s))`, `P=N!`. Equality of all triple data is equivalent to equality of all these triangular coordinate products. At every odd positive `q≤N`, the diagonal frequency `r=s=P/q` reads `P²Y(q)³`, so real cube injectivity recovers the signed coordinate without nonvanishing, connectivity or support assumptions.

This is a complete classification of triple observations and a signed reconstruction mechanism on the odd modes. It is not merely a restatement of the failure. Exact Lean theorems: `doubleDFT_tripleMoment`, `tripleMoment_eq_iff_triangles`, `tripleMoment_odd_mode_readout`, and `tripleMoment_recovers_odd_coordinates`.

## New insight and audited status

Odd-degree data can determine arithmetic signs, but an exact sign-reversing translation annihilates the whole odd hierarchy in a concrete even sector. Further observations must couple its components at even degree. The [sixth-moment recovery theorem](../3-formalized/wall15-sixth-moment-recovery-in-the-even-prime-pair-sector.md) proves quartic blindness and a sharp sixth-degree repair in this sector, with 20 audited Lean exports.

Dependency-closed paper proof and exact positive survivor are complete. All three original-source leaves passed final named checks with no diagnostics. All 32 public exports passed `#check` and `#print axioms`; only `propext`, `Classical.choice`, `Quot.sound` occur. Ten definition bodies, including the three existing underlying objects, were printed and inspected. The parent card records complete discovery, repository lint and protected-file verification. Internal novelty search was bounded; no external novelty claim, stability theorem, minimal observation degree or Wall 15 closure is asserted.

## Gates

- [x] Exact arithmetic counterexample for the entire joint observation family.
- [x] Positive-salvage audit: full triangular-product classification and signed odd-mode reconstruction.
- [x] Dependency-closed paper proof and exact positive survivor formalized and axiom-audited.
- [ ] Publication audit.

## Log

- 2026-10-18: full-recovery route retired only after the exact positive survivor and actual-object obstruction passed all named-source and public-axiom checks. Wall 15 remains open.
