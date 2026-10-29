# Infinite-symmetry continuation in positive genus: is the polar divisor constrained?

- **ID:** ISC-polar
- **Stage:** 5-failed
- **Type:** FALSIFIED (scoped: confinement by the infinite-symmetry calculus; the arithmetic-confinement candidate stays open as frontier candidate ISC-polar)
- **Source:** docs/reports/review-2910/obstacles-summary.md §2.6 Q3 and §2.7 ("analytic continuation by infinite symmetry"); predecessor [ISC-cal](infinite-symmetry-continuation-calibration.md) (genus zero: blind).
- **Statement:** For affine \(A_1\) Eisenstein data over a curve datum, decide whether any structure available without RH constrains where the zeta-zero hyperplanes of the polar divisor may lie.

## Goal

The route needs a theorem that the polar divisor of the continued affine constant term, in a region reached without RH, contains only hyperplanes of on-line type. Over \(\mathbb F_q\) a yes would re-prove RH for a curve by holomorphy (the calibration). A no retires the route.

## Gates
- [x] 0 → 1  in-progress: affine \(A_1\) Weyl sum with Gindikin–Karpelevich coefficients over a curve datum, level-four slice \(\lambda(s)=(4-s,s)\), degree rotation \(R\).
- [x] 1 → 2  fully-proven: survivors below, paper proofs complete.
- [x] 2 → 3  formalized: `RHTower/InfiniteSymmetry/`; each file checked with `lake --old env lean`; `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`.

## Verdict: the infinite-symmetry calculus is a receiver; arithmetic confinement stays open

1. **The polar calculus is purity-blind (formal).** For every curve datum with zeros in the open strip (\(1<|\alpha_i|<q\)), unitary or not, the complete affine Weyl sum continues meromorphically from the Godement half-plane, its cleared sum \(H_R\) is holomorphic on \(-1<\operatorname{Re}s<2\), and every zero of \(Z(s+1)\) is a pole of exact multiplicity for all strong rotations. The golden datum (\(q=5\), \(\beta=\varphi,\varphi^{-1}\)) satisfies all of this and has a pole at \(\operatorname{Re}s=-\tfrac12+\log\varphi/\log5\).
2. **The polar divisor is the zero set (formal).** In the band \(-1<\operatorname{Re}s<0\) the continuation is eventually holomorphic at \(s\) iff \(s+1\) is not a zero. Hence RH for the datum \(\iff\) eventual holomorphy at every point of the band off \(\operatorname{Re}s=-\tfrac12\). A constraint on the polar divisor *is* RH for the datum.
3. **The chamber is silent (formal).** Positive real roots pair with the closed positive chamber in real part \(\ge0\); zero hyperplanes have real part \(\operatorname{Re}\rho-1\). Holomorphy on the closed chamber certifies exactly \(\{\operatorname{Re}\rho\ge1\}\) (the prime-number-theorem line, the Langlands–Shahidi shape); absolute convergence certifies \(\{\operatorname{Re}\rho>2\}\). In \(w\cdot C\) a zero hyperplane of \(\beta>0\) appears only if \(\beta\in I(w^{-1})\): zeros reach the Tits cone only through the factors the functional equation transports.
4. **Where a constraint could come from (inference).** (a) A priori analytic information on Eisenstein series lives on the closed positive chamber: Godement convergence, Langlands/Maass–Selberg positivity, the unitary boundary; for loop groups there is no spectral theory at all (GMP §1.1), and Garland's Maass–Selberg continuation of minimal-parabolic series is meromorphic up to a wall. By (3) this certifies only \(\operatorname{Re}\rho\ge1\). (b) Bochner-type holomorphy of the normalized series is (1): the cleared sum is holomorphic for every datum because the normalizer carries the zeros. (c) Cuspidal series: the positive series is entire (Garland–Miller–Patnaik, arXiv 1304.4913; finite sums over function fields by Braverman–Kazhdan) but its \(P\)-constant term contains no nontrivial \(L\)-function (Shahidi); the \(L\)-functions sit in the negative series \(E^-\) with \(E=\Xi E^-\), so a pole of \(\Xi\) at \(\nu\) is exactly a zero of \(E^-\) there, and holomorphy/nonvanishing of \(E^-\) is again a receiver (the meromorphic-germ law is formal; the entirety and the functional equation are external); the continuation of \(E^-\) is open and predicted to stop at a wall. (d) Over \(\mathbb F_q\) the only known source of a placement theorem is purity of a geometric object (Weil for the curve, Deligne for the associated surfaces of the geometric Eisenstein series): Wall 14.

**Conclusion.** Infinite symmetry adds zero-seeing (in positive genus) and a natural boundary, not a constraint. Continuation, the transported coefficients, pole survival, normalized holomorphy, closed-chamber holomorphy and an entire positive cuspidal series do not confine the poles; that mechanism is retired (killed-routes row "Weyl meromorphy as polar confinement"). What stays open is the candidate ISC-polar in its strong form: an independent arithmetic confinement input that rejects the golden datum, then an actual \(\zeta\)/Eisenstein realization. By (2) such an input over \(\mathbb F_q\) proves RH for the curve, so its calibration is a new proof of Weil's theorem through the Eisenstein series; the only known source is geometric purity (Wall 14) (inference). Garland's series over \(\mathbb Q\) should wait for that calibration.

## No-go closure

- **Exact killing mechanism (of confinement by the calculus):** the complete affine Weyl expansion places its poles exactly at the shifted zeros of the datum's zeta function, with multiplicity, for every datum with zeros in the strip, unitary or not (golden datum); a constraint on the polar divisor is equivalent to RH for the datum; a priori holomorphy on the closed positive chamber certifies exactly \(\operatorname{Re}\rho\ge1\).
- **Strongest positive survivor:** *exact zero detector for every curve datum*: `weylSum_eventual_order` (pole of exact order \(-\operatorname{mult}\) at every zero, all strong rotations) with the receiver `eventually_analytic_iff` and `unitary_iff_eventually_analytic_off_critical`; *certified-set law* `certified_closedChamber` \(=\{\operatorname{Re}\rho\ge1\}\), `certified_godementChamber` \(=\{\operatorname{Re}\rho>2\}\); *inversion law* `mem_inversions_of_re_neg`, `zeroHyperplanes_finite`; *cuspidal-pair receiver* `pole_iff_zero_of_mul`, `order_zero_iff_of_mul`.
- **New insight:** genus zero was blind (no zeros to see); genus one sees every zero exactly, and still constrains none. Seeing and constraining are separated by the same line as everywhere in the corpus: the calculus is a receiver, and placement needs purity of a geometric realization (Wall 14) or a sign beyond the chamber (Wall 1). The infinite Weyl group contributes only finitely many zero hyperplanes per chamber, all transported.
- **Status:** dependency-closed; Lean below. Items 4(a), 4(d) and the external inputs of 4(c) are inferences from the cited literature.

## Lean

`formal/GaloisForLFunctions/RHTower/InfiniteSymmetry/`, wired into `RHTower.lean`:

- `CurveDatumZetaRatio.lean`: `numeratorPoly`, `zetaCoord`, `StripCondition`, `zetaRatio_eq_reduced`, `exists_reducedRatio_bound`, `exists_ratioParts_bound`, `re_root_eq`, `re_root_mem`, `re_root_eq_neg_half_iff`, `ratioNumerator_ne_zero_at_root`, `ratioDenominator_order_at_root`, `ratioDenominator_ne_zero_chamber`.
- `CurveDatumWeylPoles.lean`: `weylSum`, `regularizedWeylSum_analytic`, `continuedWeylSum_eq_chamber`, `continuedWeylSum_analytic`, `regularizedWeylSum_tendsto`, `weylSum_eventual_order`.
- `ThePolarDivisorIsTheZeroSet.lean`: `eventually_analytic_iff`, `unitary_iff_poles_on_critical_hyperplane`, `unitary_iff_eventually_analytic_off_critical`, `golden_stripCondition`, `golden_not_unitary`, `golden_offLine_pole`, `polarCalculus_does_not_force_unitarity`, `actual_stripCondition`, `actual_poles_on_critical_hyperplane`.
- `TheChamberIsSilentOnTheStrip.lean`: `rootArgument_re_nonneg`, `zeroHyperplane_not_closedChamber`, `certified_closedChamber`, `certified_godementChamber`, `level_re_nonneg`, `mem_inversions_of_re_neg`, `zeroHyperplanes_finite`.
- `TheCuspidalPairIsAReceiver.lean`: `exists_orders_of_mul`, `meromorphicOrderAt_eq_neg_of_mul`, `pole_iff_zero_of_mul`, `order_zero_iff_of_mul`.

## Paper proofs of the survivors

Notation: \(T(s)=q^{-s}\), \(P(X)=\prod_i(1-\alpha_iX)\), \(Z(s)=P(T)/((1-T)(1-qT))\), \(N(s)=(1-T/q)P(T)\), \(Q(s)=(1-qT)P(T/q)\); \(Z(s)/Z(s+1)=N/Q\) when \(T\ne1\). Strip condition: \(1<|\alpha_i|<q\).

**Lemma 1 (separation).** If \(P(T(s+1))=0\), say \(\alpha_iT(s+1)=1\), then \(-1<\operatorname{Re}s<0\), \(Q(s)=0\) with order equal to the root multiplicity, and \(N(s)\ne0\). *Proof.* \(q^{-\operatorname{Re}(s+1)}=|\alpha_i|^{-1}\) gives \(\operatorname{Re}s=\log|\alpha_i|/\log q-1\in(-1,0)\). \(T(s)=q/\alpha_i\), so \(1-qT(s)=1-q^2/\alpha_i\ne0\) since \(|\alpha_i|<q<q^2\); the order of \(Q\) is that of \(P\) composed with the locally biholomorphic \(T/q\). \(1-T(s)/q=1-1/\alpha_i\ne0\) since \(|\alpha_i|>1\), and \(P(q/\alpha_i)=\prod_j(1-q\alpha_j/\alpha_i)\ne0\) since \(|q\alpha_j/\alpha_i|>q\cdot1/q=1\). ∎

**Theorem 1 (exact pole survival).** On \(\lambda(s)=(4-s,s)\) every positive root other than \(\alpha\) has argument of real part \(>2\) for \(-1<\operatorname{Re}s<2\); there \(|T|\le q^{-2}\) and the strip condition keeps \(N/Q\) analytic on a closed disk, hence bounded by \(B\). \(N,Q\) are bounded on \(|T|\le q\) by \(K\). Clearing \(Q\) from the coefficient of \(\alpha\) (or multiplying by \(Q\)) gives holomorphic \(A_w\) with \(|A_w|\le e^{(|I(w)|+1)C}\), \(|I(w)|\le2|n|+1\); the degree factor decays like \(e^{-2Rn^2}\); the cleared sum \(H_R\) is holomorphic, equals \(Q\cdot\)(literal sum) where \(Q\ne0\), and in particular on \(1<\operatorname{Re}s<2\). As \(R\to\infty\) dominated convergence leaves the index-zero terms \(Q+N\). At a zero \(s_0\), \(Q(s_0)=0\ne N(s_0)\), so \(H_R(s_0)\ne0\) for large \(R\) and the order of \(H_R/Q\) at \(s_0\) is \(-\operatorname{mult}\). ∎

**Theorem 2 (receiver).** In \(-1<\operatorname{Re}s<0\), \(|qT(s)|>q>1\), so \(Q(s)=0\iff P(T(s+1))=0\). If \(Q(s)\ne0\), \(H_R/Q\) is holomorphic at \(s\) for every \(R>0\); if \(Q(s)=0\), Theorem 1 gives a pole for all large \(R\). With Lemma 1, \(\operatorname{Re}s=-\tfrac12\iff|\alpha_i|=\sqrt q\iff|\beta_i|=1\); every \(\alpha_i\) has the pole parameter \(\log\alpha_i/\log q-1\). Hence unitarity \(\iff\) all poles on \(\operatorname{Re}s=-\tfrac12\iff\) eventual holomorphy off that line in the band. Golden: \(\sqrt5\varphi^{-1},\sqrt5\varphi\in(1,5)\) and \(|\beta_0|=\varphi\ne1\); its pole parameter has real part \(\log(\sqrt5\varphi)/\log5-1=-\tfrac12+\log\varphi/\log5\). ∎

**Theorem 3 (chamber law).** \(\langle\lambda,\beta^\vee\rangle=c_0\lambda_0+c_1\lambda_1\) with integers \(c_0,c_1\ge0\), not both zero, for \(\beta>0\). On \(\operatorname{Re}\lambda_0,\operatorname{Re}\lambda_1\ge0\) the real part is \(\ge0\), so \(\operatorname{Re}\rho\ge1\) on any zero hyperplane through the chamber; conversely \(\lambda=(0,\rho-1)\), \(\beta=\alpha\) realizes every \(\operatorname{Re}\rho\ge1\). On \(\operatorname{Re}\lambda_i>1\): \(\operatorname{Re}\langle\lambda,\beta^\vee\rangle\ge(c_0+c_1)(1+m)>1\) with \(m=\min\operatorname{Re}\lambda_i-1>0\); \(\lambda=(2,\rho-1)\) realizes every \(\operatorname{Re}\rho>2\). For \(\lambda'=w\lambda\), \(\langle\lambda',\beta^\vee\rangle=\langle\lambda,(w^{-1}\beta)^\vee\rangle\); negative real part forces \(w^{-1}\beta<0\), i.e. \(\beta\in I(w^{-1})\), a finite set. ∎

**Theorem 4 (cuspidal pair).** If \(E=\Xi F\) on a punctured neighbourhood of \(\nu\), \(E\) holomorphic with \(E(\nu)\ne0\), then \(0=\operatorname{ord}E=\operatorname{ord}\Xi+\operatorname{ord}F\); both orders are finite and opposite, so \(\operatorname{ord}\Xi<0\iff\operatorname{ord}F>0\) and \(\operatorname{ord}\Xi=0\iff\operatorname{ord}F=0\). ∎

## Log
- 2026-10-29 — created; literature intake (GMP abstract and §1.3); plan fixed.
- 2026-10-29 — survivors formalized and audited; verdict FALSIFIED; moved to 5-failed.
- 2026-10-29 — scope narrowed to confinement by the calculus; arithmetic confinement kept as frontier candidate ISC-polar; cuspidal-pair receiver formalized.
