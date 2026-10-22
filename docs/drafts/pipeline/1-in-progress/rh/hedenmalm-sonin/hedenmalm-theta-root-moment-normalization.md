# Theta root-mode monopole normalization and dipole reduction

- **ID:** HED-THETA-ROOT-MOMENT-NORMALIZATION
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `HedenmalmThetaSourceModeNormalization` + `HedenmalmQuantileRootMode` +
  `HedenmalmThetaRootEndpoints`
- **Statement:** Every theta-source divisor mode in `|Im z| < 1` is `L¹` in quantile space,
  has monopole exactly `1`, has centered dipole exactly `-∫h_z`, and its universal rank-two
  boundary pairing is `2 Im(z)` times the positive quantile energy.

## Goal

Remove the last ambiguity between the explicit divisor mode and the universal pinned-Volterra
boundary moments. The theorem does not assume weighted-`L²` packaging: moments are first proved as
honest Lebesgue integrals of the explicit quantile function.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Conjecture/failure/proof chain

1. **C25a (failed):** existing root energy immediately packages `sourceModeF` in the weighted
   source Hilbert space. Exact failure: existing energy is `∫q|h|²`, equivalently the weighted norm
   of `g/√q`; ordinary `L²(0,1)` would require `∫|g|²`. No coercion closes that exponent gap.
2. **C25b (proved):** full source mass and the corpus's quantile change of variables force
   `∫g=1`. Because mathlib's Bochner integral is zero for a nonintegrable function, the nonzero
   equality plus the change-of-variables theorem also forces `g∈L¹`; this is not an improper or
   formal integral.
3. **C25c (proved):** integrate `h'=g-1` by parts against `t-1/2` on symmetric interior intervals,
   then use the proved endpoint limits and monotone exhaustion to get the exact dipole law.
4. **C25d (proved):** combine monopole `1`, dipole law, and the ordered-correlation flux identity.
   The rank-two moment pairing is exactly `2 Im(z) E_z`.
5. **Next conjecture:** find a corpus-native law forcing the normalized divisor dipole's real part
   to vanish. Since `E_z>0` for a nonzero mode, that would force `Im z=0` and close RH. Weighted-`L²`
   packaging is useful but is not itself the missing sign law.

## Corpus and literature audit

- `[CORPUS]` `integral_quantileTransform` identifies the full quantile average with source mass
  divided by `√M`.
- `[CORPUS]` `integral_sourceModeF_thetaSource_eq_mass` supplies the previously missing numerator.
- `[CORPUS]` `hasDerivAt_rootH` gives `h'=g-1`; `RootModeEndpoints` supplies integrable `h` and
  vanishing endpoint norms.
- `[CORPUS]` `rootFlux_identity_thetaSource` identifies `Re ∫(-h)` with `-Im(z)E_z`.
- `[LITERATURE]` Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494,
  proves rapid two-ended decay of the complex-zero eigenfunction in its second-order model. The
  fixed quantile monopole/dipole formulas here are corpus-specific first-order identities.
- `[INFERENCE]` no external novelty claim is made pending expert search beyond the directly
  relevant primary paper.

## Complete paper proof

Fix `z` with `|Im z|<1` and `XiC thetaSource z=0`. Write `M=thetaSource.mass`,
`f_z=sourceModeF thetaSource z`, `g_z=rootG thetaSource z`, and
`h_z=rootH thetaSource z`.

1. `[PROVED HERE]` Direct substitution in the definitions, using the already proved identity
   `h_z(t)=(-i/M)u_z(Q(t))`, gives
   `quantileTransform(f_z)(t)=√M g_z(t)` for `0<t<1`.
2. `[PROVED HERE]` Change of variables and canonical source normalization give
   `∫ quantileTransform(f_z)=M/√M=√M`. Since `M>0`, cancel `√M` to obtain
   `∫g_z=1`.
3. `[PROVED HERE]` If `g_z` were not integrable on `(0,1)`, its Bochner integral would be zero,
   contradicting step 2. Thus `g_z∈L¹(0,1)`. The bounded factor `t-1/2` then gives an integrable
   centered moment.
4. `[PROVED HERE]` On any interior interval `[a,b]`, integration by parts with
   `u(t)=t-1/2`, `v(t)=h_z(t)`, and `v'=g_z-1` yields
   `∫u g_z = [u h_z]_a^b - ∫h_z + ∫u`.
5. `[PROVED HERE]` Put `a=ε_n`, `b=1-ε_n`. Symmetry gives `∫_a^b u=0`. Monotone exhaustion and
   integrability give convergence of both integrals. The endpoint-square limits imply
   `h_z(ε_n),h_z(1-ε_n)→0`, hence the boundary term vanishes. Therefore
   `∫(t-1/2)g_z=-∫h_z`.
6. `[PROVED HERE]` Let `m=∫g_z=1` and `c=∫(t-1/2)g_z`. Then the rank-two moment pairing is
   `-(conj(m)c+conj(c)m)=-2 Re(c)`. Step 5 and `rootFlux_identity_thetaSource` give
   `Re(c)=-Im(z)E_z`, so the pairing equals `2 Im(z)E_z`.

All integrals and limits above are unconditional theorems. No RH-equivalent positivity input is
used.

## No-go closure for C25a

- **Exact killing theorem/mechanism:** `∫q|h|²<∞` controls `g/√q`, not `g`; weighted-source-space
  membership cannot be inferred without a new tail-ratio estimate.
- **Strongest positive survivor:** exact `L¹` monopole/dipole normalization and boundary-pairing law.
- **New insight:** actual divisor modes lie on the affine hyperplane `m=1`; off-line information is
  entirely the real part of one centered dipole, not an arbitrary rank-two boundary state.
- **Status:** dependency-closed paper proof; Lean formalization in progress.

## Door passport

- **Source purity:** theta source, explicit modes, quantile transform, and endpoint decay only.
- **No RH import:** no zero-location or positivity certificate.
- **Output:** canonical moment normalization and exact one-scalar obstruction.
- **Open core:** prove `Re c_z=0` from an independent corpus law.

## Log

- 2026-08-07 — C25a killed by exact weighted-exponent gap.
- 2026-08-07 — C25b–C25d dependency-closed paper and scratch Lean proofs completed.
