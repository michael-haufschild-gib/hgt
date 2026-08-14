# Prime-log jump packets give a conormal-faithful Sonin boundary grade frame — formalized

- **ID:** `prime-log-jump-sonin-mellin-grade-frame-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `prime-log-jump-sonin-mellin-grade-frame.md`
- **Umbrella imports:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `RHTower/PrimeLogJumpPacket.lean` | the shell `1_{A<\|x\|<B}`, the mean `μ_κ`, the packet `u_κ`, the two vanishing conditions `(8)` and the exact mass `(9)` |
| `RHTower/SoninAmplitudePacket.lean` | **new** — `AnnulusAmplitude`: an even, measurable, bounded, annulus-supported amplitude of positive mass; its packet, `L²` class, uniform bound, mean decay, and physical cutoffs |
| `RHTower/SoninAmplitudeFourier.lean` | **new** — weak escape, compact vanishing, the packet's Fourier transform, its spectral density (Plancherel), the modulation identity, the band-energy bounds and the two concentration limits, all for a general amplitude |
| `RHTower/SoninAmplitudeCoupling.lean` | **new** — the dilated packet, the aperture-layer limit, the doubly contracted packet, and the two boundary limits `(12)`–`(13)` for a general amplitude |
| `RHTower/PrimeLogJumpSoninCoupling.lean` | **new** — the jump shell *is* an `AnnulusAmplitude`; `(12)`–`(13)` for the discontinuous packet |
| `RHTower/PrimeLogJumpMellinFrame.lean` | the shell average `H(s)`, the two channels `F_A`, `F_B`, and the exact classification of their common zeros `(22)`–`(23)` |
| `RHTower/PrimeLogJumpMellinTrace.lean` | **new** — the first integration by parts on the Mellin kernel |
| `RHTower/PrimeLogJumpMellinRemainder.lean` | **new** — the second integration by parts and the explicit `O(1/κ)` bound on the residual |
| `RHTower/PrimeLogJumpMellinAsymptotic.lean` | **new** — `(16)`: the exact first Mellin boundary trace with vanishing residual |
| `HTGeometry/PairPhaseClock.lean` | **new** — two frequencies with irrational ratio are rationally independent (and conversely), and the forward-orbit clock steering both phases at arbitrarily late times |
| `RHTower/PrimeLogJumpMellinLimit.lean` | **new** — `(18)`–`(21)`: the two source-defined clocks and their two channel limits |
| `RHTower/PrimeLogJumpBVWindow.lean` | **new** — `(26b)`–`(26e)`: the two compact BV windows, `s·G = F`, and the absence of any common zero |
| `RHTower/PrimeLogJumpGradeLaw.lean` | **new** — `(14)`, `(27)`–`(30)`: the ray Mellin evaluation, the exact dilation grade, and the critical-line falsifier |
| `RHTower/PrimeLogJumpShell.lean` | **new** — `A = log p / 2`, `B = log q / 2`, irrationality of `A/B`, and the assembled two-prime frame |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `integral_jumpPacket_eq_zero`, `tendsto_jumpMean_atTop`, `integral_jumpPacket_sq`,
  `tendsto_integral_jumpPacket_sq` — `(6)`–`(9)`: the packet is an exact two-condition Poisson
  source test and its mass tends to the shell half-width;
- **`RHTower.AnnulusAmplitude.tendsto_norm_soninApertureCoupling_ampPacketEven_sub`** — `(12)` for
  an arbitrary annulus amplitude; **`…_adjoint_soninApertureCoupling_ampDilatedPacket_sub`** —
  `(13)`;
- **`tendsto_norm_soninApertureCoupling_jumpPacket_sub`**,
  **`tendsto_norm_adjoint_soninApertureCoupling_jumpDilatedPacket_sub`** — the same two limits for
  the discontinuous prime-log shell, via `jumpAmplitude`;
- `jumpAmplitude_ampPacket` — away from zero frequency the amplitude's packet *is* the jump packet,
  so the boundary limits and the Mellin trace speak about one family;
- `integral_cpow_mul_cos`, `integral_cpow_mul_sin`, `norm_integral_cpow_mul_sin_le`,
  `tendsto_integral_cpow_mul_sin` — the two integrations by parts and the explicit `O(1/κ)`
  residual bound;
- **`jumpMellin_trace`** — `(16)` as an exact identity, with `tendsto_jumpMellin_residual` for the
  vanishing of its residual;
- `HTGeometry.linearIndependent_pair_of_irrational`,
  `HTGeometry.irrational_div_of_linearIndependent_pair`,
  **`HTGeometry.exists_clock_seq`** — `(17)`: the continuous two-frequency Kronecker flow has dense
  forward tails, so a cofinal clock realises any prescribed pair of phases;
- **`exists_clock_tendsto_channelA`**, **`exists_clock_tendsto_channelB`** — `(18)`–`(21)`: two
  source-defined clocks along which `κ M_κ(s)` converges to `F_A(s)` and to `F_B(s)`, at every
  complex `s`;
- `eq_zero_of_channel_common_zero` — `(22)`–`(23)`: `s = 0` is the only common zero of the two
  channels;
- **`mul_windowMellinA`**, **`mul_windowMellinB`** — `(26c)`, `(26e)`: `s·G_A = F_A`, `s·G_B = F_B`
  by Stieltjes integration by parts against the two total-mass-zero cumulative functions, with no
  division by `s`, hence valid at every point;
- `windowMellinA_zero_ne`, `windowMellinB_zero_ne` — `(24)`: both windows are strictly negative on
  the open shell, so both desingularized channels are nonzero at the origin;
- **`no_common_zero_windowMellin`** — `(25)`: the pair `(G_A, G_B)` has no common zero anywhere in
  the plane;
- `rayMellin_jumpPacket` — `(14)`: the positive-ray Mellin evaluation of the packet is the shell
  integral;
- **`rayMellin_unitaryDilation`** — `(28)`: `M(U_{1/r} f)(s) = r^{1/2-s} M f(s)` exactly;
- `norm_dilation_multiplier`, `re_eq_half_of_norm_multiplier_eq_one`,
  **`re_eq_half_of_rayMellin_dilation_norm_eq`** — `(29)`–`(30)`: the grade of the dilation
  multiplier is `r^{1/2 - Re s}`, and grade preservation of a *nonzero* Mellin normal forces
  `Re s = 1/2`;
- `linearIndependent_logPrime_pair`, `irrational_primeShellEnd_ratio` — `(4)`: unique factorization
  makes the two shell endpoints incommensurable;
- **`primeLogJumpFrame`** — the assembled statement for a two-prime shell: two clocks realising the
  two channels, the two BV-window identities, and coprimality.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/SoninAmplitudePacket.lean
lake env lean GaloisForLFunctions/RHTower/SoninAmplitudeFourier.lean
lake env lean GaloisForLFunctions/RHTower/SoninAmplitudeCoupling.lean
lake env lean GaloisForLFunctions/RHTower/PrimeLogJumpSoninCoupling.lean
lake env lean GaloisForLFunctions/HTGeometry/PairPhaseClock.lean
lake build GaloisForLFunctions.RHTower.PrimeLogJumpShell
lake build GaloisForLFunctions.RHTower.PrimeLogJumpSoninCoupling
```

## What closed last

The card's Lean route asked for four things.

1. **Generalize the Sonin packet lemmas from the fixed smooth bump to a nonzero even `L¹ ∩ L²`
   amplitude with strict annulus support.**  The corpus's coupling architecture turned out to be
   already amplitude-blind at the operator level: the two-branch estimate
   `norm_soninApertureCoupling_sub_dilate_le` sees a vector only through two physical cutoffs.  What
   was smooth-specific was the analytic layer — weak escape, the Fourier transform, the spectral
   density, the band bounds.  Each of those uses continuity only to get integrability, and
   `AnnulusAmplitude.integrable_of_bound` supplies that from boundedness plus compact support.  So
   the three new `SoninAmplitude*` modules carry the whole chain for a measurable amplitude.
2. **Instantiate with the prime-log indicator shell.**  `jumpAmplitude` is the instance; `(12)` and
   `(13)` follow with no new analysis, exactly as the card's §2 predicted.
3. **The locally uniform Mellin asymptotic `(16)` and the clocks `(18)`–`(19)`.**  `(16)` is proved
   as an *identity* — one integration by parts plus `κ μ_κ (B − A) = sin(κB) − sin(κA)` — with the
   residual `s ∫ x^{-s-1} sin(κx) dx` bounded by an explicit constant over `κ` from a second
   integration by parts.  The clocks come from the corpus's forward-orbit Kronecker theorem
   (`HTGeometry.dense_forwardOrbit`) applied to the two-element frequency family `(A, B)`, whose
   rational independence is exactly the irrationality of `A/B`.
4. **The coprime frame `(22)`–`(26)` and the scaling law `(28)`.**  The desingularized channels are
   defined as the Mellin transforms of the two literal BV windows of `(26b)`, and `s·G = F` is
   proved by integration by parts against the cumulative functions — which needs no division by `s`
   and therefore holds at the origin too.  Both windows are strictly negative on the open shell, so
   neither transform vanishes at `s = 0`; combined with the classification of the common zeros of
   `F_A, F_B`, the pair has no common zero anywhere.  The scaling law is mathlib's
   `mellin_comp_mul_left` in the corpus's `x^{-s}` normalization.

## Boundary

- The **Cartan–Bezout identity** `(26)` itself — entire `C_A, C_B` with `C_A G_A + C_B G_B = 1` —
  is the classical Wedderburn theorem for entire functions and rests on Weierstrass products, which
  mathlib does not have.  Nothing above uses it: every downstream statement of the card needs only
  "at least one channel is nonzero at `ρ`", which is `no_common_zero_windowMellin`.
- `(24)` is formalized as the *value* `G_A(0) < 0`, `G_B(0) < 0` rather than as `F_A'(0)`,
  `F_B'(0)`; by `(26e)` these are the same number, but identifying it with a derivative would need
  holomorphy of the window transform, i.e. differentiation under the integral sign.
- The card's four remaining gates are unchanged and are declared open cores there: the canonical
  undeconvolved source-action intertwiner, closed-graph continuity of both the dagger and the Mellin
  normal, a positive self-adjoint Xi spectral realization, and RH.  `(30)` is formalized in exactly
  the conditional form the card states — it is a falsifier for the missing dagger, not a proof of
  RH.
- The independent specialist literature audit is external and remains open.
