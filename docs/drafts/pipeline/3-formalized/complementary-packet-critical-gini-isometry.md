# The complementary packet is a cofinal Gini isometry despite local zeta-two expansion

- **ID:** `complementary-packet-critical-gini-isometry`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-FRAMED FOUR-UNIT ENERGY
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Parents:**
  - `complementary-packet-euler-connection-weld.md`
  - `mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `gamma-sonin-asymptotic-passivity-incidence-curvature.md`
- **Statement:** The boundary complementary packet is not pointwise contractive in its divisor
  clock: at infinitesimal separation its squared metric coefficient is `zeta(2)>1`.  Nevertheless
  its squared distance at separation `a` is `a/(1+omega)^2+O(1)`, uniformly near the critical
  boundary.  Since the squarefree critical clock lives at separation `1/(sigma-1)`, the packet
  covariance has exactly four units of critical relative energy.  Entrywise Gamma completion and
  Sonin projection preserve this upper budget asymptotically.

## Boundary affine packet

Fix `0<omega<=omega_0` and put

```text
c_omega=1/(1+omega),
k_omega(t)=e^(-(1+omega)t)R_omega(e^t).                  (1)
```

At `delta=0`, the complementary packet is the affine path

```text
B_h(t)
 =1_(t>=h)k_omega(t-h)-c_omega 1_(t<h).                 (2)
```

Individual `B_h` are not in `L2(R_+)` because of the constant incoming branch.  Every difference
`B_h-B_k` is in `L2`, so `(2)` defines a genuine path in the affine Hilbert quotient by the common
constant mode.  This is the source-rigged boundary selected by the regularized packets as
`delta->0+`.

For `a>=0`, translation invariance of the affine difference gives

```text
D_omega(a)=||B_(h+a)-B_h||_2^2

 =integral_0^a|k_omega(r)+c_omega|^2dr
  +integral_0^infinity
     |k_omega(r+a)-k_omega(r)|^2dr.                      (3)
```

The right side is independent of `h`.

## Cofinal metric theorem `[PROVED HERE]`

There is a constant `C_(omega_0)` such that for every `0<omega<=omega_0` and every `a>=0`,

```text
|D_omega(a)-c_omega^2 a|<=C_(omega_0).                  (4)
```

### Proof

The elementary power-sum remainder estimate, uniformly for `0<omega<=omega_0`, gives

```text
|k_omega(t)|<=C(e^(-t)+e^(-(1+omega)t)).                 (5)
```

Hence the `L1` and `L2` norms of `k_omega` are uniformly bounded.  Subtracting `c_omega^2a` from
the first term of `(3)` leaves

```text
2c_omega integral_0^a k_omega(r)dr
 +integral_0^a|k_omega(r)|^2dr,                          (6)
```

whose absolute value is uniformly bounded by the `L1` and `L2` norms.  The second term of `(3)` is
at most `4||k_omega||_2^2`.  These bounds prove `(4)`. `QED`

In particular,

```text
D_omega(a)/a->c_omega^2                                 (7)
```

as `a->infinity`, uniformly near `omega=0`.

## Local expansion theorem `[PROVED HERE]`

At the opposite scale,

```text
lim_(a->0+)D_omega(a)/a=zeta(2).                         (8)
```

### Proof

The stitched profile in `(2)` has a unit jump at `0`.  At `log m`, `m>=2`, its jump is `m^(-1)`;
these values are independent of `omega`.  The locally absolutely continuous part has square-
integrable derivative between jumps and contributes `o(a)` to the translation modulus.  Each
jump of size `j` contributes `j^2a+o(a)`.  Since

```text
sum_(m>=1)m^(-2)=zeta(2),                                (9)
```

summation of the square-summable jump contributions proves `(8)`. `QED`

Thus no finite-clock pointwise inequality `D_omega(a)<=a` is available.  The successful metric
law is cofinal `(4)`, not local `(8)`.

## Exact critical four-unit packet energy `[PROVED HERE]`

Let

```text
P_sigma(d)=mu(d)^2d^(-sigma)/Z(sigma),
sigma=1+2omega,
H_sigma=log d under P_sigma,                             (10)
```

and let `H_sigma'` be an independent copy.  Define the source-framed packet curvature kernel

```text
K^B_sigma(d,e)
 =2psi_sigma(d)psi_sigma(e)
   (B_(log e)-B_(log d)).                                (11)
```

Its critical relative energy is

```text
E^B_sigma
 =epsilon sum_(d,e)||K^B_sigma(d,e)||_2^2
 =4epsilon E[D_omega(|H_sigma-H_sigma'|)].               (12)
```

By `(4)`,

```text
E^B_sigma
 =4c_omega^2 epsilon E|H_sigma-H_sigma'|+O(epsilon).     (13)
```

The critical exponential clock theorem gives

```text
epsilon E|H_sigma-H_sigma'|->1,                          (14)
```

and `c_omega->1`.  Therefore

```text
lim_(sigma->1+)E^B_sigma=4.                              (15)
```

Unlike the bare threshold curvature, `(11)` contains the full floor/power-sum packet path whose
connection was proved to synthesize the shifted-Euler source.  The four-unit calibration survives
that source framing without a fitted normalization.

## Gamma/Sonin completion

Apply the critical-line Gamma multiplier `mathcalG_omega` and the exact Sonin projection `Q_tau`
entrywise:

```text
K^(B,Gamma,Sonin)_(sigma,tau)(d,e)
 =Q_tau mathcalG_omega(K^B_sigma(d,e)).                  (16)
```

The Gamma multiplier norm tends to one and `Q_tau` is contractive.  Equations `(15)`--`(16)` give

```text
limsup_(sigma->1+)
 epsilon sum_(d,e)
 ||K^(B,Gamma,Sonin)_(sigma,tau)(d,e)||_2^2<=4.          (17)
```

This proves the source-framed Gamma/Sonin energy gate.  The remaining theorem is not a norm
estimate for `(16)`; it is the direct anti-causal identification and graph convergence of its
canonical relative readout to `ell_E`.

## No-go and positive HT statement

**No-go:** the raw packet is locally expansive by the exact coefficient `zeta(2)`.  Any proof
claiming a pointwise one-Lipschitz packet path is false.

**Positive statement:** the same path is an asymptotic affine isometry with slope
`1/(1+omega)^2`; the bounded local defect disappears against the escaping critical arithmetic
clock.  Critical passivity is therefore a cofinal probabilistic property, not a finite-clock
operator norm.

**General HT insight:** a constrained HT source can be locally expansive at every finite
resolution yet asymptotically passive on its distinguished escaping state.  Uniform operator
contractivity and source-specific critical passivity are inequivalent notions.

## Literature gate

Translation moduli, jump-square asymptotics, Gini mean differences, and power-sum remainder bounds
are established mechanisms.  Targeted searches have not located `(4)`, `(8)`, or the critical
packet energy `(15)` in this shifted-Euler/Suzuki setting.  Project inputs remain admissible;
external specialist audit is required before a novelty claim.

## Gates

- [x] boundary affine packet quotient defined
- [x] exact two-point metric formula proved
- [x] uniform cofinal affine metric proved
- [x] local `zeta(2)` expansion proved
- [x] pointwise contraction falsified positively
- [x] source-framed packet curvature kernel written
- [x] exact critical four-unit packet energy proved
- [x] Gamma/Sonin completion inserted asymptotically passively
- [ ] construct the canonical anti-causal relative readout
- [ ] prove direct pole-to-divisor identity
- [ ] prove graph convergence to `ell_E`
- [ ] independent specialist literature audit
- [ ] RH

## Formalization (in progress)

**Working state — a session that picks up this card should continue here, not restart.**

`[LEAN-PROVED]` The arithmetic core, estimate `(5)`, is compiled in
`formal/GaloisForLFunctions/RHTower/ComplementaryPacketPowerSumEnvelope.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; `#print axioms` = `propext,
Classical.choice, Quot.sound` on every theorem).

| Card item | Lean name |
|---|---|
| `R_ω(Y) = ∑_{m ≤ Y} m^ω − Y^(1+ω)/(1+ω)` | `RHTower.powerSumRemainder` |
| left/right Riemann sandwich for `x ↦ x^ω` | `RHTower.sum_rpow_range_le`, `RHTower.le_sum_rpow_range` |
| exact primitive increment `(b+1)^(1+ω) − b^(1+ω) ≤ (1+ω)(b+1)^ω` | `RHTower.rpow_succ_sub_le` |
| **sharp remainder bound** `\|R_ω(Y)\| ≤ (Y+1)^ω` for `Y ≥ 0` | `RHTower.abs_powerSumRemainder_le` |
| `k_ω(t) = e^(-(1+ω)t) R_ω(e^t)` | `RHTower.complementaryPacketKernel` |
| **`(5)`, sharpened**: `\|k_ω(t)\| ≤ 2^ω e^(-t)` for `t ≥ 0` | `RHTower.abs_complementaryPacketKernel_le` |

The Lean envelope is sharper than the card's `(5)`: instead of `C(e^{-t} + e^{-(1+ω)t})` it gives
the single term `2^ω e^{-t}`, with an explicit constant and no unnamed `C`.  Only monotonicity of
`x ↦ x^ω` (through mathlib's `MonotoneOn.sum_le_integral` / `MonotoneOn.integral_le_sum`) and the
exact power integral are used; no Euler–Maclaurin expansion and no asymptotic input enters, so the
bound is uniform in `0 < ω ≤ ω₀` as the card requires.

`[LEAN-PROVED]` The metric core, items `(3)`, `(4)` and `(7)`, is compiled in
`formal/GaloisForLFunctions/RHTower/ComplementaryPacketCofinalIsometry.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| half-line translation of an integral | `RHTower.setIntegral_Ioi_comp_add_right` |
| `(3)` the two-point modulus | `RHTower.packetTranslationModulus` |
| translated energy is dominated | `RHTower.setIntegral_translate_sq_le` |
| translation modulus `≤ 4` × energy | `RHTower.setIntegral_translationModulus_le` |
| **`(4)`** cofinal affine bound | `RHTower.abs_packetTranslationModulus_sub_le` |
| **`(7)`** cofinal slope `D(a)/a → c²` | `RHTower.tendsto_packetTranslationModulus_div` |

`(4)` is proved in the general form the paper argument actually establishes: for measurable `k`
integrable and square integrable on `(0,∞)` with `∫₀^∞ |k| ≤ A` and `∫₀^∞ k² ≤ B`,

```text
|D(a) − c² a| ≤ 5 B + 2 |c| A       for every a ≥ 0,
```

by the three pieces `∫₀^a k² ≤ B`, `|2c ∫₀^a k| ≤ 2|c| A`, and
`∫₀^∞ (k(·+a) − k)² ≤ 2∫₀^∞ k(·+a)² + 2∫₀^∞ k² ≤ 4B`, the middle translate being handled by
`MeasurePreserving.setIntegral_preimage_emb` for `r ↦ r + a`.  The bound depends on `k` only
through `A` and `B`, which is exactly what makes it uniform in `0 < ω ≤ ω₀`.

`[LEAN-PROVED]` The instantiation at the actual packet is compiled in
`formal/GaloisForLFunctions/RHTower/ComplementaryPacketKernelIntegrability.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| closed step form `k_ω(t) = e^(-(1+ω)t) ∑_{m ≤ e^t} m^ω − 1/(1+ω)` | `RHTower.complementaryPacketKernel_eq` |
| measurability | `RHTower.measurable_complementaryPacketKernel` |
| `L¹`, `L²` integrability on `(0,∞)` | `RHTower.integrableOn_complementaryPacketKernel`, `..._sq` |
| **uniform `L¹` bound** `∫₀^∞ \|k_ω\| ≤ 2^ω` | `RHTower.setIntegral_abs_complementaryPacketKernel_le` |
| **uniform `L²` bound** `∫₀^∞ k_ω² ≤ 4^ω` | `RHTower.setIntegral_complementaryPacketKernel_sq_le` |
| `c_ω = 1/(1+ω)` | `RHTower.complementaryPacketConstant` |
| **`(4)` at the actual packet** | `RHTower.abs_complementaryPacketModulus_sub_le` |
| **`(7)` at the actual packet** | `RHTower.tendsto_complementaryPacketModulus_div` |

The closed step form is what makes measurability immediate: the subtracted power integral
`(e^t)^(1+ω)/(1+ω)` cancels the exponential weight exactly and leaves the constant `1/(1+ω)`, so
the only non-continuous ingredient left is `Nat.floor`.  The `L²` constant is `4^ω` rather than
`4^ω/2` because `e^{-2t} ≤ e^{-t}` is used instead of a second exponential integral; the bound is
what matters and both are uniform on `0 ≤ ω ≤ ω₀`.

So the card's `(4)` now reads, unconditionally, for every `ω ≥ 0` and every `a ≥ 0`:

```text
|D_ω(a) − c_ω² a| ≤ 5·4^ω + 2 c_ω 2^ω ,
```

and `(7)` `D_ω(a)/a → c_ω²` as `a → ∞`.

`[LEAN-PROVED]` The four-unit transfer, items `(12)`–`(15)`, is compiled in
`formal/GaloisForLFunctions/RHTower/ComplementaryPacketFourUnitEnergy.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| `(13)` the exact collapse onto the Gini mean difference | `RHTower.abs_packetEnergy_sub_le` |
| **`(15)`** the four-unit limit | `RHTower.tendsto_four_mul_packetEnergy` |

`abs_packetEnergy_sub_le`: for a probability measure `μ`, a modulus `D` with
`|D a − c² a| ≤ C` on `a ≥ 0`, and `ε ≥ 0`,

```text
|4 ε E_μ[D(|x|)] − 4 c² (ε E_μ|x|)| ≤ 4 ε C ,
```

which is `(13)` with the `O(ε)` made explicit.  `tendsto_four_mul_packetEnergy` then concludes: for
a filtered family with `ε_i → 0`, `ε_i E|H−H'| → 1` and `c_i → 1`, the packet energy
`4 ε_i E[D_i(|H−H'|)] → 4`.  The statement is source independent — nothing about the packet
survives except its cofinal slope, and the bounded local defect (the `ζ(2)` expansion at
infinitesimal separation) is annihilated by the escaping clock, which is exactly the card's
positive statement.

### Discharging the transfer hypotheses

`[LEAN-PROVED]` The integrability hypothesis of the four-unit transfer is discharged in
`formal/GaloisForLFunctions/RHTower/ComplementaryPacketModulusMeasurable.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| the swept branch is monotone in the separation | `RHTower.monotone_packetSweptBranch` |
| the translation branch is measurable (Fubini) | `RHTower.measurable_packetTranslationBranch` |
| **`a ↦ D(a)` is measurable** | `RHTower.measurable_packetTranslationModulus` |
| **`Integrable (fun x => D |x|) μ`** for any probability `μ` with finite first moment | `RHTower.integrable_packetTranslationModulus_abs` |

The `L²` continuity of translation is **not** needed: measurability suffices, and it comes from two
elementary observations — the swept branch `a ↦ ∫₀^a (k+c)²` is monotone because its integrand is a
square, and the translation branch is measurable because `(a,r) ↦ (k(r+a) − k r)²` is jointly
measurable, so `StronglyMeasurable.integral_prod_right'` applies.  Integrability then follows from
the cofinal bound alone, since `|D(|x|)| ≤ c²|x| + C`.

`[LEAN-PROVED]` The rescaled transfer and its two source-side hypotheses are compiled in
`formal/GaloisForLFunctions/RHTower/ComplementaryPacketCriticalEnergy.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| rescaled four-unit transfer (the clock law is already `ε`-rescaled, so the modulus is read at `\|x\|/ε`) | `RHTower.tendsto_four_mul_rescaledPacketEnergy` |
| **uniform defect** `\|D_ω a − c_ω² a\| ≤ 14` for `0 ≤ ω ≤ 1/2` | `RHTower.complementaryPacketDefect_le` |
| the clock gap has a finite absolute first moment | `RHTower.integrable_abs_squarefreeMobiusCriticalGap` |

The rescaling matters and is now explicit: `squarefreeMobiusCriticalGapProbabilityMeasure σ` is the
law of `ε (log d − log e)`, so the source-framed energy is
`E_σ = 4 ε ∫ D_ω(|x|/ε) dμ_σ`, and the transfer is stated in exactly that form.  The defect bound
is made uniform near the boundary by `4^ω ≤ 2`, `2^ω ≤ 2`, `c_ω ≤ 1` for `ω ≤ 1/2`, giving the
single constant `14` that the filtered transfer requires.

`integrable_squarefreeMobiusCriticalGap_sq` in `MobiusIncidenceClockGiniFisherFourUnit.lean` was
`private`; it is now public (the only edit to that module), and
`integrable_abs_squarefreeMobiusCriticalGap` derives the absolute moment from it by
`|x| ≤ (x² + 1)/2`.

`[LEAN-PROVED]` **`(15)` is closed at the actual source.**

| Content | Lean name |
|---|---|
| scaled integrability of the modulus | `RHTower.integrable_packetTranslationModulus_abs_div` |
| the source-framed critical packet energy | `RHTower.complementaryPacketCriticalEnergy` |
| **`(15)`** `lim_{σ → 1+} E^B_σ = 4` | `RHTower.tendsto_complementaryPacketCriticalEnergy` |

```lean
theorem RHTower.tendsto_complementaryPacketCriticalEnergy :
    Tendsto complementaryPacketCriticalEnergy (nhdsWithin 1 (Ioi 1)) (nhds 4)
```

with

```lean
complementaryPacketCriticalEnergy σ =
  4 * (σ - 1) *
    ∫ x, packetTranslationModulus (complementaryPacketKernel ((σ-1)/2))
        (complementaryPacketConstant ((σ-1)/2)) (|x| / (σ-1))
      ∂(squarefreeMobiusCriticalGapProbabilityMeasure σ)
```

Everything the paper proof uses is present and nothing else: the uniform envelope gives the uniform
`L¹`/`L²` bounds, those give the cofinal bound `(4)` with a defect uniform for `ω ≤ 1/2`, and the
rescaled transfer turns the escaping Gini limit `∫|x| dμ_σ → 1` together with `c_ω → 1` into the
value four.  The locally expansive `ζ(2)` coefficient never enters: it is inside the bounded defect
that the escaping clock annihilates, which is exactly the card's positive statement.

`[LEAN-PROVED]` **`(8)` and the no-go are closed.**  Compiled in
`formal/GaloisForLFunctions/RHTower/ComplementaryPacketLocalZetaTwo.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| step profile `k_ω + c_ω = e^(-(1+ω)t) ∑_{m ≤ e^t} m^ω` | `RHTower.packetStepSum`, `RHTower.complementaryPacketKernel_add_const` |
| jump mass swept by a translation | `RHTower.packetJump` |
| **increment identity** `Δ_a k = jump + drift` | `RHTower.complementaryPacketKernel_sub_eq` |
| uniform drift bound `≤ 5a` | `RHTower.abs_packetDrift_le` |
| swept jump mass `≤ (⌊e^(r+a)⌋ − ⌊e^r⌋) e^(-r)` | `RHTower.packetJump_le` |
| increment envelope `≤ 4 e^(-r)` | `RHTower.abs_complementaryPacketKernel_sub_le` |
| **tail bound** `∫_{log N}^∞ (Δ_a k)² ≤ 50 a/N` | `RHTower.setIntegral_complementaryPacketKernel_sub_sq_tail` |
| **quantitative local expansion** | `RHTower.abs_complementaryPacketModulus_sub_partialZeta_le` |
| **`(8)`** `lim_{a→0+} D_ω(a)/a = ζ(2) = π²/6` | `RHTower.tendsto_complementaryPacketModulus_div_nhdsGT` |
| **the no-go**: `a < D_ω(a)` near zero | `RHTower.eventually_lt_complementaryPacketModulus` |

The quantitative form is the content; the limit is a corollary.  For `0 < ω ≤ 1/2`, `N ≥ 1` and
`0 < a ≤ 1/(4(N+1))`,

```text
| D_ω(a) − a·∑_{n ≤ N} 1/n² |  ≤  60 N a² + 50 a/N .
```

Two regions.  Beyond `log N` the increment identity bounds `|Δ_a k|` by the crossed-integer count
`(⌊e^(r+a)⌋ − ⌊e^r⌋)e^(-r)` plus `5a`; multiplying by the envelope `4e^(-r)` and integrating gives
`O(a/N)` — the `a` factor comes from the exact translation identity
`∫_{Ioi L} ⌊e^(r+a)⌋e^(-2r) = e^(2a)∫_{Ioi (L+a)} ⌊e^u⌋e^(-2u)`, not from a discrepancy estimate.
Below `log N` the window `[log(m+1) − a, log(m+1))` is the only place where the translation crosses
an integer once `a ≤ 1/(4(m+1))`, so the square of the increment linearises: off the window the
increment is pure drift `O(a)`, and on the window it is within `7a` of `1/(m+1)`, the exact jump.
Summing the `N` pieces and adding the swept branch — whose profile is `e^(-(1+ω)r)` for
`0 < r < log 2`, contributing the jump `1` at the origin — gives the displayed bound.

Both the `O(a²)` and the `O(a/N)` errors are explicit, so `(8)` follows by choosing `N` with
`50/N < ε/3` and then `a` with `60Na < ε/3`.  Since `π²/6 > 1`, the packet is locally expansive and
`RHTower.eventually_lt_complementaryPacketModulus` falsifies pointwise contractivity outright — the
card's no-go half, now machine-checked.

### Remaining

Nothing in the formalisation.  Every `[PROVED HERE]` item of this card — `(3)`, `(4)`, `(5)`, `(7)`,
`(8)`, `(12)`, `(13)`, `(15)` and the no-go — is compiled unconditionally in Lean.  The open gates
below (`anti-causal readout`, `pole-to-divisor identity`, `graph convergence to ℓ_E`, specialist
audit, RH) are open **research**, not open formalisation.
