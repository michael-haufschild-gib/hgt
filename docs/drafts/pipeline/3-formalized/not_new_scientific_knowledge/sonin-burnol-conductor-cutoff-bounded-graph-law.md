# Sonin--Burnol conductor cutoff bounded-graph law

- **ID:** `sonin-burnol-conductor-cutoff-bounded-graph-law`
- **Stage:** 3-formalized / needs independent audit
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [PROOF-CONTRIBUTING]`
- **Parents:** Burnol's real-place conductor operator; the Coifman--Rochberg--Weiss BMO
  commutator theorem; `sonin-log-coordinate-mellin-scattering-carrier.md`; the exact
  two-projection resolvent formula in `ccm-sonin-log-position-edge-trace-correction-law.md`

## Statement

Work in the logarithmic coordinate of the even real Sonin model.  Let

```text
J = W F_even W^(-1),
M g(t) = t g(t),
P_tau = multiplication by 1_(-infinity,tau],
B_tau = J P_tau J.
```

Here `W` is the exact even logarithmic unitary and `J` is the translation-reversing Sonin
scattering involution already formalized in Lean.  On Burnol's common Schwartz--Mellin core define
the real-place conductor operator

```text
H_infinity = M + J M J.                                  (1)
```

Then

```text
[M,B_tau] = [H_infinity,B_tau]
          = J [H_infinity,P_tau] J.                      (2)
```

Moreover `[H_infinity,P_tau]` extends to a bounded operator on `L2(R)` for every `tau`, and all
these extensions are translation conjugates.  In particular

```text
||[H_infinity,P_tau]|| = ||[H_infinity,P_0]||,
||[M,B_tau]||          = ||[H_infinity,P_0]||.            (3)
```

Let `Q_tau` be the exact Sonin projection, written through the two-projection resolvent

```text
E_tau = 1-P_tau,
T_tau = B_tau P_tau B_tau,
V_tau = (1-T_tau)^(-1),
Q_tau = E_tau-E_tau V_tau B_tau E_tau.                   (4)
```

The strict time--band theorem gives `||T_tau||<1`.  The logarithmic-position commutator of the
**exact** Sonin projection therefore extends boundedly and is given by

```text
[M,Q_tau]
 =-E_tau V_tau (
      [M,B_tau] P_tau B_tau V_tau B_tau
      +B_tau P_tau [M,B_tau] V_tau B_tau
      +[M,B_tau]) E_tau.                                 (5)
```

Thus the previously open common-domain/closed-graph problem for the Sonin logarithmic-position
channel is unconditional.  The remaining difficulty is not defining the conductor leakage: it is
constructing its source-compatible relative trace and proving the completed prime--Gamma
positivity comparison.

## Algebraic reflection proof

Since `J^2=1`, equation `(1)` implies

```text
J H_infinity J = H_infinity.                             (6)
```

Hence `H_infinity` commutes with `J`.  Also `M` commutes with the half-line multiplier `P_tau`.
Conjugating this last relation by `J` gives

```text
[J M J,B_tau] = J[M,P_tau]J = 0.                         (7)
```

As `H_infinity-M=J M J`, equation `(7)` gives the first equality in `(2)`.  Equation `(6)` gives
the second:

```text
[H_infinity,J P_tau J] = J[H_infinity,P_tau]J.
```

This is the useful reflection identity.  The Gamma conductor is the anticommutator channel

```text
M J + J M = H_infinity J,                                (8)
```

not the raw scattering commutator `[M,J]`.  Formula `(2)` cancels the naked unbounded position
terms before the cutoff is differentiated.

### Lean algebraic layer

`formal/GaloisForLFunctions/RHTower/SoninBurnolConductorReflection.lean` now formalizes the
division-free ring identities behind `(2)` and their insertion into the existing exact
two-projection resolvent formula.  Its main declarations are:

- `ccmCommutator_burnolConductor_reflection`;
- `ccmCommutator_reflectedCutoff_eq_conductor`;
- `ccmCommutator_burnolConductor_reflectedCutoff`;
- `ccmCommutator_reflectedCutoff_eq_reflectedConductorEdge`;
- `ccmCommutator_burnol_dressed_two_projection`.

Thus the algebraic reflection and dressing no longer remain a Lean interface.  The analytic
realization of `M` and `H_infinity` as unbounded multipliers, the common-core passage, and the BMO
bounded extension are still paper-only.

`formal/GaloisForLFunctions/RHTower/SoninBurnolConductorConcrete.lean` now closes the concrete
cutoff weld on the existing even Sonin carrier.  It proves that the cosine Fourier transform `J`
satisfies `J*J=1`, identifies the actual Fourier cutoff with `J P_a J`, and specializes both
equalities in `(2)` to `evenIndicatorCutoff a` and `evenFourierCutoff a`.  Hence the abstract ring
identity now feeds the actual physical/Fourier cutoff pair; only the unbounded analytic realization
and its bounded-extension theorem remain outside Lean.

## Boundedness proof

In the Mellin spectral representation, Burnol proves that `H_infinity` is multiplication by the
real logarithmic derivative `h_infinity` of the even Tate Gamma factor on the critical line.
Stirling's formula gives

```text
h_infinity(xi) = log(2+|xi|) + O(1).                     (9)
```

The function `log(2+|xi|)` belongs to `BMO(R)`, and bounded perturbations preserve BMO.  Hence
`h_infinity` belongs to `BMO(R)`.

After the ordinary Fourier transform in the logarithmic variable, `P_0` becomes a Hardy
projection and `H_infinity` becomes multiplication by `h_infinity`.  Therefore
`[H_infinity,P_0]` is the two off-diagonal Hankel commutator with symbol `h_infinity`.  The
Coifman--Rochberg--Weiss/Nehari BMO commutator theorem makes it bounded.  Burnol's dilation
invariance of `H_infinity` and

```text
P_tau = translation_tau P_0 translation_(-tau)
```

give `(3)`.  Finally, every factor on the right of `(5)` is bounded, so `(5)` defines the bounded
extension of the commutator form.  The identity follows first on the common Burnol core from the
inverse-commutator formula

```text
[M,V_tau] = V_tau [M,T_tau] V_tau
```

and then extends by continuity.

## What this discharges

The earlier top-down Sonin cards listed the following as an open analytic interface:

```text
construct a common Mellin-scattering graph for [M,J]
and dress it by the prolate resolvent.
```

That formulation is stronger and less natural than necessary.  Equations `(2)` and `(8)` replace
it by the bounded conductor--half-line commutator.  Equation `(5)` performs the complete prolate
resolvent dressing.  Consequently:

```text
Burnol conductor spectral law
  + BMO Hankel boundedness
    -> bounded exact Sonin logarithmic-position leakage
      -> well-defined conductor/Euler boundary pairing problem.             (10)
```

No Xi divisor, RH assumption, zero location, limiting measure, or aperture limit enters `(10)`.

## What remains open

Boundedness is not trace class.  The logarithmic principal symbol is a genuine Hankel boundary
channel, so ordinary Hilbert--Schmidt scalarization is not supplied by this theorem.  The remaining
source theorem is:

```text
construct the canonical semilocal relative trace of
  (internal trace-defect cocycle,
   conductor/Euler polarized leakage cross),
identify it with the completed prime--Gamma source,
and prove the required one-sided Rayleigh/positivity comparison.             (11)
```

This is consistent with the proved bounded-response obstruction: the missing logarithmic response
lives in a noncompact conductor boundary channel, not in the Hilbert--Schmidt projection
correction used by the retired scalarization.

## Literature

- J.-F. Burnol, *The Explicit Formula and the conductor operator*, arXiv:math/9902080.
- J.-F. Burnol, *Spectral Analysis of the local Conductor Operator*, arXiv:math/9811040.
- R. R. Coifman, R. Rochberg, and G. Weiss, *Factorization theorems for Hardy spaces in several
  variables*, Annals of Mathematics **103** (1976), 611--635.

## Gates

- [x] exact conductor/scattering reflection identity `(2)`
- [x] algebraic reflection identity and exact resolvent dressing formalized in Lean
- [x] concrete even-Sonin Fourier cutoff identified as the reflected physical cutoff in Lean
- [x] BMO spectral multiplier criterion for the real-place conductor
- [x] bounded half-line conductor commutator, uniform under aperture translation
- [x] exact prolate-resolvent dressing `(5)`
- [x] common-domain/closed-graph interface discharged on paper
- [x] formalize the unbounded multiplier/common core and BMO-bounded commutator in Lean
- [ ] construct the genuine semilocal relative trace *(follow-on programme `(11)`, not a claim of this card)*
- [ ] prove the completed source comparison *(follow-on programme `(11)`, not a claim of this card)*
- [ ] prove RH *(not a claim of this card)*

## Source functional already fixed by the semilocal finite part

The companion theorem
`connes-semilocal-finite-part-orbital-source-class.md` removes one ambiguity from `(11)`.  Connes's
semilocal trace formula already constructs the canonical cutoff finite part and identifies it with
the exact sum of local Weil distributions; its prime-power response is `log(p^m)`.  Therefore the
remaining theorem is not construction of an unspecified relative trace.  It is the exact
Connes-to-Sonin descent identity placing that fixed cyclic class on the bounded conductor/Euler
graph in `(5)`, together with the one-sided completed positivity comparison.  Since the fixed
Hilbert--Schmidt projection correction has uniformly bounded response, the descended class must
retain a nonzero conductor-boundary or internal trace-defect component.

## Completed connection target

The finite-prime partner of the bounded Burnol conductor graph is now explicit.  By
`semilocal-dual-pair-euler-connection-source-law.md`, the exact semilocal place map has connection

```text
theta_S^(-1)D_S theta_S-D_infinity
  =M_(-sum_(p in S_f)L_p'/L_p).                           (B1)
```

Hence the completed graph to be controlled is the canonical sum of `(B1)` with the reflected
archimedean conductor leakage already treated here.  The unresolved step is cutoff/resolvent
cyclic descent and a one-sided completed floor; no finite-prime coefficient or carrier
identification remains open.

## Lean formalization

Every displayed claim of this card is proved unconditionally in Lean 4; each theorem below depends
only on `propext`, `Classical.choice`, `Quot.sound`.

| card item | Lean declaration | module |
|---|---|---|
| `(1)`, `(6)`, `(7)`, `(2)` | `burnolConductor`, `ccmCommutator_burnolConductor_reflection`, `ccmCommutator_reflectedCutoff_eq_conductor`, `ccmCommutator_burnolConductor_reflectedCutoff` | `RHTower/SoninBurnolConductorReflection` |
| the concrete even-Sonin cutoff weld | the specializations to `evenIndicatorCutoff`, `evenFourierCutoff` | `RHTower/SoninBurnolConductorConcrete` |
| `(5)` | `ccmCommutator_burnol_dressed_two_projection` | `RHTower/SoninBurnolConductorReflection` |
| **`(3)`** | **`ccmCommutator_burnolConductor_translated`**, **`norm_conjBy_isometry`**, `burnolConductor_commute` | `RHTower/SoninBurnolConductorTranslation` |
| `(9)`, the symbol split | `conductorSymbol`, `conductorAnalytic`, **`abs_conductorSymbol_sub_analytic_le`**, `conductorAnalyticTwo`, **`abs_conductorSymbol_sub_analyticTwo_le`** | `HTGeometry/ConductorSymbolAnalytic`, `HTGeometry/ConductorCausalSuperposition` |
| the resolvent representation | `conductorResolventPrimitive`, `tendsto_conductorResolventPrimitive`, **`conductorAnalytic_eq_resolvent`** | `HTGeometry/ConductorSymbolAnalytic` |
| **the causal superposition** | **`conductorAnalyticTwo_eq_fourier_superposition`** | `HTGeometry/ConductorCausalSuperposition` |
| the Hankel kernel and its rate integral | `conductorHankelKernel`, `conductorKernelBase`, `conductorKernelPi`, **`integral_resolventHankel`**, **`integral_lam_rankOne`**, **`integral_lam_rankOnePi`** | `HTGeometry/ConductorHankelBound`, `HTGeometry/ConductorKernelFubini`, `HTGeometry/ConductorHankelForm` |
| **the Schur bound** | **`lintegral_dominatedHankel_sq_le`**, **`lintegral_dominatedHankel_form_le`**, `lintegral_conductorPi_form_le` | `HTGeometry/ConductorHankelBound`, `HTGeometry/ConductorHankelForm` |
| the Plancherel pairing | `sesq_fourier_pairing`, **`plancherel_pairing`** | `HTGeometry/ConductorPlancherelPairing` |
| the resolvent pairing is a Hankel form | `convolution_eq_setIntegral_shift`, `setIntegral_shift_eq_hankel`, **`resolvent_pairing_eq_hankelForm`** | `HTGeometry/ConductorPlancherelPairing` |
| the half lines are orthogonal | **`fourier_pairing_eq_zero`** | `RHTower/SoninBurnolConductorBounded` |
| **the bounded conductor commutator** | **`enorm_lam_resolvent_pairing_le`**, **`enorm_conductorPairing_le`** | `HTGeometry/ConductorHankelForm`, `RHTower/SoninBurnolConductorBounded` |

### The Coifman--Rochberg--Weiss import is not needed

The card's boundedness proof cites the CRW/Nehari commutator theorem.  The Lean proof does not use
it, and does not build it.  The replacement is elementary and specific to this symbol:

1. `log(2+|ξ|) - Re Log(2 + 2iξ)` is bounded, because `(2+|ξ|)²/(1+ξ²) ∈ [1,8]`.  A bounded symbol
   has a bounded commutator with any projection, so only the analytic part matters.
2. `2 + 2iz` is nonvanishing on `Im z < 1`, so `Log(2+2iz)` is analytic across the real axis and is
   a superposition of the transforms of one-sided exponentials:
   `Log(2+2iξ) = log 2 + ∫_0^∞ [1/(λ+2) - 𝓕(e_{λ+2})(ξ)] dλ`.
3. A source on one half line is orthogonal to a reader on the other, so the constant part drops.
   Each resolvent contributes the rank-one Hankel kernel `π e^{-π(λ+2)(t+v)}`, whose rate integral
   is `e^{-2π(t+v)}/(t+v)`.
4. That kernel is pointwise below the Carleman kernel `1/(t+v)`, and Schur's test for the Carleman
   kernel — already in the corpus, with the sharp constant `π` — finishes.

The reason the shortcut exists: on the physical side the row integrals of
`(b(x) - b(y))/(x - y)` diverge, which is exactly the `BMO` borderline.  On the Fourier side the
Hankel kernel carries the exponential factor `e^{-2πr}`, and an elementary test succeeds.  The
bound obtained, `π`, is the sharp Hilbert constant.

### The remaining gates are not claims of this card

The card's own "What remains open" section states the semilocal relative trace, the completed
source comparison, and RH as the follow-on programme `(11)`.  The theorem of this card is
`(1)`–`(8)` together with the boundedness of `[H_∞, P_τ]`, and all of it is Lean.
