# Scale--Mautner pure-point blindness, compact-resolvent fracture, and cross-fibre spectral law

- **ID:** `ULF-SMFM-1`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [FIELD CANDIDATE NOT ACCEPTED]`
  `[NO ROUTE INPUT] [NOT RH] [LEAN-PROVED]`
- **Date:** 2026-08-14

## 1. Setup

Let `H` be a complex Hilbert space, let `U` be unitary, and let

\[
 V:\mathbb R\longrightarrow\mathcal U(H)
\]

be a strongly continuous unitary one-parameter group.  Fix `q>1` and assume the exact formation
scale law

\[
 \boxed{UV_tU^{-1}=V_{qt}\qquad(t\in\mathbb R).}
 \tag{SM.1}
\]

Write `H_pp(U)` for the closed span of all eigenvectors of `U`.

## 2. Scale--Mautner blindness

### Theorem 2.1 — every recurrent eigenmode is formation-blind

For every `t`,

\[
 \boxed{H_{\mathrm{pp}}(U)\subseteq\ker(V_t-I).}
 \tag{SM.2}
\]

Consequently, if `U` has pure-point spectrum, then

\[
 \boxed{V_t=I\quad\text{for every }t.}
 \tag{SM.3}
\]

### Proof

Let `xi` be a `U`-eigenvector, `U xi=lambda xi`, with `|lambda|=1`.  Iterating `(SM.1)` gives

\[
 V_t=U^nV_{t/q^n}U^{-n}.
\]

Therefore

\[
 \begin{aligned}
 \|V_t\xi-\xi\|
 &=\|U^nV_{t/q^n}U^{-n}\xi-\xi\|\\
 &=\|V_{t/q^n}\xi-\xi\|.
 \end{aligned}
\]

Strong continuity makes the last expression tend to zero as `n->infinity`.  The left side is
independent of `n`, hence is zero.  Thus every eigenvector is fixed by every `V_t`.  Continuity and
closedness of the fixed space give `(SM.2)`; density gives `(SM.3)`. QED.

This is the exact Mautner mechanism.  It says more than “a recurrent observer may lose history”:
the complete pure-point sector is forced to erase the dilated formation.

### Corollary 2.2 — continuous spectrum is necessary

If `V` is nontrivial, then `U` has a nonzero continuous-spectral sector.  In particular, no finite
dimensional same-fibre unitary model can realize `(SM.1)` nontrivially.

## 3. Compact-resolvent fracture

By Stone's theorem write

\[
 V_t=e^{itA}
\]

for a self-adjoint generator `A`.  Equation `(SM.1)` is equivalent, including domains, to

\[
 UAU^{-1}=qA.
\tag{SM.4}
\]

### Theorem 3.1 — exact same-fibre dilation excludes a nontrivial compact-resolvent clock

Assume `A` has compact resolvent.  Then

\[
 \boxed{A=0\quad\text{and}\quad\dim H<\infty.}
 \tag{SM.5}
\]

Conversely, `A=0` on a finite-dimensional `H` is the only compact-resolvent model.

### Proof

Unitary equivalence and scalar functional calculus give

\[
 \sigma(A)=\sigma(qA)=q\sigma(A).
 \tag{SM.6}
\]

If a nonzero `lambda` belongs to `sigma(A)`, then every `q^{-n}lambda` belongs to `sigma(A)`.
These are distinct and converge to zero.  A self-adjoint compact-resolvent operator has discrete
spectrum of finite multiplicity with no finite accumulation point, contradiction.  Hence
`sigma(A) subseteq {0}`.  The spectral theorem gives `A=0`.  Its resolvent is then a nonzero scalar
multiple of the identity, which is compact only when `H` is finite-dimensional.  The converse is
immediate. QED.

Thus compact-resolvent recurrence and exact scale covariance cannot be two gauges of one Hilbert
clock.  At least one must change fibre, topology, or mode of transport.

## 4. Quantitative finite-aperture anomaly

### Theorem 4.1 — bounded scale defect cannot remain cofinally small

Let `A_N` be a bounded positive operator and `W_N` unitary.  Define

\[
 K_N=W_NA_NW_N^{-1}-qA_N.
 \tag{SM.7}
\]

Then

\[
 \boxed{\|K_N\|\ge(q-1)\|A_N\|.}
 \tag{SM.8}
\]

Consequently, if `||A_N||->infinity`, then `||K_N||->infinity`.  Exact dilation can hold at every
finite aperture only by paying an anomaly whose global operator norm diverges.

### Proof

Unitary conjugation preserves norm, so the reverse triangle inequality gives

\[
 \begin{aligned}
 \|K_N\|
 &\ge\big|\|W_NA_NW_N^{-1}\|-\|qA_N\|\big|\\
 &=(q-1)\|A_N\|.
 \end{aligned}
\]

QED.

The finite inequality is the bounded-dilation parent already present in the constraint-relativity
corpus.  Its cofinal compact-clock interpretation is the new positive use here.

## 5. Common recovery cannot restore the erased sector

Let `E:H->K` be an isometric embedding intertwining two scale systems:

\[
 \widetilde U E=EU,
 \qquad
 \widetilde V_tE=EV_t,
 \qquad
 \widetilde U\widetilde V_t\widetilde U^{-1}=\widetilde V_{qt}.
 \tag{SM.9}
\]

### Corollary 5.1

Every `U`-eigenvector is fixed by `V_t`, and its recovered image is fixed by
`widetilde V_t`.  Hence a split isometric recovery cannot manufacture the missing continuous
formation sector.

### Proof

If `U xi=lambda xi`, then `E xi` is a `widetilde U`-eigenvector.  Theorem 2.1 gives
`widetilde V_tE xi=E xi`.  Intertwining and injectivity give `V_t xi=xi`. QED.

The Markov analogue is ULF-PFM-2: common-kernel packet formation is an exact KL and Jeffreys
isometry.  Recovery transports information already present; it does not create a scale-sensitive
sector erased by a recurrent observer.

## 6. Positive survivor: cross-fibre scale formation

Let `s>0`.  Give each scale a Hilbert fibre `H_s`, a self-adjoint clock `A_s`, and a unitary
transport

\[
 T_s:H_s\longrightarrow H_{qs}
\]

such that, with domains transported by `T_s`,

\[
 \boxed{A_{qs}T_s=qT_sA_s.}
 \tag{SM.10}
\]

### Theorem 6.1 — normalized clock conservation

Put `B_s=A_s/s`.  Then

\[
 \boxed{B_{qs}T_s=T_sB_s.}
 \tag{SM.11}
\]

Thus `B_s` is the conserved cross-fibre clock.  Moreover,

\[
 \boxed{\sigma(A_{qs})=q\sigma(A_s).}
 \tag{SM.12}
\]

If the clocks are positive with compact resolvent, their counting functions satisfy

\[
 \boxed{N_{qs}(\Lambda)=N_s(\Lambda/q).}
 \tag{SM.13}
\]

Whenever the displayed operators are trace class,

\[
 \boxed{
 \operatorname{Tr}(e^{-tA_{qs}})=\operatorname{Tr}(e^{-qtA_s}),
 \qquad
 \zeta_{A_{qs}}(z)=q^{-z}\zeta_{A_s}(z).}
 \tag{SM.14}
\]

### Proof

Divide `(SM.10)` by `qs` to obtain `(SM.11)`.  Unitary functional calculus gives
`A_(qs)=q T_sA_sT_s^{-1}`, proving `(SM.12)`.  Spectral projections then give `(SM.13)`.
Applying the same functional calculus to `exp(-t x)` and `x^{-z}`, followed by unitary invariance
of trace, proves `(SM.14)` on their trace-class domains. QED.

### Corollary 6.2 — recurrent scale projection has open lifted clock history

Suppose a scale quotient declares `s` and `q^n s` to be the same observer point.  No unitary
identification of their fibres can close the lifted history while respecting a nonzero
compact-resolvent clock.  Indeed, such a loop would give a same-fibre unitary `L` with

\[
 LA_sL^{-1}=q^nA_s,
\]

and Theorem 3.1 would force `A_s=0` and finite dimension.

Thus compact observer recurrence and open scale history are not an added covering-space metaphor;
they are forced by spectral admission plus exact cross-fibre formation.

## 7. Four-organ prediction

The theorem predicts a necessary anomaly in every finite approximation that tries to combine:

1. a compact-resolvent spectral clock;
2. exact source dilation;
3. unitary same-fibre transport;
4. cofinal global-operator admission.

At cutoff `N`, the anomaly is at least `(q-1)||A_N||`; therefore it cannot disappear cofinally.
Any mass-shift, spectral-trace, modular, or recurrence construction claiming all four properties
must expose one of:

- cross-fibre transport;
- continuous spectrum;
- an unbounded/domain-changing anomaly;
- a topology weaker than global operator norm;
- loss of the clock under observation.

This conclusion is obtained before reading any route-specific anomaly formula.

## 8. Hostile conjecture loops

1. **Projectivizing a recurrent scale orbit repairs covariance. — False.**  It closes only the
   observer point; Corollary 6.2 forbids faithful clock closure.
2. **Common recovery restores the missing scale direction. — False.**  Corollary 5.1 and KL
   isometry preserve its erasure.
3. **Compact resolvent and exact dilation can coexist through an infinite spectrum. — False.**
   Theorem 3.1 turns scale invariance of the spectrum into a forbidden finite accumulation.
4. **Finite exact models converge uniformly to the dilation law. — False.**  The anomaly lower
   bound grows with the clock aperture.
5. **Any recurrent sequence implies pure-point blindness. — False.**  Theorem 2.1 concerns the
   pure-point/relatively compact orbit sector; rigidity along one subsequence need not be pure
   point.
6. **Cross-fibre formation is new operator theory. — False.**  Hilbert bundles, product systems,
   wavelet semidirect products, and Mautner phenomena are established.  The live field claim is
   source generation of the fibre transport and identification of its unavoidable anomaly.
7. **The theorem proves RH. — False.**  No literal source comparison to the physical radial
   displacement is constructed here.

## 9. Literature boundary

- Carter, *On the unitary representation theory of locally compact contraction groups*,
  <https://arxiv.org/abs/2311.03041>.
- Gekhtman--Machado--Solan--Yifrach, *The Structure of Almost Stationary Measures*,
  <https://arxiv.org/abs/2608.01466> (quantitative Mautner mechanisms).
- Wang, *Self-adjoint extensions with compact resolvent*,
  <https://arxiv.org/abs/2601.11074>.
- Shalit--Skeide, *CP-Semigroups and Dilations, Subproduct Systems and Superproduct Systems*,
  <https://arxiv.org/abs/2003.05166>.

The parent ingredients are occupied.  The exact cross-corpus fracture and cross-fibre survivor are
new to this corpus; external priority is not claimed.

## 10. Lean status and next gate

Every theorem and corollary of §§2–6 is formalized unconditionally (certificate below), including
the domain statements: the Stone generator is built as a partially defined operator, (SM.4) and
(SM.10)–(SM.11) are identities of partially defined operators, and (SM.13)–(SM.14) are proved for
clock invariants independent of the chosen eigenbasis.  Theorem 4.1 holds for every bounded `A`.
Open research items 3–4 of the original gate (a literal source realization of `(SM.10)` and its use
in another organ) are not claims of this card.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.ScaleMautnerFormation`, `GaloisForLFunctions.HTGeometry.ScaleMautnerGenerator`, `GaloisForLFunctions.HTGeometry.ScaleMautnerCrossFibre`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules: `GaloisForLFunctions.HTGeometry.ScaleMautnerFormation` (Theorems 2.1, 3.1, 4.1, Corollaries 2.2, 5.1),
`GaloisForLFunctions.HTGeometry.ScaleMautnerGenerator` (the Stone generator, (SM.4), (SM.6), Theorem 3.1 for generators) and
`GaloisForLFunctions.HTGeometry.ScaleMautnerCrossFibre` (§6: (SM.10)–(SM.14), Corollary 6.2). Every module is clean under
`lake env lean`, builds as a module, and the axiom audit shows only `[propext, Classical.choice, Quot.sound]`.
The strongly continuous unitary group is the corpus `UnitaryFlow`; its generator is the partially defined operator
`A x = -i (d/dt)|₀ V_t x` on the vectors with differentiable orbit (`flowGenerator`), proved symmetric. Operator identities
between generators are stated with transported domains (`ScaleIntertwining`) and as equalities of `LinearPMap`s; the spectrum
of a partially defined operator is the complement of the points where `A - z` has a bounded two-sided inverse. A
compact-resolvent clock is a Hilbert basis of joint eigenvectors whose frequencies have finite sublevel sets
(`CompactResolventClock`); the eigenspace of frequency `ν` is proved equal to `ker(A - ν)`, and the functional calculus is
proved independent of the chosen clock, so heat semigroups, complex powers, heat traces and spectral zeta functions are
invariants of the flow. Theorem 4.1 is proved for every bounded `A` (positivity is not needed).

| Claim | Lean declaration |
|-|-|
| (SM.1) exact formation scale law | `IsScaleLaw` |
| Theorem 2.1 (SM.2) every eigenvector of `U` is fixed by every `V_t`; `H_pp(U) ⊆ ker(V_t - 1)` | `norm_op_sub_eq_div`, `op_eq_of_eigenvector`, `ppSubspace`, `fixedSubspace`, `ppSubspace_le_fixedSubspace` |
| Theorem 2.1 (SM.3) pure-point `U` forces `V ≡ 1` | `op_eq_id_of_pp` |
| Corollary 2.2 nontrivial `V` needs a continuous sector; no finite-dimensional nontrivial model | `ppSubspace_eq_top_of_finiteDimensional`, `continuous_sector_of_nontrivial` |
| (SM.4) `U A U⁻¹ = qA` with domains, from (SM.1) | `flowGenerator`, `generatorDomain`, `hasDerivAt_flowGenerator`, `flowGenerator_of_hasDerivAt`, `flowGenerator_symmetric`, `flowGenerator_transport`, `scaleIntertwining_flowGenerator`, `IsScaleLaw.scaleIntertwining`, `IsScaleLaw.unitaryConjugate_flowGenerator` |
| (SM.6) `σ(A) = qσ(A)` | `IsPMapResolvent`, `pmapSpectrum`, `ScaleIntertwining.isPMapResolvent`, `ScaleIntertwining.pmapSpectrum_eq`, `IsScaleLaw.pmapSpectrum_eq` |
| Theorem 3.1 (SM.5) compact resolvent + exact dilation forces `A = 0`, `V ≡ 1`, `dim H < ∞` (group and generator forms); converse | `CompactResolventClock`, `CompactResolventClock.trivial_of_freq_div`, `compactResolvent_scaleLaw`, `CompactResolventClock.flowGenerator_basis`, `CompactResolventClock.exists_freq_eq_of_generatorEigen`, `compactResolvent_generator_scaleLaw`, `flowGenerator_of_trivial`, `trivialClock_scaleLaw` |
| Theorem 4.1 (SM.7)–(SM.8) `‖WAW⁻¹ - qA‖ ≥ (q-1)‖A‖`; divergence along diverging apertures | `norm_scaleDefect_ge`, `tendsto_norm_scaleDefect` |
| Corollary 5.1 (SM.9) isometric intertwining recovery preserves the blindness | `recovery_fixed_of_eigenvector` |
| (SM.10) cross-fibre system; `A_{qs}T_s = qT_sA_s` with domains | `CrossFibreScaleSystem`, `CrossFibreScaleSystem.generator_intertwining`, `CrossFibreScaleSystem.unitaryConjugate_clockGenerator` |
| Theorem 6.1 (SM.11) `B_s = A_s/s` conserved; `B_s` generates the normalized flow, which `T_s` conjugates exactly | `CrossFibreScaleSystem.normalizedGenerator`, `CrossFibreScaleSystem.normalized_intertwining`, `CrossFibreScaleSystem.unitaryConjugate_normalizedGenerator`, `CrossFibreScaleSystem.normalizedClock`, `CrossFibreScaleSystem.normalizedClock_transport`, `CrossFibreScaleSystem.normalizedGenerator_generates`, `UnitaryFlow.timeRescale`, `scaleIntertwining_timeRescale`, `ScaleIntertwining.smul` |
| Theorem 6.1 (SM.12) `σ(A_{qs}) = qσ(A_s)` | `CrossFibreScaleSystem.spectrum_scaling` |
| Theorem 6.1 (SM.13) `N_{qs}(Λ) = N_s(Λ/q)`; for nonnegative compact-resolvent clocks `N` counts eigenvalues with multiplicity | `flowEigenspace`, `mem_flowEigenspace_iff_generator`, `flowLowSubspace`, `flowCounting`, `map_flowEigenspace`, `map_flowLowSubspace`, `flowCounting_transport`, `CompactResolventClock.flowLowSubspace_eq`, `CompactResolventClock.flowCounting_eq_card`, `CrossFibreScaleSystem.counting_scaling`, `CrossFibreScaleSystem.counting_scaling_card` |
| Theorem 6.1 (SM.14) `e^{-tA_{qs}} = T e^{-qtA_s} T⁻¹`, `A_{qs}^{-z} = q^{-z} T A_s^{-z} T⁻¹`; `Tr e^{-tA_{qs}} = Tr e^{-qtA_s}`, `ζ_{A_{qs}}(z) = q^{-z}ζ_{A_s}(z)` on trace class; traces are eigenvalue sums | `CompactResolventClock.calculus`, `CompactResolventClock.calculus_apply_of_mem`, `CompactResolventClock.calculus_eq`, `CompactResolventClock.transport`, `CompactResolventClock.calculus_transport`, `CompactResolventClock.heat`, `CompactResolventClock.negPower`, `CompactResolventClock.heat_eq`, `CompactResolventClock.negPower_eq`, `CompactResolventClock.heat_transport`, `CompactResolventClock.negPower_transport`, `CompactResolventClock.opTrace_calculus`, `CompactResolventClock.heatTrace`, `CompactResolventClock.spectralZeta`, `CompactResolventClock.heatTrace_eq_tsum`, `CompactResolventClock.spectralZeta_eq_tsum`, `CompactResolventClock.heatTrace_transport`, `CompactResolventClock.spectralZeta_transport`, `CrossFibreScaleSystem.heatTrace_scaling`, `CrossFibreScaleSystem.spectralZeta_scaling` |
| Corollary 6.2 a clock-respecting identification of `H_{qⁿs}` with `H_s` closes the lifted history into `L⁻¹A_sL = qⁿA_s`, forcing `A_s = 0`, `dim H_s < ∞` | `CrossFibreScaleSystem.exists_iterate_transport`, `CrossFibreScaleSystem.lifted_history_open`, `ScaleIntertwining.trans`, `ScaleIntertwining.symm` |

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
