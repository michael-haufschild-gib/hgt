# Hahn-label approximation spectrum, observer deficit, and tensor convergence law

- **Stage:** 3-formalized

- **ID:** ULF-TAFM-6
- **Status:** `[PAPER-PROVED]`; `[LEAN-CERTIFIED]`; `[BRIDGE]`
- **Lane:** topologically admitted formation mechanics
- **Claim:** every decision-current deficit is exactly a weighted \(L^1\) approximation error to
  the source Hahn-sign label; observer deficits add intrinsically, and exact tensor formation
  constructs exponentially accurate continuous label approximants
- **Parents:** Hahn/Jordan decomposition, Bayes excess-risk identity, ULF-TAFM-2 through
  ULF-TAFM-5
- **Lean:** finite and arbitrary-measurable-space Hahn-label reconstruction, exact regret, observer
  deficit, and finite-channel conservation are certified in
  `HTGeometry.TopologicallyAdmittedHahnLabel` and
  `HTGeometry.TopologicallyAdmittedMeasurableHahnLabel`; the remaining clauses (HLA.5)--(HLA.20)
  are certified in `HTGeometry.TopologicallyAdmittedHahnLabelSpectrum`

## 1. New primitive

Resolution price was introduced as the least regularity cost of an effect carrying a prescribed
decision contrast. That definition still hides what the effects are approximating.

Every binary source experiment has one canonical measurable label: the sign of its signed measure
\(\mu_1-\mu_0\). The exact law is

\[
 \boxed{
 \operatorname{TV}(\mu_0,\mu_1)
 -\int e\,d(\mu_1-\mu_0)
 =\frac12\|2e-1-\sigma_\mu\|_{L^1(|\mu_1-\mu_0|)}.}
 \tag{HLA.1}
\]

Thus formation does not merely conserve an abstract current. It approximates the source's canonical
Hahn label. Every admitted effect doctrine becomes an approximation dictionary, and every no-go
becomes a lower bound on that dictionary's width.

For mutually singular full-support laws, the label is \(\pm1\) on two dense measurable sets and is
essentially nowhere continuously realizable. Exact tensor formation nevertheless produces
continuous approximants whose weighted \(L^1\) error decays exponentially.

## 2. Source label

Let \((X,\mathcal B)\) be a measurable space and let \(\mu_0,\mu_1\) be probability measures. Put

\[
 \lambda=\mu_0+\mu_1,
 \qquad
 \nu=\mu_1-\mu_0.
 \tag{HLA.2}
\]

Then \(\nu\ll\lambda\). Let

\[
 h=\frac{d\nu}{d\lambda}.
\]

Since \(-\lambda\le\nu\le\lambda\), one has \(|h|\le1\) \(\lambda\)-almost everywhere. Define a
measurable sign representative

\[
 \sigma_\mu(x)=
 \begin{cases}
  1,&h(x)\ge0,\\
 -1,&h(x)<0.
 \end{cases}
 \tag{HLA.3}
\]

and the positive measure

\[
 \omega_\mu=|h|\lambda=|\nu|.
 \tag{HLA.4}
\]

The value of \(\sigma_\mu\) on \(\{h=0\}\) is irrelevant because that set has zero
\(\omega_\mu\)-mass.

We use the probability-theory normalization

\[
 \operatorname{TV}(\mu_0,\mu_1)
 =\sup_A(\mu_1(A)-\mu_0(A))
 =\frac12|\nu|(X).
 \tag{HLA.5}
\]

The first supremum equals the usual absolute total variation because \(\nu(X)=0\).

## 3. Exact label-regret identity

### Theorem 3.1 -- decision deficit equals Hahn-label error

For every measurable effect \(e:X\to[0,1]\), put \(g=2e-1:X\to[-1,1]\). Then

\[
 \boxed{
 \operatorname{TV}(\mu_0,\mu_1)
 -\int_X e\,d\nu
 =\frac12\int_X|g-\sigma_\mu|\,d\omega_\mu.}
 \tag{HLA.6}
\]

#### Proof

Because \(\nu(X)=0\),

\[
 \int e\,d\nu
 =\int\frac{g+1}{2}h\,d\lambda
 =\frac12\int gh\,d\lambda.
\]

Equation `(HLA.5)` gives

\[
 \operatorname{TV}(\mu_0,\mu_1)
 =\frac12\int|h|\,d\lambda.
\]

On \(\{h\ne0\}\), write \(h=|h|\sigma_\mu\). Since \(-1\le g\le1\) and
\(\sigma_\mu\in\{-1,1\}\),

\[
 1-g\sigma_\mu=|g-\sigma_\mu|.
\]

Therefore

\[
 \begin{aligned}
 \operatorname{TV}-\int e\,d\nu
 &=\frac12\int(|h|-gh)\,d\lambda\\
 &=\frac12\int|g-\sigma_\mu|\,|h|\,d\lambda,
 \end{aligned}
\]

which is `(HLA.6)`. QED.

### Corollary 3.2 -- singular source form

If \(\mu_0\perp\mu_1\), then

\[
 |h|=1\quad\lambda\text{-almost everywhere},
 \qquad
 \omega_\mu=\lambda,
 \qquad
 \operatorname{TV}(\mu_0,\mu_1)=1.
\]

Hence

\[
 \boxed{
 1-\int e\,d(\mu_1-\mu_0)
 =\frac12\|2e-1-\sigma_\mu\|_{L^1(\mu_0+\mu_1)}.}
 \tag{HLA.7}
\]

#### Proof

Choose a singular separator. On its two conull sides, the density of \(\nu\) relative to
\(\mu_0+\mu_1\) is respectively \(1\) and \(-1\). Apply Theorem 3.1. QED.

## 4. Exact dictionary width

Let \(\mathcal E\) be any nonempty family of measurable \([0,1]\)-valued effects and put

\[
 2\mathcal E-1=\{2e-1:e\in\mathcal E\}.
\]

Define its Hahn-label width

\[
 \mathfrak w_\mu(\mathcal E)
 =\inf_{e\in\mathcal E}
   \|2e-1-\sigma_\mu\|_{L^1(\omega_\mu)}.
 \tag{HLA.8}
\]

### Theorem 4.1 -- exact decision capacity of a dictionary

\[
 \boxed{
 \sup_{e\in\mathcal E}\int e\,d(\mu_1-\mu_0)
 =\operatorname{TV}(\mu_0,\mu_1)
  -\frac12\mathfrak w_\mu(\mathcal E).}
 \tag{HLA.9}
\]

#### Proof

Take the supremum of the left side of `(HLA.6)`, equivalently the infimum of its nonnegative
right-side error. QED.

This is a complete classification, not a one-sided estimate. A route doctrine can carry target
contrast \(r\) exactly only if its effect dictionary comes within
\(2(\operatorname{TV}-r)\) of the source label.

### Corollary 4.2 -- compact continuous dictionaries have positive width

Assume \(X\) is compact Hausdorff and both mutually singular measures have full support. If
\(\mathcal E\subseteq C(X,[0,1])\) is compact in the uniform norm, then

\[
 \boxed{\mathfrak w_\mu(\mathcal E)>0.}
 \tag{HLA.10}
\]

#### Proof

If the width were zero, compactness would give \(e_n\to e\in\mathcal E\) uniformly with
\(2e_n-1\to\sigma_\mu\) in \(L^1(\mu_0+\mu_1)\). Hence \(2e-1=\sigma_\mu\) almost everywhere.
Thus \(e=1\) \(\mu_1\)-almost everywhere and \(e=0\) \(\mu_0\)-almost everywhere. Continuity and
full support force both \(e\equiv1\) and \(e\equiv0\), impossible. QED.

The compact-effect gap of ULF-TAFM-2 is exactly half a Hahn-label width.

## 5. Resolution spectrum is an inverse approximation spectrum

Let \(E\) be a vector space of bounded measurable functions containing constants, and let
\(q:E\to[0,+\infty)\) be a seminorm that kills constants. Define

\[
 \mathcal R^q_\mu(r)
 =\inf\left\{q(e):
 e\in E,\ 0\le e\le1,\ \int e\,d\nu\ge r\right\}
 \tag{HLA.11}
\]

and the Hahn approximation spectrum

\[
 \mathcal Q^q_\mu(\varepsilon)
 =\inf\left\{q(g):
 g\in E,\ -1\le g\le1,\
 \|g-\sigma_\mu\|_{L^1(\omega_\mu)}\le\varepsilon\right\}.
 \tag{HLA.12}
\]

### Theorem 5.1 -- exact spectrum duality

For \(0\le r\le\operatorname{TV}(\mu_0,\mu_1)\),

\[
 \boxed{
 \mathcal R^q_\mu(r)
 =\frac12\mathcal Q^q_\mu
   \left(2(\operatorname{TV}(\mu_0,\mu_1)-r)\right).}
 \tag{HLA.13}
\]

#### Proof

The affine map \(e\mapsto g=2e-1\) is a bijection from \([0,1]\)-valued members of \(E\) to
\([-1,1]\)-valued members. Since constants lie in the null space and \(q\) is homogeneous,

\[
 q(g)=q(2e-1)=2q(e).
\]

By `(HLA.6)`, the constraint \(\int e\,d\nu\ge r\) is exactly

\[
 \|g-\sigma_\mu\|_{L^1(\omega_\mu)}
 \le2(\operatorname{TV}-r).
\]

Taking infima gives `(HLA.13)`. QED.

Resolution price is therefore not an unrelated new scalar. It is the inverse approximation
spectrum of the canonical source label in the chosen regularity dictionary.

## 6. Tensor formation produces exponential label approximation

Assume now that \(\mu_0\perp\mu_1\). Let \(p_0,p_1\) be probability masses on a finite set \(Y\),
and let \(K_d:X\rightsquigarrow Y^d\) be any exact depth-\(d\) formation. Choose a
Neyman--Pearson event \(B_d\) and put

\[
 e_d=K_d^*\mathbf1_{B_d},
 \qquad
 g_d=2e_d-1.
\]

### Theorem 6.1 -- exact formation-to-label convergence

\[
 \boxed{
 \|g_d-\sigma_\mu\|_{L^1(\mu_0+\mu_1)}
 =2\left(1-
 \operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})\right).}
 \tag{HLA.14}
\]

If

\[
 A=\sum_{y\in Y}\sqrt{p_0(y)p_1(y)},
\]

then

\[
 \boxed{
 \|g_d-\sigma_\mu\|_{L^1(\mu_0+\mu_1)}
 \le2A^d.}
 \tag{HLA.15}
\]

#### Proof

Exact pushforward and the maximizing event give

\[
 \int e_d\,d(\mu_1-\mu_0)
 =\operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d}).
\]

Equation `(HLA.14)` is `(HLA.7)`. Hellinger affinity tensorizes, and the elementary testing bound

\[
 \operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})\ge1-A^d
\]

gives `(HLA.15)`. QED.

This is stronger than non-equicontinuity. Every exact formation constructs a continuous or
analytic approximation to one source label whenever its pullback doctrine is continuous or
analytic, and target tensor depth prescribes the exact approximation accuracy.

### Corollary 6.2 -- dictionary depth law

If every \(g_d\) belongs to one dictionary \(\mathcal G\subseteq[-1,1]^X\) with label width

\[
 \varepsilon=\inf_{g\in\mathcal G}
 \|g-\sigma_\mu\|_{L^1(\mu_0+\mu_1)}>0,
\]

then

\[
 \boxed{A^d\ge\varepsilon/2.}
 \tag{HLA.16}
\]

Thus

\[
 d\le\frac{\log(\varepsilon/2)}{\log A}
\]

when \(0<A<1\). This recovers compact-effect properness and extends it to every source-predeclared
dictionary with positive Hahn-label width.

## 7. Observer deficit is exact approximation distance

Let \(\pi:X\to Q\) be a measurable observer with finite nonempty target. Define the observer
dictionary

\[
 \mathcal E_\pi
 =\{f\circ\pi:f:Q\to[0,1]\}.
\]

### Theorem 7.1 -- exact observer-label deficit

\[
 \boxed{
 \inf_{f:Q\to[-1,1]}
 \|f\circ\pi-\sigma_\mu\|_{L^1(\omega_\mu)}
 =2\left(
 \operatorname{TV}(\mu_0,\mu_1)
 -\operatorname{TV}(\pi_*\mu_0,\pi_*\mu_1)
 \right).}
 \tag{HLA.17}
\]

#### Proof

The effects in \(\mathcal E_\pi\) have source contrast equal to the corresponding contrast on
\(Q\). Their maximum is
\(\operatorname{TV}(\pi_*\mu_0,\pi_*\mu_1)\), attained by a finite Neyman--Pearson event. Apply
Theorem 4.1 to \(\mathcal E_\pi\). QED.

No section of \(\pi\) is chosen. This is the intrinsic replacement for a representative-dependent
visible/hidden split.

### Theorem 7.2 -- serial observer-deficit conservation

For finite observers \(X\xrightarrow{\pi}Q\xrightarrow{\rho}R\), define

\[
 D_\mu(\pi)
 =2\left(\operatorname{TV}(\mu_0,\mu_1)
 -\operatorname{TV}(\pi_*\mu_0,\pi_*\mu_1)\right).
 \tag{HLA.18}
\]

Then

\[
 \boxed{
 D_\mu(\rho\circ\pi)
 =D_\mu(\pi)+D_{\pi_*\mu}(\rho).}
 \tag{HLA.19}
\]

#### Proof

Both sides telescope to

\[
 2\left(\operatorname{TV}(\mu_0,\mu_1)
 -\operatorname{TV}((\rho\circ\pi)_*\mu_0,
                     (\rho\circ\pi)_*\mu_1)\right).
\]

QED.

Equation `(HLA.19)` is exact current conservation through observer descent: approximation error
created at successive quotients adds, while formation edge budgets multiply. It is coordinate-free
and section-free.

## 8. Functional-equation neutrality

Let \(\tau:X\to X\) be a measurable equivalence. Transport both source laws and every effect.
Then \(\lambda,\nu,|\nu|\), and the Hahn label transport functorially. Change of variables gives

\[
 \|g\circ\tau^{-1}-\sigma_{\tau_*\mu}\|_{L^1(|\tau_*\nu|)}
 =\|g-\sigma_\mu\|_{L^1(|\nu|)}.
 \tag{HLA.20}
\]

Hence dictionary widths, observer deficits, and formation-label convergence are information-neutral
under functional-equation relabelling. If \(\tau\) also preserves the chosen regularity gauge, the
entire approximation spectrum `(HLA.13)` is invariant.

## 9. Cross-route grammar

The source label is not claimed to be one literal function already visible in every route. It is a
mechanism that predicts what each route dictionary is approximating.

| route organ | Hahn-label approximation shadow |
|---|---|
| positive effects / Gram reporters | soft classifier \(g\in[-1,1]\) approximating \(\sigma_\mu\) |
| recurrence / finite observers | observer TV deficit is exact best label-approximation error |
| analytic and BV no-gos | route function class has positive or slowly decaying label width |
| prefix/product formation | cylinder dictionaries approximate the tail label with a source rate |
| functional equation | transports label and approximation spectrum isometrically |
| hypertranscendence | unbounded differential channel rank may be needed to drive label error to zero |
| Wold/cofinal equicontinuity | a compact inverse-depth dictionary has positive label width |

This reframes thousands of endpoint theorems as possible lower bounds on one source-label width in
different dictionaries. It does not assert those bounds without literal comparison maps.

## 10. Hostile audit

### 10.1 Rediscovery boundary

The pointwise identity underlying `(HLA.6)` is the binary Bayes excess-risk identity. Classification
theory commonly writes excess risk as weighted disagreement with the Bayes classifier. Related
primary sources include:

- Nguyen--Wainwright--Jordan, surrogate losses and \(f\)-divergences,
  <https://arxiv.org/abs/math/0510521>;
- Zhang--Liu--Tao, rates from surrogate risk to the Bayes classifier,
  <https://arxiv.org/abs/1802.03688>;
- Perez-Lebel et al., decision regret under approximate posteriors,
  <https://arxiv.org/abs/2503.18025>;
- Novikov, measurable Hahn decomposition and Radon--Nikodym selection,
  <https://arxiv.org/abs/math/0501215>.

Therefore `(HLA.6)` alone is `[REDISCOVERED]`. This card is labelled `[BRIDGE]`. The corpus delta is
the exact fusion with tensor formation, source regularity dictionaries, observer descent, and the
resolution spectrum.

### 10.2 Internal collision audit

`scripts/formal_tools.py research` found:

- `[CORPUS]` `totalVariation_toSignedMeasure_sub`, proving
  \(|\mu_1-\mu_0|=\mu_0+\mu_1\) for mutually singular finite measures;
- `[CORPUS]` singularity approximation by complementary open sets;
- `[CORPUS]` Gaussian packet Bayes-risk formulas;
- `[CORPUS]` compact formation-depth gauges and numerous route-specific \(L^1\) estimates.

It did not find the Hahn-label regret identity, the exact spectrum duality `(HLA.13)`, formation
convergence `(HLA.14)`, or section-free observer deficit law `(HLA.17)` in the Lean corpus or the
pipeline.

### 10.3 Correctness attacks

1. **Does the label depend on a Hahn representative?** Only on a \(|\nu|\)-null set, so every
   displayed \(L^1\) quantity is canonical.
2. **Does total-variation normalization hide a factor two?** No. `(HLA.5)` fixes the convention;
   every later factor follows from \(|\nu|(X)=2\operatorname{TV}\).
3. **Does the general identity require singularity?** No. The weight \(|h|\lambda\) handles overlap.
   Singularity is used only to replace it by \(\mu_0+\mu_1\) and set source TV to one.
4. **Does formation merely bound the label error?** Equation `(HLA.14)` is exact; only the Hellinger
   passage to `(HLA.15)` is an inequality.
5. **Is observer additivity a chosen decomposition?** No. It is intrinsic telescoping of exact TV
   deficits and requires no section.
6. **Does this prove route dictionaries approximate the literal arithmetic label?** Not without
   comparison maps. The table is a research prediction, not a proved identification.
7. **Is this already RH?** No. No Xi occurrence or source dictionary-width lower bound is supplied.

### 10.4 Significance verdict

The parent identity is known. The formation consequence is mathematically substantive: arbitrary
tensor depth is equivalent to exponentially accurate approximation of one canonical measurable
label, and every observer loss is exactly its approximation deficit. This produces a testable common
law rather than another endpoint equivalence.

## 11. Corrected RH producer

A noncircular source architecture can now be stated without arbitrary target metrics:

1. construct a literal, zero-independent arithmetic binary source experiment;
2. identify its canonical Hahn label \(\sigma_\mu\);
3. prove every legal arithmetic formation effect belongs to a source-predeclared dictionary
   \(\mathcal G\);
4. prove an unconditional positive lower bound, or a slower-than-required decay law, for the
   Hahn-label width of \(\mathcal G\);
5. show an off-centre completed error would create tensor effects with label error at most \(2A^d\);
6. contradict the width law.

The exact open core is:

`[OPEN CORE]` Construct the literal arithmetic formation effects and prove a source-native
Hahn-label approximation-width theorem for their full dictionary before any Xi divisor is
specialized.

Unlike bare compactness, Feller admission, or a target metric, the label and weighted \(L^1\) error
are canonically generated by the source experiment itself.

## Gates

- [x] 0 -> 1: exact source-native object and route-independent falsifiable laws
- [x] 1 -> 2: dependency-closed proofs of `(HLA.6)`--`(HLA.20)`
- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedHahnLabelSpectrum`, `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedHahnLabel`, `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedMeasurableHahnLabel`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only
- [ ] 3 -> 4: independent priority and significance audit


## Lean certificate

Module `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedHahnLabelSpectrum` (63 constants, axiom-audit clean), together with the corpus modules `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedHahnLabel` (finite core) and `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedMeasurableHahnLabel` (measurable RN core). Laws are arbitrary probability measures `P = μ₀`, `Q = μ₁` on a measurable space; `λ = currentControl P Q = P + Q`.

| Claim | Lean declaration |
|-|-|
| (HLA.2)–(HLA.3) `λ`, `ν`, `h = dν/dλ`, the measurable Hahn sign `σ` | `currentControl`, `measurableSignedCurrent`, `measurableHahnDensity`, `measurableHahnLabel`, `currentControl_withDensity_measurableHahnDensity` |
| `∣h∣ ≤ 1` a.e.; `h = dμ₁/dλ - dμ₀/dλ`; `∫ g h dλ = ∫ g dμ₁ - ∫ g dμ₀` | `ae_abs_measurableHahnDensity_le_one`, `measurableHahnDensity_ae_eq`, `integral_mul_measurableHahnDensity` |
| (HLA.4) `ω = ∣h∣λ = ∣ν∣` | `variation_measurableSignedCurrent_eq` |
| (HLA.5) `TV = sup_A (μ₁A - μ₀A) = ½∣ν∣(X)`, attained at `{h ≥ 0}` | `isGreatest_measurableHahnTV`, `hahnEffectCurrent_hahnPositiveSet`, `measurableHahnTV_eq_half_variation` |
| Thm 3.1 (HLA.6) `TV - ∫ e dν = ½ ∫ ∣2e - 1 - σ∣ dω` | `measurableHahnTV_sub_effectCurrent`, `measurableHahnTV_sub_half_current`, `measurableHahnTV_sub_decisionCurrent_eq_labelError`, `hahnLabelDistance` |
| Cor 3.2 (HLA.7) singular form: `∣h∣ = 1`, `ω = λ`, `TV = 1` | `ae_abs_measurableHahnDensity_eq_one`, `hahnLabelDistance_eq_of_singular`, `measurableHahnTV_eq_one_of_singular`, `one_sub_hahnEffectCurrent_of_singular` |
| Thm 4.1 (HLA.8)–(HLA.9) dictionary capacity `sup ∫ e dν = TV - ½ width` | `iSup_hahnEffectCurrent_eq` |
| Cor 4.2 (HLA.10) compact continuous dictionaries have positive width (full-support singular laws) | `hahnLabelWidth_pos`, `abs_hahnLabelDistance_sub_le`, `ae_measurableHahnLabel_eq_one`, `ae_measurableHahnLabel_eq_neg_one` |
| Thm 5.1 (HLA.11)–(HLA.13) `ℛ^q(r) = ½ 𝒬^q(2(TV - r))` | `resolutionPriceSet`, `approximationSpectrumSet`, `resolutionPrice`, `approximationSpectrum`, `resolutionPriceSet_eq`, `resolutionPrice_eq` |
| Thm 6.1 (HLA.14) exact formation + Neyman–Pearson event: label error `2(1 - TV(p₀^{⊗d}, p₁^{⊗d}))` | `formationEffect`, `integral_formationEffect`, `hahnLabelDistance_formation`, `hahnLabelDistance_formation_hahnPositiveSet` |
| Thm 6.1 (HLA.15) `≤ 2A^d`, `A = ∑ √(p₀p₁)` | `hahnLabelDistance_formation_le`, `one_sub_measurableHahnTV_le_hellingerAffinity`, `hellingerAffinity_pi_const` |
| Cor 6.2 (HLA.16) depth law `A^d ≥ ε/2`, `d ≤ log(ε/2)/log A` | `formation_depth_law`, `formation_depth_le` |
| Thm 7.1 (HLA.17) observer deficit is the best observer label error (measurable observers; finite targets) | `isLeast_observerLabelDistance`, `isLeast_finiteObserverLabelDistance`, `hahnLabelDistance_comp`, `measurableHahnTV_map_le` |
| Thm 7.2 (HLA.18)–(HLA.19) serial observer-deficit conservation | `hahnObserverDeficit`, `hahnObserverDeficit_comp`, `observerDeficit_serial` |
| §8 (HLA.20) functional-equation neutrality under measurable relabelling | `hahnLabelDistance_map_equiv` |

## Log

- 2026-08-31 -- identified the canonical Hahn label, proved exact decision-deficit/approximation
  conservation, resolution-spectrum duality, exponential tensor-formation convergence, and
  section-free serial observer deficit conservation.
- 2026-08-31 -- built signed-measure Radon--Nikodym/variation infrastructure and Lean-certified the
  exact measurable Hahn law; spectrum duality and tensor convergence remain paper-only.
- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
