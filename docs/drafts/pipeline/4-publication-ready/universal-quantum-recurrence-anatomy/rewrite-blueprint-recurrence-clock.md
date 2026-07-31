# Rewrite blueprint: localization geometry sets the recurrence clock

**Status:** replacement architecture; not yet manuscript text  
**Supersedes:** `rewrite-blueprint-localization.md` and the architecture of
`main-localization.tex`  
**Publication gate:** do not present this as publication-ready until the
named strictly local model theorem and every displayed claim below have
unconditional Lean proofs.

## Coherence verdict

The draft title

> A universal law separates quantum recurrence from spatial localization

is retired. “Separates” joins two subjects without making either cause the
other. The draft contains three distinct papers:

1. rational rank and exact relations in finite l-bit spectra;
2. delayed influence in an infinite quasi-local interacting field;
3. local spectral weight and first quantum return.

Only the third can support one coherent localization-and-recurrence paper.
The first two may be valid, but they do not belong in its theorem spine.

## One scientific question

> Does the spatial geometry of a localized quantum state determine how long
> that state takes to return?

Every main-text definition, theorem, figure, and example must answer this
question.

## One discovery

For a local state at \(x\), let
\[
  p_j(x)=\langle x,\Pi_jx\rangle,\qquad
  N_x(L)=\#\{j:-\log p_j(x)\le L\}.
\]
The function \(N_x\) counts spectral modes visible to the observer at
logarithmic depth \(L\). Define its integrated spectral depth
\[
  {\cal H}_x(L)=\frac12\int_0^L N_x(u)\,du.
\]

The target master law for the actual first post-exit return is
\[
  \boxed{
  \log\tau_x(\eta)\sim
  {\cal H}_x\!\left(\log\frac1\eta\right).}
  \tag{M}
\]
Here \(\eta\) is survival-amplitude infidelity. For pure-state trace
distance \(\varepsilon\),
\[
  \boxed{
  \log\tau_x^{\rm tr}(\varepsilon)\sim
  {\cal H}_x\!\left(2\log\frac1\varepsilon\right).}
  \tag{T}
\]

If
\[
  N_x(L)\sim C_xL^D,
\]
then
\[
  \boxed{
  \log\tau_x^{\rm tr}(\varepsilon)
  \sim
  \frac{2^DC_x}{D+1}
  \left(\log\frac1\varepsilon\right)^{D+1}.}
  \tag{D}
\]

If localized modes have centre count
\[
  M_x(R)\sim\kappa_xR^D
\]
and local weight profile
\[
  -\log p_j(x)=\frac{2}{\xi_x}d(x,c_j)+o(d(x,c_j)),
\]
then
\[
  C_x=\kappa_x\left(\frac{\xi_x}{2}\right)^D
\]
and therefore
\[
  \boxed{
  \log\tau_x^{\rm tr}(\varepsilon)
  \sim
  \frac{\kappa_x\xi_x^D}{D+1}
  \left(\log\frac1\varepsilon\right)^{D+1}.}
  \tag{L}
\]

Equation (L) is the intended localization-to-recurrence law: spatial
dimension becomes recurrence exponent \(D+1\), while localization length
sets the leading clock scale.

## What makes Anderson locality causal

Anderson localization belongs in this paper only through the implication
\[
  \text{localized eigenfunction geometry}
  \Longrightarrow N_x(L)
  \Longrightarrow {\cal H}_x(L)
  \Longrightarrow \tau_x.
\]

Removing the Anderson or local-model theorem must break the physical
application, not merely shorten the introduction. A theorem showing only
that transport and recurrence rank are logically independent fails this
test and is excluded.

The exact abstract recurrence theorem may assume a phase law whose
active-head density cost \(K_x(L)\), uniformly after positive integer power
maps, satisfies
\[
  \log K_x(L)=o({\cal H}_x(L)).
\]
The physical model theorem must derive both the local spectral-depth law
and this anti-concentration property. They may not be inserted as
unverified physical assumptions.

## Named-model gate

At least one strictly local, nontrivial infinite quantum model must satisfy
the full chain unconditionally:

1. a pure-point local spectral measure;
2. an exact asymptotic for \(N_x(L)\);
3. the required phase anti-concentration bound;
4. an almost-sure actual first post-exit return asymptotic;
5. the trace-distance form (L).

Preferred target: the strictly nearest-neighbour random Floquet model of
Vakulchyk and Flach, whose localization length is exactly tunable. For its
two-state one-dimensional geometry, the target specialization is
\[
  \log\tau_{x,\sigma}^{\rm tr}(\varepsilon)
  \sim
  2\xi(\theta)
  \left(\log\frac1\varepsilon\right)^2.
\]

This formula remains conjectural until the spectral-depth and annealed
anti-concentration steps are proved. It must not appear as a result in the
manuscript before then.

The Blaschke-dressed atomic ensemble is an exact witness and proof
laboratory. Because its localized basis is prescribed and its operator is
exponentially quasi-local rather than nearest-neighbour, it cannot by
itself support an Anderson-localization headline.

## Main-text architecture

### 1. The question

Explain why localization results control motion and memory but do not
currently give the asymptotic first-return clock of one local state.

### 2. Spectral depth

Define \(N_x\) and \({\cal H}_x\). Explain that ordinary Hilbert-space
dimension is the wrong return variable for an infinite localized system.

### 3. Actual-return law

Prove (M) for the exact probabilistic class, including exit before return.
Distinguish actual first return from worst-case simultaneous approximation
and from a static small-deviation probability.

### 4. Geometry-to-depth theorem

Prove that two-sided localization geometry and centre counting determine
\(N_x\), yielding (D) and (L).

### 5. Strictly local model

Derive every premise of Sections 3–4 in the named local random model. This
section is the physical theorem, not an analogy.

### 6. Consequences

State only consequences of (L): dimension recovery from recurrence
accuracy, tunability through localization length, and distinction between
ambient size and observer-visible spectral geometry.

## Ruthless disposition of current draft

| Current material | Disposition | Reason |
|---|---|---|
| Universal finite-spectrum rank-nullity budget | Cut | Does not determine first-return asymptotics or localization geometry. |
| Exact l-bit Walsh classification | Separate paper | Arithmetic classification, not part of recurrence clock chain. |
| Free/interacting rank endpoints | Separate paper | Addresses interaction-generated phase rank, not local first return. |
| Finite-range support ceiling | Separate paper | Valid l-bit geometry result but not premise of (M)–(L). |
| Interaction-layer wall crossing | Separate paper | Resolution hierarchy is a different operational question. |
| Uniform product-state visibility | Separate paper | Global l-bit probe, not local spectral measure at one site. |
| Infinite quasi-local maximal-rank field | Separate paper | Different representation and different theorem object. |
| Commutator delay and eventual saturation | Cut | Lieb–Robinson/causal-influence story; no role in return law. |
| Boundary dimension doubling | Cut | Conditional frequency-count story; no role in return law. |
| Finite Anderson full-rank/nontransport separation | Cut | Proves independence, not causal localization-to-clock law. |
| Deterministic localized recurrence deadline | Supplementary precursor | One-sided upper bound only; replaced in main text by exact asymptotic. |
| Countable pure-point tail truncation | Methods lemma | Needed only as infrastructure for infinite return theorem. |
| Anderson order-of-quantifiers discussion | Cut | Answers a separate locality question. |
| Spectral-depth actual-return theorem | Keep | Core universal mathematical law. |
| Geometry-to-spectral-depth transfer | Keep | Causal bridge from space to time. |
| Strictly local named-model transfer | Required | Makes result a physics paper rather than abstract recurrence geometry. |

## Title gate

Before the named-model gate is closed:

> Spectral depth determines first return in an infinite random quantum
> system

After a strictly local Anderson/Floquet theorem is proved:

> Localization geometry sets the quantum recurrence clock

Use “Anderson localization” in the title only if disorder-induced
localization in a standard local model supplies the premises of (L).
Do not use “universal law” in the title until the formal theorem covers the
claimed universality class without model-specific hidden premises.

## Public-language sentence

> How tightly a quantum particle is trapped determines how long its history
> takes to repeat.

This sentence is licensed only after the named-model gate. It refers to a
precise first-return theorem, not to recurrence rank, a worst-case upper
bound, or a metaphor about all quantum matter.

## Formal truth gate

No equation in this blueprint is manuscript-eligible until its exact
version is proved in Lean. In particular, current formal infrastructure for
finite weighted target bounds and the localized Blaschke kernel does not
yet prove:

- the infinite actual first-return asymptotic (M);
- the trace-distance transfer (T);
- the polynomial-depth corollary (D);
- the localization-profile transfer (L);
- either missing theorem for the strictly local named model.

Until those dependencies close, `main-localization.tex` remains a retired
research draft, not a submission candidate.
