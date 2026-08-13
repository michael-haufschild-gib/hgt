# Causal-delay radial-drift work cusp and information-undercapacity law

- **ID:** ULF-SGOGM-4
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / CAUSAL FORMATION LAW
- **Source programme:**
  `../../../1-in-progress/universal-law-field/source-generated-orbit-gramian-mechanics/field-programme.md`
- **Hardy admission parent:**
  `spectral-hardy-trace-formation-admission-and-radial-capital-wall-law.md`
- **Functional-equation recovery parent:**
  `split-recovery-formation-capital-monotonicity-functional-equation-neutrality-law.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE]`
  `[EXACT DELAY/DRIFT/WORK LAW] [FORMATION CUSP] [INFORMATION UNDERCAPACITY]`
  `[LEAN PENDING] [NOT RH]`

## 1. Purpose

The unsmoothed radial multiplier `exp(delta z)-1` has infinite Euler-shell formation capital for
every nonzero drift `delta`. That wall does not say off-neutral formation is impossible. A source
may delay and average the defect.

This card classifies that escape exactly. For a width-`T` average and delay `b`, the drift is
formable precisely when both ends of its translated control remain in causal time. Its least work
is independent of the delay once admitted and has a nonsmooth cusp at zero drift:

\[
 \boxed{
 \text{work}(\delta,T)
 ={2\min(|\delta|,T)\over T^2}.}
 \tag{CDW.1}
\]

Functional-equation pairing sends `delta` to `-delta`. A common causal realization requires delay
at least `|delta|`; its paired work is twice `(CDW.1)`. For the same Euler-shell Gibbs source, that
work is linear in `|delta|` near the neutral point, whereas reflected Jeffreys information is
quadratic. Information is therefore too soft to generate causal formation properness.

## 2. Delayed smoothed radial packet

Use an Euler-shell source pair `(L,v)` from `ULF-SGOGM-3`, so the reachability map `W` is injective
and least capital equals the squared `L^2(0,infinity)` norm of the unique source history.

Let

\[
 \delta,b\in\mathbb R,
 \qquad T>0.
 \tag{CDW.2}
\]

Define the multiplier

\[
 \Phi_{\delta,b,T}(z)
 =e^{-bz}(e^{\delta z}-1){1-e^{-Tz}\over Tz}
 ={e^{-(b-\delta)z}-e^{-bz}\over Tz}(1-e^{-Tz}).
 \tag{CDW.3}
\]

The removable value at `z=0` is understood. Whenever the multiplier packet belongs to the ambient
Euler-shell Hilbert space, put

\[
 x_{\delta,b,T}=\Phi_{\delta,b,T}(L)v.
 \tag{CDW.4}
\]

## 3. Main theorem

### Theorem 3.1 — causal delay classification

If `delta=0`, then `x_(delta,b,T)=0` and its capital is zero for every `b`. Assume `delta!=0`.
Then the following are equivalent:

1. `x_(delta,b,T)` has finite source-orbit formation capital;
2. `Phi_(delta,b,T)` belongs to `H^2(C_+)`;
3. both translated interval starts are causal:

\[
 b\ge0,
 \qquad b-\delta\ge0;
 \tag{CDW.5}
\]

4. equivalently,

\[
 \boxed{b\ge\max(0,\delta).}
 \tag{CDW.6}
\]

In the admitted chamber the unique source history is

\[
 h_{\delta,b,T}(t)
 ={1\over T}\left(
 \mathbf1_{[b-\delta,b-\delta+T]}(t)
 -\mathbf1_{[b,b+T]}(t)ight),
 \tag{CDW.7}
\]

and its exact least capital is

\[
 \boxed{
 q_G(x_{\delta,b,T})
 =\|h_{\delta,b,T}\|_2^2
 ={2\min(|\delta|,T)\over T^2}.}
 \tag{CDW.8}
\]

Thus delay decides admission, but not work after admission.

### Proof

When `(CDW.5)` holds, both indicators in `(CDW.7)` lie in `L^2(0,infinity)`, and direct Laplace
transformation gives

\[
 \mathcal L h_{\delta,b,T}=\Phi_{\delta,b,T}.
 \tag{CDW.9}
\]

The Hardy-trace formation theorem gives admission. The Euler-shell reachability map is injective,
so this history is unique and its squared norm is the least capital.

The intervals in `(CDW.7)` have length `T`; their displacement is `|delta|`; their overlap length
is `(T-|delta|)_+=max(T-|delta|,0)`. Therefore

\[
 \|h_{\delta,b,T}\|_2^2
 ={2T-2(T-|\delta|)_+\over T^2}
 ={2\min(|\delta|,T)\over T^2},
 \tag{CDW.10}
\]

proving `(CDW.8)`.

Conversely, suppose one start in `(CDW.5)` is negative. Since `delta!=0`, the two exponential
rates in `(CDW.3)` are distinct. Along the positive real ray, the term with negative start grows
exponentially and cannot cancel the other term. Hence

\[
 |\Phi_{\delta,b,T}(x)|\sqrt{x}\longrightarrow\infty
 \tag{CDW.11}
\]

along the Euler-shell spectral sequence `x=log n`. But every `H^2` function satisfies

\[
 |H(x)|\le {\|H\|_{H^2}\over\sqrt{2x}},
 \tag{CDW.12}
\]

contradicting `(CDW.11)`. The Hardy-trace theorem rules out finite capital. QED.

## 4. Functional-equation common-delay law

Reflection sends `delta` to `-delta`. A single delay `b` admits both orientations exactly when

\[
 b\ge\max(0,\delta)
 \quad\text{and}\quad
 b\ge\max(0,-\delta),
 \tag{CDW.13}
\]

that is,

\[
 \boxed{b\ge|\delta|.}
 \tag{CDW.14}
\]

At every common admitted delay, both orientations have the same work. On the direct-sum doubled
packet their exact total capital is

\[
 \boxed{
 \mathfrak C_{\rm pair}(\delta,T)
 ={4\min(|\delta|,T)\over T^2}.}
 \tag{CDW.15}
\]

The functional equation therefore does not select `delta=0`; it symmetrizes the causal financing
law and forces a common delay budget.

Common extra delay is a gauge inside the admitted chamber. For `c>=0`, let `S_c` denote the
right-shift isometry on `L^2(0,infinity)`, extended by zero before `c`. Then

\[
 h_{\delta,b+c,T}=S_ch_{\delta,b,T},
 \qquad
 \Phi_{\delta,b+c,T}(z)=e^{-cz}\Phi_{\delta,b,T}(z),
 \tag{CDW.15a}
\]

and

\[
 \boxed{
 \|h_{\delta,b+c,T}\|_2^2
 =\|h_{\delta,b,T}\|_2^2.}
 \tag{CDW.15b}
\]

Hence absolute delay after admission carries no work information. The invariant is the entrance
threshold `max(0,delta)` on one orientation and `|delta|` on the reflected pair.

## 5. Work cusp versus smooth information

Retain the same Euler-shell source. For real `u` near zero, define its Gibbs tilt

\[
 dP_u(n)={n^{-\sigma+u}\over S_m(\sigma-u)},
 \qquad n\in A_m,
 \tag{CDW.16}
\]

and put

\[
 F(u)=\log S_m(\sigma-u).
 \tag{CDW.17}
\]

Then

\[
 F'(u)=\mathbb E_{P_u}(\log n),
 \qquad
 F''(u)=\operatorname{Var}_{P_u}(\log n)>0.
 \tag{CDW.18}
\]

The reflected likelihood ratio is

\[
 \log{dP_u\over dP_{-u}}(n)
 =2u\log n+F(-u)-F(u),
 \tag{CDW.19}
\]

so its Jeffreys information is

\[
 J_m(u)
 =D(P_u\Vert P_{-u})+D(P_{-u}\Vert P_u)
 =2u\big(F'(u)-F'(-u)\big).
 \tag{CDW.20}
\]

Fix `u_0>0` with `sigma-u_0>1` and put

\[
 M_{u_0}=\sup_{|s|\le u_0}F''(s)<\infty.
 \tag{CDW.21}
\]

The mean-value theorem gives

\[
 0<J_m(u)\le4M_{u_0}u^2
 \qquad(0<|u|\le u_0).
 \tag{CDW.22}
\]

Using the same parameter `delta=u`, if `0<|u|<=T`, then

\[
 \mathfrak C_{\rm pair}(u,T)={4|u|\over T^2}.
 \tag{CDW.23}
\]

Consequently

\[
 \boxed{
 {\mathfrak C_{\rm pair}(u,T)\over J_m(u)}
 \ge {1\over M_{u_0}T^2|u|}
 \longrightarrow\infty
 \qquad(u\to0,\ u\ne0).}
 \tag{CDW.24}
\]

The two grades of the same source have different local geometry:

\[
 J_m(u)=O(u^2),
 \qquad
 \mathfrak C_{\rm pair}(u,T)=\Theta(|u|).
 \tag{CDW.25}
\]

No locally bounded multiple of smooth reflected information can dominate causal formation work near
the neutral point. KL/Jeffreys information remains valuable for distinguishability, but it cannot
serve as the missing properness capital.

## 6. Source-anchor selection theorem

Let `b_src(delta)` be a source-derived causal delay for the drift packet, defined before any zero
or target specialization. If the source law supplies

\[
 b_{\rm src}(\delta)=0
 \tag{CDW.26}
\]

and requires finite formation capital, then Theorem 3.1 forces

\[
 \delta\le0.
 \tag{CDW.27}
\]

If the same zero-delay law is functional-equation invariant, it also applies to `-delta`, hence

\[
 -\delta\le0.
 \tag{CDW.28}
\]

Therefore

\[
 \boxed{\delta=0.}
 \tag{CDW.29}
\]

This is an exact conditional selection theorem: **causal anchoring + finite capital + reflection
forces the neutral locus.** The condition is not yet an independent HGT source law. In the actual
Hedenmalm source formalization, source involution fixedness is already proved equivalent to
critical-line placement. Substituting that fixedness for `(CDW.26)` would therefore be circular.
The live problem is to derive a zero-slack causal formation from a parameter-free operation before
divisor specialization, not to rename source fixedness as an anchor.

## 7. Countermodels and load-bearing hypotheses

### 7.1 Delay destroys selection

For every nonzero `delta`, choosing

\[
 b\ge\max(0,\delta)
 \tag{CDW.30}
\]

produces finite capital. With both functional-equation orientations, `b>=|delta|` suffices.
Therefore finite capital plus reflection alone never selects zero.

### 7.2 Width is load-bearing

At `T=0`, the histories become signed point impulses and leave `L^2`; exact-time packets have
infinite capital. The finite law is a temporal averaging theorem.

### 7.3 Positivity is not used in the signed history

The control in `(CDW.7)` is a signed difference of positive windows. The resulting positive defect
`|x><x|` has nonnegative energy, but formation itself retains orientation. Erasing sign before
formation loses the cancellation that defines radial drift.

### 7.4 Source clock is constitutive

Changing the origin of source time changes the admissible delay chamber. The theorem does not call
zero delay canonical; it identifies that canonicity as the exact missing source datum.

### 7.5 Source origin does not imply radial zero slack

A source theory may have a canonical origin while a particular defect begins after a positive
latency. The corpus's Hedenmalm source-origin theorem and its fixed-flow classifier exhibit exactly
this distinction. Origin marks the causal boundary; it does not prove that the RH-bearing drift
history touches it.

## 8. Parent boundary and hostile verdict

The shifted-box Laplace transform and its `L^2` norm are elementary signal/control theory. Hardy
admission and diagonal-semigroup interpolation are established parents. This card is a `[BRIDGE]`.

Its corpus leverage is the joint law:

1. radial drift becomes a signed difference of source-time windows;
2. causality gives a sharp delay threshold;
3. least work has an exact nonsmooth cusp;
4. functional equation forces a common delay, not zero drift;
5. smooth information geometry provably underprices formation near the center;
6. a global zero-slack source formation would select the neutral locus, but source fixedness is an
   RH-equivalent substitute and is forbidden.

- [x] causal admission iff proved;
- [x] exact least-work formula proved;
- [x] functional-equation common-delay threshold proved;
- [x] information-undercapacity asymptotic proved;
- [x] zero-delay reflection selection theorem proved;
- [x] delay countermodel supplied;
- [ ] Lean formalization in later pass;
- [ ] parameter-free source proof of zero-slack radial formation;
- [ ] RH consequence.

No Lean was written or built during this research pass.
