# Controllability Gramian is the universal law field

- **ID:** ULF-SGOGM-FAIL-1
- **Stage:** 5 — failed/retired
- **Type:** FALSIFIED FIELD-CORE CLAIM
- **Claim:** Every RH obstruction is curvature or degeneracy of one source controllability Gramian.
- **Verdict:** `[REDISCOVERED] [TOO WEAK] [RETIRED AS FIELD CORE]`
- **Positive survivor:**
  `../../../2-fully-proven/universal-law-field/source-generated-orbit-gramian-mechanics/cyclic-heat-orbit-gramian-lyapunov-properness-and-corona-selection-law.md`
- **Successor programme:**
  `../../../1-in-progress/universal-law-field/source-generated-orbit-gramian-mechanics/field-programme.md`

## 1. Why the claim looked plausible

A controllability Gramian simultaneously carries:

- a positive formation kernel;
- an observability/controllability range;
- a Lyapunov conservation law;
- a minimum-energy inverse;
- singular values measuring weak directions;
- a compact-versus-exact-controllability boundary in infinite dimension.

Those shadows resemble positivity, packet formation, source generation, completion escape, and
properness across the corpus. It was tempting to call every route obstruction a Gramian defect.

## 2. Exact killing theorem/mechanism

The abstract mechanism is established linear systems theory. Given any stable semigroup and input
operator, its Gramian, Lyapunov equation, reachability space, and inverse minimum-energy form are
standard. Conversely, arbitrary positive operators can be represented as Gramians after supplying
suitable dynamics and inputs. The representation therefore has the same vacuity as an arbitrary
response packet: it can encode a chosen geometry after the fact.

More decisively, a Gramian alone contains none of the following:

1. the arithmetic source selecting the semigroup;
2. the legal defect-formation operations;
3. a functional-equation or source involution;
4. hypertranscendental prolongation;
5. a reason an RH-bearing defect has finite control capital;
6. a comparison between distinct route organs.

The same positive compact Gramian supports many inequivalent source presentations and many
unrelated defects. Calling its weak directions “curvature” or “holonomy” changes no theorem.

## 3. Countermodels

### 3.1 Complete observation without a source law

Choose any compact injective positive operator `G` on `l^2`. It defines a proper inverse form, but
there is no distinguished arithmetic label, seed, or intervention. Replacing its eigenvalues
`gamma_n` by any other positive null sequence preserves algebraic completeness while changing every
cost. Thus completeness does not generate a canonical properness law.

### 3.2 Same Gramian, arbitrary interpretation

Unitary conjugation preserves all spectral Gramian data while changing coordinate labels. More
generally, different factorizations `G=WW*` have different control spaces and source histories.
Without marked source data, “formation capital” is not intrinsic.

### 3.3 A finite Gramian cannot explain the corona

In finite dimension an invertible Gramian has bounded inverse and scalar invariant densities
survive. The source-complete extinction theorem depends on infinite normal/corona separation, not
on a finite positive matrix.

### 3.4 Recurrence is independent

A positive heat Gramian does not specify a unitary phase action. One may attach no flow, a periodic
flow, or an irrational recurrent flow without changing the static positive operator. Recurrence is
obtained only when a marked generator `L` is retained.

## 4. Strongest positive survivor

The failure identifies the missing datum: not a Gramian, but a **source-generated orbit
factorization**.

For a positive compact-resolvent label `L` and full-support seed `v`, the orbit law

\[
 G=\int_0^\infty|e^{-tL}v\rangle\langle e^{-tL}v|dt
 \tag{F.1}
\]

has three properties unavailable to a bare positive operator:

1. the source fixes `G` through the weak Lyapunov equation
   `LG+GL=|v><v|`;
2. the same pair `(L,|v><v|)` has scalar common commutant;
3. finite inverse-Gramian defect cost is equivalent to a Hilbert--Schmidt factorization `X=WB`
   through the same orbit, and equals the least possible `||B||_HS^2`.

Combined with trace-class/corona transience, bounded formation capital forces trace-norm extinction.
The literal Euler shell realizes positive GNS, real generation, imaginary recurrence, HT jets, and
properness with the same marked pair.

## 5. New insight

The useful invariant is not “the Gramian.” It is the typed financing relation

\[
 \boxed{
 \mathcal E_G(XX^*)
 =\min_{X=WB}\|B\|_{\rm HS}^2.}
 \tag{F.2}
\]

It distinguishes source-born defects from arbitrary operators on the receiver. An RH route must
now construct this factorization or expose exactly why its defect lies outside the source formation
range.

## 6. Survivor status

- **Internal audit:** does not collide with the existing source-complete theorem; it removes that
  theorem's independent proper-cost choice.
- **External audit:** Gramian/Lyapunov/control-energy ingredients are established control theory.
- **Paper status:** dependency-closed Stage-2 theorem linked above.
- **Lean status:** pending; no Lean was written or built in this research pass.
- **Scientific status:** `[BRIDGE]`, not a new field theorem by itself.

## 7. Relentless-interrogation chain

1. **Gramian as field** failed because the receiver can be supplied arbitrarily.
2. **Source orbit generates Gramian** survives that failure because `(L,v)` fixes it by `(F.1)`.
3. **Source orbit generates proper cost** is paper-proved by inverse Gramian.
4. **Source-born defects have finite cost** survives only when the typed factorization `(F.2)` is
   constructed.
5. The live conjecture is therefore source-formation factorization, not another Gramian geometry.

No further positive field-core claim is retained from the bare-Gramian representation.

## Log

- 2026-08-13 — field-core claim attacked against control theory and corpus receiver-vacuity no-gos.
- 2026-08-13 — retired; source-generated factorization and endogenous-cost selection extracted as
  positive survivor.
