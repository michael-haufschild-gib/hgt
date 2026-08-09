# Periodic law producer, phase quotient, recurrence, and open-prefix law

- **ID:** ULF-NFD-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Source:** finite calibration of `nomogenic-fixed-point-dynamics-field-charter.md`
- **Statement:** One periodic word producer and one quotient force recurrent observation, nonclosed
  lifted state, nonzero carry, reconstruction failure, and unbounded finite-prefix history.
- **Status:** [LEAN-CERTIFIED] [DEPENDENCY-CLOSED] [FIXED-POINT CALIBRATION]
  [CLASSICAL FINITE MODEL] [NO PROJECT AXIOMS] [NOT RH]

## 1. Setup

Let

\[
 A=\mathbb Z/4,
 \qquad B=\mathbb Z/2,
 \qquad q:A\to B,
 \quad q(x)=x\pmod 2.
\tag{1}
\]

Define source and observer histories

\[
 a_n=n\pmod4,
 \qquad b_n=n\pmod2,
\tag{2}
\]

and the finite source prefix

\[
 W_N=(a_0,a_1,\ldots,a_{N-1})\in A^*.
\tag{3}
\]

This is the smallest concrete chart of the polynomial law producer

\[
P_A(X)=1+A\times X:
\tag{4}
\]

finite words are the well-founded syntax and the periodic infinite word is finite-state behaviour.
The theorem below only uses the explicit objects `(1)`--`(3)`; no categorical fixed-point theorem
is assumed.

## 2. Theorem

### Theorem 2.1 — one-producer recurrence/open-history package

The histories and prefixes above satisfy all of the following.

1. **Exact observer factorization:**

   \[
   q(a_n)=b_n
   \qquad(n\ge0).
   \tag{5}
   \]

2. **Closed observer recurrence:**

   \[
   b_{n+2}=b_n.
   \tag{6}
   \]

3. **Nonclosed lifted state and nonzero holonomy:** writing
   (i:B\to A), (i(x)=2x),

   \[
   a_{n+2}=a_n+i(1),
   \qquad i(1)=2\ne0.
   \tag{7}
   \]

   Hence (a_{n+2}\ne a_n), while

   \[
   a_{n+4}=a_n.
   \tag{8}
   \]

4. **No endpoint decoder:** there is no function (d:B\to A) such that

   \[
   d(b_n)=a_n
   \qquad\text{for every }n.
   \tag{9}
   \]

5. **Open finite-prefix history:**

   \[
   |W_N|=N,
   \tag{10}
   \]

   so for every bound (M) there is an (N) with (|W_N|>M), despite the period-two observer.

6. **Carry memory:** for the canonical digit section (s:B\to A), (s(0)=0,s(1)=1),

   \[
   s(1)+s(1)-s(1+1)=i(1)\ne0.
   \tag{11}
   \]

### Proof

Equation `(5)` is reduction of the same natural number modulo two after reduction modulo four.
Since (2=0) in (B),

\[
b_{n+2}=n+2=n=b_n.
\]

In (A), addition of two is the nonzero kernel element (i(1)), proving `(7)`. Addition of four
is zero, proving `(8)`. If a decoder in `(9)` existed, then `(6)` would give

\[
a_{n+2}=d(b_{n+2})=d(b_n)=a_n,
\]

contradicting `(7)` and (i(1)\ne0). Definition `(3)` gives `(10)`; choosing (N=M+1) proves
unboundedness. Finally (1+1-0=2=i(1)\) in (A), proving `(11)`. QED.

## 3. What is coupled by one producer

The theorem does not place recurrence, phase, carry, and history in independent slots.

- The same source symbol (a_n) produces the finite prefix and lifted periodic history.
- The same quotient (q) produces observer recurrence and reconstruction failure.
- The same kernel element (i(1)) is both binary carry and one-observer-period holonomy.
- Prefix growth is forced by well-founded approximation of the same periodic behaviour.

Thus one formula links four universal-law organs:

\[
\text{quotient recurrence}
\Longleftrightarrow
\text{lift increment}
\Longleftrightarrow
\text{carry memory}
\Longrightarrow
\text{decoder failure},
\tag{12}
\]

while prefix length supplies the open-history coordinate.

## 4. Exact scope and hostile boundary

1. The model is finite and classical. It does not establish NFD as the universal field.
2. Prefix growth is construction depth, not a metric complexity theorem.
3. The quotient is group-theoretic, not a positive/GNS realization.
4. Periodic finite-state behaviour is not hypertranscendence.
5. No source-normal arithmetic producer, physical clock, Stokes landing, or RH criterion is present.
6. Replacing (q) by the identity kills decoder failure and open-lift separation. Nontrivial
   quotient marking is load-bearing.

## 5. Positive survivor

The theorem upgrades the vague slogan “closed observer, open history” to a single-producer test:
the observed period must lift to a nonzero kernel increment, and that same increment must obstruct
endpoint decoding. A recurrent quotient without a marked lift or kernel increment carries no such
law memory.

The next nonfinite gate is to replace the finite word producer by a literal differential or
arithmetic producer and prove that its rational/final fixed-point comparison controls at least one
HT, completion, or source-normal boundary theorem.

## 6. Lean certificate

Certified module:

`GaloisForLFunctions.HTGeometry.NomogenicFixedPointCalibration`.

Unconditional capstone:

`nomogenicPeriodicProducer_phaseQuotient_recurrence_openPrefix`.

The module imports the already certified split/nonsplit carry module and proves `(5)`--`(11)`,
including global decoder nonexistence and prefix unboundedness, with no theorem premises or added
axioms. Direct source check, target build, and universal-law umbrella build passed.

## Gates

- [x] 0 -> 1 in-progress: source and fixed quotient declared
- [x] 1 -> 2 fully-proven: complete finite proof above
- [x] 2 -> 3 formalized: exact capstone and supporting declarations certified
- [ ] 3 -> 4 publication-ready: not eligible

## Log

- 2026-08-09 — extracted as the smallest dependency-closed one-producer fixed-point calibration;
  paper proof closed.
- 2026-08-09 — quotient, recurrence, lift increment, nonperiodicity, decoder no-go, prefix length,
  unbounded depth, and carry packaged in one unconditional Lean theorem; promoted to Stage 3.
