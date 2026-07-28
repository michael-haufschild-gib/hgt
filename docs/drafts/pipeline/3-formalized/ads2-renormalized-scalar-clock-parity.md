# Even black-hole resonances retain an irreducible clock memory

- **ID:** `ads2-renormalized-scalar-clock-parity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / ADS2 RESPONSE / RENORMALIZATION / HYPERTRANSCENDENCE
- **Statement:** Exact neutral-scalar AdS₂ clock response obeys a three-branch species law:
  positive odd resonances are DA, positive even resonances are HT after every finite local
  subtraction, and every noninteger gap is HT.
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/AdS2RenormalizedScalarClockParity.lean`

## Result

Write the positive integer throat gap as \(g=2\nu\). The exact finite-temperature neutral-scalar
AdS₂ response contains

\[
  \frac{\Gamma(-g)}{\Gamma(g)}
  \frac{\Gamma\!\left(z+\frac{1+g}{2}\right)}
       {\Gamma\!\left(z+\frac{1-g}{2}\right)}
  \frac{\Gamma\!\left(\frac{1+g}{2}\right)}
       {\Gamma\!\left(\frac{1-g}{2}\right)} .
\]

The static denominator argument \((1-g)/2\) is a Gamma pole exactly on the positive odd branch
\(g=2n+1\), where it cancels the pole of \(\Gamma(-g)\). On the positive even branch \(g=2n\),
that cancellation is absent. The remaining simple pole multiplies a polynomial in frequency and
is local. Its renormalized finite part contains a nonzero polynomial multiple of

\[
  \Psi_n(z)=
  \psi\!\left(z+\frac12-n\right)+
  \psi\!\left(z+\frac12+n\right).
\]

The terms are separated by the integer shift \(2n\), have charges \(1,1\), and hence total orbit
charge \(2\neq0\). Therefore \(\Psi_n\) is hypertranscendental. If \(a\neq0\) and both \(a\) and a
local counterterm \(p\) are differentially algebraic, then

\[
  a\Psi_n+p\ \text{is HT}\quad\Longleftrightarrow\quad\Psi_n\ \text{is HT}.
\]

Lean now proves the stronger whole-response statement. The exact normalization has a nonzero
residue \(r_n\), a single frequency-independent regular coefficient \(c_n\), and finite part

\[
  r_n\,P_{2n}(z)\frac{\Psi_n(z)}2+c_nP_{2n}(z).
\]

The polynomial response \(P_{2n}\) is DA and nonzero. Hence this entire meromorphic finite part,
not merely its displayed carrier, is HT for every value of \(c_n\). Local holographic scheme
changes cannot erase the even-resonance clock.

## Unconditionally checked in Lean

- \((1-(2n+1))/2=-n\);
- \((1-2n)/2\) is not a nonpositive integer;
- the static Gamma denominator vanishes at every odd gap and is nonzero at every even gap;
- away from frequency poles, the exact gap derivative of the Gamma quotient is the quotient times
  one half of the sum of its endpoint digammas;
- at \(g=2n\), that derivative exposes exactly \(\Psi_n/2\);
- the exact neutral-scalar AdS₂ Gamma normalization has the declared simple-pole residue at every
  positive even gap, and that residue is nonzero;
- its pole-removed analytic extension is differentiable through every positive even resonance,
  so a regular Laurent coefficient exists;
- for any simple-pole normalization, the renormalized finite part of its product with a
  differentiable response is exactly residue times response derivative plus regular part times
  response value;
- \(\Psi_n\) is hypertranscendental for every \(n\);
- the integer-gap Gamma response is DA and nonzero;
- the complete even-gap finite-part meromorphic response is HT for the exact physical residue and
  every regular complex subtraction constant;
- nonzero DA multiplication plus arbitrary DA addition preserves HT exactly.

No physical identification is introduced as an axiom. Faulkner--Liu--McGreevy--Vegh equation
(D27) and the holographic interpretation supply the external physics map; Lean proves the
normalization's Laurent behavior and resulting frequency law as unconditional complex analysis.

## Scientific survivor

The earlier normalized quotient has a DA/HT boundary at all integer/noninteger gaps. That is not
the physical renormalized boundary. Restoring its exact Gamma normalization produces a sharper
law:

\[
\boxed{
\begin{array}{c|c}
g>0 & \text{renormalized neutral-scalar throat response}\\ \hline
g\in 2\mathbb N+1 & \text{DA polynomial}\\
g\in 2\mathbb N   & \text{HT digamma finite part}\\
g\notin\mathbb Z  & \text{HT Gamma quotient}
\end{array}}
\]

All three branches are now dependency-closed in Lean. The positive odd cancellation has an exact
finite nonzero limit and a DA nonzero meromorphic response; the positive even branch includes
Laurent extraction and HT of the whole renormalized response; the noninteger exact-normalization
branch is HT. `ads2GravitationalClockSpeciesLaw` packages them as one theorem.

## Primary sources

- T. Faulkner, H. Liu, J. McGreevy, and D. Vegh,
  *Emergent quantum criticality, Fermi surfaces, and AdS2*,
  <https://arxiv.org/abs/0907.2694>, especially equation (D27).
- K. Skenderis, *Lecture Notes on Holographic Renormalization*,
  <https://arxiv.org/abs/hep-th/0209067>, especially the massive-scalar logarithmic branch.

## Next proof obligations

1. Prove clock-compass extraction of the renormalized throat response from finite operational
   reporters.
2. Prove a source-to-asymptotic observable theorem without assuming unknown outer matching
   coefficients are DA.
3. Test whether the parity law extends mode-by-mode beyond the scalaron to general
   near-\(\mathrm{AdS}_2\) gravitational effective field theories.

## Log

- 2026-07-28 — physical prefactor audit falsified the all-integer simplification claim; extracted
  odd/even resonance parity as strongest positive survivor.
- 2026-07-28 — static Gamma parity selector, even-resonance digamma HT theorem, and local
  renormalization invariance checked directly in Lean.
- 2026-07-28 — exact gap-derivative identity and its even-gap specialization checked in Lean,
  closing the mathematical identification of the digamma carrier before Laurent extraction.
- 2026-07-28 — simple-pole product finite-part law checked in Lean: renormalized finite part equals
  residue times response derivative plus regular normalization times response value.
- 2026-07-28 — exact even-gap normalization residue limit and its nonvanishing checked in Lean.
- 2026-07-28 — constructed the analytic pole-removed normalization, proved existence of its
  regular Laurent coefficient, and derived the exact finite-part response law.
- 2026-07-28 — upgraded carrier HT to whole-response HT in the genuine meromorphic differential
  field for the exact physical residue and every regular subtraction constant.
- 2026-07-28 — proved exact positive-odd pole cancellation, nonvanishing, and DA response; proved
  exact-normalization noninteger HT; packaged all branches as
  `ads2GravitationalClockSpeciesLaw`.
