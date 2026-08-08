# Route E physical-saddle antiscale coercivity barrier

- **ID:** `ROUTE-E-PHYSICAL-SADDLE-ANTISCALE-BARRIER-001`
- **Stage:** 2-fully-proven
- **Type:** `[PAPER-PROVED] [NO-GO] [POSITIVE SURVIVOR]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **RH used:** no
- **Computation used:** no
- **Lean status:** no Lean written while corpus refactor is active; exact finite Gibbs--Mellin
  factorization and Mellin \(L^2\) transport already exist unconditionally in
  `RHTower/GibbsCriticalDissipationAntiscaleResonance.lean` and
  `RHTower/L2MellinUnitary.lean`
- **Scientific status:** candidate project-new synthesis; external priority not claimed

## Result

Critical half-density supplies a large terminal frame only when its Euler saddle is allowed to
live at the product scale selected by that frame. Once the positive Euler square is centered on
physical product scale \(X\), optimally tuned antiscale resonance is separated from its
factorwise maximum by only \(X^{-o(1)}\). Thus no fixed-power Route E coercivity can follow from
an unconditioned Euler/Mellin norm comparison, even with exact Gamma completion and a moving prime
aperture.

More precisely, fix

\[
 \frac12\leq \sigma<1,\qquad a=1-\sigma,\qquad
 {\cal P}_Y=\{p:p\leq Y\},\qquad \ell=\log Y.
\tag{1}
\]

Put

\[
 {\cal G}_{\sigma,Y}=\prod_{p\leq Y}(1+p^{-\sigma})^2,\qquad
 {\cal M}_{\sigma,Y}(t)=\prod_{p\leq Y}(1-p^{-\sigma-it}).
\tag{2}
\]

The logarithmic center of the positive squared Euler law is

\[
 \Lambda_{\sigma,Y}
 :=2\sum_{p\leq Y}\frac{p^{-\sigma}}{1+p^{-\sigma}}\log p
 =\frac{2}{a}Y^a(1+o(1)).
\tag{3}
\]

At source-defined antiscale frequency

\[
 t_{\sigma,Y}=\frac{\pi}{\ell}+\frac{\pi}{a\ell^2},
\tag{4}
\]

one has exact asymptotic barrier

\[
 \boxed{
 \log\frac{{\cal G}_{\sigma,Y}}
 {|{\cal M}_{\sigma,Y}(t_{\sigma,Y})|^2}
 =\frac{\pi^2}{a^3}\frac{Y^a}{\ell^3}(1+o(1)).}
\tag{5}
\]

Suppose Euler square is aligned with ordinary physical scale \(X\), meaning each of its two
independent subset coordinates is centered at \(X\), equivalently

\[
 \Lambda_{\sigma,Y}=2\log X\,(1+o(1)).
\tag{6}
\]

Then `(3)` and `(5)` give

\[
 \boxed{
 \frac{|{\cal M}_{\sigma,Y}(t_{\sigma,Y})|^2}
 {{\cal G}_{\sigma,Y}}
 =X^{-\,\pi^2/(a^2\ell^3)+o(\ell^{-3})}
 =X^{-o(1)}.}
\tag{7}
\]

Consequently, for every fixed \(c>0\), proposed saddle-aligned coercivity

\[
 |{\cal M}_{\sigma,Y}(t)|^2\leq {\cal G}_{\sigma,Y}X^{-c}
 \quad\text{for every real }t
\tag{8}
\]

is false for all sufficiently large \(X\). Equation `(7)` is an explicit falsifier, not a
failure to prove `(8)`.

At critical half-density \(\sigma=1/2\), physical centering is

\[
 2\sqrt Y=\log X\,(1+o(1)),
\tag{9}
\]

and sharp escape reads

\[
 \frac{|{\cal M}_{1/2,Y}(t_{1/2,Y})|^2}
 {{\cal G}_{1/2,Y}}
 =X^{-\,4\pi^2/(\log Y)^3+o((\log Y)^{-3})}.
\tag{10}
\]

Thus choosing \(Y\sim(\log X)^2/4\) correctly centers the critical Euler saddle but leaves only
subpower antiscale coercivity. Choosing a much larger \(Y\) strengthens the terminal frame only
by moving Euler mass to products exponentially larger than \(X\). Aperture size cannot solve
both requirements within unconditioned product law.

## 1. Positive Euler law and its physical center

Expand the square of positive Euler product:

\[
 {\cal G}_{\sigma,Y}
 =\sum_{T,U\subseteq{\cal P}_Y}(m_Tm_U)^{-\sigma},\qquad
 m_T=\prod_{p\in T}p.
\tag{11}
\]

After division by \({\cal G}_{\sigma,Y}\), two subset coordinates are independent and each
prime is present in either coordinate with probability

\[
 q_p=\frac{p^{-\sigma}}{1+p^{-\sigma}}.
\tag{12}
\]

Therefore mean logarithmic product is exactly

\[
 {\mathbb E}\log(m_Tm_U)=2\sum_{p\leq Y}q_p\log p
 =\Lambda_{\sigma,Y}.
\tag{13}
\]

Since \(\sigma\geq1/2\),

\[
 \sum_{p\leq Y}\frac{p^{-2\sigma}}{1+p^{-\sigma}}\log p
 =o(Y^a).
\tag{14}
\]

Partial summation against unconditional prime number theorem gives

\[
 \sum_{p\leq Y}p^{-\sigma}\log p
 =\frac{Y^a}{a}(1+o(1)).
\tag{15}
\]

Equations `(12)`--`(15)` prove `(3)`. This is not a heuristic saddle: `(13)` is exact
center of finite positive Euler probability law.

Its variance is also sharply smaller than square of its mean:

\[
 \operatorname{Var}\log(m_Tm_U)
 =2\sum_{p\leq Y}q_p(1-q_p)(\log p)^2
 =\frac{2}{a}Y^a\ell(1+o(1)).
\tag{16}
\]

Hence under `(6)` each coordinate has mean \(\log X(1+o(1))\), while pair-product standard
deviation is

\[
 \asymp\sqrt{\log X\,\log Y}=o(\log X).
\tag{17}
\]

Chebyshev's inequality now shows each coordinate is concentrated on a relative \(o(1)\)
logarithmic window around product \(X\); equivalently pair product is centered at \(X^2\). Thus
“physical centering” is literal, not merely a first-moment label.

## 2. Full-aperture antiscale frame

For \(t=t_{\sigma,Y}\), write every prime as

\[
 \log p=\ell-v,\qquad v\geq0.
\tag{18}
\]

Then

\[
 t\log p
 =\pi+\frac{\pi/a-\pi v}{\ell}
   +O\!\left(\frac{1+v}{\ell^2}\right).
\tag{19}
\]

Mass \(p^{-\sigma}\) together with prime density contributes

\[
 \frac{Y^a}{\ell}e^{-av}\,dv.
\tag{20}
\]

Uniform PNT partial summation on every fixed \(v\)-window, followed by an exponentially small
tail truncation, therefore gives

\[
 \begin{aligned}
 F_{\sigma,Y}(t_{\sigma,Y})
 &:=\sum_{p\leq Y}p^{-\sigma}|1+p^{it_{\sigma,Y}}|^2 \\
 &=\frac{Y^a}{\ell^3}
   \int_0^\infty e^{-av}(\pi/a-\pi v)^2\,dv\,(1+o(1)).
 \end{aligned}
\tag{21}
\]

Elementary moments

\[
 \int_0^\infty e^{-av}\,dv=\frac1a,\quad
 \int_0^\infty ve^{-av}\,dv=\frac1{a^2},\quad
 \int_0^\infty v^2e^{-av}\,dv=\frac2{a^3}
\tag{22}
\]

give

\[
 \boxed{F_{\sigma,Y}(t_{\sigma,Y})
 =\frac{\pi^2}{a^3}\frac{Y^a}{\ell^3}(1+o(1)).}
\tag{23}
\]

Correction \(\pi/(a\ell^2)\) in `(4)` is forced: it centers terminal log-distance \(v\) at
its exponential-law mean \(1/a\). Any correction \(c/\ell^2\) replaces constant in `(23)`
by

\[
 \int_0^\infty e^{-av}(c-\pi v)^2\,dv,
\tag{24}
\]

whose unique minimizer is \(c=\pi/a\). Thus `(4)` is optimal full-aperture first resonance,
not an arbitrary near-resonant choice.

## 3. Exact Euler deficit

For \(u=p^{-\sigma}\) and \(\theta=t\log p\),

\[
 |1-ue^{-i\theta}|^2
 =(1+u)^2-u|1+e^{i\theta}|^2.
\tag{25}
\]

Consequently

\[
 \log\frac{{\cal G}_{\sigma,Y}}{|{\cal M}_{\sigma,Y}(t)|^2}
 =\sum_{p\leq Y}-\log\!\left(
 1-\frac{p^{-\sigma}|1+p^{it}|^2}{(1+p^{-\sigma})^2}\right).
\tag{26}
\]

On terminal range \(v\leq C\log\ell\), `(19)` makes summands' arguments \(o(1)\), so
\(-\log(1-z)=z+O(z^2)\) uniformly there. Total quadratic error is

\[
 o\!\left(\frac{Y^a}{\ell^3}\right)
\tag{27}
\]

for every fixed \(\sigma\geq1/2\). Choose \(C>4/a\). For nonterminal primes, elementary bound

\[
 \log\frac{(1+p^{-\sigma})^2}{|1-p^{-\sigma-it}|^2}
 \ll_\sigma p^{-\sigma}
\tag{28}
\]

(with finitely many small primes absorbed in the constant), followed by PNT partial summation,
bounds omitted range by

\[
 O(Y^a\ell^{-aC})
 =o(Y^a/\ell^3).
\tag{29}
\]

Equations `(23)` and `(26)`--`(29)` prove `(5)`. Substitution of `(3)` and `(6)` proves `(7)`.

## 4. Conjecture loops and verdicts

### Loop A — larger aperture creates missing power

`[CONJECTURE]` Increase \(Y\) until terminal half-density mass yields a fixed power of \(X\).

`[FALSIFIED]` Larger \(Y\) also changes Euler saddle center from `(3)`. If center remains
\(\log X\), equation `(7)` forces exponent \(o(1)\). If \(Y\) is increased without retuning the
Mellin line, source mass leaves physical scale.

### Loop B — Gamma completion repairs frame

`[CONJECTURE]` Gamma decay removes antiscale resonant reporter.

`[FALSIFIED]` Frequency `(4)` tends to zero. Hence

\[
 |\Gamma(\sigma+it_{\sigma,Y})|^2
 =|\Gamma(\sigma)|^2(1+o(1)).
\tag{30}
\]

Gamma completion does not attenuate escape.

### Loop C — exact Mellin \(L^2\) transport makes estimate physical

`[CONJECTURE]` Mellin unitarity alone turns critical spectral coercivity into a physical-shell
bound.

`[FALSIFIED]` Mellin unitarity preserves norms but does not condition log-product. Equations
`(13)`--`(17)` show exactly which physical scale an unconditioned Euler norm occupies. Aligning
that scale produces subpower barrier `(7)`.

### Loop D — source conditioning is positive survivor

`[POSITIVE SURVIVOR]` A viable analytic continuation must act before unconditioned Euler fusion
and retain a joint physical-shell coordinate. It must prove cancellation after conditioning

\[
 \log(m_Tm_U)=2\log X+O(\sqrt{\log X\log Y})
\tag{31}
\]

or an equivalent ordinary-integer interval, while retaining parity and growing odd grades.
This is strictly stronger information than any scalar Euler norm: `(7)` gives an explicit
near-null vector after latter has forgotten `(31)`.

## 5. Exact Route E splice

This theorem closes unconditioned moving-Mellin branch as a fixed-power producer. It does not
close Route E and does not bound a Mertens sum.

Remaining source choices are now sharper:

1. prove collision-quotiented interval Hall and co-moving endpoint flux for existing explicit
   grade-recurrent reservoir cube, which retains ordinary integers and physical intervals from
   start; or
2. construct a genuinely shell-conditioned, nonproduct Mellin/Gibbs operator which retains
   `(31)` before parity scalarization and prove physical-power transverse response there.

Call second premise

`PHYSICAL-SHELL-CONDITIONED-GROWING-ODD-CUBE-TRANSVERSALITY`.

A diagonal Euler product, Gamma completion, moving prime cutoff, unconditioned Mellin projection,
or bounded scalar renormalization does not meet this premise. Exact odd-cube determinant law
in `route-e-gibbs-antiscale-determinant-mellin-odd-cube-law.md` supplies growing parity grades;
this card proves their shell coordinate may not be integrated out first.

## 6. Novelty and anti-theatre audit

- PNT partial summation, Bernoulli Euler measures, and quadratic phase expansion are classical.
- Candidate new content is their exact synthesis into saddle-aligned barrier `(5)`--`(10)` and
  resulting Route E source classification.
- No claim of external priority is made while literature work is paused by instruction.
- Theorem is genuine no-go, not an RH equivalent: it exhibits explicit resonance and computes
  its exact deficit.
- Positive survivor is not called a proof. Physical-shell-conditioned odd-cube transversality
  and physical Hall/co-moving flux remain unproved.
- No Lean file was changed or built.

## 7. Subsequent shell-conditioned closure

The first positive survivor above is no longer open in its Gaussian-shell form.  Paper theorem
**route-e-physical-shell-conditioned-parity-energy-regression-law.md** conditions literal Euler
subsets by a positive Gaussian at

\[
 \log m_T=\log X+O(\sqrt{\log X\log Y})
\]

before parity scalarization and proves

\[
 \frac{|Z_Y^{\rm sh}(t_Y^*)|^2-|M_Y^{\rm sh}(t_Y^*)|^2}
 {(P_Y^{\rm sh})^2}
 =-X^{-\pi^2/(a^2(\log Y)^3)+o((\log Y)^{-3})}.
\]

Its exact parity--energy Schur complement is invariant under Gaussian energy conditioning, and
Fourier inversion retains every odd grade.  Therefore
**PHYSICAL-SHELL-CONDITIONED-GROWING-ODD-CUBE-TRANSVERSALITY** is discharged for this positive
shell. Remaining analytic Route E core is source-faithful descent of conditioned determinant to
literal co-moving ordinary-integer kernel, normalized Gibbs denominator, and
friable/one-large-prime seam. Route E and RH remain open.
