# Route E moving Euler-tilt chi-square contiguity law

- **ID:** `ROUTE-E-MOVING-EULER-TILT-CHI-SQUARE-CONTIGUITY-001`
- **Stage:** 3-formalized
- **Type:** `[PAPER-PROVED] [LEAN-CERTIFIED] [SOURCE-TRANSFER]`
- **Parent:** `../../2-fully-proven/new_scientific_knowledge/route-e-source-faithful-euler-tilt-unit-shell-law.md`
- **Companion:** `route-e-entropy-complement-breadth-mixture-load-law.md`
- **RH used:** no
- **Computation used:** no
- **Lean status:** dependency-closed finite and asymptotic theorem formalized in
  `formal/GaloisForLFunctions/RHTower/RouteEMovingEulerTiltChiSquareContiguity.lean`
- **Scientific status:** new project-local bridge; external priority unclaimed

## 1. Result

For a finite prime aperture (p\le N), put

\[
 q_{p,\sigma}=\frac{p^{-\sigma}}{1+p^{-\sigma}},
 \qquad \nu_{\sigma,N}=\bigotimes_{p\le N}
       \operatorname{Bernoulli}(q_{p,\sigma}).                 \tag{1}
\]

The moving supercritical Euler source is chi-square contiguous to the critical source throughout
the full sub-prime-clock regime

\[
 \delta_N\ge0,
 \qquad \delta_N\log N\longrightarrow0.                       \tag{2}
\]

More precisely, at every finite aperture,

\[
 \boxed{
 \chi^2(\nu_{1+\delta,N}\Vert\nu_{1,N})
 \le \exp\!\left\{\mathcal E_N(\delta/2)\right\}-1,}          \tag{3}
\]

where the already formalized reflected prime-clock energy is

\[
 \mathcal E_N(a)=
 \sum_{p\le N}
 \left(p^{-(1/2+a)}-p^{-(1/2-a)}\right)^2.                    \tag{4}
\]

Consequently `(2)` implies

\[
 \boxed{
 \chi^2(\nu_{1+\delta_N,N}\Vert\nu_{1,N})\longrightarrow0.}  \tag{5}
\]

This applies to the source-faithful saddle tilt

\[
 \delta_N=\frac{2\log\log N}{(\log N)^2}
 +O\!\left(\frac1{(\log N)^2}
 +\frac{(\log\log N)^2}{(\log N)^3}\right),                  \tag{6}
\]

because (delta_N\log N\to0). This transfers fixed finite observables between the two bare
Bernoulli laws. It does **not** by itself transport an RH-strength normalized Gibbs ratio; the
hostile rate audit in Section 5 explains the distinction.

The transfer is exact for every finite observable (f):

\[
 \boxed{
 \left|\mathbb E_{1+\delta,N}f-\mathbb E_{1,N}f\right|^2
 \le
 \chi^2(\nu_{1+\delta,N}\Vert\nu_{1,N})
 \mathbb E_{1,N}|f|^2.}                                     \tag{7}
\]

No event approximation, independent-prime heuristic, or asymptotic replacement occurs in
`(3)` or `(7)`.

## 2. Exact finite chi-square product

For arbitrary finite Bernoulli parameters (q_i,r_i\in(0,1)), define likelihood

\[
 L(S)=\prod_{i\in S}\frac{q_i}{r_i}
       \prod_{i\notin S}\frac{1-q_i}{1-r_i}.                  \tag{8}
\]

Termwise multiplication gives (\nu_r(S)L(S)=\nu_q(S)). Hence

\[
 1+\chi^2(\nu_q\Vert\nu_r)
 =\mathbb E_r L^2
 =\prod_i\left(
 r_i\left(\frac{q_i}{r_i}\right)^2
 +(1-r_i)\left(\frac{1-q_i}{1-r_i}\right)^2\right).         \tag{9}
\]

The local factor simplifies exactly to

\[
 r\left(\frac qr\right)^2
 +(1-r)\left(\frac{1-q}{1-r}\right)^2
 =1+\frac{(q-r)^2}{r(1-r)}.                                  \tag{10}
\]

Therefore

\[
 \boxed{
 1+\chi^2(\nu_q\Vert\nu_r)
 =\prod_i\left(1+\frac{(q_i-r_i)^2}{r_i(1-r_i)}\right).}     \tag{11}
\]

## 3. Euler local defect and prime-clock domination

Set (a=p^{-\sigma}), (b=p^{-\tau}). Substitution into `(10)` gives the exact local identity

\[
 \frac{(q_{p,\sigma}-q_{p,\tau})^2}
      {q_{p,\tau}(1-q_{p,\tau})}
 =\frac{(a-b)^2}{b(1+a)^2}.                                  \tag{12}
\]

Take (	au=1), (sigma=1+\delta), and (\delta\ge0). Write

\[
 b=p^{-1},\qquad y=p^{-\delta},\qquad z=p^\delta\ge1.        \tag{13}
\]

Then `(12)` equals

\[
 \frac{b(y-1)^2}{(1+by)^2}
 \le b(y-1)^2
 \le bz(y-1)^2.                                              \tag{14}
\]

Since (zy=1), the last expression is exactly

\[
 bz(y-1)^2
 =\left(p^{-(1/2+\delta/2)}
        -p^{-(1/2-\delta/2)}\right)^2.                       \tag{15}
\]

Combining `(11)`, `(14)`--`(15)`, and

\[
 \prod_i(1+u_i)\le\exp\!\left(\sum_i u_i\right)
 \qquad (u_i\ge0)                                           \tag{16}
\]

proves `(3)`.

The formal prime-clock scaling theorem already proves

\[
 a_N\log N\to0
 \quad\Longrightarrow\quad
 \mathcal E_N(a_N)\to0.                                    \tag{17}
\]

Apply `(17)` to (a_N=\delta_N/2), then continuity of the exponential and the squeeze between
zero and `(3)` prove `(5)`.

## 4. Observable transfer

From the exact change of measure,

\[
 \mathbb E_qf-\mathbb E_rf=\mathbb E_r[(L-1)f].              \tag{18}
\]

Cauchy--Schwarz gives

\[
 |\mathbb E_r[(L-1)f]|^2
 \le \mathbb E_r(L-1)^2\,\mathbb E_rf^2,                    \tag{19}
\]

which is `(7)`. In particular, bounded critical second moments make the forced moving tilt and
critical source asymptotically interchangeable for the same finite observable.

## 5. Normalized-ratio hostile audit and exact physical-gauge correction

The absolute theorem `(5)` is not the scale needed by the endpoint. Let

\[
 B_N=\mathbb E_{1,N}w_N,
 \qquad A_N=\mathbb E_{1,N}f_N,
\]

with (0\le w_N\le1), (|f_N|\le w_N), and (B_N>0). Exact likelihood
Cauchy--Schwarz gives the relative statement

\[
 \chi_N^2\le\eta_N^2B_N,quad 0\le\eta_N<1
 \quad\Longrightarrow\quad
 \left|\frac{\mathbb E_{1+\delta_N,N}f_N}
                 {\mathbb E_{1+\delta_N,N}w_N}
       -\frac{A_N}{B_N}\right|
 \le\frac{2\eta_N}{1-\eta_N}.                             \tag{20}
\]

For the critical physical unit-shell weight, elementary squarefree dyadic density and Mertens
give (B_N\gg1/\log N) once the aperture contains the physical dyadic shell. The strengthened
prime-clock estimate proves

\[
 \delta_N\log N\sqrt{\log N}\to0
 \quad\Longrightarrow\quad
 \chi_N^2\log N\to0.                                      \tag{21}
\]

Thus the forced tilt gives only the generic guarantee

\[
 \eta_N\ll\frac{\log\log N}{\sqrt{\log N}}=o(1),          \tag{22}
\]

not (N^{-1/2+o(1)}). Relative chi-square closes qualitative normalized contiguity, but cannot
certify Route E's strict-half power. This invalidates the earlier inference that a critical
normalized endpoint estimate could be moved to the saddle by `(7)` alone.

The physical source has a stronger exact law. If

\[
 m(T)=\prod_{p\in T}p,\qquad
 \nu_{\sigma,N}(T)=\frac{m(T)^{-\sigma}}
                         {\mathcal P_{\sigma,N}},\qquad
 W_{\sigma,x}(T)=m(T)^\sigma e^{-xm(T)},                  \tag{23}
\]

then atomwise

\[
 \boxed{\mathcal P_{\sigma,N}\nu_{\sigma,N}(T)
        W_{\sigma,x}(T)=e^{-xm(T)}.}                      \tag{24}
\]

Consequently, for every predeclared finite observable (F),

\[
 \boxed{
 \frac{\mathbb E_{\sigma,N}[F W_{\sigma,x}]}
      {\mathbb E_{\sigma,N}[W_{\sigma,x}]}
 =\frac{\sum_TF(T)e^{-xm(T)}}{\sum_Te^{-xm(T)}}}
                                                                  \tag{25}
\]

is exactly independent of (\sigma). The moving Euler parameter is a concentration gauge, not a
deformation of the physical Gibbs source. A source-faithful incidence proof may therefore work in
any Euler gauge with the matching physical multiplier and loses **zero** at the RH scale. If it
freezes the observable while changing only the Bernoulli law, it has left this exact gauge class;
then `(7)`, `(20)`, and their polylogarithmic rate are the appropriate but weaker statements.

Equation `(24)` is already the umbrella-reachable Lean theorem
`routeEEulerTiltTerm_eq_gibbsTerm`. Equation `(25)` is its finite termwise corollary. No new Lean
source was written during the corpus refactor.

## 6. Conjecture--proof/fail loop

1. **Conjecture:** every supercritical Euler tilt is contiguous to the critical source.
   **Failed.** At fixed (\delta>0), the expected occupied-prime count under
   (\nu_{1+\delta,N}) stays bounded while the critical expectation diverges. Fixed-distance
   tilts are distinguishable.
2. **Conjecture:** the exact escape boundary is the reflected prime-clock scale.
   **Proved in the direction Route E needs.** The local domination `(14)`--`(15)` reduces the full
   product law to existing prime-clock energy, giving the unconditional sufficient regime `(2)`.
3. **Conjecture:** contiguity transfers only events and is too weak for signed kernels.
   **Failed.** Exact likelihood Cauchy--Schwarz proves `(7)` for every real observable, including
   recurrence-weighted signed shell kernels.
4. **Conjecture:** source transfer itself proves unit-shell parity cancellation.
   **Failed.** Equation `(7)` compares two expectations of the same observable. It supplies no
   joint short-interval rough-token mass, column capacity, seam orientation, or recurrence
   accumulation. Those remain independent producer theorems.
5. **Conjecture:** relative chi-square repairs the normalization loss at strict-half scale.
   **Failed.** Equations `(20)`--`(22)` give only a polylogarithmic normalized error for the forced
   tilt, far above the target power.
6. **Conjecture:** a moving-to-critical source transfer theorem is nevertheless required for the
   literal physical relation.
   **Failed more strongly.** Atomwise gauge cancellation `(24)` proves exact invariance `(25)`.
   Chi-square is needed only for fixed observables that omit the compensating physical multiplier.

## 7. Lean theorem map

- `bernoulliChiSquare_eq_prod_local`: exact arbitrary finite Bernoulli product law `(11)`.
- `bernoulliExp_changeOfMeasure`: exact likelihood transport `(18)`.
- `bernoulliExp_sub_sq_le_chiSquare_mul_secondMoment`: observable transfer `(7)`.
- `routeEEulerBernoulli_localChi_eq`: Euler local identity `(12)`.
- `routeEEulerBernoulli_localChi_le_primeClock`: local domination `(14)`--`(15)`.
- `routeEEulerTiltChiSquareBelow_eq_prod`: finite prime-aperture product identity.
- `routeEEulerTiltChiSquareBelow_le_primeClock`: finite global bound `(3)`.
- `routeEEulerBernoulliExpBelow_sub_sq_le`: source-specific finite observable transfer.
- `tendsto_routeEEulerTiltChiSquareBelow_zero`: asymptotic contiguity `(5)` under `(2)`.
- `bernoulliNormalizedRatio_sub_abs_le`: relative normalized transfer `(20)`.
- `tendsto_routeEEulerTiltChiSquareBelow_mul_log_zero`: relative shell rate `(21)`.
- `routeEEulerTiltTerm_eq_gibbsTerm` in the source-faithful module: exact physical gauge
  cancellation `(24)`.

Direct check and targeted module build pass. `#print axioms` for all principal declarations reports
only `propext`, `Classical.choice`, and `Quot.sound`. No project axiom, `sorry`, `admit`, `opaque`,
`unsafe`, or computation is used.

## 8. Route E consequence and anti-theatre boundary

This theorem removes the bare-product mismatch for fixed bounded-second-moment consumers. It does
not remove that mismatch at RH power scale. For literal physical relations, the stronger atomwise
identity `(24)` removes it exactly: analysis may choose the critical or moving Euler gauge provided
the source-faithful multiplier changes with the gauge.

It does **not** close Route E. Live producer remains
`ENTROPY-COMPLEMENT-UNIT-SHELL-ROUGH-CONVOLUTION`: joint rough-token lower mass, unit incoming
load or its unmatched/chi-square replacement, normalized seam charge, and alternating recurrence
accumulation. This card changes where that theorem may be proved; it does not assert it.

## Log

- 2026-08-11 — exact Bernoulli product law, Euler local defect, prime-clock domination, observable
  transfer, and sub-prime-clock asymptotic formalized; moved directly to stage 3 after targeted
  Lean, build, lint-token, and axiom audits.
- 2026-08-11 — hostile normalized-rate audit added. Relative transfer and
  `chi-square * log N -> 0` declarations pass targeted build and axiom audit. Endpoint-transfer
  overclaim removed after recognizing exact physical Euler-gauge cancellation.
