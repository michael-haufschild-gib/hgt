# Gaussian-residue nonadmission in the unweighted Xi incidence completion

- **ID:** `deninger-meyer-gaussian-residue-incidence-nonadmission`
- **Stage:** 2-fully-proven
- **Type:** SOURCE-TOPOLOGY OBSTRUCTION / POSITIVE SURVIVOR
- **Status:** `[LOCAL-RESEARCH] [PAPER PROOF COMPLETE] [LEAN PENDING]`
- **Parent:**
  `../../../1-in-progress/deninger-meyer-gaussian-green-resolvent.md`
- **Publication context:**
  `../../../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`

## 1. Frontier statement

Fix the Gaussian centre (c=2).  For every nontrivial Xi divisor point
(ho), the completed singular Meyer lift has the exact nonzero residue

\[
 R(\rho)
 =-\frac{2\pi\,A(\rho)}
          {\chi_2(\rho)(\rho-2)},
 \qquad
 \chi_2(s)=\exp\!\left(\frac{(s-2)^2}{4\pi}\right),
\tag{1}
\]

where

\[
 A(s)=\frac{s(s-1)}2\,\Gamma_{\mathbb R}(s),
 \qquad
 \Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2).
\tag{2}
\]

The new theorem is:

> **Gaussian-residue incidence nonadmission.**  The family
> ({R(\rho):\rho\in\operatorname{Div}(\Xi)}) is unbounded.  More
> precisely, for constants (C,T_0>0), depending only on the fixed centre,
> every Xi divisor point (ho=\beta+i\gamma) with
> (|\gamma|\ge T_0) satisfies
> \[
> |R(\rho)|
> \ge C\exp\!\left(\frac{\gamma^2}{32\pi}\right).
> \tag{3}
> \]
> Consequently the raw residue packet is not in the unweighted
> (ell^2) Xi-jet carrier, nor in any completion whose coordinate
> inclusions are uniformly bounded by the unweighted (ell^2) norm.

This is unconditional.  It uses only the open-strip theorem for the Xi
divisor, local finiteness plus infinitude of that divisor, the Gamma
reflection formula, and the exact residue formula already proved in Lean.

## 2. Uniform lower bound for the Archimedean factor

Write (ho=\beta+i\gamma), with (0<\beta<1), and put
(z=\rho/2).  The reflected point (1-z) has real part in
([1/2,1]).  By the integral estimate

\[
 |\Gamma(x+iy)|\le \Gamma(x)\qquad(x>0)
\tag{4}
\]

and continuity of the real Gamma function on the compact interval
([1/2,1]), there is a finite constant

\[
 M=\max_{1/2\le x\le1}\Gamma(x)>0
\tag{5}
\]

such that (|\Gamma(1-z)|\le M) for every strip point.

Euler reflection gives

\[
 |\Gamma(z)|\,|\Gamma(1-z)|
 =\frac\pi{|\sin(\pi z)|}.
\tag{6}
\]

For (z=x+iy),

\[
 |\sin(\pi z)|^2
 =\sin^2(\pi x)+\sinh^2(\pi y)
 \le \cosh^2(\pi y)
 \le e^{2\pi|y|}.
\tag{7}
\]

Here (y=\gamma/2).  Equations (5)--(7) imply

\[
 |\Gamma(\rho/2)|
 \ge \frac\pi M e^{-\pi|\gamma|/2}.
\tag{8}
\]

Since (0<\beta<1) and (pi>1),
(pi^{-\beta/2}\ge\pi^{-1/2}).  Hence

\[
 |\Gamma_{\mathbb R}(\rho)|
 \ge \frac{\sqrt\pi}{M}e^{-\pi|\gamma|/2}.
\tag{9}
\]

No Stirling expansion is needed; (9) is a uniform strip lower bound.

## 3. Gaussian inverse growth

The exact complex-exponential norm gives

\[
 |\chi_2(\rho)|^{-1}
 =\exp\!\left(
     \frac{\gamma^2-(\beta-2)^2}{4\pi}
   \right).
\tag{10}
\]

Because (0<\beta<1), one has (1<(2-\beta)<2), hence
((\beta-2)^2\le4).  Therefore

\[
 |\chi_2(\rho)|^{-1}
 \ge e^{-1/\pi}\exp\!\left(\frac{\gamma^2}{4\pi}\right).
\tag{11}
\]

The elementary norm bounds

\[
 |\rho|\ge|\gamma|,
 \quad |\rho-1|\ge|\gamma|,
 \quad |\rho-2|\le|\gamma|+2
\tag{12}
\]

give, for (|\gamma|\ge2),

\[
 \frac{|\rho|\,|\rho-1|}{|\rho-2|}
 \ge \frac{\gamma^2}{|\gamma|+2}
 \ge \frac{|\gamma|}{2}.
\tag{13}
\]

Substituting (2), (9), (11), and (13) into (1) yields

\[
 |R(\rho)|
 \ge
 \frac{\pi^{3/2}}{2M}e^{-1/\pi}
 |\gamma|
 \exp\!\left(
       \frac{\gamma^2}{4\pi}-\frac{\pi|\gamma|}{2}
     \right).
\tag{14}
\]

If (|\gamma|\ge 8\pi^2), then

\[
 \frac{\gamma^2}{4\pi}-\frac{\pi|\gamma|}{2}
 \ge \frac{3\gamma^2}{16\pi}
 \ge \frac{\gamma^2}{32\pi}.
\tag{15}
\]

After enlarging the threshold so that (|\gamma|\ge1), (14)--(15)
prove (3), with

\[
 C=\frac{\pi^{3/2}}{2M}e^{-1/\pi}>0.
\tag{16}
\]

## 4. Xi heights escape

The Xi divisor support is infinite and locally finite.  If its ordinates
were bounded by (T), the support would lie in the compact rectangle

\[
 [0,1]+i[-T,T],
\]

and local finiteness would make it finite, contradiction.  Thus for every
(T) there is a divisor point with (|\Im\rho|>T).  Applying (3) along
such points proves unboundedness of (R).

Every (ell^2) family is bounded coordinatewise by its (ell^2) norm.
An unbounded coordinate family therefore cannot belong to the unweighted
Xi incidence Hilbert carrier.  The same argument applies after restoring
multiplicity copies: select any one copy above each support point.

## 5. Exact positive survivor: forced two-factor rigging

The obstruction determines, rather than merely rejects, the diagonal
renormalization.  Define the source-residue flattening factor

\[
 W(\rho)
 =-\frac{\chi_2(\rho)(\rho-2)}{2\pi A(\rho)}.
\tag{17}
\]

The open-strip nonvanishing of (A) makes (W) well-defined, and (1)
gives the exact identity

\[
                         W(\rho)R(\rho)=1.
\tag{18}
\]

Let (d(\rho)) be any diagonal coefficient used to place the raw residue
packet into an (ell^2) carrier.  Put

\[
                         h(\rho)=d(\rho)R(\rho).
\tag{19}
\]

Then

\[
                         d(\rho)=h(\rho)W(\rho),
\tag{20}
\]

and

\[
             (d(\rho)R(\rho))_\rho\in\ell^2
             \quad\Longleftrightarrow\quad
             (h(\rho))_\rho\in\ell^2.
\tag{21}
\]

Thus every diagonal Hilbert admission of the forced principal parts has a
unique two-factor form:

1. the nonlocal analytic factor (W), forced coefficient-by-coefficient
   by the Möbius--Gaussian source residue;
2. an independent square-summable grade factor (h), required solely to
   sum the infinite divisor.

The first factor neutralizes Gaussian residue explosion but produces the
constant packet (1), which is still not in unweighted (ell^2) because
the Xi divisor is infinite.  The second factor is therefore unavoidable.
This is the exact analytic/grade split anticipated by the finite-fibre
source-horizon theorem.  A single ungraded completion cannot perform both
jobs while remaining uniformly conservative.

## 6. Hostile audit

### Attack A: ordinary meromorphic continuation

Burnol's extended property-S theory and later Fourier interpolation
theorems already construct meromorphic continuations and zero-jet
interpolation systems.  Those results can assemble scalar principal parts.
They do not supply the source-residue normalization (17), a resolved Green
packet, completed augmentation conservativity, or the Hermitian
factorization required here.  Claiming only continuation would be
rediscovery.

### Attack B: reuse the completed Xi/incidence isometry

The existing Lean completion is built by pulling the Xi-jet Hilbert norm
back through a coefficient identification.  Its isometric comparison is
therefore exact but does not prove that the raw Möbius--Gaussian residue
packet belongs to that Hilbert space.  Theorem (3) proves it does not.
Transporting an already completed Xi vector through that isometry cannot
discharge source admission of the singular lift.

### Attack C: cancel the Gaussian by (17) and stop

Equation (18) leaves the constant packet.  Infinite Xi support makes that
packet non-(ell^2).  Analytic residue flattening and global grade
summability are independent gates.

### Attack D: choose an arbitrary rapidly decaying weight

An arbitrary weight can force summability but loses source provenance and
does not determine Hermitian normalization.  Equation (20) classifies the
only source-faithful part: every admissible diagonal weight must factor
through the canonical (W).  The remaining (h) must be derived from an
arithmetic source-horizon grading and then tested for augmentation
conservativity and Gram order.

## 7. Novelty verdict

- Generic scalar meromorphic continuation: **REDISCOVERED / BRIDGE**.
- Exact residue formula (1): **LOCAL-RESEARCH, LEAN-PROVED parent**.
- Unbounded actual-divisor residue law (3): **LOCAL-RESEARCH, PAPER-PROVED**.
- Forced analytic/grade factorization (17)--(21):
  **LOCAL-RESEARCH, PAPER-PROVED**.

External search found no theorem addressing this source-specific residue
packet or its incidence-completion nonadmission.  Novelty remains labelled
local until specialist review.

## 8. Updated Route-L frontier

The topological gate is no longer “find a completion admitting the
principal parts.”  It is:

> Construct a source-horizon grade (h) from the ordinary-prime/
> Gamma/co-Poisson source such that (h\in\ell^2), retain the canonical
> analytic normalizer (W), prove the resulting weighted incidence sector
> is conservative before codiagonal augmentation, and derive its required
> Gram domination.

This is strictly narrower than the current manuscript frontier and rules
out the unweighted completed-incidence landing for the actual singular
Meyer lift.

