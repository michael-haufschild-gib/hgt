# Species-predicted Stokes coenergy sharp prime--valuation asymptotic law

**ID:** ULF-SRFM-3  
**Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [FOURTH-ORGAN PREDICTION] [NEW CORPUS THEOREM] [NOVELTY UNVERIFIED] [LEAN PENDING] [NOT RH]`

## 1. Withheld prediction

ULF-SRFM-2 was derived without using the Stokes coenergy.  Its reflected prime reserve has order

\[
 p^{-2(1-t)}\log p.
\]

Under the corpus complementary coordinate

\[
 t=\frac{1-s}{2},
\tag{1.1}
\]

the reserve exponent is \(1+s\).  This leaves the complementary clock \(1-s\) needed to reach the
universal quadratic prime envelope \(p^{-2}\).  Before inspecting a sharp Stokes tail theorem, this
ledger predicts:

> reflected Stokes conditioning should supply the complementary clock exactly, and the existing
> upper bound should have a nonzero sharp asymptotic constant at every fixed valuation depth.

The corpus previously proved only positivity and the majorant

\[
 T_s(p,e)\le
 \frac{4(1-s)}{(e+1)^2}p^{-2-2se}.
\tag{1.2}
\]

This card proves the withheld sharp asymptotic independently from the exact Stokes definitions.

## 2. Source coordinates

Fix \(0<s<1\), a prime \(p\), and \(e\in\mathbb N_0\).  Put

\[
 L=\log p,
 \qquad q=p^{-1},
 \qquad r=p^{-s},
 \qquad u=(1-s)(e+1)L.
\tag{2.1}
\]

Let

\[
 V(u)=u\cosh u-\sinh u.
\tag{2.2}
\]

The exact corpus formulas give

\[
 I_s(p,e)=\frac{4q^{e+1}}{e+1}V(u)
\tag{2.3}
\]

for the complementary-coordinate geometric information factor, and

\[
 W_s(p,e)
 =c_s(p)^2
   \left(\frac q{1+q}\right)^2
   (1-r)^2
   \frac{r^e}{(e+1)^2Lr}
\tag{2.4}
\]

for the reflected Stokes weight.  Here the Gamma-sewn contraction satisfies

\[
 c_s(p)^4=\frac{(1+r)^4}{8(1+r^4)},
 \qquad c_s(p)>0.
\tag{2.5}
\]

The Stokes-conditioned information coenergy term is

\[
 T_s(p,e)=I_s(p,e)W_s(p,e).
\tag{2.6}
\]

Equations (2.3)--(2.5) are direct rewrites of the definitions and already formal corpus theorems;
no asymptotic conclusion from those files is imported.

## 3. Sharp asymptotic

### Theorem 3.1 (prime--valuation coenergy constant)

For every fixed \(0<s<1\) and \(e\in\mathbb N_0\),

\[
 \boxed{
 p^{2+2se}T_s(p,e)
 \longrightarrow
 \frac{1-s}{\sqrt2\,(e+1)^2}}
 \tag{3.1}
\]

as \(p\to\infty\) through primes.  Equivalently,

\[
 \boxed{
 T_s(p,e)\sim
 \frac{1-s}{\sqrt2\,(e+1)^2}
 p^{-2-2se}.}
 \tag{3.2}
\]

#### Proof

First, (2.5) and positivity imply

\[
 c_s(p)^2\longrightarrow\frac1{\sqrt8}.
\tag{3.3}
\]

Also

\[
 p^2\left(\frac q{1+q}\right)^2\longrightarrow1,
 \qquad
 (1-r)^2\longrightarrow1.
\tag{3.4}
\]

The exact exponential form of the virial is

\[
 V(u)=\frac{(u-1)e^u+(u+1)e^{-u}}2.
\tag{3.5}
\]

Since

\[
 e^u=p^{(1-s)(e+1)},
\tag{3.6}
\]

one has

\[
 p^{2se}q^{e+1}r^{e-1}e^u=1.
\tag{3.7}
\]

Moreover \(u/L=(1-s)(e+1)\), while the \(e^{-u}\) term in (3.5), after the same
renormalization, tends to zero.  Therefore

\[
 p^{2se}q^{e+1}r^{e-1}\frac{V(u)}L
 \longrightarrow \frac{(1-s)(e+1)}2.
\tag{3.8}
\]

Multiplying (2.3) and (2.4), then using (3.3), (3.4), and (3.8), gives

\[
\begin{aligned}
 p^{2+2se}T_s(p,e)
 &\longrightarrow
 4\cdot\frac1{\sqrt8}\cdot
 \frac{(1-s)(e+1)}{2(e+1)^3}\\
 &=\frac{1-s}{\sqrt2\,(e+1)^2}.
\end{aligned}
\]

This is (3.1).  ∎

### Corollary 3.2 (sharpness of the existing two-clock majorant)

Let

\[
 M_s(p,e)=\frac{4(1-s)}{(e+1)^2}p^{-2-2se}.
\tag{3.9}
\]

Then

\[
 \boxed{
 \frac{T_s(p,e)}{M_s(p,e)}
 \longrightarrow\frac1{4\sqrt2}.}
\tag{3.10}
\]

Thus the corpus majorant has the exact prime and valuation exponents.  It is not a loose
summability artifact; only its scalar constant is nonsharp.

## 4. Fourth-organ significance

The Poisson--Boolean--history fusion did not define \(T_s\).  It supplied a complementary exponent
ledger and predicted that a fourth, independently constructed Stokes conditioning law must realize
the missing clock without annihilating the coefficient.  Theorem 3.1 verifies exactly that:

\[
 \underbrace{1+s}_{\text{multiplicity-history reserve}}
 +\underbrace{1-s}_{\text{reflected conditioning clock}}
 =\underbrace{2}_{\text{Stokes prime coenergy}}.
\tag{4.1}
\]

At valuation depth \(e\), the same mechanism contributes the additional paired factor \(2se\).
The surviving constant \((1-s)/(\sqrt2(e+1)^2)\) proves that the transfer is non-erasing.

This is new unconditional leverage: it upgrades an upper-bound/summability statement in the Stokes
organ to a complete sharp tail classification, predicted from a formation-species comparison.

## 5. Hostile tests and scope

1. **No RH selection follows.**  The limit is positive for every \(0<s<1\).
2. **The result is not uniform in \(e\).**  Valuation depth is fixed before the prime limit.
3. **The Gamma constant is load-bearing.**  Omitting the sewn contraction changes the limiting
   scalar.
4. **Complementary coordinate is load-bearing.**  An arbitrary relation between \(s\) and the
   information aperture does not produce exponent (4.1).
5. **The theorem concerns the literal corpus coenergy.**  It asserts no general asymptotic for
   unrelated Stokes phenomena.
6. **The route theorem does not establish the universal field by itself.**  It passes Gate IV for
   this fusion chamber; formation properness and selection remain open.

## 6. Literature and corpus audit

The hyperbolic virial asymptotic and elementary power bookkeeping are classical.  The exact object
\(T_s(p,e)\), its Gamma-sewn factor, and its prime--valuation limit are corpus-specific.  Search of
the formal declarations, paper pipeline, and broad arXiv literature through August 2026 found the
upper bound and summability theorem but no sharp limit (3.1) or ratio (3.10).

The honest classification is a new theorem about an existing corpus construction, obtained from a
new cross-species prediction.  No external priority claim is made.

## 7. Lean boundary

This card audits existing Lean definitions read-only.  It adds no Lean code and runs no Lean build.
Formalization requires a prime-at-infinity filter lemma, the exact rewrites (2.3)--(2.5), elementary
hyperbolic asymptotics, and limit multiplication.  Stage 3 remains closed until that proof is
unconditional and axiom-audited in Lean.
