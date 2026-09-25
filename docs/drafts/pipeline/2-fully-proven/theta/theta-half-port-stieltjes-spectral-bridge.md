# The theta half-port as a positive Stieltjes spectral measure

- **Stage:** 2-fully-proven on paper; Lean formalization open.
- **Routes:** WS2, with the theta renewal connection.
- **Dependency:** The literal completed-theta source and its strict positive-ray decrease in [the half-line port theorem](theta-half-line-port-alternating-orientation.md), and the exact one-port seam identity in [the renewal factorization](theta-renewal-phase-cosh-factorization.md).
- **Scope:** An exact self-adjoint spectral representation of one theta port and its two-sheet Xi trace. Spectral positivity alone is not a zero-location theorem.

## Statement

Let `k(x)` be the even completed-theta source, positive and strictly
decreasing for `x>0`, and put

\[
 h(z)=\int_0^\infty k(x)e^{izx}\,dx,\qquad
 \omega(x)=-k'(x)>0\quad(x>0).
\]
Every exponential moment of `k` is finite, so `h` is entire and
\(\Xi(z)=h(z)+h(-z)\). Define the positive density
\[
 \boxed{\displaystyle
 \sigma(t)=\frac{1}{\pi\sqrt t}
       \int_0^\infty\omega(x)
          \bigl(1-\cos(\sqrt t\,x)\bigr)\,dx>0,
       \qquad t>0.}                                      \tag{1}
\]
It is locally smooth, behaves as `O(sqrt(t))` at zero, and is
`O(t^(-1/2))` at infinity; hence
\(\int_0^\infty\sigma(t)/(1+t)\,dt<\infty\).
For \(\zeta\in\mathbb C\setminus[0,\infty)\), choose the square root
\(w\) with \(\operatorname{Im}w>0\). Then the **literal one-sided theta
connection is a Stieltjes transform**:
\[
 \boxed{\displaystyle
 m(\zeta):=h(w)
       =\int_0^\infty\frac{\sigma(t)}{t-\zeta}\,dt.} \tag{2}
\]
Thus \(\operatorname{Im}m(\zeta)>0\) for \(\operatorname{Im}\zeta>0\),
and \(m(-r^2)=h(ir)>0\) for `r>0`. To give a genuine Hilbert-space
realization despite \(\int\sigma=\infty\), put
\(d\mu(t)=\sigma(t)dt/(1+t)\), let `A` be multiplication by `t`
on \(L^2(\mu)\), and let `1` denote its finite-norm constant vector.
Then the exact resolvent formula is
\[
 m(\zeta)=m(-1)+(\zeta+1)
   \langle 1,(A-\zeta)^{-1}1\rangle_{L^2(\mu)}.       \tag{2a}
\]
This is an explicit self-adjoint spectral model for **one port**.
The measure is the actual theta source's sine response, not a
measure inferred from an assumed RH divisor.

On the positive spectral cut, the two boundary sheets are
\(m_+(u^2)=h(u)\) and \(m_-(u^2)=h(-u)=\overline{h(u)}\). Consequently
\[
 \boxed{\displaystyle
 \sigma(u^2)=\frac{\operatorname{Im}h(u)}{\pi},\qquad
 \Xi(u)=2\operatorname{PV}\!\int_0^\infty
                  \frac{\sigma(t)}{t-u^2}\,dt\quad(u>0).} \tag{3}
\]
The Xi coefficient is the **two-sheet real trace** of a positive
Stieltjes connection. This distinguishes the self-adjoint one-port
realization from the missing two-port zero-confinement theorem.
Since \(\sigma(t)>0\) at every `t>0`, a real Xi zero in (3) is a
zero of the *principal-value real part* **inside** the spectral
continuum of `A`, while \(m_+(t)\ne0\). It is a phase-matching point,
not an eigenvalue of this multiplication operator. A self-adjoint
zero carrier would therefore need a further source-defined coupling
or a different spectral realization.

There is an exact compatibility with the positive-renewal law. With
`a=1/4`, `c=Theta(1)`, and
\[
 C(r)=\int_0^\infty Q(s)\cos(rs)\,ds,\qquad
 S(r)=\int_0^\infty Q(s)\sin(rs)\,ds,
\]
the one-port seam formula gives, for `u>0` and `r=u/2`,
\[
 \boxed{\displaystyle
 \pi\sigma(u^2)
  =c\left[r-e^{-C(r)}
              \bigl(r\cos S(r)+a\sin S(r)\bigr)\right]>0.} \tag{4}
\]
Equations (1) and (4) identify the **same positive spectral density**
from the completed-theta exit source and from its renewal logarithm.
The inequality in (4) is strict for every positive frequency, while
the real trace in (3) can change sign. Any two-port spectral argument
must use this joint identity and the source's modular arithmetic to
control the trace; the positivity of `m` on its own does not do so.

The [rational-cusp Abel formula](theta-rational-cusp-boundary-law.md)
gives a second, arithmetic expression for the same density. Define
\[
 M_u=\int_1^\infty y^{iu/2-3/4}(\Theta(y)-1)\,dy
 \qquad(u\in\mathbb R).
\]
Its one-sided connection identity is
\(h(u)=\tfrac14+\tfrac{iu}{2}(c-1)
 -\tfrac{u^2+1/4}{4}M_u\). Taking real and imaginary parts yields
\[
 \boxed{\displaystyle
 \pi\sigma(u^2)=\frac{u(c-1)}2
       -\frac{u^2+1/4}{4}\operatorname{Im}M_u>0,
 \qquad
 \Xi(u)=\frac12-\frac{u^2+1/4}{2}\operatorname{Re}M_u.} \tag{4a}
\]
Thus the positive spectral density and Xi's signed zero signal are
the imaginary and real parts of **one literal theta Mellin tail**.
The rotated-ray formula in that card transports both parts toward
the same global Abel/Gauss-cusp boundary. The missing theorem is a
coupled constraint on those parts, not a separate positivity claim
about either one.
Equating (4) and (4a) makes the renewal--Mellin compatibility explicit:
\[
 \boxed{\displaystyle
 \frac{u^2+1/4}{4}\operatorname{Im}M_u
   =c e^{-C(u/2)}\left[
          \frac u2\cos S(u/2)+a\sin S(u/2)\right]-\frac u2.}
                                                               \tag{4b}
\]
This identity is the concrete source coupling to test against the
global cusp-phase law; it retains the seam term from the one-port
formula rather than replacing it by an abstract positive measure.

## Paper proof

Integration by parts, using `k(x)->0` and
\(\int_0^\infty\omega=k(0)\), gives for `u>0`
\[
 \operatorname{Im}h(u)
  =\int_0^\infty k(x)\sin(ux)\,dx
  =\frac1u\int_0^\infty\omega(x)(1-\cos(ux))\,dx>0. \tag{5}
\]
Strict positivity follows because `omega` has positive mass on an
interval and `1-cos(ux)` vanishes only on a discrete set. This proves
the first equality of (3) and the bounds following (1). Smoothness at
positive `t` follows from the source's exponential moments.

For `r>0`, Tonelli applies to the nonnegative integrand in (1).
After setting `t=u^2`, the elementary cosine-resolvent integral gives
\[
 \begin{aligned}
 \int_0^\infty\frac{\sigma(t)}{t+r^2}\,dt
 &=\frac2\pi\int_0^\infty\omega(x)
       \left[\int_0^\infty
        \frac{1-\cos(ux)}{u^2+r^2}\,du\right]dx\\
 &=\frac1r\int_0^\infty\omega(x)(1-e^{-rx})\,dx
  =\int_0^\infty k(x)e^{-rx}\,dx=h(ir).
 \end{aligned}                                                     \tag{6}
\]
The last equality is integration by parts. Both sides of (2) are
holomorphic on the slit plane and agree on its negative real interval,
so the identity theorem proves (2) everywhere. Its upper-half-plane
imaginary part is positive by the integral in (2). The standard
principal-value boundary formula applies because `sigma` is smooth
near each `u^2>0` and has the stated endpoint bounds. This proves
(3), using the even-source identity for Xi.

For (4), substitute `z=r` in the renewal card's exact identity
\(h(2z)=(a-iz)D(-iz)+icz\) and use
\(D(-ir)=c\exp[-C(r)-iS(r)]\). Taking imaginary parts and applying
(3) gives (4), including its strict sign by (5).

## Remaining producer question

The new spectral model is positive and self-adjoint **before** the
two boundary sheets are coupled. The hard mathematical question is to
derive, from the literal theta atoms or their modular/Gauss-cusp
boundary law, a nonlocal constraint on `sigma` that keeps the analytic
continuation of its principal-value trace in (3) from vanishing at a
nonreal squared frequency. Neither Stieltjes positivity nor the
compound-Poisson renewal law separately provides that constraint.
This paper theorem changes the candidate object for WS2 from an
abstract positive network to an explicit source-defined spectral
measure; it does not claim RH or a Lean proof.
