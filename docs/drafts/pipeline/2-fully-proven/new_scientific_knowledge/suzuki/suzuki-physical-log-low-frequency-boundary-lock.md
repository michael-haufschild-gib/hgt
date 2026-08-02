# Suzuki physical-log realization is locked to low-frequency return

- **ID:** `suzuki-physical-log-low-frequency-boundary-lock`
- **Stage:** 2-fully-proven
- **Type:** SOURCE-ARCHITECTURE NO-GO / EXACT POSITIVE REPLACEMENT
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes
- **Inputs:** `suzuki-exterior-residual-rigged-wiener-realization.md`,
  `suzuki-wiener-nuclear-boundary-carrier.md`,
  `suzuki-exterior-feshbach-pruning-law.md`

## 1. Result

The proposed Route-O split

```text
high-frequency Wiener carrier
  -> physical L2(dr/r) Gamma carrier,
then
low-frequency Evans return
```

is false as an architecture.  Physical-log admissibility of the high-frequency part already
contains a low-frequency boundary condition.

Let \(u\in C(\mathbb R)\cap L^1(\mathbb R)\) be supported in \([-a,a]\), so \(u(\pm a)=0\).
Choose a real even cutoff

```text
chi in C_c^infinity(R),   chi=1 on [-Xi,Xi],
```

and split

```text
u_low=Fourier^(-1)(chi uhat),
u_high=u-u_low.                                         (1)
```

Then \(u_{\rm low}\) and \(u_{\rm high}\) are continuous at both endpoints.  If

```text
integral_0^epsilon |u_high(a-r)|^2 dr/r < infinity,     (2+)
```

then necessarily

```text
m_(chi,+)(u):=u_low(a)
 =(1/(2pi)) integral_R chi(xi) uhat(xi) exp(i a xi) dxi
 =0.                                                     (3+)
```

The left endpoint has the exact companion:

```text
integral_0^epsilon |u_high(-a+r)|^2 dr/r < infinity
 -> m_(chi,-)(u):=u_low(-a)=0.                           (3-)
```

Thus a two-ended physical-log high carrier requires the two low-frequency moment equations

```text
m_(chi,+)(u)=m_(chi,-)(u)=0.                             (4)
```

Neither Dirichlet boundary values nor vanishing half-log traces imply `(4)`.  Indeed there are
nonzero \(u\in C_c^\infty(-a,a)\), hence functions flat to every order at both endpoints, for
which \(m_{\chi,+}(u)\ne0\).  For every such function its high-frequency part has infinite
physical-log mass at the right endpoint.

Consequently the missing nuclear estimate

```text
sum_q integral_0^1 |g_q(r)|^2 dr/r < infinity            (5)
```

cannot be proved from Suzuki's completed-domain regularity and the high-frequency Neumann series
alone.  If absolute valuation evaluation reconstructs \(u_{\rm high}\), `(5)` implies `(2+)` by
Minkowski and therefore already forces `(3+)`.  The physical-log carrier gate and the
low-frequency two-port return gate are one coupled problem.

## 2. Boundary divergence lemma

Let \(E\) be a real normed space and let \(f:(-\epsilon,\epsilon)\to E\) be continuous at zero.
Then

```text
integral_0^epsilon ||f(r)||^2 dr/r < infinity
 -> f(0)=0.                                              (6)
```

### Proof

If \(f(0)\ne0\), continuity gives a \(\delta>0\) such that

```text
||f(r)|| >= ||f(0)||/2       for 0<r<delta.
```

Hence

```text
integral_0^delta ||f(r)||^2 dr/r
 >= ||f(0)||^2/4 integral_0^delta dr/r
 =infinity,
```

contradicting the premise. `QED`

This is necessity only.  A zero boundary value without a quantitative modulus does not by itself
imply physical-log integrability.

## 3. Exact low/high lock

At \(x=a\), equation `(1)` and the Dirichlet value give

```text
u_high(a)=-u_low(a)=-m_(chi,+)(u).                       (7)
```

If `(2+)` holds, apply `(6)` to \(f(r)=u_{\rm high}(a-r)\).  It gives
\(u_{\rm high}(a)=0\), and `(7)` yields `(3+)`.  The proof at \(-a\) is identical. `QED`

The conclusion is independent of cutoff sharpness.  Any continuous low/high splitting has the
same boundary lock.  Formula `(3+)` merely identifies its value for the Fourier cutoff used by
the exact high-frequency Wiener inverse.

## 4. Flat source counterexample

The failure is not caused by a rough completed-domain vector.

Take \(\chi\) real, even, nonnegative, smooth, compactly supported, nonzero, and equal to one on
the prescribed low-frequency interval.  Its inverse Fourier kernel

```text
K=Fourier^(-1)chi
```

is real and continuous, with

```text
K(0)=(1/(2pi)) integral_R chi(xi) dxi>0.                 (8)
```

Choose \(\delta>0\) so that \(K(t)>0\) for \(|t|<\delta\), and choose a nonzero
nonnegative

```text
u in C_c^infinity((a-delta,a)).
```

Then \(u\) is identically zero in endpoint collars and has zero half-log trace, zero inverse-log
grades, and every Sobolev boundary trace.  Nevertheless

```text
m_(chi,+)(u)
 =u_low(a)
 =integral K(a-y)u(y)dy
 >0.                                                     (9)
```

By `(7)`, \(u_{\rm high}(a)<0\); by `(6)`, its \(dr/r\) square mass diverges. `QED`

This counterexample does not claim that a Suzuki zero mode violates `(4)`.  It proves the sharper
architectural statement: completed-domain regularity, trace zero, even \(C_c^\infty\) boundary
flatness, and high-frequency inversion do not supply `(4)`.  Any proof of `(4)` for a zero mode
must use its low-frequency source matching.

## 5. Nuclear valuation consequence

Suppose the high-frequency Wiener carrier provides seam profiles \(g_q\) and unit-modulus phase
evaluation

```text
u_high(a-r)=sum_q omega_q(r) g_q(r),    |omega_q(r)|=1. (10)
```

If `(5)` is understood in the nuclear form

```text
sum_q ||g_q||_(L2((0,epsilon),dr/r)) < infinity,         (11)
```

then Minkowski gives

```text
||u_high(a-.)||_(L2(dr/r))
 <=sum_q ||g_q||_(L2(dr/r))<infinity.                   (12)
```

Equations `(6)`--`(7)` force \(m_{\chi,+}(u)=0\).  Therefore a theorem proving `(11)` from only
the exterior \(L^2\) Hardy amplitudes and the Neumann word majorant would silently prove a
low-frequency return equation absent from its hypotheses.  The flat counterexample shows such a
theorem is false.

## 6. Correct replacement architecture

The valid Route-O interface is

```text
exact full two-port equation
  -> solve low-frequency divisibility/return and high-frequency Wiener tail together
  -> impose the two boundary moment cancellations (4)
  -> form matched full physical profiles
  -> conjugate the sign-correct full/Feshbach system to boundary log coordinates
  -> apply Gamma scattering and physical-tail coercivity.                  (13)
```

Equivalently, one may work with a quotient in which boundary constants are retained as explicit
finite-dimensional channels.  They cannot be discarded: the low and high constants cancel only
after matching.  Applying the homogeneous Gamma theorem to the high tail before this cancellation
creates an artificial non-\(L^2(dL)\) constant mode.

This changes the frontier:

```text
old E1: high-frequency nuclear dr/r upgrade;
old E3: later low-frequency Evans injectivity;

new E1/E3 lock:
  coupled two-port return with boundary moments (4),
  followed by matched physical-log/Feshbach intertwining.                  (14)
```

The positive gain is exact.  The impossible free-standing \(dr/r\) theorem is removed, and its
missing hypotheses are identified as two explicit source moments already belonging to the
RH-bearing return operator.

## 7. Hostile audit

1. **No claim that trace zero implies `(4)`.**  The \(C_c^\infty\) counterexample disproves it.
2. **No claim that \(f(0)=0\) suffices for \(dr/r\).**  Only necessity is used.
3. **No cancellation hidden inside `ell1`.**  Nuclear control implies scalar control by
   Minkowski; cancellation cannot rescue a nonzero endpoint constant.
4. **No illegal division at low-frequency zeros.**  The replacement explicitly keeps
   divisibility and return matching.
5. **No RH claim.**  Proving the coupled return operator injective for every aperture remains
   equivalent to Suzuki's zero-mode exclusion.

## 8. Lean certificate

The load-bearing analytic implication and exact splitting lock are formalized unconditionally in

```text
formal/GaloisForLFunctions/RHTower/SuzukiPhysicalLogBoundaryMomentLock.lean
```

as:

```text
physicalLogIntegrable_continuousAt_zero;
lowFrequencyBoundaryMoment_eq_zero_of_physicalLogIntegrable_high;
not_physicalLogIntegrable_high_of_lowFrequencyBoundaryMoment_ne_zero.
```

The proof reduces nonzero boundary value to the nonintegrability of \(1/r\); it assumes no RH,
source sign, zero data, or computation.

## 9. Novelty boundary

The divergence of \(dr/r\) at a nonzero continuous boundary value and Fourier low/high splitting
are classical.  No novelty is claimed for either separately.  Candidate-new source knowledge is
their exact consequence for Suzuki's Route-O architecture:

```text
nuclear physical-log high carrier
 -> low-frequency boundary return moments
 -> E1 and E3 are inseparable.                           (15)
```

No prior corpus card or audited source identified this lock.  Specialist priority review remains
required.

## Gates

- [x] prove continuous physical-log mass forces boundary value zero
- [x] identify exact low-frequency boundary moment
- [x] prove two-ended moment lock
- [x] give a boundary-flat \(C_c^\infty\) counterexample to free-standing high-tail admissibility
- [x] prove nuclear valuation control implies the scalar lock
- [x] replace sequential E1/E3 architecture by coupled matching
- [x] formalize analytic core unconditionally in Lean
- [ ] construct literal coupled two-port/Feshbach boundary return operator
- [ ] prove its boundary moments vanish for every trace-zero zero mode
- [ ] prove matched full profiles enter the physical Gamma carrier
- [ ] prove coupled return injective for every aperture
- [ ] RH
