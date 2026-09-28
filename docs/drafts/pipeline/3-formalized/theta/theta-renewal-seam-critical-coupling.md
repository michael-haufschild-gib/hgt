# Critical seam coupling in the positive theta renewal family

- **ID:** `theta-renewal-seam-critical-coupling`
- **Stage:** 3-formalized (paper proof formalized unconditionally in Lean; see `theta-renewal-seam-critical-coupling-formalized.md`)
- **Type:** THEOREM (paper), source-specific bifurcation and zero-escape law
- **Routes:** STC, CSB, U; theta one-port interface
- **Source:** The literal [theta renewal factorization](theta-renewal-phase-cosh-factorization.md) and [complex-resonance phase](theta-renewal-complex-resonance-stieltjes-obstruction.md).
- **Statement:** Scaling the positive renewal input while holding its modular seam value fixed makes the physical Xi function an isolated cancellation point. Every coupling `0<r<1` has infinitely many nonreal zeros but only finitely many in each bounded horizontal strip. Infinitely many real zero-pair contacts accumulate exponentially at `r=1`; just below each contact, nonreal zero clusters occur inside the natural critical strip. Thus no left neighborhood of the physical coupling is off-axis zero-free.

## The conjecture tested

The renewal mass `q<1/6` is small and the causal denominator is zero-free in the physical half-plane. Could one deform from zero renewal input to the literal theta input, keep source positivity and stability, and transport zero-location by a regular scalar homotopy? The answer is **no**: the small renewal mass is not the spectral control parameter. Exact matching of the theta source to its modular seam is a singular endpoint condition.

Put `a=1/4`, `c=Θ(1)>0`, and use the literal positive increment `ν`, its entire Laplace transform `N`, and `D=c-N` from the source card. For `0≤r≤1`, define

```text
ν_r=rν,                 D_r(z)=c-rN(z),
X_r(z)=(a-iz)D_r(-iz)+(a+iz)D_r(iz),
C=2ac.                                                   (1)
```

The positive renewal mass is `q_r=rq<1/6`; for `Re z≥-a`, `|rN(z)|≤rq c<c`, so every `D_r` is zero-free there. Its logarithmic convolution kernel is still positive for `r>0`:

```text
Q_r(t)=∑_(m≥1) r^m ν^{*m}(t)/(m c^m)>0.             (2)
```

But the exact two-ended identity gives the decisive affine law

```text
X_r(z)=C(1-r)+r Xi(2z).                              (3)
```

In particular `X_0=C` has no zeros, while `X_1=Xi(2z)` is the physical function. All assertions below concern this exact source deformation; for `r≠1` it is **not** asserted to preserve the full modular identity.

The missing smoothness has an exact source interpretation. Writing `D=(λ-a)L` for the one-sided Laplace transform of `P`, one has `D_r/(λ-a)=rL+(1-r)c/(λ-a)`. Thus the inverse source is `P_r(t)=rP(t)+(1-r)c exp(at)` for `t≥0`. Its even extension has derivative jump `2ac(1-r)=C(1-r)` at zero; on the Fourier side this is the central Dirac atom represented by the constant in (3). A separate [analytic renewal-preserving surgery theorem](theta-renewal-reflection-preserving-zero-surgery.md) removes this cusp objection and still constructs off-axis zeros while retaining positive increments, exact mass and the full reflection law.

## The seam is the unique cancellation coupling

**[PROVED HERE ON PAPER]** The function `XiC` tends to zero as `|Re z|→∞`, uniformly on **every** bounded horizontal strip `|Im z|≤B`, not merely in the natural critical strip. The corpus proves the all-shift exponential integrability of the even theta source in [`integrable_exp_mul_thetaCuspFullSource`](../../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaAllShiftedTails.lean) and its global Fourier--Laplace identity in [`thetaCuspFourierLaplace_eq_XiC_all`](../../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceSpectrumExact.lean). For fixed `B`, the tilted densities `e^{v x}k(x)`, `|v|≤B`, form a compact family in `L¹`: continuity in `v` follows by domination with `e^{(B+1)|x|}k(x)`. Riemann--Lebesgue convergence is uniform on compact subsets of `L¹`, by a finite-net argument. Applying this to the Fourier--Laplace identity proves

```text
sup_(|v|≤B) |XiC(u+iv)| → 0               (|u|→∞). (4)
```

Consequently, for every `0≤r<1`, `X_r(z)→C(1-r)>0` uniformly as `|Re z|→∞` on each bounded horizontal strip. The same holds with a negative nonzero limit for `r>1`, though positivity of (2) is then not used.

This is visible already at the first endpoint coefficient. Since `ν(0)=ac` and `ν,ν'∈L¹`, integration by parts gives `iy N(iy)→ac`. Thus each of the two reflected terms in (1) contributes `ac(1-r)` at large real frequency. At `r=1` the constant seam terms cancel exactly; all further algebraic terms cancel by the physical theta reflection, leaving the exponentially small Xi signal. In (2), `Q_r(0)=ra`, whereas the physical odd-reflection seam law demands `Q(0)=a`; its failure for `r≠1` identifies the same mismatch locally.

The critical-axis phase makes the singularity explicit. Write `A_r(λ)=(a+λ)D_r(λ)` and let `H` be the physical one-sided theta transform from the renewal source card. Its seam identity gives

```text
A_r(iy)=icy+ac(1-r)+rH(-2y).                       (3a)
```

For `y>0`, `Im A_r(iy)>0` by the same positive quadrant law as for `D`, so choose `θ_r(y)=arg A_r(iy)∈(0,π)`. Since `H(-2y)→0`,

```text
lim_(y→∞) y[θ_r(y)-π/2]=-a(1-r)                 (0≤r<1). (3b)
```

At `r=1`, by contrast, the [resonance-phase law](theta-renewal-complex-resonance-stieltjes-obstruction.md) gives `θ_1(y)-π/2=O_κ(e^(-κy)/y)` with infinitely many sign changes. The coefficient `a(1-r)` is the exact algebraic **seam mismatch order parameter**. Source positivity and causal stability remain true on both sides of this qualitative phase change.

## Infinite nonreal zeros at every nonphysical coupling

**[PROVED HERE ON PAPER]** For every `0<r<1`, `X_r` has infinitely many nonreal zeros, but only finitely many zeros in each fixed horizontal strip `|Im z|≤B`.

The strip finiteness follows from (3)--(4): outside a sufficiently large real-frequency interval, `|r Xi(2z)|<C(1-r)/2` uniformly for `|Im z|≤B`; the remaining zeros lie in a compact rectangle and are finite by analyticity. On the real axis `X_r(y)→C(1-r)>0`, so in particular it has only finitely many real zeros.

For the total zero set, `X_r` is nonconstant entire of order at most one by the corpus's [`XiC_order`](../../../../../formal/GaloisForLFunctions/RHTower/XiEntireReal.lean). Suppose it had finitely many zeros. The corpus's [finite-zero Hadamard theorem](../../../../../formal/GaloisForLFunctions/RHTower/FiniteZeroHadamardProduct.lean) then gives `X_r(z)=P(z)e^{L(z)}` with `P,L` polynomials. Along the positive real ray `X_r(y)→C(1-r)≠0` and `X_r'(y)→0`; logarithmic differentiation gives `L'(y)=X_r'(y)/X_r(y)-P'(y)/P(y)→0`. As `L'` is a polynomial, it vanishes identically. The nonzero finite limit then forces `P` constant, contradicting `r>0` and nonconstancy of Xi. Thus infinitely many zeros exist. Since every bounded horizontal strip contains only finitely many, their imaginary parts are unbounded; none of this locates a zero in the natural Xi strip.

For `r=0`, `X_0=C` is zero-free. At the physical value `r=1`, the unconditional critical-zero theorem supplies infinitely many **real** zeros; whether any nonreal zeros lie in the natural strip is precisely RH.

## Contacts accumulate at the physical endpoint

**[PROVED HERE ON PAPER]** There are infinitely many disjoint bounded components `I_j=(α_j,β_j)` of the negative set `{y>0 : Xi(2y)<0}`, with `α_j→∞`. The corpus's unconditional simple critical zeros of both crossing orientations give infinitely many sign changes, so such components exist. Write

```text
m_j=min_[α_j,β_j] Xi(2y)<0,
r_j=C/(C-m_j)∈(0,1).                                (5)
```

Because Xi tends to zero on the real axis, `m_j→0` and hence `r_j→1`. On each component, (3) yields the exact contact classification:

```text
r<r_j : X_r>0 throughout [α_j,β_j];
r=r_j : X_r≥0, with an interior zero at every minimizer;
r_j<r<1 : X_r has at least two real zeros in I_j.  (6)
```

At `r=r_j` every interior contact zero has even analytic multiplicity: it is a zero of a nonnegative real-analytic function. The horizontal exponential bound in [`exists_norm_XiC_horizontal_le`](../../../../../formal/GaloisForLFunctions/RHTower/XiHorizontalStripDecay.lean) yields, for every `0<κ<π/2`,

```text
0<1-r_j=|m_j|/(C+|m_j|)≤C_κ exp(-κ α_j).          (7)
```

For any finite selection of these components, `max r_j<r<1` creates at least two real zeros in each. Therefore the number of positive real zeros of `X_r` tends to infinity as `r↑1`, while it is finite for every `r<1`. The contact parameters accumulate exponentially at the physical coupling. No nondegeneracy of the minima is assumed, so “contact” does not assert a quadratic fold.

The contacts also have an unavoidable complex side. **[PROVED HERE ON PAPER]** Choose one minimizer `y_j*∈I_j`. Because `Xi(2z)` is nonconstant real entire and `y_j*` is a real local minimum, its first nonzero Taylor term there has positive even order `2k_j`:

```text
Xi(2z)-m_j=(z-y_j*)^(2k_j) h_j(z),
k_j≥1,                    h_j(y_j*)>0.              (8)
```

Choose a disk around `y_j*` with radius less than `a=1/4`, containing no other zero of `Xi(2z)-m_j`. For `r<r_j`, define the lower target level and its gap by

```text
L(r)=-C(1-r)/r < m_j,
δ_j(r)=m_j-L(r)>0,          δ_j(r)→0 as r↑r_j.      (9)
```

Equation (3) says `X_r(z)=r[Xi(2z)-L(r)]`. On the disk boundary, Rouché's theorem gives exactly `2k_j` zeros of `Xi(2z)-m_j+δ_j(r)` when `r` is sufficiently close below `r_j`; all converge to `y_j*` as `r↑r_j`. None is real: on the real slice near the minimum, `Xi(2y)-m_j≥0`, so adding `δ_j(r)>0` is strictly positive. The zeros occur in conjugate pairs inside `|Im z|<a` (and their even reflections occur near `-y_j*`). Thus for each `j` there is `ε_j>0` such that

```text
r_j-ε_j<r<r_j  ⇒  X_r has nonreal zeros in |Im z|<a. (10)
```

Since `r_j→1`, every interval `(r₀,1)` with `r₀<1` contains such couplings. This kills the stronger conjecture that a one-sided zero-free homotopy through positive stable renewal inputs could imply RH by passage to `r=1`. The physical endpoint may still have all zeros on the critical line: these deformed nonreal clusters collide onto it before reaching `r=1`.

## Architectural consequence and remaining RH gate

The literal source is **renewal-subcritical** at every coupling `0≤r≤1`, but **spectrally critical** only at `r=1`: its modular seam cancels the surviving constant exactly. This is why perturbative small-gain or ordinary zero-count continuity from `r=0` cannot establish RH. Every `r∈(0,1)` has infinitely many nonreal zeros outside bounded horizontal strips, and arbitrarily close to `r=1` some couplings also have nonreal zeros **inside** the natural strip, born on the complex side of an infinite cascade of on-axis contacts. If one scales the seam constant as well, `c_r=rc`, then `D_r=rD` and `X_r=rXi`; the zero set is unchanged, so that scalar deformation carries no zero-location information.

The hard open problem is still source-specific confinement of the physical `r=1` complex zero set to the critical axis. The deformation does not imply an off-line zero of Xi or an RH proof. The strongest positive survivor is the exact classification (3)--(10): a stable positive renewal family with a singular modular seam endpoint, exponentially accumulating contacts, and nearby conjugate off-axis clusters. The source-specific theorem is formalized unconditionally in Lean (certificate `theta-renewal-seam-critical-coupling-formalized.md`); the external novelty audit remains open. No route is retired by this result.

## Log

- 2026-09-28: all claims (1)–(10), the inverse-source cusp, the phase law (3b), the uniform strip decay (4), the zero-set classification, the contact cascade and the Rouché clusters formalized unconditionally in Lean (modules `XiStripInverseDecay`, `EntireConstantShiftZeroCount`, `ThetaSeamCouplingFamily`, `ThetaSeamCouplingZeros`, `ThetaSeamCouplingContacts`; general layer `HTGeometry.RealNonnegativeZeroEvenOrder`); moved to stage 3.
