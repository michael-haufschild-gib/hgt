# Half-density Floquet source and Euler-boundary dichotomy

- **ID:** `deninger-half-density-floquet-euler-boundary-dichotomy`
- **Stage:** 3-formalized
- **Type:** SOURCE CONSTRUCTION / WEIGHT-ONE ENERGY / EXACT BOUNDARY OBSTRUCTION
- **Labels:**
  - `DAC_DENINGER_HALF_DENSITY_FLOQUET_EXACT_SEQUENCE`;
  - `DAC_DENINGER_COFINAL_TATE_FLOQUET_TOMOGRAPHY`;
  - `DAC_DENINGER_ALL_PRIME_FLOQUET_COCHAIN_HODGE_ENERGY`;
  - `DAC_DENINGER_EULER_FLOQUET_STRICT_HODGE_ADMISSION`;
  - `DAC_DENINGER_TATE_FLOQUET_POISSON_LEAKAGE_DICHOTOMY`;
  - `DAC_DENINGER_FLOQUET_HILBERT_POISSON_RESONANCE_QUOTIENT`;
  - `DAC_DENINGER_BOUNDED_FLOQUET_CORRECTION_RESONANCE_NO_GO`.
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Inputs:**
  - `DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION`;
  - `DAC_DENINGER_COFINAL_PRIME_PERIODIZATION_TOMOGRAPHY`;
  - `DeningerMeyerHalfDensityL1Completion.lean` (read-only corpus input).
- **Claim:** within the real-character family, weighting prime periodization by the half-density
  character produces the unique compact Floquet trace with arithmetic weight one. Any infinite
  prime family is algebraically faithful, and the all-prime family gives a continuous,
  positive-definite, source-defined weight-one Hilbert energy on the full Meyer cochain space.
  Ordinary Euler depletion is bounded below for this energy and extends to an isomorphism of its
  Hilbert completion, with an explicit uniform cross-prime Neumann inverse.
  Exact computation then shows why this still does not descend: ordinary Euler depletion makes
  the Floquet trace visible but leaks Poisson boundaries by the nonzero scalar
  $1-p^{-1/2}$; aligning depletion with the Floquet character kills the whole admitted
  $M_\zeta$ sector. The remaining theorem is therefore a genuinely relative
  Gamma/co-Poisson correction, not construction of another positive ambient energy.

## 1. Weighted prime periodization

Let
\[
 H_-=\mathscr S_{\exp}(\mathbb R),\qquad L_p=\log p,\qquad
 (\tau_ph)(t)=h(t+L_p).
\]
For $\alpha\in\mathbb R$, define
\[
 \operatorname{Per}_{p,\alpha}h(t)
 =\sum_{j\in\mathbb Z}p^{\alpha j}h(t+jL_p)
\tag{1}
\]
and the smooth Floquet line
\[
 \mathscr F_{p,\alpha}
 =\{F\in C^\infty(\mathbb R):
       F(t+L_p)=p^{-\alpha}F(t)\}.
\tag{2}
\]
The trivialization
\[
 \mathcal U_\alpha F(t)=e^{\alpha t}F(t)
\tag{3}
\]
identifies `(2)` with $C^\infty(\mathbb R/L_p\mathbb Z)$. All series in `(1)`, including
derivatives, converge absolutely and locally uniformly because $H_-$ decays faster than every
exponential at both ends.

Put
\[
 D_{p,\alpha}=1-p^\alpha\tau_p.
\tag{4}
\]

`[PROVED HERE] [DAC_DENINGER_HALF_DENSITY_FLOQUET_EXACT_SEQUENCE]`

There is a split strict exact sequence of nuclear Fr\'echet spaces
\[
 0\longrightarrow H_-
 \xrightarrow{\ D_{p,\alpha}\ }H_-
 \xrightarrow{\ \operatorname{Per}_{p,\alpha}\ }
 \mathscr F_{p,\alpha}
 \longrightarrow0.
\tag{5}
\]
The kernel identity and Green inverse are
\[
 \ker\operatorname{Per}_{p,\alpha}
 =D_{p,\alpha}H_-,
\tag{6}
\]
\[
 G_{p,\alpha}h(t)
 =\sum_{j\ge0}p^{\alpha j}h(t+jL_p)
 =-\sum_{j<0}p^{\alpha j}h(t+jL_p)
\quad
(h\in\ker\operatorname{Per}_{p,\alpha}).
\tag{7}
\]

### Proof

Index shifting gives
\[
 \operatorname{Per}_{p,\alpha}(\tau_ph)
 =p^{-\alpha}\operatorname{Per}_{p,\alpha}h,
\]
hence $\operatorname{Per}_{p,\alpha}D_{p,\alpha}=0$. If
$D_{p,\alpha}h=0$, then
$h(t+nL_p)=p^{-\alpha n}h(t)$. Faster-than-every-exponential decay at the positive end forces
$h(t)=0$, so $D_{p,\alpha}$ is injective.

If weighted periodization is zero, the two sums in `(7)` agree. Spending one exponential source
weight beyond $|\alpha|$ gives the same geometric-series seminorm estimate as for ordinary
periodization; thus $G_{p,\alpha}$ is continuous and belongs to $H_-$. Direct telescoping gives
$D_{p,\alpha}G_{p,\alpha}h=h$.

For $F\in\mathscr F_{p,\alpha}$ and a compactly supported smooth partition function $\chi$ with
$\sum_j\chi(t+jL_p)=1$, set $s_\chi(F)=\chi F$. Quasi-periodicity gives
\[
 \operatorname{Per}_{p,\alpha}s_\chi(F)
 =F\sum_j\chi(t+jL_p)=F.
\]
This is a continuous section. Closedness, strictness, and nuclearity follow exactly as in the
untwisted case after the trivialization `(3)`.

## 2. Mellin lattice and forced weight

Write
\[
 M_h(s)=\int_{\mathbb R}e^{st}h(t)\,dt.
\]
Fourier coefficients of the periodic trivialization in `(3)` are
\[
 \frac1{L_p}\int_0^{L_p}
   e^{\alpha t}\operatorname{Per}_{p,\alpha}h(t)
   e^{-2\pi i kt/L_p}\,dt
 =
 \frac1{L_p}M_h\!\left(
   \alpha-\frac{2\pi i k}{L_p}
 \right).
\tag{8}
\]
Thus a prime Floquet circle packages a full vertical Mellin lattice on $\Re s=\alpha$.

Let raw logarithmic dilation be
\[
 (T_ah)(t)=h(t-a).
\tag{9}
\]
Then
\[
 \operatorname{Per}_{p,\alpha}(T_ah)(t)
 =\operatorname{Per}_{p,\alpha}h(t-a).
\]
Equip `(2)` with the Hilbert norm
\[
 \|F\|_{p,\alpha}^2
 =\int_0^{L_p}|e^{\alpha t}F(t)|^2\,dt.
\tag{10}
\]
Translation is rotation after trivialization, with scalar $e^{\alpha a}$, so
\[
 \|\operatorname{Per}_{p,\alpha}(T_ah)\|_{p,\alpha}^2
 =e^{2\alpha a}
  \|\operatorname{Per}_{p,\alpha}h\|_{p,\alpha}^2.
\tag{11}
\]
Consequently $\alpha=1/2$ is the unique real Floquet exponent for which `(10)` has arithmetic
weight one. For the centered flow
\[
 V_a=e^{-a/2}T_a,
\tag{12}
\]
the half-density Floquet norm is exactly invariant.

This is the positive escape from the weight-zero obstruction for ordinary compact traces: the
prime orbit must carry the nonunitary half-density local system, not the trivial scalar line.

## 3. Cofinal half-density Floquet tomography

`[PROVED HERE] [DAC_DENINGER_COFINAL_TATE_FLOQUET_TOMOGRAPHY]`

If $Q$ is any infinite set of primes, then
\[
 h\longmapsto
 \bigl(\operatorname{Per}_{q,1/2}h\bigr)_{q\in Q}
\tag{13}
\]
is injective on $H_-$. No finite $Q$ is injective.

Indeed, if `(13)` is zero, `(8)` with $k=1$ gives zeros of the entire function $M_h$ at
\[
 \frac12-\frac{2\pi i}{\log q},\qquad q\in Q.
\]
They converge to $1/2$, so the identity theorem gives $M_h=0$, hence $h=0$. For finite $Q$,
the nonzero space
\[
 \left(\prod_{q\in Q}D_{q,1/2}\right)H_-
\]
lies in the common kernel by `(6)`.

The ordinary product topology is still weaker than the full all-weight Meyer topology. For
$a_0>1/2$ and $0\ne\psi\in C_c^\infty(\mathbb R)$,
\[
 h_n=e^{-a_0n}T_n\psi
\]
converges to zero in every fixed half-density Floquet trace, whose norm scales only as
$e^{n/2}$, but not in the Meyer seminorm with exponential weight $a_0$. Thus half-density Floquet
tomography captures the Hodge weight, not every stronger nuclear source seminorm.

## 4. An unconditional all-prime cochain Hodge energy

`[PROVED HERE] [DAC_DENINGER_ALL_PRIME_FLOQUET_COCHAIN_HODGE_ENERGY]`

Define
\[
 \mathcal E_{\mathrm{Fl}}(h)
 =\sum_p p^{-2}
   \|\operatorname{Per}_{p,1/2}h\|_{p,1/2}^2.
\tag{14}
\]
Then `(14)` is finite and continuous on $H_-$, positive definite, and has exact weight one:
\[
 \mathcal E_{\mathrm{Fl}}(h)=0\Longleftrightarrow h=0,
\qquad
 \mathcal E_{\mathrm{Fl}}(T_ah)=e^a\mathcal E_{\mathrm{Fl}}(h),
\qquad
 \mathcal E_{\mathrm{Fl}}(V_ah)=\mathcal E_{\mathrm{Fl}}(h).
\tag{15}
\]

### Proof

Put $u(t)=e^{t/2}h(t)$. The trivialized Floquet trace is the ordinary periodization
\[
 e^{t/2}\operatorname{Per}_{p,1/2}h(t)
 =\sum_{j\in\mathbb Z}u(t+jL_p).
\tag{16}
\]
Since $L_p\ge\log2$, weighted Cauchy--Schwarz followed by unfolding a fundamental interval gives,
for fixed $c>0$,
\[
 \int_0^{L_p}
 \left|\sum_j u(t+jL_p)\right|^2dt
 \le C_c\int_{\mathbb R}e^{c|t|}|u(t)|^2dt,
\tag{17}
\]
with $C_c$ independent of $p$. The right side is a continuous Meyer seminorm. Since
$\sum_pp^{-2}<\infty$, `(17)` proves convergence and continuity of `(14)`.

Positive definiteness follows from the injectivity in `(13)`. Equation `(11)` with
$\alpha=1/2$ proves the two covariance identities in `(15)`.

Thus Route L now has an explicit source-defined positive weight-one Hilbert energy on the full
Meyer **cochain** space. Positivity itself is no longer absent at this level.

## 5. Exact Euler-boundary dichotomy

Let ordinary Euler depletion be
\[
 \Delta_p=1-\tau_p,
\qquad
 Z^{(p)}=\Delta_pZ.
\tag{18}
\]
Index shifting gives the exact comparison
\[
 \operatorname{Per}_{p,1/2}\Delta_p
 =(1-p^{-1/2})\operatorname{Per}_{p,1/2}.
\tag{19}
\]
The scalar is nonzero.

The same law has a stronger cross-prime form. Write
\[
 \widetilde{\operatorname{Per}}_q h(t)
 =e^{t/2}\operatorname{Per}_{q,1/2}h(t)
\]
for the periodic trivialization, and let
\[
 (R_{p,q}F)(t)=F(t+L_p)
\]
be rotation of the $q$-circle by $L_p$. Then
\[
 \widetilde{\operatorname{Per}}_q(\Delta_ph)
 =
 (I-p^{-1/2}R_{p,q})
 \widetilde{\operatorname{Per}}_qh.
\tag{19a}
\]
Because $R_{p,q}$ is unitary and $p^{-1/2}<1$,
\[
 (I-p^{-1/2}R_{p,q})^{-1}
 =\sum_{n\ge0}p^{-n/2}R_{p,q}^n,
\qquad
 \left\|(I-p^{-1/2}R_{p,q})^{-1}\right\|
 \le\frac1{1-p^{-1/2}}.
\tag{19b}
\]
In particular,
\[
 (1-p^{-1/2})\|F\|_2
 \le\|(I-p^{-1/2}R_{p,q})F\|_2
 \le(1+p^{-1/2})\|F\|_2.
\tag{19c}
\]

`[PROVED HERE] [DAC_DENINGER_EULER_FLOQUET_STRICT_HODGE_ADMISSION]`

Summing `(19c)` with the weights in `(14)` gives
\[
 (1-p^{-1/2})^2\mathcal E_{\mathrm{Fl}}(h)
 \le\mathcal E_{\mathrm{Fl}}(\Delta_ph)
 \le(1+p^{-1/2})^2\mathcal E_{\mathrm{Fl}}(h).
\tag{19d}
\]
Thus ordinary Euler depletion is a bounded-below topological embedding for the explicit Hodge
energy, with closed range and a bounded inverse on that range. Auxiliary-prime compatibility is
already exact at cochain Hilbert level. The same estimate carries
$Z(H_\cap)$ to $\Delta_pZ(H_\cap)$ without changing whether its Hilbert closure is exact.

Let
\[
 d_{\mathrm{Fl}}(g,Z(H_\cap))
 =\inf_{f\in H_\cap}
   \mathcal E_{\mathrm{Fl}}(g-Zf)^{1/2}
\]
and, on the Euler-depleted cochain kernel, define
\[
 r_{\mathrm{Fl},p}(h)
 =\inf_{f\in H_\cap}
   \mathcal E_{\mathrm{Fl}}(h-\Delta_pZf)^{1/2}.
\tag{19e}
\]
Then `(19d)` gives
\[
 (1-p^{-1/2})d_{\mathrm{Fl}}(g,Z(H_\cap))
 \le r_{\mathrm{Fl},p}(\Delta_pg)
 \le(1+p^{-1/2})d_{\mathrm{Fl}}(g,Z(H_\cap)).
\tag{19f}
\]
In particular,
\[
 \ker r_{\mathrm{Fl},p}
 =\Delta_p\!\left(
   H_-\cap\overline{Z(H_\cap)}^{\,\mathcal E_{\mathrm{Fl}}}
 \right).
\tag{19g}
\]
The relative quadratic seminorm `(19e)` is centered-flow invariant and its radical is
prime-independent under the canonical Euler identifications. No faithfulness is claimed:
proving that the closure in `(19g)` meets $H_-$ only in the actual Poisson range is precisely the
remaining closed-boundary theorem.

`[PROVED HERE] [DAC_DENINGER_TATE_FLOQUET_POISSON_LEAKAGE_DICHOTOMY]`

There are exactly two uncorrected single-prime choices:

1. **Use ordinary Euler depletion.** The half-density Floquet trace is visible on
   $\Delta_pH_-$, but every Poisson boundary satisfies
   \[
   \operatorname{Per}_{p,1/2}(\Delta_pZf)
   =(1-p^{-1/2})\operatorname{Per}_{p,1/2}(Zf).
   \tag{20}
   \]
   This leakage is genuinely nonzero for suitable $f\in H_\cap$; for example its zeroth
   Fourier coefficient is the Mellin value at $1/2$, where $\zeta(1/2)\ne0$, and source Mellin
   evaluation is nontrivial.
2. **Align depletion with the Floquet character.** Put
   \[
   D_{p,1/2}=1-p^{1/2}\tau_p,\qquad Z_{\mathrm{Fl}}^{(p)}=D_{p,1/2}Z.
   \tag{21}
   \]
   Sequence `(5)` gives the same split strict admission
   \[
   0\to M_\zeta
   \longrightarrow H_-/Z_{\mathrm{Fl}}^{(p)}(H_\cap)
   \longrightarrow\mathscr F_{p,1/2}\to0,
   \tag{22}
   \]
   but the admitted copy of $M_\zeta$ is exactly the kernel of the Floquet trace. Hence every
   form factoring through that trace vanishes on the entire middle sector.

### Proof

Equation `(19)` is the same-prime case of `(19a)`. Formula `(19a)` follows by writing
$e^{t/2}\operatorname{Per}_{q,1/2}(\tau_ph)(t)$ as
$p^{-1/2}\widetilde{\operatorname{Per}}_qh(t+L_p)$. The Neumann series proves `(19b)`, and the
triangle and reverse-triangle inequalities prove `(19c)`--`(19d)`. Statement 1 follows by
composition with $Z$. For statement 2, replace the untwisted difference and periodization in the Euler-depleted
extension proof by `(4)` and `(1)`. Injectivity of $D_{p,1/2}$ gives exact boundary
conservativity, and `(6)` identifies the admitted sector with the trace kernel.

Therefore no uncorrected prime Floquet trace can simultaneously:

- see the actual $M_\zeta$ sector;
- annihilate its Poisson boundaries;
- carry positive Tate-weight-one energy.

The all-prime energy `(14)` solves positivity, covariance, and cochain faithfulness, but its
radical is zero, so it assigns positive energy to nonzero Poisson boundaries and does not descend.
The canonical quotient distance `(19e)` does descend, but replaces the boundary by its Floquet
Hilbert closure `(19g)`; proving that closure exact is a separate source theorem and cannot be
inferred from `(14)`.

## 6. Exact Floquet Hilbert quotient

The closure in `(19g)` can be classified. Define the locally finite arithmetic lattice measure
\[
 \mu_{\mathrm{Fl}}
 =\sum_p\frac{p^{-2}}{L_p}
   \sum_{k\in\mathbb Z}\delta_{2\pi k/L_p},
\tag{23}
\]
where coincident atoms at $0$ are combined. It has at most linear mass growth on bounded
frequency intervals. Parseval applied to `(16)` gives
\[
 \mathcal E_{\mathrm{Fl}}(h)
 =\int_{\mathbb R}
   \left|M_h\!\left(\frac12-i\xi\right)\right|^2
   d\mu_{\mathrm{Fl}}(\xi).
\tag{24}
\]
Let $\mathcal H_{\mathrm{Fl}}$ be the Hilbert completion of $H_-$ for this norm and put
\[
 \Sigma_{\mathrm{res}}
 =\left\{\xi\in\operatorname{supp}\mu_{\mathrm{Fl}}:
   \zeta\!\left(\frac12-i\xi\right)=0\right\}.
\tag{25}
\]

`[PROVED HERE] [DAC_DENINGER_FLOQUET_HILBERT_POISSON_RESONANCE_QUOTIENT]`

Mellin sampling extends to a unitary identification
\[
 \mathcal H_{\mathrm{Fl}}
 \cong L^2(\mu_{\mathrm{Fl}}).
\tag{26}
\]
Under `(26)`, the closed Poisson-boundary space is
\[
 \overline{Z(H_\cap)}^{\,\mathcal E_{\mathrm{Fl}}}
 =
 \left\{a\in L^2(\mu_{\mathrm{Fl}}):
   a(\xi)=0\text{ for }\xi\in\Sigma_{\mathrm{res}}\right\}.
\tag{27}
\]
Consequently
\[
 \mathcal H_{\mathrm{Fl}}\big/
 \overline{Z(H_\cap)}
 \cong L^2(\mu_{\mathrm{Fl}}|_{\Sigma_{\mathrm{res}}}).
\tag{28}
\]
The Euler-depleted relative completion defined by `(19e)` has the same quotient with an equivalent
norm, because every Euler multiplier in `(19a)` is boundedly invertible.

### Proof

The support of `(23)` has no repeated nonzero node: equality
$k/\log p=\ell/\log q$ for distinct primes and nonzero integers would give
$p^\ell=q^k$. Local finiteness with multiplicity follows because each prime contributes
$O(1+TL_p)$ nodes to $[-T,T]$, while
\[
 \sum_pp^{-2}(L_p^{-1}+T)<\infty.
\]

The sampled Mellin transforms of $C_c^\infty(\mathbb R)\subset H_-$ are dense in
$L^2(\mu_{\mathrm{Fl}})$. Indeed, an orthogonal vector defines a tempered atomic distribution on
the frequency line; if it annihilates every Fourier transform of a compactly supported smooth
function, inverse Fourier injectivity makes that distribution zero. This proves `(26)`.

For $f\in H_\cap$, Poisson--Mellin factorization gives
\[
 M_{Zf}\!\left(\frac12-i\xi\right)
 =\zeta\!\left(\frac12-i\xi\right)
  M_f\!\left(\frac12-i\xi\right).
\tag{29}
\]
The samples of $M_f$ with $f\in H_\cap$ are dense in
$L^2(|\zeta(1/2-i\xi)|^2d\mu_{\mathrm{Fl}})$. To see this without assuming spectral synthesis,
use even smooth $f$ supported away from zero. Writing $g(t)=f(e^t)$, the endpoint condition
$f(0)=0$ is automatic, while $\widehat f(0)=0$ is the single constraint
$\int e^tg(t)\,dt=0$. Put $\phi(t)=e^{t/2}g(t)$; the excluded functional is then
$\phi\mapsto\int e^{t/2}\phi(t)\,dt$.

If $a$ is orthogonal to all sampled moment-zero tests, Cauchy--Schwarz against the polynomially
growing measure $|\zeta(1/2-i\xi)|^2\mu_{\mathrm{Fl}}$ makes
$a|\zeta|^2\mu_{\mathrm{Fl}}$ a tempered atomic distribution. Its inverse Fourier transform
annihilates the kernel of the excluded functional, hence equals $ce^{t/2}$ as a distribution.
But $e^{t/2}$ is not tempered, so $c=0$ and then $a=0$ in the weighted space. This proves the
claimed density.

Multiplication by $\zeta(1/2-i\xi)$ maps this weighted $L^2$ space isometrically onto the closed
subspace of $L^2(\mu_{\mathrm{Fl}})$ vanishing at its zero atoms. Density and `(29)` prove `(27)`;
orthogonal quotient gives `(28)`.

This is an exact negative classification, not a divisor-built carrier. The nodes in `(25)` are
fixed by prime lengths before zeros are read. Uncorrected Floquet Hilbert descent retains only
those critical zeros which happen to resonate exactly with a prime Mellin lattice, and only their
zero-order value. Nonresonant critical modes, every off-line mode, and higher jets disappear in
the closure. The Gamma/co-Poisson correction must therefore change the boundary relation before
Hilbert closure; completing `(14)` first cannot recover the full Meyer quotient.

## 7. Bounded-correction no-go

The resonance classification also rules out a broad class of apparent fixes.

`[PROVED HERE] [DAC_DENINGER_BOUNDED_FLOQUET_CORRECTION_RESONANCE_NO_GO]`

Let $J:H_-\to\mathcal H_{\mathrm{Fl}}$ be the completion map from `(26)`, let $Y$ be a Hilbert
space, and suppose $A:\mathcal H_{\mathrm{Fl}}\to Y$ is bounded and
\[
 AJZf=0\qquad(f\in H_\cap).
\tag{30}
\]
Then $A$ has a unique bounded factorization
\[
 \mathcal H_{\mathrm{Fl}}
 \longrightarrow L^2(\mu_{\mathrm{Fl}}|_{\Sigma_{\mathrm{res}}})
 \xrightarrow{\ \overline A\ }Y.
\tag{31}
\]
The same statement holds on every depleted sector $\Delta_pH_-$: if a corrected trace is bounded
for $\mathcal E_{\mathrm{Fl}}$ and kills $\Delta_pZ(H_\cap)$, it factors through the same
resonance-only quotient after the invertible Euler multiplier `(19a)`.

Indeed, boundedness and `(30)` force $A$ to vanish on the closure `(27)`, so the Hilbert quotient
universal property and `(28)` give `(31)`. On the depleted sector, `(19a)` extends $\Delta_p$ to
a boundedly invertible operator on $\mathcal H_{\mathrm{Fl}}$ and transports the two closed
boundary spaces. This proves the second assertion.

Consequently a correction built as a bounded operator on the raw Floquet Hilbert completion cannot
recover any nonresonant mode or higher jet. The missing Gamma/co-Poisson descent must either be
continuous only for the finer nuclear Meyer topology and singular for
$\mathcal E_{\mathrm{Fl}}$, or enlarge the target by genuinely new source data before completion.
This is a theorem about the required analytic type of the missing object, not a design preference.

## 8. Conjecture loop and frontier movement

1. **Conjecture: compact prime energy necessarily has weight zero.**
   **Refined, not universally true.** It is true on the trivial scalar orbit. Half-density Floquet
   monodromy gives the unique weight-one compact trace.
2. **Conjecture: the weight-one Floquet trace closes Route L.**
   **Failed by `(20)`.** Correct weight creates a visible trace but not boundary descent.
3. **Conjecture: use the matching twisted Euler difference.**
   **Failed by `(22)`.** Boundary descent returns, but the whole admitted middle sector becomes
   trace-zero.
4. **Conjecture: all-prime Floquet assembly at least supplies a genuine positive cochain
   geometry.** **Proved by `(14)`--`(17)`.**
5. **Conjecture: Euler depletion may destroy that Hilbert geometry across other primes.**
   **Failed by `(19a)`--`(19d)`.** Every cross-prime Euler multiplier has a uniform Neumann
   inverse; cochain Hodge admission and auxiliary-prime compatibility are strict.
6. **Conjecture: quotient distance might retain the full Meyer cohomology.**
   **Failed exactly by `(23)`--`(28)`.** It retains only exact critical-line Floquet resonances;
   ordinary Hilbert closure erases all other modes and all higher jets.
7. **Conjecture: a bounded Hilbert correction can repair that loss.**
   **Failed by `(30)`--`(31)`.** Every such correction factors through the same resonance quotient.
   The correction must be pre-Hilbert and nuclear-topology singular, or introduce another source
   channel.

Successor results narrow the first hard Route-L object further. The cofinal lift of the existing
secondary two-collar regulator has exact radical equal to the reflected Calderón graph. Canonical
Möbius inversion is then a pointwise right inverse on every Meyer cochain and identifies the
literal Poisson range exactly by $H_\cap$ regularity of that preimage. The remaining object is a
source-derived Gamma/co-Poisson Green--Stokes realization of the canonical Möbius preimage's
singular endpoint/Fourier regularity defect, with exact boundary kernel and a joint all-prime
square sum retaining the weight-one covariance of `(14)`.

This is more concrete than “find a Hodge form”:
ambient positive energy, its Tate normalization, its cofinal faithfulness, and its exact boundary
error are now explicit. The quadratic relative seminorm and its exact closure radical are also
explicit by `(19e)`--`(19g)`.

## 9. Hostile audit

- **No RH-equivalent premise.** All identities are on source cochains and use only exponential
  decay, prime lengths, and the literal Poisson boundary.
- **No zero-selected sampling.** Floquet lattices are fixed by ordinary primes before any Xi
  divisor is read.
- **No positivity theatre.** `(14)` is positive definite and continuous, but is explicitly not
  claimed to descend.
- **No hidden boundary axiom.** Leakage `(20)` is computed and shown nonzero; matching it away
  would be the missing scientific theorem.
- **No unexamined quotient closure.** Equations `(23)`--`(28)` classify it exactly and show why
  completion before correction loses the nonresonant Meyer spectrum.
- **No bounded-correction escape.** Equations `(30)`--`(31)` show that every raw-Hilbert-bounded
  repair inherits the same resonance-only loss.
- **No arbitrary Hilbert copy.** Norm `(10)` is forced by Floquet trivialization, exponent
  $1/2$ is forced by weight one, and prime sum uses the convergent ordinary-prime mass $p^{-2}$.
- **No Lean claim.** Lean corpus was inspected read-only during refactor. No Lean file or build is
  part of this result.

## 10. Novelty boundary

Weighted periodization, Floquet trivialization, Mellin lattices, and weighted
Cauchy--Schwarz are standard separately. Repository search found general Floquet and periodization
libraries but no Deninger/Meyer theorem combining `(5)`, the forced half-density covariance
`(11)`, cofinal prime tomography `(13)`, positive all-prime energy `(14)`, strict cross-prime
  Euler admission and relative radical `(19a)`--`(19g)`, and the exact
Euler/Poisson leakage dichotomy `(19)`--`(22)`, or the resonance quotient `(23)`--`(28)`.
Targeted primary-source search found Jackson--Mellin
and $q$-Mellin periodization, but not this strict source extension or its Route-L boundary
classification. Novelty is claimed only for that arithmetic-source composition and exact
frontier movement.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  arXiv:math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*, arXiv:1807.06400.
- Shai Haran, Nobushige Kurokawa, Masato Wakayama,
  *Jackson--Mellin's transform of modular forms and q-zeta functions*, Kyushu J. Math. 61 (2007).
- `DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION`.
- `DAC_DENINGER_COFINAL_PRIME_PERIODIZATION_TOMOGRAPHY`.

## Lean status

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerFloquetExactSequence.lean`,
`DeningerFloquetTomography.lean`, `DeningerHalfDensityFloquetEnergy.lean`,
`DeningerEulerFloquetAdmission.lean`, on the all-prime energy layer
(`DeningerPeriodizationFundamentalBound.lean`, `DeningerAllPrimeFloquetEnergy.lean`,
`DeningerAllPrimeFloquetRadical.lean`, `DeningerFloquetEnergyContinuity.lean`) and the reusable
`formal/GaloisForLFunctions/HTGeometry/PeriodicRotationEnergy.lean`.  Axiom audit for every
declaration: `propext, Classical.choice, Quot.sound`.

### Done

- **§1, `(1)`--`(7)`: the twisted Floquet sequence.**  The trivialization `U_α F(t) = e^{αt}F(t)`
  is an automorphism of the source, and `deningerFloquetPeriodizationSum_trivialize` proves
  `e^{αt}Per_{α,L}h(t) = Per_L(U_α h)(t)` while `deningerExpMulLM_floquetDefect` proves
  `U_α D_{α,L} = Δ_L U_α`.  Hence the whole twisted sequence is the untwisted one conjugated:
  **`deningerFloquetDefect_injective`** is `D_{α,L}` injective,
  **`deningerFloquetPeriodization_range_eq_kernel`** is `(6)` (`ker Per_{α,L} = D_{α,L}H_-`), and
  **`deningerFloquetPeriodizationMap_surjective`** is surjectivity onto the Floquet line.  The line
  itself is `DeningerFloquetLine`, defined as the trivialization preimage of `C^∞(ℝ/Lℤ)`, with
  `mem_deningerFloquetLine_iff` recovering the card's quasi-periodicity `(2)`.
- **§3, `(13)`: cofinal Floquet tomography.**  `deningerCofinalFloquetTomography` — for any infinite
  prime family the twisted traces are jointly injective — and
  `deningerFiniteFloquetTomography_kernel_nontrivial` — no finite family is, the twisted depletion
  of the source witness being a nonzero common kernel vector.
- **§4, `(14)`--`(15)`: the all-prime cochain Hodge energy.**  After the trivialization the
  half-density Floquet trace is the ordinary periodization of `Uh`, so
  **`deningerHalfDensityFloquetEnergy h = deningerFloquetEnergy (U h)`**.  It is finite
  (`deningerHalfDensityFloquetEnergy_le`, on the period-uniform bound
  `deningerPeriodizationSum_norm_le_period` and `∑_q (log q)/q² < ∞`), continuous
  (**`deningerHalfDensityFloquetEnergy_continuous`**), positive definite
  (**`deningerHalfDensityFloquetEnergy_eq_zero_iff`**, from cofinal tomography), of arithmetic
  weight one (**`deningerHalfDensityFloquetEnergy_translate`**: `E_Fl(T_a h) = e^a E_Fl(h)`) and
  exactly centered-flow invariant (**`deningerHalfDensityFloquetEnergy_centeredFlow`**).  This is
  the positive escape from the weight-zero obstruction, formalized.
- **§5, `(19)`--`(19d)`: the Euler comparison and strict Hodge admission.**
  `deningerHalfDensityLift_defect` shows the trivialized Euler defect is the rotation multiplier
  `1 - e^{-M/2}τ_M`; **`deningerHalfDensityTrace_defect`** is `(19a)` and
  **`deningerHalfDensityTrace_defect_same`** is `(19)`, the same-prime scalar `1 - p^{-1/2}`.  The
  two-sided estimate `(19c)`--`(19d)` is
  **`deningerHalfDensityFloquetEnergy_defect_bounds`**, proved without any inner-product structure:
  `HTGeometry/PeriodicRotationEnergy.lean` shows rotation preserves the energy of a periodic
  function over one period (`intervalIntegral_normSq_rotate`) and bounds the cross term by the
  arithmetic-geometric inequality, so the triangle and reverse-triangle inequalities squared give
  `(1-c)²∫‖F‖² ≤ ∫‖F - cF(·+M)‖² ≤ (1+c)²∫‖F‖²`.  `(20)` is `(19)` composed with `Z`, and the
  content of `(22)` — that the admitted sector is exactly the Floquet trace kernel — is
  `deningerFloquetPeriodization_range_eq_kernel` at `α = 1/2`.

- **§6, `(24)`: the arithmetic lattice form of the energy.**
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerFloquetParseval.lean`.  The circle periodization is
  the unit-cell periodization of the rescaled cochain
  (`deningerPeriodizationSum_eq_l1Periodization`), so the corpus's
  `HTGeometry/L1PeriodizationFourier.lean` coefficient theorem gives
  **`deningerFourierCoeffOn_periodization`**: the `m`-th Fourier coefficient of `Per_L h` on
  `[0,L]` is `L^{-1}𝓕h(m/L)`.  Parseval on the interval (`tsum_sq_fourierCoeffOn`, applicable
  because the period-uniform bound makes the trace `MemLp 2` on the cell) then gives
  **`deningerPeriodization_intervalIntegral_normSq`**:
  `∫_0^L‖Per_L h‖² = L^{-1}∑_{m∈ℤ}‖𝓕h(m/L)‖²`, and summing over primes gives
  **`deningerHalfDensityFloquetEnergy_eq_tsum`** — this is `(24)`, the energy written on the
  arithmetic frequency lattice, with the weights `p^{-2}/L_p` of `(23)` appearing explicitly.

### Not yet formalized

- §6, `(23)` as an actual `Measure` and `(26)`--`(28)`: packaging the lattice weights as
  `μ_Fl`, the unitary identification `H_Fl ≅ L²(μ_Fl)` and the classification of the closed
  Poisson-boundary space.  The identification needs a density argument for sampled Mellin
  transforms in `L²(μ_Fl)`, and `(27)` needs the Poisson--Mellin factorization
  `M_{Zf} = ζ·M_f`, which the corpus does not yet carry.  `(24)` — the analytic content that
  makes those statements meaningful — is proved.
- §7, the bounded-correction no-go, which is stated relative to that quotient.

## Gates

- [x] 0 → 1 in-progress: half-density Floquet source and boundary falsifiers fixed
- [x] 1 → 2 fully-proven: dependency-closed proofs `(5)`--`(29)`
- [x] 2 → 3 formalized: §1 `(1)`--`(7)`, §3 `(13)`, §4 `(14)`--`(15)`, §5 `(19)`--`(19d)`, `(20)`,
  `(22)`, §6's `(23)`--`(28)` and §7 all proved unconditionally (see *Lean status*)
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-12 — Formalized `(24)`: the Fourier coefficient of the prime-circle trace is a
  Fourier-transform sample, and Parseval turns the circle energy into the arithmetic frequency
  lattice sum.
- 2026-08-12 — Formalized the twisted Floquet sequence by conjugation, cofinal Floquet tomography,
  the all-prime half-density cochain Hodge energy with its positivity, weight-one covariance and
  continuity, and the two-sided Euler comparison.  §6's Hilbert quotient remains.

- 2026-08-08 — Constructed strict half-density Floquet source, proved its forced weight-one
  covariance, cofinal tomography, continuous positive all-prime cochain energy, and exact
  ordinary-versus-twisted Euler boundary dichotomy. Proved ordinary Euler depletion is uniformly
  invertible on every cross-prime Floquet fiber and strict for the all-prime Hodge energy.
  Classified its closed Poisson quotient as the exact critical-line prime-lattice resonance
  subspace. Isolated joint corrected Floquet trace before Hilbert closure as concrete Route-L
  relative-Hodge frontier.

### §6 `(23)` as a measure and `(26)` the unitary identification `[NEW]`

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerFloquetLatticeMeasure.lean`,
`DeningerFloquetMeasureEnergy.lean`, `DeningerFloquetAtomicMeasure.lean`,
`DeningerSourceModulation.lean`, `DeningerFloquetGaussianAtom.lean`, `DeningerFloquetHilbert.lean`.
Axiom audit for every declaration: `propext, Classical.choice, Quot.sound`.

- **`(23)` as an actual `Measure`.**  `deningerFloquetMeasure` is
  `∑_q (q^{-2}/log q) ∑_{m ∈ ℤ} δ_{m/log q}`, built as an iterated `Measure.sum` of scaled Dirac
  masses; `lintegral_deningerFloquetMeasure` turns integration against it into the arithmetic
  double sum.  Its three structural properties are proved:
  `deningerFloquetNode_eq_iff` — **no nonzero node is shared by two primes**, because a
  coincidence `m/log p = n/log q` is a nontrivial rational relation between two prime logarithms;
  `deningerFloquetMeasure_compl_support` — the measure lives on the countable node set;
  `deningerFloquetMeasure_Icc_le` — **at most linear mass growth**, `μ_Fl[-T,T] ≤ ∑_q q^{-2}(2T +
  3/log q)`, whence `IsFiniteMeasureOnCompacts`.
- **`(24)` against the measure.**  `lintegral_deningerFloquetSample_normSq` :
  `∫ ‖𝓕(e^{t/2}h)‖² dμ_Fl = E_Fl(h)`.  The Fourier sample replaces the circle trace by
  `deningerFourierSample_hasSum`, the `HasSum` form of the prime-circle Parseval identity.
- **The Gaussian atom.**  `deningerModulate` — multiplication by the unimodular character
  `e^{2πict}` preserves the source, at no cost in exponential weight, so the source contains the
  modulated Gaussians.  `deningerFloquetAtom ξ₀ σ` is the cochain whose half-density
  trivialization is `√σ e^{2πiξ₀t}e^{-πσt²}`, and `deningerFloquetSample_atom` computes its
  Mellin sample exactly: `e^{-π(ξ-ξ₀)²/σ}`.  This is the analytic input that separates the atoms.
- **`(26)`.**  `deningerFloquetSample_memLp` — the sample is square integrable for `μ_Fl`;
  `deningerFloquetSample_integral_normSq` — **the sampling map is isometric**,
  `∫‖𝓕(e^{t/2}h)‖²dμ_Fl = E_Fl(h)`; `deningerFloquetLp_span_topologicalClosure` — **its range
  spans a dense subspace of `L²(μ_Fl)`**.  Density is proved without tempered distributions: the
  Gaussian atom concentrates at a node as `σ → 0`, dominated by the `σ = 1` atom, so a vector
  orthogonal to every sample has zero integral against every node indicator; every node is an atom
  of positive finite mass (`deningerFloquetMeasure_singleton_pos`) and the complement of the node
  set is null, so the vector vanishes almost everywhere.  Isometry plus dense range is exactly the
  statement that the Hilbert completion of the source for `E_Fl` is `L²(μ_Fl)`.

Still open on this card: `(27)`, `(28)` and §7.

### §6 `(27)`--`(28)` and §7 `[NEW]` — the card is fully formalized

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerFloquetPoissonSample.lean`,
`DeningerFloquetPoissonFlow.lean`, `DeningerFloquetPoissonClosure.lean`,
`DeningerFloquetPoissonCompleteness.lean`, `DeningerFloquetBoundedCorrection.lean`,
`DeningerFloquetDepletedCorrection.lean`, and the reusable
`formal/GaloisForLFunctions/HTGeometry/OrthogonalClosureCriterion.lean`.
Axiom audit for every declaration: `propext, Classical.choice, Quot.sound`.

- **`(29)` on the sampling map.**  `deningerFloquetSample_eq_strongLogMellin` — the Mellin sample
  is the two-sided Mellin transform evaluated at `s = 1/2 - 2πiξ`, because
  `e^{(1/2-2πiξ)t} = e^{t/2}e^{-2πiξt}`.  Composing with the corpus's Poisson--Mellin
  factorization gives **`deningerFloquetSample_poissonSource`**:
  `𝓕(e^{t/2}Zf)(ξ) = ζ(1/2-2πiξ)·M f(1/2-2πiξ)`.  Hence
  `deningerFloquetSample_poissonSource_eq_zero`: every Poisson boundary has vanishing sample at
  every *resonant node* `deningerFloquetResonance = {ξ ∈ supp μ_Fl : ζ(1/2-2πiξ) = 0}`.
- **`(27)`.**  `deningerFloquetBoundary` is the span of the Poisson-boundary samples and
  `deningerFloquetResonanceSpan` the span of the resonant node indicators.  One inclusion,
  `deningerFloquetBoundary_le`, is the factorization above.  The converse is
  **`deningerFloquetFlow_orthogonal_inf_eq_bot`**: scaling a Meyer test function by `e^{-c}`
  multiplies its critical-line Mellin sample by `e^{c/2}e^{-2πicξ}`
  (`mellin_deningerMeyerCapFlow`, `deningerFloquetSample_capFlow`), so a vector orthogonal to all
  Poisson boundaries has vanishing Fourier coefficient at *every* frequency against the fixed
  weight `ζ·M`; averaging those relations against a Gaussian in the scaling parameter and swapping
  the order of integration produces a Gaussian concentrating at a single node
  (`deningerGaussianCharacter_integral`), and the node is an atom, so the vector vanishes there
  whenever `ζ` does not.  The corpus's explicit Poisson test function has Mellin transform
  vanishing only at `s = 1`, hence nowhere on the critical line
  (`deningerFloquetProfile_ne_zero`), which is what makes the weight usable.  With the general
  Hilbert criterion `submodule_topologicalClosure_eq_of_orthogonal_inf_eq_bot` this gives
  **`deningerFloquetBoundary_topologicalClosure`**: the closed Poisson-boundary space is exactly
  the annihilator of the resonant nodes.
- **`(28)`.**  `deningerFloquetBoundary_closure_orthogonal`: the orthogonal complement of the
  closed boundary is the closed span of the resonant node indicators — the exact critical-line
  prime-lattice resonance subspace, and nothing else.
- **§7.**  `deningerFloquetBoundedCorrection_vanishing` — a bounded operator annihilating every
  Poisson boundary annihilates the whole closed boundary space;
  **`deningerFloquetBoundedCorrection_factors`** — it therefore equals its composition with the
  orthogonal projection onto the resonance subspace, i.e. it factors through the resonance-only
  quotient; **`deningerFloquetBoundedCorrection_unique`** — the factorization is unique, since such
  an operator is determined by its values on the resonant node indicators.
- **§7 on the depleted sector.**  `deningerMeyerCapDepletion` is `1 - τ_L` on Meyer's space;
  `mellin_deningerMeyerCapDepletion` shows it multiplies the Mellin transform by `1 - e^{-Ls}`,
  which has modulus bounded away from `1` on the critical line for `L > 0`, hence never vanishes
  (`deningerCriticalLine_depletionFactor_ne_zero`).  The scaled depleted test functions therefore
  satisfy the same hypotheses, so **`deningerFloquetDepletedBoundary_topologicalClosure`** — the
  depleted boundaries have the *same* closure — and
  **`deningerFloquetDepletedCorrection_factors`** — the no-go holds verbatim on every depleted
  sector.

Nothing on this card remains unformalized.
