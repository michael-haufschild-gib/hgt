# Cofinal prime-periodization tomography and its strict Hodge obstruction

- **ID:** `deninger-cofinal-prime-periodization-tomography-instability`
- **Stage:** 2-fully-proven
- **Type:** SOURCE TOMOGRAPHY / TOPOLOGICAL NO-GO / POSITIVE CLASSIFICATION
- **Labels:**
  - `DAC_DENINGER_COFINAL_PRIME_PERIODIZATION_TOMOGRAPHY`;
  - `DAC_DENINGER_COFINAL_PERIODIZATION_NONSTRICTNESS`;
  - `DAC_DENINGER_COMPACT_ORBIT_WEIGHT_ONE_NO_GO`;
  - `DAC_DENINGER_EULER_DEPLETED_HALF_DENSITY_RELATIVE_DEFECT`.
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Input:** `DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION`
- **Claim:** cofinally many prime circles determine every all-weight Meyer cochain, and hence give
  an algebraically conservative cross-prime model of the Euler-depleted Meyer quotient. No finite
  prime family does. However, the cofinal tomography has nonclosed range in the ordinary product
  topology, and every rotation-invariant compact-orbit energy has flow weight zero rather than
  Tate weight one. Thus the remaining Route-L Hodge object must contain a noncompact relative
  Tate defect before compact periodization.

## 1. Setup

Let
\[
 H_-=\mathscr S_{\exp}(\mathbb R)
\]
with its all-derivative, all-exponential-weight nuclear Fr\'echet topology. For every prime $q$
put
\[
 L_q=\log q,\qquad
 (T_a h)(t)=h(t-a),\qquad
 \Delta_q=1-T_{-L_q},
\tag{1}
\]
so that $\Delta_qh(t)=h(t)-h(t+L_q)$. Define
\[
 \operatorname{Per}_q h(\bar t)
 =\sum_{j\in\mathbb Z}h(t+jL_q).
\tag{2}
\]
For a set $Q$ of primes, write
\[
 \mathcal P_Q:H_-\longrightarrow
 \prod_{q\in Q}C^\infty(\mathbb R/L_q\mathbb Z),
 \qquad
 \mathcal P_Qh=(\operatorname{Per}_qh)_{q\in Q}.
\tag{3}
\]
The target has the ordinary countable product Fr\'echet topology.

For the Fourier transform
\[
 \widehat h(z)=\int_{\mathbb R}h(t)e^{-izt}\,dt,
\tag{4}
\]
two-ended faster-than-exponential decay makes $\widehat h$ entire. Unfolding `(2)` gives the exact
Fourier-coefficient identity
\[
 \frac1{L_q}\int_0^{L_q}
   \operatorname{Per}_q h(t)e^{-2\pi i kt/L_q}\,dt
 =\frac1{L_q}\widehat h\!\left(\frac{2\pi k}{L_q}\right)
 \qquad(k\in\mathbb Z).
\tag{5}
\]

## 2. Cofinal prime tomography

`[PROVED HERE] [DAC_DENINGER_COFINAL_PRIME_PERIODIZATION_TOMOGRAPHY]`

If $Q$ is any infinite set of ordinary primes, then
\[
 \ker\mathcal P_Q=0.
\tag{6}
\]
In contrast, if $Q$ is finite, then
\[
 0\ne\Delta_QH_-
 \subseteq\ker\mathcal P_Q,
 \qquad
 \Delta_Q=\prod_{q\in Q}\Delta_q.
\tag{7}
\]

### Proof

Every infinite set of primes is unbounded. If $\mathcal P_Qh=0$, equation `(5)` with $k=1$
gives
\[
 \widehat h\!\left(\frac{2\pi}{\log q}\right)=0
 \qquad(q\in Q).
\]
These are distinct zeros converging to $0$. The identity theorem gives $\widehat h=0$, and
Fourier injectivity gives $h=0$. This proves `(6)`.

For finite $Q$, choose $0\ne\phi\in C_c^\infty(\mathbb R)$. Every $\Delta_q$ is injective on
$H_-$: an $L_q$-periodic element with positive-end decay is zero. Hence
$\Delta_Q\phi\ne0$. The difference operators commute, while
$\operatorname{Per}_q\Delta_q=0$; therefore
$\operatorname{Per}_q\Delta_Q\phi=0$ for every $q\in Q$. This proves `(7)`.

Fix a prime $p$ and put
\[
 K_p=\ker\operatorname{Per}_p=\Delta_pH_-,
 \qquad B_p=\Delta_pZ(H_\cap).
\tag{8}
\]
The Euler-depleted extension gives
\[
 K_p/B_p\cong M_\zeta.
\tag{9}
\]
If $Q$ is infinite and $p\notin Q$, `(6)` induces an algebraic injection
\[
 M_\zeta\cong K_p/B_p
 \hookrightarrow
 \left(\prod_{q\in Q}C^\infty(\mathbb R/L_q\mathbb Z)\right)
 \big/\mathcal P_Q(B_p),
 \qquad
 [h]\longmapsto[\mathcal P_Qh].
\tag{10}
\]
Indeed, if $\mathcal P_Qh=\mathcal P_Qb$ for some $b\in B_p$, then `(6)` gives $h=b$.
Thus cross-prime compact orbits are algebraically conservative after the exact Poisson-boundary
quotient. This is stronger than sparse positive-radius sampling: each complete periodization
contains the full Fourier lattice, and the prime lengths cofinally accumulate at Fourier
frequency zero.

## 3. The tomography is not strict

`[PROVED HERE] [DAC_DENINGER_COFINAL_PERIODIZATION_NONSTRICTNESS]`

For every fixed $p$ and every infinite $Q$ disjoint from $p$, the restricted map
\[
 \mathcal P_Q:K_p\longrightarrow
 \prod_{q\in Q}C^\infty(\mathbb R/L_q\mathbb Z)
\tag{11}
\]
is continuous and injective, but it is not a topological embedding. Its range is not closed.

### Proof

Choose $0\ne\phi\in C_c^\infty(\mathbb R)$ and put
$\psi=\Delta_p\phi\ne0$. Fix $a>0$ and define
\[
 h_n=e^{-an}T_n\psi\in K_p.
\tag{12}
\]
For each fixed $q$, periodization intertwines $T_n$ with rotation of the $q$-circle. Every
$C^\infty$ seminorm is therefore
\[
 \|\operatorname{Per}_qh_n\|_{C^r}
 =e^{-an}\|\operatorname{Per}_q\psi\|_{C^r}
 \longrightarrow0.
\tag{13}
\]
Hence $\mathcal P_Qh_n\to0$ in the product topology.

Choose $u_0$ with $\psi(u_0)\ne0$. For all large $n$, the defining Meyer seminorm
\[
 q_{a,0,0}(h)=\sup_t e^{a|t|}|h(t)|
\]
satisfies
\[
 q_{a,0,0}(h_n)
 \ge e^{-an}e^{a|n+u_0|}|\psi(u_0)|
 =e^{au_0}|\psi(u_0)|>0.
\tag{14}
\]
Thus $h_n\not\to0$ in $K_p$, proving that the inverse on the range of `(11)` is not continuous.
Since $K_p$ and the countable product target are Fr\'echet, a closed range would make that inverse
continuous by the open-mapping theorem. Therefore the range is not closed.

Equation `(14)` identifies the exact lost datum: compact periodizations remember the translated
shape only up to rotations and do not control escape in the noncompact logarithmic direction.
Algebraic analytic continuation from the prime Fourier lattices is unique but unstable.

## 4. Compact orbit energy has the wrong weight

`[PROVED HERE] [DAC_DENINGER_COMPACT_ORBIT_WEIGHT_ONE_NO_GO]`

Let $E$ be a positive semidefinite quadratic form on the product in `(3)` invariant under the
simultaneous circle rotations induced by $T_a$. Its pullback
\[
 Q(h)=E(\mathcal P_Qh)
\tag{15}
\]
is translation-invariant:
\[
 Q(T_ah)=Q(h).
\tag{16}
\]
If the same form is required to have arithmetic weight one,
\[
 Q(T_ah)=e^aQ(h),
\tag{17}
\]
then $Q=0$. Compare `(16)` and `(17)` at any $a\ne0$.

Even one compact orbit already forces this conclusion without assuming rotation invariance of a
chosen form: because
\[
 \operatorname{Per}_q(T_{L_q}h)=\operatorname{Per}_qh,
\]
any form factoring through that orbit is $L_q$-periodic under the source flow, whereas `(17)`
multiplies it by $e^{L_q}=q$. It must vanish.

Thus the cofinal trace quotient `(10)` is an algebraically faithful coefficient model, but no
rotation-natural positive norm on compact prime traces can be the weight-one Hodge metric. This
obstruction is independent of RH and stronger than the same-prime zero-periodization no-go: it
also excludes rotation-invariant energies using all cross-prime circles simultaneously.

## 5. Conjecture loop and exact survivor

1. **Conjecture: finitely many complete prime traces recover the Euler-depleted sector.**
   **Failed exactly by `(7)`.** The finite Euler difference $\Delta_Q\phi$ is a nonzero common
   kernel vector.
2. **Conjecture: cofinally many complete prime traces recover it.**
   **Proved algebraically by `(6)` and `(10)`.** Entire Fourier uniqueness turns prime lengths
   into a source-pure tomography set.
3. **Conjecture: ordinary product topology turns that tomography into a closed Hodge carrier.**
   **Failed exactly by `(12)`--`(14)`.** Noncompact translates disappear in every fixed compact
   trace while retaining a Meyer exponential seminorm.
4. **Conjecture: a rotation-invariant all-prime trace norm supplies Deninger's weight-one
   polarization.** **Failed exactly by `(16)`--`(17)`.** Compact orbit energy has weight zero.

### The already-existing noncompact survivor, localized exactly

The corpus audit rules out claiming that every noncompact defect is missing:
`DeningerMeyerHalfDensityL1Completion.lean` already constructs
\[
 p_{1/2}(g)=\int_{\mathbb R}e^{t/2}|g(t)|\,dt,
 \qquad
 \overline p_{1/2}([g])
 =\inf_{f\in H_\cap}p_{1/2}(g-Zf).
\tag{18}
\]
It proves exact isometry of the centered flow
\[
 V_a=e^{-a/2}T_a
\tag{19}
\]
and the exact selector: an actual Xi evaluation is bounded by
$\overline p_{1/2}$ if and only if its real part is $1/2$.

`[PROVED HERE] [TRANSPORT COROLLARY]`
`[DAC_DENINGER_EULER_DEPLETED_HALF_DENSITY_RELATIVE_DEFECT]`

The Euler Green inverse localizes `(18)` to the concrete sector `(8)`:
\[
 r_p(h)
 =\inf_{f\in H_\cap}
   p_{1/2}(G_ph-Zf),
 \qquad h\in K_p.
\tag{20}
\]
This is a continuous seminorm, and for every $g\in H_-$,
\[
 r_p(\Delta_pg)=\overline p_{1/2}([g]).
\tag{21}
\]
Consequently:

1. $r_p$ kills $B_p=\Delta_pZ(H_\cap)$;
2. $r_p(e^{-a/2}T_ah)=r_p(h)$;
3. the value in `(21)` is independent of the auxiliary prime $p$;
4. its exact radical is
   \[
   \ker r_p
   =\Delta_p\!\left(
      H_-\cap\overline{Z(H_\cap)}^{\,L^1(e^{t/2}dt)}
    \right).
   \tag{22}
   \]

These statements follow immediately from the homeomorphism
$G_p:K_p\to H_-$, commutation of $G_p$ with translations, and the definition of distance to
$Z(H_\cap)$ in weighted $L^1$. They are recorded as transport, not as an independent novelty
claim.

The localized seminorm is nonzero unconditionally. Choose any known critical-line Xi zero
$\rho$ and the logarithmic Gaussian $g_\ast$, whose Mellin transform never vanishes. Since
$E_\rho$ annihilates $Z(H_\cap)$ and
$|E_\rho(g)|\le p_{1/2}(g)$,
\[
 r_p(\Delta_pg_\ast)
 =\overline p_{1/2}([g_\ast])
 \ge |E_\rho(g_\ast)|>0.
\tag{23}
\]
The centered escape family
\[
 h_a=\Delta_pV_ag_\ast
\tag{24}
\]
therefore satisfies
\[
 r_p(h_a)=r_p(\Delta_pg_\ast)>0,
 \qquad
 \mathcal P_Qh_a\longrightarrow0
 \quad(a\to+\infty)
\tag{25}
\]
in every ordinary compact-prime product. Thus `(20)` supplies exactly the noncompact control
missing from `(11)`; compact tomography cannot replace it.

### Exact hard survivor

The remaining Route-L problem is not construction of another carrier or another noncompact
seminorm. It is to upgrade `(20)` by source arithmetic:

1. prove the exact relative closedness identity
   \[
   H_-\cap\overline{Z(H_\cap)}^{\,L^1(e^{t/2}dt)}
   =Z(H_\cap),
   \tag{26}
   \]
   equivalently $\ker r_p=B_p$;
2. construct a compatible sesquilinear Green/Paugam polarization, rather than merely the
   $L^1$ seminorm, whose cochain radical is the same;
3. derive from Gamma/co-Poisson and real-Fourier source geometry that every actual Xi evaluation
   is admitted continuously by that faithful centered completion.

Clause 3 is RH-strength by the already-formalized half-density selector. It cannot be asserted as
generic functional analysis. The first hard scientific identity is therefore `(26)` together with
its polarized Gamma/co-Poisson admission law. Compact traces in `(10)` remain an algebraically
conservative comparison target, not the Hodge norm.

## 6. Hostile audit

- **No zero divisor.** The only analyticity used is the Fourier transform of a two-ended
  faster-than-exponential source cochain.
- **No disguised RH.** Equations `(5)`--`(25)` are unconditional. Equation `(26)` and
  all-divisor admission remain explicitly open.
- **Not sparse prime sampling.** Full periodizations expose Fourier lattices; `(6)` would be false
  for one evaluation at each positive prime radius.
- **Not a positivity construction.** The theorem proves algebraic conservativity, localizes the
  pre-existing half-density seminorm, and proves why ordinary compact topology cannot supply the
  required polarization.
- **No completion theatre.** Nonclosedness is witnessed by the explicit source family `(12)`;
  the missing topology is not declared into existence.
- **No Lean claim.** Lean corpus was audited read-only during its refactor; no Lean file or build
  belongs to this result.

## 7. Novelty boundary

Poisson summation, the identity theorem for entire functions, and the open-mapping theorem are
standard. Repository and targeted primary-source searches found no composition of these facts
with Meyer's all-weight Poisson quotient and Deninger's prime lengths that states `(6)`, the
relative injection `(10)`, the explicit non-strictness witness `(12)`, and the Tate-weight no-go
`(17)` as one source theorem. Novelty is claimed only for that arithmetic-source composition and
its exact Route-L frontier consequence, not for the analytic ingredients separately.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  arXiv:math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*, arXiv:1807.06400.
- `DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION`.
- `DAC_MEYER_PRIME_SAMPLING_COHOMOLOGY_OBSTRUCTION`.
- `DeningerMeyerHalfDensityL1Completion.lean`.

## Gates

- [x] 0 → 1 in-progress: tomography and instability falsifiers fixed
- [x] 1 → 2 fully-proven: dependency-closed proofs `(5)`--`(25)`
- [ ] 2 → 3 formalized: intentionally paused during Lean corpus refactor
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-08 — Proved cofinal prime-periodization tomography, finite-family failure, ordinary
  product non-strictness, and compact-orbit Tate-weight obstruction. Corpus audit identified the
  existing half-density seminorm, localized it exactly by the Euler Green inverse, and moved the
  hard frontier to relative closedness `(26)` plus polarized all-divisor admission.
