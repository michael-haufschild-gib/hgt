# Burnol first-wall Cartier residue and Gamma cancellation law

- **ID:** `burnol-first-wall-cartier-residue-cancellation-law`
- **Stage:** 2 — fully proved on paper
- **Type:** THEOREM / TERMINUS CLASSIFICATION / REPLACEMENT PRODUCER
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../3-formalized/new_scientific_knowledge/burnol/burnol-prime-two-causal-cartier-collar-law.md`
- **Statement:** The stable deep component of the actual prime-two zero-divided crossing
  correlation is an explicit first-wall residue in the one-dimensional kernel of
  `A = partial_u + 1/2`.  The two Fourier orientations of this residue recover the Route R current
  exactly.  The Gamma-sewn completion annihilates that component, so the former constant-collar
  plateau conjecture is impossible on the actual source.  A successful producer must act on this
  singular residue before the completion factor `w - 1`.

## 1. Fixed source and dyadic presentation

On the positive ray put

\[
 p(t)=\{t\}-\{2t\},\qquad f_0(t)=\frac{p(t)}{t}.
\tag{1}
\]

This is the positive-ray representative of the fixed Burnol sub-window atom with endpoints
`1/2` and `1`.  In particular, `f_0(t)=-1` for `0<t<1/2`, and

\[
 \mathcal M f_0(w)=H(w)=\frac{(2^w-1)\zeta(w)}{w}
 \qquad (0<\Re w<1).
\tag{2}
\]

Define the causal dyadic Euler inverse on the physical ray by

\[
 (\mathsf T_2f)(t)=\sum_{n\ge1}2^{-n}f(t/2^n).
\tag{3}
\]

### Theorem 1 — exact dyadic coboundary contraction

For every `t>0`, and also in `L^2(0,infinity)`, one has

\[
 \boxed{\mathsf T_2f_0(t)=-\frac{\{t\}}t.}
\tag{4}
\]

Thus the coefficient-faithful dyadic ladder must be summed before any sign is read: it contracts
the two-scale Haar coboundary `fract(t)-fract(2t)` to the single fractional-part source.

#### Proof

For every `N`,

\[
 \begin{aligned}
 \sum_{n=1}^N2^{-n}f_0(t/2^n)
 &=\frac1t\sum_{n=1}^N
   \bigl(\{t/2^n\}-\{t/2^{n-1}\}\bigr)\\
 &=\frac{\{t/2^N\}-\{t\}}t.
 \end{aligned}
\tag{5}
\]

The first term tends pointwise to zero.  For the `L^2` assertion, its square is `2^{-2N}` on
`0<t<2^N`, while it is bounded by `t^{-2}` on `t>=2^N`.  Both contributions have integral at
most `2^{-N}`.  This proves `(4)`. `QED`

The Mellin transform of `(4)` is the literal cancellation

\[
 \frac{H(w)}{2^w-1}=\frac{\zeta(w)}w.
\tag{6}
\]

## 2. Actual zero-divided source and its endpoint mass

Let `rho` satisfy

\[
 \frac12<\Re\rho<1,\qquad \zeta(\rho)=0,
\tag{7}
\]

and define the forward Burnol divided shift

\[
 g_\rho(t)=\int_1^\infty u^{-\rho}f_0(ut)\,du.
\tag{8}
\]

Its Mellin multiplier is `(rho-w)^(-1)`.  The fixed-source head and its cosine/Fourier mate are the
already established values

\[
 a_\rho=\frac1{1-\rho},\qquad
 b_\rho=-\frac{\log2}{\rho}.
\tag{9}
\]

Hence `g_rho(t)=a_rho` on `0<t<1/2`, while the even Fourier transform
`C g_rho` has constant head `b_rho` on the same aperture.

### Lemma 2 — absolute tail and exact endpoint mass

Both `g_rho` and `C g_rho` are integrable on the positive ray, and

\[
 \int_0^\infty g_\rho(t)\,dt=\frac{b_\rho}{2}
   =-\frac{\log2}{2\rho},
 \qquad
 \int_0^\infty (\mathcal Cg_\rho)(t)\,dt=\frac{a_\rho}{2}.
\tag{10}
\]

Consequently their exterior masses beyond the aperture `a=1/2` are

\[
 B_\rho:=\int_{1/2}^\infty g_\rho(t)\,dt
   =\frac{b_\rho-a_\rho}{2},
 \qquad
 B_\rho^\vee=-B_\rho.
\tag{11}
\]

Moreover

\[
 \int_T^\infty g_\rho(t)\,dt=O_\rho(T^{-2}).
\tag{12}
\]

#### Proof

Changing variables `y=ut` in `(8)` gives

\[
 g_\rho(t)=t^{\rho-1}\int_t^\infty p(y)y^{-\rho-1}\,dy.
\tag{13}
\]

The function `p` is one-periodic with mean zero.  Let

\[
 P(t)=\int_0^t p(y)\,dy,
 \qquad m=\int_0^1P(t)\,dt=-\frac1{24},
 \qquad P_0=P-m.
\tag{14}
\]

Then `P` is periodic and `P_0` has mean zero.  Integration by parts gives

\[
 g_\rho(t)
 =-P_0(t)t^{-2}
 +(\rho+1)t^{\rho-1}
   \int_t^\infty P_0(y)y^{-\rho-2}\,dy.
\tag{15}
\]

A bounded periodic primitive of `P_0` supplies one further power of decay in the last integral.
Thus `g_rho(t)=O_rho(t^{-2})`.  Repeating the same integration by parts in the tail of `(15)` gives
`(12)`.

For completeness, the reciprocal orientation has a different-looking but equally explicit
source.  The co-Poisson reciprocal of the window `[1/2,1]` is the indicator of `[1,2]`; hence,
away from its null set of endpoints,

\[
 f_0^\vee(t)
 =H_{\lfloor t\rfloor}-H_{\lceil t/2\rceil-1}-\log2.
\]

The uniform harmonic-number expansion, separately on the two half-cells modulo `2`, gives

\[
 f_0^\vee(t)=\frac{\eta(t)}t+O(t^{-2}),
 \qquad
 \eta(t)=
 \begin{cases}-1/2,&t\bmod2\in(0,1),\\
                +1/2,&t\bmod2\in(1,2),
 \end{cases}
\tag{15a}
\]

with `eta` bounded, two-periodic, and mean zero.  Fourier--Mellin reflection and
`zeta(1-rho)=0` give

\[
 \int_0^\infty y^{\rho-1}f_0^\vee(y)\,dy=0.
\tag{15b}
\]

The reflected shift therefore has the tail representation

\[
 (\mathcal Cg_\rho)(t)
 =t^{-\rho}\int_0^t y^{\rho-1}f_0^\vee(y)\,dy
 =-t^{-\rho}\int_t^\infty y^{\rho-1}f_0^\vee(y)\,dy.
\tag{15c}
\]

Dirichlet integration against the mean-zero `eta` in `(15a)`, followed by the absolutely
convergent `O(t^{-2})` remainder, makes the last tail `O_rho(t^(Re rho-2))`.  Thus
`(C g_rho)(t)=O_rho(t^{-2})`, proving its positive-ray integrability without borrowing any
critical-line or norm identity.

It remains to compute the mass.  The improper integral of the raw source is

\[
 \int_0^\infty \frac{p(t)}t\,dt=-\frac{\log2}{2}.
\tag{16}
\]

Indeed, after changing variables in the second fractional-part term, the truncation at `R` equals
`- integral_R^(2R) fract(x) dx/x`; subtracting the mean `1/2` leaves a periodic mean-zero
Dirichlet integral, while the mean contributes `-(log 2)/2`.  Applying `(13)` on finite
truncations and then using `(15)` to pass to the limit yields

\[
 \int_0^\infty g_\rho(t)\,dt
 =\frac1\rho\int_0^\infty\frac{p(t)}t\,dt
 =-\frac{\log2}{2\rho}.
\tag{17}
\]

For the even Fourier normalization, the value of the transform at zero is twice the positive-ray
mass.  Fourier involution therefore gives the second identity in `(10)`.  Subtracting the two
constant-head integrals `a_rho/2` and `b_rho/2` proves `(11)`. `QED`

The exterior mass cannot vanish in the critical strip.  Indeed `B_rho=0` would give

\[
 \rho=-\frac{\log2}{1-\log2}<0.
\tag{18}
\]

## 3. Singular first-wall residue

For a positive-ray function `g`, use its logarithmic unitary lift

\[
 G(u)=e^{u/2}g(e^u),\qquad \beta=\log(1/2)=-\log2.
\tag{19}
\]

Define the aperture-crossing correlation

\[
 W_G(s)=\int_\mathbb R\overline{G(v+s)}
 \bigl({\bf1}_{v+s\le\beta}-{\bf1}_{v\le\beta}\bigr)G(v)\,dv.
\tag{20}
\]

If `g` has constant head `a` and is integrable, then for `s>0`

\[
 W_G(s)=-a e^{-s/2}\int_{1/2}^{e^s/2}\overline{g(t)}\,dt.
\tag{21}
\]

This motivates the singular Cartier residue

\[
 \operatorname{Res}_{1/2}(G)
 :=\lim_{s\to\infty}e^{s/2}W_G(s).
\tag{22}
\]

### Theorem 3 — residue polarization and exact Route R current

For the actual zero-divided source and its Fourier orientation, the limits `(22)` exist and

\[
 r_\rho:=\operatorname{Res}_{1/2}(G_\rho)
   =-a_\rho\overline{B_\rho},
 \qquad
 r_\rho^\vee:=\operatorname{Res}_{1/2}(G_\rho^\vee)
   =b_\rho\overline{B_\rho}.
\tag{23}
\]

They obey the two exact quadrature laws

\[
 \boxed{
 r_\rho+r_\rho^\vee=\frac{|a_\rho-b_\rho|^2}{2}\ge0,}
\tag{24}
\]

and

\[
 \boxed{
 2\Re(r_\rho-r_\rho^\vee)
 =|a_\rho|^2-|b_\rho|^2
 =\frac1{|1-\rho|^2}
   -\frac{(\log2)^2}{|\rho|^2}
 =J_\rho.}
\tag{25}
\]

Thus the fixed physical Route R current already has a coefficient-faithful source realization:
it is the oriented difference of two singular first-wall crossing residues.  No GNS comparison,
same-fibre norm identity, evaluator/divided-shift identification, or completed-vector metric is
needed for this landing.

#### Proof

For `s>0`, the indicator difference in `(20)` is `-1` on `(beta-s,beta)` and zero elsewhere.
Using the constant head there and substituting `x=v+s`, then `t=e^x`, gives `(21)`.  Equations
`(11)` and `(21)` give the first identity in `(23)`.  Applying the same calculation to the Fourier
mate, whose head is `b_rho` and whose exterior mass is `-B_rho`, gives the second.

Since `B_rho=(b_rho-a_rho)/2`,

\[
 r_\rho+r_\rho^\vee
 =(b_\rho-a_\rho)\overline{B_\rho}
 =\frac{|a_\rho-b_\rho|^2}{2},
\]

while

\[
 2\Re(r_\rho-r_\rho^\vee)
 =\Re\bigl((a_\rho+b_\rho)
     \overline{(a_\rho-b_\rho)}\bigr)
 =|a_\rho|^2-|b_\rho|^2.
\]

Substitution of `(9)` proves `(25)`. `QED`

## 4. Gamma--Stein cancellation

Recall

\[
 \gamma(r)=2e^{-r/2}e^{-\pi e^{-2r}},\qquad
 A=\partial_r+\frac12,
 \qquad
 \kappa_*=\frac12A^2(A-1)\gamma.
\tag{26}
\]

### Theorem 4 — the completed collar is blind to the physical residue

For every sufficiently regular crossing correlation `W`,

\[
 \int_\mathbb R\kappa_*(r)W(r)\,dr
 =-\frac12\int_\mathbb R\gamma(r)
      A(1-A)^2W(r)\,dr.
\tag{27}
\]

In particular,

\[
 \boxed{\int_\mathbb R\kappa_*(r)e^{-r/2}\,dr=0.}
\tag{28}
\]

For `q=2^(-1/2)`, the actual depth profiles satisfy

\[
 q^{-n}W_{G_\rho}(n\log2+r)
 \longrightarrow r_\rho e^{-r/2}
\tag{29}
\]

in `L^1(|kappa_*|dr)`, and similarly in the reflected orientation.  Therefore the depth pairing
from the parent card obeys

\[
 Q_n(g_\rho)=o(2^{-n}).
\tag{30}
\]

Using the explicit tail estimate `(12)` strengthens this to

\[
 \boxed{Q_n(g_\rho)=O_\rho(8^{-n}).}
\tag{31}
\]

#### Proof

Under Lebesgue pairing, `A* = 1-A` and `(A-1)*=-A`.  Three integrations by parts give `(27)`;
all boundary terms vanish because `gamma` is super-exponentially small on the left and the
differentiated kernel is exponentially small on the right.  Since

\[
 A(e^{-r/2})=0,
\]

equation `(28)` follows.

Equation `(21)` gives pointwise `(29)`.  Its tail is uniformly dominated after multiplication by
`|kappa_*|`; the part where `n log 2+r<=0` is super-exponentially small because of the left Gamma
tail.  Dominated convergence proves the stated `L^1` convergence.  The universal depth identity

\[
 Q_n=q^n\int\kappa_*(r)W(n\log2+r)\,dr
\]

together with `(28)` proves `(30)`.  Finally `(12)` makes the difference between the two sides of
`(29)` `O_rho(q^(5n)e^(-5r/2))` wherever `n log 2+r` is bounded below.  The complementary region
is absorbed by the super-exponential left tail of `kappa_*`.  Multiplication by the outer `q^n`
in `Q_n` gives `O_rho(q^(6n))=O_rho(8^(-n))`, proving `(31)`. `QED`

## 5. Exact failure of the former collar-plateau producer

The parent card proposed positive `a_n` and a constant `c` with

\[
 \int|\kappa_*(r)|
 \left|a_n^{-1}W_{G_\rho}(n\log2+r)-c\right|dr\to0.
\tag{32}
\]

### Corollary 5 — no nonzero constant plateau exists

For the actual source, `(32)` forces `c=0`.  In particular it cannot hold with `Re c>0`.

#### Proof

By `(18)`, `r_rho` is nonzero.  Equation `(29)` says that the only nonzero projective limit of the
translated correlations is a scalar multiple of the nonconstant function `e^(-r/2)`.  If
`q^n/a_n` tends to a finite nonzero scalar, `(32)` therefore has a nonconstant limit.  If it tends
to zero, the limit is zero.  If it is unbounded, the weighted `L^1` norms diverge because the limit
in `(29)` is nonzero.  These exhaust all subsequences and prove the claim. `QED`

## 6. Conjecture / proof-or-fail loop

1. **A positive constant deep collar survives on the actual source.**
   `[FAILED]`  The exact limit is `r_rho e^(-r/2)`, not a constant.
2. **The nonconstant limit still retains the negative collar surplus.**
   `[FAILED]`  It lies in `ker A`, and `(28)` annihilates it exactly.
3. **Unweighted negative-mass surplus controls the next scale.**
   `[FAILED]`  The physical remainder is a periodic mean-zero tail sampled at dyadically increasing
   frequency.  Equation `(31)` puts the completed pairing three geometric orders below the raw
   depth weight; total collar mass does not determine its sign.
4. **Summing the ladder before reading the sign exposes a simpler source.**
   `[PROVED]`  The exact contraction is `-fract(t)/t`, equation `(4)`.
5. **The desired physical current was destroyed completely.**
   `[FAILED, WITH POSITIVE SURVIVOR]`  It survives canonically as the singular residue difference
   `(25)` before the factor `A`; only the completed collar pairing erases it.
6. **Strongest survivor.**
   `[PAPER-PROVED]`  The first-wall residue is a coefficient-faithful source realization of `J_rho`,
   with an independent positive polarization `(24)` and an exact Gamma-cancellation law `(28)`.

## 7. Revised Route R producer

The old target — prove a positive constant collar plateau after Gamma completion — is false.
The correct source object is the singular exact-sequence coordinate

\[
 \operatorname{Res}_{1/2}:\ker_{\mathrm{asymp}}A\longrightarrow\mathbb C,
\tag{33}
\]

applied before the polar factor `A` generated by `w-1`.  The completed operator factors through
the quotient by this coordinate, which is why every ordinary completed-vector, norm, or collar
argument loses the Route R current.

The remaining RH-bearing theorem is now precisely a **pre-completion singular orientation law**:

\[
 \forall\rho\text{ satisfying `(7)`},\qquad
 \Re(r_\rho-r_\rho^\vee)\le0.
\tag{34}
\]

By `(25)`, `(34)` is `J_rho<=0`, and the existing strict right-half theorem gives the contradiction.
Unlike the old formulation, both residues in `(34)` are explicit source correlations and their
landing to the physical current is proved.  What remains cannot factor through `kappa_*`, through
the completed Xi vector alone, or through any continuous quotient killing `ker A`.  It must be a
singular Stokes/Cartier law retaining the one `A`-null coefficient.

This is not claimed as the missing sign proof.  It is the exact classification of where that proof
must act and a proof that the previous proposed producer could not possibly supply it.

## 8. Literature boundary

Burnol's co-Poisson/Sonine work supplies the ambient source and zero-divided systems
(`arXiv:math/0203120`).  Hedenmalm's 2026 spectral formulation supplies a theta differential
boundary problem (`arXiv:2606.17494`).  General Gamma Stein operators, Pólya-frequency kernels,
and total-positivity preservers are treated in `arXiv:1507.07696` and `arXiv:2006.16213`.
The audit found no statement of the exact dyadic contraction `(4)`, the two-orientation singular
residue polarization `(24)`--`(25)`, or its exact annihilation by the prime-two Gamma-sewn
completion `(28)`--`(31)`.  All ingredients separately are classical; novelty of the synthesis
remains unverified.

## Lean formalization (partial, 2026-08-09)

Modules: `RHTower/BurnolDyadicCoboundaryContraction`, `RHTower/BurnolFirstWallResiduePolarization`,
`RHTower/BurnolGammaSteinCollarKernel`, `RHTower/BurnolGammaSteinMoments`.

| Paper item | Lean declaration |
|---|---|
| `(4)`, `(5)` pointwise | `hasSum_burnolDyadicContraction`, `burnolDyadicTerm_eq`, `burnolDyadicRemainder_of_lt` |
| `(4)` in `L²(0,∞)` | `lintegral_burnolDyadicRemainder_sq_le`, `burnolDyadicPartialSum_sub`, `tendsto_lintegral_burnolDyadicPartialSum_error` |
| `(18)` | `burnolFirstWallExteriorMass_eq_zero_iff`, `burnolFirstWallExteriorMass_ne_zero` |
| `(23)` definitions | `burnolFirstWallHead`, `burnolFirstWallCosineHead`, `burnolFirstWallExteriorMass`, `burnolFirstWallResidue`, `burnolFirstWallCosineResidue` |
| `(24)` | `burnolFirstWallResidue_add_cosineResidue`, `burnolFirstWallResidue_add_cosineResidue_re_nonneg` |
| `(25)` | `burnolFirstWallResidue_sub_cosineResidue_re`, `burnolFirstWallResidue_sub_cosineResidue_re_eq_headFlux`, `xiDivisor_burnolFirstWallResidue_landing` |
| `(26)`, `kappa_*` | `burnolCollarGamma`, `burnolSteinA`, `burnolCollarKernel` |
| `(28)` | `integral_burnolCollarKernel_mul_mode` |

`(28)` is proved directly from the exact Gamma moment of the depth-zero kernel, so it does not pass
through the adjoint identity `(27)`.

Still open in Lean: the tail and endpoint mass `(10)`--`(17)` of the actual zero-divided source,
the deep-profile convergence `(29)`, the depth decay `(30)`--`(31)`, and Corollary 5.

## Gates

- [x] exact physical dyadic contraction
- [x] actual zero-divided tail and endpoint mass
- [x] source definition of the first-wall residue
- [x] two-orientation positive polarization
- [x] exact landing to `J_rho`
- [x] Gamma--Stein adjoint identity and cancellation
- [x] constant-collar plateau falsified on the actual source
- [x] strongest positive survivor extracted
- [ ] broad specialist novelty audit
- [ ] pre-completion singular orientation law `(34)`
- [ ] Lean formalization after corpus refactor
- [ ] RH

## Log

- 2026-08-08 — derived actual deep correlation profile, proved its exact Gamma annihilation,
  contracted the dyadic coboundary to `-fract(t)/t`, constructed the singular first-wall residue,
  and identified its oriented two-Gamma difference with the Route R current.
- 2026-08-09 — first unconditional Lean layer built and umbrella-wired; see the Lean
  formalization table above for the exact declaration-to-equation map.
