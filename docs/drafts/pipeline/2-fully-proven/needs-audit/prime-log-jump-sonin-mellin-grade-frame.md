# Prime-log jump packets give a conormal-faithful Sonin boundary grade frame

- **ID:** `prime-log-jump-sonin-mellin-grade-frame`
- **Stage:** 2-fully-proven / needs literature and Lean audit
- **Type:** THEOREM (paper) / SOURCE-NORMAL–SONIN CROSS-LANDING / GRADE FALSIFIER
- **Scientific status:** `[PAPER-PROVED BRIDGE] [CORPUS COLLISION]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Parents:**
  `hedenmalm-two-prime-theta-interval-normal-frame.md`;
  `../new_scientific_knowledge/sonin/cofinal-essential-phase-sonin-coupling-nonannihilation.md`;
  `../../1-in-progress/bv-copoisson-principal-normal-connection-law.md`;
  `../../1-in-progress/prime-valuation-hellinger-rees-reflection-fracture.md`;
  `../../4-publication-ready/riemann-source-modular-superselection/main.tex`.
- **Statement:** A source-defined prime-log jump shell reaches the cofinal Sonin partial-unitary
  face and has a nonzero first Mellin boundary trace at every complex spectral point.  Dilation
  changes that trace by the exact grade `1/2 - Re(s)`; grade preservation therefore forces the
  critical line.

## Goal

The smooth essential-phase Sonin packets already constructed in the corpus make the successive
aperture coupling and its Hilbert adjoint inverse isometries at the cofinal boundary, but every
fixed Mellin conormal is all-orders flat on them.  The theta translation anomaly supplies the
opposite half: exact Xi conormal incidence, whose quotient by Xi is a literal interval window, but
ordinary `L2` completion loses its divisor defect.

The purpose of this theorem is to put the two survivors on one explicit packet family.  The result
must be read as a bridge and a falsifier, not as the missing RH theorem: continuity of the Mellin
normal trace in the same closed Hilbert boundary topology remains open.

## 1. The prime window is already in the theta source normal

For the centered Hedenmalm anomaly, the corpus proves

\[
 \widehat c_n(z)=a_n(z)\Xi_C(z),
 \qquad
 a_n(z)=2n^{-1/2}\frac{\sin(z\log n/2)}{z}.
 \tag{1}
\]

With the Fourier convention used there,

\[
 h_n(x)=n^{-1/2}{\bf 1}_{[-\log n/2,\,\log n/2]}(x)
 \quad\Longrightarrow\quad
 \widehat h_n=a_n.
 \tag{2}
\]

Thus `h_n` is not an added model: it is the exact coefficient exposed by dividing the theta
translation anomaly by the Xi conormal in the source normal cone.  For distinct primes `p < q`,

\[
 \sqrt q\,h_q-\sqrt p\,h_p
 ={\bf 1}_{\{\log p/2<|x|<\log q/2\}}
 \quad\text{a.e.}
 \tag{3}
\]

Write

\[
 A=\frac{\log p}{2},\qquad B=\frac{\log q}{2},\qquad D=B-A>0.
 \tag{4}
\]

Unique factorization implies `A/B` is irrational.

## 2. Discontinuous essential-phase packets

Let

\[
 \phi(x)={\bf 1}_{\{A<|x|<B\}}.
 \tag{5}
\]

For `kappa > 0`, put

\[
 \mu_\kappa
 =\frac{1}{2D}\int_{\mathbb R}\phi(x)\cos(\kappa x)\,dx
 =\frac{\sin(\kappa B)-\sin(\kappa A)}{\kappa D},
 \tag{6}
\]

\[
 u_\kappa(x)=\phi(x)\bigl(\cos(\kappa x)-\mu_\kappa\bigr),
 \qquad
 w_\kappa=\frac{u_\kappa}{\|u_\kappa\|_2}.
 \tag{7}
\]

Then `u_kappa` is real, even, compactly supported away from zero, and

\[
 u_\kappa(0)=0,
 \qquad
 \int_{\mathbb R}u_\kappa=0.
 \tag{8}
\]

It is an exact two-condition Poisson source test in the distributional/jump class.  It is not a
smooth Meyer test.  Riemann--Lebesgue gives

\[
 \mu_\kappa\longrightarrow0,
 \qquad
 \|u_\kappa\|_2^2\longrightarrow D.
 \tag{9}
\]

The same compact-support, weak-escape, Fourier-translation, Plancherel-tail, and compact-correction
arguments used for the smooth packet prove the Sonin coupling limit for `(7)`.  Namely, fix

\[
 0<a<q_0<b<A<B<c,
 \tag{10}
\]

choose the carrier `kappa_r=2 pi r q_0`.  The support in `(5)` then lies strictly inside the
outer physical aperture.  If

\[
 Z_r=L_{a,b}(U_r+U_{1/r})L_{b,c},
 \tag{11}
\]

then, along every cofinal clock satisfying the same crossing conditions as the smooth theorem,

\[
 \|Z_rw_{\kappa_r}-U_{1/r}w_{\kappa_r}\|_2\longrightarrow0,
 \tag{12}
\]

and for `v_r=U_{1/r}w_{kappa_r}`,

\[
 \|Z_r^*v_r-w_{\kappa_r}\|_2\longrightarrow0.
 \tag{13}
\]

### Proof of the extension from smooth to jump amplitude

No derivative of `phi` occurs in the proof of `(12)`--`(13)`.  The required inputs are:

1. `phi` is nonzero, bounded, integrable, square-integrable, and supported in one strict annulus;
2. `phi g` is integrable for every fixed `g in L2`, so modulation makes `w_kappa` weakly null;
3. the Fourier transform of `phi` is in `L2`, so its translated spectral energy leaves every
   fixed central band and concentrates after inverse dilation;
4. support cutoffs are exact up to null endpoints;
5. fixed Sonin correction operators are compact.

All five hold for `(5)`.  The two-branch estimate and the reversed-product adjoint identity are
operator statements independent of smoothness.  Substitution gives `(12)` and `(13)` exactly as in
the parent proof.

## 3. Exact first Mellin boundary trace

For `s in C`, define the positive-ray Mellin evaluation

\[
 M_\kappa(s)=\int_0^\infty u_\kappa(x)x^{-s}\,dx
 =\int_A^B x^{-s}\bigl(\cos(\kappa x)-\mu_\kappa\bigr)\,dx.
 \tag{14}
\]

Put

\[
 H(s)=\frac1D\int_A^B x^{-s}\,dx.
 \tag{15}
\]

This is entire.  Integration by parts twice gives, locally uniformly in `s`,

\[
 \begin{aligned}
 \kappa M_\kappa(s)
 &=B^{-s}\sin(\kappa B)-A^{-s}\sin(\kappa A)\\
 &\quad-\bigl(\sin(\kappa B)-\sin(\kappa A)\bigr)H(s)
 +O_K(\kappa^{-1})
 \end{aligned}
 \tag{16}
\]

for `s` in any fixed compact set `K subset C`.  The same estimate after arbitrary `s` derivatives
follows by inserting powers of `log x`; hence `(16)` is convergence in the compact-open entire
topology, including all multiplicity jets.

Because `A/B` is irrational, the continuous Kronecker flow

\[
 \kappa\longmapsto(\kappa A,\kappa B)\pmod{2\pi}
 \tag{17}
\]

is dense in the two-torus and is recurrent.  There are two cofinal, source-defined clocks with

\[
 (\sin(\kappa_j^A A),\sin(\kappa_j^A B))\longrightarrow(1,0),
 \tag{18}
\]

\[
 (\sin(\kappa_j^B A),\sin(\kappa_j^B B))\longrightarrow(0,1).
 \tag{19}
\]

Equations `(9)` and `(16)` yield locally uniformly

\[
 \kappa_j^A\,\mathcal M w_{\kappa_j^A}(s)
 \longrightarrow D^{-1/2}F_A(s),
 \qquad
 F_A(s)=H(s)-A^{-s},
 \tag{20}
\]

\[
 \kappa_j^B\,\mathcal M w_{\kappa_j^B}(s)
 \longrightarrow D^{-1/2}F_B(s),
 \qquad
 F_B(s)=B^{-s}-H(s).
 \tag{21}
\]

Thus the discontinuous packet is exactly first-order at the Mellin boundary.  This is the sharp
opposite of the smooth packet's all-orders flatness.

## 4. The two phase charts lose no conormal

The entire functions `F_A,F_B` have exactly one common zero, namely `s=0`, and that common zero is
simple in both channels.

Indeed, a common zero gives

\[
 A^{-s}=H(s)=B^{-s}.
 \tag{22}
\]

The endpoint equality implies

\[
 e^{-s\log(B/A)}=1,
 \tag{23}
\]

so `Re(s)=0`.  Write `s=it`.  The equality `H(it)=A^{-it}` says that the average over `[A,B]` of
the unit-modulus function `x -> x^{-it}` has modulus one.  Equality in the triangle inequality
forces this continuous function to be constant, hence `t=0`.  Conversely `F_A(0)=F_B(0)=0`.

Moreover,

\[
 F_A'(0)=\log A-\frac1D\int_A^B\log x\,dx<0,
 \qquad
 F_B'(0)=\frac1D\int_A^B\log x\,dx-\log B<0.
 \tag{24}
\]

Therefore the removable quotients

\[
 G_A(s)=\frac{F_A(s)}s,
 \qquad
 G_B(s)=\frac{F_B(s)}s
 \tag{25}
\]

are entire and have no common zero anywhere in `C`.  Cartan--Bezout consequently gives entire
`C_A,C_B` with

\[
 C_AG_A+C_BG_B=1.
 \tag{26}
\]

For every zero `rho` of completed Xi and every multiplicity `m_rho`, at least one phase channel is
nonzero at `rho`.  Consequently the candidate source-normal landing

\[
 \xi(s)\longmapsto\bigl(G_A(s)\xi(s),G_B(s)\xi(s)\bigr)
 \tag{26a}
\]

would preserve the first nonzero Xi jet and hence the exact multiplicity.  The coprimality and
jet statement are unconditional; identifying `(26a)` with the normal operator of the full,
undeconvolved theta-to-Sonin source action is still open.  No zero was used to choose the shell or
either clock.

### 4a. Explicit compact-BV realization and conormal faithfulness

The quotients `G_A,G_B` are not abstract Bezout multipliers.  They are Mellin transforms of two
literal compactly supported BV windows.  Define

\[
 W_A(x)=\frac{x-B}{Dx}{\bf 1}_{(A,B)}(x),
 \qquad
 W_B(x)=-\frac{x-A}{Dx}{\bf 1}_{(A,B)}(x).
 \tag{26b}
\]

Both functions have bounded variation and compact support in `(0,infinity)`.  Stieltjes
integration by parts, or ordinary integration followed by the endpoint jumps, gives

\[
 \int_0^\infty W_A(x)x^{-s}\,dx=G_A(s),
 \qquad
 \int_0^\infty W_B(x)x^{-s}\,dx=G_B(s).
 \tag{26c}
\]

For example, the signed measure

\[
 dC_A=D^{-1}{\bf 1}_{(A,B)}(x)\,dx-\delta_A
 \tag{26d}
\]

has cumulative function `C_A(x)=(x-B)/D` on `(A,B)` and total mass zero.  Hence

\[
 F_A(s)=\int x^{-s}\,dC_A(x)
 =s\int_A^B C_A(x)x^{-s-1}\,dx=sG_A(s).
 \tag{26e}
\]

The calculation for `B` uses
`dC_B=delta_B-D^(-1) 1_(A,B) dx` and is identical.

This gives a theta-normal/Sonin realization of a faithfulness mechanism already present in the
corpus's BV/co-Poisson and Hellinger--Rees interfaces.  Their proved principal-normal law says that
a compact-BV window `W` contributes

\[
 2M_W\,[\Lambda']
 \tag{26f}
\]

to the normal class of the completed co-Poisson multiplier ideal.  At a zero `rho` of multiplicity
`m`, the class has order `m-1` and leading coefficient proportional to the value of `M_W` at the
shifted spectral coordinate.  Since `(G_A,G_B)` has no common zero anywhere, the canonical
rank-two class

\[
 2\bigl(M_{W_A},M_{W_B}\bigr)[\Lambda']
 \tag{26g}
\]

is nonzero on the top normal jet of every Xi fibre, at every multiplicity, before any zero is
selected.  However, `bounded-variation-prime-window-divisor-tomography.md` already proves and
formalizes two-window BV faithfulness, while the Sonin aperture/grade laws already identify the
same critical exponent.  Thus `(26b)`--`(26g)` are an explicit compatibility bridge in the
theta-normal chart, not closure of a frontier gate.

It does not prove the Hellinger--Rees moderation of reflection.  The corpus already proves that
every finite-Rees operator preserves the all-orders-flat radical, so a faithful rank-two section
still needs essential-singular, source-calibrated sewing.

## 5. The critical line is the zero-grade locus

For the unitary dilation convention in the Sonin corpus,

\[
 (U_{1/r}f)(x)=r^{-1/2}f(x/r),
 \tag{27}
\]

and direct substitution gives

\[
 \mathcal M(U_{1/r}f)(s)=r^{1/2-s}\mathcal M f(s).
 \tag{28}
\]

Hence the source and target of the partial-unitary boundary transition `(12)` have Mellin normal
grades differing by

\[
 \operatorname{grade}_s(v)-\operatorname{grade}_s(w)=\frac12-\operatorname{Re}s.
 \tag{29}
\]

Because `(20)`--`(26)` ensure a nonzero normal coefficient in at least one source-defined phase
chart, equality of the two intrinsic grades forces

\[
 \operatorname{Re}s=\frac12.
 \tag{30}
\]

This is a theorem about the constructed packets, not yet a theorem that Xi root modes have equal
grade.  It gives an exact falsifier for the missing Hedenmalm/Sonin realization:

> A claimed source-defined same-fibre dagger must extend the `L2` partial unitary `(12)`--`(13)`,
> make at least one Mellin normal `(20)`--`(21)` continuous and nonzero, and preserve its Rees
> order.  If it does all three, every Xi zero lies on the critical line by `(29)`--`(30)`.

## What this changes

The source-to-consumer obstruction now has a literal representative:

```text
theta prime translation
  -> divide once by Xi in the source normal cone
  -> prime-log jump shell
  -> essential modulation exp(i x / h)
  -> Sonin cofinal partial unitary
  -> nonzero first Mellin boundary trace
  -> reflected grade difference 1/2 - Re(s).
```

This unifies four prior shadows:

1. smooth essential-phase packets reach the Hilbert boundary but are Mellin-flat;
2. theta interval anomalies carry every Xi conormal but vanish in ordinary `L2` defect;
3. finite and summably weighted prime frames fail uniform coercivity;
4. raw alternating tails at reflected zeros have grades `beta` and `1-beta`;
5. the existing BV/Hellinger two-window theorem already supplied source-normal top-jet
   faithfulness.

They are manifestations of one **trace/unitary incompatibility law**: ordinary Hilbert completion
retains the adjoint but discards the Mellin boundary trace; analytic conormal completion retains the
trace but has no Hilbert adjoint.  The critical line is precisely where their scaling grades agree.

The remaining open theorem is narrower and operator-theoretic:

> Construct the canonical closed graph/bornological completion of the literal Euler--Poisson--Gamma
> source on which both the Sonin partial unitary and the first jump-Mellin normal are continuous,
> and prove the normal is intrinsic under the Hilbert adjoint.

That theorem would imply RH immediately by `(26)` and `(29)`.  Merely declaring the trace part of
the norm would be circular unless its continuity follows from the ordinary-integer source before
zero specialization.

## Hostile audit

1. **Not RH.**  Same-grade continuity of the Mellin normal under the closed boundary dagger is not
   proved.
2. **No positivity claim.**  The argument uses a partial unitary and a first-order trace, not a
   positive quadratic energy.
3. **No smooth-source sleight of hand.**  The new effect comes exactly from endpoint jumps.  Smooth
   amplitudes are all-orders Mellin-flat and cannot give `(20)`--`(21)`.
4. **No zero-dependent clock.**  The two phase clocks depend only on the distinct source primes.
5. **No simplicity assumption.**  Compact-open convergence and coprimality retain every Xi jet.
6. **No bounded Mellin evaluation on `L2`.**  The trace is a first boundary normal and is not
   claimed continuous in ordinary `L2`; this is the remaining hard theorem.
7. **No completed spectral operator.**  `(12)`--`(13)` give a genuine boundary partial unitary, not
   a self-adjoint operator whose eigenvalues are the Xi zeros.
8. **Coordinate seam remains auditable.**  Equation `(2)` lives on the theta translation line and
   `(11)` on the Sonin dilation line.  The proposed cross-landing identifies the exposed interval
   coefficient as a Sonin packet amplitude.  A canonical intertwining of the full, undeconvolved
   source actions is not yet proved.

## Preliminary literature boundary

Burnol develops co-Poisson distributions, Mellin-entire compactly supported distributions, and
extended Sonine spaces.  Hedenmalm develops the theta differential pencil and its pair
self-adjointness problem.  Connes--Moscovici and Connes--Consani--Moscovici connect Sonin spaces to
prolate operators and zeta-zero asymptotics.  The endpoint asymptotic `(16)` and the triangle
argument proving `(22)`--`(26)` use classical ingredients.

Targeted searches did not locate the exact conjunction of the theta source-normal prime window,
cofinal Sonin partial unitary, coprime jump-Mellin phase frame, and critical Rees-grade law.
That conjunction does not add a new mathematical capability beyond the corpus's already-proved
BV tomography, Sonin aperture, and reflected-grade theorems, so it is classified as a bridge even
if the exact packaging is absent from literature.

## Gates

- [x] theta normal coefficient identified as a literal interval window
- [x] two-prime jump shell extracted before zero specialization
- [x] exact zero-mean essential-phase packet constructed
- [x] Sonin coupling and adjoint limits extended at paper level to jump amplitude
- [x] first Mellin normal computed locally uniformly with every jet
- [x] two source-only recurrent phase clocks constructed
- [x] common-zero set of the two boundary channels classified exactly
- [x] globally coprime desingularized frame proved
- [x] coprime frame realized by two explicit compact-BV windows
- [x] multiplicity-faithful rank-two BV/co-Poisson normal section proved
- [x] exact dilation grade law proved
- [x] hostile corpus collision audit: BV faithfulness and Sonin grade already proved separately
- [x] preliminary external search
- [ ] independent specialist literature audit
- [ ] Lean formalization of jump packet and Mellin normal theorem
- [ ] canonical undeconvolved source-action intertwiner
- [ ] closed graph continuity of both dagger and Mellin normal
- [ ] positive self-adjoint Xi spectral realization
- [ ] RH

## Lean route

Do not formalize only the elementary common-zero lemma.  The dependency-closed target must include
the actual jump packet and its boundary trace:

1. generalize the Sonin packet lemmas from the fixed smooth bump to a nonzero even
   `L1 intersect L2` amplitude with strict annulus support;
2. instantiate with the prime-log indicator shell and prove `(6)`--`(13)`;
3. formalize the locally uniform Mellin asymptotic `(16)` and clocks `(18)`--`(19)`;
4. prove the coprime frame `(22)`--`(26)` and scaling law `(28)`.

The existing formal parents already supply the compact Sonin correction, branch estimate,
coupling limit architecture, adjoint reversal, prime-log irrationality, and compact-torus
recurrence.

## Log

- 2026-08-01 — paper theorem proved; novelty and Lean audits remain.
