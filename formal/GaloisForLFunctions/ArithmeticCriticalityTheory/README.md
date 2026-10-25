# Arithmetic Criticality Theory (ACT)

Positive solutions, ground-state representations and criticality of the arithmetic jump operator
whose nonnegativity on odd tests is RH. ACT turns the sign question into an existence question
for a positive supersolution, proves that none exists in natural classes, and locates exactly
which quantity must carry the positivity instead.

Namespace `GaloisForLFunctions.ArithmeticCriticalityTheory`; umbrella `ArithmeticCriticalityTheory.lean`.

---

## 1. Place in the research

ACT owns the **aperture face** of the shared target: the restricted Weil ground energy $\mu(A)$,
which must never cross zero, and the gauge theory that would prove it. It distinguishes three
achievements: an identity for all tests, a positive certificate on a family, and a bound uniform
as the aperture grows. A contribution reports its unit: the aperture through which all profiles
are positive, or the rate $\sigma$ of a floor $\mu(A)\ge-Ce^{2\sigma A}$ (= strip $\tfrac12+\sigma$).

**Four pillars.** (1) A positive half-line gauge would certify positivity; the two-moment law
excludes it. (2) Subtracting the pole gives a gauge-independent zero form whose radical is the
theta span; what remains is a signed jump energy plus a calibrated variance. (3) Null sequences
forbid removing a Hardy weight, a prime rate, or any fraction of the variance. (4) Window gauges
give explicit floors at small aperture; a single bounded window carries no width information.

| Programme | Connection |
|---|---|
| [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md) | Theta source, Weil–Markov–pole split, grid tents carrying the $3/10$ window |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Positivity vs observation scale, blind directions, width |
| [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md) | Same odd theta gauges (`oddProfile`), collar transport, light-cone budget |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Prime side as incidences and centred divisor energies |
| [SquareRootThreshold](../SquareRootThreshold/README.md) | Ground-energy floor → lag bound → zero strip |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Pays reflected prime conductances; odd window to $181/500$ |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Exact shell-flux law, strict decrease and unique contact of $\mu$ |
| [ArithmeticCompensationTheory](../ArithmeticCompensationTheory/README.md) | Floor-loss transport bounds |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | All-parity critical deficit identity; Sobolev floors |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Non-Z-type obstruction = frustration on prime-sum edges |

Routes: ACT is itself a live route — for one fixed shift $a>0$, RH ⇔ the pole-free variation
inequality on even compact $C^2$ profiles. RW uses $\mu(A)$, its floors and ceiling; SRT reads the
same path at the centred difference test; Suzuki meets it in the window floor.

---

## 2. Why

**RH as a jump form.** Riemann's kernel $\Theta$ (even, positive, decreasing on $[0,\infty)$,
super-exponentially decaying, $\hat\Theta=\Xi$, $\int\Theta\cosh\frac u2=\tfrac12$). Then
$$\text{RH}\iff\forall v\text{ odd }C^2_c:\ \int\Theta\cosh(x/2)v^2\le E_{\text{arch}}(v)+E_{\text{prime}}(v),$$
jump energies at archimedean rate $\omega(t)=e^{-t/2}/(1-e^{-2t})$ and prime rate $\Lambda(n)n^{-1/2}$,
weighted by $\Theta(x)\Theta(x+t)$ (`riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg`).
So $Q(v)=$ jump energy $-$ potential must be $\ge0$ on odd tests; on even tests $Q(1)=-\tfrac12$.

**Why bounding fails.** Separate estimates lose constants, and the inequality has none to spare.
For finite Z-type jump forms, $Q\ge0$ ⇔ a positive supersolution exists (Allegretto–Piepenbrink),
via the **ground-state representation**
$E(\omega u)-\int\rho(\omega u)^2=$ (nonnegative remainder in differences of $u$) $+\int u^2\omega(L\omega-\rho\omega)$.
ACT develops this for the arithmetic operator. Vocabulary: *supercritical* (negative value),
*critical* (nonnegative, no Hardy weight), *subcritical* (Hardy weight exists).

---

## 3. Objects and language

**Coordinates.** Test coordinates ($F=\Theta v$) vs Doob coordinates ($u=v/\omega$, gauge $\omega$,
test coordinate $M=\Theta\omega$). Mixing them is the first trap.

**Gauges** (source $=\mathcal L_D\omega-\Theta\cosh(x/2)\omega$):

| Gauge | $M$ | Source |
|---|---|---|
| constant | $\Theta$ | $-\Theta\cosh(x/2)$ |
| translate $\tau_b$ | $\Theta(\cdot-b)$ | $-\Theta\cosh((x-b)/2)$ |
| shifted ground state $\omega_a$ | $m_a=\Theta(\cdot-a)-\Theta(\cdot+a)$ (odd, $>0$ on $(0,\infty)$) | $2\sinh\frac a2\sinh\frac x2\Theta$ |
| finite span / smeared | $\sum c_jm_{a_j}$, $\int\nu(c)m_c$ | $\sigma\sinh(x/2)\Theta$ |
| theta convolution | $\Theta*\varphi$ | $-\Theta(A_\varphi\cosh\frac x2-B_\varphi\sinh\frac x2)$ |
| profile gauge | any decaying $M$ | $-\Theta\cdot\mathcal WM$ |
| plateau gauge | $0\le M\le1$, window | purely archimedean on $2R<\log2$ |

*Harmonic* gauges (zero source) form the infinite-dimensional **harmonic theta span**; none is
positive on the half line.

**Jump structure.** Jump measure $dm=\omega(t)dt+\sum\Lambda(n)n^{-1/2}\delta_{\log n}$ (infinite total
mass: only differences converge). Pole-free Weil operator $\mathcal W$ with **harmonic identity**
$\mathcal W\Theta=\cosh(x/2)$ (`poleFreeWeilOperator_riemannKernelReal`). Generators on odd $\omega$:
two-sided $\mathcal L_D$ and folded $\mathcal L_N$ (reads reflected points through $\omega(|\cdot|)$);
difference = reflected mass $2\Theta(x)\int_{t>x}dm\,\Theta(t-x)\omega(t-x)$.

**Energies of $v=\omega u$.** Same-side $S$, reflected sum $P$, reflected difference $D$ (collar
$0<x<t$ = jumps crossing the origin); ground remainder $R_N=2S+P\ge0$; signed jump energy
$J_M(u)$ with conductances $M(x)M(x+t)$; variance energy $V_\mu$; cross energy $X$.

**Moments.** Pole moments $A=2\int F\cosh$, $B=2\int F\sinh$; jump-measure moment $\int M\,dm$;
reflected prime mass $P_M(x)$; collar mass $C_a$; collar ratio
$R(a)=2+2\int_0^\infty e^{-r/2}m_a/\sinh(a/2)>2$; half-line measure $\mu_a=m_a\sinh(x/2)$, mass
$\sinh(a/2)/2$; profile variance $V_a$; Weil jump density $\kappa(r)=\omega(r)-2\cosh(r/2)$ (strictly decreasing).

**Forms.**

| Form | Definition | RH |
|---|---|---|
| Markov $Q$ | $E-\int\rho v^2$ | $\ge0$ on odd |
| Zero form $Z$ | $Q-2(\int F\sinh\frac x2)^2$ | $\ge0$ on odd; annihilates odd theta span |
| Full zero form $\hat Z$ | $Q+2E_+E_-$ = Weil form | $\ge0$ on all real; annihilates whole theta span |
| Lorentz form | $(B^2-A^2)/2$ on theta span | explicit formula with zeros erased |
| Pole-free variation | $2S_a-D_a+V_a=Z(m_au)$ | gauge invariant |
| Pure jump form | $J_M+V_\mu=Z(\Theta\omega u)$ | $\ge0$ on even profiles, every smeared gauge |
| Cone form | $\hat Z(\Theta v)$, $v\ge0$ | no signed term |
| Ground energy $\mu(A)$ | inf Rayleigh quotient of $\hat Z$ on $(-A,A)$; $\mu_0$ pole-vanishing | $\mu(A)\ge0\ \forall A$ |

Lean entry points: `markovEnergy`, `zeroForm`, `fullZeroForm`, `twoSidedGenerator`,
`foldedGenerator`, `poleFreeWeilOperator`, `signedJumpEnergy`, `varianceEnergy`,
`ccmRestrictedWeilGroundEnergy`, `windowFloor`, `weilJumpDensity`.

---

## 4. Mechanisms

1. **Algebraic ground-state identities.** Difference, Neumann-sum and Dirichlet-sum identities;
   antisymmetric factor becomes $2\sum u^2\omega L\omega$. No derivatives.
2. **Folded representation and sufficiency.** $Q(\omega u)=R_N+2\int u^2\omega(\mathcal L_N\omega-\rho\omega)$;
   a positive folded supersolution gives RH. Only $\mathcal L_N$ has a nonnegative remainder.
3. **Equation of motion of $\Theta$.** $\mathcal W\Theta=\cosh$ ⇒ the source of every gauge is
   $-\Theta\mathcal WM$; $\omega_a$ has source $2\sinh\frac a2\sinh\frac x2\Theta$ but folded defect
   $2\Theta[\sinh\frac a2\sinh\frac x2-C_a]$, and the collar returns more than twice the source ($R(a)>2$).
4. **Two-moment obstruction.** For decaying $M$, folded source $/\Theta\to-2\int M\,dm$ at $0^+$ and
   $/(\Theta e^{x/2})\to-2\int_0^\infty M\cosh\frac r2$ at $\infty$; a nonnegative profile makes both
   positive ⇒ strict subsolution at both ends: **no positive folded supersolution**. Prime by prime and
   PNT-free at infinity. Sign-changing gauges with opposite moments have positive quadratic potential
   at both ends, but signed remainders. Extra jumps are seen only at infinity, iff $e^{-2a}+e^{-2\ell}<1$.
   The odd form is **not Z-type**.
5. **General-gauge representation.** $Q(\Theta\omega u)=J_M(u)+\int u^2Mg$, $g=-\mathcal WM$; harmonic
   gauges give pure signed Dirichlet forms. Plateau laws: on the span $Q\to2\sigma^2$; on translates
   the Lorentz form; the **harmonic theta span is the radical**.
6. **Two-sided representation; archimedean Z-type.** $Q(m_au)=2S-D+4\sinh\frac a2\int u^2d\mu_a$; the
   archimedean part satisfies $D_{\text{arch}}\le2S_{\text{arch}}$ (monotone Lévy density). Every
   failure of RH lives on **prime anti-diagonals** $x+y=\log n$.
7. **Light-cone law.** Archimedean surplus + profile variance $=2\iint(\kappa(s)-\kappa(s+2x))J_s(x)$ with
   $\kappa(s)-\kappa(s+2x)\ge4\sinh\frac x2\sinh\frac{x+s}2>0$ everywhere (no plastic threshold). Hence
   $Z(m_au)$ = positive light-cone continuum energy + prime part $(2S_{\text{prime}}-D_{\text{prime}})$, and
   RH ⇔ prime anti-diagonal mass $\le$ same-side prime + light-cone energy.
8. **Zero forms.** Source = pole term $8(\int u\,d\mu_a)^2$ + variance $V_a$; $Z$ gauge-invariant;
   single-shift completeness; in every odd gauge $Z=J_M+V_\mu$ (variance conductances positive across
   the origin); cone criterion with no signed term, sharp at the constant profile; capacity ratio → 1.
9. **Criticality.** No Hardy weight (odd sector and primitive hyperplane), every prime rate needed in
   full, variance-critical in every smeared gauge. Null sequences: plateau truncations of pole-free
   pairs — sign-changing, infinite-dimensional. Criticality forbids *subtracting*, not lossy floors.
10. **Shift averaging.** $\int_0^\infty Q(m_au)da$ with kernel $G(x-y)-G(x+y)$; heuristically blind to
    off-line zeros ($\Xi^2$ weight); single shifts are complete.
11. **Fold domination.** On monotone profiles $Q\ge$ source $-2\int u^2m_aW_a$; the weight criterion
    fails for large shifts by the other-pole moment.
12. **Finite model and frustration.** Finite Z-type forms: Allegretto–Piepenbrink via $v\mapsto|v|$.
    In orientation language Z-type = balance; the odd Weil ledger is frustrated exactly on prime-sum
    edges, with frustration index growing like the prime count at scale $e^{2A}$.
13. **Window gauges.** Plateau gauge below the first prime: $\hat Z\ge\frac3{40}\int F^2$ on
    $r<e^{-2}/2$. Curved/quartic gauges + even fold (free below the plastic threshold $\log\rho\approx0.2812$,
    paid by fold costs and hub Poincaré beyond) + odd plateau of AIP: $\hat Z\ge\frac1{5000}\int F^2$ on
    $[-\frac3{10},\frac3{10}]$. Odd sector reaches $181/500$ past $\frac12\log2$; mean-zero sector $7/20$.
    Window positivity is selective against $\zeta(s-a)\zeta(s+a)$.
14. **Ground-energy path.** Antitone; RH ⇔ $\mu(A)\to0$ ⇔ $\mu\ge0$; unconditional doubly exponential
    ceiling; floors $1/30$ ($A\le21/200$), $1/5000$ ($A\le3/10$), window floor = Suzuki main term $-\mu_1$;
    lag face: $\mu\ge-Ce^{2\sigma A}$ ⇒ width $\le\sigma$; converse in the archimedean ($H^1$-type)
    normalisation; multiplicative transport; bounded apertures are width-blind.

---

## 5. Pillar theorems

1. Folded sufficiency (`markovEnergy_phiDoob_eq_groundRemainder_add_potential`, `riemannHypothesis_of_foldedSupersolution`).
2. Two-moment law (`exists_origin_and_infinity_windows_foldedGenerator_lt_potential`).
3. Gauge-independent zero form; theta radical (`riemannHypothesis_iff_forall_odd_zeroForm_nonneg`,
   `abs_markovEnergy_add_harmonicPlateau_sub_le`, `exists_abs_markovEnergy_translatePlateau_sub_le`,
   `riemannHypothesis_iff_forall_fullZeroForm_nonneg`, `riemannHypothesis_iff_forall_nonneg_cone`).
4. Single-shift completeness (`riemannHypothesis_iff_forall_poleFreeVariationInequality`,
   `riemannHypothesis_iff_forall_smearedGauge_jumpForm_nonneg`).
5. Archimedean Z-type and light-cone law (`archReflectedDifferenceEnergy_le_two_mul_archSameSideEnergy`,
   `zeroForm_shiftedGroundState_eq_antisymmetric_weilJumpDensity_add_prime`,
   `riemannHypothesis_iff_forall_prime_le_antisymmetric_weilJumpDensity`).
6. Criticality (`riemannHypothesis_iff_nonneg_and_no_hardyWeight`, `riemannHypothesis_iff_isLeast_primeRate`,
   `exists_zeroForm_lt_mul_varianceEnergy`, `tendsto_capacityRatio_spanPlateau`).
7. Ground-energy path (`riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero`,
   `exists_ccmRestrictedWeilGroundEnergy_le_doubleExp`).
8. Small-aperture floors (`fullZeroForm_ge_of_support_le_threeTenths`, `windowFloor_eq_suzukiMainTerm`,
   `one_thirtieth_le_ccmRestrictedWeilGroundEnergy`).
9. Selectivity (`exists_even_shiftedPairZeroForm_neg`).

---

## 6. Traps

| Trap | Correct statement |
|---|---|
| Even positive supersolution on $\mathbb R$ | Impossible: $Q(1)=-\tfrac12$ |
| $\mathcal L_D$-supersolutions certify | Indefinite remainder; only $\mathcal L_N$ |
| Some folded supersolution exists | None in the positive decaying class |
| Sign-changing gauges help directly | Their remainders have signed conductances |
| One-sided prime sums via window PNT | Use the harmonic identity; PNT only for exact ratios |
| Total jump rate | Diverges; only differences converge |
| Perron–Frobenius on the odd sector | Reflected prime jumps break Z-type |
| Source = pole term | Source = pole term + variance; zeros live on mean-zero profiles |
| Shift is information | It is a gauge |
| Shift averaging gives a weaker target | Heuristically blind to off-line zeros |
| Hardy weight / lower rate / smaller variance | All critical |
| Criticality forbids allowances | A loss $C_\sigma e^{2\sigma r}$ gives the strip; uniform loss gives RH |
| A bounded-aperture certificate measures width | Width-blind at every level |
| $J_M$ alone positive in a positive gauge | Negative somewhere in every smeared gauge |
| Statements on the theta span are new | Pole/Lorentz facts; harmonic span is the radical |
| $\hat Z$ is a new form | It is the Weil form |
| Uniform margin in the capacity inequality | Ratio → 1 |
| Margin of $\mu(A)$ at large aperture | Doubly exponential ceiling; off RH $\to-\infty$ |
| Window floor is positivity at every small aperture | Positive only on short windows |
| Plastic threshold limits the light-cone budget | The antisymmetric $\kappa$-difference is positive everywhere |

---

## 7. Open problems

1. **Prime anti-diagonals.** RH ⇔ $D_{\text{prime}}\le2S_{\text{prime}}+2\iint(\kappa(s)-\kappa(s+2x))J_s$. Prove a
   prime-side inequality between anti-diagonal and same-side atoms plus the light-cone energy, or
   classify profiles where the anti-diagonal mass is unpaid. No slack anywhere.
2. **Coercivity on the quotient.** A Hardy weight / coercive norm for $Z$ on the quotient by the theta
   span.
3. **Monotone cone.** Replace the failed weight criterion using same-side terms away from the origin.
4. **Even sector beyond $3/10$ and across $\frac12\log2$.** Odd ($181/500$) and mean-zero ($7/20$)
   sectors already cross; the unpaid case is the pole directions on even tests.
5. **Selectivity** beyond the shifted pair; separate universal gauge algebra from identities using
   the equation of motion of $\Theta$.
6. **Graded no-crossing.** $\mu(A)\ge-Ce^{2\sigma A}$ for one $\sigma<\tfrac12$ in the $L^2$ normalisation
   along an unbounded aperture set; pass from the $H^1$ datum of the off-line zero sum to $L^2$.
   (In the CCM form-domain normalisation the rate equals the width unconditionally, and polar and
   full $L^2$ rates coincide — ACCE `formGroundEnergyRate_eq_zetaZeroWidth`,
   `groundEnergyRate_eq_polarGroundEnergyRate`; the open case is the physical $L^2$ normalisation.)
7. **Transport in aperture.** Quantitative control of the signed new-prime correlation in ACCE's
   frozen-prime decomposition of $\mu(a)-\mu(b)$; positive floors must respect the doubly exponential ceiling.
8. **Frustration → ground energy.** Least global payment of frustrated prime-sum edges at aperture
   $A$ as a $\mathbb Z/2$ gauge ground energy with full weights; does it equal $\mu(A)$?
9. **Signed gauge certificates.** A profile with opposite-moment conditions, controlled quadratic
   potential in between, and a bounded signed remainder; a quantitative Harnack across growing prime shifts.

---

## 8. Tools

Built: ground-state algebra in arbitrary gauges (folded, two-sided, general); equation of motion
of $\Theta$ and exact sources; moment laws at both ends; zero forms, theta radical, cone criterion;
criticality calculus (plateau/Lorentz null sequences); light-cone antisymmetric law; window gauges
(plateau, quadratic, quartic, curved), even fold, fold costs, hub Poincaré; ground-energy floors,
ceiling and transport.

To build: signed gauge with global nodal-remainder control; quotient coercivity; all-profile window
past $\frac12\log2$; arithmetic Harnack across prime shifts; $H^1\to L^2$ passage for the path.

---

## 9. Working conventions

- State coordinates (test vs Doob, $M=\Theta\omega$), gauge, and scope (single shift, span, convolution
  class, all profiles).
- Search the Weil-form lanes first; `oddProfile a = m_a/(2 sinh(a/2))` and `oddSinhPotential` are the
  THIM/CHMD names for the same objects.
- Exact identities before asymptotics (harmonic identity, exact sources, collar Fubini, sinh
  moments, shift integrals, Lorentz law); PNT only for exact limits.
- Lean: `integral_add`/`integral_sub` need lambda-typed integrability; use
  `simp only [Set.indicator_apply, mem_Iic]` inside `if`; `linarith only [...]` in integral-heavy
  contexts; Hadamard division via `smoothCoordinateQuotient`.
- Consequences of positivity are stated as equivalences or limits of unconditional identities.
