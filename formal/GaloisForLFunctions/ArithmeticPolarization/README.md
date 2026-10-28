# Arithmetic Polarization (APol)

Namespace `GaloisForLFunctions.ArithmeticPolarization`; umbrella `ArithmeticPolarization.lean`.

**Question.** Over $\mathbb F_q$ the sign of the explicit formula comes from a *polarization*: the theta divisor makes the Rosati
trace $\tau(\xi\xi')$ an intersection number of effective classes — a trace form at once **positive** and **equivariant** under
Frobenius. Over $\mathbb Z$ every other layer of Weil's argument exists, and every positivity built from invariance is isotropic
at off-line zeros. What could play the polarization over $\mathbb Z$, by which mechanism can a positivity be a theorem about a
structure rather than a consequence of a symmetry, and what does each mechanism give?

**Organizing principle.** *Positivity excludes a pair only through an indefinite fibre.* A symmetry hyperbolic at the pair
makes every invariant positive fibre isotropic; a symmetry elliptic at the pair makes the fibre definite (positive on one
sector, negative on the other); a collision turns the pair into a determinant, positive and sign-blind.

**Answer in one paragraph.** The test space of $\zeta$ carries two forms: Weil's form $W$ (Hecke-equivariant; positivity = RH)
and the collided form $D=\sum_\rho m_\rho|\hat f(\rho)|^2$ (positive, coercive = log-Sobolev norm; equivariance = RH), with $\Re W=D-\Delta$,
$\Delta$ an off-line defect uniform in depth. $D$ is not computed by the explicit formula; the global collision has no analytic
carrier. The only non-hyperbolic localizers are the point reflections $\sigma_\gamma$ (the functional equation conjugated by the
archimedean flow): elliptic localization is twisting; its odd sector forces, paying with gauge-charged weights and a
conductor $\log\gamma$. Positive completions are couplings, which collide evenly and hit the Fejér barrier. Lattice counts on
the square of $\operatorname{Spec}\mathbb Z$ collapse to the diagonal or factor.

---

## 1. Place in the research

The B-tier obstacles are one missing object: a **polarization of the correspondence surface of $\operatorname{Spec}\mathbb Z$** — positive by a
theorem about the structure (counting, or a non-hyperbolic localizing symmetry), seeing the sign of prime-power atoms, with
an exterior part colliding conjugate zeros without an ordinate-dependent conductor.

| Programme | What APol takes / adds |
|---|---|
| ArithmeticCorrespondencePositivity | Local form, boosts, determinant/Rosati degrees, real-anchor law, escape kernels / adds elliptic and collided types, the two forms, the leading-line law, collision parity |
| ArithmeticCorrelationGeometry | Gauge torus, charged statistics / adds charged weights $\Lambda(n)\cos(\gamma\log n)$; first gauge charge as a twist |
| ArithmeticPositiveDuality | Positive Poisson pairs, $\kappa=1$ collapse / adds rigidity of coupled classes, capacity of intrinsic charge |
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | Scaling surface, curve data, universal floor law; Rosati = orbit Hodge index |
| StripBochnerWeilForcing, MultiplicativePositivityGeometry | Completed positive systems; PD functions |
| arithmetic-positivity-theory, SquareRootThreshold | Single-height detection, conductor horizon, window certificates |
| BiarithmeticGaugeGeometry | Coupled-class non-rigidity; central vanishing ceiling |
| `Zeta23`, `RHTower` | `ZeroConfig`, `Z.W`, explicit formula, $\xi$ |

---

## 2. Objects and language

| Over $\mathbb F_q$ | APol object | Lean |
|---|---|---|
| $(\operatorname{End}J\otimes\mathbb Q,',\operatorname{Tr})$ | algebra with involution and polarization | `IsPolarization` |
| Frobenius spectrum | reflection-closed spectrum | `ReflSpectrum`, `Zeta23.ZeroConfig` |
| Rosati trace form | Weil's form $W(f,f)=\sum m\hat f(\rho)\overline{\hat f(\rho^*)}$ | `Z.W` |
| — | collided form $D$; off-line defect $\Delta=\sum\frac m2|\hat f(\rho)-\hat f(\rho^*)|^2$ | `collidedForm`, `offLineDefect` |
| Frobenius on a pair | local type: boost, swap, rotation; collided | `localForm` (ACP) |
| — | reflection-commuting affine maps $s\mapsto\tfrac12+\lambda(s-\tfrac12)+i\kappa$ | `affine`, `rosatiRefl` |
| — | point reflection $\sigma_\gamma(s)=1+2i\gamma-s$; test localizer | `sigma`, `sigmaTest` |
| — | twist $e^{-i\gamma u}f$; shifted configuration $Z-i\gamma$ | `twist`, `shiftConfig` |
| $\Lambda^2H^1$ | exterior point $\rho+\rho'-\tfrac12$; collided point $2\Re\rho-\tfrac12$ | `extPoint` |
| $D\otimes\chi$ | coupled datum | `coupleDatum` |
| — | leading-line sum; cosine polynomial | `leadingSum`, `cosPoly` |
| — | coupled class `HeightCoupledSystem 2 1 1 γ` | `CoupledRigid` |
| $h^0$ on $C\times C$ | lattice zeta functions on $\mathbb Z^2$ | `rankOne_latticeZeta` |

**Words.** *Polarization* ($\tau(v'v)$ real, $\ge0$, zero only at 0); *anisotropic*; *equivariant* vs *collided* form; *elliptic
localizer* $\sigma_\gamma$; *even/odd sector* (blind/forcing half); *conductor* (shift of the digamma density); *conductor horizon*;
*charged weight*; *positive completion* (harmonic lift with a nonnegative cosine polynomial); *collision parity* (even for
couplings, odd for exterior squares); *diagonal collapse*.

---

## 3. Mechanisms

1. **Polarization law**: in a $*$-algebra a similitude $\xi'\xi=c$ has $|\mu|^2=c$ at every anisotropic eigenvector; a polarization
   makes all eigenvectors anisotropic.
2. **Polarization identity** $2\Re(u\bar v)=|u|^2+|v|^2-|u-v|^2$ summed over zeros: $\Re W=D-\Delta$.
3. **Gårding and Bessel**: the explicit-formula density + compactness of low frequencies make $D$ coercive and equivalent to
   $\int|\hat f|^2\log(|\sigma|+4)$ at every aperture; $W$ has at most $2AT_0K/\pi$ negative orthonormal directions.
4. **Affine classification**: maps commuting with $s\mapsto1-\bar s$ sending an off-line point into its pair are only the identity and $\sigma_\gamma$.
5. **Definite sectors**: on $G\circ\sigma_\gamma=\pm G$ the local form is $\pm2|G(\rho)|^2$; sectors are twists of even/odd tests.
6. **Dihedral dilemma**: a boost and a swap at one pair blind it; twisted symmetric Hecke symbols are scalar on the pair.
7. **Twist identity** $Z.W(e^{-i\gamma u}f,e^{-i\gamma u}g)=(Z-i\gamma).W(f,g)$; the twisted explicit formula has shifted poles, phased weights,
   shifted digamma (conductor).
8. **Collision**: $\rho+\bar\rho-\tfrac12=2\Re\rho-\tfrac12$ doubles depth, forgets the ordinate; analytic functions vanishing on all collided
   points of an infinite configuration vanish.
9. **Laplace–Bochner for polar configurations**: positive vertical sections ⇔ the exponential polynomial has nonnegative real part
   on $t>0$; Fejér–Riesz on commensurable lines; Bohr large returns ⇒ leading-line law.
10. **Lattice zeta of the square**: rank-one lattices see $\zeta(s_1+s_2)$, $\mathbb Z^2$ sees $\zeta(s_1)\zeta(s_2)$; on the reflection plane a
    modulus square $|\xi|^2$.

---

## 4. Pillar theorems

1. **Polarization law** (`normSq_eq_of_hasEigenvalue_of_polarization`, `ReflSpectrum.rosatiForm_nonneg_iff_unitary`).
2. **The two forms** $\Re W=D-\Delta$; Hecke isometries of $W$; $D(T_Lf)$ grows with depth (`re_W_eq_collided_sub_defect`,
   `collidedForm_second_difference`).
3. **RH = coincidence of the two forms = equivariance of $D$**; $D$ is the log-Sobolev norm at every aperture; $W$ has finitely many
   negative directions per aperture (`riemannHypothesis_iff_W_eq_collided`, `riemannHypothesis_iff_collided_hecke_invariant`,
   `collidedForm_equiv_logSobolev`, `card_negative_orthonormal_le`).
4. **Elliptic localizers are the point reflections** (`affine_mem_pair_iff`, `sigma_eq_tau_comp_fe_comp_tau`).
5. **Dihedral dilemma** (`hecke_swap_blind`).
6. **The price of elliptic localization**: every localizer off the real axis is gauge charged; below the conductor horizon
   positivity is source-blind (`exists_vonMangoldt_pos_cos_neg`, `elliptic_sector_nonneg_below_conductor_horizon`).
7. **The forcing half**: odd-sector positivity forbids an isolated off-line zero at aperture $\asymp(1/2\delta)\log\log\gamma$; the even sector
   never forces (`odd_sector_nonneg_forces_offLine_companion`, `even_sector_summand_nonneg`).
8. **Collision law and parity**: global collision has no analytic carrier; couplings collide evenly (kernel counts are modulus
   squares); escape kernels are Pick forms of the conjugate exterior divisor (`zeta_global_collision_not_analytic`,
   `couple_detDeg_eq_normSq`, `escapeForm_eq_exteriorCauchyForm`).
9. **Leading-line law and Fejér barrier**: no positive multiplier removes a lifted divisor (`leadingSum_nonneg`, `not_removes_lifted_divisor`).
10. **Coupled rigidity would exclude zeros** at its ordinate (`xi_ne_zero_of_rigid`) — but the class is not rigid (BGG).
11. **Twists are rate neutral; diagonal collapse; the first gauge charge is a twist** at $\pi/\log2$ on the first-prime window
    (`twisted_growth_iff`, `xi_mul_xi_reflection_plane`, `weilFullFunctional_liouville_eq_twist`, `not_twist_flips_two_and_three`).

---

## 5. Traps

| Trap | Truth |
|---|---|
| An elliptic symmetry gives a positivity that excludes a zero | Fibres are definite; only the odd sector forces |
| The functional equation is the elliptic localizer | Only at ordinate 0; at $\gamma$ it is its conjugate by the archimedean flow |
| Elliptic localization is free | Charged prime side, conductor $\log\gamma$ |
| Hecke separation combines with elliptic symmetry | A boost and the swap at one pair blind it |
| The polarization over $\mathbb Z$ is missing | $D$ exists and is positive; its equivariance (computation) is missing |
| $W\ge0$ is weaker than $W=D$ | Equivalent for $\zeta$; the defect is the whole content |
| A collision producing a real point can be counted | Couplings collide evenly |
| Squaring the explicit formula collides all pairs | No analytic function carries the global collision |
| A two-variable lattice count is a surface count | It collapses to the diagonal or factors |
| A positive completion of a charged weight removes the quartet | Leading line $2m\cos\theta P(\theta)$ is negative somewhere |
| Twisting amplifies | It moves ordinates and keeps every depth |
| Escape positivity excludes zeros | Escape kernels are collided forms, positive by construction |
| The Liouville twin differs arithmetically on the first window | It is $\zeta$ at height $\pi/\log2$ up to archimedean/polar terms |

---

## 6. Open problems

1. **Compute the defect**: an arithmetic structure computing $D$ or $\Delta$ (the global collision) without the zeros; it gives $W\ge0$
   as $D\ge\Delta$.
2. **The forcing half beyond the conductor horizon**: odd-sector positivity of the twisted form between $\log\log\gamma$ and $\log\gamma$.
3. **Odd collisions over $\mathbb Z$**: a two-variable structure colliding with odd multiplicity at every ordinate at once.
4. **Central ceiling of the coupled class** beyond rational deformations (for rational ones it is equivalent to no zeros at $\gamma$).
5. **A two-variable section count** with rank growing in the class and Riemann–Roch whose quadratic term is Weil's form.
6. **Separating aperture of the first twin**: compare $W_\zeta(f)$ with $W_\zeta(e^{-i\pi u/\log2}f)+\Delta_{\rm arch}+\Delta_{\rm pole}$ on the odd window.
7. **Equivariant positive forms from counting**, and their relation to $D$.

## 7. Tools to build

A computation of $\Delta$ from arithmetic; odd-collision structures; a two-variable section theory with growing rank.

## 8. Contribution standard

Unconditional; name the mechanism (equivariant, positive, elliptic, collided, counting, charged) and the Weil layer; state
local type at off-line pairs and the forcing sector; state gauge charge, conductor and collision parity; report on the
battery (completed-system strays and their lifts, Beurling systems, Siegel family, golden datum, complex fake, dominated
and flipped twins); keep identities apart from signs. Positivity forces only through indefinite fibres; elliptic means
definite, not positive; localization in height is a twist and costs a conductor; a completion is a coupling and collides
evenly; $D$ exists, its computation is the problem.
