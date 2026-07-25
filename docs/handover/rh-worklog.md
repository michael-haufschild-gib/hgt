# RH long-running attack — working log

Standing goal: prove or disprove RH. Multi-session. This file is the compaction-safe memory.
Append new cycles at EOF. Never delete a dead end — it is the most valuable content here.

## Current position (cycle 5 open, 2026-07-25)

Frontier object: the truncated Weil quadratic form. External SOTA as of July 2026:

- Connes–Consani, *Weil positivity and trace formula, the archimedean place*, arXiv:2006.13771
  (Selecta Math 2021). Test function support `(1/2,2) ⊂ ℝ*_+`, i.e. `u ∈ (−log 2, log 2)`;
  `g = h⋆h̃` then lives on `(−log 4, log 4)` so primes 2 and 3 DO enter. Positivity proved via
  compression of the scaling action, prolate spheroidal wave functions, Toeplitz control.
- Connes–van Suijlekom 2025: truncated Weil operator, ground-state eigenvalue as an RH meter.
- Connes–Consani–Moscovici 2025: rank-one perturbation of the scaling spectral triple,
  Euler product over `p ≤ c`; numerics at `c = 67`. Connes 2026: first 50 zeros at `c = 13`.
- arXiv:2605.20224 high-precision zeros via the truncated Weil form.
- arXiv:2607.02828 finite Guinand–Weil dictionary + archimedean tail order.

So: `RH ⟺ Q_c ⪰ 0 for all prime cutoffs c`, and the unconditional frontier is a *finite* `c`.

## Established in-repo (own results, machine-checked)

| label | statement | status |
|-|-|-|
| A | CCM four-unit source budget is a class invariant of the critical clock; `rfl` connector to the Exp(1) functional | done, closes C1–C50 |
| H | `Λ≥0` + exact Riemann FE + simple pole, completion NOT entire ⟹ off-line zeros exist | done |
| J | `Λ≥0` + exact Riemann FE + entire order-1 completion, pole order 3 ⟹ off-line zeros exist | done |
| K,K′,K″ | rigidity of (H1)–(H4) for countable absolutely-summable cone deformations of ζ | superseded by M |
| N | ceiling: linear `Λ`-positivity can never cancel `e^{u/2}`; caps at PNT strength | done |
| 6.1 | monotone Möbius positivity `T^{-1}g ≥ (2−π²/6)g` | done |

## Cycle 5 — the Landau upgrade (Theorem M)

**Discovery.** K″ needed (i) `Σ|t_j| < ∞`, (ii) attainment or Landau-with-summability, (iii) the
deformation to be a countable cone combination. ALL THREE ARE REMOVABLE. Replace the
leading-frequency/Besicovitch argument by Landau's theorem for Laplace–Stieltjes transforms of
nonnegative measures, applied to the deformation measure itself.

Set-up (log coordinates, `dΨ = u·dΠ_*`, `M(s)=∫₀^∞ e^{-su}dΨ = −F'/F`):

```text
dΨ_ζ(u) = [ e^u − Σ_ρ e^{ρu} − 1/(e^{2u}−1) ] du        (distributional, u>0)
so (H1) for a divisor Z ⟺  Σ_{ρ∈Z} e^{ρu} ≤ e^u − 1/(e^{2u}−1)  as distributions.
Writing ρ = ½+w:  S(u) := Σ_{w∈W} e^{wu} ≤ β(u) := e^{u/2} − e^{−u/2}/(e^{2u}−1).
```

`β(u) ~ e^{u/2}` at ∞ and `~ −1/(2u)` at `0+`. A single off-line quadruple costs
`4cosh(au)cos(γu) ≲ 2e^{au}` with `a<½`, hence is *affordable* against `e^{u/2}` — this is
Theorem N again, and it is why no size argument can work.

**Theorem M (unconditional deformation rigidity).** Let `ν ≥ 0` be a nonzero Borel measure on
`(0,∞)` whose Laplace transform `N(z)=∫e^{-zu}dν` is meromorphic on ℂ, with abscissa `σ_c`.
Then either `σ_c = −∞`, or `z=σ_c` is a **real pole** of `N` with positive leading coefficient.
If moreover `N` is antisymmetric (`N(1−z) = −N(z)`) and `N(σ)→0` as `σ→+∞`, the case
`σ_c = −∞` forces `N ≡ 0`, because `|N(z)| ≤ N(Re z)` for `ν ≥ 0` makes an entire `N` bounded.

**Corollary.** Let `F` satisfy (H2) and `dΨ_F ≥ dΨ_ζ`. Then `ν = dΨ_F − dΨ_ζ ≥ 0`, and its
transform `N = M_F − M_ζ` is antisymmetric and meromorphic. If `ν ≠ 0` the real pole at `σ_c` is:
- `s=1` ⟹ `ord₁F ≥ 2` ⟹ **(H4) fails** — this is exactly Theorem J (`res = 2`, pole order 3);
- a real pole of `F` in `(0,1)` ⟹ **(H3) fails** — this is exactly Theorem H (poles at `½±c`);
- a real zero of `ζ` in `(0,1)` — impossible (Cor. 3.1);
- `s = −2k` with `F(−2k) ≠ 0` ⟹ the completion inherits the `Γ(s/2)` pole ⟹ **(H3) fails**;
- `s = 0`: residue `= ord₀ζ − ord₀F = −ord₀F ≤ 0`, excluded by positivity of the leading coeff.

Hence **(H1)–(H4) ⟹ `F = ζ`** on the whole class `dΨ_F ≥ dΨ_ζ`. No summability, no attainment,
no cone structure. Supersedes K, K′, K″ and *explains* H and J: both are forced to spend a real
pole, and the two admissible real poles are exactly the two hypotheses they violate.

## Dead ends recorded this cycle (do not re-attempt)

1. **Weil-form even/odd split as a lever.** For real `h`, `Ĝ(w)=Ĥ(w)Ĥ(−w)=Ĥ_e(w)²−Ĥ_o(w)²`, so
   `Q(h)=A(h_e)−B(h_o)` with NO cross terms. Structurally clean; useless as a lever, because
   `A(f)≥0 ∀ even f` is *by itself* equivalent to RH (localize `f` on one off-line quadruple).
2. **`dN ≥ 0` positive-definiteness of `F`.** `Σ c_ic̄_j F(s_i+s̄_j) ≥ 0` needs
   `Re(s_i+s_j) > 1` pairwise, so it only ever evaluates `F` where `F ≠ 0` anyway. Reduces to
   Nyman–Beurling; no new information.
3. **Deforming ζ's divisor by moving zeros.** Any continuous correction must be `≥0` a.e. because
   `dΨ_ζ` is atomic, hence `≥0` everywhere, hence killed by Theorem M. Rules out ALL
   move-a-zero constructions, including infinite non-summable ones. (This is what makes
   Conjecture L below require a *from-scratch* system.)
4. **Hamburger's theorem is not a shortcut.** (H2)+(H3)+(H4) for an *ordinary* Dirichlet series
   already forces `F = cζ` (Hamburger 1921), so "axioms ⟹ RH" is circular in that category. The
   Beurling category is the only one where the question has content — generalized primes sit at
   non-integer logs, so Hamburger does not apply.
5. **Intrinsic Landau on `dΨ_F` itself.** The abscissa is always the pole at `s=1`, whose residue
   is `+1 > 0`; it swamps every zero. Confirms Theorem N from a second direction.

## Open: Conjecture L (the decisive dichotomy)

> **Conjecture L.** There exists a Beurling generalized number system with `dΠ ≥ 0`, the exact
> Riemann functional equation, completed function entire of order one, a **simple** pole at
> `s=1`, and zeros off the critical line.

- **L true** ⟹ (H1)–(H4) provably cannot imply RH; the whole axiomatic lane is closed for good and
  the independence table becomes complete.
- **L false**, i.e. (H1)–(H4) ⟹ all zeros critical, ⟹ **RH is proven**, since ζ satisfies all four.

By Theorem M the counterexample cannot be any deformation of ζ: it must be built from scratch,
controlling a full order-one symmetric divisor with `S(u) ≤ β(u)`.

---

## Cycle 5 results (banked 2026-07-25)

### Theorem J' — pole order two already permits off-critical zeros

For `w in (0,1/2)`:

```text
d(u) = e^u + 1 - e^{(1/2+w)u} - e^{(1/2-w)u} = (e^{u/2} - e^{wu})(e^{u/2} - e^{-wu}) >= 0
N(s) = 1/(s-1) + 1/s - 1/(s-1/2-w) - 1/(s-1/2+w)        (reflection antisymmetric)
F(s) = zeta(s)*((s-1/2)^2 - w^2)/(s(s-1))
(s(s-1))^2 * pi^{-s/2} Gamma(s/2) F(s)/2 = xi(s)*((s-1/2)^2 - w^2)   (entire, order 1, s->1-s)
```

Lambda >= 0, exact Riemann FE, entire order-one completion, pole of order **two** at s=1, and the
two zeros 1/2 +- w are **real** — a Landau-Siegel zero. Prime measure nonnegative via Lemma 6.1,
because d(u)/u is nondecreasing, which reduces to monotonicity of t -> (t-1)e^t on [0,inf).
At w = 1/2 the quadratic degenerates to s(s-1) and F = zeta. Strictly improves Theorem J
(order 3 -> order 2) and produces a *real* stray, the strongest possible failure of RH.

### Theorem O — the pole-order budget law

Trace condition h(0) = sum_j t_j = 0 (local finiteness of Pi at x=1) plus (H3) (only w = 1/2 may
carry a positive coefficient) give

```text
ord_1 F = 1 + t_{1/2} = 1 + sum_{j != 1/2} |t_j|  =  1 + total inserted multiplicity
                                                     counted by FREQUENCY PAIRS.
```

Because cosh(wu) = cosh(-wu) a frequency is the pair {w,-w}, and

```text
{w,-w} = {conj w, -conj w}   <=>   Im w = 0  or  Re w = 0,
```

i.e. exactly when the inserted zeros are real or critical. Hence

| ord_1 F | what is possible |
|-|-|
| 1 | nothing: F = zeta (Theorem M) |
| 2 | one inserted pair 1/2 +- w, w real or purely imaginary — real strays occur (J') |
| >=3 | genuinely complex off-critical quadruple (J) |

A real stray costs exactly half a complex one. This is the sharp quantisation of "how far a
Lambda-positive system with the Riemann FE may stray from the critical line".

### Theorem M — unconditional deformation rigidity

Landau exchange identity (proved in ENNReal, so no convergence hypothesis):
int_0^inf e^{-(a-t)u} dnu = sum_k (t^k/k!) int_0^inf u^k e^{-au} dnu. Radius of the moment series
at a is exactly a - sigma_c, so the transform has no continuation past sigma_c; meromorphy implies
sigma_c is a real pole with positive leading coefficient. Entire case killed by |N(z)| <= N(Re z)
plus Liouville. Corollary: (H1)-(H4) imply F = zeta for every system with dPsi_F >= dPsi_zeta.
Supersedes K, K', K''.

Machine-verified (standard axioms only):
`RHTower/PoleOrderTwoRealStray.lean`, `RHTower/LandauAbscissaRigidity.lean`.

### DEAD END (structural, important) — the axiomatic lane is circular-or-false

(H1)-(H4) cannot prove RH, for a reason independent of how hard one works:

- If the Beurling category has a Hamburger-type **uniqueness** theorem — (H1)-(H4) implies
  F = c*zeta — then "(H1)-(H4) implies RH" is *equivalent* to RH, i.e. **circular**. Theorem M
  proves uniqueness on the whole domination class, so this is the likely truth.
- If instead a from-scratch counterexample exists (Conjecture L), the lane is **false**.

Either way no proof of RH comes out. Any lane that can reach RH must use input not shared by an
abstract axiom system that zeta also satisfies. **Do not spend further cycles on axiom
independence.**

Corollary worth keeping: zeta is *isolated* in the space of (H1)-(H4) systems dominating it, so no
homotopy/flow method (heat flow included) can connect zeta to a simpler object inside the axiom
class.

### Cycle 6 target

lambda(l) := inf{ W(h * h~) : supp h subset [-l,l], ||h||_2 = 1 } is nonincreasing; lambda(l) >= 0
for l <= log 2 (Connes-Consani 2020); RH <=> lambda(l) >= 0 for all l. **Target: a self-improvement
law** — positivity at scale l implies positivity at scale l + c — which would give RH by
induction; or the exact obstruction to one.

---

## Cycle 6 (2026-07-25) — Theorem P, self-correction, and Theorem R

### Theorem P — every strip divisor is realizable

Master inequality: for |a| <= 1/2, u >= 0,

```text
cos(g u)(e^{(1/2+a)u} + e^{(1/2-a)u}) = 2 e^{u/2} cos(g u) cosh(a u)
                                      <= 2 e^{u/2} cosh(u/2) = e^u + 1,
```

because cosh is even and increasing on [0,inf). So the unit correction attached to ANY point of the
closed critical strip is a nonnegative measure — **no restriction on the ordinate**. Hence for any
finite multiset Z in the closed strip, closed under s -> 1-s and conjugation, with even multiplicity
at s = 1/2 and |Z| = 2m,

```text
F(s) = zeta(s) * prod_{rho in Z}(s-rho) / (s(s-1))^m
```

satisfies (H1),(H2),(H3) with ord_1 F = 1 + m. The disc condition |s - 1/2| <= 1/2 additionally
gives dPi >= 0 (genuine Beurling system) via Lemma 6.1.

### SELF-CORRECTION: the budget law has a refund term

Cycle 5's Theorem O claimed "complex stray needs ord_1 >= 3". WRONG as stated. A deformation may
also REMOVE a zeta zero: that is a POSITIVE coefficient at a non-1/2 frequency, admissible because
zeta already vanishes there so no pole appears. It refunds one unit. General law:

```text
ord_1 F - 1 = I - R      (inserted minus removed, by frequency pairs)
```

Theorem O is correct only under the insertion-only hypothesis — which is exactly the hypothesis
`t i <= 0` already present in the Lean statement `poleOrderBudget`, so the formalization was right
and only the prose over-claimed.

### Theorem R — the refund is effective

gamma = ordinate of any critical zeta zero (Hardy, unconditional), 0 < a <= 1/4,
rho = 1/2 + a + i gamma:

```text
d(u) = (e^u+1) + 2 e^{u/2} cos(gamma u) - 2 cos(gamma u)(e^{(1/2+a)u} + e^{(1/2-a)u}) >= 0
F(s) = zeta(s)(s-rho)(s-bar rho)(s-1+rho)(s-1+bar rho) / [ ((s-1/2)^2 + gamma^2) s(s-1) ]
```

(H1),(H2),(H3), ord_1 F = 2, zeros neither real nor critical. Completion
xi(s)*quartic/((s-1/2)^2+gamma^2) is entire because xi vanishes at 1/2 +- i gamma.
Proof: 1 - 2cosh(au) <= -1 < 0 and cos <= 1 give h >= cosh(u/2)+1-2cosh(au)
= 2cosh^2(u/4) - 2cosh(au) >= 2cosh(u/4)(cosh(u/4)-1) >= 0.
Sharp range |a| <= 1/(2 sqrt 2) by Taylor coefficients 4^{-n} - 2a^{2n} >= 0; numerically h < 0 at
a = 0.4, confirming sharpness. NOTE: dPi >= 0 is NOT established for Theorem R (the +cos(gamma u)
term has negative Taylor coefficients), so it is a Lambda-positive FE solution, not certified as a
Beurling system.

### Sharp threshold (supersedes the graded picture)

```text
ord_1 F = 1  <=>  F = zeta                                     (Theorem M)
ord_1 F = 2  already admits EVERY kind of off-critical zero:
               real pair, unrefunded                           (Theorem J')
               genuinely complex quadruple, refunded once      (Theorem R)
```

No intermediate regime. The simple pole is not one graded hypothesis among many — it is the entire
remaining content. ord_1 F = 1 cannot be reached by a refund: the trace condition would leave no
positive coefficient at w = 1/2, and Theorem I forbids a correction whose top real part is attained
only by non-real frequencies with negative coefficients.

Machine-verified: `RHTower/StripDivisorRealization.lean`, `RHTower/RefundedComplexStray.lean`.

### DEAD END recorded — truncated Weil self-improvement is a restatement

lambda(l) >= 0 for a given finite l is, heuristically but robustly, equivalent to RH up to height
~ e^{2l}: detecting an off-line zero at height gamma_0 needs frequency resolution pi/l below the
mean gap 2pi/log(gamma_0/2pi), i.e. l >~ (log gamma_0)/2. So a provable self-improvement law
lambda(l) >= 0 => lambda(l+c) >= 0 would prove RH from a finite verification. It is therefore
exactly as hard as RH, not a lever. Do not pursue "bootstrap in l" again.

---

## Cycle 7 (2026-07-25) — positivity certificates for the reflection cone

### The master certificate (exact identity, replaces all earlier estimates)

For all real al, a, gam, u:

```text
cosh(al u) - cosh(a u) cos(gam u)
      = 2 sinh(((al+a)/2) u) * sinh(((al-a)/2) u)  +  2 cosh(a u) * sin^2((gam/2) u).
```

For |a| <= al both summands are separately nonnegative on all of R, because
sinh(p u) sinh(q u) >= 0 whenever p,q >= 0 (both factors carry the sign of u). Theorems H, J, J',
P all become corollaries of this single identity. Positivity is now witnessed structurally, and the
witness splits a cone element into a purely hyperbolic and a purely oscillatory part.

### The refunded certificate

```text
cosh(u/2) - (2cosh(a u) - 1) cos(gam u)
      = [cosh(u/2) + 1 - 2 cosh(a u)]  +  2 (2 cosh(a u) - 1) sin^2((gam/2) u),
```

first bracket = 2[cosh^2(u/4) - cosh(a u)] >= 0 for |a| <= 1/4; refund weight positive by
(2cosh(a u) - 1) e^{a u} = (e^{a u} - 1/2)^2 + 3/4.

### New open problem: Positivstellensatz for the reflection cone

C = { h = sum_j t_j cosh(w_j u) : h >= 0 on R }. Is every h in C a finite sum of Hermitian squares
of exponential polynomials?

- all w_j real: YES. z = e^{delta u} makes h a Laurent polynomial nonneg on (0,inf);
  Polya-Szego gives h = sigma_0 + z sigma_1, and z = (e^{delta u/2})^2 is a square.
- all w_j purely imaginary: YES, Fejer-Riesz.
- mixed: the frequency group closure is the CYLINDER R x S^1, a genuinely 2-dimensional real
  variety, where SOS is strictly smaller than nonneg in general (Hilbert 1888; Rudin's 2-variable
  counterexamples to Fejer-Riesz). OPEN whether C escapes.
  A negative answer => Lambda-positivity is NOT semidefinite-representable => no fixed-degree SDP
  relaxation can decide it. That is a structural limitation on every numerical approach to the
  Beurling constraint, including Galerkin/SDP truncations in the CCM lane.

Machine-verified: `RHTower/ReflectionConeCertificate.lean`.

### Cycle 8 target

Settle the mixed case of the Positivstellensatz: either produce an SOS algorithm for C, or an
explicit h in C that is provably not a sum of Hermitian squares. The latter is the more likely and
the more informative outcome.

---

## Cycle 8 (2026-07-25) — Theorem X: Lambda-positivity is NOT semidefinite representable

Settles the cycle-7 open problem, negatively.

**Character/cylinder-lift argument.** Let Gamma be the additive group generated by all frequencies
in a putative h = sum_k |q_k|^2. Since mu -> (Re mu, Im mu) embeds Gamma in R^2, for every (s,phi)

    chi_{s,phi}(mu) = exp(Re(mu) s + i Im(mu) phi)

is a character of Gamma with chi(conj mu) = conj chi(mu). Substituting it for e^{mu u} sends each
q_k to a function of (s,phi) and |q_k|^2 to its squared modulus. So an SOS certificate forces the
CYLINDER LIFT (replace e^{au} by e^{as}, e^{i g u} by e^{i g phi}) to be nonnegative on ALL of R^2,
not just on the diagonal phi = s where it reproduces h.

**Witness.**

    h(u) = (1/2)cosh(2u) - 5 cosh u - cos u + 15/2 = (1 - cos u) + (cosh u - 2)(cosh u - 3)

- h >= 0 on R: if cosh u <= 2 or >= 3 both summands are >= 0; if 2 < cosh u < 3 then
  cosh 1 < 2 and 3 < cosh 2 force 1 < |u| < 2, so sin(|u|/2) >= sin(1/2) > 1/2 - (1/2)^3/4 > 7/15
  and 1 - cos u = 2 sin^2(u/2) > 2(7/15)^2 > 1/4, while (cosh u - 2)(cosh u - 3) >= -1/4 by
  (y - 5/2)^2 >= 0.
- lift at phase 0 = (cosh s - 2)(cosh s - 3); at s = log((5+sqrt 21)/2) one has cosh s = 5/2 and
  the lift = -1/4 < 0. Off the diagonal: phase 0 on the diagonal means s in 2 pi Z, where cosh s is
  1 or >= cosh(2 pi), never in (2,3).

**Consequence.** The Lambda-positivity cone is STRICTLY larger than the SOS cone. No fixed-degree
semidefinite relaxation and no square-based moment/Galerkin hierarchy is complete for
Lambda-positivity. Certificates must exploit the hyperbolic-oscillatory correlation along the
diagonal — exactly what the cycle-7 certificates do. Trace-normalized witness: multiply by
1 - cos(g' u) for a fresh frequency g' and evaluate that phase at pi.

Machine-verified: `RHTower/ConePositivstellensatzFailure.lean` (standard axioms only).

### Cycle 9 target

The positive half of the Positivstellensatz: find the correct certificate class for the mixed cone.
The certificates of cycle 7 all have the shape  A(u) - B(u)cos(g u)  with  0 <= B <= A  and A, B
sums of Hermitian squares in the hyperbolic variable alone. Conjecture: this "diagonal-dominant"
class generates the whole cone. Deciding it would give a complete effective criterion for
Lambda-positivity, hence for membership in the classification of cycles 5-6.

---

## Cycle 9 (2026-07-25) — Theorem X' (no multiplier certificate) and lane exhaustion

### Phase-8 conjecture REFUTED by my own Theorem X

Cycle 8 proposed that the "diagonal-dominant" class A(u) - B(u)cos(g u) with 0 <= B <= A generates
the cone. FALSE: every diagonal-dominant element IS a sum of Hermitian squares, since
A - B cos = (A - B) + B(1 - cos) with A - B hyperbolic (hence SOS by Polya-Szego) and
B(1-cos) = 2B sin^2 SOS. Theorem X exhibits a cone element that is not SOS, so the class does not
generate. Recorded so it is not re-attempted.

### Theorem X' — not even an Artin-style denominator certificate exists

The cylinder lift of the witness satisfies  lift(s,phi) = lift(s,0) + (1 - cos phi), so at
s = obstructionPoint it equals -1/4 + (1 - cos phi), which is negative on the OPEN set
cos phi > 3/4. Hence for any sigma >= 0 with h*sigma a sum of squared moduli, sigma vanishes
identically on that open set; by real analyticity sigma = 0. So the Lambda-positivity cone admits
no sum-of-squares certificate even after multiplication by a positive multiplier.

Machine-verified: `RHTower/ConePositivstellensatzFailure.lean` (standard axioms only).

### DEAD END recorded — the two-variable lift of the zero divisor

W(a,b) := sum_rho e^{rho a + conj(rho) b}. Since Re rho = (rho + conj rho)/2 and
Im rho = (rho - conj rho)/(2i), the cylinder lift of the explicit-formula object is exactly W, and

    RH  <=>  W(a,b) = e^{(a+b)/2} S(a-b),   S(v) = sum_gamma e^{i gamma v}.

A clean functional reformulation of RH. BUT W(a,b) for b != 0 involves conj(rho), which is not
holomorphic in rho, so contour integration against xi'/xi cannot produce it: W is INACCESSIBLE off
the diagonal. This is the precise form of the classical barrier. The only accessible functionals
involving conj(rho) are the Hermitian ones  sum_rho hhat(w_rho) conj(hhat(-conj w_rho)) — i.e. the
Weil form, which pairs rho with its critical-line reflection 1 - conj(rho). Hence Weil positivity is
not one route among several: it is the unique accessible route to Re rho. Do not look for another
linear device.

### Also re-verified as blind (do not re-attempt)

Assuming an off-line zero rho_0 = 1/2 + b + i gamma_0 of zeta, EVERY refund/insert configuration
targeting ord_1 F = 1 fails by Theorem I regardless of b: the top level is either an oscillatory
pair with mean zero, or carries a negative coefficient. So the deformation calculus cannot see b.
This is Theorem N from a third direction.

---

## Cycle 10 (2026-07-25) — Theorem B: the Weil index IS the pole-order budget

### Phase 4 verdict on the first conjecture: REDISCOVERED

I conjectured "ind_-(Weil form) = (1/2) #{off-critical zeros}". Literature check: this is
BOMBIERI, "Remarks on Weil's quadratic functional in the theory of prime numbers, I" — for a large
enough truncation the number of negative eigenvalues is exactly half the number of RH-violating
zeros. Do NOT re-derive. What survives interrogation is the comparison below.

### The orbit decomposition (algebraic core, formalized)

Order the divisor by orbits of w = rho - 1/2 under w -> +-w, +-conj w:

| orbit | block | signature | index | size |
|-|-|-|-|-|
| critical {i g, -i g} | 2(X^2 + Y^2) | PSD | 0 | 2 |
| real {a, -a} | 2XY | (1,1) | 1 | 2 |
| generic {w,-w,cw,-cw} | 4(Z1 W1 - Z2 W2) | (2,2) | 2 | 4 |

Diagonalizations 2XY = [(X+Y)^2 - (X-Y)^2]/2 and 4(Z1W1 - Z2W2) = [(Z1+W1)^2-(Z1-W1)^2] -
[(Z2+W2)^2-(Z2-W2)^2]; PSD half-subspaces Y=X resp. W1=Z1, W2=-Z2; negative directions Y=-X resp.
W1=-Z1, W2=Z2. Each off-critical orbit costs exactly half its size.

### Theorem B (NEW) — budget-index identity

For F in the classification with inserted divisor Z, |Z| = 2m, off-critical part of size 2j:

    ind_-(W_F) - ind_-(W_zeta)  =  j  <=  m  =  ord_1 F - 1,

equality iff every inserted zero is off-critical. So the LINEAR cost of a deformation (the pole
order it must buy at s=1, Theorem P) DOMINATES its QUADRATIC cost (negative eigenvalues added to
the Weil form, Bombieri's count), and the two agree exactly on purely off-critical insertions.
The classification's grading and Bombieri's index are the same invariant read two ways; Theorem M
says it vanishes only at zeta. First bridge found between the linear and quadratic lanes.

Machine-verified: `RHTower/WeilIndexBudgetBridge.lean` (standard axioms only).

### DEAD END recorded — using the family to bound W_zeta

W_zeta(h) = W_F(h) - sum_{rho in Z} ghat(w_rho). To conclude RH from an unconditional W_F >= 0 one
needs sum_Z ghat <= 0 for all h. But critical insertions give sum_Z = 2|Hhat(i g)|^2 >= 0 (wrong
sign), real pairs give 2 Hhat(a) Hhat(-a) (indefinite), generic quadruples give
4 Re[Hhat(w)Hhat(-w)] (indefinite). No sign control in any case. Route closed.

### Cycle 11 target

Theorem B says the two lanes measure one invariant. The unexploited direction: the invariant is
defined for the WHOLE classification family, and Theorem M pins its zero locus to {zeta}. Ask
whether the invariant admits an intrinsic definition — one not referred to zeta — which would turn
"vanishes only at zeta" into a statement about zeta alone.
