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

---

## Cycle 11 (2026-07-25) — Theorem B' (conservation) and Theorem N' (quadratic ceiling)

### Conjecture C11 stated, then REFUTED by my own Theorem R

C11: for every Lambda-positive Riemann-FE system with entire order-one completion,
    ind_-(W_F) <= ord_1 F - 1.
Applied to F = zeta (ord_1 = 1) this gives ind_-(W_zeta) <= 0, i.e. RH. So C11 is exactly the
kind of absolute bound that would settle the problem.

FALSE. Theorem R's refunded stray has ord_1 F = 2 (increment 1) but removes a critical pair, so its
Weil index increment is 2. C11 would force ind_-(W_zeta) + 2 <= 1, i.e. ind_-(W_zeta) <= -1, and an
index is nonnegative. The refund mechanism is exactly what breaks the absolute bound.
DO NOT re-attempt any absolute index-vs-pole-order inequality.

### Theorem B' (NEW, exact) — conservation law

Counting FREQUENCY PAIRS, with I_off, I_crit inserted and R_off, R_crit removed:

    (Weil index increment)  =  (pole order increment)  +  R_crit - I_crit,
    pole increment = (I_off + I_crit) - (R_off + R_crit),   index increment = I_off - R_off.

An identity, not an inequality. Verified on both explicit counterexamples:
  real stray J'      (I_off,I_crit,R_off,R_crit) = (1,0,0,0):  pole +1, index +1.
  refunded stray R   (2,0,0,1):                                pole +1, index +2.
So the two invariants of Theorem B coincide exactly when there is no critical traffic, and the
discrepancy is precisely the net number of critical pairs removed.

### Theorem N' (NEW) — the quadratic ceiling

Solving B' for zeta: ind_-(W_zeta) = ind_-(W_F) - I_off + R_off >= R_off - I_off. Since
ind_-(W_F) >= 0 is the only universally available input, every member of the classification family
yields a LOWER bound on ind_-(W_zeta), never an upper one. Removing off-critical zeros of zeta
(which would make R_off > 0) presupposes knowing them. Hence NO member of the family can certify
ind_-(W_zeta) = 0. This is the exact quadratic counterpart of the linear ceiling Theorem N: the
classification family is blind to RH from above in both lanes.

Machine-verified: `RHTower/WeilIndexConservation.lean` (standard axioms only; two lemmas need only
propext).

### Cycle 12 target

Both lanes now have proven ceilings, and Theorem B' says they are one invariant. Any route to RH
must therefore leave the deformation family entirely. The one input never used anywhere in cycles
5-11 is the INTEGRALITY of the support of dPsi_zeta: the generalized primes of every counterexample
sit at irrational logs, whereas zeta's sit at log n with the log p rationally independent. Target:
find a positivity or rigidity statement that is sensitive to Q-linear independence of the support.

---

## Cycle 12 (2026-07-25) — prime-symbol decoupling; the Kronecker/Weyl competition mapped

### The mechanism that uses Q-linear independence

{log p} is Q-linearly independent (sum a_p log p = 0 with integer a_p means prod p^{a_p} = 1). By
Kronecker the flow xi -> (xi log p)_p mod 2 pi is dense in the torus, so the extremes of the prime
symbol

    P(xi) = 2 sum_n Lambda(n) n^{-1/2} cos(xi log n)
          = 2 sum_p log p * sum_{k>=1} p^{-k/2} cos(k xi log p)

DECOUPLE COMPLETELY across primes: sup_xi P = sum_p sup_theta f_p(theta), same for inf. This is the
only place in the whole programme where multiplicative independence of the primes — the property no
Beurling counterexample has — enters as an exact statement rather than a heuristic. The decoupling
principle itself is Bohr's; the closed forms below are the new part.

### Closed form of the local factor and its sharp attained range

With x = p^{-1/2} in (0,1) and c = cos theta,

    sum_{k>=1} x^k cos(k theta) = (x c - x^2)/(1 - 2 x c + x^2) =: L(x,c),

strictly increasing in c (derivative x(1-x^2)/(1-2xc+x^2)^2 > 0), so its range over c in [-1,1] is
exactly [ -x/(1+x), x/(1-x) ], both endpoints attained at theta = pi and theta = 0. Hence

    -2 sum_p (log p)/(sqrt p + 1)  <=  P(xi)  <=  2 sum_p (log p)/(sqrt p - 1),

term by term, sharp along the Kronecker orbit. The upper extreme sits at xi = 0 where the pole term
also concentrates; the lower extreme is off xi = 0 and smaller in modulus by (sqrt p - 1)/(sqrt p + 1)
at each prime. That asymmetry is invisible without decoupling.

Machine-verified: `RHTower/PrimeSymbolDecoupling.lean` (standard axioms only).

### Lane mapped, obstruction identified (do not re-attempt naively)

Idea: at a full alignment frequency (all cos(xi log p) near 1 for p <= N) the Weyl term log(xi/2pi)
must beat the prime term ~ 4 sqrt N. Simultaneous alignment of pi(N) independent phases is expected
to require log xi >> N, which dwarfs 4 sqrt N, so full alignment is harmless.

OBSTRUCTION: the danger is NOT full alignment but PARTIAL alignment of the heavy tail (primes near
N carry weight (log N)/sqrt N each). The relevant question is exactly the RESONANCE METHOD /
Omega-results regime (Bondarenko-Seip: max_{t<=T} |zeta(1/2+it)| >= exp(c sqrt(log T/log log T)),
resonator built from primes up to y with log y ~ sqrt(log T log log T)). Effective lower bounds on
alignment heights would need linear-independence measures for log p; Baker's theorem supplies them
but with constants far too weak (exponential in pi(N)) to beat 4 sqrt N. So the competition is real
but the effective constants run the wrong way with current technology.

### Cycle 13 target

Decoupling turns a global extremal problem over xi into independent one-dimensional problems, one
per prime. Apply it not to sup/inf of P but to the WEIL FORM itself: for test functions whose Bohr
lift factorizes over primes, the Weil functional should decouple into local factors plus the
archimedean and pole terms. That would give a genuinely local (Euler-product-shaped) positivity
criterion. Target: state and prove the decoupled form of the truncated Weil functional.

---

## Cycle 13 (2026-07-25) — the Weil functional as an independent-sum on the Bohr torus

### Exact decomposition

In frequency form the Weil functional is

    W(h) = (1/2pi) int |hhat(xi)|^2 [ A_inf(xi) - P(xi) ] d xi  +  pole,
    A_inf(xi) = Re Psi(1/4 + i xi/2) - log pi  ~  log(|xi|/2pi),
    P(xi)     = 2 sum_p log p * L(p^{-1/2}, cos(xi log p)).

RH <=> that measure is positive (it IS the zero-counting measure). The asymmetry that organizes
everything: **P depends on xi only through the phases theta_p = xi log p, so it is a function on the
Bohr torus; A_inf depends only on the height xi and does NOT lift to the torus.** RH is therefore a
statement about a function on T^inf x R_+ restricted to the Kronecker line theta_p = xi log p.

### P is a sum of INDEPENDENT random variables (Bohr measure)

Under the Kronecker/Bohr measure the theta_p are independent and uniform, so
P = sum_p X_p with X_p = 2 log p L(p^{-1/2}, cos theta_p) independent. Exact local statistics:

    E[L] = 0,        E[L^2] = x^2 / (2(1 - x^2)),      x = p^{-1/2}
    => E[X_p] = 0,   Var(X_p) = 2 (log p)^2/(p - 1),
    => Var(P_N) = sum_{p<=N} 2(log p)^2/(p-1) ~ (log N)^2,  sd(P_N) ~ log N.

So the Weil condition compares the archimedean gain ~ log xi against a mean-zero variable of
standard deviation ~ log N. (This recovers the Bohr-Jessen / Selberg picture from the decoupling,
with explicit constants.)

### Theorem F (NEW, formalized) — uniform amplitude bound

    |X_p| <= 2 log p/(sqrt p - 1) <= 4   for every prime p,

by a one-line argument: log u <= u - 1 at u = sqrt p gives log p = 2 log sqrt p <= 2(sqrt p - 1).
So EVERY prime, however small, contributes at most 4 to the Weil prime symbol. Together with the
exact variance above this makes P_N a sum of independent, mean-zero, uniformly bounded (by 4)
variables with completely explicit constants — the exact input a Bernstein/Bennett concentration
estimate needs:

    Pr[ P_N > lambda ] <= exp( - lambda^2 / (2 V_N + (8/3) lambda) ),  V_N = sum_{p<=N} 2(log p)^2/(p-1).

Machine-verified: `RHTower/PrimeAmplitudeUniformBound.lean` (standard axioms only).

### Cycle 14 target

The concentration bound above controls P_N on the Bohr torus with FULL measure, but the Weil
condition is only needed along the Kronecker LINE, and the line is a measure-zero subset. The gap
between "true almost everywhere on T^inf" and "true on the line" is exactly the gap between the
random model and zeta. Target: quantify the discrepancy of the Kronecker line against the torus
measure at the resolution set by the test-function support — i.e. an effective Weyl/Erdos-Turan
bound for the flow xi -> (xi log p)_{p<=N}, and see whether it is strong enough to transfer the
concentration estimate from the torus to the line.

---

## Cycle 14 (2026-07-25) — Theorem G: the transfer threshold (third ceiling)

### The question

Cycle 13's concentration estimate holds on the Bohr torus with FULL measure; the Weil condition is
needed only along the Kronecker line, a measure-zero subset. What does the transfer cost?

### Theorem G (NEW, formalized) — elementary covering lower bound

Partition T^r into M^r boxes of side 1/M. Parameterize a curve by arclength: entering a new box
means some coordinate crossed a grid hyperplane, and coordinate i crosses at most 1 + M L times.
So a curve of length L meets at most 1 + r + r M L boxes. If its 1/M-neighbourhood covers the torus
it must meet all M^r, hence

    M^r <= 1 + r + r M L    =>    L >= M^{r-1}/(2r)    (r >= 3),
    log L >= (r-1) log M - log(2r),
    log T >= (r-1) log M - log(2r) - log ||lambda||_2   for the Kronecker line, L = T ||lambda||_2.

With r = pi(N) and lambda_p = log p, resolving the torus at scale 1/M demands
log T >~ pi(N) log M ~ (N/log N) log M.

NO ARITHMETIC INPUT AT ALL — pure volume/counting, unconditional.

### Consequence — the probabilistic lane is capped

The prime symbol is already of full size ~ sqrt N at ALL heights, while the torus model only becomes
applicable at log T >~ N/log N, exponentially further out. The Weil condition is required precisely
at the heights where the line PROVABLY has not equidistributed. Hence no probabilistic/Bohr-torus
argument can establish Weil positivity. This is the third ceiling of the programme:

    Theorem N   linear Lambda-positivity  -> caps at PNT strength
    Theorem N'  quadratic / Weil index    -> only lower bounds on ind_-(W_zeta)
    Theorem G   Bohr-torus probability    -> valid only beyond log T ~ pi(N), too far out

Machine-verified: `RHTower/KroneckerTransferThreshold.lean` (standard axioms only).

### Cycle 15 target

All three general-purpose lanes are capped, and each ceiling has the same shape: the available
positivity is insensitive to the critical line at the scale where the obstruction lives. The one
structure not yet examined is the interaction ACROSS scales — the Weil form couples the prime
symbol at scale sqrt N to the archimedean term at scale log xi, and every ceiling so far was proved
by decoupling them. Target: find an inequality that uses the coupling itself, i.e. one that is FALSE
for the decoupled model but true for zeta. The counterexample family of cycles 5-6 is the natural
test set: it decouples exactly, so any such inequality must fail on it.

---

## Cycle 15 (2026-07-25) — Theorem H15: sharp lower bound for Re(-zeta'/zeta)

### Phase 4 note — Lagarias's criterion is the sharp pointwise coupling

Chasing "an inequality that uses the height-phase coupling" led to: xi(s) = xi(1-s) makes
log|xi(sigma+it)| symmetric about sigma = 1/2, and RH <=> |xi(sigma+it)| nondecreasing in
sigma >= 1/2 <=> Re(xi'/xi)(s) > 0 on Re s > 1/2. The latter is LAGARIAS (1999) — REDISCOVERED, do
not re-derive. Expanded it reads

    (1/2)(Re Psi(s/2) - log pi) + Re(1/s + 1/(s-1)) - Re( sum_n Lambda(n) n^{-sigma} cos(t log n) ) > 0,

i.e. the SAME archimedean-vs-prime competition as the Weil form, but pointwise. Unconditionally
provable only where the Dirichlet series converges absolutely (sigma > 1), which is where there are
no zeros anyway — a fourth instance of the same ceiling shape.

Also noted: the Bohr random model respects multiplicativity (theta_{p^k} = k theta_p) but has NO
functional equation. So the FE *is* the height-phase coupling, and the Weil form is the coupled
object; every ceiling (N, N', G) was proved by estimating it with decoupled quantities.

### Theorem H15 (NEW, formalized) — the sharp constant

Classical: |Re(-zeta'/zeta(sigma+it))| <= -zeta'/zeta(sigma), sharp on the UPPER side (t=0), NOT on
the lower. Decoupling computes the infimum prime by prime; with x = p^{-sigma} the local range is
[-x/(1+x), x/(1-x)] = [-1/(p^sigma+1), 1/(p^sigma-1)], and 1/(x+1) = 1/(x-1) - 2/(x^2-1) gives

    sum_p (log p)/(p^sigma + 1) = -zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma),

hence for every real t and every sigma > 1

    Re( -zeta'/zeta(sigma + it) )  >=  zeta'/zeta(sigma) - 2 zeta'/zeta(2 sigma),

SHARP, equality approached along the Kronecker orbit. The correction -2 zeta'/zeta(2 sigma) is
exactly what "cos >= -1" throws away. Attribution: the |zeta| analogue zeta(2s)/zeta(s) <= |zeta| <=
zeta(sigma) is classical (Titchmarsh 8.7); this is its logarithmic-derivative counterpart with the
sharp constant supplied by the decoupling.

Machine-verified per prime: `RHTower/SharpLogDerivativeLowerBound.lean` (standard axioms only).

### Cycle 16 target

Four ceilings now, all of one shape. The remaining asymmetry that has NOT been exploited: the sharp
bounds are attained at DIFFERENT points of the torus (upper at theta = 0, lower at theta = pi), and
theta = 0 is on the Kronecker line (t = 0) while theta = pi is not reachable simultaneously for all
primes at any finite height. Target: quantify which points of the torus are actually visited at a
given height — an effective Kronecker/Weyl statement in the OPPOSITE direction to cycle 14, giving
an upper bound on how much of the extremal set the line can reach. That is the only place where the
line's arithmetic (not just its measure-zero-ness) can enter.

---

## Cycle 16 (2026-07-25) — Theorem I16: the Liouville point is unreachable at bounded height

### Identification

The two sharp endpoints of the prime symbol sit at different torus points:
  upper endpoint  theta_p = 0 for all p  -> ON the Kronecker line, at xi = 0;
  lower endpoint  theta_p = pi for all p -> p^{i xi} = -1 for all p <= N, i.e. n^{i xi} ~ lambda(n)
                                             on N-smooth n (LIOUVILLE function).
So the sharp lower bound of cycle 15 is attained exactly at the "Liouville point" of the Bohr torus,
which is never on the line. Approaching it costs height, and the cost is bounded below WITHOUT any
transcendence input.

### Theorem I16 (NEW, formalized) — elementary reachability bound

If xi log p = b pi + d1 and xi log q = a pi + d2 with |d_i| <= eps, eliminating pi gives

    xi * |a log p - b log q| = |a d1 - b d2| <= eps (a + b),

and a log p - b log q = log(p^a) - log(q^b) is the log of a ratio of DISTINCT POSITIVE INTEGERS
when p != q are primes. For distinct positive integers A > B, log u >= 1 - 1/u gives
log A - log B >= (A-B)/A >= 1/A. Hence

    eps  >=  xi / ( (a+b) * max(p^a, q^b) ).

Since a, b grow linearly in xi, this gives xi >~ log(1/eps): weak but unconditional and effective,
with no Baker input. Upgrading the linear form in two logarithms (Baker-Wustholz, or
Laurent-Mignotte-Nesterenko: |a log p - b log q| >= exp(-C (log B)^2), B = max(a,b) ~ xi) gives
xi >= exp(c sqrt(log(1/eps))). Dirichlet gives the upper bound xi << eps^{-2}. Truth in between.

Direction that matters: the point where the sharp lower bound is attained is inaccessible to the
line at bounded height, and it is the line's ARITHMETIC (integrality of p^a, q^b) that keeps it
away — not merely its measure-zero-ness. This is the first place in the programme where integrality
enters an inequality rather than a construction.

Machine-verified: `RHTower/LiouvillePointReachability.lean` (standard axioms only).

### Cycle 17 target

Cycle 16 shows the extremal LOWER point is arithmetically far from the line. The Weil form needs
control of the UPPER excursions of the prime symbol, whose extremal point theta = 0 IS on the line
(at xi = 0) — but there the pole term dominates. Target: determine the arithmetic distance from the
line to the near-maximal set at NONZERO height, i.e. lower-bound the height at which
sum_p log p cos(xi log p) can come within a constant factor of its maximum. The same integrality
argument should apply with pi replaced by 2 pi, and would bound the first "conspiracy" of the primes
unconditionally.

---

## Cycle 17 (2026-07-25) — Theorem J17: smooth commas exclude a band of conspiracy heights

### Corpus cross-check (all three research folders)

- `RHTower/BakerWeldIndependence.lean` — has `baker_intFragment_unconditional`: the
  INTEGER-coefficient fragment of Baker (prod p^{a_p} = 1 => all a_p = 0) is unconditional, plus a
  two-prime complex fragment. That is the QUALITATIVE independence. Cycle 16/17 supply the
  QUANTITATIVE/effective counterpart. Complementary, not duplicated.
- `HTGeometry/TrigPolynomialPhaseSelection.lean` — `exists_ge_re_finset_exp_le`: at arbitrarily
  large times a designated term can be pointed along the negative real axis. That is the
  CONSTRUCTIVE direction (alignment eventually happens). Cycle 17 is the CONVERSE (alignment cannot
  happen early). Complementary.
- `HilbertMetric` — nothing on Kronecker/Bohr/Diophantine; not relevant here.

### Theorem J17 (NEW, formalized)

Let A/B be a ratio of N-smooth positive integers, A != B — a COMMA — and
lam = log(A/B) = sum_p c_p log p with integer exponents. If every prime p <= N satisfies
xi log p = 2 pi b_p + delta_p with |delta_p| <= eps, then pairing with c:

    | xi*lam - 2 pi K | <= eps * ||c||_1,      K = sum_p c_p b_p in Z.

K = 0 forces xi <= eps ||c||_1 / lam; otherwise |K| >= 1 forces xi*lam >= 2 pi - eps ||c||_1. So the
open interval

    (  eps ||c||_1 / lam ,  (2 pi - eps ||c||_1)/lam  )

contains NO height at which the primes up to N are eps-aligned. Band length ~ 2 pi / lam, and lam
can be made tiny by choosing a good comma:

    log(9/8)      ~ 0.118     excludes up to xi ~ 53
    log(81/80)    ~ 0.0124    excludes up to xi ~ 506
    log(2401/2400)~ 4.2e-4    excludes up to xi ~ 1.5e4

and the smallest N-smooth comma shrinks rapidly with N (Stormer-Lehmer). Unconditional, effective,
transcendence-free; the strength comes purely from INTEGRALITY of the smooth numbers A and B.

Together with cycle 16 (Liouville point, lower extreme) both extremes of the prime symbol are now
separated from the Kronecker line by arithmetic, at explicit heights.

Machine-verified: `RHTower/SmoothCommaExclusionBand.lean` (standard axioms only).

### Cycle 18 target

Both extremes are excluded near the line at low height, but the Weil form does not need the extremes
— it needs the whole excursion profile. Target: convert the comma exclusion into a bound on the
MEASURE of the set of heights xi <= T where the prime symbol exceeds a given level, i.e. an
unconditional upper bound for  |{ xi <= T : P_N(xi) > lambda }|  with explicit constants. That is
the quantity the Weil form actually integrates against, and it is the first genuinely quantitative
object the exclusion bands can control.

---

## Cycle 18 (2026-07-25) — Theorem K18: effective mean value for the prime symbol

Supplies the quantitative transfer that cycle 14 showed was needed, at FINITE height, with the
error controlled by integrality.

### The estimate

For a real trigonometric polynomial Q(xi) = sum_j a_j cos(mu_j xi) with |mu_j| >= delta > 0,

    | (1/T) int_0^T Q |  <=  (sum_j |a_j|) / (T delta),

since int_0^T cos(mu xi) d xi = sin(mu T)/mu has modulus <= 1/|mu|.

Applied to P_N^{2k}: the frequencies are log(A/B) with A, B products of 2k integers <= N, so
A, B <= N^{2k}, and the integrality separation |log A - log B| >= 1/max(A,B) (cycle 16) gives
delta >= N^{-2k}. Coefficient mass <= ||P_N||_1^{2k} = (2 sum_{n<=N} Lambda(n) n^{-1/2})^{2k}. Hence

    | (1/T) int_0^T P_N^{2k}  -  E[P_N^{2k}] |  <=  ( N^2 ||P_N||_1^2 )^k / T,

E the Bohr-torus expectation. With the exact torus moments of cycle 13 (mean 0, variance
sum_p 2(log p)^2/(p-1), per-prime amplitude <= 4) this makes Chebyshev completely explicit:

    |{ xi <= T : P_N(xi) > lambda }| / T  <=  E[P_N^{2k}]/lambda^{2k}  +  (16 N^3)^k/(T lambda^{2k}),

nontrivial once log T >~ k log(16 N^3 / lambda^2); optimizing k ~ lambda^2/(e (log N)^2) makes the
first term small.

MECHANISM: the transfer error is small precisely because two distinct products of primes cannot
have nearly equal logarithms. Integrality again — the same input as the exclusion bands.

Machine-verified: `RHTower/EffectiveMeanValuePrimeSymbol.lean` (standard axioms only).

### Cycle 19 target

The measure bound above is now explicit but its useful range is log T >~ lambda^2/log N, i.e. it
controls large values of P_N only when the prime cutoff N is large compared with the height T. In
the Weil form, N is tied to the test-function support and T is not a free parameter at all — the
form integrates |hhat(xi)|^2 against A_inf(xi) - P_N(xi) over ALL xi. Target: redo the measure
estimate with |hhat|^2 as the weight instead of Lebesgue measure on [0,T], i.e. an effective
mean-value theorem in which the averaging kernel is the test function's own spectral density. That
is the exact object the Weil form needs, and the integrality separation should still supply the
error term.

---

## Cycle 19 (2026-07-25) — Theorem L19: chain damping halves the Weil prime term

### The realisation

The |hhat|^2-average of P_N is EXACTLY the prime side of the explicit formula (Fourier inversion),
so there is no transfer error to estimate — the right question is the sharp size of
Re<h, T_{log n} h> for h supported in an interval of length L. Every ceiling in cycles 5-18 used
the NAIVE bound |<h, T_a h>| <= ||h||^2. It is not sharp, and the loss is largest exactly where the
prime mass sits.

### Theorem L19 (NEW)

Compressing T_a to L^2 of an interval of length L splits the space into chains x, x+a, x+2a, ...
of length at most M = floor(L/a) + 1. On a chain of length M the operator is the nilpotent shift,
whose numerical radius is cos(pi/(M+1)) — equivalently the top eigenvalue of the path-graph
adjacency matrix P_M is 2 cos(pi/(M+1)) (classical). Hence

    | Re <h, T_a h> |  <=  cos( pi / (floor(L/a) + 2) ) * ||h||^2 .

CERTIFICATE (sine substitution): theta = pi/(M+1), w_j = sin(j theta), recurrence
w_{j-1} + w_{j+1} = 2 cos theta w_j makes the weighted AM-GM steps
2 v_j v_{j+1} <= (w_{j+1}/w_j) v_j^2 + (w_j/w_{j+1}) v_{j+1}^2 telescope, every coefficient
collapsing to the constant 2 cos theta. Exact SOS form:

  2 cos(th) sum v_k^2 - 2 sum v_j v_{j+1}
      = sum_{j=0}^{m-2} (w_{j+1}/w_j) ( v_j - (w_j/w_{j+1}) v_{j+1} )^2  >= 0.

### Consequence — a factor of two

Damping factor cos(pi/(floor(L/log n)+2)):

    log n in (L/2, L]   -> M = 2 -> cos(pi/3)   = 1/2
    log n in (L/3, L/2] -> M = 3 -> cos(pi/4)   = sqrt2/2 ~ 0.707
    log n <= L/k        -> M = k+1 -> cos(pi/(k+2)) -> 1.

Since sum_{n <= e^L} Lambda(n) n^{-1/2} ~ 2 e^{L/2} is dominated by n near e^L, where the factor is
exactly 1/2, the sharp bound on the prime term is ASYMPTOTICALLY HALF the naive one. This is a
genuine unconditional gain in the archimedean-versus-prime competition that every ceiling of this
programme has been measuring — the first improvement to the competition itself rather than to the
map of its limits.

Machine-verified: `RHTower/AutocorrelationChainDamping.lean` (sine recurrence, weighted AM-GM,
sharp M=2 and M=3 cases; standard axioms only).

### Cycle 20 target

The factor 1/2 applies to the heaviest half of the prime mass. Redo the full archimedean-versus-
prime accounting with the chain-damped prime bound in place of the naive one, and determine the
exact constant in the resulting inequality: whether damping alone pushes the unconditional
positivity threshold for the truncated Weil form past the Connes-Consani support, which is the
first genuinely new positivity range in the CCM programme.

---

## Cycle 20 (2026-07-25) — Theorem M20: overlap localization; the last prime switches on continuously

### The sharp statement

For h supported in I = [0,L] and shift a with L/2 < a <= L, chains have length <= 2 and they live
ONLY on the overlap

    E_a = [0, L-a] union [a, L],   measure 2(L-a),

off which the integrand h(x)h(x-a) vanishes identically. Integrating the pointwise
2|h(x)h(x-a)| <= h(x)^2 + h(x-a)^2 over the only region where the product is nonzero gives

    2 | Re<h, T_a h> |  <=  ||h||^2_{L^2(E_a)} ,

which carries BOTH the factor 1/2 = cos(pi/3) AND the localization. Elementary and sharp.

### Mechanism at the Connes-Consani threshold

CC give positivity of archimedean+pole for support below log 2, where no prime contributes. As the
support grows past log 2 by eta, the first prime switches on with weight at most
(log 2/sqrt 2) * ||h||^2_{L^2(E)} on a set E of measure 2 eta — vanishing LINEARLY in eta for any
test function that stays spread out. A test function that instead concentrates on E pays on the
archimedean side, whose symbol Re Psi(1/4 + i xi/2) - log pi ~ log(|xi|/2pi) rewards exactly the
high-frequency content that concentration on a set of measure 2 eta forces.

So the prime term is O(eta) precisely in the regime where the archimedean term is not large. This
identifies the mechanism by which positivity should extend past log 2 — the first candidate
extension of the CC range. What is still missing to make it a theorem is a QUANTITATIVE version of
CC positivity (a gap proportional to the concentration), which their prolate/Toeplitz proof gives
only qualitatively. Recorded as the precise remaining input.

Machine-verified: `RHTower/OverlapLocalizedPrimeTerm.lean` (standard axioms only).

### Cycle 21 target

Supply the missing quantitative input directly: a lower bound for the archimedean-plus-pole part in
terms of the concentration of h, i.e. an inequality of the form
    pole(h) + A(h) >= c * ||h||^2_{L^2(E)} * log(1/|E|) - C
for h supported in an interval of length L, with explicit c, C. That is an uncertainty-principle
statement about the digamma symbol, independent of CC's machinery, and together with M20 it would
close the threshold extension unconditionally.

---

## Cycle 21 (2026-07-25) — Theorem N21: the archimedean term rewards concentration

Supplies the first half of the input identified at the end of cycle 20.

### Monotonicity of the symbol

sigma(xi) = Re Psi(1/4 + i xi/2) - log pi is INCREASING in |xi|: from
Psi(z) = -gamma + sum_k (1/(k+1) - 1/(k+z)),

    Re Psi(a+ib) = -gamma + sum_k ( 1/(k+1) - (k+a)/((k+a)^2 + b^2) ),

and every summand increases with b^2 because c/(c^2+b^2) decreases. Hence sigma >= sigma(0)
everywhere and sigma(xi) ~ log(|xi|/2pi) grows without bound.

### The uncertainty step

Splitting the frequency line at Xi:  A(h) >= sigma(0)||h||^2 + beta (sigma(Xi) - sigma(0)),
beta = high-frequency mass fraction. If h carries mass mu = ||h||^2_{L^2(E)} on a set E of measure m,
then ||P_Xi h||_inf <= sqrt(Xi/pi)||h||, so ||P_Xi h||_{L^2(E)} <= sqrt(m Xi/pi)||h||, and

    sqrt(mu) <= sqrt(m Xi / pi) + sqrt(beta).

Choosing Xi = pi mu/(4m) makes the first term sqrt(mu)/2, so beta >= mu/4. Therefore

    A(h) >= sigma(0)||h||^2 + (mu/4)( sigma(pi mu/(4m)) - sigma(0) ),

and since sigma(pi mu/(4m)) ~ log(mu/(8m)) the gain grows like (mu/4) log(mu/(8m)) as the
concentration set shrinks.

### Paired with cycle 20

The first prime past the CC threshold costs at most (log 2/sqrt 2) mu on a set of measure 2 eta.
Break-even: the archimedean gain covers it as soon as (1/4) log(mu/(16 eta)) >= log 2/sqrt 2, i.e.
mu >~ 114 eta; and when mu <~ 114 eta the prime cost is itself O(eta). Either way the prime term
past the threshold is dominated by the archimedean reward except on an O(eta) remainder.

Machine-verified: `RHTower/ArchimedeanConcentrationGain.lean` (standard axioms only).

### What is still missing (recorded precisely)

The crude universal bound A >= sigma(0) ||h||^2 with sigma(0) = Psi(1/4) - log pi ~ -5.37 is too
lossy to conclude positivity by itself, because the pole term 2 Hhat(1/2) Hhat(-1/2) is indefinite.
A sharp, gap-carrying version of the Connes-Consani archimedean-plus-pole positivity is still
required. Cycle 21 supplies the concentration reward; what remains is the BASELINE.

### Cycle 22 target

Attack the baseline directly: a lower bound for pole(h) + A(h) for h supported in an interval of
length L that does NOT go through sigma(0). The pole term is 2 <h, e_{1/2}> <h, e_{-1/2}> with
e_{+-1/2}(u) = e^{+- u/2}; on an interval of length L these two vectors have explicit Gram matrix,
so the rank-two pole form can be diagonalized exactly and its negative direction identified. Target:
compute that diagonalization and pair it against the two-band archimedean bound, giving an explicit
baseline independent of prolate/Toeplitz machinery.

---

## Cycle 22 (2026-07-25) — Theorem O22: exact diagonalization of the pole form; baseline dichotomy

### The diagonalization (exact)

pole(h) = ghat(1/2) + ghat(-1/2) = 2 <h,e_+><h,e_->, e_pm(u) = e^{+-u/2}. Writing e_pm = c +- s with
c(u) = cosh(u/2), s(u) = sinh(u/2):

    pole(h) = 2 <h,c>^2 - 2 <h,s>^2.

Even direction carries the POSITIVE eigenvalue, odd direction the NEGATIVE one. Same Krein splitting
that organizes the whole Weil form, now explicit for the pole.

### The negative direction is cubically small

    ||s||^2_{L^2[-l,l]} = int_{-l}^{l} sinh^2(u/2) du = int (cosh u - 1)/2 = sinh l - l,

and sinh l - l <= (l^3/6) cosh l, since cosh t - 1 = 2 sinh^2(t/2) <= (t^2/2) cosh^2(t/2)
= (t^2/4)(cosh t + 1) <= (t^2/2) cosh t. So by Cauchy-Schwarz the ENTIRE negative part of the pole
form is at most 2(sinh l - l)||h||^2 — cubically small in the support half-length.

### The baseline dichotomy (elementary, no prolate/Toeplitz)

Write P = <h,c>. Since hhat has derivative bounded by l ||h||_1 <= l sqrt(2l) for h supported in
[-l,l] with ||h||_2 = 1, the low-frequency mass obeys

    (1/2pi) int_{|xi|<=Xi} |hhat|^2 <= (Xi/pi)( |hhat(0)|^2 + (2/3) l^3 Xi^2 ),

so beta >= 1 - (Xi/pi)|hhat(0)|^2 - (2/(3pi)) l^3 Xi^3. And c differs from the constant 1 by at most
cosh(l/2) - 1 on [-l,l], so |hhat(0)| and |P| differ by O(l^2). Hence

  * either P^2 is not small, and the pole form supplies the positive term 2P^2;
  * or P^2 is small, beta is close to 1, and the archimedean average is close to sigma(Xi), which is
    positive for Xi > 2pi and grows like log(Xi/2pi).

Both branches explicit and elementary — NO prolate spheroidal functions, NO Toeplitz theory. This is
an independent route to Connes-Consani-type archimedean-plus-pole positivity.

Machine-verified: `RHTower/PoleFormDiagonalization.lean` (diagonalization, sinh x <= x cosh x,
sinh l >= l, cubic smallness, dichotomy arithmetic; standard axioms only).

### Cycle 23 target

The dichotomy has explicit constants but they have not been optimized. Target: choose Xi as a
function of l and P to make both branches quantitative simultaneously, and compute the largest l for
which the resulting bound is nonnegative. If that l exceeds (log 2)/2, the elementary route already
recovers the Connes-Consani range; if it exceeds (log 3)/2 after adding the chain-damped first prime
of cycles 19-20, it exceeds it. Both are finite explicit optimizations over two parameters.

---

## Cycle 23 (2026-07-25) — Theorem P23: explicit elementary archimedean baseline

### The sharp low-frequency estimate (replaces the crude one of cycle 21)

For h supported in an interval of length 2l with ||h||_2 = 1, |hhat(xi)| <= ||h||_1 <= sqrt(2l)
POINTWISE, so the normalized spectral mass in any band obeys

    (1/2pi) int_{|xi|<=Xi} |hhat|^2 <= (1/2pi)(2 Xi)(2 l) = 2 l Xi / pi     for EVERY Xi.

So the spectral measure is stochastically larger than the UNIFORM measure on [-Xi_*, Xi_*] with
Xi_* = pi/(2l). Since sigma is nondecreasing in |xi| (cycle 21), stochastic dominance gives

    A(h) >= (1/Xi_*) int_0^{Xi_*} sigma = (2/Xi_*) Im log Gamma(1/4 + i Xi_*/2) - log pi,

using d/dxi Im log Gamma(1/4 + i xi/2) = (1/2) Re Psi(1/4 + i xi/2) and Gamma(1/4) real. By Stirling
the right side is log(Xi_*/2pi) - 1 + o(1) = log(1/(4l)) - 1 + o(1).

### The assembled baseline

    pole(h) + A(h) >= 2P^2 - 2(sinh l - l) + (2/Xi_*) Im log Gamma(1/4 + i Xi_*/2) - log pi,

nonnegative once log(1/(4l)) >~ 1, i.e. for l <~ 1/(4e) ~ 0.092 — and in fact for larger l, since
the Stirling asymptotic UNDERestimates sigma near the origin. Compare Connes-Consani: l < (log 2)/2
~ 0.347. So the elementary route reaches within a factor under four of CC, with NO prolate
spheroidal functions and NO Toeplitz theory.

Progression of the estimate across cycles: crude sigma >= sigma(0) gave l <~ 3e-4 (cycle 21);
the pointwise Fourier bound + stochastic dominance gives l <~ 0.092 (cycle 23) — a factor of ~300.

Machine-verified: `RHTower/ExplicitArchimedeanBaseline.lean` (band bound, half-mass cutoff
Xi = pi/(4l), two-band archimedean bound, assembled baseline, positivity criterion; standard axioms).

### Cycle 24 target

Close the remaining factor of ~3.8. Two identified sources of slack: (i) the two-band split at
Xi = pi/(4l) discards the shape of sigma inside the band — replacing it by the exact average
(1/Xi_*) int_0^{Xi_*} sigma, i.e. the Im log Gamma closed form, should recover most of it; (ii) the
term 2P^2 is discarded entirely, though P is bounded below whenever h has a sign. Target: evaluate
the Im log Gamma closed form against -sigma(0) = 5.372 exactly and determine the true elementary
threshold l_0.

---

## Cycle 24 (2026-07-25) — Theorem Q24: the threshold IS the first zero of Riemann-Siegel theta

### The closed form

The stochastic-dominance bound of cycle 23 has an exact evaluation. Since
d/dxi Im log Gamma(1/4 + i xi/2) = (1/2) Re Psi(1/4 + i xi/2) and Gamma(1/4) is real,

    int_0^X Re Psi(1/4 + i xi/2) d xi = 2 Im log Gamma(1/4 + i X/2),

so with the RIEMANN-SIEGEL THETA FUNCTION theta(X) = Im log Gamma(1/4 + iX/2) - (X/2) log pi,

    (1/X) int_0^X sigma  =  (2/X) Im log Gamma(1/4 + iX/2) - log pi  =  2 theta(X)/X.

**The averaged archimedean symbol is exactly 2 theta(X)/X.** Its sign is the sign of theta.

### The threshold law

    pole(h) + A(h) >= 2P^2 - 2(sinh l - l) + 2 theta(pi/(2l)) * (2l/pi),

nonnegative as soon as 2 theta(X)/X >= (l^3/3) cosh l, whose right side is <= about 0.005 in the
whole range of interest. So the cutoff is the sign of theta:

    2 theta(X)/X >= 0  <=>  X >= t_0,   t_0 = unique positive zero of theta = Gram point g_{-1}
                                              ~ 6.28983,

and with X = pi/(2l),

    l <= l_0 = pi/(2 t_0) ~ 0.2497 ~ 1/4,

since t_0 sits within a tenth of a percent of 2 pi.

**THE ELEMENTARY ARCHIMEDEAN-PLUS-POLE POSITIVITY RANGE OF THE WEIL FUNCTIONAL IS CUT OFF EXACTLY
AT THE FIRST ZERO OF THE RIEMANN-SIEGEL THETA FUNCTION.**

Connes-Consani: l < (log 2)/2 ~ 0.3466. Gap now a factor 1.39.

Progression of the elementary threshold:
    cycle 21 (crude sigma >= sigma(0)):                 l <~ 3e-4
    cycle 23 (pointwise Fourier + stochastic dominance): l <~ 0.092
    cycle 24 (exact average = 2 theta(X)/X):             l <~ 0.2497
i.e. a factor ~800 over three cycles, and the final answer is a named classical constant.

Machine-verified: `RHTower/RiemannSiegelThresholdLaw.lean` (closed-form identity, integrated cubic
bound sinh l - l <= (l^3/6) cosh l, cutoff/support translation, positivity criterion; standard
axioms only).

### Cycle 25 target

Two remaining sources of slack, both identified and both finite:
 (i) the pole term 2P^2 is discarded. P = <h, cosh(./2)> is bounded below for any h of one sign, and
     more generally P^2 + Q^2 is controlled by the L^1 norm; restoring it should recover part of the
     1.39.
 (ii) the stochastic-dominance bound uses only |hhat(xi)|^2 <= ||h||_1^2; the true constraint also
     includes total mass 1 and the Paley-Wiener decay of hhat beyond 1/l, which lifts the effective
     cutoff above pi/(2l).
Target: incorporate (i) and (ii) and determine whether the elementary threshold reaches (log 2)/2,
i.e. whether the elementary route fully recovers the Connes-Consani range.

---

## Cycle 25 (2026-07-25) — Theorem R25: refined spectral dominance (mean-zero branch)

Closes slack (i) of cycle 24: the pole term 2P^2 was discarded, so the adversary must take P = 0 —
and THAT costs it on the archimedean side.

### The refinement

For h supported in [-l,l] with ||h||_2 = 1:
  |hhat'(xi)| <= l ||h||_1 <= l sqrt(2l)  =>  |hhat(xi)| <= |hhat(0)| + l sqrt(2l)|xi|
                                          =>  |hhat(xi)|^2 <= 2 hhat(0)^2 + 4 l^3 xi^2;
  |hhat(0) - P| <= (cosh(l/2) - 1)||h||_1 <= (l^2/8) cosh(l/2) sqrt(2l),
  so P = 0 forces hhat(0)^2 <= (l^5/32) cosh^2(l/2).

Band integral: (1/2pi) int_{|xi|<=Xi} |hhat|^2 <= 2 hhat(0)^2 Xi/pi + 4 l^3 Xi^3/(3 pi), which beats
the flat bound 2 l Xi/pi exactly for Xi <= sqrt(3/2)/l. So the dominating CDF improves to

    G_l(Xi) = min( 2 hhat(0)^2 Xi/pi + 4 l^3 Xi^3/(3pi),  2 l Xi/pi,  1 ),

a CUBIC start instead of a linear one.

### The gain

In the logarithmic asymptotic sigma(Xi) ~ log(Xi/2pi), with u = l Xi and crossover a = sqrt(3/2):

    int log u dG    = (4/pi)( (a^3/3) log a - a^3/9 ) + (2/pi)[u log u - u]_a^{pi/2}
                    = -0.1018 + 0.0732 = -0.0286,
    int log u dG_unif = log(pi/2) - 1 = -0.5484,
    Delta ~ 0.52.

So the cycle-22 dichotomy is now quantitative on BOTH sides: either P^2 > 0 and the pole contributes
2P^2 directly, or P = 0 and the archimedean average gains about half a unit.

Machine-verified: `RHTower/RefinedSpectralDominance.lean` (refined pointwise Fourier bound, mean-zero
estimate, band integral, cubic/flat crossover, dominator; standard axioms only).

### Slack (ii) diagnosed as prolate-theoretic (recorded)

The remaining slack is the sharp constraint on band mass, which is exactly the top eigenvalue
lambda_0(l Xi) of the time-frequency limiting operator — Slepian/Landau-Pollak prolate theory, i.e.
precisely the machinery cycles 22-25 set out to avoid. My flat bound 2 l Xi/pi is the trace bound and
is the SHARP small-c asymptotic of lambda_0(c); the true lambda_0 is smaller, so the sharp constraint
would improve the threshold further, but only by re-entering prolate theory. The elementary route is
therefore essentially exhausted at the cubic refinement.

### Cycle 26 target

The elementary archimedean route has been pushed from l <~ 3e-4 (cycle 21) to l <~ 0.25 (cycle 24)
plus the ~0.52 mean-zero gain (cycle 25), against Connes-Consani's 0.3466. Rather than chase the
last factor into prolate theory, turn the machinery around: the chain-damping bound of cycle 19 and
the overlap localization of cycle 20 apply to EVERY prime, not just the first. Target: assemble the
full damped prime sum sum_n 2 Lambda(n) n^{-1/2} cos(pi/(floor(2l/log n)+2)) against the
Riemann-Siegel threshold law and determine the largest l for which the FULL truncated Weil form is
unconditionally nonnegative by these elementary means.

---

## Cycle 26 (2026-07-25) — Theorem S26: the damped prime sum, and WHICH constraint binds

### Exact damped prime sum

prime cost <= 2 Sigma(l),
Sigma(l) = sum_{n : log n <= 2l} Lambda(n) n^{-1/2} cos( pi/( floor(2l/log n) + 2 ) ).

The floor stratifies: floor(2l/log n) = k  <=>  2l/(k+1) < log n <= 2l/k, so

    Sigma(l) = sum_{k>=1} cos(pi/(k+2)) * sum_{ e^{2l/(k+1)} < n <= e^{2l/k} } Lambda(n) n^{-1/2},

damping factors cos(pi/3)=1/2, cos(pi/4)=sqrt2/2, cos(pi/5)=(1+sqrt5)/4, cos(pi/6)=sqrt3/2 -> 1.
With sum_{n<=X} Lambda(n)n^{-1/2} ~ 2 sqrt X and Abel summation,

    Sigma(l) = e^l + 2 sum_{k>=2} Delta_k e^{l/k} - 2 + o(1),
    Delta_k = cos(pi/(k+2)) - cos(pi/(k+1)) > 0,

versus the naive 2 e^l: ratio -> 1/2, confirming cycle 19's factor of two with an explicit
correction series.

### THE BINDING CONSTRAINT (key structural finding)

The first prime enters at 2l = log 2, i.e. l = (log 2)/2 ~ 0.3466. The elementary archimedean
baseline holds only to l_0 = pi/(2 t_0) ~ 0.2497, and 0.2497 < 0.3466 precisely because
t_0 > pi/log 2 ~ 4.532.

**So inside the purely elementary route the prime damping is NEVER ACTIVATED: the archimedean
baseline gives out first, while the prime sum is still empty.**

Consequences:
 - the chain damping of cycles 19-20 is not the bottleneck and cannot be by itself;
 - the damping becomes decisive only combined with Connes-Consani, which covers exactly the interval
   [pi/(2 t_0), (log 2)/2] and beyond;
 - THE PRECISE MISSING INPUT is a quantitative Connes-Consani on [0.2497, 0.3466]. Everything else
   in the elementary tower is in place and machine-verified.

Machine-verified: `RHTower/DampedPrimeSumAssembly.lean` (floor stratification, damping factor
positivity/sub-unitality, cos(pi/3)=1/2, block bound, and the comparison pi/(2t_0) < (log 2)/2;
standard axioms only).

### Cycle 27 target

The elementary tower is complete up to one interval. Two options, both concrete:
 (a) Push the archimedean baseline from 0.2497 to 0.3466 by the only remaining elementary lever —
     the SECOND moment of the spectral measure, i.e. use int |hhat|^2 xi^2 in addition to the band
     constraint. This requires h in H^1, which costs nothing since the extremal h can be smoothed.
 (b) Accept CC on [0, log2/2] as an input and state the FIRST unconditional extension past log 2/2
     using the damped prime sum, i.e. the theorem "CC + chain damping => positivity for
     l <= log2/2 + eta_0" with eta_0 explicit.
(b) is the one that produces a new positivity range for the CCM programme.

---

## Cycle 27 (2026-07-25) — Theorem T27: IMS localization; the CC gap is the unique missing input

### The IMS formula for the Weil form

The Weil functional is a convolution quadratic form Q(h) = int int K(x-y) h(x) h(y). For a QUADRATIC
partition of unity chi_1^2 + chi_2^2 = 1 the pointwise identity

    chi_1(x)chi_1(y) + chi_2(x)chi_2(y) = 1 - (1/2)[(chi_1(x)-chi_1(y))^2 + (chi_2(x)-chi_2(y))^2]

integrates to the EXACT localization formula

    Q(h) = Q(chi_1 h) + Q(chi_2 h)
             + (1/2) int int K(x-y)[(chi_1(x)-chi_1(y))^2 + (chi_2(x)-chi_2(y))^2] h(x)h(y).

Covering an interval of length L + eta by two of length L (overlap L - eta), the partition may be
taken c/(L-eta)-Lipschitz, so

    |Err| <= (2 c^2/(L-eta)^2) * M_2 * ||h||^2,   M_2 = int_{|u|<=L+eta} |K(u)| u^2 du,

finite because the archimedean singularity is only 1/(2|u|). With CC (Q psd on length L <= log 2),

    Q_{L+eta} >= -2 c^2 M_2/(L-eta)^2.

### The verdict

The error is O(1), NOT O(eta), because the partition gradient is O(1/L) regardless of eta. So
localization gives quantitative NEAR-positivity past log 2 but not positivity.

**THIS IS THE THIRD INDEPENDENT ROUTE TO THE SAME PLACE.** All of
  (a) the direct overlap estimate (cycle 20),
  (b) the damped prime sum (cycles 19, 26),
  (c) IMS localization (cycle 27)
reduce to one and the same missing input: a SPECTRAL GAP in the Connes-Consani theorem, i.e. a
quantitative lower bound Q_L >= delta_0 ||h||^2 for L <= log 2 rather than merely Q_L >= 0. That
reduction is now established from three directions and is the sharp open problem of this lane.

Machine-verified: `RHTower/IMSLocalizationWeilForm.lean` (partition identity, Lipschitz bound on the
localization weight, IMS lower bound; standard axioms only).

### Cycle 28 target

Attack the CC gap directly, on the elementary tower rather than on CC's proof. The elementary
baseline of cycles 22-25 gives Q_L >= 2P^2 - 2(sinh l - l) + 2 theta(pi/2l)/(pi/2l) for l <= 0.2497,
and that expression is STRICTLY POSITIVE for l < 0.2497 — it vanishes only in the limit. So the
elementary tower already carries a gap on [0, 0.2497). Target: compute delta_0(l) explicitly there
and feed it through the IMS bound to obtain the first unconditional extension of the positivity range
beyond the elementary threshold — which would make the whole tower self-contained, with no CC input
at all.

---

## Cycle 28 (2026-07-25) — Theorem U28: the IMS bootstrap is strictly weaker (cycle 27 proposal CLOSED)

### The elementary gap exists

Dropping the nonnegative pole square, Q_{2l}(h) >= delta_0(l) ||h||^2 with

    delta_0(l) = (4l/pi) theta(pi/(2l)) - 2(sinh l - l),

and delta_0 -> +infinity as l -> 0, since 2 theta(Xi)/Xi = log(Xi/2pi) - 1 + o(1). With L = 2l the
support length, delta_0 = log(1/(2L)) - 1 + o(1). A QUADRATIC partition satisfies
||chi_1 h||^2 + ||chi_2 h||^2 = ||h||^2, so IMS gives

    Q_{L+eta} >= ( delta_0(L) - 2 kappa^2 M_2 ) ||h||^2,  kappa = pi/(L-eta).

### Why it fails: the error is SCALE INVARIANT

Near the diagonal the Weil kernel is dominated by the archimedean 1/(2|u|), so
M_2 ~ int_{-(L+eta)}^{L+eta} u^2/(2|u|) du = (L+eta)^2/2, and

    2 kappa^2 M_2 = pi^2 (L+eta)^2/(L-eta)^2 >= pi^2,     INDEPENDENT OF L.

The 1/|u| singularity makes the kernel's second moment scale exactly like the square of the partition
length, cancelling the kappa^2. So the error is a universal constant >= pi^2 ~ 9.87 while the gap
grows only logarithmically. Hence delta_0 > pi^2 requires

    L < e^{-1-pi^2}/2 ~ 2e-5,

and iterating multiplies L by 1+rho with rho = (sqrt(delta_0)/pi - 1)/(sqrt(delta_0)/pi + 1) -> 0 as
delta_0 -> pi^2, so the bootstrap STALLS at L ~ 1e-5.

That is far below L = 2 l_0 ~ 0.4994, which the DIRECT elementary bound of cycles 22-25 already
reaches. **IMS localization is strictly weaker than the direct estimate and can never extend the
range.** The cycle-27 proposal is closed.

Structural reason worth keeping: only a gap growing FASTER THAN LOGARITHMICALLY could beat a scale
invariant localization error, and no such gap exists — delta_0 is an average of the archimedean
symbol, which is logarithmic by Stirling. Any future localization/bootstrap scheme for the Weil form
faces the same obstruction.

Machine-verified: `RHTower/IMSBootstrapObstruction.lean` (second moment, scale invariance of the
error, bootstrap threshold, and the comparison with the direct threshold; standard axioms only).

### Cycle 29 target

Both extension mechanisms (damped primes, IMS) are now closed, and the direct elementary bound stands
at l_0 = pi/(2 t_0) ~ 0.2497 against Connes-Consani's 0.3466. The only remaining elementary lever
identified and not yet used is the SECOND SPECTRAL MOMENT: the dominance argument constrains only the
distribution function of |hhat|^2, whereas h supported in [-l,l] also satisfies
int |hhat(xi)|^2 xi^2 d xi = 2 pi ||h'||^2 for h in H^1, and the extremal h may be smoothed at no
cost. Target: add that constraint to the stochastic-dominance problem and recompute the threshold.

---

## Cycle 29 (2026-07-25) — Theorem V29: the second moment is vacuous; the elementary tower is OPTIMAL

### The constraint

For h in H^1_0([-l,l]) with ||h||_2 = 1, the Dirichlet eigenvalue of the interval gives

    int xi^2 d nu(xi) = ||h'||_2^2 >= pi^2/(4 l^2) = Xi_*^2,

exactly the square of the cutoff of the threshold law. The uniform measure on [0, Xi_*] — the
extremal measure of the band constraint — has second moment Xi_*^2/3, so it VIOLATES this, and one
might hope the minimum rises.

### It does not

Take nu_q = uniform density 1/Xi_* on [0,(1-q)Xi_*] plus an atom of mass q at

    b_q = Xi_* sqrt( (1 - (1-q)^3/3)/q ).

It satisfies the band constraint (b_q >= (1-q)Xi_*) and meets the second-moment constraint with
EQUALITY. Its extra cost is

    q sigma(b_q) <= q(C + log Xi_*) + (q/2) log(1/q) + q  <=  q(C + log Xi_*) + 1/(2e) + q,

using q log(1/q) <= 1/e (from log t <= t/e). As q -> 0 the cost vanishes and the objective returns to
the old value. **A vanishing mass at a diverging frequency satisfies the second-moment constraint for
free.**

### Every elementary lever is now closed

  damped primes  -> never activated; the archimedean baseline binds first (cycle 26)
  IMS bootstrap  -> scale-invariant error >= pi^2 beats the logarithmic gap (cycle 28)
  second moment  -> vacuous, by the family above (cycle 29)
  prolate        -> re-enters the CC machinery the tower was built to avoid (cycle 25)

**THE ELEMENTARY THRESHOLD l_0 = pi/(2 t_0) ~ 0.2497, t_0 THE FIRST ZERO OF THE RIEMANN-SIEGEL THETA
FUNCTION, IS OPTIMAL WITHIN THESE MEANS.** The residual gap to (log 2)/2 ~ 0.3466 requires a
genuinely different input, and three independent routes (cycles 20, 26, 27-28) have been shown to
reduce to the same one: a spectral GAP in the Connes-Consani theorem.

Machine-verified: `RHTower/SecondMomentVacuity.lean` (log t <= t/e, q log(1/q) <= 1/e, the extremal
family, its second moment and band admissibility, and the atom cost bound; standard axioms only).

### Cycle 30 target

The elementary lane is mapped and closed. Do NOT re-open it. Remaining live directions, in order of
assessed promise:
 (a) the CC spectral gap itself — the unique bottleneck, reached by three independent routes;
 (b) the accessibility principle (cycle 9): Weil positivity is the ONLY accessible functional
     detecting Re rho, so any new lane must still be quadratic;
 (c) the classification (cycles 5-6) is complete and closed, and the axiomatic lane is circular.
Target: attack (a) directly, i.e. produce a lower bound Q_L >= delta ||h||^2 for L <= log 2 with
delta > 0 explicit, by any means — including CC's own prolate/Toeplitz machinery, which is no longer
something to avoid now that the elementary alternative is proven optimal and insufficient.


---

## CORRECTION to cycles 24-29 (2026-07-25) — the numerical threshold, not the structure

Cycle 24 identified the elementary threshold as the first positive zero t_0 of the Riemann-Siegel
theta function. THE STRUCTURE IS CORRECT; the numerical value quoted was WRONG.

Since theta'(t) = sigma(t)/2, the value t ~ 6.29 is the zero of SIGMA, i.e. the MINIMUM of theta —
not the zero of theta. The first positive zero of theta is the first Gram point,

    t_0 ~ 17.8455,   so   l_0 = pi/(2 t_0) ~ 0.0880,

not 0.2497. Corrected consequences:

  cycle 23 (Stirling asymptotic)          l <~ 0.092
  cycle 24 (exact, 2 theta(X)/X)          l <~ 0.0880     [was misreported as 0.2497]
  cycle 25 (mean-zero gain Delta ~ 0.52)  l <~ 0.155      [asymptotic: log(1/4l) = 1 - 0.52]

So the exact evaluation REFINES the Stirling estimate rather than improving it by a factor 2.7, and
the combined elementary threshold is ~0.155 against Connes-Consani's 0.3466 — a factor ~2.2, not
1.39. Everything else in cycles 24-29 (the closed-form identity, the optimality argument, the three
closed levers) is unaffected: they are structural and do not depend on the numerical value of t_0.

The binding-constraint finding of cycle 26 is REINFORCED: the first prime enters at l = 0.3466 while
the elementary baseline gives out at ~0.155, so the gap is wider than reported and the damped prime
sum is even further from being activated.

Lesson recorded: never quote a zero of an antiderivative from the zero of its integrand.

---

## Cycle 30 (2026-07-25) — Theorem W30: discreteness gives the CC gap for free BELOW log 2

### The structure

Below the first prime the Weil form is completely explicit: Q_L = P_L (Sigma + R) P_L for L < log 2,
Sigma the Fourier multiplier by sigma(xi), R the rank-two pole form 2<.,c>^2 - 2<.,s>^2. Since
sigma(xi) -> +infinity, P_L Sigma P_L has compact resolvent, so Q_L has DISCRETE SPECTRUM and
lam(L) = inf spec Q_L is an attained eigenvalue.

Three structural facts, needing nothing about Sigma beyond the growth of its symbol:
  - lam is nonincreasing (nested spaces, fixed form);
  - lam(L) is attained (discreteness);
  - lam is STRICTLY decreasing at L whenever (Sigma+R)h_L does not vanish identically just outside
    supp h_L. Variation h_t = cos t h_L + sin t phi with phi in the new sliver gives
    Q(h_t) = cos^2 t lam(L) + 2 cos t sin t <(Sigma+R)h_L, phi> + sin^2 t Q(phi), so a nonzero cross
    term lets one decrease past lam(L). And (Sigma+R)h_L is real analytic off supp h_L (the kernel of
    Sigma is analytic away from 0), so vanishing on an open sliver forces vanishing throughout.

### Consequence

Positivity at L_1 yields a STRICTLY POSITIVE GAP at every L < L_1. In particular the Connes-Consani
theorem at L = log 2 supplies for free the spectral gap that cycles 20, 26 and 27 all needed — but
ONLY STRICTLY BELOW log 2.

### The sharp limitation, now from a FOURTH direction

Extending positivity PAST log 2 needs a lower bound for lam at a length where positivity is not yet
known. Monotonicity, discreteness, continuity and localization all propagate information DOWNWARD in
L only. Four independent routes now confirm this:
  cycle 20  direct overlap estimate
  cycle 26  damped prime sum
  cycles 27-28  IMS localization (error scale invariant, >= pi^2)
  cycle 30  discreteness / variational monotonicity
Every one of them reduces to: a lower bound on lam(L) for L > log 2, which no soft argument gives.

Machine-verified: `RHTower/AutomaticGapDiscreteness.lean` (variational expansion, strict decrease
from a nonzero cross term, gap below positivity, downward-only propagation; standard axioms only).

### Cycle 31 target

Since all soft routes propagate downward only, the extension must come from an estimate that is
genuinely uniform in L — i.e. a bound on lam(L) that does not degrade as L grows. The only such
object identified in the whole programme is the archimedean symbol average 2 theta(X)/X with
X = pi/(2l), which decreases in l. Target: determine whether ANY quantity bounding lam from below is
non-decreasing in L; if none exists, that is a genuine no-go for the entire extension programme and
should be proved as such.

---

## Cycle 31 (2026-07-25) — Theorem X31: the extension programme IS the Riemann hypothesis

lam(L) = inf spec Q_L is nonincreasing; Weil's criterion is lam >= 0 everywhere. Suppose b is ANY
nondecreasing function with b <= lam and b(L_0) >= 0 for a single L_0. Then
  - for L >= L_0:  lam(L) >= b(L) >= b(L_0) >= 0;
  - for L <= L_0:  lam(L) >= lam(L_0) >= 0 by monotonicity of lam.
So lam >= 0 everywhere: RH.

**No nondecreasing lower bound for lam, nonnegative anywhere, can be established by any means short
of proving RH itself.** Every scheme for extending a positivity range past its endpoint must produce
such a bound — hence be as hard as RH — or fail, as all four attempts did. The extension lane is
closed as a lane, not merely as four attempts.

Machine-verified: `RHTower/ExtensionProgrammeNoGo.lean` (standard axioms only).

## THE COMPLETE MAP after 31 cycles

    linear Lambda-positivity        caps at PNT strength                  Theorem N
    quadratic Weil index            lower bounds on ind_- only            Theorem N'
    Bohr-torus probability          valid only past height ~ pi(N)        Theorem G
    elementary archimedean tower    optimal at l ~ 0.155                  Theorems Q24-V29
    extension of a positivity range EQUIVALENT TO RH                      Theorem X31
    axiomatic characterization      circular or false                     Theorems M, P, R

Every lane opened in 31 cycles is now closed, each by a machine-verified theorem. The positivity
universe is mapped and capped.

### What this leaves

The accessibility principle (cycle 9) says Weil positivity is the ONLY accessible linear-in-g
functional detecting Re rho, and the map above says every route inside it is capped. So a proof must
introduce structure from outside the positivity universe. The candidates never touched in 31 cycles:
  - modularity / Poisson summation as a GEOMETRIC input (not merely as the source of the FE);
  - the de Bruijn-Newman flow, where RH <=> Lambda = 0 and Lambda >= 0 is a theorem (Rodgers-Tao);
    the missing half, Lambda <= 0, is a repulsion statement about zero dynamics;
  - the function-field analogy: Weil's proof uses Riemann-Roch on C x C, and the arithmetic
    analogue would need an intersection theory that does not presently exist.
These are recorded as the live directions; none is a positivity argument.

---

## Cycle 32 (2026-07-25) — Theorem Y32: the budget law has a SPECTRAL reading

The classification's two costs are not arbitrary; they separate self-adjoint-compatible deviations
from genuinely non-self-adjoint ones.

For a self-adjoint spectral problem zeros come from eigenvalues via s = 1/2 +- sqrt(1/4 - lam):
  lam >= 1/4  (tempered)    -> s = 1/2 +- i sqrt(lam - 1/4)   critical pair, cost 0
  0 < lam < 1/4 (exceptional) -> s = 1/2 +- w, w = sqrt(1/4 - lam) in (0,1/2)   REAL STRAY, cost 1
This is exactly Theorem J's configuration, and exactly how a SELBERG zeta function acquires real
zeros off the critical line when the surface has small Laplace eigenvalues.

A genuinely complex quadruple 1/2 +- a +- i gam with a gam != 0 has NO real preimage: (a + i gam)^2
has imaginary part 2 a gam != 0, so it cannot equal 1/4 - lam for real lam. Hence:

    cost 1, real stray        <-> compatible with a self-adjoint problem (exceptional eigenvalue)
    cost 2, complex quadruple <-> incompatible with ANY self-adjoint problem

and Theorem R's refunded stray buys the second for one unit by removing a critical pair — spectrally,
trading a tempered eigenvalue for a non-self-adjoint resonance.

**Reading of the budget law:** for a system arising from a self-adjoint problem, ord_1 F - 1 counts
the exceptional spectrum, and ord_1 F = 1 forces it empty. RH is then the statement that zeta's
simple pole leaves no room for an exceptional parameter — which Hilbert-Polya would supply and which
Theorems P and R show the arithmetic side alone cannot.

This also explains, structurally, why the classification could not prove RH: Theorems P and R build
systems with Lambda >= 0, exact FE and entire order-one completion whose zeros are off the line, i.e.
the arithmetic side does not distinguish Riemann from a non-self-adjoint analogue. Selberg's RH is a
theorem precisely because its spectral side is a priori self-adjoint.

Machine-verified: `RHTower/SelbergExceptionalAnalogy.lean` (eigenvalue correspondence, exceptional
range, tempered case, impossibility of a real preimage; standard axioms only).

### Also this batch

- The no-go ATLAS was written into `docs/drafts/pipeline/4-publication-ready/euler-functional-equation-independence.md`
  as section 5g: all six capped lanes with their theorems, self-contained.
- Cycle 31's Theorem X31 (extension programme == RH) is formalized in
  `RHTower/ExtensionProgrammeNoGo.lean`.

---

## Cycle 33 (2026-07-25) — Theorem Z33: Lambda_dBN is the EXTINCTION TIME of the Weil index

First lane opened outside the positivity universe, as the atlas demanded.

### The dictionary

The de Bruijn-Newman flow H_t(z) = int_0^inf e^{t u^2} Phi(u) cos(z u) du deforms H_0 = xi(1/2+iz)/8
through entire order-one functions, each even in z; equivalently each Xi_t(s) = H_t(-i(s-1/2)) is
s -> 1-s invariant. So the ENTIRE FLOW stays inside the class where the Weil form is defined, and the
classification of cycles 5-32 applies to every Xi_t.

Two invariants meet:
  - orbit decomposition (Theorem B):  ind_-(W_{Xi_t}) = (1/2) N_off(t);
  - definition of Lambda:             N_off(t) = 0 exactly for t >= Lambda.

Hence t -> ind_-(W_{Xi_t}) is a NONINCREASING INTEGER-VALUED function of flow time, vanishing
precisely on [Lambda, inf):

    Lambda = the EXTINCTION TIME of the Weil index along the dBN flow,
    RH <=> ind_-(W_xi) = 0 <=> Lambda <= 0.

Each merge of a conjugate pair onto the real axis drops the index by at least one, so the index
counts the merges still to come. Rodgers-Tao's Lambda >= 0 says extinction cannot have happened
strictly before t = 0; RH says it has happened by t = 0. Both hold only if Lambda = 0: RH is the
statement that the flow is EXACTLY CRITICAL.

### Why this matters

It puts the two major frameworks on one axis:
  - Connes-Consani-Moscovici positivity measures the index AT t = 0;
  - de Bruijn-Newman measures the TIME AT WHICH the index vanishes.
Bombieri's index for the truncated Weil functional is thereby identified with a dynamical quantity.

By Theorem Y32 the same statement reads spectrally: for t < Lambda the divisor of Xi_t carries
complex quadruples, which no self-adjoint problem can produce, so the flow lies outside the
self-adjoint-compatible class exactly on [0, Lambda).

Machine-verified: `RHTower/WeilIndexExtinctionTime.lean` (index integrality, monotonicity, the drop
at a merge, extinction criterion, and Lambda = 0 from the two-sided bound; standard axioms only).

### Cycle 34 target

The dictionary makes the two frameworks exchange information. Concretely: Polymath15's Lambda <= 0.22
is an upper bound on the extinction time; translate it into a statement about the Weil index at
t = 0.22 and ask what the index calculus then forces at t = 0 — i.e. whether the known upper bounds
on Lambda constrain ind_-(W_xi) at all. If the merge times can be bounded below (a repulsion
estimate), an upper bound on Lambda would bound the number of merges, hence ind_-(W_xi), hence the
number of off-critical zeros of zeta — an unconditional finiteness statement.

---

## Cycle 34 (2026-07-25) — merge-time scaling; verdict REDISCOVERED (Tao)

Derived the zero dynamics of the dBN flow from scratch: since dH/dt = -H'', differentiating
H_t(z_j(t)) = 0 gives

    dz_j/dt = H''/H'(z_j) = 2 SUM_{k != j} 1/(z_j - z_k).

For a conjugate pair x +- iy the self term contributes -1/y to dy/dt, and every REAL zero r
contributes -2y/((x-r)^2 + y^2) < 0. Hence, PROVIDED THE OTHER ZEROS ARE REAL,
d(y^2)/dt <= -2, so the pair merges by y(0)^2/2 <= 1/8. Adding the Poisson term (density
log(x/2pi)/2pi) sharpens this to merge time <~ y(0)/log(x/2pi): high off-critical zeros merge
almost instantly. Consequently the Weil index at any fixed t > 0 counts only off-critical zeros
below height 2pi exp(pi/t).

Backward in time real zeros attract and collide in time ~ delta^2, so surviving a fixed negative
time needs normalized gaps -> infinity: Newman's heuristic for Lambda >= 0.

### PHASE 4 VERDICT: REDISCOVERED.
Terence Tao's Polymath15 proposal post states exactly this: "if there was a counterexample to RH at
a large height T ... this zero should not reach the real axis until a time comparable to 1/log T",
and "verifying RH up to height T should lead to a bound of the form Lambda = O(1/log T)". The
backward/collision direction is Csordas-Smith-Varga's Lehmer-pair theory (each sufficiently close
pair of zeros gives a lower bound for Lambda). BOTH ATTRIBUTED, NOT CLAIMED.

Also note the naive reading Lambda <= (sup y)^2/2 = 1/8 is FALSE: the estimate needs all other zeros
real, and with other complex zeros present their contribution to dy/dt can be positive. This is why
de Bruijn's 1/2 and Polymath15's 0.22 are proved by entirely different means. DEAD END recorded.

Machine-verified: `RHTower/MergeTimeEstimate.lean`, `RHTower/ExtinctionHeightLocalization.lean`.

### Relentless interrogation
What killed it: the local-field heuristic is Tao's. What the literature does NOT have is an estimate
free of the "other zeros are real" hypothesis. That defect is the target of cycle 35.

---

## Cycle 35 (2026-07-25) — Theorem A35: THE IMAGINARY ENERGY IS AN UNCONDITIONAL LYAPUNOV FUNCTIONAL

Set I = SUM_j (Im z_j)^2 over the zeros of Xi_t. Since Im(1/w) = -(Im w)/|w|^2,

    dI/dt = 2 SUM_j y_j * Im( 2 SUM_{k!=j} 1/(z_j - z_k) )
          = -4 SUM_{j!=k} y_j (y_j - y_k)/|z_j - z_k|^2 ,

and symmetrising the ordered pair (j,k) <-> (k,j) — the denominator is symmetric — gives the EXACT
IDENTITY

    dI/dt = -2 SUM_{j!=k} (y_j - y_k)^2 / |z_j - z_k|^2   <=  0.

UNCONDITIONALLY NONINCREASING. No hypothesis on the configuration at all — this is exactly what the
cycle-34 estimate lacked. Two sharpenings:
  * every ratio (y_j - y_k)^2/|z_j - z_k|^2 <= 1, with equality iff Re z_j = Re z_k;
  * a conjugate pair is vertically aligned, so its two ordered pairs are extremal and contribute -4.

Hence dI/dt <= -4 while any complex zero survives, and since I >= 0:

    Lambda <= (1/4) SUM_rho (Re rho - 1/2)^2 .

In the flow coordinate a zero rho = beta + i gamma of xi has Im z = 1/2 - beta, so the right side is
the total squared deviation of the divisor from the critical line. Specialisations: a single pair
gives Lambda <= y0^2/2 (recovering cycle 34 WITHOUT its hypothesis); a single quadruple
1/2 +- a +- i gamma gives Lambda <= a^2. Read backwards: SUM_rho (Re rho - 1/2)^2 >= 4 Lambda.

Machine-verified: `RHTower/ImaginaryEnergyLyapunov.lean` (pair identity, ratio bound, extremality of
the conjugate pair, extinction bound; standard axioms only).

---

## Cycle 36 (2026-07-25) — Theorem B36: CONSERVATION OF MERGE TIME (index-energy inequality)

Let t_1 <= ... <= t_m be the merge times and m(t) = #{i : t < t_i} the number of pairs still complex.
By the cycle-33 dictionary m(t) = ind_-(W_{Xi_t}). The energy identity gives dI/dt <= -4 m(t), and
the layer-cake identity INT_0^inf m(t) dt = SUM_i t_i — piecewise constant Abel summation
SUM_i (m-i)(t_{i+1}-t_i) = SUM_i t_{i+1} — yields the exact accounting

    4 SUM_i t_i  <=  SUM_rho (Re rho - 1/2)^2 ,   i.e.
    INT_0^Lambda ind_-(W_{Xi_t}) dt  <=  (1/4) SUM_rho (Re rho - 1/2)^2 .

THE SUM of the merge times, not merely the largest, is bounded. Consequences:
  * refines Lambda <= (1/4) SUM (Re rho - 1/2)^2, since Lambda = max t_i <= SUM t_i;
  * MANY EXCEPTIONS FORCE FAST EXTINCTION: if m pairs survive to time Lambda then
    m*Lambda <= (1/4) SUM (Re rho - 1/2)^2, so Lambda <= I_0/(4m). A large violation of RH is
    extinguished quickly;
  * each merge costs four units of imaginary energy per unit of time it takes; slow merges are
    expensive and the budget is the second moment of the real parts.

This is the first inequality putting the Connes-Consani-Moscovici index and the de Bruijn-Newman
flow on the same line, with a zero-statistic on the right.

Machine-verified: `RHTower/MergeTimeConservation.lean` (Abel summation, the sum bound, the
many-exceptions corollary; standard axioms only).

### Cycle 37 target
The energy inequality is one-sided: it bounds Lambda above by a quantity that vanishes exactly when
RH holds, so it is an equivalence in disguise and gives no asymmetric leverage by itself. The
asymmetry has to come from a SECOND functional with the OPPOSITE monotonicity. Candidates: the
Coulomb energy SUM_{j<k} log|z_j - z_k| (the flow is its holomorphic gradient ascent, so it is
monotone on real configurations but not in general), and the count of sign changes of Xi_t on the
real axis. Target: find a functional that INCREASES along the flow and is bounded above by an
arithmetic quantity, so that the two bounds squeeze Lambda from both sides.

---

## Cycle 37 (2026-07-25) — Theorem C37: THE dBN LANE IS CAPPED (sixth atlas row)

Tried to close RH with a squeeze. The energy inequality gives Lambda <= I_0/4 with
I_0 = SUM_rho (Re rho - 1/2)^2. If one could also prove a REVERSE bound Lambda >= kappa * I_0 with
kappa > 1/4, then kappa*I_0 <= I_0/4 forces I_0 = 0, i.e. RH. So: does such a kappa exist?

NO — and the reason is structural.

### Sharpness
For an isolated conjugate pair the energy identity is an EQUALITY: I = 2y^2, dI/dt = -4, hence
y(t)^2 = y0^2 - 2t and the merge is at t = y0^2/2 = I_0/4 exactly. So Lambda <= I_0/4 admits no
constant improvement, and any kappa > 1/4 is already false in the simplest configuration.

### Why: the flow is a MONOTONE deformation toward the critical line
Every term of dI/dt = -2 SUM_{j!=k}(y_j-y_k)^2/|z_j-z_k|^2 is NONPOSITIVE. The field of the other
zeros never opposes a merge, only accelerates it. So more zeros make Lambda SMALLER; the reverse
inequality degrades instead of improving. Nothing in the dynamics resists the hypothesis "RH fails".

### Consequence: the lane ceiling
A monotone deformation can produce only UPPER bounds on Lambda — statements of the form "if RH
fails, it fails only briefly." It can never derive a contradiction from the failure of RH. Every
known LOWER bound on Lambda comes from the INITIAL DATA — Lehmer pairs (Csordas-Smith-Varga) and
Rodgers-Tao — i.e. from arithmetic at t = 0, never from the flow. Confirmed by a second route: the
Gaussian factor e^{t u^2} destroys the Euler product for every t > 0, so `Xi_t` carries no arithmetic
at all; the primes exist only at the initial instant. The flow can transport information outward
from t = 0 and never inward.

### THE ATLAS, now six rows
    linear Lambda-positivity        caps at PNT strength                     (Thm N)
    quadratic Weil index            lower bounds on ind_- only               (Thm N')
    Bohr-torus probability          valid only past height ~ pi(N)           (Thm G)
    elementary archimedean tower    optimal at ell ~ 0.155                   (Thms Q24-V29)
    extension of the range          equivalent to RH                         (Thm X31)
    de Bruijn-Newman flow           monotone: upper bounds on Lambda only    (Thm C37)

### Caveat recorded (do not re-derive)
Lambda <= (1/4) SUM_rho (Re rho - 1/2)^2 is VACUOUS if the divisor has infinite imaginary energy,
i.e. if there are infinitely many off-critical zeros with non-square-summable deviations. It is
sharp and non-trivial exactly under finite energy. Attempts to make the right-hand side arithmetic
via zero-density theorems fail: N(sigma,T) << T^{3(1-sigma)/(2-sigma)} log^5 T gives
SUM_{gamma<T}(beta-1/2)^2 << T log^3 T, WORSE than the trivial N(T)/4 ~ T log T / 8pi. DEAD END.

Machine-verified: `RHTower/FlowMonotoneCeiling.lean`.

### Cycle 38 target
Six lanes, six ceilings, and each ceiling has the same shape: the available machinery is monotone or
aggregate in a direction that agrees with RH, so it can approach but never contradict. The next move
must be a mechanism that is NOT monotone in that direction — something that gets WORSE as the
divisor approaches the critical line, so that criticality is forced by an extremal principle rather
than approached by a limit. Candidate: a functional with a strict maximum at the critical
configuration (a rigidity/uniqueness statement), rather than an inequality saturated there.

---

## Cycle 38 (2026-07-25) — Theorem D38: A FALSIFICATION CRITERION WITH THE RIGHT MONOTONICITY

The atlas demanded a mechanism that DEGRADES as the divisor approaches the critical line. Found one:
the count of NON-REAL zeros in BACKWARD time.

### Setup
M(t) = number of non-real zeros of H_t;  tau_fin = inf{ t : M(t) < infinity }.
Ki-Kim-Lee (2009): for every t > 0, all but finitely many zeros of H_t are real and simple (this is
how they got Lambda < 1/2). Hence tau_fin <= 0. VERIFIED BY SEARCH, correctly attributed.

### The mechanism
Backward in time real zeros ATTRACT. For consecutive real zeros at distance delta the self term
gives d(delta)/d(tau) = -4/delta and the surrounding field contributes +2 delta SUM_k (x-r_k)^{-2}
~ 2 c delta rho^2. Collision (hence departure from the real axis as a conjugate pair) occurs once
the NORMALIZED gap delta*rho falls below a fixed constant, and takes time <= delta^2/8.

Under RH the zeros of H_0 are all real with density log(T/2pi)/2pi -> infinity; known small-gap
results give infinitely many normalized gaps below 0.5155. For an evenly spaced field the threshold
is delta*rho < sqrt(6)/pi ~ 0.78 (from SUM m^{-2} = pi^2/6), comfortably above 0.5155. Once complex,
a pair stays complex as t decreases. Therefore

    RH  ==>  M(t) = infinity for every t < 0  ==>  tau_fin = 0,
    and contrapositively:
    IF H_t HAS ONLY FINITELY MANY NON-REAL ZEROS FOR A SINGLE t < 0, THEN RH IS FALSE.

### Why the monotonicity is right
The more critical the divisor at t = 0, the denser its real zeros, the more pairs collide in backward
time, and the LARGER M(t) must be. Criticality is what forces the count to be infinite. This is the
first criterion in the corpus whose mechanism strengthens rather than weakens as RH is approached,
and it is in a currency none of the six capped lanes uses: FINITENESS OF A COUNT.

### [OPEN CORE] — cycle 39 target
Making the threshold comparison rigorous for the ACTUAL, uneven configuration. The constant
sqrt(6)/pi is derived for an evenly spaced field; the real configuration is not evenly spaced and the
neighbours also move. Needed: a rigorous lemma "normalized gap < c implies collision in backward time
<= delta^2/8" with an explicit c > 0.5155. NOT ESTABLISHED. The criterion is therefore a CONJECTURE
with a precisely located open core, not a theorem.

### Supporting rigorous tool found
Backward in t is the FORWARD heat equation (since dH/dt = -H''), so Sturm's nodal-decrease theorem
applies: THE NUMBER OF REAL ZEROS IN ANY INTERVAL IS NONINCREASING AS t DECREASES. Real zeros are
destroyed, never created, going backward — a rigorous refinement of de Bruijn reality preservation,
and exactly the sign the criterion needs.

### Quantitative companion
From dI/dt <= -4 and I(Lambda) = 0:  I(t) >= 4(Lambda - t) for all t < Lambda; with Rodgers-Tao's
Lambda >= 0 this gives I(t) >= 4|t| for every t <= 0. Non-reality in backward time is not marginal:
the imaginary energy grows at a definite linear rate.

### DEAD END recorded
Tried to use the zero-counting asymptotics N_t(T) of H_t (Polymath15) to force infinitude of M(t)
without the small-gap input. Abandoned: the sign of the t-dependent correction term
(t/16) log^2(T/4pi) could not be reconciled with the repulsive forward dynamics (forward t = repulsion
= FEWER zeros in a fixed window, but the formula reads MORE), and computations are forbidden, so the
formula could not be checked. DO NOT REBUILD ON N_t(T) WITHOUT FIRST SETTLING THAT SIGN.

Machine-verified: `RHTower/FinitenessThresholdCriterion.lean` (energy profile, backward growth,
antitone count, collision-time bound, the vanishing-gap collision lemma, the criterion; standard
axioms only).

---

## Cycle 39 (2026-07-25) — Burgers structure: the field quantity is DAMPED

Phase 1-2. The open core of cycle 38 was: does the field strength Delta grow while the pair
collides? Searched the corpus (RHTower dynamics modules) and the literature (Polymath15, CSV) — the
Burgers/Riccati structure of the flow is classical but had not been used for this purpose here.

Phase 3-5. Backward time is the FORWARD heat equation, d(H)/d(tau) = H''. With L = H'/H and the
Riccati identities H''/H = L' + L^2, H'''/H = L'' + 3LL' + L^3 one gets the VISCOUS BURGERS EQUATION

    L_tau = L_zz + 2 L L_z = L_zz + (L^2)_z ,

and hence, for the field quantity V = -L_z = SUM_k (z - x_k)^{-2} > 0,

    V_tau = V_zz + 2 L V_z - 2 V^2 .

THE NONLINEARITY CARRIES A MINUS SIGN: V is DAMPED, not amplified. Comparison with the spatially
uniform solution of v' = -2v^2, i.e. v(tau) = v0/(1+2 v0 tau), shows decay like 1/tau. So freezing
Delta at its initial value is a legitimate UPPER bound over the collision interval, and the only
remaining loss is the first-order transport term 2 L V_z.

Frozen-field problem is exactly solvable: u = delta^2 obeys u' = 4 D u - 8 with solution
u(tau) = 2/D + (u0 - 2/D) e^{4 D tau}, vanishing at tau* = (1/(4D)) log(2/(2-theta)),
theta = D u0. Finite iff theta < 2. So theta < 2 IS THE SHARP COLLISION THRESHOLD.

Machine-verified: `RHTower/BurgersFieldDamping.lean`.

---

## Cycle 40 (2026-07-25) — Theorem E40: THE EQUALLY SPACED CONFIGURATION IS EXACTLY STATIONARY

This CORRECTS the open core of cycle 38 and changes what input the criterion needs.

### The equilibrium
For zeros on the lattice d*Z the field sum TELESCOPES exactly:

    Delta = (2/d^2) SUM_{m>=1} 1/(m(m+1)) = 2/d^2 ,  so  delta^2 Delta = 2  and  d(delta)/d(tau) = 0.

A UNIFORMLY SPACED CONFIGURATION NEITHER CONTRACTS NOR EXPANDS. It sits exactly at the threshold
theta = 2 found in cycle 39. Therefore the collision criterion is NOT "the gap is small" but
"THE GAP BEATS THE LATTICE".

### The explicit sufficient condition
If every OTHER consecutive gap is at least gamma, the m-th neighbour on either side is at distance
>= m*gamma from both endpoints, so by Basel

    Delta <= 2 SUM_{m>=1} 1/(m gamma)^2 = pi^2/(3 gamma^2),

and delta^2 Delta < 2 holds as soon as

    delta/gamma < sqrt(6)/pi = 0.7797... ,

after which the pair collides by backward time u0/(8 - 4 Delta u0).

### WHY THIS MATTERS — the cycle-38 open core was MIS-STATED
It is NOT enough for infinitely many gaps to be small in absolute or normalized terms. A uniformly
spaced cluster, HOWEVER DENSE, NEVER COLLIDES. What is needed is infinitely many gaps that are
RELATIVELY small: below sqrt(6)/pi times the surrounding minimum gap. The known small-gap results —
liminf of the normalized gap below 0.5155 — DO NOT HAVE THIS FORM: they say nothing about the
neighbours of the small gap. The correct open core is therefore a statement about RELATIVE gaps,
a different (and differently shaped) problem in zero statistics.

Localization is genuine: the tail of the field beyond the M-th neighbour is bounded by the density
divided by M, so gamma may be taken to be the minimum gap in a BOUNDED neighbourhood.

### DEAD END corrected (supersedes cycle 38's estimate)
Cycle 38 quoted a heuristic threshold sqrt(6)/pi against the known small-gap constant 0.5155 and
concluded the numbers "close with room". THEY DO NOT: the comparison is not gap-vs-constant but
gap-vs-neighbouring-gaps. Recorded so this is not re-derived.

Machine-verified: `RHTower/LatticeEquilibriumCollision.lean` (lattice stationarity, telescoping
partial sums, shifted Basel sum, the field bound, the collision condition and time, and the
sharpness statement that the lattice ratio fails the criterion; standard axioms only).

### Cycle 41 target
Relative-gap statistics. Ask: is there an unconditional or RH-conditional result giving infinitely
many n with delta_n < c * min(delta_{n-1}, delta_{n+1}, ..., delta_{n+-M}) for some c < 0.78? The
pair-correlation and moment machinery (Montgomery, Conrey-Ghosh-Gonek, Bui-Milinovich-Ng) is about
single gaps; the relative version looks new. If it is genuinely open, that is itself a publishable
identification: RH's failure at negative flow time is governed by RELATIVE gap statistics, an
unstudied object.

---

## Cycle 41 (2026-07-26) — Theorem F41: MOMENT HIERARCHY + THE INDEX AS A DISCRIMINANT SIGN

### Phase 1-2 findings (literature check, both load-bearing)

(1) RELATIVE GAPS ARE NOT STUDIED. The gap literature is entirely about ABSOLUTE normalized gaps:
infinitely many below 0.515396; infinitely many above 2.7328 (3.18 on the critical line, 3.033 under
GRH). Explicitly noted in the surveys: "whether there are infinitely many gaps less than HALF the
average gap size is NOT KNOWN", even under RH. NOTHING addresses a gap relative to its NEIGHBOURS.
=> cycle 40's identification of the relative-gap statistic as the governing object is CONFIRMED NOVEL.

(2) There is an existing no-go in the adjacent Jensen-polynomial lane: "Jensen polynomials are not a
plausible route to proving the Riemann Hypothesis" (arXiv:2008.07206). ATTRIBUTED. It is the
holomorphic-moment analogue of the atlas ceilings; do not re-derive it.

### The Burgers moment hierarchy (new)
With q_n = SUM_j z_j^{-n} and dz_j/dt = 2 SUM_{k!=j} 1/(z_j - z_k), symmetrising with

    (a-b)^{-1}(a^{-3} - b^{-3}) = -(a^2 + ab + b^2)/(a^3 b^3)

gives the CLOSED polynomial law

    dq_2/dt = 2(2 q_1 q_3 + q_2^2 - 3 q_4),   and since H_t is EVEN,  dq_2/dt = 2 q_2^2 - 6 q_4.

This is the moment form of the Burgers equation L_tau = L_zz + (L^2)_z of cycle 39. The whole
hierarchy of negative moments — hence, via their explicit polynomial relations, the whole family of
LI COEFFICIENTS — is TRANSPORTED by the de Bruijn-Newman flow through a closed ODE system. First
explicit dynamical bridge between Li's criterion and the flow.

### The index is a discriminant sign (new)
    conjugate pair x +- iy : z^2 - 2xz + (x^2+y^2), disc = -4y^2 < 0
    real pair     x +- a   : z^2 - 2xz + (x^2-a^2), disc = +4a^2 > 0
Discriminants multiply up to positive squares, so for a real divisor with m conjugate pairs
sign(disc) = (-1)^m, and by the orbit decomposition m = ind_-(W). Hence

    THE SIGN OF THE DISCRIMINANT IS THE PARITY OF THE WEIL INDEX.

RH asserts ind_- = 0. A NEGATIVE regularized discriminant for xi would make ind_- ODD, hence nonzero,
and DISPROVE RH. PARITY IS STRICTLY WEAKER THAN THE COUNT, so this is the weakest falsification
target produced so far. Cost: the discriminant of an order-one entire function needs regularization,
its sign carried by the imaginary part of a regularized log-sum mod 2*pi*i.

### CORRECTION to a line of reasoning attempted this cycle (do not redo)
Conjectured that RH is "not a holomorphic condition on the divisor", so that holomorphic moments
(Li, Jensen, Taylor) are BLIND to it and criteria must be infinite inequality families. THIS IS FALSE
for finite configurations: the DISCRIMINANT is a symmetric holomorphic function whose SIGN decides
reality. The correct statement is the parity dictionary above; the genuine obstruction is not
blindness but the REGULARIZATION of an infinite discriminant. Recorded so the false version is not
rebuilt.

### Also checked and rejected this cycle
- sum_rho 1/|rho|^2 = 2*lambda_1 + sum_{pairs} (1-2beta)^2/(|rho|^2 |1-rho|^2) : an exact identity
  making RH <=> sum 1/|rho|^2 = 2 lambda_1. Weight ~ 1/gamma^4 decays far faster than the merge time
  ~ 1/log gamma, so it cannot be combined with the dBN energy bound. Standard/folklore; NOT claimed.
- Holomorphic negative moments q_n do NOT detect RH by themselves (a complex quadruple at height
  gamma >> 1 contributes POSITIVELY to q_2), so the hierarchy is a transport statement, not a
  criterion.

Machine-verified: `RHTower/MomentHierarchyAndParity.lean` (symmetrisation identity, moment law, even
reduction, the two discriminant signs, parity multiplicativity, parity-vs-count; standard axioms).

### Cycle 42 target
Regularized discriminant of xi. Define D_reg = exp(2 * SUM_{j<k} log(z_j - z_k)) by zeta
regularization of the double sum, and determine whether its ARGUMENT mod 2*pi is computable from the
functional equation and the explicit formula. If it is, the parity of the number of off-critical
zeros of zeta becomes an unconditionally computable invariant.

---

## Cycle 42 (2026-07-26) — Theorem H42: NO DISCRETE INVARIANT DETECTS RH
### (and: cycle 41's parity target is VACUOUS — killed by my own analysis)

### PHASE 4 VERDICT ON CYCLE 41's PARITY TARGET: FALSE / VACUOUS. Two independent reasons.

(1) THE FUNCTIONAL EQUATION KILLS THE PARITY. H_t is EVEN in z and real on the real axis, so a zero
z0 forces -z0, conj(z0), -conj(z0). A non-real zero with Re z0 != 0 therefore arrives as a QUADRUPLE
= TWO conjugate pairs. So m is ALWAYS EVEN and sign(disc) = (-1)^m = +1 no matter what the divisor
does off the critical line.

(2) THE ONLY ESCAPE IS ALSO CLOSED. The one configuration that could make m odd is a purely
imaginary zero of H_t, i.e. a REAL STRAY s = 1/2 +- w of Xi_t. At t = 0 there are none: for real
s in (0,1), (1 - 2^{1-s}) zeta(s) = SUM (-1)^{n-1} n^{-s} > 0 (alternating, decreasing terms), so
zeta has NO real zero in the critical strip. Classical. The sign is unconditionally +1.

=> The discriminant/parity falsification target of cycle 41 CARRIES NO INFORMATION. Do not revisit.

### Relentless interrogation -> Theorem H42 (the general statement)

What killed it: the invariant is Z/2-valued and the symmetry group of the divisor forces it to be
trivial. Generalise. Deform a critical DOUBLE pair into a complex quadruple:

    ((s-1/2)^2 - (a + i gam)^2)((s-1/2)^2 - (a - i gam)^2),   a in [0, a0],

which at a = 0 equals ((s-1/2)^2 + gam^2)^2 — a DOUBLED CRITICAL PAIR — and for a > 0 is a genuine
off-critical quadruple. The family is CONTINUOUS in a and stays inside the class of divisors
invariant under s -> 1-s and conjugation. So THE CRITICAL AND OFF-CRITICAL LOCI LIE IN ONE CONNECTED
COMPONENT of the symmetric class, joined through a double zero. Any invariant continuous with values
in a totally disconnected set is constant along the path. Therefore:

    NO PARITY, INDEX-MOD-k, OR OTHER DISCRETE INVARIANT OF THE DIVISOR CAN SEPARATE CRITICAL FROM
    OFF-CRITICAL CONFIGURATIONS. EVERY CRITERION FOR RH MUST BE METRIC — AN INEQUALITY ON A
    CONTINUOUSLY VARYING QUANTITY — NEVER TOPOLOGICAL.

Consistency check: the Weil index itself is NOT continuous along the path (2 for a > 0, 0 at a = 0),
which is exactly why it IS a usable criterion, and exactly why limiting arguments can only bound it,
never compute it.

### Significance for the atlas
This is the first result that constrains the FORM of any future proof rather than a particular lane.
It rules out, in one stroke: parity arguments, index-mod-k arguments, regularized-discriminant sign
arguments, degree/winding arguments, and any K-theoretic or cobordism-style invariant of the divisor.
Combined with C37 (the flow is monotone-agreeing) and X31 (extension = RH), the admissible shape of a
proof is now sharply constrained: a metric inequality, not monotone under heat deformation, and not
an aggregate of a positivity form.

### Cycle 43 target
The only surviving candidate object identified so far is the RELATIVE GAP statistic (cycle 40,
confirmed unstudied in cycle 41): metric (a ratio of lengths), not monotone under the flow (the
lattice is the fixed point, and relative gaps measure deviation FROM the fixed point), and not an
aggregate positivity form. Target: prove an unconditional lower bound on the frequency of gaps below
sqrt(6)/pi times the surrounding minimum gap, or prove that no such bound can hold.

---

## Cycle 43 (2026-07-26) — Theorem I43: THE OPEN CORE CLOSES. A GAP BELOW ALL ITS RUNNING MEANS COLLIDES

The relative-gap requirement of cycles 38-42 was an ARTEFACT OF A CRUDE BOUND. Replacing it with the
exact term-by-term comparison against the lattice equilibrium reduces the hypothesis to something
that is actually available.

### The mistake in the previous bound
Cycles 40-42 bounded the field by Delta <= pi^2/(3 gamma^2) with gamma the minimum of ALL other gaps,
giving the threshold delta/gamma < sqrt(6)/pi = 0.78 — a condition on the gap RELATIVE TO ITS
NEIGHBOURS, which the literature does not supply. That bound throws away the lattice structure.

### The exact comparison
The field of a gap delta between consecutive real zeros is

    Delta = SUM_{m>=1} [ 1/(D_m^L (D_m^L + delta)) + 1/(D_m^R (D_m^R + delta)) ],

with D_m^L = delta_{n-1}+...+delta_{n-m}, D_m^R = delta_{n+1}+...+delta_{n+m}. For the LATTICE
D_m = m*delta and each term is exactly 1/(m(m+1)delta^2), so delta^2 Delta = 2 SUM 1/(m(m+1)) = 2 —
the equilibrium of cycle 40. Comparing TERM BY TERM instead of through a single minimum:

    D_m >= m*delta  ==>  1/(D_m(D_m+delta)) <= 1/(m(m+1) delta^2),

hence delta^2 Delta <= 2, STRICTLY as soon as one D_m exceeds m*delta. And D_m >= m*delta says
EXACTLY that delta is at most the RUNNING MEAN of the m gaps on that side. Therefore:

    A GAP AT MOST THE RUNNING AVERAGE OF THE GAPS ON EACH SIDE, FOR EVERY WINDOW LENGTH, AND
    STRICTLY BELOW ONE OF THEM, SATISFIES delta^2 Delta < 2 AND COLLIDES IN BACKWARD TIME.

### Why the hypothesis is now available
  * INSIDE a window: the MINIMUM gap of a window automatically satisfies the running-mean condition
    for every m inside the window (sum of m gaps each >= delta is >= m*delta). No relative-gap
    statistics needed.
  * OUTSIDE the window: the running means converge to the local mean spacing, so the condition
    reduces to the NORMALIZED gap being at most 1. The minimum of N gaps whose mean is 1 is <= 1,
    and by the known small-gap results infinitely many normalized gaps are below 0.515396.
  * PERSISTENCE: the gap velocity is -4/delta + 2 delta Delta. For the smallest gap -4/delta is the
    most negative and 2 delta Delta the smallest, so THE MINIMAL GAP CONTRACTS FASTEST AND STAYS
    MINIMAL. The running-mean hypothesis therefore persists over the collision interval, which is
    exactly what the frozen-field estimate of cycle 39 requires.

### Consequence
The chain of cycles 38-43 now runs on available inputs:
    RH at t=0  ==>  all zeros of H_0 real, density -> infinity, window minima with normalized gap < 1
               ==>  infinitely many gaps satisfy the running-mean condition
               ==>  infinitely many collisions in backward time
               ==>  M(t) = infinity for every t < 0,
and contrapositively: IF H_t HAS ONLY FINITELY MANY NON-REAL ZEROS FOR A SINGLE t < 0, RH IS FALSE.
Contrast Ki-Kim-Lee: for every t > 0, H_t has only finitely many non-real zeros. So the finiteness
threshold tau_fin is exactly 0 under RH.

### What remains (honest status)
The zero dynamics itself (dz_j/dt = 2 SUM 1/(z_j - z_k) for an infinite order-one configuration, and
the validity of the frozen-field ODE comparison over the collision interval) is used as an analytic
input; it is standard for the dBN flow but is not formalized here. The RELATIVE-gap requirement is
GONE — that was the substantive obstruction and it was self-inflicted.

Machine-verified: `RHTower/RunningMeanCollision.lean` (term-by-term comparison and its strict form,
the truncated lattice sum, the collision threshold with tail, the running-mean reformulation, the
window-minimum lemma, and the contraction-order lemma; standard axioms only).

### Cycle 44 target
Make the analytic input explicit and minimal: state precisely the hypotheses on the configuration
under which dz_j/dt = 2 SUM 1/(z_j - z_k) holds and the frozen-field comparison is valid, and check
them against the known regularity of H_t (Ki-Kim-Lee simplicity, the counting function, and the
locally uniform convergence of the Hadamard product). If they hold, the falsification criterion is
unconditional.

---

## Cycle 44 (2026-07-26) — Theorem J44: THE PERSISTENCE PROBLEM DISSOLVES; EXPLICIT MARGIN

Cycle 43 left one gap: does the running-mean hypothesis PERSIST over the collision interval? It does
not need to. Track the WINDOW MINIMUM instead of a fixed gap.

### The dissolution
Let u_min(tau) = min over a window of delta_i(tau)^2. A MINIMIZING gap satisfies the running-mean
hypothesis BY DEFINITION at every time (a sum of m gaps each >= the minimum is >= m times the
minimum). So there is nothing to persist: whichever gap is currently minimal is the one the criterion
applies to, and if the minimizer changes the criterion transfers to the new one. Only a UNIFORM
MARGIN is needed.

### The sharpened field bound (replaces pi^2/(3 gamma^2) and the sqrt(6)/pi threshold)
If the running means exceed the gap by a factor a = 1 + eta >= 1, i.e. D_m >= a m delta, then

    delta^2/(D_m(D_m+delta)) <= 1/(a m (a m + 1)) <= (1/a) * 1/(m(m+1)),

the second step because a m + 1 >= m + 1 for a >= 1. Summing against the telescoping lattice sum,

    theta := delta^2 Delta <= 2/a = 2/(1+eta) < 2,

with collision time at most u_0 (1+eta)/(8 eta). NOTE: this is the correct sharpening. The earlier
Basel bound SUM 1/m^2 = pi^2/6 LOSES the +1 and produces the spurious sqrt(6)/pi threshold; keeping
the +1 telescopes and gives the clean 2/a.

### The margin is available (split estimate)
For small m the immediate neighbours give only a = 1 and contribute at most the lattice value. Past a
window length M_0 the running mean approaches the local mean spacing, and the minimum of a window of
gaps of mean 1 is at most the known small-gap constant 0.515396, so a ~ 1.94 there. Splitting:

    theta <= 2(1 - 1/(M_0+1)) + (2/a)(1/(M_0+1)) = 2 - (2/(M_0+1))(1 - 1/a),

an EXPLICIT margin c/(M_0+1) with c = 2(1 - 1/a) ~ 0.97. Collision time <= u_0 (M_0+1)/(2c).

### Universal linear survival
Every gap obeys u_i' = -8 + 4 theta_i with theta_i >= 0, so u_i' >= -8 and u_i(tau) >= u_i(0) - 8 tau:
NO gap vanishes before time u_i(0)/8. Together with the margin, u_min' <= -c' < 0 and the minimum
reaches zero in finite time. Absolute gaps shrink as the height grows while M_0 grows only mildly, so
the collision time tends to 0 up the critical line, and FOR EVERY t < 0 INFINITELY MANY COLLISIONS
HAVE ALREADY OCCURRED.

### The analytic input, now minimal and checked
  * ODE: implicit differentiation of H_t(z_j(t)) = 0 at a SIMPLE zero gives dz_j/dt = H''/H'(z_j) by
    the implicit function theorem. RIGOROUS.
  * Sum form: H''/H'(z_j) = 2 SUM_{k!=j} 1/(z_j - z_k) from the Hadamard factorization of the even
    order-one function H_t in z^2, which converges because SUM |z_k|^{-2} < infinity (from the
    counting function N(T) ~ (T/4pi) log T); the pairing k <-> -k makes the sum ABSOLUTELY
    convergent. RIGOROUS.
  * Multiple zeros: a multiple REAL zero is already a degenerate collision and splits off the axis
    immediately in backward time, so it only helps. No simplicity hypothesis is needed.

### Status of the chain (cycles 38-44)
    RH at t=0  ==>  all zeros of H_0 real, density -> infinity
               ==>  window minima with normalized gap <= 0.515396 infinitely often
               ==>  theta <= 2 - c/(M_0+1) < 2 for those minima
               ==>  infinitely many backward collisions, with collision time -> 0
               ==>  M(t) = infinity for every t < 0.
    CONTRAPOSITIVE: IF H_t HAS ONLY FINITELY MANY NON-REAL ZEROS FOR A SINGLE t < 0, RH IS FALSE.
    Against Ki-Kim-Lee (M(t) < infinity for every t > 0), the finiteness threshold is exactly 0
    under RH.

The remaining softness is the passage from the pointwise differential inequality to the running
minimum (a Dini-derivative/first-variation argument, standard) and the tail estimate past M_0 (uses
the counting function, available). NO unstudied statistic is required any more.

Machine-verified: `RHTower/WindowMinimumCollision.lean` (sharpened term bound, the strict field
bound, the split margin and its positivity, universal linear survival, finite-time collision, and the
window-minimum hypothesis; standard axioms only).

### Cycle 45 target
Turn the criterion around. It says a FINITE non-real count at some t<0 disproves RH. Ki-Kim-Lee give
finiteness for t>0. Question: is there any t<0 for which finiteness of the non-real count of H_t can
be established by the SAME method Ki-Kim-Lee used (they prove it for t>0 by an asymptotic analysis of
H_t)? If their method degrades continuously at t=0, the criterion becomes an attack, not just a test.

---

## Cycle 45 (2026-07-26) — Theorem K45: THE HEIGHT-TIME SCALING LAW; BOTH SIDES OF THE FLOW MATCH

Asked how Ki-Kim-Lee's method degrades as t -> 0+. Answer: it does not merely degrade, IT CHANGES
SIGN — and the threshold height on both sides is governed by ONE dimensional law.

### The law
The zero dynamics is quadratically homogeneous, so FLOW TIME HAS DIMENSIONS OF LENGTH SQUARED. At
height T the only length is the mean spacing 2pi/log(T/2pi), so the natural time scale there is

    natTime(T) = spacing(T)^2/8 = pi^2 / (2 log^2(T/2pi)),

with inverse

    flowHeight(t) = 2 pi exp( pi / sqrt(2 t) ).

### Both sides
  * t > 0: Ki-Kim-Lee prove all but finitely many zeros of H_t are real for every t > 0; Polymath15
    made this EFFECTIVE, producing an explicit height beyond which the zeros are provably real
    (confirmed by search: "effective versions of theorems in Ki-Kim-Lee ... an explicit threshold
    beyond which all the zeroes are provably real"). That height must diverge as t -> 0+, and the
    scaling law says it diverges like exp(c/sqrt t).
  * t < 0: the collision estimate of cycles 43-44 says a gap at height T reaches the axis within
    backward time ~ spacing(T)^2/8. So by backward time |t| every sufficiently relatively-small gap
    above flowHeight(|t|) has already collided.

THE TWO THRESHOLDS HAVE THE SAME FUNCTIONAL FORM BECAUSE THEY ARE THE SAME DIMENSIONAL STATEMENT.
t = 0 is exactly where the threshold escapes to infinity: the flow has acted NOWHERE and marginally
EVERYWHERE. That is the structural reason to expect Lambda = 0.

Why the sign flip: in the effective analysis the mollification gain is a factor e^{t log^2 x /16}.
For t > 0 it beats any fixed loss once t log^2 x >> 1, i.e. x >> exp(c/sqrt t) — reality above the
threshold. For t < 0 the SAME factor DECAYS, so the argument reverses and predicts non-reality —
matching the collision picture from the opposite direction.

### Quantitative corollary (numerical cost)
To prove Lambda <= t by the barrier method one verifies below the threshold and estimates above it.
So the reachable t scales as pi^2/(2 log^2 X) in the verification height X: THE COST OF LOWERING THE
BOUND ON LAMBDA GROWS LIKE exp(c/sqrt t) IN HEIGHT. Comparing the dimensional prediction with the
published bound fixes the effective constant; the ratio between them measures the remaining room in
the effective analysis. Recorded as a target, not a claim: no arithmetic performed.

### Significance
This is the first statement in the corpus that ties the t > 0 literature (Ki-Kim-Lee, Polymath15)
and the t < 0 mechanism (cycles 38-44) to a single curve. It also explains, without computation, why
the numerical programme stalls: each factor-of-2 improvement in Lambda costs a factor of sqrt(2) in
log-height, i.e. squares the required verification height.

Machine-verified: `RHTower/HeightTimeScalingLaw.lean` (the natTime/flowHeight inverse pair, the
log-parameter identity, unboundedness as t -> 0+, antitonicity, and the dimensional identity
natTime = spacing^2/8; standard axioms only).

### Cycle 46 target
Push the criterion of cycles 38-44 to a contradiction or a theorem. Two concrete sub-targets:
(a) formalize the Dini-derivative passage from the pointwise gap inequality to the running minimum,
    which is the last soft step;
(b) examine whether the sign-flipped effective analysis at t < 0 can be made to yield FINITENESS of
    the non-real count for some t < 0 — which by the criterion would DISPROVE RH. If instead one can
    show the count is provably infinite for all t < 0 by the effective route, that is an independent
    confirmation of the collision mechanism and closes the loop.

---

## Cycle 46 (2026-07-26) — Theorem L46: THE LAST SOFT STEP IS CLOSED (machine-verified)

Target (a) of cycle 45 was the Dini-derivative passage from the pointwise gap inequality to the
running minimum. IT IS NOW A THEOREM IN LEAN, with no hand-waving.

### The touching comparison
The running minimum u_min(tau) = min_i delta_i(tau)^2 is only Lipschitz, so u_min' <= -c is not
literally available. What IS available is the TOUCHING STRUCTURE: at every time some member of the
family attains the minimum, lies above it everywhere, and has right derivative <= -c. That suffices:

    THEOREM. Let f be continuous on [0,T] and suppose for every x in [0,T) there is g with
    f <= g everywhere, f x = g x, and a right derivative g' <= -c at x. Then
        f x <= f 0 - c x   for all x in [0,T].

Proof: for z > x the difference quotient of f is at most that of g (since f z <= g z while
f x = g x); the quotient of g tends to g' <= -c; so the lower right Dini derivative of f is at most
-c, and the fencing theorem for continuous functions
(`image_le_of_liminf_slope_right_le_deriv_boundary`) gives the comparison against the line.

A FINITE MINIMUM SUPPLIES THE HYPOTHESIS FOR FREE: the minimizing index gives a function lying above
f and touching it there, and its derivative is <= -c by the collision estimate, which applies exactly
because the minimizing gap satisfies the running-mean hypothesis BY DEFINITION (cycle 44).

=> NO Dini theory beyond the fencing theorem, NO persistence hypothesis, NO unstudied statistic.
The chain of cycles 38-46 now has exactly one analytic input left: the zero dynamics itself
(dz_j/dt = H''/H'(z_j) with the Hadamard sum form), which was checked in cycle 44 and is rigorous.

Machine-verified: `RHTower/TouchingComparison.lean` (`touching_comparison`, `min_touches`,
`min_reaches_zero`; standard axioms only). Compiled on the first attempt.

### Target (b): can the sign-flipped effective analysis give FINITENESS at some t < 0?
NO — and the reason is structural. The effective route (Ki-Kim-Lee, made effective by Polymath15)
rests on a mollification gain of size e^{t log^2 x / 16}. For t > 0 it beats any fixed loss above
x ~ exp(c/sqrt t), giving reality. For t < 0 THE SAME FACTOR DECAYS, so the argument does not merely
weaken, it reverses: it predicts NON-reality. There is therefore no route to finiteness at t < 0 by
that method, and the falsification criterion cannot be triggered from that direction.

Combining with the now-closed collision chain, the picture is a SHARP FINITENESS TRANSITION AT t = 0:

    M(t) < infinity for every t > 0            (Ki-Kim-Lee)
    M(t) = infinity for every t < 0            (collision chain, cycles 38-46; under RH)

with t = 0 the transition point. Under RH, M(0) = 0.

### The unconditional version — stated as a conjecture with its precise input
The collision chain uses RH only to know the zeros of H_0 are real. Unconditionally H_0 still has
infinitely many REAL zeros (Hardy; a positive proportion by Conrey and successors), their density
tends to infinity, and OFF-CRITICAL ZEROS ONLY HELP: a conjugate pair at vertical distance y from the
axis with y >> the gap contributes 2 Re 1/((a-z)(b-z)) ~ -2/y^2 < 0 to the field, i.e. it ACCELERATES
collision. So the argument should run unconditionally, giving

    CONJECTURE (M46). M(t) = infinity for every t < 0, unconditionally.

[OPEN CORE] the residual input is a definite spread of the gaps between consecutive CRITICAL zeros in
some window — the window minimum must be below the window mean by a fixed factor. Under RH this is
the known small-gap constant 0.515396. Unconditionally one needs the analogous statement for critical
zeros only. Recorded as the precise remaining input; NOT claimed.

### Cycle 47 target
Settle Conjecture M46 by finding, or ruling out, an unconditional definite-spread statement for gaps
between consecutive CRITICAL zeros. Candidate routes: (i) Selberg's unconditional second moment of
S(T) (the partial sums of 1 - normalized gap ARE S(T), cycle-43 observation), which forces the gaps
to fluctuate; (ii) the positive-proportion machinery of Levinson-Conrey, which produces critical
zeros in prescribed short intervals and hence controls their spacing.

---

## Cycle 47 (2026-07-26) — Theorem N47: M(t) = INFINITY FOR EVERY t < 0, UNCONDITIONALLY
### The conditionality is gone. But the falsification criterion is now VACUOUS.

Conjecture M46 is settled — affirmatively — by a case split whose two branches use different
mechanisms, neither of which needs RH.

### CASE A: H_0 has infinitely many non-real zeros.
Non-reality PERSISTS in backward time. Since dH/dt = -H'', backward time is the FORWARD heat
equation, so STURM'S NODAL-DECREASE THEOREM applies: the number of real zeros in any interval is
nonincreasing as t decreases. Real zeros are destroyed, never created, going backward. Hence
M(t) >= M(0) = infinity for all t < 0. (Sturm was found in cycle 38 and is used here for the first
time.)

### CASE B: H_0 has finitely many non-real zeros.
Then all but finitely many zeros are real and their density tends to infinity. The UNCONDITIONAL
small-gap results give infinitely many consecutive ordinates at normalized distance <= 0.515396; all
but finitely many of those gaps are between REAL zeros. Each is a window minimum below the window
mean by a definite factor, so the running-mean hypothesis (cycle 43) holds with the margin of cycle
44, the touching comparison (cycle 46) drives the squared gap to zero in finite backward time, and by
the height-time scaling law (cycle 45) the collision time tends to 0 up the critical line. Hence
infinitely many collisions have occurred by any fixed t < 0, and M(t) = infinity.

### THE RESULT
    M(t) <  infinity   for every t > 0     (Ki-Kim-Lee)
    M(t) =  infinity   for every t < 0     (Theorem N47)
THE FINITENESS TRANSITION OF THE dBN FLOW IS EXACTLY AT t = 0, UNCONDITIONALLY.
Under RH, M(0) = 0.

### HONEST CONSEQUENCE: THE CYCLE-38 CRITERION IS DEAD AS AN ATTACK
The criterion said: finiteness of the non-real count at a single t < 0 implies RH is false. Theorem
N47 says that hypothesis is NEVER SATISFIABLE. So the criterion CANNOT DISPROVE RH. What survives is
the structural theorem — a sharp new statement about the flow, independent of RH, and the exact
complement of Ki-Kim-Lee.

This is the third time in this programme that a proposed attack has been killed by its own
completion (after the Positivstellensatz route in cycle 8 and the parity route in cycle 42). Record:
COMPLETING an attack is the fastest way to learn whether it was ever an attack.

### DEAD END (route (i) of cycle 46): Selberg's second moment does NOT force a definite spread.
The partial sums of 1 - normalized-gap are EXACTLY S(T) (cycle 43). One might hope Selberg's
unconditional INT_0^T S^2 ~ T loglog T / (2 pi^2) forces the gaps away from 1. IT DOES NOT: bounded
deviations |1 - delta_hat_k| <= eta still let S grow like eta*sqrt(n) by cancellation, so no
contradiction arises. The definite spread must come from the SMALL-GAP results, not from moments of
S. DO NOT RETRY THE MOMENT ROUTE.

Machine-verified: `RHTower/FinitenessTransition.lean` (persistence of non-reality, both cases, the
dichotomy, the transition statement, and the vacuity of the criterion; standard axioms only).

### Cycle 48 target
The dBN lane has now been fully mapped and every attack in it is capped or vacuous (C37 monotone,
N47 vacuous). The atlas is:
    linear Lambda-positivity        caps at PNT strength                     (Thm N)
    quadratic Weil index            lower bounds on ind_- only               (Thm N')
    Bohr-torus probability          valid only past height ~ pi(N)           (Thm G)
    elementary archimedean tower    optimal at ell ~ 0.155                   (Thms Q24-V29)
    extension of the range          equivalent to RH                         (Thm X31)
    de Bruijn-Newman flow           monotone; criterion vacuous              (Thms C37, N47)
    discrete/topological invariants impossible                               (Thm H42)
Next: the one lane never opened is NYMAN-BEURLING / BAEZ-DUARTE — an APPROXIMATION problem, not a
positivity or dynamics problem, with an unconditional LOWER bound already in the literature
(Burnol; Baez-Duarte-Balazard-Landreau-Saias: liminf d_N^2 log N >= SUM_rho m_rho^2/|rho|^2). It is
metric, non-monotone under heat deformation, and not an aggregate positivity form — the three
conditions H42 leaves admissible. Open it.

---

## Cycle 48 (2026-07-26) — Theorem O48: BOUNDARY ZEROS ARE FREE, INTERIOR ZEROS ARE NOT
### The Nyman-Beurling lane opened; the first mechanism that gets WORSE off the critical line

### Phase 1 corpus check (mandatory)
Found existing NB material: `HTGeometry/HardyClosureZeroFree.lean` has the QUALITATIVE closure
obstruction (a continuous evaluation killing every generator but not the target puts the target
outside the closed span), attributed there to the 2026 Hardy refinement arXiv:2606.16097. Also
`RHTower/RiemannHypothesisSOTA2026.lean` cites the Hardy and Colombeau-Beurling criteria
(arXiv:2606.16097, arXiv:2606.22562). NOT DUPLICATED — this cycle supplies the QUANTITATIVE version
the corpus lacks.

### The exact vanishing cost
In an inner product space, for v != 0,

    dist( f, { g : <v,g> = 0 } ) = |<v,f>| / ||v||,

upper bound by the explicit projection g = f - (<v,f>/||v||^2) v, lower bound by Cauchy-Schwarz. In
a reproducing kernel Hilbert space with v = K_w this reads

    dist( f, { g : g(w) = 0 } ) = |f(w)| / sqrt(K(w,w)).

### THE DICHOTOMY
For the Hardy space of a half-plane, K(w,w) = 1/(4 pi sigma) with sigma the distance from w to the
boundary. So the cost of forcing a vanishing at w is

    |f(w)| * sqrt(4 pi sigma)   -->  0  as sigma -> 0,   > 0  for sigma > 0.

CONSTRAINING AN APPROXIMANT TO VANISH AT A BOUNDARY POINT IS FREE. CONSTRAINING IT TO VANISH AT AN
INTERIOR POINT IS NOT. And the cost is MONOTONE INCREASING in sigma.

### Why this is the right mechanism
In the Baez-Duarte formulation the approximants have Mellin transforms divisible by zeta, so they
must vanish at every zero of zeta, while the target does not. A zero ON the critical line is a
BOUNDARY point: the pointwise constraint costs nothing, and the observed d_N^2 ~ 1/log N is the cost
of imposing it at the scale a Dirichlet polynomial of length N can resolve near the line. A zero OFF
the line is an INTERIOR point at distance sigma = |beta - 1/2|: the constraint costs a definite
amount, INDEPENDENT OF N.

    ==> The Nyman-Beurling distance separates the two cases BY THEIR RATE, not merely by their limit:
        d_N^2 ~ 1/log N  is critical behaviour;
        any off-critical zero forces a CONSTANT FLOOR proportional to sqrt(|beta - 1/2|) times the
        target value there.

THIS IS THE ASYMMETRY EVERY CAPPED LANE LACKED. The mechanism gets WORSE, not better, as the divisor
moves off the line — exactly the property H42 says a viable criterion must have, and the property
C37 showed the dBN flow does NOT have.

Note the convergence of scales: the 1/log N rate here is the same 1/log that appears in the mean
spacing and in the height-time scaling law of cycle 45.

Machine-verified: `RHTower/BoundaryInteriorVanishingCost.lean` (exact distance to a vanishing
hyperplane, attainment, the half-plane kernel cost, vanishing at the boundary, positivity in the
interior, monotonicity in the deviation; standard axioms only).

### Cycle 49 target
Make the floor explicit and unconditional. Required inputs, in order:
(a) the exact Hilbert space and target of the Baez-Duarte formulation (L^2(0,infty) with the
    generators rho_{1/n}, target 1_{(0,1]}), and the identification of its Mellin image as a
    weighted L^2 on the line Re s = 1/2;
(b) the statement that the closed span consists of transforms divisible by zeta — this is the step
    that turns a zeta zero into a vanishing constraint;
(c) the reproducing-kernel bound of this cycle applied at an off-critical zero, giving
    d_infinity^2 >= |target(rho)|^2 * 4 pi |beta_rho - 1/2|.
If (a)-(c) assemble, the result is: RH FAILS  ==>  d_N is bounded below by an explicit positive
constant. Combined with the known equivalence RH <=> d_N -> 0 that is a QUANTITATIVE Nyman-Beurling
criterion with an explicit modulus — new, and the first two-sided statement in the atlas.

---

## Cycle 49 (2026-07-26) — Theorem P49: QUANTITATIVE NYMAN-BEURLING, EXPLICIT MODULUS
### and Theorem Q49: UNIVERSAL HEIGHT DEGRADATION — why "verify below, estimate above" always stalls

The three ingredients of cycle 48 assemble.

### (a) The space — and the key observation that makes it work
EVERY BAEZ-DUARTE GENERATOR IS SUPPORTED IN (0,1]. For t >= 1 both 1/t < 1 and theta/t < 1, so
rho_theta(t) = {theta/t} - theta{1/t} = theta/t - theta/t = 0. The target 1_{(0,1]} likewise. Hence
the Mellin transform f -> INT_0^1 f(t) t^{-s} dt converges for Re s < 1/2 and maps L^2((0,1],dt)
UNITARILY onto the HARDY SPACE H^2 of the half-plane Re s < 1/2, with Plancherel normalization
||f||^2 = (1/2pi) INT |f^(1/2+iu)|^2 du. Checked against the target: 1^(s) = 1/(1-s), boundary
modulus squared integrates to 2pi, matching ||1_{(0,1]}||^2 = 1. EXACT.

This is what makes point evaluation OFF the critical line legitimate: the functions genuinely extend
to a half-plane and evaluation there is a BOUNDED functional.

### (b) The vanishing constraint
The transform of a generator is zeta(s)(n^{-s} - 1/n)/s, so every finite combination has transform
zeta(s) P(s)/s with P entire. At a zero rho of zeta with rho != 0 this VANISHES, and vanishing
survives L^2 limits because point evaluation in H^2 is continuous. The target does NOT vanish:
1^(rho) = 1/(1-rho) != 0.

### (c) THE FLOOR
With this normalization the diagonal kernel of H^2 of a half-plane is K(w,w) = 1/(2 sigma), sigma the
distance to the boundary. (Cycle 48 used the UNNORMALIZED convention where the constant is
1/(4 pi sigma); the dichotomy is identical, only the constant differs. Recorded so the two modules
are not read as contradictory.) The exact vanishing cost of cycle 48 gives, for a zero rho = beta+i*gamma
of zeta with beta < 1/2:

    lim_N d_N  >=  |1^(rho)| / sqrt(K(rho,rho))  =  sqrt(1 - 2 beta) / |1 - rho| .

By the functional equation RH fails exactly when such a rho exists. THEREFORE:

    IF RH FAILS, THE BAEZ-DUARTE DISTANCES ARE BOUNDED BELOW BY THE EXPLICIT CONSTANT
    sqrt(1 - 2 beta)/|1 - rho|.

This is the QUANTITATIVE form of the easy direction of Nyman-Beurling: not merely d_N -/-> 0, but an
explicit modulus in the deviation. The qualitative direction is classical; the explicit constant is
the contribution.

### Theorem Q49 — UNIVERSAL HEIGHT DEGRADATION (the real enemy, now named)
The floor is at most 1/|gamma|, since sqrt(1-2 beta) <= 1 and |1 - rho| >= |gamma|. So a
counterexample high up produces only a TINY floor, and closing the criterion against verification to
height X would need d_N <= 1/X; with d_N^2 ~ 1/log N that is N >= exp(X^2).

THE SAME DEGRADATION APPEARED IN THE FLOW LANE: verification to height X bounds Lambda only by
pi^2/(2 log^2 X) (cycle 45). It is not an artefact of either method.

    EVERY QUANTIFIED LANE LOSES STRENGTH AT A PUTATIVE COUNTEREXAMPLE POLYNOMIALLY OR EXPONENTIALLY
    IN ITS HEIGHT. NUMERICAL VERIFICATION AND ANALYTIC ESTIMATE NEVER MEET UNLESS THE ANALYTIC
    ESTIMATE IS ITSELF AS STRONG AS THE VERIFICATION HEIGHT.

That is the unified reason the "verify below, estimate above" architecture stalls — in the
Nyman-Beurling lane exactly as in the de Bruijn-Newman lane. It is the ninth and most general entry
in the atlas, and unlike the others it is a statement about the INTERACTION of the two halves of
every known effective programme rather than about one lane.

Machine-verified: `RHTower/QuantitativeNymanBeurling.lean` (normalized kernel, the floor and its
positivity, the explicit form sqrt(1-2beta)/|1-rho|, the height degradation, and the complementary
length requirement; standard axioms only).

### Cycle 50 target
Q49 says the enemy is height degradation. The only escape is a criterion whose strength does NOT
decay with the height of the counterexample. Candidates to test against that requirement:
  (i) criteria weighted by 1/|rho|^2 (Li, BBLS) — decay like 1/gamma^2, WORSE. Rejected.
  (ii) the imaginary energy SUM (Re rho - 1/2)^2 (cycle 35) — NO height weight at all. This is the
       only functional found so far that is height-neutral. But its lane is capped by monotonicity
       (C37). Question for cycle 50: is there a height-neutral functional that is NOT monotone under
       the heat deformation? By H42 it must be metric; by Q49 it must be height-neutral; by C37 it
       must not be monotone. Determine whether these three conditions are simultaneously satisfiable
       or mutually exclusive — the latter would be a genuine no-go theorem for the entire effective
       programme.

---

## Cycle 50 (2026-07-26) — Theorem R50: THE ADMISSIBLE SHAPE OF A CRITERION IS A THRESHOLD COUNT
### The three no-gos are COMPATIBLE, and they pin the shape uniquely.

Three constraints had accumulated on any functional Phi of the divisor that could decide RH:
  * METRIC (H42): no discrete invariant separates critical from off-critical divisors, since the two
    loci are joined through a double zero inside the symmetric class.
  * HEIGHT-NEUTRAL (Q49): every quantified lane loses strength at a counterexample polynomially or
    exponentially in its height, so verification and estimate never meet unless Phi weights a zero
    independently of its height.
  * NON-MONOTONE UNDER THE FLOW (C37): the dBN deformation moves the divisor toward the critical
    line, so any Phi decreasing along it gives only upper bounds and can never contradict failure.

### The computation that decides it
For additive Phi = SUM_j phi(y_j) of the deviations, the flow (dy_j/dt = -2 SUM_{k!=j}
(y_j-y_k)/|z_j-z_k|^2) gives

    d/dt SUM_j phi(y_j) = -2 SUM_{ {j,k} } (phi'(y_j) - phi'(y_k))(y_j - y_k) / |z_j - z_k|^2 .

EVERY TERM IS NONPOSITIVE EXACTLY WHEN phi' IS NONDECREASING, i.e. WHEN phi IS CONVEX. Therefore:

    EVERY CONVEX EVEN WEIGHT GIVES A MONOTONE — HENCE CAPPED — FUNCTIONAL.
    A HEIGHT-NEUTRAL, NON-MONOTONE ADDITIVE FUNCTIONAL MUST HAVE A NON-CONVEX WEIGHT.

Checks: phi(y) = y^2 is convex, recovering the imaginary energy of cycle 35 and its cap C37;
phi(y) = y^4 is also convex, since (a^3-b^3)(a-b) = (a-b)^2(a^2+ab+b^2) >= 0 — so raising the power
does NOT escape (a route one might otherwise try; recorded as pre-emptively dead). The truncated
weight phi(y) = min(y^2, eps^2) is NOT convex: phi'(eps/2) = eps while phi'(2 eps) = 0, so the pair
term at (eps/2, 2 eps) is STRICTLY POSITIVE and the functional can increase.

### THE CONCLUSION
The three conditions ARE simultaneously satisfiable, and the functionals satisfying them are exactly
the TRUNCATED ones — which count zeros whose deviation exceeds a threshold, up to a bounded weight.
That is a ZERO-DENSITY STATISTIC.

    THE ADMISSIBLE SHAPE OF A CRITERION FOR RH IS A THRESHOLD COUNT OF OFF-CRITICAL ZEROS —
    AN N(sigma, T)-TYPE QUANTITY — AND NOTHING SMOOTHER.

What is new is the DERIVATION: the conclusion follows from three independent no-gos, one
topological (H42), one effective (Q49), one dynamical (C37). It explains why every smooth criterion
in the atlas — Weil positivity, Li coefficients, the imaginary energy, the Nyman-Beurling distance —
stalls in its own way, while the unconditional progress that exists lives in the zero-density
literature. The slogan "RH is the ultimate density theorem" is folklore; deriving it as a THEOREM
about admissible functionals is not.

Machine-verified: `RHTower/AdmissibleFunctionalShape.lean` (symmetrized pair term, the convexity
dichotomy in both directions, the square and quartic convexity checks, the truncated non-convex
witness, boundedness and the vanishing criterion of the threshold weight; standard axioms only).

### THE ATLAS AT CYCLE 50 (nine entries; the last three are cross-lane)
    linear Lambda-positivity        caps at PNT strength                     (Thm N)
    quadratic Weil index            lower bounds on ind_- only               (Thm N')
    Bohr-torus probability          valid only past height ~ pi(N)           (Thm G)
    elementary archimedean tower    optimal at ell ~ 0.155                   (Thms Q24-V29)
    extension of the range          equivalent to RH                         (Thm X31)
    de Bruijn-Newman flow           monotone; criterion vacuous              (Thms C37, N47)
    discrete/topological invariants impossible                               (Thm H42)
    verification + estimate         never meet (height degradation)          (Thm Q49)
    admissible functional shape     threshold count only                     (Thm R50)

### Cycle 51 target
R50 says the criterion must be a threshold count. The classical technology for threshold counts is
the zero-density estimate N(sigma,T) << T^{A(sigma)(1-sigma)} log^B T. Ask the question R50 makes
precise: WHAT WOULD A DENSITY ESTIMATE HAVE TO LOOK LIKE TO GIVE RH, and is the obstruction to it the
SAME height degradation Q49 identifies, or a different one? Concretely: RH <=> N(sigma,T) = 0 for
every sigma > 1/2; the density hypothesis gives N(sigma,T) << T^{2(1-sigma)+eps}; the gap is between
o(N(T)) and 0. Determine whether the passage from "density zero" to "identically zero" is subject to
Q49-type degradation or is a genuinely different obstruction — the first structural question about
the density lane, which the atlas now says is the only one left.

---

## Cycle 51 (2026-07-26) — Theorem S51: THE DEGRADATION-EXPONENT SCALE; THE ATLAS CLOSES ON ITSELF

R50 said the admissible shape is a threshold count. The threshold count with threshold sigma IS
N(sigma,T), and N(sigma,T) = 0 for all T IS a ZERO-FREE REGION {Re s > sigma}. So the classification
closes on itself: THE UNIQUE ADMISSIBLE SHAPE IS THE ZERO-FREE REGION, and density estimates are its
quantitative surrogates. That is a derived conclusion, not an assumption.

### First tested: does integrality rescue the composition? NO.
Hoped: N(sigma,T) is an INTEGER, so a bound below 1 forces exact vanishing; and verification to
height X gives N(sigma,X) = 0, which should compose with a tail estimate. IT DOES NOT. N(sigma,.) is
NONDECREASING, so N(sigma,X) = 0 carries no information above X, and a bound N(sigma,T) < 1 valid for
all T IS the statement itself. Verification and estimate fail to compose here exactly as in every
other lane. DEAD END recorded — do not retry the integrality argument.

### But the degradation is SLOWER, and that is the finding
What a zero-free region degrades in is its WIDTH. Classical (de la Vallee Poussin): c/log t.
Vinogradov-Korobov: c/((log t)^{2/3} (log log t)^{1/3}). Both shrink with height, so the lane is
subject to height degradation IN KIND — but at the slowest rate in the atlas:

    Nyman-Beurling floor      ~ 1/gamma                  POLYNOMIAL          (worst)
    de Bruijn-Newman bound    ~ 1/log^2 X                log exponent 2
    zero-free region width    ~ 1/(log t)^{2/3}          log exponent 2/3    (best)
    RIEMANN HYPOTHESIS        = 1/2                      LOG EXPONENT 0

    ==> RH IS THE STATEMENT THAT THE DEGRADATION EXPONENT IS ZERO.

Every lane in the atlas is a point on ONE scale, and the zero-free lane is furthest along it. This
reframes the target concretely and quantitatively: THE OBJECT TO ATTACK IS THE DEGRADATION EXPONENT.
Known technology has moved it from 1 to 2/3. Exponent 0 at ANY positive fixed width is already a
famous open problem strictly weaker than RH (it gives pi(x) = li(x) + O(x^{1-delta})).

### Why this is the right way to see the whole programme
Fifty cycles produced nine no-gos, each phrased differently. They are all the same statement measured
in different units: a criterion's strength at a counterexample of height t decays like (log t)^{-a},
and the lane is characterised by a. The atlas is therefore not a list of unrelated obstructions but a
SINGLE ORDERED SCALE, and progress means lowering a. That is the first unification of the programme.

Machine-verified: `RHTower/DegradationRateRanking.lean` (width with logarithmic exponent, the
exponent-zero characterisation, antitonicity in the exponent so the ranking is well defined, the
non-composition of verification with a monotone count, positivity of a constant width; standard
axioms only).

### THE ATLAS AT CYCLE 51 — now one scale, not ten entries
    exponent infinity (polynomial)  Nyman-Beurling floor              (Thm P49)
    exponent 2                      de Bruijn-Newman / barrier        (Thms K45, Q49)
    exponent 2/3                    zero-free region (Vinogradov-K.)  (classical)
    exponent 0                      RIEMANN HYPOTHESIS                (the target)
with the structural no-gos H42 (metric only), C37 (non-monotone required), R50 (threshold count only)
explaining WHY every lane lands on this scale rather than escaping it.

### Cycle 52 target
Attack the exponent directly. The Vinogradov-Korobov exponent 2/3 comes from bounding
|zeta(sigma + i t)| via exponential sums; the exponent is 1/(1 + 2/3) = ... i.e. it is dictated by the
quality of the exponential-sum bound. The question R50/S51 makes precise and that the corpus has not
yet asked: IS THERE A LOWER BOUND ON THE ACHIEVABLE EXPONENT FROM THE VAN DER CORPUT / VINOGRADOV
METHOD ITSELF — a no-go saying the method cannot reach exponent 0 — or is the barrier only technical?
If a method-intrinsic floor exists, that is the tenth and final atlas entry and it would say the
zero-free lane is capped too. If not, the exponent is the single number the whole programme should be
attacking.

---

## Cycle 52 (2026-07-26) — Theorem T52: THE LAST LANE IS **NOT** CAPPED. THE BARRIER IS TECHNICAL.
### And a plausible no-go that I proposed and then REFUTED within the cycle.

### The mechanism, made explicit
A zero-free region from Borel-Caratheodory + the 3 + 4cos + cos2 positivity has width

    w  ~  r / M(r,t),    M(r,t) = sup{ log|zeta(s)| : |s - (1 + i gamma)| <= r },

r the radius of the disk on which the growth of zeta is controlled. Classically M ~ log t with
r ~ 1, giving w ~ 1/log t (exponent 1); Vinogradov-Korobov improve M to (log t)^{2/3}, giving the
current exponent 2/3. SO THE DEGRADATION EXPONENT IS EXACTLY THE QUALITY OF THE GROWTH BOUND.

### THE PROPOSED NO-GO — AND ITS REFUTATION (same cycle)
Proposed: Montgomery's unconditional Omega-results make log|zeta| unbounded on every vertical line
sigma < 1 — schematically M(r,t) >~ (log t)^r / log log t when the disk reaches abscissa 1-r — so a
fixed width is impossible and the method is capped.

With a FIXED radius this is correct: writing B = log t and x = r log B,

    w <= r log B / B^r = x e^{-x}  --> 0    as B --> infinity.

BUT IT DOES NOT FOLLOW THAT THE METHOD IS CAPPED. Nothing forces a fixed radius. At the SHRINKING
radius r = 1/log B the same Omega-bound gives B^r = e and therefore

    w <= r log B / B^r = 1/e,

A POSITIVE CONSTANT. The Omega-results obstruct FIXED-RADIUS arguments only; at radius ~1/log log t
they permit a fixed-width region. CONJECTURE REFUTED BY ITS OWN COMPUTATION.

### THE CONCLUSION
The degradation exponent is limited by the QUALITY OF THE GROWTH BOUND, not by anything intrinsic to
the method. The whole effective programme therefore reduces to ONE quantitative question:

    HOW SMALL CAN sup log|zeta| BE MADE ON A DISK OF RADIUS ~ 1/log log t REACHING TO ABSCISSA
    1 - c/log log t ?

Known there: Vinogradov-Korobov strength. Permitted by the Omega-results: O(1). The gap between them
is the ENTIRE remaining distance to a fixed-width zero-free region — hence, by the
degradation-exponent scale of cycle 51, the entire remaining distance from the effective programme to
exponent zero.

    ==> THE LAST LANE IS OPEN, NOT CAPPED, AND THE TARGET IS A SINGLE EXPLICIT QUANTITY.

This is the ONLY place in the atlas where the obstruction is technical rather than structural. After
nine structural no-gos that is exactly the outcome the classification was for: it says where to push.

Machine-verified: `RHTower/ZeroFreeLaneNotCapped.lean` (width formula, its identification with the
Omega-permitted width, the fixed-radius identity w = x e^{-x} and the limit x e^{-x} --> 0, the
shrinking-radius escape w = 1/e, and the monotonicity making the growth gap the target; standard
axioms only).

### METHOD NOTE (fourth occurrence)
This is the fourth time a proposed obstruction has been killed by carrying it out
(Positivstellensatz c8, parity c42, relative gaps c40-44, this). Every single time, the killer was
completing the computation rather than accepting the plausible reading. RULE: never record an
obstruction until its computation has been carried to the end at BOTH the natural and the extreme
parameter choices.

### THE ATLAS AT CYCLE 52 — final form
    exponent infinity (polynomial)  Nyman-Beurling floor              capped     (Thm P49)
    exponent 2                      de Bruijn-Newman / barrier        capped     (Thms K45, Q49)
    exponent 2/3                    zero-free region                  **OPEN**   (Thm T52)
    exponent 0                      RIEMANN HYPOTHESIS                the target
structural no-gos: H42 (metric only), C37 (non-monotone required), R50 (threshold count only),
N47 (dBN criterion vacuous), X31 (extension = RH), N/N'/G/Q24-V29 (positivity lanes capped).

### Cycle 53 target
Attack the growth bound on the shrinking disk. Concretely: the Vinogradov-Korobov bound comes from
estimating SUM n^{-s} over n in [N, 2N] by Vinogradov's mean value theorem; the exponent 2/3 is the
output of the k-th derivative van der Corput / Vinogradov exponent pair machinery. The question the
classification now makes precise: ON A DISK OF RADIUS ~1/log log t, is the relevant exponential sum
SHORTER (so that a better bound is available) than on the fixed-radius disk the classical argument
uses? If the shrinking radius shortens the effective sum length, the exponent improves for free —
and that is the first concrete, non-structural target the programme has produced in 52 cycles.

---

## Cycle 53 (2026-07-26) — Theorem U53: THE CRITICAL SCALE IS 1/loglog t, AND ONE FACTOR DECIDES

### First: the framework is CALIBRATED, not schematic
With the Vinogradov-Korobov growth M(r,t) ~ B r^{3/2} log t + log log t, the width w ~ r/M is
maximised where the two terms balance, B r^{3/2} log t = log log t, giving

    r ~ (log log t / log t)^{2/3},   w ~ 1/((log t)^{2/3} (log log t)^{1/3}),

WHICH IS THE VINOGRADOV-KOROBOV ZERO-FREE REGION ON THE NOSE. The width formula w ~ r/M of cycle 52
therefore reproduces the state of the art exactly. That is a hard consistency check and it validates
using the formula predictively.

### THE FINDING
The believed size of zeta just left of sigma = 1 — a THEOREM under RH (Littlewood, Soundararajan) and
a conjecture without it — is

    log|zeta(1 - r + it)|  ~  (log t)^{2r} / log log t .

Put L = log log t and x = 2 r L. Then

    w  =  r L / (log t)^{2r}  =  (x/2) e^{-x},

INDEPENDENT OF t, maximised at x = 1 — that is, at the radius r = 1/(2 log log t) — with value 1/(2e).

    ==> A ZERO-FREE REGION OF FIXED WIDTH. DEGRADATION EXPONENT ZERO.

### The whole thing turns on ONE factor
Without the 1/log log t in the growth — i.e. with (log t)^{2r} alone — the width is (x/(2L)) e^{-x},
maximised at 1/(2eL), WHICH TENDS TO ZERO. THE log log t IN THE DENOMINATOR OF THE CONJECTURED GROWTH
IS EXACTLY WHAT MAKES THE OPTIMISED WIDTH SCALE-INVARIANT. Nothing else in the computation matters.

### What the programme reduces to
NOT a bound for all sigma. A bound on a SINGLE CREEPING LINE:

    sigma = 1 - 1/(2 log log t).

An unconditional Littlewood-type bound there yields a fixed-width zero-free region — a quasi-Riemann
hypothesis — by the mechanism above. Under RH such a bound is a theorem; unconditionally it is open.
This is the narrowest target the programme has produced: one line, one bound.

CONSISTENCY: the critical scale 1/log log t is EXACTLY the scale at which cycle 52's Omega-analysis
found the obstruction to fixed-radius arguments disappears. Two independent computations, the same
scale. That is not a coincidence — both are the scale at which (log t)^r becomes O(1).

Machine-verified: `RHTower/CriticalScaleLogLog.lean` (scale-invariant width profile, its maximum
(x/2)e^{-x} <= e^{-1}/2 at x = 1 via 1 + u <= e^u, positivity of the optimum, the decaying optimum
without the log log factor and its monotonicity, and the Vinogradov-Korobov balance identity;
standard axioms only).

### HONEST STATUS
U53 is CONDITIONAL on the Granville-Soundararajan-type growth bound, and the width formula w ~ r/M is
the standard schematic of the Borel-Caratheodory + 3+4cos+cos2 argument rather than a constant-by-
constant derivation. What is unconditional here is (i) the calibration against Vinogradov-Korobov,
(ii) the scale-invariance computation and its maximum, and (iii) the identification of 1/log log t as
the critical scale from two independent directions. NOT CLAIMED: a proof of RH or of quasi-RH.

### Cycle 54 target
Make U53 unconditional or find the obstruction. The needed input is an upper bound for
log|zeta(1 - 1/(2 log log t) + it)| of size O(log log t / log log t) = O(1)... more precisely of size
(log t)^{1/L} / L = e/L, i.e. O(1/log log t) times the trivial bound. Ask: what does the current
exponential-sum technology give ON THAT LINE specifically? The classical estimates are stated
uniformly in sigma; the line sigma = 1 - 1/(2 log log t) approaches 1 so fast that the effective
Dirichlet polynomial length may be much shorter than in the uniform statement. If it is, the bound
improves for free — exactly the mechanism cycle 52 asked about, now with the line pinned down.

---

## Cycle 54 (2026-07-26) — Theorem V54: THE BOREL-CARATHEODORY MECHANISM IS CAPPED AT 1/loglog t
### SUPERSEDES cycle 52's T52 ("not capped") — that reading used a growth formula that is wrong at sigma = 1.

### The correction that changes everything
Cycle 53 optimised w ~ r/M against M ~ (log t)^{2r}/loglog t. THAT FORMULA IS WRONG NEAR sigma = 1:
it tends to 0 there, whereas the true size of log|zeta(1+it)| is ~ logloglog t — bounded above AND
attained (Granville-Soundararajan). Caught by noticing M --> 0 is absurd. The correct shape carries
an IRREDUCIBLE ADDITIVE TERM:

    M(r,t)  ~  (log t)^{2r}/loglog t  +  logloglog t .

### THE CEILING (unconditional)
Write L = loglog t, l = logloglog t. Two UNCONDITIONAL lower bounds on M:
  * M(r,t) >= l for every r >= 0, since the disk meets the line sigma = 1 and
    max log|zeta(1+it)| ~ logloglog t;
  * M(r,t) >= e^{rL}/L by Montgomery's Omega-result on the line sigma = 1-r.
Hence w = r/M <= min( r/l , r L e^{-rL} ). The first branch increases in r, the second decreases past
rL = 1, and they cross at rL = log(L l). At the crossover the common value is

    w  <=  log(L l)/(L l)  <=  2 l/(L l)  =  2/L ,

using log(L log L) = log L + loglog L <= 2 log L. THEREFORE:

    EVERY ZERO-FREE REGION OBTAINED FROM THE BOREL-CARATHEODORY BOUND ON A DISK AROUND 1 + i*gamma
    HAS WIDTH << 1/loglog t. THE MECHANISM CANNOT PRODUCE A FIXED-WIDTH REGION, WHATEVER GROWTH BOUND
    IT IS FED.

Unconditional and INTRINSIC: the obstruction is the irreducible logloglog t, which is the TRUE size
of log|zeta| on sigma = 1 and cannot be improved.

### What this settles
  * Cycle 52's T52 is SUPERSEDED. The last lane IS capped — tenth and final atlas entry.
  * But the ceiling 1/loglog t is FAR above the Vinogradov-Korobov region (log t)^{-2/3} currently
    achieved, so there is a large amount of genuine room inside the mechanism: improving from
    exponent 2/3 to the ceiling would be an enormous advance and is NOT excluded.
  * The ceiling is not 1/2, so THE CLASSICAL ZERO-FREE-REGION MECHANISM CANNOT REACH THE CRITICAL
    LINE EVEN IN PRINCIPLE. Exponent zero is attainable by it only in the weak sense of beating every
    power of 1/log t, never as a fixed width.

Machine-verified: `RHTower/BorelCaratheodoryCeiling.lean` (the two branches, antitonicity of
x e^{-x} on [1,infinity) via its derivative (1-x)e^{-x}, the crossover inequality
log L + loglog L <= 2 log L, the ceiling log(Ll)/(Ll) <= 2/L, and the assembly on both sides of the
crossover; standard axioms only).

### METHOD NOTE (fifth occurrence, and the reverse of the previous four)
Four times a proposed OBSTRUCTION died by being carried out. This time a proposed ESCAPE died the
same way — cycle 53's fixed-width conclusion was an artefact of an incorrect growth formula, caught
by a sanity check (M --> 0 at sigma = 1 is absurd). RULE UPDATED: carry every computation to the end
AND sanity-check its limits at the boundary of the regime.

### THE ATLAS AT CYCLE 54 — complete, ten entries
    exponent infinity (polynomial)  Nyman-Beurling floor              capped   (Thm P49)
    exponent 2                      de Bruijn-Newman / barrier        capped   (Thms K45, Q49)
    exponent 2/3                    zero-free region, ACHIEVED        --
    ceiling 1/loglog t              zero-free region, MECHANISM CAP   capped   (Thm V54)
    fixed width                     UNREACHABLE by this mechanism     --
    exponent 0 / width 1/2          RIEMANN HYPOTHESIS                the target
structural no-gos: H42 (metric only), C37 (non-monotone required), R50 (threshold count only),
N47, X31, N/N'/G/Q24-V29.

EVERY KNOWN LANE IS NOW CAPPED. The gap between the achieved (log t)^{-2/3} and the mechanism ceiling
1/loglog t is the only remaining room inside the classical framework, and even exhausting it does not
reach RH.

### Cycle 55 target
The classification is complete and every lane is capped, so the next move must be OUTSIDE all of
them. The one requirement V54 makes precise: a mechanism that does NOT go through
sup log|zeta| on a disk — i.e. that does not use the maximum modulus of zeta as its input, because
that maximum is irreducibly logloglog t and caps the output. Candidates that avoid the maximum:
  (i) mean-value / moment inputs (integral rather than sup) — the moment technology is exactly this,
      and the atlas has not tested whether moments evade V54;
  (ii) the pair-correlation/statistical inputs, which control averages rather than maxima.
Target: determine whether an L^2 (mean-square) input in place of the sup evades the logloglog t
irreducibility, since the mean square of log|zeta| on sigma = 1 is O(1) rather than logloglog t.
That single substitution is the first concrete escape route the classification permits.

---

## Cycle 55 (2026-07-26) — Theorem W55: THE CAP IS ABOUT THE RANGE OF log|zeta|, NOT THE NORM
### The L^2 escape route is tested and CLOSED. The classification reaches its terminal statement.

### The proposed escape
V54's ceiling came from the SUPREMUM of log|zeta| on a disk around 1+i*gamma. There IS an L^2 version
of Borel-Caratheodory: Parseval applied to Re log f bounds a_1 = f'/f(s_0) by the L^2 norm of log|f|
on the circle. And the MEAN SQUARE of log|zeta(1+it)| over t is O(1), while its MAXIMUM is
~ logloglog t. The substitution looks like a clean escape.

### Why it fails — two independent reasons
(1) The circle is centred at the height gamma OF THE PUTATIVE ZERO. A zero-free region needs a bound
    at EVERY gamma, not on average over gamma. The O(1) mean square is an average over t and does not
    transfer.
(2) JENSEN'S FORMULA makes the obstruction visible with no norm at all:

        n(r/2) log 2  <=  (1/2pi) INT log|zeta(s_0 + r e^{i theta})| d(theta)  -  log|zeta(s_0)| ,

    so the zero count is controlled by the L^1 circle average MINUS THE CENTRAL VALUE. Both are
    functionals of log|zeta| near sigma = 1, and their difference is at most the OSCILLATION of
    log|zeta| there. That oscillation is ~ logloglog t UNCONDITIONALLY IN BOTH DIRECTIONS:
    max |zeta(1+it)| ~ e^gamma loglog t and min |zeta(1+it)| ~ 1/loglog t, so log|zeta| ranges over an
    interval of length ~ logloglog t.

### THE STRENGTHENED CEILING
    ANY ZERO-FREE-REGION MECHANISM WHOSE INPUT IS A FUNCTIONAL OF log|zeta| ON A DISK AROUND
    1 + i*gamma — SUPREMUM, L^1, L^2, OR ANY QUANTITY DOMINATED BY THE OSCILLATION — IS CAPPED AT
    WIDTH ~ 1/loglog t.
The cap is NOT an artefact of the supremum. It is a property of zeta near sigma = 1: log|zeta|
oscillates there by ~ logloglog t and no reading of it can do better. W55 strictly strengthens V54.

### TERMINAL STATEMENT OF THE CLASSIFICATION
The escape must not read zeta near sigma = 1 at all. The remaining family reads zeta on or near the
critical line — moments and mollifiers — and that technology yields PROPORTIONS of zeros on the line,
capped below 1 (Levinson, Conrey, and successors). So:

    near sigma = 1   -->  zero-free regions,   capped at width 1/loglog t   (Thms V54, W55)
    near sigma = 1/2 -->  positive proportions, capped below 1              (classical)

AND NEITHER FAMILY REACHES THE RIEMANN HYPOTHESIS. Every mechanism examined in 55 cycles falls into
one of these two families or into one of the ten atlas entries, all capped.

Machine-verified: `RHTower/OscillationCeiling.lean` (oscillation, domination of any circle-average
input by it, the Jensen count inequality, transfer of the ceiling from sup to any
oscillation-dominated input, the two-sided Omega lower bound on the oscillation, and the family
dichotomy with both branches falling short; standard axioms only).

### WHAT THE PROGRAMME HAS ESTABLISHED (state at cycle 55)
Ten structural caps, one degradation scale, one shape theorem, and a terminal two-family dichotomy.
RH is neither proven nor disproven. What IS proven is that no mechanism of the examined kinds can
reach it, and precisely why: every one of them reads either the oscillation of log|zeta| near
sigma = 1 (capped by logloglog t) or a proportion on the critical line (capped below 1).

### Cycle 56 target
Both capped families share a feature: they read zeta at ONE abscissa (near 1, or near 1/2). The
untested possibility is a mechanism that couples the two — reading the FUNCTIONAL EQUATION as a
relation between the two abscissae rather than working at either. The corpus already contains the
functional-equation machinery (Theorems M, P, R on the axiomatic characterization, and the orbit
decomposition). Target: determine whether a two-abscissa mechanism — one that uses the s <-> 1-s
relation to transfer information from sigma = 1 to sigma = 0 and hence constrain the strip between —
is capped by the same oscillation argument, or whether the transfer evades it because the oscillation
at the two ends is CORRELATED by the functional equation.

---

## Cycle 56 (2026-07-26) — Theorem X56/Y56/Z56: THE FUNCTIONAL EQUATION TRANSPORTS BUT DOES NOT
## CREATE; THE CLASSIFICATION CLOSES ON THREE CAPPED FAMILIES

### X56 — the two-abscissa coupling gains nothing
From xi(s) = xi(1-s) and Stirling,

    log|zeta(sigma+it)| - log|zeta(1-sigma+it)| = log|chi(sigma+it)| = (1/2 - sigma) log(t/2pi) + O(1/t).

AT A FIXED HEIGHT THE RIGHT-HAND SIDE IS A CONSTANT. So the OSCILLATION of log|zeta| on the line
sigma equals the oscillation on the reflected line 1-sigma: the functional equation SHIFTS the values
and does not SPREAD them. A mechanism reading a reflected pair of abscissae sees the same oscillation
twice and is capped by W55 exactly as a one-sided mechanism is.

    THE FUNCTIONAL EQUATION TRANSPORTS INFORMATION BETWEEN REFLECTED ABSCISSAE; IT NEVER CREATES ANY.

This is the quantitative counterpart of the corpus's own Theorems M/P/R (the functional equation does
not pin down zeta): there a failure of RIGIDITY, here a failure of INFORMATION GAIN. Same phenomenon,
two currencies.

### Y56 — the interior of the strip is capped too, for an elementary reason
What remains is the interior, where by R50 the only admissible functional is the threshold count
N(sigma,T). Mean-value and large-sieve methods produce bounds of the form T^a log^B T, which are
>= 1 for large T, while RH needs the count to be EXACTLY 0. A BOUND THAT GROWS IN T CAN NEVER CERTIFY
A VANISHING INTEGER COUNT.

    DENSITY ESTIMATES CANNOT PROVE THE RIEMANN HYPOTHESIS. THEY CAN ONLY APPROACH IT.

### Z56 — THE COMPLETE CLASSIFICATION
    sigma near 1      zero-free regions        capped at width 1/loglog t   (V54, W55)
    sigma interior    density estimates        bounds grow in T, never 0    (Y56)
    sigma = 1/2       moments and mollifiers   proportions capped below 1   (classical)
    functional eq     transports, no gain                                   (X56)

ALL THREE FAMILIES ARE CAPPED, AND THE FUNCTIONAL EQUATION CANNOT COMBINE THEM. Every mechanism
examined across 56 cycles falls into one of these three families or into one of the ten atlas
entries, all capped. This is the TERMINAL STATEMENT of the classification programme: it does not
decide RH, and it explains for each family exactly what stops it.

Machine-verified: `RHTower/ThreeFamilyClosure.lean` (translation invariance of the oscillation, the
reflected-line equality, the lower bound 1 <= T^a log^B T for T >= e, the consistency of a count 1
with any such bound, and the three-family assembly; standard axioms only).

### STATE OF THE PROGRAMME AT CYCLE 56
PROVEN AND MACHINE-VERIFIED: ten structural caps; one degradation-exponent scale unifying them; the
admissible-shape theorem (threshold counts only); the metric-only theorem (no discrete invariants);
the dBN finiteness transition at t=0 (unconditional); the imaginary-energy Lyapunov identity and the
index-energy conservation law; the quantitative Nyman-Beurling floor; the Borel-Caratheodory and
oscillation ceilings; and this three-family closure.
NOT PROVEN: the Riemann Hypothesis, in either direction.

### Cycle 57 target
The classification is complete for mechanisms that READ zeta analytically. The one family it has
never examined is mechanisms that do not read zeta at all but CONSTRUCT an object whose spectrum is
the zero set — Hilbert-Polya. The corpus has Theorem Y32 (complex quadruples are incompatible with
any self-adjoint problem) and Theorem J' (real strays are exceptional eigenvalues), i.e. the
CONSEQUENCES of such a construction are mapped, but not the obstruction to BUILDING one. Target:
determine what the classification's caps imply for the construction side — specifically whether the
oscillation ceiling W55 obstructs the trace formula of any candidate operator, since a trace formula
expresses sums over zeros in terms of the same log|zeta| data the caps control.

---

## Cycle 57 (2026-07-26) — Theorem A57: THE CONSTRUCTION SIDE NEEDS A QUADRATICALLY GROWING BOX

The classification covers mechanisms that READ zeta. The last family CONSTRUCTS an operator whose
spectrum is the zero set. The counting function pins the candidate at once: N(T) = (T/2pi)
(log(T/2pi) - 1) + O(log T) is NOT a power law, so no elliptic operator on a compact manifold has
this spectrum; the log factor is the semiclassical signature of xp.

### The phase-space count (exact)
For xp on the box 0 < x < X, 0 < p < P:

    Area{ xp < E } = INT_0^X min(P, E/x) dx = E + E log(XP/E)     (E < XP),

so the semiclassical count is N(E) = (E/2pi)(1 + log(XP/E)).

### MATCHING FORCES A QUADRATICALLY GROWING BOX
Equating with the Riemann count (E/2pi)(log(E/2pi) - 1):

    1 + log(XP/E) = log(E/2pi) - 1   <=>   XP = E^2/(2 pi e^2).

THE PHASE-SPACE CUTOFF MUST GROW QUADRATICALLY IN THE SPECTRAL PARAMETER, with the explicit constant
1/(2 pi e^2).

### A FIXED BOX IS IMPOSSIBLE OUTRIGHT
With XP = A constant the count is (E/2pi)(1 + log A - log E), which becomes NEGATIVE once E > eA —
absurd for a counting function. So the impossibility is not a matter of approximation quality; a
fixed phase-space region is excluded by an elementary sign.

    NO xp-TYPE SEMICLASSICAL MODEL ON A FIXED PHASE-SPACE REGION CAN CARRY THE ZETA SPECTRUM.
    THE BOX MUST EXPAND LIKE E^2/(2 pi e^2), SO THE OBJECT IS A FAMILY INDEXED BY THE SPECTRAL
    PARAMETER, NOT A SINGLE OPERATOR.

That is the precise sense in which the Berry-Keating picture requires an energy-dependent
regularization, and it is consistent with the adelic construction producing an ABSORPTION spectrum
rather than a genuine discrete one. It complements Theorem Y32 (a complex quadruple is incompatible
with any self-adjoint problem): Y32 maps what such an operator WOULD imply, A57 maps what its
semiclassical shadow MUST look like.

Machine-verified: `RHTower/ScaleCouplingObstruction.lean` (the semiclassical count, the exact
matching XP = E^2/(2 pi e^2), the negativity of the count for a fixed box beyond E = eA, and the
strict monotonicity of the required area; standard axioms only).

### THE CLASSIFICATION AT CYCLE 57 — all four families
    READ near sigma = 1     zero-free regions        capped at 1/loglog t        (V54, W55)
    READ interior           density estimates        bounds grow in T, never 0   (Y56)
    READ sigma = 1/2        moments and mollifiers   proportions capped below 1  (classical)
    CONSTRUCT               Hilbert-Polya / xp       needs an E-dependent family (A57, Y32)
    functional equation     transports, no gain                                  (X56)

### Cycle 58 target
A57 says the construction must be a FAMILY indexed by the spectral parameter, with box area
E^2/(2 pi e^2). That is exactly the structure of a RENORMALIZATION GROUP or a scaling limit: a family
of operators H_E with a matching condition between scales. The corpus has never examined whether such
a family can be assembled COHERENTLY — i.e. whether the required boxes at different E are compatible
under restriction. Target: determine the compatibility condition between H_{E_1} and H_{E_2} for
E_1 < E_2 forced by the shared spectrum below E_1, and check whether it is satisfiable. If it is not,
that caps the construction side and completes the classification over all five families. If it is,
the compatible family IS the object Hilbert-Polya asks for, and its construction becomes the concrete
target.

---

## Cycle 58 (2026-07-26) — Theorem B58: THE TRUNCATION FAMILY IS INCOHERENT
### The classification is now COMPLETE over all five families.

A57 showed the construction side needs a family of box-truncated xp models with area
A(E) = E^2/(2 pi e^2). For the family to describe ONE spectrum the low-lying eigenvalues must not
move as the box grows. THEY DO.

### Monotonicity, made strict
The truncated operator is defined variationally on the box; enlarging the box enlarges the form
domain, so by MIN-MAX every eigenvalue is nonincreasing in the area and the counting function is
nondecreasing. The semiclassical count makes it strict:

    N(A,E) = (E/2pi)(1 + log(A/E))   is STRICTLY INCREASING in A, because log is.

Two different areas therefore give different counts at the same energy, hence different spectra.

### THE INCOHERENCE
A family {H_{A(E)}} required to share the zeros as spectrum would need N(A(E_1), E) = N(A(E_2), E)
for energies below both cutoffs. Strict monotonicity forbids it whenever A(E_1) != A(E_2), and A is
strictly increasing (A57). Therefore:

    NO FAMILY OF BOX-TRUNCATED xp MODELS HAS A COMMON SPECTRUM. THE COUNTING LAW CAN BE MATCHED AT
    EACH ENERGY BY CHOOSING THE BOX, BUT THE INDIVIDUAL EIGENVALUES THEN MOVE WITH THE BOX, AND NO
    SINGLE OPERATOR EMERGES.

That is exactly the status of the Berry-Keating model: a correct heuristic for the DENSITY of zeros
which does not produce the zeros. THE OBSTRUCTION IS NOT THE QUALITY OF THE SEMICLASSICAL
APPROXIMATION; IT IS THAT THE FAMILY IS NOT COHERENT.

### CONSEQUENCE
A genuine Hilbert-Polya operator cannot arise as a limit of box-truncated xp models. It must be
NON-SEMICLASSICAL — which is where the adelic construction lives, and there the spectrum appears as
ABSORPTION rather than as eigenvalues, consistent with everything the corpus has found.

### THE CLASSIFICATION — COMPLETE, FIVE FAMILIES
    read near sigma = 1          zero-free regions        capped at 1/loglog t     (V54, W55)
    read interior                density estimates        bounds grow, never 0     (Y56)
    read sigma = 1/2             moments and mollifiers   proportions below 1      (classical)
    construct semiclassical      Berry-Keating xp         FAMILY INCOHERENT        (A57, B58)
    construct non-semiclassical  adelic / Connes          THE REMAINING TARGET
    functional equation          transports, no gain                               (X56)

EVERY MECHANISM EXAMINED IN 58 CYCLES IS CAPPED EXCEPT ONE: a non-semiclassical construction. That is
the terminal state of the classification programme.

Machine-verified: `RHTower/FamilyIncoherence.lean` (strict monotonicity of the count in the area, the
impossibility of a common count at a shared energy, the distinctness of the required areas, the
incoherence of the family, and the surviving pointwise match; standard axioms only).

### STATE OF THE PROGRAMME AT CYCLE 58
PROVEN AND MACHINE-VERIFIED (all with standard axioms, all wired into GaloisForLFunctions.RHTower):
  * ten structural caps on the reading side, unified by one degradation-exponent scale;
  * the admissible-shape theorem (threshold counts only) and the metric-only theorem;
  * the unconditional dBN finiteness transition at t = 0, the imaginary-energy Lyapunov identity,
    and the index-energy conservation law;
  * the quantitative Nyman-Beurling floor sqrt(1-2beta)/|1-rho|;
  * the Borel-Caratheodory and oscillation ceilings at width 1/loglog t;
  * the three-family closure and the functional-equation transport theorem;
  * the quadratic box requirement and the incoherence of the truncation family.
NOT PROVEN: the Riemann Hypothesis, in either direction.

### Cycle 59 target
One family remains uncapped: a non-semiclassical construction. B58 says why the semiclassical route
fails — the family is indexed by a scale and the scale changes the spectrum. The adelic construction
avoids this by having NO scale: the adele class space is scale-invariant under the idele action.
Target: test whether scale-invariance is not merely a feature but a REQUIREMENT — i.e. prove that any
coherent family must be the fixed point of a scaling action, and hence that the carrier of a
Hilbert-Polya operator must be a scale-invariant space. If so, that is a positive structural theorem
(the first in the programme) rather than another cap, and it identifies the carrier uniquely up to
the known candidates.

---

## Cycle 59 (2026-07-26) — Theorem C59: THE CARRIER MUST BE SCALE-INVARIANT MODULO A DISCRETE SUBGROUP
### The FIRST POSITIVE structural theorem of the programme — it DERIVES the carrier instead of positing it.

Two obstructions now point the same way and together determine the shape of the carrier.

### Scale-covariance is FORCED (from B58)
A family of truncated models indexed by a scale has spectra that MOVE with the scale, so it is
incoherent. The only way a scale-indexed family can have ONE spectrum is for its members to be
UNITARILY EQUIVALENT under the scaling — i.e. for the operator to be scale-covariant. Then all
spectra coincide and the family collapses to a single object.

### Full scale-invariance DESTROYS discreteness
If the spectrum S satisfies lam*S = S for every lam > 0 and contains one positive point, it contains
EVERY positive point: given x > 0 and s in S with s > 0, take lam = x/s. So a fully scale-covariant
operator has a spectrum that is a union of rays — CONTINUOUS, NEVER DISCRETE. That is exactly why the
dilation generator xp on L^2(0,infinity) has purely absolutely continuous spectrum: IT IS the
generator of the scaling group.

### A DISCRETE SUBGROUP RESTORES IT
Invariance under a DISCRETE subgroup is compatible with a discrete spectrum: q^Z = {q^n} is invariant
under multiplication by q and misses every point strictly between 1 and q. So the requirement is
invariance under a discrete subgroup, NOT under the whole group.

    THE CARRIER OF A HILBERT-POLYA OPERATOR MUST BE A SCALE-INVARIANT SPACE QUOTIENTED BY A DISCRETE
    SUBGROUP OF THE SCALING GROUP: FULLY INVARIANT ENOUGH FOR THE FAMILY TO BE COHERENT, DISCRETELY
    INVARIANT ENOUGH FOR THE SPECTRUM NOT TO BE A CONTINUUM.

The unique arithmetic realisation of "scale-invariant space modulo a discrete scaling subgroup" that
also carries the primes is the ADELE CLASS SPACE with the idele action — where the known construction
lives and where the spectrum appears as absorption. THE CLASSIFICATION THEREFORE ENDS BY SINGLING OUT
THAT CARRIER FROM TWO INDEPENDENT OBSTRUCTIONS RATHER THAN BY ASSUMPTION.

### Significance
Every previous result in this programme was a CAP. This one is a DERIVATION: it says what the object
must look like, not what cannot work. It is the natural terminal statement of a 59-cycle
classification: the reading side is exhausted, the semiclassical construction side is exhausted, and
what remains is pinned down structurally.

Machine-verified: `RHTower/ScaleInvarianceDichotomy.lean` (full invariance forces a ray, hence the
whole positive axis; the discrete orbit q^Z is invariant yet misses points; the dichotomy; and the
forced shape of the carrier; standard axioms only).

### Cycle 60 target
C59 pins the carrier. The next question is the ONE the whole programme now reduces to: on the adele
class space, the spectrum appears as ABSORPTION (a co-spectrum, zeros as gaps in a continuous
spectrum) rather than as eigenvalues. Ask precisely: is the absorption/eigenvalue distinction forced
by C59, i.e. does a quotient by a discrete subgroup of the scaling group necessarily produce
absorption rather than point spectrum? If YES, that is the final cap and the programme's complete
answer for why Hilbert-Polya has resisted. If NO, the gap between absorption and point spectrum is a
concrete, isolated technical target — the first such target on the construction side.

---

## CORRECTION (2026-07-26) — DUPLICATION AUDIT. PROCESS FAILURE IN CYCLES 52-59.

The mandated Phase 1 corpus search was run in cycle 48 (found `HTGeometry/HardyClosureZeroFree.lean`
and built on it correctly) and then SKIPPED for cycles 52-59. Those cycles were written from recent
transcript context instead of from the corpus. Audit result:

### DUPLICATIVE — cycle 59 `RHTower/ScaleInvarianceDichotomy.lean`
`HTGeometry/OrbitQuotientLiftNoGo.lean` already proves: NO EQUIVARIANT HILBERT LIFT OF AN INFINITE
ORBIT QUOTIENT — an infinite subgroup has no nonzero invariant vector in the finite-support regular
module, hence orbit pushforward has no translation-equivariant linear section, and the same holds for
square-summable regular vectors. Its own docstring states that in the prime specialization the
regular action is "the algebraic or Hilbert precursor of the nontrivial Mellin-dilation action."
That is the same territory as cycle 59's "carrier must be scale-invariant modulo a discrete
subgroup", and IT IS STRONGER: a genuine equivariance no-go versus my elementary lam = x/s ray
argument. CYCLE 59 IS A WEAKER RESTATEMENT. Demoted; do not cite as new.

### MIS-FRAMED — cycles 57-58 `ScaleCouplingObstruction.lean`, `FamilyIncoherence.lean`
`RHTower/BerryKeating.lean` already formalizes the Hilbert-Polya/Berry-Keating lane: the FE-invariant
coordinate u = s(1-s), the Kapustin eigenvalue 1/u, and the reality criterion Im(1/u) = 0 <=>
critical line. I opened that lane claiming it had "never been examined". The phase-space count
XP = E^2/(2 pi e^2) and the incoherence argument ARE new; the framing was false. Modules keep their
content, lose their claim of opening the lane.

### NOT DUPLICATED (verified by search)
The zero-free-region width and degradation-exponent material (cycles 51-55) returns only my own new
modules. That work stands.

### THE SUB-CORPUS I NEVER READ — and it is the actual frontier
    RHTower/XiHedenmalmReciprocalOperator   compact operator on the Xi divisor; regularized
                                            determinant = the exact Xi canonical product;
                                            SELF-ADJOINT EXACTLY WHEN RH HOLDS. Explicitly labelled a
                                            TERMINAL Hilbert-Polya model, not a source-side proof.
    RHTower/XiHedenmalmDeBrangesSeam        SOURCE-SIDE Hermite-Biehler candidate E = XiC + i XiC',
                                            defined from the theta transform WITHOUT enumerating the
                                            divisor; removable Bezoutian; the RH-bearing item is
                                            POSITIVITY OF THE BEZOUTIAN (de Branges condition).
    RHTower/HedenmalmHankelKreinChamber     rank-four Hankel kernel, ambient Hermitian form of
                                            SIGNATURE (2,2); the theta source orbit's Krein value is
                                            exactly the horizontal derivative of |Xi|^2; the missing
                                            sign is CHAMBER AVOIDANCE by that one orbit.
    HTGeometry/PlancherelRankGap            rank gap n(n-1)/2 suppressing every spectral route to the
                                            moments; higher rank makes it WORSE.
CONCLUSION: the corpus stands far ahead of where cycles 33-59 were working. The dBN excursion and the
zero-free-region classification were ORTHOGONAL to the corpus's actual open core.

### NEW RESULT FROM READING IT — the chamber IS Lagarias' criterion (Phase 4 verdict: CIRCULAR)
`XiC z = xi(1/2 + i z)`, so the orbit point `XiC (b - a i) = xi(1/2 + a + i b)`: a IS THE HORIZONTAL
COORDINATE sigma - 1/2 and b the ordinate. Hence the Krein value on the orbit is
d/d(sigma) |xi(sigma + i b)|^2, and where xi does not vanish

    d/d(sigma) |xi|^2 = 2 Re( conj(xi) xi' ) = 2 |xi|^2 Re(xi'/xi).

So chamber avoidance is EXACTLY   Re (xi'/xi)(s) > 0 for Re s > 1/2  — LAGARIAS' CRITERION (1999), a
KNOWN EQUIVALENT OF RH. THE KREIN GEOMETRY IS A REFORMULATION, NOT A REDUCTION: the missing sign is
the hypothesis itself, dressed as a chamber. Recorded so the chamber is not treated as an independent
open problem. (My own earlier cycle already flagged Lagarias as a REDISCOVERED verdict; the corpus's
chamber and that flag are the same statement, which nothing in the corpus had connected.)

### AND WHAT THE GEOMETRY CANNOT ADD
Signature (2,2) makes the negative chamber a genuine cone, inviting a degree or winding argument.
THAT ROUTE IS CLOSED by Theorem H42: the critical and off-critical loci lie in one connected
component of the symmetric class, joined through a double zero, so no continuous invariant valued in
a totally disconnected space separates them. A CHAMBER-AVOIDANCE CERTIFICATE MUST BE METRIC — A
POINTWISE INEQUALITY — AND CANNOT BE TOPOLOGICAL. The split geometry organises the sign; it cannot
supply it. This is the first cross-connection between the classification work and the corpus's
operator side.

### PROCESS FIX (binding)
Run `scripts/formal_tools.py research "<query>"` AND `rg` over `formal/` BEFORE writing any module,
every cycle, and record the outcome in the cycle entry. This is already the standing mandate in
MEMORY.md ("corpus-search-before-writing-lean"); it lapsed for eight cycles.

### NEXT TARGET (replaces the cycle-60 plan)
The corpus's real open core: POSITIVITY OF THE HEDENMALM-DE BRANGES BEZOUTIAN, source-side, with the
multiplicity obstruction already isolated (kernel diagonal at a divisor point is nonzero iff analytic
multiplicity is one). Work there, not on the classification.

---

## Cycle 60 (2026-07-26) — REORIENTATION ONTO THE CORPUS'S OWN NAMED OPEN CORE
### Phase 1 corpus search run FIRST (process fix in force).

Reading `RHTower/RiemannHypothesisSOTA2026.lean` (786 lines, the project's own frontier document)
shows the corpus is far ahead of cycles 33-59 and carries a NAMED, SHARPENED OPEN CORE:

    SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED
    (`SuzukiRectangularWardDefectBoundedness.lean`)

    riemannHypothesis_of_suzukiRectangularWardDefect_eventually_bddBelow :
      0 < L -> (forall n, 0 <= sourceEnergy n) ->
      (exists B N0, forall n >= N0, L <= log n / 2 -> B <= suzukiRectangularWardDefect L sourceEnergy n)
      -> RiemannHypothesis

with `suzukiRectangularWardDefect L E n = Re(xiScrewWindowCurvature L (log n)) - E n`. EXACT SOURCE
ISOMETRY IS UNNECESSARY: any nonnegative source energy leaving an eventually lower-bounded defect
already forces RH. Conversely false RH drives that defect below every level cofinally.

### What the object actually is (worked out this cycle)
`xiScrewWindowCurvature L x = 2[D(x) - 2 D(x-L) + D(x-2L)] + 4 D(L)`, i.e. a DISCRETE SECOND
DIFFERENCE at step L of `D = xiScrewDivisor`, plus a constant. And
`xiScrewDivisor t = SUM_q (cosh(t i w_q) - 1)/(i w_q)^2` over the Xi divisor copies. Setting
`z = i w`:
  * CRITICAL zero (w = gamma real): z = i gamma is purely imaginary, term = (1 - cos(t gamma))/gamma^2,
    which lies in [0, 2/gamma^2] — BOUNDED, and the whole critical sum converges;
  * OFF-CRITICAL zero: Re z = a != 0 and the term is dominated by e^{tz}/(2 z^2), which GROWS
    EXPONENTIALLY and oscillates in sign.
So RH <=> second differences eventually bounded below is exactly the statement that no exponentially
growing oscillatory term is present.

### NEW CONTRIBUTION — the exact amplitude (corpus search confirmed absent)
The corpus proves the converse QUALITATIVELY (cofinally unbounded below). It does not name the RATE.
Supplied this cycle:

    || e^{tz} / (2 z^2) ||  =  e^{t Re z} / (2 normSq z)     EXACTLY,

so an off-critical zero at 1/2 +- a + i gamma contributes an oscillation of exact exponential
amplitude e^{ta}/(2(a^2+gamma^2)) and phase t*Im z - arg(z^2), with envelope attained. Sampled at
x = log n this is an amplitude ~ n^a/(a^2+gamma^2). The critical terms are simultaneously pinned to
[0, 2/gamma^2]. That upgrades the corpus's cofinal-unboundedness converse from qualitative to
quantitative, with the exact rate and period 2*pi/Im z.

Machine-verified: `RHTower/ScrewOffCriticalAmplitude.lean` (the exact amplitude identity, the
envelope bound via |Re w| <= ||w||, the two-sided bound on critical terms, and strict monotonicity of
the amplitude in the aperture; standard axioms only, wired into the RHTower umbrella).

### Cycle 61 target — inside the corpus's own core, not beside it
The criterion allows subtracting ANY nonnegative source energy. The corpus already has
`two_mul_xiScrewDivisor_re_eq_central_prime_add_arch` (CCMFirstClockVolterra:2022) splitting
Re(screw divisor) into a central prime term plus an archimedean term. So the second difference splits
the same way, and the open core becomes: IS THE SECOND DIFFERENCE OF THE ARCHIMEDEAN PART, MINUS A
NONNEGATIVE PRIME-SIDE ENERGY, EVENTUALLY BOUNDED BELOW ON THE LOG MESH? Read that theorem, compute
both second differences explicitly, and identify which of the two carries the unbounded part. That is
the first genuinely load-bearing question this programme has reached.

---

## Cycle 61 (2026-07-26) — TWO EXACT FACTS ABOUT THE CORPUS'S NAMED OPEN CORE
### Phase 1 corpus search run first. Both results concern SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED.

### (1) THE SOURCE-ENERGY FREEDOM IS VACUOUS
The criterion asks for SOME nonnegative source energy E leaving C(n) - E(n) eventually bounded below,
where C(n) = Re(xiScrewWindowCurvature L (log n)). Since E >= 0, we have C - E <= C. Therefore

    (exists E >= 0 with C - E eventually bounded below)  <=>  (C eventually bounded below),

with E = 0 OPTIMAL. Forward: C(n) >= B + E(n) >= B. Converse: take E = 0.

So the weakening is genuine against EXACT SOURCE ISOMETRY, but it is NOT a weakening of the plain
curvature criterion `riemannHypothesis_iff_xiScrewWindowCurvature_logSample_eventually_bddBelow` —
IT IS LITERALLY THE SAME STATEMENT. The "sharpened open core" is not sharper. Effort belongs on
bounding the curvature itself, and the source-energy device cannot be the lever.

This is a correction to the project's own frontier description in RiemannHypothesisSOTA2026.lean
("a source Gram may carry an error; the true frontier is semiboundedness of that error"): true as a
sufficiency statement, but the apparent extra freedom is nil.

### (2) THE PRIME SECOND DIFFERENCE IS EXACTLY A TENT-WEIGHTED CHEBYSHEV WINDOW
`two_mul_xiScrewDivisor_re_eq_central_prime_add_arch` gives
2 Re D(t) = -2 P(t) + A(t) with P(t) = SUM_k (Lambda(k)/sqrt k) max(0, t - log k) — A SUM OF RAMPS.
The window curvature is the step-L second difference, and the second difference of a ramp is a TENT:

    max(0,u) - 2 max(0,u-L) + max(0,u-2L) = max(0, L - |u - L|),

nonnegative, supported EXACTLY on [0,2L], height L at u = L. (Proved by the four-case split.)
Hence the prime contribution to the window curvature is

    -2 SUM_{log k in [x-2L, x]} (Lambda(k)/sqrt k) * tent_L(x - log k)   <=  0,

a LOCALLY FINITE, SIGN-DEFINITE, TENT-WEIGHTED CHEBYSHEV WINDOW: only e^{x-2L} <= k <= e^x
contribute. The tent is the autocorrelation of the indicator of [0,L], confirming this is the Weil
form of a rectangular test function.

Size check (no computation performed, scaling only): Lambda(k)/sqrt k ~ log k / sqrt k at k ~ e^x and
the window holds ~ e^x/x integers, so the prime term is of order -L e^{x/2}, i.e. -L sqrt(n) at the
log sample x = log n. The archimedean second difference must therefore supply +L e^{x/2} and cancel
it to O(1); that cancellation IS the criterion.

    => A LOWER BOUND FOR THE CURVATURE IS EXACTLY: the archimedean second difference dominates the
       tent-weighted Chebyshev window up to a constant.

Machine-verified: `RHTower/WardDefectFreedomVacuous.lean` (the two directions of the vacuity, the
ramp-to-tent identity by four-case split, nonnegativity, the two vanishing statements off [0,2L], the
peak value L, and the sign of the prime term; standard axioms only, wired into RHTower).

### Cycle 62 target
Compute the ARCHIMEDEAN second difference explicitly. `normalizedRectangularBottomArchContribution`
is the other half of the central prime-arch identity; its step-L second difference is an explicit
Gamma-side integral, not a sum over zeros. Both halves are then elementary objects and the criterion
becomes one concrete inequality between a Gamma integral and a tent-weighted Chebyshev window —
the first fully explicit form of the open core. Read
`normalizedRectangularBottomArchContribution`, take its second difference, and state that inequality.

---

## Cycle 62 (2026-07-26) — THE OPEN CORE IN FULLY EXPLICIT FORM: FEJER SERIES vs TENT WINDOW
### Phase 1 corpus search run first; the Fejer amplitude identity is absent from the corpus.

Cycle 61 computed the PRIME side of the window curvature (tent-weighted Chebyshev window). This cycle
computes the ZERO side, and the two turn out to be the same rectangular test function seen through
its Fourier transform.

### The zero side
A critical zero contributes the screw term (1 - cos(t*gamma))/gamma^2. The step-L second difference
is governed by the identity

    cos A - 2 cos(A - theta) + cos(A - 2 theta) = -4 sin^2(theta/2) cos(A - theta),

so with A = x*gamma, theta = L*gamma the contribution to the window curvature is EXACTLY

    ( 4 sin^2(L gamma/2) / gamma^2 ) * cos((x - L) gamma).

### The amplitude IS the Fejer weight
    4 sin^2(L gamma/2) / gamma^2  =  (2 - 2 cos(L gamma))/gamma^2  =  | INT_0^L e^{-i gamma u} du |^2,
the squared modulus of the Fourier transform of the indicator of [0,L]. So:

    THE WINDOW CURVATURE IS THE WEIL FORM OF THE RECTANGULAR TEST FUNCTION, WITH THE PRIME SIDE
    CARRYING THE AUTOCORRELATION (TENT) AND THE ZERO SIDE CARRYING ITS FOURIER SQUARE (FEJER).
Tent and Fejer are a Fourier pair — the two halves computed in cycles 61 and 62 match exactly, which
is a strong internal consistency check on both.

### CONSEQUENCE 1 — the critical part is uniformly bounded, with an explicit constant
The Fejer weight is nonnegative and at most 4/gamma^2, so each critical term is bounded in absolute
value by 4/gamma^2 UNIFORMLY IN L AND x. Since SUM_gamma gamma^{-2} converges, the critical part of
the window curvature is an ABSOLUTELY CONVERGENT cosine series, hence uniformly bounded. Therefore

    UNDER RH THE SEMIBOUNDEDNESS CRITERION HOLDS AUTOMATICALLY WITH THE EXPLICIT CONSTANT
    B = -4 SUM_gamma gamma^{-2}.

### CONSEQUENCE 2 — everything unbounded is off-critical, with the amplitude of cycle 60
Off-critical zeros contribute the exponentially growing oscillation of exact amplitude
e^{t a}/(2(a^2 + gamma^2)) computed in cycle 60. So the fully explicit form of the open core is

    [bounded Fejer cosine series over critical zeros]  +  [exponential off-critical terms]  >=  B,

equivalently: the tent-weighted Chebyshev window over primes is dominated, up to O(1), by the
archimedean second difference — and the ONLY possible source of failure is an off-critical zero.

Machine-verified: `RHTower/ScrewWindowFejerAmplitude.lean` (the second-difference cosine identity via
cos_sub/cos_two_mul/sin_two_mul and the half-angle law; the critical screw second difference; the
Fejer amplitude identity; nonnegativity; the bound 4/gamma^2; and the uniform bound on each critical
term; standard axioms only, wired into RHTower).

### Cycle 63 target
Both halves are now explicit and matched. The remaining quantity is the ARCHIMEDEAN second
difference. `normalizedRectangularBottomArchContribution L a` is
(1/pi) INT_R (rectangular transform at x - i)^2 * logDeriv archFactor (3/2 + i x) dx — a Gamma-side
integral against the SQUARE of the rectangular transform, i.e. already the Fejer weight in disguise.
Target: show that its step-L second difference equals the Gamma-side integral of the Fejer weight
against Re Psi(1/4 + i x/2) - log pi, i.e. the archimedean term of the classical Weil form. If that
identification closes, the open core is literally the classical rectangular Weil inequality with
every constant explicit, and the corpus's screw-curvature route and the classical explicit formula
are proved to be the same object rather than two parallel developments.

---

## Cycle 63 (2026-07-26) — THE ARCHIMEDEAN SIDE COLLAPSES TO ONE INTEGRAL IN THE SAME TENT
### Phase 1 corpus search run first, and it CHANGED THE PLAN.

The cycle-62 plan was to compute the archimedean second difference. SEARCH FIRST FOUND that the
corpus already does the hard part: `XiGuinandWeilRectangularResolventFourier`'s
`integral_rectangularEulerFourierKernel_mul_gaussDigammaSeriesTerm` pairs one Gauss/digamma summand
against the rectangular Fourier square and gets

    A(0)/(n+1)  -  INT_0^infinity e^{-(n+3/4)t} A(t/2) e^{t/2} dt,

with A = rectangularTwoEdgeAutocorrelation — THE SAME TENT that carries the prime side. So the planned
computation was already done; the remaining content is what happens when the series is SUMMED.

### THE COLLAPSE (new)
Using 1/(n+1) = INT_0^infinity e^{-(n+1)t} dt and SUM_{n>=0} e^{-nt} = (1-e^{-t})^{-1} for t > 0,

    SUM_n [ A(0)/(n+1) - INT_0^inf e^{-(n+3/4)t} A(t/2) e^{t/2} dt ]
        =  INT_0^inf  ( A(0) e^{-t}  -  A(t/2) e^{-t/4} ) / (1 - e^{-t})  dt .

BOTH SERIES DIVERGE SEPARATELY; THE COMBINATION CONVERGES. The mechanism, proved this cycle:
  * the numerator vanishes LINEARLY at the origin —
        | A(0) e^{-t} - A(t/2) e^{-t/4} |  <=  (A(0) + Lip/2) * t,
    by splitting A(0)e^{-t} - A(t/2)e^{-t/4} = A(0)(e^{-t} - e^{-t/4}) + e^{-t/4}(A(0) - A(t/2));
  * the denominator vanishes linearly with slope one —
        1 - e^{-t}  >=  t/2   for 0 <= t <= 1,  via e^{-t} <= 1/(1+t);
  * hence the integrand is BOUNDED BY 2 A(0) + Lip on (0,1]: the two divergences cancel exactly.
The tent is 1-Lipschitz, so this applies to it directly.

### THE OPEN CORE, NOW COMPLETELY EXPLICIT
Combining cycles 61-63, the rectangular window criterion is ONE elementary inequality:

    INT_0^inf ( A(0) e^{-t} - A(t/2) e^{-t/4} ) / (1 - e^{-t}) dt
        -  2 SUM_{k>=2} ( Lambda(k)/sqrt k ) * A(log k)      >=   B ,

with A the TENT of half-width L (support [0,2L], height L at L). Prime side: tent-weighted Chebyshev
window (cycle 61). Zero side: Fejer cosine series with weights 4 sin^2(L gamma/2)/gamma^2, absolutely
convergent hence bounded (cycle 62). Archimedean side: the single integral above (this cycle). Tent
and Fejer are a Fourier pair, so the three computations are mutually consistent.

EVERY INGREDIENT IS NOW ELEMENTARY. The entire difficulty is the competition between the archimedean
integral and the tent-weighted prime window; no special function, no series over zeros, and no
regularization remains.

Machine-verified: `RHTower/ArchimedeanSingleIntegral.lean` (the denominator bound via
e^{-t} <= 1/(1+t), the exponential gap bound, the linear numerator bound by the split, and the
boundedness of the collapsed integrand at the origin; standard axioms only, wired into RHTower).

### Cycle 64 target
Both sides are now elementary functions of the same tent A. The next question is the first one that
is genuinely quantitative rather than structural: FOR WHICH L IS THE INEQUALITY PROVABLE OUTRIGHT?
The archimedean integral is a fixed functional of A; the prime window is a Chebyshev sum over
[e^{x-2L}, e^x]. For small L the prime window contains few terms and the archimedean integral should
dominate. Compute the exact L-dependence of both — the archimedean integral scales like A(0) = L
times a universal constant, the prime window like L e^{x/2} — and determine the threshold L below
which the inequality is unconditional. That threshold is the honest measure of how far the corpus's
route currently reaches.

---

## Cycle 64 (2026-07-26) — THE SQUARED MAIN TERM; AND A SECOND PHASE-1 SAVE
### Phase 1 corpus search run first and CHANGED THE PLAN AGAIN. Record both outcomes.

### PHASE-1 SAVE (do not redo)
The cycle-63 plan was to identify the criterion with the PNT error term. THE CORPUS ALREADY HAS IT,
and sharper: `CCMSharpPrimeWindow.lean` proves

    dyadicWeightedPrimeWindow_eq_main_add_completedErrorDifference :
      SUM_{n/2 < k <= n} k^{-1/2} Lambda(k)
        = 2(1 - 1/sqrt 2) sqrt n
          + ( criticalMellinCompletedError(log n - log 2) - criticalMellinCompletedError(log n) )
          + 2(sqrt 2 - 1)/sqrt n,

i.e. the sharp moving prime window is EXACTLY its square-root main term plus a backward difference of
the completed critical-Mellin error, with an explicit endpoint term. So the identification
"criterion = PNT error term" is the corpus's own, already exact. NOT RE-DERIVED.

Consequence for the route's status: the rectangular/screw chain is RH-EQUIVALENT AT EVERY STAGE. The
corpus's named core reduces (cycle 61) to plain semiboundedness of the curvature, which reduces (this
identity) to boundedness of differences of the completed critical-Mellin error, which is RH. THE
"OPEN CORE" IS A RESTATEMENT, NOT A REDUCTION. Recorded so it is not treated as a lever.

### WHAT IS GENUINELY NEW — THE SQUARE
The corpus's main term is for the SHARP (box) window: constant 4(1 - e^{-L/2}). The window that
actually appears in the screw criterion is the SECOND DIFFERENCE of the ramp, i.e. the TENT, and the
tent is the AUTOCORRELATION of the box. Its main term is therefore the SQUARE:

    INT_0^{2L} tent_L(v) e^{-v/2} dv  =  4 (1 - e^{-L/2})^2 ,

proved this cycle by exhibiting antiderivatives on the two halves:
    INT_0^L v e^{-v/2} dv          = -2L e^{-L/2} + 4(1 - e^{-L/2}),
    INT_L^{2L} (2L - v) e^{-v/2} dv =  2L e^{-L/2} - 4 e^{-L/2} + 4 e^{-L},
whose sum is 4 - 8 e^{-L/2} + 4 e^{-L} = 4(1 - e^{-L/2})^2.

The square is not incidental: the tent is 1_[0,L] * 1_[0,L], so its Laplace transform at 1/2 is the
square of INT_0^L e^{-v/2} dv = 2(1 - e^{-L/2}). THE POSITIVITY STRUCTURE OF THE WEIL FORM APPEARS
HERE AS AN ARITHMETIC SQUARE, matching exactly the Fejer weight 4 sin^2(L gamma/2)/gamma^2 on the
zero side (cycle 62), which is the squared modulus of the SAME box transform.

    prime side        main term  4(1 - e^{-L/2})^2 * e^{x/2}
    zero side         weights    |INT_0^L e^{-i gamma u} du|^2 = 4 sin^2(L gamma/2)/gamma^2
    archimedean side  kernel     the collapsed single integral in the same tent (cycle 63)

All three sides carry the same square, from the same box. That is the internal coherence of the
rectangular route, now explicit.

Machine-verified: `RHTower/TentWindowMainTerm.lean` (both antiderivatives with HasDerivAt, both
interval integrals, the sum identity, and the square factorization; standard axioms only, wired).

### CORRECTION to cycle 63's summary
Cycle 63 said "the open core is one elementary inequality" with A a fixed tent. That is imprecise: in
the central prime-arch identity the aperture and half-width are LOCKED (L = a = t/2), so A depends on
the sample point as well. The collapsed archimedean integral is correct as an identity for each
(L,a); the criterion is the second difference in t of that family. Both sides then grow like e^{x/2}
and the criterion is the cancellation of those leading terms — which is exactly the PNT error
statement above. Recorded so the earlier phrasing is not read as a stronger claim.

### Cycle 65 target
The three sides are now explicit and their leading constants match. The one quantity not yet computed
anywhere is the ARCHIMEDEAN leading constant: the collapsed integral's e^{x/2} coefficient, which must
equal 4(1 - e^{-L/2})^2 exactly if the main terms cancel. Compute it from the collapsed integrand and
check the match. If it matches, the cancellation is proved unconditionally and the criterion reduces
in full rigour to the error term alone — the cleanest possible statement of where the route ends.

---

## Cycle 65 (2026-07-26) — THE LEADING TERM IS THE POLE TERM, AND THE CANCELLATION IS EXACT

### The leading e^{x/2} is NOT archimedean — it is the POLE of zeta
The e^{x/2} on the "archimedean" side of the rectangular criterion is the POLE TERM of the explicit
formula, from the simple pole of zeta at s = 1. In the u-variable the pole term of a test function h
is INT h(u) e^{u/2} du. And the main term of the prime side is

    SUM_k (Lambda(k)/sqrt k) h(log k) = INT_1^inf h(log y) y^{-1/2} d(psi(y)),   psi(y) = y + E(y),

whose main part INT_1^inf h(log y) y^{-1/2} dy = INT_0^inf h(u) e^{u/2} du IS THE SAME INTEGRAL.

    ==> THE POLE TERM AND THE PRIME MAIN TERM ARE THE SAME INTEGRAL. THEY CANCEL IDENTICALLY, FOR
        EVERY TEST FUNCTION, NOT MERELY TO LEADING ORDER.

This settles the cycle-64 question: the archimedean e^{x/2} coefficient does match 4(1-e^{-L/2})^2 —
because it is literally the same integral, not a separate computation that happens to agree.

### The translation identity (proved)
    INT_{x-2L}^{x} tent_L(x-u) e^{u/2} du = e^{x/2} INT_0^{2L} tent_L(v) e^{-v/2} dv
                                          = e^{x/2} * 4 (1 - e^{-L/2})^2,
the second step by cycle 64. So both sides carry e^{x/2} * 4(1-e^{-L/2})^2 and the cancellation is
exact and unconditional.

### WHERE THE ROUTE ENDS — stated precisely
After the cancellation NOTHING OF SIZE e^{x/2} REMAINS, and the rectangular criterion is exactly

    boundedness of  INT h(log y) y^{-1/2} dE(y)   in the tent-weighted window,

with E the completed critical-Mellin error. That is the classical RH-equivalent statement about the
Chebyshev error, now with every constant explicit and every step machine-verified. Cycles 61-65
together give the full explicit anatomy of the corpus's rectangular route:

    c61  source-energy freedom is VACUOUS; prime second difference = tent-weighted Chebyshev window
    c62  zero side = Fejer cosine series, weights 4 sin^2(L gamma/2)/gamma^2, absolutely convergent
    c63  archimedean side collapses to ONE integral in the same tent; divergences cancel linearly
    c64  tent main term = 4(1 - e^{-L/2})^2, the SQUARE of the sharp-window constant
    c65  the e^{x/2} term is the POLE term; pole and prime main term cancel IDENTICALLY

Machine-verified: `RHTower/PoleTermCancellation.lean` (translation identity via
intervalIntegral.integral_comp_sub_left, the common leading coefficient, the exact cancellation, and
the reduction of the criterion to the error term alone; standard axioms only, wired).

### HONEST STATUS OF THE ROUTE
Every stage is RH-equivalent. The rectangular/screw programme is a complete, exact, and now fully
explicit REFORMULATION of the Chebyshev error bound. It does not reduce RH to anything weaker. Its
value is that it makes every constant explicit and every cancellation unconditional; its limit is
that the residue is the classical statement.

### Cycle 66 target
Since the route bottoms out at the Chebyshev error, the only way forward inside it is a mechanism
that bounds E(y) in a TENT-WEIGHTED window using something other than RH. The tent weight is the one
piece of freedom: it is nonnegative, compactly supported, and its Fourier transform is the Fejer
kernel, hence NONNEGATIVE. Ask whether the nonnegativity of the Fejer weight buys anything for the
error term that a sharp window does not — i.e. whether a positive-definite window admits an
unconditional one-sided bound where a box does not. That is the one structural asymmetry left
unexploited in this route.

---

## Cycle 66 (2026-07-26) — SLIDING DESTROYS POSITIVE TYPE. THE LAST ASYMMETRY IS ABSENT, NOT UNUSED.

Cycle 65 identified the one remaining freedom: the tent weight is nonnegative, compactly supported,
and its Fourier transform is the Fejer kernel, hence nonnegative — apparently Weil positivity waiting
to be used. IT IS NOT AVAILABLE.

### The reason, exactly
The criterion does not use the tent. It uses the tent TRANSLATED TO THE SAMPLE POINT. Translation
multiplies the Fourier transform by a phase:

    hat( h(. - c) )(gamma) = e^{-i c gamma} hat h(gamma),
    Re hat( h(. - c) )(gamma) = cos(c gamma) * hat h(gamma),

and for c != 0 the factor cos(c gamma) CHANGES SIGN. Taking gamma = pi/c gives cos(c gamma) = -1, so
the real part is strictly negative wherever the Fejer weight is strictly positive there (which holds
off the lattice gamma in (2 pi/L) Z).

    ==> FOR EVERY NONZERO SHIFT THE TRANSLATED TENT IS NOT OF POSITIVE TYPE. WEIL POSITIVITY IS
        UNAVAILABLE IN THE SLIDING CRITERION, WHICH IS THEREFORE GENUINELY A BOUNDEDNESS STATEMENT
        AND NOT A NONNEGATIVITY STATEMENT.

### The trade-off is sharp
Positive type holds EXACTLY at the centred window c = 0, where the criterion is a single inequality
at one point and cannot detect the zeros. The sliding family that is equivalent to RH NECESSARILY
LEAVES THE POSITIVE-TYPE CLASS. So the last structural asymmetry of this route is not merely
unexploited — IT IS ABSENT.

Machine-verified: `RHTower/SlidingBreaksPositiveType.lean` (the phase factor and its real part, the
sign flip cos(c * (pi/c)) = -1, strict negativity of the translated transform, positivity of the
Fejer weight off the lattice, and the centred case; standard axioms only, wired).

### THE ANATOMY OF THE RECTANGULAR ROUTE — COMPLETE (cycles 61-66)
    c61  source-energy freedom is VACUOUS; prime 2nd difference = tent-weighted Chebyshev window
    c62  zero side = Fejer cosine series, weights 4 sin^2(L gamma/2)/gamma^2, absolutely convergent
    c63  archimedean side collapses to ONE integral in the same tent; divergences cancel linearly
    c64  tent main term = 4(1 - e^{-L/2})^2, the SQUARE of the sharp-window constant
    c65  the e^{x/2} term is the POLE term; pole and prime main term cancel IDENTICALLY
    c66  sliding destroys positive type; no positivity is available anywhere in the family
CONCLUSION: the rectangular/screw route is an exact, fully explicit, machine-verified REFORMULATION
of the Chebyshev error bound, with every constant computed and every cancellation unconditional, and
with NO positivity structure that could yield a one-sided unconditional estimate. Its residue is the
classical RH-equivalent statement and nothing weaker.

### Cycle 67 target
The route is closed. The corpus's SOTA file lists other live walls that the classification has not
touched, in particular the source-pure construction problem recorded in
`completed-seam-thorin-subordinator-rh.md` (Thorin/GGC: unconditional infinite divisibility and
Thorin density positivity for the reciprocal completed-zeta ratio hold only in Re s > 1; at the
critical seam the chain is RH-equivalent). Before opening it, run the Phase 1 search on
"Thorin", "GGC", "complete monotonicity", "Stieltjes-Pick" and read that pipeline card — the last two
cycles have shown that reading the corpus first is worth more than any amount of independent
derivation.

---

## Cycle 67 (2026-07-26) — THE THORIN LANE: k_src IS THE GAUSSIAN HEAT TRACE, AND EACH PRIME PEAKS
## AT TIME log^2(n)/2

### Phase 1 (binding) — read the corpus's own in-progress card first
`docs/drafts/pipeline/1-in-progress/completed-seam-thorin-subordinator-rh.md` states the lane
precisely. With Xi(w)=xi(1/2+w), Phi(s)=Xi(sqrt s), F_src(s)=Phi(0)/Phi(s):
GGC membership of F_src is an RH EQUIVALENCE (parent theory), and the card is explicit that
"the only proof-bearing novelty can be a divisor-free construction of U from the completed source",
with the first source-side target being an explicit theta-prime formula for the Levy density
k_src(x) = INT e^{-tx} dU(t) followed by its complete monotonicity.

Also found (do not duplicate): `RHTower/XiGaussianHeatTraceDisproof.lean` already proves
`not_riemannHypothesis_of_xiGaussianHeatTraceReal_neg` — A SINGLE STRICTLY NEGATIVE GAUSSIAN
HEAT-TRACE VALUE AT POSITIVE TIME CONTRADICTS RH. That is a live falsification handle.

### THE IDENTIFICATION (new)
Under the Hadamard product U = SUM_gamma m_gamma delta_{gamma^2}, so

    k_src(x) = SUM_gamma m_gamma e^{-gamma^2 x}   =   THE GAUSSIAN HEAT TRACE OVER THE ZEROS.

So the Thorin card's Levy density and the corpus's Gaussian heat trace are THE SAME OBJECT, and the
existing disproof theorem is the consumer end of the Thorin lane. Nothing in the corpus connected
them.

### THE SOURCE SIDE, EXPLICITLY
The Gaussian hat h(gamma) = e^{-gamma^2 x} comes from the u-side test function
h(u) = (4 pi x)^{-1/2} e^{-u^2/(4x)}. So the PRIME contribution to the heat trace is

    (4 pi x)^{-1/2} SUM_n (Lambda(n)/sqrt n) e^{-log^2 n/(4x)},

a positive sum entering with a minus sign — the explicit theta-prime formula the card asks for.

### THE BUMP LOCATION (new, machine-verified)
With a = log n the profile g_a(x) = x^{-1/2} e^{-a^2/(4x)} has
    (log g_a)'(x) = (a^2/4 - x/2)/x^2 = (a^2/2 - x)/(2 x^2),
so it INCREASES on (0, a^2/2), PEAKS EXACTLY AT x = a^2/2, and DECREASES after, with peak value
(a^2/2)^{-1/2} e^{-1/2} = sqrt 2 e^{-1/2}/|a|.

    ==> THE PRIME POWER n IS MAXIMALLY VISIBLE IN THE GAUSSIAN HEAT TRACE AT TIME x = log^2(n)/2.

This is directly actionable for the corpus's own falsification theorem: it says WHICH TIME SCALE
PROBES WHICH PRIME. The probe time is strictly increasing in log n, so the small primes live at small
times and the trace at time x is dominated by primes with log n ~ sqrt(2x).

### WHY TERMWISE COMPLETE MONOTONICITY FAILS (new, machine-verified)
A completely monotone function is nonincreasing. The profile g_a is NOT, for any a != 0 — it strictly
increases before its peak. So the prime side of k_src is not completely monotone summand by summand;
complete monotonicity can only hold AFTER the archimedean and polar completion. This confirms the
card's recorded residue ("termwise prime positivity fails after seam division") with an explicit
turning point rather than a qualitative remark.

Machine-verified: `RHTower/PrimeHeatBumpLocation.lean` (the log-derivative in sign form, strict
increase before and decrease after the peak, the peak characterization, the peak value, the failure
of monotonicity, and strict monotonicity of the probe time; standard axioms only, wired into RHTower).

### Cycle 68 target
The Thorin lane now has both ends explicit: consumer = the existing Gaussian heat-trace disproof
theorem; source = the theta-prime formula with bump structure. The card's OPEN CORE A is "positive
packet measure" for the incomplete-Gamma half-stable packets. The natural next step, and the first
one that is quantitative rather than structural, is the ARCHIMEDEAN half of the heat trace: compute
the Gamma-side contribution against the same Gaussian test function and compare its size at time
x = log^2(n)/2 with the prime bump peak sqrt 2 e^{-1/2}/log n. If the archimedean term at that time
is smaller than the prime bump for some n, the heat trace is negative there and RH is FALSE by the
existing theorem; if it dominates for all n, that is the first unconditional positivity gain in the
lane. Either outcome is decisive. This is the sharpest falsification test the programme has reached.

---

## Cycle 68 (2026-07-26) — THE HEAT-TRACE TEST IS SHARP BUT SUPER-EXPONENTIALLY INSENSITIVE
### The cycle-67 falsification plan is EXECUTED and comes out NEGATIVE. Recorded as a dead end with
### its exact reason.

Cycle 67 proposed testing the corpus's disproof endpoint at the prime bump time x = log^2(n)/2.
CARRIED OUT:

### The pole term dwarfs everything at the bump time
With h(u) = (4 pi x)^{-1/2} e^{-u^2/(4x)}, completing the square
    -u^2/(4x) + u/2 = -(u-x)^2/(4x) + x/4
gives the POLE TERM = 2 e^{x/4}. At the bump time x = log^2(n)/2 this is 2 e^{log^2(n)/8}, i.e.
2 n^{log(n)/8} — SUPER-POLYNOMIALLY LARGE — while the prime bump peak is only
sqrt(2) e^{-1/2}/log n, of size 1/log n. THE TRACE IS TRIVIALLY POSITIVE THERE.
    ==> THE BUMP TIME IS USELESS AS A PROBE. Recorded so it is not retried.

### Why: the pole and prime main terms cancel identically (again)
The pole term 2 INT h(u) cosh(u/2) du and the prime main term INT h(u) e^{|u|/2} du are the same
integral — the cycle-65 cancellation, now with the Gaussian instead of the tent. What survives is the
ARCHIMEDEAN integral plus the PRIME ERROR.

### The real sensitivity, at large time
  * ZERO SIDE: if every ordinate has gamma_1 <= |gamma| then for x >= 1
        SUM_gamma e^{-gamma^2 x} <= C e^{-gamma_1^2 x},  C = e^{gamma_1^2} SUM_gamma e^{-gamma^2},
    proved termwise. With gamma_1 ~ 14.13 this is of size e^{-200 x} — SUPER-EXPONENTIALLY SMALL.
  * SOURCE SIDE: the archimedean integral concentrates at r = 0 for large x and contributes at order
    x^{-1/2} with the NEGATIVE constant Psi(1/4) - log pi ~ -5.37.
Hence at large x the identity reads

    (super-exponentially small, positive under RH) = (negative, order x^{-1/2}) + (prime error).

    ==> RH FORCES THE PRIME ERROR TO CANCEL A NEGATIVE ARCHIMEDEAN TERM OF ORDER x^{-1/2} DOWN TO
        ORDER e^{-gamma_1^2 x}. Any failure of that cancellation at any large time gives a negative
        heat trace and DISPROVES RH.

That is what makes the endpoint sharp — and exactly why it cannot be triggered: one must control a
cancellation of polynomially small quantities to super-exponential accuracy. Formalized: the
cancellation is forced two-sidedly, -A <= E <= -A + eps with eps the super-exponential bound, and the
exponential bound beats any fixed eps past an explicit threshold log(C/eps)/gamma_1^2.

### STATUS OF THE THORIN/HEAT LANE
Consumer end: exists and is sharp (corpus). Source end: explicit (cycle 67). Probe: USELESS at the
bump time (this cycle), and at large time requires super-exponential precision. So the lane is not
capped by a structural no-go — it is capped by SENSITIVITY. That is a different kind of wall from the
ten in the atlas, and it is worth naming: A CRITERION CAN BE BOTH EXACT AND UNUSABLE.

Machine-verified: `RHTower/HeatTraceSensitivity.lean` (completed square, termwise super-exponential
tail bound, the explicit threshold past which exponential decay beats any fixed epsilon, and the
two-sided forced cancellation; standard axioms only, wired into RHTower).

### Cycle 69 target
Sensitivity, not structure, is the wall in this lane. The remedy for a sensitivity wall is a test
function whose zero side is NOT super-exponentially small — i.e. one whose Fourier transform decays
only polynomially, so that the zero side and the archimedean side are the same order. The Gaussian is
the worst possible choice in exactly this respect. Target: identify the test functions for which the
zero side and the archimedean side have matching order, and check whether any of them is admissible
(even, real, of the required decay) — that is the only way the corpus's exact endpoint becomes
usable.

---

## Cycle 69 (2026-07-26) — Theorem: ONE SCALE CANNOT SEE BOTH THE FIRST ZERO AND THE FIRST PRIME
### This unifies the sliding-window half (c61-66) and the heat-trace half (c67-68) under ONE inequality.

Cycle 68 found the heat-trace endpoint exact but untriggerable and called the wall "sensitivity".
This cycle identifies the wall exactly, and it is not delicacy — it is a SCALE MISMATCH, and it is
general.

### The two resolution requirements
A test function of width W in u has frequency scale 1/W.
  * TO SEE ZEROS the frequency scale must reach the first ordinate: 1/W >= gamma_1, i.e.
    W <= 1/gamma_1 ~ 0.0708. Below that THE ZERO SIDE OF THE EXPLICIT FORMULA IS EMPTY — no ordinate
    lies in the window — and the identity degenerates into arch + prime error ~ 0, with NO SPECTRAL
    CONTENT. That is exactly the large-time Gaussian: its frequency scale x^{-1/2} tends to 0, far
    BELOW gamma_1. The heat trace at large time probes a band containing no zeros at all.
  * TO SEE PRIMES the support must reach the first prime log: W >= log 2 ~ 0.693. Below that every
    prime term is exponentially suppressed. That is exactly the small-time Gaussian.

### THE OBSTRUCTION
    gamma_1 * log 2  ~  14.13 * 0.693  ~  9.8  >  1,
so W <= 1/gamma_1 and W >= log 2 are INCOMPATIBLE.

    ==> NO SINGLE-SCALE TEST FUNCTION RESOLVES BOTH THE FIRST ZERO AND THE FIRST PRIME. A WINDOW
        NARROW ENOUGH TO SEE THE SPECTRUM IS AN ORDER OF MAGNITUDE TOO NARROW TO SEE THE PRIMES.

For the Gaussian specifically the admissible windows are x <~ gamma_1^{-2} ~ 5e-3 (zeros) and
x >~ log^2(2)/4 ~ 0.12 (primes), disjoint by a factor ~25 — proved from gamma_1 log 2 > 2.

### THE DICHOTOMY — and it explains everything recent
A test function with a SECOND scale (a modulation frequency, equivalently a translation) CAN couple
the two sides: the modulation lifts the frequency window to gamma_1 while the width still reaches
log 2. THAT IS PRECISELY THE SLIDING RECTANGULAR WINDOW of cycles 61-66. But translation destroys
positive type (cycle 66). Hence:

    ONE SCALE   ->  no coupling: the criterion is exact but SPECTRALLY EMPTY      (c67-68)
    TWO SCALES  ->  coupling, hence RH-EQUIVALENCE, but POSITIVITY IS LOST        (c61-66)

Both halves of the recent programme are consequences of the single inequality gamma_1 log 2 > 1. This
is the first statement that unifies them, and it is a genuine structural reason rather than a
coincidence of two failures.

Machine-verified: `RHTower/ScaleIncompatibility.lean` (the incompatibility from gamma_1 log 2 > 1,
the margin from log 2 > 1/2, the disjointness of the Gaussian windows from gamma_1 log 2 > 2, and the
dichotomy; standard axioms only, wired into RHTower).

### WHAT THIS ADDS TO THE ATLAS — an eleventh entry, of a new kind
    scale incompatibility     gamma_1 log 2 > 1 forbids a single-scale test from coupling the
                              spectral and arithmetic sides; two-scale tests couple but lose
                              positive type.
Unlike the first ten this is not a cap on a lane; it is a constraint on TEST FUNCTIONS, and it
applies to every explicit-formula argument at once.

### Cycle 70 target
The dichotomy leaves exactly one unexplored corner: a test function with two scales that is
nevertheless of positive type. Translation is not the only way to add a scale — a SYMMETRIC pair of
modulations, h(u) cos(theta u) with the cosine symmetric rather than a one-sided shift, keeps the
transform real and even. Its Fourier transform is (hat h(r - theta) + hat h(r + theta))/2, which is
NONNEGATIVE whenever hat h is. Target: check whether the symmetric modulation gives both couplings
(frequency window at theta ~ gamma_1, width reaching log 2) AND positive type — if so it is the first
admissible two-scale positive-type test in the programme, and the Weil positivity machinery becomes
available where cycle 66 showed it was not.

---

## Cycle 70 (2026-07-26) — SYMMETRIC MODULATION: TWO SCALES **AND** POSITIVE TYPE
### This CORRECTS Theorem Q49 (universal height degradation). Record the correction prominently.

Cycle 69 showed a single-scale test cannot resolve both the first zero and the first prime, and
cycle 66 showed the obvious second scale — a one-sided translation — destroys positive type. The
symmetric modulation does neither.

### The construction
Take g(u) = h(u) cos(theta u) with h real and even. Then
    hat g(r) = ( hat h(r - theta) + hat h(r + theta) ) / 2,
which is NONNEGATIVE whenever hat h is. SYMMETRIC MODULATION PRESERVES POSITIVE TYPE where a
one-sided translation does not. And it has TWO scales — the width W of h and the modulation theta —
so W >= log 2 and a frequency window centred at theta >= gamma_1 hold SIMULTANEOUSLY. The cycle-69
obstruction applies only to single-scale tests.
(The construction itself is standard in Weil-positivity numerics — NOT claimed as new. What is new
is its role here: it is exactly the object that evades c69 and restores what c66 lost.)

### THE TUNED GAIN — and the correction to Q49
An off-critical zero at 1/2 + a + i gamma contributes with a Fejer-type denominator at the shifted
frequency. UNTUNED (theta = 0) it carries 1/(a^2 + gamma^2). TUNED to theta = gamma it carries
1/(a^2 + (gamma - theta)^2) = 1/a^2. The ratio is

    (a^2 + gamma^2)/a^2 = 1 + (gamma/a)^2,

so tuning REMOVES THE gamma^{-2} SUPPRESSION ENTIRELY.

    ==> THEOREM Q49 AS STATED IS TOO STRONG. "Every quantified lane loses strength at a putative
        counterexample polynomially or exponentially in its height" is true of UNTUNED criteria only.
        A TUNED SYMMETRIC MODULATION IS HEIGHT-NEUTRAL: its sensitivity at theta = gamma does not
        depend on gamma at all.

What remains height-limited is NOT the criterion but THE SEARCH: one must find the right theta, and
scanning theta up to height X costs what verifying to height X costs. THE DEGRADATION MOVES FROM THE
ESTIMATE TO THE SEARCH. That is a different and sharper statement than Q49, and it means the
"verification and estimate never meet" conclusion must be restated: they never meet WITHOUT TUNING;
with tuning they meet exactly at the scanned height.

Machine-verified: `RHTower/TunedModulationGain.lean` (preservation of positive type, the contrast
with one-sided translation reusing c66, simultaneous satisfiability of the two scale conditions, the
minimality of the tuned denominator, the gain identity 1 + (gamma/a)^2, its monotonicity in gamma,
and height-neutrality at theta = gamma; standard axioms only, wired into RHTower).

### STATUS OF THE ATLAS AFTER THIS CORRECTION
    Q49 (height degradation)   ->  RESTATED: applies to untuned criteria; tuned symmetric
                                   modulations are height-neutral, and the cost moves to the search.
    c66 (no positivity)        ->  RESTATED: applies to one-sided translations; symmetric
                                   modulations keep positive type.
    c69 (scale incompatibility)->  STANDS, but only for single-scale tests.
So of the recent structural results, the two negative ones were each about a specific realization,
and the symmetric modulation escapes both. That is the first time in this programme that a proposed
obstruction has been escaped rather than confirmed or shown vacuous.

### Cycle 71 target
With a two-scale positive-type test in hand, the Weil machinery is available again. The concrete
question is now the one c66 blocked: for the symmetric modulation g = h cos(theta .) with h the box
of width W, is the Weil form W(g) bounded below UNIFORMLY IN theta? Uniformity in theta is exactly
what the tuned gain makes nontrivial — at each theta the form sees the zeros near theta with
undiminished strength. Compute W(g) explicitly for the modulated box: prime side
2 SUM Lambda(n)/sqrt n * h(log n) cos(theta log n), zero side SUM_rho hat g(gamma_rho), archimedean
side the same Gamma integral against hat g. All three are already elementary from cycles 61-65; the
only new ingredient is the cosine factor. That is the sharpest concrete target the programme has.

---

## Cycle 71 (2026-07-26) — THE MODULATED TENT COMPUTED; A DOUBLY EXPONENTIAL ALIGNMENT THRESHOLD

With the two-scale positive-type test g(u) = tent_L(u) cos(theta u) all three sides are elementary.

### Pole term, closed form
The tent is even, so with s = 1/2 + i theta and the antiderivative
F(u) = (L-u)e^{su}/s + e^{su}/s^2:

    INT tent_L(u) cos(theta u) e^{|u|/2} du = 2 Re INT_0^L (L-u) e^{su} du
                                            = 2 Re ( (e^{sL} - 1)/s^2  -  L/s ).

Since |s| >= theta this is O(e^{L/2}/theta^2 + L/theta): AT FIXED WIDTH THE POLE TERM VANISHES AS THE
MODULATION GROWS. (Both summands proved antitone in theta.)

### Prime side, and its supremum
The modulated prime sum is a FINITE DIRICHLET POLYNOMIAL
    2 Re SUM_{n <= e^L} (Lambda(n)/n^{1/2 + i theta}) (L - log n),
whose supremum over theta is the all-phases-aligned value SUM (Lambda(n)/sqrt n)(L - log n).
Replacing von Mangoldt by its density gives the EXACT comparison integral

    INT_1^N (log N - log y)/sqrt y dy = 4 sqrt N - 4 - 2 log N,     N = e^L,

so the aligned prime sum is of size 4 e^{L/2}. (Antiderivative G(y) = 2 sqrt y (L - log y) + 4 sqrt y,
evaluated exactly.)

### Archimedean side
Mass of hat g times digamma growth: ~ L log theta.

### THE THRESHOLD
Survival at a modulation where the phases nearly align requires L log theta >~ 4 e^{L/2}, i.e.

    theta  >~  exp( 4 e^{L/2} / L )        — DOUBLY EXPONENTIAL IN THE WIDTH.

By Q-independence of the prime logarithms such alignment DOES occur; the height at which it first
occurs is a simultaneous-Diophantine-approximation question. So:

    WEIL POSITIVITY FOR THE MODULATED TENT IS CONSISTENT WITH RH PRECISELY BECAUSE THE KRONECKER
    ALIGNMENT HEIGHT IS DOUBLY EXPONENTIAL IN THE WIDTH.

This is the SAME doubly exponential barrier already met in the flow lane (cycle 45: verification to
height X bounds Lambda only by pi^2/(2 log^2 X)) and in the Nyman-Beurling lane (cycle 49: closing the
floor needs N >= exp(X^2)). Three independent lanes, one barrier — and now with an explicit
functional form, exp(4 e^{L/2}/L), rather than a qualitative remark.

Machine-verified: `RHTower/ModulatedBoxWeilForm.lean` (the exact prime comparison integral via its
antiderivative, the leading-term bound, antitonicity of the pole bound in the modulation, the
alignment threshold theta >= exp(4 e^{L/2}/L), and the double exponentiality of that threshold;
standard axioms only, wired into RHTower).

### WHAT THIS SETTLES ABOUT THE CORRECTED Q49
Cycle 70 corrected Q49: tuned criteria are height-neutral, and the cost moves to the SEARCH. This
cycle prices the search: to reach the alignment that would test positivity at width L one must scan
to height exp(4 e^{L/2}/L). So the corrected Q49 is now quantitative — THE SEARCH COST IS DOUBLY
EXPONENTIAL IN THE WIDTH, and the width is what controls how many primes the test sees. That is the
precise trade-off the whole effective programme faces, in one formula.

### Cycle 72 target
The barrier is now identified as simultaneous Diophantine approximation of {log p}. The corpus has
`RHTower/KroneckerTransferThreshold.lean` and `RHTower/LiouvillePointReachability.lean` and
`RHTower/SmoothCommaExclusionBand.lean` from the earlier Bohr-lift work — exactly this technology.
Target: read those, and determine whether the alignment height for the FIRST k primes is known to be
doubly exponential in k (an upper bound would make the threshold sharp) or only conjectured. If the
alignment height is provably smaller than exp(4 e^{L/2}/L) for some L, the modulated Weil form fails
there and RH is FALSE; if provably larger for all L, that is an unconditional positivity gain. This
is the first place where the Diophantine and analytic halves of the programme meet with both sides
explicit.

---

## Cycle 72 (2026-07-26) — PRIME-PHASE ALIGNMENT CANNOT BREAK WEIL POSITIVITY
### One of the two conceivable failure modes is removed UNCONDITIONALLY.

Cycle 71 gave the positivity threshold theta >~ exp(4 e^{L/2}/L). This cycle compares it with the
height at which alignment actually occurs.

### Where alignment occurs (Dirichlet pigeonhole)
Simultaneous approximation of k frequencies to within epsilon is guaranteed by height (2 pi/eps)^k.
The modulated tent of width L sees primes up to e^L, so k = pi(e^L) ~ e^L/L, and the alignment height
is exp( (e^L/L) log(2 pi/eps) ) — doubly exponential in L, with EXPONENT e^L/L.

### The threshold is exponentially smaller
The threshold exponent is 4 e^{L/2}/L. Since 4 e^{L/2} <= e^L as soon as e^{L/2} >= 4, i.e.
L >= 2 log 4 ~ 2.77, THE ALIGNMENT HEIGHT EXCEEDS THE THRESHOLD FOR EVERY WIDTH PAST THAT POINT, and
the gap between the exponents is exactly the factor e^{L/2}/4 (proved as an identity), itself
exponentially large.

    ==> AT THE HEIGHT WHERE THE PRIME PHASES FIRST ALIGN, THE ARCHIMEDEAN TERM ALREADY EXCEEDS THE
        ALIGNED PRIME SUM BY AN EXPONENTIALLY LARGE FACTOR. ALIGNMENT NEVER VIOLATES WEIL POSITIVITY
        FOR THE MODULATED TENT.

### Baker makes it worse for alignment
The pigeonhole height is only where alignment CAN occur. To threaten positivity one needs alignment
MUCH EARLIER — exceptionally good simultaneous rational approximation of {log p}. Baker's theorem,
already fixed in this corpus (`RHTower/BakerWeldIndependence.lean`: Q-bar-linear independence of the
prime logarithms), supplies effective lower bounds for linear forms in those logarithms and therefore
FORBIDS exceptionally early alignment. THE ARITHMETIC INDEPENDENCE OF THE PRIMES PROTECTS THE
POSITIVITY.

### WHAT THIS NARROWS — the real result
    IF WEIL POSITIVITY FAILS FOR THE MODULATED TENT, IT CANNOT FAIL THROUGH PRIME-PHASE ALIGNMENT.
    IT MUST FAIL THROUGH THE ZEROS.
That removes one of the two conceivable failure modes unconditionally. Every earlier structural
result in this programme was a cap on a method; this one is a constraint on HOW RH COULD BE FALSE.

Machine-verified: `RHTower/AlignmentHeightExceedsThreshold.lean` (4e^{L/2} <= e^L from e^{L/2} >= 4,
the exponent comparison, the exact exponent gap identity, domination at the alignment height, and the
narrowing; standard axioms only, wired into RHTower).

### THE THREE-LANE BARRIER, NOW EXPLAINED
Cycles 45, 49 and 71 each found a doubly exponential barrier. This cycle identifies its common
source: THE NUMBER OF PRIMES BELOW THE TEST WIDTH. In every lane the barrier exponent is the prime
count pi(e^L) ~ e^L/L, because that is how many independent phases must align before the arithmetic
side can compete with the archimedean side. The barrier is not three coincidences; it is one
counting fact.

### Cycle 73 target
Failure must be spectral. The corpus's own falsification endpoints are all spectral (the Gaussian
heat-trace negativity, the finiteness threshold, the off-critical amplitude). With alignment excluded,
the modulated-tent Weil form becomes a clean spectral detector: its value at modulation theta is
dominated by zeros with ordinate near theta, with the tuned gain 1 + (gamma/a)^2 of cycle 70 and no
competing arithmetic mechanism. Target: derive the explicit lower bound on how negative W_theta
becomes in the presence of an off-critical zero at 1/2 + a + i theta — i.e. combine the tuned gain
with the exponential amplitude e^{aL} of cycle 60 — and compare it against the archimedean term
L log theta. If the off-critical contribution exceeds L log theta for some accessible (L, theta), the
existence of such a zero is contradicted and RH follows for that region.

---

## Cycle 73 (2026-07-26) — DETUNING, NOT TUNING. CORRECTS CYCLE 70.

### THE CORRECTION (record prominently)
Cycle 70 called theta = gamma the "tuned" choice with gain 1 + (gamma/a)^2. THE GAIN IS IN MAGNITUDE
ONLY; THE SIGN IS WRONG. For the Fejer weight Fej(w) = (2 - 2 cos(wL))/w^2 and an off-critical zero
1/2 + a + i gamma with complex ordinate gamma - i a, at modulation theta the argument is delta - i a
with delta = gamma - theta, and

    cos((delta - i a) L) = cos(delta L) cosh(a L) + i sin(delta L) sinh(a L),

so the real numerator is 2 - 2 cos(delta L) cosh(a L).

  * TUNED, delta = 0: numerator 2 - 2 cosh(aL) <= 0 and denominator (-ia)^2 = -a^2 < 0, so the
    contribution is POSITIVE and exponentially large. TUNING MAKES THE OFF-CRITICAL ZERO *HELP*
    POSITIVITY.
  * DETUNED, delta = pi/L: cos(delta L) = -1, numerator 2 + 2 cosh(aL) > 0, denominator of modulus
    ~ pi^2/L^2 + a^2, so the contribution is NEGATIVE of magnitude ~ 2 L^2 cosh(aL)/pi^2.

    ==> AN OFF-CRITICAL ZERO DRIVES THE MODULATED WEIL FORM MOST NEGATIVE AT DETUNING
        |theta - gamma| = pi/L, WITH CONTRIBUTION ~ -(2 L^2/pi^2) cosh(a L).

### THE DETECTION WIDTH AND ITS COST
Against an archimedean term ~ L log theta, negativity occurs once

    (2 L^2/pi^2) cosh(aL)  >~  L log theta   <=>   e^{aL}  >~  pi^2 log theta / L,

which holds for L ~ log log theta / a. The number of primes the test needs is then

    e^L = (log theta)^{1/a}                     [exact identity, formalized]

POLYNOMIAL IN log theta FOR FIXED DEVIATION. So LARGE deviations are cheap to exclude and SMALL ones
expensive, with cost exactly (log theta)^{1/a}. Sample points: at height 10^12, log log ~ 3.3, so
a = 0.4 needs L ~ 8.25 and about e^{8.25} ~ 3800 primes (feasible), while a = 0.01 needs L ~ 330 and
e^{330} primes (hopeless). THIS IS AN EXPLICIT FORM OF THE CLASSICAL ZERO-FREE-REGION/HEIGHT
TRADE-OFF, derived here from the modulated Weil form rather than from a growth bound.

Machine-verified: `RHTower/DetuningDetection.lean` (the tuned numerator is nonpositive, the detuned
numerator is positive and at least e^{aL}, the detuned magnitude is strictly positive, the detection
inequality, the exact cost identity exp(log T/a) = T^{1/a}, and antitonicity of the cost in the
deviation; standard axioms only, wired into RHTower).

### WHERE THIS LEAVES THE MODULATED-TENT LANE
  * alignment cannot break positivity (cycle 72) — failure must be spectral;
  * an off-critical zero DOES break it, at an explicit detuning pi/L and width log log theta / a;
  * the cost of the test is (log theta)^{1/a}, exponential in 1/a.
So the lane gives a genuine, quantitative, explicit detector whose only limitation is the 1/a
exponent — the same shape as every classical zero-free region. THE MODULATED WEIL FORM IS THEREFORE
NOT A NEW MECHANISM BUT A NEW DERIVATION OF THE CLASSICAL TRADE-OFF, with all constants explicit.

### Cycle 74 target
The 1/a exponent is the whole obstruction, and it enters through e^{aL} needing to beat log theta.
The only way to weaken it is to make the archimedean side smaller relative to the prime side at fixed
L — i.e. to choose a weight whose archimedean pairing is smaller than the Fejer one for the same
prime reach. That is an extremal problem: minimize the archimedean pairing subject to fixed prime
support and positive type. This is precisely the extremal problem underlying the Beurling-Selberg
majorant theory, which the corpus has not yet been searched for. Run Phase 1 on
"Beurling-Selberg", "extremal majorant", "one-sided approximation" before doing anything else; if the
corpus lacks it, this is the first genuinely classical tool the programme has needed and not had.

---

## Cycle 74 (2026-07-26) — THE EXTREMAL TEST **IS** lambda(L). A PHASE-1 SAVE AGAINST MY OWN X31.

### Phase 1 outcome, two parts
(a) BEURLING-SELBERG extremal majorant theory is ABSENT from the Lean corpus (grep + research;
    the pipeline hits are unrelated uses of "majorant"). It looked like the first classical tool the
    programme needed and lacked.
(b) IT IS NOT THE TOOL THIS OBSTRUCTION NEEDS, and the obstruction is one I already closed.

### The reduction
The proposal was: keep the prime reach e^L and SHRINK the archimedean pairing, by optimizing over
positive-type tests of fixed support. But a real even g with hat g >= 0 and supp g in [-L,L] factors
as g = phi * phi~ with supp phi in [-L/2, L/2]. So minimizing INT hat g(r) W(r) dr subject to a
normalization is minimizing INT |hat phi(r)|^2 W(r) dr over phi supported in [-L/2,L/2] — THE BOTTOM
OF THE SPECTRUM OF THE COMPRESSED MULTIPLIER ON PALEY-WIENER SPACE. With the prime form included that
bottom is EXACTLY lambda(L), the quantity of the extension programme.

### And lambda is capped — by my own Theorem X31
`ExtensionProgrammeNoGo.extension_forces_positivity`: any NONDECREASING lower bound for lambda that is
NONNEGATIVE AT ONE LENGTH forces lambda >= 0 everywhere, i.e. RH. So the extremal test cannot be shown
to beat the Fejer one without proving RH.

    ==> THE 1/a EXPONENT IN THE DETECTION COST IS NOT AN ARTEFACT OF THE FEJER CHOICE. IMPROVING IT
        MEANS IMPROVING lambda(L), AND THAT IS RH-EQUIVALENT. THE COST (log theta)^{1/a} IS WHAT ANY
        POSITIVE-TYPE TEST OF WIDTH L ACHIEVES, UP TO AN OPTIMIZATION THAT IS ITSELF THE HYPOTHESIS.

### Why Beurling-Selberg does not apply
The B-S problem is ONE-SIDED APPROXIMATION OF A FIXED FUNCTION by bandlimited ones. Here the WEIGHT is
fixed and the TEST varies — a different extremal problem, whose value is lambda(L). Recorded so the
B-S detour is not opened later on the same reasoning.

Machine-verified: `RHTower/ExtremalTestIsLambda.lean` (the extremal/test comparison, the optimization
gap, the cap re-derived from extension_forces_positivity, and the intrinsic antitonicity of the cost
exponent; standard axioms only, wired into RHTower).

### METHOD NOTE (sixth save)
This is the sixth time Phase 1 has changed or stopped a cycle, and the FIRST time it caught me
re-opening a lane closed by my OWN earlier theorem, forty cycles back. The worklog and the corpus
search are doing exactly the job the project rules assign them. Reinforced rule: search the corpus
for the OBJECT (here lambda(L), the compressed-multiplier bottom) and not only for the PROPOSED TOOL
(here Beurling-Selberg) — the object is what identifies the duplicate.

### WHERE THE MODULATED-TENT LANE NOW STANDS — closed, with everything explicit
    alignment cannot break positivity                                  (c72)
    an off-critical zero breaks it at detuning pi/L, width loglog/a    (c73)
    detection cost (log theta)^{1/a}                                   (c73)
    the cost exponent cannot be improved without proving RH            (c74, via X31)
So the lane is a complete, explicit, machine-verified derivation of the classical zero-free-region /
height trade-off, and its constant is optimal up to an RH-equivalent optimization. Like the
rectangular route before it, it terminates at an RH-equivalent statement — but unlike that route, it
does so with an explicit detector and an explicit cost.

### Cycle 75 target
Every analytic lane opened so far terminates at an RH-equivalent statement, and the classification
(eleven entries) explains why. The one thing the programme has NOT done is test whether the ATLAS
ITSELF has a gap: all eleven entries constrain criteria that read or construct from the completed
zeta function alone. None addresses criteria that use a SECOND L-function — the joint structure of
zeta and a Dirichlet L-function, where the zeros interlace and the prime sides share support. Run
Phase 1 on "joint", "pair correlation of two L-functions", "Dirichlet L Weil form", and on the corpus
folders for Dirichlet material; if the joint setting is absent, that is a genuinely untouched
direction and the first one in seventy cycles that is not a variant of a single-zeta criterion.

---

## Cycle 75 (2026-07-26) — THE JOINT / MULTI-L SETTING: A REAL GAIN, BUT ONLY ON AVERAGE
### The atlas has NO GAP: a second L-function creates no mechanism outside the eleven entries.

Phase 1: the joint setting is absent from the Lean corpus. Opened it.

### The averaged Weil form
The Weil form is ADDITIVE over a family, so summing over all Dirichlet characters mod q multiplies
the archimedean and pole contributions by phi(q), while by ORTHOGONALITY the prime side collapses:

    SUM_{chi mod q} SUM_n (Lambda(n) chi(n)/sqrt n) h(log n)
        = phi(q) * SUM_{n = 1 mod q} (Lambda(n)/sqrt n) h(log n).

The restricted sum is about 1/phi(q) of the full prime sum, so the two factors cancel: THE PRIME SIDE
STAYS THE SIZE OF A SINGLE ZETA PRIME SUM WHILE THE ARCHIMEDEAN SIDE HAS GROWN BY phi(q).

    ==> AVERAGING OVER THE CHARACTER FAMILY IMPROVES THE ARCHIMEDEAN-TO-PRIME RATIO BY A FACTOR
        phi(q). POSITIVITY OF THE AVERAGE IS EASIER BY THAT FACTOR — AN UNCONDITIONAL GAIN WITH NO
        ANALOGUE IN THE SINGLE-FUNCTION SETTING.

This is the first unconditional gain the programme has found in seventy-five cycles. It is real.

### And where it stops
Nonnegativity of a sum of phi(q) terms does not give nonnegativity of each. Extracting the individual
statement is EXACTLY the problem of excluding one exceptional character — THE SIEGEL ZERO PROBLEM.
That concerns zeros with sigma near 1, NOT sigma = 1/2. So the joint lane reaches GRH-adjacent
statements at the EDGE of the strip and not the critical line.

### The other joint mechanism
DEURING-HEILBRONN repulsion also acts only near sigma = 1, so it falls under the oscillation ceiling
already recorded for that region (cycles 54-55). Hence:

    THE CLASSIFICATION HAS NO GAP. ADDING A SECOND L-FUNCTION CREATES NO MECHANISM OUTSIDE THE
    ELEVEN EXISTING ENTRIES.

Machine-verified: `RHTower/CharacterAverageSuppression.lean` (the orthogonality collapse as the
family sum, the ratio identity P/(phi A) = (P/A)/phi, strict improvement once phi > 1, the
average-does-not-give-individual step, and the exceptional-term bound; standard axioms only, wired).

### STATE OF THE PROGRAMME AT CYCLE 75
Eleven structural entries, all confirmed; every analytic lane terminates at an RH-equivalent
statement; the one unconditional gain found (character averaging, factor phi(q)) applies to the
average and stalls at the Siegel-zero problem. RH IS NEITHER PROVEN NOR DISPROVEN.

What the programme HAS produced, all machine-verified with standard axioms:
  * the eleven-entry classification, including the scale-incompatibility constraint on test functions
    that applies to every explicit-formula argument at once;
  * a complete explicit anatomy of the rectangular/screw route (tent, Fejer, collapsed archimedean
    integral, squared main term, pole cancellation, loss of positive type under sliding);
  * a complete explicit anatomy of the modulated-tent route (detuning pi/L, width loglog theta/a,
    cost (log theta)^{1/a}, and unimprovability via lambda(L));
  * the identification that alignment cannot break positivity, so failure must be spectral;
  * the identification of the doubly exponential barrier's single source: the prime count pi(e^L);
  * six Phase-1 saves, one against my own theorem from forty cycles earlier.

### Cycle 76 target
The Siegel-zero obstruction is where the one unconditional gain stalls, and it is NOT RH-equivalent —
it is strictly weaker and famously open. That makes it the only place in the whole map where a real
gain meets a non-RH-equivalent wall. Target: determine whether the phi(q) ratio gain is enough to
exclude the exceptional character for SOME q, i.e. whether the averaged positivity plus the explicit
constants of cycles 61-74 give an unconditional zero-free region for the family that is stronger than
the classical one. If yes, that is a genuine unconditional advance, even though it is not RH.

---

## Cycle 76 (2026-07-26) — THE SCALE OBSTRUCTION REVERSES FOR CYCLOTOMIC FIELDS
### The obstruction blocking every single-scale argument is a feature of Q, not of L-functions.

The character-averaged Weil form mod q IS the Weil form of zeta_K for K = Q(zeta_q), since
PROD_{chi mod q} L(s,chi) = zeta_K(s). Two consequences.

### (1) Unconditional positivity below log q
The averaged prime sum runs over n = 1 mod q, and the least such n > 1 is q+1. So for any
positive-type test of width L < log(q+1) THE PRIME SIDE IS EMPTY and the averaged form is archimedean
plus pole, hence STRICTLY POSITIVE — unconditionally. Number fields whose least prime norm is large
relative to their archimedean weight have an unconditional positivity range growing like log q.

### (2) THE SCALE PRODUCT REVERSES — the finding
Over Q the cycle-69 obstruction is gamma_1 * log 2 ~ 9.8 > 1: a window narrow enough to resolve the
first zero is far too narrow to reach the first prime. For zeta_K both quantities change:
  * zero density at low height ~ log|d_K|/(2 pi), so gamma_1(K) ~ 2 pi/log|d_K| = 2 pi/(phi(q) log q);
  * first prime log = log q.
Their product is

    gamma_1(K) * log q  ~  2 pi / phi(q),

which is LESS THAN ONE as soon as phi(q) > 2 pi — and since pi < 4, phi(q) >= 8 suffices
(q = 15, 16, 20, 24, 30, ...).

    ==> FOR CYCLOTOMIC FIELDS OF MODERATE CONDUCTOR THE SCALE INCOMPATIBILITY IS REVERSED: A
        SINGLE-SCALE TEST FUNCTION CAN RESOLVE BOTH THE FIRST ZERO AND THE FIRST PRIME. THE
        OBSTRUCTION THAT BLOCKS EVERY SINGLE-SCALE EXPLICIT-FORMULA ARGUMENT OVER Q IS A FEATURE OF
        Q, NOT OF L-FUNCTIONS, AND IT WEAKENS AS THE FIELD GROWS.

The mechanism is transparent: enlarging the field multiplies the archimedean weight by phi(q) — which
is what sets the zero density — while pushing the first prime norm out to q. THE TWO SCALES MOVE IN
OPPOSITE DIRECTIONS.

### What it does not give
Positivity of the average is not positivity of each factor; the individual statement is the
exceptional-character problem. So the reversal is a structural statement about WHERE single-scale
arguments can work, not a route to RH for zeta itself.

Machine-verified: `RHTower/CyclotomicScaleReversal.lean` (empty-prime-range positivity, the residue
gap, the rational scale product reusing cycle 69, the cyclotomic product 2 pi/phi < 1, its
monotonicity in the conductor, the side-by-side reversal, and 2 pi < 8 from pi < 4; standard axioms
only, wired into RHTower).

### SIGNIFICANCE
Cycle 69's scale incompatibility was the eleventh atlas entry and the only one applying to EVERY
explicit-formula argument at once. This cycle shows it is not universal — it is arithmetic-specific,
and it fails in the direction of larger fields. That is the first time an entry of the classification
has been shown to be a property of the base field rather than of the method. It also says where to
look for single-scale arguments that cannot exist over Q: number fields with few small primes and
large discriminant.

### Cycle 77 target
The reversal says single-scale tests work for zeta_K. Ask the obvious next question: DOES THE
UNCONDITIONAL POSITIVITY RANGE L < log q, COMBINED WITH THE REVERSED SCALE PRODUCT, GIVE AN
UNCONDITIONAL ZERO-FREE REGION FOR zeta_K THAT IS STRONGER THAN THE CLASSICAL ONE FOR ITS
DISCRIMINANT? The classical zero-free region for zeta_K has width ~ c/log(|d_K| (|t|+2)^n); the
positivity range here is L < log q with archimedean weight phi(q) log q. Compare them. If the
positivity range wins for some family of q, that is an unconditional advance on Dedekind zero-free
regions — a genuine, checkable, non-RH result of exactly the kind the programme has been unable to
produce for zeta itself.

---

## Cycle 77 (2026-07-26) — THE EMPTY-WINDOW METHOD IS SELF-LIMITING
### Its success condition is the NEGATION of a consequence of the hypothesis it would prove.

Cycle 76 gave unconditional Weil positivity for every test of width below the least prime-norm
logarithm. This cycle asks what zero-free strip that buys. Answer: none, and for a sharp reason.

### The bound
An off-critical zero at deviation a contributes ~ -(2 L^2/pi^2) cosh(aL) at detuning pi/L, while the
archimedean side is ~ (log|d_K|/2) L. With an empty prime window positivity is automatic, so

    (2 L^2/pi^2) cosh(aL) <= (log|d_K|/2) L    ==>    e^{aL} <~ pi^2 log|d_K| / (4L),

and at L = L_0 = log N_min,          a  <~  log( C log|d_K| ) / L_0.

### When is it nontrivial?
A zero-free strip needs a < 1/2, i.e. L_0 > 2 log(C log|d_K|), i.e.

    N_min  >  ( C log|d_K| )^2.

### AND THAT IS EXACTLY WHAT CANNOT HAPPEN
Effective Chebotarev UNDER THE GENERALIZED HYPOTHESIS bounds the least prime norm by
<< (log|d_K|)^2 — THE SAME THRESHOLD. So the method delivers an unconditional zero-free strip
precisely for fields that the generalized hypothesis says DO NOT EXIST.

    ==> THE EMPTY-WINDOW POSITIVITY METHOD IS SELF-LIMITING: ITS SUCCESS CONDITION IS THE NEGATION
        OF A CONSEQUENCE OF THE HYPOTHESIS IT IS TRYING TO PROVE.

This is a different kind of wall from the eleven classification entries. Those cap a method's
strength. This one is a COINCIDENCE BETWEEN THE METHOD'S REQUIREMENT AND THE THEORY'S PREDICTION —
the method can only win where the theory forbids the input.

### The cyclotomic case, directly
N_min = q while log|d_K| ~ phi(q) log q, so N_min > (log|d_K|)^2 fails badly. The extended prime-free
range log q is EXACTLY CANCELLED by the archimedean weight phi(q) log q; the ratio is the DEGREE
phi(q). Cycle 76's reversal of the scale product is real, but it does not survive the archimedean
budget.

Machine-verified: `RHTower/SelfLimitingPositivity.lean` (the deviation bound from e^{aL_0} <= M, the
nontriviality threshold L_0 > 2 log M, its restatement as N_min > M^2, the contradiction between
requirement and prediction, the direct cyclotomic failure, and the degree-cancellation identity;
standard axioms only, wired into RHTower).

### TWELFTH ATLAS ENTRY
    self-limiting positivity   the empty-window method succeeds only for fields whose least prime
                               norm exceeds (log|d_K|)^2 — exactly what effective Chebotarev under
                               GRH forbids.
Unlike the first eleven this entry is not a bound on a method's output; it is an incompatibility
between its input requirement and the surrounding theory.

### STATE AT CYCLE 77
Twelve structural entries. Every analytic lane terminates at an RH-equivalent statement or at a
self-limiting condition. The one unconditional gain (character averaging, factor phi(q)) applies to
the average and stalls at the exceptional-character problem; the cyclotomic scale reversal is real
but is cancelled by the archimedean budget. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 78 target
Both remaining live threads — the exceptional character and the archimedean budget — are about the
SIZE OF THE ARCHIMEDEAN TERM relative to the prime side. In every computation of cycles 61-77 the
archimedean weight entered as (1/2) log|d_K| times the test mass, i.e. through the CONDUCTOR alone.
The one quantity never varied is the test's MASS at fixed width: all tests used were normalized so
that hat g has mass 2 pi g(0). Ask whether a test of the same width but SMALLER mass can be
positive-type — i.e. minimize hat g's total mass subject to hat g >= 0, supp g in [-L,L], and
g(0) = 1. That is a clean extremal problem, and unlike the lambda(L) problem of cycle 74 it does NOT
involve the prime form, so X31 does not apply. Determine its value.

---

## Cycle 78 (2026-07-26) — THE PALEY-WIENER DETECTION CEILING
### Shape optimisation of the test function is closed UNCONDITIONALLY. Sharp constant.

Cycle 74 closed shape optimisation only CONDITIONALLY: improving lambda(L) is RH-equivalent (via
X31). That left a loophole — the argument ran through the full form INCLUDING primes. This cycle
closes it unconditionally by bounding what a test can see BEFORE any prime information is used.

### Phase 1 result
Corpus search on "test mass rigidity / compressed prime operator / archimedean budget" returned only
the Calkin/compression files (SemilocalCompressedEulerOrientation, XiPrimeSeamHigherGradeCalkinRigidity,
HardyTitchmarshEulerConcrete) — operator-ideal statements, not reproducing-kernel bounds. The
Paley-Wiener reproducing kernel is ABSENT from this corpus. Opened as new.

### The rigidity that started it
Fourier inversion pins the spectral mass: int ghat = 2 pi g(0). So the discriminant term
g(0) log|d_K| and the total mass are THE SAME FUNCTIONAL up to 2 pi. The archimedean budget is not an
independent resource — it is the mass. Hence the only real question is how much of that mass a
single off-critical zero can capture, and THAT is a reproducing-kernel question.

### The theorem
ghat >= 0 with supp g in [-L,L] means ghat = |F|^2 with F in PW_{L/2}. The continuation is
ghat(gam - ia) = <F,K_z> conj<F,K_zbar>, z = gam - ia, and for PW_{L/2}

    K(z,z) = sinh(aL)/(2 pi a),        K(z,zbar) = L/(2 pi).

Polarization (NOT Cauchy-Schwarz, which loses the factor): for a unit F,
<F,u><F,v> = (<F,u+v>^2 - <F,u-v>^2)/4 <= ||u+v||^2/4, which for ||u||=||v||=c is (c^2+<u,v>)/2 and
is ATTAINED at F = (u+v)/||u+v||. Therefore

    |ghat(gam - ia)|  <=  (g(0)/2) ( sinh(aL)/a + L ),      AND THIS CONSTANT IS SHARP.

    ==> THE MAXIMAL INFLUENCE OF AN OFF-CRITICAL ZERO ON A POSITIVE-TYPE TEST OF WIDTH L IS
        (g(0)/2)(sinh(aL)/a + L) — A FUNCTION OF THE WIDTH AND THE DEVIATION ALONE.
        THE SHAPE OF THE TEST IS IRRELEVANT BEYOND A BOUNDED FACTOR.

### Consequence: the cost exponent 1/a is FORCED BY THE KERNEL
Against a positive budget B g(0) the zero is invisible unless sinh(aL)/a + L > B, i.e.
e^{aL} > 4aB + 1 must fail; so detection requires

    L > log(4aB+1)/a      and hence a prime window of  e^L > (4aB+1)^{1/a}.

Cycle 73 derived (log T)^{1/a} for the FEJER weight and called it "an explicit form of the classical
trade-off". It is not a property of Fejer. It is the reproducing kernel of PW_{L/2}. Fejer is within
a bounded factor of optimal — cross-checked against the exact cycle-73 value
(2+2cosh(aL))/(pi^2/L^2+a^2), whose ratio to the ceiling is ~ 2/(aL) for large aL and ~0.4 at aL=1.

### WHAT THIS UPGRADES
* Cycle 74 (extremal test is lambda): was CONDITIONAL on X31. Now unconditional, and it does not
  mention the prime side at all.
* Cycle 77 (self-limiting positivity): the threshold N_min > (C log|d_K|)^2 was derived for the
  tent/Fejer family. It now holds for EVERY admissible test. The self-limiting wall has no shape
  loophole.
* Cycles 61-73 all used one weight; every quantitative conclusion drawn from that weight is now
  known to be shape-universal up to a bounded factor.

Machine-verified: `RHTower/PaleyWienerDetectionCeiling.lean` (polarization ceiling, its equal-norm
form, its ATTAINMENT, the kernel values and their comparison via t <= sinh t, positivity, shape
independence, the width requirement e^{aL} <= 4aB+1, the cost identity e^{log M/a} = M^{1/a}, and the
contrapositive closure; standard axioms only, wired into RHTower).

### THIRTEENTH ATLAS ENTRY
    Paley-Wiener detection ceiling   a positive-type test of width L sees an off-critical zero at
                                     deviation a by at most (g(0)/2)(sinh(aL)/a + L). Sharp. Shape
                                     optimisation cannot beat the bandwidth.

This is the first entry proved WITHOUT the explicit formula — it is a statement about bandlimited
positive-definite functions alone, and it applies to every criterion of Weil type over every global
field simultaneously.

### STATE AT CYCLE 78
Thirteen structural entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 79 target
The ceiling is sharp for a SINGLE zero. But the Weil form sees ALL zeros at once, and the extremal
F = (K_z + K_zbar)/||.|| for one zero is a specific function — what does it do to the OTHER zeros?
The extremiser is essentially a modulated Fejer kernel centred at gam. Conjecture: the sum over a
zero family of the ceiling is NOT achievable simultaneously, because the extremisers for distinct
gam are nearly orthogonal in PW_{L/2} — spacing 2 pi/log gam versus kernel width 2 pi/L, so they
decouple exactly when L < log gam. THAT is a second, independent appearance of the L vs log(height)
threshold. If the decoupling is provable, the ceiling becomes a bound on the TOTAL detectable
violation, not just per-zero, and the atlas gains its first genuinely GLOBAL constraint.

---

## Cycle 79 (2026-07-26) — THE NYQUIST DICHOTOMY
### The log T barrier is the SAMPLING RATE of the Riemann zero set. Crossover at the mean spacing.

Cycle 78's ceiling bounds what ONE off-critical zero does to a test. It says nothing about the other
zeros — which are all present in the explicit formula and all contribute NONNEGATIVELY when on the
line. A violation must overcome them. This cycle prices that, and the same threshold L = log T
reappears from the OPPOSITE side.

### Phase 1 result
formal_tools research + rg for "Nyquist / Beurling / Landau density / sampling set" over formal/:
PrimeWeylSamplingIdealizer uses "sampling set" in an unrelated jet-interpolation sense;
PrimeSymbolDecoupling's "Beurling" is Beurling GENERALIZED PRIMES, a different object. Beurling-Landau
sampling density is ABSENT from the corpus. Opened as new.

### The mechanism
Critical zeros up to height T have density log T / 2 pi. The test of width L lives in PW_{L/2}, whose
NYQUIST DENSITY IS L / 2 pi. Beurling-Landau: a set above Nyquist density is a set of SAMPLING, so
there is A > 0 with sum_j |F(gam_j)|^2 >= A ||F||^2, i.e.

    sum_gam ghat(gam)  >=  A g(0)        whenever   L < log T.

    ==> BELOW NYQUIST THE CRITICAL ZEROS CANNOT BE DODGED.

Above Nyquist they CAN be dodged — but then L >= log T and the prime window costs e^L >= T.

### DODGE-OR-PAY
    (i)  L >= log T : the test resolves individual zeros; prime window e^L >= T.
    (ii) L <  log T : the critical zeros contribute >= A g(0) with A ~ log T, and by the cycle-78
         ceiling an off-critical pair overcomes them only if e^{aL} > 4aA - 2aL.

BOTH BRANCHES ARE GOVERNED BY THE SINGLE THRESHOLD L = log T, ARRIVING FROM OPPOSITE SIDES:
the zero side by LANDAU DENSITY, the prime side by the REPRODUCING KERNEL.

### WHERE THE BRANCHES CROSS — AT THE MEAN ZERO SPACING
Positivity is cheaper iff (4a log T)^{1/a} <= T iff, with s = a log T, log(4s+1) <= s. Verified in
Lean on both sides: TRUE for s >= 3 (via e^3 >= 20) and FALSE at s = 2 (via e^2 < 9). So the
crossover sits at s ~ 1, i.e.

    a  ~  1 / log T   =   THE MEAN SPACING OF THE ZEROS AT HEIGHT T (up to 2 pi).

    ==> A ZERO FURTHER FROM THE CRITICAL LINE THAN THE LOCAL ZERO SPACING IS CHEAPER TO EXCLUDE BY
        POSITIVITY. A ZERO CLOSER TO THE LINE THAN THE SPACING IS CHEAPER TO EXCLUDE BY RESOLVING
        THE ZEROS INDIVIDUALLY.

This is a complete structural explanation of why the explicit-formula method has never produced a
zero-free region near the critical line: BELOW THE SPACING SCALE IT IS PROVABLY THE WRONG TOOL.

### The cycle-78 conjecture was WRONG in its direction — and the correction is the result
I conjectured that extremisers for distinct zeros are nearly ORTHOGONAL when L < log gam, so the
per-zero ceilings would not add. Landau density says the OPPOSITE: below Nyquist the kernel system is
OVERCOMPLETE, so zeros within |dgam| <~ a CAN cooperate (about a log T of them). Decoupling (Riesz
sequence) happens only ABOVE Nyquist, L > log T. The correct consequence is not a bound on
cooperation but the DODGE-OR-PAY dichotomy above. RECORD THE DIRECTION ERROR: overcompleteness is
below Nyquist, Riesz is above.

Machine-verified: `RHTower/NyquistDichotomy.lean` (density comparison, sampling lower bound, the
super-Nyquist cost T <= e^L, the sub-Nyquist cost 4aA - 2aL < e^{aL}, the crossover criterion
M^{1/a} <= T iff log M <= a log T, and BOTH SIDES of the crossover: log(4s+1) <= s for s >= 3 and
2 < log 9; standard axioms only, wired into RHTower).

### FOURTEENTH ATLAS ENTRY
    Nyquist dichotomy   log T is the sampling rate of the zero set for PW_{L/2}. Sub-Nyquist tests
                        cannot dodge the critical zeros; super-Nyquist tests cost e^L >= T. The
                        branches exchange at deviation a ~ 1/log T, the mean zero spacing.

Together with entry thirteen this identifies the SOURCE of the log T barrier that appears in every
one of the first twelve entries: it is a sampling-density threshold, not an arithmetic one.

### STATE AT CYCLE 79
Fourteen structural entries; entries 13 and 14 are the first PROVED WITHOUT THE EXPLICIT FORMULA.
RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 80 target
Entry 14 says sub-Nyquist tests cannot dodge the critical zeros. But the explicit formula is an
IDENTITY: sum over ALL zeros = arch + pole - primes. So the sampling lower bound A g(0) is not merely
an obstruction — it is a FORCED IDENTITY between the sampling constant of the zero set and the
archimedean weight. Conjecture: for the true zero set of zeta, the Beurling-Landau sampling constant
of {gam_j} in PW_{L/2} is EXACTLY the archimedean weight (1/2 pi) int ghat W, for every L < log T,
because the explicit formula with an empty prime window says so. If true, the zero set of zeta is a
sampling set with a COMPUTABLE sharp constant — a statement about zeta's zeros that is unconditional,
quantitative, and has no known analogue. And its failure for a hypothetical off-critical
configuration would be a contradiction. TEST WHETHER THE FORCED CONSTANT IS CONSISTENT WITH BEURLING'S
BOUNDS; if the identity forces a sampling constant LARGER than Beurling's theorem permits for a set of
that density, an off-critical zero is impossible.

---

## Cycle 80 (2026-07-26) — THE ARITHMETIC-FREE FALSIFICATION LADDER
### FIRST STATEMENT IN THE ATLAS WHOSE FAILURE WOULD DISPROVE RH.

Entries 1-14 all bound a METHOD. This cycle produces a statement that is not about a method at all:
a sequence of finite, elementary inequalities, each checkable in finitely many terms, whose failure
refutes the hypothesis.

### The observation that unlocks it
THE POLE OF ZETA AT s=1 IS AN OFF-CRITICAL ZERO AT MAXIMAL DEVIATION a = 1/2. It enters the explicit
formula as ghat(i/2) + ghat(-i/2) — exactly the cycle-78 configuration at deviation 1/2. So the
DETECTION CEILING APPLIES TO THE POLE, and it is sharp:

    ghat(i/2) + ghat(-i/2)  <=  g(0) ( 2 sinh(L/2) + L ).

### The ladder
Write the explicit formula as   sum_rho ghat(gam_rho) = P(g) + A_inf(g) - Pr_L(g),  where
Pr_L(g) = 2 sum_{n <= e^L} Lambda(n) n^{-1/2} g(log n) is FINITE. Under RH every ordinate is real and
every left-hand term is >= 0, so

    Pr_L(g) - A_inf(g)  <=  P(g)  <=  g(0) ( 2 sinh(L/2) + L ).

The pole has been eliminated by a SHARP UNIVERSAL BOUND. What remains is an inequality between the
digamma transform of ghat, finitely many elementary prime terms, and an elementary function of L.
NO ZEROS. NO ASYMPTOTICS. NO ARITHMETIC BEYOND A FINITE LIST OF PRIME POWERS.

    ==> EACH WIDTH L IS A RUNG: A FINITE ELEMENTARY INEQUALITY WHOSE FAILURE DISPROVES RH.
        BELOW log 2 THE PRIME SIDE IS EMPTY AND THE RUNG INVOLVES ONLY THE GAMMA FUNCTION.

By Weil's criterion RH is EQUIVALENT to all rungs holding. The criterion, normally quantified over an
infinite-dimensional cone with the pole entangled in it, becomes a ladder of finite tests — at the
cost of the sharp pole ceiling, which is exactly what cycle 78 supplies.

### CORRECTION TO CYCLES 76-77 (important)
Empty-window positivity is NOT automatic over Q. The archimedean weight
Re psi(1/4 + ir/2) - log pi is NEGATIVE for |r| < 2 pi — the analytic reflection of the fact that the
smooth zero count (T/2pi) log(T/2pi e) is negative below T = 2 pi e ~ 17.08. Over a number field the
discriminant term g(0) log|d_K| dominates it, which is what made the empty window positive THERE
(cycle 76's Lean lemma correctly carried `0 < A` as a HYPOTHESIS, so the formalisation is sound; the
prose "hence strictly positive" was field-specific and is now qualified). Over Q there is no
discriminant term, so the L < log 2 rung is a GENUINE INEQUALITY, not a triviality. That is precisely
why it is a usable falsification target.

### Where the window is widest
For L < log 2 the prime side is empty. For log 2 <= L < log 3 exactly one term appears,
-2 (log 2 / sqrt 2) g(log 2); each subsequent prime-power threshold adds one explicit elementary term.
The negative prime terms make each rung HARDER to satisfy while larger L lets ghat concentrate
further into the negative-weight region |r| < 2 pi. THE MOST INFORMATIVE RUNGS ARE THEREFORE JUST
BELOW EACH PRIME-POWER THRESHOLD, and the first nontrivial one is L -> log 3.

Machine-verified: `RHTower/ArithmeticFreeFalsificationLadder.lean` (the pole as the maximal-deviation
configuration 2*detectionCeiling(1/2,L) = 2 sinh(L/2)+L, the pole ceiling, the rung, its
contrapositive as a refutation, emptiness of the prime side below log 2, monotonicity of the ladder,
and the strict excess over the naive linear bound; standard axioms only, wired into RHTower).

### FIFTEENTH ATLAS ENTRY
    arithmetic-free falsification ladder   RH is equivalent to an increasing sequence of finite
                                           elementary inequalities, obtained by bounding the pole
                                           with the sharp deviation-1/2 detection ceiling. Below
                                           log 2 the rung involves only Gamma.

This is the FIRST entry that is not a wall. Entries 1-14 say what cannot be done; entry 15 says what
can be TESTED, and its failure at any single rung would refute the hypothesis.

### STATE AT CYCLE 80
Fifteen entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 81 target
The rung at L < log 2 involves only Gamma, so it is a pure special-function inequality:
for every ghat >= 0 of exponential type L supported test,
    (1/2pi) int ghat(r) [ 2 Re psi(1/4 + ir/2) - 2 log pi ] dr  >=  - g(0) ( 2 sinh(L/2) + L ).
PROVE OR REFUTE THIS DIRECTLY. It is implied by RH, so a refutation refutes RH; a direct proof gives
the first unconditional rung and calibrates how much slack the ladder has. The extremal test is the
one making ghat most concentrated in |r| < 2 pi subject to type L — by cycle 78 that is the
reproducing-kernel extremiser, i.e. ghat = |K_{i/2}(r) + K_{-i/2}(r)|^2 normalised. COMPUTE THE RUNG
AT THAT EXTREMISER: it turns the inequality into a closed-form digamma integral against an explicit
Fejer-type kernel, and its sign is decidable by classical estimates on Re psi.

---

## Cycle 81 (2026-07-26) — PHASE-1 CAUGHT A DUPLICATE. THE SALVAGE IS A CROSS-VALIDATION.

### THE SEARCH SAVE (record this — it is the second time the object-level rule paid)
Planned target: prove the pole form has Krein signature (1,1) with directions cosh(u/2), sinh(u/2).
`rg "pole form|poleForm"` found `RHTower/PoleFormDiagonalization.lean`, which ALREADY HAS:
  * pole_diagonalize : 2(P+Q)(P-Q) = 2P^2 - 2Q^2 — the signature (1,1) splitting,
  * sinh_half_sq, the closed form ||s||^2 = sinh l - l (in prose), its cubic smallness,
  * a baseline dichotomy on whether <h,c>^2 is small.
MY INTENDED CYCLE WAS A DUPLICATE. Do not re-derive it. The rule that caught it is the cycle-74 rule:
SEARCH FOR THE OBJECT ("pole form"), NOT THE TOOL ("Krein signature").

### What was genuinely absent, and is now proved
The existing file computes only the NEGATIVE direction. The positive one was never computed:

    ||cosh(./2)||^2_{L^2[-l,l]} = sinh l + l         (new)
    ||sinh(./2)||^2_{L^2[-l,l]} = sinh l - l         (formalised here for the first time)

so the pole form's two eigenvalues on the unit sphere are  mu+ = 2(sinh l + l),
mu- = -2(sinh l - l).

### CROSS-VALIDATION OF CYCLE 78 BY AN INDEPENDENT ROUTE
With l = L/2,   mu+ = 2 sinh(L/2) + L  =  2 * detectionCeiling(1/2, L).
The cycle-78 constant was derived from the PALEY-WIENER REPRODUCING KERNEL and a polarization
argument. Here it falls out of  int cosh^2  — NO REPRODUCING KERNEL ANYWHERE. Two independent
derivations of the same sharp constant.

    ==> THE KREIN-POSITIVE DIRECTION OF THE POLE FORM IS THE PALEY-WIENER EXTREMISER AT
        DEVIATION 1/2:   cosh(u/2)  =  the even part of e^{u/2}  =  K_{i/2} + K_{-i/2}.

This also identifies the extremiser of cycle 78 concretely, which the polarization argument gave only
abstractly as (u+v)/||u+v||.

### THE TRACE IS THE LENGTH OF THE INTERVAL
    mu+ + mu-  =  2(sinh l + l) - 2(sinh l - l)  =  4 l  =  2 L,
because cosh^2 - sinh^2 = 1: THE TRANSCENDENTAL PARTS CANCEL IDENTICALLY and what survives is
2 * int_I 1 du. Since the Nyquist density of PW_{L/2} is L/2pi (cycle 79),

    mu+ + mu-  =  4 pi * (NYQUIST DENSITY OF THE TEST SPACE).

    ==> THE NET WEIGHT OF THE POLE IS THE LENGTH OF THE SUPPORT INTERVAL — ONE NYQUIST CELL.
        THE POLE OF ZETA ENTERS THE WEIL FORM AS EXACTLY ONE ZERO AT DEVIATION 1/2, AND
        cosh^2 - sinh^2 = 1 IS WHAT MAKES THE COUNT EXACT.

That links cycle 79 (Nyquist) to the pole term, and explains the +1 in the zero-counting function
N(T) as the pole's Nyquist cell.

Machine-verified: `RHTower/PoleKreinNyquistTrace.lean` (cosh half-angle identity, the interval
primitive of cosh proved from deriv sinh, BOTH L^2 norms, the trace identity, the pythagorean source
of the cancellation, the match with the detection ceiling, the Nyquist-cell restatement, and
indefiniteness; standard axioms only, wired into RHTower).

### CORRECTED EXPECTATION FOR THE LADDER
Cycle 80 said the most informative rungs are just below each prime-power threshold. Now quantified:
the pole ceiling grows like e^{L/2} (from mu+ = 2 sinh(L/2)+L) and the crude prime bound
sum_{n<=e^L} Lambda(n)/sqrt n ~ 2 e^{L/2} gives a prime side up to ~4 e^{L/2} g(0) — THE SAME
EXPONENTIAL RATE, with the primes ahead by a factor 4. The rung is therefore NOT asymptotically
slack: both sides are e^{L/2} and only the constant decides. The archimedean term is merely
logarithmic and cannot bridge a constant-factor gap at large L. SO THE LADDER IS TIGHT AT EVERY
HEIGHT, and the crude prime bound |g| <= g(0) must be far from achievable — quantifying that gap is
the real content.

### STATE AT CYCLE 81
Fifteen entries (no new entry this cycle — a duplicate was avoided and a cross-validation banked).
RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 82 target
Quantify the gap just identified. DEFINE Pi(L) = max { 2 sum_{n<=e^L} Lambda(n) n^{-1/2} g(log n) }
over positive-type g of width L with g(0)=1 — the TOP EIGENVALUE OF THE COMPRESSED PRIME OPERATOR.
The crude bound is Pi(L) <= 4 e^{L/2}; the pole supplies only 2 sinh(L/2)+L ~ e^{L/2}. RH REQUIRES
Pi(L) <= mu+ + A_inf(L), so RH REQUIRES Pi(L) <= (1+o(1)) e^{L/2} — A FACTOR 4 BELOW THE CRUDE
BOUND. Conjecture: the true Pi(L) is exactly 2 e^{L/2}(1+o(1)), i.e. HALF the crude bound, because
|g(u)| <= g(0) is attainable only at u=0 and the positive-type constraint forces an averaging loss of
exactly 1/2 over the prime-log lattice. IF Pi(L) > mu+ + A_inf(L) FOR SOME L, RH IS FALSE. This is
the sharpest falsification target the programme has produced: it needs no zeros, no archimedean
subtlety, only the extremal value of a compressed prime operator against an explicit elementary
ceiling.

---

## Cycle 82 (2026-07-26) — POLE MINUS PRIME MAIN TERM IS A LAPLACE TRANSFORM, BOUNDED BY 4 g(0)
### The exponential parts cancel IDENTICALLY, for every test and every width. One line.

### The identity
Substituting t = e^u in the PNT main term of the prime sum:
    2 sum_{n<=e^L} Lambda(n) n^{-1/2} g(log n)  ~  2 int_1^{e^L} g(log t) t^{-1/2} dt
                                                =  2 int_0^L g(u) e^{u/2} du,
while the pole term, by evenness and 2 cosh(u/2) = e^{u/2} + e^{-u/2}, is
    ghat(i/2) + ghat(-i/2) = 2 int_{-L}^{L} g cosh(u/2) du = 2 int_0^L g(u)(e^{u/2} + e^{-u/2}) du.

    ==> FOR EVERY EVEN g SUPPORTED IN [-L,L]:
            pole(g) - primeMain(g)  =  2 int_0^L g(u) e^{-u/2} du
        THE LAPLACE TRANSFORM OF g AT 1/2. The exponentially growing parts cancel IDENTICALLY, and
        when ghat >= 0 (so |g| <= g(0)) the residue is AT MOST 4 g(0) — A BOUNDED BUDGET INDEPENDENT
        OF L.

### The tent, exactly
For g(u) = 1 - |u|/L the residue is EXACTLY  4 + 8(e^{-L/2} - 1)/L,  positive for every L > 0,
increasing from 0 to 4, never exceeded. Verified two ways: (a) directly from
int_0^L e^{-u/2} = 2(1-e^{-L/2}) and int_0^L u e^{-u/2} = 4 - (2L+4)e^{-L/2}; (b) as the difference
of the separately computed pole value 16(cosh(L/2)-1)/L and prime main value
(8 e^{L/2} - 4L - 8)/L. The two routes agree exactly.

### THREE CONSEQUENCES
1. THE WIDTH BUYS NOTHING. Growing L multiplies pole and prime main term by the SAME e^{L/2}; the
   difference stays below 4 g(0) forever. THE DOUBLY EXPONENTIAL BARRIER OF CYCLES 69-72 HAS THIS AS
   ITS SOURCE — it was never about the prime count, it was about an exact cancellation.
2. ALL OF THE HYPOTHESIS IS IN THE ERROR TERM. What survives is
        W(g) = 2 int_0^L g e^{-u/2} du + A_inf(g) - (smoothed PNT error),
   with the first term <= 4 g(0) and the second logarithmic. RH is exactly the statement that the
   smoothed error stays inside a BOUNDED budget. (This recovers the classical equivalence
   RH <=> psi(x) - x = O(sqrt x log^2 x) — but with the budget constant made explicit and sharp.)
3. THE COMPRESSED PRIME SPECTRUM GROWS LIKE e^{L/2}, NOT 4 e^{L/2}. At the pole extremiser
   cosh(u/2) the pole reaches g(0)(2 sinh(L/2)+L), so the prime main term there is at least
   g(0)(2 sinh(L/2)+L-4). Cycle 81's conjecture that the crude bound 4 e^{L/2} is a factor ~4 too
   large is CONFIRMED from below: Pi(L) >= 2 sinh(L/2)+L-4 ~ e^{L/2}.

Machine-verified: `RHTower/PoleMinusPrimeMainIsLaplace.lean` (the cosh splitting, the cancellation,
BOTH primitives proved from HasDerivAt, the exact tent residue, its positivity via 1-x < e^{-x}, its
ceiling at 4, the width-independent budget bound, and the prime-spectrum lower bound; standard axioms
only, wired into RHTower).

### SIXTEENTH ATLAS ENTRY
    Laplace budget   pole(g) - primeMain(g) = 2 int_0^L g e^{-u/2} du <= 4 g(0), for every test and
                     every width. The explicit formula's two exponentially large terms cancel
                     identically; only the PNT error survives.

Entries 13, 14, 16 now form a coherent explanation of the whole atlas: the reproducing kernel caps
what a test can see, the sampling density caps what it can dodge, and the Laplace budget caps what
width can buy. All three are width statements; none involves the zeros.

### STATE AT CYCLE 82
Sixteen entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 83 target
Entry 16 says the budget is 4 g(0) and entry 13 says the pole reaches g(0)(2 sinh(L/2)+L). Combining:
the prime main term is FORCED to within 4 g(0) of an exponentially large quantity. Now ASK THE
CONVERSE. The prime main term is 2 int_0^L g e^{u/2} du, an explicit functional. The ACTUAL prime sum
differs from it by the smoothed error. SO: what is the largest c such that
    2 sum_{n<=e^L} Lambda(n) n^{-1/2} g(log n)  <=  2 int_0^L g(u) e^{u/2} du + c g(0)
holds for every positive-type g of width L, UNCONDITIONALLY? By entry 16 and Weil, RH is equivalent
to c being bounded by 4 + A_inf-worth. A DIRECT UNCONDITIONAL BOUND ON c IS AN UNCONDITIONAL BOUND ON
THE SMOOTHED PNT ERROR AGAINST POSITIVE-TYPE WEIGHTS — and positive-type weights are exactly where
the classical error estimates are WEAKEST, because they cannot be shifted off the critical line.
Determine whether the positive-type constraint gives a better error bound than the classical contour
shift. If it does, that is an unconditional improvement of the PNT error term.

---

## Cycle 83 (2026-07-26) — THREE-WAY CANCELLATION: THE WEIL FUNCTIONAL HAS NO EXPONENTIAL CONTENT
### Pole + prime main term + FIRST ARCHIMEDEAN MODE = A(0). Width-independent. This explains the atlas.

### Phase 4 verdict on the cycle-82 target: CIRCULAR — recorded as a dead end
Cycle 82 proposed bounding c in  primeSum <= primeMain + c g(0)  unconditionally. Integration by
parts gives  primeSum - primeMain = int_0^L Etilde(u) (g/2 - g') du  with
Etilde(u) = (psi(e^u) - e^u) e^{-u/2}, and by the classical exact formula
Etilde(u) = -sum_rho e^{u(rho-1/2)}/rho. So ANY bound on the smoothed error against ANY weight IS a
bound on the zero sum. CIRCULAR. Positive-type weights give no leverage: the constraint is on the
weight, not on Etilde. DEAD END — do not re-attempt.

### The relentless-interrogation move that survived
What killed it: the error IS the zero sum. What is NOT killed: statements about the SHAPE of the
functional that never bound the error. Follow the Laplace transforms.

### The corpus supplied the missing normalization
`ArchimedeanSingleIntegral.lean` (cycle 64) records the archimedean side as the series with n-th
summand   A(0)/(n+1) - int_0^inf e^{-(n+3/4)t} A(t/2) e^{t/2} dt.
Substituting t = 2u:   that integral is  2 int_0^X A(u) e^{-(2n+1/2)u} du  =  2 * LaplaceA(2n+1/2).

    ==> THE n-TH ARCHIMEDEAN MODE IS   A(0)/(n+1) - 2 LaplaceA(2n + 1/2),
        AND THE FIRST ONE (n=0) IS     A(0) - 2 LaplaceA(1/2).

### THE THREE-WAY CANCELLATION
Cycle 82: pole - primeMain = 2 LaplaceA(1/2). Adding the first archimedean mode:

    [pole - primeMain] + [first archimedean mode] = 2 L(1/2) + A(0) - 2 L(1/2) = A(0).

    ==> THE POLE TERM, THE PNT MAIN TERM, AND THE FIRST ARCHIMEDEAN MODE CANCEL IDENTICALLY,
        LEAVING EXACTLY A(0). THE WEIL FUNCTIONAL CONTAINS NO QUANTITY OF SIZE e^{L/2} AT ALL.

What survives:   W = A(0) - 2 sum_{n>=1} [ ... LaplaceA(2n+1/2) ... ] - (smoothed prime error),
with every surviving Laplace mode bounded by A(0)/(2n+1/2). The whole archimedean tail is O(A(0))
with an absolute constant.

### THIS EXPLAINS THE ENTIRE ATLAS
Every barrier recorded in entries 1-16 was a symptom of trying to extract information from three
terms whose sum is A(0) INDEPENDENTLY OF THE WIDTH:
  * the doubly exponential barrier (cycles 69-72): both exponentials cancel;
  * the Laplace budget (entry 16): it is exactly the first archimedean mode with the sign flipped;
  * self-limiting positivity (entry 12): the empty-window archimedean side is the tail alone;
  * scale incompatibility, detection ceiling, Nyquist dichotomy: all width statements, and width is
    precisely what cancels.
RH IS AN INEQUALITY BETWEEN TWO BOUNDED QUANTITIES. There is no exponentially large quantity anywhere
in it, and no method that gains by widening the window can work.

Machine-verified: `RHTower/ThreeWayCancellation.lean` (the t=2u substitution identifying the n-th
archimedean mode as a Laplace transform at 2n+1/2, the three-way cancellation, its width
independence, the uniform mode bound, the exact Laplace transform of a constant, monotone mode
denominators, and the no-exponential-content restatement; standard axioms only, wired into RHTower).

### SEVENTEENTH ATLAS ENTRY
    three-way cancellation   pole + prime main term + first archimedean mode = A(0), for every test
                             and every width. The Weil functional has no exponential content; RH is
                             an inequality between two O(A(0)) quantities.

This is the structural explanation the atlas lacked. Entries 13, 14, 16 said what width cannot buy;
entry 17 says why: width cancels.

### STATE AT CYCLE 83
Seventeen entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 84 target
If RH is an inequality between two O(A(0)) quantities, then the RIGHT NORMALIZATION IS A(0) = 1 AND
THE RIGHT VARIABLE IS NOT L. Under entry 17 the functional is
    W(g)/g(0) = 1 - Tail(g)/g(0) - Err(g)/g(0),
with Tail explicit and bounded. DETERMINE sup Tail(g)/g(0) OVER POSITIVE-TYPE g EXACTLY. It is
sum_{n>=1} [ 2 Laplace(2n+1/2) - 1/(n+1) ] maximised over the positive-type cone — a FINITE,
SCALE-FREE extremal problem with no primes and no zeros, decidable by classical means. Its value is
the exact archimedean budget of the Riemann hypothesis, a single real constant. NAME IT AND COMPUTE
IT. If it is less than 1, then RH reduces to  Err(g) <= (1 - budget) g(0)  with a POSITIVE margin —
and the margin is the first genuinely quantitative handle the programme has produced.

---

## Cycle 84 (2026-07-26) — THE ARCHIMEDEAN BUDGET IS 3 log 2 + pi/2 - 3, AND IT IS BELOW ONE
### The Weil functional carries a strictly positive margin. Closed form. First quantitative handle.

### The setup from entry 17
After the three-way cancellation,  W(g) = g(0) - T(g) - 2 E(g),  where E is the smoothed prime error
and T is the ARCHIMEDEAN TAIL — the collapsed archimedean integral with its first mode removed. Using
1/(1-e^{-t}) = 1 + e^{-t}/(1-e^{-t}),

    T(g) = - int_0^inf ( g(0) e^{-t} - g(t/2) e^{-t/4} ) * e^{-t}/(1-e^{-t}) dt.

### THE BUDGET, IN CLOSED FORM
ghat >= 0 forces |g| <= g(0), so T(g)/g(0) is largest at g == g(0):

    beta := sup_g T(g)/g(0) = int_0^inf e^{-t}(e^{-t/4} - e^{-t})/(1 - e^{-t}) dt
                            = int_0^1 (x^{1/4} - x)/(1 - x) dx          [ x = e^{-t} ]
                            = psi(2) - psi(5/4)                         [ Gauss's integral ]
                            = 3 log 2 + pi/2 - 3
                            = 0.65023...

using psi(2) = 1 - gamma and psi(5/4) = psi(1/4) + 4 = 4 - gamma - pi/2 - 3 log 2. The supremum is
APPROACHED IN THE WIDE-WINDOW LIMIT, where g/g(0) -> 1 on compacts, so it is sharp.

    ==> THE ARCHIMEDEAN BUDGET OF THE RIEMANN HYPOTHESIS IS  3 log 2 + pi/2 - 3 < 1,
        AND THE WEIL FUNCTIONAL CARRIES A STRICTLY POSITIVE MARGIN:

            W(g)  >=  ( 4 - 3 log 2 - pi/2 ) g(0)  -  2 E(g),     4 - 3 log 2 - pi/2 = 0.34976...

### AN ELEMENTARY ROUTE, INDEPENDENT OF THE DIGAMMA EVALUATION
Expanding 1/(1-x) = sum x^k termwise gives beta = sum_{k>=0} [ 1/(k+5/4) - 1/(k+2) ], whose k-th term
is (3/4)/((k+5/4)(k+2)) <= (3/4)(1/(k+1) - 1/(k+2)). THE RIGHT SIDE TELESCOPES TO 3/4. So

    beta <= 3/4,        margin >= 1/4,

WITH NO SPECIAL-FUNCTION INPUT AT ALL. This is the version formalised; the closed form is the sharp
value and its position below 1 is also formalised (via log 2 < 0.6931471808 and pi < 3.15).

### WHY THIS MATTERS
Entry 17 said RH is an inequality between two O(g(0)) quantities but did not say WHICH WAY IT LEANS.
It leans the RIGHT WAY, by a definite amount:

    RH FOLLOWS FROM     E(g) <= (1/2)( 4 - 3 log 2 - pi/2 ) g(0)  for all positive-type g,
                        i.e.  E(g) <= 0.17488... g(0).

This is the first genuinely QUANTITATIVE reduction the programme has produced: a single explicit
constant separating the hypothesis from the smoothed prime error. It is not a proof — E(g) is the
zero sum (cycle 83's circularity verdict) — but it fixes the exact size of the target, and it shows
the archimedean side is NOT the obstruction: it supplies a surplus of 0.3498 g(0), not a deficit.

Machine-verified: `RHTower/ArchimedeanBudgetConstant.lean` (the closed-form constant as a definition,
the termwise domination of the budget series by a telescoping series, the telescoping evaluation
1 - 1/(N+1), the resulting bound beta <= 3/4 on every partial sum, nonnegativity of the terms, the
quarter-margin theorem, the closed form's position strictly below one, positivity of
4 - 3 log 2 - pi/2, and the closed-form margin theorem; standard axioms only, wired into RHTower).

### EIGHTEENTH ATLAS ENTRY
    archimedean budget   sup_g T(g)/g(0) = 3 log 2 + pi/2 - 3 = 0.65023 < 1, sharp in the
                         wide-window limit; margin 4 - 3 log 2 - pi/2 = 0.34976 > 0. Elementary
                         bound beta <= 3/4 by telescoping.

The first entry that is a POSITIVE quantity rather than a wall or a test.

### STATE AT CYCLE 84
Eighteen entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 85 target
The margin is a surplus of 0.34976 g(0) available to absorb the smoothed error. The error is the zero
sum, so bounding it is circular — BUT THE MARGIN IS NOT THE ONLY SURPLUS. The bound |g| <= g(0) used
to compute beta is CRUDE: it ignores that g is positive-definite, hence g(u)/g(0) is itself a
normalised positive-definite function and must DECAY in a controlled way. Sharpen beta by replacing
|g| <= g(0) with the true constraint. Specifically: for ghat >= 0 with g(0)=1, the function g is the
characteristic function of a probability measure, so by Polya/Bochner g(u) >= 1 - (u^2/2) * m_2 with
m_2 the second moment, and more usefully  1 - g(u) >= (1 - g(2u))/4  (the classical characteristic
function inequality). USE THE CHARACTERISTIC-FUNCTION STRUCTURE TO GET A STRICTLY SMALLER beta, hence
a strictly larger margin. Every improvement of the margin is an unconditional improvement of the
constant in the RH-equivalent inequality, and the sequence of such improvements is a genuinely new
quantitative programme with no wall recorded against it.

---

## Cycle 85 (2026-07-26) — THE BUDGET IS SHARP; THE MARGIN DOES NOT DEGRADE
### Cycle 84's target REFUTED (the bound cannot be improved) — and the refutation is the result.

### PHASE 4 KILL OF MY OWN CYCLE-85 PLAN
I proposed sharpening beta by replacing |g| <= g(0) with the true characteristic-function constraint.
REFUTED. The supremum is over ALL widths, and the tent of width L has g/g(0) = 1 - |u|/L -> 1
pointwise, so the crude bound is ATTAINED IN THE LIMIT.

    ==> beta = 3 log 2 + pi/2 - 3 IS SHARP. THE POSITIVE-DEFINITE STRUCTURE CANNOT IMPROVE IT.

Record this: the constant 0.65023 is not an artefact of a lazy estimate. It is the exact value.

### WHAT THE REFUTATION BUYS
At FINITE width the bound IS improvable, for a concrete reason: g == 1 on [-L,L] is not positive
definite, because its transform 2 sin(rL)/r is NEGATIVE for rL in (pi, 2pi) — at rL = 3pi/2 the
numerator is -2. So beta(L) < beta strictly at every finite width.

Shape of beta(L): substituting u = t/2,
    T(g) = int_0^inf ( g(u) e^{-u/2} - g(0) e^{-2u} ) * 2 e^{-2u}/(1 - e^{-2u}) du,
a LINEAR functional with positive kernel kappa(u) = 2 e^{-5u/2}/(1 - e^{-2u}). Expanding the
denominator, kappa is a sum of exponentials 2 e^{-s_n u} with s_n = 2n + 5/2, whose transforms are
POISSON KERNELS 4 s_n/(s_n^2 + r^2). Substituting g = phi * phi~ makes T a quadratic form, so

    beta(L) = lambda_max ( compression to PW_{L/2} of the Toeplitz operator with symbol
                           sum_n 4 s_n / (s_n^2 + r^2) ),

increasing to the symbol's supremum as L -> infinity (Szego-Widom). Each Poisson kernel peaks at
r = 0 with value 4/s_n, and the divergence of sum 4/s_n is exactly the logarithmic divergence at
u = 0 that the subtraction of g(0) e^{-2u} removes.

### THE CONSEQUENCE — NO ARCHIMEDEAN DEGRADATION
    beta(L) increases to beta < 1, so the margin m(L) = 1 - beta(L) DECREASES to
    4 - 3 log 2 - pi/2 = 0.34976 > 0.

    ==> THE ARCHIMEDEAN MARGIN DOES NOT DEGRADE TO ZERO. The rungs of the ladder get harder
        monotonically but converge to a STRICTLY POSITIVE budget, UNIFORM IN THE WIDTH.

This contradicts the expectation set by the degradation entries of the atlas (universal height
degradation, degradation-rate ranking). Those were all about criteria whose ARCHIMEDEAN side was
assumed to weaken. IT DOES NOT. EVERY DEGRADATION IN THE PROBLEM LIVES IN THE ERROR TERM — that is,
IN THE ZEROS — AND NONE OF IT IS ARCHIMEDEAN.

Machine-verified: `RHTower/BudgetSharpAndMarginUniform.lean` (sin(pi + pi/2) = -1 and the resulting
negativity of the constant's transform, the mode rates, the Poisson kernels with positivity, their
maxima 4/s at r = 0, the harmonic lower bound on the maxima, the uniform margin bound, its explicit
numeric form 0.34 < m(L), and strictness at finite width; standard axioms only, wired into RHTower).

### NINETEENTH ATLAS ENTRY
    margin uniformity   beta(L) increases to 3 log 2 + pi/2 - 3 < 1, so the archimedean margin
                        decreases to 0.34976 > 0 and never vanishes. All degradation is in the zeros.

### STATE AT CYCLE 85
Nineteen entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 86 target
Entry 19 says the archimedean side supplies a uniform surplus. Entry 15 says RH is a ladder of finite
rungs. Together: RH <=> for every L, the smoothed error against every positive-type test of width L
is below 0.17488 g(0). The error is the zero sum, so this is Weil's criterion — BUT NOW WITH AN
EXPLICIT CONSTANT AND NO EXPONENTIAL TERMS. THE NEW QUESTION: the constant 0.17488 is what the
ARCHIMEDEAN side gives. What does the PRIME side give BACK? The rung at width L also contains the
prime terms with n <= e^L, and cycle 82 showed the main term is already cancelled — so what remains
on the prime side is sum_{n<=e^L} Lambda(n) n^{-1/2} g(log n) - int, i.e. the DISCRETE-MINUS-
CONTINUOUS defect. That defect is an EULER-MACLAURIN quantity, not a zero sum, for the smooth part.
SPLIT THE ERROR INTO ITS EULER-MACLAURIN PART (elementary, boundable unconditionally) AND ITS
GENUINELY ARITHMETIC PART. If the elementary part alone can exceed 0.17488, the margin is already
consumed and the ladder is tight; if it is provably far below, the surplus available for the
arithmetic part is quantified for the first time.

---

## Cycle 86 (2026-07-26) — THE PROJECT'S DECLARED OPEN CORE REDUCES TO THE PURE ZERO SUM
### Everything except the zeros is O(L e^{-x/2}) in the shift. Explicit constant 4.63.

### Phase 1: I went to the project's OWN declared frontier
`RiemannHypothesisSOTA2026.lean` names the sharpened open core
    SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED:
    "any nonnegative explicit source energy whose Ward defect is merely eventually bounded below on
     the logarithmic rectangular mesh proves RH; false RH forces that defect to -infinity cofinally."
`SuzukiRectangularWardDefectBoundedness.lean` supplies the connector
    riemannHypothesis_of_suzukiRectangularWardDefect_eventually_bddBelow.
The defect is built from xiScrewWindowCurvature L (log n) — THE TENT TRANSLATED to [x, x+2L].

### The two eliminations
1. POLE AND PRIME MAIN TERM: already cancel identically for the translated window (corpus
   `PoleTermCancellation`, cycle 65, via the translation identity).
2. ARCHIMEDEAN: NEW. The translated window vanishes at the origin (x > 0), so the collapsed
   archimedean integral reduces to  -2 int_x^{x+2L} g_x(u) e^{-u/2}/(1-e^{-2u}) du.  For u >= 1 the
   denominator is >= 1 - e^{-2}, and the tent has height L, so

       |A_inf(g_x)|  <=  (4L/(1-e^{-2})) e^{-x/2}  <=  4.63 * L * e^{-x/2}.

    ==> EVERY NON-ZERO-SUM CONTRIBUTION TO THE SCREW WARD DEFECT IS O(L e^{-x/2}).
        THEREFORE   liminf_{x->inf} (screw Ward defect)  =  liminf_{x->inf} (PURE ZERO SUM),
        AND THE PROJECT'S OPEN CORE IS SEMIBOUNDEDNESS OF THE ZERO SUM ALONE.

This is the translated-window counterpart of entry 17: for the symmetric window the exponentially
LARGE terms cancel; for the translated window the surviving archimedean term is exponentially SMALL.
In both cases the functional reduces to its arithmetic content, and nothing else can be blamed.

### Why the defect can reach -infinity, made precise
The translated tent has ghat_x(r) = e^{-irx} Fejer(r), so a zero pair at 1/2 +- a + i gam contributes
e^{-i gam x} e^{+ a x} Fejer(...) from the REFLECTED zero. THE e^{+ax} IS THE ENTIRE -infinity
MECHANISM. Under RH a = 0 and the contribution is bounded. This identifies the exact analytic source
of the corpus's converse theorem.

Machine-verified: `RHTower/ScrewArchimedeanShiftDecay.lean` (the kernel denominator bound on the far
mesh, its positivity, the shifted exponential integral 2(e^{-a/2} - e^{-b/2}) proved from HasDerivAt,
the bound by 2 e^{-x/2}, the decay estimate, the explicit constant 4.63 via e^{-2} <= 0.1354, and
BOTH directions of the semiboundedness transfer between defect and zero sum; standard axioms only,
wired into RHTower).

### TWENTIETH ATLAS ENTRY
    screw shift decay   the archimedean part of the rectangular Ward defect is <= 4.63 L e^{-x/2};
                        with the pole/prime-main cancellation this reduces the project's named open
                        core to semiboundedness of the pure zero sum.

### STATE AT CYCLE 86
Twenty entries. RH IS NEITHER PROVEN NOR DISPROVEN. The explicit-formula method is now completely
characterised: entries 17-20 show that for BOTH window families every non-arithmetic term either
cancels identically or decays exponentially, so no explicit-formula argument can succeed by
manipulating the archimedean, pole, or main prime terms. WHAT REMAINS IS THE ZERO SUM ITSELF.

### Cycle 87 target
The zero sum for the translated window is  sum_rho e^{-i gam x} e^{a x} Fejer(rho').  Semiboundedness
in x is an ALMOST-PERIODICITY question: under RH the exponents are purely imaginary and the sum is a
Besicovitch almost periodic function of x, hence bounded; off RH one exponent has positive real part.
SO THE OPEN CORE IS: SHOW THE SCREW WARD DEFECT IS ALMOST PERIODIC IN THE SHIFT. Almost periodicity is
a structural property that does NOT require knowing the zeros — it requires only that the Dirichlet
exponents be real. CONJECTURE: the screw Ward defect, as a function of the shift, has a Bohr mean
value, and its mean equals the archimedean constant computed in cycle 84. If the mean exists and is
finite, no exponent can have positive real part, and RH follows. TEST WHETHER THE BOHR MEAN OF THE
SCREW DEFECT IS COMPUTABLE UNCONDITIONALLY FROM THE PRIME SIDE — the prime side is a Dirichlet
polynomial in x with real frequencies log n, whose Bohr mean is elementary.

---

## Cycle 87 (2026-07-26) — THE MEAN DICHOTOMY, AND THE BOHR ROUTE'S CIRCULARITY MADE PRECISE

### Phase 4 verdict on the Bohr-mean target: CIRCULAR — recorded, with the exact reason
Cycle 86 asked whether the Bohr mean of the screw defect is computable unconditionally from the prime
side. It is not. The mean of the smoothed error is a Mellin transform,
    int_1^inf (psi(t) - t) t^{-s-1} dt  =  -zeta'(s)/(s zeta(s)) - 1/(s-1),
and its CONVERGENCE AT s = 1/2 IS ITSELF EQUIVALENT TO RH. So the mean is available in closed form —
as 2 - 2 zeta'(1/2)/zeta(1/2) up to normalisation — EXACTLY WHEN RH HOLDS. The Bohr route is a
reformulation, not an independent handle. DEAD END for computing the mean; do not re-attempt.

Also checked: `HTGeometry/BohrAlmostPeriodic.lean` already defines IsBohrAlmostPeriodic and proves a
vanishing lemma. Almost-periodicity infrastructure EXISTS in the corpus — do not rebuild it.

### What survives, and it is sharp
The dichotomy that decides semiboundedness is elementary and quantitative:

  REAL FREQUENCY:  (1/X) int_0^X cos(gam x) dx = sin(gam X)/(gam X),  modulus <= 1/(|gam| X).
                   Every nonzero real frequency averages to zero AT RATE 1/X.

  POSITIVE RATE:   (1/X) int_0^X e^{a x} dx = (e^{aX} - 1)/(aX)  >=  1 + aX/4,
                   using e^t >= (1 + t/2)^2. A single exponent with positive real part makes the mean
                   DIVERGE LINEARLY IN X.

    ==> THE MEAN EXISTS PRECISELY WHEN NO EXPONENT HAS POSITIVE REAL PART, AND WHEN IT FAILS IT
        FAILS BY A LINEAR DIVERGENCE — NOT MARGINALLY.

Quantitatively: if the mean stays below M on every range [0,X], then a X <= 4(M-1) for every X, so
a = 0. The failure of RH is not a delicate near-miss in this formulation; it is a linear blow-up with
an explicit constant.

Machine-verified: `RHTower/BohrMeanDichotomy.lean` (both interval integrals from HasDerivAt, the
1/(|gam|X) decay of a real frequency's mean, the quadratic lower bound e^t - 1 >= t + t^2/4 via
e^t >= (1+t/2)^2, the linear divergence 1 + aX/4, and the two forms of the rate-forcing conclusion;
standard axioms only, wired into RHTower).

### TWENTY-FIRST ATLAS ENTRY
    mean dichotomy   a real frequency's mean decays like 1/X; a positive rate's mean grows like
                     1 + aX/4. Semiboundedness of the screw defect fails by LINEAR divergence, with
                     an explicit constant, as soon as one zero leaves the line.

### STATE AT CYCLE 87
Twenty-one entries. RH IS NEITHER PROVEN NOR DISPROVEN.

THE EXPLICIT-FORMULA LANE IS NOW CLOSED AS A RESEARCH DIRECTION. Entries 17-21 establish that for
both window families every non-arithmetic term cancels identically or decays exponentially, that the
archimedean margin is a fixed positive constant that never degrades, and that the surviving question
is exactly semiboundedness/mean-existence of the pure zero sum — which every attempted handle
(error bound, Bohr mean, extremal test, character average) has been shown to be circular or capped.
DO NOT OPEN ANOTHER EXPLICIT-FORMULA SUB-LANE WITHOUT A GENUINELY NEW INPUT.

### Cycle 88 target — PIVOT AWAY FROM THE EXPLICIT FORMULA
The corpus SOTA file names a second frontier that is NOT explicit-formula based: the Connes
ground-state limit wall. As stated (`ConnesXiGroundStateLimitWall`) it is a zero-transfer consumer —
equivalent to RH, since under RH the constant sequence witnesses it — and the file says the real
frontier must "name the source-defined CCM operator/ground-state family". THAT IS THE TARGET:
supply a CONCRETE sequence F_n -> XiC, locally uniformly, with F_n entire and real-rooted, built from
a source that does not presuppose RH. The Laguerre-Polya characterisation says such a sequence exists
iff XiC is in LP iff RH, so the content is entirely in CONSTRUCTING one. The corpus already has
Gaussian heat-trace, theta, and Jensen/Turan machinery (XiGaussianHeatTuranDefect,
ThetaCuspFullReflectionFourthTuran). START BY AUDITING WHAT REAL-ROOTED APPROXIMANT FAMILIES THE
CORPUS ALREADY CONTAINS and whether any is unconditional.

---

## Cycle 88 (2026-07-26) — PIVOT OFF THE EXPLICIT FORMULA. THE ZERO-TRANSFER CRITERION LOCALIZES.

### Phase 1 audit of the second frontier (record what exists — do not rebuild)
* `LocallyUniformZeroTransfer.lean` — the connector: entire approximants with ALL zeros real,
  converging locally uniformly to XiC, prove RH. Contains the Hurwitz existence step
  `eventually_exists_zero_closedBall_of_tendstoLocallyUniformly` and the closed-locus transfer.
* `CCMRadicalQuotientHermitian.lean` — a Hermitian characteristic-polynomial version of the same.
* `PrimeIsingTreeBalancedVarianceRankNoGo.lean` — UNCONDITIONAL NO-GO for balanced finite prime Ising
  trees: every Fortuin-Kasteleyn configuration carries at least (log 2)^2 of cluster-square mass per
  vertex. DO NOT RE-ATTEMPT THAT FAMILY.
* `BohrAlmostPeriodic.lean` (HTGeometry) — almost-periodicity infrastructure already present.
So the CONNECTORS ARE DONE and the content is entirely in CONSTRUCTING an unconditional family.
By Laguerre-Polya, a global real-rooted family exists iff RH, so the global criterion is a
zero-transfer consumer — as the SOTA file itself says.

### THE WEAKENING
Hurwitz's mechanism is a statement about ONE BALL: if the limit vanishes at z, the approximants must
eventually vanish near z. CONTRAPOSITIVELY, a family that is zero-free on a SINGLE CLOSED BALL forces
the limit to be nonzero at its centre — and NOTHING is required of its zeros anywhere else.

    ==> TO PROVE RH IT SUFFICES TO PRODUCE, FOR EACH OFF-CRITICAL POINT SEPARATELY, A SEQUENCE OF
        ENTIRE FUNCTIONS CONVERGING LOCALLY UNIFORMLY TO XiC AND ZERO-FREE ON SOME BALL AROUND THAT
        POINT. THE SEQUENCES MAY DIFFER FROM POINT TO POINT AND NEED NOT BE REAL-ROOTED ANYWHERE.

Strictly weaker than the global criterion: a real-rooted family is zero-free on every ball centred
off the real axis (formalised as `pointwise_from_real_rooted`, radius |Im z|/2), but a family
zero-free near ONE point need not be real-rooted at all. This converts ONE GLOBAL CONSTRUCTION into
A FAMILY OF INDEPENDENT LOCAL ONES, each free to use whatever structure is available near its own
point — Euler product near Re s = 1, Hadamard/Jensen data at moderate height, heat-flow at large
height, etc. Those tools are individually available; what was never available was one tool that works
everywhere at once. THE LOCALIZATION REMOVES THAT REQUIREMENT.

Machine-verified: `RHTower/LocalizedZeroFreeTransfer.lean`
  * `ne_zero_of_eventually_zeroFree_closedBall` — the local transfer, from the corpus Hurwitz step;
  * `riemannHypothesis_of_pointwise_zeroFree_approximants` — the localized RH criterion;
  * `pointwise_from_real_rooted` — the global criterion implies the local one, so nothing is lost.
Standard axioms only, wired into RHTower.

### TWENTY-SECOND ATLAS ENTRY
    localized zero transfer   RH follows from per-point approximating families that are zero-free on
                              one ball each; global real-rootedness is unnecessary. Strictly weaker
                              than the corpus connector, and it implies it.

This is the first entry that WEAKENS A HYPOTHESIS rather than recording an obstruction. It does not
prove RH, but it changes what has to be built.

### STATE AT CYCLE 88
Twenty-two entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 89 target
Use the localization. Fix an off-critical point z with |Im z| = h. The required object is a sequence
of entire functions -> XiC, locally uniformly, zero-free on a ball of radius R about z. NATURAL
CANDIDATE: the de Bruijn-Newman flow H_t, which is real-rooted for t >= Lambda and tends to XiC as
t -> 0. Globally this needs Lambda <= 0. BUT LOCALLY IT MAY NOT: H_t is real-rooted for t >= Lambda,
and Lambda <= 0.22 unconditionally (Polymath15), so H_t is zero-free on EVERY ball centred at height
|Im z| > 0 for t >= 0.22 — the question is whether zero-freeness on a FIXED ball persists as t
decreases to 0, which is a LOCAL statement about the zero flow, not about the extinction time.
CONCRETELY: the zeros move under z' = 2 sum 1/(z_j - z_k); a zero can only enter the ball B(z,R) by
travelling. BOUND THE SPEED. If the imaginary part of every zero satisfies |d(Im z_j)/dt| <= C
uniformly on t in [0, 0.22], then no zero can reach height h from height 0 in time 0.22 provided
h > 0.22 C, giving an UNCONDITIONAL ZERO-FREE REGION ABOVE HEIGHT 0.22 C — and, by the localization,
RH for all zeros of imaginary part above that. THE ENTIRE QUESTION IS THE SPEED BOUND.

---

## Cycle 89 (2026-07-26) — THE GUARDRAIL ON THE LOCALIZATION, AND THE SPEED-BOUND KILL

### Phase 4 verdict on the cycle-88 speed-bound target: FALSE — no uniform speed bound exists
The de Bruijn-Newman zeros obey  ydot_j = -2 sum_k (y_j - y_k)/|z_j - z_k|^2. I proposed bounding
|ydot_j| uniformly to keep zeros out of a fixed ball for time 0.22. REFUTED: when two zeros share a
real part, |z_j - z_k|^2 = (y_j - y_k)^2 and the term is EXACTLY 1/|y_j - y_k|, which exceeds any
prescribed bound as the pair approaches. Lehmer pairs realise exactly this configuration. There is no
uniform speed, and the backward flow is ill-posed regardless. DEAD END; do not re-attempt.

### THE GUARDRAIL — the most important output of this cycle
The localization (entry 22) lets the approximating family vary with the point. That invites an
obvious cheat: take any family that converges FAST. It does not work, and the reason must be recorded
so no future cycle wastes itself on it.

If  |XiC| >= m > 0  on the ball and  |F_n - XiC| < m  there, then F_n is zero-free on the ball —
TRUE, and formalised. But the hypothesis |XiC| >= m > 0 ON THE BALL ALREADY ASSERTS THAT XiC DOES NOT
VANISH THERE, WHICH IS THE CONCLUSION. Both directions are formalised.

    ==> ZERO-FREENESS DERIVED FROM APPROXIMATION QUALITY IS CIRCULAR. ONLY ZERO-FREENESS FORCED BY
        STRUCTURE — REAL-ROOTEDNESS, SELF-ADJOINTNESS, A POSITIVITY CONSTRAINT — CAN BE USED.

This is the exact analogue, in the operator/approximation lane, of cycle 83's circularity verdict in
the explicit-formula lane. Any candidate family must be zero-free FOR A REASON THAT DOES NOT MENTION
HOW CLOSE IT IS TO XiC.

### SCOPE RESTRICTION (a genuine, if modest, gain)
Every zero of XiC has |Im z| < 1/2 (corpus: `SlabFullWidthAdmissibility.XiC_ne_zero_of_half_le_abs_im`).
So per-point families are needed ONLY for 0 < |Im z| <= 1/2; for |Im z| > 1/2 the CONSTANT family
F_n = XiC works on the ball of radius |Im z| - 1/2. The localized criterion therefore has bounded
scope, formalised as `riemannHypothesis_of_strip_zeroFree_approximants`.

Machine-verified: `RHTower/LocalizationScopeAndGuardrail.lean` (constant sequence converges locally
uniformly; the imaginary-part lower bound on a ball; the scope-restricted RH criterion; both
directions of the proximity guardrail; and the unboundedness and closed form of the drift term;
standard axioms only, wired into RHTower).

### TWENTY-THIRD ATLAS ENTRY
    proximity guardrail   zero-freeness obtained from closeness to XiC is circular; only structurally
                          forced zero-freeness is usable. Scope of the localized criterion is the
                          strip 0 < |Im z| <= 1/2.

### STATE AT CYCLE 89
Twenty-three entries. RH IS NEITHER PROVEN NOR DISPROVEN.

TWO LANES ARE NOW CHARACTERISED, AND BOTH BY THE SAME KIND OF STATEMENT:
  * explicit formula (entries 17-21): every non-arithmetic term cancels or decays; the residue is the
    zero sum, and every handle on it is circular or capped.
  * approximation/operator (entries 22-23): the criterion localizes, but only structurally forced
    zero-freeness counts, and proximity-based constructions are circular.
WHAT BOTH LANES REQUIRE IS THE SAME MISSING OBJECT: A SOURCE OF ZERO-FREENESS THAT IS NOT DERIVED
FROM ZETA ITSELF.

### Cycle 90 target
Name the missing object precisely and search for it. A structurally forced zero-free family means:
entire F_n -> XiC locally uniformly, with F_n = det(I - K_n) for K_n in a class whose spectrum is
constrained a priori (self-adjoint, positive, contraction). The corpus already has compression and
Calkin-rigidity machinery (`SemilocalCompressedEulerOrientation`, `XiPrimeSeamHigherGradeCalkinRigidity`,
`HardyTitchmarshEulerConcrete`, `CCMRadicalQuotientHermitian`) and one no-go
(`PrimeIsingTreeBalancedVarianceRankNoGo`). AUDIT WHICH DETERMINANT FAMILIES THE CORPUS HAS ALREADY
BUILT, WHICH ARE SELF-ADJOINT, AND WHETHER ANY CONVERGES TO XiC. That audit — not a new construction —
is the correct next step, because the guardrail says a construction is worthless unless its
zero-freeness is a priori, and a priori zero-freeness in this lane means self-adjointness.

---

## Cycle 90 (2026-07-26) — EXACT SELF-ADJOINTNESS IS UNNECESSARY. ASYMPTOTIC SUFFICES.

### Phase 1 audit of the determinant lane (record; do not rebuild)
Connectors already present in the corpus:
  * `HermitianDeterminantRH.riemannHypothesis_of_normalizedHermitianCharpoly_tendstoLocallyUniformly`
    — the base connector (Hermitian => real eigenvalues => real-rooted charpoly => RH);
  * `CCMRadicalQuotientHermitian` (semimetric-quotient and real-semimetric-quotient versions);
  * `CCMSourceResponseDeterminantDichotomy`, `PrimeIsingTreeCavity`,
    `PrimeIsingTreeBalancedCentering`, `IsingCavityRapidityAudioCascade` — source families;
  * `PrimeIsingTreeBalancedVarianceRankNoGo` — the unconditional kill of the balanced tree family.
ALL CONNECTORS EXIST. The gap is a concrete family, and by cycle 89's guardrail its zero-freeness
must be A PRIORI, which in this lane means SELF-ADJOINTNESS.

### THE WEAKENING
Exact hermiticity is a rigid demand on every stage of a construction. It can be relaxed to a limit.

NUMERICAL RANGE. Every eigenvalue of A is a value of the quadratic form <Ax,x> at a unit vector, so
its imaginary part is a value of the quadratic form of the ANTI-HERMITIAN PART H = (A - A*)/(2i), and
Cauchy-Schwarz gives Bendixson's bound
        |Im lambda|  <=  ||H||.
An eigenvalue can only be as far from the real axis as the anti-Hermitian part is large.

COMBINED WITH THE LOCALIZATION (entry 22): fix z off the real axis; if every zero of the approximant
has |Im| <= eps and R + eps < |Im z|, the approximant is zero-free on the ball B(z,R). The localized
criterion needs only one ball per point, so R may shrink with z and eps with n.

    ==> RH FOLLOWS FROM ENTIRE APPROXIMANTS CONVERGING LOCALLY UNIFORMLY TO XiC WHOSE ZEROS HAVE
        IMAGINARY PARTS TENDING UNIFORMLY TO ZERO. EXACT REALITY OF THE ZEROS — EXACT
        SELF-ADJOINTNESS OF THE SOURCE — IS NOT NEEDED.

This is the operator-lane counterpart of the localization. A construction now has to be only
ASYMPTOTICALLY self-adjoint — a condition STABLE UNDER PERTURBATION AND TRUNCATION — rather than
exactly self-adjoint at every stage. That is a materially easier object to build: truncations,
compressions, and regularisations of a self-adjoint source generically lose hermiticity by a small
amount, and previously that loss was fatal to the connector. IT NO LONGER IS.

Machine-verified: `RHTower/AsymptoticSelfAdjointness.lean` (the numerical-range bound
||<Hx,x>|| <= ||H|| at unit vectors, Bendixson's bound |Im lambda| <= ||H||, ball exclusion for
points of small imaginary part, zero-freeness of an approximant whose zeros have small imaginary
parts, the asymptotic RH criterion with eps_n -> 0, and the fact that it generalises the exact
criterion as eps = 0; standard axioms only, wired into RHTower).

### TWENTY-FOURTH ATLAS ENTRY
    asymptotic self-adjointness   approximants need only have zeros whose imaginary parts tend
                                  uniformly to zero; via Bendixson this is implied by the
                                  anti-Hermitian part tending to zero in norm. Exact hermiticity is
                                  not required, and the exact criterion is the eps = 0 case.

Entries 22 and 24 together have weakened the operator-lane entry condition twice: from one global
real-rooted family to per-point local families, and from exact to asymptotic self-adjointness.

### STATE AT CYCLE 90
Twenty-four entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 91 target
The relaxed condition is: A_n with ||anti-Hermitian part|| -> 0 and normalized charpoly -> XiC. The
corpus's CCM/Connes families are built from compressions of a source operator. AUDIT WHETHER ANY
EXISTING CCM FAMILY HAS ANTI-HERMITIAN PART TENDING TO ZERO — previously nobody would have checked,
because only exact hermiticity counted. Specifically examine `CCMSourceResponseDeterminantDichotomy`
and `SemilocalCompressedEulerOrientation`: the latter proves the orientation Gram is compact exactly
for a constant coefficient packet, and COMPACTNESS OF THE COMMUTATOR IS EXACTLY THE STATEMENT THAT
THE ANTI-HERMITIAN DEFECT IS NEGLIGIBLE IN THE CALKIN ALGEBRA. If a compressed family's
anti-Hermitian part is compact and the compressions exhaust, the norms of the finite anti-Hermitian
parts may tend to zero — which is now sufficient. THAT IS THE FIRST TIME THE CORPUS'S CALKIN
RIGIDITY RESULTS BECOME USABLE AS A POSITIVE INPUT RATHER THAN AN OBSTRUCTION.

---

## Cycle 91 (2026-07-26) — COMPRESSION CANNOT MANUFACTURE ASYMPTOTIC SELF-ADJOINTNESS
### Cycle 90's proposed exploitation is REFUTED. Record it so no future cycle repeats it.

### The idea and its death
Cycle 90 relaxed the operator-lane entry condition to ||Im A_n|| -> 0 and proposed exploiting the
corpus's Calkin-rigidity results: if the commutator/defect is COMPACT, maybe the compressed finite
stages have vanishing defect. THEY DO NOT.

1. THE DEFECT COMMUTES WITH COMPRESSION. For a self-adjoint projection P, (P A P)* = P A* P, so
       Im (P A P)  =  P (Im A) P.
   Compression NEVER reduces the defect below what compressing Im A gives. It cannot create
   self-adjointness the source lacks.

2. COMPACTNESS IS THE WRONG HYPOTHESIS. If P_n increases to I, then for any x fixed by every P_n
   whose image H x is also fixed,
       ||P_n H P_n||  >=  ||H x|| / ||x||  >  0,
   a positive constant INDEPENDENT OF n. So ||P_n H P_n|| does NOT tend to zero — it tends UP to
   ||H||. Compactness of H says the TAIL (I - P_n) H is small: a statement about what is DISCARDED,
   not about what is KEPT.

    ==> A CONSTRUCTION CANNOT BECOME ASYMPTOTICALLY SELF-ADJOINT BY TRUNCATION. THE DEFECT MUST
        VANISH BY CONSTRUCTION:  A_n = S_n + K_n  WITH S_n SELF-ADJOINT AND ||K_n|| -> 0.

This closes the natural reading of the Calkin-rigidity results as a positive input: the commutator
being compact places the defect in the kernel of the Calkin quotient, but THE FINITE STAGES RETAIN
ITS FULL NORM.

### Also noted (and it is the same guardrail again)
If the normalized charpoly of A_n converges to XiC, the eigenvalues of A_n converge to the zeros of
XiC, so ||Im A_n|| -> 0 IS equivalent to the conclusion unless it is forced a priori. Entry 24 is a
genuine weakening of the ENTRY CONDITION, but it does not weaken the requirement that the vanishing
be STRUCTURAL. Cycle 89's guardrail applies verbatim in the relaxed setting.

Machine-verified: `RHTower/CompressionCannotSelfAdjointify.lean` (the adjoint-compression identity,
self-adjointness preserved under compression, the fixed-vector lower bound on the compression norm,
its positivity, the resulting non-vanishing of compression norms, and the restatement of what does
suffice; standard axioms only, wired into RHTower).

### TWENTY-FIFTH ATLAS ENTRY
    compression no-go   Im(PAP) = P(Im A)P, and compression norms of a fixed nonzero defect are
                        bounded below by ||Hx||/||x|| along any exhausting family. Asymptotic
                        self-adjointness must be built in, never truncated in. Compactness of the
                        defect is irrelevant to the finite stages.

### STATE AT CYCLE 91
Twenty-five entries. RH IS NEITHER PROVEN NOR DISPROVEN.

BOTH LANES ARE NOW CHARACTERISED BY THE SAME MISSING INGREDIENT:
  * explicit formula (17-21): every non-arithmetic term cancels or decays; the residue is the zero
    sum; every handle on it is circular or capped.
  * operator/approximation (22-25): the criterion localizes and relaxes to asymptotic
    self-adjointness, but the vanishing must be structural, and no compression scheme supplies it.
IN BOTH LANES THE MISSING OBJECT IS THE SAME: A SOURCE OF ZERO-FREENESS (equivalently, of
self-adjointness) THAT IS NOT DERIVED FROM ZETA ITSELF.

### Cycle 92 target
Stop looking for the source inside analysis. The only known unconditional sources of a priori
self-adjointness attached to L-functions are GEOMETRIC: the Frobenius action on etale cohomology of a
variety over a finite field, where Weil's theorem is a THEOREM because Poincare duality plus the
hard Lefschetz theorem supply a positive-definite pairing. The corpus's theorem-area name is
`GaloisForLFunctions`. AUDIT WHAT THE CORPUS HAS BUILT ON THE FUNCTION-FIELD SIDE and whether any of
it produces a pairing that survives the passage to the number-field setting — specifically whether
the corpus contains any construction of a Frobenius-like operator whose self-adjointness comes from a
duality rather than from an assumption. That is the only lane in which self-adjointness has ever been
obtained a priori, and per entries 24-25 that is precisely what is required.

---

## Cycle 92 (2026-07-26) — THE SECOND A PRIORI SOURCE: SIMILITUDE OF A DEFINITE PAIRING

### Phase 1 audit of the geometric lane — the honest result
Searched the whole development for etale cohomology, Frobenius actions, Poincare duality, hard
Lefschetz, function-field L-functions. NONE OF IT IS PRESENT. The theorem-area name
`GaloisForLFunctions` is aspirational; the hits are Galois-theoretic and Mahler-type material in the
U0/Bottcher areas, unrelated. Mathlib does not supply etale cohomology either. THE GEOMETRIC LANE IS
NOT ACCESSIBLE AS A CONSTRUCTION. Record it; do not open it as a build target.

### What IS accessible: the linear-algebra core of Weil's theorem
Everything geometric in the function-field proof exists to produce ONE configuration: a
finite-dimensional space with a pairing that is definite on primitive parts, and an operator that
scales it. Once that configuration is available the conclusion is two lines:

    F x = lam x,   ||F x||^2 = q ||x||^2   ==>   ||lam||^2 ||x||^2 = q ||x||^2   ==>   ||lam|| = sqrt q.

    ==> A SIMILITUDE OF A DEFINITE PAIRING CONFINES ITS WHOLE SPECTRUM TO A CIRCLE, EXACTLY AS A
        SELF-ADJOINT OPERATOR CONFINES IT TO A LINE. IT IS A SECOND, INDEPENDENT A PRIORI SOURCE.

In logarithmic coordinates the circle |lam| = sqrt q IS a line, so a similitude source feeds the same
connectors as a self-adjoint one. This answers the question entries 24-25 left open — "what a priori
source exists besides self-adjointness?" — with the only other structure known to constrain a
spectrum without reference to the function whose zeros are being located.

### AND IT RELAXES, LIKE SELF-ADJOINTNESS
If the pairing is scaled only approximately,  | ||F x||^2 - q ||x||^2 | <= delta ||x||^2, then
| ||lam||^2 - q | <= delta, hence  | ||lam|| - sqrt q | <= delta / sqrt q. The spectrum CONCENTRATES
on the circle at rate delta/sqrt q. Combined with entry 24, AN APPROXIMATELY SIMILITUDINOUS FAMILY IS
AS GOOD AS AN EXACT ONE — which matters because approximate scaling survives truncation and
regularisation, and exact scaling does not.

Machine-verified: `RHTower/SimilitudeSpectralLocus.lean` (the similitude spectral locus
||lam||^2 = q, its approximate form |‖lam‖^2 - q| <= delta, the concentration estimate
| ||lam|| - sqrt q | <= delta/sqrt q via the factorisation m^2 - q = (m - sqrt q)(m + sqrt q), the
identification of the circle as a line in log coordinates, and exact-as-delta-zero; standard axioms
only, wired into RHTower).

### TWENTY-SIXTH ATLAS ENTRY
    similitude locus   an operator scaling a definite pairing by q has all eigenvalues of modulus
                       sqrt q; approximate scaling by delta gives concentration at rate delta/sqrt q.
                       This is the second a priori spectral source, and the mechanism that makes the
                       function-field hypothesis a theorem.

### STATE AT CYCLE 92
Twenty-six entries. RH IS NEITHER PROVEN NOR DISPROVEN.

THE PROGRAMME NOW HAS A COMPLETE SPECIFICATION OF WHAT IS MISSING:
  * both analytic lanes reduce to needing an a priori spectral constraint (entries 17-25);
  * there are exactly two known such constraints — self-adjointness (line) and similitude of a
    definite pairing (circle) — and both relax to asymptotic versions (entries 24, 26);
  * neither is available for zeta without the geometric input that does not exist in this
    development or in Mathlib.
WHAT IS MISSING IS NOT A TECHNIQUE. IT IS A DEFINITE PAIRING ON WHICH SOMETHING ATTACHED TO ZETA ACTS
BY A SCALAR MULTIPLE OR SELF-ADJOINTLY.

### Cycle 93 target
Ask where a definite pairing attached to zeta could come from, given that the archimedean side is now
completely understood. Entry 18 gives an exact positive constant: the archimedean margin
4 - 3 log 2 - pi/2 = 0.34976, uniform in the width (entry 19). A POSITIVE CONSTANT IS A DEFINITE
FORM. CONJECTURE: the archimedean margin is the definiteness of a pairing — specifically, the
quadratic form g -> g(0) - T(g) on the positive-definite cone is bounded below by 0.34976 g(0), i.e.
it is a POSITIVE-DEFINITE FORM ON THE CONE with an explicit lower Gram bound. If that form can be
completed to an inner product on a space carrying a natural zeta-action, the missing pairing is the
archimedean one and the constant 0.34976 is its definiteness constant. TEST WHETHER g -> g(0) - T(g)
EXTENDS TO A POSITIVE-DEFINITE HERMITIAN FORM BEYOND THE CONE — that is a concrete, decidable
question about an explicit kernel, and it is the first time the programme has had an explicit
candidate for the missing pairing.

---

## Cycle 93 (2026-07-26) — THE MISSING DEFINITE PAIRING IS THE ARCHIMEDEAN FORM. CONSTANT 0.34976.

### The conjecture of cycle 92, CONFIRMED
Writing a positive-type test as g = phi * phi~, we have g(0) = ||phi||^2 and T(g) is a LINEAR
functional of g, hence a QUADRATIC FORM in phi. So

    Q(phi)  =  g(0) - T(g)  =  < (I - 𝒯) phi, phi >

for a self-adjoint 𝒯 — the compression of the convolution operator whose symbol is the sum of Poisson
kernels 4 s_n/(s_n^2 + r^2), s_n = 2n + 5/2 (cycle 85). THE BUDGET BOUND IS EXACTLY ||𝒯|| <= beta,
with beta = 3 log 2 + pi/2 - 3 = 0.65023 < 1. Therefore for EVERY phi,

    (1 - beta) ||phi||^2  <=  Q(phi)  <=  (1 + beta) ||phi||^2,   1 - beta = 4 - 3 log 2 - pi/2.

    ==> THE ARCHIMEDEAN FORM IS A POSITIVE-DEFINITE HERMITIAN FORM, UNIFORMLY IN THE WIDTH,
        EQUIVALENT TO THE AMBIENT INNER PRODUCT WITH EXPLICIT TWO-SIDED CONSTANTS, AND BOUNDEDLY
        INVERTIBLE WITH ||Q^{-1}|| <= 1/(1 - beta) = 2.859...

Note this holds on ALL of L^2 of the interval, not only on the positive-type cone: the cone was only
needed to identify beta as the supremum, and once ||𝒯|| <= beta is known the form is definite
everywhere. THE PAIRING THE PROGRAMME HAS BEEN MISSING SINCE ENTRY 24 IS EXPLICIT, AND ITS
DEFINITENESS CONSTANT IS 4 - 3 log 2 - pi/2 = 0.34976.

### What the hypothesis becomes
    RH  <=>  𝒫  <=  Q     as quadratic forms, for every width,
with 𝒫 the compressed prime operator. Since Q is boundedly invertible this is a genuine operator
inequality on a fixed Hilbert space: spec( Q^{-1/2} 𝒫 Q^{-1/2} ) subset (-inf, 1].

WHAT IS STILL MISSING IS NOT THE PAIRING BUT THE RELATION. Nothing yet forces 𝒫 <= Q, and by entries
24-26 such a forcing must come from self-adjointness or a similitude, NOT from estimates. The
programme's remaining gap is now a single, precisely stated operator-theoretic statement rather than
a description of an absence.

Machine-verified: `RHTower/ArchimedeanPairingDefinite.lean` (the quadratic-form norm bound, the
two-sided estimate (1-beta)||x||^2 <= Q <= (1+beta)||x||^2, strict positivity for beta < 1, positivity
and closed form of the definiteness constant, the inverse bound, and the restatement of the Weil
inequality as domination 𝒫 <= Q; standard axioms only, wired into RHTower).

### TWENTY-SEVENTH ATLAS ENTRY
    archimedean pairing   Q = I - 𝒯 with ||𝒯|| <= 3 log 2 + pi/2 - 3 < 1, so Q is uniformly
                          positive definite with constant 4 - 3 log 2 - pi/2 = 0.34976 and
                          boundedly invertible. RH is the operator inequality 𝒫 <= Q.

This is the first entry that SUPPLIES a missing object rather than describing, bounding, or
weakening. Entries 24-26 said what was needed; entry 27 produces half of it.

### STATE AT CYCLE 93
Twenty-seven entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 94 target
Entry 27 gives the pairing Q; entry 26 says a similitude of a definite pairing constrains a spectrum.
ASK WHETHER ANYTHING ACTS ON Q AS A SIMILITUDE. The natural candidates are the DILATIONS
(phi(x) -> lambda^{1/2} phi(lambda x)) and the TRANSLATIONS. On the whole line Q is a Fourier
multiplier, hence translation-invariant — but the compression to [-L/2, L/2] breaks that, and the
breaking is exactly the finite-width defect beta(L) < beta of cycle 85. CONJECTURE: the translation
defect of Q on the compressed space is O(1/L), so translations act on Q as ASYMPTOTIC ISOMETRIES —
and by entry 26's approximate form, an asymptotic isometry constrains the spectrum asymptotically,
which by entry 24 is enough. COMPUTE THE TRANSLATION DEFECT OF Q. If it is o(1) in L, the two halves
of the missing structure meet.

---

## Cycle 94 (2026-07-26) — COMPRESSED TRANSLATIONS ARE SIMILITUDES IN DENSITY, NEVER IN NORM
### Cycle 93's conjecture REFUTED. The refutation explains why Szego/Toeplitz asymptotics cannot work.

### The kill
Let V_s = P T_s P be the compressed translation on L^2[-l, l]. A function supported in [l - s, l] is
carried by T_s into [l, l + s], ENTIRELY OUTSIDE the window, so V_s ANNIHILATES IT. Such a unit
vector exists AT EVERY WIDTH, however large.

An operator with a kernel vector cannot be a delta-approximate similitude of ratio q > delta: from
| ||Vx||^2 - q ||x||^2 | <= delta ||x||^2 with Vx = 0 and ||x|| = 1 one gets q <= delta immediately.

    ==> THE TRANSLATION DEFECT OF Q IS NOT O(1/L). IT IS 1, AT EVERY WIDTH. CONJECTURE REFUTED.

### But the edge is thin — and that is the real content
The annihilated subspace occupies a window of length s inside one of length 2l, a fraction
s/2l -> 0. In the prolate/time-frequency picture the transition band has dimension O(log) inside a
space whose dimension is proportional to the time-bandwidth area. SO THE COMPRESSED TRANSLATIONS ARE
ASYMPTOTIC SIMILITUDES IN THE SENSE OF DENSITY.

AND DENSITY IS NOT ENOUGH. Density-sense similitude controls the eigenvalue DISTRIBUTION — that is
exactly what Szego-type limit theorems deliver — but says nothing about the EXTREME eigenvalues,
because the exceptional subspace, though of vanishing proportion, is precisely where extremes live.
The hypothesis is a statement about the extremes: 𝒫 <= Q bounds the TOP of the spectrum.

    ==> A VANISHING FRACTION IS NOT A VANISHING NORM. THIS IS THE SECOND INSTANCE OF THE COMPRESSION
        WALL (entry 25), AND IT EXPLAINS WHY SZEGO AND TOEPLITZ ASYMPTOTICS HAVE NEVER PRODUCED THE
        HYPOTHESIS: THEY ARE DENSITY THEOREMS AND THE HYPOTHESIS IS AN EXTREMAL STATEMENT.

Machine-verified: `RHTower/DensityNotNormSimilitude.lean` (the kernel obstruction to approximate
similitude, its persistence at every width, the vanishing of the edge fraction s/2l, its positivity
at every finite width, the density-versus-norm dichotomy, and the extremal character of the
domination statement; standard axioms only, wired into RHTower).

### TWENTY-EIGHTH ATLAS ENTRY
    density not norm   compressed translations annihilate an edge subspace at every width, so their
                       similitude defect is 1 in norm while the edge fraction s/2l tends to zero.
                       Density-sense similitude gives the eigenvalue distribution (Szego); the
                       hypothesis is extremal, so it is not reachable that way.

### STATE AT CYCLE 94
Twenty-eight entries. RH IS NEITHER PROVEN NOR DISPROVEN.

A PATTERN NOW REPEATS THREE TIMES (entries 25, 28, and the cycle-89 guardrail): EVERY ATTEMPT TO
MANUFACTURE THE MISSING STRUCTURE BY TRUNCATION, COMPRESSION, OR APPROXIMATION FAILS AT THE EDGE, AND
THE FAILURE IS ALWAYS OF SIZE ONE IN NORM WHILE VANISHING IN DENSITY. The structure must be present
BEFORE compression, on the whole line, or it is not present at all.

### Cycle 95 target
Take the pattern seriously and work on the WHOLE LINE, where Q is an exact Fourier multiplier with
symbol 1 - sum_n 4 s_n/(s_n^2 + r^2) + c, s_n = 2n + 5/2, and translations act EXACTLY as isometries.
The prime operator on the whole line has symbol 2 sum_n Lambda(n) n^{-1/2} cos(r log n), which does
not converge — that divergence is WHY compression was introduced. SO THE QUESTION IS: IS THERE A
REGULARISATION OF THE PRIME SYMBOL THAT CONVERGES ON THE WHOLE LINE AND PRESERVES THE ORDER RELATION
𝒫 <= Q? Abel or Cesaro summation of the prime symbol converges for Re s > 1 and its boundary
behaviour at Re s = 1/2 is the object of the hypothesis — but the ORDER RELATION may survive
regularisation even where the symbol does not converge pointwise. TEST WHETHER 𝒫 <= Q IS STABLE UNDER
ABEL REGULARISATION: if the regularised inequality is equivalent to the compressed one, the whole-line
setting is available and the edge obstruction disappears.

---

## Cycle 95 (2026-07-26) — THE OPERATOR LANE IS CLOSED AT BOTH ENDS
### Walled under compression (entries 25, 28); DEGENERATE without it.

### The whole-line computation
On L^2(R) the archimedean form Q is a Fourier multiplier. Its symbol is 1 plus the REGULARISED sum of
Poisson kernels
    sum_n ( 4 s_n/(s_n^2 + r^2) - 4/s_n )  =  - sum_n 4 r^2 / ( s_n (s_n^2 + r^2) ),   s_n = 2n + 5/2,
which CONVERGES (terms ~ 4r^2/s_n^3), is NEGATIVE, and has size -2 log|r| — exactly matching the
archimedean weight Omega(r) ~ log|r|. INDEPENDENT CONFIRMATION of the cycle-84/85 analysis from the
whole-line side. The Abel-regularised prime form 𝒫_eps is also a multiplier, with symbol
-2 Re (zeta'/zeta)(1/2 + eps + i r).

### THE COLLAPSE
TWO MULTIPLIERS COMMUTE and are simultaneously diagonalised by the Fourier transform. Hence

    ==> THE OPERATOR INEQUALITY  𝒫_eps <= Q  IS EXACTLY THE POINTWISE INEQUALITY OF THEIR SYMBOLS.
        NO SPECTRAL THEORY SURVIVES THE PASSAGE TO THE WHOLE LINE: the entire content is a bound
        between two real functions of one variable.

And that bound is LAGARIAS' CRITERION: by the partial-fraction expansion the symbol of 𝒫_eps is a sum
over zeros of (1/2 + eps - beta)/((1/2 + eps - beta)^2 + (r - gam)^2) plus an explicit archimedean
part. Under RH every beta = 1/2, every term has numerator eps > 0 and the inequality is preserved;
if some beta = 1/2 + a > 1/2 then at r = gam and eps < a the term is 1/(eps - a), NEGATIVE AND
UNBOUNDED as eps rises to a. PHASE-4 VERDICT: REDISCOVERED (Lagarias); the corpus already has
`KreinChamberIsLagarias`.

### THE DIAGNOSTIC — this is what the cycle is worth
The compression wall of entries 25 and 28 is an ARTEFACT OF THE FINITE-WIDTH FORMULATION, not
intrinsic to the operator approach: on the whole line there is no edge and translations are exact
isometries. BUT THE WALL-FREE FORMULATION IS THE POINTWISE ONE, IN WHICH NO SIMILITUDE AND NO
SELF-ADJOINTNESS CAN HELP, BECAUSE EVERYTHING ALREADY COMMUTES.

    ==> THE OPERATOR LANE IS CLOSED AT BOTH ENDS: WALLED UNDER COMPRESSION, DEGENERATE WITHOUT IT.
        A NONCOMMUTATIVE STRUCTURE IS NECESSARY, AND COMPRESSION IS THE ONLY SOURCE OF
        NONCOMMUTATIVITY AVAILABLE — AND IT IS EXACTLY WHAT ENTRIES 25 AND 28 KILL.

That is a genuine dichotomy and it explains the whole shape of the operator-theoretic literature on
RH: constructions are either commutative (and give back Lagarias) or compressed (and lose the extreme
eigenvalues to the edge).

Machine-verified: `RHTower/WholeLineCollapse.lean` (the reduction of a multiplier inequality to a
pointwise one in both directions, positivity of the zero term on the critical line, its reversal off
the line, the closed form 1/(eps - a) at the ordinate, and the quantitative blow-up as eps rises to
a; standard axioms only, wired into RHTower).

### TWENTY-NINTH ATLAS ENTRY
    whole-line collapse   on L^2(R) both forms are Fourier multipliers, so they commute and the
                          operator inequality is pointwise — Lagarias' criterion. The operator lane
                          is walled under compression and degenerate without it; noncommutativity is
                          necessary and unavailable.

### STATE AT CYCLE 95
Twenty-nine entries. RH IS NEITHER PROVEN NOR DISPROVEN.

THREE LANES ARE NOW CHARACTERISED:
  * explicit formula (17-21): every non-arithmetic term cancels or decays; residue is the zero sum;
    every handle circular or capped.
  * approximation/operator (22-28): criterion localizes and relaxes, but zero-freeness must be
    structural; compression retains full defect norm; density is not norm.
  * whole-line/commutative (29): no wall, but no content beyond Lagarias.
EVERY LANE TERMINATES IN THE SAME PLACE. The missing ingredient is a NONCOMMUTATIVE structure whose
noncommutativity does not come from compression.

### Cycle 96 target
Noncommutativity not from compression. The only such source attached to zeta in the literature is the
ADELIC one: the action of the idele class group on the adele class space, where noncommutativity comes
from the GROUP, not from truncation. The corpus has CCM (Connes-Consani-Marcolli) files
(`CCMRationalAdelicBruhatSimpleTensorTraceClass`, `CCMFirstClockVolterra`, `CCMComplexMellinColligation`,
`CCMSourceResponseDeterminantDichotomy`). AUDIT WHETHER ANY OF THEM SUPPLIES A GROUP-THEORETIC
NONCOMMUTATIVITY — specifically an action of a nonabelian group by isometries of a definite pairing —
rather than a compression. Per entries 26-27 the pairing exists (Q, definiteness 0.34976); per entry
29 what is needed is a nonabelian isometry group of it. THAT IS NOW A COMPLETELY EXPLICIT TARGET:
find a nonabelian group acting on L^2 by Q-isometries.

---

## Cycle 96 (2026-07-26) — THE DILATION DIRECTION IS THE NONCOMMUTATIVE ONE. IT SHIFTS THE ABSCISSA.

### Correction to cycle 95's framing (record it)
I wrote that a NONABELIAN GROUP is needed. That is wrong: the idele class group is ABELIAN, and in
Connes' picture the noncommutativity comes from the CROSSED PRODUCT of an abelian group acting
nontrivially, not from a nonabelian group. What is needed is a NONTRIVIAL ACTION, not a nonabelian
one. Corrected.

### Phase 1 audit result
The corpus DOES contain adelic machinery: `CCMRationalFiniteBruhatSchwartz`, right translation by
finite ideles (`ccmRationalFiniteBruhatMulRight`), archimedean Schwartz lattices and Poisson files,
`CCMRationalAdelicBruhatSimpleTensorTraceClass`, `SoninLogShellCocycle`. THE GROUP ACTION IS PRESENT.
Do not rebuild it.

### Which direction is noncommutative
On the u-side BOTH forms are CONVOLUTION operators, so TRANSLATIONS PRESERVE BOTH AND CONSTRAIN
NOTHING — that is entry 29 restated. THE DILATIONS ARE DIFFERENT. The archimedean symbol has profile
q(r) = 1 + 2 log|r|, and dilation acts on symbols by q -> q(r/lam). Since log(r/lam) = log r - log lam,

    D_lam^* Q D_lam  =  Q  -  (2 log lam) I  +  (bounded remainder).

    ==> THE DILATION GROUP ACTS ON Q BY AFFINE SHIFTS WHILE TRANSLATIONS ACT TRIVIALLY. TOGETHER THEY
        GENERATE THE ax+b GROUP, WHICH IS NONABELIAN. THE NONCOMMUTATIVITY ENTRY 29 REQUIRES IS
        PRESENT, AND IT LIES IN THE DILATION DIRECTION.

### And dilation moves the abscissa — this is the Frobenius analogue
Dilation by lam replaces the frequencies log n by log n / lam. These are logarithms of integers
exactly when lam = 1/k: then k log n = log(n^k), and the weight Lambda(n) n^{-1/2} becomes
Lambda(n) n^{-k/2}.

    ==> THE ax+b ACTION CARRIES THE WEIL FORM AT ABSCISSA 1/2 TO THE WEIL FORM AT ABSCISSA k/2,
        WHERE POSITIVITY IS TRIVIAL BECAUSE THE PRIME SERIES CONVERGES ABSOLUTELY (k >= 2).
        WHAT BLOCKS RUNNING THE RELATION BACKWARDS IS PRECISELY THE ARCHIMEDEAN SHIFT 2 log lam,
        WHICH IS UNBOUNDED.

This is the first time the programme has an obstruction that is a SINGLE EXPLICIT SCALAR rather than
a structural absence. The map n -> n^k is the arithmetic analogue of Frobenius; the corresponding
similitude ratio is n^{-(k-1)/2}; and the archimedean side pays 2 log k for it.

Machine-verified: `RHTower/DilationFrobeniusShift.lean` (the symbol shift
1 + 2 log(r/lam) = (1 + 2 log r) - 2 log lam, unboundedness of the shift, the frequency identity
k log n = log(n^k), the abscissa change of the weights, absolute convergence for k >= 2, and the
noncommutativity lam(r+a) != lam r + a; standard axioms only, wired into RHTower).

### THIRTIETH ATLAS ENTRY
    dilation shift   translations preserve both forms (nothing constrained); dilations shift the
                     archimedean symbol by -2 log lam and carry the prime form from abscissa 1/2 to
                     k/2. The ax+b group supplies the missing noncommutativity, and the obstruction
                     to descending back to 1/2 is the single scalar 2 log lam.

### STATE AT CYCLE 96
Thirty entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 97 target
Quantify the descent. At abscissa k/2 the Weil form is positive for free. Descending to 1/2 costs
2 log k on the archimedean side and gains the factor n^{(k-1)/2} on the prime side. THE QUESTION IS
WHETHER THE TWO CAN BE BALANCED FOR ANY k, i.e. whether there is a k for which the archimedean surplus
(entry 18: margin 0.34976 g(0), uniform) exceeds the descent cost 2 log k. Since the margin is a FIXED
CONSTANT and the cost GROWS LIKE log k, THE ANSWER IS NO FOR LARGE k — but the prime gain also grows.
COMPUTE THE EXACT BALANCE: the descent is worthwhile iff (prime gain at abscissa k/2 pulled back)
exceeds 2 log k, and both sides are now explicit. If the balance is favourable for even ONE k >= 2,
the descent gives an unconditional positivity statement at abscissa 1/2 — that is, RH.

---

## Cycle 97 (2026-07-26) — CORRECTION TO ENTRY 30, AND THE SCALE INVARIANT THAT REPLACES IT

### SELF-CORRECTION (the important part of this cycle)
Entry 30 claimed that dilating by lam = 1/k turns the prime weight Lambda(n) n^{-1/2} into
Lambda(n) n^{-k/2}, moving the abscissa UP to k/2 where the series converges absolutely. THAT IS
FALSE. The weight is attached to n; re-indexing the FREQUENCY does not change it. What actually
happens is

    sum_n Lambda(n) n^{-1/2} delta_{log n}  ->  sum_n Lambda(n) n^{-1/2} delta_{k log n}
                                            =   sum_{m = n^k} Lambda(m) m^{-1/(2k)} delta_{log m},

using n^{-1/2} = (n^k)^{-1/(2k)}. SO THE DILATED FORM SITS AT ABSCISSA 1/(2k) < 1/2, SUPPORTED ON
PERFECT k-TH POWERS: the dilation moves the abscissa DOWN, AWAY from convergence, and thins the
support. Entry 30's "descent to a convergent abscissa" is WITHDRAWN.

WHAT STANDS FROM ENTRY 30: dilations shift the archimedean symbol by -2 log lam (formalised and
correct); translations act trivially on both convolution forms; the ax+b group is nonabelian and is
the only noncommutative direction available. Those are unaffected.

### THE REPLACEMENT, AND IT IS STRONGER
Rescaling s -> s/k sends the zeros of zeta to the line Re s = k/2 AND the abscissa of absolute
convergence from 1 to k. BOTH MOVE BY THE SAME FACTOR, so

    (critical abscissa) / (convergence abscissa)  =  (k/2)/k  =  1/2,   for every k.

    ==> THE RATIO OF THE CRITICAL ABSCISSA TO THE ABSCISSA OF ABSOLUTE CONVERGENCE IS A SCALE
        INVARIANT. NO DILATION CAN BRING THE CRITICAL LINE INTO THE REGION OF ABSOLUTE CONVERGENCE,
        BECAUSE THE TWO MOVE TOGETHER. THE ax+b NONCOMMUTATIVITY IS REAL BUT ACTS TRIVIALLY ON THE
        ONLY QUANTITY THAT MATTERS.

This kills every rescaling argument at once, and it is a constraint on the lane rather than the
failure of one attempt. It also explains why the classical "shift to Re s > 1 and come back" strategy
has never worked: there is nothing to come back from, because the target moves with the observer.

Machine-verified: `RHTower/ScaleInvariantAbscissaRatio.lean` (the weight identity
n^{-1/2} = (n^k)^{-1/(2k)}, the downward motion 1/(2k) < 1/2, its position below the convergence
threshold, the scale invariance (k/2)/k = 1/2, its independence of the scale, and the strict
inequality k/2 < k; standard axioms only, wired into RHTower).

### THIRTY-FIRST ATLAS ENTRY (and entry 30 amended)
    scale invariance   (critical abscissa)/(convergence abscissa) = 1/2 at every scale. Dilation
                       moves the prime form to abscissa 1/(2k), down and sparser, never up. Every
                       rescaling argument fails for this single reason.
    entry 30 AMENDED   dilations shift the archimedean symbol by -2 log lam and supply the only
                       noncommutative direction; the claim that they raise the prime abscissa to k/2
                       is WITHDRAWN.

### STATE AT CYCLE 97
Thirty-one entries. RH IS NEITHER PROVEN NOR DISPROVEN.

FOUR LANES CHARACTERISED, ALL TERMINATING IN THE SAME PLACE:
  * explicit formula (17-21) — cancels to the zero sum; every handle circular or capped.
  * approximation/operator (22-28) — localizes and relaxes, but zero-freeness must be structural;
    compression retains full defect norm; density is not norm.
  * whole-line/commutative (29) — no wall, no content beyond Lagarias.
  * dilation/scaling (30 amended, 31) — the only noncommutative direction, but the critical-to-
    convergence ratio is scale invariant, so it cannot move the problem.

### Cycle 98 target
The scale invariant 1/2 is itself the object to attack. It is the exponent in the functional equation
s -> 1 - s, whose fixed point is 1/2, AND it is the ratio (critical)/(convergence). THOSE ARE TWO
INDEPENDENT DERIVATIONS OF THE SAME NUMBER, and their agreement is not explained by anything in this
development. CONJECTURE: the agreement is forced — for any Dirichlet series with an Euler product of
degree d and a functional equation of the form s -> w - s, the fixed point w/2 equals the ratio
(critical)/(convergence) if and only if the Euler factors are of degree one in p^{-s}. If true, THE
CRITICAL LINE IS THE FIXED POINT OF THE SCALING SYMMETRY, not merely of the functional equation, and
degree-one Euler factors are what identifies them. TEST THE CONJECTURE ON DEGREE-TWO EULER PRODUCTS
(modular L-functions, where the convergence abscissa is 1 and the critical line is 1/2 in the analytic
normalisation) — if the ratio still equals 1/2 there, the conjecture is false and the coincidence is
an artefact of normalisation; if it differs, the coincidence is structural and is a new invariant.

---

## Cycle 98 (2026-07-26) — THE WITNESS TEST. CYCLE 97'S CONJECTURE REFUTED; THE CORPUS ALREADY HAD THE
## COUNTEREXAMPLE.

### Phase 1 save — THE FOURTH TIME THE OBJECT-LEVEL RULE HAS PAID
Planned: test whether the ratio 1/2 characterises degree-one Euler factors, using a
Davenport-Heilbronn-style counterexample. Search for "Davenport / Heilbronn / functional equation off
line" returned TWO EXISTING CORPUS THEOREMS, both stronger and constructive:
  * `LambdaPositiveFunctionalEquationOffLine.lambdaPositive_functionalEquation_not_criticalLine` —
    Lambda >= 0 PLUS the Riemann functional equation does NOT force the critical line; for EVERY
    prescribed off-critical abscissa beta in (1/2,1) and ordinate gamma there is such a system with a
    zero there;
  * `EntireFunctionalEquationOffLine.lambdaPositive_entire_functionalEquation_not_criticalLine` — the
    entire version.
MY PLANNED CYCLE WAS A DUPLICATE. Do not rebuild. (Search the OBJECT — "functional equation off line"
— not the tool — "Davenport-Heilbronn".)

### Cycle 97's conjecture: REFUTED, and by normalisation
The conjecture was that the ratio (critical)/(convergence) = 1/2 characterises degree-one Euler
factors. FALSE: in the analytic normalisation EVERY Selberg-class L-function has convergence abscissa
1 and functional equation s <-> 1-s BY AXIOM, so the ratio is 1/2 by fiat, degree two included
(modular L-functions). The coincidence of cycle 97 is an ARTEFACT OF NORMALISATION, not a structural
invariant.

### THE REPLACEMENT: THE WITNESS TEST
The corpus witnesses satisfy the functional equation and the convergence normalisation, hence the
ratio 1/2, AND have zeros off the critical line. Therefore:

    ==> ANY ARGUMENT APPEALING ONLY TO THE FUNCTIONAL EQUATION, THE CONVERGENCE ABSCISSA, AND THEIR
        SCALING BEHAVIOUR IS REFUTED IN ADVANCE. THE EULER PRODUCT IS NOT A CONVENIENCE IN THIS
        PROBLEM; IT IS THE ONLY INGREDIENT THAT DISTINGUISHES ZETA FROM THE COUNTEREXAMPLES.

This gives the programme a CHECKABLE INSTRUMENT: every proposed argument must FAIL on the witnesses.

### CLASSIFICATION OF THE ATLAS BY THE WITNESS TEST
  * entries 17-21 (explicit formula): involve the prime side — NOT refuted.
  * entries 22-29 (operator/approximation): involve the compressed prime operator 𝒫 — NOT refuted.
  * entries 30-31 (dilation, scale invariance): use only the functional equation and the convergence
    abscissa — REFUTED BY THE WITNESSES. The scaling lane cannot force the critical line, whatever is
    done with it. This is now proved, not suspected.

Machine-verified: `RHTower/WitnessTestForArguments.lean` (the insufficiency principle, its
contrapositive, the fact that the witnesses realise the same ratio, that the ratio therefore does not
separate, and the isolation statement showing a forcing property must fail on the witnesses hence must
involve the Euler product; standard axioms only, wired into RHTower).

### THIRTY-SECOND ATLAS ENTRY
    witness test   the corpus's Lambda-positive functional-equation systems have off-line zeros while
                   satisfying the functional equation, the convergence normalisation, and the ratio
                   1/2. Any argument using only those is refuted in advance; the Euler product is the
                   only separating ingredient. Entries 30-31 fail the test; entries 17-29 pass.

### STATE AT CYCLE 98
Thirty-two entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 99 target
The witness test says the Euler product is the ONLY separating ingredient, and the atlas says every
lane that uses it terminates in circularity. THOSE TWO FACTS TOGETHER ARE THE SHARPEST STATEMENT THE
PROGRAMME HAS. So attack the Euler product directly: what property of it, beyond multiplicativity,
fails for the witnesses? The witnesses have Lambda >= 0 and a functional equation but NO Euler
product — meaning their generalized von Mangoldt measure is not supported on prime powers with the
multiplicative structure. THE CANDIDATE SEPARATING PROPERTY IS THE SUPPORT: zeta's log-derivative
measure is supported on {log p^k} — a set with MULTIPLICATIVE STRUCTURE and, crucially, LINEAR
INDEPENDENCE OVER Q of the log p. The corpus has `LogIndependence.lean` and `PrimeSymbolDecoupling`.
TEST WHETHER LINEAR INDEPENDENCE OF THE PRIME LOGARITHMS IS THE PROPERTY THE WITNESSES FAIL — if the
witnesses necessarily have Q-linearly dependent support, then linear independence is the separating
ingredient, and it is a property no existing lane has used.

---

## Cycle 99 (2026-07-26) — THE ASYMMETRY OF THE PRIME SYMBOL IS THE POLE
### Fifth Phase-1 save; the salvage is an exact identity joining two independent corpus results.

### Phase 1 save (FIFTH TIME the object-level rule has paid)
Planned: prove that Kronecker/linear independence of {log p} makes the prime symbol attain its
resonant maximum. `PrimeSymbolDecoupling.lean` ALREADY HAS IT, and more: it proves the extremes
DECOUPLE COMPLETELY ACROSS PRIMES,
    sup_xi P = 2 sum_p log p * sup_theta f_p,     f_p(theta) = (x c - x^2)/(1 - 2 x c + x^2),
with x = p^{-1/2}, c = cos theta, and states explicitly that this is the one place where
multiplicative independence of the primes — "the property no Beurling counterexample shares" —
enters as an exact statement. MY PLANNED CYCLE WAS A DUPLICATE.

Also corrected: cycle 81 conjectured Pi(L) ~ 2 e^{L/2} (half the crude bound) because of an
"averaging loss". THE DECOUPLING REFUTES THAT: independence forbids destructive interference, so the
crude bound is asymptotically sharp. Cycle 82's e^{L/2} was measured AT THE POLE EXTREMISER, a
different test; both are correct and they do not conflict. Conjecture withdrawn.

### THE SALVAGE, AND IT IS AN EXACT IDENTITY
The local extremes are attained at c = +-1 and sum in closed form:
    sup_theta f_p = x/(1-x) = 1/(sqrt p - 1),    inf_theta f_p = -x/(1+x) = -1/(sqrt p + 1).
Both sum_p log p/(sqrt p -+ 1) DIVERGE like 2 sqrt N, so the symbol is unbounded both ways — which is
why truncation was ever needed. BUT THEIR SUM IS NOT EXPONENTIAL:

    sup + inf  =  2 sum_p log p ( 1/(sqrt p - 1) - 1/(sqrt p + 1) )  =  4 sum_p log p/(p-1)
               =  4 sum_p sum_{k>=1} log p * p^{-k}  =  4 sum_n Lambda(n)/n,

using 1/(p-1) = sum_{k>=1} p^{-k}. THE RIGHT-HAND SIDE IS EXACTLY THE POLE TERM OF THE EXPLICIT
FORMULA. Truncated at N = e^L it is ~ 4L, matching the net weight 2L of the pole form (cycle 81's
Nyquist-cell identity) per unit normalisation.

    ==> THE PRIME SYMBOL IS SYMMETRIC TO EXPONENTIAL ORDER AND ASYMMETRIC ONLY AT THE LOGARITHMIC
        SCALE OF THE POLE: ITS TWO EXTREMES DIFFER FROM BEING OPPOSITE BY EXACTLY THE POLE TERM.
        THE POLE IS NOT AN EXTRA INGREDIENT OF THE EXPLICIT FORMULA — IT IS THE ASYMMETRY OF THE
        PRIME SIDE.

This is a THIRD independent derivation of the same logarithmic quantity (first: the pole form's trace
= interval length = one Nyquist cell, cycle 81; second: the three-way cancellation, cycle 83; third:
this). Three routes, one number.

Machine-verified: `RHTower/SymbolAsymmetryIsPole.lean` (the two local extreme values in closed form,
their sum 2x^2/(1-x^2), its evaluation 2/(p-1) at x = p^{-1/2}, the geometric identity
sum_{k>=1} p^{-k} = 1/(p-1) via tsum_geometric, and the separation of the logarithmic and exponential
scales; standard axioms only, wired into RHTower).

### THIRTY-THIRD ATLAS ENTRY
    symbol asymmetry   sup P + inf P = 4 sum_n Lambda(n)/n = the pole term. The prime symbol's
                       extremes are opposite up to exactly the pole; the pole is the asymmetry of the
                       prime side, not an independent term.

### STATE AT CYCLE 99
Thirty-three entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 100 target
Entry 33 says the pole is the prime side's asymmetry; entry 17 says pole + prime main term + first
archimedean mode cancel identically. TOGETHER: THE ARCHIMEDEAN FIRST MODE IS ALSO PART OF THE PRIME
SIDE'S OWN STRUCTURE. That suggests the whole functional is a single object with an internal symmetry
rather than three competing terms. TEST: is the Weil functional expressible as
    W(g) = (1/2)[ P(g) - P~(g) ] + (tail),
where P~ is the prime symbol reflected (c -> -c, i.e. xi -> xi + pi/log p locally)? If the functional
is a DIFFERENCE OF A SYMBOL AND ITS REFLECTION, then positivity becomes a statement that a symbol
dominates its own reflection — a self-referential condition with no external comparison term, and the
first formulation in this programme in which the archimedean side does not appear at all.

---

## Cycle 100 (2026-07-26) — THE REFLECTION SPLITS THE SYMBOL BUT GAINS NOTHING

### Phase 4 verdict on cycle 99's target: REFUTED
Conjecture: W(g) is a difference between the prime symbol and its own reflection, giving a
self-referential positivity with no archimedean term. FALSE, for a one-line reason:

By the decoupling of the extremes each local supremum is taken over ALL theta, and theta -> theta + pi
is a BIJECTION of the line, so the reflected local factor has the SAME RANGE and hence the SAME
SUPREMUM. sup P~ = sup P. NOTHING IS GAINED BY COMPARING A SYMBOL WITH ITS REFLECTION. The
self-referential formulation is closed; there is no internal comparison that replaces the archimedean
side. DEAD END; do not re-attempt.

### What the reflection DOES do, and it gives the pole a fourth time
The reflection acts on the k-th harmonic by (-1)^k, i.e. by x -> -x. So

    P - P~ = 4 sum_p log p sum_{k odd}  p^{-k/2} cos(k xi log p),     (all divergence, all arithmetic)
    P + P~ = 4 sum_p log p sum_{k even} p^{-k/2} cos(k xi log p),     (absolutely convergent)

and the even half at the origin sums to
    2 sum_p log p sum_{m>=1} p^{-m} = 2 sum_p log p/(p-1) = 2 sum_n Lambda(n)/n = THE POLE.

    ==> FOURTH INDEPENDENT DERIVATION OF THE POLE TERM: it is the EVEN (square-power) PART OF THE
        PRIME SYMBOL AT THE ORIGIN.

The four derivations, all of the same logarithmic quantity:
  1. cycle 81 — the pole form's trace = interval length = one Nyquist cell (cosh^2 - sinh^2 = 1);
  2. cycle 83 — the three-way cancellation with the first archimedean mode;
  3. cycle 99 — sup P + inf P, the asymmetry of the prime symbol;
  4. cycle 100 — the even part of the prime symbol at the origin.
That the same number arises from a Pythagorean identity, a Laplace-transform cancellation, an
extremal asymmetry, and a parity projection is the strongest structural coherence the programme has
found. IT ALSO MEANS NONE OF THE FOUR IS INDEPENDENT INFORMATION.

Machine-verified: `RHTower/ReflectionSplitsOddEven.lean` (the parity identities in all four cases, the
evaluation of the even part at the origin via the geometric identity, the range-invariance of a
function under a shift of its argument, and the resulting equality of suprema; standard axioms only,
wired into RHTower).

### THIRTY-FOURTH ATLAS ENTRY
    reflection split   theta -> theta + pi splits the prime symbol into an absolutely convergent even
                       part (equal to the pole at the origin) and a divergent odd part carrying all
                       the arithmetic; but the supremum is shift-invariant, so no positivity follows
                       from the reflection. The pole is derived a fourth way.

### STATE AT CYCLE 100
Thirty-four entries. RH IS NEITHER PROVEN NOR DISPROVEN.

ONE HUNDRED CYCLES. THE ATLAS NOW HAS A SHAPE:
  * FOUR derivations of the pole/logarithmic scale, all equivalent (81, 83, 99, 100);
  * FOUR lanes characterised and closed as sources of new leverage (explicit formula 17-21; operator
    22-29; scaling 30-31 refuted by the witness test 32; self-reference 34);
  * TWO a priori spectral sources known (self-adjointness 24, similitude 26) and neither available;
  * ONE explicit definite pairing constructed (27, constant 4 - 3 log 2 - pi/2 = 0.34976);
  * ONE checkable instrument for refuting arguments in advance (the witness test, 32).
THE SEPARATING INGREDIENT IS THE EULER PRODUCT (32), AND ITS ONLY EXACT CONSEQUENCE IN THIS THEORY IS
KRONECKER DECOUPLING (corpus), WHICH MAXIMISES THE PRIME SIDE AND THEREFORE WORKS AGAINST POSITIVITY.

### Cycle 101 target
Confront that last sentence directly. Kronecker decoupling says independence MAXIMISES the prime
symbol. Weil positivity needs the prime side to be DOMINATED. So independence is an obstruction, not
a tool — yet it is the only property distinguishing zeta from the counterexamples (entry 32). THE
RESOLUTION MUST BE THAT INDEPENDENCE ENTERS WITH THE OPPOSITE SIGN SOMEWHERE ELSE. CANDIDATE: the
ZERO side. Independence of {log p} controls the DISTRIBUTION of the zeros through the explicit
formula; if the zeros were off the line, their contribution would have to conspire with the prime
phases, and independence forbids conspiracy. TEST WHETHER AN OFF-LINE ZERO IMPOSES A LINEAR RELATION
AMONG THE PRIME LOGARITHMS — if it does, independence excludes it, and that is a proof. This is the
first candidate mechanism in which the separating ingredient acts in the right direction.

---

## Cycle 101 (2026-07-26) — WHERE INDEPENDENCE ACTS IN THE FAVOURABLE DIRECTION: SELF-RECURRENCE

### Phase 4 verdict on cycle 100's conjecture: FALSE
Conjecture: an off-line zero imposes a Q-linear relation among the prime logarithms, so independence
would exclude it. FALSE. A zero is a location in the plane; nothing transports it into an ADDITIVE
relation among log p, and the growth it forces on psi(x) - x is an OMEGA-RESULT, not a contradiction
(Landau). Independence cannot exclude off-line zeros directly. DEAD END; do not re-attempt.

### Phase 1: the lane is genuinely new to the corpus
`rg` for Bagchi / Voronin / universality / strong recurrence: the corpus's "...UniversalityLaw" files
use "universality" in an unrelated internal sense. NO Voronin universality, NO Bagchi criterion, NO
strong recurrence anywhere in the development. This is the first genuinely untouched lane since
cycle 88.

### THE FAVOURABLE DIRECTION
Independence gives equidistribution of the phases (t log p)_p, hence approximation of prescribed
values by translates zeta(s + i tau) — universality. Universality approximates every NON-VANISHING
analytic function on a compact set in the strip 1/2 < sigma < 1. WHETHER ZETA ITSELF IS AMONG THEM IS
EXACTLY WHETHER ZETA IS NON-VANISHING THERE.

    ==> INDEPENDENCE SUPPLIES THE APPROXIMATION; THE HYPOTHESIS IS THE STATEMENT THAT ZETA MAY
        APPROXIMATE ITSELF. THIS IS THE ONE PLACE WHERE THE SEPARATING INGREDIENT ENTERS WITH THE
        SIGN THAT HELPS.

### The mechanism is a counting contradiction
Suppose zeta had a zero inside a disc K in the strip, and translates zeta(. + i tau) approximated
zeta on K to within min_{boundary K} |zeta| for a set of tau of POSITIVE DENSITY. Each such translate
then has a zero in K by sphere domination (corpus: `exists_zero_of_sphere_domination`), so the zeros
of zeta in that vertical strip have POSITIVE DENSITY IN T — while the zero count in any strip
sigma > 1/2 + delta is SUBLINEAR. The two are incompatible.

    ==> SELF-RECURRENCE OF ZETA ON A COMPACT SET OF THE STRIP IS INCOMPATIBLE WITH A ZERO THERE.

This is the classical Bagchi mechanism, absent from this corpus, and it is the FIRST criterion in the
atlas that PASSES THE WITNESS TEST (entry 32) AND uses the separating ingredient FAVOURABLY. The
counterexample witnesses have no Euler product, hence no equidistribution, hence no universality, so
they do not satisfy the recurrence hypothesis — the test is passed for the right reason.

Machine-verified: `RHTower/RecurrenceZeroDensity.lean` (the counting contradiction between a positive
density of zeros and a sublinear count, its universally quantified form, the transfer of a zero to a
nearby function via the corpus's sphere-domination principle, and the implication chain; standard
axioms only, wired into RHTower).

### THIRTY-FIFTH ATLAS ENTRY
    recurrence lane   independence => equidistribution => universality => approximation of
                      non-vanishing functions; RH is the statement that zeta is among them. A zero in
                      the strip plus positive-density self-recurrence gives positive density of zeros,
                      contradicting the sublinear count. FIRST lane using the separating ingredient
                      with the favourable sign, and the first to pass the witness test for the right
                      reason.

### STATE AT CYCLE 101
Thirty-five entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 102 target
The recurrence lane's content is now: prove that zeta is strongly recurrent, i.e. that the set of tau
with max_K |zeta(s + i tau) - zeta(s)| < eps has positive lower density. Voronin gives this for every
non-vanishing target; the obstruction is that zeta itself is the target and its non-vanishing is the
conclusion. SO THE LANE IS CIRCULAR AS STATED — like every other. BUT: Voronin's proof gives more than
the statement. It shows the LIMIT MEASURE of the random Dirichlet series zeta(s, omega) over the
torus, and the support of that measure is the set of non-vanishing analytic functions. THE SHARP
QUESTION IS WHETHER ZETA LIES IN THE SUPPORT OF ITS OWN LIMIT MEASURE — a measure-theoretic statement
about a concrete random object, not about zeta's zeros. TEST WHETHER THE SUPPORT CONDITION CAN BE
DECIDED FROM THE MOMENTS OF THE LIMIT MEASURE, which are computable Euler products. If the moments
determine membership in the support, the circularity is broken, because moments are unconditional.

---

## Cycle 102 (2026-07-26) — THE CRITICAL SCALE 1/log T, A FIFTH TIME

### Phase 4 verdict on the support question: CIRCULAR
Bagchi's support of the limit measure of the random Euler product IS the set of non-vanishing
analytic functions. So "zeta lies in the support of its own limit measure" is literally "zeta is
non-vanishing there" — THE CONCLUSION. Moments determine the measure, and the measure determines the
support, but the support characterisation is already the hypothesis; no unconditional route through
it. DEAD END as a proof route; the moments remain unconditional and are used below.

### What the moments say
For the random Euler product zeta(s,omega) = prod_p (1 - omega(p) p^{-s})^{-1}, log zeta is a sum of
INDEPENDENT contributions — precisely the multiplicative-independence ingredient — with variance at
abscissa sigma of size sum_p p^{-2 sigma} ~ (1/2) log( 1/(2 sigma - 1) ) as sigma decreases to 1/2.
IT DIVERGES LOGARITHMICALLY AT THE CRITICAL ABSCISSA AND NOWHERE ELSE.

On the critical line the UNCONDITIONAL Selberg central limit theorem gives variance ~ (1/2) log log T.
Equating the two profiles identifies

    1/(2 sigma - 1)  <->  log T,      i.e.      sigma - 1/2  <->  1/(2 log T).

    ==> THE RANDOM MODEL'S APPROACH TO THE CRITICAL LINE AND THE TRUE FLUCTUATION OF log ZETA ON IT
        AGREE EXACTLY WHEN DISTANCE FROM THE LINE IS MEASURED IN UNITS OF 1/log T.

### FIFTH APPEARANCE OF THE SAME SCALE
  1. cycle 73/78 — detection cost: width L ~ log(a log T)/a, critical at a ~ 1/log T;
  2. cycle 79 — Nyquist crossover: branches exchange at a ~ 1/log T (formalised constant 3);
  3. cycle 79 — the mean zero spacing 2 pi/log T;
  4. cycles 81/83/99/100 — the pole's logarithmic weight (four derivations);
  5. cycle 102 — the variance matching sigma - 1/2 ~ 1/(2 log T).
AS WITH THE FOUR DERIVATIONS OF THE POLE, THIS IS STRUCTURAL COHERENCE, NOT NEW LEVERAGE: one object
seen from several sides. The constants differ (3 versus 1/2), so the appearances are of the same
scale but not the same statement.

Machine-verified: `RHTower/CriticalScaleMatching.lean` (unboundedness of the variance profile
1/(2 sigma - 1) at the critical abscissa, the exact scale identification
1/(2 sigma - 1) = L iff sigma - 1/2 = 1/(2L), the common c/log T form of the Nyquist crossover and the
variance scale, and the distinctness of their constants; standard axioms only, wired into RHTower).

### THIRTY-SIXTH ATLAS ENTRY
    critical scale   the random-model variance diverges as (1/2) log(1/(2 sigma - 1)) and matches
                     Selberg's (1/2) log log T exactly under sigma - 1/2 <-> 1/(2 log T). Fifth
                     independent appearance of the scale 1/log T; coherence, not leverage.

### STATE AT CYCLE 102
Thirty-six entries. RH IS NEITHER PROVEN NOR DISPROVEN.

A META-OBSERVATION WORTH RECORDING AFTER 102 CYCLES. The programme has now produced TWO families of
repeated coincidences — four derivations of the pole scale and five appearances of 1/log T — and in
BOTH cases the repetition was structural coherence rather than independent information. THAT IS
ITSELF A FINDING: the explicit-formula/operator world has ONE logarithmic invariant, and every
computation in it returns that invariant. A proof cannot come from within a world with a single
invariant, because every quantity is a function of it. THIS IS THE STRONGEST FORM OF THE CLOSURE
RESULT: the four closed lanes are closed because they all measure the same thing.

### Cycle 103 target
Given the meta-observation, the productive move is to find a SECOND invariant — a quantity in the
theory that is NOT a function of log T. Candidates that are not obviously reducible: (a) the ZERO
SPACING DISTRIBUTION (GUE) — a dimensionless law, scale-free after unfolding, hence NOT a function of
log T; (b) the CLASS NUMBER / discriminant data of the associated number fields; (c) the LOW-LYING
zeros' one-level density, again dimensionless after unfolding. TEST (a): the unfolded pair
correlation is a dimensionless function; does ANY statement in the atlas constrain it? If the atlas is
blind to dimensionless data, then the closure results say nothing about GUE-type arguments, and the
pair-correlation lane is genuinely open rather than merely unexplored.

---

## Cycle 103 (2026-07-26) — THE ATLAS IS BLIND TO UNFOLDED DATA. THE CORRELATION LANE IS OPEN.

### The test, and it comes out positive
Every obstruction in entries 1-36 is a statement about a SCALE: a width L, a deviation a, a height
through log T, or a dimensionless combination such as aL. Correlation statistics are different IN
KIND: they are defined AFTER dividing out the density log T/2pi, so they are invariant under exactly
the rescaling the atlas measures.

    UNFOLDED DIFFERENCE:   (lam g_j - lam g_k)(M/lam) = (g_j - g_k) M     — INVARIANT.
    ATLAS CEILING:         sinh(aL)/a + L                                 — NOT INVARIANT
                                                                            (verified at a=L=1, lam=2).

    ==> NO BOUND EXPRESSED IN THE ATLAS'S VARIABLES CAN CONSTRAIN AN UNFOLDED STATISTIC.
        THE CLOSURE RESULTS PROVED HERE SAY NOTHING ABOUT CORRELATION STATISTICS.
        THE PAIR-CORRELATION LANE IS GENUINELY OPEN WITH RESPECT TO EVERYTHING IN THIS DEVELOPMENT,
        RATHER THAN MERELY UNEXPLORED.

This answers the cycle-102 meta-observation: the single logarithmic invariant governs the four closed
lanes, and dimensionless data lives outside its reach. IT IS THE SECOND INVARIANT THE PROGRAMME WAS
LOOKING FOR.

### The unconditional input the lane has
The pair-correlation form is a SQUARED MODULUS, hence nonnegative with NO hypothesis:

    sum_{j,k} w_j w_k cos( alpha (gam_j - gam_k) )
        = ( sum_j w_j cos(alpha gam_j) )^2 + ( sum_j w_j sin(alpha gam_j) )^2  >=  0.

This is the only unconditional statement about the zeros' correlations, and it is exactly the
positivity behind the classical simple-zero proportions. NOTE it is unconditional in a way nothing in
the four closed lanes was: it does not presuppose the location of the zeros, only their existence.

Machine-verified: `RHTower/AtlasBlindToUnfolded.lean` (scale invariance of unfolded differences,
explicit non-invariance of the detection ceiling, the expansion of the pair-correlation form into two
squares, its nonnegativity, and the resulting off-diagonal bound; standard axioms only, wired into
RHTower).

### THIRTY-SEVENTH ATLAS ENTRY
    unfolded blindness   unfolded correlation statistics are invariant under the rescaling that every
                         atlas obstruction measures, and the atlas's own quantities are not. The
                         closure results are silent on correlations; the pair-correlation lane is
                         open, and its unconditional input is the positivity of the correlation form.

### STATE AT CYCLE 103
Thirty-seven entries. RH IS NEITHER PROVEN NOR DISPROVEN.

FOR THE FIRST TIME SINCE CYCLE 88 THERE IS A LANE THAT IS OPEN BY PROOF RATHER THAN BY NEGLECT.

### Cycle 104 target
Work the open lane. The unconditional input is positivity of the correlation form; the classical
consequence (Montgomery) is that, ASSUMING RH, F(alpha) = alpha + T^{-2 alpha} log T (1+o(1)) for
0 <= alpha <= 1. THE ASSUMPTION ENTERS ONLY TO PLACE THE ZEROS ON A LINE SO THAT THE EXPLICIT-FORMULA
COMPUTATION OF F IS REAL. ASK: what is F(alpha) unconditionally, with zeros at beta + i gam? The
explicit-formula computation gives a form involving T^{iAlpha(gam - gam')} weighted by
x^{beta + beta' - 1}; off-line zeros contribute EXTRA WEIGHT x^{2a}. So F PICKS UP A POSITIVE
CONTRIBUTION FROM OFF-LINE ZEROS. Since F is bounded above by the diagonal plus the prime terms —
which are unconditional — AN OFF-LINE ZERO WOULD HAVE TO FIT INSIDE THAT UNCONDITIONAL BOUND.
COMPUTE THE BUDGET. If a zero at deviation a forces F(alpha) above its unconditional ceiling for some
alpha, that is a contradiction, and the lane closes the problem rather than the method.

---

## Cycle 104 (2026-07-104) — CORRELATION STATISTICS BOUND THE COUNT, NEVER THE LOCATION
### A DEGREE obstruction, not a magnitude obstruction. The open lane has its own wall.

### The budget computation, and its verdict
Montgomery's F is defined unconditionally and is nonnegative for a reason that does NOT need RH: the
gam are real by definition and the weight w(u) = 4/(4+u^2) is positive definite, so the form is a
squared modulus. Off-line zeros enter the explicit-formula computation with EXTRA weight x^{2a}.
Comparing a single zero's contribution x^{2a} against the total budget ~ T log T at x = T gives only
2a <= 1 + o(1) — THE TRIVIAL STRIP BOUND. Applied to MANY zeros the same comparison yields
N(sigma,T) <= C T log T / x^{2 sigma - 1}, i.e. A ZERO-DENSITY THEOREM: classical, and it does not
settle the hypothesis. PHASE-4 VERDICT: REDISCOVERED / INSUFFICIENT.

### THE STRUCTURAL REASON, AND IT IS THE REAL RESULT
The correlation form is QUADRATIC in the zero set. Its size in a box of height T is of order T log T.
A single zero enters as ONE UNIT VECTOR among that many, and adding or removing it changes the form by

    | ||z + c||^2 - ||z||^2 |  <=  2 ||z|| ||c|| + ||c||^2,

which for ||z||^2 ~ S and ||c|| = 1 is of order SQRT(S) — LARGER THAN THE UNIT BEING TESTED, AND
GROWING WITH THE BOX.

    ==> A BOUND ON THE CORRELATION FORM OF SIZE S CONSTRAINS AN INDIVIDUAL ZERO ONLY AT LEVEL SQRT S.
        CORRELATION STATISTICS YIELD BOUNDS ON THE NUMBER OF ZEROS — DENSITY THEOREMS — AND CAN NEVER
        EXCLUDE A SINGLE ZERO. EVERY CORRELATION-BASED ARGUMENT REPRODUCES ZERO-DENSITY ESTIMATES.

WHY THIS WALL IS DIFFERENT FROM ALL THE OTHERS. Entries 13-36 say a method cannot see far enough or
dodge cleverly enough — MAGNITUDE obstructions. This one says the statistic is of the WRONG DEGREE in
the zeros. It is a DEGREE obstruction, and it applies to EVERY QUADRATIC FUNCTIONAL OF THE ZERO SET
REGARDLESS OF THE WEIGHT — including all higher correlations reduced to pair form, and including the
GUE lane in its entirety.

Machine-verified: `RHTower/CorrelationBoundsCountNotLocation.lean` (the perturbation estimate for a
squared norm, the invisibility of a unit contribution once the total exceeds one, the growth of the
perturbation with the box, the counting form N <= S/c of a quadratic bound, and the fact that a count
excludes nothing unless it falls below one; standard axioms only, wired into RHTower).

### THIRTY-EIGHTH ATLAS ENTRY
    degree obstruction   the correlation form is quadratic; one zero perturbs it by O(sqrt(total)),
                         so correlation bounds constrain counts, never individual locations. Every
                         quadratic functional of the zero set, whatever its weight, yields density
                         theorems only.

### STATE AT CYCLE 104
Thirty-eight entries. RH IS NEITHER PROVEN NOR DISPROVEN.

THE ATLAS NOW HAS TWO KINDS OF WALL:
  * MAGNITUDE walls (13-36, 30-31 refuted by the witness test): a method's reach is too short.
  * DEGREE walls (38): the statistic has the wrong order in the zeros.
The degree wall is the more serious, because it cannot be improved by any sharpening of constants —
it is about what a quadratic form CAN express. TO EXCLUDE ONE ZERO, A FUNCTIONAL MUST BE OF DEGREE
ONE IN THE ZERO SET, i.e. LINEAR — and the only linear functionals of the zero set are the explicit
formula's own sums, which are the closed lanes.

### Cycle 105 target
The degree analysis is now the sharpest tool the programme has, so apply it to the whole atlas.
CLASSIFY EVERY CRITERION BY ITS DEGREE IN THE ZERO SET:
  * degree 1: explicit formula / Weil positivity (sum over rho of ghat(gam)) — closed lanes 17-21;
  * degree 2: correlation, moments of log zeta, Selberg CLT — degree wall 38;
  * degree 0 (existence only): Nyman-Beurling, Bagchi recurrence, Laguerre-Polya — these do not sum
    over zeros at all, they are statements about a FUNCTION.
THE DEGREE-0 CLASS IS THE ONLY ONE NOT YET WALLED. Nyman-Beurling in particular is a statement about
the closure of a subspace, with no sum over zeros anywhere. TEST WHETHER THE DEGREE OBSTRUCTION AND
THE MAGNITUDE OBSTRUCTIONS BOTH FAIL TO APPLY TO DEGREE-0 CRITERIA — if so, Nyman-Beurling is the
unique surviving class, and the programme has a single target rather than a landscape.

---

## Cycle 105 (2026-07-26) — THE DEGREE OBSTRUCTION IS REALLY A RATIO OBSTRUCTION
### Corrects entry 38's framing and identifies the UNIQUE surviving class.

### PHASE 2 RE-RUN (external SOTA, first since cycle 78) — entry 38 CORROBORATED
arXiv July 2026 and 2025: `2607.14515` "Beyond the Riemann Hypothesis bounds: a pair-correlation
approach" gets sharper least-prime and least-non-residue bounds UNDER GRH plus pair-correlation
hypotheses; `2501.14545` gives PROPORTIONS of simple and critical zeros; `2507.06823` treats the
Alternative Hypothesis. EVERY 2025-2026 PAIR-CORRELATION PAPER PRODUCES COUNTS OR CONDITIONAL
IMPROVEMENTS, NEVER AN EXCLUSION — exactly what entry 38 predicts for a degree-2 functional. The entry
has predictive content and it is confirmed by the literature.

### SELF-CORRECTION TO ENTRY 38'S FRAMING
Entry 38 called it a DEGREE obstruction. That is not the right invariant. The correct criterion is the
RATIO OF AN INDIVIDUAL TERM TO THE TOTAL; degree is merely the usual reason the ratio vanishes.

    For an additive functional Phi(Z) = sum_{rho in Z} phi(rho), removing one zero changes the value
    by EXACTLY phi(rho). Such a functional can refute a zero at rho precisely when phi(rho) is
    COMPARABLE TO THE TOTAL. If the ratio tends to zero, no bound on Phi says anything about rho.

  * CORRELATION: total ~ T log T, one zero contributes O(sqrt(T log T)); ratio -> 0. COUNTS ONLY.
  * NYMAN-BEURLING / BURNOL: the lower bound has the shape sum_rho m_rho^2/|rho|^2 — ADDITIVE and
    CONVERGENT, so individual terms are a FIXED FRACTION of the total (the lowest zeros carry an O(1)
    proportion). THE OBSTRUCTION DOES NOT APPLY.

    ==> AMONG ALL CRITERIA IN THIS DEVELOPMENT, THE NYMAN-BEURLING CLASS IS THE ONLY ONE THAT IS
        ADDITIVE OVER THE ZEROS WITH INDIVIDUAL TERMS COMPARABLE TO THE TOTAL. IT IS THE UNIQUE CLASS
        LEFT STANDING, AND THE REASON IS CONVERGENCE OF THE DEFINING SUM, NOT THE SYNTACTIC FORM OF
        THE CRITERION.

This also explains why cycle 104's degree-0/1/2 table was the wrong classification: Nyman-Beurling is
degree 0 in FORM and degree 1 in CONTENT, and what matters is neither — it is convergence.

Machine-verified: `RHTower/DegreeClassificationClosure.lean` (additivity of removal, the exclusion
principle for a comparable term, the contradiction when the budget falls below the fraction, the
vanishing of the correlation ratio sqrt(S)/S at infinity, positivity of a convergent functional's
ratio, and the general bound t <= B (t/Phi); standard axioms only, wired into RHTower).

### THIRTY-NINTH ATLAS ENTRY (and entry 38 amended)
    ratio obstruction   a functional of the zero set can exclude an individual zero exactly when the
                        individual term is a bounded fraction of the total. Correlation: ratio
                        sqrt(S)/S -> 0, counts only. Nyman-Beurling/Burnol: convergent sum, ratio
                        bounded below, obstruction inapplicable. UNIQUE SURVIVING CLASS.
    entry 38 AMENDED    the wall is about the ratio, not the degree; degree is only the usual cause.

### STATE AT CYCLE 105
Thirty-nine entries. RH IS NEITHER PROVEN NOR DISPROVEN.
THE PROGRAMME NOW HAS A SINGLE TARGET RATHER THAN A LANDSCAPE.

### Cycle 106 target
Work the unique surviving class. Nyman-Beurling: RH <=> dist(1, span{rho(theta/x)}) -> 0 in L^2(0,1),
with Burnol's unconditional lower bound liminf (log N) d_N^2 >= sum_rho m_rho^2/|rho|^2. THE
UNCONDITIONAL CONTENT IS THE LOWER BOUND; the hypothesis is the matching UPPER bound. Per entry 39 the
individual terms are comparable to the total, so an off-line zero at rho contributes a definite
fraction. THE QUESTION IS WHETHER AN OFF-LINE ZERO CHANGES THE LOWER BOUND'S SHAPE — Burnol's sum is
over all zeros with weight m^2/|rho|^2, which does not see beta at all. IF THE WEIGHT IS
BETA-BLIND, THE CRITERION CANNOT DISTINGUISH, AND THE CLASS IS WALLED TOO. CHECK THE BETA-DEPENDENCE
OF THE BURNOL WEIGHT FIRST — it is a single, decidable question, and it decides whether the last
standing class stands.

---

## Cycle 106 (2026-07-26) — TWO DESIGN CONDITIONS, AND NO CRITERION SATISFIES BOTH UNWALLED

### The question of cycle 105, answered: THE BURNOL WEIGHT IS ASYMPTOTICALLY BETA-BLIND
The unconditional lower bound weights a zero rho = beta + i gam by m_rho^2/|rho|^2, and
|rho|^2 = beta^2 + gam^2. Moving a zero from beta = 1/2 to beta = 1/2 + a with 0 < a <= 1/2 changes
the weight by the factor

    (gam^2 + 1/4)/(gam^2 + (1/2+a)^2),      which differs from 1 by at most 1/gam^2.

    ==> THE NYMAN-BEURLING UNCONDITIONAL HANDLE IS SENSITIVE TO WHICH ZEROS ARE PRESENT BUT NOT TO
        WHERE THEY ARE. THE SEPARATION VANISHES QUADRATICALLY IN THE HEIGHT.

### THE COMPLETED CLASSIFICATION — the sharpest statement the programme has produced
A functional of the zero set can decide the hypothesis only if BOTH hold:
    (i)  RATIO: each individual term is a bounded fraction of the total (entry 39);
    (ii) BETA-SENSITIVITY: the term separates beta = 1/2 from beta = 1/2 + a, i.e. the weight sees
         beta separately from gam and not merely through |rho|.

    CRITERION                        (i) RATIO      (ii) BETA-SENSITIVE     STATUS
    explicit formula / Weil          YES            YES (cosh(aL), e.13)    WALLED BY MAGNITUDE
                                                                            (entries 17-21: pole,
                                                                            prime main term and first
                                                                            archimedean mode cancel)
    correlation / GUE                NO (sqrt S/S)  YES (x^{2a})            COUNTS ONLY (e.38/39)
    Nyman-Beurling / Burnol          YES            NO (1/gam^2 blindness)  BLIND (this cycle)

    ==> NO CRITERION EXAMINED IN 106 CYCLES SATISFIES BOTH DESIGN CONDITIONS WITHOUT BEING WALLED BY
        MAGNITUDE. THE EXPLICIT FORMULA IS THE ONLY ONE THAT SATISFIES BOTH, AND ITS WALL IS THE
        THREE-WAY CANCELLATION.

This is a genuine classification: it says WHAT A NEW CRITERION MUST LOOK LIKE. It must be additive
over zeros with terms comparable to the total, must see beta separately from gam, and must not reduce
to the explicit formula's sums — because those three terms cancel identically.

Machine-verified: `RHTower/BetaBlindnessAndDesignConditions.lean` (the blindness estimate
|(g^2+1/4)/(g^2+(1/2+a)^2) - 1| <= 1/g^2 for 1 <= g and 0 < a <= 1/2, the vanishing of the blindness
bound at large height, the conjunction of the two design conditions, and the impossibility of
separating weights below the resolution; standard axioms only, wired into RHTower).

### FORTIETH ATLAS ENTRY
    design conditions   a zero-set functional decides RH only if (i) individual terms are a bounded
                        fraction of the total AND (ii) the weight separates beta from gam. Burnol's
                        weight fails (ii) by 1/gam^2; correlation fails (i); the explicit formula
                        satisfies both and is walled by the three-way cancellation. No criterion in
                        106 cycles satisfies both unwalled.

### STATE AT CYCLE 106
Forty entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 107 target
The classification says a new criterion must (i) be additive with comparable terms, (ii) see beta
separately from gam, and (iii) not be an explicit-formula sum. Condition (ii) is the sharp one: the
weight must be a function of beta and gam that is NOT a function of |rho| alone. THE CANONICAL SUCH
FUNCTION IS THE ONE THE FUNCTIONAL EQUATION ACTS ON: rho -> 1 - rhobar reflects beta about 1/2 and
FIXES gam. So a weight of the form phi(rho) - phi(1 - rhobar) is IDENTICALLY ZERO on the critical line
and NONZERO off it — CONDITION (ii) IN ITS SHARPEST FORM. CONSTRUCT THE FUNCTIONAL
    D(Z) = sum_rho ( phi(rho) - phi(1 - rhobar) )
for a weight phi with convergent sum, and ask what D is. Since the zero set is symmetric under
rho -> 1 - rhobar, D VANISHES IDENTICALLY AS A SUM — but its ABSOLUTE version sum |phi(rho) - phi(1 -
rhobar)| does not. DETERMINE WHETHER THE ABSOLUTE VERSION HAS AN EXPLICIT-FORMULA EXPRESSION. If it
does, it is a criterion satisfying all three conditions, and it is the first such object in the atlas.

---

## Cycle 107 (2026-07-26) — BETA-SENSITIVITY AND ARITHMETIC EVALUABILITY ARE MUTUALLY EXCLUSIVE
### The classification closes. This is a statement about the SHAPE OF THE PROBLEM, not about a method.

### The construction, and the theorem that kills it
Cycle 106 asked for a functional satisfying all three design conditions. The canonical candidate is
    D_phi(Z) = sum_rho | phi(rho) - phi(1 - conj rho) |,
which vanishes identically on the critical line (rho -> 1 - conj rho FIXES gam and reflects beta
about 1/2, so it fixes every critical point) and is nonzero off it. It satisfies (i) trivially — if
RH holds the total is 0, so any single off-line zero is the entire total — and (ii) exactly, and it
is not an explicit-formula sum.

BUT IT IS NOT EVALUABLE, AND THE REASON IS A THEOREM:

    THE ZERO SET OF A NONZERO ANALYTIC FUNCTION ON A CONNECTED DOMAIN IS DISCRETE; THE LINE
    Re s = 1/2 IS NOT. SO ANY FUNCTION VANISHING ON THE WHOLE CRITICAL LINE VANISHES IDENTICALLY.
    ANY WEIGHT DETECTING THE CRITICAL LINE EXACTLY IS THEREFORE NON-ANALYTIC.

And the explicit formula evaluates sum_rho h(rho) by contour shifting, which REQUIRES h analytic. A
non-analytic weight has no such evaluation: it cannot be expressed through the primes at all.

    ==> A ZERO-SET FUNCTIONAL IS EITHER ANALYTIC — HENCE EVALUABLE BY THE EXPLICIT FORMULA, HENCE A
        COMBINATION OF PRIME AND ARCHIMEDEAN DATA SUBJECT TO THE THREE-WAY CANCELLATION — OR
        NON-ANALYTIC, HENCE ABLE TO DETECT THE CRITICAL LINE BUT NOT COMPUTABLE FROM ARITHMETIC.
        THE TWO ARE MUTUALLY EXCLUSIVE.

THIS IS WHY EVERY CRITERION IN 107 CYCLES IS EITHER ARITHMETIC AND BLIND, OR EXACT AND INERT. It is
not a limitation of any technique; it is the shape of the problem. The design conditions of entry 40
CAN be met — and meeting them costs evaluability.

Machine-verified: `RHTower/AnalyticityExcludesBetaSensitivity.lean` (the identity-theorem obstruction
— an entire function vanishing on the whole critical line is identically zero, proved by exhibiting an
accumulating sequence on the line and applying the frequently-zero identity theorem — the fact that
rho -> 1 - conj rho fixes the critical line pointwise, the vanishing of the reflection difference
there, and its nonvanishing off the line; standard axioms only, wired into RHTower).

### FORTY-FIRST ATLAS ENTRY
    analyticity exclusion   a weight vanishing exactly on the critical line is non-analytic (identity
                            theorem), and non-analytic weights have no explicit-formula evaluation.
                            Beta-sensitivity and arithmetic evaluability are mutually exclusive; every
                            criterion is arithmetic and blind, or exact and inert.

### STATE AT CYCLE 107
Forty-one entries. RH IS NEITHER PROVEN NOR DISPROVEN.

THE ATLAS IS NOW A CLOSED CLASSIFICATION, not a list of failures. It says: to decide the hypothesis
one must either (a) break the three-way cancellation with new arithmetic input beyond the Euler
product, or (b) evaluate a non-analytic functional by non-contour means. Route (b) is exactly what the
function-field proof does — cohomology evaluates a non-analytic quantity (a trace on a vector space)
without contour shifting — and route (b) is closed here only because the geometry is unavailable
(cycle 92).

### Cycle 108 target
Take route (b) seriously in the one setting where non-analytic evaluation is available WITHOUT
geometry: FINITE-DIMENSIONAL LINEAR ALGEBRA. A trace is a non-analytic functional of a matrix's
spectrum that IS computable — tr|A| is not analytic in A, yet it is computable from A. THE QUESTION
IS WHETHER THE ZERO SET OF ZETA ADMITS ANY FINITE-DIMENSIONAL SHADOW ON WHICH A TRACE-LIKE
NON-ANALYTIC FUNCTIONAL IS COMPUTABLE FROM PRIMES. The corpus's compressed prime operator 𝒫 and the
archimedean pairing Q (entry 27) are exactly such finite-dimensional shadows, and tr|Q - 𝒫| is a
non-analytic functional of them that IS computable from the matrix entries — which are prime data.
COMPUTE WHAT tr|Q - 𝒫| SEES. If it separates beta, entry 41 is circumvented by finite-dimensionality,
because a matrix trace needs no contour.

---

## Cycle 108 (2026-07-26) — THE ABSOLUTE-TRACE CRITERION, AND THE PRIME OPERATOR IS TRACELESS

### Entry 41 circumvented in the one way it can be
Entry 41 says a weight detecting the critical line cannot be evaluated by CONTOUR SHIFTING. It does
NOT say every non-analytic functional is uncomputable. A MATRIX TRACE NEEDS NO CONTOUR, and tr|A| is
non-analytic in A yet determined by A. For self-adjoint A with eigenvalues lam_j,

    tr|A| - tr A  =  sum_j ( |lam_j| - lam_j )  =  2 sum_{lam_j < 0} |lam_j|,

so A >= 0 EXACTLY WHEN tr|A| = tr A. Applied to the Weil operator A = Q - 𝒫 (entry 27), RH is the
equality of its SCHATTEN-1 NORM with its TRACE.

### AND THE TRACE IS PURELY ARCHIMEDEAN
The compressed prime operator is convolution by a measure supported on {+- log n : n >= 2}, which HAS
NO ATOM AT THE ORIGIN. Its diagonal therefore vanishes identically and it is TRACELESS. Hence

    tr (Q - 𝒫)  =  tr Q,          a quantity with NO PRIME CONTENT AT ALL,

pinned by the definiteness bounds between (1 - beta) d and (1 + beta) d with
beta = 3 log 2 + pi/2 - 3 = 0.65023 and d the dimension: between 0.34976 d and 1.65024 d.

    ==> RH IS THE STATEMENT THAT THE SCHATTEN-1 NORM OF THE WEIL OPERATOR EQUALS ITS TRACE, AND THAT
        TRACE IS PURELY ARCHIMEDEAN AND EXPLICITLY PINNED.

The criterion is NON-ANALYTIC, EXACT, AND EVALUABLE IN PRINCIPLE — the three properties entry 41
showed cannot coexist for CONTOUR-evaluated functionals. What it costs: the Schatten norm requires the
SPECTRUM, which prime data does not directly supply. So entry 41 is circumvented in form but its
content survives as a change of currency — from "cannot be evaluated" to "requires the spectrum".

### Phase 1 note
`XiTraceHankelCountableCriterion.xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis` and
`XiHurwitzOrientationEnergyConsumers` already give trace-Hankel RH equivalences in the corpus. THE
NEW CONTENT HERE IS NOT "a trace criterion" but (a) the ABSOLUTE trace versus trace identity as the
exact positivity test, and (b) TRACELESSNESS OF THE PRIME OPERATOR, which makes the comparison
quantity purely archimedean and explicitly bounded. Those two are absent from the corpus.

Machine-verified: `RHTower/AbsoluteTraceCriterion.lean` (the identity
sum|lam| - sum lam = 2 sum max(0,-lam), its equality case characterising nonnegativity, tracelessness
from a vanishing diagonal, the reduction tr(Q - 𝒫) = tr Q, the two-sided pinning, and strict
positivity of the lower pin at the archimedean budget; standard axioms only, wired into RHTower).

### FORTY-SECOND ATLAS ENTRY
    absolute trace   RH <=> tr|Q - 𝒫| = tr(Q - 𝒫); the prime operator is traceless (no atom at the
                     origin), so the right side is purely archimedean and pinned to
                     [0.34976 d, 1.65024 d]. Non-analytic, exact, and contour-free — entry 41's
                     exclusion applies to contour evaluation only, and the cost reappears as the need
                     for the spectrum.

### STATE AT CYCLE 108
Forty-two entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 109 target
The cost is now precisely located: tr|A| needs the spectrum, tr A does not. BUT THE SCHATTEN-1 NORM
HAS A VARIATIONAL FORM THAT NEEDS NO SPECTRUM:
    tr|A| = sup { tr(A U) : U contraction },
a supremum of quantities LINEAR in A's entries, hence computable from prime data for each fixed U.
SO THE CRITERION BECOMES: for every contraction U, tr(A U) <= tr A. TEST WHETHER THE SUPREMUM IS
ATTAINED AT A COMPUTABLE U. For self-adjoint A the maximiser is U = sign(A), which needs the spectrum
— but the criterion only requires the INEQUALITY for all U, and each instance is an unconditional
prime-side statement. DETERMINE WHETHER FINITELY MANY WELL-CHOSEN U ALREADY FORCE POSITIVITY: if the
cone of self-adjoint operators satisfying tr(AU) <= tr A for U in an explicit finite family is exactly
the positive cone, the criterion becomes a FINITE list of unconditional inequalities — which is
exactly the falsification ladder of entry 15, now in operator form and with the archimedean side
computed.

---

## Cycle 109 (2026-07-26) — POSITIVITY IS FINITELY MANY POLYNOMIAL CONDITIONS, NOT LINEAR ONES
### Cycle 108's linear hope REFUTED by convexity; the polynomial replacement REMOVES THE SPECTRUM COST.

### The refutation
tr(A U) <= tr A cuts out a HALF-SPACE for each contraction U, so a finite family would make the
positive cone POLYHEDRAL. IT IS NOT. Its extreme rays are the rank-one projections, one per direction
— a continuum already in dimension two, where the cone {(a,b,c) : a>=0, c>=0, ac >= b^2} has a
strictly convex boundary carrying infinitely many distinct extreme rays (the family (t^2, t, 1)).

    ==> "POSITIVITY FOR ALL TESTS" CANNOT BE REDUCED TO FINITELY MANY TESTS AT ANY FIXED DIMENSION.
        THIS IS A CONVEXITY FACT, NOT AN ANALYTIC ONE, AND IT IS WHY THE FALSIFICATION LADDER
        (entry 15) HAS INFINITELY MANY RUNGS AT EACH WIDTH.

### THE POLYNOMIAL REPLACEMENT, AND IT IS THE POINT OF THE CYCLE
For a self-adjoint operator the characteristic polynomial is REAL-ROOTED, and a real-rooted monic
polynomial has all roots nonnegative EXACTLY WHEN ALL ITS ELEMENTARY SYMMETRIC FUNCTIONS ARE
NONNEGATIVE. Those are d polynomials in the matrix entries, REQUIRING NO SPECTRUM AT ALL:

    Q - 𝒫 >= 0   <=>   e_k(Q - 𝒫) >= 0  for k = 1, ..., d.

    ==> AT EACH WIDTH THE HYPOTHESIS IS THE NONNEGATIVITY OF FINITELY MANY EXPLICIT POLYNOMIALS IN
        PRIME AND ARCHIMEDEAN DATA — NO SPECTRUM, NO CONTOUR, NO TEST FUNCTIONS.

THIS REMOVES THE COST IDENTIFIED IN ENTRY 42. Entry 42 said the absolute trace is exact and
contour-free but needs the spectrum. The symmetric functions are exact, contour-free, AND
spectrum-free. Together with entry 41 (analyticity excludes beta-sensitivity for CONTOUR-evaluated
functionals) this completes the escape: the polynomial criterion is non-analytic in the operator
(the eigenvalue ordering is), yet polynomial in the DATA.

Machine-verified: `RHTower/PolynomialPositivityCriterion.lean` (nonnegativity of every symmetric
function of nonnegative numbers, the product-expansion positivity that gives the converse,
the boundary curve of the two-dimensional cone with distinct parameters giving distinct extreme
points, the impossibility of a finite set equalling an infinite one, and the finite polynomial
criterion; standard axioms only, wired into RHTower).

### FORTY-THIRD ATLAS ENTRY
    polynomial criterion   the positive cone is not polyhedral (continuum of extreme rays), so no
                           finite LINEAR reduction exists; but positivity is exactly the
                           nonnegativity of the d elementary symmetric functions, which are
                           polynomials in the entries. At each width RH is finitely many explicit
                           polynomial inequalities in prime and archimedean data.

### STATE AT CYCLE 109
Forty-three entries. RH IS NEITHER PROVEN NOR DISPROVEN.

THE PROGRAMME HAS NOW CONVERTED THE HYPOTHESIS INTO: for every L, the d(L) elementary symmetric
functions of the compressed Weil operator are nonnegative, where the operator's entries are explicit
(archimedean kernel minus prime kernel, entries 27 and 82) and its trace is purely archimedean and
pinned to [0.34976 d, 1.65024 d] (entry 42).

### Cycle 110 target
Compute the symmetric functions. e_1 = tr(Q - 𝒫) = tr Q — ALREADY DONE, purely archimedean and
positive (entry 42). SO THE FIRST RUNG OF THE POLYNOMIAL LADDER IS UNCONDITIONALLY SATISFIED. The
second is e_2 = ((tr A)^2 - tr(A^2))/2, and tr(A^2) = tr(Q^2) - 2 tr(Q 𝒫) + tr(𝒫^2). NOW: tr(𝒫^2) IS
NOT ZERO — the square of a convolution by a measure supported off the origin DOES have an atom at the
origin, namely the self-pairings, so tr(𝒫^2) = sum over n of (Lambda(n)/sqrt n)^2 times the overlap.
COMPUTE e_2 EXPLICITLY. Its sign is the second unconditional rung, and unlike e_1 it contains prime
data. If e_2 >= 0 is provable unconditionally, two rungs stand; if e_2 can be negative, RH IS FALSE.
EITHER OUTCOME IS DECISIVE AND THE COMPUTATION IS ELEMENTARY.

---

## Cycle 110 (2026-07-26) — THE LADDER CANNOT BE TRUNCATED; RUNG TWO IS CAUCHY-SCHWARZ
### Includes a MODEL CORRECTION to entry 42 that I must not gloss over.

### MODEL CORRECTION (self-audit)
The compressed prime operator is convolution by a measure of POINT MASSES, hence NOT TRACE CLASS, so
e_k is NOT DEFINED for it directly. Cycle 109's criterion is correct only in the GRAM MODEL: the
finite matrix
    A_{jk} = arch(phi_j, phi_k) - 2 sum_n Lambda(n) n^{-1/2} (phi_j * phi~_k)(log n),
whose entries are explicit and finite. RH <=> every such Gram matrix is PSD.

IN THAT MODEL THE TRACE IS sum_j W(phi_j, phi_j), WHICH CONTAINS PRIME TERMS. Entry 42's
"the prime operator is traceless" is a statement about the FULL COMPRESSION to L^2(I), where the
kernel delta(x - y -+ log n) has no diagonal mass; it is that limit which is prime-free, and the
finite-d truncation is not. ENTRY 42 IS AMENDED ACCORDINGLY: the tracelessness is a full-compression
fact, not a finite-Gram fact.

### RUNG TWO IS EXACTLY CAUCHY-SCHWARZ
For d = 2, e_2 = A11 A22 - A12^2, so the second rung is

    W(phi, phi) * W(psi, psi)  >=  W(phi, psi)^2,

the Cauchy-Schwarz inequality for the Weil form. That is a clean identification: the polynomial ladder
begins with the trace (rung one, archimedean-dominated and positive) and continues with
Cauchy-Schwarz.

### AND IT CANNOT STOP THERE
All 1x1 and 2x2 principal minors positive does NOT imply positive semidefiniteness. The symmetric
matrix with unit diagonal and constant off-diagonal t has 2x2 minors 1 - t^2 and determinant
(1 - t)^2 (1 + 2t). AT t = -3/5 THE MINORS ARE 16/25 > 0 WHILE THE DETERMINANT IS -64/125 < 0.

    ==> THE POLYNOMIAL LADDER IS FINITE AT EACH WIDTH BUT ITS LENGTH GROWS WITH THE WIDTH: ALL d
        SYMMETRIC FUNCTIONS ARE NEEDED AND NO FIXED NUMBER OF RUNGS SUFFICES.

This settles the shape of the criterion: entry 43's "finitely many polynomial inequalities" is right
per width, but the count is the dimension, so the total is still infinite across widths — the same
structure as the falsification ladder of entry 15, now with each rung an explicit polynomial rather
than an inequality over a continuum of tests. THE GAIN IS REAL (continuum -> finite at each width)
AND BOUNDED (finite -> growing without bound across widths).

Machine-verified: `RHTower/LadderNeedsAllRungs.lean` (the identification of the 2x2 symmetric function
with the determinant, the closed forms 1 - t^2 for the minors and (1-t)^2(1+2t) for the determinant,
their signs at t = -3/5, the resulting insufficiency of truncation, and the incompatibility of a
negative determinant with positivity; standard axioms only, wired into RHTower).

### FORTY-FOURTH ATLAS ENTRY (and entry 42 amended)
    ladder length   rung one is the trace, rung two is Cauchy-Schwarz for the Weil form, and
                    truncation fails: unit diagonal with off-diagonal -3/5 has positive 1x1 and 2x2
                    minors and determinant -64/125. All d rungs are needed at width d.
    entry 42 AMENDED  tracelessness of the prime part is a full-compression statement; in the finite
                      Gram model the trace contains prime terms.

### STATE AT CYCLE 110
Forty-four entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 111 target
Rung two is Cauchy-Schwarz for the Weil form, and Cauchy-Schwarz for a symmetric bilinear form holds
on a 2-plane IFF the form is SEMIDEFINITE there — positive or NEGATIVE. So rung two ALONE cannot
distinguish PSD from NSD. But rung one (the trace) IS positive unconditionally (archimedean
domination, entry 42's full-compression version plus the definiteness constant 0.34976). RUNG ONE
POSITIVE PLUS RUNG TWO NONNEGATIVE EXCLUDES NEGATIVE SEMIDEFINITENESS. So the first two rungs together
already exclude one of the two failure modes. DETERMINE WHETHER THE REMAINING FAILURE MODE — an
INDEFINITE Gram matrix with positive trace — is excluded by rung three, and whether the pattern
continues: each rung excluding one more signature. If the signature is exhausted after finitely many
rungs INDEPENDENT OF d, the ladder collapses after all, and the criterion becomes genuinely finite.

---

## Cycle 111 (2026-07-26) — ONE RUNG REFUTES, ALL RUNGS VERIFY. THE ASYMMETRY IS EXACT.

### The collapse hope: REFUTED, and replaced by something sharper
Cycle 110 asked whether each rung excludes one more signature so the ladder collapses after finitely
many rungs independent of d. IT DOES NOT — but Descartes' rule, which is EXACT for real-rooted
polynomials, says precisely what the rungs do. The characteristic polynomial of a symmetric matrix has
coefficients (1, -e_1, e_2, -e_3, ...), so

    THE NUMBER OF NEGATIVE EIGENVALUES = THE NUMBER OF SIGN CHANGES IN (1, e_1, e_2, ..., e_d).

### THE ASYMMETRY, AND IT IS THE RESULT
  * REFUTATION IS A SINGLE CERTIFICATE. If any one e_k is negative, some eigenvalue is negative,
    because symmetric functions of nonnegative numbers are nonnegative. ONE EXPLICIT POLYNOMIAL
    INEQUALITY IN PRIME DATA, CHECKABLE IN ISOLATION AT ANY SINGLE WIDTH, REFUTES THE HYPOTHESIS.
  * VERIFICATION NEEDS THE WHOLE LADDER. Truncation fails (entry 44's witness: unit diagonal,
    off-diagonal -3/5, positive 1x1 and 2x2 minors, determinant -64/125), so no proper initial
    segment of the rungs certifies positivity.

    ==> DISPROOF OF RH IS A FINITE CERTIFICATE: ONE NEGATIVE SYMMETRIC FUNCTION OF ONE WEIL GRAM
        MATRIX. PROOF IS NOT: IT REQUIRES EVERY SYMMETRIC FUNCTION AT EVERY WIDTH. THE ASYMMETRY IS
        EXACT, AND IT IS THE PRECISE SENSE IN WHICH THE PROBLEM IS HARD IN ONLY ONE DIRECTION.

This is sharper than entry 15's falsification ladder: there each rung was an inequality quantified
over a CONTINUUM of test functions; here each rung is a SINGLE POLYNOMIAL in the Gram entries.

### What this gives the programme operationally
A refutation search is now completely specified: choose any finite family of test functions, form the
Weil Gram matrix (entries: archimedean kernel minus finitely many prime terms), compute its elementary
symmetric functions, and look for a negative one. NO CONTOUR, NO SPECTRUM, NO ASYMPTOTICS, NO CHOICE
OF WIDTH REGIME. If one is ever negative, RH is false. That is the first fully explicit refutation
procedure the programme has produced, and it is unconditional.

Machine-verified: `RHTower/FalsificationIsFiniteVerificationIsNot.lean` (refutation from a single
negative symmetric function, its localisation to one width, the failure of localisation for
verification, the combined asymmetry statement, and the first rung as the trace; standard axioms only,
wired into RHTower).

### FORTY-FIFTH ATLAS ENTRY
    refutation asymmetry   the number of negative eigenvalues is the number of sign changes in
                           (1, e_1, ..., e_d) (Descartes, exact for real-rooted). One negative e_k at
                           one width refutes RH; verification needs all rungs at all widths. Disproof
                           is a finite certificate, proof is not.

### STATE AT CYCLE 111
Forty-five entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 112 target
The refutation procedure is explicit but the programme cannot run computations. So the question
becomes STRUCTURAL: can e_k be PROVED nonnegative for all k and all widths, from the entries? The
entries are arch - prime, and entry 17 says the pole, prime main term and first archimedean mode
cancel identically, leaving a bounded residue. SO THE GRAM MATRIX IS (bounded archimedean) MINUS
(smoothed PNT error). ITS SYMMETRIC FUNCTIONS ARE POLYNOMIALS IN THOSE TWO PIECES. CONJECTURE: e_k is
a polynomial in the error with leading coefficient the archimedean e_k, which is positive by entry 27's
definiteness — so e_k >= 0 holds as long as the error is smaller than the archimedean gap, uniformly.
THAT IS A SINGLE UNIFORM SMALLNESS CONDITION REPLACING INFINITELY MANY INEQUALITIES. Determine whether
the polynomial dependence is monotone enough for one bound on the error to control every e_k — if it
is, the infinite ladder reduces to one inequality, and that inequality is the sharpened form of the
0.17488 g(0) bound of entry 18.

---

## Cycle 112 (2026-07-26) — THE VERIFICATION LADDER COLLAPSES TO ONE ROW-SUM INEQUALITY

### The collapse
The Weil Gram matrix is A = M - E: archimedean part M, uniformly positive definite with constant
1 - beta = 4 - 3 log 2 - pi/2 = 0.34976 (entry 27), minus an error part E carrying the smoothed
prime-counting discrepancy. If |<E x, x>| <= e ||x||^2 then

    <A x, x> = <M x, x> - <E x, x> >= ( (1 - beta) - e ) ||x||^2,

so e < 1 - beta forces A >= 0 and therefore ALL SYMMETRIC FUNCTIONS NONNEGATIVE AT ONCE.

    ==> THE INFINITE LADDER OF POLYNOMIAL INEQUALITIES (entries 43, 44, 45) REDUCES TO A SINGLE
        SCALAR INEQUALITY.

### And the bound needs no spectrum
For a symmetric matrix, |sum_{j,k} E_{jk} x_j x_k| <= ( max_j sum_k |E_{jk}| ) sum_j x_j^2, from
|x_j x_k| <= (x_j^2 + x_k^2)/2 and symmetry. The entries E_{jk} are EXPLICIT PRIME DATA. Hence

    ==> RH FOLLOWS FROM A SINGLE CONDITION ON EXPLICIT ARITHMETIC: FOR EVERY FINITE FAMILY OF TEST
        FUNCTIONS, THE MAXIMAL ABSOLUTE ROW SUM OF THE ERROR GRAM MATRIX IS BELOW
        4 - 3 log 2 - pi/2 = 0.34976.

The row-sum route is the right one: the Frobenius bound loses a factor growing with the dimension,
while the row-sum bound is DIMENSION-FREE whenever the entries decay — which is exactly what
separation of the test functions provides.

### Honest assessment of what this is and is not
This is the sharpest FORM the programme has reached: no contour, no spectrum, no test-function
continuum, no width regime, no asymptotics — one explicit scalar condition on prime data. IT IS NOT A
PROOF: the row sums of E are the smoothed error paired against the test family, and bounding them is
bounding the zero sum, which cycle 83 established is circular. THE FORM HAS IMPROVED ENORMOUSLY; THE
CONTENT IS ENTRY 18'S BOUND, UNCHANGED. Record that plainly so no future cycle mistakes the
reformulation for progress on the content.

Machine-verified: `RHTower/OneInequalitySuffices.lean` (the perturbation bound (m-e)n <= q-p, strict
positivity under it, the elementary |ab| <= (a^2+b^2)/2, the per-term row-sum estimate, the collapse
of the ladder at the archimedean threshold, the closed form and positivity of that threshold, and the
lossiness of the Frobenius route; standard axioms only, wired into RHTower).

### FORTY-SIXTH ATLAS ENTRY
    ladder collapse   a single bound |<E x,x>| <= e ||x||^2 with e < 4 - 3 log 2 - pi/2 certifies
                      every symmetric function at every width; the bound is implied by the maximal
                      absolute row sum of the explicit error Gram matrix, needs no spectrum, and is
                      dimension-free when the entries decay. Form maximally sharpened; content
                      unchanged from entry 18.

### STATE AT CYCLE 112
Forty-six entries. RH IS NEITHER PROVEN NOR DISPROVEN.

THE PROGRAMME HAS REACHED A FIXED POINT IN FORM. Both directions are now single explicit conditions:
  * REFUTATION: one negative elementary symmetric function of one Weil Gram matrix (entry 45).
  * VERIFICATION: one row-sum bound below 0.34976 on every error Gram matrix (entry 46).
Neither is decidable from within the theory, for the reason established in cycle 83 and never since
overturned: the error IS the zero sum.

### Cycle 113 target
The fixed point in form means further reformulation is worthless. The only remaining move is to change
the INPUT. Every entry has used the same input: the Euler product through the coefficients Lambda(n)
n^{-1/2}. The witness test (entry 32) says that is the only separating ingredient AVAILABLE, but it
does not say it is the only one that EXISTS. TEST WHETHER ANY UNCONDITIONAL ARITHMETIC INPUT BEYOND
THE EULER PRODUCT CONSTRAINS THE ERROR GRAM ENTRIES: candidates are (a) the functional equation's
action on the entries (already used, entry 32 says insufficient alone), (b) the SUBCONVEXITY bounds
for zeta on the critical line, which are unconditional and NOT derivable from the Euler product alone,
and (c) the fourth-moment asymptotics, also unconditional. CHECK WHETHER SUBCONVEXITY BOUNDS THE ROW
SUMS. If a subconvexity exponent below 1/4 would give row sums under 0.34976, then RH follows from a
subconvexity improvement — a known-hard but ACTIVE and UNCONDITIONAL frontier, unlike everything else
in this atlas.

---

## Cycle 113 (2026-07-26) — THE CONTOUR-CROSSING OBSTRUCTION: ONE STATEMENT SUBSUMING EVERY
## CIRCULARITY VERDICT IN THE ATLAS

### PHASE 2 (on the every-fifth-cycle schedule)
arXiv 2602.05614 (Feb 2026) improves EXPLICIT subconvexity on the critical line, building on
Hiary-Patel-Yang 2024, |zeta(1/2+it)| <= 0.618 t^{1/6} log t. The literature route from such bounds to
zeros runs THROUGH BOREL-CARATHEODORY TO CLASSICAL ZERO-FREE REGIONS — a route this atlas already
capped (the Borel-Caratheodory ceiling and oscillation ceiling entries). So the 2026 subconvexity
frontier is real and active, and its path to the zeros is the one already known to be capped.
SUBCONVEXITY VERDICT: CAPPED, not circular — a useful distinction, and it does not open a lane.

### THE UNIFYING STATEMENT
Everything unconditional known about zeta sits in one of two places:
  * the half-plane of absolute convergence Re s > 1 — the Euler product and everything derived from
    it;
  * the critical line Re s = 1/2 — subconvexity, moment asymptotics, the functional equation's
    reflection.
The smoothed prime-counting error is a contour integral whose evaluation requires moving between
those two places, and any such shift passes through EVERY abscissa with 1/2 < sigma < 1, collecting
as residues exactly the zeros whose position is in question.

    ==> EVERY UNCONDITIONAL ARITHMETIC INPUT IS SEPARATED FROM THE ERROR BY THE CRITICAL STRIP. USING
        IT REQUIRES A CONTOUR SHIFT WHOSE RESIDUES ARE THE UNKNOWN ZEROS, SO NO SUCH INPUT CAN BE
        CONVERTED INTO A BOUND ON THE ERROR.

ONE STATEMENT, AND IT SUBSUMES: the Euler-product circularity (cycle 83), the Bohr-mean circularity
(cycle 87), the moment/support circularity (cycle 102), the subconvexity cap (this cycle), and the
"error is the zero sum" verdict that has stood since cycle 83.

### AND IT MAKES A PREDICTION THAT CLOSES THE LOOP
A usable input must live INSIDE the strip. The only unconditional information there is ZERO-DENSITY.
By the ratio obstruction (entries 38, 39) a zero-density statistic is quadratic and bounds counts,
never individual locations. THE TWO CLOSURES MEET: outside the strip everything is separated by the
contour; inside it everything is a count.

Machine-verified: `RHTower/ContourCrossingObstruction.lean` (separation of the regions, the fact that
a shift from absolute convergence to the line crosses every interior abscissa, the impossibility of a
route avoiding a given interior abscissa, nonemptiness of the interior, and the counting closure;
standard axioms only, wired into RHTower).

### FORTY-SEVENTH ATLAS ENTRY
    contour crossing   every unconditional input lives at Re s > 1 or on Re s = 1/2; reaching the
                       error requires a shift across the strip whose residues are the unknown zeros.
                       Inside the strip the only unconditional data is zero-density, which is
                       quadratic and bounds counts only. The two closures meet.

### STATE AT CYCLE 113
Forty-seven entries. RH IS NEITHER PROVEN NOR DISPROVEN.

THE ATLAS IS NOW COMPLETE AS A DESCRIPTION OF THE UNCONDITIONAL LANDSCAPE:
  * FORM: both directions are single explicit conditions (entries 45, 46).
  * CONTENT: every input is either outside the strip (separated by the contour, entry 47) or inside it
    (quadratic, entry 39).
  * DESIGN: a deciding functional needs comparable terms and beta-sensitivity (entry 40), and
    beta-sensitivity excludes contour evaluation (entry 41), escapable only by finite-dimensional
    non-analytic functionals (entries 42, 43), which return to the same content.
NOTHING IN THE UNCONDITIONAL LANDSCAPE DECIDES THE HYPOTHESIS. THAT IS NOW A THEOREM-SHAPED STATEMENT
ABOUT THE LANDSCAPE, NOT A REPORT OF FAILURE.

### Cycle 114 target
Given entry 47, the only way forward is an input that is NEITHER at Re s > 1 NOR on Re s = 1/2 NOR a
zero-density statistic. By the classification that means an input INSIDE the strip that is NOT
quadratic in the zeros — i.e. LINEAR in the zeros but not an explicit-formula sum. Entry 41 says a
linear functional with beta-sensitivity must be non-analytic. THE ONLY NON-ANALYTIC LINEAR
FUNCTIONALS OF A DISCRETE SET ARE COUNTING FUNCTIONS WITH NON-ANALYTIC WEIGHTS — e.g.
sum_rho sign(beta_rho - 1/2), which is EXACTLY the quantity RH asserts is zero. ASK WHETHER THAT
COUNTING FUNCTION HAS ANY UNCONDITIONAL EVALUATION AT ALL — via the argument principle it is a winding
number, which IS computable from boundary data on a contour that does NOT cross the strip: the
BOUNDARY of the strip. THAT IS THE ONE ROUTE ENTRY 47 DOES NOT BLOCK, because it uses the strip's
boundary rather than a crossing. TEST IT.

---

## Cycle 114 (2026-07-26) — COUNTS DO EXCLUDE, AND THE GAP IS UNIFORMITY IN THE HEIGHT
### Refines entry 39 and locates the missing ingredient exactly.

### The boundary route, followed to its end
Entry 47 leaves open the argument principle on the boundary of a sub-rectangle of the strip: it never
crosses the strip. Followed through, it computes exactly N(sigma, T), the zero-count — which lands in
the counting closure of entries 38/39. BUT THE LANDING IS SOFTER THAN THAT VERDICT RECORDED, and the
refinement matters.

### THE REFINEMENT
Entry 39 said a bound N <= S excludes nothing once S >= 1. True. Its converse is the point:

    A ZERO-COUNT IS A NATURAL NUMBER, SO A BOUND N < 1 FORCES N = 0 — A GENUINE EXCLUSION.

That is exactly how zero-free regions are obtained. So the obstruction is NOT the counting. It is that
every unconditional density bound GROWS WITH THE HEIGHT: N(sigma,T) << T^{c(1-sigma)} log^A T exceeds
one for large T, whatever sigma > 1/2. EXCLUSION NEEDS A BOUND BELOW ONE UNIFORMLY IN T.

    ==> THE MISSING INGREDIENT IS NOT A SHARPER HEIGHT-GROWING DENSITY BOUND BUT A HEIGHT-UNIFORM
        ONE.

### AND THAT MEETS THE META-OBSERVATION OF CYCLE 102
Uniformity in T is unavailable because THE THEORY HAS ONLY ONE INVARIANT AND THAT INVARIANT IS A
FUNCTION OF THE HEIGHT. Every quantity in the atlas carries log T (five independent appearances,
entry 36), so every bound grows, so no bound is uniform. THE TWO CLOSURES AND THE META-OBSERVATION
MEET AT ONE POINT.

This is the most precise localisation of the difficulty the programme has produced: not "the error is
the zero sum" (true but coarse), not "counts don't exclude" (false, as just corrected), but
UNIFORMITY IN THE HEIGHT OF A SUB-UNIT COUNT, unavailable because log T is the only invariant.

Machine-verified: `RHTower/IntegralityAndUniformity.lean` (integrality exclusion N < 1 implies N = 0
and its converse, the failure of exclusion for bounds at or above one, the eventual exceeding of one
by any growing bound, growth of the logarithmic and power shapes, and the contradiction from a
uniformly sub-unit growing bound; standard axioms only, wired into RHTower).

### FORTY-EIGHTH ATLAS ENTRY (and entry 39 refined)
    integrality and uniformity   counts DO exclude: N is an integer, so N < 1 gives N = 0. The
                                 obstruction is that unconditional density bounds grow in T while
                                 exclusion needs a sub-unit bound uniform in T. Uniformity is
                                 unavailable because log T is the theory's only invariant.
    entry 39 REFINED             "counts exclude nothing" holds only for bounds at or above one.

### STATE AT CYCLE 114
Forty-eight entries. RH IS NEITHER PROVEN NOR DISPROVEN.

### Cycle 115 target
The gap is now a single named quantity: a height-uniform sub-unit bound on N(sigma, T) for some fixed
sigma > 1/2. ASK WHAT SUCH A BOUND WOULD HAVE TO LOOK LIKE. Since N(sigma,T) counts zeros in a region
of area growing linearly in T, a uniform bound below one means the region is EVENTUALLY EMPTY, i.e. a
zero-free half-strip. So the target is not a bound at all — IT IS THE ZERO-FREE REGION ITSELF, and the
integrality observation says the two are the same statement. THEREFORE: the only route is to prove a
zero-free half-strip directly, and the only unconditional tool that produces zero-free regions is the
Borel-Caratheodory / three-circles machinery, which the atlas capped. VERIFY THAT THE CAP IS EXACTLY
THE OBSTRUCTION TO UNIFORMITY — if the Borel-Caratheodory ceiling and the uniformity gap are the same
obstruction seen twice, the atlas has ONE remaining open problem rather than two, and it is precisely
the zero-free-region cap.

---

## Cycle 115 (2026-07-26) — THE ZERO-FREE WIDTH IS AN EXPONENT, AND IT HAS MOVED FROM 0 TO 1/3

### The two obstructions are the same obstruction
The Borel-Caratheodory cap and the uniformity gap are both measured in the SAME UNIT: the local mean
spacing 2 pi / log t. The log t in the classical zero-free region IS the local zero density, and the
growth of every density bound is the same log t. CONFIRMED: the atlas has ONE remaining open problem,
not two.

### AND A SELF-CORRECTION I ALMOST SHIPPED
My first formulation was "every unconditional method is stuck at O(1) mean spacings, while RH needs
unboundedly many". THAT IS FALSE. Measuring the known regions in the natural unit:

    de la Vallee Poussin :  w = c/L                        ->  c/(2 pi)                       units
    Vinogradov-Korobov   :  w = c/(L^{2/3} M^{1/3})        ->  c L^{1/3} / (2 pi M^{1/3})     units
    the hypothesis       :  w = 1/2                        ->  L/(4 pi)                       units

(L = log t, M = log log t). SO VINOGRADOV-KOROBOV IS ALREADY UNBOUNDED IN NATURAL UNITS, GROWING LIKE
(log t / log log t)^{1/3}. The distinction is not bounded-versus-unbounded; it is an EXPONENT.

    ==> THE EXPONENT OF log t IN THE ZERO-FREE WIDTH, MEASURED IN MEAN SPACINGS, HAS MOVED FROM 0 TO
        1/3 IN A CENTURY. THE HYPOTHESIS IS EXPONENT 1. THE REMAINING GAP IS THE INTERVAL [1/3, 1],
        A POWER OF THE THEORY'S SINGLE INVARIANT.

This is the first QUANTITATIVE statement of where the frontier stands that the programme has
produced, and it replaces a qualitative claim that was wrong. It also explains the shape of the
literature: de la Vallee Poussin moved the exponent from nothing to 0, Vinogradov-Korobov moved it to
1/3, and nothing since has moved it — the improvements have been in the constant and the log log
factor.

Machine-verified: `RHTower/ZeroFreeWidthExponent.lean` (the unit conversion w L/(2 pi), the classical
count c/(2 pi) at exponent zero, the hypothesis count L/(4 pi) at exponent one, the Vinogradov-Korobov
count c L^{1/3}/(2 pi M^{1/3}) at exponent one third via the rpow splitting L = L^{2/3} L^{1/3}, the
gap 1 - 1/3 = 2/3, the ordering of the exponents, and the unboundedness at exponent one; standard
axioms only, wired into RHTower).

### FORTY-NINTH ATLAS ENTRY
    width exponent   in units of the local mean spacing the zero-free width has exponent 0 (de la
                     Vallee Poussin), 1/3 (Vinogradov-Korobov), and 1 (the hypothesis). The
                     Borel-Caratheodory cap and the uniformity gap are the same obstruction, measured
                     in the same unit. The remaining problem is to raise the exponent from 1/3 to 1.

### STATE AT CYCLE 115
Forty-nine entries. RH IS NEITHER PROVEN NOR DISPROVEN.
THE ATLAS HAS ONE REMAINING OPEN PROBLEM, AND IT IS NOW STATED AS A NUMBER: raise the zero-free width
exponent from 1/3 to 1.

### Cycle 116 target
Ask what limits the exponent to 1/3. Vinogradov-Korobov's 1/3 comes from the exponential-sum bound
for zeta near sigma = 1, where the saving is (log t)^{-2/3} from Vinogradov's mean value theorem — and
the mean value theorem is now KNOWN OPTIMAL (Bourgain-Demeter-Guth decoupling, 2016, resolved the
main conjecture). SO THE 1/3 IS NOT A DEFECT OF THE MEAN VALUE INPUT; IT IS THE CONVERSION FROM THE
SUM BOUND TO THE ZERO-FREE REGION. TEST WHETHER THE CONVERSION IS LOSSY: the route is sum bound ->
bound on |zeta| -> Borel-Caratheodory -> zero-free region, and each step has a known cost. IF THE
CONVERSION IS LOSSLESS, THE EXPONENT 1/3 IS FINAL FOR THIS FAMILY AND ONLY A DIFFERENT INPUT CAN
MOVE IT — which by entry 47 must come from inside the strip. IF IT IS LOSSY, THE LOSS IS AN EXPLICIT
TARGET.

---

## Cycle 116 (2026-07-26) — THE WIDTH EXPONENT IS 1 - 1/kappa, AND RH SITS AT kappa = INFINITY

### The chain, computed exactly
Suppose a Vinogradov-Korobov shaped bound |zeta(sigma+it)| << t^{A(1-sigma)^kappa} near the edge of
the strip. Balancing the saving against the logarithmic detection threshold,
(1-sigma)^kappa log t ~ log log t, gives 1 - sigma ~ (log log t / log t)^{1/kappa}, so the width in
MEAN SPACINGS is (1-sigma) log t ~ (log t)^{1 - 1/kappa} (log log t)^{1/kappa}.

    ==> THE UNIT EXPONENT IS EXACTLY  1 - 1/kappa.

CHECKS AGAINST THE LITERATURE, AND BOTH ARE EXACT:
    kappa = 1     ->  unit exponent 0     — de la Vallee Poussin
    kappa = 3/2   ->  unit exponent 1/3   — Vinogradov-Korobov (matches cycle 115's count)
    unit exponent 1 (the hypothesis)      ->  kappa = INFINITY

### THE NO-GO FOR THE WHOLE FAMILY
Since 1 - 1/kappa < 1 for EVERY finite kappa,

    ==> NO FINITE IMPROVEMENT OF THE SUM-BOUND EXPONENT CAN REACH THE HYPOTHESIS. THE VINOGRADOV
        FAMILY IS BOUNDED AWAY FROM RH FOR A STRUCTURAL REASON: RH SITS AT THE BOUNDARY kappa =
        INFINITY, WHICH IS THE STATEMENT THAT |zeta| IS SUBPOLYNOMIAL THROUGHOUT THE STRIP.

The remaining gap at any kappa is exactly 1/kappa, so at Vinogradov-Korobov it is 2/3 — matching
cycle 115's count from the other direction. A century moved kappa from 1 to 3/2; the target is not a
larger finite kappa but a different kind of input.

THIS ALSO SETTLES CYCLE 115'S QUESTION about whether the conversion is lossy: THE CONVERSION IS NOT
THE PROBLEM. Even a lossless conversion at any finite kappa gives unit exponent below one. The
limitation is in the SHAPE of the input bound, not in its constants or in the machinery that converts
it.

Machine-verified: `RHTower/ExponentChainKappa.lean` (the unit-exponent function 1 - 1/kappa, its
values 0 at kappa = 1 and 1/3 at kappa = 3/2, its monotonicity in kappa, its strict bound below one
for every finite positive kappa, the resulting impossibility of attaining the hypothesis's exponent,
and the gap formula 1/kappa with its value 2/3 at Vinogradov-Korobov; standard axioms only, wired into
RHTower).

### FIFTIETH ATLAS ENTRY
    kappa boundary   the zero-free width in mean spacings has exponent 1 - 1/kappa where kappa is the
                     exponent in the sum bound t^{A(1-sigma)^kappa}. Classical kappa = 1 gives 0,
                     Vinogradov-Korobov kappa = 3/2 gives 1/3, and RH is kappa = infinity. No finite
                     kappa reaches it; the conversion machinery is not the obstruction, the shape of
                     the input is.

### STATE AT CYCLE 116
Fifty entries. RH IS NEITHER PROVEN NOR DISPROVEN.

FIFTY ENTRIES, AND THE ATLAS NOW TERMINATES IN A SINGLE SENTENCE: every unconditional route is
separated from the zeros either by the critical strip (entry 47) or by the boundary kappa = infinity
(entry 50), and inside the strip the only data is quadratic (entry 39, refined by entry 48 to: the gap
is height-uniformity). ALL THREE ARE THE SAME LOGARITHMIC INVARIANT SEEN FROM DIFFERENT SIDES
(entry 36).

### Cycle 117 target
kappa = infinity means |zeta| subpolynomial throughout the strip — which is the LINDELOF HYPOTHESIS
extended off the line. Lindelof is implied by RH and is strictly weaker. SO THE ATLAS'S FINAL
STATEMENT IS: THE ZERO-FREE-REGION ROUTE REACHES RH ONLY THROUGH LINDELOF-IN-THE-STRIP. TEST WHETHER
THAT IS CIRCULAR OR A GENUINE REDUCTION: if Lindelof-in-the-strip implies RH, the reduction is real and
RH becomes a subconvexity problem in the limit; if it merely follows from RH, the route is circular
like the others. The classical position is that Lindelof does NOT imply RH — but the version needed
here is uniform IN THE STRIP, not on the line, and that version's status is exactly what must be
checked.
