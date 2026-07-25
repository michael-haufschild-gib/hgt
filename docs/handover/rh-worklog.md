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
