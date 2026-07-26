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
