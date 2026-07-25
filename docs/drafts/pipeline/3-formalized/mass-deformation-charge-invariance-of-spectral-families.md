# The mass deformation is a charge-preserving automorphism of the admissible spectral class

- **ID:** `mass-deformation-charge-invariance-of-spectral-families`
- **Stage:** 3-formalized
- **Type:** GENERAL LAW subsuming a Xi-specific construction / QUANTITATIVE FAITHFULNESS
- **Status:** `[PAPER-PROVED]` and `[LEAN-PROVED]`; `[NOVELTY UNVERIFIED]`
- **Parents (corpus):**
  - `formal/GaloisForLFunctions/HTGeometry/AbstractSpectralFamily.lean` (the admissibility interface)
  - `formal/GaloisForLFunctions/HTGeometry/PrincipalSquareRoot.lean` (`csqrt`, `csqrtRe`, `csqrtIm`)
  - `formal/GaloisForLFunctions/RHTower/XiMassShiftedFamily.lean` (`xiMassFamily`, the Xi instance)
  - `formal/GaloisForLFunctions/HTGeometry/AbstractSpectralDefect.lean` (`defect`, `energy`,
    `sq_im_le_of_defect_le`)

## 0. What the corpus has, and the exact residue

`XiMassShiftedFamily` builds one object: for the **Xi divisor only**, and using three Xi-specific
inputs — heights `> 3` (`three_lt_xiPoissonPoint_re`), the Xi shell finiteness, and the Xi weight
summability — it shows `beta_a(q) = sqrt(alpha_q^2 + a^2)` is admissible for `a >= 1/2`, and deduces
`riemannHypothesis_of_xiMassTrace_line_bound`.

Two things are missing and both are structural, not technical:

1. The construction is stated for one divisor. Nothing in it is about zeta.
2. It is **one-directional**. A line bound on the mass-shifted trace gives RH; nothing says how much
   information the deformation destroys. If the deformation crushed displacements by an unbounded
   factor, the prime-accessible criterion would be strictly weaker than the object it replaces, and
   every quantitative consequence (zero-free region, energy bound) would be lost in the passage.

The residue is therefore: *what exactly does `z -> sqrt(z^2 + a^2)` do to an admissible family, and
is any of the displacement information conserved?*

## 1. The law `[CONJECTURE -> PROVED BELOW]`

Let `F` be an abstract spectral family: points `p_i = R_i + i J_i` with `R_i >= base > 0`,
`|J_i| < 1/2`, `sum_i exp(-sigma R_i) < infinity` for every `sigma > 0`, finite height shells, and an
involution with `p_{inv i} = conj p_i`.

For `a >= 1/2` define the **mass deformation**

```text
(m_a F).pt i := csqrt (p_i^2 + a^2).
```

> **LAW.**
> **(A) Closure.** `m_a F` is again an abstract spectral family, with the same `base`, using nothing
> beyond the interface — in particular no height lower bound beyond `base > 0`.
> **(B) Conserved charge.** The **displacement charge**
> ```text
> chi_i(F) := Im (p_i^2) = 2 R_i J_i
> ```
> satisfies `chi_i(m_a F) = chi_i(F)` for every `a`. It vanishes for all `i` exactly when the family
> is real.
> **(C) Strict smoothing with an exact law.** Writing `R'_i = Re (m_a F).pt i`,
> ```text
> R_i < R'_i <= sqrt (R_i^2 + a^2),        Im (m_a F).pt i = chi_i / (2 R'_i).
> ```
> Hence displacements are strictly contracted, `|Im (m_a F).pt i| < |J_i|` unless `J_i = 0`.
> **(D) Bounded loss / faithfulness.**
> ```text
> |J_i| <= (sqrt (R_i^2 + a^2) / R_i) * |Im (m_a F).pt i| <= sqrt (1 + a^2 / base^2) * |Im (m_a F).pt i|.
> ```
> **(E) Semigroup.** `m_b (m_a F) = m_{sqrt (a^2 + b^2)} F`.

(A) makes the Xi construction one instance. (B)–(D) are the new content: the deformation is not a
lossy smoothing but a **reparametrisation of a conserved charge**, and the criterion it carries is
quantitatively equivalent to the original within the explicit factor `sqrt (1 + a^2/base^2)`.

## 2. Paper proof `[PAPER-PROVED]`

Throughout `z_i := p_i^2 + a^2`, so `Re z_i = R_i^2 - J_i^2 + a^2` and `Im z_i = 2 R_i J_i`.
Recall the corpus definitions `csqrtRe z = sqrt ((|z| + Re z)/2)` and `csqrtIm z = Im z / (2 csqrtRe z)`.

**(0) `csqrt` is a square root on the right half-plane.**  Let `Re z > 0` and put
`A = csqrtRe z`, `B = csqrtIm z`.  Then `A^2 = (|z| + Re z)/2 > 0` and, using
`(Im z)^2 = |z|^2 - (Re z)^2 = (|z| - Re z)(|z| + Re z)`,

```text
B^2 = (Im z)^2 / (4 A^2) = (|z| - Re z)/2,
A^2 - B^2 = Re z,     2 A B = 2 A * (Im z / (2A)) = Im z,
```

so `csqrt z ^ 2 = z`.

**(1) The argument stays in the right half-plane.**  `a >= 1/2 > |J_i|`, so `a^2 - J_i^2 > 0` and
`Re z_i > R_i^2 >= base^2 > 0`.

**(2) Heights strictly increase.**  `A_i^2 = (|z_i| + Re z_i)/2 >= Re z_i > R_i^2`, and `A_i >= 0`,
so `A_i > R_i > 0`.  (The first inequality is `Re z <= |z|`.)

**(3) Heights are capped.**  `|z_i| <= R_i^2 + J_i^2 + a^2`.  Indeed, with `u = R_i^2 + a^2`,

```text
(R_i^2 + J_i^2 + a^2)^2 - |z_i|^2 = (u + J_i^2)^2 - ((u - J_i^2)^2 + 4 R_i^2 J_i^2)
                                  = 4 J_i^2 (u - R_i^2) = 4 J_i^2 a^2 >= 0.
```

Therefore `A_i^2 <= ((R_i^2 + J_i^2 + a^2) + (R_i^2 - J_i^2 + a^2))/2 = R_i^2 + a^2`, i.e.
`A_i <= sqrt (R_i^2 + a^2)`.

**(4) The displacement law and the conserved charge.**  By (0), `Im ((m_a F).pt i ^ 2) = Im z_i =
2 R_i J_i = Im (p_i^2)`, which is (B).  Also

```text
Im (m_a F).pt i = csqrtIm z_i = Im z_i / (2 A_i) = R_i J_i / A_i = chi_i / (2 A_i),
```

which is the displacement law in (C).  With (2), `|R_i J_i / A_i| < |J_i|` unless `J_i = 0`, and
`Im (m_a F).pt i = 0` iff `J_i = 0` (as `R_i > 0`).  With (3),
`|R_i J_i / A_i| >= R_i |J_i| / sqrt (R_i^2 + a^2)`, which rearranges to (D); the uniform form uses
`R_i >= base` and monotonicity of `t -> sqrt (t^2 + a^2)/t`.

**(5) Admissibility of `m_a F`.**  `base_le`: `A_i > R_i >= base`.  `abs_im_lt`:
`|Im (m_a F).pt i| < |J_i| < 1/2` when `J_i != 0`, and `= 0 < 1/2` otherwise.  `summable_weight`:
`exp (-sigma A_i) <= exp (-sigma R_i)` for `sigma > 0` by (2), so comparison applies.
`shell_finite`: `{i : A_i <= C} subset {i : R_i <= C}` by (2).  `conj_stable`: `csqrt` commutes with
conjugation (corpus `csqrt_conj`) and `conj (p_i)^2 + a^2 = conj (p_i^2 + a^2)` since `a^2` is real;
hence `(m_a F).pt (inv i) = csqrt (conj z_i) = conj (csqrt z_i)`.

**(6) Semigroup.**  By (0) applied to `z_i` (legitimate by (1)),
`((m_a F).pt i)^2 + b^2 = z_i + b^2 = p_i^2 + (a^2 + b^2)`, so
`m_b (m_a F) = m_{sqrt (a^2 + b^2)} F` pointwise.  `QED`

## 3. Consequences

### 3.1 Subsumption

`xiMassFamily ha` has `pt q = csqrt (xiPoissonPoint q ^ 2 + a^2)`, which is exactly
`m_a (xiPoissonAbstract) .pt q`.  The Xi-specific height bound `3 < Re xiPoissonPoint` used in the
corpus proof is **not needed**: `base > 0` suffices.  The construction is therefore an instance of a
law about admissible families, not a fact about zeta.

### 3.2 The prime-accessible criterion is quantitatively faithful

The Xi Poisson family has `base > 3` (corpus `three_lt_xiPoissonPoint_re` gives `Re > 3` pointwise).
With `a = 1/2`, (D) gives, for every zero copy,

```text
|1/2 - Re rho| = |Im alpha_q| <= sqrt (1 + (1/4)/9) * |Im beta_{1/2}(q)| <= 1.014 * |Im beta_{1/2}(q)|.
```

So every displacement bound obtained from the **mass-shifted, prime-accessible** carrier transfers to
the actual Xi divisor with a loss of at most `1.4%`.  Combined with the corpus's
`sq_im_le_of_defect_le` this turns a defect bound for the mass-shifted trace into an explicit
zero-free region for zeta with an explicit constant.  Before this, only the degenerate case
(defect `= 0`) transferred.

### 3.3 What the invariant says about the programme

`chi = Im (p^2)` is conserved along the whole deformation, while both the height and the
displacement move.  The deformation is a genuine flow in `a`; the law says the flow has a complete
set of invariants, one per point, and RH is exactly `chi = 0`.  So no amount of smoothing can create
or destroy the obstruction: the mass parameter buys convergence of the prime side and nothing else.
That is the precise sense in which the object is fixed by a constraint (`chi_i = 0`) and not
propagated by the flow (`a`).

## 4. Hostile audit

- **FALSE?** Every step is an identity or an elementary inequality verified above with explicit
  algebra; the only inequalities used are `Re z <= |z|` and `4 J^2 a^2 >= 0`.
- **CIRCULAR?** No zero location is assumed anywhere; `a >= 1/2` uses only `|J| < 1/2`, which is the
  interface field, i.e. the trivial strip.
- **REDISCOVERED?** The map `z -> sqrt (z^2 + a^2)` is the classical relativistic dispersion / mass
  shell, and its half-plane mapping properties are elementary. What is not a restatement of that is
  (i) the identification of `Im (p^2)` as the exact conserved charge of the deformation, and
  (ii) the two-sided distortion bound that makes the prime-accessible criterion quantitatively
  faithful rather than merely sufficient. Elementary in proof; new as a statement about this class.
- **INSIGNIFICANT?** It upgrades a one-directional RH criterion to a two-sided one with an explicit
  constant, and removes a Xi-specific hypothesis from a construction that is really a law about
  admissible families.

## 5. Next generative move

The invariant `chi_i = Im (p_i^2)` is a per-point quantity that survives every mass deformation.
The next object to construct is the **charge-weighted trace** `sum_i chi_i exp(-tau p_i)` and to ask
whether it, unlike the plain trace, is prime-accessible at bounded resolution — the `1/delta` card
predicts it is not, and a proof either way is a decision about the whole detection programme.

---

## 6. The charge is neutral — a second law from the same object `[PROVED]`

Once `chi_i = Im (p_i ^ 2)` is named, a second law is forced by the interface field `conj_stable`.

> **LAW (charge neutrality).** Let `F` be an abstract spectral family with conjugating involution
> `inv`.  Then
>
> ```text
> chi (inv i) = - chi i,        Re (pt (inv i)) = Re (pt i),
> ```
>
> so for every real time `sigma > 0`
>
> ```text
> sum_i weight sigma i * chi_i = 0.
> ```
>
> More generally every summable `f` with `f (inv i) = - f i` has `sum_i f i = 0`.  In particular the
> trace is real on the positive axis: `Im (traceC sigma) = 0`.

**Proof.** `pt (inv i) = conj (pt i)` gives `Im ((pt (inv i))^2) = Im (conj (pt i ^ 2)) = - Im (pt i ^2)`
and `Re (conj z) = Re z`.  The weight depends on the point only through its real part, so
`weight sigma (inv i) * chi (inv i) = - weight sigma i * chi i`.  Since `inv` is a bijection of the
index set, reindexing the sum by it gives `S = -S`, hence `S = 0`.  Summability of
`weight sigma i * chi_i` follows from `|chi_i| < Re (pt i)` (charge coordinates, below) and
`t <= (2/sigma) exp(sigma t/2)`, comparing with the weight at `sigma/2`.  The same odd-reindexing
argument applied to `f i = Im (term sigma i)` gives reality of the trace.  `QED`

### 6.1 Charge coordinates `[PROVED]`

`|chi_i| < Re (pt i)` is *equivalent* to the interface bound `|Im (pt i)| < 1/2`, since
`chi_i = 2 Re(pt i) Im(pt i)` and `Re (pt i) > 0`.  So admissibility is not a normalisation choice:
it is the comparison of the charge with the height.  Along the mass deformation the charge is fixed
and the height strictly increases, so **admissibility is monotone in the mass**: a mass shift can
only create admissibility, never destroy it.

### 6.2 What neutrality explains

Neutrality is the abstract, unconditional form of the mechanism the `harmonic-invisibility` card
identifies analytically: no functional of the divisor that is *linear in the displacement* can be
nonzero, for any admissible family whatsoever.  The corpus's detection functionals — `defect`
(`1 - cos`), `energy` (second moment), the Hankel and Gram criteria — are all quadratic, and the law
says they had to be.  It also explains, in one line, why the trace is real on the positive axis, a
fact the corpus previously used only through the separate real-part computation.

This is a *no-go with an exact positive residue*: the first surviving displacement functional is the
quadratic one, and the corpus's `energy` is exactly it.

## 7. Lean status `[LEAN-PROVED]`

All statements below are unconditional (`#print axioms` gives only `propext`, `Classical.choice`,
`Quot.sound`), and `scripts/formal_tools.py lint --check-generated` passes.

| Statement | Declaration |
|---|---|
| Closure (A) | `HTGeometry.AbstractSpectralFamily.mass` |
| Charge invariance (B) | `HTGeometry.AbstractSpectralFamily.charge_mass` |
| Height increase / cap (C) | `re_lt_csqrtRe_massArg`, `sq_csqrtRe_massArg_le`, `csqrtRe_massArg_le_add` |
| Displacement law (C) | `re_mul_im_mass`, `csqrtIm_massArg_mul_csqrtRe` |
| Real locus preserved | `mass_im_eq_zero_iff` |
| Faithfulness (D) | `sq_re_mul_sq_im_le`, `sq_im_le_of_mass` |
| Criterion transfer | `im_eq_zero_of_mass_line_bound`, `im_eq_zero_iff_exists_mass_line_bound` |
| Defect transfer | `sq_im_le_of_mass_defect_le` |
| Semigroup (E) | `mass_mass_pt`, `mass_mass_pt_eq_mass_pt` |
| Charge coordinates | `HTGeometry.AbstractSpectralFamily.abs_charge_lt_re` |
| Odd-sum vanishing | `HTGeometry.AbstractSpectralFamily.tsum_eq_zero_of_inv_odd` |
| Charge neutrality | `HTGeometry.AbstractSpectralFamily.tsum_weight_mul_charge_eq_zero` |
| Trace real on the axis | `HTGeometry.AbstractSpectralFamily.im_traceC_ofReal_eq_zero` |
| `csqrt` is a square root | `HTGeometry.csqrt_sq`, `sq_csqrtIm`, `csqrtIm_mul_csqrtRe` |
| Xi: subsumption | `RHTower.xiMassFamily_pt_eq_mass_pt` |
| Xi: charge conserved | `RHTower.charge_xiMassFamily_eq` |
| Xi: faithfulness | `RHTower.nine_mul_sq_im_xiSpectralPoint_le` |
| Xi: zero-free region | `RHTower.sq_im_xiSpectralPoint_le_of_xiMass_defect_le` |
| Xi: criterion equivalence | `RHTower.riemannHypothesis_iff_exists_xiMassTrace_line_bound` |
| Xi: neutrality | `RHTower.tsum_xiPoissonWeight_mul_charge_eq_zero` |
| Xi: trace real | `RHTower.im_xiPoissonTraceC_ofReal_eq_zero` |

Files: `formal/GaloisForLFunctions/HTGeometry/AbstractSpectralCharge.lean`,
`formal/GaloisForLFunctions/HTGeometry/AbstractSpectralMass.lean`,
`formal/GaloisForLFunctions/HTGeometry/PrincipalSquareRoot.lean`,
`formal/GaloisForLFunctions/RHTower/XiMassFaithfulTransfer.lean`.

## 8. Novelty, bounded

- The inequalities are elementary; none of the individual steps is deep.
- `Im (p^2)` being conserved by `p -> sqrt(p^2 + a^2)` is immediate once stated, and the vanishing of
  a linear statistic of the zeros under `rho <-> 1 - rho` is classical.  Neither is claimed as new
  mathematics.
- What is corpus-new and, as far as the audit reached, not stated elsewhere in this form: the
  identification of `Im (p^2)` as *the* invariant of the whole deformation semigroup, the
  reformulation of admissibility as `|chi| < R`, the two-sided distortion bound that makes the
  prime-accessible criterion quantitatively faithful (previously only sufficient), and the fact that
  the Xi-specific mass construction needs none of its Xi-specific hypotheses.
- Label: `[LEAN-PROVED]`, `[NOVELTY UNVERIFIED]` pending independent priority audit.

## 9. Next generative move

Neutrality kills every linear charge functional.  The next object is therefore the *quadratic* charge
statistic `sum_i weight sigma i * chi_i ^ 2`, which is `4 * sum_i weight sigma i * R_i^2 J_i^2` — a
height-weighted energy that the mass deformation does **not** preserve (the heights move).  Its
deformation derivative in `a` is the first quantity in this calculus that is neither invariant nor
sign-definite for trivial reasons; computing it is the next concrete question.

---

## 10. Global faithfulness — the energies are comparable `[LEAN-PROVED]`

§3.2 compares displacements one zero at a time.  The same two ingredients — the height cap
`R' <= R + a` and the pointwise distortion bound — compare the *global* invariants.

> **LAW (energy comparability).** For every admissible family, every `a >= 1/2` and every
> `sigma > 0`,
>
> ```text
> base^2 * exp(-sigma a) * energy_F(sigma)  <=  (base^2 + a^2) * energy_{m_a F}(sigma)
>                                           and  energy_{m_a F}(sigma) <= energy_F(sigma).
> ```

**Proof.**  Upper bound: termwise, `weight' <= weight` (heights increase) and `|J'| <= |J|`
(displacements contract), so each energy term drops.  Lower bound: termwise,
`weight' >= exp(-sigma a) * weight` because `R' <= R + a`, and
`base^2 J^2 <= (base^2 + a^2) J'^2` is the pointwise distortion bound; multiplying the two and
summing over the index set — both series are summable by the interface — gives the claim.  `QED`

### 10.1 Consequence for the Xi divisor

With `base > 3`,

```text
9 * exp(-sigma a) * energy_Poisson(sigma)  <=  (9 + a^2) * energy_mass(sigma)  and
energy_mass(sigma) <= energy_Poisson(sigma).
```

So the prime-accessible mass-shifted energy and the Poisson energy of the Xi divisor are comparable
with explicit constants.  In particular RH is the vanishing of *either*, and a numerical or analytic
bound on the mass-shifted energy is a genuine zero-density and zero-free-region statement for zeta,
not only a criterion that triggers at zero.  This is what upgrades the mass shift from "a carrier
whose explicit formula converges" to "a carrier that keeps the information".

| Statement | Declaration |
|---|---|
| Energy decreases | `HTGeometry.AbstractSpectralFamily.energy_mass_le` |
| Energy loses only an explicit factor | `HTGeometry.AbstractSpectralFamily.energy_le_mass_energy` |
| Xi: both directions | `RHTower.xiMassEnergy_le_xiPoissonEnergy`, `RHTower.nine_mul_exp_mul_xiPoissonEnergy_le` |
| Xi: RH as vanishing mass energy | `RHTower.riemannHypothesis_iff_xiMassEnergy_eq_zero` |

All unconditional (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`);
`scripts/formal_tools.py lint --check-generated` passes.

## 11. Where this leaves the next question

The deformation now has: a conserved per-point charge, a monotone height, a contracted displacement
with two-sided control, a semigroup law, and comparable global energies.  Everything except the
charge moves, and everything that moves is controlled by `R < R' <= sqrt(R^2 + a^2)` — including
every further weighted charge moment, since those depend on the deformation only through the weight.
So nothing else in this calculus is open: the deformation is exactly a controlled reparametrisation,
and the loss factor `exp(-sigma a) * base^2/(base^2 + a^2)` is strictly decreasing in `a`, which
makes `a = 1/2` — the smallest mass for which the prime side of the explicit formula converges
absolutely — the information-optimal choice.

The open core is therefore *not* inside the deformation calculus.  It is:

> `[OPEN CORE]` Bound `energy_{m_a F}(sigma)` — equivalently the mass-shifted defect — from the
> arithmetic side.  The mass-shifted carrier is `exp(-tau sqrt(r^2 + a^2))`, whose Fourier transform
> is the Bessel kernel `2 a tau K_1(a sqrt(x^2 + tau^2)) / sqrt(x^2 + tau^2)`, decaying like
> `exp(-a x)`; for `a > 1/2` the prime series `sum_n Lambda(n) n^{-1/2} that-kernel(log n)` converges
> absolutely at real time.  What is *not* available is a bound uniform along a vertical line: at
> `tau = sigma + i t` the same series is absolutely divergent as `t -> infinity`, so the line
> criterion needs cancellation, not majorisation.  That divergence is the exact local form of the
> obstruction the `harmonic-invisibility-and-the-one-over-delta-law` card predicts.
