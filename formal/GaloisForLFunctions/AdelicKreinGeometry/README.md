# Adelic Krein Geometry (AKG)

**Arithmetic signature theory: indefinite harmonic analysis on the adelic dilation–translation system.**

Namespace `GaloisForLFunctions.AdelicKreinGeometry`; umbrella `AdelicKreinGeometry.lean`.

**Question.** Every open problem of the corpus asks to pay an infinite-rank arithmetic debt through
one rank-one channel, the archimedean place, at zero margin and at the exponent `1/2`. Positive
harmonic analysis on `Aff(ℚ)` cannot do it (Weil's correlation carries no successor), and the
indefinite theory of the Weil kernel (HKT, AKL) lives on the multiplicative group alone, where local
assemblies have index `0` or `∞`. AKG asks for the geometry in between:

> *Which Hermitian forms of finite negative index live on the dilation–translation system
> `ℚ^×_{>0} ⋉ 𝔸 ⊃ Aff(ℚ)`, how is their index computed from prime towers glued at the archimedean
> place, and how do their additive (theta, successor, Haar) and multiplicative (Euler, Mellin,
> dilation) readings compare?*

Everything is unconditional; RH appears only inside equivalences.

---

## 1. Place in the research

The corpus diagnosis (`docs/reports/review-3010/obstacles-summary.md` §2.6): a crossing input must
be critical, square-root precise and selective at once; all coupling between primes, and between
addition and multiplication, passes through the archimedean place. Existing fields supply two of
the needed features each:

| Field | Supplies | Lacks |
|---|---|---|
| Hodge theory | index theorem at zero margin | finite rank, conformal Frobenius |
| Harmonic analysis on groups | Plancherel positivity | `+` and `×` are spectrally singular on `Aff(ℚ)` |
| Krein / Pontryagin spaces | exact negative indices, finite-rank perturbation | arithmetic producers of the index |
| Probability on the gauge torus | Kakutani dichotomies, zero–one laws | the trivial point |
| Analytic number theory | precision | spends a margin |

AKG is the field that combines the third with the first two: **indefinite** (finite negative index
replaces positivity), **affine** (both ring operations act), **adelic** (local factors at every
place, glued at `∞`).

| Programme | What AKG takes | What AKG adds |
|---|---|---|
| ArithmeticPositiveDuality | positive states on `Aff(ℚ)`, Hecke states, Kakutani wall, Mautner rigidity, Weil's correlation has a blind successor | the indefinite theory: what finite negative index changes |
| HeckeKreinToeplitz | kernels on groups, `negIndex`, orthogonal translates, index formula on `ℚ_{>0}` | index calculus on non-abelian groups: induction, escape, witnesses |
| ArithmeticKreinLangerTheory | Hasse principles on towers, zero-or-infinity for axis-supported kernels | zero-or-infinity laws for the affine and adelic systems |
| RenormalizedArithmeticPotentialTheory | matched local Hodge index at one prime, coupled survival | local–global signature calculus: gluing, shared polar hyperplanes, finite sieves |
| ArithmeticLorentzianGeometry | Frobenius is conformal, Hecke is a boost | the conformal symmetries of Pontryagin states |
| ArithmeticPolarization, HilbertianExplicitFormulas | `W` = collided form ⇔ RH; explicit formulas read only `W` | the additive–multiplicative comparison as a signature problem |
| SuccessorShellArithmetic, CriticalArithmeticCorrelationTheory | successor shells, conductor modes, complete Weil matrix | Ramanujan Plancherel on `ℤ̂` as the additive spectral side |

---

## 2. Why

**Over `𝔽_q` one object supplies everything.** The Frobenius graph on `C × C` carries the sign
(Hodge index), the count (`Γ_F·Δ = N₁`) and the selection; Frobenius is conformal with factor `q`;
all data live on one tower.

**Over `ℤ` the corpus has the pieces but not the object.**

- *Positivity is excluded on `Aff(ℚ)`.* A positive-definite state with Weil's dilation part has a
  blind successor; the integer successor forces Hecke decay `(nd)^{−1/2}` and a Kronecker-null
  dilation spectrum; a `ℤ`-periodic successor with continuous dilation part is constant (Mautner).
  The positive theory has no room for a successor-carrying carrier.
- *Indefiniteness is confined to `ℚ_{>0}`.* HKT/AKL compute the index of Weil's kernel on the
  multiplicative group; there the towers meet only at the identity, and tower-supported assemblies
  have index `0` or `∞`. The archimedean factor is the only off-tower constituent.
- *Local Hodge indices exist one prime at a time.* Matched against `log M − γ`, each prime form has
  one positive direction, the pole, with gap `→ p log p/(p − 1)`.
- *The two readings of the divisor are never compared.* The same-point form `S` is read from theta
  prefixes, `W` from primes; RH is `S = W`.

**What changes.** AKG treats the negative index as the invariant of an **indefinite affine state**,
computed by **localization** (local signatures at each prime, glued at `∞`) and compared between the
additive and multiplicative spectral sides. Its working hypotheses, each a theorem to prove or to
refute:

1. *Indefiniteness constrains the successor.* In the positive theory the successor coordinates are
   free; in the indefinite theory freeing them costs index.
2. *Arithmetic support forces a dichotomy.* States supported by the integer successor (Hecke
   support) cannot have finite nonzero index.
3. *Signatures glue through a shared polar hyperplane*, not through a shared positive vector.
4. *Conformal symmetry needs indefiniteness*: positive states admit no conformal automorphism with
   factor `≠ 1`; Pontryagin states do, and the arithmetic archimedean kernel sits at the conformal
   endpoint.

---

## 3. Objects and language

| Weil over `𝔽_q` | AKG object | Over `ℤ` |
|---|---|---|
| `C × C` with its intersection form | a **Pontryagin state**: Hermitian `φ : G → ℂ` with `κ(φ) < ∞` | `G = Aff(ℚ)` and its adelic completion |
| Frobenius tower | **dilation part** `φ ∘ dilation` | Weil's correlation `ratCorr` on `ℚ_{>0}` |
| additive structure of `𝔽_q[T]` | **successor** `b ↦ φ(x ↦ x + b)` | Haar state `1_ℤ`, Hecke states |
| local factor at a point | **local state** at `p` | `p`-adic factor of a Hecke state |
| Riemann–Roch ceiling | **gluing bound** | archimedean glue of finite rank |
| one positive class `H + V` | **polar hyperplane** shared by all local forms | pole moment `ℓ` |
| conformal Frobenius | **conformal automorphism** `φ ∘ α = λφ` | dilations acting on stable kernels |

**Words.**

- *Witness family*: a finite family on which the Gram matrix attains `κ(φ)`. *Witness complement*:
  the coefficient vectors `φ`-orthogonal to every witness point.
- *Escaping*: a translate `t` with `φ(x_a⁻¹ t y_b) = 0` for given finite families `x, y`.
- *Blind extension*: pullback along the slope homomorphism (constant successor). *Regular
  extension*: extension by zero off the dilations.
- *Hecke support*: `φ(x ↦ ax + b) = 0` unless `den(a)·b ∈ ℤ`.
- *Local defect*: negative squares of a local constituent. *Archimedean gluing*: the part of the
  form coupling different towers. *Gluing defect*: local negative squares cancelled by the glue.
- *Matched counterterm*: the scalar subtracted at each prime so that its form has one positive
  direction. *Shared polar hyperplane*: the common kernel of the pole moment.
- *Conformal factor*: `λ` with `φ ∘ α = λφ` for an automorphism `α`. *Conformal endpoint*: the
  exponent at which the factor becomes `1` with an additive anomaly.
- *Kakutani wall*: the exponent at which a local product state changes type.
- From the corpus: agreement/disagreement shells, coherent excess (pole), orientation, quantum,
  rate = depth, pre-ergodic regime.

---

## 4. Mechanisms

1. **Index under induction.** Pullback along a surjective homomorphism preserves the index; the
   extension by zero from a subgroup multiplies it by the number of cosets.
2. **Escape.** If every pair of finite families can be separated by a translate, a finite index is
   zero: the witness complement is positive, and translates of any family land in it.
3. **Arithmetic escape.** Translation by `1/P` for a large prime `P` separates every finite family
   from a Hecke-supported state.
4. **Shared polar hyperplane.** Local forms dominated by `−g_p‖x‖² + C_pℓ(x)²` with one common `ℓ`
   sum to a form with one positive square and gap `Σ g_p`; a common positive vector alone does not
   suffice.
5. **Gluing.** A positive glue of rank `r` cancels at most `r` local negative squares:
   `κ = Σ_p κ_p − g`, `0 ≤ g ≤ r`.
6. **Conformal rigidity.** An automorphism with factor `λ ≠ 1` kills every positive state; on
   Pontryagin states it forces homogeneity, realized by stable kernels `∓|b|^s`.
7. **Kakutani–Hellinger.** Local affinities of Poisson factors multiply; the product converges exactly
   on `σ > 1/2`.
8. **Ramanujan Plancherel.** On each finite level of `ℤ̂` the Ramanujan sums are the orthogonal
   basis of conductor-invariant functions; the Haar state is their constant mode.

---

## 5. Pillar theorems (targets)

A. **Index calculus on groups.** Witness complements are positive; escape forces `κ ∈ {0, ∞}`;
   pullback preserves `κ`; extension by zero multiplies `κ` by the index of the subgroup.

B. **The affine zero-or-infinity law.** Every Hecke-supported Hermitian function on `Aff(ℚ)` has index
   `0` or `∞`. The Kakutani wall is an index wall: the Hecke state of exponent `s` has index `0` for
   `s ≥ 1/2` and `∞` for `s < 1/2`.

C. **The Pontryagin extensions of Weil's correlation.** The least index of an affine extension of
   Weil's correlation is its dilation index, attained by the blind extension; the regular extension
   has index `0` or `∞`; every Hecke-supported extension of finite index is positive and forces RH;
   no Hecke-supported state of finite index has Weil's dilation part and the integer successor.

D. **Local–global signature calculus.** Shared-polar-hyperplane law; gluing formula; failure for a
   shared positive vector; the finite-sieve matched Hodge index.

E. **Conformal symmetry.** No positive state has a conformal automorphism of factor `≠ 1`;
   Pontryagin states on `ℚ` with conformal dilations are homogeneous; the arithmetic kernel is the
   conformal endpoint.

---

## 6. Traps

| Trap | Truth (to be established) |
|---|---|
| Successor coordinates are free | Only at index zero; the regular extension multiplies the index by the number of cosets |
| An indefinite carrier escapes the positive no-go theorems | A Hecke-supported carrier of finite index is positive |
| Matched local indices sharing the pole glue | Only a shared polar hyperplane glues; a shared positive vector does not |
| A finite-rank archimedean glue can absorb the prime debt | It cancels at most its rank |
| Conformal Frobenius has a positive analogue over `ℤ` | Conformal factors `≠ 1` need negative squares |
| The Kakutani wall is where `ℤ` differs from `𝔽_q` | Calibration: the same local wall over `𝔽_q[T]` |
| A new equivalence of RH is progress | A contribution computes, bounds or excludes an index |

---

## 7. Questions

1. Is there a signature formula expressing `κ(K_ζ)` as a sum of local prime defects minus an
   archimedean gluing term?
2. Do the matched local Hodge indices share one positive direction for every finite sieve, and what
   obstructs the infinite assembly?
3. Is there a Pontryagin state on the adelic system whose dilation part is Weil's correlation and
   whose successor is the Haar state at the critical temperature? Is its index `κ(K_ζ)`?
4. What replaces conformal Frobenius over `ℤ`?
5. Is there an integer invariant computable on the additive side that equals the number of off-line
   zeros (collision charge from theta prefixes; a Toeplitz index on `H²(𝕋^∞)`)?
6. Is there an exact sum-of-squares decomposition of the complete Weil form whose squares are
   indexed by successor-agreement shells?

---

## 8. Tools

Pontryagin index theory on groups; local–global signature calculus (matched counterterms, survival
cones, coupled survival); Kakutani–Hellinger dichotomies on the gauge torus; Mautner/Howe–Moore
phenomena for adelic `ax + b` systems; Bost–Connes/KMS states at the critical temperature;
Ramanujan sums as a Plancherel basis on `ℤ̂`; successor-shell calculus; Lyapunov methods for the
de Bruijn–Newman flow; quantitative linear independence of logarithms.

---

## 9. Success criteria and contributions

**The field is real, not a reformulation, when it has** (criteria of the field assessment):

1. intrinsic objects defined from `ℤ` without zeros;
2. a local signature theorem at each prime and a global gluing theorem;
3. an additive–multiplicative comparison theorem proved as an identity;
4. a conformal symmetry with factor `≠ 1`, or a proof that none exists and its substitute;
5. calibration: over `𝔽_q[T]` it reduces to Rosati positivity and Weil's theorem;
6. selectivity: it fails for twins, Beurling systems, continuous `Λ`-measures, higher-order poles;
7. edge control: renormalized limits keep a nontrivial null cone.

**A contribution** is an unconditional theorem about Hermitian forms of finite negative index on a
stated group or assembly. It names its local data and its glue, computes, bounds or excludes an
index (not a new RH equivalence), says what it gives over `𝔽_q` and for the twins, and records the
positive survivor of every no-go.

**Principles.** Index before sign. Localize, then glue at `∞`. Support decides type. Calibrate over
`𝔽_q`. A reformulation is not a reduction.
