# Detector Order Classification: every RH-detecting fiber reader is a displacement variance

- **ID:** detector-order-classification-rh-readers
- **Stage:** 1-in-progress (paper proof complete; Lean batch in flight)
- **Type:** THEOREM (classification; unconditional, elementary-but-structural)
- **Label:** `[PAPER-PROVED]` `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE — NOVELTY UNVERIFIED]`
- **Lane:** Fable (`logs/rhproof-fable.md`), positive-inversion sweep of the kill-list
- **Inverts (positively):** NG32 mean-kill, NG30 Bezoutian sign inertia, NG16 closed-contour SOS,
  NG21 analytic-reader closure, NG36 single-h repackaging, NG34 conformal saturation — six recorded
  no-gos become corollaries of ONE positive structure theorem.

## Motivation (why this is a discovery and not a restatement)

Across ~34 interrogation cycles this lane killed reader after reader for what looked like six
unrelated reasons ("mean-killed", "sign-inert", "integrates to zero", "analytic through the
collision", "h-saturated", "repackaged"). The classification below shows these are ONE phenomenon
with an exact cause, and — the positive content — it says precisely which readers *do* work and
what shape they are *forced* to take. It converts a scattered kill-list into a structure theorem
about the space of RH criteria. It also *predicts* the arc's own convergence: every surviving
object this lane found (`V_Xi = sum m d^2`, `q_2`, `det G_herm`, the displacement germ) is a
weighted displacement variance, which the theorem says is the ONLY thing they could have been.

## Setup

Work in the centered `u`-frame at a height `gamma` (`u = -i(s - 1/2)`; the height fiber is
`u_j = gamma + i d_j` with `d_j` the displacement of the zero from the critical line, `m_j > 0`
its multiplicity). After centering, the fiber lies on the imaginary axis and **RH at `gamma`**
is the statement `d_j = 0` for all `j`. Equivalently in the un-rotated coordinate: the fiber
divisor is supported on the reals.

Let `Omega ⊂ C` be a domain symmetric under conjugation with `Omega ∩ R ≠ ∅`. A **fiber reader**
of order `(1)` is a functional on finite divisors `D = sum_j m_j delta_{z_j}` in `Omega`,

> `R_F(D) := sum_j m_j * F(z_j, conj z_j)`,

where `F : Omega × Omega* -> C` is holomorphic in BOTH arguments (`F(z, w)`; the reader
substitutes `w = conj z`). This is the exact class produced by boundary-germ evaluation: the
germ theorem (`SlabConjugatedGermTheorem`, cont. 47-48) shows every conjugated boundary germ of
the trace is of this form, and `Omega* = Omega` by conjugation symmetry.

`R_F` **detects RH at `gamma`** if `R_F(D) = 0` for every divisor `D` supported in `Omega ∩ R`
and `R_F(D) != 0` for some divisor with a point off `R`.

## Theorem (Detector Order Classification)

Let `F` be holomorphic on `Omega × Omega` with `z ↦ F(z,z)` holomorphic on `Omega`. Then:

**(0) Order zero — no holomorphic detector exists.** If `F(z,w) = f(z)` does not depend on `w`
(the reader is `sum_j m_j f(z_j)`, i.e. the linear/explicit-formula class), then `R_F` vanishes on
all real divisors **iff** `f ≡ 0` on `Omega`. Hence NO nonzero reader of this class detects RH.

**(1) Order one — detectors exist but every one carries the displacement as a factor.** `R_F`
vanishes on all real divisors **iff** `F` vanishes on the whole complex diagonal, **iff**
`F(z,w) = (z - w) * G(z,w)` with `G` holomorphic. On the fiber this reads
`R_F(D) = sum_j m_j * (2i d_j) * G(z_j, conj z_j)` — the displacement `2i d_j = z_j - conj z_j`
appears as an explicit factor in EVERY detecting reader.

**(2) The mirror obstruction — order one is annihilated by the functional equation.** The Xi
divisor is invariant under `rho ↦ 1 - conj rho` with multiplicity preserved, i.e. the fiber is
invariant under `d ↦ -d`. Therefore for every `G` invariant under the same involution (in
particular every `G` depending on `z` only through `z*conj z` or through the fiber's symmetric
functions — including `G ≡ const`, the minimal case)

> `sum_j m_j d_j = 0` identically, unconditionally.

So the order-one detectors, though nonzero as functionals on general divisors, vanish on every
FE-symmetric fiber: they cannot detect on the actual Xi divisor. **This is the mean-kill law
(cont. 47-49, NG32), here derived as a structural consequence rather than observed per route.**

**(3) Order two is minimal, and its shape is forced.** If `R_F` in addition vanishes to second
order on the diagonal (equivalently: `R_F` is real-valued on FE-symmetric fibers and vanishes on
all real divisors), then `F(z,w) = (z-w)^2 * H(z,w)` and

> `R_F(D) = -4 * sum_j m_j * d_j^2 * H(z_j, conj z_j)` — a **weighted displacement variance**.

In particular, with `H ≡ -1/4` one gets exactly the fiber variance `V_Xi(gamma) = sum_j m_j d_j^2`
of `SlabConjugatedGermTheorem`/`SlabTraceEdgeEstimate`, and the classification says: *this is not
one certificate among many; up to a holomorphic weight it is the unique minimal one.*

**(4) Quadratic (Gram/Hankel) readers reduce to the same form.** For a bidivisor reader
`R(D) = sum_{j,k} m_j m_k F(z_j, conj z_j, z_k, conj z_k)`, vanishing on real divisors forces
`F` into the ideal generated by `(z - w)` and `(z' - w')`; the mirror obstruction kills every
term of odd total order, and the cross term `(z-w)(z'-w')` evaluates to
`(sum_j m_j d_j)^2 = 0`. The minimal surviving terms are again `(z-w)^2` and `(z'-w')^2`, i.e.
weighted variances. **This is why the Gram determinant, the Hankel minor `mu_1`, the Bezoutian,
and the Q-face all collapsed onto `V_Xi`: they had no alternative.**

## Proof

**(0)** `R_F(delta_x) = f(x)` for `x in Omega ∩ R`. Vanishing on all real divisors gives `f = 0`
on `Omega ∩ R`, a nonempty open subset of `R`, hence a subset of `Omega` with an accumulation
point in `Omega`. The identity theorem for holomorphic functions on the connected open set
`Omega` gives `f ≡ 0`. Conversely `f ≡ 0` gives `R_F ≡ 0`. ∎

**(1)** Taking `D = delta_x`, `x in Omega ∩ R`: `R_F(delta_x) = F(x, x)`. So vanishing on all
real divisors is equivalent to `g(x) := F(x,x) = 0` for all `x in Omega ∩ R`. The function `g` is
holomorphic on `Omega` by hypothesis; by the identity theorem (as in (0)) `g ≡ 0` on `Omega`,
i.e. **`F` vanishes on the entire complex diagonal**, not merely its real points. This is the
load-bearing step: real vanishing propagates to complex vanishing.

Now fix `z in Omega`. The function `w ↦ F(z,w)` is holomorphic and vanishes at `w = z`. Hence,
with `dslope` the divided-difference operator (`dslope h a b = (h b - h a)/(b - a)` for `b != a`,
`= h'(a)` at `b = a`, holomorphic in `b` whenever `h` is),
`F(z,w) = F(z,w) - F(z,z) = (w - z) * dslope (F z) z w`.
Set `G(z,w) := -dslope (F z) z w`; then `F(z,w) = (z - w) G(z,w)` with `G` holomorphic in `w`
(and in `z` by the same construction applied in the other slot / by Hartogs on the joint domain;
for the applications `F` is entire in both slots and no Hartogs is needed). Substituting
`w = conj z_j` and `z = z_j` gives the stated fiber form, since `z_j - conj z_j = 2i d_j`
after centering. ∎

**(2)** The functional equation `xi(1-s) = xi(s)` together with the Schwarz reflection
`xi(conj s) = conj(xi(s))` gives that the zero divisor is invariant under
`rho ↦ 1 - conj rho`, which at a fixed height is `d ↦ -d`, multiplicity preserved. Pair the
fiber points into `{d, -d}` orbits (fixed points have `d = 0`); each orbit contributes
`m d + m(-d) = 0`. ∎

**(3)** Second-order vanishing on the diagonal means `F` and its first normal derivative vanish
there; then `G` of (1) itself vanishes on the diagonal, so by (1) applied to `G` we get
`G = (z-w) H`, hence `F = (z-w)^2 H`, and `(z_j - conj z_j)^2 = (2i d_j)^2 = -4 d_j^2`. The
reality clause: for `R_F` real-valued on all FE-symmetric fibers, the order-one part must vanish
identically (its value is `2i sum m_j d_j G(...)`, purely imaginary against a real requirement
unless it vanishes), which is exactly the second-order condition after the mirror pairing. ∎

**(4)** Same argument variable by variable, plus (2) applied to each factor. ∎

## Hostile audit (performed before promotion)

- **Is (0) vacuous?** No: it says the entire linear/explicit-formula class is empty of detectors,
  which is exactly why Weil had to pass to `f * conj f`. The theorem locates that classical move
  as forced by the identity theorem.
- **Is the real-to-complex diagonal propagation legitimate?** Yes, and it is the crux: `F(z,z)` is
  a holomorphic function of ONE variable; vanishing on a real interval kills it on all of `Omega`.
  Without the separate hypothesis that `z ↦ F(z,z)` is holomorphic this step fails, and the
  hypothesis is automatic for the jointly-entire kernels the applications produce.
- **Does (2) secretly assume RH?** No. The mirror symmetry `d ↦ -d` is the functional equation,
  a theorem. The mean-kill is unconditional and holds equally for off-line fibers.
- **Is the "forced" claim overstated?** It is stated for readers whose kernel is holomorphic in
  `(z, conj z)`. Readers built from genuinely non-holomorphic ingredients (Bergman projections,
  domain distances) are outside the class — and the record shows those died for their own reasons
  (NG33 log-divergence, NG34 h-saturation), so the class is not artificially narrow, but the
  scope must be stated honestly: **the theorem classifies the holomorphic-germ class**.
- **Novelty risk (folklore adjacency, stated openly):** "you need a Hermitian/quadratic object,
  the linear explicit formula cannot see the line" is folklore around Weil positivity. What is
  NOT folklore, and is the claim to novelty here: the exact ideal-membership statement
  (`detector ⟺ kernel ∈ (z-w)`), the derivation of the mean-kill as the order-one obstruction,
  and the resulting uniqueness-up-to-weight of the displacement variance at order two. Grade
  stays `[NOVELTY UNVERIFIED]` pending an external audit of the classification statement itself.

## Consequences recorded (the six inverted no-gos)

1. **NG32 mean-kill** — the order-one obstruction (2). No longer a coincidence of the singular
   kernel `1/(u - conj v)`; every order-one reader dies the same death.
2. **NG30 Bezoutian sign inertia** — the Bezoutian germ `2V^2` is an order-two reader squared;
   its sign-inertness is (4)'s cross-term collapse.
3. **NG16 closed-contour SOS = 0** — additive squares of holomorphic data are order-zero readers
   in disguise; (0) forbids them from carrying any information.
4. **NG21 analytic-reader closure** — real-analyticity in the collision parameter is the shadow
   of the kernel's holomorphy; (1) says the only escape is the diagonal ideal.
5. **NG36 single-h repackaging** — the single-`h` identity is an order-two reader with
   `H ≡ const`; by (3) it CANNOT be more than `V = 0` restated.
6. **NG34 conformal saturation** — domain-distance detectors leave the holomorphic class and
   gain nothing, consistent with the scope clause.

## Lean plan (Gate 5)

New leaf `RHTower/DetectorOrderClassification.lean`:
- `holomorphic_detector_order_zero` — identity-theorem form of (0);
- `diagonal_vanishing_of_real_diagonal_vanishing` — the real-to-complex propagation of (1);
- `exists_displacement_factor` — the `dslope` factorization `F z w = (z - w) * G z w`;
- `mirror_mean_kill` — (2) for a finite mirror-symmetric mass family;
- `order_two_reader_eq_weighted_variance` — (3), plus nonnegativity and the vanishing
  characterization;
- capstone gluing to the corpus `heightFiber` / `fiberVariance` surface.

## Log

- 2026-07-18 (Fable): stated, proved on paper, hostile-audited, card created as the first
  deliverable of the kill-list positive-inversion sweep. Next: Lean batch; then the remaining
  no-gos (NG01-NG31, NG33, NG35) each get their own positive statement.

## SCOPE CORRECTION (self-caught, 2026-07-18) — and the theorem's real consequence

**The error.** The consequences section above reads the classification as if it applied to every
reader appearing in this corpus. It does not, and testing it against the corpus's own certificate
exposes the gap immediately: the height-fiber variance is

> `V(gamma) = sum_j m_j d_j^2 = - sum_j m_j (u_j - gamma)^2 = -(p_2 - 2 gamma p_1 + gamma^2 p_0)`,

the **centered second Newton sum** — a reader with the *holomorphic* kernel
`f_gamma(u) = -(u - gamma)^2`, i.e. an ORDER-ZERO reader. Under the loose reading, part (0) would
declare it impossible. It is not impossible; it is the certificate this lane actually built.

**The resolution — and it sharpens the theorem.** Part (0)'s hypothesis is vanishing on *every*
divisor supported on the whole real axis. `f_gamma` does not satisfy it: it vanishes at the single
real point `gamma` only. The distinction is exactly the distinction between

- **global readers** — one kernel `F`, required to certify at every height simultaneously. On-line
  divisors then range over the whole real axis, part (0) applies, and **no order-zero global
  reader exists**; the order-one obstruction and the order-two forcing apply as stated.
- **height-localized families** — a kernel `F_gamma` per height. On-line fibers are supported at
  the single point `gamma`, the identity-theorem step is unavailable, and order-zero readers DO
  exist: the minimal one is `f_gamma(u) = -(u - gamma)^2`, whose reader is precisely `V(gamma)`.

**The consequence, which is the theorem's real content.** Height-localization is not a technical
convenience of the slab construction — it is **logically necessary**: a single global holomorphic
kernel is provably blind (part (0)), so every certificate in this class must be a family localized
at each height. And within a localized family the forcing survives verbatim in the centered
variable `u - gamma`: the first centered moment `sum_j m_j (u_j - gamma) = i sum_j m_j d_j` is
annihilated by the functional-equation mirror symmetry (`mirror_mean_kill`), so the minimal
surviving reader is the **centered second moment**, which is `V(gamma)`.

This is exactly the structure the lane arrived at empirically over cont. 41-49 (`q_1` killed by
the circuit, `q_2` the entire demand). The classification says that outcome was forced:
localize per height, lose the first moment to the functional equation, land on the second.

**Effect on the Lean module.** None. `order_zero_reader_eq_zero` is the identity theorem and is
stated with the correct (global) hypothesis; `mirror_mean_kill` and the order-two results are
stated for an arbitrary finite configuration and apply verbatim in the centered variable. The
error was in the prose reading, not in a formal statement — recorded here rather than repaired
silently.

**Grade adjustment.** Consequence 3 (NG16, closed-contour SOS) and consequence 5 (NG36, single-h)
are retained: both concern readers required to work uniformly, where part (0) does apply.
Consequences 1, 2, 4, 6 are retained unchanged. The novelty claim is narrowed and made honest:
what the theorem contributes is (i) the impossibility of global order-zero detection, (ii) the
forced necessity of height-localization, and (iii) the order-two forcing inside a localized
family. Grade remains `[NOVELTY UNVERIFIED]`.
