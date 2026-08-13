# Pole-purchase escape and the collision-gap law

- **ID:** ULF-INV-3
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / NECESSITY AXIOM N6 + AMPLIFICATION-GAP OPENING
- **Source:** lane-deep read of `RHTower/Sieve/CoefficientFreeCap.lean` executed against
  ULF-INV-2's open core
- **Statement:** The corpus's two cap laws are exact walls of the modulus category: a certified
  gap between a unimodular completely multiplicative sequence and the constant sequence exists,
  is elementary, and consumes exactly one invariant beyond moduli — the pole of the associated
  Dirichlet series at \(s=1\). The de la Vallée Poussin coupled-positivity engine is the
  \(t\ne0\) extension of the same purchase, lies outside both cap hypothesis classes, and in
  every world where an RH-analogue advanced, the mechanism is the same: zeros are purchased with
  poles of amplified objects. Necessity axiom N6: any engine beating the caps must consume pole
  data; the frozen barrier conjecture: bounded amplification degree bounds what poles can buy.
- **Status:** [PAPER-PROVED CORE] [CAP CLASSES READ FROM LEAN SOURCE] [N6 EXTRACTED]
  [BARRIER CONJECTURE FROZEN] [CLASSICAL COMPONENTS DISCLAIMED] [NOT RH] [LEAN CERTIFIED]

## 1. The cap laws, as formalized

From `RHTower/Sieve/CoefficientFreeCap.lean` (read in source, 2026-08-09):

- `le_of_coefficientFree_bound`: if \(\Phi(g)\le B\) for **every** completely multiplicative
  \(g\) with \(g(1)=1\), \(\|g\|\le1\), and \(B\) is a constant, then \(B\ge\Phi(\mathbf 1)\).
- `le_of_modulusOnly_bound` / `max_le_of_modulusOnly_bound`: if \(B\) depends on \(g\) only
  through \((\|g(n)\|)_n\), then \(B\) majorises \(\Phi\) at **both** members of any
  modulus-collided pair (unimodular \(f\) versus \(\mathbf 1\)): such a bound can never certify
  a gap \(\Phi(f)<\Phi(\mathbf 1)\).

These quantify over per-\(g\) majorants. Everything below is about what provably lives outside
that class.

## 2. The collision gap exists, and its price is one pole

### Theorem 2.1 — a certified modulus-collided gap

For \(\sigma>1\) let

\[
\Phi_\sigma(g)=(\sigma-1)\,\Bigl|\sum_{n\ge1}g(n)\,n^{-\sigma}\Bigr| .
\]

Let \(\lambda\) be the Liouville function (completely multiplicative, \(\lambda(p)=-1\),
unimodular, hence modulus-collided with \(\mathbf 1\)). Then

\[
\lim_{\sigma\to1^+}\Phi_\sigma(\mathbf 1)=1,
\qquad
\lim_{\sigma\to1^+}\Phi_\sigma(\lambda)=0 .
\tag{INV3.1}
\]

So the gap that `max_le_of_modulusOnly_bound` proves no modulus-only bound can certify is
nevertheless real and elementarily certified — by a functional that consumes exactly one
non-modulus invariant: the pole of \(\sum g(n)n^{-\sigma}\) at \(\sigma=1\).

#### Proof

\((\sigma-1)\zeta(\sigma)\to1\) since \(\zeta(\sigma)=\frac1{\sigma-1}+O(1)\). For \(\lambda\),
the Euler product gives, on \(\sigma>1\),

\[
\sum_n\lambda(n)n^{-\sigma}
=\prod_p\bigl(1+p^{-\sigma}\bigr)^{-1}
=\prod_p\frac{1-p^{-\sigma}}{1-p^{-2\sigma}}
=\frac{\zeta(2\sigma)}{\zeta(\sigma)},
\]

so \(\Phi_\sigma(\lambda)=(\sigma-1)\zeta(2\sigma)/\zeta(\sigma)
=\zeta(2\sigma)\,(\sigma-1)^2(1+o(1))\to0\). QED.

The corpus's Perron-layer record already knew single-frequency escapes exist ("a route needing
the damping at one frequency only would escape both"); Theorem 2.1 types the escape invariant:
it is the pole, and nothing else — the functional uses no zero, no distance, no cancellation.

### Theorem 2.2 — the coupled purchase at \(t\ne0\) (classical, retyped)

For \(\sigma>1\), \(t\in\mathbb R\):

\[
3\Bigl(-\tfrac{\zeta'}{\zeta}\Bigr)(\sigma)
+4\,\mathrm{Re}\Bigl(-\tfrac{\zeta'}{\zeta}\Bigr)(\sigma+it)
+\mathrm{Re}\Bigl(-\tfrac{\zeta'}{\zeta}\Bigr)(\sigma+2it)
=\sum_n\frac{\Lambda(n)}{n^{\sigma}}\bigl(3+4\cos(t\log n)+\cos(2t\log n)\bigr)\;\ge\;0,
\tag{INV3.2}
\]

since \(3+4\cos\theta+\cos2\theta=2(1+\cos\theta)^2\ge0\) and \(\Lambda\ge0\). If \(\zeta\) had a
zero of order \(m\ge1\) at \(1+it\) (\(t\ne0\)) and order \(k\ge0\) at \(1+2it\), then as
\(\sigma\to1^+\) the three terms behave as \(\frac{3}{\sigma-1},\ \frac{-4m}{\sigma-1},\
\frac{-k}{\sigma-1}\) up to \(O(1)\), forcing \(3\ge4m+k\ge4\), a contradiction: \(\zeta(1+it)\ne0\).

Two typed observations, which are the card's point:

1. (INV3.2) is a **lower** bound on a coupled combination of one functional at three
   frequencies, whose positive input is the source cone \(\Lambda\ge0\) and whose purchasing
   power is the pole term \(3/(\sigma-1)\). It is not a per-\(g\) majorant with sequence-free or
   modulus-only right side; neither cap hypothesis contains it.
2. The caps cannot be extended over it: any strengthened cap of the form "no engine certifies a
   modulus-collided gap" is **false** by Theorem 2.1, and any "coefficient-free bounds cap all
   engines" reading is false by (INV3.2)'s output. The cap laws are thus exact boundary stones
   of a category — the modulus/majorant category — and the minimal invariant beyond it is the
   pole. This is **necessity axiom N6**: any engine that beats the trivial size consumes pole
   data; the corpus's own zero-free-region layer is the degree-1 case.

## 3. The purchase pattern across the calibration worlds (cited, not proved)

- Rankin–Selberg bounds \(|a_p|\): purchased with the pole of \(L(s,f\times\bar f)\).
- Deligne's \(|\alpha|\le q^{w/2}\): the tensor-power trick — the trivial pole/invariant bound on
  \(H^0\) of \((\otimes^{2k})\)-objects, \(k\to\infty\); purity is pole-purchase at unbounded
  amplification degree.
- Kim–Sarnak \(7/64\): poles/analyticity of \(\mathrm{sym}^k\), \(k\le4\) — bounded degree,
  partial exclusion; the folklore chain "\(\mathrm{sym}^k\) automorphic for all \(k\) ⟹
  Ramanujan" is the unbounded-degree limit.

One mechanism in every world: **zeros are bought with poles of amplified family objects, and the
strength of the exclusion is the amplification degree afforded.** The corpus's caps are the
degree-0 statement (no purchase ⇒ trivial size); VP is degree 1; the ZFR-exponent memories
(κ-hierarchy, Littlewood, Vinogradov) grade the classical degrees.

## 4. Frozen barrier conjecture (ULF-INV-4)

> **Bounded-degree pole-purchase barrier.** In the corpus's framework there is a function
> \(\kappa(d)\) such that every engine whose positive input is the source cone and whose
> purchasing data are poles/analytic invariants of a fixed \(d\)-element twist/tensor family has
> zero-free-region exponent at least \(\kappa(d)\), with \(\kappa(d)\not\to\) below the corridor
> threshold: reaching \(\kappa<1\) requires unbounded families. If true: the corridor
> (Route E's wall) provably needs family input — the first corpus-derived theorem pointing all
> remaining single-object hope at the family direction. If false: a bounded-degree engine
> reaching \(\kappa<1\) exists, which would be an extraordinary constructive discovery.

`[OPEN CORE]` A definition of "engine of degree \(d\)" that (i) contains VP at \(d=1\) and the
classical trig-polynomial family, (ii) makes the corpus caps the \(d=0\) theorem, and (iii) is
closed under the operations the classical proofs use. First unprovable point: whether the
degree-1 barrier (the \(c/\log t\) ceiling for all nonnegative trigonometric polynomial weights)
can be made exact — the optimal-constant literature (Mossinghoff–Trudgian school; Kondratyev)
must be audited first, since the degree-1 statement may be implicit there.

## 5. Hostile scope

- Theorems 2.1/2.2 are classical in content (Euler product of \(\lambda\); de la Vallée
  Poussin); the additions are their exact typing against the Lean cap laws (read in source), the
  identification of the pole as the unique consumed invariant, the impossibility of extending
  the caps over pole-consuming engines, and the N6 extraction. If the corpus states N6 in this
  form anywhere, this card demotes to BRIDGE; the Perron-layer record's single-frequency remark
  is the closest prior form found and is quoted above.
- §3 is calibration with literature citations, not proof. §4 is frozen conjecture.
- Nothing here creates positivity or moves κ; the leverage claim is limited to: the escape
  hatch from the certified caps is now typed (pole data), matches the universal mechanism of
  the solved worlds, and yields a well-posed barrier target whose either resolution is new.

## Log

- 2026-08-09 — created after reading `CoefficientFreeCap.lean` in source; collision gap proved;
  VP retyped as degree-1 pole-purchase; N6 extracted; ULF-INV-4 frozen with its literature-audit
  precondition.
- 2026-08-12 — Theorem 2.1 fully formalized (`RHTower/PolePurchaseCollisionGap.lean`), together
  with the modulus collision, the falsity of the strengthened cap, and both ends of (INV3.2).  The
  (INV3.2) log-derivative identity itself remains open in Lean; card stays at stage 2.

## Lean certification (partial)

Module: `formal/GaloisForLFunctions/RHTower/PolePurchaseCollisionGap.lean`
(wired into `GaloisForLFunctions.RHTower`).

| Card statement | Lean name |
|---|---|
| §1 cap laws (pre-existing) | `RHTower.Sieve.le_of_coefficientFree_bound`, `le_of_modulusOnly_bound`, `max_le_of_modulusOnly_bound` |
| Thm 2.1, `Φ_σ(1) → 1` | `tendsto_poleFunctionalZeta` (from `riemannZeta_residue_one`) |
| Thm 2.1, `Φ_σ(λ) → 0` | `tendsto_poleFunctionalLiouville` (from the corpus's `LSeries_liouvilleC_mul_riemannZeta`) |
| Thm 2.1, the gap itself | `exists_collision_gap` |
| modulus collision of `λ` with `1` | `norm_liouvilleC`, `norm_liouvilleC_eq_norm_one` |
| §2.2 point 2, the strengthened cap is false | `exists_modulusCollided_gap` |
| (INV3.2) positive input | `vallee_poussin_identity`, `vallee_poussin_nonneg` |
| (INV3.2) conclusion `ζ(1+it) ≠ 0` | `riemannZeta_ne_zero_one_add_I_mul` |

`Φ_σ(1)` is the pole functional at the constant sequence; `poleFunctionalZeta_eq_lseries` identifies
it with `(σ−1)‖L(1, σ)‖` on the half-plane of absolute convergence, so the functional really is the
card's `Φ_σ` evaluated at `g = 1`.

**Closed 2026-08-13.**  The middle of (INV3.2) — the identity

`3(−ζ'/ζ)(σ) + 4 Re(−ζ'/ζ)(σ+it) + Re(−ζ'/ζ)(σ+2it) = ∑_n Λ(n) n^{−σ} (3 + 4cos(t log n) + cos(2t log n))`

— is certified in `RHTower/PolePurchaseLogDerivIdentity.lean` (wired into
`GaloisForLFunctions.RHTower`):

| Clause | Lean name |
|---|---|
| real part of one von Mangoldt line term `Λ(n) n^{−σ} cos(t log n)` | `re_vonMangoldt_line_term` |
| cosine-weighted summability at `σ > 1` | `summable_vonMangoldt_cos_weight` |
| `Re L(Λ, σ+it)` as the cosine-weighted series | `re_LSeries_vonMangoldt` |
| **the (INV3.2) identity itself** | **`vallee_poussin_log_deriv_identity`** |
| termwise nonnegativity of the 3–4–1 combination | `vallee_poussin_log_deriv_nonneg` |

The Dirichlet-series input is mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`; the line
kernels reuse `VonMangoldtLineSeriesSwap`.  `#print axioms` on every declaration reports only
`propext`, `Classical.choice`, `Quot.sound`.  With this the card's entire displayed Lean surface is
closed: §3 is calibration with citations, §4 (ULF-INV-4) is a frozen conjecture with a declared
open core — neither is a Lean gate.

§3 is calibration with literature citations, not proof.  §4 (ULF-INV-4) is a frozen conjecture with
a declared `[OPEN CORE]` and is a research frontier, not a Lean gate.
- 2026-08-13 — promoted: (INV3.2) log-derivative identity certified (RHTower/PolePurchaseLogDerivIdentity.lean, axiom-clean); full displayed surface now Lean-closed
