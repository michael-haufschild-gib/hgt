# Arithmetic symplectic descent: the Hilbert-symbol form as the symplectic structure the multiplicity ladder demands

- **ID:** ULF-SYMP-001
- **Stage:** 5-failed (T2 refuted on paper by three algebraic theorems, all in Lean)
- **Type:** CONJECTURE (mechanism, frozen before proof search)
- **Source:** `1-in-progress/multiplicity-parity-ladder-route.md` (open core: "construct, from
  Euler data, a symplectic structure on an operator model of the off-line divisor whose anomaly is
  line-supported"; Lean `rhLadder_iff_root`, `rhLadder_one_iff_symplecticRealization`,
  `even_finrank_maxGenEigenspace`), `ReflectionTateAnomaly` (free two-cycles cohomologically
  trivial), `GaloisMonoidDichotomyEndgame`, `prime-ising-tree-cavity-lee-yang`,
  `BakerWeldIndependence`, `SeamKreinStructure.graph_lagrangian`; the five 2026-09-02 no-go cards
  (`ULF-PIO/SLC/IND/ANC/INT-001`).
- **Statement:** The discrete doors visible in the corpus — divisibility of off-line orders
  (Kramers), reflection torsion, Galois-monoid dichotomy, exact finite Lee–Yang models, Baker
  independence — are shadows of one structure: the *alternating* pairing on the multiplicative
  group of `ℚ` given by the Hilbert/Steinberg symbols, with the global group Lagrangian by
  quadratic reciprocity, and the theta function as its metaplectic quantization. RH is the
  statement that the off-line divisor of `ξ` is the spectrum of an operator self-adjoint for this
  alternating form (hence of even multiplicity at every rung of the `2`-adic tower), while the
  on-line divisor sits on the symmetric part of the form (the sign symbol at `∞`), where no
  degeneracy is forced.
- **Status:** [REFUTED 2026-09-02] [NOT RH] [LEAN: cyclic no-symplectic, doubling is free, quadratic symbols symmetric]

## 1. What the doors have in common (proved facts)

| door | discrete invariant | what it sees | corpus theorem |
|---|---|---|---|
| multiplicity ladder | `2^k ∣ ord_ρ ξ` off the line; `RH ⟺` all rungs | every eigenvalue of an ω-self-adjoint operator, real or not | `even_finrank_maxGenEigenspace`, `rhLadder_one_iff_symplecticRealization` |
| reflection torsion | `ℤ/2` per fixed label | fixed points only; free orbits trivial | `ReflectionTateAnomaly` |
| Galois dichotomy | Kolchin closure `SL₂` or a connection | differential type of the object | `isomonodromy_or_sl2_galoisMonoid` |
| Lee–Yang trees | exact real zeros of finite prime trees | finite site models with `±1` spins | `prime-ising-tree-cavity-lee-yang` |
| Baker | independence of `log p` | the free abelian group `ℚ^×/±1` | `BakerLinearIndependence` |
| pair parity | evenness in `δ` | nothing at free orbits | `pairLedger_even` |

All but the first are fixed-point invariants of the reflection group and are blind at free
orbits by theorem. The ladder is the exception: symplectic self-adjointness forces even
multiplicity at *every* eigenvalue. This is why the corpus could localize RH to a single
construction there and nowhere else. The construction it asks for is an alternating form built
from Euler data, self-adjoint for the divisor operator off the line, with anomaly on the line.

## 2. The mechanism

The multiplicative group `ℚ^×` carries exactly one canonical alternating structure: the
Hilbert symbols `(a, b)_v ∈ {±1}` at every place, bimultiplicative and alternating
(`(a, b)(b, a) = 1`, `(a, −a) = 1`), nondegenerate on `ℚ_v^×/ℚ_v^{×2}`, with the global group
`ℚ^×` Lagrangian for the adelic form by quadratic reciprocity `∏_v (a, b)_v = 1`. Its universal
version is the Steinberg symbol into `K₂(ℚ) ≅ μ₂ ⊕ ⊕_p 𝔽_p^×` (Tate), whose `μ₂` is the symbol at
`∞`, the sign. Its quantization is the Weil (metaplectic) representation, in which the theta
function is the `Sp(2, ℚ)`-invariant vector and quadratic reciprocity is the Poisson summation
that gives `ξ` its functional equation.

**Conjecture (arithmetic symplectic descent).** There is an operator model `(V, A)` of the divisor
of `ξ` — a completion of the corpus's window model `𝒪(B)/(ξ)` over the family of quadratic twists
`ζ(s) L(s, χ_D)` — carrying the Hilbert-symbol form `ω` transported from `ℚ^×/ℚ^{×2}` (the dual of
the twist family), such that:
1. `A` is `ω`-self-adjoint on the off-line part of the divisor, so every off-line order is even
   (rung 1), and the `2`-power cyclotomic tower `ℚ(ζ_{2^k})` with its higher symbols supplies rung
   `k` (the `2`-adic amplification MUST-122 requires);
2. on the line the form degenerates to the symmetric sign symbol at `∞`, so no degeneracy is
   forced there (line-supported anomaly, as the ladder's open core specifies; consistent with the
   simplicity of infinitely many on-line zeros).

**Why the doors are its shadows.** Kramers is the `ω`-self-adjointness; the `ℤ/2` anomaly is
`μ₂ ⊂ K₂(ℚ)`, the symbol at `∞`; the Galois dichotomy is the differential type of the metaplectic
tower; the Lee–Yang trees are the finite `±1`-spin (quadratic-character) quotients of the form;
Baker's independence is the freeness of `ℚ^×/±1` on which the symbols live; pair parity is the
statement that the fixed-line part is symmetric.

**Ontological reversal.** The functional equation is symplectic *isometry* (eigenvalue pairing
`ρ ↔ 1 − ρ`, as Frobenius on `H¹` of a curve is an isometry of the cup-product form), which is
why FE transports but never selects (F06). The missing structure is symplectic *self-adjointness*,
a different relation to the same kind of form, and the arithmetic supplies an alternating form
only through the Hilbert symbols. No spectral, positivity, or growth input enters.

## 3. Why this is not in the literature, and the risk

The Hilbert-symbol form and the Weil representation are classical; the multiplicity ladder is
corpus-native; the metaplectic reading of RH-adjacent objects exists for half-integral weight
forms (Waldspurger, Kohnen–Zagier) but concerns central values, never zero multiplicities. The
claim that the alternating structure of quadratic reciprocity forces Kramers degeneracy of
off-line zeros is, to my knowledge, not proposed anywhere. The risk is concentrated in one
place: whether the divisor operator of the twist family is `ω`-self-adjoint at all. That is a
finite question on any EM split (Lean `EMSplitData`) with a finite prime set, and it is the
first thing to test on paper.

## 4. Targets (paper first; Lean after corpus search)

- **T1** Hilbert-symbol form on a finite prime set: alternating, nondegenerate on the finite
  quotient, with the global product formula as a Lagrangian statement (mathlib
  `legendreSym.quadratic_reciprocity` and the supplementary laws; check the corpus's
  `SeamKreinStructure.graph_lagrangian` for the abstract Lagrangian form).
- **T2** The finite window model `𝒪(B)/(ξ)` over quadratic twists of an EM split: write the
  divisor operator and the transported form explicitly; decide self-adjointness on paper. If it
  fails on one finite split, the mechanism is refuted and the card closes with that witness.
- **T3** Line-supported anomaly: the form's restriction to the fixed line is the symmetric sign
  symbol; show the on-line part of the model is a Lagrangian (no degeneracy forced).
- **T4** Amplification: the `2^k`-th root tower `rhLadder_iff_root` against the cyclotomic
  `2`-power symbols; identify rung `k` with self-adjointness over `ℚ(ζ_{2^k})`.

## Gates
- [ ] 0 → 1: T1 formalized; T2 decided on paper for one finite split.
- [ ] 1 → 2 / 2 → 3 / 3 → 4.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-09-02 — created in 0-backlog from the five-door audit; frozen before proof search;
  corpus searched for Hilbert symbols, Steinberg symbols, metaplectic/Weil representation
  (absent as zero-multiplicity mechanisms; Steinberg appears only in Deninger transgression
  lanes; a Lagrangian reciprocity graph exists abstractly in `SeamKreinStructure`).

## Paper proofs (2026-09-02): T2 fails for structural reasons

Three facts, each now a Lean theorem, close the mechanism before any arithmetic is reached.

1. **Single blocks carry no alternating self-adjoint form.** If `K` has a cyclic vector `g`
   (every vector is `p(K) g`), then any bilinear form with `B (K x) y = B x (K y)` satisfies
   `B (p(K) g) (q(K) g) = B g ((pq)(K) g)`, which is symmetric in `p, q`. An alternating such form
   is therefore zero, so no nondegenerate alternating `K`-self-adjoint form exists on a nonzero
   space with a cyclic vector. The canonical analytic model of the divisor at a zero,
   `ℂ[z]/(z − w)^m` with multiplication by `z`, is cyclic. Hence the symplectic structure the
   ladder asks for cannot live on the divisor model itself, for any `m`, even or odd.
2. **Doubling is free.** For any nondegenerate symmetric `K`-self-adjoint form `S` on `V` (for a
   cyclic block, the residue pairing `S(x, y) = coeff_{m−1}(xy)`), the doubled form
   `ω((x₁,x₂),(y₁,y₂)) = S x₁ y₂ − S x₂ y₁` on `V ⊕ V` is nondegenerate, alternating, and
   `K ⊕ K`-self-adjoint. So every model obtained by pairing two copies of the block — quadratic
   twists, reflection partners, FE doubling, any family of even size — is a symplectic
   realization automatically, and its multiplicity parity is the family size, not `ord_ρ ξ`.
   This is the general form of the ladder's proved FE-doubling blindness.
3. **Quadratic symbols are symmetric.** A `{±1}`-valued skew pairing (`b x y · b y x = 1`) is
   symmetric, so the Hilbert symbol lifted to `ℂ` is a symmetric form. The only alternating
   forms from symbols come from tame symbols composed with non-real characters (`Im` of a
   Hermitian form), which have no global reciprocity: `K₂(ℚ) ≅ μ₂ ⊕ ⊕_p 𝔽_p^×` (Tate) has no
   relation beyond `μ₂`. Alternating and Lagrangian are never supplied together.

**Consequence.** By (1) a symplectic realization must decompose the block into two isomorphic
halves paired alternately; by (2) any such decomposition obtained from a family is blind; so the
only admissible realization is a *canonical splitting of the block itself*, which is exactly a
square root of the local factor — rung 1. The proposal reduces to its conclusion, as
ULF-IND-001's multiplicative side and ULF-ANC-001's line anchor did. The stronger structural
theorem for the ladder is: **a symplectically self-adjoint endomorphism has no cyclic vector**;
Kramers doubles Jordan blocks, not just multiplicities. Any arithmetic construction for the
ladder must produce two isomorphic copies of the local divisor from Euler data; nothing linear
in the Euler product does.

## No-go closure
- **Exact killing theorem/mechanism:** `GaloisForLFunctions.HTGeometry.not_symplectic_selfAdjoint_of_cyclic`,
  `not_isCyclicVector_of_symplectic_selfAdjoint`, `bilin_symm_of_cyclic`,
  `exists_symplectic_selfAdjoint_doubled`, `symm_of_skew_units`
  (module `HTGeometry.CyclicNoSymplecticSelfAdjoint`); on paper, the absence of a global
  reciprocity for non-quadratic tame symbols.
- **Strongest positive survivor:** the sharpened Kramers statement (no cyclic vector; Jordan
  blocks double), which sharpens the ladder's open core: the symplectic structure must live on a
  doubled model whose two halves are produced canonically from Euler data.
- **New insight:** "alternating form from Euler data" and "square root of the local factor" are
  the same demand; the doors are shadows of the reflection group's fixed-point structure, and
  the symplectic door is the one that acts at free orbits only because doubling is free.
- **Status:** internal audit; module `lake build` green, axioms `propext, Classical.choice,
  Quot.sound`, wired into `GaloisForLFunctions.HTGeometry`.

## Log (continued)
- 2026-09-02 — T2 decided on paper (negative); three theorems formalized; card moved to 5-failed.
