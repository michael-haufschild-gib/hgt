# Terminal classification of producer shapes, and the metaplectic AII† test

- **ID:** ULF-TERM-001
- **Stage:** 0-backlog
- **Type:** CLASSIFICATION (theorem-backed) + one risky prediction on a new object
- **Source:** the six 2026-09-02 closures (`ULF-PIO/SLC/IND/ANC/INT/SYMP-001`), the ladder's twin
  rigidity (`RHTower.TwinRigidity`), `SymplecticCyclicObstruction`, `SymplecticDoublingFree`,
  the antiunitary catalogue of `multiplicity-parity-ladder-route.md` (class AII† is the unique
  symmetry class whose induced pairing fixes a non-real eigenvalue).
- **Statement:** Every producer shape proposed in the corpus or the literature is one of four
  kinds, and each kind is closed by a theorem: (1) real-valued inequalities from fixed
  functionals or positivity — slack `≥ log t` per zero; (2) convergence or continuation of an
  arithmetic object inside the strip — identical to the conclusion; (3) symmetries relating the
  fibre at `s` to the fibre at `σ(s)` — blind at free orbits; (4) two-factor presentations of
  ξ — the root dressed by a unit. What survives is a discrete invariant with an amplifiable
  squeeze (the F₁ template) or a direct sub-unit anchor (the Ferrero–Washington template).
  The one arithmetic operator model that is neither cyclic nor a family and that carries a
  genuine `J² = −1` is the transfer operator twisted by the theta multiplier; the laws predict
  that its Kramers doubling is cusp-pairing, hence blind.
- **Status:** [FROZEN] [NOT RH] [NO LEAN — the prediction is a paper check on a classical object]

## 1. The classification (each row is a theorem)

| shape | why it cannot produce | certificate |
|---|---|---|
| fixed functional of the zero measure | pair-even (T1), crowd slack `1/ν(t)` (C1–C4, Selberg ledger) | `pairLedger_even`, `SelbergLedgerCeiling`, `CosinePolynomialPurchaseCap` |
| created `L²` positivity on GL(2) | zeros are poles of `φ`, outside every Parseval identity | `ULF-SLC-001` P3 |
| convergent Möbius / prime series in the strip | convergence at one point is the zero-free half-plane | `riemannZeta_ne_zero_of_moebius_convergesAt` |
| means of `log|ζ|`, Laguerre expressions | density level `o(T)`; the inner band needs pointwise on-line density | `laguerre_XiC_eq_tsum_inv_sq`, kernel counterexample |
| integer counts with real bounds | slack `≥ log t` per integer | `ULF-INT-001` audit |
| reflection torsion, Galois type, Lee–Yang trees, Baker | fixed-point invariants, trivial on free orbits | `ReflectionTateAnomaly`, walls of the ladder card |
| symplectic structure on the canonical divisor model | cyclic modules carry only symmetric invariant forms | `SymplecticCyclicObstruction` |
| symplectic structure on a family/mirror model | doubling is free | `exists_symplectic_selfAdjoint_doubled`, FE-doubling blindness |
| quadratic symbols as the alternating form | `{±1}` skew pairings are symmetric | `symm_of_skew_units` |
| twins, 2×2 presentations, Gram balance, metaplectic channels | every twin is `(g v, g/v)` for a root `g` | `twin_eq_sqrt_mul_unit` |
| motivic halves of ζ | `L(M ⊕ N) = L(M)L(N)`, `𝟙` simple | paper |

**Reading.** Kinds (1)–(3) fail for one reason: they observe ξ through structures that are
either even in the free-orbit displacement or valid on a continuous class containing RH-false
members. Kind (4) fails because ξ has no internal second channel. The surviving requirement is
a *discrete* invariant of the free-orbit part of the divisor with a squeeze below `1`:
amplified (F₁) or direct (Ferrero–Washington).

## 2. The unexamined object and the prediction

The ladder's antiunitary catalogue proves that the only symmetry class whose induced pairing
fixes a non-real eigenvalue is AII†: an antiunitary `J` with `J² = −1` intertwining an operator
with its transpose. The corpus's operator models of ξ are analytic (cyclic) or mirror-doubled,
and both are closed above. One arithmetic operator model exists that is neither: Mayer's
transfer operator `L_s` of the Gauss map, whose Fredholm determinant is the Selberg zeta of the
modular surface, with ζ's zeros entering as the scattering poles `ρ/2`. In the Hankel
representation `L_s` is complex-symmetric (class AI†), so it forces no parity, consistent with
simple zeros. Twisting by the **theta multiplier system** (weight `½`, the metaplectic double
cover, whose cocycle is built from Hilbert symbols) replaces the transpose symmetry by a genuine
one with `J² = −1`: the twisted operator `L_s^{θ}` is a candidate AII† model, and its determinant
is the Selberg zeta for the theta multiplier on `Γ₀(4)`, whose scattering poles are again
zeros of ζ (scaled) and of quadratic `L`-functions.

**Prediction (risky, decided on paper).** Kramers doubling in `det(1 − L_s^{θ})` is produced by
the pairing of the cusps of `Γ₀(4)` under the Fricke involution and by the two components of
the Weil representation; the ζ-part of the metaplectic scattering determinant enters as a
*square by cusp pairing*, so the even multiplicities it forces are free doubling, not a
constraint on `ord_ρ ξ`. If instead the ζ-part entered unsquared while the operator is AII†,
the operator would force every ζ-zero to have even multiplicity, contradicting the infinitely
many simple on-line zeros; so the laws predict the metaplectic door is closed by the same
theorem as every other doubling. A single explicit scattering determinant decides it.

## 3. What a genuinely new idea must therefore contain

Not a functional, not a convergence, not a symmetry relating `s` to `σ(s)`, not a factorization
of ξ, not a family. It must name an integer attached to the free-orbit divisor and a bound below
`1`. Two doors remain: an F₁-type object carrying the zeros as local eigenvalues with a tensor
amplification, or a direct anchor in the Ferrero–Washington sense. No candidate for the second
exists in the corpus; producing one is the only research act this classification leaves open.

## Gates
- [x] 0 → 1 (2026-09-02): prediction confirmed on paper and the no-go formalized — see
  `5-failed/metaplectic-transfer-operator-kramers.md` (P1–P5) and `RHTower.GlobalParityWall`.
  The classification stands; the metaplectic door is closed.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-09-02 — created in 0-backlog as the terminal classification of the day's six closures;
  corpus searched for theta-multiplier/metaplectic transfer operators (absent).
- 2026-09-02 — §2 prediction confirmed (two singular cusps, Fricke square, `e = 2`); global parity
  wall proved in Lean; the card remains as the standing classification.
- 2026-09-02 — door 1 attacked directly: Weil–Deligne integrality refuted in both coordinates
  (`5-failed/f1-frobenius-integrality-torsion-law.md`, `RHTower.FrobeniusTorsionLaw`); producer
  positivity shown RH-or-blind. Door 1 survives only as a structure without characteristic
  polynomials (MUST-129).
- 2026-09-02 — door 2 audited: the corpus's direct anchor integer is the off-line indicator
  (`RHTower.EscapeMultiplicityOffLineIndicator`); its gap is the off-line condition and its
  everywhere-vanishing is RH. Both doors are receivers as the corpus stands (CANNOT-193, MUST-130).
