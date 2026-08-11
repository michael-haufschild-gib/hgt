# Attempt 11: the fundamental symmetry of the Weil-Pontryagin form (Lean-proved)

Module: `formal/GaloisForLFunctions/RHTower/GaussHodgeWeilFundamentalSymmetry.lean` (wired into
RHTower umbrella, build green, all key theorems `[propext, Classical.choice, Quot.sound]`).
Card: `docs/drafts/pipeline/1-in-progress/hodge-sign-wall-constructed-pairing.md` (attempt 11 entry).

## Content (all unconditional unless marked RH-iff)
- `xiWeilParityFlip F z := F (conj z)` — J. Involutive; J-self-adjoint for xiWeilPolarization
  (`xiWeilPolarization_parityFlip_symm`, proof = divisor reindexing by xiZeroCopyLineConjEquiv).
- `xiWeilPolarization_parityFlip_right`: W(F, J G) = Σ' F(α_q)·conj(G(α_q)) — the J-twisted form
  IS divisor ℓ². `xiWeilParityFlip_hasSum_sq`: unconditional GNS law of the J-metric.
- Divisor parity: XiWeilDivisorEven/Odd, xiWeilEvenPart/OddPart (= pairSum/2, pairDif/2 on the
  divisor). `tsum_eq_zero_of_lineConj_neg` (generic reindexing-kill lemma, no summability).
  `xiWeilPolarization_even_odd` / `_odd_even`: full sesquilinear W-orthogonality of parities.
- Sector diagonals: even ⇒ W F F = +Σ'↑‖F‖² (`xiWeilEvenSector_hasSum_sq` = unconditional
  even-sector square realization); odd ⇒ W F F = −Σ'↑‖F‖².
- `xiWeilPolarization_parity_decomposition` (uses XiQuotientRealDecay additivity), complex-valued
  Krein identity `xiWeilPolarization_self_eq_parity_energies`, reality
  `xiWeilPolarization_self_im`.
- RH capstones: `riemannHypothesis_iff_forall_divisorOdd_eval_eq_zero` (converse = two-point
  indicator at off-line spectral point, NO summation) and
  `riemannHypothesis_iff_polarization_parityFlip_invariant`: **RH ⟺ W = its own J-twist**,
  quantifier over all F G with no summability hypotheses.

## Frontier consequence
The producer target is minimal: any exogenous positivity (compressed trace, intersection form)
forcing J-twist invariance of W closes RH; the negative sector is exactly the odd ℓ² sector.
Structure-level [BRIDGE] to textbook Krein fundamental-symmetry theory; the corpus-new content is
the explicit J with ℓ² J-metric on THIS form and the RH ⟺ J-triviality law.

## Reusable facts discovered
- `XiQuotientRealDecay.lean` owns the sesquilinear toolkit: xiWeilPolarization_add_left/_right,
  _const_smul_left/_right, _sub_left, norm_xiWeilPolarization_sub_left_le,
  XiWeilSquareSummable.add/.sub/.const_smul, XiWeilSquareSummable_sharp,
  xiWeilPairSummable_of_squareSummable', xiZeroCopyStarEquiv (= lineConj as star).
- `Complex.ofReal_tsum` holds with NO summability hypothesis.
- Concurrent session's `GaussReciprocalCharacterAdmission.lean`: RH ⟺ all-prime summability of
  the Hodge mass current (virial normalization) — complementary divergence criterion.
