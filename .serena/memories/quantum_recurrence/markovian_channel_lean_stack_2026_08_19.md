# Markovian return-recovery card: new Lean stack (2026-08-19)

Goal: close 5 stage-2 cards. Working card 1 = `markovian-return-recovery-complexity-reflection-law`.

## New HTGeometry modules (all umbrella-wired, axiom-clean, built)
1. `HermitianTraceNorm.lean` — `trace_cfc_re`, `cfc_abs_eq_sqrt`,
   `finiteMatrixNuclearNorm_isHermitian` (= Σ|λ|), `trace_re_eq_sum_eigenvalues`,
   `finiteMatrixNuclearNorm_posSemidef`, `IsHermContraction`, `re_trace_mul_le_nuclearNorm`,
   `exists_isHermContraction_re_trace_eq`, `finiteMatrixNuclearNorm_add_le`,
   `hermitian_eq_conj_diagonal`.
2. `PositiveTraceContraction.lean` — `hermPos`/`hermNeg` Jordan split,
   `finiteMatrixNuclearNorm_apply_le` (positive TP contracts ‖·‖₁ on Hermitian).
3. `AncillaBlockMatrix.lean` — `blockMat`/`matBlock`, `blockMat_mul`, `_conjTranspose`,
   `_trace`, `amplify_blockMat`, `trace_amplify`, `amplify_sub'`.
4. `PositiveMapTraceNormContraction.lean` — `blockDiag2`, `hermDilation2`,
   `finiteMatrixNuclearNorm_hermDilation2` (= 2‖X‖₁), `IsPositiveTP`,
   `positiveLinear_map_*` (zero/neg/sub/isHermitian/conjTranspose),
   `nuclearNorm_apply_le_of_twoPositive` (general X), `finiteMatrixNuclearNorm_add_le'`,
   `_sub_le'`, `_sub_le_sub`, `_neg`, `_zero`, `_smul_ofReal`.
5. `QuantumChannelDiamond.lean` — `QuantumChannel` structure (CP over arbitrary finite ancilla
   `m : Type`), Monoid, `amplify_amplify`, `twoPositive_amplify`, `nuclearNorm_amplify_le`,
   `IsDensity`, `diamondDist` (sup over the ‖·‖₁ unit ball), **MetricSpace instance**,
   `nuclearNorm_sub_le_diamondDist_mul`, `leftContracting_quantumChannel`, `unitaryChannel`,
   `diamondDist_mul_unitaryChannel` (isometry).
6. `MarkovianReturnRecovery.lean` — `DynamicalSemigroup`, `recovery_left/right` (6),
   `dist_recovery_eq` (7), `one_sub_defect_mul_nuclearNorm_le` (8), `UnitaryDictionary`,
   `dist_reflect_word` (9), `card_reflect_word` (10), `sum_weighted_le` (11).
7. `CompletelyPositiveSchwarz.lean` — `blockVec2`, `dotProduct_blockMat_two`,
   `sub_conjTranspose_mul_posSemidef`, `posSemidef_schwarzBlock`, `IsCP`, `IsCP.schwarz`.
8. `UnitalCPInverseRigidity.lean` — `IsCP.monotone`, `IsCP.schwarz_eq`,
   `IsCP.map_mul_of_inverse` (polarisation).
9. `MatrixStarAutomorphismInner.lean` — `star_mulVec_dotProduct`,
   `exists_unitary_conjugation_of_starAlgHom` (Skolem–Noether by matrix units).
10. `ChannelInverseRigidity.lean` (in progress) — `posSemidef_le_trace_smul_one`,
    `linear_eq_zero_of_eqOn_posSemidef`, `eq_one_of_trace_mul_eq`,
    `QuantumChannel.det_map_one_ne_zero`, `exists_unitary_of_channel_inverse` (Corollary C).

## Traps hit
- `open Matrix` INSIDE `namespace GaloisForLFunctions.HTGeometry` shadows `_root_.Matrix`
  (the corpus declares `Matrix.*` lemmas inside that namespace), which kills the `ᴴ` notation.
  Put all `open`s BEFORE the namespace, as `FiniteNuclearIncidenceLaw.lean` does.
- `⊗ₖ` needs `open scoped Kronecker`.
- `Matrix.PosSemidef` is stated with `Finsupp`; use `posSemidef_iff_dotProduct_mulVec`,
  `PosSemidef.dotProduct_mulVec_nonneg`, `PosSemidef.of_dotProduct_mulVec_nonneg`.
- `(1 : QuantumChannel n).map` reduction through the Monoid instance can time out `rfl`;
  rewrite with `one_map : (1).map = id` first.
