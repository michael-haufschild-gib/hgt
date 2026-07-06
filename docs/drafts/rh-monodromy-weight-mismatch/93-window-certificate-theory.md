# 93 — The height-window certificate theory (rung 1 on the box, ground out)

Doc 92 localized the whole ladder to the box `{½<Re<1, Im≥0}` and named the next object: the
per-height-window certificate. This doc is the ledger of that object, now built in full — three
Lean modules, all axiom-clean `[propext, Classical.choice, Quot.sound]`, RHTower (8745) and
MainTheorems (9135) green, lint passed.

Modules: `RHTower/WindowLadder.lean` (the certificate theory), `RHTower/DeckWindow.lean` (the
deck/monodromy face, with chart-root existence built), `RHTower/WindowSeam.lean` (the line-data
weld). ~45 new declarations.

## 1. The windows and the certificate (WindowLadder)

- `stripWindow T` = `{0<Re<1, 0≤Im<T}` (lineReflect-closed), `boxWindow T` its right half;
  `stripZeros T`, `boxZeros T` their ξ-zero sets.
- **`stripZeros_finite` / `boxZeros_finite`** — every height window holds finitely many ξ-zeros:
  the compact-exhaustion handle the bounded box supplies and the half-plane denied.
- **`WindowCertificate k T`** := every `boxZeros T` order divisible by `2^k`. Structure:
  trivial at `k=0` and `T≤0`; monotone in `T` (`windowCertificate_mono`), antitone in `k`
  (`windowCertificate_of_le`); a finite check (`windowCertificate_iff_finset`); equal to the
  valuation bound `k ≤ ladderHeight` per zero (`windowCertificate_iff_ladderHeight`); at `k=1`
  exactly *no odd-order zero in the window* (`windowCertificate_one_iff_even`).
- **Sharp collapse per window**: a window zero of height `h` breaks certificate level `h+1`
  (`not_windowCertificate_ladderHeight_succ`).

## 2. Exhaustion — the certificates decide the ladder and RH

- `rhLadder_iff_forall_windowCertificate` — rung `k` = all height-`T` certificates.
- `rhLadder_iff_forall_nat_windowCertificate` — ℕ-heights suffice (countable sequence).
- `rhLadder_of_cofinal_windowCertificates` — cofinal heights suffice.
- **`rh_iff_diagonal_windowCertificate`** — **RH ⟺ the diagonal sequence
  `WindowCertificate n n`, `n ∈ ℕ`**: one countable sequence of statements, each about finitely
  many zeros. Both monotonicities compress the two-parameter family to the diagonal.
- `forall_windowCertificate_iff_boxZeros_empty` — all levels on ONE window ⟺ that window is
  zero-free; `rh_iff_forall_boxZeros_empty`.

## 3. The per-window Kummer correspondence (bounded-domain roots)

`halfBand T` = `{Re>½, |Im|<T}` (convex, bounded height, anchor 2).

- **`windowCertificate_iff_bandRoot`** — certificate at level `k`, height `T>0` ⟺ ξ has an
  analytic `2^k`-th root on `halfBand T`. The windowed `rhLadder_iff_root`.
- `windowCertificate_one_iff_band_sqrt` — rung 1 per window = √ξ on the band.
- `bandRoot_of_succ` (nesting by squaring), `bandRoot_mono` (restriction),
  `bandRoot_unique` (rigidity: roots agreeing at the anchor agree), `bandRoot_restrict_eq`
  (coherence across heights: the normalized band roots form a compatible family over the
  exhaustion, whose totality is the half-plane root).
- `rhLadder_iff_forall_bandRoot` — the half-plane root ⟺ roots on every bounded band.
- **Windowed coherent tower**: `coherentTower_halfBand_iff_boxZeros_empty`,
  `coherentTower_halfBand_iff_forall_windowCertificate`,
  `rh_iff_forall_coherentTower_halfBand` — the full ℤ₂-Kummer tower on a band ⟺ window
  emptiness; RH ⟺ towers at all heights. The bounded form of `rh_iff_tower`.

## 4. The boundary/counting face on the ACTUAL divisor

Previously the window identity `D = L + 2N` was a theorem about hypothetical Finset
configurations; now it holds on the actual ξ-zero set of the window (closure and multiplicity
invariance under `lineReflect` are theorems of ξ):

- **`stripWindow_order_identity`** — `D_T = L_T + 2·N_T` on `stripZeros T`, with
  `N_T` = the box sum exactly (`stripZeros_toFinset_filter_right`).
- **`stripWindow_parity`** — `D_T ≡ L_T (mod 2)` unconditionally: off-line zeros pair under the
  line reflection with equal orders, so *a loop-level mod-2 functional of the window divisor can
  never see an off-line zero*. The per-zero certificate is strictly finer than any single window
  total — the formal location of why the boundary program must certify per zero, not per loop.
- `stripWindow_modEq_of_windowCertificate` — certificate ⟹ `D_T ≡ L_T (mod 2^{k+1})`, same
  window only.
- **`windowCertificate_iff_subWindow_congruences`** — certificate ⟺ EVERY reflection-closed
  sub-configuration of the window divisor satisfies the mod-`2^{k+1}` congruence. Backward via
  the two-point pair sub-window of each box zero. The quantifier difference (all
  sub-configurations vs the one full window) is the machine-visible gap between loop data and
  per-zero data. `rh_iff_forall_subWindow_congruences` is the capstone.

## 5. The deck/monodromy face (DeckWindow) — root existence BUILT

The per-zero deck dictionary (`xi_deckClass_eq_one_iff_ladder_dvd`) was conditional on chart
roots being given. That conditionality is now discharged:

- `isSimplyConnected_chartR/L` — the slit charts are star-convex ∩ ball, hence simply connected.
- `xi_ne_zero_on_charts` — below the peel radius the charts are ξ-nonvanishing.
- **`xi_exists_chart_roots`** — analytic `n`-th roots of ξ exist on both charts at every level,
  every small radius, around EVERY point. Unconditional.
- **`windowCertificate_iff_deck_trivial`** — certificate ⟺ at each window zero the (existing)
  level-`2^k` chart roots have trivial deck class. A true iff — both directions carry content
  now. `rhLadder_iff_forall_deck_trivial`, `rh_iff_forall_deck_trivial`.
- **`xi_deckClass_line_holography`** — UNDER the certificate, the level-`2^{k+1}` deck class of
  any reflection-closed enclosed configuration equals `exp(2πi·L/2^{k+1})`, `L` = on-line order
  sum: the certificate forces every boundary loop to read pure critical-line data. The
  constraint-fixes-bulk dictionary, machine-checked.

## 6. The line-data weld (WindowSeam)

- **`windowCertificate_of_emCarrier_sign_certificates`** — a family of finite line certificates
  (EM remainder bound + `emCarrier`/`gN` closeness + LOW floor on the charts + certified ξ sign
  alternations dominating the enclosed count) covering the window's box zeros forces the
  height-`T` certificate at every level. At `k=1` this is literally *line data forcing
  `ladderHeight ≥ 1` per window* — the object doc 92 §5 named.
- `boxZeros_empty_of_emCarrier_sign_certificates` — the same data empties the window: RH below
  height `T` from finitely many finite-data checks.
- Generic consumer: `windowCertificate_of_ball_online_cover` / `rhLadder_of_ball_online_covers` —
  any instrument producing on-line ball covers plugs in.

## 7. What is exhausted, and what this opens

Exhausted (unconditional Lean): the certificate's order/valuation/finiteness structure, both
exhaustion directions (windows→ladder→RH, incl. the diagonal), the bounded Kummer/tower
correspondence, the boundary identity + congruence surface on the actual divisor, the deck face
with root existence built, the holography reading, and the typed line-data weld.

The open core is unchanged in *content* but changed in *shape*: rung 1 is now a countable
sequence of FINITE statements — `WindowCertificate 1 n`, each deciding finitely many parities —
and the sub-window congruence surface says exactly which boundary data would decide each one:
the two-point pair congruences at level 4, per box zero. The next object is therefore not a new
reduction but a *producer*: an instrument whose finite window inputs (the `WindowSeam`
hypothesis package: floors, closeness, sign tables) are themselves forced analytically on a
cofinal family of windows. The holography theorem gives the target invariant — the boundary loop
class `exp(2πi·L/2^{k+1})` — and `stripWindow_parity` says its mod-2 shadow is already
unconditional; the generative move is to find the *second* boundary functional, independent of
the loop class, that separates the pair congruence from the full-window congruence (the DISC-bit
of the dictionary, now typed at the window level as the difference between §4's two quantifiers).
