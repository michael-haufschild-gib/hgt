# WD abscissa at the critical scale on almost all heights

- **ID:** wd-critical-scale-typical-abscissa
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `wd-goal-loop-2026-10-09.md` row 294
- **Statement:** There is B > 0 such that for every c ≥ 2 and all large U, the slice x ↦ ξ(½+x+it)ξ(½−x+it) is absolutely monotone from c/log U at every height t ∈ [U/4+2, U/2−2] outside a set of measure ≤ B e^{−c/28} U. Hence for every ε > 0 some c gives exceptional measure ≤ εU.

## Paper proof
1. Hyperbola criterion (corpus): AbsMono at (t, x₀) holds if every zero copy has (Re ρ − ½)² ≤ (Im ρ − t)² + x₀².
2. A failure exhibits a zero w of ζ with ½ + x₀ < Re w < 1 and |Im w − t| < Re w − ½ (reflect left zeros by ρ ↦ 1 − ρ̄, same ordinate).
3. On [T₁+½, T₂−½] such w lie in Selberg's box [½, 15/2] × [T₁, T₂]; the failure set is covered by the intervals (Im w − (Re w − ½), Im w + (Re w − ½)), of total length ≤ 2 Σ m_w (Re w − ½) over Re w ≥ ½ + c/log U.
4. The corpus tail moment (`exists_offLineTailMoment_window_le_exp`) bounds that sum by B e^{−c/28}(T₂ − T₁) + K log² U; log² U = o(U).

## Lean
- `RHTower/XiHorizontalAbsMonoCriticalScaleDensity`: `exists_right_zero_of_not_xiHorizontalAbsMono`, `exists_volume_not_xiHorizontalAbsMono_le_exp`, `exists_volume_not_xiHorizontalAbsMono_le_criticalScale`, `eventually_volume_not_xiHorizontalAbsMono_le`.
- `#print axioms`: propext, Classical.choice, Quot.sound. Wired into `GaloisForLFunctions.RHTower`.

## Position
- Every height: ½ − w(t) (Vinogradov–Korobov). Almost every height: c/log t with exceptional proportion e^{−c/28} (this card). Centre x₀ = 0: positive density only (corpus, mollified mean square). RH: 0 at every height.
- Below the critical scale, density methods hit the fixed-a mean-square barrier.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3

## Log
- 2026-10-12 — conjectured, proved, formalized (row 294).
