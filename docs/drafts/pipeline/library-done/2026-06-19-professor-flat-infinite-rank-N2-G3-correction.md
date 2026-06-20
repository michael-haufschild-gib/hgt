# Library ticket — 2026-06-19 (Professor + Wheeler/DeWitt synthesis): N2/G3 "flat" disambiguation

**For:** librarian — update `00-foundations-native-objects-and-gatekeepers.md` N2 and the G3 statement (and the
G3-corank-dichotomy card / door G3); cross-ref bucket-time-and-non-holonomic-time (#N4 Bohr–Kronecker).

**The correction (verified).** The field's geometry is **flat-with-infinite-rank**, and the literal N2/G3
statements are contradicted by it:
- N2 currently: "Flat (integrable) ⟺ holonomic; non-flat ⟺ non-holonomic."
- G3 currently: "holonomic ⟺ corank(Λ)<∞ ⟺ its connection is flat."
- BUT: the field is **curvature-flat** (`F_pq=[σ_p,σ_q]=0`, verified — the σ_p are commuting dilations on
  DISJOINT Bohr coordinates `x_p`) AND **non-holonomic** (corank ∞). So "non-flat ⟺ non-holonomic" and
  "flat ⟹ holonomic" are literally false here.

**Resolution — disambiguate "flat":**
1. *curvature-flat* (`F_pq=0`): ALWAYS true (commuting σ_p). Verified: σ_2σ_3=σ_3σ_2.
2. *integrable-to-finite-rank* (= holonomic, finite-dim solution space / finite-order equation): FALSE
   (corank ∞). The obstruction is the **dense diagonal Kronecker orbit** `t↦(p^{−it})_p`, dense in 𝕋^∞ by
   ℚ-independence of {log p} (Kronecker–Weyl; verified numerically) — i.e. INFINITE RANK = the hypertranscendence.
In finite dimensions Frobenius gives (1)⟺(2); in INFINITE dimensions they split. The field is (1) but not (2).

**Corrected statements (suggested):**
- N2: "The connection is **curvature-flat** (`F_pq=0`, commuting σ_p) at every truncation and in the limit; it
  is holonomic ⟺ **finite rank** (corank<∞). The arithmetic case is curvature-flat but **infinite-rank**
  (corank=∞) — non-holonomic by RANK, not curvature."
- G3: "holonomic ⟺ corank(Λ)<∞ ⟺ integrable-to-finite-rank" (drop/qualify the bare "⟺ flat": curvature-flat
  is necessary-but-not-sufficient in infinite dim).

**Why it matters:** aligns the geometry with the hypertranscendence (both = infinite rank, not curvature),
with the |1−1/ρ|=1 flat/abelian Li-geometry, the flow-dim-1/corank-∞ seam, and f1-inversion's trdeg=corank.
The Bohr–Kronecker border (#N4) IS the field's actual geometry: the flat Kronecker flow on 𝕋^∞, non-holonomic
by infinite rank. (Joint: Wheeler id=440, DeWitt's flat-∞-holonomy, Professor verification id=442.)
