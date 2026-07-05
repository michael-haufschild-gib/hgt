/-
The parity-selected dip counter (doc 72 §9.3, doc 81 §3.2 — the odd-parity
budget knob, formal core).

The banked counters price ALL dips and pay the Fubini–Markov thickness
factor 4/(1−β) to exclude the on-line-zero floor. But the floor and the
creation events differ by PARITY: a simple on-line zero's dip changes the
sign of the real carrier across its window (odd event); a creation dip —
an off-line pair pressing on the line — preserves it (even event). A
counter that counts only selected (even) events against the mass of THEIR
OWN windows never meets the floor:

* `selected_dips_count_le` — count of selected dips ≤ vol(E \ F)/h, given
  each selected window holds ≥ h of floor-free mass.
* `selected_dips_count_le_of_disjoint` — the discharge form: if each
  selected window is disjoint from the floor set (the no-zero certificate
  of a sign-preserving window), the plain dip-mass hypothesis suffices.
* `selected_sliver_budget` — the budget composition: with a kernel bound
  vol(E \ F) ≤ M, the selected count obeys count·h ≤ M — NO thickness
  factor. Against doc 74's budget arithmetic this moves the tail budget
  from ε₀*/(4/(1−β)) to ε₀* — a structural ×4.05.

The parity certificate (which windows are even) is the (K1) sign reading
of `DictionarySign` on the finite carrier — per-window certifiable data.
-/
import GaloisForLFunctions.RHTower.MollifiedDip
import GaloisForLFunctions.RHTower.RelayLedger

namespace RHTower

open MeasureTheory Set

/-- **Parity-selected dip counting.** Selected dips, each holding `h` of
floor-free sublevel mass in their own window, are counted by the floor-free
measure alone. -/
theorem selected_dips_count_le {E F : Set ℝ} (hE : MeasurableSet E)
    (hF : MeasurableSet F) {h : ℝ} (hh : 0 < h) (S : Finset ℝ)
    (sel : ℝ → Prop) [DecidablePred sel]
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (hdip : ∀ γ ∈ S, sel γ →
      ENNReal.ofReal h ≤ volume ((E \ F) ∩ Icc (γ - h) (γ + h))) :
    ((S.filter sel).card : ENNReal) * ENNReal.ofReal h ≤ volume (E \ F) := by
  refine separated_dips_count_le (hE.diff hF) hh (S.filter sel) ?_ ?_
  · exact hsep.mono (by exact_mod_cast Finset.coe_subset.mpr (Finset.filter_subset _ _))
  · intro γ hγ
    obtain ⟨hγS, hγsel⟩ := Finset.mem_filter.mp hγ
    exact hdip γ hγS hγsel

/-- **The discharge form**: a selected window disjoint from the floor set
(the no-zero certificate of a sign-preserving window) needs only the plain
dip-mass hypothesis. -/
theorem selected_dips_count_le_of_disjoint {E F : Set ℝ} (hE : MeasurableSet E)
    (hF : MeasurableSet F) {h : ℝ} (hh : 0 < h) (S : Finset ℝ)
    (sel : ℝ → Prop) [DecidablePred sel]
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (hdip : ∀ γ ∈ S, sel γ →
      ENNReal.ofReal h ≤ volume (E ∩ Icc (γ - h) (γ + h)))
    (hdisj : ∀ γ ∈ S, sel γ → F ∩ Icc (γ - h) (γ + h) = ∅) :
    ((S.filter sel).card : ENNReal) * ENNReal.ofReal h ≤ volume (E \ F) := by
  refine selected_dips_count_le hE hF hh S sel hsep ?_
  intro γ hγS hγsel
  have hset : (E \ F) ∩ Icc (γ - h) (γ + h) = E ∩ Icc (γ - h) (γ + h) := by
    ext t
    constructor
    · rintro ⟨⟨htE, -⟩, htI⟩
      exact ⟨htE, htI⟩
    · rintro ⟨htE, htI⟩
      refine ⟨⟨htE, fun htF => ?_⟩, htI⟩
      have : t ∈ F ∩ Icc (γ - h) (γ + h) := ⟨htF, htI⟩
      rw [hdisj γ hγS hγsel] at this
      exact this
  rw [hset]
  exact hdip γ hγS hγsel

/-- **The thickness-free budget**: selected count times `h` is bounded by
any certified kernel bound on the floor-free mass — the tail budget enters
at `ε₀*` directly, with no Fubini–Markov thickness factor. -/
theorem selected_sliver_budget {E F : Set ℝ} (hE : MeasurableSet E)
    (hF : MeasurableSet F) {h M : ℝ} (hh : 0 < h) (hM : 0 ≤ M) (S : Finset ℝ)
    (sel : ℝ → Prop) [DecidablePred sel]
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (hdip : ∀ γ ∈ S, sel γ →
      ENNReal.ofReal h ≤ volume ((E \ F) ∩ Icc (γ - h) (γ + h)))
    (hker : volume (E \ F) ≤ ENNReal.ofReal M) :
    ((S.filter sel).card : ℝ) * h ≤ M := by
  have h1 := (selected_dips_count_le hE hF hh S sel hsep hdip).trans hker
  have h2 : ENNReal.ofReal (((S.filter sel).card : ℝ) * h)
      = ((S.filter sel).card : ENNReal) * ENNReal.ofReal h := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have h3 : ENNReal.ofReal (((S.filter sel).card : ℝ) * h)
      ≤ ENNReal.ofReal M := by
    rw [h2]
    exact h1
  have h4 := ENNReal.toReal_le_of_le_ofReal hM h3
  rwa [ENNReal.toReal_ofReal (by positivity)] at h4

end RHTower

namespace RHTower

open MeasureTheory Set

/-- **Integer selected-census form.** If selected windows have dip mass, are
certified disjoint from the floor, and the floor-free kernel budget lies below
the next integer multiple of `h`, then the selected count is at most `K`. -/
theorem selected_sliver_card_le_of_disjoint_kernel {E F : Set ℝ} (hE : MeasurableSet E)
    (hF : MeasurableSet F) {h M : ℝ} (hh : 0 < h) (hM : 0 ≤ M) (S : Finset ℝ)
    (sel : ℝ → Prop) [DecidablePred sel]
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (hdip : ∀ γ ∈ S, sel γ →
      ENNReal.ofReal h ≤ volume (E ∩ Icc (γ - h) (γ + h)))
    (hdisj : ∀ γ ∈ S, sel γ → F ∩ Icc (γ - h) (γ + h) = ∅)
    (hker : volume (E \ F) ≤ ENNReal.ofReal M)
    {K : ℕ} (hK : M < (K + 1 : ℝ) * h) :
    (S.filter sel).card ≤ K := by
  have hselected :=
    (selected_dips_count_le_of_disjoint hE hF hh S sel hsep hdip hdisj).trans hker
  have h2 : ENNReal.ofReal (((S.filter sel).card : ℝ) * h)
      = ((S.filter sel).card : ENNReal) * ENNReal.ofReal h := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have h3 : ENNReal.ofReal (((S.filter sel).card : ℝ) * h)
      ≤ ENNReal.ofReal M := by
    rw [h2]
    exact hselected
  have hreal := ENNReal.toReal_le_of_le_ofReal hM h3
  have hcount : ((S.filter sel).card : ℝ) * h ≤ M := by
    rwa [ENNReal.toReal_ofReal (by positivity)] at hreal
  have hcard_lt_real : ((S.filter sel).card : ℝ) < (K + 1 : ℝ) := by
    have hlt : ((S.filter sel).card : ℝ) * h < (K + 1 : ℝ) * h :=
      lt_of_le_of_lt hcount hK
    nlinarith
  have hcard_lt_nat : (S.filter sel).card < K + 1 := by
    exact_mod_cast hcard_lt_real
  exact Nat.lt_succ_iff.mp hcard_lt_nat

end RHTower

namespace RHTower

open MeasureTheory Set

/-- Relay spread obstruction from a parity-selected floor-free census.  The map
`hup` is the explicit bridge from upcrossings below `M` to selected windows;
the selected-window budget then supplies the upcross bound consumed by
`spread_lt_of_upcross_budget`. -/
theorem spread_lt_of_upcross_selected_kernel {D₀ : ℝ} {pushes : List ℝ} {ℓ k M K : ℕ}
    {levels : ℕ → ℕ} [DecidablePred (UpcrossAt D₀ pushes)]
    (hD₀ : D₀ ≤ 0) (hexc : ExcursionBound D₀ pushes ℓ)
    (hgap : ∀ i, i < k → levels i + ℓ ≤ levels (i + 1))
    (hpres : ∀ i, i ≤ k → 0 < signedDepth D₀ pushes (levels i))
    (hM : levels k ≤ M)
    {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F)
    {w B : ℝ} (hw : 0 < w) (hBnonneg : 0 ≤ B) (S : Finset ℝ)
    (sel : ℝ → Prop) [DecidablePred sel]
    (hup : ((Finset.range M).filter (UpcrossAt D₀ pushes)).card ≤ (S.filter sel).card)
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * w ≤ |x - y|)
    (hdip : ∀ γ ∈ S, sel γ →
      ENNReal.ofReal w ≤ volume (E ∩ Icc (γ - w) (γ + w)))
    (hdisj : ∀ γ ∈ S, sel γ → F ∩ Icc (γ - w) (γ + w) = ∅)
    (hker : volume (E \ F) ≤ ENNReal.ofReal B)
    (hK : B < (K + 1 : ℝ) * w) :
    k < K := by
  have hselected : (S.filter sel).card ≤ K :=
    selected_sliver_card_le_of_disjoint_kernel hE hF hw hBnonneg S sel hsep hdip hdisj hker hK
  exact spread_lt_of_upcross_budget hD₀ hexc hgap hpres hM (Nat.le_trans hup hselected)

end RHTower
