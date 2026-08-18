/-
# The iterated-exponential growth scale

Composition depth is measured on the iterated-exponential scale: `iterExp k` is `exp` applied `k`
times, `GrowthHeightAtLeast F k` says the maximum modulus of `F` on the disc of radius `r`
eventually dominates `exp_k(r^δ)` for some `δ > 0`, and `GrowthHeightAtMost F k` says it is
eventually dominated by `exp_k(r^C)` for some `C`.

The two are incompatible one step apart, because one extra exponential beats every fixed power:
`r^C < exp(r^δ)` eventually, and `iterExp k` is strictly monotone.  Positive lower order is growth
height at least one.
-/
import Mathlib

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The `k`-fold iterated real exponential. -/
def iterExp (k : ℕ) (x : ℝ) : ℝ := (Real.exp)^[k] x

@[simp] theorem iterExp_zero (x : ℝ) : iterExp 0 x = x := rfl

theorem iterExp_succ (k : ℕ) (x : ℝ) : iterExp (k + 1) x = Real.exp (iterExp k x) :=
  Function.iterate_succ_apply' Real.exp k x

theorem iterExp_succ' (k : ℕ) (x : ℝ) : iterExp (k + 1) x = iterExp k (Real.exp x) :=
  Function.iterate_succ_apply Real.exp k x

theorem iterExp_monotone (k : ℕ) : Monotone (iterExp k) := by
  induction k with
  | zero => exact monotone_id
  | succ k ih =>
      intro x y hxy
      rw [iterExp_succ, iterExp_succ]
      exact Real.exp_le_exp.mpr (ih hxy)

theorem iterExp_strictMono (k : ℕ) : StrictMono (iterExp k) := by
  induction k with
  | zero => exact strictMono_id
  | succ k ih =>
      intro x y hxy
      rw [iterExp_succ, iterExp_succ]
      exact Real.exp_lt_exp.mpr (ih hxy)

theorem iterExp_le_succ (m : ℕ) (x : ℝ) : iterExp m x ≤ iterExp (m + 1) x := by
  rw [iterExp_succ']
  exact iterExp_monotone m (by linarith [Real.add_one_le_exp x])

theorem iterExp_mono_index {l k : ℕ} (h : l ≤ k) (x : ℝ) : iterExp l x ≤ iterExp k x := by
  induction k with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge l (k + 1) with hlt | hge
      · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (iterExp_le_succ k x)
      · rw [le_antisymm h hge]

/-- One extra exponential beats any fixed power inside any fixed number of exponentials. -/
theorem eventually_iterExp_rpow_lt (k : ℕ) (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in atTop, iterExp k (r ^ C) < iterExp (k + 1) (r ^ δ) := by
  have hkey : ∀ᶠ r : ℝ in atTop, r ^ C < Real.exp (r ^ δ) := by
    have hcomp := (isLittleO_rpow_exp_atTop (C / δ)).comp_tendsto (tendsto_rpow_atTop hδ)
    have hhalf := hcomp.def (c := (1 : ℝ) / 2) (by norm_num)
    filter_upwards [hhalf, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    have hpow : ((r ^ δ) ^ (C / δ) : ℝ) = r ^ C := by
      rw [← Real.rpow_mul hr0.le]
      congr 1
      field_simp
    simp only [Function.comp_apply] at hr
    rw [hpow] at hr
    have hexp : (0 : ℝ) < Real.exp (r ^ δ) := Real.exp_pos _
    have h1 : |r ^ C| ≤ 1 / 2 * |Real.exp (r ^ δ)| := hr
    rw [abs_of_pos hexp] at h1
    calc r ^ C ≤ |r ^ C| := le_abs_self _
      _ ≤ 1 / 2 * Real.exp (r ^ δ) := h1
      _ < Real.exp (r ^ δ) := by linarith
  filter_upwards [hkey] with r hr
  rw [iterExp_succ']
  exact iterExp_strictMono k hr


/-- **Growth height at least `k`.**  For some `δ > 0`, the maximum modulus on the disc of radius `r`
is eventually at least the `k`-fold exponential of `r ^ δ`.  For `k = 1` this is exactly positive
lower order. -/
def GrowthHeightAtLeast (F : ℂ → ℂ) (k : ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖ ≤ r ∧ iterExp k (r ^ δ) ≤ ‖F z‖

/-- **Growth height at most `k`.**  For some exponent `C`, the maximum modulus on the disc of radius
`r` is eventually at most the `k`-fold exponential of `r ^ C`. -/
def GrowthHeightAtMost (F : ℂ → ℂ) (k : ℕ) : Prop :=
  ∃ C : ℝ, ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ r → ‖F z‖ ≤ iterExp k (r ^ C)

/-- Positive lower order is growth height at least one. -/
def PositiveLowerOrder (F : ℂ → ℂ) : Prop := GrowthHeightAtLeast F 1

theorem GrowthHeightAtLeast.mono {F : ℂ → ℂ} {k l : ℕ} (h : GrowthHeightAtLeast F k)
    (hkl : l ≤ k) : GrowthHeightAtLeast F l := by
  obtain ⟨δ, hδ, hev⟩ := h
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hev] with r hr
  obtain ⟨z, hz, hle⟩ := hr
  exact ⟨z, hz, le_trans (iterExp_mono_index hkl _) hle⟩

/-- **The two heights are incompatible one step apart.** -/
theorem not_growthHeightAtLeast_succ_of_atMost {F : ℂ → ℂ} {k : ℕ}
    (h : GrowthHeightAtMost F k) : ¬ GrowthHeightAtLeast F (k + 1) := by
  rintro ⟨δ, hδ, hlow⟩
  obtain ⟨C, hup⟩ := h
  obtain ⟨r, ⟨⟨hrlow, hrup⟩, hcomp⟩⟩ :=
    ((hlow.and hup).and (eventually_iterExp_rpow_lt k C (δ := δ) hδ)).exists
  obtain ⟨z, hz, hle⟩ := hrlow
  have h1 : ‖F z‖ ≤ iterExp k (r ^ C) := hrup z hz
  exact absurd (le_trans hle h1) (not_le.mpr hcomp)

end GaloisForLFunctions.HTGeometry
