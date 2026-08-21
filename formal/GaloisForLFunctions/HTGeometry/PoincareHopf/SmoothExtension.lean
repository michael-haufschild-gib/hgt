import GaloisForLFunctions.HTGeometry.PoincareHopf.IndexPushforward
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Globally smooth representatives of locally smooth fields

A field that is `C²` on an open set may be replaced, without changing it on a smaller closed ball,
by a globally `C²` field: multiply by a smooth bump equal to one on that ball and supported in the
open set, and extend by zero.  Degree theory is stated for globally smooth maps, and this is what
lets it be applied to a field given only in a chart.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ}

theorem exists_contDiff_extension {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {v : (Fin n → ℝ) → (Fin n → ℝ)} (hv : ContDiffOn ℝ 2 v U)
    {q : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall q r ⊆ U) :
    ∃ u : (Fin n → ℝ) → (Fin n → ℝ), ContDiff ℝ 2 u ∧
      ∀ x ∈ Metric.closedBall q (r / 2), u x = v x := by
  classical
  set f : ContDiffBump q := ⟨r / 2, r, by linarith, by linarith⟩ with hf
  set u : (Fin n → ℝ) → (Fin n → ℝ) := fun x => if x ∈ U then f x • v x else 0 with hu
  have hfout : ∀ x, r ≤ ‖x - q‖ → f x = 0 := by
    intro x hx
    have hsupp := ContDiffBump.support_eq f
    by_contra hne
    have hmem : x ∈ Function.support (⇑f) := hne
    rw [hsupp, Metric.mem_ball, dist_eq_norm] at hmem
    have : f.rOut = r := rfl
    rw [this] at hmem
    linarith
  have huzero : ∀ x ∉ Metric.closedBall q r, u x = 0 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hx
    by_cases hxU : x ∈ U
    · rw [hu]
      simp only [if_pos hxU, hfout x hx.le, zero_smul]
    · rw [hu]
      simp only [if_neg hxU]
  refine ⟨u, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxU : x ∈ U
    · have hev : u =ᶠ[nhds x] fun z => f z • v z := by
        filter_upwards [hU.mem_nhds hxU] with z hz
        rw [hu]
        simp only [if_pos hz]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      exact (f.contDiff.contDiffAt).smul ((hv.contDiffAt (hU.mem_nhds hxU)))
    · have hxout : x ∉ Metric.closedBall q r := fun hmem => hxU (hball hmem)
      have hopen : IsOpen (Metric.closedBall q r)ᶜ := Metric.isClosed_closedBall.isOpen_compl
      have hev : u =ᶠ[nhds x] fun _ => (0 : Fin n → ℝ) := by
        filter_upwards [hopen.mem_nhds hxout] with z hz
        exact huzero z hz
      exact (contDiffAt_const (c := (0 : Fin n → ℝ))).congr_of_eventuallyEq hev
  · intro x hx
    have hxU : x ∈ U := hball (Metric.closedBall_subset_closedBall (by linarith) hx)
    have hone : f x = 1 := ContDiffBump.one_of_mem_closedBall f hx
    rw [hu]
    simp only [if_pos hxU, hone, one_smul]

variable {v v₁ v₂ : (Fin n → ℝ) → (Fin n → ℝ)} {p : Fin n → ℝ} {ε : ℝ}

/-- The index only depends on the field near the point. -/
theorem index_congr (hv₁ : ContDiff ℝ 2 v₁) (hv₂ : ContDiff ℝ 2 v₂) (hεpos : 0 < ε)
    (heq : ∀ x ∈ Metric.closedBall p ε, v₁ x = v₂ x) (hiso : IsolatingRadius v₁ p ε) :
    index v₁ p = index v₂ p := by
  have hiso₂ : IsolatingRadius v₂ p ε :=
    ⟨hεpos, fun x hx hxp => by rw [← heq x hx]; exact hiso.2 x hx hxp⟩
  rw [index_eq_degree hv₁ hiso, index_eq_degree hv₂ hiso₂]
  exact degree_congr hv₁ hv₂ Metric.isOpen_ball Metric.isBounded_ball
    (fun x hx => heq x (Metric.closure_ball_subset_closedBall hx))

/-- `k` is the index at `p` of a field defined only near `p`: some globally `C²` field agreeing
with it on a closed ball around `p`, isolating `p`, has index `k` there. -/
def HasIndex (v : (Fin n → ℝ) → (Fin n → ℝ)) (p : Fin n → ℝ) (k : ℝ) : Prop :=
  ∃ (u : (Fin n → ℝ) → (Fin n → ℝ)) (ε : ℝ), ContDiff ℝ 2 u ∧ 0 < ε ∧
    (∀ x ∈ Metric.closedBall p ε, u x = v x) ∧ IsolatingRadius u p ε ∧ index u p = k

theorem HasIndex.unique {k₁ k₂ : ℝ} (h₁ : HasIndex v p k₁) (h₂ : HasIndex v p k₂) : k₁ = k₂ := by
  obtain ⟨u₁, ε₁, hu₁, hε₁, heq₁, hiso₁, hk₁⟩ := h₁
  obtain ⟨u₂, ε₂, hu₂, hε₂, heq₂, hiso₂, hk₂⟩ := h₂
  set ε := min ε₁ ε₂ with hε
  have hεpos : 0 < ε := lt_min hε₁ hε₂
  have hsub₁ : Metric.closedBall p ε ⊆ Metric.closedBall p ε₁ :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hsub₂ : Metric.closedBall p ε ⊆ Metric.closedBall p ε₂ :=
    Metric.closedBall_subset_closedBall (min_le_right _ _)
  have heq : ∀ x ∈ Metric.closedBall p ε, u₁ x = u₂ x := fun x hx => by
    rw [heq₁ x (hsub₁ hx), heq₂ x (hsub₂ hx)]
  have hisoε : IsolatingRadius u₁ p ε := hiso₁.mono hεpos (min_le_left _ _)
  rw [← hk₁, ← hk₂]
  exact index_congr hu₁ hu₂ hεpos heq hisoε

open scoped Classical in
/-- The index at `p` of a field defined only near `p`. -/
noncomputable def localIndex (v : (Fin n → ℝ) → (Fin n → ℝ)) (p : Fin n → ℝ) : ℝ :=
  if h : ∃ k, HasIndex v p k then Classical.choose h else 0

theorem localIndex_eq {k : ℝ} (h : HasIndex v p k) : localIndex v p = k := by
  classical
  have hex : ∃ k, HasIndex v p k := ⟨k, h⟩
  rw [localIndex, dif_pos hex]
  exact (Classical.choose_spec hex).unique h

/-- A field that is `C²` on an open set and has an isolated zero there has a local index. -/
theorem hasIndex_of_contDiffOn {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hv : ContDiffOn ℝ 2 v U) (hεpos : 0 < ε) (hball : Metric.closedBall p ε ⊆ U)
    (hiso : ∀ x ∈ Metric.closedBall p ε, x ≠ p → v x ≠ 0) :
    ∃ k, HasIndex v p k := by
  obtain ⟨u, hu, heq⟩ := exists_contDiff_extension hU hv hεpos hball
  refine ⟨index u p, u, ε / 2, hu, by linarith, heq, ⟨by linarith, fun x hx hxp => ?_⟩, rfl⟩
  rw [heq x hx]
  exact hiso x (Metric.closedBall_subset_closedBall (by linarith) hx) hxp

/-- For a globally `C²` field the local index is the index. -/
theorem localIndex_eq_index (hv : ContDiff ℝ 2 v) (hiso : IsolatingRadius v p ε) :
    localIndex v p = index v p :=
  localIndex_eq ⟨v, ε, hv, hiso.1, fun _ _ => rfl, hiso, rfl⟩

/-- **Chart invariance of the local index.** -/
theorem localIndex_pushforward {ψ w : (Fin n → ℝ) → (Fin n → ℝ)} {ε₀ : ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hv : ContDiff ℝ 2 v) (hw : ContDiff ℝ 2 w) (hε₀ : 0 < ε₀)
    (hinj : Set.InjOn ψ (Metric.closedBall p ε₀))
    (hopenmap : ∀ S ⊆ Metric.ball p ε₀, IsOpen S → IsOpen (ψ '' S))
    (hdet : (jac ψ p).det ≠ 0)
    (hiso : ∀ x ∈ Metric.closedBall p ε₀, x ≠ p → v x ≠ 0)
    (htrans : ∀ x ∈ Metric.closedBall p ε₀, w (ψ x) = matVec (jac ψ x) (v x)) :
    localIndex w (ψ p) = localIndex v p := by
  obtain ⟨εw, hεw, hisow⟩ :=
    exists_isolating_pushforward hψ hv hw hε₀ hinj hopenmap hdet hiso htrans
  rw [localIndex_eq_index hw hisow, localIndex_eq_index hv ⟨hε₀, hiso⟩]
  exact index_pushforward hψ hv hw hε₀ hinj hopenmap hdet hiso htrans

end GaloisForLFunctions.HTGeometry.PoincareHopf
