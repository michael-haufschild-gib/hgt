/-
# The basin of infinity and the full-basin Böttcher coordinate (hRigid lane)

For the both-connected case of `q62` (Eremenko–van Strien rigidity), the inverse Böttcher coordinate
`φ_c` must be seen as a function on the whole **basin of `∞`** `ℂ \ K_c` (not just the `escapeOpen`
germ near `∞`), whose natural boundary is the Julia set `J_c = ∂K_c`. This file builds the basin and
its identification with the filled-Julia complement; the full-basin extension of `φ_c` (via the
functional equation `φ_c(z) = φ_c(f_c z)^{1/2}`) and the natural boundary are the analytic core that
feeds `BottcherIndep.no_phi_relation_of_natural_boundary`.

New file (hRigid lane); only consumes `BottcherCoord`/`Dynamics`.
-/
import GaloisForLFunctions.Bottcher.BottcherCoord

open Metric

namespace Bottcher

/-- **The basin of `∞`.** Points whose forward orbit eventually enters `escapeOpen c` (exceeds
`max 2 ‖c‖`, hence escapes to `∞`). The domain of the inverse Böttcher coordinate. -/
def basin (c : ℂ) : Set ℂ := {z | ∃ n : ℕ, (quadratic c)^[n] z ∈ escapeOpen c}

/-- The germ domain `escapeOpen c` sits inside the basin (`n = 0`). -/
theorem escapeOpen_subset_basin (c : ℂ) : escapeOpen c ⊆ basin c := fun z hz => ⟨0, by simpa using hz⟩

/-- **The basin is exactly the complement of the filled Julia set** `ℂ \ K_c`: a point escapes iff its
orbit is unbounded. -/
theorem basin_eq_compl_filledJulia (c : ℂ) : basin c = (filledJulia c)ᶜ := by
  ext z
  simp only [basin, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · rintro ⟨n, hn⟩ hzK
    have hfwd := filledJulia_forward hzK n
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hn
    exact not_mem_filledJulia hc hz2 hfwd
  · intro hzK
    rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le] at hzK
    push Not at hzK
    obtain ⟨x, hxmem, hx⟩ := hzK (max 2 ‖c‖)
    obtain ⟨n, hn⟩ := hxmem
    refine ⟨n, ?_⟩
    rw [escapeOpen, Set.mem_setOf_eq, show (quadratic c)^[n] z = x from hn]
    exact hx

/-- The basin is open (`escapeOpen` is open and `f_c` is continuous, so its iterated preimages are). -/
theorem isOpen_basin (c : ℂ) : IsOpen (basin c) := by
  rw [basin_eq_compl_filledJulia]
  exact (isClosed_filledJulia c).isOpen_compl

/-- The basin is unbounded (it contains the whole `escapeOpen c`, an exterior neighborhood of `∞`). -/
theorem not_isBounded_basin (c : ℂ) : ¬ Bornology.IsBounded (basin c) := by
  rw [isBounded_iff_forall_norm_le]
  push Not
  intro C
  have hmax : (0 : ℝ) < max C (max 2 ‖c‖) + 1 := by
    have h2 : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    have := le_max_right C (max 2 ‖c‖)
    linarith
  refine ⟨((max C (max 2 ‖c‖) + 1 : ℝ) : ℂ), escapeOpen_subset_basin c ?_, ?_⟩
  · rw [escapeOpen, Set.mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmax]
    have := le_max_right C (max 2 ‖c‖); linarith
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmax]
    have := le_max_left C (max 2 ‖c‖); linarith

end Bottcher
