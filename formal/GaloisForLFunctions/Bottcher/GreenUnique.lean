/-
# Böttcher tower — the filled Julia set determines the Green's function (E1)

If two connected quadratic parameters have the **same filled Julia set**, they have the **same Green's
function**: `K_{c₁} = K_{c₂} ⟹ G_{c₁} = G_{c₂}`. This is the uniqueness half of brick E (distinctness
of Julia sets for distinct parameters).

The difference `u = G_{c₁} − G_{c₂}` is: harmonic on the common basin `Ω = K_cᶜ`
(`harmonicOnNhd_greenLimit_basin`), continuous on all of `ℂ` (`continuous_greenFunctionDyn`, D1),
`= 0` on `K` (both Green's functions vanish there), and `→ 0` at `∞` (`tendsto_greenLimit_sub_log`).
The exterior maximum-principle uniqueness `harmonic_exterior_unique` then forces `u ≡ 0` — provided the
basin is preconnected (`K_c` full), the one remaining topological input.

New file (hRigid connected lane); consumes `GreenContinuity`, `BottcherBasin`, `HarmonicMinPrinciple`.
-/
import GaloisForLFunctions.Bottcher.GreenContinuity
import GaloisForLFunctions.Bottcher.BottcherBasin
import GaloisForLFunctions.Bottcher.HarmonicMinPrinciple

open Filter Topology Metric Bornology Set InnerProductSpace

namespace Bottcher

/-- **`K` determines `G` (E1).** Equal filled Julia sets ⟹ equal Green's functions, given the basin is
preconnected (`K_c` full). The Green-difference is harmonic on the basin, continuous on `ℂ`, vanishes
on `K`, and `→0` at `∞`; `harmonic_exterior_unique` closes it. -/
theorem greenFunctionDyn_eq_of_filledJulia_eq {c₁ c₂ : ℂ}
    (hK : filledJulia c₁ = filledJulia c₂)
    (hconn : IsPreconnected (filledJulia c₁)ᶜ) :
    greenFunctionDyn c₁ = greenFunctionDyn c₂ := by
  set u : ℂ → ℝ := fun z => greenFunctionDyn c₁ z - greenFunctionDyn c₂ z with hudef
  have hu0 : u = 0 := by
    refine harmonic_exterior_unique (Ω := (filledJulia c₁)ᶜ)
      ((isClosed_filledJulia c₁).isOpen_compl) hconn ?_ ?_ ?_ ?_ ?_
    · -- Ω unbounded
      rw [← basin_eq_compl_filledJulia]
      exact not_isBounded_basin c₁
    · -- u harmonic on Ω
      intro z hz
      have hz1 : z ∉ filledJulia c₁ := hz
      have hz2 : z ∉ filledJulia c₂ := hK ▸ hz1
      have heq : u =ᶠ[𝓝 z] (fun w => greenLimit c₁ w - greenLimit c₂ w) := by
        filter_upwards [((isClosed_filledJulia c₁).isOpen_compl).mem_nhds hz] with w hw
        have hw1 : w ∉ filledJulia c₁ := hw
        have hw2 : w ∉ filledJulia c₂ := hK ▸ hw1
        simp only [hudef, greenFunctionDyn, if_neg hw1, if_neg hw2]
      have hh : HarmonicAt (fun w => greenLimit c₁ w - greenLimit c₂ w) z :=
        (harmonicOnNhd_greenLimit_basin c₁ z hz1).sub (harmonicOnNhd_greenLimit_basin c₂ z hz2)
      exact (harmonicAt_congr_nhds heq).mpr hh
    · -- u continuous on ℂ
      exact (continuous_greenFunctionDyn c₁).sub (continuous_greenFunctionDyn c₂)
    · -- u = 0 off Ω (on K)
      intro z hz
      have hz1 : z ∈ filledJulia c₁ := by simpa using hz
      have hz2 : z ∈ filledJulia c₂ := hK ▸ hz1
      simp only [hudef, greenFunctionDyn, if_pos hz1, if_pos hz2, sub_zero]
    · -- u → 0 at ∞
      have hΩ₁ : (filledJulia c₁)ᶜ ∈ cobounded ℂ :=
        isBounded_compl_iff.mp (by rw [compl_compl]; exact isBounded_filledJulia c₁)
      have hΩ₂ : (filledJulia c₂)ᶜ ∈ cobounded ℂ :=
        isBounded_compl_iff.mp (by rw [compl_compl]; exact isBounded_filledJulia c₂)
      have hev : u =ᶠ[cobounded ℂ]
          (fun z => (greenLimit c₁ z - Real.log ‖z‖) - (greenLimit c₂ z - Real.log ‖z‖)) := by
        filter_upwards [hΩ₁, hΩ₂] with z hz1 hz2
        simp only [hudef, greenFunctionDyn, if_neg hz1, if_neg hz2]
        ring
      have htw : Tendsto
          (fun z => (greenLimit c₁ z - Real.log ‖z‖) - (greenLimit c₂ z - Real.log ‖z‖))
          (cobounded ℂ) (𝓝 0) := by
        simpa using (tendsto_greenLimit_sub_log c₁).sub (tendsto_greenLimit_sub_log c₂)
      exact Filter.Tendsto.congr' hev.symm htw
  funext z
  have h := congrFun hu0 z
  simp only [hudef, Pi.zero_apply] at h
  linarith

end Bottcher
