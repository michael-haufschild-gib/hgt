import GaloisForLFunctions.HTGeometry.SteinbergTWTClosureFinFourW23
import GaloisForLFunctions.HTGeometry.SteinbergTWTorusClosure
import GaloisForLFunctions.HTGeometry.SteinbergWeylTriangle

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

theorem fin4_weyl_eq_torus_mul_simple {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    steinbergWeyl hij u = steinbergTorus hij u * steinbergWeyl hij (1 : Fˣ) := by
  rw [steinbergTorus, steinbergWeyl_neg hij (1 : Fˣ)]
  group

theorem fin4_hspare : ∀ i j : Fin 4, i ≠ j → ∃ m : Fin 4, i ≠ m ∧ j ≠ m := by
  intro i j _
  obtain ⟨m, hmi, hmj⟩ := exists_third_index (by decide) i j
  exact ⟨m, hmi.symm, hmj.symm⟩

theorem fin4_steinbergTWT_mul_w01_unit {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4)) (u : Fˣ) :
    g * steinbergWeyl (by decide : (0 : Fin 4) ≠ 1) u
      ∈ steinbergTWT (F := F) (n := Fin 4) := by
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  rw [fin4_weyl_eq_torus_mul_simple h01]
  have htorus := steinbergTWT_mul_torus fin4_hspare hg h01 u
  simpa only [mul_assoc] using fin4_steinbergTWT_mul_w01 htorus

theorem fin4_steinbergTWT_mul_w12_unit {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4)) (u : Fˣ) :
    g * steinbergWeyl (by decide : (1 : Fin 4) ≠ 2) u
      ∈ steinbergTWT (F := F) (n := Fin 4) := by
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  rw [fin4_weyl_eq_torus_mul_simple h12]
  have htorus := steinbergTWT_mul_torus fin4_hspare hg h12 u
  simpa only [mul_assoc] using fin4_steinbergTWT_mul_w12 htorus

theorem fin4_steinbergTWT_mul_w23_unit {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4)) (u : Fˣ) :
    g * steinbergWeyl (by decide : (2 : Fin 4) ≠ 3) u
      ∈ steinbergTWT (F := F) (n := Fin 4) := by
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  rw [fin4_weyl_eq_torus_mul_simple h23]
  have htorus := steinbergTWT_mul_torus fin4_hspare hg h23 u
  simpa only [mul_assoc] using fin4_steinbergTWT_mul_w23 htorus

theorem fin4_steinbergTWT_mul_w02_unit {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4)) (u : Fˣ) :
    g * steinbergWeyl (by decide : (0 : Fin 4) ≠ 2) u
      ∈ steinbergTWT (F := F) (n := Fin 4) := by
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  let h02 : (0 : Fin 4) ≠ 2 := by decide
  rw [← steinbergWeyl_triangle h02 h01 (Ne.symm h12) u]
  have h1 := fin4_steinbergTWT_mul_w01_unit hg u
  have h2 := fin4_steinbergTWT_mul_w12_unit h1 (1 : Fˣ)
  simpa only [mul_assoc] using fin4_steinbergTWT_mul_w01_unit h2 (-u)

theorem fin4_steinbergTWT_mul_w13_unit {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4)) (u : Fˣ) :
    g * steinbergWeyl (by decide : (1 : Fin 4) ≠ 3) u
      ∈ steinbergTWT (F := F) (n := Fin 4) := by
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  rw [← steinbergWeyl_triangle h13 h12 (Ne.symm h23) u]
  have h1 := fin4_steinbergTWT_mul_w12_unit hg u
  have h2 := fin4_steinbergTWT_mul_w23_unit h1 (1 : Fˣ)
  simpa only [mul_assoc] using fin4_steinbergTWT_mul_w12_unit h2 (-u)

theorem fin4_steinbergTWT_mul_w03_unit {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4)) (u : Fˣ) :
    g * steinbergWeyl (by decide : (0 : Fin 4) ≠ 3) u
      ∈ steinbergTWT (F := F) (n := Fin 4) := by
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  rw [← steinbergWeyl_triangle h03 h01 (Ne.symm h13) u]
  have h1 := fin4_steinbergTWT_mul_w01_unit hg u
  have h2 := fin4_steinbergTWT_mul_w13_unit h1 (1 : Fˣ)
  simpa only [mul_assoc] using fin4_steinbergTWT_mul_w01_unit h2 (-u)

/-- `TWT` is stable under every Weyl generator in rank four. -/
theorem fin4_steinbergTWT_mul_weyl {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4))
    {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    g * steinbergWeyl hij u ∈ steinbergTWT (F := F) (n := Fin 4) := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact fin4_steinbergTWT_mul_w01_unit hg u
  · exact fin4_steinbergTWT_mul_w02_unit hg u
  · exact fin4_steinbergTWT_mul_w03_unit hg u
  · rw [steinbergWeyl_reverse (k := 2) hij (by decide) (by decide) u]
    exact fin4_steinbergTWT_mul_w01_unit hg (-u⁻¹)
  · exact (hij rfl).elim
  · exact fin4_steinbergTWT_mul_w12_unit hg u
  · exact fin4_steinbergTWT_mul_w13_unit hg u
  · rw [steinbergWeyl_reverse (k := 1) hij (by decide) (by decide) u]
    exact fin4_steinbergTWT_mul_w02_unit hg (-u⁻¹)
  · rw [steinbergWeyl_reverse (k := 0) hij (by decide) (by decide) u]
    exact fin4_steinbergTWT_mul_w12_unit hg (-u⁻¹)
  · exact (hij rfl).elim
  · exact fin4_steinbergTWT_mul_w23_unit hg u
  · rw [steinbergWeyl_reverse (k := 1) hij (by decide) (by decide) u]
    exact fin4_steinbergTWT_mul_w03_unit hg (-u⁻¹)
  · rw [steinbergWeyl_reverse (k := 0) hij (by decide) (by decide) u]
    exact fin4_steinbergTWT_mul_w13_unit hg (-u⁻¹)
  · rw [steinbergWeyl_reverse (k := 0) hij (by decide) (by decide) u]
    exact fin4_steinbergTWT_mul_w23_unit hg (-u⁻¹)
  · exact (hij rfl).elim

end GaloisForLFunctions.HTGeometry
