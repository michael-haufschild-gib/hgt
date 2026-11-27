import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.Relative.MovingGrid
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.PhysicalBonds

/-! # Relative Gaussian box bounds at all radii above logarithmic mean -/
open Set Filter MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BlockDilations.AdaptiveCuts
open private count_mono from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.MovingBoxes
open private physical_counts from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.PhysicalBonds
noncomputable section

/-- Rounding a radius up to the reciprocal grid costs at most a factor
two in radius. The required expected count grows only logarithmically. -/
theorem gaussian_relative_weak_upper :
    ∃ d>0, ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ h∈Ioc (0:ℝ) 1,
      let N : ℝ := (n+1:ℕ)
      1≤N*h → 16*log N≤d*h^9*N →
      ((weakEdges (pathPauliDisorderShell ω n) h).card:ℝ)≤C*N*h^9 := by
  let d := (2*gaussianDensityFloor)^9
  have hd : 0<d := pow_pos (mul_pos zero_lt_two gaussianDensityFloor_pos) 9
  let radii (m : ℕ) (i : Fin m) := 1/((i.val+1:ℕ):ℝ)
  obtain hw := gaussian_relative_box_grid 0 1 one_pos id radii
  refine ⟨d,hd,4*4^9*2^9,by norm_num,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hω] with n hn
  intro h hh N hsize hmass
  let j := ⌊1/h⌋₊
  have hrec : 1≤1/h := (le_div_iff₀ hh.1).mpr (by simpa only [one_mul] using hh.2)
  have hj : 1≤j := Nat.le_floor (by simpa only [Nat.cast_one] using hrec)
  have hjpos : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have hjN : j≤n+1 := by
    apply (Nat.cast_le (α:=ℝ)).mp
    exact (Nat.floor_le (one_div_pos.mpr hh.1).le).trans ((div_le_iff₀ hh.1).mpr hsize)
  let i : Fin (n+1) := ⟨j-1,by omega⟩
  let r := 1/(j:ℝ)
  have he : radii (n+1) i=r := by change 1/((j-1+1:ℕ):ℝ)=_; rw [Nat.sub_add_cancel hj]
  have hl := (le_div_iff₀ hh.1).mp (Nat.floor_le (one_div_pos.mpr hh.1).le)
  have hu := (div_lt_iff₀ hh.1).mp (Nat.lt_floor_add_one (1/h))
  change (j:ℝ)*h≤1 at hl
  change 1<((j:ℝ)+1)*h at hu
  have hr : h≤r := (le_div_iff₀ hjpos).mpr (by linarith only [hl])
  have hJ₁ : (1:ℝ)≤j := by exact_mod_cast hj
  have hr' : r≤2*h := (div_le_iff₀ hjpos).mpr (by
    linarith only [hu,mul_le_mul_of_nonneg_right hJ₁ hh.1.le])
  have hbox := box_probability (one_div_pos.mpr hjpos) ((div_le_one hjpos).mpr hJ₁)
  have hlow : d*h^9≤bondLaw.real (weakBond r) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.1.le hr 9) hd.le).trans hbox.1
  have hg := hn i
  dsimp only [id] at hg
  rw [he] at hg
  have hpr := (hg (hmass.trans (mul_le_mul_of_nonneg_right hlow (Nat.cast_nonneg _)))).2.le
  rw [(physical_counts ω n h).1]
  calc
    _ ≤ (boxCount ω 0 1 (n+1) r:ℝ) := Nat.cast_le.mpr (count_mono ω 0 1 (n+1) hr)
    _ ≤ 4*(bondLaw.real (weakBond r)*N) := hpr
    _ ≤ 4*((4^9*(2*h)^9)*N) := by
      have hb := hbox.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (one_div_pos.mpr hjpos).le hr' 9)
        (by norm_num : (0:ℝ)≤4^9))
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)) (by norm_num)
    _ = _ := by ring

#print axioms gaussian_relative_weak_upper
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
