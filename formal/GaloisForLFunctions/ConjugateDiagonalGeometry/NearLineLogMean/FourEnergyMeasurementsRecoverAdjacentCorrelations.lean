import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheFirstNeighborsInTheLogWindowSpectrum

/-!
# Four energy measurements recover a block of adjacent correlations

Subtract the diagonal and measure the logarithmic window at two
lengths and two bandwidths. In the first overlap band the newly
included pairs are all adjacent. Differencing in bandwidth removes
their individual log gaps. A fixed choice of bandwidths recovers the
entire signed correlation block with coefficients of bounded size.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
open Finset Filter Topology
noncomputable section

/-- The off-diagonal part of the measured energy. -/
def excessEnergy (a : ℕ → ℂ) (N : ℕ) (d : ℝ) :=
  energy a N d - d*(∑ j ∈ range N, ‖a (j+1)‖^2)

/-- Energy per unit bandwidth after subtraction of the diagonal. -/
def normalizedExcess (a : ℕ → ℂ) (N : ℕ) (d : ℝ) := excessEnergy a N d/d

/-- Signed adjacent Gram mass on the indicated interval of indices. -/
def adjacentBlock (a : ℕ → ℂ) (A B : ℕ) :=
  ∑ j ∈ Ico A B, gram (a (j+2)) (a (j+1))

/-- Inside the first overlap band the entire excess is the triangularly weighted adjacent Gram sum. -/
theorem excess_energy_adjacent_spectrum (a : ℕ → ℂ) (N : ℕ) {d : ℝ} (hd : 0 ≤ d)
    (hw : d*((N+1 : ℕ) : ℝ) ≤ 2) : excessEnergy a (N+1) d =
      2*∑ j ∈ range N, gram (a (j+2)) (a (j+1))*max (d-adjacentLogGap (j+1)) 0 := by
  rw [excessEnergy, log_window_adjacent_band a N hd hw,add_sub_cancel_left]

private theorem excess_interval (a : ℕ → ℂ) {A B : ℕ} (hAB : A ≤ B) {d : ℝ}
    (hd : 0 ≤ d) (hlo : 1/((A+1 : ℕ) : ℝ) ≤ d) (hw : d*((B+1 : ℕ) : ℝ) ≤ 2) :
    excessEnergy a (B+1) d-excessEnergy a (A+1) d =
      2*∑ j ∈ Ico A B, gram (a (j+2)) (a (j+1))*(d-adjacentLogGap (j+1)) := by
  have hA := (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.succ_le_succ hAB)) hd).trans hw
  rw [excess_energy_adjacent_spectrum a B hd hw,excess_energy_adjacent_spectrum a A hd hA,←mul_sub,
    ←sum_Ico_eq_sub _ hAB]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hg := (adjacent_log_gap_bounds (Nat.succ_pos j)).2
  have hle : ((A+1 : ℕ) : ℝ) ≤ (j+1 : ℕ) := Nat.cast_le.mpr (Nat.succ_le_succ (mem_Ico.mp hj).1)
  have hr := (one_div_le_one_div_of_le (Nat.cast_pos.mpr (Nat.succ_pos A)) hle).trans hlo
  rw [max_eq_left (sub_nonneg.mpr (hg.trans hr))]

/-- The rectangular difference in length and bandwidth gives the
signed adjacent product with constant weight throughout the block. -/
theorem adjacent_block_rectangle (a : ℕ → ℂ) {A B : ℕ} (hab : A ≤ B) {d e : ℝ}
    (hd : 1/((A+1 : ℕ) : ℝ) ≤ d) (hde : d ≤ e) (he : e*((B+1 : ℕ) : ℝ) ≤ 2) :
    (excessEnergy a (B+1) e-excessEnergy a (A+1) e) -
      (excessEnergy a (B+1) d-excessEnergy a (A+1) d) = 2*(e-d)*adjacentBlock a A B := by
  have hp : 0 ≤ d := (by positivity : 0 ≤ 1/((A+1 : ℕ) : ℝ)).trans hd
  have hw := (mul_le_mul_of_nonneg_right hde (Nat.cast_nonneg (B+1))).trans he
  rw [excess_interval a hab (hp.trans hde) (hd.trans hde) he,excess_interval a hab hp hd hw,
    ←mul_sub,←sum_sub_distrib,adjacentBlock,mul_assoc]
  congr 1
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- Two bandwidths in ratio 3/2 have a uniformly conditioned inverse
on every block whose upper and lower endpoints are in ratio at most 4/3. -/
theorem adjacent_block_four_readings (a : ℕ → ℂ) {A B : ℕ} (hab : A ≤ B)
    (hr : 3*(B+1) ≤ 4*(A+1)) :
    let u := 1/((A+1 : ℕ) : ℝ)
    adjacentBlock a A B = (3/2 : ℝ)*(normalizedExcess a (B+1) (3*u/2)-
      normalizedExcess a (A+1) (3*u/2)) -
      (normalizedExcess a (B+1) u-normalizedExcess a (A+1) u) := by
  let u := 1/((A+1 : ℕ) : ℝ)
  have hA : (0 : ℝ)<(A+1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hu : 0<u := one_div_pos.mpr hA
  have hv : 0<3*u/2 := by positivity
  have hr' : 3*((B+1 : ℕ) : ℝ) ≤ 4*((A+1 : ℕ) : ℝ) := by exact_mod_cast hr
  have he : (3*u/2)*((B+1 : ℕ) : ℝ) ≤ 2 := by
    dsimp only [u]
    field_simp [hA]
    linarith only [hr']
  have hh := adjacent_block_rectangle a hab (d:=u) le_rfl (show u≤3*u/2 by linarith only [hu]) he
  have hscale (K : ℕ) {v : ℝ} (hv : v≠0) : excessEnergy a K v = v*normalizedExcess a K v := by
    unfold normalizedExcess
    field_simp [hv]
  rw [hscale (B+1) hv.ne',hscale (A+1) hv.ne',hscale (B+1) hu.ne',hscale (A+1) hu.ne'] at hh
  change adjacentBlock a A B = (3/2 : ℝ)*(_-_)-(_-_)
  apply mul_left_cancel₀ hu.ne'
  linear_combination -hh

/-- Uniform convergence of the measured normalized energy to its
diagonal in the first overlap band forces cancellation of every
multiplicatively short block of adjacent correlations. -/
theorem adjacent_block_cancellation_of_near_diagonal (a : ℕ → ℂ) :
    (∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ d : ℝ,
      1 ≤ d*((N+1 : ℕ) : ℝ) → d*((N+1 : ℕ) : ℝ) ≤ 2 →
      |normalizedExcess a (N+1) d| ≤ η) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ A : ℕ in atTop, ∀ B : ℕ, A ≤ B → 3*(B+1) ≤ 4*(A+1) →
      |adjacentBlock a A B| ≤ ε := by
  intro h ε hε
  let η := ε/5
  obtain ⟨K,hK⟩ := eventually_atTop.mp (h η (by dsimp only [η]; positivity))
  filter_upwards [eventually_ge_atTop K] with A hA
  intro B hab hr
  let u := 1/((A+1 : ℕ) : ℝ)
  have hp : (0 : ℝ)<(A+1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hu : 0<u := one_div_pos.mpr hp
  have hA1 : u*((A+1 : ℕ) : ℝ)=1 := by dsimp only [u]; field_simp [hp.ne']
  have hn : ((A+1 : ℕ) : ℝ) ≤ (B+1 : ℕ) := Nat.cast_le.mpr (Nat.succ_le_succ hab)
  have hB1 : 1≤u*((B+1 : ℕ) : ℝ) := hA1.symm.le.trans (mul_le_mul_of_nonneg_left hn hu.le)
  have hB4 : u*((B+1 : ℕ) : ℝ)≤4/3 := by
    have hr' : 3*((B+1 : ℕ) : ℝ) ≤ 4*((A+1 : ℕ) : ℝ) := by exact_mod_cast hr
    dsimp only [u]
    field_simp [hp]
    linarith only [hr']
  have scale (z : ℝ) : (3*u/2)*z = 3*(u*z)/2 := by ring
  have h₁ := abs_le.mp (hK A hA u hA1.ge (by linarith only [hA1]))
  have h₂ := abs_le.mp (hK B (hA.trans hab) u hB1 (by linarith only [hB4]))
  have h₃ := abs_le.mp (hK A hA (3*u/2) (by rw [scale,hA1]; norm_num) (by rw [scale,hA1]; norm_num))
  have h₄ := abs_le.mp (hK B (hA.trans hab) (3*u/2)
    (by rw [scale];linarith only [hB1]) (by rw [scale];linarith only [hB4]))
  rw [adjacent_block_four_readings a hab hr]
  change |(3/2 : ℝ)*(normalizedExcess a (B+1) (3*u/2)-normalizedExcess a (A+1) (3*u/2))-
    (normalizedExcess a (B+1) u-normalizedExcess a (A+1) u)| ≤ ε
  have hη : 5*η=ε := by dsimp only [η]; ring
  exact abs_le.mpr ⟨by linarith only [h₁.1,h₂.2,h₃.2,h₄.1,hη],
    by linarith only [h₁.2,h₂.1,h₃.1,h₄.2,hη]⟩

#print axioms excess_energy_adjacent_spectrum
#print axioms adjacent_block_rectangle
#print axioms adjacent_block_four_readings
#print axioms adjacent_block_cancellation_of_near_diagonal
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
