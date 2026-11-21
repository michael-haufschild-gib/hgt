import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateFullOccupation

/-!
# Uniform zero-gate occupation over tolerances

Monotonicity brackets every empirical occupation between two grid values.
The Haar variation across a grid cell controls the error between the nodes.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Equally spaced arc tolerances, including both endpoints of the unit turn. -/
def unitTurnGrid {m : ℕ} (hm : 0 < m) (j : Fin (m + 1)) : Icc (0 : ℝ) 1 :=
  ⟨(j.val : ℝ) / m, by positivity,
    (div_le_one (Nat.cast_pos.mpr hm)).mpr (by exact_mod_cast Nat.lt_succ_iff.mp j.isLt)⟩

private theorem exists_unitTurnGrid_bracket {m : ℕ} (hm : 0 < m) (r : Icc (0 : ℝ) 1) :
    ∃ i j, (unitTurnGrid hm i : ℝ) ≤ r ∧ (r : ℝ) ≤ unitTurnGrid hm j ∧
      (unitTurnGrid hm j : ℝ) - unitTurnGrid hm i ≤ 1 / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  by_cases hr : (r : ℝ) = 1
  · let i : Fin (m + 1) := ⟨m, Nat.lt_succ_self _⟩
    have hi : (unitTurnGrid hm i : ℝ) = 1 := div_self hmR.ne'
    exact ⟨i, i, by rw [hi, hr], by rw [hi, hr], by rw [sub_self]; positivity⟩
  let k := ⌊(m : ℝ) * (r : ℝ)⌋₊
  have hk := Nat.floor_le (mul_nonneg hmR.le r.2.1)
  have hk' := Nat.lt_floor_add_one ((m : ℝ) * (r : ℝ))
  have hkmR : (k : ℝ) < m := hk.trans_lt (by
    simpa only [mul_one] using mul_lt_mul_of_pos_left (lt_of_le_of_ne r.2.2 hr) hmR)
  have hkm : k < m := by exact_mod_cast hkmR
  let i : Fin (m + 1) := ⟨k, by omega⟩
  let j : Fin (m + 1) := ⟨k + 1, by omega⟩
  refine ⟨i, j, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hmR).mpr
    simpa only [mul_comm (r : ℝ)] using hk
  · apply (le_div_iff₀ hmR).mpr
    simpa only [j, Nat.cast_add, Nat.cast_one, mul_comm (r : ℝ)] using hk'.le
  · change (((k + 1 : ℕ) : ℝ) / m - (k : ℝ) / m) ≤ 1 / (m : ℝ)
    rw [Nat.cast_add, Nat.cast_one, add_div]
    linarith only

/-- Bounds at a finite grid of radii control the full empirical occupation
error, with a loss at most the Haar Lipschitz constant divided by grid size. -/
theorem zeroGateFullOccupation_error_le_grid {n m : ℕ} (H : selfAdjoint (Reg n)) (hm : 0 < m)
    {a T d : ℝ} (haT : a ≤ T)
    (hgrid : ∀ j : Fin (m + 1),
      |volume.real (zeroGateReturnSet H (unitTurnGrid hm j) ∩ Icc a T) / (T - a) -
        zeroGateFullArcMass n (unitTurnGrid hm j)| ≤ d) (r : Icc (0 : ℝ) 1) :
    |volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a) - zeroGateFullArcMass n r| ≤
      d + (Fintype.card (Fin n → Bool) : ℝ) * ((Fintype.card (Fin n → Bool) - 1 : ℕ) : ℝ) / m := by
  let ref : Fin n → Bool := fun _ => false
  let K := (Fintype.card (Fin n → Bool) : ℝ) * ((Fintype.card (Fin n → Bool) - 1 : ℕ) : ℝ)
  let F (s : Icc (0 : ℝ) 1) := volume.real (zeroGateReturnSet H s ∩ Icc a T) / (T - a)
  let p (s : Icc (0 : ℝ) 1) := zeroGateFullArcMass n s
  have hF (s t : Icc (0 : ℝ) 1) (hst : (s : ℝ) ≤ t) : F s ≤ F t := by
    have hsub : zeroGateReturnSet H s ⊆ zeroGateReturnSet H t := by
      rw [zeroGateReturnSet_eq_preimage_full H ref s, zeroGateReturnSet_eq_preimage_full H ref t]
      exact preimage_mono (relativeEnclosingUnitArc_mono ref hst)
    exact div_le_div_of_nonneg_right
      (measureReal_mono (inter_subset_inter_left _ hsub)
        (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)) (sub_nonneg.mpr haT)
  have hp (s t : Icc (0 : ℝ) 1) (hst : (s : ℝ) ≤ t) : p s ≤ p t := relativeUnitArcMass_mono ref hst
  obtain ⟨i, j, hi, hj, hstep⟩ := exists_unitTurnGrid_bracket hm r
  let l := unitTurnGrid hm i
  let u := unitTurnGrid hm j
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hwidth : p u - p l ≤ K / m := calc
    _ ≤ K * ((u : ℝ) - l) := relativeUnitArcMass_sub_le ref l u (hi.trans hj)
    _ ≤ K * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_left hstep hK
    _ = K / m := by rw [← mul_div_assoc, mul_one]
  change |F r - p r| ≤ d + K / m
  have hlow : -d ≤ F l - p l := (abs_le.mp (hgrid i)).1
  have hhigh : F u - p u ≤ d := (abs_le.mp (hgrid j)).2
  apply abs_le.mpr
  constructor
  · linarith only [hF l r hi, hp r u hj, hwidth, hlow]
  · linarith only [hF r u hj, hp l r hi, hwidth, hhigh]

/-- The return fractions converge simultaneously across the entire tolerance
range, so the tolerance can be chosen after observing the time window. -/
theorem maximallyProjective_zeroGateFullOccupation_uniform {n : ℕ} (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ r : Icc (0 : ℝ) 1,
      |volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a) - zeroGateFullArcMass n r| < ε := by
  let K := (Fintype.card (Fin n → Bool) : ℝ) * ((Fintype.card (Fin n → Bool) - 1 : ℕ) : ℝ)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨m, hm⟩ := exists_nat_gt (K / (ε / 2))
  have hmpos : 0 < m := by
    exact_mod_cast (div_nonneg hK hhalf.le).trans_lt hm
  have hstep : K / (m : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hmpos)).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hhalf).mp hm
  have hgrid : ∀ᶠ T in atTop, ∀ j : Fin (m + 1),
      |volume.real (zeroGateReturnSet H (unitTurnGrid hmpos j) ∩ Icc a T) / (T - a) -
        zeroGateFullArcMass n (unitTurnGrid hmpos j)| < ε / 2 := by
    let err (T : ℝ) (j : Fin (m + 1)) :=
      |volume.real (zeroGateReturnSet H (unitTurnGrid hmpos j) ∩ Icc a T) / (T - a) -
        zeroGateFullArcMass n (unitTurnGrid hmpos j)|
    have hnode (j : Fin (m + 1)) : ∀ᶠ T in atTop, err T j < ε / 2 := by
      have h := maximallyProjective_zeroGateFullOccupation_from_start H hmax (unitTurnGrid hmpos j) a
      simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp h) (ε / 2) hhalf
    have hnodes : ∀ᶠ T in atTop, ∀ j ∈ (univ : Set (Fin (m + 1))), err T j < ε / 2 :=
      (Filter.eventually_all_finite finite_univ).mpr fun j _ => hnode j
    exact hnodes.mono fun _ h j => h j (mem_univ j)
  filter_upwards [eventually_ge_atTop a, hgrid] with T haT hG r
  refine (zeroGateFullOccupation_error_le_grid H hmpos haT (fun j => (hG j).le) r).trans_lt ?_
  change ε / 2 + K / (m : ℝ) < ε
  linarith only [hstep]

/-- On a single almost-sure event, convergence over the full tolerance range
is uniform on every prefix of at least three sites, from any fixed start. -/
theorem gaussian_path_zeroGateFullOccupation_uniform :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ a ε : ℝ, 0 < ε →
      let u := pathPauliDisorderShell ω (k + 1)
      let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      ∀ᶠ T in atTop, ∀ r : Icc (0 : ℝ) 1,
        |volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a) - zeroGateFullArcMass (k + 3) r| < ε := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k a ε hε
  let u := pathPauliDisorderShell ω (k + 1)
  let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  exact maximallyProjective_zeroGateFullOccupation_uniform H (hω k) a hε

#print axioms zeroGateFullOccupation_error_le_grid
#print axioms maximallyProjective_zeroGateFullOccupation_uniform
#print axioms gaussian_path_zeroGateFullOccupation_uniform

end

end GaloisForLFunctions.HTGeometry
