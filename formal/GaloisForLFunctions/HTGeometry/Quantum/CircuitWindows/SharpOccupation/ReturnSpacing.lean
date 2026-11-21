import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitWindows

/-! # Exact exponential rate of mean spacing between resolved cheap returns -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- The next recorded visit is the first affordable time at least one
physical time unit after the preceding observation. -/
def records {n : ℕ} (H : selfAdjoint (Register n)) (s : ℕ) (ε a : ℝ) (t : ℕ → ℝ) : Prop :=
  t 0 = a ∧ ∀ j, IsLeast {v | t j+1 ≤ v ∧ v ∈ visitSet H s ε} (t (j+1))

theorem exists_records {n : ℕ} (H : selfAdjoint (Register n)) (s : ℕ) (x : Ioo (0:ℝ) (1/2)) (a : ℝ) :
    ∃ t, records H s (zeroGateArcTolerance x) a t := by
  classical
  let ε := zeroGateArcTolerance x
  let A := visitSet H s ε
  have hclosed : IsClosed A := by
    have heq : A = {u | orbitCircuitDistance H s u ≤ ε} := by
      ext u; exact hasProjectiveCircuitApproximation_iff_infDist _ _ _
    rw [heq]
    exact isClosed_le (orbitCircuitDistance_lipschitz H s).continuous continuous_const
  have least (b : ℝ) : ∃ w, IsLeast {u | b+1 ≤ u ∧ u ∈ A} w := by
    obtain ⟨v,hv0,hv⟩ := exists_zeroGateReturnSequence H ⟨x,x.2.1,x.2.2.le⟩ b 1
    have hb := (hv 0).1
    rw [hv0] at hb
    obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 ε).mpr hb.2
    have hfit : v 1 ∈ A := ⟨z,hz,C,hC.trans (Nat.zero_le _),he⟩
    let B := Icc (b+1) (v 1) ∩ A
    obtain ⟨hm,hl⟩ := (isCompact_Icc.inter_right hclosed : IsCompact B).isLeast_sInf
      (show B.Nonempty from ⟨v 1,⟨hb.1,le_rfl⟩,hfit⟩)
    refine ⟨sInf B,⟨hm.1.1,hm.2⟩,?_⟩
    rintro u ⟨hu,hA⟩
    exact (le_total u (v 1)).elim (fun h => hl ⟨⟨hu,h⟩,hA⟩) (fun h => hm.1.2.trans h)
  choose f hf using least
  let t (j : ℕ) : ℝ := Nat.rec a (fun _ v => f v) j
  exact ⟨t,rfl,fun j => hf (t j)⟩

private theorem records_tendsto {n s : ℕ} {H : selfAdjoint (Register n)} {ε a : ℝ} {t : ℕ → ℝ}
    (ht : records H s ε a t) : Tendsto t atTop atTop := by
  have h (j : ℕ) : a+(j:ℝ) ≤ t j := by
    induction j with
    | zero => simp [ht.1]
    | succ j ih =>
      rw [Nat.cast_succ]
      linarith only [ih,(ht.2 j).1.1]
  exact tendsto_atTop_mono h (tendsto_atTop_add_const_left atTop a tendsto_natCast_atTop_atTop)

/-- The unit-resolved mean waiting time has exponential rate the reciprocal
of the cheap-time occupation. This holds for all origins on the same draw,
including an origin selected as a first robust crossing. -/
theorem gaussian_resolved_return_spacing_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (s : ℕ → ℕ), subcriticalBudget s →
      ∀ x ∈ Ioo (0:ℝ) (1/2), ∀ l b : ℝ, 0 < l → l < x → x < b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        ∀ j ≤ s N, ∀ a : ℝ, ∃ t, records H j (zeroGateArcTolerance x) a t ∧
          ∀ᶠ i : ℕ in atTop, 1/b^D < (t i-a)/i ∧ (t i-a)/i < 1/l^D := by
  filter_upwards [gaussian_cheap_occupation_rate,gaussian_unit_hit_enlargement] with ω hw hunit
  intro s hs x hx l b hl hlx hxb
  obtain ⟨y,hxy,hy⟩ := exists_between (lt_min hxb hx.2)
  have hyhalf := hy.trans_le (min_le_right ..)
  have hδ := sub_pos.mpr (strictMonoOn_zeroGateArcTolerance ⟨hx.1.le,hx.2.le⟩
    ⟨(hx.1.trans hxy).le,hyhalf.le⟩ hxy)
  have hsmall := hw s hs x hx l b hl.le hlx hxb
  have hwide := hw (fun n => s n+n^4) (subcritical_add_pow_four hs) y ⟨hx.1.trans hxy,hyhalf⟩
    0 b le_rfl (hx.1.trans hxy) (hy.trans_le (min_le_left ..))
  filter_upwards [hsmall,hwide,hunit _ hδ] with k hA hB hwin
  intro N D H j hj a
  obtain ⟨t,ht⟩ := exists_records H j ⟨x,hx⟩ a
  refine ⟨t,ht,?_⟩
  have hwindows := hwin j (zeroGateArcTolerance x)
  rw [show zeroGateArcTolerance x+(zeroGateArcTolerance y-zeroGateArcTolerance x)=
    zeroGateArcTolerance y by ring] at hwindows
  have htime := records_tendsto ht
  filter_upwards [htime.eventually (hA a),htime.eventually (hB a),
    htime.eventually (eventually_gt_atTop a),eventually_gt_atTop 0] with i hLo hHi hat hi
  have hi' : 0 < (i:ℝ) := by exact_mod_cast hi
  have hbp : 0 < b^D := pow_pos (hx.1.trans hxb) _
  have hlp : 0 < l^D := pow_pos hl _
  have hdur := sub_pos.mpr hat
  obtain ⟨cover,pack⟩ := resolved_visit_occupation_bounds _ t a 1 1 zero_lt_one le_rfl ht.1 ht.2 i
  rw [mul_one] at cover pack
  have hpack := pack.trans (measureReal_mono (inter_subset_inter_left _ hwindows)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne))
  have hupper := (div_lt_iff₀ hdur).mp (hHi (j+N^4) (Nat.add_le_add_right hj _)).2
  have hlower := (lt_div_iff₀ hdur).mp (hLo j hj).1
  constructor
  · rw [div_lt_div_iff₀ hbp hi',one_mul]
    rw [mul_comm (t i-a)]
    exact hpack.trans_lt hupper
  · rw [div_lt_div_iff₀ hi' hlp,one_mul]
    rw [mul_comm (t i-a)]
    exact hlower.trans_le cover

#print axioms gaussian_resolved_return_spacing_rate
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
