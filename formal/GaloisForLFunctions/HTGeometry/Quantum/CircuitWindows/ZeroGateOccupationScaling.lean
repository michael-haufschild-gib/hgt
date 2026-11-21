import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateFullOccupation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dimension scaling of zero-gate occupation

Changing the reference phase preserves the whole relative Haar law.
Each possible anchor therefore supplies the same product probability, which
bounds full enclosure even when the anchor events overlap.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

section Relative

variable {ι : Type*}

private def changeUnitPhaseBase (ref i : ι) (x : {j : ι // j ≠ ref} → UnitAddCircle)
    (j : {j : ι // j ≠ i}) : UnitAddCircle :=
  relativeUnitPhasePacket ref x j - relativeUnitPhasePacket ref x i

private theorem relativeUnitPhasePacket_changeBase (ref i : ι) (x : {j : ι // j ≠ ref} → UnitAddCircle)
    (j : ι) : relativeUnitPhasePacket i (changeUnitPhaseBase ref i x) j =
      relativeUnitPhasePacket ref x j - relativeUnitPhasePacket ref x i := by
  rcases eq_or_ne j i with rfl | h
  · simp [relativeUnitPhasePacket]
  · simp only [relativeUnitPhasePacket, dif_pos h, changeUnitPhaseBase]

/-- Change the zero phase from `ref` to `i` by subtracting the phase at `i`. -/
def relativeUnitPhaseRebase (ref i : ι) :
    ({j : ι // j ≠ ref} → UnitAddCircle) ≃+ ({j : ι // j ≠ i} → UnitAddCircle) where
  toFun := changeUnitPhaseBase ref i
  invFun := changeUnitPhaseBase i ref
  left_inv x := by
    funext j
    change relativeUnitPhasePacket i (changeUnitPhaseBase ref i x) j -
      relativeUnitPhasePacket i (changeUnitPhaseBase ref i x) ref = x j
    rw [relativeUnitPhasePacket_changeBase, relativeUnitPhasePacket_changeBase, sub_sub_sub_cancel_right]
    simp [relativeUnitPhasePacket, j.2]
  right_inv x := by
    funext j
    change relativeUnitPhasePacket ref (changeUnitPhaseBase i ref x) j -
      relativeUnitPhasePacket ref (changeUnitPhaseBase i ref x) i = x j
    rw [relativeUnitPhasePacket_changeBase, relativeUnitPhasePacket_changeBase, sub_sub_sub_cancel_right]
    simp [relativeUnitPhasePacket, j.2]
  map_add' x y := by
    have hadd (j : ι) : relativeUnitPhasePacket ref (x + y) j =
        relativeUnitPhasePacket ref x j + relativeUnitPhasePacket ref y j := by
      by_cases h : j = ref <;> simp [relativeUnitPhasePacket, h]
    funext j
    change relativeUnitPhasePacket ref (x + y) j - relativeUnitPhasePacket ref (x + y) i =
      (relativeUnitPhasePacket ref x j - relativeUnitPhasePacket ref x i) +
        (relativeUnitPhasePacket ref y j - relativeUnitPhasePacket ref y i)
    rw [hadd j, hadd i]
    abel

theorem relativeUnitPhasePacket_rebase (ref i : ι) (x : {j : ι // j ≠ ref} → UnitAddCircle) (j : ι) :
    relativeUnitPhasePacket i (relativeUnitPhaseRebase ref i x) j =
      relativeUnitPhasePacket ref x j - relativeUnitPhasePacket ref x i :=
  relativeUnitPhasePacket_changeBase ref i x j

private theorem continuous_relativeUnitPhase_at (ref j : ι) :
    Continuous (fun x : {j : ι // j ≠ ref} → UnitAddCircle => relativeUnitPhasePacket ref x j) := by
  by_cases h : j ≠ ref
  · simpa only [relativeUnitPhasePacket, dif_pos h] using
      (continuous_apply (⟨j, h⟩ : {j : ι // j ≠ ref}))
  · simp only [relativeUnitPhasePacket, dif_neg h]
    exact continuous_const

variable [Fintype ι] [DecidableEq ι]

/-- Rebasing preserves the joint law, including independence of all new
coordinates. -/
theorem measurePreserving_relativeUnitPhaseRebase (ref i : ι) :
    MeasurePreserving (relativeUnitPhaseRebase ref i) volume volume := by
  let e := relativeUnitPhaseRebase ref i
  letI : Measure.IsAddHaarMeasure (volume : Measure ({j : ι // j ≠ ref} → UnitAddCircle)) := {}
  letI : Measure.IsAddHaarMeasure (volume : Measure ({j : ι // j ≠ i} → UnitAddCircle)) := {}
  refine e.toAddMonoidHom.measurePreserving (continuous_pi fun j => ?_) e.surjective ?_
  · exact (continuous_relativeUnitPhase_at ref j).sub (continuous_relativeUnitPhase_at ref i)
  · simp only [measure_univ]

/-- The enclosure profile is independent of the reference phase, for any radius. -/
theorem relativeUnitArcMass_eq_of_reference (ref i : ι) (r : ℝ) :
    relativeUnitArcMass ref r = relativeUnitArcMass i r := by
  have hpre : relativeUnitPhaseRebase ref i ⁻¹' relativeEnclosingUnitArc i r =
      relativeEnclosingUnitArc ref r := by
    ext x
    simp only [relativeEnclosingUnitArc, mem_preimage, enclosingUnitArc, mem_iUnion, anchoredUnitArc,
      mem_setOf_eq, relativeUnitPhasePacket_rebase, sub_sub_sub_cancel_right]
  rw [relativeUnitArcMass, relativeUnitArcMass, ← hpre]
  exact (measurePreserving_relativeUnitPhaseRebase ref i).measureReal_preimage
    (isClosed_relativeEnclosingUnitArc i r).measurableSet.nullMeasurableSet

/-- At any allowed length, each fixed anchor has the same product probability. -/
theorem volume_relativeAnchoredUnitArc_full (ref i : ι) (r : Icc (0 : ℝ) 1) :
    volume (relativeUnitPhasePacket ref ⁻¹' anchoredUnitArc i r) =
      ENNReal.ofReal (r : ℝ) ^ (Fintype.card ι - 1) := by
  let B : Set ({j : ι // j ≠ i} → UnitAddCircle) := univ.pi (fun _ => forwardUnitArc r)
  have hB : MeasurableSet B := MeasurableSet.univ_pi (fun _ => (isClosed_forwardUnitArc r).measurableSet)
  have hpre : relativeUnitPhasePacket ref ⁻¹' anchoredUnitArc i r = relativeUnitPhaseRebase ref i ⁻¹' B := by
    ext x
    simp only [B, mem_preimage, anchoredUnitArc, mem_setOf_eq, Set.mem_pi, mem_univ, true_implies, Subtype.forall]
    rfl
  have hcard : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl (fun j => j = i), Fintype.card_subtype_eq]
  rw [hpre, (measurePreserving_relativeUnitPhaseRebase ref i).measure_preimage hB.nullMeasurableSet]
  change volume (univ.pi _) = _
  rw [volume_pi_pi]
  simp only [volume_forwardUnitArc_full r, Finset.prod_const, Finset.card_univ, hcard]

/-- A single anchor gives a lower bound and summing all anchors gives an
upper bound, across the full range of enclosing arcs. -/
theorem relativeUnitArcMass_bounds (ref : ι) (r : Icc (0 : ℝ) 1) :
    (r : ℝ) ^ (Fintype.card ι - 1) ≤ relativeUnitArcMass ref r ∧
      relativeUnitArcMass ref r ≤ (Fintype.card ι : ℝ) * (r : ℝ) ^ (Fintype.card ι - 1) := by
  let A (i : ι) := relativeUnitPhasePacket ref ⁻¹' anchoredUnitArc i (r : ℝ)
  have hA (i : ι) : volume.real (A i) = (r : ℝ) ^ (Fintype.card ι - 1) := by
    rw [Measure.real, volume_relativeAnchoredUnitArc_full ref i r, ENNReal.toReal_pow, ENNReal.toReal_ofReal r.2.1]
  have hset : relativeEnclosingUnitArc ref r = ⋃ i, A i := by
    simp only [relativeEnclosingUnitArc, enclosingUnitArc, preimage_iUnion, A]
  change _ ≤ volume.real _ ∧ volume.real _ ≤ _
  rw [hset]
  constructor
  · rw [← hA ref]
    exact measureReal_mono (subset_iUnion A ref) (measure_ne_top _ _)
  · refine (measureReal_iUnion_fintype_le A).trans_eq ?_
    simp only [hA, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Relative

/-- At all tolerances the return fraction lies between a single anchor's
probability and that probability multiplied by the register dimension. -/
theorem zeroGateFullArcMass_bounds (n : ℕ) (r : Icc (0 : ℝ) 1) :
    (r : ℝ) ^ (2 ^ n - 1) ≤ zeroGateFullArcMass n r ∧
      zeroGateFullArcMass n r ≤ (2 : ℝ) ^ n * (r : ℝ) ^ (2 ^ n - 1) := by
  simpa only [zeroGateFullArcMass, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] using
    relativeUnitArcMass_bounds (fun _ : Fin n => false) r

/-- The complementary arc length controls the bound even for tolerances
that depend on the register dimension. -/
theorem zeroGateFullArcMass_le_exp_complement (n : ℕ) (r : Icc (0 : ℝ) 1) :
    zeroGateFullArcMass n r ≤ (2 : ℝ) ^ n * Real.exp (((2 ^ n - 1 : ℕ) : ℝ) * ((r : ℝ) - 1)) := by
  have h : (r : ℝ) ≤ Real.exp ((r : ℝ) - 1) := by
    simpa only [sub_add_cancel] using Real.add_one_le_exp ((r : ℝ) - 1)
  rw [Real.exp_nat_mul]
  exact (zeroGateFullArcMass_bounds n r).2.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ r.2.1 h _) (pow_nonneg (by norm_num) _))

private theorem zeroGateFullArcMass_pos (n : ℕ) (r : Ioc (0 : ℝ) 1) : 0 < zeroGateFullArcMass n r :=
  (pow_pos r.2.1 _).trans_le (zeroGateFullArcMass_bounds n ⟨r, r.2.1.le, r.2.2⟩).1

/-- The finite-dimensional error in the log occupation is between zero and
the logarithm of the number of possible anchors. -/
theorem zeroGateFullArcMass_log_bounds (n : ℕ) (r : Ioc (0 : ℝ) 1) :
    ((2 : ℝ) ^ n - 1) * Real.log r ≤ Real.log (zeroGateFullArcMass n r) ∧
      Real.log (zeroGateFullArcMass n r) ≤ ((2 : ℝ) ^ n - 1) * Real.log r + Real.log ((2 : ℝ) ^ n) := by
  obtain ⟨hl, hu⟩ := zeroGateFullArcMass_bounds n ⟨r, r.2.1.le, r.2.2⟩
  have hr := pow_pos r.2.1 (2 ^ n - 1)
  have hl' := Real.log_le_log hr hl
  have hu' := Real.log_le_log (hr.trans_le hl) hu
  have hD : 1 ≤ (2 : ℕ) ^ n := one_le_pow₀ (by norm_num)
  rw [Real.log_pow, Nat.cast_sub hD, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hl'
  rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) n).ne' hr.ne',
    Real.log_pow (r : ℝ) (2 ^ n - 1), Nat.cast_sub hD, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hu'
  exact ⟨hl', by simpa only [add_comm] using hu'⟩

/-- For fixed positive tolerance, log occupation divided by Hilbert-space
dimension tends to the logarithm of the allowed arc length. -/
theorem tendsto_zeroGateFullArcMass_log_div_dimension (r : Ioc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => Real.log (zeroGateFullArcMass n r) / (2 : ℝ) ^ n) atTop (𝓝 (Real.log r)) := by
  have hd : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hrecip : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := hd.inv_tendsto_atTop
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlow : Tendsto (fun n : ℕ => (1 - ((2 : ℝ) ^ n)⁻¹) * Real.log r) atTop (𝓝 (Real.log r)) := by
    simpa only [sub_zero, one_mul] using (hrecip.const_sub 1).mul_const (Real.log r)
  have hhigh : Tendsto (fun n : ℕ => (1 - ((2 : ℝ) ^ n)⁻¹) * Real.log r +
      Real.log ((2 : ℝ) ^ n) / (2 : ℝ) ^ n) atTop (𝓝 (Real.log r)) := by
    simpa only [add_zero, Function.comp_apply] using hlow.add (hlog.comp hd)
  have hD (n : ℕ) : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hnorm (n : ℕ) : (((2 : ℝ) ^ n - 1) * Real.log r) / (2 : ℝ) ^ n =
      (1 - ((2 : ℝ) ^ n)⁻¹) * Real.log r := by
    rw [mul_div_right_comm, sub_div, div_self (hD n).ne', one_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · exact Eventually.of_forall fun n => by
      rw [← hnorm n]
      exact div_le_div_of_nonneg_right (zeroGateFullArcMass_log_bounds n r).1 (hD n).le
  · exact Eventually.of_forall fun n => by
      rw [← hnorm n, ← add_div]
      exact div_le_div_of_nonneg_right (zeroGateFullArcMass_log_bounds n r).2 (hD n).le

/-- Every exponential rate below the limiting decay rate bounds the eventual
occupation from above, on the scale of the register dimension. -/
theorem eventually_zeroGateFullArcMass_le_exp_dimension (r : Ioc (0 : ℝ) 1) {c : ℝ}
    (hc : c < -Real.log r) :
    ∀ᶠ n : ℕ in atTop, zeroGateFullArcMass n r ≤ Real.exp (-c * (2 : ℝ) ^ n) := by
  have hlt : Real.log r < -c := by linarith only [hc]
  filter_upwards [(tendsto_order.mp (tendsto_zeroGateFullArcMass_log_div_dimension r)).2 (-c) hlt] with n hn
  have hd : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have he := Real.exp_le_exp_of_le ((div_lt_iff₀ hd).mp hn).le
  simpa only [Real.exp_log (zeroGateFullArcMass_pos n r)] using he

/-- Occupation vanishes if the scaled complementary length exceeds the log
dimension by a diverging margin, even when the tolerance tends to one. -/
theorem tendsto_zeroGateFullArcMass_zero_of_complement (r : ℕ → Icc (0 : ℝ) 1)
    (hr : Tendsto (fun n : ℕ => ((2 ^ n - 1 : ℕ) : ℝ) * (1 - (r n : ℝ)) - Real.log ((2 : ℝ) ^ n))
      atTop atTop) : Tendsto (fun n : ℕ => zeroGateFullArcMass n (r n)) atTop (𝓝 0) := by
  let b (n : ℕ) := ((2 ^ n - 1 : ℕ) : ℝ) * (1 - (r n : ℝ)) - Real.log ((2 : ℝ) ^ n)
  have hneg : Tendsto (fun n : ℕ => -b n) atTop atBot := tendsto_neg_atTop_atBot.comp hr
  have hexp : Tendsto (fun n : ℕ => Real.exp (-b n)) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hneg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · exact Eventually.of_forall fun n =>
      (pow_nonneg (r n).2.1 _).trans (zeroGateFullArcMass_bounds n (r n)).1
  · exact Eventually.of_forall fun n => by
      have he : -b n = Real.log ((2 : ℝ) ^ n) + ((2 ^ n - 1 : ℕ) : ℝ) * ((r n : ℝ) - 1) := by
        dsimp only [b]
        ring
      rw [he, Real.exp_add, Real.exp_log (pow_pos (by norm_num) _)]
      exact zeroGateFullArcMass_le_exp_complement n (r n)

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- On one Gaussian draw the log return fraction, divided by dimension,
has the stated rate in the long-time limit followed by the prefix limit. -/
theorem gaussian_path_zeroGateOccupation_log_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ r : Ioc (0 : ℝ) 1, ∀ a : ℝ,
      (∀ k : ℕ,
        let u := pathPauliDisorderShell ω (k + 1)
        let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        Tendsto (fun T => Real.log (volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a)) /
          (2 : ℝ) ^ (k + 3)) atTop (𝓝 (Real.log (zeroGateFullArcMass (k + 3) r) / (2 : ℝ) ^ (k + 3)))) ∧
      Tendsto (fun k : ℕ => Real.log (zeroGateFullArcMass (k + 3) r) / (2 : ℝ) ^ (k + 3)) atTop (𝓝 (Real.log r)) := by
  filter_upwards [gaussian_path_zeroGateFullOccupation_from_start] with ω hω
  intro r a
  constructor
  · intro k
    exact ((Real.continuousAt_log (zeroGateFullArcMass_pos (k + 3) r).ne').tendsto.comp
      (hω k ⟨r, r.2.1.le, r.2.2⟩ a)).div_const _
  · have hshift : Tendsto (fun k : ℕ => k + 3) atTop atTop :=
      tendsto_atTop.mpr fun b => (eventually_ge_atTop b).mono fun k hk => by omega
    exact (tendsto_zeroGateFullArcMass_log_div_dimension r).comp hshift

#print axioms measurePreserving_relativeUnitPhaseRebase
#print axioms relativeUnitArcMass_eq_of_reference
#print axioms volume_relativeAnchoredUnitArc_full
#print axioms relativeUnitArcMass_bounds
#print axioms zeroGateFullArcMass_bounds
#print axioms zeroGateFullArcMass_le_exp_complement
#print axioms zeroGateFullArcMass_log_bounds
#print axioms tendsto_zeroGateFullArcMass_log_div_dimension
#print axioms eventually_zeroGateFullArcMass_le_exp_dimension
#print axioms tendsto_zeroGateFullArcMass_zero_of_complement
#print axioms gaussian_path_zeroGateOccupation_log_rate

end

end GaloisForLFunctions.HTGeometry
