import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.GaussianRate

/-! # Excluding all early affordable multiples of a sampled period -/
open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstClockIndex
noncomputable section
open SharpOccupation

/-- One of the first M positive multiples admits an affordable circuit. -/
def earlyVisit {n : ℕ} (H : selfAdjoint (Register n)) (s M : ℕ) (ε : ℝ) : Set ℝ :=
  {t | ∃ q : ℕ, 0 < q ∧ q ≤ M ∧ (q:ℝ)*t ∈ visitSet H s ε}

private theorem dilated_fraction (A : Set ℝ) {q : ℝ} (hq : 0 < q) (a T : ℝ) :
    volume.real ((fun u => q*u) ⁻¹' A ∩ Icc a T)/(T-a) =
      volume.real (A ∩ Icc (q*a) (q*T))/(q*T-q*a) := by
  have he : (fun u => q*u) ⁻¹' A ∩ Icc a T = (fun u => q*u) ⁻¹' (A ∩ Icc (q*a) (q*T)) := by
    ext u
    exact and_congr_right' (and_congr (mul_le_mul_iff_right₀ hq).symm (mul_le_mul_iff_right₀ hq).symm)
  rw [he,Measure.real,Real.volume_preimage_mul_left hq.ne',ENNReal.toReal_mul,abs_of_pos (inv_pos.mpr hq),
    ENNReal.toReal_ofReal (inv_pos.mpr hq).le,←mul_sub,Measure.real]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A single-date upper fraction p bounds the union of all M initial
tests by Mp, with the same physical error at every harmonic. -/
theorem early_fraction {n : ℕ} (H : selfAdjoint (Register n)) (s M : ℕ) (ε p : ℝ)
    (h : ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, volume.real (visitSet H s ε ∩ Icc a T)/(T-a) < p)
    (a : ℝ) : ∀ᶠ T : ℝ in atTop, volume.real (earlyVisit H s M ε ∩ Icc a T)/(T-a) ≤ M*p := by
  let A := visitSet H s ε
  let q (i : Fin M) : ℝ := (i.val:ℝ)+1
  have qpos (i : Fin M) : 0 < q i := by dsimp [q]; positivity
  have hi (i : Fin M) := (tendsto_id.const_mul_atTop (qpos i)).eventually (h (q i*a))
  filter_upwards [Filter.eventually_all.mpr hi,eventually_gt_atTop a] with T ht hT
  let B (i : Fin M) := (fun u => q i*u) ⁻¹' A ∩ Icc a T
  have he : earlyVisit H s M ε ∩ Icc a T = ⋃ i, B i := by
    ext t
    constructor
    · rintro ⟨⟨r,hr,hrM,hvisit⟩,hI⟩
      let i : Fin M := ⟨r-1,by omega⟩
      have hq : q i = (r:ℝ) := by
        change ((r-1:ℕ):ℝ)+1 = r
        exact_mod_cast (Nat.sub_add_cancel hr)
      exact mem_iUnion.mpr ⟨i,show q i*t ∈ A from hq.symm ▸ hvisit,hI⟩
    · intro hB
      obtain ⟨i,hh,hI⟩ := mem_iUnion.mp hB
      exact ⟨⟨i.val+1,Nat.succ_pos _,i.isLt,by rw [Nat.cast_succ]; exact hh⟩,hI⟩
  rw [he]
  apply (div_le_div_of_nonneg_right (measureReal_iUnion_fintype_le B) (sub_nonneg.mpr hT.le)).trans
  rw [Finset.sum_div]
  have hsingle (i : Fin M) : volume.real (B i)/(T-a) ≤ p :=
    (dilated_fraction A (qpos i) a T).le.trans (ht i).le
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hsingle i)

/-- If x<b<1, the fraction of periods having any affordable positive
multiple through b⁻ᴰ decays exponentially in D. -/
theorem gaussian_no_early_clock_index :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ x ∈ Ioo (0:ℝ) (1/2), ∀ y b : ℝ, x < y → y < b → b < 1 → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
          volume.real (earlyVisit H (s N) ⌊(1/b)^D⌋₊ (zeroGateArcTolerance x) ∩ Icc a T)/(T-a) ≤ (y/b)^D := by
  filter_upwards [gaussian_cheap_occupation_rate] with ω hω
  intro s hs x hx y b hxy hyb _
  filter_upwards [hω s hs x hx 0 y le_rfl hx.1 hxy] with k hk
  intro N D H a
  have hv (u : ℝ) := (hk u).mono fun T hw => (hw (s N) le_rfl).2
  filter_upwards [early_fraction H (s N) ⌊(1/b)^D⌋₊ _ (y^D) hv a] with T hT
  apply hT.trans
  have hbp := (hx.1.trans hxy).trans hyb
  calc
    _ ≤ (1/b)^D*y^D := mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (pow_nonneg (hx.1.trans hxy).le D)
    _ = _ := by rw [←mul_pow]; congr 1; ring

#print axioms gaussian_no_early_clock_index
end
end GaloisForLFunctions.HTGeometry.FirstClockIndex
