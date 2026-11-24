import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Selections

/-! # Finite inversion of divisibility readings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exclude a list of divisors by subtracting the readings of their intersections. -/
def sieveReading (R : ℕ+ → ℝ) : List ℕ+ → ℕ+ → ℝ
  | [], d => R d
  | b :: L, d => sieveReading R L d -
      sieveReading R L ⟨Nat.lcm d.val b.val, Nat.lcm_pos d.pos b.pos⟩

/-- Exponents counted after removing every divisor in the exclusion list. -/
def sieveSurvives (L : List ℕ+) (d : ℕ+) (e : ℕ) :=
  d.val ∣ e ∧ ∀ b ∈ L, ¬ b.val ∣ e

theorem sieveReading_eq_selected {w : ℕ → ℝ} (hs : Summable w) (L : List ℕ+) (d : ℕ+) :
    sieveReading (fun b => selectedMass w (fun e => b.val ∣ e)) L d =
      selectedMass w (sieveSurvives L d) := by
  induction L generalizing d with
  | nil => exact selectedMass_congr _ (fun _ => by simp [sieveSurvives])
  | cons b L ih =>
    rw [sieveReading, ih, ih, selectedMass, selectedMass, selectedMass,
      ← (selected_summable hs _).tsum_sub (selected_summable hs _)]
    apply tsum_congr
    intro e
    have hl : Nat.lcm d.val b.val ∣ e ↔ d.val ∣ e ∧ b.val ∣ e :=
      ⟨fun h => ⟨dvd_trans (Nat.dvd_lcm_left _ _) h, dvd_trans (Nat.dvd_lcm_right _ _) h⟩,
       fun h => Nat.lcm_dvd h.1 h.2⟩
    by_cases hd : d.val ∣ e <;> by_cases hb : b.val ∣ e <;>
      by_cases hL : ∀ c ∈ L, ¬ c.val ∣ e <;> simp [sieveSurvives,hl,hd,hb,hL]

/-- Multiples of h from 2h through (N+1)h. -/
def multipleExclusions (h : ℕ+) (N : ℕ) : List ℕ+ :=
  (List.range N).map fun i => ⟨h.val*(i+2),Nat.mul_pos h.pos (by omega)⟩

private theorem survives_self (h : ℕ+) (N : ℕ) : sieveSurvives (multipleExclusions h N) h h.val := by
  refine ⟨dvd_refl _,?_⟩
  intro b hb hd
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
  have hlt : h.val*1 < h.val*(i+2) := Nat.mul_lt_mul_of_pos_left (by omega) h.pos
  exact (not_lt_of_ge (Nat.le_of_dvd h.pos hd)) (by simpa using hlt)

private theorem survives_eventually (h : ℕ+) (e : ℕ) :
    ∀ᶠ N in atTop, sieveSurvives (multipleExclusions h N) h e ↔ e = h.val := by
  by_cases he : e = h.val
  · subst e
    exact Eventually.of_forall fun N => iff_of_true (survives_self h N) rfl
  by_cases hd : h.val ∣ e
  · obtain ⟨k,rfl⟩ := hd
    have exclude (i N : ℕ) (hi : i < N) (hdv : h.val*(i+2) ∣ h.val*k) :
        ¬ sieveSurvives (multipleExclusions h N) h (h.val*k) := by
      intro hs
      exact hs.2 ⟨h.val*(i+2),Nat.mul_pos h.pos (by omega)⟩
        (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩) hdv
    rcases k with _ | (_ | k)
    · filter_upwards [eventually_gt_atTop 0] with N hN
      exact iff_of_false (exclude 0 N hN (by simp)) he
    · simp at he
    · filter_upwards [eventually_gt_atTop k] with N hN
      exact iff_of_false (exclude k N hN (dvd_refl _)) he
  · exact Eventually.of_forall fun _ => iff_of_false (fun h => hd h.1) he

/-- Finite inclusion-exclusion converges for every summable nonnegative exponent law. -/
theorem sieveReading_limit {w : ℕ → ℝ} (hw : ∀ e, 0 ≤ w e) (hs : Summable w) (h : ℕ+) :
    Tendsto (fun N => sieveReading (fun b => selectedMass w (fun e => b.val ∣ e))
      (multipleExclusions h N) h) atTop (𝓝 (w h.val)) := by
  simp_rw [sieveReading_eq_selected hs]
  exact selectedMass_limit_singleton hw hs _ _ (survives_eventually h)

theorem sieveReading_antitone {w : ℕ → ℝ} (hw : ∀ e, 0 ≤ w e) (hs : Summable w) (h : ℕ+) :
    Antitone (fun N => sieveReading (fun b => selectedMass w (fun e => b.val ∣ e))
      (multipleExclusions h N) h) := by
  intro M N hMN
  change sieveReading _ (multipleExclusions h N) h ≤ sieveReading _ (multipleExclusions h M) h
  rw [sieveReading_eq_selected hs (multipleExclusions h N) h,
    sieveReading_eq_selected hs (multipleExclusions h M) h]
  unfold selectedMass
  apply (selected_summable hs _).tsum_le_tsum _ (selected_summable hs _)
  intro e
  by_cases hn : sieveSurvives (multipleExclusions h N) h e
  · have hm : sieveSurvives (multipleExclusions h M) h e := by
      refine ⟨hn.1,fun b hb => hn.2 b ?_⟩
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
      exact List.mem_map.mpr ⟨i,List.mem_range.mpr ((List.mem_range.mp hi).trans_le hMN),rfl⟩
    simp [hn,hm]
  · by_cases hm : sieveSurvives (multipleExclusions h M) h e <;> simp [hn,hm,hw]

#print axioms sieveReading_eq_selected
#print axioms sieveReading_limit
#print axioms sieveReading_antitone

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
