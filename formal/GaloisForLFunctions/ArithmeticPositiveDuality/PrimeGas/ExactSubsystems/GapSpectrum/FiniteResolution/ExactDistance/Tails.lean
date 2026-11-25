import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.ExactDistance.Cells
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.RowProbability

/-! # The discrete Gibbs tail between a trapezoid and a centered-cell bound -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GibbsTail

open Set Filter Topology

/-- Unnormalized weight of all integer labels strictly greater than k. -/
def tail (h : Ioi (0:ℝ)) (k : ℕ) : ℝ :=
  ∑' m : ℕ+, if k < m.val then thermalWeight (labelTemperature h) m else 0

theorem density_label (h : Ioi (0:ℝ)) (n : ℕ+) :
    density h (n.val:ℝ) = thermalWeight (labelTemperature h) n := by
  rw [density,Real.rpow_def_of_pos (Nat.cast_pos.mpr n.pos)]
  exact congrArg Real.exp (mul_comm _ _)

private theorem restricted_summable (h : Ioi (0:ℝ)) (P : ℕ+ → Prop) [DecidablePred P] :
    Summable (fun m : ℕ+ => if P m then thermalWeight (labelTemperature h) m else 0) := by
  apply Summable.of_nonneg_of_le _ _ (thermalWeight_summable (labelTemperature h))
  · intro m
    split
    · exact (thermalWeight_pos _ _).le
    · exact le_rfl
  · intro m
    split
    · exact le_rfl
    · exact (thermalWeight_pos _ _).le

theorem tail_step (h : Ioi (0:ℝ)) (k : ℕ) :
    tail h k = density h ((k:ℝ)+1)+tail h (k+1) := by
  let m₀ : ℕ+ := ⟨k+1,Nat.zero_lt_succ _⟩
  let u := fun m : ℕ+ => if m = m₀ then thermalWeight (labelTemperature h) m else 0
  have hu : Summable u := restricted_summable h (fun m => m = m₀)
  have hv : ∑' m, u m = density h ((k:ℝ)+1) := by
    rw [tsum_eq_single m₀ (fun m hm => if_neg hm)]
    change (if m₀ = m₀ then _ else (0:ℝ)) = _
    rw [if_pos rfl,← density_label h m₀]
    change density h ((k+1:ℕ):ℝ) = _
    rw [Nat.cast_add_one]
  rw [← hv,tail,tail,← hu.tsum_add (restricted_summable h (fun m => k+1 < m.val))]
  apply tsum_congr
  intro m
  by_cases he : m = m₀
  · subst m
    simp [u,m₀]
  · have hn : m.val ≠ k+1 := fun hm => he (PNat.coe_injective hm)
    have hi : k < m.val ↔ k+1 < m.val := by omega
    simp only [u,if_neg he,zero_add,hi]

theorem tail_tendsto_zero (h : Ioi (0:ℝ)) : Tendsto (tail h) atTop (𝓝 0) := by
  have ht := tendsto_tsum_of_dominated_convergence (g := fun _ : ℕ+ => (0:ℝ))
    (f := fun k (m : ℕ+) => if k < m.val then thermalWeight (labelTemperature h) m else 0)
    (𝓕 := atTop) (thermalWeight_summable (labelTemperature h))
    (fun m => tendsto_const_nhds.congr' ((eventually_ge_atTop m.val).mono fun k hk => (if_neg (not_lt.mpr hk)).symm))
    (Eventually.of_forall fun k m => by
      by_cases hm : k < m.val
      · rw [if_pos hm,Real.norm_eq_abs,abs_of_pos (thermalWeight_pos _ _)]
      · simpa only [if_neg hm,norm_zero] using (thermalWeight_pos (labelTemperature h) m).le)
  rw [tsum_zero] at ht
  exact ht.congr (fun _ => rfl)

private theorem shift_atTop (z : ℝ) : Tendsto (fun k : ℕ => (k:ℝ)+z) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := z))

private theorem primitive_shift_limit (h : Ioi (0:ℝ)) (z : ℝ) :
    Tendsto (fun k : ℕ => primitive h ((k:ℝ)+z)) atTop (𝓝 0) := by
  have he := ((tendsto_rpow_neg_atTop (show 0 < h.val from h.property)).comp (shift_atTop z)).div_const h.val
  rw [zero_div] at he
  exact he

private theorem density_shift_limit (h : Ioi (0:ℝ)) (z : ℝ) :
    Tendsto (fun k : ℕ => density h ((k:ℝ)+z)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by linarith only [show 0 < h.val from h.property] : 0 < 1+h.val)).comp (shift_atTop z)

/-- Successive cell errors have one sign and vanish at infinity. Strict convexity survives summation. -/
theorem integer_tail_bounds (h : Ioi (0:ℝ)) (n : ℕ+) :
    primitive h (n.val:ℝ)-density h (n.val:ℝ)/2 < tail h n.val ∧
    tail h n.val ≤ primitive h ((n.val:ℝ)+1/2) := by
  let A := fun k : ℕ => primitive h ((k:ℝ)+1)-density h ((k:ℝ)+1)/2-tail h (k+1)
  let B := fun k : ℕ => tail h (k+1)-primitive h ((k:ℝ)+1+1/2)
  have ht := (tail_tendsto_zero h).comp (tendsto_add_atTop_nat 1)
  have hA : Tendsto A atTop (𝓝 0) := by
    have he := ((primitive_shift_limit h 1).sub ((density_shift_limit h 1).div_const 2)).sub ht
    rw [zero_div,sub_zero,sub_zero] at he
    exact he.congr (fun _ => rfl)
  have hB : Tendsto B atTop (𝓝 0) := by
    have he := ht.sub (primitive_shift_limit h (1+1/2))
    rw [sub_zero] at he
    apply he.congr
    intro k
    dsimp [B,Function.comp]
    rw [add_assoc (k:ℝ) 1]
  have hs (k : ℕ) : A k < A (k+1) ∧ B k ≤ B (k+1) := by
    have hp : 0 < (k:ℝ)+1 := by positivity
    have hl := strict_trapezoid h hp
    have hu := midpoint_cell h (show 0 < (k:ℝ)+1+1/2 by linarith only [hp])
    rw [show (k:ℝ)+1+1/2+1/2 = (k:ℝ)+1+1 by ring,
      show (k:ℝ)+1+1/2+1 = (k:ℝ)+1+1+1/2 by ring] at hu
    have he := tail_step h (k+1)
    rw [Nat.cast_add_one] at he
    dsimp only [A,B]
    rw [Nat.cast_add_one]
    exact ⟨by linarith only [hl,he],by linarith only [hu,he]⟩
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero n.pos.ne'
  have ha := (hs k).1.trans_le ((monotone_nat_of_le_succ fun j => (hs j).1.le).ge_of_tendsto hA (k+1))
  have hb := (monotone_nat_of_le_succ fun j => (hs j).2).ge_of_tendsto hB k
  rw [hk,Nat.cast_add_one]
  exact ⟨sub_lt_zero.mp ha,sub_nonpos.mp hb⟩

/-- For a real cutoff, the fractional endpoint can cost at most half the first row weight. -/
theorem real_tail_bound (h : Ioi (0:ℝ)) (n : ℕ+) {y : ℝ} (hy : (n.val:ℝ) ≤ y) :
    tail h ⌊y⌋₊ ≤ primitive h y+density h (n.val:ℝ)/2 := by
  have hn : 0 < (n.val:ℝ) := Nat.cast_pos.mpr n.pos
  have hd : n.val ≤ ⌊y⌋₊ := Nat.le_floor hy
  let k : ℕ+ := ⟨⌊y⌋₊,n.pos.trans_le hd⟩
  have hnk : (n.val:ℝ) ≤ k.val := by exact_mod_cast hd
  have he := (integer_tail_bounds h k).2
  have hp : 0 < density h (n.val:ℝ) := Real.rpow_pos_of_pos hn _
  change tail h k.val ≤ primitive h y+density h (n.val:ℝ)/2
  by_cases hb : y ≤ (k.val:ℝ)+1/2
  · have hh := primitive_antitone h (hn.trans_le hy) hb
    linarith only [he,hh,hp]
  · have hh := primitive_loss h hn (show (n.val:ℝ) ≤ k.val+1/2 by linarith only [hnk]) (le_of_not_ge hb)
    have hfloor : y < (k.val:ℝ)+1 := Nat.lt_floor_add_one y
    have hw := mul_le_mul_of_nonneg_right (show y-((k.val:ℝ)+1/2) ≤ 1/2 by linarith only [hfloor]) hp.le
    linarith only [he,hh,hw]

#print axioms density_label
#print axioms tail_step
#print axioms tail_tendsto_zero
#print axioms integer_tail_bounds
#print axioms real_tail_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GibbsTail
