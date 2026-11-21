import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliClawGrowingCutoff

/-!
# Almost-sure scale of the strongest six-coordinate Pauli certificate

A block has strength equal to its weakest certificate coefficient.
Over a prefix, the maximum block strength differs from the Gaussian
cutoff scale by a quantity tending to zero almost surely. The upper
tail is summable along dyadic prefixes, whose scale gaps vanish.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private def blockMagnitudes (ω : PathPauliDisorder) (j : ℕ) : Finset ℝ :=
  clawBlockLabels.image fun i => |pathPauliBlock ω j i|

private theorem blockMagnitudes_nonempty (ω : PathPauliDisorder) (j : ℕ) :
    (blockMagnitudes ω j).Nonempty := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < clawBlockLabels.card by
    rw [card_clawBlockLabels]; exact Nat.zero_lt_succ 5)
  exact ⟨_, Finset.mem_image_of_mem _ hi⟩

/-- The smallest magnitude among a block's six witness coefficients. -/
def clawBlockStrength (ω : PathPauliDisorder) (j : ℕ) : ℝ :=
  (blockMagnitudes ω j).min' (blockMagnitudes_nonempty ω j)

theorem mem_clawBlockEvent_iff_lt_strength (ω : PathPauliDisorder) (j : ℕ) (t : ℝ) :
    pathPauliBlock ω j ∈ clawBlockEvent t ↔ t < clawBlockStrength ω j := by
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp
      (Finset.min'_mem (blockMagnitudes ω j) (blockMagnitudes_nonempty ω j))
    have hh : t < |pathPauliBlock ω j i| := h i hi
    exact hh.trans_eq he
  · intro h i hi
    exact h.trans_le (Finset.min'_le _ _ (Finset.mem_image_of_mem _ hi))

private def prefixStrengthValues (ω : PathPauliDisorder) (n : ℕ) : Finset ℝ :=
  insert 0 ((Finset.range ((n + 1) / 2)).image (clawBlockStrength ω))

private theorem prefixStrengthValues_nonempty (ω : PathPauliDisorder) (n : ℕ) :
    (prefixStrengthValues ω n).Nonempty :=
  ⟨0, Finset.mem_insert_self _ _⟩

/-- The strongest six-coordinate certificate inside the prefix of n+2 sites. -/
def clawPrefixStrength (ω : PathPauliDisorder) (n : ℕ) : ℝ :=
  (prefixStrengthValues ω n).max' (prefixStrengthValues_nonempty ω n)

private theorem blockStrength_le_prefixStrength (ω : PathPauliDisorder) {n j : ℕ}
    (hj : j ∈ Finset.range ((n + 1) / 2)) :
    clawBlockStrength ω j ≤ clawPrefixStrength ω n :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))

theorem clawPrefixStrength_mono (ω : PathPauliDisorder) : Monotone (clawPrefixStrength ω) := by
  intro n m h
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    apply blockStrength_le_prefixStrength
    apply Finset.mem_range.mpr
    exact (Finset.mem_range.mp hj).trans_le (by omega)

theorem lt_clawPrefixStrength_iff (ω : PathPauliDisorder) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t < clawPrefixStrength ω n ↔
      ∃ j ∈ Finset.range ((n + 1) / 2), pathPauliBlock ω j ∈ clawBlockEvent t := by
  constructor
  · intro h
    rcases Finset.mem_insert.mp (Finset.max'_mem
      (prefixStrengthValues ω n) (prefixStrengthValues_nonempty ω n)) with he | he
    · exact (not_lt_of_ge ht (h.trans_eq he)).elim
    · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp he
      exact ⟨j, hj, (mem_clawBlockEvent_iff_lt_strength _ _ _).mpr (h.trans_eq heq.symm)⟩
  · rintro ⟨j, hj, hb⟩
    exact ((mem_clawBlockEvent_iff_lt_strength _ _ _).mp hb).trans_le
      (blockStrength_le_prefixStrength ω hj)

private def dyadicPrefix (k : ℕ) : ℕ := 2 ^ (k + 1) - 1

private theorem dyadicPrefix_mono : Monotone dyadicPrefix := by
  intro a b h
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)) _

private theorem lt_dyadicPrefix_self (k : ℕ) : k < dyadicPrefix k := by
  have h := Nat.lt_two_pow_self (n := k + 1)
  unfold dyadicPrefix
  omega

private theorem scale_mono : Monotone clawCutoffScale := by
  intro n m h
  unfold clawCutoffScale
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)

private def dyadicLogStep : ℝ := Real.log 2 / 3

private theorem dyadicLogStep_pos : 0 < dyadicLogStep :=
  div_pos (Real.log_pos (by norm_num)) (by norm_num)

private theorem scale_dyadic (k : ℕ) :
    clawCutoffScale (dyadicPrefix k) = Real.sqrt (dyadicLogStep * ((k : ℝ) + 1)) := by
  have hnat : dyadicPrefix k + 1 = 2 ^ (k + 1) := by
    unfold dyadicPrefix
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos (by omega : 0 < (2 : ℕ)) _))
  have hreal : (dyadicPrefix k : ℝ) + 1 = (2 : ℝ) ^ (k + 1) := by exact_mod_cast hnat
  unfold clawCutoffScale dyadicLogStep
  rw [hreal, Real.log_pow, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

private theorem eventually_scale_dyadic_gap_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, clawCutoffScale (dyadicPrefix (k + 1)) ≤ clawCutoffScale (dyadicPrefix k) + η := by
  let a := dyadicLogStep
  have ha : 0 < a := dyadicLogStep_pos
  let b := a / (2 * η)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  obtain ⟨K, hK⟩ := exists_nat_ge (b ^ 2 / a)
  filter_upwards [eventually_ge_atTop K] with k hk
  have hKr : (K : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (hk.trans (Nat.le_succ _))
  have hr : b ≤ Real.sqrt (a * ((k : ℝ) + 1)) := by
    have he := (div_le_iff₀ ha).mp (hK.trans hKr)
    exact (Real.sqrt_sq hb).symm.trans_le (Real.sqrt_le_sqrt (by simpa only [mul_comm] using he))
  have hr' : a ≤ (2 * η) * Real.sqrt (a * ((k : ℝ) + 1)) := by
    have h := (div_le_iff₀ (show 0 < 2 * η by positivity)).mp (show a / (2 * η) ≤ _ from hr)
    simpa only [mul_comm] using h
  rw [scale_dyadic, scale_dyadic]
  change √(a * (((k + 1 : ℕ) : ℝ) + 1)) ≤ √(a * ((k : ℝ) + 1)) + η
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Nat.cast_add, Nat.cast_one, Real.sq_sqrt (by positivity)]
  have hs : (√(a * ((k : ℝ) + 1))) ^ 2 = a * ((k : ℝ) + 1) := Real.sq_sqrt (by positivity)
  nlinarith only [hr', hs, sq_nonneg η]

private theorem ae_eventually_notMem_dyadic_exp_bound (E : ℕ → Set PathPauliDisorder)
    {C₀ η : ℝ} (hC₀ : 0 ≤ C₀) (hη : 0 < η)
    (hrate : ∀ k, pathPauliDisorderLaw (E k) ≤
      ENNReal.ofReal (C₀ * Real.exp (-(6 * η * clawCutoffScale (dyadicPrefix k))))) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω ∉ E k := by
  let a := dyadicLogStep
  have ha : 0 < a := dyadicLogStep_pos
  let Q := (6 * η) ^ 4 * a ^ 2
  let C := (C₀ * 24) / Q
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hprob (k : ℕ) :
      pathPauliDisorderLaw (E k) ≤ ENNReal.ofReal (C * (1 / ((k : ℝ) + 1) ^ 2)) := by
    let r := Real.sqrt (a * ((k : ℝ) + 1))
    let v := 6 * η * r
    have hv : 0 < v := by dsimp [v, r]; positivity
    have hv4 : v ^ 4 = Q * ((k : ℝ) + 1) ^ 2 := by
      have hr4 : r ^ 4 = (a * ((k : ℝ) + 1)) ^ 2 := by
        calc
          _ = (r ^ 2) ^ 2 := pow_mul _ _ _
          _ = _ := by rw [show r ^ 2 = a * ((k : ℝ) + 1) from Real.sq_sqrt (by positivity)]
      rw [show v = 6 * η * r from rfl, mul_pow, hr4, mul_pow]
      dsimp [Q]
      ring
    have hTaylor := Real.pow_div_factorial_le_exp v hv.le 4
    have hfact : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hfact] at hTaylor
    have he : Real.exp (-v) ≤ 24 / v ^ 4 := by
      rw [Real.exp_neg, ← inv_div]
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hTaylor
    have H := hrate k
    rw [scale_dyadic] at H
    refine H.trans (ENNReal.ofReal_le_ofReal ?_)
    change C₀ * Real.exp (-v) ≤ _
    calc
      _ ≤ C₀ * (24 / v ^ 4) := mul_le_mul_of_nonneg_left he hC₀
      _ = _ := by rw [hv4, ← div_div]; dsimp [C]; ring
  have hs : Summable (fun k : ℕ => C * (1 / ((k : ℝ) + 1) ^ 2)) := by
    have h := Real.summable_one_div_nat_pow.mpr (show 1 < 2 by omega)
    simpa only [Function.comp_def, Nat.cast_succ] using
      (h.comp_injective Nat.succ_injective).mul_left C
  have hE : (∑' k, pathPauliDisorderLaw (E k)) ≠ ⊤ :=
    ne_top_of_le_ne_top hs.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hprob)
  exact ae_eventually_notMem hE

/-- A Gaussian cutoff tail bound on nested prefix events gives an almost-sure
upper cutoff. The dyadic gaps shrink, so the upper bound holds on every prefix. -/
theorem gaussian_ae_eventually_notMem_prefixEvents_above (E : ℕ → ℝ → Set PathPauliDisorder)
    (hmono : ∀ t, Monotone (fun n => E n t)) (hanti : ∀ n, Antitone (E n))
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hrate : ∀ n η, 0 ≤ η → pathPauliDisorderLaw (E n (clawCutoffScale n + η)) ≤
      ENNReal.ofReal (C * Real.exp (-(6 * η * clawCutoffScale n)))) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω ∉ E n (clawCutoffScale n + ε) := by
  have hh : 0 < ε / 2 := by positivity
  filter_upwards [ae_eventually_notMem_dyadic_exp_bound
    (fun k => E (dyadicPrefix k) (clawCutoffScale (dyadicPrefix k) + ε / 2)) hC hh
    (fun k => hrate (dyadicPrefix k) _ hh.le)] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hω.and (eventually_scale_dyadic_gap_le hh))
  refine eventually_atTop.mpr ⟨dyadicPrefix K, fun n hn => ?_⟩
  have hex : ∃ k, n < dyadicPrefix k := ⟨n, lt_dyadicPrefix_self n⟩
  let k := Nat.find hex
  have hnk : n < dyadicPrefix k := Nat.find_spec hex
  have hk : K < k := by
    by_contra! h
    exact (not_lt_of_ge ((dyadicPrefix_mono h).trans hn)) hnk
  have hprev : dyadicPrefix (k - 1) ≤ n := by
    apply le_of_not_gt
    exact Nat.find_min hex (show k - 1 < k by omega)
  have he : k - 1 + 1 = k := by omega
  have hgap := (hK (k - 1) (by omega)).2
  rw [he] at hgap
  have hup := (hK k hk.le).1
  have hscale := scale_mono hprev
  intro hhit
  exact hup (hanti _ (by linarith only [hgap, hscale]) ((hmono _) hnk.le hhit))

/-- Almost surely the upper bound at any positive fixed margin holds
along all sufficiently long prefixes of the common draw. -/
theorem gaussian_ae_eventually_clawStrength_le_scale_add {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      clawPrefixStrength ω n ≤ clawCutoffScale n + ε := by
  let E (n : ℕ) (t : ℝ) : Set PathPauliDisorder := {ω | t < clawPrefixStrength ω n}
  have hmono (t : ℝ) : Monotone (fun n => E n t) :=
    fun n m hnm ω hlt => hlt.trans_le (clawPrefixStrength_mono ω hnm)
  have hanti (n : ℕ) : Antitone (E n) := fun _ _ h _ hlt => h.trans_lt hlt
  have hrate (n : ℕ) (η : ℝ) (hη : 0 ≤ η) :
      pathPauliDisorderLaw (E n (clawCutoffScale n + η)) ≤
        ENNReal.ofReal (32 * Real.exp (-(6 * η * clawCutoffScale n))) := by
    have hsubset : E n (clawCutoffScale n + η) ⊆
        (noClawBlockEvent (clawCutoffScale n + η) ((n + 1) / 2))ᶜ := by
      intro ω hlt hnone
      obtain ⟨j, hj, hb⟩ := (lt_clawPrefixStrength_iff ω n
        (add_nonneg (Real.sqrt_nonneg _) hη)).mp hlt
      exact hnone j hj hb
    refine (measure_mono hsubset).trans
      ((gaussian_measure_someClawBlock_above_growingCutoff n hη).trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [sq_nonneg η]))
      (by positivity)
  simpa only [E, Set.mem_setOf_eq, not_lt] using
    gaussian_ae_eventually_notMem_prefixEvents_above E hmono hanti (by norm_num) hε hrate

private theorem exists_small_inverse (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 1 / ((k : ℝ) + 1) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have h := (div_lt_iff₀ hε).mp hk
  refine ⟨k, (div_lt_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr ?_⟩
  nlinarith only [h, hε]

/-- The strongest certificate follows the growing cutoff almost surely
with a vanishing additive error. -/
theorem gaussian_ae_clawPrefixStrength_sub_scale_tendsto :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      Tendsto (fun n : ℕ => clawPrefixStrength ω n - clawCutoffScale n) atTop (𝓝 0) := by
  let d (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hd (k : ℕ) : 0 < d k := by dsimp [d]; positivity
  have hu (k : ℕ) := gaussian_ae_eventually_clawStrength_le_scale_add (hd k)
  have hl (k : ℕ) := gaussian_ae_eventually_clawBlock_at_growing_cutoff (hd k)
  filter_upwards [ae_all_iff.mpr hu, ae_all_iff.mpr hl] with ω hωu hωl
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨k, hk⟩ := exists_small_inverse (-b) (neg_pos.mpr hb)
    filter_upwards [hωl k] with n hn
    obtain ⟨j, hj, hgood⟩ := hn
    have h := ((mem_clawBlockEvent_iff_lt_strength _ _ _).mp hgood).trans_le
      (blockStrength_le_prefixStrength ω hj)
    linarith only [show d k < -b from hk, h]
  · intro b hb
    obtain ⟨k, hk⟩ := exists_small_inverse b hb
    filter_upwards [hωu k] with n hn
    linarith only [show d k < b from hk, hn]

#print axioms lt_clawPrefixStrength_iff
#print axioms gaussian_ae_eventually_clawStrength_le_scale_add
#print axioms gaussian_ae_clawPrefixStrength_sub_scale_tendsto

end

end GaloisForLFunctions.HTGeometry
