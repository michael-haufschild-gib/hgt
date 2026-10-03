import GaloisForLFunctions.HTGeometry.BaileyCrandallParityDrift

/-!
# The Bailey–Crandall sequence of `π` has no finite attractor

Bailey and Crandall's Hypothesis A asserts that a sequence `x_{n+1} = fract(b xₙ + r(n))` with
rational forcing `r(n) → 0` either has a finite attractor or is equidistributed.  For the BBP
sequence of `π` the first alternative is impossible:

* `not_finiteAttractor_orbit` : for an irrational `x` and an integer `b ≥ 2`, the orbit
  `bⁿ x mod 1` does not approach any finite subset of the circle.  If it did, the defect
  `eₙ = bⁿx − wₙ` would satisfy `e_{n+1} = b eₙ` exactly once the attracting points are matched,
  so `eₙ = 0`, the orbit would be eventually periodic, and `x` would be rational.
* `not_hasFiniteAttractor_bbpSeq` : the Bailey–Crandall sequence of `π` has no finite attractor.
* `not_parityDriftHypothesis_pi_of_hypothesisA` : Hypothesis A for this one sequence refutes the
  Parity-Drift Hypothesis for `π`.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.BBPPi

open BinaryParityDrift

local notation "𝕋" => AddCircle (1 : ℝ)

/-- Multiplication by `k` scales the circle norm exactly while `k ‖z‖ ≤ 1/2`. -/
theorem norm_nsmul_eq_of_le {z : 𝕋} {k : ℕ} (hk : (k : ℝ) * ‖z‖ ≤ 1 / 2) :
    ‖k • z‖ = k * ‖z‖ := by
  induction z using QuotientAddGroup.induction_on with
  | H x =>
    set a : ℝ := x - round x with ha
    have hcoe : ((x : ℝ) : 𝕋) = (a : 𝕋) := by
      rw [ha, AddCircle.coe_sub, eq_comm, sub_eq_self, AddCircle.coe_eq_zero_iff]
      exact ⟨round x, by simp⟩
    have hna : ‖(a : 𝕋)‖ = |a| := by
      rw [AddCircle.norm_eq, ha]
      simp
    show ‖k • ((x : ℝ) : 𝕋)‖ = k * ‖((x : ℝ) : 𝕋)‖
    rw [hcoe, hna, ← AddCircle.coe_nsmul, nsmul_eq_mul]
    rw [hcoe, hna] at hk
    rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr
      (by rw [abs_mul, Nat.abs_cast, abs_one]; linarith), abs_mul, Nat.abs_cast]

theorem eq_zero_of_pow_mul_lt {b : ℕ} (hb : 2 ≤ b) {c ε : ℝ} (hc : 0 ≤ c)
    (h : ∀ k : ℕ, (b : ℝ) ^ k * c < ε) : c = 0 := by
  by_contra hne
  have hpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hne)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (ε / c) hb1
  have := h k
  rw [div_lt_iff₀ hpos] at hk
  linarith

/-- **No finite attractor.**  For irrational `x` and `b ≥ 2`, the orbit `bⁿx mod 1` does not
approach any finite subset of the circle. -/
theorem not_finiteAttractor_orbit {x : ℝ} (hx : Irrational x) {b : ℕ} (hb : 2 ≤ b)
    (W : Finset 𝕋) :
    ¬ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ w ∈ W, ‖((((b : ℝ) ^ n * x : ℝ)) : 𝕋) - w‖ < ε := by
  intro hW
  set Y : ℕ → 𝕋 := fun n => (((b : ℝ) ^ n * x : ℝ) : 𝕋) with hY
  have hYsucc : ∀ n, Y (n + 1) = b • Y n := fun n => by
    simp only [hY]
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, pow_succ]
    ring_nf
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  -- the positive defects between attracting points
  set D : Finset ℝ := (W ×ˢ W).image fun p => ‖b • p.1 - p.2‖ with hD
  set P : Finset ℝ := D.filter fun d => 0 < d
  set δ : ℝ := if h : P.Nonempty then P.min' h else 1 with hδ
  have hδpos : 0 < δ := by
    simp only [hδ]
    split_ifs with h
    · exact (mem_filter.mp (P.min'_mem h)).2
    · norm_num
  have hDzero : ∀ w ∈ W, ∀ w' ∈ W, ‖b • w - w'‖ < δ → ‖b • w - w'‖ = 0 := by
    intro w hw w' hw' hlt
    by_contra hne
    have hpos : 0 < ‖b • w - w'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hmemP : ‖b • w - w'‖ ∈ P :=
      mem_filter.mpr ⟨mem_image.mpr ⟨(w, w'), mem_product.mpr ⟨hw, hw'⟩, rfl⟩, hpos⟩
    have hne' : P.Nonempty := ⟨_, hmemP⟩
    have : δ ≤ ‖b • w - w'‖ := by
      simp only [hδ, dif_pos hne']
      exact P.min'_le _ hmemP
    linarith
  set ε : ℝ := min (δ / (2 * (b + 1))) (1 / (2 * b)) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε1 : ((b : ℝ) + 1) * ε < δ := by
    have h1 : ε ≤ δ / (2 * (b + 1)) := min_le_left _ _
    have h2 : ((b : ℝ) + 1) * ε ≤ ((b : ℝ) + 1) * (δ / (2 * (b + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ((b : ℝ) + 1) * (δ / (2 * (b + 1))) = δ / 2 := by field_simp
    linarith
  have hε2 : (b : ℝ) * ε ≤ 1 / 2 := by
    have h1 : ε ≤ 1 / (2 * b) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_left h1 hb0.le
    rw [show (b : ℝ) * (1 / (2 * b)) = 1 / 2 by field_simp] at h2
    exact h2
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hW ε hεpos)
  choose! w hwW hwY using hN
  have hstep : ∀ n ≥ N, b • w n = w (n + 1) := by
    intro n hn
    have h1 := hwY n hn
    have h2 := hwY (n + 1) (by omega)
    have e : b • w n - w (n + 1) = (Y (n + 1) - w (n + 1)) - b • (Y n - w n) := by
      rw [hYsucc, smul_sub]; abel
    have hle : ‖b • w n - w (n + 1)‖ < δ := by
      calc ‖b • w n - w (n + 1)‖ ≤ ‖Y (n + 1) - w (n + 1)‖ + ‖b • (Y n - w n)‖ := by
            rw [e]; exact norm_sub_le _ _
        _ ≤ ε + b * ‖Y n - w n‖ := add_le_add h2.le norm_nsmul_le
        _ ≤ ε + b * ε := by gcongr
        _ = (b + 1) * ε := by ring
        _ < δ := hε1
    have h0 := hDzero _ (hwW n hn) _ (hwW (n + 1) (by omega)) hle
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  set E : ℕ → 𝕋 := fun n => Y n - w n with hE
  have hEsucc : ∀ n ≥ N, E (n + 1) = b • E n := by
    intro n hn
    simp only [hE]
    rw [hYsucc, ← hstep n hn, smul_sub]
  have hEnorm : ∀ n ≥ N, ‖E (n + 1)‖ = b * ‖E n‖ := by
    intro n hn
    rw [hEsucc n hn]
    apply norm_nsmul_eq_of_le
    have := (hwY n hn).le
    calc (b : ℝ) * ‖E n‖ ≤ b * ε := by gcongr
      _ ≤ 1 / 2 := hε2
  have hpow : ∀ k : ℕ, ‖E (N + k)‖ = (b : ℝ) ^ k * ‖E N‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, hEnorm _ (by omega), ih, pow_succ]
      ring
  have hEN : ‖E N‖ = 0 :=
    eq_zero_of_pow_mul_lt hb (norm_nonneg _) fun k => by
      rw [← hpow k]; exact hwY _ (by omega)
  have hzero : ∀ k : ℕ, Y (N + k) = w (N + k) := by
    intro k
    have : ‖E (N + k)‖ = 0 := by rw [hpow, hEN, mul_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  obtain ⟨k, k', hlt, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun k : ℕ => Y (N + k)) (t := (W : Set 𝕋))
    (fun k => by rw [hzero]; exact hwW _ (by omega)) W.finite_toSet
  simp only [hY] at heq
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at heq
  obtain ⟨m, hm⟩ := heq
  rw [zsmul_eq_mul, mul_one] at hm
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hlt' : (b : ℝ) ^ (N + k) < (b : ℝ) ^ (N + k') := pow_lt_pow_right₀ hb1 (by omega)
  have hden : (b : ℝ) ^ (N + k) - (b : ℝ) ^ (N + k') ≠ 0 := by linarith
  apply hx
  refine ⟨(m : ℚ) / ((b : ℚ) ^ (N + k) - (b : ℚ) ^ (N + k')), ?_⟩
  push_cast
  rw [div_eq_iff hden, hm]
  ring

/-- A real sequence has a finite attractor: it approaches a finite set. -/
def HasFiniteAttractor (u : ℕ → ℝ) : Prop :=
  ∃ W : Finset ℝ, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ w ∈ W, |u n - w| < ε

theorem coe_sixteen_pow_mul_pi (n : ℕ) :
    (((16 : ℝ) ^ n * Real.pi : ℝ) : 𝕋) = ((bbpSeq n + bbpTail n : ℝ) : 𝕋) := by
  rw [sixteen_pow_mul_pi, bbpSeq, ← Int.self_sub_floor (bbpHead n),
    show bbpHead n + bbpTail n = (bbpHead n - ⌊bbpHead n⌋ + bbpTail n) + ((⌊bbpHead n⌋ : ℤ) : ℝ) by
      ring,
    AddCircle.coe_add,
    show ((((⌊bbpHead n⌋ : ℤ) : ℝ)) : 𝕋) = 0 from
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨⌊bbpHead n⌋, by simp⟩, add_zero]

theorem norm_coe_le_abs (a : ℝ) : ‖(a : 𝕋)‖ ≤ |a| := by
  rw [AddCircle.norm_eq]
  simpa using round_le a 0

/-- **The Bailey–Crandall sequence of `π` has no finite attractor.** -/
theorem not_hasFiniteAttractor_bbpSeq : ¬ HasFiniteAttractor bbpSeq := by
  rintro ⟨W, hW⟩
  refine not_finiteAttractor_orbit irrational_pi (b := 16) (by norm_num)
    (W.image fun w : ℝ => (w : 𝕋)) ?_
  intro ε hε
  filter_upwards [hW (ε / 2) (by positivity),
    tendsto_bbpTail.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))] with n hn ht
  obtain ⟨w, hw, hlt⟩ := hn
  refine ⟨(w : 𝕋), mem_image_of_mem _ hw, ?_⟩
  push_cast
  rw [coe_sixteen_pow_mul_pi, ← AddCircle.coe_sub]
  calc ‖((bbpSeq n + bbpTail n - w : ℝ) : 𝕋)‖ ≤ |bbpSeq n + bbpTail n - w| := norm_coe_le_abs _
    _ ≤ |bbpSeq n - w| + |bbpTail n| := by
        rw [show bbpSeq n + bbpTail n - w = (bbpSeq n - w) + bbpTail n by ring]
        exact abs_add_le _ _
    _ < ε / 2 + ε / 2 := by rw [abs_of_nonneg (bbpTail_nonneg n)]; linarith
    _ = ε := by ring

/-- Bailey–Crandall Hypothesis A for the BBP sequence of `π`. -/
def BBPHypothesisA : Prop := HasFiniteAttractor bbpSeq ∨ BBPEquidistributed

/-- **Hypothesis A for `π` refutes the Parity-Drift Hypothesis.** -/
theorem not_parityDriftHypothesis_pi_of_hypothesisA (h : BBPHypothesisA) :
    ¬ ParityDriftHypothesis Real.pi := by
  rcases h with h | h
  · exact absurd h not_hasFiniteAttractor_bbpSeq
  · exact not_parityDriftHypothesis_pi_of_bbpEquidistributed h

end GaloisForLFunctions.HTGeometry.BBPPi
