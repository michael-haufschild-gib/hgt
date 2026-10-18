import GaloisForLFunctions.TransHorizonIncidenceMechanics.ShortWindowCorrelationDefectAndIsoStateClassification

/-!
# Nonnegative weights, endpoint order, and calibrated short-window defect

For nonnegative coefficients, universal short-window defect nonpositivity is
exactly reverse divisibility of endpoint observation states. For squarefree-supported
coefficients, the corresponding order is divisibility of radical states. Ordered
endpoints give the quantitative bound `D <= -E/2`, without a full-period return.

Necessity survives every fixed positive harmonic scalar H and the coefficient box
`0 <= c(d) <= H`: a weight supported on 1 and one newly visible divisor produces
positive defect. The squarefree witness uses a prime. At zero harmonic scalar all
nonnegative visible coefficients vanish; negative harmonic scalar is infeasible.

Classical baseline: finite divisor incidence transforms and r-even functions as in
Toth--Haukkanen, https://arxiv.org/abs/1009.5281, with shifted-correlation quantities
as in Coppola--Murty--Saha, https://arxiv.org/abs/1612.03136. The equivalent classical
statement is copositivity of `sum s(k)*(s(k+1)-s(k))` on a nonnegative divisor-weight
cone, characterized by inclusion of the endpoint divisor sets. The proof combines
elementary positive incidence order, discrete Dirichlet polarization, and a calibrated
two-coefficient perturbation. Labels below distinguish Known, Corollary, and New
formulation. No external novelty claim or new shifted-convolution asymptotic is made.
These coefficient cones do not include the signed Mobius/damped weight families.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- [Known] State divisibility is inclusion of visible divisor tests. -/
theorem horizonObservationState_dvd_iff_visible_inclusion (N k l : ℕ) :
    horizonObservationState N k ∣ horizonObservationState N l ↔
      ∀ d ∈ Finset.Icc 1 N, d ∣ k → d ∣ l := by
  constructor
  · intro h d hd hdk
    exact (dvd_horizonObservationState_iff N l d hd).mp
      (((dvd_horizonObservationState_iff N k d hd).mpr hdk).trans h)
  · intro h
    apply Finset.lcm_dvd
    intro d hd
    have hdI := (Finset.mem_filter.mp hd).1
    exact (dvd_horizonObservationState_iff N l d hdI).mpr
      (h d hdI (Finset.mem_filter.mp hd).2)

/-- [Known] Radical-state divisibility is inclusion of visible prime tests. -/
theorem horizonRadicalState_dvd_iff_prime_inclusion (N k l : ℕ) :
    horizonRadicalState N k ∣ horizonRadicalState N l ↔
      ∀ p : ℕ, p.Prime → p ≤ N → p ∣ k → p ∣ l := by
  constructor
  · intro h p hp hpN hpk
    exact ((prime_dvd_horizonRadicalState_iff N l hp).mp
      (((prime_dvd_horizonRadicalState_iff N k hp).mpr ⟨hpk, hpN⟩).trans h)).1
  · intro h
    rw [← Nat.prod_primeFactors_of_squarefree (horizonRadicalState_squarefree N k)]
    apply (Nat.prod_primeFactors_dvd_iff (horizonRadicalState_pos N l).ne').mpr
    intro p hp
    obtain ⟨hpprime, hpk, _⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨hpk', hpN⟩ := (prime_dvd_horizonRadicalState_iff N k hpprime).mp hpk
    exact Nat.mem_primeFactors.mpr ⟨hpprime,
      (prime_dvd_horizonRadicalState_iff N l hpprime).mpr ⟨h p hpprime hpN hpk', hpN⟩,
      (horizonRadicalState_pos N l).ne'⟩

/-- [Corollary] Failure of state order exposes one nonunit visible divisor. -/
theorem exists_visible_divisor_of_observationState_not_dvd {N k l : ℕ}
    (h : ¬ horizonObservationState N k ∣ horizonObservationState N l) :
    ∃ q : ℕ, q ∈ Finset.Icc 2 N ∧ q ∣ k ∧ ¬ q ∣ l := by
  by_contra! hn
  apply h
  apply (horizonObservationState_dvd_iff_visible_inclusion N k l).mpr
  intro d hd hdk
  by_cases hd1 : d = 1
  · simp [hd1]
  · exact hn d (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega,
      (Finset.mem_Icc.mp hd).2⟩) hdk

/-- [Corollary] Failure of radical order exposes one visible prime. -/
theorem exists_visible_prime_of_radicalState_not_dvd {N k l : ℕ}
    (h : ¬ horizonRadicalState N k ∣ horizonRadicalState N l) :
    ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ p ∣ k ∧ ¬ p ∣ l := by
  by_contra! hn
  exact h ((horizonRadicalState_dvd_iff_prime_inclusion N k l).mpr hn)

/-- [Known] Nonnegative divisor coefficients give nonnegative responses. -/
theorem sieveSeq_nonneg_of_nonneg_weight (N k : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, 0 ≤ c d) : 0 ≤ sieveSeq N c k :=
  Finset.sum_nonneg fun d _ => hc d

/-- [Known] A nonnegative divisor response is monotone in divisibility. -/
theorem sieveSeq_le_of_dvd_of_nonneg_weight (N : ℕ) {k l : ℕ} {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, 0 ≤ c d) (hkl : k ∣ l) : sieveSeq N c k ≤ sieveSeq N c l := by
  unfold sieveSeq
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,
      (Finset.mem_filter.mp hd).2.trans hkl⟩
  · intro d _ _
    exact hc d

/-- [Known] Nonnegative observations detect the complete state order. -/
theorem horizonObservationState_dvd_iff_all_nonneg_sieveSeq_le (N k l : ℕ) :
    horizonObservationState N k ∣ horizonObservationState N l ↔
      ∀ c : ℕ → ℝ, (∀ d : ℕ, 0 ≤ c d) → sieveSeq N c k ≤ sieveSeq N c l := by
  constructor
  · intro h c hc
    rw [← sieveSeq_horizonObservationState N k c, ← sieveSeq_horizonObservationState N l c]
    exact sieveSeq_le_of_dvd_of_nonneg_weight N hc h
  · intro h
    apply (horizonObservationState_dvd_iff_visible_inclusion N k l).mpr
    intro d hd hdk
    have ht := h (fun j => if j = d then 1 else 0) (fun j => by split_ifs <;> positivity)
    by_contra hdl
    simp [sieveSeq, hd, hdk, hdl] at ht
    linarith only [ht]

private theorem indicator_squarefree_support {q : ℕ} (hq : Squarefree q) :
    ∀ d : ℕ, ¬ Squarefree d → (if d = q then (1 : ℝ) else 0) = 0 := by
  intro d hd
  by_cases hdq : d = q
  · subst d
    exact (hd hq).elim
  · simp [hdq]

/-- [Known] Nonnegative squarefree observations detect the radical-state order. -/
theorem horizonRadicalState_dvd_iff_all_nonneg_squarefree_sieveSeq_le (N k l : ℕ) :
    horizonRadicalState N k ∣ horizonRadicalState N l ↔
      ∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
        (∀ d : ℕ, 0 ≤ c d) → sieveSeq N c k ≤ sieveSeq N c l := by
  constructor
  · intro h c hsf hc
    rw [← sieveSeq_horizonRadicalState N k hsf, ← sieveSeq_horizonRadicalState N l hsf]
    exact sieveSeq_le_of_dvd_of_nonneg_weight N hc h
  · intro h
    apply (horizonRadicalState_dvd_iff_prime_inclusion N k l).mpr
    intro p hp hpN hpk
    have ht := h (fun j => if j = p then 1 else 0) (indicator_squarefree_support hp.squarefree)
      (fun j => by split_ifs <;> positivity)
    have hpI : p ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hp.one_le, hpN⟩
    by_contra hpl
    simp [sieveSeq, hpI, hpk, hpl] at ht
    linarith only [ht]

/-- [Corollary] Every short-window Dirichlet energy is nonnegative. -/
theorem shortWindowDirichletEnergy_nonneg (N M₀ M : ℕ) (c : ℕ → ℝ) :
    0 ≤ shortWindowDirichletEnergy N M₀ M c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem shortWindowRenormalizedDefect_le_neg_half_energy_of_response_le
    (N M₀ M : ℕ) {c : ℕ → ℝ} (hc : ∀ d : ℕ, 0 ≤ c d)
    (h : sieveSeq N c (M₀ + M + 1) ≤ sieveSeq N c (M₀ + 1)) :
    shortWindowRenormalizedDefect N M₀ M c ≤ -shortWindowDirichletEnergy N M₀ M c / 2 := by
  have hs := pow_le_pow_left₀ (sieveSeq_nonneg_of_nonneg_weight N (M₀ + M + 1) hc) h 2
  have hid := two_mul_shortWindowRenormalizedDefect_eq N M₀ M c
  linarith only [hs, hid]

theorem shortWindowRenormalizedDefect_le_neg_half_energy_of_state_dvd
    (N M₀ M : ℕ) {c : ℕ → ℝ} (hc : ∀ d : ℕ, 0 ≤ c d)
    (h : horizonObservationState N (M₀ + M + 1) ∣ horizonObservationState N (M₀ + 1)) :
    shortWindowRenormalizedDefect N M₀ M c ≤ -shortWindowDirichletEnergy N M₀ M c / 2 :=
  shortWindowRenormalizedDefect_le_neg_half_energy_of_response_le N M₀ M hc
    ((horizonObservationState_dvd_iff_all_nonneg_sieveSeq_le N _ _).mp h c hc)

theorem shortWindowRenormalizedDefect_le_neg_half_energy_of_radical_dvd
    (N M₀ M : ℕ) {c : ℕ → ℝ} (hsf : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hc : ∀ d : ℕ, 0 ≤ c d)
    (h : horizonRadicalState N (M₀ + M + 1) ∣ horizonRadicalState N (M₀ + 1)) :
    shortWindowRenormalizedDefect N M₀ M c ≤ -shortWindowDirichletEnergy N M₀ M c / 2 :=
  shortWindowRenormalizedDefect_le_neg_half_energy_of_response_le N M₀ M hc
    ((horizonRadicalState_dvd_iff_all_nonneg_squarefree_sieveSeq_le N _ _).mp h c hsf hc)

/-- [Corollary] Short-window defect is quadratic under weight scaling. -/
theorem shortWindowRenormalizedDefect_scale_weight (N M₀ M : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    shortWindowRenormalizedDefect N M₀ M (fun d => t * c d) =
      t ^ (2 : ℕ) * shortWindowRenormalizedDefect N M₀ M c := by
  simp only [shortWindowRenormalizedDefect, sieveRenormalizedPrefixDefect_scale_weight]
  ring

/-- [New formulation] One newly visible divisor yields a bounded positive-defect witness at any positive harmonic scalar. -/
theorem exists_calibrated_two_atom_positive_shortWindowDefect (N M₀ M : ℕ)
    {H : ℝ} (hH : 0 < H) {q : ℕ} (hq : q ∈ Finset.Icc 2 N)
    (hqr : q ∣ M₀ + M + 1) (hql : ¬ q ∣ M₀ + 1) :
    ∃ c : ℕ → ℝ, (∀ d : ℕ, d ≠ 1 → d ≠ q → c d = 0) ∧
      (∀ d : ℕ, 0 ≤ c d ∧ c d ≤ H) ∧ finiteHarmonicSum N c = H ∧
      0 < shortWindowRenormalizedDefect N M₀ M c := by
  let u : ℕ → ℝ := fun d => if d = q then 1 else 0
  let D := shortWindowRenormalizedDefect N M₀ M u
  let Q : ℝ := D - 1 / (q : ℝ)
  let t : ℝ := H / (|Q| + 1)
  let c := sieveUnitShiftWeight (fun d => t * u d) (H - t / (q : ℝ))
  have hq2 := (Finset.mem_Icc.mp hq).1
  have hqN := (Finset.mem_Icc.mp hq).2
  have hq1 : q ≠ 1 := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqpos : (0 : ℝ) < q := by linarith
  have ht : 0 < t := div_pos hH (by positivity)
  have hcancel : t * (|Q| + 1) = H := div_mul_cancel₀ H (ne_of_gt (by positivity))
  have htH : t ≤ H := by nlinarith [mul_nonneg ht.le (abs_nonneg Q)]
  have hdiv0 : 0 ≤ t / (q : ℝ) := div_nonneg ht.le hqpos.le
  have hdivle : t / (q : ℝ) ≤ t := (div_le_iff₀ hqpos).mpr (by nlinarith)
  have ha0 : 0 ≤ H - t / (q : ℝ) := by linarith
  have haH : H - t / (q : ℝ) ≤ H := by linarith
  have hqI : q ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hqN⟩
  have hNI : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hur : sieveSeq N u (M₀ + M + 1) = 1 := by simp [u, sieveSeq, hqI, hqr]
  have hul : sieveSeq N u (M₀ + 1) = 0 := by simp [u, sieveSeq, hqI, hql]
  have hvalue : shortWindowRenormalizedDefect N M₀ M c = t * H + t ^ (2 : ℕ) * Q := by
    dsimp only [c]
    rw [shortWindowRenormalizedDefect_unitShiftWeight,
      shortWindowRenormalizedDefect_scale_weight, sieveSeq_scale_weight, sieveSeq_scale_weight,
      hur, hul]
    dsimp only [Q, D]
    ring
  have hpositive : 0 < t ^ (2 : ℕ) * (Q + |Q| + 1) := by
    apply mul_pos (sq_pos_of_pos ht)
    linarith [neg_abs_le Q]
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro d hd1 hdq
    simp [c, sieveUnitShiftWeight, u, hd1, hdq]
  · intro d
    by_cases hd1 : d = 1
    · subst d
      simpa [c, sieveUnitShiftWeight, u, Ne.symm hq1] using And.intro ha0 haH
    · by_cases hdq : d = q
      · subst d
        simpa [c, sieveUnitShiftWeight, u, hq1] using And.intro ht.le htH
      · simp [c, sieveUnitShiftWeight, u, hd1, hdq, hH.le]
  · simp [c, sieveUnitShiftWeight, u, finiteHarmonicSum, add_div,
      Finset.sum_add_distrib, mul_ite, ite_div, hqI, hNI]
  · rw [hvalue]
    have hcancel' := congrArg (fun x : ℝ => t * x) hcancel
    nlinarith only [hpositive, hcancel']

theorem exists_bounded_calibrated_positive_shortWindowDefect_of_state_not_dvd
    (N M₀ M : ℕ) {H : ℝ} (hH : 0 < H)
    (h : ¬ horizonObservationState N (M₀ + M + 1) ∣ horizonObservationState N (M₀ + 1)) :
    ∃ c : ℕ → ℝ, (∀ d : ℕ, 0 ≤ c d ∧ c d ≤ H) ∧ finiteHarmonicSum N c = H ∧
      0 < shortWindowRenormalizedDefect N M₀ M c := by
  obtain ⟨q, hq, hqr, hql⟩ := exists_visible_divisor_of_observationState_not_dvd h
  obtain ⟨c, _, hbox, hcal, hpos⟩ :=
    exists_calibrated_two_atom_positive_shortWindowDefect N M₀ M hH hq hqr hql
  exact ⟨c, hbox, hcal, hpos⟩

theorem exists_bounded_calibrated_squarefree_positive_shortWindowDefect_of_radical_not_dvd
    (N M₀ M : ℕ) {H : ℝ} (hH : 0 < H)
    (h : ¬ horizonRadicalState N (M₀ + M + 1) ∣ horizonRadicalState N (M₀ + 1)) :
    ∃ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) ∧
      (∀ d : ℕ, 0 ≤ c d ∧ c d ≤ H) ∧ finiteHarmonicSum N c = H ∧
      0 < shortWindowRenormalizedDefect N M₀ M c := by
  obtain ⟨p, hp, hpN, hpr, hpl⟩ := exists_visible_prime_of_radicalState_not_dvd h
  obtain ⟨c, hsupport, hbox, hcal, hpos⟩ :=
    exists_calibrated_two_atom_positive_shortWindowDefect N M₀ M hH
      (Finset.mem_Icc.mpr ⟨hp.two_le, hpN⟩) hpr hpl
  refine ⟨c, ?_, hbox, hcal, hpos⟩
  intro d hd
  apply hsupport d
  · rintro rfl
    exact hd squarefree_one
  · rintro rfl
    exact hd hp.squarefree

theorem forall_bounded_calibrated_shortWindowDefect_nonpos_iff_state_dvd
    (N M₀ M : ℕ) {H : ℝ} (hH : 0 < H) :
    (∀ c : ℕ → ℝ, (∀ d : ℕ, 0 ≤ c d ∧ c d ≤ H) → finiteHarmonicSum N c = H →
      shortWindowRenormalizedDefect N M₀ M c ≤ 0) ↔
      horizonObservationState N (M₀ + M + 1) ∣ horizonObservationState N (M₀ + 1) := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨c, hbox, hcal, hpos⟩ :=
      exists_bounded_calibrated_positive_shortWindowDefect_of_state_not_dvd N M₀ M hH hn
    exact (not_le_of_gt hpos) (h c hbox hcal)
  · intro h c hc _
    have hb := shortWindowRenormalizedDefect_le_neg_half_energy_of_state_dvd N M₀ M
      (fun d => (hc d).1) h
    have he := shortWindowDirichletEnergy_nonneg N M₀ M c
    linarith

theorem forall_bounded_calibrated_squarefree_shortWindowDefect_nonpos_iff_radical_dvd
    (N M₀ M : ℕ) {H : ℝ} (hH : 0 < H) :
    (∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
      (∀ d : ℕ, 0 ≤ c d ∧ c d ≤ H) → finiteHarmonicSum N c = H →
        shortWindowRenormalizedDefect N M₀ M c ≤ 0) ↔
      horizonRadicalState N (M₀ + M + 1) ∣ horizonRadicalState N (M₀ + 1) := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨c, hsf, hbox, hcal, hpos⟩ :=
      exists_bounded_calibrated_squarefree_positive_shortWindowDefect_of_radical_not_dvd
        N M₀ M hH hn
    exact (not_le_of_gt hpos) (h c hsf hbox hcal)
  · intro h c hsf hc _
    have hb := shortWindowRenormalizedDefect_le_neg_half_energy_of_radical_dvd N M₀ M
      hsf (fun d => (hc d).1) h
    have he := shortWindowDirichletEnergy_nonneg N M₀ M c
    linarith

/-- [New formulation] Universal nonnegative-weight dissipation is exactly reverse endpoint-state divisibility. -/
theorem forall_nonneg_shortWindowDefect_nonpos_iff_state_dvd (N M₀ M : ℕ) :
    (∀ c : ℕ → ℝ, (∀ d : ℕ, 0 ≤ c d) → shortWindowRenormalizedDefect N M₀ M c ≤ 0) ↔
      horizonObservationState N (M₀ + M + 1) ∣ horizonObservationState N (M₀ + 1) := by
  constructor
  · intro h
    exact (forall_bounded_calibrated_shortWindowDefect_nonpos_iff_state_dvd N M₀ M
      (H := 1) (by positivity)).mp (fun c hc _ => h c (fun d => (hc d).1))
  · intro h c hc
    have hb := shortWindowRenormalizedDefect_le_neg_half_energy_of_state_dvd N M₀ M hc h
    have he := shortWindowDirichletEnergy_nonneg N M₀ M c
    linarith

/-- [New formulation] Universal nonnegative squarefree dissipation is exactly reverse radical divisibility. -/
theorem forall_nonneg_squarefree_shortWindowDefect_nonpos_iff_radical_dvd (N M₀ M : ℕ) :
    (∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) → (∀ d : ℕ, 0 ≤ c d) →
      shortWindowRenormalizedDefect N M₀ M c ≤ 0) ↔
      horizonRadicalState N (M₀ + M + 1) ∣ horizonRadicalState N (M₀ + 1) := by
  constructor
  · intro h
    exact (forall_bounded_calibrated_squarefree_shortWindowDefect_nonpos_iff_radical_dvd
      N M₀ M (H := 1) (by positivity)).mp (fun c hsf hc _ => h c hsf (fun d => (hc d).1))
  · intro h c hsf hc
    have hb := shortWindowRenormalizedDefect_le_neg_half_energy_of_radical_dvd N M₀ M hsf hc h
    have he := shortWindowDirichletEnergy_nonneg N M₀ M c
    linarith

private theorem harmonic_nonneg (N : ℕ) {c : ℕ → ℝ} (hc : ∀ d : ℕ, 0 ≤ c d) :
    0 ≤ finiteHarmonicSum N c :=
  Finset.sum_nonneg fun d _ => div_nonneg (hc d) (Nat.cast_nonneg d)

/-- [Known] Zero harmonic sum on the nonnegative cone is equivalent to zero visible coefficients. -/
theorem nonneg_weight_harmonic_zero_iff_visible_zero (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, 0 ≤ c d) :
    finiteHarmonicSum N c = 0 ↔ ∀ d ∈ Finset.Icc 1 N, c d = 0 := by
  constructor
  · intro h d hd
    have hle : c d / (d : ℝ) ≤ finiteHarmonicSum N c :=
      Finset.single_le_sum (fun j _ => div_nonneg (hc j) (Nat.cast_nonneg j)) hd
    rw [h] at hle
    have hdR : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    exact le_antisymm (by simpa using (div_le_iff₀ hdR).mp hle) (hc d)
  · intro h
    apply Finset.sum_eq_zero
    intro d hd
    rw [h d hd, zero_div]

/-- [Corollary] Nonpositive harmonic scalar forces zero defect for every nonnegative weight. -/
theorem shortWindowDefect_eq_zero_of_nonneg_harmonic_nonpos (N M₀ M : ℕ)
    {c : ℕ → ℝ} (hc : ∀ d : ℕ, 0 ≤ c d) (hH : finiteHarmonicSum N c ≤ 0) :
    shortWindowRenormalizedDefect N M₀ M c = 0 := by
  have hzero := (nonneg_weight_harmonic_zero_iff_visible_zero N hc).mp
    (le_antisymm hH (harmonic_nonneg N hc))
  have hs : ∀ k, sieveSeq N c k = 0 := by
    intro k
    apply Finset.sum_eq_zero
    intro d hd
    exact hzero d (Finset.mem_filter.mp hd).1
  simp [shortWindowRenormalizedDefect_eq_sum_mul_addDiff, hs]

/-- [New formulation] Complete harmonic-slice classification, including the zero and infeasible negative cases. -/
theorem forall_nonneg_harmonic_shortWindowDefect_nonpos_iff (N M₀ M : ℕ) (H : ℝ) :
    (∀ c : ℕ → ℝ, (∀ d : ℕ, 0 ≤ c d) → finiteHarmonicSum N c = H →
      shortWindowRenormalizedDefect N M₀ M c ≤ 0) ↔
      H ≤ 0 ∨ horizonObservationState N (M₀ + M + 1) ∣ horizonObservationState N (M₀ + 1) := by
  constructor
  · intro h
    by_cases hH : H ≤ 0
    · exact Or.inl hH
    · exact Or.inr ((forall_bounded_calibrated_shortWindowDefect_nonpos_iff_state_dvd
        N M₀ M (lt_of_not_ge hH)).mp (fun c hc hcal => h c (fun d => (hc d).1) hcal))
  · rintro (hH | hstate) c hc hcal
    · rw [shortWindowDefect_eq_zero_of_nonneg_harmonic_nonpos N M₀ M hc (by simpa [hcal] using hH)]
    · exact (forall_nonneg_shortWindowDefect_nonpos_iff_state_dvd N M₀ M).mpr hstate c hc

theorem forall_nonneg_squarefree_harmonic_shortWindowDefect_nonpos_iff
    (N M₀ M : ℕ) (H : ℝ) :
    (∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
      (∀ d : ℕ, 0 ≤ c d) → finiteHarmonicSum N c = H →
        shortWindowRenormalizedDefect N M₀ M c ≤ 0) ↔
      H ≤ 0 ∨ horizonRadicalState N (M₀ + M + 1) ∣ horizonRadicalState N (M₀ + 1) := by
  constructor
  · intro h
    by_cases hH : H ≤ 0
    · exact Or.inl hH
    · exact Or.inr ((forall_bounded_calibrated_squarefree_shortWindowDefect_nonpos_iff_radical_dvd
        N M₀ M (lt_of_not_ge hH)).mp (fun c hsf hc hcal => h c hsf (fun d => (hc d).1) hcal))
  · rintro (hH | hstate) c hsf hc hcal
    · rw [shortWindowDefect_eq_zero_of_nonneg_harmonic_nonpos N M₀ M hc (by simpa [hcal] using hH)]
    · exact (forall_nonneg_squarefree_shortWindowDefect_nonpos_iff_radical_dvd N M₀ M).mpr
        hstate c hsf hc

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
