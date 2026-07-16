import GaloisForLFunctions.HTGeometry.PolynomialProuhetLock
import GaloisForLFunctions.HTGeometry.StretchedExponentialConvexConfinement

open Filter Finset Set Asymptotics Topology

namespace GaloisForLFunctions

noncomputable section

def powerIncrement (β : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ β - (n : ℝ) ^ β

lemma powerIncrement_strictMono {β : ℝ} (hβ : 1 < β) :
    StrictMono (powerIncrement β) := by
  intro a b hab
  have hf := strictConvexOn_rpow hβ
  by_cases hab1 : a + 1 = b
  · subst b
    have hs := hf.slope_strict_mono_adjacent
      (x := (a : ℝ)) (y := ((a + 1 : ℕ) : ℝ))
      (z := ((a + 1 + 1 : ℕ) : ℝ))
      (by simp only [Set.mem_Ici]; positivity)
      (by simp only [Set.mem_Ici]; positivity) (by norm_num) (by norm_num)
    norm_num [powerIncrement, Nat.cast_add, Nat.cast_one] at hs ⊢
    exact hs
  · have habgap : a + 1 < b := by omega
    have h₁ := hf.slope_strict_mono_adjacent
      (x := (a : ℝ)) (y := ((a + 1 : ℕ) : ℝ)) (z := (b : ℝ))
      (by simp only [Set.mem_Ici]; positivity)
      (by simp only [Set.mem_Ici]; positivity)
      (by norm_num) (by exact_mod_cast habgap)
    have h₂ := hf.slope_strict_mono_adjacent
      (x := ((a + 1 : ℕ) : ℝ)) (y := (b : ℝ)) (z := ((b + 1 : ℕ) : ℝ))
      (by simp only [Set.mem_Ici]; positivity)
      (by simp only [Set.mem_Ici]; positivity)
      (by exact_mod_cast habgap) (by norm_num)
    simp only [powerIncrement]
    norm_num [Nat.cast_add, Nat.cast_one] at h₁ h₂ ⊢
    exact h₁.trans h₂

def tuplePowerValuation (β : ℝ) {D : ℕ} (s : Fin D → ℕ) : ℝ :=
  ∑ i, (s i : ℝ) ^ β

lemma tuplePowerValuation_smoothTuple_lt {β : ℝ} (hβ : 1 < β)
    {D : ℕ} (s : Fin D → ℕ) {lo hi : Fin D} (hne : lo ≠ hi)
    (hgap : s lo + 1 < s hi) :
    tuplePowerValuation β (smoothTuple s lo hi) < tuplePowerValuation β s := by
  classical
  rw [tuplePowerValuation, tuplePowerValuation]
  rw [sum_comp_smoothTuple s hne (fun n => (n : ℝ) ^ β),
    sum_eq_two_add_rest (fun i => (s i : ℝ) ^ β) hne]
  have hhi : 0 < s hi := by omega
  have hinc := powerIncrement_strictMono hβ (show s lo < s hi - 1 by omega)
  dsimp [powerIncrement] at hinc
  have hsub : (s hi - 1 : ℕ) + 1 = s hi := Nat.sub_add_cancel hhi
  have hcast : (((s hi - 1 : ℕ) + 1 : ℕ) : ℝ) = (s hi : ℝ) := by
    exact_mod_cast hsub
  rw [hcast] at hinc
  push_cast at hinc ⊢
  linarith

lemma exists_boundaryShell_of_power_sum_bounds {β : ℝ} {D q K C : ℕ}
    (hβ : 1 < β) (hD : 0 < D) (hKC : C < K)
    (s : Fin D → ℕ)
    (hsumLower : D * q ≤ ∑ i, s i)
    (hsumUpper : ∑ i, s i ≤ D * q + C)
    (hout : ¬ tupleInWindow q K s) :
    ∃ t : Fin D → ℕ,
      ∑ i, t i = ∑ i, s i ∧
      tupleInWindow q (K + 1) t ∧
      ¬ tupleInWindow q K t ∧
      tuplePowerValuation β t ≤ tuplePowerValuation β s := by
  classical
  induction hE : tupleEnergy s using Nat.strong_induction_on generalizing s with
  | h E ih =>
      by_cases hshell : tupleInWindow q (K + 1) s
      · exact ⟨s, rfl, hshell, hout, le_rfl⟩
      · have hbad : ∃ i, s i + (K + 1) < q ∨ q + (K + 1) < s i := by
          rw [tupleInWindow] at hshell
          obtain ⟨i, hi⟩ := not_forall.mp hshell
          refine ⟨i, ?_⟩
          by_cases hlo : q ≤ s i + (K + 1)
          · right
            have hhi : ¬ s i ≤ q + (K + 1) := fun h => hi ⟨hlo, h⟩
            omega
          · left
            omega
        obtain ⟨i, hiLow | hiHigh⟩ := hbad
        · have huniv : (Finset.univ : Finset (Fin D)).Nonempty := by
            obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp hD
            exact ⟨i₀, Finset.mem_univ i₀⟩
          have hconst : (∑ _j : Fin D, q) ≤ ∑ j, s j := by
            simpa using hsumLower
          obtain ⟨j, _hjmem, hj⟩ := Finset.exists_le_of_sum_le huniv hconst
          have hne : i ≠ j := by
            intro hij
            subst j
            omega
          let s' := smoothTuple s i j
          have hjpos : 0 < s j := by omega
          have hsum : ∑ k, s' k = ∑ k, s k := by
            exact sum_smoothTuple s hne hjpos
          have hgap : s i + 1 < s j := by omega
          have henergy : tupleEnergy s' < E := by
            rw [← hE]
            exact tupleEnergy_smoothTuple_lt s hne hgap
          have hout' : ¬ tupleInWindow q K s' := by
            intro hin
            have hlo := (hin i).1
            change q ≤ smoothTuple s i j i + K at hlo
            rw [smoothTuple_apply_lo s] at hlo
            omega
          have hval : tuplePowerValuation β s' < tuplePowerValuation β s := by
            exact tuplePowerValuation_smoothTuple_lt hβ s hne hgap
          obtain ⟨t, htsum, htwide, htout, htval⟩ :=
            ih (tupleEnergy s') henergy s'
              (by rw [hsum]; exact hsumLower)
              (by rw [hsum]; exact hsumUpper) hout' rfl
          exact ⟨t, htsum.trans hsum, htwide, htout, htval.trans hval.le⟩

        · have huniv : (Finset.univ : Finset (Fin D)).Nonempty := by
            obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp hD
            exact ⟨i₀, Finset.mem_univ i₀⟩
          have hsumConst : (∑ j, s j) ≤ ∑ _j : Fin D, (q + C) := by
            calc
              ∑ j, s j ≤ D * q + C := hsumUpper
              _ ≤ D * (q + C) := by nlinarith
              _ = ∑ _j : Fin D, (q + C) := by simp [Nat.mul_add]
          obtain ⟨j, _hjmem, hj⟩ := Finset.exists_le_of_sum_le huniv hsumConst
          have hne : j ≠ i := by
            intro hij
            subst j
            omega
          let s' := smoothTuple s j i
          have hipos : 0 < s i := by omega
          have hsum : ∑ k, s' k = ∑ k, s k := by
            exact sum_smoothTuple s hne hipos
          have hgap : s j + 1 < s i := by omega
          have henergy : tupleEnergy s' < E := by
            rw [← hE]
            exact tupleEnergy_smoothTuple_lt s hne hgap
          have hout' : ¬ tupleInWindow q K s' := by
            intro hin
            have hhi := (hin i).2
            change smoothTuple s j i i ≤ q + K at hhi
            rw [smoothTuple_apply_hi s hne] at hhi
            omega
          have hval : tuplePowerValuation β s' < tuplePowerValuation β s := by
            exact tuplePowerValuation_smoothTuple_lt hβ s hne hgap
          obtain ⟨t, htsum, htwide, htout, htval⟩ :=
            ih (tupleEnergy s') henergy s'
              (by rw [hsum]; exact hsumLower)
              (by rw [hsum]; exact hsumUpper) hout' rfl
          exact ⟨t, htsum.trans hsum, htwide, htout, htval.trans hval.le⟩

lemma polynomialPowerFiniteDifference_tupleDifference {β x : ℝ} {D : ℕ}
    (u v : Fin D → ℕ) :
    polynomialPowerFiniteDifference β (tupleDifference u v) x =
      (∑ i, (x + u i) ^ β) - ∑ i, (x + v i) ^ β := by
  classical
  rw [polynomialPowerFiniteDifference, tupleDifference, Finsupp.sum_sub_index]
  · have hsum (w : Fin D → ℕ) :
        (∑ i, Finsupp.single (w i) (1 : ℝ)).sum
            (fun r a => a * (x + r) ^ β) = ∑ i, (x + w i) ^ β := by
      rw [← Finsupp.sum_finsetSum_index (s := Finset.univ)
        (g := fun i => Finsupp.single (w i) (1 : ℝ))
        (h := fun r a => a * (x + r) ^ β)]
      · simp
      · intro a
        simp
      · intro a b₁ b₂
        ring
    rw [hsum u, hsum v]
  · intro a b₁ b₂
    ring

lemma eventually_const_mul_log_lt_polynomialPowerFiniteDifference_of_pos
    {β : ℝ} (hβ : 2 < β) (d : ℕ →₀ ℝ) (j : ℕ) (hj : j ≤ 2)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : 0 < stretchedMoment d j) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop,
      A * Real.log x < polynomialPowerFiniteDifference β d x := by
  have hjcast : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  have hjβ : (j : ℝ) < β := hjcast.trans_lt hβ
  have hpochPos : 0 < (descPochhammer ℝ j).eval β := by
    apply descPochhammer_pos
    show (j : ℝ) - 1 < β
    linarith
  have habs := eventually_const_mul_log_lt_abs_polynomialPowerFiniteDifference
    d j hcancel hmoment.ne' hjβ hA
  have hequiv := polynomialPowerFiniteDifference_isEquivalent d j hcancel hmoment.ne' hpochPos.ne'
  have hc : 0 < polynomialPowerDifferenceCoefficient β d j := by
    rw [polynomialPowerDifferenceCoefficient]
    exact div_pos (mul_pos hmoment hpochPos) (by positivity)
  have hlead : ∀ᶠ x : ℝ in atTop,
      0 < polynomialPowerDifferenceCoefficient β d j * x ^ (β - j) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hc (Real.rpow_pos_of_pos hx _)
  have hpos := hequiv.eventually_pos hlead
  filter_upwards [habs, hpos] with x hx hxp
  rwa [abs_of_pos hxp] at hx

lemma boundaryOffsetCandidate_eventually_const_mul_log_power_gap
    {β : ℝ} (hβ : 2 < β) {A : ℝ} (hA : 0 < A)
    {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2)
    (u : Fin D → Fin (2 * L + 1)) (hu : boundaryOffsetCandidate δ u) :
    ∀ᶠ x : ℝ in atTop, A * Real.log x <
      polynomialPowerFiniteDifference β
        (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) x := by
  let d := tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)
  have hm0 : stretchedMoment d 0 = 0 := by
    dsimp [d]
    rw [stretchedMoment_tupleDifference]
    simp
  have hm1nn : 0 ≤ stretchedMoment d 1 := by
    dsimp [d]
    exact boundaryOffsetCandidate_moment_one_nonneg δ u hu
  rcases hm1nn.eq_or_lt with hm1 | hm1
  · have hm2 : 0 < stretchedMoment d 2 := by
      dsimp [d]
      exact boundaryOffsetCandidate_moment_two_pos_of_moment_one_zero
        δ u hu hLsq (by simpa [d] using hm1.symm)
    exact eventually_const_mul_log_lt_polynomialPowerFiniteDifference_of_pos
      hβ d 2 (by omega)
        (by
          intro k hk
          interval_cases k
          · exact hm0
          · exact hm1.symm) hm2 hA
  · exact eventually_const_mul_log_lt_polynomialPowerFiniteDifference_of_pos
      hβ d 1 (by omega) (by intro k hk; interval_cases k; exact hm0) hm1 hA

lemma boundaryOffsetCandidate_eventually_all_const_mul_log_power_gap
    {β : ℝ} (hβ : 2 < β) {A : ℝ} (hA : 0 < A)
    {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2) :
    ∀ᶠ x : ℝ in atTop, ∀ u : Fin D → Fin (2 * L + 1),
      boundaryOffsetCandidate δ u → A * Real.log x <
        polynomialPowerFiniteDifference β
          (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) x := by
  rw [Filter.eventually_all]
  intro u
  by_cases hu : boundaryOffsetCandidate δ u
  · exact (boundaryOffsetCandidate_eventually_const_mul_log_power_gap
      hβ hA δ hLsq u hu).mono fun x hx _ => hx
  · exact Filter.Eventually.of_forall fun _ hx => (hu hx).elim

lemma tuplePowerValuation_shellOffset {β : ℝ} {D q L : ℕ}
    (t : Fin D → ℕ) (hLq : L ≤ q) (hwide : tupleInWindow q L t) :
    tuplePowerValuation β t =
      ∑ i, (((q - L : ℕ) + (shellOffset t hLq hwide i : ℕ) : ℕ) : ℝ) ^ β := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact_mod_cast (shellOffset_add_base t hLq hwide i).symm

lemma tuplePowerValuation_witness_as_offset {β : ℝ} {D q L : ℕ}
    (δ : Fin D → ℕ) (hLq : L ≤ q) :
    tuplePowerValuation β (fun i => q + δ i) =
      ∑ i, (((q - L : ℕ) + (δ i + L) : ℕ) : ℝ) ^ β := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hnat : q - L + (δ i + L) = q + δ i := by omega
  exact_mod_cast hnat.symm

lemma polynomialPowerFiniteDifference_shellOffset_eq {β : ℝ} {D q L : ℕ}
    (δ t : Fin D → ℕ) (hLq : L ≤ q) (hwide : tupleInWindow q L t) :
    polynomialPowerFiniteDifference β
        (tupleDifference (fun i => (shellOffset t hLq hwide i : ℕ))
          (fun i => δ i + L)) ((q : ℝ) - L) =
      tuplePowerValuation β t - tuplePowerValuation β (fun i => q + δ i) := by
  rw [polynomialPowerFiniteDifference_tupleDifference]
  rw [tuplePowerValuation_shellOffset t hLq hwide,
    tuplePowerValuation_witness_as_offset δ hLq]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    rw [Nat.cast_sub hLq]
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    rw [Nat.cast_sub hLq]

lemma eventually_log_natCast_le_two_mul_log_natCast_sub (L : ℕ) :
    ∀ᶠ q : ℕ in atTop,
      Real.log (q : ℝ) ≤ 2 * Real.log ((q : ℝ) - L) := by
  filter_upwards [eventually_ge_atTop (2 * L + 4)] with q hq
  have hLq : L ≤ q := by omega
  have hy2 : 2 ≤ q - L := by omega
  have hqsplit : q - L + L = q := Nat.sub_add_cancel hLq
  have hquadNat : q ≤ (q - L) ^ 2 := by nlinarith
  have hquad : (q : ℝ) ≤ ((q : ℝ) - L) ^ 2 := by
    have hcast : (q : ℝ) ≤ ((q - L : ℕ) : ℝ) ^ 2 := by exact_mod_cast hquadNat
    simpa [Nat.cast_sub hLq] using hcast
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hypos : (0 : ℝ) < (q : ℝ) - L := by
    rw [← Nat.cast_sub hLq]
    exact_mod_cast (show 0 < q - L by omega)
  calc
    Real.log (q : ℝ) ≤ Real.log (((q : ℝ) - L) ^ 2) :=
      Real.log_le_log hqpos hquad
    _ = 2 * Real.log ((q : ℝ) - L) := by rw [Real.log_pow]; norm_num

/-- For a power profile of exponent greater than two, every tuple whose valuation is within an
arbitrary prescribed logarithmic error of a fixed-offset witness is eventually confined to one
fixed coordinate window. -/
theorem exists_eventually_bounded_powerNearMinimizer {β : ℝ} (hβ : 2 < β)
    {D : ℕ} (hD : 0 < D) (δ : Fin D → ℕ) (C A : ℕ) :
    ∃ K : ℕ, ∀ᶠ q : ℕ in atTop,
      ∀ s : Fin D → ℕ,
        (D * q + (∑ i, δ i) ≤ ∑ i, s i ∧
          (∑ i, s i) ≤ D * q + (∑ i, δ i) + C) →
        tuplePowerValuation β s <
          tuplePowerValuation β (fun i => q + δ i) +
            (A : ℝ) * Real.log ((q : ℝ) + 2) →
        tupleInWindow q K s := by
  classical
  let Aδ := ∑ i, δ i
  let Sδ := ∑ i, (δ i) ^ 2
  let K := C + Aδ + Sδ + 1
  let L := K + 1
  let G : ℕ := 4 * A + 1
  have hCtotK : Aδ + C < K := by
    dsimp [K]
    omega
  have hLpos : 0 < L := by dsimp [L, K]; omega
  have hSltL : Sδ < L := by dsimp [L, K]; omega
  have hSltLsq : Sδ < L ^ 2 := by
    exact hSltL.trans_le (by nlinarith : L ≤ L ^ 2)
  have hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2 := by
    have hcast : (Sδ : ℝ) < (L : ℝ) ^ 2 := by exact_mod_cast hSltLsq
    simpa [Sδ] using hcast
  have hGpos : (0 : ℝ) < G := by dsimp [G]; positivity
  have hgapReal := boundaryOffsetCandidate_eventually_all_const_mul_log_power_gap
    hβ hGpos δ hLsq
  have hbaseT : Tendsto (fun q : ℕ => (q : ℝ) - L) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(L : ℝ)) tendsto_natCast_atTop_atTop
  have hgapNat : ∀ᶠ q : ℕ in atTop, ∀ u : Fin D → Fin (2 * L + 1),
      boundaryOffsetCandidate δ u → (G : ℝ) * Real.log ((q : ℝ) - L) <
        polynomialPowerFiniteDifference β
          (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L))
          ((q : ℝ) - L) := hbaseT.eventually hgapReal
  have hlogSub := eventually_log_natCast_le_two_mul_log_natCast_sub L
  have hlogAdd := eventually_log_nat_add_const_le_two_mul_log_nat 0
  refine ⟨K, ?_⟩
  filter_upwards [hgapNat, hlogSub, hlogAdd,
    eventually_ge_atTop (max (2 * L + 4) 2)] with q hgap hlogSubq hlogAddq hq
  intro s hsBounds hnear
  by_contra hout
  have hLq : L ≤ q := by omega
  have hsumLower0 : D * q ≤ ∑ i, s i := by
    exact (Nat.le_add_right _ Aδ).trans (by simpa [Aδ] using hsBounds.1)
  have hsumUpper0 : (∑ i, s i) ≤ D * q + (Aδ + C) := by
    simpa [Aδ, Nat.add_assoc] using hsBounds.2
  obtain ⟨t, htsum, htwide, htout, htval⟩ :=
    exists_boundaryShell_of_power_sum_bounds (by linarith : 1 < β) hD hCtotK s
      hsumLower0 hsumUpper0 hout
  have htsumLower : D * q + (∑ i, δ i) ≤ ∑ i, t i := by
    rw [htsum]
    exact hsBounds.1
  have hcand := shellOffset_boundaryCandidate δ t hLq htwide htout htsumLower
  have hgap' := hgap (shellOffset t hLq htwide) hcand
  rw [polynomialPowerFiniteDifference_shellOffset_eq δ t hLq htwide] at hgap'
  have hbaseLogPos : 0 < Real.log ((q : ℝ) - L) := by
    apply Real.log_pos
    rw [← Nat.cast_sub hLq]
    exact_mod_cast (show 1 < q - L by omega)
  have hlogAddq' : Real.log ((q : ℝ) + 2) ≤ 2 * Real.log (q : ℝ) := by
    simpa only [Nat.zero_eq, Nat.add_zero] using hlogAddq
  have hlogScale : (A : ℝ) * Real.log ((q : ℝ) + 2) <
      (G : ℝ) * Real.log ((q : ℝ) - L) := by
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have h₁ := mul_le_mul_of_nonneg_left hlogAddq' hA0
    have h₂ := mul_le_mul_of_nonneg_left hlogSubq (show (0 : ℝ) ≤ 2 * A by positivity)
    dsimp [G]
    push_cast
    nlinarith
  have hwitGap : tuplePowerValuation β t -
      tuplePowerValuation β (fun i => q + δ i) <
      (A : ℝ) * Real.log ((q : ℝ) + 2) := by
    linarith
  linarith

end

end GaloisForLFunctions
