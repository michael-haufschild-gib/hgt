import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.StepPacketMassAndGroundEnergy
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRobustCombDirectionsTransferToStepPackets

/-!
# RH is exact eventual positivity of every fixed comb window

The positive aperture gap pays both the block approximation error and the
Schur cross term. Crucially, the latter is charged to block means only;
the mean-zero component is already controlled by the counterterm.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-- The block projection is orthogonal for coefficient mass. -/
theorem sum_sq_eq_blockMean_add_residual {B : ℕ} (hB : 0 < B) (N J : ℕ) (c : ℕ → ℝ) :
    ∑ n ∈ Ioc N (N + B * J), c n ^ 2 =
      (∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) ^ 2) +
        ∑ n ∈ Ioc N (N + B * J), (c n - blockMean N B J c (blockIndex N B n)) ^ 2 := by
  have horth := sum_blockFunction_mul_eq_zero N B (Ioc N (N + B * J))
    (blockMean N B J c) (fun n => c n - blockMean N B J c (blockIndex N B n))
    (sum_filter_sub_blockMean hB N J c)
  have he : ∑ n ∈ Ioc N (N + B * J), c n ^ 2 =
      (∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) ^ 2) +
      2 * (∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) *
        (c n - blockMean N B J c (blockIndex N B n))) +
      ∑ n ∈ Ioc N (N + B * J), (c n - blockMean N B J c (blockIndex N B n)) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  simpa only [horth, mul_zero, add_zero] using he

/-- Block reduction can reserve any fixed residual mass floor while
charging its Schur error only to block means. -/
theorem exists_blockSize_combForm_ge_blockMean_with_residual
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) (κ : ℝ) :
    ∃ R : ℕ, 0 < R ∧ ∀ N J : ℕ, R ≤ N → N + N / R * J ≤ Q * N → ∀ c : ℕ → ℝ,
      combForm (Ioc N (N + N / R * J))
          (fun n => blockMean N (N / R) J c (blockIndex N (N / R) n)) -
        ε * ∑ n ∈ Ioc N (N + N / R * J),
          blockMean N (N / R) J c (blockIndex N (N / R) n) ^ 2 +
        κ * ∑ n ∈ Ioc N (N + N / R * J),
          (c n - blockMean N (N / R) J c (blockIndex N (N / R) n)) ^ 2 ≤
      combForm (Ioc N (N + N / R * J)) c := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi) +
      crossConstant Q ^ 2 / ε + κ := ⟨_, rfl⟩
  have hR : 0 < ⌈Real.exp E⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos E)
  refine ⟨⌈Real.exp E⌉₊, hR, ?_⟩
  intro N J hRN hQ c
  have hRE : E ≤ Real.log (⌈Real.exp E⌉₊ : ℝ) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast hR)]
    exact Nat.le_ceil _
  have hmargin := log_sub_row_ge (M := N / ⌈Real.exp E⌉₊ * J) hR hRN hQ
  have hB : 0 < N / ⌈Real.exp E⌉₊ := Nat.div_pos hRN hR
  let σ := blockMean N (N / ⌈Real.exp E⌉₊) J c
  let z := fun n => c n - σ (blockIndex N (N / ⌈Real.exp E⌉₊) n)
  have hzero := sum_filter_sub_blockMean hB N J c
  have hN : 0 < N := hB.trans_le (Nat.div_le_self _ _)
  have hC := crossConstant_pos Q
  have hz0 : 0 ≤ ∑ n ∈ Ioc N (N + N / ⌈Real.exp E⌉₊ * J), z n ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hμ : crossConstant Q ^ 2 / ε + κ ≤ Real.log ((N : ℝ) / (2 * Real.pi)) -
      (harm (2 * (N / ⌈Real.exp E⌉₊)) + 2 +
        ((N / ⌈Real.exp E⌉₊ * J : ℕ) : ℝ) / (4 * N) + 2 * chebyshev Q) := by
    linarith only [hmargin, hRE, hE]
  have hco : (crossConstant Q ^ 2 / ε + κ) *
      ∑ n ∈ Ioc N (N + N / ⌈Real.exp E⌉₊ * J), z n ^ 2 ≤
        combForm (Ioc N (N + N / ⌈Real.exp E⌉₊ * J)) z := by
    have hpair := combPairing_le_of_blockSum_eq_zero hN hB hQ (Finset.Subset.refl _) z hzero
    rw [combForm, degTwo_eq_zero_of_blockSum_eq_zero N _ _ z hzero,
      mul_zero, mul_zero, zero_sub]
    nlinarith only [hpair, mul_le_mul_of_nonneg_right hμ hz0]
  have hcross := two_mul_abs_formBilin_le hB (Nat.div_le_self _ _) hQ σ z hzero
    (p := ε / crossConstant Q) (q := crossConstant Q / ε) (div_pos hε hC)
    (by rw [div_mul_div_comm, mul_comm ε, div_self (mul_pos hC hε).ne'])
  rw [cross_weights hC.ne'] at hcross
  have he : (fun n => blockMean N (N / ⌈Real.exp E⌉₊) J c
      (blockIndex N (N / ⌈Real.exp E⌉₊) n) +
      (c n - blockMean N (N / ⌈Real.exp E⌉₊) J c
        (blockIndex N (N / ⌈Real.exp E⌉₊) n))) = c := by
    funext n
    ring
  conv_rhs => rw [← he, combForm_add]
  have hneg := neg_abs_le (formBilin (Ioc N (N + N / ⌈Real.exp E⌉₊ * J))
    (fun n => σ (blockIndex N (N / ⌈Real.exp E⌉₊) n)) z)
  change combForm _ (fun n => σ (blockIndex _ _ n)) - ε * _ + κ * _ ≤ _
  linarith only [hco, hcross, hneg]

/-- A positive continuum mass floor becomes a positive block-constant
comb floor on all sufficiently fine meshes. -/
theorem eventually_combForm_blockFunction_mass_floor {R J Q : ℕ}
    (hR : 1 ≤ R) (hQ : R + J ≤ Q * R) {δ : ℝ} (hδ : 0 < δ)
    (hfloor : ∀ σ : ℕ → ℝ, δ * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ)) :
    ∀ᶠ B : ℕ in atTop, ∀ σ : ℕ → ℝ,
      (δ / 2) * ∑ n ∈ Ioc (R * B) (R * B + B * J), σ (blockIndex (R * B) B n) ^ 2 ≤
        combForm (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) := by
  filter_upwards [eventually_packetForm_stepPacket_le_combForm hR hQ (half_pos hδ),
    eventually_ge_atTop 1] with B hB hB1 σ
  have h := hB σ
  rw [sum_blockFunction_sq (by omega) σ] at h ⊢
  have hm := mul_le_mul_of_nonneg_left (hfloor σ) (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  nlinarith only [h, hm]

/-- Under RH every fixed comb window has a uniform positive mass floor
at all sufficiently large scales. -/
theorem exists_eventual_combForm_positive_mass_floor (hRH : RiemannHypothesis) (K : ℕ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      γ * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 ≤ combForm (Ioc N (N + 3 * K * N)) c := by
  obtain ⟨δ, hδ, hfloor⟩ := exists_uniform_stepPacket_mass_floor_of_riemannHypothesis
    hRH (Q := 6 * K + 2) (by omega)
  obtain ⟨R, hR, hred⟩ :=
    exists_blockSize_combForm_ge_blockMean_with_residual (6 * K + 2)
      (show 0 < δ / 4 by positivity) (δ / 4)
  have hQ : R + (6 * K + 1) * R ≤ (6 * K + 2) * R := le_of_eq (by ring)
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp
    (eventually_combForm_blockFunction_mass_floor hR hQ hδ (hfloor R _ hR hQ))
  refine ⟨δ / 4, by positivity, eventually_atTop.mpr ⟨R * (B₀ + 1), fun N hN c => ?_⟩⟩
  have hB1 : B₀ + 1 ≤ N / R := (Nat.le_div_iff_mul_le hR).mpr (by rw [Nat.mul_comm]; exact hN)
  have hBpos : 0 < N / R := by omega
  have hNle : R * (N / R) ≤ N := Nat.mul_div_le N R
  have hNlt : N ≤ R * (N / R) + R := by
    have := Nat.lt_mul_div_succ N hR
    linarith
  have hRB : R ≤ R * (N / R) := Nat.le_mul_of_pos_right R hBpos
  have hsub : Ioc N (N + 3 * K * N) ⊆
      Ioc (R * (N / R)) (R * (N / R) + N / R * ((6 * K + 1) * R)) := by
    refine Finset.Ioc_subset_Ioc hNle ?_
    have h1 := Nat.mul_le_mul_left (3 * K + 1) hNlt
    have h2 := Nat.mul_le_mul_left (3 * K + 1) hRB
    linarith
  have hform : combForm (Ioc (R * (N / R)) (R * (N / R) + N / R * ((6 * K + 1) * R)))
        (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0) =
      combForm (Ioc N (N + 3 * K * N)) c :=
    (combForm_of_subset hsub fun n _ hn => if_neg hn).trans
      (combForm_congr fun n hn => if_pos hn)
  have hdiv : R * (N / R) / R = N / R := Nat.mul_div_cancel_left (N / R) hR
  have h1 := hred (R * (N / R)) ((6 * K + 1) * R) hRB
    (by rw [hdiv]; exact le_of_eq (by ring))
    (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0)
  rw [hdiv, hform] at h1
  have h2 := hB₀ (N / R) (by omega)
    (blockMean (R * (N / R)) (N / R) ((6 * K + 1) * R)
      (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0))
  have hsq : ∑ n ∈ Ioc (R * (N / R)) (R * (N / R) + N / R * ((6 * K + 1) * R)),
        (if n ∈ Ioc N (N + 3 * K * N) then c n else 0) ^ 2 =
      ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 := by
    rw [← Finset.sum_subset hsub fun n _ hn => by rw [if_neg hn]; ring]
    exact Finset.sum_congr rfl fun n hn => by rw [if_pos hn]
  have hmass := sum_sq_eq_blockMean_add_residual hBpos (R * (N / R)) ((6 * K + 1) * R)
    (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0)
  rw [hsq] at hmass
  rw [hmass]
  nlinarith only [h1, h2]

/-- Exact eventual sign follows from the positive mass floor. -/
theorem eventually_combForm_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ, 0 ≤ combForm (Ioc N (N + 3 * K * N)) c := by
  obtain ⟨γ, hγ, hev⟩ := exists_eventual_combForm_positive_mass_floor hRH K
  filter_upwards [hev] with N hN c
  exact (mul_nonneg hγ.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans (hN c)

/-- RH is equivalent to exact eventual nonnegativity of every fixed
finite comb window. -/
theorem riemannHypothesis_iff_eventually_combForm_nonneg :
    RiemannHypothesis ↔ ∀ K : ℕ, 1 ≤ K → ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      0 ≤ combForm (Ioc N (N + 3 * K * N)) c := by
  constructor
  · exact fun hRH K _ => eventually_combForm_nonneg_of_riemannHypothesis hRH K
  · intro h
    apply riemannHypothesis_of_frequently_combForm_ge
    intro K hK η hη
    exact ((h K hK).mono fun N hN c =>
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hη.le)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans (hN c)).frequently

/-- The exact finite-scale criterion can be strengthened to a uniform
strictly positive mass floor on each fixed window. -/
theorem riemannHypothesis_iff_eventual_combForm_positive_mass_floor :
    RiemannHypothesis ↔ ∀ K : ℕ, 1 ≤ K → ∃ γ : ℝ, 0 < γ ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
        γ * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 ≤ combForm (Ioc N (N + 3 * K * N)) c := by
  constructor
  · exact fun hRH K _ => exists_eventual_combForm_positive_mass_floor hRH K
  · intro h
    apply riemannHypothesis_iff_eventually_combForm_nonneg.mpr
    intro K hK
    obtain ⟨γ, hγ, hev⟩ := h K hK
    filter_upwards [hev] with N hN c
    exact (mul_nonneg hγ.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans (hN c)

/-- Extending by zero preserves both the comb form and coefficient mass. -/
theorem combForm_mass_floor_of_subset {S T : Finset ℕ} (hST : S ⊆ T) {γ : ℝ}
    (hT : ∀ c : ℕ → ℝ, γ * ∑ n ∈ T, c n ^ 2 ≤ combForm T c) (c : ℕ → ℝ) :
    γ * ∑ n ∈ S, c n ^ 2 ≤ combForm S c := by
  have h := hT (fun n => if n ∈ S then c n else 0)
  have hform : combForm T (fun n => if n ∈ S then c n else 0) = combForm S c :=
    (combForm_of_subset hST fun n _ hn => if_neg hn).trans
      (combForm_congr fun n hn => if_pos hn)
  have hmass : ∑ n ∈ T, (if n ∈ S then c n else 0) ^ 2 = ∑ n ∈ S, c n ^ 2 := by
    rw [← Finset.sum_subset hST fun n _ hn => by rw [if_neg hn]; ring]
    exact Finset.sum_congr rfl fun n hn => by rw [if_pos hn]
  rwa [hform, hmass] at h

/-- The positive floor holds on every fixed integer-ratio window. -/
theorem exists_eventual_ratioWindow_positive_mass_floor (hRH : RiemannHypothesis) (Q : ℕ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      γ * ∑ n ∈ Ioc N (Q * N), c n ^ 2 ≤ combForm (Ioc N (Q * N)) c := by
  obtain ⟨γ, hγ, hev⟩ := exists_eventual_combForm_positive_mass_floor hRH Q
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with N hN c
  apply combForm_mass_floor_of_subset (T := Ioc N (N + 3 * Q * N)) _ hN c
  apply Finset.Ioc_subset_Ioc le_rfl
  have h := Nat.mul_le_mul_right N (show Q ≤ 3 * Q + 1 by omega)
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using h

/-- RH iff all sufficiently late finite combs on each fixed ratio window
have a uniform positive smallest eigenvalue in coefficient mass. -/
theorem riemannHypothesis_iff_ratioWindow_positive_mass_floor :
    RiemannHypothesis ↔ ∀ Q : ℕ, 2 ≤ Q → ∃ γ : ℝ, 0 < γ ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
        γ * ∑ n ∈ Ioc N (Q * N), c n ^ 2 ≤ combForm (Ioc N (Q * N)) c := by
  constructor
  · exact fun hRH Q _ => exists_eventual_ratioWindow_positive_mass_floor hRH Q
  · intro h
    apply riemannHypothesis_iff_eventual_combForm_positive_mass_floor.mpr
    intro K hK
    obtain ⟨γ, hγ, hev⟩ := h (1 + 3 * K) (by omega)
    exact ⟨γ, hγ, by simpa only [Nat.add_mul, one_mul] using hev⟩

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
