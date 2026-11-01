import GaloisForLFunctions.TransThresholdPairCorrelation.StabilizerTaperTransport
import GaloisForLFunctions.RHTower.ThetaIntegerCutoffMovingPacket
import GaloisForLFunctions.HTGeometry.RiemannSumCell
import GaloisForLFunctions.RHTower.Sieve.LevinsonGcdFormBound

/-!
# Odd-base quadrature for primitive spatial samples

The actual standard taper and a fixed smooth height profile give an odd-lattice
quadrature error `4T/c + C L`. Support vanishing identifies the height cutoff
with the taper cutoff exactly. Summing over primitive frequencies and odd
conductors costs `K T (1 + L + log ((Q+1)T)) (1 + log Q)` by the harmonic
frequency bound and the existing totient-ratio first moment.
-/

noncomputable section
open MeasureTheory Real Filter Topology Finset intervalIntegral
open Zeta23
open RHTower.Sieve
namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem abs_standard_taper_le {ρ : ℝ → ℝ} {L w : ℝ}
    (hρ : TaperProfile ρ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    |Taper.g ρ L w y| ≤ L := by
  have hL : 0 ≤ L := (by linarith only [hw] : 0 ≤ 2 * w).trans hwL
  rw [abs_of_nonneg (Taper.g_nonneg hρ hw hwL y)]
  exact ((Taper.g_le_Aphi hρ hw hwL y).trans (Taper.Aphi_le hρ hw hwL y)).trans
    (max_le (sub_le_self L (abs_nonneg y)) hL)

private theorem profile_norm_le_one {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) (T x : ℝ) : ‖profileΩ u T x‖ ≤ 1 := by
  have h0 : 0 ≤ profileΩ u T x := pow_nonneg (profileU_mem hu T x).1 4
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact pow_le_one₀ (profileU_mem hu T x).1 (profileU_mem hu T x).2

private theorem spatial_product_lipschitz {ε L w T c ℓ : ℝ} {u ρ : ℝ → ℝ}
    (hu : WindowProfile ε u) (hρ : TaperProfile ρ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (hL : 0 ≤ L) (hT : 0 < T) (hc : 0 < c) (hℓ : 0 ≤ ℓ)
    (hLip : ∀ s t, |u s - u t| ≤ ℓ * |s - t|) :
    LipschitzOnWith ⟨2 + 4 * L * ℓ * c / T, by positivity⟩
      (fun x : ℝ => Taper.g ρ L w (Real.log x) * profileΩ u T (c * x)) (Set.Ici 1) := by
  have hg : LipschitzOnWith 2 (fun x : ℝ => Taper.g ρ L w (Real.log x)) (Set.Ici 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hl := _root_.HTGeometry.lipschitzOnWith_log_Ici_one.dist_le_mul x hx y hy
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hl
    change |Taper.g ρ L w (Real.log x) - Taper.g ρ L w (Real.log y)| ≤ 2 * |x - y|
    exact (abs_taperAutocorrelation_sub_le hρ hw hwL _ _).trans
      (mul_le_mul_of_nonneg_left hl (by norm_num))
  let KΩ : NNReal := ⟨4 * ℓ * c / T, by positivity⟩
  have hΩ : LipschitzOnWith KΩ (fun x : ℝ => profileΩ u T (c * x)) (Set.Ici 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x _ y _
    change |profileΩ u T (c * x) - profileΩ u T (c * y)| ≤ (4 * ℓ * c / T) * |x - y|
    calc
      _ ≤ (4 * ℓ / T) * |c * x - c * y| := abs_profileΩ_sub_le hu hLip hT _ _
      _ = _ := by rw [← mul_sub, abs_mul, abs_of_pos hc]; ring
  have hp := _root_.HTGeometry.lipschitzOnWith_mul_of_bound hg hΩ
    (fun x _ => by rw [Real.norm_eq_abs]; exact abs_standard_taper_le hρ hw hwL (Real.log x))
    (fun x _ => profile_norm_le_one hu T (c * x))
  have hK : Real.toNNReal L * KΩ + Real.toNNReal (1 : ℝ) * 2 =
      (⟨2 + 4 * L * ℓ * c / T, by positivity⟩ : NNReal) := by
    apply NNReal.eq
    change (Real.toNNReal L : ℝ) * (4 * ℓ * c / T) + (Real.toNNReal (1 : ℝ) : ℝ) * 2 =
      2 + 4 * L * ℓ * c / T
    rw [Real.coe_toNNReal L hL, Real.coe_toNNReal 1 (by norm_num)]
    ring
  rw [hK] at hp
  exact hp

/-- Error of the positive odd lattice against half its integral, at a cutoff
past the support of a height window scaled by the positive frequency `c`. -/
def oddSpatialQuadratureError (Ω g : ℝ → ℝ) (T c : ℝ) : ℝ :=
  (∑ r ∈ range ⌈T / c⌉₊,
    g (Real.log (1 + 2 * ((r : ℝ) + 1))) * Ω (c * (1 + 2 * ((r : ℝ) + 1)))) -
    (1 / 2 : ℝ) * ∫ x in (1 : ℝ)..(1 + 2 * (⌈T / c⌉₊ : ℝ)), g (Real.log x) * Ω (c * x)

/-- Fixed smooth profiles admit an odd-lattice quadrature error
`4T/c + C L`, uniformly over all admissible standard tapers and `0<c≤2T`. -/
theorem WindowProfile.exists_oddSpatialQuadratureError_le {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ → ℝ) (L w T c : ℝ),
      TaperProfile ρ → 0 < w → 2 * w ≤ L → 1 ≤ L → 1 ≤ T → 0 < c → c ≤ 2 * T →
      |oddSpatialQuadratureError (profileΩ u T) (Taper.g ρ L w) T c| ≤ 4 * T / c + C * L := by
  obtain ⟨ℓ, hℓ, hLip⟩ := hu.exists_lipschitz
  refine ⟨4 + 24 * ℓ, by positivity, ?_⟩
  intro ρ L w T c hρ hw hwL hL hT hc hcT
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  let N : ℕ := ⌈T / c⌉₊
  let K : NNReal := ⟨2 + 4 * L * ℓ * c / T, by positivity⟩
  let F : ℝ → ℝ := fun x => Taper.g ρ L w (Real.log x) * profileΩ u T (c * x)
  have hp : LipschitzOnWith K F (Set.Ici 1) := spatial_product_lipschitz hu hρ hw hwL hL0 hT0 hc hℓ hLip
  have hf : LipschitzOnWith K (fun x : ℝ => F (1 + x)) (Set.Icc 0 (2 * N)) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have h := hp.dist_le_mul (1 + x) (by simpa only [Set.mem_Ici] using (by linarith only [hx.1] : 1 ≤ 1 + x))
      (1 + y) (by simpa only [Set.mem_Ici] using (by linarith only [hy.1] : 1 ≤ 1 + y))
    simpa only [Real.dist_eq, add_sub_add_left_eq_sub] using h
  have hq := RHTower.abs_riemannSum_sub_integral_le hf hf.continuousOn N
    (by norm_num : (0 : ℝ) ≤ 2) (le_of_eq (by ring : (N : ℝ) * 2 = 2 * N))
  have hshift : (∫ x in (0 : ℝ)..((N : ℝ) * 2), F (1 + x)) =
      ∫ x in (1 : ℝ)..(1 + 2 * N), F x := by
    simpa only [add_zero, mul_comm] using
      (intervalIntegral.integral_comp_add_left (f := F) (a := 0) (b := (N : ℝ) * 2) 1)
  have he : oddSpatialQuadratureError (profileΩ u T) (Taper.g ρ L w) T c =
      (2 * ∑ r ∈ range N, F (((r : ℝ) + 1) * 2 + 1) -
        ∫ x in (0 : ℝ)..((N : ℝ) * 2), F (1 + x)) / 2 := by
    rw [hshift]
    unfold oddSpatialQuadratureError
    dsimp only [N, F]
    have hs : (∑ r ∈ range ⌈T / c⌉₊,
        Taper.g ρ L w (Real.log (1 + 2 * ((r : ℝ) + 1))) *
          profileΩ u T (c * (1 + 2 * ((r : ℝ) + 1)))) =
        ∑ r ∈ range ⌈T / c⌉₊,
        Taper.g ρ L w (Real.log (((r : ℝ) + 1) * 2 + 1)) *
          profileΩ u T (c * (((r : ℝ) + 1) * 2 + 1)) := by
      apply sum_congr rfl
      intro r _
      rw [show 1 + 2 * ((r : ℝ) + 1) = ((r : ℝ) + 1) * 2 + 1 by ring]
    rw [hs]
    ring
  have hq' : |2 * ∑ r ∈ range N, F (((r : ℝ) + 1) * 2 + 1) -
        ∫ x in (0 : ℝ)..((N : ℝ) * 2), F (1 + x)| ≤ (K : ℝ) * N * 2^2 := by
    have hs : (∑ i ∈ range N, F (1 + ((i : ℝ) + 1) * 2)) =
        ∑ i ∈ range N, F (((i : ℝ) + 1) * 2 + 1) :=
      sum_congr rfl (fun i _ => congrArg F (add_comm 1 (((i : ℝ) + 1) * 2)))
    rw [hs] at hq
    exact hq
  have hN : (N : ℝ) ≤ T / c + 1 := (Nat.ceil_lt_add_one (div_nonneg hT0.le hc.le)).le
  have hKN := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2 * (K : ℝ) by positivity)
  have hcdiv : c / T ≤ 2 := (div_le_iff₀ hT0).mpr hcT
  have hpay := mul_le_mul_of_nonneg_left hcdiv (show 0 ≤ 8 * L * ℓ by positivity)
  rw [he, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ ((K : ℝ) * N * 2^2) / 2 := div_le_div_of_nonneg_right hq' (by norm_num)
    _ = 2 * (K : ℝ) * N := by ring
    _ ≤ 2 * (K : ℝ) * (T / c + 1) := hKN
    _ = 4 * T / c + 4 + 8 * L * ℓ + 8 * L * ℓ * (c / T) := by
      change 2 * (2 + 4 * L * ℓ * c / T) * (T / c + 1) = _
      field_simp [hc.ne', hT0.ne']
      ring
    _ ≤ 4 * T / c + (4 + 24 * ℓ) * L := by nlinarith only [hpay, hL]

private theorem standard_taper_log_eq_zero {ρ : ℝ → ℝ} {L w x : ℝ}
    (hρ : TaperProfile ρ) (hw : 0 < w) (hwL : 2 * w ≤ L) (hx : Real.exp L ≤ x) :
    Taper.g ρ L w (Real.log x) = 0 := by
  have hx0 : 0 < x := (Real.exp_pos L).trans_le hx
  have hl : L ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hu := (Taper.g_le_Aphi hρ hw hwL (Real.log x)).trans
    (Taper.Aphi_le hρ hw hwL (Real.log x))
  have hm : max (L - |Real.log x|) 0 = 0 := max_eq_right (by
    linarith only [hl, le_abs_self (Real.log x)])
  rw [hm] at hu
  exact le_antisymm hu (Taper.g_nonneg hρ hw hwL _)

private theorem profile_eq_zero_above {ε T x : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) (hT : 0 < T) (hx : 2 * T ≤ x) : profileΩ u T x = 0 := by
  have hzero : profileU u T x = 0 := profileU_eq_zero hu hT (by
    intro h
    have he : 0 < ε * T := mul_pos hu.pos hT
    linarith only [h.2, hx, he])
  simp only [profileΩ, hzero, zero_pow (by norm_num : (4 : ℕ) ≠ 0)]

private theorem sum_eq_of_vanishing_tails {f : ℕ → ℝ} {N M : ℕ}
    (hN : ∀ r, N ≤ r → f r = 0) (hM : ∀ r, M ≤ r → f r = 0) :
    (∑ r ∈ range N, f r) = ∑ r ∈ range M, f r := by
  have h (K : ℕ) (hK : K ≤ max N M) (hz : ∀ r, K ≤ r → f r = 0) :
      (∑ r ∈ range K, f r) = ∑ r ∈ range (max N M), f r := by
    apply sum_subset (range_mono hK)
    intro r _ hr
    exact hz r (by simpa only [mem_range, not_lt] using hr)
  exact (h N (le_max_left _ _) hN).trans (h M (le_max_right _ _) hM).symm

private theorem integral_eq_of_vanishing_tails {F : ℝ → ℝ} {A B : ℝ}
    (hF : ContinuousOn F (Set.Ici 1)) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hzA : ∀ x, A ≤ x → F x = 0) (hzB : ∀ x, B ≤ x → F x = 0) :
    (∫ x in (1 : ℝ)..A, F x) = ∫ x in (1 : ℝ)..B, F x := by
  have hi (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : IntervalIntegrable F volume a b :=
    (hF.mono (by intro x hx; exact (le_min ha hb).trans hx.1)).intervalIntegrable
  have h (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (hz : ∀ x, a ≤ x → F x = 0) :
      (∫ x in (1 : ℝ)..a, F x) = ∫ x in (1 : ℝ)..b, F x := by
    have hzero : (∫ x in a..b, F x) = 0 := by
      calc
        _ = ∫ x in a..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le hab] at hx
          exact hz x hx.1
        _ = 0 := by simp only [intervalIntegral.integral_zero]
    have hh := intervalIntegral.integral_add_adjacent_intervals (hi 1 a le_rfl ha)
      (hi a b ha (ha.trans hab))
    simpa only [hzero, add_zero] using hh
  rcases le_total A B with hab | hba
  · exact h A B hA hab hzA
  · exact (h B A hB hba hzB).symm

/-- The auxiliary height cutoff equals the actual taper cutoff. Both the odd
sum and its integral can be extended because the complementary factors vanish. -/
theorem WindowProfile.oddSpatialQuadratureError_eq_taper_cutoff {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) {ρ : ℝ → ℝ} {L w T c : ℝ}
    (hρ : TaperProfile ρ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (hL : 0 ≤ L) (hT : 0 < T) (hc : 0 < c) :
    oddSpatialQuadratureError (profileΩ u T) (Taper.g ρ L w) T c =
      (∑ r ∈ range ((⌊Real.exp L⌋₊ - 1) / 2),
        Taper.g ρ L w (Real.log (1 + 2 * ((r : ℝ) + 1))) *
          profileΩ u T (c * (1 + 2 * ((r : ℝ) + 1)))) -
        (1 / 2 : ℝ) * ∫ x in (1 : ℝ)..Real.exp L,
          Taper.g ρ L w (Real.log x) * profileΩ u T (c * x) := by
  let F : ℝ → ℝ := fun x => Taper.g ρ L w (Real.log x) * profileΩ u T (c * x)
  let N := ⌈T / c⌉₊
  let M := (⌊Real.exp L⌋₊ - 1) / 2
  have hN : T / c ≤ (N : ℝ) := Nat.le_ceil _
  have hfreq : 2 * T ≤ c * (1 + 2 * (N : ℝ)) := by
    have hh := (div_le_iff₀ hc).mp hN
    nlinarith only [hh, hc]
  have hzN (x : ℝ) (hx : 1 + 2 * (N : ℝ) ≤ x) : F x = 0 := by
    have hh := mul_le_mul_of_nonneg_left hx hc.le
    dsimp only [F]
    rw [profile_eq_zero_above hu hT (hfreq.trans hh), mul_zero]
  have hzM (x : ℝ) (hx : Real.exp L ≤ x) : F x = 0 := by
    dsimp only [F]
    rw [standard_taper_log_eq_zero hρ hw hwL hx, zero_mul]
  have hsum : (∑ r ∈ range N, F (1 + 2 * ((r : ℝ) + 1))) =
      ∑ r ∈ range M, F (1 + 2 * ((r : ℝ) + 1)) := by
    apply sum_eq_of_vanishing_tails
    · intro r hr
      have hh : (N : ℝ) ≤ r := by exact_mod_cast hr
      exact hzN _ (by linarith only [hh])
    · intro r hr
      have hn : ⌊Real.exp L⌋₊ < 1 + 2 * (r + 1) := by dsimp only [M] at hr; omega
      have he := Nat.lt_floor_add_one (Real.exp L)
      have hh : (⌊Real.exp L⌋₊ : ℝ) + 1 ≤ 1 + 2 * ((r : ℝ) + 1) := by exact_mod_cast hn
      exact hzM _ (he.le.trans hh)
  obtain ⟨ℓ, hℓ, hLip⟩ := hu.exists_lipschitz
  have hcont := (spatial_product_lipschitz hu hρ hw hwL hL hT hc hℓ hLip).continuousOn
  have hint := integral_eq_of_vanishing_tails hcont
    (by linarith only [Nat.cast_nonneg (α := ℝ) N] : (1 : ℝ) ≤ 1 + 2 * (N : ℝ))
    (Real.one_le_exp_iff.mpr hL) hzN hzM
  change (∑ r ∈ range N, F (1 + 2 * ((r : ℝ) + 1))) -
      (1 / 2 : ℝ) * (∫ x in (1 : ℝ)..(1 + 2 * (N : ℝ)), F x) = _
  rw [hsum, hint]

private theorem frequency_cutoff_le {T : ℝ} (hT : 0 ≤ T) (q : ℕ) :
    (⌊2 * (q : ℝ) * T / Real.pi⌋₊ : ℝ) ≤ (q : ℝ) * T := by
  have hq : 0 ≤ (q : ℝ) * T := mul_nonneg (Nat.cast_nonneg _) hT
  refine (Nat.floor_le (by positivity)).trans ?_
  apply (div_le_iff₀ Real.pi_pos).mpr
  have h := mul_le_mul_of_nonneg_left Real.two_le_pi hq
  nlinarith only [h]

private theorem harmonic_sum_le_log_horizon {N : ℕ} {H : ℝ}
    (hH : 1 ≤ H) (hN : (N : ℝ) ≤ H) :
    (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) ≤ 1 + Real.log H := by
  have h := harmonic_le_one_add_log N
  simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  simp only [← one_div] at h
  have hl : Real.log N ≤ Real.log H := by
    rcases Nat.eq_zero_or_pos N with rfl | hn
    · simpa only [Nat.cast_zero, Real.log_zero] using Real.log_nonneg hH
    · exact Real.log_le_log (by exact_mod_cast hn) hN
  linarith only [h, hl]

/-- Summing primitive-frequency quadrature errors costs only
`C T (1 + L + log ((Q+1)T)) (1 + log Q)`. The arithmetic first moment
absorbs the conductor factor; the frequency sum is harmonic. -/
theorem WindowProfile.exists_sum_oddSpatialQuadratureError_le {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : ℝ → ℝ) (L w T : ℝ) (Q : ℕ),
      TaperProfile ρ → 0 < w → 2 * w ≤ L → 1 ≤ L → 1 ≤ T →
      (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1),
        (sqfreeTotientInv q / (q.totient : ℝ)) *
          ∑ n ∈ (Icc 1 ⌊2 * (q : ℝ) * T / Real.pi⌋₊).filter (fun n => Nat.Coprime n q),
            |oddSpatialQuadratureError (profileΩ u T) (Taper.g ρ L w) T (Real.pi * n / q)|) ≤
        K * T * (1 + L + Real.log (((Q : ℝ) + 1) * T)) * (1 + Real.log Q) := by
  obtain ⟨C, hC, hquad⟩ := hu.exists_oddSpatialQuadratureError_le
  refine ⟨64 * (4 + C), by positivity, ?_⟩
  intro ρ L w T Q hρ hw hwL hL hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  let H : ℝ := ((Q : ℝ) + 1) * T
  let B : ℝ := 4 * (1 + Real.log H) + C * L
  let A : ℕ → ℝ := fun q => sqfreeTotientInv q / (q.totient : ℝ)
  have hH : 1 ≤ H := by dsimp only [H]; nlinarith only [Nat.cast_nonneg (α := ℝ) Q, hT]
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hA (q : ℕ) : 0 ≤ A q := div_nonneg (sqfreeTotientInv_nonneg _) (Nat.cast_nonneg _)
  have hrow (q : ℕ) (hq : q ∈ Icc 1 Q) :
      (∑ n ∈ (Icc 1 ⌊2 * (q : ℝ) * T / Real.pi⌋₊).filter (fun n => Nat.Coprime n q),
        |oddSpatialQuadratureError (profileΩ u T) (Taper.g ρ L w) T (Real.pi * n / q)|) ≤
        (q : ℝ) * T * B := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    let N := ⌊2 * (q : ℝ) * T / Real.pi⌋₊
    have hN : (N : ℝ) ≤ (q : ℝ) * T := frequency_cutoff_le hT0.le q
    have hqQ : (q : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hq).2
    have hNH : (N : ℝ) ≤ H := hN.trans (by dsimp only [H]; nlinarith only [hqQ, hT0])
    have hsum : (∑ n ∈ (Icc 1 N).filter (fun n => Nat.Coprime n q),
        |oddSpatialQuadratureError (profileΩ u T) (Taper.g ρ L w) T (Real.pi * n / q)|) ≤
        ∑ n ∈ Icc 1 N, (4 * T * q * (1 / (n : ℝ)) + C * L) := by
      refine (sum_le_sum (fun n hn => ?_)).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => by positivity))
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).2
      have hnc : (n : ℝ) ≤ 2 * (q : ℝ) * T / Real.pi :=
        hnN.trans (Nat.floor_le (by positivity))
      have hc : Real.pi * n / q ≤ 2 * T := by
        apply (div_le_iff₀ hq0).mpr
        have hh := (le_div_iff₀ Real.pi_pos).mp hnc
        nlinarith only [hh]
      have he := hquad ρ L w T (Real.pi * n / q) hρ hw hwL hL hT (by positivity) hc
      refine he.trans (add_le_add ?_ le_rfl)
      have hden : (n : ℝ) / q ≤ Real.pi * n / q :=
        div_le_div_of_nonneg_right (by nlinarith only [Real.two_le_pi, hn0]) hq0.le
      calc
        _ ≤ 4 * T / ((n : ℝ) / q) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = _ := by field_simp
    have hh := harmonic_sum_le_log_horizon hH hNH
    calc
      _ ≤ ∑ n ∈ Icc 1 N, (4 * T * q * (1 / (n : ℝ)) + C * L) := hsum
      _ = 4 * T * q * (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) + (N : ℝ) * (C * L) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc]
        simp only [Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ 4 * T * q * (1 + Real.log H) + ((q : ℝ) * T) * (C * L) :=
        add_le_add (mul_le_mul_of_nonneg_left hh (by positivity))
          (mul_le_mul_of_nonneg_right hN (mul_nonneg hC hL0))
      _ = _ := by dsimp only [B]; ring
  have hfirst : (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), (q : ℝ) * A q) ≤
      64 * (1 + Real.log Q) := by
    calc
      _ ≤ ∑ q ∈ Icc 1 Q, (q : ℝ) * A q :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => mul_nonneg (Nat.cast_nonneg _) (hA q))
      _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ))^2 / q := by
        apply sum_le_sum
        intro q hq
        have hq0 : 0 < q := (mem_Icc.mp hq).1
        have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
        have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
        dsimp only [A]
        by_cases hs : Squarefree q
        · rw [sqfreeTotientInv_apply, if_pos hs]
          apply le_of_eq
          field_simp
        · rw [sqfreeTotientInv_apply, if_neg hs, zero_div, mul_zero]
          positivity
      _ ≤ _ := sum_totientRatio_sq_div_le Q
  have hshape : B ≤ (4 + C) * (1 + L + Real.log H) := by
    dsimp only [B]
    nlinarith only [hL0, hC, mul_nonneg hC hlogH]
  calc
    _ ≤ ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), A q * ((q : ℝ) * T * B) :=
      sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left (hrow q (mem_filter.mp hq).1) (hA q))
    _ = (T * B) * ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), (q : ℝ) * A q := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ (T * B) * (64 * (1 + Real.log Q)) :=
      mul_le_mul_of_nonneg_left hfirst (mul_nonneg hT0.le hB)
    _ ≤ 64 * (4 + C) * T * (1 + L + Real.log H) * (1 + Real.log Q) := by
      have hh := mul_le_mul_of_nonneg_left hshape
        (show 0 ≤ 64 * T * (1 + Real.log Q) by
          have := Real.log_natCast_nonneg Q
          positivity)
      nlinarith only [hh]

end GaloisForLFunctions.TransThresholdPairCorrelation
