import GaloisForLFunctions.RHTower.SmoothAFENormalizedChannelEnergy

/-!
# Arbitrarily large conditional covariance constants for literal reflected-AFE channels

The normalized cofactor energy construction transfers to the actual reflected-primal AFE
coefficients through the exact common-height phase rotation and the proved chi conductor
envelope. For any requested positive constant, one fixed finite-character cell produces a
lower bound by that constant divided by `log N`, in every node coefficient direction,
throughout a common-height window of length proportional to `N`.

Every phase in the cell is explicitly rotated with the common height. The pointwise theorem
is recovered at the cell centre. Measure transport for this rotation, simultaneous centre/target
control, and deterministic recurrence are separate steps.
-/

noncomputable section
open Filter Topology Finset Complex
namespace RHTower

/-- The exact node conductor multiplier in the reflected-primal channel identity. -/
def reflectedPrimalNodeScale (d tau : ℝ) (N : ℕ) : ℂ :=
  zetaChi (rightDisplacedLinePt d tau) * (N : ℂ) ^ (rightDisplacedLinePt d tau - 1)

private theorem exists_reflectedPrimalNodeScale_lower {d : ℝ}
    (hd : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ}, 1 ≤ N → ∀ tau ∈ Set.Icc (N : ℝ) (2 * N),
      c * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖reflectedPrimalNodeScale d tau N‖ := by
  obtain ⟨c, hc, hchi⟩ := exists_norm_zetaChi_rightDisplaced_ge_nat_window hd hdhalf
  refine ⟨c, hc, ?_⟩
  intro N hN tau htau
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hre : (rightDisplacedLinePt d tau - 1).re = d - 1 / 2 := by
    rw [Complex.sub_re, rightDisplacedLinePt_re, Complex.one_re]
    ring
  rw [reflectedPrimalNodeScale, norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, hre]
  calc
    c * (N : ℝ) ^ (-(1 / 2 : ℝ)) =
        (c * (N : ℝ) ^ (-d)) * (N : ℝ) ^ (d - 1 / 2) := by
      rw [mul_assoc, ← Real.rpow_add hNR]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hchi hN tau htau) (Real.rpow_nonneg hNR.le _)

/-- One positive conductor constant controls all fixed nodes throughout the common-height window. -/
theorem exists_eventually_reflectedPrimalNodeScale_lower
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N), ∀ j,
        c * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖reflectedPrimalNodeScale (d j) (tau + b j) N‖ := by
  haveI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  choose c hc hscale using fun j => exists_reflectedPrimalNodeScale_lower (hd j) (hdhalf j)
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ c Finset.univ_nonempty
  have hoffset : ∀ᶠ N : ℕ in atTop, ∀ j, 4 * |b j| ≤ (N : ℝ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (4 * |b j|))
  refine ⟨c i, hc i, ?_⟩
  filter_upwards [hoffset, eventually_ge_atTop 1] with N hbN hN
  intro tau htau j
  have hwindow : tau + b j ∈ Set.Icc (N : ℝ) (2 * N) := by
    have hb := hbN j
    have hlo := neg_abs_le (b j)
    have hhi := le_abs_self (b j)
    constructor <;> linarith [htau.1, htau.2]
  exact (mul_le_mul_of_nonneg_right (hi j (mem_univ j)) (Real.rpow_nonneg (Nat.cast_nonneg N) _)).trans
    (hscale j hN _ hwindow)

/-- The literal channel combination has exactly its normalized energy after shifting phases
and multiplying the node coefficients by their conductor scales. -/
theorem norm_reflectedPrimalChannel_dot_eq_normalized
    {J : ℕ} (d b : Fin J → ℝ) (tau r : ℝ) (N p : ℕ)
    (hN : 0 < N) (hp : 0 < p) (hL : 0 < N / p)
    (omega : SteinhausModel.Omega) (u : Fin J → ℂ) :
    ‖∑ j, steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
        N p omega * u j‖ =
      ‖∑ j, normalizedCofactorChannel (fun j => rightDisplacedLinePt (d j) (b j))
          r N p (steinhausLogPhaseShift omega tau) j *
        (reflectedPrimalNodeScale (d j) (tau + b j) N * u j)‖ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hunit : ‖(((p : ℝ) / N : ℝ) : ℂ) ^ ((tau : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hpR hNR)]
    simp
  have heq : (∑ j, steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
        N p omega * u j) =
      (((p : ℝ) / N : ℝ) : ℂ) ^ ((tau : ℂ) * I) *
      (∑ j, normalizedCofactorChannel (fun j => rightDisplacedLinePt (d j) (b j))
          r N p (steinhausLogPhaseShift omega tau) j *
        (reflectedPrimalNodeScale (d j) (tau + b j) N * u j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [reflectedPrimalChannel_eq_normalized_smoothCofactor d b tau r N p hp hL omega j]
    simp only [normalizedCofactorChannel, reflectedPrimalNodeScale]
    ring
  rw [heq, norm_mul, hunit, one_mul]

/-- Unconditional covariance construction on a fixed phase cell for actual reflected-primal
channels. Its constant is arbitrary, and every cell phase and coefficient direction is covered
throughout the common-height window after the exact common phase rotation. -/
theorem exists_reflectedPrimalConditional_energy_cell_lower
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j)))
    (S : Finset ℕ) (omega : SteinhausModel.Omega) {H : ℝ} (hH : 0 < H) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ r₀ : ℝ, ∃ K B : ℕ, ∃ δ : ℝ, 0 < r₀ ∧ 0 < K ∧ 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
        N < (N / (2 * K)) * (N / (2 * K)) ∧
        ∀ eta ∈ steinhausCharacterCell B omega' δ,
          ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
          ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ u : Fin J → ℂ,
            H / Real.log N * ‖u‖ ^ 2 ≤
              ∑ p ∈ largePrimes N (N / (2 * K)),
                ‖∑ j, steinhausLargePrimeChannel
                    (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
                    N p (steinhausLogPhaseShift eta (-tau)) * u j‖ ^ 2 := by
  classical
  haveI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  let s : Fin J → ℂ := fun j => rightDisplacedLinePt (d j) (b j)
  have hs : ∀ j, 0 < (s j).re := by
    intro j
    dsimp only [s]
    rw [rightDisplacedLinePt_re]
    linarith [hd j]
  have hs1 : ∀ j, (s j).re < 1 := by
    intro j
    dsimp only [s]
    rw [rightDisplacedLinePt_re]
    linarith [hdhalf j]
  obtain ⟨c, hc, hscale⟩ := exists_eventually_reflectedPrimalNodeScale_lower hJ d b hd hdhalf
  obtain ⟨omega', hp, r₀, K, B, δ, hr₀, hK, hδ, hnormalized⟩ :=
    exists_normalizedCofactorChannel_energy_cell_lower hJ s hs hs1 hinj S omega (H / c ^ 2)
  refine ⟨omega', hp, r₀, K, B, δ, hr₀, hK, hδ, ?_⟩
  filter_upwards [hnormalized, hscale, eventually_ge_atTop 2] with N hnormN hscaleN hN
  refine ⟨hnormN.1, ?_⟩
  intro eta heta tau htau r hr hrle u
  let v : Fin J → ℂ := fun j => reflectedPrimalNodeScale (d j) (tau + b j) N * u j
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hv : (c * (N : ℝ) ^ (-(1 / 2 : ℝ))) * ‖u‖ ≤ ‖v‖ := by
    obtain ⟨j, hj⟩ := (IsGreatest.pi_norm u).1
    calc
      _ = (c * (N : ℝ) ^ (-(1 / 2 : ℝ))) * ‖u j‖ := by congr 1; exact hj.symm
      _ ≤ ‖reflectedPrimalNodeScale (d j) (tau + b j) N‖ * ‖u j‖ :=
        mul_le_mul_of_nonneg_right (hscaleN tau htau j) (norm_nonneg _)
      _ = ‖v j‖ := by dsimp only [v]; rw [norm_mul]
      _ ≤ _ := norm_le_pi_norm v j
  have hv2 := (sq_le_sq₀ (by positivity) (norm_nonneg v)).mpr hv
  have hcancel : (N : ℝ) * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 := by
    rw [pow_two, ← Real.rpow_add hNR,
      show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by ring, Real.rpow_neg_one]
    exact mul_inv_cancel₀ hNR.ne'
  have hphase : steinhausLogPhaseShift (steinhausLogPhaseShift eta (-tau)) tau = eta := by
    ext p
    simp only [steinhausLogPhaseShift]
    ring
  calc
    H / Real.log N * ‖u‖ ^ 2 =
        (H / c ^ 2) * N / Real.log N * ((c * (N : ℝ) ^ (-(1 / 2 : ℝ))) * ‖u‖) ^ 2 := by
      calc
        _ = H / Real.log N * ‖u‖ ^ 2 * ((N : ℝ) * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) := by
          rw [hcancel, mul_one]
        _ = _ := by field_simp
    _ ≤ (H / c ^ 2) * N / Real.log N * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hv2 (by positivity)
    _ ≤ ∑ p ∈ largePrimes N (N / (2 * K)),
        ‖∑ j, normalizedCofactorChannel s r N p eta j * v j‖ ^ 2 := hnormN.2 eta heta r hr hrle v
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hpblock
      obtain ⟨⟨hpN, hpp⟩, _⟩ := mem_largePrimes.mp hpblock
      have hL : 0 < N / p := Nat.div_pos hpN hpp.pos
      rw [norm_reflectedPrimalChannel_dot_eq_normalized d b tau r N p (by omega)
        hpp.pos hL (steinhausLogPhaseShift eta (-tau)) u, hphase]

/-- The fixed cell's centre recovers the pointwise actual-channel covariance bound. -/
theorem exists_reflectedPrimalConditional_energy_lower
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j)))
    (S : Finset ℕ) (omega : SteinhausModel.Omega) {H : ℝ} (hH : 0 < H) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ r₀ : ℝ, ∃ K : ℕ, 0 < r₀ ∧ 0 < K ∧ ∀ᶠ N : ℕ in atTop,
        N < (N / (2 * K)) * (N / (2 * K)) ∧
        ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
          ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ u : Fin J → ℂ,
            H / Real.log N * ‖u‖ ^ 2 ≤
              ∑ p ∈ largePrimes N (N / (2 * K)),
                ‖∑ j, steinhausLargePrimeChannel
                    (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
                    N p (steinhausLogPhaseShift omega' (-tau)) * u j‖ ^ 2 := by
  obtain ⟨omega', hp, r₀, K, B, δ, hr₀, hK, hδ, hcell⟩ :=
    exists_reflectedPrimalConditional_energy_cell_lower hJ d b hd hdhalf hinj S omega hH
  refine ⟨omega', hp, r₀, K, hr₀, hK, ?_⟩
  filter_upwards [hcell] with N hN
  refine ⟨hN.1, hN.2 omega' ?_⟩
  intro n _
  simpa using hδ

end RHTower
