import GaloisForLFunctions.RHTower.SteinhausTruncatedGaussianChannelEnergy
import GaloisForLFunctions.RHTower.SmoothAFEReflectedTruncatedGaussianTransfer
import GaloisForLFunctions.RHTower.SmoothAFEReflectedConditionalEnergy



open Filter Topology Finset Complex
noncomputable section
namespace RHTower

/-- Exact conductor separation for an independently truncated literal Gaussian channel. -/
theorem reflectedPrimalChannel_eq_normalized_truncatedGaussian
    {J : ℕ} (d b : Fin J → ℝ) (tau : ℝ) (N L p : ℕ)
    (hN : 0 < N) (hp : 0 < p) (ω : SteinhausModel.Omega) (j : Fin J) :
    steinhausLargePrimeChannel
      (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N) L p ω =
      reflectedPrimalNodeScale (d j) (tau + b j) N *
        (((p : ℝ) / N : ℝ) : ℂ) ^ ((tau : ℂ) * I) *
          normalizedTruncatedGaussianCofactorChannel (fun j => rightDisplacedLinePt (d j) (b j))
            ((N : ℝ) / p) (L / p) (steinhausLogPhaseShift ω tau) j := by
  let s := rightDisplacedLinePt (d j) (b j)
  let z := rightDisplacedLinePt (d j) (tau + b j)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hz : z - 1 = s - 1 + (tau : ℂ) * I := by
    simp only [s, z, rightDisplacedLinePt, Complex.ofReal_add]
    ring
  have hheight : (N : ℂ) ^ ((tau : ℂ) * I) *
      (((p : ℝ) / N : ℝ) : ℂ) ^ ((tau : ℂ) * I) = (p : ℂ) ^ ((tau : ℂ) * I) := by
    have h := Complex.mul_cpow_ofReal_nonneg hNR.le (div_pos hpR hNR).le ((tau : ℂ) * I)
    have hinner : (N : ℝ) * ((p : ℝ) / N) = p := by field_simp
    rw [← Complex.ofReal_mul, hinner] at h
    simpa only [Complex.ofReal_natCast] using h.symm
  have hbase := truncatedGaussian_prime_channel_factor
    (fun j => rightDisplacedLinePt (d j) (b j)) hNR hpR (L / p) (steinhausLogPhaseShift ω tau) j
  simp only [Complex.ofReal_natCast] at hbase
  rw [reflectedPrimalChannel_eq_truncatedFullGaussianCofactor _ _ _ _ _ _ hN hp]
  change (zetaChi z * (p : ℂ) ^ (z - 1)) * _ =
    (zetaChi z * (N : ℂ) ^ (z - 1)) * _ * _
  rw [hz, Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hNC]
  calc
    _ = (zetaChi z * (p : ℂ) ^ ((tau : ℂ) * I)) *
        ((p : ℂ) ^ (s - 1) * truncatedFullGaussianCofactor s ((N : ℝ) / p) (L / p)
          (steinhausLogPhaseShift ω tau)) := by ring
    _ = _ := by rw [hbase, ← hheight]; ring

/-- Common height contributes only a unit scalar to every actual prime row. -/
theorem norm_reflectedPrimalWindowChannel_dot_eq_normalized
    {J : ℕ} (d b : Fin J → ℝ) (tau : ℝ) (N L p : ℕ)
    (hN : 0 < N) (hp : 0 < p) (omega : SteinhausModel.Omega) (u : Fin J → ℂ) :
    ‖∑ j, steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N)
        L p omega * u j‖ =
      ‖∑ j, normalizedTruncatedGaussianCofactorChannel (fun j => rightDisplacedLinePt (d j) (b j))
          ((N : ℝ) / p) (L / p) (steinhausLogPhaseShift omega tau) j *
        (reflectedPrimalNodeScale (d j) (tau + b j) N * u j)‖ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hunit : ‖(((p : ℝ) / N : ℝ) : ℂ) ^ ((tau : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hpR hNR)]
    simp
  have heq : (∑ j, steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N)
        L p omega * u j) =
      (((p : ℝ) / N : ℝ) : ℂ) ^ ((tau : ℂ) * I) *
      (∑ j, normalizedTruncatedGaussianCofactorChannel (fun j => rightDisplacedLinePt (d j) (b j))
          ((N : ℝ) / p) (L / p) (steinhausLogPhaseShift omega tau) j *
        (reflectedPrimalNodeScale (d j) (tau + b j) N * u j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [reflectedPrimalChannel_eq_normalized_truncatedGaussian d b tau N L p hN hp omega j]
    ring
  rw [heq, norm_mul, hunit, one_mul]

/-- The literal reflected channels at any sufficiently long polynomial cutoff have arbitrary
H/log N energy throughout one fixed character cell and the entire common-height window.
Together with the free-window decomposition this is the actual conditional Gram floor. -/
theorem exists_reflectedPrimalWindowConditional_energy_cell_lower
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j)))
    (S : Finset ℕ) (omega : SteinhausModel.Omega) {H : ℝ} (hH : 0 < H) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ K B D : ℕ, ∃ δ : ℝ, 0 < K ∧ 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
        N < (N / (2 * K)) * (N / (2 * K)) ∧
        ∀ L : ℕ, N * D ≤ L → ∀ eta ∈ steinhausCharacterCell B omega' δ,
          ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
          ∀ u : Fin J → ℂ,
            H / Real.log N * ‖u‖ ^ 2 ≤
              ∑ p ∈ largePrimes N (N / (2 * K)),
                ‖∑ j, steinhausLargePrimeChannel
                    (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N)
                    L p (steinhausLogPhaseShift eta (-tau)) * u j‖ ^ 2 := by
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
  obtain ⟨omega', hp, K, B, D, δ, hK, hδ, hnormalized⟩ :=
    exists_normalizedTruncatedGaussianCofactorChannel_energy_cell_lower hJ s hs hs1 hinj S omega (H / c ^ 2)
  refine ⟨omega', hp, K, B, D, δ, hK, hδ, ?_⟩
  filter_upwards [hnormalized, hscale, eventually_ge_atTop 2] with N hnormN hscaleN hN
  refine ⟨hnormN.1, ?_⟩
  intro L hL eta heta tau htau u
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
        ‖∑ j, normalizedTruncatedGaussianCofactorChannel s ((N : ℝ) / p) (L / p) eta j * v j‖ ^ 2 := hnormN.2 L hL eta heta v
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hpblock
      obtain ⟨⟨hpN, hpp⟩, _⟩ := mem_largePrimes.mp hpblock
      rw [norm_reflectedPrimalWindowChannel_dot_eq_normalized d b tau N L p (by omega)
        hpp.pos (steinhausLogPhaseShift eta (-tau)) u, hphase]


end RHTower
