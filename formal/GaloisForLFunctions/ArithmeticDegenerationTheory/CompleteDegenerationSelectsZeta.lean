import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheResolutionThresholdOfAFlippedPrimeIsExact
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.EveryFiniteFlipSetHasAnExactResolutionThreshold
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheLimitingMixedStructure

/-!
# Complete degeneration selects `ζ`

For a real twist `λ` of the von Mangoldt weights with summable defect, the twisted complete Weil
family has a fixed-overlap limit on Ramanujan packets (RAPT):

`E_λ(c; T, β) = Σ_{m∈T} β_m² E_m(c) + F_λ(y)`,   `y = Σ β_m r_m`,

where `F_λ(y) = 2 Σ_k d_λ(k) k^{-1/2} M(y·y(k·))` (`twistLimitEnergy`) does not depend on the
overlap. Since `E_m(c) → 0`, the limit structure of a twin does **not** degenerate to zero: it
degenerates to the overlap-independent form `F_λ`.

* **The degeneration of a twist** (`tendsto_packetEnergy_atTop`): `E_λ(c; T, β) → F_λ(y)` as
  `c → ∞`.
* **`ζ` degenerates completely** (`twistLimitEnergy_vonMangoldt`, `packetEnergy_vonMangoldt`):
  for `λ = Λ` the defect vanishes, `F_Λ = 0`, the limit structure tends to `0` and, for the tilted
  spline, its rescaling `c⁷ E_Λ` tends to the positive Jordan form
  (`tendsto_rescaled_packetEnergy_vonMangoldt`).
* **Every prime flip degenerates to an indefinite form** (`primeFlip_degenerates_indefinitely`):
  for a profile without real Fourier zeros, `F_{ω_p}` is positive on the pole packet
  (`4 log p Σ_j p^{-(2j+1)}`) and negative on some unit packet. Hence the rescaled limit of the
  twin does not exist: `c⁷ E_{ω_p} → −∞` on that packet (`tendsto_rescaled_packetEnergy_primeFlip`).

* **Every finite flip set** (`finiteFlip_residue_indefinite`): the overlap-independent residue
  `F_{ω_S}` of flipping a nonempty finite set `S` of primes is positive on the pole profile and
  negative on RAPT's flip-set trial.

So within the twist family, complete degeneration — a limiting structure that tends to zero and has
a polarized rescaled limit — is the signature of `ζ`. A flip leaves a non-degenerating, indefinite
residue of weight zero, the size of the flip and independent of the resolution. This is selection by
structure (the defect identity `d_Λ = 0`), not by a margin; it does not decide the sign of `ζ`.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  RenormalizedBiarithmeticGeometry SpacingScaleHarmonicAnalysis ArithmeticCountingPositivity

variable {φ : ℝ → ℝ}

/-- **The degeneration of a twist.** As the overlap grows, the twisted limit energy of a packet
tends to the overlap-independent twist energy. -/
theorem tendsto_packetEnergy_atTop (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    (lam : ℕ → ℝ) (T : Finset ℕ) (β : ℕ → ℝ) :
    Tendsto (fun c => packetEnergy lam φ c T β) atTop
      (𝓝 (twistLimitEnergy lam (packetProfile T β) (packetPeriod T))) := by
  have h : Tendsto (fun c => ∑ m ∈ T, β m ^ 2 * completedConductorEnergy φ c m) atTop
      (𝓝 (∑ m ∈ T, β m ^ 2 * 0)) :=
    tendsto_finsetSum _ fun m _ =>
      (tendsto_completedConductorEnergy_atTop hφ hsupp hM m).const_mul _
  simp only [mul_zero, sum_const_zero] at h
  simpa [packetEnergy] using h.add_const (twistLimitEnergy lam (packetProfile T β) (packetPeriod T))

/-- The von Mangoldt weights have zero twist defect. -/
theorem twistDefect_vonMangoldt (k : ℕ) :
    twistDefect (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) k = 0 := by
  simp [twistDefect, _root_.RHTower.vonMangoldtAtom, twistCoeff]

theorem twistLimitEnergy_vonMangoldt (y : ℕ → ℝ) (P : ℕ) :
    twistLimitEnergy (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) y P = 0 := by
  simp [twistLimitEnergy, twistDefect_vonMangoldt]

/-- **`ζ` degenerates completely**: its packet energies are the conductor energies alone. -/
theorem packetEnergy_vonMangoldt (c : ℝ) (T : Finset ℕ) (β : ℕ → ℝ) :
    packetEnergy (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) φ c T β =
      ∑ m ∈ T, β m ^ 2 * completedConductorEnergy φ c m := by
  simp [packetEnergy, twistLimitEnergy_vonMangoldt]

/-- For the tilted spline the rescaled packet energies of `ζ` tend to the Jordan form. -/
theorem tendsto_rescaled_packetEnergy_vonMangoldt (T : Finset ℕ) (β : ℕ → ℝ) :
    Tendsto (fun c => c ^ (7 : ℝ) *
        packetEnergy (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) tiltedUnitSpline c T β)
      atTop (𝓝 (∑ m ∈ T, β m ^ 2 * jordanCoefficient m)) := by
  simp_rw [packetEnergy_vonMangoldt, mul_sum]
  refine tendsto_finsetSum _ fun m _ => ?_
  have := (tendsto_rpow_seven_mul_completedConductorEnergy_jordan m).const_mul (β m ^ 2)
  refine this.congr fun c => ?_
  ring

/-- The pole packet `y ≡ 1`. -/
theorem packetProfile_pole (n : ℕ) : packetProfile {1} (fun _ => 1) n = 1 := by
  simp [packetProfile, normalizedRamanujanMode, ramanujanMode_one]

/-- **A flip is positive on the pole packet**: `F_{ω_p}(1) = 4 log p Σ_j p^{-(2j+1)} > 0`. -/
theorem twistLimitEnergy_primeFlip_pole_pos {p : ℕ} (hp : p.Prime) :
    0 < twistLimitEnergy (primeFlipWeight p) (packetProfile {1} (fun _ => 1))
      (packetPeriod {1}) := by
  have hP : 0 < packetPeriod ({1} : Finset ℕ) := by simp [packetPeriod]
  have hy : Function.Periodic (packetProfile {1} (fun _ => 1)) (packetPeriod {1}) := fun n => by
    simp only [packetProfile_pole]
  rw [twistLimitEnergy_primeFlip hp hP hy]
  have hshift : ∀ k : ℕ, shiftMean (packetProfile {1} (fun _ => 1)) (packetPeriod {1}) k = 1 := by
    intro k
    simp [shiftMean, periodMean, packetProfile_pole, packetPeriod]
  simp only [hshift]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hsum : Summable fun j : ℕ => 1 / (p : ℝ) ^ (2 * j + 1) := by
    have hg : Summable fun j : ℕ => ((p : ℝ)⁻¹ ^ 2) ^ j :=
      summable_geometric_of_lt_one (by positivity)
        (by rw [inv_pow]; exact inv_lt_one_of_one_lt₀ (by nlinarith))
    refine (hg.mul_left (p : ℝ)⁻¹).congr fun j => ?_
    rw [one_div, ← inv_pow, ← pow_mul, ← pow_succ']
  have hpos : 0 < ∑' j : ℕ, 1 / (p : ℝ) ^ (2 * j + 1) :=
    hsum.tsum_pos (fun j => by positivity) 0 (one_div_pos.mpr (pow_pos hp0 _))
  positivity

/-- **A flip is negative on some unit packet** (for profiles without real Fourier zeros). -/
theorem exists_twistLimitEnergy_primeFlip_neg (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hFT : ∀ r : ℝ, Zeta23.paperFT (ArithmeticCastelnuovoSeveri.cx φ) (r : ℂ) ≠ 0) {p : ℕ}
    (hp : p.Prime) :
    ∃ T : Finset ℕ, (∀ m ∈ T, 0 < m) ∧ ∃ β : ℕ → ℝ, ∑ m ∈ T, β m ^ 2 = 1 ∧
      twistLimitEnergy (primeFlipWeight p) (packetProfile T β) (packetPeriod T) < 0 := by
  obtain ⟨c₁, hc₁, hneg⟩ := exists_primeFlip_resolutionBottom_neg hφ hsupp hFT hp
  obtain ⟨E, ⟨T, hT, β, hβ, rfl⟩, hE⟩ :=
    exists_lt_of_csInf_lt (unitPacketEnergies_nonempty _ φ c₁) hneg
  refine ⟨T, hT, β, hβ, ?_⟩
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  have hnn : 0 ≤ ∑ m ∈ T, β m ^ 2 * completedConductorEnergy φ c₁ m :=
    sum_nonneg fun m hm => mul_nonneg (sq_nonneg _)
      (completedConductorEnergy_nonneg hφ hsupp hM hc₁ (hT m hm))
  have : packetEnergy (primeFlipWeight p) φ c₁ T β < 0 := hE
  unfold packetEnergy at this
  linarith

/-- **Every prime flip degenerates to an indefinite form.** The large-overlap limit of the
flipped limit structure is positive on the pole packet and negative on some unit packet. -/
theorem primeFlip_degenerates_indefinitely (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hFT : ∀ r : ℝ, Zeta23.paperFT (ArithmeticCastelnuovoSeveri.cx φ) (r : ℂ) ≠ 0) {p : ℕ}
    (hp : p.Prime) :
    Tendsto (fun c => packetEnergy (primeFlipWeight p) φ c {1} (fun _ => 1)) atTop
        (𝓝 (twistLimitEnergy (primeFlipWeight p) (packetProfile {1} (fun _ => 1))
          (packetPeriod {1}))) ∧
      0 < twistLimitEnergy (primeFlipWeight p) (packetProfile {1} (fun _ => 1)) (packetPeriod {1}) ∧
      ∃ T : Finset ℕ, (∀ m ∈ T, 0 < m) ∧ ∃ β : ℕ → ℝ, ∑ m ∈ T, β m ^ 2 = 1 ∧
        Tendsto (fun c => packetEnergy (primeFlipWeight p) φ c T β) atTop
          (𝓝 (twistLimitEnergy (primeFlipWeight p) (packetProfile T β) (packetPeriod T))) ∧
        twistLimitEnergy (primeFlipWeight p) (packetProfile T β) (packetPeriod T) < 0 := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  obtain ⟨T, hT, β, hβ, hneg⟩ := exists_twistLimitEnergy_primeFlip_neg hφ hsupp hFT hp
  exact ⟨tendsto_packetEnergy_atTop hφ hsupp hM _ _ _, twistLimitEnergy_primeFlip_pole_pos hp,
    T, hT, β, hβ, tendsto_packetEnergy_atTop hφ hsupp hM _ _ _, hneg⟩

/-- **A flip twin has no rescaled limit.** For the tilted spline, on a unit packet where the flip
energy is negative, the rescaled twin energy `c⁷ E_{ω_p}` tends to `−∞`. -/
theorem tendsto_rescaled_packetEnergy_primeFlip {p : ℕ} (hp : p.Prime) :
    ∃ T : Finset ℕ, (∀ m ∈ T, 0 < m) ∧ ∃ β : ℕ → ℝ, ∑ m ∈ T, β m ^ 2 = 1 ∧
      Tendsto (fun c => c ^ (7 : ℝ) * packetEnergy (primeFlipWeight p) tiltedUnitSpline c T β)
        atTop atBot := by
  have hFT : ∀ r : ℝ, Zeta23.paperFT (ArithmeticCastelnuovoSeveri.cx tiltedUnitSpline) (r : ℂ) ≠ 0 :=
    paperFT_tiltedUnitSpline_real_ne_zero
  obtain ⟨T, hT, β, hβ, hneg⟩ := exists_twistLimitEnergy_primeFlip_neg contDiff_tiltedUnitSpline
    (fun u hu => tiltedUnitSpline_eq_zero u hu) hFT hp
  refine ⟨T, hT, β, hβ, ?_⟩
  have hlim := tendsto_packetEnergy_atTop contDiff_tiltedUnitSpline
    (fun u hu => tiltedUnitSpline_eq_zero u hu) integral_tiltedUnitSpline_sq_pos
    (primeFlipWeight p) T β
  have h7 : Tendsto (fun c : ℝ => c ^ (7 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  exact h7.atTop_mul_neg hneg hlim

/-- **Every finite flip set leaves an indefinite residue.** For a nonempty finite set `S` of primes,
the overlap-independent twist energy of `ω_S` is positive on the pole profile `y ≡ 1` and negative on
the flip-set trial. -/
theorem finiteFlip_residue_indefinite {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) :
    0 < twistLimitEnergy (finiteFlipWeight S) (fun _ => 1) 1 ∧
      twistLimitEnergy (finiteFlipWeight S) (flipSetTrial S) (flipSetModulus S) < 0 := by
  constructor
  · rw [twistLimitEnergy_finiteFlip hS one_pos (fun _ => rfl)]
    refine sum_pos (fun p hp => ?_) hne
    have h := twistLimitEnergy_primeFlip_pole_pos (hS p hp)
    have hprof : packetProfile {1} (fun _ => (1 : ℝ)) = fun _ => 1 := funext packetProfile_pole
    have hper : packetPeriod ({1} : Finset ℕ) = 1 := by simp [packetPeriod]
    rwa [hprof, hper] at h
  · exact twistLimitEnergy_finiteFlip_flipSetTrial_neg hS hne (flipSetModulus_pos hS) dvd_rfl

end GaloisForLFunctions.ArithmeticDegenerationTheory
