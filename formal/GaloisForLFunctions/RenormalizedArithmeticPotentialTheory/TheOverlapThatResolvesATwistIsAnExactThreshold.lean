import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ATwistedCompleteWeilMatrixIsDecidedByItsRamanujanPackets

/-!
# The overlap that resolves a twist is an exact threshold

For a real twist `λ` with summable defect, the twisted complete Weil matrix at a fixed overlap
`c` is decided by the explicit quadratic form `E_λ(c; T, β)` on Ramanujan packets
(`ATwistedCompleteWeilMatrixIsDecidedByItsRamanujanPackets`). Its bottom

`λ_λ(c) = inf {E_λ(c; T, β) : Σ_{m∈T} β_m² = 1}`  (`resolutionBottom`)

decides the sign: `λ_λ(c) > 0` gives eventual positive definiteness, `λ_λ(c) < 0` an eventually
negative atomic test (`eventually_posDef_of_resolutionBottom_pos`,
`exists_eventually_neg_of_resolutionBottom_neg`).

* **Monotone in the overlap** (`resolutionBottom_antitone`): the conductor energies
  `E_m(c) = (2/(Mφ(m))) Σ_{(a,m)=1} (m/a) ∫_{ac/m}^∞ |φ̂(2πt)|²` decrease in `c`, the twist part
  does not depend on `c`.
* **Strictly, past zero** (`resolutionBottom_neg_of_lt`): for a profile without real Fourier zeros,
  `λ_λ(c) ≤ 0` forces `λ_λ(c') < 0` for every `c' > c`. Near-minimizing packets carry half their
  mass on the finitely many conductors of bounded energy, and there each `E_m` strictly decreases.
* **The exact threshold** (`resolutionThreshold`, `resolutionThreshold_spec`): if some overlap
  sees the twist, `c_0(λ) = sup{c : λ_λ(c) > 0}` is positive and finite, the twisted complete
  matrix is eventually positive definite for every `c < c_0(λ)`, and eventually negative on an
  atomic test for every `c > c_0(λ)`.
* **Single flips** (`primeFlip_resolutionThreshold_spec`, `tendsto_primeFlip_resolutionThreshold`):
  flipping the odd powers of one prime `p` is seen, so `c_0(ω_p)` is an exact finite threshold, and
  `c_0(ω_p) → ∞` as `p → ∞`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticLorentzianGeometry
  RenormalizedBiarithmeticGeometry CompletedShell
open _root_.RHTower (vonMangoldtAtom)

/-! ### Homogeneity of packet energies -/

section Homogeneity

variable {lam : ℕ → ℝ} {φ : ℝ → ℝ} {c : ℝ}

theorem shiftMean_smul (y : ℕ → ℝ) (P k : ℕ) (s : ℝ) :
    shiftMean (fun n => s * y n) P k = s ^ 2 * shiftMean y P k := by
  unfold shiftMean periodMean
  rw [mul_div_assoc', mul_sum]
  congr 1
  exact sum_congr rfl fun i _ => by ring

theorem twistLimitEnergy_smul (y : ℕ → ℝ) (P : ℕ) (s : ℝ) :
    twistLimitEnergy lam (fun n => s * y n) P = s ^ 2 * twistLimitEnergy lam y P := by
  unfold twistLimitEnergy
  simp only [shiftMean_smul]
  rw [← tsum_mul_left]
  rw [mul_left_comm, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun k => by ring

theorem packetProfile_smul (T : Finset ℕ) (β : ℕ → ℝ) (s : ℝ) :
    packetProfile T (fun m => s * β m) = fun n => s * packetProfile T β n := by
  funext n
  unfold packetProfile
  rw [mul_sum]
  exact sum_congr rfl fun m _ => by ring

/-- Packet energies are quadratic in the coefficients. -/
theorem packetEnergy_smul (T : Finset ℕ) (β : ℕ → ℝ) (s : ℝ) :
    packetEnergy lam φ c T (fun m => s * β m) = s ^ 2 * packetEnergy lam φ c T β := by
  unfold packetEnergy
  rw [packetProfile_smul, twistLimitEnergy_smul, mul_add, mul_sum]
  congr 1
  exact sum_congr rfl fun m _ => by ring

theorem packetEnergy_eq_zero {T : Finset ℕ} {β : ℕ → ℝ} (hβ : ∀ m ∈ T, β m = 0) :
    packetEnergy lam φ c T β = 0 := by
  have hprof : packetProfile T β = fun _ => 0 := by
    funext n
    unfold packetProfile
    exact sum_eq_zero fun m hm => by rw [hβ m hm, zero_mul]
  unfold packetEnergy
  rw [hprof, sum_eq_zero fun m hm => by rw [hβ m hm]; ring]
  simp [twistLimitEnergy, shiftMean, periodMean]

end Homogeneity

/-! ### Bounds on packet energies -/

section Bounds

variable {lam : ℕ → ℝ} {φ : ℝ → ℝ} {c : ℝ}

/-- The bound `2 Σ|d_λ| (1 + 2c e^c)` of the twist gap at overlap `c`. -/
def twistBound (lam : ℕ → ℝ) (c : ℝ) : ℝ :=
  2 * (∑' k, |twistDefect lam k|) * (1 + 2 * c * Real.exp c)

theorem twistBound_nonneg (lam : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ twistBound lam c := by
  have := tsum_nonneg fun k => abs_nonneg (twistDefect lam k)
  unfold twistBound
  positivity

theorem twistBound_mono (lam : ℕ → ℝ) {c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') :
    twistBound lam c ≤ twistBound lam c' := by
  have h0 := tsum_nonneg fun k => abs_nonneg (twistDefect lam k)
  unfold twistBound
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have : c * Real.exp c ≤ c' * Real.exp c' :=
    mul_le_mul hcc (Real.exp_le_exp.mpr hcc) (Real.exp_pos _).le (hc.trans hcc)
  linarith

/-- The normalized packets are asymptotically isometric to their coefficients. -/
theorem tendsto_norm_sq_packet {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m) (β : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ‖∑ m ∈ T, β m • normalizedRamanujanHorizonVector m N‖ ^ 2) atTop
      (𝓝 (∑ m ∈ T, β m ^ 2)) := by
  have hexp : ∀ N : ℕ, ‖∑ m ∈ T, β m • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      ∑ m ∈ T, ∑ l ∈ T, β m * β l *
        ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ := by
    intro N
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun l _ => by ring
  have hlim := tendsto_finsetSum T fun m hm => tendsto_finsetSum T fun l hl =>
    (tendsto_normalizedRamanujanHorizonVector_gram (hT m hm) (hT l hl)).const_mul (β m * β l)
  have hval : ∑ m ∈ T, ∑ l ∈ T, β m * β l * (if m = l then (1 : ℝ) else 0) =
      ∑ m ∈ T, β m ^ 2 := by
    refine sum_congr rfl fun m hm => ?_
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, if_pos hm]
    ring
  rw [← hval]
  exact hlim.congr fun N => (hexp N).symm

/-- The gap matrix of a packet tends to the limit twist energy of its profile. -/
theorem tendsto_twistGap_packet (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c) (hlam : Summable fun k => |twistDefect lam k|)
    {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m) (β : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      ⟪toEuclideanLin (twistGapMatrix lam φ c N)
          (∑ m ∈ T, β m • normalizedRamanujanHorizonVector m N),
        ∑ m ∈ T, β m • normalizedRamanujanHorizonVector m N⟫) atTop
      (𝓝 (twistLimitEnergy lam (packetProfile T β) (packetPeriod T))) := by
  have hG := tendsto_twistedGap_packet hφ hsupp hM hc hlam (packetPeriod_pos hT)
    (packetProfile_periodic hT β)
  refine hG.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [inner_twistGapMatrix hφ hsupp hc hN,
    atomicTest_congr (fun n hn => primeHorizonExtension_packet (T := T) (β := β) hn)]

/-- **The twist energy of a packet is bounded** by `twistBound λ c · Σβ²`. -/
theorem abs_twistLimitEnergy_packet_le (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c)
    (hlam : Summable fun k => |twistDefect lam k|) {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m)
    (β : ℕ → ℝ) :
    |twistLimitEnergy lam (packetProfile T β) (packetPeriod T)| ≤
      twistBound lam c * ∑ m ∈ T, β m ^ 2 := by
  have hG := (tendsto_twistGap_packet hφ hsupp hM hc hlam hT β).abs
  have hN := (tendsto_norm_sq_packet hT β).const_mul (twistBound lam c)
  refine le_of_tendsto_of_tendsto hG hN ?_
  filter_upwards [eventually_ge_atTop 1] with N hN1
  exact abs_inner_twistGapMatrix_le hφ hsupp hM hc hlam hN1 _

/-- **Lower bound by the pole energy.** Every conductor energy is at least the pole energy
`E(c) = E_1(c)`, so `E_λ(c; T, β) ≥ (E(c) − twistBound λ c) Σβ²`. -/
theorem packetEnergy_ge (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c) (hlam : Summable fun k => |twistDefect lam k|)
    {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m) (β : ℕ → ℝ) :
    (completedShellEnergy φ c - twistBound lam c) * ∑ m ∈ T, β m ^ 2 ≤
      packetEnergy lam φ c T β := by
  have hE : completedShellEnergy φ c * ∑ m ∈ T, β m ^ 2 ≤
      ∑ m ∈ T, β m ^ 2 * completedConductorEnergy φ c m := by
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [← completedConductorEnergy_one]
    exact completedConductorEnergy_one_le hφ hsupp hM hc (hT m hm)
  have hG := (abs_le.mp (abs_twistLimitEnergy_packet_le hφ hsupp hM hc hlam hT β)).1
  unfold packetEnergy
  linarith

end Bounds

/-! ### The resolution bottom -/

section Bottom

variable {lam : ℕ → ℝ} {φ : ℝ → ℝ} {c : ℝ}

/-- The limiting twisted energies of unit Ramanujan packets at overlap `c`. -/
def unitPacketEnergies (lam : ℕ → ℝ) (φ : ℝ → ℝ) (c : ℝ) : Set ℝ :=
  {E | ∃ T : Finset ℕ, (∀ m ∈ T, 0 < m) ∧ ∃ β : ℕ → ℝ,
    ∑ m ∈ T, β m ^ 2 = 1 ∧ packetEnergy lam φ c T β = E}

/-- The **resolution bottom** `λ_λ(c)`: the infimum of the limiting twisted energies of unit
Ramanujan packets. -/
def resolutionBottom (lam : ℕ → ℝ) (φ : ℝ → ℝ) (c : ℝ) : ℝ := sInf (unitPacketEnergies lam φ c)

theorem unitPacketEnergies_nonempty (lam : ℕ → ℝ) (φ : ℝ → ℝ) (c : ℝ) :
    (unitPacketEnergies lam φ c).Nonempty :=
  ⟨_, {1}, fun m hm => by rw [Finset.mem_singleton] at hm; omega, fun _ => 1,
    by simp, rfl⟩

theorem bddBelow_unitPacketEnergies (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c)
    (hlam : Summable fun k => |twistDefect lam k|) :
    BddBelow (unitPacketEnergies lam φ c) := by
  refine ⟨completedShellEnergy φ c - twistBound lam c, ?_⟩
  rintro E ⟨T, hT, β, hβ, rfl⟩
  have := packetEnergy_ge hφ hsupp hM hc hlam hT β
  rwa [hβ, mul_one] at this

theorem resolutionBottom_le_packetEnergy (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c)
    (hlam : Summable fun k => |twistDefect lam k|) {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m)
    {β : ℕ → ℝ} (hβ : ∑ m ∈ T, β m ^ 2 = 1) :
    resolutionBottom lam φ c ≤ packetEnergy lam φ c T β :=
  csInf_le (bddBelow_unitPacketEnergies hφ hsupp hM hc hlam) ⟨T, hT, β, hβ, rfl⟩

theorem le_resolutionBottom {X : ℝ}
    (h : ∀ T : Finset ℕ, (∀ m ∈ T, 0 < m) → ∀ β : ℕ → ℝ, ∑ m ∈ T, β m ^ 2 = 1 →
      X ≤ packetEnergy lam φ c T β) :
    X ≤ resolutionBottom lam φ c := by
  refine le_csInf (unitPacketEnergies_nonempty lam φ c) ?_
  rintro E ⟨T, hT, β, hβ, rfl⟩
  exact h T hT β hβ

theorem completedShellEnergy_sub_le_resolutionBottom (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c)
    (hlam : Summable fun k => |twistDefect lam k|) :
    completedShellEnergy φ c - twistBound lam c ≤ resolutionBottom lam φ c :=
  le_resolutionBottom fun T hT β hβ => by
    have := packetEnergy_ge hφ hsupp hM hc hlam hT β
    rwa [hβ, mul_one] at this

/-- The bottom bounds every packet energy by homogeneity. -/
theorem resolutionBottom_mul_le (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c) (hlam : Summable fun k => |twistDefect lam k|)
    {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m) (β : ℕ → ℝ) :
    resolutionBottom lam φ c * ∑ m ∈ T, β m ^ 2 ≤ packetEnergy lam φ c T β := by
  set S := ∑ m ∈ T, β m ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun m _ => sq_nonneg _
  rcases eq_or_lt_of_le hS0 with hS1 | hS1
  · have hβ : ∀ m ∈ T, β m = 0 := by
      intro m hm
      have := (sum_eq_zero_iff_of_nonneg fun m _ => sq_nonneg (β m)).mp hS1.symm m hm
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    rw [← hS1, mul_zero, packetEnergy_eq_zero hβ]
  · set r := Real.sqrt S with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hS1
    have hrr : r ^ 2 = S := Real.sq_sqrt hS0
    have hunit : ∑ m ∈ T, (r⁻¹ * β m) ^ 2 = 1 := by
      simp only [mul_pow, ← mul_sum, inv_pow, hrr]
      exact inv_mul_cancel₀ hS1.ne'
    have h := resolutionBottom_le_packetEnergy hφ hsupp hM hc hlam hT hunit
    rw [packetEnergy_smul, inv_pow, hrr] at h
    have := mul_le_mul_of_nonneg_left h hS0
    rwa [← mul_assoc, mul_inv_cancel₀ hS1.ne', one_mul, mul_comm] at this

/-- **Positivity above the bottom.** -/
theorem eventually_posDef_of_resolutionBottom_pos (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c)
    {a₀ β₀ : ℝ} (hβ₀ : 0 < β₀)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a₀ * ‖x‖ ^ 2 + β₀ * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    (hlam : Summable fun k => |twistDefect lam k|) (hpos : 0 < resolutionBottom lam φ c) :
    ∀ᶠ N : ℕ in atTop, (twistedCompleteWeilMatrix lam φ c N).PosDef :=
  eventually_twistedCompleteWeilMatrix_posDef hφ hsupp hM hc hβ₀ hres hlam hpos
    fun T hT β => resolutionBottom_mul_le hφ hsupp hM hc hlam hT β

/-- **Negativity below the bottom.** -/
theorem exists_eventually_neg_of_resolutionBottom_neg (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c)
    (hlam : Summable fun k => |twistDefect lam k|) (hneg : resolutionBottom lam φ c < 0) :
    ∃ T : Finset ℕ, (∀ m ∈ T, 0 < m) ∧ ∃ β : ℕ → ℝ, ∑ m ∈ T, β m ^ 2 = 1 ∧
      ∀ᶠ N : ℕ in atTop, weilQuadTw lam
        (atomicTest N (packetCoeff (packetProfile T β) N) (atomDilate φ (c / N))) < 0 := by
  obtain ⟨E, ⟨T, hT, β, hβ, rfl⟩, hE⟩ :=
    exists_lt_of_csInf_lt (unitPacketEnergies_nonempty lam φ c) hneg
  exact ⟨T, hT, β, hβ, eventually_twisted_packet_neg hφ hsupp hM hc hlam hT hE⟩

/-- A positive definite twisted matrix forbids a negative atomic test. -/
theorem resolutionBottom_nonpos_of_frequently_neg (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hc : 0 < c)
    {a₀ β₀ : ℝ} (hβ₀ : 0 < β₀)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a₀ * ‖x‖ ^ 2 + β₀ * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    (hlam : Summable fun k => |twistDefect lam k|) {y : ℕ → ℝ} (hy1 : y 1 ≠ 0)
    (hneg : ∀ᶠ N : ℕ in atTop, weilQuadTw lam (atomicTest N y (atomDilate φ (c / N))) < 0) :
    resolutionBottom lam φ c ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  obtain ⟨N, hN, hNneg, hN1⟩ := ((eventually_posDef_of_resolutionBottom_pos hφ hsupp hM hc hβ₀
    hres hlam hpos).and (hneg.and (eventually_ge_atTop 1))).exists
  set x : EuclideanSpace ℝ (PrimeHorizonIndex N) := WithLp.toLp 2 (fun n => y n) with hx
  have hx0 : x ≠ 0 := by
    intro h0
    have h1 : x ⟨1, mem_Icc.mpr ⟨le_rfl, hN1⟩⟩ = 0 := by rw [h0]; rfl
    exact hy1 h1
  have hpd := hN.2
  have hinner : 0 < ⟪toEuclideanLin (twistedCompleteWeilMatrix lam φ c N) x, x⟫ := by
    have hA := twistedCompleteWeilMatrix_isHermitian lam φ c N
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    have hev := hA.posDef_iff_eigenvalues_pos.mp hN
    have hsum := hA.eigenvectorBasis.sum_sq_inner_left x
    have hnz : ∃ i, ⟪x, hA.eigenvectorBasis i⟫ ≠ 0 := by
      by_contra hall
      push_neg at hall
      have : ‖x‖ ^ 2 = 0 := by rw [← hsum]; simp [hall]
      exact hx0 (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this))
    obtain ⟨i, hi⟩ := hnz
    refine lt_of_lt_of_le (mul_pos (hev i) (pow_pos (abs_pos.mpr hi) 2 |>.trans_eq (sq_abs _)))
      (single_le_sum (fun j _ => mul_nonneg (hev j).le (sq_nonneg _)) (mem_univ i))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc hN0
  have hG0 : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  rw [inner_twistedCompleteWeilMatrix hφ hsupp hc hN1,
    atomicTest_congr (x' := y) (fun n hn => by
      rw [primeHorizonExtension, dif_pos hn]; rfl)] at hinner
  have := (div_pos_iff_of_pos_right hG0).mp hinner
  linarith

end Bottom

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
