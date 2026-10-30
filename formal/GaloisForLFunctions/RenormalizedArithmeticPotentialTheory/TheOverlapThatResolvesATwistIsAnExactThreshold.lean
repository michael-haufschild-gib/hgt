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
  RenormalizedBiarithmeticGeometry CompletedShell ArithmeticCastelnuovoSeveri Zeta23
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
  have h : ∀ k : ℕ, twistDefect lam k / Real.sqrt k * (s ^ 2 * shiftMean y P k) =
      s ^ 2 * (twistDefect lam k / Real.sqrt k * shiftMean y P k) := fun k => by ring
  simp only [h, tsum_mul_left]
  ring

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
  have : 0 ≤ ∑' k, |twistDefect lam k| := tsum_nonneg fun k => abs_nonneg _
  unfold twistBound
  positivity

theorem twistBound_mono (lam : ℕ → ℝ) {c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') :
    twistBound lam c ≤ twistBound lam c' := by
  have h0 : 0 ≤ ∑' k, |twistDefect lam k| := tsum_nonneg fun k => abs_nonneg _
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
      (single_le_sum (f := fun j => hA.eigenvalues j * ⟪x, hA.eigenvectorBasis j⟫ ^ 2)
        (fun j _ => mul_nonneg (hev j).le (sq_nonneg _)) (mem_univ i))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc hN0
  have hG0 : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  rw [inner_twistedCompleteWeilMatrix hφ hsupp hc hN1,
    atomicTest_congr (x' := y) (fun n hn => by
      rw [primeHorizonExtension, dif_pos hn])] at hinner
  have := (div_pos_iff_of_pos_right hG0).mp hinner
  linarith

end Bottom

/-! ### Monotonicity in the overlap -/

section Monotone

variable {lam : ℕ → ℝ} {φ : ℝ → ℝ}

theorem setIntegral_Ioi_shellSpectrum_anti (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {a a' : ℝ} (h : a ≤ a') :
    ∫ t in Set.Ioi a', shellSpectrum φ t ≤ ∫ t in Set.Ioi a, shellSpectrum φ t :=
  setIntegral_mono_set (CriticalArithmeticCorrelationTheory.integrableOn_shellSpectrum_Ioi hφ
    (hasCompactSupport_of_unitSupport hsupp) a) (ae_of_all _ fun t => shellSpectrum_nonneg t)
    (Eventually.of_forall (Set.Ioi_subset_Ioi h))

/-- Without real Fourier zeros the spectral tail strictly decreases. -/
theorem setIntegral_Ioi_shellSpectrum_strictAnti (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    {a a' : ℝ} (h : a < a') :
    ∫ t in Set.Ioi a', shellSpectrum φ t < ∫ t in Set.Ioi a, shellSpectrum φ t := by
  have hφc := hasCompactSupport_of_unitSupport hsupp
  have hint := CriticalArithmeticCorrelationTheory.integrableOn_shellSpectrum_Ioi hφ hφc a
  have hcont := continuous_shellSpectrum hφ.continuous hφc
  have hP : ∀ t : ℝ, 0 < shellSpectrum φ t := fun t =>
    sq_pos_of_pos (norm_pos_iff.mpr (hFT (2 * Real.pi * t)))
  have hsplit : ∫ t in Set.Ioi a, shellSpectrum φ t =
      (∫ t in Set.Ioc a a', shellSpectrum φ t) + ∫ t in Set.Ioi a', shellSpectrum φ t := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi h.le)),
      Set.Ioc_union_Ioi_eq_Ioi h.le]
  have hpos : 0 < ∫ t in Set.Ioc a a', shellSpectrum φ t := by
    rw [← intervalIntegral.integral_of_le h.le]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable a a')
      (fun t _ => hP t) h
  linarith

/-- The completed conductor energies decrease in the overlap. -/
theorem completedConductorEnergy_anti (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c c' : ℝ} (hc : 0 < c)
    (hcc : c ≤ c') {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy φ c' m ≤ completedConductorEnergy φ c m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine hasSum_le (fun n => ?_) (hasSum_completedConductorEnergy hφ hsupp hM (hc.trans_le hcc) hm)
    (hasSum_completedConductorEnergy hφ hsupp hM hc hm)
  split_ifs
  · refine mul_le_mul_of_nonneg_left (setIntegral_Ioi_shellSpectrum_anti hφ hsupp ?_)
      (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcc (by positivity)) hm0.le
  · exact le_rfl

/-- Without real Fourier zeros the completed conductor energies strictly decrease. -/
theorem completedConductorEnergy_strictAnti (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    {c c' : ℝ} (hc : 0 < c) (hcc : c < c') {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy φ c' m < completedConductorEnergy φ c m := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  refine hasSum_lt (i := 0) (fun n => ?_) ?_
    (hasSum_completedConductorEnergy hφ hsupp hM (hc.trans hcc) hm)
    (hasSum_completedConductorEnergy hφ hsupp hM hc hm)
  · simp only
    split_ifs
    · refine mul_le_mul_of_nonneg_left (setIntegral_Ioi_shellSpectrum_anti hφ hsupp ?_)
        (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcc.le (by positivity)) hm0.le
    · exact le_rfl
  · simp only [Nat.coprime_one_right_eq_true, if_true, Nat.cast_zero, zero_add]
    refine mul_lt_mul_of_pos_left (setIntegral_Ioi_shellSpectrum_strictAnti hφ hsupp hFT ?_)
      (by positivity)
    exact div_lt_div_of_pos_right (by linarith) hm0

theorem packetEnergy_anti (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') {T : Finset ℕ}
    (hT : ∀ m ∈ T, 0 < m) (β : ℕ → ℝ) :
    packetEnergy lam φ c' T β ≤ packetEnergy lam φ c T β := by
  unfold packetEnergy
  have := sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
    (completedConductorEnergy_anti hφ hsupp hM hc hcc (hT m hm)) (sq_nonneg (β m))
  linarith

/-- **The resolution bottom decreases in the overlap.** -/
theorem resolutionBottom_antitone (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hlam : Summable fun k => |twistDefect lam k|) {c c' : ℝ}
    (hc : 0 < c) (hcc : c ≤ c') :
    resolutionBottom lam φ c' ≤ resolutionBottom lam φ c :=
  le_resolutionBottom fun T hT β hβ =>
    (resolutionBottom_le_packetEnergy hφ hsupp hM (hc.trans_le hcc) hlam hT hβ).trans
      (packetEnergy_anti hφ hsupp hM hc hcc hT β)

theorem exists_pos_le_of_finset {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ m ∈ s, 0 < f m) :
    ∃ g : ℝ, 0 < g ∧ ∀ m ∈ s, g ≤ f m := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨g, hg, hgs⟩ := ih fun m hm => h m (mem_insert_of_mem hm)
    refine ⟨min (f a) g, lt_min (h a (mem_insert_self a s)) hg, fun m hm => ?_⟩
    rcases mem_insert.mp hm with rfl | hm'
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hgs m hm')

/-- **Strictly past zero.** For a profile without real Fourier zeros, `λ_λ(c) ≤ 0` forces
`λ_λ(c') < 0` at every larger overlap: a near-minimizing unit packet keeps half its mass on the
finitely many conductors of energy `< 2·twistBound + 2`, where each energy drops by a fixed
amount. -/
theorem resolutionBottom_neg_of_lt (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    (hlam : Summable fun k => |twistDefect lam k|) {c c' : ℝ} (hc : 0 < c) (hcc : c < c')
    (hle : resolutionBottom lam φ c ≤ 0) : resolutionBottom lam φ c' < 0 := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  obtain ⟨B, hB⟩ : ∃ B, B = twistBound lam c := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact twistBound_nonneg lam hc.le
  have hfin := finite_completedConductorEnergy_sublevel φ hc (2 * B + 2)
  obtain ⟨g, hg, hgF⟩ := exists_pos_le_of_finset (s := hfin.toFinset)
    (f := fun m => completedConductorEnergy φ c m - completedConductorEnergy φ c' m)
    fun m hm => sub_pos.mpr (completedConductorEnergy_strictAnti hφ hsupp hFT hc hcc
      (hfin.mem_toFinset.mp hm).1)
  obtain ⟨η, hη⟩ : ∃ η, η = min (g / 4) 1 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min (by positivity) one_pos
  have hηg : η ≤ g / 4 := by rw [hη]; exact min_le_left _ _
  have hη1 : η ≤ 1 := by rw [hη]; exact min_le_right _ _
  obtain ⟨E, ⟨T, hT, β, hβ, rfl⟩, hE⟩ := exists_lt_of_csInf_lt
    (unitPacketEnergies_nonempty lam φ c)
    (show resolutionBottom lam φ c < resolutionBottom lam φ c + η by linarith)
  have hTLE := (abs_le.mp (abs_twistLimitEnergy_packet_le hφ hsupp hM hc hlam hT β)).1
  rw [hβ, mul_one, ← hB] at hTLE
  have hEsum : ∑ m ∈ T, β m ^ 2 * completedConductorEnergy φ c m ≤ η + B := by
    unfold packetEnergy at hE
    linarith
  set F := hfin.toFinset with hF
  -- the mass off the low conductors is at most one half
  have hoff : ∑ m ∈ T.filter (· ∉ F), β m ^ 2 ≤ 1 / 2 := by
    have hK : (2 * B + 2) * ∑ m ∈ T.filter (· ∉ F), β m ^ 2 ≤
        ∑ m ∈ T, β m ^ 2 * completedConductorEnergy φ c m := by
      calc (2 * B + 2) * ∑ m ∈ T.filter (· ∉ F), β m ^ 2
          = ∑ m ∈ T.filter (· ∉ F), β m ^ 2 * (2 * B + 2) := by rw [mul_sum]; ring_nf
        _ ≤ ∑ m ∈ T.filter (· ∉ F), β m ^ 2 * completedConductorEnergy φ c m := by
            refine sum_le_sum fun m hm => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            obtain ⟨hmT, hmF⟩ := mem_filter.mp hm
            by_contra hlt
            push_neg at hlt
            exact hmF (hfin.mem_toFinset.mpr ⟨hT m hmT, hlt⟩)
        _ ≤ ∑ m ∈ T, β m ^ 2 * completedConductorEnergy φ c m :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun m hm _ =>
              mul_nonneg (sq_nonneg _) (completedConductorEnergy_nonneg hφ hsupp hM hc (hT m hm))
    have hS0 : 0 ≤ ∑ m ∈ T.filter (· ∉ F), β m ^ 2 := sum_nonneg fun m _ => sq_nonneg _
    nlinarith
  have hon : 1 / 2 ≤ ∑ m ∈ T.filter (· ∈ F), β m ^ 2 := by
    have := sum_filter_add_sum_filter_not T (· ∈ F) (fun m => β m ^ 2)
    rw [hβ] at this
    linarith
  -- each low conductor loses at least `g`
  have hdrop : g / 2 ≤ ∑ m ∈ T, β m ^ 2 *
      (completedConductorEnergy φ c m - completedConductorEnergy φ c' m) := by
    calc g / 2 ≤ g * ∑ m ∈ T.filter (· ∈ F), β m ^ 2 := by nlinarith
      _ = ∑ m ∈ T.filter (· ∈ F), β m ^ 2 * g := by rw [mul_sum]; ring_nf
      _ ≤ ∑ m ∈ T.filter (· ∈ F), β m ^ 2 *
            (completedConductorEnergy φ c m - completedConductorEnergy φ c' m) :=
          sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hgF m (mem_filter.mp hm).2)
            (sq_nonneg _)
      _ ≤ ∑ m ∈ T, β m ^ 2 *
            (completedConductorEnergy φ c m - completedConductorEnergy φ c' m) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun m hm _ =>
            mul_nonneg (sq_nonneg _) (sub_nonneg.mpr
              (completedConductorEnergy_anti hφ hsupp hM hc hcc.le (hT m hm)))
  have hpE' : packetEnergy lam φ c' T β = packetEnergy lam φ c T β -
      ∑ m ∈ T, β m ^ 2 * (completedConductorEnergy φ c m - completedConductorEnergy φ c' m) := by
    unfold packetEnergy
    simp only [mul_sub, sum_sub_distrib]
    ring
  calc resolutionBottom lam φ c' ≤ packetEnergy lam φ c' T β :=
        resolutionBottom_le_packetEnergy hφ hsupp hM (hc.trans hcc) hlam hT hβ
    _ < 0 := by rw [hpE']; linarith

end Monotone

/-! ### The exact threshold -/

section Threshold

variable {lam : ℕ → ℝ} {φ : ℝ → ℝ}

/-- The **resolution threshold** `c_0(λ) = sup {c > 0 : λ_λ(c) > 0}`. -/
def resolutionThreshold (lam : ℕ → ℝ) (φ : ℝ → ℝ) : ℝ :=
  sSup {c : ℝ | 0 < c ∧ 0 < resolutionBottom lam φ c}

/-- Small overlaps resolve nothing: the pole energy `E(c) ≥ log(1/(2πc)) + O(1)` exceeds every
bounded twist. -/
theorem exists_resolutionBottom_pos (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    (hlam : Summable fun k => |twistDefect lam k|) :
    ∃ c : ℝ, 0 < c ∧ 0 < resolutionBottom lam φ c := by
  obtain ⟨R, hR⟩ : ∃ R, R = bumpRobin φ 1 / (∫ u, φ u ^ 2) + ramanujanAdjunctionEnergy 1 -
      Real.eulerMascheroniConstant := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = max 0 (twistBound lam 1 - R + 1) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; exact le_max_left _ _
  have hXR : twistBound lam 1 - R + 1 ≤ X := by rw [hX]; exact le_max_right _ _
  set c := Real.exp (-X) / (2 * Real.pi) with hcdef
  have hpi : 0 < 2 * Real.pi := by positivity
  have hc : 0 < c := div_pos (Real.exp_pos _) hpi
  have hc1 : c ≤ 1 := by
    rw [hcdef, div_le_one hpi]
    have h1 : Real.exp (-X) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    linarith
  refine ⟨c, hc, lt_of_lt_of_le ?_ (completedShellEnergy_sub_le_resolutionBottom hφ hsupp hM hc
    hlam)⟩
  have hE : completedShellEnergy φ c = completeWeilAdjunctionEnergy φ c 1 := by
    rw [← completedConductorEnergy_one, completedConductorEnergy_eq_adjunction hc hc1 one_pos]
  have hlog : Real.log (1 / (2 * Real.pi * c)) = X := by
    rw [hcdef, mul_div_cancel₀ _ hpi.ne', one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hpole := completeWeilPoleShift_nonneg φ hc.le
  have hbd := twistBound_mono lam hc.le hc1
  rw [hE]
  unfold completeWeilAdjunctionEnergy completeWeilSelfFinitePart
  rw [hlog, if_pos rfl]
  linarith

/-- **The exact resolution threshold.** Let `φ` have no real Fourier zeros and let the twist
`λ`, of summable defect, be seen at some overlap `c₁`. Then `0 < c_0(λ) ≤ c₁`; at every overlap
below `c_0(λ)` the twisted complete Weil matrix is eventually positive definite, and at every
overlap above it a unit Ramanujan packet makes the twisted form eventually negative. -/
theorem resolutionThreshold_spec (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    (hlam : Summable fun k => |twistDefect lam k|) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hseen : resolutionBottom lam φ c₁ < 0) :
    0 < resolutionThreshold lam φ ∧ resolutionThreshold lam φ ≤ c₁ ∧
      (∀ c, 0 < c → c < resolutionThreshold lam φ →
        ∀ᶠ N : ℕ in atTop, (twistedCompleteWeilMatrix lam φ c N).PosDef) ∧
      (∀ c, resolutionThreshold lam φ < c →
        ∃ T : Finset ℕ, (∀ m ∈ T, 0 < m) ∧ ∃ β : ℕ → ℝ, ∑ m ∈ T, β m ^ 2 = 1 ∧
          ∀ᶠ N : ℕ in atTop, weilQuadTw lam
            (atomicTest N (packetCoeff (packetProfile T β) N) (atomDilate φ (c / N))) < 0) := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  set S := {c : ℝ | 0 < c ∧ 0 < resolutionBottom lam φ c} with hS
  have hbdd : BddAbove S := by
    refine ⟨c₁, fun c hc => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := resolutionBottom_antitone hφ hsupp hM hlam hc₁ hlt.le
    linarith [hc.2]
  obtain ⟨c₀, hc₀, hpos₀⟩ := exists_resolutionBottom_pos hφ hsupp hM hlam
  have hmem₀ : c₀ ∈ S := ⟨hc₀, hpos₀⟩
  have hne : S.Nonempty := ⟨c₀, hmem₀⟩
  refine ⟨hc₀.trans_le (le_csSup hbdd hmem₀), csSup_le hne fun c hc => ?_, ?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    have := resolutionBottom_antitone hφ hsupp hM hlam hc₁ hlt.le
    linarith [hc.2]
  · intro c hc hlt
    obtain ⟨c', ⟨hc', hpos'⟩, hcc'⟩ := exists_lt_of_lt_csSup hne hlt
    have hpos : 0 < resolutionBottom lam φ c :=
      hpos'.trans_le (resolutionBottom_antitone hφ hsupp hM hlam hc hcc'.le)
    obtain ⟨a₀, β₀, hβ₀, hres⟩ :=
      CriticalArithmeticCorrelationTheory.exists_noRealZero_completeWeilEnergy_reserve hφ hsupp
        hFT hc
    exact eventually_posDef_of_resolutionBottom_pos hφ hsupp hM hc hβ₀ hres hlam hpos
  · intro c hlt
    have hth : 0 < resolutionThreshold lam φ := hc₀.trans_le (le_csSup hbdd hmem₀)
    set c'' := (resolutionThreshold lam φ + c) / 2 with hc''
    have hc''0 : 0 < c'' := by rw [hc'']; linarith
    have hc''c : c'' < c := by rw [hc'']; linarith
    have hnot : c'' ∉ S := fun hmem => by
      have := le_csSup hbdd hmem
      have h' : sSup S = resolutionThreshold lam φ := rfl
      rw [hc'', h'] at this
      linarith
    have hle : resolutionBottom lam φ c'' ≤ 0 := by
      by_contra hgt
      push_neg at hgt
      exact hnot ⟨hc''0, hgt⟩
    have hneg := resolutionBottom_neg_of_lt hφ hsupp hFT hlam hc''0 hc''c hle
    exact exists_eventually_neg_of_resolutionBottom_neg hφ hsupp hM (hc''0.trans hc''c) hlam hneg

end Threshold

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
