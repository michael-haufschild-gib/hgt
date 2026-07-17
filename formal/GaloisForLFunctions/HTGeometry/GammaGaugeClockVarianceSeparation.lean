import GaloisForLFunctions.HTGeometry.GammaFactorialObservabilitySpectrum

/-!
# Gamma gauge clocks and factorial reporter clocks have different variance

Every positive derivative tail of a period-one Fourier mode belongs to the maximal domain on
which the cyclic Gamma conormals can be paired.  Nonconstant mode tails nevertheless fail to be
square-summable, so they are not vectors in the Hilbert space on which the factorial observability
operator acts.

The exact pure-mode intersection consists only of the constant mode.  Thus the Gamma conormal
domain cannot be identified coordinatewise with the factorial reporter Hilbert space.  A reporter
for the actual periodic gauge must instead be formulated across distinct variance spaces.
-/

open Complex Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Gamma Fourier frequency norm dominates its mode number. -/
theorem natCast_le_norm_gammaPeriodicFrequency (m : ℕ) :
    (m : ℝ) ≤ ‖gammaPeriodicFrequency m‖ := by
  rw [gammaPeriodicFrequency, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_natCast, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, norm_I, mul_one]
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  simpa using mul_le_mul_of_nonneg_left hpi (Nat.cast_nonneg m)

/-- Every nonzero period-one Fourier frequency has norm at least one. -/
theorem one_le_norm_gammaPeriodicFrequency {m : ℕ} (hm : m ≠ 0) :
    1 ≤ ‖gammaPeriodicFrequency m‖ := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have hm1r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  exact hm1r.trans (natCast_le_norm_gammaPeriodicFrequency m)

/-- The derivative tail of a periodic mode, measured in the Hilbert pivot of radial scale `rho`. -/
def gammaPeriodicModeRadialTail (rho : ℝ) (m : ℕ) : ℕ → ℂ :=
  fun n => (gammaPeriodicFrequency m / (rho : ℂ)) ^ (n + 1)

private lemma summable_normSq_pow_succ_iff_norm_lt_one (q : ℂ) :
    Summable (fun n : ℕ => ‖q ^ (n + 1)‖ ^ 2) ↔ ‖q‖ < 1 := by
  have hseq : (fun n : ℕ => ‖q ^ (n + 1)‖ ^ 2) =
      fun n : ℕ => (‖q‖ ^ 2) ^ (n + 1) := by
    funext n
    rw [norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hseq, summable_nat_add_iff 1, summable_geometric_iff_norm_lt_one]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖q‖)]
  constructor <;> intro h <;> nlinarith [norm_nonneg q]

/-- **Exact Gamma variance horizon.**  At radial scale `rho`, the `m`-th periodic gauge mode is a
square-summable clock exactly after the scale crosses the norm of its Fourier frequency. -/
theorem summable_normSq_gammaPeriodicModeRadialTail_iff
    {rho : ℝ} (hrho : 0 < rho) (m : ℕ) :
    Summable (fun n : ℕ => ‖gammaPeriodicModeRadialTail rho m n‖ ^ 2) ↔
      ‖gammaPeriodicFrequency m‖ < rho := by
  change Summable (fun n : ℕ =>
    ‖(gammaPeriodicFrequency m / (rho : ℂ)) ^ (n + 1)‖ ^ 2) ↔ _
  rw [summable_normSq_pow_succ_iff_norm_lt_one, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hrho]
  exact div_lt_one hrho

/-- Every pure periodic gauge mode enters some finite radial Hilbert pivot. -/
theorem exists_radialPivot_summable_gammaPeriodicMode (m : ℕ) :
    ∃ rho : ℝ, 0 < rho ∧
      Summable (fun n : ℕ => ‖gammaPeriodicModeRadialTail rho m n‖ ^ 2) := by
  refine ⟨‖gammaPeriodicFrequency m‖ + 1, by positivity, ?_⟩
  rw [summable_normSq_gammaPeriodicModeRadialTail_iff (by positivity)]
  linarith

/-- No fixed radial Hilbert pivot contains all pure periodic Gamma gauge modes. -/
theorem exists_gammaPeriodicMode_not_summable_at_radialPivot
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ m : ℕ,
      ¬ Summable (fun n : ℕ => ‖gammaPeriodicModeRadialTail rho m n‖ ^ 2) := by
  obtain ⟨m, hm⟩ := exists_nat_gt rho
  refine ⟨m, ?_⟩
  rw [summable_normSq_gammaPeriodicModeRadialTail_iff hrho]
  exact not_lt_of_ge (le_trans (le_of_lt hm) (natCast_le_norm_gammaPeriodicFrequency m))

/-! ## Exact radial filtration of every finite Fourier packet -/

/-- The finite Gamma Fourier-jet Vandermonde map as a linear map. -/
def gammaPeriodicFourierJetLinearMap (r : ℕ) :
    (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
  (Matrix.vandermonde (fun m : Fin r => gammaPeriodicFrequency m)).vecMulLinear

@[simp] theorem gammaPeriodicFourierJetLinearMap_apply
    {r : ℕ} (a : Fin r → ℂ) :
    gammaPeriodicFourierJetLinearMap r a = gammaPeriodicFourierJet a := by
  rfl

theorem gammaPeriodicFourierJetLinearMap_bijective (r : ℕ) :
    Function.Bijective (gammaPeriodicFourierJetLinearMap r) := by
  constructor
  · intro a b hab
    obtain ⟨x, hx, huniq⟩ :=
      existsUnique_gammaPeriodicFourierJet (gammaPeriodicFourierJet a)
    exact (huniq a (fun _ => rfl)).trans (huniq b (fun n => by
      have hn := congrFun hab n
      simpa [gammaPeriodicFourierJetLinearMap_apply] using hn.symm)).symm
  · intro c
    obtain ⟨a, ha, _⟩ := existsUnique_gammaPeriodicFourierJet c
    refine ⟨a, ?_⟩
    rw [gammaPeriodicFourierJetLinearMap_apply]
    exact funext ha

/-- Finite Fourier jets give a continuous linear coordinate equivalence.  Its inverse separates
the modal components of a packet from any block of as many consecutive clock readings. -/
def gammaPeriodicFourierJetContinuousLinearEquiv (r : ℕ) :
    (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ) :=
  (LinearEquiv.ofBijective (gammaPeriodicFourierJetLinearMap r)
    (gammaPeriodicFourierJetLinearMap_bijective r)).toContinuousLinearEquiv

@[simp] theorem gammaPeriodicFourierJetContinuousLinearEquiv_apply
    {r : ℕ} (a : Fin r → ℂ) :
    gammaPeriodicFourierJetContinuousLinearEquiv r a = gammaPeriodicFourierJet a := by
  rfl

private lemma tendsto_zero_of_summable_normSq {f : ℕ → ℂ}
    (hf : Summable (fun n => ‖f n‖ ^ 2)) :
    Tendsto f atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun n => ‖f n‖ ^ 2) atTop (𝓝 0) :=
    hf.tendsto_atTop_zero
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  convert hsqrt using 1
  · funext n
    rw [Function.comp_apply, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg (f n))]
  · simp

/-- A finite periodic Fourier packet measured in the radial Hilbert pivot of scale `rho`. -/
def gammaPeriodicFourierRadialTail {r : ℕ}
    (rho : ℝ) (a : Fin r → ℂ) : ℕ → ℂ :=
  fun n => ∑ m : Fin r,
    a m * (gammaPeriodicFrequency m / (rho : ℂ)) ^ (n + 1)

/-- A block of consecutive radial clock readings is exactly the Gamma Fourier jet of the current
modal-component vector. -/
theorem gammaPeriodicFourierJet_modalComponent_eq_radialBlock
    {r : ℕ} {rho : ℝ} (hrho : rho ≠ 0) (a : Fin r → ℂ) (n : ℕ) (j : Fin r) :
    gammaPeriodicFourierJet
        (fun m => a m *
          (gammaPeriodicFrequency m / (rho : ℂ)) ^ (n + 1)) j =
      (rho : ℂ) ^ (j : ℕ) *
        gammaPeriodicFourierRadialTail rho a (n + (j : ℕ)) := by
  rw [gammaPeriodicFourierJet, gammaPeriodicFourierRadialTail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [show n + (j : ℕ) + 1 = (n + 1) + (j : ℕ) by omega, pow_add]
  have hscale :
      (rho : ℂ) ^ (j : ℕ) *
          (gammaPeriodicFrequency m / (rho : ℂ)) ^ (j : ℕ) =
        gammaPeriodicFrequency m ^ (j : ℕ) := by
    rw [← mul_pow]
    field_simp [hrho]
  rw [← hscale]
  ring

/-- Square summability of a finite radial packet forces every individual modal component to tend
to zero.  The proof uses the continuous inverse of the finite Gamma Vandermonde jet map. -/
theorem gammaPeriodicFourierRadialComponent_tendsto_zero
    {r : ℕ} {rho : ℝ} (hrho : 0 < rho) (a : Fin r → ℂ)
    (hsum : Summable (fun n : ℕ =>
      ‖gammaPeriodicFourierRadialTail rho a n‖ ^ 2)) (m : Fin r) :
    Tendsto
      (fun n : ℕ => a m *
        (gammaPeriodicFrequency m / (rho : ℂ)) ^ (n + 1))
      atTop (𝓝 0) := by
  have hpacket : Tendsto (gammaPeriodicFourierRadialTail rho a) atTop (𝓝 0) :=
    tendsto_zero_of_summable_normSq hsum
  let block : ℕ → Fin r → ℂ := fun n j =>
    (rho : ℂ) ^ (j : ℕ) *
      gammaPeriodicFourierRadialTail rho a (n + (j : ℕ))
  have hblock : Tendsto block atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro j
    have hj := (hpacket.comp (tendsto_add_atTop_nat (j : ℕ))).const_mul
      ((rho : ℂ) ^ (j : ℕ))
    simpa [block] using hj
  let component : ℕ → Fin r → ℂ := fun n m =>
    a m * (gammaPeriodicFrequency m / (rho : ℂ)) ^ (n + 1)
  have hrecover : ∀ n,
      (gammaPeriodicFourierJetContinuousLinearEquiv r).symm (block n) = component n := by
    intro n
    rw [← (gammaPeriodicFourierJetContinuousLinearEquiv r).symm_apply_apply (component n)]
    congr 1
    ext j
    rw [gammaPeriodicFourierJetContinuousLinearEquiv_apply]
    exact (gammaPeriodicFourierJet_modalComponent_eq_radialBlock hrho.ne' a n j).symm
  have hcomponent : Tendsto component atTop (𝓝 0) := by
    have hmap :=
      (gammaPeriodicFourierJetContinuousLinearEquiv r).symm.continuous.continuousAt.tendsto.comp
        hblock
    have hmap' : Tendsto
        (fun n => (gammaPeriodicFourierJetContinuousLinearEquiv r).symm (block n))
        atTop (𝓝 0) := by
      simpa only [Function.comp_apply, map_zero] using hmap
    exact hmap'.congr' (Eventually.of_forall hrecover)
  exact (tendsto_pi_nhds.mp hcomponent) m

private lemma mem_lpSubmodule_two_iff (f : ℕ → ℂ) :
    f ∈ lpSubmodule ℂ (fun _ : ℕ => ℂ) 2 ↔
      Summable (fun n => ‖f n‖ ^ 2) := by
  rw [lpSubmodule]
  change Memℓp f 2 ↔ _
  rw [memℓp_gen_iff (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  apply summable_congr
  intro n
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private lemma gammaPeriodicFourierRadialTail_summable_of_active_frequency_lt
    {r : ℕ} {rho : ℝ} (hrho : 0 < rho) (a : Fin r → ℂ)
    (hactive : ∀ m, a m ≠ 0 → ‖gammaPeriodicFrequency m‖ < rho) :
    Summable (fun n : ℕ => ‖gammaPeriodicFourierRadialTail rho a n‖ ^ 2) := by
  rw [← mem_lpSubmodule_two_iff]
  have hfun : gammaPeriodicFourierRadialTail rho a =
      ∑ m : Fin r, fun n : ℕ =>
        a m * (gammaPeriodicFrequency m / (rho : ℂ)) ^ (n + 1) := by
    funext n
    simp [gammaPeriodicFourierRadialTail]
  rw [hfun]
  apply Submodule.sum_mem
  intro m hm
  apply (mem_lpSubmodule_two_iff (fun n : ℕ =>
    a m * (gammaPeriodicFrequency m / (rho : ℂ)) ^ (n + 1))).2
  by_cases ha : a m = 0
  · simp [ha]
  · have hq : ‖gammaPeriodicFrequency m / (rho : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho]
      exact (div_lt_one hrho).mpr (hactive m ha)
    have hs := (summable_normSq_pow_succ_iff_norm_lt_one
      (gammaPeriodicFrequency m / (rho : ℂ))).mpr hq
    apply (hs.mul_left (‖a m‖ ^ 2)).congr
    intro n
    rw [norm_mul]
    ring

private lemma coefficient_eq_zero_of_tendsto_scaledPowers
    {a q : ℂ} (hq : 1 ≤ ‖q‖)
    (hzero : Tendsto (fun n : ℕ => a * q ^ (n + 1)) atTop (𝓝 0)) :
    a = 0 := by
  have hnorm : Tendsto (fun n : ℕ => ‖a * q ^ (n + 1)‖) atTop (𝓝 0) := by
    simpa using hzero.norm
  have hlower : ∀ n : ℕ, ‖a‖ ≤ ‖a * q ^ (n + 1)‖ := by
    intro n
    rw [norm_mul, norm_pow]
    simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ hq) (norm_nonneg a)
  have ha0 : ‖a‖ ≤ 0 :=
    ge_of_tendsto hnorm (Eventually.of_forall hlower)
  exact norm_eq_zero.mp (le_antisymm ha0 (norm_nonneg a))

/-- **Finite-packet Gamma variance horizon.**  A radial finite Fourier packet is square-summable
exactly when every active Fourier frequency lies strictly below the radial scale.  No cancellation
between distinct modes can move the entry wall. -/
theorem summable_normSq_gammaPeriodicFourierRadialTail_iff
    {r : ℕ} {rho : ℝ} (hrho : 0 < rho) (a : Fin r → ℂ) :
    Summable (fun n : ℕ => ‖gammaPeriodicFourierRadialTail rho a n‖ ^ 2) ↔
      ∀ m, a m ≠ 0 → ‖gammaPeriodicFrequency m‖ < rho := by
  constructor
  · intro hsum m ha
    by_contra hfreq
    have hfreq' : rho ≤ ‖gammaPeriodicFrequency m‖ := le_of_not_gt hfreq
    have hq : 1 ≤ ‖gammaPeriodicFrequency m / (rho : ℂ)‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho]
      exact (one_le_div hrho).mpr hfreq'
    exact ha (coefficient_eq_zero_of_tendsto_scaledPowers hq
      (gammaPeriodicFourierRadialComponent_tendsto_zero hrho a hsum m))
  · exact gammaPeriodicFourierRadialTail_summable_of_active_frequency_lt hrho a

/-- Every finite Gamma Fourier packet enters the radial Hilbert system at some finite scale. -/
theorem exists_radialPivot_summable_gammaPeriodicFourierRadialTail
    {r : ℕ} (a : Fin r → ℂ) :
    ∃ rho : ℝ, 0 < rho ∧
      Summable (fun n : ℕ => ‖gammaPeriodicFourierRadialTail rho a n‖ ^ 2) := by
  let rho : ℝ := (∑ m : Fin r, ‖gammaPeriodicFrequency m‖) + 1
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  refine ⟨rho, hrho, (summable_normSq_gammaPeriodicFourierRadialTail_iff hrho a).2 ?_⟩
  intro m hm
  have hle : ‖gammaPeriodicFrequency m‖ ≤
      ∑ j : Fin r, ‖gammaPeriodicFrequency j‖ := by
    simpa using Finset.single_le_sum (s := Finset.univ) (a := m)
      (fun (j : Fin r) _ => norm_nonneg (gammaPeriodicFrequency j))
      (Finset.mem_univ m)
  dsimp [rho]
  linarith

/-- Coefficient packets supported strictly below the radial variance wall. -/
def gammaPeriodicFourierRadialCoefficientSpace (rho : ℝ) (r : ℕ) :
    Submodule ℂ (Fin r → ℂ) where
  carrier := {a | ∀ m : Fin r, rho ≤ ‖gammaPeriodicFrequency m‖ → a m = 0}
  zero_mem' := by intro m hm; rfl
  add_mem' := by
    intro a b ha hb m hm
    simp [ha m hm, hb m hm]
  smul_mem' := by
    intro c a ha m hm
    simp [ha m hm]

theorem mem_gammaPeriodicFourierRadialCoefficientSpace_iff
    {rho : ℝ} {r : ℕ} (a : Fin r → ℂ) :
    a ∈ gammaPeriodicFourierRadialCoefficientSpace rho r ↔
      ∀ m, a m ≠ 0 → ‖gammaPeriodicFrequency m‖ < rho := by
  change (∀ m : Fin r, rho ≤ ‖gammaPeriodicFrequency m‖ → a m = 0) ↔ _
  constructor
  · intro h m ham
    by_contra hfreq
    exact ham (h m (le_of_not_gt hfreq))
  · intro h m hfreq
    by_contra ham
    exact (not_lt_of_ge hfreq) (h m ham)

/-- Radial square summability is exactly membership in the frequency-cut coefficient space. -/
theorem summable_normSq_gammaPeriodicFourierRadialTail_iff_mem
    {r : ℕ} {rho : ℝ} (hrho : 0 < rho) (a : Fin r → ℂ) :
    Summable (fun n : ℕ => ‖gammaPeriodicFourierRadialTail rho a n‖ ^ 2) ↔
      a ∈ gammaPeriodicFourierRadialCoefficientSpace rho r := by
  rw [summable_normSq_gammaPeriodicFourierRadialTail_iff hrho,
    mem_gammaPeriodicFourierRadialCoefficientSpace_iff]

/-- The radial coefficient spaces form an increasing filtration. -/
theorem gammaPeriodicFourierRadialCoefficientSpace_mono
    {rho sigma : ℝ} (h : rho ≤ sigma) (r : ℕ) :
    gammaPeriodicFourierRadialCoefficientSpace rho r ≤
      gammaPeriodicFourierRadialCoefficientSpace sigma r := by
  intro a ha
  change ∀ m : Fin r, sigma ≤ ‖gammaPeriodicFrequency m‖ → a m = 0
  intro m hm
  exact ha m (h.trans hm)

/-- Crossing an actual Gamma frequency strictly enlarges the radial coefficient space. -/
theorem gammaPeriodicFourierRadialCoefficientSpace_lt_of_crossing
    {rho sigma : ℝ} {r : ℕ} (m : Fin r)
    (hleft : rho ≤ ‖gammaPeriodicFrequency m‖)
    (hright : ‖gammaPeriodicFrequency m‖ < sigma) :
    gammaPeriodicFourierRadialCoefficientSpace rho r <
      gammaPeriodicFourierRadialCoefficientSpace sigma r := by
  have hle := gammaPeriodicFourierRadialCoefficientSpace_mono (hleft.trans hright.le) r
  apply lt_of_le_of_ne hle
  intro heq
  have hback : gammaPeriodicFourierRadialCoefficientSpace sigma r ≤
      gammaPeriodicFourierRadialCoefficientSpace rho r := by rw [heq]
  let e : Fin r → ℂ := Pi.single m 1
  have heSigma : e ∈ gammaPeriodicFourierRadialCoefficientSpace sigma r := by
    rw [mem_gammaPeriodicFourierRadialCoefficientSpace_iff]
    intro j hj
    by_cases hjm : j = m
    · subst j
      exact hright
    · exfalso
      apply hj
      simp [e, hjm]
  have heRho := hback heSigma
  have hmode := (mem_gammaPeriodicFourierRadialCoefficientSpace_iff e).mp heRho m
  have hem : e m ≠ 0 := by simp [e]
  exact (not_lt_of_ge hleft) (hmode hem)

/-! ## The radial Hilbert directed system and reporter naturality -/

/-- Coordinatewise multiplication by the positive-degree powers of a closed-unit-disk scalar is
a contraction on the factorial `ℓ²` pivot. -/
def gammaRadialLpContraction (q : ℂ) (hq : ‖q‖ ≤ 1) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 := by
  let L : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
    { toFun := fun x =>
        ⟨fun n => q ^ (n + 1) * x n,
          (lp.memℓp x).mono' (fun n => by
            rw [norm_mul, norm_pow]
            have hp : ‖q‖ ^ (n + 1) ≤ 1 := pow_le_one₀ (norm_nonneg q) hq
            simpa using mul_le_of_le_one_left (norm_nonneg (x n)) hp)⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext n
        change q ^ (n + 1) * (x n + y n) =
          q ^ (n + 1) * x n + q ^ (n + 1) * y n
        ring
      map_smul' := by
        intro c x
        apply lp.ext
        funext n
        change q ^ (n + 1) * (c * x n) = c * (q ^ (n + 1) * x n)
        ring }
  exact L.mkContinuous 1 (fun x => by
    simpa using lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun n => by
      change ‖q ^ (n + 1) * x n‖ ≤ ‖x n‖
      rw [norm_mul, norm_pow]
      have hp : ‖q‖ ^ (n + 1) ≤ 1 := pow_le_one₀ (norm_nonneg q) hq
      simpa using mul_le_of_le_one_left (norm_nonneg (x n)) hp))

@[simp] theorem gammaRadialLpContraction_apply
    (q : ℂ) (hq : ‖q‖ ≤ 1) (x : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    gammaRadialLpContraction q hq x n = q ^ (n + 1) * x n := by
  rfl

/-- The coordinate transition from radial pivot `rho` to the larger pivot `sigma`. -/
def gammaRadialClockTransition
    (rho sigma : ℝ) (hrho : 0 ≤ rho) (hsigma : 0 < sigma) (h : rho ≤ sigma) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  gammaRadialLpContraction (rho / sigma : ℂ) (by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hrho, abs_of_pos hsigma]
    exact (div_le_one hsigma).mpr h)

@[simp] theorem gammaRadialClockTransition_apply
    (rho sigma : ℝ) (hrho : 0 ≤ rho) (hsigma : 0 < sigma) (h : rho ≤ sigma)
    (x : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    gammaRadialClockTransition rho sigma hrho hsigma h x n =
      (rho / sigma : ℂ) ^ (n + 1) * x n := by
  rfl

/-- Every radial contraction commutes with the Gamma factorial reporter. -/
theorem gammaRadialLpContraction_commutes_gammaFactorialReporter
    (q : ℂ) (hq : ‖q‖ ≤ 1) :
    gammaRadialLpContraction q hq ∘L gammaFactorialObservabilityOperator =
      gammaFactorialObservabilityOperator ∘L gammaRadialLpContraction q hq := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.comp_apply, gammaRadialLpContraction_apply,
    gammaFactorialObservabilityOperator_apply]
  ring

/-- The factorial reporter is a natural endomorphism of the radial Gamma clock system. -/
theorem gammaRadialClockTransition_commutes_gammaFactorialReporter
    (rho sigma : ℝ) (hrho : 0 ≤ rho) (hsigma : 0 < sigma) (h : rho ≤ sigma) :
    gammaRadialClockTransition rho sigma hrho hsigma h ∘L
        gammaFactorialObservabilityOperator =
      gammaFactorialObservabilityOperator ∘L
        gammaRadialClockTransition rho sigma hrho hsigma h := by
  unfold gammaRadialClockTransition
  exact gammaRadialLpContraction_commutes_gammaFactorialReporter _ _

/-- Radial transitions compose exactly. -/
theorem gammaRadialClockTransition_trans
    {rho sigma tau : ℝ} (hrho : 0 ≤ rho) (hsigma : 0 < sigma) (htau : 0 < tau)
    (hrs : rho ≤ sigma) (hst : sigma ≤ tau) :
    gammaRadialClockTransition sigma tau hsigma.le htau hst ∘L
        gammaRadialClockTransition rho sigma hrho hsigma hrs =
      gammaRadialClockTransition rho tau hrho htau (hrs.trans hst) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.comp_apply, gammaRadialClockTransition_apply]
  have hratio : (sigma / tau : ℂ) * (rho / sigma : ℂ) = (rho / tau : ℂ) := by
    field_simp [hsigma.ne', htau.ne']
  rw [← mul_assoc, ← mul_pow, hratio]

/-- The radial transition at a fixed positive scale is the identity. -/
theorem gammaRadialClockTransition_refl
    {rho : ℝ} (hrho : 0 < rho) :
    gammaRadialClockTransition rho rho hrho.le hrho le_rfl =
      ContinuousLinearMap.id ℂ (lp (fun _ : ℕ => ℂ) 2) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  have hρc : (rho : ℂ) ≠ 0 := by exact_mod_cast hrho.ne'
  simp [gammaRadialClockTransition_apply, div_self hρc]

/-! ## Compact regularity of strict radial transitions -/

/-- The diagonal kernel representing a strict radial contraction. -/
def gammaRadialContractionKernel (q : ℂ) : ℕ × ℕ → ℂ :=
  fun p => if p.1 = p.2 then q ^ (p.1 + 1) else 0

/-- A strict radial contraction is Hilbert--Schmidt. -/
theorem gammaRadialContractionKernel_isHS {q : ℂ} (hq : ‖q‖ < 1) :
    HilbertSchmidt.IsHS (gammaRadialContractionKernel q) := by
  rw [HilbertSchmidt.IsHS, summable_prod_of_nonneg (fun p => by positivity)]
  refine ⟨?_, ?_⟩
  · intro i
    apply summable_of_ne_finset_zero (s := {i})
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [gammaRadialContractionKernel, hji.symm]
  · convert (summable_normSq_pow_succ_iff_norm_lt_one q).mpr hq using 1
    funext i
    rw [tsum_eq_single i]
    · simp [gammaRadialContractionKernel]
    · intro j hji
      simp [gammaRadialContractionKernel, hji.symm]

/-- The Hilbert--Schmidt operator of the diagonal kernel is the radial contraction. -/
theorem toOperator_gammaRadialContractionKernel_eq
    {q : ℂ} (hq : ‖q‖ < 1) :
    HilbertSchmidt.toOperator (gammaRadialContractionKernel_isHS hq) =
      gammaRadialLpContraction q hq.le := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  rw [HilbertSchmidt.toOperator_apply (gammaRadialContractionKernel_isHS hq),
    tsum_eq_single n]
  · simp [gammaRadialContractionKernel]
  · intro j hj
    simp [gammaRadialContractionKernel, hj.symm]

/-- Every strict radial contraction is compact. -/
theorem gammaRadialLpContraction_isCompact
    {q : ℂ} (hq : ‖q‖ < 1) :
    IsCompactOperator (gammaRadialLpContraction q hq.le) := by
  rw [← toOperator_gammaRadialContractionKernel_eq hq]
  exact (HilbertSchmidt.isHilbertSchmidt_toOperator
    (gammaRadialContractionKernel_isHS hq)).isCompactOperator

/-- A radial contraction by a nonzero scalar loses no vector. -/
theorem gammaRadialLpContraction_injective
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1) :
    Function.Injective (gammaRadialLpContraction q hq1) := by
  intro x y hxy
  apply lp.ext
  funext n
  have hn := congrArg (fun z : lp (fun _ : ℕ => ℂ) 2 => z n) hxy
  change q ^ (n + 1) * x n = q ^ (n + 1) * y n at hn
  exact mul_left_cancel₀ (pow_ne_zero (n + 1) hq0) hn

/-- Every transition across a strict radial scale increase is compact. -/
theorem gammaRadialClockTransition_isCompact_of_lt
    {rho sigma : ℝ} (hrho : 0 ≤ rho) (hsigma : 0 < sigma) (hrs : rho < sigma) :
    IsCompactOperator
      (gammaRadialClockTransition rho sigma hrho hsigma hrs.le) := by
  unfold gammaRadialClockTransition
  apply gammaRadialLpContraction_isCompact
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hrho, abs_of_pos hsigma]
  exact (div_lt_one hsigma).mpr hrs

/-- Positive radial transitions are injective, including strict compact ones. -/
theorem gammaRadialClockTransition_injective
    {rho sigma : ℝ} (hrho : 0 < rho) (hsigma : 0 < sigma) (hrs : rho ≤ sigma) :
    Function.Injective
      (gammaRadialClockTransition rho sigma hrho.le hsigma hrs) := by
  unfold gammaRadialClockTransition
  apply gammaRadialLpContraction_injective
  exact div_ne_zero (by exact_mod_cast hrho.ne') (by exact_mod_cast hsigma.ne')

/-- Strict positive radial transitions are simultaneously compact and injective. -/
theorem gammaRadialClockTransition_compact_injective_of_lt
    {rho sigma : ℝ} (hrho : 0 < rho) (hsigma : 0 < sigma) (hrs : rho < sigma) :
    IsCompactOperator
        (gammaRadialClockTransition rho sigma hrho.le hsigma hrs.le) ∧
      Function.Injective
        (gammaRadialClockTransition rho sigma hrho.le hsigma hrs.le) :=
  ⟨gammaRadialClockTransition_isCompact_of_lt hrho.le hsigma hrs,
    gammaRadialClockTransition_injective hrho hsigma hrs.le⟩

/-! ## The scale-independent factorial reporter cocone -/

/-- The source-factorial reporter coefficient expressed in the radial coordinates at scale
`rho`. -/
def gammaRadialReporterCoefficient (rho : ℝ) (n : ℕ) : ℂ :=
  (rho : ℂ) ^ (n + 1) * gammaPeriodicConormalCoefficient n

/-- The radial factorial reporter coefficients are square-summable at every finite scale. -/
theorem summable_normSq_gammaRadialReporterCoefficient (rho : ℝ) :
    Summable (fun n : ℕ => ‖gammaRadialReporterCoefficient rho n‖ ^ 2) := by
  have hbase : Summable
      (fun n : ℕ => (‖(rho : ℂ)‖ ^ 2) ^ n / (n.factorial : ℝ)) := by
    exact Real.summable_pow_div_factorial (‖(rho : ℂ)‖ ^ 2)
  have htail : Summable
      (fun n : ℕ => (‖(rho : ℂ)‖ ^ 2) ^ (n + 1) /
        ((n + 1).factorial : ℝ)) := by
    simpa [Nat.succ_eq_add_one] using hbase.comp_injective Nat.succ_injective
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) htail
  rw [gammaRadialReporterCoefficient, norm_mul, norm_pow,
    gammaPeriodicConormalCoefficient, norm_div, norm_one, Complex.norm_natCast]
  have hfac : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n + 1)
  have hfacpos : (0 : ℝ) < ((n + 1).factorial : ℝ) :=
    lt_of_lt_of_le zero_lt_one hfac
  calc
    (‖(rho : ℂ)‖ ^ (n + 1) *
        (1 / ((n + 1).factorial : ℝ))) ^ 2 =
        (‖(rho : ℂ)‖ ^ 2) ^ (n + 1) /
          ((n + 1).factorial : ℝ) ^ 2 := by ring
    _ ≤ (‖(rho : ℂ)‖ ^ 2) ^ (n + 1) /
          ((n + 1).factorial : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) hfacpos
      nlinarith

/-- The diagonal kernel of the radial factorial reporter. -/
def gammaRadialReporterKernel (rho : ℝ) : ℕ × ℕ → ℂ :=
  fun p => if p.1 = p.2 then gammaRadialReporterCoefficient rho p.1 else 0

/-- Every finite-scale radial factorial reporter is Hilbert--Schmidt. -/
theorem gammaRadialReporterKernel_isHS (rho : ℝ) :
    HilbertSchmidt.IsHS (gammaRadialReporterKernel rho) := by
  rw [HilbertSchmidt.IsHS, summable_prod_of_nonneg (fun p => by positivity)]
  refine ⟨?_, ?_⟩
  · intro i
    apply summable_of_ne_finset_zero (s := {i})
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [gammaRadialReporterKernel, hji.symm]
  · convert summable_normSq_gammaRadialReporterCoefficient rho using 1
    funext i
    rw [tsum_eq_single i]
    · simp [gammaRadialReporterKernel]
    · intro j hji
      simp [gammaRadialReporterKernel, hji.symm]

/-- The source-factorial reporter acting on radial clock coordinates at scale `rho`. -/
def gammaRadialReporter (rho : ℝ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  HilbertSchmidt.toOperator (gammaRadialReporterKernel_isHS rho)

@[simp] theorem gammaRadialReporter_apply
    (rho : ℝ) (x : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    gammaRadialReporter rho x n =
      gammaRadialReporterCoefficient rho n * x n := by
  rw [gammaRadialReporter, HilbertSchmidt.toOperator_apply
    (gammaRadialReporterKernel_isHS rho), tsum_eq_single n]
  · simp [gammaRadialReporterKernel]
  · intro j hj
    simp [gammaRadialReporterKernel, hj.symm]

/-- **Scale-independent reporter law.**  Observing after a radial scale transition gives exactly
the reporter at the original scale. -/
theorem gammaRadialReporter_transition
    {rho sigma : ℝ} (hrho : 0 ≤ rho) (hsigma : 0 < sigma) (hrs : rho ≤ sigma) :
    gammaRadialReporter sigma ∘L
        gammaRadialClockTransition rho sigma hrho hsigma hrs =
      gammaRadialReporter rho := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.comp_apply, gammaRadialReporter_apply,
    gammaRadialClockTransition_apply]
  rw [gammaRadialReporterCoefficient, gammaRadialReporterCoefficient]
  have hsigmac : (sigma : ℂ) ≠ 0 := by exact_mod_cast hsigma.ne'
  rw [div_pow]
  field_simp [hsigmac]

/-- At unit radius the radial reporter is the original Gamma factorial reporter. -/
theorem gammaRadialReporter_one :
    gammaRadialReporter 1 = gammaFactorialObservabilityOperator := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  rw [gammaRadialReporter_apply, gammaFactorialObservabilityOperator_apply]
  simp [gammaRadialReporterCoefficient]

/-- Every radial reporter is compact. -/
theorem gammaRadialReporter_isCompact (rho : ℝ) :
    IsCompactOperator (gammaRadialReporter rho) :=
  (HilbertSchmidt.isHilbertSchmidt_toOperator
    (gammaRadialReporterKernel_isHS rho)).isCompactOperator

theorem gammaRadialReporterCoefficient_ne_zero
    {rho : ℝ} (hrho : rho ≠ 0) (n : ℕ) :
    gammaRadialReporterCoefficient rho n ≠ 0 := by
  rw [gammaRadialReporterCoefficient]
  exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hrho))
    (gammaPeriodicConormalCoefficient_ne_zero n)

/-- At every positive scale the radial reporter loses no vector algebraically. -/
theorem gammaRadialReporter_injective
    {rho : ℝ} (hrho : rho ≠ 0) :
    Function.Injective (gammaRadialReporter rho) := by
  intro x y hxy
  apply lp.ext
  funext n
  have hn := congrArg (fun z : lp (fun _ : ℕ => ℂ) 2 => z n) hxy
  change gammaRadialReporter rho x n = gammaRadialReporter rho y n at hn
  rw [gammaRadialReporter_apply, gammaRadialReporter_apply] at hn
  exact mul_left_cancel₀ (gammaRadialReporterCoefficient_ne_zero hrho n) hn

theorem norm_gammaRadialReporter_single (rho : ℝ) (n : ℕ) :
    ‖gammaRadialReporter rho (lp.single 2 n 1)‖ =
      ‖gammaRadialReporterCoefficient rho n‖ := by
  have heq : gammaRadialReporter rho (lp.single 2 n 1) =
      gammaRadialReporterCoefficient rho n • lp.single 2 n 1 := by
    apply lp.ext
    funext j
    rw [gammaRadialReporter_apply]
    by_cases h : j = n
    · subst j
      simp
    · change gammaRadialReporterCoefficient rho j *
          (Pi.single n (1 : ℂ) : ℕ → ℂ) j =
        gammaRadialReporterCoefficient rho n *
          (Pi.single n (1 : ℂ) : ℕ → ℂ) j
      rw [Pi.single_eq_of_ne h]
      simp
  rw [heq, norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  norm_num

/-- Every radial reporter has normalized approximate-null clock directions. -/
theorem gammaRadialReporter_hasApproximateUnitKernel (rho : ℝ) :
    HasApproximateUnitKernel (gammaRadialReporter rho) := by
  refine ⟨fun n => lp.single 2 n (1 : ℂ), ?_, ?_⟩
  · intro n
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    norm_num
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    rw [show (fun n : ℕ => ‖gammaRadialReporter rho (lp.single 2 n 1)‖) =
        (fun n => ‖gammaRadialReporterCoefficient rho n‖) by
      funext n
      exact norm_gammaRadialReporter_single rho n]
    simpa using (tendsto_zero_of_summable_normSq
      (summable_normSq_gammaRadialReporterCoefficient rho)).norm

/-- The range of every nonzero-scale radial reporter is nonclosed. -/
theorem gammaRadialReporter_not_isClosed_range
    {rho : ℝ} (hrho : rho ≠ 0) :
    ¬ IsClosed (Set.range (gammaRadialReporter rho)) :=
  (hasApproximateUnitKernel_iff_not_isClosed_range
    (gammaRadialReporter rho) (gammaRadialReporter_injective hrho)).mp
      (gammaRadialReporter_hasApproximateUnitKernel rho)

/-- Every nonzero-scale radial reporter has dense range. -/
theorem gammaRadialReporter_denseRange
    {rho : ℝ} (hrho : rho ≠ 0) :
    DenseRange (gammaRadialReporter rho) := by
  have hle : Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ℕ)) ≤
      (gammaRadialReporter rho).toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    rw [HilbertSchmidt.lpBasis_apply]
    refine ⟨(gammaRadialReporterCoefficient rho n)⁻¹ • lp.single 2 n 1, ?_⟩
    apply lp.ext
    funext j
    change gammaRadialReporter rho
      ((gammaRadialReporterCoefficient rho n)⁻¹ • lp.single 2 n 1) j =
        (lp.single 2 n (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2) j
    rw [gammaRadialReporter_apply]
    by_cases h : j = n
    · subst j
      simp [gammaRadialReporterCoefficient_ne_zero hrho]
    · simp [h]
  apply (Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (HilbertSchmidt.lpBasis ℕ).dense_span).mono
  intro x hx
  rcases hle hx with ⟨y, hy⟩
  exact ⟨y, hy⟩

/-- Every nonzero-scale radial reporter is a compact injective map with dense proper range. -/
theorem gammaRadialReporter_compact_injective_dense_nonsurjective
    {rho : ℝ} (hrho : rho ≠ 0) :
    IsCompactOperator (gammaRadialReporter rho) ∧
      Function.Injective (gammaRadialReporter rho) ∧
      DenseRange (gammaRadialReporter rho) ∧
      ¬ Function.Surjective (gammaRadialReporter rho) := by
  refine ⟨gammaRadialReporter_isCompact rho, gammaRadialReporter_injective hrho,
    gammaRadialReporter_denseRange hrho, ?_⟩
  intro hsurj
  apply gammaRadialReporter_not_isClosed_range hrho
  rw [hsurj.range_eq]
  exact isClosed_univ

/-- A nonconstant periodic gauge mode has infinite ordinary clock energy. -/
theorem not_summable_normSq_gammaPeriodicModeTail {m : ℕ} (hm : m ≠ 0) :
    ¬ Summable (fun n : ℕ => ‖gammaPeriodicModeTail m n‖ ^ 2) := by
  intro hsum
  have hfreq : 1 ≤ ‖gammaPeriodicFrequency m‖ :=
    one_le_norm_gammaPeriodicFrequency hm
  have hone : ∀ n : ℕ, (1 : ℝ) ≤ ‖gammaPeriodicModeTail m n‖ ^ 2 := by
    intro n
    rw [gammaPeriodicModeTail, norm_pow]
    exact one_le_pow₀ (one_le_pow₀ hfreq)
  have hcontra : (1 : ℝ) ≤ 0 :=
    ge_of_tendsto hsum.tendsto_atTop_zero (Eventually.of_forall hone)
  norm_num at hcontra

/-- No vector in the factorial reporter Hilbert space has the raw derivative coordinates of a
nonconstant periodic gauge mode. -/
theorem not_exists_lp_eq_gammaPeriodicModeTail {m : ℕ} (hm : m ≠ 0) :
    ¬ ∃ x : lp (fun _ : ℕ => ℂ) 2,
      ∀ n, x n = gammaPeriodicModeTail m n := by
  rintro ⟨x, hx⟩
  apply not_summable_normSq_gammaPeriodicModeTail hm
  exact (HilbertSchmidt.summable_coe_sq x).congr fun n => by rw [hx n]

/-- **Pure-mode variance seam.**  Among period-one Fourier modes, exactly the constant mode has a
positive derivative tail represented by a vector of the factorial reporter Hilbert space. -/
theorem exists_lp_eq_gammaPeriodicModeTail_iff (m : ℕ) :
    (∃ x : lp (fun _ : ℕ => ℂ) 2,
      ∀ n, x n = gammaPeriodicModeTail m n) ↔ m = 0 := by
  constructor
  · intro h
    by_contra hm
    exact not_exists_lp_eq_gammaPeriodicModeTail hm h
  · rintro rfl
    refine ⟨0, ?_⟩
    intro n
    change (0 : ℂ) = gammaPeriodicModeTail 0 n
    simp [gammaPeriodicModeTail, gammaPeriodicFrequency]

/-- A nonconstant periodic mode is simultaneously admissible for every cyclic Gamma conormal and
inadmissible as a raw-coordinate input to the factorial `ℓ²` reporter. -/
theorem gammaPeriodicModeTail_corona_not_lp {m : ℕ} (hm : m ≠ 0) :
    gammaPeriodicModeTail m ∈ gammaCoronaClockDomain ∧
      ¬ ∃ x : lp (fun _ : ℕ => ℂ) 2,
        ∀ n, x n = gammaPeriodicModeTail m n :=
  ⟨gammaPeriodicModeTail_mem_coronaClockDomain m,
    not_exists_lp_eq_gammaPeriodicModeTail hm⟩

/-- The maximal Gamma conormal domain has no coordinate-preserving realization inside the
factorial reporter Hilbert space, even without asking the realization to be linear or continuous. -/
theorem gammaCoronaClockDomain_no_coordinatewise_lp_lift :
    ¬ ∃ lift : gammaCoronaClockDomain → lp (fun _ : ℕ => ℂ) 2,
      ∀ b n, lift b n = b.1 n := by
  rintro ⟨lift, hlift⟩
  let b : gammaCoronaClockDomain :=
    ⟨gammaPeriodicModeTail 1, gammaPeriodicModeTail_mem_coronaClockDomain 1⟩
  apply not_exists_lp_eq_gammaPeriodicModeTail (by norm_num : (1 : ℕ) ≠ 0)
  refine ⟨lift b, ?_⟩
  intro n
  exact hlift b n

end

end GaloisForLFunctions.HTGeometry
