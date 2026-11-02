import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryNonzeroProfileHasAPositiveConductorFloor
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileRetainsHighConductorCoercivity
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorQuasimodesAreUniformOnBoundedOverlap

/-!
# Positivity on growing conductor spans

A fixed low-conductor block has a positive spectral floor and vanishing quasimode residuals.
Above that block, logarithmic prime coercivity absorbs the profile-dependent errors. The
orthogonal split removes the diagonal quasimodes from the cross term.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

private theorem residual_packet_norm_le {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N) {e : ℝ} (he : 0 < e)
    (r : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N))
    (hr : (∑ m ∈ Icc 1 Q, ‖r m‖ ^ 2) ≤ e ^ 2 / 128) (a : ℕ → ℝ) :
    ‖∑ m ∈ Icc 1 Q, a m • r m‖ ≤
      e / 8 * ‖∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N‖ := by
  let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  have hframe := (half_and_three_halves_riesz_of_log_le hQ hQN hlog a).1
  have hcoeff : (∑ m ∈ Icc 1 Q, a m ^ 2) ≤ 2 * ‖u‖ ^ 2 := by
    linarith only [hframe]
  have htri : ‖∑ m ∈ Icc 1 Q, a m • r m‖ ≤ ∑ m ∈ Icc 1 Q, |a m| * ‖r m‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 Q) (fun m => |a m|) (fun m => ‖r m‖)
  simp only [sq_abs] at hcs
  have hsq : ‖∑ m ∈ Icc 1 Q, a m • r m‖ ^ 2 ≤ (e / 8 * ‖u‖) ^ 2 := by
    calc
      _ ≤ (∑ m ∈ Icc 1 Q, |a m| * ‖r m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (∑ m ∈ Icc 1 Q, a m ^ 2) * ∑ m ∈ Icc 1 Q, ‖r m‖ ^ 2 := hcs
      _ ≤ (2 * ‖u‖ ^ 2) * (e ^ 2 / 128) :=
        mul_le_mul hcoeff hr (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hright : 0 ≤ e / 8 * ‖u‖ := by positivity
  nlinarith only [hsq, hright, norm_nonneg (∑ m ∈ Icc 1 Q, a m • r m)]

private theorem finite_block_energy_and_cross {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N) (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) (E : ℕ → ℝ)
    {e M : ℝ} (he : 0 < e)
    (hE : ∀ m ∈ Icc 1 Q, e ≤ E m ∧ E m ≤ M)
    (hgram : 9 * (1 + Real.log Q) / Real.log N * M ≤ e / 4)
    (hres : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ e ^ 2 / 128)
    (a : ℕ → ℝ) :
    let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
    (3 * e / 8) * ‖u‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A u, u⟫ ∧
      ∀ z ∈ (conductorSubspace Q N)ᗮ,
        |⟪Matrix.toEuclideanLin A u, z⟫| ≤ e / 8 * ‖u‖ * ‖z‖ := by
  let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  let S := ∑ m ∈ Icc 1 Q, a m ^ 2
  let d := ∑ m ∈ Icc 1 Q, (a m * E m) • normalizedRamanujanHorizonVector m N
  let r := fun m => Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
    E m • normalizedRamanujanHorizonVector m N
  let v := ∑ m ∈ Icc 1 Q, a m • r m
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hM : 0 ≤ M := he.le.trans ((hE 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩)).1.trans
    (hE 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩)).2)
  have hAu : Matrix.toEuclideanLin A u = d + v := by
    dsimp only [u, d, v, r]
    rw [map_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [map_smul, smul_sub, mul_smul]
    abel
  have hv : ‖v‖ ≤ e / 8 * ‖u‖ := residual_packet_norm_le hQ hQN hlog he r hres a
  have hdiag : e * S ≤ ∑ m ∈ Icc 1 Q, (a m * E m) * a m := by
    dsimp only [S]
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    have hh := mul_le_mul_of_nonneg_right (hE m hm).1 (sq_nonneg (a m))
    nlinarith only [hh]
  have hdSq : (∑ m ∈ Icc 1 Q, (a m * E m) ^ 2) ≤ M ^ 2 * S := by
    dsimp only [S]
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    have hh := pow_le_pow_left₀ (he.le.trans (hE m hm).1) (hE m hm).2 2
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg (a m))
    nlinarith only [hmul]
  have hsqrt : Real.sqrt (∑ m ∈ Icc 1 Q, (a m * E m) ^ 2) ≤ M * Real.sqrt S := by
    calc
      _ ≤ Real.sqrt (M ^ 2 * S) := Real.sqrt_le_sqrt hdSq
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg Q]
  have hcoef : 0 ≤ 9 * (1 + Real.log Q) / Real.log N := by positivity
  have hpol := abs_inner_sum_normalizedRamanujanHorizonVector_sub_le hQ hQN
    (fun m => a m * E m) a
  have herr : |⟪d, u⟫ - ∑ m ∈ Icc 1 Q, (a m * E m) * a m| ≤ (e / 4) * S := by
    calc
      _ ≤ 9 * (1 + Real.log Q) / Real.log N *
          Real.sqrt (∑ m ∈ Icc 1 Q, (a m * E m) ^ 2) * Real.sqrt S := hpol
      _ ≤ 9 * (1 + Real.log Q) / Real.log N * (M * Real.sqrt S) * Real.sqrt S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hcoef) (Real.sqrt_nonneg S)
      _ = (9 * (1 + Real.log Q) / Real.log N * M) * S := by
        rw [mul_assoc, mul_assoc, Real.mul_self_sqrt hS]
        ring
      _ ≤ (e / 4) * S := mul_le_mul_of_nonneg_right hgram hS
  have hframe := (half_and_three_halves_riesz_of_log_le hQ hQN hlog a).2
  have hnormCost : (e / 2) * ‖u‖ ^ 2 ≤ (3 * e / 4) * S := by
    have hh := mul_le_mul_of_nonneg_left hframe (show 0 ≤ e / 2 by positivity)
    linarith only [hh]
  have hdLower : (e / 2) * ‖u‖ ^ 2 ≤ ⟪d, u⟫ := by
    linarith only [hdiag, (abs_le.mp herr).1, hnormCost]
  have hvInner : |⟪v, u⟫| ≤ (e / 8) * ‖u‖ ^ 2 := by
    exact (abs_real_inner_le_norm v u).trans
      ((mul_le_mul_of_nonneg_right hv (norm_nonneg u)).trans_eq (by ring))
  constructor
  · change (3 * e / 8) * ‖u‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A u, u⟫
    rw [hAu, inner_add_left]
    linarith only [hdLower, (abs_le.mp hvInner).1]
  · intro z hz
    have hdMem : d ∈ conductorSubspace Q N :=
      sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q N _
    have hdOrth : ⟪d, z⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hdMem hz
    change |⟪Matrix.toEuclideanLin A u, z⟫| ≤ _
    rw [hAu, inner_add_left, hdOrth, zero_add]
    exact (abs_real_inner_le_norm v z).trans
      (mul_le_mul_of_nonneg_right hv (norm_nonneg z))

private theorem finite_uniform_profile_residuals {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2)
    {K : ℝ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ m ∈ S,
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  induction S using Finset.induction_on with
  | empty => exact Eventually.of_forall fun N c hc hcK m hm => False.elim (notMem_empty m hm)
  | @insert m S hm ih =>
      filter_upwards [eventually_completeWeil_completedConductor_residual_uniform_overlap
        hφ hsupp hM hK (hS m (mem_insert_self m S)) hε,
        ih fun k hk => hS k (mem_insert_of_mem hk)] with N hmN hSN
      intro c hc hcK k hk
      rcases mem_insert.mp hk with rfl | hkS
      · exact hmN c hc hcK
      · exact hSN c hc hcK k hkS

private theorem eventually_fixed_block_energy_and_cross {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2)
    {K : ℝ} (hK : 1 ≤ K) {e : ℝ} (he : 0 < e)
    (hfloor : ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ m : ℕ, 0 < m →
      e ≤ completedConductorEnergy φ c m) {Q : ℕ} (hQ : 2 ≤ Q) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ∀ p ∈ conductorSubspace Q N,
        (3 * e / 8) * ‖p‖ ^ 2 ≤ completeWeilEnergy φ c N p ∧
        ∀ z ∈ (conductorSubspace Q N)ᗮ,
          |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫| ≤ e / 8 * ‖p‖ * ‖z‖ := by
  let M := |completeWeilSelfFinitePart φ 1| + 2 * Real.log Q + 3 * K ^ 4
  let S := Icc 1 Q
  let ε := e / (16 * ((S.card : ℝ) + 1))
  have hcard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hε : 0 < ε := div_pos he (by positivity)
  have hbudget : (S.card : ℝ) * ε ^ 2 ≤ e ^ 2 / 128 := by
    have hden : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
    dsimp only [ε]
    field_simp
    nlinarith only [sq_nonneg (S.card : ℝ), sq_nonneg e,
      mul_nonneg (sq_nonneg e) (sq_nonneg (S.card : ℝ)),
      mul_nonneg (sq_nonneg e) hcard]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (Q * Q),
    hLlim.eventually_ge_atTop (18 * (1 + Real.log Q)),
    hLlim.eventually_ge_atTop (36 * (1 + Real.log Q) * M / e),
    finite_uniform_profile_residuals hφ hsupp hM hK hε S
      (fun m hm => (mem_Icc.mp hm).1)] with N hQN hlog hgramN hresN
  intro c hc hcK p hp
  obtain ⟨a, -, rfl⟩ := (mem_conductorSubspace_iff (M := Q) (N := N) (x := p)).mp hp
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg Q]
  have hgram : 9 * (1 + Real.log Q) / Real.log N * M ≤ e / 4 := by
    have hh := (div_le_iff₀ he).mp hgramN
    rw [show 9 * (1 + Real.log Q) / Real.log N * M =
      (9 * (1 + Real.log Q) * M) / Real.log N by ring, div_le_iff₀ hL]
    nlinarith only [hh]
  have hE : ∀ m ∈ Icc 1 Q,
      e ≤ completedConductorEnergy φ c m ∧ completedConductorEnergy φ c m ≤ M := by
    intro m hm
    obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
    refine ⟨hfloor c hc hcK m hm1, ?_⟩
    have hh := completedConductorEnergy_le_of_one_le hφ hsupp hM hc hm1
    have hl : Real.log (m : ℝ) ≤ Real.log Q := Real.log_le_log
      (by exact_mod_cast hm1) (by exact_mod_cast hmQ)
    have hp : c ^ 4 ≤ K ^ 4 := pow_le_pow_left₀ (zero_lt_one.trans_le hc).le hcK 4
    dsimp only [M]
    linarith only [hh, hl, hp]
  have hres : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ e ^ 2 / 128 := by
    have hh := sum_le_sum fun m (hm : m ∈ S) =>
      pow_le_pow_left₀ (norm_nonneg _) (hresN c hc hcK m hm) 2
    have hs : (∑ m ∈ S, ε ^ 2) = (S.card : ℝ) * ε ^ 2 := by
      rw [sum_const, nsmul_eq_mul]
    rw [hs] at hh
    exact hh.trans hbudget
  exact finite_block_energy_and_cross hQ hQN hlog (completeWeilMatrix φ c N)
    (completedConductorEnergy φ c) he hE hgram hres a

private theorem eventually_powerConductor_horizon {θ K : ℝ}
    (hθ : 0 < θ) (hθlt : θ < 1 / 1080) (hK : 1 ≤ K) {Q : ℕ} (hQ : 2 ≤ Q) :
    ∀ᶠ N : ℕ in atTop,
      let R := ⌊(N : ℝ) ^ θ⌋₊
      Q ≤ R ∧ R ^ 6 ≤ N ∧ 1080 * (1 + Real.log R) ≤ Real.log N ∧
      (1 + Real.log R) * (R : ℝ) ^ 2 * (Real.log N / N) ≤ 1 ∧
      ∀ c : ℝ, 1 ≤ c → c ≤ K → c / N ≤ 1 / 3 ∧
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N := by
  have hgap : 0 < 1 - 1080 * θ := by linarith only [hθlt]
  have hθsmall : θ ≤ 1 / 36 := by linarith only [hθlt]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hRlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have hXlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 36 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).comp tendsto_natCast_atTop_atTop
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).bound zero_lt_one)
  filter_upwards [eventually_ge_atTop 1, hRlim.eventually_ge_atTop (Q : ℝ),
    hLlim.eventually_ge_atTop (1080 / (1 - 1080 * θ)), hsmall,
    hXlim.eventually_ge_atTop 1, hXlim.eventually_ge_atTop (3 * K),
    hXlim.eventually_ge_atTop (2 * (2 * K * Real.exp 2 + 1)),
    hXlim.eventually_ge_atTop (2 * (K * Real.exp 1 + 1))]
    with N hN1 hRQ hlogN hLXraw hX1 hX3K hXnear hXup
  let R := ⌊(N : ℝ) ^ θ⌋₊
  let X := (N : ℝ) ^ (1 / 36 : ℝ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hQR : Q ≤ R := Nat.le_floor hRQ
  have hR2 : 2 ≤ R := hQ.trans hQR
  have hRR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hRXθ : (R : ℝ) ≤ (N : ℝ) ^ θ := Nat.floor_le (Real.rpow_nonneg hN0.le θ)
  have hRX : (R : ℝ) ≤ X := hRXθ.trans
    (Real.rpow_le_rpow_of_exponent_le hNR1 hθsmall)
  have hLX : Real.log N ≤ X := by
    have hh : |Real.log (N : ℝ)| ≤ X := by
      simpa only [Function.comp_def, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul] using hLXraw
    exact (le_abs_self _).trans hh
  have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
    dsimp only [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hpowX : ∀ k : ℕ, k ≤ 36 → X ^ k ≤ (N : ℝ) := fun k hk =>
    (pow_le_pow_right₀ hX1 hk).trans_eq hX36
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hlogR : Real.log R ≤ θ * Real.log N := by
    have hh := Real.log_le_log hRR0 hRXθ
    rwa [Real.log_rpow hN0 θ] at hh
  have hlog : 1080 * (1 + Real.log R) ≤ Real.log N := by
    have hh := (div_le_iff₀ hgap).mp hlogN
    nlinarith only [hh, hlogR]
  have hH : 0 ≤ 1 + Real.log R := by positivity
  have hHX : 1 + Real.log R ≤ X :=
    (show 1 + Real.log R ≤ Real.log N by linarith only [hlog, hH]).trans hLX
  have hR6 : R ^ 6 ≤ N := by
    exact_mod_cast (pow_le_pow_left₀ (Nat.cast_nonneg R) hRX 6).trans (hpowX 6 (by norm_num))
  have hR2X : (R : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg R) hRX 2
  have htail : (1 + Real.log R) * (R : ℝ) ^ 2 * (Real.log N / N) ≤ 1 := by
    have hprod : (1 + Real.log R) * (R : ℝ) ^ 2 * Real.log N ≤ (N : ℝ) := by
      calc
        _ ≤ X * X ^ 2 * X := by gcongr
        _ = X ^ 4 := by ring
        _ ≤ (N : ℝ) := hpowX 4 (by norm_num)
    calc
      _ = ((1 + Real.log R) * (R : ℝ) ^ 2 * Real.log N) / N := by ring
      _ ≤ 1 := (div_le_one hN0).mpr hprod
  refine ⟨hQR, hR6, hlog, htail, ?_⟩
  intro c hc hcK
  have hc0 : 0 ≤ c := (zero_lt_one.trans_le hc).le
  have hK0 : 0 ≤ K := (zero_lt_one.trans_le hK).le
  have hw : c / N ≤ 1 / 3 := by
    rw [div_le_iff₀ hN0]
    have hh : X ≤ (N : ℝ) := by simpa only [pow_one] using hpowX 1 (by norm_num)
    linarith only [hcK, hX3K, hh]
  have hRR1 : ((R * R : ℕ) + 1 : ℝ) ≤ 2 * X ^ 2 := by
    have hh : 1 ≤ X ^ 2 := one_le_pow₀ hX1
    push_cast
    nlinarith only [hR2X, hh]
  have hnear : linearNearRowRadius c + 1 ≤ 2 * K * Real.exp 2 + 1 := by
    unfold linearNearRowRadius
    gcongr
  have hup : c * Real.exp 1 + 1 ≤ K * Real.exp 1 + 1 := by gcongr
  have hnearN : ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
    calc
      _ ≤ (2 * X ^ 2) * (2 * K * Real.exp 2 + 1) :=
        mul_le_mul hRR1 hnear (by unfold linearNearRowRadius; positivity) (by positivity)
      _ = (2 * (2 * K * Real.exp 2 + 1)) * X ^ 2 := by ring
      _ ≤ X * X ^ 2 := mul_le_mul_of_nonneg_right hXnear (sq_nonneg X)
      _ = X ^ 3 := by ring
      _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
  have hupN : ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N := by
    calc
      _ ≤ (2 * X ^ 2) * (K * Real.exp 1 + 1) :=
        mul_le_mul hRR1 hup (by positivity) (by positivity)
      _ = (2 * (K * Real.exp 1 + 1)) * X ^ 2 := by ring
      _ ≤ X * X ^ 2 := mul_le_mul_of_nonneg_right hXup (sq_nonneg X)
      _ = X ^ 3 := by ring
      _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
  exact ⟨hw, hnearN, hupN⟩

private theorem profile_energy_smul (φ : ℝ → ℝ) (c : ℝ) {N : ℕ} (s : ℝ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (s • u) = s ^ 2 * completeWeilEnergy φ c N u := by
  simp only [completeWeilEnergy, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem profile_energy_add (φ : ℝ → ℝ) (c : ℝ) {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (x + y) = completeWeilEnergy φ c N x +
      2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ +
        completeWeilEnergy φ c N y := by
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian φ c N)) y x
  simp only [completeWeilEnergy, map_add, inner_add_left, inner_add_right]
  rw [hsym, real_inner_comm y (Matrix.toEuclideanLin (completeWeilMatrix φ c N) x)]
  ring

/-- Every nonzero compact `C²` profile is uniformly coercive on a polynomial conductor span
throughout bounded overlap intervals. -/
theorem eventually_profile_polynomialConductor_coercive {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2)
    {K θ : ℝ} (hK : 1 ≤ K) (hθ : 0 < θ) (hθlt : θ < 1 / 1080) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ∀ x ∈ conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N,
        b * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  obtain ⟨e₀, he₀, hfloor₀⟩ := exists_uniform_completedConductor_floor hφ hsupp hM K
  let e := min e₀ 1
  have he : 0 < e := lt_min he₀ zero_lt_one
  have he1 : e ≤ 1 := min_le_right _ _
  have hfloor : ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ m : ℕ, 0 < m →
      e ≤ completedConductorEnergy φ c m := fun c hc hcK m hm =>
    (min_le_left _ _).trans (hfloor₀ c (zero_lt_one.trans_le hc) hcK m hm)
  obtain ⟨C, hC, hcoerc⟩ := exists_profile_highConductor_coercivity hφ hsupp hM hK
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Q, hQ, hlogQ⟩ := ((eventually_ge_atTop 2).and
    (hLlim.eventually_ge_atTop (4 * (C + 1)))).exists
  refine ⟨e / 4, by positivity, ?_⟩
  filter_upwards [eventually_powerConductor_horizon hθ hθlt hK hQ,
    eventually_fixed_block_energy_and_cross hφ hsupp hM hK he hfloor hQ]
    with N hhor hlow
  let R := ⌊(N : ℝ) ^ θ⌋₊
  obtain ⟨hQR, hR6, hlog, htail, hwidth⟩ := hhor
  intro c hc hcK
  obtain ⟨hw, hnear, hup⟩ := hwidth c hc hcK
  have hhigh : ∀ z ∈ conductorSubspace R N, z ∈ (conductorSubspace Q N)ᗮ →
      ‖z‖ ^ 2 ≤ completeWeilEnergy φ c N z := by
    intro z hzR hzQ
    by_cases hz0 : z = 0
    · simp only [hz0, norm_zero, zero_pow (by decide : 2 ≠ 0), completeWeilEnergy,
        map_zero, inner_zero_left, le_refl]
    have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let y := ‖z‖⁻¹ • z
    have hyR : y ∈ conductorSubspace R N := Submodule.smul_mem _ _ hzR
    have hyQ : y ∈ (conductorSubspace Q N)ᗮ := Submodule.smul_mem _ _ hzQ
    have hyNorm : ‖y‖ = 1 := by
      dsimp only [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzNorm), inv_mul_cancel₀ hzNorm.ne']
    obtain ⟨a, -, hay⟩ := (mem_conductorSubspace_iff (M := R) (N := N) (x := y)).mp hyR
    rw [hay] at hyQ hyNorm
    have hh := hcoerc hQ hQR hR6 hlog hc hcK hw hnear hup htail a hyQ hyNorm
    rw [← hay] at hh
    have hWy : 1 ≤ completeWeilEnergy φ c N y := by
      linarith only [hh, hlogQ, primeAdjunctionMass_nonneg R a]
    change 1 ≤ completeWeilEnergy φ c N (‖z‖⁻¹ • z) at hWy
    rw [profile_energy_smul] at hWy
    have hprod := mul_le_mul_of_nonneg_left hWy (sq_nonneg ‖z‖)
    have hscale : ‖z‖ ^ 2 * (‖z‖⁻¹ ^ 2 * completeWeilEnergy φ c N z) =
        completeWeilEnergy φ c N z := by field_simp
    rwa [mul_one, hscale] at hprod
  intro x hx
  let p := (conductorSubspace Q N).starProjection x
  let z := x - p
  have hp : p ∈ conductorSubspace Q N := (conductorSubspace Q N).starProjection_apply_mem x
  have hzQ : z ∈ (conductorSubspace Q N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [real_inner_comm]
    exact (conductorSubspace Q N).starProjection_inner_eq_zero x v hv
  have hzR : z ∈ conductorSubspace R N :=
    (conductorSubspace R N).sub_mem hx (conductorSubspace_mono hQR N hp)
  have hpyth : ‖p‖ ^ 2 + ‖z‖ ^ 2 = ‖x‖ ^ 2 :=
    norm_starProjection_sq_add_sub_sq (conductorSubspace Q N) x
  obtain ⟨hpEnergy, hpCross⟩ := hlow c hc hcK p hp
  have hzEnergy := hhigh z hzR hzQ
  have hcross := hpCross z hzQ
  have hcrossCost : 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫| ≤
      (e / 8) * (‖p‖ ^ 2 + ‖z‖ ^ 2) := by
    have hh := mul_nonneg (show 0 ≤ e / 8 by positivity) (sq_nonneg (‖p‖ - ‖z‖))
    nlinarith only [hcross, hh]
  have hxSplit : x = p + z := by dsimp only [z]; abel
  have henergy := profile_energy_add φ c p z
  rw [← hxSplit] at henergy
  have hcrossLower := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫
  have hzReserve : (3 * e / 8) * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right he1 (sq_nonneg ‖z‖)
    nlinarith only [hh, sq_nonneg ‖z‖, mul_nonneg he.le (sq_nonneg ‖z‖)]
  rw [← hpyth]
  nlinarith only [hpEnergy, hzEnergy, hcrossCost, henergy, hcrossLower, hzReserve]

/-- One positive constant works for every fixed polylogarithmic conductor cutoff; only its
waiting horizon depends on the logarithmic exponent. -/
theorem eventually_profile_polylogConductor_coercive {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2)
    {K : ℝ} (hK : 1 ≤ K) :
    ∃ b : ℝ, 0 < b ∧ ∀ A : ℝ, 0 < A →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
        ∀ x ∈ conductorSubspace ⌊Real.log (N : ℝ) ^ A⌋₊ N,
          b * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  obtain ⟨b, hb, hpoly⟩ := eventually_profile_polynomialConductor_coercive hφ hsupp hM hK
    (by norm_num : (0 : ℝ) < 1 / 2160) (by norm_num : (1 / 2160 : ℝ) < 1 / 1080)
  refine ⟨b, hb, ?_⟩
  intro A hA
  let δ := (1 / 2160 : ℝ) / A
  have hδ : 0 < δ := div_pos (by norm_num) hA
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop hδ).bound zero_lt_one)
  filter_upwards [hpoly, hsmall, eventually_ge_atTop 1] with N hpolyN hsmallN hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log N ≤ (N : ℝ) ^ δ := by
    have hh : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ δ := by
      simpa only [Function.comp_def, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul] using hsmallN
    exact (le_abs_self _).trans hh
  have hpower : Real.log (N : ℝ) ^ A ≤ (N : ℝ) ^ (1 / 2160 : ℝ) := by
    calc
      _ ≤ ((N : ℝ) ^ δ) ^ A := Real.rpow_le_rpow (Real.log_natCast_nonneg N) hlog hA.le
      _ = (N : ℝ) ^ (δ * A) := (Real.rpow_mul hN0.le δ A).symm
      _ = _ := by rw [show δ * A = (1 / 2160 : ℝ) from div_mul_cancel₀ _ hA.ne']
  have hcut : ⌊Real.log (N : ℝ) ^ A⌋₊ ≤ ⌊(N : ℝ) ^ (1 / 2160 : ℝ)⌋₊ :=
    Nat.le_floor ((Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg N) A)).trans hpower)
  intro c hc hcK x hx
  exact hpolyN c hc hcK x (conductorSubspace_mono hcut N hx)

private theorem profile_dilation_energy (φ : ℝ → ℝ) {w : ℝ} (hw : 0 < w)
    (c : ℝ) (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy (atomDilate φ w) (c / w) N x = completeWeilEnergy φ c N x := by
  have hatom : atomDilate (atomDilate φ w) (c / w / N) = atomDilate φ (c / N) := by
    funext t
    change φ ((t / (c / w / N)) / w) = φ (t / (c / N))
    have hwidth : (c / w / N) * w = c / N := by
      calc
        _ = (c / w * w) / N := by ring
        _ = _ := by rw [div_mul_cancel₀ c hw.ne']
    rw [div_div, hwidth]
  simp only [completeWeilEnergy, completeWeilMatrix, hatom]

/-- Polynomial conductor spans are uniformly coercive on every compact interval of positive
overlaps, including intervals below the touching ratio. -/
theorem eventually_profile_polynomialConductor_coercive_on_compact_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0)
    (hM : 0 < ∫ x, φ x ^ 2) {a b θ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hθ : 0 < θ) (hθlt : θ < 1 / 1080) :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, a ≤ c → c ≤ b →
      ∀ x ∈ conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N,
        k * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  let w := min a 1
  let ψ := atomDilate φ w
  have hw : 0 < w := lt_min ha zero_lt_one
  have hw1 : w ≤ 1 := min_le_right _ _
  have hwa : w ≤ a := min_le_left _ _
  obtain ⟨hψ, hsψ, -⟩ := atomDilate_facts hφ hsupp hw
  have hψsupp : ∀ x, x ∉ Set.Icc 0 1 → ψ x = 0 := by
    intro x hx
    exact hsψ x fun hm => hx ⟨hm.1, hm.2.trans hw1⟩
  have hψM : 0 < ∫ x, ψ x ^ 2 := by
    dsimp only [ψ]
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hK : 1 ≤ b / w := (one_le_div hw).mpr (hwa.trans hab)
  obtain ⟨k, hk, hpos⟩ := eventually_profile_polynomialConductor_coercive
    hψ hψsupp hψM hK hθ hθlt
  refine ⟨k, hk, ?_⟩
  filter_upwards [hpos] with N hN
  intro c hac hcb x hx
  have hc1 : 1 ≤ c / w := (one_le_div hw).mpr (hwa.trans hac)
  have hcK : c / w ≤ b / w := div_le_div_of_nonneg_right hcb hw.le
  have hh := hN (c / w) hc1 hcK x hx
  rwa [profile_dilation_energy φ hw c N x] at hh

/-- Every fixed polylogarithmic conductor span shares a positive lower bound on compact
positive-overlap intervals. The exponent changes only the waiting horizon. -/
theorem eventually_profile_polylogConductor_coercive_on_compact_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0)
    (hM : 0 < ∫ x, φ x ^ 2) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ k : ℝ, 0 < k ∧ ∀ A : ℝ, 0 < A →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, a ≤ c → c ≤ b →
        ∀ x ∈ conductorSubspace ⌊Real.log (N : ℝ) ^ A⌋₊ N,
          k * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  let w := min a 1
  let ψ := atomDilate φ w
  have hw : 0 < w := lt_min ha zero_lt_one
  have hw1 : w ≤ 1 := min_le_right _ _
  have hwa : w ≤ a := min_le_left _ _
  obtain ⟨hψ, hsψ, -⟩ := atomDilate_facts hφ hsupp hw
  have hψsupp : ∀ x, x ∉ Set.Icc 0 1 → ψ x = 0 := by
    intro x hx
    exact hsψ x fun hm => hx ⟨hm.1, hm.2.trans hw1⟩
  have hψM : 0 < ∫ x, ψ x ^ 2 := by
    dsimp only [ψ]
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hK : 1 ≤ b / w := (one_le_div hw).mpr (hwa.trans hab)
  obtain ⟨k, hk, hpos⟩ := eventually_profile_polylogConductor_coercive hψ hψsupp hψM hK
  refine ⟨k, hk, ?_⟩
  intro A hA
  filter_upwards [hpos A hA] with N hN
  intro c hac hcb x hx
  have hc1 : 1 ≤ c / w := (one_le_div hw).mpr (hwa.trans hac)
  have hcK : c / w ≤ b / w := div_le_div_of_nonneg_right hcb hw.le
  have hh := hN (c / w) hc1 hcK x hx
  rwa [profile_dilation_energy φ hw c N x] at hh

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
