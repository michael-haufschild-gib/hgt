import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedAmplitudeCell

/-!
# Uniform scalar schedule for the raised branch of Matomäki--Teräväinen Proposition 4.2

The selected power controls only the lower edge `A^ell`; the actual convolution occupies the
`ell + 1` literal blocks `A^ell * 2^r`.  A fixed bound on `ell` makes both the width `2^ell` and
the pigeonhole loss `ell + 1` absorbable in arbitrarily small powers of the height.  This file
packages that absorption together with the energy-form Huxley threshold.
-/

namespace RHTower.Sieve

open Filter

/-- If the finite pigeonhole cost is at most `N^kappa`, its exact logarithmic exponent loss lies
between `sigma` and `sigma + kappa`. -/
theorem huxleyThresholdLossSigma_mem_interval
    {N : ℕ} (hN : 2 ≤ N) {sigma L kappa : ℝ}
    (hL : 1 ≤ L) (_hkappa : 0 ≤ kappa) (hpow : L ≤ (N : ℝ) ^ kappa) :
    sigma ≤ huxleyThresholdLossSigma N sigma L ∧
      huxleyThresholdLossSigma N sigma L ≤ sigma + kappa := by
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogpow : Real.log L ≤ kappa * Real.log (N : ℝ) := by
    have h := Real.log_le_log (by linarith : 0 < L) hpow
    rw [Real.log_rpow (by linarith : 0 < (N : ℝ))] at h
    linarith
  constructor
  · rw [huxleyThresholdLossSigma]
    have : 0 ≤ Real.log L / Real.log (N : ℝ) := div_nonneg hlogL hlogN.le
    linarith
  · rw [huxleyThresholdLossSigma]
    have : Real.log L / Real.log (N : ℝ) ≤ kappa :=
      (div_le_iff₀ hlogN).2 (by linarith)
    linarith

/-- A fixed width cap turns a base window ending at `T^(1-2 eps)` into valid Huxley windows for
all literal dyadic blocks. -/
theorem matomakiTeravainen_raised_block_window
    {T eps : ℝ} {A ell L : ℕ}
    (hT : 1 < T) (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) (hellL : ell ≤ L)
    (hwidth : (((2 ^ L : ℕ) : ℝ)) ≤ T ^ eps)
    (hlo : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ ((A ^ ell : ℕ) : ℝ))
    (hhi : ((A ^ ell : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps)) :
    ∀ r : Fin (ell + 1),
      2 ≤ A ^ ell * 2 ^ (r : ℕ) ∧
      T ^ ((9 : ℝ) / 11 - 10 * eps) ≤
        ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ∧
      ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ≤ T ^ (1 - eps) := by
  intro r
  have hT0 : 0 < T := by linarith
  have hrL : (r : ℕ) ≤ L := le_trans (by omega) hellL
  have htwoNat : 2 ^ (r : ℕ) ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hrL
  have htwoCast : (((2 ^ (r : ℕ) : ℕ) : ℝ)) ≤ ((2 ^ L : ℕ) : ℝ) := by
    exact_mod_cast htwoNat
  have htwo : (((2 ^ (r : ℕ) : ℕ) : ℝ)) ≤ T ^ eps := htwoCast.trans hwidth
  have htwo1 : (1 : ℝ) ≤ ((2 ^ (r : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
  have hloBlock : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤
      ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact hlo.trans (le_mul_of_one_le_right (by positivity) htwo1)
  have hhiBlock : ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ≤ T ^ (1 - eps) := by
    rw [Nat.cast_mul]
    calc
      ((A ^ ell : ℕ) : ℝ) * ((2 ^ (r : ℕ) : ℕ) : ℝ)
          ≤ T ^ (1 - 2 * eps) * T ^ eps :=
            mul_le_mul hhi htwo (by positivity) (by positivity)
      _ = T ^ (1 - eps) := by
        rw [← Real.rpow_add hT0]
        congr 1
        ring
  have hone : (1 : ℝ) < ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) := by
    have : (1 : ℝ) < T ^ ((9 : ℝ) / 11 - 10 * eps) :=
      Real.one_lt_rpow hT (by linarith)
    exact this.trans_le hloBlock
  refine ⟨?_, hloBlock, hhiBlock⟩
  have hnat : 1 < A ^ ell * 2 ^ (r : ℕ) := by exact_mod_cast hone
  omega

/-- The bounded pigeonhole count is uniformly absorbed into `kappa` at the literature lower edge. -/
theorem matomakiTeravainen_raised_threshold_loss
    {T kappa eps : ℝ} {A ell L : ℕ} (hT : 1 < T) (hkappa : 0 < kappa)
    (heps : 0 < eps) (hepss : eps ≤ 1 / 1000)
    (hellL : ell ≤ L)
    (hloss : (((L + 1 : ℕ) : ℝ)) ≤
      T ^ (((9 : ℝ) / 11 - 10 * eps) * kappa))
    (hlo : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ ((A ^ ell : ℕ) : ℝ)) :
    ∀ r : Fin (ell + 1), ∀ sigma : ℝ,
      sigma ≤ huxleyThresholdLossSigma (A ^ ell * 2 ^ (r : ℕ))
          sigma (ell + 1 : ℝ) ∧
      huxleyThresholdLossSigma (A ^ ell * 2 ^ (r : ℕ))
          sigma (ell + 1 : ℝ) ≤ sigma + kappa := by
  intro r sigma
  let D : ℕ := A ^ ell * 2 ^ (r : ℕ)
  have hT0 : 0 < T := by linarith
  have hbase1 : (1 : ℝ) < ((A ^ ell : ℕ) : ℝ) :=
    (Real.one_lt_rpow hT (by linarith)).trans_le hlo
  have hDbase : ((A ^ ell : ℕ) : ℝ) ≤ (D : ℝ) := by
    dsimp [D]
    rw [Nat.cast_mul]
    exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))))
  have hD : 2 ≤ D := by exact_mod_cast (hbase1.trans_le hDbase)
  have hcollapse : T ^ (((9 : ℝ) / 11 - 10 * eps) * kappa) =
      (T ^ ((9 : ℝ) / 11 - 10 * eps)) ^ kappa := by
    rw [← Real.rpow_mul hT0.le]
  have hpowBase : (((ell + 1 : ℕ) : ℝ)) ≤ ((A ^ ell : ℕ) : ℝ) ^ kappa := by
    have hellcast : (((ell + 1 : ℕ) : ℝ)) ≤ ((L + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hellL 1
    have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _) hlo hkappa.le
    rw [← hcollapse] at hmono
    exact hellcast.trans (hloss.trans hmono)
  have hpowD : (((ell + 1 : ℕ) : ℝ)) ≤ (D : ℝ) ^ kappa :=
    hpowBase.trans (Real.rpow_le_rpow (by positivity) hDbase hkappa.le)
  have hLone : (1 : ℝ) ≤ (ell + 1 : ℝ) := by
    show (1 : ℝ) ≤ (ell : ℝ) + 1
    have hell0 : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg ell
    linarith
  have hpowD' : (ell + 1 : ℝ) ≤ (D : ℝ) ^ kappa := by simpa using hpowD
  exact huxleyThresholdLossSigma_mem_interval hD
    (sigma := sigma) (L := (ell + 1 : ℝ)) (kappa := kappa)
    hLone hkappa.le hpowD'

/-- Huxley's energy threshold follows from the same subpower energy budget used in the density
estimate.  No separate coefficient-size asymptotic is needed. -/
theorem huxley_energy_threshold_of_subpower
    {T N sigma eps Q : ℝ} (hT : 1 ≤ T)
    (heps : 0 < eps) (hepss : eps ≤ 1 / 1000)
    (hready : 2400 ≤ T ^ ((1 : ℝ) / 32))
    (hQ : 1 ≤ Q) (hQ3 : Q ^ 3 ≤ T ^ (eps ^ 2))
    (hNlo : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ N)
    (hsigma : sigma ≤ 7 / 32 - 5 * eps) :
    2400 * Q ≤ N ^ ((1 : ℝ) / 2 - 2 * sigma) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hQle : Q ≤ T ^ (eps ^ 2) := by
    have hQpow : Q ≤ Q ^ 3 := by
      calc
        Q = Q ^ 1 := by ring
        _ ≤ Q ^ 3 := pow_le_pow_right₀ hQ (by norm_num)
    exact hQpow.trans hQ3
  have hconst : 2400 * Q ≤ T ^ ((1 : ℝ) / 32 + eps ^ 2) := by
    calc
      2400 * Q ≤ T ^ ((1 : ℝ) / 32) * T ^ (eps ^ 2) :=
        mul_le_mul hready hQle (by positivity) (by positivity)
      _ = T ^ ((1 : ℝ) / 32 + eps ^ 2) := by rw [← Real.rpow_add hT0]
  have hexp : (1 : ℝ) / 32 + eps ^ 2 ≤
      ((9 : ℝ) / 11 - 10 * eps) * ((1 : ℝ) / 16 + 10 * eps) := by
    nlinarith [sq_nonneg eps]
  have htoBase : T ^ ((1 : ℝ) / 32 + eps ^ 2) ≤
      (T ^ ((9 : ℝ) / 11 - 10 * eps)) ^ ((1 : ℝ) / 16 + 10 * eps) := by
    rw [← Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow_of_exponent_le hT hexp
  have hN0 : 0 ≤ N := le_trans (Real.rpow_nonneg hT0.le _) hNlo
  have hsmallExp : 0 ≤ (1 : ℝ) / 16 + 10 * eps := by positivity
  have htoN : (T ^ ((9 : ℝ) / 11 - 10 * eps)) ^ ((1 : ℝ) / 16 + 10 * eps) ≤
      N ^ ((1 : ℝ) / 16 + 10 * eps) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _) hNlo hsmallExp
  have hexpN : (1 : ℝ) / 16 + 10 * eps ≤ (1 : ℝ) / 2 - 2 * sigma := by
    linarith
  exact hconst.trans (htoBase.trans (htoN.trans
    (Real.rpow_le_rpow_of_exponent_le (by
      have : 1 ≤ T ^ ((9 : ℝ) / 11 - 10 * eps) :=
        Real.one_le_rpow hT (by linarith)
      exact this.trans hNlo) hexpN)))

/-- Uniform completion of every scalar condition imposed by the raised energy-form Lemma 4.1.
Only the source-scale window, fixed raising cap, amplitude interior, and intrinsic energy budget
remain as inputs. -/
theorem exists_matomakiTeravainen_raised_huxley_schedule
    {eps kappa : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000)
    (hkappa : 0 < kappa) (L : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ (T : ℝ) (A ell : ℕ) (rho Q : ℝ),
      T₀ ≤ T → 0 < ell → ell ≤ L →
      T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ ((A ^ ell : ℕ) : ℝ) →
      ((A ^ ell : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) →
      5 * eps + kappa ≤ rho → rho + kappa ≤ 7 / 32 - 5 * eps →
      1 ≤ Q → Q ^ 3 ≤ T ^ (eps ^ 2) →
      ∀ r : Fin (ell + 1),
        2 ≤ A ^ ell * 2 ^ (r : ℕ) ∧
        T ^ ((9 : ℝ) / 11 - 10 * eps) ≤
          ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ∧
        ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ≤ T ^ (1 - eps) ∧
        5 * eps ≤ huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ) ∧
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ) ≤ 7 / 32 - 5 * eps ∧
        2400 * Q ≤ ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ^
          ((1 : ℝ) / 2 - 2 * huxleyThresholdLossSigma
            (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ)) ∧
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ) ≤ rho + kappa := by
  have hwidthGrowth : Tendsto (fun T : ℝ => T ^ eps) atTop atTop :=
    tendsto_rpow_atTop heps
  have hlossExp : 0 < ((9 : ℝ) / 11 - 10 * eps) * kappa := by
    exact mul_pos (by linarith) hkappa
  have hlossGrowth : Tendsto
      (fun T : ℝ => T ^ (((9 : ℝ) / 11 - 10 * eps) * kappa)) atTop atTop :=
    tendsto_rpow_atTop hlossExp
  have hreadyGrowth : Tendsto (fun T : ℝ => T ^ ((1 : ℝ) / 32)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hevent : ∀ᶠ T : ℝ in atTop,
      1 < T ∧
      (((2 ^ L : ℕ) : ℝ)) ≤ T ^ eps ∧
      (((L + 1 : ℕ) : ℝ)) ≤
        T ^ (((9 : ℝ) / 11 - 10 * eps) * kappa) ∧
      2400 ≤ T ^ ((1 : ℝ) / 32) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hwidthGrowth.eventually_ge_atTop (((2 ^ L : ℕ) : ℝ)),
      hlossGrowth.eventually_ge_atTop (((L + 1 : ℕ) : ℝ)),
      hreadyGrowth.eventually_ge_atTop (2400 : ℝ)] with T hT hwidth hloss hready
    exact ⟨hT, hwidth, hloss, hready⟩
  obtain ⟨T₀, hT₀⟩ := (eventually_atTop.1 hevent)
  refine ⟨max 1 T₀, le_max_left _ _, ?_⟩
  intro T A ell rho Q hT hell hellL hlo hhi hrhoLo hrhoHi hQ hQ3
  have hdata := hT₀ T (le_trans (le_max_right _ _) hT)
  have hblocks := matomakiTeravainen_raised_block_window hdata.1 heps hepss hellL
    hdata.2.1 hlo hhi
  have hloss0 := matomakiTeravainen_raised_threshold_loss hdata.1 hkappa heps hepss hellL
    hdata.2.2.1 hlo
  intro r
  obtain ⟨hD, hDlo, hDhi⟩ := hblocks r
  have hDloss := hloss0 r rho
  have hsl : 5 * eps ≤ huxleyThresholdLossSigma
      (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ) :=
    le_trans (by linarith) hDloss.1
  have hsh : huxleyThresholdLossSigma
      (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ) ≤ 7 / 32 - 5 * eps :=
    hDloss.2.trans hrhoHi
  have hthr := huxley_energy_threshold_of_subpower
    (T := T) (N := ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ))
    (sigma := huxleyThresholdLossSigma
      (A ^ ell * 2 ^ (r : ℕ)) rho (ell + 1 : ℝ))
    hdata.1.le heps hepss hdata.2.2.2 hQ hQ3 hDlo hsh
  exact ⟨hD, hDlo, hDhi, hsl, hsh, hthr, hDloss.2⟩

end RHTower.Sieve
