import GaloisForLFunctions.RHTower.Sieve.VinogradovLogHeightWindow
import GaloisForLFunctions.RHTower.Sieve.VinogradovTaylorPerturbation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovUpperHalfProduct (Q : ℕ) (l m : Fin Q) : ℝ :=
  ((Q + l.val : ℕ) : ℝ) * ((Q + m.val : ℕ) : ℝ)

def routeTLogTaylorError
    (t x : ℝ) (Q k : ℕ) (l m : Fin Q) : ℝ :=
  t / (2 * Real.pi) *
      Real.log (1 - vinogradovUpperHalfProduct Q l m / x) -
    vinogradovUpperHalfPairPhase
      (fun j : Fin k => -logTaylorMagnitude t x j) l m

theorem vinogradovUpperHalfPairPhase_neg_logTaylorMagnitude
    {t x : ℝ} (hx : x ≠ 0) {Q k : ℕ} (l m : Fin Q) :
    vinogradovUpperHalfPairPhase
        (fun j : Fin k => -logTaylorMagnitude t x j) l m =
      -(t / (2 * Real.pi)) *
        ∑ i ∈ Finset.range k,
          (vinogradovUpperHalfProduct Q l m / x) ^ (i + 1) / (i + 1) := by
  unfold vinogradovUpperHalfPairPhase
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ =>
      (vinogradovUpperHalfProduct Q l m / x) ^ (i + 1) / (i + 1)) k,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [logTaylorMagnitude, vinogradovUpperHalfProduct]
  rw [div_pow]
  push_cast
  field_simp [hx, pow_ne_zero]

theorem routeTLogTaylorError_bound
    {t x : ℝ} (ht : 0 < t) (hx : 0 < x)
    {Q k : ℕ} (hQ : 1 ≤ Q)
    (hscale : 4 * ((2 * Q : ℕ) : ℝ) ^ 2 ≤ x)
    (l m : Fin Q) :
    |routeTLogTaylorError t x Q k l m| ≤
      t / (2 * Real.pi) *
        (2 * (vinogradovUpperHalfProduct Q l m / x) ^ (k + 1)) := by
  let y := vinogradovUpperHalfProduct Q l m
  let z := y / x
  have hl : (((Q + l.val : ℕ) : ℝ)) ≤ (2 * Q : ℕ) := by
    exact_mod_cast (show Q + l.val ≤ 2 * Q by omega)
  have hm : (((Q + m.val : ℕ) : ℝ)) ≤ (2 * Q : ℕ) := by
    exact_mod_cast (show Q + m.val ≤ 2 * Q by omega)
  have hl0 : (0 : ℝ) ≤ ((Q + l.val : ℕ) : ℝ) := by positivity
  have hm0 : (0 : ℝ) ≤ ((Q + m.val : ℕ) : ℝ) := by positivity
  have hy0 : 0 ≤ y := by unfold y vinogradovUpperHalfProduct; positivity
  have hy : y ≤ ((2 * Q : ℕ) : ℝ) ^ 2 := by
    unfold y vinogradovUpperHalfProduct
    rw [pow_two]
    exact mul_le_mul hl hm (by positivity) (by positivity)
  have hz0 : 0 ≤ z := by unfold z; positivity
  have hzquarter : z ≤ 1 / 4 := by
    rw [div_le_iff₀ hx]
    exact hy.trans (by linarith [hscale] :
      ((2 * Q : ℕ) : ℝ) ^ 2 ≤ 1 / 4 * x)
  have hzabs : |z| < 1 := by rw [abs_of_nonneg hz0]; linarith
  have hseries := Real.abs_log_sub_add_sum_range_le hzabs k
  have hden : (1 - |z|)⁻¹ ≤ 2 := by
    rw [abs_of_nonneg hz0]
    apply (inv_le_comm₀ (by linarith : 0 < 1 - z) (by norm_num : (0 : ℝ) < 2)).2
    norm_num
    linarith
  have htail : |z| ^ (k + 1) / (1 - |z|) ≤ 2 * z ^ (k + 1) := by
    have hdenz : (1 - z)⁻¹ ≤ 2 := by
      simpa [abs_of_nonneg hz0] using hden
    rw [abs_of_nonneg hz0, div_eq_mul_inv]
    calc
      z ^ (k + 1) * (1 - z)⁻¹ ≤ z ^ (k + 1) * 2 :=
        mul_le_mul_of_nonneg_left hdenz (by positivity)
      _ = 2 * z ^ (k + 1) := by ring
  have hphase := vinogradovUpperHalfPairPhase_neg_logTaylorMagnitude
    (t := t) (ne_of_gt hx) (Q := Q) (k := k) l m
  unfold routeTLogTaylorError
  rw [hphase]
  have hc : 0 ≤ t / (2 * Real.pi) := by positivity
  rw [show t / (2 * Real.pi) *
      Real.log (1 - vinogradovUpperHalfProduct Q l m / x) -
      -(t / (2 * Real.pi)) *
        (∑ i ∈ Finset.range k,
          (vinogradovUpperHalfProduct Q l m / x) ^ (i + 1) / (i + 1)) =
      t / (2 * Real.pi) *
        ((∑ i ∈ Finset.range k,
          (vinogradovUpperHalfProduct Q l m / x) ^ (i + 1) / (i + 1)) +
          Real.log (1 - vinogradovUpperHalfProduct Q l m / x)) by ring,
    abs_mul, abs_of_nonneg hc]
  dsimp [z, y] at hseries htail ⊢
  exact mul_le_mul_of_nonneg_left (hseries.trans htail) hc

private theorem routeTLog_pow_cancel_two
    {b : ℝ} (hb : b ≠ 0) (r : ℕ) :
    b ^ (2 * r) * ((b ^ 2)⁻¹) ^ (r + 1) = (b ^ 2)⁻¹ := by
  rw [inv_pow, ← pow_mul]
  have heq : 2 * (r + 1) = 2 * r + 2 := by omega
  rw [heq, pow_add]
  field_simp

/-- At Route-T scale, the entire order-`400u` logarithmic Taylor tail is
at most `B^-2`.  Height contributes `B^(800u)`, while the first omitted
power contributes `B^(-2(400u+1))`, leaving exactly two powers. -/
theorem routeTLogTaylorError_le_inv_sq
    {u C : ℕ} {t x : ℝ}
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ)))
    (hxlower : ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ)) ≤ x)
    (l m : Fin (routeTLogHalfBlock C)) :
    |routeTLogTaylorError t x (routeTLogHalfBlock C)
        (vinogradovRouteTOrder (4 * u)) l m| ≤
      (((2 * C : ℕ) : ℝ) ^ 2)⁻¹ := by
  let B := 2 * C
  let Q := routeTLogHalfBlock C
  let k := vinogradovRouteTOrder (4 * u)
  have hB2 : 2 ≤ B := routeTLogBaseThreshold_ge_two (by simpa only [B] using hC)
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  have hP : 2 * Q = B ^ routeTLogHalfLengthExponent := by
    simpa [B, Q] using two_mul_routeTLogHalfBlock C
  have hscale : 4 * ((2 * Q : ℕ) : ℝ) ^ 2 ≤ x := by
    have hb4 : (4 : ℝ) ≤ (B : ℝ) ^ 2 := by
      have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB2
      nlinarith [sq_nonneg ((B : ℝ) - 2)]
    have hpow :
        4 * (B : ℝ) ^ (2 * routeTLogHalfLengthExponent) ≤
          (B : ℝ) ^ routeTLogCentreExponent := by
      rw [show routeTLogHalfLengthExponent = 99 by rfl,
        show routeTLogCentreExponent = 200 by rfl]
      calc
        4 * (B : ℝ) ^ (2 * 99) ≤ (B : ℝ) ^ 2 * (B : ℝ) ^ (2 * 99) := by
          gcongr
        _ = (B : ℝ) ^ 200 := by rw [← pow_add]
    calc
      4 * ((2 * Q : ℕ) : ℝ) ^ 2 =
          4 * (B : ℝ) ^ (2 * routeTLogHalfLengthExponent) := by
        rw [hP]
        push_cast
        rw [← pow_mul]
        congr 2
      _ ≤ (B : ℝ) ^ routeTLogCentreExponent := hpow
      _ = (((B ^ routeTLogCentreExponent : ℕ) : ℝ)) := by norm_cast
      _ ≤ x := by simpa only [B] using hxlower
  have hraw := routeTLogTaylorError_bound ht
    (lt_of_lt_of_le (by positivity : (0 : ℝ) <
      ((B ^ routeTLogCentreExponent : ℕ) : ℝ))
      (by simpa only [B] using hxlower))
    (Q := Q) (k := k) (by
      have : 1 ≤ B ^ routeTLogHalfLengthExponent :=
        one_le_pow₀ (show 1 ≤ B by omega)
      rw [← hP] at this
      omega) hscale l m
  let y := vinogradovUpperHalfProduct Q l m
  let z := y / x
  have hy : y ≤ ((2 * Q : ℕ) : ℝ) ^ 2 := by
    unfold y vinogradovUpperHalfProduct
    rw [pow_two]
    exact mul_le_mul
      (by exact_mod_cast (show Q + l.val ≤ 2 * Q by omega))
      (by exact_mod_cast (show Q + m.val ≤ 2 * Q by omega))
      (by positivity) (by positivity)
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) <
      ((B ^ routeTLogCentreExponent : ℕ) : ℝ))
    (by simpa only [B] using hxlower)
  have hz0 : 0 ≤ z := by unfold z y vinogradovUpperHalfProduct; positivity
  have hz : z ≤ ((B : ℝ) ^ 2)⁻¹ := by
    rw [div_le_iff₀ hx0]
    have hbaseIdentity :
        ((B : ℝ) ^ 2)⁻¹ * (B : ℝ) ^ routeTLogCentreExponent =
          (B : ℝ) ^ (2 * routeTLogHalfLengthExponent) := by
      rw [show routeTLogCentreExponent = 200 by rfl,
        show routeTLogHalfLengthExponent = 99 by rfl]
      rw [show (B : ℝ) ^ 200 = (B : ℝ) ^ 2 * (B : ℝ) ^ 198 by
        rw [← pow_add]]
      field_simp
    calc
      y ≤ ((2 * Q : ℕ) : ℝ) ^ 2 := hy
      _ = (B : ℝ) ^ (2 * routeTLogHalfLengthExponent) := by
        rw [hP]
        push_cast
        rw [← pow_mul]
        simp [routeTLogHalfLengthExponent, Nat.mul_comm]
      _ = ((B : ℝ) ^ 2)⁻¹ * (B : ℝ) ^ routeTLogCentreExponent :=
        hbaseIdentity.symm
      _ ≤ ((B : ℝ) ^ 2)⁻¹ * x := by
        gcongr
        calc
          (B : ℝ) ^ routeTLogCentreExponent =
              ((B ^ routeTLogCentreExponent : ℕ) : ℝ) := by norm_cast
          _ ≤ x := by simpa only [B] using hxlower
  have hfactor : t / (2 * Real.pi) * 2 ≤ t := by
    have hpi := Real.two_le_pi
    have hden : 0 < 2 * Real.pi := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  have hzpow : z ^ (k + 1) ≤ (((B : ℝ) ^ 2)⁻¹) ^ (k + 1) :=
    pow_le_pow_left₀ hz0 hz _
  have htopB : t ≤ (B : ℝ) ^ (800 * u) := by
    have hc : (((B ^ routeTLogCentreExponent) ^ (4 * u) : ℕ) : ℝ) =
        (B : ℝ) ^ (800 * u) := by
      push_cast
      rw [← pow_mul]
      simp [routeTLogCentreExponent]
      congr 1
      omega
    rw [← hc]
    simpa only [B] using htop
  have hk : k + 1 = 400 * u + 1 := by
    unfold k vinogradovRouteTOrder
    omega
  calc
    _ ≤ t / (2 * Real.pi) * (2 * z ^ (k + 1)) := by
      simpa [Q, k, z, y] using hraw
    _ = (t / (2 * Real.pi) * 2) * z ^ (k + 1) := by ring
    _ ≤ t * z ^ (k + 1) := by gcongr
    _ ≤ (B : ℝ) ^ (800 * u) * (((B : ℝ) ^ 2)⁻¹) ^ (k + 1) :=
      mul_le_mul htopB hzpow (by positivity) (by positivity)
    _ = ((B : ℝ) ^ 2)⁻¹ := by
      rw [hk]
      rw [show 800 * u = 2 * (400 * u) by omega]
      exact routeTLog_pow_cancel_two hB0 (400 * u)
    _ = (((2 * C : ℕ) : ℝ) ^ 2)⁻¹ := by simp [B]

def routeTLogRatioBilinearSum (t x : ℝ) (Q : ℕ) : ℂ :=
  ∑ l : Fin Q, ∑ m : Fin Q,
    finitePhaseChar
      (t / (2 * Real.pi) *
        Real.log (1 - vinogradovUpperHalfProduct Q l m / x))

theorem vinogradovUpperHalfPerturbed_logTaylor_eq_ratio
    {t x : ℝ} {Q k : ℕ} :
    vinogradovUpperHalfPerturbedBilinearSum
        (fun j : Fin k => -logTaylorMagnitude t x j)
        (routeTLogTaylorError t x Q k) =
      routeTLogRatioBilinearSum t x Q := by
  unfold vinogradovUpperHalfPerturbedBilinearSum routeTLogRatioBilinearSum
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  unfold routeTLogTaylorError
  ring

/-- Complete logarithmic ratio block: VMVT power saving plus an explicit
`B^-2` Taylor perturbation term. -/
theorem norm_routeTLogRatioBilinearSum_le_of_shell
    {u C : ℕ} {t x : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ)))
    (hxlower : ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ)) ≤ x)
    (hxupper : x ≤ routeTLogCentreMultiplier *
      ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ))) :
    ‖routeTLogRatioBilinearSum t x (routeTLogHalfBlock C)‖ ≤
      ((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
          (2 - vinogradovRouteTPowerSavingExponent u) +
        2 * Real.pi * ((((2 * C : ℕ) : ℝ) ^ 2)⁻¹) *
          (routeTLogHalfBlock C : ℝ) ^ 2 := by
  let Q := routeTLogHalfBlock C
  let k := vinogradovRouteTOrder (4 * u)
  let α : Fin k → ℝ := fun j => -logTaylorMagnitude t x j
  let ε : Fin Q → Fin Q → ℝ := routeTLogTaylorError t x Q k
  let η : ℝ := (((2 * C : ℕ) : ℝ) ^ 2)⁻¹
  have hbase := norm_routeTLogUpperHalfBilinearSum_le_rpow_of_shell
    hu hC ht hbottom htop hxlower hxupper
  have herror : ∀ l m, |ε l m| ≤ η := by
    intro l m
    exact routeTLogTaylorError_le_inv_sq hC ht htop hxlower l m
  have hperturb := norm_vinogradovUpperHalfPerturbedBilinearSum_sub_le
    α ε herror
  rw [← vinogradovUpperHalfPerturbed_logTaylor_eq_ratio
    (t := t) (x := x) (Q := Q) (k := k)]
  calc
    _ ≤ ‖vinogradovUpperHalfBilinearSum Q α‖ +
        ‖vinogradovUpperHalfPerturbedBilinearSum α ε -
          vinogradovUpperHalfBilinearSum Q α‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ ((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
          (2 - vinogradovRouteTPowerSavingExponent u) +
        2 * Real.pi * η * (Q : ℝ) ^ 2 := by
      exact add_le_add (by simpa [Q, k, α] using hbase) hperturb
    _ = _ := by rfl

theorem routeTLog_taylor_term_le_saved_rpow
    {u C : ℕ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C) :
    2 * Real.pi * ((((2 * C : ℕ) : ℝ) ^ 2)⁻¹) *
        (routeTLogHalfBlock C : ℝ) ^ 2 ≤
      ((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
        (2 - vinogradovRouteTPowerSavingExponent u) := by
  let B := 2 * C
  let Q := routeTLogHalfBlock C
  let δ := vinogradovRouteTPowerSavingExponent u
  have hCB : routeTLogBaseThreshold u ≤ B := by simpa only [B] using hC
  have hwindow : routeTLogWindowThreshold u ≤ B :=
    (le_max_left _ _).trans hCB
  have hmultPos : 0 < routeTLogCentreMultiplier := by
    norm_num [routeTLogCentreMultiplier]
  have hfactorPos : 0 < (240 * u + 1) *
      routeTLogCentreMultiplier ^ (240 * u) := by
    exact Nat.mul_pos (by omega) (pow_pos hmultPos _)
  have hB32 : 32 ≤ B := by
    calc
      32 = 32 * 1 := by omega
      _ ≤ 32 * ((240 * u + 1) * routeTLogCentreMultiplier ^ (240 * u)) := by
        exact Nat.mul_le_mul_left 32 (by omega)
      _ = routeTLogWindowThreshold u := by
        unfold routeTLogWindowThreshold
        ring
      _ ≤ B := hwindow
  have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hb0 : (0 : ℝ) < B := by positivity
  have hbn0 : (B : ℝ) ≠ 0 := ne_of_gt hb0
  have hP : 2 * Q = B ^ routeTLogHalfLengthExponent := by
    simpa [B, Q] using two_mul_routeTLogHalfBlock C
  have hQNat : Q ≤ B ^ routeTLogHalfLengthExponent := by
    rw [← hP]
    omega
  have hQsq : (Q : ℝ) ^ 2 ≤
      (B : ℝ) ^ (2 * routeTLogHalfLengthExponent) := by
    have hqr : (Q : ℝ) ≤ ((B ^ routeTLogHalfLengthExponent : ℕ) : ℝ) := by
      exact_mod_cast hQNat
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Q) hqr 2
    calc
      (Q : ℝ) ^ 2 ≤ (((B ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^ 2 := hs
      _ = (B : ℝ) ^ (2 * routeTLogHalfLengthExponent) := by
        push_cast
        rw [show 2 * routeTLogHalfLengthExponent =
          routeTLogHalfLengthExponent * 2 by omega, pow_mul]
  have hpiB : 2 * Real.pi ≤ (B : ℝ) := by
    have hb8 : (8 : ℝ) ≤ B := by exact_mod_cast (show 8 ≤ B by omega)
    nlinarith [Real.pi_le_four]
  have herrorPower :
      2 * Real.pi * ((B : ℝ) ^ 2)⁻¹ * (Q : ℝ) ^ 2 ≤
        (B : ℝ) ^ 197 := by
    calc
      _ ≤ (B : ℝ) * ((B : ℝ) ^ 2)⁻¹ *
          (B : ℝ) ^ (2 * routeTLogHalfLengthExponent) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hpiB (by positivity)) hQsq
          (by positivity) (by positivity)
      _ = (B : ℝ) ^ 197 := by
        rw [show routeTLogHalfLengthExponent = 99 by rfl]
        field_simp
  have hδ : δ ≤ 1 / 100 :=
    vinogradovRouteTPowerSavingExponent_le_one_hundredth (by omega)
  have hexponent : (197 : ℝ) ≤ 99 * (2 - δ) := by
    nlinarith
  have hmainPower : (B : ℝ) ^ 197 ≤
      (((B ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^ (2 - δ) := by
    rw [show routeTLogHalfLengthExponent = 99 by rfl]
    push_cast
    rw [← Real.rpow_natCast (B : ℝ) 197,
      ← Real.rpow_natCast (B : ℝ) 99,
      ← Real.rpow_mul hb0.le]
    exact Real.rpow_le_rpow_of_exponent_le hb1 hexponent
  simpa [B, Q, δ] using herrorPower.trans hmainPower

/-- Taylor perturbation is dominated by the same VMVT saved power. -/
theorem norm_routeTLogRatioBilinearSum_le_two_rpow_of_shell
    {u C : ℕ} {t x : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ)))
    (hxlower : ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ)) ≤ x)
    (hxupper : x ≤ routeTLogCentreMultiplier *
      ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ))) :
    ‖routeTLogRatioBilinearSum t x (routeTLogHalfBlock C)‖ ≤
      2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
        (2 - vinogradovRouteTPowerSavingExponent u)) := by
  have hraw := norm_routeTLogRatioBilinearSum_le_of_shell
    hu hC ht hbottom htop hxlower hxupper
  have htail := routeTLog_taylor_term_le_saved_rpow hu hC
  linarith

def routeTLogShiftBilinearSum (t x : ℝ) (Q : ℕ) : ℂ :=
  ∑ l : Fin Q, ∑ m : Fin Q,
    finitePhaseChar
      (t / (2 * Real.pi) *
        Real.log (x - vinogradovUpperHalfProduct Q l m))

theorem routeTLogShiftBilinearSum_eq_const_mul_ratio
    {t x : ℝ} (hx : 0 < x) {Q : ℕ} (hQ : 1 ≤ Q)
    (hscale : 4 * ((2 * Q : ℕ) : ℝ) ^ 2 ≤ x) :
    routeTLogShiftBilinearSum t x Q =
      finitePhaseChar (t / (2 * Real.pi) * Real.log x) *
        routeTLogRatioBilinearSum t x Q := by
  have hphase : ∀ l m : Fin Q,
      t / (2 * Real.pi) *
          Real.log (x - vinogradovUpperHalfProduct Q l m) =
        t / (2 * Real.pi) * Real.log x +
          t / (2 * Real.pi) *
            Real.log (1 - vinogradovUpperHalfProduct Q l m / x) := by
    intro l m
    let y := vinogradovUpperHalfProduct Q l m
    have hy0 : 0 ≤ y := by unfold y vinogradovUpperHalfProduct; positivity
    have hy : y ≤ ((2 * Q : ℕ) : ℝ) ^ 2 := by
      unfold y vinogradovUpperHalfProduct
      rw [pow_two]
      exact mul_le_mul
        (by exact_mod_cast (show Q + l.val ≤ 2 * Q by omega))
        (by exact_mod_cast (show Q + m.val ≤ 2 * Q by omega))
        (by positivity) (by positivity)
    have hyx : y < x := by linarith
    have hone : 1 - y / x ≠ 0 := by
      have : y / x < 1 := (div_lt_one hx).2 hyx
      linarith
    have hmul : x - y = x * (1 - y / x) := by field_simp
    rw [show vinogradovUpperHalfProduct Q l m = y by rfl, hmul,
      Real.log_mul (ne_of_gt hx) hone]
    ring
  unfold routeTLogShiftBilinearSum routeTLogRatioBilinearSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [hphase l m, finitePhaseChar_add]

theorem norm_routeTLogShiftBilinearSum_eq_ratio
    {t x : ℝ} (hx : 0 < x) {Q : ℕ} (hQ : 1 ≤ Q)
    (hscale : 4 * ((2 * Q : ℕ) : ℝ) ^ 2 ≤ x) :
    ‖routeTLogShiftBilinearSum t x Q‖ =
      ‖routeTLogRatioBilinearSum t x Q‖ := by
  rw [routeTLogShiftBilinearSum_eq_const_mul_ratio hx hQ hscale,
    norm_mul, norm_finitePhaseChar, one_mul]

/-- Final source phase `e((t/2π)log(x-lm))`, with Taylor constant restored. -/
theorem norm_routeTLogShiftBilinearSum_le_two_rpow_of_shell
    {u C : ℕ} {t x : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ)))
    (hxlower : ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ)) ≤ x)
    (hxupper : x ≤ routeTLogCentreMultiplier *
      ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ))) :
    ‖routeTLogShiftBilinearSum t x (routeTLogHalfBlock C)‖ ≤
      2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
        (2 - vinogradovRouteTPowerSavingExponent u)) := by
  let B := 2 * C
  let Q := routeTLogHalfBlock C
  have hB2 : 2 ≤ B := routeTLogBaseThreshold_ge_two (by simpa only [B] using hC)
  have hP : 2 * Q = B ^ routeTLogHalfLengthExponent := by
    simpa [B, Q] using two_mul_routeTLogHalfBlock C
  have hscale : 4 * ((2 * Q : ℕ) : ℝ) ^ 2 ≤ x := by
    have hb4 : (4 : ℝ) ≤ (B : ℝ) ^ 2 := by
      have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB2
      nlinarith [sq_nonneg ((B : ℝ) - 2)]
    calc
      4 * ((2 * Q : ℕ) : ℝ) ^ 2 = 4 * (B : ℝ) ^ 198 := by
        rw [hP]
        push_cast
        rw [← pow_mul]
        norm_num [routeTLogHalfLengthExponent]
      _ ≤ (B : ℝ) ^ 2 * (B : ℝ) ^ 198 := by gcongr
      _ = (B : ℝ) ^ 200 := by rw [← pow_add]
      _ = (((B ^ routeTLogCentreExponent : ℕ) : ℝ)) := by
        simp [routeTLogCentreExponent]
      _ ≤ x := by simpa only [B] using hxlower
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) <
      ((B ^ routeTLogCentreExponent : ℕ) : ℝ))
    (by simpa only [B] using hxlower)
  have hQ1 : 1 ≤ Q := by
    have : 1 ≤ B ^ routeTLogHalfLengthExponent :=
      one_le_pow₀ (show 1 ≤ B by omega)
    rw [← hP] at this
    omega
  rw [norm_routeTLogShiftBilinearSum_eq_ratio hx0 hQ1 hscale]
  exact norm_routeTLogRatioBilinearSum_le_two_rpow_of_shell
    hu hC ht hbottom htop hxlower hxupper

def routeTLogTwistedRatioBilinearSum
    (t x β : ℝ) (Q : ℕ) : ℂ :=
  ∑ l : Fin Q, ∑ m : Fin Q,
    finitePhaseChar
      (t / (2 * Real.pi) *
          Real.log (1 - vinogradovUpperHalfProduct Q l m / x) +
        β * vinogradovUpperHalfProduct Q l m)

theorem vinogradovUpperHalfPairPhase_twisted
    {t x β : ℝ} {Q k : ℕ} (hk : 0 < k) (l m : Fin Q) :
    vinogradovUpperHalfPairPhase
        (routeTLogTwistedTaylorCoefficient (k := k) t x β) l m =
      vinogradovUpperHalfPairPhase
          (fun j : Fin k => -logTaylorMagnitude t x j) l m +
        β * vinogradovUpperHalfProduct Q l m := by
  let j0 : Fin k := ⟨0, hk⟩
  let y := vinogradovUpperHalfProduct Q l m
  have hsingle :
      (∑ j : Fin k,
        (if j.val = 0 then β else 0) * y ^ (j.val + 1)) = β * y := by
    rw [Finset.sum_eq_single j0]
    · simp [j0]
    · intro j _hj hjne
      have hj0 : j.val ≠ 0 := by
        intro hval
        apply hjne
        apply Fin.ext
        simpa [j0] using hval
      simp [hj0]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j0))
  unfold vinogradovUpperHalfPairPhase routeTLogTwistedTaylorCoefficient
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hy :
      ((((Q + l.val) : ℝ) * ((Q + m.val) : ℝ))) = y := by
    unfold y vinogradovUpperHalfProduct
    push_cast
    ring
  have hyexpanded :
      (Q : ℝ) * ((Q : ℝ) + m.val) +
          (l.val : ℝ) * ((Q : ℝ) + m.val) = y := by
    rw [← hy]
    ring
  rw [hyexpanded, hsingle]

theorem vinogradovUpperHalfPerturbed_twistedLogTaylor_eq_ratio
    {u Q : ℕ} {t x β : ℝ} (hu : 1 ≤ u) :
    vinogradovUpperHalfPerturbedBilinearSum
        (routeTLogTwistedTaylorCoefficient
          (k := vinogradovRouteTOrder (4 * u)) t x β)
        (routeTLogTaylorError t x Q (vinogradovRouteTOrder (4 * u))) =
      routeTLogTwistedRatioBilinearSum t x β Q := by
  unfold vinogradovUpperHalfPerturbedBilinearSum
    routeTLogTwistedRatioBilinearSum
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  rw [vinogradovUpperHalfPairPhase_twisted (by
    unfold vinogradovRouteTOrder
    omega)]
  unfold routeTLogTaylorError
  ring

/-- Uniform `max_beta` input required by MV24.10, with the Taylor tail
absorbed into the same saved power. -/
theorem norm_routeTLogTwistedRatioBilinearSum_le_two_rpow_of_shell
    {u C : ℕ} {t x β : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ)))
    (hxlower : ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ)) ≤ x)
    (hxupper : x ≤ routeTLogCentreMultiplier *
      ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ))) :
    ‖routeTLogTwistedRatioBilinearSum t x β (routeTLogHalfBlock C)‖ ≤
      2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
        (2 - vinogradovRouteTPowerSavingExponent u)) := by
  let Q := routeTLogHalfBlock C
  let k := vinogradovRouteTOrder (4 * u)
  let α : Fin k → ℝ := routeTLogTwistedTaylorCoefficient t x β
  let ε : Fin Q → Fin Q → ℝ := routeTLogTaylorError t x Q k
  let η : ℝ := (((2 * C : ℕ) : ℝ) ^ 2)⁻¹
  have hbase := norm_routeTLogTwistedUpperHalfBilinearSum_le_rpow_of_shell
    hu hC ht hbottom htop hxlower hxupper (β := β)
  have herror : ∀ l m, |ε l m| ≤ η := by
    intro l m
    exact routeTLogTaylorError_le_inv_sq hC ht htop hxlower l m
  have hperturb := norm_vinogradovUpperHalfPerturbedBilinearSum_sub_le
    α ε herror
  have htail := routeTLog_taylor_term_le_saved_rpow hu hC
  rw [← vinogradovUpperHalfPerturbed_twistedLogTaylor_eq_ratio
    (u := u) (Q := Q) (t := t) (x := x) (β := β) (by omega)]
  calc
    _ ≤ ‖vinogradovUpperHalfBilinearSum Q α‖ +
        ‖vinogradovUpperHalfPerturbedBilinearSum α ε -
          vinogradovUpperHalfBilinearSum Q α‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ ((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
          (2 - vinogradovRouteTPowerSavingExponent u) +
        2 * Real.pi * η * (Q : ℝ) ^ 2 := by
      exact add_le_add (by simpa [Q, k, α] using hbase) hperturb
    _ ≤ 2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
          (2 - vinogradovRouteTPowerSavingExponent u)) := by
      dsimp [η, Q]
      linarith

def routeTLogTwistedShiftBilinearSum
    (t x β : ℝ) (Q : ℕ) : ℂ :=
  ∑ l : Fin Q, ∑ m : Fin Q,
    finitePhaseChar
      (t / (2 * Real.pi) *
          Real.log (x - vinogradovUpperHalfProduct Q l m) +
        β * vinogradovUpperHalfProduct Q l m)

theorem norm_routeTLogTwistedShiftBilinearSum_eq_ratio
    {t x β : ℝ} (hx : 0 < x) {Q : ℕ} (hQ : 1 ≤ Q)
    (hscale : 4 * ((2 * Q : ℕ) : ℝ) ^ 2 ≤ x) :
    ‖routeTLogTwistedShiftBilinearSum t x β Q‖ =
      ‖routeTLogTwistedRatioBilinearSum t x β Q‖ := by
  have hphase : ∀ l m : Fin Q,
      t / (2 * Real.pi) *
          Real.log (x - vinogradovUpperHalfProduct Q l m) +
          β * vinogradovUpperHalfProduct Q l m =
        t / (2 * Real.pi) * Real.log x +
          (t / (2 * Real.pi) *
              Real.log (1 - vinogradovUpperHalfProduct Q l m / x) +
            β * vinogradovUpperHalfProduct Q l m) := by
    intro l m
    let y := vinogradovUpperHalfProduct Q l m
    have hy : y ≤ ((2 * Q : ℕ) : ℝ) ^ 2 := by
      unfold y vinogradovUpperHalfProduct
      rw [pow_two]
      exact mul_le_mul
        (by exact_mod_cast (show Q + l.val ≤ 2 * Q by omega))
        (by exact_mod_cast (show Q + m.val ≤ 2 * Q by omega))
        (by positivity) (by positivity)
    have hyx : y < x := by linarith
    have hone : 1 - y / x ≠ 0 := by
      have : y / x < 1 := (div_lt_one hx).2 hyx
      linarith
    have hmul : x - y = x * (1 - y / x) := by field_simp
    rw [show vinogradovUpperHalfProduct Q l m = y by rfl, hmul,
      Real.log_mul (ne_of_gt hx) hone]
    ring
  have hsum : routeTLogTwistedShiftBilinearSum t x β Q =
      finitePhaseChar (t / (2 * Real.pi) * Real.log x) *
        routeTLogTwistedRatioBilinearSum t x β Q := by
    unfold routeTLogTwistedShiftBilinearSum routeTLogTwistedRatioBilinearSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [hphase l m, finitePhaseChar_add]
  rw [hsum, norm_mul, norm_finitePhaseChar, one_mul]

theorem norm_routeTLogTwistedShiftBilinearSum_le_two_rpow_of_shell
    {u C : ℕ} {t x β : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ)))
    (hxlower : ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ)) ≤ x)
    (hxupper : x ≤ routeTLogCentreMultiplier *
      ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ))) :
    ‖routeTLogTwistedShiftBilinearSum t x β (routeTLogHalfBlock C)‖ ≤
      2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
        (2 - vinogradovRouteTPowerSavingExponent u)) := by
  let B := 2 * C
  let Q := routeTLogHalfBlock C
  have hB2 : 2 ≤ B := routeTLogBaseThreshold_ge_two (by simpa only [B] using hC)
  have hP : 2 * Q = B ^ routeTLogHalfLengthExponent := by
    simpa [B, Q] using two_mul_routeTLogHalfBlock C
  have hscale : 4 * ((2 * Q : ℕ) : ℝ) ^ 2 ≤ x := by
    calc
      4 * ((2 * Q : ℕ) : ℝ) ^ 2 = 4 * (B : ℝ) ^ 198 := by
        rw [hP]
        push_cast
        rw [← pow_mul]
        norm_num [routeTLogHalfLengthExponent]
      _ ≤ (B : ℝ) ^ 2 * (B : ℝ) ^ 198 := by
        gcongr
        have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB2
        nlinarith [sq_nonneg ((B : ℝ) - 2)]
      _ = (B : ℝ) ^ 200 := by rw [← pow_add]
      _ = (((B ^ routeTLogCentreExponent : ℕ) : ℝ)) := by
        simp [routeTLogCentreExponent]
      _ ≤ x := by simpa only [B] using hxlower
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) <
      ((B ^ routeTLogCentreExponent : ℕ) : ℝ))
    (by simpa only [B] using hxlower)
  have hQ1 : 1 ≤ Q := by
    have : 1 ≤ B ^ routeTLogHalfLengthExponent :=
      one_le_pow₀ (show 1 ≤ B by omega)
    rw [← hP] at this
    omega
  rw [norm_routeTLogTwistedShiftBilinearSum_eq_ratio hx0 hQ1 hscale]
  exact norm_routeTLogTwistedRatioBilinearSum_le_two_rpow_of_shell
    hu hC ht hbottom htop hxlower hxupper

end

end RHTower.Sieve
