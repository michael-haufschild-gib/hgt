import GaloisForLFunctions.RHTower.Sieve.VinogradovDyadicBlock

/-!
# Vinogradov's estimate for shifted logarithmic phases

For `0 ≤ α ≤ 1` the phase `(n + α)^{it} = e((t/2π) log(n + α))` obeys the same estimate as `n^{it}`:
for `22 ≤ r`, `P = 2Q` above the Vinogradov threshold, `P^{4r} ≤ t ≤ P^{4r+4}` and
`(A, A + L + 1] ⊂ [4P⁴, 162P⁴]`,

`‖Σ_{A<n≤A+L} (n+α)^{it}‖ ≤ 4e^{20} L P^{-δ_r} + 400 P²`   (`norm_sum_shiftedLogPhase_le_vinogradov`).

The shift `n ↦ n − (Q+l)(Q+m)` turns `(n+α)^{it}` into `(x+α)^{it} e((t/2π) log(1 − (Q+l)(Q+m)/(x+α)))`,
so the bilinear sum `R(t, x+α, Q)` of the corpus estimate appears at the real point `x + α`
(`sq_mul_norm_sum_shiftedLogPhase_le`); the pointwise bound for `R(t, y, Q)` holds at every real
`y ∈ [4P⁴, 162P⁴]` (`norm_routeTLogRatioBilinearSum_le_window`).
-/

open scoped BigOperators
open RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- **The bilinear sum at a real point.** For `4 ≤ r`, `P = 2Q` above the threshold,
`P^{4r} ≤ t ≤ P^{4r+4}` and `y ∈ [4P⁴, 162P⁴]`: `‖R(t,y,Q)‖ ≤ M_r P^{2−δ_r} + 1/2`. -/
theorem norm_routeTLogRatioBilinearSum_le_window {r Q : ℕ} {t y : ℝ} (hr : 4 ≤ r)
    (hP : vinogradovWeylThreshold r ≤ 2 * Q)
    (ht1 : ((2 * Q : ℕ) : ℝ) ^ (4 * r) ≤ t) (ht2 : t ≤ ((2 * Q : ℕ) : ℝ) ^ (4 * r + 4))
    (hylow : 4 * ((2 * Q : ℕ) : ℝ) ^ 4 ≤ y) (hyup : y ≤ 162 * ((2 * Q : ℕ) : ℝ) ^ 4) :
    ‖routeTLogRatioBilinearSum t y Q‖ ≤
      vinogradovWeylConstant r * ((2 * Q : ℕ) : ℝ) ^ (2 - vinogradovWeylSaving r) + 1 / 2 := by
  classical
  set k := vinogradovWeylDegree r with hk
  set b := vinogradovWeylMoment r with hb
  set P : ℝ := ((2 * Q : ℕ) : ℝ) with hPdef
  have hk3 : 3 ≤ k := three_le_vinogradovWeylDegree (by omega)
  have hb1 : 1 ≤ b := one_le_vinogradovWeylMoment r
  have hP48 : (2 : ℝ) ^ 48 ≤ P := by
    rw [hPdef]
    have : 2 ^ 48 ≤ 2 * Q := le_trans (le_max_left _ _) hP
    exact_mod_cast this
  have hPb : ((384 * b ^ 2 * k) ^ 2 : ℕ) ≤ P := by
    rw [hPdef]
    have : (384 * b ^ 2 * k) ^ 2 ≤ 2 * Q := le_trans (le_max_right _ _) hP
    exact_mod_cast this
  have hP1 : (1 : ℝ) ≤ P := le_trans (one_le_pow₀ (by norm_num)) hP48
  have hP0 : 0 < P := by linarith
  have hQ1 : 1 ≤ Q := by
    have : 2 ^ 48 ≤ 2 * Q := le_trans (le_max_left _ _) hP
    have h1 : 1 ≤ 2 ^ 48 := Nat.one_le_two_pow
    omega
  have hQP : (Q : ℝ) = P / 2 := by rw [hPdef]; push_cast; ring
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  set U := vinogradovWeylUseful r with hU
  set e : Fin k → ℕ := fun _ => vinogradovWeylSave r with he
  have hsave1 : 1 ≤ vinogradovWeylSave r := by unfold vinogradovWeylSave; omega
  set Mfull : ℝ := vinogradovExplicitConstant k b ^ 2 * (24 * (b : ℝ) ^ 2) ^ k with hMfull
  set D : ℝ := (k * (k + 1) / 2 : ℝ) * (1 - 1 / (k : ℝ)) ^ ((b : ℝ) / k) with hD
  have hD1 : D < 1 := vinogradovWeyl_defect_lt_one (by omega)
  have hD0 : 0 ≤ D := by
    have := Real.rpow_nonneg (rpow_one_sub_inv_pos (k := k) (by omega)).le ((b : ℝ) / k)
    rw [hD]; positivity
  set SU : ℕ := ∑ j ∈ (Finset.univ : Finset (Fin k)).filter U, e j with hSU
  have hSU : vinogradovWeylCount r * vinogradovWeylSave r ≤ SU := by
    rw [hSU, Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (le_card_vinogradovWeylUseful hr)
  have hMfull0 : 0 ≤ Mfull := by
    have := (vinogradovExplicitConstant_pos k b).le
    rw [hMfull]; positivity
  set bb : ℝ := (((4 * b ^ 2 : ℕ) : ℝ))⁻¹ with hbb
  have hbb0 : 0 < bb := by rw [hbb]; positivity
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by positivity) hylow
  have hscale : 4 * ((2 * Q : ℕ) : ℝ) ^ 2 ≤ y := by
    rw [← hPdef]
    have : P ^ 2 ≤ P ^ 4 := pow_le_pow_right₀ hP1 (by norm_num)
    linarith
  have hW4 := norm_routeTLogRatioBilinearSum_le_explicit (b := b) ht0 hy0 hk3 hb1 hQ1 hscale
    U e
    (fun j hj => by
      have := hj.1
      simp only [he, vinogradovWeylSave]
      unfold vinogradovWeylLow at this
      omega)
    (fun j hj => le_logTaylorMagnitude_mul hP48 ht1 hy0 hyup j (by
      have := hj.2
      simp only [he, vinogradovWeylSave]
      unfold vinogradovWeylHigh at this
      omega))
    (fun j hj => logTaylorMagnitude_mul_le_one hP1 ht2 hylow j (by
      have := hj.1
      simp only [he, vinogradovWeylSave]
      unfold vinogradovWeylLow at this
      omega))
    (fun j _ => absorb_le_pow hP48 hPb hsave1 ht1 hy0 hyup j)
  -- first term
  have hfirst : (Mfull * P ^ (8 * (b : ℝ) ^ 2 + 2 * D) * (P ^ SU)⁻¹) ^ bb ≤
      vinogradovWeylConstant r * P ^ (2 - vinogradovWeylSaving r) := by
    have hsplit : (Mfull * P ^ (8 * (b : ℝ) ^ 2 + 2 * D) * (P ^ SU)⁻¹) ^ bb =
        Mfull ^ bb * P ^ ((8 * (b : ℝ) ^ 2 + 2 * D - SU) * bb) := by
      have hPSU : (P ^ SU)⁻¹ = P ^ (-(SU : ℝ)) := by
        rw [Real.rpow_neg hP0.le, Real.rpow_natCast]
      rw [hPSU, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hMfull0 (by positivity), ← Real.rpow_mul hP0.le,
        ← Real.rpow_mul hP0.le, mul_assoc, ← Real.rpow_add hP0]
      congr 2
      ring
    have hMconst : Mfull ^ bb = vinogradovWeylConstant r := by
      rw [hMfull, hbb, vinogradovWeylConstant]
    rw [hsplit, hMconst]
    apply mul_le_mul_of_nonneg_left _ (by
      rw [← hMconst]; exact Real.rpow_nonneg hMfull0 _)
    apply Real.rpow_le_rpow_of_exponent_le hP1
    have hb2 : (0 : ℝ) < 4 * (b : ℝ) ^ 2 := by positivity
    have hbbv : bb = 1 / (4 * (b : ℝ) ^ 2) := by rw [hbb]; push_cast; ring
    have hSUR : ((vinogradovWeylCount r * vinogradovWeylSave r : ℕ) : ℝ) ≤ (SU : ℝ) := by
      exact_mod_cast hSU
    rw [hbbv, vinogradovWeylSaving]
    rw [show 2 - (((vinogradovWeylCount r * vinogradovWeylSave r : ℕ) : ℝ) - 2) /
        (4 * (b : ℝ) ^ 2) = (8 * (b : ℝ) ^ 2 + 2 - ((vinogradovWeylCount r *
          vinogradovWeylSave r : ℕ) : ℝ)) * (1 / (4 * (b : ℝ) ^ 2)) by field_simp; ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  -- second term
  have hsecond : 2 * Real.pi * (t / Real.pi * (P ^ 2 / y) ^ (k + 1)) *
      (Q : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [hQP]
    have hratio : P ^ 2 / y ≤ 1 / (4 * P ^ 2) := by
      rw [div_le_div_iff₀ hy0 (by positivity)]
      have e : P ^ 2 * (4 * P ^ 2) = 4 * P ^ 4 := by ring
      linarith
    have hr0 : 0 ≤ P ^ 2 / y := by positivity
    have hpow : (P ^ 2 / y) ^ (k + 1) ≤ (1 / (4 * P ^ 2)) ^ (k + 1) :=
      pow_le_pow_left₀ hr0 hratio _
    have hk1 : k + 1 = 2 * r + 3 := by rw [hk]; unfold vinogradovWeylDegree; ring
    have h4 : (1 / (4 * P ^ 2)) ^ (k + 1) ≤ 1 / (4 * P ^ (4 * r + 6)) := by
      rw [hk1, div_pow, one_pow, mul_pow, ← pow_mul]
      apply one_div_le_one_div_of_le (by positivity)
      have : (4 : ℝ) ≤ 4 ^ (2 * r + 3) := by
        calc (4 : ℝ) = 4 ^ 1 := by norm_num
          _ ≤ 4 ^ (2 * r + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [show 2 * (2 * r + 3) = 4 * r + 6 by ring]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hpi : 0 < Real.pi := Real.pi_pos
    calc 2 * Real.pi * (t / Real.pi * (P ^ 2 / y) ^ (k + 1)) * (P / 2) ^ 2
        = 2 * t * (P ^ 2 / y) ^ (k + 1) * (P / 2) ^ 2 := by field_simp
      _ ≤ 2 * P ^ (4 * r + 4) * (1 / (4 * P ^ (4 * r + 6))) * (P / 2) ^ 2 := by
          gcongr
          exact hpow.trans h4
      _ = 1 / 8 := by
          field_simp
          ring
      _ ≤ 1 / 2 := by norm_num
  calc ‖routeTLogRatioBilinearSum t y Q‖
      ≤ (Mfull * P ^ (8 * (b : ℝ) ^ 2 + 2 * D) * (P ^ SU)⁻¹) ^ bb +
          2 * Real.pi * (t / Real.pi * (P ^ 2 / y) ^ (k + 1)) * (Q : ℝ) ^ 2 := hW4
    _ ≤ _ := add_le_add hfirst hsecond

/-- The shifted logarithmic phase `(n + α)^{it} = e((t/2π) log(n + α))`. -/
def shiftedLogPhase (t α : ℝ) (n : ℕ) : ℂ :=
  finitePhaseChar (t / (2 * Real.pi) * Real.log (n + α))

theorem norm_shiftedLogPhase (t α : ℝ) (n : ℕ) : ‖shiftedLogPhase t α n‖ = 1 :=
  norm_finitePhaseChar _

/-- `(x − h + α)^{it} = (x+α)^{it} e((t/2π) log(1 − h/(x+α)))` for `h < x`, `α ≥ 0`. -/
theorem shiftedLogPhase_sub {t α : ℝ} (hα : 0 ≤ α) {x h : ℕ} (hhx : h < x) :
    shiftedLogPhase t α (x - h) =
      shiftedLogPhase t α x * finitePhaseChar (t / (2 * Real.pi) * Real.log (1 - h / (x + α))) := by
  unfold shiftedLogPhase
  rw [← finitePhaseChar_add]
  congr 1
  have hhxR : (h : ℝ) < x := by exact_mod_cast hhx
  have hx0 : (0 : ℝ) < x + α := by
    have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    linarith
  have h1 : (0 : ℝ) < 1 - h / (x + α) := by
    rw [sub_pos, div_lt_one hx0]; linarith
  have hcast : ((x - h : ℕ) : ℝ) + α = ((x : ℝ) + α) * (1 - h / (x + α)) := by
    rw [Nat.cast_sub hhx.le]
    field_simp
    ring
  rw [hcast, Real.log_mul hx0.ne' h1.ne']
  ring

/-- **Shift averaging.** `Q² ‖Σ_{A<n≤A+L} (n+α)^{it}‖ ≤ Σ_{A<x≤A+L} ‖R(t, x+α, Q)‖ + 8Q⁴` for
`4Q² ≤ A`, `α ≥ 0`. -/
theorem sq_mul_norm_sum_shiftedLogPhase_le {t α : ℝ} (hα : 0 ≤ α) {A L Q : ℕ}
    (hA : 4 * Q ^ 2 ≤ A) :
    (Q : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ioc A (A + L), shiftedLogPhase t α n‖ ≤
      ∑ x ∈ Finset.Ioc A (A + L), ‖routeTLogRatioBilinearSum t ((x : ℝ) + α) Q‖ +
        8 * (Q : ℝ) ^ 4 := by
  classical
  set S := ∑ n ∈ Finset.Ioc A (A + L), shiftedLogPhase t α n with hS
  set hh : Fin Q → Fin Q → ℕ := fun l m => (Q + l.val) * (Q + m.val) with hhdef
  have hhle : ∀ l m, hh l m < 4 * Q ^ 2 := by
    intro l m
    simp only [hhdef]
    have hl := l.isLt
    have hm := m.isLt
    calc (Q + l.val) * (Q + m.val) < (2 * Q) * (2 * Q) :=
          Nat.mul_lt_mul'' (by omega) (by omega)
      _ = 4 * Q ^ 2 := by ring
  set T : Fin Q → Fin Q → ℂ := fun l m =>
    ∑ x ∈ Finset.Ioc A (A + L), shiftedLogPhase t α (x - hh l m) with hTdef
  have hTreindex : ∀ l m, T l m =
      ∑ n ∈ Finset.Ioc (A - hh l m) (A + L - hh l m), shiftedLogPhase t α n := by
    intro l m
    have hle : hh l m ≤ A := le_trans (hhle l m).le hA
    have hmap := Finset.map_add_right_Ioc (A - hh l m) (A + L - hh l m) (hh l m)
    have e1 : A - hh l m + hh l m = A := Nat.sub_add_cancel hle
    have e2 : A + L - hh l m + hh l m = A + L := Nat.sub_add_cancel (by omega)
    rw [e1, e2] at hmap
    simp only [hTdef]
    rw [← hmap, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n _
    simp
  have hdiff : ∀ l m, ‖S - T l m‖ ≤ 8 * (Q : ℝ) ^ 2 := by
    intro l m
    rw [hTreindex]
    have hle : hh l m ≤ A := le_trans (hhle l m).le hA
    have h := norm_sum_Ioc_sub_sum_Ioc_shift_le (shiftedLogPhase t α)
      (fun n => (norm_shiftedLogPhase t α n).le) (L := L) hle
    have hhR : (hh l m : ℝ) ≤ 4 * (Q : ℝ) ^ 2 := by exact_mod_cast (hhle l m).le
    linarith
  have hmain : ∑ l : Fin Q, ∑ m : Fin Q, T l m =
      ∑ x ∈ Finset.Ioc A (A + L),
        shiftedLogPhase t α x * routeTLogRatioBilinearSum t ((x : ℝ) + α) Q := by
    have hpt : ∀ x ∈ Finset.Ioc A (A + L),
        shiftedLogPhase t α x * routeTLogRatioBilinearSum t ((x : ℝ) + α) Q =
          ∑ l : Fin Q, ∑ m : Fin Q, shiftedLogPhase t α (x - hh l m) := by
      intro x hx
      have hxA : A < x := (Finset.mem_Ioc.mp hx).1
      unfold routeTLogRatioBilinearSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      have hlt : hh l m < x := lt_of_lt_of_le (hhle l m) (le_trans hA hxA.le)
      rw [shiftedLogPhase_sub hα hlt]
      congr 3
      simp only [hhdef, vinogradovUpperHalfProduct]
      push_cast
      ring
    calc ∑ l : Fin Q, ∑ m : Fin Q, T l m
        = ∑ l : Fin Q, ∑ m : Fin Q, ∑ x ∈ Finset.Ioc A (A + L),
            shiftedLogPhase t α (x - hh l m) := rfl
      _ = ∑ l : Fin Q, ∑ x ∈ Finset.Ioc A (A + L), ∑ m : Fin Q,
            shiftedLogPhase t α (x - hh l m) :=
          Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = ∑ x ∈ Finset.Ioc A (A + L), ∑ l : Fin Q, ∑ m : Fin Q,
            shiftedLogPhase t α (x - hh l m) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun x hx => (hpt x hx).symm
  have hmain_norm : ‖∑ l : Fin Q, ∑ m : Fin Q, T l m‖ ≤
      ∑ x ∈ Finset.Ioc A (A + L), ‖routeTLogRatioBilinearSum t ((x : ℝ) + α) Q‖ := by
    rw [hmain]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, norm_shiftedLogPhase, one_mul]
  have hsplit : ((Q : ℂ) ^ 2) * S =
      ∑ l : Fin Q, ∑ m : Fin Q, T l m + ∑ l : Fin Q, ∑ m : Fin Q, (S - T l m) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, add_sub_cancel]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have herr : ‖∑ l : Fin Q, ∑ m : Fin Q, (S - T l m)‖ ≤ 8 * (Q : ℝ) ^ 4 := by
    calc ‖∑ l : Fin Q, ∑ m : Fin Q, (S - T l m)‖
        ≤ ∑ l : Fin Q, ∑ m : Fin Q, ‖S - T l m‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_sum_le _ _)
      _ ≤ ∑ _l : Fin Q, ∑ _m : Fin Q, 8 * (Q : ℝ) ^ 2 :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ => hdiff l m
      _ = 8 * (Q : ℝ) ^ 4 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hnorm : (Q : ℝ) ^ 2 * ‖S‖ = ‖((Q : ℂ) ^ 2) * S‖ := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
  rw [hnorm, hsplit]
  calc ‖∑ l : Fin Q, ∑ m : Fin Q, T l m + ∑ l : Fin Q, ∑ m : Fin Q, (S - T l m)‖
      ≤ ‖∑ l : Fin Q, ∑ m : Fin Q, T l m‖ + ‖∑ l : Fin Q, ∑ m : Fin Q, (S - T l m)‖ :=
        norm_add_le _ _
    _ ≤ _ := add_le_add hmain_norm herr

/-- **Vinogradov's estimate for shifted phases.** For `22 ≤ r`, `P = 2Q` above the threshold,
`P^{4r} ≤ t ≤ P^{4r+4}`, `0 ≤ α ≤ 1` and `4P⁴ ≤ A`, `A + L + 1 ≤ 162P⁴`:
`‖Σ_{A<n≤A+L} (n+α)^{it}‖ ≤ 4e^{20} L P^{-δ_r} + 400P²`,
`δ_r = 1/(5184 r² (⌊log₂ 9r²⌋ + 1)²)`. -/
theorem norm_sum_shiftedLogPhase_le_vinogradov {r Q A L : ℕ} {t α : ℝ} (hr : 22 ≤ r)
    (hP : vinogradovWeylThreshold r ≤ 2 * Q)
    (ht1 : ((2 * Q : ℕ) : ℝ) ^ (4 * r) ≤ t) (ht2 : t ≤ ((2 * Q : ℕ) : ℝ) ^ (4 * r + 4))
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hA : 4 * (2 * Q) ^ 4 ≤ A) (hAL : A + L + 1 ≤ 162 * (2 * Q) ^ 4) :
    ‖∑ n ∈ Finset.Ioc A (A + L), shiftedLogPhase t α n‖ ≤
      4 * Real.exp 20 * L * ((2 * Q : ℕ) : ℝ) ^
          (-(1 / (5184 * (r : ℝ) ^ 2 * ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) ^ 2))) +
        400 * ((2 * Q : ℕ) : ℝ) ^ 2 := by
  set P : ℝ := ((2 * Q : ℕ) : ℝ) with hPdef
  set δ : ℝ := 1 / (5184 * (r : ℝ) ^ 2 * ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) ^ 2) with hδdef
  have hP48 : (2 : ℝ) ^ 48 ≤ P := by
    rw [hPdef]
    have : 2 ^ 48 ≤ 2 * Q := le_trans (le_max_left _ _) hP
    exact_mod_cast this
  have hP1 : (1 : ℝ) ≤ P := le_trans (one_le_pow₀ (by norm_num)) hP48
  have hP0 : 0 < P := by linarith
  have hQ1 : 1 ≤ Q := by
    have : 2 ^ 48 ≤ 2 * Q := le_trans (le_max_left _ _) hP
    have h1 : 1 ≤ 2 ^ 48 := Nat.one_le_two_pow
    omega
  have hQP : (Q : ℝ) = P / 2 := by rw [hPdef]; push_cast; ring
  have hM := vinogradovWeylConstant_le (r := r) (by omega)
  have hsave := vinogradovWeylSaving_ge hr
  rw [← hδdef] at hsave
  -- the pointwise bound along the shifted points
  have hpoint : ∀ x ∈ Finset.Ioc A (A + L),
      ‖routeTLogRatioBilinearSum t ((x : ℝ) + α) Q‖ ≤ Real.exp 20 * P ^ 2 * P ^ (-δ) + 1 / 2 := by
    intro x hx
    have hxI := Finset.mem_Ioc.mp hx
    have hxlow : 4 * P ^ 4 ≤ (x : ℝ) + α := by
      have : 4 * (2 * Q) ^ 4 ≤ x := by omega
      have h : 4 * P ^ 4 ≤ (x : ℝ) := by rw [hPdef]; exact_mod_cast this
      linarith
    have hxup : (x : ℝ) + α ≤ 162 * P ^ 4 := by
      have : x + 1 ≤ 162 * (2 * Q) ^ 4 := by omega
      have h : (x : ℝ) + 1 ≤ 162 * P ^ 4 := by rw [hPdef]; exact_mod_cast this
      linarith
    have hw := norm_routeTLogRatioBilinearSum_le_window (by omega) hP ht1 ht2 hxlow hxup
    refine hw.trans ?_
    have hpow : P ^ (2 - vinogradovWeylSaving r) ≤ P ^ 2 * P ^ (-δ) := by
      rw [← Real.rpow_two, ← Real.rpow_add hP0]
      exact Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
    have hpow0 : 0 ≤ P ^ (2 - vinogradovWeylSaving r) := Real.rpow_nonneg hP0.le _
    have hM0 : 0 ≤ vinogradovWeylConstant r := Real.rpow_nonneg (by
      have := (vinogradovExplicitConstant_pos (vinogradovWeylDegree r)
        (vinogradovWeylMoment r)).le
      positivity) _
    have h1 : vinogradovWeylConstant r * P ^ (2 - vinogradovWeylSaving r) ≤
        Real.exp 20 * (P ^ 2 * P ^ (-δ)) :=
      mul_le_mul hM hpow hpow0 (by positivity)
    linarith
  have hshift := sq_mul_norm_sum_shiftedLogPhase_le hα0 (t := t) (A := A) (L := L) (Q := Q) (by
    have : Q ^ 2 ≤ (2 * Q) ^ 4 := by
      calc Q ^ 2 ≤ (2 * Q) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ (2 * Q) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega)
  have hsum : ∑ x ∈ Finset.Ioc A (A + L), ‖routeTLogRatioBilinearSum t ((x : ℝ) + α) Q‖ ≤
      L * (Real.exp 20 * P ^ 2 * P ^ (-δ) + 1 / 2) := by
    calc _ ≤ ∑ _x ∈ Finset.Ioc A (A + L), (Real.exp 20 * P ^ 2 * P ^ (-δ) + 1 / 2) :=
          Finset.sum_le_sum hpoint
      _ = _ := by rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]; congr 2; omega
  have hLP : (L : ℝ) ≤ 162 * P ^ 4 := by
    have : L ≤ 162 * (2 * Q) ^ 4 := by omega
    rw [hPdef]; exact_mod_cast this
  set S := ‖∑ n ∈ Finset.Ioc A (A + L), shiftedLogPhase t α n‖
  have hmain : (Q : ℝ) ^ 2 * S ≤ L * (Real.exp 20 * P ^ 2 * P ^ (-δ) + 1 / 2) +
      8 * (Q : ℝ) ^ 4 := hshift.trans (add_le_add hsum le_rfl)
  rw [hQP] at hmain
  have hP2 : 0 < (P / 2) ^ 2 := by positivity
  have hS : S ≤ (L * (Real.exp 20 * P ^ 2 * P ^ (-δ) + 1 / 2) + 8 * (P / 2) ^ 4) / (P / 2) ^ 2 := by
    rw [le_div_iff₀ hP2]; linarith
  refine hS.trans ?_
  rw [div_le_iff₀ hP2]
  set w := P ^ (-δ)
  have e1 : (4 * Real.exp 20 * L * w + 400 * P ^ 2) * (P / 2) ^ 2 =
      Real.exp 20 * L * (P ^ 2 * w) + 100 * P ^ 4 := by ring
  have e2 : (L : ℝ) * (Real.exp 20 * P ^ 2 * w + 1 / 2) + 8 * (P / 2) ^ 4 =
      Real.exp 20 * L * (P ^ 2 * w) + L / 2 + P ^ 4 / 2 := by ring
  rw [e1, e2]
  linarith [pow_nonneg hP0.le 4]

/-- **Vinogradov's estimate on a dyadic block, shifted.** For `0 ≤ α ≤ 1` and
`(A, A + L + 1] ⊂ [N, 2N]` the bound of `Sieve.norm_sum_logPhase_le_dyadic` holds for
`Σ_{A<n≤A+L} (n+α)^{it}`. -/
theorem norm_sum_shiftedLogPhase_le_dyadic {N R A L : ℕ} {t α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hR : 22 ≤ R) (hN : 3 ^ 8 ≤ N)
    (hNt : (N : ℝ) ^ 22 ≤ t) (htR : t ≤ ((N : ℝ) ^ ((1 : ℝ) / 4) / 3) ^ (4 * R))
    (hthr : (vinogradovWeylThreshold R : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) / 3)
    (hA : N ≤ A) (hAL : A + L + 1 ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc A (A + L), shiftedLogPhase t α n‖ ≤
      12 * Real.exp 20 * L * (N : ℝ) ^ (-(vinogradovDyadicSaving R / 4)) +
        200 * (N : ℝ) ^ ((1 : ℝ) / 2) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (N : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hy] at htR hthr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hy0 : 0 < y := by rw [hy]; exact Real.rpow_pos_of_pos hN0 _
  have hy4 : y ^ 4 = N := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hy9 : (9 : ℝ) ≤ y := by
    have h : ((3 : ℝ) ^ 8) ^ ((1 : ℝ) / 4) ≤ y := by
      rw [hy]; exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN) (by norm_num)
    have e : ((3 : ℝ) ^ 8) ^ ((1 : ℝ) / 4) = 9 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  -- the even integer `P`
  set Q : ℕ := ⌈y / 6⌉₊ with hQ
  set P : ℝ := ((2 * Q : ℕ) : ℝ) with hP
  have hQlow : y / 6 ≤ Q := Nat.le_ceil _
  have hQup : (Q : ℝ) < y / 6 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hPlow : y / 3 ≤ P := by rw [hP]; push_cast; linarith
  have hPup : P ≤ y * (7 / 10) := by
    rw [hP]; push_cast; nlinarith
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hPlow
  have hP1 : 1 < P := by nlinarith
  have hQ1 : 1 ≤ Q := by
    have : (1 : ℝ) ≤ Q := by nlinarith
    exact_mod_cast this
  -- `[N, 2N] ⊂ [4P⁴, 162P⁴]`
  have hP4up : 4 * P ^ 4 ≤ N := by
    rw [← hy4]
    have : P ^ 4 ≤ (y * (7 / 10)) ^ 4 := pow_le_pow_left₀ hP0.le hPup 4
    nlinarith [pow_nonneg hy0.le 4]
  have hP4low : (2 * N : ℝ) ≤ 162 * P ^ 4 := by
    rw [← hy4]
    have : (y / 3) ^ 4 ≤ P ^ 4 := pow_le_pow_left₀ (by positivity) hPlow 4
    nlinarith
  have hPQ : P = 2 * (Q : ℝ) := by rw [hP]; push_cast; ring
  have hAnat : 4 * (2 * Q) ^ 4 ≤ A := by
    have : ((4 * (2 * Q) ^ 4 : ℕ) : ℝ) ≤ N := by
      push_cast; rw [hPQ] at hP4up; exact hP4up
    have : 4 * (2 * Q) ^ 4 ≤ N := by exact_mod_cast this
    omega
  have hALnat : A + L + 1 ≤ 162 * (2 * Q) ^ 4 := by
    have : ((2 * N : ℕ) : ℝ) ≤ ((162 * (2 * Q) ^ 4 : ℕ) : ℝ) := by
      push_cast; rw [hPQ] at hP4low; exact hP4low
    have : 2 * N ≤ 162 * (2 * Q) ^ 4 := by exact_mod_cast this
    omega
  -- the order `r`
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hNt
  set r : ℕ := ⌊Real.log t / (4 * Real.log P)⌋₊ with hr
  have hlogt : Real.log t = Real.log t := rfl
  have hr_le : (r : ℝ) ≤ Real.log t / (4 * Real.log P) := Nat.floor_le (by
    have : 0 ≤ Real.log t := Real.log_nonneg (le_trans (one_le_pow₀ (by
      exact_mod_cast (by omega : 1 ≤ N))) hNt)
    positivity)
  have hr_lt : Real.log t / (4 * Real.log P) < r + 1 := Nat.lt_floor_add_one _
  have ht1 : P ^ (4 * r) ≤ t := by
    rw [← Real.rpow_natCast, Real.rpow_le_iff_le_log hP0 ht0]
    rw [le_div_iff₀ (by positivity)] at hr_le
    push_cast; linarith
  have ht2 : t ≤ P ^ (4 * r + 4) := by
    rw [← Real.rpow_natCast, Real.le_rpow_iff_log_le ht0 hP0]
    rw [div_lt_iff₀ (by positivity)] at hr_lt
    push_cast; linarith
  have hlogPy : Real.log P ≤ Real.log y := Real.log_le_log hP0 (by linarith)
  have hlogyN : 4 * Real.log y = Real.log N := by
    rw [← hy4, Real.log_pow]; push_cast; ring
  have hr22 : 22 ≤ r := by
    have h1 : 22 * Real.log N ≤ Real.log t := by
      have := Real.log_le_log (by positivity) hNt
      rwa [Real.log_pow] at this
    have h2 : (22 : ℝ) ≤ Real.log t / (4 * Real.log P) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    exact Nat.le_floor (by exact_mod_cast h2)
  have hrR : r ≤ R := by
    have hle : t ≤ P ^ (4 * R) := htR.trans (pow_le_pow_left₀ (by positivity) hPlow _)
    have h1 : Real.log t ≤ (4 * R) * Real.log P := by
      have := Real.log_le_log ht0 hle
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have h2 : Real.log t / (4 * Real.log P) ≤ R := by
      rw [div_le_iff₀ (by positivity)]; linarith
    exact Nat.floor_le_of_le h2
  have hthrP : vinogradovWeylThreshold r ≤ 2 * Q := by
    have h1 := vinogradovWeylThreshold_mono hrR
    have h2 : (vinogradovWeylThreshold R : ℝ) ≤ P := hthr.trans hPlow
    have : (vinogradovWeylThreshold R : ℝ) ≤ ((2 * Q : ℕ) : ℝ) := h2
    have h3 : vinogradovWeylThreshold R ≤ 2 * Q := by exact_mod_cast this
    omega
  have hmain := norm_sum_shiftedLogPhase_le_vinogradov hr22 hthrP ht1 ht2 hα0 hα1 hAnat hALnat
  rw [← hP] at hmain
  -- convert to `N`
  have hδ := vinogradovDyadicSaving_anti (by omega : 1 ≤ r) hrR
  have hδ0 := vinogradovDyadicSaving_pos R (by omega)
  have hpow1 : P ^ (-(1 / (5184 * (r : ℝ) ^ 2 * ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) ^ 2))) ≤
      P ^ (-vinogradovDyadicSaving R) := by
    apply Real.rpow_le_rpow_of_exponent_le hP1.le
    unfold vinogradovDyadicSaving at hδ ⊢
    linarith
  have hpow2 : P ^ (-vinogradovDyadicSaving R) ≤
      3 * (N : ℝ) ^ (-(vinogradovDyadicSaving R / 4)) := by
    calc P ^ (-vinogradovDyadicSaving R) ≤ (y / 3) ^ (-vinogradovDyadicSaving R) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hPlow (by linarith)
      _ = 3 ^ vinogradovDyadicSaving R * y ^ (-vinogradovDyadicSaving R) := by
          rw [Real.div_rpow hy0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
          field_simp
      _ ≤ 3 * y ^ (-vinogradovDyadicSaving R) := by
          gcongr
          calc (3 : ℝ) ^ vinogradovDyadicSaving R ≤ 3 ^ (1 : ℝ) := by
                apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
                unfold vinogradovDyadicSaving
                rw [div_le_one (by positivity)]
                have hR22 : (22 : ℝ) ≤ R := by exact_mod_cast hR
                have hm1 : (1 : ℝ) ≤ ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) := by
                  exact_mod_cast (Nat.le_add_left 1 _)
                have hR2 : (1 : ℝ) ≤ (R : ℝ) ^ 2 := one_le_pow₀ (by linarith)
                have hm2 : (1 : ℝ) ≤ ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) ^ 2 := one_le_pow₀ hm1
                have h := mul_le_mul (mul_le_mul (show (1 : ℝ) ≤ 5184 by norm_num) hR2
                  (by norm_num) (by norm_num)) hm2 (by norm_num) (by positivity)
                linarith
            _ = 3 := Real.rpow_one 3
      _ = 3 * (N : ℝ) ^ (-(vinogradovDyadicSaving R / 4)) := by
          rw [hy, ← Real.rpow_mul hN0.le,
            show (1 : ℝ) / 4 * -vinogradovDyadicSaving R = -(vinogradovDyadicSaving R / 4) by ring]
  have hP2 : P ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) / 2 := by
    have hy2 : y ^ 2 = (N : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    have h1 : P ^ 2 ≤ (y * (7 / 10)) ^ 2 := pow_le_pow_left₀ hP0.le hPup 2
    have h2 : (y * (7 / 10)) ^ 2 = 49 / 100 * y ^ 2 := by ring
    have h3 : 0 ≤ y ^ 2 := sq_nonneg y
    rw [← hy2]
    linarith
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hE : (0 : ℝ) ≤ 4 * Real.exp 20 := by positivity
  calc ‖∑ n ∈ Finset.Ioc A (A + L), shiftedLogPhase t α n‖
      ≤ 4 * Real.exp 20 * L *
          P ^ (-(1 / (5184 * (r : ℝ) ^ 2 * ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) ^ 2))) +
        400 * P ^ 2 := hmain
    _ ≤ 4 * Real.exp 20 * L * (3 * (N : ℝ) ^ (-(vinogradovDyadicSaving R / 4))) +
        400 * ((N : ℝ) ^ ((1 : ℝ) / 2) / 2) := by
        gcongr
        exact hpow1.trans hpow2
    _ = 12 * Real.exp 20 * L * (N : ℝ) ^ (-(vinogradovDyadicSaving R / 4)) +
        200 * (N : ℝ) ^ ((1 : ℝ) / 2) := by ring


end

end GaloisForLFunctions.MatomakiRadziwill
