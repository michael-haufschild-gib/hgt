import GaloisForLFunctions.RHTower.Sieve.FreeScaleTileCount
import GaloisForLFunctions.RHTower.Sieve.WindowTiling

/-!
# Covering every scale by a start modulus

The bottoms `tileBase K₀ u = (2^{K₀+1}u)²⌊log(2^{K₀+1}u)⌋` of the tile ranges grow by a factor at
most `3/2` from one index to the next, so the ranges `[tileBase K₀ u, 2·tileBase K₀ u]` cover every
sufficiently large scale.
-/

namespace RHTower.Sieve

open Finset Filter ArithmeticFunction

noncomputable section

theorem tileM_succ_le {K₀ u : ℕ} (hu : 0 < u) :
    ((tileM K₀ (u + 1) : ℕ) : ℝ) ≤ Real.exp 1 * ((tileM K₀ u : ℕ) : ℝ) := by
  rw [tileM, tileM]
  push_cast
  have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hq : (0 : ℝ) < (2 : ℝ) ^ (K₀ + 1) := by positivity
  have hkey : (u : ℝ) + 1 ≤ Real.exp 1 * (u : ℝ) := by nlinarith [hu1, he]
  calc (2 : ℝ) ^ (K₀ + 1) * ((u : ℝ) + 1)
      ≤ (2 : ℝ) ^ (K₀ + 1) * (Real.exp 1 * (u : ℝ)) := mul_le_mul_of_nonneg_left hkey hq.le
    _ = Real.exp 1 * ((2 : ℝ) ^ (K₀ + 1) * (u : ℝ)) := by ring

/-- **The integer logarithm of the start modulus grows by at most one.** -/
theorem tileLog_succ_le {K₀ u : ℕ} (hu : 0 < u) : tileLog K₀ (u + 1) ≤ tileLog K₀ u + 1 := by
  have hm0 : 0 < tileM K₀ u := tileM_pos hu
  have hmR : (1 : ℝ) ≤ ((tileM K₀ u : ℕ) : ℝ) := by exact_mod_cast hm0
  have hstep : Real.log ((tileM K₀ (u + 1) : ℕ) : ℝ)
      ≤ Real.log ((tileM K₀ u : ℕ) : ℝ) + 1 := by
    have h1 := tileM_succ_le (K₀ := K₀) hu
    have hpos : (0 : ℝ) < ((tileM K₀ (u + 1) : ℕ) : ℝ) := by
      have : 0 < tileM K₀ (u + 1) := tileM_pos (by omega)
      exact_mod_cast this
    have h2 : Real.log ((tileM K₀ (u + 1) : ℕ) : ℝ)
        ≤ Real.log (Real.exp 1 * ((tileM K₀ u : ℕ) : ℝ)) := Real.log_le_log hpos h1
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (by linarith), Real.log_exp] at h2
    linarith
  rw [tileLog, tileLog]
  calc ⌊Real.log ((tileM K₀ (u + 1) : ℕ) : ℝ)⌋₊
      ≤ ⌊Real.log ((tileM K₀ u : ℕ) : ℝ) + 1⌋₊ := Nat.floor_le_floor hstep
    _ = ⌊Real.log ((tileM K₀ u : ℕ) : ℝ)⌋₊ + 1 := Nat.floor_add_one (Real.log_nonneg hmR)

/-- **The bottom of the physical range grows by at most a half.** -/
theorem tileBase_succ_le {K₀ u : ℕ} (hu : 8 ≤ u) (hT : 8 ≤ tileLog K₀ u) :
    2 * tileBase K₀ (u + 1) ≤ 3 * tileBase K₀ u := by
  set T : ℕ := tileLog K₀ u with hTdef
  set T' : ℕ := tileLog K₀ (u + 1) with hT'def
  have hTT : T' ≤ T + 1 := by rw [hT'def, hTdef]; exact tileLog_succ_le (by omega)
  -- the scale-free core of the estimate
  have h1 : 64 * (u + 1) ^ 2 ≤ 81 * u ^ 2 := by nlinarith [hu]
  have h2 : 8 * (T + 1) ≤ 9 * T := by omega
  have hprod : (64 * (u + 1) ^ 2) * (8 * (T + 1)) ≤ (81 * u ^ 2) * (9 * T) :=
    Nat.mul_le_mul h1 h2
  have hcore : 2 * (u + 1) ^ 2 * (T + 1) ≤ 3 * u ^ 2 * T := by
    have hexp : (64 * (u + 1) ^ 2) * (8 * (T + 1)) = 512 * ((u + 1) ^ 2 * (T + 1)) := by ring
    have hexp2 : (81 * u ^ 2) * (9 * T) = 729 * (u ^ 2 * T) := by ring
    rw [hexp, hexp2] at hprod
    have hgoal : 512 * (2 * (u + 1) ^ 2 * (T + 1)) ≤ 512 * (3 * u ^ 2 * T) := by
      have hL : 512 * (2 * (u + 1) ^ 2 * (T + 1)) = 2 * (512 * ((u + 1) ^ 2 * (T + 1))) := by ring
      have hR : 512 * (3 * u ^ 2 * T) = 1536 * (u ^ 2 * T) := by ring
      rw [hL, hR]
      omega
    exact Nat.le_of_mul_le_mul_left hgoal (by norm_num)
  -- multiply by the square of the power of two
  set q : ℕ := 2 ^ (K₀ + 1) with hq
  have hrw : ∀ v : ℕ, tileBase K₀ v = q * q * (v * v * tileLog K₀ v) := by
    intro v
    rw [tileBase, tileM, hq]
    ring
  rw [hrw, hrw]
  have hstep : 2 * ((u + 1) * (u + 1) * T') ≤ 3 * (u * u * T) := by
    have hmono : (u + 1) * (u + 1) * T' ≤ (u + 1) * (u + 1) * (T + 1) :=
      Nat.mul_le_mul_left _ hTT
    have hA : 2 * ((u + 1) * (u + 1) * T') ≤ 2 * ((u + 1) * (u + 1) * (T + 1)) :=
      Nat.mul_le_mul_left 2 hmono
    have hB : 2 * ((u + 1) * (u + 1) * (T + 1)) ≤ 3 * (u * u * T) := by
      have hEq1 : 2 * ((u + 1) * (u + 1) * (T + 1)) = 2 * (u + 1) ^ 2 * (T + 1) := by ring
      have hEq2 : 3 * u ^ 2 * T = 3 * (u * u * T) := by ring
      rw [hEq1, ← hEq2]
      exact hcore
    exact le_trans hA hB
  calc 2 * (q * q * ((u + 1) * (u + 1) * T'))
      = q * q * (2 * ((u + 1) * (u + 1) * T')) := by ring
    _ ≤ q * q * (3 * (u * u * T)) := Nat.mul_le_mul_left _ hstep
    _ = 3 * (q * q * (u * u * T)) := by ring

/-- **The bottom of the physical range exceeds its index.** -/
theorem lt_tileBase {K₀ u : ℕ} (hu : 0 < u) (hT : 1 ≤ tileLog K₀ u) : u < tileBase K₀ u := by
  have hm : u < tileM K₀ u := by
    rw [tileM]
    have : (2 : ℕ) ^ (K₀ + 1) * u ≥ 2 * u := Nat.mul_le_mul_right u (by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (K₀ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hm0 : 0 < tileM K₀ u := tileM_pos hu
  calc u < tileM K₀ u := hm
    _ = tileM K₀ u * 1 * 1 := by ring
    _ ≤ tileM K₀ u * tileM K₀ u * tileLog K₀ u :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hm0) hT
    _ = tileBase K₀ u := by rw [tileBase]

/-- **Every large scale lies in the range of some start modulus.** -/
theorem exists_cover {K₀ Z u₀ : ℕ} (hu₀Z : u₀ ≤ Z) (hbig : tileBase K₀ u₀ ≤ Z)
    (hu₀ : 8 ≤ u₀) (hZlog : 1 ≤ tileLog K₀ Z)
    (hsucc : ∀ v, u₀ ≤ v → 2 * tileBase K₀ (v + 1) ≤ 3 * tileBase K₀ v) :
    ∃ u, u₀ ≤ u ∧ tileBase K₀ u ≤ Z ∧ 2 * Z < 3 * tileBase K₀ u := by
  classical
  have hZ0 : 0 < Z := by omega
  have hPZ : ¬ (tileBase K₀ Z ≤ Z) := not_le.2 (lt_tileBase hZ0 hZlog)
  have hspec : tileBase K₀ (Nat.findGreatest (fun v => tileBase K₀ v ≤ Z) Z) ≤ Z :=
    Nat.findGreatest_spec (P := fun v => tileBase K₀ v ≤ Z) hu₀Z hbig
  have hge : u₀ ≤ Nat.findGreatest (fun v => tileBase K₀ v ≤ Z) Z :=
    Nat.le_findGreatest (P := fun v => tileBase K₀ v ≤ Z) hu₀Z hbig
  have hle : Nat.findGreatest (fun v => tileBase K₀ v ≤ Z) Z ≤ Z :=
    Nat.findGreatest_le (P := fun v => tileBase K₀ v ≤ Z) Z
  have hlt : Nat.findGreatest (fun v => tileBase K₀ v ≤ Z) Z < Z := by
    rcases lt_or_eq_of_le hle with hcase | hcase
    · exact hcase
    · exfalso
      rw [hcase] at hspec
      exact hPZ hspec
  have hnot : ¬ (tileBase K₀ (Nat.findGreatest (fun v => tileBase K₀ v ≤ Z) Z + 1) ≤ Z) :=
    Nat.findGreatest_is_greatest (P := fun v => tileBase K₀ v ≤ Z)
      (Nat.lt_succ_self _) (by omega)
  refine ⟨Nat.findGreatest (fun v => tileBase K₀ v ≤ Z) Z, hge, hspec, ?_⟩
  have hgt : Z < tileBase K₀ (Nat.findGreatest (fun v => tileBase K₀ v ≤ Z) Z + 1) :=
    not_le.1 hnot
  have hs := hsucc (Nat.findGreatest (fun v => tileBase K₀ v ≤ Z) Z) hge
  omega

/-- **The integer logarithm of the start modulus is monotone.** -/
theorem tileLog_mono (K₀ : ℕ) {a b : ℕ} (hab : a ≤ b) (ha : 0 < a) :
    tileLog K₀ a ≤ tileLog K₀ b := by
  have h1 : 0 < tileM K₀ a := tileM_pos ha
  have h1R : (0 : ℝ) < ((tileM K₀ a : ℕ) : ℝ) := by exact_mod_cast h1
  have hab' : tileM K₀ a ≤ tileM K₀ b := by
    rw [tileM, tileM]; exact Nat.mul_le_mul_left _ hab
  have habR : ((tileM K₀ a : ℕ) : ℝ) ≤ ((tileM K₀ b : ℕ) : ℝ) := by exact_mod_cast hab'
  rw [tileLog, tileLog]
  exact Nat.floor_le_floor (Real.log_le_log h1R habR)

/-- **The window of a tile is positive.** -/
theorem tileLen_pos {β : ℝ} {K₀ u : ℕ} (hu : 0 < u) (hT : 0 < tileLog K₀ u) :
    0 < tileLen β K₀ u := by
  have hm := tileM_pos (K₀ := K₀) hu
  have hmR : (0 : ℝ) < ((tileM K₀ u : ℕ) : ℝ) := by exact_mod_cast hm
  have hP : 0 < tileBase K₀ u := by
    rw [tileBase]; exact Nat.mul_pos (Nat.mul_pos hm hm) hT
  have hPR : (0 : ℝ) < ((tileBase K₀ u : ℕ) : ℝ) := by exact_mod_cast hP
  have hC := tileC_pos β K₀ u
  rw [tileLen]
  refine Nat.pos_of_ne_zero fun hzero => ?_
  have hle : (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((tileBase K₀ u : ℕ) : ℝ))
      / ((tileM K₀ u : ℕ) : ℝ) ≤ 0 := by
    have := Nat.le_ceil ((2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1))
      * (2 * ((tileBase K₀ u : ℕ) : ℝ)) / ((tileM K₀ u : ℕ) : ℝ))
    rw [hzero] at this
    simpa using this
  have hpos : (0 : ℝ) < (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1))
      * (2 * ((tileBase K₀ u : ℕ) : ℝ)) / ((tileM K₀ u : ℕ) : ℝ) := by positivity
  linarith

set_option maxHeartbeats 1600000 in
/-- **The tiled sign count.**  Every large scale `Z` admits a start modulus whose tile length
divides every admissible window into blocks on each of which the marker construction applies. -/
theorem tiled_count {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (K₀ : ℕ) (hharm : 0 < multiHarmConst K₀) :
    ∀ᶠ Z : ℕ in atTop, ∃ u : ℕ, tileBase K₀ u ≤ Z ∧ 2 * Z < 3 * tileBase K₀ u ∧
      ∀ H : ℕ, 3 * H ≤ Z → 2 * tileLen β K₀ u ≤ H →
        tileConst K₀ / 4 * ((H : ℝ) / Real.log ((Z : ℕ) : ℝ))
          ≤ ((((Finset.Ioc Z (Z + H)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  have hTC := tileConst_pos K₀ hharm
  obtain ⟨u₁, hu₁⟩ := Filter.eventually_atTop.1 (tile_count_clean hβ0 hβ1 hσ K₀ hharm)
  obtain ⟨u₂, hu₂⟩ := Filter.eventually_atTop.1 (eventually_tileLog_ge K₀ 8)
  set u₀ : ℕ := max (max u₁ u₂) 8 with hu₀def
  have hsucc : ∀ v, u₀ ≤ v → 2 * tileBase K₀ (v + 1) ≤ 3 * tileBase K₀ v := fun v hv =>
    tileBase_succ_le (by omega) (hu₂ v (by omega))
  filter_upwards [eventually_ge_atTop u₀, eventually_ge_atTop (tileBase K₀ u₀),
    eventually_tileLog_ge K₀ 1, eventually_ge_atTop 2] with Z hZu hZb hZlog hZ2
  obtain ⟨u, hu0, hPu, hcov⟩ := exists_cover hZu hZb (by omega) hZlog hsucc
  refine ⟨u, hPu, hcov, ?_⟩
  intro H hH3 hHh
  set h : ℕ := tileLen β K₀ u with hhdef
  have hu8 : 8 ≤ u := by omega
  have hTu : 8 ≤ tileLog K₀ u := hu₂ u (by omega)
  have hh0 : 0 < h := by rw [hhdef]; exact tileLen_pos (by omega) (by omega)
  set N : ℕ := H / h with hNdef
  have hNh : N * h ≤ H := Nat.div_mul_le_self H h
  have hNlt : H < (N + 1) * h := by
    rw [hNdef]
    exact (Nat.div_lt_iff_lt_mul hh0).1 (Nat.lt_succ_self _)
  have hHN : H ≤ 2 * (N * h) := by nlinarith [hNlt, hHh, hh0]
  -- every tile lies in the range served by the modulus
  have hZH : Z + H ≤ 2 * tileBase K₀ u := by omega
  have hZ2Z : Z + H ≤ 2 * Z := by omega
  have hcount : ∀ j, j < N →
      tileConst K₀ * ((h : ℝ) / Real.log ((2 * Z : ℕ) : ℝ))
        ≤ ((((Finset.Ioc (Z + j * h) (Z + j * h + h)).filter
            (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
    intro j hj
    have hjh : j * h + h ≤ N * h := by
      have h1 : (j + 1) * h ≤ N * h := Nat.mul_le_mul_right h (by omega)
      have h2 : (j + 1) * h = j * h + h := by ring
      omega
    have hlo : tileBase K₀ u ≤ Z + j * h := by omega
    have hhi : Z + j * h ≤ 2 * tileBase K₀ u := by omega
    have hbase := hu₁ u (by omega) (Z + j * h) hlo hhi
    refine le_trans ?_ hbase
    have hX2 : (2 : ℝ) ≤ ((Z + j * h : ℕ) : ℝ) := by
      have : 2 ≤ Z + j * h := by omega
      exact_mod_cast this
    have hXle : ((Z + j * h : ℕ) : ℝ) ≤ ((2 * Z : ℕ) : ℝ) := by
      have : Z + j * h ≤ 2 * Z := by omega
      exact_mod_cast this
    have hlogX : (0 : ℝ) < Real.log ((Z + j * h : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hmono : Real.log ((Z + j * h : ℕ) : ℝ) ≤ Real.log ((2 * Z : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hXle
    have hdiv : (h : ℝ) / Real.log ((2 * Z : ℕ) : ℝ)
        ≤ (h : ℝ) / Real.log ((Z + j * h : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlogX hmono
    exact mul_le_mul_of_nonneg_left hdiv hTC.le
  have htile := card_filter_Ioc_tile (X := Z) (N := N) (h := h)
    (fun n => moebius n = σ) hcount
  -- the tiled window sits inside the prescribed one
  have hsub : ((Finset.Ioc Z (Z + N * h)).filter (fun n => moebius n = σ)).card
      ≤ ((Finset.Ioc Z (Z + H)).filter (fun n => moebius n = σ)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.Ioc_subset_Ioc_right (by omega)))
  have hsubR : ((((Finset.Ioc Z (Z + N * h)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ)
      ≤ ((((Finset.Ioc Z (Z + H)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
    exact_mod_cast hsub
  refine le_trans ?_ (le_trans htile hsubR)
  -- the arithmetic of the tiling constant
  have hlogZ : (0 : ℝ) < Real.log ((Z : ℕ) : ℝ) := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ ((Z : ℕ) : ℝ) := by exact_mod_cast hZ2
    linarith
  have hlog2Z : Real.log ((2 * Z : ℕ) : ℝ) ≤ 2 * Real.log ((Z : ℕ) : ℝ) := by
    have hZ0 : (0 : ℝ) < ((Z : ℕ) : ℝ) := by
      have : (2 : ℝ) ≤ ((Z : ℕ) : ℝ) := by exact_mod_cast hZ2
      linarith
    have hcast : ((2 * Z : ℕ) : ℝ) = 2 * ((Z : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, Real.log_mul (by norm_num) (ne_of_gt hZ0)]
    have hZ2R : (2 : ℝ) ≤ ((Z : ℕ) : ℝ) := by exact_mod_cast hZ2
    have hlt : Real.log 2 ≤ Real.log ((Z : ℕ) : ℝ) := Real.log_le_log (by norm_num) hZ2R
    linarith
  have hlog2Z0 : (0 : ℝ) < Real.log ((2 * Z : ℕ) : ℝ) := by
    have hcast : ((2 * Z : ℕ) : ℝ) = 2 * ((Z : ℕ) : ℝ) := by push_cast; ring
    have hZ0 : (2 : ℝ) ≤ ((Z : ℕ) : ℝ) := by exact_mod_cast hZ2
    rw [hcast]
    exact Real.log_pos (by linarith)
  have hNhR : (H : ℝ) ≤ 2 * ((N : ℝ) * (h : ℝ)) := by exact_mod_cast hHN
  have hval : (N : ℝ) * (tileConst K₀ * ((h : ℝ) / Real.log ((2 * Z : ℕ) : ℝ)))
      = tileConst K₀ * ((N : ℝ) * (h : ℝ)) / Real.log ((2 * Z : ℕ) : ℝ) := by
    field_simp
    try ring
  rw [hval]
  have hgoal : tileConst K₀ / 4 * ((H : ℝ) / Real.log ((Z : ℕ) : ℝ))
      = (tileConst K₀ / 4 * (H : ℝ)) / Real.log ((Z : ℕ) : ℝ) := by ring
  rw [hgoal, div_le_div_iff₀ hlogZ hlog2Z0]
  have hH0R : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hNh0 : (0 : ℝ) ≤ (N : ℝ) * (h : ℝ) := by positivity
  have hstep1 : tileConst K₀ / 4 * (H : ℝ) * Real.log ((2 * Z : ℕ) : ℝ)
      ≤ tileConst K₀ / 4 * (H : ℝ) * (2 * Real.log ((Z : ℕ) : ℝ)) := by
    have hnn : (0 : ℝ) ≤ tileConst K₀ / 4 * (H : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hlog2Z hnn
  have hstep2 : tileConst K₀ / 4 * (H : ℝ) * (2 * Real.log ((Z : ℕ) : ℝ))
      ≤ tileConst K₀ * ((N : ℝ) * (h : ℝ)) * Real.log ((Z : ℕ) : ℝ) := by
    have hmul : tileConst K₀ * (H : ℝ) ≤ tileConst K₀ * (2 * ((N : ℝ) * (h : ℝ))) :=
      mul_le_mul_of_nonneg_left hNhR hTC.le
    nlinarith [hmul, hlogZ.le]
  linarith [hstep1, hstep2]

end

end RHTower.Sieve
