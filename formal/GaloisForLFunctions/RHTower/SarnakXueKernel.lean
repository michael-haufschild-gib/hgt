import GaloisForLFunctions.RHTower.SarnakXuePretrace
import GaloisForLFunctions.RHTower.SarnakXueCounting
import GaloisForLFunctions.RHTower.HyperbolicLens

open MeasureTheory UpperHalfPlane ModularGroup Set Metric
open scoped MatrixGroups Pointwise ENNReal

/-!
# The kernel sum of the pretrace inequality

For `h ∈ Γ̄(p)` the ball `h B_R(w)` is `B_R(hw)`; balls at distance `> 2R` are disjoint, so only the finitely
many `h` with `2 cosh d(w, hw) ≤ 2 cosh 2R` contribute (`near_finite`). The lens bound, the inequality
`1/cosh(d/2) ≤ √2/√(cosh d)`, a dyadic decomposition of `cosh d` and the counting bound in `Γ(p)` give
`Σ_{h ∈ Γ̄(p)} μ(B_R(w) ∩ h B_R(w)) ≤ 16√2 cosh R · A (2^{K+2})^ε (4 + 2K(y+1)/p + 4K√(2^K)/p³)` whenever
`cosh 2R < 2^K`, with `A = 32(1 + C 9^ε)` (`kernel_sum_le`).
-/

namespace GaloisForLFunctions.RHTower.SarnakXueKernel

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.SarnakXuePretrace
open CongruenceSubgroup

noncomputable section

theorem dist_sl_smul (γ : SL(2, ℤ)) (a b : ℍ) : dist (γ • a) (γ • b) = dist a b := by
  show dist ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ : SL(2, ℝ)) • a)
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ : SL(2, ℝ)) • b) = dist a b
  exact dist_smul _ _ _

variable {p : ℕ}

theorem gammaBar_lift (h : gammaBar p) : ∃ γ ∈ Gamma p, (QuotientGroup.mk γ : PSL2Z) = h := by
  obtain ⟨γ, hγ, he⟩ := h.2
  exact ⟨γ, hγ, he⟩

/-- A chosen lift of `h ∈ Γ̄(p)` to `Γ(p)`. -/
def lift (h : gammaBar p) : SL(2, ℤ) := (gammaBar_lift h).choose

theorem lift_mem (h : gammaBar p) : lift h ∈ Gamma p := (gammaBar_lift h).choose_spec.1

theorem lift_mk (h : gammaBar p) : (QuotientGroup.mk (lift h) : PSL2Z) = h :=
  (gammaBar_lift h).choose_spec.2

theorem lift_injective : Function.Injective (lift (p := p)) := by
  intro h h' e
  apply Subtype.ext
  rw [← lift_mk h, ← lift_mk h', e]

theorem smul_eq_lift (h : gammaBar p) (z : ℍ) : h • z = lift h • z := by
  rw [Subgroup.smul_def, ← lift_mk h, PSL2Z_mk_smul]

theorem smul_closedBall' (h : gammaBar p) (w : ℍ) (R : ℝ) :
    h • closedBall w R = closedBall (h • w) R := by
  ext z
  simp only [mem_smul_set_iff_inv_smul_mem, mem_closedBall]
  constructor
  · intro hz
    have := dist_sl_smul (lift h) (h⁻¹ • z) w
    rw [← smul_eq_lift, ← smul_eq_lift, smul_inv_smul] at this
    rwa [this]
  · intro hz
    have := dist_sl_smul (lift h) (h⁻¹ • z) w
    rw [← smul_eq_lift, ← smul_eq_lift, smul_inv_smul] at this
    rwa [← this]

theorem inter_eq_empty {w w' : ℍ} {R : ℝ} (h : 2 * R < dist w w') :
    closedBall w R ∩ closedBall w' R = ∅ := by
  ext z
  simp only [mem_inter_iff, mem_closedBall, mem_empty_iff_false, iff_false, not_and, not_le]
  intro h1
  by_contra h2
  push Not at h2
  have := dist_triangle w z w'
  rw [dist_comm w z] at this
  linarith


open GaloisForLFunctions.RHTower.SarnakXueCounting

/-- The counting bound of `SarnakXueCounting.card_le`. -/
def cnt (p : ℕ) (y X C ε : ℝ) : ℝ :=
  (2 * y * Real.sqrt X / p + 1) + (4 * Real.sqrt X / p + 1) +
    (4 * Real.sqrt X / (p : ℝ) ^ 2 + 1) * (4 * Real.sqrt X / p + 1) * (2 * C * (9 * X) ^ ε)

section count
variable [hp : Fact p.Prime] (hp2 : p ≠ 2) {w : ℍ} (hx : |w.re| ≤ 1 / 2) (hy : 1 / 2 ≤ w.im)
  {X ε C : ℝ} (hX : 1 ≤ X) (hε : 0 < ε) (hC0 : 0 ≤ C)
  (hC : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε)
include hp2 hx hy hX hε hC0 hC

theorem card_near_le (T : Finset (gammaBar p))
    (hT : ∀ h ∈ T, 2 * Real.cosh (dist w (h • w)) ≤ X) :
    (T.card : ℝ) ≤ cnt p w.im X C ε := by
  rw [← Finset.card_image_of_injective T lift_injective]
  apply card_le hp2 hx hy hX hε hC0 hC
  intro γ hγ
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hγ
  refine ⟨lift_mem h, ?_⟩
  rw [← two_cosh_dist_eq_qform, ← smul_eq_lift]
  exact hT h hh

theorem near_finite : {h : gammaBar p | 2 * Real.cosh (dist w (h • w)) ≤ X}.Finite := by
  by_contra hinf
  obtain ⟨T, hTs, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈cnt p w.im X C ε⌉₊ + 1)
  have := card_near_le hp2 hx hy hX hε hC0 hC T (fun h hh => hTs hh)
  rw [hTc] at this
  push_cast at this
  linarith [Nat.le_ceil (cnt p w.im X C ε)]

end count

end

section dyadic
open Finset
/-- `1/√t ≤ Σ_{k<K, t < 2^{k+1}} 2^{-k/2}` for `1 ≤ t < 2^K`. -/
theorem inv_sqrt_le_sum {t : ℝ} {K : ℕ} (h1 : 1 ≤ t) (hK : t < 2 ^ K) :
    1 / Real.sqrt t ≤ ∑ k ∈ range K, if t < 2 ^ (k + 1) then 1 / Real.sqrt (2 ^ k) else 0 := by
  have hex : ∃ k, t < 2 ^ (k + 1) := ⟨K, by
    calc t < 2 ^ K := hK
      _ ≤ 2 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ K)⟩
  classical
  set k₀ := Nat.find hex
  have hk₀ : t < 2 ^ (k₀ + 1) := Nat.find_spec hex
  have hlow : (2 : ℝ) ^ k₀ ≤ t := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
    · rw [h0, pow_zero]; exact h1
    · have := Nat.find_min hex (show k₀ - 1 < k₀ by omega)
      push Not at this
      rwa [Nat.sub_add_cancel hpos] at this
  have hk₀K : k₀ < K := by
    by_contra hc
    push Not at hc
    have : (2 : ℝ) ^ K ≤ 2 ^ k₀ := pow_le_pow_right₀ (by norm_num) hc
    linarith
  have hterm : 1 / Real.sqrt t ≤ 1 / Real.sqrt (2 ^ k₀) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt hlow)
  calc 1 / Real.sqrt t ≤ (if t < 2 ^ (k₀ + 1) then 1 / Real.sqrt (2 ^ k₀) else 0) := by
        rw [if_pos hk₀]; exact hterm
    _ ≤ _ := single_le_sum (f := fun k => if t < 2 ^ (k + 1) then 1 / Real.sqrt (2 ^ k) else 0)
        (fun k _ => by split_ifs <;> positivity) (mem_range.mpr hk₀K)

/-- `1/cosh(d/2) ≤ √2 / √(cosh d)`. -/
theorem inv_cosh_half_le (d : ℝ) : 1 / Real.cosh (d / 2) ≤ Real.sqrt 2 / Real.sqrt (Real.cosh d) := by
  have hc : 0 < Real.cosh d := Real.cosh_pos d
  have hc2 : 0 < Real.cosh (d / 2) := Real.cosh_pos _
  have hsq : Real.cosh d = 2 * Real.cosh (d / 2) ^ 2 - 1 := by
    have := Real.cosh_two_mul (d / 2)
    rw [show 2 * (d / 2) = d by ring, Real.sinh_sq] at this
    linarith
  have h1 : Real.cosh d ≤ 2 * Real.cosh (d / 2) ^ 2 := by linarith
  rw [div_le_div_iff₀ hc2 (Real.sqrt_pos.mpr hc), one_mul]
  have : Real.sqrt (Real.cosh d) ≤ Real.sqrt 2 * Real.cosh (d / 2) := by
    rw [← Real.sqrt_sq hc2.le, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt h1
  linarith

/-- A single-shape upper bound for the counting function. -/
theorem cnt_le {P y Y C ε : ℝ} (hP : 1 ≤ P) (hy : 0 ≤ y) (hY : 1 ≤ Y) (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    (2 * y * Real.sqrt Y / P + 1) + (4 * Real.sqrt Y / P + 1) +
        (4 * Real.sqrt Y / P ^ 2 + 1) * (4 * Real.sqrt Y / P + 1) * (2 * C * (9 * Y) ^ ε) ≤
      32 * (1 + C * 9 ^ ε) * Y ^ ε * (1 + (y + 1) * Real.sqrt Y / P + Y / P ^ 3) := by
  have hP0 : 0 < P := by linarith
  set s := Real.sqrt Y
  have hs1 : 1 ≤ s := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hY
  have hss : s * s = Y := Real.mul_self_sqrt (by linarith)
  have hYe : 1 ≤ Y ^ ε := Real.one_le_rpow hY hε
  have h9 : (9 * Y) ^ ε = 9 ^ ε * Y ^ ε := Real.mul_rpow (by norm_num) (by linarith)
  have h9e : 1 ≤ (9 : ℝ) ^ ε := Real.one_le_rpow (by norm_num) hε
  set E := Y ^ ε
  set G := C * 9 ^ ε
  have hG : 0 ≤ G := by positivity
  rw [h9]
  -- expand the product term
  have hprod : (4 * s / P ^ 2 + 1) * (4 * s / P + 1) ≤ 16 * Y / P ^ 3 + 8 * s / P + 1 := by
    have h1 : 4 * s / P ^ 2 ≤ 4 * s / P := by
      apply div_le_div_of_nonneg_left (by positivity) hP0
      nlinarith
    have : (4 * s / P ^ 2 + 1) * (4 * s / P + 1) = 16 * (s * s) / P ^ 3 + 4 * s / P ^ 2 + 4 * s / P + 1 := by
      field_simp; ring
    rw [this, hss]
    have e : 8 * s / P = 4 * s / P + 4 * s / P := by ring
    linarith
  have hA : (2 * C * (9 ^ ε * E)) = 2 * G * E := by simp only [G]; ring
  rw [mul_assoc (4 * s / P ^ 2 + 1), hA]
  have hpos : 0 ≤ 2 * G * E := by positivity
  have key : (4 * s / P ^ 2 + 1) * ((4 * s / P + 1) * (2 * G * E)) ≤
      (16 * Y / P ^ 3 + 8 * s / P + 1) * (2 * G * E) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hprod hpos
  have hsP : 0 ≤ s / P := by positivity
  have hYP : 0 ≤ Y / P ^ 3 := by positivity
  have hE1 : 1 ≤ E := hYe
  -- compare term by term
  have t1 : 2 * y * s / P + 1 + (4 * s / P + 1) ≤ 32 * E * (1 + (y + 1) * s / P) := by
    have : 2 * y * s / P + 1 + (4 * s / P + 1) = 2 + (2 * y + 4) * (s / P) := by ring
    rw [this, show (y + 1) * s / P = (y + 1) * (s / P) by ring]
    nlinarith [mul_le_mul_of_nonneg_right hE1 hsP, mul_nonneg hy hsP]
  have t2 : (16 * Y / P ^ 3 + 8 * s / P + 1) * (2 * G * E) ≤
      32 * G * E * (1 + (y + 1) * s / P + Y / P ^ 3) := by
    rw [show 16 * Y / P ^ 3 = 16 * (Y / P ^ 3) by ring, show 8 * s / P = 8 * (s / P) by ring,
      show (y + 1) * s / P = (y + 1) * (s / P) by ring]
    have hGE : 0 ≤ G * E := by positivity
    nlinarith [mul_nonneg hGE hsP, mul_nonneg hGE hYP, mul_nonneg (mul_nonneg hGE hy) hsP]
  calc _ ≤ 32 * E * (1 + (y + 1) * s / P) + 32 * G * E * (1 + (y + 1) * s / P + Y / P ^ 3) := by
        linarith
    _ ≤ 32 * (1 + G) * E * (1 + (y + 1) * s / P + Y / P ^ 3) := by
        have : 0 ≤ 32 * E * (Y / P ^ 3) := by positivity
        nlinarith

theorem sqrt_two_pow (k : ℕ) : Real.sqrt (2 ^ k) = Real.sqrt 2 ^ k := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
    Real.mul_self_sqrt (by norm_num)]

theorem geom_inv_sqrt_le (K : ℕ) : ∑ k ∈ range K, 1 / Real.sqrt (2 ^ k) ≤ 4 := by
  have hs : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (4 / 3 : ℝ) = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  set r := 1 / Real.sqrt 2
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 3 / 4 := by
    simp only [r]; rw [div_le_iff₀ (by positivity)]; linarith
  have hterm : ∀ k, 1 / Real.sqrt (2 ^ k) = r ^ k := by
    intro k; rw [sqrt_two_pow, one_div_pow]
  simp_rw [hterm]
  rw [geom_sum_eq (by linarith)]
  have h1 : 0 < 1 - r := by linarith
  rw [div_le_iff_of_neg (by linarith : r - 1 < 0)]
  nlinarith [pow_nonneg hr0 K]

/-- **Dyadic summation of the counting bound.** -/
theorem dyadic_sum_le {P y A ε : ℝ} (hP : 1 ≤ P) (hy : 0 ≤ y) (hA : 0 ≤ A) (hε : 0 ≤ ε) (K : ℕ) :
    ∑ k ∈ range K, 1 / Real.sqrt (2 ^ k) *
        (A * ((2 : ℝ) ^ (k + 2)) ^ ε *
          (1 + (y + 1) * Real.sqrt (2 ^ (k + 2)) / P + 2 ^ (k + 2) / P ^ 3)) ≤
      A * ((2 : ℝ) ^ (K + 2)) ^ ε * (4 + 2 * K * (y + 1) / P + 4 * K * Real.sqrt (2 ^ K) / P ^ 3) := by
  have hP0 : 0 < P := by linarith
  set E := ((2 : ℝ) ^ (K + 2)) ^ ε
  have hterm : ∀ k ∈ range K, 1 / Real.sqrt (2 ^ k) *
      (A * ((2 : ℝ) ^ (k + 2)) ^ ε * (1 + (y + 1) * Real.sqrt (2 ^ (k + 2)) / P + 2 ^ (k + 2) / P ^ 3)) ≤
      A * E * (1 / Real.sqrt (2 ^ k) + 2 * (y + 1) / P + 4 * Real.sqrt (2 ^ K) / P ^ 3) := by
    intro k hk
    have hkK : k ≤ K := (mem_range.mp hk).le
    have hs : 0 < Real.sqrt ((2 : ℝ) ^ k) := Real.sqrt_pos.mpr (by positivity)
    have hsk : Real.sqrt ((2 : ℝ) ^ (k + 2)) = 2 * Real.sqrt (2 ^ k) := by
      rw [pow_add, Real.sqrt_mul (by positivity), show ((2 : ℝ) ^ 2) = 2 ^ 2 from rfl,
        Real.sqrt_sq (by norm_num), mul_comm]
    have hss : Real.sqrt ((2 : ℝ) ^ k) * Real.sqrt (2 ^ k) = 2 ^ k := Real.mul_self_sqrt (by positivity)
    have hE : ((2 : ℝ) ^ (k + 2)) ^ ε ≤ E :=
      Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)) hε
    have hsK : Real.sqrt ((2 : ℝ) ^ k) ≤ Real.sqrt (2 ^ K) :=
      Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) hkK)
    have hinner : 1 / Real.sqrt (2 ^ k) * (1 + (y + 1) * Real.sqrt (2 ^ (k + 2)) / P + 2 ^ (k + 2) / P ^ 3) =
        1 / Real.sqrt (2 ^ k) + 2 * (y + 1) / P + 4 * Real.sqrt (2 ^ k) / P ^ 3 := by
      have h2 : (2 : ℝ) ^ (k + 2) = Real.sqrt (2 ^ k) * Real.sqrt (2 ^ k) * 4 := by
        rw [hss]; ring
      rw [hsk, h2]
      field_simp
    have hi2 : 1 / Real.sqrt (2 ^ k) + 2 * (y + 1) / P + 4 * Real.sqrt (2 ^ k) / P ^ 3 ≤
        1 / Real.sqrt (2 ^ k) + 2 * (y + 1) / P + 4 * Real.sqrt (2 ^ K) / P ^ 3 := by
      gcongr
    have hpos : 0 ≤ 1 / Real.sqrt (2 ^ k) + 2 * (y + 1) / P + 4 * Real.sqrt (2 ^ k) / P ^ 3 := by
      positivity
    calc 1 / Real.sqrt (2 ^ k) * (A * ((2 : ℝ) ^ (k + 2)) ^ ε *
          (1 + (y + 1) * Real.sqrt (2 ^ (k + 2)) / P + 2 ^ (k + 2) / P ^ 3))
        = A * ((2 : ℝ) ^ (k + 2)) ^ ε * (1 / Real.sqrt (2 ^ k) *
          (1 + (y + 1) * Real.sqrt (2 ^ (k + 2)) / P + 2 ^ (k + 2) / P ^ 3)) := by ring
      _ = A * ((2 : ℝ) ^ (k + 2)) ^ ε *
          (1 / Real.sqrt (2 ^ k) + 2 * (y + 1) / P + 4 * Real.sqrt (2 ^ k) / P ^ 3) := by rw [hinner]
      _ ≤ A * E * (1 / Real.sqrt (2 ^ k) + 2 * (y + 1) / P + 4 * Real.sqrt (2 ^ K) / P ^ 3) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hE hA) hi2 hpos (by positivity)
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_const, sum_const, card_range, nsmul_eq_mul,
    nsmul_eq_mul]
  have hg := geom_inv_sqrt_le K
  have hAE : 0 ≤ A * E := by positivity
  apply mul_le_mul_of_nonneg_left _ hAE
  have : (K : ℝ) * (2 * (y + 1) / P) = 2 * K * (y + 1) / P := by ring
  have : (K : ℝ) * (4 * Real.sqrt (2 ^ K) / P ^ 3) = 4 * K * Real.sqrt (2 ^ K) / P ^ 3 := by ring
  linarith

end dyadic

section kernel
open Finset GaloisForLFunctions.RHTower.HyperbolicLens

variable [hp : Fact p.Prime] (hp2 : p ≠ 2) {w : ℍ} (hx : |w.re| ≤ 1 / 2) (hy : 1 / 2 ≤ w.im)
  {ε C : ℝ} (hε : 0 < ε) (hC0 : 0 ≤ C)
  (hC : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε)
include hp2 hx hy hε hC0 hC

/-- **Kernel sum bound.** For `R ≥ 0` and `cosh 2R < 2^K`,
`Σ_{h ∈ Γ̄(p)} μ(B_R(w) ∩ h B_R(w)) ≤ 16√2 cosh R · A (2^{K+2})^ε (4 + 2K(y+1)/p + 4K√(2^K)/p³)` with
`A = 32(1 + C 9^ε)`. -/
theorem kernel_sum_le {R : ℝ} (hR : 0 ≤ R) (K : ℕ) (hK : Real.cosh (2 * R) < 2 ^ K) :
    (∑' h : gammaBar p, volume (closedBall w R ∩ h • closedBall w R)) ≤
      ENNReal.ofReal (16 * Real.cosh R * Real.sqrt 2 *
        (32 * (1 + C * 9 ^ ε) * ((2 : ℝ) ^ (K + 2)) ^ ε *
          (4 + 2 * K * (w.im + 1) / p + 4 * K * Real.sqrt (2 ^ K) / (p : ℝ) ^ 3))) := by
  have hX1 : (1 : ℝ) ≤ 2 * Real.cosh (2 * R) := by linarith [Real.one_le_cosh (2 * R)]
  have hfin := near_finite hp2 hx hy hX1 hε hC0 hC
  set S := hfin.toFinset
  set d : gammaBar p → ℝ := fun h => dist w (h • w)
  have hmemS : ∀ h, h ∈ S ↔ 2 * Real.cosh (d h) ≤ 2 * Real.cosh (2 * R) := by
    intro h; simp [S, d]
  -- terms outside `S` vanish
  have hzero : ∀ h ∉ S, volume (closedBall w R ∩ h • closedBall w R) = 0 := by
    intro h hh
    rw [hmemS] at hh
    push Not at hh
    have hlt : Real.cosh (2 * R) < Real.cosh (d h) := by linarith
    rw [Real.cosh_lt_cosh, abs_of_nonneg (by positivity), abs_of_nonneg dist_nonneg] at hlt
    rw [smul_closedBall', inter_eq_empty hlt, measure_empty]
  rw [tsum_eq_sum (s := S) (fun h hh => hzero h hh)]
  -- each term by the lens bound
  have hterm : ∀ h ∈ S, volume (closedBall w R ∩ h • closedBall w R) ≤
      ENNReal.ofReal (16 * Real.cosh R / Real.cosh (d h / 2)) := by
    intro h _
    rw [smul_closedBall']
    exact volume_lens_le w (h • w) R
  refine (sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun h _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- real estimate
  set A := 32 * (1 + C * 9 ^ ε)
  have hA : 0 ≤ A := by positivity
  have hK' : ∀ h ∈ S, Real.cosh (d h) < 2 ^ K := by
    intro h hh
    rw [hmemS] at hh
    linarith
  have hstep1 : ∀ h ∈ S, 16 * Real.cosh R / Real.cosh (d h / 2) ≤
      16 * Real.cosh R * Real.sqrt 2 *
        ∑ k ∈ range K, if Real.cosh (d h) < 2 ^ (k + 1) then 1 / Real.sqrt (2 ^ k) else 0 := by
    intro h hh
    have h1 := inv_cosh_half_le (d h)
    have h2 := inv_sqrt_le_sum (Real.one_le_cosh (d h)) (hK' h hh)
    have hc : 0 ≤ 16 * Real.cosh R := by positivity
    calc 16 * Real.cosh R / Real.cosh (d h / 2) = 16 * Real.cosh R * (1 / Real.cosh (d h / 2)) := by ring
      _ ≤ 16 * Real.cosh R * (Real.sqrt 2 / Real.sqrt (Real.cosh (d h))) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ = 16 * Real.cosh R * Real.sqrt 2 * (1 / Real.sqrt (Real.cosh (d h))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  refine (sum_le_sum hstep1).trans ?_
  rw [← mul_sum, sum_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- swap and count
  have hcount : ∀ k ∈ range K, ∑ h ∈ S, (if Real.cosh (d h) < 2 ^ (k + 1) then 1 / Real.sqrt (2 ^ k) else 0) ≤
      1 / Real.sqrt (2 ^ k) * (A * ((2 : ℝ) ^ (k + 2)) ^ ε *
        (1 + (w.im + 1) * Real.sqrt (2 ^ (k + 2)) / p + 2 ^ (k + 2) / (p : ℝ) ^ 3)) := by
    intro k _
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hY1 : (1 : ℝ) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
    have hc := card_near_le hp2 hx hy hY1 hε hC0 hC (S.filter (fun h => Real.cosh (d h) < 2 ^ (k + 1)))
      (fun h hh => by
        have := (mem_filter.mp hh).2
        simp only [d] at this
        have e1 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
        have e2 : (2 : ℝ) ^ (k + 2) = 4 * 2 ^ k := by ring
        rw [e1] at this; rw [e2]; linarith)
    refine hc.trans ?_
    have hP : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
    exact cnt_le hP (by linarith) hY1 hC0 hε.le
  refine (sum_le_sum hcount).trans ?_
  exact dyadic_sum_le (by exact_mod_cast hp.out.one_lt.le) (by linarith) hA hε.le K

end kernel

end GaloisForLFunctions.RHTower.SarnakXueKernel
