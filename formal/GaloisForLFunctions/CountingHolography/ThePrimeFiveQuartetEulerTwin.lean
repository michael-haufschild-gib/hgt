import GaloisForLFunctions.CountingHolography.TheCountLawAtEveryGenus
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRestrictionToTheFrobeniusGraph
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Universal Witt–Euler Coordinates and the Prime-Five Non-Real Quartet Beurling Curve Twin

This module establishes two results connecting formal integral zeta series, effective elements of
the big Witt ghost ring, and the base-change count tower at genus two:

1. **Universal Witt–Euler coordinates for integral power series**
   (`exists_int_necklace_of_integral_hasGhost`):
   Every formal power series `Zℤ ∈ 1 + X ℤ⟦X⟧` whose logarithmic derivative satisfies
   `X Z'(X) = Z(X) ∑_{k ≥ 1} N_k X^k` automatically has ghost sequence `N ∈ ghostRing` (`IsGhost`),
   uniquely decomposing `N_k = ∑_{d ∣ k} d π_d` with `π_d ∈ ℤ` and `k π_k = ∑_{d ∣ k} μ(k/d) N_d`
   without requiring a subshift or transfer-matrix realization.

2. **Prime-base (`q = 5`) genus-`2` non-real single-quartet effective Beurling curve twin**
   (`primeFiveQuartetDatum`, `primeFiveQuartet_complete_twin`):
   The reciprocal polynomial `P_4(X) = 1 - 2X + 12X² - 10X³ + 25X⁴ = (1 - (1+i)X + 5X²)(1 - (1-i)X + 5X²)`
   over the prime base `q = 5` defines a genus-`2` `CurveDatum (Fin 4)` with:
   - Exact functional equation `β_{fe(i)} β_i = 1`, conjugation symmetry, and integral rational zeta
     series in `1 + X ℤ⟦X⟧` with `P_4(1) = 26`;
   - A lone non-real off-circle Frobenius quartet (`Im β_i ≠ 0` for all `i`, `√5 < ‖α_0‖ < 3 < 5`),
     so every degree-`1` kernel count `detDeg P` (`P ∈ ℝ[X]`) is nonnegative;
   - **Strictly positive integer closed-prime-orbit counts `π_d ≥ 1` at every degree `d ≥ 1`**
     (`IsEffective` in `ghostRing`, giving an effective Beurling Euler product
     `∏_{d ≥ 1} (1 - X^d)^{-π_d}` with `π_1 = 4, π_2 = 21, π_3 = 52`);
   - **Genus-`2` Weil count laws at levels `n = 1, 2, 3`** (attaining exact boundary tangency
     `a_2² = (-20)² = 400 = 16 · 5²` at `n = 2`), while failing the full tower count law.
-/

noncomputable section
set_option autoImplicit false

open Finset PowerSeries Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography ArithmeticCastelnuovoSeveri AbsoluteGeometryOfSpecZ

/-! ## 1. Universal Witt–Euler coordinates of integral formal power series -/

/-- Truncated Euler factor `(1 - X^j)^e` in `ℤ⟦X⟧` (`e ∈ ℤ`, `j ≥ 1`). -/
private def eulerFactorInt (j : ℕ) (e : ℤ) : PowerSeries ℤ :=
  if 0 ≤ e then (1 - PowerSeries.X ^ j) ^ e.toNat
  else (PowerSeries.mk fun n => if j ∣ n then 1 else 0) ^ (-e).toNat

private theorem coeff_pow_step {A : PowerSeries ℤ} {j : ℕ} (hj : 1 ≤ j) {s : ℤ}
    (h0 : PowerSeries.coeff 0 A = 1)
    (hmid : ∀ m : ℕ, 1 ≤ m → m < j → PowerSeries.coeff m A = 0)
    (hj_eq : PowerSeries.coeff j A = s) (r : ℕ) :
    PowerSeries.coeff 0 (A ^ r) = 1 ∧
      (∀ m : ℕ, 1 ≤ m → m < j → PowerSeries.coeff m (A ^ r) = 0) ∧
      PowerSeries.coeff j (A ^ r) = (r : ℤ) * s := by
  induction r with
  | zero =>
    refine ⟨by simp, fun m hm _ => ?_, by simp⟩
    have hm0 : m ≠ 0 := by omega
    simp [PowerSeries.coeff_one, hm0]
  | succ r ih =>
    obtain ⟨ih0, ihmid, ihj⟩ := ih
    rw [pow_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff,
        ih0, h0, mul_one]
    · intro m hm1 hmj
      rw [PowerSeries.coeff_mul]
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp_eq := Finset.mem_antidiagonal.mp hp
      rcases eq_or_ne p.1 0 with hp1 | hp1
      · have hp2_ge : 1 ≤ p.2 := by omega
        have hp2_lt : p.2 < j := by omega
        rw [hmid p.2 hp2_ge hp2_lt, mul_zero]
      · have hp1_ge : 1 ≤ p.1 := by omega
        have hp1_lt : p.1 < j := by omega
        rw [ihmid p.1 hp1_ge hp1_lt, zero_mul]
    · rw [PowerSeries.coeff_mul]
      have hsub : ∀ p ∈ Finset.antidiagonal j, p ≠ (0, j) → p ≠ (j, 0) →
          PowerSeries.coeff p.1 (A ^ r) * PowerSeries.coeff p.2 A = 0 := by
        intro p hp hne1 hne2
        have hp_eq := Finset.mem_antidiagonal.mp hp
        have hp1_pos : 1 ≤ p.1 := by
          rcases eq_or_ne p.1 0 with h0' | hpos
          · exfalso; apply hne1; ext <;> simp [h0'] <;> omega
          · omega
        have hp1_lt : p.1 < j := by
          rcases eq_or_ne p.2 0 with h0' | hpos
          · exfalso; apply hne2; ext <;> simp [h0'] <;> omega
          · omega
        rw [ihmid p.1 hp1_pos hp1_lt, zero_mul]
      have h0j : (0, j) ∈ Finset.antidiagonal j := by simp
      have hj0 : (j, 0) ∈ (Finset.antidiagonal j).erase (0, j) := by
        simp only [Finset.mem_erase, Finset.mem_antidiagonal]
        refine ⟨fun h => ?_, Nat.add_zero j⟩
        have := Prod.mk.inj h; omega
      rw [← Finset.add_sum_erase _ _ h0j, ← Finset.add_sum_erase _ _ hj0]
      have hrest : ∑ x ∈ ((Finset.antidiagonal j).erase (0, j)).erase (j, 0),
          PowerSeries.coeff x.1 (A ^ r) * PowerSeries.coeff x.2 A = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx1 := Finset.mem_erase.mp hx
        have hx2 := Finset.mem_erase.mp hx1.2
        exact hsub x hx2.2 hx2.1 hx1.1
      rw [hrest, add_zero, ih0, hj_eq, ihj, h0]
      push_cast; ring

private theorem coeff_eulerFactorInt {j : ℕ} (hj : 1 ≤ j) (e : ℤ) :
    PowerSeries.coeff 0 (eulerFactorInt j e) = 1 ∧
      (∀ m : ℕ, 1 ≤ m → m < j → PowerSeries.coeff m (eulerFactorInt j e) = 0) ∧
      PowerSeries.coeff j (eulerFactorInt j e) = -e := by
  unfold eulerFactorInt
  split_ifs with he
  · have hbase0 : PowerSeries.coeff 0 (1 - (PowerSeries.X : PowerSeries ℤ) ^ j) = 1 := by
      rw [map_sub, PowerSeries.coeff_one, if_pos rfl, PowerSeries.coeff_X_pow, if_neg (by omega),
        sub_zero]
    have hbasemid : ∀ m : ℕ, 1 ≤ m → m < j →
        PowerSeries.coeff m (1 - (PowerSeries.X : PowerSeries ℤ) ^ j) = 0 := by
      intro m hm1 hmj
      rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_X_pow,
        if_neg (by omega), sub_zero]
    have hbasej : PowerSeries.coeff j (1 - (PowerSeries.X : PowerSeries ℤ) ^ j) = -1 := by
      rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_X_pow, if_pos rfl,
        zero_sub]
    obtain ⟨c0, cmid, cj⟩ := coeff_pow_step hj hbase0 hbasemid hbasej e.toNat
    refine ⟨c0, cmid, ?_⟩
    rw [cj, Int.toNat_of_nonneg he]; ring
  · have he_neg : 0 ≤ -e := by omega
    set B : PowerSeries ℤ := PowerSeries.mk fun n => if j ∣ n then 1 else 0
    have hbase0 : PowerSeries.coeff 0 B = 1 := by simp [B]
    have hbasemid : ∀ m : ℕ, 1 ≤ m → m < j → PowerSeries.coeff m B = 0 := by
      intro m hm1 hmj
      simp only [B, PowerSeries.coeff_mk, ite_eq_right_iff]
      intro hdvd
      exact absurd (Nat.le_of_dvd hm1 hdvd) (by omega)
    have hbasej : PowerSeries.coeff j B = 1 := by simp [B]
    obtain ⟨c0, cmid, cj⟩ := coeff_pow_step hj hbase0 hbasemid hbasej (-e).toNat
    refine ⟨c0, cmid, ?_⟩
    rw [cj, Int.toNat_of_nonneg he_neg]; ring

private theorem hasGhost_one_sub_X_pow {j : ℕ} (hj : 1 ≤ j) :
    HasGhost (1 - (PowerSeries.X : ℂ⟦X⟧) ^ j)
      (PowerSeries.mk fun n => if n = 0 then 0 else if j ∣ n then -(j : ℂ) else 0) := by
  unfold HasGhost
  set G : ℂ⟦X⟧ := PowerSeries.mk fun n => if j ∣ n then 1 else 0
  have hinv : (1 - (PowerSeries.X : ℂ⟦X⟧) ^ j) * G = 1 := by
    ext n
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
    simp only [G, PowerSeries.coeff_mk]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [show ¬ j ≤ 0 by omega]
    · rw [if_neg hn0]
      by_cases hjn : j ∣ n
      · obtain ⟨q, rfl⟩ := hjn
        have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn0
        have hjle : j ≤ j * q := Nat.le_mul_of_pos_right j hq1
        have hdvd_sub : j ∣ j * q - j := by
          rw [show j * q - j = j * (q - 1) by zify [hjle, hq1]; ring]
          exact dvd_mul_right j _
        simp [hjle, dvd_mul_right j q, hdvd_sub]
      · rw [if_neg hjn, zero_sub, neg_eq_zero]
        split_ifs with hjle
        · rw [if_neg]
          intro hdvd
          exact hjn (by rw [← Nat.sub_add_cancel hjle]; exact dvd_add hdvd dvd_rfl)
        · rfl
  -- Compute `X * d/dX (1 - X^j) = -j X^j`.
  have hderiv : PowerSeries.X * d⁄dX ℂ (1 - (PowerSeries.X : ℂ⟦X⟧) ^ j) =
      -PowerSeries.C (j : ℂ) * PowerSeries.X ^ j := by
    ext n
    rw [PowerSeries.coeff_X_mul_derivative, map_sub, PowerSeries.coeff_one,
      PowerSeries.coeff_X_pow, neg_mul, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [show 0 ≠ j by omega]
    · rw [if_neg hn0, zero_sub]
      split_ifs with hnj
      · subst hnj; ring
      · ring
  have htail : -PowerSeries.C (j : ℂ) * PowerSeries.X ^ j * G =
      PowerSeries.mk fun n => if n = 0 then 0 else if j ∣ n then -(j : ℂ) else 0 := by
    ext n
    rw [neg_mul, mul_assoc, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_mk]
    simp only [G, PowerSeries.coeff_mk]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [show ¬ j ≤ 0 by omega]
    · rw [if_neg hn0]
      by_cases hjn : j ∣ n
      · obtain ⟨q, rfl⟩ := hjn
        have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn0
        have hjle : j ≤ j * q := Nat.le_mul_of_pos_right j hq1
        have hdvd_sub : j ∣ j * q - j := by
          rw [show j * q - j = j * (q - 1) by zify [hjle, hq1]; ring]
          exact dvd_mul_right j _
        simp [hjle, dvd_mul_right j q, hdvd_sub]
      · rw [if_neg hjn]
        split_ifs with hjle
        · rw [if_neg]
          · ring
          · intro hdvd
            exact hjn (by rw [← Nat.sub_add_cancel hjle]; exact dvd_add hdvd dvd_rfl)
        · ring
  rw [hderiv, ← htail]
  linear_combination (-PowerSeries.C (j : ℂ) * PowerSeries.X ^ j * G) * hinv

private theorem hasGhost_geom_pow {j : ℕ} (hj : 1 ≤ j) :
    HasGhost (PowerSeries.mk fun n => if j ∣ n then (1 : ℂ) else 0)
      (PowerSeries.mk fun n => if n = 0 then 0 else if j ∣ n then (j : ℂ) else 0) := by
  set F : ℂ⟦X⟧ := 1 - (PowerSeries.X : ℂ⟦X⟧) ^ j
  set G : ℂ⟦X⟧ := PowerSeries.mk fun n => if j ∣ n then (1 : ℂ) else 0
  set H : ℂ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else if j ∣ n then (j : ℂ) else 0
  have hneg : (PowerSeries.mk fun n => if n = 0 then 0 else if j ∣ n then -(j : ℂ) else 0) = -H := by
    ext n; simp [H]; split_ifs <;> ring
  have hF : HasGhost F (-H) := by rw [← hneg]; exact hasGhost_one_sub_X_pow hj
  have hinv : F * G = 1 := by
    ext n
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
    simp only [G, PowerSeries.coeff_mk]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [show ¬ j ≤ 0 by omega]
    · rw [if_neg hn0]
      by_cases hjn : j ∣ n
      · obtain ⟨q, rfl⟩ := hjn
        have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn0
        have hjle : j ≤ j * q := Nat.le_mul_of_pos_right j hq1
        have hdvd_sub : j ∣ j * q - j := by
          rw [show j * q - j = j * (q - 1) by zify [hjle, hq1]; ring]
          exact dvd_mul_right j _
        simp [hjle, dvd_mul_right j q, hdvd_sub]
      · rw [if_neg hjn, zero_sub, neg_eq_zero]
        split_ifs with hjle
        · rw [if_neg]
          intro hdvd
          exact hjn (by rw [← Nat.sub_add_cancel hjle]; exact dvd_add hdvd dvd_rfl)
        · rfl
  unfold HasGhost at hF ⊢
  have hd : d⁄dX ℂ (F * G) = 0 := by rw [hinv, Derivation.map_one_eq_zero]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hd
  linear_combination (G * PowerSeries.X) * hd - G ^ 2 * hF -
    (PowerSeries.X * d⁄dX ℂ G - G * H) * hinv

private theorem hasGhost_pow_nat {A B : ℂ⟦X⟧} (h : HasGhost A B) (r : ℕ) :
    HasGhost (A ^ r) ((r : ℂ) • B) := by
  induction r with
  | zero => simpa using hasGhost_one
  | succ r ih =>
    rw [pow_succ, Nat.cast_succ, add_smul, one_smul]
    exact hasGhost_mul ih h

private theorem hasGhost_eulerFactorInt {j : ℕ} (hj : 1 ≤ j) (e : ℤ) :
    HasGhost (PowerSeries.map (Int.castRingHom ℂ) (eulerFactorInt j e))
      (PowerSeries.mk fun n => if n = 0 then 0 else if j ∣ n then -(((j : ℤ) * e : ℤ) : ℂ) else 0) := by
  unfold eulerFactorInt
  split_ifs with he
  · rw [map_pow, map_sub, map_one, map_pow, PowerSeries.map_X]
    have hp := hasGhost_pow_nat (hasGhost_one_sub_X_pow hj) e.toNat
    convert hp using 1
    ext n
    simp only [PowerSeries.coeff_mk, map_smul, smul_eq_mul]
    split_ifs with hn0 hjn
    · simp
    · rw [Int.toNat_of_nonneg he]; push_cast; ring
    · simp
  · have he_neg : 0 ≤ -e := by omega
    rw [map_pow]
    have hmap : PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.mk fun n => if j ∣ n then (1 : ℤ) else 0) =
        PowerSeries.mk fun n => if j ∣ n then (1 : ℂ) else 0 := by
      ext n; simp; split_ifs <;> simp
    rw [hmap]
    have hp := hasGhost_pow_nat (hasGhost_geom_pow hj) (-e).toNat
    convert hp using 1
    ext n
    simp only [PowerSeries.coeff_mk, map_smul, smul_eq_mul]
    split_ifs with hn0 hjn
    · simp
    · rw [Int.toNat_of_nonneg he_neg]; push_cast; ring
    · simp

/-- Recursive remainder and integer necklace coordinates extracted from `Zℤ ∈ 1 + X ℤ⟦X⟧`. -/
private def wittEulerStep (Zℤ : PowerSeries ℤ) : ℕ → PowerSeries ℤ × ℤ
  | 0 => (Zℤ, 0)
  | d + 1 =>
      let prev := (wittEulerStep Zℤ d).1
      let c := PowerSeries.coeff (d + 1) prev
      (prev * eulerFactorInt (d + 1) c, c)

/-- **Universal Witt–Euler coordinates of integral power series.**
If `Zℤ ∈ ℤ⟦X⟧` has constant term `1` and complex ghost series `∑_{k ≥ 1} N_k X^k` (`N : ℕ → ℤ`),
then `n ↦ N_n` lies in `ghostRing` (`IsGhost`), i.e., there exists `π : ℕ → ℤ` with
`N_k = ∑_{d ∣ k} d π_d` and `k π_k = ∑_{d ∣ k} μ(k/d) N_d` for every `k ≥ 1`. -/
theorem exists_int_necklace_of_integral_hasGhost (Zℤ : PowerSeries ℤ)
    (h0 : PowerSeries.constantCoeff Zℤ = 1) (N : ℕ → ℤ)
    (hghost : HasGhost (PowerSeries.map (Int.castRingHom ℂ) Zℤ)
      (PowerSeries.mk fun k => if k = 0 then 0 else (N k : ℂ))) :
    IsGhost (fun n : ℕ+ => N n) ∧
      ∃ π : ℕ → ℤ, π 0 = 0 ∧
        (∀ k : ℕ, 1 ≤ k → N k = ∑ d ∈ k.divisors, (d : ℤ) * π d) ∧
        (∀ k : ℕ, 1 ≤ k → (k : ℤ) * π k =
          ∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k / d) : ℤ) * N d) := by
  let R : ℕ → PowerSeries ℤ := fun d => (wittEulerStep Zℤ d).1
  let π : ℕ → ℤ := fun d => (wittEulerStep Zℤ d).2
  -- Prove by induction on `d` that `R d = 1 + O(X^{d+1})` and track its ghost series.
  have hR_inv : ∀ d : ℕ,
      PowerSeries.coeff 0 (R d) = 1 ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ d → PowerSeries.coeff m (R d) = 0) ∧
      HasGhost (PowerSeries.map (Int.castRingHom ℂ) (R d))
        (PowerSeries.mk fun k => if k = 0 then 0 else
          ((N k - ∑ j ∈ (Finset.Icc 1 d).filter (· ∣ k), (j : ℤ) * π j : ℤ) : ℂ)) := by
    intro d
    induction d with
    | zero =>
      refine ⟨by simpa [R, wittEulerStep] using h0, fun m hm1 hm0 => by omega, ?_⟩
      convert hghost using 1
      ext k
      simp only [PowerSeries.coeff_mk]
      split_ifs with hk0
      · rfl
      · have hemp : (Finset.Icc 1 0).filter (· ∣ k) = ∅ := by
          ext j; simp; omega
        rw [hemp, Finset.sum_empty, sub_zero]
    | succ d ih =>
      obtain ⟨ih0, ihz, ihg⟩ := ih
      have hR_succ : R (d + 1) = R d * eulerFactorInt (d + 1) (π (d + 1)) := rfl
      have hπ_succ : π (d + 1) = PowerSeries.coeff (d + 1) (R d) := rfl
      obtain ⟨ef0, efmid, efj⟩ := coeff_eulerFactorInt (Nat.succ_pos d) (π (d + 1))
      refine ⟨?_, ?_, ?_⟩
      · rw [hR_succ, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
          ← PowerSeries.coeff_zero_eq_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff,
          ih0, ef0, mul_one]
      · intro m hm1 hmd1
        rw [hR_succ, PowerSeries.coeff_mul]
        rcases lt_or_eq_of_le hmd1 with hlt | rfl
        · refine Finset.sum_eq_zero fun p hp => ?_
          have hp_eq := Finset.mem_antidiagonal.mp hp
          rcases eq_or_ne p.1 0 with hp1 | hp1
          · rw [efmid p.2 (by omega) (by omega), mul_zero]
          · rw [ihz p.1 (by omega) (by omega), zero_mul]
        · -- `m = d + 1`: only `(0, d+1)` and `(d+1, 0)` survive, cancelling `π (d+1) - π (d+1) = 0`!
          have h0m : (0, d + 1) ∈ Finset.antidiagonal (d + 1) := by simp
          have hm0 : (d + 1, 0) ∈ (Finset.antidiagonal (d + 1)).erase (0, d + 1) := by
            simp only [Finset.mem_erase, Finset.mem_antidiagonal]
            exact ⟨fun h => by have := Prod.mk.inj h; omega, Nat.add_zero _⟩
          rw [← Finset.add_sum_erase _ _ h0m, ← Finset.add_sum_erase _ _ hm0]
          have hrest : ∑ p ∈ ((Finset.antidiagonal (d + 1)).erase (0, d + 1)).erase (d + 1, 0),
              PowerSeries.coeff p.1 (R d) * PowerSeries.coeff p.2 (eulerFactorInt (d + 1) (π (d + 1))) = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            have hp1 := Finset.mem_erase.mp hp
            have hp2 := Finset.mem_erase.mp hp1.2
            have hp_sum := Finset.mem_antidiagonal.mp hp2.2
            have hp1_pos : 1 ≤ p.1 := by
              rcases eq_or_ne p.1 0 with h0' | _
              · exfalso; apply hp2.1; ext <;> simp [h0'] <;> omega
              · omega
            have hp1_le : p.1 ≤ d := by
              rcases eq_or_ne p.2 0 with h0' | _
              · exfalso; apply hp1.1; ext <;> simp [h0'] <;> omega
              · omega
            rw [ihz p.1 hp1_pos hp1_le, zero_mul]
          rw [hrest, add_zero, ih0, efj, ← hπ_succ, ef0]
          ring
      · rw [hR_succ, map_mul]
        have hg_mul := hasGhost_mul ihg (hasGhost_eulerFactorInt (Nat.succ_pos d) (π (d + 1)))
        convert hg_mul using 1
        ext k
        simp only [PowerSeries.coeff_mk, map_add]
        split_ifs with hk0
        · simp
        · have hIcc : Finset.Icc 1 (d + 1) = insert (d + 1) (Finset.Icc 1 d) := by
            ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.filter_insert]
          split_ifs with hdvd
          · rw [Finset.sum_insert (by simp; omega)]
            push_cast; ring
          · push_cast; ring
  have hN_eq : ∀ k : ℕ, 1 ≤ k → N k = ∑ d ∈ k.divisors, (d : ℤ) * π d := by
    intro k hk
    obtain ⟨hR0, hRz, hRg⟩ := hR_inv k
    unfold HasGhost at hRg
    have hc := congrArg (PowerSeries.coeff k) hRg
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
    rw [PowerSeries.coeff_X_mul_derivative, PowerSeries.coeff_map, hRz (m + 1) (by omega) le_rfl,
      Int.cast_zero, mul_zero, PowerSeries.coeff_mul] at hc
    have h0k : (0, m + 1) ∈ Finset.antidiagonal (m + 1) := by simp
    rw [← Finset.add_sum_erase _ _ h0k] at hc
    have hrest : ∑ p ∈ (Finset.antidiagonal (m + 1)).erase (0, m + 1),
        PowerSeries.coeff p.1 (PowerSeries.map (Int.castRingHom ℂ) (R (m + 1))) *
          PowerSeries.coeff p.2 _ = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp1 := Finset.mem_erase.mp hp
      have hp_sum := Finset.mem_antidiagonal.mp hp1.2
      have hp1_pos : 1 ≤ p.1 := by
        rcases eq_or_ne p.1 0 with h0' | _
        · exfalso; apply hp1.1; ext <;> simp [h0'] <;> omega
        · omega
      rw [PowerSeries.coeff_map, hRz p.1 hp1_pos (by omega), Int.cast_zero, zero_mul]
    rw [hrest, add_zero, PowerSeries.coeff_map, hR0, Int.cast_one, one_mul,
      PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero m)] at hc
    have hsub0 : N (m + 1) - ∑ j ∈ (Finset.Icc 1 (m + 1)).filter (· ∣ m + 1), (j : ℤ) * π j = 0 := by
      exact_mod_cast hc.symm
    have hdiv_eq : (Finset.Icc 1 (m + 1)).filter (· ∣ m + 1) = (m + 1).divisors := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨_, hdvd⟩; exact ⟨hdvd, Nat.succ_ne_zero m⟩
      · rintro ⟨hdvd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (Nat.succ_pos m), Nat.le_of_dvd (Nat.succ_pos m) hdvd⟩, hdvd⟩
    rw [hdiv_eq] at hsub0
    linarith
  have hghost_mem : IsGhost (fun n : ℕ+ => N n) :=
    isGhost_of_necklace (b := π) fun n => hN_eq n n.pos
  refine ⟨hghost_mem, π, rfl, hN_eq, fun k hk => ?_⟩
  let g : ℕ → ℤ := fun d => if d = 0 then 0 else N d
  have hmoeb := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => (d : ℤ) * π d) (g := g)).mp
      (fun m hm => by dsimp [g]; rw [if_neg (by omega)]; exact (hN_eq m hm).symm) k hk
  simp only [Int.cast_id] at hmoeb
  rw [Nat.sum_divisorsAntidiagonal' (fun i j => (ArithmeticFunction.moebius i : ℤ) * g j)] at hmoeb
  rw [← hmoeb]
  refine Finset.sum_congr rfl fun d hd => ?_
  dsimp [g]
  rw [if_neg (Nat.pos_of_mem_divisors hd).ne']

/-! ## 2. The prime-five (`q = 5`) genus-`2` non-real single-quartet curve datum -/

/-- Real part of `√(-20 + 2i)`: `u₀ = √(√101 - 10)`. -/
def fiveQuartetU : ℝ := Real.sqrt (Real.sqrt 101 - 10)

/-- Imaginary part of `√(-20 + 2i)`: `v₀ = √(√101 + 10)`. -/
def fiveQuartetV : ℝ := Real.sqrt (Real.sqrt 101 + 10)

private theorem ten_lt_sqrt_101 : (10 : ℝ) < Real.sqrt 101 := by
  rw [show (10 : ℝ) = Real.sqrt (10 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private theorem sqrt_101_lt_ten_tenths : Real.sqrt 101 < 101 / 10 := by
  rw [show (101 / 10 : ℝ) = Real.sqrt ((101 / 10) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private theorem fiveQuartetU_sq : fiveQuartetU ^ 2 = Real.sqrt 101 - 10 :=
  Real.sq_sqrt (by linarith [ten_lt_sqrt_101])

private theorem fiveQuartetV_sq : fiveQuartetV ^ 2 = Real.sqrt 101 + 10 :=
  Real.sq_sqrt (by linarith [ten_lt_sqrt_101])

private theorem fiveQuartetU_mul_V : fiveQuartetU * fiveQuartetV = 1 := by
  unfold fiveQuartetU fiveQuartetV
  rw [← Real.sqrt_mul (by linarith [ten_lt_sqrt_101])]
  have hprod : (Real.sqrt 101 - 10) * (Real.sqrt 101 + 10) = 1 := by
    have hsq : Real.sqrt 101 ^ 2 = 101 := Real.sq_sqrt (by norm_num)
    nlinarith
  rw [hprod, Real.sqrt_one]

/-- Outer Frobenius root `α₀ = ((1 + u₀) + i(1 + v₀)) / 2` of `z² - (1 + i)z + 5 = 0`. -/
def fiveQuartetAlpha0 : ℂ :=
  (((1 + fiveQuartetU) / 2 : ℝ) : ℂ) + (((1 + fiveQuartetV) / 2 : ℝ) : ℂ) * I

/-- Partner Frobenius root `α₂ = ((1 - u₀) + i(1 - v₀)) / 2` of `z² - (1 + i)z + 5 = 0`. -/
def fiveQuartetAlpha2 : ℂ :=
  (((1 - fiveQuartetU) / 2 : ℝ) : ℂ) + (((1 - fiveQuartetV) / 2 : ℝ) : ℂ) * I

theorem fiveQuartetAlpha_add_and_mul :
    fiveQuartetAlpha0 + fiveQuartetAlpha2 = 1 + I ∧
      fiveQuartetAlpha0 * fiveQuartetAlpha2 = 5 := by
  constructor
  · unfold fiveQuartetAlpha0 fiveQuartetAlpha2
    apply Complex.ext <;> simp <;> ring
  · unfold fiveQuartetAlpha0 fiveQuartetAlpha2
    have hu := fiveQuartetU_sq
    have hv := fiveQuartetV_sq
    have huv := fiveQuartetU_mul_V
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_add, Complex.add_im,
        Complex.mul_im, Complex.ofNat_re]
      nlinarith
    · simp only [Complex.mul_im, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_add, Complex.add_im,
        Complex.ofNat_im]
      nlinarith

theorem fiveQuartetAlpha_norms :
    5 < Complex.normSq fiveQuartetAlpha0 ∧
      Complex.normSq fiveQuartetAlpha0 < 9 ∧
      ‖fiveQuartetAlpha0‖ < 3 ∧
      ‖fiveQuartetAlpha2‖ < 3 := by
  have hu_pos : 0 < fiveQuartetU := Real.sqrt_pos.mpr (by linarith [ten_lt_sqrt_101])
  have hv_gt4 : 4 < fiveQuartetV := by
    unfold fiveQuartetV
    rw [show (4 : ℝ) = Real.sqrt (4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [ten_lt_sqrt_101])
  have hu_lt : fiveQuartetU < 2 / 5 := by
    unfold fiveQuartetU
    rw [show (2 / 5 : ℝ) = Real.sqrt ((2 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by linarith [ten_lt_sqrt_101]) (by linarith [sqrt_101_lt_ten_tenths])
  have hv_lt : fiveQuartetV < 9 / 2 := by
    unfold fiveQuartetV
    rw [show (9 / 2 : ℝ) = Real.sqrt ((9 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by linarith [ten_lt_sqrt_101]) (by linarith [sqrt_101_lt_ten_tenths])
  have hnsq0 : Complex.normSq fiveQuartetAlpha0 =
      ((1 + fiveQuartetU) / 2) ^ 2 + ((1 + fiveQuartetV) / 2) ^ 2 := by
    unfold fiveQuartetAlpha0
    rw [Complex.normSq_apply]
    simp [sq]
  have hgt5 : 5 < Complex.normSq fiveQuartetAlpha0 := by
    rw [hnsq0]; nlinarith [fiveQuartetU_sq, fiveQuartetV_sq, ten_lt_sqrt_101]
  have hlt9 : Complex.normSq fiveQuartetAlpha0 < 9 := by
    rw [hnsq0]; nlinarith [fiveQuartetU_sq, fiveQuartetV_sq, sqrt_101_lt_ten_tenths]
  have hn0_lt3 : ‖fiveQuartetAlpha0‖ < 3 := by
    rw [Complex.norm_def, show (3 : ℝ) = Real.sqrt 9 by norm_num]
    exact Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) hlt9
  have hn2_lt3 : ‖fiveQuartetAlpha2‖ < 3 := by
    have hprod := congrArg norm fiveQuartetAlpha_add_and_mul.2
    rw [norm_mul, Complex.norm_ofNat] at hprod
    have hn0_gt : Real.sqrt 5 < ‖fiveQuartetAlpha0‖ := by
      rw [Complex.norm_def]
      exact Real.sqrt_lt_sqrt (by norm_num) hgt5
    have h5_lt : Real.sqrt 5 > 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    nlinarith [norm_nonneg fiveQuartetAlpha2]
  exact ⟨hgt5, hlt9, hn0_lt3, hn2_lt3⟩

/-- **The prime-five genus-two non-real quartet curve datum (`q = 5`, `P_4(X) = 1 - 2X + 12X² - 10X³ + 25X⁴`).** -/
def primeFiveQuartetDatum : CurveDatum (Fin 4) where
  q := 5
  one_lt_q := by norm_num
  β := ![fiveQuartetAlpha0 / (Real.sqrt 5 : ℂ),
         conj fiveQuartetAlpha0 / (Real.sqrt 5 : ℂ),
         conj fiveQuartetAlpha2 / (Real.sqrt 5 : ℂ),
         fiveQuartetAlpha2 / (Real.sqrt 5 : ℂ)]
  conjPerm := ⟨![1, 0, 3, 2], ![1, 0, 3, 2], by decide, by decide⟩
  β_conjPerm i := by
    fin_cases i <;> simp [map_div₀]
  fePerm := ⟨![3, 2, 1, 0], ![3, 2, 1, 0], by decide, by decide⟩
  β_fePerm i := by
    have h5_ne : (Real.sqrt 5 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    have h5_sq : (Real.sqrt 5 : ℂ) * (Real.sqrt 5 : ℂ) = 5 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num), Complex.ofReal_ofNat]
    have hmul := fiveQuartetAlpha_add_and_mul.2
    have hcmul : conj fiveQuartetAlpha0 * conj fiveQuartetAlpha2 = 5 := by
      rw [← map_mul, hmul, map_ofNat]
    fin_cases i
    · show (fiveQuartetAlpha2 / (Real.sqrt 5 : ℂ)) * (fiveQuartetAlpha0 / (Real.sqrt 5 : ℂ)) = 1
      rw [div_mul_div_comm, mul_comm fiveQuartetAlpha2, hmul, h5_sq, div_self (by norm_num)]
    · show (conj fiveQuartetAlpha2 / (Real.sqrt 5 : ℂ)) * (conj fiveQuartetAlpha0 / (Real.sqrt 5 : ℂ)) = 1
      rw [div_mul_div_comm, mul_comm (conj fiveQuartetAlpha2), hcmul, h5_sq, div_self (by norm_num)]
    · show (conj fiveQuartetAlpha0 / (Real.sqrt 5 : ℂ)) * (conj fiveQuartetAlpha2 / (Real.sqrt 5 : ℂ)) = 1
      rw [div_mul_div_comm, hcmul, h5_sq, div_self (by norm_num)]
    · show (fiveQuartetAlpha0 / (Real.sqrt 5 : ℂ)) * (fiveQuartetAlpha2 / (Real.sqrt 5 : ℂ)) = 1
      rw [div_mul_div_comm, hmul, h5_sq, div_self (by norm_num)]

theorem primeFiveQuartetDatum_alpha :
    primeFiveQuartetDatum.alpha =
      ![fiveQuartetAlpha0, conj fiveQuartetAlpha0, conj fiveQuartetAlpha2, fiveQuartetAlpha2] := by
  have hs : primeFiveQuartetDatum.sqrtq = Real.sqrt 5 := rfl
  have h5_ne : (Real.sqrt 5 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  funext i
  rw [CurveDatum.alpha, hs]
  fin_cases i <;> simp [primeFiveQuartetDatum, mul_div_cancel₀ _ h5_ne]

theorem primeFiveQuartetDatum_im_ne_zero (i : Fin 4) :
    (primeFiveQuartetDatum.β i).im ≠ 0 := by
  have hv_gt4 : 4 < fiveQuartetV := by
    unfold fiveQuartetV
    rw [show (4 : ℝ) = Real.sqrt (4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [ten_lt_sqrt_101])
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have him0 : fiveQuartetAlpha0.im = (1 + fiveQuartetV) / 2 := by simp [fiveQuartetAlpha0]
  have him2 : fiveQuartetAlpha2.im = (1 - fiveQuartetV) / 2 := by simp [fiveQuartetAlpha2]
  fin_cases i <;>
    simp only [primeFiveQuartetDatum, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, div_ofReal_im, Complex.conj_im, him0, him2]
  · exact div_ne_zero (by linarith) hs5.ne'
  · exact div_ne_zero (by linarith) hs5.ne'
  · exact div_ne_zero (by linarith) hs5.ne'
  · exact div_ne_zero (by linarith) hs5.ne'

theorem primeFiveQuartetDatum_not_unitary :
    ¬ ∀ i : Fin 4, ‖primeFiveQuartetDatum.β i‖ = 1 := by
  intro hall
  have h0 := hall 0
  simp only [primeFiveQuartetDatum, Matrix.cons_val_zero, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))] at h0
  have hsq5 : Real.sqrt 5 < ‖fiveQuartetAlpha0‖ := by
    rw [Complex.norm_def]
    exact Real.sqrt_lt_sqrt (by norm_num) fiveQuartetAlpha_norms.1
  have h5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_eq_one_iff_eq h5_pos.ne'] at h0
  linarith

/-- Exact `H¹` numerator `P_4(X) = 1 - 2X + 12X² - 10X³ + 25X⁴`. -/
theorem primeFiveQuartetDatum_hOnePoly :
    primeFiveQuartetDatum.hOnePoly =
      1 - C 2 * X + C 12 * X ^ 2 - C 10 * X ^ 3 + C 25 * X ^ 4 := by
  rw [CurveDatum.hOnePoly, Fin.prod_univ_four, primeFiveQuartetDatum_alpha]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  obtain ⟨hadd, hmul⟩ := fiveQuartetAlpha_add_and_mul
  have hcadd : conj fiveQuartetAlpha0 + conj fiveQuartetAlpha2 = 1 - I := by
    rw [← map_add, hadd, map_add, map_one, Complex.conj_I]; ring
  have hcmul : conj fiveQuartetAlpha0 * conj fiveQuartetAlpha2 = 5 := by
    rw [← map_mul, hmul, map_ofNat]
  have hf1 : (1 - C fiveQuartetAlpha0 * X) * (1 - C fiveQuartetAlpha2 * X) =
      1 - C (1 + I) * X + C 5 * X ^ 2 := by
    calc (1 - C fiveQuartetAlpha0 * X) * (1 - C fiveQuartetAlpha2 * X)
        = 1 - C (fiveQuartetAlpha0 + fiveQuartetAlpha2) * X +
            C (fiveQuartetAlpha0 * fiveQuartetAlpha2) * X ^ 2 := by
          simp only [map_add, map_mul]; ring
      _ = 1 - C (1 + I) * X + C 5 * X ^ 2 := by rw [hadd, hmul]; norm_num
  have hf2 : (1 - C (conj fiveQuartetAlpha0) * X) * (1 - C (conj fiveQuartetAlpha2) * X) =
      1 - C (1 - I) * X + C 5 * X ^ 2 := by
    calc (1 - C (conj fiveQuartetAlpha0) * X) * (1 - C (conj fiveQuartetAlpha2) * X)
        = 1 - C (conj fiveQuartetAlpha0 + conj fiveQuartetAlpha2) * X +
            C (conj fiveQuartetAlpha0 * conj fiveQuartetAlpha2) * X ^ 2 := by
          simp only [map_add, map_mul]; ring
      _ = 1 - C (1 - I) * X + C 5 * X ^ 2 := by rw [hcadd, hcmul]; norm_num
  have hpair : (1 - C fiveQuartetAlpha0 * X) * (1 - C (conj fiveQuartetAlpha0) * X) *
      (1 - C (conj fiveQuartetAlpha2) * X) * (1 - C fiveQuartetAlpha2 * X) =
      ((1 - C fiveQuartetAlpha0 * X) * (1 - C fiveQuartetAlpha2 * X)) *
      ((1 - C (conj fiveQuartetAlpha0) * X) * (1 - C (conj fiveQuartetAlpha2) * X)) := by ring
  rw [hpair, hf1, hf2]
  have hI2 : C (1 + I) * C (1 - I) = (C 2 : ℂ⟦X⟧) := by
    rw [← map_mul]
    congr 1
    ring_nf; simp [Complex.I_sq]; norm_num
  have hIsum : C (1 + I) + C (1 - I) = (C 2 : ℂ⟦X⟧) := by
    rw [← map_add]; congr 1; ring
  calc (1 - C (1 + I) * X + C 5 * X ^ 2) * (1 - C (1 - I) * X + C 5 * X ^ 2)
      = 1 - (C (1 + I) + C (1 - I)) * X + (C 10 + C (1 + I) * C (1 - I)) * X ^ 2 -
          C 5 * (C (1 + I) + C (1 - I)) * X ^ 3 + C 25 * X ^ 4 := by
        simp only [← map_mul, ← map_add]; ring_nf; norm_num
    _ = 1 - C 2 * X + C 12 * X ^ 2 - C 10 * X ^ 3 + C 25 * X ^ 4 := by
        rw [hIsum, hI2]
        simp only [← map_add, ← map_mul]
        norm_num

/-- Newton's integer trace sequence of `P_4(X) = 1 - 2X + 12X² - 10X³ + 25X⁴`. -/
def fiveQuartetTrace : ℕ → ℤ
  | 0 => 4
  | 1 => 2
  | 2 => -20
  | 3 => -34
  | n + 4 => 2 * fiveQuartetTrace (n + 3) - 12 * fiveQuartetTrace (n + 2) +
      10 * fiveQuartetTrace (n + 1) - 25 * fiveQuartetTrace n

theorem primeFiveQuartetDatum_powerSum_eq_trace (n : ℕ) :
    primeFiveQuartetDatum.sqrtq ^ n * primeFiveQuartetDatum.trace n = fiveQuartetTrace n := by
  have hs : primeFiveQuartetDatum.sqrtq = Real.sqrt 5 := rfl
  have hpow_eq : ∀ k : ℕ, ((primeFiveQuartetDatum.sqrtq ^ k * primeFiveQuartetDatum.trace k : ℝ) : ℂ) =
      fiveQuartetAlpha0 ^ k + conj fiveQuartetAlpha0 ^ k +
        conj fiveQuartetAlpha2 ^ k + fiveQuartetAlpha2 ^ k := by
    intro k
    rw [← primeFiveQuartetDatum.powerSum_eq_trace, CurveDatum.powerSum, Fin.sum_univ_four]
    have hmul : ∀ i : Fin 4, (primeFiveQuartetDatum.sqrtq : ℂ) * primeFiveQuartetDatum.β i =
        primeFiveQuartetDatum.alpha i := fun _ => rfl
    push_cast
    rw [Finset.mul_sum]
    simp_rw [← mul_pow, hmul, primeFiveQuartetDatum_alpha]
    simp [add_assoc]
  -- Each root satisfies `α^4 = 2 α^3 - 12 α^2 + 10 α - 25`.
  obtain ⟨hadd, hmul⟩ := fiveQuartetAlpha_add_and_mul
  have hroot_quad : ∀ z : ℂ, z ^ 2 - (1 + I) * z + 5 = 0 →
      z ^ 4 = 2 * z ^ 3 - 12 * z ^ 2 + 10 * z - 25 := by
    intro z hz
    have hc : (z ^ 2 - (1 + I) * z + 5) * (z ^ 2 - (1 - I) * z + 5) = 0 := by rw [hz, zero_mul]
    have hexp : (z ^ 2 - (1 + I) * z + 5) * (z ^ 2 - (1 - I) * z + 5) =
        z ^ 4 - 2 * z ^ 3 + 12 * z ^ 2 - 10 * z + 25 := by
      ring_nf; simp [Complex.I_sq]; ring
    rw [hexp] at hc
    linear_combination hc
  have hroot_cquad : ∀ z : ℂ, z ^ 2 - (1 - I) * z + 5 = 0 →
      z ^ 4 = 2 * z ^ 3 - 12 * z ^ 2 + 10 * z - 25 := by
    intro z hz
    have hc : (z ^ 2 - (1 + I) * z + 5) * (z ^ 2 - (1 - I) * z + 5) = 0 := by rw [hz, mul_zero]
    have hexp : (z ^ 2 - (1 + I) * z + 5) * (z ^ 2 - (1 - I) * z + 5) =
        z ^ 4 - 2 * z ^ 3 + 12 * z ^ 2 - 10 * z + 25 := by
      ring_nf; simp [Complex.I_sq]; ring
    rw [hexp] at hc
    linear_combination hc
  have hz0 : fiveQuartetAlpha0 ^ 2 - (1 + I) * fiveQuartetAlpha0 + 5 = 0 := by
    rw [← hadd, ← hmul]; ring
  have hz2 : fiveQuartetAlpha2 ^ 2 - (1 + I) * fiveQuartetAlpha2 + 5 = 0 := by
    rw [← hadd, ← hmul]; ring
  have hcz0 : conj fiveQuartetAlpha0 ^ 2 - (1 - I) * conj fiveQuartetAlpha0 + 5 = 0 := by
    have hc := congrArg conj hz0
    simpa [Complex.conj_I, sub_eq_add_neg] using hc
  have hcz2 : conj fiveQuartetAlpha2 ^ 2 - (1 - I) * conj fiveQuartetAlpha2 + 5 = 0 := by
    have hc := congrArg conj hz2
    simpa [Complex.conj_I, sub_eq_add_neg] using hc
  -- Prove the identity in `ℂ` by strong induction on `n`.
  suffices hC : ∀ m : ℕ,
      fiveQuartetAlpha0 ^ m + conj fiveQuartetAlpha0 ^ m +
        conj fiveQuartetAlpha2 ^ m + fiveQuartetAlpha2 ^ m = (fiveQuartetTrace m : ℂ) by
    have heq := (hpow_eq n).trans (hC n)
    exact_mod_cast heq
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp [fiveQuartetTrace]; norm_num
    | 1 =>
      simp only [pow_one, fiveQuartetTrace]
      have hcadd : conj fiveQuartetAlpha0 + conj fiveQuartetAlpha2 = 1 - I := by
        rw [← map_add, hadd, map_add, map_one, Complex.conj_I]; ring
      calc fiveQuartetAlpha0 + conj fiveQuartetAlpha0 + conj fiveQuartetAlpha2 + fiveQuartetAlpha2
          = (fiveQuartetAlpha0 + fiveQuartetAlpha2) + (conj fiveQuartetAlpha0 + conj fiveQuartetAlpha2) := by ring
        _ = (1 + I) + (1 - I) := by rw [hadd, hcadd]
        _ = (2 : ℤ) := by norm_num
    | 2 =>
      simp only [fiveQuartetTrace]
      have hsq1 : fiveQuartetAlpha0 ^ 2 + fiveQuartetAlpha2 ^ 2 = -10 + 2 * I := by
        have : fiveQuartetAlpha0 ^ 2 + fiveQuartetAlpha2 ^ 2 =
            (fiveQuartetAlpha0 + fiveQuartetAlpha2) ^ 2 - 2 * (fiveQuartetAlpha0 * fiveQuartetAlpha2) := by ring
        rw [this, hadd, hmul]; ring_nf; simp [Complex.I_sq]; ring
      have hsq2 : conj fiveQuartetAlpha0 ^ 2 + conj fiveQuartetAlpha2 ^ 2 = -10 - 2 * I := by
        have hc := congrArg conj hsq1
        simpa [Complex.conj_I, sub_eq_add_neg] using hc
      calc fiveQuartetAlpha0 ^ 2 + conj fiveQuartetAlpha0 ^ 2 + conj fiveQuartetAlpha2 ^ 2 + fiveQuartetAlpha2 ^ 2
          = (fiveQuartetAlpha0 ^ 2 + fiveQuartetAlpha2 ^ 2) +
              (conj fiveQuartetAlpha0 ^ 2 + conj fiveQuartetAlpha2 ^ 2) := by ring
        _ = (-10 + 2 * I) + (-10 - 2 * I) := by rw [hsq1, hsq2]
        _ = (-20 : ℤ) := by norm_num
    | 3 =>
      simp only [fiveQuartetTrace]
      have hcub1 : fiveQuartetAlpha0 ^ 3 + fiveQuartetAlpha2 ^ 3 = -17 - 13 * I := by
        have : fiveQuartetAlpha0 ^ 3 + fiveQuartetAlpha2 ^ 3 =
            (fiveQuartetAlpha0 + fiveQuartetAlpha2) ^ 3 -
              3 * (fiveQuartetAlpha0 * fiveQuartetAlpha2) * (fiveQuartetAlpha0 + fiveQuartetAlpha2) := by ring
        rw [this, hadd, hmul]; ring_nf; simp [Complex.I_sq]; ring
      have hcub2 : conj fiveQuartetAlpha0 ^ 3 + conj fiveQuartetAlpha2 ^ 3 = -17 + 13 * I := by
        have hc := congrArg conj hcub1
        simpa [Complex.conj_I, sub_eq_add_neg] using hc
      calc fiveQuartetAlpha0 ^ 3 + conj fiveQuartetAlpha0 ^ 3 + conj fiveQuartetAlpha2 ^ 3 + fiveQuartetAlpha2 ^ 3
          = (fiveQuartetAlpha0 ^ 3 + fiveQuartetAlpha2 ^ 3) +
              (conj fiveQuartetAlpha0 ^ 3 + conj fiveQuartetAlpha2 ^ 3) := by ring
        _ = (-17 - 13 * I) + (-17 + 13 * I) := by rw [hcub1, hcub2]
        _ = (-34 : ℤ) := by norm_num
    | k + 4 =>
      have hr0 := hroot_quad _ hz0
      have hr2 := hroot_quad _ hz2
      have hcr0 := hroot_cquad _ hcz0
      have hcr2 := hroot_cquad _ hcz2
      have hstep : ∀ z : ℂ, z ^ 4 = 2 * z ^ 3 - 12 * z ^ 2 + 10 * z - 25 →
          z ^ (k + 4) = 2 * z ^ (k + 3) - 12 * z ^ (k + 2) + 10 * z ^ (k + 1) - 25 * z ^ k := by
        intro z hz4
        calc z ^ (k + 4) = z ^ k * z ^ 4 := by ring
          _ = z ^ k * (2 * z ^ 3 - 12 * z ^ 2 + 10 * z - 25) := by rw [hz4]
          _ = 2 * z ^ (k + 3) - 12 * z ^ (k + 2) + 10 * z ^ (k + 1) - 25 * z ^ k := by ring
      rw [hstep _ hr0, hstep _ hcr0, hstep _ hcr2, hstep _ hr2]
      have i3 := ih (k + 3) (by omega)
      have i2 := ih (k + 2) (by omega)
      have i1 := ih (k + 1) (by omega)
      have i0 := ih k (by omega)
      rw [fiveQuartetTrace]
      push_cast
      linear_combination 2 * i3 - 12 * i2 + 10 * i1 - 25 * i0

/-- Integer point counts `N_n = 5^n + 1 - fiveQuartetTrace n` of `primeFiveQuartetDatum`. -/
def fiveQuartetPointCount (n : ℕ) : ℤ :=
  (5 : ℤ) ^ n + 1 - fiveQuartetTrace n

theorem primeFiveQuartetDatum_pointCount_eq (n : ℕ) :
    primeFiveQuartetDatum.pointCount n = (fiveQuartetPointCount n : ℝ) := by
  rw [CurveDatum.pointCount, primeFiveQuartetDatum_powerSum_eq_trace]
  have hq : primeFiveQuartetDatum.q = 5 := rfl
  rw [hq, fiveQuartetPointCount]
  push_cast
  ring

theorem primeFiveQuartetDatum_zetaSeries_integral :
    ∃ Zℤ : ℤ⟦X⟧, PowerSeries.constantCoeff Zℤ = 1 ∧
      PowerSeries.map (Int.castRingHom ℂ) Zℤ = primeFiveQuartetDatum.zetaSeries := by
  refine ⟨(PowerSeries.mk fun n => (1 : ℤ) ^ n) * (PowerSeries.mk fun n => (5 : ℤ) ^ n) *
      (1 - C 2 * X + C 12 * X ^ 2 - C 10 * X ^ 3 + C 25 * X ^ 4), by simp, ?_⟩
  have hq : ((primeFiveQuartetDatum.q : ℝ) : ℂ) = ((5 : ℤ) : ℂ) := by
    show ((5 : ℝ) : ℂ) = ((5 : ℤ) : ℂ); norm_num
  rw [CurveDatum.zetaSeries, CurveDatum.poleZeta, primeFiveQuartetDatum_hOnePoly,
    map_mul, map_mul, map_mk_pow, map_mk_pow, Int.cast_one, hq]
  congr 1
  simp only [map_add, map_sub, map_one, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  norm_num

private theorem abs_fiveQuartetTrace_le (n : ℕ) :
    |(fiveQuartetTrace n : ℝ)| ≤ 4 * (3 : ℝ) ^ n := by
  rw [← primeFiveQuartetDatum_powerSum_eq_trace, ← Real.norm_eq_abs, ← Complex.norm_real]
  have heq : ((primeFiveQuartetDatum.sqrtq ^ n * primeFiveQuartetDatum.trace n : ℝ) : ℂ) =
      ∑ i : Fin 4, primeFiveQuartetDatum.alpha i ^ n := by
    rw [← primeFiveQuartetDatum.powerSum_eq_trace, CurveDatum.powerSum]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← mul_pow]; rfl
  rw [heq]
  refine (norm_sum_le _ _).trans ?_
  have hlt3 : ∀ i : Fin 4, ‖primeFiveQuartetDatum.alpha i‖ ≤ 3 := by
    obtain ⟨-, -, hn0, hn2⟩ := fiveQuartetAlpha_norms
    intro i
    rw [primeFiveQuartetDatum_alpha]
    fin_cases i <;> simp [hn0.le, hn2.le]
  calc ∑ i : Fin 4, ‖primeFiveQuartetDatum.alpha i ^ n‖
      ≤ ∑ _i : Fin 4, (3 : ℝ) ^ n := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hlt3 i) n
    _ = 4 * (3 : ℝ) ^ n := by simp

private theorem five_pow_dominates_for_five_le :
    ∀ d : ℕ, 5 ≤ d → 4 * (3 : ℤ) ^ d + 3 * (d : ℤ) * (5 : ℤ) ^ (d / 2) < (5 : ℤ) ^ d := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    by_cases hd7 : d ≤ 7
    · interval_cases d <;> norm_num
    · have hexp_gap : 2 + (d + 1) / 2 ≤ d := by omega
      have hmul_5 : 25 * (5 : ℤ) ^ (d - 2 - (d + 1) / 2) * (5 : ℤ) ^ ((d + 1) / 2) = (5 : ℤ) ^ d := by
        rw [show (25 : ℤ) = 5 ^ 2 by norm_num, ← pow_add, ← pow_add]
        congr 1; omega
      have h1_le_10 : (d : ℤ) + 1 ≤ 5 * (5 : ℤ) ^ (d - 2 - (d + 1) / 2) := by
        have hm_pow : ∀ m : ℕ, (m : ℤ) + 1 ≤ (5 : ℤ) ^ m := by
          intro m; induction m with
          | zero => norm_num
          | succ m ihm =>
            have : (1 : ℤ) ≤ (5 : ℤ) ^ m := one_le_pow₀ (by norm_num)
            calc ((m + 1 : ℕ) : ℤ) + 1 = (m : ℤ) + 1 + 1 := by push_cast; ring
              _ ≤ 5 * (5 : ℤ) ^ m := by linarith
              _ = (5 : ℤ) ^ (m + 1) := by ring
        have hlin : (d : ℤ) + 1 ≤ 5 * (((d - 2 - (d + 1) / 2 : ℕ) : ℤ) + 1) := by omega
        exact hlin.trans (Int.mul_le_mul_of_nonneg_left (hm_pow _) (by norm_num))
      have hterm2_sharp : 3 * ((d : ℤ) + 1) * (5 : ℤ) ^ ((d + 1) / 2) ≤ (5 : ℤ) ^ d := by
        calc 3 * ((d : ℤ) + 1) * (5 : ℤ) ^ ((d + 1) / 2)
            ≤ 25 * (5 : ℤ) ^ (d - 2 - (d + 1) / 2) * (5 : ℤ) ^ ((d + 1) / 2) := by
              have := Int.mul_le_mul_of_nonneg_right h1_le_10
                (le_of_lt (pow_pos (by norm_num : (0 : ℤ) < 5) ((d + 1) / 2)))
              linarith
          _ = (5 : ℤ) ^ d := hmul_5
      have h3d : 4 * (3 : ℤ) ^ (d + 1) < 3 * (5 : ℤ) ^ d := by
        have : 4 * (3 : ℤ) ^ d < (5 : ℤ) ^ d := by
          have : 0 ≤ 3 * (d : ℤ) * (5 : ℤ) ^ (d / 2) := by positivity
          linarith
        calc 4 * (3 : ℤ) ^ (d + 1) = 3 * (4 * (3 : ℤ) ^ d) := by ring
          _ < 3 * (5 : ℤ) ^ d := by linarith
      have h5_succ : (5 : ℤ) ^ (d + 1) = 5 * (5 : ℤ) ^ d := by ring
      have h5d_pos : 0 < (5 : ℤ) ^ d := pow_pos (by norm_num) d
      linarith

/-- **Complete Beurling Euler-product and count-law profile of `primeFiveQuartetDatum`.**
Over the prime base `q = 5`, `primeFiveQuartetDatum` has:
1. Integral zeta series in `1 + X ℤ⟦X⟧` with functional equation and non-real off-circle quartet;
2. Nonnegative degree-`1` kernel counts `detDeg P ≥ 0` for all `P ∈ ℝ[X]`;
3. An effective Witt ghost element (`0 ≤ coord x d` for all `d` and `1 ≤ coord x d` for every `d ≥ 1`,
   with `coord x 1 = 4`, `coord x 2 = 21`, `coord x 3 = 52`) realizing `N_k = ∑_{d ∣ k} d π_d`;
4. Genus-`2` Weil count laws at levels `n = 1, 2, 3` (with exact boundary equality
   `fiveQuartetTrace 2 ^ 2 = 16 * 5 ^ 2 = 400` at `n = 2`), while failing the full tower count law. -/
theorem primeFiveQuartet_complete_twin :
    (∃ Zℤ : ℤ⟦X⟧, PowerSeries.constantCoeff Zℤ = 1 ∧
      PowerSeries.map (Int.castRingHom ℂ) Zℤ = primeFiveQuartetDatum.zetaSeries) ∧
    (∀ i : Fin 4, (primeFiveQuartetDatum.β i).im ≠ 0) ∧
    ¬ (∀ i : Fin 4, ‖primeFiveQuartetDatum.β i‖ = 1) ∧
    (∃ x : ghostRing, (∀ d : ℕ, 0 ≤ coord x d) ∧
      coord x 1 = 4 ∧ coord x 2 = 21 ∧ coord x 3 = 52 ∧
      (∀ d : ℕ, 1 ≤ d → 1 ≤ coord x d) ∧
      (∀ k : ℕ+, ((ghostComponent k x : ℤ) : ℝ) = primeFiveQuartetDatum.pointCount k)) ∧
    (∀ n ∈ ({1, 2, 3} : Finset ℕ), ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧
      (K 0 1 : ℤ) = 2 ∧ (K 1 0 : ℤ) = 2 * (5 : ℤ) ^ n ∧
      (K 1 1 : ℤ) = 2 * ((5 : ℤ) ^ n + 1) - fiveQuartetTrace n) ∧
    fiveQuartetTrace 2 ^ 2 = 16 * (5 : ℤ) ^ 2 ∧
    ¬ (∀ n : ℕ, 1 ≤ n → ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧
      (K 0 1 : ℤ) = 2 ∧ (K 1 0 : ℤ) = 2 * (5 : ℤ) ^ n ∧
      (K 1 1 : ℤ) = 2 * ((5 : ℤ) ^ n + 1) - fiveQuartetTrace n) := by
  obtain ⟨Zℤ, hZ0, hZmap⟩ := primeFiveQuartetDatum_zetaSeries_integral
  have hghost_eq : primeFiveQuartetDatum.ghostSeries =
      PowerSeries.mk fun k => if k = 0 then 0 else (fiveQuartetPointCount k : ℂ) := by
    ext k
    simp only [CurveDatum.ghostSeries, PowerSeries.coeff_mk]
    split_ifs with hk0
    · rfl
    · rw [primeFiveQuartetDatum_pointCount_eq]; push_cast; rfl
  have hghost_Z : HasGhost (PowerSeries.map (Int.castRingHom ℂ) Zℤ)
      (PowerSeries.mk fun k => if k = 0 then 0 else (fiveQuartetPointCount k : ℂ)) := by
    rw [hZmap, ← hghost_eq]
    exact primeFiveQuartetDatum.zetaSeries_hasGhost
  obtain ⟨hIsGhost, π, hπ0, hN_sum, hmoeb_sum⟩ :=
    exists_int_necklace_of_integral_hasGhost Zℤ hZ0 fiveQuartetPointCount hghost_Z
  -- Bound `fiveQuartetPointCount m` from above and below via `|fiveQuartetTrace m| ≤ 4 * 3^m`.
  have htr_int : ∀ m : ℕ, |fiveQuartetTrace m| ≤ 4 * (3 : ℤ) ^ m := by
    intro m
    have hr := abs_fiveQuartetTrace_le m
    exact_mod_cast hr
  have hN_bounds : ∀ m : ℕ,
      (5 : ℤ) ^ m + 1 - 4 * (3 : ℤ) ^ m ≤ fiveQuartetPointCount m ∧
        fiveQuartetPointCount m ≤ (5 : ℤ) ^ m + 1 + 4 * (3 : ℤ) ^ m := by
    intro m
    have habs := abs_le.mp (htr_int m)
    unfold fiveQuartetPointCount
    exact ⟨by linarith, by linarith⟩
  -- Explicit values `π 1 = 4`, `π 2 = 21`, `π 3 = 52`, `π 4 = 122` and positivity `1 ≤ π d` for all `d ≥ 1`.
  have hπ1 : π 1 = 4 := by
    have h1 := hN_sum 1 le_rfl
    simp [fiveQuartetPointCount, fiveQuartetTrace] at h1
    linarith
  have hπ2 : π 2 = 21 := by
    have h2 := hN_sum 2 (by decide)
    have hdiv2 : (2 : ℕ).divisors = {1, 2} := by decide
    rw [hdiv2] at h2
    simp only [Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), Nat.cast_one, one_mul, Nat.cast_ofNat,
      hπ1, fiveQuartetPointCount, fiveQuartetTrace] at h2
    linarith
  have hπ3 : π 3 = 52 := by
    have h3 := hN_sum 3 (by decide)
    have hdiv3 : (3 : ℕ).divisors = {1, 3} := by decide
    rw [hdiv3] at h3
    simp only [Finset.sum_pair (by decide : (1 : ℕ) ≠ 3), Nat.cast_one, one_mul, Nat.cast_ofNat,
      hπ1, fiveQuartetPointCount, fiveQuartetTrace] at h3
    linarith
  have hπ4 : π 4 = 122 := by
    have h4 := hN_sum 4 (by decide)
    have hdiv4 : (4 : ℕ).divisors = {1, 2, 4} := by decide
    have htr4 : fiveQuartetTrace 4 = 92 := by decide
    rw [hdiv4] at h4
    simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 4} : Finset ℕ)),
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 4), Nat.cast_one, one_mul, Nat.cast_ofNat,
      hπ1, hπ2, fiveQuartetPointCount, htr4] at h4
    linarith
  have hπ_pos : ∀ d : ℕ, 1 ≤ d → 1 ≤ π d := by
    intro d hd1
    rcases lt_or_ge d 5 with hlt5 | hge5
    · interval_cases d <;> omega
    · -- Use `(d : ℤ) * π d = ∑_{e ∣ d} μ(d/e) N_e ≥ N_d - ∑_{e ∈ properDivisors d} |N_e| > 0`.
      have hm := hmoeb_sum d hd1
      rw [← Nat.cons_self_properDivisors (by omega : d ≠ 0), Finset.sum_cons,
        Nat.div_self hd1] at hm
      have hmu1 : (ArithmeticFunction.moebius 1 : ℤ) = 1 := by simp
      rw [hmu1, one_mul] at hm
      -- Every proper divisor `e` of `d` has `1 ≤ e ≤ d / 2` and `0 ≤ N_e ≤ 6 * 5^{d/2}`.
      have hprop_le : ∑ e ∈ d.properDivisors,
          -(ArithmeticFunction.moebius (d / e) : ℤ) * fiveQuartetPointCount e ≤
          3 * (d : ℤ) * (5 : ℤ) ^ (d / 2) := by
        have hcard_prop : (d.properDivisors.card : ℤ) ≤ d / 2 := by
          have hsub : d.properDivisors ⊆ Finset.Icc 1 (d / 2) := by
            intro e he
            obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp he
            have he_pos : 1 ≤ e := Nat.pos_of_dvd_of_pos hdvd hd1
            obtain ⟨q, hq⟩ := hdvd
            have hq2 : 2 ≤ q := by
              by_contra hq1
              have : q ≤ 1 := by omega
              have : e * q ≤ e * 1 := Nat.mul_le_mul_left e this
              omega
            exact Finset.mem_Icc.mpr ⟨he_pos, by have := Nat.mul_le_mul_left e hq2; omega⟩
          have hle_nat := (Finset.card_le_card hsub).trans (by simp : (Finset.Icc 1 (d / 2)).card ≤ d / 2)
          exact_mod_cast hle_nat
        calc ∑ e ∈ d.properDivisors,
              -(ArithmeticFunction.moebius (d / e) : ℤ) * fiveQuartetPointCount e
            ≤ ∑ _e ∈ d.properDivisors, 6 * (5 : ℤ) ^ (d / 2) := by
              refine Finset.sum_le_sum fun e he => ?_
              obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp he
              have he_pos : 1 ≤ e := Nat.pos_of_dvd_of_pos hdvd hd1
              obtain ⟨q, hq⟩ := hdvd
              have hq2 : 2 ≤ q := by
                by_contra hq1; have : q ≤ 1 := by omega
                have : e * q ≤ e * 1 := Nat.mul_le_mul_left e this; omega
              have he_half : e ≤ d / 2 := by have := Nat.mul_le_mul_left e hq2; omega
              have hNe_up : fiveQuartetPointCount e ≤ 6 * (5 : ℤ) ^ (d / 2) := by
                have hup := (hN_bounds e).2
                have h5e : (5 : ℤ) ^ e ≤ (5 : ℤ) ^ (d / 2) := pow_le_pow_right₀ (by norm_num) he_half
                have h3e : 4 * (3 : ℤ) ^ e ≤ 4 * (5 : ℤ) ^ (d / 2) := by
                  have h1 : (3 : ℤ) ^ e ≤ (5 : ℤ) ^ e := pow_le_pow_left₀ (by norm_num) (by norm_num) e
                  linarith
                have h1_le : 1 ≤ (5 : ℤ) ^ (d / 2) := one_le_pow₀ (by norm_num)
                linarith
              have hNe_nn : 0 ≤ fiveQuartetPointCount e := by
                rcases lt_or_ge e 3 with he3 | he3
                · interval_cases e <;> decide
                · have hlow := (hN_bounds e).1
                  -- `4 * 3^e ≤ 5^e` for `e ≥ 3`: `4 * 27 = 108 < 125`!
                  have h35 : ∀ m : ℕ, 3 ≤ m → 4 * (3 : ℤ) ^ m ≤ (5 : ℤ) ^ m := by
                    intro m hm3
                    induction m, hm3 using Nat.le_induction with
                    | base => norm_num
                    | succ m _ ihm =>
                      calc 4 * (3 : ℤ) ^ (m + 1) = 3 * (4 * (3 : ℤ) ^ m) := by ring
                        _ ≤ 3 * (5 : ℤ) ^ m := by linarith
                        _ ≤ 5 * (5 : ℤ) ^ m := by nlinarith [pow_pos (by norm_num : (0 : ℤ) < 5) m]
                        _ = (5 : ℤ) ^ (m + 1) := by ring
                  linarith [h35 e he3]
              have hmu_le : -(ArithmeticFunction.moebius (d / e) : ℤ) ≤ 1 := by
                have habs := ArithmeticFunction.abs_moebius_le_one (d / e)
                linarith [(abs_le.mp habs).1]
              calc -(ArithmeticFunction.moebius (d / e) : ℤ) * fiveQuartetPointCount e
                  ≤ 1 * fiveQuartetPointCount e :=
                    Int.mul_le_mul_of_nonneg_right hmu_le hNe_nn
                _ ≤ 6 * (5 : ℤ) ^ (d / 2) := by linarith
          _ = (d.properDivisors.card : ℤ) * (6 * (5 : ℤ) ^ (d / 2)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (d / 2 : ℕ) * (6 * (5 : ℤ) ^ (d / 2)) :=
              Int.mul_le_mul_of_nonneg_right hcard_prop (by positivity)
          _ ≤ 3 * (d : ℤ) * (5 : ℤ) ^ (d / 2) := by
              have hdiv2 : 2 * ((d / 2 : ℕ) : ℤ) ≤ d := by omega
              nlinarith [pow_pos (by norm_num : (0 : ℤ) < 5) (d / 2)]
      have hdom := five_pow_dominates_for_five_le d hge5
      have hNd_low := (hN_bounds d).1
      have hdπ_pos : 0 < (d : ℤ) * π d := by
        have hneg_sum : ∑ e ∈ d.properDivisors,
            (ArithmeticFunction.moebius (d / e) : ℤ) * fiveQuartetPointCount e =
          -(∑ e ∈ d.properDivisors,
            -(ArithmeticFunction.moebius (d / e) : ℤ) * fiveQuartetPointCount e) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun _ _ => by ring
        rw [hneg_sum] at hm
        linarith
      have hd_zpos : (0 : ℤ) < d := by exact_mod_cast hd1
      have hπ_gt0 : 0 < π d := pos_of_mul_pos_right hdπ_pos hd_zpos.le
      omega
  -- Package `x` in `ghostRing`.
  let x : ghostRing :=
    ⟨fun n => ∑ d ∈ (n : ℕ).divisors, (d : ℤ) * π d, isGhost_of_necklace (b := π) fun _ => rfl⟩
  have hcoord_x : ∀ d : ℕ, 1 ≤ d → coord x d = π d := by
    intro d hd
    refine necklace_unique (b := coord x) (b' := π) (fun n hn => ?_) d (by omega)
    obtain ⟨N_p, rfl⟩ : ∃ N_p : ℕ+, (N_p : ℕ) = n := ⟨⟨n, Nat.pos_of_ne_zero hn⟩, rfl⟩
    rw [← ghostComponent_eq_sum_coord]
    rfl
  have heff_x : ∀ d : ℕ, 0 ≤ coord x d := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [coord, necklace_eq]; simp
    · rw [hcoord_x d hd]; exact le_trans zero_le_one (hπ_pos d hd)
  -- Check genus-2 Weil count laws at `n = 1, 2, 3` and failure on the full tower.
  have hlaw_123 : ∀ n ∈ ({1, 2, 3} : Finset ℕ), ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧
      (K 0 1 : ℤ) = 2 ∧ (K 1 0 : ℤ) = 2 * (5 : ℤ) ^ n ∧
      (K 1 1 : ℤ) = 2 * ((5 : ℤ) ^ n + 1) - fiveQuartetTrace n := by
    intro n hn
    rw [exists_genusCountLaw_iff (by norm_num : (0 : ℤ) < 2)]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> decide
  have hnot_tower : ¬ (∀ n : ℕ, 1 ≤ n → ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧
      (K 0 1 : ℤ) = 2 ∧ (K 1 0 : ℤ) = 2 * (5 : ℤ) ^ n ∧
      (K 1 1 : ℤ) = 2 * ((5 : ℤ) ^ n + 1) - fiveQuartetTrace n) := by
    intro hall
    -- Via `unitary_of_abs_trace_le`, full tower count laws force unitarity!
    have hunit : ∀ i : Fin 4, ‖primeFiveQuartetDatum.β i‖ = 1 := by
      refine unitary_of_abs_trace_le primeFiveQuartetDatum fun n hn => ?_
      have hlev := (exists_genusCountLaw_iff (by norm_num : (0 : ℤ) < 2)).mp (hall n hn)
      have hr : ((fiveQuartetTrace n ^ 2 : ℤ) : ℝ) ≤ ((4 * (2 : ℤ) ^ 2 * (5 : ℤ) ^ n : ℤ) : ℝ) := by
        exact_mod_cast hlev
      push_cast at hr
      rw [← primeFiveQuartetDatum_powerSum_eq_trace, mul_pow] at hr
      have hsq5 : (primeFiveQuartetDatum.sqrtq ^ n) ^ 2 = (5 : ℝ) ^ n := by
        rw [← pow_mul, mul_comm, pow_mul, primeFiveQuartetDatum.sqrtq_sq]
        rfl
      rw [hsq5] at hr
      have h5n : (0 : ℝ) < (5 : ℝ) ^ n := by positivity
      have htr_sq : primeFiveQuartetDatum.trace n ^ 2 ≤ 16 :=
        le_of_mul_le_mul_left (by linarith : (5 : ℝ) ^ n * primeFiveQuartetDatum.trace n ^ 2 ≤ (5 : ℝ) ^ n * 16) h5n
      rw [Fintype.card_fin, abs_le]
      constructor <;> nlinarith
    exact primeFiveQuartetDatum_not_unitary hunit
  exact ⟨⟨Zℤ, hZ0, hZmap⟩, primeFiveQuartetDatum_im_ne_zero, primeFiveQuartetDatum_not_unitary,
    ⟨x, heff_x, hcoord_x 1 le_rfl ▸ hπ1, hcoord_x 2 (by decide) ▸ hπ2,
      hcoord_x 3 (by decide) ▸ hπ3, fun d hd => hcoord_x d hd ▸ hπ_pos d hd, fun k => by
        change ((∑ d ∈ (k : ℕ).divisors, (d : ℤ) * π d : ℤ) : ℝ) = primeFiveQuartetDatum.pointCount k
        rw [← hN_sum k k.pos, primeFiveQuartetDatum_pointCount_eq]⟩,
    hlaw_123, by decide, hnot_tower⟩

end GaloisForLFunctions.CountingHolography

end
