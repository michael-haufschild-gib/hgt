import GaloisForLFunctions.RHTower.MobiusSquareResidueGcdBound
import GaloisForLFunctions.HTGeometry.CenteredModularAbel
import GaloisForLFunctions.RHTower.DivisorCenteredHyperbola
import GaloisForLFunctions.RHTower.RoutePTwoPrimePacketTimeResponse

/-!
# Cancellation in the square-sampled centered divisor hyperbola

The quadratic interval estimate is summed over the actual sparse set of
moduli, using its cardinality in the weighted GCD bound. The quotient ramp
identity retains both the scaled modulus and the correction at the original
modulus. Exact square-root births then give a uniform finite estimate for
the entire centered hyperbola sampled at `floor(s²/q)`.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset HTGeometry

namespace RHTower

noncomputable def squareResidueIntervalGcdRow (q R : ℕ) : ℝ :=
  ∑ k ∈ Ioc 0 R, Real.sqrt ((Nat.gcd q k : ℝ) / q) / k

theorem sum_centeredModularRamp_square_prefix (N q : ℕ) :
    (∑ s ∈ range N, centeredModularRamp q (s ^ 2)) =
      (quadraticResiduePrefix N q - (N : ℝ) * ((q : ℝ) - 1) / 2) / q := by
  by_cases hq : q = 0
  · subst q
    simp [centeredModularRamp]
  unfold centeredModularRamp quadraticResiduePrefix
  rw [sum_sub_distrib, ← sum_div]
  simp only [sum_const, card_range, nsmul_eq_mul]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  field_simp [hqR]

private theorem interval_gcd_row_nonneg (q R : ℕ) :
    0 ≤ squareResidueIntervalGcdRow q R := by
  unfold squareResidueIntervalGcdRow
  exact sum_nonneg fun _ _ => by positivity

private theorem interval_gcd_row_mono (q : ℕ) {R T : ℕ} (hRT : R ≤ T) :
    squareResidueIntervalGcdRow q R ≤ squareResidueIntervalGcdRow q T := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1, (mem_Ioc.mp hk).2.trans hRT⟩
  · intro k _ _
    positivity

theorem abs_sum_centeredModularRamp_square_prefix_le_gcd
    {q R M N : ℕ} (hq : 0 < q) (hqR : q ≤ R) (hMN : M ≤ N) :
    |∑ s ∈ range M, centeredModularRamp q (s ^ 2)| ≤
      ((N : ℝ) + R) * (2 + Real.log R) * squareResidueIntervalGcdRow q R := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hlogq := Real.log_natCast_nonneg q
  have hlogR := Real.log_natCast_nonneg R
  have hlog : Real.log q ≤ Real.log R :=
    Real.log_le_log hqpos (by exact_mod_cast hqR)
  have hQ : ((M / q : ℕ) + 1 : ℝ) * q ≤ (N : ℝ) + R := by
    have hn : (M / q + 1) * q ≤ N + R := by
      rw [Nat.add_mul, one_mul]
      have := Nat.div_mul_le_self M q
      omega
    exact_mod_cast hn
  have hbase := abs_quadraticResiduePrefix_centered_le_gcd (q := q) M
  rw [sum_centeredModularRamp_square_prefix, abs_div, abs_of_pos hqpos]
  calc
    _ ≤ (((M / q : ℕ) + 1 : ℝ) * (q : ℝ) ^ 2 * (2 + Real.log q) *
        squareResidueIntervalGcdRow q q) / q :=
      div_le_div_of_nonneg_right hbase hqpos.le
    _ = (((M / q : ℕ) + 1 : ℝ) * q) * (2 + Real.log q) *
        squareResidueIntervalGcdRow q q := by field_simp [ne_of_gt hqpos]
    _ ≤ _ := by
      apply mul_le_mul
      · exact mul_le_mul hQ (by linarith) (by positivity) (by positivity)
      · exact interval_gcd_row_mono q hqR
      · exact interval_gcd_row_nonneg q q
      · positivity

theorem abs_sum_centeredModularRamp_square_Ico_le_gcd
    {q R L M N : ℕ} (hq : 0 < q) (hqR : q ≤ R)
    (hLM : L ≤ M) (hMN : M ≤ N) :
    |∑ s ∈ Ico L M, centeredModularRamp q (s ^ 2)| ≤
      2 * ((N : ℝ) + R) * (2 + Real.log R) * squareResidueIntervalGcdRow q R := by
  rw [sum_Ico_eq_sub _ hLM]
  calc
    _ ≤ |∑ s ∈ range M, centeredModularRamp q (s ^ 2)| +
        |∑ s ∈ range L, centeredModularRamp q (s ^ 2)| := abs_sub _ _
    _ ≤ ((N : ℝ) + R) * (2 + Real.log R) * squareResidueIntervalGcdRow q R +
        ((N : ℝ) + R) * (2 + Real.log R) * squareResidueIntervalGcdRow q R :=
      add_le_add (abs_sum_centeredModularRamp_square_prefix_le_gcd hq hqR hMN)
        (abs_sum_centeredModularRamp_square_prefix_le_gcd hq hqR (hLM.trans hMN))
    _ = _ := by ring

theorem sum_squareResidueIntervalGcdRow_le_card
    (S : Finset ℕ) (R : ℕ) (hS : S ⊆ Ioc 0 R) :
    (∑ q ∈ S, squareResidueIntervalGcdRow q R) ≤
      Real.sqrt (S.card : ℝ) * (1 + Real.log R) ^ 2 := by
  classical
  let w : ℕ → ℝ := fun q => if q ∈ S then 1 else 0
  have hw2 : (∑ q ∈ Ioc 0 R, (w q) ^ 2) = (S.card : ℝ) := by
    calc
      _ = ∑ q ∈ S, (w q) ^ 2 := by
        symm
        apply sum_subset hS
        intro q hq hqS
        simp [w, hqS]
      _ = ∑ _q ∈ S, (1 : ℝ) := by
        apply sum_congr rfl
        intro q hq
        simp [w, hq]
      _ = _ := by simp
  have hwrow : (∑ q ∈ Ioc 0 R, w q * squareResidueIntervalGcdRow q R) =
      ∑ q ∈ S, squareResidueIntervalGcdRow q R := by
    calc
      _ = ∑ q ∈ S, w q * squareResidueIntervalGcdRow q R := by
        symm
        apply sum_subset hS
        intro q hq hqS
        simp [w, hqS]
      _ = _ := by
        apply sum_congr rfl
        intro q hq
        simp [w, hq]
  have h := squareResidue_weighted_gcd_harmonic_le R w
  rw [hw2] at h
  calc
    _ = ∑ q ∈ Ioc 0 R, w q * squareResidueIntervalGcdRow q R := hwrow.symm
    _ = ∑ q ∈ Ioc 0 R, ∑ k ∈ Ioc 0 R,
        w q * Real.sqrt ((Nat.gcd q k : ℝ) / q) / k := by
      simp only [squareResidueIntervalGcdRow, mul_sum, mul_div_assoc]
    _ ≤ _ := h

/-- A moving interval at each retained modulus costs the square root of the support size. -/
theorem sum_abs_centeredModularRamp_square_Ico_le_card
    (S : Finset ℕ) (R N : ℕ) (L U : ℕ → ℕ) (hS : S ⊆ Ioc 0 R)
    (hLU : ∀ q ∈ S, L q ≤ U q) (hUN : ∀ q ∈ S, U q ≤ N) :
    (∑ q ∈ S, |∑ s ∈ Ico (L q) (U q), centeredModularRamp q (s ^ 2)|) ≤
      2 * ((N : ℝ) + R) * (2 + Real.log R) *
        Real.sqrt (S.card : ℝ) * (1 + Real.log R) ^ 2 := by
  have hlog := Real.log_natCast_nonneg R
  have hC : 0 ≤ 2 * ((N : ℝ) + R) * (2 + Real.log R) := by positivity
  calc
    _ ≤ ∑ q ∈ S,
        2 * ((N : ℝ) + R) * (2 + Real.log R) * squareResidueIntervalGcdRow q R := by
      apply sum_le_sum
      intro q hq
      have hqR := mem_Ioc.mp (hS hq)
      exact abs_sum_centeredModularRamp_square_Ico_le_gcd
        hqR.1 hqR.2 (hLU q hq) (hUN q hq)
    _ = (2 * ((N : ℝ) + R) * (2 + Real.log R)) *
        ∑ q ∈ S, squareResidueIntervalGcdRow q R := (mul_sum _ _ _).symm
    _ ≤ (2 * ((N : ℝ) + R) * (2 + Real.log R)) *
        (Real.sqrt (S.card : ℝ) * (1 + Real.log R) ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_squareResidueIntervalGcdRow_le_card S R hS) hC
    _ = _ := by ring

def squareSampledHyperbolaBirth (q d : ℕ) : ℕ := Nat.sqrt (q * d * d - 1) + 1

def squareSampledHyperbolaCutoff (N q : ℕ) : ℕ := Nat.sqrt ((N - 1) ^ 2 / q)

theorem squareSampledHyperbolaBirth_le_iff {q d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (s : ℕ) : squareSampledHyperbolaBirth q d ≤ s ↔ q * d * d ≤ s ^ 2 := by
  have hp : 0 < q * d * d := Nat.mul_pos (Nat.mul_pos hq hd) hd
  have hroot : s ≤ Nat.sqrt (q * d * d - 1) ↔ s * s ≤ q * d * d - 1 := Nat.le_sqrt
  unfold squareSampledHyperbolaBirth
  rw [pow_two]
  omega

/-- Exact square sampling, retaining the moving birth and the quotient correction. -/
theorem sum_centeredDivisorHyperbola_square_quotient_eq_birth_channels
    (N : ℕ) {q : ℕ} (hq : 0 < q) :
    (∑ s ∈ range N, centeredDivisorHyperbola (s ^ 2 / q)) =
      ∑ d ∈ Icc 1 (squareSampledHyperbolaCutoff N q),
        ∑ s ∈ Ico (squareSampledHyperbolaBirth q d) N,
          (centeredModularRamp (q * d) (s ^ 2) - centeredModularRamp q (s ^ 2) / d) := by
  have hrel (d s : ℕ) : d ≤ Nat.sqrt (s ^ 2 / q) ↔ q * d * d ≤ s ^ 2 := by
    rw [Nat.le_sqrt, Nat.le_div_iff_mul_le hq]
    simp only [Nat.mul_left_comm, Nat.mul_comm]
  have hfibre (s : ℕ) (hs : s ∈ range N) :
      Icc 1 (Nat.sqrt (s ^ 2 / q)) =
        (Icc 1 (squareSampledHyperbolaCutoff N q)).filter (fun d => q * d * d ≤ s ^ 2) := by
    have hsN : s ≤ N - 1 := by have := mem_range.mp hs; omega
    have hs2 : s ^ 2 ≤ (N - 1) ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hsN hsN
    have hup : Nat.sqrt (s ^ 2 / q) ≤ squareSampledHyperbolaCutoff N q :=
      Nat.sqrt_le_sqrt (Nat.div_le_div_right hs2)
    ext d
    simp only [mem_Icc, mem_filter]
    constructor
    · intro hd
      exact ⟨⟨hd.1, hd.2.trans hup⟩, (hrel d s).mp hd.2⟩
    · intro hd
      exact ⟨hd.1.1, (hrel d s).mpr hd.2⟩
  have htime (d : ℕ) (hd : 0 < d) :
      (range N).filter (fun s => q * d * d ≤ s ^ 2) =
        Ico (squareSampledHyperbolaBirth q d) N := by
    ext s
    simp only [mem_filter, mem_range, mem_Ico,
      squareSampledHyperbolaBirth_le_iff hq hd]
    omega
  unfold centeredDivisorHyperbola
  calc
    _ = ∑ s ∈ range N, ∑ d ∈ Icc 1 (squareSampledHyperbolaCutoff N q),
        if q * d * d ≤ s ^ 2 then centeredModularRamp d (s ^ 2 / q) else 0 := by
      apply sum_congr rfl
      intro s hs
      rw [hfibre s hs, sum_filter]
    _ = ∑ d ∈ Icc 1 (squareSampledHyperbolaCutoff N q), ∑ s ∈ range N,
        if q * d * d ≤ s ^ 2 then centeredModularRamp d (s ^ 2 / q) else 0 := by
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      have hdpos : 0 < d := by have := (mem_Icc.mp hd).1; omega
      rw [← sum_filter, htime d hdpos]
      apply sum_congr rfl
      intro s hs
      exact routeP_centeredModularRamp_quotient hq hdpos (s ^ 2)

/-- Uniform cancellation for the square-sampled centered hyperbola at every positive dilation. -/
theorem abs_sum_centeredDivisorHyperbola_square_quotient_le
    (N : ℕ) {q : ℕ} (hq : 0 < q) :
    |∑ s ∈ range N, centeredDivisorHyperbola (s ^ 2 / q)| ≤
      8 * ((N : ℝ) + (q * squareSampledHyperbolaCutoff N q : ℕ)) *
        Real.sqrt (squareSampledHyperbolaCutoff N q) *
          (1 + Real.log (q * squareSampledHyperbolaCutoff N q : ℕ)) ^ 4 := by
  classical
  let D := squareSampledHyperbolaCutoff N q
  let R := q * D
  let l : ℝ := 1 + Real.log R
  let B : ℝ := 2 * ((N : ℝ) + R) * (2 + Real.log R)
  let J := Icc 1 D
  let S := J.image (fun d => q * d)
  let H : ℝ := ∑ d ∈ J, (1 : ℝ) / d
  change _ ≤ 8 * ((N : ℝ) + R) * Real.sqrt D * l ^ 4
  have he := sum_centeredDivisorHyperbola_square_quotient_eq_birth_channels N hq
  change (∑ s ∈ range N, centeredDivisorHyperbola (s ^ 2 / q)) =
    ∑ d ∈ Icc 1 D, ∑ s ∈ Ico (squareSampledHyperbolaBirth q d) N,
      (centeredModularRamp (q * d) (s ^ 2) - centeredModularRamp q (s ^ 2) / d) at he
  by_cases hD0 : D = 0
  · rw [he, hD0]
    simp
  have hD1 : 1 ≤ D := by omega
  have hDR : D ≤ R := by
    simpa [R] using Nat.mul_le_mul_right D (show 1 ≤ q by omega)
  have hqR : q ≤ R := by simpa [R] using Nat.mul_le_mul_left q hD1
  have hlog := Real.log_natCast_nonneg R
  have hl : 1 ≤ l := by dsimp [l]; linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hH0 : 0 ≤ H := sum_nonneg fun _ _ => by positivity
  have hH : H ≤ l := by
    have hlogDR : Real.log D ≤ Real.log R :=
      Real.log_le_log (by exact_mod_cast (show 0 < D by omega)) (by exact_mod_cast hDR)
    have hh := Sieve.sum_Icc_one_div_le_one_add_log D
    dsimp [H, J, l]
    linarith
  have hsqrt : 1 ≤ Real.sqrt (D : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ D by exact_mod_cast hD1)
    simpa using h
  have hN : 1 ≤ N := by
    by_contra h
    have hN0 : N = 0 := by omega
    have hz : D = 0 := by simp [D, squareSampledHyperbolaCutoff, hN0]
    exact hD0 hz
  have hbirth (d : ℕ) (hd : d ∈ J) : squareSampledHyperbolaBirth q d ≤ N := by
    have hd' := mem_Icc.mp hd
    have hdpos : 0 < d := by omega
    have hdroot : d ≤ Nat.sqrt ((N - 1) ^ 2 / q) := hd'.2
    have hprod := (Nat.le_div_iff_mul_le hq).mp (Nat.le_sqrt.mp hdroot)
    have hsmall : q * d * d ≤ (N - 1) ^ 2 := by
      simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hprod
    have hb := (squareSampledHyperbolaBirth_le_iff hq hdpos (N - 1)).mpr hsmall
    omega
  have hS : S ⊆ Ioc 0 R := by
    intro r hr
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hr
    have hd' := mem_Icc.mp hd
    exact mem_Ioc.mpr ⟨Nat.mul_pos hq (by omega), Nat.mul_le_mul_left q hd'.2⟩
  have hcard : S.card ≤ D := by
    calc
      _ ≤ J.card := card_image_le
      _ = D := by simp [J]
  have hinj : Function.Injective (fun d : ℕ => q * d) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hq hab
  have hrows : (∑ d ∈ J, squareResidueIntervalGcdRow (q * d) R) ≤
      Real.sqrt D * l ^ 2 := by
    calc
      _ = ∑ r ∈ S, squareResidueIntervalGcdRow r R := by
        dsimp [S]
        rw [sum_image]
        intro a ha b hb hab
        exact hinj hab
      _ ≤ Real.sqrt (S.card : ℝ) * l ^ 2 :=
        sum_squareResidueIntervalGcdRow_le_card S R hS
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (by exact_mod_cast hcard)) (sq_nonneg l)
  have hsingle : squareResidueIntervalGcdRow q R ≤ l ^ 2 := by
    have hsub : ({q} : Finset ℕ) ⊆ Ioc 0 R := by
      intro r hr
      have hrq := mem_singleton.mp hr
      subst r
      exact mem_Ioc.mpr ⟨hq, hqR⟩
    have h := sum_squareResidueIntervalGcdRow_le_card {q} R hsub
    simpa [l] using h
  have hmain : (∑ d ∈ J,
      |∑ s ∈ Ico (squareSampledHyperbolaBirth q d) N,
        centeredModularRamp (q * d) (s ^ 2)|) ≤ B * Real.sqrt D * l ^ 2 := by
    calc
      _ ≤ ∑ d ∈ J, B * squareResidueIntervalGcdRow (q * d) R := by
        apply sum_le_sum
        intro d hd
        have hd' := mem_Icc.mp hd
        exact abs_sum_centeredModularRamp_square_Ico_le_gcd
          (Nat.mul_pos hq (by omega)) (Nat.mul_le_mul_left q hd'.2) (hbirth d hd) le_rfl
      _ = B * ∑ d ∈ J, squareResidueIntervalGcdRow (q * d) R := (mul_sum _ _ _).symm
      _ ≤ B * (Real.sqrt D * l ^ 2) := mul_le_mul_of_nonneg_left hrows hB
      _ = _ := by ring
  have hcorrection : (∑ d ∈ J,
      |∑ s ∈ Ico (squareSampledHyperbolaBirth q d) N,
        centeredModularRamp q (s ^ 2)| / d) ≤ B * H * l ^ 2 := by
    calc
      _ ≤ ∑ d ∈ J, (B * l ^ 2) / d := by
        apply sum_le_sum
        intro d hd
        have ht := abs_sum_centeredModularRamp_square_Ico_le_gcd
          hq hqR (hbirth d hd) (N := N) le_rfl
        have hb : |∑ s ∈ Ico (squareSampledHyperbolaBirth q d) N,
            centeredModularRamp q (s ^ 2)| ≤ B * l ^ 2 :=
          ht.trans (mul_le_mul_of_nonneg_left hsingle hB)
        exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg d)
      _ = B * H * l ^ 2 := by
        dsimp [H]
        simp only [div_eq_mul_inv, one_mul, mul_sum, sum_mul]
        apply sum_congr rfl
        intro d hd
        ring
  have hcombined : |∑ s ∈ range N, centeredDivisorHyperbola (s ^ 2 / q)| ≤
      B * (Real.sqrt D + H) * l ^ 2 := by
    rw [he]
    calc
      _ ≤ ∑ d ∈ J, |∑ s ∈ Ico (squareSampledHyperbolaBirth q d) N,
          (centeredModularRamp (q * d) (s ^ 2) - centeredModularRamp q (s ^ 2) / d)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ J,
          (|∑ s ∈ Ico (squareSampledHyperbolaBirth q d) N,
              centeredModularRamp (q * d) (s ^ 2)| +
            |∑ s ∈ Ico (squareSampledHyperbolaBirth q d) N,
              centeredModularRamp q (s ^ 2)| / d) := by
        apply sum_le_sum
        intro d hd
        have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
        rw [sum_sub_distrib, ← sum_div]
        have h := abs_sub
          (∑ s ∈ Ico (squareSampledHyperbolaBirth q d) N, centeredModularRamp (q * d) (s ^ 2))
          ((∑ s ∈ Ico (squareSampledHyperbolaBirth q d) N, centeredModularRamp q (s ^ 2)) / d)
        simpa only [abs_div, abs_of_pos hdR] using h
      _ ≤ B * Real.sqrt D * l ^ 2 + B * H * l ^ 2 := by
        rw [sum_add_distrib]
        exact add_le_add hmain hcorrection
      _ = _ := by ring
  have hrootH : Real.sqrt D + H ≤ Real.sqrt D * (2 + Real.log R) := by
    have hm := mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ l by linarith)
    dsimp [l] at hH hm
    nlinarith only [hH, hm]
  have hlogs : (2 + Real.log R) ^ 2 ≤ 4 * l ^ 2 := by
    dsimp [l]
    nlinarith [sq_nonneg (Real.log R)]
  calc
    _ ≤ B * (Real.sqrt D + H) * l ^ 2 := hcombined
    _ ≤ B * (Real.sqrt D * (2 + Real.log R)) * l ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrootH hB) (sq_nonneg l)
    _ = (2 * ((N : ℝ) + R) * Real.sqrt D * l ^ 2) * (2 + Real.log R) ^ 2 := by
      dsimp [B]
      ring
    _ ≤ (2 * ((N : ℝ) + R) * Real.sqrt D * l ^ 2) * (4 * l ^ 2) :=
      mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = _ := by ring

end RHTower
