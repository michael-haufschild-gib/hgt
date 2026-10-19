import GaloisForLFunctions.RHTower.QuasiRHDilationCovarianceAbscissa
import GaloisForLFunctions.RHTower.QuasiRHPowerMeshSquareSampleAndObserverJetAbscissaLaw

/-!
# Mean-square exponents on integer-power meshes

Finite-window averaging survives the map `j ↦ j^m`: its power-gap saving is divided by
`m`, but remains positive. Thus the sharp cumulative square exponent on this mesh is
`1 + 2*m*(Θ - 1/2)`. On the sixth and fourth power meshes the literal high-dilation
covariance retains the exact small-quotient range `q < j`.
-/

open Real Filter Topology Finset
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.RHTower

/-- Taking positive integer powers preserves a positive power saving in sampling gaps. -/
theorem exists_powerGap_pow_samples {A : Set ℕ} {m N₀ : ℕ} {θ : ℝ}
    (hm : 1 ≤ m) (hθ : 0 ≤ θ)
    (hsamples : ∀ j : ℕ, N₀ ≤ j → ∃ k ∈ A,
      k ≤ j ∧ (j : ℝ) - k ≤ (j : ℝ) ^ θ) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A,
      k ^ m ≤ n ∧ (n : ℝ) - ((k ^ m : ℕ) : ℝ) ≤
        (2 * (m : ℝ) * 2 ^ (m - 1)) * (n : ℝ) ^ (1 - (1 - θ) / m) := by
  let L := max N₀ 1
  refine ⟨L ^ m, fun n hn => ?_⟩
  have hL : 1 ≤ L := le_max_right _ _
  have hn1 : 1 ≤ n := (hL.trans (le_self_pow hL (by omega : m ≠ 0))).trans hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let x : ℝ := (n : ℝ) ^ (1 / (m : ℝ))
  have hx1 : 1 ≤ x := Real.one_le_rpow hn1R (by positivity)
  have hx0 : 0 < x := by linarith
  have hxm : x ^ m = n := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    rw [show 1 / (m : ℝ) * m = 1 by field_simp, Real.rpow_one]
  let j : ℕ := ⌊x⌋₊
  have hjx : (j : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxj : x < (j : ℝ) + 1 := Nat.lt_floor_add_one x
  have hjm : (j : ℝ) ^ m ≤ n := by
    rw [← hxm]
    exact pow_le_pow_left₀ (Nat.cast_nonneg j) hjx m
  have hnj : (n : ℝ) < ((j : ℝ) + 1) ^ m := by
    rw [← hxm]
    exact pow_lt_pow_left₀ hxj hx0.le (by omega)
  have hLj : L ≤ j := by
    by_contra h
    have hjL : j + 1 ≤ L := by omega
    have hp : ((j : ℝ) + 1) ^ m ≤ (L : ℝ) ^ m :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hjL) m
    have hLn : (L : ℝ) ^ m ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨k, hkA, hkj, hgap⟩ := hsamples j ((le_max_left _ _).trans hLj)
  have hkjR : (k : ℝ) ≤ j := by exact_mod_cast hkj
  have hkj1 : (k : ℝ) ≤ j + 1 := by linarith
  have hkn : k ^ m ≤ n := by
    exact_mod_cast (pow_le_pow_left₀ (Nat.cast_nonneg k) hkjR m).trans hjm
  have hθmono : (j : ℝ) ^ θ ≤ x ^ θ :=
    Real.rpow_le_rpow (Nat.cast_nonneg j) hjx hθ
  have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx1 hθ
  have hstep : (j : ℝ) + 1 - k ≤ 2 * x ^ θ := by linarith
  have hpow : ((j : ℝ) + 1) ^ (m - 1) ≤ 2 ^ (m - 1) * x ^ (m - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hdiff : ((j : ℝ) + 1) ^ m - (k : ℝ) ^ m ≤
      ((j : ℝ) + 1 - k) * m * ((j : ℝ) + 1) ^ (m - 1) := by
    have h := _root_.abs_pow_sub_pow_le (a := (j : ℝ) + 1) (b := (k : ℝ)) (n := m)
    have hnonneg : 0 ≤ ((j : ℝ) + 1) ^ m - (k : ℝ) ^ m :=
      sub_nonneg.mpr (pow_le_pow_left₀ (Nat.cast_nonneg k) hkj1 m)
    simpa only [abs_of_nonneg hnonneg, abs_of_nonneg (sub_nonneg.mpr hkj1),
      abs_of_nonneg (show (0 : ℝ) ≤ j + 1 by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ k by positivity),
      max_eq_left hkj1] using h
  have hprod : x ^ (m - 1) * x ^ θ = (n : ℝ) ^ (1 - (1 - θ) / m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
    dsimp [x]
    rw [← Real.rpow_mul hn0.le]
    congr 1
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm, Nat.cast_one]
    rw [hcast]
    field_simp
    ring
  refine ⟨k, hkA, hkn, ?_⟩
  push_cast
  calc
    (n : ℝ) - (k : ℝ) ^ m ≤ ((j : ℝ) + 1) ^ m - (k : ℝ) ^ m := by linarith
    _ ≤ ((j : ℝ) + 1 - k) * m * ((j : ℝ) + 1) ^ (m - 1) := hdiff
    _ ≤ (2 * x ^ θ) * m * (2 ^ (m - 1) * x ^ (m - 1)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hstep hm0.le) hpow
        (by positivity) (by positivity)
    _ = (2 * (m : ℝ) * 2 ^ (m - 1)) * (n : ℝ) ^ (1 - (1 - θ) / m) := by
      rw [← hprod]
      ring

/-- Literal cumulative square energy on the `m`-th power mesh. -/
noncomputable def mobiusDivisorAbelPowerMeshEnergy (m J : ℕ) : ℝ :=
  ∑ j ∈ Icc 2 J, (mobiusDivisorSquareRootAbelMoment (j ^ m) / ((j ^ m : ℕ) : ℝ)) ^ 2

/-- Sparse cumulative energy retains the full averaging saving in the mesh index. -/
theorem zetaZeroAbscissa_le_of_mobiusDivisorAbelPowerMeshEnergy_le_rpow
    {m : ℕ} {C r : ℝ} (hm : 1 ≤ m) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hE : ∀ J : ℕ, 2 ≤ J → mobiusDivisorAbelPowerMeshEnergy m J ≤ C * (J : ℝ) ^ r) :
    zetaZeroAbscissa ≤ 1 / 2 + (r - 1) / (2 * m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let δ := min ((m : ℝ) * ε) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ (m : ℝ) * ε := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  let θ := 1 - δ
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  obtain ⟨D, hD, N₀, hsamples⟩ := exists_powerGap_samples_of_sum_sq_le_rpow
    hC hr hθ hθ1 hE
  let c := (r - θ) / (2 * m)
  have hc : 0 ≤ c := div_nonneg (by linarith) (by positivity)
  let A : Set ℕ := {k | 2 ≤ k ∧
    |mobiusDivisorSquareRootAbelMoment (k ^ m) / ((k ^ m : ℕ) : ℝ)| ≤
      D * (k : ℝ) ^ ((r - θ) / 2)}
  obtain ⟨N₁, hgap⟩ := exists_powerGap_pow_samples (A := A) hm hθ.le
    (fun j hj => by
      obtain ⟨k, hk2, hkj, hdist, hkbound⟩ := hsamples j hj
      exact ⟨k, ⟨hk2, hkbound⟩, hkj, hdist⟩)
  have hstrip := zetaZeroAbscissa_le_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    (A := (fun k : ℕ => k ^ m) '' A) (c := c)
    (K := 2 * (m : ℝ) * 2 ^ (m - 1)) (N₀ := N₁) hD
    (show 0 < (1 - θ) / (m : ℝ) by dsimp [θ]; positivity) (by positivity)
    (fun N hN _ => by
      obtain ⟨k, hk, rfl⟩ := hN
      have hpow : ((k ^ m : ℕ) : ℝ) ^ c = (k : ℝ) ^ ((r - θ) / 2) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
        congr 1
        dsimp [c]
        field_simp
      rw [hpow]
      exact (le_abs_self _).trans (hk.2.trans (by linarith)))
    (fun n hn => by
      obtain ⟨k, hk, hkn, hdist⟩ := hgap n hn
      exact ⟨k ^ m, ⟨k, hk, rfl⟩, hkn, hdist⟩)
  rw [max_eq_right hc] at hstrip
  have heq : c = (r - 1) / (2 * m) + δ / (2 * m) := by
    dsimp [c, θ]
    ring
  have hsmall : δ / (2 * m) ≤ ε := (div_le_iff₀ (by positivity : 0 < 2 * (m : ℝ))).mpr
    (by nlinarith)
  rw [heq] at hstrip
  linarith

/-- The intrinsic zero abscissa supplies every larger mesh-energy exponent. -/
theorem exists_mobiusDivisorAbelPowerMeshEnergy_le_rpow_zetaZeroAbscissa
    {m : ℕ} (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℕ, 2 ≤ J →
      mobiusDivisorAbelPowerMeshEnergy m J ≤
        C * (J : ℝ) ^ (1 + 2 * m * (zetaZeroAbscissa - 1 / 2) + ε) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨C, hC, hbound⟩ :=
    exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa
      (ε / (2 * m)) (by positivity)
  have hf : ∀ j : ℕ, 2 ≤ j →
      |mobiusDivisorSquareRootAbelMoment (j ^ m) / ((j ^ m : ℕ) : ℝ)| ≤
        C * (j : ℝ) ^ ((m : ℝ) * (zetaZeroAbscissa - 1 / 2) + ε / 2) := by
    intro j hj
    have hjm : 2 ≤ j ^ m := hj.trans (le_self_pow (by omega : 1 ≤ j) (by omega : m ≠ 0))
    calc
      _ ≤ C * ((j ^ m : ℕ) : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / (2 * m)) := hbound _ hjm
      _ = _ := by
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg j)]
        congr 2
        field_simp
  refine ⟨C ^ 2, sq_nonneg _, fun J hJ => ?_⟩
  have h := sum_sq_le_rpow_of_abs_le_rpow hC
    (show 0 ≤ (m : ℝ) * (zetaZeroAbscissa - 1 / 2) + ε / 2 by
      have := half_le_zetaZeroAbscissa
      positivity) hf hJ
  simpa only [mobiusDivisorAbelPowerMeshEnergy,
    show 2 * ((m : ℝ) * (zetaZeroAbscissa - 1 / 2) + ε / 2) + 1 =
      1 + 2 * m * (zetaZeroAbscissa - 1 / 2) + ε by ring] using h

/-- Exact mean-square exponent on every positive integer-power mesh. -/
theorem powerMeshEnergy_exponent_eq_sInf {m : ℕ} (hm : 1 ≤ m) :
    1 + 2 * m * (zetaZeroAbscissa - 1 / 2) = sInf {r : ℝ | 1 ≤ r ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℕ, 2 ≤ J →
        mobiusDivisorAbelPowerMeshEnergy m J ≤ C * (J : ℝ) ^ r} := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let a := 1 + 2 * m * (zetaZeroAbscissa - 1 / 2)
  let S : Set ℝ := {r | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℕ, 2 ≤ J →
    mobiusDivisorAbelPowerMeshEnergy m J ≤ C * (J : ℝ) ^ r}
  have hmem : ∀ ε : ℝ, 0 < ε → a + ε ∈ S := by
    intro ε hε
    refine ⟨?_, exists_mobiusDivisorAbelPowerMeshEnergy_le_rpow_zetaZeroAbscissa hm ε hε⟩
    dsimp [a]
    nlinarith [half_le_zetaZeroAbscissa]
  have hne : S.Nonempty := ⟨a + 1, hmem 1 (by norm_num)⟩
  have hbdd : BddBelow S := ⟨1, fun _ hr => hr.1⟩
  change a = sInf S
  apply le_antisymm
  · refine le_csInf hne fun r hr => ?_
    obtain ⟨hr, C, hC, hE⟩ := hr
    have hstrip := zetaZeroAbscissa_le_of_mobiusDivisorAbelPowerMeshEnergy_le_rpow hm hC hr hE
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (m : ℝ))).mp
      (show zetaZeroAbscissa - 1 / 2 ≤ (r - 1) / (2 * m) by linarith)
    dsimp [a]
    nlinarith
  · exact le_of_forall_pos_le_add fun ε hε => csInf_le hbdd (hmem ε hε)

/-- Endpoint strip criterion through the literal mesh energy. -/
theorem zetaZeroAbscissa_le_iff_mobiusDivisorAbelPowerMeshEnergy_subpower
    {m : ℕ} {b : ℝ} (hm : 1 ≤ m) (hb : 1 / 2 ≤ b) :
    zetaZeroAbscissa ≤ b ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ J : ℕ, 2 ≤ J → mobiusDivisorAbelPowerMeshEnergy m J ≤
        C * (J : ℝ) ^ (1 + 2 * m * (b - 1 / 2) + ε) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  constructor
  · intro hstrip ε hε
    obtain ⟨C, hC, hE⟩ := exists_mobiusDivisorAbelPowerMeshEnergy_le_rpow_zetaZeroAbscissa hm ε hε
    refine ⟨C, hC, fun J hJ => (hE J hJ).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (by omega : 1 ≤ J)) (by nlinarith)) hC
  · intro hE
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, hC, hbound⟩ := hE (2 * m * ε) (by positivity)
    have hr : 1 ≤ 1 + 2 * m * (b - 1 / 2) + 2 * m * ε := by nlinarith
    have h := zetaZeroAbscissa_le_of_mobiusDivisorAbelPowerMeshEnergy_le_rpow hm hC hr hbound
    have heq : (1 + 2 * m * (b - 1 / 2) + 2 * m * ε - 1) / (2 * m) = b - 1 / 2 + ε := by
      field_simp
      ring
    rw [heq] at h
    linarith

/-- Ordered high-dilation covariance on an exact integer-power mesh. -/
noncomputable def mobiusDivisorDilationPowerMeshCovariance (m J : ℕ) : ℝ :=
  ∑ j ∈ Icc 2 J, mobiusDivisorDilationTailCovariance (j ^ m) (j ^ (m - 1))

/-- Tail square energy on the same exact mesh and cutoff. -/
noncomputable def mobiusDivisorDilationPowerMeshTailEnergy (m J : ℕ) : ℝ :=
  ∑ j ∈ Icc 2 J,
    (mobiusDivisorDilationTail (j ^ m) (j ^ (m - 1)) / ((j ^ m : ℕ) : ℝ)) ^ 2

/-- Sampling does not change the linear budget for the literal diagonal. -/
theorem mobiusDivisorDilationPowerMesh_diagonal_bounds {m : ℕ} (hm : 1 ≤ m) (J : ℕ) :
    0 ≤ mobiusDivisorDilationPowerMeshTailEnergy m J - mobiusDivisorDilationPowerMeshCovariance m J ∧
    mobiusDivisorDilationPowerMeshTailEnergy m J - mobiusDivisorDilationPowerMeshCovariance m J ≤
      (9 / 25 : ℝ) * J := by
  have hid : mobiusDivisorDilationPowerMeshTailEnergy m J - mobiusDivisorDilationPowerMeshCovariance m J =
      ∑ j ∈ Icc 2 J, mobiusDivisorDilationTailDiagonal (j ^ m) (j ^ (m - 1)) := by
    unfold mobiusDivisorDilationPowerMeshTailEnergy mobiusDivisorDilationPowerMeshCovariance
    simp_rw [mobiusDivisorDilationTail_sq_eq_diagonal_add_covariance]
    rw [sum_add_distrib, add_sub_cancel_right]
  have hM (j : ℕ) (hj : j ∈ Icc 2 J) : 1 ≤ j ^ m := by
    have hj1 : 1 ≤ j := by have := (mem_Icc.mp hj).1; omega
    exact hj1.trans (le_self_pow hj1 (by omega : m ≠ 0))
  rw [hid]
  constructor
  · exact sum_nonneg fun j hj => (mobiusDivisorDilationTailDiagonal_bounds (hM j hj) _).1
  · calc
      _ ≤ ∑ _j ∈ Icc 2 J, (9 / 25 : ℝ) := sum_le_sum fun j hj =>
        (mobiusDivisorDilationTailDiagonal_bounds (hM j hj) _).2
      _ = ((Icc 2 J).card : ℝ) * (9 / 25 : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        have hcard : ((Icc 2 J).card : ℝ) ≤ J := by
          exact_mod_cast (show (Icc 2 J).card ≤ J by rw [Nat.card_Icc]; omega)
        linarith

/-- The sampled tail energy is a square sum with the exact quotient range `q < j`. -/
theorem mobiusDivisorDilationPowerMeshTailEnergy_eq_smallQuotient_energy
    {m : ℕ} (hm : 2 ≤ m) (J : ℕ) :
    mobiusDivisorDilationPowerMeshTailEnergy m J =
      ∑ j ∈ Icc 2 J, ((∑ q ∈ Icc 1 (j - 1), primeFreeDivisorDefect q *
        mobiusHighDilationClippedAbelKernel (j ^ m) (j ^ (m - 1)) q) / ((j ^ m : ℕ) : ℝ)) ^ 2 := by
  unfold mobiusDivisorDilationPowerMeshTailEnergy
  apply sum_congr rfl
  intro j hj
  rw [mobiusDivisorDilationTail_pow_eq_Icc_pred_smallQuotient hm
    (by have := (mem_Icc.mp hj).1; omega)]

/-- On even meshes the paid head and diagonal have exponent `m-1`. -/
theorem mobiusDivisorDilationPowerMeshCovariance_comparison
    {s J : ℕ} (hs : 1 ≤ s) (hJ : 2 ≤ J) :
    mobiusDivisorAbelPowerMeshEnergy (2 * s) J ≤
      2 * mobiusDivisorDilationPowerMeshCovariance (2 * s) J +
        (36 / 25 : ℝ) * (J : ℝ) ^ (2 * s - 1) ∧
    mobiusDivisorDilationPowerMeshCovariance (2 * s) J ≤
      2 * mobiusDivisorAbelPowerMeshEnergy (2 * s) J +
        (18 / 25 : ℝ) * (J : ℝ) ^ (2 * s - 1) := by
  have hhead : ∑ j ∈ Icc 2 J,
      (mobiusDivisorDilationHead (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ)) ^ 2 ≤
        (9 / 25 : ℝ) * (J : ℝ) ^ (2 * s - 1) := by
    have h := sum_sq_le_rpow_of_abs_le_rpow (by norm_num : (0 : ℝ) ≤ 3 / 5)
      (show (0 : ℝ) ≤ ((s - 1 : ℕ) : ℝ) by positivity)
      (fun j (hj : 2 ≤ j) => by
        simpa only [Real.rpow_natCast] using
          abs_mobiusDivisorDilationHead_even_pow_div_le hs (by omega : 1 ≤ j)) hJ
    have heq : 2 * ((s - 1 : ℕ) : ℝ) + 1 = ((2 * s - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hs, Nat.cast_sub (by omega : 1 ≤ 2 * s)]
      push_cast
      ring
    simpa only [heq, Real.rpow_natCast, show (3 / 5 : ℝ) ^ 2 = 9 / 25 by norm_num] using h
  have hpoint (j : ℕ) :
      (mobiusDivisorSquareRootAbelMoment (j ^ (2 * s)) / ((j ^ (2 * s) : ℕ) : ℝ)) ^ 2 ≤
        2 * (mobiusDivisorDilationTail (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ)) ^ 2 +
        2 * (mobiusDivisorDilationHead (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ)) ^ 2 ∧
      (mobiusDivisorDilationTail (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ)) ^ 2 ≤
        2 * (mobiusDivisorSquareRootAbelMoment (j ^ (2 * s)) / ((j ^ (2 * s) : ℕ) : ℝ)) ^ 2 +
        2 * (mobiusDivisorDilationHead (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ)) ^ 2 := by
    have hid : mobiusDivisorSquareRootAbelMoment (j ^ (2 * s)) / ((j ^ (2 * s) : ℕ) : ℝ) =
        mobiusDivisorDilationHead (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ) +
        mobiusDivisorDilationTail (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ) := by
      rw [mobiusDivisorSquareRootAbelMoment_eq_dilationHead_add_dilationTail, add_div]
    rw [hid]
    constructor <;> nlinarith [sq_nonneg
      (mobiusDivisorDilationHead (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ) -
        mobiusDivisorDilationTail (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ)),
      sq_nonneg (2 * (mobiusDivisorDilationHead (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ)) +
        mobiusDivisorDilationTail (j ^ (2 * s)) (j ^ (2 * s - 1)) / ((j ^ (2 * s) : ℕ) : ℝ))]
  have hU := sum_le_sum (s := Icc 2 J) (fun j _ => (hpoint j).1)
  have hT := sum_le_sum (s := Icc 2 J) (fun j _ => (hpoint j).2)
  simp only [sum_add_distrib, ← mul_sum] at hU hT
  change mobiusDivisorAbelPowerMeshEnergy (2 * s) J ≤
    2 * mobiusDivisorDilationPowerMeshTailEnergy (2 * s) J + _ at hU
  change mobiusDivisorDilationPowerMeshTailEnergy (2 * s) J ≤
    2 * mobiusDivisorAbelPowerMeshEnergy (2 * s) J + _ at hT
  have hdiag := mobiusDivisorDilationPowerMesh_diagonal_bounds (by omega : 1 ≤ 2 * s) J
  have hlinear : (J : ℝ) ≤ (J : ℝ) ^ (2 * s - 1) := by
    have hp := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (by omega : 1 ≤ J) : (1 : ℝ) ≤ J)
      (by exact_mod_cast (by omega : 1 ≤ 2 * s - 1) : (1 : ℝ) ≤ ((2 * s - 1 : ℕ) : ℝ))
    simpa only [Real.rpow_one, Real.rpow_natCast] using hp
  constructor <;> linarith

/-- Exact endpoint criterion for signed covariance on any even power mesh. -/
theorem zetaZeroAbscissa_le_iff_mobiusDivisorDilationPowerMeshCovariance_subpower
    {s : ℕ} {b : ℝ} (hs : 1 ≤ s) (hb : 1 / 2 ≤ b)
    (hbudget : ((2 * s - 1 : ℕ) : ℝ) ≤ 1 + 2 * (2 * s : ℕ) * (b - 1 / 2)) :
    zetaZeroAbscissa ≤ b ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ J : ℕ, 2 ≤ J → mobiusDivisorDilationPowerMeshCovariance (2 * s) J ≤
        C * (J : ℝ) ^ (1 + 2 * (2 * s : ℕ) * (b - 1 / 2) + ε) := by
  rw [zetaZeroAbscissa_le_iff_mobiusDivisorAbelPowerMeshEnergy_subpower (by omega : 1 ≤ 2 * s) hb]
  constructor
  · intro hE ε hε
    obtain ⟨C, hC, hbound⟩ := hE ε hε
    refine ⟨2 * C + 18 / 25, by positivity, fun J hJ => ?_⟩
    have hp : (J : ℝ) ^ (2 * s - 1) ≤
        (J : ℝ) ^ (1 + 2 * (2 * s : ℕ) * (b - 1 / 2) + ε) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ J)) (by linarith)
    have h := (mobiusDivisorDilationPowerMeshCovariance_comparison hs hJ).2
    have hEJ := hbound J hJ
    nlinarith
  · intro hV ε hε
    obtain ⟨C, hC, hbound⟩ := hV ε hε
    refine ⟨2 * C + 36 / 25, by positivity, fun J hJ => ?_⟩
    have hp : (J : ℝ) ^ (2 * s - 1) ≤
        (J : ℝ) ^ (1 + 2 * (2 * s : ℕ) * (b - 1 / 2) + ε) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ J)) (by linarith)
    have h := (mobiusDivisorDilationPowerMeshCovariance_comparison hs hJ).1
    have hVJ := hbound J hJ
    nlinarith

/-- The sixth-power mesh reduces the `5/6` strip to an averaged fifth-power budget. -/
theorem xi_zero_five_sixths_strip_iff_powerMeshCovariance_subpower :
    (∀ ρ : ℂ, xi ρ = 0 → (1 / 6 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 5 / 6) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℕ, 2 ≤ J →
        mobiusDivisorDilationPowerMeshCovariance 6 J ≤ C * (J : ℝ) ^ (5 + ε) := by
  rw [← zetaZeroAbscissa_le_five_sixths_iff_xi_zero_mem_strip]
  convert zetaZeroAbscissa_le_iff_mobiusDivisorDilationPowerMeshCovariance_subpower
    (s := 3) (b := 5 / 6) (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num

/-- The fourth-power mesh reduces the `3/4` strip to an averaged cubic budget. -/
theorem xi_zero_three_quarters_strip_iff_powerMeshCovariance_subpower :
    (∀ ρ : ℂ, xi ρ = 0 → (1 / 4 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3 / 4) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℕ, 2 ≤ J →
        mobiusDivisorDilationPowerMeshCovariance 4 J ≤ C * (J : ℝ) ^ (3 + ε) := by
  rw [← zetaZeroAbscissa_le_three_quarters_iff_xi_zero_mem_strip]
  convert zetaZeroAbscissa_le_iff_mobiusDivisorDilationPowerMeshCovariance_subpower
    (s := 2) (b := 3 / 4) (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num

end RHTower
