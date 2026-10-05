import GaloisForLFunctions.RHTower.BaezDuarteSmoothZeroDual
import GaloisForLFunctions.RHTower.FractionalPartZeta


/-!
# Burnol's lower bound for the Báez-Duarte distances

Let `d_N` be the distance in the discrete Nyman–Beurling space from the target to the span of the
first `N` generators (`bdDistDiscrete`).

* `eventually_le_bdDistDiscrete_sq_mul_log_of_zeros`: for every finite set `Z` of zeros of `ζ` with
  `Re ρ = ½`, `Im ρ > 0`,

  `liminf_{N→∞} d_N² log N ≥ Σ_{ρ ∈ Z} 2/|ρ|²`.

* `eventually_le_bdDistDiscrete_sq_mul_log_of_zero`: `liminf d_N² log N ≥ 2/|ρ|²` for every zero
  on the critical line.

**Proof.**  Take `Y = N^{1+η}`, the smoothed duals `Re a_ρ`, `a_ρ(k) = k^{−ρ} ψ(k/Y)`
(`BaezDuarteSmoothZeroDual`), and the combination `Σ_ρ λ_ρ Re a_ρ` with `λ_ρ = |ρ|^{−2}/S`,
`S = Σ |ρ|^{−2}`.  Its energy is `Σ λ_ρ² (|ρ|²/2) log Y + O(1) = log Y/(2S) + O(1)`, because the
duals of distinct zeros are asymptotically orthogonal.  Its defects against the first `N` moduli
are `O(N^A Y^{−A}) = O(N^{−4})` for `A = 4/η`, and an exact Möbius correction over the divisor
lattice removes them at bounded energy cost.  The dual-sequence inequality
`1 ≤ d_N² · energy` then gives `1 ≤ d_N²((1 + η)²/(2S) log N + K)`, and `η → 0`.
-/

open Complex MeasureTheory Set Filter Topology ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Energies and defects of combinations -/

theorem bdDualEnergy_add_le (f g : ℕ → ℝ) (K : ℕ) {t : ℝ} (ht : 0 < t) :
    bdDualEnergy (fun k => f k + g k) K ≤
      (1 + t) * bdDualEnergy f K + (1 + 1 / t) * bdDualEnergy g K := by
  unfold bdDualEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  set x := f (n + 1) - f (n + 2)
  set y := g (n + 1) - g (n + 2)
  have hw : 0 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have hxy : (f (n + 1) + g (n + 1) - (f (n + 2) + g (n + 2))) = x + y := by ring
  have hsq : (x + y) ^ 2 ≤ (1 + t) * x ^ 2 + (1 + 1 / t) * y ^ 2 := by
    have h := sq_nonneg (t * x - y)
    have : 2 * x * y ≤ t * x ^ 2 + y ^ 2 / t := by
      rw [← mul_le_mul_iff_of_pos_left ht]
      field_simp
      nlinarith [h]
    have e : (1 + 1 / t) * y ^ 2 = y ^ 2 + y ^ 2 / t := by ring
    nlinarith [this, e]
  rw [hxy]
  calc ((n : ℝ) + 1) * ((n : ℝ) + 2) * (x + y) ^ 2
      ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((1 + t) * x ^ 2 + (1 + 1 / t) * y ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hw
    _ = _ := by ring

theorem bdDualEnergy_sum_eq {ι : Type*} (s : Finset ι) (c : ι → ℝ) (A : ι → ℕ → ℝ) (K : ℕ) :
    bdDualEnergy (fun k => ∑ i ∈ s, c i * A i k) K =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * bdDualBilin (A i) (A j) K := by
  unfold bdDualEnergy bdDualBilin
  have hΔ : ∀ n : ℕ, (∑ i ∈ s, c i * A i (n + 1)) - (∑ i ∈ s, c i * A i (n + 2)) =
      ∑ i ∈ s, c i * (A i (n + 1) - A i (n + 2)) := by
    intro n
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hΔ, sq, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem bdModDefect_sum_mul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℕ → ℂ) (K m : ℕ) :
    bdModDefect (fun k => ∑ i ∈ s, c i * f i k) K m = ∑ i ∈ s, c i * bdModDefect (f i) K m := by
  unfold bdModDefect
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.Icc 1 K), Finset.mul_sum]
  simp_rw [Finset.mul_sum, mul_sub]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ## Burnol's lower bound -/

/-- **The energy bound for finitely many critical zeros.**  Let `Z` be a nonempty finite set of
zeros of `ζ` with `Re ρ = ½`, `Im ρ > 0`, and `S = Σ_{ρ ∈ Z} 1/|ρ|²`.  For every `η > 0` there is
`K₁` with `1 ≤ d_N² ((1 + η)²/(2S) log N + K₁)` for all `N ≥ 2`.  The dual is
`Σ_ρ λ_ρ Re(k^{−ρ}) ψ(k/N^{1+η})` with `λ_ρ = |ρ|^{−2}/S`, corrected over the divisor lattice;
the duals of distinct zeros are asymptotically orthogonal. -/
theorem exists_one_le_bdDistDiscrete_sq_mul_log_of_zeros {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ 0 < ρ.im) (hZne : Z.Nonempty) {η : ℝ}
    (hη : 0 < η) :
    ∃ K₁ : ℝ, ∀ N : ℕ, 2 ≤ N →
      1 ≤ bdDistDiscrete N ^ 2 *
        ((1 + η) ^ 2 / (2 * ∑ ρ ∈ Z, 1 / ‖ρ‖ ^ 2) * Real.log N + K₁) := by
  obtain ⟨ν, hνsmooth, hνnn, hνsupp, hνmass⟩ := SmoothExistence
  have hν : IsHalfTwoBump ν := ⟨hνsmooth, hνsupp⟩
  have νpos : ∀ x > 0, 0 ≤ ν x := fun x _ => hνnn x
  have mass_one : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; norm_num
  have hε1 : ε < 1 := by rw [hεdef]; norm_num
  set A : ℝ := 4 / η with hAdef
  have hA0 : 0 < A := by positivity
  -- the constants of each zero and each pair
  have hdef : ∀ ρ ∈ Z, ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y → ∀ K : ℕ, 3 * Y ≤ K → ∀ m : ℕ,
      1 ≤ m → ‖bdModDefect (zeroSmoothDual ν ε ρ Y) K m‖ ≤ 2 * C * (m : ℝ) ^ A * Y ^ (-A) :=
    fun ρ hρ => exists_norm_bdModDefect_zeroSmoothDual_le hν νpos mass_one hε0 hε1 (hZ ρ hρ).1
      (by rw [(hZ ρ hρ).2.1]; norm_num) (by rw [(hZ ρ hρ).2.1]; norm_num) hA0
  choose! Cf hCf0 hCf using hdef
  have hpair : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ∃ K₃ : ℝ, ∀ Y : ℝ, 1 ≤ Y → ∀ K : ℕ,
      bdDualBilin (fun k => (zeroSmoothDual ν ε ρ Y k).re)
          (fun k => (zeroSmoothDual ν ε ρ' Y k).re) K ≤
        (if ρ = ρ' then ‖ρ‖ ^ 2 / 2 * Real.log Y else 0) + K₃ := by
    intro ρ hρ ρ' hρ'
    by_cases h : ρ = ρ'
    · subst h
      obtain ⟨K₀, hK₀⟩ := exists_bdDualEnergy_re_zeroSmoothDual_le hν νpos mass_one hε0 hε1
        (hZ ρ hρ).2.1 (hZ ρ hρ).2.2.ne'
      exact ⟨K₀, fun Y hY K => by
        rw [if_pos rfl, ← bdDualEnergy_eq_bdDualBilin]; exact hK₀ Y hY K⟩
    · obtain ⟨K₃, hK₃⟩ := exists_bdDualBilin_zeroSmoothDual_le_of_ne hν νpos mass_one hε0 hε1
        (hZ ρ hρ).2.1 (hZ ρ' hρ').2.1 (hZ ρ hρ).2.2 (hZ ρ' hρ').2.2 h
      exact ⟨K₃, fun Y hY K => by rw [if_neg h, zero_add]; exact hK₃ Y hY K⟩
  choose! Kf hKf using hpair
  obtain ⟨c₁, _, hc₁, hbelow⟩ := Smooth1Properties_below hν.2 mass_one
  -- the weights
  have hnorm0 : ∀ ρ ∈ Z, 0 < ‖ρ‖ := fun ρ hρ =>
    norm_pos_iff.mpr fun h => by have := (hZ ρ hρ).2.1; rw [h] at this; simp at this
  set S : ℝ := ∑ ρ ∈ Z, 1 / ‖ρ‖ ^ 2 with hS
  have hS0 : 0 < S := Finset.sum_pos (fun ρ hρ => by have := hnorm0 ρ hρ; positivity) hZne
  set lam : ℂ → ℝ := fun ρ => 1 / ‖ρ‖ ^ 2 / S with hlam
  have hlam0 : ∀ ρ, 0 ≤ lam ρ := fun ρ => by positivity
  have hlam1 : ∑ ρ ∈ Z, lam ρ = 1 := by
    rw [hlam, ← Finset.sum_div, ← hS, div_self hS0.ne']
  have hlam2 : ∑ ρ ∈ Z, lam ρ ^ 2 * (‖ρ‖ ^ 2 / 2) = 1 / (2 * S) := by
    have : ∀ ρ ∈ Z, lam ρ ^ 2 * (‖ρ‖ ^ 2 / 2) = (1 / ‖ρ‖ ^ 2) / (2 * S ^ 2) := by
      intro ρ hρ
      have := hnorm0 ρ hρ
      rw [hlam]; field_simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← hS]
    field_simp
  set Cs : ℝ := ∑ ρ ∈ Z, lam ρ * Cf ρ with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun ρ hρ => mul_nonneg (hlam0 ρ) (hCf0 ρ hρ)
  set KK : ℝ := ∑ ρ ∈ Z, ∑ ρ' ∈ Z, lam ρ * lam ρ' * Kf ρ ρ' with hKK
  refine ⟨(1 + η) * KK + (1 + 1 / η) * (1152 * Cs ^ 2), fun N hN => ?_⟩
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set Y : ℝ := (N : ℝ) ^ (1 + η) with hYdef
  have hNY : (N : ℝ) ≤ Y := Real.self_le_rpow_of_one_le (by linarith) (by linarith)
  have hY0 : 0 < Y := by linarith
  set K : ℕ := ⌈3 * Y⌉₊ + 2 * N with hKdef
  have hYK : 3 * Y ≤ K := by
    have := Nat.le_ceil (3 * Y)
    have h2 : ((⌈3 * Y⌉₊ : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : ⌈3 * Y⌉₊ ≤ K)
    linarith
  obtain ⟨P, hP, hNP, hP2N⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  have hPK : P ≤ K := by omega
  set a : ℕ → ℂ := fun k => ∑ ρ ∈ Z, (lam ρ : ℂ) * zeroSmoothDual ν ε ρ Y k with ha
  set v : ℕ → ℂ := fun m => -bdModDefect a K m with hv
  set b : ℕ → ℂ := bdMoebiusCorrection N P v with hb
  set Aseq : ℕ → ℝ := fun k => (a k).re + (b k).re with hAseq
  have hare : ∀ k, (a k).re = ∑ ρ ∈ Z, lam ρ * (zeroSmoothDual ν ε ρ Y k).re := by
    intro k
    simp only [ha, Complex.re_sum, Complex.re_ofReal_mul]
  -- support, value at one, constraints
  have hAsupp : ∀ k, K < k → Aseq k = 0 := by
    intro k hk
    have hk' : 3 * Y ≤ k := by
      have : (K : ℝ) + 1 ≤ k := by exact_mod_cast hk
      linarith
    simp only [hAseq, hare]
    rw [Finset.sum_eq_zero fun ρ _ => by rw [zeroSmoothDual_eq_zero hν hε0 hε1 ρ hY0 hk']; simp,
      hb, bdMoebiusCorrection_eq_zero hNP v (by omega)]
    simp
  have hψ : Smooth1 ν ε ((1 : ℕ) / Y) = 1 := by
    refine hbelow ε _ hε0 (by positivity) ?_
    rw [hc₁, hεdef]
    have hl := Real.log_two_lt_d9
    have : ((1 : ℕ) : ℝ) / Y ≤ 1 / 2 := by
      rw [Nat.cast_one, div_le_div_iff₀ hY0 (by norm_num)]; linarith
    norm_num at this hl ⊢
    linarith
  have hA1 : Aseq 1 = 1 := by
    simp only [hAseq, hare, hb]
    rw [bdMoebiusCorrection_one hP.two_le]
    have h1 : ∀ ρ ∈ Z, lam ρ * (zeroSmoothDual ν ε ρ Y 1).re = lam ρ := by
      intro ρ _
      unfold zeroSmoothDual zeroCoeff
      rw [if_neg one_ne_zero, hψ]
      simp
    rw [Finset.sum_congr rfl h1, hlam1]
    simp
  have hC' : ∀ m, 2 ≤ m → m ≤ N →
      ∑ n ∈ (Finset.range K).filter (fun n => m ∣ n + 1), Aseq (n + 1) =
        (1 / (m : ℝ)) * ∑ n ∈ Finset.range K, Aseq (n + 1) := by
    intro m hm2 hmN
    have h := dual_constraint_re (a := a + b) (K := K) (m := m) (by
      rw [bdModDefect_add, hb, bdModDefect_bdMoebiusCorrection hP hNP hPK v hm2 hmN, hv]
      ring)
    simpa only [Pi.add_apply, Complex.add_re, hAseq] using h
  have hmain := one_le_bdDistDiscrete_sq_mul_energy hAsupp hA1 hC'
  -- the energy of the combination
  have hlogY : Real.log Y = (1 + η) * Real.log N := by
    rw [hYdef, Real.log_rpow hN0]
  have hEa : bdDualEnergy (fun k => (a k).re) K ≤
      (1 + η) * Real.log N / (2 * S) + KK := by
    have hfun : (fun k => (a k).re) =
        fun k => ∑ ρ ∈ Z, lam ρ * (fun ρ k => (zeroSmoothDual ν ε ρ Y k).re) ρ k := by
      funext k; exact hare k
    rw [hfun, bdDualEnergy_sum_eq]
    have hle : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, lam ρ * lam ρ' *
        bdDualBilin (fun k => (zeroSmoothDual ν ε ρ Y k).re)
          (fun k => (zeroSmoothDual ν ε ρ' Y k).re) K ≤
        (if ρ = ρ' then lam ρ ^ 2 * (‖ρ‖ ^ 2 / 2) * Real.log Y else 0) +
          lam ρ * lam ρ' * Kf ρ ρ' := by
      intro ρ hρ ρ' hρ'
      have h := mul_le_mul_of_nonneg_left (hKf ρ hρ ρ' hρ' Y (by linarith) K)
        (mul_nonneg (hlam0 ρ) (hlam0 ρ'))
      refine h.trans (le_of_eq ?_)
      split_ifs with he
      · subst he; ring
      · ring
    calc ∑ ρ ∈ Z, ∑ ρ' ∈ Z, lam ρ * lam ρ' *
          bdDualBilin (fun k => (zeroSmoothDual ν ε ρ Y k).re)
            (fun k => (zeroSmoothDual ν ε ρ' Y k).re) K
        ≤ ∑ ρ ∈ Z, ∑ ρ' ∈ Z, ((if ρ = ρ' then lam ρ ^ 2 * (‖ρ‖ ^ 2 / 2) * Real.log Y else 0) +
          lam ρ * lam ρ' * Kf ρ ρ') :=
          Finset.sum_le_sum fun ρ hρ => Finset.sum_le_sum fun ρ' hρ' => hle ρ hρ ρ' hρ'
      _ = (∑ ρ ∈ Z, lam ρ ^ 2 * (‖ρ‖ ^ 2 / 2)) * Real.log Y + KK := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_mul]
          rw [hKK]
          congr 1
          exact Finset.sum_congr rfl fun ρ hρ => by rw [if_pos hρ]
      _ = (1 + η) * Real.log N / (2 * S) + KK := by
          rw [hlam2, hlogY]; field_simp
  -- the energy of the correction
  set δ : ℝ := 2 * Cs * ((N : ℝ) ^ 4)⁻¹ with hδ
  have hNA : ∀ m : ℕ, 1 ≤ m → m ≤ N → (m : ℝ) ^ A * Y ^ (-A) ≤ ((N : ℝ) ^ 4)⁻¹ := by
    intro m hm1 hmN
    have hmA : (m : ℝ) ^ A ≤ (N : ℝ) ^ A :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmN) hA0.le
    have hYA : Y ^ (-A) = (N : ℝ) ^ ((1 + η) * (-A)) := by
      rw [hYdef, ← Real.rpow_mul hN0.le]
    have hNY' : (N : ℝ) ^ A * Y ^ (-A) = ((N : ℝ) ^ 4)⁻¹ := by
      rw [hYA, ← Real.rpow_add hN0, show A + (1 + η) * (-A) = -((4 : ℕ) : ℝ) by
        rw [hAdef]; field_simp; push_cast; ring, Real.rpow_neg hN0.le, Real.rpow_natCast]
    rw [← hNY']
    exact mul_le_mul_of_nonneg_right hmA (Real.rpow_nonneg hY0.le _)
  have hvb : ∀ m, 1 ≤ m → m ≤ N → ‖v m‖ ≤ δ := by
    intro m hm1 hmN
    rw [hv, norm_neg, ha, bdModDefect_sum_mul]
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ ρ ∈ Z, ‖(lam ρ : ℂ) * bdModDefect (zeroSmoothDual ν ε ρ Y) K m‖ ≤
        lam ρ * Cf ρ * (2 * ((N : ℝ) ^ 4)⁻¹) := by
      intro ρ hρ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlam0 ρ)]
      have h1 := hCf ρ hρ Y hY0 K hYK m hm1
      have h2 : 2 * Cf ρ * (m : ℝ) ^ A * Y ^ (-A) ≤ 2 * Cf ρ * ((N : ℝ) ^ 4)⁻¹ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hNA m hm1 hmN) (by have := hCf0 ρ hρ; positivity)
      calc lam ρ * ‖bdModDefect (zeroSmoothDual ν ε ρ Y) K m‖ ≤
            lam ρ * (2 * Cf ρ * ((N : ℝ) ^ 4)⁻¹) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (hlam0 ρ)
        _ = lam ρ * Cf ρ * (2 * ((N : ℝ) ^ 4)⁻¹) := by ring
    refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← hCs, hδ]
    ring
  have hδ0 : 0 ≤ δ := by positivity
  have hV : ∑ m ∈ Finset.Icc 2 N, ‖v m‖ ≤ N * δ := by
    refine (Finset.sum_le_sum fun m hm => hvb m (by simp only [Finset.mem_Icc] at hm; omega)
      (Finset.mem_Icc.mp hm).2).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hδ0
    exact_mod_cast (by omega : N + 1 - 2 ≤ N)
  have hbB : ∀ k, ‖b k‖ ≤ ((N : ℝ) + 1) * (N * δ) := by
    intro k
    refine (norm_bdMoebiusCorrection_le N P v k).trans ?_
    exact mul_le_mul_of_nonneg_left hV (by positivity)
  have hEb := bdDualEnergyC_le_of_bounded (K := K)
    (fun k hk => bdMoebiusCorrection_eq_zero hNP v hk) hbB
  have hEb' : bdDualEnergyC b K ≤ 1152 * Cs ^ 2 := by
    refine hEb.trans ?_
    have hPR : (P : ℝ) ≤ 2 * N := by exact_mod_cast hP2N
    have hP1 : (P : ℝ) + 1 ≤ 3 * N := by linarith
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
    have hN1 : (N : ℝ) + 1 ≤ 2 * N := by linarith
    calc (P : ℝ) * ((P : ℝ) + 1) ^ 2 * (2 * (((N : ℝ) + 1) * (N * δ))) ^ 2
        ≤ (2 * N) * (3 * N) ^ 2 * (2 * ((2 * N) * (N * δ))) ^ 2 := by
          gcongr
      _ = 1152 * Cs ^ 2 * (N : ℝ)⁻¹ := by
          rw [hδ]; field_simp; ring
      _ ≤ 1152 * Cs ^ 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact inv_le_one_of_one_le₀ (by linarith)
      _ = 1152 * Cs ^ 2 := mul_one _
  have hEbre : bdDualEnergy (fun k => (b k).re) K ≤ 1152 * Cs ^ 2 :=
    (bdDualEnergy_re_le b K).trans hEb'
  have hEtot := bdDualEnergy_add_le (fun k => (a k).re) (fun k => (b k).re) K hη
  have hE : bdDualEnergy Aseq K ≤ (1 + η) ^ 2 / (2 * S) * Real.log N +
      ((1 + η) * KK + (1 + 1 / η) * (1152 * Cs ^ 2)) := by
    have h1 : (1 + η) * bdDualEnergy (fun k => (a k).re) K ≤
        (1 + η) * ((1 + η) * Real.log N / (2 * S) + KK) :=
      mul_le_mul_of_nonneg_left hEa (by positivity)
    have h2 : (1 + 1 / η) * bdDualEnergy (fun k => (b k).re) K ≤
        (1 + 1 / η) * (1152 * Cs ^ 2) :=
      mul_le_mul_of_nonneg_left hEbre (by positivity)
    have e : (1 + η) * ((1 + η) * Real.log N / (2 * S) + KK) =
        (1 + η) ^ 2 / (2 * S) * Real.log N + (1 + η) * KK := by ring
    have : bdDualEnergy Aseq K = bdDualEnergy (fun k => (a k).re + (b k).re) K := rfl
    rw [this]
    linarith only [hEtot, h1, h2, e]
  calc (1 : ℝ) ≤ bdDistDiscrete N ^ 2 * bdDualEnergy Aseq K := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (sq_nonneg _)

/-- Letting `η → 0`: if `1 ≤ f(N)((1 + η)² β₀ log N + K₁(η))` for every `η > 0`, then
`liminf f(N) log N ≥ 1/β₀`. -/
theorem eventually_le_mul_log_of_forall_one_le {f : ℕ → ℝ} (hf0 : ∀ N, 0 ≤ f N) {β₀ : ℝ}
    (hβ₀ : 0 < β₀)
    (h : ∀ η : ℝ, 0 < η → ∃ K₁ : ℝ, ∀ N : ℕ, 2 ≤ N →
      1 ≤ f N * ((1 + η) ^ 2 * β₀ * Real.log N + K₁))
    {c : ℝ} (hc : c < 1 / β₀) :
    ∀ᶠ N : ℕ in Filter.atTop, c ≤ f N * Real.log N := by
  rcases le_or_gt c 0 with hc0 | hc0
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    exact hc0.trans (mul_nonneg (hf0 N) this)
  set r : ℝ := 1 / (c * β₀) with hr
  have hr1 : 1 < r := by
    rw [hr, one_lt_div (by positivity)]
    exact (lt_div_iff₀ hβ₀).mp hc
  set η : ℝ := min 1 ((r - 1) / 4) with hη
  have hη0 : 0 < η := lt_min one_pos (by linarith)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ (r - 1) / 4 := min_le_right _ _
  set β : ℝ := (1 + η) ^ 2 * β₀ with hβ
  have hcβ : c * β < 1 := by
    have h1 : (1 + η) ^ 2 < r := by nlinarith
    have h3 : r * (c * β₀) = 1 := by rw [hr]; field_simp
    have h2 : c * β = (1 + η) ^ 2 * (c * β₀) := by rw [hβ]; ring
    rw [h2]
    nlinarith [mul_pos hc0 hβ₀]
  obtain ⟨K₁, hK₁⟩ := h η hη0
  set T : ℝ := |K₁| * c / (1 - c * β) + 1 with hT
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 2, hlog.eventually_ge_atTop T] with N hN hNT
  have hK := hK₁ N hN
  rw [← hβ] at hK
  by_contra hlt
  push Not at hlt
  have hT0 : 0 < T := by
    rw [hT]
    have : 0 ≤ |K₁| * c / (1 - c * β) := div_nonneg (by positivity) (by linarith)
    linarith
  have hlogpos : 0 < Real.log N := by linarith
  set D : ℝ := f N with hD
  have hD0 : 0 ≤ D := hf0 N
  have hDc : D < c / Real.log N := by rw [lt_div_iff₀ hlogpos]; exact hlt
  have hDK : D * K₁ ≤ |K₁| * (c / Real.log N) :=
    (le_abs_self _).trans (by rw [abs_mul, abs_of_nonneg hD0, mul_comm]; exact
      mul_le_mul_of_nonneg_left hDc.le (abs_nonneg _))
  have h1 : 1 ≤ β * (D * Real.log N) + D * K₁ := by
    have e : D * (β * Real.log N + K₁) = β * (D * Real.log N) + D * K₁ := by ring
    linarith
  have hβ0 : 0 < β := by positivity
  have h2 : β * (D * Real.log N) < β * c := mul_lt_mul_of_pos_left hlt hβ0
  have h3 : |K₁| * (c / Real.log N) ≤ 1 - c * β := by
    have hT' : |K₁| * c / (1 - c * β) ≤ Real.log N := by linarith
    rw [div_le_iff₀ (by linarith)] at hT'
    rw [mul_div_assoc', div_le_iff₀ hlogpos]
    nlinarith
  linarith only [h1, h2, hDK, h3]

/-- **Burnol's lower bound.**  For every finite set `Z` of zeros of `ζ` on the critical line in
the upper half-plane, `liminf_{N→∞} d_N² log N ≥ Σ_{ρ ∈ Z} 2/|ρ|²`. -/
theorem eventually_le_bdDistDiscrete_sq_mul_log_of_zeros {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ 0 < ρ.im) {c : ℝ}
    (hc : c < ∑ ρ ∈ Z, 2 / ‖ρ‖ ^ 2) :
    ∀ᶠ N : ℕ in Filter.atTop, c ≤ bdDistDiscrete N ^ 2 * Real.log N := by
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · subst hZe
    simp only [Finset.sum_empty] at hc
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    exact hc.le.trans (by positivity)
  have hnorm0 : ∀ ρ ∈ Z, 0 < ‖ρ‖ := fun ρ hρ =>
    norm_pos_iff.mpr fun h => by have := (hZ ρ hρ).2.1; rw [h] at this; simp at this
  set S : ℝ := ∑ ρ ∈ Z, 1 / ‖ρ‖ ^ 2 with hS
  have hS0 : 0 < S := Finset.sum_pos (fun ρ hρ => by have := hnorm0 ρ hρ; positivity) hZne
  have h2S : ∑ ρ ∈ Z, 2 / ‖ρ‖ ^ 2 = 1 / (1 / (2 * S)) := by
    rw [one_div_one_div, hS, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  rw [h2S] at hc
  refine eventually_le_mul_log_of_forall_one_le (fun N => sq_nonneg _) (by positivity)
    (fun η hη => ?_) hc
  obtain ⟨K₁, hK₁⟩ := exists_one_le_bdDistDiscrete_sq_mul_log_of_zeros hZ hZne hη
  refine ⟨K₁, fun N hN => (hK₁ N hN).trans_eq ?_⟩
  rw [← hS]
  ring

/-- **One critical zero.**  For every zero `ρ` of `ζ` with `Re ρ = ½`,
`liminf_{N→∞} d_N² log N ≥ 2/|ρ|²`. -/
theorem eventually_le_bdDistDiscrete_sq_mul_log_of_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : ρ.re = 1 / 2) {c : ℝ} (hc : c < 2 / ‖ρ‖ ^ 2) :
    ∀ᶠ N : ℕ in Filter.atTop, c ≤ bdDistDiscrete N ^ 2 * Real.log N := by
  have him : ρ.im ≠ 0 := by
    intro h
    have hρr : ρ = ((1 / 2 : ℝ) : ℂ) := Complex.ext (by simp [hre]) (by simp [h])
    exact riemannZeta_ne_zero_of_ofReal_mem_Ioo (by norm_num) (by norm_num) (hρr ▸ hρ)
  rcases him.lt_or_gt with hneg | hpos
  · refine eventually_le_bdDistDiscrete_sq_mul_log_of_zeros (Z := {conj ρ}) ?_ ?_
    · intro σ hσ
      rw [Finset.mem_singleton] at hσ
      subst hσ
      refine ⟨by rw [riemannZeta_conj, hρ, map_zero], by simp [hre], by simp; linarith⟩
    · simpa [Complex.norm_conj] using hc
  · refine eventually_le_bdDistDiscrete_sq_mul_log_of_zeros (Z := {ρ}) ?_ ?_
    · intro σ hσ
      rw [Finset.mem_singleton] at hσ
      subst hσ
      exact ⟨hρ, hre, hpos⟩
    · simpa using hc

end

end RHTower
