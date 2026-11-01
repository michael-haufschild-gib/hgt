import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormOnTheCoherentSector
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixDecomposesAtEveryOverlap

/-!
# The complete Weil form on packets at every overlap

At overlap `c > 1` neighbouring atoms meet and the prime side pairs `n` with the non-ratio partners
`m ≈ kn` (successor shells). RAPT's exact decomposition at every overlap
(`completeWeilMatrix_inner_eq_decomposition_at_every_overlap`) adds two matrices to the strictly
separated picture: the literal archimedean pairing `Ov` of near atoms and the non-ratio prime matrix
`NR`. In packet coordinates `x_n = F(n)/√n`:

* **Laplacian polarization** (`sum_sum_mul_eq_degree_sub_dirichlet`): every symmetric form is its
  degree diagonal minus half its Dirichlet energy. For `NR` with weights `v_{nm} = NR_{nm}/√(nm)`
  this gives `⟨NR x, x⟩ = Σ_n d_n F(n)² − ½ A_N(F)` (`inner_nonRatio_packetVector`), with the
  **shell degree** `d_n = Σ_m v_{nm}` and the **affine Dirichlet energy**
  `A_N(F) = Σ_{n,m} v_{nm}(F(n) − F(m))²`.
* **Nonnegative weights** (`fullWeilNonRatioMatrix_nonneg`): for a nonnegative profile every
  non-ratio entry is nonnegative. The exact-ratio term of the prime pairing is exactly Weil's prime
  kernel and every other term is an overlap integral of nonnegative atoms. Hence `A_N(F) ≥ 0`
  (`affineDirichlet_nonneg`).
* **The identity at every overlap** (`completeWeilEnergy_packetVector_at_every_overlap`):

  `E(F/√·) = J_N(F) + ½ A_N(F) + Σ_n F(n)²/n (s_c + e_N + δ_N(n) − R(⌊N/n⌋)) − Σ_n d_n F(n)²`
  `          + (center − far cross + pole error + near archimedean overlap)`.

  The prime side is therefore, at every overlap, a sum of squares of dilation and affine jumps
  minus an exact diagonal: the Mertens term `ψ₁ + log n` (cancelled by `log N − γ` up to `R` and
  `δ`) plus the shell degree `d_n`. On incidence packets every jump is a sum of incidence events
  (`incidencePacket_dilation_jump`, `incidencePacket_affine_jump`).
* **Localization at every overlap** (`jumpEnergy_add_half_affine_le_of_nonpos`): a packet with
  nonpositive complete energy has total incidence energy at most its shell degree plus a bounded
  diagonal plus the pole, boundary and overlap terms. The shell degree is the only quantity that
  grows with the overlap.
-/

open Finset ArithmeticFunction Filter Topology
open scoped RealInnerProductSpace
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticLorentzianGeometry
  GaloisForLFunctions.CriticalArithmeticCorrelationTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-! ### Laplacian polarization -/

/-- **Laplacian polarization.** A symmetric form is its degree diagonal minus half its Dirichlet
energy. -/
theorem sum_sum_mul_eq_degree_sub_dirichlet {ι : Type*} (s : Finset ι) (v : ι → ι → ℝ)
    (hv : ∀ i j, v i j = v j i) (F : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, v i j * F i * F j =
      ∑ i ∈ s, (∑ j ∈ s, v i j) * F i ^ 2 - (1 / 2) * ∑ i ∈ s, ∑ j ∈ s, v i j * (F i - F j) ^ 2 := by
  have hswap : ∑ i ∈ s, ∑ j ∈ s, v i j * F j ^ 2 = ∑ i ∈ s, (∑ j ∈ s, v i j) * F i ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_mul]
    exact sum_congr rfl fun i _ => by rw [hv]
  have hexp : ∑ i ∈ s, ∑ j ∈ s, v i j * (F i - F j) ^ 2 =
      ∑ i ∈ s, (∑ j ∈ s, v i j) * F i ^ 2 + ∑ i ∈ s, ∑ j ∈ s, v i j * F j ^ 2 -
        2 * ∑ i ∈ s, ∑ j ∈ s, v i j * F i * F j := by
    simp only [mul_sum, sum_mul, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [hexp, hswap]; ring

/-! ### Packet coordinates of the non-ratio matrix -/

/-- The packet vector `x_n = F(n)/√n` on the horizon. -/
abbrev packetVector (F : ℕ → ℝ) (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  horizonProfileVector (atomAmplitude F) N

/-- The non-ratio weight `v_{nm} = NR_{nm}/√(nm)` in packet coordinates. -/
def nonRatioWeight (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (n m : PrimeHorizonIndex N) : ℝ :=
  fullWeilNonRatioMatrix φ c N n m / (Real.sqrt (n : ℕ) * Real.sqrt (m : ℕ))

/-- The shell degree `d_n = Σ_m v_{nm}`. -/
def shellDegree (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (n : PrimeHorizonIndex N) : ℝ :=
  ∑ m, nonRatioWeight φ c N n m

/-- The affine Dirichlet energy `A_N(F) = Σ_{n,m} v_{nm}(F(n) − F(m))²`. -/
def affineDirichlet (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ n : PrimeHorizonIndex N, ∑ m : PrimeHorizonIndex N,
    nonRatioWeight φ c N n m * (F n - F m) ^ 2

theorem nonRatioWeight_symm (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (n m : PrimeHorizonIndex N) :
    nonRatioWeight φ c N n m = nonRatioWeight φ c N m n := by
  have h := (fullWeilNonRatioMatrix_isHermitian φ c N).apply n m
  simp only [star_trivial] at h
  rw [nonRatioWeight, nonRatioWeight, h, mul_comm]

/-- **The non-ratio prime form in packet coordinates**: shell degree minus half the affine Dirichlet
energy. -/
theorem inner_nonRatio_packetVector (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (F : ℕ → ℝ) :
    ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) (packetVector F N), packetVector F N⟫ =
      ∑ n : PrimeHorizonIndex N, shellDegree φ c N n * F n ^ 2 -
        (1 / 2) * affineDirichlet φ c N F := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, atomAmplitude F n *
    ∑ m : PrimeHorizonIndex N, fullWeilNonRatioMatrix φ c N n m * atomAmplitude F m) = _
  have hpos : ∀ n : PrimeHorizonIndex N, 0 < Real.sqrt (n : ℕ) := fun n =>
    Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp n.property).1)
  have hterm : ∀ n m : PrimeHorizonIndex N, atomAmplitude F n *
      (fullWeilNonRatioMatrix φ c N n m * atomAmplitude F m) =
      nonRatioWeight φ c N n m * F n * F m := fun n m => by
    have h1 := (hpos n).ne'
    have h2 := (hpos m).ne'
    simp only [atomAmplitude, nonRatioWeight]
    field_simp
  simp_rw [mul_sum, hterm]
  rw [sum_sum_mul_eq_degree_sub_dirichlet univ _ (nonRatioWeight_symm φ c N)]
  rfl

/-! ### Nonnegative non-ratio weights -/

/-- **The non-ratio entries of a nonnegative profile are nonnegative.** -/
theorem fullWeilNonRatioMatrix_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (n m : PrimeHorizonIndex N) : 0 ≤ fullWeilNonRatioMatrix φ c N n m := by
  have hn := mem_Icc.mp n.property
  have hm := mem_Icc.mp m.property
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hn.1.trans hn.2
  set w := c / N with hwdef
  have hw : 0 < w := div_pos hc hN0
  set g := atomDilate φ w with hgdef
  have hg0 : ∀ u, 0 ≤ g u := fun u => hφ0 _
  have hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0 := fun u hu => by
    apply hsupp
    rintro ⟨h1, h2⟩
    apply hu
    constructor
    · exact (div_nonneg_iff.mp h1).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hw)
    · exact (div_le_one hw).mp h2
  have hG : 0 < ∫ u, g u ^ 2 := by rw [hgdef, integral_atomDilate_sq hw]; exact mul_pos hw hM
  set R := Real.log N + w + 1
  have hfin := primePair_eq_sum_of_supportedIn (supportedIn_atom hgsupp hw.le n.property)
    (supportedIn_atom hgsupp hw.le m.property)
  have hplus (k : ℕ) : 0 ≤ ∫ u, atom g n u * atom g m (u + Real.log k) :=
    MeasureTheory.integral_nonneg fun u => mul_nonneg (hg0 _) (hg0 _)
  have hminus (k : ℕ) : 0 ≤ ∫ u, atom g n u * atom g m (u - Real.log k) :=
    MeasureTheory.integral_nonneg fun u => mul_nonneg (hg0 _) (hg0 _)
  have hterm : ∀ k ∈ range (lagRange R), 0 ≤ RHTower.vonMangoldtAtom k *
      ((∫ t, atom g n t * atom g m (t - Real.log k)) + ∫ t, atom g n t * atom g m (t + Real.log k)) :=
    fun k _ => mul_nonneg (vonMangoldtAtom_nonneg' k) (add_nonneg (hminus k) (hplus k))
  have hrange : ∀ k : ℕ, 1 ≤ k → k ≤ N → k ∈ range (lagRange R) := fun k hk1 hkN => by
    by_contra hk
    have hlarge := two_mul_lt_abs_log_of_lagRange_le
      (show lagRange R ≤ k by simpa only [mem_range, not_lt] using hk)
    rw [abs_of_nonneg (Real.log_natCast_nonneg k)] at hlarge
    have hlog := Real.log_le_log (show (0 : ℝ) < k by exact_mod_cast hk1)
      (show (k : ℝ) ≤ N by exact_mod_cast hkN)
    simp only [R] at hlarge
    linarith [Real.log_natCast_nonneg N]
  have hmass : ∀ a b k : ℕ, 0 < a → 0 < k → b = k * a →
      (∫ u, atom g a u * atom g b (u + Real.log k)) = ∫ u, g u ^ 2 := fun a b k ha hk hb => by
    have hlog : Real.log b = Real.log k + Real.log a := by
      rw [hb, Nat.cast_mul, Real.log_mul (by exact_mod_cast hk.ne') (by exact_mod_cast ha.ne')]
    have e : (fun u => atom g a u * atom g b (u + Real.log k)) = fun u => g (u - Real.log a) ^ 2 := by
      funext u
      simp only [atom, hlog, sq]
      congr 2; ring
    rw [e]
    exact MeasureTheory.integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log a)
  have hmass' : ∀ a b k : ℕ, 0 < b → 0 < k → a = k * b →
      (∫ u, atom g a u * atom g b (u - Real.log k)) = ∫ u, g u ^ 2 := fun a b k hb hk ha => by
    have hlog : Real.log a = Real.log k + Real.log b := by
      rw [ha, Nat.cast_mul, Real.log_mul (by exact_mod_cast hk.ne') (by exact_mod_cast hb.ne')]
    have e : (fun u => atom g a u * atom g b (u - Real.log k)) = fun u => g (u - Real.log a) ^ 2 := by
      funext u
      simp only [atom, hlog, sq]
      congr 2; ring
    rw [e]
    exact MeasureTheory.integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log a)
  have hatom : ∀ k : ℕ, 2 ≤ k → RHTower.vonMangoldtAtom k = Λ k / Real.sqrt k := fun k hk => by
    simp [RHTower.vonMangoldtAtom, hk]
  rw [fullWeilNonRatioMatrix_apply, ← hgdef, sub_nonneg, le_div_iff₀ hG]
  unfold weilPrimeKernel
  split_ifs with h1 h2
  · -- `n ∣ m`: the exact-ratio lag `k₀ = m/n`
    set k₀ := (m : ℕ) / (n : ℕ)
    have hk₀m : (m : ℕ) = k₀ * n := (Nat.div_mul_cancel h1.1).symm
    have hk₀2 : 2 ≤ k₀ := by
      rcases Nat.lt_or_ge k₀ 2 with h | h
      · interval_cases hk : k₀
        · rw [zero_mul] at hk₀m; omega
        · rw [one_mul] at hk₀m; exact absurd hk₀m.symm h1.2
      · exact h
    have hk₀N : k₀ ≤ N := (Nat.div_le_self _ _).trans hm.2
    rw [← hatom k₀ hk₀2, hfin]
    refine le_trans ?_ (single_le_sum hterm (hrange k₀ (by omega) hk₀N))
    rw [hmass n m k₀ hn.1 (by omega) hk₀m]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hminus k₀))
      (vonMangoldtAtom_nonneg' k₀) |>.trans_eq' (by ring)
  · -- `m ∣ n`: the exact-ratio lag `k₀ = n/m`
    set k₀ := (n : ℕ) / (m : ℕ)
    have hk₀n : (n : ℕ) = k₀ * m := (Nat.div_mul_cancel h2.1).symm
    have hk₀2 : 2 ≤ k₀ := by
      rcases Nat.lt_or_ge k₀ 2 with h | h
      · interval_cases hk : k₀
        · rw [zero_mul] at hk₀n; omega
        · rw [one_mul] at hk₀n; exact absurd hk₀n.symm h2.2
      · exact h
    have hk₀N : k₀ ≤ N := (Nat.div_le_self _ _).trans hn.2
    rw [← hatom k₀ hk₀2, hfin]
    refine le_trans ?_ (single_le_sum hterm (hrange k₀ (by omega) hk₀N))
    rw [hmass' n m k₀ hm.1 (by omega) hk₀n]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hplus k₀))
      (vonMangoldtAtom_nonneg' k₀) |>.trans_eq' (by ring)
  · rw [zero_mul, hfin]
    exact sum_nonneg hterm

theorem nonRatioWeight_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (n m : PrimeHorizonIndex N) : 0 ≤ nonRatioWeight φ c N n m :=
  div_nonneg (fullWeilNonRatioMatrix_nonneg hφ0 hsupp hM hc n m)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- **The affine Dirichlet energy of a nonnegative profile is nonnegative.** -/
theorem affineDirichlet_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    (N : ℕ) (F : ℕ → ℝ) : 0 ≤ affineDirichlet φ c N F :=
  sum_nonneg fun n _ => sum_nonneg fun m _ =>
    mul_nonneg (nonRatioWeight_nonneg hφ0 hsupp hM hc n m) (sq_nonneg _)

/-! ### The identity at every overlap -/

/-- The renormalized prime part on a packet: jump energy plus the Mertens–Euler diagonal. -/
theorem renormalizedPrime_packetVector (N : ℕ) (F : ℕ → ℝ) (s : ℝ) :
    (Real.log N * ‖packetVector F N‖ ^ 2 -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (packetVector F N), packetVector F N⟫) +
      (s - Real.eulerMascheroniConstant) * ‖packetVector F N‖ ^ 2 =
      jumpEnergy N F + ∑ n ∈ Icc 1 N, F n ^ 2 / n * (s + floorDefect N n - mertensRemainder (N / n)) := by
  set x := packetVector F N
  have hext : ∀ n ∈ Icc 1 N, primeHorizonExtension x n = atomAmplitude F n := fun n hn => by
    simp [primeHorizonExtension, hn, x, horizonProfileVector]
  have hnorm : ‖x‖ ^ 2 = ∑ n ∈ Icc 1 N, F n ^ 2 / n := by
    rw [horizonProfileVector_norm_sq]
    exact sum_congr rfl fun n hn => atomAmplitude_sq (mem_Icc.mp hn).1 F
  have hprime : ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) x, x⟫ = primeDilationForm N F := by
    rw [← atomicWeilForm_primeHorizonExtension, atomicWeilForm_congr hext,
      atomicWeilForm_atomAmplitude]
  rw [hprime, primeDilationForm_eq, mertensDiagonal, hnorm]
  have hdiag : ∀ n ∈ Icc 1 N, F n ^ 2 / n * (s + floorDefect N n - mertensRemainder (N / n)) =
      Real.log N * (F n ^ 2 / n) - F n ^ 2 / n * (mertensSum (N / n) + Real.log n) +
        (s - Real.eulerMascheroniConstant) * (F n ^ 2 / n) := fun n _ => by
    rw [show s + floorDefect N n - mertensRemainder (N / n) =
        s + (Real.log N - Real.eulerMascheroniConstant - mertensSum (N / n) - Real.log n) by
      rw [log_sub_euler_sub_mertens]; ring]
    ring
  rw [sum_congr rfl hdiag, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  ring

/-- **The complete Weil energy of a packet at every overlap**: dilation and affine incidence squares,
the Mertens–Euler diagonal, minus the shell degree, plus the pole, boundary and overlap terms. -/
theorem completeWeilEnergy_packetVector_at_every_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (F : ℕ → ℝ) :
    completeWeilEnergy φ c N (packetVector F N) =
      jumpEnergy N F + (1 / 2) * affineDirichlet φ c N F +
      ∑ n ∈ Icc 1 N, F n ^ 2 / n * (completeWeilSelfFinitePart φ c +
        completeWeilSelfError φ c N + floorDefect N n - mertensRemainder (N / n)) -
      ∑ n : PrimeHorizonIndex N, shellDegree φ c N n * F n ^ 2 +
      (⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (packetVector F N), packetVector F N⟫ -
        ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (packetVector F N),
          packetVector F N⟫ +
        ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (packetVector F N),
          packetVector F N⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (packetVector F N), packetVector F N⟫) := by
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_decomposition_at_every_overlap hφ hsupp hM hc hN,
    inner_nonRatio_packetVector]
  have h := renormalizedPrime_packetVector N F (completeWeilSelfFinitePart φ c +
    completeWeilSelfError φ c N)
  have e : ∑ n ∈ Icc 1 N, F n ^ 2 / n * (completeWeilSelfFinitePart φ c +
      completeWeilSelfError φ c N + floorDefect N n - mertensRemainder (N / n)) =
      ∑ n ∈ Icc 1 N, F n ^ 2 / n * ((completeWeilSelfFinitePart φ c + completeWeilSelfError φ c N) +
        floorDefect N n - mertensRemainder (N / n)) := rfl
  rw [e]
  linear_combination h

/-- **Localization at every overlap.** A packet with nonpositive complete energy has its dilation and
affine incidence energy bounded by its shell degree, a bounded diagonal, and the pole, boundary
and overlap terms. -/
theorem jumpEnergy_add_half_affine_le_of_nonpos {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (F : ℕ → ℝ)
    (hE : completeWeilEnergy φ c N (packetVector F N) ≤ 0) :
    jumpEnergy N F + (1 / 2) * affineDirichlet φ c N F ≤
      ∑ n : PrimeHorizonIndex N, shellDegree φ c N n * F n ^ 2 -
      ∑ n ∈ Icc 1 N, F n ^ 2 / n * (completeWeilSelfFinitePart φ c +
        completeWeilSelfError φ c N + floorDefect N n - mertensRemainder (N / n)) -
      (⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (packetVector F N), packetVector F N⟫ -
        ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (packetVector F N),
          packetVector F N⟫ +
        ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (packetVector F N),
          packetVector F N⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (packetVector F N), packetVector F N⟫) := by
  have h := completeWeilEnergy_packetVector_at_every_overlap hφ hsupp hM hc hN F
  linarith

end GaloisForLFunctions.ArithmeticCouplingTheory
