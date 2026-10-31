import GaloisForLFunctions.CompletedArithmeticForms.RamanujanConductorFrames
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeDefectHasAnExponentialConductorCutoff
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramUniformRemainder
import GaloisForLFunctions.HTGeometry.HarmonicQuotientTailBound

/-!
# Conductor-band projections, quantitative confinement, and sub-horizon tails

This module develops the geometric and harmonic properties of finite Ramanujan conductor
subspaces `conductorSubspace R N` below the square-root horizon `R * R ≤ N`:

* **Quantitative exponential confinement and reverse defect gap.** Unfolding the prime-prefix
  conditioning cutoffs in terms of the squared-error threshold `0 < η ≤ 1` yields an explicit
  cubic dependence `log R ≤ (C / η^3) (K + 1)`. Contraposition at `η = 1/16` converts a lower
  bound on the distance to `conductorSubspace Q N` into a logarithmic lower bound on `poleDefect`.
* **Polarized harmonic Gram discrepancy and band decoupling.** Dividing the uniform harmonic Gram
  remainder by `log N` bounds `|‖∑ a_m v_m‖^2 - ∑ a_m^2|` by `9 (1 + log Q) / log N · ∑ a_m^2`,
  polarizes to coefficient-orthogonal packets without entrywise double sums, bounds the low-band
  leak of vectors in `conductorSubspace R N ⊓ (conductorSubspace Q N)ᗮ`, and certifies the
  reverse defect gap on packets supported above `Q`.
* **Sub-horizon quotient tails and linear moments.** Subtracting the quadratic harmonic Gram
  torsion expansion at `K` and `N` cancels the torsion pairing identically, giving a `log Q`-free
  top-band mass bound on `(K, N]` whenever `R * R ≤ K ≤ N`, and an `O(log log N / log N)` bound
  on the linear moment `∑_{n=1}^N (n / N) u_n^2`.
-/

noncomputable section

open Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Classical

namespace GaloisForLFunctions.CompletedArithmeticForms

open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  SuccessorShellArithmetic ArithmeticElectrostatics

/-! ### 1. Conductor-subspace monotonicity and orthogonal projections -/

/-- A normalized Ramanujan mode with conductor `m ∈ Icc 1 M` belongs to `conductorSubspace M N`. -/
theorem mem_conductorSubspace_normalizedRamanujanHorizonVector {m M N : ℕ}
    (hm : m ∈ Icc 1 M) :
    normalizedRamanujanHorizonVector m N ∈ conductorSubspace M N :=
  Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩

/-- Any linear combination of `normalizedRamanujanHorizonVector m N` over `Icc 1 M` lies in
`conductorSubspace M N`. -/
theorem sum_normalizedRamanujanHorizonVector_mem_conductorSubspace (M N : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) ∈ conductorSubspace M N :=
  Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ (mem_conductorSubspace_normalizedRamanujanHorizonVector hm)

/-- Conductor subspaces are monotone in the conductor cutoff. -/
theorem conductorSubspace_mono {Q R : ℕ} (hQR : Q ≤ R) (N : ℕ) :
    conductorSubspace Q N ≤ conductorSubspace R N := by
  unfold conductorSubspace
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  exact ⟨⟨m.1, mem_Icc.mpr ⟨(mem_Icc.mp m.2).1, (mem_Icc.mp m.2).2.trans hQR⟩⟩, rfl⟩

/-- Orthogonal projection minimizes squared Euclidean distance to a submodule. -/
theorem norm_sub_starProjection_sq_le {N : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (x v : EuclideanSpace ℝ (PrimeHorizonIndex N)) (hv : v ∈ K) :
    ‖x - K.starProjection x‖ ^ 2 ≤ ‖x - v‖ ^ 2 := by
  let p := K.starProjection x
  have hmem : p - v ∈ K := K.sub_mem (K.starProjection_apply_mem x) hv
  have horth : ⟪x - p, p - v⟫ = 0 := K.starProjection_inner_eq_zero x (p - v) hmem
  have hdecomp : x - v = (x - p) + (p - v) := by abel
  rw [hdecomp, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
    real_inner_comm (p - v) (x - p), horth, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  nlinarith only [sq_nonneg ‖p - v‖]

/-- Pythagorean decomposition for orthogonal projection on `EuclideanSpace ℝ (PrimeHorizonIndex N)`. -/
theorem norm_starProjection_sq_add_sub_sq {N : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖K.starProjection x‖ ^ 2 + ‖x - K.starProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
  let p := K.starProjection x
  have horth : ⟪x - p, p⟫ = 0 := K.starProjection_inner_eq_zero x p (K.starProjection_apply_mem x)
  have hdecomp : x = p + (x - p) := by abel
  conv_rhs => rw [hdecomp]
  rw [← real_inner_self_eq_norm_sq (p + (x - p)), inner_add_left, inner_add_right,
    inner_add_right, real_inner_comm p (x - p), horth, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  ring

/-- Projecting onto a larger submodule `L` preserves orthogonality to any smaller `K ≤ L`. -/
theorem starProjection_mem_orthogonal_of_le {N : ℕ}
    {K L : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N))} (hKL : K ≤ L)
    {x : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hx : x ∈ Kᗮ) :
    L.starProjection x ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  have hx0 : ⟪v, x⟫ = 0 := (Submodule.mem_orthogonal K x).mp hx v hv
  have hsub : ⟪x - L.starProjection x, v⟫ = 0 :=
    L.starProjection_inner_eq_zero x v (hKL hv)
  rw [inner_sub_left, real_inner_comm x v, hx0, zero_sub, neg_eq_zero, real_inner_comm] at hsub
  exact hsub

private theorem primeHorizonExtension_smul (N : ℕ) (s : ℝ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonExtension (s • x) = s • primeHorizonExtension x := by
  funext n
  simp only [primeHorizonExtension, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rfl
  · exact (mul_zero s).symm

private theorem poleDefect_smul (N : ℕ) (s : ℝ) (x : ℕ → ℝ) :
    poleDefect N (s • x) = s ^ 2 * poleDefect N x := by
  unfold poleDefect
  simp only [mul_sum, Pi.smul_apply, smul_eq_mul]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

private theorem norm_sub_normalizedRamanujan_sum_sq {R N : ℕ} (hN : 2 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) (b : ℕ → ℝ) :
    ‖x - ∑ m ∈ Icc 1 R, (b m * Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      ∑ n ∈ Icc 1 N,
        (primeHorizonExtension x n - ∑ m ∈ Icc 1 R, b m * ramanujanPoleProfile m n) ^ 2 := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hs : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  have heq : (∑ m ∈ Icc 1 R,
      (b m * Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector m N) =
      ∑ m ∈ Icc 1 R, b m • ramanujanHorizonVector m N := by
    refine sum_congr rfl fun m _ => ?_
    rw [normalizedRamanujanHorizonVector, smul_smul]
    congr 1
    field_simp [hs]
  rw [heq, EuclideanSpace.real_norm_sq_eq, ← sum_coe_sort (Icc 1 N) (fun n =>
    (primeHorizonExtension x n - ∑ m ∈ Icc 1 R, b m * ramanujanPoleProfile m n) ^ 2)]
  refine sum_congr rfl fun n _ => ?_
  have hsum : (∑ m ∈ Icc 1 R, b m • ramanujanHorizonVector m N) n =
      ∑ m ∈ Icc 1 R, b m * ramanujanPoleProfile m n := by
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
      (∑ m ∈ Icc 1 R, b m • ramanujanHorizonVector m N) = _
    rw [map_sum]
    exact sum_congr rfl fun _ _ => rfl
  simp only [PiLp.sub_apply, hsum, primeHorizonExtension_coe]

/-! ### 2. Quantitative exponential confinement and reverse defect gap -/

private theorem exists_nat_log_cutoff_quant {x : ℝ} (hx : 0 ≤ x) :
    ∃ T : ℕ, 1 < T ∧ x ≤ Real.log T ∧ Real.log T ≤ x + 3 := by
  let z : ℝ := x + 2
  let T : ℕ := ⌈Real.exp z⌉₊
  have hz : 0 < z := by dsimp only [z]; linarith only [hx]
  have hexp : 1 < Real.exp z := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hz
  have hceil : Real.exp z ≤ (T : ℝ) := Nat.le_ceil _
  have hTR : (1 : ℝ) < T := hexp.trans_le hceil
  have hT : 1 < T := by exact_mod_cast hTR
  have hlower : z ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos z) hceil
  have hceilUpper : (T : ℝ) < Real.exp z + 1 := Nat.ceil_lt_add_one (Real.exp_pos z).le
  have hdouble : (T : ℝ) ≤ 2 * Real.exp z := by linarith only [hceilUpper, hexp]
  have hlogTwo : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hupper : Real.log T ≤ z + 1 := by
    have h := Real.log_le_log (zero_lt_one.trans hTR) hdouble
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero z), Real.log_exp] at h
    linarith only [h, hlogTwo]
  refine ⟨T, hT, ?_, ?_⟩
  · dsimp only [z] at hlower; linarith only [hlower]
  · dsimp only [z] at hupper; linarith only [hupper]

private def extendSieveCoeff (Q : Finset Nat.Primes) (b : SieveClass Q → ℝ) (m : ℕ) : ℝ :=
  if hm : SieveSupported Q m then b ⟨m, hm⟩ else 0

private theorem sum_extendSieveCoeff_ramanujanPole (Q : Finset Nat.Primes)
    (R : ℕ) (b : SieveClass Q → ℝ) (n : ℕ) :
    (∑ m ∈ Icc 1 R, extendSieveCoeff Q b m * ramanujanPoleProfile m n) =
      ∑ m ∈ sieveClassPrefix Q R, b m * ramanujanPoleProfile m n := by
  let S := (sieveClassPrefix Q R).image (fun m : SieveClass Q => (m : ℕ))
  have hS : S ⊆ Icc 1 R := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hm
    exact mem_Icc.mpr ⟨a.property.pos, (mem_sieveClassPrefix Q R a).mp ha⟩
  have hzero (m : ℕ) (hm : m ∈ Icc 1 R) (hmS : m ∉ S) :
      extendSieveCoeff Q b m * ramanujanPoleProfile m n = 0 := by
    have hnot : ¬SieveSupported Q m := fun hsup =>
      hmS (mem_image.mpr ⟨⟨m, hsup⟩,
        (mem_sieveClassPrefix Q R ⟨m, hsup⟩).mpr (mem_Icc.mp hm).2, rfl⟩)
    rw [extendSieveCoeff, dif_neg hnot, zero_mul]
  calc
    _ = ∑ m ∈ S, extendSieveCoeff Q b m * ramanujanPoleProfile m n :=
      (sum_subset hS hzero).symm
    _ = ∑ m ∈ sieveClassPrefix Q R, extendSieveCoeff Q b (m : ℕ) * ramanujanPoleProfile m n :=
      sum_image fun _ _ _ _ h => Subtype.ext h
    _ = _ := sum_congr rfl fun m _ => by rw [extendSieveCoeff, dif_pos m.property]

private theorem exists_quant_cutoffs {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ K : ℝ, 0 ≤ K →
      ∃ P A R : ℕ, 1 < P ∧ 1 < A ∧ 1 < R ∧ A ^ 2 ≤ R ∧
        2 * ladderConstant P + 4 ≤ Real.log R ∧
        C₀ / Real.log P * K ≤ δ ∧
        (2 * K + 2 * ladderConstant P) / Real.log A ≤ δ ∧
        16 * (Real.log A + ladderConstant P) / Real.log R ≤ δ ∧
        Real.log R ≤ C / δ ^ 3 * (K + 1) := by
  let J : ℝ := Real.log 4 + 4
  have hJ : 0 < J := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    dsimp only [J]; linarith only [h]
  let B₁ : ℝ := C₀ + 3
  let B₂ : ℝ := 2 * B₁ + 2 * J
  let B₃ : ℝ := 2 * (1 + B₂) + 3
  let C : ℝ := 18 * B₃ + 18 * B₂ + 7
  refine ⟨C, by dsimp only [C, B₃, B₂, B₁]; positivity, fun δ hδ hδ1 K hK => ?_⟩
  have hK1 : 0 < K + 1 := by linarith only [hK]
  have hinv1 : 1 ≤ 1 / δ := one_le_div hδ |>.mpr hδ1
  have hinv2 : 1 / δ ≤ 1 / δ ^ 2 := by
    rw [one_div_le_one_div (sq_pos_of_pos hδ) hδ]
    nlinarith only [hδ.le, hδ1]
  have hinv3 : 1 / δ ^ 2 ≤ 1 / δ ^ 3 := by
    rw [one_div_le_one_div (pow_pos hδ 3) (sq_pos_of_pos hδ)]
    have hsq0 : 0 ≤ δ ^ 2 := sq_nonneg δ
    have hcube : δ ^ 3 = δ ^ 2 * δ := by ring
    rw [hcube]
    exact mul_le_of_le_one_right hsq0 hδ1
  obtain ⟨P, hP, hPlow, hPup⟩ := exists_nat_log_cutoff_quant
    (div_nonneg (mul_nonneg hC₀.le hK1.le) hδ.le)
  have hPR : (1 : ℝ) < P := by exact_mod_cast hP
  have hlogP : 0 < Real.log P := Real.log_pos hPR
  have hPbound : Real.log P ≤ (B₁ / δ) * (K + 1) := by
    calc
      Real.log P ≤ C₀ * (K + 1) / δ + 3 := hPup
      _ ≤ C₀ * (K + 1) / δ + 3 * (1 / δ) * (K + 1) := by
        have h1 : (1 : ℝ) ≤ (1 / δ) * (K + 1) := by nlinarith only [hinv1, hK]
        linarith only [h1]
      _ = (B₁ / δ) * (K + 1) := by dsimp only [B₁]; ring
  have hL0 := ladderConstant_nonneg P
  have hLbound : ladderConstant P ≤ (B₂ / δ) * (K + 1) := by
    have hL := ladderConstant_le_log (show 1 ≤ P by omega)
    change ladderConstant P ≤ 2 * (Real.log P + J) at hL
    have hJterm : 2 * J ≤ (2 * J / δ) * (K + 1) := by
      have h1 : (1 : ℝ) ≤ (1 / δ) * (K + 1) := by nlinarith only [hinv1, hK]
      have hm := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * J by positivity)
      linarith only [hm.trans_eq (by ring : 2 * J * ((1 / δ) * (K + 1)) = (2 * J / δ) * (K + 1))]
    calc
      ladderConstant P ≤ 2 * Real.log P + 2 * J := by linarith only [hL]
      _ ≤ 2 * ((B₁ / δ) * (K + 1)) + (2 * J / δ) * (K + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hPbound zero_le_two) hJterm
      _ = (B₂ / δ) * (K + 1) := by dsimp only [B₂]; ring
  obtain ⟨A, hA, hAlow, hAup⟩ := exists_nat_log_cutoff_quant
    (div_nonneg (mul_nonneg zero_le_two (add_nonneg hK hL0)) hδ.le)
  have hAR : (1 : ℝ) < A := by exact_mod_cast hA
  have hlogA : 0 < Real.log A := Real.log_pos hAR
  have hAbound : Real.log A ≤ (B₃ / δ ^ 2) * (K + 1) := by
    have hKL : K + ladderConstant P ≤ ((1 + B₂) / δ) * (K + 1) := by
      have hKterm : K + 1 ≤ (1 / δ) * (K + 1) :=
        (one_mul (K + 1)).symm.trans_le (mul_le_mul_of_nonneg_right hinv1 hK1.le)
      calc
        K + ladderConstant P ≤ (K + 1) + (B₂ / δ) * (K + 1) := by linarith only [hLbound]
        _ ≤ (1 / δ) * (K + 1) + (B₂ / δ) * (K + 1) := add_le_add hKterm le_rfl
        _ = ((1 + B₂) / δ) * (K + 1) := by ring
    have h3term : (3 : ℝ) ≤ (3 / δ ^ 2) * (K + 1) := by
      have h12 : (1 : ℝ) ≤ 1 / δ ^ 2 := hinv1.trans hinv2
      have h1 : (1 : ℝ) ≤ (1 / δ ^ 2) * (K + 1) :=
        (one_mul (1 : ℝ)).symm.trans_le (mul_le_mul h12 (by linarith only [hK]) zero_le_one
          (zero_le_one.trans h12))
      linarith only [(mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)).trans_eq
        (by ring : 3 * ((1 / δ ^ 2) * (K + 1)) = (3 / δ ^ 2) * (K + 1))]
    calc
      Real.log A ≤ 2 * (K + ladderConstant P) / δ + 3 := hAup
      _ ≤ 2 * (((1 + B₂) / δ) * (K + 1)) / δ + (3 / δ ^ 2) * (K + 1) :=
        add_le_add (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKL zero_le_two) hδ.le) h3term
      _ = (B₃ / δ ^ 2) * (K + 1) := by
        dsimp only [B₃]
        field_simp [hδ.ne']
        ring
  let z : ℝ := 2 * Real.log A + 2 * ladderConstant P + 4 +
    16 * (Real.log A + ladderConstant P) / δ
  have hfrac : 0 ≤ 16 * (Real.log A + ladderConstant P) / δ := by positivity
  obtain ⟨R, hR, hRlow, hRup⟩ := exists_nat_log_cutoff_quant (by dsimp only [z]; positivity : 0 ≤ z)
  have hRR : (1 : ℝ) < R := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos hRR
  have hARsq : A ^ 2 ≤ R := by
    have hlogs : Real.log ((A : ℝ) ^ 2) ≤ Real.log R := by
      rw [pow_two, Real.log_mul (zero_lt_one.trans hAR).ne' (zero_lt_one.trans hAR).ne']
      dsimp only [z] at hRlow
      linarith only [hRlow, hL0, hfrac]
    have he := Real.exp_le_exp.mpr hlogs
    rw [Real.exp_log (sq_pos_of_pos (zero_lt_one.trans hAR)),
      Real.exp_log (zero_lt_one.trans hRR)] at he
    exact_mod_cast he
  have hEuler : 2 * ladderConstant P + 4 ≤ Real.log R := by
    dsimp only [z] at hRlow; linarith only [hRlow, hlogA, hfrac]
  have hmean : C₀ / Real.log P * K ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hlogP]
    have hp := (div_le_iff₀ hδ).mp hPlow
    nlinarith only [hp, hC₀]
  have htail : (2 * K + 2 * ladderConstant P) / Real.log A ≤ δ := by
    apply (div_le_iff₀ hlogA).mpr
    have ha := (div_le_iff₀ hδ).mp hAlow
    nlinarith only [ha]
  have hmode : 16 * (Real.log A + ladderConstant P) / Real.log R ≤ δ := by
    apply (div_le_iff₀ hlogR).mpr
    have hf : 16 * (Real.log A + ladderConstant P) / δ ≤ Real.log R := by
      dsimp only [z] at hRlow; linarith only [hRlow, hlogA, hL0]
    have h := (div_le_iff₀ hδ).mp hf
    nlinarith only [h]
  have hRbound : Real.log R ≤ C / δ ^ 3 * (K + 1) := by
    have hB₂0 : 0 ≤ B₂ := by dsimp only [B₂, B₁]; positivity
    have hB₃0 : 0 ≤ B₃ := by dsimp only [B₃]; positivity
    have hA3 : Real.log A ≤ (B₃ / δ ^ 3) * (K + 1) :=
      hAbound.trans (mul_le_mul_of_nonneg_right
        (by simpa only [div_eq_mul_inv, one_div] using
          mul_le_mul_of_nonneg_left hinv3 hB₃0) hK1.le)
    have hL2 : ladderConstant P ≤ (B₂ / δ ^ 2) * (K + 1) :=
      hLbound.trans (mul_le_mul_of_nonneg_right
        (by simpa only [div_eq_mul_inv, one_div] using
          mul_le_mul_of_nonneg_left hinv2 hB₂0) hK1.le)
    have hL3 : ladderConstant P ≤ (B₂ / δ ^ 3) * (K + 1) :=
      hL2.trans (mul_le_mul_of_nonneg_right
        (by simpa only [div_eq_mul_inv, one_div] using
          mul_le_mul_of_nonneg_left hinv3 hB₂0) hK1.le)
    have hdiv : 16 * (Real.log A + ladderConstant P) / δ ≤
        ((16 * B₃ + 16 * B₂) / δ ^ 3) * (K + 1) := by
      have hsum : Real.log A + ladderConstant P ≤ ((B₃ + B₂) / δ ^ 2) * (K + 1) := by
        calc
          Real.log A + ladderConstant P ≤ (B₃ / δ ^ 2) * (K + 1) + (B₂ / δ ^ 2) * (K + 1) :=
            add_le_add hAbound hL2
          _ = ((B₃ + B₂) / δ ^ 2) * (K + 1) := by ring
      calc
        16 * (Real.log A + ladderConstant P) / δ ≤
            16 * (((B₃ + B₂) / δ ^ 2) * (K + 1)) / δ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hδ.le
        _ = ((16 * B₃ + 16 * B₂) / δ ^ 3) * (K + 1) := by
          field_simp [hδ.ne']
          ring
    have h7 : (7 : ℝ) ≤ (7 / δ ^ 3) * (K + 1) := by
      have h13 : (1 : ℝ) ≤ 1 / δ ^ 3 := (hinv1.trans hinv2).trans hinv3
      have h1 : (1 : ℝ) ≤ (1 / δ ^ 3) * (K + 1) :=
        (one_mul (1 : ℝ)).symm.trans_le (mul_le_mul h13 (by linarith only [hK]) zero_le_one
          (zero_le_one.trans h13))
      linarith only [(mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 7)).trans_eq
        (by ring : 7 * ((1 / δ ^ 3) * (K + 1)) = (7 / δ ^ 3) * (K + 1))]
    dsimp only [z] at hRup
    calc
      Real.log R ≤ 2 * Real.log A + 2 * ladderConstant P + 7 +
          16 * (Real.log A + ladderConstant P) / δ := by linarith only [hRup]
      _ ≤ 2 * ((B₃ / δ ^ 3) * (K + 1)) + 2 * ((B₂ / δ ^ 3) * (K + 1)) +
          (7 / δ ^ 3) * (K + 1) + ((16 * B₃ + 16 * B₂) / δ ^ 3) * (K + 1) :=
        add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hA3 zero_le_two)
          (mul_le_mul_of_nonneg_left hL3 zero_le_two)) h7) hdiv
      _ = C / δ ^ 3 * (K + 1) := by dsimp only [C]; ring
  exact ⟨P, A, R, hP, hA, hR, hARsq, hEuler, hmean, htail, hmode, hRbound⟩

/-- Quantitative exponential conductor confinement: for every `0 < η ≤ 1` and `K ≥ 0`, there is a
conductor cutoff `R ≥ 2` with `log R ≤ (C / η^3) (K + 1)` such that every horizon vector `z` with
`‖z‖ ≤ 1` and `poleDefect N (primeHorizonExtension z) ≤ K` lies within squared distance `η` of
`conductorSubspace R N`. -/
theorem exists_quantitative_exponential_conductor_cutoff_of_poleDefect_le :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ K : ℝ, 0 ≤ K →
      ∃ R : ℕ, 2 ≤ R ∧ Real.log R ≤ C / η ^ 3 * (K + 1) ∧
        ∀ N : ℕ, 2 ≤ N → ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
          ‖z‖ ≤ 1 → poleDefect N (primeHorizonExtension z) ≤ K →
          ‖z - (conductorSubspace R N).starProjection z‖ ^ 2 ≤ η := by
  obtain ⟨C₀, hC₀, hconditioning⟩ := exists_smoothRoughPoleProjection_error_le
  obtain ⟨C₁, hC₁, hcutoffs⟩ := exists_quant_cutoffs hC₀
  refine ⟨512 * C₁, by positivity, fun η hη hη1 K hK => ?_⟩
  let δ : ℝ := η / 8
  have hδ : 0 < δ := div_pos hη (by norm_num)
  have hδ1 : δ ≤ 1 := by dsimp only [δ]; linarith only [hη1]
  obtain ⟨P, A, R, hP, hA, hR, hAR, hEuler, hmeanBound, htailBound, hmodeBound, hRlog⟩ :=
    hcutoffs δ hδ hδ1 K hK
  have hRlog' : Real.log R ≤ (512 * C₁) / η ^ 3 * (K + 1) := by
    refine hRlog.trans_eq ?_
    dsimp only [δ]
    field_simp [hη.ne']
    ring
  refine ⟨R, by omega, hRlog', fun N hN2 z hznorm hdef => ?_⟩
  let x := primeHorizonExtension z
  have hmass : (∑ n ∈ Icc 1 N, x n ^ 2) ≤ 1 := by
    rw [sum_primeHorizonExtension_sq]
    nlinarith only [hznorm, norm_nonneg z]
  suffices hex : ∃ b : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, (x n - ∑ m ∈ Icc 1 R, b m * ramanujanPoleProfile m n) ^ 2) ≤ η by
    obtain ⟨b, hb⟩ := hex
    let v := ∑ m ∈ Icc 1 R, (b m * Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector m N
    have hv : v ∈ conductorSubspace R N :=
      sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N _
    exact (norm_sub_starProjection_sq_le (conductorSubspace R N) z v hv).trans
      ((norm_sub_normalizedRamanujan_sum_sq hN2 z b).trans_le hb)
  by_cases hRN : R ≤ N
  · have hPR : (1 : ℝ) < P := by exact_mod_cast hP
    have hAR' : (1 : ℝ) < A := by exact_mod_cast hA
    have hRR : (1 : ℝ) < R := by exact_mod_cast hR
    have hlogP : 0 < Real.log P := Real.log_pos hPR
    have hlogA : 0 < Real.log A := Real.log_pos hAR'
    have hL0 := ladderConstant_nonneg P
    have hAN : A ≤ N :=
      ((show A ≤ A ^ 2 by nlinarith only [hA]).trans hAR).trans hRN
    have hlogN : Real.log R ≤ Real.log (N + 1 : ℕ) :=
      Real.log_le_log (zero_lt_one.trans hRR) (by exact_mod_cast hRN.trans (Nat.le_succ N))
    have hNsieve : 2 * (sieveEuler (primePrefixSieve P) - Real.eulerMascheroniConstant) + 4 ≤
        Real.log (N + 1 : ℕ) := by
      rw [sieveEuler_primePrefix_sub_euler]
      exact hEuler.trans hlogN
    let f : ℕ → ℝ := smoothRoughMean P N x
    let g : ℕ → ℝ := fun n =>
      (if RHTower.Sieve.smoothPart (P - 1) n ≤ A then
        f (RHTower.Sieve.smoothPart (P - 1) n) else 0) / Real.sqrt n
    obtain ⟨b, hb⟩ := exists_sieveProfile_ramanujan_approximation (primePrefixSieve P) hR
      ((hAR.trans hRN).trans (Nat.le_succ N)) hNsieve (fun a => f a)
    rw [sieveEuler_primePrefix_sub_euler] at hb
    have hprofileMass :
        (∑ a ∈ sieveClassPrefix (primePrefixSieve P) A,
          sieveClassMass (primePrefixSieve P) a N * f a ^ 2) ≤ 1 :=
      (sum_smoothRoughMean_prefix_classMass_le P N hAN x).trans hmass
    have hpacketError : (∑ n ∈ Icc 1 N,
        (g n - ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R,
          b m * ramanujanPoleProfile m n) ^ 2) ≤ δ := by
      dsimp only [g]
      rw [smoothProfile_ramanujan_error_eq_classMass P A R N f b]
      have hcoef : 0 ≤ 16 * (Real.log A + ladderConstant P) / Real.log R := by
        have := Real.log_pos hRR; positivity
      exact (hb.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hprofileMass hcoef)).trans hmodeBound
    have hmeanError :
        (∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection P N x n) ^ 2) ≤ δ :=
      (hconditioning P (by omega) N x).trans
        ((mul_le_mul_of_nonneg_left hdef (div_nonneg hC₀.le hlogP.le)).trans hmeanBound)
    have hsmoothTail :
        (∑ n ∈ Icc 1 N, if A < RHTower.Sieve.smoothPart (P - 1) n then x n ^ 2 else 0) ≤ δ := by
      have hpaid := mul_le_mul_of_nonneg_left hmass (mul_nonneg zero_le_two hL0)
      have hnum : 2 * poleDefect N x + 2 * ladderConstant P * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
          2 * K + 2 * ladderConstant P := by nlinarith only [hdef, hpaid]
      exact (sum_outside_smoothPart_le P N hA x).trans
        ((div_le_div_of_nonneg_right hnum hlogA.le).trans htailBound)
    have hpreError : (∑ n ∈ Icc 1 N, (x n - g n) ^ 2) ≤ 2 * δ := by
      calc
        _ ≤ ∑ n ∈ Icc 1 N, ((x n - smoothRoughPoleProjection P N x n) ^ 2 +
            if A < RHTower.Sieve.smoothPart (P - 1) n then x n ^ 2 else 0) := by
          refine sum_le_sum fun n _ => ?_
          by_cases hn : RHTower.Sieve.smoothPart (P - 1) n ≤ A
          · simp only [g, f, if_pos hn, if_neg (not_lt.mpr hn), add_zero, smoothRoughPoleProjection]
            exact le_rfl
          · simp only [g, if_neg hn, if_pos (not_le.mp hn), zero_div, sub_zero]
            exact le_add_of_nonneg_left (sq_nonneg _)
        _ = (∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection P N x n) ^ 2) +
            ∑ n ∈ Icc 1 N, if A < RHTower.Sieve.smoothPart (P - 1) n then x n ^ 2 else 0 :=
          sum_add_distrib
        _ ≤ δ + δ := add_le_add hmeanError hsmoothTail
        _ = 2 * δ := by ring
    refine ⟨extendSieveCoeff (primePrefixSieve P) b, ?_⟩
    simp_rw [sum_extendSieveCoeff_ramanujanPole (primePrefixSieve P) R b]
    calc
      _ ≤ ∑ n ∈ Icc 1 N,
          (2 * (x n - g n) ^ 2 + 2 * (g n -
            ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m n) ^ 2) :=
        sum_le_sum fun n _ => by
          nlinarith only [sq_nonneg ((x n - g n) - (g n -
            ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m n))]
      _ = 2 * (∑ n ∈ Icc 1 N, (x n - g n) ^ 2) +
          2 * ∑ n ∈ Icc 1 N, (g n -
            ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m n) ^ 2 := by
        simp only [sum_add_distrib, mul_sum]
      _ ≤ 2 * (2 * δ) + 2 * δ := add_le_add
        (mul_le_mul_of_nonneg_left hpreError zero_le_two)
        (mul_le_mul_of_nonneg_left hpacketError zero_le_two)
      _ ≤ η := by dsimp only [δ]; linarith only [hη]
  · obtain ⟨b, hb⟩ := exists_horizon_ramanujanPole_expansion N x
    refine ⟨fun m => if m ≤ N then b m else 0, ?_⟩
    have hNR : N ≤ R := (lt_of_not_ge hRN).le
    have hsub : Icc 1 N ⊆ Icc 1 R := Icc_subset_Icc le_rfl hNR
    have hzero : (∑ n ∈ Icc 1 N,
        (x n - ∑ m ∈ Icc 1 R, (if m ≤ N then b m else 0) * ramanujanPoleProfile m n) ^ 2) = 0 := by
      refine sum_eq_zero fun n hn => ?_
      have hs : (∑ m ∈ Icc 1 R, (if m ≤ N then b m else 0) * ramanujanPoleProfile m n) =
          ∑ m ∈ Icc 1 N, b m * ramanujanPoleProfile m n := by
        calc
          _ = ∑ m ∈ Icc 1 N, (if m ≤ N then b m else 0) * ramanujanPoleProfile m n :=
            (sum_subset hsub fun m hm hmN => by
              have hnot : ¬m ≤ N := fun h => hmN (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
              rw [if_neg hnot, zero_mul]).symm
          _ = _ := sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]
      rw [hs, ← hb n hn, sub_self, zero_pow (by decide)]
    rw [hzero]
    exact hη.le

/-- The absolute exponential confinement constant at approximation threshold `η₀ = 1/16`. -/
def conductorCutoffConstant : ℝ :=
  Classical.choose (exists_exponential_conductor_cutoff_of_poleDefect_le
    (by norm_num : (0 : ℝ) < 1 / 16))

theorem conductorCutoffConstant_pos : 0 < conductorCutoffConstant :=
  (Classical.choose_spec (exists_exponential_conductor_cutoff_of_poleDefect_le
    (by norm_num : (0 : ℝ) < 1 / 16))).1

/-- Reverse prime-defect gap: any vector `y` whose squared distance from `conductorSubspace Q N`
exceeds `(1 / 16) ‖y‖^2` has `poleDefect` at least `(log Q / conductorCutoffConstant - 1) ‖y‖^2`. -/
theorem poleDefect_ge_of_norm_sub_starProjection_gt {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 2 ≤ N)
    {y : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hdist : (1 / 16 : ℝ) * ‖y‖ ^ 2 < ‖y - (conductorSubspace Q N).starProjection y‖ ^ 2) :
    (Real.log Q / conductorCutoffConstant - 1) * ‖y‖ ^ 2 ≤
      poleDefect N (primeHorizonExtension y) := by
  have hy0 : ‖y‖ ≠ 0 := by
    intro hz
    rw [norm_eq_zero.mp hz] at hdist
    simp at hdist
  have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
  let z := (‖y‖)⁻¹ • y
  have hznorm : (∑ n ∈ Icc 1 N, primeHorizonExtension z n ^ 2) ≤ 1 := by
    rw [sum_primeHorizonExtension_sq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hypos,
      inv_mul_cancel₀ hy0, one_pow]
  let K := poleDefect N (primeHorizonExtension z)
  have hK0 : 0 ≤ K := poleDefect_nonneg N _
  obtain ⟨R, hRexp, happ⟩ := (Classical.choose_spec
    (exists_exponential_conductor_cutoff_of_poleDefect_le (by norm_num : (0 : ℝ) < 1 / 16))).2 K hK0
  change (R : ℝ) ≤ Real.exp (conductorCutoffConstant * (K + 1)) at hRexp
  obtain ⟨b, hb⟩ := happ N (primeHorizonExtension z) hznorm le_rfl
  have hQR : Q < R := by
    by_contra hnot
    have hRQ : R ≤ Q := le_of_not_gt hnot
    let v := ∑ m ∈ Icc 1 R, (b m * Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector m N
    have hvQ : ‖y‖ • v ∈ conductorSubspace Q N :=
      conductorSubspace_mono hRQ N
        (Submodule.smul_mem _ _ (sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N _))
    have hzv : ‖z - v‖ ^ 2 ≤ 1 / 16 :=
      (norm_sub_normalizedRamanujan_sum_sq hN z b).trans_le hb
    have hyv : ‖y - ‖y‖ • v‖ ^ 2 ≤ (1 / 16) * ‖y‖ ^ 2 := by
      have hid : y - ‖y‖ • v = ‖y‖ • (z - v) := by
        dsimp only [z]
        rw [smul_sub, smul_smul, mul_inv_cancel₀ hy0, one_smul]
      rw [hid, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right hzv (sq_nonneg _)
    linarith only [hdist, norm_sub_starProjection_sq_le (conductorSubspace Q N) y (‖y‖ • v) hvQ, hyv]
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQlt : (Q : ℝ) < Real.exp (conductorCutoffConstant * (K + 1)) :=
    (show (Q : ℝ) < R by exact_mod_cast hQR).trans_le hRexp
  have hlogQ : Real.log Q ≤ conductorCutoffConstant * (K + 1) := by
    simpa only [Real.log_exp] using (Real.log_le_log hQpos hQlt.le)
  have hD0 : 0 < conductorCutoffConstant := conductorCutoffConstant_pos
  have hKge : Real.log Q / conductorCutoffConstant - 1 ≤ K := by
    rw [sub_le_iff_le_add, div_le_iff₀ hD0]
    linarith only [hlogQ]
  have hKeq : K * ‖y‖ ^ 2 = poleDefect N (primeHorizonExtension y) := by
    dsimp only [K, z]
    rw [primeHorizonExtension_smul, poleDefect_smul, inv_pow]
    field_simp [hy0]
  exact (mul_le_mul_of_nonneg_right hKge (sq_nonneg ‖y‖)).trans_eq hKeq

/-! ### 3. Polarized harmonic Gram bounds and band decoupling -/

/-- Uniform squared-norm Gram discrepancy below the square-root horizon `Q * Q ≤ N`. -/
theorem abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N) (a : ℕ → ℝ) :
    |‖∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 -
        ∑ m ∈ Icc 1 Q, a m ^ 2| ≤
      9 * (1 + Real.log Q) / Real.log N * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  have hN4 : 4 ≤ N := (Nat.mul_le_mul hQ hQ).trans hQN
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsq_eq : (∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) ^ 2) =
      ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ) := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hs : (∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) =
        (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) / Real.sqrt n := by
      rw [sum_div]
      exact sum_congr rfl fun m _ => by rw [ramanujanPoleProfile, mul_div_assoc]
    rw [hs, div_pow, Real.sq_sqrt hn0.le]
  have hgram := abs_harmonicGram_sub_log_mass_le hQ (by omega : 1 ≤ N) a
  have hdiv : |‖∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 -
      ∑ m ∈ Icc 1 Q, a m ^ 2| =
      |(∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) -
        Real.log N * ∑ m ∈ Icc 1 Q, a m ^ 2| / Real.log N := by
    rw [norm_sum_normalizedRamanujanHorizonVector_sq, hsq_eq, ← abs_of_pos hL, ← abs_div]
    congr 1
    field_simp [hL.ne']
  rw [hdiv]
  have hγ : |Real.eulerMascheroniConstant| ≤ 1 := by
    rw [abs_le]
    have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 0
    simp [Real.eulerMascheroniSeq] at h1
    have h2 := Real.eulerMascheroniConstant_lt_two_thirds
    constructor <;> linarith
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    linarith only [h]
  have hquad : (Q : ℝ) * ((Q : ℝ) - 1) / ((N : ℝ) + 1) ≤ 1 := by
    have h : (Q : ℝ) * Q ≤ N := by exact_mod_cast hQN
    rw [div_le_one (by positivity)]
    nlinarith only [h, Nat.cast_nonneg (α := ℝ) Q]
  have hinvN : 1 / (N : ℝ) ≤ 1 := div_le_self zero_le_one (by exact_mod_cast (show 1 ≤ N by omega))
  have hcoef : |Real.eulerMascheroniConstant| + 4 * Real.log Q + (Real.log 4 + 4) +
      (Q : ℝ) * ((Q : ℝ) - 1) / ((N : ℝ) + 1) + 1 / N ≤ 9 * (1 + Real.log Q) := by
    linarith only [hγ, hlog4, hquad, hinvN, Real.log_natCast_nonneg Q]
  have hM : 0 ≤ ∑ m ∈ Icc 1 Q, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  exact (div_le_div_of_nonneg_right
    (hgram.trans (mul_le_mul_of_nonneg_right hcoef hM)) hL.le).trans_eq (by ring)

/-- Polarized off-diagonal Gram bound: any two conductor combinations over `Icc 1 Q` (`Q * Q ≤ N`)
with orthogonal coefficient sequences have inner product bounded by `9 (1 + log Q) / log N` times
the product of their `ℓ²` coefficient norms. -/
theorem abs_inner_sum_normalizedRamanujanHorizonVector_of_orthog_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N) {a b : ℕ → ℝ}
    (horth : (∑ m ∈ Icc 1 Q, a m * b m) = 0) :
    |⟪∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N,
        ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N⟫| ≤
      9 * (1 + Real.log Q) / Real.log N *
        Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) * Real.sqrt (∑ m ∈ Icc 1 Q, b m ^ 2) := by
  let A := ∑ m ∈ Icc 1 Q, a m ^ 2
  let B := ∑ m ∈ Icc 1 Q, b m ^ 2
  have hA0 : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => sq_nonneg _
  by_cases hAz : A = 0
  · have ha0 : ∀ m ∈ Icc 1 Q, a m = 0 := fun m hm =>
      sq_eq_zero_iff.mp ((sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (a k))).mp hAz m hm)
    have hu0 : (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) = 0 :=
      sum_eq_zero fun m hm => by rw [ha0 m hm, zero_smul]
    simp [A, hAz, hu0]
  by_cases hBz : B = 0
  · have hb0 : ∀ m ∈ Icc 1 Q, b m = 0 := fun m hm =>
      sq_eq_zero_iff.mp ((sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (b k))).mp hBz m hm)
    have hv0 : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) = 0 :=
      sum_eq_zero fun m hm => by rw [hb0 m hm, zero_smul]
    simp [B, hBz, hv0]
  have hAp : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
  have hBp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBz)
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hAp
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBp
  let a' : ℕ → ℝ := fun m => a m / Real.sqrt A
  let b' : ℕ → ℝ := fun m => b m / Real.sqrt B
  have ha'sq : (∑ m ∈ Icc 1 Q, a' m ^ 2) = 1 := by
    have h1 : (∑ m ∈ Icc 1 Q, a' m ^ 2) = A / A := by
      dsimp only [a', A]
      rw [← sum_div]
      exact sum_congr rfl fun m _ => by rw [div_pow, Real.sq_sqrt hAp.le]
    rw [h1, div_self hAp.ne']
  have hb'sq : (∑ m ∈ Icc 1 Q, b' m ^ 2) = 1 := by
    have h1 : (∑ m ∈ Icc 1 Q, b' m ^ 2) = B / B := by
      dsimp only [b', B]
      rw [← sum_div]
      exact sum_congr rfl fun m _ => by rw [div_pow, Real.sq_sqrt hBp.le]
    rw [h1, div_self hBp.ne']
  have horth' : (∑ m ∈ Icc 1 Q, a' m * b' m) = 0 := by
    have h1 : (∑ m ∈ Icc 1 Q, a' m * b' m) =
        (∑ m ∈ Icc 1 Q, a m * b m) / (Real.sqrt A * Real.sqrt B) := by
      rw [sum_div]
      exact sum_congr rfl fun m _ => by dsimp only [a', b']; ring
    rw [h1, horth, zero_div]
  have hplus_mass : (∑ m ∈ Icc 1 Q, (a' m + b' m) ^ 2) = 2 := by
    have hexp : (∑ m ∈ Icc 1 Q, (a' m + b' m) ^ 2) =
        (∑ m ∈ Icc 1 Q, a' m ^ 2) + (∑ m ∈ Icc 1 Q, b' m ^ 2) +
          2 * ∑ m ∈ Icc 1 Q, a' m * b' m := by
      rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun m _ => by ring
    rw [hexp, ha'sq, hb'sq, horth']
    norm_num
  have hminus_mass : (∑ m ∈ Icc 1 Q, (a' m - b' m) ^ 2) = 2 := by
    have hexp : (∑ m ∈ Icc 1 Q, (a' m - b' m) ^ 2) =
        (∑ m ∈ Icc 1 Q, a' m ^ 2) + (∑ m ∈ Icc 1 Q, b' m ^ 2) -
          2 * ∑ m ∈ Icc 1 Q, a' m * b' m := by
      rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun m _ => by ring
    rw [hexp, ha'sq, hb'sq, horth']
    norm_num
  let u' := ∑ m ∈ Icc 1 Q, a' m • normalizedRamanujanHorizonVector m N
  let v' := ∑ m ∈ Icc 1 Q, b' m • normalizedRamanujanHorizonVector m N
  have hu'pv' : (∑ m ∈ Icc 1 Q, (a' m + b' m) • normalizedRamanujanHorizonVector m N) = u' + v' := by
    simp only [u', v', add_smul, sum_add_distrib]
  have hu'mv' : (∑ m ∈ Icc 1 Q, (a' m - b' m) • normalizedRamanujanHorizonVector m N) = u' - v' := by
    simp only [u', v', sub_smul, sum_sub_distrib]
  have hgp := abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hQ hQN (fun m => a' m + b' m)
  have hgm := abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hQ hQN (fun m => a' m - b' m)
  rw [hu'pv', hplus_mass] at hgp
  rw [hu'mv', hminus_mass] at hgm
  have hpol : ‖u' + v'‖ ^ 2 - ‖u' - v'‖ ^ 2 = 4 * ⟪u', v'⟫ := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm v' u']
    ring
  have h4 : 4 * |⟪u', v'⟫| ≤ 4 * (9 * (1 + Real.log Q) / Real.log N) := by
    have habs : |4 * ⟪u', v'⟫| ≤
        |‖u' + v'‖ ^ 2 - 2| + |‖u' - v'‖ ^ 2 - 2| := by
      rw [← hpol]
      calc
        |‖u' + v'‖ ^ 2 - ‖u' - v'‖ ^ 2| = |(‖u' + v'‖ ^ 2 - 2) - (‖u' - v'‖ ^ 2 - 2)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    rw [abs_mul, show |(4 : ℝ)| = 4 by norm_num] at habs
    linarith only [habs, hgp, hgm]
  have hu_eq : (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) = Real.sqrt A • u' := by
    dsimp only [u', a']
    rw [Finset.smul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [smul_smul, mul_div_cancel₀ _ hsA.ne']
  have hv_eq : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) = Real.sqrt B • v' := by
    dsimp only [v', b']
    rw [Finset.smul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [smul_smul, mul_div_cancel₀ _ hsB.ne']
  rw [hu_eq, hv_eq, real_inner_smul_left, real_inner_smul_right, abs_mul, abs_mul,
    abs_of_pos hsA, abs_of_pos hsB]
  have h1 : |⟪u', v'⟫| ≤ 9 * (1 + Real.log Q) / Real.log N := by linarith only [h4]
  calc
    Real.sqrt A * (Real.sqrt B * |⟪u', v'⟫|) ≤
        Real.sqrt A * (Real.sqrt B * (9 * (1 + Real.log Q) / Real.log N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hsB.le) hsA.le
    _ = 9 * (1 + Real.log Q) / Real.log N * Real.sqrt A * Real.sqrt B := by ring

/-- Two-sided Riesz bounds `(1/2) ∑ a_m^2 ≤ ‖u‖^2 ≤ (3/2) ∑ a_m^2` once
`18 * (1 + log Q) ≤ log N` and `Q * Q ≤ N`. -/
theorem half_and_three_halves_riesz_of_log_le {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N) (a : ℕ → ℝ) :
    (1 / 2 : ℝ) * (∑ m ∈ Icc 1 Q, a m ^ 2) ≤
        ‖∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ∧
      ‖∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        (3 / 2 : ℝ) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  have hL : 0 < Real.log N := by
    have hQ0 : 0 ≤ Real.log (Q : ℝ) := Real.log_natCast_nonneg Q
    linarith only [hlog, hQ0]
  have hfrac : 9 * (1 + Real.log Q) / Real.log N ≤ 1 / 2 := by
    rw [div_le_iff₀ hL]
    linarith only [hlog]
  have hM : 0 ≤ ∑ m ∈ Icc 1 Q, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have habs := (abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hQ hQN a).trans
    (mul_le_mul_of_nonneg_right hfrac hM)
  rcases abs_le.mp habs with ⟨hlo, hhi⟩
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

/-- Low-band leak bound: if `u = ∑_{m=1}^R a_m v_m` is orthogonal to `conductorSubspace Q N`
(`1 ≤ Q ≤ R`, `2 ≤ R`, `R * R ≤ N`, `18 * (1 + log R) ≤ log N`), then both its low-band `ℓ²`
coefficient norm and Euclidean low-band norm `‖∑_{m=1}^Q a_m v_m‖` are `O((1 + log R) / log N) ‖u‖`. -/
theorem low_band_norm_le_of_mem_orthogonal {Q R N : ℕ} (hQ1 : 1 ≤ Q) (hQR : Q ≤ R)
    (hR2 : 2 ≤ R) (hRN : R * R ≤ N) (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {a : ℕ → ℝ}
    (horth : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
      (conductorSubspace Q N)ᗮ) :
    Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) ≤
        36 * (1 + Real.log R) / Real.log N *
          ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ∧
      ‖∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N‖ ≤
        54 * (1 + Real.log R) / Real.log N *
          ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ := by
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let aLow : ℕ → ℝ := fun m => if m ≤ Q then a m else 0
  let aHigh : ℕ → ℝ := fun m => if m ≤ Q then 0 else a m
  have huLow_eq : (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) =
      ∑ m ∈ Icc 1 R, aLow m • normalizedRamanujanHorizonVector m N := by
    have hsub : Icc 1 Q ⊆ Icc 1 R := Icc_subset_Icc le_rfl hQR
    calc
      _ = ∑ m ∈ Icc 1 Q, aLow m • normalizedRamanujanHorizonVector m N :=
        sum_congr rfl fun m hm => by simp [aLow, (mem_Icc.mp hm).2]
      _ = _ := sum_subset hsub fun m hmR hmQ => by
        have hnot : ¬m ≤ Q := fun h => hmQ (mem_Icc.mpr ⟨(mem_Icc.mp hmR).1, h⟩)
        simp [aLow, hnot]
  have haLow_sq : (∑ m ∈ Icc 1 R, aLow m ^ 2) = ∑ m ∈ Icc 1 Q, a m ^ 2 := by
    have hsub : Icc 1 Q ⊆ Icc 1 R := Icc_subset_Icc le_rfl hQR
    calc
      _ = ∑ m ∈ Icc 1 Q, aLow m ^ 2 := (sum_subset hsub fun m hmR hmQ => by
          have hnot : ¬m ≤ Q := fun h => hmQ (mem_Icc.mpr ⟨(mem_Icc.mp hmR).1, h⟩)
          simp [aLow, hnot]).symm
      _ = _ := sum_congr rfl fun m hm => by simp [aLow, (mem_Icc.mp hm).2]
  have hsplit : u = (∑ m ∈ Icc 1 R, aLow m • normalizedRamanujanHorizonVector m N) +
      ∑ m ∈ Icc 1 R, aHigh m • normalizedRamanujanHorizonVector m N := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    dsimp only [aLow, aHigh]
    split_ifs <;> simp
  have hmemLow : (∑ m ∈ Icc 1 R, aLow m • normalizedRamanujanHorizonVector m N) ∈
      conductorSubspace Q N := by
    rw [← huLow_eq]
    exact sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q N a
  have hinner0 : ⟪∑ m ∈ Icc 1 R, aLow m • normalizedRamanujanHorizonVector m N, u⟫ = 0 :=
    (Submodule.mem_orthogonal (conductorSubspace Q N) u).mp horth _ hmemLow
  have hdisj : (∑ m ∈ Icc 1 R, aLow m * aHigh m) = 0 :=
    sum_eq_zero fun m _ => by dsimp only [aLow, aHigh]; split_ifs <;> ring
  let uLow := ∑ m ∈ Icc 1 R, aLow m • normalizedRamanujanHorizonVector m N
  let uHigh := ∑ m ∈ Icc 1 R, aHigh m • normalizedRamanujanHorizonVector m N
  have hself_eq : ‖uLow‖ ^ 2 = -⟪uLow, uHigh⟫ := by
    have h1 : ⟪uLow, uLow + uHigh⟫ = 0 := by rwa [← hsplit]
    rw [inner_add_right, real_inner_self_eq_norm_sq] at h1
    linarith only [h1]
  have hoff := abs_inner_sum_normalizedRamanujanHorizonVector_of_orthog_le hR2 hRN hdisj
  have hrieszLow := half_and_three_halves_riesz_of_log_le hR2 hRN hlog aLow
  have hrieszU := half_and_three_halves_riesz_of_log_le hR2 hRN hlog a
  have hHigh_le : (∑ m ∈ Icc 1 R, aHigh m ^ 2) ≤ 2 * ‖u‖ ^ 2 := by
    have hle : (∑ m ∈ Icc 1 R, aHigh m ^ 2) ≤ ∑ m ∈ Icc 1 R, a m ^ 2 :=
      sum_le_sum fun m _ => by dsimp only [aHigh]; split_ifs <;> simp [sq_nonneg]
    linarith only [hle, hrieszU.1]
  have hsHigh : Real.sqrt (∑ m ∈ Icc 1 R, aHigh m ^ 2) ≤ 2 * ‖u‖ := by
    calc
      Real.sqrt (∑ m ∈ Icc 1 R, aHigh m ^ 2) ≤ Real.sqrt (4 * ‖u‖ ^ 2) :=
        Real.sqrt_le_sqrt (hHigh_le.trans (by nlinarith only [sq_nonneg ‖u‖]))
      _ = 2 * ‖u‖ := by
        rw [show (4 : ℝ) * ‖u‖ ^ 2 = (2 * ‖u‖) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
  have hL : 0 < Real.log N := by
    have hR0 : 0 ≤ Real.log (R : ℝ) := Real.log_natCast_nonneg R
    linarith only [hlog, hR0]
  have hcoef0 : 0 ≤ 9 * (1 + Real.log R) / Real.log N := by
    have := Real.log_natCast_nonneg R; positivity
  have hbound_sq : (1 / 2 : ℝ) * Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) ^ 2 ≤
      (18 * (1 + Real.log R) / Real.log N * ‖u‖) * Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) := by
    rw [Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _), ← haLow_sq]
    calc
      (1 / 2 : ℝ) * (∑ m ∈ Icc 1 R, aLow m ^ 2) ≤ ‖uLow‖ ^ 2 := hrieszLow.1
      _ = |‖uLow‖ ^ 2| := (abs_of_nonneg (sq_nonneg _)).symm
      _ = |⟪uLow, uHigh⟫| := by rw [hself_eq, abs_neg]
      _ ≤ 9 * (1 + Real.log R) / Real.log N *
            Real.sqrt (∑ m ∈ Icc 1 R, aLow m ^ 2) * Real.sqrt (∑ m ∈ Icc 1 R, aHigh m ^ 2) := hoff
      _ ≤ 9 * (1 + Real.log R) / Real.log N *
            Real.sqrt (∑ m ∈ Icc 1 R, aLow m ^ 2) * (2 * ‖u‖) :=
        mul_le_mul_of_nonneg_left hsHigh (mul_nonneg hcoef0 (Real.sqrt_nonneg _))
      _ = (18 * (1 + Real.log R) / Real.log N * ‖u‖) * Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) := by
        rw [haLow_sq]; ring
  have hsLow : Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) ≤
      36 * (1 + Real.log R) / Real.log N * ‖u‖ := by
    by_cases hz : Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) = 0
    · rw [hz]; positivity
    · have hpos : 0 < Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      nlinarith only [hbound_sq, hpos]
  refine ⟨hsLow, ?_⟩
  rw [huLow_eq]
  have hnorm_le : ‖uLow‖ ≤ (3 / 2 : ℝ) * Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) := by
    have h2 : ‖uLow‖ ^ 2 ≤ ((3 / 2 : ℝ) * Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2)) ^ 2 := by
      have hsq := hrieszLow.2
      rw [haLow_sq] at hsq
      have h94 : (3 / 2 : ℝ) ≤ (3 / 2 : ℝ) ^ 2 := by norm_num
      calc
        ‖uLow‖ ^ 2 ≤ (3 / 2 : ℝ) * ∑ m ∈ Icc 1 Q, a m ^ 2 := hsq
        _ ≤ (3 / 2 : ℝ) ^ 2 * ∑ m ∈ Icc 1 Q, a m ^ 2 :=
          mul_le_mul_of_nonneg_right h94 (sum_nonneg fun _ _ => sq_nonneg _)
        _ = ((3 / 2 : ℝ) * Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
    have hrhs0 : 0 ≤ (3 / 2 : ℝ) * Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) := by positivity
    nlinarith only [h2, norm_nonneg uLow, hrhs0]
  calc
    ‖uLow‖ ≤ (3 / 2 : ℝ) * Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) := hnorm_le
    _ ≤ (3 / 2 : ℝ) * (36 * (1 + Real.log R) / Real.log N * ‖u‖) :=
      mul_le_mul_of_nonneg_left hsLow (by norm_num)
    _ = 54 * (1 + Real.log R) / Real.log N * ‖u‖ := by ring

/-- Reverse defect gap on any conductor packet `y = ∑_{m=1}^R a_m v_m` whose coefficients vanish
on `Icc 1 Q` (`2 ≤ Q ≤ R`, `R * R ≤ N`, `36 * (1 + log R) ≤ log N`). -/
theorem poleDefect_ge_of_supported_above {Q R N : ℕ} (hQ : 2 ≤ Q) (hQR : Q ≤ R)
    (hRN : R * R ≤ N) (hlog : 36 * (1 + Real.log R) ≤ Real.log N)
    {a : ℕ → ℝ} (hzero : ∀ m ∈ Icc 1 Q, a m = 0) :
    (Real.log Q / conductorCutoffConstant - 1) *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      poleDefect N (primeHorizonExtension
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N)) := by
  let y := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  have hR2 : 2 ≤ R := hQ.trans hQR
  have hN2 : 2 ≤ N := by
    have h4 : 4 ≤ N := (Nat.mul_le_mul hR2 hR2).trans hRN
    omega
  by_cases hy0 : ‖y‖ = 0
  · have hy_eq : y = 0 := norm_eq_zero.mp hy0
    have hdef0 : poleDefect N (primeHorizonExtension y) = 0 := by
      have hp0 : primeHorizonExtension y = 0 := by
        rw [hy_eq, ← zero_smul ℝ (0 : EuclideanSpace ℝ (PrimeHorizonIndex N)),
          primeHorizonExtension_smul, zero_smul]
      rw [hp0, ← zero_smul ℝ (0 : ℕ → ℝ), poleDefect_smul]
      norm_num
    rw [hy0, hdef0]
    norm_num
  have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
  apply poleDefect_ge_of_norm_sub_starProjection_gt hQ hN2
  let v := (conductorSubspace Q N).starProjection y
  obtain ⟨b, -, hv_eq⟩ :=
    (mem_conductorSubspace_iff (M := Q) (N := N) (x := v)).mp
      ((conductorSubspace Q N).starProjection_apply_mem y)
  let b' : ℕ → ℝ := fun m => if m ≤ Q then b m else 0
  have hv_R : v = ∑ m ∈ Icc 1 R, b' m • normalizedRamanujanHorizonVector m N := by
    rw [hv_eq]
    have hsub : Icc 1 Q ⊆ Icc 1 R := Icc_subset_Icc le_rfl hQR
    calc
      _ = ∑ m ∈ Icc 1 Q, b' m • normalizedRamanujanHorizonVector m N :=
        sum_congr rfl fun m hm => by simp [b', (mem_Icc.mp hm).2]
      _ = _ := sum_subset hsub fun m hmR hmQ => by
        have hnot : ¬m ≤ Q := fun h => hmQ (mem_Icc.mpr ⟨(mem_Icc.mp hmR).1, h⟩)
        simp [b', hnot]
  have hdisj : (∑ m ∈ Icc 1 R, a m * b' m) = 0 := by
    refine sum_eq_zero fun m hm => ?_
    dsimp only [b']
    split_ifs with hmQ
    · rw [hzero m (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, hmQ⟩), zero_mul]
    · rw [mul_zero]
  have hlog18 : 18 * (1 + Real.log R) ≤ Real.log N := by
    have hR0 := Real.log_natCast_nonneg R
    linarith only [hlog, hR0]
  have hL : 0 < Real.log N := by
    have hR0 := Real.log_natCast_nonneg R
    linarith only [hlog, hR0]
  have hoff := abs_inner_sum_normalizedRamanujanHorizonVector_of_orthog_le hR2 hRN hdisj
  rw [← hv_R] at hoff
  have hry := (half_and_three_halves_riesz_of_log_le hR2 hRN hlog18 a).1
  have hrv := (half_and_three_halves_riesz_of_log_le hR2 hRN hlog18 b').1
  rw [← hv_R] at hrv
  have hprod_sqrt :
      Real.sqrt (∑ m ∈ Icc 1 R, a m ^ 2) * Real.sqrt (∑ m ∈ Icc 1 R, b' m ^ 2) ≤
        2 * ‖y‖ * ‖v‖ := by
    rw [← Real.sqrt_mul (sum_nonneg fun _ _ => sq_nonneg _)]
    have hmul : (∑ m ∈ Icc 1 R, a m ^ 2) * (∑ m ∈ Icc 1 R, b' m ^ 2) ≤
        (2 * ‖y‖ * ‖v‖) ^ 2 := by
      calc
        (∑ m ∈ Icc 1 R, a m ^ 2) * (∑ m ∈ Icc 1 R, b' m ^ 2) ≤
            (2 * ‖y‖ ^ 2) * (2 * ‖v‖ ^ 2) :=
          mul_le_mul (by linarith only [hry]) (by linarith only [hrv])
            (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = (2 * ‖y‖ * ‖v‖) ^ 2 := by ring
    exact (Real.sqrt_le_sqrt hmul).trans_eq (Real.sqrt_sq (by positivity))
  have hfrac_half : 18 * (1 + Real.log R) / Real.log N ≤ 1 / 2 := by
    rw [div_le_iff₀ hL]
    linarith only [hlog]
  have hy_v : |⟪y, v⟫| ≤ (1 / 2 : ℝ) * ‖y‖ * ‖v‖ := by
    have hcoef0 : 0 ≤ 9 * (1 + Real.log R) / Real.log N := by
      have := Real.log_natCast_nonneg R; positivity
    calc
      |⟪y, v⟫| ≤ 9 * (1 + Real.log R) / Real.log N *
          (Real.sqrt (∑ m ∈ Icc 1 R, a m ^ 2) * Real.sqrt (∑ m ∈ Icc 1 R, b' m ^ 2)) := by
        linarith only [hoff.trans_eq (by ring)]
      _ ≤ 9 * (1 + Real.log R) / Real.log N * (2 * ‖y‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left hprod_sqrt hcoef0
      _ = (18 * (1 + Real.log R) / Real.log N) * (‖y‖ * ‖v‖) := by ring
      _ ≤ (1 / 2 : ℝ) * (‖y‖ * ‖v‖) := mul_le_mul_of_nonneg_right hfrac_half (by positivity)
      _ = (1 / 2 : ℝ) * ‖y‖ * ‖v‖ := by ring
  have hpyth := norm_starProjection_sq_add_sub_sq (conductorSubspace Q N) y
  change ‖v‖ ^ 2 + ‖y - v‖ ^ 2 = ‖y‖ ^ 2 at hpyth
  have hv_sq_eq : ‖v‖ ^ 2 = ⟪y, v⟫ := by
    have h0 : ⟪y - v, v⟫ = 0 :=
      (conductorSubspace Q N).starProjection_inner_eq_zero y v
        ((conductorSubspace Q N).starProjection_apply_mem y)
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h0
    linarith only [h0]
  have hv_le : ‖v‖ ≤ (1 / 2 : ℝ) * ‖y‖ := by
    have hsq : ‖v‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖y‖ * ‖v‖ := by
      rw [hv_sq_eq]
      exact (le_abs_self _).trans hy_v
    by_cases hvz : ‖v‖ = 0
    · rw [hvz]; positivity
    · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hvz)
      nlinarith only [hsq, hvpos]
  have hv_sq_le : ‖v‖ ^ 2 ≤ (1 / 4 : ℝ) * ‖y‖ ^ 2 := by
    nlinarith only [hv_le, norm_nonneg v, hypos]
  have hy_pos_sq : 0 < ‖y‖ ^ 2 := sq_pos_of_pos hypos
  nlinarith only [hpyth, hv_sq_le, hy_pos_sq]

/-! ### 4. Sub-horizon packet quotient tails and linear moments -/

/-- Subtracting the quadratic harmonic Gram torsion identity at `K` and `N` cancels the torsion
pairing identically, leaving zero `log R` loss whenever `R * R ≤ K ≤ N`. -/
theorem sum_Ioc_packet_sq_le {R K N : ℕ} (hR : 2 ≤ R) (hRK : R * R ≤ K) (hKN : K ≤ N)
    (a : ℕ → ℝ) :
    (∑ n ∈ Ioc K N, (∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n) ^ 2) ≤
      ((harmonic N : ℝ) - harmonic K + 2) * ∑ m ∈ Icc 1 R, a m ^ 2 := by
  have hset : Ioc K N = Icc 1 N \ Icc 1 K := by
    ext n; simp only [mem_Ioc, mem_sdiff, mem_Icc]; omega
  have hpole (X : ℕ) : (∑ n ∈ Icc 1 X, (∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n) ^ 2) =
      ∑ n ∈ Icc 1 X, (∑ m ∈ Icc 1 R, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ) := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hs : (∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n) =
        (∑ m ∈ Icc 1 R, a m * normalizedRamanujanMode m n) / Real.sqrt n := by
      rw [sum_div]
      exact sum_congr rfl fun m _ => by rw [ramanujanPoleProfile, mul_div_assoc]
    rw [hs, div_pow, Real.sq_sqrt hn0.le]
  have hdiff : (∑ n ∈ Ioc K N, (∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n) ^ 2) =
      (∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 R, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) -
        ∑ n ∈ Icc 1 K, (∑ m ∈ Icc 1 R, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ) := by
    rw [hset, eq_sub_iff_add_eq.mpr (sum_sdiff (Icc_subset_Icc le_rfl hKN)), hpole N, hpole K]
  rw [hdiff]
  have hM : 0 ≤ ∑ m ∈ Icc 1 R, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hqK : (R : ℝ) * ((R : ℝ) - 1) / ((K : ℝ) + 1) ≤ 1 := by
    have h : (R : ℝ) * R ≤ K := by exact_mod_cast hRK
    rw [div_le_one (by positivity)]
    nlinarith only [h, Nat.cast_nonneg (α := ℝ) R]
  have hqN : (R : ℝ) * ((R : ℝ) - 1) / ((N : ℝ) + 1) ≤ 1 := by
    have h : (R : ℝ) * R ≤ N := by exact_mod_cast (hRK.trans hKN)
    rw [div_le_one (by positivity)]
    nlinarith only [h, Nat.cast_nonneg (α := ℝ) R]
  have hN := ((abs_le.mp (abs_harmonicGram_quadratic_torsion_remainder hR N a)).2).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hqN hM)
  have hK := neg_le_iff_add_nonneg.mp
    ((neg_le_neg (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hqK hM)).trans
      (abs_le.mp (abs_harmonicGram_quadratic_torsion_remainder hR K a)).1)
  linarith only [hN, hK]

/-- Top-band Euclidean tail bound on `Ioc K N` for any `u ∈ conductorSubspace R N` whenever
`R * R ≤ K ≤ N` and `18 * (1 + log R) ≤ log N`. -/
theorem sum_Ioc_sq_le_of_mem_conductorSubspace {R K N : ℕ} (hR : 2 ≤ R) (hRK : R * R ≤ K)
    (hKN : K ≤ N) (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ conductorSubspace R N) :
    Real.log N * (∑ n ∈ Ioc K N, primeHorizonExtension u n ^ 2) ≤
      2 * (Real.log ((N : ℝ) / K) + 3) * ‖u‖ ^ 2 := by
  obtain ⟨a, -, rfl⟩ := (mem_conductorSubspace_iff (M := R) (N := N) (x := u)).mp hu
  have hK1 : 1 ≤ K := (Nat.mul_le_mul (by omega : 2 ≤ R) (by omega : 2 ≤ R)).trans hRK |>.trans' (by omega)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (hK1.trans hKN)
  have hL : 0 < Real.log N := by
    have hR0 := Real.log_natCast_nonneg R
    linarith only [hlog, hR0]
  have hval (n : ℕ) (hn : n ∈ Ioc K N) :
      Real.log N * primeHorizonExtension
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) n ^ 2 =
        (∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n) ^ 2 := by
    have hnI : n ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
    rw [primeHorizonExtension_coe _ ⟨n, hnI⟩]
    have hp : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ⟨n, hnI⟩ =
        (Real.sqrt (Real.log N))⁻¹ * ∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n := by
      change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hnI⟩)
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) = _
      rw [map_sum, mul_sum]
      refine sum_congr rfl fun m _ => ?_
      change a m * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n) =
        (Real.sqrt (Real.log N))⁻¹ * (a m * ramanujanPoleProfile m n)
      ring
    rw [hp, mul_pow, inv_pow, Real.sq_sqrt hL.le]
    field_simp [hL.ne']
  rw [mul_sum, sum_congr rfl hval]
  have hpack := sum_Ioc_packet_sq_le hR hRK hKN a
  have hriesz := (half_and_three_halves_riesz_of_log_le hR (hRK.trans hKN) hlog a).1
  have hHN : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  have hHK : Real.log K ≤ (harmonic K : ℝ) :=
    (Real.log_le_log hK0 (by exact_mod_cast Nat.le_succ K)).trans (log_add_one_le_harmonic K)
  have hhar : (harmonic N : ℝ) - harmonic K + 2 ≤ Real.log ((N : ℝ) / K) + 3 := by
    rw [Real.log_div hN0.ne' hK0.ne']
    linarith only [hHN, hHK]
  have hhar0 : 0 ≤ Real.log ((N : ℝ) / K) + 3 := by
    have hdiv1 : 1 ≤ (N : ℝ) / K := (one_le_div hK0).mpr (by exact_mod_cast hKN)
    have hlog0 := Real.log_nonneg hdiv1
    linarith only [hlog0]
  calc
    (∑ n ∈ Ioc K N, (∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n) ^ 2) ≤
        ((harmonic N : ℝ) - harmonic K + 2) * ∑ m ∈ Icc 1 R, a m ^ 2 := hpack
    _ ≤ (Real.log ((N : ℝ) / K) + 3) * ∑ m ∈ Icc 1 R, a m ^ 2 :=
      mul_le_mul_of_nonneg_right hhar (sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ (Real.log ((N : ℝ) / K) + 3) *
        (2 * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hriesz]) hhar0
    _ = 2 * (Real.log ((N : ℝ) / K) + 3) *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

/-- Quotient-cutoff form of the top-band tail bound: on `{n ∈ Icc 1 N | N / n < T}` with `1 ≤ T`
and `(R * R + 1) * T ≤ N`, the Euclidean mass of `u ∈ conductorSubspace R N` is at most
`2 * (log (2 T) + 3) / log N * ‖u‖^2`. -/
theorem sum_quotient_tail_sq_le_of_mem_conductorSubspace {R N : ℕ} {T : ℝ}
    (hR : 2 ≤ R) (hT : 1 ≤ T) (hRNT : ((R * R : ℕ) + 1 : ℝ) * T ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ conductorSubspace R N) :
    Real.log N *
        (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T),
          primeHorizonExtension u n ^ 2) ≤
      2 * (Real.log (2 * T) + 3) * ‖u‖ ^ 2 := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  let K : ℕ := ⌊(N : ℝ) / T⌋₊
  have hNR_div : ((R * R : ℕ) : ℝ) + 1 ≤ (N : ℝ) / T := (le_div_iff₀ hT0).mpr hRNT
  have hRK : R * R ≤ K := by
    have hlt : ((R * R : ℕ) : ℝ) < K + 1 := by
      have hf := Nat.lt_floor_add_one ((N : ℝ) / T)
      linarith only [hNR_div, hf]
    have hnat : R * R < K + 1 := by exact_mod_cast hlt
    omega
  have hKN : K ≤ N := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h : (K : ℝ) ≤ N := (Nat.floor_le (div_nonneg hN0 hT0.le)).trans (div_le_self hN0 hT)
    exact_mod_cast h
  have hK1 : 1 ≤ K := (Nat.mul_le_mul hR hR).trans hRK |>.trans' (by omega)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hsub : (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T) ⊆ Ioc K N := by
    intro n hn
    obtain ⟨hnI, hquot⟩ := mem_filter.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
    have hx : (N : ℝ) / T < n := (div_lt_iff₀ hT0).mpr (by
      have h := (div_lt_iff₀ hn0).mp hquot; nlinarith only [h])
    have hKn : (K : ℝ) < n := (Nat.floor_le (by positivity)).trans_lt hx
    exact mem_Ioc.mpr ⟨by exact_mod_cast hKn, (mem_Icc.mp hnI).2⟩
  have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hNK_le : (N : ℝ) / K ≤ 2 * T := by
    have hf : (N : ℝ) / T < (K : ℝ) + 1 := Nat.lt_floor_add_one _
    have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have h2 : (N : ℝ) / T ≤ 2 * K := by linarith only [hf, hK1R]
    rw [div_le_iff₀ hK0]
    have h := (div_le_iff₀ hT0).mp h2
    nlinarith only [h]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (hK1.trans hKN)
  have hlog_le : Real.log ((N : ℝ) / K) ≤ Real.log (2 * T) :=
    Real.log_le_log (div_pos hN0 hK0) hNK_le
  calc
    Real.log N * (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T),
        primeHorizonExtension u n ^ 2) ≤
        Real.log N * ∑ n ∈ Ioc K N, primeHorizonExtension u n ^ 2 :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _) hL0
    _ ≤ 2 * (Real.log ((N : ℝ) / K) + 3) * ‖u‖ ^ 2 :=
      sum_Ioc_sq_le_of_mem_conductorSubspace hR hRK hKN hlog hu
    _ ≤ 2 * (Real.log (2 * T) + 3) * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hlog_le]) (sq_nonneg _)

/-- Linear-moment bound `∑_{n=1}^N (n / N) u_n^2 ≤ (2 log log N + 11) / log N · ‖u‖^2` on
`conductorSubspace R N`. -/
theorem sum_linear_moment_sq_le_of_mem_conductorSubspace {R N : ℕ} (hR : 2 ≤ R)
    (hRN : ((R * R : ℕ) + 1 : ℝ) * (Real.log N + 1) ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ conductorSubspace R N) :
    (∑ n ∈ Icc 1 N, ((n : ℝ) / N) * primeHorizonExtension u n ^ 2) ≤
      (2 * Real.log (Real.log N) + 11) / Real.log N * ‖u‖ ^ 2 := by
  have hL1 : 1 ≤ Real.log N := by
    have hR0 := Real.log_natCast_nonneg R
    linarith only [hlog, hR0]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  let T : ℝ := Real.log N + 1
  have hT1 : 1 ≤ T := by dsimp only [T]; linarith only [hL0]
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < ((R * R : ℕ) + 1 : ℝ) * T := by positivity
    linarith only [this, hRN]
  have hpoint : ∀ n ∈ Icc 1 N,
      ((n : ℝ) / N) * primeHorizonExtension u n ^ 2 ≤
        (1 / Real.log N) * primeHorizonExtension u n ^ 2 +
          if (N : ℝ) / n < T then primeHorizonExtension u n ^ 2 else 0 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast (mem_Icc.mp hn).2)
    by_cases hlt : (N : ℝ) / n < T
    · rw [if_pos hlt]
      have h1 : ((n : ℝ) / N) * primeHorizonExtension u n ^ 2 ≤ primeHorizonExtension u n ^ 2 :=
        by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnN (sq_nonneg _)
      exact h1.trans (le_add_of_nonneg_left (by positivity))
    · rw [if_neg hlt, add_zero]
      have hge : Real.log N ≤ (N : ℝ) / n := by
        have := le_of_not_gt hlt; dsimp only [T] at this; linarith only [this]
      have hrat : (n : ℝ) / N ≤ 1 / Real.log N := by
        rw [div_le_div_iff₀ hN0 hL0]
        have hm := (le_div_iff₀ hn0).mp hge
        linarith only [hm]
      exact mul_le_mul_of_nonneg_right hrat (sq_nonneg _)
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, ← mul_sum, ← sum_filter, sum_primeHorizonExtension_sq] at hsum
  have htail := (le_div_iff₀ hL0).mpr (by
    simpa only [mul_comm (Real.log N), mul_assoc] using
      sum_quotient_tail_sq_le_of_mem_conductorSubspace hR hT1 hRN hlog hu)
  have h2T : Real.log (2 * T) ≤ Real.log (Real.log N) + 2 := by
    have h4L : 2 * T ≤ 4 * Real.log N := by dsimp only [T]; linarith only [hL1]
    have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
      linarith only [h]
    calc
      Real.log (2 * T) ≤ Real.log (4 * Real.log N) := Real.log_le_log (by positivity) h4L
      _ = Real.log 4 + Real.log (Real.log N) := Real.log_mul (by norm_num) hL0.ne'
      _ ≤ Real.log (Real.log N) + 2 := by linarith only [hlog4]
  calc
    (∑ n ∈ Icc 1 N, ((n : ℝ) / N) * primeHorizonExtension u n ^ 2) ≤
        (1 / Real.log N) * ‖u‖ ^ 2 +
          2 * (Real.log (2 * T) + 3) * ‖u‖ ^ 2 / Real.log N := hsum.trans (add_le_add le_rfl htail)
    _ ≤ (1 / Real.log N) * ‖u‖ ^ 2 +
          2 * (Real.log (Real.log N) + 5) * ‖u‖ ^ 2 / Real.log N := by
      refine add_le_add le_rfl (div_le_div_of_nonneg_right ?_ hL0.le)
      exact mul_le_mul_of_nonneg_right (by linarith only [h2T]) (sq_nonneg _)
    _ = (2 * Real.log (Real.log N) + 11) / Real.log N * ‖u‖ ^ 2 := by
      field_simp [hL0.ne']
      ring

#print axioms exists_quantitative_exponential_conductor_cutoff_of_poleDefect_le
#print axioms poleDefect_ge_of_norm_sub_starProjection_gt
#print axioms abs_inner_sum_normalizedRamanujanHorizonVector_of_orthog_le
#print axioms low_band_norm_le_of_mem_orthogonal
#print axioms poleDefect_ge_of_supported_above
#print axioms sum_Ioc_sq_le_of_mem_conductorSubspace
#print axioms sum_linear_moment_sq_le_of_mem_conductorSubspace

end GaloisForLFunctions.CompletedArithmeticForms
