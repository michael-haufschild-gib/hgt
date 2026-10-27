import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheGoldenDatumHasNoFixedBudget
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.KernelCountsAreBlindToComplexQuartets

/-!
# The prime-error budget of a curve counts its spectrum

The `𝔽_q` calibration of `TheMertensEnergyPaysItsCriticalResidues` and
`ThePrimeErrorEnergyPaysTheCriticalZeros`. For a curve datum with normalized Frobenius eigenvalues
`β_i`, the normalized prime error at degree `m` is the power sum `e_m = Σ_i β_i^m`
(`N_m = q^m + 1 − q^{m/2} e_m`), and its energy is `E(M) = Σ_{m ≤ M} |e_m|²`.

* **A finite slope is purity** (`unitary_of_powerSum_energy_le_linear`). If `E(M) ≤ S M + B` for all
  `M`, every `|β_i| = 1`: the power sums grow at most polynomially, and the functional equation
  pairs `β` with `β⁻¹`.
* **The slope counts the spectrum** (`tendsto_powerSum_energy_div`). For a pure datum
  `E(M)/M → #{(i, j) : β_i = β_j} = Σ_β mult(β)²`: equal eigenvalues contribute `1` per degree, and
  distinct unimodular ones `β_i β̄_j ≠ 1` average out.
* **The budget** (`card_le_spectrumCount`, `spectrumCount_eq_card_iff`). The slope is at least
  `#ι = 2g`, with equality exactly for a simple spectrum; the golden datum and the complex fake have
  no finite slope (`goldenDatum_not_powerSum_energy_le_linear`,
  `complexFake_not_powerSum_energy_le_linear`).

Over `ℤ` the same slope, read on `ψ(n) − n` on the log scale, is bounded below by Cramér's constant
`Σ_ρ m_ρ²/|ρ|²` unconditionally, and is finite exactly under RH; over `𝔽_q` it is
`Σ_β mult(β)²` and finite exactly under purity. Cramér's constant is the arithmetic form of Weil's
budget `2g`: the spectrum counted with squared multiplicities, here weighted by `1/|ρ|²`.
-/

open Complex Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι]

/-- **A finite slope is purity.** If the prime-error energy of a curve datum grows at most
linearly, `Σ_{m ≤ M} |e_m|² ≤ S M + B`, the datum is unitary. -/
theorem unitary_of_powerSum_energy_le_linear (D : CurveDatum ι) {S B : ℝ}
    (h : ∀ M : ℕ, ∑ m ∈ Icc 1 M, ‖D.powerSum m‖ ^ 2 ≤ S * M + B) : ∀ i, ‖D.β i‖ = 1 := by
  -- polynomial growth of the power sums
  have hpoly : ∀ m : ℕ, 1 ≤ m → ‖D.powerSum m‖ ≤ |S| * m + |B| + 1 := by
    intro m hm
    have h1 : ‖D.powerSum m‖ ^ 2 ≤ S * m + B :=
      (single_le_sum (f := fun k => ‖D.powerSum k‖ ^ 2) (fun _ _ => sq_nonneg _)
        (mem_Icc.mpr ⟨hm, le_rfl⟩)).trans (h m)
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have hx : 1 ≤ |S| * m + |B| + 1 := by
      have := mul_nonneg (abs_nonneg S) hm0; linarith [abs_nonneg B]
    have h2 : S * m + B ≤ (|S| * m + |B| + 1) ^ 2 := by
      have h3 : S * m ≤ |S| * m := mul_le_mul_of_nonneg_right (le_abs_self S) hm0
      have h4 := le_self_pow₀ hx two_ne_zero
      linarith [le_abs_self B]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h1.trans h2)
  -- hence `|β_i| ≤ ρ` for every `ρ > 1`
  have hle : ∀ i, ‖D.β i‖ ≤ 1 := by
    intro i
    refine le_of_forall_gt_imp_ge_of_dense fun ρ hρ => ?_
    have hρ0 : 0 ≤ ρ := by linarith
    have hbern : ∀ m : ℕ, (m : ℝ) ≤ ρ ^ m / (ρ - 1) := fun m => by
      rw [le_div_iff₀ (by linarith)]
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ ρ - 1 by linarith) m
      rw [show 1 + (ρ - 1) = ρ by ring] at this
      linarith
    refine RHTower.WeilKloosterman.norm_le_of_power_sums_bound (m0 := 1) Finset.univ D.β hρ0
      (C := |S| / (ρ - 1) + |B| + 1) (fun m hm => ?_) i (mem_univ i)
    have hpow : 1 ≤ ρ ^ m := one_le_pow₀ hρ.le
    calc ‖∑ i ∈ univ, D.β i ^ m‖ = ‖D.powerSum m‖ := rfl
      _ ≤ |S| * m + |B| + 1 := hpoly m hm
      _ ≤ |S| * (ρ ^ m / (ρ - 1)) + (|B| + 1) * ρ ^ m := by
          have h1 := mul_le_mul_of_nonneg_left (hbern m) (abs_nonneg S)
          have h2 : |B| + 1 ≤ (|B| + 1) * ρ ^ m := le_mul_of_one_le_right (by positivity) hpow
          linarith
      _ = (|S| / (ρ - 1) + |B| + 1) * ρ ^ m := by ring
  intro i
  have hfe := D.β_fePerm i
  have h1 := hle (D.fePerm i)
  have h2 := hle i
  have hprod : ‖D.β (D.fePerm i)‖ * ‖D.β i‖ = 1 := by rw [← norm_mul, hfe, norm_one]
  have hi0 : 0 ≤ ‖D.β i‖ := norm_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) hi0]

/-- The number of ordered pairs of equal eigenvalues, `Σ_β mult(β)²`. -/
def spectrumCount (D : CurveDatum ι) : ℕ :=
  ((univ ×ˢ univ).filter fun p : ι × ι => D.β p.1 = D.β p.2).card

/-- `|e_m|² = Σ_{i,j} (β_i β̄_j)^m`. -/
theorem norm_powerSum_sq_eq (D : CurveDatum ι) (m : ℕ) :
    ((‖D.powerSum m‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ univ ×ˢ univ, (D.β p.1 * starRingEnd ℂ (D.β p.2)) ^ m := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', CurveDatum.powerSum, map_sum, sum_mul_sum,
    ← sum_product']
  refine sum_congr rfl fun p _ => ?_
  rw [map_pow, mul_pow]

/-- The Cesàro mean of the powers of a unimodular `z ≠ 1` vanishes. -/
theorem tendsto_sum_pow_div_zero {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun M : ℕ => (∑ m ∈ Icc 1 M, z ^ m) / M) atTop (𝓝 0) := by
  have hbound : ∀ M : ℕ, ‖∑ m ∈ Icc 1 M, z ^ m‖ ≤ 2 / ‖z - 1‖ := by
    intro M
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hgeom : ∑ m ∈ Icc 1 M, z ^ m = z * (z ^ M - 1) / (z - 1) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      simp_rw [pow_add, pow_one]
      rw [← Finset.mul_sum, geom_sum_eq hz1]
      ring
    rw [hgeom, norm_div, norm_mul, hz, one_mul]
    gcongr
    calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  refine squeeze_zero_norm (a := fun M : ℕ => (2 / ‖z - 1‖) / M) (fun M => ?_) ?_
  · rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hbound M) (Nat.cast_nonneg M)
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-- **The slope counts the spectrum.** For a unitary curve datum,
`(1/M) Σ_{m ≤ M} |e_m|² → #{(i, j) : β_i = β_j}`. -/
theorem tendsto_powerSum_energy_div (D : CurveDatum ι) (hu : ∀ i, ‖D.β i‖ = 1) :
    Tendsto (fun M : ℕ => (∑ m ∈ Icc 1 M, ‖D.powerSum m‖ ^ 2) / M) atTop
      (𝓝 (spectrumCount D : ℝ)) := by
  -- work in `ℂ` pair by pair
  have hpair : ∀ p ∈ (univ ×ˢ univ : Finset (ι × ι)),
      Tendsto (fun M : ℕ => (∑ m ∈ Icc 1 M, (D.β p.1 * starRingEnd ℂ (D.β p.2)) ^ m) / M) atTop
        (𝓝 (if D.β p.1 = D.β p.2 then 1 else 0)) := by
    intro p _
    have hz : ‖D.β p.1 * starRingEnd ℂ (D.β p.2)‖ = 1 := by
      rw [norm_mul, Complex.norm_conj, hu, hu, one_mul]
    by_cases heq : D.β p.1 = D.β p.2
    · rw [if_pos heq]
      have h1 : D.β p.1 * starRingEnd ℂ (D.β p.2) = 1 := by
        rw [← heq, Complex.mul_conj', hu]; simp
      simp only [h1, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with M hM
      rw [div_self (Nat.cast_ne_zero.mpr hM)]
    · rw [if_neg heq]
      refine tendsto_sum_pow_div_zero hz fun h1 => heq ?_
      have hne : D.β p.2 ≠ 0 := fun h => by
        have := hu p.2; rw [h, norm_zero] at this; norm_num at this
      have hconj : starRingEnd ℂ (D.β p.2) = (D.β p.2)⁻¹ := by
        rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu, one_pow, inv_one, Complex.ofReal_one,
          mul_one]
      rw [hconj, mul_inv_eq_one₀ hne] at h1
      exact h1
  have hsum := tendsto_finsetSum _ hpair
  have hcount : (∑ p ∈ (univ ×ˢ univ : Finset (ι × ι)),
      (if D.β p.1 = D.β p.2 then (1 : ℂ) else 0)) = (spectrumCount D : ℂ) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, spectrumCount]
  rw [hcount] at hsum
  have hident : ∀ M : ℕ, (∑ p ∈ (univ ×ˢ univ : Finset (ι × ι)),
      (∑ m ∈ Icc 1 M, (D.β p.1 * starRingEnd ℂ (D.β p.2)) ^ m) / M) =
      (((∑ m ∈ Icc 1 M, ‖D.powerSum m‖ ^ 2) / M : ℝ) : ℂ) := by
    intro M
    rw [← Finset.sum_div, Finset.sum_comm]
    push_cast
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [← Complex.ofReal_pow, norm_powerSum_sq_eq]
  have hre := (Complex.continuous_re.tendsto _).comp hsum
  simp only [hident, Complex.natCast_re] at hre
  exact hre

/-- **The budget is at least `2g`.** Every eigenvalue is equal to itself. -/
theorem card_le_spectrumCount (D : CurveDatum ι) : Fintype.card ι ≤ spectrumCount D := by
  rw [spectrumCount, ← card_univ]
  refine card_le_card_of_injOn (fun i => (i, i)) (fun i _ => ?_) (fun i _ j _ h => ?_)
  · simp
  · exact (Prod.mk.inj h).1

/-- **The budget is `2g` exactly for a simple spectrum.** -/
theorem spectrumCount_eq_card_iff (D : CurveDatum ι) :
    spectrumCount D = Fintype.card ι ↔ Function.Injective D.β := by
  classical
  have hdiag : ((univ ×ˢ univ).filter fun p : ι × ι => p.1 = p.2).card = Fintype.card ι := by
    rw [← card_univ]
    refine card_bij (fun p _ => p.1) (fun p _ => mem_univ _) (fun p hp q hq h => ?_)
      (fun i _ => ⟨(i, i), by simp, rfl⟩)
    simp only [mem_filter] at hp hq
    exact Prod.ext h (by rw [← hp.2, ← hq.2, h])
  have hsub : ((univ ×ˢ univ).filter fun p : ι × ι => p.1 = p.2) ⊆
      ((univ ×ˢ univ).filter fun p : ι × ι => D.β p.1 = D.β p.2) := by
    intro p hp
    simp only [mem_filter] at hp ⊢
    exact ⟨hp.1, by rw [hp.2]⟩
  constructor
  · intro heq i j hij
    by_contra hne
    have hlt : ((univ ×ˢ univ).filter fun p : ι × ι => p.1 = p.2).card <
        ((univ ×ˢ univ).filter fun p : ι × ι => D.β p.1 = D.β p.2).card := by
      refine card_lt_card ⟨hsub, fun h => ?_⟩
      have := h (show (i, j) ∈ ((univ ×ˢ univ).filter fun p : ι × ι => D.β p.1 = D.β p.2) by
        simp [hij])
      simp only [mem_filter] at this
      exact hne this.2
    rw [hdiag] at hlt
    exact absurd heq (ne_of_gt (by simpa [spectrumCount] using hlt))
  · intro hinj
    rw [spectrumCount, ← hdiag]
    congr 1
    ext p
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1, hinj h.2⟩, fun h => ⟨h.1, by rw [h.2]⟩⟩

/-- **The golden datum has no finite prime-error slope.** -/
theorem goldenDatum_not_powerSum_energy_le_linear {S B : ℝ} :
    ¬ ∀ M : ℕ, ∑ m ∈ Icc 1 M, ‖goldenDatum.powerSum m‖ ^ 2 ≤ S * M + B :=
  fun h => goldenDatum_not_unitary (unitary_of_powerSum_energy_le_linear goldenDatum h)

/-- **The complex fake has no finite prime-error slope.** -/
theorem complexFake_not_powerSum_energy_le_linear {S B : ℝ} :
    ¬ ∀ M : ℕ, ∑ m ∈ Icc 1 M, ‖complexFake.powerSum m‖ ^ 2 ≤ S * M + B := by
  intro h
  have := unitary_of_powerSum_energy_le_linear complexFake h 0
  rw [complexFake_norm_β] at this
  norm_num at this

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
