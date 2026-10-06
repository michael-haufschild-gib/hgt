import GaloisForLFunctions.RHTower.KuznetsovSameSignSpecWeightBounds
import GaloisForLFunctions.RHTower.KuznetsovLargeSieveGammaZero

/-!
# Summability of the spectral coefficients from the large sieve

For one cusp vector `v` at frequency `μ > 0` the large sieve (`large_sieve_full`) bounds, for every
`K ≥ 1`, `Σ_j (κ_j+1)e^{−πκ_j}[λ_j ≤ ¼+K²] |ρ_j(v)|²` by `|geomRow(1, K)| ≤ G₁K³ + G₂`
(`exists_bound_norm_geomRow_self`).  Splitting the spectrum by `K_j = ⌈κ_j⌉ + 1` gives

`Σ_j |ρ_j(v)|² e^{−πκ_j} (1+κ_j)^{−4} < ∞`   (`summable_cuspCoeff_sq_weight`)

and in the same way `∫ Σ_i |η_i(v, r)|² e^{−π|r|} (1+|r|)^{−4} dr < ∞`
(`integrable_eisCoeff_sq_weight`): these are the dominating functions for `σ ↓ 1`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry KuznetsovGauss

noncomputable section

variable {N : ℕ}

/-- **`|geomRow(1, K; μ, μ; v, v)| ≤ G₁ K³ + G₂`** for `K ≥ 1`. -/
theorem exists_bound_norm_geomRow_self {μ : ℝ} (hμ : 0 < μ) (v : DeckSpace N) :
    ∃ G₁ G₂ : ℝ, 0 ≤ G₁ ∧ 0 ≤ G₂ ∧ ∀ K : ℝ, 1 ≤ K → ‖geomRow 1 K μ μ v v‖ ≤ G₁ * K ^ 3 + G₂ := by
  set S := ∑' r : ReducedRow, rowSq r ^ (-(3 / 2 : ℝ))
  have hS : Summable fun r : ReducedRow => rowSq r ^ (-(3 / 2 : ℝ)) :=
    summable_reducedRow_rpow (by norm_num)
  set G₂ := 2 * (‖v‖ * ‖v‖ * (Real.pi * (4 * Real.pi * μ) * (2 * Real.pi * Real.exp 1)) * S)
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by have := rowSq_pos ‹_›; positivity
  refine ⟨2 * ‖diagPlus ((1 : ℝ) : ℂ) 1 μ μ v v‖ * (Real.sqrt Real.pi / 2), G₂, by positivity,
    by positivity, fun K hK => ?_⟩
  have hK0 : 0 < K := by linarith
  have hrow : ∀ r : ReducedRow, ‖rowWeightPlus μ μ v v r.1 * ((rowSq r ^ (-(1 : ℝ)) : ℝ) : ℂ) *
      gaussKernel 1 K (4 * Real.pi * Real.sqrt (μ * μ / rowSq r))‖ ≤
      ‖v‖ * ‖v‖ * (Real.pi * (4 * Real.pi * μ) * (2 * Real.pi * Real.exp 1)) *
        rowSq r ^ (-(3 / 2 : ℝ)) := fun r => by
    have hq := rowSq_pos r
    have hX : 4 * Real.pi * Real.sqrt (μ * μ / rowSq r) = 4 * Real.pi * μ * rowSq r ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_div' _ hq.le, Real.sqrt_mul_self hμ.le, Real.sqrt_eq_rpow, Real.rpow_neg hq.le]
      ring
    have hk := norm_gaussKernel_le (le_refl (1 : ℝ)) hK0 (by positivity :
      0 ≤ 4 * Real.pi * Real.sqrt (μ * μ / rowSq r))
    have hm := gaussSinhMass_le hK
    have hw := norm_rowWeightPlus_le μ μ v v r.1
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hpow : rowSq r ^ (-(1 : ℝ)) * rowSq r ^ (-(1 / 2 : ℝ)) = rowSq r ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hq]; norm_num
    calc ‖rowWeightPlus μ μ v v r.1‖ * rowSq r ^ (-(1 : ℝ)) *
          ‖gaussKernel 1 K (4 * Real.pi * Real.sqrt (μ * μ / rowSq r))‖
        ≤ (‖v‖ * ‖v‖) * rowSq r ^ (-(1 : ℝ)) *
          (Real.pi * (4 * Real.pi * μ * rowSq r ^ (-(1 / 2 : ℝ))) * (2 * Real.pi * Real.exp 1)) := by
          rw [← hX]; gcongr; exact hk.trans (by gcongr)
      _ = _ := by rw [← hpow]; ring
  have hsum : Summable fun r : ReducedRow => ‖rowWeightPlus μ μ v v r.1 *
      ((rowSq r ^ (-(1 : ℝ)) : ℝ) : ℂ) * gaussKernel 1 K (4 * Real.pi * Real.sqrt (μ * μ / rowSq r))‖ :=
    (hS.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _) hrow
  have htsum := (norm_tsum_le_tsum_norm hsum).trans
    (hsum.tsum_le_tsum hrow (hS.mul_left _))
  rw [tsum_mul_left] at htsum
  rw [geomRow, gaussMass_eq hK0]
  calc ‖2 * diagPlus ((1 : ℝ) : ℂ) 1 μ μ v v * ((Real.sqrt Real.pi / 2 * K ^ 3 : ℝ) : ℂ) +
        2 * ∑' r : ReducedRow, rowWeightPlus μ μ v v r.1 * ((rowSq r ^ (-(1 : ℝ)) : ℝ) : ℂ) *
          gaussKernel 1 K (4 * Real.pi * Real.sqrt (μ * μ / rowSq r))‖
      ≤ ‖2 * diagPlus ((1 : ℝ) : ℂ) 1 μ μ v v * ((Real.sqrt Real.pi / 2 * K ^ 3 : ℝ) : ℂ)‖ +
        ‖2 * ∑' r : ReducedRow, rowWeightPlus μ μ v v r.1 * ((rowSq r ^ (-(1 : ℝ)) : ℝ) : ℂ) *
          gaussKernel 1 K (4 * Real.pi * Real.sqrt (μ * μ / rowSq r))‖ := norm_add_le _ _
    _ ≤ _ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          RCLike.norm_ofNat]
        have : 2 * ‖∑' r : ReducedRow, rowWeightPlus μ μ v v r.1 * ((rowSq r ^ (-(1 : ℝ)) : ℝ) : ℂ) *
            gaussKernel 1 K (4 * Real.pi * Real.sqrt (μ * μ / rowSq r))‖ ≤ G₂ := by
          simp only [G₂]; gcongr
        nlinarith

/-- The family consisting of one cusp vector. -/
theorem specCoeff_unit (j : CuspEigenIndex N) (μ : ℝ) (hμ : 0 < μ) (v : DeckSpace N) :
    ‖specCoeff j 1 (Finset.univ : Finset Unit) (fun _ => μ) (fun _ => v) (fun _ => 1)‖ ^ 2 =
      ‖cuspCoeff j μ v‖ ^ 2 * (2 * Real.pi * μ)⁻¹ := by
  have hx : (0 : ℝ) < 2 * Real.pi * μ := by positivity
  simp only [specCoeff, Finset.univ_unique, Finset.sum_singleton, map_one, one_mul, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have : (-(((1 : ℝ) : ℂ) - 1 / 2)).re = -(1 / 2) := by simp; norm_num
  have hsq : ((2 * Real.pi * μ) ^ (-(1 / 2 : ℝ))) ^ 2 = (2 * Real.pi * μ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num [Real.rpow_neg_one]
  rw [this, mul_pow, hsq]

theorem geomForm_unit (K μ : ℝ) (v : DeckSpace N) :
    geomForm 1 K (Finset.univ : Finset Unit) (fun _ => μ) (fun _ => v) (fun _ => 1) =
      geomRow 1 K μ μ v v := by
  simp [geomForm]

/-- `K_κ = ⌈κ⌉ + 1`: `1 ≤ K_κ`, `κ ≤ K_κ ≤ κ + 2`. -/
theorem natCeil_add_one_bounds {κ : ℝ} (hκ : 0 ≤ κ) :
    1 ≤ ((⌈κ⌉₊ + 1 : ℕ) : ℝ) ∧ κ ≤ ((⌈κ⌉₊ + 1 : ℕ) : ℝ) ∧ ((⌈κ⌉₊ + 1 : ℕ) : ℝ) ≤ κ + 2 := by
  have h1 := Nat.le_ceil κ
  have h2 := Nat.ceil_lt_add_one hκ
  push_cast
  refine ⟨by linarith [Nat.cast_nonneg (α := ℝ) ⌈κ⌉₊], by linarith, by linarith⟩

theorem sieveWeight_of_kappa_le {K lam : ℝ} (h : specKappa lam ≤ K) :
    sieveWeight K lam = specWeightConst * (specKappa lam + 1) * Real.exp (-(Real.pi * specKappa lam)) := by
  unfold sieveWeight
  rw [if_pos]
  rcases le_total lam (1 / 4) with hl | hl
  · nlinarith [sq_nonneg K]
  · have hk : specKappa lam ^ 2 = lam - 1 / 4 := by
      unfold specKappa; rw [max_eq_left (by linarith), Real.sq_sqrt (by linarith)]
    have hκ0 : 0 ≤ specKappa lam := Real.sqrt_nonneg _
    nlinarith [mul_self_le_mul_self hκ0 h]

/-- `e^{−πκ}(1+κ)^{−4} ≤ (2⁵/c₀) K_κ^{−5} · c₀(κ+1)e^{−πκ}`. -/
theorem weight_le_sieveWeight_ceil (lam : ℝ) :
    Real.exp (-(Real.pi * specKappa lam)) / (1 + specKappa lam) ^ 4 ≤
      2 ^ 5 / specWeightConst * ((((⌈specKappa lam⌉₊ + 1 : ℕ) : ℝ) ^ 5)⁻¹ *
        sieveWeight (⌈specKappa lam⌉₊ + 1 : ℕ) lam) := by
  set κ := specKappa lam
  have hκ : 0 ≤ κ := Real.sqrt_nonneg _
  obtain ⟨hK1, hKκ, hK2⟩ := natCeil_add_one_bounds hκ
  set K : ℝ := ((⌈κ⌉₊ + 1 : ℕ) : ℝ)
  rw [sieveWeight_of_kappa_le hKκ]
  have hc := specWeightConst_pos
  have hE := Real.exp_pos (-(Real.pi * κ))
  have hK0 : 0 < K := by linarith
  have h5 : K ^ 5 ≤ 2 ^ 5 * (1 + κ) ^ 5 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hK0.le (by linarith) 5
  rw [div_le_iff₀ (by positivity)]
  have hK5 : 0 < K ^ 5 := by positivity
  field_simp
  have : (1 + κ) ^ 5 = (1 + κ) ^ 4 * (1 + κ) := by ring
  nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ Real.exp (-(Real.pi * κ)) *
    (κ + 1) * (1 + κ) ^ 4), pow_pos (by linarith : (0 : ℝ) < 1 + κ) 4]


/-- `e^{−πκ}(1+κ)^{−4} ≤ 2⁵ K_κ^{−5} (κ+1)e^{−πκ}`, `K_κ = ⌈κ⌉ + 1`. -/
theorem weight_le_ceil_profile {κ : ℝ} (hκ : 0 ≤ κ) :
    Real.exp (-(Real.pi * κ)) / (1 + κ) ^ 4 ≤
      2 ^ 5 * ((((⌈κ⌉₊ + 1 : ℕ) : ℝ) ^ 5)⁻¹ * ((κ + 1) * Real.exp (-(Real.pi * κ)))) := by
  obtain ⟨hK1, hKκ, hK2⟩ := natCeil_add_one_bounds hκ
  set K : ℝ := ((⌈κ⌉₊ + 1 : ℕ) : ℝ)
  have hE := Real.exp_pos (-(Real.pi * κ))
  have hK0 : 0 < K := by linarith
  have h5 : K ^ 5 ≤ 2 ^ 5 * (1 + κ) ^ 5 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hK0.le (by linarith) 5
  rw [div_le_iff₀ (by positivity)]
  have hK5 : 0 < K ^ 5 := by positivity
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ Real.exp (-(Real.pi * κ)) *
    (κ + 1) * (1 + κ) ^ 4), pow_pos (by linarith : (0 : ℝ) < 1 + κ) 4]

theorem summable_tail_profile (G₁ G₂ : ℝ) :
    Summable fun K : ℕ => (((K : ℝ) ^ 5)⁻¹ * (G₁ * (K : ℝ) ^ 3 + G₂)) := by
  have h2 := (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
  have h5 := (Real.summable_nat_pow_inv (p := 5)).2 (by norm_num)
  refine ((h2.mul_left G₁).add (h5.mul_left G₂)).congr fun K => ?_
  rcases eq_or_ne K 0 with rfl | hK
  · simp
  · have : (K : ℝ) ≠ 0 := by exact_mod_cast hK
    field_simp

/-- **Summability of the discrete spectral coefficients**: `Σ_j |ρ_j(v)|² e^{−πκ_j}(1+κ_j)^{−4} < ∞`. -/
theorem summable_cuspCoeff_sq_weight (hN : 2 ≤ N) {μ : ℝ} (hμ : 0 < μ) {v : DeckSpace N}
    (hv : IsCuspEigen μ v) {n : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n) :
    Summable fun j : CuspEigenIndex N =>
      ‖cuspCoeff j μ v‖ ^ 2 * (Real.exp (-(Real.pi * specKappa j.1)) / (1 + specKappa j.1) ^ 4) := by
  obtain ⟨G₁, G₂, hG₁, hG₂, hG⟩ := exists_bound_norm_geomRow_self hμ v
  set a : ℕ → CuspEigenIndex N → ℝ := fun K j =>
    sieveWeight K j.1 * (‖cuspCoeff j μ v‖ ^ 2 * (2 * Real.pi * μ)⁻¹) with ha
  have ha0 : ∀ K j, 0 ≤ a K j := fun K j => by
    have := sieveWeight_nonneg (K : ℝ) j.1; simp only [ha]; positivity
  have hLS : ∀ K : ℕ, 1 ≤ K → ∀ u : Finset (CuspEigenIndex N), ∑ j ∈ u, a K j ≤ G₁ * K ^ 3 + G₂ := by
    intro K hK u
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have h := large_sieve_full hN hK' (Finset.univ : Finset Unit) (μ := fun _ => μ) (fun _ => hμ)
      (v := fun _ => v) (fun _ => hv) (n := fun _ => n) (fun _ => hn) (fun _ => 1)
    rw [geomForm_unit] at h
    simp_rw [specCoeff_unit _ μ hμ v] at h
    have h2 : ∑ j ∈ u, ENNReal.ofReal (a K j) ≤ ENNReal.ofReal ‖geomRow 1 K μ μ v v‖ :=
      (ENNReal.sum_le_tsum u).trans (le_self_add.trans h)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => ha0 K j),
      ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] at h2
    exact h2.trans (hG K hK')
  set T := ∑' K : ℕ, (((K : ℝ) ^ 5)⁻¹ * (G₁ * (K : ℝ) ^ 3 + G₂))
  have hT := summable_tail_profile G₁ G₂
  have hc := specWeightConst_pos
  refine summable_of_sum_le (c := 2 ^ 5 * (2 * Real.pi * μ) / specWeightConst * T)
    (fun j => by positivity) fun u => ?_
  set M := u.sup fun j : CuspEigenIndex N => ⌈specKappa j.1⌉₊ + 1
  have hpt : ∀ j ∈ u, ‖cuspCoeff j μ v‖ ^ 2 * (Real.exp (-(Real.pi * specKappa j.1)) /
      (1 + specKappa j.1) ^ 4) ≤ 2 ^ 5 * (2 * Real.pi * μ) / specWeightConst *
        ∑ K ∈ Finset.Icc 1 M, ((K : ℝ) ^ 5)⁻¹ * a K j := fun j hj => by
    have hκ : 0 ≤ specKappa j.1 := Real.sqrt_nonneg _
    set Kj := ⌈specKappa j.1⌉₊ + 1
    have hKj : Kj ∈ Finset.Icc 1 M := Finset.mem_Icc.2 ⟨by omega, Finset.le_sup (f := fun j :
      CuspEigenIndex N => ⌈specKappa j.1⌉₊ + 1) hj⟩
    have hsingle : ((Kj : ℝ) ^ 5)⁻¹ * a Kj j ≤ ∑ K ∈ Finset.Icc 1 M, ((K : ℝ) ^ 5)⁻¹ * a K j :=
      Finset.single_le_sum (f := fun K : ℕ => ((K : ℝ) ^ 5)⁻¹ * a K j)
        (fun K _ => mul_nonneg (by positivity) (ha0 K j)) hKj
    have hw := weight_le_sieveWeight_ceil j.1
    have hμ' : (0 : ℝ) < 2 * Real.pi * μ := by positivity
    calc ‖cuspCoeff j μ v‖ ^ 2 * (Real.exp (-(Real.pi * specKappa j.1)) / (1 + specKappa j.1) ^ 4)
        ≤ ‖cuspCoeff j μ v‖ ^ 2 * (2 ^ 5 / specWeightConst * (((Kj : ℝ) ^ 5)⁻¹ *
          sieveWeight Kj j.1)) := by gcongr
      _ = 2 ^ 5 * (2 * Real.pi * μ) / specWeightConst * (((Kj : ℝ) ^ 5)⁻¹ * a Kj j) := by
          simp only [ha]; field_simp
      _ ≤ _ := by gcongr
  calc ∑ j ∈ u, ‖cuspCoeff j μ v‖ ^ 2 *
        (Real.exp (-(Real.pi * specKappa j.1)) / (1 + specKappa j.1) ^ 4)
      ≤ ∑ j ∈ u, 2 ^ 5 * (2 * Real.pi * μ) / specWeightConst *
          ∑ K ∈ Finset.Icc 1 M, ((K : ℝ) ^ 5)⁻¹ * a K j := Finset.sum_le_sum hpt
    _ = 2 ^ 5 * (2 * Real.pi * μ) / specWeightConst *
          ∑ K ∈ Finset.Icc 1 M, ((K : ℝ) ^ 5)⁻¹ * ∑ j ∈ u, a K j := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ ≤ 2 ^ 5 * (2 * Real.pi * μ) / specWeightConst *
          ∑ K ∈ Finset.Icc 1 M, ((K : ℝ) ^ 5)⁻¹ * (G₁ * (K : ℝ) ^ 3 + G₂) := by
        gcongr with K hK
        exact hLS K (Finset.mem_Icc.1 hK).1 u
    _ ≤ _ := by
        gcongr
        exact hT.sum_le_tsum _ fun K _ => mul_nonneg (by positivity) (by positivity)


theorem eisSpecCoeff_unit (i : Fin (Module.finrank ℂ (cuspVecSub N))) (r μ : ℝ) (hμ : 0 < μ)
    (v : DeckSpace N) (n : ℤ) :
    ‖eisSpecCoeff i 1 r (Finset.univ : Finset Unit) (fun _ => μ) (fun _ => v) (fun _ => n)
        (fun _ => 1)‖ ^ 2 =
      ‖eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n‖ ^ 2 * (2 * Real.pi * μ)⁻¹ := by
  have hx : (0 : ℝ) < 2 * Real.pi * μ := by positivity
  simp only [eisSpecCoeff, Finset.univ_unique, Finset.sum_singleton, map_one, one_mul, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have : (-(((1 : ℝ) : ℂ) - 1 / 2)).re = -(1 / 2) := by simp; norm_num
  have hsq : ((2 * Real.pi * μ) ^ (-(1 / 2 : ℝ))) ^ 2 = (2 * Real.pi * μ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num [Real.rpow_neg_one]
  rw [this, mul_pow, hsq]

/-- **Integrability of the continuous spectral coefficients**:
`∫ Σ_i |η_i(v, r)|² e^{−π|r|}(1+|r|)^{−4} dr < ∞`. -/
theorem integrable_eisCoeff_sq_weight (hN : 2 ≤ N) {μ : ℝ} (hμ : 0 < μ) {v : DeckSpace N}
    (hv : IsCuspEigen μ v) {n : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n) :
    Integrable fun r : ℝ => (∑ i, ‖eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n‖ ^ 2) *
      (Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4) := by
  obtain ⟨G₁, G₂, hG₁, hG₂, hG⟩ := exists_bound_norm_geomRow_self hμ v
  set g : ℝ → ℝ := fun r => ∑ i, ‖eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n‖ ^ 2
  have hg0 : ∀ r, 0 ≤ g r := fun r => Finset.sum_nonneg fun _ _ => by positivity
  have hgm : AEStronglyMeasurable g volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      ((aestronglyMeasurable_eisCoeff_line v _ n).norm.pow 2)
  set hfun : ℝ → ℝ := fun r => (4 * Real.pi)⁻¹ * (specWeightConst * (|r| + 1) *
    Real.exp (-(Real.pi * |r|))) * (g r * (2 * Real.pi * μ)⁻¹)
  have hc := specWeightConst_pos
  have hμ' : (0 : ℝ) < 2 * Real.pi * μ := by positivity
  have hh0 : ∀ r, 0 ≤ hfun r := fun r => by have := hg0 r; simp only [hfun]; positivity
  have hhm : AEMeasurable (fun r => ENNReal.ofReal (hfun r)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((aestronglyMeasurable_const.mul (Continuous.aestronglyMeasurable (by fun_prop))).mul
        (hgm.mul aestronglyMeasurable_const)).aemeasurable
  -- the large sieve on `[−K, K]`
  have hLS : ∀ K : ℕ, 1 ≤ K →
      ∫⁻ r in Icc (-(K : ℝ)) K, ENNReal.ofReal (hfun r) ≤ ENNReal.ofReal (G₁ * K ^ 3 + G₂) := by
    intro K hK
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have h := large_sieve_full hN hK' (Finset.univ : Finset Unit) (μ := fun _ => μ) (fun _ => hμ)
      (v := fun _ => v) (fun _ => hv) (n := fun _ => n) (fun _ => hn) (fun _ => 1)
    rw [geomForm_unit] at h
    simp_rw [eisSpecCoeff_unit _ _ μ hμ v n, ← Finset.sum_mul] at h
    exact (le_add_self.trans h).trans (ENNReal.ofReal_le_ofReal (hG K hK'))
  set C : ℝ := 2 ^ 5 * (4 * Real.pi) * (2 * Real.pi * μ) / specWeightConst
  set F : ℕ → ℝ → ENNReal := fun K r => ENNReal.ofReal (C * ((K : ℝ) ^ 5)⁻¹) *
    (Icc (-(K : ℝ)) K).indicator (fun r => ENNReal.ofReal (hfun r)) r
  have hpt : ∀ r, ENNReal.ofReal (g r * (Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4)) ≤
      ∑' K, F K r := fun r => by
    have hκ := abs_nonneg r
    obtain ⟨hK1, hKκ, -⟩ := natCeil_add_one_bounds hκ
    refine le_trans ?_ (ENNReal.le_tsum (⌈|r|⌉₊ + 1))
    have hmem : r ∈ Icc (-(((⌈|r|⌉₊ + 1 : ℕ) : ℝ))) ((⌈|r|⌉₊ + 1 : ℕ) : ℝ) :=
      ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩
    simp only [F, Set.indicator_of_mem hmem]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw := weight_le_ceil_profile hκ
    have hgr := hg0 r
    calc g r * (Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4)
        ≤ g r * (2 ^ 5 * ((((⌈|r|⌉₊ + 1 : ℕ) : ℝ) ^ 5)⁻¹ *
          ((|r| + 1) * Real.exp (-(Real.pi * |r|))))) := by gcongr
      _ = _ := by simp only [C, hfun]; field_simp
  have hFm : ∀ K, AEMeasurable (F K) volume := fun K =>
    aemeasurable_const.mul (hhm.indicator measurableSet_Icc)
  have hint : ∫⁻ r, ∑' K, F K r ≤ ENNReal.ofReal (C * ∑' K : ℕ,
      ((K : ℝ) ^ 5)⁻¹ * (G₁ * (K : ℝ) ^ 3 + G₂)) := by
    rw [lintegral_tsum hFm]
    have hT := summable_tail_profile G₁ G₂
    rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun K => by positivity) (hT.mul_left C)]
    refine ENNReal.tsum_le_tsum fun K => ?_
    simp only [F]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Icc]
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · calc ENNReal.ofReal (C * ((K : ℝ) ^ 5)⁻¹) * ∫⁻ r in Icc (-(K : ℝ)) K, ENNReal.ofReal (hfun r)
          ≤ ENNReal.ofReal (C * ((K : ℝ) ^ 5)⁻¹) * ENNReal.ofReal (G₁ * K ^ 3 + G₂) := by
            gcongr; exact hLS K hK
        _ = ENNReal.ofReal (C * (((K : ℝ) ^ 5)⁻¹ * (G₁ * (K : ℝ) ^ 3 + G₂))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
  have hcw : Continuous fun r : ℝ => Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4 :=
    (by fun_prop : Continuous fun r : ℝ => Real.exp (-(Real.pi * |r|))).div (by fun_prop)
      fun r => by positivity
  refine ⟨(hgm.mul hcw.aestronglyMeasurable), ?_⟩
  refine (lintegral_mono fun r => ?_).trans_lt ((lintegral_mono hpt).trans hint |>.trans_lt
    ENNReal.ofReal_lt_top)
  rw [Real.enorm_eq_ofReal (mul_nonneg (hg0 r) (by positivity))]

end

end GaloisForLFunctions.RHTower.DeckPointPair
