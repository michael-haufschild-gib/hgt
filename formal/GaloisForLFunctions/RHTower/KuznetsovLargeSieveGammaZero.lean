import GaloisForLFunctions.RHTower.KuznetsovGammaZeroGeomBound

/-!
# The large sieve for `Γ₀(Q)` at the cusp `∞` with the Gaussian weight

For `Q ∣ L + 1`, the cusp vector `1_H` of `Γ₀(Q)` in the deck of level `L`, coefficients `a` on
`(N, 2N]` and `K ≥ 1`, the same-sign Kuznetsov inequality `large_sieve_full` with `b_k = ā_k √(2πk)`
and the bound for its geometric side give (`large_sieve_gamma0_level`)

`Σ_j c₀(κ_j + 1)e^{−πκ_j}[λ_j ≤ ¼ + K²] |Σ_n a_n ρ_j(1_H, n)|²
   + (4π)⁻¹ ∫_{−K}^{K} c₀(|r| + 1)e^{−π|r|} Σ_i |Σ_n a_n η_i(1_H, r, n)|² dr
  ≤ 2|H| (√π/2 K³ + P K N^{1+2δ} Q^{−1−δ/2} Z + P₃ K² e^{−K²/2}(N² Q^{−2} Z₂ + N³ Q^{−3} Z₃)) Σ|a_n|²`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex Filter Topology
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry RHTower.Sieve KuznetsovGauss KuznetsovSeparation

noncomputable section

/-- `∫ t² e^{−(t/K)²} dt = (√π/2) K³`. -/
theorem gaussMass_eq {K : ℝ} (hK : 0 < K) : gaussMass K = Real.sqrt Real.pi / 2 * K ^ 3 := by
  unfold gaussMass gaussWeight
  have hb : (0 : ℝ) < (K⁻¹) ^ 2 := by positivity
  have e : (fun t : ℝ => t ^ 2 * Real.exp (-(t / K) ^ 2)) =
      fun t => t ^ 2 * Real.exp (-((K⁻¹) ^ 2) * t ^ 2) := by
    funext t; congr 2; field_simp
  rw [e, integral_sq_mul_exp_neg_sq hb]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.inv_rpow hK.le,
    ← Real.rpow_neg hK.le]
  norm_num

/-- The frequencies `μ_k = max(k, 1)`. -/
def gamma0Freq (k : ℕ) : ℝ := ((max k 1 : ℕ) : ℝ)

theorem gamma0Freq_pos (k : ℕ) : 0 < gamma0Freq k := by
  unfold gamma0Freq; exact_mod_cast lt_of_lt_of_le zero_lt_one (le_max_right k 1)

theorem gamma0Freq_of_mem {N k : ℕ} (hk : k ∈ Finset.Ioc N (N + N)) : gamma0Freq k = k := by
  rw [Finset.mem_Ioc] at hk
  unfold gamma0Freq
  rw [max_eq_left (by omega)]

theorem summable_intKloosterman_mul_gamma0Weight (Q : ℕ) {K : ℝ} (hK : 0 < K) (m n : ℕ) :
    Summable fun c : ℤ => intKloosterman m n c * gamma0Weight Q K m n c := by
  set B := Real.pi * (4 * Real.pi * Real.sqrt ((m : ℝ) * n)) * gaussSinhMass K
  have hB : 0 ≤ B := by
    have : 0 ≤ gaussSinhMass K := integral_nonneg fun w => abs_nonneg _
    positivity
  refine ((summable_natAbs_rpow (s := 2) (by norm_num)).mul_left B).of_norm_bounded ?_
  intro c
  by_cases hc : c = 0
  · subst hc
    simp only [intKloosterman, dif_pos, zero_mul, norm_zero]
    positivity
  · haveI : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.2 hc⟩
    have hc0 : (0 : ℝ) < c.natAbs := by exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 hc)
    have h1 : ‖intKloosterman m n c‖ ≤ c.natAbs := by
      rw [intKloosterman, dif_neg hc]
      exact (norm_kloostermanSum_le_totient _ _ _).trans (by exact_mod_cast Nat.totient_le _)
    have h2 := norm_gamma0Weight_le Q (m := m) (n := n) hK hc
    have e : ((c : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) = (c.natAbs : ℝ) ^ (-(3 : ℝ)) := by
      have : (c : ℝ) ^ 2 = (c.natAbs : ℝ) ^ 2 := by
        rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
      rw [this, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
      norm_num
    rw [e] at h2
    have e2 : (c.natAbs : ℝ) * (c.natAbs : ℝ) ^ (-(3 : ℝ)) = (c.natAbs : ℝ) ^ (-(2 : ℝ)) := by
      rw [show (c.natAbs : ℝ) * (c.natAbs : ℝ) ^ (-(3 : ℝ)) = (c.natAbs : ℝ) ^ ((1 : ℝ) + -(3 : ℝ)) by
        rw [Real.rpow_add hc0, Real.rpow_one]]
      norm_num
    rw [norm_mul]
    calc ‖intKloosterman m n c‖ * ‖gamma0Weight Q K m n c‖
        ≤ (c.natAbs : ℝ) * (B * (c.natAbs : ℝ) ^ (-(3 : ℝ))) := by gcongr
      _ = B * (c.natAbs : ℝ) ^ (-(2 : ℝ)) := by rw [← e2]; ring

open Classical in
/-- **The geometric side for `Γ₀(Q)`.** -/
theorem exists_norm_geomForm_gamma0_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ P P₃ : ℝ, 0 ≤ P ∧ 0 ≤ P₃ ∧ ∀ {L Q : ℕ}, Q ∣ L + 1 → ∀ (N : ℕ), 1 ≤ N → ∀ (K : ℝ), 1 ≤ K →
      ∀ (a : ℕ → ℂ),
        ‖geomForm 1 K (Finset.Ioc N (N + N)) gamma0Freq (fun _ => gamma0Vec L Q) (gamma0Coeff a)‖ ≤
          2 * (Fintype.card (gamma0Deck L Q) : ℝ) * (Real.sqrt Real.pi / 2 * K ^ 3 +
            (P * K * (N : ℝ) ^ (1 + 2 * δ) * ((Q : ℝ) ^ (-(1 + δ / 2)) * intZeta (1 + δ / 2)) +
              P₃ * K ^ 2 * Real.exp (-K ^ 2 / 2) *
                ((N : ℝ) ^ 2 * ((Q : ℝ) ^ (-(2 : ℝ)) * intZeta 2) +
                  (N : ℝ) ^ 3 * ((Q : ℝ) ^ (-(3 : ℝ)) * intZeta 3)))) *
            ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2 := by
  obtain ⟨P, P₃, hP, hP₃, hpart⟩ := exists_norm_tsum_kloosterman_part_le hδ hδ1
  refine ⟨P, P₃, hP, hP₃, fun {L Q} hQ N hN K hK a => ?_⟩
  classical
  set S := Finset.Ioc N (N + N)
  set A := ∑ k ∈ S, ‖a k‖ ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ => by positivity
  have hK0 : 0 < K := by linarith
  have hQ1 : 1 ≤ Q := Nat.pos_of_dvd_of_pos hQ (Nat.succ_pos L)
  set b := gamma0Coeff a
  set H : ℂ := (Fintype.card (gamma0Deck L Q) : ℂ)
  set F : ℤ → ℂ := fun c => ∑ k ∈ S, ∑ l ∈ S,
    conj (b k) * b l * (intKloosterman k l c * gamma0Weight Q K k l c)
  obtain ⟨hFsum, hFle⟩ := hpart Q hQ1 N hN K hK a
  -- the row formula on the support
  have hrow : ∀ k ∈ S, ∀ l ∈ S, geomRow 1 K (gamma0Freq k) (gamma0Freq l) (gamma0Vec L Q)
      (gamma0Vec L Q) = (if k = l then 4 * H * ((4 * Real.pi * k : ℝ) : ℂ)⁻¹ * (gaussMass K : ℂ)
        else 0) + 2 * H * ∑' c : ℤ, intKloosterman k l c * gamma0Weight Q K k l c := by
    intro k hk l hl
    rw [gamma0Freq_of_mem hk, gamma0Freq_of_mem hl]
    have hk0 : 0 < k := by rw [Finset.mem_Ioc] at hk; omega
    exact geomRow_gamma0 hQ hK0 k l hk0
  have hsplit : geomForm 1 K S gamma0Freq (fun _ => gamma0Vec L Q) b =
      (∑ k ∈ S, ∑ l ∈ S, conj (b k) * b l *
        (if k = l then 4 * H * ((4 * Real.pi * k : ℝ) : ℂ)⁻¹ * (gaussMass K : ℂ) else 0)) +
      2 * H * ∑' c : ℤ, F c := by
    rw [geomForm]
    have hint : ∀ k ∈ S, ∀ l ∈ S, conj (b k) * b l * ∑' c : ℤ,
        intKloosterman k l c * gamma0Weight Q K k l c =
        ∑' c : ℤ, conj (b k) * b l * (intKloosterman k l c * gamma0Weight Q K k l c) := by
      intro k _ l _
      exact ((summable_intKloosterman_mul_gamma0Weight Q hK0 k l).tsum_mul_left _).symm
    have hswap : ∑ k ∈ S, ∑ l ∈ S, conj (b k) * b l * ∑' c : ℤ,
        intKloosterman k l c * gamma0Weight Q K k l c = ∑' c : ℤ, F c := by
      rw [Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => hint k hk l hl]
      simp only [F]
      rw [Summable.tsum_finsetSum fun k _ => ?_]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [Summable.tsum_finsetSum fun l _ =>
          (summable_intKloosterman_mul_gamma0Weight Q hK0 k l).mul_left _]
      · exact summable_sum fun l _ => (summable_intKloosterman_mul_gamma0Weight Q hK0 k l).mul_left _
    rw [← hswap, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hrow k hk l hl]
    ring
  have hdiag : (∑ k ∈ S, ∑ l ∈ S, conj (b k) * b l *
      (if k = l then 4 * H * ((4 * Real.pi * k : ℝ) : ℂ)⁻¹ * (gaussMass K : ℂ) else 0)) =
      ((2 * (Fintype.card (gamma0Deck L Q) : ℝ) * gaussMass K * A : ℝ) : ℂ) := by
    rw [show A = ∑ k ∈ S, ‖a k‖ ^ 2 from rfl, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_eq_single k (fun l _ hne => by rw [if_neg (Ne.symm hne), mul_zero])
      (fun h => absurd hk h), if_pos rfl]
    have hk0 : (0 : ℝ) < k := by
      rw [Finset.mem_Ioc] at hk; exact_mod_cast (Nat.zero_le N).trans_lt hk.1
    have hbb : conj (b k) * b k = ((2 * Real.pi * k * ‖a k‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj', ← norm_gamma0Coeff_sq]; push_cast; rfl
    rw [← mul_assoc, hbb]
    simp only [H]
    have : ((4 * Real.pi * k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 4 * Real.pi * k).ne'
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
    push_cast
    field_simp
  rw [hsplit, hdiag]
  have hG := gaussMass_eq hK0
  have hcard : (0 : ℝ) ≤ (Fintype.card (gamma0Deck L Q) : ℝ) := Nat.cast_nonneg _
  calc ‖((2 * (Fintype.card (gamma0Deck L Q) : ℝ) * gaussMass K * A : ℝ) : ℂ) + 2 * H * ∑' c : ℤ, F c‖
      ≤ 2 * (Fintype.card (gamma0Deck L Q) : ℝ) * gaussMass K * A +
          2 * (Fintype.card (gamma0Deck L Q) : ℝ) * ‖∑' c : ℤ, F c‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [Complex.norm_real, Real.norm_of_nonneg (by rw [hG]; positivity), norm_mul, norm_mul]
        simp [H]
    _ ≤ _ := by
        rw [hG]
        have := mul_le_mul_of_nonneg_left hFle (by positivity : (0 : ℝ) ≤ 2 * (Fintype.card (gamma0Deck L Q) : ℝ))
        linarith

/-! ## The spectral side -/

theorem ofReal_cpow_neg_half_mul_sqrt {x : ℝ} (hx : 0 < x) :
    ((x : ℝ) : ℂ) ^ (-(((1 : ℝ) : ℂ) - 1 / 2)) * ((Real.sqrt x : ℝ) : ℂ) = 1 := by
  have e : (-(((1 : ℝ) : ℂ) - 1 / 2)) = ((-(1 / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e, ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul, Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  norm_num

theorem conj_gamma0Coeff (a : ℕ → ℂ) (k : ℕ) :
    conj (gamma0Coeff a k) = a k * ((Real.sqrt (2 * Real.pi * k) : ℝ) : ℂ) := by
  rw [gamma0Coeff, map_mul, Complex.conj_conj, Complex.conj_ofReal]

theorem specCoeff_gamma0 {L : ℕ} (j : CuspEigenIndex L) (Q N : ℕ) (a : ℕ → ℂ) :
    specCoeff j 1 (Finset.Ioc N (N + N)) gamma0Freq (fun _ => gamma0Vec L Q) (gamma0Coeff a) =
      ∑ k ∈ Finset.Ioc N (N + N), a k * cuspCoeff j k (gamma0Vec L Q) := by
  rw [specCoeff]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (0 : ℝ) < 2 * Real.pi * k := by
    rw [Finset.mem_Ioc] at hk
    have : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_le N).trans_lt hk.1
    positivity
  rw [gamma0Freq_of_mem hk, conj_gamma0Coeff]
  have h := ofReal_cpow_neg_half_mul_sqrt hk0
  calc a k * ((Real.sqrt (2 * Real.pi * k) : ℝ) : ℂ) * cuspCoeff j k (gamma0Vec L Q) *
        ((2 * Real.pi * k : ℝ) : ℂ) ^ (-(((1 : ℝ) : ℂ) - 1 / 2))
      = a k * cuspCoeff j k (gamma0Vec L Q) * (((2 * Real.pi * k : ℝ) : ℂ) ^ (-(((1 : ℝ) : ℂ) - 1 / 2)) *
          ((Real.sqrt (2 * Real.pi * k) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [h, mul_one]

/-- The Eisenstein frequencies `n_k = max(k, 1)(L + 1)`. -/
def gamma0EisFreq (L : ℕ) (k : ℕ) : ℤ := ((max k 1 : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ)

theorem eisSpecCoeff_gamma0 {L : ℕ} (i : Fin (Module.finrank ℂ (cuspVecSub L))) (r : ℝ) (Q N : ℕ)
    (a : ℕ → ℂ) :
    eisSpecCoeff i 1 r (Finset.Ioc N (N + N)) gamma0Freq (fun _ => gamma0Vec L Q) (gamma0EisFreq L)
        (gamma0Coeff a) =
      ∑ k ∈ Finset.Ioc N (N + N), a k *
        eisCoeff (1 / 2 + r * Complex.I) (gamma0Vec L Q) (cuspBasisVec L i) ((k : ℤ) * ((L + 1 : ℕ) : ℤ)) := by
  rw [eisSpecCoeff]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (0 : ℝ) < 2 * Real.pi * k := by
    rw [Finset.mem_Ioc] at hk
    have : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_le N).trans_lt hk.1
    positivity
  have hmax : max k 1 = k := by rw [Finset.mem_Ioc] at hk; omega
  have hn : gamma0EisFreq L k = (k : ℤ) * ((L + 1 : ℕ) : ℤ) := by rw [gamma0EisFreq, hmax]
  rw [gamma0Freq_of_mem hk, conj_gamma0Coeff, hn]
  have h := ofReal_cpow_neg_half_mul_sqrt hk0
  calc a k * ((Real.sqrt (2 * Real.pi * k) : ℝ) : ℂ) *
        eisCoeff (1 / 2 + r * Complex.I) (gamma0Vec L Q) (cuspBasisVec L i) ((k : ℤ) * ((L + 1 : ℕ) : ℤ)) *
        ((2 * Real.pi * k : ℝ) : ℂ) ^ (-(((1 : ℝ) : ℂ) - 1 / 2))
      = a k * eisCoeff (1 / 2 + r * Complex.I) (gamma0Vec L Q) (cuspBasisVec L i)
          ((k : ℤ) * ((L + 1 : ℕ) : ℤ)) * (((2 * Real.pi * k : ℝ) : ℂ) ^ (-(((1 : ℝ) : ℂ) - 1 / 2)) *
          ((Real.sqrt (2 * Real.pi * k) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [h, mul_one]

open Classical in
/-- **The Gaussian-weighted large sieve for `Γ₀(Q)` at `∞`.** -/
theorem large_sieve_gamma0_level {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ P P₃ : ℝ, 0 ≤ P ∧ 0 ≤ P₃ ∧ ∀ {L Q : ℕ}, 2 ≤ L → Q ∣ L + 1 → ∀ (N : ℕ), 1 ≤ N →
      ∀ (K : ℝ), 1 ≤ K → ∀ (a : ℕ → ℂ),
        (∑' j : CuspEigenIndex L, ENNReal.ofReal (sieveWeight K j.1 *
            ‖∑ k ∈ Finset.Ioc N (N + N), a k * cuspCoeff j k (gamma0Vec L Q)‖ ^ 2)) +
          ∫⁻ r in Icc (-K) K, ENNReal.ofReal ((4 * Real.pi)⁻¹ *
            (specWeightConst * (|r| + 1) * Real.exp (-(Real.pi * |r|))) *
              ∑ i, ‖∑ k ∈ Finset.Ioc N (N + N), a k * eisCoeff (1 / 2 + r * Complex.I) (gamma0Vec L Q)
                (cuspBasisVec L i) ((k : ℤ) * ((L + 1 : ℕ) : ℤ))‖ ^ 2)
        ≤ ENNReal.ofReal (2 * (Fintype.card (gamma0Deck L Q) : ℝ) * (Real.sqrt Real.pi / 2 * K ^ 3 +
            (P * K * (N : ℝ) ^ (1 + 2 * δ) * ((Q : ℝ) ^ (-(1 + δ / 2)) * intZeta (1 + δ / 2)) +
              P₃ * K ^ 2 * Real.exp (-K ^ 2 / 2) *
                ((N : ℝ) ^ 2 * ((Q : ℝ) ^ (-(2 : ℝ)) * intZeta 2) +
                  (N : ℝ) ^ 3 * ((Q : ℝ) ^ (-(3 : ℝ)) * intZeta 3)))) *
            ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2) := by
  obtain ⟨P, P₃, hP, hP₃, hgeom⟩ := exists_norm_geomForm_gamma0_le hδ hδ1
  refine ⟨P, P₃, hP, hP₃, fun {L Q} hL hQ N hN K hK a => ?_⟩
  have hv : ∀ k, IsCuspEigen (gamma0Freq k) ((fun _ : ℕ => gamma0Vec L Q) k) := fun k => by
    have := isCuspEigen_gamma0Vec hQ ((max k 1 : ℕ) : ℤ)
    simpa [gamma0Freq] using this
  have hn : ∀ k, gamma0Freq k * ((L + 1 : ℕ) : ℝ) = gamma0EisFreq L k := fun k => by
    simp [gamma0Freq, gamma0EisFreq]
  have h := large_sieve_full hL hK (Finset.Ioc N (N + N)) gamma0Freq_pos hv hn (gamma0Coeff a)
  simp only [specCoeff_gamma0, eisSpecCoeff_gamma0] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (hgeom hQ N hN K hK a))

end

end GaloisForLFunctions.RHTower.DeckPointPair
