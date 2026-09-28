import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIMeanSquare
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRealNaturalBlocks
import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare

/-!
# The Deshouillers–Iwaniec and Watt mean values, and the amplifier against them

`MTDeshouillersIwaniecBound` is Matomäki–Teräväinen Lemma 3.5(ii) (Deshouillers–Iwaniec) and
`MTWattBound` is Lemma 3.5(i) (Watt), both in the Perron-line normalisation of the corpus's unit and
coefficient blocks.  The prime-power amplifier is split into its dyadic coefficient blocks, and the
Deshouillers–Iwaniec bound gives `∫_{T/2}^{T} |N|⁴ |𝓜|² ≤ 8(k+1) C T^η (T/N² + 1/T³)/(M k!)` when the
amplifier's support stays below `T^{1/5}`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Matomäki–Teräväinen Lemma 3.5(ii)** (Deshouillers–Iwaniec). -/
def MTDeshouillersIwaniecBound : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
    1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N → ∀ T : ℝ, 2 ≤ T →
    (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
        ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ)) ≤
      C * T ^ η *
        (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T + (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
              ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
            (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
          (1 / (A : ℝ)) * ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ (2 : ℕ))

/-- **Matomäki–Teräväinen Lemma 3.5(i)** (Watt). -/
def MTWattBound : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ) (B : ℝ),
    1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N → (∀ m, ‖a m‖ ≤ B) → ∀ T : ℝ, 2 ≤ T →
    (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
        ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ)) ≤
      C * T ^ η *
        (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T) / ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
            (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) * B ^ 2)

/-- A coefficient block is the literal sum over `(A, 2A]`. -/
theorem mtWattCoefficientBlock_eq_sum_Ioc (a : ℕ → ℂ) (A : ℕ) (t : ℝ) :
    mtWattCoefficientBlock a A t =
      ∑ n ∈ Finset.Ioc A (2 * A), a n * (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) := by
  classical
  rw [mtWattCoefficientBlock, perronPoly]
  have hsub : Finset.Ioc A (2 * A) ⊆ Finset.Icc 1 (2 * A) := fun n hn => by
    have := Finset.mem_Ioc.1 hn
    exact Finset.mem_Icc.2 ⟨by omega, this.2⟩
  rw [← Finset.sum_subset hsub fun n hn hnot => by
    have hn1 := (Finset.mem_Icc.1 hn).1
    rw [mtRealIntervalAF_apply_of_pos _ _ _ (by omega)]
    rw [if_neg]; · simp
    rintro ⟨h1, h2⟩
    apply hnot
    refine Finset.mem_Ioc.2 ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩]
  refine Finset.sum_congr rfl fun n hn => ?_
  have h := Finset.mem_Ioc.1 hn
  rw [mtRealIntervalAF_apply_of_pos _ _ _ (by omega), if_pos]
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- A truncated one-line Dirichlet polynomial supported in `(A₀, A₀·2^J]` is the sum of its `J`
dyadic coefficient blocks. -/
theorem perronPoly_one_eq_sum_mtWattCoefficientBlock (c : ℕ → ℂ) {K A₀ J : ℕ}
    (hc : ∀ n, c n ≠ 0 → n ≤ K ∧ A₀ < n ∧ n ≤ A₀ * 2 ^ J) (t : ℝ) :
    perronPoly c K 1 t = ∑ j ∈ Finset.range J, mtWattCoefficientBlock c (A₀ * 2 ^ j) t := by
  classical
  set f : ℕ → ℂ := fun n => c n * (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) with hf
  have hf0 : ∀ n, f n ≠ 0 → n ≤ K ∧ A₀ < n ∧ n ≤ A₀ * 2 ^ J := fun n hn =>
    hc n (left_ne_zero_of_mul hn)
  have e1 : ∑ n ∈ Finset.Icc 1 K, f n = ∑ n ∈ Finset.Icc 1 K ∪ Finset.Ioc A₀ (A₀ * 2 ^ J), f n :=
    Finset.sum_subset Finset.subset_union_left fun n _ hn => by
      by_contra hne
      obtain ⟨h1, h2, _⟩ := hf0 n hne
      exact hn (Finset.mem_Icc.2 ⟨by omega, h1⟩)
  have e2 : ∑ n ∈ Finset.Ioc A₀ (A₀ * 2 ^ J), f n =
      ∑ n ∈ Finset.Icc 1 K ∪ Finset.Ioc A₀ (A₀ * 2 ^ J), f n :=
    Finset.sum_subset Finset.subset_union_right fun n _ hn => by
      by_contra hne
      obtain ⟨_, h2, h3⟩ := hf0 n hne
      exact hn (Finset.mem_Ioc.2 ⟨h2, h3⟩)
  change ∑ n ∈ Finset.Icc 1 K, f n = _
  rw [e1, ← e2, mtSum_Ioc_dyadic]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mtWattCoefficientBlock_eq_sum_Ioc, show A₀ * 2 ^ (j + 1) = 2 * (A₀ * 2 ^ j) by ring]

theorem continuous_mtWattUnitBlock (N N' : ℕ) : Continuous (mtWattUnitBlock N N') :=
  continuous_perronPoly _ _ 1

theorem continuous_mtWattCoefficientBlock (a : ℕ → ℂ) (A : ℕ) :
    Continuous (mtWattCoefficientBlock a A) :=
  continuous_perronPoly _ _ 1

/-- `‖∑_{j<J} z_j‖² ≤ J ∑_{j<J} ‖z_j‖²`. -/
theorem norm_sum_range_sq_le (z : ℕ → ℂ) (J : ℕ) :
    ‖∑ j ∈ Finset.range J, z j‖ ^ 2 ≤ J * ∑ j ∈ Finset.range J, ‖z j‖ ^ 2 := by
  have h1 : ‖∑ j ∈ Finset.range J, z j‖ ≤ ∑ j ∈ Finset.range J, ‖z j‖ := norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range J) (f := fun j => ‖z j‖)
  rw [Finset.card_range] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- The total amplifier mass: `∑_m c_k(m) = |B|^k`. -/
theorem sum_primeSetCount_eq (B : Finset ℕ) (k : ℕ) :
    ∑ m ∈ primeSetSupport B k, primeSetCount B k m = B.card ^ k := by
  classical
  have hmaps : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => B), (∏ i, t i) ∈ primeSetSupport B k :=
    fun t ht => Finset.mem_image_of_mem (fun t : Fin k → ℕ => ∏ i, t i) ht
  have h := Finset.card_eq_sum_card_fiberwise (s := Fintype.piFinset fun _ : Fin k => B)
    (t := primeSetSupport B k) (f := fun t => ∏ i, t i) (fun t ht => hmaps t ht)
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  rfl

/-- The squared amplifier coefficients over any window have total mass `≤ |B|^k / k!`. -/
theorem sum_normSq_primeSetAmplifierCoeff_le {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (k : ℕ)
    (s : Finset ℕ) :
    ∑ m ∈ s, ‖primeSetAmplifierCoeff B k m‖ ^ 2 ≤ (B.card : ℝ) ^ k / k.factorial := by
  classical
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  calc ∑ m ∈ s, ‖primeSetAmplifierCoeff B k m‖ ^ 2
      ≤ ∑ m ∈ s.filter (fun m => m ∈ primeSetSupport B k), ‖primeSetAmplifierCoeff B k m‖ := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun m _ => ?_
        split_ifs with hm
        · have h1 := norm_primeSetAmplifierCoeff_le_one hB k m
          nlinarith [norm_nonneg (primeSetAmplifierCoeff B k m)]
        · have : primeSetAmplifierCoeff B k m = 0 := by
            by_contra hne; exact hm (mem_primeSetSupport_of_amplifierCoeff_ne_zero hne)
          simp [this]
    _ ≤ ∑ m ∈ primeSetSupport B k, ‖primeSetAmplifierCoeff B k m‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => (Finset.mem_filter.1 hm).2)
          fun _ _ _ => norm_nonneg _
    _ = ∑ m ∈ primeSetSupport B k, (primeSetCount B k m : ℝ) / k.factorial := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [primeSetAmplifierCoeff, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    _ = (B.card : ℝ) ^ k / k.factorial := by
        rw [← Finset.sum_div]
        congr 1
        exact_mod_cast sum_primeSetCount_eq B k

/-- **The Deshouillers–Iwaniec bound against the prime-power amplifier.** -/
theorem integral_unitBlock_fourth_amplifier_le (hDI : MTDeshouillersIwaniecBound) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ {B : Finset ℕ} {P : ℝ} {k K N N' : ℕ} {T : ℝ},
      (∀ p ∈ B, p.Prime) → (∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) → 2 ≤ P → 1 ≤ k →
      (2 * P) ^ k ≤ K → 1 ≤ N → N < N' → N' ≤ 2 * N → 2 ≤ T →
      (2 * P) ^ k ≤ T ^ (1 / 5 : ℝ) →
      (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
          ‖perronPoly (primeSetAmplifierCoeff B k) K 1 t‖ ^ (2 : ℕ)) ≤
        (k + 1) * C * T ^ η * (16 * T / ((N : ℝ) ^ (2 : ℕ) * P ^ k) + 4 / (T ^ (3 : ℕ) * P ^ k)) *
          (2 * (P + 1) ^ k / (P ^ k * k.factorial)) := by
  obtain ⟨C, hC, hbound⟩ := hDI η hη
  refine ⟨C, hC, ?_⟩
  intro B P k K N N' T hBp hB hP hk hK hN hNN' hN' hT hT5
  classical
  set A₀ : ℕ := ⌊P ^ k⌋₊ with hA₀
  set c := primeSetAmplifierCoeff B k with hcdef
  have hP0 : 0 < P := by linarith
  have hPk1 : 2 ≤ P ^ k := by
    calc (2 : ℝ) ≤ P := hP
      _ = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ k := pow_le_pow_right₀ (by linarith) hk
  have hA₀1 : 1 ≤ A₀ := Nat.le_floor (by push_cast; linarith)
  have hA₀lo : P ^ k / 2 ≤ (A₀ : ℝ) := by
    have := Nat.lt_floor_add_one (P ^ k)
    rw [← hA₀] at this
    have h1 : (1 : ℝ) ≤ A₀ := by exact_mod_cast hA₀1
    linarith
  have hA₀le : (A₀ : ℝ) ≤ P ^ k := Nat.floor_le (by positivity)
  -- support of the amplifier in `(A₀, A₀·2^(k+1)]`
  have hsupp : ∀ n, c n ≠ 0 → n ≤ K ∧ A₀ < n ∧ n ≤ A₀ * 2 ^ (k + 1) := by
    intro n hn
    have hmem := mem_primeSetSupport_of_amplifierCoeff_ne_zero hn
    obtain ⟨hlo, hhi⟩ := mem_primeSetSupport_bounds hP0.le hB hk hmem
    refine ⟨?_, ?_, ?_⟩
    · exact_mod_cast hhi.trans hK
    · exact (Nat.floor_lt (by positivity)).2 hlo
    · have h2 : (2 * P) ^ k = 2 ^ k * P ^ k := by rw [mul_pow]
      have hlt := Nat.lt_floor_add_one (P ^ k)
      rw [← hA₀] at hlt
      have : (n : ℝ) < ((A₀ * 2 ^ (k + 1) : ℕ) : ℝ) + 1 := by
        push_cast
        have h2k : (0 : ℝ) < 2 ^ k := by positivity
        have h1 : (1 : ℝ) ≤ A₀ := by exact_mod_cast hA₀1
        calc (n : ℝ) ≤ 2 ^ k * P ^ k := h2 ▸ hhi
          _ < 2 ^ k * ((A₀ : ℝ) + 1) := by gcongr
          _ ≤ (A₀ : ℝ) * 2 ^ (k + 1) := by rw [pow_succ]; nlinarith
          _ < _ := by linarith
      exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  -- pointwise Cauchy–Schwarz over the `k + 1` blocks
  have hpt : ∀ t, ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) * ‖perronPoly c K 1 t‖ ^ (2 : ℕ) ≤
      (k + 1 : ℝ) * ∑ j ∈ Finset.range (k + 1),
        ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) * ‖mtWattCoefficientBlock c (A₀ * 2 ^ j) t‖ ^ (2 : ℕ) := by
    intro t
    rw [perronPoly_one_eq_sum_mtWattCoefficientBlock c hsupp t]
    have h := norm_sum_range_sq_le (fun j => mtWattCoefficientBlock c (A₀ * 2 ^ j) t) (k + 1)
    rw [← Finset.mul_sum, mul_left_comm]
    push_cast at h
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hint : ∀ j, IntervalIntegrable (fun t => ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
      ‖mtWattCoefficientBlock c (A₀ * 2 ^ j) t‖ ^ (2 : ℕ)) volume (T / 2) T := fun j =>
    (((continuous_mtWattUnitBlock N N').norm.pow 4).mul
      ((continuous_mtWattCoefficientBlock c _).norm.pow 2)).intervalIntegrable _ _
  have hT2 : T / 2 ≤ T := by linarith
  have hstep : (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
        ‖perronPoly c K 1 t‖ ^ (2 : ℕ)) ≤
      (k + 1 : ℝ) * ∑ j ∈ Finset.range (k + 1), ∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) * ‖mtWattCoefficientBlock c (A₀ * 2 ^ j) t‖ ^ (2 : ℕ) := by
    rw [← intervalIntegral.integral_finsetSum fun j _ => hint j, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT2 ?_ ?_ fun t _ => hpt t
    · exact (((continuous_mtWattUnitBlock N N').norm.pow 4).mul
        ((continuous_perronPoly c K 1).norm.pow 2)).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_finsetSum _ fun j _ =>
        (((continuous_mtWattUnitBlock N N').norm.pow 4).mul
          ((continuous_mtWattCoefficientBlock c _).norm.pow 2))))
        |>.intervalIntegrable _ _
  refine hstep.trans ?_
  -- the Deshouillers–Iwaniec bound on every block
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hblockA : ∀ j ∈ Finset.range (k + 1), 1 ≤ A₀ * 2 ^ j ∧
      ((A₀ * 2 ^ j : ℕ) : ℝ) ≤ T ^ (1 / 5 : ℝ) ∧ P ^ k / 2 ≤ ((A₀ * 2 ^ j : ℕ) : ℝ) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    refine ⟨Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
    · push_cast
      calc (A₀ : ℝ) * 2 ^ j ≤ P ^ k * 2 ^ k :=
            mul_le_mul hA₀le (pow_le_pow_right₀ (by norm_num) hjk) (by positivity) (by positivity)
        _ = (2 * P) ^ k := by rw [mul_pow]; ring
        _ ≤ T ^ (1 / 5 : ℝ) := hT5
    · push_cast
      calc P ^ k / 2 ≤ A₀ := hA₀lo
        _ ≤ (A₀ : ℝ) * 2 ^ j := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  have hPk0 : 0 < P ^ k := by positivity
  set S : ℕ → ℝ := fun j => ∑ m ∈ Finset.Ioc (A₀ * 2 ^ j) (2 * (A₀ * 2 ^ j)), ‖c m‖ ^ (2 : ℕ)
    with hSdef
  set Q : ℝ := 6 * T / ((N : ℝ) ^ (2 : ℕ) * P ^ k) + 4 / (T ^ (3 : ℕ) * P ^ k) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hblock : ∀ j ∈ Finset.range (k + 1), (∫ t in (T / 2)..T,
      ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) * ‖mtWattCoefficientBlock c (A₀ * 2 ^ j) t‖ ^ (2 : ℕ)) ≤
      C * T ^ η * Q * (2 / P ^ k * S j) := by
    intro j hj
    obtain ⟨hA1, hAT, hAlo⟩ := hblockA j hj
    refine (hbound c (A₀ * 2 ^ j) N N' hA1 hN hNN' hN' T hT).trans ?_
    set A : ℝ := ((A₀ * 2 ^ j : ℕ) : ℝ) with hAdef
    have hA0 : 0 < A := by rw [hAdef]; exact_mod_cast hA1
    have hAT' : A ≤ T := hAT.trans (by
      calc T ^ (1 / 5 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        _ = T := Real.rpow_one T)
    have hsq : A ^ (2 : ℕ) * Real.sqrt T ≤ T := by
      have h1 : A ^ (2 : ℕ) ≤ T ^ (2 / 5 : ℝ) := by
        calc A ^ (2 : ℕ) ≤ (T ^ (1 / 5 : ℝ)) ^ (2 : ℕ) := pow_le_pow_left₀ hA0.le hAT 2
          _ = T ^ (2 / 5 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
      calc A ^ (2 : ℕ) * Real.sqrt T ≤ T ^ (2 / 5 : ℝ) * T ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]; gcongr
        _ = T ^ (9 / 10 : ℝ) := by rw [← Real.rpow_add hT0]; norm_num
        _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        _ = T := Real.rpow_one T
    have hfq : A ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) ≤ T := by
      calc A ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) ≤ (T ^ (1 / 5 : ℝ)) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by
            gcongr
        _ = T := by rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]; norm_num
    have hN0 : (0 : ℝ) < (N : ℝ) ^ (2 : ℕ) := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      positivity
    have hterm1 : (T + A ^ (2 : ℕ) * Real.sqrt T + A ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
        ((N : ℝ) ^ (2 : ℕ) * A) ≤ 6 * T / ((N : ℝ) ^ (2 : ℕ) * P ^ k) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (T + A ^ (2 : ℕ) * Real.sqrt T + A ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) ≤ 3 * T := by
        linarith
      have hA2 : P ^ k ≤ 2 * A := by linarith
      calc (T + A ^ (2 : ℕ) * Real.sqrt T + A ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) *
            ((N : ℝ) ^ (2 : ℕ) * P ^ k) ≤ (3 * T) * ((N : ℝ) ^ (2 : ℕ) * (2 * A)) := by gcongr
        _ = 6 * T * ((N : ℝ) ^ (2 : ℕ) * A) := by ring
    have hterm2 : (T + A) / (T ^ (4 : ℕ) * A) ≤ 4 / (T ^ (3 : ℕ) * P ^ k) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hA2 : P ^ k ≤ 2 * A := by linarith
      calc (T + A) * (T ^ (3 : ℕ) * P ^ k) ≤ (2 * T) * (T ^ (3 : ℕ) * (2 * A)) := by gcongr; linarith
        _ = 4 * (T ^ (4 : ℕ) * A) := by ring
    have hinv : 1 / A ≤ 2 / P ^ k := by
      rw [div_le_div_iff₀ hA0 hPk0]; linarith
    have hS0 : 0 ≤ S j := Finset.sum_nonneg fun _ _ => by positivity
    have hCT : 0 ≤ C * T ^ η := by positivity
    calc C * T ^ η * (((T + A ^ (2 : ℕ) * Real.sqrt T + A ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
            ((N : ℝ) ^ (2 : ℕ) * A) + (T + A) / (T ^ (4 : ℕ) * A)) * (1 / A) *
            ∑ m ∈ Finset.Ioc (A₀ * 2 ^ j) (2 * (A₀ * 2 ^ j)), ‖c m‖ ^ (2 : ℕ))
        = C * T ^ η * (((T + A ^ (2 : ℕ) * Real.sqrt T + A ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
            ((N : ℝ) ^ (2 : ℕ) * A) + (T + A) / (T ^ (4 : ℕ) * A)) * ((1 / A) * S j)) := by
          rw [hSdef]; ring
      _ ≤ C * T ^ η * (Q * (2 / P ^ k * S j)) := by
          gcongr
          rw [hQ]; linarith
      _ = C * T ^ η * Q * (2 / P ^ k * S j) := by ring
  have hsumS : ∑ j ∈ Finset.range (k + 1), S j ≤ (P + 1) ^ k / k.factorial := by
    have hdy := mtSum_Ioc_dyadic A₀ (fun m => ‖c m‖ ^ (2 : ℕ)) (k + 1)
    have hre : ∑ j ∈ Finset.range (k + 1), S j =
        ∑ n ∈ Finset.Ioc A₀ (A₀ * 2 ^ (k + 1)), ‖c n‖ ^ (2 : ℕ) := by
      rw [hdy]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hSdef, show A₀ * 2 ^ (j + 1) = 2 * (A₀ * 2 ^ j) by ring]
    rw [hre]
    refine (sum_normSq_primeSetAmplifierCoeff_le hBp k _).trans ?_
    have hcard := card_le_of_subset_Ioc_real hP0.le hB
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard k) hf.le
  calc (k + 1 : ℝ) * ∑ j ∈ Finset.range (k + 1), ∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) * ‖mtWattCoefficientBlock c (A₀ * 2 ^ j) t‖ ^ (2 : ℕ)
      ≤ (k + 1 : ℝ) * ∑ j ∈ Finset.range (k + 1), C * T ^ η * Q * (2 / P ^ k * S j) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hblock) (by positivity)
    _ = (k + 1) * C * T ^ η * Q * (2 / P ^ k * ∑ j ∈ Finset.range (k + 1), S j) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ (k + 1) * C * T ^ η * Q * (2 / P ^ k * ((P + 1) ^ k / k.factorial)) := by
        gcongr
    _ ≤ (k + 1) * C * T ^ η * (16 * T / ((N : ℝ) ^ (2 : ℕ) * P ^ k) + 4 / (T ^ (3 : ℕ) * P ^ k)) *
          (2 * (P + 1) ^ k / (P ^ k * k.factorial)) := by
        have hQ' : Q ≤ 16 * T / ((N : ℝ) ^ (2 : ℕ) * P ^ k) + 4 / (T ^ (3 : ℕ) * P ^ k) := by
          rw [hQ]
          have : 6 * T / ((N : ℝ) ^ (2 : ℕ) * P ^ k) ≤ 16 * T / ((N : ℝ) ^ (2 : ℕ) * P ^ k) := by
            gcongr; norm_num
          linarith
        have heq : 2 / P ^ k * ((P + 1) ^ k / k.factorial) = 2 * (P + 1) ^ k / (P ^ k * k.factorial) := by
          field_simp
        rw [heq]
        gcongr

end

end RHTower.Sieve
