import GaloisForLFunctions.RHTower.BaezDuarteGibbsChannel
import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic
import GaloisForLFunctions.RHTower.SquarefreeLowerDensity

/-!
# The unconditional feature-norm scale

The spectral feature energy `Σ_n μ(n)² n^{-2}(1-n^{-2})^{2k}` is between two positive multiples of
`k^{-1/2}`.  The upper bound is elementary: `(1-n^{-2})^{2k} ≤ e^{-2k/n²} ≤ n⁴/(2k²)` handles
`n ≤ √k` and the inverse-square tail handles the rest.  The lower bound restricts to squarefree
`n` with `4k < n² ≤ 100k`, where Bernoulli gives `(1-n^{-2})^{2k} ≥ 1/2`, and counts them with the
quarter-density of the squarefree integers.
-/

namespace RHTower

open Real MeasureTheory ArithmeticFunction

noncomputable section

/-- The unnormalized feature energy `Σ_n μ(n)² n^{-2} (1-n^{-2})^{2k}`. -/
def bdFeatureEnergy (k : ℕ) : ℝ :=
  ∑' n : ℕ, squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k)

theorem squarefreeMobiusMass_le_inv_sq (n : ℕ) :
    squarefreeMobiusMass 2 n ≤ ((n : ℝ) ^ 2)⁻¹ := by
  rw [squarefreeMobiusMass]
  have hval : ((n : ℝ)) ^ (-(2 : ℝ)) = ((n : ℝ) ^ 2)⁻¹ := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      norm_num
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h0
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn0.le,
        Real.rpow_natCast]
  split_ifs
  · exact le_of_eq hval
  · positivity

theorem bdSpectralValue_pow_le_exp {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    bdSpectralValue n ^ m ≤ Real.exp (-((m : ℝ) * ((n : ℝ) ^ 2)⁻¹)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hX := bdSpectralValue_mem n
  have h1 : bdSpectralValue n ≤ Real.exp (-((n : ℝ) ^ 2)⁻¹) := by
    have := Real.add_one_le_exp (-((n : ℝ) ^ 2)⁻¹)
    rw [bdSpectralValue]
    linarith
  have h2 : bdSpectralValue n ^ m ≤ (Real.exp (-((n : ℝ) ^ 2)⁻¹)) ^ m :=
    pow_le_pow_left₀ hX.1 h1 m
  have h3 : (Real.exp (-((n : ℝ) ^ 2)⁻¹)) ^ m = Real.exp (-((m : ℝ) * ((n : ℝ) ^ 2)⁻¹)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  linarith [h2, h3.le, h3.ge]

theorem exp_neg_le_two_div_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h1 : y ^ 2 / 2 ≤ Real.exp y := by
    have := Real.quadratic_le_exp_of_nonneg hy.le
    linarith
  have h2 : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [h2, inv_le_iff_one_le_mul₀ (Real.exp_pos y)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [Real.exp_pos y]

/-- Each energy term is dominated by `n²/(2k²)`. -/
theorem energy_term_le_head {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k)
      ≤ (n : ℝ) ^ 2 / (2 * (k : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hmass := squarefreeMobiusMass_le_inv_sq n
  have hmass0 : 0 ≤ squarefreeMobiusMass 2 n := squarefreeMobiusMass_nonneg 2 n
  have hX := bdSpectralValue_mem n
  have hpow := bdSpectralValue_pow_le_exp hn (2 * k)
  have hy : (0 : ℝ) < ((2 * k : ℕ) : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
    have : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by
      have : 0 < 2 * k := by omega
      exact_mod_cast this
    positivity
  have hexp := exp_neg_le_two_div_sq hy
  have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  rw [hcast] at hpow hy hexp
  have hkey : (2 : ℝ) / (2 * (k : ℝ) * ((n : ℝ) ^ 2)⁻¹) ^ 2 = (n : ℝ) ^ 4 / (2 * (k : ℝ) ^ 2) := by
    field_simp
  rw [hkey] at hexp
  have hpow0 : 0 ≤ bdSpectralValue n ^ (2 * k) := pow_nonneg hX.1 (2 * k)
  calc squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k)
      ≤ ((n : ℝ) ^ 2)⁻¹ * bdSpectralValue n ^ (2 * k) :=
        mul_le_mul_of_nonneg_right hmass hpow0
    _ ≤ ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ) ^ 4 / (2 * (k : ℝ) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (le_trans hpow hexp) (by positivity)
    _ = (n : ℝ) ^ 2 / (2 * (k : ℝ) ^ 2) := by
        field_simp

theorem energy_term_nonneg (k n : ℕ) :
    0 ≤ squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k) :=
  mul_nonneg (squarefreeMobiusMass_nonneg 2 n) (pow_nonneg (bdSpectralValue_mem n).1 _)

theorem energy_term_le_mass (k n : ℕ) :
    squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k) ≤ squarefreeMobiusMass 2 n := by
  have hX := bdSpectralValue_mem n
  have h1 : bdSpectralValue n ^ (2 * k) ≤ 1 := pow_le_one₀ hX.1 hX.2
  nlinarith [squarefreeMobiusMass_nonneg 2 n, pow_nonneg hX.1 (2 * k)]

theorem summable_energy_term (k : ℕ) :
    Summable (fun n : ℕ => squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k)) :=
  Summable.of_nonneg_of_le (energy_term_nonneg k) (energy_term_le_mass k)
    (summable_squarefreeMobiusMass (by norm_num))

theorem energy_term_le_inv_sq (k n : ℕ) :
    squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k) ≤ ((n : ℝ) ^ 2)⁻¹ :=
  le_trans (energy_term_le_mass k n) (squarefreeMobiusMass_le_inv_sq n)

theorem sum_sq_Icc_le (D : ℕ) : ∑ n ∈ Finset.Icc 1 D, (n : ℝ) ^ 2 ≤ (D : ℝ) ^ 3 := by
  induction D with
  | zero => simp
  | succ D ih =>
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · subst h0
      norm_num
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have hD : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast h0
      have hcast : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      nlinarith [ih]

/-- **The upper half of (7j).**  The feature energy is `O(k^{-1/2})`. -/
theorem bdFeatureEnergy_le {k : ℕ} (hk : 1 ≤ k) :
    bdFeatureEnergy k ≤ 5 / (2 * Real.sqrt (k : ℝ)) := by
  classical
  set D := Nat.sqrt k with hDdef
  have hD1 : 1 ≤ D := Nat.sqrt_pos.mpr hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hs0 : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hssq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk0.le
  have hDsq : D ^ 2 ≤ k := Nat.sqrt_le' k
  have hDlt : k < (D + 1) ^ 2 := Nat.lt_succ_sqrt' k
  have hDle : (D : ℝ) ≤ Real.sqrt (k : ℝ) := by
    rw [Real.le_sqrt hD0.le]
    · exact_mod_cast hDsq
    · exact hk0.le
  have hDhalf : Real.sqrt (k : ℝ) ≤ 2 * (D : ℝ) := by
    have hR : (k : ℝ) < ((D : ℝ) + 1) ^ 2 := by exact_mod_cast hDlt
    have h1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    nlinarith [Real.sqrt_nonneg (k : ℝ), hssq]
  refine (summable_energy_term k).tsum_le_of_sum_le fun s => ?_
  set M := max (s.sup id) D with hM
  have hsub : s ⊆ Finset.Icc 0 M := by
    intro n hn
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, le_trans (Finset.le_sup (f := id) hn) (le_max_left _ _)⟩
  have hDM : D ≤ M := le_max_right _ _
  have hstep1 : ∑ n ∈ s, squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k)
      ≤ ∑ n ∈ Finset.Icc 0 M, squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => energy_term_nonneg k i)
  have hzero : squarefreeMobiusMass 2 0 * bdSpectralValue 0 ^ (2 * k) = 0 := by
    rw [squarefreeMobiusMass, if_neg (by simp), zero_mul]
  have hIcc : Finset.Icc 0 M = insert 0 (Finset.Ioc 0 M) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hstep2 : ∑ n ∈ Finset.Icc 0 M, squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k)
      = ∑ n ∈ Finset.Ioc 0 M, squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k) := by
    rw [hIcc, Finset.sum_insert (by simp), hzero, zero_add]
  have hsplit := Finset.sum_Ioc_consecutive
    (fun n : ℕ => squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k))
    (Nat.zero_le D) hDM
  have hhead : ∑ n ∈ Finset.Ioc 0 D, squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k)
      ≤ 1 / (2 * Real.sqrt (k : ℝ)) := by
    have hIoc : Finset.Ioc 0 D = Finset.Icc 1 D := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIoc]
    have hterms : ∀ n ∈ Finset.Icc 1 D,
        squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k)
          ≤ (n : ℝ) ^ 2 / (2 * (k : ℝ) ^ 2) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      exact energy_term_le_head hk hn.1
    refine le_trans (Finset.sum_le_sum hterms) ?_
    rw [← Finset.sum_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsum := sum_sq_Icc_le D
    have hcube : (D : ℝ) ^ 3 ≤ Real.sqrt (k : ℝ) ^ 3 :=
      pow_le_pow_left₀ hD0.le hDle 3
    nlinarith [hsum, hcube, hssq, hs0]
  have htail : ∑ n ∈ Finset.Ioc D M, squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k)
      ≤ 2 / Real.sqrt (k : ℝ) := by
    have hIoc : Finset.Ioc D M = Finset.Icc (D + 1) M := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIoc]
    have hterms : ∀ n ∈ Finset.Icc (D + 1) M,
        squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k) ≤ 1 / (n : ℝ) ^ 2 := by
      intro n _
      rw [one_div]
      exact energy_term_le_inv_sq k n
    refine le_trans (Finset.sum_le_sum hterms) (le_trans (sum_inv_sq_tail_le hD1 M) ?_)
    rw [div_le_div_iff₀ hD0 hs0]
    linarith [hDhalf]
  have hfin : 1 / (2 * Real.sqrt (k : ℝ)) + 2 / Real.sqrt (k : ℝ)
      = 5 / (2 * Real.sqrt (k : ℝ)) := by
    field_simp
    ring
  linarith [hstep1, hstep2.le, hstep2.ge, hsplit.le, hsplit.ge, hhead, htail, hfin.le, hfin.ge]

/-! ## The lower half -/

theorem card_squarefree_Ioc_ge {A B : ℕ} (hAB : A ≤ B) :
    (B : ℝ) / 4 - (A : ℝ)
      ≤ ((((Finset.Ioc A B).filter fun d => Squarefree d).card : ℕ) : ℝ) := by
  classical
  have hunion : Finset.Ioc 0 B = Finset.Ioc 0 A ∪ Finset.Ioc A B :=
    (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le A) hAB).symm
  have hIccA : Finset.Icc 1 A = Finset.Ioc 0 A := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hIccB : Finset.Icc 1 B = Finset.Ioc 0 B := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint ((Finset.Ioc 0 A).filter fun d => Squarefree d)
      ((Finset.Ioc A B).filter fun d => Squarefree d) := by
    refine Finset.disjoint_filter_filter ?_
    rw [Finset.disjoint_left]
    intro x hx hx2
    rw [Finset.mem_Ioc] at hx hx2
    omega
  have hcard : (((Finset.Icc 1 B).filter fun d => Squarefree d).card : ℕ)
      = (((Finset.Icc 1 A).filter fun d => Squarefree d).card : ℕ)
        + (((Finset.Ioc A B).filter fun d => Squarefree d).card : ℕ) := by
    rw [hIccA, hIccB, hunion, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  have hA : (((Finset.Icc 1 A).filter fun d => Squarefree d).card : ℕ) ≤ A := by
    calc (((Finset.Icc 1 A).filter fun d => Squarefree d).card : ℕ)
        ≤ (Finset.Icc 1 A).card := Finset.card_filter_le _ _
      _ = A := by rw [Nat.card_Icc]; omega
  have hB := quarter_le_card_squarefree B
  have hcardR : ((((Finset.Icc 1 B).filter fun d => Squarefree d).card : ℕ) : ℝ)
      = ((((Finset.Icc 1 A).filter fun d => Squarefree d).card : ℕ) : ℝ)
        + ((((Finset.Ioc A B).filter fun d => Squarefree d).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hAR : ((((Finset.Icc 1 A).filter fun d => Squarefree d).card : ℕ) : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast hA
  linarith

/-- **The lower half of (7j).**  The feature energy is `≫ k^{-1/2}`. -/
theorem le_bdFeatureEnergy {k : ℕ} (hk : 7 ≤ k) :
    1 / (500 * Real.sqrt (k : ℝ)) ≤ bdFeatureEnergy k := by
  classical
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hs0 : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hssq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk0.le
  have hsge : (2.5 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    rw [show (2.5 : ℝ) = Real.sqrt (2.5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    refine Real.sqrt_le_sqrt ?_
    have : (7 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    norm_num
    linarith
  set A := Nat.sqrt (4 * k) with hA
  set B := Nat.sqrt (100 * k) with hB
  have hAB : A ≤ B := Nat.sqrt_le_sqrt (by omega)
  have hAle : (A : ℝ) ≤ 2 * Real.sqrt (k : ℝ) := by
    have h1 : A ^ 2 ≤ 4 * k := Nat.sqrt_le' (4 * k)
    have h1R : (A : ℝ) ^ 2 ≤ 4 * (k : ℝ) := by exact_mod_cast h1
    nlinarith [Nat.cast_nonneg (α := ℝ) A, hssq, hs0]
  have hBge : 10 * Real.sqrt (k : ℝ) - 1 ≤ (B : ℝ) := by
    have h1 : 100 * k < (B + 1) ^ 2 := Nat.lt_succ_sqrt' (100 * k)
    have h1R : 100 * (k : ℝ) < ((B : ℝ) + 1) ^ 2 := by exact_mod_cast h1
    nlinarith [Nat.cast_nonneg (α := ℝ) B, hssq, hs0]
  -- the finite lower sum
  set S := (Finset.Ioc A B).filter (fun d => Squarefree d) with hS
  have hcard : (0.4 : ℝ) * Real.sqrt (k : ℝ) ≤ ((S.card : ℕ) : ℝ) := by
    have h := card_squarefree_Ioc_ge hAB
    rw [← hS] at h
    linarith
  have hterm : ∀ n ∈ S, 1 / (200 * (k : ℝ))
      ≤ squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hnA, hnB⟩, hsf⟩ := hn
    have hn1 : 1 ≤ n := by
      by_contra hc
      have : n = 0 := by omega
      subst this
      exact absurd hsf (by simp)
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnsqA : 4 * k < n ^ 2 := by
      have h1 : A + 1 ≤ n := by omega
      calc 4 * k < (A + 1) ^ 2 := Nat.lt_succ_sqrt' (4 * k)
        _ ≤ n ^ 2 := Nat.pow_le_pow_left h1 2
    have hnsqB : n ^ 2 ≤ 100 * k := by
      calc n ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hnB 2
        _ ≤ 100 * k := Nat.sqrt_le' (100 * k)
    have hnsqAR : 4 * (k : ℝ) < (n : ℝ) ^ 2 := by exact_mod_cast hnsqA
    have hnsqBR : (n : ℝ) ^ 2 ≤ 100 * (k : ℝ) := by exact_mod_cast hnsqB
    have hmass : squarefreeMobiusMass 2 n = ((n : ℝ) ^ 2)⁻¹ := by
      rw [squarefreeMobiusMass, if_pos hsf,
        show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn0.le, Real.rpow_natCast]
    have hbern : 1 - 2 * (k : ℝ) * ((n : ℝ) ^ 2)⁻¹ ≤ bdSpectralValue n ^ (2 * k) := by
      have hb := one_add_mul_le_pow (a := -((n : ℝ) ^ 2)⁻¹) (by
        have : ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          nlinarith
        linarith) (2 * k)
      have hbd : (1 + -((n : ℝ) ^ 2)⁻¹) = bdSpectralValue n := by
        rw [bdSpectralValue]; ring
      rw [hbd] at hb
      have hcast : (((2 * k : ℕ)) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
      rw [hcast] at hb
      linarith
    have hhalf : (1 : ℝ) / 2 ≤ 1 - 2 * (k : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
      have hkey : 2 * (k : ℝ) * ((n : ℝ) ^ 2)⁻¹ ≤ 1 / 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        linarith
      linarith
    rw [hmass]
    have hpos : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by positivity
    have hinv : 1 / (100 * (k : ℝ)) ≤ ((n : ℝ) ^ 2)⁻¹ := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) hnsqBR
    have hXhalf : (1 : ℝ) / 2 ≤ bdSpectralValue n ^ (2 * k) := by linarith
    have hprod : (1 / (100 * (k : ℝ))) * (1 / 2)
        ≤ ((n : ℝ) ^ 2)⁻¹ * bdSpectralValue n ^ (2 * k) :=
      mul_le_mul hinv hXhalf (by norm_num) hpos.le
    have heq : (1 / (100 * (k : ℝ))) * (1 / 2) = 1 / (200 * (k : ℝ)) := by ring
    linarith
  have hsum : ∑ n ∈ S, (1 / (200 * (k : ℝ))) ≤ ∑ n ∈ S,
      squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k) := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hle : ∑ n ∈ S, squarefreeMobiusMass 2 n * bdSpectralValue n ^ (2 * k)
      ≤ bdFeatureEnergy k :=
    (summable_energy_term k).sum_le_tsum S (fun i _ => energy_term_nonneg k i)
  have hfin : 1 / (500 * Real.sqrt (k : ℝ)) ≤ ((S.card : ℕ) : ℝ) * (1 / (200 * (k : ℝ))) := by
    have hstep : (0.4 : ℝ) * Real.sqrt (k : ℝ) * (1 / (200 * (k : ℝ)))
        ≤ ((S.card : ℕ) : ℝ) * (1 / (200 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have heq : (0.4 : ℝ) * Real.sqrt (k : ℝ) * (1 / (200 * (k : ℝ)))
        = 1 / (500 * Real.sqrt (k : ℝ)) := by
      rw [eq_div_iff (by positivity)]
      field_simp
      nlinarith [hssq]
    linarith [hstep, heq.le, heq.ge]
  linarith [hsum, hle, hfin]

/-! ## The feature norm -/

/-- **Equation (7h).**  The feature energy is the normalized squared feature norm. -/
theorem norm_bdFeatureLp_sq (k : ℕ) :
    ‖bdFeatureLp k‖ ^ 2 = bdFeatureEnergy k / squarefreeMobiusTotal 2 := by
  have hZ : (0 : ℝ) < squarefreeMobiusTotal 2 := squarefreeMobiusTotal_pos (by norm_num)
  rw [HilbertSchmidt.lp_norm_sq_eq, bdFeatureEnergy, ← tsum_div_const]
  refine tsum_congr fun n => ?_
  have h := norm_bdFeature_sq k n
  have hfeat : ((bdFeatureLp k : ℕ → ℂ) n) = bdFeature k n := rfl
  rw [hfeat, h, squarefreeMobiusProbability]
  ring

/-- **Equation (7j), upper half.** -/
theorem norm_bdFeatureLp_sq_le {k : ℕ} (hk : 1 ≤ k) :
    ‖bdFeatureLp k‖ ^ 2 ≤ (5 / (2 * squarefreeMobiusTotal 2)) / Real.sqrt (k : ℝ) := by
  have hZ : (0 : ℝ) < squarefreeMobiusTotal 2 := squarefreeMobiusTotal_pos (by norm_num)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hs0 : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  rw [norm_bdFeatureLp_sq, div_le_div_iff₀ hZ hs0]
  have h := bdFeatureEnergy_le hk
  have hkey : 5 / (2 * Real.sqrt (k : ℝ)) * Real.sqrt (k : ℝ) = 5 / 2 := by
    field_simp
  have hZkey : 5 / (2 * squarefreeMobiusTotal 2) * squarefreeMobiusTotal 2 = 5 / 2 := by
    field_simp
  have hEk : bdFeatureEnergy k * Real.sqrt (k : ℝ) ≤ 5 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right h hs0.le
    rw [hkey] at hmul
    exact hmul
  linarith

/-- **Equation (7j), lower half.** -/
theorem le_norm_bdFeatureLp_sq {k : ℕ} (hk : 7 ≤ k) :
    (1 / (500 * squarefreeMobiusTotal 2)) / Real.sqrt (k : ℝ) ≤ ‖bdFeatureLp k‖ ^ 2 := by
  have hZ : (0 : ℝ) < squarefreeMobiusTotal 2 := squarefreeMobiusTotal_pos (by norm_num)
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hs0 : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  rw [norm_bdFeatureLp_sq, div_le_div_iff₀ hs0 hZ]
  have h := le_bdFeatureEnergy hk
  have hkey : 1 / (500 * Real.sqrt (k : ℝ)) * Real.sqrt (k : ℝ) = 1 / 500 := by
    field_simp
  have hZkey : 1 / (500 * squarefreeMobiusTotal 2) * squarefreeMobiusTotal 2 = 1 / 500 := by
    field_simp
  have hEk : (1 : ℝ) / 500 ≤ bdFeatureEnergy k * Real.sqrt (k : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right h hs0.le
    rw [hkey] at hmul
    exact hmul
  linarith

end

end RHTower
