import GaloisForLFunctions.RHTower.LiCriterion

/-!
# Li coefficients are never eventually negative

The hard half of Li's criterion shows that a zero off the critical line makes some paired Li
coefficient `2λ_n = Σ_ρ m_ρ (2 − w_ρⁿ − w_ρ⁻ⁿ)` negative.  This module proves the complementary
oscillation: off the line the coefficients are also positive for arbitrarily large `n`, so the
sequence of signs never stabilises.

The mechanism is a mean-value argument on the dominant zeros.  Among the finitely many zeros whose
Cayley representatives `v_ρ` (normalised to modulus at least one) exceed a fixed threshold, take
those of maximal modulus `R`; their unimodular directions `u_ρ` are non-real.  Simultaneous
recurrence gives `n₀` with every `u_ρ^{n₀}` close to `1`, and the geometric sum
`Σ_{k=1}^{n₀} u^k = u (u^{n₀} − 1)/(u − 1)` is then small, so the weighted cosine sum
`Σ m_ρ Re(u_ρ^k)` is negative for some `k₀ < n₀`.  At exponents `n + k₀` with `n` a recurrence
time, the dominant part of `−Σ m_ρ Re(v_ρ^{n+k₀})` is `R^{n+k₀}` times a positive constant, and the
remaining zeros contribute at most a smaller exponential rate; so `2λ_{n+k₀} > 0`.

Consequently, unconditionally, the paired Li coefficients are never eventually negative: there is
no archimedean analogue of a hypothesis forcing every coefficient of a sequence into a sign
class, which is the shape a Ferrero–Washington-type argument would need.
-/

open Complex Finset

namespace RHTower

/-- Simultaneous recurrence at arbitrarily large exponents. -/
theorem exists_ge_pow_sub_one_lt {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∀ i, ‖u i ^ n - 1‖ < ε := by
  obtain ⟨m, hm, hlt⟩ := exists_pos_pow_sub_one_lt (fun i => u i ^ (N + 1))
    (by intro i; rw [norm_pow, hu i, one_pow]) hε
  refine ⟨(N + 1) * m, by nlinarith, by positivity, fun i => ?_⟩
  rw [pow_mul]
  exact hlt i

/-- **Mean value on the torus.**  A positive combination of non-trivial unimodular characters
`k ↦ Re(u_i^k)` is negative for some positive `k`. -/
theorem exists_re_sum_pow_neg {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℂ) (m : ι → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hu1 : ∀ i, u i ≠ 1) (hm : ∀ i, 0 < m i) :
    ∃ k : ℕ, 0 < k ∧ ∑ i, m i * (u i ^ k).re < 0 := by
  classical
  set A : ℝ := ∑ i, m i with hA
  have hA0 : 0 < A := Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  set B : ℝ := ∑ i, m i / ‖u i - 1‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => div_nonneg (hm i).le (norm_nonneg _)
  obtain ⟨δ, hδ0, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ ‖u i - 1‖ := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun i => ‖u i - 1‖), ?_,
      fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => ‖u i - 1‖)
    rw [hj]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (hu1 j))
  set ε : ℝ := min (δ / 2) (A / (2 * (A + B))) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεAB : ε * (A + B) ≤ A / 2 := by
    have h := min_le_right (δ / 2) (A / (2 * (A + B)))
    have hAB : 0 < A + B := by linarith
    calc ε * (A + B) ≤ A / (2 * (A + B)) * (A + B) :=
          mul_le_mul_of_nonneg_right h hAB.le
      _ = A / 2 := by field_simp
  obtain ⟨n₀, hn₀, hclose⟩ := exists_pos_pow_sub_one_lt u hu hε0
  have hn₀2 : 2 ≤ n₀ := by
    by_contra h
    have h1 : n₀ = 1 := by omega
    have h2 := hclose (Classical.arbitrary ι)
    rw [h1, pow_one] at h2
    linarith [hδle (Classical.arbitrary ι)]
  by_contra hcon
  push Not at hcon
  have hgeom : ∀ i, ∑ k ∈ Finset.Ico 1 (n₀ + 1), u i ^ k
      = u i * ((u i ^ n₀ - 1) / (u i - 1)) := by
    intro i
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    rw [show ∑ k ∈ Finset.range n₀, u i ^ (1 + k) = u i * ∑ k ∈ Finset.range n₀, u i ^ k by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add, pow_one]]
    rw [geom_sum_eq (hu1 i) n₀]
  have hbound : ∑ k ∈ Finset.Ico 1 (n₀ + 1), ∑ i, m i * (u i ^ k).re ≤ ε * B := by
    rw [Finset.sum_comm]
    calc ∑ i, ∑ k ∈ Finset.Ico 1 (n₀ + 1), m i * (u i ^ k).re
        = ∑ i, m i * (∑ k ∈ Finset.Ico 1 (n₀ + 1), u i ^ k).re := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.re_sum, Finset.mul_sum]
      _ ≤ ∑ i, m i * (ε / ‖u i - 1‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hm i).le
          rw [hgeom i]
          calc (u i * ((u i ^ n₀ - 1) / (u i - 1))).re
              ≤ ‖u i * ((u i ^ n₀ - 1) / (u i - 1))‖ := Complex.re_le_norm _
            _ = ‖u i ^ n₀ - 1‖ / ‖u i - 1‖ := by rw [norm_mul, hu i, one_mul, norm_div]
            _ ≤ ε / ‖u i - 1‖ := div_le_div_of_nonneg_right (hclose i).le (norm_nonneg _)
      _ = ε * B := by
          rw [hB, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
  have hlast : A * (1 - ε) ≤ ∑ i, m i * (u i ^ n₀).re := by
    rw [hA, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hm i).le
    have h1 : (1 - u i ^ n₀).re ≤ ‖1 - u i ^ n₀‖ := Complex.re_le_norm _
    rw [Complex.sub_re, Complex.one_re, norm_sub_rev] at h1
    linarith [hclose i]
  have hsplit : ∑ k ∈ Finset.Ico 1 (n₀ + 1), ∑ i, m i * (u i ^ k).re
      = ∑ k ∈ Finset.Ico 1 n₀, ∑ i, m i * (u i ^ k).re + ∑ i, m i * (u i ^ n₀).re :=
    Finset.sum_Ico_succ_top (by omega) _
  have hnonneg : 0 ≤ ∑ k ∈ Finset.Ico 1 n₀, ∑ i, m i * (u i ^ k).re :=
    Finset.sum_nonneg fun k hk => hcon k (by rw [Finset.mem_Ico] at hk; omega)
  have hfinal : A * (1 - ε) ≤ ε * B := by linarith
  nlinarith

/-- `bⁿ (a/b)ⁿ = aⁿ` for `b ≠ 0`. -/
theorem pow_mul_div_pow_cancel {a b : ℝ} (hb : b ≠ 0) (n : ℕ) : b ^ n * (a / b) ^ n = a ^ n := by
  rw [div_pow]
  field_simp

variable {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}

/-- **Positivity at arbitrarily large exponents, abstract form.**  If one member of a non-real
family lies strictly outside the unit circle, the paired Li sums are positive for arbitrarily
large `n`. -/
theorem exists_ge_re_tsum_liTerm_pos
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) (hnr : ∀ i, (v i).im ≠ 0)
    {i₀ : ι} (hlt : 1 < ‖v i₀‖) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < ∑' i, m i * (liTerm (v i) n).re := by
  classical
  have hm0 : ∀ i, (0:ℝ) ≤ m i := fun i => by linarith [hm i]
  have hvne : ∀ i, v i ≠ 0 := by
    intro i h
    have h1 := hv i
    rw [h] at h1
    simp at h1
    linarith
  have hvpos : ∀ i, (0:ℝ) < ‖v i‖ := fun i => lt_of_lt_of_le zero_lt_one (hv i)
  set W : ℝ := ‖v i₀‖ with hWdef
  set q : ℝ := (1 + W) / 2 with hqdef
  clear_value W q
  have hq1 : 1 < q := by rw [hqdef]; linarith
  have hqW : q < W := by rw [hqdef]; linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hFfin : {i | q ≤ ‖v i‖}.Finite := finite_far_set hm hs hq1
  set S : Finset ι := hFfin.toFinset with hSdef
  have hmemS : ∀ i, i ∈ S ↔ q ≤ ‖v i‖ := by
    intro i
    rw [hSdef, Set.Finite.mem_toFinset]
    rfl
  have hi₀S : i₀ ∈ S := (hmemS i₀).mpr (by rw [hWdef] at hqW; exact le_of_lt hqW)
  have hSne : S.Nonempty := ⟨i₀, hi₀S⟩
  -- the dominant modulus
  set R : ℝ := S.sup' hSne (fun i => ‖v i‖) with hRdef
  have hRle : ∀ i ∈ S, ‖v i‖ ≤ R := fun i hi => Finset.le_sup' (fun i => ‖v i‖) hi
  have hWR : W ≤ R := by rw [hWdef]; exact hRle i₀ hi₀S
  have hqR : q < R := lt_of_lt_of_le hqW hWR
  have hR0 : (0:ℝ) < R := by linarith
  have hR1 : (1:ℝ) < R := by linarith
  set D : Finset ι := S.filter (fun i => ‖v i‖ = R) with hDdef
  set E : Finset ι := S.filter (fun i => ¬ ‖v i‖ = R) with hEdef
  have hDne : D.Nonempty := by
    obtain ⟨j, hjS, hj⟩ := Finset.exists_mem_eq_sup' hSne (fun i => ‖v i‖)
    exact ⟨j, Finset.mem_filter.mpr ⟨hjS, hj.symm⟩⟩
  have hDnorm : ∀ i ∈ D, ‖v i‖ = R := fun i hi => (Finset.mem_filter.mp hi).2
  have hElt : ∀ i ∈ E, ‖v i‖ < R := fun i hi =>
    lt_of_le_of_ne (hRle i (Finset.mem_filter.mp hi).1) (Finset.mem_filter.mp hi).2
  -- unimodular directions
  set u : ι → ℂ := fun i => v i / (‖v i‖ : ℂ) with hudef
  have hunit : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hudef]
    simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hvpos i),
      div_self (ne_of_gt (hvpos i))]
  have hfac : ∀ i, v i = (‖v i‖ : ℂ) * u i := by
    intro i
    rw [hudef]
    simp only
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt (hvpos i))]
  have huim : ∀ i, (u i).im ≠ 0 := by
    intro i h
    apply hnr i
    have := hfac i
    rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, h]
    ring
  have hu1 : ∀ i, u i ≠ 1 := by
    intro i h
    apply huim i
    rw [h]
    rfl
  -- the mean-value exponent on the dominant set
  haveI : Nonempty {x // x ∈ D} := ⟨⟨hDne.choose, hDne.choose_spec⟩⟩
  obtain ⟨k₀, hk₀, hT⟩ := exists_re_sum_pow_neg (fun i : {x // x ∈ D} => u i)
    (fun i : {x // x ∈ D} => m i) (fun i => hunit i) (fun i => hu1 i) (fun i => by linarith [hm i])
  set T₀ : ℝ := ∑ i : {x // x ∈ D}, m i * (u i ^ k₀).re with hT₀def
  set mD : ℝ := ∑ i ∈ D, m i with hmDdef
  clear_value T₀ mD
  have hmD0 : 0 < mD := by
    rw [hmDdef]
    exact Finset.sum_pos (fun i _ => by linarith [hm i]) hDne
  set ε : ℝ := -T₀ / (2 * mD) with hεdef
  set c₀ : ℝ := -T₀ / 2 with hc₀def
  clear_value ε c₀
  have hε0 : 0 < ε := by rw [hεdef]; exact div_pos (by linarith) (by positivity)
  have hc₀ : 0 < c₀ := by rw [hc₀def]; linarith
  -- the error terms tend to zero relative to `R^n`
  set C : ℝ := ∑' i, m i * ‖v i - 1‖ ^ (2 : ℕ) with hCdef
  clear_value C
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact tsum_nonneg fun i => by nlinarith [hm0 i, sq_nonneg ‖v i - 1‖]
  have hlimE : Filter.Tendsto (fun n : ℕ => ∑ i ∈ E, m i * (‖v i‖ / R) ^ n)
      Filter.atTop (nhds 0) := by
    have h0 : (0:ℝ) = ∑ i ∈ E, m i * 0 := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun i hi => ?_
    have hr0 : 0 ≤ ‖v i‖ / R := by positivity
    have hr1 : ‖v i‖ / R < 1 := by rw [div_lt_one hR0]; exact hElt i hi
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul _
  have hlimT : Filter.Tendsto (fun n : ℕ => C * ((n : ℝ) ^ (2 : ℕ) * (q / R) ^ n))
      Filter.atTop (nhds 0) := by
    have hr0 : 0 ≤ q / R := by positivity
    have hr1 : q / R < 1 := by rw [div_lt_one hR0]; exact hqR
    have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (2 : ℕ) * (q / R) ^ n) := by
      refine summable_pow_mul_geometric_of_norm_lt_one 2 ?_
      rw [Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1
    simpa using hsum.tendsto_atTop_zero.const_mul C
  have hlim : Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ E, m i * (‖v i‖ / R) ^ n + C * ((n : ℝ) ^ (2 : ℕ) * (q / R) ^ n))
      Filter.atTop (nhds 0) := by simpa using hlimE.add hlimT
  obtain ⟨N₁, hN₁⟩ := (hlim.eventually (gt_mem_nhds hc₀)).exists_forall_of_atTop
  -- recurrence time
  obtain ⟨n, hnN, hnpos, hnrec⟩ :=
    exists_ge_pow_sub_one_lt (fun i : {x // x ∈ S} => u i) (fun i => hunit i) hε0 (max N N₁)
  refine ⟨n + k₀, by omega, ?_⟩
  set n' : ℕ := n + k₀ with hn'def
  clear_value n'
  have hn'N₁ : N₁ ≤ n' := by omega
  have hsmall := hN₁ n' hn'N₁
  -- the split
  have hsummable := summable_re_liTerm_of_one_le hm0 hv hM hs n'
  have hsplit := hsummable.sum_add_tsum_compl (s := S)
  -- tail bound (as in the hard half)
  have hBsum : Summable fun i : {x // x ∈ (↑S : Set ι)ᶜ} =>
      (n' : ℝ) ^ (2 : ℕ) * q ^ n' * (m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) :=
    (hs.subtype _).mul_left _
  have hBle : ∀ i : {x // x ∈ (↑S : Set ι)ᶜ},
      -((n' : ℝ) ^ (2 : ℕ) * q ^ n' * (m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)))
        ≤ m (i : ι) * (liTerm (v (i : ι)) n').re := by
    rintro ⟨i, hi⟩
    have hiS : ¬ (q ≤ ‖v i‖) := by
      intro h
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hi
      exact hi ((hmemS i).mpr h)
    have hlt' : ‖v i‖ < q := lt_of_not_ge hiS
    have hmax : max ‖v i‖ ‖v i‖⁻¹ = ‖v i‖ := by
      refine max_eq_left ?_
      rw [inv_le_iff_one_le_mul₀ (hvpos i)]
      nlinarith [hv i]
    have hbase := norm_liTerm_le (hvne i) n'
    rw [hmax] at hbase
    have hpow : ‖v i‖ ^ n' ≤ q ^ n' := pow_le_pow_left₀ (norm_nonneg _) hlt'.le n'
    have hre : -‖liTerm (v i) n'‖ ≤ (liTerm (v i) n').re :=
      neg_le_of_abs_le (Complex.abs_re_le_norm _)
    have hchain : ‖liTerm (v i) n'‖ ≤ (n' : ℝ) ^ (2 : ℕ) * q ^ n' * ‖v i - 1‖ ^ (2 : ℕ) := by
      refine le_trans hbase ?_
      have h2 : (0:ℝ) ≤ ‖v i - 1‖ ^ (2 : ℕ) := sq_nonneg _
      have h3 : (0:ℝ) ≤ (n' : ℝ) ^ (2 : ℕ) := sq_nonneg _
      rw [mul_assoc, mul_assoc]
      gcongr
    have hmi := hm0 i
    calc -((n' : ℝ) ^ (2 : ℕ) * q ^ n' * (m i * ‖v i - 1‖ ^ (2 : ℕ)))
        = m i * (-((n' : ℝ) ^ (2 : ℕ) * q ^ n' * ‖v i - 1‖ ^ (2 : ℕ))) := by ring
      _ ≤ m i * (-‖liTerm (v i) n'‖) := by
          apply mul_le_mul_of_nonneg_left _ hmi
          linarith
      _ ≤ m i * (liTerm (v i) n').re := mul_le_mul_of_nonneg_left hre hmi
  have htailC : (∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) ≤ C := by
    have hsp := hs.sum_add_tsum_compl (s := S)
    have hSnn : (0:ℝ) ≤ ∑ i ∈ S, m i * ‖v i - 1‖ ^ (2 : ℕ) :=
      Finset.sum_nonneg fun i _ => by nlinarith [hm0 i, sq_nonneg ‖v i - 1‖]
    rw [hCdef, ← hsp]
    linarith
  have htail : -((n' : ℝ) ^ (2 : ℕ) * q ^ n' * C)
      ≤ ∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * (liTerm (v (i : ι)) n').re := by
    have h1 := Summable.tsum_le_tsum hBle hBsum.neg (hsummable.subtype ((↑S : Set ι)ᶜ))
    rw [tsum_neg, Summable.tsum_mul_left] at h1
    · have hcoef : (0:ℝ) ≤ (n' : ℝ) ^ (2 : ℕ) * q ^ n' := by positivity
      have := mul_le_mul_of_nonneg_left htailC hcoef
      linarith
    · exact hs.subtype _
  -- the finite part: split into `D` and `E`
  have hSDE : ∑ i ∈ S, m i * (liTerm (v i) n').re
      = ∑ i ∈ D, m i * (liTerm (v i) n').re + ∑ i ∈ E, m i * (liTerm (v i) n').re := by
    rw [hDdef, hEdef]
    exact (Finset.sum_filter_add_sum_filter_not S _ _).symm
  -- generic lower bound for one term: `Re liTerm ≥ -Re(vⁿ)`
  have hterm : ∀ i, -(v i ^ n').re ≤ (liTerm (v i) n').re := by
    intro i
    have hinv : ((v i)⁻¹ ^ n').re ≤ 1 := by
      have h2 : ‖(v i)⁻¹ ^ n'‖ ≤ 1 := by
        rw [norm_pow, norm_inv]
        refine pow_le_one₀ (by positivity) ?_
        rw [inv_le_one₀ (hvpos i)]
        exact hv i
      exact le_trans (Complex.re_le_norm _) h2
    have hlire : (liTerm (v i) n').re = 2 - (v i ^ n').re - ((v i)⁻¹ ^ n').re := by
      rw [liTerm]
      simp
    rw [hlire]
    linarith
  -- `E` part
  have hEbound : -(∑ i ∈ E, m i * ‖v i‖ ^ n') ≤ ∑ i ∈ E, m i * (liTerm (v i) n').re := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : (v i ^ n').re ≤ ‖v i‖ ^ n' := by
      rw [← norm_pow]
      exact Complex.re_le_norm _
    calc -(m i * ‖v i‖ ^ n') = m i * (-‖v i‖ ^ n') := by ring
      _ ≤ m i * (-(v i ^ n').re) := mul_le_mul_of_nonneg_left (by linarith) (hm0 i)
      _ ≤ m i * (liTerm (v i) n').re := mul_le_mul_of_nonneg_left (hterm i) (hm0 i)
  -- `D` part: the dominant estimate
  have hDbound : R ^ n' * c₀ ≤ ∑ i ∈ D, m i * (liTerm (v i) n').re := by
    have hstep : ∀ i ∈ D, -(R ^ n' * (m i * ((u i ^ k₀).re + ε)))
        ≤ m i * (liTerm (v i) n').re := by
      intro i hi
      have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
      have hrec := hnrec ⟨i, hiS⟩
      have hvi : v i ^ n' = (R : ℂ) ^ n' * (u i ^ n * u i ^ k₀) := by
        rw [hfac i, hDnorm i hi, mul_pow, hn'def]
        ring
      have hre : (u i ^ n * u i ^ k₀).re ≤ (u i ^ k₀).re + ε := by
        have h1 : u i ^ n * u i ^ k₀ - u i ^ k₀ = (u i ^ n - 1) * u i ^ k₀ := by ring
        have h2 : ‖u i ^ n * u i ^ k₀ - u i ^ k₀‖ < ε := by
          rw [h1, norm_mul, norm_pow, hunit i, one_pow, mul_one]
          exact hrec
        have h3 : (u i ^ n * u i ^ k₀ - u i ^ k₀).re ≤ ‖u i ^ n * u i ^ k₀ - u i ^ k₀‖ :=
          Complex.re_le_norm _
        rw [Complex.sub_re] at h3
        linarith
      have hRpow : ((R : ℂ) ^ n').re = R ^ n' := by
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
      have hvre : (v i ^ n').re = R ^ n' * (u i ^ n * u i ^ k₀).re := by
        rw [hvi, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
      have hRn : (0:ℝ) ≤ R ^ n' := pow_nonneg hR0.le _
      calc -(R ^ n' * (m i * ((u i ^ k₀).re + ε)))
          ≤ -(m i * (v i ^ n').re) := by
            rw [hvre]
            have := mul_le_mul_of_nonneg_left hre (mul_nonneg hRn (hm0 i))
            nlinarith [this]
        _ = m i * (-(v i ^ n').re) := by ring
        _ ≤ m i * (liTerm (v i) n').re := mul_le_mul_of_nonneg_left (hterm i) (hm0 i)
    have hsumD : ∑ i ∈ D, m i * ((u i ^ k₀).re + ε) = T₀ + ε * mD := by
      rw [hT₀def, hmDdef, Finset.mul_sum, Finset.sum_coe_sort D (fun i => m i * (u i ^ k₀).re),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hc₀eq : c₀ = -(T₀ + ε * mD) := by
      rw [hc₀def, hεdef]
      field_simp
      ring
    calc R ^ n' * c₀ = -(R ^ n' * ∑ i ∈ D, m i * ((u i ^ k₀).re + ε)) := by
          rw [hsumD, hc₀eq]
          ring
      _ = ∑ i ∈ D, -(R ^ n' * (m i * ((u i ^ k₀).re + ε))) := by
          rw [Finset.mul_sum, Finset.sum_neg_distrib]
      _ ≤ ∑ i ∈ D, m i * (liTerm (v i) n').re := Finset.sum_le_sum hstep
  -- assemble
  have hEpow : ∑ i ∈ E, m i * ‖v i‖ ^ n' = R ^ n' * ∑ i ∈ E, m i * (‖v i‖ / R) ^ n' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul_div_pow_cancel (a := ‖v i‖) hR0.ne' n']
    ring
  have hqpow : (n' : ℝ) ^ (2 : ℕ) * q ^ n' * C = R ^ n' * (C * ((n' : ℝ) ^ (2 : ℕ) * (q / R) ^ n')) := by
    rw [← pow_mul_div_pow_cancel (a := q) hR0.ne' n']
    ring
  have hRn : (0:ℝ) < R ^ n' := pow_pos hR0 _
  rw [← hsplit, hSDE]
  have hgap : ∑ i ∈ E, m i * (‖v i‖ / R) ^ n' + C * ((n' : ℝ) ^ (2 : ℕ) * (q / R) ^ n') < c₀ := hsmall
  have hkey : 0 < R ^ n' * c₀ - ∑ i ∈ E, m i * ‖v i‖ ^ n' - (n' : ℝ) ^ (2 : ℕ) * q ^ n' * C := by
    rw [hEpow, hqpow]
    nlinarith [hRn, hgap]
  linarith [hDbound, hEbound, htail]

/-! ### The Xi divisor -/

/-- **Off the line, the paired Li coefficients are positive for arbitrarily large `n`.** -/
theorem exists_ge_re_xiLiPaired_pos_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis)
    (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ 0 < (xiLiPaired n).re := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half] at hRH
  push Not at hRH
  obtain ⟨ρ₁, hρ₁zero, hρ₁re⟩ := hRH
  set ρ₀ : XiDivisorSupport := ⟨ρ₁, mem_xi_divisor_support_of_eq_zero hρ₁zero⟩ with hρ₀def
  obtain ⟨M, hM1, hMb⟩ := exists_bound_xiRootW
  have hne0 : ∀ ρ : XiDivisorSupport, (ρ : ℂ) ≠ 0 := by
    intro ρ h
    have him := xi_divisor_support_im_ne_zero ρ
    rw [h] at him
    simp at him
  have hne1 : ∀ ρ : XiDivisorSupport, (ρ : ℂ) ≠ 1 := by
    intro ρ h
    have him := xi_divisor_support_im_ne_zero ρ
    rw [h] at him
    simp at him
  have hmult : ∀ ρ : XiDivisorSupport,
      (1 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    intro ρ
    have := xi_divisor_pos_on_support ρ
    exact_mod_cast this
  have hvnorm : ∀ ρ : XiDivisorSupport, 1 ≤ ‖xiRootV (ρ : ℂ)‖ :=
    fun ρ => one_le_norm_xiRootV (hne0 ρ) (hne1 ρ)
  have hvM : ∀ ρ : XiDivisorSupport, ‖xiRootV (ρ : ℂ)‖ ≤ M := by
    intro ρ
    rw [norm_xiRootV (hne0 ρ) (hne1 ρ)]
    exact hMb ρ
  have hsum : Summable fun ρ : XiDivisorSupport =>
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ) := by
    refine Summable.of_nonneg_of_le (fun ρ => by nlinarith [hmult ρ, sq_nonneg ‖xiRootV (ρ:ℂ) - 1‖])
      (fun ρ => ?_) (xi_zero_multiplicity_inv_sq_summable.mul_left (M ^ (2 : ℕ)))
    have hb := norm_xiRootV_sub_one_le (hne0 ρ) (hne1 ρ) hM1 (hMb ρ)
    have hw1 : ‖xiRootW (ρ : ℂ) - 1‖ = 1 / ‖(ρ : ℂ)‖ := norm_xiRootW_sub_one _
    rw [hw1] at hb
    have hnn : (0 : ℝ) ≤ ‖xiRootV (ρ : ℂ) - 1‖ := norm_nonneg _
    have hsq : ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by
      have hM0 : (0 : ℝ) ≤ M := by linarith
      have hmul : (M * (1 / ‖(ρ : ℂ)‖)) ^ (2 : ℕ) = M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by
        rw [mul_pow, div_pow, one_pow]
      rw [← hmul]
      nlinarith [mul_nonneg hM0 (by positivity : (0:ℝ) ≤ 1 / ‖(ρ : ℂ)‖)]
    calc ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ)
        ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ))) := by
          have := hmult ρ
          nlinarith
      _ = M ^ (2 : ℕ) * (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by
          ring
  have hnr : ∀ ρ : XiDivisorSupport, (xiRootV (ρ : ℂ)).im ≠ 0 := by
    intro ρ h
    have hw : (xiRootW (ρ : ℂ)).im ≠ 0 := by
      intro hw
      exact xi_divisor_support_im_ne_zero ρ (im_eq_zero_of_xiRootW_im_eq_zero (hne0 ρ) hw)
    apply hw
    unfold xiRootV at h
    split_ifs at h with hcase
    · exact h
    · rw [Complex.inv_im] at h
      have hn0 : Complex.normSq (xiRootW (ρ : ℂ)) ≠ 0 := by
        rw [Ne, Complex.normSq_eq_zero]
        exact xiRootW_ne_zero (hne0 ρ) (hne1 ρ)
      rcases div_eq_zero_iff.mp h with h1 | h1
      · exact neg_eq_zero.mp h1
      · exact absurd h1 hn0
  have hbad : 1 < ‖xiRootV ((ρ₀ : XiDivisorSupport) : ℂ)‖ := by
    have hnorm : ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ ≠ 1 := by
      intro hEq
      exact hρ₁re ((norm_xiRootW_eq_one_iff (hne0 ρ₀)).mp hEq)
    have hposw : 0 < ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ :=
      norm_pos_iff.mpr (xiRootW_ne_zero (hne0 ρ₀) (hne1 ρ₀))
    rw [norm_xiRootV (hne0 ρ₀) (hne1 ρ₀)]
    rcases lt_trichotomy ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ 1 with hlt | heq | hgt
    · refine lt_of_lt_of_le ?_ (le_max_right _ _)
      rw [one_lt_inv₀ hposw]
      exact hlt
    · exact absurd heq hnorm
    · exact lt_of_lt_of_le hgt (le_max_left _ _)
  obtain ⟨n, hnN, hn⟩ := exists_ge_re_tsum_liTerm_pos hmult hvnorm hvM hsum hnr hbad N
  refine ⟨n, hnN, ?_⟩
  have hre : (xiLiPaired n).re
      = ∑' ρ : XiDivisorSupport,
          ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (liTerm (xiRootV (ρ : ℂ)) n).re := by
    rw [xiLiPaired, Complex.re_tsum (summable_xiLiPairedTerm n)]
    refine tsum_congr fun ρ => ?_
    rw [xiLiPairedTerm, Complex.re_ofReal_mul, liTerm_xiRootV]
  rw [hre]
  exact hn

/-- **The paired Li coefficients are never eventually negative.**  Under RH they are all
nonnegative; off the line they are positive for arbitrarily large `n`. -/
theorem not_eventually_re_xiLiPaired_neg :
    ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (xiLiPaired n).re < 0 := by
  rintro ⟨N, hN⟩
  by_cases hRH : RiemannHypothesis
  · exact absurd (hN N le_rfl) (not_lt.mpr (re_xiLiPaired_nonneg_of_rh hRH N))
  · obtain ⟨n, hn, hpos⟩ := exists_ge_re_xiLiPaired_pos_of_not_riemannHypothesis hRH N
    exact absurd (hN n hn) (not_lt.mpr hpos.le)

end RHTower
