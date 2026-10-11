import GaloisForLFunctions.RHTower.LiSignProgressionsSharp

/-!
# Li's criterion along a set of indices is Bohr recurrence

For `A ⊆ ℕ` say that Li thinning holds along `A` (`LiThinning A`) if, for every abstract Li family
`(v_i, m_i)` (`|v_i| ≥ 1`, `m_i ≥ 1`, `Σ m_i|v_i − 1|² < ∞`) with a member off the unit circle, the
paired Li sums `Σ m_i Re(1 − (1 − 1/ρ)ⁿ)`, written `Σ m_i Re liTerm(v_i, n)`, are negative for infinitely
many `n ∈ A`. Say that `A` is a set of Bohr recurrence (`IsBohrRecurrent A`) if for every finite family
of rotations `φ_1, …, φ_k` and every `η > 0` there are arbitrarily large `n ∈ A` with every `nφ_i`
within `η` of `2πℤ`.

**Theorem** (`liThinning_iff_isBohrRecurrent`). `LiThinning A ↔ IsBohrRecurrent A`.

* (⟸) The dominant layer `|v| = R` is finite. At a recurrence time every `Re((v/R)ⁿ) ≥ ½`, so the
  dominant part `−Rⁿ Σ m Re((v/R)ⁿ)` is negative of size `Rⁿ`.
* (⟹) If `A` is not recurrent for `(φ, η)`, take `Q(y) = Π_i |Σ_{j≤M} e^{ijy_i}|^{2k}`. It is a sum of
  characters `e^{i⟨h, y⟩}` with unit coefficients. Its constant term is at least
  `((M+1)^{2k}/(kM+1))^k` (Cauchy–Schwarz on the sums of `k`-tuples). Off the Bohr box one factor is at
  most `1/sin²(η/2)` (geometric sum). For large `M`, `Q(nφ)` is below the constant term at every
  non-recurrent `n`. The nonconstant characters then form a conjugation-closed Li family
  `2e^{i⟨h, φ⟩}` whose paired Li sums are positive along `A`.

So Li's criterion, thinned to an index set, is complete for all abstract zero configurations exactly
along sets of Bohr recurrence: the intersective polynomial images (`LiSignIntersective`) and the squares
are examples, nonzero residue classes are not.

**For `ξ`** (`exists_bohr_neighbourhood_re_xiLiPaired_neg`,
`riemannHypothesis_iff_eventually_re_xiLiPaired_of_isBohrRecurrent`). If the Riemann hypothesis fails,
the set of `n` with `Re 2λ_n < 0` contains a Bohr neighbourhood of `0` minus finitely many indices. Hence
the Riemann hypothesis holds iff `Re 2λ_n ≥ 0` for all large `n` in any set of Bohr recurrence.
-/

open Complex Filter Finset

noncomputable section

namespace RHTower

/-! ## Definitions -/

/-- `A ⊆ ℕ` is a set of Bohr recurrence. -/
def IsBohrRecurrent (A : Set ℕ) : Prop :=
  ∀ (k : ℕ) (φ : Fin k → ℝ) (η : ℝ), 0 < η → ∀ N : ℕ,
    ∃ n ∈ A, N ≤ n ∧ ∀ i, ∃ z : ℤ, |(n : ℝ) * φ i - z * (2 * Real.pi)| < η

/-- Li thinning along `A`: every abstract Li family with a member off the unit circle has negative
paired Li sums at infinitely many indices of `A`. -/
def LiThinning (A : Set ℕ) : Prop :=
  ∀ (ι : Type) (v : ι → ℂ) (m : ι → ℝ) (M : ℝ), (∀ i, 1 ≤ m i) → (∀ i, 1 ≤ ‖v i‖) →
    (∀ i, ‖v i‖ ≤ M) → Summable (fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) → (∃ i₀, 1 < ‖v i₀‖) →
    ∃ᶠ n in atTop, n ∈ A ∧ ∑' i, m i * (liTerm (v i) n).re < 0

/-! ## Recurrence gives Li thinning -/

theorem half_le_cos_of_abs_le {y : ℝ} (hy : |y| ≤ Real.pi / 3) : 1 / 2 ≤ Real.cos y := by
  rw [← Real.cos_abs, ← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) (by linarith [Real.pi_pos]) hy

/-- **The failure set contains a Bohr neighbourhood of `0`.** For an abstract Li family with a member
off the unit circle there are finitely many angles `φ_i` and an index `N₀` such that every `n ≥ N₀`
with all `nφ_i` within `π/3` of `2πℤ` has negative paired Li sum. -/
theorem exists_bohr_neighbourhood_re_tsum_liTerm_neg {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ (k : ℕ) (φ : Fin k → ℝ) (N₀ : ℕ), ∀ n : ℕ, N₀ ≤ n →
      (∀ i, ∃ z : ℤ, |(n : ℝ) * φ i - z * (2 * Real.pi)| < Real.pi / 3) →
      ∑' i, m i * (liTerm (v i) n).re < 0 := by
  classical
  obtain ⟨D, R, hDne, hR1, hDnorm, hdec⟩ := abs_re_tsum_liTerm_add_dominant_le hm hv hM hs hlt
  have hR0 : (0 : ℝ) < R := by linarith
  obtain ⟨N₁, hN₁⟩ := hdec (1 / 4) (by norm_num)
  set e := D.equivFin with he
  set φ : Fin D.card → ℝ := fun i => Complex.arg (v (e.symm i) / R) with hφ
  refine ⟨D.card, φ, N₁, fun n hnN hrec => ?_⟩
  have hhalf : ∀ x ∈ D, (1 : ℝ) / 2 ≤ ((v x / R) ^ n).re := by
    intro x hx
    have hu : ‖v x / R‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, (hDnorm x).mp hx,
        div_self hR0.ne']
    obtain ⟨z, hz⟩ := hrec (e ⟨x, hx⟩)
    have hφx : φ (e ⟨x, hx⟩) = Complex.arg (v x / R) := by simp [hφ]
    rw [hφx] at hz
    rw [eq_exp_arg_mul_I_of_norm_eq_one hu, ← Complex.exp_nat_mul]
    have e1 : (n : ℂ) * ((Complex.arg (v x / R) : ℂ) * I) =
        (((n : ℝ) * Complex.arg (v x / R) : ℝ) : ℂ) * I := by push_cast; ring
    rw [e1, Complex.exp_ofReal_mul_I_re]
    have e2 : (n : ℝ) * Complex.arg (v x / R) =
        ((n : ℝ) * Complex.arg (v x / R) - z * (2 * Real.pi)) + ((z : ℤ) : ℝ) * (2 * Real.pi) := by
      ring
    rw [e2, Real.cos_add_int_mul_two_pi]
    exact half_le_cos_of_abs_le hz.le
  have hsum : (1 : ℝ) / 2 ≤ ∑ x ∈ D, m x * ((v x / R) ^ n).re := by
    obtain ⟨x₀, hx₀⟩ := hDne
    calc (1 : ℝ) / 2 ≤ m x₀ * ((v x₀ / R) ^ n).re := by
          have := hhalf x₀ hx₀; have := hm x₀; nlinarith
      _ ≤ ∑ x ∈ D, m x * ((v x / R) ^ n).re :=
          Finset.single_le_sum (f := fun x => m x * ((v x / R) ^ n).re)
            (fun x hx => mul_nonneg (by linarith [hm x]) (by linarith [hhalf x hx])) hx₀
  have hd := hN₁ n hnN
  have hRn : (0 : ℝ) < R ^ n := pow_pos hR0 n
  have h2 := (abs_le.mp hd).2
  nlinarith

/-- **Bohr recurrence gives Li thinning.** -/
theorem liThinning_of_isBohrRecurrent {A : Set ℕ} (hA : IsBohrRecurrent A) : LiThinning A := by
  intro ι v m M hm hv hM hs ⟨i₀, hlt⟩
  obtain ⟨k, φ, N₀, hneg⟩ := exists_bohr_neighbourhood_re_tsum_liTerm_neg hm hv hM hs hlt
  rw [Filter.frequently_atTop]
  intro N₂
  obtain ⟨n, hnA, hnN, hrec⟩ := hA k φ (Real.pi / 3) (by positivity) (max N₀ N₂)
  exact ⟨n, le_trans (le_max_right _ _) hnN, hnA, hneg n (le_trans (le_max_left _ _) hnN) hrec⟩

/-! ## The case of `ξ` -/

/-- **Li's failure set for `ξ` contains a Bohr neighbourhood of `0`.** If the Riemann hypothesis fails,
there are finitely many angles `φ_i` and `N₀` such that `Re 2λ_n < 0` for every `n ≥ N₀` with all
`nφ_i` within `π/3` of `2πℤ`. -/
theorem exists_bohr_neighbourhood_re_xiLiPaired_neg (hRH : ¬ RiemannHypothesis) :
    ∃ (k : ℕ) (φ : Fin k → ℝ) (N₀ : ℕ), ∀ n : ℕ, N₀ ≤ n →
      (∀ i, ∃ z : ℤ, |(n : ℝ) * φ i - z * (2 * Real.pi)| < Real.pi / 3) →
      (xiLiPaired n).re < 0 := by
  obtain ⟨M, hmult, hvnorm, hvM, hsum, _, hbad⟩ := xiLi_family_facts
  obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
  obtain ⟨k, φ, N₀, h⟩ :=
    exists_bohr_neighbourhood_re_tsum_liTerm_neg hmult hvnorm hvM hsum hρ₀
  exact ⟨k, φ, N₀, fun n hn hrec => by rw [re_xiLiPaired_eq_tsum_mult]; exact h n hn hrec⟩

/-- **Li's criterion along any set of Bohr recurrence.** If `A` is a set of Bohr recurrence, the Riemann
hypothesis holds iff `Re 2λ_n ≥ 0` for all large `n ∈ A`. -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_of_isBohrRecurrent {A : Set ℕ}
    (hA : IsBohrRecurrent A) :
    RiemannHypothesis ↔ ∀ᶠ n in atTop, n ∈ A → 0 ≤ (xiLiPaired n).re := by
  constructor
  · intro hRH
    exact Filter.Eventually.of_forall fun n _ => re_xiLiPaired_nonneg_of_rh hRH n
  · intro h
    by_contra hRH
    obtain ⟨k, φ, N₀, hneg⟩ := exists_bohr_neighbourhood_re_xiLiPaired_neg hRH
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h
    obtain ⟨n, hnA, hnN, hrec⟩ := hA k φ (Real.pi / 3) (by positivity) (max N₀ N₁)
    have h1 := hN₁ n (le_trans (le_max_right _ _) hnN) hnA
    have h2 := hneg n (le_trans (le_max_left _ _) hnN) hrec
    linarith

/-! ## The Dirichlet root sum and its character expansion -/

/-- `S_M(t) = Σ_{j ≤ M} e^{ijt}`. -/
def rootSum (M : ℕ) (t : ℝ) : ℂ := ∑ j : Fin (M + 1), Complex.exp ((((j : ℕ) : ℝ) * t : ℝ) * I)

/-- The sum of the entries of a tuple. -/
def tupleSum {M r : ℕ} (J : Fin r → Fin (M + 1)) : ℕ := ∑ s, (J s : ℕ)

/-- The frequency `ΣJ − ΣJ'` of a pair of tuples. -/
def tuplePairFreq {M r : ℕ} (q : (Fin r → Fin (M + 1)) × (Fin r → Fin (M + 1))) : ℤ :=
  (tupleSum q.1 : ℤ) - (tupleSum q.2 : ℤ)

theorem rootSum_pow (M r : ℕ) (t : ℝ) : rootSum M t ^ r =
    ∑ J : Fin r → Fin (M + 1), Complex.exp ((((tupleSum J : ℕ) : ℝ) * t : ℝ) * I) := by
  classical
  rw [rootSum, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← Complex.exp_sum]
  congr 1
  simp only [tupleSum]
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]

theorem normSq_rootSum_pow (M r : ℕ) (t : ℝ) :
    ((Complex.normSq (rootSum M t) ^ r : ℝ) : ℂ) =
      ∑ q : (Fin r → Fin (M + 1)) × (Fin r → Fin (M + 1)),
        Complex.exp ((((tuplePairFreq q : ℤ) : ℝ) * t : ℝ) * I) := by
  have h1 : ((Complex.normSq (rootSum M t) ^ r : ℝ) : ℂ) =
      rootSum M t ^ r * (starRingEnd ℂ) (rootSum M t ^ r) := by
    rw [Complex.mul_conj, map_pow]
  rw [h1, rootSum_pow, map_sum, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun J' _ => ?_
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [tuplePairFreq, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem prod_normSq_rootSum_pow {k : ℕ} (M r : ℕ) (y : Fin k → ℝ) :
    ∏ i, Complex.normSq (rootSum M (y i)) ^ r =
      ∑ α : Fin k → (Fin r → Fin (M + 1)) × (Fin r → Fin (M + 1)),
        Real.cos (∑ i, ((tuplePairFreq (α i) : ℤ) : ℝ) * y i) := by
  classical
  have hC : ((∏ i, Complex.normSq (rootSum M (y i)) ^ r : ℝ) : ℂ) =
      ∑ α : Fin k → (Fin r → Fin (M + 1)) × (Fin r → Fin (M + 1)),
        Complex.exp (((∑ i, ((tuplePairFreq (α i) : ℤ) : ℝ) * y i : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_prod]
    simp_rw [normSq_rootSum_pow]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  have h := congrArg Complex.re hC
  rw [Complex.ofReal_re] at h
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Complex.exp_ofReal_mul_I_re]

/-! ## The constant term: Cauchy–Schwarz on tuple sums -/

theorem tupleSum_le {M r : ℕ} (J : Fin r → Fin (M + 1)) : tupleSum J ≤ r * M := by
  unfold tupleSum
  calc ∑ s, (J s : ℕ) ≤ ∑ _s : Fin r, M :=
        Finset.sum_le_sum fun s _ => Nat.lt_succ_iff.mp (J s).2
    _ = r * M := by simp

/-- `(M+1)^{2r} ≤ #{(J, J') : ΣJ = ΣJ'} · (rM + 1)`. -/
theorem pow_le_card_pairFreq_eq_zero_mul (M r : ℕ) :
    (M + 1) ^ (2 * r) ≤ (univ.filter fun q : (Fin r → Fin (M + 1)) × (Fin r → Fin (M + 1)) =>
      tuplePairFreq q = 0).card * (r * M + 1) := by
  classical
  set N : ℕ → ℕ := fun t =>
    (univ.filter fun J : Fin r → Fin (M + 1) => tupleSum J = t).card with hN
  have hmaps : ∀ J ∈ (univ : Finset (Fin r → Fin (M + 1))), tupleSum J ∈ range (r * M + 1) :=
    fun J _ => mem_range.mpr (Nat.lt_succ_of_le (tupleSum_le J))
  have hsum : ∑ t ∈ range (r * M + 1), N t = (M + 1) ^ r := by
    have h := Finset.card_eq_sum_card_fiberwise (f := tupleSum)
      (s := (univ : Finset (Fin r → Fin (M + 1)))) (t := range (r * M + 1))
      (fun J hJ => hmaps J hJ)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
    rw [h]
  have hZ : (univ.filter fun q : (Fin r → Fin (M + 1)) × (Fin r → Fin (M + 1)) =>
      tuplePairFreq q = 0).card = ∑ t ∈ range (r * M + 1), N t ^ 2 := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    have h1 : ∀ J : Fin r → Fin (M + 1),
        (∑ J' : Fin r → Fin (M + 1), if tuplePairFreq (J, J') = 0 then 1 else 0) = N (tupleSum J) := by
      intro J
      simp only [hN]
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun J' _ => ?_
      have : tuplePairFreq (J, J') = 0 ↔ tupleSum J' = tupleSum J := by
        simp only [tuplePairFreq]; omega
      simp only [this]
    rw [Finset.sum_congr rfl fun J _ => h1 J, ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl fun J hJ => by rw [(Finset.mem_filter.mp hJ).2], Finset.sum_const,
      smul_eq_mul, sq]
  have hCS := sq_sum_le_card_mul_sum_sq (s := range (r * M + 1)) (f := fun t => N t)
  rw [hsum, card_range, ← hZ] at hCS
  calc (M + 1) ^ (2 * r) = ((M + 1) ^ r) ^ 2 := by ring
    _ ≤ _ := by rw [mul_comm]; exact hCS

/-! ## Off the Bohr box -/

theorem sin_half_le_abs_sin_half {t η : ℝ} (hη : 0 < η) (hηπ : η ≤ Real.pi)
    (hfar : ∀ z : ℤ, η ≤ |t - z * (2 * Real.pi)|) : Real.sin (η / 2) ≤ |Real.sin (t / 2)| := by
  have hπ := Real.pi_pos
  set z : ℤ := round (t / (2 * Real.pi)) with hz
  set t' := t - z * (2 * Real.pi) with ht'
  have h1 : |t'| ≤ Real.pi := by
    have h := abs_sub_round (t / (2 * Real.pi))
    rw [← hz] at h
    have e : t' = (2 * Real.pi) * (t / (2 * Real.pi) - z) := by rw [ht']; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    nlinarith
  have h2 : η ≤ |t'| := hfar z
  have hsin : |Real.sin (t / 2)| = |Real.sin (t' / 2)| := by
    have e : t / 2 = t' / 2 + (z : ℤ) * Real.pi := by rw [ht']; ring
    rw [e, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  rw [hsin]
  have h3 : Real.sin (|t'| / 2) ≤ |Real.sin (t' / 2)| := by
    rcases le_or_gt 0 t' with h | h
    · rw [abs_of_nonneg h]; exact le_abs_self _
    · rw [abs_of_neg h, show -t' / 2 = -(t' / 2) by ring, Real.sin_neg]; exact neg_le_abs _
  refine le_trans ?_ h3
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

theorem normSq_rootSum_le (M : ℕ) (t : ℝ) : Complex.normSq (rootSum M t) ≤ ((M : ℝ) + 1) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have h : ‖rootSum M t‖ ≤ (M : ℝ) + 1 := by
    calc ‖rootSum M t‖ ≤ ∑ j : Fin (M + 1), ‖Complex.exp ((((j : ℕ) : ℝ) * t : ℝ) * I)‖ :=
          norm_sum_le _ _
      _ = (M : ℝ) + 1 := by
          rw [Finset.sum_congr rfl fun j _ => Complex.norm_exp_ofReal_mul_I _]
          simp
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem normSq_rootSum_le_of_far {M : ℕ} {t η : ℝ} (hη : 0 < η) (hηπ : η ≤ Real.pi)
    (hfar : ∀ z : ℤ, η ≤ |t - z * (2 * Real.pi)|) :
    Complex.normSq (rootSum M t) ≤ 1 / Real.sin (η / 2) ^ 2 := by
  have hπ := Real.pi_pos
  set w : ℂ := Complex.exp ((t : ℂ) * I) with hw
  have hw1 : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hsum : rootSum M t = ∑ j ∈ range (M + 1), w ^ j := by
    rw [rootSum, Fin.sum_univ_eq_sum_range
      (fun j : ℕ => Complex.exp ((((j : ℕ) : ℝ) * t : ℝ) * I)) (M + 1)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hw, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hs := sin_half_le_abs_sin_half hη hηπ hfar
  have hs0 : 0 < Real.sin (η / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hnorm : ‖w - 1‖ = 2 * |Real.sin (t / 2)| := by
    rw [hw, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
      abs_two]
  have hwne : w ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hnorm
    linarith
  have hg := norm_geom_sum_le_of_ne_one hw1 hwne (M + 1)
  rw [← hsum, hnorm] at hg
  have hS : ‖rootSum M t‖ ≤ 1 / Real.sin (η / 2) := by
    refine le_trans hg ?_
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * |Real.sin (t / 2)|) hs0]
    linarith
  rw [Complex.normSq_eq_norm_sq, one_div, ← inv_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (by rwa [one_div] at hS) 2

/-! ## A cosine family that is negative off the Bohr box -/

/-- **A negative cosine family off the Bohr box.** For `k ≥ 1` rotations `φ` and `0 < η ≤ π` there is
a finite nonempty family of frequencies `ω_a` with `Σ_a cos(nω_a) < 0` whenever some `nφ_i` is at
distance at least `η` from `2πℤ`. -/
theorem exists_cos_family_of_far {k : ℕ} (hk : 1 ≤ k) (φ : Fin k → ℝ) {η : ℝ} (hη : 0 < η)
    (hηπ : η ≤ Real.pi) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (ω : ι → ℝ),
      ∀ n : ℕ, (∃ i, ∀ z : ℤ, η ≤ |(n : ℝ) * φ i - z * (2 * Real.pi)|) →
        ∑ a, Real.cos (n * ω a) < 0 := by
  classical
  have hπ := Real.pi_pos
  set s : ℝ := Real.sin (η / 2) with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1 : s ≤ 1 := Real.sin_le_one _
  set M : ℕ := ⌈((k : ℝ) + 1) / s ^ 2⌉₊ with hM
  have hMge : ((k : ℝ) + 1) / s ^ 2 ≤ M := Nat.le_ceil _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ ((k : ℝ) + 1) / s ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    exact_mod_cast le_trans this hMge
  refine ⟨{α : Fin k → (Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)) //
      ¬ ∀ i, tuplePairFreq (α i) = 0}, inferInstance, ?_,
    fun a => ∑ i, ((tuplePairFreq (a.1 i) : ℤ) : ℝ) * φ i, ?_⟩
  · refine ⟨⟨fun _ => (fun _ => ⟨1, by omega⟩, fun _ => 0), fun h => ?_⟩⟩
    have h0 := h ⟨0, by omega⟩
    simp only [tuplePairFreq, tupleSum, Fin.val_zero, Finset.sum_const_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h0
    omega
  · rintro n ⟨i₀, hfar⟩
    set y : Fin k → ℝ := fun i => (n : ℝ) * φ i with hy
    set Z : Finset ((Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1))) :=
      univ.filter (fun q => tuplePairFreq q = 0) with hZ
    -- the character expansion splits into the zero frequencies and the family
    have hsplit : ∏ i, Complex.normSq (rootSum M (y i)) ^ k =
        ((Z.card : ℝ) ^ k) + ∑ a : {α : Fin k → (Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)) //
          ¬ ∀ i, tuplePairFreq (α i) = 0}, Real.cos (n * ∑ i, ((tuplePairFreq (a.1 i) : ℤ) : ℝ) * φ i) := by
      rw [prod_normSq_rootSum_pow, ← Finset.sum_filter_add_sum_filter_not univ
        (fun α : Fin k → (Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)) =>
          ∀ i, tuplePairFreq (α i) = 0)]
      congr 1
      · have hfil : (univ.filter fun α : Fin k → (Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)) =>
            ∀ i, tuplePairFreq (α i) = 0) = Fintype.piFinset (fun _ => Z) := by
          ext α
          simp [Fintype.mem_piFinset, hZ]
        rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (fun α hα => by
          have h := (Finset.mem_filter.mp hα).2
          simp [h]), Finset.sum_const, nsmul_eq_mul, mul_one, hfil, Fintype.card_piFinset]
        simp
      · rw [Finset.sum_subtype (p := fun α : Fin k → (Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)) =>
          ¬ ∀ i, tuplePairFreq (α i) = 0) _ (fun α => by simp)]
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hy]
        ring
    -- the product is small off the box
    set X : ℝ := (M : ℝ) + 1 with hX
    have hX1 : 1 ≤ X := by rw [hX]; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    set C : ℝ := (X ^ 2) ^ k with hC
    have hfac : ∀ i, 0 ≤ Complex.normSq (rootSum M (y i)) ^ k := fun i =>
      pow_nonneg (Complex.normSq_nonneg _) k
    have hQle : ∏ i, Complex.normSq (rootSum M (y i)) ^ k ≤
        (1 / s ^ 2) ^ k * C ^ (univ.erase i₀).card := by
      rw [← Finset.mul_prod_erase univ (fun i => Complex.normSq (rootSum M (y i)) ^ k)
        (mem_univ i₀)]
      refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun i _ => hfac i) (by positivity)
      · exact pow_le_pow_left₀ (Complex.normSq_nonneg _)
          (normSq_rootSum_le_of_far hη hηπ hfar) k
      · rw [← Finset.prod_const]
        exact Finset.prod_le_prod (fun i _ => hfac i) fun i _ =>
          pow_le_pow_left₀ (Complex.normSq_nonneg _) (normSq_rootSum_le M (y i)) k
    have hcard : (univ.erase i₀).card + 1 = k := by
      rw [Finset.card_erase_of_mem (mem_univ i₀), Finset.card_univ, Fintype.card_fin]; omega
    -- the constant term is large
    have hcount := pow_le_card_pairFreq_eq_zero_mul M k
    have hcountR : X ^ (2 * k) ≤ (Z.card : ℝ) * ((k : ℝ) * M + 1) := by
      rw [hX]; exact_mod_cast hcount
    set Zc : ℝ := (Z.card : ℝ) with hZc
    have hkey : (k : ℝ) * M + 1 < s ^ 2 * X ^ 2 := by
      have h1 : (k : ℝ) + 1 ≤ s ^ 2 * M := by
        rw [div_le_iff₀ (by positivity)] at hMge; linarith
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      rw [hX]; nlinarith
    have hpos : (0 : ℝ) < (k : ℝ) * M + 1 := by positivity
    have hlt : (1 / s ^ 2) ^ k * ((k : ℝ) * M + 1) ^ k < X ^ (2 * k) := by
      have h := pow_lt_pow_left₀ hkey hpos.le (by omega : k ≠ 0)
      have e : X ^ (2 * k) = (1 / s ^ 2) ^ k * (s ^ 2 * X ^ 2) ^ k := by
        rw [← mul_pow, ← mul_assoc, one_div, inv_mul_cancel₀ (by positivity), one_mul, ← pow_mul]
      rw [e]
      exact mul_lt_mul_of_pos_left h (by positivity)
    have hQ : ∏ i, Complex.normSq (rootSum M (y i)) ^ k < Zc ^ k := by
      have hC0 : 0 < C := by positivity
      have h1 : (∏ i, Complex.normSq (rootSum M (y i)) ^ k) * ((k : ℝ) * M + 1) ^ k <
          Zc ^ k * ((k : ℝ) * M + 1) ^ k := by
        calc (∏ i, Complex.normSq (rootSum M (y i)) ^ k) * ((k : ℝ) * M + 1) ^ k
            ≤ (1 / s ^ 2) ^ k * C ^ (univ.erase i₀).card * ((k : ℝ) * M + 1) ^ k :=
              mul_le_mul_of_nonneg_right hQle (by positivity)
          _ = C ^ (univ.erase i₀).card * ((1 / s ^ 2) ^ k * ((k : ℝ) * M + 1) ^ k) := by ring
          _ < C ^ (univ.erase i₀).card * X ^ (2 * k) :=
              mul_lt_mul_of_pos_left hlt (by positivity)
          _ = (X ^ (2 * k)) ^ k := by
              generalize hc : (univ.erase i₀).card = c at hcard ⊢
              rw [hC, ← hcard]
              ring_nf
          _ ≤ (Zc * ((k : ℝ) * M + 1)) ^ k :=
              pow_le_pow_left₀ (by positivity) hcountR k
          _ = Zc ^ k * ((k : ℝ) * M + 1) ^ k := mul_pow _ _ _
      exact lt_of_mul_lt_mul_right h1 (by positivity)
    rw [hsplit] at hQ
    linarith

/-! ## Li thinning forces recurrence -/

/-- **Li thinning forces Bohr recurrence.** -/
theorem isBohrRecurrent_of_liThinning {A : Set ℕ} (hA : LiThinning A) : IsBohrRecurrent A := by
  intro k φ η hη N
  by_contra hno
  push Not at hno
  have hπ := Real.pi_pos
  set η' := min η Real.pi with hη'
  have hη'0 : 0 < η' := lt_min hη hπ
  have hfar : ∀ n ∈ A, N ≤ n → ∃ i, ∀ z : ℤ, η' ≤ |(n : ℝ) * φ i - z * (2 * Real.pi)| := by
    intro n hn hN
    obtain ⟨i, hi⟩ := hno n hn hN
    exact ⟨i, fun z => le_trans (min_le_left _ _) (hi z)⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- no rotations: `A` has no element beyond `N`
    subst hk0
    have hfin : ∀ n ∈ A, ¬ N ≤ n := fun n hn hN => by
      obtain ⟨i, _⟩ := hfar n hn hN
      exact i.elim0
    have h := hA Unit (fun _ => 2) (fun _ => 1) 2 (fun _ => le_rfl) (fun _ => by norm_num)
      (fun _ => by norm_num) Summable.of_finite ⟨(), by norm_num⟩
    obtain ⟨n, hnN, hnA, _⟩ := (Filter.frequently_atTop.mp h) N
    exact hfin n hnA hnN
  · obtain ⟨ι, hι, hne, ω, hω⟩ := exists_cos_family_of_far hkpos φ hη'0 (min_le_right _ _)
    have hu : ∀ a, ‖Complex.exp ((ω a : ℂ) * I)‖ = 1 := fun a => Complex.norm_exp_ofReal_mul_I _
    have hv : ∀ a, ‖(2 : ℂ) * Complex.exp ((ω a : ℂ) * I)‖ = 2 := fun a => by
      rw [norm_mul, hu, mul_one]; norm_num
    obtain ⟨a₀⟩ := hne
    have h := hA ι (fun a => (2 : ℂ) * Complex.exp ((ω a : ℂ) * I)) (fun _ => 1) 2
      (fun _ => le_rfl) (fun a => by rw [hv]; norm_num) (fun a => by rw [hv])
      Summable.of_finite ⟨a₀, by rw [hv]; norm_num⟩
    obtain ⟨n, hnN, hnA, hneg⟩ := (Filter.frequently_atTop.mp h) N
    have hc := hω n (hfar n hnA hnN)
    rw [tsum_fintype] at hneg
    have hterm : ∀ a, (1 : ℝ) * (liTerm ((2 : ℂ) * Complex.exp ((ω a : ℂ) * I)) n).re =
        2 - (2 ^ n + (2⁻¹) ^ n) * Real.cos (n * ω a) := by
      intro a
      have e : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
      rw [one_mul, e, re_liTerm_ofReal_mul_unit (hu a) (by norm_num : (0 : ℝ) < 2),
        ← Complex.exp_nat_mul]
      have e2 : (n : ℂ) * ((ω a : ℂ) * I) = (((n : ℝ) * ω a : ℝ) : ℂ) * I := by push_cast; ring
      rw [e2, Complex.exp_ofReal_mul_I_re]
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib, ← Finset.mul_sum] at hneg
    have h2 : (0 : ℝ) < 2 ^ n + (2⁻¹) ^ n := by positivity
    have h3 : (0 : ℝ) ≤ ∑ _a : ι, (2 : ℝ) := Finset.sum_nonneg fun _ _ => by norm_num
    nlinarith

/-- **Li's criterion along `A` is complete for all abstract configurations exactly when `A` is a set of
Bohr recurrence.** -/
theorem liThinning_iff_isBohrRecurrent (A : Set ℕ) : LiThinning A ↔ IsBohrRecurrent A :=
  ⟨isBohrRecurrent_of_liThinning, liThinning_of_isBohrRecurrent⟩

end RHTower

end
