import GaloisForLFunctions.HTGeometry.PolydiscSeriesCoefficients

/-!
# A holomorphic function of several complex variables is analytic

The Cauchy kernel of a polydisc expands, at every point of the distinguished boundary, into the
geometric series of the coordinate ratios; grouping the multi-indices by total degree and summing
term by term under the integral turns the Cauchy integral formula into a convergent power series.
So a function of several complex variables that is complex differentiable is analytic, which the
one-variable theory of mathlib does not give.

* `hasSum_torusIntegral` : term-by-term summation of a dominated series of torus integrals.
* `polydiscHasFPowerSeriesOnBall` : the power series of a holomorphic function on a polydisc.
* `analyticAt_of_differentiable` : complex differentiability implies analyticity in several
  variables.
-/

open MeasureTheory Complex Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

section TorusHasSum

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **A dominated series of torus integrals may be summed term by term.** -/
theorem hasSum_torusIntegral {c : Fin n → ℂ} {R : Fin n → ℝ} {F : ℕ → (Fin n → ℂ) → E}
    {G : (Fin n → ℂ) → E} {b : ℕ → ℝ}
    (hF : ∀ k, Continuous fun θ : Fin n → ℝ => F k (torusMap c R θ))
    (hpt : ∀ θ : Fin n → ℝ, HasSum (fun k => F k (torusMap c R θ)) (G (torusMap c R θ)))
    (hb : ∀ (k : ℕ) (θ : Fin n → ℝ), ‖F k (torusMap c R θ)‖ ≤ b k) (hbsum : Summable b) :
    HasSum (fun k => ∯ ζ in T(c, R), F k ζ) (∯ ζ in T(c, R), G ζ) := by
  classical
  set box : Set (Fin n → ℝ) := Icc (0 : Fin n → ℝ) fun _ => 2 * π with hbox
  set w : (Fin n → ℝ) → ℂ :=
    fun θ => ∏ i, (R i : ℂ) * Complex.exp (θ i * Complex.I) * Complex.I with hw
  have hwcont : Continuous w := by
    refine continuous_finsetProd _ fun i _ => ?_
    fun_prop
  have hwnorm : ∀ θ, ‖w θ‖ ≤ ∏ i, |R i| := by
    intro θ
    rw [hw]
    show ‖∏ i, (R i : ℂ) * Complex.exp (θ i * Complex.I) * Complex.I‖ ≤ ∏ i, |R i|
    rw [norm_prod]
    refine le_of_eq (Finset.prod_congr rfl fun i _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hint : ∀ k, IntegrableOn (fun θ => w θ • F k (torusMap c R θ)) box volume := fun k =>
    ((hwcont.smul (hF k)).continuousOn).integrableOn_compact isCompact_Icc
  have hbnn : ∀ k, 0 ≤ b k := fun k => le_trans (norm_nonneg _) (hb k fun _ => 0)
  have hprodnn : (0 : ℝ) ≤ ∏ i, |R i| := Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hnormbound : ∀ k, (∫ θ in box, ‖w θ • F k (torusMap c R θ)‖) ≤
      (volume box).toReal * ((∏ i, |R i|) * b k) := by
    intro k
    have h1 : ∀ θ, ‖w θ • F k (torusMap c R θ)‖ ≤ (∏ i, |R i|) * b k := by
      intro θ
      rw [norm_smul]
      exact mul_le_mul (hwnorm θ) (hb k θ) (norm_nonneg _) hprodnn
    have h2 : (∫ θ in box, ‖w θ • F k (torusMap c R θ)‖) ≤
        ∫ _θ in box, (∏ i, |R i|) * b k := by
      refine setIntegral_mono_on (hint k).norm ?_ measurableSet_Icc fun θ _ => h1 θ
      exact (continuous_const.continuousOn).integrableOn_compact isCompact_Icc
    rwa [setIntegral_const, smul_eq_mul] at h2
  have hsummable : Summable fun k => ∫ θ in box, ‖w θ • F k (torusMap c R θ)‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun θ => norm_nonneg _)
      hnormbound ?_
    exact (hbsum.mul_left (∏ i, |R i|)).mul_left ((volume box).toReal)
  have hmain := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsummable
  have htsum : (fun θ => ∑' k, w θ • F k (torusMap c R θ)) =
      fun θ => w θ • G (torusMap c R θ) := by
    funext θ
    exact ((hpt θ).const_smul (w θ)).tsum_eq
  rw [htsum] at hmain
  exact hmain

end TorusHasSum

section KernelExpansion

variable {n : ℕ}

/-- The part of degree `k` of the expansion of the Cauchy kernel of a polydisc. -/
noncomputable def polydiscKernelTerm (c y : Fin n → ℂ) (k : ℕ) (ζ : Fin n → ℂ) : ℂ :=
  ∑ m ∈ Finset.Nat.antidiagonalTuple n k, (∏ i, y i ^ m i) * (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹

/-- **The Cauchy kernel of a polydisc expands into the geometric series of the coordinate
ratios**, grouped by total degree. -/
theorem hasSum_polydiscKernelTerm {c y ζ : Fin n → ℂ} (hζ : ∀ i, ‖y i‖ < ‖ζ i - c i‖) :
    HasSum (fun k => polydiscKernelTerm c y k ζ) (∏ i, (ζ i - (c i + y i))⁻¹) := by
  have hne : ∀ i, ζ i - c i ≠ 0 := by
    intro i hcon
    have := hζ i
    rw [hcon, norm_zero] at this
    exact absurd this (not_lt.2 (norm_nonneg _))
  have hunorm : ∀ i, ‖y i / (ζ i - c i)‖ < 1 := by
    intro i
    have hpos : 0 < ‖ζ i - c i‖ := lt_of_le_of_lt (norm_nonneg _) (hζ i)
    rw [norm_div, div_lt_one hpos]
    exact hζ i
  have hgeo := hasSum_multiGeometric n (fun i => y i / (ζ i - c i)) hunorm
  have hconst := hgeo.mul_left (∏ i, (ζ i - c i)⁻¹)
  have hterm : ∀ m : Fin n → ℕ,
      (∏ i, (ζ i - c i)⁻¹) * ∏ i, (y i / (ζ i - c i)) ^ (m i) =
        (∏ i, y i ^ m i) * (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ := by
    intro m
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_pow, pow_succ]
    field_simp
  have hval : (∏ i, (ζ i - c i)⁻¹) * ∏ i, (1 - y i / (ζ i - c i))⁻¹ =
      ∏ i, (ζ i - (c i + y i))⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_inv]
    congr 1
    have h := hne i
    field_simp
    ring
  rw [hval] at hconst
  refine hasSum_degree_regroup ?_
  exact hconst.congr_fun fun m => (hterm m).symm

end KernelExpansion

section PowerSeries

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The value of the term of degree `k` of the series on a constant tuple is the corresponding
Cauchy integral. -/
theorem polydiscSeries_apply_diag {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : ℝ}
    (hf : Continuous fun θ : Fin n → ℝ => f (torusMap c (fun _ => R) θ))
    (hR : 0 < R) (y : Fin n → ℂ) (k : ℕ) :
    (polydiscSeries f c R k fun _ => y) =
      ((2 * Real.pi * Complex.I) ^ n : ℂ)⁻¹ •
        ∯ ζ in T(c, fun _ => R), (polydiscKernelTerm c y k ζ) • f ζ := by
  classical
  have hint : ∀ m ∈ Finset.Nat.antidiagonalTuple n k,
      TorusIntegrable (fun ζ : Fin n → ℂ =>
        ((∏ i, y i ^ m i) * (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹) • f ζ) c (fun _ => R) := by
    intro m _
    refine torusIntegrable_of_continuous ?_
    have hsmul : (fun θ : Fin n → ℝ =>
        ((∏ i, y i ^ m i) * (∏ i, (torusMap c (fun _ => R) θ i - c i) ^ (m i + 1))⁻¹) •
          f (torusMap c (fun _ => R) θ)) =
        fun θ : Fin n → ℝ => (∏ i, y i ^ m i) •
          ((∏ i, (torusMap c (fun _ => R) θ i - c i) ^ (m i + 1))⁻¹ •
            f (torusMap c (fun _ => R) θ)) := by
      funext θ
      rw [smul_smul]
    rw [hsmul]
    exact (polydiscCoeff_continuous hf hR m).const_smul _
  have hstep : (polydiscSeries f c R k fun _ => y) =
      ∑ m ∈ Finset.Nat.antidiagonalTuple n k,
        (∏ i, y i ^ m i) • polydiscCoeff f c R m := by
    show (∑ m ∈ (Finset.Nat.antidiagonalTuple n k).attach,
        (multiIndexCMM m.1 (Finset.Nat.mem_antidiagonalTuple.1 m.2)).smulRight
          (polydiscCoeff f c R m.1)) (fun _ => y) = _
    rw [sum_apply]
    rw [← Finset.sum_attach (Finset.Nat.antidiagonalTuple n k)
      fun m => (∏ i, y i ^ m i) • polydiscCoeff f c R m]
    refine Finset.sum_congr rfl fun m _ => ?_
    show (multiIndexCMM m.1 (Finset.Nat.mem_antidiagonalTuple.1 m.2) fun _ => y) •
      polydiscCoeff f c R m.1 = _
    rw [multiIndexCMM_diagonal]
  have hpull : ∀ m : Fin n → ℕ, (∏ i, y i ^ m i) • polydiscCoeff f c R m =
      ((2 * Real.pi * Complex.I) ^ n : ℂ)⁻¹ •
        ∯ ζ in T(c, fun _ => R),
          ((∏ i, y i ^ m i) * (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹) • f ζ := by
    intro m
    have hfun : (fun ζ : Fin n → ℂ =>
        (∏ i, y i ^ m i) • ((∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • f ζ)) =
        fun ζ : Fin n → ℂ => ((∏ i, y i ^ m i) * (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹) • f ζ := by
      funext ζ
      rw [smul_smul]
    rw [polydiscCoeff, smul_comm, ← torusIntegral_smul, hfun]
  have hfun2 : (fun ζ : Fin n → ℂ => ∑ m ∈ Finset.Nat.antidiagonalTuple n k,
      ((∏ i, y i ^ m i) * (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹) • f ζ) =
      fun ζ : Fin n → ℂ => (∑ m ∈ Finset.Nat.antidiagonalTuple n k,
        (∏ i, y i ^ m i) * (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹) • f ζ := by
    funext ζ
    rw [Finset.sum_smul]
  simp only [polydiscKernelTerm]
  rw [hstep, Finset.sum_congr rfl fun m _ => hpull m, ← Finset.smul_sum,
    ← torusIntegral_finsetSum _ _ hint, hfun2]

end PowerSeries


section Analytic

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The series of the monomial counts against a geometric series converges. -/
theorem summable_succ_pow_mul_geometric (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun k : ℕ => (((k + 1) ^ n : ℕ) : ℝ) * x ^ k := by
  have h1 : Summable fun k : ℕ => ((k : ℝ) ^ n) * x ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one n (by rwa [Real.norm_eq_abs, abs_of_nonneg hx0])
  have h2 : Summable fun k : ℕ => x ^ k := summable_geometric_of_lt_one hx0 hx1
  have hmaj : Summable fun k : ℕ => (2 : ℝ) ^ n * (((k : ℝ) ^ n) * x ^ k) + (2 : ℝ) ^ n * x ^ k :=
    (h1.mul_left _).add (h2.mul_left _)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
  have hkey : (((k + 1) ^ n : ℕ) : ℝ) ≤ (2 : ℝ) ^ n * ((k : ℝ) ^ n) + (2 : ℝ) ^ n := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hz : (0 : ℝ) ≤ (2 : ℝ) ^ n * (((0 : ℕ) : ℝ) ^ n) := by positivity
      have hone : (((0 + 1) ^ n : ℕ) : ℝ) = 1 := by norm_num
      rw [hone]
      linarith
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have h : ((k : ℝ) + 1) ≤ 2 * (k : ℝ) := by linarith
      have hpow : (((k : ℝ) + 1)) ^ n ≤ (2 * (k : ℝ)) ^ n :=
        pow_le_pow_left₀ (by positivity) h n
      have hcast : (((k + 1) ^ n : ℕ) : ℝ) = ((k : ℝ) + 1) ^ n := by push_cast; ring
      have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
      rw [hcast]
      calc ((k : ℝ) + 1) ^ n ≤ (2 * (k : ℝ)) ^ n := hpow
        _ = (2 : ℝ) ^ n * ((k : ℝ) ^ n) := by rw [mul_pow]
        _ ≤ (2 : ℝ) ^ n * ((k : ℝ) ^ n) + (2 : ℝ) ^ n := by linarith
  have hxk : (0 : ℝ) ≤ x ^ k := pow_nonneg hx0 k
  calc (((k + 1) ^ n : ℕ) : ℝ) * x ^ k
      ≤ ((2 : ℝ) ^ n * ((k : ℝ) ^ n) + (2 : ℝ) ^ n) * x ^ k :=
        mul_le_mul_of_nonneg_right hkey hxk
    _ = (2 : ℝ) ^ n * (((k : ℝ) ^ n) * x ^ k) + (2 : ℝ) ^ n * x ^ k := by ring

omit [NormedSpace ℂ E] [CompleteSpace E] in
/-- A holomorphic function is bounded on the distinguished boundary of a polydisc. -/
theorem exists_bound_on_torus {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f {z : Fin n → ℂ | ∀ i, ‖z i - c i‖ = R}) :
    ∃ M : ℝ, ∀ θ : Fin n → ℝ, ‖f (torusMap c (fun _ => R) θ)‖ ≤ M := by
  set T : Set (Fin n → ℂ) := {z : Fin n → ℂ | ∀ i, ‖z i - c i‖ = R} with hT
  have hmemT : ∀ θ : Fin n → ℝ, torusMap c (fun _ => R) θ ∈ T := by
    intro θ i
    rw [norm_torusMap_sub_center, abs_of_pos hR]
  have hclosed : IsClosed T := by
    have heq : T = ⋂ i : Fin n, (fun z : Fin n → ℂ => z i) ⁻¹' (Metric.sphere (c i) R) := by
      ext z
      simp only [hT, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Metric.mem_sphere,
        Complex.dist_eq]
    rw [heq]
    exact isClosed_iInter fun i => (Metric.isClosed_sphere).preimage (continuous_apply i)
  have hbdd : Bornology.IsBounded T := by
    refine (Metric.isBounded_iff_subset_closedBall c).2 ⟨R, fun z hz => ?_⟩
    rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
    intro i
    rw [Complex.dist_eq]
    exact le_of_eq (hz i)
  have hcomp : IsCompact T := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  obtain ⟨p₀, hp₀mem, hp₀⟩ := hcomp.exists_isMaxOn ⟨torusMap c (fun _ => R) 0, hmemT 0⟩
    (continuous_norm.comp_continuousOn hf)
  exact ⟨‖f p₀‖, fun θ => hp₀ (hmemT θ)⟩

omit [CompleteSpace E] in
/-- **A continuous affine-line-entire function has its Cauchy power series on every polydisc.**
This is the finite-dimensional Banach-valued Gâteaux-to-Fréchet bridge. -/
theorem polydiscSeries_hasSum_of_cauchy
    {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f {z : Fin n → ℂ | ∀ i, ‖z i - c i‖ = R})
    (hcauchy : ∀ z : Fin n → ℂ, (∀ i, z i ∈ Metric.ball (c i) R) →
      (∯ ζ in T(c, fun _ => R), (∏ i, (ζ i - z i)⁻¹) • f ζ) =
        ((2 * Real.pi * Complex.I) ^ n : ℂ) • f z)
    {M : ℝ} (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c (fun _ => R) θ)‖ ≤ M)
    {y : Fin n → ℂ} (hy : ‖y‖ < R) :
    HasSum (fun k => polydiscSeries f c R k fun _ => y) (f (c + y)) := by
  classical
  have hmemT : ∀ θ : Fin n → ℝ,
      torusMap c (fun _ => R) θ ∈ {z : Fin n → ℂ | ∀ i, ‖z i - c i‖ = R} := by
    intro θ i
    rw [norm_torusMap_sub_center, abs_of_pos hR]
  have hfT : Continuous fun θ : Fin n → ℝ => f (torusMap c (fun _ => R) θ) :=
    hf.comp_continuous (continuous_torusMap c fun _ => R) hmemT
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM fun _ => 0)
  have hynn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
  have hyi : ∀ i, ‖y i‖ < R := fun i => lt_of_le_of_lt (norm_le_pi_norm y i) hy
  -- the dominating sequence
  set b : ℕ → ℝ := fun k => (((k + 1) ^ n : ℕ) : ℝ) * (‖y‖ / R) ^ k * (M / R ^ n) with hb
  have hbsum : Summable b := by
    rw [hb]
    exact (summable_succ_pow_mul_geometric n (by positivity)
      ((div_lt_one hR).2 hy)).mul_right _
  -- the terms and their pointwise sum
  have hkernelbound : ∀ (k : ℕ) (θ : Fin n → ℝ),
      ‖(polydiscKernelTerm c y k (torusMap c (fun _ => R) θ)) •
        f (torusMap c (fun _ => R) θ)‖ ≤ b k := by
    intro k θ
    have hnormζ : ∀ i, ‖torusMap c (fun _ => R) θ i - c i‖ = R := by
      intro i
      rw [norm_torusMap_sub_center, abs_of_pos hR]
    have hterm : ∀ m ∈ Finset.Nat.antidiagonalTuple n k,
        ‖(∏ i, y i ^ m i) *
          (∏ i, (torusMap c (fun _ => R) θ i - c i) ^ (m i + 1))⁻¹‖ ≤ ‖y‖ ^ k / R ^ (k + n) := by
      intro m hm
      have hk : ∑ i, m i = k := Finset.Nat.mem_antidiagonalTuple.1 hm
      rw [norm_mul, norm_inv, norm_prod, norm_prod]
      have h1 : (∏ i, ‖y i ^ m i‖) ≤ ‖y‖ ^ k := by
        calc (∏ i, ‖y i ^ m i‖) = ∏ i, ‖y i‖ ^ (m i) := by
              exact Finset.prod_congr rfl fun i _ => norm_pow _ _
          _ ≤ ∏ i, ‖y‖ ^ (m i) :=
              Finset.prod_le_prod (fun i _ => by positivity)
                (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm y i) _)
          _ = ‖y‖ ^ k := by rw [Finset.prod_pow_eq_pow_sum, hk]
      have h2 : (∏ i, ‖(torusMap c (fun _ => R) θ i - c i) ^ (m i + 1)‖) = R ^ (k + n) := by
        have hstep : ∀ i : Fin n, ‖(torusMap c (fun _ => R) θ i - c i) ^ (m i + 1)‖ =
            R ^ (m i + 1) := by
          intro i
          rw [norm_pow, hnormζ i]
        rw [Finset.prod_congr rfl fun i _ => hstep i, Finset.prod_pow_eq_pow_sum]
        congr 1
        rw [Finset.sum_add_distrib, hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one]
      rw [h2, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hkernel : ‖polydiscKernelTerm c y k (torusMap c (fun _ => R) θ)‖ ≤
        (((k + 1) ^ n : ℕ) : ℝ) * (‖y‖ ^ k / R ^ (k + n)) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc (∑ m ∈ Finset.Nat.antidiagonalTuple n k,
              ‖(∏ i, y i ^ m i) *
                (∏ i, (torusMap c (fun _ => R) θ i - c i) ^ (m i + 1))⁻¹‖)
          ≤ ∑ _m ∈ Finset.Nat.antidiagonalTuple n k, ‖y‖ ^ k / R ^ (k + n) :=
            Finset.sum_le_sum hterm
        _ = ((Finset.Nat.antidiagonalTuple n k).card : ℝ) * (‖y‖ ^ k / R ^ (k + n)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (((k + 1) ^ n : ℕ) : ℝ) * (‖y‖ ^ k / R ^ (k + n)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast card_antidiagonalTuple_le n k
    rw [norm_smul]
    simp only [hb]
    have hbeq : (((k + 1) ^ n : ℕ) : ℝ) * (‖y‖ / R) ^ k * (M / R ^ n) =
        ((((k + 1) ^ n : ℕ) : ℝ) * (‖y‖ ^ k / R ^ (k + n))) * M := by
      rw [div_pow, pow_add]
      field_simp
    rw [hbeq]
    exact mul_le_mul hkernel (hM θ) (norm_nonneg _) (by positivity)
  have hcont : ∀ k : ℕ, Continuous fun θ : Fin n → ℝ =>
      (polydiscKernelTerm c y k (torusMap c (fun _ => R) θ)) • f (torusMap c (fun _ => R) θ) := by
    intro k
    have hmap : Continuous fun θ : Fin n → ℝ => torusMap c (fun _ => R) θ :=
      continuous_torusMap c fun _ => R
    refine Continuous.smul ?_ hfT
    refine continuous_finsetSum _ fun m _ => ?_
    refine Continuous.mul continuous_const ?_
    refine Continuous.inv₀ ?_ ?_
    · refine continuous_finsetProd _ fun i _ => ?_
      exact (((continuous_apply i).comp hmap).sub continuous_const).pow _
    · intro θ
      refine Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ?_
      intro hcon
      have hn := norm_torusMap_sub_center c R θ i
      rw [hcon, norm_zero] at hn
      exact absurd hn.symm (by positivity)
  have hptsum : ∀ θ : Fin n → ℝ,
      HasSum (fun k => (polydiscKernelTerm c y k (torusMap c (fun _ => R) θ)) •
        f (torusMap c (fun _ => R) θ))
        ((∏ i, (torusMap c (fun _ => R) θ i - (c i + y i))⁻¹) • f (torusMap c (fun _ => R) θ)) := by
    intro θ
    refine HasSum.smul_const ?_ _
    refine hasSum_polydiscKernelTerm fun i => ?_
    rw [norm_torusMap_sub_center, abs_of_pos hR]
    exact hyi i
  have hcontG : Continuous fun θ : Fin n → ℝ =>
      (∏ i, (torusMap c (fun _ => R) θ i - (c i + y i))⁻¹) • f (torusMap c (fun _ => R) θ) := by
    have hmap : Continuous fun θ : Fin n → ℝ => torusMap c (fun _ => R) θ :=
      continuous_torusMap c fun _ => R
    refine Continuous.smul ?_ hfT
    refine continuous_finsetProd _ fun i _ => ?_
    refine Continuous.inv₀ (((continuous_apply i).comp hmap).sub continuous_const) fun θ => ?_
    have hn := norm_torusMap_sub_center c R θ i
    intro hcon
    have hzero : torusMap c (fun _ => R) θ i - c i = y i := by
      have : torusMap c (fun _ => R) θ i = c i + y i := sub_eq_zero.1 hcon
      rw [this]
      ring
    rw [hzero, abs_of_pos hR] at hn
    exact absurd hn (ne_of_lt (hyi i))
  have hmain := hasSum_torusIntegral (c := c) (R := fun _ : Fin n => R)
    (F := fun k ζ => (polydiscKernelTerm c y k ζ) • f ζ)
    (G := fun ζ => (∏ i, (ζ i - (c i + y i))⁻¹) • f ζ) (b := b) hcont hptsum hkernelbound hbsum
  have hcauchy : (∯ ζ in T(c, fun _ => R), (∏ i, (ζ i - (c i + y i))⁻¹) • f ζ) =
      ((2 * Real.pi * Complex.I) ^ n : ℂ) • f (c + y) := by
    have hmem : ∀ i, (c + y) i ∈ Metric.ball (c i) R := by
      intro i
      rw [Metric.mem_ball, dist_eq_norm]
      show ‖c i + y i - c i‖ < R
      rw [add_sub_cancel_left]
      exact hyi i
    have := hcauchy (c + y) hmem
    rw [← this]
    rfl
  rw [hcauchy] at hmain
  have hne : ((2 * Real.pi * Complex.I) ^ n : ℂ) ≠ 0 := by
    refine pow_ne_zero _ ?_
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hfinal := hmain.const_smul (((2 * Real.pi * Complex.I) ^ n : ℂ)⁻¹)
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at hfinal
  refine hfinal.congr_fun fun k => ?_
  exact polydiscSeries_apply_diag hfT hR y k

/-- **A continuous affine-line-entire function has its Cauchy power series on every polydisc.** -/
theorem polydiscSeries_hasSum_of_affineLineEntire
    {f : (Fin n → ℂ) → E} (hf : Continuous f) (hline : AffineLineEntire f)
    (c : Fin n → ℂ)
    {R : ℝ} (hR : 0 < R) {M : ℝ} (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c (fun _ => R) θ)‖ ≤ M)
    {y : Fin n → ℂ} (hy : ‖y‖ < R) :
    HasSum (fun k => polydiscSeries f c R k fun _ => y) (f (c + y)) :=
  polydiscSeries_hasSum_of_cauchy hR hf.continuousOn
    (fun z hz => polydiscCauchyFormula_of_affineLineEntire n f hf hline c (fun _ => R) z hz) hM hy

/-- Compatibility form for a globally Fréchet-differentiable function. -/
theorem polydiscSeries_hasSum {f : (Fin n → ℂ) → E} (hf : Differentiable ℂ f)
    (c : Fin n → ℂ) {R : ℝ} (hR : 0 < R) {M : ℝ}
    (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c (fun _ => R) θ)‖ ≤ M)
    {y : Fin n → ℂ} (hy : ‖y‖ < R) :
    HasSum (fun k => polydiscSeries f c R k fun _ => y) (f (c + y)) :=
  polydiscSeries_hasSum_of_affineLineEntire hf.continuous
    (affineLineEntire_of_differentiable hf) c hR hM hy

omit [CompleteSpace E] in
/-- **A continuous affine-line-entire function has a convergent power series** on every polydisc,
hence on a ball around every point. -/
theorem polydiscHasFPowerSeriesOnBall_of_cauchy
    {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f {z : Fin n → ℂ | ∀ i, ‖z i - c i‖ = R})
    (hcauchy : ∀ z : Fin n → ℂ, (∀ i, z i ∈ Metric.ball (c i) R) →
      (∯ ζ in T(c, fun _ => R), (∏ i, (ζ i - z i)⁻¹) • f ζ) =
        ((2 * Real.pi * Complex.I) ^ n : ℂ) • f z) :
    HasFPowerSeriesOnBall f (polydiscSeries f c R) c (ENNReal.ofReal (R / 2 ^ (n + 1))) := by
  obtain ⟨M, hM⟩ := exists_bound_on_torus hR hf
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM fun _ => 0)
  set ρ : ℝ := R / 2 ^ (n + 1) with hρ
  have hpow : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hρpos : 0 < ρ := by
    rw [hρ]
    positivity
  have hρR : ρ < R := by
    have h2 : (2 : ℝ) ≤ 2 ^ (n + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ (Nat.zero_le n))
    rw [hρ, div_lt_iff₀ hpow]
    nlinarith [hR]
  clear_value ρ
  refine ⟨?_, by rwa [ENNReal.ofReal_pos], ?_⟩
  · show (ENNReal.ofReal ρ) ≤ (polydiscSeries f c R).radius
    have hcast : ENNReal.ofReal ρ = ((ρ.toNNReal : NNReal) : ENNReal) := rfl
    rw [hcast]
    refine (polydiscSeries f c R).le_radius_of_bound M fun k => ?_
    have hcoe : ((ρ.toNNReal : NNReal) : ℝ) = ρ := Real.coe_toNNReal ρ hρpos.le
    rw [hcoe]
    have hnorm := norm_polydiscSeries_le c hR hM k
    have hkey : (((k + 1) ^ n : ℕ) : ℝ) * (ρ / R) ^ k ≤ 1 := by
      have h1 : ((k + 1) ^ n : ℕ) ≤ ((2 ^ n) ^ k : ℕ) := by
        have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
        calc (k + 1) ^ n ≤ (2 ^ k) ^ n := Nat.pow_le_pow_left hk n
          _ = (2 ^ n) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h2 : ρ / R = 1 / 2 ^ (n + 1) := by
        rw [hρ]
        field_simp
      rw [h2]
      calc (((k + 1) ^ n : ℕ) : ℝ) * (1 / 2 ^ (n + 1)) ^ k
          ≤ (((2 ^ n) ^ k : ℕ) : ℝ) * (1 / 2 ^ (n + 1)) ^ k := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast h1
        _ = ((2 : ℝ) ^ n * (1 / 2 ^ (n + 1))) ^ k := by
            rw [mul_pow]
            push_cast
            ring
        _ = ((1 : ℝ) / 2) ^ k := by
            congr 1
            rw [pow_succ]
            field_simp
        _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc ‖polydiscSeries f c R k‖ * ρ ^ k
        ≤ (((k + 1) ^ n : ℕ) : ℝ) * (M / R ^ k) * ρ ^ k :=
          mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ = M * ((((k + 1) ^ n : ℕ) : ℝ) * (ρ / R) ^ k) := by
          rw [div_pow]
          ring
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hkey hMnn
      _ = M := mul_one M
  · intro y hy
    refine polydiscSeries_hasSum_of_cauchy hR hf hcauchy hM ?_
    have h1 : ‖y‖ₑ < ENNReal.ofReal ρ := mem_eball_zero_iff.1 hy
    rw [← ofReal_norm] at h1
    exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff hρpos).1 h1) hρR

/-- **A continuous affine-line-entire function has a convergent power series** on every polydisc. -/
theorem polydiscHasFPowerSeriesOnBall_of_affineLineEntire
    {f : (Fin n → ℂ) → E} (hf : Continuous f) (hline : AffineLineEntire f)
    (c : Fin n → ℂ) {R : ℝ} (hR : 0 < R) :
    HasFPowerSeriesOnBall f (polydiscSeries f c R) c (ENNReal.ofReal (R / 2 ^ (n + 1))) :=
  polydiscHasFPowerSeriesOnBall_of_cauchy hR hf.continuousOn
    (fun z hz => polydiscCauchyFormula_of_affineLineEntire n f hf hline c (fun _ => R) z hz)

/-- Compatibility form for a globally Fréchet-differentiable function. -/
theorem polydiscHasFPowerSeriesOnBall {f : (Fin n → ℂ) → E} (hf : Differentiable ℂ f)
    (c : Fin n → ℂ) {R : ℝ} (hR : 0 < R) :
    HasFPowerSeriesOnBall f (polydiscSeries f c R) c (ENNReal.ofReal (R / 2 ^ (n + 1))) :=
  polydiscHasFPowerSeriesOnBall_of_affineLineEntire hf.continuous
    (affineLineEntire_of_differentiable hf) c hR

/-- **Continuous affine-line entireness implies analyticity in finite complex dimension.** -/
theorem analyticAt_of_continuous_affineLineEntire {f : (Fin n → ℂ) → E}
    (hf : Continuous f) (hline : AffineLineEntire f) (c : Fin n → ℂ) :
    AnalyticAt ℂ f c :=
  (polydiscHasFPowerSeriesOnBall_of_affineLineEntire hf hline c one_pos).analyticAt

/-- Continuous affine-line-entire functions are analytic everywhere. -/
theorem analyticOnNhd_of_continuous_affineLineEntire {f : (Fin n → ℂ) → E}
    (hf : Continuous f) (hline : AffineLineEntire f) :
    AnalyticOnNhd ℂ f Set.univ := fun c _ =>
  analyticAt_of_continuous_affineLineEntire hf hline c

/-- **Finite-dimensional Banach-valued Gâteaux-entire functions are smooth in the Fréchet sense.** -/
theorem contDiff_of_continuous_affineLineEntire {f : (Fin n → ℂ) → E}
    (hf : Continuous f) (hline : AffineLineEntire f) :
    ContDiff ℂ (⊤ : WithTop ℕ∞) f :=
  (analyticOnNhd_of_continuous_affineLineEntire hf hline).contDiff

/-- **Complex differentiability implies analyticity in several variables.** -/
theorem analyticAt_of_differentiable {f : (Fin n → ℂ) → E} (hf : Differentiable ℂ f)
    (c : Fin n → ℂ) : AnalyticAt ℂ f c :=
  (polydiscHasFPowerSeriesOnBall hf c one_pos).analyticAt

/-- **A holomorphic function of several complex variables is analytic everywhere.** -/
theorem analyticOnNhd_of_differentiable {f : (Fin n → ℂ) → E} (hf : Differentiable ℂ f) :
    AnalyticOnNhd ℂ f Set.univ := fun c _ => analyticAt_of_differentiable hf c

end Analytic

end GaloisForLFunctions.HTGeometry
