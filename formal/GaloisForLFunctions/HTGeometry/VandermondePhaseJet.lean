import Mathlib.Tactic

/-!
# The uniform directional phase jet of a finite Laurent phase polynomial

A finite Laurent polynomial `Q(U) = ∑_l c_l U^l` in a single phase variable is determined by its
logarithmic-derivative jets `((U d/dU)^m Q)(a) = ∑_l c_l l^m a^l` at any single point `a`: after
stripping the unimodular factors `a^l` the linear map from coefficients to jets is the Vandermonde
matrix `(l^m)`, invertible because the exponents are distinct.  The resulting lower bound is uniform
over unit phase points, because a diagonal of unimodular entries is an isometry for the supremum
norm.

Grouping a two-variable phase polynomial `∑_{k,l} c_{k,l} W^k U^l` by the exponent of `W` and
multiplying by the unimodular phases `ω^k` preserves the bound, so a nonzero finite phase polynomial
always exposes a jet of size at least a fixed constant, whatever the phase point.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Matrix

/-- **An invertible matrix is bounded below.**  On a finite-dimensional space the minimum of
`‖A x‖` over the unit sphere is attained and positive. -/
theorem exists_matrix_lower_bound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin N → ℂ, c * ‖x‖ ≤ ‖A.mulVec x‖ := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨1, one_pos, fun x => ?_⟩
    have h1 : ‖x‖ = 0 := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg le_rfl).mpr fun i => i.elim0) (norm_nonneg _)
    rw [h1, mul_zero]
    exact norm_nonneg _
  · have hcont : Continuous (fun x : Fin N → ℂ => ‖A.mulVec x‖) := by
      refine Continuous.norm (continuous_pi fun i => ?_)
      show Continuous fun x : Fin N → ℂ => ∑ j, A i j * x j
      exact continuous_finset_sum _ fun j _ => by fun_prop
    have hne : (Metric.sphere (0 : Fin N → ℂ) 1).Nonempty := by
      refine ⟨fun _ => 1, ?_⟩
      rw [Metric.mem_sphere, dist_zero_right]
      refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp) ?_
      have hpi := norm_le_pi_norm (fun _ : Fin N => (1 : ℂ)) ⟨0, hN⟩
      simpa using hpi
    obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
      (isCompact_sphere (0 : Fin N → ℂ) 1).exists_isMinOn hne hcont.continuousOn
    have hx₀norm : ‖x₀‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx₀mem
      exact hx₀mem
    have hx₀ne : x₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx₀norm
      exact zero_ne_one hx₀norm
    have hpos : 0 < ‖A.mulVec x₀‖ := by
      rw [norm_pos_iff]
      intro h
      exact hx₀ne (Matrix.eq_zero_of_mulVec_eq_zero hA h)
    refine ⟨‖A.mulVec x₀‖, hpos, fun x => ?_⟩
    by_cases hx : x = 0
    · rw [hx, norm_zero, mul_zero]
      exact norm_nonneg _
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      set y : Fin N → ℂ := (‖x‖)⁻¹ • x with hydef
      have hynorm : ‖y‖ = 1 := by
        rw [hydef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hxpos,
          inv_mul_cancel₀ (ne_of_gt hxpos)]
      have hymem : y ∈ Metric.sphere (0 : Fin N → ℂ) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]
        exact hynorm
      have hmin : ‖A.mulVec x₀‖ ≤ ‖A.mulVec y‖ := hx₀min hymem
      have hAy : A.mulVec y = (‖x‖)⁻¹ • A.mulVec x := by
        rw [hydef, Matrix.mulVec_smul]
      rw [hAy, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hxpos] at hmin
      have hstep := mul_le_mul_of_nonneg_right hmin hxpos.le
      have heq : (‖x‖)⁻¹ * ‖A.mulVec x‖ * ‖x‖ = ‖A.mulVec x‖ := by
        field_simp
      linarith [hstep, heq.le, heq.ge]

/-- **The uniform logarithmic-derivative jet bound.**  For distinct integer exponents, the jets
`∑_i c_i l_i^m a^{l_i}` control the coefficient vector with a constant depending only on the exponent
set, uniformly over unit phase points. -/
theorem exists_logDeriv_jet_lower_bound {N : ℕ} (l : Fin N → ℤ) (hl : Function.Injective l) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℂ, ‖a‖ = 1 → ∀ C : Fin N → ℂ,
      c * ‖C‖ ≤ ‖fun m : Fin N => ∑ i, (l i : ℂ) ^ (m : ℕ) * (C i * a ^ (l i))‖ := by
  classical
  set A : Matrix (Fin N) (Fin N) ℂ := (Matrix.vandermonde fun i => (l i : ℂ))ᵀ with hAdef
  have hdet : A.det ≠ 0 := by
    rw [hAdef, Matrix.det_transpose, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    rw [sub_ne_zero]
    intro h
    have hij : l j = l i := by exact_mod_cast h
    have : j = i := hl hij
    rw [this] at hj
    exact absurd (Finset.mem_Ioi.mp hj) (lt_irrefl i)
  obtain ⟨c, hc, hbound⟩ := exists_matrix_lower_bound A hdet
  refine ⟨c, hc, fun a ha C => ?_⟩
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    exact zero_ne_one ha
  set D : Fin N → ℂ := fun i => C i * a ^ (l i) with hDdef
  have hDnorm : ‖D‖ = ‖C‖ := by
    have hentry : ∀ i, ‖D i‖ = ‖C i‖ := by
      intro i
      rw [hDdef, norm_mul, norm_zpow, ha, one_zpow, mul_one]
    refine le_antisymm ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
      rw [hentry i]
      exact norm_le_pi_norm C i
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
      rw [← hentry i]
      exact norm_le_pi_norm D i
  have hmul : A.mulVec D = fun m : Fin N => ∑ i, (l i : ℂ) ^ (m : ℕ) * (C i * a ^ (l i)) := by
    funext m
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hAdef]
    simp [Matrix.vandermonde, hDdef]
  have := hbound D
  rw [hDnorm, hmul] at this
  exact this

/-- **The directional phase-jet law.**  Grouping a finite two-variable phase polynomial by the
exponent of the recurrent exponential and evaluating the logarithmic-derivative jets of each group
at a unit phase point gives a family whose maximum norm is at least a fixed multiple of the maximum
coefficient norm, uniformly over both phase points. -/
theorem exists_phase_jet_lower_bound {Kn N : ℕ} (l : Fin N → ℤ) (hl : Function.Injective l) :
    ∃ cst : ℝ, 0 < cst ∧ ∀ ω a : ℂ, ‖ω‖ = 1 → ‖a‖ = 1 → ∀ c : Fin Kn → Fin N → ℂ,
      cst * ‖c‖ ≤ ‖fun p : Fin Kn × Fin N =>
        ω ^ (p.1 : ℕ) * ∑ i, (l i : ℂ) ^ (p.2 : ℕ) * (c p.1 i * a ^ (l i))‖ := by
  classical
  obtain ⟨cst, hcst, hjet⟩ := exists_logDeriv_jet_lower_bound l hl
  refine ⟨cst, hcst, fun ω a hω ha c => ?_⟩
  rcases Nat.eq_zero_or_pos Kn with hK | hK
  · subst hK
    have hc0 : ‖c‖ = 0 :=
      le_antisymm ((pi_norm_le_iff_of_nonneg le_rfl).mpr fun k => k.elim0) (norm_nonneg _)
    rw [hc0, mul_zero]
    exact norm_nonneg _
  · -- pick a group realising the maximum coefficient norm
    have hne : (Finset.univ : Finset (Fin Kn)).Nonempty := ⟨⟨0, hK⟩, Finset.mem_univ _⟩
    obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ (fun k => ‖c k‖) hne
    have hcnorm : ‖c‖ = ‖c k₀‖ := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun k =>
        hk₀ k (Finset.mem_univ k)) (norm_le_pi_norm c k₀)
    rw [hcnorm]
    refine le_trans (hjet a ha (c k₀)) ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun m => ?_
    have hentry := norm_le_pi_norm
      (fun p : Fin Kn × Fin N =>
        ω ^ (p.1 : ℕ) * ∑ i, (l i : ℂ) ^ (p.2 : ℕ) * (c p.1 i * a ^ (l i))) (k₀, m)
    have hnorm : ‖ω ^ (k₀ : ℕ) * ∑ i, (l i : ℂ) ^ (m : ℕ) * (c k₀ i * a ^ (l i))‖
        = ‖∑ i, (l i : ℂ) ^ (m : ℕ) * (c k₀ i * a ^ (l i))‖ := by
      rw [norm_mul, norm_pow, hω, one_pow, one_mul]
    rw [hnorm] at hentry
    exact hentry


/-- **The directional survival bound.**  If the top asymptotic layer of a finite phase polynomial has
a nonzero coefficient family at the growth rate `S^{-M}`, then its phase-jet family has norm at least
a fixed multiple of `S^{-M}` at all large heights, uniformly in the phase point. -/
theorem exists_phase_jet_survival {Kn N : ℕ} {lam : ℝ} (l : Fin N → ℤ)
    (hl : Function.Injective l)
    (b : Fin Kn → Fin N → ℝ → ℂ) (c : Fin Kn → Fin N → ℂ) (hc : c ≠ 0)
    (ω a : ℝ → ℂ) (hω : ∀ S, ‖ω S‖ = 1) (ha : ∀ S, ‖a S‖ = 1)
    (hlayer : ∀ ε : ℝ, 0 < ε → ∀ᶠ S : ℝ in atTop, ∀ k i,
      ‖b k i S - c k i * ((S ^ lam : ℝ) : ℂ)‖ ≤ ε * S ^ lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop,
      C * S ^ lam ≤ ‖fun p : Fin Kn × Fin N =>
        (ω S) ^ (p.1 : ℕ) * ∑ i, (l i : ℂ) ^ (p.2 : ℕ) * (b p.1 i S * (a S) ^ (l i))‖ := by
  classical
  obtain ⟨cst, hcst, hjet⟩ := exists_phase_jet_lower_bound (Kn := Kn) l hl
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set Λ : ℝ := ∑ i : Fin N, (max ‖(l i : ℂ)‖ 1) ^ N with hΛdef
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun i _ => by positivity
  set ε : ℝ := cst * ‖c‖ / (2 * (Λ + 1)) with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    positivity
  refine ⟨cst * ‖c‖ / 2, by positivity, ?_⟩
  filter_upwards [hlayer ε hε0, eventually_gt_atTop (0 : ℝ)] with S hS hS0
  set X : ℝ := S ^ lam with hXdef
  have hX0 : 0 < X := Real.rpow_pos_of_pos hS0 _
  -- the jet family of the layer coefficients
  set G : Fin Kn × Fin N → ℂ := fun p =>
    (ω S) ^ (p.1 : ℕ) * ∑ i, (l i : ℂ) ^ (p.2 : ℕ) * (c p.1 i * (a S) ^ (l i)) with hGdef
  set F : Fin Kn × Fin N → ℂ := fun p =>
    (ω S) ^ (p.1 : ℕ) * ∑ i, (l i : ℂ) ^ (p.2 : ℕ) * (b p.1 i S * (a S) ^ (l i)) with hFdef
  have hlow : cst * ‖c‖ ≤ ‖G‖ := hjet (ω S) (a S) (hω S) (ha S) c
  -- the difference is controlled by the layer error
  have hdiff : ‖F - X • G‖ ≤ Λ * ε * X := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
    have hentry : (F - X • G) p
        = (ω S) ^ (p.1 : ℕ)
          * ∑ i, (l i : ℂ) ^ (p.2 : ℕ) * ((b p.1 i S - c p.1 i * X) * (a S) ^ (l i)) := by
      simp only [Pi.sub_apply, Pi.smul_apply, hFdef, hGdef, Complex.real_smul,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [hentry, norm_mul, norm_pow, hω S, one_pow, one_mul]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin N)),
        ‖(l i : ℂ) ^ (p.2 : ℕ) * ((b p.1 i S - c p.1 i * X) * (a S) ^ (l i))‖
          ≤ (max ‖(l i : ℂ)‖ 1) ^ N * (ε * X) := by
      intro i _
      have haS0 : a S ≠ 0 := by
        intro h
        have := ha S
        rw [h, norm_zero] at this
        exact zero_ne_one this
      rw [norm_mul, norm_pow, norm_mul, norm_zpow, ha S, one_zpow, mul_one]
      have h1 : ‖(l i : ℂ)‖ ^ (p.2 : ℕ) ≤ (max ‖(l i : ℂ)‖ 1) ^ N := by
        calc ‖(l i : ℂ)‖ ^ (p.2 : ℕ) ≤ (max ‖(l i : ℂ)‖ 1) ^ (p.2 : ℕ) :=
              pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _
          _ ≤ (max ‖(l i : ℂ)‖ 1) ^ N := pow_le_pow_right₀ (le_max_right _ _) (by omega)
      have h2 : ‖b p.1 i S - c p.1 i * ((X : ℝ) : ℂ)‖ ≤ ε * X := hS p.1 i
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    calc ∑ i : Fin N, ‖(l i : ℂ) ^ (p.2 : ℕ) * ((b p.1 i S - c p.1 i * X) * (a S) ^ (l i))‖
        ≤ ∑ i : Fin N, (max ‖(l i : ℂ)‖ 1) ^ N * (ε * X) := Finset.sum_le_sum hterm
      _ = Λ * ε * X := by
          rw [hΛdef, ← Finset.sum_mul]
          ring
  -- combine
  have hXG : ‖X • G‖ = X * ‖G‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hX0]
  have hFlow : X * ‖G‖ - Λ * ε * X ≤ ‖F‖ := by
    have hns := norm_sub_norm_le (X • G) F
    rw [hXG, norm_sub_rev] at hns
    linarith [hdiff, hns]
  have hεΛ : Λ * ε ≤ cst * ‖c‖ / 2 := by
    have hA : 0 < cst * ‖c‖ := by positivity
    have hrw : Λ * ε = Λ * (cst * ‖c‖) / (2 * (Λ + 1)) := by
      rw [hεdef]
      ring
    rw [hrw, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hΛ0, hA]
  have hGX : cst * ‖c‖ * X ≤ X * ‖G‖ := by
    rw [mul_comm X ‖G‖]
    exact mul_le_mul_of_nonneg_right hlow hX0.le
  have hstep : Λ * ε * X ≤ cst * ‖c‖ / 2 * X := mul_le_mul_of_nonneg_right hεΛ hX0.le
  linarith [hFlow, hGX, hstep]

/-- **An upper power-Poincaré element.**  Its first generalized power monomial `c · S^λ` is nonzero,
and it has at most polynomial growth on upper vertical tubes together with its reciprocal. -/
structure PowerPoincare (b : ℝ → ℂ) (c : ℂ) (lam : ℝ) : Prop where
  /-- The first generalized power coefficient does not vanish. -/
  ne_zero : c ≠ 0
  /-- The first monomial is the complete leading asymptotics. -/
  layer : ∀ ε : ℝ, 0 < ε → ∀ᶠ S : ℝ in atTop, ‖b S - c * ((S ^ lam : ℝ) : ℂ)‖ ≤ ε * S ^ lam
  /-- Polynomial growth on the axis. -/
  growth : ∃ (C : ℝ) (Mg : ℕ), 0 < C ∧ ∀ᶠ S : ℝ in atTop, ‖b S‖ ≤ C * S ^ Mg
  /-- Polynomial growth of the reciprocal on the axis. -/
  growth_inv : ∃ (C : ℝ) (Mg : ℕ), 0 < C ∧ ∀ᶠ S : ℝ in atTop, ‖(b S)⁻¹‖ ≤ C * S ^ Mg

/-- **The directional survival bound over a power-Poincaré coefficient field.**  A finite family of
power-Poincaré coefficients sharing the greatest growth exponent forces the phase-jet family of the
phase polynomial to survive at that exponent. -/
theorem exists_phase_jet_survival_of_powerPoincare {Kn N : ℕ} {lam : ℝ} (l : Fin N → ℤ)
    (hl : Function.Injective l) (b : Fin Kn → Fin N → ℝ → ℂ) (c : Fin Kn → Fin N → ℂ)
    (hc : c ≠ 0) (ω a : ℝ → ℂ) (hω : ∀ S, ‖ω S‖ = 1) (ha : ∀ S, ‖a S‖ = 1)
    (hlayer : ∀ k i, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ S : ℝ in atTop, ‖b k i S - c k i * ((S ^ lam : ℝ) : ℂ)‖ ≤ ε * S ^ lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop,
      C * S ^ lam ≤ ‖fun p : Fin Kn × Fin N =>
        (ω S) ^ (p.1 : ℕ) * ∑ i, (l i : ℂ) ^ (p.2 : ℕ) * (b p.1 i S * (a S) ^ (l i))‖ := by
  refine exists_phase_jet_survival l hl b c hc ω a hω ha ?_
  intro ε hε
  have hall : ∀ k : Fin Kn, ∀ᶠ S : ℝ in atTop, ∀ i : Fin N,
      ‖b k i S - c k i * ((S ^ lam : ℝ) : ℂ)‖ ≤ ε * S ^ lam := by
    intro k
    exact Filter.eventually_all.mpr fun i => hlayer k i ε hε
  exact Filter.eventually_all.mpr hall

/-- **The terminal rational character rank is at most one.**  The character group of the terminal
carrier is the rank-one lattice generated by the recurrent frequency. -/
theorem rank_span_singleton_le_one (β : ℝ) :
    Module.rank ℤ (Submodule.span ℤ ({β} : Set ℝ)) ≤ 1 := by
  have h := rank_span_le ({β} : Set ℝ) (R := ℤ)
  simpa using h

/-- The terminal rank vanishes exactly when the recurrent frequency does. -/
theorem span_singleton_eq_bot_iff (β : ℝ) :
    Submodule.span ℤ ({β} : Set ℝ) = ⊥ ↔ β = 0 := by
  rw [Submodule.span_singleton_eq_bot]

end GaloisForLFunctions.HTGeometry
