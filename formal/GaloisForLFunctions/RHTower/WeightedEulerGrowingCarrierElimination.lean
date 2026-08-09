import GaloisForLFunctions.RHTower.WeightedEulerAnnihilatorOversamplingCarrierEliminationUniversalityLaw
import GaloisForLFunctions.RHTower.GrowingOrderPrimeLogNodes
import GaloisForLFunctions.RHTower.WeightedEulerLambertWindowDerivatives
import GaloisForLFunctions.HTGeometry.SampledRayRateTransferGrowingHalfplane

/-!
# Growing-order carrier elimination for the weighted-Euler graph

The fixed-order oversampling law caps its ray rate at `min σ (α/2)`, and on a nonempty carrier the
strip walls force `α ≤ β`, so its separation hypothesis `β < min σ (α/2)` has no instance.  The
growing derivative order `⌊cR⌋ + 1` removes the cap: the interpolation loss is `6c` with `c` free,
so the ray rate can be pushed to any `σ' < σ`, and the separation hypothesis becomes `β < σ`.

* `compactFourierBorel_eq_zero_of_lambert_ray_decay` — the carrier-elimination core with the ray
  rate abstract;
* `norm_le_ray_of_primeLog_sampled_decay_growing_halfplane` — the growing-order prime-log
  oversampling for a half-plane analytic function, which is what the Lambert transform is;
* **`compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_growing`** — the resulting law,
  whose rate hypothesis `β < σ` is satisfiable.
-/

noncomputable section

namespace RHTower

open Complex Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- **Carrier elimination from a Lambert ray bound.**  If the compact-carrier Lambert transform
decays along the positive ray at a rate strictly beyond the carrier's upper wall, the whole
Fourier--Borel transform and every coordinate-power value vanish. -/
theorem compactFourierBorel_eq_zero_of_lambert_ray_decay
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) {α β κ C' R₁ : ℝ}
    (hα : 0 < α) (hκ : 0 < κ)
    (hstrip : ∀ k, α ≤ (s k).re ∧ (s k).re ≤ β)
    (hβκ : β < κ)
    (hray : ∀ x : ℝ, R₁ ≤ x →
      ‖compactCarrierLambertTransform L s (x : ℂ)‖ ≤ C' * Real.exp (-(κ * x))) :
    (∀ z : ℂ, compactFourierBorel L s z = 0) ∧
      ∀ m : ℕ, L (s ^ m) = 0 := by
  let D : ℝ := max C' 0
  have hD : 0 ≤ D := le_max_right _ _
  let R : ℝ := max (max R₁ 0) (Real.log 2 / κ)
  have hR0 : 0 < R := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    exact lt_of_lt_of_le (div_pos hlog2 hκ) (le_max_right _ _)
  have htail : ∀ x : ℝ, R ≤ x →
      ‖compactFourierBorel L s (x : ℂ)‖
        ≤ 4 * D * Real.exp (-(κ * x)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hR0 hx
    set ρ : ℝ := Real.exp (-(κ * x)) with hρ
    have hρ0 : 0 ≤ ρ := Real.exp_nonneg _
    have hρ1 : ρ < 1 := by
      rw [hρ, Real.exp_lt_one_iff]
      nlinarith [mul_pos hκ hx0]
    have hρhalf : ρ ≤ 1 / 2 := by
      rw [hρ]
      have hxlog : Real.log 2 / κ ≤ x :=
        le_trans (le_max_right _ _) hx
      have hlog : Real.log 2 ≤ κ * x := by
        rw [div_le_iff₀ hκ] at hxlog
        simpa [mul_comm] using hxlog
      calc
        Real.exp (-(κ * x)) ≤ Real.exp (-(Real.log 2)) :=
          Real.exp_le_exp.2 (by linarith)
        _ = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log two_pos]
          norm_num
    have hq : ∀ n : ℕ+,
        ‖compactExponentialTest s ((n : ℂ) * (x : ℂ))‖ < 1 := by
      intro n
      have hnpos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.prop
      apply norm_compactExponentialTest_lt_one_of_re_pos s _
        ((n : ℝ) * (α * x))
      · positivity
      · intro k
        have hcast :
            (n : ℂ) * (x : ℂ) = (((n : ℝ) * x : ℝ) : ℂ) := by
          norm_cast
        calc
          (n : ℝ) * (α * x)
              ≤ (n : ℝ) * (x * (s k).re) := by
                apply mul_le_mul_of_nonneg_left _ hnpos.le
                nlinarith [mul_le_mul_of_nonneg_left (hstrip k).1 hx0.le]
          _ = (((n : ℂ) * (x : ℂ)) * s k).re := by
                rw [hcast]
                simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
                ring
    have hFB : ∀ n : ℕ+,
        ‖compactFourierBorel L s ((n : ℂ) * (x : ℂ))‖
          ≤ ‖L‖ * Real.exp (-(α * x)) ^ (n : ℕ) := by
      intro n
      have hnpos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.prop
      have hre : ∀ k,
          (n : ℝ) * (α * x) ≤
            (((n : ℂ) * (x : ℂ)) * s k).re := by
        intro k
        have hcast :
            (n : ℂ) * (x : ℂ) = (((n : ℝ) * x : ℝ) : ℂ) := by
          norm_cast
        calc
          (n : ℝ) * (α * x)
              ≤ (n : ℝ) * (x * (s k).re) := by
                apply mul_le_mul_of_nonneg_left _ hnpos.le
                nlinarith [mul_le_mul_of_nonneg_left (hstrip k).1 hx0.le]
          _ = (((n : ℂ) * (x : ℂ)) * s k).re := by
                rw [hcast]
                simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
                ring
      have htest := norm_compactExponentialTest_le_exp_neg_of_re s
        ((n : ℂ) * (x : ℂ)) ((n : ℝ) * (α * x)) hre
      calc
        ‖compactFourierBorel L s ((n : ℂ) * (x : ℂ))‖
            ≤ ‖L‖ * ‖compactExponentialTest s ((n : ℂ) * (x : ℂ))‖ :=
          L.le_opNorm _
        _ ≤ ‖L‖ * Real.exp (-((n : ℝ) * (α * x))) := by gcongr
        _ = ‖L‖ * Real.exp (-(α * x)) ^ (n : ℕ) := by
          congr 1
          rw [show -((n : ℝ) * (α * x)) =
              (n : ℕ) * (-(α * x)) by ring, Real.exp_nat_mul]
    have hlam : ∀ n : ℕ+,
        ‖compactCarrierLambertTransform L s ((n : ℂ) * (x : ℂ))‖
          ≤ D * ρ ^ (n : ℕ) := by
      intro n
      have hn1 : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.prop
      have hyR₁ : R₁ ≤ (n : ℝ) * x := by
        have hxR₁ : R₁ ≤ x :=
          le_trans (le_trans (le_max_left R₁ 0) (le_max_left _ _)) hx
        nlinarith
      have hcast :
          (n : ℂ) * (x : ℂ) = (((n : ℝ) * x : ℝ) : ℂ) := by
        norm_cast
      rw [hcast]
      calc
        ‖compactCarrierLambertTransform L s (((n : ℝ) * x : ℝ) : ℂ)‖
            ≤ C' * Real.exp (-(κ * ((n : ℝ) * x))) :=
          hray ((n : ℝ) * x) hyR₁
        _ ≤ D * Real.exp (-(κ * ((n : ℝ) * x))) := by
          exact mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.exp_nonneg _)
        _ = D * ρ ^ (n : ℕ) := by
          congr 1
          rw [hρ, show -(κ * ((n : ℝ) * x)) =
              (n : ℕ) * (-(κ * x)) by ring,
            Real.exp_nat_mul]
    have hrecover := norm_compactFourierBorel_le_of_sampled_lambert_decay
      L s (x : ℂ) hq (norm_nonneg L) (Real.exp_nonneg _)
      (by rw [Real.exp_lt_one_iff]; nlinarith [mul_pos hα hx0])
      hFB hD hρ0 hρhalf hlam
    simpa [hρ] using hrecover
  let B : ℝ := max (4 * D) (‖L‖ * Real.exp ((‖s‖ + κ) * R))
  have hdecay : ∀ x : ℝ, 0 ≤ x →
      ‖compactFourierBorel L s (x : ℂ)‖
        ≤ B * Real.exp (-(κ * x)) := by
    intro x hx
    by_cases hRx : R ≤ x
    · exact (htail x hRx).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.exp_nonneg _))
    · have hxR : x ≤ R := le_of_not_ge hRx
      have hbasic := norm_compactFourierBorel_le_exp L s (x : ℂ)
      have hnormx : ‖(x : ℂ)‖ = x := by
        rw [Complex.norm_real, Real.norm_of_nonneg hx]
      rw [hnormx] at hbasic
      calc
        ‖compactFourierBorel L s (x : ℂ)‖
            ≤ ‖L‖ * Real.exp (‖s‖ * x) := hbasic
        _ = (‖L‖ * Real.exp ((‖s‖ + κ) * x)) *
              Real.exp (-(κ * x)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ ≤ (‖L‖ * Real.exp ((‖s‖ + κ) * R)) *
              Real.exp (-(κ * x)) := by
          gcongr
        _ ≤ B * Real.exp (-(κ * x)) := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.exp_nonneg _)
  have hzero : ∀ z : ℂ, compactFourierBorel L s z = 0 :=
    compactFourierBorel_eq_zero_of_ray_decay L s hβκ
      (fun k => (hstrip k).2) hdecay
  exact ⟨hzero, fun m =>
    map_coordinate_pow_eq_zero_of_fourierBorel_zero L s hzero m⟩


/-- **Growing-order prime-log oversampling for a half-plane analytic function.** -/
theorem norm_le_ray_of_primeLog_sampled_decay_growing_halfplane
    {T : ℝ} {H : ℂ → ℂ} (hH : ∀ t : ℝ, T < t → AnalyticAt ℂ H (t : ℂ))
    {R₀ δ K c σ C σ' : ℝ} (hTR₀ : T < R₀)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hc : 0 < c) (hC : 0 ≤ C)
    (hσ0 : 0 ≤ σ) (hσ'0 : 0 ≤ σ') (hσ' : σ' + 6 * c ≤ σ)
    (hder : ∀ R : ℝ, R₀ ≤ R → ∀ x ∈ Set.Icc R (R + 1),
      ‖iteratedDeriv (⌊c * R⌋₊ + 1) H (x : ℂ)‖ ≤ K * Real.exp (-(δ * R)))
    (hsamp : ∀ p : ℕ, p.Prime →
      ‖H (Real.log p : ℂ)‖ ≤ C * Real.exp (-(σ * Real.log p))) :
    ∃ C' R₁ : ℝ, ∀ x : ℝ, R₁ ≤ x →
      ‖H (x : ℂ)‖ ≤ C' * Real.exp (-(σ' * x)) := by
  obtain ⟨Rn, hRn⟩ := exists_separated_primeLog_nodes_growing hc
  refine HTGeometry.norm_le_ray_of_sampled_decay_halfplane (R₀ := max R₀ Rn) hH
    (lt_of_lt_of_le hTR₀ (le_max_left _ _)) hδ hK hc hC hσ'0 hσ' ?_ ?_
  · intro R hR
    exact hder R (le_trans (le_max_left _ _) hR)
  · intro R hR
    obtain ⟨s, hcard, hsub, hsep, hlog⟩ :=
      hRn R (le_trans (le_max_right _ _) hR)
    refine ⟨s, hcard, hsub, hsep, fun t ht => ?_⟩
    obtain ⟨p, hp, rfl⟩ := hlog t ht
    have h2 : R ≤ Real.log p := (hsub ht).1
    have h3 : Real.exp (-(σ * Real.log p)) ≤ Real.exp (-(σ * R)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left h2 hσ0
      linarith
    calc ‖H (Real.log p : ℂ)‖
        ≤ C * Real.exp (-(σ * Real.log p)) := hsamp p hp
      _ ≤ C * Real.exp (-(σ * R)) := mul_le_mul_of_nonneg_left h3 hC

/-- The compact-carrier Lambert transform is analytic at every positive real point of a carrier
with positive real-part floor: there the exponential test is contractive. -/
theorem compactCarrierLambertTransform_analyticAt_pos
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) {α : ℝ} (hα : 0 < α)
    (hre : ∀ k, α ≤ (s k).re) {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℂ (compactCarrierLambertTransform L s) (t : ℂ) := by
  refine compactCarrierLambertTransform_analyticAt L s _ ?_
  refine norm_compactExponentialTest_lt_one_of_re_pos s (t : ℂ) (t * α) (by positivity) ?_
  intro k
  have hcalc : ((t : ℂ) * s k).re = t * (s k).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [hcalc]
  exact mul_le_mul_of_nonneg_left (hre k) ht.le

/-- **Growing-order weighted-Euler carrier elimination.**  The growing derivative order removes the
`α/2` cap of the fixed-order law, so the separation hypothesis is the satisfiable `β < σ`: choosing
the node density `c` below both `α/(8M)` and `(σ − β)/12` pushes the ray rate `σ − 6c` past the
carrier's upper wall. -/
theorem compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_growing
    [Nonempty K] (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) (lam : ℕ → ℂ)
    {α β σ C : ℝ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hstrip : ∀ k, α ≤ (s k).re ∧ (s k).re ≤ β)
    (hβσ : β < σ)
    (hgraph : ∀ p : ℕ, p.Prime →
      lam p + L (compactPrimeEulerUnitTangent s p) = 0)
    (hdual : ∀ p : ℕ, p.Prime →
      ‖lam p‖ ≤ C * Real.log p * (p : ℝ) ^ (-σ)) :
    (∀ z : ℂ, compactFourierBorel L s z = 0) ∧
      ∀ m : ℕ, L (s ^ m) = 0 := by
  classical
  let k₀ : K := Classical.choice inferInstance
  have hαβ : α ≤ β := (hstrip k₀).1.trans (hstrip k₀).2
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hσ0 : 0 < σ := lt_trans hβ0 hβσ
  set M : ℝ := max α ‖s‖ with hM
  have hαM : α ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le hα hαM
  have hnorm : ∀ k, ‖s k‖ ≤ M := fun k =>
    le_trans (s.norm_coe_le_norm k) (le_max_right _ _)
  -- prime-log samples of the Lambert transform
  have hsamp : ∀ p : ℕ, p.Prime →
      ‖compactCarrierLambertTransform L s (Real.log p : ℂ)‖
        ≤ C * Real.exp (-(σ * Real.log p)) := by
    intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    calc
      ‖compactCarrierLambertTransform L s (Real.log p : ℂ)‖
          ≤ C * (p : ℝ) ^ (-σ) :=
        norm_lambert_primeLog_le_of_graph_annihilation L s hp.two_le
          (hgraph p hp) (hdual p hp)
      _ = C * Real.exp (-(σ * Real.log p)) := by
        rw [Real.rpow_def_of_pos hpR]
        congr 2
        ring
  -- the node density
  set c : ℝ := min (α / (8 * M)) ((σ - β) / 12) with hc
  have hc0 : 0 < c := by
    refine lt_min (by positivity) ?_
    have : 0 < σ - β := by linarith
    positivity
  have hcα : c ≤ α / (8 * M) := min_le_left _ _
  have hcσ : c ≤ (σ - β) / 12 := min_le_right _ _
  set σ' : ℝ := σ - 6 * c with hσ'
  have hβσ' : β < σ' := by
    have : 6 * c ≤ (σ - β) / 2 := by linarith
    rw [hσ']
    linarith
  have hσ'0 : 0 ≤ σ' := le_of_lt (lt_trans hβ0 hβσ')
  -- the growing-order window derivative bound
  set R₀ : ℝ := max (8 * M / α) (2 * Real.log 2 / α) with hR₀
  have hR₀0 : 0 < R₀ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hder := lambert_derivative_window_bound L s hα hαM
    (fun k => (hstrip k).1) hnorm hc0 hcα
  -- the half-plane analyticity
  have hH : ∀ t : ℝ, (0 : ℝ) < t →
      AnalyticAt ℂ (compactCarrierLambertTransform L s) (t : ℂ) := fun t ht =>
    compactCarrierLambertTransform_analyticAt_pos L s hα (fun k => (hstrip k).1) ht
  obtain ⟨C', R₁, hray⟩ :=
    norm_le_ray_of_primeLog_sampled_decay_growing_halfplane (T := 0) (R₀ := R₀) hH
      hR₀0 (by positivity : (0:ℝ) < α / 2) (by positivity : (0:ℝ) ≤ 4 * ‖L‖)
      hc0 hC hσ0.le hσ'0 (by rw [hσ']; linarith)
      (fun R hR x hx => hder R hR x hx) hsamp
  exact compactFourierBorel_eq_zero_of_lambert_ray_decay L s hα
    (lt_of_le_of_lt hβ0.le hβσ') hstrip hβσ' hray

/-- **Critical-boundary carrier elimination.**  At the critical dual rate `σ = 1` the growing-order
law applies to every carrier compactly contained in `Re s < 1`, which is exactly the geometry of the
weighted-Euler graph annihilator: the `T₁`/`M₀` dual bound gives Lambert samples decaying like
`C/p`. -/
theorem compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_critical
    [Nonempty K] (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) (lam : ℕ → ℂ)
    {α β C : ℝ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hstrip : ∀ k, α ≤ (s k).re ∧ (s k).re ≤ β)
    (hβ1 : β < 1)
    (hgraph : ∀ p : ℕ, p.Prime →
      lam p + L (compactPrimeEulerUnitTangent s p) = 0)
    (hdual : ∀ p : ℕ, p.Prime →
      ‖lam p‖ ≤ C * criticalNorm (primeCoordinateField p)) :
    (∀ z : ℂ, compactFourierBorel L s z = 0) ∧
      ∀ m : ℕ, L (s ^ m) = 0 := by
  refine compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_growing
    L s lam hα hC hstrip hβ1 hgraph ?_
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc ‖lam p‖ ≤ C * criticalNorm (primeCoordinateField p) := hdual p hp
    _ = C * Real.log p * ((p : ℝ)) ^ (-(1 : ℝ)) := by
        rw [criticalNorm_coordinate hp, Real.rpow_neg_one]
        ring

end RHTower
