/-
# The Steinhaus Jensen floor: large-prime energy bounds the credited ceiling

The log-mean-credited ceiling (`ZetaOffLineFirstMomentMollifierCredit`) bounds the off-line first
moment of `ζ` by `½ log(mean square of ζΨ) − (log-mean of Ψ)`. In the Steinhaus model this
quantity has a floor that no choice of mollifier can beat: with `E_r(z) = ∏_j (1 - r_j z_j)⁻¹`
the random Euler product on `k₀ + m` phases and `Ψ` any continuous function of the first `k₀`
phases,

  `2 J_ε(Ψ) + Σ_{j ≥ k₀} log (1 - r_j²)⁻¹ ≤ log (E‖E_r Ψ‖² + ε² B² ∏_{j ≥ k₀} (1 - r_j²)⁻¹)`

(`torusJensenFloor`), where `J_ε(Ψ) = E ½ log max(‖Ψ‖², ε²)` and `B = ∏_{j<k₀} (1 - r_j)⁻¹`.
Ingredients: the torus mean square factorizes over the large coordinates with the Poisson integral
`⨍ ‖1 - r z‖⁻² = (1 - r²)⁻¹` (`torusAverage_normSq_eulerAmp_restrict`), Jensen for the torus
average (`torusAverage_log_max_le`), and the corpus identity `E log‖E_r‖ = 0`
(`torusAverage_log_norm_eulerProduct`). The clamp `safeCircle` provides a globally continuous copy
of the Euler amplitude so that the torus-average calculus (linearity, monotonicity, continuity of
parametric circle integrals) applies.

With `r_j = p_j^{-1/2}`: for every mollifier of the primes `≤ M = T^θ`, half the log of the
mollified mean square minus the mollifier's Jensen mass is at least half the large-prime energy
`Σ_{M < p ≤ T} log (1 - 1/p)⁻¹ ≈ log (1/θ)`, with equality iff `|ζ_{≤M} Ψ|` is a.s. constant. The
credited ceiling therefore reaches `(L)` only as `θ → 1`.
-/
import GaloisForLFunctions.RHTower.SteinhausTorusLogMean
import GaloisForLFunctions.Bottcher.PoissonBoundary

open Real Complex

namespace RHTower

noncomputable section

/-- Joint continuity of `Fin.snoc` in the pair (prefix, last coordinate). -/
theorem continuous_finSnoc {k : ℕ} :
    Continuous (fun p : (Fin k → ℂ) × ℂ => (Fin.snoc p.1 p.2 : Fin (k + 1) → ℂ)) := by
  refine continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
    exact continuous_snd
  · simp only [Fin.snoc_castSucc]
    exact (continuous_apply i).comp continuous_fst

/-- Continuity of a slice `w ↦ F (Fin.snoc z w)`. -/
theorem continuous_snocSlice {k : ℕ} {F : (Fin (k + 1) → ℂ) → ℝ} (hF : Continuous F)
    (z : Fin k → ℂ) : Continuous (fun w : ℂ => F (Fin.snoc z w)) :=
  hF.comp (continuous_finSnoc.comp (continuous_const.prodMk continuous_id))

theorem circleIntegrable_snocSlice {k : ℕ} {F : (Fin (k + 1) → ℂ) → ℝ} (hF : Continuous F)
    (z : Fin k → ℂ) : CircleIntegrable (fun w : ℂ => F (Fin.snoc z w)) 0 1 :=
  ((continuous_snocSlice hF z).continuousOn).circleIntegrable zero_le_one

/-- Continuity of the averaged slice `z ↦ ⨍ F (Fin.snoc z ·)` (continuity of parametric
integrals). -/
theorem continuous_torusSlice {k : ℕ} {F : (Fin (k + 1) → ℂ) → ℝ} (hF : Continuous F) :
    Continuous (fun z : Fin k → ℂ => circleAverage (fun w => F (Fin.snoc z w)) 0 1) := by
  have hint : Continuous (fun z : Fin k → ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), F (Fin.snoc z (circleMap 0 1 θ))) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (z : Fin k → ℂ) (θ : ℝ) => F (Fin.snoc z (circleMap 0 1 θ))) ?_ continuous_const
    exact hF.comp (continuous_finSnoc.comp
      (continuous_fst.prodMk ((continuous_circleMap 0 1).comp continuous_snd)))
  simp only [Real.circleAverage_def]
  exact hint.const_smul ((2 * Real.pi)⁻¹ : ℝ)

theorem torusAverage_const' {k : ℕ} (c : ℝ) : torusAverage k (fun _ => c) = c := by
  induction k with
  | zero => simp [torusAverage]
  | succ k ih =>
    simp only [torusAverage, Real.circleAverage_const]
    exact ih

theorem torusAverage_add' {k : ℕ} {F G : (Fin k → ℂ) → ℝ} (hF : Continuous F)
    (hG : Continuous G) :
    torusAverage k (fun z => F z + G z) = torusAverage k F + torusAverage k G := by
  induction k with
  | zero => simp [torusAverage]
  | succ k ih =>
    simp only [torusAverage]
    have h : (fun z : Fin k → ℂ =>
        circleAverage (fun w => F (Fin.snoc z w) + G (Fin.snoc z w)) 0 1)
        = fun z => circleAverage (fun w => F (Fin.snoc z w)) 0 1
            + circleAverage (fun w => G (Fin.snoc z w)) 0 1 := by
      funext z
      exact Real.circleAverage_fun_add (circleIntegrable_snocSlice hF z)
        (circleIntegrable_snocSlice hG z)
    rw [h]
    exact ih (continuous_torusSlice hF) (continuous_torusSlice hG)

theorem torusAverage_mul_const' {k : ℕ} {F : (Fin k → ℂ) → ℝ} (c : ℝ) :
    torusAverage k (fun z => c * F z) = c * torusAverage k F := by
  induction k with
  | zero => simp [torusAverage]
  | succ k ih =>
    simp only [torusAverage]
    have h : (fun z : Fin k → ℂ => circleAverage (fun w => c * F (Fin.snoc z w)) 0 1)
        = fun z => c * circleAverage (fun w => F (Fin.snoc z w)) 0 1 := by
      funext z
      have : (fun w => c * F (Fin.snoc z w)) = c • (fun w => F (Fin.snoc z w)) := by
        funext w; simp [smul_eq_mul]
      rw [this, Real.circleAverage_smul, smul_eq_mul]
    rw [h]
    exact ih

/-- Monotonicity of the torus average for continuous functions ordered on the torus. -/
theorem torusAverage_mono' {k : ℕ} {F G : (Fin k → ℂ) → ℝ} (hF : Continuous F)
    (hG : Continuous G) (h : ∀ z, OnTorus z → F z ≤ G z) :
    torusAverage k F ≤ torusAverage k G := by
  induction k with
  | zero =>
    simp only [torusAverage]
    exact h _ (fun j => Fin.elim0 j)
  | succ k ih =>
    simp only [torusAverage]
    refine ih (continuous_torusSlice hF) (continuous_torusSlice hG) ?_
    intro z hz
    have hsub : circleAverage (fun w => F (Fin.snoc z w) - G (Fin.snoc z w)) 0 1 ≤ 0 := by
      refine Real.circleAverage_mono_on_of_le_circle ?_ ?_
      · exact ((continuous_snocSlice hF z).sub (continuous_snocSlice hG z)).continuousOn
          |>.circleIntegrable zero_le_one
      · intro w hw
        have hw1 : ‖w‖ = 1 := by simpa using hw
        have := h _ (onTorus_snoc hz hw1)
        linarith
    have hsplit : circleAverage (fun w => F (Fin.snoc z w) - G (Fin.snoc z w)) 0 1
        = circleAverage (fun w => F (Fin.snoc z w)) 0 1
          - circleAverage (fun w => G (Fin.snoc z w)) 0 1 := by
      have : (fun w => F (Fin.snoc z w) - G (Fin.snoc z w))
          = (fun w => F (Fin.snoc z w)) - (fun w => G (Fin.snoc z w)) := by
        funext w; simp
      rw [this]
      exact Real.circleAverage_sub (circleIntegrable_snocSlice hF z)
        (circleIntegrable_snocSlice hG z)
    linarith

/-- On the unit circle, `‖1 - r z‖ = ‖z - r‖` for real `r`. -/
theorem norm_one_sub_mul_eq_norm_sub {z : ℂ} (hz : ‖z‖ = 1) (r : ℝ) :
    ‖1 - (r : ℂ) * z‖ = ‖z - (r : ℂ)‖ := by
  have hzz : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    simp
  have hfac : z - (r : ℂ) = z * (1 - (r : ℂ) * (starRingEnd ℂ) z) := by
    calc z - (r : ℂ) = z - (r : ℂ) * (z * (starRingEnd ℂ) z) := by rw [hzz, mul_one]
      _ = z * (1 - (r : ℂ) * (starRingEnd ℂ) z) := by ring
  rw [hfac, norm_mul, hz, one_mul]
  have hconj : (starRingEnd ℂ) (1 - (r : ℂ) * z) = 1 - (r : ℂ) * (starRingEnd ℂ) z := by
    simp [map_sub, map_mul, Complex.conj_ofReal]
  rw [← hconj, Complex.norm_conj]

/-- **The Poisson integral of one Euler factor.** For `0 ≤ r < 1`,
`⨍_{|z|=1} ‖1 - r z‖⁻² = (1 - r²)⁻¹`. -/
theorem circleAverage_inv_normSq_one_sub_mul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleAverage (fun z : ℂ => (‖1 - (r : ℂ) * z‖ ^ 2)⁻¹) 0 1 = (1 - r ^ 2)⁻¹ := by
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have hball : (r : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hcongr : circleAverage (fun z : ℂ => (‖1 - (r : ℂ) * z‖ ^ 2)⁻¹) 0 1
      = circleAverage ((1 - r ^ 2)⁻¹ • poissonKernel 0 (r : ℂ)) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    simp only [Pi.smul_apply, smul_eq_mul, poissonKernel, sub_zero]
    rw [norm_one_sub_mul_eq_norm_sub hz1, hz1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    have hne : ‖z - (r : ℂ)‖ ^ 2 ≠ 0 := by
      have : z - (r : ℂ) ≠ 0 := by
        intro h
        have := congrArg norm h
        rw [sub_eq_zero] at h
        rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at hz1
        linarith
      positivity
    field_simp
  rw [hcongr, Real.circleAverage_smul, Bottcher.poissonKernel_circleAverage_eq_one hball, smul_eq_mul,
    mul_one]

/-! ## The safe amplitude: a globally continuous copy of the Euler amplitude on the torus -/

/-- Radial clamp: `w ↦ w / max(‖w‖, 1)`; the identity on the unit circle, of norm `≤ 1`. -/
def safeCircle (w : ℂ) : ℂ := w / ((max ‖w‖ 1 : ℝ) : ℂ)

theorem norm_safeCircle_le_one (w : ℂ) : ‖safeCircle w‖ ≤ 1 := by
  unfold safeCircle
  have hpos : 0 < max ‖w‖ 1 := lt_max_of_lt_right one_pos
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  exact div_le_one_of_le₀ (le_max_left _ _) hpos.le

theorem safeCircle_eq_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) : safeCircle w = w := by
  unfold safeCircle
  rw [hw, max_self]
  simp

theorem continuous_safeCircle : Continuous safeCircle := by
  unfold safeCircle
  refine continuous_id.div₀ (Complex.continuous_ofReal.comp (continuous_norm.max continuous_const))
    ?_
  intro w
  exact Complex.ofReal_ne_zero.mpr (lt_max_of_lt_right one_pos).ne'

/-- The Euler amplitude `∏_j (1 - r_j z_j)⁻¹` on the `k`-torus. -/
def eulerAmp {k : ℕ} (r : Fin k → ℝ) (z : Fin k → ℂ) : ℂ := ∏ j, (1 - (r j : ℂ) * z j)⁻¹

/-- The clamped Euler amplitude: equals `eulerAmp` on the torus, continuous and nonvanishing
everywhere. -/
def eulerAmpSafe {k : ℕ} (r : Fin k → ℝ) (z : Fin k → ℂ) : ℂ :=
  ∏ j, (1 - (r j : ℂ) * safeCircle (z j))⁻¹

theorem eulerAmpSafe_eq_of_onTorus {k : ℕ} (r : Fin k → ℝ) {z : Fin k → ℂ} (hz : OnTorus z) :
    eulerAmpSafe r z = eulerAmp r z := by
  unfold eulerAmpSafe eulerAmp
  exact Finset.prod_congr rfl (fun j _ => by rw [safeCircle_eq_of_norm_one (hz j)])

theorem one_sub_le_norm_one_sub_mul {r : ℝ} (hr0 : 0 ≤ r) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    1 - r ≤ ‖1 - (r : ℂ) * s‖ := by
  have h := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * s)
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at h
  have := mul_le_mul_of_nonneg_left hs hr0
  linarith

theorem one_sub_mul_safeCircle_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (w : ℂ) :
    1 - (r : ℂ) * safeCircle w ≠ 0 := by
  intro h0
  have := one_sub_le_norm_one_sub_mul hr0 (norm_safeCircle_le_one w)
  rw [h0, norm_zero] at this
  linarith

theorem continuous_eulerAmpSafe {k : ℕ} (r : Fin k → ℝ) (hr0 : ∀ j, 0 ≤ r j)
    (hr1 : ∀ j, r j < 1) : Continuous (eulerAmpSafe r) := by
  unfold eulerAmpSafe
  refine continuous_finsetProd _ (fun j _ => ?_)
  refine Continuous.inv₀ (continuous_const.sub
    (continuous_const.mul (continuous_safeCircle.comp (continuous_apply j)))) ?_
  intro z
  exact one_sub_mul_safeCircle_ne_zero (hr0 j) (hr1 j) (z j)

theorem eulerAmpSafe_ne_zero {k : ℕ} (r : Fin k → ℝ) (hr0 : ∀ j, 0 ≤ r j)
    (hr1 : ∀ j, r j < 1) (z : Fin k → ℂ) : eulerAmpSafe r z ≠ 0 := by
  unfold eulerAmpSafe
  refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
  exact inv_ne_zero (one_sub_mul_safeCircle_ne_zero (hr0 j) (hr1 j) (z j))

theorem norm_eulerAmpSafe_le {k : ℕ} (r : Fin k → ℝ) (hr0 : ∀ j, 0 ≤ r j)
    (hr1 : ∀ j, r j < 1) (z : Fin k → ℂ) :
    ‖eulerAmpSafe r z‖ ≤ ∏ j, (1 - r j)⁻¹ := by
  unfold eulerAmpSafe
  rw [norm_prod]
  refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
  rw [norm_inv]
  exact inv_anti₀ (by linarith [hr1 j])
    (one_sub_le_norm_one_sub_mul (hr0 j) (norm_safeCircle_le_one (z j)))

/-! ## Factorization over the last coordinates -/

/-- Restriction of a point of the `k`-torus to its first `k₀` coordinates. -/
def restrictFin {k₀ k : ℕ} (h : k₀ ≤ k) (z : Fin k → ℂ) : Fin k₀ → ℂ :=
  fun i => z (Fin.castLE h i)

/-- The radii of the first `k₀` coordinates. -/
def headRadii {k₀ m : ℕ} (r : Fin (k₀ + m) → ℝ) : Fin k₀ → ℝ :=
  fun i => r (Fin.castLE (Nat.le_add_right k₀ m) i)

/-- The mean-square energy of the last `m` coordinates: `∏ (1 - r_j²)⁻¹`. -/
def tailEnergy {k₀ m : ℕ} (r : Fin (k₀ + m) → ℝ) : ℝ :=
  ∏ j : Fin m, (1 - (r (Fin.natAdd k₀ j)) ^ 2)⁻¹

theorem eulerAmp_snoc {k : ℕ} (r : Fin (k + 1) → ℝ) (z : Fin k → ℂ) (w : ℂ) :
    eulerAmp r (Fin.snoc z w)
      = eulerAmp (fun j => r (Fin.castSucc j)) z * (1 - (r (Fin.last k) : ℂ) * w)⁻¹ := by
  unfold eulerAmp
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem restrictFin_snoc {k₀ m : ℕ} (z : Fin (k₀ + m) → ℂ) (w : ℂ) :
    restrictFin (Nat.le_add_right k₀ (m + 1)) (Fin.snoc z w : Fin (k₀ + m + 1) → ℂ)
      = restrictFin (Nat.le_add_right k₀ m) z := by
  funext i
  simp only [restrictFin]
  have : Fin.castLE (Nat.le_add_right k₀ (m + 1)) i
      = Fin.castSucc (Fin.castLE (Nat.le_add_right k₀ m) i) := by
    apply Fin.ext
    simp
  rw [this, Fin.snoc_castSucc]

theorem headRadii_castSucc {k₀ m : ℕ} (r : Fin (k₀ + (m + 1)) → ℝ) :
    headRadii (fun j : Fin (k₀ + m) => r (Fin.castSucc j)) = headRadii r := by
  funext i
  rfl

theorem tailEnergy_succ {k₀ m : ℕ} (r : Fin (k₀ + (m + 1)) → ℝ) :
    tailEnergy r
      = tailEnergy (fun j : Fin (k₀ + m) => r (Fin.castSucc j))
        * (1 - (r (Fin.last (k₀ + m))) ^ 2)⁻¹ := by
  unfold tailEnergy
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.natAdd_castSucc, Fin.natAdd_last]

theorem restrictFin_zero {k₀ : ℕ} (z : Fin (k₀ + 0) → ℂ) :
    restrictFin (Nat.le_add_right k₀ 0) z = z := by
  funext i
  rfl

theorem headRadii_zero {k₀ : ℕ} (r : Fin (k₀ + 0) → ℝ) : headRadii r = r := by
  funext i
  rfl

/-- **Factorization over the large coordinates.** The torus mean square of `E_r · Ψ∘restrict`
is the mean square over the first `k₀` coordinates times the tail energy `∏ (1 - r_j²)⁻¹`. -/
theorem torusAverage_normSq_eulerAmp_restrict {k₀ : ℕ} (Ψ : (Fin k₀ → ℂ) → ℂ) :
    ∀ (m : ℕ) (r : Fin (k₀ + m) → ℝ), (∀ j, 0 ≤ r j) → (∀ j, r j < 1) →
      torusAverage (k₀ + m)
          (fun z => ‖eulerAmp r z * Ψ (restrictFin (Nat.le_add_right k₀ m) z)‖ ^ 2)
        = torusAverage k₀ (fun z => ‖eulerAmp (headRadii r) z * Ψ z‖ ^ 2) * tailEnergy r := by
  intro m
  induction m with
  | zero =>
    intro r _ _
    have hP : tailEnergy r = 1 := by
      unfold tailEnergy
      simp
    rw [hP, mul_one, headRadii_zero]
    rfl
  | succ m ih =>
    intro r hr0 hr1
    show torusAverage (k₀ + m + 1) _ = _
    simp only [torusAverage]
    have hinner : (fun z : Fin (k₀ + m) → ℂ =>
        circleAverage (fun w => ‖eulerAmp r (Fin.snoc z w)
          * Ψ (restrictFin (Nat.le_add_right k₀ (m + 1)) (Fin.snoc z w))‖ ^ 2) 0 1)
        = fun z => (1 - (r (Fin.last (k₀ + m))) ^ 2)⁻¹ *
            ‖eulerAmp (fun j : Fin (k₀ + m) => r (Fin.castSucc j)) z
              * Ψ (restrictFin (Nat.le_add_right k₀ m) z)‖ ^ 2 := by
      funext z
      have hfun : (fun w : ℂ => ‖eulerAmp r (Fin.snoc z w)
            * Ψ (restrictFin (Nat.le_add_right k₀ (m + 1)) (Fin.snoc z w))‖ ^ 2)
          = (‖eulerAmp (fun j : Fin (k₀ + m) => r (Fin.castSucc j)) z
              * Ψ (restrictFin (Nat.le_add_right k₀ m) z)‖ ^ 2)
            • (fun w : ℂ => (‖1 - (r (Fin.last (k₀ + m)) : ℂ) * w‖ ^ 2)⁻¹) := by
        funext w
        rw [eulerAmp_snoc (k := k₀ + m), restrictFin_snoc]
        simp only [Pi.smul_apply, smul_eq_mul]
        have hcomm : ∀ (a b c : ℂ), a * b⁻¹ * c = (a * c) * b⁻¹ := fun a b c => by ring
        rw [hcomm, norm_mul, norm_inv, mul_pow, inv_pow]
      rw [hfun, Real.circleAverage_smul,
        circleAverage_inv_normSq_one_sub_mul (hr0 _) (hr1 _), smul_eq_mul, mul_comm]
    have hmc := torusAverage_mul_const' (k := k₀ + m)
      (F := fun z => ‖eulerAmp (fun j : Fin (k₀ + m) => r (Fin.castSucc j)) z
        * Ψ (restrictFin (Nat.le_add_right k₀ m) z)‖ ^ 2) ((1 - (r (Fin.last (k₀ + m))) ^ 2)⁻¹)
    rw [hinner]
    refine hmc.trans ?_
    rw [ih (fun j : Fin (k₀ + m) => r (Fin.castSucc j)) (fun j => hr0 _) (fun j => hr1 _),
      headRadii_castSucc, tailEnergy_succ]
    ring

/-! ## Jensen on the torus -/

theorem torusAverage_nonneg' {k : ℕ} {F : (Fin k → ℂ) → ℝ} (hF : Continuous F)
    (h0 : ∀ z, OnTorus z → 0 ≤ F z) : 0 ≤ torusAverage k F := by
  have := torusAverage_mono' continuous_const hF h0
  rwa [torusAverage_const'] at this

/-- **Jensen for the torus average.** `E log max(F, c) ≤ log (E F + c)` for continuous `F ≥ 0`
on the torus and `c > 0`. -/
theorem torusAverage_log_max_le {k : ℕ} {F : (Fin k → ℂ) → ℝ} (hF : Continuous F)
    (h0 : ∀ z, OnTorus z → 0 ≤ F z) {c : ℝ} (hc : 0 < c) :
    torusAverage k (fun z => Real.log (max (F z) c)) ≤ Real.log (torusAverage k F + c) := by
  set m : ℝ := torusAverage k F + c with hm
  have hm0 : 0 < m := by
    have := torusAverage_nonneg' hF h0
    linarith
  have hpt : ∀ z, OnTorus z →
      Real.log (max (F z) c) ≤ m⁻¹ * F z + (Real.log m + m⁻¹ * (c - m)) := by
    intro z hz
    have hFz := h0 z hz
    have hmax : max (F z) c ≤ F z + c := max_le (by linarith) (by linarith)
    have hpos : 0 < max (F z) c := lt_max_of_lt_right hc
    have h1 : Real.log (max (F z) c) ≤ Real.log (F z + c) := Real.log_le_log hpos hmax
    have h2 : Real.log ((F z + c) / m) ≤ (F z + c) / m - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (by linarith) hm0)
    rw [Real.log_div (by linarith) hm0.ne'] at h2
    calc Real.log (max (F z) c) ≤ Real.log (F z + c) := h1
      _ ≤ Real.log m + ((F z + c) / m - 1) := by linarith
      _ = m⁻¹ * F z + (Real.log m + m⁻¹ * (c - m)) := by field_simp; ring
  have hcont1 : Continuous (fun z => Real.log (max (F z) c)) :=
    (hF.max continuous_const).log (fun z => (lt_max_of_lt_right hc).ne')
  have hcont2 : Continuous (fun z => m⁻¹ * F z + (Real.log m + m⁻¹ * (c - m))) :=
    (continuous_const.mul hF).add continuous_const
  have hmono := torusAverage_mono' hcont1 hcont2 hpt
  rw [torusAverage_add' (F := fun z => m⁻¹ * F z) (G := fun _ => Real.log m + m⁻¹ * (c - m))
    (continuous_const.mul hF) continuous_const, torusAverage_mul_const' (F := F) m⁻¹,
    torusAverage_const'] at hmono
  have hzero : m⁻¹ * torusAverage k F + (Real.log m + m⁻¹ * (c - m)) = Real.log m := by
    rw [hm]
    field_simp
    ring
  linarith

/-! ## The floor -/

/-- **The Steinhaus Jensen floor.** For any continuous `Ψ` of the first `k₀` phases, any radii
`0 ≤ r_j < 1` on `k₀ + m` phases, and any truncation `ε > 0`:

`2 J_ε(Ψ) + Σ_{j ≥ k₀} log (1 - r_j²)⁻¹ ≤ log (E‖E_r Ψ‖² + ε² B² ∏_{j ≥ k₀}(1 - r_j²)⁻¹)`,

where `J_ε(Ψ) = E ½ log max(‖Ψ‖², ε²)` is the truncated torus Jensen mass and
`B = ∏_{j < k₀} (1 - r_j)⁻¹`. With `r_j = p_j^{-1/2}` this says that half the log of the mollified
mean square minus the mollifier's Jensen mass is at least half the large-prime energy
`Σ_{p > M} log (1 - 1/p)⁻¹`, for every mollifier of the primes `≤ M`. -/
theorem torusJensenFloor {k₀ : ℕ} (Ψ : (Fin k₀ → ℂ) → ℂ) (hΨ : Continuous Ψ) (m : ℕ)
    (r : Fin (k₀ + m) → ℝ) (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j < 1) {ε : ℝ} (hε : 0 < ε) :
    2 * torusAverage k₀ (fun z => (1 / 2) * Real.log (max (‖Ψ z‖ ^ 2) (ε ^ 2)))
      + ∑ j : Fin m, Real.log ((1 - (r (Fin.natAdd k₀ j)) ^ 2)⁻¹)
    ≤ Real.log (torusAverage (k₀ + m)
          (fun z => ‖eulerAmp r z * Ψ (restrictFin (Nat.le_add_right k₀ m) z)‖ ^ 2)
        + ε ^ 2 * (∏ i, (1 - headRadii r i)⁻¹) ^ 2 * tailEnergy r) := by
  have hr₀0 : ∀ i, 0 ≤ headRadii r i := fun i => hr0 _
  have hr₀1 : ∀ i, headRadii r i < 1 := fun i => hr1 _
  set B : ℝ := ∏ i, (1 - headRadii r i)⁻¹ with hB
  set A : ℝ := torusAverage k₀ (fun z => ‖eulerAmp (headRadii r) z * Ψ z‖ ^ 2) with hA
  have hfac : torusAverage (k₀ + m)
      (fun z => ‖eulerAmp r z * Ψ (restrictFin (Nat.le_add_right k₀ m) z)‖ ^ 2)
      = A * tailEnergy r := torusAverage_normSq_eulerAmp_restrict Ψ m r hr0 hr1
  have hfactor : ∀ j : Fin m, 0 < (1 - (r (Fin.natAdd k₀ j)) ^ 2)⁻¹ := fun j =>
    inv_pos.mpr (by nlinarith [hr0 (Fin.natAdd k₀ j), hr1 (Fin.natAdd k₀ j)])
  have hPpos : 0 < tailEnergy r := Finset.prod_pos (fun j _ => hfactor j)
  have hBpos : 0 < B := Finset.prod_pos (fun i _ => inv_pos.mpr (by linarith [hr₀1 i]))
  have hE : Continuous (eulerAmpSafe (headRadii r)) := continuous_eulerAmpSafe _ hr₀0 hr₀1
  have hEne : ∀ z, eulerAmpSafe (headRadii r) z ≠ 0 := eulerAmpSafe_ne_zero _ hr₀0 hr₀1
  have hEle : ∀ z, ‖eulerAmpSafe (headRadii r) z‖ ≤ B := norm_eulerAmpSafe_le _ hr₀0 hr₀1
  have hAsafe : torusAverage k₀ (fun z => ‖eulerAmpSafe (headRadii r) z * Ψ z‖ ^ 2) = A := by
    rw [hA]
    apply torusAverage_congr
    intro z hz
    rw [eulerAmpSafe_eq_of_onTorus _ hz]
  have hcontEΨ : Continuous (fun z => ‖eulerAmpSafe (headRadii r) z * Ψ z‖ ^ 2) :=
    (hE.mul hΨ).norm.pow 2
  have hA0 : 0 ≤ A := by
    rw [← hAsafe]
    exact torusAverage_nonneg' hcontEΨ (fun z _ => by positivity)
  have hlogE : torusAverage k₀ (fun z => Real.log (‖eulerAmpSafe (headRadii r) z‖ ^ 2)) = 0 := by
    have h1 : (fun z => Real.log (‖eulerAmpSafe (headRadii r) z‖ ^ 2))
        = fun z => 2 * Real.log ‖eulerAmpSafe (headRadii r) z‖ := by
      funext z
      rw [Real.log_pow]
      push_cast
      ring
    rw [h1, torusAverage_mul_const' (F := fun z => Real.log ‖eulerAmpSafe (headRadii r) z‖) 2]
    have h2 : torusAverage k₀ (fun z => Real.log ‖eulerAmpSafe (headRadii r) z‖)
        = torusAverage k₀ (fun z => Real.log ‖∏ j, (1 - (headRadii r j : ℂ) * z j)⁻¹‖) := by
      apply torusAverage_congr
      intro z hz
      rw [eulerAmpSafe_eq_of_onTorus _ hz]
      rfl
    rw [h2, torusAverage_log_norm_eulerProduct _ hr₀0 hr₀1, mul_zero]
  have hJ : 2 * torusAverage k₀ (fun z => (1 / 2) * Real.log (max (‖Ψ z‖ ^ 2) (ε ^ 2)))
      = torusAverage k₀ (fun z => Real.log (max (‖Ψ z‖ ^ 2) (ε ^ 2))) := by
    rw [torusAverage_mul_const' (F := fun z => Real.log (max (‖Ψ z‖ ^ 2) (ε ^ 2))) (1 / 2)]
    ring
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hcontJ : Continuous (fun z => Real.log (max (‖Ψ z‖ ^ 2) (ε ^ 2))) :=
    ((hΨ.norm.pow 2).max continuous_const).log (fun z => (lt_max_of_lt_right hε2).ne')
  have hcontE : Continuous (fun z => Real.log (‖eulerAmpSafe (headRadii r) z‖ ^ 2)) :=
    (hE.norm.pow 2).log (fun z => (pow_pos (norm_pos_iff.mpr (hEne z)) 2).ne')
  have hεB : (0 : ℝ) < ε ^ 2 * B ^ 2 := by positivity
  have hstep : torusAverage k₀ (fun z => Real.log (max (‖Ψ z‖ ^ 2) (ε ^ 2)))
      ≤ torusAverage k₀ (fun z =>
          Real.log (max (‖eulerAmpSafe (headRadii r) z * Ψ z‖ ^ 2) (ε ^ 2 * B ^ 2))) := by
    have hsum : torusAverage k₀ (fun z => Real.log (‖eulerAmpSafe (headRadii r) z‖ ^ 2)
          + Real.log (max (‖Ψ z‖ ^ 2) (ε ^ 2)))
        = torusAverage k₀ (fun z => Real.log (max (‖Ψ z‖ ^ 2) (ε ^ 2))) := by
      rw [torusAverage_add' hcontE hcontJ, hlogE, zero_add]
    rw [← hsum]
    refine torusAverage_mono' (hcontE.add hcontJ)
      ((hcontEΨ.max continuous_const).log (fun z => (lt_max_of_lt_right hεB).ne')) ?_
    intro z _
    have hE2 : 0 < ‖eulerAmpSafe (headRadii r) z‖ ^ 2 := pow_pos (norm_pos_iff.mpr (hEne z)) 2
    rw [← Real.log_mul hE2.ne' (lt_max_of_lt_right hε2).ne']
    apply Real.log_le_log (by positivity)
    rw [mul_max_of_nonneg _ _ hE2.le, norm_mul, mul_pow]
    apply max_le_max le_rfl
    calc ‖eulerAmpSafe (headRadii r) z‖ ^ 2 * ε ^ 2 ≤ B ^ 2 * ε ^ 2 := by
          gcongr
          exact hEle z
      _ = ε ^ 2 * B ^ 2 := by ring
  have hjen := torusAverage_log_max_le hcontEΨ (fun z _ => by positivity) hεB
  rw [hAsafe] at hjen
  have hlogP : Real.log (tailEnergy r)
      = ∑ j : Fin m, Real.log ((1 - (r (Fin.natAdd k₀ j)) ^ 2)⁻¹) := by
    unfold tailEnergy
    exact Real.log_prod (fun j _ => (hfactor j).ne')
  have hRHS : Real.log (A * tailEnergy r + ε ^ 2 * B ^ 2 * tailEnergy r)
      = Real.log (A + ε ^ 2 * B ^ 2) + Real.log (tailEnergy r) := by
    rw [← Real.log_mul (by positivity) hPpos.ne']
    congr 1
    ring
  rw [hfac, hRHS, hJ, hlogP]
  linarith [hstep, hjen]

end

end RHTower
