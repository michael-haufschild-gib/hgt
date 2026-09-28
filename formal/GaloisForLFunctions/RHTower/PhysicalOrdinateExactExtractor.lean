import GaloisForLFunctions.RHTower.PhysicalOrdinateTransportNoGo
import GaloisForLFunctions.HTGeometry.WeightedDirichletZeroCount
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators

/-!
# The exact singular source-to-seam transport

Write `y_{σ,γ} = x_{σ,-γ}`, so `y_{σ,γ}(n) = μ(n) √(prob_σ(n)) n^{iγ}`.  For a bounded
`T : ℓ²(ℕ) → ℓ²(P)` the `p`-coordinate of `T y_{σ,γ}` is the Dirichlet readout
`Σ_n μ(n) √(prob_σ(n)) (T δ_n)(p) n^{iγ}`, absolutely convergent with weight `n^η` for
`η < (σ-1)/2`, hence holomorphic in a half-plane.

* **Rigidity.**  If `T y_{σ,γ} = v_{β,γ}` for all `γ` in a nonempty open interval, then on every
  squarefree coordinate `T` is the prime extraction
  `(D_{σ,β} f)(p) = m_{σ,β}(p) f(p)`, `m_{σ,β}(p) = -√Q(σ) log p p^{(σ-1)/2}(p^{-β} - p^{β-1})` **(5)**.
* `D_{σ,β}` is bounded exactly when `1 < σ < 1 + 2 min(β, 1-β)` **(6)**; then `D_{σ,β} y_{σ,γ} = v_{β,γ}`
  at every height, and the least norm of an exact landing is `‖D_{σ,β}‖ = sup_p |m_{σ,β}(p)|` **(7)**.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

local notation "ℓ²ℕ" => lp (fun _ : ℕ => ℂ) 2
local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-! ### Coordinates of a bounded map -/

/-- The evaluation of `ℓ²(P)` at a prime. -/
def primeEval (p : Nat.Primes) : ℓ²P →L[ℂ] ℂ := innerSL ℂ (lp.single 2 p (1 : ℂ))

theorem primeEval_apply (p : Nat.Primes) (f : ℓ²P) : primeEval p f = (f : Nat.Primes → ℂ) p := by
  classical
  simp [primeEval, innerSL_apply_apply, lp.inner_single_left]

/-- **Coordinate expansion.**  `(T f)(p) = Σ_n f(n) (T δ_n)(p)`. -/
theorem hasSum_coord (T : ℓ²ℕ →L[ℂ] ℓ²P) (f : ℓ²ℕ) (p : Nat.Primes) :
    HasSum (fun n => (f : ℕ → ℂ) n * (T (lp.single 2 n 1) : Nat.Primes → ℂ) p)
      ((T f : Nat.Primes → ℂ) p) := by
  classical
  have h2 := ((lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) f).mapL T).mapL
    (primeEval p)
  rw [primeEval_apply] at h2
  refine h2.congr_fun fun n => ?_
  have hs : lp.single (E := fun _ : ℕ => ℂ) 2 n ((f : ℕ → ℂ) n) =
      (f : ℕ → ℂ) n • lp.single (E := fun _ : ℕ => ℂ) 2 n 1 := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  change _ = primeEval p (T (lp.single 2 n ((f : ℕ → ℂ) n)))
  rw [hs, map_smul, map_smul, primeEval_apply, smul_eq_mul]

/-- The coordinates `(T δ_n)(p)` are square summable in `n`. -/
theorem summable_norm_sq_coord (T : ℓ²ℕ →L[ℂ] ℓ²P) (p : Nat.Primes) :
    Summable fun n => ‖(T (lp.single 2 n 1) : Nat.Primes → ℂ) p‖ ^ 2 := by
  classical
  refine (summable_norm_sq_lp (ContinuousLinearMap.adjoint T
    (lp.single 2 p (1 : ℂ)))).congr fun n => ?_
  have h1 : (T (lp.single 2 n 1) : Nat.Primes → ℂ) p =
      inner ℂ (lp.single 2 p (1 : ℂ)) (T (lp.single 2 n 1)) := by
    rw [lp.inner_single_left]; simp
  have h2 : inner ℂ (lp.single 2 p (1 : ℂ)) (T (lp.single 2 n 1)) =
      (starRingEnd ℂ) ((ContinuousLinearMap.adjoint T (lp.single 2 p (1 : ℂ)) : ℕ → ℂ) n) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm, lp.inner_single_left]; simp
  rw [h1, h2, Complex.norm_conj]

/-! ### Source coordinates and readouts -/

/-- The source weight `w_σ(n) = μ(n) √(prob_σ(n))`. -/
abbrev sourceWeight (σ : ℝ) (n : ℕ) : ℂ := infiniteMobiusSignedWeight σ n

theorem sourceWeight_zero (σ : ℝ) : sourceWeight σ 0 = 0 := by
  simp [sourceWeight, infiniteMobiusSignedWeight]

theorem ordinateSource_neg_apply {σ : ℝ} (hσ : 1 < σ) (γ : ℝ) (n : ℕ) :
    (ordinateSource σ (-γ) : ℕ → ℂ) n =
      GaloisForLFunctions.expChar (Real.log n) γ * sourceWeight σ n := by
  rw [ordinateSource_apply hσ, GaloisForLFunctions.expChar, GaloisForLFunctions.expChar]
  congr 2
  push_cast
  ring

theorem norm_sourceWeight_sq_le {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    ‖sourceWeight σ n‖ ^ 2 ≤ (n : ℝ) ^ (-σ) / squarefreeMobiusTotal σ := by
  rw [sourceWeight, norm_infiniteMobiusSignedWeight_sq hσ, squarefreeMobiusProbability]
  gcongr
  · exact (squarefreeMobiusTotal_pos hσ).le
  · rw [squarefreeMobiusMass]; split_ifs
    · exact le_rfl
    · positivity

/-- Weighted summability of source-weighted square-summable coefficients for `2η < σ - 1`. -/
theorem weightedAbsSummable_source_mul {σ η : ℝ} (hσ : 1 < σ)
    (hησ : 2 * η < σ - 1) {t : ℕ → ℂ} (ht : Summable fun n => ‖t n‖ ^ 2) :
    WeightedAbsSummable (fun n => sourceWeight σ n * t n) η := by
  have hQ := squarefreeMobiusTotal_pos hσ
  have hs : Summable fun n : ℕ => (n : ℝ) ^ (-σ + 2 * η) / squarefreeMobiusTotal σ := by
    have h1 : 1 < σ - 2 * η := by linarith
    refine ((Real.summable_nat_rpow_inv.mpr h1).div_const (squarefreeMobiusTotal σ)).congr
      fun n => ?_
    rw [← Real.rpow_neg (Nat.cast_nonneg n)]; ring_nf
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hs.add ht).div_const 2)
  rw [norm_mul]
  have hab : ‖sourceWeight σ n‖ * ‖t n‖ * (n : ℝ) ^ η ≤
      ((‖sourceWeight σ n‖ * (n : ℝ) ^ η) ^ 2 + ‖t n‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖sourceWeight σ n‖ * (n : ℝ) ^ η - ‖t n‖)]
  refine hab.trans ?_
  gcongr
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [sourceWeight_zero]; positivity
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ η), ← Real.rpow_mul hn0.le]
    calc ‖sourceWeight σ n‖ ^ 2 * (n : ℝ) ^ (η * ((2 : ℕ) : ℝ))
        ≤ (n : ℝ) ^ (-σ) / squarefreeMobiusTotal σ * (n : ℝ) ^ (η * ((2 : ℕ) : ℝ)) := by
          gcongr; exact norm_sourceWeight_sq_le hσ n
      _ = (n : ℝ) ^ (-σ + 2 * η) / squarefreeMobiusTotal σ := by
          rw [div_mul_eq_mul_div, ← Real.rpow_add hn0]; norm_num; ring_nf

/-- The readout coefficients of the `p`-coordinate of `T y_{σ,·}`. -/
def landingCoeff (σ : ℝ) (T : ℓ²ℕ →L[ℂ] ℓ²P) (p : Nat.Primes) (n : ℕ) : ℂ :=
  sourceWeight σ n * (T (lp.single 2 n 1) : Nat.Primes → ℂ) p

theorem weightedAbsSummable_landingCoeff {σ η : ℝ} (hσ : 1 < σ)
    (hησ : 2 * η < σ - 1) (T : ℓ²ℕ →L[ℂ] ℓ²P) (p : Nat.Primes) :
    WeightedAbsSummable (landingCoeff σ T p) η :=
  weightedAbsSummable_source_mul hσ hησ (summable_norm_sq_coord T p)

/-- **The `p`-coordinate of `T y_{σ,γ}` is a Dirichlet readout.** -/
theorem coord_landing_eq_readout {σ : ℝ} (hσ : 1 < σ) (T : ℓ²ℕ →L[ℂ] ℓ²P) (p : Nat.Primes)
    (γ : ℝ) : (T (ordinateSource σ (-γ)) : Nat.Primes → ℂ) p =
      dirichletReadout (landingCoeff σ T p) γ := by
  have hw := weightedAbsSummable_landingCoeff (η := 0) hσ (by linarith) T p
  rw [dirichletReadout_ofReal hw le_rfl, GaloisForLFunctions.expSeriesCarrier]
  have h := (hasSum_coord T (ordinateSource σ (-γ)) p)
  have hsumm := h.summable
  rw [← h.tsum_eq, hsumm.tsum_eq_zero_add]
  simp only [ordinateSource_neg_apply hσ, sourceWeight_zero, mul_zero, zero_mul, zero_add]
  refine tsum_congr fun m => ?_
  rw [landingCoeff]
  ring

/-! ### The seam coordinate as an entire readout -/

/-- The entire extension `b_β(p) p^{iz}` of the `p`-coordinate of the seam. -/
def seamCoordEntire (β : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  (seamAmplitude β p : ℂ) * Complex.exp (I * z * Real.log p)

theorem differentiable_seamCoordEntire (β : ℝ) (p : ℕ) : Differentiable ℂ (seamCoordEntire β p) :=
  fun z => by unfold seamCoordEntire; fun_prop

theorem seamCoordEntire_ofReal (β : ℝ) (p : ℕ) (t : ℝ) :
    seamCoordEntire β p t = (seamAmplitude β p : ℂ) * GaloisForLFunctions.expChar (Real.log p) t := by
  rw [seamCoordEntire, GaloisForLFunctions.expChar]
  congr 2
  push_cast
  ring

/-- The single-frequency coefficient sequence of the seam coordinate. -/
def seamCoeffSeq (β : ℝ) (p : ℕ) (n : ℕ) : ℂ := if n = p then (seamAmplitude β p : ℂ) else 0

theorem weightedAbsSummable_seamCoeffSeq (β : ℝ) (p : ℕ) (η : ℝ) :
    WeightedAbsSummable (seamCoeffSeq β p) η := by
  refine summable_of_ne_finset_zero (s := {p}) fun n hn => ?_
  rw [Finset.mem_singleton] at hn
  simp [seamCoeffSeq, hn]

theorem dirichletReadout_seamCoeffSeq {β : ℝ} {p : ℕ} (hp : 0 < p) (t : ℝ) :
    dirichletReadout (seamCoeffSeq β p) t = seamCoordEntire β p t := by
  rw [dirichletReadout_ofReal (weightedAbsSummable_seamCoeffSeq β p 0) le_rfl,
    GaloisForLFunctions.expSeriesCarrier, seamCoordEntire_ofReal]
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [tsum_eq_single k fun m hm => by
    simp only [seamCoeffSeq]; rw [if_neg (by omega), zero_mul]]
  simp [seamCoeffSeq]

/-! ### Rigidity -/

/-- The prime extraction multiplier `m_{σ,β}(p)` **(5)**. -/
def extractorMultiplier (σ β : ℝ) (p : ℕ) : ℝ :=
  -(Real.sqrt (squarefreeMobiusTotal σ) * Real.log p * (p : ℝ) ^ ((σ - 1) / 2) *
    ((p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1)))

theorem sourceWeight_prime {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) :
    sourceWeight σ p = -(((p : ℝ) ^ (-(σ / 2)) / Real.sqrt (squarefreeMobiusTotal σ) : ℝ) : ℂ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hQ := squarefreeMobiusTotal_pos hσ
  rw [sourceWeight, infiniteMobiusSignedWeight, ArithmeticFunction.moebius_apply_prime p.2,
    squarefreeMobiusProbability, squarefreeMobiusMass, if_pos p.2.squarefree,
    Real.sqrt_div (by positivity), show (p : ℝ) ^ (-σ) = ((p : ℝ) ^ (-(σ / 2))) ^ 2 by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; ring_nf,
    Real.sqrt_sq (by positivity)]
  push_cast
  ring

theorem extractorMultiplier_mul_sourceWeight {σ : ℝ} (hσ : 1 < σ) (β : ℝ) (p : Nat.Primes) :
    (extractorMultiplier σ β p : ℂ) * sourceWeight σ p = (seamAmplitude β p : ℂ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hQ := squarefreeMobiusTotal_pos hσ
  have hsQ : Real.sqrt (squarefreeMobiusTotal σ) ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  rw [sourceWeight_prime hσ]
  have hpow : (p : ℝ) ^ ((σ - 1) / 2) * (p : ℝ) ^ (-(σ / 2)) = 1 / Real.sqrt p := by
    rw [← Real.rpow_add hp0, Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hp0.le]; ring_nf
  rw [extractorMultiplier, seamAmplitude]
  have e : -(Real.sqrt (squarefreeMobiusTotal σ) * Real.log p * (p : ℝ) ^ ((σ - 1) / 2) *
      ((p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1))) *
      -((p : ℝ) ^ (-(σ / 2)) / Real.sqrt (squarefreeMobiusTotal σ)) =
      Real.log p / Real.sqrt p * ((p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1)) := by
    field_simp
    rw [show Real.log ↑↑p * ↑↑p ^ ((σ - 1) / 2) * (↑↑p ^ (-β) - ↑↑p ^ (β - 1)) * ↑↑p ^ (-(σ / 2)) =
      Real.log ↑↑p * (↑↑p ^ ((σ - 1) / 2) * ↑↑p ^ (-(σ / 2))) * (↑↑p ^ (-β) - ↑↑p ^ (β - 1)) by ring,
      hpow]
    field_simp
  rw [← e]
  push_cast
  ring

/-- **Rigidity of exact landing.**  If a bounded `T` satisfies `T y_{σ,γ} = v_{β,γ}` for all `γ` in a
nonempty open interval, then for every squarefree `n` and prime `p`,
`(T δ_n)(p) = m_{σ,β}(p)` if `n = p` and `0` otherwise. -/
theorem coord_eq_of_exact_landing {σ β : ℝ} (hσ : 1 < σ) (hβ : β ∈ Ioo 0 1)
    (T : ℓ²ℕ →L[ℂ] ℓ²P) {a b : ℝ} (hab : a < b)
    (hT : ∀ γ ∈ Ioo a b, T (ordinateSource σ (-γ)) = seamVector β hβ γ) (p : Nat.Primes)
    {n : ℕ} (hn : Squarefree n) :
    (T (lp.single 2 n 1) : Nat.Primes → ℂ) p =
      if n = p then (extractorMultiplier σ β p : ℂ) else 0 := by
  set η : ℝ := (σ - 1) / 4 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hw := weightedAbsSummable_landingCoeff (η := η) hσ (by rw [hηdef]; linarith) T p
  have hinterval : ∀ t ∈ Ioo a b, dirichletReadout (landingCoeff σ T p) t =
      seamCoordEntire β p t := by
    intro t ht
    rw [← coord_landing_eq_readout hσ T p t, hT t ht, seamVector_apply, seamCoordEntire_ofReal]
  have hline : ∀ t : ℝ, dirichletReadout (landingCoeff σ T p) t =
      dirichletReadout (seamCoeffSeq β p) t := by
    intro t
    rw [dirichletReadout_seamCoeffSeq p.2.pos]
    exact dirichletReadout_eq_of_eqOn_Ioo hw hη (differentiable_seamCoordEntire β p) hab
      hinterval (by simp; linarith)
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by subst h; exact not_squarefree_zero hn
  have hcoef := coeff_eq_of_dirichletReadout_eq hw (weightedAbsSummable_seamCoeffSeq β p η) hη.le
    hline hn0
  simp only [landingCoeff, seamCoeffSeq] at hcoef
  have hwn : sourceWeight σ n ≠ 0 := by
    intro h
    have := norm_infiniteMobiusSignedWeight_sq hσ n
    rw [show infiniteMobiusSignedWeight σ n = sourceWeight σ n from rfl, h, norm_zero] at this
    have hprob : 0 < squarefreeMobiusProbability σ n := by
      rw [squarefreeMobiusProbability, squarefreeMobiusMass, if_pos hn]
      exact div_pos (by positivity) (squarefreeMobiusTotal_pos hσ)
    nlinarith
  split_ifs at hcoef ⊢ with hnp
  · subst hnp
    have := extractorMultiplier_mul_sourceWeight hσ β p
    rw [← this, mul_comm] at hcoef
    exact mul_right_cancel₀ hwn hcoef
  · exact (mul_eq_zero.mp hcoef).resolve_left hwn

/-- An exact landing on an interval has norm at least `|m_{σ,β}(p)|` for every prime `p` **(7)**. -/
theorem abs_extractorMultiplier_le_norm {σ β : ℝ} (hσ : 1 < σ) (hβ : β ∈ Ioo 0 1)
    (T : ℓ²ℕ →L[ℂ] ℓ²P) {a b : ℝ} (hab : a < b)
    (hT : ∀ γ ∈ Ioo a b, T (ordinateSource σ (-γ)) = seamVector β hβ γ) (p : Nat.Primes) :
    |extractorMultiplier σ β p| ≤ ‖T‖ := by
  have h := coord_eq_of_exact_landing hσ hβ T hab hT p p.2.squarefree
  rw [if_pos rfl] at h
  set e : ℓ²ℕ := lp.single (E := fun _ : ℕ => ℂ) 2 (p : ℕ) 1 with he
  have he1 : ‖e‖ = 1 := by rw [he, lp.norm_single (by norm_num)]; simp
  have h1 : ‖(T e : Nat.Primes → ℂ) p‖ ≤ ‖T e‖ :=
    lp.norm_apply_le_norm (E := fun _ : Nat.Primes => ℂ) (p := 2) two_ne_zero (T e) p
  have h2 : ‖T e‖ ≤ ‖T‖ := by
    have := T.le_opNorm e
    rwa [he1, mul_one] at this
  have h3 : ‖(T e : Nat.Primes → ℂ) p‖ = |extractorMultiplier σ β p| := by
    rw [he, h, Complex.norm_real, Real.norm_eq_abs]
  rw [← h3]
  exact h1.trans h2

/-! ### The boundedness window (6) -/

theorem log_mul_rpow_neg_le_one_div {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    Real.log x * x ^ (-δ) ≤ 1 / δ := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_le_rpow_div hx0.le hδ
  have hpos : 0 < x ^ (-δ) := Real.rpow_pos_of_pos hx0 _
  calc Real.log x * x ^ (-δ) ≤ x ^ δ / δ * x ^ (-δ) := by gcongr
    _ = 1 / δ := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hx0]; simp

/-- `|m_{σ,β}(p)| = √Q(σ) · log p · p^{(σ-1)/2} |p^{-β} - p^{β-1}|`. -/
theorem abs_extractorMultiplier {σ β : ℝ} (p : ℕ) :
    |extractorMultiplier σ β p| = Real.sqrt (squarefreeMobiusTotal σ) *
      (Real.log p * (p : ℝ) ^ ((σ - 1) / 2) * |(p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1)|) := by
  rw [extractorMultiplier, abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.log_natCast_nonneg p), abs_of_nonneg (by positivity)]
  ring

/-- The profile `s_p(σ) = log p · p^{(σ-1)/2} |p^{-β} - p^{β-1}|`. -/
def seamLogProfile (σ β : ℝ) (p : ℕ) : ℝ :=
  Real.log p * (p : ℝ) ^ ((σ - 1) / 2) * |(p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1)|

theorem seamLogProfile_nonneg (σ β : ℝ) (p : ℕ) : 0 ≤ seamLogProfile σ β p := by
  unfold seamLogProfile
  have := Real.log_natCast_nonneg p
  positivity

theorem seamLogProfile_le {σ β : ℝ} {p : ℕ} (hp : 1 ≤ p) :
    seamLogProfile σ β p ≤ 2 * (Real.log p * (p : ℝ) ^ (-(min β (1 - β) - (σ - 1) / 2))) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have habs := abs_rpow_neg_sub_rpow_le (β := β) hp1
  unfold seamLogProfile
  have hlog := Real.log_nonneg hp1
  calc Real.log p * (p : ℝ) ^ ((σ - 1) / 2) * |(p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1)|
      ≤ Real.log p * (p : ℝ) ^ ((σ - 1) / 2) * (2 * (p : ℝ) ^ (-min β (1 - β))) := by gcongr
    _ = 2 * (Real.log p * ((p : ℝ) ^ ((σ - 1) / 2) * (p : ℝ) ^ (-min β (1 - β)))) := by ring
    _ = 2 * (Real.log p * (p : ℝ) ^ (-(min β (1 - β) - (σ - 1) / 2))) := by
        rw [← Real.rpow_add hp0]; ring_nf

theorem seamLogProfile_bound {σ β : ℝ}
    (hw : σ < 1 + 2 * min β (1 - β)) (p : ℕ) :
    seamLogProfile σ β p ≤ 2 / (min β (1 - β) - (σ - 1) / 2) := by
  have hδ : 0 < min β (1 - β) - (σ - 1) / 2 := by linarith
  rcases Nat.eq_zero_or_pos p with h0 | hpos
  · subst h0; simp [seamLogProfile]; exact div_nonneg (by norm_num) hδ.le
  · refine (seamLogProfile_le hpos).trans ?_
    have := log_mul_rpow_neg_le_one_div (x := p) (by exact_mod_cast hpos) hδ
    rw [div_eq_mul_one_div 2]
    linarith

/-- For large `p`, `|p^{-β} - p^{β-1}| ≥ p^{-κ}/2`, `κ = min(β, 1-β)`, when `β ≠ 1/2`. -/
theorem half_rpow_neg_le_abs {β : ℝ} (hβ2 : β ≠ 1 / 2) {x : ℝ}
    (hx : 2 ^ (1 / (1 - 2 * min β (1 - β))) ≤ x) :
    x ^ (-min β (1 - β)) / 2 ≤ |x ^ (-β) - x ^ (β - 1)| := by
  set κ := min β (1 - β) with hκ
  have hκlt : κ < 1 / 2 := by
    rcases lt_or_gt_of_ne hβ2 with h | h
    · exact lt_of_le_of_lt (min_le_left _ _) h
    · have : 1 - β < 1 / 2 := by linarith
      exact lt_of_le_of_lt (min_le_right _ _) this
  have hd : 0 < 1 - 2 * κ := by linarith
  have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow (by norm_num) (by positivity)) hx
  have hx0 : 0 < x := by linarith
  have hkey : 2 ≤ x ^ (1 - 2 * κ) := by
    calc (2 : ℝ) = (2 ^ (1 / (1 - 2 * κ))) ^ (1 - 2 * κ) := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ x ^ (1 - 2 * κ) := Real.rpow_le_rpow (by positivity) hx hd.le
  have hsmall : x ^ (-(1 - κ)) ≤ x ^ (-κ) / 2 := by
    have e : x ^ (-(1 - κ)) = x ^ (-κ) * (x ^ (1 - 2 * κ))⁻¹ := by
      rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]; ring_nf
    rw [e]
    have hpos : 0 < x ^ (-κ) := Real.rpow_pos_of_pos hx0 _
    rw [div_eq_mul_inv]
    gcongr
  have hB0 : 0 ≤ x ^ (-(1 - κ)) := (Real.rpow_pos_of_pos hx0 _).le
  rcases le_or_gt β (1 - β) with h | h
  · have hk : κ = β := min_eq_left h
    rw [hk] at hsmall hB0 ⊢
    rw [show β - 1 = -(1 - β) by ring]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hk : κ = 1 - β := min_eq_right h.le
    rw [hk] at hsmall hB0 ⊢
    rw [show -β = -(1 - (1 - β)) by ring, show β - 1 = -(1 - β) by ring]
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

/-- **(6)** `sup_p |m_{σ,β}(p)| < ∞` exactly when `σ < 1 + 2 min(β, 1-β)`. -/
theorem bddAbove_extractorMultiplier_iff {σ β : ℝ} (hσ : 1 < σ) (hβ2 : β ≠ 1 / 2) :
    BddAbove (range fun p : Nat.Primes => |extractorMultiplier σ β p|) ↔
      σ < 1 + 2 * min β (1 - β) := by
  have hQ := squarefreeMobiusTotal_pos hσ
  have hsQ : 0 < Real.sqrt (squarefreeMobiusTotal σ) := Real.sqrt_pos.mpr hQ
  constructor
  · intro hb
    by_contra hw
    push Not at hw
    obtain ⟨C, hC⟩ := hb
    set κ := min β (1 - β) with hκ
    set P₀ : ℝ := max (2 ^ (1 / (1 - 2 * κ))) (Real.exp (2 * |C| / Real.sqrt
      (squarefreeMobiusTotal σ) + 1)) with hP₀
    obtain ⟨p, hpP, hp⟩ := Nat.exists_infinite_primes (⌈P₀⌉₊ + 1)
    have hpP' : P₀ < p := by
      have := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hpP
      exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast this)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hmem := hC ⟨⟨p, hp⟩, rfl⟩
    simp only at hmem
    rw [abs_extractorMultiplier] at hmem
    have hlow := half_rpow_neg_le_abs hβ2 (x := p) (le_trans (le_max_left _ _) hpP'.le)
    have hexp : 1 ≤ (p : ℝ) ^ ((σ - 1) / 2 - κ) := Real.one_le_rpow hp1 (by linarith)
    have hlogbig : 2 * |C| / Real.sqrt (squarefreeMobiusTotal σ) + 1 < Real.log p := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      exact lt_of_le_of_lt (le_max_right _ _) hpP'
    have hp0 : (0 : ℝ) < p := by linarith
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have h1 : Real.log p / 2 ≤ Real.log p * (p : ℝ) ^ ((σ - 1) / 2) *
        |(p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1)| := by
      have e : (p : ℝ) ^ ((σ - 1) / 2) * ((p : ℝ) ^ (-κ) / 2) =
          (p : ℝ) ^ ((σ - 1) / 2 - κ) / 2 := by
        rw [mul_div_assoc', ← Real.rpow_add hp0]; ring_nf
      calc Real.log p / 2 ≤ Real.log p * ((p : ℝ) ^ ((σ - 1) / 2 - κ) / 2) := by nlinarith
        _ = Real.log p * ((p : ℝ) ^ ((σ - 1) / 2) * ((p : ℝ) ^ (-κ) / 2)) := by rw [e]
        _ ≤ _ := by rw [← mul_assoc]; gcongr
    have h2 : Real.sqrt (squarefreeMobiusTotal σ) * (Real.log p / 2) ≤ C :=
      le_trans (mul_le_mul_of_nonneg_left h1 hsQ.le) hmem
    have h3 : 2 * |C| / Real.sqrt (squarefreeMobiusTotal σ) < Real.log p := by linarith
    rw [div_lt_iff₀ hsQ] at h3
    nlinarith [le_abs_self C]
  · intro hw
    refine ⟨Real.sqrt (squarefreeMobiusTotal σ) * (2 / (min β (1 - β) - (σ - 1) / 2)), ?_⟩
    rintro _ ⟨p, rfl⟩
    simp only
    rw [abs_extractorMultiplier]
    exact mul_le_mul_of_nonneg_left (seamLogProfile_bound hw p) hsQ.le

/-! ### The extractor operator and its norm (7) -/

theorem memℓp_extractor {σ β : ℝ} {C : ℝ} (hC : ∀ p : Nat.Primes, |extractorMultiplier σ β p| ≤ C)
    (f : ℓ²ℕ) :
    Memℓp (fun p : Nat.Primes => (extractorMultiplier σ β p : ℂ) * (f : ℕ → ℂ) p) 2 := by
  refine HilbertSchmidt.memℓp_of_sq ?_
  have hf : Summable fun p : Nat.Primes => ‖(f : ℕ → ℂ) p‖ ^ 2 :=
    (summable_norm_sq_lp f).comp_injective Subtype.val_injective
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) (hf.mul_left (C ^ 2))
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsq : extractorMultiplier σ β p ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC p) 2
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- The prime extraction `D_{σ,β}` (given a bound on the multiplier). -/
def extractorOp {σ β C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ p : Nat.Primes, |extractorMultiplier σ β p| ≤ C) :
    ℓ²ℕ →L[ℂ] ℓ²P :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨_, memℓp_extractor hC f⟩
      map_add' := fun f g => by
        ext p
        simp only [lp.coeFn_add, Pi.add_apply]
        change _ = (extractorMultiplier σ β p : ℂ) * (f : ℕ → ℂ) p +
          (extractorMultiplier σ β p : ℂ) * (g : ℕ → ℂ) p
        ring
      map_smul' := fun c f => by
        ext p
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        change _ = c * ((extractorMultiplier σ β p : ℂ) * (f : ℕ → ℂ) p)
        ring }
    C fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have h2 : ‖(⟨_, memℓp_extractor hC f⟩ : ℓ²P)‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
        rw [HilbertSchmidt.lp_norm_sq_eq, mul_pow, HilbertSchmidt.lp_norm_sq_eq]
        have hf : Summable fun p : Nat.Primes => ‖(f : ℕ → ℂ) p‖ ^ 2 :=
          (summable_norm_sq_lp f).comp_injective Subtype.val_injective
        calc ∑' p : Nat.Primes, ‖(extractorMultiplier σ β p : ℂ) * (f : ℕ → ℂ) p‖ ^ 2
            ≤ ∑' p : Nat.Primes, C ^ 2 * ‖(f : ℕ → ℂ) p‖ ^ 2 := by
              refine Summable.tsum_le_tsum (fun p => ?_) ?_ (hf.mul_left _)
              · rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
                have hsq : extractorMultiplier σ β p ^ 2 ≤ C ^ 2 := by
                  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC p) 2
                exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
              · exact summable_norm_sq_lp (⟨_, memℓp_extractor hC f⟩ : ℓ²P)
          _ = C ^ 2 * ∑' p : Nat.Primes, ‖(f : ℕ → ℂ) p‖ ^ 2 := tsum_mul_left
          _ ≤ C ^ 2 * ∑' n : ℕ, ‖(f : ℕ → ℂ) n‖ ^ 2 := by
              gcongr
              exact hf.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
                (fun _ _ => by positivity) (fun _ => le_rfl) (summable_norm_sq_lp f)
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg f))).mp h2

theorem extractorOp_apply {σ β C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p : Nat.Primes, |extractorMultiplier σ β p| ≤ C) (f : ℓ²ℕ) (p : Nat.Primes) :
    (extractorOp hC0 hC f : Nat.Primes → ℂ) p = (extractorMultiplier σ β p : ℂ) * (f : ℕ → ℂ) p :=
  rfl

/-- **(5)** `D_{σ,β} y_{σ,γ} = v_{β,γ}` at every height. -/
theorem extractorOp_ordinateSource {σ β C : ℝ} (hσ : 1 < σ) (hβ : β ∈ Ioo 0 1) (hC0 : 0 ≤ C)
    (hC : ∀ p : Nat.Primes, |extractorMultiplier σ β p| ≤ C) (γ : ℝ) :
    extractorOp hC0 hC (ordinateSource σ (-γ)) = seamVector β hβ γ := by
  ext p
  rw [extractorOp_apply, ordinateSource_neg_apply hσ, seamVector_apply,
    ← extractorMultiplier_mul_sourceWeight hσ β p]
  ring

theorem abs_extractorMultiplier_le_norm_extractorOp {σ β C : ℝ} (hσ : 1 < σ)
    (hβ : β ∈ Ioo 0 1) (hC0 : 0 ≤ C) (hC : ∀ p : Nat.Primes, |extractorMultiplier σ β p| ≤ C)
    (p : Nat.Primes) : |extractorMultiplier σ β p| ≤ ‖extractorOp hC0 hC‖ :=
  abs_extractorMultiplier_le_norm hσ hβ (extractorOp hC0 hC) (a := 0) (b := 1) one_pos
    (fun γ _ => extractorOp_ordinateSource hσ hβ hC0 hC γ) p

theorem iSup_abs_extractorMultiplier_nonneg {σ β : ℝ}
    (hb : BddAbove (range fun p : Nat.Primes => |extractorMultiplier σ β p|)) :
    0 ≤ ⨆ p : Nat.Primes, |extractorMultiplier σ β p| :=
  (abs_nonneg (extractorMultiplier σ β 2)).trans
    (le_ciSup hb (⟨2, Nat.prime_two⟩ : Nat.Primes))

/-- **(7)** The least norm of an exact landing: `‖D_{σ,β}‖ = sup_p |m_{σ,β}(p)|`, and every exact
landing on an interval has norm at least this. -/
theorem norm_extractorOp {σ β : ℝ} (hσ : 1 < σ) (hβ : β ∈ Ioo 0 1)
    (hb : BddAbove (range fun p : Nat.Primes => |extractorMultiplier σ β p|)) :
    ‖extractorOp (iSup_abs_extractorMultiplier_nonneg hb) (fun p => (le_ciSup hb p :
        |extractorMultiplier σ β p| ≤ ⨆ q : Nat.Primes, |extractorMultiplier σ β q|))‖ =
      ⨆ p : Nat.Primes, |extractorMultiplier σ β p| := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (iSup_abs_extractorMultiplier_nonneg hb) _) ?_
  refine ciSup_le fun p => ?_
  exact abs_extractorMultiplier_le_norm_extractorOp hσ hβ _ _ p

/-- An exact bounded landing on an interval exists exactly in the window **(6)**. -/
theorem exists_exact_landing_iff {σ β : ℝ} (hσ : 1 < σ) (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2)
    {a b : ℝ} (hab : a < b) :
    (∃ T : ℓ²ℕ →L[ℂ] ℓ²P, ∀ γ ∈ Ioo a b, T (ordinateSource σ (-γ)) = seamVector β hβ γ) ↔
      σ < 1 + 2 * min β (1 - β) := by
  rw [← bddAbove_extractorMultiplier_iff hσ hβ2]
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨‖T‖, by rintro _ ⟨p, rfl⟩; exact abs_extractorMultiplier_le_norm hσ hβ T hab hT p⟩
  · intro hb
    exact ⟨extractorOp (iSup_abs_extractorMultiplier_nonneg hb)
      (fun p => (le_ciSup hb p :
        |extractorMultiplier σ β p| ≤ ⨆ q : Nat.Primes, |extractorMultiplier σ β q|)),
      fun γ _ => extractorOp_ordinateSource hσ hβ _ _ γ⟩

/-! ### The critical cost asymptotic (8) -/

/-- `C_β = sup_p log p |p^{-β} - p^{β-1}|`. -/
def seamLogConst (β : ℝ) : ℝ := ⨆ p : Nat.Primes, seamLogProfile 1 β p

theorem bddAbove_seamLogProfile {σ β : ℝ} (hw : σ < 1 + 2 * min β (1 - β)) :
    BddAbove (range fun p : Nat.Primes => seamLogProfile σ β p) :=
  ⟨2 / (min β (1 - β) - (σ - 1) / 2), by rintro _ ⟨p, rfl⟩; exact seamLogProfile_bound hw p⟩

theorem seamLogProfile_eq_mul (σ β : ℝ) (p : ℕ) :
    seamLogProfile σ β p = seamLogProfile 1 β p * (p : ℝ) ^ ((σ - 1) / 2) := by
  simp only [seamLogProfile, sub_self, zero_div, Real.rpow_zero, mul_one]; ring

theorem seamLogProfile_one_le {σ β : ℝ} (hσ : 1 ≤ σ) (p : ℕ) :
    seamLogProfile 1 β p ≤ seamLogProfile σ β p := by
  rw [seamLogProfile_eq_mul σ β p]
  rcases Nat.eq_zero_or_pos p with h0 | hpos
  · subst h0; simp [seamLogProfile]
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpos
    exact le_mul_of_one_le_right (seamLogProfile_nonneg _ _ _)
      (Real.one_le_rpow hp1 (by linarith))

theorem seamLogConst_nonneg {β : ℝ} (hβ : β ∈ Ioo 0 1) : 0 ≤ seamLogConst β :=
  (seamLogProfile_nonneg 1 β 2).trans (le_ciSup (bddAbove_seamLogProfile (by
    have := lt_min hβ.1 (by linarith [hβ.2] : (0 : ℝ) < 1 - β); linarith))
    (⟨2, Nat.prime_two⟩ : Nat.Primes))

/-- `sup_p s_p(σ) → C_β` as `σ ↓ 1`. -/
theorem tendsto_iSup_seamLogProfile {β : ℝ} (hβ : β ∈ Ioo 0 1) :
    Tendsto (fun σ => ⨆ p : Nat.Primes, seamLogProfile σ β p) (𝓝[>] 1) (𝓝 (seamLogConst β)) := by
  set κ := min β (1 - β) with hκ
  have hκpos : 0 < κ := lt_min hβ.1 (by linarith [hβ.2])
  have hC0 := seamLogConst_nonneg hβ
  have hwin : ∀ᶠ σ in 𝓝[>] (1 : ℝ), 1 < σ ∧ σ < 1 + κ := by
    have h1 : Iio (1 + κ) ∈ 𝓝[>] (1 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
    filter_upwards [self_mem_nhdsWithin, h1] with σ hσ h2 using ⟨hσ, h2⟩
  have hlow : ∀ᶠ σ in 𝓝[>] (1 : ℝ), seamLogConst β ≤ ⨆ p : Nat.Primes, seamLogProfile σ β p := by
    filter_upwards [hwin] with σ hσ
    refine ciSup_le fun p => (seamLogProfile_one_le hσ.1.le p).trans ?_
    exact le_ciSup (bddAbove_seamLogProfile (by linarith)) p
  rw [tendsto_order]
  refine ⟨fun a ha => hlow.mono fun σ h => lt_of_lt_of_le ha h, fun b hb => ?_⟩
  set ε : ℝ := (b - seamLogConst β) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  -- the tail threshold
  set P : ℝ := max 1 ((8 / (κ * ε)) ^ (4 / κ)) with hP
  have htail : ∀ x : ℝ, P ≤ x → ∀ σ, 1 < σ → σ < 1 + κ →
      2 * (Real.log x * x ^ (-(κ - (σ - 1) / 2))) ≤ ε := by
    intro x hx σ hσ1 hσ2
    have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
    have hx0 : 0 < x := by linarith
    have hlog : Real.log x ≤ x ^ (κ / 4) / (κ / 4) := Real.log_le_rpow_div hx0.le (by positivity)
    have hexp : x ^ (-(κ - (σ - 1) / 2)) ≤ x ^ (-(κ / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hbig : (8 / (κ * ε)) ^ (4 / κ) ≤ x := le_trans (le_max_right _ _) hx
    have hkey : x ^ (-(κ / 4)) ≤ κ * ε / 8 := by
      have h1 : (8 / (κ * ε)) ≤ x ^ (κ / 4) := by
        calc (8 / (κ * ε)) = ((8 / (κ * ε)) ^ (4 / κ)) ^ (κ / 4) := by
              rw [← Real.rpow_mul (by positivity), show 4 / κ * (κ / 4) = 1 by field_simp,
                Real.rpow_one]
          _ ≤ x ^ (κ / 4) := Real.rpow_le_rpow (by positivity) hbig (by positivity)
      rw [Real.rpow_neg hx0.le]
      have hpos : 0 < x ^ (κ / 4) := Real.rpow_pos_of_pos hx0 _
      rw [inv_le_comm₀ hpos (by positivity)]
      calc (κ * ε / 8)⁻¹ = 8 / (κ * ε) := by field_simp
        _ ≤ x ^ (κ / 4) := h1
    calc 2 * (Real.log x * x ^ (-(κ - (σ - 1) / 2)))
        ≤ 2 * (x ^ (κ / 4) / (κ / 4) * x ^ (-(κ / 2))) := by gcongr
      _ = 8 / κ * x ^ (-(κ / 4)) := by
          rw [div_mul_eq_mul_div, ← Real.rpow_add hx0]; field_simp; ring_nf
      _ ≤ 8 / κ * (κ * ε / 8) := by gcongr
      _ = ε := by field_simp
  have hPpow : Tendsto (fun σ : ℝ => P ^ ((σ - 1) / 2)) (𝓝[>] 1) (𝓝 1) := by
    have hc : ContinuousAt (fun σ : ℝ => P ^ ((σ - 1) / 2)) 1 :=
      (Real.continuousAt_const_rpow (by positivity)).comp (by fun_prop)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    simpa using this
  have hhead : ∀ᶠ σ in 𝓝[>] (1 : ℝ), seamLogConst β * P ^ ((σ - 1) / 2) ≤ seamLogConst β + ε := by
    have hlim : Tendsto (fun σ : ℝ => seamLogConst β * P ^ ((σ - 1) / 2)) (𝓝[>] 1)
        (𝓝 (seamLogConst β)) := by simpa using hPpow.const_mul (seamLogConst β)
    exact hlim.eventually (ge_mem_nhds (by linarith))
  filter_upwards [hwin, hhead] with σ hσ hh
  have hsup : (⨆ p : Nat.Primes, seamLogProfile σ β p) ≤ seamLogConst β + ε := by
    refine ciSup_le fun p => ?_
    by_cases hpP : P ≤ (p : ℝ)
    · have := htail p hpP σ hσ.1 hσ.2
      exact ((seamLogProfile_le (σ := σ) (β := β) p.2.one_le).trans this).trans (by linarith)
    · push Not at hpP
      rw [seamLogProfile_eq_mul]
      calc seamLogProfile 1 β p * (p : ℝ) ^ ((σ - 1) / 2)
          ≤ seamLogConst β * P ^ ((σ - 1) / 2) := by
            gcongr
            · exact le_ciSup (bddAbove_seamLogProfile (by linarith)) p
            · linarith [hσ.1]
        _ ≤ seamLogConst β + ε := hh
  rw [hε] at hsup
  linarith

/-- `M_{σ,β} = √Q(σ) · sup_p s_p(σ)`. -/
theorem iSup_abs_extractorMultiplier_eq (σ β : ℝ) :
    ⨆ p : Nat.Primes, |extractorMultiplier σ β p| =
      Real.sqrt (squarefreeMobiusTotal σ) * ⨆ p : Nat.Primes, seamLogProfile σ β p := by
  rw [Real.mul_iSup_of_nonneg (Real.sqrt_nonneg _)]
  exact iSup_congr fun p => abs_extractorMultiplier p

/-- **(8)** `√(σ-1) · M_{σ,β} → C_β / √ζ(2)`, `ζ(2) = π²/6`. -/
theorem tendsto_sqrt_mul_leastCost {β : ℝ} (hβ : β ∈ Ioo 0 1) :
    Tendsto (fun σ => Real.sqrt (σ - 1) * ⨆ p : Nat.Primes, |extractorMultiplier σ β p|)
      (𝓝[>] 1) (𝓝 (seamLogConst β / Real.sqrt (Real.pi ^ 2 / 6))) := by
  have hsq := (Real.continuous_sqrt.tendsto _).comp tendsto_sub_one_mul_squarefreeMobiusTotal
  have hprod := hsq.mul (tendsto_iSup_seamLogProfile hβ)
  have hval : Real.sqrt (6 / Real.pi ^ 2) * seamLogConst β =
      seamLogConst β / Real.sqrt (Real.pi ^ 2 / 6) := by
    rw [show (6 : ℝ) / Real.pi ^ 2 = (Real.pi ^ 2 / 6)⁻¹ by field_simp, Real.sqrt_inv]
    ring
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hs : (1 : ℝ) < σ := hσ
  simp only [Function.comp_apply]
  rw [iSup_abs_extractorMultiplier_eq, Real.sqrt_mul (by linarith)]
  ring

/-! ### Uniform approximate landing (9) -/

theorem continuous_dirichletReadout_ofReal {c : ℕ → ℂ} (hc : WeightedAbsSummable c 0) :
    Continuous fun t : ℝ => dirichletReadout c t := by
  have e := funext (dirichletReadout_ofReal hc le_rfl)
  rw [show (fun t : ℝ => dirichletReadout c t) = _ from e]
  exact GaloisForLFunctions.continuous_expSeriesCarrier
    ((summable_nat_add_iff 1).mpr (hc.summable_norm le_rfl)) _

theorem isBohrAlmostPeriodic_dirichletReadout {c : ℕ → ℂ} (hc : WeightedAbsSummable c 0) :
    HTGeometry.IsBohrAlmostPeriodic fun t : ℝ => dirichletReadout c t := by
  have e := funext (dirichletReadout_ofReal hc le_rfl)
  rw [show (fun t : ℝ => dirichletReadout c t) = _ from e]
  exact GaloisForLFunctions.isBohrAlmostPeriodic_expSeriesCarrier
    ((summable_nat_add_iff 1).mpr (hc.summable_norm le_rfl)) _

/-- **(9)** Uniform-in-height approximate landing still costs `√Q(σ) C_β`:
if `sup_γ ‖T_σ y_{σ,γ} - v_{β,γ}‖ ≤ ε(σ) → 0`, then `‖T_σ‖/√Q(σ) ≥ c` eventually, for every
`c < C_β`. -/
theorem eventually_le_norm_div_sqrt_of_uniform_landing {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (T : ℝ → ℓ²ℕ →L[ℂ] ℓ²P) (ε : ℝ → ℝ) (hε : Tendsto ε (𝓝[>] 1) (𝓝 0))
    (happrox : ∀ σ, 1 < σ → ∀ γ : ℝ,
      ‖T σ (ordinateSource σ (-γ)) - seamVector β hβ γ‖ ≤ ε σ)
    {c : ℝ} (hc : c < seamLogConst β) :
    ∀ᶠ σ in 𝓝[>] 1, c ≤ ‖T σ‖ / Real.sqrt (squarefreeMobiusTotal σ) := by
  have hbdd : BddAbove (range fun p : Nat.Primes => seamLogProfile 1 β p) :=
    bddAbove_seamLogProfile (by
      have := lt_min hβ.1 (by linarith [hβ.2] : (0 : ℝ) < 1 - β); linarith)
  obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hc
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hlim : Tendsto (fun σ => (p : ℝ) ^ (σ / 2) * ε σ) (𝓝[>] 1) (𝓝 ((p : ℝ) ^ ((1 : ℝ) / 2) * 0)) := by
    have hc1 : ContinuousAt (fun σ : ℝ => (p : ℝ) ^ (σ / 2)) 1 :=
      (Real.continuousAt_const_rpow hp0.ne').comp (by fun_prop)
    exact (hc1.tendsto.mono_left nhdsWithin_le_nhds).mul hε
  rw [mul_zero] at hlim
  have hgap : 0 < seamLogProfile 1 β p - c := by linarith
  filter_upwards [self_mem_nhdsWithin, hlim.eventually (gt_mem_nhds hgap)] with σ hσ hsmall
  have hs : (1 : ℝ) < σ := hσ
  have hQ := squarefreeMobiusTotal_pos hs
  have hsQ : 0 < Real.sqrt (squarefreeMobiusTotal σ) := Real.sqrt_pos.mpr hQ
  -- the two coordinate readouts
  have hwL := weightedAbsSummable_landingCoeff (η := 0) hs (by linarith) (T σ) p
  have hwS := weightedAbsSummable_seamCoeffSeq β p 0
  have hdiff : ∀ γ : ℝ, ‖dirichletReadout (landingCoeff σ (T σ) p) γ -
      dirichletReadout (seamCoeffSeq β p) γ‖ ≤ ε σ := by
    intro γ
    rw [← coord_landing_eq_readout hs, dirichletReadout_seamCoeffSeq p.2.pos,
      seamCoordEntire_ofReal, ← seamVector_apply hβ γ p, ← Pi.sub_apply, ← lp.coeFn_sub]
    exact (lp.norm_apply_le_norm (E := fun _ : Nat.Primes => ℂ) (p := 2) two_ne_zero _ p).trans
      (happrox σ hs γ)
  have hbohr := GaloisForLFunctions.norm_bohrCoefficient_sub_le
    (continuous_dirichletReadout_ofReal hwL) (isBohrAlmostPeriodic_dirichletReadout hwL)
    (continuous_dirichletReadout_ofReal hwS) (isBohrAlmostPeriodic_dirichletReadout hwS) hdiff
    (Real.log p)
  rw [bohrCoefficient_dirichletReadout hwL le_rfl p.2.pos,
    bohrCoefficient_dirichletReadout hwS le_rfl p.2.pos] at hbohr
  simp only [landingCoeff, seamCoeffSeq, if_true] at hbohr
  -- `|w(p)| = p^{-σ/2}/√Q` and `|t_pp| ≤ ‖T σ‖`
  have hw : ‖sourceWeight σ p‖ = (p : ℝ) ^ (-(σ / 2)) / Real.sqrt (squarefreeMobiusTotal σ) := by
    rw [sourceWeight_prime hs, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have ht : ‖(T σ (lp.single 2 (p : ℕ) 1) : Nat.Primes → ℂ) p‖ ≤ ‖T σ‖ := by
    set e : ℓ²ℕ := lp.single (E := fun _ : ℕ => ℂ) 2 (p : ℕ) 1 with he
    have he1 : ‖e‖ = 1 := by rw [he, lp.norm_single (by norm_num)]; simp
    have h1 := lp.norm_apply_le_norm (E := fun _ : Nat.Primes => ℂ) (p := 2) two_ne_zero
      (T σ e) p
    have h2 := (T σ).le_opNorm e
    rw [he1, mul_one] at h2
    exact h1.trans h2
  have hb : ‖(seamAmplitude β p : ℂ)‖ ≤ ‖sourceWeight σ p‖ * ‖T σ‖ + ε σ := by
    have h1 := norm_sub_norm_le (seamAmplitude β p : ℂ)
      (sourceWeight σ p * (T σ (lp.single 2 (p : ℕ) 1) : Nat.Primes → ℂ) p)
    rw [norm_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left ht (norm_nonneg (sourceWeight σ p))
    rw [norm_sub_rev] at hbohr
    linarith
  rw [hw, Complex.norm_real, Real.norm_eq_abs] at hb
  -- `p^{σ/2} |b(p)| = s_p(σ) ≥ s_p(1)`
  have hprof : (p : ℝ) ^ (σ / 2) * |seamAmplitude β p| = seamLogProfile σ β p := by
    rw [seamAmplitude, seamLogProfile, abs_mul, abs_div, abs_of_nonneg (Real.log_natCast_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow]
    have : (p : ℝ) ^ (σ / 2) / (p : ℝ) ^ (1 / 2 : ℝ) = (p : ℝ) ^ ((σ - 1) / 2) := by
      rw [← Real.rpow_sub hp0]; ring_nf
    rw [← this]; ring
  have hpow : (p : ℝ) ^ (σ / 2) * (p : ℝ) ^ (-(σ / 2)) = 1 := by
    rw [← Real.rpow_add hp0]; simp
  have hmain : seamLogProfile σ β p - (p : ℝ) ^ (σ / 2) * ε σ ≤
      ‖T σ‖ / Real.sqrt (squarefreeMobiusTotal σ) := by
    rw [← hprof]
    have hpp : 0 < (p : ℝ) ^ (σ / 2) := Real.rpow_pos_of_pos hp0 _
    have h1 := mul_le_mul_of_nonneg_left hb hpp.le
    have h2 : (p : ℝ) ^ (σ / 2) * ((p : ℝ) ^ (-(σ / 2)) / Real.sqrt (squarefreeMobiusTotal σ) *
        ‖T σ‖ + ε σ) = ‖T σ‖ / Real.sqrt (squarefreeMobiusTotal σ) + (p : ℝ) ^ (σ / 2) * ε σ := by
      calc (p : ℝ) ^ (σ / 2) * ((p : ℝ) ^ (-(σ / 2)) / Real.sqrt (squarefreeMobiusTotal σ) *
            ‖T σ‖ + ε σ) = ((p : ℝ) ^ (σ / 2) * (p : ℝ) ^ (-(σ / 2))) * ‖T σ‖ /
              Real.sqrt (squarefreeMobiusTotal σ) + (p : ℝ) ^ (σ / 2) * ε σ := by ring
        _ = _ := by rw [hpow, one_mul]
    rw [h2] at h1
    linarith
  have h1 := seamLogProfile_one_le (β := β) hs.le p
  linarith

end RHTower
