import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheSecondCriticalState

/-!
# The critical states form an orthogonal ladder

Let `Q_R = B + a(R) W₈` be the confined form, `W₈(F, G) = ∫ F G e^{−8u}` its confinement pairing, and
call a finite family of unit null vectors `Φ_0, …, Φ_m` of `Q_{R_0}, …, Q_{R_m}`, `W₀ = R_0 ≤ … ≤ R_m`,
a **critical ladder** when the `Φ_i` are `W₈`-orthogonal and `Q_R ≥ 0` on their `W₈`-orthogonal
complement for every `R ≤ R_m` (`IsCriticalLadder`).

* **Exact expansion** (`fullEnergy_add_sum_nullVectors`). For `Z` orthogonal to the family,
  `Q_R(Z + Σ c_i Φ_i) = Q_R(Z) + Σ c_i² (a(R) − a(R_i)) W₈(Φ_i)`: a null vector at `R_i` pairs with every
  profile at ratio `R` through the confinement alone, `Q_R(Φ_i, G) = (a(R) − a(R_i)) W₈(Φ_i, G)`.
* **The ladder extends** (`IsCriticalLadder.extend`). If `Q_{R*}` is negative somewhere on the
  orthogonal complement at a ratio `R* > R_m`, let `R_{m+1}` be the infimum of such ratios. Then
  `Q_{R_{m+1}} ≥ 0` on the complement, the constrained energy `0` is attained there by a unit profile
  `K`, and `K` is a null vector of `Q_{R_{m+1}}`: on the whole domain
  `Q_{R_{m+1}}(X) ≥ Σ_i (a(R_{m+1}) − a(R_i)) W₈(Φ_i, X)²/W₈(Φ_i)`, with equality to first order at `K`.
* **As many critical states as right zeros** (`exists_criticalLadder`,
  `riemannHypothesis_or_criticalLadder`). If at least `k + 1` zeros of `ζ` lie right of the line (as a
  set), there is a critical ladder of length `k + 1` starting at the critical state: the confined Gram
  matrix of half-line tests has `k + 1` negative squares at large ratios, and its real negative
  `(k+1)`-space meets the complement of `k` given profiles.

Constraints pass to `L²` limits with bounded confinement (`tendsto_exponentialPair_of_tendsto_L2`):
the pairing splits into a tail beyond `−T`, small uniformly, and a head controlled by `e^{4T}‖·‖₂`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23 Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory
  HTGeometry HeckeKreinToeplitz

local notation "W8" => criticalHalfLineExponentialPair

/-! ### The confinement pairing -/

theorem integrable_exponentialPairIntegrand {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    Integrable fun u => F u * G u * Real.exp (-(8 * u)) := by
  refine ((hF.exponential.add hG.exponential).div_const 2).mono'
    ((hF.meas.mul hG.meas).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e := Real.exp_pos (-(8 * u))
  show |F u| * |G u| * Real.exp (-(8 * u)) ≤
    (F u ^ 2 * Real.exp (-(8 * u)) + G u ^ 2 * Real.exp (-(8 * u))) / 2
  nlinarith [sq_abs (F u), sq_abs (G u), mul_nonneg (sq_nonneg (|F u| - |G u|)) e.le]

theorem exponentialPair_comm (F G : ℝ → ℝ) : W8 F G = W8 G F := by
  unfold criticalHalfLineExponentialPair
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)

theorem exponentialPair_add_const_mul {F G H : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (hH : CriticalHalfLineEnergyDomain H) (c : ℝ) :
    W8 F (fun u => G u + c * H u) = W8 F G + c * W8 F H := by
  unfold criticalHalfLineExponentialPair
  rw [← integral_const_mul, ← integral_add (integrable_exponentialPairIntegrand hF hG)
    ((integrable_exponentialPairIntegrand hF hH).const_mul c)]
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)

theorem exponentialPair_const_mul (F G : ℝ → ℝ) (c : ℝ) :
    W8 F (fun u => c * G u) = c * W8 F G := by
  unfold criticalHalfLineExponentialPair
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)

theorem criticalHalfLineEnergyDomain_add_sum {ι : Type*} {Z : ℝ → ℝ}
    (hZ : CriticalHalfLineEnergyDomain Z) {Φ : ι → ℝ → ℝ}
    (hΦ : ∀ i, CriticalHalfLineEnergyDomain (Φ i)) (c : ι → ℝ) (s : Finset ι) :
    CriticalHalfLineEnergyDomain (fun u => Z u + ∑ i ∈ s, c i * Φ i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hZ
  | insert j s hj ih =>
    have e : (fun u => Z u + ∑ i ∈ insert j s, c i * Φ i u) =
        fun u => (Z u + ∑ i ∈ s, c i * Φ i u) + c j * Φ j u := by
      funext u; rw [Finset.sum_insert hj]; ring
    rw [e]
    exact ih.add_const_mul (hΦ j) (c j)

theorem exponentialPair_add_sum {ι : Type*} {F Z : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hZ : CriticalHalfLineEnergyDomain Z) {Φ : ι → ℝ → ℝ}
    (hΦ : ∀ i, CriticalHalfLineEnergyDomain (Φ i)) (c : ι → ℝ) (s : Finset ι) :
    W8 F (fun u => Z u + ∑ i ∈ s, c i * Φ i u) = W8 F Z + ∑ i ∈ s, c i * W8 F (Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have e : (fun u => Z u + ∑ i ∈ insert j s, c i * Φ i u) =
        fun u => (Z u + ∑ i ∈ s, c i * Φ i u) + c j * Φ j u := by
      funext u; rw [Finset.sum_insert hj]; ring
    rw [e, exponentialPair_add_const_mul hF (criticalHalfLineEnergyDomain_add_sum hZ hΦ c s) (hΦ j),
      ih, Finset.sum_insert hj]
    ring

theorem criticalHalfLineMixedEnergy_self (R : ℝ) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    criticalHalfLineMixedEnergy R F F = criticalHalfLineFullEnergy R F := by
  have h := criticalHalfLineFullEnergy_add_const_mul R hF hF 1
  have e : (fun u => F u + 1 * F u) = fun u => 2 * F u := by funext u; ring
  rw [e, criticalHalfLineFullEnergy_const_mul] at h
  linarith

theorem exponentialPair_self_pos {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hm : (∫ u, F u ^ 2) ≠ 0) : 0 < W8 F F := by
  rw [criticalHalfLineExponentialPair_self]
  have hle : (∫ u, F u ^ 2) ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
    refine integral_mono hF.sq hF.exponential fun u => ?_
    show F u ^ 2 ≤ F u ^ 2 * Real.exp (-(8 * u))
    rcases le_or_gt 0 u with hu | hu
    · rw [hF.support u hu]; simp
    · have h1 : 1 ≤ Real.exp (-(8 * u)) := Real.one_le_exp (by linarith)
      nlinarith [sq_nonneg (F u)]
  have h0 : 0 < ∫ u, F u ^ 2 :=
    lt_of_le_of_ne (integral_nonneg fun u => sq_nonneg _) (Ne.symm hm)
  linarith

/-! ### Null vectors pair through the confinement -/

/-- A null vector of `Q_S` pairs with every profile at ratio `R` through the confinement alone:
`Q_R(Φ, G) = (a(R) − a(S)) W₈(Φ, G)`. -/
theorem IsConfinedNullVector.mixedEnergy_eq {S : ℝ} {Φ : ℝ → ℝ} (hΦ : IsConfinedNullVector S Φ)
    (R : ℝ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineMixedEnergy R Φ G =
      (criticalAliasCoefficient R - criticalAliasCoefficient S) * W8 Φ G := by
  rw [criticalHalfLineMixedEnergy_change_ratio R S hΦ.1 hG, hΦ.2.2 G hG, zero_add]

/-- **Exact expansion along a family of orthogonal null vectors.** For `Z` orthogonal to the family,
`Q_R(Z + Σ c_i Φ_i) = Q_R(Z) + Σ c_i² (a(R) − a(R_i)) W₈(Φ_i)`. -/
theorem fullEnergy_add_sum_nullVectors (R : ℝ) {ι : Type*} {S : ι → ℝ} {Φ : ι → ℝ → ℝ}
    (hΦ : ∀ i, IsConfinedNullVector (S i) (Φ i))
    (horth : ∀ i j, i ≠ j → W8 (Φ i) (Φ j) = 0) {Z : ℝ → ℝ}
    (hZ : CriticalHalfLineEnergyDomain Z) (hZo : ∀ i, W8 (Φ i) Z = 0) (c : ι → ℝ)
    (s : Finset ι) :
    criticalHalfLineFullEnergy R (fun u => Z u + ∑ i ∈ s, c i * Φ i u) =
      criticalHalfLineFullEnergy R Z + ∑ i ∈ s, c i ^ 2 *
        ((criticalAliasCoefficient R - criticalAliasCoefficient (S i)) * W8 (Φ i) (Φ i)) := by
  classical
  have hD : ∀ i, CriticalHalfLineEnergyDomain (Φ i) := fun i => (hΦ i).1
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    set A : ℝ → ℝ := fun u => Z u + ∑ i ∈ s, c i * Φ i u
    have hA : CriticalHalfLineEnergyDomain A := criticalHalfLineEnergyDomain_add_sum hZ hD c s
    have e : (fun u => Z u + ∑ i ∈ insert j s, c i * Φ i u) = fun u => A u + c j * Φ j u := by
      funext u; simp only [A]; rw [Finset.sum_insert hj]; ring
    have hAo : W8 (Φ j) A = 0 := by
      rw [exponentialPair_add_sum (hD j) hZ hD c s, hZo j]
      rw [Finset.sum_eq_zero fun i hi => by
        rw [horth j i (fun h => hj (h ▸ hi)), mul_zero], add_zero]
    have hmix : criticalHalfLineMixedEnergy R A (Φ j) = 0 := by
      rw [criticalHalfLineMixedEnergy_symm R hA (hD j), (hΦ j).mixedEnergy_eq R hA, hAo, mul_zero]
    have hself : criticalHalfLineFullEnergy R (Φ j) =
        (criticalAliasCoefficient R - criticalAliasCoefficient (S j)) * W8 (Φ j) (Φ j) := by
      rw [← criticalHalfLineMixedEnergy_self R (hD j), (hΦ j).mixedEnergy_eq R (hD j)]
    rw [e, criticalHalfLineFullEnergy_add_const_mul R hA (hD j), hmix, hself, ih,
      Finset.sum_insert hj]
    ring

/-- **The floor inequality.** If `Q_R ≥ 0` on the `W₈`-orthogonal complement of a family of orthogonal
null vectors, then on the whole domain `Q_R(X) ≥ Σ_i (a(R) − a(R_i)) W₈(Φ_i, X)²/W₈(Φ_i)`. -/
theorem fullEnergy_ge_of_floor (R : ℝ) {ι : Type*} [Fintype ι] {S : ι → ℝ} {Φ : ι → ℝ → ℝ}
    (hΦ : ∀ i, IsConfinedNullVector (S i) (Φ i))
    (horth : ∀ i j, i ≠ j → W8 (Φ i) (Φ j) = 0)
    (hfloor : ∀ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X → (∀ i, W8 (Φ i) X = 0) →
      0 ≤ criticalHalfLineFullEnergy R X)
    {X : ℝ → ℝ} (hX : CriticalHalfLineEnergyDomain X) :
    ∑ i, (criticalAliasCoefficient R - criticalAliasCoefficient (S i)) * W8 (Φ i) X ^ 2 /
      W8 (Φ i) (Φ i) ≤ criticalHalfLineFullEnergy R X := by
  classical
  have hD : ∀ i, CriticalHalfLineEnergyDomain (Φ i) := fun i => (hΦ i).1
  have hpos : ∀ i, 0 < W8 (Φ i) (Φ i) := fun i => exponentialPair_self_pos (hD i) (hΦ i).2.1
  set c : ι → ℝ := fun i => W8 (Φ i) X / W8 (Φ i) (Φ i)
  set Y : ℝ → ℝ := fun u => X u + ∑ i, (-c i) * Φ i u
  have hY : CriticalHalfLineEnergyDomain Y := criticalHalfLineEnergyDomain_add_sum hX hD _ _
  have hYo : ∀ j, W8 (Φ j) Y = 0 := fun j => by
    rw [exponentialPair_add_sum (hD j) hX hD _ _, Finset.sum_eq_single j
      (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero]) (by simp)]
    simp only [c]
    field_simp [(hpos j).ne']
    ring
  have hXY : (fun u => Y u + ∑ i, c i * Φ i u) = X := by
    funext u
    simp only [Y, neg_mul, Finset.sum_neg_distrib]
    ring
  have h := fullEnergy_add_sum_nullVectors R hΦ horth hY hYo c Finset.univ
  rw [hXY] at h
  rw [h]
  have hterm : ∀ i, (criticalAliasCoefficient R - criticalAliasCoefficient (S i)) *
      W8 (Φ i) X ^ 2 / W8 (Φ i) (Φ i) = c i ^ 2 *
        ((criticalAliasCoefficient R - criticalAliasCoefficient (S i)) * W8 (Φ i) (Φ i)) := by
    intro i
    simp only [c]
    field_simp [(hpos i).ne']
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  linarith [hfloor Y hY hYo]

/-- **A zero of the constrained energy is a null vector.** -/
theorem isConfinedNullVector_of_floor_zero (R : ℝ) {ι : Type*} [Fintype ι] {S : ι → ℝ}
    {Φ : ι → ℝ → ℝ} (hΦ : ∀ i, IsConfinedNullVector (S i) (Φ i))
    (horth : ∀ i j, i ≠ j → W8 (Φ i) (Φ j) = 0)
    (hfloor : ∀ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X → (∀ i, W8 (Φ i) X = 0) →
      0 ≤ criticalHalfLineFullEnergy R X)
    {K : ℝ → ℝ} (hK : CriticalHalfLineEnergyDomain K) (hKm : (∫ u, K u ^ 2) = 1)
    (hKo : ∀ i, W8 (Φ i) K = 0) (hKQ : criticalHalfLineFullEnergy R K = 0) :
    IsConfinedNullVector R K := by
  refine ⟨hK, by rw [hKm]; norm_num, fun G hG => ?_⟩
  set q : (ℝ → ℝ) → ℝ := fun X => ∑ i, (criticalAliasCoefficient R -
    criticalAliasCoefficient (S i)) * W8 (Φ i) X ^ 2 / W8 (Φ i) (Φ i)
  refine eq_zero_of_forall_quadratic_nonneg (A := criticalHalfLineFullEnergy R G - q G)
    (sub_nonneg.mpr (fullEnergy_ge_of_floor R hΦ horth hfloor hG)) fun c => ?_
  have h := fullEnergy_ge_of_floor R hΦ horth hfloor (hK.add_const_mul hG c)
  have hq : q (fun u => K u + c * G u) = c ^ 2 * q G := by
    simp only [q]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [exponentialPair_add_const_mul (hΦ i).1 hK hG, hKo i, zero_add]
    ring
  change q (fun u => K u + c * G u) ≤ _ at h
  rw [hq, criticalHalfLineFullEnergy_add_const_mul R hK hG, hKQ] at h
  nlinarith

/-! ### Constraints pass to limits -/

theorem abs_integral_mul_le_sqrt {f g : ℝ → ℝ} (hfm : AEStronglyMeasurable f volume)
    (hgm : AEStronglyMeasurable g volume) (hf2 : Integrable fun x => f x ^ 2)
    (hg2 : Integrable fun x => g x ^ 2) :
    |∫ x, f x * g x| ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  rw [← Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)]
  exact Real.abs_le_sqrt (sq_integral_mul_le hfm hgm hf2 hg2)

/-- **Tail and head of the confinement pairing.** Beyond `−T` the pairing is controlled by the tail of
`W₈(Φ)`, and on `(−T, 0)` the weight `e^{−8u}` is at most `e^{4T} e^{−4u}`. -/
theorem abs_exponentialPair_le_split {Φ D : ℝ → ℝ} (hΦ : CriticalHalfLineEnergyDomain Φ)
    (hD : CriticalHalfLineEnergyDomain D) (T : ℝ) :
    |W8 Φ D| ≤ Real.sqrt (∫ u, (Iic (-T)).indicator
        (fun u => Φ u ^ 2 * Real.exp (-(8 * u))) u) *
        Real.sqrt (∫ u, D u ^ 2 * Real.exp (-(8 * u))) +
      Real.exp (4 * T) * Real.sqrt (∫ u, Φ u ^ 2 * Real.exp (-(8 * u))) *
        Real.sqrt (∫ u, D u ^ 2) := by
  set f₁ : ℝ → ℝ := (Iic (-T)).indicator fun u => Φ u * Real.exp (-(4 * u))
  set g₁ : ℝ → ℝ := fun u => D u * Real.exp (-(4 * u))
  set f₂ : ℝ → ℝ := (Ioi (-T)).indicator fun u => Φ u * Real.exp (-(8 * u))
  have hm₁ : AEStronglyMeasurable f₁ volume :=
    ((hΦ.meas.mul (by fun_prop)).indicator measurableSet_Iic).aestronglyMeasurable
  have hmg : AEStronglyMeasurable g₁ volume := (hD.meas.mul (by fun_prop)).aestronglyMeasurable
  have hm₂ : AEStronglyMeasurable f₂ volume :=
    ((hΦ.meas.mul (by fun_prop)).indicator measurableSet_Ioi).aestronglyMeasurable
  have e4 : ∀ u : ℝ, Real.exp (-(4 * u)) ^ 2 = Real.exp (-(8 * u)) := fun u => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hf₁sq : (fun u => f₁ u ^ 2) =
      (Iic (-T)).indicator fun u => Φ u ^ 2 * Real.exp (-(8 * u)) := by
    funext u
    by_cases hu : u ∈ Iic (-T)
    · simp only [f₁, indicator_of_mem hu, mul_pow, e4]
    · simp [f₁, indicator_of_notMem hu]
  have hg₁sq : (fun u => g₁ u ^ 2) = fun u => D u ^ 2 * Real.exp (-(8 * u)) := by
    funext u; simp only [g₁, mul_pow, e4]
  have hf₂le : ∀ u, f₂ u ^ 2 ≤ Real.exp (8 * T) * (Φ u ^ 2 * Real.exp (-(8 * u))) := by
    intro u
    by_cases hu : u ∈ Ioi (-T)
    · simp only [f₂, indicator_of_mem hu]
      rcases le_or_gt 0 u with h0 | h0
      · rw [hΦ.support u h0]; simp
      · have hu' : -T < u := hu
        have he : Real.exp (-(8 * u)) ≤ Real.exp (8 * T) := Real.exp_le_exp.mpr (by linarith)
        have hsq : (Φ u * Real.exp (-(8 * u))) ^ 2 =
            (Φ u ^ 2 * Real.exp (-(8 * u))) * Real.exp (-(8 * u)) := by ring
        rw [hsq, mul_comm (Real.exp (8 * T))]
        exact mul_le_mul_of_nonneg_left he (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    · have h0 : f₂ u = 0 := indicator_of_notMem hu _
      rw [h0, sq, zero_mul]
      positivity
  have hf₁2 : Integrable fun u => f₁ u ^ 2 := by
    rw [hf₁sq]; exact hΦ.exponential.indicator measurableSet_Iic
  have hg₁2 : Integrable fun u => g₁ u ^ 2 := by rw [hg₁sq]; exact hD.exponential
  have hf₂2 : Integrable fun u => f₂ u ^ 2 :=
    (hΦ.exponential.const_mul (Real.exp (8 * T))).mono' (hm₂.pow 2)
      (Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hf₂le u)
  have hsplit : (fun u => Φ u * D u * Real.exp (-(8 * u))) = fun u => f₁ u * g₁ u + f₂ u * D u := by
    funext u
    by_cases hu : u ≤ -T
    · have h1 : u ∈ Iic (-T) := hu
      have h2 : u ∉ Ioi (-T) := fun h => absurd (show -T < u from h) (not_lt.mpr hu)
      simp only [f₁, f₂, g₁, indicator_of_mem h1, indicator_of_notMem h2, zero_mul, add_zero]
      rw [show Φ u * Real.exp (-(4 * u)) * (D u * Real.exp (-(4 * u))) =
        Φ u * D u * Real.exp (-(4 * u)) ^ 2 by ring, e4]
    · have h1 : u ∉ Iic (-T) := hu
      have h2 : u ∈ Ioi (-T) := show -T < u from lt_of_not_ge hu
      simp only [f₁, f₂, indicator_of_mem h2, indicator_of_notMem h1, zero_mul, zero_add]
      ring
  have hi₁ := integrable_mul_of_sq_integrable hm₁ hmg hf₁2 hg₁2
  have hi₂ := integrable_mul_of_sq_integrable hm₂ hD.meas.aestronglyMeasurable hf₂2 hD.sq
  have hb₁ := abs_integral_mul_le_sqrt hm₁ hmg hf₁2 hg₁2
  have hb₂ := abs_integral_mul_le_sqrt hm₂ hD.meas.aestronglyMeasurable hf₂2 hD.sq
  have hint₂ : (∫ u, f₂ u ^ 2) ≤ Real.exp (8 * T) * ∫ u, Φ u ^ 2 * Real.exp (-(8 * u)) := by
    rw [← integral_const_mul]
    exact integral_mono hf₂2 (hΦ.exponential.const_mul _) hf₂le
  have hsq₂ : Real.sqrt (∫ u, f₂ u ^ 2) ≤
      Real.exp (4 * T) * Real.sqrt (∫ u, Φ u ^ 2 * Real.exp (-(8 * u))) := by
    calc Real.sqrt (∫ u, f₂ u ^ 2)
        ≤ Real.sqrt (Real.exp (8 * T) * ∫ u, Φ u ^ 2 * Real.exp (-(8 * u))) :=
          Real.sqrt_le_sqrt hint₂
      _ = Real.exp (4 * T) * Real.sqrt (∫ u, Φ u ^ 2 * Real.exp (-(8 * u))) := by
          rw [Real.sqrt_mul (Real.exp_pos _).le,
            show Real.exp (8 * T) = Real.exp (4 * T) ^ 2 by
              rw [← Real.exp_nat_mul]; congr 1; push_cast; ring,
            Real.sqrt_sq (Real.exp_pos _).le]
  unfold criticalHalfLineExponentialPair
  rw [hsplit, integral_add hi₁ hi₂]
  rw [hf₁sq] at hb₁
  rw [hg₁sq] at hb₁
  calc |(∫ u, f₁ u * g₁ u) + ∫ u, f₂ u * D u|
      ≤ |∫ u, f₁ u * g₁ u| + |∫ u, f₂ u * D u| := abs_add_le _ _
    _ ≤ _ := add_le_add hb₁ (hb₂.trans (mul_le_mul_of_nonneg_right hsq₂ (Real.sqrt_nonneg _)))

/-- **Constraints pass to limits.** If `‖D_n‖₂ → 0` with bounded confinement mass, then
`W₈(Φ, D_n) → 0`. -/
theorem tendsto_exponentialPair_of_tendsto_L2 {Φ : ℝ → ℝ} (hΦ : CriticalHalfLineEnergyDomain Φ)
    {D : ℕ → ℝ → ℝ} (hD : ∀ n, CriticalHalfLineEnergyDomain (D n)) {M : ℝ}
    (hM : ∀ n, (∫ u, D n u ^ 2 * Real.exp (-(8 * u))) ≤ M)
    (hL2 : Tendsto (fun n => ∫ u, D n u ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => W8 Φ (D n)) atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun u => Φ u ^ 2 * Real.exp (-(8 * u))
  have hg : Integrable g := hΦ.exponential
  have hg0 : ∀ u, 0 ≤ g u := fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  -- the tails of the confinement mass of `Φ` vanish
  have htail : Tendsto (fun k : ℕ => ∫ u, (Iic (-(k : ℝ))).indicator g u) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence g
      (fun k => (hg.indicator measurableSet_Iic).aestronglyMeasurable) hg
      (fun k => Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs]
        by_cases hu : u ∈ Iic (-(k : ℝ))
        · rw [indicator_of_mem hu, abs_of_nonneg (hg0 u)]
        · rw [indicator_of_notMem hu, abs_zero]; exact hg0 u)
      (Eventually.of_forall fun u => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop (Nat.ceil (-u))] with k hk
        have hk' : -u < (k : ℝ) := (Nat.le_ceil (-u)).trans_lt (by exact_mod_cast hk)
        rw [indicator_of_notMem (show u ∉ Iic (-(k : ℝ)) from fun h => by
          have : u ≤ -(k : ℝ) := h
          linarith)])
    simpa using h
  set M' : ℝ := max M 0
  have hM' : ∀ n, (∫ u, D n u ^ 2 * Real.exp (-(8 * u))) ≤ M' := fun n => (hM n).trans (le_max_left _ _)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsq := ((Real.continuous_sqrt.tendsto 0).comp htail).mul_const (Real.sqrt M')
  rw [Real.sqrt_zero, zero_mul] at hsq
  obtain ⟨k, hk⟩ := (hsq.eventually (gt_mem_nhds (half_pos hε))).exists
  have hhead : Tendsto (fun n => Real.exp (4 * (k : ℝ)) * Real.sqrt (∫ u, g u) *
      Real.sqrt (∫ u, D n u ^ 2)) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hL2).const_mul
      (Real.exp (4 * (k : ℝ)) * Real.sqrt (∫ u, g u))
    rwa [Real.sqrt_zero, mul_zero] at this
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hhead (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hb := abs_exponentialPair_le_split hΦ (hD n) (k : ℝ)
  have h1 : Real.sqrt (∫ u, (Iic (-(k : ℝ))).indicator g u) *
      Real.sqrt (∫ u, D n u ^ 2 * Real.exp (-(8 * u))) < ε / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hM' n)) (Real.sqrt_nonneg _))
      (by simpa only [Function.comp] using hk)
  have h2 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  rw [Real.dist_eq, sub_zero]
  linarith

/-- The confinement mass of a difference is at most twice the sum of the masses. -/
theorem exponentialMass_sub_le {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    (∫ u, (F u - G u) ^ 2 * Real.exp (-(8 * u))) ≤
      2 * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 2 * ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
  have hd : CriticalHalfLineEnergyDomain fun u => F u - G u := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using hF.add_const_mul hG (-1)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hF.exponential.const_mul _)
    (hG.exponential.const_mul _)]
  refine integral_mono hd.exponential ((hF.exponential.const_mul _).add
    (hG.exponential.const_mul _)) fun u => ?_
  have e := Real.exp_pos (-(8 * u))
  show (F u - G u) ^ 2 * Real.exp (-(8 * u)) ≤
    2 * (F u ^ 2 * Real.exp (-(8 * u))) + 2 * (G u ^ 2 * Real.exp (-(8 * u)))
  nlinarith [mul_nonneg (sq_nonneg (F u + G u)) e.le]

theorem exponentialPair_sub {F G H : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (hH : CriticalHalfLineEnergyDomain H) :
    W8 F (fun u => G u - H u) = W8 F G - W8 F H := by
  have h := exponentialPair_add_const_mul hF hG hH (-1)
  rw [show (fun u => G u + -1 * H u) = fun u => G u - H u by funext u; ring] at h
  rw [h]; ring

/-! ### The constrained energy -/

/-- The infimum of `Q_R` over unit profiles `W₈`-orthogonal to a family. -/
def constrainedEnergy (R : ℝ) {ι : Type*} (Φ : ι → ℝ → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∫ u, G u ^ 2) = 1 ∧
    (∀ i, W8 (Φ i) G = 0) ∧ criticalHalfLineFullEnergy R G = e}

theorem constrainedEnergy_bddBelow {R : ℝ} (hR : 0 < R) {ι : Type*} (Φ : ι → ℝ → ℝ) :
    BddBelow {e : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∫ u, G u ^ 2) = 1 ∧
      (∀ i, W8 (Φ i) G = 0) ∧ criticalHalfLineFullEnergy R G = e} :=
  ⟨criticalHalfLineGroundEnergy R, by
    rintro e ⟨G, hG, hm, -, rfl⟩
    have h := criticalHalfLineGroundEnergy_mul_mass_le_all hR hG
    rwa [hm, mul_one] at h⟩

theorem constrainedEnergy_le {R : ℝ} (hR : 0 < R) {ι : Type*} {Φ : ι → ℝ → ℝ} {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hm : (∫ u, G u ^ 2) = 1) (ho : ∀ i, W8 (Φ i) G = 0) :
    constrainedEnergy R Φ ≤ criticalHalfLineFullEnergy R G :=
  csInf_le (constrainedEnergy_bddBelow hR Φ) ⟨G, hG, hm, ho, rfl⟩

/-- **The constrained energy is attained.** -/
theorem exists_constrainedEnergy_minimizer {R : ℝ} (hR : 0 < R) {ι : Type*} {Φ : ι → ℝ → ℝ}
    (hΦ : ∀ i, CriticalHalfLineEnergyDomain (Φ i))
    (hne : ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∫ u, G u ^ 2) = 1 ∧
      ∀ i, W8 (Φ i) G = 0) :
    ∃ K : ℝ → ℝ, CriticalHalfLineEnergyDomain K ∧ (∫ u, K u ^ 2) = 1 ∧ (∀ i, W8 (Φ i) K = 0) ∧
      criticalHalfLineFullEnergy R K = constrainedEnergy R Φ := by
  set L : ℝ := constrainedEnergy R Φ
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos (n : ℕ) : 0 < e n := by dsimp only [e]; positivity
  have hele (n : ℕ) : e n ≤ 1 := by
    dsimp only [e]
    exact div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨G₀, hG₀, hm₀, ho₀⟩ := hne
  have hnonempty : ({b : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∫ u, G u ^ 2) = 1 ∧
      (∀ i, W8 (Φ i) G = 0) ∧ criticalHalfLineFullEnergy R G = b} : Set ℝ).Nonempty :=
    ⟨_, G₀, hG₀, hm₀, ho₀, rfl⟩
  have hchoose (n : ℕ) : ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∫ u, G u ^ 2) = 1 ∧
      (∀ i, W8 (Φ i) G = 0) ∧ criticalHalfLineFullEnergy R G < L + e n := by
    obtain ⟨b, ⟨G, hG, hm, ho, rfl⟩, hb⟩ := exists_lt_of_csInf_lt hnonempty
      (show constrainedEnergy R Φ < L + e n from lt_add_of_pos_right L (hepos n))
    exact ⟨G, hG, hm, ho, hb⟩
  choose G hDG hmG hoG heG using hchoose
  obtain ⟨B, hB, hgard⟩ := criticalHalfLineFullEnergy_coercive_remainder hR
  have ha := criticalAliasCoefficient_positive hR
  let M : ℝ := (|L| + 1 + B) / (criticalAliasCoefficient R / 2)
  have hM : 0 ≤ M := div_nonneg
    (add_nonneg (add_nonneg (abs_nonneg _) zero_le_one) hB) (half_pos ha).le
  have hG8 (n : ℕ) : (∫ u, G n u ^ 2 * Real.exp (-(8 * u))) ≤ M := by
    apply (le_div_iff₀ (half_pos ha)).mpr
    have h := hgard (hDG n)
    rw [hmG n, mul_one] at h
    linarith only [h, heG n, hele n, le_abs_self L]
  have hrec (n : ℕ) := exists_window_energy_recovery hR (hDG n) (hmG n).le (hepos n)
  choose A H hA hHwin hmH hdH hH8 heH using hrec
  have hDH (n : ℕ) := criticalHalfLineEnergyDomain_of_window (hHwin n)
  have hdiff (n : ℕ) : CriticalHalfLineEnergyDomain (fun u => H n u - G n u) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using (hDH n).add_const_mul (hDG n) (-1)
  have herr : Tendsto (fun n => ∫ u, (H n u - G n u) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun u => sq_nonneg _) (fun n => (hdH n).le) helim
  have hmasslim : Tendsto (fun n => ∫ u, H n u ^ 2) atTop (𝓝 1) := by
    have h := HTGeometry.tendsto_integral_sq_add_of_tendsto_zero
      (Eventually.of_forall fun n => (hDG n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hdiff n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hDG n).sq)
      (Eventually.of_forall fun n => (hdiff n).sq)
      (show Tendsto (fun n => ∫ u, G n u ^ 2) atTop (𝓝 1) by
        simpa only [hmG] using (tendsto_const_nhds (x := (1 : ℝ)))) herr
    exact h.congr fun n => integral_congr_ae (Eventually.of_forall fun u => by congr 1; ring)
  have hupper (n : ℕ) : criticalHalfLineFullEnergy R (H n) ≤ L + 2 * e n := by
    linarith only [heH n, heG n]
  set μ := criticalHalfLineGroundEnergy R
  have hlower (n : ℕ) : -|μ| ≤ criticalHalfLineFullEnergy R (H n) := by
    have h1 := criticalHalfLineGroundEnergy_mul_mass_le_all hR (hDH n)
    have h2 : (∫ u, H n u ^ 2) ≤ 1 := (hmH n).trans (hmG n).le
    have h3 : 0 ≤ ∫ u, H n u ^ 2 := integral_nonneg fun u => sq_nonneg _
    nlinarith [neg_abs_le μ, abs_nonneg μ]
  obtain ⟨L', -, φ, hφ, hφlim⟩ := tendsto_subseq_of_bounded
    (x := fun n => criticalHalfLineFullEnergy R (H n))
    (Metric.isBounded_Icc (-|μ|) (L + 2)) fun n => ⟨hlower n, (hupper n).trans (by linarith [hele n])⟩
  have hL' : L' ≤ L := by
    have h2 : Tendsto (fun n => L + 2 * e (φ n)) atTop (𝓝 (L + 2 * 0)) :=
      tendsto_const_nhds.add ((helim.comp hφ.tendsto_atTop).const_mul 2)
    rw [mul_zero, add_zero] at h2
    exact le_of_tendsto_of_tendsto hφlim h2 (Eventually.of_forall fun n => hupper (φ n))
  obtain ⟨K, s, hs, hDK, hmK, heK, hK8, hL2, -⟩ := exists_domain_limit_of_smooth_energy_limit hR
    (fun n => hDH (φ n)) (fun n => (hHwin (φ n)).contDiff) (fun n => (hHwin (φ n)).hasCompactSupport)
    (fun n => (hmH (φ n)).trans (hmG (φ n)).le) (hmasslim.comp hφ.tendsto_atTop)
    (mul_nonneg (by norm_num) hM)
    (fun n => (hH8 (φ n)).trans (mul_le_mul_of_nonneg_left (hG8 (φ n)) (by norm_num)))
    (B := L + 2) (fun n => (hupper (φ n)).trans (by linarith [hele (φ n)])) hφlim
  -- the constraints pass to the limit
  have hoK : ∀ i, W8 (Φ i) K = 0 := by
    intro i
    set ψ : ℕ → ℕ := fun n => φ (s n)
    have hψ : StrictMono ψ := hφ.comp hs
    have hdK (n : ℕ) : CriticalHalfLineEnergyDomain (fun u => H (ψ n) u - K u) := by
      simpa only [neg_one_mul, sub_eq_add_neg] using (hDH (ψ n)).add_const_mul hDK (-1)
    have hv : Tendsto (fun n => W8 (Φ i) (fun u => H (ψ n) u - K u)) atTop (𝓝 0) :=
      tendsto_exponentialPair_of_tendsto_L2 (hΦ i) hdK (M := 2 * (2 * M) + 2 * (2 * M))
        (fun n => (exponentialMass_sub_le (hDH (ψ n)) hDK).trans (by
          have h1 := (hH8 (ψ n)).trans (mul_le_mul_of_nonneg_left (hG8 (ψ n)) (by norm_num))
          linarith)) hL2
    have hz : Tendsto (fun n => W8 (Φ i) (fun u => H (ψ n) u - G (ψ n) u)) atTop (𝓝 0) :=
      tendsto_exponentialPair_of_tendsto_L2 (hΦ i) (fun n => hdiff (ψ n))
        (M := 2 * (2 * M) + 2 * M)
        (fun n => (exponentialMass_sub_le (hDH (ψ n)) (hDG (ψ n))).trans (by
          have h1 := (hH8 (ψ n)).trans (mul_le_mul_of_nonneg_left (hG8 (ψ n)) (by norm_num))
          linarith [hG8 (ψ n)])) (herr.comp hψ.tendsto_atTop)
    have hv' : Tendsto (fun n => W8 (Φ i) (H (ψ n)) - W8 (Φ i) K) atTop (𝓝 0) :=
      hv.congr fun n => exponentialPair_sub (hΦ i) (hDH (ψ n)) hDK
    have hz' : Tendsto (fun n => W8 (Φ i) (H (ψ n))) atTop (𝓝 0) := by
      refine hz.congr fun n => ?_
      rw [exponentialPair_sub (hΦ i) (hDH (ψ n)) (hDG (ψ n)), hoG (ψ n) i, sub_zero]
    have h := hz'.sub hv'
    simp only [sub_sub_cancel, sub_self] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  exact ⟨K, hDK, hmK, hoK, le_antisymm (heK.trans hL') (constrainedEnergy_le hR hDK hmK hoK)⟩

/-! ### Negative directions orthogonal to a family -/

/-- **Realification.** `m + 1` negative squares of the confined Gram matrix of half-line tests give a
real profile with negative confined energy, `W₈`-orthogonal to `m` given profiles. -/
theorem exists_real_negative_orthogonal_family {S : Finset ℝ} {H : S → ℝ → ℝ}
    (hH : ∀ s, IsHalfLineTest (H s)) {R : ℝ} {m : ℕ}
    (hm : m + 1 ≤ hermNegIndex (confinedGram R H)) {Φ : Fin m → ℝ → ℝ}
    (hΦ : ∀ i, CriticalHalfLineEnergyDomain (Φ i)) :
    ∃ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X ∧ criticalHalfLineFullEnergy R X < 0 ∧
      ∀ i, W8 (Φ i) X = 0 := by
  set M := confinedGram R H
  obtain ⟨W, hWr, hWpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (-M)
  have hWm : m < Module.finrank ℂ W := by
    have hneg : hermNegIndex M = hermPosIndex (-M) := rfl
    omega
  obtain ⟨A, hA⟩ := exists_common_window hH
  have hDs : ∀ s, CriticalHalfLineEnergyDomain (H s) := fun s =>
    criticalHalfLineEnergyDomain_of_window ⟨(hH s).1, hA s⟩
  let c : Fin m → S → ℝ := fun i s => W8 (Φ i) (H s)
  let L : (S → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun v i => ∑ s, v s * (c i s : ℂ)
      map_add' := fun v w => by
        funext i
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a v => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker (L.domRestrict W) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fin_fun]
    exact hWm
  obtain ⟨w, hwker, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv0 : (w : S → ℂ) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hφv : ∀ i, ∑ s, (w : S → ℂ) s * (c i s : ℂ) = 0 := fun i =>
    congrFun (LinearMap.mem_ker.mp hwker) i
  have hneg : hermQuad M (w : S → ℂ) < 0 := by
    have h := hWpos (w : S → ℂ) w.2 hv0
    rw [hermQuad_neg] at h
    linarith
  rw [hermQuad_eq_re_add_im (fun i j => confinedGram_im R H i j)] at hneg
  have hre : ∀ i, ∑ s, ((w : S → ℂ) s).re * c i s = 0 := fun i => by
    have := congrArg Complex.re (hφv i)
    simpa [Complex.re_sum, Complex.mul_re] using this
  have him : ∀ i, ∑ s, ((w : S → ℂ) s).im * c i s = 0 := fun i => by
    have := congrArg Complex.im (hφv i)
    simpa [Complex.im_sum, Complex.mul_im] using this
  have hcomb : ∀ y : S → ℝ, (∀ i, ∑ s, y s * c i s = 0) →
      hermQuad M (fun s => (y s : ℂ)) < 0 →
      ∃ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X ∧ criticalHalfLineFullEnergy R X < 0 ∧
        ∀ i, W8 (Φ i) X = 0 := by
    intro y hy hq
    refine ⟨fun u => ∑ s, y s * H s u, ?_, ?_, fun i => ?_⟩
    · exact criticalHalfLineEnergyDomain_of_window (A := A)
        ⟨ContDiff.sum fun s _ => contDiff_const.mul (hH s).1,
          fun u (hu : u ∉ Icc (-A) 0) => by simp [hA _ u hu]⟩
    · rwa [← hermQuad_confinedGram_ofReal R hH y]
    · unfold criticalHalfLineExponentialPair
      have hfun : (fun u => Φ i u * (∑ s, y s * H s u) * Real.exp (-(8 * u))) =
          fun u => ∑ s, y s * (Φ i u * H s u * Real.exp (-(8 * u))) := by
        funext u; rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [hfun, integral_finsetSum _ fun s _ =>
        (integrable_exponentialPairIntegrand (hΦ i) (hDs s)).const_mul _]
      have hy' := hy i
      simp only [c, criticalHalfLineExponentialPair] at hy'
      simpa [integral_const_mul] using hy'
  rcases lt_or_ge (hermQuad M fun s => (((w : S → ℂ) s).re : ℂ)) 0 with hr | hr
  · exact hcomb (fun s => ((w : S → ℂ) s).re) hre hr
  · exact hcomb (fun s => ((w : S → ℂ) s).im) him (by linarith)

/-! ### Critical ladders -/

/-- A **critical ladder** of length `m + 1`: unit null vectors `Φ_i` of `Q_{R_i}` with nondecreasing
positive ratios, pairwise `W₈`-orthogonal, and `Q_r ≥ 0` on their `W₈`-orthogonal complement for every
`0 < r ≤ R_m`. -/
structure IsCriticalLadder (m : ℕ) (R : Fin (m + 1) → ℝ) (Φ : Fin (m + 1) → ℝ → ℝ) : Prop where
  null : ∀ i, IsConfinedNullVector (R i) (Φ i)
  unit : ∀ i, (∫ u, Φ i u ^ 2) = 1
  pos : ∀ i, 0 < R i
  mono : Monotone R
  orth : ∀ i j, i ≠ j → W8 (Φ i) (Φ j) = 0
  floor : ∀ r : ℝ, 0 < r → r ≤ R (Fin.last m) → ∀ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X →
    (∀ i, W8 (Φ i) X = 0) → 0 ≤ criticalHalfLineFullEnergy r X

/-- A profile with negative confined energy has positive mass. -/
theorem integral_sq_pos_of_fullEnergy_neg {R : ℝ} (hR : 0 < R) {X : ℝ → ℝ}
    (hX : CriticalHalfLineEnergyDomain X) (hXQ : criticalHalfLineFullEnergy R X < 0) :
    0 < ∫ u, X u ^ 2 := by
  rcases (integral_nonneg (fun u => sq_nonneg (X u)) : (0 : ℝ) ≤ ∫ u, X u ^ 2).lt_or_eq with h | h
  · exact h
  · have := criticalHalfLineGroundEnergy_mul_mass_le_all hR hX
    rw [← h, mul_zero] at this
    linarith

/-- Normalization keeps orthogonality and the sign of the energy. -/
theorem exists_unit_of_fullEnergy_neg {R : ℝ} (hR : 0 < R) {ι : Type*} {Φ : ι → ℝ → ℝ}
    {X : ℝ → ℝ} (hX : CriticalHalfLineEnergyDomain X) (hXo : ∀ i, W8 (Φ i) X = 0)
    (hXQ : criticalHalfLineFullEnergy R X < 0) :
    ∃ Y : ℝ → ℝ, CriticalHalfLineEnergyDomain Y ∧ (∫ u, Y u ^ 2) = 1 ∧ (∀ i, W8 (Φ i) Y = 0) ∧
      criticalHalfLineFullEnergy R Y < 0 := by
  have hm := integral_sq_pos_of_fullEnergy_neg hR hX hXQ
  set k : ℝ := (Real.sqrt (∫ u, X u ^ 2))⁻¹
  have hk2 : k ^ 2 * (∫ u, X u ^ 2) = 1 := by
    simp only [k, inv_pow, Real.sq_sqrt hm.le]
    exact inv_mul_cancel₀ hm.ne'
  refine ⟨fun u => k * X u, hX.const_mul k, ?_, fun i => ?_, ?_⟩
  · simp_rw [mul_pow]; rw [integral_const_mul, hk2]
  · rw [exponentialPair_const_mul, hXo i, mul_zero]
  · rw [criticalHalfLineFullEnergy_const_mul]
    exact mul_neg_of_pos_of_neg (by positivity) hXQ

/-- **The ladder extends.** If `Q_{R*}` is negative on the complement of a critical ladder at a ratio
`R* > R_m`, the infimum `r` of such ratios carries a further rung. -/
theorem IsCriticalLadder.extend {m : ℕ} {R : Fin (m + 1) → ℝ} {Φ : Fin (m + 1) → ℝ → ℝ}
    (hL : IsCriticalLadder m R Φ) {Rs : ℝ} (hRs : R (Fin.last m) < Rs) {Y : ℝ → ℝ}
    (hY : CriticalHalfLineEnergyDomain Y) (hYo : ∀ i, W8 (Φ i) Y = 0)
    (hYQ : criticalHalfLineFullEnergy Rs Y < 0) :
    ∃ (r : ℝ) (K : ℝ → ℝ), R (Fin.last m) ≤ r ∧ r ≤ Rs ∧
      IsCriticalLadder (m + 1) (Fin.snoc R r) (Fin.snoc Φ K) := by
  set Rl := R (Fin.last m)
  have hRl : 0 < Rl := hL.pos _
  set A : Set ℝ := {t | Rl < t ∧ ∃ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X ∧
    (∀ i, W8 (Φ i) X = 0) ∧ criticalHalfLineFullEnergy t X < 0}
  have hAs : Rs ∈ A := ⟨hRs, Y, hY, hYo, hYQ⟩
  have hAbdd : BddBelow A := ⟨Rl, fun t ht => ht.1.le⟩
  set r := sInf A
  have hrRl : Rl ≤ r := le_csInf ⟨Rs, hAs⟩ fun t ht => ht.1.le
  have hr0 : 0 < r := hRl.trans_le hrRl
  have hrRs : r ≤ Rs := csInf_le hAbdd hAs
  -- ratios above an admissible one are admissible
  have hup : ∀ t₁ ∈ A, ∀ t₂, t₁ ≤ t₂ → t₂ ∈ A := by
    rintro t₁ ⟨h1, X, hX, hXo, hXQ⟩ t₂ h12
    refine ⟨h1.trans_le h12, X, hX, hXo, ?_⟩
    rw [criticalHalfLineFullEnergy_change_ratio t₂ t₁ hX]
    have ha := criticalAliasCoefficient_antitone (hRl.trans h1) h12
    have hw : 0 ≤ ∫ u, X u ^ 2 * Real.exp (-(8 * u)) :=
      integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    nlinarith
  -- the energy of a fixed profile is continuous in the ratio
  have hcont : ∀ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X →
      Tendsto (fun t => criticalHalfLineFullEnergy t X) (𝓝 r)
        (𝓝 (criticalHalfLineFullEnergy r X)) := by
    intro X hX
    have ha : Tendsto (fun t => criticalAliasCoefficient 1 / t) (𝓝 r)
        (𝓝 (criticalAliasCoefficient 1 / r)) := tendsto_const_nhds.div tendsto_id hr0.ne'
    have h := (ha.sub (tendsto_const_nhds (x := criticalAliasCoefficient 1 / r))).mul_const
      (∫ u, X u ^ 2 * Real.exp (-(8 * u))) |>.const_add (criticalHalfLineFullEnergy r X)
    rw [sub_self, zero_mul, add_zero] at h
    refine h.congr fun t => ?_
    rw [criticalHalfLineFullEnergy_change_ratio t r hX, criticalAliasCoefficient_eq_div t,
      criticalAliasCoefficient_eq_div r]
  -- the infimum is not admissible
  have hrA : r ∉ A := by
    rintro ⟨h1, X, hX, hXo, hXQ⟩
    have hev : ∀ᶠ t in 𝓝 r, Rl < t ∧ criticalHalfLineFullEnergy t X < 0 :=
      (lt_mem_nhds h1).and ((hcont X hX).eventually (gt_mem_nhds hXQ))
    have hev' : ∀ᶠ t in 𝓝[<] r, (Rl < t ∧ criticalHalfLineFullEnergy t X < 0) ∧ t ∈ Iio r :=
      (eventually_nhdsWithin_of_eventually_nhds hev).and self_mem_nhdsWithin
    obtain ⟨t, ⟨ht1, ht2⟩, htr⟩ := hev'.exists
    exact absurd (csInf_le hAbdd ⟨ht1, X, hX, hXo, ht2⟩) (not_le.mpr htr)
  -- the floor holds up to `r`
  have hfloor : ∀ t : ℝ, 0 < t → t ≤ r → ∀ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X →
      (∀ i, W8 (Φ i) X = 0) → 0 ≤ criticalHalfLineFullEnergy t X := by
    intro t ht0 htr X hX hXo
    by_cases htl : t ≤ Rl
    · exact hL.floor t ht0 htl X hX hXo
    · by_contra hneg
      have htA : t ∈ A := ⟨lt_of_not_ge htl, X, hX, hXo, lt_of_not_ge hneg⟩
      rcases htr.lt_or_eq with h | h
      · exact absurd (csInf_le hAbdd htA) (not_le.mpr h)
      · exact hrA (h ▸ htA)
  -- the constrained energy at `r` vanishes
  obtain ⟨Y₁, hY₁, hY₁m, hY₁o, -⟩ := exists_unit_of_fullEnergy_neg (hRl.trans hRs) hY hYo hYQ
  have hE0 : 0 ≤ constrainedEnergy r Φ :=
    le_csInf ⟨_, Y₁, hY₁, hY₁m, hY₁o, rfl⟩ fun e ⟨G, hG, _, hGo, he⟩ =>
      he ▸ hfloor r hr0 le_rfl G hG hGo
  have hE1 : constrainedEnergy r Φ ≤ 0 := by
    obtain ⟨B, hB, hgard⟩ := criticalHalfLineFullEnergy_coercive_remainder hr0
    have har := criticalAliasCoefficient_positive hr0
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    rw [zero_add]
    set δ : ℝ := min (criticalAliasCoefficient r / 4) (ε * criticalAliasCoefficient r / (4 * B + 1))
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    have hca : Tendsto criticalAliasCoefficient (𝓝[>] r) (𝓝 (criticalAliasCoefficient r)) := by
      have h : Tendsto (fun t => criticalAliasCoefficient 1 / t) (𝓝 r)
          (𝓝 (criticalAliasCoefficient 1 / r)) := tendsto_const_nhds.div tendsto_id hr0.ne'
      rw [← criticalAliasCoefficient_eq_div r] at h
      exact (h.congr fun t => (criticalAliasCoefficient_eq_div t).symm).mono_left
        nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] r, criticalAliasCoefficient t ∈
        Metric.ball (criticalAliasCoefficient r) δ ∧ t ∈ Ioi r :=
      (hca.eventually (Metric.ball_mem_nhds _ hδ)).and self_mem_nhdsWithin
    obtain ⟨t, ht1, ht2'⟩ := hev.exists
    have ht2 : r < t := ht2'
    have htA : t ∈ A := by
      obtain ⟨t₀, ht₀A, ht₀⟩ := exists_lt_of_csInf_lt ⟨Rs, hAs⟩ ht2
      exact hup t₀ ht₀A t ht₀.le
    obtain ⟨X, hX, hXo, hXQ⟩ := htA.2
    obtain ⟨Z, hZ, hZm, hZo, hZQ⟩ := exists_unit_of_fullEnergy_neg (hr0.trans ht2) hX hXo hXQ
    have hgap : criticalAliasCoefficient r - criticalAliasCoefficient t < δ := by
      have h1 := Metric.mem_ball.mp ht1
      rw [Real.dist_eq] at h1
      linarith [(abs_lt.mp h1).1]
    have hgap0 : 0 ≤ criticalAliasCoefficient r - criticalAliasCoefficient t :=
      sub_nonneg.mpr (criticalAliasCoefficient_antitone hr0 ht2.le)
    set w := ∫ u, Z u ^ 2 * Real.exp (-(8 * u))
    have hw0 : 0 ≤ w := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    have hchange := criticalHalfLineFullEnergy_change_ratio r t hZ
    have hg := hgard hZ
    rw [hZm, mul_one] at hg
    -- `w` is bounded by coercivity at `r`
    have hwle : w * (criticalAliasCoefficient r / 4) ≤ B := by
      have hδ4 : δ ≤ criticalAliasCoefficient r / 4 := min_le_left _ _
      nlinarith
    have hwle' : w ≤ 4 * B / criticalAliasCoefficient r := by
      rw [le_div_iff₀ har]; linarith
    have hlt : criticalHalfLineFullEnergy r Z < ε := by
      have hδε : δ ≤ ε * criticalAliasCoefficient r / (4 * B + 1) := min_le_right _ _
      have hprod : (criticalAliasCoefficient r - criticalAliasCoefficient t) * w ≤
          δ * (4 * B / criticalAliasCoefficient r) :=
        mul_le_mul hgap.le hwle' hw0 hδ.le
      have hfin : δ * (4 * B / criticalAliasCoefficient r) < ε := by
        calc δ * (4 * B / criticalAliasCoefficient r)
            ≤ ε * criticalAliasCoefficient r / (4 * B + 1) * (4 * B / criticalAliasCoefficient r) :=
              mul_le_mul_of_nonneg_right hδε (by positivity)
          _ = ε * (4 * B / (4 * B + 1)) := by field_simp
          _ < ε := by
              have : 4 * B / (4 * B + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
              nlinarith
      linarith
    exact (constrainedEnergy_le hr0 hZ hZm hZo).trans_lt hlt
  obtain ⟨K, hK, hKm, hKo, hKQ⟩ := exists_constrainedEnergy_minimizer hr0 (fun i => (hL.null i).1)
    ⟨Y₁, hY₁, hY₁m, hY₁o⟩
  have hKQ0 : criticalHalfLineFullEnergy r K = 0 := by rw [hKQ]; exact le_antisymm hE1 hE0
  have hKnull : IsConfinedNullVector r K :=
    isConfinedNullVector_of_floor_zero r hL.null hL.orth (hfloor r hr0 le_rfl) hK hKm hKo hKQ0
  refine ⟨r, K, hrRl, hrRs, ⟨fun i => ?_, fun i => ?_, fun i => ?_, ?_, fun i j hij => ?_, ?_⟩⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hKnull
    · simpa using hL.null j
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hKm
    · simpa using hL.unit j
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hr0
    · simpa using hL.pos j
  · intro i j hij
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using (hL.mono (Fin.le_last i)).trans hrRl
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_le.mpr (Fin.castSucc_lt_last j))
      | cast i => simpa using hL.mono (Fin.castSucc_le_castSucc_iff.mp hij)
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j => simpa [exponentialPair_comm] using hKo j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa using hKo i
      | cast j =>
        simpa using hL.orth i j fun h => hij (by rw [h])
  · intro t ht0 htr X hX hXo
    refine hfloor t ht0 (by simpa using htr) X hX fun i => ?_
    simpa using hXo (Fin.castSucc i)

/-- **As many critical states as right zeros.** If at least `k + 1` zeros of `ζ` lie right of the
line, the critical state starts a critical ladder of length `k + 1`. -/
theorem exists_criticalLadder {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard →
      ∃ (R : Fin (k + 1) → ℝ) (Φ : Fin (k + 1) → ℝ → ℝ),
        IsCriticalLadder k R Φ ∧ R 0 = W₀ ∧ Φ 0 = F := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => W₀, fun _ => F, ⟨fun _ => isConfinedNullVector_of_groundState hW ht hF,
      fun _ => hF.2.2.2.1, fun _ => hW, fun _ _ _ => le_rfl,
      fun i j hij => absurd (Fin.ext (by have := i.2; have := j.2; omega)) hij, ?_⟩, rfl, rfl⟩
    intro r hr0 hr X hX _
    have hμ := criticalHalfLineGroundEnergy_nonneg_of_le hW ht hF hr0 hr
    have h := criticalHalfLineGroundEnergy_mul_mass_le_all hr0 hX
    nlinarith [(integral_nonneg fun u => sq_nonneg (X u) : (0 : ℝ) ≤ ∫ u, X u ^ 2)]
  | succ k ih =>
    intro hk
    obtain ⟨R, Φ, hL, hR0, hΦ0⟩ := ih (le_trans (Nat.cast_le.mpr (by omega)) hk)
    obtain ⟨S, H, hH, hev⟩ := exists_halfLineTests_eventually_le_hermNegIndex hk
    obtain ⟨Rs, hRs, hRsl⟩ := (hev.and (eventually_gt_atTop (R (Fin.last k)))).exists
    obtain ⟨Y, hY, hYQ, hYo⟩ := exists_real_negative_orthogonal_family hH (m := k + 1)
      (by simpa using hRs) (Φ := Φ) fun i => (hL.null i).1
    obtain ⟨r, K, -, -, hL'⟩ := hL.extend hRsl hY hYo hYQ
    refine ⟨Fin.snoc R r, Fin.snoc Φ K, hL', ?_, ?_⟩
    · rw [← Fin.castSucc_zero, Fin.snoc_castSucc, hR0]
    · rw [← Fin.castSucc_zero, Fin.snoc_castSucc, hΦ0]

/-- **Either RH holds, or the critical state starts a critical ladder with one rung per right zero.** -/
theorem riemannHypothesis_or_criticalLadder :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard →
        ∃ (R : Fin (k + 1) → ℝ) (Φ : Fin (k + 1) → ℝ → ℝ),
          IsCriticalLadder k R Φ ∧ R 0 = W₀ ∧ Φ 0 = F := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀, F, hW, ht, hF, exists_criticalLadder hW ht hF⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
