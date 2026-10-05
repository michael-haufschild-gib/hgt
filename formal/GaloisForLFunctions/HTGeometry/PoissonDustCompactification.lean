import GaloisForLFunctions.HTGeometry.WeakStarFormationContinuity
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Poisson-dust formation compactification

Let `K` be a compact metrizable commutative monoid and `M(K) = C(K, ℂ)*` its measure algebra
(complex Radon measures, total-variation norm, convolution).  A finite positive packet
`A = (α_1, …, α_m)` has the formation `Λ_A(z) = Π_j (δ_1 + z α_j)` and mass
`|A|_1 = Σ_j ‖α_j‖`; the convolution exponential `Exp_⋆(z γ)` converges in norm.

**Theorem 4.1.**  Packets of mass `≤ C` have a subsequence whose formations converge, against every
test function and uniformly on compact `z`-sets, to a decorated formation
`Exp_⋆(z γ) ⋆ Π_j (δ_1 + z α_j)` with positive dust `γ`, positive atoms `α_j` and
`‖γ‖ + Σ_j ‖α_j‖ ≤ C`.  Order each packet by decreasing mass, so that the
`j`-th factor has mass `≤ C/(j+1)`; extract one subsequence along which every factor and the total
`Γ_N = Σ_j α_{N,j}` converge weak-* (diagonal argument in the positive ball); put
`γ = Γ - Σ_j α_j`, positive as a limit of positive tails.  Splitting the formation into its first
`J` factors and its tail, the tail is within `e^{3RC} R² C²/(J+1)` of `Exp_⋆(z ⋅ tail sum)`
uniformly in `N`, and for fixed `J` the approximants converge weak-* uniformly by the product and
exponential continuity lemmas.

**Theorem 5.1 / Corollary 5.2.**  Conversely every decorated formation with
`‖γ‖ + Σ_j ‖α_j‖ ≤ C` is a limit of finite packets `(α_1, …, α_J, γ/M, …, γ/M)` of mass `≤ C`, in
norm uniformly on compact sets (Lemma 3.1).  Hence the limits of finite formations of mass `≤ C`
are exactly the decorated formations, and every sequence of decorated formations has a convergent
subsequence.
-/

open Filter Topology NormedSpace MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationDust

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
  [CommMonoid K] [ContinuousMul K] [MeasurableSpace K] [BorelSpace K]

open MeasureAlgebra

attribute [local instance] ratAlgebra

/-! ### Formations -/

/-- The formation `Λ_A(z) = Π_j (δ_1 + z α_j)` of a finite packet. -/
def formation {m : ℕ} (α : Fin m → MeasureAlgebra K) (z : ℂ) : MeasureAlgebra K :=
  ∏ j, (1 + z • α j)

/-- The packet mass `|A|_1 = Σ_j ‖α_j‖`; for positive packets `‖α_j‖ = α_j(K)`. -/
def packetMass {m : ℕ} (α : Fin m → MeasureAlgebra K) : ℝ := ∑ j, ‖α j‖

/-- The decorated formation `Exp_⋆(z γ) ⋆ Π_j (δ_1 + z α_j)`. -/
def decorated (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) (z : ℂ) : MeasureAlgebra K :=
  exp (z • γ) * ∏' j, (1 + z • α j)

/-- Compact-open weak convergence. -/
def FormConv (F : ℕ → ℂ → MeasureAlgebra K) (G : ℂ → MeasureAlgebra K) : Prop :=
  ∀ R : ℝ, WeakUnifOn F G (Metric.closedBall 0 R)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- The infinite product converges in norm when the masses are summable. -/
theorem multipliable_formation {α : ℕ → MeasureAlgebra K} (hα : Summable fun j => ‖α j‖)
    (z : ℂ) : Multipliable fun j => 1 + z • α j :=
  multipliable_one_add_of_summable ((hα.mul_left ‖z‖).congr fun j => (norm_smul z (α j)).symm)

/-! ### The tail estimate -/

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **The tail estimate**: if the factors beyond `J` have mass
`≤ C/(J+1)` and the total mass is `≤ C`, then
`‖Π_{j<L}(1 + zα_j) - Π_{j<J}(1 + zα_j) Exp_⋆(z Σ_{J≤j<L} α_j)‖ ≤ e^{3RC} R²C²/(J+1)`. -/
theorem norm_prod_range_sub_le (α : ℕ → MeasureAlgebra K) {z : ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hz : ‖z‖ ≤ R) {J L : ℕ} (hJL : J ≤ L) (hmass : ∑ j ∈ Finset.range L, ‖α j‖ ≤ C)
    (htail : ∀ j, J ≤ j → ‖α j‖ ≤ C / (J + 1)) :
    ‖∏ j ∈ Finset.range L, (1 + z • α j) -
        (∏ j ∈ Finset.range J, (1 + z • α j)) * exp (z • ∑ j ∈ Finset.Ico J L, α j)‖ ≤
      Real.exp (3 * (R * C)) * (R ^ 2 * C ^ 2 / (J + 1)) := by
  have hC : 0 ≤ C := (Finset.sum_nonneg fun j _ => norm_nonneg (α j)).trans hmass
  have hsplit : ∑ j ∈ Finset.range J, ‖α j‖ + ∑ j ∈ Finset.Ico J L, ‖α j‖ =
      ∑ j ∈ Finset.range L, ‖α j‖ := Finset.sum_range_add_sum_Ico _ hJL
  have hIco : ∑ j ∈ Finset.Ico J L, ‖α j‖ ≤ C := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range J) => norm_nonneg (α j)
    linarith
  have hJ : ∑ j ∈ Finset.range J, ‖α j‖ ≤ C := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.Ico J L) => norm_nonneg (α j)
    linarith
  rw [← Finset.prod_range_mul_prod_Ico _ hJL, ← mul_sub, Finset.smul_sum]
  refine (norm_mul_le _ _).trans ?_
  have h1 : ‖∏ j ∈ Finset.range J, (1 + z • α j)‖ ≤ Real.exp (R * C) :=
    (norm_prod_one_add_le _ _ hz).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hJ hR))
  have h2 := norm_prod_one_add_sub_exp_le (Finset.Ico J L) fun j => z • α j
  have hn : ∀ j, ‖z • α j‖ ≤ R * ‖α j‖ := fun j => by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hs1 : ∑ j ∈ Finset.Ico J L, ‖z • α j‖ ≤ R * C := by
    calc ∑ j ∈ Finset.Ico J L, ‖z • α j‖ ≤ ∑ j ∈ Finset.Ico J L, R * ‖α j‖ :=
          Finset.sum_le_sum fun j _ => hn j
      _ = R * ∑ j ∈ Finset.Ico J L, ‖α j‖ := by rw [Finset.mul_sum]
      _ ≤ R * C := mul_le_mul_of_nonneg_left hIco hR
  have hs2 : ∑ j ∈ Finset.Ico J L, ‖z • α j‖ ^ 2 ≤ R ^ 2 * C ^ 2 / (J + 1) := by
    calc ∑ j ∈ Finset.Ico J L, ‖z • α j‖ ^ 2
        ≤ ∑ j ∈ Finset.Ico J L, R ^ 2 * (C / (J + 1)) * ‖α j‖ := Finset.sum_le_sum fun j hj => by
          have hjJ : J ≤ j := (Finset.mem_Ico.1 hj).1
          have h3 := hn j
          have h4 := htail j hjJ
          have h5 : ‖z • α j‖ ^ 2 ≤ (R * ‖α j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
          calc ‖z • α j‖ ^ 2 ≤ (R * ‖α j‖) ^ 2 := h5
            _ = R ^ 2 * ‖α j‖ * ‖α j‖ := by ring
            _ ≤ R ^ 2 * (C / (J + 1)) * ‖α j‖ := by
                gcongr
      _ = R ^ 2 * (C / (J + 1)) * ∑ j ∈ Finset.Ico J L, ‖α j‖ := by rw [Finset.mul_sum]
      _ ≤ R ^ 2 * (C / (J + 1)) * C := mul_le_mul_of_nonneg_left hIco (by positivity)
      _ = R ^ 2 * C ^ 2 / (J + 1) := by ring
  calc ‖∏ j ∈ Finset.range J, (1 + z • α j)‖ *
        ‖∏ j ∈ Finset.Ico J L, (1 + z • α j) - exp (∑ j ∈ Finset.Ico J L, z • α j)‖
      ≤ Real.exp (R * C) * (Real.exp (2 * (R * C)) * (R ^ 2 * C ^ 2 / (J + 1))) :=
        mul_le_mul h1 (h2.trans (mul_le_mul (Real.exp_le_exp.2 (by linarith)) hs2
          (Finset.sum_nonneg fun j _ => by positivity) (Real.exp_pos _).le)) (norm_nonneg _)
          (Real.exp_pos _).le
    _ = Real.exp (3 * (R * C)) * (R ^ 2 * C ^ 2 / (J + 1)) := by
        rw [← mul_assoc, ← Real.exp_add]; ring_nf

/-! ### Positive sums and evaluation -/

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem isPositive_sum {ι : Type*} (s : Finset ι) {Φ : ι → MeasureAlgebra K}
    (h : ∀ i ∈ s, IsPositive (Φ i)) : IsPositive (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPositive_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [SecondCountableTopology K] in
theorem norm_sum_of_isPositive {ι : Type*} (s : Finset ι) {Φ : ι → MeasureAlgebra K}
    (h : ∀ i ∈ s, IsPositive (Φ i)) : ‖∑ i ∈ s, Φ i‖ = ∑ i ∈ s, ‖Φ i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, IsPositive.norm_add
      (h a (Finset.mem_insert_self a s)) (isPositive_sum s fun i hi =>
        h i (Finset.mem_insert_of_mem hi)), ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- Evaluation against a test function, as a continuous linear functional on `M(K)`. -/
def evalAt (f : C(K, ℂ)) : MeasureAlgebra K →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun Φ => Φ f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } ‖f‖ fun Φ => by
    rw [mul_comm]; exact le_opNorm Φ f

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
@[simp] theorem evalAt_apply (f : C(K, ℂ)) (Φ : MeasureAlgebra K) : evalAt f Φ = Φ f := rfl

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem tsum_apply {α : ℕ → MeasureAlgebra K} (hα : Summable α) (f : C(K, ℂ)) :
    (∑' j, α j) f = ∑' j, α j f := by
  rw [← evalAt_apply, (evalAt f).map_tsum hα]
  rfl

omit [SecondCountableTopology K] in
/-- Weak-* limits of positive elements carry the limit of the masses. -/
theorem tendsto_norm_of_isPositive {Φ : ℕ → MeasureAlgebra K} {Ψ : MeasureAlgebra K}
    (hΦ : ∀ n, IsPositive (Φ n)) (hΨ : IsPositive Ψ)
    (h : ∀ f, Tendsto (fun n => Φ n f) atTop (𝓝 (Ψ f))) :
    Tendsto (fun n => ‖Φ n‖) atTop (𝓝 ‖Ψ‖) := by
  have := (Complex.continuous_re.tendsto _).comp (h 1)
  rw [IsPositive.norm_eq hΨ]
  exact this.congr fun n => (IsPositive.norm_eq (hΦ n)).symm

/-! ### Ordering a packet by decreasing mass -/

/-- The packet reordered by decreasing mass and padded with zeros. -/
def padded {m : ℕ} (α : Fin m → MeasureAlgebra K) (j : ℕ) : MeasureAlgebra K :=
  if h : j < m then α (Tuple.sort (fun i => -‖α i‖) ⟨j, h⟩) else 0

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem padded_antitone {m : ℕ} (α : Fin m → MeasureAlgebra K) :
    Antitone fun j => ‖padded α j‖ := by
  intro j k hjk
  simp only [padded]
  split_ifs with hk hj hj
  · have := Tuple.monotone_sort (fun i => -‖α i‖) (show (⟨j, hj⟩ : Fin m) ≤ ⟨k, hk⟩ from hjk)
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  · exact absurd (lt_of_le_of_lt hjk hk) hj
  · simp
  · simp

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem padded_of_le {m : ℕ} (α : Fin m → MeasureAlgebra K) {j : ℕ} (hj : m ≤ j) :
    padded α j = 0 := dif_neg (not_lt.2 hj)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem prod_range_padded {m : ℕ} (α : Fin m → MeasureAlgebra K) (z : ℂ) {L : ℕ} (hL : m ≤ L) :
    ∏ j ∈ Finset.range L, (1 + z • padded α j) = formation α z := by
  rw [← Finset.prod_range_mul_prod_Ico _ hL, Finset.prod_eq_one (s := Finset.Ico m L)
    (fun j hj => by rw [padded_of_le α (Finset.mem_Ico.1 hj).1, smul_zero, add_zero]), mul_one,
    ← Fin.prod_univ_eq_prod_range, formation]
  calc ∏ i : Fin m, (1 + z • padded α i)
      = ∏ i : Fin m, (1 + z • α (Tuple.sort (fun i => -‖α i‖) i)) :=
        Finset.prod_congr rfl fun i _ => by simp [padded]
    _ = ∏ i : Fin m, (1 + z • α i) :=
        Equiv.prod_comp (Tuple.sort fun i => -‖α i‖) fun i => 1 + z • α i

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem sum_range_padded {m : ℕ} (α : Fin m → MeasureAlgebra K) {L : ℕ} (hL : m ≤ L) :
    ∑ j ∈ Finset.range L, padded α j = ∑ i, α i := by
  rw [← Finset.sum_range_add_sum_Ico _ hL, Finset.sum_eq_zero (s := Finset.Ico m L) (fun j hj =>
    padded_of_le α (Finset.mem_Ico.1 hj).1), add_zero, ← Fin.sum_univ_eq_sum_range]
  calc ∑ i : Fin m, padded α i = ∑ i : Fin m, α (Tuple.sort (fun i => -‖α i‖) i) :=
        Finset.sum_congr rfl fun i _ => by simp [padded]
    _ = ∑ i : Fin m, α i := Equiv.sum_comp (Tuple.sort fun i => -‖α i‖) α

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem sum_range_norm_padded_le {m : ℕ} (α : Fin m → MeasureAlgebra K) (L : ℕ) :
    ∑ j ∈ Finset.range L, ‖padded α j‖ ≤ packetMass α := by
  have hfull : ∑ j ∈ Finset.range (max L m), ‖padded α j‖ = packetMass α := by
    rw [packetMass, ← Finset.sum_range_add_sum_Ico _ (le_max_right L m), Finset.sum_eq_zero
      (s := Finset.Ico m (max L m)) (fun j hj => by rw [padded_of_le α (Finset.mem_Ico.1 hj).1,
        norm_zero]), add_zero, ← Fin.sum_univ_eq_sum_range]
    calc ∑ i : Fin m, ‖padded α i‖ = ∑ i : Fin m, ‖α (Tuple.sort (fun i => -‖α i‖) i)‖ :=
          Finset.sum_congr rfl fun i _ => by simp [padded]
      _ = ∑ i : Fin m, ‖α i‖ := Equiv.sum_comp (Tuple.sort fun i => -‖α i‖) fun i => ‖α i‖
  rw [← hfull]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left L m))
    fun j _ _ => norm_nonneg _

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- After ordering, the `j`-th factor has mass `≤ |A|_1/(j+1)`. -/
theorem norm_padded_le {m : ℕ} (α : Fin m → MeasureAlgebra K) (j : ℕ) :
    ‖padded α j‖ ≤ packetMass α / (j + 1) := by
  rw [le_div_iff₀ (by positivity)]
  calc ‖padded α j‖ * (j + 1) = ∑ _i ∈ Finset.range (j + 1), ‖padded α j‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ∑ i ∈ Finset.range (j + 1), ‖padded α i‖ := Finset.sum_le_sum fun i hi =>
        padded_antitone α (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    _ ≤ packetMass α := sum_range_norm_padded_le α (j + 1)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem isPositive_padded {m : ℕ} {α : Fin m → MeasureAlgebra K} (h : ∀ i, IsPositive (α i))
    (j : ℕ) : IsPositive (padded α j) := by
  unfold padded
  split_ifs
  · exact h _
  · exact isPositive_zero

/-! ### Approximation by finitely many factors and an exponential -/

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- A finite packet formation is within `e^{3RC} R²C²/(J+1)` of its first `J` ordered factors
times the exponential of the remaining mass. -/
theorem norm_formation_sub_le {m : ℕ} (A : Fin m → MeasureAlgebra K) {R C : ℝ} (hR : 0 ≤ R)
    (hmass : packetMass A ≤ C) {z : ℂ} (hz : ‖z‖ ≤ R) (J : ℕ) :
    ‖formation A z - (∏ j ∈ Finset.range J, (1 + z • padded A j)) *
        exp (z • (∑ i, A i - ∑ j ∈ Finset.range J, padded A j))‖ ≤
      Real.exp (3 * (R * C)) * (R ^ 2 * C ^ 2 / (J + 1)) := by
  have hC : 0 ≤ C := (Finset.sum_nonneg fun i _ => norm_nonneg (A i)).trans hmass
  rw [← prod_range_padded A z (le_max_right J m), ← sum_range_padded A (le_max_right J m),
    ← Finset.sum_Ico_eq_sub _ (le_max_left J m)]
  refine norm_prod_range_sub_le _ hR hz (le_max_left J m)
    ((sum_range_norm_padded_le A _).trans hmass) fun j hj => (norm_padded_le A j).trans ?_
  calc packetMass A / (j + 1) ≤ C / (j + 1) := div_le_div_of_nonneg_right hmass (by positivity)
    _ ≤ C / (J + 1) := div_le_div_of_nonneg_left hC (by positivity) (by
        have : (J : ℝ) ≤ j := by exact_mod_cast hj
        linarith)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- A decorated formation is within `e^{4RC} R²C²/(J+1)` of its first `J` factors times the
exponential of the remaining mass. -/
theorem norm_decorated_sub_le {γ : MeasureAlgebra K} {α : ℕ → MeasureAlgebra K}
    (hα : Summable fun j => ‖α j‖) {R C : ℝ} (hR : 0 ≤ R) (hγ : ‖γ‖ ≤ C)
    (hmass : ∑' j, ‖α j‖ ≤ C) (htail : ∀ j, ‖α j‖ ≤ C / (j + 1)) {z : ℂ} (hz : ‖z‖ ≤ R)
    (J : ℕ) :
    ‖decorated γ α z - (∏ j ∈ Finset.range J, (1 + z • α j)) *
        exp (z • (γ + ∑' j, α j - ∑ j ∈ Finset.range J, α j))‖ ≤
      Real.exp (R * C) * (Real.exp (3 * (R * C)) * (R ^ 2 * C ^ 2 / (J + 1))) := by
  have hC : 0 ≤ C := (norm_nonneg γ).trans hγ
  have hsum : Summable α := Summable.of_norm hα
  set PJ := ∏ j ∈ Finset.range J, (1 + z • α j)
  set E := exp (z • γ)
  set SJ := ∑ j ∈ Finset.range J, α j
  have hE : ‖E‖ ≤ Real.exp (R * C) := (norm_exp_le _).trans (Real.exp_le_exp.2 (by
    rw [norm_smul]; exact mul_le_mul hz hγ (norm_nonneg _) hR))
  have hbound : ∀ L, J ≤ L → ‖E * ∏ j ∈ Finset.range L, (1 + z • α j) -
      PJ * exp (z • (γ + (∑ j ∈ Finset.range L, α j - SJ)))‖ ≤
      Real.exp (R * C) * (Real.exp (3 * (R * C)) * (R ^ 2 * C ^ 2 / (J + 1))) := fun L hL => by
    have h1 := norm_prod_range_sub_le α hR hz hL
      ((hα.sum_le_tsum _ fun j _ => norm_nonneg _).trans hmass) fun j hj => (htail j).trans
        (div_le_div_of_nonneg_left hC (by positivity) (by
          have : (J : ℝ) ≤ j := by exact_mod_cast hj
          linarith))
    rw [Finset.sum_Ico_eq_sub _ hL] at h1
    set PL := ∏ j ∈ Finset.range L, (1 + z • α j)
    set X := exp (z • (∑ j ∈ Finset.range L, α j - SJ))
    have he : E * PL - PJ * exp (z • (γ + (∑ j ∈ Finset.range L, α j - SJ))) =
        E * (PL - PJ * X) := by
      rw [smul_add, exp_add]
      ring
    rw [he]
    exact (norm_mul_le _ _).trans (mul_le_mul hE h1 (norm_nonneg _) (Real.exp_pos _).le)
  have hS : Tendsto (fun L => γ + (∑ j ∈ Finset.range L, α j - SJ)) atTop
      (𝓝 (γ + (∑' j, α j - SJ))) :=
    tendsto_const_nhds.add ((hsum.hasSum.tendsto_sum_nat).sub tendsto_const_nhds)
  have hX : Tendsto (fun L => PJ * exp (z • (γ + (∑ j ∈ Finset.range L, α j - SJ)))) atTop
      (𝓝 (PJ * exp (z • (γ + (∑' j, α j - SJ))))) :=
    tendsto_const_nhds.mul ((exp_continuous.tendsto _).comp (hS.const_smul z))
  have hP : Tendsto (fun L => E * ∏ j ∈ Finset.range L, (1 + z • α j)) atTop
      (𝓝 (decorated γ α z)) :=
    tendsto_const_nhds.mul (multipliable_formation hα z).tendsto_prod_tprod_nat
  have hlim := (hP.sub hX).norm
  rw [show γ + ∑' j, α j - SJ = γ + (∑' j, α j - SJ) by abel]
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop J] with L hL
  exact hbound L hL

/-! ### Theorem 4.1 -/

omit [SecondCountableTopology K] in
theorem IsPositive.apply_one {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) :
    Φ 1 = ((‖Φ‖ : ℝ) : ℂ) := by
  rw [IsPositive.norm_eq hΦ]
  have h := hΦ.apply_realToComplex 1
  have h1 : realToComplex (1 : C(K, ℝ)) = 1 := by ext x; simp
  rwa [h1] at h

omit [SecondCountableTopology K] in
theorem norm_sub_le_of_isPositive {Φ Ψ : MeasureAlgebra K} (hΨ : IsPositive Ψ)
    (hd : IsPositive (Φ - Ψ)) : ‖Φ - Ψ‖ + ‖Ψ‖ = ‖Φ‖ := by
  rw [← IsPositive.norm_add hd hΨ, sub_add_cancel]

/-- **Theorem 4.1: Poisson-dust subsequential compactification.**  Positive
packets of mass `≤ C` have a subsequence whose formations converge in the compact-open weak
topology to `Exp_⋆(z γ) ⋆ Π_j (δ_1 + z α_j)`, with positive dust `γ`, positive atoms `α_j`, and
`‖γ‖ + Σ_j ‖α_j‖ ≤ C`. -/
theorem poissonDust_compactification {m : ℕ → ℕ} (A : (N : ℕ) → Fin (m N) → MeasureAlgebra K)
    {C : ℝ} (hpos : ∀ N j, IsPositive (A N j)) (hmass : ∀ N, packetMass (A N) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K),
      IsPositive γ ∧ (∀ j, IsPositive (α j)) ∧ Summable (fun j => ‖α j‖) ∧
      ‖γ‖ + ∑' j, ‖α j‖ ≤ C ∧ FormConv (fun n => formation (A (φ n))) (decorated γ α) := by
  classical
  set Γ : ℕ → MeasureAlgebra K := fun N => ∑ i, A N i
  have hΓpos : ∀ N, IsPositive (Γ N) := fun N => isPositive_sum _ fun i _ => hpos N i
  have hΓnorm : ∀ N, ‖Γ N‖ ≤ C := fun N => by
    rw [norm_sum_of_isPositive _ fun i _ => hpos N i]; exact hmass N
  have hC : 0 ≤ C := (norm_nonneg _).trans (hΓnorm 0)
  set p : ℕ → ℕ → MeasureAlgebra K := fun N j => padded (A N) j
  have hppos : ∀ N j, IsPositive (p N j) := fun N j => isPositive_padded (hpos N) j
  have hpnorm : ∀ N j, ‖p N j‖ ≤ C / (j + 1) := fun N j =>
    (norm_padded_le _ j).trans (div_le_div_of_nonneg_right (hmass N) (by positivity))
  have hpnorm' : ∀ N j, ‖p N j‖ ≤ C := fun N j =>
    (hpnorm N j).trans (div_le_self hC (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith))
  -- one subsequence for the totals and every ordered factor
  set x : ℕ → ℕ → MeasureAlgebra K := fun N j => match j with
    | 0 => Γ N
    | j + 1 => p N j
  have hx : ∀ N j, IsPositive (x N j) ∧ ‖x N j‖ ≤ C := fun N j => by
    cases j with
    | zero => exact ⟨hΓpos N, hΓnorm N⟩
    | succ j => exact ⟨hppos N j, hpnorm' N j⟩
  obtain ⟨φ, hφ, y, hy⟩ := exists_diagonal_positive C x hx
  set G := y 0
  set α : ℕ → MeasureAlgebra K := fun j => y (j + 1)
  have hGpos : IsPositive G := (hy 0).1
  have hGnorm : ‖G‖ ≤ C := (hy 0).2.1
  have hG : ∀ f, Tendsto (fun n => Γ (φ n) f) atTop (𝓝 (G f)) := (hy 0).2.2
  have hαpos : ∀ j, IsPositive (α j) := fun j => (hy (j + 1)).1
  have hα : ∀ j f, Tendsto (fun n => p (φ n) j f) atTop (𝓝 (α j f)) := fun j => (hy (j + 1)).2.2
  have hαnorm : ∀ j, ‖α j‖ ≤ C / (j + 1) := fun j =>
    le_of_tendsto' (tendsto_norm_of_isPositive (fun n => hppos _ j) (hαpos j) (hα j))
      fun n => hpnorm _ j
  have hαnorm' : ∀ j, ‖α j‖ ≤ C := fun j =>
    (hαnorm j).trans (div_le_self hC (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith))
  -- the positive tails
  have htail_pos : ∀ N J, IsPositive (Γ N - ∑ j ∈ Finset.range J, p N j) := fun N J => by
    have h := sum_range_padded (A N) (le_max_right J (m N))
    rw [← Finset.sum_range_add_sum_Ico _ (le_max_left J (m N))] at h
    show IsPositive (∑ i, A N i - ∑ j ∈ Finset.range J, padded (A N) j)
    rw [← h, add_sub_cancel_left]
    exact isPositive_sum _ fun j _ => hppos N j
  have htail_norm : ∀ N J, ‖Γ N - ∑ j ∈ Finset.range J, p N j‖ ≤ C := fun N J => by
    have h := norm_sub_le_of_isPositive (isPositive_sum (Finset.range J) fun j _ => hppos N j)
      (htail_pos N J)
    linarith [norm_nonneg (∑ j ∈ Finset.range J, p N j), hΓnorm N]
  have hlimtail : ∀ J f, Tendsto (fun n => (Γ (φ n) - ∑ j ∈ Finset.range J, p (φ n) j) f)
      atTop (𝓝 ((G - ∑ j ∈ Finset.range J, α j) f)) := fun J f => by
    simp only [MeasureAlgebra.sub_apply, MeasureAlgebra.sum_apply]
    exact (hG f).sub (tendsto_finsetSum _ fun j _ => hα j f)
  have hGtail_pos : ∀ J, IsPositive (G - ∑ j ∈ Finset.range J, α j) := fun J =>
    isPositive_of_tendsto (fun n => htail_pos (φ n) J) (hlimtail J)
  have hpartial : ∀ J, ∑ j ∈ Finset.range J, ‖α j‖ ≤ ‖G‖ := fun J => by
    have h := norm_sub_le_of_isPositive (isPositive_sum (Finset.range J) fun j _ => hαpos j)
      (hGtail_pos J)
    rw [norm_sum_of_isPositive _ fun j _ => hαpos j] at h
    linarith [norm_nonneg (G - ∑ j ∈ Finset.range J, α j)]
  have hGtail_norm : ∀ J, ‖G - ∑ j ∈ Finset.range J, α j‖ ≤ C := fun J => by
    have h := norm_sub_le_of_isPositive (isPositive_sum (Finset.range J) fun j _ => hαpos j)
      (hGtail_pos J)
    linarith [norm_nonneg (∑ j ∈ Finset.range J, α j)]
  have hsummable : Summable fun j => ‖α j‖ :=
    summable_of_sum_range_le (fun j => norm_nonneg _) hpartial
  have hsumα : Summable α := Summable.of_norm hsummable
  set γ := G - ∑' j, α j
  have hγpos : IsPositive γ := isPositive_of_tendsto (fun J => hGtail_pos J) fun f =>
    ((evalAt f).continuous.tendsto _).comp (tendsto_const_nhds.sub hsumα.hasSum.tendsto_sum_nat)
  have hmass_eq : ‖γ‖ + ∑' j, ‖α j‖ = ‖G‖ := by
    have h1 : (∑' j, α j) 1 = ((∑' j, ‖α j‖ : ℝ) : ℂ) := by
      rw [tsum_apply hsumα, Complex.ofReal_tsum]
      exact tsum_congr fun j => IsPositive.apply_one (hαpos j)
    have h2 := IsPositive.norm_eq hγpos
    rw [MeasureAlgebra.sub_apply, h1, Complex.sub_re, Complex.ofReal_re,
      ← IsPositive.norm_eq hGpos] at h2
    linarith
  have htn : (0 : ℝ) ≤ ∑' j, ‖α j‖ := tsum_nonneg fun j => norm_nonneg (α j)
  have hγnorm : ‖γ‖ ≤ C := by linarith
  have hαtsum : ∑' j, ‖α j‖ ≤ C := by linarith [norm_nonneg γ]
  refine ⟨φ, hφ, γ, α, hγpos, hαpos, hsummable, by linarith, fun R f => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set R' := max R 0
  have hR' : 0 ≤ R' := le_max_right R 0
  have hz' : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖z‖ ≤ R' := fun z hz =>
    (mem_closedBall_zero_iff.1 hz).trans (le_max_left _ _)
  set T := (Real.exp (R' * C) * Real.exp (3 * (R' * C)) + Real.exp (3 * (R' * C))) *
    (R' ^ 2 * C ^ 2) * (‖f‖ + 1)
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 * T / ε)
  have hJ' : T / (J + 1) < ε / 2 := by
    rw [div_lt_iff₀ hε] at hJ
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [show 0 ≤ T by positivity]
  -- the fixed-`J` approximants converge
  have hD : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have hQ := WeakUnifOn.mul hD
    (weakUnifOn_prod_range (fun n j => p (φ n) j) α hD subset_rfl (c := fun _ => C)
      (fun n j => hpnorm' _ j) hαnorm' hα J)
    (weakUnifOn_exp (fun n => Γ (φ n) - ∑ j ∈ Finset.range J, p (φ n) j)
      (G - ∑ j ∈ Finset.range J, α j) (fun n => htail_norm _ J) (hGtail_norm J) (hlimtail J) hD
      subset_rfl)
    (B := Real.exp (R' * C)) (B' := Real.exp (R' * C))
    (fun n z hz => (norm_prod_one_add_le _ _ (hz' z hz)).trans (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left ((sum_range_norm_padded_le _ J).trans (hmass _)) hR')))
    (fun z hz => (norm_prod_one_add_le _ _ (hz' z hz)).trans (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left ((hpartial J).trans hGnorm) hR')))
    (fun n z hz => (norm_exp_le _).trans (Real.exp_le_exp.2 (by
      rw [norm_smul]; exact mul_le_mul (hz' z hz) (htail_norm _ J) (norm_nonneg _) hR')))
    (fun z hz => (norm_exp_le _).trans (Real.exp_le_exp.2 (by
      rw [norm_smul]; exact mul_le_mul (hz' z hz) (hGtail_norm J) (norm_nonneg _) hR')))
    ((exp_continuous.comp (continuous_id.smul continuous_const)).continuousOn)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hQ f) (ε / 2) (by positivity)] with n hn z hz
  have e1 := norm_formation_sub_le (A (φ n)) hR' (hmass _) (hz' z hz) J
  have e2 := norm_decorated_sub_le hsummable hR' hγnorm hαtsum hαnorm (hz' z hz) J
  rw [show γ + ∑' j, α j - ∑ j ∈ Finset.range J, α j = G - ∑ j ∈ Finset.range J, α j by
    simp only [γ, sub_add_cancel]] at e2
  have h3 := hn z hz
  rw [dist_eq_norm] at h3 ⊢
  set Qn := (∏ j ∈ Finset.range J, (1 + z • p (φ n) j)) *
    exp (z • (Γ (φ n) - ∑ j ∈ Finset.range J, p (φ n) j))
  set Q := (∏ j ∈ Finset.range J, (1 + z • α j)) * exp (z • (G - ∑ j ∈ Finset.range J, α j))
  have f1 : ‖decorated γ α z f - Q f‖ ≤
      ‖f‖ * (Real.exp (R' * C) * (Real.exp (3 * (R' * C)) * (R' ^ 2 * C ^ 2 / (J + 1)))) := by
    rw [← MeasureAlgebra.sub_apply, mul_comm]
    exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right e2 (norm_nonneg _))
  have f2 : ‖Qn f - formation (A (φ n)) z f‖ ≤
      ‖f‖ * (Real.exp (3 * (R' * C)) * (R' ^ 2 * C ^ 2 / (J + 1))) := by
    rw [← MeasureAlgebra.sub_apply, mul_comm]
    refine (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [norm_sub_rev]
    exact e1
  have hsumT : ‖f‖ * (Real.exp (R' * C) * (Real.exp (3 * (R' * C)) * (R' ^ 2 * C ^ 2 / (J + 1))))
      + ‖f‖ * (Real.exp (3 * (R' * C)) * (R' ^ 2 * C ^ 2 / (J + 1))) ≤ T / (J + 1) := by
    simp only [T]
    rw [le_div_iff₀ (by positivity)]
    have hJ0 : (0 : ℝ) < J + 1 := by positivity
    field_simp
    nlinarith [Real.exp_pos (R' * C), Real.exp_pos (3 * (R' * C)), sq_nonneg R', sq_nonneg C,
      norm_nonneg f, mul_pos (Real.exp_pos (R' * C)) (Real.exp_pos (3 * (R' * C)))]
  calc ‖decorated γ α z f - formation (A (φ n)) z f‖
      = ‖(decorated γ α z f - Q f) + (Q f - Qn f) + (Qn f - formation (A (φ n)) z f)‖ := by
        ring_nf
    _ ≤ ‖decorated γ α z f - Q f‖ + ‖Q f - Qn f‖ + ‖Qn f - formation (A (φ n)) z f‖ :=
        norm_add₃_le
    _ < ε := by linarith

/-! ### Theorem 5.1: every decorated formation is a limit of finite packets -/

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- `‖Π_{j∈s}(1 + zα_j) - 1‖ ≤ e^{R Σ‖α_j‖} R Σ‖α_j‖` for `‖z‖ ≤ R`. -/
theorem norm_prod_one_add_sub_one_le (s : Finset ℕ) (α : ℕ → MeasureAlgebra K) {z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖∏ j ∈ s, (1 + z • α j) - 1‖ ≤ Real.exp (R * ∑ j ∈ s, ‖α j‖) * (R * ∑ j ∈ s, ‖α j‖) := by
  have h := norm_prod_sub_prod_le s (fun j => 1 + z • α j) (fun _ => 1)
    (fun j => Real.exp (R * ‖α j‖)) (fun j _ => Real.one_le_exp (mul_nonneg hR (norm_nonneg _)))
    (fun j _ => norm_one_add_smul_le (α j) hz)
    (fun j _ => by rw [norm_one]; exact Real.one_le_exp (mul_nonneg hR (norm_nonneg _)))
  rw [Finset.prod_const_one, ← Real.exp_sum, ← Finset.mul_sum] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    rw [add_sub_cancel_left, norm_smul]; exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- The partial products converge to the infinite product at the rate of the mass tail:
`‖Π_j (1 + zα_j) - Π_{j<N}(1 + zα_j)‖ ≤ e^{2RC} R Σ_{j≥N} ‖α_j‖`. -/
theorem norm_tprod_sub_prod_range_le {α : ℕ → MeasureAlgebra K} (hα : Summable fun j => ‖α j‖)
    {C R : ℝ} (hR : 0 ≤ R) (hmass : ∑' j, ‖α j‖ ≤ C) {z : ℂ} (hz : ‖z‖ ≤ R) (N : ℕ) :
    ‖∏' j, (1 + z • α j) - ∏ j ∈ Finset.range N, (1 + z • α j)‖ ≤
      Real.exp (R * C) * (Real.exp (R * C) * (R * ∑' j, ‖α (j + N)‖)) := by
  have htail : ∀ L, ∑ j ∈ Finset.Ico N L, ‖α j‖ ≤ ∑' j, ‖α (j + N)‖ := fun L => by
    rw [Finset.sum_Ico_eq_sum_range]
    simp_rw [add_comm N]
    exact ((summable_nat_add_iff N).2 hα).sum_le_tsum _ fun j _ => norm_nonneg _
  have htC : ∑' j, ‖α (j + N)‖ ≤ C := by
    have := hα.sum_add_tsum_nat_add N
    have h0 := Finset.sum_nonneg fun j (_ : j ∈ Finset.range N) => norm_nonneg (α j)
    linarith
  have hN : ∑ j ∈ Finset.range N, ‖α j‖ ≤ C :=
    (hα.sum_le_tsum _ fun j _ => norm_nonneg _).trans hmass
  have hbound : ∀ L, N ≤ L → ‖∏ j ∈ Finset.range L, (1 + z • α j) -
      ∏ j ∈ Finset.range N, (1 + z • α j)‖ ≤
      Real.exp (R * C) * (Real.exp (R * C) * (R * ∑' j, ‖α (j + N)‖)) := fun L hL => by
    rw [← Finset.prod_range_mul_prod_Ico _ hL,
      show ∀ a b : MeasureAlgebra K, a * b - a = a * (b - 1) from fun a b => by ring]
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_prod_one_add_le _ _ hz).trans
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hN hR)))
      ((norm_prod_one_add_sub_one_le _ α hR hz).trans ?_) (norm_nonneg _) (Real.exp_pos _).le)
    exact mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((htail L).trans htC) hR))
      (mul_le_mul_of_nonneg_left (htail L) hR)
      (mul_nonneg hR (Finset.sum_nonneg fun j _ => norm_nonneg _)) (Real.exp_pos _).le
  exact le_of_tendsto (((multipliable_formation hα z).tendsto_prod_tprod_nat).sub
    tendsto_const_nhds).norm (eventually_atTop.2 ⟨N, hbound⟩)

/-- The packet `(α_0, …, α_{N-1}, γ/N, …, γ/N)` with `N` copies of `γ/N`. -/
def realizingPacket (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) (N : ℕ) :
    Fin (N + N) → MeasureAlgebra K :=
  Fin.append (fun j : Fin N => α j) fun _ => (N : ℂ)⁻¹ • γ

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem formation_realizingPacket (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) (N : ℕ)
    (z : ℂ) : formation (realizingPacket γ α N) z =
      (∏ j ∈ Finset.range N, (1 + z • α j)) * (1 + z • ((N : ℂ)⁻¹ • γ)) ^ N := by
  rw [formation, Fin.prod_univ_add]
  simp only [realizingPacket, Fin.append_left, Fin.append_right, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fin.prod_univ_eq_prod_range (fun j => 1 + z • α j) N]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem packetMass_realizingPacket_le (γ : MeasureAlgebra K) {α : ℕ → MeasureAlgebra K}
    (hα : Summable fun j => ‖α j‖) (N : ℕ) :
    packetMass (realizingPacket γ α N) ≤ ‖γ‖ + ∑' j, ‖α j‖ := by
  rw [packetMass, Fin.sum_univ_add]
  simp only [realizingPacket, Fin.append_left, Fin.append_right, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j => ‖α j‖) N]
  have h1 : (N : ℝ) * ‖(N : ℂ)⁻¹ • γ‖ ≤ ‖γ‖ := by
    rw [norm_smul, norm_inv, Complex.norm_natCast, ← mul_assoc]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [mul_inv_cancel₀ (by positivity), one_mul]
  have h2 := hα.sum_le_tsum (Finset.range N) fun j _ => norm_nonneg _
  linarith

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem isPositive_realizingPacket {γ : MeasureAlgebra K} {α : ℕ → MeasureAlgebra K}
    (hγ : IsPositive γ) (hα : ∀ j, IsPositive (α j)) (N : ℕ) (i : Fin (N + N)) :
    IsPositive (realizingPacket γ α N i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [realizingPacket, Fin.append_left]
    exact hα j
  · simp only [realizingPacket, Fin.append_right]
    have h := IsPositive.smul hγ (c := (N : ℝ)⁻¹) (by positivity)
    rwa [Complex.ofReal_inv, Complex.ofReal_natCast] at h

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- The realization error: for `‖z‖ ≤ R` and `‖γ‖ + Σ_j ‖α_j‖ ≤ C`,
`‖Λ_{A_N}(z) - Exp_⋆(zγ) Π_j (1 + zα_j)‖ ≤ e^{3RC} (R²C²/N + R Σ_{j≥N} ‖α_j‖)`. -/
theorem norm_formation_realizingPacket_sub_le {γ : MeasureAlgebra K} {α : ℕ → MeasureAlgebra K}
    (hα : Summable fun j => ‖α j‖) {C R : ℝ} (hR : 0 ≤ R) (hmass : ‖γ‖ + ∑' j, ‖α j‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ R) {N : ℕ} (hN : 0 < N) :
    ‖formation (realizingPacket γ α N) z - decorated γ α z‖ ≤
      Real.exp (3 * (R * C)) * (R ^ 2 * C ^ 2 / N + R * ∑' j, ‖α (j + N)‖) := by
  have ht0 : 0 ≤ ∑' j, ‖α j‖ := tsum_nonneg fun j => norm_nonneg _
  have hγC : ‖γ‖ ≤ C := by linarith
  have hαC : ∑' j, ‖α j‖ ≤ C := by linarith [norm_nonneg γ]
  rw [formation_realizingPacket, decorated]
  set P := ∏ j ∈ Finset.range N, (1 + z • α j)
  set Q := (1 + z • ((N : ℂ)⁻¹ • γ)) ^ N
  set E := exp (z • γ)
  set T := ∏' j, (1 + z • α j)
  have hP : ‖P‖ ≤ Real.exp (R * C) := (norm_prod_one_add_le _ _ hz).trans (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left ((hα.sum_le_tsum _ fun j _ => norm_nonneg _).trans hαC) hR))
  have hE : ‖E‖ ≤ Real.exp (R * C) := (norm_exp_le _).trans (Real.exp_le_exp.2 (by
    rw [norm_smul]; exact mul_le_mul hz hγC (norm_nonneg _) hR))
  have hQ : ‖Q - E‖ ≤ Real.exp (2 * (R * C)) * (R ^ 2 * C ^ 2 / N) := by
    have h := norm_pow_approx_exp_le γ hR hz hγC hN
    rwa [Finset.prod_const, Finset.card_range] at h
  have hT := norm_tprod_sub_prod_range_le hα hR hαC hz N
  have he : P * Q - E * T = P * (Q - E) - E * (T - P) := by ring
  have ht : 0 ≤ R * ∑' j, ‖α (j + N)‖ := mul_nonneg hR (tsum_nonneg fun j => norm_nonneg _)
  have h2 : Real.exp (2 * (R * C)) = Real.exp (R * C) * Real.exp (R * C) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (3 * (R * C)) = Real.exp (R * C) * Real.exp (R * C) * Real.exp (R * C) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [he]
  refine (norm_sub_le _ _).trans ?_
  calc ‖P * (Q - E)‖ + ‖E * (T - P)‖
      ≤ Real.exp (R * C) * (Real.exp (2 * (R * C)) * (R ^ 2 * C ^ 2 / N)) +
          Real.exp (R * C) * (Real.exp (R * C) * (Real.exp (R * C) * (R * ∑' j, ‖α (j + N)‖))) :=
        add_le_add ((norm_mul_le _ _).trans (mul_le_mul hP hQ (norm_nonneg _) (Real.exp_pos _).le))
          ((norm_mul_le _ _).trans (mul_le_mul hE hT (norm_nonneg _) (Real.exp_pos _).le))
    _ = Real.exp (3 * (R * C)) * (R ^ 2 * C ^ 2 / N + R * ∑' j, ‖α (j + N)‖) := by
        rw [h2, h3]; ring

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- The formations of the realizing packets converge in norm to the decorated formation,
uniformly on every disc. -/
theorem tendstoUniformlyOn_formation_realizingPacket {γ : MeasureAlgebra K}
    {α : ℕ → MeasureAlgebra K} (hα : Summable fun j => ‖α j‖) (R : ℝ) :
    TendstoUniformlyOn (fun N => formation (realizingPacket γ α N)) (decorated γ α) atTop
      (Metric.closedBall 0 R) := by
  set R' := max R 0
  set C := ‖γ‖ + ∑' j, ‖α j‖
  have hb : Tendsto (fun N : ℕ => Real.exp (3 * (R' * C)) *
      (R' ^ 2 * C ^ 2 / N + R' * ∑' j, ‖α (j + N)‖)) atTop (𝓝 0) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat (R' ^ 2 * C ^ 2)).add
      ((tendsto_sum_nat_add fun j => ‖α j‖).const_mul R')).const_mul (Real.exp (3 * (R' * C)))
    rwa [show Real.exp (3 * (R' * C)) * (0 + R' * 0) = 0 by ring] at this
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hb.eventually (gt_mem_nhds hε), eventually_gt_atTop 0] with N hN hN0 z hz
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_formation_realizingPacket_sub_le hα (le_max_right R 0) le_rfl
    ((mem_closedBall_zero_iff.1 hz).trans (le_max_left _ _)) hN0).trans_lt hN

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- Norm convergence uniformly on every disc implies compact-open weak convergence. -/
theorem formConv_of_tendstoUniformlyOn {F : ℕ → ℂ → MeasureAlgebra K} {G : ℂ → MeasureAlgebra K}
    (h : ∀ R, TendstoUniformlyOn F G atTop (Metric.closedBall 0 R)) : FormConv F G :=
  fun R f => by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (h R) (ε / (‖f‖ + 1)) (by positivity)]
    with n hn z hz
  have hn := hn z hz
  rw [dist_eq_norm] at hn ⊢
  rw [← MeasureAlgebra.sub_apply]
  calc ‖(G z - F n z) f‖ ≤ ‖G z - F n z‖ * ‖f‖ := le_opNorm _ _
    _ ≤ ε / (‖f‖ + 1) * ‖f‖ := mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg f]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **Theorem 5.1: every dust boundary is a packet limit.**  If `γ, α_j` are positive with
`‖γ‖ + Σ_j ‖α_j‖ ≤ C`, the decorated formation `Exp_⋆(zγ) ⋆ Π_j (δ_1 + zα_j)` is the
compact-open weak limit (indeed the norm limit, uniformly on compact sets) of the formations of
positive finite packets of mass `≤ C`. -/
theorem decorated_isLimit {γ : MeasureAlgebra K} {α : ℕ → MeasureAlgebra K} (hγ : IsPositive γ)
    (hα : ∀ j, IsPositive (α j)) (hs : Summable fun j => ‖α j‖) {C : ℝ}
    (hmass : ‖γ‖ + ∑' j, ‖α j‖ ≤ C) :
    ∃ (m : ℕ → ℕ) (A : (N : ℕ) → Fin (m N) → MeasureAlgebra K), (∀ N j, IsPositive (A N j)) ∧
      (∀ N, packetMass (A N) ≤ C) ∧
      (∀ R, TendstoUniformlyOn (fun N => formation (A N)) (decorated γ α) atTop
        (Metric.closedBall 0 R)) ∧
      FormConv (fun N => formation (A N)) (decorated γ α) :=
  ⟨fun N => N + N, realizingPacket γ α, isPositive_realizingPacket hγ hα,
    fun N => (packetMass_realizingPacket_le γ hs N).trans hmass,
    tendstoUniformlyOn_formation_realizingPacket hs,
    formConv_of_tendstoUniformlyOn (tendstoUniformlyOn_formation_realizingPacket hs)⟩

/-! ### Corollary 5.2: the closure of finite formations, sequentially -/

/-- The decorated formations obeying the mass law `‖γ‖ + Σ_j ‖α_j‖ ≤ C`. -/
def decoratedSet (C : ℝ) : Set (ℂ → MeasureAlgebra K) :=
  {F | ∃ (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K), IsPositive γ ∧
    (∀ j, IsPositive (α j)) ∧ Summable (fun j => ‖α j‖) ∧ ‖γ‖ + ∑' j, ‖α j‖ ≤ C ∧
    F = decorated γ α}

/-- The formations of positive finite packets of mass `≤ C`. -/
def packetFormationSet (C : ℝ) : Set (ℂ → MeasureAlgebra K) :=
  {F | ∃ (m : ℕ) (A : Fin m → MeasureAlgebra K), (∀ j, IsPositive (A j)) ∧ packetMass A ≤ C ∧
    F = formation A}

omit [CompactSpace K] [T2Space K] [SecondCountableTopology K] [CommMonoid K] [ContinuousMul K]
  [MeasurableSpace K] [BorelSpace K] in
theorem FormConv.unique {F : ℕ → ℂ → MeasureAlgebra K} {G G' : ℂ → MeasureAlgebra K}
    (h : FormConv F G) (h' : FormConv F G') : G = G' := by
  funext z
  ext f
  exact tendsto_nhds_unique ((h ‖z‖ f).tendsto_at (mem_closedBall_zero_iff.2 le_rfl))
    ((h' ‖z‖ f).tendsto_at (mem_closedBall_zero_iff.2 le_rfl))

omit [CompactSpace K] [T2Space K] [SecondCountableTopology K] [CommMonoid K] [ContinuousMul K]
  [MeasurableSpace K] [BorelSpace K] in
theorem FormConv.comp {F : ℕ → ℂ → MeasureAlgebra K} {G : ℂ → MeasureAlgebra K}
    (h : FormConv F G) {φ : ℕ → ℕ} (hφ : StrictMono φ) : FormConv (F ∘ φ) G := fun R f => by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact hφ.tendsto_atTop.eventually (Metric.tendstoUniformlyOn_iff.1 (h R f) ε hε)

/-- **Corollary 5.2, closure.**  A compact-open weak limit of formations of positive packets of
mass `≤ C` is a decorated formation obeying the mass law. -/
theorem mem_decoratedSet_of_formConv {m : ℕ → ℕ} {A : (N : ℕ) → Fin (m N) → MeasureAlgebra K}
    {C : ℝ} (hpos : ∀ N j, IsPositive (A N j)) (hmass : ∀ N, packetMass (A N) ≤ C)
    {G : ℂ → MeasureAlgebra K} (h : FormConv (fun N => formation (A N)) G) :
    G ∈ decoratedSet C := by
  obtain ⟨φ, hφ, γ, α, hγ, hα, hs, hm, hconv⟩ := poissonDust_compactification A hpos hmass
  exact ⟨γ, α, hγ, hα, hs, hm, (h.comp hφ).unique hconv⟩

/-- **Corollary 5.2, exact closure.**  The sequential compact-open weak limits of positive finite
formations of mass `≤ C` are exactly the decorated formations obeying the mass law. -/
theorem mem_decoratedSet_iff {C : ℝ} {G : ℂ → MeasureAlgebra K} :
    G ∈ decoratedSet C ↔
      ∃ F : ℕ → ℂ → MeasureAlgebra K, (∀ n, F n ∈ packetFormationSet C) ∧ FormConv F G := by
  constructor
  · rintro ⟨γ, α, hγ, hα, hs, hm, rfl⟩
    obtain ⟨m, A, hpos, hmass, -, hconv⟩ := decorated_isLimit hγ hα hs hm
    exact ⟨fun N => formation (A N), fun N => ⟨m N, A N, hpos N, hmass N, rfl⟩, hconv⟩
  · rintro ⟨F, hF, hconv⟩
    choose m A hpos hmass hFA using hF
    have hF' : F = fun N => formation (A N) := funext hFA
    subst hF'
    exact mem_decoratedSet_of_formConv hpos hmass hconv

/-- **Corollary 5.2, compactness (sequential form).**  Every sequence of decorated formations
obeying the mass law has a subsequence converging in the compact-open weak topology to a decorated
formation obeying the mass law.  Each term is replaced by a finite packet within `1/(n+1)` on the
disc of radius `n`, and Theorem 4.1 is applied to the packets. -/
theorem decoratedSet_seqCompact {C : ℝ} {F : ℕ → ℂ → MeasureAlgebra K}
    (hF : ∀ n, F n ∈ decoratedSet C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G ∈ decoratedSet C, FormConv (F ∘ φ) G := by
  have happrox : ∀ n : ℕ, ∃ (m : ℕ) (A : Fin m → MeasureAlgebra K), (∀ j, IsPositive (A j)) ∧
      packetMass A ≤ C ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) n,
        ‖F n z - formation A z‖ < 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨γ, α, hγ, hα, hs, hm, hFn⟩ := hF n
    obtain ⟨m, A, hpos, hmass, hunif, -⟩ := decorated_isLimit hγ hα hs hm
    obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 (hunif n) (1 / ((n : ℝ) + 1))
      (by positivity)).exists
    refine ⟨m N, A N, hpos N, hmass N, fun z hz => ?_⟩
    rw [hFn, ← dist_eq_norm]
    exact hN z hz
  choose m A hpos hmass herr using happrox
  obtain ⟨φ, hφ, γ, α, hγ, hα, hs, hm, hconv⟩ := poissonDust_compactification A hpos hmass
  refine ⟨φ, hφ, decorated γ α, ⟨γ, α, hγ, hα, hs, hm, rfl⟩, fun R f => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h2 : ∀ᶠ k in atTop, R ≤ φ k :=
    (hφ.tendsto_atTop.eventually_ge_atTop ⌈R⌉₊).mono fun k hk =>
      (Nat.le_ceil R).trans (by exact_mod_cast hk)
  have h3 : ∀ᶠ k in atTop, 1 / ((φ k : ℝ) + 1) * ‖f‖ < ε / 2 := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).mul_const ‖f‖
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hconv R f) (ε / 2) (by positivity), h2, h3]
    with k hk1 hk2 hk3 z hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) (φ k : ℕ) :=
    mem_closedBall_zero_iff.2 ((mem_closedBall_zero_iff.1 hz).trans hk2)
  have e := herr (φ k) z hz'
  have e1 := hk1 z hz
  rw [dist_eq_norm] at e1 ⊢
  have e2 : ‖formation (A (φ k)) z f - (F ∘ φ) k z f‖ < ε / 2 := by
    rw [← MeasureAlgebra.sub_apply, ← norm_neg, ← MeasureAlgebra.neg_apply, neg_sub]
    calc ‖(F (φ k) z - formation (A (φ k)) z) f‖
        ≤ ‖F (φ k) z - formation (A (φ k)) z‖ * ‖f‖ := le_opNorm _ _
      _ ≤ 1 / ((φ k : ℝ) + 1) * ‖f‖ := mul_le_mul_of_nonneg_right e.le (norm_nonneg _)
      _ < ε / 2 := hk3
  calc ‖decorated γ α z f - (F ∘ φ) k z f‖
      ≤ ‖decorated γ α z f - formation (A (φ k)) z f‖ +
          ‖formation (A (φ k)) z f - (F ∘ φ) k z f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add e1 e2
    _ = ε := add_halves ε

end GaloisForLFunctions.HTGeometry.FormationDust
