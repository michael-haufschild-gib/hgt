import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartOfABlockAndAFarWindowIsMinusTheProductOfTheirCharges
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartOfAWindowOfRatioTwoHasOneNegativeSquareAtEveryBlockSize
import GaloisForLFunctions.HeckeKreinToeplitz.EveryFlipSetHasInfiniteIndexOnTheHeckeLattice

/-!
# The Riemann hypothesis is one negative square of the neutral part of every window

The neutral part of the block matrix of a window `(R, R + J]` is the matrix of the step packets
without the product of the two charges. The Riemann hypothesis holds iff for every window that
contains the dyadic window (`R ≤ J`) the neutral part has exactly one negative square
(`riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one`): the Hodge index theorem for
the step-packet matrices, at finite scale.

Under the Riemann hypothesis the block matrix is nonnegative and its neutral part has one
negative square. Conversely let `σ` be a step packet on the blocks of `(R, R + J]` with
`m(σ) = N(σ) + 2c₀c₁ < 0`, `c₁ = Σσ_j`, `c₀ = Σσ_j d(R + j)`. On the blocks of `(1, 2M]` take

* `u₁`: the refinement of `σ` by `L`, on the blocks above `LR`;
* `u₂ = √L/M` on the blocks `M ≤ b < 2M`;
* `u₃ = 1/√L` on the block one.

The refinement keeps `N(u₁, u₁) = N(σ)`. A block and a far window pair by minus the product of
their charges, so with `ℓ = d(1)` and `n₁ = N(1, 1)`, as `M → ∞` and then `L → ∞`:

  `N(u₁, u₂) → −c₀`,  `N(u₁, u₃) → −ℓc₁`,  `N(u₂, u₃) → −ℓ`,
  `N(u₂, u₂) = L n₁/M → 0`,  `N(u₃, u₃) = n₁/L → 0`.

So `u₂` and `u₃` span a hyperbolic plane in the limit, and on `w₁ = u₁ − c₁u₂ − (c₀/ℓ)u₃`,
`w₂ = u₂ + u₃` the form tends to `diag(m(σ), −2ℓ)`: two negative squares
(`exists_two_le_hermNegIndex_neutralWindow`).
-/

open Finset Filter Topology Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Pairings over rectangles of blocks -/

/-- The pairing of two step functions by a kernel over two sets of blocks. -/
def rectSum (K : ℕ → ℕ → ℝ) (A B : Finset ℕ) (f g : ℕ → ℝ) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ B, f a * g b * K a b

theorem rectSum_comm {K : ℕ → ℕ → ℝ} (hK : ∀ a b, K a b = K b a) (A B : Finset ℕ)
    (f g : ℕ → ℝ) : rectSum K A B f g = rectSum K B A g f := by
  unfold rectSum
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by
    rw [hK a b]
    ring

/-- Step functions supported on two sets of blocks pair over the rectangle of the two sets. -/
theorem rectSum_indicator (K : ℕ → ℕ → ℝ) {T S₁ S₂ : Finset ℕ} (h₁ : S₁ ⊆ T) (h₂ : S₂ ⊆ T)
    (φ ψ : ℕ → ℝ) :
    rectSum K T T (fun b => if b ∈ S₁ then φ b else 0) (fun b => if b ∈ S₂ then ψ b else 0) =
      rectSum K S₁ S₂ φ ψ := by
  show ∑ a ∈ T, ∑ b ∈ T, (if a ∈ S₁ then φ a else 0) * (if b ∈ S₂ then ψ b else 0) * K a b =
    ∑ a ∈ S₁, ∑ b ∈ S₂, φ a * ψ b * K a b
  have h1 : ∑ a ∈ S₁, ∑ b ∈ T,
        (if a ∈ S₁ then φ a else 0) * (if b ∈ S₂ then ψ b else 0) * K a b =
      ∑ a ∈ T, ∑ b ∈ T, (if a ∈ S₁ then φ a else 0) * (if b ∈ S₂ then ψ b else 0) * K a b :=
    Finset.sum_subset h₁ fun a _ ha' => Finset.sum_eq_zero fun b _ => by
      rw [if_neg ha']
      ring
  rw [← h1]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h2 : ∑ b ∈ S₂, (if a ∈ S₁ then φ a else 0) * (if b ∈ S₂ then ψ b else 0) * K a b =
      ∑ b ∈ T, (if a ∈ S₁ then φ a else 0) * (if b ∈ S₂ then ψ b else 0) * K a b :=
    Finset.sum_subset h₂ fun b _ hb' => by
      rw [if_neg hb']
      ring
  rw [← h2]
  exact Finset.sum_congr rfl fun b hb => by rw [if_pos ha, if_pos hb]

/-- A constant on the second set of blocks factors out. -/
theorem rectSum_const_right (K : ℕ → ℕ → ℝ) (A B : Finset ℕ) (φ : ℕ → ℝ) (x : ℝ) :
    rectSum K A B φ (fun _ => x) = x * ∑ a ∈ A, φ a * ∑ b ∈ B, K a b := by
  show ∑ a ∈ A, ∑ b ∈ B, φ a * x * K a b = x * ∑ a ∈ A, φ a * ∑ b ∈ B, K a b
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The pairing of a combination of three step functions with itself. -/
theorem rectSum_lin3 (K : ℕ → ℕ → ℝ) (A : Finset ℕ) (U₁ U₂ U₃ : ℕ → ℝ) (x₁ x₂ x₃ : ℝ) :
    rectSum K A A (fun b => x₁ * U₁ b + x₂ * U₂ b + x₃ * U₃ b)
        (fun b => x₁ * U₁ b + x₂ * U₂ b + x₃ * U₃ b) =
      x₁ * x₁ * rectSum K A A U₁ U₁ + x₁ * x₂ * rectSum K A A U₁ U₂ +
        x₁ * x₃ * rectSum K A A U₁ U₃ + x₂ * x₁ * rectSum K A A U₂ U₁ +
        x₂ * x₂ * rectSum K A A U₂ U₂ + x₂ * x₃ * rectSum K A A U₂ U₃ +
        x₃ * x₁ * rectSum K A A U₃ U₁ + x₃ * x₂ * rectSum K A A U₃ U₂ +
        x₃ * x₃ * rectSum K A A U₃ U₃ := by
  simp only [rectSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The pairing over the blocks of a window, by the index of the block in the window. -/
theorem rectSum_Ico_eq_sum_range (K : ℕ → ℕ → ℝ) (R J : ℕ) (f g : ℕ → ℝ) :
    rectSum K (Ico R (R + J)) (Ico R (R + J)) f g =
      ∑ j ∈ range J, ∑ l ∈ range J, f (R + j) * g (R + l) * K (R + j) (R + l) := by
  unfold rectSum
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

theorem Ico_one_two : (Ico 1 2 : Finset ℕ) = {1} := by
  ext b
  simp only [Finset.mem_Ico, Finset.mem_singleton]
  omega

/-! ### Two negative squares on a real plane -/

/-- A binary quadratic form with negative leading coefficient and positive discriminant
`αγ − β²` is negative off the origin. -/
theorem quad_neg_of_disc {α β γ : ℝ} (hα : α < 0) (hδ : 0 < α * γ - β ^ 2) {s t : ℝ}
    (hst : s ≠ 0 ∨ t ≠ 0) : α * s ^ 2 + 2 * β * s * t + γ * t ^ 2 < 0 := by
  by_contra hcon
  have hcon' : 0 ≤ α * s ^ 2 + 2 * β * s * t + γ * t ^ 2 := not_lt.mp hcon
  have h3 : α * (α * s ^ 2 + 2 * β * s * t + γ * t ^ 2) =
      (α * s + β * t) ^ 2 + (α * γ - β ^ 2) * t ^ 2 := by ring
  have h4 := mul_nonpos_of_nonpos_of_nonneg hα.le hcon'
  have h5 : 0 ≤ (α * s + β * t) ^ 2 := sq_nonneg _
  by_cases ht : t = 0
  · subst ht
    have hs : s ≠ 0 := by
      rcases hst with h | h
      · exact h
      · exact absurd rfl h
    have hs2 : 0 < s ^ 2 := by positivity
    have e : α * s ^ 2 + 2 * β * s * 0 + γ * (0 : ℝ) ^ 2 = α * s ^ 2 := by ring
    rw [e] at hcon'
    linarith [mul_neg_of_neg_of_pos hα hs2]
  · have ht2 : 0 < t ^ 2 := by positivity
    have := mul_pos hδ ht2
    linarith

/-- **A real symmetric matrix that is negative on a real plane has two negative squares.** -/
theorem two_le_hermNegIndex_of_plane {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (w₁ w₂ : Fin n → ℝ)
    (h : ∀ s t : ℝ, (s ≠ 0 ∨ t ≠ 0) →
      ∑ i, ∑ j, (s * w₁ i + t * w₂ i) * (s * w₁ j + t * w₂ j) * B i j < 0) :
    2 ≤ hermNegIndex (B.map (↑) : Matrix (Fin n) (Fin n) ℂ) := by
  let v : Fin 2 → Fin n → ℝ := ![w₁, w₂]
  have e : ∀ (γ : Fin 2 → ℝ) (i : Fin n), ∑ j : Fin 2, γ j * v j i = γ 0 * w₁ i + γ 1 * w₂ i :=
    fun γ i => by
      rw [Fin.sum_univ_two]
      rfl
  have hv : ∀ γ : Fin 2 → ℝ, γ ≠ 0 →
      hermQuad (B.map (↑) : Matrix (Fin n) (Fin n) ℂ)
        (fun m => ((∑ j, γ j * v j m : ℝ) : ℂ)) < 0 := by
    intro γ hγ
    rw [HeckeKreinToeplitz.hermQuad_map_ofReal_real, dotProduct_mulVec_eq_sum]
    simp only [e]
    refine h (γ 0) (γ 1) ?_
    by_contra hcon
    push Not at hcon
    refine hγ (funext fun i => ?_)
    fin_cases i
    · exact hcon.1
    · exact hcon.2
  let L : (Fin 2 → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun a m => ∑ j : Fin 2, a j * ((v j m : ℝ) : ℂ)
      map_add' := by
        intro a b
        funext m
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro t a
        funext m
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hcard := HeckeKreinToeplitz.card_le_hermNegIndex_of_forall_neg
    (B.map (↑) : Matrix (Fin n) (Fin n) ℂ) L
    (HeckeKreinToeplitz.hermQuad_complexify_neg (H := (B.map (↑) : Matrix (Fin n) (Fin n) ℂ))
      (κ := Fin 2) (fun i j => by simp) v hv)
  rwa [Fintype.card_fin] at hcard

/-! ### The Gram matrix of three vectors on a plane -/

/-- The coefficient of `s²` of the form on `s(u₁ − c₁u₂ − κu₃) + t(u₂ + u₃)`. -/
def gramA (c₁ κ p₁₁ p₂₂ p₃₃ p₁₂ p₁₃ p₂₃ : ℝ) : ℝ :=
  p₁₁ + c₁ ^ 2 * p₂₂ + κ ^ 2 * p₃₃ - 2 * c₁ * p₁₂ - 2 * κ * p₁₃ + 2 * c₁ * κ * p₂₃

/-- Half the coefficient of `st`. -/
def gramB (c₁ κ p₂₂ p₃₃ p₁₂ p₁₃ p₂₃ : ℝ) : ℝ :=
  p₁₂ + p₁₃ - c₁ * (p₂₂ + p₂₃) - κ * (p₂₃ + p₃₃)

/-- The coefficient of `t²`. -/
def gramC (p₂₂ p₃₃ p₂₃ : ℝ) : ℝ := p₂₂ + 2 * p₂₃ + p₃₃

theorem gram_expand (c₁ κ p₁₁ p₂₂ p₃₃ p₁₂ p₁₃ p₂₃ s t : ℝ) :
    s * s * p₁₁ + s * (t - s * c₁) * p₁₂ + s * (t - s * κ) * p₁₃ + (t - s * c₁) * s * p₁₂ +
        (t - s * c₁) * (t - s * c₁) * p₂₂ + (t - s * c₁) * (t - s * κ) * p₂₃ +
        (t - s * κ) * s * p₁₃ + (t - s * κ) * (t - s * c₁) * p₂₃ +
        (t - s * κ) * (t - s * κ) * p₃₃ =
      gramA c₁ κ p₁₁ p₂₂ p₃₃ p₁₂ p₁₃ p₂₃ * s ^ 2 + 2 * gramB c₁ κ p₂₂ p₃₃ p₁₂ p₁₃ p₂₃ * s * t +
        gramC p₂₂ p₃₃ p₂₃ * t ^ 2 := by
  unfold gramA gramB gramC
  ring

section Limits

variable {ι : Type*} {l : Filter ι} {f₁₁ f₂₂ f₃₃ f₁₂ f₁₃ f₂₃ : ι → ℝ}
  {a₁₁ a₂₂ a₃₃ a₁₂ a₁₃ a₂₃ : ℝ}

theorem tendsto_gramA (c₁ κ : ℝ) (h₁₁ : Tendsto f₁₁ l (𝓝 a₁₁)) (h₂₂ : Tendsto f₂₂ l (𝓝 a₂₂))
    (h₃₃ : Tendsto f₃₃ l (𝓝 a₃₃)) (h₁₂ : Tendsto f₁₂ l (𝓝 a₁₂)) (h₁₃ : Tendsto f₁₃ l (𝓝 a₁₃))
    (h₂₃ : Tendsto f₂₃ l (𝓝 a₂₃)) :
    Tendsto (fun i => gramA c₁ κ (f₁₁ i) (f₂₂ i) (f₃₃ i) (f₁₂ i) (f₁₃ i) (f₂₃ i)) l
      (𝓝 (gramA c₁ κ a₁₁ a₂₂ a₃₃ a₁₂ a₁₃ a₂₃)) := by
  unfold gramA
  exact ((((h₁₁.add (h₂₂.const_mul _)).add (h₃₃.const_mul _)).sub (h₁₂.const_mul _)).sub
    (h₁₃.const_mul _)).add (h₂₃.const_mul _)

theorem tendsto_gramB (c₁ κ : ℝ) (h₂₂ : Tendsto f₂₂ l (𝓝 a₂₂)) (h₃₃ : Tendsto f₃₃ l (𝓝 a₃₃))
    (h₁₂ : Tendsto f₁₂ l (𝓝 a₁₂)) (h₁₃ : Tendsto f₁₃ l (𝓝 a₁₃))
    (h₂₃ : Tendsto f₂₃ l (𝓝 a₂₃)) :
    Tendsto (fun i => gramB c₁ κ (f₂₂ i) (f₃₃ i) (f₁₂ i) (f₁₃ i) (f₂₃ i)) l
      (𝓝 (gramB c₁ κ a₂₂ a₃₃ a₁₂ a₁₃ a₂₃)) := by
  unfold gramB
  exact ((h₁₂.add h₁₃).sub ((h₂₂.add h₂₃).const_mul _)).sub ((h₂₃.add h₃₃).const_mul _)

theorem tendsto_gramC (h₂₂ : Tendsto f₂₂ l (𝓝 a₂₂)) (h₃₃ : Tendsto f₃₃ l (𝓝 a₃₃))
    (h₂₃ : Tendsto f₂₃ l (𝓝 a₂₃)) :
    Tendsto (fun i => gramC (f₂₂ i) (f₃₃ i) (f₂₃ i)) l (𝓝 (gramC a₂₂ a₃₃ a₂₃)) := by
  unfold gramC
  exact (h₂₂.add (h₂₃.const_mul _)).add h₃₃

end Limits

/-! ### The three vectors -/

/-- The step function on the blocks of `(1, 2M]`: `x₁` times the refinement of `σ` by `L` on the
blocks above `LR`, plus `x₂ √L/M` on the blocks `M ≤ b < 2M`, plus `x₃/√L` on the block one. -/
def probe (R J L M : ℕ) (σ : ℕ → ℝ) (x₁ x₂ x₃ : ℝ) (b : ℕ) : ℝ :=
  x₁ * (if b ∈ Ico (L * R) (L * R + L * J) then refineStep L σ (b - L * R) else 0) +
    x₂ * (if b ∈ Ico M (M + M) then Real.sqrt L / M else 0) +
    x₃ * (if b ∈ Ico 1 2 then 1 / Real.sqrt L else 0)

/-- The neutral pairing of the refinement of `σ` with the far window. -/
def liftFar (R J L M : ℕ) (σ : ℕ → ℝ) : ℝ :=
  Real.sqrt L / M * ∑ a ∈ Ico (L * R) (L * R + L * J),
    refineStep L σ (a - L * R) * ∑ b ∈ Ico M (M + M), neutralBlock (M + M) a b

/-- The neutral pairing of the refinement of `σ` with the block one. -/
def liftFirst (R J L : ℕ) (σ : ℕ → ℝ) : ℝ :=
  1 / Real.sqrt L * ∑ a ∈ Ico (L * R) (L * R + L * J),
    refineStep L σ (a - L * R) * neutralBlock (L * (R + J)) a 1

/-- The neutral pairing of the far window with the block one. -/
def farFirst (L M : ℕ) : ℝ :=
  1 / Real.sqrt L * ∑ a ∈ Ico M (M + M), Real.sqrt L / M * neutralBlock (M + M) a 1

theorem neutralBlock_self_eq (Q Q' : ℕ) {a : ℕ} (ha : 1 ≤ a) :
    neutralBlock Q a a = neutralBlock Q' a a := by
  rw [neutralBlock, neutralBlock, blockMatrix_self ha, blockMatrix_self ha]

theorem blockDegree_one_pos : 0 < blockDegree 1 := by
  have h := Real.log_lt_log (show (0 : ℝ) < ((1 : ℕ) : ℝ) by norm_num)
    (show ((1 : ℕ) : ℝ) < ((1 + 1 : ℕ) : ℝ) by norm_num)
  unfold blockDegree
  linarith

/-- The far window with itself. -/
theorem far_far_eq {L M : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M) (Q : ℕ) :
    Real.sqrt L / M * ∑ a ∈ Ico M (M + M),
        Real.sqrt L / M * ∑ b ∈ Ico M (M + M), neutralBlock Q a b =
      L * neutralBlock 0 1 1 / M := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hsum : ∑ a ∈ Ico M (M + M), ∑ b ∈ Ico M (M + M), neutralBlock Q a b =
      M * neutralBlock 0 1 1 := by
    have h := sum_neutralBlock_dyadic Q hM
    rw [neutralBlock_self_eq Q 0 le_rfl] at h
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  rw [← Finset.mul_sum, hsum]
  calc Real.sqrt L / M * (Real.sqrt L / M * (M * neutralBlock 0 1 1))
      = Real.sqrt L * Real.sqrt L * neutralBlock 0 1 1 / M := by field_simp
    _ = L * neutralBlock 0 1 1 / M := by rw [hss]

/-- The block one with itself. -/
theorem first_first_eq {L : ℕ} (hL : 1 ≤ L) (Q : ℕ) :
    1 / Real.sqrt L * ∑ a ∈ Ico 1 2, 1 / Real.sqrt L * ∑ b ∈ Ico 1 2, neutralBlock Q a b =
      neutralBlock 0 1 1 / L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  rw [Ico_one_two, Finset.sum_singleton, Finset.sum_singleton, neutralBlock_self_eq Q 0 le_rfl]
  calc 1 / Real.sqrt L * (1 / Real.sqrt L * neutralBlock 0 1 1)
      = neutralBlock 0 1 1 / (Real.sqrt L * Real.sqrt L) := by field_simp
    _ = neutralBlock 0 1 1 / L := by rw [hss]

/-- **The far window and the block one**: their pairing tends to minus the degree of the block
one. -/
theorem tendsto_farFirst {L : ℕ} (hL : 1 ≤ L) :
    Tendsto (fun M : ℕ => farFirst L M) atTop (𝓝 (-blockDegree 1)) := by
  have hT := tendsto_sum_Ico_neutralBlock_div (a := 1) le_rfl (c := 1) (d := 2) le_rfl
    (by norm_num) (fun M => M + M) (Eventually.of_forall fun M => by
      show M * 2 ≤ M + M
      omega)
  have hval : -((((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) * blockDegree 1) = -blockDegree 1 := by
    push_cast
    ring
  rw [hval] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hs : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hL)).ne'
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  show (∑ l ∈ Ico (M * 1) (M * 2), neutralBlock (M + M) 1 l) / (M : ℝ) = farFirst L M
  rw [Nat.mul_one, Nat.mul_two, farFirst, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [neutralBlock_comm (M + M) a 1]
  field_simp

/-- **The refinement of `σ` and the far window**: their pairing tends to minus the second charge
of `σ`. -/
theorem tendsto_liftFar {R : ℕ} (hR : 1 ≤ R) {L : ℕ} (hL : 1 ≤ L) (J : ℕ) (σ : ℕ → ℝ) :
    Tendsto (fun M : ℕ => liftFar R J L M σ) atTop
      (𝓝 (-∑ j ∈ range J, σ j * blockDegree (R + j))) := by
  have hs : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hL)).ne'
  have hT : ∀ a ∈ Ico (L * R) (L * R + L * J),
      Tendsto (fun M : ℕ => (∑ l ∈ Ico (M * 1) (M * 2), neutralBlock (M + M) a l) / M) atTop
        (𝓝 (-((((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) * blockDegree a))) := fun a ha =>
    tendsto_sum_Ico_neutralBlock_div (a := a)
      (by
        have h1 := (Finset.mem_Ico.mp ha).1
        have h2 := Nat.mul_pos (show 0 < L by omega) (show 0 < R by omega)
        omega)
      le_rfl (by norm_num) (fun M => M + M) (Eventually.of_forall fun M => by
        show M * 2 ≤ M + M
        omega)
  have hsum := (tendsto_finsetSum (Ico (L * R) (L * R + L * J)) fun a ha =>
    (hT a ha).const_mul (refineStep L σ (a - L * R))).const_mul (Real.sqrt L)
  have hval : Real.sqrt L * ∑ a ∈ Ico (L * R) (L * R + L * J),
      refineStep L σ (a - L * R) * -((((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) * blockDegree a) =
      -∑ j ∈ range J, σ j * blockDegree (R + j) := by
    have h1 : ∑ a ∈ Ico (L * R) (L * R + L * J),
        refineStep L σ (a - L * R) * -((((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) * blockDegree a) =
        -∑ i ∈ range (L * J), refineStep L σ i * blockDegree (L * R + i) := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_sub_cancel_left]
      push_cast
      ring
    rw [h1, sum_refineStep_mul_blockDegree hR hL]
    field_simp
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  show Real.sqrt L * ∑ a ∈ Ico (L * R) (L * R + L * J), refineStep L σ (a - L * R) *
      ((∑ l ∈ Ico (M * 1) (M * 2), neutralBlock (M + M) a l) / (M : ℝ)) = liftFar R J L M σ
  rw [Nat.mul_one, Nat.mul_two, liftFar, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp

/-- **The refinement of `σ` and the block one**: their pairing tends to minus the degree of the
block one times the first charge of `σ`. -/
theorem tendsto_liftFirst {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    Tendsto (fun L : ℕ => liftFirst R J L σ) atTop
      (𝓝 (-(blockDegree 1 * ∑ j ∈ range J, σ j))) := by
  have hT : ∀ j ∈ range J,
      Tendsto (fun L : ℕ => (∑ l ∈ Ico (L * (R + j)) (L * (R + j + 1)),
          neutralBlock (L * (R + J)) 1 l) / L) atTop
        (𝓝 (-((((R + j + 1 : ℕ) : ℝ) - ((R + j : ℕ) : ℝ)) * blockDegree 1))) := fun j hj =>
    tendsto_sum_Ico_neutralBlock_div (a := 1) le_rfl (c := R + j) (d := R + j + 1) (by omega)
      (by omega) (fun L => L * (R + J)) (Eventually.of_forall fun L => by
        show L * (R + j + 1) ≤ L * (R + J)
        exact Nat.mul_le_mul_left L (by
          have := Finset.mem_range.mp hj
          omega))
  have hsum := tendsto_finsetSum (range J) fun j hj => (hT j hj).const_mul (σ j)
  have hval : ∑ j ∈ range J,
      σ j * -((((R + j + 1 : ℕ) : ℝ) - ((R + j : ℕ) : ℝ)) * blockDegree 1) =
      -(blockDegree 1 * ∑ j ∈ range J, σ j) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      push_cast
      ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hs : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL0).ne'
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  show ∑ j ∈ range J, σ j * ((∑ l ∈ Ico (L * (R + j)) (L * (R + j + 1)),
      neutralBlock (L * (R + J)) 1 l) / (L : ℝ)) = liftFirst R J L σ
  -- the blocks of the refinement, grouped by the blocks of `σ`
  have hgroup : ∑ a ∈ Ico (L * R) (L * R + L * J),
        refineStep L σ (a - L * R) * neutralBlock (L * (R + J)) a 1 =
      ∑ j ∈ range J, σ j / Real.sqrt L *
        ∑ l ∈ Ico (L * (R + j)) (L * (R + j + 1)), neutralBlock (L * (R + J)) 1 l := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, sum_range_mul_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlen : L * (R + j + 1) - L * (R + j) = L := by
      rw [mul_add_one, Nat.add_sub_cancel_left]
    rw [Finset.mul_sum, Finset.sum_Ico_eq_sum_range, hlen]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.add_sub_cancel_left, refineStep_mul_add hL σ j (Finset.mem_range.mp hi),
      neutralBlock_comm, ← Nat.add_assoc, ← Nat.mul_add]
  rw [liftFirst, hgroup, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  generalize (∑ l ∈ Ico (L * (R + j)) (L * (R + j + 1)), neutralBlock (L * (R + J)) 1 l) = S
  have h1 : 1 / Real.sqrt L * (σ j / Real.sqrt L * S) =
      σ j * S / (Real.sqrt L * Real.sqrt L) := by field_simp
  rw [h1, hss]
  ring

/-! ### The form of the neutral part on the three vectors -/

/-- The form of the neutral part of the window `(1, 2M]` on a step function is its pairing over
the blocks. -/
theorem sum_fin_neutralWindow_eq_rectSum {M : ℕ} (hM : 1 ≤ M) (Q : ℕ) (Ψ : ℕ → ℝ) :
    ∑ i : Fin (M + M - 1), ∑ j : Fin (M + M - 1),
        Ψ (1 + (i : ℕ)) * Ψ (1 + (j : ℕ)) * neutralWindow Q 1 (M + M - 1) i j =
      rectSum (neutralBlock Q) (Ico 1 (M + M)) (Ico 1 (M + M)) Ψ Ψ := by
  have h1 := sum_fin_windowMatrix_coe (neutralBlock Q) 1 (M + M - 1) (fun j => Ψ (1 + j))
  have h2 := rectSum_Ico_eq_sum_range (neutralBlock Q) 1 (M + M - 1) Ψ Ψ
  rw [show 1 + (M + M - 1) = M + M by omega] at h2
  rw [h2, ← h1]
  rfl

/-- **The Gram matrix of the three vectors.** On `s(u₁ − c₁u₂ − κu₃) + t(u₂ + u₃)` the neutral
part of the window `(1, 2M]` is a binary quadratic form in `(s, t)` whose coefficients are the
neutral part of `σ`, the exact values `L n₁/M` and `n₁/L`, and the three pairings. -/
theorem probe_form {R J Q₀ : ℕ} (hR : 1 ≤ R) (hQ₀ : R + J ≤ Q₀ * R) (σ : ℕ → ℝ) {L M : ℕ}
    (hL1 : 1 ≤ L) (hM1 : 1 ≤ M) (hLM : L * (R + J) ≤ M) (hQM : Q₀ ≤ M + M)
    (c₁ κ s t : ℝ) :
    rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
        (probe R J L M σ s (t - s * c₁) (t - s * κ))
        (probe R J L M σ s (t - s * c₁) (t - s * κ)) =
      gramA c₁ κ (∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q₀ (R + j) (R + l))
          (L * neutralBlock 0 1 1 / M) (neutralBlock 0 1 1 / L) (liftFar R J L M σ)
          (liftFirst R J L σ) (farFirst L M) * s ^ 2 +
        2 * gramB c₁ κ (L * neutralBlock 0 1 1 / M) (neutralBlock 0 1 1 / L)
          (liftFar R J L M σ) (liftFirst R J L σ) (farFirst L M) * s * t +
        gramC (L * neutralBlock 0 1 1 / M) (neutralBlock 0 1 1 / L) (farFirst L M) * t ^ 2 := by
  -- the three sets of blocks inside the window
  have hLR : 1 ≤ L * R := Nat.mul_pos (by omega) (by omega)
  have hmul : L * (R + J) = L * R + L * J := Nat.mul_add L R J
  have hS₁ : Ico (L * R) (L * R + L * J) ⊆ Ico 1 (M + M) :=
    Finset.Ico_subset_Ico hLR (by omega)
  have hS₂ : Ico M (M + M) ⊆ Ico 1 (M + M) := Finset.Ico_subset_Ico hM1 le_rfl
  have hS₃ : Ico 1 2 ⊆ Ico 1 (M + M) := Finset.Ico_subset_Ico le_rfl (by omega)
  have hsym : ∀ a b, neutralBlock (M + M) a b = neutralBlock (M + M) b a :=
    neutralBlock_comm (M + M)
  -- the entries
  have P11 : rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
      (fun b => if b ∈ Ico (L * R) (L * R + L * J) then refineStep L σ (b - L * R) else 0)
      (fun b => if b ∈ Ico (L * R) (L * R + L * J) then refineStep L σ (b - L * R) else 0) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q₀ (R + j) (R + l) := by
    rw [rectSum_indicator _ hS₁ hS₁, rectSum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    rw [sum_neutralBlock_refine hR hL1 (M + M) J σ]
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => ?_
    have hj' := Finset.mem_range.mp hj
    have hl' := Finset.mem_range.mp hl
    rw [neutralBlock_eq_of_le hQM]
    calc max (R + j) (R + l) < R + J := max_lt (by omega) (by omega)
      _ ≤ Q₀ * R := hQ₀
      _ ≤ (Q₀ + 1) * R := Nat.mul_le_mul_right R (Nat.le_succ Q₀)
      _ ≤ (Q₀ + 1) * min (R + j) (R + l) :=
          Nat.mul_le_mul_left (Q₀ + 1) (le_min (by omega) (by omega))
  have P12 : rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
      (fun b => if b ∈ Ico (L * R) (L * R + L * J) then refineStep L σ (b - L * R) else 0)
      (fun b => if b ∈ Ico M (M + M) then Real.sqrt L / M else 0) = liftFar R J L M σ :=
    (rectSum_indicator _ hS₁ hS₂ _ _).trans (rectSum_const_right _ _ _ _ _)
  have P13 : rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
      (fun b => if b ∈ Ico (L * R) (L * R + L * J) then refineStep L σ (b - L * R) else 0)
      (fun b => if b ∈ Ico 1 2 then 1 / Real.sqrt L else 0) = liftFirst R J L σ := by
    refine (rectSum_indicator _ hS₁ hS₃ _ _).trans ((rectSum_const_right _ _ _ _ _).trans ?_)
    rw [liftFirst]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : 1 ≤ a := hLR.trans (Finset.mem_Ico.mp ha).1
    have ha2 := (Finset.mem_Ico.mp ha).2
    rw [Ico_one_two, Finset.sum_singleton,
      neutralBlock_eq_of_le (Q := L * (R + J)) (Q' := M + M) (by omega)]
    rw [max_eq_left ha1, min_eq_right ha1, Nat.mul_one]
    omega
  have P22 : rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
      (fun b => if b ∈ Ico M (M + M) then Real.sqrt L / M else 0)
      (fun b => if b ∈ Ico M (M + M) then Real.sqrt L / M else 0) =
      L * neutralBlock 0 1 1 / M :=
    (rectSum_indicator _ hS₂ hS₂ _ _).trans
      ((rectSum_const_right _ _ _ _ _).trans (far_far_eq hL1 hM1 (M + M)))
  have P23 : rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
      (fun b => if b ∈ Ico M (M + M) then Real.sqrt L / M else 0)
      (fun b => if b ∈ Ico 1 2 then 1 / Real.sqrt L else 0) = farFirst L M := by
    refine (rectSum_indicator _ hS₂ hS₃ _ _).trans ((rectSum_const_right _ _ _ _ _).trans ?_)
    simp only [farFirst, Ico_one_two, Finset.sum_singleton]
  have P33 : rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
      (fun b => if b ∈ Ico 1 2 then 1 / Real.sqrt L else 0)
      (fun b => if b ∈ Ico 1 2 then 1 / Real.sqrt L else 0) = neutralBlock 0 1 1 / L :=
    (rectSum_indicator _ hS₃ hS₃ _ _).trans
      ((rectSum_const_right _ _ _ _ _).trans (first_first_eq hL1 (M + M)))
  have P21 := (rectSum_comm hsym (Ico 1 (M + M)) (Ico 1 (M + M))
    (fun b => if b ∈ Ico M (M + M) then Real.sqrt L / M else 0)
    (fun b => if b ∈ Ico (L * R) (L * R + L * J) then refineStep L σ (b - L * R) else 0)).trans
    P12
  have P31 := (rectSum_comm hsym (Ico 1 (M + M)) (Ico 1 (M + M))
    (fun b => if b ∈ Ico 1 2 then 1 / Real.sqrt L else 0)
    (fun b => if b ∈ Ico (L * R) (L * R + L * J) then refineStep L σ (b - L * R) else 0)).trans
    P13
  have P32 := (rectSum_comm hsym (Ico 1 (M + M)) (Ico 1 (M + M))
    (fun b => if b ∈ Ico 1 2 then 1 / Real.sqrt L else 0)
    (fun b => if b ∈ Ico M (M + M) then Real.sqrt L / M else 0)).trans P23
  have hlin : rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
      (probe R J L M σ s (t - s * c₁) (t - s * κ))
      (probe R J L M σ s (t - s * c₁) (t - s * κ)) = _ :=
    rectSum_lin3 (neutralBlock (M + M)) (Ico 1 (M + M))
      (fun b => if b ∈ Ico (L * R) (L * R + L * J) then refineStep L σ (b - L * R) else 0)
      (fun b => if b ∈ Ico M (M + M) then Real.sqrt L / M else 0)
      (fun b => if b ∈ Ico 1 2 then 1 / Real.sqrt L else 0) s (t - s * c₁) (t - s * κ)
  rw [hlin, P11, P12, P13, P21, P22, P23, P31, P32, P33]
  exact gram_expand c₁ κ _ _ _ _ _ _ s t

/-! ### Two negative squares -/

/-- **A step packet of negative Weil form gives two negative squares of the neutral part** on
the blocks of a window `(1, 2M]`. -/
theorem exists_two_le_hermNegIndex_neutralWindow {R J Q₀ : ℕ} (hR : 1 ≤ R)
    (hQ₀ : R + J ≤ Q₀ * R) (σ : ℕ → ℝ)
    (hneg : 2 * (∑ j ∈ range J, σ j) * (∑ j ∈ range J, σ j * blockDegree (R + j)) +
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q₀ (R + j) (R + l) < 0) :
    ∃ M : ℕ, 1 ≤ M ∧ 2 ≤ hermNegIndex
      ((neutralWindow (M + M) 1 (M + M - 1)).map (↑) :
        Matrix (Fin (M + M - 1)) (Fin (M + M - 1)) ℂ) := by
  set c₁ := ∑ j ∈ range J, σ j with hc₁
  set c₀ := ∑ j ∈ range J, σ j * blockDegree (R + j) with hc₀
  set nσ := ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q₀ (R + j) (R + l)
    with hnσ
  have hℓ := blockDegree_one_pos
  set ℓ := blockDegree 1 with hℓdef
  set n₁ := neutralBlock 0 1 1 with hn₁
  set κ := c₀ / ℓ with hκ
  have hκℓ : κ * ℓ = c₀ := div_mul_cancel₀ c₀ hℓ.ne'
  -- stage one: the scale `L` of the refinement
  have h33 : Tendsto (fun L : ℕ => n₁ / (L : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat n₁
  have h13 : Tendsto (fun L : ℕ => liftFirst R J L σ) atTop (𝓝 (-(ℓ * c₁))) :=
    tendsto_liftFirst hR J σ
  have hc : ∀ x : ℝ, Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := fun _ => tendsto_const_nhds
  have hA₁ := tendsto_gramA c₁ κ (hc nσ) (hc 0) h33 (hc (-c₀)) h13 (hc (-ℓ))
  have hB₁ := tendsto_gramB c₁ κ (hc 0) h33 (hc (-c₀)) h13 (hc (-ℓ))
  have hC₁ := tendsto_gramC (hc 0) h33 (hc (-ℓ))
  have hAval : gramA c₁ κ nσ 0 0 (-c₀) (-(ℓ * c₁)) (-ℓ) = 2 * c₁ * c₀ + nσ := by
    unfold gramA
    ring
  have hBval : gramB c₁ κ 0 0 (-c₀) (-(ℓ * c₁)) (-ℓ) = 0 := by
    unfold gramB
    linear_combination hκℓ
  have hCval : gramC 0 0 (-ℓ) = -2 * ℓ := by
    unfold gramC
    ring
  have hD₁ := (hA₁.mul hC₁).sub (hB₁.pow 2)
  have hDpos : 0 < gramA c₁ κ nσ 0 0 (-c₀) (-(ℓ * c₁)) (-ℓ) * gramC 0 0 (-ℓ) -
      gramB c₁ κ 0 0 (-c₀) (-(ℓ * c₁)) (-ℓ) ^ 2 := by
    rw [hAval, hBval, hCval]
    nlinarith
  obtain ⟨L, hL1, hAL, hDL⟩ : ∃ L : ℕ, 1 ≤ L ∧
      gramA c₁ κ nσ 0 (n₁ / L) (-c₀) (liftFirst R J L σ) (-ℓ) < 0 ∧
      0 < gramA c₁ κ nσ 0 (n₁ / L) (-c₀) (liftFirst R J L σ) (-ℓ) * gramC 0 (n₁ / L) (-ℓ) -
        gramB c₁ κ 0 (n₁ / L) (-c₀) (liftFirst R J L σ) (-ℓ) ^ 2 := by
    have h1 := hA₁.eventually (Iio_mem_nhds (show gramA c₁ κ nσ 0 0 (-c₀) (-(ℓ * c₁)) (-ℓ) < 0 by
      rw [hAval]
      exact hneg))
    have h2 := hD₁.eventually (Ioi_mem_nhds hDpos)
    obtain ⟨L, hL⟩ := ((eventually_ge_atTop 1).and (h1.and h2)).exists
    exact ⟨L, hL.1, hL.2.1, hL.2.2⟩
  -- stage two: the far window
  have h22 : Tendsto (fun M : ℕ => (L : ℝ) * n₁ / (M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h12 : Tendsto (fun M : ℕ => liftFar R J L M σ) atTop (𝓝 (-c₀)) :=
    tendsto_liftFar hR hL1 J σ
  have h23 : Tendsto (fun M : ℕ => farFirst L M) atTop (𝓝 (-ℓ)) := tendsto_farFirst hL1
  have hA₂ := tendsto_gramA c₁ κ (hc nσ) h22 (hc (n₁ / L)) h12 (hc (liftFirst R J L σ)) h23
  have hB₂ := tendsto_gramB c₁ κ h22 (hc (n₁ / L)) h12 (hc (liftFirst R J L σ)) h23
  have hC₂ := tendsto_gramC h22 (hc (n₁ / L)) h23
  have hD₂ := (hA₂.mul hC₂).sub (hB₂.pow 2)
  obtain ⟨M, hMge, hAM, hDM⟩ := ((eventually_ge_atTop (max 1 (max (L * (R + J)) Q₀))).and
    ((hA₂.eventually (Iio_mem_nhds hAL)).and (hD₂.eventually (Ioi_mem_nhds hDL)))).exists
  have hM1 : 1 ≤ M := (le_max_left _ _).trans hMge
  have hLM : L * (R + J) ≤ M := ((le_max_left _ _).trans (le_max_right _ _)).trans hMge
  have hQM : Q₀ ≤ M + M := (((le_max_right _ _).trans (le_max_right _ _)).trans hMge).trans
    (Nat.le_add_right M M)
  refine ⟨M, hM1, ?_⟩
  -- the plane spanned by `u₁ − c₁u₂ − κu₃` and `u₂ + u₃`
  refine two_le_hermNegIndex_of_plane _
    (fun i : Fin (M + M - 1) => probe R J L M σ 1 (-c₁) (-κ) (1 + (i : ℕ)))
    (fun i : Fin (M + M - 1) => probe R J L M σ 0 1 1 (1 + (i : ℕ))) fun s t hst => ?_
  have hW : ∀ b, s * probe R J L M σ 1 (-c₁) (-κ) b + t * probe R J L M σ 0 1 1 b =
      probe R J L M σ s (t - s * c₁) (t - s * κ) b := fun b => by
    unfold probe
    ring
  have hform : ∑ i : Fin (M + M - 1), ∑ j : Fin (M + M - 1),
      (s * probe R J L M σ 1 (-c₁) (-κ) (1 + (i : ℕ)) + t * probe R J L M σ 0 1 1 (1 + (i : ℕ))) *
        (s * probe R J L M σ 1 (-c₁) (-κ) (1 + (j : ℕ)) +
          t * probe R J L M σ 0 1 1 (1 + (j : ℕ))) *
        neutralWindow (M + M) 1 (M + M - 1) i j =
      rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
        (probe R J L M σ s (t - s * c₁) (t - s * κ))
        (probe R J L M σ s (t - s * c₁) (t - s * κ)) := by
    rw [← sum_fin_neutralWindow_eq_rectSum hM1]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hW, hW]
  show ∑ i : Fin (M + M - 1), ∑ j : Fin (M + M - 1),
      (s * probe R J L M σ 1 (-c₁) (-κ) (1 + (i : ℕ)) + t * probe R J L M σ 0 1 1 (1 + (i : ℕ))) *
        (s * probe R J L M σ 1 (-c₁) (-κ) (1 + (j : ℕ)) +
          t * probe R J L M σ 0 1 1 (1 + (j : ℕ))) *
        neutralWindow (M + M) 1 (M + M - 1) i j < 0
  rw [hform, probe_form hR hQ₀ σ hL1 hM1 hLM hQM c₁ κ s t]
  exact quad_neg_of_disc hAM hDM hst

/-! ### The criterion -/

/-- **The Riemann hypothesis is the signature of the neutral part of the step-packet matrices**:
it holds iff the neutral part of the block matrix of every window `(R, R + J]` with `R ≤ J` has
exactly one negative square. -/
theorem riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one :
    RiemannHypothesis ↔ ∀ Q R J : ℕ, 1 ≤ R → R ≤ J → R + J ≤ Q * R →
      hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 := by
  constructor
  · intro hRH Q R J hR hRJ hQ
    exact hermNegIndex_neutralWindow_eq_one_of_riemannHypothesis hRH hR hRJ hQ
  · intro h
    by_contra hRH
    rw [riemannHypothesis_iff_forall_packetForm_stepPacket_nonneg] at hRH
    push Not at hRH
    obtain ⟨K, -, R, hR, σ, hσ⟩ := hRH
    rw [packetForm_stepPacket_eq_sum_blockMatrix hR,
      sum_blockMatrix_eq_charges_add_neutral] at hσ
    obtain ⟨M, hM, h2⟩ := exists_two_le_hermNegIndex_neutralWindow hR
      (Q₀ := 3 * K + 1) (J := 3 * K * R) (le_of_eq (by ring)) σ hσ
    have h1 := h (M + M) 1 (M + M - 1) le_rfl (by omega) (by omega)
    omega

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
