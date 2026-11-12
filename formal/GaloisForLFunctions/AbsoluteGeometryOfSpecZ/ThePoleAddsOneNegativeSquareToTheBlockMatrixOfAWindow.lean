import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsOneNegativeSquareOfTheNeutralPartOfEveryWindow
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.AdelicKreinGeometry.MixingKillsNegativeSquares

/-!
# The pole adds one negative square to the block matrix of a window

For every window `(R, R + J]` there is a window `(1, 2M]` whose neutral part has at least one
negative square more than the block matrix of `(R, R + J]`
(`exists_hermNegIndex_blockWindow_add_one_le`). With the converse bound on one window (the
indices of the neutral part and of the block matrix differ by at most one) the neutral part
carries, in the limit of the windows, exactly one square more than the block matrix: the square
of the pole.

**Proof.** For a packet `σ` on the blocks of `(R, R + J]` and a real `t` take, on the blocks of
`(1, 2M]`, the vector `u₁(σ) − c₁(σ)u₂ − (c₀(σ)/ℓ)u₃ + t(u₂ + u₃)`: the refinement of `σ` by `L`
with its two charges moved to the far window and to the block one. It is linear in `(σ, t)`
(`sum_poleFrame`), so the neutral part on these vectors is the form of the Gram matrix of a
frame of `J + 1` vectors (`poleGram`, `bilin_poleGram_eq`). As `M → ∞` and then `L → ∞` it tends,
on each `(σ, t)`, to `m(σ) − 2ℓt²`, the form of the block matrix plus one negative square. A
symmetric matrix is the polarization of its form (`polar_bilin`), so the Gram matrices converge
entrywise; the negative index is lower semicontinuous under entrywise convergence, and a Gram
matrix has at most the index of the form (`hermNegIndex_gram_le`).
-/

open Finset Filter Topology Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### A symmetric matrix is the polarization of its form -/

section Polar

variable {ι : Type*} [Fintype ι]

/-- The bilinear form of a real matrix. -/
def bilin (G : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ := ∑ i, ∑ j, x i * y j * G i j

theorem dotProduct_mulVec_eq_bilin (G : Matrix ι ι ℝ) (y : ι → ℝ) :
    y ⬝ᵥ (G *ᵥ y) = bilin G y y := by
  simp only [dotProduct, mulVec, bilin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bilin_add_add (G : Matrix ι ι ℝ) (x y : ι → ℝ) :
    bilin G (x + y) (x + y) = bilin G x x + bilin G x y + bilin G y x + bilin G y y := by
  simp only [bilin, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [Fintype ι] in
/-- The complexification of a real symmetric matrix is Hermitian. -/
theorem isHermitian_map_ofReal {G : Matrix ι ι ℝ} (hG : ∀ a c, G a c = G c a) :
    (G.map (↑) : Matrix ι ι ℂ).IsHermitian :=
  Matrix.IsHermitian.ext fun a c => by
    simp only [Matrix.map_apply, RCLike.star_def, Complex.conj_ofReal]
    rw [hG c a]

/-- **The Gram matrix of a family of real vectors has at most the negative index of the
form.** -/
theorem hermNegIndex_gram_le {κ : Type*} [Fintype κ] (B : Matrix κ κ ℝ) (V : ι → κ → ℝ)
    (G : Matrix ι ι ℝ)
    (hG : ∀ y : ι → ℝ,
      bilin B (fun k => ∑ a, y a * V a k) (fun k => ∑ a, y a * V a k) = bilin G y y) :
    hermNegIndex (G.map (↑) : Matrix ι ι ℂ) ≤ hermNegIndex (B.map (↑) : Matrix κ κ ℂ) := by
  let L : (ι → ℂ) →ₗ[ℂ] (κ → ℂ) :=
    { toFun := fun c k => ∑ a, c a * ((V a k : ℝ) : ℂ)
      map_add' := by
        intro c d
        funext k
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro t c
        funext k
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  refine HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_eq _ _ L fun c => ?_
  have hre : (fun k => (L c k).re) = fun k => ∑ a, (c a).re * V a k := by
    funext k
    show (∑ a, c a * ((V a k : ℝ) : ℂ)).re = _
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun a _ => Complex.re_mul_ofReal _ _
  have him : (fun k => (L c k).im) = fun k => ∑ a, (c a).im * V a k := by
    funext k
    show (∑ a, c a * ((V a k : ℝ) : ℂ)).im = _
    rw [Complex.im_sum]
    exact Finset.sum_congr rfl fun a _ => Complex.im_mul_ofReal _ _
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal, HeckeKreinToeplitz.hermQuad_map_ofReal,
    dotProduct_mulVec_eq_bilin, dotProduct_mulVec_eq_bilin, dotProduct_mulVec_eq_bilin,
    dotProduct_mulVec_eq_bilin, hre, him, hG, hG]

variable [DecidableEq ι]

theorem sum_single_mul (a : ι) (F : ι → ℝ) :
    ∑ i, (Pi.single a (1 : ℝ) : ι → ℝ) i * F i = F a := by
  rw [Finset.sum_eq_single a (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_mul])
    (fun h => absurd (Finset.mem_univ a) h), Pi.single_eq_same, one_mul]

theorem bilin_single (G : Matrix ι ι ℝ) (a c : ι) :
    bilin G (Pi.single a 1) (Pi.single c 1) = G a c := by
  unfold bilin
  have h : ∀ i, ∑ j, (Pi.single a (1 : ℝ) : ι → ℝ) i * (Pi.single c (1 : ℝ) : ι → ℝ) j * G i j =
      (Pi.single a (1 : ℝ) : ι → ℝ) i * G i c := fun i => by
    rw [← sum_single_mul c fun j => (Pi.single a (1 : ℝ) : ι → ℝ) i * G i j]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => h i]
  exact sum_single_mul a fun i => G i c

/-- The polarization of a function on vectors: the matrix of its values on the sums of two
basis vectors. -/
def polar (q : (ι → ℝ) → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun a c =>
    (q (Pi.single a 1 + Pi.single c 1) - q (Pi.single a 1) - q (Pi.single c 1)) / 2

omit [Fintype ι] in
theorem polar_apply (q : (ι → ℝ) → ℝ) (a c : ι) :
    polar q a c =
      (q (Pi.single a 1 + Pi.single c 1) - q (Pi.single a 1) - q (Pi.single c 1)) / 2 :=
  rfl

omit [Fintype ι] in
theorem polar_comm (q : (ι → ℝ) → ℝ) (a c : ι) : polar q a c = polar q c a := by
  rw [polar_apply, polar_apply,
    add_comm (Pi.single a (1 : ℝ) : ι → ℝ) (Pi.single c (1 : ℝ) : ι → ℝ)]
  ring

/-- **A symmetric matrix is the polarization of its form.** -/
theorem polar_bilin {G : Matrix ι ι ℝ} (hG : ∀ a c, G a c = G c a) :
    polar (fun x => bilin G x x) = G := by
  ext a c
  rw [polar_apply, bilin_add_add, bilin_single, bilin_single, bilin_single, bilin_single,
    hG c a]
  ring

omit [Fintype ι] in
/-- Functions that converge on every vector have converging polarizations. -/
theorem tendsto_polar {β : Type*} {l : Filter β} {q : β → (ι → ℝ) → ℝ} {q₀ : (ι → ℝ) → ℝ}
    (h : ∀ x, Tendsto (fun n => q n x) l (𝓝 (q₀ x))) (a c : ι) :
    Tendsto (fun n => polar (q n) a c) l (𝓝 (polar q₀ a c)) := by
  simp only [polar_apply]
  exact (((h _).sub (h _)).sub (h _)).div_const 2

end Polar

/-- A negative `1 × 1` matrix has one negative square. -/
theorem hermNegIndex_single_neg {r : ℝ} (hr : r < 0) :
    hermNegIndex ((Matrix.of fun _ _ : Fin 1 => r).map (↑) : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  have h : ((Matrix.of fun _ _ : Fin 1 => r).map (↑) : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.diagonal fun _ => ((r : ℝ) : ℂ) := by
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp
  rw [h, negIndex_diagonal]
  simp [hr]

/-! ### Linear combinations of step functions -/

/-- The pairing of two linear combinations of step functions. -/
theorem rectSum_linear_comb {ι : Type*} [Fintype ι] (K : ℕ → ℕ → ℝ) (A B : Finset ℕ)
    (W : ι → ℕ → ℝ) (x y : ι → ℝ) :
    rectSum K A B (fun β => ∑ a, x a * W a β) (fun β => ∑ c, y c * W c β) =
      ∑ a, ∑ c, x a * y c * rectSum K A B (W a) (W c) := by
  unfold rectSum
  have h1 : ∀ α ∈ A, ∀ β ∈ B, (∑ a, x a * W a α) * (∑ c, y c * W c β) * K α β =
      ∑ a, ∑ c, x a * y c * (W a α * W c β * K α β) := fun α _ β _ => by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  have h2 : ∀ α ∈ A, ∑ β ∈ B, (∑ a, x a * W a α) * (∑ c, y c * W c β) * K α β =
      ∑ a, ∑ c, ∑ β ∈ B, x a * y c * (W a α * W c β * K α β) := fun α hα => by
    rw [Finset.sum_congr rfl fun β hβ => h1 α hα β hβ, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]

theorem sum_fin_mul_indicator {J : ℕ} (u : Fin J → ℝ) (n : ℕ) :
    ∑ p : Fin J, u p * (if n = (p : ℕ) then (1 : ℝ) else 0) = extendFin u n := by
  by_cases h : n < J
  · rw [extendFin, dif_pos h, Finset.sum_eq_single (⟨n, h⟩ : Fin J)]
    · rw [if_pos rfl, mul_one]
    · intro p _ hp
      rw [if_neg, mul_zero]
      intro hn
      exact hp (Fin.ext hn.symm)
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [extendFin, dif_neg h]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [if_neg, mul_zero]
    intro hn
    exact h (by rw [hn]; exact p.2)

theorem sum_fin_mul_eq_sum_range_extendFin {J : ℕ} (u : Fin J → ℝ) (w : ℕ → ℝ) :
    ∑ i, u i * w i = ∑ j ∈ range J, extendFin u j * w j := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => extendFin u j * w j) J]
  exact Finset.sum_congr rfl fun i _ => by rw [extendFin_coe]

/-! ### The frame of a window and of the pole -/

/-- The frame on the blocks of `(1, 2M]`: for a block `p` of the window `(R, R + J]` the vector
`u₁(e_p) − u₂ − (d(R + p)/ℓ)u₃`, and the vector `u₂ + u₃`. -/
def poleFrame (R J L M : ℕ) : Fin J ⊕ Fin 1 → ℕ → ℝ :=
  Sum.elim
    (fun p => probe R J L M (fun j => if j = (p : ℕ) then 1 else 0) 1 (-1)
      (-(blockDegree (R + (p : ℕ)) / blockDegree 1)))
    (fun _ => probe R J L M (fun _ => 0) 0 1 1)

/-- The step function of the first coordinates of a vector of the frame. -/
def frameStep {J : ℕ} (x : Fin J ⊕ Fin 1 → ℝ) : ℕ → ℝ := extendFin fun i => x (Sum.inl i)

/-- **The frame is linear**: a combination of the frame is the vector of the step function of
its coordinates, with the charges of that step function moved to the far window and to the
block one. -/
theorem sum_poleFrame (R J L M : ℕ) (x : Fin J ⊕ Fin 1 → ℝ) (b : ℕ) :
    ∑ a, x a * poleFrame R J L M a b =
      probe R J L M (frameStep x) 1 (x (Sum.inr 0) - 1 * ∑ j ∈ range J, frameStep x j)
        (x (Sum.inr 0) -
          1 * ((∑ j ∈ range J, frameStep x j * blockDegree (R + j)) / blockDegree 1)) b := by
  have hc₁ : ∑ p : Fin J, x (Sum.inl p) = ∑ j ∈ range J, frameStep x j :=
    sum_fin_eq_sum_range_extendFin _
  have hc₀ : ∑ p : Fin J, x (Sum.inl p) * blockDegree (R + (p : ℕ)) =
      ∑ j ∈ range J, frameStep x j * blockDegree (R + j) :=
    sum_fin_mul_eq_sum_range_extendFin _ fun j => blockDegree (R + j)
  -- the refinement is linear in the step function
  have hU : ∑ p : Fin J, x (Sum.inl p) *
        (if b ∈ Ico (L * R) (L * R + L * J) then
          refineStep L (fun j => if j = (p : ℕ) then 1 else 0) (b - L * R) else 0) =
      if b ∈ Ico (L * R) (L * R + L * J) then refineStep L (frameStep x) (b - L * R)
        else 0 := by
    by_cases hb : b ∈ Ico (L * R) (L * R + L * J)
    · simp only [if_pos hb, refineStep, frameStep]
      rw [← sum_fin_mul_indicator (fun p => x (Sum.inl p)) ((b - L * R) / L), Finset.sum_div]
      exact Finset.sum_congr rfl fun p _ => by ring
    · simp only [if_neg hb, mul_zero, Finset.sum_const_zero]
  have hsum : ∀ A B : ℝ, ∑ p : Fin J, x (Sum.inl p) *
        (1 * (if b ∈ Ico (L * R) (L * R + L * J) then
            refineStep L (fun j => if j = (p : ℕ) then 1 else 0) (b - L * R) else 0) +
          -1 * A + -(blockDegree (R + (p : ℕ)) / blockDegree 1) * B) =
      (∑ p : Fin J, x (Sum.inl p) *
        (if b ∈ Ico (L * R) (L * R + L * J) then
          refineStep L (fun j => if j = (p : ℕ) then 1 else 0) (b - L * R) else 0)) -
        (∑ p : Fin J, x (Sum.inl p)) * A -
        (∑ p : Fin J, x (Sum.inl p) * blockDegree (R + (p : ℕ))) / blockDegree 1 * B := by
    intro A B
    rw [Finset.sum_mul, Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [Fintype.sum_sum_type, Fin.sum_univ_one]
  simp only [poleFrame, Sum.elim_inl, Sum.elim_inr, probe]
  rw [← hc₁, ← hc₀, ← hU, hsum]
  ring

/-- The Gram matrix of the frame for the neutral part of the window `(1, 2M]`. -/
def poleGram (R J L M : ℕ) : Matrix (Fin J ⊕ Fin 1) (Fin J ⊕ Fin 1) ℝ :=
  Matrix.of fun a c => rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
    (poleFrame R J L M a) (poleFrame R J L M c)

theorem poleGram_comm (R J L M : ℕ) (a c : Fin J ⊕ Fin 1) :
    poleGram R J L M a c = poleGram R J L M c a :=
  rectSum_comm (neutralBlock_comm (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
    (poleFrame R J L M a) (poleFrame R J L M c)

theorem bilin_poleGram (R J L M : ℕ) (x : Fin J ⊕ Fin 1 → ℝ) :
    bilin (poleGram R J L M) x x =
      rectSum (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
        (fun b => ∑ a, x a * poleFrame R J L M a b)
        (fun b => ∑ a, x a * poleFrame R J L M a b) :=
  (rectSum_linear_comb (neutralBlock (M + M)) (Ico 1 (M + M)) (Ico 1 (M + M))
    (poleFrame R J L M) x x).symm

/-- The form on the vector of a step function and a real `t`, in the Gram coefficients. -/
def probeQuad (c₁ κ p₁₁ p₂₂ p₃₃ p₁₂ p₁₃ p₂₃ t : ℝ) : ℝ :=
  gramA c₁ κ p₁₁ p₂₂ p₃₃ p₁₂ p₁₃ p₂₃ * (1 : ℝ) ^ 2 +
    2 * gramB c₁ κ p₂₂ p₃₃ p₁₂ p₁₃ p₂₃ * 1 * t + gramC p₂₂ p₃₃ p₂₃ * t ^ 2

theorem tendsto_probeQuad {ι : Type*} {l : Filter ι} {f₁₁ f₂₂ f₃₃ f₁₂ f₁₃ f₂₃ : ι → ℝ}
    {a₁₁ a₂₂ a₃₃ a₁₂ a₁₃ a₂₃ : ℝ} (c₁ κ t : ℝ) (h₁₁ : Tendsto f₁₁ l (𝓝 a₁₁))
    (h₂₂ : Tendsto f₂₂ l (𝓝 a₂₂)) (h₃₃ : Tendsto f₃₃ l (𝓝 a₃₃)) (h₁₂ : Tendsto f₁₂ l (𝓝 a₁₂))
    (h₁₃ : Tendsto f₁₃ l (𝓝 a₁₃)) (h₂₃ : Tendsto f₂₃ l (𝓝 a₂₃)) :
    Tendsto (fun i => probeQuad c₁ κ (f₁₁ i) (f₂₂ i) (f₃₃ i) (f₁₂ i) (f₁₃ i) (f₂₃ i) t) l
      (𝓝 (probeQuad c₁ κ a₁₁ a₂₂ a₃₃ a₁₂ a₁₃ a₂₃ t)) := by
  unfold probeQuad
  exact (((tendsto_gramA c₁ κ h₁₁ h₂₂ h₃₃ h₁₂ h₁₃ h₂₃).mul_const _).add
    ((((tendsto_gramB c₁ κ h₂₂ h₃₃ h₁₂ h₁₃ h₂₃).const_mul 2).mul_const 1).mul_const t)).add
    ((tendsto_gramC h₂₂ h₃₃ h₂₃).mul_const _)

/-- **The form of the Gram matrix of the frame**, in the Gram coefficients of the three
vectors. -/
theorem bilin_poleGram_eq {R J Q₀ : ℕ} (hR : 1 ≤ R) (hQ₀ : R + J ≤ Q₀ * R) {L M : ℕ}
    (hL1 : 1 ≤ L) (hM1 : 1 ≤ M) (hLM : L * (R + J) ≤ M) (hQM : Q₀ ≤ M + M)
    (x : Fin J ⊕ Fin 1 → ℝ) :
    bilin (poleGram R J L M) x x =
      probeQuad (∑ j ∈ range J, frameStep x j)
        ((∑ j ∈ range J, frameStep x j * blockDegree (R + j)) / blockDegree 1)
        (∑ j ∈ range J, ∑ l ∈ range J,
          frameStep x j * frameStep x l * neutralBlock Q₀ (R + j) (R + l))
        (L * neutralBlock 0 1 1 / M) (neutralBlock 0 1 1 / L) (liftFar R J L M (frameStep x))
        (liftFirst R J L (frameStep x)) (farFirst L M) (x (Sum.inr 0)) := by
  rw [bilin_poleGram, show (fun b => ∑ a, x a * poleFrame R J L M a b) =
      probe R J L M (frameStep x) 1 (x (Sum.inr 0) - 1 * ∑ j ∈ range J, frameStep x j)
        (x (Sum.inr 0) -
          1 * ((∑ j ∈ range J, frameStep x j * blockDegree (R + j)) / blockDegree 1)) from
      funext (sum_poleFrame R J L M x),
    probe_form hR hQ₀ (frameStep x) hL1 hM1 hLM hQM]
  rfl

/-! ### The limit: the block matrix and one negative square -/

/-- The block matrix of the window `(R, R + J]` and one negative square. -/
def poleLimit (Q₀ R J : ℕ) : Matrix (Fin J ⊕ Fin 1) (Fin J ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (blockWindow Q₀ R J) 0 0 (Matrix.of fun _ _ => -2 * blockDegree 1)

theorem poleLimit_comm (Q₀ R J : ℕ) (a c : Fin J ⊕ Fin 1) :
    poleLimit Q₀ R J a c = poleLimit Q₀ R J c a := by
  rcases a with a | a <;> rcases c with c | c
  · show blockMatrix Q₀ (R + (a : ℕ)) (R + (c : ℕ)) = blockMatrix Q₀ (R + (c : ℕ)) (R + (a : ℕ))
    exact blockMatrix_comm _ _ _
  · rfl
  · rfl
  · rfl

/-- The form of the limit: the form of the block matrix minus `2ℓt²`. -/
theorem bilin_poleLimit (Q₀ R J : ℕ) (x : Fin J ⊕ Fin 1 → ℝ) :
    bilin (poleLimit Q₀ R J) x x =
      2 * (∑ j ∈ range J, frameStep x j) * (∑ j ∈ range J, frameStep x j * blockDegree (R + j)) +
        ∑ j ∈ range J, ∑ l ∈ range J,
          frameStep x j * frameStep x l * neutralBlock Q₀ (R + j) (R + l) +
        -2 * blockDegree 1 * x (Sum.inr 0) ^ 2 := by
  have h1 : bilin (poleLimit Q₀ R J) x x =
      (∑ i : Fin J, ∑ j : Fin J, x (Sum.inl i) * x (Sum.inl j) * blockWindow Q₀ R J i j) +
        x (Sum.inr 0) * x (Sum.inr 0) * (-2 * blockDegree 1) := by
    simp only [bilin, poleLimit, Fintype.sum_sum_type, Fin.sum_univ_one,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.of_apply, mul_zero, add_zero,
      zero_add, Finset.sum_const_zero]
  rw [h1, blockWindow, sum_fin_windowMatrix_eq, sum_blockMatrix_eq_charges_add_neutral]
  simp only [frameStep]
  ring

/-- The index of the limit is the index of the block matrix plus one. -/
theorem hermNegIndex_blockWindow_add_one_le_poleLimit (Q₀ R J : ℕ) :
    hermNegIndex ((blockWindow Q₀ R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) + 1 ≤
      hermNegIndex ((poleLimit Q₀ R J).map (↑) : Matrix (Fin J ⊕ Fin 1) (Fin J ⊕ Fin 1) ℂ) := by
  have hmap : ((poleLimit Q₀ R J).map (↑) : Matrix (Fin J ⊕ Fin 1) (Fin J ⊕ Fin 1) ℂ) =
      Matrix.fromBlocks ((blockWindow Q₀ R J).map (↑)) 0 0
        ((Matrix.of fun _ _ : Fin 1 => -2 * blockDegree 1).map (↑)) := by
    rw [poleLimit, Matrix.fromBlocks_map]
    simp
  have h := AdelicKreinGeometry.hermNegIndex_add_le_fromBlocks
    ((blockWindow Q₀ R J).map (↑) : Matrix (Fin J) (Fin J) ℂ)
    ((Matrix.of fun _ _ : Fin 1 => -2 * blockDegree 1).map (↑) : Matrix (Fin 1) (Fin 1) ℂ)
  rw [hermNegIndex_single_neg (by linarith [blockDegree_one_pos])] at h
  rw [hmap]
  exact h

/-! ### The pole adds one negative square -/

/-- The limit of the form of the Gram matrix of the frame as the far window recedes. -/
def frameLimit (Q₀ R J L : ℕ) (x : Fin J ⊕ Fin 1 → ℝ) : ℝ :=
  probeQuad (∑ j ∈ range J, frameStep x j)
    ((∑ j ∈ range J, frameStep x j * blockDegree (R + j)) / blockDegree 1)
    (∑ j ∈ range J, ∑ l ∈ range J,
      frameStep x j * frameStep x l * neutralBlock Q₀ (R + j) (R + l))
    0 (neutralBlock 0 1 1 / L) (-∑ j ∈ range J, frameStep x j * blockDegree (R + j))
    (liftFirst R J L (frameStep x)) (-blockDegree 1) (x (Sum.inr 0))

/-- As the far window recedes the form of the Gram matrix tends to `frameLimit`. -/
theorem tendsto_bilin_poleGram {R J Q₀ : ℕ} (hR : 1 ≤ R) (hQ₀ : R + J ≤ Q₀ * R) {L : ℕ}
    (hL1 : 1 ≤ L) (x : Fin J ⊕ Fin 1 → ℝ) :
    Tendsto (fun M : ℕ => bilin (poleGram R J L M) x x) atTop (𝓝 (frameLimit Q₀ R J L x)) := by
  have hc : ∀ r : ℝ, Tendsto (fun _ : ℕ => r) atTop (𝓝 r) := fun _ => tendsto_const_nhds
  have h22 : Tendsto (fun M : ℕ => (L : ℝ) * neutralBlock 0 1 1 / (M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim := tendsto_probeQuad (∑ j ∈ range J, frameStep x j)
    ((∑ j ∈ range J, frameStep x j * blockDegree (R + j)) / blockDegree 1) (x (Sum.inr 0))
    (hc (∑ j ∈ range J, ∑ l ∈ range J,
      frameStep x j * frameStep x l * neutralBlock Q₀ (R + j) (R + l)))
    h22 (hc (neutralBlock 0 1 1 / L)) (tendsto_liftFar hR hL1 J (frameStep x))
    (hc (liftFirst R J L (frameStep x))) (tendsto_farFirst hL1)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (max 1 (max (L * (R + J)) Q₀))] with M hMge
  have hM1 : 1 ≤ M := (le_max_left _ _).trans hMge
  have hLM : L * (R + J) ≤ M := ((le_max_left _ _).trans (le_max_right _ _)).trans hMge
  have hQM : Q₀ ≤ M + M := (((le_max_right _ _).trans (le_max_right _ _)).trans hMge).trans
    (Nat.le_add_right M M)
  exact (bilin_poleGram_eq hR hQ₀ hL1 hM1 hLM hQM x).symm

/-- As the refinement grows `frameLimit` tends to the form of the block matrix and one negative
square. -/
theorem tendsto_frameLimit {R : ℕ} (hR : 1 ≤ R) (Q₀ J : ℕ) (x : Fin J ⊕ Fin 1 → ℝ) :
    Tendsto (fun L : ℕ => frameLimit Q₀ R J L x) atTop
      (𝓝 (bilin (poleLimit Q₀ R J) x x)) := by
  have hc : ∀ r : ℝ, Tendsto (fun _ : ℕ => r) atTop (𝓝 r) := fun _ => tendsto_const_nhds
  have h33 : Tendsto (fun L : ℕ => neutralBlock 0 1 1 / (L : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim := tendsto_probeQuad (∑ j ∈ range J, frameStep x j)
    ((∑ j ∈ range J, frameStep x j * blockDegree (R + j)) / blockDegree 1) (x (Sum.inr 0))
    (hc (∑ j ∈ range J, ∑ l ∈ range J,
      frameStep x j * frameStep x l * neutralBlock Q₀ (R + j) (R + l)))
    (hc 0) h33 (hc (-∑ j ∈ range J, frameStep x j * blockDegree (R + j)))
    (tendsto_liftFirst hR J (frameStep x)) (hc (-blockDegree 1))
  have hℓ := blockDegree_one_pos
  have hκ : (∑ j ∈ range J, frameStep x j * blockDegree (R + j)) / blockDegree 1 *
      blockDegree 1 = ∑ j ∈ range J, frameStep x j * blockDegree (R + j) :=
    div_mul_cancel₀ _ hℓ.ne'
  have hval : probeQuad (∑ j ∈ range J, frameStep x j)
      ((∑ j ∈ range J, frameStep x j * blockDegree (R + j)) / blockDegree 1)
      (∑ j ∈ range J, ∑ l ∈ range J,
        frameStep x j * frameStep x l * neutralBlock Q₀ (R + j) (R + l))
      0 0 (-∑ j ∈ range J, frameStep x j * blockDegree (R + j))
      (-(blockDegree 1 * ∑ j ∈ range J, frameStep x j)) (-blockDegree 1) (x (Sum.inr 0)) =
      bilin (poleLimit Q₀ R J) x x := by
    rw [bilin_poleLimit]
    unfold probeQuad gramA gramB gramC
    linear_combination (2 * x (Sum.inr 0)) * hκ
  rw [hval] at hlim
  exact hlim

/-- **The pole adds one negative square.** For every window `(R, R + J]` there is a window
`(1, 2M]` whose neutral part has at least one negative square more than the block matrix of
`(R, R + J]`. -/
theorem exists_hermNegIndex_blockWindow_add_one_le {R J Q₀ : ℕ} (hR : 1 ≤ R)
    (hQ₀ : R + J ≤ Q₀ * R) :
    ∃ M : ℕ, 1 ≤ M ∧
      hermNegIndex ((blockWindow Q₀ R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) + 1 ≤
        hermNegIndex ((neutralWindow (M + M) 1 (M + M - 1)).map (↑) :
          Matrix (Fin (M + M - 1)) (Fin (M + M - 1)) ℂ) := by
  -- the refinement: the polarizations of `frameLimit` tend to the limit matrix
  have hpl := polar_bilin (poleLimit_comm Q₀ R J)
  have hstage₁ := HeckeKreinToeplitz.eventually_le_hermNegIndex
    (H := fun L : ℕ => ((polar (frameLimit Q₀ R J L)).map (↑) :
      Matrix (Fin J ⊕ Fin 1) (Fin J ⊕ Fin 1) ℂ))
    (isHermitian_map_ofReal (poleLimit_comm Q₀ R J)) fun a c => by
      have h := tendsto_polar (fun x => tendsto_frameLimit hR Q₀ J x) a c
      rw [hpl] at h
      exact (Complex.continuous_ofReal.tendsto _).comp h
  obtain ⟨L, hL1, hL⟩ := ((eventually_ge_atTop 1).and hstage₁).exists
  -- the far window: the Gram matrices tend to the polarization of `frameLimit`
  have hstage₂ := HeckeKreinToeplitz.eventually_le_hermNegIndex
    (H := fun M : ℕ => ((poleGram R J L M).map (↑) :
      Matrix (Fin J ⊕ Fin 1) (Fin J ⊕ Fin 1) ℂ))
    (isHermitian_map_ofReal (polar_comm (frameLimit Q₀ R J L))) fun a c => by
      have h := tendsto_polar (fun x => tendsto_bilin_poleGram hR hQ₀ hL1 x) a c
      have he : (fun M : ℕ => polar (fun x => bilin (poleGram R J L M) x x) a c) =
          fun M : ℕ => poleGram R J L M a c := by
        funext M
        rw [polar_bilin (poleGram_comm R J L M)]
      rw [he] at h
      exact (Complex.continuous_ofReal.tendsto _).comp h
  obtain ⟨M, hM1, hM⟩ := ((eventually_ge_atTop 1).and hstage₂).exists
  refine ⟨M, hM1, ?_⟩
  -- the Gram matrix of the frame has at most the index of the neutral part
  have hgram := hermNegIndex_gram_le (neutralWindow (M + M) 1 (M + M - 1))
    (fun a (k : Fin (M + M - 1)) => poleFrame R J L M a (1 + (k : ℕ))) (poleGram R J L M)
    fun y => (sum_fin_neutralWindow_eq_rectSum hM1 (M + M)
      fun b => ∑ a, y a * poleFrame R J L M a b).trans (bilin_poleGram R J L M y).symm
  exact (hermNegIndex_blockWindow_add_one_le_poleLimit Q₀ R J).trans (hL.trans (hM.trans hgram))

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
