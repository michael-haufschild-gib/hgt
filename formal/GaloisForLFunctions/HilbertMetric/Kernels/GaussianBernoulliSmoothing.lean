import GaloisForLFunctions.HilbertMetric.Kernels.GaussianCollocation

/-!
# Gaussian smoothing of finite Bernoulli convolutions

Salazar's two-sided Toeplitz smoothing theorem (arXiv:2607.02778, §4)
has a finite-factor proof for products of Bernoulli factors. Expanding in
the rows gives weakly ordered integer grids; a collision kills its term.
The unchanged grid supplies an explicit lower bound on every minor.
-/

namespace GaloisForLFunctions.HilbertMetric
open Finset Matrix Filter Topology
open scoped Classical NNReal
noncomputable section

/-- A two-sided Toeplitz sampling matrix, including independently translated grids. -/
def latticeSample {n : ℕ} (a : ℤ → ℝ) (x y : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => a (x i - y j)

/-- Strict positivity of all square minors with increasingly ordered lattice sites. -/
def StrictLatticeMinors (a : ℤ → ℝ) : Prop :=
  ∀ (n : ℕ) (x y : Fin n ↪o ℤ), 0 < (latticeSample a x y).det

/-- One unnormalized Bernoulli convolution. -/
def bernoulliStep (w : ℝ≥0) (a : ℤ → ℝ) (k : ℤ) : ℝ := a k + w * a (k-1)

private theorem latticeSample_det_nonneg {a : ℤ → ℝ} (ha : StrictLatticeMinors a)
    {n : ℕ} (z : Fin n → ℤ) (hz : Monotone z) (y : Fin n ↪o ℤ) :
    0 ≤ (latticeSample a z y).det := by
  by_cases h : Function.Injective z
  · exact (ha n (OrderEmbedding.ofStrictMono z (hz.strictMono_of_injective h)) y).le
  · obtain ⟨i,j,he,hne⟩ := Function.not_injective_iff.mp h
    rw [det_zero_of_row_eq hne (by ext k; simp [latticeSample, he])]

/-- Each Bernoulli step increases every ordered minor of a strictly positive input. -/
theorem bernoulliStep_minor_ge {a : ℤ → ℝ} (ha : StrictLatticeMinors a) (w : ℝ≥0)
    {n : ℕ} (x y : Fin n ↪o ℤ) :
    (latticeSample a x y).det ≤ (latticeSample (bernoulliStep w a) x y).det := by
  let A := latticeSample a x y
  let B : Matrix (Fin n) (Fin n) ℝ := of fun i j => (w:ℝ)*a (x i-y j-1)
  have hm : latticeSample (bernoulliStep w a) x y = A+B := rfl
  have hex : (A+B).det = ∑ S : Finset (Fin n), Matrix.det (S.piecewise A B) :=
    detRowAlternating.map_add_univ A B
  rw [hm,hex]
  have ht (S : Finset (Fin n)) : 0 ≤ Matrix.det (S.piecewise A B) := by
    let z i := if i ∈ S then x i else x i-1
    have hz : Monotone z := by
      intro i j hij
      rcases eq_or_lt_of_le hij with rfl | h
      · exact le_rfl
      · have hlt := x.strictMono h
        dsimp [z]
        split_ifs <;> omega
    let c := fun i => if i ∈ S then (1:ℝ) else w
    have hs : (S.piecewise A B : Matrix _ _ ℝ) =
        of (fun i j => c i * latticeSample a z y i j) := by
      ext i j
      by_cases hi : i ∈ S <;> simp [piecewise, A, B, c, z, latticeSample, hi, sub_right_comm]
    rw [hs, det_mul_column]
    exact mul_nonneg (prod_nonneg fun i _ => by dsimp [c]; split_ifs <;> positivity)
      (latticeSample_det_nonneg ha z hz y)
  have h := single_le_sum (fun S (_ : S ∈ univ) => ht S) (mem_univ (univ : Finset (Fin n)))
  simpa [A] using h

/-- Finite products of arbitrary Bernoulli factors. -/
def bernoulliProduct : List ℝ≥0 → (ℤ → ℝ) → ℤ → ℝ
  | [], a => a
  | w::ws, a => bernoulliStep w (bernoulliProduct ws a)

/-- No minor drops below the unsmoothed Gaussian minor, for any finite product of factors. -/
theorem bernoulliProduct_minor_ge {a : ℤ → ℝ} (ha : StrictLatticeMinors a) (ws : List ℝ≥0) :
    ∀ (n : ℕ) (x y : Fin n ↪o ℤ),
    (latticeSample a x y).det ≤ (latticeSample (bernoulliProduct ws a) x y).det := by
  induction ws with
  | nil => exact fun _ _ _ => le_rfl
  | cons w ws ih =>
    exact fun n x y => (ih n x y).trans
      (bernoulliStep_minor_ge (fun m r c => (ha m r c).trans_le (ih m r c)) w x y)

/-- Gaussian approximants to every finite Bernoulli convolution have positive minors
of every order, including minors arbitrarily far outside the limiting support. -/
theorem gaussianBernoulli_strict (q : Set.Ioo (0:ℝ) 1) (ws : List ℝ≥0) :
    StrictLatticeMinors (bernoulliProduct ws (fun k => q.val ^ (k.natAbs^2))) := by
  have h : StrictLatticeMinors (fun k : ℤ => q.val ^ (k.natAbs^2)) :=
    fun _ x y => discreteGaussian_minor_pos q x y
  exact fun n x y => (h n x y).trans_le (bernoulliProduct_minor_ge h ws n x y)

/-- The same path extends continuously to the finite-support coefficient sequence. -/
theorem gaussianBernoulli_limit (ws : List ℝ≥0) (k : ℤ) :
    Tendsto (fun q : ℝ => bernoulliProduct ws (fun j => q ^ (j.natAbs^2)) k) (𝓝 0)
      (𝓝 (bernoulliProduct ws (fun j => if j = 0 then 1 else 0) k)) := by
  induction ws generalizing k with
  | nil =>
    have h : (0:ℝ)^(k.natAbs^2) = (if k = 0 then 1 else 0) := by
      by_cases hk : k = 0 <;> simp [hk]
    simp only [bernoulliProduct, ← h]
    exact (continuous_id.pow _).tendsto _
  | cons w ws ih =>
    exact (ih k).add (tendsto_const_nhds.mul (ih (k-1)))

/-- Total mass of a finite unnormalized Bernoulli convolution. -/
def bernoulliMass : List ℝ≥0 → ℝ
  | [] => 1
  | w :: ws => (1+(w:ℝ))*bernoulliMass ws

private theorem product_error (ws : List ℝ≥0) {f g : ℤ → ℝ} {M : ℝ}
    (h : ∀ k, f k-g k ∈ Set.Icc 0 M) (k : ℤ) :
    bernoulliProduct ws f k - bernoulliProduct ws g k ∈ Set.Icc 0 (M*bernoulliMass ws) := by
  induction ws generalizing k with
  | nil => simpa [bernoulliProduct,bernoulliMass] using h k
  | cons w ws ih =>
    obtain ⟨ha,hb⟩ := ih k
    obtain ⟨hc,hd⟩ := ih (k-1)
    change 0 ≤ _ ∧ _ ≤ M*((1+(w:ℝ))*bernoulliMass ws)
    dsimp only [bernoulliProduct,bernoulliStep]
    rw [show bernoulliProduct ws f k + (w:ℝ)*bernoulliProduct ws f (k-1) -
        (bernoulliProduct ws g k + (w:ℝ)*bernoulliProduct ws g (k-1)) =
        (bernoulliProduct ws f k - bernoulliProduct ws g k) +
        (w:ℝ)*(bernoulliProduct ws f (k-1)-bernoulliProduct ws g (k-1)) by ring]
    refine ⟨add_nonneg ha (mul_nonneg w.property hc),?_⟩
    apply (add_le_add hb (mul_le_mul_of_nonneg_left hd (show 0 ≤ (w:ℝ) from w.property))).trans_eq
    change M*bernoulliMass ws+(w:ℝ)*(M*bernoulliMass ws) = M*((1+(w:ℝ))*bernoulliMass ws)
    ring

private theorem product_mask (S : Finset ℤ) (a : ℤ → ℝ) (ws : List ℝ≥0) (k : ℤ) :
    bernoulliProduct ws (fun j => if j ∈ S then a j else 0) k =
      ∑ j ∈ S, a j * bernoulliProduct ws (fun t => if t = 0 then 1 else 0) (k-j) := by
  induction ws generalizing k with
  | nil => simp [bernoulliProduct,mul_ite,sub_eq_zero]
  | cons w ws ih =>
    change bernoulliProduct ws _ k + (w:ℝ)*bernoulliProduct ws _ (k-1) = _
    rw [ih k,ih (k-1),mul_sum,← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    dsimp only [bernoulliProduct,bernoulliStep]
    rw [show k-1-j = k-j-1 by ring]
    ring

/-- Truncating the spatial Gaussian at distance `r` gives a uniform
error controlled by the next square exponent. This strengthens pointwise
density to an all-orders approximation on the entire integer lattice. -/
theorem gaussianBernoulli_shell_error (q : Set.Icc (0:ℝ) 1) (r : ℕ) (ws : List ℝ≥0) (k : ℤ) :
    bernoulliProduct ws (fun j => q.val^(j.natAbs^2)) k -
      (∑ j ∈ Icc (-(r:ℤ)) r, q.val^(j.natAbs^2) *
        bernoulliProduct ws (fun t => if t = 0 then 1 else 0) (k-j)) ∈
      Set.Icc 0 (q.val^((r+1)^2)*bernoulliMass ws) := by
  rw [← product_mask]
  apply product_error
  intro j
  by_cases hj : j ∈ Icc (-(r:ℤ)) r
  · simp [hj,pow_nonneg q.property.1]
  · rw [if_neg hj,sub_zero]
    have hdist : r+1 ≤ j.natAbs := by
      rw [mem_Icc] at hj
      cases j <;> simp_all
      omega
    exact ⟨pow_nonneg q.property.1 _,pow_le_pow_of_le_one q.property.1 q.property.2
      (Nat.pow_le_pow_left hdist 2)⟩

/-- The first omitted shell attains the uniform rate for the unsmoothed
point mass. Thus its square exponent is optimal even among finite products. -/
theorem gaussian_shell_error_attained (q : Set.Icc (0:ℝ) 1) (r : ℕ) :
    let k : ℤ := (r+1:ℕ)
    bernoulliProduct [] (fun j => q.val^(j.natAbs^2)) k -
      (∑ j ∈ Icc (-(r:ℤ)) r, q.val^(j.natAbs^2) *
        bernoulliProduct [] (fun t => if t = 0 then 1 else 0) (k-j)) = q.val^((r+1)^2) := by
  dsimp only
  rw [← product_mask]
  have ho : ((r+1:ℕ):ℤ) ∉ Icc (-(r:ℤ)) r := by simp
  simp only [bernoulliProduct,if_neg ho,sub_zero,Int.natAbs_natCast]

#print axioms gaussianBernoulli_strict
#print axioms gaussianBernoulli_limit
#print axioms gaussianBernoulli_shell_error
#print axioms gaussian_shell_error_attained

end
end GaloisForLFunctions.HilbertMetric
