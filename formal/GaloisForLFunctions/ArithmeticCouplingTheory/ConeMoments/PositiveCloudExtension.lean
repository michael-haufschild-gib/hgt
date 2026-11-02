import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveMomentExtension

/-!
# Positive atomic prefixes with exact moment cancellation

Finite clouds concatenate without changing old coordinates. A prefix at level
`k` has mass `2 - 2⁻ᵏ`, vanishes on its finite frequency set, and places atom
number `j` above height `j + 1`. Each weight dominates the reciprocal of one
plus its height. Exponential tail control constructs the next prefix by adding
a positive block of mass `2⁻⁽ᵏ⁺¹⁾` at the next real level.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Finite positive atomic approximants are assembled by concatenating their coordinates. -/
structure Cloud where
  size : ℕ
  point : Fin size → ℂ
  weight : Fin size → ℝ

def Cloud.mass (c : Cloud) : ℝ := ∑ j, c.weight j

def Cloud.moment (c : Cloud) (u : ℝ) : ℂ := finiteLaplaceSum c.point c.weight u

def Cloud.append (c b : Cloud) : Cloud where
  size := c.size + b.size
  point := Fin.append c.point b.point
  weight := Fin.append c.weight b.weight

lemma Cloud.mass_append (c b : Cloud) : (c.append b).mass = c.mass + b.mass := by
  change (∑ j : Fin (c.size + b.size), Fin.append c.weight b.weight j) = c.mass + b.mass
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Cloud.mass]

lemma Cloud.moment_append (c b : Cloud) (u : ℝ) :
    (c.append b).moment u = c.moment u + b.moment u := by
  change (∑ j : Fin (c.size + b.size), ((Fin.append c.weight b.weight j : ℝ) : ℂ) *
    Complex.exp ((u : ℂ) * Fin.append c.point b.point j)) = c.moment u + b.moment u
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Cloud.moment, finiteLaplaceSum]

lemma Cloud.positive_append (c b : Cloud)
    (hc : ∀ j, 0 < c.weight j) (hb : ∀ j, 0 < b.weight j) :
    ∀ j, 0 < (c.append b).weight j := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [Cloud.append, Fin.append_left] using hc i
  · simpa only [Cloud.append, Fin.append_right] using hb i

lemma Cloud.real_bound_append (c b : Cloud) {D : ℝ}
    (hc : ∀ j, (c.point j).re ≤ D) (hb : ∀ j, (b.point j).re ≤ D) :
    ∀ j, ((c.append b).point j).re ≤ D := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [Cloud.append, Fin.append_left] using hc i
  · simpa only [Cloud.append, Fin.append_right] using hb i

def levelCloud {n : ℕ} (D : ℝ) (x w : Fin n → ℝ) : Cloud where
  size := n
  point := fun j => (D : ℂ) + (x j : ℂ) * Complex.I
  weight := w

lemma levelCloud_real {n : ℕ} (D : ℝ) (x w : Fin n → ℝ) (j : Fin n) :
    ((levelCloud D x w).point j).re = D := by
  simp only [levelCloud, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]

lemma levelCloud_im {n : ℕ} (D : ℝ) (x w : Fin n → ℝ) (j : Fin n) :
    ((levelCloud D x w).point j).im = x j := by
  simp only [levelCloud, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]

lemma Cloud.reciprocal_append (c b : Cloud)
    (hc : ∀ j, 1 / (1 + |(c.point j).im|) ≤ c.weight j)
    (hb : ∀ j, 1 / (1 + |(b.point j).im|) ≤ b.weight j) :
    ∀ j, 1 / (1 + |((c.append b).point j).im|) ≤ (c.append b).weight j := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [Cloud.append, Fin.append_left] using hc i
  · simpa only [Cloud.append, Fin.append_right] using hb i

lemma Cloud.rank_height_append (c b : Cloud)
    (hc : ∀ j, ((j.val + 1 : ℕ) : ℝ) ≤ (c.point j).im)
    (hb : ∀ j, ((c.size + j.val + 1 : ℕ) : ℝ) ≤ (b.point j).im) :
    ∀ j, ((j.val + 1 : ℕ) : ℝ) ≤ ((c.append b).point j).im := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [Cloud.append, Fin.append_left, Fin.val_castAdd] using hc i
  · simpa only [Cloud.append, Fin.append_right, Fin.val_natAdd] using hb i

lemma reciprocal_le_weight {x w η : ℝ} (hη : 0 < η) (hx : 1 / η ≤ x) (hw : η ≤ w) :
    1 / (1 + |x|) ≤ w := by
  apply (div_le_iff₀ (by positivity : 0 < 1 + |x|)).mpr
  have hprod : 1 ≤ x * η := (div_le_iff₀ hη).mp hx
  have hxabs : x ≤ 1 + |x| := by linarith [le_abs_self x]
  calc 1 ≤ x * η := hprod
    _ ≤ (1 + |x|) * η := mul_le_mul_of_nonneg_right hxabs hη.le
    _ ≤ (1 + |x|) * w := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = w * (1 + |x|) := by ring

lemma Cloud.append_point_left (c b : Cloud) (j : Fin c.size) :
    (c.append b).point (Fin.castAdd b.size j) = c.point j := Fin.append_left _ _ _

lemma Cloud.append_weight_left (c b : Cloud) (j : Fin c.size) :
    (c.append b).weight (Fin.castAdd b.size j) = c.weight j := Fin.append_left _ _ _

/-- Every prefix has a fixed mass, a real-part bound, cancelled moments, and sparse heights. -/
structure CloudStage (S : ℕ → Finset ℝ) (δ : ℕ → ℝ) (k : ℕ) where
  cloud : Cloud
  positive : ∀ j, 0 < cloud.weight j
  real_bound : ∀ j, (cloud.point j).re ≤ δ k
  real_lower : ∀ j, δ 0 ≤ (cloud.point j).re
  mass_eq : cloud.mass = 2 - (1 / 2 : ℝ) ^ k
  zero : ∀ u ∈ S k, cloud.moment u = 0
  rank_height : ∀ j, ((j.val + 1 : ℕ) : ℝ) ≤ (cloud.point j).im
  reciprocal_weight : ∀ j, 1 / (1 + |(cloud.point j).im|) ≤ cloud.weight j

lemma levelCloud_moment {n : ℕ} (D u : ℝ) (x w : Fin n → ℝ) :
    (levelCloud D x w).moment u =
      (Real.exp (D * u) : ℂ) * ∑ j, (w j : ℂ) * phase u (x j) := by
  simp only [Cloud.moment, finiteLaplaceSum, levelCloud, exp_level_eq, Finset.mul_sum]
  exact sum_congr rfl fun j _ => by ring

lemma exists_initial_stage (S : ℕ → Finset ℝ) (δ : ℕ → ℝ)
    (hS : ∀ u ∈ S 0, 0 < u) :
    ∃ c : CloudStage S δ 0, 0 < c.cloud.size := by
  obtain ⟨n, hn, hc⟩ := exists_positive_correction (S 0) hS (fun _ => 0)
    (A := 1) (by norm_num) (by simp)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let η : ℝ := 1 / (2 * n)
  have hη : 0 < η := div_pos zero_lt_one (mul_pos (by norm_num) hnR)
  obtain ⟨x, w, hx, hw, hm, hz⟩ := hc ((n : ℝ) + 1 + 1 / η)
  let c : CloudStage S δ 0 := {
    cloud := levelCloud (δ 0) x w
    positive := fun j => (hw j).1
    real_bound := fun j => (levelCloud_real (δ 0) x w j).le
    real_lower := fun j => (levelCloud_real (δ 0) x w j).ge
    mass_eq := by
      change (∑ j, w j) = 2 - (1 / 2 : ℝ) ^ 0
      convert hm using 1; norm_num
    zero := by
      intro u hu
      rw [levelCloud_moment, hz u hu]
      simp
    rank_height := by
      intro j
      rw [levelCloud_im]
      have hj : ((j.val + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt j.isLt
      have hnonneg : 0 ≤ 1 / η := (div_pos zero_lt_one hη).le
      linarith [hx j]
    reciprocal_weight := by
      intro j
      rw [levelCloud_im]
      apply reciprocal_le_weight hη ?_ (hw j).2.1
      have hn0 : (0 : ℝ) ≤ n := hnR.le
      linarith [hx j]
  }
  exact ⟨c, hn⟩

/-- An extension records its appended block, so every old atom retains its index. -/
structure StageExtension {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} {k : ℕ}
    (c : CloudStage S δ k) where
  size : ℕ
  size_pos : 0 < size
  height : Fin size → ℝ
  weight : Fin size → ℝ
  next : CloudStage S δ (k + 1)
  cloud_eq : next.cloud = c.cloud.append (levelCloud (δ (k + 1)) height weight)

lemma exists_stage_extension {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} {k : ℕ}
    (c : CloudStage S δ k) (hS : ∀ u ∈ S (k + 1), 0 < u)
    (hδ : δ k ≤ δ (k + 1)) (hδ0 : δ 0 ≤ δ (k + 1))
    (htail : 2 * ∑ u ∈ S (k + 1) \ S k,
      Real.exp (-(δ (k + 1) - δ k) * u) ≤ (1 / 2 : ℝ) ^ (k + 1) / 4) :
    Nonempty (StageExtension c) := by
  have hM : c.cloud.mass ≤ 2 := by
    rw [c.mass_eq]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]
  have hA : 0 < (1 / 2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
  obtain ⟨n, hn, hc⟩ := exists_positive_level_extension c.cloud.point c.cloud.weight
    (S (k + 1)) (S k) (fun j => (c.positive j).le) c.real_bound hM hS c.zero hA htail
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let η : ℝ := (1 / 2 : ℝ) ^ (k + 1) / (2 * n)
  have hη : 0 < η := div_pos hA (mul_pos (by norm_num) hnR)
  obtain ⟨x, w, hx, hw, hm, hz⟩ := hc (((c.cloud.size + n : ℕ) : ℝ) + 1 + 1 / η)
  let b := levelCloud (δ (k + 1)) x w
  let q : CloudStage S δ (k + 1) := {
    cloud := c.cloud.append b
    positive := Cloud.positive_append c.cloud b c.positive (fun j => (hw j).1)
    real_bound := Cloud.real_bound_append c.cloud b
      (fun j => (c.real_bound j).trans hδ) (fun j => (levelCloud_real _ x w j).le)
    real_lower := by
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [Cloud.append, Fin.append_left] using c.real_lower i
      · simp only [Cloud.append, Fin.append_right]
        rw [levelCloud_real]
        exact hδ0
    mass_eq := by
      rw [Cloud.mass_append, c.mass_eq]
      change (2 - (1 / 2 : ℝ) ^ k) + (∑ j, w j) = 2 - (1 / 2 : ℝ) ^ (k + 1)
      rw [hm, pow_succ]
      ring
    zero := by
      intro u hu
      rw [Cloud.moment_append]
      exact hz u hu
    rank_height := Cloud.rank_height_append c.cloud b c.rank_height (by
      intro j
      rw [levelCloud_im]
      have hjn : j.val < n := j.isLt
      have hj : ((c.cloud.size + j.val + 1 : ℕ) : ℝ) ≤ (c.cloud.size + n : ℕ) := by
        exact_mod_cast (show c.cloud.size + j.val + 1 ≤ c.cloud.size + n by omega)
      have hnonneg : 0 ≤ 1 / η := (div_pos zero_lt_one hη).le
      linarith [hx j])
    reciprocal_weight := Cloud.reciprocal_append c.cloud b c.reciprocal_weight (by
      intro j
      rw [levelCloud_im]
      apply reciprocal_le_weight hη ?_ (hw j).2.1
      have hsize0 : (0 : ℝ) ≤ (c.cloud.size + n : ℕ) := Nat.cast_nonneg _
      linarith [hx j])
  }
  exact ⟨{
    size := n
    size_pos := hn
    height := x
    weight := w
    next := q
    cloud_eq := rfl
  }⟩

#print axioms exists_initial_stage
#print axioms exists_stage_extension
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
