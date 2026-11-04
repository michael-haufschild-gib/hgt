import GaloisForLFunctions.HTGeometry.LatticeMinimalVectors
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Round

/-!
# Successive minima in rank two

For a rank-two adelic vector space with an integral model over `ℤ`, Minkowski's theorem on
successive minima provides two linearly independent sections whose heights add up to at most
`-deg + A` with an absolute constant `A`.  At the archimedean place this is a statement about a
lattice `L = ℤ b₀ + ℤ b₁` in a real inner product space with Gram determinant
`G = ‖b₀‖² ‖b₁‖² - ⟪b₀, b₁⟫²` (the squared covolume):

  there are `v₁, v₂ ∈ L` spanning a sublattice of the same covolume with
  `‖v₁‖² ‖v₂‖² ≤ (4/3) G`,

so `log ‖v₁‖ + log ‖v₂‖ ≤ (1/2) log G + log (2/√3)`.

The proof is Lagrange–Gauss reduction, starting from a shortest nonzero vector
(`HTGeometry.exists_minimal_norm`): a shortest vector is primitive, so it extends to a basis
`(v₁, u)` with the same Gram determinant; shearing `u` by the nearest integer multiple of `v₁`
gives `v₂` with `|⟪v₁, v₂⟫| ≤ ‖v₁‖²/2 ≤ ‖v₁‖ ‖v₂‖/2`, hence `G ≥ (3/4) ‖v₁‖² ‖v₂‖²`.
-/

noncomputable section

open Submodule

namespace GaloisForLFunctions.KodairaParshinAbc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The Gram determinant `‖x‖² ‖y‖² - ⟪x, y⟫²`. -/
def gramDet (x y : E) : ℝ := ‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫ ^ 2

/-- **Unimodular change of basis**: for `x = m b₀ + n b₁`, `y = p b₀ + q b₁`,
`gramDet x y = (mq - np)² gramDet b₀ b₁`. -/
theorem gramDet_combination (b₀ b₁ : E) (m n p q : ℝ) :
    gramDet (m • b₀ + n • b₁) (p • b₀ + q • b₁) = (m * q - n * p) ^ 2 * gramDet b₀ b₁ := by
  simp only [gramDet, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm b₀ b₁]
  ring

/-- **Shear invariance**: `gramDet x (y - k x) = gramDet x y`. -/
theorem gramDet_sub_smul (x y : E) (k : ℝ) : gramDet x (y - k • x) = gramDet x y := by
  simp only [gramDet, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm x y]
  ring

theorem gramDet_zero_right (x : E) : gramDet x 0 = 0 := by simp [gramDet]

/-- `gramDet b₀ b₁ = ‖b₀‖² ‖b₁ - t b₀‖²` for `t = ⟪b₀, b₁⟫ / ‖b₀‖²`. -/
theorem gramDet_eq_mul_norm_sq {b₀ : E} (h0 : b₀ ≠ 0) (b₁ : E) :
    gramDet b₀ b₁ = ‖b₀‖ ^ 2 * ‖b₁ - (⟪b₀, b₁⟫ / ‖b₀‖ ^ 2) • b₀‖ ^ 2 := by
  have hA : ‖b₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)
  rw [gramDet, ← real_inner_self_eq_norm_sq (b₁ - (⟪b₀, b₁⟫ / ‖b₀‖ ^ 2) • b₀)]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm b₀ b₁]
  field_simp
  ring

/-- The Gram determinant of two linearly independent vectors is positive. -/
theorem gramDet_pos_of_linearIndependent {b : Fin 2 → E} (hb : LinearIndependent ℝ b) :
    0 < gramDet (b 0) (b 1) := by
  have h0 : b 0 ≠ 0 := hb.ne_zero 0
  rw [gramDet_eq_mul_norm_sq h0]
  have hb' : LinearIndependent ℝ ![b 0, b 1] := by
    have : b = ![b 0, b 1] := by ext i; fin_cases i <;> rfl
    rwa [this] at hb
  have h1 : b 1 - (⟪b 0, b 1⟫ / ‖b 0‖ ^ 2) • b 0 ≠ 0 := by
    intro h
    have := LinearIndependent.pair_iff.mp hb' (-(⟪b 0, b 1⟫ / ‖b 0‖ ^ 2)) 1
    simp only [neg_smul, one_smul] at this
    have h' : -((⟪b 0, b 1⟫ / ‖b 0‖ ^ 2) • b 0) + b 1 = 0 := by rw [← h]; abel
    exact one_ne_zero (this h').2
  have := norm_pos_iff.mpr h0
  have := norm_pos_iff.mpr h1
  positivity

/-- **Successive minima in rank two.**  Let `b` be a basis of a two-dimensional real inner product
space and `L = ℤ b₀ + ℤ b₁`.  There are nonzero `v₁, v₂ ∈ L` with `gramDet v₁ v₂ = gramDet b₀ b₁`
and `3 ‖v₁‖² ‖v₂‖² ≤ 4 gramDet b₀ b₁`. -/
theorem exists_reduced_pair (b : Module.Basis (Fin 2) ℝ E) :
    ∃ v₁ ∈ span ℤ (Set.range b), ∃ v₂ ∈ span ℤ (Set.range b), v₁ ≠ 0 ∧ v₂ ≠ 0 ∧
      gramDet v₁ v₂ = gramDet (b 0) (b 1) ∧
        3 * (‖v₁‖ ^ 2 * ‖v₂‖ ^ 2) ≤ 4 * gramDet (b 0) (b 1) := by
  classical
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  set L := span ℤ (Set.range b) with hL
  have hmem : ∀ m n : ℤ, (m : ℝ) • b 0 + (n : ℝ) • b 1 ∈ L := by
    intro m n
    have h0 : b 0 ∈ L := subset_span ⟨0, rfl⟩
    have h1 : b 1 ∈ L := subset_span ⟨1, rfl⟩
    rw [← Int.cast_smul_eq_zsmul ℝ m (b 0), ← Int.cast_smul_eq_zsmul ℝ n (b 1)] at *
    exact L.add_mem (L.zsmul_mem h0 m) (L.zsmul_mem h1 n)
  have hcoord : ∀ v ∈ L, ∃ m n : ℤ, v = (m : ℝ) • b 0 + (n : ℝ) • b 1 := by
    intro v hv
    obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℤ).mp hv
    refine ⟨c 0, c 1, ?_⟩
    rw [← hc, Fin.sum_univ_two, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hne : ∃ v ∈ L, v ≠ (0 : E) := ⟨b 0, subset_span ⟨0, rfl⟩, b.ne_zero 0⟩
  obtain ⟨v₁, hv₁L, hv₁0, hmin⟩ := HTGeometry.exists_minimal_norm L hne
  obtain ⟨m, n, rfl⟩ := hcoord v₁ hv₁L
  -- a shortest vector is primitive
  have hcop : IsCoprime m n := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    set g := Int.gcd m n with hgdef
    have hg0 : g ≠ 0 := by
      intro h0
      rw [Int.gcd_eq_zero_iff] at h0
      apply hv₁0
      simp [h0.1, h0.2]
    have hg2 : (2 : ℝ) ≤ g := by
      have : 2 ≤ g := by omega
      exact_mod_cast this
    obtain ⟨m', hm'⟩ := Int.gcd_dvd_left m n
    obtain ⟨n', hn'⟩ := Int.gcd_dvd_right m n
    set w := (m' : ℝ) • b 0 + (n' : ℝ) • b 1 with hw
    have hvw : (m : ℝ) • b 0 + (n : ℝ) • b 1 = (g : ℝ) • w := by
      rw [hw, smul_add, smul_smul, smul_smul]
      congr 2 <;> [rw [hm']; rw [hn']] <;> push_cast <;> ring
    have hw0 : w ≠ 0 := by
      intro h; apply hv₁0; rw [hvw, h, smul_zero]
    have := hmin w (hmem m' n') hw0
    rw [hvw, norm_smul, Real.norm_natCast] at this
    have hwpos := norm_pos_iff.mpr hw0
    nlinarith
  -- extend to a unimodular basis `(v₁, u)`
  obtain ⟨s, t, hst⟩ := hcop
  set v₁ := (m : ℝ) • b 0 + (n : ℝ) • b 1 with hv₁
  set u := ((-t : ℤ) : ℝ) • b 0 + (s : ℝ) • b 1 with hu
  have hGu : gramDet v₁ u = gramDet (b 0) (b 1) := by
    rw [hv₁, hu, gramDet_combination]
    have : ((m : ℝ) * s - n * ((-t : ℤ) : ℝ)) = 1 := by
      push_cast
      have := congrArg (fun z : ℤ => (z : ℝ)) hst
      push_cast at this
      linarith
    rw [this]
    ring
  -- shear `u` by the nearest integer multiple of `v₁`
  have hv₁pos : 0 < ‖v₁‖ ^ 2 := by positivity [norm_pos_iff.mpr hv₁0]
  set k : ℤ := round (⟪v₁, u⟫ / ‖v₁‖ ^ 2) with hk
  set v₂ := u - (k : ℝ) • v₁ with hv₂
  have hv₂L : v₂ ∈ L := by
    rw [hv₂, ← Int.cast_smul_eq_zsmul ℝ k v₁ |>.symm.trans rfl]
    refine L.sub_mem (hmem _ _) ?_
    rw [Int.cast_smul_eq_zsmul]
    exact L.zsmul_mem hv₁L k
  have hGv : gramDet v₁ v₂ = gramDet (b 0) (b 1) := by rw [hv₂, gramDet_sub_smul, hGu]
  have hGpos : 0 < gramDet (b 0) (b 1) := gramDet_pos_of_linearIndependent b.linearIndependent
  have hv₂0 : v₂ ≠ 0 := by
    intro h
    rw [h, gramDet_zero_right] at hGv
    linarith
  have hinner : |⟪v₁, v₂⟫| ≤ ‖v₁‖ ^ 2 / 2 := by
    have hr := abs_sub_round (⟪v₁, u⟫ / ‖v₁‖ ^ 2)
    rw [← hk] at hr
    have he : ⟪v₁, v₂⟫ = ‖v₁‖ ^ 2 * (⟪v₁, u⟫ / ‖v₁‖ ^ 2 - k) := by
      rw [hv₂, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
      ring
    rw [he, abs_mul, abs_of_pos hv₁pos]
    nlinarith
  have hle : ‖v₁‖ ≤ ‖v₂‖ := hmin v₂ hv₂L hv₂0
  refine ⟨v₁, hv₁L, v₂, hv₂L, hv₁0, hv₂0, hGv, ?_⟩
  rw [← hGv, gramDet]
  have hsq : ⟪v₁, v₂⟫ ^ 2 ≤ (‖v₁‖ ^ 2 / 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hinner 2
  have hle2 : ‖v₁‖ ^ 2 ≤ ‖v₂‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  nlinarith

/-- **The logarithmic form** of the successive-minima bound:
`log ‖v₁‖ + log ‖v₂‖ ≤ (1/2) log G + log (2/√3)` with `G = gramDet b₀ b₁`. -/
theorem exists_reduced_pair_log (b : Module.Basis (Fin 2) ℝ E) :
    ∃ v₁ ∈ span ℤ (Set.range b), ∃ v₂ ∈ span ℤ (Set.range b), v₁ ≠ 0 ∧ v₂ ≠ 0 ∧
      gramDet v₁ v₂ = gramDet (b 0) (b 1) ∧
        Real.log ‖v₁‖ + Real.log ‖v₂‖ ≤
          Real.log (gramDet (b 0) (b 1)) / 2 + Real.log (2 / Real.sqrt 3) := by
  obtain ⟨v₁, h₁, v₂, h₂, h₁0, h₂0, hG, hbound⟩ := exists_reduced_pair b
  refine ⟨v₁, h₁, v₂, h₂, h₁0, h₂0, hG, ?_⟩
  have hp₁ := norm_pos_iff.mpr h₁0
  have hp₂ := norm_pos_iff.mpr h₂0
  have hGpos : 0 < gramDet (b 0) (b 1) := gramDet_pos_of_linearIndependent b.linearIndependent
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  -- `(‖v₁‖ ‖v₂‖)² ≤ (4/3) G = (2/√3)² G`
  have hsq : (‖v₁‖ * ‖v₂‖) ^ 2 ≤ ((2 / Real.sqrt 3) * Real.sqrt (gramDet (b 0) (b 1))) ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hGpos.le]
    linarith
  have hprod : ‖v₁‖ * ‖v₂‖ ≤ (2 / Real.sqrt 3) * Real.sqrt (gramDet (b 0) (b 1)) :=
    pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero |>.mp hsq
  have := Real.log_le_log (by positivity) hprod
  rw [Real.log_mul hp₁.ne' hp₂.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt hGpos.le] at this
  linarith

end GaloisForLFunctions.KodairaParshinAbc
