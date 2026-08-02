import GaloisForLFunctions.RHTower.SuzukiArchimedeanParityHankelInfiniteRank
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Infinite negative index of Suzuki's archimedean parity Hankel kernel

On the positive quadrant, the exact real profile has the signed Gram expansion

`h(x+y) = p(x)p(y) - ∑ₖ qₖ(x)qₖ(y)`,

where `p(x)=exp(x/2)` and `qₖ(x)=exp(-(5/2+2k)x)`.  The negative modes have
Vandermonde-independent finite moment packets.  Consequently every nonempty positive interval
contains finite Gram matrices with negative subspaces of arbitrarily large dimension, while every
strictly positive subspace has dimension at most one.

This sharpens the infinite-rank theorem to kernel signature `(≤ 1, ∞)` and rules out finite-index
Pontryagin or finite-negative-square transfers between Suzuki's literal parity blocks.
-/

namespace RHTower

open Complex Filter
open scoped Matrix

noncomputable section

def realArchHankelProfile (t : ℝ) : ℝ :=
  Real.exp (t / 2) -
    Real.exp (-5 * t / 2) / (1 - Real.exp (-2 * t))

def archPositiveMode (x : ℝ) : ℝ :=
  Real.exp (x / 2)

def archNegativeMode (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(5 / 2 + 2 * (k : ℝ)) * x)

theorem hasSum_archNegativeMode_product
    {x y : ℝ} (hxy : 0 < x + y) :
    HasSum (fun k : ℕ => archNegativeMode k x * archNegativeMode k y)
      (Real.exp (-5 * (x + y) / 2) /
        (1 - Real.exp (-2 * (x + y)))) := by
  let r : ℝ := Real.exp (-2 * (x + y))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp only [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (Real.exp (-5 * (x + y) / 2))
  have hterms :
      ∀ k : ℕ,
        archNegativeMode k x * archNegativeMode k y =
          Real.exp (-5 * (x + y) / 2) * r ^ k := by
    intro k
    simp only [archNegativeMode]
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hsum :
      HasSum (fun k : ℕ => archNegativeMode k x * archNegativeMode k y)
        (Real.exp (-5 * (x + y) / 2) * (1 - r)⁻¹) :=
    hgeom.congr_fun hterms
  simpa only [r, div_eq_mul_inv] using hsum

theorem realArchHankelProfile_eq_mode_tsum
    {x y : ℝ} (hxy : 0 < x + y) :
    realArchHankelProfile (x + y) =
      archPositiveMode x * archPositiveMode y -
        ∑' k : ℕ, archNegativeMode k x * archNegativeMode k y := by
  rw [(hasSum_archNegativeMode_product hxy).tsum_eq]
  unfold realArchHankelProfile archPositiveMode
  rw [← Real.exp_add]
  congr 2
  ring

theorem ofReal_realArchHankelProfile (t : ℝ) :
    (realArchHankelProfile t : ℂ) =
      archHankelProfile (t : ℂ) := by
  unfold realArchHankelProfile archHankelProfile
  rw [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_exp, Complex.ofReal_exp]
  norm_num

theorem archHankelKernel_eq_ofReal_realArchHankelProfile
    (x y : ℝ) :
    archHankelKernel x y =
      (realArchHankelProfile (x + y) : ℂ) := by
  rw [archHankelKernel, ofReal_realArchHankelProfile]

def archKernelGramQuadratic {n : ℕ}
    (x c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * realArchHankelProfile (x i + x j)

def archPositiveMoment {n : ℕ}
    (x c : Fin n → ℝ) : ℝ :=
  ∑ i, c i * archPositiveMode (x i)

def archNegativeMoment {n : ℕ}
    (k : ℕ) (x c : Fin n → ℝ) : ℝ :=
  ∑ i, c i * archNegativeMode k (x i)

theorem hasSum_archNegativeMoment_sq
    {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i)
    (c : Fin n → ℝ) :
    HasSum (fun k : ℕ => (archNegativeMoment k x c) ^ 2)
      (∑ i, ∑ j, c i * c j *
        (Real.exp (-5 * (x i + x j) / 2) /
          (1 - Real.exp (-2 * (x i + x j))))) := by
  have hij (i j : Fin n) :
      HasSum
        (fun k : ℕ =>
          c i * c j *
            (archNegativeMode k (x i) * archNegativeMode k (x j)))
        (c i * c j *
          (Real.exp (-5 * (x i + x j) / 2) /
            (1 - Real.exp (-2 * (x i + x j))))) :=
    (hasSum_archNegativeMode_product (add_pos (hx i) (hx j))).mul_left
      (c i * c j)
  have hsumJ (i : Fin n) :
      HasSum
        (fun k : ℕ => ∑ j,
          c i * c j *
            (archNegativeMode k (x i) * archNegativeMode k (x j)))
        (∑ j, c i * c j *
          (Real.exp (-5 * (x i + x j) / 2) /
            (1 - Real.exp (-2 * (x i + x j))))) := by
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      (hasSum_sum (s := Finset.univ) fun j _ => hij i j)
  have hsumIJ :
      HasSum
        (fun k : ℕ => ∑ i, ∑ j,
          c i * c j *
            (archNegativeMode k (x i) * archNegativeMode k (x j)))
        (∑ i, ∑ j, c i * c j *
          (Real.exp (-5 * (x i + x j) / 2) /
            (1 - Real.exp (-2 * (x i + x j))))) := by
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      (hasSum_sum (s := Finset.univ) fun i _ => hsumJ i)
  apply hsumIJ.congr_fun
  intro k
  rw [archNegativeMoment, sq]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem archKernelGramQuadratic_eq_moments
    {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i)
    (c : Fin n → ℝ) :
    archKernelGramQuadratic x c =
      (archPositiveMoment x c) ^ 2 -
        ∑' k : ℕ, (archNegativeMoment k x c) ^ 2 := by
  rw [(hasSum_archNegativeMoment_sq hx c).tsum_eq]
  unfold archKernelGramQuadratic archPositiveMoment
  simp_rw [realArchHankelProfile, mul_sub]
  simp only [Finset.sum_sub_distrib]
  congr 1
  · rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    unfold archPositiveMode
    rw [show Real.exp ((x i + x j) / 2) =
        Real.exp (x i / 2) * Real.exp (x j / 2) by
      rw [← Real.exp_add]
      congr 1
      ring]
    ring

theorem archKernelGramQuadratic_nonpos_of_positiveMoment_eq_zero
    {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i)
    {c : Fin n → ℝ} (hc : archPositiveMoment x c = 0) :
    archKernelGramQuadratic x c ≤ 0 := by
  rw [archKernelGramQuadratic_eq_moments hx c, hc]
  norm_num
  exact tsum_nonneg fun k => sq_nonneg _

theorem coeff_eq_zero_of_archNegativeMoment_zero
    {n : ℕ} {x c : Fin n → ℝ}
    (hx : Function.Injective x)
    (hzero : ∀ k : Fin n, archNegativeMoment (k : ℕ) x c = 0) :
    c = 0 := by
  let r : Fin n → ℝ := fun j => Real.exp (-2 * x j)
  let d : Fin n → ℝ := fun j => c j * Real.exp (-5 * x j / 2)
  have hr : Function.Injective r := by
    intro i j hij
    dsimp only [r] at hij
    have harg : -2 * x i = -2 * x j := Real.exp_injective hij
    apply hx
    linarith
  have hvec : d ᵥ* Matrix.vandermonde r = 0 := by
    funext k
    have hk := hzero k
    rw [archNegativeMoment] at hk
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply,
      Pi.zero_apply]
    rw [← hk]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [d, r]
    rw [archNegativeMode]
    rw [show Real.exp (-(5 / 2 + 2 * (k : ℝ)) * x j) =
        Real.exp (-5 * x j / 2) * (Real.exp (-2 * x j)) ^ (k : ℕ) by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring]
    ring
  have hd : d = 0 :=
    Matrix.eq_zero_of_vecMul_eq_zero
      (Matrix.det_vandermonde_ne_zero_iff.mpr hr) hvec
  funext j
  have hdj := congrFun hd j
  dsimp only [d] at hdj
  simp only [Pi.zero_apply] at hdj
  exact (mul_eq_zero.mp hdj).resolve_right (Real.exp_ne_zero _)

theorem exists_archNegativeMoment_ne_zero
    {n : ℕ} {x c : Fin n → ℝ}
    (hx : Function.Injective x) (hc : c ≠ 0) :
    ∃ k : Fin n, archNegativeMoment (k : ℕ) x c ≠ 0 := by
  by_contra h
  apply hc
  apply coeff_eq_zero_of_archNegativeMoment_zero hx
  intro k
  by_contra hk
  exact h ⟨k, hk⟩

def archPositiveMomentLinear {n : ℕ}
    (x : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := archPositiveMoment x
    map_add' := by
      intro c d
      simp only [archPositiveMoment, Pi.add_apply, add_mul,
        Finset.sum_add_distrib]
    map_smul' := by
      intro a c
      simp only [archPositiveMoment, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro i hi
      ring }

/-- The archimedean Hankel profile has at least `m` negative squares on `(0,b)` when a
finite Gram matrix admits an `m`-dimensional coefficient subspace on which its quadratic
form is strictly negative. -/
def ArchHankelHasAtLeastNegativeSquaresOn
    (m : ℕ) (b : ℝ) : Prop :=
  ∃ (n : ℕ) (x : Fin n → ℝ)
      (W : Submodule ℝ (Fin n → ℝ)),
    (∀ i, 0 < x i ∧ x i < b) ∧
    m ≤ Module.finrank ℝ W ∧
    ∀ c, c ∈ W → c ≠ 0 →
      archKernelGramQuadratic x c < 0

theorem realArchHankelProfile_hasAtLeastNegativeSquaresOn
    (m : ℕ) {b : ℝ} (hb : 0 < b) :
    ArchHankelHasAtLeastNegativeSquaresOn m b := by
  let n : ℕ := m + 1
  let x : Fin n → ℝ := fun j =>
    b * (((j : ℕ) : ℝ) + 1) / (m + 2)
  have hxPos : ∀ j, 0 < x j := by
    intro j
    dsimp only [x]
    positivity
  have hxLt : ∀ j, x j < b := by
    intro j
    have hj : (j : ℕ) + 1 < m + 2 := by
      dsimp only [n] at j
      omega
    dsimp only [x]
    change b * (((j : ℕ) : ℝ) + 1) /
        (((m : ℕ) : ℝ) + 2) < b
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 2)]
    have hjReal :
        (((j : ℕ) : ℝ) + 1) < (m + 2 : ℕ) := by
      exact_mod_cast hj
    norm_num at hjReal ⊢
    exact mul_lt_mul_of_pos_left hjReal hb
  have hxInj : Function.Injective x := by
    intro i j hij
    apply Fin.ext
    have hden : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hb0 : b ≠ 0 := hb.ne'
    dsimp only [x] at hij
    field_simp [hden] at hij
    have hcast : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
      nlinarith
    exact_mod_cast hcast
  let P : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    archPositiveMomentLinear x
  let W : Submodule ℝ (Fin n → ℝ) := LinearMap.ker P
  refine ⟨n, x, W, fun i => ⟨hxPos i, hxLt i⟩, ?_, ?_⟩
  · have hrange :
        Module.finrank ℝ (LinearMap.range P) ≤ 1 := by
      simpa using (LinearMap.range P).finrank_le
    have hdim := P.finrank_range_add_finrank_ker
    have hdomain :
        Module.finrank ℝ (Fin n → ℝ) = m + 1 := by
      simp [n]
    rw [hdomain] at hdim
    dsimp only [W]
    omega
  · intro c hcW hcNe
    have hcPos : archPositiveMoment x c = 0 := by
      have hcKer : c ∈ LinearMap.ker P := hcW
      have hPc : P c = 0 := LinearMap.mem_ker.mp hcKer
      exact hPc
    obtain ⟨k, hk⟩ :=
      exists_archNegativeMoment_ne_zero hxInj hcNe
    have hsum := hasSum_archNegativeMoment_sq hxPos c
    have hle :
        (archNegativeMoment (k : ℕ) x c) ^ 2 ≤
          ∑' l : ℕ, (archNegativeMoment l x c) ^ 2 :=
      hsum.summable.le_tsum (k : ℕ) (fun l hl => sq_nonneg _)
    have hsumPos :
        0 < ∑' l : ℕ, (archNegativeMoment l x c) ^ 2 :=
      lt_of_lt_of_le (sq_pos_of_ne_zero hk) hle
    rw [archKernelGramQuadratic_eq_moments hxPos c, hcPos]
    norm_num
    exact hsumPos

/-- Every strictly positive coefficient subspace for a positive-node Gram matrix of the
archimedean Hankel profile has dimension at most one. -/
theorem archHankel_positive_subspace_finrank_le_one
    {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i)
    {W : Submodule ℝ (Fin n → ℝ)}
    (hW : ∀ c, c ∈ W → c ≠ 0 →
      0 < archKernelGramQuadratic x c) :
    Module.finrank ℝ W ≤ 1 := by
  let P : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    archPositiveMomentLinear x
  have hinj : Function.Injective (P.domRestrict W) := by
    intro c d hcd
    apply Subtype.ext
    by_contra hne
    have hmem : c.1 - d.1 ∈ W := W.sub_mem c.2 d.2
    have hvne : c.1 - d.1 ≠ 0 := sub_ne_zero.mpr hne
    have hpos : 0 < archKernelGramQuadratic x (c.1 - d.1) :=
      hW (c.1 - d.1) hmem hvne
    have hmoment : archPositiveMoment x (c.1 - d.1) = 0 := by
      have hsub : P (c.1 - d.1) = 0 := by
        change P c.1 = P d.1 at hcd
        rw [map_sub, sub_eq_zero]
        exact hcd
      exact hsub
    have hnonpos :=
      archKernelGramQuadratic_nonpos_of_positiveMoment_eq_zero
        hx hmoment
    linarith
  simpa using (P.domRestrict W).finrank_le_finrank_of_injective hinj

end

end RHTower
