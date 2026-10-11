import GaloisForLFunctions.RHTower.JointAncestryClusterTwoSided
import GaloisForLFunctions.RHTower.JointAncestryClusterOrdinates

/-!
# Rescuing clusters: aligned or large

A cluster `(u_j, ψ_j)` of unimodular prime-phase patterns can cancel the negative JAS test of its
members only if its untwisted average is exponentially small relative to its coherent value
(`jasCluster_re_le`, `jasClusterTwoSided_re_le`).  The untwisted average is a Gram form whose
diagonal entries all equal the coherent factor `G = Π_p (1 − b_p)⁻¹`.  If every off-diagonal entry
has modulus at most `ε G` (pairwise non-alignment), the Gram form is at least
`G ((1 + ε) Σ u_j² − ε (Σ|u_j|)²)` (`re_sum_sum_ge_of_offdiag_le`).  Hence a rescuing cluster
satisfies (`jasCluster_sum_sq_le_of_nonaligned`)

`Σ_j u_j² ≤ (ε + 6 e^{−S/60}) (Σ_j |u_j|)²`,

i.e. its effective size `(Σ|u_j|)² / Σ u_j²` is at least `1/(ε + 6e^{−S/60})`.  The same holds
for the full two-sided kernel of a cluster with a common real part, with `10` in place of `6`
(`jasClusterTwoSided_sum_sq_le_of_nonaligned`).

For zeros the pattern of a member at height `γ_j` is `p ↦ p^{iγ_j}`, and the off-diagonal entry
of the pair `(j, k)` is the partial Euler product `Π_p (1 − p^{i(γ_j − γ_k)} p^{−σ})⁻¹` at the height
difference (`jasCluster_sum_sq_le_of_nonaligned_ordinates`).  So a cluster of zeros rescues its
own test only if some height difference makes this product nearly as large as `Π_p (1 − p^{−σ})⁻¹`
(Bohr alignment on the test primes), or the cluster has many members of comparable weight.
-/

open Complex

namespace RHTower

open scoped ComplexConjugate

noncomputable section

/-- **Gram lower bound under off-diagonal smallness.** -/
theorem re_sum_sum_ge_of_offdiag_le {ι : Type*} [DecidableEq ι] (t : Finset ι) (u : ι → ℝ)
    (T : ι → ι → ℂ) {G ε : ℝ} (hdiag : ∀ j ∈ t, T j j = G)
    (hoff : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → ‖T j k‖ ≤ ε * G) :
    G * ((1 + ε) * ∑ j ∈ t, u j ^ 2 - ε * (∑ j ∈ t, |u j|) ^ 2) ≤
      (∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k * T j k).re := by
  have hre : (∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k * T j k).re =
      ∑ j ∈ t, ∑ k ∈ t, u j * u k * (T j k).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
  rw [hre]
  have hrow : ∀ j ∈ t, u j ^ 2 * G * (1 + ε) - ε * G * |u j| * ∑ k ∈ t, |u k| ≤
      ∑ k ∈ t, u j * u k * (T j k).re := by
    intro j hj
    rw [← Finset.add_sum_erase t _ hj, hdiag j hj, Complex.ofReal_re,
      ← Finset.add_sum_erase t (fun k => |u k|) hj]
    have hrest : -(ε * G * |u j| * ∑ k ∈ t.erase j, |u k|) ≤
        ∑ k ∈ t.erase j, u j * u k * (T j k).re := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun k hk => ?_
      have hkj : k ≠ j := Finset.ne_of_mem_erase hk
      have hT := hoff j hj k (Finset.mem_of_mem_erase hk) (Ne.symm hkj)
      have h1 : |(T j k).re| ≤ ε * G := (Complex.abs_re_le_norm _).trans hT
      have h2 : |u j * u k * (T j k).re| ≤ |u j| * |u k| * (ε * G) := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have := neg_abs_le (u j * u k * (T j k).re)
      nlinarith
    have hsq : u j * u j = u j ^ 2 := by ring
    have hab : |u j| * |u j| = u j ^ 2 := by rw [← abs_mul, abs_mul_self]; ring
    nlinarith [hrest]
  calc G * ((1 + ε) * ∑ j ∈ t, u j ^ 2 - ε * (∑ j ∈ t, |u j|) ^ 2)
      = ∑ j ∈ t, (u j ^ 2 * G * (1 + ε) - ε * G * |u j| * ∑ k ∈ t, |u k|) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
          ← Finset.sum_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum hrow

theorem prod_inv_one_sub_rpow_pos {P : Finset Nat.Primes} {σ : ℝ}
    (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100) :
    0 < ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ :=
  Finset.prod_pos fun i _ => inv_pos.mpr (by linarith [hb i])

theorem prod_inv_one_sub_unimodular {P : Finset Nat.Primes} {ψ : ↥P → ℂ}
    (hψ : ∀ i, ‖ψ i‖ = 1) (σ : ℝ) :
    ∏ i : ↥P, (1 - ψ i * conj (ψ i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ =
      ((∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ : ℝ) : ℂ) := by
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ i, rpow_natCast_neg_ofReal]
  push_cast
  ring

/-- **A rescuing cluster of pairwise non-aligned patterns is large.** -/
theorem jasCluster_sum_sq_le_of_nonaligned {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (u : ι → ℝ) (P : Finset Nat.Primes) {ψ : ι → ↥P → ℂ} (hψ : ∀ j i, ‖ψ j i‖ = 1) {σ : ℝ}
    (hσ : 0 < σ) (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100)
    (hS : 0 < ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) {ε : ℝ} (hε : 0 ≤ ε)
    (halign : ∀ j ∈ t, ∀ k ∈ t, j ≠ k →
      ‖∏ i : ↥P, (1 - ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤
        ε * ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹)
    (hres : 0 ≤ (∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k * ∏ i : ↥P,
        (1 - Complex.exp (((Real.pi / ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.I) * ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹).re) :
    ∑ j ∈ t, u j ^ 2 ≤
      (ε + 6 * Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60))) *
        (∑ j ∈ t, |u j|) ^ 2 := by
  have h1 := jasCluster_re_le t u P (fun j i => (hψ j i).le) hσ hb hS
  have hG := prod_inv_one_sub_rpow_pos hb
  have hlow := re_sum_sum_ge_of_offdiag_le t u
    (fun j k => ∏ i : ↥P, (1 - ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)
    (G := ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) (ε := ε)
    (fun j _ => prod_inv_one_sub_unimodular (hψ j) σ) halign
  have hE := (Real.exp_pos (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60))).le
  have hsq : 0 ≤ ∑ j ∈ t, u j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hU : 0 ≤ (∑ j ∈ t, |u j|) ^ 2 := sq_nonneg _
  have key : (1 + ε) * ∑ j ∈ t, u j ^ 2 - ε * (∑ j ∈ t, |u j|) ^ 2 ≤
      6 * (∑ j ∈ t, |u j|) ^ 2 *
        Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60)) := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_left hcon hG
    nlinarith
  nlinarith

/-- **Two-sided version** for clusters with a common real part. -/
theorem jasClusterTwoSided_sum_sq_le_of_nonaligned {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (u : ι → ℝ) (P : Finset Nat.Primes) {ψ : ι → ↥P → ℂ} (hψ : ∀ j i, ‖ψ j i‖ = 1) {a σ : ℝ}
    (ha : 0 < a) (hσ : 0 < σ)
    (hα : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a) ≤ 1 / 100)
    (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100)
    (hS : 0 < ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))
    (hαS : ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a) ≤
      (∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 100) {ε : ℝ} (hε : 0 ≤ ε)
    (halign : ∀ j ∈ t, ∀ k ∈ t, j ≠ k →
      ‖(∏ i : ↥P, (1 - ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(a : ℂ)))⁻¹) *
          ∏ i : ↥P, (1 - conj (ψ j i) * ψ k i * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤
        ε * ((∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹) *
          ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹))
    (hres : 0 ≤ (jasTwoSidedCluster t u P ψ
        (fun _ => Complex.exp (((Real.pi / ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.I)) a σ).re) :
    ∑ j ∈ t, u j ^ 2 ≤
      (ε + 10 * Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60))) *
        (∑ j ∈ t, |u j|) ^ 2 := by
  have h1 := jasClusterTwoSided_re_le t u P (fun j i => (hψ j i).le) ha hσ hα hb hS hαS
  have hGa := prod_inv_one_sub_rpow_pos hα
  have hGb := prod_inv_one_sub_rpow_pos hb
  have hG := mul_pos hGa hGb
  have hψc : ∀ j, ∀ i, ‖conj (ψ j i)‖ = 1 := fun j i => by rw [Complex.norm_conj]; exact hψ j i
  have hdiag : ∀ j ∈ t,
      (∏ i : ↥P, (1 - ψ j i * conj (ψ j i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(a : ℂ)))⁻¹) *
        ∏ i : ↥P, (1 - conj (ψ j i) * ψ j i * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ =
      (((∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹) *
        ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ : ℝ) : ℂ) := fun j _ => by
    have h2 := prod_inv_one_sub_unimodular (hψc j) σ
    simp only [Complex.conj_conj] at h2
    rw [prod_inv_one_sub_unimodular (hψ j) a, Complex.ofReal_mul,
      show (fun i : ↥P => conj (ψ j i) * ψ j i) = fun i => ψ j i * conj (ψ j i) from
        funext fun i => mul_comm _ _]
    rw [← h2]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (conj (ψ j i))]
  have hlow := re_sum_sum_ge_of_offdiag_le t u
    (fun j k => (∏ i : ↥P, (1 - ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(a : ℂ)))⁻¹) *
      ∏ i : ↥P, (1 - conj (ψ j i) * ψ k i * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)
    (G := (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹) *
      ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) (ε := ε) hdiag halign
  have hone : jasTwoSidedCluster t u P ψ (fun _ => 1) a σ =
      ∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k *
        ((∏ i : ↥P, (1 - ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(a : ℂ)))⁻¹) *
          ∏ i : ↥P, (1 - conj (ψ j i) * ψ k i * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹) := by
    simp only [jasTwoSidedCluster, one_mul, map_one]
  rw [hone] at h1
  have hE := (Real.exp_pos (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60))).le
  have hsq : 0 ≤ ∑ j ∈ t, u j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hU : 0 ≤ (∑ j ∈ t, |u j|) ^ 2 := sq_nonneg _
  have key : (1 + ε) * ∑ j ∈ t, u j ^ 2 - ε * (∑ j ∈ t, |u j|) ^ 2 ≤
      10 * (∑ j ∈ t, |u j|) ^ 2 *
        Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60)) := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_left hcon hG
    nlinarith
  nlinarith

/-- **Ordinate form.**  For members at heights `γ_j` (patterns `p ↦ p^{iγ_j}`) the alignment of a
pair is the partial Euler product at the height difference. -/
theorem jasCluster_sum_sq_le_of_nonaligned_ordinates {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (u : ι → ℝ) (P : Finset Nat.Primes) (γ : ι → ℝ) {σ : ℝ}
    (hσ : 0 < σ) (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100)
    (hS : 0 < ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) {ε : ℝ} (hε : 0 ≤ ε)
    (halign : ∀ j ∈ t, ∀ k ∈ t, j ≠ k →
      ‖∏ i : ↥P, (1 - jasHeightPattern P (γ j - γ k) i *
          (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤
        ε * ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹)
    (hres : 0 ≤ (∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k * ∏ i : ↥P,
        (1 - Complex.exp (((Real.pi / ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.I) * jasHeightPattern P (γ j) i * conj (jasHeightPattern P (γ k) i) *
            (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹).re) :
    ∑ j ∈ t, u j ^ 2 ≤
      (ε + 6 * Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60))) *
        (∑ j ∈ t, |u j|) ^ 2 := by
  refine jasCluster_sum_sq_le_of_nonaligned t u P (ψ := fun j => jasHeightPattern P (γ j))
    (fun j i => norm_jasHeightPattern P _ i) hσ hb hS hε (fun j hj k hk hjk => ?_) hres
  have h := halign j hj k hk hjk
  simp only [jasHeightPattern_mul_conj]
  exact h

end

end RHTower
