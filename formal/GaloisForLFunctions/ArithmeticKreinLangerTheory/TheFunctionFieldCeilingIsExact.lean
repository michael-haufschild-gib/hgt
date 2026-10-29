import GaloisForLFunctions.RHTower.WeilKloostermanLFunction

/-!
# The function-field ceiling is exact

Over `ℤ` the atomic kernel `D·1 − P_N` on `1, …, N` (HKT `TheMarginIsTheWidthOfTheIndexOneWindow`)
has no negative square once `D ≥ log N − γ + ε`, eventually in `N`: the pole vector `n^{−1/2}` is an
approximate eigenvector of the prime kernel, with eigenvalue `Σ_{k ≤ N/m} Λ(k)/k + Σ_{k ∣ m} Λ(k) =
log N − γ + o(1)` by Mertens. This module computes the same rung over `𝔽_q[T]`, where it is exact.

**The prime polynomial theorem** (`powerSumW_one_eq`). With weight `1` the Newton identity on monic
polynomials reads `m q^m = Σ_{j ≤ m} c_j q^{m−j}`, so `c_j = Σ_{d ∣ j} d·#{P irreducible, deg P = d}
= q^j`: Mertens' sum is exact, `Σ_{1 ≤ deg h ≤ M} Λ(h)/|h| = M log q` (`sum_primePower_weight_eq`).

**The pole vector is an exact eigenvector** (`primeKernelFq_poleVec`). On monic polynomials of degree
`≤ N`, with `P_N(f, g) = Λ(g/f) |g/f|^{−1/2}` symmetrized, `P_N |·|^{−1/2} = N log q · |·|^{−1/2}`:
the forward prime powers contribute `(N − deg m) log q` and the divisors of `m` contribute
`deg m · log q`. (Here `Λ` and the eigenvalue are written in units of `log q`.)

**The exact ceiling** (`atomFq_nonneg_iff`). A nonnegative symmetric kernel with a positive
eigenvector has that eigenvalue as the top of its quadratic form (`sum_mul_le_of_pos_eigenvector`,
Schur's test). So `D·1 − P_N ≥ 0` iff `D ≥ N log q`: the Robin–Euler ceiling over `𝔽_q` is `N log q`
with no error term. Over `ℤ` the ceiling is `log N − γ`; Euler's constant is the archimedean defect of
Mertens' theorem.
-/

open Polynomial Finset
open GaloisForLFunctions.RHTower.WeilKloosterman

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

attribute [local instance] Classical.propDecidable

/-! ### Schur's test with a positive eigenvector -/

/-- **Schur's test.** For a symmetric kernel `P ≥ 0` on a finite set with a positive eigenvector
`P v = μ v`, the quadratic form of `P` is at most `μ |x|²`. -/
theorem sum_mul_le_of_pos_eigenvector {ι : Type*} (s : Finset ι) (P : ι → ι → ℝ)
    (hsym : ∀ i j, P i j = P j i) (hnn : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ P i j) {v : ι → ℝ}
    (hv : ∀ i ∈ s, 0 < v i) {μ : ℝ} (heig : ∀ i ∈ s, ∑ j ∈ s, P i j * v j = μ * v i)
    (x : ι → ℝ) : ∑ i ∈ s, ∑ j ∈ s, P i j * x i * x j ≤ μ * ∑ i ∈ s, x i ^ 2 := by
  -- `2 x_i x_j ≤ (v_j / v_i) x_i² + (v_i / v_j) x_j²`
  have hpt : ∀ i ∈ s, ∀ j ∈ s, P i j * x i * x j ≤
      (P i j * (v j / v i) * x i ^ 2 + P i j * (v i / v j) * x j ^ 2) / 2 := by
    intro i hi j hj
    have hvi := hv i hi
    have hvj := hv j hj
    have key : 2 * x i * x j ≤ v j / v i * x i ^ 2 + v i / v j * x j ^ 2 := by
      have h := sq_nonneg (v j * x i - v i * x j)
      have e : v j / v i * x i ^ 2 + v i / v j * x j ^ 2 =
          ((v j * x i) ^ 2 + (v i * x j) ^ 2) / (v i * v j) := by
        field_simp
      rw [e, le_div_iff₀ (mul_pos hvi hvj)]
      nlinarith [h]
    nlinarith [mul_le_mul_of_nonneg_left key (hnn i hi j hj)]
  have hswap : ∑ i ∈ s, ∑ j ∈ s, P i j * (v i / v j) * x j ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, P i j * (v j / v i) * x i ^ 2 := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hsym]
  calc ∑ i ∈ s, ∑ j ∈ s, P i j * x i * x j
      ≤ ∑ i ∈ s, ∑ j ∈ s, (P i j * (v j / v i) * x i ^ 2 + P i j * (v i / v j) * x j ^ 2) / 2 :=
        sum_le_sum fun i hi => sum_le_sum fun j hj => hpt i hi j hj
    _ = ∑ i ∈ s, ∑ j ∈ s, P i j * (v j / v i) * x i ^ 2 := by
        simp only [add_div, sum_add_distrib, ← sum_div, hswap]
        ring
    _ = ∑ i ∈ s, μ * x i ^ 2 := sum_congr rfl fun i hi => by
        have hvi := hv i hi
        calc ∑ j ∈ s, P i j * (v j / v i) * x i ^ 2
            = (∑ j ∈ s, P i j * v j) * (x i ^ 2 / v i) := by
              rw [sum_mul]
              exact sum_congr rfl fun j _ => by field_simp
          _ = μ * x i ^ 2 := by rw [heig i hi]; field_simp
    _ = μ * ∑ i ∈ s, x i ^ 2 := (mul_sum _ _ _).symm

/-- **The exact ceiling of an atomic kernel.** If `P ≥ 0` is symmetric with a positive eigenvector
`P v = μ v` on a nonempty finite set, then `D·1 − P` is positive semidefinite iff `μ ≤ D`. -/
theorem atom_nonneg_iff {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (P : ι → ι → ℝ)
    (hsym : ∀ i j, P i j = P j i) (hnn : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ P i j) {v : ι → ℝ}
    (hv : ∀ i ∈ s, 0 < v i) {μ : ℝ} (heig : ∀ i ∈ s, ∑ j ∈ s, P i j * v j = μ * v i) (D : ℝ) :
    (∀ x : ι → ℝ, 0 ≤ D * ∑ i ∈ s, x i ^ 2 - ∑ i ∈ s, ∑ j ∈ s, P i j * x i * x j) ↔ μ ≤ D := by
  constructor
  · intro h
    have hv2 : 0 < ∑ i ∈ s, v i ^ 2 := sum_pos (fun i hi => pow_pos (hv i hi) 2) hs
    have hq : ∑ i ∈ s, ∑ j ∈ s, P i j * v i * v j = μ * ∑ i ∈ s, v i ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      calc ∑ j ∈ s, P i j * v i * v j = v i * ∑ j ∈ s, P i j * v j := by
            rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
        _ = μ * v i ^ 2 := by rw [heig i hi]; ring
    have := h v
    rw [hq] at this
    by_contra hlt
    push Not at hlt
    nlinarith
  · intro hμ x
    have := sum_mul_le_of_pos_eigenvector s P hsym hnn hv heig x
    nlinarith [sum_nonneg fun i (_ : i ∈ s) => sq_nonneg (x i)]

/-! ### The prime polynomial theorem -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem degSumW_one (m : ℕ) : degSumW (F := F) (fun _ => (1 : ℂ)) m = (Fintype.card F : ℂ) ^ m := by
  rw [degSumW, sum_const, card_monicDeg, nsmul_eq_mul, mul_one]
  push_cast; rfl

/-- **The prime polynomial theorem.** `Σ_{d ∣ j} d · #{P monic irreducible of degree d} = q^j`. -/
theorem powerSumW_one_eq {j : ℕ} (hj : 1 ≤ j) :
    powerSumW (F := F) (fun _ => (1 : ℂ)) j = (Fintype.card F : ℂ) ^ j := by
  induction j using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hN := newton_identity (F := F) (fun _ => (1 : ℂ)) (fun _ _ _ _ => (mul_one 1).symm) rfl
      (n + 1)
    rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, degSumW_one, degSumW_one, pow_zero,
      mul_one] at hN
    have hlow : ∑ k ∈ Icc 1 n, powerSumW (F := F) (fun _ => (1 : ℂ)) k *
        degSumW (F := F) (fun _ => (1 : ℂ)) (n + 1 - k) = n * (Fintype.card F : ℂ) ^ (n + 1) := by
      have hterm : ∀ k ∈ Icc 1 n, powerSumW (F := F) (fun _ => (1 : ℂ)) k *
          degSumW (F := F) (fun _ => (1 : ℂ)) (n + 1 - k) = (Fintype.card F : ℂ) ^ (n + 1) := by
        intro k hk
        obtain ⟨hk1, hkn⟩ := mem_Icc.mp hk
        rw [ih k (by omega) hk1, degSumW_one, ← pow_add]
        congr 1
        omega
      rw [sum_congr rfl hterm, sum_const, Nat.card_Icc, nsmul_eq_mul]
      congr 1
    rw [hlow] at hN
    push_cast at hN
    linear_combination -hN

/-- **Mertens' sum over `𝔽_q[T]` is exact.** `Σ_{d, P, k : k·d ≤ M} d · q^{−kd} = M`, i.e.
`Σ_{1 ≤ deg h ≤ M} Λ(h)/|h| = M log q`. -/
theorem sum_primePower_weight_eq {N M : ℕ} (hM : M ≤ N) :
    ∑ d ∈ Icc 1 N, ∑ _P ∈ irrDeg (F := F) d, ∑ k ∈ Icc 1 N,
      (if k * d ≤ M then (d : ℝ) * ((Fintype.card F : ℝ)⁻¹) ^ (k * d) else 0) = M := by
  set Q : ℝ := (Fintype.card F : ℝ)⁻¹ with hQ
  set g : ℕ → ℕ → ℝ := fun d k => ((irrDeg (F := F) d).card * d : ℝ) * Q ^ (k * d) with hg
  -- the summand does not depend on `P`
  have h1 : ∀ d ∈ Icc 1 N, ∑ _P ∈ irrDeg (F := F) d, ∑ k ∈ Icc 1 N,
      (if k * d ≤ M then (d : ℝ) * Q ^ (k * d) else 0) =
      ∑ k ∈ Icc 1 N, (if k * d ≤ M then g d k else 0) := by
    intro d _
    rw [sum_const, nsmul_eq_mul, mul_sum]
    exact sum_congr rfl fun k _ => by split_ifs <;> simp [hg]; ring
  rw [sum_congr rfl h1]
  -- shrink both ranges to `[1, M]`
  have hshrink : ∑ d ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (if k * d ≤ M then g d k else 0) =
      ∑ d ∈ Icc 1 M, ∑ k ∈ Icc 1 M, (if k * d ≤ M then g d k else 0) := by
    symm
    rw [sum_subset (Icc_subset_Icc_right hM)]
    · refine sum_congr rfl fun d hd => ?_
      refine sum_subset (Icc_subset_Icc_right hM) fun k hk hkM => if_neg fun hkd => ?_
      have := (mem_Icc.mp hd).1
      exact hkM (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, by nlinarith⟩)
    · intro d hd hdM
      refine sum_eq_zero fun k hk => if_neg fun hkd => hdM (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, ?_⟩)
      have := (mem_Icc.mp hk).1
      nlinarith
  rw [hshrink]
  -- reindex by `j = k·d` and use the prime polynomial theorem
  have hq0 : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hj : ∀ j ∈ Icc 1 M, ∑ d ∈ j.divisors, ((g d (j / d) : ℝ) : ℂ) = 1 := by
    intro j hj
    have hsum : ∑ d ∈ j.divisors, ((g d (j / d) : ℝ) : ℂ) =
        (Q : ℂ) ^ j * powerSumW (F := F) (fun _ => (1 : ℂ)) j := by
      rw [powerSumW, mul_sum]
      refine sum_congr rfl fun d hd => ?_
      simp only [hg, one_pow, mul_one, sum_const, nsmul_eq_mul]
      rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
      push_cast
      ring
    rw [hsum, powerSumW_one_eq (mem_Icc.mp hj).1, hQ, Complex.ofReal_inv, Complex.ofReal_natCast,
      ← mul_pow, inv_mul_cancel₀ hq0, one_pow]
  have hC := sum_pairs_eq_sum_divisors M (fun d k => ((g d k : ℝ) : ℂ))
  rw [sum_congr rfl hj, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at hC
  have : ((∑ d ∈ Icc 1 M, ∑ k ∈ Icc 1 M, (if k * d ≤ M then g d k else 0) : ℝ) : ℂ) = M := by
    rw [← hC]
    push_cast
    refine sum_congr rfl fun d _ => sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  exact_mod_cast this

/-! ### The prime kernel of `𝔽_q[T]` and its pole vector -/

/-- Monic polynomials of degree at most `N`. -/
def monicLE (N : ℕ) : Finset F[X] := (range (N + 1)).biUnion monicDeg

theorem mem_monicLE {N : ℕ} {f : F[X]} : f ∈ monicLE N ↔ f.Monic ∧ f.natDegree ≤ N := by
  simp only [monicLE, mem_biUnion, mem_range, mem_monicDeg]
  constructor
  · rintro ⟨d, hd, hm, rfl⟩
    exact ⟨hm, by omega⟩
  · rintro ⟨hm, hd⟩
    exact ⟨_, by omega, hm, rfl⟩

/-- The pole vector `|f|^{−1/2} = q^{−deg f / 2}`. -/
def poleVec (f : F[X]) : ℝ := (Real.sqrt (Fintype.card F))⁻¹ ^ f.natDegree

omit [DecidableEq F] in
theorem poleVec_pos (f : F[X]) : 0 < poleVec f :=
  pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos))) _

/-- Weil's prime kernel on monic polynomials, in units of `log q`:
`P_N(f, g) = Σ_{P irreducible, k ≥ 1} deg P · |P|^{−k/2} ([g = f P^k] + [f = g P^k])`. -/
def primeKernelFq (N : ℕ) (f g : F[X]) : ℝ :=
  ∑ d ∈ Icc 1 N, ∑ P ∈ irrDeg (F := F) d, ∑ k ∈ Icc 1 N,
    (d : ℝ) * (Real.sqrt (Fintype.card F))⁻¹ ^ (k * d) *
      ((if g = f * P ^ k then 1 else 0) + (if f = g * P ^ k then 1 else 0))

theorem primeKernelFq_symm (N : ℕ) (f g : F[X]) : primeKernelFq N f g = primeKernelFq N g f := by
  unfold primeKernelFq
  exact sum_congr rfl fun d _ => sum_congr rfl fun P _ => sum_congr rfl fun k _ => by
    rw [add_comm (ite (g = f * P ^ k) _ _)]

theorem primeKernelFq_nonneg (N : ℕ) (f g : F[X]) : 0 ≤ primeKernelFq N f g :=
  sum_nonneg fun d _ => sum_nonneg fun P _ => sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _))
      (add_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num))

/-- **The pole vector is an exact eigenvector.** `P_N |·|^{−1/2} = N · |·|^{−1/2}` on monic
polynomials of degree `≤ N`: forward prime powers give `N − deg m`, divisors of `m` give `deg m`. -/
theorem primeKernelFq_poleVec {N : ℕ} {m : F[X]} (hm : m ∈ monicLE N) :
    ∑ n ∈ monicLE N, primeKernelFq N m n * poleVec n = N * poleVec m := by
  obtain ⟨hmon, hmN⟩ := mem_monicLE.mp hm
  set r : ℝ := (Real.sqrt (Fintype.card F))⁻¹ with hr
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hr2 : r ^ 2 = (Fintype.card F : ℝ)⁻¹ := by rw [hr, inv_pow, Real.sq_sqrt hq.le]
  -- expand the kernel and move the sum over `n` inside
  have hexp : ∑ n ∈ monicLE N, primeKernelFq N m n * poleVec n =
      ∑ d ∈ Icc 1 N, ∑ P ∈ irrDeg (F := F) d, ∑ k ∈ Icc 1 N, (d : ℝ) * r ^ (k * d) *
        (∑ n ∈ monicLE N, (if n = m * P ^ k then poleVec n else 0) +
          ∑ n ∈ monicLE N, (if m = n * P ^ k then poleVec n else 0)) := by
    simp only [primeKernelFq, sum_mul]
    rw [sum_comm]; refine sum_congr rfl fun d _ => ?_
    rw [sum_comm]; refine sum_congr rfl fun P _ => ?_
    rw [sum_comm]; refine sum_congr rfl fun k _ => ?_
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  -- forward prime powers: `n = m P^k`
  have hfwd : ∀ d, ∀ P ∈ irrDeg (F := F) d, ∀ k : ℕ,
      ∑ n ∈ monicLE N, (if n = m * P ^ k then poleVec n else 0) =
        if m.natDegree + k * d ≤ N then r ^ (m.natDegree + k * d) else 0 := by
    intro d P hP k
    obtain ⟨hPm, hPd, -⟩ := mem_irrDeg.mp hP
    have hdeg : (m * P ^ k).natDegree = m.natDegree + k * d := by
      rw [hmon.natDegree_mul (hPm.pow k), hPm.natDegree_pow, hPd]
    rw [sum_ite_eq']
    simp only [mem_monicLE, hmon.mul (hPm.pow k), true_and, hdeg, poleVec, hr]
  -- divisors of `m`: `m = n P^k`
  have hbwd : ∀ d, ∀ P ∈ irrDeg (F := F) d, ∀ k : ℕ,
      ∑ n ∈ monicLE N, (if m = n * P ^ k then poleVec n else 0) =
        if P ^ k ∣ m then r ^ (m.natDegree - k * d) else 0 := by
    intro d P hP k
    obtain ⟨hPm, hPd, -⟩ := mem_irrDeg.mp hP
    have hPk : (P ^ k).Monic := hPm.pow k
    by_cases hdvd : P ^ k ∣ m
    · obtain ⟨g, hg⟩ := hdvd
      have hgm : g.Monic := hPk.of_mul_monic_left (hg ▸ hmon)
      have hdeg : m.natDegree = k * d + g.natDegree := by
        rw [hg, hPk.natDegree_mul hgm, hPm.natDegree_pow, hPd]
      have hiff : ∀ n : F[X], m = n * P ^ k ↔ n = g := fun n => by
        rw [hg, mul_comm n]
        exact ⟨fun h => (mul_left_cancel₀ hPk.ne_zero h).symm, fun h => by rw [h]⟩
      rw [if_pos ⟨g, hg⟩, sum_congr rfl (g := fun n => if n = g then poleVec n else 0)
        fun n _ => by simp only [hiff], sum_ite_eq', if_pos (mem_monicLE.mpr ⟨hgm, by omega⟩)]
      show r ^ g.natDegree = r ^ (m.natDegree - k * d)
      congr 1
      omega
    · rw [if_neg hdvd]
      exact sum_eq_zero fun n _ => if_neg fun h => hdvd ⟨n, by rw [h, mul_comm]⟩
  -- each term is `r^{deg m}` times a forward weight plus a divisor weight
  have hterm : ∀ d ∈ Icc 1 N, ∀ P ∈ irrDeg (F := F) d, ∀ k ∈ Icc 1 N,
      (d : ℝ) * r ^ (k * d) *
        (∑ n ∈ monicLE N, (if n = m * P ^ k then poleVec n else 0) +
          ∑ n ∈ monicLE N, (if m = n * P ^ k then poleVec n else 0)) =
      r ^ m.natDegree *
        ((if k * d ≤ N - m.natDegree then (d : ℝ) * ((Fintype.card F : ℝ)⁻¹) ^ (k * d) else 0) +
          (if P ^ k ∣ m then (d : ℝ) else 0)) := by
    intro d _ P hP k _
    rw [hfwd d P hP k, hbwd d P hP k]
    have hfw : (d : ℝ) * r ^ (k * d) *
        (if m.natDegree + k * d ≤ N then r ^ (m.natDegree + k * d) else 0) =
        r ^ m.natDegree *
          (if k * d ≤ N - m.natDegree then (d : ℝ) * ((Fintype.card F : ℝ)⁻¹) ^ (k * d) else 0) := by
      by_cases h : m.natDegree + k * d ≤ N
      · rw [if_pos h, if_pos (by omega), ← hr2, ← pow_mul, pow_add]
        ring_nf
      · rw [if_neg h, if_neg (by omega)]
        ring
    have hbw : (d : ℝ) * r ^ (k * d) * (if P ^ k ∣ m then r ^ (m.natDegree - k * d) else 0) =
        r ^ m.natDegree * (if P ^ k ∣ m then (d : ℝ) else 0) := by
      by_cases h : P ^ k ∣ m
      · obtain ⟨hPm, hPd, -⟩ := mem_irrDeg.mp hP
        have hle : k * d ≤ m.natDegree := by
          have := natDegree_le_of_dvd h hmon.ne_zero
          rwa [hPm.natDegree_pow, hPd] at this
        rw [if_pos h, if_pos h]
        calc (d : ℝ) * r ^ (k * d) * r ^ (m.natDegree - k * d)
            = (d : ℝ) * r ^ (k * d + (m.natDegree - k * d)) := by rw [pow_add]; ring
          _ = r ^ m.natDegree * d := by rw [Nat.add_sub_cancel' hle]; ring
      · rw [if_neg h, if_neg h]
        ring
    rw [mul_add, hfw, hbw, mul_add]
  rw [hexp, sum_congr rfl fun d hd => sum_congr rfl fun P hP => sum_congr rfl fun k hk =>
    hterm d hd P hP k hk]
  simp only [← mul_sum, sum_add_distrib]
  rw [sum_primePower_weight_eq (Nat.sub_le N m.natDegree)]
  have hdeg : ∑ d ∈ Icc 1 N, ∑ P ∈ irrDeg (F := F) d, ∑ k ∈ Icc 1 N,
      (if P ^ k ∣ m then (d : ℝ) else 0) = m.natDegree := by
    exact_mod_cast (natDegree_eq_sum_irr hmon hmN).symm
  rw [hdeg, poleVec, ← hr, Nat.cast_sub hmN]
  ring

/-- **The function-field ceiling is exact.** On monic polynomials of degree `≤ N` over `𝔽_q`, the
atomic kernel `D·1 − P_N` is positive semidefinite iff `D ≥ N` (in units of `log q`). -/
theorem atomFq_nonneg_iff (N : ℕ) (D : ℝ) :
    (∀ x : F[X] → ℝ, 0 ≤ D * ∑ f ∈ monicLE N, x f ^ 2 -
      ∑ f ∈ monicLE N, ∑ g ∈ monicLE N, primeKernelFq N f g * x f * x g) ↔ (N : ℝ) ≤ D :=
  atom_nonneg_iff (monicLE N) ⟨1, mem_monicLE.mpr ⟨monic_one, by simp⟩⟩ (primeKernelFq N)
    (primeKernelFq_symm N) (fun f _ g _ => primeKernelFq_nonneg N f g) (fun f _ => poleVec_pos f)
    (fun _ hm => primeKernelFq_poleVec hm) D

/-! ### The second rung -/

/-- The pole vector restricted to the multiples of `Q`. -/
def divVec (Q f : F[X]) : ℝ := if Q ∣ f then poleVec f else 0

/-- **The multiples of `Q` carry energy `N − deg Q`.** For monic `Q ∣ m`,
`(P_N u_Q)(m) = (N − deg Q) u_Q(m)`: forward prime powers keep the factor `Q`, and the divisors
`h ∣ m` with `Q ∣ m/h` are exactly the divisors of `m/Q`. -/
theorem primeKernelFq_divVec {N : ℕ} {Q : F[X]} (hQ : Q.Monic) {m : F[X]} (hm : m ∈ monicLE N)
    (hQm : Q ∣ m) :
    ∑ n ∈ monicLE N, primeKernelFq N m n * divVec Q n = ((N : ℝ) - Q.natDegree) * divVec Q m := by
  obtain ⟨hmon, hmN⟩ := mem_monicLE.mp hm
  obtain ⟨m', hm'⟩ := hQm
  have hm'mon : m'.Monic := hQ.of_mul_monic_left (hm' ▸ hmon)
  have hdegm : m.natDegree = Q.natDegree + m'.natDegree := by
    rw [hm', hQ.natDegree_mul hm'mon]
  set r : ℝ := (Real.sqrt (Fintype.card F))⁻¹ with hr
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hr2 : r ^ 2 = (Fintype.card F : ℝ)⁻¹ := by rw [hr, inv_pow, Real.sq_sqrt hq.le]
  have hexp : ∑ n ∈ monicLE N, primeKernelFq N m n * divVec Q n =
      ∑ d ∈ Icc 1 N, ∑ P ∈ irrDeg (F := F) d, ∑ k ∈ Icc 1 N, (d : ℝ) * r ^ (k * d) *
        (∑ n ∈ monicLE N, (if n = m * P ^ k then divVec Q n else 0) +
          ∑ n ∈ monicLE N, (if m = n * P ^ k then divVec Q n else 0)) := by
    simp only [primeKernelFq, sum_mul]
    rw [sum_comm]; refine sum_congr rfl fun d _ => ?_
    rw [sum_comm]; refine sum_congr rfl fun P _ => ?_
    rw [sum_comm]; refine sum_congr rfl fun k _ => ?_
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  -- forward prime powers keep the factor `Q`
  have hfwd : ∀ d, ∀ P ∈ irrDeg (F := F) d, ∀ k : ℕ,
      ∑ n ∈ monicLE N, (if n = m * P ^ k then divVec Q n else 0) =
        if m.natDegree + k * d ≤ N then r ^ (m.natDegree + k * d) else 0 := by
    intro d P hP k
    obtain ⟨hPm, hPd, -⟩ := mem_irrDeg.mp hP
    have hdeg : (m * P ^ k).natDegree = m.natDegree + k * d := by
      rw [hmon.natDegree_mul (hPm.pow k), hPm.natDegree_pow, hPd]
    have hQ' : Q ∣ m * P ^ k := ⟨m' * P ^ k, by rw [hm', mul_assoc]⟩
    rw [sum_ite_eq']
    simp only [mem_monicLE, hmon.mul (hPm.pow k), true_and, hdeg, divVec, if_pos hQ', poleVec, hr]
  -- the divisors `h` of `m` with `Q ∣ m/h` are the divisors of `m' = m/Q`
  have hbwd : ∀ d, ∀ P ∈ irrDeg (F := F) d, ∀ k : ℕ,
      ∑ n ∈ monicLE N, (if m = n * P ^ k then divVec Q n else 0) =
        if P ^ k ∣ m' then r ^ (m.natDegree - k * d) else 0 := by
    intro d P hP k
    obtain ⟨hPm, hPd, -⟩ := mem_irrDeg.mp hP
    have hPk : (P ^ k).Monic := hPm.pow k
    by_cases hdvd : P ^ k ∣ m
    · obtain ⟨g, hg⟩ := hdvd
      have hgm : g.Monic := hPk.of_mul_monic_left (hg ▸ hmon)
      have hdeg : m.natDegree = k * d + g.natDegree := by
        rw [hg, hPk.natDegree_mul hgm, hPm.natDegree_pow, hPd]
      have hiff : ∀ n : F[X], m = n * P ^ k ↔ n = g := fun n => by
        rw [hg, mul_comm n]
        exact ⟨fun h => (mul_left_cancel₀ hPk.ne_zero h).symm, fun h => by rw [h]⟩
      have hQg : Q ∣ g ↔ P ^ k ∣ m' := by
        constructor
        · rintro ⟨g', rfl⟩
          refine ⟨g', mul_left_cancel₀ hQ.ne_zero ?_⟩
          rw [← hm', hg]; ring
        · rintro ⟨g'', hg''⟩
          refine ⟨g'', mul_left_cancel₀ hPk.ne_zero ?_⟩
          rw [← hg, hm', hg'']; ring
      rw [sum_congr rfl (g := fun n => if n = g then divVec Q n else 0)
        fun n _ => by simp only [hiff], sum_ite_eq', if_pos (mem_monicLE.mpr ⟨hgm, by omega⟩)]
      unfold divVec
      by_cases hQg' : Q ∣ g
      · rw [if_pos hQg', if_pos (hQg.mp hQg')]
        show r ^ g.natDegree = r ^ (m.natDegree - k * d)
        congr 1
        omega
      · rw [if_neg hQg', if_neg fun h => hQg' (hQg.mpr h)]
    · rw [if_neg fun h => hdvd (h.trans ⟨Q, by rw [hm', mul_comm]⟩)]
      exact sum_eq_zero fun n _ => if_neg fun h => hdvd ⟨n, by rw [h, mul_comm]⟩
  have hterm : ∀ d ∈ Icc 1 N, ∀ P ∈ irrDeg (F := F) d, ∀ k ∈ Icc 1 N,
      (d : ℝ) * r ^ (k * d) *
        (∑ n ∈ monicLE N, (if n = m * P ^ k then divVec Q n else 0) +
          ∑ n ∈ monicLE N, (if m = n * P ^ k then divVec Q n else 0)) =
      r ^ m.natDegree *
        ((if k * d ≤ N - m.natDegree then (d : ℝ) * ((Fintype.card F : ℝ)⁻¹) ^ (k * d) else 0) +
          (if P ^ k ∣ m' then (d : ℝ) else 0)) := by
    intro d _ P hP k _
    rw [hfwd d P hP k, hbwd d P hP k]
    have hfw : (d : ℝ) * r ^ (k * d) *
        (if m.natDegree + k * d ≤ N then r ^ (m.natDegree + k * d) else 0) =
        r ^ m.natDegree *
          (if k * d ≤ N - m.natDegree then (d : ℝ) * ((Fintype.card F : ℝ)⁻¹) ^ (k * d) else 0) := by
      by_cases h : m.natDegree + k * d ≤ N
      · rw [if_pos h, if_pos (by omega), ← hr2, ← pow_mul, pow_add]
        ring_nf
      · rw [if_neg h, if_neg (by omega)]
        ring
    have hbw : (d : ℝ) * r ^ (k * d) * (if P ^ k ∣ m' then r ^ (m.natDegree - k * d) else 0) =
        r ^ m.natDegree * (if P ^ k ∣ m' then (d : ℝ) else 0) := by
      by_cases h : P ^ k ∣ m'
      · obtain ⟨hPm, hPd, -⟩ := mem_irrDeg.mp hP
        have hle : k * d ≤ m.natDegree := by
          have := natDegree_le_of_dvd h hm'mon.ne_zero
          rw [hPm.natDegree_pow, hPd] at this
          omega
        rw [if_pos h, if_pos h]
        calc (d : ℝ) * r ^ (k * d) * r ^ (m.natDegree - k * d)
            = (d : ℝ) * r ^ (k * d + (m.natDegree - k * d)) := by rw [pow_add]; ring
          _ = r ^ m.natDegree * d := by rw [Nat.add_sub_cancel' hle]; ring
      · rw [if_neg h, if_neg h]
        ring
    rw [mul_add, hfw, hbw, mul_add]
  rw [hexp, sum_congr rfl fun d hd => sum_congr rfl fun P hP => sum_congr rfl fun k hk =>
    hterm d hd P hP k hk]
  simp only [← mul_sum, sum_add_distrib]
  rw [sum_primePower_weight_eq (Nat.sub_le N m.natDegree)]
  have hdeg' : ∑ d ∈ Icc 1 N, ∑ P ∈ irrDeg (F := F) d, ∑ k ∈ Icc 1 N,
      (if P ^ k ∣ m' then (d : ℝ) else 0) = m'.natDegree := by
    exact_mod_cast (natDegree_eq_sum_irr hm'mon (by omega)).symm
  rw [hdeg', divVec, if_pos ⟨m', hm'⟩, poleVec, ← hr, Nat.cast_sub hmN, hdegm]
  push_cast
  ring

end GaloisForLFunctions.ArithmeticKreinLangerTheory
