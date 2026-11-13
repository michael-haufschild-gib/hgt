import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBoundStatesOfAWindowAreTheSlowModesOfItsDoobChain
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.UnderTheRiemannHypothesisWeilsFormOfAStepPacketIsNonnegative
import Mathlib.NumberTheory.Chebyshev

/-!
# The floor trees bind a window at the square root of its ratio

The **binding energy** of a window is minus the eigenvalue `λ` of the positive ground vector of
its neutral part. It is created by the floor trees, at the scale of the Chebyshev sum
`Σ_{k ≤ ρ} Λ(k)/√k ≍ √ρ`, and under the Riemann hypothesis it is at most of that order.

* **Lower bound, unconditional** (`eigenvalue_mul_harmonic_le`). On the window `(R, (1 + J)R]`,
  at every block size `R`, the ground eigenvalue satisfies
  `λ · Σ_{j < J} 1/(j + 1) ≤ Σ_{j < J} log(j + 2)/(j + 1) − 2 ψ(K)/√(2K)`, `K = ⌊(J + 1)/2⌋`.
  The test is the packet `a^{−1/2}` on the blocks `a = 1, …, J` of the coarsest member of the
  tower. The diagonal costs at most `log(a + 1)` per block; the jets only help; the gain comes from
  the edges of the floor trees of all `k ≤ (J + 1)/2` at the root block `(1, 2]`: its `k`
  children `k, …, 2k − 1` carry `Λ(k)/√(2k)` each (`sum_rootPacket_floorContact_ge`). Chebyshev's
  bound `ψ(K) ≥ K log 2 − log(K + 1)` makes the right side of order `−√J`, while the harmonic sum
  is `log J`: the binding energy grows at least like `√ρ/log ρ`.
* **Upper bound under RH** (`neg_eigenvalue_le_of_riemannHypothesis`). Weil's form is nonnegative
  on step packets, so the neutral part is at least minus twice the product of the charges, and
  Cauchy–Schwarz gives `−λ ≤ 2 √(J (log(R + J) − log R)/R)` on `(R, R + J]`: at most
  `2√((ρ − 1) log ρ)` at ratio `ρ`.

So under RH the binding energy of a window of ratio `ρ` lies between `c √ρ/log ρ` and
`2 √(ρ log ρ)`; the Doob chain must mix at that rate, and the edges that create the binding are
those of the floor trees of the primes up to the size of the window.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open scoped ArithmeticFunction.vonMangoldt Chebyshev

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-! ### The entries of the neutral part -/

/-- The diagonal of the neutral part is at most `log(a + 1)`: the density of the block minus its
positive self-jet. -/
theorem neutralBlock_self_le_log {a : ℕ} (ha : 1 ≤ a) (Q : ℕ) :
    neutralBlock Q a a ≤ Real.log (a + 1) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hself : neutralBlock Q a a = blockDensity a - blockJet a a := by
    rw [neutralBlock, blockMatrix_self ha Q]
    ring
  have hjet : 0 ≤ blockJet a a := by
    unfold blockJet
    have h1 := xLogXDiff_pos (n := a + a + 1) (by omega)
    rw [Nat.sub_self, xLogXDiff_zero]
    linarith
  -- `a log((a + 1)/a) ≤ 1`
  have hlog : (a : ℝ) * (Real.log (a + 1) - Real.log a) ≤ 1 := by
    rw [← Real.log_div (by positivity) ha'.ne']
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (a + 1) / a by positivity)
    have he : ((a : ℝ) + 1) / a - 1 = 1 / a := by field_simp; ring
    rw [he] at h
    calc (a : ℝ) * Real.log ((a + 1) / a) ≤ a * (1 / a) :=
          mul_le_mul_of_nonneg_left h ha'.le
      _ = 1 := by field_simp
  have hγ : 0 ≤ Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant.le.trans'
    (by norm_num)
  have h2π : 1 ≤ Real.log (2 * Real.pi) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have hdens : blockDensity a = (a + 1) * Real.log (a + 1) - a * Real.log a -
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) := by
    simp only [blockDensity, xLogX]
    push_cast
    ring
  rw [hself, hdens]
  nlinarith [hlog]

/-- Off the diagonal the neutral part is at most minus the contacts. -/
theorem neutralBlock_le_neg_floorContact {a b : ℕ} (hab : a < b) (Q : ℕ) :
    neutralBlock Q a b ≤ -floorContact Q a b := by
  rw [neutralBlock, blockMatrix_of_lt hab]
  have hJ : 0 < blockJet a b := by
    unfold blockJet
    have h1 := xLogXDiff_pos (n := a + b + 1) (by omega)
    have h2 := xLogXDiff_pos (n := b - a) (by omega)
    linarith
  linarith

/-! ### The packet `a^{−1/2}` -/

/-- The value `a^{−1/2}` on the block `a = j + 1`. -/
def rootPacket (j : ℕ) : ℝ := 1 / Real.sqrt (j + 1)

theorem rootPacket_pos (j : ℕ) : 0 < rootPacket j := by
  unfold rootPacket
  positivity

theorem rootPacket_zero : rootPacket 0 = 1 := by simp [rootPacket]

theorem rootPacket_sq (j : ℕ) : rootPacket j ^ 2 = 1 / (j + 1) := by
  unfold rootPacket
  rw [div_pow, Real.sq_sqrt (by positivity), one_pow]

/-- **The neutral part on the packet `a^{−1/2}`** is at most its diagonal bound minus twice the
contacts of the root block. -/
theorem sum_rootPacket_neutralBlock_le (Q : ℕ) {J : ℕ} (hJ : 1 ≤ J) :
    ∑ j ∈ range J, ∑ l ∈ range J, rootPacket j * rootPacket l * neutralBlock Q (1 + j) (1 + l) ≤
      ∑ j ∈ range J, rootPacket j ^ 2 * Real.log (j + 2) -
        2 * ∑ l ∈ range J, rootPacket l * floorContact Q 1 (1 + l) := by
  have hterm : ∀ j l, rootPacket j * rootPacket l * neutralBlock Q (1 + j) (1 + l) ≤
      (if j = l then rootPacket j ^ 2 * Real.log (j + 2) else 0) -
        ((if j = 0 then rootPacket l * floorContact Q 1 (1 + l) else 0) +
          (if l = 0 then rootPacket j * floorContact Q 1 (1 + j) else 0)) := by
    intro j l
    have hj := rootPacket_pos j
    have hl := rootPacket_pos l
    by_cases hjl : j = l
    · subst hjl
      have hd := neutralBlock_self_le_log (a := 1 + j) (by omega) Q
      have hcast : ((1 + j : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
      rw [hcast] at hd
      have hc0 : (if j = 0 then rootPacket j * floorContact Q 1 (1 + j) else 0) = 0 := by
        split_ifs with h
        · subst h
          rw [show 1 + 0 = 1 from rfl, floorContact_self le_rfl Q, mul_zero]
        · rfl
      rw [if_pos rfl, hc0, add_zero, sub_zero, ← sq]
      exact mul_le_mul_of_nonneg_left hd (sq_nonneg _)
    · rw [if_neg hjl]
      by_cases hj0 : j = 0
      · subst hj0
        have hl0 : l ≠ 0 := fun h => hjl h.symm
        rw [if_pos rfl, if_neg hl0, rootPacket_zero, one_mul]
        have h := neutralBlock_le_neg_floorContact (show 1 < 1 + l by omega) Q
        have := mul_le_mul_of_nonneg_left h hl.le
        simp only [add_zero, zero_sub] at this ⊢
        linarith
      · by_cases hl0 : l = 0
        · subst hl0
          rw [if_neg hj0, if_pos rfl, zero_add, zero_sub, rootPacket_zero, mul_one, Nat.add_zero,
            neutralBlock_comm]
          have h := neutralBlock_le_neg_floorContact (show 1 < 1 + j by omega) Q
          have := mul_le_mul_of_nonneg_left h hj.le
          linarith
        · rw [if_neg hj0, if_neg hl0, add_zero, sub_zero]
          have h := neutralBlock_neg (show 1 + j ≠ 1 + l by omega) Q
          nlinarith [mul_pos hj hl]
  refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hterm j l).trans
    (le_of_eq ?_)
  have h0 : 0 ∈ range J := Finset.mem_range.mpr hJ
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : ∑ j ∈ range J, ∑ l ∈ range J,
      (if j = l then rootPacket j ^ 2 * Real.log (j + 2) else 0) =
      ∑ j ∈ range J, rootPacket j ^ 2 * Real.log (j + 2) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.sum_ite_eq (range J) j (fun _ => rootPacket j ^ 2 * Real.log (j + 2)),
        if_pos hj]
  have hB : ∑ j ∈ range J, ∑ l ∈ range J,
      (if j = 0 then rootPacket l * floorContact Q 1 (1 + l) else 0) =
      ∑ l ∈ range J, rootPacket l * floorContact Q 1 (1 + l) := by
    rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (fun h => absurd h0 h)]
    simp
  have hC : ∑ j ∈ range J, ∑ l ∈ range J,
      (if l = 0 then rootPacket j * floorContact Q 1 (1 + j) else 0) =
      ∑ j ∈ range J, rootPacket j * floorContact Q 1 (1 + j) :=
    Finset.sum_congr rfl fun j _ => by
      rw [Finset.sum_ite_eq' (range J) 0 (fun _ => rootPacket j * floorContact Q 1 (1 + j)),
        if_pos h0]
  rw [hA, hB, hC]
  ring

/-- **The contacts of the root block**: its `k` children under the floor map of `k ≤ (J + 1)/2`
carry at least `Λ(k)/√(2k)`. -/
theorem sum_rootPacket_floorContact_ge {Q J : ℕ} (hJQ : J ≤ Q) :
    ∑ k ∈ Icc 2 ((J + 1) / 2), (Λ k : ℝ) / Real.sqrt (2 * k) ≤
      ∑ l ∈ range J, rootPacket l * floorContact Q 1 (1 + l) := by
  have hexp : ∑ l ∈ range J, rootPacket l * floorContact Q 1 (1 + l) =
      ∑ k ∈ Icc 2 Q, ∑ l ∈ range J,
        (if (1 + l) / k = 1 then rootPacket l * ((Λ k : ℝ) / k) else 0) := by
    simp only [floorContact, Finset.mul_sum, mul_ite, mul_zero]
    exact Finset.sum_comm
  rw [hexp]
  have hsub : Icc 2 ((J + 1) / 2) ⊆ Icc 2 Q := Finset.Icc_subset_Icc le_rfl (by omega)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
    Finset.sum_nonneg fun l _ => by
      split_ifs
      · exact mul_nonneg (rootPacket_pos l).le
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
      · exact le_rfl)
  refine Finset.sum_le_sum fun k hk => ?_
  obtain ⟨hk2, hkJ⟩ := Finset.mem_Icc.mp hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hΛ : (0 : ℝ) ≤ (Λ k : ℝ) / k := div_nonneg ArithmeticFunction.vonMangoldt_nonneg hk'.le
  have hIco : Ico (k - 1) (2 * k - 1) ⊆ range J := fun l hl => by
    have := Finset.mem_Ico.mp hl
    exact Finset.mem_range.mpr (by omega)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hIco fun l _ _ => by
    split_ifs
    · exact mul_nonneg (rootPacket_pos l).le hΛ
    · exact le_rfl)
  have hlow : ∀ l ∈ Ico (k - 1) (2 * k - 1), 1 / Real.sqrt (2 * k) * ((Λ k : ℝ) / k) ≤
      (if (1 + l) / k = 1 then rootPacket l * ((Λ k : ℝ) / k) else 0) := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := Finset.mem_Ico.mp hl
    have hdiv : (1 + l) / k = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [if_pos hdiv]
    refine mul_le_mul_of_nonneg_right ?_ hΛ
    unfold rootPacket
    refine one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_le_sqrt ?_)
    have : (l : ℝ) + 1 ≤ 2 * k := by
      have : l + 1 ≤ 2 * k := by omega
      exact_mod_cast this
    linarith
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hlow)
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    show 2 * k - 1 - (k - 1) = k by omega]
  have hs : Real.sqrt (2 * k) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

/-- The von Mangoldt sum from `2` is Chebyshev's function. -/
theorem sum_Icc_two_vonMangoldt (K : ℕ) : ∑ k ∈ Icc 2 K, (Λ k : ℝ) = ψ (K : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  refine Finset.sum_subset (fun k hk => ?_) fun k hk hk2 => ?_
  · have := Finset.mem_Icc.mp hk
    exact Finset.mem_Ioc.mpr ⟨by omega, this.2⟩
  · have h1 := Finset.mem_Ioc.mp hk
    have hk1 : k = 1 := by
      by_contra hne
      exact hk2 (Finset.mem_Icc.mpr ⟨by omega, h1.2⟩)
    rw [hk1, ArithmeticFunction.vonMangoldt_apply_one]

/-- **The contacts of the root block are at least Chebyshev's function over `√(2K)`.** -/
theorem psi_div_le_sum_vonMangoldt_div_sqrt (K : ℕ) :
    ψ (K : ℝ) / Real.sqrt (2 * K) ≤ ∑ k ∈ Icc 2 K, (Λ k : ℝ) / Real.sqrt (2 * k) := by
  rw [← sum_Icc_two_vonMangoldt, Finset.sum_div]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk := Finset.mem_Icc.mp hk
  have hk0 : (0 : ℝ) < 2 * k := by
    have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    linarith
  exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
    (Real.sqrt_pos.mpr hk0) (Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 2 * k ≤ 2 * K)))

/-! ### The binding energy -/

/-- **The floor trees bind every window at the square root of its ratio.** On `(R, (1 + J)R]`, at
every block size `R`, the eigenvalue `λ` of a positive eigenvector of the neutral part satisfies
`λ · Σ_{j < J} 1/(j + 1) ≤ Σ_{j < J} log(j + 2)/(j + 1) − 2 ψ(K)/√(2K)`, `K = ⌊(J + 1)/2⌋`. -/
theorem eigenvalue_mul_harmonic_le {Q R J : ℕ} (hR : 1 ≤ R) (hJ : 1 ≤ J) (hJQ : J ≤ Q)
    {φ : Fin (R * J) → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : neutralWindow Q R (R * J) *ᵥ φ = lam • φ) :
    lam * ∑ j ∈ range J, 1 / ((j : ℝ) + 1) ≤
      ∑ j ∈ range J, Real.log (j + 2) / (j + 1) -
        2 * (ψ (((J + 1) / 2 : ℕ) : ℝ) / Real.sqrt (2 * ((J + 1) / 2 : ℕ))) := by
  have hray : lam * ∑ i : Fin (R * J), refineStep R rootPacket i ^ 2 ≤
      bilin (neutralWindow Q R (R * J)) (fun i => refineStep R rootPacket i)
        (fun i => refineStep R rootPacket i) :=
    lam_mul_sum_sq_le_bilin (neutralWindow_symm Q R (R * J))
      (fun _ _ hij => (neutralWindow_neg_of_ne Q R hij).le) hφ heig
      (fun i => refineStep R rootPacket i)
  have hform : bilin (neutralWindow Q R (R * J)) (fun i => refineStep R rootPacket i)
      (fun i => refineStep R rootPacket i) =
      ∑ j ∈ range J, ∑ l ∈ range J, rootPacket j * rootPacket l *
        neutralBlock Q (1 + j) (1 + l) := by
    have h := sum_neutralBlock_refine (R := 1) le_rfl hR Q J rootPacket
    simp only [Nat.mul_one] at h
    rw [← h]
    exact sum_fin_windowMatrix_coe (neutralBlock Q) R (R * J) (refineStep R rootPacket)
  have hmass : ∑ i : Fin (R * J), refineStep R rootPacket i ^ 2 =
      ∑ j ∈ range J, 1 / ((j : ℝ) + 1) :=
    (Fin.sum_univ_eq_sum_range (fun i => refineStep R rootPacket i ^ 2) (R * J)).trans
      ((sum_refineStep_sq hR J rootPacket).trans
        (Finset.sum_congr rfl fun j _ => rootPacket_sq j))
  have hdiag : ∑ j ∈ range J, rootPacket j ^ 2 * Real.log (j + 2) =
      ∑ j ∈ range J, Real.log (j + 2) / (j + 1) :=
    Finset.sum_congr rfl fun j _ => by rw [rootPacket_sq]; ring
  have hmain := sum_rootPacket_neutralBlock_le Q hJ
  have hcont := (psi_div_le_sum_vonMangoldt_div_sqrt ((J + 1) / 2)).trans
    (sum_rootPacket_floorContact_ge hJQ)
  rw [hmass, hform] at hray
  rw [hdiag] at hmain
  linarith

/-- **Under the Riemann hypothesis the binding energy is at most of the order of the square root
of the ratio**: on `(R, R + J]`, `−λ ≤ 2 √(J (log(R + J) − log R)/R)`. -/
theorem neg_eigenvalue_le_of_riemannHypothesis (hRH : RiemannHypothesis) {Q R J : ℕ}
    (hR : 1 ≤ R) (hJ : 1 ≤ J) (hQ : R + J ≤ Q * R) {φ : Fin J → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : neutralWindow Q R J *ᵥ φ = lam • φ) :
    -lam ≤ 2 * Real.sqrt (J * (Real.log ((R + J : ℕ) : ℝ) - Real.log R) / R) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  set σ : ℕ → ℝ := extendFin φ with hσ
  have hnn := packetForm_stepPacket_nonneg_of_riemannHypothesis hRH hR hQ σ
  rw [packetForm_stepPacket_eq_sum_blockMatrix hR Q J σ,
    sum_blockMatrix_eq_charges_add_neutral] at hnn
  -- the neutral part on the ground vector
  have hN : ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) =
      lam * ∑ j ∈ range J, σ j ^ 2 := by
    have h1 := bilin_eigen heig φ
    have h2 : bilin (neutralWindow Q R J) φ φ =
        ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) := by
      unfold bilin
      rw [neutralWindow]
      have := sum_fin_windowMatrix_eq (neutralBlock Q) R φ
      exact this
    rw [← h2, h1, show ∑ k, φ k * φ k = ∑ j ∈ range J, extendFin (fun k => φ k * φ k) j from
      sum_fin_eq_sum_range_extendFin _]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [hσ, extendFin, dif_pos (Finset.mem_range.mp hj), sq]
  set S := ∑ j ∈ range J, σ j ^ 2
  set c₀ := ∑ j ∈ range J, σ j
  set c₁ := ∑ j ∈ range J, σ j * blockDegree (R + j)
  have hS : 0 < S := by
    have hpos : 0 < σ 0 := by
      rw [hσ, extendFin, dif_pos (show 0 < J from hJ)]
      exact hφ _
    exact lt_of_lt_of_le (pow_pos hpos 2) (Finset.single_le_sum
      (f := fun j => σ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_range.mpr hJ))
  -- the degrees: each at most `1/R`, summing to `log((R + J)/R)`
  have hdeg_nonneg : ∀ j, 0 ≤ blockDegree (R + j) := fun j =>
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast (show 0 < R + j by omega))
      (by exact_mod_cast (Nat.le_succ _)))
  have hdeg_le : ∀ j, blockDegree (R + j) ≤ 1 / R := by
    intro j
    have hpos : (0 : ℝ) < (R + j : ℕ) := by exact_mod_cast (show 0 < R + j by omega)
    have hlog := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < ((R + j + 1 : ℕ) : ℝ) / (R + j : ℕ) by positivity)
    rw [Real.log_div (by positivity) hpos.ne'] at hlog
    have he : ((R + j + 1 : ℕ) : ℝ) / (R + j : ℕ) - 1 = 1 / (R + j : ℕ) := by
      field_simp
      push_cast
      ring
    rw [he] at hlog
    have hRj : (R : ℝ) ≤ (R + j : ℕ) := by exact_mod_cast (Nat.le_add_right R j)
    calc blockDegree (R + j) = Real.log ((R + j + 1 : ℕ) : ℝ) - Real.log (R + j : ℕ) := by
          simp only [blockDegree]
      _ ≤ 1 / (R + j : ℕ) := hlog
      _ ≤ 1 / R := one_div_le_one_div_of_le hR' hRj
  have hdeg_sum : ∑ j ∈ range J, blockDegree (R + j) =
      Real.log ((R + J : ℕ) : ℝ) - Real.log R := sum_blockDegree_range R J
  have hdeg_sq : ∑ j ∈ range J, blockDegree (R + j) ^ 2 ≤
      (Real.log ((R + J : ℕ) : ℝ) - Real.log R) / R := by
    rw [← hdeg_sum, div_eq_mul_one_div, Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (hdeg_le j) (hdeg_nonneg j)
  -- Cauchy–Schwarz on the charges
  have hc₀ : c₀ ^ 2 ≤ J * S := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (range J) (fun _ => (1 : ℝ)) σ
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at h
    exact h
  have hc₁ : c₁ ^ 2 ≤ S * ((Real.log ((R + J : ℕ) : ℝ) - Real.log R) / R) :=
    (Finset.sum_mul_sq_le_sq_mul_sq (range J) σ fun j => blockDegree (R + j)).trans
      (mul_le_mul_of_nonneg_left hdeg_sq hS.le)
  set B := J * ((Real.log ((R + J : ℕ) : ℝ) - Real.log R) / R)
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (by
    rw [← hdeg_sum]
    exact div_nonneg (Finset.sum_nonneg fun j _ => hdeg_nonneg j) hR'.le)
  have hprod : |c₀ * c₁| ≤ S * Real.sqrt B := by
    have hsq : (c₀ * c₁) ^ 2 ≤ (S * Real.sqrt B) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hB]
      calc c₀ ^ 2 * c₁ ^ 2 ≤ (J * S) * (S * ((Real.log ((R + J : ℕ) : ℝ) - Real.log R) / R)) :=
            mul_le_mul hc₀ hc₁ (sq_nonneg _) (by positivity)
        _ = S ^ 2 * B := by simp only [B]; ring
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (by positivity : 0 ≤ S * Real.sqrt B)] at h
  have hlower : -(2 * (S * Real.sqrt B)) ≤ lam * S := by
    rw [← hN]
    linarith [hnn, hprod, le_abs_self (c₀ * c₁)]
  have hfinal : -lam * S ≤ 2 * Real.sqrt B * S := by nlinarith
  have := le_of_mul_le_mul_right hfinal hS
  simpa [B, mul_div_assoc] using this

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
