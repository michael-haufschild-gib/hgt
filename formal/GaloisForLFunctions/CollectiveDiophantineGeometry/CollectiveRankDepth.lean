import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.LinearFormsWithExplicitDependenceOnTheirNumber
import GaloisForLFunctions.HTGeometry.LinearIndependenceMinorTransfer
import GaloisForLFunctions.HTGeometry.ReplicaCrowdingSpectralDimensionLaw

/-!
# Rank bounds for collective prime-logarithm approximation

An independent family of `r` integer forms in `k` prime logarithms cannot
all be arbitrarily small inside a fixed coefficient box. Eliminating a
nonzero maximal minor reduces the transcendence estimate to `k-r+1`
logarithms. In particular, the penultimate rank uses only two logarithms.
Full rank has an elementary determinant floor. Below the rank-`r` floor,
near relations span at most `r-1` dimensions and their number in a height-`H`
box is at most `(2H+1)^(r-1)`.
-/

open Finset Real Matrix

namespace GaloisForLFunctions.CollectiveDiophantineGeometry

open TranscendenceTheoryOfThePrimeOrbit RHTower.Matveev

noncomputable section

/-- Values of integer coefficient rows on the vector of prime logarithms. -/
def primeLogForms {r k : ℕ} (M : Matrix (Fin r) (Fin k) ℤ) (p : Fin k → ℕ) : Fin r → ℝ :=
  fun i => ∑ j, (M i j : ℝ) * log (p j)

/-- Depth floor for `r` independent forms, with `d` uneliminated coordinates.
The scalar exponent uses `d+1` logarithms; full rank needs only an integer determinant. -/
def rankDepthFloor (r d y : ℕ) (H : ℝ) : ℝ :=
  (if d = 0 then log 2 else
    exp (-(bakerExponent d ⌈(d + 1 : ℝ) * log y⌉₊ *
      (log ((d + 1 : ℝ) * (r.factorial : ℝ) * H ^ r) + 2)))) /
        ((r.factorial : ℝ) * H ^ (r - 1))

/-- The collective floor is positive for every positive coefficient height. -/
theorem rankDepthFloor_pos (r d y : ℕ) {H : ℝ} (hH : 0 < H) :
    0 < rankDepthFloor r d y H := by
  unfold rankDepthFloor
  apply div_pos ?_ (by positivity)
  split_ifs
  · exact log_pos (by norm_num)
  · exact exp_pos _

private theorem abs_det_cast_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {H : ℝ}
    (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    |(A.det : ℝ)| ≤ (r.factorial : ℝ) * H ^ r := by
  have h := Matrix.det_le (A := (Int.castRingHom ℝ).mapMatrix A)
    (abv := AbsoluteValue.abs) hA
  rw [← (Int.castRingHom ℝ).map_det] at h
  simp only [Fintype.card_fin, nsmul_eq_mul] at h
  change |(A.det : ℝ)| ≤ (r.factorial : ℝ) * H ^ r at h
  exact h

private theorem abs_adjugate_le {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {H : ℝ} (hA : ∀ i j, |A i j| ≤ H) (i j : Fin (n + 1)) :
    |A.adjugate i j| ≤ (n.factorial : ℝ) * H ^ n := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]
  have h := Matrix.det_le (A := A.submatrix j.succAbove i.succAbove)
    (abv := AbsoluteValue.abs) (fun k l => hA _ _)
  simp only [Fintype.card_fin, nsmul_eq_mul] at h
  change |(A.submatrix j.succAbove i.succAbove).det| ≤ (n.factorial : ℝ) * H ^ n at h
  exact h

private theorem abs_cramer_le {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {H ε : ℝ}
    (hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H)
    (v : Fin (n + 1) → ℝ) (hv : ∀ i, |v i| ≤ ε) (i : Fin (n + 1)) :
    |A.cramer v i| ≤ ((n + 1).factorial : ℝ) * H ^ n * ε := by
  rw [Matrix.cramer_eq_adjugate_mulVec]
  change |∑ j, A.adjugate i j * v j| ≤ _
  calc
    _ ≤ ∑ j, |A.adjugate i j * v j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (n + 1), (n.factorial : ℝ) * H ^ n * ε := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (abs_adjugate_le A hA i j) (hv j) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hH _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

private theorem cast_cramer {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (b : Fin r → ℤ) (i : Fin r) :
    ((Int.castRingHom ℝ).mapMatrix A).cramer (fun j => (b j : ℝ)) i =
      (A.cramer b i : ℝ) := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply]
  have heq : ((Int.castRingHom ℝ).mapMatrix A).updateCol i (fun j => (b j : ℝ)) =
      (Int.castRingHom ℝ).mapMatrix (A.updateCol i b) := by
    ext j k
    by_cases hk : k = i
    · subst k
      rw [Matrix.updateCol_self]
      change (b j : ℝ) = ((A.updateCol i b j i : ℤ) : ℝ)
      rw [Matrix.updateCol_self]
    · rw [Matrix.updateCol_ne hk]
      change (A j k : ℝ) = ((A.updateCol i b j k : ℤ) : ℝ)
      rw [Matrix.updateCol_ne hk]
  rw [heq, ← (Int.castRingHom ℝ).map_det]
  rfl

private theorem abs_integer_cramer_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (b : Fin r → ℤ) {H : ℝ} (hA : ∀ i j, |(A i j : ℝ)| ≤ H)
    (hb : ∀ i, |(b i : ℝ)| ≤ H) (i : Fin r) :
    |(A.cramer b i : ℝ)| ≤ (r.factorial : ℝ) * H ^ r := by
  rw [Matrix.cramer_apply]
  apply abs_det_cast_le
  intro j k
  by_cases hk : k = i
  · subst k
    simpa only [Matrix.updateCol_self] using hb j
  · simpa only [Matrix.updateCol_ne hk] using hA j k

private theorem cramer_mulVec_eq {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (x : Fin r → ℝ) :
    A.cramer (A.mulVec x) = A.det • x := by
  rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Elimination retains one pivot logarithm and all uneliminated logarithms. -/
private theorem cramer_block_identity {r d : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (B : Matrix (Fin r) (Fin d) ℤ) (x : Fin r → ℝ) (z : Fin d → ℝ) (i : Fin r) :
    (A.det : ℝ) * x i + ∑ j, (A.cramer (fun h => B h j) i : ℝ) * z j =
      ((Int.castRingHom ℝ).mapMatrix A).cramer
        (((Int.castRingHom ℝ).mapMatrix A).mulVec x +
          (B.map (Int.castRingHom ℝ)).mulVec z) i := by
  have hsplit : (B.map (Int.castRingHom ℝ)).mulVec z =
      ∑ j, z j • (fun h => (B h j : ℝ)) := by
    ext h
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j hj => mul_comm _ _
  rw [hsplit, map_add, cramer_mulVec_eq, map_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [← (Int.castRingHom ℝ).map_det]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, cast_cramer]
  ring


private theorem block_baker_depth {n d y : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (B : Matrix (Fin (n + 1)) (Fin d) ℤ) (q : Fin (d + 1) → ℕ)
    (hq : Function.Injective q) (hprime : ∀ j, (q j).Prime) (hy : ∀ j, q j ≤ y)
    (x : Fin (n + 1) → ℝ) (hx : x 0 = log (q 0))
    {H : ℝ} (hH : 1 ≤ H) (hA : ∀ i j, |(A i j : ℝ)| ≤ H)
    (hB : ∀ i j, |(B i j : ℝ)| ≤ H) (hdet : A.det ≠ 0) :
    ∃ i, exp (-(bakerExponent d ⌈(d + 1 : ℝ) * log y⌉₊ *
        (log ((d + 1 : ℝ) * ((n + 1).factorial : ℝ) * H ^ (n + 1)) + 2))) /
      (((n + 1).factorial : ℝ) * H ^ n) ≤
      |(((Int.castRingHom ℝ).mapMatrix A).mulVec x +
        (B.map (Int.castRingHom ℝ)).mulVec (fun j => log (q j.succ))) i| := by
  let ν : Fin (d + 1) → ℤ :=
    Fin.cons A.det (fun j => A.cramer (fun h => B h j) 0)
  have hν : ν ≠ 0 := by
    intro hz
    have h := congrFun hz 0
    simp only [ν, Fin.cons_zero, Pi.zero_apply] at h
    exact hdet h
  have hheightpos : 0 < (coeffHeight ν : ℝ) := by
    have hdetpos : 0 < A.det.natAbs := Int.natAbs_pos.mpr hdet
    have hle : A.det.natAbs ≤ coeffHeight ν := by
      unfold coeffHeight
      simpa only [ν, Fin.cons_zero] using
        (Finset.single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin (d + 1)))) =>
          Nat.zero_le (ν j).natAbs) (mem_univ 0))
    exact_mod_cast hdetpos.trans_le hle
  have hcoeff : ∀ j, |(ν j : ℝ)| ≤ ((n + 1).factorial : ℝ) * H ^ (n + 1) := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact abs_det_cast_le A hA
    · exact abs_integer_cramer_le A (fun h => B h j) hA (fun h => hB h j) 0
  have hheight : (coeffHeight ν : ℝ) ≤
      (d + 1 : ℝ) * ((n + 1).factorial : ℝ) * H ^ (n + 1) := by
    calc
      _ = ∑ j, |(ν j : ℝ)| := by simp only [coeffHeight, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]
      _ ≤ ∑ _j : Fin (d + 1), ((n + 1).factorial : ℝ) * H ^ (n + 1) :=
        Finset.sum_le_sum fun j hj => hcoeff j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring
  let v := ((Int.castRingHom ℝ).mapMatrix A).mulVec x +
    (B.map (Int.castRingHom ℝ)).mulVec (fun j => log (q j.succ))
  have hform : primeLogForm q ν = ((Int.castRingHom ℝ).mapMatrix A).cramer v 0 := by
    unfold primeLogForm
    rw [Fin.sum_univ_succ]
    simp only [ν, Fin.cons_zero, Fin.cons_succ]
    rw [← hx]
    exact cramer_block_identity A B x (fun j => log (q j.succ)) 0
  have hscalar := abs_primeLogForm_ge_of_le q hq hprime hy ν hν
  rw [hform] at hscalar
  have hlower : exp (-(bakerExponent d ⌈(d + 1 : ℝ) * log y⌉₊ *
      (log ((d + 1 : ℝ) * ((n + 1).factorial : ℝ) * H ^ (n + 1)) + 2))) ≤
      |((Int.castRingHom ℝ).mapMatrix A).cramer v 0| := by
    refine le_trans ?_ hscalar
    apply exp_le_exp.mpr
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left
    · exact add_le_add (log_le_log hheightpos hheight) le_rfl
    · unfold bakerExponent
      positivity
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image univ (fun i => |v i|)
    (Finset.univ_nonempty : (univ : Finset (Fin (n + 1))).Nonempty)
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hu := abs_cramer_le ((Int.castRingHom ℝ).mapMatrix A) hH0.le hA v
    (fun j => hmax j (mem_univ j)) 0
  refine ⟨i, ?_⟩
  apply (div_le_iff₀ (mul_pos (by positivity) (pow_pos hH0 n))).mpr
  simpa only [mul_comm] using hlower.trans hu

/-- At full rank, integrality of the determinant replaces the transcendence estimate. -/
private theorem full_rank_block_depth {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (x : Fin (n + 1) → ℝ)
    (hx : log 2 ≤ x 0) {H : ℝ} (hH : 1 ≤ H)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ H) (hdet : A.det ≠ 0) :
    ∃ i, log 2 / (((n + 1).factorial : ℝ) * H ^ n) ≤
      |((Int.castRingHom ℝ).mapMatrix A).mulVec x i| := by
  have hdetone : (1 : ℝ) ≤ |(A.det : ℝ)| := by
    have hpos : (0 : ℤ) < |A.det| := abs_pos.mpr hdet
    have hone : (1 : ℤ) ≤ |A.det| := by omega
    exact_mod_cast hone
  have hx0 : 0 ≤ x 0 := (log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hx
  let v := ((Int.castRingHom ℝ).mapMatrix A).mulVec x
  have hlower : log 2 ≤ |((Int.castRingHom ℝ).mapMatrix A).cramer v 0| := by
    change log 2 ≤ |((Int.castRingHom ℝ).mapMatrix A).cramer
      (((Int.castRingHom ℝ).mapMatrix A).mulVec x) 0|
    rw [cramer_mulVec_eq]
    change log 2 ≤ |((Int.castRingHom ℝ).mapMatrix A).det * x 0|
    rw [← (Int.castRingHom ℝ).map_det, abs_mul, abs_of_nonneg hx0]
    exact hx.trans (le_mul_of_one_le_left hx0 hdetone)
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image univ (fun i => |v i|)
    (Finset.univ_nonempty : (univ : Finset (Fin (n + 1))).Nonempty)
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hu := abs_cramer_le ((Int.castRingHom ℝ).mapMatrix A) hH0.le hA v
    (fun j => hmax j (mem_univ j)) 0
  refine ⟨i, (div_le_iff₀ (mul_pos (by positivity) (pow_pos hH0 n))).mpr ?_⟩
  simpa only [mul_comm] using hlower.trans hu

private theorem block_rank_depth {n d y : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (B : Matrix (Fin (n + 1)) (Fin d) ℤ) (q : Fin (d + 1) → ℕ)
    (hq : Function.Injective q) (hprime : ∀ j, (q j).Prime) (hy : ∀ j, q j ≤ y)
    (x : Fin (n + 1) → ℝ) (hx : x 0 = log (q 0))
    {H : ℝ} (hH : 1 ≤ H) (hA : ∀ i j, |(A i j : ℝ)| ≤ H)
    (hB : ∀ i j, |(B i j : ℝ)| ≤ H) (hdet : A.det ≠ 0) :
    ∃ i, rankDepthFloor (n + 1) d y H ≤
      |(((Int.castRingHom ℝ).mapMatrix A).mulVec x +
        (B.map (Int.castRingHom ℝ)).mulVec (fun j => log (q j.succ))) i| := by
  cases d with
  | zero =>
    have hx' : log 2 ≤ x 0 := by
      rw [hx]
      exact log_le_log (by norm_num) (by exact_mod_cast (hprime 0).two_le)
    obtain ⟨i, hi⟩ := full_rank_block_depth A x hx' hH hA hdet
    have hBzero : (B.map (Int.castRingHom ℝ)).mulVec
        (fun j : Fin 0 => log (q j.succ)) = 0 := by
      ext j
      simp [Matrix.mulVec, dotProduct]
    refine ⟨i, ?_⟩
    rw [hBzero, add_zero]
    exact hi
  | succ d =>
    have h := block_baker_depth A B q hq hprime hy x hx hH hA hB hdet
    simpa only [rankDepthFloor, if_neg (Nat.succ_ne_zero d), Nat.add_sub_cancel] using h

private theorem cons_injective {α : Type*} {d : ℕ} (a : α) (f : Fin d → α)
    (hf : Function.Injective f) (ha : ∀ j, a ≠ f j) :
    Function.Injective (Fin.cons a f) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      rfl
    · intro h
      exact (ha j h).elim
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact (ha i h.symm).elim
    · intro h
      exact congrArg Fin.succ (hf h)

/-- An independent family of integer forms has a collective depth floor.
Eliminating a maximal minor leaves only codimension plus one logarithms in
the scalar transcendence estimate. All dimensions and coefficient heights
are unrestricted. -/
theorem exists_large_form_of_independent_rows {n k y : ℕ}
    (p : Fin k → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hy : ∀ j, p j ≤ y) (M : Matrix (Fin (n + 1)) (Fin k) ℤ)
    (hind : LinearIndependent ℚ (fun i j => (M i j : ℚ)))
    {H : ℝ} (hH : 1 ≤ H) (hM : ∀ i j, |(M i j : ℝ)| ≤ H) :
    ∃ i, rankDepthFloor (n + 1) (k - (n + 1)) y H ≤ |primeLogForms M p i| := by
  classical
  obtain ⟨s, hsi, hminor⟩ := HTGeometry.exists_injective_det_submatrix_ne_zero
    (M := M.map (Int.castRingHom ℚ)) hind
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := M.submatrix id s
  have hdet : A.det ≠ 0 := by
    intro hz
    apply hminor
    change ((Int.castRingHom ℚ).mapMatrix A).det = 0
    rw [← (Int.castRingHom ℚ).map_det, hz, map_zero]
  let C := {j : Fin k // j ∉ Set.range s}
  have hscard : Fintype.card (Set.range s) = n + 1 := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (Equiv.ofInjective s hsi)).symm
  have hcard : Fintype.card C = k - (n + 1) := by
    change Fintype.card ↑(Set.range s)ᶜ = _
    rw [Fintype.card_compl_set, hscard, Fintype.card_fin]
  let e : Fin (k - (n + 1)) ≃ C :=
    (Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard)).symm
  let t : Fin (k - (n + 1)) → Fin k := fun j => (e j).val
  have ht : Function.Injective t := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hst : ∀ i j, s i ≠ t j := by
    intro i j hij
    exact (e j).property ⟨i, hij⟩
  let B : Matrix (Fin (n + 1)) (Fin (k - (n + 1))) ℤ := fun i j => M i (t j)
  let q : Fin ((k - (n + 1)) + 1) → ℕ :=
    Fin.cons (p (s 0)) (fun j => p (t j))
  have hq : Function.Injective q :=
    cons_injective _ _ (hp.comp ht) (fun j h => hst 0 j (hp h))
  have hqprime : ∀ j, (q j).Prime := by
    intro j
    exact Fin.cases (hprime (s 0)) (fun j => hprime (t j)) j
  have hqy : ∀ j, q j ≤ y := by
    intro j
    exact Fin.cases (hy (s 0)) (fun j => hy (t j)) j
  let x : Fin (n + 1) → ℝ := fun j => log (p (s j))
  have hx : x 0 = log (q 0) := rfl
  obtain ⟨i, hi⟩ := block_rank_depth A B q hq hqprime hqy x hx hH
    (fun i j => hM i (s j)) (fun i j => hM i (t j)) hdet
  let E : Fin (n + 1) ⊕ Fin (k - (n + 1)) ≃ Fin k :=
    (Equiv.sumCongr (Equiv.ofInjective s hsi) e).trans
      (Equiv.sumCompl (fun j : Fin k => j ∈ Set.range s))
  have hsplit : primeLogForms M p i =
      (((Int.castRingHom ℝ).mapMatrix A).mulVec x +
        (B.map (Int.castRingHom ℝ)).mulVec (fun j => log (q j.succ))) i := by
    have hsum := Fintype.sum_equiv E
      (fun j => (M i (E j) : ℝ) * log (p (E j)))
      (fun j => (M i j : ℝ) * log (p j)) (fun j => rfl)
    rw [Fintype.sum_sum_type] at hsum
    exact hsum.symm
  refine ⟨i, ?_⟩
  rw [hsplit]
  exact hi

/-- The approximation body below the collective depth floor cannot contain
an independent family of the specified rank. -/
theorem not_independent_of_small_forms {n k y : ℕ}
    (p : Fin k → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hy : ∀ j, p j ≤ y) (M : Matrix (Fin (n + 1)) (Fin k) ℤ)
    {H : ℝ} (hH : 1 ≤ H) (hM : ∀ i j, |(M i j : ℝ)| ≤ H)
    (hsmall : ∀ i, |primeLogForms M p i| < rankDepthFloor (n + 1) (k - (n + 1)) y H) :
    ¬ LinearIndependent ℚ (fun i j => (M i j : ℚ)) := by
  intro hind
  obtain ⟨i, hi⟩ := exists_large_form_of_independent_rows p hp hprime hy M hind hH hM
  exact (not_lt_of_ge hi) (hsmall i)

/-- At penultimate rank the scalar exponent involves exactly two logarithms,
independently of how many prime coordinates are present. -/
theorem penultimate_rank_depth {n y : ℕ}
    (p : Fin (n + 2) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hy : ∀ j, p j ≤ y) (M : Matrix (Fin (n + 1)) (Fin (n + 2)) ℤ)
    (hind : LinearIndependent ℚ (fun i j => (M i j : ℚ)))
    {H : ℝ} (hH : 1 ≤ H) (hM : ∀ i j, |(M i j : ℝ)| ≤ H) :
    ∃ i, rankDepthFloor (n + 1) 1 y H ≤ |primeLogForms M p i| := by
  simpa only [show n + 2 - (n + 1) = 1 by omega] using
    exists_large_form_of_independent_rows p hp hprime hy M hind hH hM

/-- Integer near relations in a coefficient box. The form condition is strict
so boundary points at the collective depth floor are excluded. -/
def nearRelationBox {k : ℕ} (p : Fin k → ℕ) (H : ℕ) (ε : ℝ) :
    Finset (Fin k → ℤ) := by
  classical
  exact (HTGeometry.integerCoordinateBox (Fin k) H).filter
    (fun ν => |primeLogForm p ν| < ε)

theorem mem_nearRelationBox {k : ℕ} (p : Fin k → ℕ) (H : ℕ) (ε : ℝ) (ν : Fin k → ℤ) :
    ν ∈ nearRelationBox p H ε ↔
      (∀ j, |ν j| ≤ (H : ℤ)) ∧ |primeLogForm p ν| < ε := by
  classical
  simp only [nearRelationBox, Finset.mem_filter, HTGeometry.integerCoordinateBox,
    Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- A basis chosen from the near relations cannot contain a forbidden independent family. -/
private theorem small_forms_span_finrank_le {n k y : ℕ}
    (p : Fin k → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hy : ∀ j, p j ≤ y) (S : Finset (Fin k → ℤ)) {H : ℝ} (hH : 1 ≤ H)
    (hheight : ∀ ν ∈ S, ∀ j, |(ν j : ℝ)| ≤ H)
    (hsmall : ∀ ν ∈ S, |primeLogForm p ν| < rankDepthFloor (n + 1) (k - (n + 1)) y H) :
    Module.finrank ℚ (Submodule.span ℚ
      (↑(S.image HTGeometry.intVectorToRat) : Set (Fin k → ℚ))) ≤ n := by
  classical
  let T : Set (Fin k → ℚ) := ↑(S.image HTGeometry.intVectorToRat)
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent ℚ T
  have hbfin : b.Finite := (S.image HTGeometry.intVectorToRat).finite_toSet.subset hbsub
  letI : Fintype b := hbfin.fintype
  have hdim : Module.finrank ℚ (Submodule.span ℚ T) = Fintype.card b := by
    have h := finrank_span_eq_card hbind
    rw [Subtype.range_coe, hbspan] at h
    exact h
  by_contra hdimle
  have hcard : n + 1 ≤ Fintype.card b := by
    rw [← hdim]
    exact Nat.succ_le_of_lt (lt_of_not_ge hdimle)
  let f : Fin (n + 1) → b := fun i =>
    (Fintype.equivFin b).symm ⟨i.val, lt_of_lt_of_le i.isLt hcard⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have h := congrArg (fun v : b => (Fintype.equivFin b v).val) hij
    simpa only [f, Equiv.apply_symm_apply] using h
  have hex : ∀ i : Fin (n + 1), ∃ ν ∈ S,
      HTGeometry.intVectorToRat ν = (f i : Fin k → ℚ) := by
    intro i
    exact Finset.mem_image.mp (hbsub (f i).property)
  choose M hMs hMeq using hex
  have heq : (fun i j => (M i j : ℚ)) = (Subtype.val ∘ f) := funext hMeq
  have hind : LinearIndependent ℚ (fun i j => (M i j : ℚ)) := by
    rw [heq]
    exact hbind.comp f hf
  obtain ⟨i, hi⟩ := exists_large_form_of_independent_rows p hp hprime hy M hind hH
    (fun i j => hheight (M i) (hMs i) j)
  exact (not_lt_of_ge hi) (hsmall (M i) (hMs i))

/-- Below the collective floor, all near relations lie in a rational
subspace of dimension at most `n`. -/
theorem nearRelationBox_finrank_le {n k y H : ℕ}
    (p : Fin k → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hy : ∀ j, p j ≤ y) (hH : 1 ≤ H) {ε : ℝ}
    (hε : ε ≤ rankDepthFloor (n + 1) (k - (n + 1)) y H) :
    Module.finrank ℚ (Submodule.span ℚ
      (↑((nearRelationBox p H ε).image HTGeometry.intVectorToRat) : Set (Fin k → ℚ))) ≤ n := by
  apply small_forms_span_finrank_le (H := (H : ℝ)) p hp hprime hy (nearRelationBox p H ε)
    (by exact_mod_cast hH)
  · intro ν hν j
    have h := ((mem_nearRelationBox p H ε ν).mp hν).1 j
    exact_mod_cast h
  · intro ν hν
    exact (((mem_nearRelationBox p H ε ν).mp hν).2).trans_le hε

/-- A uniform count for all small integer forms, not only a bound for the
smallest form. Rank `n+1` exclusion reduces the coefficient-box exponent to `n`. -/
theorem nearRelationBox_card_le {n k y H : ℕ}
    (p : Fin k → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hy : ∀ j, p j ≤ y) (hH : 1 ≤ H) {ε : ℝ}
    (hε : ε ≤ rankDepthFloor (n + 1) (k - (n + 1)) y H) :
    (nearRelationBox p H ε).card ≤ (2 * H + 1) ^ n := by
  have hc := HTGeometry.card_intVectors_le_pow_finrank_span (nearRelationBox p H ε) H
    (fun ν hν => ((mem_nearRelationBox p H ε ν).mp hν).1)
  refine hc.trans ?_
  exact pow_le_pow_right₀ (by omega)
    (nearRelationBox_finrank_le p hp hprime hy hH hε)
end
end GaloisForLFunctions.CollectiveDiophantineGeometry
