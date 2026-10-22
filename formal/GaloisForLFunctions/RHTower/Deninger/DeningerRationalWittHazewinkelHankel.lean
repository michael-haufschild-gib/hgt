import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelHankelDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittSource

/-!
# Rational Witt vectors and sharp nilpotent Hankel bounds

This module formalizes Deninger's Proposition 2.1(a) and the kernel-rank core of
Proposition 2.10.  It proves directly, over every commutative ring:

* a normalized rational series satisfies an explicit eventual linear recurrence;
* that recurrence factors every sufficiently large Hankel minor through a rectangular matrix;
* every rational Witt vector therefore has finite Hankel rank;
* if `ker(f)^k = 0`, every big-Witt vector mapping to `1` has Hankel rank at most `k`;
* consequently `W(I) = W_J(I) = W_J^{≤k}(I)` for `I = ker(f)`.

No domain, reducedness, torsion-freeness, characteristic-zero, or decidable ring-equality
assumption is used.  The sharp kernel bound is proved from the Leibniz formula, retaining the
single possible constant Hankel entry and forcing the other `k` factors into the nilpotent ideal.
-/

namespace RHTower
noncomputable section
open scoped BigOperators

variable {A : Type*} [CommRing A]

theorem det_rectangular_factor_succ_eq_zero (d : ℕ)
    (U : Matrix (Fin (d + 1)) (Fin d) A)
    (V : Matrix (Fin d) (Fin (d + 1)) A) :
    (U * V).det = 0 := by
  let U' : Matrix (Fin (d + 1)) (Fin (d + 1)) A := fun i j =>
    if h : j.val < d then U i ⟨j.val, h⟩ else 0
  let V' : Matrix (Fin (d + 1)) (Fin (d + 1)) A := fun i j =>
    if h : i.val < d then V ⟨i.val, h⟩ j else 0
  have hmul : U' * V' = U * V := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp [U', V']
  rw [← hmul, Matrix.det_mul]
  have hdet : U'.det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero (Fin.last d)
    intro i
    simp [U']
  rw [hdet, zero_mul]

def DeningerHankelColumnGenerated (a : ℕ → A) (d : ℕ) : Prop :=
  ∀ j : ℕ, ∃ c : Fin d → A, ∀ i : ℕ,
    a (i + j) = ∑ t : Fin d, a (i + t.val) * c t

theorem hankelRankLT_succ_of_columnGenerated (a : ℕ → A) (d : ℕ)
    (h : DeningerHankelColumnGenerated a d) :
    ∀ rows cols : Fin (d + 1) → ℕ,
      (Matrix.submatrix (fun i j => a (i + j)) rows cols).det = 0 := by
  intro rows cols
  choose c hc using fun j : Fin (d + 1) => h (cols j)
  let U : Matrix (Fin (d + 1)) (Fin d) A := fun i t => a (rows i + t.val)
  let V : Matrix (Fin d) (Fin (d + 1)) A := fun t j => c j t
  have hfactor : Matrix.submatrix (fun i j => a (i + j)) rows cols = U * V := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.mul_apply]
    exact hc j (rows i)
  rw [hfactor]
  exact det_rectangular_factor_succ_eq_zero d U V

def DeningerLinearRecurrenceFrom (a q : ℕ → A) (d : ℕ) : Prop :=
  ∀ i j : ℕ, d ≤ j →
    a (i + j) + ∑ t ∈ Finset.Icc 1 d, q t * a (i + (j - t)) = 0

theorem columnGenerated_of_linearRecurrenceFrom
    (a q : ℕ → A) (d : ℕ) (hrec : DeningerLinearRecurrenceFrom a q d) :
    DeningerHankelColumnGenerated a d := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj : j < d
    · let tj : Fin d := ⟨j, hj⟩
      refine ⟨fun t => if t = tj then 1 else 0, ?_⟩
      intro i
      simp [tj]
    · have hdj : d ≤ j := Nat.le_of_not_gt hj
      let s := Finset.Icc 1 d
      have hprev : ∀ t : ↥s, ∃ c : Fin d → A, ∀ i : ℕ,
          a (i + (j - t.val)) = ∑ u : Fin d, a (i + u.val) * c u := by
        intro t
        apply ih (j - t.val)
        have ht : t.val ∈ Finset.Icc 1 d := by simp [s, t.property]
        have htpos : 0 < t.val := (Finset.mem_Icc.mp ht).1
        have htj : 0 < j := htpos.trans_le
          ((Finset.mem_Icc.mp ht).2.trans hdj)
        exact Nat.sub_lt htj htpos
      choose c hc using hprev
      refine ⟨fun u => -∑ t : ↥s, q t.val * c t u, ?_⟩
      intro i
      have hr := hrec i j hdj
      rw [Finset.sum_subtype s (fun _ => Iff.rfl)] at hr
      rw [eq_neg_iff_add_eq_zero.mpr hr]
      change -(∑ t : ↥s, q t.val * a (i + (j - t.val))) = _
      simp_rw [hc]
      simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      funext t
      ac_rfl

theorem linearRecurrenceFrom_of_powerSeries_mul_polynomial
    (F : PowerSeries A) (P Q : Polynomial A) (hQ0 : Q.coeff 0 = 1)
    (hFQ : F * (Q : PowerSeries A) = (P : PowerSeries A)) :
    let d := max (P.natDegree + 1) Q.natDegree
    DeningerLinearRecurrenceFrom (fun n => PowerSeries.coeff n F) Q.coeff d := by
  dsimp only
  intro i j hdj
  let d := max (P.natDegree + 1) Q.natDegree
  let N := i + j
  have hdP : P.natDegree < d := by
    dsimp [d]
    omega
  have hdQ : Q.natDegree ≤ d := by
    exact le_max_right _ _
  have hjN : j ≤ N := by simp [N]
  have hPN : P.coeff N = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hdP.trans_le (hdj.trans hjN))
  have hcoef := congrArg (PowerSeries.coeff N) hFQ
  have hcoef' : PowerSeries.coeff N (F * (Q : PowerSeries A)) = P.coeff N := by
    simpa using hcoef
  have hsum : (∑ t ∈ Finset.range (N + 1),
      Q.coeff t * PowerSeries.coeff (N - t) F) = 0 := by
    rw [← hPN]
    calc
      _ = PowerSeries.coeff N ((Q : PowerSeries A) * F) := by
        rw [PowerSeries.coeff_mul]
        symm
        calc
          _ = ∑ t ∈ Finset.range (N + 1),
              PowerSeries.coeff t (Q : PowerSeries A) *
                PowerSeries.coeff (N - t) F := by
            simpa [Nat.succ_eq_add_one] using
              (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun x y => PowerSeries.coeff x (Q : PowerSeries A) *
                  PowerSeries.coeff y F) N)
          _ = ∑ t ∈ Finset.range (N + 1),
              Q.coeff t * PowerSeries.coeff (N - t) F := by simp
      _ = PowerSeries.coeff N (F * (Q : PowerSeries A)) := by rw [mul_comm]
      _ = P.coeff N := hcoef'
  have hsubset : insert 0 (Finset.Icc 1 d) ⊆ Finset.range (N + 1) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_range] at ht ⊢
    rcases ht with rfl | ht
    · omega
    · omega
  have hrestricted :
      (∑ t ∈ Finset.range (N + 1), Q.coeff t * PowerSeries.coeff (N - t) F) =
        ∑ t ∈ insert 0 (Finset.Icc 1 d),
          Q.coeff t * PowerSeries.coeff (N - t) F := by
    symm
    apply Finset.sum_subset hsubset
    intro t htRange htNot
    have htgt : d < t := by
      simp only [Finset.mem_insert, Finset.mem_Icc, not_or, not_and] at htNot
      have ht0 : t ≠ 0 := htNot.1
      have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
      exact lt_of_not_ge (htNot.2 ht1)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdQ.trans_lt htgt), zero_mul]
  rw [hrestricted] at hsum
  rw [Finset.sum_insert (by simp : 0 ∉ Finset.Icc 1 d)] at hsum
  simp only [hQ0, one_mul, Nat.sub_zero, N] at hsum
  change d ≤ j at hdj
  change PowerSeries.coeff (i + j) F +
    ∑ t ∈ Finset.Icc 1 d,
      Q.coeff t * PowerSeries.coeff (i + (j - t)) F = 0
  calc
    _ = PowerSeries.coeff (i + j) F +
        ∑ t ∈ Finset.Icc 1 d,
          Q.coeff t * PowerSeries.coeff (i + j - t) F := by
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      have htj : t ≤ j := (Finset.mem_Icc.mp ht).2.trans hdj
      rw [Nat.add_sub_assoc htj]
    _ = 0 := hsum

theorem deningerRationalWitt_exists_normalized_powerSeries_fraction
    (w : DeningerRationalWittAdditive A) :
    ∃ P Q : Polynomial A, P.coeff 0 = 1 ∧ Q.coeff 0 = 1 ∧
      deningerBigWittSeries (deningerRationalWittToBigWittAdditive A w) *
          (Q : PowerSeries A) = (P : PowerSeries A) := by
  obtain ⟨P, Q, hQmem, hP, hQ, hwval⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction A w
  refine ⟨P, Q, hP, hQ, ?_⟩
  have hwPQ := hwval
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul] at hwPQ
  have hwPQps := congrArg (deningerRationalWittLocalizationToPowerSeries A) hwPQ
  have hwPQps' : (P : PowerSeries A) =
      deningerRationalWittLocalizationToPowerSeries A (w.1 : _) *
        (Q : PowerSeries A) := by
    simpa [deningerRationalWittLocalizationToPowerSeries,
      IsLocalization.lift_eq] using hwPQps
  change deningerRationalWittLocalizationToPowerSeries A (w.1 : _) *
    (Q : PowerSeries A) = (P : PowerSeries A)
  exact hwPQps'.symm

theorem deningerRationalWittToBigWitt_finiteHankelRank
    (w : DeningerRationalWittAdditive A) :
    DeningerBigWittFiniteHankelRank
      (deningerRationalWittToBigWittAdditive A w) := by
  obtain ⟨P, Q, hP, hQ, hFQ⟩ :=
    deningerRationalWitt_exists_normalized_powerSeries_fraction w
  let d := max (P.natDegree + 1) Q.natDegree
  refine ⟨d + 1, ?_⟩
  intro rows cols
  change (Matrix.submatrix
    (fun i j => PowerSeries.coeff (i + j)
      (deningerBigWittSeries (deningerRationalWittToBigWittAdditive A w)))
      rows cols).det = 0
  let F := deningerBigWittSeries (deningerRationalWittToBigWittAdditive A w)
  have hrec : DeningerLinearRecurrenceFrom
      (fun n => PowerSeries.coeff n F) Q.coeff d :=
    linearRecurrenceFrom_of_powerSeries_mul_polynomial F P Q hQ hFQ
  have hcol : DeningerHankelColumnGenerated
      (fun n => PowerSeries.coeff n F) d :=
    columnGenerated_of_linearRecurrenceFrom _ Q.coeff d hrec
  exact hankelRankLT_succ_of_columnGenerated
    (fun n => PowerSeries.coeff n F) d hcol rows cols

theorem finset_prod_mem_ideal_pow_card_filter
    {ι : Type*} [DecidableEq ι] (I : Ideal A) (s : Finset ι)
    (x : ι → A) (p : ι → Prop) [DecidablePred p]
    (hx : ∀ i ∈ s, p i → x i ∈ I) :
    (∏ i ∈ s, x i) ∈ I ^ (s.filter p).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hpa : p a
      · have hfilter : (insert a s).filter p = insert a (s.filter p) := by
          rw [Finset.filter_insert, if_pos hpa]
        have hafilter : a ∉ s.filter p := fun h =>
          ha (Finset.filter_subset p s h)
        rw [Finset.prod_insert ha, hfilter,
          Finset.card_insert_of_notMem hafilter, pow_succ']
        exact Ideal.mul_mem_mul (hx a (Finset.mem_insert_self a s) hpa)
          (ih fun i hi hpi => hx i (Finset.mem_insert_of_mem hi) hpi)
      · have hfilter : (insert a s).filter p = s.filter p := by
          rw [Finset.filter_insert, if_neg hpa]
        rw [Finset.prod_insert ha, hfilter]
        exact (I ^ (s.filter p).card).mul_mem_left _
          (ih fun i hi hpi => hx i (Finset.mem_insert_of_mem hi) hpi)

theorem hankelMinor_det_mem_ideal_pow
    (a : ℕ → A) (I : Ideal A) (k : ℕ)
    (ha : ∀ n : ℕ, 0 < n → a n ∈ I)
    (rows cols : Fin (k + 1) → ℕ) :
    (Matrix.submatrix (fun i j => a (i + j)) rows cols).det ∈ I ^ k := by
  let M := Matrix.submatrix (fun i j => a (i + j)) rows cols
  by_cases hrows : Function.Injective rows
  · by_cases hcols : Function.Injective cols
    · rw [Matrix.det_apply']
      apply (I ^ k).sum_mem
      intro σ hσ
      let p : Fin (k + 1) → Prop := fun i => 0 < rows (σ i) + cols i
      have hprod : (∏ i : Fin (k + 1), M (σ i) i) ∈
          I ^ ((Finset.univ.filter p).card) := by
        apply finset_prod_mem_ideal_pow_card_filter I Finset.univ
        intro i hi hpi
        exact ha _ hpi
      have hnonpos : (Finset.univ.filter fun i : Fin (k + 1) => ¬ p i).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        have hxsum : rows (σ x) + cols x = 0 :=
          Nat.eq_zero_of_not_pos (Finset.mem_filter.mp hx).2
        have hysum : rows (σ y) + cols y = 0 :=
          Nat.eq_zero_of_not_pos (Finset.mem_filter.mp hy).2
        apply hcols
        omega
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (k + 1)))) p
      have hcard : k ≤ (Finset.univ.filter p).card := by
        simp only [Finset.card_univ, Fintype.card_fin] at hpartition
        omega
      exact (I ^ k).mul_mem_left _ (Ideal.pow_le_pow_right hcard hprod)
    · rw [Function.not_injective_iff] at hcols
      obtain ⟨x, y, hxy, hcol⟩ := hcols
      have hzero : M.det = 0 := by
        apply Matrix.det_zero_of_column_eq hcol
        intro i
        simp [M, Matrix.submatrix_apply, hxy]
      rw [hzero]
      exact (I ^ k).zero_mem
  · rw [Function.not_injective_iff] at hrows
    obtain ⟨x, y, hxy, hrow⟩ := hrows
    have hzero : M.det = 0 := by
      apply Matrix.det_zero_of_row_eq hrow
      funext j
      simp [M, Matrix.submatrix_apply, hxy]
    rw [hzero]
    exact (I ^ k).zero_mem

theorem deningerBigWitt_coeff_mem_ker_of_map_eq_one
    {B : Type*} [CommRing B] (f : A →+* B)
    (w : DeningerBigWittAdditive A)
    (hw : deningerBigWittMap f w = 1) (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n (deningerBigWittSeries w) ∈ RingHom.ker f := by
  rw [RingHom.mem_ker]
  have hs := congrArg deningerBigWittSeries hw
  rw [deningerBigWittSeries_map] at hs
  have hc := congrArg (PowerSeries.coeff n) hs
  rw [PowerSeries.coeff_map] at hc
  simpa [deningerBigWittSeries, PowerSeries.coeff_one, hn.ne'] using hc

theorem DeningerBigWittHankelRankLT.of_map_eq_one_of_ker_pow_eq_bot
    {B : Type*} [CommRing B] (f : A →+* B) (k : ℕ)
    (hker : (RingHom.ker f) ^ k = ⊥)
    (w : DeningerBigWittAdditive A)
    (hw : deningerBigWittMap f w = 1) :
    DeningerBigWittHankelRankLT (k + 1) w := by
  intro rows cols
  have hmem : ((deningerBigWittHankel w).submatrix rows cols).det ∈
      (RingHom.ker f) ^ k := by
    apply hankelMinor_det_mem_ideal_pow
      (fun n => PowerSeries.coeff n (deningerBigWittSeries w))
      (RingHom.ker f) k
    intro n hn
    exact deningerBigWitt_coeff_mem_ker_of_map_eq_one f w hw n hn
  have hbot : ((deningerBigWittHankel w).submatrix rows cols).det ∈
      (⊥ : Ideal A) := by
    rw [← hker]
    exact hmem
  exact hbot

theorem deningerBigWittKernel_eq_hazewinkelKernel
    {B : Type*} [CommRing B] (f : A →+* B) (k : ℕ)
    (hker : (RingHom.ker f) ^ k = ⊥) :
    {w : DeningerBigWittAdditive A | deningerBigWittMap f w = 1} =
      {w : DeningerBigWittAdditive A |
        deningerBigWittMap f w = 1 ∧ DeningerBigWittFiniteHankelRank w} := by
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hw
    exact ⟨hw, k + 1,
      DeningerBigWittHankelRankLT.of_map_eq_one_of_ker_pow_eq_bot f k hker w hw⟩
  · exact fun hw => hw.1

theorem deningerBigWittKernel_eq_hankelRankLEKernel
    {B : Type*} [CommRing B] (f : A →+* B) (k : ℕ)
    (hker : (RingHom.ker f) ^ k = ⊥) :
    {w : DeningerBigWittAdditive A | deningerBigWittMap f w = 1} =
      {w : DeningerBigWittAdditive A |
        deningerBigWittMap f w = 1 ∧ DeningerBigWittHankelRankLT (k + 1) w} := by
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hw
    exact ⟨hw,
      DeningerBigWittHankelRankLT.of_map_eq_one_of_ker_pow_eq_bot f k hker w hw⟩
  · exact fun hw => hw.1

/-- Deninger Proposition 2.10(1): the Hazewinkel map is onto across a nilpotent
kernel, and its ambient kernel is exactly both the finite-rank and rank-at-most-`k` kernel. -/
theorem deningerHazewinkelWitt_nilpotentKernel_exact
    {B : Type*} [CommRing B] (f : A →+* B) (hf : Function.Surjective f)
    (k : ℕ) (hker : (RingHom.ker f) ^ k = ⊥) :
    Function.Surjective (deningerHazewinkelWittMap f) ∧
      {w : DeningerBigWittAdditive A | deningerBigWittMap f w = 1} =
        {w : DeningerBigWittAdditive A |
          deningerBigWittMap f w = 1 ∧ DeningerBigWittFiniteHankelRank w} ∧
      {w : DeningerBigWittAdditive A | deningerBigWittMap f w = 1} =
        {w : DeningerBigWittAdditive A |
          deningerBigWittMap f w = 1 ∧ DeningerBigWittHankelRankLT (k + 1) w} := by
  exact ⟨deningerHazewinkelWitt_formally_smooth f hf k hker,
    deningerBigWittKernel_eq_hazewinkelKernel f k hker,
    deningerBigWittKernel_eq_hankelRankLEKernel f k hker⟩

/-- Deninger Proposition 2.10(2), specialized to the quotient by the nilradical. -/
theorem deningerHazewinkelWitt_nilradical_exact
    (k : ℕ) (hnil : (nilradical A) ^ k = ⊥) :
    Function.Surjective
        (deningerHazewinkelWittMap (Ideal.Quotient.mk (nilradical A))) ∧
      {w : DeningerBigWittAdditive A |
          deningerBigWittMap (Ideal.Quotient.mk (nilradical A)) w = 1} =
        {w : DeningerBigWittAdditive A |
          deningerBigWittMap (Ideal.Quotient.mk (nilradical A)) w = 1 ∧
            DeningerBigWittFiniteHankelRank w} ∧
      {w : DeningerBigWittAdditive A |
          deningerBigWittMap (Ideal.Quotient.mk (nilradical A)) w = 1} =
        {w : DeningerBigWittAdditive A |
          deningerBigWittMap (Ideal.Quotient.mk (nilradical A)) w = 1 ∧
            DeningerBigWittHankelRankLT (k + 1) w} := by
  apply deningerHazewinkelWitt_nilpotentKernel_exact
    (Ideal.Quotient.mk (nilradical A)) Ideal.Quotient.mk_surjective k
  simpa only [Ideal.mk_ker] using hnil

end
end RHTower
