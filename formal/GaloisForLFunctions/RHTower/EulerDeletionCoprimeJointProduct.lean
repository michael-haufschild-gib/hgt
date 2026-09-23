import GaloisForLFunctions.RHTower.EulerDeletionCoprimePolygonSignature
import GaloisForLFunctions.RHTower.EulerDeletionJointProductOneFifth
import Mathlib.Tactic

/-!
# The joint deletion product above one fifth, for every coprime pair of moduli

For coprime `P = p+1` and `Q = q+1`, arbitrary `X, Y` in any complete complex normed unital
algebra, and every complex `s` with `Re s > 1/5`, the literal chronological products

```text
prod_{n=1}^{N} exp (n^(-s) * (a_P(n) X + a_Q(n) Y)),    a_d(n) = 1 - d * [d divides n],
```

converge in algebra norm to a unit.  No zero condition, no commutation of `X` and `Y`, and no
supplied cancellation is assumed.

The block of one full common period has a fifth-order remainder at the origin, because all its
chronological jets through order four vanish: that is the signature theorem of
`EulerDeletionCoprimePolygonSignature`.  Scalar successive variation of the Dirichlet weights makes
the freezing error summable; reversed products of negated exponentials supply two-sided inverse
blocks with summable displacement; exact regrouping and the `P*Q` residue limits recover every
partial prefix, not only the block subsequence.

This generalizes `EulerDeletionJointProductOneFifth` from the actual moduli two and three to every
coprime pair.  Convergence here reaches strictly left of the critical line and holds without a zero
hypothesis, so this admission property alone selects no line and carries no RH implication.
-/

open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionCoprimeProduct
open RHTower.DeletionJointExponential
open GaloisForLFunctions.HTGeometry.NoncommutativeAbel
noncomputable section

section Generic
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- Reverse-ordered product, the two-sided partner of `orderedProduct`. -/
def revProduct (f : ℕ → A) : ℕ → A
  | 0 => 1
  | n+1 => f n * revProduct f n

omit [NormedAlgebra ℂ A] in
theorem orderedProduct_mul_revProduct (f g : ℕ → A) (h : ∀ j, f j * g j = 1) (n : ℕ) :
    orderedProduct f n * revProduct g n = 1 := by
  induction n with
  | zero => simp [orderedProduct, revProduct]
  | succ n ih =>
    show (orderedProduct f n * f n) * (g n * revProduct g n) = 1
    rw [mul_assoc, ← mul_assoc (f n), h n, one_mul, ih]

omit [NormedAlgebra ℂ A] in
theorem revProduct_mul_orderedProduct (f g : ℕ → A) (h : ∀ j, g j * f j = 1) (n : ℕ) :
    revProduct g n * orderedProduct f n = 1 := by
  induction n with
  | zero => simp [orderedProduct, revProduct]
  | succ n ih =>
    show (g n * revProduct g n) * (orderedProduct f n * f n) = 1
    rw [mul_assoc, ← mul_assoc (revProduct g n), ih, one_mul, h n]

omit [NormedAlgebra ℂ A] in
theorem orderedProduct_congr {f g : ℕ → A} {n : ℕ} (h : ∀ j, j < n → f j = g j) :
    orderedProduct f n = orderedProduct g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show orderedProduct f n * f n = orderedProduct g n * g n
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

omit [NormedAlgebra ℂ A] in
theorem listProd_range_eq_orderedProduct (g : ℕ → A) (n : ℕ) :
    ((List.range n).map g).prod = orderedProduct g n := by
  induction n with
  | zero => simp [orderedProduct]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp [orderedProduct]

omit [NormedAlgebra ℂ A] in
theorem tendsto_revProduct {ι : Type*} {l : Filter ι} (F : ι → ℕ → A) (m : ℕ)
    (h : ∀ j, Tendsto (fun i => F i j) l (nhds 1)) :
    Tendsto (fun i => revProduct (F i) m) l (nhds 1) := by
  induction m with
  | zero => simpa [revProduct] using tendsto_const_nhds (x := (1:A))
  | succ m ih => simpa [revProduct] using (h m).mul ih

omit [NormedAlgebra ℂ A] in
theorem tendsto_orderedProduct {ι : Type*} {l : Filter ι} (F : ι → ℕ → A) (m : ℕ)
    (h : ∀ j, Tendsto (fun i => F i j) l (nhds 1)) :
    Tendsto (fun i => orderedProduct (F i) m) l (nhds 1) := by
  induction m with
  | zero => simpa [orderedProduct] using tendsto_const_nhds (x := (1:A))
  | succ m ih =>
    have : Tendsto (fun i => orderedProduct (F i) m * F i m) l (nhds ((1:A)*1)) := ih.mul (h m)
    simpa [orderedProduct] using this

end Generic

section Strides
variable {L : ℕ}

theorem stride_tendsto (hL : 0 < L) (c : ℕ) : Tendsto (fun k : ℕ => L*k+c) atTop atTop := by
  refine tendsto_atTop_mono (fun k => ?_) tendsto_id
  exact le_trans (Nat.le_mul_of_pos_left k hL) (Nat.le_add_right _ _)

theorem summable_stride_difference (hL : 0 < L) {w : ℕ → ℂ}
    (hw : Summable (fun n => ‖w n - w (n+1)‖)) (c : ℕ) :
    Summable (fun k => ‖w (L*k+c) - w (L*k)‖) := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hinj : Function.Injective (fun k : ℕ => L*k+c) := by
      intro a b hab
      dsimp only at hab
      exact Nat.eq_of_mul_eq_mul_left hL (by omega)
    have hstep : Summable (fun k => ‖w (L*k+(c+1)) - w (L*k+c)‖) := by
      have h := hw.comp_injective hinj
      exact h.congr (fun k => by simp only [Function.comp_def, Nat.add_assoc, norm_sub_rev])
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k =>
      norm_sub_le_norm_sub_add_norm_sub (w (L*k+(c+1))) (w (L*k+c)) (w (L*k))) (hstep.add ih)

/-- The actual weights inside one block. -/
def blockWeights (L : ℕ) (w : ℕ → ℂ) (k : ℕ) : Fin L → ℂ := fun j => w (L*k+j)

/-- One frozen weight per block. -/
def frozenWeights (L : ℕ) (w : ℕ → ℂ) (k : ℕ) : Fin L → ℂ := fun _ => w (L*k)

theorem summable_block_input_error (hL : 0 < L) {w : ℕ → ℂ}
    (hw : Summable (fun n => ‖w n - w (n+1)‖)) :
    Summable (fun k => ‖blockWeights L w k - frozenWeights L w k‖) := by
  have h : Summable (fun k => ∑ j : Fin L, ‖w (L*k+j) - w (L*k)‖) :=
    summable_sum (fun j _ => summable_stride_difference hL hw j)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ h
  intro k
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).2
  intro j
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem blockWeights_tendsto (hL : 0 < L) {w : ℕ → ℂ} (hw : Tendsto w atTop (nhds 0)) :
    Tendsto (blockWeights L w) atTop (nhds 0) := by
  apply tendsto_pi_nhds.2
  intro j
  exact hw.comp (stride_tendsto hL j)

theorem frozenWeights_tendsto (hL : 0 < L) {w : ℕ → ℂ} (hw : Tendsto w atTop (nhds 0)) :
    Tendsto (frozenWeights L w) atTop (nhds 0) := by
  apply tendsto_pi_nhds.2
  intro j
  simpa only [Nat.add_zero, Function.comp_def, frozenWeights, Pi.zero_apply] using
    hw.comp (stride_tendsto hL 0)

end Strides

section Block
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Coordinate extension of a finite weight vector by zero. -/
def extend (L : ℕ) (u : Fin L → ℂ) (j : ℕ) : ℂ := if h : j < L then u ⟨j, h⟩ else 0

theorem extend_of_lt {L : ℕ} (u : Fin L → ℂ) {j : ℕ} (h : j < L) :
    extend L u j = u ⟨j, h⟩ := dif_pos h

theorem extend_of_not_lt {L : ℕ} (u : Fin L → ℂ) {j : ℕ} (h : ¬ j < L) :
    extend L u j = 0 := dif_neg h

/-- The literal chronological block, each factor carrying its own weight. -/
def variableBlock (P Q L : ℕ) (X Y : A) (u : Fin L → ℂ) : A :=
  orderedProduct (fun j => NormedSpace.exp (extend L u j • sourceVelocity P Q j X Y)) L

/-- The reversed product of negated exponentials, the two-sided inverse block. -/
def inverseBlock (P Q L : ℕ) (X Y : A) (u : Fin L → ℂ) : A :=
  revProduct (fun j => NormedSpace.exp (-(extend L u j • sourceVelocity P Q j X Y))) L

theorem variableBlock_inverse_pair (P Q L : ℕ) (X Y : A) (u : Fin L → ℂ) :
    variableBlock P Q L X Y u * inverseBlock P Q L X Y u = 1 ∧
    inverseBlock P Q L X Y u * variableBlock P Q L X Y u = 1 := by
  haveI : NormedAlgebra ℝ A := .restrictScalars ℝ ℂ A
  exact ⟨orderedProduct_mul_revProduct _ _ (fun _ => exp_mul_neg _) L,
    revProduct_mul_orderedProduct _ _ (fun _ => exp_neg_mul _) L⟩

theorem analytic_variableBlock (P Q L : ℕ) (X Y : A) :
    AnalyticAt ℂ (variableBlock P Q L X Y) 0 := by
  have key : ∀ m : ℕ, AnalyticAt ℂ (fun u : Fin L → ℂ =>
      orderedProduct (fun j => NormedSpace.exp (extend L u j • sourceVelocity P Q j X Y)) m) 0 := by
    intro m
    induction m with
    | zero => exact (analyticAt_const : AnalyticAt ℂ (fun _ : Fin L → ℂ => (1:A)) 0)
    | succ m ih =>
      have hfac : AnalyticAt ℂ (fun u : Fin L → ℂ =>
          NormedSpace.exp (extend L u m • sourceVelocity P Q m X Y)) 0 := by
        by_cases h : m < L
        · have heq : (fun u : Fin L → ℂ => extend L u m • sourceVelocity P Q m X Y)
              = fun u : Fin L → ℂ => ((ContinuousLinearMap.proj (R := ℂ)
                  (φ := fun _ : Fin L => ℂ) (⟨m, h⟩ : Fin L)).smulRight
                  (sourceVelocity P Q m X Y)) u := by
            funext u
            simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
              extend_of_lt u h]
          have hl : AnalyticAt ℂ (fun u : Fin L → ℂ => extend L u m • sourceVelocity P Q m X Y) 0 := by
            rw [heq]
            exact ContinuousLinearMap.analyticAt _ 0
          exact (NormedSpace.exp_analytic (𝕂 := ℂ)
            (extend L (0 : Fin L → ℂ) m • sourceVelocity P Q m X Y)).comp
            (f := fun u : Fin L → ℂ => extend L u m • sourceVelocity P Q m X Y) hl
        · have heq : (fun u : Fin L → ℂ =>
              NormedSpace.exp (extend L u m • sourceVelocity P Q m X Y)) = fun _ => (1:A) := by
            funext u
            rw [extend_of_not_lt u h, zero_smul, NormedSpace.exp_zero]
          rw [heq]
          exact analyticAt_const
      exact ih.mul hfac
  exact key L

theorem variableBlock_frozen (P Q L : ℕ) (X Y : A) (z : ℂ) :
    variableBlock P Q L X Y (fun _ => z) =
      exponentialWord ((List.range L).map (fun n => sourceVelocity P Q n X Y)) z := by
  simp only [variableBlock, exponentialWord, List.map_map, Function.comp_def]
  rw [listProd_range_eq_orderedProduct]
  exact orderedProduct_congr (fun j hj => by simp [extend_of_lt _ hj])

theorem inverseBlock_tendsto (P Q L : ℕ) (hL : 0 < L) (X Y : A) {w : ℕ → ℂ}
    (hw : Tendsto w atTop (nhds 0)) :
    Tendsto (fun k => inverseBlock P Q L X Y (blockWeights L w k)) atTop (nhds 1) := by
  refine tendsto_revProduct _ L (fun j => ?_)
  by_cases h : j < L
  · have hcoord : ∀ k, extend L (blockWeights L w k) j = w (L*k+j) := by
      intro k
      rw [extend_of_lt _ h]
      rfl
    have hz : Tendsto
        (fun k => -(extend L (blockWeights L w k) j • sourceVelocity P Q j X Y))
        atTop (nhds (0:A)) := by
      simp only [hcoord]
      simpa only [Function.comp_def, zero_smul, neg_zero] using
        (((hw.comp (stride_tendsto hL j)).smul
          (tendsto_const_nhds (x := sourceVelocity P Q j X Y))).neg)
    simpa only [NormedSpace.exp_zero, Function.comp_def] using
      (NormedSpace.exp_analytic (𝕂 := ℂ) (0:A)).continuousAt.tendsto.comp hz
  · simp only [extend_of_not_lt _ h, zero_smul, neg_zero, NormedSpace.exp_zero]
    exact tendsto_const_nhds

/-- The chronological exponential block of one full common period. -/
def sourceBlock (P Q : ℕ) (X Y : A) : ℂ → A :=
  exponentialWord ((List.range (P*Q)).map (fun n => sourceVelocity P Q n X Y))

/-- A vanishing jet through order four forces a fifth-order analytic remainder. -/
theorem exponentialWord_remainder (vs : List A) (h : ∀ n, 1 ≤ n → n ≤ 4 → jet vs n = 0) :
    (fun z : ℂ => exponentialWord vs z - 1) =O[nhds 0] (fun z : ℂ => ‖z‖^(5 : ℕ)) := by
  obtain ⟨pS, hpS⟩ := analytic_exponentialWord vs 0
  obtain ⟨r, hr⟩ := hpS
  have hp : HasFPowerSeriesAt (exponentialWord vs) pS 0 := ⟨r, hr⟩
  have hterm (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 4) (z : ℂ) : pS n (fun _ => z) = 0 := by
    have h0 := hr.factorial_smul z n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      iteratedDeriv_exponentialWord_zero, h n hn hn', smul_zero] at h0
    have hc : (n.factorial : ℂ) • pS n (fun _ => z) = 0 := by
      simpa only [Nat.cast_smul_eq_nsmul] using h0
    exact (smul_eq_zero.mp hc).resolve_left (by exact_mod_cast n.factorial_ne_zero)
  have hpartial (z : ℂ) : pS.partialSum 5 z = 1 := by
    unfold FormalMultilinearSeries.partialSum
    rw [Finset.sum_eq_single 0]
    · simpa only [exponentialWord_zero] using hp.coeff_zero (fun _ => z)
    · intro n hn hn0
      exact hterm n (by omega) (by have := Finset.mem_range.mp hn; omega) z
    · simp
  have hbig := hp.isBigO_sub_partialSum_pow 5
  simpa only [zero_add, hpartial] using hbig

/-- The actual coprime-period block has a fifth-order remainder at the origin. -/
theorem sourceBlock_remainder {p q : ℕ} (hpq : (p+1).Coprime (q+1)) (X Y : A) :
    (fun z : ℂ => sourceBlock (p+1) (q+1) X Y z - 1) =O[nhds 0] (fun z : ℂ => ‖z‖^(5 : ℕ)) :=
  exponentialWord_remainder _ (fun n hn hn' =>
    RHTower.DeletionPolygonSignature.jet_sourceVelocity_eq_zero hpq X Y n hn hn')

end Block

section Convergence
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem orderedProduct_add (f : ℕ → A) (m n : ℕ) :
    orderedProduct f (m+n) = orderedProduct f m * orderedProduct (fun j => f (m+j)) n := by
  induction n with
  | zero => simp [orderedProduct]
  | succ n ih =>
    show orderedProduct f (m+n) * f (m+n) =
      orderedProduct f m * (orderedProduct (fun j => f (m+j)) n * f (m+n))
    rw [ih, mul_assoc]

theorem summable_frozen_block_error {p q : ℕ} (hpq : (p+1).Coprime (q+1)) (X Y : A)
    {s : ℂ} (hs : (1:ℝ)/5 < s.re) :
    Summable (fun k => ‖sourceBlock (p+1) (q+1) X Y
      (arithmeticDirichletWeight s ((p+1)*(q+1)*k)) - 1‖) := by
  have hspos : 0 < s.re := by linarith
  have hL : 0 < (p+1)*(q+1) := by positivity
  have hw : Tendsto (fun k => arithmeticDirichletWeight s ((p+1)*(q+1)*k)) atTop (nhds 0) := by
    simpa only [Nat.add_zero, Function.comp_def] using
      (arithmeticDirichletWeight_tendsto_zero hspos).comp (stride_tendsto hL 0)
  have hsum := (DeletionJointProduct.summable_weight_fifth hs).comp_injective
    (show Function.Injective (fun k : ℕ => (p+1)*(q+1)*k) by
      intro a b hab
      exact Nat.eq_of_mul_eq_mul_left hL hab)
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (sourceBlock_remainder hpq X Y)
  apply Summable.of_norm_bounded_eventually_nat (hsum.mul_left C)
  filter_upwards [hw.eventually hC] with k hk
  simpa only [Function.comp_def, norm_pow, norm_norm] using hk

theorem summable_actual_block_error {p q : ℕ} (hpq : (p+1).Coprime (q+1)) (X Y : A)
    {s : ℂ} (hs : (1:ℝ)/5 < s.re) :
    Summable (fun k => ‖variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
      (blockWeights ((p+1)*(q+1)) (arithmeticDirichletWeight s) k) - 1‖) := by
  have hspos : 0 < s.re := by linarith
  have hL : 0 < (p+1)*(q+1) := by positivity
  have hw := arithmeticDirichletWeight_tendsto_zero hspos
  have hvar := arithmeticDirichletWeight_summable_variation hspos
  have hdiff := DeletionJointProduct.summable_image_error (analytic_variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y).contDiffAt
    (blockWeights_tendsto hL hw) (frozenWeights_tendsto hL hw) (summable_block_input_error hL hvar)
  have hfrozen : Summable (fun k =>
      ‖variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
        (frozenWeights ((p+1)*(q+1)) (arithmeticDirichletWeight s) k) - 1‖) := by
    change Summable (fun k => ‖variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
      (fun _ => arithmeticDirichletWeight s ((p+1)*(q+1)*k)) - 1‖)
    simp_rw [variableBlock_frozen]
    exact summable_frozen_block_error hpq X Y hs
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hdiff.add hfrozen)
  intro k
  calc
    _ = ‖(variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
            (blockWeights ((p+1)*(q+1)) (arithmeticDirichletWeight s) k) -
          variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
            (frozenWeights ((p+1)*(q+1)) (arithmeticDirichletWeight s) k)) +
          (variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
            (frozenWeights ((p+1)*(q+1)) (arithmeticDirichletWeight s) k) - 1)‖ := by
      congr 1
      abel
    _ ≤ _ := norm_add_le _ _

theorem actual_blocks_converge_to_unit [NormOneClass A] {p q : ℕ}
    (hpq : (p+1).Coprime (q+1)) (X Y : A) {s : ℂ} (hs : (1:ℝ)/5 < s.re) :
    ∃ U : A, IsUnit U ∧ Tendsto
      (orderedProduct (fun k => variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
        (blockWeights ((p+1)*(q+1)) (arithmeticDirichletWeight s) k)))
      atTop (nhds U) := by
  have hL : 0 < (p+1)*(q+1) := by positivity
  set f := fun k => variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
    (blockWeights ((p+1)*(q+1)) (arithmeticDirichletWeight s) k) with hf_def
  set g := fun k => inverseBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
    (blockWeights ((p+1)*(q+1)) (arithmeticDirichletWeight s) k) with hg_def
  have hf : Summable (fun k => ‖f k - 1‖) := summable_actual_block_error hpq X Y hs
  have hg : Tendsto g atTop (nhds 1) := inverseBlock_tendsto _ _ _ hL X Y
    (arithmeticDirichletWeight_tendsto_zero (by linarith))
  obtain ⟨M, hM⟩ := hg.norm.bddAbove_range
  have hsumg : Summable (fun k => ‖g k - 1‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hf.mul_left (max M 0))
    intro k
    have hgf : g k * f k = 1 := (variableBlock_inverse_pair _ _ _ X Y _).2
    calc
      ‖g k - 1‖ = ‖g k*(1 - f k)‖ := by rw [mul_sub, mul_one, hgf]
      _ ≤ ‖g k‖*‖1 - f k‖ := norm_mul_le _ _
      _ ≤ max M 0 * ‖f k - 1‖ := by
        rw [norm_sub_rev (1:A) (f k)]
        exact mul_le_mul_of_nonneg_right
          ((hM (Set.mem_range_self k)).trans (le_max_left M 0)) (norm_nonneg _)
  exact orderedProduct_converges_to_unit hf hsumg
    (fun k => (variableBlock_inverse_pair _ _ _ X Y _).1)
    (fun k => (variableBlock_inverse_pair _ _ _ X Y _).2)

theorem sourceVelocity_stride (p q : ℕ) (X Y : A) (k j : ℕ) :
    sourceVelocity (p+1) (q+1) ((p+1)*(q+1)*k+j) X Y = sourceVelocity (p+1) (q+1) j X Y := by
  have hP : blockDeletionCoefficient (p+1) ((p+1)*(q+1)*k+j+1)
      = blockDeletionCoefficient (p+1) (j+1) := by
    have h := (DeletionCoprimeWords.shifted_deletion_periodic (p+1)).nat_mul ((q+1)*k) j
    simp only [Nat.cast_id] at h
    convert h using 3
    ring
  have hQ : blockDeletionCoefficient (q+1) ((p+1)*(q+1)*k+j+1)
      = blockDeletionCoefficient (q+1) (j+1) := by
    have h := (DeletionCoprimeWords.shifted_deletion_periodic (q+1)).nat_mul ((p+1)*k) j
    simp only [Nat.cast_id] at h
    convert h using 3
    ring
  simp only [sourceVelocity, hP, hQ]

/-- The actual chronological exponential factors with one-based Dirichlet weights. -/
def sourceFactor (P Q : ℕ) (X Y : A) (s : ℂ) (n : ℕ) : A :=
  NormedSpace.exp (arithmeticDirichletWeight s n • sourceVelocity P Q n X Y)

theorem sourceFactor_block (p q : ℕ) (X Y : A) (s : ℂ) (k : ℕ) :
    orderedProduct (fun j => sourceFactor (p+1) (q+1) X Y s ((p+1)*(q+1)*k+j)) ((p+1)*(q+1)) =
      variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
        (blockWeights ((p+1)*(q+1)) (arithmeticDirichletWeight s) k) := by
  rw [variableBlock]
  refine orderedProduct_congr (fun j hj => ?_)
  rw [sourceFactor, sourceVelocity_stride, extend_of_lt _ hj]
  rfl

theorem sourceProduct_block_mul (p q : ℕ) (X Y : A) (s : ℂ) (k : ℕ) :
    orderedProduct (sourceFactor (p+1) (q+1) X Y s) ((p+1)*(q+1)*k) =
      orderedProduct (fun k => variableBlock (p+1) (q+1) ((p+1)*(q+1)) X Y
        (blockWeights ((p+1)*(q+1)) (arithmeticDirichletWeight s) k)) k := by
  induction k with
  | zero => simp [orderedProduct]
  | succ k ih =>
    rw [Nat.mul_succ, orderedProduct_add, ih, sourceFactor_block]
    rfl

theorem sourceFactor_stride_tendsto (p q : ℕ) (X Y : A) {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    Tendsto (fun k => sourceFactor (p+1) (q+1) X Y s ((p+1)*(q+1)*k+j)) atTop (nhds 1) := by
  have hL : 0 < (p+1)*(q+1) := by positivity
  have hz : Tendsto (fun k => arithmeticDirichletWeight s ((p+1)*(q+1)*k+j) •
      sourceVelocity (p+1) (q+1) j X Y) atTop (nhds (0:A)) := by
    simpa only [Function.comp_def, zero_smul] using
      ((arithmeticDirichletWeight_tendsto_zero hs).comp (stride_tendsto hL j)).smul
        (tendsto_const_nhds (x := sourceVelocity (p+1) (q+1) j X Y))
  have heq : ∀ k, sourceFactor (p+1) (q+1) X Y s ((p+1)*(q+1)*k+j) =
      NormedSpace.exp (arithmeticDirichletWeight s ((p+1)*(q+1)*k+j) •
        sourceVelocity (p+1) (q+1) j X Y) := by
    intro k
    rw [sourceFactor, sourceVelocity_stride]
  simp only [heq]
  simpa only [Function.comp_def, NormedSpace.exp_zero] using
    (NormedSpace.exp_analytic (𝕂 := ℂ) (0:A)).continuousAt.tendsto.comp hz

theorem unfinishedBlock_tendsto (p q : ℕ) (X Y : A) {s : ℂ} (hs : 0 < s.re) (r : ℕ) :
    Tendsto (fun k => orderedProduct
      (fun j => sourceFactor (p+1) (q+1) X Y s ((p+1)*(q+1)*k+j)) r) atTop (nhds 1) :=
  tendsto_orderedProduct _ r (fun j => sourceFactor_stride_tendsto p q X Y hs j)

private theorem tendsto_of_residues {L : ℕ} (hL : 0 < L) {f : ℕ → A} {U : A}
    (h : ∀ r : Fin L, Tendsto (fun k => f (L*k+r)) atTop (nhds U)) :
    Tendsto f atTop (nhds U) := by
  rw [Filter.tendsto_def]
  intro S hS
  have he : ∀ᶠ k in atTop, ∀ r : Fin L, f (L*k+r) ∈ S :=
    Filter.eventually_all.2 (fun r => (h r).eventually hS)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 he
  apply Filter.eventually_atTop.2
  refine ⟨L*K, ?_⟩
  intro N hN
  have hk : K ≤ N/L := (Nat.le_div_iff_mul_le hL).2 (by rw [Nat.mul_comm]; exact hN)
  have hr : N%L < L := Nat.mod_lt N hL
  have heq : L*(N/L)+N%L = N := Nat.div_add_mod N L
  simpa only [heq] using hK (N/L) hk (⟨N%L, hr⟩ : Fin L)

/-- The literal joint deletion product for an arbitrary coprime pair of moduli greater
than one converges to a unit throughout `Re s > 1/5`.  No zero condition and no
commutativity or cancellation premise is supplied. -/
theorem sourceProduct_converges_to_unit [NormOneClass A] {p q : ℕ}
    (hpq : (p+1).Coprime (q+1)) (X Y : A) {s : ℂ} (hs : (1:ℝ)/5 < s.re) :
    ∃ U : A, IsUnit U ∧
      Tendsto (orderedProduct (sourceFactor (p+1) (q+1) X Y s)) atTop (nhds U) := by
  have hL : 0 < (p+1)*(q+1) := by positivity
  obtain ⟨U, hunit, hU⟩ := actual_blocks_converge_to_unit hpq X Y hs
  refine ⟨U, hunit, tendsto_of_residues hL (fun r => ?_)⟩
  have hb : Tendsto (fun k => orderedProduct (sourceFactor (p+1) (q+1) X Y s)
      ((p+1)*(q+1)*k)) atTop (nhds U) := by
    simpa only [sourceProduct_block_mul] using hU
  have hh := hb.mul (unfinishedBlock_tendsto p q X Y (by linarith : 0 < s.re) r)
  simpa only [← orderedProduct_add, mul_one] using hh

end Convergence

end
end RHTower.DeletionCoprimeProduct
