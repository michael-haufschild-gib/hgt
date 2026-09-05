import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleCrossDomain

/-!
# Coprime Euler-deletion cross completion

For coprime positive moduli p and q, the literal chronological cross sum of
(1-p[p divides n]) n^(-s) and (1-q[q divides n]) n^(-t) converges when both
real parts are positive. No sum-of-real-parts bound, zeta zero, continuation,
rearrangement, or counterterm is required.

The outer Abel prefix is n mod q. Chinese remaindering proves that its product
with the inner deletion coefficient has zero complete-period sum. A second
Abel summation retains this cancellation instead of estimating it absolutely.
The remaining increment term is absolutely summable.

This is a source-completion theorem, not a critical-line selection law. It does
not apply to two equal nontrivial moduli and does not identify higher histories.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace RHTower.DeletionChronologicalLimit

/-- Zero complete-period mass bounds every chronological coefficient prefix. -/
theorem periodic_zero_sum_prefix_bound {f : ℕ → ℂ} {d : ℕ}
    (hd : 0 < d) (hf : Function.Periodic f d)
    (hzero : ∑ n ∈ Finset.range d, f n = 0) :
    ∃ C : ℝ, ∀ N, ‖∑ n ∈ Finset.range N, f n‖ ≤ C := by
  let S (N : ℕ) := ∑ n ∈ Finset.range N, f n
  have hS : Function.Periodic S d := by
    intro N
    dsimp [S]
    rw [Nat.add_comm N d, Finset.sum_range_add, hzero, zero_add]
    exact Finset.sum_congr rfl (fun n _ => by simpa [Nat.add_comm] using hf n)
  obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun n : Fin d => ‖S n‖)
  refine ⟨C, fun N => ?_⟩
  change ‖S N‖ ≤ C
  rw [← hS.map_mod_nat N]
  exact hC ⟨⟨N % d, Nat.mod_lt N hd⟩, rfl⟩

/-- The literal outer Abel prefix is the residue of the current integer. -/
def coprimeAbelCoefficient (p q n : ℕ) : ℂ :=
  (blockDeletionCoefficient p n : ℂ) * ((n % q : ℕ) : ℂ)

theorem coprimeAbelCoefficient_periodic (p q : ℕ) :
    Function.Periodic (coprimeAbelCoefficient p q) (p*q) := by
  intro n
  have hd : p ∣ n + p*q ↔ p ∣ n := by
    simpa [Nat.add_comm] using (Nat.dvd_add_right (dvd_mul_right p q) :
      p ∣ p*q+n ↔ p ∣ n)
  simp [coprimeAbelCoefficient, blockDeletionCoefficient, hd, Nat.add_mod]

private theorem finEquiv_eq_natCast (d : ℕ) [NeZero d] (n : Fin d) :
    ZMod.finEquiv d n = (n.val : ZMod d) := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d =>
    apply Fin.ext
    change n.val = n.val % (d+1)
    exact (Nat.mod_eq_of_lt n.isLt).symm

theorem coprimeAbelCoefficient_period_sum_zero {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q) :
    ∑ n ∈ Finset.range (p*q), coprimeAbelCoefficient p q n = 0 := by
  letI : NeZero p := ⟨hp.ne'⟩
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero (p*q) := ⟨(Nat.mul_pos hp hq).ne'⟩
  let G (x : ZMod p × ZMod q) : ℂ :=
    (1 - (p : ℂ) * if x.1 = 0 then 1 else 0) * (x.2.val : ℂ)
  let e : Fin (p*q) ≃ ZMod p × ZMod q :=
    (ZMod.finEquiv (p*q)).toEquiv.trans (ZMod.chineseRemainder hpq).toEquiv
  have he (n : Fin (p*q)) :
      G (e n) = coprimeAbelCoefficient p q n := by
    change G (ZMod.chineseRemainder hpq (ZMod.finEquiv (p*q) n)) = _
    rw [finEquiv_eq_natCast, map_natCast]
    change (1 - (p : ℂ) * if (n.val : ZMod p) = 0 then 1 else 0) *
      ((n.val : ZMod q).val : ℂ) = _
    rw [ZMod.val_natCast]
    simp [coprimeAbelCoefficient, blockDeletionCoefficient,
      ZMod.natCast_eq_zero_iff]
  calc
    _ = ∑ n : Fin (p*q), coprimeAbelCoefficient p q n :=
      (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ n : Fin (p*q), G (e n) := Finset.sum_congr rfl (fun n _ => (he n).symm)
    _ = ∑ x : ZMod p × ZMod q, G x := e.sum_comp G
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      change (∑ x : ZMod p, ∑ y : ZMod q,
        (1 - (p : ℂ) * if x = 0 then 1 else 0) * (y.val : ℂ)) = 0
      have hsum : (∑ x : ZMod p, (1 - (p : ℂ) * if x = 0 then 1 else 0)) = 0 := by
        simp [Finset.sum_sub_distrib]
      calc
        _ = (∑ x : ZMod p, (1 - (p : ℂ) * if x = 0 then 1 else 0)) *
          ∑ y : ZMod q, (y.val : ℂ) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            exact Finset.sum_comm
        _ = 0 := by rw [hsum, zero_mul]

theorem coprimeAbelCoefficient_shift_prefix_bound {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q) :
    ∃ C : ℝ, ∀ N,
      ‖∑ n ∈ Finset.range N, coprimeAbelCoefficient p q (n+1)‖ ≤ C := by
  have hf := coprimeAbelCoefficient_periodic p q
  have hz := coprimeAbelCoefficient_period_sum_zero hp hq hpq
  have hzero : ∑ n ∈ Finset.range (p*q), coprimeAbelCoefficient p q (n+1) = 0 := by
    have h := Finset.sum_range_succ' (coprimeAbelCoefficient p q) (p*q)
    rw [Finset.sum_range_succ, hz] at h
    have he := hf 0
    simp only [zero_add] at he
    rw [he] at h
    exact (add_right_cancel h).symm
  apply periodic_zero_sum_prefix_bound (Nat.mul_pos hp hq) _ hzero
  intro n
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf (n+1)

theorem kernel_pair_increment_summable (s t : ℂ)
    (hs : 0 < s.re) (ht : 0 < t.re) :
    Summable (fun n => ‖kernel s (n+1) * star (kernel t (n+1)) -
      kernel s n * star (kernel t n)‖) := by
  obtain ⟨B, hB⟩ := (kernel_tendsto_zero s hs).norm.bddAbove_range
  obtain ⟨C, hC⟩ := (kernel_tendsto_zero t ht).norm.bddAbove_range
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (((kernel_increment_summable t ht).mul_left B).add
      ((kernel_increment_summable s hs).mul_right C))
  have hid : kernel s (n+1) * star (kernel t (n+1)) - kernel s n * star (kernel t n) =
      kernel s (n+1) * star (kernel t (n+1) - kernel t n) +
        (kernel s (n+1) - kernel s n) * star (kernel t n) := by rw [star_sub]; ring
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right (hB ⟨n+1, rfl⟩) (norm_nonneg _)
  · rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left (hC ⟨n, rfl⟩) (norm_nonneg _)

/-- The Abel correction retains its literal residue and is absolutely summable. -/
theorem outerTest_remainder_summable (p q : ℕ) (s t : ℂ)
    (hs : 0 < s.re) (ht : 0 < t.re) :
    Summable (fun n => innerPrefix p s (n+1) * star (kernel t (n+1) - kernel t n) *
      (( (n+1) % (q+1) : ℕ) : ℂ)) := by
  obtain ⟨B, hB⟩ := innerPrefix_bounded p s hs
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  apply Summable.of_norm_bounded
    (((kernel_increment_summable t ht).mul_left B).mul_right (q : ℝ))
  intro n
  rw [norm_mul, norm_mul, norm_star, Complex.norm_natCast]
  apply mul_le_mul
    (mul_le_mul_of_nonneg_right (hB (n+1)) (norm_nonneg _))
  · exact_mod_cast (Nat.lt_succ_iff.mp (Nat.mod_lt (n+1) (Nat.succ_pos q)))
  · positivity
  · exact mul_nonneg hB0 (norm_nonneg _)

/-- Coprime channels admit their literal ordered cross level on the full positive quadrant. -/
theorem crossPrefix_converges_of_coprime (p q : ℕ) (s t : ℂ)
    (hpq : (p+1).Coprime (q+1)) (hs : 0 < s.re) (ht : 0 < t.re) :
    ∃ L : ℂ, Tendsto (crossPrefix p q s t) atTop (nhds L) := by
  obtain ⟨C, hC⟩ := coprimeAbelCoefficient_shift_prefix_bound
    (Nat.succ_pos p) (Nat.succ_pos q) hpq
  have hpair : Tendsto (fun n => kernel s n * star (kernel t n)) atTop (nhds 0) := by
    simpa using (kernel_tendsto_zero s hs).mul (kernel_tendsto_zero t ht).star
  obtain ⟨V, hV⟩ := ordered_sum_of_finite_variation hC hpair
    (kernel_pair_increment_summable s t hs ht)
  obtain ⟨W, hW⟩ := outerTest_remainder_summable p q s t hs ht
  let A (N : ℕ) : ℂ := ((N % (q+1) : ℕ) : ℂ)
  have hA (N : ℕ) : ∑ n ∈ Finset.range N, eulerDeletionDirichletCoefficient q n = A N :=
    eulerDeletionDirichletCoefficient_partialSum q N
  have hAnorm (N : ℕ) : ‖A N‖ ≤ q := by
    rw [← hA]
    exact eulerDeletionDirichletCoefficient_partialSum_norm_le q N
  have hboundary : Tendsto (fun N => outerTest p s t (N-1) * A N) atTop (nhds 0) := by
    apply squeeze_zero_norm' (Filter.Eventually.of_forall (fun N => ?_))
      (by simpa using ((outerTest_tendsto_zero p s t hs ht).comp
        (Filter.tendsto_sub_atTop_nat 1)).norm.mul_const (q : ℝ))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hAnorm N) (norm_nonneg _)
  have hid (N : ℕ) : crossPrefix p q s t N = outerTest p s t (N-1) * A N -
      ((∑ n ∈ Finset.range (N-1), coprimeAbelCoefficient (p+1) (q+1) (n+1) *
        (kernel s n * star (kernel t n))) +
      ∑ n ∈ Finset.range (N-1), innerPrefix p s (n+1) *
        star (kernel t (n+1) - kernel t n) * A (n+1)) := by
    have hab := Finset.sum_range_by_parts (outerTest p s t)
      (eulerDeletionDirichletCoefficient q) N
    simp only [smul_eq_mul, hA] at hab
    have hleft : crossPrefix p q s t N =
        ∑ n ∈ Finset.range N, outerTest p s t n * eulerDeletionDirichletCoefficient q n := by
      apply Finset.sum_congr rfl
      intro n _
      have ha : star (eulerDeletionDirichletCoefficient q n) =
        eulerDeletionDirichletCoefficient q n := by simp [eulerDeletionDirichletCoefficient]
      change innerPrefix p s n * star (eulerDeletionDirichletCoefficient q n * kernel t n) =
        (innerPrefix p s n * star (kernel t n)) * eulerDeletionDirichletCoefficient q n
      rw [star_mul', ha]
      ring
    rw [hleft, hab, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [outerTest_increment]
    change (eulerDeletionDirichletCoefficient p n * kernel s n * star (kernel t n) +
      innerPrefix p s (n+1) * star (kernel t (n+1) - kernel t n)) * A (n+1) = _
    dsimp [coprimeAbelCoefficient, A, eulerDeletionDirichletCoefficient]
    ring
  refine ⟨-(V+W), ?_⟩
  have hsum := (hV.add hW.tendsto_sum_nat).comp (Filter.tendsto_sub_atTop_nat 1)
  convert (hboundary.sub hsum).congr (fun N => (hid N).symm) using 1
  simp

end RHTower.DeletionChronologicalLimit

namespace RHTower

/-- Both exponents may cross the critical line: distinct coprime labels remove the
complete-period mixed coefficient, without changing the chronological cutoffs. -/
theorem tendsto_chronologicalCrossPrefix_eulerDeletion_coprime (p q : ℕ) (s t : ℂ)
    (hpq : (p+1).Coprime (q+1)) (hs : 0 < s.re) (ht : 0 < t.re) :
    ∃ L : ℂ, Tendsto
      (fun N => chronologicalCrossPrefix (eulerDeletionWeightedJump p s)
        (eulerDeletionWeightedJump q t) N) atTop (nhds L) :=
  DeletionChronologicalLimit.crossPrefix_converges_of_coprime p q s t hpq hs ht

end RHTower

