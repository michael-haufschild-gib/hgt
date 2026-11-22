import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedResonance

/-!
# Appending a digit to a balanced occupation cutoff

Deleting the low base-C² digit leaves a balanced parent. The positive
labels are the first C−1 digits together with C children of each parent.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation

abbrev radix (t : ExceptionalTime) (j : ℕ) := (tailRadix t j).val
abbrev Label (t : ExceptionalTime) (j : ℕ) := PositiveBalancedCutoff t j
abbrev First (C : ℕ) := {d : Fin C // 0 < d.val}
abbrev DigitTree (t : ExceptionalTime) (j : ℕ) :=
  First (radix t j) ⊕ Fin (radix t j) × Label t j

private def value (t : ExceptionalTime) (j : ℕ) : DigitTree t j → ℕ
  | .inl d => d.val.val
  | .inr (d,x) => d.val+(radix t j)^2*x.val.val

private theorem base_bound {C : ℕ} (hc : 1 < C) : C ≤ C^2 := by
  rw [pow_two]
  exact Nat.le_mul_of_pos_right _ (by omega)

private theorem child_digits {C : ℕ} (hc : 1 < C) (n : ℕ) (hn : 0 < n) (d : Fin C) :
    (C^2).digits (d.val+C^2*n) = d.val :: (C^2).digits n := by
  have hb : 1 < C^2 := hc.trans_le (base_bound hc)
  have hd := d.isLt.trans_le (base_bound hc)
  rw [Nat.digits_def' hb (Nat.add_pos_right _ (Nat.mul_pos (by omega) hn)),
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hd,Nat.add_mul_div_left _ _ (by omega : 0 < C^2),
    Nat.div_eq_of_lt hd,Nat.zero_add]

private def branchLabel (t : ExceptionalTime) (j : ℕ) (b : DigitTree t j) : Label t j := by
  let C := radix t j
  have hc : 1 < C := radix_gt_one t j
  refine ⟨⟨value t j b,(adjacent_count_equality t j _).mpr ?_⟩,?_⟩
  · cases b with
    | inl d =>
      change ∀ a ∈ (C^2).digits d.val.val, a < C
      rw [Nat.digits_of_lt _ _ d.property.ne' (d.val.isLt.trans_le (base_bound hc))]
      simpa only [List.mem_singleton,forall_eq] using d.val.isLt
    | inr p =>
      obtain ⟨d,x⟩ := p
      change ∀ a ∈ (C^2).digits (d.val+C^2*x.val.val), a < C
      rw [child_digits hc _ x.property d]
      exact List.forall_mem_cons.mpr ⟨d.isLt,(adjacent_count_equality t j _).mp x.val.property⟩
  · cases b with
    | inl d => exact d.property
    | inr p => exact Nat.add_pos_right _ (Nat.mul_pos (pow_pos (by omega : 0 < C) _) p.2.property)

private theorem onto (t : ExceptionalTime) (j : ℕ) : Function.Surjective (branchLabel t j) := by
  intro x
  let C := radix t j
  let B := C^2
  let n := x.val.val
  have hc : 1 < C := radix_gt_one t j
  have hb : 1 < B := hc.trans_le (base_bound hc)
  have h := (adjacent_count_equality t j n).mp x.val.property
  change ∀ d ∈ B.digits n, d < C at h
  rw [Nat.digits_def' hb x.property] at h
  obtain ⟨hd,hq⟩ := List.forall_mem_cons.mp h
  by_cases hz : n/B = 0
  · have hn : n%B = n := by simpa only [hz,mul_zero,add_zero] using Nat.mod_add_div n B
    exact ⟨.inl ⟨⟨n,hn ▸ hd⟩,x.property⟩,rfl⟩
  · refine ⟨.inr (⟨n%B,hd⟩,⟨⟨n/B,(adjacent_count_equality t j _).mpr hq⟩,Nat.pos_of_ne_zero hz⟩),?_⟩
    exact Subtype.ext (Subtype.ext (Nat.mod_add_div n B))

private theorem branch_injective (t : ExceptionalTime) (j : ℕ) : Function.Injective (branchLabel t j) := by
  let C := radix t j
  let B := C^2
  have hc : 1 < C := radix_gt_one t j
  have hb : 0 < B := (zero_lt_one.trans hc).trans_le (base_bound hc)
  have hd (d : Fin C) : d.val < B := d.isLt.trans_le (base_bound hc)
  have hlarge (d : Fin C) (x : Label t j) : B ≤ d.val+B*x.val.val :=
    (Nat.le_mul_of_pos_right _ x.property).trans (Nat.le_add_left _ _)
  rintro (a|⟨a,x⟩) (b|⟨b,y⟩) he
  · exact congrArg Sum.inl (Subtype.ext (Fin.ext (congrArg (fun z : Label t j => z.val.val) he)))
  · have hv : a.val.val = b.val+B*y.val.val := congrArg (fun z : Label t j => z.val.val) he
    exact ((hd a.val).not_ge (hv.symm ▸ hlarge b y)).elim
  · have hv : a.val+B*x.val.val = b.val.val := congrArg (fun z : Label t j => z.val.val) he
    exact ((hd b.val).not_ge (hv ▸ hlarge a x)).elim
  · have hv : a.val+B*x.val.val = b.val+B*y.val.val := congrArg (fun z : Label t j => z.val.val) he
    have hr := congrArg (· % B) hv
    have hq := congrArg (· / B) hv
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (hd a),Nat.mod_eq_of_lt (hd b)] at hr
    simp only [Nat.add_mul_div_left _ _ hb,Nat.div_eq_of_lt (hd a),Nat.div_eq_of_lt (hd b),Nat.zero_add] at hq
    exact congrArg Sum.inr (Prod.ext (Fin.ext hr) (Subtype.ext (Subtype.ext hq)))

/-- The first digit and the parent with its appended digit enumerate each balanced occupation once. -/
def digitTreeEquiv (t : ExceptionalTime) (j : ℕ) : DigitTree t j ≃ Label t j :=
  Equiv.ofBijective (branchLabel t j) ⟨branch_injective t j,onto t j⟩

/-- Integer energy label of the radix dilation of a balanced parent. -/
def dilation (t : ExceptionalTime) (j : ℕ) : ℕ+ := (tailRadix t j)^2

def child (t : ExceptionalTime) (j : ℕ) (d : Fin (radix t j)) (x : Label t j) : ℕ+ :=
  ⟨(digitTreeEquiv t j (.inr (d,x))).val.val,(digitTreeEquiv t j (.inr (d,x))).property⟩

theorem child_value (t : ExceptionalTime) (j : ℕ) (d : Fin (radix t j)) (x : Label t j) :
    (child t j d x).val = d.val+(dilation t j).val*x.val.val := rfl

/-- Contribution of the positive one-digit labels. -/
def firstHeat (t : ExceptionalTime) (j : ℕ) (s : ℂ) :=
  ∑ d : First (radix t j), heat s ⟨d.val.val,d.property⟩

/-- Heat difference between a child and the unshifted dilation of its parent. -/
def correction (t : ExceptionalTime) (j : ℕ) (d : Fin (radix t j)) (x : Label t j) (s : ℂ) : ℂ :=
  heat s (child t j d x) - heat s (dilation t j)*balancedHeat t j s x

/-- Removing the scale denominator leaves a sum of digit differences. -/
def numerator (t : ExceptionalTime) (j : ℕ) (s : ℂ) :=
  firstHeat t j s+∑ d : Fin (radix t j), ∑' x : Label t j, correction t j d x s

theorem digit_renewal (t : ExceptionalTime) (j : ℕ) (z : {s : ℂ // 1/2 < s.re}) :
    numerator t j z.val = (1-(radix t j:ℂ)*heat z.val (dilation t j))*balancedPartition t j z.val := by
  classical
  let C := radix t j
  let P := balancedPartition t j z.val
  let q := heat z.val (dilation t j)
  let W := balancedHeat t j z.val
  let e := digitTreeEquiv t j
  have hW : Summable W := ((balanced_heat_summable_iff t j z.val).mpr z.property).of_norm
  have hT : Summable (fun b : DigitTree t j => W (e b)) := e.summable_iff.mpr hW
  have hpair := hT.comp_injective (Sum.inr_injective (α := First C))
  change Summable (fun p : Fin C × Label t j => heat z.val (child t j p.1 p.2)) at hpair
  have hd (d : Fin C) : Summable (fun x : Label t j => heat z.val (child t j d x)) :=
    hpair.prod_factor d
  have hdecomp := e.tsum_eq W
  have hb := Summable.tsum_sum (f := fun b : DigitTree t j => W (e b)) Summable.of_finite hpair
  rw [hb,tsum_fintype (fun d : First C => W (e (.inl d)))] at hdecomp
  change firstHeat t j z.val+(∑' p : Fin C × Label t j, heat z.val (child t j p.1 p.2)) = P at hdecomp
  rw [hpair.tsum_prod] at hdecomp
  change firstHeat t j z.val+(∑' d : Fin C, ∑' x : Label t j, heat z.val (child t j d x)) = P at hdecomp
  rw [tsum_fintype] at hdecomp
  have hchange (d : Fin C) : (∑' x : Label t j, correction t j d x z.val) =
      (∑' x : Label t j, heat z.val (child t j d x))-q*P := by
    unfold correction
    rw [Summable.tsum_sub (hd d) (hW.mul_left q),tsum_mul_left]
    rfl
  change firstHeat t j z.val+∑ d : Fin C, _ = (1-(C:ℂ)*q)*P
  simp only [hchange,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  linear_combination hdecomp

#print axioms digitTreeEquiv
#print axioms digit_renewal

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation
