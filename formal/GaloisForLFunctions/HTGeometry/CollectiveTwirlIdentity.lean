import GaloisForLFunctions.HTGeometry.CollectiveCentralBlock

/-!
# The collective twirl of a replica moment is the normalized symmetric projector

A collectively central operator pairs with the replica projector of a unit vector to one and the
same number, and that pairing reads off the content-class row sums against the squared moduli of
the pure tensor.  Feeding a strictly positive weight vector through the square root turns the
resulting identity into the vanishing of a pure-tensor pairing, so monomial separation forces every
content-class sum of the row sums to be the class size times that number.

Summing the row sums against the symmetric projector's class averages then gives the number of
content classes times the pairing, which is exactly the statement that the moment of any law on
unit targets and the normalized symmetric projector have the same pairing with every collectively
central operator.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Twirl

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The content-class row sum of an operator. -/
def classRowSum (r : ℕ) (Z : Matrix (Fin r → α) (Fin r → α) ℂ) (x : Fin r → α) : ℂ :=
  ∑ y ∈ symClass r x, Z x y

/-- **The replica trace pairing reads off the content-class row sums.** -/
theorem trace_mul_replicaProjector_eq_sum (r : ℕ) {Z : Matrix (Fin r → α) (Fin r → α) ℂ}
    (hZ : IsCollectiveCentral r Z) (psi : α → ℂ) :
    (Z * replicaProjector r psi).trace
      = ∑ x, ((starRingEnd ℂ) (finitePureTensorPower r psi x) *
          finitePureTensorPower r psi x) * classRowSum r Z x := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hterm : ∀ y : Fin r → α, Z x y * replicaProjector r psi y x
      = if symTupleIndex r y = symTupleIndex r x then
          ((starRingEnd ℂ) (finitePureTensorPower r psi x) *
            finitePureTensorPower r psi x) * Z x y else 0 := by
    intro y
    by_cases hy : symTupleIndex r y = symTupleIndex r x
    · rw [if_pos hy, replicaProjector_apply, finitePureTensorPower_congr r psi hy]
      ring
    · rw [if_neg hy, eq_zero_of_isCollectiveCentral r hZ (fun hh => hy hh.symm), zero_mul]
  rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.sum_filter, ← Finset.mul_sum]
  rfl

/-- **The class-sum identity.**  Every content-class sum of the row sums is the class size times
the common pairing. -/
theorem sum_symClass_classRowSum (r : ℕ) [Nonempty α]
    {Z : Matrix (Fin r → α) (Fin r → α) ℂ} (hZ : IsCollectiveCentral r Z) (a0 : α)
    (x0 : Fin r → α) :
    (∑ x ∈ symClass r x0, classRowSum r Z x)
      = ((symClass r x0).card : ℂ) *
          (Z * replicaProjector r (fun a => if a = a0 then (1 : ℂ) else 0)).trace := by
  classical
  set q0 : ℂ := (Z * replicaProjector r
    (fun a => if a = a0 then (1 : ℂ) else 0)).trace with hq0
  have hsep : ∀ t : α → ℝ, (∀ a, 0 < t a) →
      (∑ x, (classRowSum r Z x - q0) *
        finitePureTensorPower r (fun a => (t a : ℂ)) x) = 0 := by
    intro t ht
    set s : ℝ := ∑ a, t a with hs
    have hspos : 0 < s := Finset.sum_pos (fun a _ => ht a) Finset.univ_nonempty
    set u : α → ℝ := fun a => Real.sqrt (t a / s) with hu
    have husq : ∀ a, u a ^ (2 : ℕ) = t a / s := by
      intro a
      rw [hu]
      exact Real.sq_sqrt (le_of_lt (div_pos (ht a) hspos))
    set psi : α → ℂ := fun a => (u a : ℂ) with hpsi
    have hunit : finiteComplexInner psi psi = 1 := by
      rw [finiteComplexInner]
      have hstep : ∀ a : α, (starRingEnd ℂ) (psi a) * psi a = ((t a / s : ℝ) : ℂ) := by
        intro a
        rw [hpsi]
        simp only [Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, ← husq a]
        push_cast
        ring
      rw [Finset.sum_congr rfl fun a _ => hstep a, ← Complex.ofReal_sum, ← Finset.sum_div, ← hs,
        div_self (ne_of_gt hspos), Complex.ofReal_one]
    have hw : ∀ x : Fin r → α,
        (starRingEnd ℂ) (finitePureTensorPower r psi x) * finitePureTensorPower r psi x *
          ((s : ℂ) ^ r) = finitePureTensorPower r (fun a => (t a : ℂ)) x := by
      intro x
      have hpure : finitePureTensorPower r psi x = ((∏ i, u (x i) : ℝ) : ℂ) := by
        rw [finitePureTensorPower, hpsi]
        push_cast
        ring
      rw [hpure]
      simp only [Complex.conj_ofReal]
      rw [← Complex.ofReal_mul]
      have hreal : (∏ i, u (x i)) * (∏ i, u (x i)) = (∏ i, t (x i)) / s ^ r := by
        rw [← Finset.prod_mul_distrib]
        have hstep : ∀ i : Fin r, u (x i) * u (x i) = t (x i) / s := by
          intro i
          have := husq (x i)
          nlinarith [this]
        rw [Finset.prod_congr rfl fun i _ => hstep i, Finset.prod_div_distrib,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hreal]
      have hsne : ((s : ℂ)) ^ r ≠ 0 := by
        have hs0 : ((s : ℝ) : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact ne_of_gt hspos
        exact pow_ne_zero r hs0
      rw [finitePureTensorPower]
      push_cast
      field_simp
    have hQ := trace_mul_replicaProjector_eq_sum r hZ psi
    have hconst := trace_mul_replicaProjector_eq_of_unit r hZ psi hunit a0
    have htotal : (∑ x : Fin r → α, (starRingEnd ℂ) (finitePureTensorPower r psi x) *
        finitePureTensorPower r psi x) = 1 := by
      have := finiteComplexInner_pureTensorPower r psi psi
      rw [finiteComplexInner] at this
      rw [this, hunit, one_pow]
    have hzero : (∑ x : Fin r → α, ((starRingEnd ℂ) (finitePureTensorPower r psi x) *
        finitePureTensorPower r psi x) * (classRowSum r Z x - q0)) = 0 := by
      have hsplit : (∑ x : Fin r → α, ((starRingEnd ℂ) (finitePureTensorPower r psi x) *
          finitePureTensorPower r psi x) * (classRowSum r Z x - q0))
          = (∑ x : Fin r → α, ((starRingEnd ℂ) (finitePureTensorPower r psi x) *
              finitePureTensorPower r psi x) * classRowSum r Z x)
            - (∑ x : Fin r → α, ((starRingEnd ℂ) (finitePureTensorPower r psi x) *
              finitePureTensorPower r psi x)) * q0 := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [hsplit, ← hQ, hconst, htotal, one_mul, sub_self]
    have hscale : (∑ x, (classRowSum r Z x - q0) *
        finitePureTensorPower r (fun a => (t a : ℂ)) x)
        = (∑ x : Fin r → α, ((starRingEnd ℂ) (finitePureTensorPower r psi x) *
            finitePureTensorPower r psi x) * (classRowSum r Z x - q0)) * ((s : ℂ) ^ r) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hw x]
      ring
    rw [hscale, hzero, zero_mul]
  have hclass := sum_symClass_eq_zero_of_forall_pos r
    (fun x => classRowSum r Z x - q0) hsep x0
  have hsplit : (∑ x ∈ symClass r x0, (classRowSum r Z x - q0))
      = (∑ x ∈ symClass r x0, classRowSum r Z x) - ((symClass r x0).card : ℂ) * q0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hsplit, sub_eq_zero] at hclass
  exact hclass

/-- **`(21)`.**  The pairing of a collectively central operator with the normalized symmetric
projector is the same as with the replica projector of any unit vector. -/
theorem trace_mul_symReplicaProjection (r : ℕ) [Nonempty α]
    {Z : Matrix (Fin r → α) (Fin r → α) ℂ} (hZ : IsCollectiveCentral r Z) (a0 : α) :
    (Z * symReplicaProjection (α := α) r).trace
      = (((Fintype.card α + r - 1).choose r : ℕ) : ℂ) *
          (Z * replicaProjector r (fun a => if a = a0 then (1 : ℂ) else 0)).trace := by
  classical
  set q0 : ℂ := (Z * replicaProjector r
    (fun a => if a = a0 then (1 : ℂ) else 0)).trace with hq0
  have hrow : ∀ x : Fin r → α,
      (∑ y : Fin r → α, Z x y * symReplicaProjection (α := α) r y x)
        = classRowSum r Z x * (((symClass r x).card : ℂ))⁻¹ := by
    intro x
    have hterm : ∀ y : Fin r → α, Z x y * symReplicaProjection (α := α) r y x
        = if symTupleIndex r y = symTupleIndex r x then
            Z x y * (((symClass r x).card : ℂ))⁻¹ else 0 := by
      intro y
      rw [symReplicaProjection_apply]
      by_cases hy : symTupleIndex r y = symTupleIndex r x
      · rw [if_pos hy, if_pos hy, symClass_eq_of_index_eq r hy]
      · rw [if_neg hy, if_neg hy, mul_zero]
    rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.sum_filter, ← Finset.sum_mul]
    rfl
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun x _ => hrow x,
    ← Finset.sum_fiberwise (Finset.univ : Finset (Fin r → α)) (symTupleIndex r)
      (fun x => classRowSum r Z x * (((symClass r x).card : ℂ))⁻¹)]
  have hfib : ∀ s : Sym α r,
      (∑ x ∈ Finset.univ with symTupleIndex r x = s,
        classRowSum r Z x * (((symClass r x).card : ℂ))⁻¹) = q0 := by
    intro s
    obtain ⟨x0, hx0⟩ := symTupleIndex_surjective (α := α) r s
    have hset : (Finset.univ.filter fun x : Fin r → α => symTupleIndex r x = s)
        = symClass r x0 := by
      ext z
      simp [symClass, hx0]
    rw [hset]
    have hval : ∀ z ∈ symClass r x0,
        classRowSum r Z z * (((symClass r z).card : ℂ))⁻¹
          = classRowSum r Z z * (((symClass r x0).card : ℂ))⁻¹ := by
      intro z hz
      rw [symClass_eq_of_index_eq r ((mem_symClass_iff r x0 z).mp hz)]
    have hcard := symClass_card_ne_zero r x0
    rw [Finset.sum_congr rfl hval, ← Finset.sum_mul,
      sum_symClass_classRowSum r hZ a0 x0]
    field_simp
    exact hq0.symm
  rw [Finset.sum_congr rfl fun s _ => hfib s, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Sym.card_sym_eq_choose (α := α) r]


theorem replicaMoment_eq_sum_smul (r : ℕ) {C : Type*} [Fintype C] (w : C → ℝ)
    (target : C → α → ℂ) :
    replicaMoment r w target = ∑ c, (w c : ℂ) • replicaProjector r (target c) := by
  funext x y
  rw [replicaMoment_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_apply, replicaProjector_apply, smul_eq_mul]

theorem trace_mul_replicaMoment (r : ℕ) [Nonempty α] {C : Type*} [Fintype C]
    {Z : Matrix (Fin r → α) (Fin r → α) ℂ} (hZ : IsCollectiveCentral r Z)
    (w : C → ℝ) (target : C → α → ℂ)
    (hunit : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (hsum : ∑ c, w c = 1) (a0 : α) :
    (Z * replicaMoment r w target).trace
      = (Z * replicaProjector r (fun a => if a = a0 then (1 : ℂ) else 0)).trace := by
  rw [replicaMoment_eq_sum_smul, Finset.mul_sum, Matrix.trace_sum]
  have hterm : ∀ c : C, (Z * ((w c : ℂ) • replicaProjector r (target c))).trace
      = (w c : ℂ) * (Z * replicaProjector r
          (fun a => if a = a0 then (1 : ℂ) else 0)).trace := by
    intro c
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      trace_mul_replicaProjector_eq_of_unit r hZ (target c) (hunit c) a0]
  rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_mul, ← Complex.ofReal_sum, hsum,
    Complex.ofReal_one, one_mul]

/-- **`(21)`.**  The moment of a law on unit targets and the normalized symmetric projector have
the same pairing with every collectively central operator, so the collective twirl of the moment is
`Ω_{D,r}` and `(I - Π_{D,r}) M_ν = M_ν - Ω_{D,r}`. -/
theorem trace_mul_replicaMoment_eq_omega (r : ℕ) [Nonempty α] {C : Type*} [Fintype C]
    {Z : Matrix (Fin r → α) (Fin r → α) ℂ} (hZ : IsCollectiveCentral r Z)
    (w : C → ℝ) (target : C → α → ℂ)
    (hunit : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (hsum : ∑ c, w c = 1) (a0 : α) :
    (Z * replicaMoment r w target).trace
      = (Z * (((((Fintype.card α + r - 1).choose r : ℕ) : ℝ) : ℂ))⁻¹ •
          symReplicaProjection (α := α) r).trace := by
  have hh : ((((Fintype.card α + r - 1).choose r : ℕ) : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < (((Fintype.card α + r - 1).choose r : ℕ) : ℝ) :=
      choose_pos_of_nonempty (α := α) r
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hpos
  rw [trace_mul_replicaMoment r hZ w target hunit hsum a0, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, trace_mul_symReplicaProjection r hZ a0]
  have hcast : (((Fintype.card α + r - 1).choose r : ℕ) : ℂ)
      = ((((Fintype.card α + r - 1).choose r : ℕ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast]
  field_simp

end Twirl

end

end GaloisForLFunctions.HTGeometry
