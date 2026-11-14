import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupHasIndexAtMostTwoInTheSignedPermutationsOfFiniteSupport
import GaloisForLFunctions.GaloisTheoryOfZeros.ConjugationOfTheZerosIsAMonodromyOfTheHeatCover
import GaloisForLFunctions.GaloisTheoryOfZeros.EveryForwardMonodromyMovesFinitelyManyZeros

/-!
# An odd number of quartets of nonreal zeros at a real time gives every signed permutation

At a real time `t > 0` the nonreal zeros of `H_t` form quartets `{z, z̄, −z, −z̄}`: the family is
positive on the imaginary axis, so no zero is imaginary. Each quartet has one zero in the open
first quadrant; `firstQuadrantZeros t` is the set of these zeros.

* **No imaginary zero** (`re_ne_zero_of_complexHeat_ofReal_eq_zero`).
  `H_t(iy) = ∫ Φ(x) e^{tx² − yx} dx > 0`.
* **Conjugation is a product of exchanges** (`quartetConj_firstQuadrantZeros`). Conjugation of
  the zeros of `H_t` exchanges the pairs `{z, −z}` and `{z̄, −z̄}` of every quartet and fixes
  every real zero.
* **The parity decides the last sign** (`mem_forwardMonodromy_of_odd_firstQuadrantZeros`). If
  the number of quartets is odd at one real time `t > 0` off the branch times, then at every
  forward time `b` off the branch times the group `G₊(b)` contains every permutation of the
  zeros of `H_b` that commutes with `z ↦ −z` and moves finitely many zeros.
* **Contrapositive** (`even_ncard_firstQuadrantZeros`). If `G₊` is not the group of all signed
  permutations of finite support, the nonreal zeros form an even number of quartets at every
  real time `t > 0` off the branch times.

Proof. Conjugation at `t` is an element of `G₊(t)`. Write it as the product of the exchanges of
its quartets. `G₊(t)` has index at most two in the signed permutations of finite support, so if
it contains none of these exchanges it contains the products of an even number of them and no
product of an odd number. With an odd number of quartets `G₊(t)` therefore contains one
exchange, and one exchange gives the whole group; a forward path carries the exchange to the
base `b`.
-/

open Complex MeasureTheory Set
open RHTower RHTower.DeBruijn Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-! ## No zero on the imaginary axis at a real time -/

theorem integrable_riemannKernelReal_mul_exp_sub (t y : ℝ) :
    Integrable fun x : ℝ => riemannKernelReal x * Real.exp (t * x ^ 2 - y * x) := by
  have h := (integrable_complexWeight_mul_pow_mul_exp (t : ℂ) 0 (I * y)).norm
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  have hpos := riemannKernelReal_pos x
  have hre : ((t : ℂ) * (x : ℂ) ^ 2).re = t * x ^ 2 := by
    rw [show (t : ℂ) * (x : ℂ) ^ 2 = ((t * x ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hre2 : (I * (I * (y : ℂ)) * x).re = -(y * x) := by
    rw [show I * (I * (y : ℂ)) * x = ((-(y * x) : ℝ) : ℂ) by
      push_cast
      linear_combination (y : ℂ) * x * I_mul_I, Complex.ofReal_re]
  simp only [pow_zero, mul_one, complexWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos, Complex.norm_exp, hre, hre2]
  rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]

/-- On the imaginary axis the family at a real time is the integral of a positive function. -/
theorem complexHeat_ofReal_mul_I (t y : ℝ) :
    complexHeat (t : ℂ) (I * y) =
      ((∫ x : ℝ, riemannKernelReal x * Real.exp (t * x ^ 2 - y * x) : ℝ) : ℂ) := by
  have h := integral_ofReal (μ := (volume : Measure ℝ)) (𝕜 := ℂ)
    (f := fun x : ℝ => riemannKernelReal x * Real.exp (t * x ^ 2 - y * x))
  rw [complexHeat]
  refine Eq.trans ?_ h
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (riemannKernelReal x : ℂ) * cexp ((t : ℂ) * (x : ℂ) ^ 2 + I * (I * y) * x) =
    ((riemannKernelReal x * Real.exp (t * x ^ 2 - y * x) : ℝ) : ℂ)
  rw [show (t : ℂ) * (x : ℂ) ^ 2 + I * (I * y) * x = ((t * x ^ 2 - y * x : ℝ) : ℂ) by
    push_cast
    linear_combination (y : ℂ) * x * I_mul_I, Complex.ofReal_mul, Complex.ofReal_exp]

/-- **At a real time no zero of the family lies on the imaginary axis.** -/
theorem re_ne_zero_of_complexHeat_ofReal_eq_zero {t : ℝ} {z : ℂ}
    (h : complexHeat (t : ℂ) z = 0) : z.re ≠ 0 := by
  intro hre
  have hz : z = I * (z.im : ℂ) := Complex.ext (by simp [hre]) (by simp)
  rw [hz, complexHeat_ofReal_mul_I, Complex.ofReal_eq_zero] at h
  have hpos : 0 < ∫ x : ℝ, riemannKernelReal x * Real.exp (t * x ^ 2 - z.im * x) := by
    rw [integral_pos_iff_support_of_nonneg
      (fun x => (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)).le)
      (integrable_riemannKernelReal_mul_exp_sub t z.im),
      eq_univ_of_forall fun x => Function.mem_support.mpr
        (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)).ne', Real.volume_univ]
    exact ENNReal.zero_lt_top
  exact hpos.ne' h

/-! ## The quartets -/

/-- The zeros of `H_t` in the open first quadrant, one for each quartet of nonreal zeros. -/
def firstQuadrantZeros (t : ℝ) : Set ℂ :=
  {z | complexHeat (t : ℂ) z = 0 ∧ 0 < z.re ∧ 0 < z.im}

/-- `z` lies in the quartet `{a, ā, −a, −ā}` of a point `a` of `A`. -/
def InQuartets (A : Set ℂ) (z : ℂ) : Prop :=
  z ∈ A ∨ starRingEnd ℂ z ∈ A ∨ -z ∈ A ∨ -starRingEnd ℂ z ∈ A

variable {A : Set ℂ} {z a : ℂ} {t : ℝ}

theorem inQuartets_conj : InQuartets A (starRingEnd ℂ z) ↔ InQuartets A z := by
  simp only [InQuartets, Complex.conj_conj]
  tauto

theorem inQuartets_neg : InQuartets A (-z) ↔ InQuartets A z := by
  simp only [InQuartets, map_neg, neg_neg]
  tauto

theorem inQuartets_insert : InQuartets (insert a A) z ↔ InQuartets {a} z ∨ InQuartets A z := by
  simp only [InQuartets, mem_insert_iff, mem_singleton_iff]
  tauto

theorem not_inQuartets_empty : ¬InQuartets ∅ z := by
  simp only [InQuartets, mem_empty_iff_false, or_self, not_false_eq_true]

/-- A quartet of a set of points of the open first quadrant meets the set in the point
`|Re z| + i |Im z|`. -/
theorem mk_abs_mem_of_inQuartets (hA : ∀ w ∈ A, 0 < w.re ∧ 0 < w.im) (h : InQuartets A z) :
    (⟨|z.re|, |z.im|⟩ : ℂ) ∈ A := by
  rcases h with h | h | h | h
  · have e : (⟨|z.re|, |z.im|⟩ : ℂ) = z :=
      Complex.ext (abs_of_pos (hA z h).1) (abs_of_pos (hA z h).2)
    rw [e]
    exact h
  · have h1 := (hA _ h).1
    have h2 := (hA _ h).2
    rw [Complex.conj_re] at h1
    rw [Complex.conj_im] at h2
    have e : (⟨|z.re|, |z.im|⟩ : ℂ) = starRingEnd ℂ z :=
      Complex.ext (by rw [Complex.conj_re]; exact abs_of_pos h1)
        (by rw [Complex.conj_im]; exact abs_of_neg (by linarith))
    rw [e]
    exact h
  · have h1 := (hA _ h).1
    have h2 := (hA _ h).2
    rw [Complex.neg_re] at h1
    rw [Complex.neg_im] at h2
    have e : (⟨|z.re|, |z.im|⟩ : ℂ) = -z :=
      Complex.ext (by rw [Complex.neg_re]; exact abs_of_neg (by linarith))
        (by rw [Complex.neg_im]; exact abs_of_neg (by linarith))
    rw [e]
    exact h
  · have h1 := (hA _ h).1
    have h2 := (hA _ h).2
    rw [Complex.neg_re, Complex.conj_re] at h1
    rw [Complex.neg_im, Complex.conj_im, neg_neg] at h2
    have e : (⟨|z.re|, |z.im|⟩ : ℂ) = -starRingEnd ℂ z :=
      Complex.ext (by rw [Complex.neg_re, Complex.conj_re]; exact abs_of_neg (by linarith))
        (by rw [Complex.neg_im, Complex.conj_im, neg_neg]; exact abs_of_pos h2)
    rw [e]
    exact h

theorem finite_setOf_inQuartets (hA : A.Finite) : {w : ℂ | InQuartets A w}.Finite := by
  refine ((hA.union (hA.image (starRingEnd ℂ))).union
    ((hA.image Neg.neg).union (hA.image fun w => -starRingEnd ℂ w))).subset fun w hw => ?_
  rcases hw with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr ⟨_, h, Complex.conj_conj w⟩)
  · exact Or.inr (Or.inl ⟨_, h, neg_neg w⟩)
  · exact Or.inr (Or.inr ⟨_, h, by
      show -starRingEnd ℂ (-starRingEnd ℂ w) = w
      rw [map_neg, Complex.conj_conj, neg_neg]⟩)

/-! ## Conjugation on a set of quartets -/

open Classical in
/-- `z ↦ z̄` on the quartets of the points of `A`, the identity on the other zeros. -/
noncomputable def quartetConjFun (t : ℝ) (A : Set ℂ)
    (p : {z : ℂ // complexHeat (t : ℂ) z = 0}) : {z : ℂ // complexHeat (t : ℂ) z = 0} :=
  if InQuartets A p.1 then fibreConj t p else p

variable {p : {z : ℂ // complexHeat (t : ℂ) z = 0}}

theorem quartetConjFun_of_inQuartets (h : InQuartets A p.1) :
    quartetConjFun t A p = fibreConj t p := if_pos h

theorem quartetConjFun_of_not_inQuartets (h : ¬InQuartets A p.1) :
    quartetConjFun t A p = p := if_neg h

theorem involutive_quartetConjFun (t : ℝ) (A : Set ℂ) :
    Function.Involutive (quartetConjFun t A) := by
  intro p
  by_cases h : InQuartets A p.1
  · have h' : InQuartets A (fibreConj t p).1 := inQuartets_conj.mpr h
    rw [quartetConjFun_of_inQuartets h, quartetConjFun_of_inQuartets h']
    exact Subtype.ext (Complex.conj_conj _)
  · rw [quartetConjFun_of_not_inQuartets h, quartetConjFun_of_not_inQuartets h]

/-- The conjugation of the quartets of the points of `A`, as a permutation of the zeros. -/
noncomputable def quartetConj (t : ℝ) (A : Set ℂ) :
    Perm {z : ℂ // complexHeat (t : ℂ) z = 0} :=
  (involutive_quartetConjFun t A).toPerm _

theorem quartetConj_apply_of_inQuartets (h : InQuartets A p.1) :
    quartetConj t A p = fibreConj t p := quartetConjFun_of_inQuartets h

theorem quartetConj_apply_of_not_inQuartets (h : ¬InQuartets A p.1) :
    quartetConj t A p = p := quartetConjFun_of_not_inQuartets h

theorem quartetConj_mul_self (t : ℝ) (A : Set ℂ) : quartetConj t A * quartetConj t A = 1 :=
  Equiv.ext fun p => involutive_quartetConjFun t A p

theorem quartetConj_inv (t : ℝ) (A : Set ℂ) : (quartetConj t A)⁻¹ = quartetConj t A :=
  inv_eq_of_mul_eq_one_left (quartetConj_mul_self t A)

theorem quartetConj_empty (t : ℝ) : quartetConj t ∅ = 1 :=
  Equiv.ext fun _ => quartetConj_apply_of_not_inQuartets not_inQuartets_empty

/-- It commutes with `z ↦ −z`. -/
theorem quartetConj_fibreNeg (A : Set ℂ) (p : {z : ℂ // complexHeat (t : ℂ) z = 0}) :
    quartetConj t A (fibreNeg (t : ℂ) p) = fibreNeg (t : ℂ) (quartetConj t A p) := by
  by_cases h : InQuartets A p.1
  · have h' : InQuartets A (fibreNeg (t : ℂ) p).1 := inQuartets_neg.mpr h
    rw [quartetConj_apply_of_inQuartets h, quartetConj_apply_of_inQuartets h']
    exact Subtype.ext (map_neg _ _)
  · have h' : ¬InQuartets A (fibreNeg (t : ℂ) p).1 := fun h' => h (inQuartets_neg.mp h')
    rw [quartetConj_apply_of_not_inQuartets h, quartetConj_apply_of_not_inQuartets h']

/-- It moves finitely many zeros when `A` is finite. -/
theorem finite_setOf_quartetConj_ne (t : ℝ) (hA : A.Finite) :
    {p | quartetConj t A p ≠ p}.Finite := by
  refine ((finite_setOf_inQuartets hA).preimage
    (Subtype.val_injective (p := fun z : ℂ => complexHeat (t : ℂ) z = 0)).injOn).subset
    fun p hp => ?_
  by_contra h
  exact hp (quartetConj_apply_of_not_inQuartets h)

/-- The conjugation of the quartets of `A` and of one more quartet is the product. -/
theorem quartetConj_insert (hA : ∀ w ∈ A, 0 < w.re ∧ 0 < w.im) (ha : 0 < a.re ∧ 0 < a.im)
    (haA : a ∉ A) : quartetConj t (insert a A) = quartetConj t A * quartetConj t {a} := by
  refine Equiv.ext fun p => ?_
  rw [Perm.mul_apply]
  by_cases h1 : InQuartets {a} p.1
  · -- the quartet of `a` is not a quartet of `A`
    have h2 : ¬InQuartets A p.1 := fun h2 => by
      have e1 := mk_abs_mem_of_inQuartets (A := {a}) (fun w hw => by
        rw [mem_singleton_iff.mp hw]
        exact ha) h1
      rw [mem_singleton_iff] at e1
      have e2 := mk_abs_mem_of_inQuartets hA h2
      rw [e1] at e2
      exact haA e2
    have h2' : ¬InQuartets A (fibreConj t p).1 := fun h => h2 (inQuartets_conj.mp h)
    rw [quartetConj_apply_of_inQuartets (inQuartets_insert.mpr (Or.inl h1)),
      quartetConj_apply_of_inQuartets h1, quartetConj_apply_of_not_inQuartets h2']
  · rw [quartetConj_apply_of_not_inQuartets h1]
    by_cases h2 : InQuartets A p.1
    · rw [quartetConj_apply_of_inQuartets (inQuartets_insert.mpr (Or.inr h2)),
        quartetConj_apply_of_inQuartets h2]
    · rw [quartetConj_apply_of_not_inQuartets (fun h => (inQuartets_insert.mp h).elim h1 h2),
        quartetConj_apply_of_not_inQuartets h2]

/-- **Conjugation is the conjugation of all quartets.** At a real time the conjugation of the
zeros moves exactly the zeros of the quartets. -/
theorem quartetConj_firstQuadrantZeros (t : ℝ) :
    quartetConj t (firstQuadrantZeros t) = fibreConj t := by
  refine Equiv.ext fun p => ?_
  by_cases h : InQuartets (firstQuadrantZeros t) p.1
  · exact quartetConj_apply_of_inQuartets h
  · rw [quartetConj_apply_of_not_inQuartets h]
    -- a zero outside the quartets is real
    have hre := re_ne_zero_of_complexHeat_ofReal_eq_zero p.2
    have him : p.1.im = 0 := by
      by_contra him
      refine h ?_
      rcases lt_or_gt_of_ne hre with h1 | h1 <;> rcases lt_or_gt_of_ne him with h2 | h2
      · exact Or.inr (Or.inr (Or.inl ⟨by rw [complexHeat_neg]; exact p.2,
          by rw [Complex.neg_re]; linarith, by rw [Complex.neg_im]; linarith⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by
          rw [complexHeat_neg, complexHeat_ofReal_conj, p.2, map_zero],
          by rw [Complex.neg_re, Complex.conj_re]; linarith,
          by rw [Complex.neg_im, Complex.conj_im, neg_neg]; exact h2⟩))
      · exact Or.inr (Or.inl ⟨by rw [complexHeat_ofReal_conj, p.2, map_zero],
          by rw [Complex.conj_re]; exact h1, by rw [Complex.conj_im]; linarith⟩)
      · exact Or.inl ⟨p.2, h1, h2⟩
    exact (Subtype.ext (Complex.conj_eq_iff_im.mpr him)).symm

/-- **The quartets are finitely many** at a real time off the branch times. -/
theorem finite_firstQuadrantZeros (ht : 0 < t) (hb : (t : ℂ) ∉ branchTimes) :
    (firstQuadrantZeros t).Finite := by
  refine ((finite_setOf_forwardMonodromy_ne (fibreConj_mem_forwardMonodromy ht hb)).image
    Subtype.val).subset fun z hz => ?_
  refine ⟨⟨z, hz.1⟩, fun h => ?_, rfl⟩
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp (congrArg Subtype.val h)
  exact hz.2.2.ne' him

/-! ## The exchange of one quartet -/

/-- The conjugation of one quartet is the exchange of its two pairs. -/
theorem quartetConj_singleton_exchange (ha : a ∈ firstQuadrantZeros t) :
    ∃ x x' : {z : ℂ // complexHeat (t : ℂ) z = 0}, x' ≠ x ∧ x' ≠ fibreNeg (t : ℂ) x ∧
      quartetConj t {a} x = x' ∧ quartetConj t {a} x' = x ∧
      ∀ y, y ≠ x → y ≠ fibreNeg (t : ℂ) x → y ≠ x' → y ≠ fibreNeg (t : ℂ) x' →
        quartetConj t {a} y = y := by
  have hx : InQuartets {a} a := Or.inl rfl
  have hx' : InQuartets {a} (starRingEnd ℂ a) := inQuartets_conj.mpr hx
  refine ⟨⟨a, ha.1⟩, fibreConj t ⟨a, ha.1⟩, fun h => ?_, fun h => ?_,
    quartetConj_apply_of_inQuartets hx, ?_, fun y h1 h2 h3 h4 => ?_⟩
  · exact ha.2.2.ne' (Complex.conj_eq_iff_im.mp (congrArg Subtype.val h))
  · have e : starRingEnd ℂ a = -a := congrArg Subtype.val h
    have e' := congrArg Complex.re e
    rw [Complex.conj_re, Complex.neg_re] at e'
    linarith [ha.2.1]
  · rw [quartetConj_apply_of_inQuartets (p := fibreConj t ⟨a, ha.1⟩) hx']
    exact Subtype.ext (Complex.conj_conj a)
  · refine quartetConj_apply_of_not_inQuartets fun h => ?_
    rcases h with h | h | h | h
    · exact h1 (Subtype.ext h)
    · refine h3 (Subtype.ext ?_)
      show y.1 = starRingEnd ℂ a
      rw [← mem_singleton_iff.mp h, Complex.conj_conj]
    · refine h2 (Subtype.ext ?_)
      show y.1 = -a
      rw [← mem_singleton_iff.mp h, neg_neg]
    · refine h4 (Subtype.ext ?_)
      show y.1 = -starRingEnd ℂ a
      rw [← mem_singleton_iff.mp h, map_neg, Complex.conj_conj, neg_neg]

/-! ## The parity of the number of quartets -/

/-- If `G₊(t)` contains the exchange of no quartet, it contains the conjugation of a set of
quartets exactly when their number is even. -/
theorem quartetConj_mem_forwardMonodromy_iff_even (ht : 0 < t) (hb : (t : ℂ) ∉ branchTimes)
    (hno : ∀ a ∈ firstQuadrantZeros t, quartetConj t {a} ∉
      forwardMonodromy (t : ℂ) (by rw [Complex.ofReal_re]; exact ht) hb)
    (B : Finset ℂ) (hB : (B : Set ℂ) ⊆ firstQuadrantZeros t) :
    quartetConj t (B : Set ℂ) ∈
      forwardMonodromy (t : ℂ) (by rw [Complex.ofReal_re]; exact ht) hb ↔ Even B.card := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, quartetConj_empty]
    exact ⟨fun _ => Even.zero, fun _ => Subgroup.one_mem _⟩
  | insert a B haB ih =>
    have hB' : (B : Set ℂ) ⊆ firstQuadrantZeros t := fun w hw =>
      hB (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hw)))
    have ha : a ∈ firstQuadrantZeros t := hB (Finset.mem_coe.2 (Finset.mem_insert_self a B))
    have hea := hno a ha
    rw [Finset.coe_insert, quartetConj_insert (fun w hw => (hB' hw).2) ha.2
      (fun h => haB (Finset.mem_coe.1 h)), Finset.card_insert_of_notMem haB, Nat.even_add_one,
      ← ih hB']
    refine ⟨fun h hx => hea (((Subgroup.mul_mem_cancel_left _ hx).mp h)), fun hx => ?_⟩
    -- index at most two: the product of two elements outside the group lies in it
    have key := mem_forwardMonodromy_or_mem_or_mul_inv_mem
      (by rw [Complex.ofReal_re]; exact ht) hb
      (quartetConj_fibreNeg (t := t) (B : Set ℂ))
      (finite_setOf_quartetConj_ne t B.finite_toSet)
      (quartetConj_fibreNeg (t := t) {a})
      (finite_setOf_quartetConj_ne t (finite_singleton a))
    rw [quartetConj_inv] at key
    exact (key.resolve_left hx).resolve_left hea

/-- **With an odd number of quartets `G₊(t)` contains the exchange of one quartet.** -/
theorem exists_quartetConj_singleton_mem_forwardMonodromy (ht : 0 < t)
    (hb : (t : ℂ) ∉ branchTimes) (hodd : Odd (firstQuadrantZeros t).ncard) :
    ∃ a ∈ firstQuadrantZeros t, quartetConj t {a} ∈
      forwardMonodromy (t : ℂ) (by rw [Complex.ofReal_re]; exact ht) hb := by
  by_contra hno
  have hno' : ∀ a ∈ firstQuadrantZeros t, quartetConj t {a} ∉
      forwardMonodromy (t : ℂ) (by rw [Complex.ofReal_re]; exact ht) hb :=
    fun a ha h => hno ⟨a, ha, h⟩
  have hfin := finite_firstQuadrantZeros ht hb
  have h := quartetConj_mem_forwardMonodromy_iff_even ht hb hno' hfin.toFinset
    (by rw [hfin.coe_toFinset])
  rw [hfin.coe_toFinset, quartetConj_firstQuadrantZeros,
    ← Set.ncard_eq_toFinset_card (firstQuadrantZeros t) hfin] at h
  exact (Nat.not_even_iff_odd.mpr hodd) (h.mp (fibreConj_mem_forwardMonodromy ht hb))

/-! ## Every signed permutation -/

/-- **An odd number of quartets gives every signed permutation.** If at one real time `t > 0`
off the branch times the nonreal zeros of `H_t` form an odd number of quartets, then at every
forward time `b` off the branch times the group `G₊(b)` contains every permutation of the zeros
of `H_b` that commutes with `z ↦ −z` and moves finitely many zeros. -/
theorem mem_forwardMonodromy_of_odd_firstQuadrantZeros (ht : 0 < t)
    (hb : (t : ℂ) ∉ branchTimes) (hodd : Odd (firstQuadrantZeros t).ncard) {b : ℂ}
    (hb₀ : 0 < b.re) (hbb : b ∉ branchTimes) {w : Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite) :
    w ∈ forwardMonodromy b hb₀ hbb := by
  have ht₀ : 0 < ((t : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact ht
  obtain ⟨a, ha, haG⟩ := exists_quartetConj_singleton_mem_forwardMonodromy ht hb hodd
  obtain ⟨x, x', h1, h2, hx, hx', ho⟩ := quartetConj_singleton_exchange ha
  -- a forward path carries the exchange to the base `b`
  obtain ⟨γ, hγ, g0, g1⟩ := exists_isForwardPath ht₀ hb₀ hb hbb
  obtain ⟨φ, hφ⟩ := hγ.exists_fibreEquiv g0 g1
  have hφn : ∀ q, φ (fibreNeg (t : ℂ) q) = fibreNeg b (φ q) := fun q =>
    Subtype.ext (hγ.transports_unique (hφ (fibreNeg (t : ℂ) q)) (hφ q).neg)
  have hφs : ∀ y, φ.symm (fibreNeg b y) = fibreNeg (t : ℂ) (φ.symm y) := fun y => by
    rw [Equiv.symm_apply_eq, hφn, Equiv.apply_symm_apply]
  refine mem_forwardMonodromy_of_exchange_mem hb₀ hbb (a := φ x) (a' := φ x')
    (e := φ.permCongr (quartetConj t {a})) (fun h => h1 (φ.injective h))
    (fun h => h2 (φ.injective (h.trans (hφn x).symm))) ?_ ?_ (fun y => ?_)
    (fun y k1 k2 k3 k4 => ?_) (hγ.permCongr_mem_forwardMonodromy g0 g1 hφ haG) hw hfin
  · rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, hx]
  · rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, hx']
  · rw [Equiv.permCongr_apply, Equiv.permCongr_apply, hφs, quartetConj_fibreNeg, hφn]
  · rw [Equiv.permCongr_apply, ho (φ.symm y) (fun h => k1 ((Equiv.symm_apply_eq φ).mp h))
      (fun h => k2 (by rw [(Equiv.symm_apply_eq φ).mp h, hφn]))
      (fun h => k3 ((Equiv.symm_apply_eq φ).mp h))
      (fun h => k4 (by rw [(Equiv.symm_apply_eq φ).mp h, hφn])), Equiv.apply_symm_apply]

/-- **If `G₊` is not the group of all signed permutations of finite support, the quartets of
nonreal zeros are even in number** at every real time `t > 0` off the branch times. -/
theorem even_ncard_firstQuadrantZeros {b : ℂ} (hb₀ : 0 < b.re) (hbb : b ∉ branchTimes)
    {w : Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite)
    (hwG : w ∉ forwardMonodromy b hb₀ hbb) (ht : 0 < t) (hb : (t : ℂ) ∉ branchTimes) :
    Even (firstQuadrantZeros t).ncard := by
  by_contra h
  exact hwG (mem_forwardMonodromy_of_odd_firstQuadrantZeros ht hb (Nat.not_even_iff_odd.mp h)
    hb₀ hbb hw hfin)

end GaloisForLFunctions.GaloisTheoryOfZeros
