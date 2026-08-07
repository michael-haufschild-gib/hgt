import GaloisForLFunctions.HTGeometry.CDGABarSquare

/-!
# Multiplications at distance commute

The head of a bar differential multiplies the first two factors; the tail of a tail applies a
degree-one map inside the third and later ones.  They act on disjoint factors, so they commute, and
the two Koszul signs differ by one: the head raises the degree of the first slot by one before the
outer sign is taken.  That is the second of the two cancellations in `d² = 0`, the one that is not
associativity.

* `HTGeometry.barMulTail` : multiply the first two factors and act on the rest.
* `HTGeometry.barMulTail_cancel` : the two orders cancel.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))
  {W W' : Type u} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']

/-- **Multiply the first two of three adjacent factors and act on the third.** -/
noncomputable def barMulTail {p q m : ℕ} (h : p + q + 1 = m) (g : W →ₗ[R] W') :
    TensorProduct R (barShiftFamily ε p) (TensorProduct R (barShiftFamily ε q) W)
      →ₗ[R] TensorProduct R (barShiftFamily ε m) W' :=
  (TensorProduct.map (augIdealShiftMulOfTensor ε h) g).comp
    ((TensorProduct.assoc R (barShiftFamily ε p) (barShiftFamily ε q) W).symm.toLinearMap)

@[simp] theorem barMulTail_tmul {p q m : ℕ} (h : p + q + 1 = m) (g : W →ₗ[R] W')
    (x : barShiftFamily ε p) (y : barShiftFamily ε q) (z : W) :
    barMulTail ε h g (x ⊗ₜ[R] (y ⊗ₜ[R] z))
      = augIdealShiftMulOf ε h x y ⊗ₜ[R] g z := rfl

/-- **The two orders cancel.**  Both compose to the same map; the signs are `(-1)^{p+q}` for acting
first and `(-1)^{p+q+1}` for multiplying first, because the multiplication raises the degree of the
slot the outer sign reads. -/
theorem barMulTail_cancel {p q m : ℕ} (h : p + q + 1 = m) (g : W →ₗ[R] W')
    (T : TensorProduct R (barShiftFamily ε p) (TensorProduct R (barShiftFamily ε q) W)) :
    ((-1 : R)) ^ (p + q) • barMulTail ε h g T
      + ((-1 : R)) ^ m • barMulTail ε h g T = 0 := by
  rw [← add_smul]
  have hm : ((-1 : R)) ^ (p + q) + ((-1 : R)) ^ m = 0 := by
    subst h
    rw [pow_succ]
    ring
  rw [hm, zero_smul]

/-- Acting on the third factor and then multiplying the first two is the combined map. -/
theorem barMulTail_first {p q m : ℕ} (h : p + q + 1 = m) (g : W →ₗ[R] W')
    (T : TensorProduct R (barShiftFamily ε p) (TensorProduct R (barShiftFamily ε q) W)) :
    (TensorProduct.map (augIdealShiftMulOfTensor ε h) (LinearMap.id (R := R) (M := W')))
        ((TensorProduct.assoc R (barShiftFamily ε p) (barShiftFamily ε q) W').symm
          (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
            (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε q)) g) T))
      = barMulTail ε h g T := by
  induction T using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add T T' hT hT' =>
      simp only [map_add]
      rw [hT, hT']
  | tmul x V =>
      induction V using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add V V' hV hV' =>
          simp only [TensorProduct.tmul_add, map_add]
          rw [hV, hV']
      | tmul y z => rfl

/-- Multiplying the first two factors and then acting on the third is the combined map. -/
theorem barMulTail_second {p q m : ℕ} (h : p + q + 1 = m) (g : W →ₗ[R] W')
    (T : TensorProduct R (barShiftFamily ε p) (TensorProduct R (barShiftFamily ε q) W)) :
    (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε m)) g)
        ((TensorProduct.map (augIdealShiftMulOfTensor ε h) (LinearMap.id (R := R) (M := W)))
          ((TensorProduct.assoc R (barShiftFamily ε p) (barShiftFamily ε q) W).symm T))
      = barMulTail ε h g T := by
  induction T using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add T T' hT hT' =>
      simp only [map_add]
      rw [hT, hT']
  | tmul x V =>
      induction V using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add V V' hV hV' =>
          simp only [TensorProduct.tmul_add, map_add]
          rw [hV, hV']
      | tmul y z => rfl

section General

/-- The head of a bar differential at a stage, in the spelling instance synthesis produces. -/
noncomputable abbrev barH (k m : ℕ) :
    TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier) m
      →ₗ[R] TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier (m + 1) :=
  barHeadₗ ε (barPower ε k).carrier m

/-- The tail of a bar differential at a stage, in the spelling instance synthesis produces. -/
noncomputable abbrev barT (k m : ℕ) :
    TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier) m
      →ₗ[R] TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier (m + 1) :=
  tensorRightDegOneₗ (M := barShiftFamily ε)
    (N := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
    (N' := (barPower ε k).carrier) (fun b => barD ε k b) m

/-- The head one stage up, with the coefficient family unfolded so that all three terms of the
inductive step share one spelling. -/
noncomputable abbrev barHsucc (k m : ℕ) :
    TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε)
          (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)) m
      →ₗ[R] TensorCarrier (R := R) (barShiftFamily ε)
        (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) (m + 1) :=
  barHeadₗ ε (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) m

/-- The tail of the tail, in the same spelling. -/
noncomputable abbrev barTT (k m : ℕ) :
    TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε)
          (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)) m
      →ₗ[R] TensorCarrier (R := R) (barShiftFamily ε)
        (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) (m + 1) :=
  tensorRightDegOneₗ (M := barShiftFamily ε)
    (N := fun b => TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier) b)
    (N' := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
    (fun b => barT ε k b) m

/-- The tail of the head, in the same spelling. -/
noncomputable abbrev barTH (k m : ℕ) :
    TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε)
          (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)) m
      →ₗ[R] TensorCarrier (R := R) (barShiftFamily ε)
        (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) (m + 1) :=
  tensorRightDegOneₗ (M := barShiftFamily ε)
    (N := fun b => TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier) b)
    (N' := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
    (fun b => barH ε k b) m

end General

section Componentwise

variable {N N' : ℕ → Type u} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  [∀ n, AddCommGroup (N' n)] [∀ n, Module R (N' n)]

/-- **The head after a tail of a tail, at one outer split, is the combined map.** -/
theorem barHead_tailtail_term (n c r : ℕ) (hp : c + (r + 1) = n + 1 + 1) (a a' : ℕ)
    (hs : a + a' + 1 = c) (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1))
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) N) n) (hix : a + (a' + r) = n) :
    barHeadTermₗ ε N' (n + 1) c (r + 1) hp a a' hs
        (tensorRightDegOneₗ (M := barShiftFamily ε)
          (fun b => tensorRightDegOneₗ (M := barShiftFamily ε) g b) n F)
      = ((-1 : R)) ^ (a + a') • barMulTail ε hs (g r)
        (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a))
          (barProj (M := barShiftFamily ε) (N := N) ⟨(a', r), rfl⟩) (F ⟨(a, a' + r), hix⟩)) := by
  rw [barHeadTermₗ_eq_comp]
  rw [show tensorRightDegOneₗ (M := barShiftFamily ε)
        (fun b => tensorRightDegOneₗ (M := barShiftFamily ε) g b) n F ⟨(a, a' + (r + 1)), by omega⟩
      = ((-1 : R)) ^ a • TensorProduct.map LinearMap.id
        (tensorRightDegOneₗ (M := barShiftFamily ε) g (a' + r)) (F ⟨(a, a' + r), hix⟩) from
      tensorRightDegOneₗ_succ (M := barShiftFamily ε)
        (fun b => tensorRightDegOneₗ (M := barShiftFamily ε) g b) n a (a' + r) F _]
  rw [map_smul, map_smul, map_smul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    LinearMap.comp_id,
    show (barProj (M := barShiftFamily ε) (N := N') ⟨(a', r + 1), rfl⟩).comp
        (tensorRightDegOneₗ (M := barShiftFamily ε) g (a' + r))
      = ((-1 : R)) ^ a' • (TensorProduct.map (LinearMap.id (R := R)
          (M := barShiftFamily ε a')) (g r)).comp
        (barProj (M := barShiftFamily ε) (N := N) ⟨(a', r), rfl⟩) from by
      refine LinearMap.ext fun V => ?_
      show tensorRightDegOneₗ (M := barShiftFamily ε) g (a' + r) V ⟨(a', r + 1), rfl⟩ = _
      rw [tensorRightDegOneₗ_succ]
      rfl,
    TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul, map_smul, smul_smul, ← pow_add]
  refine congrArg (fun z => ((-1 : R)) ^ (a + a') • z) ?_
  have hsplit : TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a))
        ((TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a')) (g r)).comp
          (barProj (M := barShiftFamily ε) (N := N) ⟨(a', r), rfl⟩))
      = (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a))
          (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a')) (g r))).comp
        (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a))
          (barProj (M := barShiftFamily ε) (N := N) ⟨(a', r), rfl⟩)) := by
    rw [← TensorProduct.map_comp, LinearMap.comp_id]
  rw [hsplit, LinearMap.comp_apply]
  exact barMulTail_first ε hs (g r) _

/-- **A tail after the head, at one outer split, is the combined map.** -/
theorem barHead_tail_term (n c r : ℕ) (hq : c + r = n + 1) (a a' : ℕ) (hs : a + a' + 1 = c)
    (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1))
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) N) n) (hix : a + (a' + r) = n) :
    TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε c)) (g r)
        (barHeadTermₗ ε N n c r hq a a' hs F)
      = barMulTail ε hs (g r)
        (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a))
          (barProj (M := barShiftFamily ε) (N := N) ⟨(a', r), rfl⟩) (F ⟨(a, a' + r), hix⟩)) := by
  rw [barHeadTermₗ_eq_comp]
  exact barMulTail_second ε hs (g r) _

set_option maxHeartbeats 1000000 in
/-- **The head and a tail of a tail cancel**, componentwise. -/
theorem barHead_comm_tail_apply (n c e : ℕ) (hp : c + e = n + 1 + 1)
    (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1))
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) N) n) :
    barHeadₗ ε N' (n + 1)
        (tensorRightDegOneₗ (M := barShiftFamily ε)
          (fun b => tensorRightDegOneₗ (M := barShiftFamily ε) g b) n F) ⟨(c, e), hp⟩
      + tensorRightDegOneₗ (M := barShiftFamily ε) g (n + 1)
        (barHeadₗ ε N n F) ⟨(c, e), hp⟩ = 0 := by
  cases e with
  | zero =>
      rw [tensorRightDegOneₗ_zero, add_zero, barHead_apply]
      refine Finset.sum_eq_zero fun s _ => ?_
      obtain ⟨⟨a, a'⟩, hsa⟩ := s
      have hpc : c + 0 = n + 1 + 1 := hp
      rw [barHeadTermₗ_eq_comp]
      cases a' with
      | zero =>
          have hsc : a + 0 + 1 = c := hsa
          rw [show tensorRightDegOneₗ (M := barShiftFamily ε)
                (fun b => tensorRightDegOneₗ (M := barShiftFamily ε) g b) n F
                ⟨(a, 0 + 0), by omega⟩ = 0 from
              tensorRightDegOneₗ_zero (M := barShiftFamily ε)
                (fun b => tensorRightDegOneₗ (M := barShiftFamily ε) g b) n a F _,
            map_zero, map_zero, map_zero]
      | succ a'' =>
          have hsc : a + (a'' + 1) + 1 = c := hsa
          rw [show tensorRightDegOneₗ (M := barShiftFamily ε)
                (fun b => tensorRightDegOneₗ (M := barShiftFamily ε) g b) n F
                ⟨(a, a'' + 1 + 0), by omega⟩
              = ((-1 : R)) ^ a • TensorProduct.map LinearMap.id
                (tensorRightDegOneₗ (M := barShiftFamily ε) g a'')
                (F ⟨(a, a''), by omega⟩) from
              tensorRightDegOneₗ_succ (M := barShiftFamily ε)
                (fun b => tensorRightDegOneₗ (M := barShiftFamily ε) g b) n a a'' F _,
            map_smul, map_smul, map_smul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
            LinearMap.comp_id,
            show (barProj (M := barShiftFamily ε) (N := N') ⟨(a'' + 1, 0), rfl⟩).comp
                (tensorRightDegOneₗ (M := barShiftFamily ε) g a'') = 0 from by
              refine LinearMap.ext fun V => ?_
              show tensorRightDegOneₗ (M := barShiftFamily ε) g a'' V ⟨(a'' + 1, 0), rfl⟩ = _
              rw [tensorRightDegOneₗ_zero]
              rfl,
            TensorProduct.map_zero_right, LinearMap.zero_apply, map_zero, map_zero, smul_zero]
  | succ r =>
      rw [barHead_apply,
        show tensorRightDegOneₗ (M := barShiftFamily ε) g (n + 1) (barHeadₗ ε N n F)
            ⟨(c, r + 1), hp⟩
          = ((-1 : R)) ^ c • TensorProduct.map LinearMap.id (g r)
            (barHeadₗ ε N n F ⟨(c, r), by omega⟩) from
          tensorRightDegOneₗ_succ (M := barShiftFamily ε) g (n + 1) c r (barHeadₗ ε N n F) _,
        barHead_apply, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun s _ => ?_
      obtain ⟨⟨a, a'⟩, hsa⟩ := s
      have hsc : a + a' + 1 = c := hsa
      have hpc : c + (r + 1) = n + 1 + 1 := hp
      rw [barHead_tailtail_term ε n c r hp a a' hsa g F (by omega),
        barHead_tail_term ε n c r (by omega) a a' hsa g F (by omega)]
      exact barMulTail_cancel ε hsa (g r) _

section Induction

set_option maxHeartbeats 1000000 in
/-- **The bar differential squares to zero.** -/
theorem barD_sq : ∀ (k n : ℕ) (F : (barPower ε (k + 2)).carrier n),
    barD ε k (n + 1) (barD ε (k + 1) n F) = 0
  | 0, n, F => by
      rw [barD_zero]
      rfl
  | (k + 1), n, F => by
    have hIH : ∀ (b : ℕ) (G : (barPower ε (k + 2)).carrier b),
        barD ε k (b + 1) (barD ε (k + 1) b G) = 0 := fun b G => barD_sq k b G
    have hsplit : barD ε (k + 2) n F
        = barHsucc ε k n F + (barTH ε k n F + barTT ε k n F) := by
      show barHsucc ε k n F
          + tensorRightDegOneₗ (M := barShiftFamily ε)
            (N := fun b => TensorCarrier (R := R) (barShiftFamily ε)
              (TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier) b)
            (N' := fun b => TensorCarrier (R := R) (barShiftFamily ε)
              (barPower ε k).carrier b) (fun b => barD ε (k + 1) b) n F = _
      refine congrArg (fun z => barHsucc ε k n F + z) ?_
      rw [show (fun b => barD ε (k + 1) b) = (fun b => barH ε k b + barT ε k b) from
        funext fun b => barD_succ ε k b]
      exact tensorRightDegOne_add_map (M := barShiftFamily ε) _ _ n F
    have hout : ∀ V : TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier) (n + 1),
        barD ε (k + 1) (n + 1) V = barH ε k (n + 1) V + barT ε k (n + 1) V := fun V => by
      rw [barD_succ]
      rfl
    have hzero : barT ε k (n + 1) (barTH ε k n F + barTT ε k n F) = 0 := by
      have hcomp := tensorRightDegOne_comp (M := barShiftFamily ε)
        (N := fun b => TensorCarrier (R := R) (barShiftFamily ε)
          (TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier) b)
        (N' := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
        (N'' := (barPower ε k).carrier)
        (fun b => barD ε (k + 1) b) (fun b => barD ε k b)
        (fun b => LinearMap.ext fun G => hIH b G) n F
      show barT ε k (n + 1) (barTH ε k n F + barTT ε k n F) = 0
      rw [show barTH ε k n F + barTT ε k n F
          = tensorRightDegOneₗ (M := barShiftFamily ε)
            (N := fun b => TensorCarrier (R := R) (barShiftFamily ε)
              (TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier) b)
            (N' := fun b => TensorCarrier (R := R) (barShiftFamily ε)
              (barPower ε k).carrier b) (fun b => barD ε (k + 1) b) n F from by
        rw [show (fun b => barD ε (k + 1) b) = (fun b => barH ε k b + barT ε k b) from
          funext fun b => barD_succ ε k b]
        exact (tensorRightDegOne_add_map (M := barShiftFamily ε) _ _ n F).symm]
      exact hcomp
    rw [hsplit, hout, map_add, map_add]
    funext p
    obtain ⟨⟨c, e⟩, hp⟩ := p
    have h12 := barHead_sq_add (ε := ε) (Z := (barPower ε k).carrier) n c e hp F
    have h34 := barHead_comm_tail_apply (ε := ε)
      (N := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
      (N' := (barPower ε k).carrier) n c e hp (fun b => barD ε k b) F
    have h56 : barT ε k (n + 1) (barTH ε k n F + barTT ε k n F) ⟨(c, e), hp⟩ = 0 := by
      rw [hzero]
      rfl
    show (barH ε k (n + 1) (barHsucc ε k n F) ⟨(c, e), hp⟩
        + (barH ε k (n + 1) (barTH ε k n F) ⟨(c, e), hp⟩
          + barH ε k (n + 1) (barTT ε k n F) ⟨(c, e), hp⟩))
      + barT ε k (n + 1) (barHsucc ε k n F + (barTH ε k n F + barTT ε k n F))
        ⟨(c, e), hp⟩ = 0
    rw [map_add]
    show (barH ε k (n + 1) (barHsucc ε k n F) ⟨(c, e), hp⟩
        + (barH ε k (n + 1) (barTH ε k n F) ⟨(c, e), hp⟩
          + barH ε k (n + 1) (barTT ε k n F) ⟨(c, e), hp⟩))
      + (barT ε k (n + 1) (barHsucc ε k n F) ⟨(c, e), hp⟩
        + barT ε k (n + 1) (barTH ε k n F + barTT ε k n F) ⟨(c, e), hp⟩) = 0
    rw [h56, add_zero]
    calc barH ε k (n + 1) (barHsucc ε k n F) ⟨(c, e), hp⟩
          + (barH ε k (n + 1) (barTH ε k n F) ⟨(c, e), hp⟩
            + barH ε k (n + 1) (barTT ε k n F) ⟨(c, e), hp⟩)
          + barT ε k (n + 1) (barHsucc ε k n F) ⟨(c, e), hp⟩
        = (barH ε k (n + 1) (barHsucc ε k n F) ⟨(c, e), hp⟩
            + barH ε k (n + 1) (barTH ε k n F) ⟨(c, e), hp⟩)
          + (barH ε k (n + 1) (barTT ε k n F) ⟨(c, e), hp⟩
            + barT ε k (n + 1) (barHsucc ε k n F) ⟨(c, e), hp⟩) := by abel
      _ = 0 := by rw [h12, h34, add_zero]

end Induction

end Componentwise

end GaloisForLFunctions.HTGeometry
