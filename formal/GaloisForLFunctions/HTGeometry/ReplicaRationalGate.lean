import GaloisForLFunctions.HTGeometry.AllReplicaSiteString

/-!
# The rational replicated one-site rotation gate

Placing the invertible element `1 + s i σ` on one physical site of every replica gives a matrix
whose conjugation action is an exact rational deformation of the identity.  Two facts make it the
right symmetry for the collective Pauli family.

Conjugation acts on one replica at a time: all the other replica factors cancel against their
partners, so a collective Pauli string is sent to a fixed linear combination of itself and the
string obtained by multiplying the rotation letter into the physical word.

The sandwich is a polynomial in the scale whose linear coefficient is exactly the collective
commutator of the rotation generator.  Rational conjugation at enough scales therefore recovers
the infinitesimal generator with no limit.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Pauli matrices whose labels have disjoint supports commute. -/
theorem commute_finitePauliMatrix_of_disjoint {S T : σ → Option (Fin 3)}
    (h : Disjoint (labelSupport S) (labelSupport T)) :
    Commute (finitePauliMatrix S) (finitePauliMatrix T) := by
  show finitePauliMatrix S * finitePauliMatrix T = finitePauliMatrix T * finitePauliMatrix S
  rw [finitePauliMatrix_mul' S T, finitePauliMatrix_mul' T S,
    optPhaseProd_eq_one_of_disjoint h, optPhaseProd_eq_one_of_disjoint h.symm,
    optMulLabel_comm S T]

variable (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The rational rotation of scale `s` at one physical site, applied in every replica of a set. -/
def replicaGate (v : I) (c : Fin 3) (T : Finset R) (s : ℂ) :
    Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ :=
  ∑ S ∈ T.powerset, (s * Complex.I) ^ S.card • finitePauliMatrix (replicaSetLabel I R v c S)

variable {I R}

theorem replicaGate_empty (v : I) (c : Fin 3) (s : ℂ) :
    replicaGate I R v c ∅ s = 1 := by
  classical
  rw [replicaGate, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero,
    one_smul]
  have hnone : replicaSetLabel I R v c ∅ = fun _ : I × R => (none : Option (Fin 3)) := by
    funext q
    rw [replicaSetLabel_apply, if_neg (fun hc => absurd hc.2 (Finset.notMem_empty q.2))]
  rw [hnone, finitePauliMatrix_const_none]

theorem pauli_mul_replicaSetLabel {v : I} {c : Fin 3} {ℓ : R} {S : Finset R} (hℓ : ℓ ∉ S) :
    finitePauliMatrix (siteLabel ((v, ℓ) : I × R) c) *
        finitePauliMatrix (replicaSetLabel I R v c S) =
      finitePauliMatrix (replicaSetLabel I R v c (insert ℓ S)) := by
  rw [finitePauliMatrix_mul' (siteLabel ((v, ℓ) : I × R) c) (replicaSetLabel I R v c S),
    optPhaseProd_eq_one_of_disjoint (disjoint_siteLabel_replicaSetLabel hℓ), one_smul,
    optMulLabel_siteLabel_replicaSetLabel hℓ]

/-- The gate factors one replica at a time. -/
theorem replicaGate_insert (v : I) (c : Fin 3) {ℓ : R} {T : Finset R} (hℓ : ℓ ∉ T) (s : ℂ) :
    replicaGate I R v c (insert ℓ T) s =
      (1 + (s * Complex.I) • finitePauliMatrix (siteLabel ((v, ℓ) : I × R) c)) *
        replicaGate I R v c T s := by
  classical
  have hsecond : (∑ S ∈ T.powerset, (s * Complex.I) ^ (insert ℓ S).card •
      finitePauliMatrix (replicaSetLabel I R v c (insert ℓ S))) =
      (s * Complex.I) • (finitePauliMatrix (siteLabel ((v, ℓ) : I × R) c) *
        replicaGate I R v c T s) := by
    rw [replicaGate, Matrix.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hℓS : ℓ ∉ S := fun hc => hℓ (Finset.mem_powerset.mp hS hc)
    rw [Matrix.mul_smul, smul_smul, ← pow_succ', pauli_mul_replicaSetLabel hℓS,
      Finset.card_insert_of_notMem hℓS]
  rw [replicaGate, Finset.sum_powerset_insert hℓ, ← replicaGate, hsecond, add_mul, one_mul,
    Matrix.smul_mul]

theorem commute_pauli_replicaGate (v : I) (c : Fin 3) (ℓ : R) (T : Finset R) (s : ℂ) :
    Commute (finitePauliMatrix (siteLabel ((v, ℓ) : I × R) c)) (replicaGate I R v c T s) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      rw [replicaGate_empty]
      exact Commute.one_right _
  | insert m T hm ih =>
      rw [replicaGate_insert v c hm]
      refine Commute.mul_right ?_ ih
      refine Commute.add_right (Commute.one_right _) (Commute.smul_right ?_ _)
      by_cases h : ℓ = m
      · rw [h]
        exact Commute.refl _
      · exact commute_finitePauliMatrix_siteLabel (fun hc => h (congrArg Prod.snd hc)) c c

theorem commute_replicaGate_of_forall (v : I) (c : Fin 3) (T : Finset R) (s : ℂ)
    {Y : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ}
    (hY : ∀ ℓ ∈ T, Commute Y (finitePauliMatrix (siteLabel ((v, ℓ) : I × R) c))) :
    Commute Y (replicaGate I R v c T s) := by
  classical
  revert hY
  induction T using Finset.induction_on with
  | empty =>
      intro _
      rw [replicaGate_empty]
      exact Commute.one_right _
  | insert m T hm ih =>
      intro hY
      rw [replicaGate_insert v c hm]
      refine Commute.mul_right ?_ (ih fun ℓ hℓ => hY ℓ (Finset.mem_insert_of_mem hℓ))
      exact Commute.add_right (Commute.one_right _)
        (Commute.smul_right (hY m (Finset.mem_insert_self m T)) _)

theorem square_expand
    (P : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ)
    (a b : ℂ) :
    (1 + a • P) * (1 + b • P) = 1 + (a + b) • P + (a * b) • (P * P) := by
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, add_smul, mul_comm b a]
  abel

theorem scale_prod (s : ℂ) : (s * Complex.I) * ((-s) * Complex.I) = s ^ 2 := by
  calc (s * Complex.I) * ((-s) * Complex.I)
      = -(s * s) * (Complex.I * Complex.I) := by ring
    _ = -(s * s) * (-1) := by rw [Complex.I_mul_I]
    _ = s ^ 2 := by ring

/-- Opposite scales of the gate are inverse up to the scalar `(1+s²)` per replica. -/
theorem replicaGate_mul_neg (v : I) (c : Fin 3) (T : Finset R) (s : ℂ) :
    replicaGate I R v c T s * replicaGate I R v c T (-s) =
      ((1 + s ^ 2) ^ T.card) •
        (1 : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      rw [replicaGate_empty, replicaGate_empty, Matrix.one_mul, Finset.card_empty, pow_zero,
        one_smul]
  | insert m T hm ih =>
      rw [replicaGate_insert v c hm, replicaGate_insert v c hm]
      have hcomm : Commute (1 + ((-s) * Complex.I) •
          finitePauliMatrix (siteLabel ((v, m) : I × R) c)) (replicaGate I R v c T s) :=
        Commute.add_left (Commute.one_left _)
          (Commute.smul_left (commute_pauli_replicaGate v c m T s) _)
      have hpair : (1 + (s * Complex.I) • finitePauliMatrix (siteLabel ((v, m) : I × R) c)) *
          (1 + ((-s) * Complex.I) • finitePauliMatrix (siteLabel ((v, m) : I × R) c)) =
          (1 + s ^ 2) • (1 : Matrix (FiniteQubitConfiguration (I × R))
            (FiniteQubitConfiguration (I × R)) ℂ) := by
        rw [square_expand, finitePauliMatrix_mul_self, scale_prod]
        have hzero : (s * Complex.I) + ((-s) * Complex.I) = 0 := by ring
        rw [hzero, zero_smul, add_zero, add_smul, one_smul]
      calc ((1 + (s * Complex.I) • finitePauliMatrix (siteLabel ((v, m) : I × R) c)) *
              replicaGate I R v c T s) *
            ((1 + ((-s) * Complex.I) • finitePauliMatrix (siteLabel ((v, m) : I × R) c)) *
              replicaGate I R v c T (-s))
          = ((1 + (s * Complex.I) • finitePauliMatrix (siteLabel ((v, m) : I × R) c)) *
              (1 + ((-s) * Complex.I) • finitePauliMatrix (siteLabel ((v, m) : I × R) c))) *
              (replicaGate I R v c T s * replicaGate I R v c T (-s)) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (replicaGate I R v c T s), ← hcomm.eq,
              Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = ((1 + s ^ 2) • (1 : Matrix (FiniteQubitConfiguration (I × R))
              (FiniteQubitConfiguration (I × R)) ℂ)) * (((1 + s ^ 2) ^ T.card) • 1) := by
            rw [hpair, ih]
        _ = ((1 + s ^ 2) ^ (insert m T).card) • 1 := by
            rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
              Finset.card_insert_of_notMem hm, ← pow_succ']


theorem disjoint_replicaLabel_siteLabel {p : I → Option (Fin 3)} {m ℓ : R} (h : ℓ ≠ m)
    (v : I) (c : Fin 3) :
    Disjoint (labelSupport (replicaLabel I R p m))
      (labelSupport (siteLabel ((v, ℓ) : I × R) c)) := by
  classical
  rw [labelSupport_siteLabel]
  refine Finset.disjoint_right.mpr fun q hq hq' => ?_
  rw [Finset.mem_singleton] at hq
  have hsub := labelSupport_replicaLabel_subset (I := I) (R := R) p m hq'
  rw [Finset.mem_filter, hq] at hsub
  exact h hsub.2

theorem finitePauliConjugationSign_siteLabel_replicaLabel (v : I) (c : Fin 3)
    (p : I → Option (Fin 3)) (m : R) :
    finitePauliConjugationSign (siteLabel ((v, m) : I × R) c) (replicaLabel I R p m) =
      boolPauliConjugationSign (some c) (p v) := by
  classical
  rw [finitePauliConjugationSign, Finset.prod_eq_single ((v, m) : I × R)]
  · rw [siteLabel_apply, if_pos rfl, replicaLabel_apply, if_pos rfl]
  · intro q _ hq
    rw [siteLabel_apply, if_neg hq, boolPauliConjugationSign, if_pos (Or.inl rfl)]
  · intro hcon
    exact absurd (Finset.mem_univ ((v, m) : I × R)) hcon

theorem sandwich_expand
    (P W : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ)
    (a : ℂ) :
    (1 + a • P) * W * (1 + (-a) • P) =
      W + a • (P * W - W * P) + (-(a * a)) • (P * W * P) := by
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, smul_sub, neg_smul, mul_neg]
  abel

/-- **Conjugation acts one replica at a time.**  All the other replica factors of the gate cancel
against their opposite-scale partners. -/
theorem replicaGate_conj_replicaLabel (v : I) (c : Fin 3) (s : ℂ) (p : I → Option (Fin 3))
    (m : R) :
    replicaGate I R v c Finset.univ s * finitePauliMatrix (replicaLabel I R p m) *
        replicaGate I R v c Finset.univ (-s) =
      ((1 + s ^ 2) ^ (Fintype.card R - 1)) •
        ((1 + (s * Complex.I) • finitePauliMatrix (siteLabel ((v, m) : I × R) c)) *
          finitePauliMatrix (replicaLabel I R p m) *
          (1 + ((-s) * Complex.I) • finitePauliMatrix (siteLabel ((v, m) : I × R) c))) := by
  classical
  have hm : m ∉ Finset.univ.erase m := Finset.notMem_erase m _
  have huniv : (Finset.univ : Finset R) = insert m (Finset.univ.erase m) :=
    (Finset.insert_erase (Finset.mem_univ m)).symm
  set P := finitePauliMatrix (siteLabel ((v, m) : I × R) c) with hPdef
  set W := finitePauliMatrix (replicaLabel I R p m) with hWdef
  set E1 := replicaGate I R v c (Finset.univ.erase m) s with hE1
  set E2 := replicaGate I R v c (Finset.univ.erase m) (-s) with hE2
  have hcW : Commute W E1 := by
    refine commute_replicaGate_of_forall v c _ s fun ℓ hℓ => ?_
    exact commute_finitePauliMatrix_of_disjoint
      (disjoint_replicaLabel_siteLabel (Finset.ne_of_mem_erase hℓ) v c)
  have hcg : Commute (1 + ((-s) * Complex.I) • P) E1 :=
    Commute.add_left (Commute.one_left _)
      (Commute.smul_left (commute_pauli_replicaGate v c m _ s) _)
  have hgate1 : replicaGate I R v c Finset.univ s = (1 + (s * Complex.I) • P) * E1 := by
    rw [hE1, hPdef, ← replicaGate_insert v c hm, ← huniv]
  have hgate2 : replicaGate I R v c Finset.univ (-s) = (1 + ((-s) * Complex.I) • P) * E2 := by
    rw [hE2, hPdef, ← replicaGate_insert v c hm, ← huniv]
  have h1 : ((1 + (s * Complex.I) • P) * E1) * W = ((1 + (s * Complex.I) • P) * W) * E1 := by
    rw [Matrix.mul_assoc, hcW.symm.eq, ← Matrix.mul_assoc]
  have h2 : E1 * ((1 + ((-s) * Complex.I) • P) * E2) =
      (1 + ((-s) * Complex.I) • P) * (E1 * E2) := by
    rw [← Matrix.mul_assoc, ← hcg.eq, Matrix.mul_assoc]
  rw [hgate1, hgate2]
  calc ((1 + (s * Complex.I) • P) * E1) * W * ((1 + ((-s) * Complex.I) • P) * E2)
      = (((1 + (s * Complex.I) • P) * W) * E1) * ((1 + ((-s) * Complex.I) • P) * E2) := by
        rw [h1]
    _ = ((1 + (s * Complex.I) • P) * W) * (E1 * ((1 + ((-s) * Complex.I) • P) * E2)) :=
        Matrix.mul_assoc _ _ _
    _ = ((1 + (s * Complex.I) • P) * W) * ((1 + ((-s) * Complex.I) • P) * (E1 * E2)) := by
        rw [h2]
    _ = (((1 + (s * Complex.I) • P) * W) * (1 + ((-s) * Complex.I) • P)) * (E1 * E2) :=
        (Matrix.mul_assoc _ _ _).symm
    _ = (((1 + (s * Complex.I) • P) * W) * (1 + ((-s) * Complex.I) • P)) *
          (((1 + s ^ 2) ^ (Finset.univ.erase m).card) • 1) := by
        rw [hE1, hE2, replicaGate_mul_neg]
    _ = ((1 + s ^ 2) ^ (Fintype.card R - 1)) •
          ((1 + (s * Complex.I) • P) * W * (1 + ((-s) * Complex.I) • P)) := by
        rw [Matrix.mul_smul, Matrix.mul_one,
          Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ]


/-- **The gate conjugates a collective Pauli string inside the span of collective strings on the
same physical support.** -/
theorem replicaGate_conj_collectivePauliString (v : I) (c : Fin 3) (s : ℂ)
    (p : I → Option (Fin 3)) :
    replicaGate I R v c Finset.univ s * collectivePauliString I R p *
        replicaGate I R v c Finset.univ (-s) =
      ((1 + s ^ 2) ^ (Fintype.card R - 1) *
          (1 + s ^ 2 * boolPauliConjugationSign (some c) (p v))) •
          collectivePauliString I R p +
        ((1 + s ^ 2) ^ (Fintype.card R - 1) * ((s * Complex.I) *
            (optPhaseProd (siteLabel v c) p - optPhaseProd p (siteLabel v c)))) •
          collectivePauliString I R (optMulLabel (siteLabel v c) p) := by
  classical
  have hterm : ∀ m : R, replicaGate I R v c Finset.univ s *
      finitePauliMatrix (replicaLabel I R p m) * replicaGate I R v c Finset.univ (-s) =
      ((1 + s ^ 2) ^ (Fintype.card R - 1)) •
        (finitePauliMatrix (replicaLabel I R p m) +
          (s * Complex.I) •
            ringCommutator (finitePauliMatrix (replicaLabel I R (siteLabel v c) m))
              (finitePauliMatrix (replicaLabel I R p m)) +
          s ^ 2 • (boolPauliConjugationSign (some c) (p v) •
            finitePauliMatrix (replicaLabel I R p m))) := by
    intro m
    rw [replicaGate_conj_replicaLabel v c s p m]
    congr 1
    have hneg : ((-s) * Complex.I) = -(s * Complex.I) := by ring
    rw [hneg, sandwich_expand, replicaLabel_siteLabel]
    have hsq : -((s * Complex.I) * (s * Complex.I)) = s ^ 2 := by
      calc -((s * Complex.I) * (s * Complex.I))
          = -((s * s) * (Complex.I * Complex.I)) := by ring
        _ = -((s * s) * (-1)) := by rw [Complex.I_mul_I]
        _ = s ^ 2 := by ring
    rw [hsq, finitePauliMatrix_conj, finitePauliConjugationSign_siteLabel_replicaLabel]
    rfl
  have hdistrib : replicaGate I R v c Finset.univ s * collectivePauliString I R p *
      replicaGate I R v c Finset.univ (-s) =
      ∑ m : R, (replicaGate I R v c Finset.univ s * finitePauliMatrix (replicaLabel I R p m) *
        replicaGate I R v c Finset.univ (-s)) := by
    rw [collectivePauliString, Matrix.mul_sum, Finset.sum_mul]
  have hbracket : (∑ m : R,
      ringCommutator (finitePauliMatrix (replicaLabel I R (siteLabel v c) m))
        (finitePauliMatrix (replicaLabel I R p m))) =
      (optPhaseProd (siteLabel v c) p - optPhaseProd p (siteLabel v c)) •
        collectivePauliString I R (optMulLabel (siteLabel v c) p) := by
    rw [← collectivePauliString_bracket (I := I) (R := R) (siteLabel v c) p,
      collectivePauliString, collectivePauliString,
      ringCommutator_sum_diagonal]
    intro l n hln
    exact commute_finitePauliMatrix_of_disjoint (disjoint_replicaLabel hln _ _)
  rw [hdistrib, Finset.sum_congr rfl fun m _ => hterm m, ← Finset.smul_sum,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
    ← Finset.smul_sum, hbracket, ← collectivePauliString]
  module


theorem replicaSetLabel_singleton (v : I) (c : Fin 3) (ℓ : R) :
    replicaSetLabel I R v c {ℓ} = siteLabel ((v, ℓ) : I × R) c := by
  classical
  funext q
  rw [replicaSetLabel_apply, siteLabel_apply]
  by_cases h : q = ((v, ℓ) : I × R)
  · rw [if_pos h, if_pos ⟨by rw [h], by rw [h]; exact Finset.mem_singleton_self ℓ⟩]
  · rw [if_neg h, if_neg (fun hc => h (Prod.ext hc.1 (Finset.mem_singleton.mp hc.2)))]

theorem finitePauliMatrix_replicaSetLabel_empty (v : I) (c : Fin 3) :
    finitePauliMatrix (replicaSetLabel I R v c ∅) = 1 := by
  classical
  have hnone : replicaSetLabel I R v c ∅ = fun _ : I × R => (none : Option (Fin 3)) := by
    funext q
    rw [replicaSetLabel_apply, if_neg (fun hc => absurd hc.2 (Finset.notMem_empty q.2))]
  rw [hnone, finitePauliMatrix_const_none]

/-- **The conjugated sandwich is a polynomial in the scale**, graded by the total number of
replicas carrying the rotation letter. -/
theorem replicaGate_sandwich_eq_gradedSum (v : I) (c : Fin 3) (s : ℂ)
    (X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :
    replicaGate I R v c Finset.univ s * X * replicaGate I R v c Finset.univ (-s) =
      ∑ a : Finset R × Finset R, s ^ (a.1.card + a.2.card) •
        ((Complex.I ^ a.1.card * (-Complex.I) ^ a.2.card) •
          (finitePauliMatrix (replicaSetLabel I R v c a.1) * X *
            finitePauliMatrix (replicaSetLabel I R v c a.2))) := by
  classical
  have hscal : ∀ k j : ℕ, (s * Complex.I) ^ k * ((-s) * Complex.I) ^ j =
      s ^ (k + j) * (Complex.I ^ k * (-Complex.I) ^ j) := by
    intro k j
    rw [show ((-s) * Complex.I) = s * (-Complex.I) by ring, mul_pow, mul_pow, pow_add]
    ring
  rw [Fintype.sum_prod_type, replicaGate, replicaGate, Finset.powerset_univ, Finset.sum_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun S' _ => ?_
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, hscal]

/-- The linear coefficient of the sandwich polynomial is the collective commutator of the
rotation generator. -/
theorem replicaGate_gradedSum_degree_one (v : I) (c : Fin 3)
    (X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :
    (∑ a ∈ Finset.univ.filter fun a : Finset R × Finset R => a.1.card + a.2.card = 1,
      ((Complex.I ^ a.1.card * (-Complex.I) ^ a.2.card) •
        (finitePauliMatrix (replicaSetLabel I R v c a.1) * X *
          finitePauliMatrix (replicaSetLabel I R v c a.2)))) =
      Complex.I • ringCommutator (collectivePauliString I R (siteLabel v c)) X := by
  classical
  have hQ : collectivePauliString I R (siteLabel v c) =
      ∑ ℓ : R, finitePauliMatrix (siteLabel ((v, ℓ) : I × R) c) := by
    rw [collectivePauliString]
    exact Finset.sum_congr rfl fun ℓ _ => by rw [replicaLabel_siteLabel]
  have hinj1 : Set.InjOn (fun ℓ : R => (({ℓ} : Finset R), (∅ : Finset R)))
      ((Finset.univ : Finset R) : Set R) := by
    intro a _ b _ hab
    have h := congrArg Prod.fst hab
    simpa using h
  have hinj2 : Set.InjOn (fun ℓ : R => ((∅ : Finset R), ({ℓ} : Finset R)))
      ((Finset.univ : Finset R) : Set R) := by
    intro a _ b _ hab
    have h := congrArg Prod.snd hab
    simpa using h
  have hdisj : Disjoint (Finset.univ.image fun ℓ : R => (({ℓ} : Finset R), (∅ : Finset R)))
      (Finset.univ.image fun ℓ : R => ((∅ : Finset R), ({ℓ} : Finset R))) := by
    refine Finset.disjoint_left.mpr ?_
    rintro a ha ha'
    rw [Finset.mem_image] at ha ha'
    obtain ⟨ℓ, -, hℓ⟩ := ha
    obtain ⟨n, -, hn⟩ := ha'
    rw [← hℓ] at hn
    exact absurd (congrArg Prod.fst hn).symm (Finset.singleton_ne_empty ℓ)
  have hfiber : (Finset.univ.filter fun a : Finset R × Finset R => a.1.card + a.2.card = 1) =
      (Finset.univ.image fun ℓ : R => (({ℓ} : Finset R), (∅ : Finset R))) ∪
        (Finset.univ.image fun ℓ : R => ((∅ : Finset R), ({ℓ} : Finset R))) := by
    ext a
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨-, h⟩
      rcases Nat.add_eq_one_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp h2
        exact Or.inr ⟨ℓ, Finset.mem_univ ℓ,
          Prod.ext (Finset.card_eq_zero.mp h1).symm hℓ.symm⟩
      · obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp h1
        exact Or.inl ⟨ℓ, Finset.mem_univ ℓ,
          Prod.ext hℓ.symm (Finset.card_eq_zero.mp h2).symm⟩
    · rintro (⟨ℓ, -, hℓ⟩ | ⟨ℓ, -, hℓ⟩) <;> rw [← hℓ] <;>
        exact ⟨Finset.mem_univ _, by simp⟩
  rw [hfiber, Finset.sum_union hdisj, Finset.sum_image hinj1, Finset.sum_image hinj2]
  simp only [Finset.card_singleton, Finset.card_empty, pow_one, pow_zero, one_mul, mul_one,
    replicaSetLabel_singleton, finitePauliMatrix_replicaSetLabel_empty]
  rw [← Finset.sum_add_distrib, ringCommutator, hQ, Finset.sum_mul, Finset.mul_sum, smul_sub,
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [neg_smul, ← sub_eq_add_neg]

end GaloisForLFunctions.HTGeometry
