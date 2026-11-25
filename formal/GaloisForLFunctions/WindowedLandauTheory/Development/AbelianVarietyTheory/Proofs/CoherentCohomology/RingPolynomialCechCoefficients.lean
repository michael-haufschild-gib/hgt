import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.RingPolynomialLaurent
import Mathlib.Tactic.Linarith

/-! Admissible Laurent coefficients present the Čech complex of each negative twist. -/

noncomputable section

open HTGeometry MvPolynomial AddMonoidAlgebra GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.SchemeCohomology.RingPolynomialCech

universe u

variable {K : Type u} [CommRing K] {ι ν : Type}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section Adm

variable [Fintype ι]

variable (K) in
/-- **The admissible Laurent polynomials**: projective degree `-e`, nonnegative fibre exponents,
negative projective exponents only at indices of `s`. -/
def admSubgroup (s : Finset ι) (e : ℕ) : AddSubgroup (LaurentRing K ι ν) where
  carrier := {f | ∀ a ∈ f.coeff.support, negSupp a ⊆ s ∧ DegAdm e a}
  zero_mem' := by
    intro a ha
    simp at ha
  add_mem' := by
    classical
    intro f g hf hg a ha
    rw [AddMonoidAlgebra.coeff_add] at ha
    rcases Finset.mem_union.mp (Finsupp.support_add ha) with h | h
    exacts [hf a h, hg a h]
  neg_mem' := by
    intro f hf a ha
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.support_neg] at ha
    exact hf a ha

theorem mem_admSubgroup {s : Finset ι} {e : ℕ} {f : LaurentRing K ι ν} :
    f ∈ admSubgroup K s e ↔ ∀ a ∈ f.coeff.support, negSupp a ⊆ s ∧ DegAdm e a := Iff.rfl

variable [DecidableEq ι] [Fintype ν] [DecidableEq ν]

/-- **Degree `-e` fractions are admissible.** -/
theorem laurentLoc_mem_admSubgroup {s : Finset ι} {e : ℕ} {y : LocAt (projCoord K ι ν) s}
    (hy : y ∈ twPart (projGrading K ι ν) (projCoord K ι ν) s e) :
    laurentLoc K ι ν s y ∈ admSubgroup K s e := by
  refine (AddSubgroup.closure_le ((admSubgroup K s e).comap
    (laurentLoc K ι ν s).toAddMonoidHom)).mpr ?_ hy
  rintro _ ⟨m, i, x, hx, hdeg, rfl⟩
  change laurentLoc K ι ν s (frac (projCoord K ι ν) s m x) ∈ admSubgroup K s e
  rw [laurentLoc_frac, mem_admSubgroup]
  intro a ha
  rw [AddMonoidAlgebra.support_coeff_mul_single _ _ (fun y => by simp), support_laurentEmb,
    Finset.mem_map] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
  have hwt : ∑ k, b (Sum.inl k) = i := by
    rw [← weight_projWeight]
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp hx (MvPolynomial.mem_support_iff.mp hb)
  simp only [addRightEmbedding_apply]
  refine ⟨fun k hk => ?_, fun j => ?_, ?_⟩
  · have hk' := (Finset.mem_filter.mp hk).2
    rw [shift_apply_inl] at hk'
    by_contra hks
    rw [if_neg hks] at hk'
    omega
  · rw [shift_apply_inr]
    exact_mod_cast Nat.zero_le _
  · simp only [shift_apply_inl, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
    have h1 : ((i : ℕ) : ℤ) + e = m * s.card := by exact_mod_cast hdeg
    have h2 : ∑ k, ((b (Sum.inl k) : ℕ) : ℤ) = i := by exact_mod_cast hwt
    linarith

omit [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
theorem eq_sum_single (g : LaurentRing K ι ν) :
    g = ∑ c ∈ g.coeff.support, AddMonoidAlgebra.single c (g.coeff c) := by
  apply AddMonoidAlgebra.ext
  rw [AddMonoidAlgebra.coeff_sum]
  simp only [AddMonoidAlgebra.coeff_single]
  exact (Finsupp.sum_single g.coeff).symm

/-- **Every admissible Laurent polynomial is a degree `-e` fraction.** -/
theorem exists_laurentLoc_eq {s : Finset ι} {e : ℕ} {f : LaurentRing K ι ν}
    (hf : f ∈ admSubgroup K s e) :
    ∃ y ∈ twPart (projGrading K ι ν) (projCoord K ι ν) s e, laurentLoc K ι ν s y = f := by
  classical
  by_cases hf0 : f = 0
  · exact ⟨0, zero_mem _, by rw [map_zero, hf0]⟩
  set M₀ : ℕ := ∑ a ∈ f.coeff.support, ∑ k, (a (Sum.inl k)).natAbs with hM₀
  have hbound : ∀ a ∈ f.coeff.support, ∀ k, (a (Sum.inl k)).natAbs ≤ M₀ := by
    intro a ha k
    calc (a (Sum.inl k)).natAbs ≤ ∑ k', (a (Sum.inl k')).natAbs :=
          Finset.single_le_sum (f := fun k' => (a (Sum.inl k')).natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      _ ≤ M₀ := Finset.single_le_sum (f := fun a => ∑ k', (a (Sum.inl k')).natAbs)
          (fun _ _ => Nat.zero_le _) ha
  set g := f * AddMonoidAlgebra.single (M₀ • sExp s) (1 : K) with hg
  have hgsupp : g.coeff.support = f.coeff.support.map (addRightEmbedding (M₀ • sExp s)) :=
    AddMonoidAlgebra.support_coeff_mul_single _ _ (fun y => by simp) _
  have hshift : ∀ a : LaurentExp ι ν, ∀ k : ι,
      ((a + M₀ • sExp s : LaurentExp ι ν)) (Sum.inl k)
        = a (Sum.inl k) + if k ∈ s then (M₀ : ℤ) else 0 := by
    intro a k
    rw [Finsupp.add_apply, Finsupp.smul_apply, sExp_apply_inl]
    split_ifs <;> simp
  have hshift' : ∀ a : LaurentExp ι ν, ∀ j : ν,
      ((a + M₀ • sExp s : LaurentExp ι ν)) (Sum.inr j) = a (Sum.inr j) := by
    intro a j
    rw [Finsupp.add_apply, Finsupp.smul_apply, sExp_apply_inr]
    simp
  have hnonneg : ∀ c ∈ g.coeff.support, ∀ k, 0 ≤ c k := by
    intro c hc
    rw [hgsupp, Finset.mem_map] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    obtain ⟨hneg, hinr, -⟩ := hf a ha
    rintro (k | j)
    · simp only [addRightEmbedding_apply, hshift]
      by_cases hk : k ∈ s
      · rw [if_pos hk]
        have := hbound a ha k
        omega
      · rw [if_neg hk, add_zero]
        by_contra hlt
        exact hk (hneg (Finset.mem_filter.mpr ⟨Finset.mem_univ k, by omega⟩))
    · simp only [addRightEmbedding_apply, hshift']
      exact hinr j
  have hsum : ∀ c ∈ g.coeff.support, ∑ k, c (Sum.inl k) = (M₀ * s.card : ℕ) - (e : ℤ) := by
    intro c hc
    rw [hgsupp, Finset.mem_map] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    obtain ⟨-, -, hdeg⟩ := hf a ha
    simp only [addRightEmbedding_apply, hshift, Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hdeg]
    push_cast
    ring
  have hgne : g ≠ 0 := by
    intro hg0
    apply hf0
    have := congrArg (· * AddMonoidAlgebra.single (-(M₀ • sExp s)) (1 : K)) hg0
    simp only [zero_mul, hg, mul_assoc, single_mul_single_neg, mul_one] at this
    exact this
  obtain ⟨c₀, hc₀⟩ : g.coeff.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty,
      AddMonoidAlgebra.coeff_eq_zero]
    exact hgne
  have he : e ≤ M₀ * s.card := by
    have h1 := hsum c₀ hc₀
    have h2 : 0 ≤ ∑ k, c₀ (Sum.inl k) := Finset.sum_nonneg fun k _ => hnonneg c₀ hc₀ _
    omega
  set i := M₀ * s.card - e with hi
  set x : MvPolynomial (ι ⊕ ν) K := ∑ c ∈ g.coeff.support,
    monomial (Finsupp.mapRange Int.toNat (by simp) c) (g.coeff c) with hx
  have hxmem : x ∈ projGrading K ι ν i := by
    refine Submodule.sum_mem _ fun c hc => ?_
    refine isWeightedHomogeneous_monomial _ _ _ ?_
    rw [weight_projWeight]
    have h1 := hsum c hc
    have h2 : ∑ k, ((Finsupp.mapRange Int.toNat (by simp) c (Sum.inl k) : ℕ) : ℤ)
        = ∑ k, c (Sum.inl k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finsupp.mapRange_apply, Int.toNat_of_nonneg (hnonneg c hc _)]
    have h3 : ((∑ k, Finsupp.mapRange Int.toNat (by simp) c (Sum.inl k) : ℕ) : ℤ) = (i : ℤ) := by
      push_cast
      rw [h2, h1, hi]
      push_cast [he]
      ring
    exact_mod_cast h3
  have hemb : laurentEmb K ι ν x = g := by
    rw [hx, map_sum]
    conv_rhs => rw [eq_sum_single g]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [laurentEmb_monomial, castExp_toNatExp (hnonneg c hc)]
  refine ⟨frac (projCoord K ι ν) s M₀ x, frac_mem_twPart hxmem (by omega), ?_⟩
  rw [laurentLoc_frac, hemb, hg, mul_assoc, single_mul_single_neg, mul_one]

end Adm

section Exact

variable [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype ν] [DecidableEq ν]

variable (K ι ν) in
/-- The twisted Čech datum of `T`. -/
noncomputable abbrev polyTwCech (e : ℕ) : FinsetCechDatum ι :=
  twCech (projGrading K ι ν) (projCoord K ι ν) projCoord_mem e

/-- The underlying fraction, as an additive map. -/
noncomputable def twValHom {e : ℕ} (s : Finset ι) :
    (polyTwCech K ι ν e).obj s →+ LocAt (projCoord K ι ν) s :=
  (twPart (projGrading K ι ν) (projCoord K ι ν) s e).subtype

omit [Fintype ι] [LinearOrder ι] [Fintype ν] [DecidableEq ν] in
theorem twVal_eq_twValHom {e : ℕ} {s : Finset ι} (y : (polyTwCech K ι ν e).obj s) :
    twVal projCoord_mem y = twValHom s y := rfl

/-- The Laurent coefficients of a cochain. -/
noncomputable def laurentCoeffs {e : ℕ} (c : (polyTwCech K ι ν e).Cochain) :
    Finset ι → (LaurentExp ι ν →₀ K) :=
  fun I => (laurentLoc K ι ν I (twVal projCoord_mem (c I))).coeff

omit [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
theorem cechSign_intCast (I : Finset ι) (u : ι) :
    (((cechSign I u : ℤ)) : K) = cechSign I u := by
  simp [cechSign]

omit [Fintype ι] [Fintype ν] [DecidableEq ν] in
/-- **The Laurent coefficients intertwine the differentials.** -/
theorem laurentCoeffs_d {e : ℕ} (c : (polyTwCech K ι ν e).Cochain) (t : Finset ι) :
    laurentCoeffs ((polyTwCech K ι ν e).d c) t = monoCechD (laurentCoeffs c) t := by
  have hval : twVal projCoord_mem ((polyTwCech K ι ν e).d c t)
      = ∑ u ∈ t, (cechSign t u : ℤ) •
          resLoc (projCoord K ι ν) (Finset.erase_subset u t) (twVal projCoord_mem (c (t.erase u))) := by
    rw [twVal_eq_twValHom, FinsetCechDatum.d, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_zsmul]
    rfl
  rw [laurentCoeffs, hval, map_sum, AddMonoidAlgebra.coeff_sum, monoCechD]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_zsmul, laurentLoc_resLoc, ← cechSign_intCast (K := K), Int.cast_smul_eq_zsmul]
  rfl

end Exact

end GlobalTheory.SchemeCohomology.RingPolynomialCech
