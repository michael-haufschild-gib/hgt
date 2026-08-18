import GaloisForLFunctions.HTGeometry.AffineLineSimplyConnected

/-!
# Algebraic simple connectedness of affine space

Over an algebraically closed field of characteristic zero, a monic polynomial over a polynomial ring
in `k` variables whose resultant against its own derivative is a unit splits into monic linear
factors.  This is the statement that affine `k`-space carries no nontrivial connected finite étale
cover with a monogenic model.

The induction on `k` is elementary once the one-variable case
(`AffineLineSimplyConnected`) is available.  Over the algebraic closure of the fraction field of the
smaller polynomial ring the polynomial splits; the unit resultant makes every difference of two
roots a unit of that polynomial ring, hence a constant; so all roots equal one fixed polynomial —
`-(1/d)` times the subleading coefficient — plus constants, and translating by it produces a monic
polynomial in one fewer variable with the same resultant.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

/-- A commutative ring has the **étale splitting property** if every monic polynomial whose
resultant against its own derivative is a unit splits into monic linear factors. -/
def HasEtaleSplitting (B : Type*) [CommRing B] : Prop :=
  ∀ f : B[X], f.Monic → IsUnit (Polynomial.resultant f (Polynomial.derivative f)) →
    ∃ M : Multiset B, f = (M.map fun a => X - Polynomial.C a).prod

/-- An algebraically closed field has the étale splitting property, trivially. -/
theorem hasEtaleSplitting_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] :
    HasEtaleSplitting K := by
  intro f hf _
  refine ⟨f.roots, ?_⟩
  have h := Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits f) hf
  simpa using h

/-- A polynomial over an algebraically closed field with no root is a constant. -/
theorem natDegree_eq_zero_of_forall_eval_ne_zero {L : Type*} [Field L] [IsAlgClosed L]
    {p : L[X]} (h : ∀ s : L, p.eval s ≠ 0) : p.natDegree = 0 := by
  by_contra hdz
  have hne : p ≠ 0 := fun hp => h 0 (by simp [hp])
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p
    (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdz)).ne'
  exact h z hz

/-- **Constant shift.**  Over an algebraically closed field of characteristic zero, a monic
two-variable polynomial with separable fibres has all its roots equal to one fixed polynomial plus
constants; the fixed polynomial is `-(1/d)` times the subleading coefficient. -/
theorem exists_constant_shift {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]
    {g : L[X][X]} (hgm : g.Monic) (hd0 : g.natDegree ≠ 0)
    (hgsep : ∀ s : L, (biFibre g s).Separable) (h : L[X])
    (hh : (g.natDegree : L[X]) * h = - g.coeff (g.natDegree - 1)) :
    ∃ N : Multiset L, g = (N.map fun a => X - Polynomial.C (Polynomial.C a + h)).prod := by
  classical
  set d := g.natDegree with hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  obtain ⟨M, hM⟩ := exists_multiset_prod_of_forall_separable_algClosed d g hgm rfl hgsep
  have hcardM : Multiset.card M = d := by
    have h1 := congrArg Polynomial.natDegree hM
    rw [← hd, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    exact h1.symm
  -- any two roots differ by a constant
  have hdiffconst : ∀ a ∈ M, ∀ b ∈ M, (a - b).natDegree = 0 := by
    intro a ha b hb
    by_cases hab : a = b
    · simp [hab]
    refine natDegree_eq_zero_of_forall_eval_ne_zero ?_
    intro s hs
    have hpair : (a ::ₘ {b}) ≤ M := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hxa : x = a
      · subst hxa
        have hc1 : Multiset.count x (x ::ₘ {b}) = 1 := by
          simp [hab]
        rw [hc1]
        exact Multiset.one_le_count_iff_mem.mpr ha
      · by_cases hxb : x = b
        · subst hxb
          have hc1 : Multiset.count x (a ::ₘ {x}) = 1 := by
            simp [Ne.symm hab]
          rw [hc1]
          exact Multiset.one_le_count_iff_mem.mpr hb
        · simp [hxa, hxb]
    obtain ⟨N, hN⟩ := Multiset.le_iff_exists_add.mp hpair
    have hval : a.eval s = b.eval s := by
      have h2 := hs
      rw [Polynomial.eval_sub, sub_eq_zero] at h2
      exact h2
    have hsq : ¬ Squarefree (biFibre g s) := by
      have hfac : biFibre g s =
          (X - Polynomial.C (a.eval s)) * ((X - Polynomial.C (b.eval s)) *
            (N.map fun t : L[X] => X - Polynomial.C (t.eval s)).prod) := by
        rw [hM, hN]
        simp [biFibre, Polynomial.map_mul, Polynomial.map_multiset_prod, Multiset.map_map,
          Polynomial.map_sub]
      intro hsf
      have hdvd : (X - Polynomial.C (a.eval s)) * (X - Polynomial.C (a.eval s)) ∣ biFibre g s := by
        rw [hfac, hval]
        exact ⟨(N.map fun t : L[X] => X - Polynomial.C (t.eval s)).prod, by ring⟩
      exact (Polynomial.not_isUnit_X_sub_C (a.eval s)) (hsf _ hdvd)
    exact hsq (hgsep s).squarefree
  -- the sum of the roots
  have hsum : g.coeff (d - 1) = - M.sum := by
    have hnext : g.nextCoeff = - M.sum := by
      rw [hM, Polynomial.Monic.nextCoeff_multiset_prod _ _ (fun p _ => Polynomial.monic_X_sub_C _)]
      simp [Polynomial.nextCoeff_X_sub_C, Multiset.sum_map_neg']
    rw [← hnext, Polynomial.nextCoeff_of_natDegree_pos (by rw [← hd]; exact hdpos), hd]
  -- every root is `h` plus a constant
  have hrootconst : ∀ a ∈ M, (a - h).natDegree = 0 := by
    intro a ha
    have hdne : (d : L[X]) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact hd0
    have hkey : (d : L[X]) * (a - h) = (M.map fun b => a - b).sum := by
      rw [mul_sub, hh, hsum, neg_neg, Multiset.sum_map_sub, Multiset.map_const',
        Multiset.sum_replicate, hcardM, nsmul_eq_mul]
      simp
    have hdeg : ((M.map fun b => a - b).sum).natDegree = 0 := by
      refine Nat.le_zero.mp ?_
      refine (Polynomial.natDegree_multiset_sum_le _).trans
        (Multiset.max_le_of_forall_le _ _ ?_)
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hy
      exact le_of_eq (hdiffconst a ha b hb)
    have hnz : a - h ≠ 0 ∨ True := Or.inr trivial
    by_cases hz : a - h = 0
    · simp [hz]
    have h3 := congrArg Polynomial.natDegree hkey
    rw [Polynomial.natDegree_mul hdne hz, hdeg] at h3
    simpa using h3
  -- assemble
  refine ⟨M.map fun a => (a - h).coeff 0, ?_⟩
  rw [hM, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl ?_
  intro a ha
  simp only [Function.comp_apply]
  have hc := Polynomial.eq_C_of_natDegree_eq_zero (hrootconst a ha)
  have ha' : a = Polynomial.C ((a - h).coeff 0) + h := by
    rw [← hc]; ring
  exact congrArg (fun t : L[X] => X - Polynomial.C t) ha'

/-- **The étale splitting property passes to a polynomial extension.** -/
theorem hasEtaleSplitting_polynomial {B : Type*} [CommRing B] [IsDomain B] [Algebra ℚ B]
    (hB : HasEtaleSplitting B) : HasEtaleSplitting B[X] := by
  classical
  haveI : CharZero B := charZero_of_injective_algebraMap (algebraMap ℚ B).injective
  haveI : CharZero (FractionRing B) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective B (FractionRing B))
  haveI : CharZero (AlgebraicClosure (FractionRing B)) :=
    charZero_of_injective_algebraMap
      (algebraMap (FractionRing B) (AlgebraicClosure (FractionRing B))).injective
  intro f hf hres
  by_cases hd0 : f.natDegree = 0
  · exact ⟨0, by simpa using Polynomial.eq_one_of_monic_natDegree_zero hf hd0⟩
  obtain ⟨c, hcunit, hcres⟩ :
      ∃ c : B, IsUnit c ∧ Polynomial.resultant f (Polynomial.derivative f) = Polynomial.C c := by
    obtain ⟨r, hr, hrc⟩ := Polynomial.isUnit_iff.mp hres
    exact ⟨r, hr, hrc.symm⟩
  have hderdeg : (Polynomial.derivative f).natDegree = f.natDegree - 1 :=
    Polynomial.natDegree_derivative f
  have hbires : biResultant f = Polynomial.C c := by
    rw [biResultant, ← hderdeg, ← hcres]
  -- the shift, defined over `B`
  set invd : B := algebraMap ℚ B ((f.natDegree : ℚ)⁻¹) with hinvd
  have hdinv : (f.natDegree : B) * invd = 1 := by
    rw [hinvd, show ((f.natDegree : B)) = algebraMap ℚ B (f.natDegree : ℚ) by simp, ← map_mul,
      mul_inv_cancel₀ (by exact_mod_cast hd0), map_one]
  set h₀ : B[X] := Polynomial.C invd * (- f.coeff (f.natDegree - 1)) with hh₀
  -- pass to the algebraic closure of the fraction field
  set φ : B →+* AlgebraicClosure (FractionRing B) :=
    (algebraMap (FractionRing B) (AlgebraicClosure (FractionRing B))).comp
      (algebraMap B (FractionRing B)) with hφ
  have hφinj : Function.Injective φ :=
    (algebraMap (FractionRing B) (AlgebraicClosure (FractionRing B))).injective.comp
      (IsFractionRing.injective B (FractionRing B))
  set g : (AlgebraicClosure (FractionRing B))[X][X] := f.map (Polynomial.mapRingHom φ) with hg
  have hgm : g.Monic := hf.map _
  have hgd : g.natDegree = f.natDegree := hf.natDegree_map _
  have hgres : biResultant g = Polynomial.C (φ c) := by
    rw [hg, biResultant_map φ hf, hbires, Polynomial.map_C]
  have hφc : φ c ≠ 0 := fun hz => hcunit.ne_zero (hφinj (by simpa using hz))
  have hgsep : ∀ s, (biFibre g s).Separable :=
    forall_separable_of_biResultant_eq_C hgm hφc hgres
  have hcoeffmap : g.coeff (f.natDegree - 1) = (f.coeff (f.natDegree - 1)).map φ := by
    rw [hg]; simp [Polynomial.coeff_map]
  have hh : ((g.natDegree : (AlgebraicClosure (FractionRing B))[X])) * (h₀.map φ) =
      - g.coeff (g.natDegree - 1) := by
    rw [hgd, hh₀, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_neg, ← hcoeffmap,
      ← mul_assoc]
    have hone : ((f.natDegree : (AlgebraicClosure (FractionRing B))[X])) *
        Polynomial.C (φ invd) = 1 := by
      calc ((f.natDegree : (AlgebraicClosure (FractionRing B))[X])) * Polynomial.C (φ invd)
          = Polynomial.C (((f.natDegree : AlgebraicClosure (FractionRing B))) * φ invd) := by
            rw [map_mul, Polynomial.C_eq_natCast]
        _ = 1 := by
            have := congrArg φ hdinv
            simp only [map_mul, map_natCast, map_one] at this
            rw [this, map_one]
    rw [hone, one_mul]
  obtain ⟨N, hN⟩ := exists_constant_shift hgm (by rw [hgd]; exact hd0) hgsep (h₀.map φ) hh
  -- the shifted polynomial has constant coefficients
  set F : B[X][X] := f.comp (X + Polynomial.C h₀) with hF
  have hFmonic : F.Monic := hf.comp_X_add_C h₀
  have hgcomp : g.comp (X + Polynomial.C (h₀.map φ)) =
      (N.map fun a => X - Polynomial.C (Polynomial.C a)).prod := by
    have haux : ∀ p : (AlgebraicClosure (FractionRing B))[X][X],
        p.comp (X + Polynomial.C (h₀.map φ)) =
          Polynomial.aeval (X + Polynomial.C (h₀.map φ)) p := fun p => rfl
    rw [hN, haux, map_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro a _
    simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, map_add]
    ring
  have hFmap : F.map (Polynomial.mapRingHom φ) =
      (N.map fun a => X - Polynomial.C (Polynomial.C a)).prod := by
    rw [hF, Polynomial.map_comp, ← hg, ← hgcomp]
    congr 1
    simp
  have hFcoeff : ∀ j, ∃ b : B, F.coeff j = Polynomial.C b := by
    intro j
    have hlift : (N.map fun a => X - Polynomial.C (Polynomial.C a)).prod ∈
        Polynomial.lifts (Polynomial.C : (AlgebraicClosure (FractionRing B)) →+*
          (AlgebraicClosure (FractionRing B))[X]) := by
      refine Subsemiring.multiset_prod_mem _ _ ?_
      intro p hp
      obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hp
      rw [Polynomial.lifts_iff_set_range]
      exact ⟨X - Polynomial.C a, by simp⟩
    rw [Polynomial.lifts_iff_coeff_lifts] at hlift
    obtain ⟨u, hu⟩ := hlift j
    have hdeg0 : (F.coeff j).natDegree = 0 := by
      have h1 : ((F.coeff j).map φ).natDegree = 0 := by
        have h2 : (F.coeff j).map φ = (F.map (Polynomial.mapRingHom φ)).coeff j := by
          simp [Polynomial.coeff_map]
        rw [h2, hFmap, ← hu, Polynomial.natDegree_C]
      rwa [Polynomial.natDegree_map_eq_of_injective hφinj] at h1
    exact ⟨(F.coeff j).coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hdeg0⟩
  -- descend the shifted polynomial to `B`
  have hFlifts : F ∈ Polynomial.lifts (Polynomial.C : B →+* B[X]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    obtain ⟨b, hb⟩ := hFcoeff j
    exact ⟨b, hb.symm⟩
  obtain ⟨F₀, hF₀map, hF₀deg, hF₀monic⟩ := Polynomial.lifts_and_degree_eq_and_monic hFlifts hFmonic
  -- its resultant is a unit
  have hFcop : IsCoprime F (Polynomial.derivative F) := by
    have h1 : IsCoprime f (Polynomial.derivative f) :=
      (Polynomial.isUnit_resultant_iff_isCoprime hf).mp hres
    have h2 := h1.map
      (Polynomial.aeval (X + Polynomial.C h₀) : B[X][X] →ₐ[B[X]] B[X][X]).toRingHom
    have hda : Polynomial.derivative F = (Polynomial.derivative f).comp (X + Polynomial.C h₀) := by
      rw [hF, Polynomial.derivative_comp]
      simp
    rw [hF, hda]
    exact h2
  have hF₀res : IsUnit (Polynomial.resultant F₀ (Polynomial.derivative F₀)) := by
    have hu : IsUnit (Polynomial.resultant F (Polynomial.derivative F)) :=
      (Polynomial.isUnit_resultant_iff_isCoprime hFmonic).mpr hFcop
    have hderF : Polynomial.derivative F = (Polynomial.derivative F₀).map Polynomial.C := by
      rw [← hF₀map, Polynomial.derivative_map]
    have hdegF : F.natDegree = F₀.natDegree := by
      rw [← hF₀map, Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
    have hdegdF : (Polynomial.derivative F).natDegree = (Polynomial.derivative F₀).natDegree := by
      rw [hderF, Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
    have heq : Polynomial.resultant F (Polynomial.derivative F) =
        Polynomial.C (Polynomial.resultant F₀ (Polynomial.derivative F₀)) := by
      rw [hdegF, hdegdF, ← hF₀map, Polynomial.derivative_map]
      exact Polynomial.resultant_map_map (f := F₀) (g := Polynomial.derivative F₀)
        (m := F₀.natDegree) (n := (Polynomial.derivative F₀).natDegree) Polynomial.C
    rw [heq] at hu
    exact Polynomial.isUnit_C.mp hu
  obtain ⟨M₀, hM₀⟩ := hB F₀ hF₀monic hF₀res
  -- undo the shift
  refine ⟨M₀.map fun b => Polynomial.C b + h₀, ?_⟩
  have hback : f = F.comp (X - Polynomial.C h₀) := by
    rw [hF, Polynomial.comp_assoc]
    simp
  rw [hback, ← hF₀map, hM₀]
  have haux2 : ∀ p : B[X][X], p.comp (X - Polynomial.C h₀) =
      Polynomial.aeval (X - Polynomial.C h₀) p := fun p => rfl
  rw [Polynomial.map_multiset_prod, Multiset.map_map, haux2, map_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro b _
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.algebraMap_eq,
    Polynomial.C_add]
  ring

/-- The étale splitting property transports along a ring isomorphism. -/
theorem hasEtaleSplitting_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (hA : HasEtaleSplitting A) : HasEtaleSplitting B := by
  intro f hf hres
  set f' : A[X] := f.map (e.symm : B →+* A) with hf'
  have hf'monic : f'.Monic := hf.map _
  have hdeg : f'.natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (EquivLike.injective e.symm) f
  have hddeg : (Polynomial.derivative f').natDegree = (Polynomial.derivative f).natDegree := by
    rw [hf', Polynomial.derivative_map,
      Polynomial.natDegree_map_eq_of_injective (EquivLike.injective e.symm)]
  have hres' : IsUnit (Polynomial.resultant f' (Polynomial.derivative f')) := by
    have heq : Polynomial.resultant f' (Polynomial.derivative f') =
        (e.symm : B →+* A) (Polynomial.resultant f (Polynomial.derivative f)) := by
      rw [hdeg, hddeg, hf', Polynomial.derivative_map]
      exact Polynomial.resultant_map_map (f := f) (g := Polynomial.derivative f)
        (m := f.natDegree) (n := (Polynomial.derivative f).natDegree) (e.symm : B →+* A)
    rw [heq]
    exact hres.map _
  obtain ⟨M, hM⟩ := hA f' hf'monic hres'
  refine ⟨M.map e, ?_⟩
  have hback : f = f'.map (e : A →+* B) := by
    rw [hf', Polynomial.map_map]
    simp
  rw [hback, hM, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro a _
  simp

/-- **Algebraic simple connectedness of affine space, monogenic form.**  Over an algebraically
closed field of characteristic zero, a monic polynomial over a polynomial ring in `k` variables
whose resultant against its derivative is a unit splits into monic linear factors. -/
theorem hasEtaleSplitting_mvPolynomial (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] :
    ∀ k : ℕ, HasEtaleSplitting (MvPolynomial (Fin k) K) := by
  intro k
  induction k with
  | zero =>
      exact hasEtaleSplitting_of_ringEquiv
        (MvPolynomial.isEmptyRingEquiv K (Fin 0)).symm
        (hasEtaleSplitting_of_isAlgClosed K)
  | succ n ih =>
      exact hasEtaleSplitting_of_ringEquiv
        (MvPolynomial.finSuccEquiv K n).symm.toRingEquiv
        (hasEtaleSplitting_polynomial ih)

end GaloisForLFunctions.HTGeometry
