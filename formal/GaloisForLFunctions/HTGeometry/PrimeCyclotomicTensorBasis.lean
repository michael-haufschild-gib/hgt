import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CofinalRankTransfer
import GaloisForLFunctions.HTGeometry.PrimeCyclotomicFieldEscape

/-!
# Prime-cyclotomic tensor bases

Finite families of primitive roots of pairwise coprime orders generate a compositum of degree the
product of the individual totients.  Consequently a fresh root has the full cyclotomic minimal
polynomial degree over every finite prefix, and its standard power packet is linearly independent
over that prefix.  These are the relative tail-basis facts needed by cyclotomic coefficient
separation arguments.
-/

open scoped IntermediateField
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

theorem isPrimitiveRoot_mul_of_coprime {x y : ℂ} {m n : ℕ}
    (hx : IsPrimitiveRoot x m) (hy : IsPrimitiveRoot y n) (hc : Nat.Coprime m n) :
    IsPrimitiveRoot (x * y) (m * n) := by
  constructor
  · rw [mul_pow]
    calc
      x ^ (m * n) * y ^ (m * n) = (x ^ m) ^ n * (y ^ n) ^ m := by
        rw [pow_mul, Nat.mul_comm m n, pow_mul]
      _ = 1 := by simp [hx.pow_eq_one, hy.pow_eq_one]
  · intro l hl
    have hxl : x ^ (l * n) = 1 := by
      have hpow := congrArg (fun z : ℂ => z ^ n) hl
      rw [one_pow, ← pow_mul, mul_pow] at hpow
      have hyn : y ^ (l * n) = 1 := by
        rw [Nat.mul_comm, pow_mul, hy.pow_eq_one, one_pow]
      calc
        x ^ (l * n) = x ^ (l * n) * 1 := by rw [mul_one]
        _ = x ^ (l * n) * y ^ (l * n) := by rw [hyn]
        _ = 1 := hpow
    have hyl : y ^ (l * m) = 1 := by
      have hpow := congrArg (fun z : ℂ => z ^ m) hl
      rw [one_pow, ← pow_mul, mul_pow] at hpow
      have hxm : x ^ (l * m) = 1 := by
        rw [Nat.mul_comm, pow_mul, hx.pow_eq_one, one_pow]
      calc
        y ^ (l * m) = 1 * y ^ (l * m) := by rw [one_mul]
        _ = x ^ (l * m) * y ^ (l * m) := by rw [hxm]
        _ = 1 := hpow
    have hm : m ∣ l := hc.dvd_mul_right.mp (hx.dvd_of_pow_eq_one _ hxl)
    have hn : n ∣ l := hc.symm.dvd_mul_right.mp (hy.dvd_of_pow_eq_one _ hyl)
    exact hc.mul_dvd_of_dvd_of_dvd hm hn

theorem isPrimitiveRoot_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → ℕ) (u : ι → ℂ)
    (hu : ∀ i ∈ s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (q i) (q j)) :
    IsPrimitiveRoot (∏ i ∈ s, u i) (∏ i ∈ s, q i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      apply isPrimitiveRoot_mul_of_coprime (hu a (Finset.mem_insert_self a s))
        (ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
          (fun i hi j hj hij => hcop i (Finset.mem_insert_of_mem hi)
            j (Finset.mem_insert_of_mem hj) hij))
      apply Nat.Coprime.prod_right
      intro i hi
      exact hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))

noncomputable def cyclotomicAdjoin {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (u '' (s : Set ι))

theorem primitiveRoot_isAlgebraic {n : ℕ} (hn : 0 < n) {u : ℂ}
    (hu : IsPrimitiveRoot u n) : IsAlgebraic ℚ u := by
  apply isAlgebraic_iff_isIntegral.mpr
  refine ⟨Polynomial.cyclotomic n ℚ, Polynomial.cyclotomic.monic n ℚ, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact (hu.isRoot_cyclotomic hn).eq_zero

theorem cyclotomicAdjoin_finiteDimensional {ι : Type*} (s : Finset ι)
    (q : ι → ℕ) (u : ι → ℂ) (hq : ∀ i ∈ s, 0 < q i)
    (hu : ∀ i ∈ s, IsPrimitiveRoot (u i) (q i)) :
    FiniteDimensional ℚ (cyclotomicAdjoin s u) := by
  apply IntermediateField.finiteDimensional_adjoin
  rintro z ⟨i, hi, rfl⟩
  exact isAlgebraic_iff_isIntegral.mp
    (primitiveRoot_isAlgebraic (hq i hi) (hu i hi))

theorem cyclotomicAdjoin_finrank_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → ℕ) (u : ι → ℂ) (hq : ∀ i ∈ s, 0 < q i)
    (hu : ∀ i ∈ s, IsPrimitiveRoot (u i) (q i)) :
    Module.finrank ℚ (cyclotomicAdjoin s u) ≤ ∏ i ∈ s, Nat.totient (q i) := by
  induction s using Finset.induction_on with
  | empty =>
      have heq : cyclotomicAdjoin (∅ : Finset ι) u = ⊥ := by
        ext z
        simp [cyclotomicAdjoin]
      rw [heq]
      simp
  | @insert a s ha ih =>
      have haalg := primitiveRoot_isAlgebraic
        (hq a (Finset.mem_insert_self a s)) (hu a (Finset.mem_insert_self a s))
      have haint := isAlgebraic_iff_isIntegral.mp haalg
      have hadjoin : cyclotomicAdjoin (insert a s) u =
          cyclotomicAdjoin s u ⊔ IntermediateField.adjoin ℚ {u a} := by
        rw [cyclotomicAdjoin, cyclotomicAdjoin, ← IntermediateField.adjoin_union]
        congr 1
        ext z
        simp [eq_comm]
      rw [hadjoin, Finset.prod_insert ha]
      calc
        Module.finrank ℚ ↥(cyclotomicAdjoin s u ⊔ IntermediateField.adjoin ℚ {u a}) ≤
            Module.finrank ℚ (cyclotomicAdjoin s u) *
              Module.finrank ℚ (IntermediateField.adjoin ℚ {u a}) :=
          IntermediateField.finrank_sup_le _ _
        _ ≤ (∏ i ∈ s, Nat.totient (q i)) *
              Module.finrank ℚ (IntermediateField.adjoin ℚ {u a}) := by
          exact Nat.mul_le_mul_right _ (ih
            (fun i hi => hq i (Finset.mem_insert_of_mem hi))
            (fun i hi => hu i (Finset.mem_insert_of_mem hi)))
        _ = (∏ i ∈ s, Nat.totient (q i)) * Nat.totient (q a) := by
          congr 1
          rw [IntermediateField.adjoin.finrank haint,
            minpoly_natDegree_of_isPrimitiveRoot
              (hq a (Finset.mem_insert_self a s))
              (hu a (Finset.mem_insert_self a s))]
        _ = Nat.totient (q a) * ∏ i ∈ s, Nat.totient (q i) := by ac_rfl

theorem cyclotomicAdjoin_finrank_eq {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → ℕ) (u : ι → ℂ) (hq : ∀ i ∈ s, 0 < q i)
    (hu : ∀ i ∈ s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (q i) (q j)) :
    Module.finrank ℚ (cyclotomicAdjoin s u) = ∏ i ∈ s, Nat.totient (q i) := by
  letI : FiniteDimensional ℚ (cyclotomicAdjoin s u) :=
    cyclotomicAdjoin_finiteDimensional s q u hq hu
  apply le_antisymm (cyclotomicAdjoin_finrank_le s q u hq hu)
  rw [← HTGeometry.ConstraintRelativity.totient_prod_of_pairwise_coprime s q hcop]
  apply totient_le_finrank_of_isPrimitiveRoot_mem (cyclotomicAdjoin s u)
    (Finset.prod_pos fun i hi => hq i hi)
    (isPrimitiveRoot_finset_prod s q u hu hcop)
  apply (cyclotomicAdjoin s u).prod_mem
  intro i hi
  exact IntermediateField.subset_adjoin ℚ _ ⟨i, hi, rfl⟩

theorem cyclotomicAdjoin_le_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (u : ι → ℂ) :
    cyclotomicAdjoin s u ≤ cyclotomicAdjoin (insert a s) u := by
  dsimp [cyclotomicAdjoin]
  rw [IntermediateField.adjoin_le_iff]
  rintro z ⟨i, hi, rfl⟩
  exact IntermediateField.subset_adjoin ℚ _
    ⟨i, Finset.mem_insert_of_mem hi, rfl⟩

noncomputable def cyclotomicPrefixBase {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (u : ι → ℂ) :
    IntermediateField ℚ (cyclotomicAdjoin (insert a s) u) :=
  IntermediateField.map
    (IntermediateField.inclusion (cyclotomicAdjoin_le_insert s a u)) ⊤

noncomputable def cyclotomicFreshRoot {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (u : ι → ℂ) : cyclotomicAdjoin (insert a s) u :=
  ⟨u a, IntermediateField.subset_adjoin ℚ _
    ⟨a, Finset.mem_insert_self a s, rfl⟩⟩

theorem cyclotomicPrefixBase_relative_finrank {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ insert a s, 0 < q i)
    (hu : ∀ i ∈ insert a s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ insert a s, ∀ j ∈ insert a s,
      i ≠ j → Nat.Coprime (q i) (q j)) :
    Module.finrank (cyclotomicPrefixBase s a u) (cyclotomicAdjoin (insert a s) u) =
      Nat.totient (q a) := by
  let Kprev := cyclotomicAdjoin s u
  let Kall := cyclotomicAdjoin (insert a s) u
  let inc : Kprev →ₐ[ℚ] Kall :=
    IntermediateField.inclusion (cyclotomicAdjoin_le_insert s a u)
  let Kbase : IntermediateField ℚ Kall := cyclotomicPrefixBase s a u
  letI : FiniteDimensional ℚ Kprev :=
    cyclotomicAdjoin_finiteDimensional s q u
      (fun i hi => hq i (Finset.mem_insert_of_mem hi))
      (fun i hi => hu i (Finset.mem_insert_of_mem hi))
  letI : FiniteDimensional ℚ Kall :=
    cyclotomicAdjoin_finiteDimensional (insert a s) q u hq hu
  have hbase : Module.finrank ℚ Kbase = ∏ i ∈ s, Nat.totient (q i) := by
    calc
      Module.finrank ℚ Kbase =
          Module.finrank ℚ (⊤ : IntermediateField ℚ Kprev) :=
        (IntermediateField.equivMap (⊤ : IntermediateField ℚ Kprev) inc).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank ℚ Kprev := by simp
      _ = ∏ i ∈ s, Nat.totient (q i) := cyclotomicAdjoin_finrank_eq s q u
        (fun i hi => hq i (Finset.mem_insert_of_mem hi))
        (fun i hi => hu i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => hcop i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij)
  have hall : Module.finrank ℚ Kall =
      (∏ i ∈ s, Nat.totient (q i)) * Nat.totient (q a) := by
    rw [cyclotomicAdjoin_finrank_eq (insert a s) q u hq hu hcop,
      Finset.prod_insert ha]
    ac_rfl
  letI : Algebra Kbase Kall := Kbase.toAlgebra
  have htower := Module.finrank_mul_finrank ℚ Kbase Kall
  rw [hbase, hall] at htower
  have hpos : 0 < ∏ i ∈ s, Nat.totient (q i) := by
    apply Finset.prod_pos
    intro i hi
    exact Nat.totient_pos.mpr (hq i (Finset.mem_insert_of_mem hi))
  have htower' : (∏ i ∈ s, Nat.totient (q i)) * Module.finrank Kbase Kall =
      (∏ i ∈ s, Nat.totient (q i)) * Nat.totient (q a) := by
    simpa [Kbase, Kall] using htower
  exact Nat.eq_of_mul_eq_mul_left hpos htower'

theorem cyclotomicFreshRoot_minpoly_natDegree {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ insert a s, 0 < q i)
    (hu : ∀ i ∈ insert a s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ insert a s, ∀ j ∈ insert a s,
      i ≠ j → Nat.Coprime (q i) (q j)) :
    (minpoly (cyclotomicPrefixBase s a u) (cyclotomicFreshRoot s a u)).natDegree =
      Nat.totient (q a) := by
  let Kprev := cyclotomicAdjoin s u
  let Kall := cyclotomicAdjoin (insert a s) u
  let inc : Kprev →ₐ[ℚ] Kall :=
    IntermediateField.inclusion (cyclotomicAdjoin_le_insert s a u)
  let Kbase : IntermediateField ℚ Kall := cyclotomicPrefixBase s a u
  let ua : Kall := cyclotomicFreshRoot s a u
  letI : FiniteDimensional ℚ Kall :=
    cyclotomicAdjoin_finiteDimensional (insert a s) q u hq hu
  letI : Algebra Kbase Kall := Kbase.toAlgebra
  have htop : IntermediateField.adjoin Kbase {ua} = ⊤ := by
    apply top_unique
    intro z hz
    let A : IntermediateField Kbase Kall := IntermediateField.adjoin Kbase {ua}
    change z ∈ A
    have hzC : (z : ℂ) ∈ IntermediateField.adjoin ℚ
        (u '' ((insert a s : Finset ι) : Set ι)) := z.property
    apply IntermediateField.adjoin_induction ℚ
      (p := fun x hx => (⟨x, hx⟩ : Kall) ∈ A)
      (x := (z : ℂ)) _ _ _ _ _ hzC
    · rintro x ⟨i, hi, rfl⟩
      by_cases hia : i = a
      · subst i
        exact IntermediateField.subset_adjoin Kbase {ua} (by simp [ua, cyclotomicFreshRoot])
      · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
        have huiPrev : u i ∈ Kprev := IntermediateField.subset_adjoin ℚ _ ⟨i, his, rfl⟩
        let zi : Kprev := ⟨u i, huiPrev⟩
        have hziMap : inc zi ∈ Kbase := by
          change inc zi ∈ IntermediateField.map inc ⊤
          exact ⟨zi, by simp, rfl⟩
        let kb : Kbase := ⟨inc zi, hziMap⟩
        have hmem := A.algebraMap_mem kb
        convert hmem using 1
        apply Subtype.ext
        rfl
    · intro r
      have hmem := A.algebraMap_mem (algebraMap ℚ Kbase r)
      convert hmem using 1
      apply Subtype.ext
      simp
    · intro x y hx hy hxA hyA
      exact A.add_mem hxA hyA
    · intro x hx hxA
      exact A.inv_mem hxA
    · intro x y hx hy hxA hyA
      exact A.mul_mem hxA hyA
  have huaInt : IsIntegral Kbase ua := IsIntegral.of_finite Kbase ua
  rw [← IntermediateField.adjoin.finrank huaInt, htop]
  simpa [Kbase, Kall, ua] using
    cyclotomicPrefixBase_relative_finrank s a ha q u hq hu hcop

theorem linearIndependent_cyclotomicFreshRoot_powers {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (q : ι → ℕ) (u : ι → ℂ)
    (hq : ∀ i ∈ insert a s, 0 < q i)
    (hu : ∀ i ∈ insert a s, IsPrimitiveRoot (u i) (q i))
    (hcop : ∀ i ∈ insert a s, ∀ j ∈ insert a s,
      i ≠ j → Nat.Coprime (q i) (q j)) :
    LinearIndependent (cyclotomicPrefixBase s a u)
      (fun e : Fin (Nat.totient (q a)) => cyclotomicFreshRoot s a u ^ (e : ℕ)) := by
  let Kall := cyclotomicAdjoin (insert a s) u
  let Kbase : IntermediateField ℚ Kall := cyclotomicPrefixBase s a u
  let ua : Kall := cyclotomicFreshRoot s a u
  letI : Algebra Kbase Kall := Kbase.toAlgebra
  have hdeg := cyclotomicFreshRoot_minpoly_natDegree s a ha q u hq hu hcop
  have hli := linearIndependent_pow (K := Kbase) ua
  rw [hdeg] at hli
  exact hli

end GaloisForLFunctions.HTGeometry
