import GaloisForLFunctions.HTGeometry.QBlockTelescoper
import GaloisForLFunctions.HTGeometry.QOrbitResidueEuler
import GaloisForLFunctions.HTGeometry.PrincipalPartDecomposition

/-!
# Vanishing `q`-discrete residues make a principal part summable

Removing one orbit-and-order block at a time, a finite combination of principal-part monomials at
nonzero points whose `q`-discrete residues all vanish is a dilation coboundary.  This is the
converse half of the Chen–Singer criterion.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

theorem principalPartSum_finsetSum {ι : Type*} (s : Finset ι) (f : ι → (K × ℕ →₀ K)) :
    principalPartSum (∑ i ∈ s, f i) = ∑ i ∈ s, principalPartSum (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, principalPartSum_add, ih]

theorem principalPartSum_sub (c₁ c₂ : K × ℕ →₀ K) :
    principalPartSum (c₁ - c₂) = principalPartSum c₁ - principalPartSum c₂ := by
  have h : principalPartSum ((c₁ - c₂) + c₂) = principalPartSum (c₁ - c₂) + principalPartSum c₂ :=
    principalPartSum_add _ _
  rw [sub_add_cancel] at h
  rw [h]
  ring

theorem exists_dilationTelescoper_principalPartSum {q : K} (hq : q ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) :
    ∀ (M : ℕ) (c : K × ℕ →₀ K), c.support.card ≤ M →
      (∀ p ∈ c.support, p.1 ≠ 0 ∧ 0 < p.2) →
      (∀ a : K, a ≠ 0 → ∀ e : ℕ, 0 < e → qOrbitResidue q a e (principalPartSum c) = 0) →
      ∃ k : RatFunc K, principalPartSum c = ratFuncScale q hq k - k := by
  classical
  intro M
  induction M with
  | zero =>
      intro c hcard _ _
      have hc : c = 0 := by
        rw [← Finsupp.support_eq_empty]
        exact Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
      exact ⟨0, by rw [hc, principalPartSum_zero, map_zero, sub_zero]⟩
  | succ M ih =>
      intro c hcard hsupp hres
      rcases eq_or_ne c 0 with rfl | hc0
      · exact ⟨0, by rw [principalPartSum_zero, map_zero, sub_zero]⟩
      obtain ⟨p₀, hp₀⟩ := Finsupp.support_nonempty_iff.2 hc0
      obtain ⟨hα0, hd0⟩ := hsupp p₀ hp₀
      set α : K := p₀.1 with hαdef
      set d : ℕ := p₀.2 with hddef
      set A : ℤ → K := fun n => c (α * q ^ n, d) with hAdef
      have hinj : Function.Injective (fun n : ℤ => (α * q ^ n, d)) := by
        intro m n hmn
        exact multOrbit_injective hq hα0 hqtor (congrArg Prod.fst hmn)
      have hfin : {n : ℤ | A n ≠ 0}.Finite := by
        refine Set.Finite.subset
          (Set.Finite.preimage hinj.injOn c.support.finite_toSet) ?_
        intro n hn
        simpa [Finsupp.mem_support_iff] using hn
      set N : ℕ := hfin.toFinset.sup (fun n => n.natAbs) with hN
      have hA : ∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) → A n = 0 := by
        intro n hn
        by_contra hcon
        have hmem : n ∈ hfin.toFinset := by
          rw [Set.Finite.mem_toFinset]
          exact hcon
        have hle : n.natAbs ≤ N := Finset.le_sup (f := fun n : ℤ => n.natAbs) hmem
        have habs : |n| ≤ (N : ℤ) := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast hle
        rw [Finset.mem_Icc] at hn
        rw [abs_le] at habs
        exact hn ⟨habs.1, habs.2⟩
      have hterm : ∀ m : ℤ, polePart (principalPartSum c) (multOrbit q α m) d = A m := by
        intro m
        rw [polePart_principalPartSum c _ d hd0, multOrbit, hAdef]
      have hmem : ∀ n : ℤ, polePart (principalPartSum c) (multOrbit q α n) d ≠ 0 →
          n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        intro n hn
        by_contra hcon
        exact hn (by rw [hterm n, hA n hcon])
      have hresBlock : ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ((q ^ (-(d : ℤ))) ^ m) * A m = 0 := by
        have hsum : qOrbitResidue q α d (principalPartSum c)
            = ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ((q ^ (-(d : ℤ))) ^ m) * A m := by
          rw [qOrbitResidue_eq_sum (principalPartSum c) (Finset.Icc (-(N : ℤ)) (N : ℤ)) hmem]
          exact Finset.sum_congr rfl fun m _ => by rw [hterm m]
        rw [← hsum, hres α hα0 d hd0]
      set g : RatFunc K := blockTelescoper q α d N A with hg
      have hblock := ratFuncScale_blockTelescoper_sub hq α d N A hA hresBlock
      set blockFinsupp : K × ℕ →₀ K :=
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Finsupp.single (α * q ^ n, d) (A n) with hbf
      have hbfapply : ∀ β : K, ∀ e : ℕ, blockFinsupp (β, e)
          = if h : ∃ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (α * q ^ n, d) = (β, e)
              then c (β, e) else 0 := by
        intro β e
        rw [hbf, Finsupp.finsetSum_apply]
        by_cases h : ∃ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (α * q ^ n, d) = (β, e)
        · obtain ⟨n₀, hn₀mem, hn₀⟩ := h
          rw [dif_pos ⟨n₀, hn₀mem, hn₀⟩]
          rw [Finset.sum_eq_single n₀]
          · rw [Finsupp.single_apply, if_pos hn₀, hAdef, ← hn₀]
          · intro b _ hb
            refine Finsupp.single_apply_eq_zero.2 fun hbe => ?_
            exact absurd (hinj (hbe.symm.trans hn₀.symm)) hb
          · intro hnot
            exact absurd hn₀mem hnot
        · rw [dif_neg h]
          refine Finset.sum_eq_zero fun n hn => ?_
          refine Finsupp.single_apply_eq_zero.2 fun hbe => ?_
          exact absurd ⟨n, hn, hbe.symm⟩ h
      have hbfsum : principalPartSum blockFinsupp
          = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
              algebraMap K (RatFunc K) (A n) * invLinPow (α * q ^ n) d := by
        rw [hbf, principalPartSum_finsetSum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [principalPartSum_single]
      set c' : K × ℕ →₀ K := c - blockFinsupp with hc'
      have hc'apply : ∀ p : K × ℕ, c' p
          = if h : ∃ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (α * q ^ n, d) = p then 0 else c p := by
        intro p
        obtain ⟨β, e⟩ := p
        rw [hc', Finsupp.sub_apply, hbfapply β e]
        by_cases h : ∃ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (α * q ^ n, d) = (β, e)
        · rw [dif_pos h, dif_pos h, sub_self]
        · rw [dif_neg h, dif_neg h, sub_zero]
      have hc'sub : c'.support ⊆ c.support := by
        intro p hp
        rw [Finsupp.mem_support_iff, hc'apply p] at hp
        by_cases h : ∃ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (α * q ^ n, d) = p
        · rw [dif_pos h] at hp
          exact absurd rfl hp
        · rw [dif_neg h] at hp
          exact Finsupp.mem_support_iff.2 hp
      have hp₀notin : p₀ ∉ c'.support := by
        rw [Finsupp.mem_support_iff, hc'apply p₀]
        rw [dif_pos ⟨0, by simp, by simp [hαdef, hddef]⟩]
        simp
      have hcard' : c'.support.card ≤ M := by
        have hstrict : c'.support ⊂ c.support :=
          ⟨hc'sub, fun hsub => hp₀notin (hsub hp₀)⟩
        have := Finset.card_lt_card hstrict
        omega
      have hpps : principalPartSum c = principalPartSum c' + (ratFuncScale q hq g - g) := by
        rw [hc', principalPartSum_sub, hblock, hbfsum]
        ring
      have hres' : ∀ a : K, a ≠ 0 → ∀ e : ℕ, 0 < e →
          qOrbitResidue q a e (principalPartSum c') = 0 := by
        intro a ha e he
        have hsplit : principalPartSum c'
            = principalPartSum c - (ratFuncScale q hq g - g) := by
          rw [hpps]
          ring
        rw [hsplit, show principalPartSum c - (ratFuncScale q hq g - g)
            = principalPartSum c + -(ratFuncScale q hq g - g) from by ring,
          qOrbitResidue_add hq ha hqtor he, hres a ha e he]
        have hneg : qOrbitResidue q a e (-(ratFuncScale q hq g - g)) = 0 := by
          have h1 : (-(ratFuncScale q hq g - g))
              = ratFuncScale q hq (-g) - (-g) := by
            rw [map_neg]
            ring
          rw [h1, qOrbitResidue_ratFuncScale_sub hq ha hqtor he]
        rw [hneg, add_zero]
      obtain ⟨k', hk'⟩ := ih c' hcard' (fun p hp => hsupp p (hc'sub hp)) hres'
      exact ⟨k' + g, by rw [hpps, hk', map_add]; ring⟩


/-- A polynomial vanishing at the origin is a dilation coboundary. -/
theorem exists_dilationTelescoper_polynomial {q : K} (hq : q ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) (R : Polynomial K) (hR : R.coeff 0 = 0) :
    ∃ k : RatFunc K, algebraMap (Polynomial K) (RatFunc K) R = ratFuncScale q hq k - k := by
  classical
  set n : ℕ := R.natDegree + 1 with hn
  set S : Polynomial K :=
    ∑ i ∈ Finset.range n, Polynomial.C (R.coeff i / (q ^ i - 1)) * Polynomial.X ^ i with hS
  refine ⟨algebraMap (Polynomial K) (RatFunc K) S, ?_⟩
  have hscale : ratFuncScale q hq (algebraMap (Polynomial K) (RatFunc K) S)
      = algebraMap (Polynomial K) (RatFunc K) (polyScale q S) := by
    have h := ratFuncScale_div q hq S 1
    simpa using h
  rw [hscale, ← map_sub]
  congr 1
  have hpoly : polyScale q S - S
      = ∑ i ∈ Finset.range n,
          Polynomial.C (R.coeff i / (q ^ i - 1) * (q ^ i - 1)) * Polynomial.X ^ i := by
    rw [hS, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, polyScale_X]
    have hC : polyScale q (Polynomial.C (R.coeff i / (q ^ i - 1)))
        = Polynomial.C (R.coeff i / (q ^ i - 1)) := by
      rw [polyScale, Polynomial.aeval_C, Polynomial.algebraMap_eq]
    rw [hC, mul_pow, ← Polynomial.C_pow]
    rw [show Polynomial.C (R.coeff i / (q ^ i - 1)) *
        (Polynomial.C (q ^ i) * Polynomial.X ^ i)
        = Polynomial.C (R.coeff i / (q ^ i - 1) * q ^ i) * Polynomial.X ^ i from by
      rw [Polynomial.C_mul]; ring]
    rw [← sub_mul, ← Polynomial.C_sub]
    congr 2
    ring
  rw [hpoly]
  have hterm : ∀ i ∈ Finset.range n,
      Polynomial.C (R.coeff i / (q ^ i - 1) * (q ^ i - 1)) * Polynomial.X ^ i
        = Polynomial.C (R.coeff i) * Polynomial.X ^ i := by
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hR]
      simp
    · have hqi : q ^ i - 1 ≠ 0 := by
        intro h
        refine hqtor (i : ℤ) (Int.natCast_ne_zero.2 hi.ne') ?_
        rw [zpow_natCast]
        exact sub_eq_zero.1 h
      rw [div_mul_cancel₀ _ hqi]
  rw [Finset.sum_congr rfl hterm]
  conv_lhs => rw [Polynomial.as_sum_range' R n (by omega)]
  exact Finset.sum_congr rfl fun i _ => (Polynomial.C_mul_X_pow_eq_monomial).symm

theorem polePart_zero_zero_algebraMap (R : Polynomial K) :
    polePart (algebraMap (Polynomial K) (RatFunc K) R) 0 0 = R.eval 0 := by
  have hshift : ratFuncShift 0 (algebraMap (Polynomial K) (RatFunc K) R)
      = algebraMap (Polynomial K) (RatFunc K) R := by
    rw [ratFuncShift_algebraMap, polyShift_apply, map_zero, add_zero, Polynomial.comp_X]
  rw [polePart, hshift]
  have hdiv : algebraMap (Polynomial K) (RatFunc K) R
      = algebraMap (Polynomial K) (RatFunc K) R / algebraMap (Polynomial K) (RatFunc K) 1 := by
    rw [map_one, div_one]
  rw [Nat.cast_zero, neg_zero, hdiv, coeff_zero_algebraMap_div R 1 (by simp)]
  simp

/-- **Chen–Singer, converse half.**  A rational function regular and vanishing at the origin whose
`q`-discrete residues all vanish is `q`-summable. -/
theorem exists_dilationTelescoper_of_qOrbitResidue_vanish [IsAlgClosed K] {q : K} (hq : q ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) (r : RatFunc K)
    (hzero : polePart r 0 0 = 0)
    (hreg0 : ∀ d : ℕ, 0 < d → polePart r 0 d = 0)
    (hres : ∀ a : K, a ≠ 0 → ∀ d : ℕ, 0 < d → qOrbitResidue q a d r = 0) :
    ∃ k : RatFunc K, r = ratFuncScale q hq k - k := by
  classical
  obtain ⟨R, c, hc, hcoeff, hdec⟩ := exists_principalPart_decomposition r
  have hsupp : ∀ p ∈ c.support, p.1 ≠ 0 ∧ 0 < p.2 := by
    intro p hp
    refine ⟨?_, hc p hp⟩
    intro h0
    refine Finsupp.mem_support_iff.1 hp ?_
    have : p = (0, p.2) := by
      rw [Prod.ext_iff]
      exact ⟨h0, rfl⟩
    rw [this, hcoeff 0 p.2 (hc p hp), hreg0 p.2 (hc p hp)]
  have hpole : ∀ (β : K) (e : ℕ), 0 < e → polePart (principalPartSum c) β e = polePart r β e := by
    intro β e he
    rw [polePart_principalPartSum c β e he, hcoeff β e he]
  have hres' : ∀ a : K, a ≠ 0 → ∀ e : ℕ, 0 < e →
      qOrbitResidue q a e (principalPartSum c) = 0 := by
    intro a ha e he
    have hfun : (fun n : ℤ => (q ^ (-(e : ℤ))) ^ n *
          polePart (principalPartSum c) (multOrbit q a n) e)
        = fun n : ℤ => (q ^ (-(e : ℤ))) ^ n * polePart r (multOrbit q a n) e :=
      funext fun n => by rw [hpole _ e he]
    show ∑ᶠ n : ℤ, (q ^ (-(e : ℤ))) ^ n *
        polePart (principalPartSum c) (multOrbit q a n) e = 0
    rw [hfun]
    exact hres a ha e he
  obtain ⟨g, hg⟩ := exists_dilationTelescoper_principalPartSum hq hqtor
    c.support.card c le_rfl hsupp hres'
  have hRzero : R.coeff 0 = 0 := by
    have hval : polePart (algebraMap (Polynomial K) (RatFunc K) R) 0 0 = R.eval 0 :=
      polePart_zero_zero_algebraMap R
    have hsplit : polePart r 0 0
        = polePart (algebraMap (Polynomial K) (RatFunc K) R) 0 0
          + polePart (principalPartSum c) 0 0 := by
      rw [hdec, polePart_add]
    have hgz : polePart (principalPartSum c) 0 0 = 0 := by
      rw [hg, sub_eq_add_neg, polePart_add, polePart_neg, polePart_ratFuncScale, mul_zero]
      simp
    rw [hgz, add_zero, hval] at hsplit
    rw [← Polynomial.coeff_zero_eq_eval_zero] at hsplit
    rw [← hsplit, hzero]
  obtain ⟨h, hh⟩ := exists_dilationTelescoper_polynomial hq hqtor R hRzero
  exact ⟨h + g, by rw [hdec, hh, hg, map_add]; ring⟩

end

end GaloisForLFunctions.HTGeometry
