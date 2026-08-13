import GaloisForLFunctions.RHTower.DeningerHankelDiagonalMonicity
import GaloisForLFunctions.HTGeometry.IntegralMonicGroebnerTransfer

namespace RHTower
noncomputable section

open MvPolynomial
open scoped MonomialOrder BigOperators

/-- Weight of a finite monomial exponent under `X_i ↦ T^i`. -/
def hankelRankOneWeight (N : ℕ) : (Fin N →₀ ℕ) →+ ℕ :=
  (Finsupp.linearCombination ℕ (fun i : Fin N => i.val)).toAddMonoidHom

@[simp] theorem hankelRankOneWeight_single (N : ℕ) (i : Fin N) (a : ℕ) :
    hankelRankOneWeight N (Finsupp.single i a) = i.val * a := by
  simp [hankelRankOneWeight, mul_comm]

/-- Exponent map retaining total degree and Hankel weight. -/
def hankelRankOneExponentHom (N : ℕ) : (Fin N →₀ ℕ) →+ (Fin 2 →₀ ℕ) :=
  ((Finsupp.singleAddHom (0 : Fin 2)).comp Finsupp.degree) +
    ((Finsupp.singleAddHom (1 : Fin 2)).comp (hankelRankOneWeight N))

@[simp] theorem hankelRankOneExponentHom_apply (N : ℕ) (e : Fin N →₀ ℕ) :
    hankelRankOneExponentHom N e =
      Finsupp.single (0 : Fin 2) (Finsupp.degree e) +
        Finsupp.single (1 : Fin 2) (hankelRankOneWeight N e) := rfl

@[simp] theorem hankelRankOneExponentHom_single (N : ℕ) (i : Fin N) (a : ℕ) :
    hankelRankOneExponentHom N (Finsupp.single i a) =
      Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) (i.val * a) := by
  simp [hankelRankOneExponentHom]

/-- Monoid-algebra parameterization `X_i ↦ U T^i`. -/
def hankelRankOneParameterization (R : Type*) [CommSemiring R] (N : ℕ) :
    MvPolynomial (Fin N) R →+* MvPolynomial (Fin 2) R :=
  AddMonoidAlgebra.mapDomainRingHom R (hankelRankOneExponentHom N)

@[simp] theorem hankelRankOneParameterization_monomial
    (R : Type*) [CommSemiring R] (N : ℕ) (e : Fin N →₀ ℕ) (a : R) :
    hankelRankOneParameterization R N (MvPolynomial.monomial e a) =
      MvPolynomial.monomial (hankelRankOneExponentHom N e) a := by
  rw [hankelRankOneParameterization,
    AddMonoidAlgebra.mapDomainRingHom_apply,
    ← MvPolynomial.single_eq_monomial e a,
    ← MvPolynomial.single_eq_monomial (hankelRankOneExponentHom N e) a,
    AddMonoidAlgebra.mapDomain_single]

@[simp] theorem hankelRankOneParameterization_X
    (R : Type*) [CommSemiring R] (N : ℕ) (i : Fin N) :
    hankelRankOneParameterization R N (MvPolynomial.X i) =
      MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) i.val) 1 := by
  simp [MvPolynomial.X]

theorem hankelRankOneParameterization_finiteHankelMinor_zero
    (R : Type*) [CommRing R] (N : ℕ) (c : Fin 2 → ℕ)
    (hbound : ∀ j, 2 + c j ≤ N) :
    hankelRankOneParameterization R N
      (finiteHankelMaximalMinorOver R c hbound) = 0 := by
  rw [finiteHankelMaximalMinorOver, Matrix.det_fin_two]
  simp only [map_sub, map_mul, hankelRankOneParameterization_X,
    MvPolynomial.monomial_mul]
  have hexp :
      (Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2)
            (finiteHankelIndex c hbound (0 : Fin 2) (0 : Fin 2)).val) +
        (Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2)
            (finiteHankelIndex c hbound (1 : Fin 2) (1 : Fin 2)).val) =
      (Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2)
            (finiteHankelIndex c hbound (0 : Fin 2) (1 : Fin 2)).val) +
        (Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2)
            (finiteHankelIndex c hbound (1 : Fin 2) (0 : Fin 2)).val) := by
    ext i
    fin_cases i
    · simp [finiteHankelIndex]
    · simp [finiteHankelIndex]
      omega
  rw [hexp]
  simp

/-- Exponent avoids every diagonal leading monomial of a `2 × 2` Hankel minor. -/
def HankelRankOneReduced (N : ℕ) (e : Fin N →₀ ℕ) : Prop :=
  ∀ (c : Fin 2 → ℕ) (hbound : ∀ j, 2 + c j ≤ N), StrictMono c →
    ¬hankelDiagonalExponent c hbound ≤ e

theorem hankelRankOneReduced_support_close {N : ℕ} {e : Fin N →₀ ℕ}
    (he : HankelRankOneReduced N e) {i j : Fin N}
    (hi : i ∈ e.support) (hj : j ∈ e.support) :
    i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1 := by
  constructor
  · by_contra h
    have hgap : j.val + 1 < i.val := by omega
    let c : Fin 2 → ℕ := ![j.val, i.val - 1]
    have hbound : ∀ k, 2 + c k ≤ N := by
      intro k
      fin_cases k <;> simp [c] <;> omega
    have hc : StrictMono c := by
      rw [Fin.strictMono_iff_lt_succ]
      intro k
      fin_cases k
      simp [c]
      omega
    have h0 : finiteHankelIndex c hbound (0 : Fin 2) (0 : Fin 2) = j := by
      apply Fin.ext
      simp [finiteHankelIndex, c]
    have h1 : finiteHankelIndex c hbound (1 : Fin 2) (1 : Fin 2) = i := by
      apply Fin.ext
      simp [finiteHankelIndex, c]
      omega
    have hdiag : hankelDiagonalExponent c hbound =
        Finsupp.single j 1 + Finsupp.single i 1 := by
      ext x
      rw [hankelDiagonalExponent, hankelPermutationExponent_apply]
      simp only [Equiv.Perm.one_apply, Fin.sum_univ_two]
      simp [h0, h1, Finsupp.single_apply]
    apply he c hbound hc
    rw [hdiag]
    intro x
    have hji : j ≠ i := by omega
    by_cases hxj : x = j
    · subst x
      simp [hji, Nat.one_le_iff_ne_zero, Finsupp.mem_support_iff.mp hj]
    · by_cases hxi : x = i
      · subst x
        simp [hji, Nat.one_le_iff_ne_zero, Finsupp.mem_support_iff.mp hi]
      · simp [hxj, hxi]
  · by_contra h
    have hgap : i.val + 1 < j.val := by omega
    let c : Fin 2 → ℕ := ![i.val, j.val - 1]
    have hbound : ∀ k, 2 + c k ≤ N := by
      intro k
      fin_cases k <;> simp [c] <;> omega
    have hc : StrictMono c := by
      rw [Fin.strictMono_iff_lt_succ]
      intro k
      fin_cases k
      simp [c]
      omega
    have h0 : finiteHankelIndex c hbound (0 : Fin 2) (0 : Fin 2) = i := by
      apply Fin.ext
      simp [finiteHankelIndex, c]
    have h1 : finiteHankelIndex c hbound (1 : Fin 2) (1 : Fin 2) = j := by
      apply Fin.ext
      simp [finiteHankelIndex, c]
      omega
    have hdiag : hankelDiagonalExponent c hbound =
        Finsupp.single i 1 + Finsupp.single j 1 := by
      ext x
      rw [hankelDiagonalExponent, hankelPermutationExponent_apply]
      simp only [Equiv.Perm.one_apply, Fin.sum_univ_two]
      simp [h0, h1, Finsupp.single_apply]
    apply he c hbound hc
    rw [hdiag]
    intro x
    have hij : i ≠ j := by omega
    by_cases hxi : x = i
    · subst x
      simp [hij, Nat.one_le_iff_ne_zero, Finsupp.mem_support_iff.mp hi]
    · by_cases hxj : x = j
      · subst x
        simp [hij, Nat.one_le_iff_ne_zero, Finsupp.mem_support_iff.mp hj]
      · simp [hxi, hxj]

theorem hankelRankOneReduced_min_weight_div_degree {N : ℕ}
    {e : Fin N →₀ ℕ} (he : HankelRankOneReduced N e) (he0 : e ≠ 0) :
    hankelRankOneWeight N e / Finsupp.degree e =
      (e.support.min' (by simpa [Finset.nonempty_iff_ne_empty,
        Finsupp.support_eq_empty] using he0)).val := by
  have hsnon : e.support.Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty, Finsupp.support_eq_empty] using he0
  let q : Fin N := e.support.min' hsnon
  have hqmem : q ∈ e.support := Finset.min'_mem e.support hsnon
  have hqpos : 0 < e q := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hqmem)
  have hqmin : ∀ x ∈ e.support, q ≤ x := by
    intro x hx
    exact Finset.min'_le e.support x hx
  change hankelRankOneWeight N e / Finsupp.degree e = q.val
  by_cases hsucc : q.val + 1 < N
  · let r : Fin N := ⟨q.val + 1, hsucc⟩
    have hqr : q ≠ r := by
      intro h
      have := congrArg Fin.val h
      simp [r] at this
    have hedec : e = Finsupp.single q (e q) + Finsupp.single r (e r) := by
      ext x
      by_cases hxq : x = q
      · subst x
        simp [hqr]
      · by_cases hxr : x = r
        · subst x
          simp [hqr]
        · have hx0 : e x = 0 := by
            rw [← Finsupp.notMem_support_iff]
            intro hxmem
            have hle : q.val ≤ x.val := hqmin x hxmem
            have hclose := hankelRankOneReduced_support_close he hqmem hxmem
            have hxval : x.val = q.val ∨ x.val = q.val + 1 := by omega
            rcases hxval with hxval | hxval
            · exact hxq (Fin.ext hxval)
            · exact hxr (Fin.ext (by simpa [r] using hxval))
          rw [hx0]
          simp [hxq, hxr]
    rw [hedec]
    simp only [map_add, Finsupp.degree_single,
      hankelRankOneWeight_single]
    change (q.val * e q + (q.val + 1) * e r) / (e q + e r) = q.val
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  · have hlast : N ≤ q.val + 1 := Nat.le_of_not_gt hsucc
    have hedec : e = Finsupp.single q (e q) := by
      ext x
      by_cases hxq : x = q
      · subst x
        simp
      · have hx0 : e x = 0 := by
          rw [← Finsupp.notMem_support_iff]
          intro hxmem
          have hle : q.val ≤ x.val := hqmin x hxmem
          have hclose := hankelRankOneReduced_support_close he hqmem hxmem
          have hxval : x.val = q.val := by
            have hxlt := x.isLt
            omega
          exact hxq (Fin.ext hxval)
        simp [hxq, hx0]
    rw [hedec]
    simp only [Finsupp.degree_single, hankelRankOneWeight_single]
    exact Nat.mul_div_left q.val hqpos

/-- Two reduced exponents with the same total degree and Hankel weight are equal. -/
theorem hankelRankOneExponentHom_injective_on_reduced {N : ℕ}
    {e f : Fin N →₀ ℕ} (he : HankelRankOneReduced N e)
    (hf : HankelRankOneReduced N f)
    (hef : hankelRankOneExponentHom N e = hankelRankOneExponentHom N f) :
    e = f := by
  have hdeg : Finsupp.degree e = Finsupp.degree f := by
    have h := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hef
    simpa [hankelRankOneExponentHom, Finsupp.single_apply] using h
  have hweight : hankelRankOneWeight N e = hankelRankOneWeight N f := by
    have h := congrArg (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) hef
    simpa [hankelRankOneExponentHom, Finsupp.single_apply] using h
  by_cases he0 : e = 0
  · subst e
    have hfdeg : Finsupp.degree f = 0 := by simpa using hdeg.symm
    exact (Finsupp.degree_eq_zero_iff f).mp hfdeg |>.symm
  have hf0 : f ≠ 0 := by
    intro h
    subst f
    exact he0 ((Finsupp.degree_eq_zero_iff e).mp hdeg)
  have hesnon : e.support.Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty, Finsupp.support_eq_empty] using he0
  have hfsnon : f.support.Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty, Finsupp.support_eq_empty] using hf0
  let qe : Fin N := e.support.min' hesnon
  let qf : Fin N := f.support.min' hfsnon
  have hqe : qe.val = hankelRankOneWeight N e / Finsupp.degree e := by
    symm
    exact hankelRankOneReduced_min_weight_div_degree he he0
  have hqf : qf.val = hankelRankOneWeight N f / Finsupp.degree f := by
    symm
    exact hankelRankOneReduced_min_weight_div_degree hf hf0
  have hqval : qe.val = qf.val := by
    rw [hqe, hqf, hweight, hdeg]
  have hq : qe = qf := Fin.ext hqval
  have hqemem : qe ∈ e.support := Finset.min'_mem e.support hesnon
  have hqfmem : qe ∈ f.support := by
    rw [hq]
    exact Finset.min'_mem f.support hfsnon
  have hqemin : ∀ x ∈ e.support, qe ≤ x := by
    intro x hx
    exact Finset.min'_le e.support x hx
  have hqfmin : ∀ x ∈ f.support, qe ≤ x := by
    intro x hx
    rw [hq]
    exact Finset.min'_le f.support x hx
  by_cases hsucc : qe.val + 1 < N
  · let r : Fin N := ⟨qe.val + 1, hsucc⟩
    have hqr : qe ≠ r := by
      intro h
      have := congrArg Fin.val h
      simp [r] at this
    have edecomp : e = Finsupp.single qe (e qe) + Finsupp.single r (e r) := by
      ext x
      by_cases hxq : x = qe
      · subst x
        simp [hqr]
      · by_cases hxr : x = r
        · subst x
          simp [hqr]
        · have hx0 : e x = 0 := by
            rw [← Finsupp.notMem_support_iff]
            intro hxmem
            have hle : qe.val ≤ x.val := hqemin x hxmem
            have hclose := hankelRankOneReduced_support_close he hqemem hxmem
            have hxval : x.val = qe.val ∨ x.val = qe.val + 1 := by omega
            rcases hxval with hxval | hxval
            · exact hxq (Fin.ext hxval)
            · exact hxr (Fin.ext (by simpa [r] using hxval))
          rw [hx0]
          simp [hxq, hxr]
    have fdecomp : f = Finsupp.single qe (f qe) + Finsupp.single r (f r) := by
      ext x
      by_cases hxq : x = qe
      · subst x
        simp [hqr]
      · by_cases hxr : x = r
        · subst x
          simp [hqr]
        · have hx0 : f x = 0 := by
            rw [← Finsupp.notMem_support_iff]
            intro hxmem
            have hle : qe.val ≤ x.val := hqfmin x hxmem
            have hclose := hankelRankOneReduced_support_close hf hqfmem hxmem
            have hxval : x.val = qe.val ∨ x.val = qe.val + 1 := by omega
            rcases hxval with hxval | hxval
            · exact hxq (Fin.ext hxval)
            · exact hxr (Fin.ext (by simpa [r] using hxval))
          rw [hx0]
          simp [hxq, hxr]
    have hdeg' : e qe + e r = f qe + f r := by
      rw [edecomp, fdecomp] at hdeg
      simpa only [map_add, Finsupp.degree_single] using hdeg
    have hweight' : qe.val * e qe + (qe.val + 1) * e r =
        qe.val * f qe + (qe.val + 1) * f r := by
      rw [edecomp, fdecomp] at hweight
      simpa only [map_add, hankelRankOneWeight_single, r] using hweight
    have her : e r = f r := by nlinarith
    have heq : e qe = f qe := by omega
    rw [edecomp, fdecomp, her, heq]
  · have hlast : N ≤ qe.val + 1 := Nat.le_of_not_gt hsucc
    have edecomp : e = Finsupp.single qe (e qe) := by
      ext x
      by_cases hxq : x = qe
      · subst x
        simp
      · have hx0 : e x = 0 := by
          rw [← Finsupp.notMem_support_iff]
          intro hxmem
          have hle : qe.val ≤ x.val := hqemin x hxmem
          have hxlt := x.isLt
          exact hxq (Fin.ext (by omega))
        simp [hxq, hx0]
    have fdecomp : f = Finsupp.single qe (f qe) := by
      ext x
      by_cases hxq : x = qe
      · subst x
        simp
      · have hx0 : f x = 0 := by
          rw [← Finsupp.notMem_support_iff]
          intro hxmem
          have hle : qe.val ≤ x.val := hqfmin x hxmem
          have hxlt := x.isLt
          exact hxq (Fin.ext (by omega))
        simp [hxq, hx0]
    have heq : e qe = f qe := by
      rw [edecomp, fdecomp] at hdeg
      simpa using hdeg
    calc
      e = Finsupp.single qe (e qe) := edecomp
      _ = Finsupp.single qe (f qe) := by rw [heq]
      _ = f := fdecomp.symm

/-- Parameterization is coefficientwise injective on polynomials whose support avoids every
Hankel-chain leading monomial. -/
theorem eq_zero_of_hankelRankOneParameterization_eq_zero_of_reduced
    {R : Type*} [CommRing R] {N : ℕ} {p : MvPolynomial (Fin N) R}
    (hred : ∀ e ∈ p.support, HankelRankOneReduced N e)
    (hp : hankelRankOneParameterization R N p = 0) :
    p = 0 := by
  let S : Set (Fin N →₀ ℕ) := {e | HankelRankOneReduced N e}
  have hsupp : (p.support : Set (Fin N →₀ ℕ)) ⊆ S := by
    intro e he
    exact hred e he
  have hinj : Set.InjOn (hankelRankOneExponentHom N) S := by
    intro e he f hf hef
    exact hankelRankOneExponentHom_injective_on_reduced he hf hef
  apply MvPolynomial.ext
  intro e
  by_cases he : e ∈ p.support
  · have heS : e ∈ S := hsupp he
    have hcoeff := congrArg
      (MvPolynomial.coeff (hankelRankOneExponentHom N e)) hp
    rw [hankelRankOneParameterization,
      AddMonoidAlgebra.mapDomainRingHom_apply] at hcoeff
    change (AddMonoidAlgebra.mapDomain (hankelRankOneExponentHom N) p).coeff
      (hankelRankOneExponentHom N e) = 0 at hcoeff
    rw [AddMonoidAlgebra.coeff_mapDomain,
      Finsupp.mapDomain_apply' S (AddMonoidAlgebra.coeff p) hsupp hinj heS] at hcoeff
    change AddMonoidAlgebra.coeff p e = 0
    exact hcoeff
  · rw [MvPolynomial.coeff_zero]
    exact Finsupp.notMem_support_iff.mp he

/-- Ideal of finite generic `2 × 2` Hankel minors. -/
def finiteHankelRankOneIdeal (R : Type*) [CommRing R] (N : ℕ) :
    Ideal (MvPolynomial (Fin N) R) :=
  Ideal.span (finiteHankelMaximalMinorSetOver R N 2)

theorem finiteHankelRankOneIdeal_le_parameterization_ker
    (R : Type*) [CommRing R] (N : ℕ) :
    finiteHankelRankOneIdeal R N ≤
      RingHom.ker (hankelRankOneParameterization R N) := by
  rw [finiteHankelRankOneIdeal, Ideal.span_le]
  intro p hp
  rcases hp with ⟨c, hbound, _hc, rfl⟩
  exact RingHom.mem_ker.mpr
    (hankelRankOneParameterization_finiteHankelMinor_zero R N c hbound)

/-- The generic rank-one Hankel determinantal ideal is exactly the toric
parameterization kernel, over every commutative coefficient ring. -/
theorem finiteHankelRankOneIdeal_eq_parameterization_ker
    (R : Type*) [CommRing R] (N : ℕ) :
    finiteHankelRankOneIdeal R N =
      RingHom.ker (hankelRankOneParameterization R N) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    exact Subsingleton.elim _ _
  letI := hR
  apply le_antisymm
  · exact finiteHankelRankOneIdeal_le_parameterization_ker R N
  · intro p hp
    let B := finiteHankelMaximalMinorSetOver R N 2
    have hmonic : ∀ b ∈ B, MonomialOrder.degLex.Monic b :=
      finiteHankelMaximalMinorSetOver_degLex_monic R N 2
    have hunit : ∀ b ∈ B, IsUnit (MonomialOrder.degLex.leadingCoeff b) := by
      intro b hb
      rw [(hmonic b hb).leadingCoeff_eq_one]
      exact isUnit_one
    obtain ⟨g, r, hpr, _hdeg, hred⟩ :=
      MonomialOrder.degLex.div_set hunit p
    let q := Finsupp.linearCombination (MvPolynomial (Fin N) R)
      (fun b : B => (b : MvPolynomial (Fin N) R)) g
    have hq : q ∈ finiteHankelRankOneIdeal R N := by
      exact MonomialOrder.linearCombination_mem_span B g
    have hqker : q ∈ RingHom.ker (hankelRankOneParameterization R N) :=
      finiteHankelRankOneIdeal_le_parameterization_ker R N hq
    have hpzero : hankelRankOneParameterization R N p = 0 :=
      RingHom.mem_ker.mp hp
    have hqzero : hankelRankOneParameterization R N q = 0 :=
      RingHom.mem_ker.mp hqker
    have hrzero : hankelRankOneParameterization R N r = 0 := by
      change p = q + r at hpr
      have hmap := congrArg (hankelRankOneParameterization R N) hpr
      rw [map_add, hpzero, hqzero, zero_add] at hmap
      exact hmap.symm
    have hrreduced : ∀ e ∈ r.support, HankelRankOneReduced N e := by
      intro e he c hbound hc hdiv
      have hb : finiteHankelMaximalMinorOver R c hbound ∈ B :=
        ⟨c, hbound, hc, rfl⟩
      apply hred e he (finiteHankelMaximalMinorOver R c hbound) hb
      rwa [finiteHankelMaximalMinorOver_degLex_degree c hbound hc]
    have hr0 : r = 0 :=
      eq_zero_of_hankelRankOneParameterization_eq_zero_of_reduced hrreduced hrzero
    rw [finiteHankelRankOneIdeal, hpr, hr0, add_zero]
    exact hq

/-- The finite generic `2 × 2` Hankel minors form a degree-lex Gröbner basis over
every commutative coefficient ring. -/
theorem finiteHankelRankOne_degLex_isGroebnerBasis
    (R : Type*) [CommRing R] (N : ℕ) :
    MonomialOrder.degLex.IsGroebnerBasis
      (finiteHankelMaximalMinorSetOver R N 2) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    intro p _hp hp0
    exact (hp0 (Subsingleton.elim _ _)).elim
  letI := hR
  let B := finiteHankelMaximalMinorSetOver R N 2
  intro p hp hp0
  have hpker : p ∈ RingHom.ker (hankelRankOneParameterization R N) := by
    rw [← finiteHankelRankOneIdeal_eq_parameterization_ker R N,
      finiteHankelRankOneIdeal]
    exact hp
  have hmonic : ∀ b ∈ B, MonomialOrder.degLex.Monic b :=
    finiteHankelMaximalMinorSetOver_degLex_monic R N 2
  have hunit : ∀ b ∈ B, IsUnit (MonomialOrder.degLex.leadingCoeff b) := by
    intro b hb
    rw [(hmonic b hb).leadingCoeff_eq_one]
    exact isUnit_one
  obtain ⟨g, r, hpr, hdeg, hred⟩ :=
    MonomialOrder.degLex.div_set hunit p
  let q := Finsupp.linearCombination (MvPolynomial (Fin N) R)
    (fun b : B => (b : MvPolynomial (Fin N) R)) g
  have hq : q ∈ finiteHankelRankOneIdeal R N :=
    MonomialOrder.linearCombination_mem_span B g
  have hqker : q ∈ RingHom.ker (hankelRankOneParameterization R N) :=
    finiteHankelRankOneIdeal_le_parameterization_ker R N hq
  have hrzero : hankelRankOneParameterization R N r = 0 := by
    change p = q + r at hpr
    have hmap := congrArg (hankelRankOneParameterization R N) hpr
    rw [map_add, RingHom.mem_ker.mp hpker, RingHom.mem_ker.mp hqker,
      zero_add] at hmap
    exact hmap.symm
  have hrreduced : ∀ e ∈ r.support, HankelRankOneReduced N e := by
    intro e he c hbound hc hdiv
    have hb : finiteHankelMaximalMinorOver R c hbound ∈ B :=
      ⟨c, hbound, hc, rfl⟩
    apply hred e he (finiteHankelMaximalMinorOver R c hbound) hb
    rwa [finiteHankelMaximalMinorOver_degLex_degree c hbound hc]
  have hr0 : r = 0 :=
    eq_zero_of_hankelRankOneParameterization_eq_zero_of_reduced hrreduced hrzero
  have hpq : p = q := by
    change p = q + r at hpr
    simpa [hr0] using hpr
  have hcoeffq : MvPolynomial.coeff (MonomialOrder.degLex.degree p) q ≠ 0 := by
    rw [← hpq]
    exact MonomialOrder.leadingCoeff_ne_zero_iff.mpr hp0
  dsimp [q] at hcoeffq
  rw [Finsupp.linearCombination_apply] at hcoeffq
  have hsum : (∑ b ∈ g.support,
      MvPolynomial.coeff (MonomialOrder.degLex.degree p)
        (g b • (b : MvPolynomial (Fin N) R))) ≠ 0 := by
    change (MvPolynomial.coeffAddMonoidHom
      (MonomialOrder.degLex.degree p))
        (∑ b ∈ g.support, g b • (b : MvPolynomial (Fin N) R)) ≠ 0 at hcoeffq
    rw [map_sum] at hcoeffq
    exact hcoeffq
  obtain ⟨b, hbmem, hbcoeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hbcoeff' : MvPolynomial.coeff (MonomialOrder.degLex.degree p)
      ((b : MvPolynomial (Fin N) R) * g b) ≠ 0 := by
    simpa [smul_eq_mul, mul_comm] using hbcoeff
  have hbpSupport : MonomialOrder.degLex.degree p ∈
      ((b : MvPolynomial (Fin N) R) * g b).support := by
    exact MvPolynomial.mem_support_iff.mpr hbcoeff'
  have hprodDegree : MonomialOrder.degLex.degree
      ((b : MvPolynomial (Fin N) R) * g b) =
        MonomialOrder.degLex.degree p := by
    apply MonomialOrder.degLex.toSyn.injective
    exact le_antisymm (hdeg b)
      (MonomialOrder.degLex.le_degree hbpSupport)
  have hgb : g b ≠ 0 := Finsupp.mem_support_iff.mp hbmem
  have hmulDegree : MonomialOrder.degLex.degree
      ((b : MvPolynomial (Fin N) R) * g b) =
        MonomialOrder.degLex.degree (b : MvPolynomial (Fin N) R) +
          MonomialOrder.degLex.degree (g b) :=
    MonomialOrder.degLex.degree_mul_of_isRegular_left
      (hunit b b.property).isRegular hgb
  refine ⟨b, b.property, ?_⟩
  rw [← hprodDegree, hmulDegree]
  intro i
  exact Nat.le_add_right _ _

/-- Over a domain, the finite rank-one Hankel determinantal ideal is prime. -/
theorem finiteHankelRankOneIdeal_isPrime
    (R : Type*) [CommRing R] [IsDomain R] (N : ℕ) :
    (finiteHankelRankOneIdeal R N).IsPrime := by
  rw [finiteHankelRankOneIdeal_eq_parameterization_ker]
  exact RingHom.ker_isPrime (hankelRankOneParameterization R N)

/-- Closed integral capstone: every finite generic rank-one Hankel determinantal ideal over
the integers is prime. -/
theorem finiteHankelRankOneIdeal_int_isPrime (N : ℕ) :
    (finiteHankelRankOneIdeal ℤ N).IsPrime :=
  finiteHankelRankOneIdeal_isPrime ℤ N

end
end RHTower
