import GaloisForLFunctions.HTGeometry.ShiftTranslateFiltration
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# A shift-stable ideal of relations contains an affine-linear invariant

Let `Φ(P) = P^σ(X + R)` be the coefficient shift composed with the translation of the variables, and
let `J` be an ideal of polynomial relations stable under `Φ` and containing no nonzero constant.
Starting from any nonzero element of `J`, normalizing one top-degree coefficient to `1` makes the
difference `Φ(P) - P` lose that coefficient, so the pair

```text
(total degree, number of top-degree monomials)
```

drops lexicographically.  The descent therefore stops, and it stops only at a nonzero `Φ`-invariant
element of `J`.  Since `J` has no nonzero constant, that element has positive degree, and partial
differentiation — which commutes with `Φ` and lowers the total degree by exactly one at a suitable
variable — brings it down to degree exactly one.

An affine-linear `Φ`-invariant polynomial `b + ∑ᵢ aᵢ Xᵢ` says precisely

```text
σ(aᵢ) = aᵢ    and    ∑ᵢ aᵢ Rᵢ = σg - g   with  g = -b,
```

so one polynomial relation among elements whose difference defects lie in the coefficient field
produces a constant-coefficient linear combination of those defects which is a difference
coboundary.  This is the elementary half of the difference-Galois criterion for indefinite sums, and
it is the only half a differential-independence proof needs.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] {ι : Type*}

/-! ## Scaling by a nonzero constant -/

theorem support_C_mul_eq {a : K} (ha : a ≠ 0) (P : MvPolynomial ι K) :
    (C a * P).support = P.support := by
  ext e
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, ne_eq, mul_eq_zero, ha,
    false_or]

theorem totalDegree_C_mul_eq {a : K} (ha : a ≠ 0) (P : MvPolynomial ι K) :
    (C a * P).totalDegree = P.totalDegree := by
  rw [totalDegree_eq_sup, totalDegree_eq_sup, support_C_mul_eq ha]

/-! ## The top-degree monomials -/

/-- The exponents at which a polynomial attains its total degree. -/
def topSupport (P : MvPolynomial ι K) : Finset (ι →₀ ℕ) :=
  P.support.filter fun e => Finsupp.degree e = P.totalDegree

theorem mem_topSupport {P : MvPolynomial ι K} {e : ι →₀ ℕ} :
    e ∈ topSupport P ↔ coeff e P ≠ 0 ∧ Finsupp.degree e = P.totalDegree := by
  rw [topSupport, Finset.mem_filter, MvPolynomial.mem_support_iff]

theorem topSupport_nonempty {P : MvPolynomial ι K} (hP : P ≠ 0) : (topSupport P).Nonempty := by
  obtain ⟨e, he, hdeg⟩ := exists_mem_support_degree_eq_totalDegree hP
  exact ⟨e, mem_topSupport.mpr ⟨MvPolynomial.mem_support_iff.mp he, hdeg⟩⟩

theorem topSupport_C_mul_eq {a : K} (ha : a ≠ 0) (P : MvPolynomial ι K) :
    topSupport (C a * P) = topSupport P := by
  rw [topSupport, topSupport, support_C_mul_eq ha, totalDegree_C_mul_eq ha]

/-! ## The descent -/

/-- **A shift-stable ideal with no nonzero constant contains a nonzero invariant.**  Normalizing a
top-degree coefficient to `1` makes it cancel in `Φ(P) - P`, so either that difference vanishes or
the pair `(total degree, number of top-degree monomials)` drops lexicographically. -/
theorem exists_ne_zero_shiftTranslate_eq_self (σ : K →+* K) (R : ι → K)
    (J : Ideal (MvPolynomial ι K)) (hJ : ∀ P ∈ J, shiftTranslate σ R P ∈ J)
    {P : MvPolynomial ι K} (hP : P ∈ J) (hP0 : P ≠ 0) :
    ∃ Q ∈ J, Q ≠ 0 ∧ shiftTranslate σ R Q = Q := by
  classical
  suffices H : ∀ d c : ℕ, ∀ P : MvPolynomial ι K, P.totalDegree = d →
      (topSupport P).card = c → P ∈ J → P ≠ 0 → ∃ Q ∈ J, Q ≠ 0 ∧ shiftTranslate σ R Q = Q from
    H P.totalDegree (topSupport P).card P rfl rfl hP hP0
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ihc =>
      intro P hd hc hPJ hP0
      obtain ⟨e₀, he₀⟩ := topSupport_nonempty hP0
      obtain ⟨hce₀, hdeg₀⟩ := mem_topSupport.mp he₀
      have hPnorm : coeff e₀ (C (coeff e₀ P)⁻¹ * P) = 1 := by
        rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hce₀]
      set P' : MvPolynomial ι K := C (coeff e₀ P)⁻¹ * P with hP'def
      have hinv0 : (coeff e₀ P)⁻¹ ≠ 0 := inv_ne_zero hce₀
      have hP'J : P' ∈ J := Ideal.mul_mem_left _ _ hPJ
      have hP'0 : P' ≠ 0 := by
        intro hcon
        rw [hcon, MvPolynomial.coeff_zero] at hPnorm
        exact one_ne_zero hPnorm.symm
      have hdeg' : P'.totalDegree = d := by rw [hP'def, totalDegree_C_mul_eq hinv0, hd]
      have htop' : topSupport P' = topSupport P := topSupport_C_mul_eq hinv0 P
      set Q : MvPolynomial ι K := shiftTranslate σ R P' - P' with hQdef
      have hQJ : Q ∈ J := Ideal.sub_mem _ (hJ _ hP'J) hP'J
      have hQtop : ∀ e : ι →₀ ℕ, Finsupp.degree e = d →
          coeff e Q = σ (coeff e P') - coeff e P' := by
        intro e he
        rw [hQdef, MvPolynomial.coeff_sub,
          coeff_shiftTranslate_of_le σ R P' (by rw [hdeg', he])]
      have hQdeg : Q.totalDegree ≤ d := by
        refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
        refine max_le ?_ (le_of_eq hdeg')
        exact le_trans (totalDegree_shiftTranslate_le σ R P') (le_of_eq hdeg')
      by_cases hQ0 : Q = 0
      · refine ⟨P', hP'J, hP'0, ?_⟩
        have := sub_eq_zero.mp (hQdef ▸ hQ0)
        exact this
      · have he₀Q : e₀ ∉ topSupport Q := by
          intro hcon
          obtain ⟨hne, _⟩ := mem_topSupport.mp hcon
          refine hne ?_
          rw [hQtop e₀ (by rw [hdeg₀, hd]), hPnorm, map_one, sub_self]
        by_cases hQd : Q.totalDegree = d
        · have hsub : topSupport Q ⊆ topSupport P' := by
            intro e he
            obtain ⟨hne, hde⟩ := mem_topSupport.mp he
            rw [hQd] at hde
            refine mem_topSupport.mpr ⟨?_, by rw [hdeg', hde]⟩
            intro hzero
            rw [hQtop e hde, hzero, map_zero, sub_zero] at hne
            exact hne rfl
          have hcard : (topSupport Q).card < c := by
            rw [← hc, ← htop']
            refine Finset.card_lt_card ⟨hsub, ?_⟩
            intro hcon
            exact he₀Q (hcon (htop' ▸ he₀))
          exact ihc _ hcard Q hQd rfl hQJ hQ0
        · exact ihd Q.totalDegree (lt_of_le_of_ne hQdeg hQd) (topSupport Q).card Q rfl rfl hQJ hQ0

/-! ## Partial differentiation against the operator -/

theorem pderiv_bind₁_translatedVariable [DecidableEq ι] (R : ι → K) (i : ι)
    (P : MvPolynomial ι K) :
    pderiv i (bind₁ (translatedVariable R) P) = bind₁ (translatedVariable R) (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      have hTj : pderiv i (translatedVariable R j)
          = (if j = i then 1 else 0 : MvPolynomial ι K) := by
        rw [translatedVariable, map_add, MvPolynomial.pderiv_C, add_zero, MvPolynomial.pderiv_X,
          Pi.single_apply]
      have hXj : pderiv i (X j : MvPolynomial ι K)
          = (if j = i then 1 else 0 : MvPolynomial ι K) := by
        rw [MvPolynomial.pderiv_X, Pi.single_apply]
      have hbind : bind₁ (translatedVariable R) (if j = i then 1 else 0 : MvPolynomial ι K)
          = (if j = i then 1 else 0 : MvPolynomial ι K) := by
        by_cases hij : j = i
        · simp [hij]
        · simp [hij]
      simp only [map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.pderiv_mul, hp, hTj, hXj,
        map_add, hbind]

/-- **Partial differentiation commutes with the shift-translate operator.** -/
theorem pderiv_shiftTranslate [DecidableEq ι] (σ : K →+* K) (R : ι → K) (i : ι)
    (P : MvPolynomial ι K) :
    pderiv i (shiftTranslate σ R P) = shiftTranslate σ R (pderiv i P) := by
  rw [shiftTranslate_apply, shiftTranslate_apply, pderiv_bind₁_translatedVariable,
    MvPolynomial.pderiv_map]

/-- Partial differentiation lowers the total degree by at least one. -/
theorem totalDegree_pderiv_le_sub_one [DecidableEq ι] (i : ι) (P : MvPolynomial ι K) :
    (pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  refine totalDegree_le_of_coeff_eq_zero fun e he => ?_
  rw [MvPolynomial.coeff_pderiv]
  have hzero : coeff (e + Finsupp.single i 1) P = 0 := by
    refine coeff_eq_zero_of_totalDegree_lt_degree ?_
    have h1 : Finsupp.degree (e + Finsupp.single i 1) = Finsupp.degree e + 1 := by
      rw [map_add, Finsupp.degree_single]
    omega
  rw [hzero, zero_mul]

/-- **A polynomial of positive degree has a variable in which differentiation drops the degree by
exactly one.** -/
theorem exists_pderiv_totalDegree_eq [DecidableEq ι] [CharZero K] {P : MvPolynomial ι K}
    (h : 1 ≤ P.totalDegree) :
    ∃ i : ι, (pderiv i P).totalDegree = P.totalDegree - 1 := by
  have hP0 : P ≠ 0 := by
    intro hcon
    rw [hcon, MvPolynomial.totalDegree_zero] at h
    omega
  obtain ⟨e, heS, hdeg⟩ := exists_mem_support_degree_eq_totalDegree hP0
  have hene : e ≠ 0 := by
    intro hcon
    rw [hcon] at hdeg
    simp only [map_zero] at hdeg
    omega
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hene
  have hei : 1 ≤ e i := Nat.one_le_iff_ne_zero.mpr (by simpa using hi)
  have hesplit : (e - Finsupp.single i 1) + Finsupp.single i 1 = e :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hei)
  refine ⟨i, le_antisymm (totalDegree_pderiv_le_sub_one i P) ?_⟩
  have hcoeff : coeff (e - Finsupp.single i 1) (pderiv i P) ≠ 0 := by
    rw [MvPolynomial.coeff_pderiv, hesplit]
    refine mul_ne_zero (MvPolynomial.mem_support_iff.mp heS) ?_
    have hval : (e - Finsupp.single i 1 : ι →₀ ℕ) i = e i - 1 := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    rw [hval]
    have hcast : ((e i - 1 : ℕ) : K) + 1 = ((e i : ℕ) : K) := by
      have : (e i - 1) + 1 = e i := by omega
      rw [← this]
      push_cast
      ring
    rw [hcast]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hle := degree_le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)
  have hdegsub : Finsupp.degree (e - Finsupp.single i 1) + 1 = Finsupp.degree e := by
    have h2 : Finsupp.degree (e - Finsupp.single i 1)
        + Finsupp.degree (Finsupp.single i (1 : ℕ)) = Finsupp.degree e := by
      rw [← map_add, hesplit]
    rw [Finsupp.degree_single] at h2
    omega
  omega

/-- **Descending to degree one.**  A `Φ`-invariant polynomial of positive degree produces a
`Φ`-invariant polynomial of degree exactly one. -/
theorem exists_totalDegree_eq_one_shiftTranslate_eq_self [DecidableEq ι] [CharZero K]
    (σ : K →+* K) (R : ι → K) :
    ∀ (d : ℕ) (P : MvPolynomial ι K), P.totalDegree = d → 1 ≤ d →
      shiftTranslate σ R P = P →
      ∃ Q : MvPolynomial ι K, Q.totalDegree = 1 ∧ shiftTranslate σ R Q = Q := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro P hd h1 hinv
    rcases eq_or_lt_of_le h1 with heq | hlt
    · exact ⟨P, by rw [hd, ← heq], hinv⟩
    · obtain ⟨i, hi⟩ := exists_pderiv_totalDegree_eq (P := P) (by omega)
      refine ih (d - 1) (by omega) (pderiv i P) (by rw [hi, hd]) (by omega) ?_
      rw [← pderiv_shiftTranslate, hinv]

end

end GaloisForLFunctions
