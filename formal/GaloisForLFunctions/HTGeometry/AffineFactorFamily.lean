import GaloisForLFunctions.HTGeometry.PairFamGradient

/-!
# Factor families affine in the newer coordinate

A first-order equation solved *linearly* for the derivative, `h' = a(z)·h + b(z)`, places at the
coordinates `j`, `j+1` a factor

`fac j = lead j · X_(j+1) + cnst j`,

with both coefficients functions of `X_j` alone.  Nothing requires them to be polynomials: for
rational coefficients they are ratios, and the model is a field.

The three facts the peel reads off this shape are that the factor is nonzero (its derivative in the
newer coordinate is the leading coefficient), that its degree there is exactly one — so its inverse
drops a degree — and that its logarithmic residue at infinity is one.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## A coordinate-free element is killed by that coordinate -/

theorem pderiv_eq_zero_of_degreeOf_eq_zero {σ : Type*} {i : σ} {P : MvPolynomial σ ℂ}
    (h : MvPolynomial.degreeOf i P = 0) : MvPolynomial.pderiv i P = 0 := by
  by_contra hne
  have := degreeOf_pderiv_lt hne
  omega

theorem TopFree.fpderiv_eq_zero {m : ℕ} {f : CascadeField} (h : TopFree m f) :
    fpderiv m f = 0 := by
  obtain ⟨N, D, hD, hval, hN0, hD0⟩ := h
  have hDne : algebraMap (MvPolynomial ℕ ℂ) CascadeField D ≠ 0 := by
    simpa using (IsFractionRing.injective (MvPolynomial ℕ ℂ) CascadeField).ne hD
  have hd : fpderiv m (algebraMap (MvPolynomial ℕ ℂ) CascadeField D * f)
      = fpderiv m (algebraMap (MvPolynomial ℕ ℂ) CascadeField N) := by rw [hval]
  rw [Derivation.leibniz, fpderiv_algebraMap, fpderiv_algebraMap,
    pderiv_eq_zero_of_degreeOf_eq_zero hD0, pderiv_eq_zero_of_degreeOf_eq_zero hN0,
    map_zero] at hd
  simp only [smul_eq_mul, mul_zero, add_zero] at hd
  exact (mul_eq_zero.mp hd).resolve_left hDne

/-! ## The inverse of an affine element -/

/-- **An element affine in a coordinate with a nonzero leading coefficient has an inverse of degree
`−1` in that coordinate.** -/
theorem topDegLE_inv_affine {m : ℕ} {A B : CascadeField} (hA0 : A ≠ 0)
    (hA : TopFree m A) (hB : TopFree m B) :
    TopDegLE m (-1) ((A * fx m + B)⁻¹) := by
  classical
  obtain ⟨NA, DA, hDA, hvalA, hNA0, hDA0⟩ := hA
  obtain ⟨NB, DB, hDB, hvalB, hNB0, hDB0⟩ := hB
  have hDAne : algebraMap (MvPolynomial ℕ ℂ) CascadeField DA ≠ 0 := by
    simpa using (IsFractionRing.injective (MvPolynomial ℕ ℂ) CascadeField).ne hDA
  have hNAne : NA ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvalA
    exact hA0 ((mul_eq_zero.mp hvalA).resolve_left hDAne)
  set P : MvPolynomial ℕ ℂ := NA * DB * MvPolynomial.X m + NB * DA with hP
  have hpd : MvPolynomial.pderiv m P = NA * DB := by
    rw [hP, map_add, Derivation.leibniz, MvPolynomial.pderiv_X_self,
      pderiv_eq_zero_of_degreeOf_eq_zero
        (show MvPolynomial.degreeOf m (NA * DB) = 0 by
          have := MvPolynomial.degreeOf_mul_le m NA DB
          omega),
      pderiv_eq_zero_of_degreeOf_eq_zero
        (show MvPolynomial.degreeOf m (NB * DA) = 0 by
          have := MvPolynomial.degreeOf_mul_le m NB DA
          omega)]
    simp
  have hpdne : MvPolynomial.pderiv m P ≠ 0 := by
    rw [hpd]
    exact mul_ne_zero hNAne hDB
  have hP0 : P ≠ 0 := fun h0 => hpdne (by rw [h0, map_zero])
  have hdeg1 : 1 ≤ MvPolynomial.degreeOf m P := by
    have := degreeOf_pderiv_lt hpdne
    omega
  have halg : algebraMap (MvPolynomial ℕ ℂ) CascadeField (DA * DB) * (A * fx m + B)
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField P := by
    rw [hP, map_add, map_mul, map_mul, map_mul, map_mul,
      show algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X m) = fx m from rfl]
    calc algebraMap (MvPolynomial ℕ ℂ) CascadeField DA
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField DB * (A * fx m + B)
        = (algebraMap (MvPolynomial ℕ ℂ) CascadeField DA * A)
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField DB * fx m
          + (algebraMap (MvPolynomial ℕ ℂ) CascadeField DB * B)
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField DA := by ring
      _ = algebraMap (MvPolynomial ℕ ℂ) CascadeField NA
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField DB * fx m
          + algebraMap (MvPolynomial ℕ ℂ) CascadeField NB
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField DA := by
          rw [hvalA, hvalB]
  have hne : A * fx m + B ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at halg
    exact hP0 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp halg.symm)
  refine ⟨DA * DB, P, hP0, ?_, ?_⟩
  · rw [← halg, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  · have hle : MvPolynomial.degreeOf m (DA * DB) = 0 := by
      have := MvPolynomial.degreeOf_mul_le m DA DB
      omega
    rw [hle]
    omega

/-! ## Affine factor families -/

/-- A factor family affine in the newer coordinate: `fac j = lead j · X_(j+1) + cnst j`, with both
coefficients functions of `X_j` alone. -/
structure AffineFam where
  /-- The leading coefficient at level `j`, a function of `X_j`. -/
  lead : ℕ → CascadeField
  /-- The constant term at level `j`, a function of `X_j`. -/
  cnst : ℕ → CascadeField
  lead_ne_zero : ∀ j, lead j ≠ 0
  fpderiv_lead : ∀ {j k : ℕ}, k ≠ j → fpderiv k (lead j) = 0
  fpderiv_cnst : ∀ {j k : ℕ}, k ≠ j → fpderiv k (cnst j) = 0

namespace AffineFam

variable (E : AffineFam)

/-- The factor at level `j`. -/
noncomputable def fac (j : ℕ) : CascadeField := E.lead j * fx (j + 1) + E.cnst j

theorem lead_mem_coordField {j m : ℕ} (h : j ≤ m) : E.lead j ∈ coordField m := by
  rw [mem_coordField_iff]
  exact fun i hi => E.fpderiv_lead (by omega)

theorem cnst_mem_coordField {j m : ℕ} (h : j ≤ m) : E.cnst j ∈ coordField m := by
  rw [mem_coordField_iff]
  exact fun i hi => E.fpderiv_cnst (by omega)

@[simp] theorem fpderiv_fac_top (j : ℕ) : fpderiv (j + 1) (E.fac j) = E.lead j := by
  rw [fac, map_add, Derivation.leibniz, fpderiv_fx_self,
    E.fpderiv_lead (by omega : j + 1 ≠ j), E.fpderiv_cnst (by omega : j + 1 ≠ j)]
  simp

theorem fac_ne_zero (j : ℕ) : E.fac j ≠ 0 := by
  intro h0
  refine E.lead_ne_zero j ?_
  rw [← E.fpderiv_fac_top j, h0, map_zero]

theorem fac_mem_coordField (j : ℕ) : E.fac j ∈ coordField (j + 1) :=
  add_mem (mul_mem (E.lead_mem_coordField (by omega)) (fx_mem_coordField (le_refl (j + 1))))
    (E.cnst_mem_coordField (by omega))

theorem fpderiv_fac_of_ne {j k : ℕ} (h0 : k ≠ j) (h1 : k ≠ j + 1) : fpderiv k (E.fac j) = 0 := by
  rw [fac, map_add, Derivation.leibniz, fpderiv_fx_of_ne (fun h => h1 h.symm),
    E.fpderiv_lead h0, E.fpderiv_cnst h0]
  simp

/-- The underlying abstract factor family. -/
noncomputable def toPairFam : PairFam where
  fac := E.fac
  fac_ne_zero := E.fac_ne_zero
  fac_mem := E.fac_mem_coordField
  fpderiv_fac_of_ne := E.fpderiv_fac_of_ne

@[simp] theorem toPairFam_fac (j : ℕ) : E.toPairFam.fac j = E.fac j := rfl

/-! ## Degrees at the newer coordinate -/

theorem topFree_lead {j m : ℕ} (h : j < m) : TopFree m (E.lead j) :=
  topFree_of_mem_coordField h (E.lead_mem_coordField (le_refl j))

theorem topFree_cnst {j m : ℕ} (h : j < m) : TopFree m (E.cnst j) :=
  topFree_of_mem_coordField h (E.cnst_mem_coordField (le_refl j))

theorem topDegLE_fac_top (j : ℕ) : TopDegLE (j + 1) 1 (E.fac j) := by
  rw [fac]
  have h := TopDegLE.add
    (TopDegLE.mul (E.topFree_lead (by omega : j < j + 1)).topDegLE (topDegLE_fx (j + 1)))
    (TopDegLE.mono (by norm_num) (E.topFree_cnst (by omega : j < j + 1)).topDegLE)
  simpa using h

/-- **The factor's inverse drops a degree in the newer coordinate.** -/
theorem topDegLE_inv_fac (j : ℕ) : TopDegLE (j + 1) (-1) ((E.fac j)⁻¹) :=
  topDegLE_inv_affine (E.lead_ne_zero j) (E.topFree_lead (by omega))
    (E.topFree_cnst (by omega))

/-- **The logarithmic residue at the border is one.** -/
theorem topLim_fx_mul_logTerm_top (j : ℕ) :
    TopLim (j + 1) (fx (j + 1) * E.toPairFam.logTerm j (j + 1)) 1 := by
  have hne : E.fac j ≠ 0 := E.fac_ne_zero j
  have hval : fx (j + 1) * E.toPairFam.logTerm j (j + 1) - 1
      = -(E.cnst j) * (E.fac j)⁻¹ := by
    rw [PairFam.logTerm, toPairFam_fac, E.fpderiv_fac_top j, div_eq_mul_inv]
    field_simp
    rw [fac]
    ring
  rw [TopLim, hval]
  have hb : TopFree (j + 1) (-(E.cnst j)) :=
    TopFree.neg (E.topFree_cnst (by omega))
  have h := TopDegLE.mul hb.topDegLE (E.topDegLE_inv_fac j)
  simpa using h

end AffineFam

end GaloisForLFunctions.HTGeometry
