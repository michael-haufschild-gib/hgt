import GaloisForLFunctions.HTGeometry.DbarFormsBasic
import GaloisForLFunctions.HTGeometry.DbarProductSolve

/-!
# `(0,q)`-forms indexed by sets of directions

The Dolbeault induction needs the decomposition of a form into the part containing a distinguished
direction and the part free of it, and that decomposition is available only for alternating
families.  Indexing the coefficients by finite sets of directions makes it definitional: the sets
containing `k` are exactly the `insert k` images of the sets not containing it.

The differential inserts a direction with the sign given by the number of smaller elements already
present.

* `HTGeometry.SetForm` : coefficients indexed by finite sets of directions.
* `HTGeometry.insertSign` : the insertion sign.
* `HTGeometry.setDbar` : the Dolbeault operator in this indexing.
* `HTGeometry.SetFormBelow` : the form uses only directions below an index.
-/

namespace HTGeometry

open Complex

section SetForms

variable {n : ℕ}

/-- A `(0,q)`-form with coefficients indexed by finite sets of directions.  The degree is carried by
the cardinality of the index rather than by the type. -/
def SetForm (n : ℕ) : Type := Finset (Fin n) → (Fin n → ℂ) → ℂ

/-- The sign with which a direction is inserted into a set: the parity of the number of smaller
directions already present. -/
def insertSign (k : Fin n) (S : Finset (Fin n)) : ℂ :=
  (-1 : ℂ) ^ (S.filter (fun j => j < k)).card

/-- **The Dolbeault operator on set-indexed forms.**  The coefficient at `S` is the signed sum of
the antiholomorphic derivatives of the coefficients at the sets obtained by deleting one direction
of `S`. -/
noncomputable def setDbar (f : SetForm n) : SetForm n :=
  fun S z => ∑ k ∈ S, insertSign k (S.erase k) * dzbarAt (f (S.erase k)) k z

/-- A form is smooth when all its coefficients are. -/
def SmoothSetForm (f : SetForm n) : Prop :=
  ∀ S : Finset (Fin n), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f S)

/-- The difference of two set-indexed forms. -/
def setFormSub (f g : SetForm n) : SetForm n := fun S z => f S z - g S z

@[simp] theorem setFormSub_apply (f g : SetForm n) (S : Finset (Fin n)) (z : Fin n → ℂ) :
    setFormSub f g S z = f S z - g S z := rfl

theorem SmoothSetForm.sub {f g : SetForm n} (hf : SmoothSetForm f) (hg : SmoothSetForm g) :
    SmoothSetForm (setFormSub f g) := fun S => (hf S).sub (hg S)

theorem SmoothSetForm.differentiable {f : SetForm n} (hf : SmoothSetForm f) (S : Finset (Fin n)) :
    Differentiable ℝ (f S) := (hf S).differentiable (by simp)

/-- **The Dolbeault operator preserves smoothness.** -/
theorem setDbar_smooth {f : SetForm n} (hf : SmoothSetForm f) : SmoothSetForm (setDbar f) := by
  intro S
  refine ContDiff.sum fun k _ => ?_
  exact contDiff_const.mul (contDiff_infty_dzbarAt (hf _) k)

/-- **The Dolbeault operator is subtractive.** -/
theorem setDbar_sub {f g : SetForm n} (hf : SmoothSetForm f) (hg : SmoothSetForm g)
    (S : Finset (Fin n)) (z : Fin n → ℂ) :
    setDbar (setFormSub f g) S z = setDbar f S z - setDbar g S z := by
  show (∑ k ∈ S, insertSign k (S.erase k) *
      dzbarAt (setFormSub f g (S.erase k)) k z) = _
  have hterm : ∀ k ∈ S,
      insertSign k (S.erase k) * dzbarAt (setFormSub f g (S.erase k)) k z
        = insertSign k (S.erase k) * dzbarAt (f (S.erase k)) k z
          - insertSign k (S.erase k) * dzbarAt (g (S.erase k)) k z := by
    intro k _
    rw [show setFormSub f g (S.erase k) = fun z => f (S.erase k) z - g (S.erase k) z from rfl,
      dzbarAt_sub (hf.differentiable _) (hg.differentiable _) k z, mul_sub]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  rfl

/-- A set-indexed form uses only the directions below an index. -/
def SetFormBelow (m : ℕ) (f : SetForm n) (P : Set (Fin n → ℂ)) : Prop :=
  ∀ S : Finset (Fin n), (∃ k ∈ S, m ≤ (k : ℕ)) → ∀ z ∈ P, f S z = 0

theorem SetFormBelow.mono {m m' : ℕ} (hmm' : m ≤ m') {f : SetForm n} {P : Set (Fin n → ℂ)}
    (hf : SetFormBelow m f P) : SetFormBelow m' f P := by
  intro S hS z hz
  obtain ⟨k, hkS, hk⟩ := hS
  exact hf S ⟨k, hkS, le_trans hmm' hk⟩ z hz

/-- **The Dolbeault operator on a set containing a distinguished direction separates that
direction.**  The term of the distinguished direction is its own derivative of the coefficient at
the complement; every other term keeps the direction inside the index. -/
theorem setDbar_insert {f : SetForm n} {k : Fin n} {T : Finset (Fin n)} (hk : k ∉ T)
    (z : Fin n → ℂ) :
    setDbar f (insert k T) z
      = insertSign k T * dzbarAt (f T) k z
        + ∑ j ∈ T, insertSign j ((insert k T).erase j) *
            dzbarAt (f ((insert k T).erase j)) j z := by
  show (∑ j ∈ insert k T, insertSign j ((insert k T).erase j) *
      dzbarAt (f ((insert k T).erase j)) j z) = _
  rw [Finset.sum_insert hk]
  congr 1
  rw [Finset.erase_insert hk]

end SetForms

section Transform

variable {n : ℕ}

theorem insertSign_ne_zero (k : Fin n) (S : Finset (Fin n)) : insertSign k S ≠ 0 := by
  rw [insertSign]
  exact pow_ne_zero _ (by norm_num)

theorem insertSign_mul_inv (k : Fin n) (S : Finset (Fin n)) :
    insertSign k S * (insertSign k S)⁻¹ = 1 :=
  mul_inv_cancel₀ (insertSign_ne_zero k S)

/-- **The coordinatewise primitive of the top coefficients**, normalized by the insertion sign and
extended by zero on the sets that already contain the distinguished direction. -/
noncomputable def setTransform (f : SetForm n) (chi : ℂ → ℝ) (psi : (Fin n → ℂ) → ℝ)
    (k : Fin n) : SetForm n := fun T =>
  if k ∈ T then 0
  else (insertSign k T)⁻¹ •
    dbarSliceSolution
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k

@[simp] theorem setTransform_of_mem {f : SetForm n} {chi psi} {k : Fin n} {T : Finset (Fin n)}
    (hk : k ∈ T) : setTransform f chi psi k T = 0 := by
  rw [setTransform, if_pos hk]

theorem setTransform_of_notMem {f : SetForm n} {chi psi} {k : Fin n} {T : Finset (Fin n)}
    (hk : k ∉ T) :
    setTransform f chi psi k T
      = (insertSign k T)⁻¹ •
        dbarSliceSolution
          (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k := by
  rw [setTransform, if_neg hk]

/-- **The transform solves in the distinguished direction.**  On the small domain the cutoff is one,
so the coordinatewise Cauchy transform returns the top coefficient, and the normalization by the
insertion sign makes it come out of the differential with coefficient one. -/
theorem setDbar_setTransform_top {f : SetForm n} {chi : ℂ → ℝ} {psi : (Fin n → ℂ) → ℝ}
    {k : Fin n} {T : Finset (Fin n)} (hk : k ∉ T) {S M M₀ : ℝ}
    (hC1 : ContDiff ℝ 1 (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)))
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ →
      (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x) = 0)
    {z : Fin n → ℂ} (hchione : chi (z k) = 1) (hpsione : psi z = 1) :
    insertSign k T * dzbarAt (setTransform f chi psi k T) k z = f (insert k T) z := by
  rw [setTransform_of_notMem hk]
  have hlin : dzbarAt ((insertSign k T)⁻¹ • dbarSliceSolution
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k) k z
      = (insertSign k T)⁻¹ * dzbarAt (dbarSliceSolution
        (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k) k z := by
    have hwa0 : wirtingerAntihol (0 : ℂ →L[ℝ] ℂ) = 0 := by
      show ((0 : ℂ →L[ℝ] ℂ) 1 + Complex.I * (0 : ℂ →L[ℝ] ℂ) Complex.I) / 2 = 0
      simp
    have hd : ∀ (c : ℂ) (F : (Fin n → ℂ) → ℂ),
        dzbarAt (c • F) k z = c * dzbarAt F k z := by
      intro c F
      show dzbar (dbarSlice (fun x => c * F x) k z) (z k) = _
      have hslice : dbarSlice (fun x => c * F x) k z = fun t => c * dbarSlice F k z t := rfl
      rw [hslice]
      show wirtingerAntihol (fderiv ℝ (fun t => c * dbarSlice F k z t) (z k))
        = c * wirtingerAntihol (fderiv ℝ (dbarSlice F k z) (z k))
      by_cases hF : DifferentiableAt ℝ (dbarSlice F k z) (z k)
      · rw [fderiv_const_mul hF]
        show ((c • fderiv ℝ (dbarSlice F k z) (z k)) 1
            + Complex.I * (c • fderiv ℝ (dbarSlice F k z) (z k)) Complex.I) / 2
          = c * ((fderiv ℝ (dbarSlice F k z) (z k) 1
            + Complex.I * fderiv ℝ (dbarSlice F k z) (z k) Complex.I) / 2)
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      · by_cases hc : c = 0
        · simp [hc, hwa0]
        · have hnd : ¬ DifferentiableAt ℝ (fun t => c * dbarSlice F k z t) (z k) := by
            intro hcon
            refine hF ?_
            have := hcon.const_mul c⁻¹
            simpa [hc, mul_comm, mul_assoc, inv_mul_cancel₀ hc] using this
          rw [fderiv_zero_of_not_differentiableAt hF,
            fderiv_zero_of_not_differentiableAt hnd]
          show ((0 : ℂ →L[ℝ] ℂ) 1 + Complex.I * (0 : ℂ →L[ℝ] ℂ) Complex.I) / 2
            = c * (((0 : ℂ →L[ℝ] ℂ) 1 + Complex.I * (0 : ℂ →L[ℝ] ℂ) Complex.I) / 2)
          simp
    exact hd _ _
  rw [hlin, dzbarAt_dbarSliceSolution_of_slab hC1 hgS z]
  show insertSign k T * ((insertSign k T)⁻¹ *
    ((chi (z k) : ℝ) • ((psi z : ℝ) • f (insert k T) z))) = _
  rw [hchione, hpsione, one_smul, one_smul, ← mul_assoc, insertSign_mul_inv, one_mul]

/-- **The residue is free of the distinguished direction.**  On a set containing `k` the
differential of the transform is exactly the top coefficient: the `k`-term reproduces it, and every
other term evaluates the transform at a set that still contains `k`, where it is zero. -/
theorem setDbar_setTransform_eq {f : SetForm n} {chi : ℂ → ℝ} {psi : (Fin n → ℂ) → ℝ}
    {k : Fin n} {T : Finset (Fin n)} (hk : k ∉ T) {S : ℝ}
    (hC1 : ContDiff ℝ 1 (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)))
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ →
      (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x) = 0)
    {z : Fin n → ℂ} (hchione : chi (z k) = 1) (hpsione : psi z = 1) :
    setDbar (setTransform f chi psi k) (insert k T) z = f (insert k T) z := by
  rw [setDbar_insert hk]
  have hzero : ∀ j ∈ T, setTransform f chi psi k ((insert k T).erase j) = 0 := by
    intro j hj
    refine setTransform_of_mem ?_
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_insert_self k T⟩
    intro hcon
    exact hk (hcon ▸ hj)
  have hsum : (∑ j ∈ T, insertSign j ((insert k T).erase j) *
      dzbarAt (setTransform f chi psi k ((insert k T).erase j)) j z) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hzero j hj]
    have hz0 : dzbarAt (fun _ : Fin n → ℂ => (0 : ℂ)) j z = 0 := dzbarAt_zero j z
    rw [show (0 : (Fin n → ℂ) → ℂ) = fun _ : Fin n → ℂ => (0 : ℂ) from rfl, hz0, mul_zero]
  rw [hsum, add_zero]
  exact setDbar_setTransform_top (M := 0) (M₀ := 0) hk hC1 hgS hchione hpsione


/-- **The residue vanishes on every set containing the distinguished direction.** -/
theorem setFormSub_setTransform_eq_zero {f : SetForm n} {chi : ℂ → ℝ} {psi : (Fin n → ℂ) → ℝ}
    {k : Fin n} {T : Finset (Fin n)} (hk : k ∉ T) {S : ℝ}
    (hC1 : ContDiff ℝ 1 (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)))
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ →
      (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x) = 0)
    {z : Fin n → ℂ} (hchione : chi (z k) = 1) (hpsione : psi z = 1) :
    setFormSub f (setDbar (setTransform f chi psi k)) (insert k T) z = 0 := by
  show f (insert k T) z - setDbar (setTransform f chi psi k) (insert k T) z = 0
  rw [setDbar_setTransform_eq hk hC1 hgS hchione hpsione, sub_self]


/-- **The transform is annihilated by every direction along which the top coefficient is already
`∂̄`-closed on the domain.**  This is the second clause of the induction step, in the set model: it
is the degree-one argument, with the coefficient now indexed by a set. -/
theorem dzbarAt_setTransform_eq_zero {f : SetForm n} {D D' : Fin n → Set ℂ} {k j : Fin n}
    (hjk : j ≠ k) (hD : ∀ i, D' i ⊆ D i) (hopen : ∀ i, IsOpen (D i))
    (chi : ℂ → ℝ) (psi : (Fin n → ℂ) → ℝ)
    (hchi : ∀ t : ℂ, chi t ≠ 0 → t ∈ D k)
    (hpsione : ∀ y ∈ productDomain D, psi y = 1)
    {T : Finset (Fin n)} (hk : k ∉ T) {S M M₀ : ℝ}
    (hC1 : ContDiff ℝ 1 (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)))
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ →
      (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x) = 0)
    (hdS : ∀ x : Fin n → ℂ, S < ‖x k‖ →
      fderiv ℝ (fun y : Fin n → ℂ => (chi (y k) : ℝ) • ((psi y : ℝ) • f (insert k T) y)) x = 0)
    (hM : ∀ x : Fin n → ℂ,
      ‖fderiv ℝ (fun y : Fin n → ℂ => (chi (y k) : ℝ) • ((psi y : ℝ) • f (insert k T) y)) x‖ ≤ M)
    (hM₀ : ∀ x : Fin n → ℂ, ‖(chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)‖ ≤ M₀)
    (hvanish : ∀ y ∈ productDomain D, dzbarAt (f (insert k T)) j y = 0)
    {z : Fin n → ℂ} (hz : z ∈ productDomain D') :
    dzbarAt (setTransform f chi psi k T) j z = 0 := by
  rw [setTransform_of_notMem hk]
  have hbase : dzbarAt (dbarSliceSolution
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k) j z = 0 := by
    refine dzbarAt_dbarSliceSolution_eq_zero hjk hC1 hgS hdS hM hM₀ z ?_
    intro t
    have hslice : dzbarAt
        (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) j
          (Function.update z k t)
        = (chi t : ℝ) • dzbarAt
            (fun x : Fin n → ℂ => (psi x : ℝ) • f (insert k T) x) j (Function.update z k t) := by
      rw [dzbarAt_slabCutoff_smul hjk chi, Function.update_self]
    rw [hslice]
    by_cases ht : chi t = 0
    · rw [ht, zero_smul]
    · have hmem : Function.update z k t ∈ productDomain D :=
        update_mem_productDomain (productDomain_mono hD hz) (hchi t ht)
      have hloc : dzbarAt (fun x : Fin n → ℂ => (psi x : ℝ) • f (insert k T) x) j
            (Function.update z k t)
          = dzbarAt (f (insert k T)) j (Function.update z k t) := by
        refine dzbarAt_congr_of_eventuallyEq ?_
        refine Filter.eventually_of_mem ((isOpen_productDomain hopen).mem_nhds hmem)
          (fun y hy => ?_)
        show (psi y : ℝ) • f (insert k T) y = f (insert k T) y
        rw [hpsione y hy, one_smul]
      rw [hloc, hvanish _ hmem, smul_zero]
  have hd : dzbarAt ((insertSign k T)⁻¹ • dbarSliceSolution
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k) j z
      = (insertSign k T)⁻¹ * dzbarAt (dbarSliceSolution
        (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k) j z := by
    show dzbar (dbarSlice (fun x => (insertSign k T)⁻¹ * dbarSliceSolution
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k x) j z) (z j) = _
    have hslice : dbarSlice (fun x => (insertSign k T)⁻¹ * dbarSliceSolution
        (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k x) j z
        = fun t => (insertSign k T)⁻¹ * dbarSlice (dbarSliceSolution
          (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k) j z t := rfl
    rw [hslice]
    set F := dbarSlice (dbarSliceSolution
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)) k) j z with hF
    set c : ℂ := (insertSign k T)⁻¹ with hc
    show wirtingerAntihol (fderiv ℝ (fun t => c * F t) (z j))
      = c * wirtingerAntihol (fderiv ℝ F (z j))
    by_cases hFd : DifferentiableAt ℝ F (z j)
    · rw [fderiv_const_mul hFd]
      show ((c • fderiv ℝ F (z j)) 1 + Complex.I * (c • fderiv ℝ F (z j)) Complex.I) / 2
        = c * ((fderiv ℝ F (z j) 1 + Complex.I * fderiv ℝ F (z j) Complex.I) / 2)
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    · have hwa0 : wirtingerAntihol (0 : ℂ →L[ℝ] ℂ) = 0 := by
        show ((0 : ℂ →L[ℝ] ℂ) 1 + Complex.I * (0 : ℂ →L[ℝ] ℂ) Complex.I) / 2 = 0
        simp
      by_cases hc0 : c = 0
      · simp [hc0, hwa0]
      · have hnd : ¬ DifferentiableAt ℝ (fun t => c * F t) (z j) := by
          intro hcon
          refine hFd ?_
          have := hcon.const_mul c⁻¹
          simpa [hc0, mul_comm, mul_assoc, inv_mul_cancel₀ hc0] using this
        rw [fderiv_zero_of_not_differentiableAt hFd,
          fderiv_zero_of_not_differentiableAt hnd, hwa0, mul_zero]
  rw [hd, hbase, mul_zero]


end Transform

section Closedness

variable {n : ℕ}

/-- **Closedness forces the derivative along a direction in which the form vanishes.**  Expanding
`∂̄f` at the set obtained by inserting that direction, every summand but one differentiates a
coefficient at a set that still contains it, hence a coefficient vanishing on the domain; what is
left is the wanted derivative times a unit. -/
theorem dzbarAt_eq_zero_of_setDbar_zero {f : SetForm n} {P : Set (Fin n → ℂ)} (hP : IsOpen P)
    (hclosed : ∀ S : Finset (Fin n), ∀ z ∈ P, setDbar f S z = 0)
    {l : Fin n} {W : Finset (Fin n)} (hl : l ∉ W)
    (hvan : ∀ S : Finset (Fin n), l ∈ S → ∀ z ∈ P, f S z = 0)
    {z : Fin n → ℂ} (hz : z ∈ P) :
    dzbarAt (f W) l z = 0 := by
  have hexp := setDbar_insert (f := f) hl z
  have hzero : (∑ j ∈ W, insertSign j ((insert l W).erase j) *
      dzbarAt (f ((insert l W).erase j)) j z) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjl : j ≠ l := by
      intro hcon
      exact hl (hcon ▸ hj)
    have hlmem : l ∈ (insert l W).erase j :=
      Finset.mem_erase.2 ⟨fun hcon => hjl hcon.symm, Finset.mem_insert_self l W⟩
    have hzeroF : dzbarAt (f ((insert l W).erase j)) j z = 0 := by
      refine dzbarAt_eq_zero_of_eventually_zero ?_
      exact Filter.eventually_of_mem (hP.mem_nhds hz)
        fun y hy => hvan _ hlmem y hy
    rw [hzeroF, mul_zero]
  have h0 := hclosed (insert l W) z hz
  rw [hexp, hzero, add_zero] at h0
  have hne := insertSign_ne_zero l W
  exact (mul_eq_zero.1 h0).resolve_left hne

end Closedness

section Step

variable {n : ℕ}

/-- **The `(0,q)` Dolbeault induction step.**  Subtracting the differential of the transform lowers
by one the highest direction the form uses. -/
theorem setDbar_step_below {f : SetForm n} {D D' : Fin n → Set ℂ} {k : Fin n} {m : ℕ}
    (hkm : (k : ℕ) = m) (hD : ∀ i, D' i ⊆ D i) (hopen : ∀ i, IsOpen (D i))
    (chi : ℂ → ℝ) (psi : (Fin n → ℂ) → ℝ)
    (hchi : ∀ t : ℂ, chi t ≠ 0 → t ∈ D k)
    (hchione : ∀ z ∈ productDomain D', chi (z k) = 1)
    (hpsione : ∀ z ∈ productDomain D, psi z = 1)
    (Sr M M₀ : Finset (Fin n) → ℝ)
    (hC1 : ∀ T, ContDiff ℝ 1
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)))
    (hgS : ∀ T, ∀ x : Fin n → ℂ, Sr T < ‖x k‖ →
      (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x) = 0)
    (hdS : ∀ T, ∀ x : Fin n → ℂ, Sr T < ‖x k‖ →
      fderiv ℝ (fun y : Fin n → ℂ => (chi (y k) : ℝ) • ((psi y : ℝ) • f (insert k T) y)) x = 0)
    (hMb : ∀ T, ∀ x : Fin n → ℂ,
      ‖fderiv ℝ (fun y : Fin n → ℂ => (chi (y k) : ℝ) • ((psi y : ℝ) • f (insert k T) y)) x‖
        ≤ M T)
    (hM₀b : ∀ T, ∀ x : Fin n → ℂ,
      ‖(chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)‖ ≤ M₀ T)
    (hclosed : ∀ S : Finset (Fin n), ∀ z ∈ productDomain D, setDbar f S z = 0)
    (hbelow : SetFormBelow (m + 1) f (productDomain D)) :
    SetFormBelow m (setFormSub f (setDbar (setTransform f chi psi k))) (productDomain D') := by
  intro S hS z hz
  obtain ⟨l, hlS, hlm⟩ := hS
  have hzD : z ∈ productDomain D := productDomain_mono hD hz
  by_cases hkS : k ∈ S
  · have heq : S = insert k (S.erase k) := (Finset.insert_erase hkS).symm
    rw [heq]
    exact setFormSub_setTransform_eq_zero (Finset.notMem_erase k S) (hC1 _) (hgS _)
      (hchione z hz) (hpsione z hzD)
  · have hlk : l ≠ k := fun hcon => hkS (hcon ▸ hlS)
    have hlgt : m + 1 ≤ (l : ℕ) := by
      rcases lt_or_eq_of_le hlm with h | h
      · omega
      · exact absurd (Fin.ext (by omega : (l : ℕ) = (k : ℕ))) hlk
    have hvanl : ∀ S' : Finset (Fin n), l ∈ S' → ∀ y ∈ productDomain D, f S' y = 0 :=
      fun S' hS' y hy => hbelow S' ⟨l, hS', hlgt⟩ y hy
    have hfS : f S z = 0 := hvanl S hlS z hzD
    show f S z - setDbar (setTransform f chi psi k) S z = 0
    have hdb : setDbar (setTransform f chi psi k) S z = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjk : j ≠ k := fun hcon => hkS (hcon ▸ hj)
      have hkj : k ∉ S.erase j := fun hcon => hkS (Finset.mem_of_mem_erase hcon)
      have hvanish : ∀ y ∈ productDomain D,
          dzbarAt (f (insert k (S.erase j))) j y = 0 := by
        intro y hy
        by_cases hjl : j = l
        · subst hjl
          refine dzbarAt_eq_zero_of_setDbar_zero (isOpen_productDomain hopen) hclosed ?_ hvanl hy
          intro hcon
          rcases Finset.mem_insert.1 hcon with h | h
          · exact hjk h
          · exact (Finset.notMem_erase j S) h
        · refine dzbarAt_eq_zero_of_eventually_zero ?_
          refine Filter.eventually_of_mem
            ((isOpen_productDomain hopen).mem_nhds hy) fun y' hy' => ?_
          refine hvanl _ ?_ y' hy'
          refine Finset.mem_insert_of_mem ?_
          exact Finset.mem_erase.2 ⟨fun hcon => hjl hcon.symm, hlS⟩
      rw [dzbarAt_setTransform_eq_zero hjk hD hopen chi psi hchi hpsione hkj (hC1 _) (hgS _)
        (hdS _) (hMb _) (hM₀b _) hvanish hz, mul_zero]
    rw [hfS, hdb, sub_zero]

end Step

end HTGeometry
