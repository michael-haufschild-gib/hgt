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

section Signs

variable {n : ℕ}

/-- Deleting a direction does not change the count of directions below it. -/
theorem filter_erase_self (S : Finset (Fin n)) (k : Fin n) :
    (S.erase k).filter (fun i => i < k) = S.filter (fun i => i < k) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨-, hiS⟩, hlt⟩
    exact ⟨hiS, hlt⟩
  · rintro ⟨hiS, hlt⟩
    exact ⟨⟨fun h => absurd (h ▸ hlt) (lt_irrefl _), hiS⟩, hlt⟩

/-- Deleting a larger direction does not change the count below a smaller one. -/
theorem filter_erase_two_lt {S : Finset (Fin n)} {j k : Fin n} (hjk : j < k) :
    ((S.erase k).erase j).filter (fun i => i < j) = S.filter (fun i => i < j) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨-, -, hiS⟩, hlt⟩
    exact ⟨hiS, hlt⟩
  · rintro ⟨hiS, hlt⟩
    refine ⟨⟨fun h => absurd (h ▸ hlt) (lt_irrefl _), ?_, hiS⟩, hlt⟩
    intro h
    exact absurd (h ▸ lt_trans hlt hjk) (lt_irrefl _)

/-- Deleting a smaller direction removes exactly one from the count below a larger one. -/
theorem filter_erase_two_lt' {S : Finset (Fin n)} {j k : Fin n} (hjk : j < k) :
    ((S.erase j).erase k).filter (fun i => i < k) = (S.filter (fun i => i < k)).erase j := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨-, hij, hiS⟩, hlt⟩
    exact ⟨hij, hiS, hlt⟩
  · rintro ⟨hij, hiS, hlt⟩
    exact ⟨⟨fun h => absurd (h ▸ hlt) (lt_irrefl _), hij, hiS⟩, hlt⟩

/-- **The two orders of deleting a pair of directions carry opposite signs.** -/
theorem insertSign_swap {S : Finset (Fin n)} {j k : Fin n} (hjk : j < k) (hj : j ∈ S) :
    insertSign k (S.erase k) * insertSign j ((S.erase k).erase j)
      = -(insertSign j (S.erase j) * insertSign k ((S.erase j).erase k)) := by
  have hjmem : j ∈ S.filter (fun i => i < k) := Finset.mem_filter.2 ⟨hj, hjk⟩
  have ha : (S.erase k).filter (fun i => i < k) = S.filter (fun i => i < k) :=
    filter_erase_self S k
  have hb : ((S.erase k).erase j).filter (fun i => i < j) = S.filter (fun i => i < j) :=
    filter_erase_two_lt hjk
  have hc : (S.erase j).filter (fun i => i < j) = S.filter (fun i => i < j) :=
    filter_erase_self S j
  have hd : ((S.erase j).erase k).filter (fun i => i < k)
      = (S.filter (fun i => i < k)).erase j := filter_erase_two_lt' hjk
  have hcard : ((S.filter (fun i => i < k)).erase j).card
      = (S.filter (fun i => i < k)).card - 1 := Finset.card_erase_of_mem hjmem
  have hpos : 1 ≤ (S.filter (fun i => i < k)).card := Finset.card_pos.2 ⟨j, hjmem⟩
  simp only [insertSign, ha, hb, hc, hd, hcard]
  set A := (S.filter (fun i => i < k)).card with hA
  set B := (S.filter (fun i => i < j)).card with hB
  have hAsub : A - 1 + 1 = A := Nat.succ_pred_eq_of_pos hpos
  calc (-1 : ℂ) ^ A * (-1 : ℂ) ^ B
      = -((-1 : ℂ) ^ B * (-1 : ℂ) ^ (A - 1)) := by
        rw [← pow_add, ← pow_add]
        rw [show B + (A - 1) = (A - 1 + B) by omega, show A + B = (A - 1 + B) + 1 by omega]
        rw [pow_succ]
        ring
    _ = -((-1 : ℂ) ^ B * (-1 : ℂ) ^ (A - 1)) := rfl

end Signs

section Linearity

variable {n : ℕ}

/-- **`∂̄_j` is homogeneous under a complex constant.**  The corpus has this for real constants
only; the insertion signs are complex. -/
theorem dzbarAt_const_mul (c : ℂ) (F : (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) :
    dzbarAt (fun x => c * F x) j z = c * dzbarAt F j z := by
  have hwa0 : wirtingerAntihol (0 : ℂ →L[ℝ] ℂ) = 0 := by
    show ((0 : ℂ →L[ℝ] ℂ) 1 + Complex.I * (0 : ℂ →L[ℝ] ℂ) Complex.I) / 2 = 0
    simp
  have hslice : dbarSlice (fun x => c * F x) j z = fun t => c * dbarSlice F j z t := rfl
  show dzbar (dbarSlice (fun x => c * F x) j z) (z j) = c * dzbar (dbarSlice F j z) (z j)
  rw [hslice]
  set G := dbarSlice F j z with hG
  show wirtingerAntihol (fderiv ℝ (fun t => c * G t) (z j))
    = c * wirtingerAntihol (fderiv ℝ G (z j))
  by_cases hGd : DifferentiableAt ℝ G (z j)
  · rw [fderiv_const_mul hGd]
    show ((c • fderiv ℝ G (z j)) 1 + Complex.I * (c • fderiv ℝ G (z j)) Complex.I) / 2
      = c * ((fderiv ℝ G (z j) 1 + Complex.I * fderiv ℝ G (z j) Complex.I) / 2)
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  · by_cases hc0 : c = 0
    · simp [hc0, hwa0]
    · have hnd : ¬ DifferentiableAt ℝ (fun t => c * G t) (z j) := by
        intro hcon
        refine hGd ?_
        have := hcon.const_mul c⁻¹
        simpa [hc0, mul_comm, mul_assoc, inv_mul_cancel₀ hc0] using this
      rw [fderiv_zero_of_not_differentiableAt hGd,
        fderiv_zero_of_not_differentiableAt hnd, hwa0, mul_zero]

/-- **`∂̄_j` is additive over a finite sum.** -/
theorem dzbarAt_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → (Fin n → ℂ) → ℂ) (hF : ∀ i, Differentiable ℝ (F i)) (j : Fin n) (z : Fin n → ℂ) :
    dzbarAt (fun x => ∑ i ∈ s, F i x) j z = ∑ i ∈ s, dzbarAt (F i) j z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using dzbarAt_zero j z
  | insert a s ha ih =>
      have heq : (fun x : Fin n → ℂ => ∑ i ∈ insert a s, F i x)
          = fun x : Fin n → ℂ => F a x + ∑ i ∈ s, F i x := by
        funext x
        rw [Finset.sum_insert ha]
      have hdsum : Differentiable ℝ (fun x : Fin n → ℂ => ∑ i ∈ s, F i x) := by
        have hfun : (fun x : Fin n → ℂ => ∑ i ∈ s, F i x) = ∑ i ∈ s, F i := by
          funext x
          simp [Finset.sum_apply]
        rw [hfun]
        exact Differentiable.sum fun i _ => hF i
      rw [heq, dzbarAt_add (hF a) hdsum j z, ih, Finset.sum_insert ha]

end Linearity

section Square

variable {n : ℕ}

/-- **The double differential expands into a sum over ordered pairs of distinct directions.** -/
theorem setDbar_setDbar_expand {f : SetForm n} (hf : ∀ S : Finset (Fin n), ContDiff ℝ 2 (f S))
    (S : Finset (Fin n)) (z : Fin n → ℂ) :
    setDbar (setDbar f) S z
      = ∑ k ∈ S, ∑ j ∈ S.erase k,
          (insertSign k (S.erase k) * insertSign j ((S.erase k).erase j)) *
            dzbarAt (dzbarAt (f ((S.erase k).erase j)) j) k z := by
  classical
  show (∑ k ∈ S, insertSign k (S.erase k) * dzbarAt (setDbar f (S.erase k)) k z) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  have hinner : setDbar f (S.erase k)
      = fun y => ∑ j ∈ (S.erase k), insertSign j ((S.erase k).erase j) *
          dzbarAt (f ((S.erase k).erase j)) j y := rfl
  have hdiff : ∀ j : Fin n, Differentiable ℝ
      (fun y : Fin n → ℂ => insertSign j ((S.erase k).erase j) *
        dzbarAt (f ((S.erase k).erase j)) j y) := by
    intro j
    refine Differentiable.const_mul ?_ _
    exact (contDiff_dzbarAt (m := 1) (hf _) j).differentiable (by norm_num)
  rw [hinner, dzbarAt_finset_sum _ _ hdiff k z]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dzbarAt_const_mul, ← mul_assoc]

/-- The two deletion orders give the same set. -/
theorem erase_erase_comm (S : Finset (Fin n)) (k j : Fin n) :
    (S.erase k).erase j = (S.erase j).erase k := by
  ext i
  simp only [Finset.mem_erase]
  tauto

/-- **The Dolbeault operator squares to zero.**  The double sum runs over ordered pairs of distinct
directions, and the transposition of the pair is a fixed-point-free involution whose two terms have
the same iterated derivative, at the same coefficient, with opposite signs. -/
theorem setDbar_setDbar_eq_zero {f : SetForm n} (hf : ∀ S : Finset (Fin n), ContDiff ℝ 2 (f S))
    (S : Finset (Fin n)) (z : Fin n → ℂ) : setDbar (setDbar f) S z = 0 := by
  classical
  rw [setDbar_setDbar_expand hf S z]
  rw [Finset.sum_sigma' S (fun k => S.erase k)
    (fun k j => (insertSign k (S.erase k) * insertSign j ((S.erase k).erase j)) *
      dzbarAt (dzbarAt (f ((S.erase k).erase j)) j) k z)]
  have hmem : ∀ (p : Σ _ : Fin n, Fin n), p ∈ S.sigma (fun k => S.erase k) →
      (⟨p.2, p.1⟩ : Σ _ : Fin n, Fin n) ∈ S.sigma (fun k => S.erase k) := by
    rintro ⟨k, j⟩ hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hkS, hj⟩ := hp
    rw [Finset.mem_erase] at hj
    obtain ⟨hjk, hjS⟩ := hj
    rw [Finset.mem_sigma]
    exact ⟨hjS, Finset.mem_erase.2 ⟨Ne.symm hjk, hkS⟩⟩
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ hmem ?_
  · rintro ⟨k, j⟩ hp
    rw [Finset.mem_sigma, Finset.mem_erase] at hp
    obtain ⟨hkS, hjk, hjS⟩ := hp
    have hset : (S.erase j).erase k = (S.erase k).erase j := erase_erase_comm S j k
    have hcomm : dzbarAt (dzbarAt (f ((S.erase j).erase k)) k) j z
        = dzbarAt (dzbarAt (f ((S.erase k).erase j)) j) k z := by
      rw [hset]
      exact dzbarAt_comm (hf _) j k z
    show (insertSign k (S.erase k) * insertSign j ((S.erase k).erase j)) *
        dzbarAt (dzbarAt (f ((S.erase k).erase j)) j) k z
      + (insertSign j (S.erase j) * insertSign k ((S.erase j).erase k)) *
        dzbarAt (dzbarAt (f ((S.erase j).erase k)) k) j z = 0
    rw [hcomm]
    rcases lt_trichotomy j k with hlt | heq | hgt
    · rw [insertSign_swap hlt hjS]
      ring
    · exact absurd heq hjk
    · rw [insertSign_swap hgt hkS]
      ring
  · rintro ⟨k, j⟩ hp _
    rw [Finset.mem_sigma, Finset.mem_erase] at hp
    intro hcon
    exact hp.2.1 (congrArg Sigma.fst hcon)
  · rintro ⟨k, j⟩ _
    rfl

end Square

section Additivity

variable {n : ℕ}

/-- The sum of two set-indexed forms. -/
def setFormAdd (f g : SetForm n) : SetForm n := fun S z => f S z + g S z

@[simp] theorem setFormAdd_apply (f g : SetForm n) (S : Finset (Fin n)) (z : Fin n → ℂ) :
    setFormAdd f g S z = f S z + g S z := rfl

theorem SmoothSetForm.add {f g : SetForm n} (hf : SmoothSetForm f) (hg : SmoothSetForm g) :
    SmoothSetForm (setFormAdd f g) := fun S => (hf S).add (hg S)

/-- **The Dolbeault operator is additive.** -/
theorem setDbar_add {f g : SetForm n} (hf : SmoothSetForm f) (hg : SmoothSetForm g)
    (S : Finset (Fin n)) (z : Fin n → ℂ) :
    setDbar (setFormAdd f g) S z = setDbar f S z + setDbar g S z := by
  show (∑ k ∈ S, insertSign k (S.erase k) *
      dzbarAt (setFormAdd f g (S.erase k)) k z) = _
  have hterm : ∀ k ∈ S,
      insertSign k (S.erase k) * dzbarAt (setFormAdd f g (S.erase k)) k z
        = insertSign k (S.erase k) * dzbarAt (f (S.erase k)) k z
          + insertSign k (S.erase k) * dzbarAt (g (S.erase k)) k z := by
    intro k _
    rw [show setFormAdd f g (S.erase k) = fun z => f (S.erase k) z + g (S.erase k) z from rfl,
      dzbarAt_add (hf.differentiable _) (hg.differentiable _) k z, mul_add]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  rfl

/-- The differential of anything is zero at the empty index. -/
@[simp] theorem setDbar_empty (f : SetForm n) (z : Fin n → ℂ) : setDbar f ∅ z = 0 := by
  show (∑ k ∈ (∅ : Finset (Fin n)), insertSign k _ * dzbarAt (f _) k z) = 0
  simp

/-- **The transform is smooth** when the cut-off top coefficients are smooth and compactly
supported. -/
theorem smoothSetForm_setTransform {f : SetForm n} {chi : ℂ → ℝ} {psi : (Fin n → ℂ) → ℝ}
    {k : Fin n}
    (hCG : ∀ T : Finset (Fin n), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)))
    (hcs : ∀ T : Finset (Fin n), HasCompactSupport
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x))) :
    SmoothSetForm (setTransform f chi psi k) := by
  intro T
  by_cases hk : k ∈ T
  · rw [setTransform_of_mem hk]
    exact contDiff_const
  · rw [setTransform_of_notMem hk]
    exact ContDiff.const_smul (c := (insertSign k T)⁻¹)
      (contDiff_infty_dbarSliceSolution _ k (hCG T) (hcs T))

end Additivity


section Degree

variable {n : ℕ}

/-- A form is homogeneous of a given degree. -/
def SetFormDeg (q : ℕ) (f : SetForm n) : Prop :=
  ∀ S : Finset (Fin n), S.card ≠ q → ∀ z : Fin n → ℂ, f S z = 0

/-- A form of positive degree has no degree-zero part. -/
theorem SetFormDeg.empty {q : ℕ} (hq : q ≠ 0) {f : SetForm n} (hf : SetFormDeg q f)
    (z : Fin n → ℂ) : f ∅ z = 0 :=
  hf ∅ (by rw [Finset.card_empty]; exact Ne.symm hq) z

/-- The coordinatewise Cauchy transform of the zero function is zero. -/
theorem dbarSliceSolution_zero (k : Fin n) (y : Fin n → ℂ) :
    dbarSliceSolution (fun _ : Fin n → ℂ => (0 : ℂ)) k y = 0 := by
  rw [dbarSliceSolution_eq_integral]
  simp

/-- **The transform of a form of degree `q + 1` has degree `q`.** -/
theorem setTransform_deg {q : ℕ} {f : SetForm n} (hf : SetFormDeg (q + 1) f)
    (chi : ℂ → ℝ) (psi : (Fin n → ℂ) → ℝ) (k : Fin n) :
    SetFormDeg q (setTransform f chi psi k) := by
  intro T hT z
  by_cases hk : k ∈ T
  · rw [setTransform_of_mem hk]
    rfl
  · rw [setTransform_of_notMem hk]
    have hzero : (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x))
        = fun _ : Fin n → ℂ => (0 : ℂ) := by
      funext x
      rw [hf (insert k T) ?_ x, smul_zero, smul_zero]
      rw [Finset.card_insert_of_notMem hk]
      omega
    rw [hzero]
    show ((insertSign k T)⁻¹ • dbarSliceSolution (fun _ : Fin n → ℂ => (0 : ℂ)) k) z = 0
    rw [Pi.smul_apply, dbarSliceSolution_zero, smul_zero]

/-- The difference of two forms of the same degree has that degree. -/
theorem SetFormDeg.sub {q : ℕ} {f g : SetForm n} (hf : SetFormDeg q f) (hg : SetFormDeg q g) :
    SetFormDeg q (setFormSub f g) := by
  intro S hS z
  show f S z - g S z = 0
  rw [hf S hS z, hg S hS z, sub_zero]

/-- The sum of two forms of the same degree has that degree. -/
theorem SetFormDeg.add {q : ℕ} {f g : SetForm n} (hf : SetFormDeg q f) (hg : SetFormDeg q g) :
    SetFormDeg q (setFormAdd f g) := by
  intro S hS z
  show f S z + g S z = 0
  rw [hf S hS z, hg S hS z, add_zero]

/-- **The differential of a form of degree `q` has degree `q + 1`.** -/
theorem setDbar_deg {q : ℕ} {f : SetForm n} (hf : SetFormDeg q f) :
    SetFormDeg (q + 1) (setDbar f) := by
  intro S hS z
  refine Finset.sum_eq_zero fun k hk => ?_
  have hcard : (S.erase k).card ≠ q := by
    rw [Finset.card_erase_of_mem hk]
    have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨k, hk⟩
    omega
  have hzero : f (S.erase k) = fun _ : Fin n → ℂ => (0 : ℂ) := by
    funext y
    exact hf (S.erase k) hcard y
  rw [hzero, dzbarAt_zero, mul_zero]

end Degree

section Recursion

variable {n : ℕ}

/-- The cut-off top coefficient at one index set. -/
noncomputable def cutCoeff (chi : ℂ → ℝ) (psi : (Fin n → ℂ) → ℝ) (k : Fin n) (f : SetForm n)
    (T : Finset (Fin n)) : (Fin n → ℂ) → ℂ :=
  fun x => (chi (x k) : ℝ) • ((psi x : ℝ) • f (insert k T) x)

/-- **The cut-off data one link of a chain of product domains supplies at a direction.** -/
def StepCutoff (D D' : Fin n → Set ℂ) (k : Fin n) (f : SetForm n) : Prop :=
  ∃ (chi : ℂ → ℝ) (psi : (Fin n → ℂ) → ℝ) (Sr M M₀ : Finset (Fin n) → ℝ),
    (∀ t : ℂ, chi t ≠ 0 → t ∈ D k) ∧
    (∀ z ∈ productDomain D', chi (z k) = 1) ∧
    (∀ z ∈ productDomain D, psi z = 1) ∧
    (∀ T, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutCoeff chi psi k f T)) ∧
    (∀ T, HasCompactSupport (cutCoeff chi psi k f T)) ∧
    (∀ T, ∀ x : Fin n → ℂ, Sr T < ‖x k‖ → cutCoeff chi psi k f T x = 0) ∧
    (∀ T, ∀ x : Fin n → ℂ, Sr T < ‖x k‖ → fderiv ℝ (cutCoeff chi psi k f T) x = 0) ∧
    (∀ T, ∀ x : Fin n → ℂ, ‖fderiv ℝ (cutCoeff chi psi k f T) x‖ ≤ M T) ∧
    (∀ T, ∀ x : Fin n → ℂ, ‖cutCoeff chi psi k f T x‖ ≤ M₀ T)

/-- **The `(0,q)` Dolbeault induction along a chain of product domains.** -/
theorem setDbar_solve_aux (Dom : ℕ → Fin n → Set ℂ)
    (hopen : ∀ o i, IsOpen (Dom o i))
    (hmono : ∀ o i, Dom (o + 1) i ⊆ Dom o i)
    (hcut : ∀ (o : ℕ) (k : Fin n) (f : SetForm n), SmoothSetForm f →
      StepCutoff (Dom o) (Dom (o + 1)) k f) :
    ∀ (m o q : ℕ) (f : SetForm n), SmoothSetForm f → (∀ z, f ∅ z = 0) →
      SetFormDeg (q + 1) f →
      (∀ S : Finset (Fin n), ∀ z ∈ productDomain (Dom o), setDbar f S z = 0) →
      SetFormBelow m f (productDomain (Dom o)) →
      ∃ u : SetForm n, SmoothSetForm u ∧ SetFormDeg q u ∧
        ∀ S : Finset (Fin n), ∀ z ∈ productDomain (Dom (o + m)), setDbar u S z = f S z := by
  intro m
  induction m with
  | zero =>
      intro o q f _ hempty _ _ hbelow
      refine ⟨fun _ _ => 0, fun _ => contDiff_const, fun _ _ _ => rfl, fun S z hz => ?_⟩
      have hzero : setDbar (fun _ _ => (0 : ℂ)) S z = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [show (fun _ _ => (0 : ℂ)) (S.erase k) = fun _ : Fin n → ℂ => (0 : ℂ) from rfl,
          dzbarAt_zero, mul_zero]
      rw [hzero]
      rcases Finset.eq_empty_or_nonempty S with hS | ⟨k, hk⟩
      · rw [hS, hempty z]
      · rw [hbelow S ⟨k, hk, Nat.zero_le _⟩ z hz]
  | succ m ih =>
      intro o q f hCf hempty hdeg hclosed hbelow
      have hstepmono : productDomain (Dom (o + (m + 1))) ⊆ productDomain (Dom (o + m)) := by
        have hidx : o + (m + 1) = (o + m) + 1 := by omega
        rw [hidx]
        exact productDomain_mono fun i => hmono (o + m) i
      by_cases hmn : n ≤ m
      · obtain ⟨u, hCu, hdu, hu⟩ :=
          ih o q f hCf hempty hdeg hclosed (fun S hS z hz => by
            obtain ⟨k, hkS, hk⟩ := hS
            exact absurd hk (by have := k.isLt; omega))
        exact ⟨u, hCu, hdu, fun S z hz => hu S z (hstepmono hz)⟩
      · push_neg at hmn
        set k : Fin n := ⟨m, hmn⟩ with hk
        obtain ⟨chi, psi, Sr, M, M₀, hchi, hchione, hpsione, hCG, hcs, hgS, hdS, hMb, hM₀b⟩ :=
          hcut o k f hCf
        set G : SetForm n := setTransform f chi psi k with hG
        have hCG' : SmoothSetForm G := smoothSetForm_setTransform hCG hcs
        have hres : SetFormBelow m (setFormSub f (setDbar G)) (productDomain (Dom (o + 1))) := by
          refine setDbar_step_below (k := k) rfl (fun i => hmono o i) (hopen o) chi psi hchi
            hchione hpsione Sr M M₀ (fun T => (hCG T).of_le (by exact_mod_cast le_top))
            hgS hdS hMb hM₀b hclosed ?_
          exact hbelow
        have hCres : SmoothSetForm (setFormSub f (setDbar G)) :=
          hCf.sub (setDbar_smooth hCG')
        have hresempty : ∀ z, setFormSub f (setDbar G) ∅ z = 0 := by
          intro z
          show f ∅ z - setDbar G ∅ z = 0
          rw [hempty z, setDbar_empty, sub_zero]
        have hresclosed : ∀ S : Finset (Fin n), ∀ z ∈ productDomain (Dom (o + 1)),
            setDbar (setFormSub f (setDbar G)) S z = 0 := by
          intro S z hz
          rw [setDbar_sub hCf (setDbar_smooth hCG') S z,
            setDbar_setDbar_eq_zero (fun T => (hCG' T).of_le (by decide)) S z,
            hclosed S z (productDomain_mono (fun i => hmono o i) hz), sub_zero]
        have hdG : SetFormDeg q G := setTransform_deg hdeg chi psi k
        have hdres : SetFormDeg (q + 1) (setFormSub f (setDbar G)) :=
          hdeg.sub (setDbar_deg hdG)
        obtain ⟨v, hCv, hdv, hv⟩ := ih (o + 1) q _ hCres hresempty hdres hresclosed hres
        have hidx : o + 1 + m = o + (m + 1) := by omega
        rw [hidx] at hv
        refine ⟨setFormAdd G v, hCG'.add hCv, hdG.add hdv, fun S z hz => ?_⟩
        rw [setDbar_add hCG' hCv S z, hv S z hz]
        show setDbar G S z + (f S z - setDbar G S z) = f S z
        ring

/-- **The `(0,q)` Dolbeault–Grothendieck lemma on a product domain.**  A smooth `∂̄`-closed form of
positive degree on the first domain of a decreasing chain of product domains, each link of which
carries the cut-off data, has a smooth primitive on the `n`-th domain of the chain. -/
theorem setDbar_solve (Dom : ℕ → Fin n → Set ℂ)
    (hopen : ∀ o i, IsOpen (Dom o i))
    (hmono : ∀ o i, Dom (o + 1) i ⊆ Dom o i)
    (hcut : ∀ (o : ℕ) (k : Fin n) (f : SetForm n), SmoothSetForm f →
      StepCutoff (Dom o) (Dom (o + 1)) k f)
    {q : ℕ} {f : SetForm n} (hCf : SmoothSetForm f) (hempty : ∀ z, f ∅ z = 0)
    (hdeg : SetFormDeg (q + 1) f)
    (hclosed : ∀ S : Finset (Fin n), ∀ z ∈ productDomain (Dom 0), setDbar f S z = 0) :
    ∃ u : SetForm n, SmoothSetForm u ∧ SetFormDeg q u ∧
      ∀ S : Finset (Fin n), ∀ z ∈ productDomain (Dom n), setDbar u S z = f S z := by
  have h := setDbar_solve_aux Dom hopen hmono hcut n 0 q f hCf hempty hdeg hclosed
    (fun S hS z hz => by
      obtain ⟨k, hkS, hk⟩ := hS
      exact absurd hk (by have := k.isLt; omega))
  rwa [Nat.zero_add] at h

/-- **The cut-off data follows from a pair of bumps.**  Smoothness and compact support of the
cut-off top coefficients come from the second bump; the slab radii and the two bounds are then the
usual consequences of compact support. -/
theorem stepCutoff_of_bumps {D D' : Fin n → Set ℂ} {k : Fin n} {f : SetForm n}
    (hCf : SmoothSetForm f)
    (chi : ℂ → ℝ) (psi : (Fin n → ℂ) → ℝ)
    (hCchi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi)
    (hCpsi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi) (hcspsi : HasCompactSupport psi)
    (hchi : ∀ t : ℂ, chi t ≠ 0 → t ∈ D k)
    (hchione : ∀ z ∈ productDomain D', chi (z k) = 1)
    (hpsione : ∀ z ∈ productDomain D, psi z = 1) :
    StepCutoff D D' k f := by
  classical
  have hCG : ∀ T : Finset (Fin n), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (cutCoeff chi psi k f T) :=
    fun T => (hCchi.comp (contDiff_apply ℝ ℂ k)).smul (hCpsi.smul (hCf _))
  have hcs : ∀ T : Finset (Fin n), HasCompactSupport (cutCoeff chi psi k f T) := by
    intro T
    refine hcspsi.mono fun x hx => ?_
    by_contra hzero
    simp only [Function.mem_support, not_not] at hzero
    exact hx (by simp [cutCoeff, hzero])
  have hC1 : ∀ T : Finset (Fin n), ContDiff ℝ 1 (cutCoeff chi psi k f T) :=
    fun T => (hCG T).of_le (by exact_mod_cast le_top)
  have hslab : ∀ T : Finset (Fin n), ∃ S : ℝ, 0 < S ∧
      ∀ x : Fin n → ℂ, S < ‖x k‖ → cutCoeff chi psi k f T x = 0 :=
    fun T => exists_slab_of_hasCompactSupport (hcs T) k
  have hslabd : ∀ T : Finset (Fin n), ∃ S : ℝ, 0 < S ∧
      ∀ x : Fin n → ℂ, S < ‖x k‖ → fderiv ℝ (cutCoeff chi psi k f T) x = 0 :=
    fun T => exists_slab_of_hasCompactSupport ((hcs T).fderiv ℝ) k
  have hbd : ∀ T : Finset (Fin n), ∃ M : ℝ,
      ∀ x : Fin n → ℂ, ‖fderiv ℝ (cutCoeff chi psi k f T) x‖ ≤ M :=
    fun T => ((hcs T).fderiv ℝ).exists_bound_of_continuous
      ((hC1 T).continuous_fderiv one_ne_zero)
  have hbd0 : ∀ T : Finset (Fin n), ∃ M₀ : ℝ,
      ∀ x : Fin n → ℂ, ‖cutCoeff chi psi k f T x‖ ≤ M₀ :=
    fun T => (hcs T).exists_bound_of_continuous (hC1 T).continuous
  choose Sr1 _ hSr1 using hslab
  choose Sr2 _ hSr2 using hslabd
  choose M hM using hbd
  choose M₀ hM₀ using hbd0
  refine ⟨chi, psi, fun T => max (Sr1 T) (Sr2 T), M, M₀, hchi, hchione, hpsione, hCG, hcs,
    ?_, ?_, hM, hM₀⟩
  · intro T x hx
    exact hSr1 T x (lt_of_le_of_lt (le_max_left _ _) hx)
  · intro T x hx
    exact hSr2 T x (lt_of_le_of_lt (le_max_right _ _) hx)

end Recursion

section PolydiscInstance

variable {n : ℕ}

/-- The geometric chain of radii interpolating between an outer and an inner polydisc. -/
noncomputable def polydiscChain (r ρ : Fin n → ℝ) (o : ℕ) (i : Fin n) : ℝ :=
  r i - (r i - ρ i) * (1 - (1 / 2 : ℝ) ^ o)

/-- **The `(0,q)` Dolbeault–Grothendieck lemma on a polydisc.** -/
theorem setDbar_polydisc_solve {c : Fin n → ℂ} {r ρ : Fin n → ℝ}
    (hρ : ∀ i, 0 < ρ i) (hρr : ∀ i, ρ i < r i)
    {q : ℕ} {f : SetForm n} (hCf : SmoothSetForm f) (hempty : ∀ z, f ∅ z = 0)
    (hdeg : SetFormDeg (q + 1) f)
    (hclosed : ∀ S : Finset (Fin n), ∀ z ∈ polydisc c r, setDbar f S z = 0) :
    ∃ u : SetForm n, SmoothSetForm u ∧ SetFormDeg q u ∧
      ∀ S : Finset (Fin n), ∀ z ∈ polydisc c ρ, setDbar u S z = f S z := by
  classical
  set R : ℕ → Fin n → ℝ := polydiscChain r ρ with hR
  set Dom : ℕ → Fin n → Set ℂ := fun o i => Metric.ball (c i) (R o i) with hDom
  have hhalf : ∀ o : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ o := fun o => by positivity
  have hhalfle : ∀ o : ℕ, (1 / 2 : ℝ) ^ o ≤ 1 := fun o => pow_le_one₀ (by norm_num) (by norm_num)
  have hhalfstep : ∀ o : ℕ, (1 / 2 : ℝ) ^ (o + 1) < (1 / 2 : ℝ) ^ o := fun o => by
    rw [pow_succ]
    nlinarith [hhalf o]
  have hRgt : ∀ (o : ℕ) (i : Fin n), ρ i < R o i := by
    intro o i
    simp only [hR, polydiscChain]
    nlinarith [hρr i, hhalf o]
  have hRle : ∀ (o : ℕ) (i : Fin n), R o i ≤ r i := by
    intro o i
    simp only [hR, polydiscChain]
    nlinarith [hρr i, hhalfle o]
  have hRstep : ∀ (o : ℕ) (i : Fin n), R (o + 1) i < R o i := by
    intro o i
    simp only [hR, polydiscChain]
    nlinarith [hρr i, hhalfstep o]
  have hRpos : ∀ (o : ℕ) (i : Fin n), 0 < R o i := fun o i => lt_trans (hρ i) (hRgt o i)
  have hR0 : R 0 = r := by
    funext i
    simp [hR, polydiscChain]
  have hopen : ∀ o i, IsOpen (Dom o i) := fun o i => Metric.isOpen_ball
  have hmono : ∀ o i, Dom (o + 1) i ⊆ Dom o i := fun o i =>
    Metric.ball_subset_ball (hRstep o i).le
  set Rmax : ℝ := 1 + ∑ i, |r i| with hRmax
  have hRmaxpos : 0 < Rmax := by
    rw [hRmax]
    positivity
  have hrRmax : ∀ (o : ℕ) (i : Fin n), R o i ≤ Rmax := by
    intro o i
    have h1 : |r i| ≤ ∑ i', |r i'| :=
      Finset.single_le_sum (f := fun i' => |r i'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : r i ≤ |r i| := le_abs_self _
    have h3 := hRle o i
    rw [hRmax]
    linarith
  have hcut : ∀ (o : ℕ) (k : Fin n) (g : SetForm n), SmoothSetForm g →
      StepCutoff (Dom o) (Dom (o + 1)) k g := by
    intro o k g hCg
    obtain ⟨chi, psi, hCchi, hCpsi, hcspsi, hchi, hchione, hpsione⟩ :=
      exists_polydisc_bumps (c := c) (r := R o) (r' := R (o + 1)) (R := Rmax) k
        (hRpos (o + 1) k) (hRstep o k) hRmaxpos (fun i => hrRmax o i)
    exact stepCutoff_of_bumps hCg chi psi hCchi hCpsi hcspsi hchi hchione hpsione
  have hclosed' : ∀ S : Finset (Fin n), ∀ z ∈ productDomain (Dom 0), setDbar f S z = 0 := by
    intro S z hz
    refine hclosed S z ?_
    intro i
    have h := hz i
    show z i ∈ Metric.ball (c i) (r i)
    have hb : Dom 0 i = Metric.ball (c i) (R 0 i) := rfl
    rw [hb, hR0] at h
    exact h
  obtain ⟨u, hCu, hdu, hu⟩ := setDbar_solve Dom hopen hmono hcut hCf hempty hdeg hclosed'
  refine ⟨u, hCu, hdu, fun S z hz => hu S z fun i => ?_⟩
  exact Metric.ball_subset_ball (hRgt n i).le (hz i)

end PolydiscInstance

section PolyannulusInstance

variable {n : ℕ}

/-- **The `(0,q)` Dolbeault–Grothendieck lemma on a polyannulus.** -/
theorem setDbar_polyannulus_solve {a a' b' b : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (haa' : ∀ i, a i < a' i) (ha'b' : ∀ i, a' i < b' i)
    (hb'b : ∀ i, b' i < b i)
    {q : ℕ} {f : SetForm n} (hCf : SmoothSetForm f) (hempty : ∀ z, f ∅ z = 0)
    (hdeg : SetFormDeg (q + 1) f)
    (hclosed : ∀ S : Finset (Fin n), ∀ z ∈ productDomain (fun i => annulus (a i) (b i)),
      setDbar f S z = 0) :
    ∃ u : SetForm n, SmoothSetForm u ∧ SetFormDeg q u ∧
      ∀ S : Finset (Fin n), ∀ z ∈ productDomain (fun i => annulus (a' i) (b' i)),
        setDbar u S z = f S z := by
  classical
  set A : ℕ → Fin n → ℝ := annulusChainIn a a' with hA
  set B : ℕ → Fin n → ℝ := annulusChainOut b b' with hB
  set Dom : ℕ → Fin n → Set ℂ := fun o i => annulus (A o i) (B o i) with hDom
  have hhalf : ∀ o : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ o := fun o => by positivity
  have hhalfle : ∀ o : ℕ, (1 / 2 : ℝ) ^ o ≤ 1 := fun o => pow_le_one₀ (by norm_num) (by norm_num)
  have hhalfstep : ∀ o : ℕ, (1 / 2 : ℝ) ^ (o + 1) < (1 / 2 : ℝ) ^ o := fun o => by
    rw [pow_succ]
    nlinarith [hhalf o]
  have hAlt : ∀ (o : ℕ) (i : Fin n), A o i < a' i := by
    intro o i
    simp only [hA, annulusChainIn]
    nlinarith [haa' i, hhalf o]
  have hBgt : ∀ (o : ℕ) (i : Fin n), b' i < B o i := by
    intro o i
    simp only [hB, annulusChainOut]
    nlinarith [hb'b i, hhalf o]
  have hAge : ∀ (o : ℕ) (i : Fin n), a i ≤ A o i := by
    intro o i
    simp only [hA, annulusChainIn]
    nlinarith [haa' i, hhalfle o]
  have hBle : ∀ (o : ℕ) (i : Fin n), B o i ≤ b i := by
    intro o i
    simp only [hB, annulusChainOut]
    nlinarith [hb'b i, hhalfle o]
  have hAstep : ∀ (o : ℕ) (i : Fin n), A o i < A (o + 1) i := by
    intro o i
    simp only [hA, annulusChainIn]
    nlinarith [haa' i, hhalfstep o]
  have hBstep : ∀ (o : ℕ) (i : Fin n), B (o + 1) i < B o i := by
    intro o i
    simp only [hB, annulusChainOut]
    nlinarith [hb'b i, hhalfstep o]
  have hAnn : ∀ (o : ℕ) (i : Fin n), 0 ≤ A o i := fun o i => le_trans (ha i) (hAge o i)
  have hABstep : ∀ (o : ℕ) (i : Fin n), A o i < B o i := fun o i => by
    have h1 := hAlt o i
    have h2 := ha'b' i
    have h3 := hBgt o i
    linarith
  have hA0 : A 0 = a := by
    funext i
    simp [hA, annulusChainIn]
  have hB0 : B 0 = b := by
    funext i
    simp [hB, annulusChainOut]
  have hopen : ∀ o i, IsOpen (Dom o i) := fun o i => isOpen_annulus _ _
  have hmono : ∀ o i, Dom (o + 1) i ⊆ Dom o i := fun o i =>
    annulus_mono (hAstep o i).le (hBstep o i).le
  set Rmax : ℝ := 1 + ∑ i, |b i| with hRmax
  have hRmaxpos : 0 < Rmax := by
    rw [hRmax]
    positivity
  have hbRmax : ∀ i : Fin n, b i ≤ Rmax := by
    intro i
    have h1 : |b i| ≤ ∑ i', |b i'| :=
      Finset.single_le_sum (f := fun i' => |b i'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : b i ≤ |b i| := le_abs_self _
    rw [hRmax]
    linarith
  have hbounded : ∀ (o : ℕ) (z : Fin n → ℂ), z ∈ productDomain (Dom o) → ∀ i, ‖z i‖ ≤ Rmax :=
    fun o z hz i => le_of_lt (lt_of_lt_of_le (hz i).2 (le_trans (hBle o i) (hbRmax i)))
  have hcut : ∀ (o : ℕ) (k : Fin n) (g : SetForm n), SmoothSetForm g →
      StepCutoff (Dom o) (Dom (o + 1)) k g := by
    intro o k g hCg
    obtain ⟨chi, hCchi, hchisupp, hchione⟩ :=
      exists_annulus_cutoff (a := A o k) (a' := A (o + 1) k) (b' := B (o + 1) k) (b := B o k)
        (hAnn o k) (hAstep o k) (hABstep (o + 1) k) (hBstep o k)
    obtain ⟨psi, hCpsi, hcspsi, hpsione⟩ :=
      exists_bounded_bump (D := Dom o) (R := Rmax) hRmaxpos (hbounded o)
    exact stepCutoff_of_bumps hCg chi psi hCchi hCpsi hcspsi hchisupp
      (fun z hz => hchione (z k) (hz k)) hpsione
  have hclosed' : ∀ S : Finset (Fin n), ∀ z ∈ productDomain (Dom 0), setDbar f S z = 0 := by
    intro S z hz
    refine hclosed S z fun i => ?_
    have h := hz i
    show z i ∈ annulus (a i) (b i)
    have hb : Dom 0 i = annulus (A 0 i) (B 0 i) := rfl
    rw [hb, hA0, hB0] at h
    exact h
  obtain ⟨u, hCu, hdu, hu⟩ := setDbar_solve Dom hopen hmono hcut hCf hempty hdeg hclosed'
  refine ⟨u, hCu, hdu, fun S z hz => hu S z fun i => ?_⟩
  exact ⟨lt_trans (hAlt n i) (hz i).1, lt_trans (hz i).2 (hBgt n i)⟩

end PolyannulusInstance



end HTGeometry
