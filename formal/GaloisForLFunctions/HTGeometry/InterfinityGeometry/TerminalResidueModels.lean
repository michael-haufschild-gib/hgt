import GaloisForLFunctions.HTGeometry.InterfinityGeometry.TerminalTransgression

/-!
# Two models for the terminal residue

Two explicit terminal data show what the transgression theory does and does not decide.

*Curved nonvacuity.*  On the monoid `ℝ≥0 × C₂` acting on `ℂ` by `π(r t) = e^{-t}` and `π(g) = −1`,
the one-cochain `b(r t) = e^{-t} − 1`, `b(r t · g) = 0` is radially flat with stable primitive
`η = 1`, and the central involution is normalized by the whole ray.  Its flat transgression
therefore vanishes, yet the residue is `2`, produced entirely by the oriented difference of the two
bulk curvature faces `ω_b(r t, g) = 1 − e^{-t}` and `ω_b(g, r t) = e^{-t} − 1`.

*Free-source universality.*  On the free product `ℝ≥0 * F_n^+`, represented by `e^{-t}` on the time
ray and by the identity on every free generator, a genuine cocycle can take arbitrary prescribed
values on the generators.  Hence, before source relations are imposed, residues carry no
information at all.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open Filter Topology NNReal

noncomputable section

/-! ## The affine monoid of a module -/

/-- Pairs `(v, a)` acting on a module by `w ↦ v + a • w`. -/
@[ext] structure AffineMonoid (R : Type*) (E : Type*) [Monoid R] [AddCommMonoid E]
    [DistribMulAction R E] where
  /-- The translation part. -/
  vec : E
  /-- The scaling part. -/
  scal : R

namespace AffineMonoid

variable {R E : Type*} [Monoid R] [AddCommMonoid E] [DistribMulAction R E]

instance : One (AffineMonoid R E) := ⟨⟨0, 1⟩⟩

instance : Mul (AffineMonoid R E) :=
  ⟨fun x y => ⟨x.vec + x.scal • y.vec, x.scal * y.scal⟩⟩

@[simp] theorem one_vec : (1 : AffineMonoid R E).vec = 0 := rfl
@[simp] theorem one_scal : (1 : AffineMonoid R E).scal = 1 := rfl
@[simp] theorem mul_vec (x y : AffineMonoid R E) : (x * y).vec = x.vec + x.scal • y.vec := rfl
@[simp] theorem mul_scal (x y : AffineMonoid R E) : (x * y).scal = x.scal * y.scal := rfl

instance : Monoid (AffineMonoid R E) where
  one_mul x := by
    refine AffineMonoid.ext ?_ ?_ <;> simp
  mul_one x := by
    refine AffineMonoid.ext ?_ ?_ <;> simp
  mul_assoc x y z := by
    refine AffineMonoid.ext ?_ ?_ <;> simp [smul_add, smul_smul, add_assoc, mul_assoc]

end AffineMonoid

/-! ## The free-source model -/

section FreeSource

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- The free product of the time ray with a free monoid on `n` generators. -/
abbrev FreeSourceMonoid (n : ℕ) := Monoid.Coprod (Multiplicative ℝ≥0) (FreeMonoid (Fin n))

/-- The time ray of the free-source model, represented by exponential decay. -/
def freeTimeHom (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Multiplicative ℝ≥0 →* AffineMonoid ℝ E where
  toFun V := ⟨0, Real.exp (-((Multiplicative.toAdd V : ℝ≥0) : ℝ))⟩
  map_one' := by
    refine AffineMonoid.ext rfl ?_
    show Real.exp (-((Multiplicative.toAdd (1 : Multiplicative ℝ≥0) : ℝ≥0) : ℝ)) = 1
    simp
  map_mul' V W := by
    refine AffineMonoid.ext ?_ ?_
    · show (0 : E) = 0 + (Real.exp _) • (0 : E)
      simp
    · show Real.exp (-((Multiplicative.toAdd (V * W) : ℝ≥0) : ℝ)) =
        Real.exp (-((Multiplicative.toAdd V : ℝ≥0) : ℝ)) *
          Real.exp (-((Multiplicative.toAdd W : ℝ≥0) : ℝ))
      rw [show (Multiplicative.toAdd (V * W) : ℝ≥0) =
        (Multiplicative.toAdd V : ℝ≥0) + (Multiplicative.toAdd W : ℝ≥0) from rfl]
      push_cast
      rw [← Real.exp_add]
      ring_nf

/-- The free generators of the model, represented by pure translations. -/
def freeGenHom (h : Fin n → E) : FreeMonoid (Fin n) →* AffineMonoid ℝ E :=
  FreeMonoid.lift fun j => ⟨h j, 1⟩

/-- The affine realization of the free source monoid. -/
def freeAffine (h : Fin n → E) : FreeSourceMonoid n →* AffineMonoid ℝ E :=
  Monoid.Coprod.lift (freeTimeHom E) (freeGenHom h)

/-- The time ray inside the free source monoid. -/
def freeRay (V : ℝ≥0) : FreeSourceMonoid n := Monoid.Coprod.inl (Multiplicative.ofAdd V)

/-- The `j`-th free generator. -/
def freeGen (j : Fin n) : FreeSourceMonoid n := Monoid.Coprod.inr (FreeMonoid.of j)

@[simp] theorem freeAffine_ray_scal (h : Fin n → E) (V : ℝ≥0) :
    (freeAffine h (freeRay V)).scal = Real.exp (-(V : ℝ)) := by
  rw [freeAffine, freeRay, Monoid.Coprod.lift_apply_inl]
  rfl

@[simp] theorem freeAffine_ray_vec (h : Fin n → E) (V : ℝ≥0) :
    (freeAffine h (freeRay V)).vec = 0 := by
  rw [freeAffine, freeRay, Monoid.Coprod.lift_apply_inl]
  rfl

@[simp] theorem freeAffine_gen_vec (h : Fin n → E) (j : Fin n) :
    (freeAffine h (freeGen j)).vec = h j := by
  rw [freeAffine, freeGen, Monoid.Coprod.lift_apply_inr, freeGenHom, FreeMonoid.lift_eval_of]

@[simp] theorem freeAffine_gen_scal (h : Fin n → E) (j : Fin n) :
    (freeAffine h (freeGen j)).scal = 1 := by
  rw [freeAffine, freeGen, Monoid.Coprod.lift_apply_inr, freeGenHom, FreeMonoid.lift_eval_of]

theorem coe_smul_id (c : ℝ) :
    ⇑(c • (LinearMap.id : E →ₗ[ℝ] E)) = fun x : E => c • x := by
  funext x
  simp

/-- The terminal datum of the free-source model. -/
def freeDatum (h : Fin n → E) : TerminalDatum ℝ (FreeSourceMonoid n) E where
  π m := (freeAffine h m).scal • LinearMap.id
  π_one := by simp
  π_mul g g' := by
    ext x
    simp [mul_smul]
  π_continuous g := by
    rw [coe_smul_id]
    exact continuous_const_smul _
  r := freeRay
  r_add V W := by
    show Monoid.Coprod.inl (Multiplicative.ofAdd (V + W)) =
      Monoid.Coprod.inl (Multiplicative.ofAdd V) * Monoid.Coprod.inl (Multiplicative.ofAdd W)
    rw [← map_mul]
    rfl
  stableSpace := ⊤
  tendsto_stable x _ := by
    have hexp : Tendsto (fun V : ℝ≥0 => Real.exp (-(V : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
    have hsmul := hexp.smul_const x
    rw [zero_smul] at hsmul
    refine hsmul.congr fun V => ?_
    simp

/-- The cochain of the free-source model. -/
def freeCochain (h : Fin n → E) : FreeSourceMonoid n → E := fun m => (freeAffine h m).vec

theorem freeCochain_isCocycle (h : Fin n → E) : (freeDatum h).IsCocycle (freeCochain h) := by
  intro g g'
  simp [freeCochain, freeDatum, map_mul]

@[simp] theorem freeCochain_ray (h : Fin n → E) (V : ℝ≥0) :
    freeCochain h ((freeDatum h).r V) = 0 := by
  simp [freeCochain, freeDatum]

theorem freeCochain_tendsto (h : Fin n → E) :
    Tendsto (fun V => freeCochain h ((freeDatum h).r V)) atTop (𝓝 (0 : E)) := by
  simp only [freeCochain_ray]
  exact tendsto_const_nhds

/-- **Free-source universality.**  The terminal residue takes arbitrary prescribed values on the
free generators, so residues carry no information before source relations are imposed. -/
theorem freeCochain_residue_gen (h : Fin n → E) (j : Fin n) :
    (freeDatum h).residue (freeCochain h) (-(0 : E)) (freeGen j) = h j := by
  simp [TerminalDatum.residue, TerminalDatum.coboundary, freeCochain, freeDatum]

end FreeSource

/-! ## The curved nonvacuity model -/

section Curved

/-- The parity monoid of the model. -/
abbrev ParityTime := Multiplicative ℝ≥0 × Multiplicative (ZMod 2)

private theorem parity_key (a b : ZMod 2) :
    (if a + b = 0 then (1 : ℂ) else -1) =
      (if a = 0 then (1 : ℂ) else -1) * (if b = 0 then (1 : ℂ) else -1) := by
  have hall : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl <;>
    simp [show ((1 : ZMod 2) + 1 = 0) from by decide,
      show ((1 : ZMod 2) ≠ 0) from by decide]

/-- The sign character of the central involution. -/
def paritySign (ε : Multiplicative (ZMod 2)) : ℂ :=
  if Multiplicative.toAdd ε = 0 then 1 else -1

@[simp] theorem paritySign_one : paritySign 1 = 1 := by
  show (if (0 : ZMod 2) = 0 then (1 : ℂ) else -1) = 1
  rw [if_pos rfl]

@[simp] theorem paritySign_ofAdd_one : paritySign (Multiplicative.ofAdd (1 : ZMod 2)) = -1 := by
  show (if (1 : ZMod 2) = 0 then (1 : ℂ) else -1) = -1
  rw [if_neg (by decide)]

theorem paritySign_mul (ε δ : Multiplicative (ZMod 2)) :
    paritySign (ε * δ) = paritySign ε * paritySign δ := by
  show (if Multiplicative.toAdd (ε * δ) = 0 then (1 : ℂ) else -1) = _
  rw [show (Multiplicative.toAdd (ε * δ) : ZMod 2) =
    (Multiplicative.toAdd ε : ZMod 2) + (Multiplicative.toAdd δ : ZMod 2) from rfl]
  exact parity_key _ _

/-- The scalar by which the parity model acts. -/
def parityScalar (m : ParityTime) : ℂ :=
  ((Real.exp (-((Multiplicative.toAdd m.1 : ℝ≥0) : ℝ)) : ℝ) : ℂ) * paritySign m.2

@[simp] theorem parityScalar_one : parityScalar 1 = 1 := by
  show ((Real.exp (-((0 : ℝ≥0) : ℝ)) : ℝ) : ℂ) * paritySign 1 = 1
  rw [paritySign_one]
  norm_num

theorem parityScalar_mul (m m' : ParityTime) :
    parityScalar (m * m') = parityScalar m * parityScalar m' := by
  have hadd : ((Multiplicative.toAdd (m * m').1 : ℝ≥0) : ℝ) =
      ((Multiplicative.toAdd m.1 : ℝ≥0) : ℝ) + ((Multiplicative.toAdd m'.1 : ℝ≥0) : ℝ) := by
    rw [show (Multiplicative.toAdd (m * m').1 : ℝ≥0) =
      (Multiplicative.toAdd m.1 : ℝ≥0) + (Multiplicative.toAdd m'.1 : ℝ≥0) from rfl]
    push_cast
    ring
  show ((Real.exp (-((Multiplicative.toAdd (m * m').1 : ℝ≥0) : ℝ)) : ℝ) : ℂ) *
      paritySign (m * m').2 = _
  rw [show ((m * m').2 : Multiplicative (ZMod 2)) = m.2 * m'.2 from rfl, paritySign_mul, hadd,
    neg_add, Real.exp_add, Complex.ofReal_mul, parityScalar, parityScalar]
  ring

theorem coe_smul_id_complex (c : ℂ) :
    ⇑(c • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) = fun x : ℂ => c • x := by
  funext x
  simp

theorem tendsto_ofReal_exp_neg :
    Tendsto (fun V : ℝ≥0 => ((Real.exp (-(V : ℝ)) : ℝ) : ℂ)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun V : ℝ≥0 => Real.exp (-(V : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hcx := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hexp
  rw [Complex.ofReal_zero] at hcx
  exact hcx

/-- The terminal datum of the curved nonvacuity model. -/
def parityDatum : TerminalDatum ℂ ParityTime ℂ where
  π m := parityScalar m • LinearMap.id
  π_one := by simp
  π_mul g h := by
    refine LinearMap.ext fun x => ?_
    simp [parityScalar_mul, mul_smul]
  π_continuous g := by
    rw [coe_smul_id_complex]
    exact continuous_const_smul _
  r V := (Multiplicative.ofAdd V, 1)
  r_add V W := by
    refine Prod.ext rfl ?_
    simp
  stableSpace := ⊤
  tendsto_stable x _ := by
    have hsmul := tendsto_ofReal_exp_neg.smul_const x
    rw [zero_smul] at hsmul
    refine hsmul.congr fun V => ?_
    rw [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    congr 1
    show ((Real.exp (-(V : ℝ)) : ℝ) : ℂ) =
      ((Real.exp (-((V : ℝ≥0) : ℝ)) : ℝ) : ℂ) * paritySign 1
    rw [paritySign_one, mul_one]

@[simp] theorem parityDatum_π_apply (m : ParityTime) (x : ℂ) :
    parityDatum.π m x = parityScalar m * x := rfl

@[simp] theorem parityDatum_r (V : ℝ≥0) :
    parityDatum.r V = (Multiplicative.ofAdd V, (1 : Multiplicative (ZMod 2))) := rfl

@[simp] theorem parityScalar_ray (V : ℝ≥0) :
    parityScalar (parityDatum.r V) = ((Real.exp (-(V : ℝ)) : ℝ) : ℂ) := by
  show ((Real.exp (-((V : ℝ≥0) : ℝ)) : ℝ) : ℂ) * paritySign 1 = _
  rw [paritySign_one, mul_one]

/-- The central involution. -/
def parityInvolution : ParityTime := (1, Multiplicative.ofAdd (1 : ZMod 2))

@[simp] theorem parityScalar_involution : parityScalar parityInvolution = -1 := by
  show ((Real.exp (-((0 : ℝ≥0) : ℝ)) : ℝ) : ℂ) *
    paritySign (Multiplicative.ofAdd (1 : ZMod 2)) = -1
  rw [paritySign_ofAdd_one]
  norm_num

/-- The curved cochain: it vanishes on the odd sheet. -/
def parityCochain (m : ParityTime) : ℂ :=
  if Multiplicative.toAdd m.2 = 0 then
    ((Real.exp (-((Multiplicative.toAdd m.1 : ℝ≥0) : ℝ)) : ℝ) : ℂ) - 1 else 0

@[simp] theorem parityCochain_even (V : ℝ≥0) :
    parityCochain (Multiplicative.ofAdd V, (1 : Multiplicative (ZMod 2))) =
      ((Real.exp (-(V : ℝ)) : ℝ) : ℂ) - 1 := by
  show (if (0 : ZMod 2) = 0 then ((Real.exp (-((V : ℝ≥0) : ℝ)) : ℝ) : ℂ) - 1 else 0) = _
  rw [if_pos rfl]

@[simp] theorem parityCochain_odd (V : ℝ≥0) :
    parityCochain (Multiplicative.ofAdd V, Multiplicative.ofAdd (1 : ZMod 2)) = 0 := by
  show (if (1 : ZMod 2) = 0 then ((Real.exp (-((V : ℝ≥0) : ℝ)) : ℝ) : ℂ) - 1 else 0) = 0
  rw [if_neg (by decide)]

@[simp] theorem parityCochain_ray (V : ℝ≥0) :
    parityCochain (parityDatum.r V) = ((Real.exp (-(V : ℝ)) : ℝ) : ℂ) - 1 := by
  rw [parityDatum_r, parityCochain_even]

@[simp] theorem parityCochain_involution : parityCochain parityInvolution = 0 := by
  show parityCochain (Multiplicative.ofAdd (0 : ℝ≥0), Multiplicative.ofAdd (1 : ZMod 2)) = 0
  exact parityCochain_odd 0

theorem parityCochain_tendsto :
    Tendsto (fun V => parityCochain (parityDatum.r V)) atTop (𝓝 (-1 : ℂ)) := by
  have hsub := tendsto_ofReal_exp_neg.sub_const (1 : ℂ)
  rw [zero_sub] at hsub
  exact hsub.congr fun V => (parityCochain_ray V).symm

theorem parityDatum_ray_mul_involution (V : ℝ≥0) :
    parityDatum.r V * parityInvolution =
      (Multiplicative.ofAdd V, Multiplicative.ofAdd (1 : ZMod 2)) := by
  refine Prod.ext ?_ ?_
  · show Multiplicative.ofAdd V * (1 : Multiplicative ℝ≥0) = Multiplicative.ofAdd V
    rw [mul_one]
  · show (1 : Multiplicative (ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) =
      Multiplicative.ofAdd (1 : ZMod 2)
    rw [one_mul]

/-- The ray is central, so it normalizes the involution. -/
theorem parityDatum_ray_commutes (V : ℝ≥0) :
    parityDatum.r V * parityInvolution = parityInvolution * parityDatum.r V := mul_comm _ _

theorem parityCochain_radiallyFlat : parityDatum.IsRadiallyFlat parityCochain := by
  intro V W
  have hmul : parityDatum.r V * parityDatum.r W = parityDatum.r (V + W) :=
    (parityDatum.r_add V W).symm
  have hVW : ((V + W : ℝ≥0) : ℝ) = (V : ℝ) + (W : ℝ) := by push_cast; ring
  rw [TerminalDatum.curvature, hmul, parityCochain_ray, parityCochain_ray, parityCochain_ray,
    parityDatum_π_apply, parityScalar_ray, hVW, neg_add, Real.exp_add, Complex.ofReal_mul]
  ring

/-- The stable radial primitive of the model is `η = 1`. -/
theorem parityCochain_radial_primitive (V : ℝ≥0) :
    parityCochain (parityDatum.r V) = parityDatum.coboundary (-(-1 : ℂ)) (parityDatum.r V) :=
  parityDatum.radial_coboundary parityCochain_radiallyFlat parityCochain_tendsto V

/-- **The curved residue of the model is `2`.**  Flat transgression vanishes on the central
involution, but the curved flux does not. -/
theorem parityCochain_residue_involution :
    parityDatum.residue parityCochain (-(-1 : ℂ)) parityInvolution = 2 := by
  rw [TerminalDatum.residue, TerminalDatum.coboundary, parityCochain_involution,
    parityDatum_π_apply, parityScalar_involution]
  ring

/-- The left bulk curvature face. -/
theorem parityCochain_curvature_left (V : ℝ≥0) :
    parityDatum.curvature parityCochain (parityDatum.r V) parityInvolution =
      1 - ((Real.exp (-(V : ℝ)) : ℝ) : ℂ) := by
  rw [TerminalDatum.curvature, parityDatum_ray_mul_involution, parityCochain_odd,
    parityCochain_ray, parityCochain_involution, parityDatum_π_apply]
  ring

/-- The right bulk curvature face. -/
theorem parityCochain_curvature_right (V : ℝ≥0) :
    parityDatum.curvature parityCochain parityInvolution (parityDatum.r V) =
      ((Real.exp (-(V : ℝ)) : ℝ) : ℂ) - 1 := by
  rw [TerminalDatum.curvature, ← parityDatum_ray_commutes, parityDatum_ray_mul_involution,
    parityCochain_odd, parityCochain_ray, parityCochain_involution, parityDatum_π_apply,
    parityScalar_involution]
  ring

/-- **Curved nonvacuity.**  The oriented difference of the two bulk curvature faces converges to
the residue `2`. -/
theorem parityCochain_flux :
    Tendsto (fun V => parityDatum.curvature parityCochain (parityDatum.r V) parityInvolution -
        parityDatum.curvature parityCochain parityInvolution (parityDatum.r V)) atTop (𝓝 2) := by
  have hmain := parityDatum.tendsto_curvature_flux (b := parityCochain) (fun _ => trivial)
    parityCochain_tendsto parityInvolution (φ := id) tendsto_id
    (Filter.Eventually.of_forall fun V => parityDatum_ray_commutes V)
  rwa [parityCochain_residue_involution] at hmain

/-- The model's cochain is not a cocycle: a flat cocycle would have vanishing residue at an element
normalized by the whole ray. -/
theorem parityCochain_not_isCocycle : ¬ parityDatum.IsCocycle parityCochain := by
  intro hb
  have hres := parityDatum.residue_eq_zero_of_eventually_commutes (b := parityCochain)
    (fun _ => trivial) hb parityCochain_tendsto parityInvolution (φ := id) tendsto_id
    (Filter.Eventually.of_forall fun V => parityDatum_ray_commutes V)
  rw [parityCochain_residue_involution] at hres
  norm_num at hres

end Curved

end

end GaloisForLFunctions.HTGeometry.Interfinity
