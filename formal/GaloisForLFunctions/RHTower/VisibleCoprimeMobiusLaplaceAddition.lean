import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayArithmeticPartition
import GaloisForLFunctions.RHTower.GradeMonodromyInversion

/-!
# Visible coprime Möbius--Laplace addition

The exact Lambert law for the concrete Möbius--Laplace transform is regrouped through the
positive-lattice primitive-ray equivalence.  Absolute convergence gives the common-dilation
renewal law, an explicit geometric envelope, and then a second absolutely convergent Möbius
inversion gives the nonlinear identity

`∑' (a,b)=1, Φ(a x) Φ(b y) = Φ(x+y)` for `x,y>0`.

Every interchange is backed by a `Summable` proof; no zero information or RH premise enters.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Product of two Möbius--Laplace values along one positive coprime direction. -/
def visibleCoprimeMobiusLaplaceTerm
    (x y : ℝ) (q : ThetaCuspPrimitiveDirection) : ℂ :=
  mobiusDiscreteLaplaceTransform ((q.1.1 : ℝ) * x) *
    mobiusDiscreteLaplaceTransform ((q.1.2 : ℝ) * y)

/-- Primitive visible-pair sum over all positive coprime directions. -/
def visibleCoprimeMobiusLaplaceSum (x y : ℝ) : ℂ :=
  ∑' q : ThetaCuspPrimitiveDirection,
    visibleCoprimeMobiusLaplaceTerm x y q

private theorem summable_mobiusDiscreteLaplaceTransform_pair
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Summable (fun p : ℕ+ × ℕ+ =>
      mobiusDiscreteLaplaceTransform ((p.1 : ℝ) * x) *
        mobiusDiscreteLaplaceTransform ((p.2 : ℝ) * y)) := by
  have hsx := summable_pnat_mobiusDiscreteLaplaceTransform_dilate x hx
  have hsy := summable_pnat_mobiusDiscreteLaplaceTransform_dilate y hy
  apply Summable.of_norm
  simpa only [norm_mul] using
    hsx.norm.mul_of_nonneg hsy.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-- Public row form of the absolutely summable Lambert pair family. -/
theorem mobiusDiscreteLaplaceTransform_eq_tsum_lambertRow
    (x : ℝ) (hx : 0 < x) (k : ℕ+) :
    mobiusDiscreteLaplaceTransform ((k : ℝ) * x) =
      ∑' n : ℕ+, mobiusLaplaceLambertPair x (k, n) := by
  have hkx : 0 < (k : ℝ) * x := mul_pos (by exact_mod_cast k.property) hx
  have hsum := summable_mobiusDiscreteLaplaceTerm hkx
  have hsplit := hsum.sum_add_tsum_nat_add 1
  calc
    mobiusDiscreteLaplaceTransform ((k : ℝ) * x) =
        ∑' n : ℕ, mobiusDiscreteLaplaceTerm ((k : ℝ) * x) (n + 1) := by
      rw [mobiusDiscreteLaplaceTransform]
      simpa [mobiusDiscreteLaplaceTerm] using hsplit.symm
    _ = ∑' n : ℕ+, mobiusDiscreteLaplaceTerm ((k : ℝ) * x) (n : ℕ) :=
      tsum_pnat_eq_tsum_succ.symm
    _ = ∑' n : ℕ+, mobiusLaplaceLambertPair x (k, n) := by
      apply tsum_congr
      intro n
      rw [mobiusLaplaceLambertPair, mobiusDiscreteLaplaceTerm]
      apply congrArg (fun z : ℂ =>
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * z)
      apply congrArg Complex.exp
      push_cast
      ring

/-- A finite geometric constant controlling every positive integer dilation of the
Möbius--Laplace transform. -/
def mobiusLaplaceDilationConstant (x : ℝ) : ℝ :=
  Real.exp x * ∑' n : ℕ+, Real.exp (-((n : ℝ) * x))

/-- The dilation envelope constant is nonnegative. -/
theorem mobiusLaplaceDilationConstant_nonneg (x : ℝ) :
    0 ≤ mobiusLaplaceDilationConstant x := by
  unfold mobiusLaplaceDilationConstant
  exact mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)

/-- Uniform exponential envelope for every positive integer dilation. -/
theorem norm_mobiusDiscreteLaplaceTransform_dilate_le
    (x : ℝ) (hx : 0 < x) (k : ℕ+) :
    ‖mobiusDiscreteLaplaceTransform ((k : ℝ) * x)‖ ≤
      mobiusLaplaceDilationConstant x * Real.exp (-((k : ℝ) * x)) := by
  have hgeoNat : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * x))) := by
    simpa using summable_pow_mul_exp_neg 0 hx
  have hgeo : Summable (fun n : ℕ+ => Real.exp (-((n : ℝ) * x))) :=
    hgeoNat.comp_injective PNat.coe_injective
  have hrow : Summable (fun n : ℕ+ => mobiusLaplaceLambertPair x (k, n)) :=
    (summable_mobiusLaplaceLambertPair hx).comp_injective
      (fun _ _ h => Prod.mk.inj h |>.2)
  have hmajor : Summable (fun n : ℕ+ =>
      (Real.exp x * Real.exp (-((k : ℝ) * x))) *
        Real.exp (-((n : ℝ) * x))) :=
    hgeo.mul_left _
  rw [mobiusDiscreteLaplaceTransform_eq_tsum_lambertRow x hx k]
  calc
    ‖∑' n : ℕ+, mobiusLaplaceLambertPair x (k, n)‖ ≤
        ∑' n : ℕ+, ‖mobiusLaplaceLambertPair x (k, n)‖ :=
      norm_tsum_le_tsum_norm hrow.norm
    _ ≤ ∑' n : ℕ+, (Real.exp x * Real.exp (-((k : ℝ) * x))) *
          Real.exp (-((n : ℝ) * x)) := by
      refine hrow.norm.tsum_le_tsum (fun n => ?_) hmajor
      rw [mobiusLaplaceLambertPair, norm_mul, Complex.norm_exp]
      simp only [Complex.neg_re, Complex.ofReal_re]
      have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.property
      have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.property
      have hprod : (k : ℝ) + (n : ℝ) - 1 ≤ (k : ℝ) * (n : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hn)]
      have hexp : Real.exp (-((k : ℝ) * (n : ℝ) * x)) ≤
          (Real.exp x * Real.exp (-((k : ℝ) * x))) *
            Real.exp (-((n : ℝ) * x)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ *
              Real.exp (-((k : ℝ) * (n : ℝ) * x)) ≤
            1 * Real.exp (-((k : ℝ) * (n : ℝ) * x)) :=
          mul_le_mul_of_nonneg_right hmu (Real.exp_pos _).le
        _ ≤ _ := by simpa using hexp
    _ = mobiusLaplaceDilationConstant x * Real.exp (-((k : ℝ) * x)) := by
      rw [tsum_mul_left]
      unfold mobiusLaplaceDilationConstant
      ring

/-- The primitive visible-pair family is absolutely summable at positive scales. -/
theorem summable_visibleCoprimeMobiusLaplaceTerm
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Summable (visibleCoprimeMobiusLaplaceTerm x y) := by
  have hfull := summable_mobiusDiscreteLaplaceTransform_pair x y hx hy
  exact hfull.comp_injective Subtype.val_injective

/-- Geometric constant for the primitive visible-pair dilation family. -/
def visibleCoprimeMobiusLaplaceDilationConstant (x y : ℝ) : ℝ :=
  mobiusLaplaceDilationConstant x * mobiusLaplaceDilationConstant y *
    Real.exp (x + y) *
      (∑' a : ℕ+, Real.exp (-((a : ℝ) * x))) *
      (∑' b : ℕ+, Real.exp (-((b : ℝ) * y)))

/-- The two-variable primitive dilation envelope constant is nonnegative. -/
theorem visibleCoprimeMobiusLaplaceDilationConstant_nonneg (x y : ℝ) :
    0 ≤ visibleCoprimeMobiusLaplaceDilationConstant x y := by
  unfold visibleCoprimeMobiusLaplaceDilationConstant
  have hx := mobiusLaplaceDilationConstant_nonneg x
  have hy := mobiusLaplaceDilationConstant_nonneg y
  have hsx : 0 ≤ ∑' a : ℕ+, Real.exp (-((a : ℝ) * x)) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  have hsy : 0 ≤ ∑' b : ℕ+, Real.exp (-((b : ℝ) * y)) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  positivity

private theorem norm_visibleCoprimeMobiusLaplaceTerm_dilate_le
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (d : ℕ+) (q : ThetaCuspPrimitiveDirection) :
    ‖visibleCoprimeMobiusLaplaceTerm ((d : ℝ) * x) ((d : ℝ) * y) q‖ ≤
      mobiusLaplaceDilationConstant x * mobiusLaplaceDilationConstant y *
        Real.exp (x + y) *
        Real.exp (-((q.1.1 : ℝ) * x)) *
        Real.exp (-((q.1.2 : ℝ) * y)) *
        Real.exp (-((d : ℝ) * (x + y))) := by
  have hleft := norm_mobiusDiscreteLaplaceTransform_dilate_le x hx (q.1.1 * d)
  have hright := norm_mobiusDiscreteLaplaceTransform_dilate_le y hy (q.1.2 * d)
  have hcastLeft : ((q.1.1 * d : ℕ+) : ℝ) = (q.1.1 : ℝ) * (d : ℝ) := by
    push_cast
    rfl
  have hcastRight : ((q.1.2 * d : ℕ+) : ℝ) = (q.1.2 : ℝ) * (d : ℝ) := by
    push_cast
    rfl
  have hleft' :
      ‖mobiusDiscreteLaplaceTransform ((q.1.1 : ℝ) * ((d : ℝ) * x))‖ ≤
        mobiusLaplaceDilationConstant x *
          Real.exp (-(((q.1.1 : ℝ) * (d : ℝ)) * x)) := by
    rw [hcastLeft] at hleft
    simpa only [mul_assoc] using hleft
  have hright' :
      ‖mobiusDiscreteLaplaceTransform ((q.1.2 : ℝ) * ((d : ℝ) * y))‖ ≤
        mobiusLaplaceDilationConstant y *
          Real.exp (-(((q.1.2 : ℝ) * (d : ℝ)) * y)) := by
    rw [hcastRight] at hright
    simpa only [mul_assoc] using hright
  have hq1 : (1 : ℝ) ≤ (q.1.1 : ℝ) := by exact_mod_cast q.1.1.property
  have hq2 : (1 : ℝ) ≤ (q.1.2 : ℝ) := by exact_mod_cast q.1.2.property
  have hd : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast d.property
  have hprod1 : (q.1.1 : ℝ) + (d : ℝ) - 1 ≤ (q.1.1 : ℝ) * (d : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hd)]
  have hprod2 : (q.1.2 : ℝ) + (d : ℝ) - 1 ≤ (q.1.2 : ℝ) * (d : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq2) (sub_nonneg.mpr hd)]
  have hexp1 : Real.exp (-(((q.1.1 : ℝ) * (d : ℝ)) * x)) ≤
      Real.exp x * Real.exp (-((q.1.1 : ℝ) * x)) *
        Real.exp (-((d : ℝ) * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexp2 : Real.exp (-(((q.1.2 : ℝ) * (d : ℝ)) * y)) ≤
      Real.exp y * Real.exp (-((q.1.2 : ℝ) * y)) *
        Real.exp (-((d : ℝ) * y)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [visibleCoprimeMobiusLaplaceTerm, norm_mul]
  calc
    ‖mobiusDiscreteLaplaceTransform ((q.1.1 : ℝ) * ((d : ℝ) * x))‖ *
          ‖mobiusDiscreteLaplaceTransform ((q.1.2 : ℝ) * ((d : ℝ) * y))‖ ≤
        (mobiusLaplaceDilationConstant x *
          Real.exp (-(((q.1.1 : ℝ) * (d : ℝ)) * x))) *
        (mobiusLaplaceDilationConstant y *
          Real.exp (-(((q.1.2 : ℝ) * (d : ℝ)) * y))) :=
      mul_le_mul hleft' hright' (norm_nonneg _) <|
        mul_nonneg (mobiusLaplaceDilationConstant_nonneg _)
          (Real.exp_pos _).le
    _ ≤ (mobiusLaplaceDilationConstant x *
          (Real.exp x * Real.exp (-((q.1.1 : ℝ) * x)) * Real.exp (-((d : ℝ) * x)))) *
        (mobiusLaplaceDilationConstant y *
          (Real.exp y * Real.exp (-((q.1.2 : ℝ) * y)) * Real.exp (-((d : ℝ) * y)))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hexp1
          (mobiusLaplaceDilationConstant_nonneg _)
      · exact mul_le_mul_of_nonneg_left hexp2
          (mobiusLaplaceDilationConstant_nonneg _)
      · exact mul_nonneg (mobiusLaplaceDilationConstant_nonneg _) (Real.exp_pos _).le
      · exact mul_nonneg (mobiusLaplaceDilationConstant_nonneg _)
          (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
            (Real.exp_pos _).le)
    _ = _ := by
      rw [show Real.exp (x + y) = Real.exp x * Real.exp y by rw [Real.exp_add]]
      rw [show Real.exp (-((d : ℝ) * (x + y))) =
          Real.exp (-((d : ℝ) * x)) * Real.exp (-((d : ℝ) * y)) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring

/-- Common dilations of the full visible sum have an explicit exponential envelope. -/
theorem norm_visibleCoprimeMobiusLaplaceSum_dilate_le
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (d : ℕ+) :
    ‖visibleCoprimeMobiusLaplaceSum ((d : ℝ) * x) ((d : ℝ) * y)‖ ≤
      visibleCoprimeMobiusLaplaceDilationConstant x y *
        Real.exp (-((d : ℝ) * (x + y))) := by
  have hgeoXNat : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * x))) := by
    simpa using summable_pow_mul_exp_neg 0 hx
  have hgeoYNat : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * y))) := by
    simpa using summable_pow_mul_exp_neg 0 hy
  have hgeoX : Summable (fun a : ℕ+ => Real.exp (-((a : ℝ) * x))) :=
    hgeoXNat.comp_injective PNat.coe_injective
  have hgeoY : Summable (fun b : ℕ+ => Real.exp (-((b : ℝ) * y))) :=
    hgeoYNat.comp_injective PNat.coe_injective
  let A : ℝ := mobiusLaplaceDilationConstant x * mobiusLaplaceDilationConstant y *
    Real.exp (x + y) * Real.exp (-((d : ℝ) * (x + y)))
  let g : ℕ+ × ℕ+ → ℝ := fun p =>
    A * (Real.exp (-((p.1 : ℝ) * x)) * Real.exp (-((p.2 : ℝ) * y)))
  have hbase : Summable (fun p : ℕ+ × ℕ+ =>
      Real.exp (-((p.1 : ℝ) * x)) * Real.exp (-((p.2 : ℝ) * y))) :=
    hgeoX.mul_of_nonneg hgeoY (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mobiusLaplaceDilationConstant_nonneg _)
          (mobiusLaplaceDilationConstant_nonneg _))
        (Real.exp_pos _).le)
      (Real.exp_pos _).le
  have hg : Summable g := hbase.mul_left A
  have hterm := summable_visibleCoprimeMobiusLaplaceTerm
    ((d : ℝ) * x) ((d : ℝ) * y)
    (mul_pos (by exact_mod_cast d.property) hx)
    (mul_pos (by exact_mod_cast d.property) hy)
  rw [visibleCoprimeMobiusLaplaceSum]
  calc
    ‖∑' q : ThetaCuspPrimitiveDirection,
        visibleCoprimeMobiusLaplaceTerm ((d : ℝ) * x) ((d : ℝ) * y) q‖ ≤
        ∑' q : ThetaCuspPrimitiveDirection,
          ‖visibleCoprimeMobiusLaplaceTerm ((d : ℝ) * x) ((d : ℝ) * y) q‖ :=
      norm_tsum_le_tsum_norm hterm.norm
    _ ≤ ∑' p : ℕ+ × ℕ+, g p := by
      refine hterm.norm.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun p _ => ?_) (fun q => ?_) hg
      · exact mul_nonneg hA <| mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      · have h := norm_visibleCoprimeMobiusLaplaceTerm_dilate_le x y hx hy d q
        apply h.trans_eq
        dsimp [g, A]
        ring
    _ = A * ((∑' a : ℕ+, Real.exp (-((a : ℝ) * x))) *
          (∑' b : ℕ+, Real.exp (-((b : ℝ) * y)))) := by
      rw [show (∑' p : ℕ+ × ℕ+, g p) = A * ∑' p : ℕ+ × ℕ+,
          Real.exp (-((p.1 : ℝ) * x)) * Real.exp (-((p.2 : ℝ) * y)) by
        exact tsum_mul_left]
      congr 1
      exact (hgeoX.tsum_mul_tsum hgeoY hbase).symm
    _ = visibleCoprimeMobiusLaplaceDilationConstant x y *
          Real.exp (-((d : ℝ) * (x + y))) := by
      unfold A visibleCoprimeMobiusLaplaceDilationConstant
      ring

/-- Common dilations of the full visible sum form an absolutely summable family. -/
theorem summable_visibleCoprimeMobiusLaplaceSum_dilate
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Summable (fun d : ℕ+ =>
      visibleCoprimeMobiusLaplaceSum ((d : ℝ) * x) ((d : ℝ) * y)) := by
  have hxy : 0 < x + y := add_pos hx hy
  have hgeoNat : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * (x + y)))) := by
    simpa using summable_pow_mul_exp_neg 0 hxy
  have hgeo : Summable (fun d : ℕ+ => Real.exp (-((d : ℝ) * (x + y)))) :=
    hgeoNat.comp_injective PNat.coe_injective
  have hmajor : Summable (fun d : ℕ+ =>
      visibleCoprimeMobiusLaplaceDilationConstant x y *
        Real.exp (-((d : ℝ) * (x + y)))) :=
    hgeo.mul_left _
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun d => norm_visibleCoprimeMobiusLaplaceSum_dilate_le x y hx hy d) hmajor

/-- Exact common-dilation renewal law `(V3)` in two variables. -/
theorem tsum_visibleCoprimeMobiusLaplaceSum_dilate
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∑' d : ℕ+, visibleCoprimeMobiusLaplaceSum ((d : ℝ) * x) ((d : ℝ) * y)) =
      Complex.exp (-(x + y)) := by
  let f : ℕ+ × ℕ+ → ℂ := fun p =>
    mobiusDiscreteLaplaceTransform ((p.1 : ℝ) * x) *
      mobiusDiscreteLaplaceTransform ((p.2 : ℝ) * y)
  have hsum : Summable f :=
    summable_mobiusDiscreteLaplaceTransform_pair x y hx hy
  have hprimitive : Summable (fun q : ThetaCuspPrimitiveRayIndex =>
      f (thetaCuspPrimitiveRayIndexToPositivePair q)) :=
    (Equiv.summable_iff thetaCuspPrimitiveRayIndexEquivPositivePair).2 hsum
  let e : (ℕ+ × ThetaCuspPrimitiveDirection) ≃ ThetaCuspPrimitiveRayIndex :=
    (Equiv.prodComm ThetaCuspPrimitiveDirection ℕ+).symm
  have hswap : Summable (fun q : ℕ+ × ThetaCuspPrimitiveDirection =>
      f (thetaCuspPrimitiveRayIndexToPositivePair (e q))) :=
    (Equiv.summable_iff e).2 hprimitive
  calc
    (∑' d : ℕ+, visibleCoprimeMobiusLaplaceSum ((d : ℝ) * x) ((d : ℝ) * y)) =
        ∑' d : ℕ+, ∑' q : ThetaCuspPrimitiveDirection,
          f (thetaCuspPrimitiveRayIndexToPositivePair (q, d)) := by
      apply tsum_congr
      intro d
      rw [visibleCoprimeMobiusLaplaceSum]
      apply tsum_congr
      intro q
      rw [visibleCoprimeMobiusLaplaceTerm]
      simp only [f, thetaCuspPrimitiveRayIndexToPositivePair]
      congr 2 <;> push_cast <;> ring
    _ = ∑' q : ℕ+ × ThetaCuspPrimitiveDirection,
          f (thetaCuspPrimitiveRayIndexToPositivePair (e q)) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro d
      apply tsum_congr
      intro q
      rfl
    _ = ∑' q : ThetaCuspPrimitiveRayIndex,
          f (thetaCuspPrimitiveRayIndexToPositivePair q) := by
      exact Equiv.tsum_eq e
        (fun q : ThetaCuspPrimitiveRayIndex =>
          f (thetaCuspPrimitiveRayIndexToPositivePair q))
    _ = ∑' p : ℕ+ × ℕ+, f p := by
      exact (tsum_thetaCuspPositivePair_eq_primitiveRay f).symm
    _ = (∑' a : ℕ+, mobiusDiscreteLaplaceTransform ((a : ℝ) * x)) *
          (∑' b : ℕ+, mobiusDiscreteLaplaceTransform ((b : ℝ) * y)) := by
      exact (summable_pnat_mobiusDiscreteLaplaceTransform_dilate x hx).tsum_mul_tsum
        (summable_pnat_mobiusDiscreteLaplaceTransform_dilate y hy) hsum |>.symm
    _ = Complex.exp (-x) * Complex.exp (-y) := by
      rw [tsum_pnat_mobiusDiscreteLaplaceTransform_dilate x hx,
        tsum_pnat_mobiusDiscreteLaplaceTransform_dilate y hy]
    _ = Complex.exp (-(x + y)) := by
      rw [← Complex.exp_add]
      congr 1
      ring

private theorem summable_moebius_visibleCoprimeMobiusLaplaceSum_pair
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Summable (fun c : ℕ+ × ℕ+ =>
      (ArithmeticFunction.moebius (c.1 : ℕ) : ℂ) *
        visibleCoprimeMobiusLaplaceSum
          (((c.1 * c.2 : ℕ+) : ℝ) * x)
          (((c.1 * c.2 : ℕ+) : ℝ) * y)) := by
  have hxy : 0 < x + y := add_pos hx hy
  have hgeoNat : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * (x + y)))) := by
    simpa using summable_pow_mul_exp_neg 0 hxy
  have hgeo : Summable (fun n : ℕ+ => Real.exp (-((n : ℝ) * (x + y)))) :=
    hgeoNat.comp_injective PNat.coe_injective
  let C : ℝ := visibleCoprimeMobiusLaplaceDilationConstant x y * Real.exp (x + y)
  let g : ℕ+ × ℕ+ → ℝ := fun c =>
    C * (Real.exp (-((c.1 : ℝ) * (x + y))) *
      Real.exp (-((c.2 : ℝ) * (x + y))))
  have hbase : Summable (fun c : ℕ+ × ℕ+ =>
      Real.exp (-((c.1 : ℝ) * (x + y))) *
        Real.exp (-((c.2 : ℝ) * (x + y)))) :=
    hgeo.mul_of_nonneg hgeo (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
  have hg : Summable g := hbase.mul_left C
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => ?_) hg
  rw [norm_mul]
  have hmu : ‖(ArithmeticFunction.moebius (c.1 : ℕ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := c.1)
  let d : ℕ+ := c.1 * c.2
  have hsum := norm_visibleCoprimeMobiusLaplaceSum_dilate_le x y hx hy d
  have hsum' :
      ‖visibleCoprimeMobiusLaplaceSum
          (((c.1 * c.2 : ℕ+) : ℝ) * x)
          (((c.1 * c.2 : ℕ+) : ℝ) * y)‖ ≤
        visibleCoprimeMobiusLaplaceDilationConstant x y *
          Real.exp (-(((c.1 * c.2 : ℕ+) : ℝ) * (x + y))) := by
    simpa only [d] using hsum
  have hc1 : (1 : ℝ) ≤ (c.1 : ℝ) := by exact_mod_cast c.1.property
  have hc2 : (1 : ℝ) ≤ (c.2 : ℝ) := by exact_mod_cast c.2.property
  have hprod : (c.1 : ℝ) + (c.2 : ℝ) - 1 ≤ (c.1 : ℝ) * (c.2 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hc2)]
  have hexp : Real.exp (-(((c.1 * c.2 : ℕ+) : ℝ) * (x + y))) ≤
      Real.exp (x + y) * Real.exp (-((c.1 : ℝ) * (x + y))) *
        Real.exp (-((c.2 : ℝ) * (x + y))) := by
    push_cast
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    ‖(ArithmeticFunction.moebius (c.1 : ℕ) : ℂ)‖ *
        ‖visibleCoprimeMobiusLaplaceSum
          (((c.1 * c.2 : ℕ+) : ℝ) * x)
          (((c.1 * c.2 : ℕ+) : ℝ) * y)‖ ≤
      1 * (visibleCoprimeMobiusLaplaceDilationConstant x y *
        Real.exp (-(((c.1 * c.2 : ℕ+) : ℝ) * (x + y)))) :=
      mul_le_mul hmu hsum' (norm_nonneg _) zero_le_one
    _ ≤ visibleCoprimeMobiusLaplaceDilationConstant x y *
        (Real.exp (x + y) * Real.exp (-((c.1 : ℝ) * (x + y))) *
          Real.exp (-((c.2 : ℝ) * (x + y)))) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_left hexp
        (visibleCoprimeMobiusLaplaceDilationConstant_nonneg _ _)
    _ = g c := by
      dsimp [g, C]
      ring

/-- Exact two-variable visible-addition law `(V5)`. -/
theorem visibleCoprimeMobiusLaplaceSum_eq_add
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    visibleCoprimeMobiusLaplaceSum x y =
      mobiusDiscreteLaplaceTransform (x + y) := by
  let F : ℕ → ℂ := fun n =>
    visibleCoprimeMobiusLaplaceSum ((n : ℝ) * x) ((n : ℝ) * y)
  have hpair : Summable (fun c : ℕ+ × ℕ+ =>
      (ArithmeticFunction.moebius (c.1 : ℕ) : ℂ) *
        F ((c.1 : ℕ) * (c.2 : ℕ))) := by
    apply (summable_moebius_visibleCoprimeMobiusLaplaceSum_pair x y hx hy).congr
    intro c
    dsimp [F]
  have hcollapse :
      (∑' c : ℕ+ × ℕ+,
        (ArithmeticFunction.moebius (c.1 : ℕ) : ℂ) *
          F ((c.1 : ℕ) * (c.2 : ℕ))) = F 1 :=
    tsum_moebius_pair hpair
  have hrows : ∀ n : ℕ+,
      (∑' m : ℕ+, F ((n : ℕ) * (m : ℕ))) =
        Complex.exp (-((n : ℝ) * (x + y))) := by
    intro n
    have hnx : 0 < (n : ℝ) * x := mul_pos (by exact_mod_cast n.property) hx
    have hny : 0 < (n : ℝ) * y := mul_pos (by exact_mod_cast n.property) hy
    have h := tsum_visibleCoprimeMobiusLaplaceSum_dilate
      ((n : ℝ) * x) ((n : ℝ) * y) hnx hny
    calc
      (∑' m : ℕ+, F ((n : ℕ) * (m : ℕ))) =
          ∑' m : ℕ+, visibleCoprimeMobiusLaplaceSum
            ((m : ℝ) * ((n : ℝ) * x)) ((m : ℝ) * ((n : ℝ) * y)) := by
        apply tsum_congr
        intro m
        dsimp [F]
        apply congrArg₂ visibleCoprimeMobiusLaplaceSum
        · push_cast
          ring
        · push_cast
          ring
      _ = Complex.exp (-((↑((n : ℝ) * x) : ℂ) + ↑((n : ℝ) * y))) := h
      _ = Complex.exp (-((n : ℝ) * (x + y))) := by
        congr 1
        push_cast
        ring
  have hseries :
      (∑' c : ℕ+ × ℕ+,
        (ArithmeticFunction.moebius (c.1 : ℕ) : ℂ) *
          F ((c.1 : ℕ) * (c.2 : ℕ))) =
        ∑' n : ℕ+, (ArithmeticFunction.moebius (n : ℕ) : ℂ) *
          Complex.exp (-((n : ℝ) * (x + y))) := by
    rw [hpair.tsum_prod]
    apply tsum_congr
    intro n
    change (∑' m : ℕ+, (ArithmeticFunction.moebius (n : ℕ) : ℂ) *
      F ((n : ℕ) * (m : ℕ))) =
        (ArithmeticFunction.moebius (n : ℕ) : ℂ) *
          Complex.exp (-((n : ℝ) * (x + y)))
    rw [tsum_mul_left, hrows n]
  have hphi :
      (∑' n : ℕ+, (ArithmeticFunction.moebius (n : ℕ) : ℂ) *
          Complex.exp (-((n : ℝ) * (x + y)))) =
        mobiusDiscreteLaplaceTransform (x + y) := by
    have hrow := mobiusDiscreteLaplaceTransform_eq_tsum_lambertRow
      (x + y) (add_pos hx hy) 1
    rw [show ((1 : ℕ+) : ℝ) * (x + y) = x + y by norm_num] at hrow
    calc
      (∑' n : ℕ+, (ArithmeticFunction.moebius (n : ℕ) : ℂ) *
          Complex.exp (-((n : ℝ) * (x + y)))) =
          ∑' n : ℕ+, mobiusLaplaceLambertPair (x + y) (1, n) := by
        apply tsum_congr
        intro n
        rw [mobiusLaplaceLambertPair]
        norm_num
      _ = mobiusDiscreteLaplaceTransform (x + y) := hrow.symm
  have hF : F 1 = visibleCoprimeMobiusLaplaceSum x y := by
    dsimp [F]
    norm_num
  rw [hseries, hphi] at hcollapse
  exact hF.symm.trans hcollapse.symm

end

end RHTower
