/-
# The exact Sonin principal-relative ideal

The Calkin model forgets two concrete error sources: the exact Sonin projection correction and
finite time-band blocks coupling the physical and Fourier polarizations.  This module retains
those sources in one algebraic two-sided ideal on the actual even carrier.  It then replays the
quadratic-corner reduction without passing to arbitrary compact operators.
-/
import GaloisForLFunctions.RHTower.CCM.CCMSoninFiniteWordNormalForm
import GaloisForLFunctions.RHTower.SoninEulerFiniteGramLower
import GaloisForLFunctions.RHTower.SoninTimeBandSchatten
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

noncomputable section


namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- Exact correction between the even Sonin projection and its formal physical/Fourier
complement. -/
def evenSoninProjectionCorrection (a : ℝ) :
    evenSubspace →L[Complex] evenSubspace :=
  evenCentralSoninProjection a -
    (1 - evenIndicatorCutoff a - evenFourierCutoff a)

/-- Algebraic two-sided ideal retaining every error source used in the Sonin principal-shell
reduction: exact projection corrections and finite physical/Fourier time-band blocks. -/
inductive IsSoninPrincipalRelativeIdeal :
    (evenSubspace →L[Complex] evenSubspace) → Prop
  | zero : IsSoninPrincipalRelativeIdeal 0
  | projectionCorrection (a : ℝ) (ha : 0 < a) :
      IsSoninPrincipalRelativeIdeal (evenSoninProjectionCorrection a)
  | indicatorFourier (s t : ℝ) (hs : 0 < s) :
      IsSoninPrincipalRelativeIdeal
        (evenIndicatorCutoff s * evenFourierCutoff t)
  | fourierIndicator (s t : ℝ) (hs : 0 < s) :
      IsSoninPrincipalRelativeIdeal
        (evenFourierCutoff s * evenIndicatorCutoff t)
  | add {S T : evenSubspace →L[Complex] evenSubspace}
      (hS : IsSoninPrincipalRelativeIdeal S)
      (hT : IsSoninPrincipalRelativeIdeal T) :
      IsSoninPrincipalRelativeIdeal (S + T)
  | neg {T : evenSubspace →L[Complex] evenSubspace}
      (hT : IsSoninPrincipalRelativeIdeal T) :
      IsSoninPrincipalRelativeIdeal (-T)
  | leftMul (L : evenSubspace →L[Complex] evenSubspace)
      {T : evenSubspace →L[Complex] evenSubspace}
      (hT : IsSoninPrincipalRelativeIdeal T) :
      IsSoninPrincipalRelativeIdeal (L * T)
  | rightMul {T : evenSubspace →L[Complex] evenSubspace}
      (hT : IsSoninPrincipalRelativeIdeal T)
      (R : evenSubspace →L[Complex] evenSubspace) :
      IsSoninPrincipalRelativeIdeal (T * R)

namespace IsSoninPrincipalRelativeIdeal

theorem sub {S T : evenSubspace →L[Complex] evenSubspace}
    (hS : IsSoninPrincipalRelativeIdeal S)
    (hT : IsSoninPrincipalRelativeIdeal T) :
    IsSoninPrincipalRelativeIdeal (S - T) := by
  rw [sub_eq_add_neg]
  exact hS.add hT.neg

theorem of_eq {S T : evenSubspace →L[Complex] evenSubspace}
    (hS : IsSoninPrincipalRelativeIdeal S) (h : S = T) :
    IsSoninPrincipalRelativeIdeal T := by
  rwa [← h]

theorem smul (c : Complex) {T : evenSubspace →L[Complex] evenSubspace}
    (hT : IsSoninPrincipalRelativeIdeal T) :
    IsSoninPrincipalRelativeIdeal (c • T) := by
  have h := hT.leftMul (c • (1 : evenSubspace →L[Complex] evenSubspace))
  apply h.of_eq
  apply ContinuousLinearMap.ext
  intro x
  simp

theorem isCompactOperator {T : evenSubspace →L[Complex] evenSubspace}
    (hT : IsSoninPrincipalRelativeIdeal T) : IsCompactOperator T := by
  induction hT with
  | zero => exact isCompactOperator_zero
  | projectionCorrection a ha =>
      exact evenCentralSoninProjection_compactEq_complement a ha
  | indicatorFourier s t hs =>
      exact isCompactOperator_evenIndicatorFourierBlock s t hs
  | fourierIndicator s t hs =>
      exact isCompactOperator_evenFourierIndicatorBlock s t hs
  | add hS hT ihS ihT => exact ihS.add ihT
  | neg hT ihT => exact ihT.neg
  | leftMul L hT ihT => exact ihT.clm_comp L
  | rightMul hT R ihT => exact ihT.comp_clm R

/-- The exact even projection correction is Schatten-1, by invariant-subspace descent from the
ambient Sonin time-band ideal. -/
theorem projectionCorrection_memSchattenClass_one (a : ℝ) (ha : 0 < a) :
    MemSchattenClass 1 (evenSoninProjectionCorrection a) := by
  let T : SoninL2 →L[Complex] SoninL2 := centralSoninProjectionCorrection a
  have hT : MemSchattenClass 1 T := by
    simpa [T] using centralSoninProjectionCorrection_memSchattenClass_one a ha
  have hmap : Set.MapsTo T evenSubspace evenSubspace := by
    intro f hf
    change centralSoninProjection a f -
      (f - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f -
        fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f) ∈ evenSubspace
    exact evenSubspace.sub_mem
      (centralSoninProjection_mapsTo_evenSubspace a hf)
      (evenSubspace.sub_mem
        (evenSubspace.sub_mem hf (indicatorCutoff_central_mapsTo_evenSubspace a hf))
        (fourierCutoff_central_mapsTo_evenSubspace a hf))
  have hr := memSchattenClass_one_restrict evenSubspace T hmap hT
  have heq : T.restrict hmap = evenSoninProjectionCorrection a := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    rfl
  rwa [heq] at hr

/-- Every physical-then-Fourier block on the even carrier is Schatten-1. -/
theorem indicatorFourier_memSchattenClass_one
    (s t : ℝ) (hs : 0 < s) :
    MemSchattenClass 1 (evenIndicatorCutoff s * evenFourierCutoff t) := by
  let T : SoninL2 →L[Complex] SoninL2 :=
    indicatorCutoff (centralInterval s) (measurableSet_centralInterval s) *
      fourierCutoff (centralInterval t) (measurableSet_centralInterval t)
  have hT : MemSchattenClass 1 T := by
    simpa [T] using
      memSchattenClass_one_indicatorCutoff_fourierCutoff_central s t hs
  have hmap : Set.MapsTo T evenSubspace evenSubspace := by
    intro f hf
    exact indicatorCutoff_central_mapsTo_evenSubspace s
      (fourierCutoff_central_mapsTo_evenSubspace t hf)
  have hr := memSchattenClass_one_restrict evenSubspace T hmap hT
  have heq : T.restrict hmap = evenIndicatorCutoff s * evenFourierCutoff t := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    rfl
  rwa [heq] at hr

/-- Every Fourier-then-physical block on the even carrier is Schatten-1. -/
theorem fourierIndicator_memSchattenClass_one
    (s t : ℝ) (hs : 0 < s) :
    MemSchattenClass 1 (evenFourierCutoff s * evenIndicatorCutoff t) := by
  let T : SoninL2 →L[Complex] SoninL2 :=
    fourierCutoff (centralInterval s) (measurableSet_centralInterval s) *
      indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
  have hT : MemSchattenClass 1 T := by
    simpa [T] using
      memSchattenClass_one_fourierCutoff_indicatorCutoff_central s t hs
  have hmap : Set.MapsTo T evenSubspace evenSubspace := by
    intro f hf
    exact fourierCutoff_central_mapsTo_evenSubspace s
      (indicatorCutoff_central_mapsTo_evenSubspace t hf)
  have hr := memSchattenClass_one_restrict evenSubspace T hmap hT
  have heq : T.restrict hmap = evenFourierCutoff s * evenIndicatorCutoff t := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    rfl
  rwa [heq] at hr

/-- Every exact principal-relative correction is Schatten-1.  This closes all constructors of
the algebraic ideal, rather than merely its named generators. -/
theorem memSchattenClass_one {T : evenSubspace →L[Complex] evenSubspace}
    (hT : IsSoninPrincipalRelativeIdeal T) : MemSchattenClass 1 T := by
  induction hT with
  | zero => simp [MemSchattenClass, approxNumber_zero_op]
  | projectionCorrection a ha => exact projectionCorrection_memSchattenClass_one a ha
  | indicatorFourier s t hs => exact indicatorFourier_memSchattenClass_one s t hs
  | fourierIndicator s t hs => exact fourierIndicator_memSchattenClass_one s t hs
  | add hS hT ihS ihT =>
      exact memSchattenClass_one_add
        hS.isCompactOperator hT.isCompactOperator ihS ihT
  | neg hT ihT => simpa using memSchattenClass_one_smul ihT (-1)
  | leftMul L hT ihT => exact memSchattenClass_one_comp_left ihT L
  | rightMul hT R ihT => exact memSchattenClass_one_comp_right ihT R

/-- The ordinary operator trace is genuinely defined on every principal-relative correction:
its canonical diagonal converges absolutely. -/
theorem summable_inner_diag {T : evenSubspace →L[Complex] evenSubspace}
    (hT : IsSoninPrincipalRelativeIdeal T) :
    Summable (fun i => inner ℂ (ContinuousLinearMap.hsBasis ℂ evenSubspace i)
      (T (ContinuousLinearMap.hsBasis ℂ evenSubspace i))) :=
  hT.memSchattenClass_one.one_summable_inner_diag

/-- The ordinary trace of a principal-relative correction is controlled by its trace norm. -/
theorem norm_opTrace_le_traceNorm {T : evenSubspace →L[Complex] evenSubspace}
    (hT : IsSoninPrincipalRelativeIdeal T) :
    ‖ContinuousLinearMap.opTrace T‖ ≤ traceNorm evenSubspace T :=
  RHTower.norm_opTrace_le_traceNorm hT.memSchattenClass_one

end IsSoninPrincipalRelativeIdeal

/-- Congruence modulo the exact Sonin principal-relative ideal. -/
def SoninPrincipalRelativeEq
    (S T : evenSubspace →L[Complex] evenSubspace) : Prop :=
  IsSoninPrincipalRelativeIdeal (S - T)

infix:50 " =ᵣ " => SoninPrincipalRelativeEq

namespace SoninPrincipalRelativeEq

theorem refl (T : evenSubspace →L[Complex] evenSubspace) : T =ᵣ T := by
  rw [SoninPrincipalRelativeEq, sub_self]
  exact IsSoninPrincipalRelativeIdeal.zero

theorem of_eq {S T : evenSubspace →L[Complex] evenSubspace} (h : S = T) : S =ᵣ T := by
  rw [h]
  exact refl T

theorem symm {S T : evenSubspace →L[Complex] evenSubspace} (h : S =ᵣ T) : T =ᵣ S := by
  apply h.neg.of_eq
  simp only [neg_sub]

theorem trans {S T U : evenSubspace →L[Complex] evenSubspace}
    (hST : S =ᵣ T) (hTU : T =ᵣ U) : S =ᵣ U := by
  unfold SoninPrincipalRelativeEq at hST hTU ⊢
  apply IsSoninPrincipalRelativeIdeal.of_eq
    (IsSoninPrincipalRelativeIdeal.add hST hTU)
  abel

theorem add {S T U V : evenSubspace →L[Complex] evenSubspace}
    (hST : S =ᵣ T) (hUV : U =ᵣ V) : S + U =ᵣ T + V := by
  unfold SoninPrincipalRelativeEq at hST hUV ⊢
  apply IsSoninPrincipalRelativeIdeal.of_eq
    (IsSoninPrincipalRelativeIdeal.add hST hUV)
  abel

theorem smul (c : Complex) {S T : evenSubspace →L[Complex] evenSubspace}
    (hST : S =ᵣ T) : c • S =ᵣ c • T := by
  unfold SoninPrincipalRelativeEq at hST ⊢
  apply (hST.smul c).of_eq
  rw [smul_sub]

theorem sum {ι : Type*} (s : Finset ι)
    (S T : ι → evenSubspace →L[Complex] evenSubspace)
    (h : ∀ i ∈ s, S i =ᵣ T i) :
    (∑ i ∈ s, S i) =ᵣ ∑ i ∈ s, T i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact refl 0
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem left_mul (L : evenSubspace →L[Complex] evenSubspace)
    {S T : evenSubspace →L[Complex] evenSubspace} (hST : S =ᵣ T) :
    L * S =ᵣ L * T := by
  unfold SoninPrincipalRelativeEq at hST ⊢
  apply IsSoninPrincipalRelativeIdeal.of_eq (hST.leftMul L)
  rw [mul_sub]

theorem right_mul {S T : evenSubspace →L[Complex] evenSubspace}
    (hST : S =ᵣ T) (R : evenSubspace →L[Complex] evenSubspace) :
    S * R =ᵣ T * R := by
  unfold SoninPrincipalRelativeEq at hST ⊢
  apply IsSoninPrincipalRelativeIdeal.of_eq (hST.rightMul R)
  rw [sub_mul]

theorem mul {S T U V : evenSubspace →L[Complex] evenSubspace}
    (hST : S =ᵣ T) (hUV : U =ᵣ V) : S * U =ᵣ T * V := by
  have h₁ := hST.right_mul U
  have h₂ := hUV.left_mul T
  exact h₁.trans h₂

theorem eq_zero {T : evenSubspace →L[Complex] evenSubspace}
    (hT : IsSoninPrincipalRelativeIdeal T) : T =ᵣ 0 := by
  simpa [SoninPrincipalRelativeEq] using hT

/-- Removing one relative-ideal corner from both sides of a sandwich changes the sandwich only
by the same ideal. -/
theorem sub_sandwich
    (E K X : evenSubspace →L[Complex] evenSubspace)
    (hKX : IsSoninPrincipalRelativeIdeal (K * X))
    (hXK : IsSoninPrincipalRelativeIdeal (X * K)) :
    (E - K) * X * (E - K) =ᵣ E * X * E := by
  have hleft : (E - K) * X =ᵣ E * X := by
    unfold SoninPrincipalRelativeEq
    apply hKX.neg.of_eq
    rw [sub_mul]
    abel
  have hright : (E * X) * (E - K) =ᵣ (E * X) * E := by
    unfold SoninPrincipalRelativeEq
    apply (hXK.leftMul E).neg.of_eq
    rw [mul_sub]
    abel
  exact (hleft.right_mul (E - K)).trans hright

end SoninPrincipalRelativeEq

/-- Finite physical/Fourier window blocks belong to the retained relative ideal, with no
positivity needed on Fourier endpoints. -/
theorem evenIndicatorDiff_mul_evenFourierDiff_mem_principalRelativeIdeal
    (b c d e : ℝ) (hb : 0 < b) (hc : 0 < c) :
    IsSoninPrincipalRelativeIdeal
      ((evenIndicatorCutoff b - evenIndicatorCutoff c) *
        (evenFourierCutoff d - evenFourierCutoff e)) := by
  have hbd := IsSoninPrincipalRelativeIdeal.indicatorFourier b d hb
  have hbe := IsSoninPrincipalRelativeIdeal.indicatorFourier b e hb
  have hcd := IsSoninPrincipalRelativeIdeal.indicatorFourier c d hc
  have hce := IsSoninPrincipalRelativeIdeal.indicatorFourier c e hc
  apply (hbd.sub hbe |>.sub hcd |>.add hce).of_eq
  rw [sub_mul, mul_sub, mul_sub]
  abel

/-- Fourier/physical counterpart of the finite window-block certificate. -/
theorem evenFourierDiff_mul_evenIndicatorDiff_mem_principalRelativeIdeal
    (b c d e : ℝ) (hb : 0 < b) (hc : 0 < c) :
    IsSoninPrincipalRelativeIdeal
      ((evenFourierCutoff b - evenFourierCutoff c) *
        (evenIndicatorCutoff d - evenIndicatorCutoff e)) := by
  have hbd := IsSoninPrincipalRelativeIdeal.fourierIndicator b d hb
  have hbe := IsSoninPrincipalRelativeIdeal.fourierIndicator b e hb
  have hcd := IsSoninPrincipalRelativeIdeal.fourierIndicator c d hc
  have hce := IsSoninPrincipalRelativeIdeal.fourierIndicator c e hc
  apply (hbd.sub hbe |>.sub hcd |>.add hce).of_eq
  rw [sub_mul, mul_sub, mul_sub]
  abel

/-- Every physical-window/Fourier-window cross product stays in the concrete relative ideal. -/
theorem physicalWindow_mul_fourierWindow_mem_principalRelativeIdeal
    (a b c d e x y : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    IsSoninPrincipalRelativeIdeal
      (((evenIndicatorCutoff b - evenIndicatorCutoff c) * evenDilationCLM x hx *
          (1 - evenIndicatorCutoff a) *
        ((evenFourierCutoff d - evenFourierCutoff e) * evenDilationCLM y hy *
          (1 - evenFourierCutoff a)) : evenSubspace →L[Complex] evenSubspace)) := by
  let A := evenIndicatorCutoff a
  let R := evenFourierCutoff a
  let AB := evenIndicatorCutoff b - evenIndicatorCutoff c
  let RD := evenFourierCutoff (x * d) - evenFourierCutoff (x * e)
  let Ax := evenIndicatorCutoff (x⁻¹ * a)
  let Ux := evenDilationCLM x hx
  let Uy := evenDilationCLM y hy
  have hmoveA : Ux * (1 - A) = (1 - Ax) * Ux := by
    have h := evenDilationCLM_mul_evenIndicatorCutoff a x hx
    change Ux * A = Ax * Ux at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hmoveR : Ux * (evenFourierCutoff d - evenFourierCutoff e) = RD * Ux := by
    have hd' := evenDilationCLM_mul_evenFourierCutoff d x hx
    have he' := evenDilationCLM_mul_evenFourierCutoff e x hx
    change Ux * evenFourierCutoff d = evenFourierCutoff (x * d) * Ux at hd'
    change Ux * evenFourierCutoff e = evenFourierCutoff (x * e) * Ux at he'
    rw [mul_sub, hd', he', ← sub_mul]
  have hdirect : IsSoninPrincipalRelativeIdeal (AB * RD) := by
    exact evenIndicatorDiff_mul_evenFourierDiff_mem_principalRelativeIdeal
      b c (x * d) (x * e) hb hc
  have hAx : IsSoninPrincipalRelativeIdeal (Ax * RD) := by
    have h₁ := IsSoninPrincipalRelativeIdeal.indicatorFourier
      (x⁻¹ * a) (x * d) (mul_pos (inv_pos.mpr hx) ha)
    have h₂ := IsSoninPrincipalRelativeIdeal.indicatorFourier
      (x⁻¹ * a) (x * e) (mul_pos (inv_pos.mpr hx) ha)
    apply (h₁.sub h₂).of_eq
    dsimp only [Ax, RD]
    rw [mul_sub]
  have hbracket : IsSoninPrincipalRelativeIdeal
      ((AB * (1 - Ax) * RD : evenSubspace →L[Complex] evenSubspace)) := by
    have h := hdirect.sub (hAx.leftMul AB)
    apply h.of_eq
    calc
      AB * RD - AB * (Ax * RD) = AB * RD - (AB * Ax) * RD := by
        rw [mul_assoc]
      _ = (AB - AB * Ax) * RD := (sub_mul AB (AB * Ax) RD).symm
      _ = (AB * 1 - AB * Ax) * RD := by rw [mul_one]
      _ = AB * (1 - Ax) * RD := by
        congr 1
        exact (mul_sub AB 1 Ax).symm
  have heq :
      AB * Ux * (1 - A) * ((evenFourierCutoff d - evenFourierCutoff e) * Uy * (1 - R)) =
        (AB * (1 - Ax) * RD) * (Ux * Uy * (1 - R)) := by
    calc
      AB * Ux * (1 - A) * ((evenFourierCutoff d - evenFourierCutoff e) * Uy * (1 - R)) =
          AB * (Ux * (1 - A)) * (evenFourierCutoff d - evenFourierCutoff e) *
            Uy * (1 - R) := by simp only [mul_assoc]
      _ = AB * ((1 - Ax) * Ux) * (evenFourierCutoff d - evenFourierCutoff e) *
            Uy * (1 - R) := by rw [hmoveA]
      _ = AB * (1 - Ax) * (Ux * (evenFourierCutoff d - evenFourierCutoff e)) *
            Uy * (1 - R) := by simp only [mul_assoc]
      _ = AB * (1 - Ax) * (RD * Ux) * Uy * (1 - R) := by rw [hmoveR]
      _ = (AB * (1 - Ax) * RD) * (Ux * Uy * (1 - R)) := by simp only [mul_assoc]
  change IsSoninPrincipalRelativeIdeal
    ((AB * Ux * (1 - A) * ((evenFourierCutoff d - evenFourierCutoff e) *
      Uy * (1 - R)) : evenSubspace →L[Complex] evenSubspace))
  rw [heq]
  exact hbracket.rightMul (Ux * Uy * (1 - R))

/-- Every Fourier-window/physical-window cross product stays in the concrete relative ideal. -/
theorem fourierWindow_mul_physicalWindow_mem_principalRelativeIdeal
    (a b c d e x y : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    IsSoninPrincipalRelativeIdeal
      (((evenFourierCutoff b - evenFourierCutoff c) * evenDilationCLM x hx *
          (1 - evenFourierCutoff a) *
        ((evenIndicatorCutoff d - evenIndicatorCutoff e) * evenDilationCLM y hy *
          (1 - evenIndicatorCutoff a)) : evenSubspace →L[Complex] evenSubspace)) := by
  let A := evenIndicatorCutoff a
  let R := evenFourierCutoff a
  let RB := evenFourierCutoff b - evenFourierCutoff c
  let AD := evenIndicatorCutoff (x⁻¹ * d) - evenIndicatorCutoff (x⁻¹ * e)
  let Rx := evenFourierCutoff (x * a)
  let Ux := evenDilationCLM x hx
  let Uy := evenDilationCLM y hy
  have hmoveR : Ux * (1 - R) = (1 - Rx) * Ux := by
    have h := evenDilationCLM_mul_evenFourierCutoff a x hx
    change Ux * R = Rx * Ux at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hmoveA : Ux * (evenIndicatorCutoff d - evenIndicatorCutoff e) = AD * Ux := by
    have hd' := evenDilationCLM_mul_evenIndicatorCutoff d x hx
    have he' := evenDilationCLM_mul_evenIndicatorCutoff e x hx
    change Ux * evenIndicatorCutoff d = evenIndicatorCutoff (x⁻¹ * d) * Ux at hd'
    change Ux * evenIndicatorCutoff e = evenIndicatorCutoff (x⁻¹ * e) * Ux at he'
    rw [mul_sub, hd', he', ← sub_mul]
  have hdirect : IsSoninPrincipalRelativeIdeal (RB * AD) := by
    exact evenFourierDiff_mul_evenIndicatorDiff_mem_principalRelativeIdeal
      b c (x⁻¹ * d) (x⁻¹ * e) hb hc
  have hRx : IsSoninPrincipalRelativeIdeal (Rx * AD) := by
    have h₁ := IsSoninPrincipalRelativeIdeal.fourierIndicator
      (x * a) (x⁻¹ * d) (mul_pos hx ha)
    have h₂ := IsSoninPrincipalRelativeIdeal.fourierIndicator
      (x * a) (x⁻¹ * e) (mul_pos hx ha)
    apply (h₁.sub h₂).of_eq
    dsimp only [Rx, AD]
    rw [mul_sub]
  have hbracket : IsSoninPrincipalRelativeIdeal
      ((RB * (1 - Rx) * AD : evenSubspace →L[Complex] evenSubspace)) := by
    have h := hdirect.sub (hRx.leftMul RB)
    apply h.of_eq
    calc
      RB * AD - RB * (Rx * AD) = RB * AD - (RB * Rx) * AD := by
        rw [mul_assoc]
      _ = (RB - RB * Rx) * AD := (sub_mul RB (RB * Rx) AD).symm
      _ = (RB * 1 - RB * Rx) * AD := by rw [mul_one]
      _ = RB * (1 - Rx) * AD := by
        congr 1
        exact (mul_sub RB 1 Rx).symm
  have heq :
      RB * Ux * (1 - R) * ((evenIndicatorCutoff d - evenIndicatorCutoff e) * Uy * (1 - A)) =
        (RB * (1 - Rx) * AD) * (Ux * Uy * (1 - A)) := by
    calc
      RB * Ux * (1 - R) * ((evenIndicatorCutoff d - evenIndicatorCutoff e) * Uy * (1 - A)) =
          RB * (Ux * (1 - R)) * (evenIndicatorCutoff d - evenIndicatorCutoff e) *
            Uy * (1 - A) := by simp only [mul_assoc]
      _ = RB * ((1 - Rx) * Ux) * (evenIndicatorCutoff d - evenIndicatorCutoff e) *
            Uy * (1 - A) := by rw [hmoveR]
      _ = RB * (1 - Rx) * (Ux * (evenIndicatorCutoff d - evenIndicatorCutoff e)) *
            Uy * (1 - A) := by simp only [mul_assoc]
      _ = RB * (1 - Rx) * (AD * Ux) * Uy * (1 - A) := by rw [hmoveA]
      _ = (RB * (1 - Rx) * AD) * (Ux * Uy * (1 - A)) := by simp only [mul_assoc]
  change IsSoninPrincipalRelativeIdeal
    ((RB * Ux * (1 - R) * ((evenIndicatorCutoff d - evenIndicatorCutoff e) *
      Uy * (1 - A)) : evenSubspace →L[Complex] evenSubspace))
  rw [heq]
  exact hbracket.rightMul (Ux * Uy * (1 - A))

/-- **Principal algebra closure.**  General two-polarization Sonin windows are closed under
multiplication modulo the same concrete relative ideal used for exact Gram-corner descent. -/
theorem evenSoninWindowTranslation_mul_principalRelativeEq
    (a C₁ F₁ x C₂ F₂ y : ℝ)
    (ha : 0 < a) (haF₁ : a ≤ F₁) (haF₂ : a ≤ F₂)
    (hF₁C₁ : F₁ ≤ C₁) (hF₂C₂ : F₂ ≤ C₂)
    (hx : 0 < x) (hy : 0 < y) :
    evenSoninWindowTranslation a C₁ F₁ x hx *
        evenSoninWindowTranslation a C₂ F₂ y hy =ᵣ
      evenSoninWindowTranslation a
        (soninWindowComposeCeiling C₁ x C₂)
        (soninWindowComposeFloor C₁ F₁ x C₂ F₂)
        (x * y) (mul_pos hx hy) := by
  have hC₁ : 0 < C₁ := lt_of_lt_of_le ha (haF₁.trans hF₁C₁)
  have hF₁ : 0 < F₁ := lt_of_lt_of_le ha haF₁
  have hPP := SoninPrincipalRelativeEq.of_eq
    (evenPhysicalWindowTranslation_mul a C₁ F₁ x C₂ F₂ y
      haF₂ hF₁C₁ hF₂C₂ hx hy)
  have hFF := SoninPrincipalRelativeEq.of_eq
    (evenFourierWindowTranslation_mul a C₁ F₁ x C₂ F₂ y
      haF₂ hF₁C₁ hF₂C₂ hx hy)
  have hPF : evenPhysicalWindowTranslation a C₁ F₁ x hx *
      evenFourierWindowTranslation a C₂ F₂ y hy =ᵣ 0 :=
    SoninPrincipalRelativeEq.eq_zero (by
      simpa only [evenPhysicalWindowTranslation, evenFourierWindowTranslation] using
        physicalWindow_mul_fourierWindow_mem_principalRelativeIdeal
          a C₁ F₁ C₂ F₂ x y⁻¹ ha hC₁ hF₁ hx (inv_pos.mpr hy))
  have hFP : evenFourierWindowTranslation a C₁ F₁ x hx *
      evenPhysicalWindowTranslation a C₂ F₂ y hy =ᵣ 0 :=
    SoninPrincipalRelativeEq.eq_zero (by
      simpa only [evenPhysicalWindowTranslation, evenFourierWindowTranslation] using
        fourierWindow_mul_physicalWindow_mem_principalRelativeIdeal
          a C₁ F₁ C₂ F₂ x⁻¹ y ha hC₁ hF₁ (inv_pos.mpr hx) hy)
  have hsum := SoninPrincipalRelativeEq.add
    (SoninPrincipalRelativeEq.add hPP hPF)
    (SoninPrincipalRelativeEq.add hFP hFF)
  dsimp only [evenSoninWindowTranslation]
  simpa only [mul_add, add_mul, add_zero, zero_add, add_assoc,
    add_left_comm, add_comm] using hsum

/-- The physical branch of the exact Sonin mixed corner differs from its principal shell
translation by the retained relative ideal, not merely by an unspecified compact operator. -/
theorem physicalMixedBranch_principalRelativeEq_shellTranslation
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninProjection a *
        (evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) *
          evenIndicatorCutoff a * evenDilationCLM q (zero_lt_one.trans hq)) *
        evenCentralSoninProjection a =ᵣ
      evenPhysicalMixedShellTranslation a p q hp hq := by
  let Q := evenCentralSoninProjection a
  let A := evenIndicatorCutoff a
  let R := evenFourierCutoff a
  let Upi := evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))
  let Uq := evenDilationCLM q (zero_lt_one.trans hq)
  let X := Upi * A * Uq
  let Eₐ := 1 - A
  let E := Eₐ - R
  have hQ : Q =ᵣ E := by
    apply IsSoninPrincipalRelativeIdeal.projectionCorrection a ha |>.of_eq
    dsimp [evenSoninProjectionCorrection, Q, E, Eₐ, A, R]
  have hRX : IsSoninPrincipalRelativeIdeal (R * X) := by
    have hmove := evenFourierCutoff_mul_evenDilationCLM
      a p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))
    have hscale : (p⁻¹)⁻¹ * a = p * a := by rw [inv_inv]
    rw [hscale] at hmove
    have hb := IsSoninPrincipalRelativeIdeal.fourierIndicator
      (p * a) a (mul_pos (zero_lt_one.trans hp) ha)
    have hc := (hb.rightMul Uq).leftMul Upi
    apply hc.of_eq
    change Upi * (evenFourierCutoff (p * a) * A) * Uq = R * X
    calc
      Upi * (evenFourierCutoff (p * a) * A) * Uq =
          (Upi * evenFourierCutoff (p * a)) * A * Uq := by noncomm_ring
      _ = (R * Upi) * A * Uq := by rw [hmove]
      _ = R * X := by noncomm_ring
  have hXR : IsSoninPrincipalRelativeIdeal (X * R) := by
    have hmove := evenFourierCutoff_mul_evenDilationCLM
      (q * a) q (zero_lt_one.trans hq)
    have hscale : q⁻¹ * (q * a) = a := inv_mul_cancel_left₀ (zero_lt_one.trans hq).ne' a
    rw [hscale] at hmove
    have hb := IsSoninPrincipalRelativeIdeal.indicatorFourier a (q * a) ha
    have hc := (hb.rightMul Uq).leftMul Upi
    apply hc.of_eq
    change Upi * (A * evenFourierCutoff (q * a)) * Uq = X * R
    calc
      Upi * (A * evenFourierCutoff (q * a)) * Uq =
          Upi * A * (evenFourierCutoff (q * a) * Uq) := by noncomm_ring
      _ = Upi * A * (Uq * R) := by rw [hmove.symm]
      _ = X * R := by noncomm_ring
  have houter : Q * X * Q =ᵣ E * X * E :=
    (hQ.mul (SoninPrincipalRelativeEq.refl X)).mul hQ
  have hremove : E * X * E =ᵣ Eₐ * X * Eₐ := by
    exact SoninPrincipalRelativeEq.sub_sandwich Eₐ R X hRX hXR
  refine houter.trans (hremove.trans (SoninPrincipalRelativeEq.of_eq ?_))
  dsimp [Eₐ, X, Upi, Uq, A, evenPhysicalMixedShellTranslation]
  exact physicalMixedBranch_eq_shellTranslation a p q ha hp hq

/-- Fourier counterpart of the exact mixed-corner principal-relative reduction. -/
theorem fourierMixedBranch_principalRelativeEq_shellTranslation
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninProjection a *
        (evenDilationCLM p (zero_lt_one.trans hp) * evenFourierCutoff a *
          evenDilationCLM q⁻¹ (inv_pos.mpr (zero_lt_one.trans hq))) *
        evenCentralSoninProjection a =ᵣ
      evenFourierMixedShellTranslation a p q hp hq := by
  let Q := evenCentralSoninProjection a
  let A := evenIndicatorCutoff a
  let R := evenFourierCutoff a
  let Up := evenDilationCLM p (zero_lt_one.trans hp)
  let Uqi := evenDilationCLM q⁻¹ (inv_pos.mpr (zero_lt_one.trans hq))
  let X := Up * R * Uqi
  let Eᵣ := 1 - R
  let E := Eᵣ - A
  have hQ : Q =ᵣ E := by
    apply IsSoninPrincipalRelativeIdeal.projectionCorrection a ha |>.of_eq
    dsimp [evenSoninProjectionCorrection, Q, E, Eᵣ, A, R]
    abel
  have hAX : IsSoninPrincipalRelativeIdeal (A * X) := by
    have hmove := evenIndicatorCutoff_mul_evenDilationCLM
      a p (zero_lt_one.trans hp)
    have hb := IsSoninPrincipalRelativeIdeal.indicatorFourier
      (p * a) a (mul_pos (zero_lt_one.trans hp) ha)
    have hc := (hb.rightMul Uqi).leftMul Up
    apply hc.of_eq
    change Up * (evenIndicatorCutoff (p * a) * R) * Uqi = A * X
    calc
      Up * (evenIndicatorCutoff (p * a) * R) * Uqi =
          (Up * evenIndicatorCutoff (p * a)) * R * Uqi := by noncomm_ring
      _ = (A * Up) * R * Uqi := by rw [hmove]
      _ = A * X := by noncomm_ring
  have hXA : IsSoninPrincipalRelativeIdeal (X * A) := by
    have hmove := evenIndicatorCutoff_mul_evenDilationCLM
      (q * a) q⁻¹ (inv_pos.mpr (zero_lt_one.trans hq))
    have hscale : q⁻¹ * (q * a) = a := inv_mul_cancel_left₀ (zero_lt_one.trans hq).ne' a
    rw [hscale] at hmove
    have hb := IsSoninPrincipalRelativeIdeal.fourierIndicator a (q * a) ha
    have hc := (hb.rightMul Uqi).leftMul Up
    apply hc.of_eq
    change Up * (R * evenIndicatorCutoff (q * a)) * Uqi = X * A
    calc
      Up * (R * evenIndicatorCutoff (q * a)) * Uqi =
          Up * R * (evenIndicatorCutoff (q * a) * Uqi) := by noncomm_ring
      _ = Up * R * (Uqi * A) := by rw [hmove.symm]
      _ = X * A := by noncomm_ring
  have houter : Q * X * Q =ᵣ E * X * E :=
    (hQ.mul (SoninPrincipalRelativeEq.refl X)).mul hQ
  have hremove : E * X * E =ᵣ Eᵣ * X * Eᵣ := by
    exact SoninPrincipalRelativeEq.sub_sandwich Eᵣ A X hAX hXA
  refine houter.trans (hremove.trans (SoninPrincipalRelativeEq.of_eq ?_))
  dsimp [Eᵣ, X, Up, Uqi, R, evenFourierMixedShellTranslation]
  exact fourierMixedBranch_eq_shellTranslation a p q ha hp hq

/-- Exact mixed Calkin model reduced to its two principal shell branches modulo the retained
relative ideal. -/
theorem evenSoninMixedModel_principalRelativeEq_shellTranslation
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenSoninMixedCalkinModel a p q hp hq =ᵣ
      evenSoninMixedShellTranslation a p q hp hq := by
  have hpbranch :=
    physicalMixedBranch_principalRelativeEq_shellTranslation a p q ha hp hq
  have hfbranch :=
    fourierMixedBranch_principalRelativeEq_shellTranslation a p q ha hp hq
  have hsum := hpbranch.add hfbranch
  dsimp [evenSoninMixedCalkinModel, evenSoninMixedShellTranslation]
  simpa only [mul_add, add_mul, mul_assoc] using hsum

/-- The exact quadratic Sonin Gram corner differs from the mixed model only through the exact
projection correction. -/
theorem evenCentralSoninQuadraticCorner_principalRelativeEq_mixedModel
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninQuadraticCorner a p q hp hq =ᵣ
      evenSoninMixedCalkinModel a p q hp hq := by
  let Q := evenCentralSoninProjection a
  let A := evenIndicatorCutoff a
  let R := evenFourierCutoff a
  let Dp := evenDilationSum p hp
  let Dq := evenDilationSum q hq
  have hQ : Q =ᵣ 1 - A - R := by
    unfold SoninPrincipalRelativeEq
    simpa [evenSoninProjectionCorrection, Q, A, R] using
      (IsSoninPrincipalRelativeIdeal.projectionCorrection a ha)
  have hE : 1 - Q =ᵣ A + R := by
    unfold SoninPrincipalRelativeEq at hQ ⊢
    apply hQ.neg.of_eq
    abel
  have hreplace : Q * Dp * (1 - Q) * Dq * Q =ᵣ
      Q * Dp * (A + R) * Dq * Q := by
    have h := hE.left_mul (Q * Dp)
    have h' := h.right_mul (Dq * Q)
    simpa only [mul_assoc] using h'
  rw [evenCentralSoninQuadraticCorner_eq_mul]
  refine hreplace.trans (SoninPrincipalRelativeEq.of_eq ?_)
  dsimp [evenSoninMixedCalkinModel, Q, A, R, Dp, Dq]
  rw [evenDilationSum_eq, evenDilationSum_eq]
  have h₁ := evenSoninProjection_mul_dilation_mul_indicatorCutoff a p ha hp
  have h₂ := evenSoninProjection_mul_inverseDilation_mul_fourierCutoff a p ha hp
  have h₃ := evenIndicatorCutoff_mul_inverseDilation_mul_soninProjection a q ha hq
  have h₄ := evenFourierCutoff_mul_dilation_mul_soninProjection a q ha hq
  noncomm_ring [h₁, h₂, h₃, h₄]

/-- **Principal-relative Sonin reduction.**  The exact quadratic Gram corner has the canonical
two-polarization shell translation as its principal representative; their difference retains a
concrete derivation from projection corrections and finite time-band blocks. -/
theorem evenCentralSoninQuadraticCorner_principalRelativeEq_shellTranslation
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninQuadraticCorner a p q hp hq =ᵣ
      evenSoninMixedShellTranslation a p q hp hq :=
  (evenCentralSoninQuadraticCorner_principalRelativeEq_mixedModel a p q ha hp hq).trans
    (evenSoninMixedModel_principalRelativeEq_shellTranslation a p q ha hp hq)

/-- Finite matrix combination of actual prime-scale quadratic Sonin Gram corners. -/
def finitePrimeSoninQuadraticCornerCombination
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (A : Matrix (Fin n) (Fin n) ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ i, ∑ j, A i j •
    evenCentralSoninQuadraticCorner a (p i : ℝ) (p j : ℝ)
      (by exact_mod_cast (hp i).one_lt) (by exact_mod_cast (hp j).one_lt)

/-- Matching finite combination of canonical two-polarization shell representatives. -/
def finitePrimeSoninPrincipalShellCombination
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (A : Matrix (Fin n) (Fin n) ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ i, ∑ j, A i j •
    evenSoninMixedShellTranslation a (p i : ℝ) (p j : ℝ)
      (by exact_mod_cast (hp i).one_lt) (by exact_mod_cast (hp j).one_lt)

/-- Finite prime Gram matrices descend coefficientwise to their principal shell representatives
inside the exact relative ideal. -/
theorem finitePrimeSoninQuadraticCorner_principalRelativeEq_shellCombination
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finitePrimeSoninQuadraticCornerCombination a p hp A =ᵣ
      finitePrimeSoninPrincipalShellCombination a p hp A := by
  classical
  unfold finitePrimeSoninQuadraticCornerCombination
    finitePrimeSoninPrincipalShellCombination
  apply SoninPrincipalRelativeEq.sum Finset.univ
  intro i hi
  apply SoninPrincipalRelativeEq.sum Finset.univ
  intro j hj
  apply SoninPrincipalRelativeEq.smul
  exact evenCentralSoninQuadraticCorner_principalRelativeEq_shellTranslation
    a (p i : ℝ) (p j : ℝ) ha
      (by exact_mod_cast (hp i).one_lt) (by exact_mod_cast (hp j).one_lt)

/-- The actual prime Gram combination used here is definitionally the corpus's finite Gram
combination. -/
theorem finitePrimeSoninQuadraticCornerCombination_eq_finiteEvenDilationGramCombination
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finitePrimeSoninQuadraticCornerCombination a p hp A =
      finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (fun i => by
          exact_mod_cast (show 1 < p i from (hp i).one_lt)) A := by
  classical
  unfold finitePrimeSoninQuadraticCornerCombination
    finiteEvenDilationGramCombination evenCentralSoninQuadraticCorner
  rfl

/-- **Principal/residual uniqueness for finite prime systems.**  A nonzero finite matrix
combination of canonical Sonin principal shells cannot lie in the concrete relative ideal.
Thus the principal part of every finite prime Gram combination is unique before any trace is
defined. -/
theorem finitePrimeSoninPrincipalShellCombination_not_mem_relativeIdeal_of_ne_zero
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ≠ 0) :
    ¬ IsSoninPrincipalRelativeIdeal
      (finitePrimeSoninPrincipalShellCombination a p hp A) := by
  intro hshell
  have hdescent :=
    finitePrimeSoninQuadraticCorner_principalRelativeEq_shellCombination
      a ha p hp A
  unfold SoninPrincipalRelativeEq at hdescent
  have hactual : IsSoninPrincipalRelativeIdeal
      (finitePrimeSoninQuadraticCornerCombination a p hp A) := by
    apply hdescent.add hshell |>.of_eq
    abel
  have hcompact := hactual.isCompactOperator
  have hnot := finitePrimeEvenDilationGram_not_isCompactOperator_of_ne_zero
    a ha p hp hinj A hA
  apply hnot
  rw [← finitePrimeSoninQuadraticCornerCombination_eq_finiteEvenDilationGramCombination
    a p hp A]
  exact hcompact

end RHTower
