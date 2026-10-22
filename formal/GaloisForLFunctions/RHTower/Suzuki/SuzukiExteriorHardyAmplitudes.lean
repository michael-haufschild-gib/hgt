import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The two-port Hardy amplitudes of an exterior source

An exterior two-port source is an `L²` function vanishing on the aperture `(-a, a)`.  It splits
into its two half-line pieces, which are again `L²`, and translating each piece to the origin
produces the two Hardy amplitudes: by Plancherel they have exactly the `L²` norms of the pieces,
and by the translation formula the transform of the source is the sum of the two amplitudes
carrying the opposite boundary phases `e^{± i a ξ}`.
-/

open Set MeasureTheory Filter Topology
open scoped FourierTransform RealInnerProductSpace

namespace RHTower

noncomputable section

/-- The left exterior port of a source, supported in `(-∞, -a]`. -/
def suzukiExteriorLeft (a : ℝ) (b : ℝ → ℂ) : ℝ → ℂ := Set.indicator (Iic (-a)) b

/-- The right exterior port of a source, supported in `[a, ∞)`. -/
def suzukiExteriorRight (a : ℝ) (b : ℝ → ℂ) : ℝ → ℂ := Set.indicator (Ici a) b

theorem suzukiExteriorLeft_eq_zero_of_lt {a : ℝ} {b : ℝ → ℂ} {x : ℝ} (hx : -a < x) :
    suzukiExteriorLeft a b x = 0 :=
  Set.indicator_of_notMem (by simp [not_le.mpr hx]) _

theorem suzukiExteriorRight_eq_zero_of_lt {a : ℝ} {b : ℝ → ℂ} {x : ℝ} (hx : x < a) :
    suzukiExteriorRight a b x = 0 :=
  Set.indicator_of_notMem (by simp [not_le.mpr hx]) _

/-- **`(9)`: an exterior source is the sum of its two ports.** -/
theorem suzukiExterior_add_eq {a : ℝ} (ha : 0 < a) {b : ℝ → ℂ}
    (hsupp : ∀ x ∈ Ioo (-a) a, b x = 0) (x : ℝ) :
    suzukiExteriorLeft a b x + suzukiExteriorRight a b x = b x := by
  rcases le_or_gt x (-a) with hle | hgt
  · have h1 : suzukiExteriorLeft a b x = b x :=
      Set.indicator_of_mem (show x ∈ Iic (-a) from hle) b
    have h2 : suzukiExteriorRight a b x = 0 :=
      suzukiExteriorRight_eq_zero_of_lt (by linarith)
    rw [h1, h2, add_zero]
  · rcases lt_or_ge x a with hlt | hge
    · have h1 : suzukiExteriorLeft a b x = 0 := suzukiExteriorLeft_eq_zero_of_lt hgt
      have h2 : suzukiExteriorRight a b x = 0 := suzukiExteriorRight_eq_zero_of_lt hlt
      rw [h1, h2, add_zero, hsupp x ⟨hgt, hlt⟩]
    · have h1 : suzukiExteriorLeft a b x = 0 :=
        suzukiExteriorLeft_eq_zero_of_lt (by linarith)
      have h2 : suzukiExteriorRight a b x = b x :=
        Set.indicator_of_mem (show x ∈ Ici a from hge) b
      rw [h1, h2, zero_add]

/-- Both ports of an `L²` source are `L²`. -/
theorem memLp_suzukiExteriorLeft {a : ℝ} {b : ℝ → ℂ} (hb : MemLp b 2 volume) :
    MemLp (suzukiExteriorLeft a b) 2 volume :=
  hb.indicator measurableSet_Iic

theorem memLp_suzukiExteriorRight {a : ℝ} {b : ℝ → ℂ} (hb : MemLp b 2 volume) :
    MemLp (suzukiExteriorRight a b) 2 volume :=
  hb.indicator measurableSet_Ici

/-- The left port translated to the origin: supported in `(-∞, 0]`. -/
def suzukiLeftPortAtOrigin (a : ℝ) (b : ℝ → ℂ) : ℝ → ℂ :=
  fun x => suzukiExteriorLeft a b (x - a)

/-- The right port translated to the origin: supported in `[0, ∞)`. -/
def suzukiRightPortAtOrigin (a : ℝ) (b : ℝ → ℂ) : ℝ → ℂ :=
  fun x => suzukiExteriorRight a b (x + a)

theorem suzukiLeftPortAtOrigin_eq_zero_of_pos {a : ℝ} {b : ℝ → ℂ} {x : ℝ} (hx : 0 < x) :
    suzukiLeftPortAtOrigin a b x = 0 :=
  suzukiExteriorLeft_eq_zero_of_lt (by linarith)

theorem suzukiRightPortAtOrigin_eq_zero_of_neg {a : ℝ} {b : ℝ → ℂ} {x : ℝ} (hx : x < 0) :
    suzukiRightPortAtOrigin a b x = 0 :=
  suzukiExteriorRight_eq_zero_of_lt (by linarith)

theorem memLp_suzukiLeftPortAtOrigin {a : ℝ} {b : ℝ → ℂ} (hb : MemLp b 2 volume) :
    MemLp (suzukiLeftPortAtOrigin a b) 2 volume :=
  (memLp_suzukiExteriorLeft (a := a) hb).comp_measurePreserving
    (measurePreserving_sub_right volume a)

theorem memLp_suzukiRightPortAtOrigin {a : ℝ} {b : ℝ → ℂ} (hb : MemLp b 2 volume) :
    MemLp (suzukiRightPortAtOrigin a b) 2 volume := by
  have h : suzukiRightPortAtOrigin a b = suzukiExteriorRight a b ∘ fun x => x - (-a) := by
    funext x
    rw [suzukiRightPortAtOrigin, Function.comp_apply, sub_neg_eq_add]
  rw [h]
  exact (memLp_suzukiExteriorRight (a := a) hb).comp_measurePreserving
    (measurePreserving_sub_right volume (-a))

/-- **`(11)`: the Hardy amplitudes are ordinary `L²` functions with the port norms.**  The
amplitude of a port is the `L²` Fourier transform of its translate to the origin, and Plancherel
gives it exactly the norm of the port. -/
theorem norm_fourier_suzukiLeftPortAtOrigin {a : ℝ} {b : ℝ → ℂ} (hb : MemLp b 2 volume) :
    ‖(𝓕 ((memLp_suzukiLeftPortAtOrigin (a := a) hb).toLp _) : Lp ℂ 2 volume)‖
      = ‖((memLp_suzukiLeftPortAtOrigin (a := a) hb).toLp _ : Lp ℂ 2 volume)‖ :=
  Lp.norm_fourier_eq _

theorem norm_fourier_suzukiRightPortAtOrigin {a : ℝ} {b : ℝ → ℂ} (hb : MemLp b 2 volume) :
    ‖(𝓕 ((memLp_suzukiRightPortAtOrigin (a := a) hb).toLp _) : Lp ℂ 2 volume)‖
      = ‖((memLp_suzukiRightPortAtOrigin (a := a) hb).toLp _ : Lp ℂ 2 volume)‖ :=
  Lp.norm_fourier_eq _

/-- **`(10)`: the exterior transform carries the two opposite boundary phases.**  Translating a
port to the origin multiplies its Fourier transform by the boundary phase, with opposite signs at
the two ends. -/
theorem fourierIntegral_suzukiLeftPortAtOrigin (a : ℝ) (b : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (suzukiLeftPortAtOrigin a b) ξ
      = Real.fourierChar (-(a * ξ)) • 𝓕 (suzukiExteriorLeft a b) ξ := by
  have h : suzukiLeftPortAtOrigin a b = suzukiExteriorLeft a b ∘ fun v => v + (-a) := by
    funext x
    rw [suzukiLeftPortAtOrigin, Function.comp_apply, ← sub_eq_add_neg]
  rw [h]
  have hbase := congrFun (VectorFourier.fourierIntegral_comp_add_right (E := ℂ)
    Real.fourierChar volume (innerₗ ℝ) (suzukiExteriorLeft a b) (-a)) ξ
  have hinner : (innerₗ ℝ) (-a) ξ = -(a * ξ) := by
    simp
    ring
  rw [hinner] at hbase
  exact hbase

theorem fourierIntegral_suzukiRightPortAtOrigin (a : ℝ) (b : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (suzukiRightPortAtOrigin a b) ξ
      = Real.fourierChar (a * ξ) • 𝓕 (suzukiExteriorRight a b) ξ := by
  have h : suzukiRightPortAtOrigin a b = suzukiExteriorRight a b ∘ fun v => v + a := by
    funext x
    rw [suzukiRightPortAtOrigin, Function.comp_apply]
  rw [h]
  have hbase := congrFun (VectorFourier.fourierIntegral_comp_add_right (E := ℂ)
    Real.fourierChar volume (innerₗ ℝ) (suzukiExteriorRight a b) a) ξ
  have hinner : (innerₗ ℝ) a ξ = a * ξ := by
    simp
    ring
  rw [hinner] at hbase
  exact hbase

end

end RHTower
