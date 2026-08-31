import GaloisForLFunctions.HTGeometry.LaurentShiftKernel
import GaloisForLFunctions.HTGeometry.ShiftPolePreimage
import GaloisForLFunctions.HTGeometry.ShiftLaurentOstrowski
import GaloisForLFunctions.HTGeometry.EulerPolePartCalculus

/-!
# The first-order equation in the formal Laurent field at infinity

An element of `ℂ((s⁻¹))` whose translation increment is rational and which solves a first-order
constant-coefficient equation with rational right-hand side is itself rational.  The translated
equation makes the pole obstruction `Θ` shift-periodic, and a finitely supported shift-periodic
family vanishes, so the right-hand side lies in the image of `δ - λ` on `ℂ(s)`; the difference of
the two solutions lies in the kernel of `δ - λ` inside the Laurent field, which is `ℂ` or `0`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential RatFunc

noncomputable section

local instance : Differential (LaurentSeries ℂ) := laurentSDifferential
attribute [local instance] ratFuncIntAlgebra'
local instance : Differential (RatFunc ℂ) := ratFuncSDifferential
attribute [local instance] ratLaurentAlgebra

/-! ### The two translations of the rational function field agree -/

theorem ratShiftBy_eq_ratFuncShift (c : ℂ) (r : RatFunc ℂ) :
    ratShiftBy c r = ratFuncShift c r := by
  refine RatFunc.induction_on (P := fun r => ratShiftBy c r = ratFuncShift c r) r ?_
  intro P S _
  rw [map_div₀, map_div₀, ratShiftBy_algebraMap, ratShiftBy_algebraMap,
    ratFuncShift_algebraMap, ratFuncShift_algebraMap, polyTranslate_apply, polyTranslate_apply]

/-! ### The first-order operator on the Laurent field -/

/-- The first-order constant-coefficient operator `u ↦ u′ - λ u` on `ℂ((s⁻¹))`. -/
def firstOrderLaurentOp (lam : ℂ) (u : LaurentSeries ℂ) : LaurentSeries ℂ :=
  u′ - algebraMap ℂ (LaurentSeries ℂ) lam * u

theorem algebraMap_complex_laurent (c : ℂ) :
    algebraMap ℂ (LaurentSeries ℂ) c = laurentC c := by
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, ← laurentCHom_eq_single,
    laurentCHom_apply]

theorem ratToLaurent_algebraMap_complex (c : ℂ) :
    ratToLaurent (algebraMap ℂ (RatFunc ℂ) c) = algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [RatFunc.algebraMap_eq_C, ratToLaurent_C, laurentCHom_apply, algebraMap_complex_laurent]

theorem firstOrderLaurentOp_add (lam : ℂ) (u w : LaurentSeries ℂ) :
    firstOrderLaurentOp lam (u + w)
      = firstOrderLaurentOp lam u + firstOrderLaurentOp lam w := by
  rw [firstOrderLaurentOp, firstOrderLaurentOp, firstOrderLaurentOp, laurentSDeriv_add, mul_add]
  ring

theorem firstOrderLaurentOp_sub (lam : ℂ) (u w : LaurentSeries ℂ) :
    firstOrderLaurentOp lam (u - w)
      = firstOrderLaurentOp lam u - firstOrderLaurentOp lam w := by
  have hd : (u - w)′ = u′ - w′ := by simp only [map_sub]
  rw [firstOrderLaurentOp, firstOrderLaurentOp, firstOrderLaurentOp, hd, mul_sub]
  ring

theorem firstOrderLaurentOp_ratToLaurent (lam : ℂ) (x : RatFunc ℂ) :
    firstOrderLaurentOp lam (ratToLaurent x) = ratToLaurent (firstOrderOp lam x) := by
  rw [firstOrderLaurentOp, firstOrderOp, map_sub, deriv_ratToLaurent, ratFuncSDeriv_apply,
    map_mul, ratToLaurent_algebraMap_complex]

theorem shiftLaurent_firstOrderLaurentOp (h lam : ℂ) (u : LaurentSeries ℂ) :
    shiftLaurent h (firstOrderLaurentOp lam u)
      = firstOrderLaurentOp lam (shiftLaurent h u) := by
  rw [firstOrderLaurentOp, firstOrderLaurentOp, map_sub, shiftLaurent_deriv, map_mul,
    shiftLaurent_algebraMap_complex]

/-! ### A uniform bound on the pole orders -/

theorem exists_polePart_order_bound (g : RatFunc ℂ) :
    ∃ N : ℕ, ∀ (β : ℂ) (d : ℕ), N < d → polePart g β d = 0 := by
  classical
  obtain ⟨s, hs⟩ := (finite_support_polePart g).exists_finset
  refine ⟨(s.image Prod.snd).sup id + 1, ?_⟩
  intro β d hd
  by_contra hc
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hmem : (β, e) ∈ s := (hs (β, e)).mpr (by simpa using hc)
  have hime : e ∈ s.image Prod.snd := Finset.mem_image.mpr ⟨(β, e), hmem, rfl⟩
  have hle : e ≤ (s.image Prod.snd).sup id := Finset.le_sup (f := id) hime
  omega

/-! ### The first-order dichotomy -/

/-- **The first-order equation with a rational translation increment has a rational solution.**
The translated equation makes the pole obstruction shift-periodic, hence identically zero, so the
right-hand side is in the image of `δ - λ` over `ℂ(s)`, and the two solutions differ by a kernel
element, which is constant. -/
theorem exists_ratToLaurent_of_firstOrder {h : ℂ} (hh : h ≠ 0) (lam : ℂ)
    {u : LaurentSeries ℂ} {rho g : RatFunc ℂ}
    (hshift : shiftLaurent h u = u + ratToLaurent rho)
    (hode : firstOrderLaurentOp lam u = ratToLaurent g) :
    ∃ q : RatFunc ℂ, u = ratToLaurent q := by
  classical
  have hinj : Function.Injective (ratToLaurent : RatFunc ℂ → LaurentSeries ℂ) :=
    RingHom.injective ratToLaurent
  have hstep : ratToLaurent (ratShiftBy h g)
      = ratToLaurent (g + firstOrderOp lam rho) := by
    rw [← shiftLaurent_ratToLaurent, ← hode, shiftLaurent_firstOrderLaurentOp, hshift,
      firstOrderLaurentOp_add, hode, firstOrderLaurentOp_ratToLaurent, ← map_add]
  have hshiftg : ratFuncShift h g - g = firstOrderOp lam rho := by
    have hg := hinj hstep
    rw [← ratShiftBy_eq_ratFuncShift]
    linear_combination hg
  have hper : ∀ β : ℂ, Theta lam g (β + h) = Theta lam g β := by
    intro β
    have h1 : Theta lam (ratFuncShift h g - g) β = 0 := by
      rw [hshiftg]
      exact Theta_firstOrderOp lam rho β
    rw [Theta_sub, Theta_ratFuncShift] at h1
    exact sub_eq_zero.mp h1
  have hTheta : ∀ β : ℂ, Theta lam g β = 0 := fun β =>
    Theta_eq_zero_of_periodic hh hper β
  obtain ⟨N, hN⟩ := exists_polePart_order_bound g
  obtain ⟨v, hv⟩ := exists_preimage_of_Theta_zero lam N g (fun β d hd => hN β d hd) hTheta
  have hker : firstOrderLaurentOp lam (u - ratToLaurent v) = 0 := by
    rw [firstOrderLaurentOp_sub, hode, firstOrderLaurentOp_ratToLaurent, hv, sub_self]
  rcases eq_or_ne lam 0 with rfl | hlam
  · have h0 : (u - ratToLaurent v)′ = 0 := by
      have hk := hker
      rw [firstOrderLaurentOp, map_zero, zero_mul, sub_zero] at hk
      exact hk
    obtain ⟨c, hc⟩ := exists_laurentC_of_deriv_eq_zero h0
    refine ⟨v + RatFunc.C c, ?_⟩
    rw [map_add, ratToLaurent_C, laurentCHom_apply]
    linear_combination -hc
  · have h1 : (u - ratToLaurent v)′ = laurentC lam * (u - ratToLaurent v) := by
      have hk := hker
      rw [firstOrderLaurentOp, sub_eq_zero, algebraMap_complex_laurent] at hk
      exact hk
    have hzero := eq_zero_of_deriv_eq_const_mul hlam h1
    exact ⟨v, by linear_combination hzero⟩

/-! ### Words of first-order operators -/

/-- A composite of first-order operators on the Laurent field. -/
def laurentOpWord (l : List ℂ) (u : LaurentSeries ℂ) : LaurentSeries ℂ :=
  l.foldr firstOrderLaurentOp u

/-- The same composite on the rational function field. -/
def ratOpWord (l : List ℂ) (x : RatFunc ℂ) : RatFunc ℂ :=
  l.foldr firstOrderOp x

@[simp] theorem laurentOpWord_nil (u : LaurentSeries ℂ) : laurentOpWord [] u = u := rfl

@[simp] theorem laurentOpWord_cons (a : ℂ) (l : List ℂ) (u : LaurentSeries ℂ) :
    laurentOpWord (a :: l) u = firstOrderLaurentOp a (laurentOpWord l u) := rfl

@[simp] theorem ratOpWord_nil (x : RatFunc ℂ) : ratOpWord [] x = x := rfl

@[simp] theorem ratOpWord_cons (a : ℂ) (l : List ℂ) (x : RatFunc ℂ) :
    ratOpWord (a :: l) x = firstOrderOp a (ratOpWord l x) := rfl

theorem laurentOpWord_ratToLaurent (l : List ℂ) (x : RatFunc ℂ) :
    laurentOpWord l (ratToLaurent x) = ratToLaurent (ratOpWord l x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [laurentOpWord_cons, ih, firstOrderLaurentOp_ratToLaurent, ratOpWord_cons]

theorem shiftLaurent_laurentOpWord {h : ℂ} {u : LaurentSeries ℂ} {rho : RatFunc ℂ}
    (hu : shiftLaurent h u = u + ratToLaurent rho) (l : List ℂ) :
    shiftLaurent h (laurentOpWord l u)
      = laurentOpWord l u + ratToLaurent (ratOpWord l rho) := by
  induction l with
  | nil => simpa using hu
  | cons a l ih =>
      rw [laurentOpWord_cons, shiftLaurent_firstOrderLaurentOp, ih, firstOrderLaurentOp_add,
        firstOrderLaurentOp_ratToLaurent, ratOpWord_cons]

/-- **Descent through a word of first-order operators.**  If a composite of first-order
constant-coefficient operators sends a Laurent series with rational translation increment to a
rational function, the series itself is rational. -/
theorem exists_ratToLaurent_of_opWord {h : ℂ} (hh : h ≠ 0) :
    ∀ (l : List ℂ) (u : LaurentSeries ℂ) (rho g : RatFunc ℂ),
      shiftLaurent h u = u + ratToLaurent rho → laurentOpWord l u = ratToLaurent g →
      ∃ q : RatFunc ℂ, u = ratToLaurent q := by
  intro l
  induction l with
  | nil => intro u _ g _ hg; exact ⟨g, hg⟩
  | cons a l ih =>
      intro u rho g hshift hg
      rw [laurentOpWord_cons] at hg
      obtain ⟨q1, hq1⟩ := exists_ratToLaurent_of_firstOrder hh a
        (shiftLaurent_laurentOpWord hshift l) hg
      exact ih u rho q1 hshift hq1

end

end GaloisForLFunctions.HTGeometry
