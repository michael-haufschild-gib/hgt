import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Variable-width two-edge principalization

At a fixed additive aperture `a ≥ 0`, every even function supported in
`[-a,a]` is uniquely a two-edge packet `x ↦ f (a - |x|)` whose one-sided
profile is supported in `[0,a]`.  The same statement holds in the odd
sector with the canonical sign between the two edges.

Thus a two-edge profile class whose width is allowed to grow with the
aperture is the whole parity sector.  Uniform profile tightness is the
load-bearing condition in any nontrivial boundary-profile decomposition.
-/

open Set

namespace RHTower

noncomputable section

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Read an aperture function from the positive edge.  Values outside the
one-sided aperture `[0,a]` are discarded. -/
def apertureBoundaryReadout (a : ℝ) (u : ℝ → E) (s : ℝ) : E :=
  if s ∈ Icc (0 : ℝ) a then u (a - s) else 0

/-- Reconstruct an even two-edge packet from its one-sided boundary
profile. -/
def evenTwoEdgePacket (a : ℝ) (f : ℝ → E) (x : ℝ) : E :=
  f (a - |x|)

/-- Reconstruct an odd two-edge packet from its positive-edge profile. -/
def oddTwoEdgePacket (a : ℝ) (f : ℝ → E) (x : ℝ) : E :=
  if 0 ≤ x then f (a - x) else -f (a + x)

/-- Functions supported in the symmetric aperture and even under
reflection. -/
def evenApertureSubmodule (a : ℝ) : Submodule ℝ (ℝ → E) where
  carrier := {u | Function.Even u ∧ ∀ x, a < |x| → u x = 0}
  zero_mem' := by
    constructor
    · intro x
      rfl
    · intro x _
      rfl
  add_mem' := by
    rintro u v ⟨huEven, huSupp⟩ ⟨hvEven, hvSupp⟩
    constructor
    · intro x
      simp only [Pi.add_apply, huEven x, hvEven x]
    · intro x hx
      simp only [Pi.add_apply, huSupp x hx, hvSupp x hx, add_zero]
  smul_mem' := by
    rintro c u ⟨huEven, huSupp⟩
    constructor
    · intro x
      simp only [Pi.smul_apply, huEven x]
    · intro x hx
      simp only [Pi.smul_apply, huSupp x hx, smul_zero]

/-- Functions supported in the symmetric aperture and odd under
reflection. -/
def oddApertureSubmodule (a : ℝ) : Submodule ℝ (ℝ → E) where
  carrier := {u | Function.Odd u ∧ ∀ x, a < |x| → u x = 0}
  zero_mem' := by
    constructor
    · intro x
      simp
    · intro x _
      rfl
  add_mem' := by
    rintro u v ⟨huOdd, huSupp⟩ ⟨hvOdd, hvSupp⟩
    constructor
    · intro x
      simp only [Pi.add_apply, huOdd x, hvOdd x, neg_add]
    · intro x hx
      simp only [Pi.add_apply, huSupp x hx, hvSupp x hx, add_zero]
  smul_mem' := by
    rintro c u ⟨huOdd, huSupp⟩
    constructor
    · intro x
      simp only [Pi.smul_apply, huOdd x, smul_neg]
    · intro x hx
      simp only [Pi.smul_apply, huSupp x hx, smul_zero]

/-- One-sided profiles supported in `[0,a]`. -/
def apertureBoundaryProfileSubmodule (a : ℝ) : Submodule ℝ (ℝ → E) where
  carrier := {f | ∀ s, s ∉ Icc (0 : ℝ) a → f s = 0}
  zero_mem' := by
    intro s _
    rfl
  add_mem' := by
    intro f g hf hg s hs
    simp only [Pi.add_apply, hf s hs, hg s hs, add_zero]
  smul_mem' := by
    intro c f hf s hs
    simp only [Pi.smul_apply, hf s hs, smul_zero]

/-- The one-sided profile space for the odd sector.  The value at `a`
corresponds to the reflection fixed point `x=0`, so oddness forces it to
vanish. -/
def oddApertureBoundaryProfileSubmodule (a : ℝ) : Submodule ℝ (ℝ → E) where
  carrier := {f | (∀ s, s ∉ Icc (0 : ℝ) a → f s = 0) ∧ f a = 0}
  zero_mem' := by
    constructor
    · intro s _
      rfl
    · rfl
  add_mem' := by
    rintro f g ⟨hfSupp, hfa⟩ ⟨hgSupp, hga⟩
    constructor
    · intro s hs
      simp only [Pi.add_apply, hfSupp s hs, hgSupp s hs, add_zero]
    · simp only [Pi.add_apply, hfa, hga, add_zero]
  smul_mem' := by
    rintro c f ⟨hfSupp, hfa⟩
    constructor
    · intro s hs
      simp only [Pi.smul_apply, hfSupp s hs, smul_zero]
    · simp only [Pi.smul_apply, hfa, smul_zero]

theorem apertureBoundaryReadout_mem
    (a : ℝ) (u : ℝ → E) :
    apertureBoundaryReadout a u ∈ apertureBoundaryProfileSubmodule (E := E) a := by
  intro s hs
  simp [apertureBoundaryReadout, hs]

theorem apertureBoundaryReadout_odd_mem
    {a : ℝ} (u : oddApertureSubmodule (E := E) a) :
    apertureBoundaryReadout a (u : ℝ → E) ∈
      oddApertureBoundaryProfileSubmodule (E := E) a := by
  constructor
  · exact apertureBoundaryReadout_mem a (u : ℝ → E)
  · have hself : (u : ℝ → E) (0 : ℝ) = -(u : ℝ → E) 0 := by
      simpa only [neg_zero] using u.property.1 0
    have htwo : (2 : ℝ) • (u : ℝ → E) 0 = 0 := by
      rw [two_smul]
      calc
        (u : ℝ → E) 0 + (u : ℝ → E) 0 =
            -(u : ℝ → E) 0 + (u : ℝ → E) 0 :=
          congrArg (fun y => y + (u : ℝ → E) 0) hself
        _ = 0 := neg_add_cancel ((u : ℝ → E) 0)
    have hzero : (u : ℝ → E) (0 : ℝ) = 0 :=
      (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    by_cases ha : 0 ≤ a <;> simp [apertureBoundaryReadout, ha, hzero]

omit [AddCommGroup E] [Module ℝ E] in
theorem evenTwoEdgePacket_even (a : ℝ) (f : ℝ → E) :
    Function.Even (evenTwoEdgePacket a f) := by
  intro x
  simp [evenTwoEdgePacket]

theorem evenTwoEdgePacket_eq_zero_of_abs_gt
    {a : ℝ} (f : ℝ → E)
    (hf : f ∈ apertureBoundaryProfileSubmodule (E := E) a)
    {x : ℝ} (hx : a < |x|) :
    evenTwoEdgePacket a f x = 0 := by
  apply hf
  intro hs
  exact (not_le_of_gt (sub_neg.mpr hx)) hs.1

theorem evenTwoEdgePacket_mem
    {a : ℝ} (f : apertureBoundaryProfileSubmodule (E := E) a) :
    evenTwoEdgePacket a (f : ℝ → E) ∈ evenApertureSubmodule (E := E) a := by
  constructor
  · exact evenTwoEdgePacket_even a (f : ℝ → E)
  · intro x hx
    exact evenTwoEdgePacket_eq_zero_of_abs_gt (f : ℝ → E) f.property hx

theorem oddTwoEdgePacket_odd {a : ℝ}
    (f : oddApertureBoundaryProfileSubmodule (E := E) a) :
    Function.Odd (oddTwoEdgePacket a (f : ℝ → E)) := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [oddTwoEdgePacket, f.property.2]
  · by_cases hpos : 0 < x
    · have hneg : ¬ 0 ≤ -x := by linarith
      rw [oddTwoEdgePacket, if_neg hneg, oddTwoEdgePacket, if_pos hpos.le]
      congr 2
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
      have hnegpos : 0 ≤ -x := by linarith
      rw [oddTwoEdgePacket, if_pos hnegpos, oddTwoEdgePacket,
        if_neg (not_le.mpr hxneg)]
      simp only [neg_neg, sub_neg_eq_add]

omit [Module ℝ E] in
theorem oddTwoEdgePacket_eq_zero_of_abs_gt
    {a : ℝ} (f : ℝ → E)
    (hf : ∀ s, s ∉ Icc (0 : ℝ) a → f s = 0)
    {x : ℝ} (hx : a < |x|) :
    oddTwoEdgePacket a f x = 0 := by
  by_cases hnonneg : 0 ≤ x
  · have hnot : a - x ∉ Icc (0 : ℝ) a := by
      intro hs
      rw [abs_of_nonneg hnonneg] at hx
      linarith [hs.1]
    simp [oddTwoEdgePacket, hnonneg, hf _ hnot]
  · have hxneg : x < 0 := lt_of_not_ge hnonneg
    have hnot : a + x ∉ Icc (0 : ℝ) a := by
      intro hs
      rw [abs_of_neg hxneg] at hx
      linarith [hs.1]
    simp [oddTwoEdgePacket, hnonneg, hf _ hnot]

theorem oddTwoEdgePacket_mem
    {a : ℝ} (f : oddApertureBoundaryProfileSubmodule (E := E) a) :
    oddTwoEdgePacket a (f : ℝ → E) ∈ oddApertureSubmodule (E := E) a := by
  constructor
  · exact oddTwoEdgePacket_odd f
  · intro x hx
    exact oddTwoEdgePacket_eq_zero_of_abs_gt (f : ℝ → E) f.property.1 hx

/-- Exact even reconstruction from the positive-edge readout. -/
theorem evenTwoEdgePacket_apertureBoundaryReadout
    {a : ℝ} (u : evenApertureSubmodule (E := E) a) :
    evenTwoEdgePacket a (apertureBoundaryReadout a (u : ℝ → E)) = (u : ℝ → E) := by
  funext x
  by_cases hx : |x| ≤ a
  · have hmem : a - |x| ∈ Icc (0 : ℝ) a := by
      constructor <;> linarith [abs_nonneg x]
    rw [evenTwoEdgePacket, apertureBoundaryReadout, if_pos hmem]
    have harg : a - (a - |x|) = |x| := by ring
    rw [harg]
    by_cases hnonneg : 0 ≤ x
    · rw [abs_of_nonneg hnonneg]
    · have hxneg : x < 0 := lt_of_not_ge hnonneg
      simpa [abs_of_neg hxneg] using u.property.1 x
  · have hxgt : a < |x| := lt_of_not_ge hx
    have hnot : a - |x| ∉ Icc (0 : ℝ) a := by
      intro hs
      linarith [hs.1]
    rw [evenTwoEdgePacket, apertureBoundaryReadout, if_neg hnot,
      u.property.2 x hxgt]

/-- Exact odd reconstruction from the positive-edge readout. -/
theorem oddTwoEdgePacket_apertureBoundaryReadout
    {a : ℝ} (u : oddApertureSubmodule (E := E) a) :
    oddTwoEdgePacket a (apertureBoundaryReadout a (u : ℝ → E)) = (u : ℝ → E) := by
  funext x
  by_cases hx : |x| ≤ a
  · by_cases hnonneg : 0 ≤ x
    · have hmem : a - x ∈ Icc (0 : ℝ) a := by
        rw [abs_of_nonneg hnonneg] at hx
        constructor <;> linarith
      simp [oddTwoEdgePacket, hnonneg, apertureBoundaryReadout, hmem]
    · have hxneg : x < 0 := lt_of_not_ge hnonneg
      have hmem : a + x ∈ Icc (0 : ℝ) a := by
        rw [abs_of_neg hxneg] at hx
        constructor <;> linarith
      rw [oddTwoEdgePacket, if_neg hnonneg, apertureBoundaryReadout, if_pos hmem]
      have harg : a - (a + x) = -x := by ring
      rw [harg, u.property.1 x, neg_neg]
  · have hxgt : a < |x| := lt_of_not_ge hx
    rw [u.property.2 x hxgt]
    by_cases hnonneg : 0 ≤ x
    · have hnot : a - x ∉ Icc (0 : ℝ) a := by
        intro hs
        rw [abs_of_nonneg hnonneg] at hxgt
        linarith [hs.1]
      simp [oddTwoEdgePacket, hnonneg, apertureBoundaryReadout, hnot]
    · have hxneg : x < 0 := lt_of_not_ge hnonneg
      have hnot : a + x ∉ Icc (0 : ℝ) a := by
        intro hs
        rw [abs_of_neg hxneg] at hxgt
        linarith [hs.1]
      simp [oddTwoEdgePacket, hnonneg, apertureBoundaryReadout, hnot]

/-- Reading the positive edge of an even packet recovers the original
one-sided profile. -/
theorem apertureBoundaryReadout_evenTwoEdgePacket
    {a : ℝ}
    (f : apertureBoundaryProfileSubmodule (E := E) a) :
    apertureBoundaryReadout a (evenTwoEdgePacket a (f : ℝ → E)) = (f : ℝ → E) := by
  funext s
  by_cases hs : s ∈ Icc (0 : ℝ) a
  · have hnonneg : 0 ≤ a - s := sub_nonneg.mpr hs.2
    simp [apertureBoundaryReadout, hs, evenTwoEdgePacket,
      abs_of_nonneg hnonneg]
  · simp [apertureBoundaryReadout, hs, f.property s hs]

/-- Reading the positive edge of an odd packet recovers the original
one-sided profile. -/
theorem apertureBoundaryReadout_oddTwoEdgePacket
    {a : ℝ}
    (f : oddApertureBoundaryProfileSubmodule (E := E) a) :
    apertureBoundaryReadout a (oddTwoEdgePacket a (f : ℝ → E)) = (f : ℝ → E) := by
  funext s
  by_cases hs : s ∈ Icc (0 : ℝ) a
  · have hnonneg : 0 ≤ a - s := sub_nonneg.mpr hs.2
    simp [apertureBoundaryReadout, hs, oddTwoEdgePacket, hnonneg]
  · simp [apertureBoundaryReadout, hs, f.property.1 s hs]

/-- **Even variable-width principalization.**  At aperture `a`, the whole
even aperture space is linearly equivalent to the one-sided width-`a`
profile space. -/
def evenApertureBoundaryLinearEquiv (a : ℝ) :
    evenApertureSubmodule (E := E) a ≃ₗ[ℝ]
      apertureBoundaryProfileSubmodule (E := E) a where
  toFun u := ⟨apertureBoundaryReadout a (u : ℝ → E),
    apertureBoundaryReadout_mem a (u : ℝ → E)⟩
  invFun f := ⟨evenTwoEdgePacket a (f : ℝ → E), evenTwoEdgePacket_mem f⟩
  left_inv u := Subtype.ext (evenTwoEdgePacket_apertureBoundaryReadout u)
  right_inv f := Subtype.ext (apertureBoundaryReadout_evenTwoEdgePacket f)
  map_add' u v := by
    ext s
    by_cases hs : s ∈ Icc (0 : ℝ) a <;>
      simp [apertureBoundaryReadout, hs]
  map_smul' c u := by
    ext s
    by_cases hs : s ∈ Icc (0 : ℝ) a <;>
      simp [apertureBoundaryReadout, hs]

/-- **Odd variable-width principalization.**  The odd aperture sector has
the same one-sided profile coordinate, with the reflection sign inserted
by `oddTwoEdgePacket`. -/
def oddApertureBoundaryLinearEquiv (a : ℝ) :
    oddApertureSubmodule (E := E) a ≃ₗ[ℝ]
      oddApertureBoundaryProfileSubmodule (E := E) a where
  toFun u := ⟨apertureBoundaryReadout a (u : ℝ → E),
    apertureBoundaryReadout_odd_mem u⟩
  invFun f := ⟨oddTwoEdgePacket a (f : ℝ → E), oddTwoEdgePacket_mem f⟩
  left_inv u := Subtype.ext (oddTwoEdgePacket_apertureBoundaryReadout u)
  right_inv f := Subtype.ext (apertureBoundaryReadout_oddTwoEdgePacket f)
  map_add' u v := by
    ext s
    by_cases hs : s ∈ Icc (0 : ℝ) a <;>
      simp [apertureBoundaryReadout, hs]
  map_smul' c u := by
    ext s
    by_cases hs : s ∈ Icc (0 : ℝ) a <;>
      simp [apertureBoundaryReadout, hs]

end

end

end RHTower
